use plonky2::{
    field::extension::Extendable,
    hash::{
        hash_types::{HashOutTarget, NUM_HASH_OUT_ELTS, RichField},
        hashing::PlonkyPermutation,
        poseidon::PoseidonHash,
    },
    iop::target::{BoolTarget, Target},
    plonk::{circuit_builder::CircuitBuilder, config::AlgebraicHasher},
};

#[derive(Default, Clone, Debug)]
pub struct EndCheck {
    pub past_end: Vec<BoolTarget>,
    pub exact_end: Vec<BoolTarget>,
}

pub fn compute_end_checks<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    len: Target,
    max_len: usize,
) -> EndCheck {
    if max_len == 0 {
        return Default::default();
    }
    let neg_one = builder.neg_one();
    let zero = builder.zero();
    let mut exact_end = Vec::with_capacity(max_len);
    let mut past_end = Vec::with_capacity(max_len);
    let mut finished = builder.is_equal(len, zero);
    exact_end.push(finished);
    past_end.push(finished);
    let mut remaining_len = len;
    for _ in 0..(max_len - 1) {
        remaining_len = builder.add(remaining_len, neg_one);
        let at_end = builder.is_equal(remaining_len, zero);
        finished = builder.or(finished, at_end);
        exact_end.push(at_end);
        past_end.push(finished);
    }
    EndCheck {
        past_end,
        exact_end,
    }
}

// TODO: Other parts of the circuit may care about / `finished`,
// so maybe compute it outside this function and pass it in
/// Computes the hash of the first `len` elements of `data`.
pub fn hash_variable_len<F: RichField + Extendable<D>, const D: usize, H: AlgebraicHasher<F>>(
    builder: &mut CircuitBuilder<F, D>,
    data: &[Target],
    past_end: &[BoolTarget],
) -> HashOutTarget {
    let zero = builder.zero();
    let mut item_index = 0;
    let mut state = H::AlgebraicPermutation::new(core::iter::repeat(zero));
    for input_chunk in data.chunks(H::AlgebraicPermutation::RATE) {
        let prev_finished = past_end[item_index];
        let existing_chunk = state.as_ref();
        let mut mod_state = Vec::with_capacity(input_chunk.len());
        for (&input, &existing) in input_chunk.iter().zip(existing_chunk.iter()) {
            let item = builder.select(past_end[item_index], existing, input);
            mod_state.push(item);
            item_index += 1;
        }
        state.set_from_slice(&mod_state, 0);
        let permuted_state = builder.permute::<H>(state);
        let selected: Vec<_> = state
            .as_ref()
            .iter()
            .zip(permuted_state.as_ref().iter())
            .map(|(&st, &pst)| builder.select(prev_finished, st, pst))
            .collect();
        state.set_from_slice(&selected, 0);
    }
    let mut outputs = [zero; NUM_HASH_OUT_ELTS];
    let mut idx = 0;
    loop {
        for &s in state.squeeze() {
            outputs[idx] = s;
            idx += 1;
            if idx == NUM_HASH_OUT_ELTS {
                return HashOutTarget { elements: outputs };
            }
        }
        state = builder.permute::<H>(state);
    }
}

/// Combine groups of seven bytes into a single field element.
///
/// This function assumes that `data` has space for at least one
/// byte of padding at the end.
fn collapse_str<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    data: &[Target],
    end_checks: &EndCheck,
) -> (Vec<Target>, Vec<BoolTarget>) {
    assert_eq!(data.len(), end_checks.past_end.len());
    let factor = builder.constant(F::from_canonical_u32(0x100));
    let out_len = data.len().div_ceil(7);
    let mut out_data = Vec::new();
    let out_end_check: Vec<_> = (0..out_len)
        .map(|i| {
            if i == 0 {
                builder._false()
            } else {
                end_checks.past_end[7 * i - 1]
            }
        })
        .collect();
    for (c, chunk) in data.chunks(7).enumerate() {
        let mut out_byte = builder.zero();
        for (b, &in_byte) in chunk.iter().enumerate().rev() {
            let idx = 7 * c + b;
            let to_add = builder.select(
                end_checks.past_end[idx],
                end_checks.exact_end[idx].target,
                in_byte,
            );
            out_byte = builder.mul_add(factor, out_byte, to_add);
        }
        out_data.push(out_byte);
    }
    assert_eq!(out_data.len(), out_end_check.len());
    (out_data, out_end_check)
}

/// pod2 string hash function, in circuit, with variable length strings
///
/// Assumes that the string is strictly shorter than `data`.
pub fn pod_str_hash<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    data: &[Target],
    len: Target,
) -> HashOutTarget {
    let end_checks = compute_end_checks(builder, len, data.len());
    pod_str_hash_with_end_check(builder, data, &end_checks)
}

pub fn pod_str_hash_with_end_check<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    data: &[Target],
    end_checks: &EndCheck,
) -> HashOutTarget {
    let (collapsed, collapsed_end_check) = collapse_str(builder, data, end_checks);
    hash_variable_len::<F, D, PoseidonHash>(builder, &collapsed, &collapsed_end_check)
}

#[cfg(test)]
mod test {
    use plonky2::{
        field::{
            goldilocks_field::GoldilocksField,
            types::{Field, Sample},
        },
        hash::{
            hash_types::HashOut,
            hashing::hash_n_to_hash_no_pad,
            poseidon::{PoseidonHash, PoseidonPermutation},
        },
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
    };
    use pod2::middleware::hash_str;
    use rand::{Rng, rngs::OsRng};

    use crate::gadgets::hash_var_len::{compute_end_checks, hash_variable_len, pod_str_hash};

    type C = plonky2::plonk::config::PoseidonGoldilocksConfig;

    #[test]
    fn test_hash_var_len() -> anyhow::Result<()> {
        for _ in 0..40 {
            let max_len = OsRng.gen_range(0..129);
            let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
            let msg_t = builder.add_virtual_targets(max_len);
            let msg_len_t = builder.add_virtual_target();
            let end_check_t = compute_end_checks(&mut builder, msg_len_t, max_len);
            let hash_t = hash_variable_len::<_, 2, PoseidonHash>(
                &mut builder,
                &msg_t,
                &end_check_t.past_end,
            );
            let data = builder.build::<C>();

            let msg = GoldilocksField::rand_vec(max_len);
            let msg_len = OsRng.gen_range(0..(max_len + 1));
            let hash = hash_n_to_hash_no_pad::<_, PoseidonPermutation<_>>(&msg[..msg_len]);
            let mut pw = PartialWitness::new();
            pw.set_target_arr(&msg_t, &msg)?;
            pw.set_target(msg_len_t, GoldilocksField::from_canonical_usize(msg_len))?;
            pw.set_hash_target(hash_t, hash)?;
            let proof = data.prove(pw)?;
            data.verify(proof)?;
        }
        Ok(())
    }

    #[test]
    fn test_pod_hash() -> anyhow::Result<()> {
        for _ in 0..50 {
            let max_len = OsRng.gen_range(1..25);
            let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
            let msg_t = builder.add_virtual_targets(max_len);
            let msg_len_t = builder.add_virtual_target();
            let hash_t = pod_str_hash(&mut builder, &msg_t, msg_len_t);
            let data = builder.build::<C>();

            let msg_bytes: Vec<u8> = std::iter::repeat_with(|| OsRng.gen_range(0..128))
                .take(max_len)
                .collect();
            let msg: Vec<_> = msg_bytes
                .iter()
                .map(|&b| GoldilocksField::from_canonical_u8(b))
                .collect();
            let msg_len = OsRng.gen_range(0..max_len);
            let hash = HashOut {
                elements: hash_str(core::str::from_utf8(&msg_bytes[..msg_len])?).0,
            };
            println!("max len {max_len} msg len {msg_len} hash {hash:?}");

            let mut pw = PartialWitness::new();
            pw.set_target_arr(&msg_t, &msg)?;
            pw.set_target(msg_len_t, GoldilocksField::from_canonical_usize(msg_len))?;
            pw.set_hash_target(hash_t, hash)?;
            let proof = data.prove(pw)?;
            data.verify(proof)?;
        }
        Ok(())
    }
}
