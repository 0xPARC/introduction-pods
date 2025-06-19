use plonky2::{
    field::extension::Extendable,
    hash::{
        hash_types::{HashOutTarget, NUM_HASH_OUT_ELTS, RichField},
        hashing::PlonkyPermutation,
    },
    iop::target::{BoolTarget, Target},
    plonk::{circuit_builder::CircuitBuilder, config::AlgebraicHasher},
};

fn finished_array<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    len: Target,
    max_len: usize,
) -> Vec<BoolTarget> {
    if max_len == 0 {
        return Vec::new();
    }
    let neg_one = builder.neg_one();
    let zero = builder.zero();
    let mut ans = Vec::with_capacity(max_len);
    let mut finished = builder.is_equal(len, zero);
    ans.push(finished);
    let mut remaining_len = len;
    for _ in 0..(max_len - 1) {
        remaining_len = builder.add(remaining_len, neg_one);
        let at_end = builder.is_equal(remaining_len, zero);
        finished = builder.or(finished, at_end);
        ans.push(finished);
    }
    ans
}

// TODO: Other parts of the circuit may care about / `finished`,
// so maybe compute it outside this function and pass it in
/// Computes the hash of the first `len` elements of `data`.
pub fn hash_variable_len<F: RichField + Extendable<D>, const D: usize, H: AlgebraicHasher<F>>(
    builder: &mut CircuitBuilder<F, D>,
    data: &[Target],
    len: Target,
) -> HashOutTarget {
    let zero = builder.zero();
    let neg_one = builder.neg_one();
    let mut remaining_len = len;
    let finished = finished_array(builder, len, data.len());
    let mut item_index = 0;
    let mut state = H::AlgebraicPermutation::new(core::iter::repeat(zero));
    for input_chunk in data.chunks(H::AlgebraicPermutation::RATE) {
        let prev_finished = finished[item_index];
        let existing_chunk = state.as_ref();
        let mut mod_state = Vec::with_capacity(input_chunk.len());
        for (&input, &existing) in input_chunk.iter().zip(existing_chunk.iter()) {
            remaining_len = builder.add(remaining_len, neg_one);
            let item = builder.select(finished[item_index], existing, input);
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

#[cfg(test)]
mod test {
    use plonky2::{
        field::{
            goldilocks_field::GoldilocksField,
            types::{Field, Sample},
        },
        hash::{
            hashing::hash_n_to_hash_no_pad,
            poseidon::{PoseidonHash, PoseidonPermutation},
        },
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
    };
    use rand::{Rng, rngs::OsRng};

    use crate::gadgets::hash_var_len::hash_variable_len;

    type C = plonky2::plonk::config::PoseidonGoldilocksConfig;

    #[test]
    fn test_var_len_hash() -> anyhow::Result<()> {
        const MAX_LEN: usize = 128;
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let msg_t = builder.add_virtual_targets(MAX_LEN);
        let msg_len_t = builder.add_virtual_target();
        let hash_t = hash_variable_len::<_, 2, PoseidonHash>(&mut builder, &msg_t, msg_len_t);
        let data = builder.build::<C>();
        for _ in 0..20 {
            let msg: [GoldilocksField; MAX_LEN] = Sample::rand_array();
            let msg_len = OsRng.gen_range(0..(MAX_LEN + 1));
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
}
