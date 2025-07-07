use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::{BoolTarget, Target},
    plonk::circuit_builder::CircuitBuilder,
};

pub fn shift_left<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    array: &[Target],
    shift_base2: &[BoolTarget],
) -> Vec<Target> {
    let zero = builder.zero();
    let mut out = array.to_vec();
    for (n, &bit) in shift_base2.iter().enumerate() {
        let shift = 1 << n;
        for idx in 0..out.len() {
            let shifted = out.get(idx + shift).copied().unwrap_or(zero);
            out[idx] = builder.select(bit, shifted, out[idx]);
        }
    }
    out
}

#[cfg(test)]
mod test {
    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field},
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use rand::{Rng, RngCore, rngs::OsRng};

    use crate::gadgets::shift::shift_left;

    pub const WINDOW_LEN: usize = 34;
    pub const DOC_LENGTH: usize = 4129;
    pub type C = PoseidonGoldilocksConfig;

    #[test]
    fn test_find() -> anyhow::Result<()> {
        let mut msg = [0u8; DOC_LENGTH];
        OsRng.fill_bytes(&mut msg);
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let mut pw = PartialWitness::new();
        let msg_t = builder.add_virtual_targets(DOC_LENGTH);
        for (&ch, &ch_t) in msg.iter().zip(msg_t.iter()) {
            pw.set_target(ch_t, GoldilocksField::from_canonical_u8(ch))?;
        }
        let idx = OsRng.gen_range(0..4096);
        let idx_bits_t: [_; 12] = core::array::from_fn(|_| builder.add_virtual_bool_target_safe());
        for (n, &b) in idx_bits_t.iter().enumerate() {
            pw.set_bool_target(b, (idx >> n) & 1 != 0)?;
        }
        let window_t = builder.add_virtual_targets(WINDOW_LEN);
        for (&ch, &ch_t) in msg.iter().skip(idx).zip(window_t.iter()) {
            pw.set_target(ch_t, GoldilocksField::from_canonical_u8(ch))?;
        }
        let shifted_t = shift_left(&mut builder, &msg_t, &idx_bits_t);
        for (&t1, &t2) in window_t.iter().zip(shifted_t.iter()) {
            builder.connect(t1, t2);
        }
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)
    }
}
