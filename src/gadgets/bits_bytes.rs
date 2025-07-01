use plonky2::{
    field::{extension::Extendable, types::Field},
    hash::hash_types::RichField,
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};

pub fn bytes_to_bits_be<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    bytes: &[Target],
) -> Vec<BoolTarget> {
    bytes
        .iter()
        .flat_map(|&byte| builder.split_le(byte, 8).into_iter().rev())
        .collect()
}

pub fn bits_to_bytes_be<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    bits: &[BoolTarget],
) -> Vec<Target> {
    assert!(bits.len() % 8 == 0);
    bits.chunks(8)
        .map(|window| builder.le_sum(window.iter().rev()))
        .collect()
}

pub fn set_bits_target_le<F: Field>(
    pw: &mut PartialWitness<F>,
    bits: &[BoolTarget],
    data: u64,
) -> anyhow::Result<()> {
    for (n, b) in bits.iter().enumerate() {
        pw.set_bool_target(*b, (data >> n) & 1 != 0)?;
    }
    Ok(())
}
