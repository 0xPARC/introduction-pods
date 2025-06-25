use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::{BoolTarget, Target},
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
    bits.windows(8)
        .map(|window| builder.le_sum(window.iter().rev()))
        .collect()
}
