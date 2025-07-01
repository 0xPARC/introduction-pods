use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField, iop::target::Target,
    plonk::circuit_builder::CircuitBuilder,
};

pub fn check_less_or_equal<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    lhs: Target,
    rhs: Target,
    max_bits: usize,
) {
    let diff = builder.sub(rhs, lhs);
    builder.range_check(diff, max_bits);
}
