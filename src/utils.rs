use plonky2::{
    iop::target::{BoolTarget, Target},
    plonk::circuit_builder::CircuitBuilder,
};
use pod2::backends::plonky2::basetypes::{D, F};

// Helper function to convert bit targets to byte targets
pub(crate) fn le_bits_to_bytes_targets(
    builder: &mut CircuitBuilder<F, D>,
    bits: &[BoolTarget],
) -> Vec<Target> {
    assert_eq!(bits.len() % 8, 0);
    let mut bytes = Vec::new();

    for chunk in bits.chunks(8) {
        let byte_val = builder.le_sum(chunk.iter());

        bytes.push(byte_val);
    }

    bytes.reverse();
    bytes
}
