use plonky2::{
    field::{extension::Extendable, types::Field},
    hash::hash_types::RichField,
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};

pub fn bits_to_bytes_be<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    bits: &[BoolTarget],
) -> Vec<Target> {
    assert_eq!(bits.len() % 8, 0);
    bits.chunks(8)
        .map(|chunk| builder.le_sum(chunk.iter().rev()))
        .collect()
}

// Helper function to convert bit targets to byte targets
pub fn reversed_bits_to_bytes_be<F: RichField + Extendable<D>, const D: usize>(
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
