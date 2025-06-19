use plonky2::{
    field::extension::Extendable,
    hash::{
        hash_types::{HashOutTarget, RichField},
        hashing::PlonkyPermutation,
    },
    iop::target::Target,
    plonk::{circuit_builder::CircuitBuilder, config::AlgebraicHasher},
};

/// Computes the hash of the first `len` elements of `data`.
pub fn hash_variable_len<F: RichField + Extendable<D>, const D: usize, H: AlgebraicHasher<F>>(
    builder: &mut CircuitBuilder<F, D>,
    data: &[Target],
    len: Target,
) -> HashOutTarget {
    let zero = builder.zero();
    let mut remaining_len = len;
    let mut finished = builder._true();
    let mut state = H::AlgebraicPermutation::new(core::iter::repeat(zero));
    for input_chunk in data.chunks(H::AlgebraicPermutation::RATE) {
        let prev_finished = finished;
        let existing_chunk = state.as_ref();
        let mut mod_state = Vec::with_capacity(input_chunk.len());
        for (&input, &existing) in input_chunk.iter().zip(existing_chunk.iter()) {
            let at_end = builder.is_equal(remaining_len, zero);
            finished = builder.or(finished, at_end);
            let item = builder.select(finished, existing, input);
            mod_state.push(item);
        }
        state.set_from_slice(&mod_state, 0);
        let permuted_state = builder.permute::<H>(state);
        // TODO: select state or permuted state based on prev_finished
    }
    // TODO: Squeeze to get outputs
    todo!()
}
