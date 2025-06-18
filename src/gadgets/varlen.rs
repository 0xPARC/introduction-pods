use plonky2::iop::{target::Target, witness::PartialWitness};

/// An array whose length is not known at the time of circuit creation.
///
/// The array is stored at the end of `data`.  The rest of `data` is filled
/// with arbitrary values.  The variable `padding_len` keeps track of the number
/// of arbitrary filler values.
struct VariableLengthArrayTarget {
    padding_len: Target,
    data: Vec<Target>,
}

impl VariableLengthArrayTarget {
    fn set_target<F: Field>(
        &self,
        pw: &mut PartialWitness<F>,
        values: &[Target],
    ) -> anyhow::Result<()> {
        if values.len() > self.data.len() {
            anyhow::bail!("Array is too large");
        }
    }
}
