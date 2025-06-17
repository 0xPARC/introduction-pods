#![feature(trait_upcasting)]
use std::fmt;

use pod2::middleware::TypedValue;

pub mod ecdsapod;
pub mod ed25519pod;

pub enum PodType {
    Ecdsa = 1001,
    Ed25519 = 1002,
}

impl fmt::Display for PodType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PodType::Ed25519 => write!(f, "Ed25519"),
            PodType::Ecdsa => write!(f, "Ecdsa"),
        }
    }
}
impl From<PodType> for TypedValue {
    fn from(t: PodType) -> Self {
        TypedValue::from(t as i64)
    }
}

// TODO remove this function and get it from
// https://github.com/0xPARC/pod2/blob/3c6930dfe61ce28f925bea942dcff839c910ddc7/src/backends/plonky2/mainpod/mod.rs#L584
// once it is exposed publicly (will be done at https://github.com/0xPARC/pod2/issues/294 ).
use pod2::backends::plonky2::{
    Error,
    basetypes::{D, F},
};
fn get_common_data(
    params: &pod2::middleware::Params,
) -> Result<plonky2::plonk::circuit_data::CommonCircuitData<F, D>, Error> {
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    let (_, circuit_data) = pod2::backends::plonky2::recursion::RecursiveCircuit::<
        pod2::backends::plonky2::circuits::mainpod::MainPodVerifyTarget,
    >::target_and_circuit_data_padded(
        params.max_input_recursive_pods,
        &rec_circuit_data.common,
        params,
    )?;
    Ok(circuit_data.common.clone())
}
