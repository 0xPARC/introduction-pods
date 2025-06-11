use std::sync::LazyLock;

use base64::{Engine, prelude::BASE64_STANDARD};
use pod2::{
    backends::plonky2::{basetypes::{C, D}, Error, Result}, middleware::{self, DynError, Hash, Params, Pod, PodId, Proof, F}, timed
};
use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::{CircuitConfig, CircuitData, VerifierOnlyCircuitData}};


pub struct RSATargets {
    // TODO implement RSATargets
}

fn make_verify_circuits(builder: &mut CircuitBuilder<F, D>, len: usize) -> RSATargets {
    panic!("make_verify_circuits not implemented");
}

// Standard message length for ED25519 pods (can be made configurable)
const SIGNED_DATA_LEN: usize = 108; // SIGNED_DATA_LEN = 108 u8 = 864 bits

static RSA_VERIFY_DATA: LazyLock<(RSATargets, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_rsa_verify().expect("successful build"));

fn build_rsa_verify() -> Result<(RSATargets, CircuitData<F, C, D>)> {
    let config = CircuitConfig::wide_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let rsa_verify_target = make_verify_circuits(&mut builder, SIGNED_DATA_LEN);

    let data = timed!("Ed25519Verify build", builder.build::<C>());
    Ok((rsa_verify_target, data))
}



#[derive(Clone, Debug)]
pub struct RsaPod {
    params: Params,
    id: PodId,
    msg: Vec<u8>,
    pk: Vec<u8>,
    proof: Proof,
    vds_hash: Hash,
}

impl middleware::RecursivePod for RsaPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        //let (_, circuit_data): (u32, &CircuitData<F, C, D>) = panic!("Rsa pod verification circuit data not available");//&*STANDARD_ED25519_POD_DATA;
        let (_, circuit_data) = &*RSA_VERIFY_DATA;
        circuit_data.verifier_data().verifier_only
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vds_root(&self) -> Hash {
        self.vds_hash
    }
}

impl RsaPod {
    fn _prove(/* TODO: args */) -> Result<RsaPod> {
        // TODO: implement
        panic!("RsaPod._prove not implemented");
    }

    fn _verify(&self/* TODO: args */) -> Result<()> {
        // TODO: implement
        panic!("RsaPod._verify not implemented");
    }
}

impl Pod for RsaPod {
    fn params(&self) -> &Params {
        &self.params
    }

    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify().map_err(Box::new)?)
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        pub_self_statements(&self.msg, &self.pk)
    }

    fn serialized_proof(&self) -> String {
        let mut buffer = Vec::new();
        use plonky2::util::serialization::Write;
        buffer.write_proof(&self.proof).unwrap();
        BASE64_STANDARD.encode(buffer)
    }
}

fn pub_self_statements(msg: &Vec<u8>, pk: &Vec<u8>) -> Vec<middleware::Statement> {
    /* TODO */
    panic!("pub_self_statements not implemented");
}