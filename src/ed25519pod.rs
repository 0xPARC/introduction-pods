//! Implements the Ed25519Pod, a POD that proves that the given `pk` has signed
//! the `msg` with the Ed25519 signature scheme.
//!
//! This POD is build through two steps:
//! - first it generates a plonky2 proof of correct signature verification
//! - then, verifies the previous proof in a new plonky2 proof, using the
//!   `standard_recursion_config`, padded to match the `RecursiveCircuit<MainPod>`
//!   configuration.

use std::{any::Any, sync::LazyLock};

use itertools::Itertools;
use plonky2::{
    field::types::Field,
    hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    },
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData, VerifierOnlyCircuitData},
        config::Hasher,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};
use plonky2_ed25519::gadgets::eddsa::{EDDSATargets, fill_circuits, make_verify_circuits};
use pod2::{
    backends::plonky2::{
        Error, Result,
        basetypes::{C, D, Proof, VDSet},
        circuits::{
            common::{
                CircuitBuilderPod, Flattenable, StatementArgTarget, StatementTarget, ValueTarget,
            },
            mainpod::CalculateIdGadget,
        },
        deserialize_proof, mainpod,
        mainpod::{calculate_id, get_common_data},
        serialize_proof,
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        self, AnchoredKey, F, Hash, KEY_TYPE, Key, NativePredicate, Params, Pod, PodId, RawValue,
        RecursivePod, SELF, Statement, ToFields, Value,
    },
    timed,
};
use serde::{Deserialize, Serialize};
use ssh_key::{SshSig, public::KeyData};

use crate::{PodType, gadgets::bits_bytes::reversed_bits_to_bytes_be};

const KEY_SIGNED_MSG: &str = "signed_msg";
const KEY_ED25519_PK: &str = "ed25519_pk";

/// Standard message length for ED25519 pods (can be made configurable)
const SIGNED_DATA_LEN: usize = 108; // SIGNED_DATA_LEN = 108 u8 = 864 bits

/// targets and circuit_data of the circuit that verifies ed25519 signatures
static ED25519_VERIFY_DATA: LazyLock<(EDDSATargets, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_ed25519_verify().expect("successful build"));

fn build_ed25519_verify() -> Result<(EDDSATargets, CircuitData<F, C, D>)> {
    let config = CircuitConfig::wide_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ed25519_verify_target = make_verify_circuits(&mut builder, SIGNED_DATA_LEN);

    let data = timed!("Ed25519Verify build", builder.build::<C>());
    Ok((ed25519_verify_target, data))
}

/// Circuit that verifies a proof generated from the Ed25519_VERIFY_DATA circuit.
#[derive(Clone, Debug)]
struct Ed25519PodVerifyTarget {
    vd_root: HashOutTarget,
    id: HashOutTarget,
    proof: ProofWithPublicInputsTarget<D>,
}

pub struct Ed25519PodVerifyInput {
    vd_root: Hash,
    id: PodId,
    proof: ProofWithPublicInputs<F, C, D>,
}

impl Ed25519PodVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>, params: &Params) -> Self {
        let measure = measure_gates_begin!(builder, "Ed25519PodVerifyTarget");

        // Verify Ed25519VerifyTarget's proof (with verifier_data hardcoded as constant)
        let (_, circuit_data) = &*ED25519_VERIFY_DATA;
        let verifier_data_targ = builder.constant_verifier_data(&circuit_data.verifier_only);
        let proof_targ = builder.add_virtual_proof_with_pis(&circuit_data.common);
        builder.verify_proof::<C>(&proof_targ, &verifier_data_targ, &circuit_data.common);

        // Extract message and public key from public inputs
        // The message is the first SIGNED_DATA_LEN*8 bits, and pk is registered after
        let msg_bits = &proof_targ.public_inputs[0..SIGNED_DATA_LEN * 8];
        let pk_bits = &proof_targ.public_inputs[SIGNED_DATA_LEN * 8..SIGNED_DATA_LEN * 8 + 256];

        // Convert bits to bytes for hashing (group by 8 bits)
        let msg_targets = reversed_bits_to_bytes_be(
            builder,
            &msg_bits
                .iter()
                .rev()
                .map(|b| BoolTarget::new_unsafe(*b)) // assuming that msg_bits contains only {0, 1}
                .collect::<Vec<_>>(),
        );
        let pk_targets = reversed_bits_to_bytes_be(
            builder,
            &pk_bits
                .iter()
                .rev()
                .map(|b| BoolTarget::new_unsafe(*b)) // assuming that pk_bits contains only {0, 1}
                .collect::<Vec<_>>(),
        );

        // Calculate statements and ID
        let statements = pub_self_statements_target(builder, params, &msg_targets, &pk_targets);
        let id = CalculateIdGadget {
            params: params.clone(),
        }
        .eval(builder, &statements);

        // Register the public inputs
        let vd_root = builder.add_virtual_hash();
        builder.register_public_inputs(&id.elements);
        builder.register_public_inputs(&vd_root.elements);

        measure_gates_end!(builder, measure);
        Ed25519PodVerifyTarget {
            vd_root,
            id,
            proof: proof_targ,
        }
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &Ed25519PodVerifyInput) -> Result<()> {
        pw.set_proof_with_pis_target(&self.proof, &input.proof)?;
        pw.set_hash_target(self.id, HashOut::from_vec(input.id.0.0.to_vec()))?;
        pw.set_target_arr(&self.vd_root.elements, &input.vd_root.0)?;

        Ok(())
    }
}

/// Ed25519Pod implements the trait RecursivePod
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ed25519Pod {
    params: Params,
    id: PodId,
    msg: Vec<u8>,
    pk: Vec<u8>,
    proof: Proof,
    vd_set: VDSet,
}

impl RecursivePod for Ed25519Pod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        let (_, circuit_data) = &*STANDARD_ED25519_POD_DATA;
        circuit_data.verifier_data().verifier_only
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vd_set(&self) -> &VDSet {
        &self.vd_set
    }
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vd_set: VDSet,
        id: PodId,
    ) -> Result<Box<dyn RecursivePod>> {
        let data: Data = serde_json::from_value(data)?;
        let common = get_common_data(&params)?;
        let proof = deserialize_proof(&common, &data.proof)?;
        Ok(Box::new(Self {
            params,
            id,
            msg: data.msg,
            pk: data.pk,
            proof,
            vd_set,
        }))
    }
}

impl Pod for Ed25519Pod {
    fn params(&self) -> &Params {
        &self.params
    }

    fn verify(&self) -> Result<()> {
        let statements = pub_self_statements(&self.msg, &self.pk)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        let (_, circuit_data) = &*STANDARD_ED25519_POD_DATA;

        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(self.vd_set().root().0.iter())
            .cloned()
            .collect_vec();

        circuit_data
            .verify(ProofWithPublicInputs {
                proof: self.proof.clone(),
                public_inputs,
            })
            .map_err(|e| Error::custom(format!("Ed25519Pod proof verification failure: {:?}", e)))
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::Ed25519 as usize, "Ed25519")
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        pub_self_statements(&self.msg, &self.pk)
    }

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::to_value(Data {
            proof: serialize_proof(&self.proof),
            msg: self.msg.clone(),
            pk: self.pk.clone(),
        })
        .expect("serialization to json")
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn Pod) -> bool {
        if let Some(other) = other.as_any().downcast_ref::<Ed25519Pod>() {
            self == other
        } else {
            false
        }
    }
}

#[derive(Serialize, Deserialize)]
struct Data {
    msg: Vec<u8>,
    pk: Vec<u8>,
    proof: String,
}

static STANDARD_ED25519_POD_DATA: LazyLock<(Ed25519PodVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build().expect("successful build"));

fn build() -> Result<(Ed25519PodVerifyTarget, CircuitData<F, C, D>)> {
    let params = &*pod2::backends::plonky2::DEFAULT_PARAMS;

    // use pod2's recursion config as config for the introduction pod; which if
    // the zk feature enabled, it will have the zk property enabled
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    let config = rec_circuit_data.common.config.clone();

    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ed25519_pod_verify_target = Ed25519PodVerifyTarget::add_targets(&mut builder, params);
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    pod2::backends::plonky2::recursion::pad_circuit(&mut builder, &rec_circuit_data.common);

    let data = timed!("Ed25519Pod build", builder.build::<C>());
    assert_eq!(rec_circuit_data.common, data.common);
    Ok((ed25519_pod_verify_target, data))
}

/// Build SSH signed data format
pub fn build_ssh_signed_data(namespace: &str, raw_msg: &[u8], ssh_sig: &SshSig) -> Vec<u8> {
    // Use the SSH library's built-in method to create the signed data
    ssh_key::SshSig::signed_data(namespace, ssh_sig.hash_alg(), raw_msg)
        .expect("failed to build SSH signed data")
}

impl Ed25519Pod {
    fn new(
        params: &Params,
        vd_set: &VDSet,
        raw_msg: &str,
        sig: &SshSig,
        namespace: &str,
    ) -> Result<Ed25519Pod> {
        // 1. Prove the Ed25519Verify circuit
        let (ed25519_verify_target, ed25519_circuit_data) = &*ED25519_VERIFY_DATA;
        let mut pw = PartialWitness::<F>::new();
        let signed_data = build_ssh_signed_data(namespace, raw_msg.as_bytes(), sig);

        let pk = match sig.public_key() {
            KeyData::Ed25519(pk) => pk,
            _ => {
                return Err(Error::custom(String::from(
                    "signature does not carry an Ed25519 key",
                )));
            }
        };

        fill_circuits::<F, 2>(
            &mut pw,
            &signed_data,
            sig.signature_bytes(),
            pk.as_ref(),
            ed25519_verify_target,
        );

        let ed25519_verify_proof = timed!(
            "prove the ed25519 signature verification (Ed25519VerifyTarget)",
            ed25519_circuit_data.prove(pw)?
        );

        // 2. Verify the ed25519_verify proof in a Ed25519PodVerifyTarget circuit
        let (ed25519_pod_target, circuit_data) = &*STANDARD_ED25519_POD_DATA;

        let statements = pub_self_statements(signed_data.as_slice(), pk.as_ref())
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, params));

        // Set targets
        let input = Ed25519PodVerifyInput {
            vd_root: vd_set.root(),
            id,
            proof: ed25519_verify_proof,
        };
        let mut pw = PartialWitness::<F>::new();
        ed25519_pod_target.set_targets(&mut pw, &input)?;
        let proof_with_pis = timed!(
            "prove the ed25519-verification proof verification (Ed25519Pod proof)",
            circuit_data.prove(pw)?
        );

        #[cfg(test)] // sanity check
        {
            circuit_data
                .verifier_data()
                .verify(proof_with_pis.clone())?;
        }

        Ok(Ed25519Pod {
            params: params.clone(),
            id,
            msg: signed_data,
            pk: pk.as_ref().to_vec(),
            proof: proof_with_pis.proof,
            vd_set: vd_set.clone(),
        })
    }

    pub fn new_boxed(
        params: &Params,
        vd_set: &VDSet,
        raw_msg: &str,
        sig: &SshSig,
        namespace: &str,
    ) -> Result<Box<dyn RecursivePod>> {
        Ok(Self::new(params, vd_set, raw_msg, sig, namespace).map(Box::new)?)
    }
}

fn type_statement() -> Statement {
    Statement::equal(
        AnchoredKey::from((SELF, KEY_TYPE)),
        Value::from(PodType::Ed25519),
    )
}

fn pub_self_statements_target(
    builder: &mut CircuitBuilder<F, D>,
    params: &Params,
    msg: &[Target],
    pk: &[Target],
) -> Vec<StatementTarget> {
    let st_type = StatementTarget::from_flattened(
        params,
        &builder.constants(&type_statement().to_fields(params)),
    );

    let ak_podid = builder.constant_value(RawValue::from(SELF.0));

    // Hash the message
    let msg_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(msg.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_SIGNED_MSG).raw());
    let ak_msg = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&msg_hash.elements));
    let st_msg =
        StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak_msg, value]);

    // Hash the public key
    let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pk.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_ED25519_PK).raw());
    let ak_pk = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&pk_hash.elements));
    let st_pk =
        StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak_pk, value]);

    vec![st_type, st_msg, st_pk]
}

// compatible with the same method in-circuit (pub_self_statements_target)
fn pub_self_statements(msg: &[u8], pk: &[u8]) -> Vec<middleware::Statement> {
    let st_type = type_statement();

    // Hash the message
    let msg_fields: Vec<F> = msg.iter().map(|&b| F::from_canonical_u8(b)).collect();
    let msg_hash = PoseidonHash::hash_no_pad(&msg_fields);

    let st_msg = Statement::equal(
        AnchoredKey::from((SELF, KEY_SIGNED_MSG)),
        Value::from(RawValue(msg_hash.elements)),
    );

    // Hash the public key
    let pk_fields: Vec<F> = pk.iter().map(|&b| F::from_canonical_u8(b)).collect();
    let pk_hash = PoseidonHash::hash_no_pad(&pk_fields);

    let st_pk = Statement::equal(
        AnchoredKey::from((SELF, KEY_ED25519_PK)),
        Value::from(RawValue(pk_hash.elements)),
    );

    vec![st_type, st_msg, st_pk]
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use pod2::{self, middleware::VDSet};
    use ssh_key::SshSig;

    use super::*;

    fn get_test_ed25519_pod(
        namespace: &str,
        msg: &str,
        sig: &SshSig,
    ) -> Result<(Box<dyn RecursivePod>, Params, VDSet)> {
        let params = Params {
            max_input_signed_pods: 0,
            ..Default::default()
        };

        let vds = vec![
            pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA
                .verifier_only
                .clone(),
            pod2::backends::plonky2::emptypod::STANDARD_EMPTY_POD_DATA
                .1
                .verifier_only
                .clone(),
            STANDARD_ED25519_POD_DATA.1.verifier_only.clone(),
        ];
        let vdset = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

        let ed25519_pod = timed!(
            "Ed25519Pod::new",
            Ed25519Pod::new_boxed(&params, &vdset, &msg, &sig, &namespace).unwrap()
        );

        Ok((ed25519_pod, params, vdset))
    }

    #[test]
    #[ignore] // this is for the GitHub CI, it takes too long and the CI would fail.
    fn test_ed25519_pod_with_mainpod_verify() -> Result<()> {
        // Use the sample data from plonky2_ed25519
        let msg = "0xPARC\n";
        let namespace = "double-blind.xyz";
        let sig = SshSig::from_pem(include_bytes!("../test_keys/ed25519_example.sig")).unwrap();

        let (ed25519_pod, params, vdset) = get_test_ed25519_pod(namespace, msg, &sig)?;

        // prepare the msg_hash as it will be checked in the 2nd iteration
        // MainPod in the pod operation
        let signed_data = build_ssh_signed_data(namespace, msg.as_bytes(), &sig);
        let msg_fields: Vec<F> = signed_data
            .iter()
            .map(|&b| F::from_canonical_u8(b))
            .collect();
        let msg_hash = PoseidonHash::hash_no_pad(&msg_fields);

        crate::tests::test_introduction_pod_signature_flow(
            ed25519_pod,
            params,
            vdset,
            KEY_SIGNED_MSG,
            msg_hash,
        )?;

        Ok(())
    }

    #[test]
    #[ignore] // this is for the GitHub CI, it takes too long and the CI would fail.
    fn test_serialization() -> Result<()> {
        // Use the sample data from plonky2_ed25519
        let msg = "0xPARC\n";
        let namespace = "double-blind.xyz";
        let sig = SshSig::from_pem(include_bytes!("../test_keys/ed25519_example.sig")).unwrap();

        let (ed25519_pod, params, vdset) = get_test_ed25519_pod(namespace, msg, &sig)?;

        ed25519_pod.verify().unwrap();

        let ed25519_pod = (ed25519_pod as Box<dyn Any>)
            .downcast::<Ed25519Pod>()
            .unwrap();
        let data = ed25519_pod.serialize_data();
        let recovered_ecdsa_pod =
            Ed25519Pod::deserialize_data(params, data, vdset, ed25519_pod.id).unwrap();
        let recovered_ed25519_pod = (recovered_ecdsa_pod as Box<dyn Any>)
            .downcast::<Ed25519Pod>()
            .unwrap();

        assert_eq!(recovered_ed25519_pod, ed25519_pod);

        Ok(())
    }
}
