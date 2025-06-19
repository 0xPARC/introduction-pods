//ed25519pod.rs
use std::sync::LazyLock;

use base64::{Engine, prelude::BASE64_STANDARD};
use itertools::Itertools;
use plonky2::{
    field::types::Field,
    hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    },
    iop::{
        target::Target,
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
        basetypes::{C, D, Proof},
        circuits::{
            common::{
                CircuitBuilderPod, Flattenable, StatementArgTarget, StatementTarget, ValueTarget,
            },
            mainpod::CalculateIdGadget,
        },
        mainpod,
        mainpod::calculate_id,
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        self, AnchoredKey, DynError, EMPTY_HASH, F, Hash, KEY_TYPE, Key, NativePredicate, Params,
        Pod, PodId, RawValue, SELF, Statement, ToFields, Value,
    },
    timed,
};
use ssh_key::{SshSig, public::KeyData};

use crate::PodType;

const KEY_SIGNED_MSG: &str = "signed_msg";
const KEY_ED25519_PK: &str = "ed25519_pk";

// Standard message length for ED25519 pods (can be made configurable)
const SIGNED_DATA_LEN: usize = 108; // SIGNED_DATA_LEN = 108 u8 = 864 bits

static ED25519_VERIFY_DATA: LazyLock<(EDDSATargets, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_ed25519_verify().expect("successful build"));

fn build_ed25519_verify() -> Result<(EDDSATargets, CircuitData<F, C, D>)> {
    let config = CircuitConfig::wide_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ed25519_verify_target = make_verify_circuits(&mut builder, SIGNED_DATA_LEN);

    let data = timed!("Ed25519Verify build", builder.build::<C>());
    Ok((ed25519_verify_target, data))
}

#[derive(Clone, Debug)]
struct Ed25519PodVerifyTarget {
    vds_root: HashOutTarget,
    id: HashOutTarget,
    proof: ProofWithPublicInputsTarget<D>,
}

pub struct Ed25519PodVerifyInput {
    vds_root: Hash,
    id: PodId,
    proof: ProofWithPublicInputs<F, C, D>,
}

impl Ed25519PodVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>, params: &Params) -> Result<Self> {
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
        let msg_targets = bits_to_bytes_targets(builder, msg_bits);
        let pk_targets = bits_to_bytes_targets(builder, pk_bits);

        // Calculate statements and ID
        let statements = pub_self_statements_target(builder, params, &msg_targets, &pk_targets);
        let id = CalculateIdGadget {
            params: params.clone(),
        }
        .eval(builder, &statements);

        // Register the public inputs
        let vds_root = builder.add_virtual_hash();
        builder.register_public_inputs(&id.elements);
        builder.register_public_inputs(&vds_root.elements);

        measure_gates_end!(builder, measure);
        Ok(Ed25519PodVerifyTarget {
            vds_root,
            id,
            proof: proof_targ,
        })
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &Ed25519PodVerifyInput) -> Result<()> {
        pw.set_proof_with_pis_target(&self.proof, &input.proof)?;
        pw.set_hash_target(self.id, HashOut::from_vec(input.id.0.0.to_vec()))?;
        pw.set_target_arr(&self.vds_root.elements, &input.vds_root.0)?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct Ed25519Pod {
    params: Params,
    id: PodId,
    msg: Vec<u8>,
    pk: Vec<u8>,
    proof: Proof,
    vds_hash: Hash,
}

impl middleware::RecursivePod for Ed25519Pod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        let (_, circuit_data) = &*STANDARD_ED25519_POD_DATA;
        circuit_data.verifier_data().verifier_only
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vds_root(&self) -> Hash {
        self.vds_hash
    }
}

static STANDARD_ED25519_POD_DATA: LazyLock<(Ed25519PodVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build().expect("successful build"));

fn build() -> Result<(Ed25519PodVerifyTarget, CircuitData<F, C, D>)> {
    let params = &*pod2::backends::plonky2::DEFAULT_PARAMS;
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ed25519_pod_verify_target = Ed25519PodVerifyTarget::add_targets(&mut builder, params)?;
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
    fn _prove(
        params: &Params,
        vds_root: Hash,
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
            vds_root,
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
            vds_hash: EMPTY_HASH,
        })
    }

    #[allow(clippy::new_ret_no_self)]
    pub fn new(
        params: &Params,
        vds_root: Hash,
        raw_msg: &str,
        sig: &SshSig,
        namespace: &str,
    ) -> Result<Box<dyn Pod>, Box<DynError>> {
        Ok(Self::_prove(params, vds_root, raw_msg, sig, namespace).map(Box::new)?)
    }

    fn _verify(&self) -> Result<()> {
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
            .chain(EMPTY_HASH.0.iter()) // slot for the unused vds root
            .cloned()
            .collect_vec();

        circuit_data
            .verify(ProofWithPublicInputs {
                proof: self.proof.clone(),
                public_inputs,
            })
            .map_err(|e| Error::custom(format!("Ed25519Pod proof verification failure: {:?}", e)))
    }
}

impl Pod for Ed25519Pod {
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

// Helper function to convert bit targets to byte targets
fn bits_to_bytes_targets(builder: &mut CircuitBuilder<F, D>, bits: &[Target]) -> Vec<Target> {
    assert_eq!(bits.len() % 8, 0);
    let mut bytes = Vec::new();

    for chunk in bits.chunks(8) {
        // Convert 8 bits to a byte value
        let mut byte_val = builder.zero();
        let two = builder.two();
        let mut power = builder.one();

        // Little-endian bit order
        for i in 0..8 {
            let bit_val = builder.mul(chunk[7 - i], power);
            byte_val = builder.add(byte_val, bit_val);
            power = builder.mul(power, two);
        }

        bytes.push(byte_val);
    }

    bytes
}

fn type_statement() -> Statement {
    Statement::ValueOf(
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
        StatementTarget::new_native(builder, params, NativePredicate::ValueOf, &[ak_msg, value]);

    // Hash the public key
    let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pk.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_ED25519_PK).raw());
    let ak_pk = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&pk_hash.elements));
    let st_pk =
        StatementTarget::new_native(builder, params, NativePredicate::ValueOf, &[ak_pk, value]);

    vec![st_type, st_msg, st_pk]
}

fn pub_self_statements(msg: &[u8], pk: &[u8]) -> Vec<middleware::Statement> {
    let st_type = type_statement();

    // Hash the message
    let msg_fields: Vec<F> = msg.iter().map(|&b| F::from_canonical_u8(b)).collect();
    let msg_hash = PoseidonHash::hash_no_pad(&msg_fields);

    let st_msg = Statement::ValueOf(
        AnchoredKey::from((SELF, KEY_SIGNED_MSG)),
        Value::from(RawValue(msg_hash.elements)),
    );

    // Hash the public key
    let pk_fields: Vec<F> = pk.iter().map(|&b| F::from_canonical_u8(b)).collect();
    let pk_hash = PoseidonHash::hash_no_pad(&pk_fields);

    let st_pk = Statement::ValueOf(
        AnchoredKey::from((SELF, KEY_ED25519_PK)),
        Value::from(RawValue(pk_hash.elements)),
    );

    vec![st_type, st_msg, st_pk]
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use pod2::{self, frontend::MainPodBuilder, op};
    use ssh_key::SshSig;

    use super::*;

    #[test]
    fn test_ed25519_pod_with_mainpod_verify() -> Result<()> {
        let params = Params {
            max_input_signed_pods: 0,
            ..Default::default()
        };

        // Use the sample data from plonky2_ed25519
        let msg = "0xPARC\n";
        let namespace = "double-blind.xyz";
        let sig = SshSig::from_pem(include_bytes!("../test_keys/ed25519_example.sig")).unwrap();
        let vds_root = EMPTY_HASH;

        let ed25519_pod = timed!(
            "Ed25519Pod::new",
            Ed25519Pod::new(&params, vds_root, msg, &sig, namespace).unwrap()
        );

        ed25519_pod.verify().unwrap();

        // wrap the ed25519_pod in a 'MainPod' (RecursivePod)
        let main_ed25519_pod = pod2::frontend::MainPod {
            pod: (ed25519_pod.clone() as Box<dyn Any>)
                .downcast::<Ed25519Pod>()
                .unwrap(),
            public_statements: ed25519_pod.pub_statements(),
            params: params.clone(),
        };

        // now generate a new MainPod from the ed25519_pod
        let mut main_pod_builder = MainPodBuilder::new(&params);
        main_pod_builder.add_main_pod(main_ed25519_pod.clone());

        // add operation that ensures that the msg is as expected in the EcdsaPod
        let signed_data = build_ssh_signed_data(namespace, msg.as_bytes(), &sig);
        let msg_fields: Vec<F> = signed_data
            .iter()
            .map(|&b| F::from_canonical_u8(b))
            .collect();
        let msg_hash = PoseidonHash::hash_no_pad(&msg_fields);
        let msg_copy = main_pod_builder
            .pub_op(op!(
                new_entry,
                (KEY_SIGNED_MSG, Value::from(RawValue(msg_hash.elements)))
            ))
            .unwrap();
        main_pod_builder
            .pub_op(op!(eq, (&main_ed25519_pod, KEY_SIGNED_MSG), msg_copy))
            .unwrap();
        // perpetuate the pk
        main_pod_builder
            .pub_op(op!(copy, main_ed25519_pod.public_statements[2].clone()))
            .unwrap();

        let mut prover = pod2::backends::plonky2::mock::mainpod::MockProver {};
        let pod = main_pod_builder.prove(&mut prover, &params).unwrap();
        assert!(pod.pod.verify().is_ok());

        println!("going to prove the main_pod");
        let mut prover = mainpod::Prover {};
        let main_pod = main_pod_builder.prove(&mut prover, &params).unwrap();
        let pod = (main_pod.pod as Box<dyn Any>)
            .downcast::<mainpod::MainPod>()
            .unwrap();
        pod.verify().unwrap();

        Ok(())
    }

    #[test]
    fn test_ed25519_pod_only_verify() -> Result<()> {
        let params = Params {
            max_input_signed_pods: 0,
            ..Default::default()
        };

        // Use the sample data from plonky2_ed25519
        let msg = "0xPARC\n";
        let namespace = "double-blind.xyz";
        let sig = SshSig::from_pem(include_bytes!("../test_keys/ed25519_example.sig")).unwrap();
        let vds_root = EMPTY_HASH;

        let ed25519_pod = timed!(
            "Ed25519Pod::new",
            Ed25519Pod::new(&params, vds_root, msg, &sig, namespace).unwrap()
        );

        ed25519_pod.verify().unwrap();

        Ok(())
    }
}
