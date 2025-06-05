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
        Pod, PodId, RawValue, RecursivePod, SELF, Statement, ToFields, Value,
    },
    timed,
};
use ssh_key::SshSig;

use crate::PodType;

const KEY_SIGNED_MSG: &str = "signed_msg";
const KEY_ED25519_PK: &str = "ed25519_pk";
// Standard message length for ED25519 pods (can be made configurable)
const SIGNED_DATA_LEN: usize = 108; // SIGNED_DATA_LEN = 108 u8 = 864 bits

static EDDSA_VERIFY_DATA: LazyLock<(Ed25519VerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_ed25519_verify().expect("successful build"));

fn build_ed25519_verify() -> Result<(Ed25519VerifyTarget, CircuitData<F, C, D>)> {
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ed25519_verify_target = Ed25519VerifyTarget::add_targets(&mut builder)?;

    let data = timed!("Ed25519Verify build", builder.build::<C>());
    Ok((ed25519_verify_target, data))
}

/// Note: this circuit requires the CircuitConfig's standard_ecc_config or
/// wide_ecc_config.
struct Ed25519VerifyTarget(EDDSATargets);

impl Ed25519VerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "Ed25519VerifyTarget");
        let ed25519_targets = make_verify_circuits(builder, SIGNED_DATA_LEN);
        // register public inputs (msg & pk)
        dbg!(ed25519_targets.msg.len());
        dbg!(ed25519_targets.pk.len());
        dbg!(ed25519_targets.sig.len());
        for i in 0..(SIGNED_DATA_LEN * 8) {
            builder.register_public_input(ed25519_targets.msg[i].target);
        }
        for i in 0..256 {
            builder.register_public_input(ed25519_targets.pk[i].target);
        }

        measure_gates_end!(builder, measure);

        Ok(Ed25519VerifyTarget(ed25519_targets))
    }

    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        namespace: &str,
        msg: &[u8],
        pk: [u8; 32],
        sig: &SshSig,
    ) -> Result<()> {
        let signed_data = build_ssh_signed_data(namespace, msg, sig);
        fill_circuits::<F, D>(pw, &signed_data, sig.signature_bytes(), &pk, &self.0);
        Ok(())
    }
}

/// Build SSH signed data format
pub fn build_ssh_signed_data(namespace: &str, raw_msg: &[u8], ssh_sig: &SshSig) -> Vec<u8> {
    // Use the SSH library's built-in method to create the signed data
    ssh_key::SshSig::signed_data(namespace, ssh_sig.hash_alg(), raw_msg)
        .expect("failed to build SSH signed data")
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
        let (_, circuit_data) = &*EDDSA_VERIFY_DATA;
        let verifier_data_targ = builder.constant_verifier_data(&circuit_data.verifier_only);
        let proof_targ = builder.add_virtual_proof_with_pis(&circuit_data.common);
        builder.verify_proof::<C>(&proof_targ, &verifier_data_targ, &circuit_data.common);

        // calculate id
        let msg = &proof_targ.public_inputs[0..SIGNED_DATA_LEN * 8];
        let pk = &proof_targ.public_inputs[SIGNED_DATA_LEN * 8..SIGNED_DATA_LEN * 8 + 256];
        let statements = pub_self_statements_target(builder, params, msg, pk);
        let id = CalculateIdGadget {
            params: params.clone(),
        }
        .eval(builder, &statements);

        // register the public inputs
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
    pk: [u8; 32],
    proof: Proof,
    vds_hash: Hash,
}
impl<'a> middleware::RecursivePod for Ed25519Pod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        let (_, circuit_data) = &*STANDARD_EDDSA_POD_DATA;
        circuit_data.verifier_data().verifier_only
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vds_root(&self) -> Hash {
        self.vds_hash
    }
}

static STANDARD_EDDSA_POD_DATA: LazyLock<(Ed25519PodVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build().expect("successful build"));

fn build() -> Result<(Ed25519PodVerifyTarget, CircuitData<F, C, D>)> {
    let params = &*pod2::backends::plonky2::DEFAULT_PARAMS;
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ed25519_pod_verify_target = Ed25519PodVerifyTarget::add_targets(&mut builder, params)?;
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    pod2::backends::plonky2::recursion::pad_circuit(&mut builder, &rec_circuit_data.common);

    // use plonky2::gates::gate::GateRef;
    // builder.add_gate_to_gate_set(GateRef::new(
    //     plonky2::gates::exponentiation::ExponentiationGate::new(66),
    // ));

    let data = timed!("Ed25519Pod build", builder.build::<C>());
    assert_eq!(rec_circuit_data.common, data.common);
    Ok((ed25519_pod_verify_target, data))
}

impl Ed25519Pod {
    fn _prove(
        params: &Params,
        vds_root: Hash,
        namespace: &str,
        msg: &[u8],
        pk: [u8; 32],
        sig: &SshSig,
    ) -> Result<Ed25519Pod> {
        // 1. prove the Ed25519Verify circuit
        let (ed25519_verify_target, ed25519_circuit_data) = &*EDDSA_VERIFY_DATA;
        let mut pw = PartialWitness::<F>::new();
        ed25519_verify_target.set_targets(&mut pw, namespace, msg, pk, sig)?;

        let ed25519_verify_proof = timed!(
            "prove the ed25519 signature verification (Ed25519VerifyTarget)",
            ed25519_circuit_data.prove(pw)?
        );

        // 2. verify the ed25519_verify proof in a Ed25519PodVerifyTarget circuit

        let (ed25519_pod_target, circuit_data) = &*STANDARD_EDDSA_POD_DATA;

        let statements = pub_self_statements(msg, pk)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, params));

        // set targets
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
            msg: msg.to_vec(),
            pk,
            proof: proof_with_pis.proof,
            vds_hash: EMPTY_HASH,
        })
    }

    #[allow(clippy::new_ret_no_self)]
    pub fn new(
        params: &Params,
        vds_root: Hash,
        namespace: &str,
        msg: &[u8],
        pk: [u8; 32],
        sig: &SshSig,
    ) -> Result<Box<dyn RecursivePod>, Box<DynError>> {
        Ok(Self::_prove(params, vds_root, namespace, msg, pk, sig).map(Box::new)?)
    }

    fn _verify(&self) -> Result<()> {
        let statements = pub_self_statements(&self.msg, self.pk)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        let (_, circuit_data) = &*STANDARD_EDDSA_POD_DATA;

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
        pub_self_statements(&self.msg, self.pk)
    }

    fn serialized_proof(&self) -> String {
        let mut buffer = Vec::new();
        use plonky2::util::serialization::Write;
        buffer.write_proof(&self.proof).unwrap();
        BASE64_STANDARD.encode(buffer)
    }
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

    let msg_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(msg.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_SIGNED_MSG).raw());
    let ak_msg = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&msg_hash.elements));
    let st_msg =
        StatementTarget::new_native(builder, params, NativePredicate::ValueOf, &[ak_msg, value]);

    let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pk.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_ED25519_PK).raw());
    let ak_pk = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&pk_hash.elements));
    let st_pk =
        StatementTarget::new_native(builder, params, NativePredicate::ValueOf, &[ak_pk, value]);

    vec![st_type, st_msg, st_pk]
}

// compatible with the same method in-circuit (pub_self_statements_target)
fn pub_self_statements(msg: &[u8], pk: [u8; 32]) -> Vec<middleware::Statement> {
    let st_type = type_statement();

    // hash the msg as in-circuit
    let msg_fields: Vec<F> = msg.iter().map(|&b| F::from_canonical_u8(b)).collect();
    let msg_hash = PoseidonHash::hash_no_pad(&msg_fields);

    let st_msg = Statement::ValueOf(
        AnchoredKey::from((SELF, KEY_SIGNED_MSG)),
        Value::from(RawValue(msg_hash.elements)),
    );

    // hash the pk as in-circuit
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
    use ssh_key::public::KeyData;

    use super::*;

    #[test]
    fn test_ed25519_pod_verify() -> Result<()> {
        // first generate all the circuits data so that it does not need to be
        // computed at further stages of the test (affecting the time reports)
        timed!(
            "generate EDDSA_VERIFY, STANDARD_EDDSA_POD_DATA, STANDARD_REC_MAIN_POD_CIRCUIT",
            {
                let (_, _) = &*EDDSA_VERIFY_DATA;
                let (_, _) = &*STANDARD_EDDSA_POD_DATA;
                let _ = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
            }
        );

        let params = Params {
            max_input_signed_pods: 0,
            ..Default::default()
        };

        let msg = "0xPARC\n".as_bytes();
        let namespace = "double-blind.xyz";
        let sig = SshSig::from_pem(include_bytes!("../test_keys/ed25519_example.sig")).unwrap();
        let pk = match sig.public_key() {
            KeyData::Ed25519(pk) => pk,
            _ => {
                return Err(Error::custom(String::from(
                    "signature does not carry an Ed25519 key",
                )));
            }
        };
        let pk_bytes = pk.0;
        let vds_root = EMPTY_HASH;
        let ed25519_pod = timed!(
            "Ed25519Pod::new",
            Ed25519Pod::new(&params, vds_root, namespace, msg, pk_bytes, &sig).unwrap()
        );

        ed25519_pod.verify().unwrap();
        // pod2::measure_gates_print!();

        // wrap the ed25519_pod in a 'MainPod' (RecursivePod)
        let main_ed25519_pod = pod2::frontend::MainPod {
            pod: ed25519_pod.clone(),
            public_statements: ed25519_pod.pub_statements(),
            params: params.clone(),
        };

        // now generate a new MainPod from the ed25519_pod
        let mut main_pod_builder = MainPodBuilder::new(&params);
        main_pod_builder.add_main_pod(main_ed25519_pod.clone());

        let mut prover = pod2::backends::plonky2::mock::mainpod::MockProver {};
        let pod = main_pod_builder.prove(&mut prover, &params).unwrap();
        assert!(pod.pod.verify().is_ok());

        println!("going to prove the main_pod");
        let mut prover = mainpod::Prover {};
        let main_pod = timed!(
            "main_pod_builder.prove",
            main_pod_builder.prove(&mut prover, &params).unwrap()
        );
        let pod = (main_pod.pod as Box<dyn Any>)
            .downcast::<mainpod::MainPod>()
            .unwrap();
        pod.verify().unwrap();

        Ok(())
    }
}
