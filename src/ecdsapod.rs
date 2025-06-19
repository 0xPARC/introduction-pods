//! Implements the EcdsaPod, a POD that proves that the given `pk` has signed
//! the `msg` with the ECDSA over Secp256k1 signature scheme.
//!
//! This POD is build through two steps:
//! - first it generates a plonky2 proof of correct signature verification,
//!   using the `standard_ecc_config` (136 wires)
//! - then, verifies the previous proof in a new plonky2 proof, using the
//!   `standard_recursion_config` (135 wires), padded to match the
//!   `RecursiveCircuit<MainPod>` configuration.

use std::sync::LazyLock;

use itertools::Itertools;
use num::bigint::BigUint;
use plonky2::{
    field::{secp256k1_scalar::Secp256K1Scalar, types::Field},
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
use plonky2_ecdsa::{
    curve::{
        ecdsa::{ECDSAPublicKey, ECDSASignature},
        secp256k1::Secp256K1,
    },
    gadgets::{
        biguint::WitnessBigUint,
        curve::CircuitBuilderCurve,
        ecdsa::{ECDSAPublicKeyTarget, ECDSASignatureTarget, verify_message_circuit},
        nonnative::{CircuitBuilderNonNative, NonNativeTarget},
    },
};
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
        deserialize_proof, mainpod,
        mainpod::{calculate_id, get_common_data},
        serialize_proof,
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        self, AnchoredKey, DynError, F, Hash, KEY_TYPE, Key, NativePredicate, Params, Pod, PodId,
        RawValue, RecursivePod, SELF, Statement, ToFields, Value,
    },
    timed,
};
use serde::{Deserialize, Serialize};

use crate::PodType;

const KEY_SIGNED_MSG: &str = "signed_msg";
const KEY_ECDSA_PK: &str = "ecdsa_pk";

static ECDSA_VERIFY_DATA: LazyLock<(EcdsaVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_ecdsa_verify().expect("successful build"));

fn build_ecdsa_verify() -> Result<(EcdsaVerifyTarget, CircuitData<F, C, D>)> {
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ecdsa_verify_target = EcdsaVerifyTarget::add_targets(&mut builder)?;

    let data = timed!("EcdsaVerify build", builder.build::<C>());
    Ok((ecdsa_verify_target, data))
}

/// Note: this circuit requires the CircuitConfig's standard_ecc_config or
/// wide_ecc_config.
struct EcdsaVerifyTarget {
    msg: NonNativeTarget<Secp256K1Scalar>,
    pk: ECDSAPublicKeyTarget<Secp256K1>,
    signature: ECDSASignatureTarget<Secp256K1>,
}

impl EcdsaVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "EcdsaVerifyTarget");
        let msg = builder.add_virtual_nonnative_target::<Secp256K1Scalar>();
        let pk = ECDSAPublicKeyTarget(builder.add_virtual_affine_point_target::<Secp256K1>());
        let r = builder.add_virtual_nonnative_target();
        let s = builder.add_virtual_nonnative_target();
        let sig = ECDSASignatureTarget::<Secp256K1> { r, s };

        verify_message_circuit(builder, msg.clone(), sig.clone(), pk.clone());

        // register public inputs
        for l in msg.value.limbs.iter() {
            builder.register_public_input(l.0);
        }
        // register pk as public input
        for l in pk.0.x.value.limbs.iter() {
            builder.register_public_input(l.0);
        }
        for l in pk.0.y.value.limbs.iter() {
            builder.register_public_input(l.0);
        }

        measure_gates_end!(builder, measure);
        Ok(EcdsaVerifyTarget {
            msg,
            pk,
            signature: sig,
        })
    }

    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        msg: Secp256K1Scalar,
        pk: ECDSAPublicKey<Secp256K1>,
        signature: ECDSASignature<Secp256K1>,
    ) -> Result<()> {
        pw.set_biguint_target(
            &self.msg.value,
            &biguint_from_array(std::array::from_fn(|i| msg.0[i])),
        )?;
        pw.set_biguint_target(&self.pk.0.x.value, &biguint_from_array(pk.0.x.0))?;
        pw.set_biguint_target(&self.pk.0.y.value, &biguint_from_array(pk.0.y.0))?;
        pw.set_biguint_target(&self.signature.r.value, &biguint_from_array(signature.r.0))?;
        pw.set_biguint_target(&self.signature.s.value, &biguint_from_array(signature.s.0))?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
struct EcdsaPodVerifyTarget {
    vds_root: HashOutTarget,
    id: HashOutTarget,
    proof: ProofWithPublicInputsTarget<D>,
}

pub struct EcdsaPodVerifyInput {
    vds_root: Hash,
    id: PodId,
    proof: ProofWithPublicInputs<F, C, D>,
}
impl EcdsaPodVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>, params: &Params) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "EcdsaPodVerifyTarget");

        // Verify EcdsaVerifyTarget's proof (with verifier_data hardcoded as constant)
        let (_, circuit_data) = &*ECDSA_VERIFY_DATA;
        let verifier_data_targ = builder.constant_verifier_data(&circuit_data.verifier_only);
        let proof_targ = builder.add_virtual_proof_with_pis(&circuit_data.common);
        builder.verify_proof::<C>(&proof_targ, &verifier_data_targ, &circuit_data.common);

        // calculate id
        let msg = &proof_targ.public_inputs[0..8];
        let pk = &proof_targ.public_inputs[8..24];
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
        Ok(EcdsaPodVerifyTarget {
            vds_root,
            id,
            proof: proof_targ,
        })
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &EcdsaPodVerifyInput) -> Result<()> {
        pw.set_proof_with_pis_target(&self.proof, &input.proof)?;
        pw.set_hash_target(self.id, HashOut::from_vec(input.id.0.0.to_vec()))?;
        pw.set_target_arr(&self.vds_root.elements, &input.vds_root.0)?;

        Ok(())
    }
}

/// EcdsaPod implements the trait RecursivePod
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EcdsaPod {
    params: Params,
    id: PodId,
    msg: Secp256K1Scalar,
    pk: ECDSAPublicKey<Secp256K1>,
    proof: Proof,
    vds_root: Hash,
}

impl RecursivePod for EcdsaPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        let (_, circuit_data) = &*STANDARD_ECDSA_POD_DATA;
        circuit_data.verifier_data().verifier_only
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vds_root(&self) -> Hash {
        self.vds_root
    }
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vds_root: Hash,
        id: PodId,
    ) -> Result<Box<dyn RecursivePod>, Box<DynError>> {
        let data: Data = serde_json::from_value(data)?;
        let common = get_common_data(&params)?;
        let proof = deserialize_proof(&common, &data.proof)?;
        Ok(Box::new(Self {
            params,
            id,
            msg: data.msg,
            pk: data.pk,
            proof,
            vds_root,
        }))
    }
}

impl Pod for EcdsaPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify().map_err(Box::new)?)
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::Ecdsa as usize, "Ecdsa")
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        pub_self_statements(self.msg, self.pk)
    }

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::to_value(Data {
            proof: serialize_proof(&self.proof),
            msg: self.msg,
            pk: self.pk,
        })
        .expect("serialization to json")
    }
}

#[derive(Serialize, Deserialize)]
struct Data {
    msg: Secp256K1Scalar,
    pk: ECDSAPublicKey<Secp256K1>,
    proof: String,
}

static STANDARD_ECDSA_POD_DATA: LazyLock<(EcdsaPodVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build().expect("successful build"));

fn build() -> Result<(EcdsaPodVerifyTarget, CircuitData<F, C, D>)> {
    let params = &*pod2::backends::plonky2::DEFAULT_PARAMS;
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    let config = rec_circuit_data.common.config.clone();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ecdsa_pod_verify_target = EcdsaPodVerifyTarget::add_targets(&mut builder, params)?;
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    pod2::backends::plonky2::recursion::pad_circuit(&mut builder, &rec_circuit_data.common);

    let data = timed!("EcdsaPod build", builder.build::<C>());
    assert_eq!(rec_circuit_data.common, data.common);
    Ok((ecdsa_pod_verify_target, data))
}

impl EcdsaPod {
    fn _prove(
        params: &Params,
        vds_root: Hash,
        msg: Secp256K1Scalar,
        pk: ECDSAPublicKey<Secp256K1>,
        signature: ECDSASignature<Secp256K1>,
    ) -> Result<EcdsaPod> {
        // 1. prove the EcdsaVerify circuit
        let (ecdsa_verify_target, ecdsa_circuit_data) = &*ECDSA_VERIFY_DATA;
        let mut pw = PartialWitness::<F>::new();
        ecdsa_verify_target.set_targets(&mut pw, msg, pk, signature)?;

        let ecdsa_verify_proof = timed!(
            "prove the ecdsa signature verification (EcdsaVerifyTarget)",
            ecdsa_circuit_data.prove(pw)?
        );

        // sanity check
        ecdsa_circuit_data
            .verifier_data()
            .verify(ecdsa_verify_proof.clone())?;

        // 2. verify the ecdsa_verify proof in a EcdsaPodVerifyTarget circuit

        let (ecdsa_pod_target, circuit_data) = &*STANDARD_ECDSA_POD_DATA;

        let statements = pub_self_statements(msg, pk)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, params));

        // set targets
        let input = EcdsaPodVerifyInput {
            vds_root,
            id,
            proof: ecdsa_verify_proof,
        };
        let mut pw = PartialWitness::<F>::new();
        ecdsa_pod_target.set_targets(&mut pw, &input)?;
        let proof_with_pis = timed!(
            "prove the ecdsa-verification proof verification (EcdsaPod proof)",
            circuit_data.prove(pw)?
        );

        // sanity check
        circuit_data
            .verifier_data()
            .verify(proof_with_pis.clone())?;

        Ok(EcdsaPod {
            params: params.clone(),
            id,
            msg,
            pk,
            proof: proof_with_pis.proof,
            vds_root,
        })
    }

    #[allow(clippy::new_ret_no_self)]
    pub fn new(
        params: &Params,
        vds_root: Hash,
        msg: Secp256K1Scalar,
        pk: ECDSAPublicKey<Secp256K1>,
        signature: ECDSASignature<Secp256K1>,
    ) -> Result<Box<dyn RecursivePod>, Box<DynError>> {
        Ok(Self::_prove(params, vds_root, msg, pk, signature).map(Box::new)?)
    }

    fn _verify(&self) -> Result<()> {
        let statements = pub_self_statements(self.msg, self.pk)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        let (_, circuit_data) = &*STANDARD_ECDSA_POD_DATA;

        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(self.vds_root().0.iter())
            .cloned()
            .collect_vec();

        circuit_data
            .verify(ProofWithPublicInputs {
                proof: self.proof.clone(),
                public_inputs,
            })
            .map_err(|e| Error::custom(format!("EcdsaPod proof verification failure: {:?}", e)))
    }
}

fn type_statement() -> Statement {
    Statement::equal(
        AnchoredKey::from((SELF, KEY_TYPE)),
        Value::from(PodType::Ecdsa),
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
        StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak_msg, value]);

    let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pk.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_ECDSA_PK).raw());
    let ak_pk = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&pk_hash.elements));
    let st_pk =
        StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak_pk, value]);

    vec![st_type, st_msg, st_pk]
}

// compatible with the same method in-circuit (pub_self_statements_target)
fn pub_self_statements(
    msg: Secp256K1Scalar,
    pk: ECDSAPublicKey<Secp256K1>,
) -> Vec<middleware::Statement> {
    let st_type = type_statement();

    // hash the msg as in-circuit
    let msg_limbs = secp_field_to_limbs(msg.0);
    let msg_hash = PoseidonHash::hash_no_pad(&msg_limbs);

    let st_msg = Statement::equal(
        AnchoredKey::from((SELF, KEY_SIGNED_MSG)),
        Value::from(RawValue(msg_hash.elements)),
    );

    // hash the pk as in-circuit
    let pk_x_limbs = secp_field_to_limbs(pk.0.x.0);
    let pk_y_limbs = secp_field_to_limbs(pk.0.y.0);
    let pk_hash = PoseidonHash::hash_no_pad(&[pk_x_limbs, pk_y_limbs].concat());

    let st_pk = Statement::equal(
        AnchoredKey::from((SELF, KEY_ECDSA_PK)),
        Value::from(RawValue(pk_hash.elements)),
    );

    vec![st_type, st_msg, st_pk]
}

fn secp_field_to_limbs(v: [u64; 4]) -> Vec<F> {
    let max_num_limbs = 8;
    let v_biguint = biguint_from_array(std::array::from_fn(|i| v[i]));
    let mut limbs = v_biguint.to_u32_digits();
    assert!(max_num_limbs >= limbs.len());
    limbs.resize(max_num_limbs, 0);
    let limbs_f: Vec<F> = limbs.iter().map(|l| F::from_canonical_u32(*l)).collect();
    limbs_f
}

fn biguint_from_array(arr: [u64; 4]) -> BigUint {
    BigUint::from_slice(&[
        arr[0] as u32,
        (arr[0] >> 32) as u32,
        arr[1] as u32,
        (arr[1] >> 32) as u32,
        arr[2] as u32,
        (arr[2] >> 32) as u32,
        arr[3] as u32,
        (arr[3] >> 32) as u32,
    ])
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use plonky2_ecdsa::curve::{
        curve_types::{Curve, CurveScalar},
        ecdsa::{ECDSAPublicKey, ECDSASecretKey, ECDSASignature, sign_message},
        secp256k1::Secp256K1,
    };
    use pod2::{self, frontend::MainPodBuilder, middleware::VDSet, op};

    use super::*;

    /// test to ensure that the pub_self_statements methods match between the
    /// in-circuit and the out-circuit implementations
    #[test]
    fn test_pub_self_statements_target() -> Result<()> {
        let params = &Default::default();

        let msg = Secp256K1Scalar([321, 654, 987, 321]);
        let sk = ECDSASecretKey::<Secp256K1>(Secp256K1Scalar([123, 456, 789, 123]));
        let pk: ECDSAPublicKey<Secp256K1> =
            ECDSAPublicKey((CurveScalar(sk.0) * Secp256K1::GENERATOR_PROJECTIVE).to_affine());
        let st = pub_self_statements(msg, pk)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id_hash: HashOut<F> = HashOut::<F>::from_vec(
            pod2::backends::plonky2::mainpod::calculate_id(&st, params)
                .0
                .to_vec(),
        );

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        // add targets
        let msg_targ = builder.add_virtual_nonnative_target::<Secp256K1Scalar>();
        let pk_targ = ECDSAPublicKeyTarget(builder.add_virtual_affine_point_target::<Secp256K1>());
        let expected_id = builder.add_virtual_hash();

        // set values to targets
        pw.set_biguint_target(
            &msg_targ.value,
            &biguint_from_array(std::array::from_fn(|i| msg.0[i])),
        )?;
        pw.set_biguint_target(&pk_targ.0.x.value, &biguint_from_array(pk.0.x.0))?;
        pw.set_biguint_target(&pk_targ.0.y.value, &biguint_from_array(pk.0.y.0))?;
        pw.set_hash_target(expected_id, id_hash)?;

        let msg_field_targ: Vec<Target> = msg_targ.value.limbs.iter().map(|l| l.0).collect();
        let pk_x_field_targ: Vec<Target> = pk_targ.0.x.value.limbs.iter().map(|l| l.0).collect();
        let pk_y_field_targ: Vec<Target> = pk_targ.0.y.value.limbs.iter().map(|l| l.0).collect();
        let pk_field_targ: Vec<Target> = [pk_x_field_targ, pk_y_field_targ].concat();
        let st_targ =
            pub_self_statements_target(&mut builder, params, &msg_field_targ, &pk_field_targ);
        let id_targ = CalculateIdGadget {
            params: params.clone(),
        }
        .eval(&mut builder, &st_targ);

        builder.connect_hashes(expected_id, id_targ);

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }

    fn compute_new_ecdsa_pod(
        sk: ECDSASecretKey<Secp256K1>,
        msg: Secp256K1Scalar,
    ) -> Result<(Box<dyn RecursivePod>, Params, VDSet)> {
        // first generate all the circuits data so that it does not need to be
        // computed at further stages of the test (affecting the time reports)
        timed!(
            "generate ECDSA_VERIFY, STANDARD_ECDSA_POD_DATA, STANDARD_REC_MAIN_POD_CIRCUIT",
            {
                let (_, _) = &*ECDSA_VERIFY_DATA;
                let (_, _) = &*STANDARD_ECDSA_POD_DATA;
                let _ = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
            }
        );
        let params = Params {
            max_input_signed_pods: 0,
            ..Default::default()
        };

        // compute the pk & signature
        let pk: ECDSAPublicKey<Secp256K1> =
            ECDSAPublicKey((CurveScalar(sk.0) * Secp256K1::GENERATOR_PROJECTIVE).to_affine());
        let signature: ECDSASignature<Secp256K1> = sign_message(msg, sk);

        let vds = vec![
            pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA
                .verifier_only
                .clone(),
            pod2::backends::plonky2::emptypod::STANDARD_EMPTY_POD_DATA
                .1
                .verifier_only
                .clone(),
            STANDARD_ECDSA_POD_DATA.1.verifier_only.clone(),
        ];
        let vdset = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

        // generate a new EcdsaPod from the given msg, pk, signature
        let ecdsa_pod = timed!(
            "EcdsaPod::new",
            EcdsaPod::new(&params, vdset.root(), msg, pk, signature).unwrap()
        );
        Ok((ecdsa_pod, params, vdset))
    }

    #[test]
    fn test_ecdsa_pod() -> Result<()> {
        let sk = ECDSASecretKey::<Secp256K1>(Secp256K1Scalar([123, 456, 789, 123]));
        let msg = Secp256K1Scalar([321, 654, 987, 321]);

        let (ecdsa_pod, params, vdset) = compute_new_ecdsa_pod(sk, msg)?;

        ecdsa_pod.verify().unwrap();
        // pod2::measure_gates_print!();

        // wrap the ecdsa_pod in a 'MainPod' (RecursivePod)
        let main_ecdsa_pod = pod2::frontend::MainPod {
            pod: ecdsa_pod.clone(),
            public_statements: ecdsa_pod.pub_statements(),
            params: params.clone(),
        };

        // now generate a new MainPod from the ecdsa_pod
        let mut main_pod_builder = MainPodBuilder::new(&params, &vdset);
        main_pod_builder.add_main_pod(main_ecdsa_pod.clone());

        // add operation that ensures that the msg is as expected in the EcdsaPod
        let msg_limbs = secp_field_to_limbs(msg.0);
        let msg_hash = PoseidonHash::hash_no_pad(&msg_limbs);
        let msg_copy = main_pod_builder
            .pub_op(op!(
                new_entry,
                KEY_SIGNED_MSG,
                Value::from(RawValue(msg_hash.elements))
            ))
            .unwrap();
        main_pod_builder
            .pub_op(op!(eq, (&main_ecdsa_pod, KEY_SIGNED_MSG), msg_copy))
            .unwrap();

        // perpetuate the pk
        main_pod_builder
            .pub_op(op!(copy, main_ecdsa_pod.public_statements[2].clone()))
            .unwrap();

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

    #[test]
    fn test_serialization() -> Result<()> {
        let sk = ECDSASecretKey::<Secp256K1>(Secp256K1Scalar([123, 456, 789, 123]));
        let msg = Secp256K1Scalar([321, 654, 987, 321]);

        let (ecdsa_pod, params, vdset) = compute_new_ecdsa_pod(sk, msg)?;

        ecdsa_pod.verify().unwrap();

        let ecdsa_pod = (ecdsa_pod as Box<dyn Any>).downcast::<EcdsaPod>().unwrap();
        let data = ecdsa_pod.serialize_data();
        let recovered_ecdsa_pod =
            EcdsaPod::deserialize_data(params, data, vdset.root(), ecdsa_pod.id).unwrap();
        let recovered_ecdsa_pod = (recovered_ecdsa_pod as Box<dyn Any>)
            .downcast::<EcdsaPod>()
            .unwrap();

        assert_eq!(recovered_ecdsa_pod, ecdsa_pod);

        Ok(())
    }
}
