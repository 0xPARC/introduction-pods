use std::sync::LazyLock;

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
use pod2::{
    backends::plonky2::{
        Error, Result, serialize_proof, deserialize_proof,
        basetypes::{C, D},
        circuits::{
            common::{
                CircuitBuilderPod, Flattenable, StatementArgTarget, StatementTarget, ValueTarget,
            },
            mainpod::CalculateIdGadget,
        },
        mainpod::{self, calculate_id, get_common_data},
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        self, AnchoredKey, DynError, F, Hash, KEY_TYPE, Key, NativePredicate, Params,
        Pod, PodId, Proof, RawValue, SELF, Statement, ToFields, Value, RecursivePod,
    },
    timed,
};
use sha2::{Digest, Sha256, Sha512};
use ssh_key::{Algorithm, HashAlg, SshSig, public::KeyData};
use serde::{Serialize, Deserialize};

use crate::{
    PodType,
    rsa::{BITS, BigUintTarget, RSA_LIMBS, RSATargets, build_rsa, set_rsa_targets},
};

const RSA_BYTE_SIZE: usize = 512;

const KEY_SIGNED_MSG: &str = "signed_msg";
const KEY_RSA_PK: &str = "rsa_pk";

#[derive(Serialize, Deserialize)]
struct Data {
    msg: Vec<u8>,
    pk: Vec<u8>,
    proof: String,
}


static RSA_VERIFY_DATA: LazyLock<(RSATargets, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_rsa_verify().expect("successful build"));

fn build_rsa_verify() -> Result<(RSATargets, CircuitData<F, C, D>)> {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let rsa_pod_verify_target = build_rsa(&mut builder);

    // Register public inputs
    builder.register_public_inputs(&rsa_pod_verify_target.signature.limbs);
    builder.register_public_inputs(&rsa_pod_verify_target.modulus.limbs);
    builder.register_public_inputs(&rsa_pod_verify_target.padded_data.limbs);

    let data = timed!("RSAVerify build", builder.build::<C>());
    Ok((rsa_pod_verify_target, data))
}

#[derive(Clone, Debug)]
struct RsaPodVerifyTarget {
    vds_root: HashOutTarget,
    id: HashOutTarget,
    proof: ProofWithPublicInputsTarget<D>,
}

struct RsaPodVerifyInput {
    vds_root: Hash,
    id: PodId,
    proof: ProofWithPublicInputs<F, C, D>,
}

impl RsaPodVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>, params: &Params) -> Self {
        let measure = measure_gates_begin!(builder, "RsaPodVerifyTarget");

        // Verify proof of RSA verification
        let (_, circuit_data) = &*RSA_VERIFY_DATA;
        let verifier_data_targ = builder.constant_verifier_data(&circuit_data.verifier_only);
        let proof_targ = builder.add_virtual_proof_with_pis(&circuit_data.common);
        builder.verify_proof::<C>(&proof_targ, &verifier_data_targ, &circuit_data.common);

        // Extract message & public key
        let msg = BigUintTarget {
            limbs: proof_targ.public_inputs[2 * RSA_LIMBS..].to_vec(),
        };
        let modulus = BigUintTarget {
            limbs: proof_targ.public_inputs[RSA_LIMBS..2 * RSA_LIMBS].to_vec(),
        };

        // Form statements
        let msg_bits = biguint_to_bits_targets(builder, &msg, 8 * RSA_BYTE_SIZE);
        let msg_bytes = le_bits_to_bytes_targets(builder, &msg_bits);
        let modulus_bits = biguint_to_bits_targets(builder, &modulus, 8 * RSA_BYTE_SIZE);
        let modulus_bytes = le_bits_to_bytes_targets(builder, &modulus_bits);

        let statements = pub_self_statements_target(builder, params, &msg_bytes, &modulus_bytes);
        let id = CalculateIdGadget {
            params: params.clone(),
        }
        .eval(builder, &statements);

        // Register public inputs
        let vds_root = builder.add_virtual_hash();
        builder.register_public_inputs(&id.elements);
        builder.register_public_inputs(&vds_root.elements);

        measure_gates_end!(builder, measure);
        Self {
            vds_root,
            id,
            proof: proof_targ,
        }
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &RsaPodVerifyInput) -> Result<()> {
        pw.set_proof_with_pis_target(&self.proof, &input.proof)?;
        pw.set_hash_target(self.id, HashOut::from_vec(input.id.0.0.to_vec()))?;
        pw.set_target_arr(&self.vds_root.elements, &input.vds_root.0)?;

        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RsaPod {
    params: Params,
    id: PodId,
    msg: Vec<u8>,
    pk: Vec<u8>,
    proof: Proof,
    vds_root: Hash,
}

impl RecursivePod for RsaPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        let (_, circuit_data) = &*STANDARD_RSA_POD_DATA;
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

static STANDARD_RSA_POD_DATA: LazyLock<(RsaPodVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build().expect("successful build"));

fn build() -> Result<(RsaPodVerifyTarget, CircuitData<F, C, D>)> {
    let params = &*pod2::backends::plonky2::DEFAULT_PARAMS;
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let rsa_pod_verify_target = RsaPodVerifyTarget::add_targets(&mut builder, params);
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    pod2::backends::plonky2::recursion::pad_circuit(&mut builder, &rec_circuit_data.common);

    let data = timed!("RSAPod build", builder.build::<C>());
    assert_eq!(rec_circuit_data.common, data.common);
    Ok((rsa_pod_verify_target, data))
}

impl RsaPod {
    fn _prove(
        params: &Params,
        vds_root: Hash,
        raw_msg: &str,
        sig: &SshSig,
        namespace: &str,
    ) -> Result<RsaPod> {
        // Load signature into verification circuit
        let (rsa_verify_target, rsa_circuit_data) = &*RSA_VERIFY_DATA;
        let mut pw = PartialWitness::<F>::new();
        let encoded_padded_data = build_ssh_signed_data(namespace, raw_msg.as_bytes(), sig)?;

        let pk = match sig.public_key() {
            KeyData::Rsa(pk) => pk,
            _ => {
                return Err(Error::custom(String::from(
                    "signature does not carry an Rsa key",
                )));
            }
        };

        let pk_bytes =
            pk.n.as_positive_bytes()
                .expect("Public key was negative")
                .to_vec();
        if pk_bytes.len() != RSA_BYTE_SIZE {
            return Err(Error::custom(String::from(
                "Public key was not the correct size",
            )));
        }

        set_rsa_targets(&mut pw, rsa_verify_target, sig, &encoded_padded_data)?;

        let rsa_verify_proof = timed!(
            "prove the RSA signature verification (RSAVerifyTarget)",
            rsa_circuit_data.prove(pw)?
        );

        // Verify in wrapped circuit
        let (rsa_pod_target, circuit_data) = &*STANDARD_RSA_POD_DATA;

        let statements = pub_self_statements(&encoded_padded_data, &pk_bytes)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, params));

        // Set targets
        let input = RsaPodVerifyInput {
            vds_root,
            id,
            proof: rsa_verify_proof,
        };

        let mut pw = PartialWitness::<F>::new();
        rsa_pod_target.set_targets(&mut pw, &input)?;
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

        Ok(RsaPod {
            params: params.clone(),
            id,
            msg: encoded_padded_data,
            pk: pk_bytes,
            proof: proof_with_pis.proof,
            vds_root,
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

        let (_, circuit_data) = &*STANDARD_RSA_POD_DATA;

        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(self.vds_root().0.iter()) // slot for the unused vds root
            .cloned()
            .collect_vec();

        circuit_data
            .verify(ProofWithPublicInputs {
                proof: self.proof.clone(),
                public_inputs,
            })
            .map_err(|e| Error::custom(format!("RSAPod proof verification failure: {:?}", e)))
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

    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::Rsa as usize, "RSA")
    }

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::to_value(Data {
            proof: serialize_proof(&self.proof),
            msg: self.msg.clone(),
            pk: self.pk.clone(),
        })
        .expect("serialization to json")
    }
}

fn type_statement() -> Statement {
    Statement::equal(
        AnchoredKey::from((SELF, KEY_TYPE)),
        Value::from(PodType::Rsa),
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
    let ak_key = builder.constant_value(Key::from(KEY_RSA_PK).raw());
    let ak_pk = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&pk_hash.elements));
    let st_pk =
        StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak_pk, value]);

    vec![st_type, st_msg, st_pk]
}

fn pub_self_statements(msg: &Vec<u8>, pk: &Vec<u8>) -> Vec<middleware::Statement> {
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
        AnchoredKey::from((SELF, KEY_RSA_PK)),
        Value::from(RawValue(pk_hash.elements)),
    );

    vec![st_type, st_msg, st_pk]
}

// Helper function to convert bit targets to byte targets
fn le_bits_to_bytes_targets(
    builder: &mut CircuitBuilder<F, D>,
    bits: &Vec<BoolTarget>,
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

fn biguint_to_bits_targets(
    builder: &mut CircuitBuilder<F, D>,
    biguint: &BigUintTarget,
    total_bits: usize,
) -> Vec<BoolTarget> {
    // Returns bits in little-endian order, i.e. least significant BIT first (this is NOT the same as little endian BYTE ordering)
    let false_target = builder._false();
    let mut bits = Vec::new();
    for limb in &biguint.limbs {
        bits.extend_from_slice(&builder.split_le(*limb, BITS));
    }

    if bits.len() < total_bits {
        bits.extend(vec![false_target; total_bits - bits.len()]);
    } else if bits.len() > total_bits {
        for i in total_bits..bits.len() {
            let not_bit_i = builder.not(bits[i]);
            builder.assert_bool(not_bit_i);
        }
        return bits[..total_bits].to_vec();
    }
    bits
}

/// Build SSH signed data format
pub fn build_ssh_signed_data(namespace: &str, raw_msg: &[u8], ssh_sig: &SshSig) -> Result<Vec<u8>> {
    // Use the SSH library's built-in method to create the data to sign
    let encoded_data = ssh_key::SshSig::signed_data(namespace, ssh_sig.hash_alg(), raw_msg)
        .expect("failed to build encoded SSH data");

    // Hash the data to sign and generate the digest info
    let (hashed_data, digest_info): (Vec<u8>, Vec<u8>) = match ssh_sig.algorithm() {
        Algorithm::Rsa {
            hash: Some(HashAlg::Sha256),
        } => (Sha256::digest(&encoded_data).to_vec(), vec![
            0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
            0x01, 0x05, 0x00, 0x04, 0x20,
        ]),
        Algorithm::Rsa {
            hash: Some(HashAlg::Sha512),
        } => (Sha512::digest(&encoded_data).to_vec(), vec![
            0x30, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
            0x03, 0x05, 0x00, 0x04, 0x40,
        ]),
        _ => {
            return Err(Error::custom(String::from(
                "rsa-sha2-256 and rsa-sha2-256 only",
            )));
        }
    };

    let mut combined_data = digest_info;
    combined_data.extend_from_slice(&hashed_data);

    let comb_len = combined_data.len();

    if RSA_BYTE_SIZE < comb_len + 11 {
        return Err(Error::custom(String::from(
            "Internal encoding error. Encoded message overflows modulus.",
        )));
    }

    // Generate padding string PS
    let ps_len = RSA_BYTE_SIZE - comb_len - 3;
    let ps = vec![0xff; ps_len]; // PS consists of 0xff octets

    // Concatenate to form the encoded message EM
    // EM = 0x00 || 0x01 || PS || 0x00 || T
    let mut padded_data = Vec::with_capacity(RSA_BYTE_SIZE);
    padded_data.push(0x00); // Leading 0x00
    padded_data.push(0x01); // 0x01 byte
    padded_data.extend_from_slice(&ps); // Padding string PS (all 0xff)
    padded_data.push(0x00); // Separator 0x00
    padded_data.extend_from_slice(&combined_data); // DigestInfo T

    Ok(padded_data)
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use pod2::{self, frontend::MainPodBuilder, middleware::VDSet};

    use super::*;

    fn get_test_rsa_pod() -> Result<(Box<dyn Pod>, VDSet)> {
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
            STANDARD_RSA_POD_DATA.1.verifier_only.clone(),
        ];
        let vdset = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

        // Use the sample data from plonky2_rsa
        let msg = "0xPARC\n";
        let namespace = "double-blind.xyz";
        let sig = SshSig::from_pem(include_bytes!("../test_keys/id_rsa_example.sig")).unwrap();
        let vds_root = vdset.root();

        let rsa_pod = timed!(
            "RsaPod::new",
            RsaPod::new(&params, vds_root, msg, &sig, namespace).unwrap()
        );
        Ok((rsa_pod, vdset))
    }

    #[test]
    #[ignore] // This test is a subset of rsa_pod_with_mainpod_verify
    fn rsa_pod_only_verify() -> Result<()> {
        let (rsa_pod, _) = get_test_rsa_pod().unwrap();
        rsa_pod.verify().unwrap();

        Ok(())
    }

    #[test]
    fn rsa_pod_with_mainpod_verify() -> Result<()> {
        let (rsa_pod, vd_set) = get_test_rsa_pod().unwrap();
        rsa_pod.verify().unwrap();

        let params = rsa_pod.params().clone();

        // wrap the rsa_pod in a 'MainPod' (RecursivePod)
        let main_rsa_pod = pod2::frontend::MainPod {
            pod: (rsa_pod.clone() as Box<dyn Any>)
                .downcast::<RsaPod>()
                .unwrap(),
            public_statements: rsa_pod.pub_statements(),
            params: params.clone(),
        };

        // now generate a new MainPod from the rsa_pod
        let mut main_pod_builder = MainPodBuilder::new(&params, &vd_set);
        main_pod_builder.add_main_pod(main_rsa_pod);

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
    fn ssh_rsa_encode() -> Result<()> {
        // Only tests a signature generated with Sha512 as the inner hash algorithm and rsa-sha2-512 as the signature method.
        let msg = "0xPARC\n";
        let namespace = "double-blind.xyz";
        let sig = SshSig::from_pem(include_bytes!("../test_keys/id_rsa_example.sig")).unwrap();
        let data = build_ssh_signed_data(namespace, msg.as_bytes(), &sig).unwrap();

        assert_eq!(data, vec![
            0, 1, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 0, 48, 81, 48, 13, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 3, 5, 0, 4, 64, 181,
            197, 44, 214, 116, 75, 54, 39, 234, 42, 140, 208, 11, 206, 41, 35, 206, 205, 191, 120,
            173, 54, 59, 138, 2, 32, 227, 203, 41, 241, 18, 139, 161, 89, 68, 192, 135, 58, 241,
            130, 136, 20, 149, 230, 135, 249, 125, 234, 20, 202, 101, 48, 221, 110, 27, 245, 17,
            102, 82, 107, 69, 88, 89, 51
        ]);

        Ok(())
    }

    #[test]
    fn serialization() -> Result<()> {
        let (rsa_pod, vd_set) = get_test_rsa_pod().unwrap();

        rsa_pod.verify().unwrap();

        let rsa_pod = (rsa_pod as Box<dyn Any>)
            .downcast::<RsaPod>()
            .unwrap();
        let data = rsa_pod.serialize_data();
        let recovered_rsa_pod =
            RsaPod::deserialize_data(rsa_pod.params().clone(), data, vd_set.root(), rsa_pod.id()).unwrap();
        let recovered_rsa_pod = (recovered_rsa_pod as Box<dyn Any>)
            .downcast::<RsaPod>()
            .unwrap();

        assert_eq!(recovered_rsa_pod, rsa_pod);

        Ok(())
    }
}
