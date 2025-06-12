use std::{sync::LazyLock};

use base64::{Engine, prelude::BASE64_STANDARD};
use itertools::Itertools;
use pod2::{
    backends::plonky2::{
        basetypes::{
            C, D
        },
        Error, Result, mainpod::{self, calculate_id}
    },
    middleware::{
        self, DynError, Hash, Params, Pod, PodId, Proof, F
    }, 
    timed
};
use plonky2::{iop::witness::PartialWitness, plonk::{circuit_builder::CircuitBuilder, circuit_data::{CircuitConfig, CircuitData, VerifierOnlyCircuitData}}};
use crate::rsa::{RSATargets, build_rsa, set_rsa_targets};
use ssh_key::{public::{KeyData}, Algorithm, HashAlg, SshSig};
use pod2::middleware::EMPTY_HASH;
use sha2::{Sha512, Sha256, Digest};

const RSA_BYTE_SIZE: usize = 512;

fn make_verify_circuits(builder: &mut CircuitBuilder<F, D>) -> RSATargets {
    return build_rsa(builder);
}

// Standard message length for ED25519 pods (can be made configurable)
// const SIGNED_DATA_LEN: usize = 108; // SIGNED_DATA_LEN = 108 u8 = 864 bits

static RSA_VERIFY_DATA: LazyLock<(RSATargets, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_rsa_verify().expect("successful build"));

fn build_rsa_verify() -> Result<(RSATargets, CircuitData<F, C, D>)> {
    let config = CircuitConfig::standard_recursion_config(); // TODO is this the right config?
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let rsa_verify_target = make_verify_circuits(&mut builder);

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
    fn _prove(
        params: &Params,
        vds_root: Hash, // TODO what is this?
        raw_msg: &str,
        sig: &SshSig,
        namespace: &str,
    ) -> Result<RsaPod> {
        
        // Load signature
        let (rsa_verify_target, rsa_circuit_data) = &*RSA_VERIFY_DATA;
        let mut pw = PartialWitness::<F>::new();
        let encoded_padded_data = build_ssh_signed_data(namespace, raw_msg.as_bytes(), sig)?;
    
        let pk = match sig.public_key() {
            KeyData::Rsa(pk) => pk,
            _ => {
                return Err(Error::custom(String::from(
                    "signature does not carry an Ed25519 key",
                )));
            }
        };
        
        set_rsa_targets(&mut pw, rsa_verify_target, sig, &encoded_padded_data)?;

        let rsa_verify_proof = timed!(
            "prove the rsa signature verification (RsaVerifyTarget)",
            rsa_circuit_data.prove(pw)?
        );


        #[cfg(test)] // sanity check
        {
            rsa_circuit_data
                .verifier_data()
                .verify(rsa_verify_proof.clone())?;
        }
        let pk_bytes = pk.n.as_positive_bytes().expect("Public key was negative").to_vec();

        let statements = pub_self_statements(&encoded_padded_data, &pk_bytes)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, params));

        Ok(RsaPod {
            params: params.clone(),
            id,
            msg: encoded_padded_data,
            pk: pk_bytes,
            proof: rsa_verify_proof.proof,
            vds_hash: EMPTY_HASH,
        })
    }

    #[allow(clippy::new_ret_no_self)]// TODO what does this do?
    pub fn new(
        params: &Params,
        vds_root: Hash,
        raw_msg: &str,
        sig: &SshSig,
        namespace: &str,
    ) -> Result<Box<dyn Pod>, Box<DynError>> {
        Ok(Self::_prove(params, vds_root, raw_msg, sig, namespace).map(Box::new)?)
    }

    fn _verify(&self/* TODO: args */) -> Result<()> {
        // TODO: implement
        panic!("RsaPod::_verify not implemented");
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


/// Build SSH signed data format
pub fn build_ssh_signed_data(namespace: &str, raw_msg: &[u8], ssh_sig: &SshSig) -> Result<Vec<u8>> {
    // Use the SSH library's built-in method to create the data to sign
    let encoded_data = ssh_key::SshSig::signed_data(namespace, ssh_sig.hash_alg(), raw_msg)
        .expect("failed to build encoded SSH data");

    // Hash the data to sign and generate the digest info
    let (hashed_data, digest_info) : (Vec<u8>, Vec<u8>) = match ssh_sig.algorithm() {
        Algorithm::Rsa { hash: Some(HashAlg::Sha256) } => (
            Sha256::digest(&encoded_data).to_vec(),
            vec![
                0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20
            ]
        ),
        Algorithm::Rsa { hash: Some(HashAlg::Sha512) } => (
            Sha512::digest(&encoded_data).to_vec(),
            vec![
                0x30, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03, 0x05, 0x00, 0x04, 0x40
            ]
        ),
        _ => return Err(Error::custom(String::from("rsa-sha2-256 and rsa-sha2-256 only"))),
    };
    
    let mut combined_data = digest_info;
    combined_data.extend_from_slice(&hashed_data);

    let comb_len = combined_data.len();

    if RSA_BYTE_SIZE < comb_len + 11 {
        return Err(Error::custom(String::from("Internal encoding error. Encoded message overflows modulus.")))
    }

    // Generate padding string PS
    let ps_len = RSA_BYTE_SIZE - comb_len - 3;
    let ps = vec![0xff; ps_len]; // PS consists of 0xff octets
    
    // Step 5: Concatenate to form the encoded message EM
    // EM = 0x00 || 0x01 || PS || 0x00 || T
    let mut padded_data = Vec::with_capacity(RSA_BYTE_SIZE);
    padded_data.push(0x00);           // Leading 0x00
    padded_data.push(0x01);           // 0x01 byte
    padded_data.extend_from_slice(&ps); // Padding string PS (all 0xff)
    padded_data.push(0x00);           // Separator 0x00
    padded_data.extend_from_slice(&combined_data); // DigestInfo T

    println!("{:?}", padded_data);
    Ok(padded_data)
}

#[cfg(test)]
pub mod tests {
    use super::*;

    fn get_test_rsa_pod() -> Result<Box<dyn Pod>, Box<DynError>> {
        let params = Params {
            max_input_signed_pods: 0,
            ..Default::default()
        };

        // Use the sample data from plonky2_ed25519
        let msg = "0xPARC\n";
        let namespace = "double-blind.xyz";
        let sig = SshSig::from_pem(include_bytes!("../test_keys/id_rsa_example.sig")).unwrap();
        let vds_root = EMPTY_HASH;
    

        let rsa_pod = timed!(
            "RsaPod::new",
            RsaPod::new(&params, vds_root, msg, &sig, namespace).unwrap()
        );
        return Ok(rsa_pod);
    }

    #[ignore]
    #[test]
    fn rsa_pod_only() -> Result<()> {
        let rsa_pod = get_test_rsa_pod().unwrap();
        Ok(())
    }

    #[ignore]
    #[test]
    fn rsa_pod_only_verify() -> Result<()> {
        
        let rsa_pod = get_test_rsa_pod().unwrap();
        rsa_pod.verify().unwrap();

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
            0, 1, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0, 48, 81, 48, 13, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 3, 5, 0, 4, 64, 181, 197, 44, 214, 116, 75, 54, 39, 234, 42, 140, 208, 11, 206, 41, 35, 206, 205, 191, 120, 173, 54, 59, 138, 2, 32, 227, 203, 41, 241, 18, 139, 161, 89, 68, 192, 135, 58, 241, 130, 136, 20, 149, 230, 135, 249, 125, 234, 20, 202, 101, 48, 221, 110, 27, 245, 17, 102, 82, 107, 69, 88, 89, 51
        ]);
        
        Ok(())
    }
}