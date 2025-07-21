use anyhow::anyhow;
use log::{Level, LevelFilter};
use pod2::{
    backends::plonky2::{
        Result
    },
    middleware::{
        Params,
        RecursivePod,
        C,
        F
    },
    timed,
};
use introduction_pods::{
    mdlpod::{
        parse::{MdlData, parse_data, sha_256_pad, scalar_from_bytes},
        bytes_to_u64_array_be,
        STANDARD_MDL_POD_DATA,
        MdlPod,
        build,
        MdlDocTarget,
        MDL_VERIFY_DATA
    }
};

use p256::{
    PublicKey, 
    elliptic_curve::sec1::ToEncodedPoint
};

//-----------------------------------------------------------------------------


use sha2::{Sha256, Digest};
use plonky2_ecdsa::{
    curve::{
        curve_types::AffinePoint,
        ecdsa::{ECDSAPublicKey, verify_message},
        p256::{
            P256,
        }
    },
    field::p256_base::P256Base,
};
use pod2::{self, middleware::VDSet};
use x509_parser;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::iop::witness::PartialWitness;
use plonky2::field::types::Field;
use plonky2::iop::witness::WitnessWrite;
use introduction_pods::mdlpod::parse::DataType;
use introduction_pods::mdlpod::MDLFieldData;

const CBOR_DATA: &[u8] = include_bytes!("../test_keys/mdl/response.cbor");

const MSO_MAX_BLOCKS: usize = 48;

const MDL_FIELDS: MDLFieldData<'static> = &[
    ("document_number", DataType::String),
    ("expiry_date", DataType::Date),
    ("family_name", DataType::String),
    ("given_name", DataType::String),
    ("resident_address", DataType::String),
    ("birth_date", DataType::Date),
    ("age_birth_year", DataType::Int),
    ("sex", DataType::Int),
    ("hair_colour", DataType::String),
    ("eye_colour", DataType::String),
    ("height", DataType::Int),
    ("weight", DataType::Int),
];


pub fn cbor_parsed() -> anyhow::Result<MdlData> {
    parse_data(CBOR_DATA)
}
fn public_key_from_bytes(bytes: &[u8]) -> anyhow::Result<ECDSAPublicKey<P256>> {
    let (_, pem) = x509_parser::pem::parse_x509_pem(bytes)
        .map_err(|e| anyhow!("Failed to parse PEM: {:?}", e))?;
    let (_, cert) = x509_parser::parse_x509_certificate(&pem.contents)
        .map_err(|e| anyhow!("Failed to parse certificate: {:?}", e))?;
    let pk_sec1 = cert.public_key().subject_public_key.data.as_ref();

    // Parse SEC1 encoded public key
    let pk = PublicKey::from_sec1_bytes(pk_sec1)
        .map_err(|e| anyhow!("Failed to parse public key: {}", e))?;

    let enc = pk.to_encoded_point(false);

    let x_slice = enc.x().expect("x coordinate missing");
    let y_slice = enc.y().expect("y coordinate missing");
    let mut x_arr = [0u8; 32];
    x_arr.copy_from_slice(x_slice);
    let mut y_arr = [0u8; 32];
    y_arr.copy_from_slice(y_slice);

    let x = bytes_to_u64_array_be(&x_arr);
    let y = bytes_to_u64_array_be(&y_arr);

    Ok(ECDSAPublicKey(AffinePoint {
        x: P256Base(x),
        y: P256Base(y),
        zero: false,
    }))
}

fn extract_pk_from_cert(cert_path: &str) -> anyhow::Result<ECDSAPublicKey<P256>> {
    let pem_data = std::fs::read(cert_path)?;
    public_key_from_bytes(&pem_data)
}



fn get_test_mdl_pod() -> anyhow::Result<(Box<dyn RecursivePod>, Params, VDSet)> {
    // Load the MDL data
    let mdl_doc = include_bytes!("../test_keys/mdl/response.cbor");

    // Extract public key from certificate
    let pk = extract_pk_from_cert("test_keys/mdl/issuer-cert.pem")?;

    // Create the MdlPod
    let params = Params {
        max_input_signed_pods: 0,
        max_public_statements: 14,
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
        STANDARD_MDL_POD_DATA.1.verifier_only.clone(),
    ];
    let vd_set = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

    let mdl_pod = timed!("MdlPod::new", MdlPod::new(&params, &vd_set, pk, mdl_doc)?);

    mdl_pod.verify()?;

    Ok((mdl_pod, params, vd_set))
}



fn test_mdl_pod() -> anyhow::Result<()> {
    get_test_mdl_pod().map(|_| ())
}

fn test_verify_mdl_no_sig() -> anyhow::Result<()> {
    let mdl_data = cbor_parsed()?;
    let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
    let doc = MdlDocTarget::add_targets(&mut builder, MDL_FIELDS);
    
    let data = builder.build::<C>();
    let mut pw = PartialWitness::new();
    doc.set_targets(&mut pw, &mdl_data)?;
    let mut mso_padded = mdl_data.signed_message.clone();
    sha_256_pad(&mut mso_padded, MSO_MAX_BLOCKS)?;
    for (&ch_t, ch) in doc.mso.iter().zip(mso_padded) {
        pw.set_target(ch_t, F::from_canonical_u8(ch))?;
    }
    pw.set_target(
        doc.mso_len,
        F::from_canonical_usize(mdl_data.signed_message.len()),
    )?;
    let proof = data.prove(pw)?;
    data.verify(proof)
}

fn verify_mdl_signature(mdl_data: &MdlData, pk: &ECDSAPublicKey<P256>) -> bool {
        let digest = Sha256::digest(&mdl_data.signed_message);
        let ecdsa_msg = scalar_from_bytes(&digest);
        verify_message(ecdsa_msg, mdl_data.signature, *pk)
    }


fn test_verify_mdl_with_sig() -> anyhow::Result<()> {
    let mdl_data = cbor_parsed()?;
    let pk = public_key_from_bytes(include_bytes!("../test_keys/mdl/issuer-cert.pem"))?;
    if !verify_mdl_signature(&mdl_data, &pk) {
        anyhow::bail!("Invalid signature form message");
    }
    let (target, data) = &*MDL_VERIFY_DATA;
    let mut pw = PartialWitness::new();
    target.set_targets(&mut pw, &pk, &mdl_data)?;
    let proof = data.prove(pw)?;
    data.verify(proof)
}

fn main() -> Result<()> {
    let mut builder = env_logger::Builder::from_default_env();
    builder.format_timestamp(None);
    builder.filter_level(LevelFilter::Debug);   
    builder.try_init();
    //test_mdl_pod();
    //build();
    test_verify_mdl_with_sig();
    Ok(())
}
