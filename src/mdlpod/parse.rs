use std::collections::BTreeMap;

use anyhow::anyhow;
use ciborium::{Value, from_reader, into_writer};
use itertools::Itertools;
use num::BigUint;
use plonky2::{
    field::types::Field,
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_ecdsa::{
    curve::{ecdsa::ECDSASignature, p256::P256},
    field::p256_scalar::P256Scalar,
};
use pod2::{
    backends::plonky2::{
        basetypes::{D, F},
        circuits::common::ValueTarget,
    },
    middleware::{TypedValue, hash_str},
};
use serde::Deserialize;

use crate::gadgets::{hash_var_len::pod_str_hash, shift::shift_left};

pub trait ValueLookup: Sized {
    fn get_key<'a>(&'a self, key: &'_ str) -> anyhow::Result<&'a Self>;
    fn get_index(&self, idx: usize) -> anyhow::Result<&Self>;
    fn get_bytes(&self) -> anyhow::Result<&[u8]>;
    fn get_array(&self) -> anyhow::Result<&[Self]>;
    fn get_tag(&self, tag: u64) -> anyhow::Result<&Value>;
}

impl ValueLookup for Value {
    fn get_key<'a>(&'a self, key: &'_ str) -> anyhow::Result<&'a Value> {
        self.as_map()
            .ok_or_else(|| anyhow!("Expected a map"))?
            .iter()
            .find_map(|(k, v)| match k {
                Value::Text(s) if key == s => Some(v),
                _ => None,
            })
            .ok_or(anyhow!("Missing key {key}"))
    }

    fn get_index(&self, idx: usize) -> anyhow::Result<&Value> {
        self.get_array()?
            .get(idx)
            .ok_or_else(|| anyhow!("Index {idx} out of range"))
    }

    fn get_bytes(&self) -> anyhow::Result<&[u8]> {
        self.as_bytes()
            .map(Vec::as_slice)
            .ok_or_else(|| anyhow!("Expected a byte string"))
    }

    fn get_array(&self) -> anyhow::Result<&[Value]> {
        Ok(self
            .as_array()
            .ok_or_else(|| anyhow!("Expected an array"))?
            .as_slice())
    }

    fn get_tag(&self, tag: u64) -> anyhow::Result<&Value> {
        self.as_tag()
            .and_then(|(t, v)| if t == tag { Some(v) } else { None })
            .ok_or_else(|| anyhow!("Expected tag {tag}"))
    }
}

fn pod_value_for(v: &Value) -> Option<TypedValue> {
    match v {
        Value::Integer(n) => Some(TypedValue::Int(i64::try_from(*n).ok()?)),
        Value::Text(s) => Some(TypedValue::String(s.clone())),
        Value::Bool(b) => Some(TypedValue::Bool(*b)),
        Value::Tag(1004, v) => match v.as_ref() {
            Value::Text(s) => Some(TypedValue::String(s.clone())),
            _ => None,
        },
        _ => None,
    }
}

fn issuer_signed_item(entry: &Value) -> Option<MdlField> {
    let bytes = entry.get_tag(24).ok()?.get_bytes().ok()?;
    let mut cbor = Vec::new();
    ciborium::into_writer(entry, &mut cbor).ok()?;
    let item: MdlItem = from_reader(bytes).ok()?;
    pod_value_for(&item.elementValue).map(|v| MdlField {
        key: item.elementIdentifier,
        value: v,
        cbor,
    })
}

pub fn prefix_for_key(key: &str) -> Vec<u8> {
    assert!(key.len() < 24);
    let mut buf = Vec::new();
    buf.extend_from_slice(b"qelementIdentifier");
    buf.push((key.len() as u8) | 0x60);
    buf.extend(key.bytes());
    buf.extend(b"lelementValue");
    buf
}

#[derive(Debug, Clone)]
pub struct MdlField {
    pub key: String,
    pub value: TypedValue,
    pub cbor: Vec<u8>,
}

pub struct MdlData {
    pub signed_message: Vec<u8>,
    pub signature: ECDSASignature<P256>,
    pub data: BTreeMap<String, MdlField>,
}

#[derive(Deserialize, Debug, Clone)]
#[allow(non_snake_case, dead_code)]
struct MdlItem {
    digestID: u64,
    random: Vec<u8>,
    elementIdentifier: String,
    elementValue: Value,
}

const NAMESPACE_STRINGS: &[&str] = &["org.iso.18013.5.1", "org.iso.18013.5.1.aamva"];

pub fn scalar_from_bytes(bytes: &[u8]) -> P256Scalar {
    let scalar_biguint = BigUint::from_bytes_be(bytes);
    P256Scalar::from_noncanonical_biguint(scalar_biguint)
}

pub fn sig_structure(issuer_auth: &[Value]) -> anyhow::Result<Vec<u8>> {
    if issuer_auth.len() != 4 {
        anyhow::bail!("incorrect issuerAuth length");
    }
    let context = Value::Text("Signature1".to_string());
    let body_protected = issuer_auth[0].clone();
    let external_aad = Value::Bytes(Vec::new());
    let payload = issuer_auth[2].clone();
    let sig_structure_obj = Value::Array(vec![context, body_protected, external_aad, payload]);
    let mut sig_structure = Vec::new();
    into_writer(&sig_structure_obj, &mut sig_structure)?;
    Ok(sig_structure)
}

pub fn parse_data(data: &[u8]) -> anyhow::Result<MdlData> {
    let parsed: Value = from_reader(data)?;
    let issuer_signed = parsed
        .get_key("documents")?
        .get_index(0)?
        .get_key("issuerSigned")?;
    let issuer_auth = issuer_signed.get_key("issuerAuth")?;
    let signature_bytes = issuer_auth.get_index(3)?.get_bytes()?.to_vec();
    let namespaces = issuer_signed.get_key("nameSpaces")?;
    let mut entries: BTreeMap<String, MdlField> = BTreeMap::new();
    for ns_name in NAMESPACE_STRINGS {
        if let Ok(ns) = namespaces.get_key(ns_name) {
            for tagged_data in ns.get_array()?.iter() {
                if let Some(item) = issuer_signed_item(tagged_data) {
                    entries.insert(item.key.clone(), item);
                }
            }
        }
    }
    if signature_bytes.len() != 64 {
        anyhow::bail!("Malformed signature");
    }
    let r = scalar_from_bytes(&signature_bytes[..32]);
    let s = scalar_from_bytes(&signature_bytes[32..]);
    let signature = ECDSASignature { r, s };
    let signed_message = sig_structure(issuer_auth.get_array()?)?;
    Ok(MdlData {
        signed_message,
        signature,
        data: entries,
    })
}

pub fn sha_256_pad(v: &mut Vec<u8>, max_blocks: usize) -> anyhow::Result<()> {
    let sha_blocks = (v.len() + 9).div_ceil(64);
    if sha_blocks > max_blocks {
        anyhow::bail!("Message too long");
    }
    let length: u64 = (v.len() * 8) as u64;
    v.push(0x80);
    v.resize(sha_blocks * 64 - 8, 0);
    let desired_len = max_blocks * 64;
    let length_bytes = length.to_be_bytes();
    // For consistency with plonky2_sha256::circuit::fill_variable_length_circuits,
    // we fill the space past the end by repeating the length of the message.
    while v.len() < desired_len {
        v.extend(length_bytes);
    }
    Ok(())
}

fn string_from_cbor(builder: &mut CircuitBuilder<F, D>, cbor: &[Target]) -> (ValueTarget, Target) {
    let str_tag = builder.constant(-F::from_canonical_u8(0x60));
    let mut name_len = builder.add(cbor[0], str_tag);
    let twenty_four = builder.constant(F::from_canonical_u32(24));
    builder.range_check(name_len, 5);
    let len_is_24 = builder.is_equal(name_len, twenty_four);
    name_len = builder.select(len_is_24, cbor[1], name_len);
    let shifted = shift_left(builder, &cbor[1..], &[len_is_24]);
    let value = ValueTarget {
        elements: pod_str_hash(builder, &shifted, name_len).elements,
    };
    let one = builder.one();
    let tag_len = builder.add(one, len_is_24.target);
    let total_len = builder.add(tag_len, name_len);
    (value, total_len)
}

fn int_from_cbor(builder: &mut CircuitBuilder<F, D>, cbor: &[Target]) -> (ValueTarget, Target) {
    // TODO: cbor[0] should be <= 27
    // TODO: handle values > 2^16
    builder.range_check(cbor[0], 5);
    let c_24 = builder.constant(F::from_canonical_u32(24));
    let c_25 = builder.constant(F::from_canonical_u32(25));
    let c_256 = builder.constant(F::from_canonical_u32(0x100));
    let is_24 = builder.is_equal(cbor[0], c_24);
    let is_25 = builder.is_equal(cbor[0], c_25);
    let value_2_bytes = builder.mul_add(c_256, cbor[1], cbor[2]);
    let mut value = builder.select(is_24, cbor[1], cbor[0]);
    value = builder.select(is_25, value_2_bytes, value);
    let zero = builder.zero();
    let value = ValueTarget {
        elements: [value, zero, zero, zero],
    };
    let two = builder.constant(F::TWO);
    let mut len = builder.constant(F::ONE);
    len = builder.add(is_24.target, len);
    len = builder.mul_add(two, is_25.target, len);
    (value, len)
}

fn date_from_cbor(builder: &mut CircuitBuilder<F, D>, cbor: &[Target]) -> (ValueTarget, Target) {
    let header = [0xd9, 0x03, 0xec].map(F::from_canonical_u8);
    let header_t = builder.constants(&header);
    for (&c, h) in cbor.iter().zip(header_t.into_iter()) {
        builder.connect(c, h);
    }
    let (value, string_len) = string_from_cbor(builder, &cbor[3..]);
    let date_tag_len = builder.constant(F::from_canonical_u32(3));
    let total_len = builder.add(date_tag_len, string_len);
    (value, total_len)
}

fn set_field_string(
    pw: &mut PartialWitness<F>,
    field: &ValueTarget,
    cbor: &[u8],
) -> anyhow::Result<()> {
    let item_tag = cbor[0];
    let item_len = (item_tag & 0x1F) as usize;
    if item_tag & 0xE0 != 0x60 || item_len > 23 {
        anyhow::bail!("Expected a string of length <= 23");
    }
    let item_str = core::str::from_utf8(&cbor[1..][..item_len])?;
    let name_hash = hash_str(item_str);
    pw.set_target_arr(&field.elements, &name_hash.0)
}

fn set_field_int(
    pw: &mut PartialWitness<F>,
    field: &ValueTarget,
    cbor: &[u8],
) -> anyhow::Result<()> {
    let value = match cbor[0] {
        0..=23 => cbor[0] as u32,
        24 => cbor[1] as u32,
        25 => ((cbor[1] as u32) << 8) | (cbor[2] as u32),
        _ => anyhow::bail!("Expected: integer between 0 and 65535"),
    };
    pw.set_target(field.elements[0], F::from_canonical_u32(value))
}

fn set_field_date(
    pw: &mut PartialWitness<F>,
    field: &ValueTarget,
    cbor: &[u8],
) -> anyhow::Result<()> {
    set_field_string(pw, field, &cbor[3..])
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DataType {
    String,
    Int,
    Date,
}

impl DataType {
    pub fn field_from_cbor(
        self,
        builder: &mut CircuitBuilder<F, D>,
        cbor: &[Target],
    ) -> (ValueTarget, Target) {
        match self {
            DataType::String => string_from_cbor(builder, cbor),
            DataType::Int => int_from_cbor(builder, cbor),
            DataType::Date => date_from_cbor(builder, cbor),
        }
    }

    pub fn set_field(
        self,
        pw: &mut PartialWitness<F>,
        field: &ValueTarget,
        cbor: &[u8],
    ) -> anyhow::Result<()> {
        match self {
            DataType::String => set_field_string(pw, field, cbor),
            DataType::Int => set_field_int(pw, field, cbor),
            DataType::Date => set_field_date(pw, field, cbor),
        }
    }
}

pub struct EntryTarget {
    pub cbor: Box<[Target; 128]>,
    pub prefix_offset_bits: [BoolTarget; 7],
    pub data_end_offset: Target,
    pub value: ValueTarget,
    pub data_type: DataType,
    pub field_name: String,
}

impl EntryTarget {
    pub fn new(builder: &mut CircuitBuilder<F, D>, field_name: &str, data_type: DataType) -> Self {
        // don't need to range check cbor here, because it gets range checked
        // when it's converted to bytes for the SHA256 hash
        let cbor = Box::new(core::array::from_fn(|_| builder.add_virtual_target()));
        let prefix_offset_bits = core::array::from_fn(|_| builder.add_virtual_bool_target_safe());
        let prefix = prefix_for_key(field_name);
        let shifted_cbor = shift_left(builder, cbor.as_ref(), &prefix_offset_bits);
        for (&ch_t, &ch) in shifted_cbor.iter().zip(prefix.iter()) {
            let ch_const = builder.constant(F::from_canonical_u8(ch));
            builder.connect(ch_t, ch_const);
        }
        let raw_data = &shifted_cbor[prefix.len()..];
        let (value, data_len) = data_type.field_from_cbor(builder, raw_data);
        let prefix_offset = builder.le_sum(prefix_offset_bits.iter());
        let prefix_len = builder.constant(F::from_canonical_usize(prefix.len()));
        let data_offset = builder.add(prefix_offset, prefix_len);
        let data_end_offset = builder.add(data_offset, data_len);
        Self {
            cbor,
            prefix_offset_bits,
            data_end_offset,
            value,
            data_type,
            field_name: field_name.to_string(),
        }
    }

    pub fn set_targets(&self, pw: &mut PartialWitness<F>, cbor: &[u8]) -> anyhow::Result<()> {
        let mut cbor_padded = cbor.to_vec();
        sha_256_pad(&mut cbor_padded, 2)?;
        for (&ch_t, ch) in self.cbor.iter().zip_eq(cbor_padded.into_iter()) {
            pw.set_target(ch_t, F::from_canonical_u8(ch))?;
        }
        let name_prefix = prefix_for_key(&self.field_name);
        let prefix_offset = memchr::memmem::find(cbor, &name_prefix)
            .ok_or_else(|| anyhow!("Could not find entry"))
            .unwrap();
        for (n, &b) in self.prefix_offset_bits.iter().enumerate() {
            pw.set_bool_target(b, (prefix_offset >> n) & 1 != 0)?;
        }
        let name_offset = prefix_offset + name_prefix.len();
        self.data_type
            .set_field(pw, &self.value, &cbor[name_offset..])
    }
}

#[cfg(test)]
pub(crate) mod test {
    use anyhow::anyhow;
    use plonky2::{
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use super::parse_data;
    use crate::mdlpod::parse::{DataType, EntryTarget, MdlData};

    const CBOR_DATA: &[u8] = include_bytes!("../../test_keys/mdl/response.cbor");

    pub fn cbor_parsed() -> anyhow::Result<MdlData> {
        parse_data(CBOR_DATA)
    }

    #[test]
    #[ignore]
    fn test_parse() -> anyhow::Result<()> {
        parse_data(CBOR_DATA)?;
        Ok(())
    }

    #[test]
    #[ignore]
    fn test_string_hash() -> anyhow::Result<()> {
        let data = parse_data(CBOR_DATA)?;
        let family_name_entry = data
            .data
            .get("family_name")
            .ok_or_else(|| anyhow!("Could not find family name"))?;
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let entry_t = EntryTarget::new(&mut builder, "family_name", DataType::String);
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let mut pw = PartialWitness::new();
        entry_t.set_targets(&mut pw, &family_name_entry.cbor)?;
        let proof = data.prove(pw)?;
        data.verify(proof)
    }

    #[test]
    #[ignore]
    fn test_date() -> anyhow::Result<()> {
        let data = parse_data(CBOR_DATA)?;
        println!("{:?}", data.data.keys());
        let birth_date_entry = data
            .data
            .get("birth_date")
            .ok_or_else(|| anyhow!("Could not find birth date"))?;
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let entry_t = EntryTarget::new(&mut builder, "birth_date", DataType::Date);
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let mut pw = PartialWitness::new();
        entry_t.set_targets(&mut pw, &birth_date_entry.cbor)?;
        let proof = data.prove(pw)?;
        data.verify(proof)
    }

    #[test]
    #[ignore]
    fn test_int() -> anyhow::Result<()> {
        let data = parse_data(CBOR_DATA)?;
        let height_entry = data
            .data
            .get("height")
            .ok_or_else(|| anyhow!("Could not find height"))?;
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let entry_t = EntryTarget::new(&mut builder, "height", DataType::Int);
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let mut pw = PartialWitness::new();
        entry_t.set_targets(&mut pw, &height_entry.cbor)?;
        let proof = data.prove(pw)?;
        data.verify(proof)
    }
}
