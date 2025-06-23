use std::collections::BTreeMap;

use anyhow::anyhow;
use ciborium::{Value, from_reader};
use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, goldilocks_field::GoldilocksField, types::Field},
    hash::hash_types::{HashOut, HashOutTarget, RichField},
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};
use pod2::middleware::{TypedValue, hash_str};
use serde::Deserialize;

use crate::gadgets::{hash_var_len::pod_str_hash, shift::shift_left};

type F = GoldilocksField;
const D: usize = 2;

trait ValueLookup: Sized {
    fn get_key<'a, 'b>(&'a self, key: &'b str) -> anyhow::Result<&'a Self>;
    fn get_index(&self, idx: usize) -> anyhow::Result<&Self>;
    fn get_bytes(&self) -> anyhow::Result<&[u8]>;
    fn get_array(&self) -> anyhow::Result<&[Self]>;
    fn get_tag(&self, tag: u64) -> anyhow::Result<&Value>;
}

impl ValueLookup for Value {
    fn get_key<'a, 'b>(&'a self, key: &'b str) -> anyhow::Result<&'a Value> {
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
        _ => None,
    }
}

fn issuer_signed_item(entry: &Value) -> Option<MdlField> {
    let bytes = entry.get_tag(24).ok()?.get_bytes().ok()?;
    let item: MdlItem = from_reader(bytes).ok()?;
    pod_value_for(&item.elementValue).map(|v| MdlField {
        key: item.elementIdentifier,
        value: v,
        cbor: bytes.to_vec(),
        digest_id: item.digestID,
        random: item.random,
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
    key: String,
    value: TypedValue,
    digest_id: u64,
    random: Vec<u8>,
    cbor: Vec<u8>,
}

pub struct MdlData {
    mso: Vec<u8>,
    signature: Vec<u8>,
    data: BTreeMap<String, MdlField>,
}

#[derive(Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct MdlItem {
    digestID: u64,
    random: Vec<u8>,
    elementIdentifier: String,
    elementValue: Value,
}

const NAMESPACE_STRINGS: &[&str] = &["org.iso.18013.5.1", "org.iso.18013.5.1.aamva"];

pub fn parse_data(data: &[u8]) -> anyhow::Result<MdlData> {
    let parsed: Value = from_reader(data)?;
    let issuer_signed = parsed
        .get_key("documents")?
        .get_index(0)?
        .get_key("issuerSigned")?;
    let issuer_auth = issuer_signed.get_key("issuerAuth")?;
    let mso = issuer_auth.get_index(2)?.get_bytes()?.to_vec();
    let signature = issuer_auth.get_index(3)?.get_bytes()?.to_vec();
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
    Ok(MdlData {
        mso,
        signature,
        data: entries,
    })
}

pub fn sha_256_pad(v: &mut Vec<u8>) -> anyhow::Result<()> {
    let sha_blocks = (v.len() + 9).div_ceil(64);
    if sha_blocks > 2 {
        anyhow::bail!("Expected message length <= 117");
    }
    let length: u64 = (v.len() * 8) as u64;
    v.push(0x80);
    v.resize(sha_blocks * 64 - 8, 0);
    v.extend(length.to_be_bytes());
    v.resize(128, 0);
    Ok(())
}

pub trait DataTarget {
    fn from_cbor(builder: &mut CircuitBuilder<F, D>, cbor: &[Target]) -> Self;

    fn set_target(&self, pw: &mut PartialWitness<F>, cbor: &[u8]) -> anyhow::Result<()>;
}

pub struct StringDataTarget {
    hash: HashOutTarget,
}

impl DataTarget for StringDataTarget {
    fn from_cbor(builder: &mut CircuitBuilder<F, D>, cbor: &[Target]) -> Self {
        let str_tag = builder.constant(-F::from_canonical_u8(0x60));
        let name_len = builder.add(cbor[0], str_tag);
        Self {
            hash: pod_str_hash(builder, &cbor[1..], name_len),
        }
    }

    fn set_target(
        &self,
        pw: &mut PartialWitness<GoldilocksField>,
        cbor: &[u8],
    ) -> anyhow::Result<()> {
        let item_tag = cbor[0];
        let item_len = (item_tag & 0x1F) as usize;
        if item_tag & 0xE0 != 0x60 || item_len > 23 {
            anyhow::bail!("Expected a string of length <= 23");
        }
        let item_str = core::str::from_utf8(&cbor[1..][..item_len])?;
        let name_hash = HashOut {
            elements: hash_str(item_str).0,
        };
        pw.set_hash_target(self.hash, name_hash)
    }
}

pub struct EntryTarget<T: DataTarget> {
    cbor: Box<[Target; 128]>,
    prefix_offset_bits: [BoolTarget; 7],
    data: T,
    field_name: String,
}

impl<T: DataTarget> EntryTarget<T> {
    pub fn new(builder: &mut CircuitBuilder<F, D>, field_name: &str) -> Self {
        let cbor = Box::new(core::array::from_fn(|_| {
            let t = builder.add_virtual_target();
            builder.range_check(t, 8);
            t
        }));
        let prefix_offset_bits = core::array::from_fn(|_| builder.add_virtual_bool_target_safe());
        let prefix = prefix_for_key(field_name);
        let shifted_cbor = shift_left(builder, cbor.as_ref(), &prefix_offset_bits);
        for (&ch_t, &ch) in shifted_cbor.iter().zip(prefix.iter()) {
            let ch_const = builder.constant(F::from_canonical_u8(ch));
            builder.connect(ch_t, ch_const);
        }
        let raw_data = &shifted_cbor[prefix.len()..];
        let data = T::from_cbor(builder, raw_data);
        Self {
            cbor,
            prefix_offset_bits,
            data,
            field_name: field_name.to_string(),
        }
    }

    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<GoldilocksField>,
        cbor: &[u8],
    ) -> anyhow::Result<()> {
        let mut cbor_padded = cbor.to_vec();
        sha_256_pad(&mut cbor_padded)?;
        for (&ch_t, ch) in self.cbor.iter().zip_eq(cbor_padded.into_iter()) {
            pw.set_target(ch_t, GoldilocksField::from_canonical_u8(ch))?;
        }
        let name_prefix = prefix_for_key(&self.field_name);
        let prefix_offset = memchr::memmem::find(cbor, &name_prefix)
            .ok_or_else(|| anyhow!("Could not find entry"))
            .unwrap();
        for (n, &b) in self.prefix_offset_bits.iter().enumerate() {
            pw.set_bool_target(b, (prefix_offset >> n) & 1 != 0)?;
        }
        let name_offset = prefix_offset + name_prefix.len();
        // TODO: The MDL spec allows strings of length up to 150.  But strings
        // of length > 23 use 2 bytes for the tag instead of 1.
        self.data.set_target(pw, &cbor[name_offset..])
    }
}

#[cfg(test)]
mod test {
    use anyhow::anyhow;
    use plonky2::{
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use super::parse_data;
    use crate::mdlpod::parse::{EntryTarget, StringDataTarget};

    const CBOR_DATA: &[u8] = include_bytes!("../../test_keys/mdl_response.cbor");

    #[test]
    fn test_parse() -> anyhow::Result<()> {
        parse_data(CBOR_DATA)?;
        Ok(())
    }

    #[test]
    fn test_string_hash() -> anyhow::Result<()> {
        let data = parse_data(CBOR_DATA)?;
        let family_name_entry = data
            .data
            .get("family_name")
            .ok_or_else(|| anyhow!("Could not find family name"))?;
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let entry_t = EntryTarget::<StringDataTarget>::new(&mut builder, "family_name");
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let mut pw = PartialWitness::new();
        entry_t.set_targets(&mut pw, &family_name_entry.cbor)?;
        let proof = data.prove(pw)?;
        data.verify(proof)
    }
}
