use std::collections::BTreeMap;

use anyhow::anyhow;
use ciborium::{Value, from_reader};
use pod2::middleware::TypedValue;
use serde::Deserialize;

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
    let item: MdlItem = from_reader(entry.get_tag(24).ok()?.get_bytes().ok()?).ok()?;
    pod_value_for(&item.elementValue).map(|v| MdlField {
        key: item.elementIdentifier,
        value: v,
        random_data: item.random.clone(),
    })
}

#[derive(Debug, Clone)]
pub struct MdlField {
    key: String,
    value: TypedValue,
    random_data: Vec<u8>,
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

#[cfg(test)]
mod test {
    use super::parse_data;

    #[test]
    fn test_parse() -> anyhow::Result<()> {
        parse_data(include_bytes!("../../test_keys/mdl_response.cbor"))?;
        Ok(())
    }
}
