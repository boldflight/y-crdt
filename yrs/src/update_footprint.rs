//! Read-only evidence for every original update struct and declared deletion.
//! Engine identities do not establish application authorship or authorization.

use crate::block::{Block, Item, ItemContent};
use crate::branch::BranchID;
use crate::encoding::read::{Error as DecodeError, Read};
use crate::types::{TypePtr, TypeRef};
use crate::updates::decoder::{Decode, DecoderV1};
use crate::{Any, ReadTxn, Update, ID};
use std::collections::HashMap;
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum FootprintError {
    #[error("mutation footprint traversal budget exhausted")]
    Limit,
    #[error("mutation footprint requires a settled retained UTF-16 owner")]
    Prestate,
    #[error("invalid original mutation update")]
    Update,
    #[error("original mutation item is unavailable or unsupported")]
    Unretained,
}
fn step(budget: &mut usize) -> Result<(), FootprintError> {
    *budget = budget.checked_sub(1).ok_or(FootprintError::Limit)?;
    Ok(())
}
fn object<const N: usize>(entries: [(&str, Any); N]) -> Any {
    Any::from(
        IntoIterator::into_iter(entries)
            .map(|(key, value)| (key.to_string(), value))
            .collect::<HashMap<_, _>>(),
    )
}
fn identity(id: ID) -> Any {
    object([
        ("client", Any::from(id.client.get() as i64)),
        ("clock", Any::from(id.clock)),
    ])
}
fn optional_identity(id: Option<ID>) -> Any {
    id.map(identity).unwrap_or(Any::Null)
}
fn parent(item: &Item) -> Result<Any, FootprintError> {
    let id = match &item.parent {
        TypePtr::Branch(branch) => branch.id(),
        TypePtr::Named(name) => BranchID::Root(name.clone()),
        TypePtr::ID(id) => BranchID::Nested(*id),
        TypePtr::Unknown => return Err(FootprintError::Unretained),
    };
    Ok(match id {
        BranchID::Root(name) => object([("root", Any::from(name))]),
        BranchID::Nested(id) => object([("type", identity(id))]),
    })
}
fn value(value: &Any, budget: &mut usize, depth: usize) -> Result<Any, FootprintError> {
    step(budget)?;
    if depth > 128 {
        return Err(FootprintError::Limit);
    }
    match value {
        Any::Undefined | Any::Buffer(_) => Err(FootprintError::Unretained),
        Any::Array(values) => Ok(Any::from(
            values
                .iter()
                .map(|v| self::value(v, budget, depth + 1))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Any::Map(values) => Ok(Any::from(
            values
                .iter()
                .map(|(k, v)| Ok((k.clone(), self::value(v, budget, depth + 1)?)))
                .collect::<Result<HashMap<_, _>, FootprintError>>()?,
        )),
        value => Ok(value.clone()),
    }
}
fn content(item: &Item, budget: &mut usize) -> Result<Any, FootprintError> {
    step(budget)?;
    Ok(match &item.content {
        ItemContent::String(text) => object([
            ("kind", Any::from("string")),
            ("text", Any::from(text.as_str())),
        ]),
        ItemContent::Format(key, attribute) => object([
            ("kind", Any::from("format")),
            ("key", Any::from(key.clone())),
            ("value", value(attribute, budget, 0)?),
        ]),
        ItemContent::Any(values) => object([
            ("kind", Any::from("any")),
            (
                "values",
                Any::from(
                    values
                        .iter()
                        .map(|v| value(v, budget, 0))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
            ),
        ]),
        ItemContent::Embed(v) => object([
            ("kind", Any::from("embed")),
            ("value", value(v, budget, 0)?),
        ]),
        ItemContent::JSON(values) => object([
            ("kind", Any::from("json")),
            ("values", Any::from(values.clone())),
        ]),
        ItemContent::Binary(bytes) => object([
            ("kind", Any::from("binary")),
            (
                "bytes",
                Any::from(
                    bytes
                        .iter()
                        .map(|b| Any::from(*b as u32))
                        .collect::<Vec<_>>(),
                ),
            ),
        ]),
        ItemContent::Type(branch) => {
            let (kind, name) = match branch.type_ref() {
                TypeRef::Array => ("array", Any::Null),
                TypeRef::Map => ("map", Any::Null),
                TypeRef::Text => ("text", Any::Null),
                TypeRef::XmlElement(name) => ("xml_element", Any::from(name.clone())),
                TypeRef::XmlFragment => ("xml_fragment", Any::Null),
                TypeRef::XmlText => ("xml_text", Any::Null),
                _ => return Err(FootprintError::Unretained),
            };
            object([
                ("kind", Any::from("type")),
                ("type_kind", Any::from(kind)),
                ("name", name),
            ])
        }
        ItemContent::Deleted(_) | ItemContent::Doc(_, _) => return Err(FootprintError::Unretained),
    })
}
/// Decodes the exact original update with the maintained codec. The already
/// integrated candidate resolves inferred parents, including deleted items.
/// This does not infer effects from visible output or mutate/re-encode the owner.
/// Hosts bind this evidence to the exact locked prestate/update/receipt scope.
pub fn inspect<T: ReadTxn>(
    txn: &T,
    bytes: &[u8],
    maximum_steps: usize,
) -> Result<Any, FootprintError> {
    let store = txn.store();
    if !store.skip_gc
        || store.offset_kind != crate::OffsetKind::Utf16
        || store.pending_update().is_some()
        || store.pending_ds().is_some()
    {
        return Err(FootprintError::Prestate);
    }
    if bytes.len() > 8 * 1024 * 1024 || maximum_steps == 0 || maximum_steps > 1_000_000 {
        return Err(FootprintError::Limit);
    }
    let mut decoder = DecoderV1::from(bytes);
    let update = Update::decode(&mut decoder).map_err(|_| FootprintError::Update)?;
    if !matches!(decoder.read_u8(), Err(DecodeError::EndOfBuffer(_))) {
        return Err(FootprintError::Update);
    }
    let mut budget = maximum_steps;
    let current = txn.state_vector();
    let mut structs = Vec::new();
    let mut clients = update.blocks.clients.iter().collect::<Vec<_>>();
    clients.sort_by_key(|(client, _)| **client);
    for (_, blocks) in clients {
        for block in blocks {
            step(&mut budget)?;
            let Block::Item(item) = block else {
                return Err(FootprintError::Unretained);
            };
            let stored = store
                .blocks
                .get_item(&item.id)
                .ok_or(FootprintError::Unretained)?;
            let end = item
                .id
                .clock
                .checked_add(item.len)
                .ok_or(FootprintError::Update)?;
            if end > current.get(&item.id.client) {
                return Err(FootprintError::Unretained);
            }
            structs.push(object([
                ("item", identity(item.id)),
                ("count", Any::from(item.len)),
                ("parent", parent(&stored)?),
                (
                    "key",
                    stored
                        .parent_sub
                        .clone()
                        .map(Any::from)
                        .unwrap_or(Any::Null),
                ),
                ("origin", optional_identity(item.origin)),
                ("right_origin", optional_identity(item.right_origin)),
                ("content", content(item, &mut budget)?),
                ("deleted", Any::from(stored.is_deleted())),
            ]));
        }
    }
    let mut declared = Vec::new();
    let mut deleted = Vec::new();
    let mut clients = update.delete_set.iter().collect::<Vec<_>>();
    clients.sort_by_key(|(client, _)| **client);
    for (client, ranges) in clients {
        for range in ranges.iter() {
            step(&mut budget)?;
            if range.start >= range.end {
                return Err(FootprintError::Update);
            }
            declared.push(object([
                ("item", identity(ID::new(*client, range.start))),
                ("count", Any::from(range.end - range.start)),
            ]));
            let mut clock = range.start;
            while clock < range.end {
                step(&mut budget)?;
                let id = ID::new(*client, clock);
                let stored = store
                    .blocks
                    .get_item(&id)
                    .ok_or(FootprintError::Unretained)?;
                let next = stored
                    .id
                    .clock
                    .checked_add(stored.len)
                    .ok_or(FootprintError::Update)?
                    .min(range.end);
                if next <= clock || !stored.is_deleted() {
                    return Err(FootprintError::Unretained);
                }
                deleted.push(object([
                    ("item", identity(id)),
                    ("count", Any::from(next - clock)),
                    ("stored_item", identity(stored.id)),
                    ("stored_count", Any::from(stored.len)),
                    ("parent", parent(&stored)?),
                    (
                        "key",
                        stored
                            .parent_sub
                            .clone()
                            .map(Any::from)
                            .unwrap_or(Any::Null),
                    ),
                    ("content", content(&stored, &mut budget)?),
                ]));
                clock = next;
            }
        }
    }
    Ok(object([
        ("structs", Any::from(structs)),
        ("declared_deletes", Any::from(declared)),
        ("deleted_items", Any::from(deleted)),
    ]))
}
#[cfg(test)]
mod tests {
    use crate::{Doc, GetString, Map, OffsetKind, Options, ReadTxn, Text, Transact};
    #[test]
    fn observes_hidden_transient_text_and_metadata_without_changing_owner() {
        let doc = Doc::with_options(Options {
            offset_kind: OffsetKind::Utf16,
            skip_gc: true,
            ..Options::default()
        });
        let text = doc.get_or_insert_text("default");
        let metadata = doc.get_or_insert_map("relaymark");
        text.insert(&mut doc.transact_mut(), 0, "A🌍Z");
        let before = doc.transact().state_vector();
        {
            let mut tx = doc.transact_mut();
            text.insert(&mut tx, 1, "hidden");
            text.remove_range(&mut tx, 1, 6);
            metadata.insert(&mut tx, "transient", "secret");
            metadata.remove(&mut tx, "transient");
        }
        let tx = doc.transact();
        let bytes = tx.encode_diff_v1(&before);
        let state = tx.encode_state_as_update_v1(&Default::default());
        let footprint = super::inspect(&tx, &bytes, 1_000_000).unwrap();
        let json = serde_json::to_string(&footprint).unwrap();
        assert!(json.contains("hidden"));
        assert!(json.contains("secret"));
        assert!(json.contains("declared_deletes"));
        assert!(json.contains("relaymark"));
        let exact: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(exact["structs"].as_array().unwrap().len(), 2);
        assert_eq!(exact["structs"][0]["count"], 6);
        assert_eq!(
            exact["structs"][0]["parent"],
            serde_json::json!({"root":"default"})
        );
        assert_eq!(
            exact["structs"][0]["content"],
            serde_json::json!({"kind":"string","text":"hidden"})
        );
        assert_eq!(exact["structs"][0]["deleted"], true);
        assert_eq!(
            exact["structs"][1]["parent"],
            serde_json::json!({"root":"relaymark"})
        );
        assert_eq!(exact["structs"][1]["key"], "transient");
        assert_eq!(
            exact["structs"][1]["content"],
            serde_json::json!({"kind":"any","values":["secret"]})
        );
        assert_eq!(
            exact["deleted_items"]
                .as_array()
                .unwrap()
                .iter()
                .map(|v| v["count"].as_u64().unwrap())
                .sum::<u64>(),
            7
        );

        assert_eq!(text.get_string(&tx), "A🌍Z");
        assert_eq!(tx.encode_state_as_update_v1(&Default::default()), state);
        assert!(super::inspect(&tx, &bytes, 1).is_err());
    }
}

#[cfg(test)]
#[test]
fn original_update_clock_overflow_refuses_without_panicking() {
    use crate::{Doc, OffsetKind, Options, Transact};
    let doc = Doc::with_options(Options {
        offset_kind: OffsetKind::Utf16,
        skip_gc: true,
        ..Options::default()
    });
    let bytes = [
        1, 1, 7, 255, 255, 255, 255, 15, 4, 1, 7, b'd', b'e', b'f', b'a', b'u', b'l', b't', 1,
        b'x', 0,
    ];
    assert!(inspect(&doc.transact(), &bytes, 1_000_000).is_err());
}
