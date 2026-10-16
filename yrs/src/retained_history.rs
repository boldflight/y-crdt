//! Independent, process-local retained owners for history preflight.
//!
//! This is not a wire or persistence format. Ordinary updates intentionally do
//! not carry UndoManager's redone links; reconstructing only those updates is
//! insufficient after undoing a parent deletion.
use crate::slice::ItemSlice;
use crate::updates::decoder::Decode;
use crate::{Doc, ReadTxn, StateVector, Transact, Update};

/// Fork a settled retained document without sharing mutable items or observers.
/// The result has the same identity and may only be used for local preflight:
/// its prospective updates must never be delivered as another replica's edits.
/// History installation remains the caller's exact owner/scope validation.
pub fn fork(doc: &Doc, max_blocks: usize) -> Result<Doc, &'static str> {
    let source = doc.try_transact().map_err(|_| "History owner is busy")?;
    let store = source.store();
    if !doc.skip_gc()
        || store.pending_update().is_some()
        || store.pending_ds().is_some()
        || !store.subdocs.is_empty()
        || store.parent.is_some()
        || !store.linked_by.is_empty()
    {
        return Err("History fork requires a settled retained root document");
    }
    let mut items = Vec::new();
    let mut count = 0;
    for (_, blocks) in store.blocks.iter() {
        for block in blocks.iter() {
            count += 1;
            if count > max_blocks {
                return Err("History fork exceeds block budget");
            }
            if let Some(item) = block.as_item() {
                items.push((item.id, item.len(), item.redone, item.info.is_keep()));
            }
        }
    }
    let bytes = source.encode_diff_v1(&StateVector::default());
    let fork = Doc::with_options((**doc.store.options()).clone());
    {
        let mut target = fork.transact_mut();
        target
            .apply_update(Update::decode_v1(&bytes).map_err(|_| "Invalid retained update")?)
            .map_err(|_| "Invalid retained update")?;
    }
    {
        let mut target = fork.transact_mut();
        for (id, len, redone, keep) in items {
            let ptr = target
                .store()
                .blocks
                .get_item(&id)
                .ok_or("Missing retained item")?;
            let start = id.clock - ptr.id().clock;
            let end = start
                .checked_add(len)
                .and_then(|n| n.checked_sub(1))
                .filter(|end| *end < ptr.len())
                .ok_or("Invalid retained boundary")?;
            let mut item = target
                .store_mut()
                .materialize(ItemSlice::new(ptr, start, end));
            item.redone = redone;
            if keep {
                item.info.set_keep();
            } else {
                item.info.clear_keep();
            }
        }
    }
    let target = fork.transact();
    if target.snapshot() != source.snapshot()
        || target.encode_diff_v1(&StateVector::default()) != bytes
    {
        return Err("History fork changed retained state");
    }
    drop(target);
    Ok(fork)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::undo::{Options as UndoOptions, UndoManager};
    use crate::{GetString, Options, Xml, XmlElementPrelim, XmlFragment};

    // Deletion Undo restores a different item ID. A standard update alone loses
    // the redone chain needed by the preceding attribute Undo.
    #[test]
    fn fork_preserves_rename_and_linked_task_history_without_mutating_owner() {
        for (tag, key, before, after) in [
            ("relayAnchor", "name", "later", "later_more"),
            ("taskItem", "checked", "false", "true"),
        ] {
            let doc = Doc::with_options(Options {
                guid: "retained-owner".into(),
                skip_gc: true,
                ..Options::default()
            });
            let root = doc.get_or_insert_xml_fragment("default");
            let mut manager: UndoManager<()> = UndoManager::new();
            manager.expand_scope(&doc, &root);
            manager.include_origin("local");
            manager.preserve_changed_xml(true);
            let item = {
                let mut txn = doc.transact_mut_with("local");
                let item = root.insert(&mut txn, 0, XmlElementPrelim::empty(tag));
                item.insert_attribute(&mut txn, key, before);
                if tag == "taskItem" {
                    item.insert_attribute(&mut txn, "entityID", "task-authorized-separately");
                }
                item
            };
            manager.reset();
            item.insert_attribute(&mut doc.transact_mut_with("local"), key, after);
            manager.reset();
            root.remove_range(&mut doc.transact_mut_with("local"), 0, 1);
            manager.reset();
            assert!(manager.undo_blocking());
            let original_xml = root.get_string(&doc.transact());
            let original_bytes = doc.transact().encode_diff_v1(&StateVector::default());
            let original_snapshot = doc.transact().snapshot();
            let preview = fork(&doc, 100).unwrap();
            assert_eq!(preview.guid(), doc.guid());
            let preview_root = preview.get_or_insert_xml_fragment("default");
            let mut restored = UndoManager::with_options(UndoOptions {
                init_undo_stack: manager.undo_stack().to_vec(),
                init_redo_stack: manager.redo_stack().to_vec(),
                preserve_changed_xml: true,
                ..UndoOptions::default()
            });
            restored.expand_scope(&preview, &preview_root);
            assert!(restored.undo_blocking());
            let xml = preview_root.get_string(&preview.transact());
            assert!(xml.contains(&format!("{}=\"{}\"", key, before)), "{}", xml);
            assert!(!xml.contains(&format!("{}=\"{}\"", key, after)), "{}", xml);
            if tag == "taskItem" {
                assert!(xml.contains("task-authorized-separately"));
            }
            assert!(restored.redo_blocking());
            assert_eq!(preview_root.get_string(&preview.transact()), original_xml);
            assert_eq!(root.get_string(&doc.transact()), original_xml);
            assert_eq!(doc.transact().snapshot(), original_snapshot);
            assert_eq!(
                doc.transact().encode_diff_v1(&StateVector::default()),
                original_bytes
            );
            assert!(manager.undo_blocking());
            assert!(root
                .get_string(&doc.transact())
                .contains(&format!("{}=\"{}\"", key, before)));
        }
    }

    #[test]
    fn fork_refuses_unretained_busy_and_over_budget_owners() {
        assert!(fork(&Doc::new(), 100).is_err());
        let doc = Doc::with_options(Options {
            skip_gc: true,
            ..Options::default()
        });
        let root = doc.get_or_insert_xml_fragment("default");
        root.insert(
            &mut doc.transact_mut(),
            0,
            XmlElementPrelim::empty("taskItem"),
        );
        assert!(fork(&doc, 0).is_err());
        let _busy = doc.transact_mut();
        assert!(fork(&doc, 100).is_err());
    }
}
