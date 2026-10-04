//! Bounded read-only observation of visible UTF-16 string item runs.
//! These are CRDT identities, not application authorship or authorization.
use crate::branch::BranchID;
use crate::{ReadTxn, ID};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextItemRun {
    pub item: ID,
    pub count: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum TextItemError {
    #[error("text item traversal budget exhausted")]
    Limit,
    #[error("text items require a settled UTF-16 prestate")]
    Prestate,
    #[error("unavailable text branch or range")]
    Target,
    #[error("non-string content cannot establish string item identity")]
    Unprovable,
}

/// Traverse linked items once; cost is bounded by visited ancestors/items, not
/// repeated position lookup per character. No partial result escapes on exhaustion.
/// Output allocation is proportional to admitted string runs. Callers authorize
/// the document and validate its authored schema independently.
pub fn observe<T: ReadTxn>(
    txn: &T,
    branch_id: &BranchID,
    start: u32,
    length: u32,
    max_steps: usize,
) -> Result<Vec<TextItemRun>, TextItemError> {
    use crate::block::ItemContent;
    use crate::types::TypeRef;
    use crate::OffsetKind;
    if txn.store().offset_kind != OffsetKind::Utf16
        || txn.store().pending_update().is_some()
        || txn.store().pending_ds().is_some()
    {
        return Err(TextItemError::Prestate);
    }
    let mut budget = max_steps;
    let step = |budget: &mut usize| -> Result<(), TextItemError> {
        *budget = budget.checked_sub(1).ok_or(TextItemError::Limit)?;
        Ok(())
    };
    step(&mut budget)?;
    let branch = branch_id.get_branch(txn).ok_or(TextItemError::Target)?;
    if !matches!(
        branch.type_ref(),
        TypeRef::Text | TypeRef::XmlText | TypeRef::Undefined
    ) {
        return Err(TextItemError::Target);
    }
    let end = start
        .checked_add(length)
        .filter(|n| *n <= branch.content_len)
        .ok_or(TextItemError::Target)?;
    let mut ancestor = branch.item;
    while let Some(item) = ancestor {
        step(&mut budget)?;
        if item.is_deleted() {
            return Err(TextItemError::Target);
        }
        ancestor = item.parent.as_branch().ok_or(TextItemError::Target)?.item;
    }
    let mut runs: Vec<TextItemRun> = Vec::new();
    let mut index: u32 = 0;
    let mut next = branch.start;
    while index < end {
        let item = next.ok_or(TextItemError::Unprovable)?;
        step(&mut budget)?;
        next = item.right;
        if item.is_deleted() {
            continue;
        }
        match &item.content {
            ItemContent::Format(_, _) => {}
            ItemContent::String(_) => {
                let upper = index
                    .checked_add(item.len)
                    .ok_or(TextItemError::Unprovable)?;
                let first = start.max(index);
                let last = end.min(upper);
                if first < last {
                    let id = ID::new(
                        item.id.client,
                        item.id
                            .clock
                            .checked_add(first - index)
                            .ok_or(TextItemError::Unprovable)?,
                    );
                    let count = last - first;
                    if let Some(prior) = runs.last_mut().filter(|run| {
                        run.item.client == id.client
                            && run.item.clock.checked_add(run.count) == Some(id.clock)
                    }) {
                        prior.count = prior
                            .count
                            .checked_add(count)
                            .ok_or(TextItemError::Unprovable)?;
                    } else {
                        runs.push(TextItemRun { item: id, count });
                    }
                }
                index = upper;
            }
            _ => return Err(TextItemError::Unprovable),
        }
    }
    Ok(runs)
}

/// A visible UTF-16 string run in its actual rich XML text branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VisibleTextItemRun {
    pub branch: BranchID,
    pub item: ID,
    pub count: u32,
}

/// Observe all currently visible string identities allocated since `before`,
/// in XML document order. Traversal is bounded by structural/string items, not
/// character count. Deleted ancestors, format markers and metadata maps do not
/// contribute text. Admission/authorship and command-copy witnesses remain the
/// host's responsibility. A future vector or exhausted traversal never yields a
/// partial accounting result.
pub fn observe_visible<T: ReadTxn>(
    txn: &T,
    scope: &BranchID,
    before: &crate::StateVector,
    max_steps: usize,
) -> Result<Vec<VisibleTextItemRun>, TextItemError> {
    use crate::block::ItemContent;
    use crate::branch::Branch;
    use crate::types::TypeRef;
    let store = txn.store();
    if store.offset_kind != crate::OffsetKind::Utf16
        || store.pending_update().is_some()
        || store.pending_ds().is_some()
        || before
            .iter()
            .any(|(client, clock)| *clock > txn.state_vector().get(client))
    {
        return Err(TextItemError::Prestate);
    }
    fn step(budget: &mut usize) -> Result<(), TextItemError> {
        *budget = budget.checked_sub(1).ok_or(TextItemError::Limit)?;
        Ok(())
    }
    fn visit(
        branch: &Branch,
        before: &crate::StateVector,
        depth: usize,
        budget: &mut usize,
        runs: &mut Vec<VisibleTextItemRun>,
    ) -> Result<(), TextItemError> {
        step(budget)?;
        // A traversal resource boundary, independent of application schema depth.
        if depth > 128 {
            return Err(TextItemError::Limit);
        }
        let is_text = matches!(branch.type_ref(), TypeRef::XmlText);
        if !is_text
            && !matches!(
                branch.type_ref(),
                TypeRef::XmlElement(_) | TypeRef::XmlFragment | TypeRef::Undefined
            )
        {
            return Err(TextItemError::Target);
        }
        let branch_id = branch.id();
        let mut next = branch.start;
        while let Some(item) = next {
            step(budget)?;
            next = item.right;
            if item.is_deleted() {
                continue;
            }
            match &item.content {
                ItemContent::Type(child) if !is_text => {
                    visit(child, before, depth + 1, budget, runs)?
                }
                ItemContent::Format(_, _) if is_text => {}
                ItemContent::String(_) if is_text => {
                    let end = item
                        .id
                        .clock
                        .checked_add(item.len)
                        .ok_or(TextItemError::Unprovable)?;
                    let first = item.id.clock.max(before.get(&item.id.client));
                    if first < end {
                        let id = ID::new(item.id.client, first);
                        let count = end - first;
                        if let Some(prior) = runs.last_mut().filter(|run| {
                            run.branch == branch_id
                                && run.item.client == id.client
                                && run.item.clock.checked_add(run.count) == Some(id.clock)
                        }) {
                            prior.count = prior
                                .count
                                .checked_add(count)
                                .ok_or(TextItemError::Unprovable)?;
                        } else {
                            runs.push(VisibleTextItemRun {
                                branch: branch_id.clone(),
                                item: id,
                                count,
                            });
                        }
                    }
                }
                _ => return Err(TextItemError::Unprovable),
            }
        }
        Ok(())
    }
    let branch = scope.get_branch(txn).ok_or(TextItemError::Target)?;
    let mut budget = max_steps;
    let mut ancestor = branch.item;
    while let Some(item) = ancestor {
        step(&mut budget)?;
        if item.is_deleted() {
            return Err(TextItemError::Target);
        }
        ancestor = item.parent.as_branch().ok_or(TextItemError::Target)?.item;
    }
    let mut runs = Vec::new();
    visit(&branch, before, 0, &mut budget, &mut runs)?;
    Ok(runs)
}

/// A direct retained UndoManager redone edge. This is engine identity evidence,
/// never a claim about author, permission, operation ownership or equal prose.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RestoredTextItemRun {
    pub source_type: BranchID,
    pub source: TextItemRun,
    pub destination_type: BranchID,
    pub destination: TextItemRun,
}

/// Observe direct redone edges whose destination was allocated after `before`.
/// Capture immediately after the owned operation: Yjs update bytes do not encode
/// ephemeral redone pointers. The host must retain the resulting immutable receipt.
/// Deleted source ancestors are valid retained evidence; destinations must remain
/// live under the exact supplied scope. Equal text without a redone edge is ignored.
pub fn observe_restored<T: ReadTxn>(
    txn: &T,
    scope: &BranchID,
    before: &crate::StateVector,
    max_steps: usize,
) -> Result<Vec<RestoredTextItemRun>, TextItemError> {
    use crate::block::ItemContent;
    use crate::branch::BranchPtr;
    use crate::types::TypeRef;
    use crate::OffsetKind;
    let store = txn.store();
    if !store.skip_gc
        || store.offset_kind != OffsetKind::Utf16
        || store.pending_update().is_some()
        || store.pending_ds().is_some()
    {
        return Err(TextItemError::Prestate);
    }
    let current = txn.state_vector();
    if before
        .iter()
        .any(|(client, clock)| *clock > current.get(client))
    {
        return Err(TextItemError::Prestate);
    }
    let mut budget = max_steps;
    fn step(budget: &mut usize) -> Result<(), TextItemError> {
        *budget = budget.checked_sub(1).ok_or(TextItemError::Limit)?;
        Ok(())
    }
    fn scoped(
        mut branch: BranchPtr,
        scope: &BranchID,
        live: bool,
        budget: &mut usize,
    ) -> Result<bool, TextItemError> {
        loop {
            step(budget)?;
            if &branch.id() == scope {
                return Ok(true);
            }
            let Some(item) = branch.item else {
                return Ok(false);
            };
            if live && item.is_deleted() {
                return Ok(false);
            }
            branch = *item.parent.as_branch().ok_or(TextItemError::Unprovable)?;
        }
    }
    let mut result = Vec::new();
    // Struct traversal is bounded independently from output size and string length.
    for (_, blocks) in store.blocks.iter() {
        for block in blocks.iter() {
            step(&mut budget)?;
            let Some(source) = block.as_item() else {
                continue;
            };
            let Some(target) = source.redone else {
                continue;
            };
            if !matches!(source.content, ItemContent::String(_))
                || source.id.clock >= before.get(&source.id.client)
                || target.clock < before.get(&target.client)
            {
                continue;
            }
            let count = source.len;
            if source
                .id
                .clock
                .checked_add(count)
                .filter(|end| *end <= before.get(&source.id.client))
                .is_none()
            {
                return Err(TextItemError::Unprovable);
            }
            let source_parent = source.parent.as_branch().ok_or(TextItemError::Unprovable)?;
            if !matches!(
                source_parent.type_ref(),
                TypeRef::Text | TypeRef::XmlText | TypeRef::Undefined
            ) || !scoped(*source_parent, scope, false, &mut budget)?
            {
                continue;
            }
            let mut offset = 0;
            while offset < count {
                step(&mut budget)?;
                let destination_id = ID::new(
                    target.client,
                    target
                        .clock
                        .checked_add(offset)
                        .ok_or(TextItemError::Unprovable)?,
                );
                let destination = store
                    .blocks
                    .get_item_clean_start(&destination_id)
                    .ok_or(TextItemError::Unprovable)?;
                let ptr = destination.ptr;
                if ptr.is_deleted() || !matches!(ptr.content, ItemContent::String(_)) {
                    return Err(TextItemError::Unprovable);
                }
                let parent = ptr.parent.as_branch().ok_or(TextItemError::Unprovable)?;
                if !matches!(
                    parent.type_ref(),
                    TypeRef::Text | TypeRef::XmlText | TypeRef::Undefined
                ) || !scoped(*parent, scope, true, &mut budget)?
                {
                    return Err(TextItemError::Target);
                }
                let n = (count - offset).min(destination.len());
                if n == 0 {
                    return Err(TextItemError::Unprovable);
                }
                result.push(RestoredTextItemRun {
                    source_type: source_parent.id(),
                    source: TextItemRun {
                        item: ID::new(source.id.client, source.id.clock + offset),
                        count: n,
                    },
                    destination_type: parent.id(),
                    destination: TextItemRun {
                        item: destination_id,
                        count: n,
                    },
                });
                offset = offset.checked_add(n).ok_or(TextItemError::Unprovable)?;
            }
        }
    }
    result.sort_by_key(|r| (r.destination.item.client, r.destination.item.clock));
    for adjacent in result.windows(2) {
        let a = &adjacent[0].destination;
        let b = &adjacent[1].destination;
        if a.item.client == b.item.client
            && a.item
                .clock
                .checked_add(a.count)
                .ok_or(TextItemError::Unprovable)?
                > b.item.clock
        {
            return Err(TextItemError::Unprovable);
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Any, Doc, OffsetKind, Options, StateVector, Text, Transact};
    use std::sync::Arc;
    #[test]
    fn visible_runs_preserve_utf16_clocks_deleted_gaps_and_format_items_without_mutation() {
        let doc = Doc::with_options(Options {
            offset_kind: OffsetKind::Utf16,
            skip_gc: true,
            ..Options::default()
        });
        let text = doc.get_or_insert_text("text");
        text.insert(&mut doc.transact_mut(), 0, "A🌍Z");
        text.format(
            &mut doc.transact_mut(),
            1,
            2,
            [(Arc::from("bold"), Any::Map(Arc::new(Default::default())))].into(),
        );
        let branch = BranchID::Root(Arc::from("text"));
        let txn = doc.transact();
        let before = txn.encode_state_as_update_v1(&StateVector::default());
        let runs = observe(&txn, &branch, 1, 2, 100).unwrap();
        assert_eq!(
            runs,
            vec![TextItemRun {
                item: ID::new(doc.client_id(), 1),
                count: 2
            }]
        );
        assert_eq!(
            txn.encode_state_as_update_v1(&StateVector::default()),
            before
        );
        assert_eq!(observe(&txn, &branch, 0, 4, 1), Err(TextItemError::Limit));
        assert_eq!(
            observe(&txn, &branch, 4, 1, 100),
            Err(TextItemError::Target)
        );
        drop(txn);
        text.remove_range(&mut doc.transact_mut(), 1, 2);
        let txn = doc.transact();
        assert_eq!(
            observe(&txn, &branch, 0, 2, 100).unwrap(),
            vec![
                TextItemRun {
                    item: ID::new(doc.client_id(), 0),
                    count: 1
                },
                TextItemRun {
                    item: ID::new(doc.client_id(), 3),
                    count: 1
                }
            ]
        );
    }
    #[test]
    fn long_single_string_uses_item_budget_and_deleted_xml_ancestors_refuse() {
        use crate::{SharedRef, XmlElementPrelim, XmlFragment, XmlTextPrelim};
        let doc = Doc::with_options(Options {
            offset_kind: OffsetKind::Utf16,
            skip_gc: true,
            ..Options::default()
        });
        let root = doc.get_or_insert_xml_fragment("default");
        let text = {
            let mut txn = doc.transact_mut();
            let q = root.push_back(&mut txn, XmlElementPrelim::empty("questionBlock"));
            q.push_back(&mut txn, XmlTextPrelim::new("x".repeat(250000)))
        };
        let branch = text.hook().id().clone();
        let runs = observe(&doc.transact(), &branch, 0, 250000, 8).unwrap();
        let scope_runs = observe_visible(
            &doc.transact(),
            &root.hook().id(),
            &StateVector::default(),
            8,
        )
        .unwrap();
        assert_eq!(scope_runs.len(), 1);
        assert_eq!(scope_runs[0].count, 250000);
        let mut future = doc.transact().state_vector();
        future.inc_by(doc.client_id(), 1);
        assert_eq!(
            observe_visible(&doc.transact(), &root.hook().id(), &future, 8),
            Err(TextItemError::Prestate)
        );
        assert_eq!(runs.len(), 1);
        assert_eq!(runs[0].count, 250000);
        root.remove_range(&mut doc.transact_mut(), 0, 1);
        assert_eq!(
            observe(&doc.transact(), &branch, 0, 1, 8),
            Err(TextItemError::Target)
        );
    }
    #[test]
    fn scope_observer_accounts_for_new_text_in_independent_rich_leaves() {
        use crate::{SharedRef, XmlElementPrelim, XmlFragment, XmlTextPrelim};
        let doc = Doc::with_options(Options {
            client_id: crate::block::ClientID::new(7),
            offset_kind: OffsetKind::Utf16,
            skip_gc: true,
            ..Options::default()
        });
        let root = doc.get_or_insert_xml_fragment("default");
        let (label, option) = {
            let mut tx = doc.transact_mut();
            let q = root.push_back(&mut tx, XmlElementPrelim::empty("questionBlock"));
            let l = q.push_back(&mut tx, XmlElementPrelim::empty("questionLabel"));
            let label = l.push_back(&mut tx, XmlTextPrelim::new("A🌍Z"));
            let o = q.push_back(&mut tx, XmlElementPrelim::empty("questionOption"));
            let option = o.push_back(&mut tx, XmlTextPrelim::new("Choice"));
            (label, option)
        };
        let before = doc.transact().state_vector();
        assert_eq!(before.get(&doc.client_id()), 15);
        label.insert(&mut doc.transact_mut(), 4, "!"); // merged string, clipped to post-vector clocks
        option.insert(&mut doc.transact_mut(), 6, "🌍"); // a second, independently edited option must not be omitted
        let tx = doc.transact();
        let state = tx.encode_state_as_update_v1(&StateVector::default());
        let runs = observe_visible(&tx, &root.hook().id(), &before, 100).unwrap();
        assert_eq!(
            runs,
            vec![
                VisibleTextItemRun {
                    branch: label.hook().id().clone(),
                    item: ID::new(crate::block::ClientID::new(7), 15),
                    count: 1
                },
                VisibleTextItemRun {
                    branch: option.hook().id().clone(),
                    item: ID::new(crate::block::ClientID::new(7), 16),
                    count: 2
                }
            ]
        );
        assert_eq!(tx.encode_state_as_update_v1(&StateVector::default()), state);
        assert_eq!(
            observe_visible(&tx, &root.hook().id(), &before, 1),
            Err(TextItemError::Limit)
        );
        drop(tx);
        option.remove_range(&mut doc.transact_mut(), 6, 2);
        assert_eq!(
            observe_visible(&doc.transact(), &root.hook().id(), &before, 100)
                .unwrap()
                .len(),
            1
        );
        root.remove_range(&mut doc.transact_mut(), 0, 1);
        assert!(
            observe_visible(&doc.transact(), &root.hook().id(), &before, 100)
                .unwrap()
                .is_empty()
        );
    }
    #[test]
    fn restored_runs_require_actual_redone_edges_and_exclude_identical_peer_text() {
        use crate::{SharedRef, UndoManager, XmlElementPrelim, XmlFragment, XmlTextPrelim};
        let doc = Doc::with_options(Options {
            offset_kind: OffsetKind::Utf16,
            skip_gc: true,
            ..Options::default()
        });
        let root = doc.get_or_insert_xml_fragment("default");
        let text = {
            let mut tx = doc.transact_mut();
            let q = root.push_back(&mut tx, XmlElementPrelim::empty("questionOption"));
            q.push_back(&mut tx, XmlTextPrelim::new("A🌍Z"))
        };
        let scope = root.hook().id().clone();
        let branch = text.hook().id().clone();
        let original = observe(&doc.transact(), &branch, 1, 2, 100).unwrap()[0].item;
        let mut manager = UndoManager::new();
        manager.expand_scope(&doc, &root);
        manager.include_origin("owner");
        text.remove_range(&mut doc.transact_mut_with("owner"), 1, 2);
        manager.reset();
        text.insert(&mut doc.transact_mut_with("peer"), 1, "🌍");
        let before = doc.transact().state_vector();
        assert!(observe_restored(&doc.transact(), &scope, &before, 1000)
            .unwrap()
            .is_empty());
        assert!(manager.undo_blocking());
        let tx = doc.transact();
        let state = tx.encode_state_as_update_v1(&StateVector::default());
        let copies = observe_restored(&tx, &scope, &before, 1000).unwrap();
        assert_eq!(copies.len(), 1);
        assert_eq!(copies[0].source.item, original);
        assert_eq!(copies[0].source.count, 2);
        assert_eq!(copies[0].source_type, branch);
        assert_eq!(copies[0].destination_type, branch);
        assert!(copies[0].destination.item.clock >= before.get(&copies[0].destination.item.client));
        assert_eq!(copies[0].destination.count, 2);
        assert_eq!(tx.encode_state_as_update_v1(&StateVector::default()), state);
        assert_eq!(
            observe_restored(&tx, &scope, &before, 1),
            Err(TextItemError::Limit)
        );
        drop(tx);
        assert!(manager.redo_blocking());
        let before_second = doc.transact().state_vector();
        assert!(manager.undo_blocking());
        let second = observe_restored(&doc.transact(), &scope, &before_second, 1000).unwrap();
        assert_eq!(second.len(), 1);
        assert_ne!(second[0].destination.item, copies[0].destination.item);
        assert_ne!(second[0].source.item, original); // the direct maintained edge, not a text-matched root shortcut
        assert_eq!(
            observe_restored(
                &doc.transact(),
                &BranchID::Root(Arc::from("elsewhere")),
                &before_second,
                1000
            )
            .unwrap()
            .len(),
            0
        );
    }
}
