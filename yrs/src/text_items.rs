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
        assert_eq!(runs.len(), 1);
        assert_eq!(runs[0].count, 250000);
        root.remove_range(&mut doc.transact_mut(), 0, 1);
        assert_eq!(
            observe(&doc.transact(), &branch, 0, 1, 8),
            Err(TextItemError::Target)
        );
    }
}
