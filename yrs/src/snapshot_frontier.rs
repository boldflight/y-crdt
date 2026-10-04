//! Read-only causal frontier reconstruction from retained admitted items.
//! Snapshot bytes supply clocks/deletes, never new document state or authority.
use crate::encoding::read::{Error as DecodeError, Read};
use crate::updates::decoder::{Decode, DecoderV1};
use crate::updates::encoder::{Encoder, EncoderV1};
use crate::{ReadTxn, Snapshot};

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum FrontierError {
    #[error("invalid encoded sender snapshot")]
    Decode,
    #[error("sender snapshot requires a settled retained UTF-16 prestate")]
    Prestate,
    #[error("sender snapshot exceeds admitted causal frontier")]
    Frontier,
    #[error("sender snapshot includes unadmitted deletes")]
    Deletes,
    #[error("sender snapshot original items are unavailable")]
    Unretained,
    #[error("sender snapshot traversal budget exhausted")]
    Limit,
}

pub fn encode<T: ReadTxn>(
    txn: &T,
    bytes: &[u8],
    maximum_steps: usize,
) -> Result<Vec<u8>, FrontierError> {
    use crate::block::ItemContent;
    let store = txn.store();
    if !store.skip_gc
        || store.offset_kind != crate::OffsetKind::Utf16
        || store.pending_update().is_some()
        || store.pending_ds().is_some()
    {
        return Err(FrontierError::Prestate);
    }
    if bytes.len() > 1024 * 1024 || maximum_steps == 0 || maximum_steps > 1_000_000 {
        return Err(FrontierError::Limit);
    }
    let mut decoder = DecoderV1::from(bytes);
    let snapshot = Snapshot::decode(&mut decoder).map_err(|_| FrontierError::Decode)?;
    if !matches!(decoder.read_u8(), Err(DecodeError::EndOfBuffer(_))) {
        return Err(FrontierError::Decode);
    }
    let mut budget = maximum_steps;
    fn step(budget: &mut usize) -> Result<(), FrontierError> {
        *budget = budget.checked_sub(1).ok_or(FrontierError::Limit)?;
        Ok(())
    }
    let admitted = txn.snapshot();
    for (client, clock) in snapshot.state_map.iter() {
        step(&mut budget)?;
        if *clock == 0 || *clock > admitted.state_map.get(client) {
            return Err(FrontierError::Frontier);
        }
        let blocks = store
            .blocks
            .get_client(client)
            .ok_or(FrontierError::Frontier)?;
        let mut expected = 0;
        for stored in blocks.iter() {
            step(&mut budget)?;
            let block = stored.as_ref();
            let start = block.id().clock;
            if start >= *clock {
                break;
            }
            if start != expected {
                return Err(FrontierError::Unretained);
            }
            let item = stored.as_item().ok_or(FrontierError::Unretained)?;
            if matches!(item.content, ItemContent::Deleted(_)) {
                return Err(FrontierError::Unretained);
            }
            expected = start
                .checked_add(block.len().min(*clock - start))
                .ok_or(FrontierError::Unretained)?;
        }
        if expected != *clock {
            return Err(FrontierError::Unretained);
        }
    }
    for (client, _) in snapshot.delete_set.iter() {
        let ranges = snapshot
            .delete_set
            .get(client)
            .ok_or(FrontierError::Deletes)?;
        step(&mut budget)?;
        let known = admitted
            .delete_set
            .get(client)
            .ok_or(FrontierError::Deletes)?;
        if !ranges.subset_of(known) {
            return Err(FrontierError::Deletes);
        }
        for (range, _) in ranges.iter() {
            step(&mut budget)?;
            if range.is_empty() || range.end > snapshot.state_map.get(client) {
                return Err(FrontierError::Deletes);
            }
        }
    }
    let mut encoder = EncoderV1::new();
    txn.encode_state_from_snapshot(&snapshot, &mut encoder)
        .map_err(|_| FrontierError::Unretained)?;
    Ok(encoder.to_vec())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::updates::encoder::Encode;
    use crate::{Doc, GetString, OffsetKind, Options, Text, Transact, Update, ID};
    fn retained(client: u64) -> Doc {
        Doc::with_options(Options {
            client_id: crate::ClientID::new(client),
            offset_kind: OffsetKind::Utf16,
            skip_gc: true,
            ..Options::default()
        })
    }
    #[test]
    fn sender_frontier_preserves_peer_state_and_restores_sender_unicode() {
        let document = retained(7);
        let text = document.get_or_insert_text("default");
        text.insert(&mut document.transact_mut(), 0, "A🌍Z");
        let snapshot = document.transact().snapshot();
        let bytes = snapshot.encode_v1();
        let peer = retained(8);
        let peer_text = peer.get_or_insert_text("default");
        peer.transact_mut()
            .apply_update(
                Update::decode_v1(
                    &document
                        .transact()
                        .encode_state_as_update_v1(&crate::StateVector::default()),
                )
                .unwrap(),
            )
            .unwrap();
        peer_text.insert(&mut peer.transact_mut(), 0, "Peer ");
        document
            .transact_mut()
            .apply_update(
                Update::decode_v1(
                    &peer
                        .transact()
                        .encode_state_as_update_v1(&crate::StateVector::default()),
                )
                .unwrap(),
            )
            .unwrap();
        let unchanged = document
            .transact()
            .encode_state_as_update_v1(&crate::StateVector::default());
        let state = encode(&document.transact(), &bytes, 100).unwrap();
        let restored = retained(9);
        restored
            .transact_mut()
            .apply_update(Update::decode_v1(&state).unwrap())
            .unwrap();
        assert_eq!(
            restored
                .get_or_insert_text("default")
                .get_string(&restored.transact()),
            "A🌍Z"
        );
        assert_eq!(
            document
                .transact()
                .encode_state_as_update_v1(&crate::StateVector::default()),
            unchanged
        );
        assert_eq!(
            encode(&document.transact(), &bytes, 1),
            Err(FrontierError::Limit)
        );
        let mut future = snapshot.clone();
        future.state_map.set_max(crate::ClientID::new(7), 100);
        assert_eq!(
            encode(&document.transact(), &future.encode_v1(), 100),
            Err(FrontierError::Frontier)
        );
        let mut deletes = snapshot.clone();
        deletes
            .delete_set
            .insert(ID::new(crate::ClientID::new(7), 0), 1);
        assert_eq!(
            encode(&document.transact(), &deletes.encode_v1(), 100),
            Err(FrontierError::Deletes)
        );
    }
    #[test]
    fn sender_frontier_refuses_pruned_originals_even_in_retained_target() {
        let pruned = Doc::with_client_id(11);
        let text = pruned.get_or_insert_text("default");
        text.insert(&mut pruned.transact_mut(), 0, "Original");
        text.remove_range(&mut pruned.transact_mut(), 0, 8);
        let target = retained(12);
        target
            .transact_mut()
            .apply_update(
                Update::decode_v1(
                    &pruned
                        .transact()
                        .encode_state_as_update_v1(&crate::StateVector::default()),
                )
                .unwrap(),
            )
            .unwrap();
        let snapshot = target.transact().snapshot().encode_v1();
        assert_eq!(
            encode(&target.transact(), &snapshot, 100),
            Err(FrontierError::Unretained)
        );
    }
}
