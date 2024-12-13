use crate::{
  collections::climb::{
    glyph::CLiMBTreeNodeGlyph, CLiMBTreeKey, CLiMBTreeValue,
  },
  util::debug::{CloneDebugIterator, SimpleMapDebug},
  ArcGlyph, Glyph, GlyphErr, GlyphOffset,
};
use alloc::{
  collections::{BTreeMap, BTreeSet},
  sync::Arc,
};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
  mem::{replace, transmute},
};
use smallvec::SmallVec;

pub struct UpdateContext<K, V>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  /// The number of bytes necessary to store the contents of this `UpdateSet`.
  ///
  /// This includes any offsets, if necessary, but does not include any padding
  /// for the offsets table, as whether that's required can't be known
  /// without also knowing what would be in the rest of the node.
  known_enc_length: Option<(usize, usize)>,

  /// New entries to add to the tree
  entries: BTreeMap<UnsafeUpdateCell<K>, UnsafeUpdateCell<V>>,

  /// New tombstones
  tombstones: BTreeSet<UnsafeUpdateCell<K>>,

  /// References to parent nodes from which we keep pointers.
  referenced_nodes: ReferencedNodes,
}

impl<K, V> UpdateContext<K, V>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  /// Creates a new empty `UpdateSet`.
  pub(super) fn new() -> Self {
    Self {
      known_enc_length: Some((0, 0)),
      entries:          Default::default(),
      tombstones:       Default::default(),
      referenced_nodes: ReferencedNodes::new(),
    }
  }

  /// The number of entries (key/value pairs) in the update set.
  pub(super) fn num_entries(&self) -> usize {
    self.entries.len()
  }

  /// The number of tombstone keys in the update set.
  pub(super) fn num_tombstones(&self) -> usize {
    self.tombstones.len()
  }

  /// The total number of entries and tombstones in the update set.
  pub(super) fn num_items(&self) -> usize {
    self.num_tombstones() + self.entries.len()
  }

  /// Returns the number of bytes necessary to encode the tombstones and entries in this update,
  /// respectively.
  ///
  /// Returns: A tuple containing the number of bytes necessary to encode the tombstones and the
  /// number of bytes necessary to encode the entries, _including offsets if necessary_.
  pub fn get_encode_length(&mut self) -> (usize, usize) {
    if let Some((tombstones_len, entries_len)) = self.known_enc_length {
      (tombstones_len, entries_len)
    } else {
      unsafe {
        let tombstones_len: usize = if let Some(key_len) = K::FIXED_LEN {
          key_len * self.tombstones.len()
        } else {
          let mut len = self.tombstones.len() * size_of::<GlyphOffset>();
          for key in self.tombstones.iter() {
            len += K::length(key.as_ref());
          }
          len
        };
        let entries_len: usize = if let (Some(key_len), Some(val_len)) =
          (K::FIXED_LEN, V::FIXED_LEN)
        {
          (key_len + val_len) * self.entries.len()
        } else {
          let mut len = self.entries.len() * size_of::<GlyphOffset>();
          for (key, value) in self.entries.iter() {
            len += K::length(key.as_ref());
            len += V::length(value.as_ref());
          }
          len
        };
        self.known_enc_length = Some((tombstones_len, entries_len));
        (tombstones_len, entries_len)
      }
    }
  }

  /// Returns a reference to the first key in the update set.
  pub fn first_key(&self) -> Option<K::RefType<'_>> {
    // Safety: See note at the top of this impl block.
    unsafe {
      match (self.entries.first_key_value(), self.tombstones.first()) {
        (Some((key, _value)), Some(tombstone)) => {
          if key < tombstone {
            Some(key.as_ref())
          } else {
            Some(tombstone.as_ref())
          }
        },
        (Some((key, _value)), None) => Some(key.as_ref()),
        (None, Some(tombstone)) => Some(tombstone.as_ref()),
        (None, None) => None,
      }
    }
  }

  /// Returns a reference to the last key in the update set.
  pub fn last_key(&self) -> Option<K::RefType<'_>> {
    // Safety: See note at the top of this impl block.
    unsafe {
      match (self.entries.last_key_value(), self.tombstones.last()) {
        (Some((key, _value)), Some(tombstone)) => {
          if key > tombstone {
            Some(key.as_ref())
          } else {
            Some(tombstone.as_ref())
          }
        },
        (Some((key, _value)), None) => Some(key.as_ref()),
        (None, Some(tombstone)) => Some(tombstone.as_ref()),
        (None, None) => None,
      }
    }
  }

  /// Returns an iterator over the update set's tombstones.
  ///
  /// This function is primarily intended to be used to create an iterator
  /// that can be passed on to [`climb_glyph_encode()`].  Note that this should
  /// not be used when writing leaf nodes, as tombstones are only relevant in
  /// intermediate tree nodes.
  pub fn tombstones(&self) -> impl Iterator<Item = K::RefType<'_>> + Clone {
    // Safety: See note at the top of this impl block.
    unsafe { self.tombstones.iter().map(|uc| uc.as_ref()) }
  }

  /// Returns an iterator over the update set's entries.
  ///
  /// This function is primarily intended to be used to create an iterator
  /// that can be passed on to [`climb_glyph_encode()`].
  pub fn entries(
    &self,
  ) -> impl Iterator<Item = (K::RefType<'_>, V::RefType<'_>)> + Clone {
    // Safety: See note at the top of this impl block.
    unsafe { self.entries.iter().map(|(k, v)| (k.as_ref(), v.as_ref())) }
  }

  /// Returns an iterator over the glyphs (potentially) referenced in this
  /// update.
  pub fn referenced_glyphs(
    &self,
  ) -> impl Iterator<Item = &'_ ArcGlyph> + Clone {
    IterUpdateContextParents {
      referenced_nodes: Some(&self.referenced_nodes),
      index:            0,
    }
  }

  /// Have this update context keep a reference.
  ///
  /// Calling this function is necessary when adding pointers.
  pub fn keep_reference(&mut self, glyph: ArcGlyph) {
    self.referenced_nodes.nodes.push(glyph);
  }

  /// Adds a tombstone into the update set, as if it took place after any data
  /// in the update set.
  ///
  /// # Conflicts
  ///
  /// - If there is already an entry in the update set with the same key, that
  ///   entry will be removed.
  /// - If there is already a tombstone with this key in the update set, it will
  ///   remain present--it is relevant until it gets to the very bottom of the
  ///   tree.
  ///
  /// # Safety
  ///
  /// If the tombstone is based on a reference, that reference must remain valid
  /// for the lifetime of this update context.  See [`Self::keep_reference()`].
  pub(super) unsafe fn add_newer_tombstone(
    &mut self,
    tombstone: UnsafeUpdateCell<K>,
  ) {
    // Since it's a newer tombstone, we can remove any existing (older entries)
    if let Some(removed_val) = self.entries.remove(&tombstone) {
      if let Some((_tombstones_len, entries_len)) = &mut self.known_enc_length {
        *entries_len -= K::length(tombstone.as_ref());
        *entries_len -= V::length(removed_val.as_ref());
        if K::FIXED_LEN.is_none() | V::FIXED_LEN.is_none() {
          *entries_len -= size_of::<GlyphOffset>();
        }
      }
    }

    let key_len = K::length(tombstone.as_ref());
    if self.tombstones.insert(tombstone) {
      if let Some((tombstones, _entries_len)) = &mut self.known_enc_length {
        *tombstones += key_len;
        if K::FIXED_LEN.is_none() {
          *tombstones += size_of::<GlyphOffset>();
        }
      }
    }
  }

  pub(super) fn add_newer_tombstone_owned(&mut self, tombstone: impl Into<K>) {
    let tombstone: K = tombstone.into();
    let tombstone = UnsafeUpdateCell::from_val(tombstone);
    // SAFETY: No pointer guarantees necessary for owned valued.
    unsafe {
      self.add_newer_tombstone(tombstone);
    }
  }

  /// Adds an entry into the update set, as if it took place after any data in
  /// the update set.
  ///
  /// # Conflicts
  ///
  /// - If there is already an entry in the update set with the same key, what
  ///   happens will be determined by the value type.  If [`V::REDUCE`] is
  ///   `false`, then the new entry will replace the old entry.  If not, then
  ///   the [`V::reduce()`] will be called.  If that function call results
  ///   returns `Some(V)`, then that value will replace the existing value. If
  ///   it returns `None`, the two values have annihilated each other; the entry
  ///   will be removed and a tombstone with the same key will be added if it
  ///   is not present already.
  /// - If there is already a tombstone in the update set with the same key,
  ///   it will remain present--it is relevent until it gets to the very bottom
  ///   of the tree.
  ///
  /// # Safety
  ///
  /// If the tombstone is based on a reference, that reference must remain valid
  /// for the lifetime of this update context.  See [`Self::keep_reference()`].
  pub(super) unsafe fn add_newer_entry(
    &mut self,
    new_key: UnsafeUpdateCell<K>,
    new_value: UnsafeUpdateCell<V>,
  ) {
    unsafe {
      if let Some(older_value) = self.entries.get(&new_key) {
        if V::REDUCE {
          if let Some(reduced) =
            V::reduce(older_value.as_ref(), new_value.as_ref())
          {
            // Replace the old k/v entry with the new one
            if let Some((_tombstones_len, entries_len)) =
              &mut self.known_enc_length
            {
              *entries_len -= V::length(older_value.as_ref());
              *entries_len += V::length(reduced.as_ref());
            }
            self.entries.insert(new_key, new_value);
          } else {
            // Reduction was annihilation; remove entry and add tombstone.
            if let Some((_tombstones_len, entries_len)) =
              &mut self.known_enc_length
            {
              *entries_len -= K::length(new_key.as_ref());
              *entries_len -= V::length(older_value.as_ref());
              if K::FIXED_LEN.is_none() | V::FIXED_LEN.is_none() {
                *entries_len -= size_of::<GlyphOffset>();
              }
            }
            self.entries.remove(&new_key);
            let new_key_len = K::length(new_key.as_ref());
            if self.tombstones.insert(new_key) {
              if let Some((tombstones_len, _entries_len)) =
                &mut self.known_enc_length
              {
                *tombstones_len += new_key_len;
                if K::FIXED_LEN.is_none() {
                  *tombstones_len += size_of::<GlyphOffset>();
                }
              }
            }
          }
        } else {
          // Reduce is disabled, replace the old entry with the new one.
          // Value's length changes, but not key or offsets.
          if let Some((_tombstones_len, entries_len)) =
            &mut self.known_enc_length
          {
            *entries_len -= V::length(older_value.as_ref());
            *entries_len += V::length(new_value.as_ref());
          }
          self.entries.insert(new_key, new_value);
        }
      } else {
        // No existing entry to displace; simply track length and add.
        if let Some((_, entries_len)) = &mut self.known_enc_length {
          *entries_len += K::length(new_key.as_ref());
          *entries_len += V::length(new_value.as_ref());
          if K::FIXED_LEN.is_none() | V::FIXED_LEN.is_none() {
            *entries_len += size_of::<GlyphOffset>();
          }
        }
        self.entries.insert(new_key, new_value);
      }
    }
  }

  pub(super) fn add_newer_entry_owned(
    &mut self,
    new_key: impl Into<K>,
    new_value: impl Into<V>,
  ) {
    let key: K = new_key.into();
    let key = UnsafeUpdateCell::from_val(key);
    let value: V = new_value.into();
    let value = UnsafeUpdateCell::from_val(value);

    // SAFETY: No pointer guarantees necessary for owned valued.
    unsafe { self.add_newer_entry(key, value) }
  }

  /// Adds the tombstone to the update set.
  ///
  /// Note that tombstones must be included even if there is an entry in the
  /// update set with the same key, as the existence of the tombstone is
  /// necessary to prevent reduction with entries that existed before the
  /// tombstone we're adding here.  In other words... without the tombstone, the
  /// query would keep going until it reaches the bottom of the tree, and there
  /// may be old (now deleted) entries on the way down.
  ///
  /// SAFETY: Callers must ensure that the pointers they're adding here remain
  ///         valid for the life of this object.  This is typically done by
  ///         keeping a clone of an [`ArcGlyph`] backing an existing node.
  pub(super) unsafe fn add_older_tombstone(
    &mut self,
    key: UnsafeUpdateCell<K>,
  ) {
    // The tombstone only gets added if it's not already there.
    let key: UnsafeUpdateCell<K> = key.into();
    let key_length = K::length(key.as_ref());
    if self.tombstones.insert(key) {
      if let Some((tombstones_len, _entries_len)) = &mut self.known_enc_length {
        *tombstones_len += key_length;
        if K::FIXED_LEN.is_none() {
          *tombstones_len += size_of::<GlyphOffset>();
        }
      }
    }
    // else tombstone was already there, adding an even older one has no effect.
  }

  pub(super) fn add_older_tombstone_owned(&mut self, key: impl Into<K>) {
    let key: K = key.into();
    let key = UnsafeUpdateCell::from_val(key);
    // SAFETY: No pointer guarantees necessary for owned valued.
    unsafe { self.add_older_tombstone(key) };
  }

  /// Adds an entry from an older node into the update set.
  ///
  /// - If the entry key is present as a tombstone, the old key and value are
  ///   not added to the update set.
  /// - If there is no tombstone for the old entry key, but there is an existing
  ///   newer entry with that key, a reduction operation is performed by
  ///   calling [`ClimbTreeValue::update`] with the pair of values.
  /// - Otherwise, the entry is added to the `UpdateSet` without modification.
  ///
  /// SAFETY: Callers must ensure that the pointers they're adding here remain
  ///         valid for the life of this object.  This is typically done by
  ///         keeping a clone of an [`ArcGlyph`] backing an existing node.
  pub(super) unsafe fn add_older_entry(
    &mut self,
    key: UnsafeUpdateCell<K>,
    old_value: UnsafeUpdateCell<V>,
  ) {
    // If there's already a tombstones for this key, we don't need to process it
    // because the entry has already been deleted.
    if self.tombstones.get(&key).is_none() {
      // If there's already an entry with this key, we need to reduce.
      if let Some(current_value) = self.entries.get_mut(&key) {
        if V::REDUCE {
          match V::reduce(old_value.as_ref(), current_value.as_ref()) {
            None => {
              // Values cancelled each other out, remove existing value
              self.add_newer_tombstone(key)
            },
            Some(reduced) => {
              if let Some((_tombstone_len, entries_len)) =
                &mut self.known_enc_length
              {
                // Key and offset remain unchanged, all we need to do is account
                // for the difference in length between the two entries.
                *entries_len -= V::length(current_value.as_ref());
                *entries_len += V::length(reduced.as_ref());
              }

              // Replace old with new value.
              *current_value = UnsafeUpdateCell::Owned(reduced);
            },
          }
        }
      } else {
        // There's no newer entry or tombstone, include the old data.
        if let Some((_tombstones_len, entries_len)) = &mut self.known_enc_length
        {
          *entries_len += K::length(key.as_ref());
          *entries_len += V::length(old_value.as_ref());
          if K::FIXED_LEN.is_none() | V::FIXED_LEN.is_none() {
            *entries_len += size_of::<GlyphOffset>();
          }
        }
        self.entries.insert(key, old_value);
      }
    }
  }

  pub(super) fn add_older_entry_owned(
    &mut self,
    key: impl Into<K>,
    value: impl Into<V>,
  ) {
    let key: K = key.into();
    let key = UnsafeUpdateCell::from_val(key);
    let value: V = value.into();
    let value = UnsafeUpdateCell::from_val(value);
    // SAFETY: No pointer guarantees necessary for owned valued.
    unsafe { self.add_older_entry(key, value) };
  }

  /// Add the entries and tombstones from an older node to the update set.
  ///
  /// The node must be based on an [`ArcGlyph`], because we'll be taking
  /// pointers into the old node and must ensure that they remain valid.
  pub(super) fn add_older_node(
    &mut self,
    node: &CLiMBTreeNodeGlyph<ArcGlyph, K, V>,
  ) -> Result<(), GlyphErr> {
    unsafe {
      let referenced_node = node.clone_arc_inner();
      self.referenced_nodes.add_node(referenced_node);

      for (old_key, old_value) in node.iter_entries() {
        // SAFETY: Requires the update context to keep a reference to the underlying glyph (see above).
        self.add_older_entry(
          UnsafeUpdateCell::from_ref(old_key),
          UnsafeUpdateCell::from_ref(old_value),
        );
      }

      // Iterate through all the tombstones in the old node.  Add them to the
      // update set iff they do not match an existing entry in the update set.
      for old_tombstone in node.iter_tombstones() {
        self.add_older_tombstone(UnsafeUpdateCell::from_ref(old_tombstone))
      }
    }
    Ok(())
  }

  /// When we get down to the leaf level, we no longer need to keep tombstones.
  pub fn drop_tombstones(&mut self) {
    if let Some((tombstones_len, _entries_len)) = &mut self.known_enc_length {
      *tombstones_len = 0;
    }
    self.tombstones.clear();
  }

  pub fn split_at_key(
    &mut self,
    split_key: K::RefType<'_>,
    lower_known_length: Option<(usize, usize)>,
  ) -> Self {
    // SAFETY: We're not keeping the reference, we're just using it to split the update set.
    let split_key = unsafe { UnsafeUpdateCell::from_ref(split_key) };

    let high_entries = self.entries.split_off(&split_key);
    let high_tombstones = self.tombstones.split_off(&split_key);

    let low_entries = replace(&mut self.entries, high_entries);
    let low_tombstones = replace(&mut self.tombstones, high_tombstones);
    let referenced_nodes = self.referenced_nodes.clone();

    // If we know the encode length of the lower keys, then we also know
    // how removing them will affect the encoding length of the higher keys
    if let (
      Some((low_tomb_len, low_entry_len)),
      Some((high_tomb_len, high_entry_len)),
    ) = (&lower_known_length, &mut self.known_enc_length)
    {
      *high_tomb_len -= *low_tomb_len;
      *high_entry_len -= *low_entry_len;
    } else {
      self.known_enc_length = None;
    }

    Self {
      known_enc_length: lower_known_length,
      entries: low_entries,
      tombstones: low_tombstones,
      referenced_nodes,
    }
  }

  /// Splits off a (lower keys) portion of the update that fits into the
  /// specified # of bytes.
  ///
  /// - If the entire node fits into the space specified, return `None`.
  /// - Otherwise, return a new `UpdateContext` that fits into the specified
  ///   size, and removes those tombstones, keys, and values from this one.
  pub fn split_at_enc_bytes(&mut self, enc_bytes: usize) -> Option<Self> {
    // We already keep track of the total.  If that fits, we can short-circuit counting
    // everything and just return None.
    let (unsplit_tombstones_len, unsplit_entries_len) =
      self.get_encode_length();
    if unsplit_tombstones_len + unsplit_entries_len < enc_bytes {
      return None;
    }

    // Determine the split key, keep track of bytes and #offsets we'd be
    // removing separately--we need to alter the former to update the remainder
    unsafe {
      let mut split_tombstones_len = 0;
      let mut split_entries_len = 0;
      let mut tombstones_iter = self.tombstones.iter().peekable();
      for (entry_key, entry_value) in self.entries.iter() {
        /* Advance tombstones until the NEXT key is greater than the entries key
        We use peek() here because we don't want to advance the tombstones
        iterator if its next key is already greater than the entry key.
        */
        while let Some(tombstone_key) = tombstones_iter.peek() {
          if K::climb_tree_ord(tombstone_key.as_ref(), entry_key.as_ref())
            != Ordering::Greater
          {
            let mut tombstone_len = K::length(tombstone_key.as_ref());
            if K::FIXED_LEN.is_none() {
              tombstone_len += size_of::<GlyphOffset>();
            }
            // If this tombstone puts us over the limit...
            if split_tombstones_len + split_entries_len + tombstone_len
              > enc_bytes
            {
              let split_key = (*tombstone_key).clone();
              return Some(self.split_at_key(
                split_key.as_ref(),
                Some((split_tombstones_len, split_entries_len)),
              ));
            }
            split_tombstones_len += tombstone_len;
            tombstones_iter.next();
          } else {
            break;
          }
        }

        // Now check the entry
        let mut entry_len = K::length(entry_key.as_ref());
        entry_len += V::length(entry_value.as_ref());
        if K::FIXED_LEN.is_none() | V::FIXED_LEN.is_none() {
          entry_len += size_of::<GlyphOffset>();
        }
        // If this entry would exceed the length limit...
        if split_tombstones_len + split_entries_len + entry_len > enc_bytes {
          // Before we return, what if there's already a tombstone with this key?
          // it won't be in the split, but we've already counted its length.
          // length needs to be upadted to remove it.
          if self.tombstones.contains(entry_key) {
            split_tombstones_len -= K::length(entry_key.as_ref());
            if K::FIXED_LEN.is_none() {
              split_tombstones_len -= size_of::<GlyphOffset>();
            }
          }
          let split_key = (*entry_key).clone();
          return Some(self.split_at_key(
            split_key.as_ref(),
            Some((split_tombstones_len, split_entries_len)),
          ));
        } else {
          split_entries_len += entry_len;
        }

        // Key in the tombstones iterator is now greater, this key fits, ready
        // to check the next key.
      }

      // We got through all the entry keys, but we still might have tombstones left
      while let Some(tombstone_key) = tombstones_iter.next() {
        let mut tombstone_len = K::length(tombstone_key.as_ref());
        if K::FIXED_LEN.is_none() {
          tombstone_len += size_of::<GlyphOffset>();
        }
        if split_tombstones_len + split_entries_len + tombstone_len > enc_bytes
        {
          let split_key = (*tombstone_key).clone();
          return Some(self.split_at_key(
            split_key.as_ref(),
            Some((split_tombstones_len, split_entries_len)),
          ));
        } else {
          split_tombstones_len += tombstone_len;
        }
      }

      /* We got through all entries and tombstones without hitting the limit,
        but we should have caught that earlier!  Return `None`, but emit a log
        statement first.
      */

      log::debug!("CLiMB Tree Update Context stored length was higher than actual length!");
      None
    }
  }
}

impl<K: CLiMBTreeKey, V: CLiMBTreeValue> Debug for UpdateContext<K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("UpdateContext");
    if let Some(known_length) = self.known_enc_length {
      df.field("known_length", &known_length);
    } else {
      df.field("known_length", &Option::<usize>::None);
    }
    df.field("tombstones", &self.tombstones.iter().clone_debug());
    df.field(
      "entries",
      &self
        .entries
        .iter()
        .map(|(k, v)| SimpleMapDebug(k, v))
        .clone_debug(),
    );
    let nodes_iter = self.referenced_glyphs();
    let nodes_iter = nodes_iter
      .map(|ag| SimpleMapDebug(ag.as_ref().as_ptr(), ag.glyph_hash()));
    let nodes_iter = nodes_iter.clone_debug();
    df.field("referenced_nodes", &nodes_iter);
    df.finish()
  }
}

#[derive(Clone)]
struct IterUpdateContextParents<'a> {
  referenced_nodes: Option<&'a ReferencedNodes>,
  index:            usize,
}

impl<'a> Iterator for IterUpdateContextParents<'a> {
  type Item = &'a ArcGlyph;

  fn next(&mut self) -> Option<Self::Item> {
    while let Some(referenced_node) = self.referenced_nodes {
      if let Some(glyph) = referenced_node.nodes.get(self.index) {
        self.index += 1;
        return Some(glyph);
      } else {
        // No more in this parent, look to next one.
        self.referenced_nodes =
          referenced_node.parent.as_ref().map(|a| a.as_ref());
        self.index = 0;
      }
    }
    None
  }
}

/// A container for individual items (keys, values) in a CLiMB Tree, intended
/// for use in an [`UpdateContext`].
///
/// To do this, we must store _either_ a reference to existing data, or possibly
/// entirely new data--either new data coming from the user update, or new
/// data generated as a result of a reducing upsert (e.g., consolidating
/// counters).
///
/// # Safety
///
/// This type is designed to not only to reference data directly in existing
/// [`CLiMBTreeNode`]s, but to be able to do so in a complex tree update
/// context where the lifetimes can't feasibly (at least to the author's
/// knowledge / ability) be expressed through rust's type system.
///
/// At the same time, this type is intended to be used in container types
/// (e.g., [`BTreeMap`]) that expect types to be `Ord`.  Implementing `Ord`
/// requires unsafe operations, but `Ord` itself is not unsafe.  Therefore, to
/// prevent unsafe operation from taking place unexpectedly, we must gate the
/// creation of any instances of `UpdateCell` using pointers behind `unsafe`.
#[derive(Clone)]
pub(super) enum UnsafeUpdateCell<V>
where
  V: CLiMBTreeValue,
{
  // Note this isn't actually 'static, should be treated like a pointer.
  StaticRef(V::RefType<'static>),
  Owned(V),
}

impl<V: CLiMBTreeValue> Debug for UnsafeUpdateCell<V>
where
  for<'a> V::RefType<'a>: Debug,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    unsafe { Debug::fmt(&self.as_ref(), f) }
  }
}

impl<V> UnsafeUpdateCell<V>
where
  V: CLiMBTreeValue,
{
  /// Creates a new `UpdateCell` from an existing reference to `V::RefType`.
  ///
  /// Safety: Users creating an UpdateCell from references must ensure that
  ///         the referenced data remains valid and pinned for the life of the
  ///         `UpdateCell`, as the comparison `impls` such as `Ord` will
  ///         dereference
  pub(crate) unsafe fn from_ref(from: V::RefType<'_>) -> Self {
    Self::StaticRef(transmute::<_, _>(from))
  }

  /// Creates a new `UpdateCell` from a new value.
  fn from_val(from: V) -> Self {
    Self::Owned(from)
  }

  /// Returns a reference to the contained value.
  ///
  /// Safety: Callers must ensure that the pointer contained is valid.
  unsafe fn as_ref<'a>(&'a self) -> V::RefType<'a> {
    match self {
      UnsafeUpdateCell::StaticRef(ptr) => transmute::<_, _>(*ptr),
      UnsafeUpdateCell::Owned(owned) => V::as_ref(owned),
    }
  }
}

impl<V: CLiMBTreeValue> From<V> for UnsafeUpdateCell<V> {
  fn from(value: V) -> Self {
    Self::Owned(value)
  }
}

impl<K> PartialOrd for UnsafeUpdateCell<K>
where
  K: CLiMBTreeKey,
{
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<K> Eq for UnsafeUpdateCell<K> where K: CLiMBTreeKey {}

impl<K> PartialEq for UnsafeUpdateCell<K>
where
  K: CLiMBTreeKey,
{
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<K> Ord for UnsafeUpdateCell<K>
where
  K: CLiMBTreeKey,
{
  fn cmp(&self, other: &Self) -> Ordering {
    unsafe { K::climb_tree_ord(self.as_ref(), other.as_ref()) }
  }
}

/// Tracks the nodes referenced by an [`UpdateSet`].
///
/// A ReferencedNodes instance will typically be organized in a tree-like
/// configuration, as an `UpdateSet` will contain pointers to entries in both
/// (1) the old nodes being updated and replaced and (2) nodes closer to the
/// root of the tree.
///
/// This is accomplished with a vector of `Arc` references to nodes from (1)
/// and another `Arc` reference to a parent `ReferencedNodes` for (2).
#[derive(Clone)]
struct ReferencedNodes {
  parent: Option<Arc<ReferencedNodes>>,
  nodes:  SmallVec<ArcGlyph, 4>,
}

impl ReferencedNodes {
  pub fn new() -> Self {
    Self {
      parent: None,
      nodes:  Default::default(),
    }
  }
}

impl ReferencedNodes {
  pub fn add_node(&mut self, glyph: ArcGlyph) {
    self.nodes.push(glyph);
  }

  pub fn finalize(self) -> Arc<Self> {
    Arc::new(self)
  }

  pub fn new_child(self: &Arc<Self>) -> Self {
    Self {
      parent: Some(self.clone()),
      nodes:  Default::default(),
    }
  }
}

#[cfg(test)]
pub(crate) mod tests {
  use super::*;
  use crate::{glyph_new_arc, zerocopy::I64};
  use core::ops::Range;

  /// For use in tests below.
  pub(crate) fn gen_test_climb_tree_update_context(
    tombstones: Range<i64>,
    entries: Range<i64>,
  ) -> (UpdateContext<I64, I64>, (usize, usize)) {
    let mut ctx = UpdateContext::new();
    let mut expected_tombtones_len = 0;
    let mut expected_entries_len = 0;
    for i in tombstones {
      ctx.add_newer_tombstone_owned(i);
      expected_tombtones_len += size_of::<I64>();
    }
    for i in entries {
      ctx.add_newer_entry_owned(i, i);
      expected_entries_len += size_of::<I64>() * 2;
    }
    (ctx, (expected_tombtones_len, expected_entries_len))
  }

  #[test]
  fn update_context() {
    update_context_lengths();
    update_context_key_splits();
    update_context_length_splits();
    update_context_codec();
  }

  /// Tests how updates change length.
  fn update_context_lengths() {
    //== Test with fixed length data ==//
    let (mut ctx, mut expected_lens) =
      gen_test_climb_tree_update_context(-10..0, 0..10);
    assert_eq!(ctx.get_encode_length(), expected_lens);

    // Duplicating a tombstone shouldn't change anything, older or newer.
    ctx.add_newer_tombstone_owned(-1);
    assert_eq!(ctx.get_encode_length(), expected_lens);
    ctx.add_older_tombstone_owned(-1);
    assert_eq!(ctx.get_encode_length(), expected_lens);

    // Duplicating an entry shouldn't change anything, newer or older.
    ctx.add_newer_entry_owned(1, 1);
    assert_eq!(ctx.get_encode_length(), expected_lens);
    ctx.add_older_entry_owned(1, 1);
    assert_eq!(ctx.get_encode_length(), expected_lens);

    // Adding an older entry under an existing tombstone shouldn't change length.
    ctx.add_older_entry_owned(-1, -1);
    assert_eq!(ctx.get_encode_length(), expected_lens);

    // However, adding a newer one should.
    ctx.add_newer_entry_owned(-1, -1);
    expected_lens.1 += size_of::<I64>() * 2;
    assert_eq!(ctx.get_encode_length(), expected_lens);

    // And adding a newer tombstone should reduce it again.  The old tombstone
    // is already there, but the new tombstone should remove the entry
    ctx.add_newer_tombstone_owned(-1);
    expected_lens.1 -= size_of::<I64>() * 2;
    assert_eq!(ctx.get_encode_length(), expected_lens);
  }

  /// Tests split functionality
  fn update_context_key_splits() {
    // Get a test context, but let's arbitrarily add a referenced glyph.
    let (mut ctx, expected_len) =
      gen_test_climb_tree_update_context(-10..0, 0..10);
    assert_eq!(ctx.get_encode_length(), expected_len);
    let ag = glyph_new_arc(()).unwrap();
    ctx.keep_reference(ag);
    std::dbg!(&ctx);

    // Splitting at key zero should result in all tombstones in the first one
    // and all entries in the second, with equal lengths.  However, the key
    // length will be unknown until we count them again.
    let ts = ctx.split_at_key(&I64::from(0), None);
    std::dbg!(&ts);
    std::dbg!(&ctx);
    assert_eq!(ctx.referenced_glyphs().count(), 1);
    assert_eq!(ts.referenced_glyphs().count(), 1);
    assert_eq!(ts.num_tombstones(), 10);
    assert_eq!(ts.num_entries(), 0);
    assert_eq!(ctx.num_tombstones(), 0);
    assert_eq!(ctx.num_entries(), 10);

    assert!(ts.known_enc_length.is_none());
    assert!(ctx.known_enc_length.is_none());
    // let (ts_tomb_len, ts_entry_len) = ts.get_encode_length();
    // assert_eq!(ts.get_encode_length(), size_of::<I64>() * 10);
    // assert_eq!(ctx.get_encode_length(), size_of::<I64>() * 20);
  }

  fn update_context_length_splits() {
    // Get a test context, but let's arbitrarily add a referenced glyph.
    let (mut ctx, _expected_len) =
      gen_test_climb_tree_update_context(-10..5, 0..10);
    // std::dbg!(&ctx);
    // std::dbg!(ctx.num_tombstones(), ctx.num_entries());

    let mut lower = ctx.split_at_enc_bytes(size_of::<I64>() * 15).unwrap();
    assert_eq!(lower.get_encode_length().0, 88);
    assert_eq!(lower.get_encode_length().1, 16);
    assert_eq!(*lower.first_key().unwrap(), -10);
    assert_eq!(*lower.last_key().unwrap(), 0);
    assert_eq!(*ctx.first_key().unwrap(), 1);
    assert_eq!(*ctx.last_key().unwrap(), 9);
  }

  fn update_context_codec() {
    let (_ctx, _ctx_len) = gen_test_climb_tree_update_context(0..10, 10..20);
    // let writer = UpdateContextLeafWriter::new(&ctx);
    // let leaf = glyph_new_arc(writer).unwrap();
    // let decoded = CLiMBTreeNodeGlyph::<_, I64, I64>::from_glyph(leaf).unwrap();
    // std::dbg!(&decoded);
    todo!("FIXME")
  }
}
