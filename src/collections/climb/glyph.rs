use crate::{
  collections::climb::{CLiMBTreeKey, CLiMBTreeTypeID, CLiMBTreeValue},
  crypto::GlyphHash,
  util::{
    debug::{CloneDebugIterator, SimpleMapDebug},
    BloomFilter, BloomFilterOccupancy,
  },
  zerocopy::{round_to_word, ZeroCopy, U16, U32},
  ArcGlyph, FromGlyph, Glyph, GlyphErr, GlyphOffset, GlyphType,
};
use core::{
  fmt::{Debug, Formatter},
  marker::PhantomData,
  ptr::NonNull,
};

#[derive(Copy, Clone)]
#[repr(packed)]
pub(super) struct CLiMBTreeNodeHeader {
  /// An incrementing version number, currently 0=experimental.
  version:        u8,
  /// The number of node-level links to SS Tables.
  num_ss_tables:  u8,
  /// The data type of the key; see [`TypeID`].
  key_type:       U16,
  /// The data type of the value; see [`TypeID`].
  value_type:     U16,
  /// The number of pivot keys in the node.
  num_pivots:     U16,
  /// The number of deletes in the node.
  num_tombstones: U32,
  /// The number of entries in the node.
  num_entries:    U32,
}

unsafe impl ZeroCopy for CLiMBTreeNodeHeader {}

impl CLiMBTreeNodeHeader {
  pub(super) fn new<K: CLiMBTreeKey, V: CLiMBTreeValue>(
    num_children: usize,
    num_ss_tables: usize,
    num_tombstones: usize,
    num_entries: usize,
  ) -> Result<Self, GlyphErr> {
    let key_type = U16::from(K::TYPE_ID as u16);
    let value_type = U16::from(V::TYPE_ID as u16);
    let num_pivots = U16::try_from(num_children)
      .map_err(|_| GlyphErr::CLiMBTreeNumPivotsOverflow(num_children))?;
    let num_ss_tables = u8::try_from(num_ss_tables)
      .map_err(|_| GlyphErr::CLiMBTreeNumSSLinksOverflow(num_ss_tables))?;

    let num_tombstones = U32::try_from(num_tombstones).map_err(|_| {
      GlyphErr::CLiMBTreeNodeNumTombstoneOverflow(num_tombstones)
    })?;
    let num_entries = U32::try_from(num_entries)
      .map_err(|_| GlyphErr::CLiMBTreeNumEntriesOverflow(num_entries))?;
    Ok(Self {
      version: 0,
      num_ss_tables,
      key_type,
      value_type,
      num_pivots,
      num_tombstones,
      num_entries,
    })
  }

  fn key_type(&self) -> CLiMBTreeTypeID {
    CLiMBTreeTypeID::from(self.key_type)
  }

  fn value_type(&self) -> CLiMBTreeTypeID {
    CLiMBTreeTypeID::from(self.value_type)
  }

  fn num_pivots(&self) -> usize {
    self.num_pivots.get() as usize
  }

  fn num_ss_tables(&self) -> usize {
    self.num_ss_tables as usize
  }

  fn num_tombstones(&self) -> usize {
    self.num_tombstones.get() as usize
  }

  fn num_entries(&self) -> usize {
    self.num_entries.get() as usize
  }
}

/// A Node in a CLiMB Tree.
///
/// # Binary Format
///
/// ## Overall
///
/// - An 8-byte [`GlyphHeader`].
/// - A 16-byte `CLiMBTreeNodeHeader`.  Its format is as follows:
///   - A version byte.
///   - A byte describing the number of node-level links to SSTables.
///   - A [`U16`] describing the key type.  See [`CLiMBTreeTypeID`].
///   - A [`U16`] describing the value type.  See [`CLiMBTreeTypeID`].
///   - A [`U16`] describing the number of pivots in the node.
///   - A [`U32`] describing the number of tombstones in the node.
///   - A [`U32`] describing the number of entries in the node.
/// - An offsets section
///   - An array of [`GlyphOffset`]s for each pivot
///   - An array of [`GlyphOffset`]s for each node-level SSTable link.
///   - If the key type is of variable length, an array of [`GlyphOffset`]s for each tombstone.
///   - If the key OR value types are of variable length, an array of [`GlyphOffset`]s for each
///     entry.
///   - Zero padding to the nearest 8-byte boundary.
/// - A fixed-length data section
///   - If the key type is of fixed length, an array of keys.
///   - If the key type AND value type are of fixed length, an array of entries.
/// - A data section containing Contains pivot data and links to SSTables, as well as keys and
///   entries when not present in the fixed-length data section.  These can be present in any order,
///   though their position must match the offsets for each specified in the offsets section.  The
///   specific format of each of these objects is detailed below.
///
/// ## Pivot Information
///
/// - An instance of the key type, describing the lowest key in nodes linked under this pivot.
/// - A byte for bitflags.
/// - A byte for the number of SSTable links present in the pivot information.
/// - Two bytes of reserved zero-padding.
/// - If the least significant bit of the bitflags byte is set (`FLAG_HAS_CHILD`), then a 32-byte
///   cryptographic hash of the child node.
/// - An array of [`GlyphOffset`]s, one for each SSTable link present in the pivot information.
/// - Zero padding to the nearest 8-byte boundary
///
/// ## SSTable Link Information
///
/// - A 32-byte cryptographic hash of the target SSTable Node
/// - A [`U32`] describing the length of that node, in multiples of 8 bytes.
/// - A [`U16`] describing the length of a bloom filter, in multiples of 8 bytes.
/// - A [`U16`] containing the number of hash keys that were used in creating the bloom filter
/// - An array of bytes containing the bloom filter (with length described above).
///
pub struct CLiMBTreeNodeGlyph<G, K, V>
where
  G: Glyph,
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  glyph: G,

  /// A pointer to the node's type-specific header.
  header: NonNull<CLiMBTreeNodeHeader>,

  /// An array containing the offsets in the glyph for data on each pivot.
  pivot_offsets: NonNull<[GlyphOffset]>,

  /// An array containing the offsets in the glyph for each link to a SSTable Node.
  ss_table_offsets: NonNull<[GlyphOffset]>,

  /// If keys are a fixed length, the start of the tombstones array. Otherwise,
  /// the start of the offsets table for tombstones.
  tombstones_offset: GlyphOffset,

  /// If keys AND values are a fixed length, the start of the entries array.
  /// Otherwise, the start of the offsets table for pivots.
  entries_offset: GlyphOffset,
  _phantom:       PhantomData<(K, V)>,
}

unsafe impl<G, K, V> Send for CLiMBTreeNodeGlyph<G, K, V>
where
  G: Glyph,
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
}

impl<G, K, V> CLiMBTreeNodeGlyph<G, K, V>
where
  G: Glyph,
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  fn header(&self) -> &CLiMBTreeNodeHeader {
    unsafe { self.header.as_ref() }
  }

  /// The number of child nodes
  pub fn num_pivots(&self) -> usize {
    self.header().num_pivots()
  }

  pub fn num_ss_tables(&self) -> usize {
    self.header().num_ss_tables()
  }

  /// The number of tombstone keys present in the node.
  pub fn num_tombstones(&self) -> usize {
    self.header().num_tombstones()
  }

  /// The number of key/value pairs present in the node.
  pub fn num_entries(&self) -> usize {
    self.header().num_entries()
  }

  /// The length of the underlying glyph.
  pub fn glyph_len(&self) -> usize {
    self.glyph.len()
  }

  fn pivot_offsets(&self) -> &[GlyphOffset] {
    unsafe { self.pivot_offsets.as_ref() }
  }

  /// Retrieves the pivot at the specified index.
  ///
  /// # Arguments
  ///
  /// * `index` - The index of the pivot to be retrieved.
  ///
  /// # Returns
  ///
  /// If successful, a tuple containing the pivot's lower bound (if applicable),
  /// upper bound (if applicable), and the hash of the child node.
  ///
  /// # Errors
  ///
  /// - A `GlyphErr::OutOfBounds` error if the specified index is greater than
  ///   the number of pivots in the node.
  /// - Various errors caused by a malformed node (e.g., failed bounds checks).
  pub fn get_pivot(&self, index: usize) -> Result<PivotInfo<'_, K>, GlyphErr> {
    let offset =
      self
        .pivot_offsets()
        .get(index)
        .ok_or(GlyphErr::OutOfBounds {
          index,
          length: self.header().num_pivots(),
        })?;
    let content = self.glyph.content_padded();
    let mut cursor = offset.cursor(0);

    let lower_bound = K::read(content, &mut cursor)?;
    // Upper bound is only available if there's a next pivot.
    let upper_bound = match self.pivot_offsets().get(index + 1) {
      None => None,
      Some(offset) => {
        let mut ub_cursor = offset.cursor(0);
        Some(K::read(content, &mut ub_cursor)?)
      },
    };

    let rpi = RawPivotInfo::bbrf(content, &mut cursor)?;
    let child_hash = if rpi.has_child() {
      Some(GlyphHash::bbrf(content, &mut cursor)?)
    } else {
      None
    };
    let ss_table_offsets =
      GlyphOffset::bbrfs(content, &mut cursor, rpi.num_ss_tables())?;

    Ok(PivotInfo {
      lower_bound,
      upper_bound,
      child_hash,
      ss_table_offsets,
      glyph_content: content,
    })
  }

  pub fn iter_pivots(
    &self,
  ) -> impl Iterator<Item = PivotInfo<'_, K>> + Clone + ExactSizeIterator {
    IterPivots::<G, K, V> {
      glyph: self,
      index: 0,
    }
  }

  fn ss_table_offsets(&self) -> &[GlyphOffset] {
    unsafe { self.ss_table_offsets.as_ref() }
  }

  /// Retrieves the SSTable at the specified index.
  ///
  /// # Arguments
  ///
  /// * `index` - The index of the SSTable to be retrieved.
  ///
  /// # Returns
  ///
  /// If successful, a [`SSTableInfo`] describing the linked SSTable.
  ///
  /// # Errors
  ///
  /// - A `GlyphErr::OutOfBounds` error if the specified index is greater than
  ///   the number of SSTables in the node.
  /// - Various errors caused by a malformed node (e.g., failed bounds checks).
  pub fn get_ss_table(&self, index: usize) -> Result<SSTableInfo, GlyphErr> {
    let offset =
      self
        .ss_table_offsets()
        .get(index)
        .ok_or(GlyphErr::OutOfBounds {
          index,
          length: self.ss_table_offsets.len(),
        })?;

    let mut cursor = offset.cursor(0);
    let raw = RawSSTableInfo::bbrf(self.glyph.content_padded(), &mut cursor)?;
    let bloom_data =
      u8::bbrfs(self.glyph.content_padded(), &mut cursor, raw.bloom_length())?;
    Ok(SSTableInfo { raw, bloom_data })
  }

  pub fn iter_ss_tables(
    &self,
  ) -> impl Iterator<Item = SSTableInfo> + Clone + ExactSizeIterator {
    IterSSTables {
      glyph_content: self.glyph.content_padded(),
      offsets:       self.ss_table_offsets(),
    }
  }

  /// Retrieves the tombstone at the specified index.
  ///
  /// # Arguments
  ///
  /// * `index` - The index of the pivot to be retrieved.
  ///
  /// # Returns
  ///
  /// If successful, a tuple containing the pivot's lower bound (if applicable),
  /// upper bound (if applicable), and the hash of the child node.
  ///
  /// # Errors
  ///
  /// - A `GlyphErr::OutOfBounds` error if the specified index is greater than
  ///   the number of pivots in the node.
  /// - Various errors caused by a malformed node (e.g., failed bounds checks).
  pub fn get_tombstone(
    &self,
    index: usize,
  ) -> Result<K::RefType<'_>, GlyphErr> {
    if index > self.header().num_tombstones() {
      Err(GlyphErr::OutOfBounds {
        index,
        length: self.header().num_tombstones(),
      })
    } else {
      let content = self.glyph.content();
      if let Some(key_len) = K::FIXED_LEN {
        // Pull from data area
        let relative_pos = index * key_len;
        let mut cursor = self.tombstones_offset.cursor(0) + relative_pos;
        let tombstone = K::read(content, &mut cursor)?;
        Ok(tombstone)
      } else {
        // Pull from offset
        let rel_offset_pos = size_of::<GlyphOffset>() * index;
        let mut offset_cursor =
          self.tombstones_offset.cursor(0) + rel_offset_pos;
        let offset = GlyphOffset::bbrf(content, &mut offset_cursor)?;
        let mut cursor = offset.cursor(0);
        let tombstone = K::read(content, &mut cursor)?;
        Ok(tombstone)
      }
    }
  }

  /// Iterates through the node's tombstones.
  ///
  /// Note that errors retrieving a tombstone will result in the iterator
  /// returning a `None` early.
  ///
  // TODO: Consider making these iterators return a `Result` instead, so users
  //       are forced to deal with situations in which not all tombstones can
  //       be read due to error conditions.
  pub fn iter_tombstones(
    &self,
  ) -> impl Iterator<Item = K::RefType<'_>> + Clone + ExactSizeIterator {
    IterTombstones::<K> {
      content:         self.glyph.content_padded(),
      cursor:          self.tombstones_offset.cursor(0),
      tombstones_left: self.num_tombstones(),
      _phantom:        Default::default(),
    }
  }

  pub fn get_entry(
    &self,
    index: usize,
  ) -> Result<(K::RefType<'_>, V::RefType<'_>), GlyphErr> {
    if index > self.header().num_tombstones() {
      Err(GlyphErr::OutOfBounds {
        index,
        length: self.header().num_tombstones(),
      })
    } else {
      let content = self.glyph.content();
      if let (Some(key_len), Some(val_len)) = (K::FIXED_LEN, V::FIXED_LEN) {
        // Pull from data area
        let relative_pos = index * (key_len + val_len);
        let mut cursor = self.tombstones_offset.cursor(0) + relative_pos;
        let key = K::read(content, &mut cursor)?;
        let val = V::read(content, &mut cursor)?;
        Ok((key, val))
      } else {
        // Pull from offset
        let rel_offset_pos = size_of::<GlyphOffset>() * index;
        let mut offset_cursor =
          self.tombstones_offset.cursor(0) + rel_offset_pos;
        let offset = GlyphOffset::bbrf(content, &mut offset_cursor)?;
        let mut cursor = offset.cursor(0);
        let key = K::read(content, &mut cursor)?;
        let val = V::read(content, &mut cursor)?;
        Ok((key, val))
      }
    }
  }

  pub fn iter_entries(
    &self,
  ) -> impl Iterator<Item = (K::RefType<'_>, V::RefType<'_>)>
       + Clone
       + ExactSizeIterator {
    IterEntries::<K, V> {
      content:      self.glyph.content_padded(),
      cursor:       self.entries_offset.cursor(0),
      entries_left: self.num_entries(),
      _phantom:     Default::default(),
    }
  }
}

impl<K, V> CLiMBTreeNodeGlyph<ArcGlyph, K, V>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  pub fn clone_arc_inner(&self) -> ArcGlyph {
    self.glyph.clone()
  }
}

impl<G, K, V> FromGlyph<G> for CLiMBTreeNodeGlyph<G, K, V>
where
  G: Glyph,
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::CLiMBTreeNode)?;
    let content = glyph.content();
    let cursor = &mut 0;
    let header = CLiMBTreeNodeHeader::bbrf(content, cursor)?;
    let (pivot_offsets, ss_table_offsets, tombstones_offset, entries_offset) =
      match (K::FIXED_LEN, V::FIXED_LEN) {
        (Some(key_len), Some(_val_len)) => {
          let pivot_offsets =
            GlyphOffset::bbrfs(content, cursor, header.num_pivots())?;
          let ss_table_offsets =
            GlyphOffset::bbrfs(content, cursor, header.num_ss_tables())?;
          *cursor = round_to_word(*cursor);

          // Tombstones and entries both have data areas.
          let tombstones_offset = GlyphOffset::new(0, *cursor)?;
          *cursor += header.num_tombstones() * key_len;
          let entries_offset = GlyphOffset::new(0, *cursor)?;
          (
            pivot_offsets,
            ss_table_offsets,
            tombstones_offset,
            entries_offset,
          )
        },
        (Some(_key_len), None) => {
          let pivot_offsets =
            GlyphOffset::bbrfs(content, cursor, header.num_pivots())?;
          let ss_table_offsets =
            GlyphOffset::bbrfs(content, cursor, header.num_ss_tables())?;
          let entries_offset = GlyphOffset::new(0, *cursor)?;
          *cursor += size_of::<GlyphOffset>() * header.num_entries();
          *cursor = round_to_word(*cursor);

          let tombstones_offset = GlyphOffset::new(0, *cursor)?;
          (
            pivot_offsets,
            ss_table_offsets,
            tombstones_offset,
            entries_offset,
          )
        },
        _ => {
          // Offsets for tombstones, and entries.
          let pivot_offsets =
            GlyphOffset::bbrfs(content, cursor, header.num_pivots())?;
          let ss_table_offsets =
            GlyphOffset::bbrfs(content, cursor, header.num_ss_tables())?;
          let tombstones_offset = GlyphOffset::new(0, *cursor)?;
          *cursor += header.num_tombstones() + size_of::<GlyphOffset>();
          let entries_offset = GlyphOffset::new(0, *cursor)?;
          *cursor += size_of::<GlyphOffset>() * header.num_entries();
          *cursor = round_to_word(*cursor); // Technically not needed b/c never used
          (
            pivot_offsets,
            ss_table_offsets,
            tombstones_offset,
            entries_offset,
          )
        },
      };

    let pivot_offsets = NonNull::from(pivot_offsets);
    let ss_table_offsets = NonNull::from(ss_table_offsets);
    let header = NonNull::from(header);
    Ok(Self {
      glyph,
      header,
      pivot_offsets,
      ss_table_offsets,
      tombstones_offset,
      entries_offset,
      _phantom: Default::default(),
    })
  }
}

impl<G, K, V> Debug for CLiMBTreeNodeGlyph<G, K, V>
where
  G: Glyph,
  K: CLiMBTreeKey + Debug,
  V: CLiMBTreeValue + Debug,
{
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("CLiMBTreeNodeGlyph")
      .field("num_children", &self.num_pivots())
      .field("num_tombstones", &self.num_tombstones())
      .field("num_entries", &self.num_entries())
      .field("children", &self.iter_pivots().clone_debug())
      .field("tombstones", &self.iter_tombstones().clone_debug())
      .field(
        "entries",
        &self
          .iter_entries()
          .map(|(k, v)| SimpleMapDebug(k, v))
          .clone_debug(),
      )
      .finish()
  }
}

#[derive(Copy)]
struct IterPivots<'a, G: Glyph, K: CLiMBTreeKey, V: CLiMBTreeValue> {
  glyph: &'a CLiMBTreeNodeGlyph<G, K, V>,
  index: usize,
}

impl<'a, G: Glyph, K: CLiMBTreeKey, V: CLiMBTreeValue> Clone
  for IterPivots<'a, G, K, V>
{
  fn clone(&self) -> Self {
    Self {
      glyph: self.glyph,
      index: self.index,
    }
  }
}

impl<'a, G: Glyph, K: CLiMBTreeKey, V: CLiMBTreeValue> Iterator
  for IterPivots<'a, G, K, V>
{
  type Item = PivotInfo<'a, K>;

  fn next(&mut self) -> Option<Self::Item> {
    let info = self.glyph.get_pivot(self.index).ok()?;
    self.index += 1;
    Some(info)
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len(), Some(self.len()))
  }
}

impl<'a, G: Glyph, K: CLiMBTreeKey, V: CLiMBTreeValue> ExactSizeIterator
  for IterPivots<'a, G, K, V>
{
  fn len(&self) -> usize {
    self.glyph.num_pivots() - self.index
  }
}

#[derive(Copy, Clone)]
struct IterSSTables<'a> {
  glyph_content: &'a [u8],
  offsets:       &'a [GlyphOffset],
}

impl<'a> Iterator for IterSSTables<'a> {
  type Item = SSTableInfo<'a>;

  fn next(&mut self) -> Option<Self::Item> {
    let (first, remainder) = self.offsets.split_first()?;
    self.offsets = remainder;
    let mut cursor = first.cursor(0);
    let raw = RawSSTableInfo::bbrf(self.glyph_content, &mut cursor).ok()?;
    let bloom_filter = u8::bbrfs(
      self.glyph_content,
      &mut cursor,
      raw.bloom_length.get() as usize * 8,
    )
    .ok()?;
    Some(SSTableInfo {
      raw,
      bloom_data: bloom_filter,
    })
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len(), Some(self.len()))
  }
}

#[derive(Copy, Clone)]
struct IterTombstones<'a, K: CLiMBTreeKey> {
  content:         &'a [u8],
  cursor:          usize,
  tombstones_left: usize,
  _phantom:        PhantomData<fn(&'a [u8]) -> K::RefType<'a>>,
}

impl<'a, K: CLiMBTreeKey> Iterator for IterTombstones<'a, K> {
  type Item = K::RefType<'a>;

  fn next(&mut self) -> Option<Self::Item> {
    if self.tombstones_left == 0 {
      None
    } else {
      self.tombstones_left -= 1;
      if let Some(_key_len) = K::FIXED_LEN {
        // Read directly from buffer
        K::read(self.content, &mut self.cursor).ok()
      } else {
        // Read from offset
        let offset = GlyphOffset::bbrf(self.content, &mut self.cursor).ok()?;
        let mut cursor = offset.cursor(0);
        K::read(self.content, &mut cursor).ok()
      }
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len(), Some(self.len()))
  }
}

impl<'a, K: CLiMBTreeKey> ExactSizeIterator for IterTombstones<'a, K> {
  fn len(&self) -> usize {
    self.tombstones_left
  }
}

#[derive(Copy, Clone)]
struct IterEntries<'a, K: CLiMBTreeKey, V: CLiMBTreeValue> {
  content:      &'a [u8],
  cursor:       usize,
  entries_left: usize,
  _phantom:     PhantomData<fn(&'a [u8]) -> (K::RefType<'a>, V::RefType<'a>)>,
}

impl<'a, K: CLiMBTreeKey, V: CLiMBTreeValue> Iterator
  for IterEntries<'a, K, V>
{
  type Item = (K::RefType<'a>, V::RefType<'a>);

  fn next(&mut self) -> Option<Self::Item> {
    if self.entries_left == 0 {
      None
    } else {
      self.entries_left -= 1;
      if let Some(_key_len) = K::FIXED_LEN {
        // Read directly from buffer
        if let (Ok(key), Ok(value)) = (
          K::read(self.content, &mut self.cursor),
          V::read(self.content, &mut self.cursor),
        ) {
          Some((key, value))
        } else {
          None
        }
      } else {
        // Read from offset
        let offset = GlyphOffset::bbrf(self.content, &mut self.cursor).ok()?;
        let mut cursor = offset.cursor(0);
        if let (Ok(key), Ok(value)) = (
          K::read(self.content, &mut cursor),
          V::read(self.content, &mut cursor),
        ) {
          Some((key, value))
        } else {
          None
        }
      }
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len(), Some(self.len()))
  }
}

impl<'a, K: CLiMBTreeKey, V: CLiMBTreeValue> ExactSizeIterator
  for IterEntries<'a, K, V>
{
  fn len(&self) -> usize {
    self.entries_left
  }
}

#[derive(Copy, Clone)]
#[repr(packed)]
pub(super) struct RawPivotInfo {
  flags:         u8,
  num_ss_tables: u8,
  reserved:      [u8; 2],
}

impl RawPivotInfo {
  const FLAG_HAS_CHILD: u8 = 0b0000_0001;

  pub fn new(has_child: bool, num_ss_tables: usize) -> Result<Self, GlyphErr> {
    let num_ss_tables = u8::try_from(num_ss_tables)
      .map_err(|_| GlyphErr::CLiMBTreeNumSSLinksOverflow(num_ss_tables))?;
    let mut flags = 0;
    if has_child {
      flags |= Self::FLAG_HAS_CHILD;
    }
    Ok(Self {
      flags,
      num_ss_tables,
      reserved: Default::default(),
    })
  }

  pub fn has_child(&self) -> bool {
    self.flags & Self::FLAG_HAS_CHILD != 0
  }

  pub fn num_ss_tables(&self) -> usize {
    self.num_ss_tables as usize
  }
}

unsafe impl ZeroCopy for RawPivotInfo {}

/// Information on a pivot in a [`CLiMBTreeNodeGlyph`].
#[derive(Copy, Clone)]
pub struct PivotInfo<'a, K: CLiMBTreeKey> {
  lower_bound:      K::RefType<'a>,
  upper_bound:      Option<K::RefType<'a>>,
  child_hash:       Option<&'a GlyphHash>,
  ss_table_offsets: &'a [GlyphOffset],
  /// Keep reference to content, so we can read SSTable Links
  glyph_content:    &'a [u8],
}

impl<'a, K: CLiMBTreeKey> PivotInfo<'a, K> {
  pub fn iter_ss_tables(
    &self,
  ) -> impl Iterator<Item = SSTableInfo<'a>> + Clone + ExactSizeIterator {
    IterSSTables {
      glyph_content: self.glyph_content,
      offsets:       self.ss_table_offsets,
    }
  }

  pub fn lower_bound(&self) -> K::RefType<'a> {
    self.lower_bound
  }

  pub fn upper_bound(&self) -> Option<K::RefType<'a>> {
    self.upper_bound
  }

  pub fn child_hash(&self) -> Option<&'a GlyphHash> {
    self.child_hash
  }
}

impl<'a, K: CLiMBTreeKey> Debug for PivotInfo<'a, K> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("PivotInfo");
    df.field("lower_bound", &self.lower_bound());
    if let Some(upper_bound) = self.upper_bound() {
      df.field("upper_bound", &upper_bound);
    }
    if let Some(child_hash) = self.child_hash() {
      df.field("child_hash", &child_hash);
    }
    df.field("ss_table_links", &self.iter_ss_tables().clone_debug());
    df.finish()
  }
}

impl<'a> ExactSizeIterator for IterSSTables<'a> {
  fn len(&self) -> usize {
    self.offsets.len()
  }
}

/// The raw [`ZeroCopy`] type for SSTable data in [`CLiMBTreeNodeGlyph`]s.
#[derive(Copy, Clone)]
pub(super) struct RawSSTableInfo {
  /// The hash of the target SSTable
  target_hash:   GlyphHash,
  /// The length of the target SSTable Node, in multiples of 8 bytes
  target_length: U32,
  /// The length of the (following) bloom filter, in multiples of 8 bytes
  bloom_length:  U16,
  /// The number of hash keys that were used in creating the bloom filter
  bloom_k:       U16,
}

impl RawSSTableInfo {
  pub(super) fn new(
    target_hash: GlyphHash,
    target_length: usize,
    bloom_length: usize,
    bloom_k: usize,
  ) -> Result<Self, GlyphErr> {
    let target_length =
      if target_length <= u32::MAX as usize * 8 && target_length % 8 == 0 {
        Ok(U32::from((target_length / 8) as u32))
      } else {
        Err(GlyphErr::GlyphLenOverflow(target_length))
      }?;

    let bloom_length =
      if bloom_length <= u16::MAX as usize * 8 && bloom_length % 8 == 0 {
        Ok(U16::from((bloom_length / 8) as u16))
      } else {
        Err(GlyphErr::CLiMBTreeIllegalBloomLen(bloom_length))
      }?;

    let bloom_k = if bloom_k <= u16::MAX as usize {
      Ok(U16::from(bloom_k as u16))
    } else {
      Err(GlyphErr::CLiMBTreeIllegalBloomK(bloom_k))
    }?;

    Ok(Self {
      target_hash,
      target_length,
      bloom_length,
      bloom_k,
    })
  }

  /// The cryptographic hash of the target
  pub fn target_hash(&self) -> &GlyphHash {
    &self.target_hash
  }

  pub fn target_length(&self) -> usize {
    self.target_length.get() as usize * 8
  }

  pub fn bloom_length(&self) -> usize {
    self.bloom_length.get() as usize * 8
  }

  pub fn bloom_k(&self) -> usize {
    self.bloom_k.get() as usize
  }
}

unsafe impl ZeroCopy for RawSSTableInfo {}

pub struct SSTableInfo<'a> {
  raw:        &'a RawSSTableInfo,
  bloom_data: &'a [u8],
}

impl<'a> SSTableInfo<'a> {
  pub fn target_hash(&self) -> &GlyphHash {
    self.raw.target_hash()
  }

  pub fn target_length(&self) -> usize {
    self.raw.target_length()
  }

  pub fn bloom_length(&self) -> usize {
    self.raw.bloom_length()
  }

  pub fn bloom_k(&self) -> usize {
    self.raw.bloom_k()
  }

  pub fn bloom_data(&self) -> &'a [u8] {
    &self.bloom_data
  }

  pub fn bloom_filter(&self) -> BloomFilter<&[u8]> {
    BloomFilter::new(self.bloom_data(), self.bloom_k())
  }
}

impl<'a> Debug for SSTableInfo<'a> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("SSTableInfo");
    df.field("target_hash", &self.raw.target_hash());
    df.field("target_length", &self.raw.target_length());
    df.field("bloom_length", &self.raw.bloom_length());
    df.field("bloom_k", &self.raw.bloom_k());
    df.field(
      "bloom_occupancy",
      &BloomFilterOccupancy::new(self.bloom_data()),
    );
    df.finish()
  }
}
