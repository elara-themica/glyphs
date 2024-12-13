use crate::{
  collections::climb::{
    glyph::{CLiMBTreeNodeHeader, RawPivotInfo, RawSSTableInfo},
    CLiMBTreeKey, CLiMBTreeNodeGlyph, CLiMBTreeValue,
  },
  crypto::GlyphHash,
  glyph::glyph_close,
  util::BloomFilter,
  zerocopy::{round_to_word, ZeroCopy, U16, U32},
  ArcGlyph, GlyphErr, GlyphHeader, GlyphOffset, GlyphType, ToGlyph,
};
use core::marker::PhantomData;

/// Structure used for writing a [`CLiMBTreeNodeGlyph`].  
///
/// Users of the library need to use something that implements [`ToGlyph`] instead, e.g.,
/// [`CLiMBTreeNodeIterWriter`], which will then use this type themselves.  This type provides no
/// error-checking or protection from errors--e.g., if you call `write_tombstone()` more times than
/// the number of tombstones specified in the constructor, you'll start overwriting the section used
/// to store entries (or entry offsets, depending on whether types are fixed length...).  Nor does
/// it calculate in advance the size of the glyph.
pub(super) struct CLiMBTreeNodeWriter<'a, K, V> {
  /// The buffer the node glyph will be written into
  target:                  &'a mut [u8],
  /// The position in the buffer at which the glyph starts (needed to calculate offsets).
  content_offset:          usize,
  /// The offset at which the pivot offsets will be written.
  pivot_offsets_cursor:    usize,
  /// The offset at which the cache link offsets will be written
  ss_table_offsets_cursor: usize,
  /// The offset at which the tombstone offsets or keys will be written.
  tombstones_cursor:       usize,
  /// The offset at which the entry offsets or keys will be written.
  entries_cursor:          usize,
  /// The offset at which any variable-length data (if any) will be written.
  glyph_cursor:            &'a mut usize,
  _phantom:                PhantomData<(K, V)>,
}

impl<'a, K, V> CLiMBTreeNodeWriter<'a, K, V>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  /// Initializes the writer.
  ///
  /// Parameters:
  /// - `target`: The buffer into which the glyph will be written
  /// - `cursor`: The index at which the glyph will start
  /// - `num_pivots`:  The number of pivots that will be written to the node.  This must match
  ///   the number of times `start_pivot()` is called exactly.
  /// - `num_ss_tables`:  The number of node-level links to SS Tables that will be written to the
  ///   node.  This must match the number of times `write_ss_link()` is called exactly.
  /// - `num_tombstones`:  The number of tombstones that will be written to this node.  This must
  ///   match the number of times `write_tombstone()` will be called exactly.
  /// - `num_entries`:  The number of entries that will be written to this node. This must match
  ///   the number of times `write_entry()` will be called exactly.
  pub fn new(
    target: &'a mut [u8],
    cursor: &'a mut usize,
    num_pivots: usize,
    num_ss_tables: usize,
    num_tombstones: usize,
    num_entries: usize,
  ) -> Result<Self, GlyphErr> {
    let _glyph_offset = GlyphHeader::skip(cursor);
    let content_offset = *cursor;
    CLiMBTreeNodeHeader::new::<K, V>(
      num_pivots,
      num_ss_tables,
      num_tombstones,
      num_entries,
    )?
    .bbwr(target, cursor)?;

    let (
      pivot_offsets_cursor,
      ss_table_offsets_cursor,
      tombstones_cursor,
      entries_cursor,
    ) = match (K::FIXED_LEN, V::FIXED_LEN) {
      (Some(key_len), Some(val_len)) => {
        // pivots at offsets, tombstones buffer, entries buffer
        let pivot_offsets_cursor =
          GlyphOffset::skip(target, cursor, num_pivots, false)?;
        let ss_table_offsets_cursor =
          GlyphOffset::skip(target, cursor, num_ss_tables, true)?;
        debug_assert_eq!(*cursor % 8, 0);
        let tombstones_cursor = *cursor;
        *cursor += num_tombstones * key_len;
        debug_assert_eq!(*cursor % 8, 0);
        let entries_cursor = *cursor;
        *cursor += num_entries * (key_len + val_len);
        debug_assert_eq!(*cursor % 8, 0);
        (
          pivot_offsets_cursor,
          ss_table_offsets_cursor,
          tombstones_cursor,
          entries_cursor,
        )
      },
      (Some(key_len), None) => {
        // pivots at offsets, entries at offsets, tombstones buffer
        let pivot_offsets_cursor =
          GlyphOffset::skip(target, cursor, num_pivots, false)?;
        let ss_table_offsets_cursor =
          GlyphOffset::skip(target, cursor, num_ss_tables, false)?;
        let entries_cursor =
          GlyphOffset::skip(target, cursor, num_entries, true)?;
        debug_assert_eq!(*cursor % 8, 0);

        let tombstones_cursor = *cursor;
        *cursor += num_tombstones * key_len;
        debug_assert_eq!(*cursor % 8, 0);
        (
          pivot_offsets_cursor,
          ss_table_offsets_cursor,
          tombstones_cursor,
          entries_cursor,
        )
      },
      _ => {
        // Everything at offsets
        let pivot_offsets_cursor =
          GlyphOffset::skip(target, cursor, num_pivots, false)?;
        let ss_table_offsets_cursor =
          GlyphOffset::skip(target, cursor, num_ss_tables, false)?;
        let tombstones_cursor =
          GlyphOffset::skip(target, cursor, num_pivots, false)?;
        let entries_cursor =
          GlyphOffset::skip(target, cursor, num_pivots, true)?;
        debug_assert_eq!(*cursor % 8, 0);
        (
          pivot_offsets_cursor,
          ss_table_offsets_cursor,
          tombstones_cursor,
          entries_cursor,
        )
      },
    };

    Ok(Self {
      target,
      content_offset,
      pivot_offsets_cursor,
      ss_table_offsets_cursor,
      tombstones_cursor,
      entries_cursor,
      glyph_cursor: cursor,
      _phantom: Default::default(),
    })
  }

  pub fn start_pivot(
    &mut self,
    lower_bound: K::RefType<'_>,
    child_target_hash: Option<&'_ GlyphHash>,
    num_ss_tables: usize,
  ) -> Result<PivotWriter<K>, GlyphErr> {
    // Write offset to this pivot, let the pivot writer take care of writing
    // everything AT that offset.
    let offset = GlyphOffset::new(self.content_offset, *self.glyph_cursor)?;
    offset.bbwr(self.target, &mut self.pivot_offsets_cursor)?;
    let pw = PivotWriter::<K>::new(
      self.target,
      self.glyph_cursor,
      self.content_offset,
      lower_bound,
      child_target_hash,
      num_ss_tables,
    )?;
    Ok(pw)
  }

  pub fn write_ss_table(
    &mut self,
    target_hash: &GlyphHash,
    target_len: usize,
    bloom_k: usize,
    bloom_data: &[u8],
  ) -> Result<(), GlyphErr> {
    if bloom_data.len() % 8 != 0 || bloom_data.len() > u16::MAX as usize * 8 {
      Err(GlyphErr::CLiMBTreeIllegalBloomLen(bloom_data.len()))
    } else if bloom_k > u16::MAX as usize {
      Err(GlyphErr::CLiMBTreeIllegalBloomK(bloom_k))
    } else {
      let offset = GlyphOffset::new(self.content_offset, *self.glyph_cursor)?;
      offset.bbwr(self.target, &mut self.ss_table_offsets_cursor)?;
      target_hash.bbwr(self.target, self.glyph_cursor)?;
      U32::from((target_len / 8) as u32)
        .bbwr(self.target, self.glyph_cursor)?;
      U16::from((bloom_data.len() / 8) as u16)
        .bbwr(self.target, self.glyph_cursor)?;
      U16::from(bloom_k as u16).bbwr(self.target, self.glyph_cursor)?;
      u8::bbwrs(bloom_data, self.target, self.glyph_cursor)?;
      Ok(())
    }
  }

  pub fn write_tombstone(
    &mut self,
    tombstone: K::RefType<'_>,
  ) -> Result<(), GlyphErr> {
    if let Some(_key_len) = K::FIXED_LEN {
      // Write to tombstones area
      K::write(tombstone, self.target, &mut self.tombstones_cursor)
    } else {
      // Write via an offset
      let offset = GlyphOffset::new(self.content_offset, *self.glyph_cursor)?;
      offset.bbwr(self.target, &mut self.tombstones_cursor)?;
      K::write(tombstone, self.target, self.glyph_cursor)
    }
  }

  pub fn write_entry(
    &mut self,
    key: K::RefType<'_>,
    value: V::RefType<'_>,
  ) -> Result<(), GlyphErr> {
    if let (Some(_key_len), Some(_val_len)) = (K::FIXED_LEN, V::FIXED_LEN) {
      // Write to entries area
      K::write(key, self.target, &mut self.entries_cursor)?;
      V::write(value, self.target, &mut self.entries_cursor)
    } else {
      // Write via an offset
      let offset = GlyphOffset::new(self.content_offset, *self.glyph_cursor)?;
      offset.bbwr(self.target, &mut self.entries_cursor)?;
      K::write(key, self.target, self.glyph_cursor)?;
      V::write(value, self.target, self.glyph_cursor)
    }
  }

  pub fn finish(self) -> Result<(), GlyphErr> {
    let glyph_offset = self.content_offset - size_of::<GlyphHeader>();
    glyph_close(
      GlyphType::CLiMBTreeNode,
      self.target,
      glyph_offset,
      self.glyph_cursor,
      false,
    )?;
    debug_assert_eq!(*self.glyph_cursor % 8, 0);
    Ok(())
  }
}

pub struct PivotWriter<'a, K> {
  target:                  &'a mut [u8],
  cursor:                  &'a mut usize,
  content_offset:          usize,
  ss_table_offsets_cursor: usize,
  _phantom:                PhantomData<K>,
}

impl<'a, K> PivotWriter<'a, K>
where
  K: CLiMBTreeKey,
{
  pub fn new(
    target: &'a mut [u8],
    cursor: &'a mut usize,
    content_offset: usize,
    lower_bound: K::RefType<'_>,
    child_target_hash: Option<&GlyphHash>,
    num_ss_tables: usize,
  ) -> Result<PivotWriter<'a, K>, GlyphErr> {
    // Write pivot info header after the key
    K::write(lower_bound, target, cursor)?;
    let rpi = RawPivotInfo::new(child_target_hash.is_some(), num_ss_tables)?;
    rpi.bbwr(target, cursor)?;
    if let Some(hash) = child_target_hash {
      hash.bbwr(target, cursor)?;
    }
    let ss_table_offsets_cursor =
      GlyphOffset::skip(target, cursor, num_ss_tables, true)?;

    Ok(Self {
      target,
      ss_table_offsets_cursor,
      content_offset,
      cursor,
      _phantom: Default::default(),
    })
  }

  pub fn write_ss_table(
    &mut self,
    target_hash: &GlyphHash,
    target_length: usize,
    bloom_filter: &BloomFilter<&[u8]>,
  ) -> Result<(), GlyphErr> {
    let bloom_len = bloom_filter.data().len();
    if bloom_len % 8 != 0 {
      Err(GlyphErr::CLiMBTreeIllegalBloomLen(bloom_len))
    } else {
      U16::try_from(bloom_len)
        .map_err(|_| GlyphErr::CLiMBTreeIllegalBloomLen(bloom_len))
    }?;

    // Write the pivot's offset to this SSTable.
    let offset = GlyphOffset::new(self.content_offset, *self.cursor)?;
    offset.bbwr(self.target, &mut self.ss_table_offsets_cursor)?;

    // Write the raw info and the bloom filter.
    let raw = RawSSTableInfo::new(
      *target_hash,
      target_length,
      bloom_len,
      bloom_filter.num_hashes(),
    )?;
    raw.bbwr(self.target, self.cursor)?;
    u8::bbwrs(bloom_filter.data(), self.target, self.cursor)
  }

  pub fn finish(self) {
    // LATER: Currently does nothing; could add optional debug tracking/assertions?
  }
}

#[derive(Copy, Clone, Debug)]
pub struct CLiMBTreeNodeLenCalc<K, V> {
  len:         usize,
  num_offsets: usize,
  _phantom:    PhantomData<(K, V)>,
}

impl<K, V> CLiMBTreeNodeLenCalc<K, V>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  pub fn new() -> Self {
    Self {
      len:         0,
      num_offsets: 0,
      _phantom:    Default::default(),
    }
  }

  /// Returns a pivot length calculation object.
  pub fn add_pivot(
    &mut self,
    lower_bound_len: usize,
    has_child: bool,
  ) -> PivotLenCalc<K, V> {
    // Glyph-level offset to the pivot
    self.num_offsets += 1;
    PivotLenCalc::new(self, lower_bound_len, has_child)
  }

  /// Accounts for space necessary to reference a SSTable with the specified
  /// bloom filter length.
  ///
  /// `bf_len` must be less than `u16::MAX as usize * 8` or an error will occur
  /// when attempting to write the resulting node glyph.
  pub fn add_ss_table(&mut self, bf_len: usize) {
    self.num_offsets += 1;
    self.len += size_of::<RawSSTableInfo>();
    self.len += bf_len;
  }

  /// Accounts for the length of all tombstones; used when the length of each
  /// key is fixed.
  pub fn fixed_len_tombstones(&mut self, num_tombstones: usize) {
    let key_len = K::FIXED_LEN.unwrap();
    self.len += key_len * num_tombstones;
  }

  /// Accounts for the length of a single tombstone; used when each key is of
  /// variable length.
  pub fn add_tombstone(&mut self, tombstone: K::RefType<'_>) {
    assert!(K::FIXED_LEN.is_none());
    self.len += K::length(tombstone);
    self.num_offsets += 1;
  }

  /// Accounts for the length of all entries; used when the length of all keys
  /// and values are fixed.
  pub fn fixed_len_entries(&mut self, num_entries: usize) {
    let key_len = K::FIXED_LEN.unwrap();
    let entry_len = V::FIXED_LEN.unwrap();
    self.len += (key_len + entry_len) * num_entries;
  }

  /// Accounts for the length of a single entry; used when the length of either
  /// keys or values are variable.
  pub fn add_entry(&mut self, key: K::RefType<'_>, value: V::RefType<'_>) {
    assert!(K::FIXED_LEN.is_none() | V::FIXED_LEN.is_none());
    self.len += K::length(key) + V::length(value);
    self.num_offsets += 1;
  }

  /// Performs final calculations and returns the total length of a node.
  ///
  /// This is necessary because the offsets table must be padded to the nearest
  /// 8-byte boundary and amount of padding cannot be known until we know the
  /// total number of offsets required.
  pub fn finish(self) -> usize {
    let fixed_len = size_of::<GlyphHeader>() + size_of::<CLiMBTreeNodeHeader>();
    let offsets_len =
      round_to_word(self.num_offsets * size_of::<GlyphOffset>());
    fixed_len + offsets_len + self.len
  }
}

#[derive(Debug)]
#[must_use]
pub struct PivotLenCalc<'a, K, V> {
  nlc:           &'a mut CLiMBTreeNodeLenCalc<K, V>,
  header_len:    usize,
  dat_len:       usize,
  num_ss_tables: usize,
}

impl<'a, K, V> PivotLenCalc<'a, K, V> {
  pub fn new(
    nlc: &'a mut CLiMBTreeNodeLenCalc<K, V>,
    key_len: usize,
    has_child: bool,
  ) -> Self {
    let mut header_len = key_len + size_of::<RawPivotInfo>();
    if has_child {
      header_len += size_of::<GlyphHash>();
    }
    Self {
      nlc,
      header_len,
      dat_len: 0,
      num_ss_tables: 0,
    }
  }

  pub fn add_ss_table(&mut self, bloom_len: usize) -> Result<(), GlyphErr> {
    if bloom_len % 8 != 0 {
      Err(GlyphErr::CLiMBTreeIllegalBloomLen(bloom_len))
    } else if bloom_len > (u16::MAX as usize * 8) {
      Err(GlyphErr::CLiMBTreeIllegalBloomLen(bloom_len))
    } else {
      self.dat_len += size_of::<RawSSTableInfo>(); // Includes target hash
      self.dat_len += bloom_len;
      self.num_ss_tables += 1;
      Ok(())
    }
  }

  pub fn finish(mut self) {
    self.header_len += self.num_ss_tables * size_of::<GlyphOffset>();
    self.nlc.len += round_to_word(self.header_len);
    self.nlc.len += self.dat_len;
  }
}

pub struct CLiMBTreeNodeIterWriter<'a, 'b, 'c, K, V, PI, PSSTLI, NSSTLI, TI, EI>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
  PI: Iterator<Item = (K::RefType<'a>, Option<&'a GlyphHash>, PSSTLI)>
    + Clone
    + ExactSizeIterator,
  PSSTLI: Iterator<Item = (&'a GlyphHash, usize, BloomFilter<&'a [u8]>)>
    + ExactSizeIterator,
  NSSTLI: Iterator<Item = (&'a GlyphHash, usize, BloomFilter<&'a [u8]>)>
    + Clone
    + ExactSizeIterator,
  TI: Iterator<Item = K::RefType<'b>> + Clone + ExactSizeIterator,
  EI: Iterator<Item = (K::RefType<'c>, V::RefType<'c>)>
    + Clone
    + ExactSizeIterator,
{
  pivots:     PI,
  ss_tables:  NSSTLI,
  tombstones: TI,
  entries:    EI,
  _phantom:   PhantomData<(K, V, &'a (), &'b (), &'c ())>,
}

impl<'a, 'b, 'c, K, V, PI, SSTLI, NSSTLI, TI, EI>
  CLiMBTreeNodeIterWriter<'a, 'b, 'c, K, V, PI, SSTLI, NSSTLI, TI, EI>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
  PI: Iterator<Item = (K::RefType<'a>, Option<&'a GlyphHash>, SSTLI)>
    + Clone
    + ExactSizeIterator,
  SSTLI: Iterator<Item = (&'a GlyphHash, usize, BloomFilter<&'a [u8]>)>
    + ExactSizeIterator,
  NSSTLI: Iterator<Item = (&'a GlyphHash, usize, BloomFilter<&'a [u8]>)>
    + Clone
    + ExactSizeIterator,
  TI: Iterator<Item = K::RefType<'b>> + Clone + ExactSizeIterator,
  EI: Iterator<Item = (K::RefType<'c>, V::RefType<'c>)>
    + Clone
    + ExactSizeIterator,
{
  pub fn new(
    pivots: PI,
    ss_tables: NSSTLI,
    tombstones: TI,
    entries: EI,
  ) -> Self {
    Self {
      pivots,
      ss_tables,
      tombstones,
      entries,
      _phantom: Default::default(),
    }
  }
}

impl<'a, 'b, 'c, K, V, PI, SSTLI, NSSTLI, TI, EI> ToGlyph
  for CLiMBTreeNodeIterWriter<'a, 'b, 'c, K, V, PI, SSTLI, NSSTLI, TI, EI>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
  PI: Iterator<Item = (K::RefType<'a>, Option<&'a GlyphHash>, SSTLI)>
    + Clone
    + ExactSizeIterator,
  SSTLI: Iterator<Item = (&'a GlyphHash, usize, BloomFilter<&'a [u8]>)>
    + ExactSizeIterator,
  NSSTLI: Iterator<Item = (&'a GlyphHash, usize, BloomFilter<&'a [u8]>)>
    + Clone
    + ExactSizeIterator,
  TI: Iterator<Item = K::RefType<'b>> + Clone + ExactSizeIterator,
  EI: Iterator<Item = (K::RefType<'c>, V::RefType<'c>)>
    + Clone
    + ExactSizeIterator,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let mut enc = CLiMBTreeNodeWriter::<K, V>::new(
      target,
      cursor,
      self.pivots.len(),
      self.ss_tables.len(),
      self.tombstones.len(),
      self.entries.len(),
    )?;
    for (lower_bound, target, sstli) in self.pivots.clone() {
      let mut pw = enc.start_pivot(lower_bound, target, sstli.len())?;
      for (ss_table_hash, ss_table_len, ss_table_bf) in sstli {
        pw.write_ss_table(ss_table_hash, ss_table_len, &ss_table_bf)?;
      }
      pw.finish();
    }
    for (target_hash, target_len, bf) in self.ss_tables.clone() {
      enc.write_ss_table(
        target_hash,
        target_len,
        bf.num_hashes(),
        bf.data(),
      )?;
    }
    for tombstone in self.tombstones.clone() {
      enc.write_tombstone(tombstone)?;
    }
    for (key, value) in self.entries.clone() {
      enc.write_entry(key, value)?;
    }
    enc.finish()
  }

  fn glyph_len(&self) -> usize {
    let mut len_calc = CLiMBTreeNodeLenCalc::<K, V>::new();

    // Pivots
    for (pivot, op_child_hash, sstli) in self.pivots.clone() {
      let mut plc =
        len_calc.add_pivot(K::length(pivot), op_child_hash.is_some());
      for (_ss_table_hash, _ss_table_len, ss_table_bf) in sstli {
        plc.add_ss_table(ss_table_bf.data().len()).ok(); // Defer err until late.
      }
      plc.finish();
    }

    // SSTables
    for (_hash, _target_len, bf) in self.ss_tables.clone() {
      len_calc.add_ss_table(bf.data().len())
    }

    match (K::FIXED_LEN, V::FIXED_LEN) {
      (Some(_key_len), Some(_val_len)) => {
        // All data areas
        len_calc.fixed_len_tombstones(self.tombstones.len());
        len_calc.fixed_len_entries(self.entries.len());
      },
      (Some(_key_len), None) => {
        // Data area for pivots and tombstones, offsets for entries.
        len_calc.fixed_len_tombstones(self.tombstones.len());
        for (key, value) in self.entries.clone() {
          len_calc.add_entry(key, value);
        }
      },
      _ => {
        // Offsets for pivots, tombstones, and entries.
        for tombstone in self.tombstones.clone() {
          len_calc.add_tombstone(tombstone);
        }
        for (key, value) in self.entries.clone() {
          len_calc.add_entry(key, value);
        }
      },
    };
    len_calc.finish()
  }
}

/// Writes a node based on the
pub struct SSTableWriter<'a, 'b, TI, EI, K, V>
where
  TI: Iterator<Item = K::RefType<'a>> + Clone + ExactSizeIterator,
  EI: Iterator<Item = (K::RefType<'b>, V::RefType<'b>)>
    + Clone
    + ExactSizeIterator,
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  tombstones: TI,
  entries:    EI,
  _phantom:   PhantomData<(&'a K, &'b V)>,
}

impl<'a, 'b, TI, EI, K, V> SSTableWriter<'a, 'b, TI, EI, K, V>
where
  TI: Iterator<Item = K::RefType<'a>> + Clone + ExactSizeIterator,
  EI: Iterator<Item = (K::RefType<'b>, V::RefType<'b>)>
    + Clone
    + ExactSizeIterator,
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  pub fn new_cache(tombstones: TI, entries: EI) -> Self {
    Self {
      tombstones,
      entries,
      _phantom: Default::default(),
    }
  }
}

impl<'a, 'b, EI, K, V>
  SSTableWriter<'a, 'b, core::iter::Empty<K::RefType<'a>>, EI, K, V>
where
  EI: Iterator<Item = (K::RefType<'b>, V::RefType<'b>)>
    + Clone
    + ExactSizeIterator,
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  pub fn new_leaf(entries: EI) -> Self {
    Self {
      tombstones: core::iter::empty(),
      entries,
      _phantom: Default::default(),
    }
  }
}

impl<'a, 'b, TI, EI, K, V> ToGlyph for SSTableWriter<'a, 'b, TI, EI, K, V>
where
  TI: Iterator<Item = K::RefType<'a>> + Clone + ExactSizeIterator,
  EI: Iterator<Item = (K::RefType<'b>, V::RefType<'b>)>
    + Clone
    + ExactSizeIterator,
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let mut writer = CLiMBTreeNodeWriter::<K, V>::new(
      target,
      cursor,
      0,
      0,
      self.tombstones.len(),
      self.entries.len(),
    )?;
    for tombstone in self.tombstones.clone() {
      writer.write_tombstone(tombstone)?
    }
    for (key, value) in self.entries.clone() {
      writer.write_entry(key, value)?;
    }
    writer.finish()
  }

  fn glyph_len(&self) -> usize {
    let mut len_calc = CLiMBTreeNodeLenCalc::<K, V>::new();
    if K::FIXED_LEN.is_some() && V::FIXED_LEN.is_some() {
      len_calc.fixed_len_tombstones(self.tombstones.len());
      len_calc.fixed_len_entries(self.entries.len());
    } else {
      for tombstone in self.tombstones.clone() {
        len_calc.add_tombstone(tombstone);
      }
      for (key, value) in self.entries.clone() {
        len_calc.add_entry(key, value);
      }
    }
    len_calc.finish()
  }
}

pub struct ReplaceDataNodeWriter<'a, 'b, 'c, K, V, SSTLI, TI, EI>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
  SSTLI: Iterator<Item = (&'a GlyphHash, usize, BloomFilter<&'a [u8]>)>
    + Clone
    + ExactSizeIterator,
  TI: Iterator<Item = K::RefType<'b>> + Clone + ExactSizeIterator,
  EI: Iterator<Item = (K::RefType<'c>, V::RefType<'c>)>
    + Clone
    + ExactSizeIterator,
{
  /// The node we are replacing.
  ///
  /// We'll copy the entire pivots section over from the old node, as well as
  /// (possibly) the existing SSTable links.
  old_node:          &'a CLiMBTreeNodeGlyph<ArcGlyph, K, V>,
  /// A new iterator of links to SSTables.
  ss_tables:         SSTLI,
  /// Are we replacing all existing SSTables (`true`) or just appending new ones
  /// (`false`)?
  replace_ss_tables: bool,
  tombstones:        TI,
  entries:           EI,
  _phantom:          PhantomData<(&'b (), &'c ())>,
}

impl<'a, 'b, 'c, K, V, SSTLI, TI, EI>
  ReplaceDataNodeWriter<'a, 'b, 'c, K, V, SSTLI, TI, EI>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
  SSTLI: Iterator<Item = (&'a GlyphHash, usize, BloomFilter<&'a [u8]>)>
    + Clone
    + ExactSizeIterator,
  TI: Iterator<Item = K::RefType<'b>> + Clone + ExactSizeIterator,
  EI: Iterator<Item = (K::RefType<'c>, V::RefType<'c>)>
    + Clone
    + ExactSizeIterator,
{
  pub fn new(
    old_node: &'a CLiMBTreeNodeGlyph<ArcGlyph, K, V>,
    ss_tables: SSTLI,
    replace_ss_tables: bool,
    tombstones: TI,
    entries: EI,
  ) -> Self {
    Self {
      old_node,
      ss_tables,
      replace_ss_tables,
      tombstones,
      entries,
      _phantom: Default::default(),
    }
  }
}

impl<'a, 'b, 'c, K, V, SSTLI, TI, EI> ToGlyph
  for ReplaceDataNodeWriter<'a, 'b, 'c, K, V, SSTLI, TI, EI>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
  SSTLI: Iterator<Item = (&'a GlyphHash, usize, BloomFilter<&'a [u8]>)>
    + Clone
    + ExactSizeIterator,
  TI: Iterator<Item = K::RefType<'b>> + Clone + ExactSizeIterator,
  EI: Iterator<Item = (K::RefType<'c>, V::RefType<'c>)>
    + Clone
    + ExactSizeIterator,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let num_ss_tables = if self.replace_ss_tables {
      self.ss_tables.len()
    } else {
      self.old_node.num_ss_tables() + self.ss_tables.len()
    };

    let mut writer = CLiMBTreeNodeWriter::<K, V>::new(
      target,
      cursor,
      self.old_node.num_pivots(),
      num_ss_tables,
      self.tombstones.len(),
      self.entries.len(),
    )?;

    // === Pivots From Old Node ===
    for pivot in self.old_node.iter_pivots() {
      let ssti_it = pivot.iter_ss_tables();
      let mut pw = writer.start_pivot(
        pivot.lower_bound(),
        pivot.child_hash(),
        ssti_it.len(),
      )?;
      for ssti in ssti_it {
        pw.write_ss_table(
          ssti.target_hash(),
          ssti.target_length(),
          &ssti.bloom_filter(),
        )?;
      }
      pw.finish();
    }

    if !self.replace_ss_tables {
      for ssti in self.old_node.iter_ss_tables() {
        writer.write_ss_table(
          ssti.target_hash(),
          ssti.target_length(),
          ssti.bloom_k(),
          ssti.bloom_data(),
        )?;
      }
    }
    for (target_hash, target_len, bf) in self.ss_tables.clone() {
      writer.write_ss_table(
        target_hash,
        target_len,
        bf.num_hashes(),
        bf.data(),
      )?;
    }

    // === Tombstones and Entries From Update Set ===
    for tombstone in self.tombstones.clone() {
      writer.write_tombstone(tombstone)?;
    }
    for (key, value) in self.entries.clone() {
      writer.write_entry(key, value)?;
    }
    writer.finish()
  }

  fn glyph_len(&self) -> usize {
    let mut lc = CLiMBTreeNodeLenCalc::<K, V>::new();

    // === Pivots From Old Node ===
    for pivot in self.old_node.iter_pivots() {
      let mut plc = lc.add_pivot(
        K::length(pivot.lower_bound()),
        pivot.child_hash().is_some(),
      );
      for ssti in pivot.iter_ss_tables() {
        plc.add_ss_table(ssti.bloom_length()).ok(); // LATER: Handle error condition.
      }
      plc.finish();
    }

    //=== SSTables ===/
    if !self.replace_ss_tables {
      for ssti in self.old_node.iter_ss_tables() {
        lc.add_ss_table(ssti.bloom_length());
      }
    }
    for (_target_hash, _target_len, bf) in self.ss_tables.clone() {
      lc.add_ss_table(bf.data().len());
    }

    // === Tombstones and Entries from Update Set ===
    if K::FIXED_LEN.is_some() {
      lc.fixed_len_tombstones(self.tombstones.len())
    } else {
      for tombstone in self.tombstones.clone() {
        lc.add_tombstone(tombstone);
      }
    }
    if K::FIXED_LEN.is_some() && V::FIXED_LEN.is_some() {
      lc.fixed_len_entries(self.entries.len());
    } else {
      for (key, value) in self.entries.clone() {
        lc.add_entry(key, value);
      }
    }
    lc.finish()
  }
}
