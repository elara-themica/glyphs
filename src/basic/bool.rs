use crate::{
  glyph::glyph_close,
  util::debug::{HexDump, ShortHexDump},
  zerocopy::{round_to_word, ZeroCopy},
  DecodeErr, EncodedGlyph, FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType,
  ToGlyph,
};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
};
use std::ops::Deref;

/// A glyph containing a boolean value.
///
pub struct BoolGlyph<G: Deref<Target = Glyph>>(G);

impl<G: Deref<Target = Glyph>> BoolGlyph<G> {
  /// Fetches the glyph's truth value.
  ///
  /// `BoolGlyph`s are short glyphs, with the content stored in the length
  /// filed of the [`GlyphHeader`].  If all of these bytes are zero, the truth
  /// value will be `false`.  In all other conditions, it will be `true`.
  pub fn get(&self) -> bool {
    self.0.header().short_content() != &[0u8; 4]
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for BoolGlyph<G> {
  type Error = GlyphErr;

  fn from_glyph(source: G) -> Result<Self, DecodeErr<G, GlyphErr>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Bool) {
      Err(DecodeErr::new(source, err))
    } else {
      Ok(BoolGlyph(source))
    }
  }
}

impl<G: Deref<Target = Glyph>> Debug for BoolGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "BoolGlyph({:?})", self.get())?;
    Ok(())
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for BoolGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> &Glyph {
    &self.0
  }
}

impl<G: Deref<Target = Glyph>> Eq for BoolGlyph<G> {}

impl<G: Deref<Target = Glyph>> Ord for BoolGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.get().cmp(&other.get())
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for BoolGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.get() == other.get()
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for BoolGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

/// A dense bit vector, with 8 bits per byte rather than a `[bool]`
///
/// Ideally, we would have liked to us
#[derive(Copy, Clone)]
pub struct BitVec<B>
where
  B: AsRef<[u8]>,
{
  /// The source bytes
  data:         B,
  /// The number of bits in the last byte which are padding
  bits_padding: u8,
}

impl<B> BitVec<B>
where
  B: AsRef<[u8]>,
{
  /// Create a new BitVector from the provided buffer.
  ///
  /// # Parameters:
  ///
  /// `data`: a slice of bytes that contain the bit array.
  /// `length`: an optional length (in bits), if different from
  ///           `data.len() * 8`.
  ///
  /// # Errors:
  ///
  /// A [`GlyphErr::BitVecLenOverflow`] will be returned if the length given
  /// is longer than the data vector provided.
  pub fn from_bytes(data: B, bits_padding: u8) -> Self {
    Self { data, bits_padding }
  }

  /// Returns the length of the vector, in bits.
  pub fn len(&self) -> u64 {
    self.data.as_ref().len() as u64 * 8 - self.bits_padding as u64
  }

  /// Returns `true` if the vector is of length zero
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Gets the bit at position `index`.
  pub fn get(&self, index: u64) -> Option<bool> {
    // Bounds Check
    if index >= self.len() {
      None
    } else {
      let data = self.data.as_ref();
      let (byte_num, bit_mask) = Self::index_mask(index);
      let value = data.get(byte_num)?;
      let result = value & bit_mask;
      Some(result != 0)
    }
  }

  /// Return a new instance of this bit vector, bound to the original's
  /// lifetime.
  ///
  /// This is typically used to avoid a generic in functions that receive this
  /// type as a parameter.
  pub fn borrow(&self) -> BitVec<&[u8]> {
    BitVec {
      data:         self.data.as_ref(),
      bits_padding: self.bits_padding,
    }
  }

  /// Returns an iterator through all the individual bits in this bit vector.
  pub fn iter(
    &self,
  ) -> impl Iterator<Item = bool>
       + Clone
       + ExactSizeIterator
       + DoubleEndedIterator
       + '_ {
    IterBits {
      vector:   self.borrow(),
      position: 0,
      end:      self.len(),
    }
  }

  /// For a given bit index, return a byte index and a mask with (only) that bit set.
  #[inline(always)]
  fn index_mask(bit_index: u64) -> (usize, u8) {
    let byte_num = bit_index / 8;
    let bit_num = bit_index % 8;
    let bit_mask: u8 = 0x80u8 >> bit_num;
    (byte_num as usize, bit_mask)
  }
}

impl<B> BitVec<B>
where
  B: AsRef<[u8]> + AsMut<[u8]>,
{
  /// Sets the specified bit to the provided value.
  pub fn set(&mut self, index: u64, value: bool) -> Option<()> {
    if index < self.len() {
      let content = self.data.as_mut();
      let (index, mask) = Self::index_mask(index);
      let old = content.get_mut(index)?;
      if value {
        *old |= mask;
      } else {
        *old &= !mask;
      }
      Some(())
    } else {
      None
    }
  }
}

impl<'a> BitVec<&'a [u8]> {
  /// Returns an iterator through all the individual bits in this vit vector,
  /// but the iterator's lifetime is bound only to the underlying buffer.
  pub fn iter_parsed(
    &self,
  ) -> impl Iterator<Item = bool>
       + Clone
       + ExactSizeIterator
       + DoubleEndedIterator
       + 'a {
    IterBits {
      vector:   BitVec {
        data:         self.data,
        bits_padding: self.bits_padding,
      },
      position: 0,
      end:      self.len(),
    }
  }
}

#[cfg(feature = "alloc")]
impl BitVec<alloc::boxed::Box<[u8]>> {
  /// Creates a new bit vector sufficient to hold `num_bits` bits.  They will
  /// all be initialized to zero/false.
  ///
  /// An error will be returned if memory allocation fails.
  pub fn new(num_bits: u64) -> Result<Self, GlyphErr> {
    let num_bytes = (num_bits + 7) / 8;
    let bits_padding = (8 - (num_bits % 8)) as u8 & 0b111;
    let data = unsafe {
      alloc::boxed::Box::<[u8]>::try_new_zeroed_slice(num_bytes as usize)?
        .assume_init()
    };

    Ok(BitVec { data, bits_padding })
  }
}
impl<B> AsRef<[u8]> for BitVec<B>
where
  B: AsRef<[u8]>,
{
  fn as_ref(&self) -> &[u8] {
    self.data.as_ref()
  }
}

impl<B> Debug for BitVec<B>
where
  B: AsRef<[u8]>,
{
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    let mut d = f.debug_struct("BitVector");
    d.field("bits_padding", &self.bits_padding);
    if self.data.as_ref().len() <= 32 {
      d.field("bits", &ShortHexDump(self.data.as_ref(), 2));
    } else {
      d.field("bits", &HexDump(self.data.as_ref()));
    }
    d.finish()
  }
}

impl<B> Eq for BitVec<B> where B: AsRef<[u8]> {}

impl<G: Deref<Target = Glyph>> FromGlyph<G>
  for BitVec<alloc::boxed::Box<[u8]>>
{
  type Error = GlyphErr;

  fn from_glyph(source: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    match BitVec::<&[u8]>::from_glyph(source.deref()) {
      Ok(b) => {
        let data = alloc::boxed::Box::<[u8]>::from(b.data);
        Ok(BitVec {
          data,
          bits_padding: b.bits_padding,
        })
      },
      Err(e) => {
        // Awkwardness to satisfy borrow checker
        let err = e.into_parts().1;
        Err(DecodeErr::new(source, err))
      },
    }
  }
}

impl<'a> FromGlyph<&'a Glyph> for BitVec<&'a [u8]> {
  type Error = GlyphErr;

  fn from_glyph(
    source: &'a Glyph,
  ) -> Result<Self, DecodeErr<&'a Glyph, Self::Error>> {
    let bvg = BitVecGlyph::<&'a Glyph>::from_glyph(source)?;
    let bv = bvg.bit_vector_parsed();
    Ok(bv)
  }
}

impl<B> Ord for BitVec<B>
where
  B: AsRef<[u8]>,
{
  fn cmp(&self, other: &Self) -> Ordering {
    //=== Complexity here is to ignore unused bits in the buffers.

    // Compare overlapping full bytes
    let overlapping_bits = self.len().min(other.len());
    let overlapping_bytes = (overlapping_bits / 8) as usize;
    let extra_bits = overlapping_bits % 8;
    match (
      self.data.as_ref().get(0..overlapping_bytes),
      self.data.as_ref().get(0..overlapping_bytes),
    ) {
      (Some(self_bytes), Some(other_bytes)) => {
        match self_bytes.cmp(other_bytes) {
          Ordering::Less => return Ordering::Less,
          Ordering::Greater => return Ordering::Greater,
          Ordering::Equal => {
            if extra_bits == 0 && self.len() == other.len() {
              return Ordering::Equal;
            }
          },
        }
      },
      _ => unreachable!("A BitVec has a length greater than its data buffer"),
    }

    // Compare overlapping partial bits
    match (
      self.data.as_ref().get(overlapping_bytes + 1),
      self.data.as_ref().get(overlapping_bytes + 1),
    ) {
      (Some(self_byte), Some(other_byte)) => {
        let mask = 0b1111_1111u8 << (8 - extra_bits);
        let self_byte = *self_byte & mask;
        let other_byte = *other_byte & mask;
        match self_byte.cmp(&other_byte) {
          Ordering::Less => return Ordering::Less,
          Ordering::Greater => return Ordering::Greater,
          Ordering::Equal => {
            if self.len() == other.len() {
              return Ordering::Equal;
            }
          },
        }
      },
      _ => unreachable!("A BitVec has a length greater than its data buffer"),
    }

    // Shorter bit vectors come first
    self.len().cmp(&other.len())
  }
}

impl<B, C> PartialEq<BitVec<C>> for BitVec<B>
where
  B: AsRef<[u8]>,
  C: AsRef<[u8]>,
{
  fn eq(&self, other: &BitVec<C>) -> bool {
    let a = self.borrow();
    let b = other.borrow();
    a.cmp(&b) == Ordering::Equal
  }
}

impl<B, C> PartialOrd<BitVec<B>> for BitVec<C>
where
  B: AsRef<[u8]>,
  C: AsRef<[u8]>,
{
  fn partial_cmp(&self, other: &BitVec<B>) -> Option<Ordering> {
    let a = self.borrow();
    let b = other.borrow();
    Some(a.cmp(&b))
  }
}

impl<B> ToGlyph for BitVec<B>
where
  B: AsRef<[u8]>,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();
    if self.len() > 0 {
      let bit_padding = (8 - (self.len() % 8) as u8) & 0b0000_0111;
      bit_padding.bbwr(target, cursor)?;
      u8::bbwrs(self.data.as_ref(), target, cursor)?;
    }
    glyph_close(GlyphType::VecBool, target, offset, cursor, true)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + if self.len() > 0 {
        round_to_word(size_of::<u8>() + self.data.as_ref().len())
      } else {
        0
      }
  }
}

#[derive(Clone)]
struct IterBits<B>
where
  B: AsRef<[u8]>,
{
  vector:   BitVec<B>,
  position: u64,
  end:      u64,
}

impl<B> DoubleEndedIterator for IterBits<B>
where
  B: AsRef<[u8]>,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    if self.position <= self.end {
      let result = self.vector.get(self.end)?;
      self.end -= 1;
      Some(result)
    } else {
      None
    }
  }
}

impl<B> ExactSizeIterator for IterBits<B>
where
  B: AsRef<[u8]>,
{
  fn len(&self) -> usize {
    (self.end - self.position) as usize
  }
}

impl<B> Iterator for IterBits<B>
where
  B: AsRef<[u8]>,
{
  type Item = bool;

  fn next(&mut self) -> Option<Self::Item> {
    if self.position <= self.end {
      let result = self.vector.get(self.position)?;
      self.position += 1;
      Some(result)
    } else {
      None
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    let len = self.len();
    (len, Some(len))
  }
}

/// A glyph containing a dense (8 bits per byte) bit vector.
pub struct BitVecGlyph<G: Deref<Target = Glyph>> {
  glyph: G,
}

impl<G: Deref<Target = Glyph>> BitVecGlyph<G> {
  const BIT_PADDING_MASK: u8 = 0b0000_0111;

  /// Returns the actual bit vector contained in this glyph.
  ///
  /// See the [`BitVec`] type for more details, though note that the
  /// resulting BitVector will be immutable.
  pub fn bit_vector(&self) -> BitVec<&[u8]> {
    if let (Some(bits_padding), Some(buffer)) =
      (self.glyph.content().get(0), self.glyph.content().get(1..))
    {
      let bits_padding = *bits_padding & Self::BIT_PADDING_MASK;
      BitVec::from_bytes(buffer, bits_padding)
    } else {
      BitVec::from_bytes(&[][..], 0)
    }
  }
}

impl<'a> BitVecGlyph<&'a Glyph> {
  /// Returns the actual bit vector contained in this glyph, but with a lifetime
  /// bound only to the underlying buffer.
  ///
  /// See the [`BitVec`] type for more details, though note that the
  /// resulting BitVector will be immutable.
  pub fn bit_vector_parsed(&self) -> BitVec<&'a [u8]> {
    if let (Some(bits_padding), Some(buffer)) =
      (self.glyph.content().get(0), self.glyph.content().get(1..))
    {
      let bits_padding = *bits_padding & Self::BIT_PADDING_MASK;
      BitVec::from_bytes(buffer, bits_padding)
    } else {
      BitVec::from_bytes(&[][..], 0)
    }
  }
}

impl<G: Deref<Target = Glyph>> Debug for BitVecGlyph<G> {
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    let mut df = f.debug_struct("BitVectorGlyph");
    let bv = self.bit_vector();
    df.field("num_bits", &bv.len());
    if bv.as_ref().len() <= 32 {
      df.field("bits", &ShortHexDump(bv.as_ref(), 4));
    } else if bv.as_ref().len() <= 1_048_576 {
      // 1MB max display
      df.field("bits", &HexDump(bv.as_ref()));
    }
    df.finish()
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for BitVecGlyph<G> {
  fn into_inner(self) -> G {
    self.glyph
  }

  fn glyph(&self) -> &Glyph {
    &self.glyph.deref()
  }
}

impl<G: Deref<Target = Glyph>> Eq for BitVecGlyph<G> {}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for BitVecGlyph<G> {
  type Error = GlyphErr;

  fn from_glyph(source: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    match source.header().confirm_type(GlyphType::VecBool) {
      Ok(_) => Ok(BitVecGlyph { glyph: source }),
      Err(err) => Err(DecodeErr::new(source, err)),
    }
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for BitVecGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for BitVecGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Deref<Target = Glyph>> Ord for BitVecGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.bit_vector().cmp(&other.bit_vector())
  }
}

impl<G> FromGlyph<G> for bool
where
  G: Deref<Target = Glyph>,
{
  type Error = GlyphErr;

  fn from_glyph(source: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Bool) {
      return Err(DecodeErr::new(source, err));
    }
    let content = source.header().short_content();
    let value = u32::from_le_bytes(*content);
    Ok(value != 0)
  }
}

impl ToGlyph for bool {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let bytes = match self {
      true => [1u8, 0, 0, 0],
      false => [0u8; 4],
    };
    GlyphHeader::new_short(GlyphType::Bool, bytes).bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

/// This specialized implementation encodes a slice of booleans as a bit vector
/// (and not individual [`BoolGlyph`]s.
impl ToGlyph for [bool] {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    if self.len() > 0 {
      let glyph_start = *cursor;
      *cursor += size_of::<GlyphHeader>();
      let bits_padding = (8 - self.len() % 8) as u8 & 0b0000_0111;
      bits_padding.bbwr(target, cursor)?;
      let num_bytes = (self.len() + 7) / 8;
      // We're going to construct a mutable BitVector in place and set the bits.
      let bytes = u8::bbrfs_mut(target, cursor, num_bytes)?;
      if let Some(byte) = bytes.last_mut() {
        *byte = 0; // Make sure any unused bits are zeroed.
      }
      let mut bv = BitVec::from_bytes(bytes, bits_padding);
      for (i, bit) in self.iter().enumerate() {
        bv.set(i as u64, *bit);
      }
      glyph_close(GlyphType::VecBool, target, glyph_start, cursor, true)
    } else {
      GlyphHeader::new_short(GlyphType::VecBool, Default::default())
        .bbwr(target, cursor)?;
      Ok(())
    }
  }

  fn glyph_len(&self) -> usize {
    let num_bits = self.len();
    let data_bytes = (num_bits + 7) / 8;
    match num_bits {
      0 => size_of::<GlyphHeader>(),
      _ => {
        size_of::<GlyphHeader>() + round_to_word(size_of::<u8>() + data_bytes)
      },
    }
  }
}

#[cfg(test)]
#[allow(unused_imports)]
mod tests {
  use super::*;
  use alloc::vec::Vec;
  use std::{dbg, vec};

  #[test]
  fn bit_vec() {
    // Vector of bool
    let bools = vec![true, false, true, false, true, true, false, true];
    let bools_g = Glyph::new(&bools[..]).unwrap();
    let bools_g = BitVecGlyph::<_>::from_glyph(bools_g).unwrap();

    for (bools_val, bools_g_val) in
      bools.iter().zip(bools_g.bit_vector().iter())
    {
      assert_eq!(*bools_val, bools_g_val);
    }

    // Basic BitVec ops, zero length
    let bvz = BitVec::new(0).unwrap();
    assert!(bvz.is_empty());
    assert_eq!(bvz.len(), 0);
    assert!(bvz.iter().collect::<Vec<_>>().is_empty()); // Empty iter

    // Basic BitVecG ops
    let bvz_g = Glyph::new(&bvz).unwrap();
    let bvz_g = BitVecGlyph::<_>::from_glyph(bvz_g).unwrap();
    assert_eq!(bvz_g.bit_vector(), bvz);

    // Test with varying bit lengths covering every value modulo 8
    for len in (0..16u64).chain(100..130u64) {
      let mut bv = BitVec::new(len).unwrap();
      for i in 0..len {
        bv.set(i, (i % 2) == 0).unwrap(); // Set even-indexed bits
      }

      // Validate bits
      for i in 0..len {
        assert_eq!(bv.get(i).unwrap(), (i % 2) == 0);
      }

      // Encode and decode the BitVector
      let bvg = Glyph::new(&bv).unwrap();
      // dbg!(&bvg);
      let decoded = BitVec::<&[u8]>::from_glyph(bvg.as_ref()).unwrap();
      // dbg!(&decoded);

      // Check equality between original and decoded
      assert_eq!(bv.as_ref(), decoded.as_ref());
    }
  }
}
