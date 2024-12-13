//! Numbers, strings, boolean, nothing, option, etc...
use crate::{
  glyph::glyph_close,
  util::debug::{HexDump, ShortHexDump},
  zerocopy::{
    bounds_check, pad_to_word, round_to_word, HasZeroCopyID, ZeroCopy,
    ZeroCopyGlyph, ZeroCopyTypeID, F32, F64, I128, I16, I32, I64, U128, U16,
    U32, U64,
  },
  FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType,
  GlyphType::{Float, SignedInt, UnsignedInt},
  ParsedGlyph, ToGlyph,
};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
  marker::PhantomData,
  ops::Deref,
  ptr::NonNull,
  str::from_utf8,
};

/// A single instance of a basic zero-copy type, e.g., a [`U32`].
///
/// The type is generic over the type of glyph `G`, allowing it to be
/// constructed from borrowed or owned data, and over the corresponding type
/// `T`, which must implement [`ZeroCopyGlyph`].  This requires that the type
/// be readable directly from a string of bytes (i.e., is [`ZeroCopy`]) as well
/// as providing an associated [`GlyphType`].
///
/// This type can only be constructed via the [`FromGlyph`] trait, which will
/// check that (1) type ID of the source glyph matches that of the target type,
/// and (2) will perform a bounds check to ensure the glyph is large enough to
/// contain an instance of `T`.
///
/// Types with a size of <= 4 bytes will be written as short glyphs and read
/// from the glyph header.
///
// TODO: Write doc example.
pub struct BasicGlyph<G: Glyph, T: ZeroCopyGlyph>(G, PhantomData<T>);

impl<G: Glyph, T: ZeroCopyGlyph> FromGlyph<G> for BasicGlyph<G, T> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(T::GLYPH_TYPE_ID)?;
    if size_of::<T>() > 4 {
      bounds_check(glyph.content_padded(), size_of::<T>())?;
      Ok(Self(glyph, PhantomData::default()))
    } else {
      Ok(Self(glyph, PhantomData::default()))
    }
  }
}

impl<G: Glyph, T: ZeroCopyGlyph> Deref for BasicGlyph<G, T> {
  type Target = T;

  fn deref(&self) -> &Self::Target {
    // SAFETY: We already did the bounds check in `FromGlyph`.
    unsafe {
      let buf = if size_of::<T>() > 4 {
        self.0.content_padded()
      } else {
        &self.0.header().short_content_ref()[..]
      };
      T::bbrf_u(buf, &mut 0)
    }
  }
}

impl<'a, T: ZeroCopyGlyph> BasicGlyph<ParsedGlyph<'a>, T> {
  /// Returns a reference to the target type from the underlying buffer (i.e.,
  /// not also this `BasicGlyph`.
  pub fn get_parsed(&self) -> &'a T {
    // SAFETY: We already did the bounds check in `FromGlyph`.
    unsafe {
      let buf = if size_of::<T>() > 4 {
        self.0.content_padded_parsed()
      } else {
        &self.0.header_parsed().short_content_ref()[..]
      };
      T::bbrf_u(buf, &mut 0)
    }
  }
}

#[derive(Copy, Clone, Eq, PartialOrd, PartialEq, Debug)]
#[repr(packed)]
pub(crate) struct BasicVecGlyphHeader {
  /// A type identifier.  See [`ZeroCopyTypeID`].
  pub basic_type_id: U16,

  /// The length of the basic type, in bytes.
  pub type_len: U16,

  /// Allows the specification of arbitrary dimensionality.
  ///
  /// See the documentation on [`BasicVecGlyph`].
  pub tensor_rank: u8,

  /// Reserved for future use.
  pub _reserved: [u8; 3],
}

impl BasicVecGlyphHeader {
  pub fn new_vec<T: HasZeroCopyID>() -> Result<Self, GlyphErr> {
    let type_len = U16::from(
      u16::try_from(size_of::<T>())
        .map_err(|_t| GlyphErr::BasicTypeLenOverflow)?,
    );

    Ok(Self {
      basic_type_id: T::ZERO_COPY_ID.into(),
      type_len,
      tensor_rank: 0,
      _reserved: Default::default(),
    })
  }

  pub fn confirm_zero_copy_type(
    &self,
    expected: ZeroCopyTypeID,
  ) -> Result<(), GlyphErr> {
    let observed = self.get_zero_copy_type_id();
    if observed == expected {
      Ok(())
    } else {
      Err(GlyphErr::UnexpectedZeroCopyType { expected, observed })
    }
  }

  pub fn get_zero_copy_type_id(&self) -> ZeroCopyTypeID {
    self.basic_type_id.into()
  }
}

unsafe impl ZeroCopy for BasicVecGlyphHeader {}

/// A vector of a basic zero-copy type, e.g., a [`U32`].
///
/// The type is generic over the type of glyph `G`, allowing it to be
/// constructed from borrowed or owned data, and over the corresponding type
/// `T`, which must implement [`ZeroCopyGlyph`].  This requires that the type
/// be readable directly from a string of bytes (i.e., is [`ZeroCopy`]) as well
/// as providing an associated [`GlyphType`].
///
/// This type can only be constructed via the [`FromGlyph`] trait, which will
/// check that (1) type ID of the source glyph matches that of the target type,
/// and (2) will perform a bounds check to ensure the glyph is large enough to
/// contain an instance of `T`.
///
/// Types with a size of <= 4 bytes will be written as short glyphs and read
/// from the glyph header.
///

pub struct BasicVecGlyph<G: Glyph, T: ZeroCopy>(G, NonNull<[T]>);

impl<G: Glyph, T: HasZeroCopyID> FromGlyph<G> for BasicVecGlyph<G, T> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::BasicVecGlyph)?;
    let cursor = &mut 0;
    let content = glyph.content();
    let header = BasicVecGlyphHeader::bbrf(content, cursor)?;
    header.confirm_zero_copy_type(T::ZERO_COPY_ID)?;
    *cursor += header.tensor_rank as usize * size_of::<U32>();
    *cursor = round_to_word(*cursor);
    let slice_ptr = NonNull::from(T::bbrfs_i(content, cursor));
    Ok(Self(glyph, slice_ptr))
  }
}

impl<G: Glyph, T: ZeroCopy> Deref for BasicVecGlyph<G, T> {
  type Target = [T];

  fn deref(&self) -> &Self::Target {
    // SAFETY: Glyph referenced is immutable and pinned.
    unsafe { self.1.as_ref() }
  }
}

impl<'a, T: ZeroCopy> BasicVecGlyph<ParsedGlyph<'a>, T> {
  pub fn get_parsed(&self) -> &'a [T] {
    // SAFETY: Glyph referenced is immutable, pinned, and result's lifetime is
    //         bound by that of the underlying buffer.
    unsafe { self.1.as_ref() }
  }
}

impl<G: Glyph, T: ZeroCopy + Debug> Debug for BasicVecGlyph<G, T> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    if !f.alternate() {
      core::fmt::Debug::fmt(self.deref(), f)
    } else {
      let mut df = f.debug_tuple(core::any::type_name::<Self>());
      df.field(&self.0);
      df.finish()
    }
  }
}

impl<T> ToGlyph for Option<T>
where
  T: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    match self {
      None => ().glyph_encode(target, cursor),
      Some(src) => src.glyph_encode(target, cursor),
    }
  }

  fn glyph_len(&self) -> usize {
    match self {
      None => ().glyph_len(),
      Some(src) => src.glyph_len(),
    }
  }
}

impl<B, T> FromGlyph<B> for Option<T>
where
  B: Glyph,
  T: FromGlyph<B>,
{
  fn from_glyph(source: B) -> Result<Self, GlyphErr> {
    let type_id = source.header().glyph_type();
    if type_id == GlyphType::Nothing {
      return Ok(None);
    } else {
      let val = T::from_glyph(source)?;
      Ok(Some(val))
    }
  }
}

impl ToGlyph for () {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    GlyphHeader::new_short(GlyphType::Nothing, [0; 4]).bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

impl<G> FromGlyph<G> for ()
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Nothing)?;
    Ok(())
  }
}

/// A glyph that represents the concept of nothingness--like zero but broader
/// than the concept of numbers.
///
/// Can be created by encoding the rust unit type `()`.
pub struct NothingGlyph<G>(G)
where
  G: Glyph;

impl<G> FromGlyph<G> for NothingGlyph<G>
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Nothing)?;
    Ok(NothingGlyph(source))
  }
}

impl<G> Debug for NothingGlyph<G>
where
  G: Glyph,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "NothingGlyph")
  }
}

impl<T: Glyph> PartialEq for NothingGlyph<T> {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl<T: Glyph> Eq for NothingGlyph<T> {}

impl<T: Glyph> PartialOrd for NothingGlyph<T> {
  fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
    Some(Ordering::Equal)
  }
}

impl<T> Ord for NothingGlyph<T>
where
  T: Glyph,
{
  fn cmp(&self, _other: &Self) -> Ordering {
    Ordering::Equal
  }
}

/// Represents the concept that some information exists, but has been removed,
/// e.g., for security or confidentiality.
#[derive(Copy, Clone, Debug)]
pub struct Redacted;

impl<G> FromGlyph<G> for Redacted
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Redacted)?;
    Ok(Redacted)
  }
}

impl ToGlyph for Redacted {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    GlyphHeader::new_short(GlyphType::Redacted, [0; 4]).bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

impl Eq for Redacted {}

impl PartialEq for Redacted {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl PartialOrd for Redacted {
  fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
    Some(Ordering::Equal)
  }
}

impl Ord for Redacted {
  fn cmp(&self, _other: &Self) -> Ordering {
    Ordering::Equal
  }
}

/// A glyph representing the concept of some information that exists, but which
/// has been removed, e.g., for security or confidentiality.
///
/// See also [`Redacted`].
pub struct RedactedGlyph<G: Glyph>(G);

impl<G: Glyph> FromGlyph<G> for RedactedGlyph<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Redacted)?;
    Ok(RedactedGlyph(source))
  }
}

impl<G: Glyph> Debug for RedactedGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "RedactedGlyph")
  }
}

impl<G: Glyph> PartialEq for RedactedGlyph<G> {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl<G: Glyph> Eq for RedactedGlyph<G> {}

impl<G: Glyph> PartialOrd for RedactedGlyph<G> {
  fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
    Some(Ordering::Equal)
  }
}

impl<G: Glyph> Ord for RedactedGlyph<G> {
  fn cmp(&self, _other: &Self) -> Ordering {
    Ordering::Equal
  }
}

/// Something that is unknown.
///
/// See also [`UnknownGlyph`].
#[derive(Copy, Clone, Debug)]
pub struct Unknown;

impl<G: Glyph> FromGlyph<G> for Unknown {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Unknown)?;
    Ok(Unknown)
  }
}

impl ToGlyph for Unknown {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    GlyphHeader::new_short(GlyphType::Unknown, [0; 4]).bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

impl Eq for Unknown {}

impl PartialEq for Unknown {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl PartialOrd for Unknown {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(Ord::cmp(self, other))
  }
}

impl Ord for Unknown {
  fn cmp(&self, _other: &Self) -> Ordering {
    Ordering::Equal
  }
}

/// A glyph representing the concept of something that is unknown.
///
/// This is distinct from a [`NothingGlyph`] in that the latter is an assertion
/// that no value is present.
pub struct UnknownGlyph<G: Glyph>(G);

impl<G: Glyph> FromGlyph<G> for UnknownGlyph<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Unknown)?;
    Ok(UnknownGlyph(source))
  }
}

impl<G: Glyph> Debug for UnknownGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "UnknownGlyph")
  }
}

impl<G: Glyph> PartialEq for UnknownGlyph<G> {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl<G: Glyph> Eq for UnknownGlyph<G> {}

impl<G: Glyph> PartialOrd for UnknownGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(Ord::cmp(self, other))
  }
}

impl<G: Glyph> Ord for UnknownGlyph<G> {
  fn cmp(&self, _other: &Self) -> Ordering {
    Ordering::Equal
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

impl<G> FromGlyph<G> for bool
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Bool)?;
    let content = source.short_content();
    let value = u32::from_le_bytes(content);
    Ok(value != 0)
  }
}

/// A glyph containing a boolean value.
///
pub struct BoolGlyph<G: Glyph>(G);

impl<G: Glyph> BoolGlyph<G> {
  pub fn get(&self) -> bool {
    self.0.header().short_content() != [0u8; 4]
  }
}

impl<G: Glyph> FromGlyph<G> for BoolGlyph<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.confirm_type(GlyphType::Bool)?;
    Ok(BoolGlyph(source))
  }
}

impl<G: Glyph> Debug for BoolGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    if !f.alternate() {
      Debug::fmt(&self.get(), f)
    } else {
      let mut df = f.debug_tuple("BoolGlyph");
      df.field(&self.0);
      df.finish()
    }
  }
}

impl<G: Glyph> PartialEq for BoolGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.get() == other.get()
  }
}

impl<G: Glyph> Eq for BoolGlyph<G> {}

impl<G: Glyph> PartialOrd for BoolGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for BoolGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.get().cmp(&other.get())
  }
}

/// A dense bit vector, with 8 bits per byte rather than a `[bool]`
///
/// Ideally, we would have liked to us
#[derive(Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct BitVector<B>
where
  B: AsRef<[u8]>,
{
  /// The source bytes
  data: B,
  /// The number of bits in the vector.
  ///
  /// A separate length (other than self.data.len() * 8) is necessary to allow
  /// lengths other than multiples of 8.
  len:  usize,
}

impl<B> BitVector<B>
where
  B: AsRef<[u8]>,
{
  /// Create a new BitVector from the provided buffer.
  ///
  /// # Parameters:
  ///
  /// `data`: a slice of bytes that contain the bit array.
  /// `length`: an optional length (in bits), if different from `data.len() * 8`.
  pub fn from_bytes(data: B, length: Option<usize>) -> Self {
    let len = length.unwrap_or(data.as_ref().len() * 8);
    Self { data, len }
  }

  /// Returns the length of the vector, in bits.
  pub fn len(&self) -> usize {
    self.len
  }

  /// Returns `true` if the vector is of length zero
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }

  /// Gets the bit at position `index`.
  pub fn get(&self, index: usize) -> Option<bool> {
    // Bounds Check
    if index >= self.len {
      None
    } else {
      let data = self.data.as_ref();
      let (byte_num, bit_mask) = Self::index_mask(index);
      let value = data.get(byte_num)?;
      let result = value & bit_mask;
      Some(result != 0)
    }
  }

  pub fn borrow(&self) -> BitVector<&[u8]> {
    BitVector {
      data: self.data.as_ref(),
      len:  self.len(),
    }
  }

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
      end:      self.len,
    }
  }

  /// For a given bit index, return a byte index and a mask with (only) that bit set.
  #[inline(always)]
  fn index_mask(bit_index: usize) -> (usize, u8) {
    let byte_num = bit_index / 8;
    let bit_num = bit_index % 8;
    let bit_mask: u8 = 0x80u8 >> bit_num;
    (byte_num, bit_mask)
  }
}

impl<'a> BitVector<&'a [u8]> {
  pub fn iter_parsed(
    &self,
  ) -> impl Iterator<Item = bool>
       + Clone
       + ExactSizeIterator
       + DoubleEndedIterator
       + 'a {
    IterBits {
      vector:   BitVector {
        data: self.data,
        len:  self.len,
      },
      position: 0,
      end:      self.len,
    }
  }
}

impl<B> BitVector<B>
where
  B: AsRef<[u8]> + AsMut<[u8]>,
{
  /// Sets the specified bit to the provided value.
  pub fn set(&mut self, index: usize, value: bool) -> Option<()> {
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

#[cfg(feature = "alloc")]
impl BitVector<alloc::boxed::Box<[u8]>> {
  /// Creates a new bit vector sufficient to hold `num_bits` bits.  They will
  /// all be initialized to zero/false.
  pub fn new(num_bits: usize) -> Result<Self, GlyphErr> {
    let num_bytes = (num_bits + 7) / 8;

    let data: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(num_bytes).collect();
    Ok(BitVector {
      data,
      len: num_bits,
    })
  }
}

impl<B> Debug for BitVector<B>
where
  B: AsRef<[u8]>,
{
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    let mut d = f.debug_struct("BitVector");
    d.field("length", &self.len);
    if self.data.as_ref().len() <= 32 {
      d.field("bits", &ShortHexDump(self.data.as_ref(), 4));
    } else {
      d.field("bits", &HexDump(self.data.as_ref()));
    }
    d.finish()
  }
}

impl<B> ToGlyph for BitVector<B>
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
      U64::from(self.len as u64).bbwr(target, cursor)?;
      u8::bbwrs(self.data.as_ref(), target, cursor)?;
    }
    glyph_close(GlyphType::VecBool, target, offset, cursor, true)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + if self.len() > 0 {
        round_to_word(size_of::<U64>() + self.data.as_ref().len())
      } else {
        0
      }
  }
}

impl<B> AsRef<[u8]> for BitVector<B>
where
  B: AsRef<[u8]>,
{
  fn as_ref(&self) -> &[u8] {
    self.data.as_ref()
  }
}

#[derive(Clone)]
struct IterBits<B>
where
  B: AsRef<[u8]>,
{
  vector:   BitVector<B>,
  position: usize,
  end:      usize,
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

impl<B> ExactSizeIterator for IterBits<B>
where
  B: AsRef<[u8]>,
{
  fn len(&self) -> usize {
    self.vector.len - self.position
  }
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

impl<'a> FromGlyph<ParsedGlyph<'a>> for BitVector<&'a [u8]> {
  fn from_glyph(source: ParsedGlyph<'a>) -> Result<Self, GlyphErr> {
    source.header_parsed().confirm_type(GlyphType::VecBool)?;
    let content = source.content_parsed();
    if content.len() == 0 {
      Ok(BitVector { data: &[], len: 0 })
    } else {
      let cursor = &mut 0;
      let num_bits: u64 = U64::bbrd(source.content_padded(), cursor)?.into();
      let num_bytes = (num_bits + 7) / 8;
      let buf = u8::bbrfs(content, cursor, num_bytes as usize)?;

      // Don't need to zero because we're just going to overwrite every byte.
      let result = BitVector {
        data: buf,
        len:  num_bits as usize,
      };
      Ok(result)
    }
  }
}

/// A glyph containing a dense (8 bits per byte) bit vector.
pub struct BitVecGlyph<G: Glyph> {
  // SAFETY: bit_vector references this.
  #[allow(dead_code)]
  glyph:      G,
  // The &'static [u8] is an internal self-reference to the glyph's content.
  bit_vector: BitVector<&'static [u8]>,
}

impl<G: Glyph> BitVecGlyph<G> {
  pub fn bit_vector(&self) -> &BitVector<&'_ [u8]> {
    &self.bit_vector
  }
}

impl<'a> BitVecGlyph<ParsedGlyph<'a>> {
  pub fn bit_vector_parsed(&self) -> BitVector<&'a [u8]> {
    self.bit_vector.clone()
  }
}

impl<G: Glyph> Debug for BitVecGlyph<G> {
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    let mut df = f.debug_struct("BitVectorGlyph");
    df.field("num_bits", &self.bit_vector.len());
    if self.bit_vector.as_ref().len() <= 32 {
      df.field("bits", &ShortHexDump(self.bit_vector.as_ref(), 4));
    } else {
      df.field("bits", &HexDump(self.bit_vector.as_ref()));
    }
    df.finish()
  }
}

impl<G: Glyph> FromGlyph<G> for BitVecGlyph<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::VecBool)?;
    let content = source.content_padded();

    if content.len() == 0 {
      let bit_vector = BitVector::from_bytes(&[][..], None);
      Ok(Self {
        glyph: source,
        bit_vector,
      })
    } else {
      let cursor = &mut 0;
      let num_bits: u64 = U64::bbrd(content, cursor)?.into();
      let num_bytes = (num_bits + 7) / 8;
      let buf =
        u8::bbrfs(content, cursor, num_bytes as usize)? as *const [u8];
      // SAFETY: Pinning is guaranteed by the bounds on G, just need to make sure
      // it doesn't escape this type unless bounded by the lifetime of `self`.
      let buf = unsafe { &*buf };

      // Don't need to zero because we're just going to overwrite every byte.
      let bit_vector = BitVector::from_bytes(buf, Some(num_bits as usize));
      Ok(Self {
        glyph: source,
        bit_vector,
      })
    }
  }
}

impl ToGlyph for [bool] {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    if self.len() > 0 {
      let glyph_start = GlyphHeader::skip(cursor);
      let num_bytes = round_to_word((self.len() + 7) / 8);
      U64::from(self.len() as u64).bbwr(target, cursor)?;

      // We're going to construct a mutable BitVector in place and set the bits.
      let bytes = u8::bbrfs_mut(target, cursor, num_bytes)?;
      bytes.fill(0);
      let mut bv = BitVector::from_bytes(bytes, Some(self.len()));
      for (i, bit) in self.iter().enumerate() {
        bv.set(i, *bit);
      }
      pad_to_word(target, cursor)?;
      glyph_close(GlyphType::VecBool, target, glyph_start, cursor, false)
    } else {
      GlyphHeader::new_short(GlyphType::VecBool, Default::default())
        .bbwr(target, cursor)?;
      Ok(())
    }
  }

  fn glyph_len(&self) -> usize {
    let num_bits = self.len();
    match num_bits {
      0 => size_of::<GlyphHeader>(),
      _ => {
        size_of::<GlyphHeader>()
          + size_of::<U64>()
          + round_to_word((num_bits + 7) / 8)
      },
    }
  }
}

impl<G: Glyph> PartialEq for BitVecGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Glyph> Eq for BitVecGlyph<G> {}

impl<G: Glyph> PartialOrd for BitVecGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for BitVecGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.bit_vector.cmp(&other.bit_vector)
  }
}

/// Signed integers
///
/// 32-, 64-, and 128-bit versions are supported.
///
///
///
/// ```
/// use glyphs::{glyph_new, FromGlyph};
///
/// // 32-bit encoding and decoding
/// let g = glyph_new(42i32).unwrap();
/// assert_eq!(g.as_ref().len(), 8);
/// let decoded = i32::from_glyph(g).unwrap();
/// assert_eq!(decoded, 42i32);
///
///
///
/// ```
#[derive(Copy, Clone, Debug)]
pub struct IntGlyph<G: Glyph>(G, i128);

impl<G: Glyph> FromGlyph<G> for IntGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(SignedInt)?;
    let val = if glyph.header().is_short() {
      i32::from_le_bytes(glyph.header().short_content()) as i128
    } else {
      let buf = glyph.content_padded();
      // SAFETY: Bounds checks are redundant with switching on length
      unsafe {
        if buf.len() >= size_of::<I128>() {
          I128::bbrf_u(buf, &mut 0).get()
        } else if buf.len() >= size_of::<I64>() {
          I64::bbrf_u(buf, &mut 0).get() as i128
        } else {
          0
        }
      }
    };
    Ok(Self(glyph, val))
  }
}

impl<G: Glyph> Deref for IntGlyph<G> {
  type Target = i128;

  fn deref(&self) -> &Self::Target {
    &self.1
  }
}

impl<G: Glyph> From<IntGlyph<G>> for i128 {
  fn from(value: IntGlyph<G>) -> Self {
    value.1
  }
}

impl<G: Glyph> TryFrom<IntGlyph<G>> for i64 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      i64::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<IntGlyph<G>> for i32 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      i32::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<IntGlyph<G>> for i16 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      i16::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<IntGlyph<G>> for i8 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      i8::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

pub struct UIntGlyph<G: Glyph>(G, u128);

impl<G: Glyph> FromGlyph<G> for UIntGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(UnsignedInt)?;
    let val = if glyph.header().is_short() {
      u32::from_le_bytes(glyph.header().short_content()) as u128
    } else {
      let buf = glyph.content_padded();
      // SAFETY: Bounds checks are redundant with switching on length
      unsafe {
        if buf.len() >= size_of::<U128>() {
          U128::bbrf_u(buf, &mut 0).get()
        } else if buf.len() >= size_of::<U64>() {
          U64::bbrf_u(buf, &mut 0).get() as u128
        } else {
          0
        }
      }
    };
    Ok(Self(glyph, val))
  }
}

impl<G: Glyph> Deref for UIntGlyph<G> {
  type Target = u128;

  fn deref(&self) -> &Self::Target {
    &self.1
  }
}

impl<G: Glyph> From<UIntGlyph<G>> for u128 {
  fn from(value: UIntGlyph<G>) -> Self {
    value.1
  }
}

impl<G: Glyph> TryFrom<UIntGlyph<G>> for u64 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      u64::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<UIntGlyph<G>> for u32 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      u32::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<UIntGlyph<G>> for u16 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      u16::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<UIntGlyph<G>> for u8 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      u8::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

pub struct FloatGlyph<G: Glyph>(G, f64);

impl<G: Glyph> FromGlyph<G> for FloatGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(Float)?;
    let val = if glyph.header().is_short() {
      f32::from_le_bytes(glyph.header().short_content()) as f64
    } else {
      let buf = glyph.content_padded();
      // SAFETY: Bounds checks are redundant with switching on length
      unsafe {
        if buf.len() >= size_of::<F64>() {
          F64::bbrf_u(buf, &mut 0).get()
        } else {
          0.0
        }
      }
    };
    Ok(Self(glyph, val))
  }
}

impl<G: Glyph> Deref for FloatGlyph<G> {
  type Target = f64;

  fn deref(&self) -> &Self::Target {
    &self.1
  }
}

impl<G: Glyph> From<FloatGlyph<G>> for f32 {
  fn from(value: FloatGlyph<G>) -> Self {
    value.1 as f32
  }
}

gen_prim_to_glyph!(u8, UnsignedInt, short, |src: &u8| {
  u32::from(*src).to_le_bytes()
});
gen_prim_to_glyph!(u16, UnsignedInt, short, |src: &u16| {
  u32::from(*src).to_le_bytes()
});
gen_prim_to_glyph!(u32, UnsignedInt, short, |src: &u32| { src.to_le_bytes() });
gen_prim_to_glyph!(u64, UnsignedInt, conv, U64, |src: &u64| {
  U64::from(*src)
});
gen_prim_to_glyph!(u128, UnsignedInt, conv, U128, |src: &u128| {
  U128::from(*src)
});
gen_prim_to_glyph!(i8, SignedInt, short, |src: &i8| {
  i32::from(*src).to_le_bytes()
});
gen_prim_to_glyph!(i16, SignedInt, short, |src: &i16| {
  i32::from(*src).to_le_bytes()
});
gen_prim_to_glyph!(i32, SignedInt, short, |src: &i32| { src.to_le_bytes() });
gen_prim_to_glyph!(i64, SignedInt, conv, I64, |src: &i64| { I64::from(*src) });
gen_prim_to_glyph!(i128, SignedInt, conv, I128, |src: &i128| {
  I128::from(*src)
});
gen_prim_to_glyph!(f32, Float, short, |src: &f32| { src.to_le_bytes() });
gen_prim_to_glyph!(f64, Float, conv, F64, |src: &f64| { F64::from(*src) });
gen_prim_to_glyph!(U16, UnsignedInt, short, |src: &U16| {
  u32::from(src.get()).to_le_bytes()
});
gen_prim_to_glyph!(U32, UnsignedInt, short, |src: &U32| *src.bytes());
gen_prim_to_glyph!(U64, UnsignedInt);
gen_prim_to_glyph!(U128, UnsignedInt);
gen_prim_to_glyph!(I16, SignedInt, short, |src: &I16| {
  i32::from(src.get()).to_le_bytes()
});
gen_prim_to_glyph!(I32, SignedInt, short, |src: &I32| *src.bytes());
gen_prim_to_glyph!(I64, SignedInt);
gen_prim_to_glyph!(I128, SignedInt);
gen_prim_to_glyph!(F32, Float, short, |src: &F32| { *src.bytes() });
gen_prim_to_glyph!(F64, Float);

gen_prim_slice_to_glyph!(u8);
gen_prim_slice_to_glyph!(u16, conv, U16, |src: &u16| U16::from(*src));
gen_prim_slice_to_glyph!(u32, conv, U32, |src: &u32| U32::from(*src));
gen_prim_slice_to_glyph!(u64, conv, U64, |src: &u64| U64::from(*src));
gen_prim_slice_to_glyph!(u128, conv, U128, |src: &u128| U128::from(*src));
gen_prim_slice_to_glyph!(i8);
gen_prim_slice_to_glyph!(i16, conv, I16, |src: &i16| I16::from(*src));
gen_prim_slice_to_glyph!(i32, conv, I32, |src: &i32| I32::from(*src));
gen_prim_slice_to_glyph!(i64, conv, I64, |src: &i64| I64::from(*src));
gen_prim_slice_to_glyph!(i128, conv, I128, |src: &i128| I128::from(*src));
gen_prim_slice_to_glyph!(f32, conv, F32, |src: &f32| F32::from(*src));
gen_prim_slice_to_glyph!(f64, conv, F64, |src: &f64| F64::from(*src));
gen_prim_slice_to_glyph!(U16);
gen_prim_slice_to_glyph!(U32);
gen_prim_slice_to_glyph!(U64);
gen_prim_slice_to_glyph!(U128);
gen_prim_slice_to_glyph!(I16);
gen_prim_slice_to_glyph!(I32);
gen_prim_slice_to_glyph!(I64);
gen_prim_slice_to_glyph!(I128);
gen_prim_slice_to_glyph!(F32);
gen_prim_slice_to_glyph!(F64);

gen_prim_from_glyph!(u8, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<G>| {
  u8::try_from(*gl)
});
gen_prim_from_glyph!(u16, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<G>| {
  u16::try_from(*gl)
});
gen_prim_from_glyph!(u32, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<G>| {
  u32::try_from(*gl)
});
gen_prim_from_glyph!(u64, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<G>| {
  u64::try_from(*gl)
});
gen_prim_from_glyph!(u128, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<G>| {
  u128::try_from(*gl)
});
gen_prim_from_glyph!(i8, try_conv_glyph, IntGlyph, |gl: IntGlyph<G>| {
  i8::try_from(*gl)
});
gen_prim_from_glyph!(i16, try_conv_glyph, IntGlyph, |gl: IntGlyph<G>| {
  i16::try_from(*gl)
});
gen_prim_from_glyph!(i32, try_conv_glyph, IntGlyph, |gl: IntGlyph<G>| {
  i32::try_from(*gl)
});
gen_prim_from_glyph!(i64, try_conv_glyph, IntGlyph, |gl: IntGlyph<G>| {
  i64::try_from(*gl)
});
gen_prim_from_glyph!(i128, try_conv_glyph, IntGlyph, |gl: IntGlyph<G>| {
  i128::try_from(*gl)
});
gen_prim_from_glyph!(f32, conv_glyph, FloatGlyph, |gl: FloatGlyph<G>| {
  (*gl) as f32
});
gen_prim_from_glyph!(f64, conv_glyph, FloatGlyph, |gl: FloatGlyph<G>| { *gl });
gen_prim_from_glyph!(U32, conv, u32, |val| { U32::from(val) });
gen_prim_from_glyph!(U64, conv, u64, |val| { U64::from(val) });
gen_prim_from_glyph!(U128, conv, u128, |val| { U128::from(val) });
gen_prim_from_glyph!(I32, conv, i32, |val| { I32::from(val) });
gen_prim_from_glyph!(I64, conv, i64, |val| { I64::from(val) });
gen_prim_from_glyph!(I128, conv, i128, |val| { I128::from(val) });
gen_prim_from_glyph!(F32, conv, f32, |val| { F32::from(val) });
gen_prim_from_glyph!(F64, conv, f64, |val| { F64::from(val) });

gen_prim_slice_from_glyph_parsed!(u8);
gen_prim_slice_from_glyph_parsed!(U16, le_native, u16);
gen_prim_slice_from_glyph_parsed!(U32, le_native, u32);
gen_prim_slice_from_glyph_parsed!(U64, le_native, u64);
gen_prim_slice_from_glyph_parsed!(U128);
gen_prim_slice_from_glyph_parsed!(i8);
gen_prim_slice_from_glyph_parsed!(I16, le_native, i16);
gen_prim_slice_from_glyph_parsed!(I32, le_native, i32);
gen_prim_slice_from_glyph_parsed!(I64, le_native, i64);
gen_prim_slice_from_glyph_parsed!(I128);
gen_prim_slice_from_glyph_parsed!(F32, le_native, f32);
gen_prim_slice_from_glyph_parsed!(F64, le_native, f64);

impl<'a> FromGlyph<ParsedGlyph<'a>> for &'a str {
  fn from_glyph(source: ParsedGlyph<'a>) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::StringUTF8)?;
    let str_bytes = source.content_parsed();
    let valid_str = from_utf8(str_bytes)?;
    Ok(valid_str)
  }
}

impl ToGlyph for str {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    // SAFETY: So we can do one bounds check.
    unsafe {
      let str_bytes = self.as_bytes();
      let header = GlyphHeader::new(GlyphType::StringUTF8, str_bytes.len())?;
      let bounds =
        round_to_word(*cursor + size_of::<GlyphHeader>() + str_bytes.len());
      bounds_check(target, bounds)?;
      let mut zero_idx = bounds - 8;
      U64::from(0).bbwr_u(target, &mut zero_idx);
      header.bbwr_u(target, cursor);
      u8::bbwrs_u(str_bytes, target, cursor);
      *cursor = round_to_word(*cursor);
      // pad_to_word_u(target, cursor);
    }
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    round_to_word(size_of::<GlyphHeader>() + self.len())
  }
}

#[cfg(feature = "alloc")]
impl<G> FromGlyph<G> for alloc::string::String
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::StringUTF8)?;
    let bytes = source.content();
    let bytes_v = u8::bbrds_i(bytes, &mut 0)?;
    let valid_string = alloc::string::String::from_utf8(bytes_v)?;
    Ok(valid_string)
  }
}

#[cfg(feature = "alloc")]
impl ToGlyph for alloc::string::String {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    self.as_str().glyph_encode(target, cursor)
  }

  fn glyph_len(&self) -> usize {
    self.as_str().glyph_len()
  }
}

/// A glyph containing a valid UTF-8 string.
pub struct StringGlyph<G>(G)
where
  G: Glyph;

impl<G> StringGlyph<G>
where
  G: Glyph,
{
  /// The string contained in the glyph.
  pub fn get(&self) -> &str {
    let bytes = self.0.content();
    // Validity was already checked during `glyph_decode`.
    unsafe { core::str::from_utf8_unchecked(bytes) }
  }
}

impl<G> Debug for StringGlyph<G>
where
  G: Glyph,
{
  fn fmt(&self, f: &mut Formatter) -> Result<(), core::fmt::Error> {
    write!(f, "Utf8Glyph(\"{}\")", self.get())
  }
}

impl<G> FromGlyph<G> for StringGlyph<G>
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::StringUTF8)?;
    // Check for valid UTF-8 string.
    let _ = from_utf8(source.content())?;
    Ok(StringGlyph(source))
  }
}

impl<G: Glyph> PartialEq for StringGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.get() == other.get()
  }
}

impl<G: Glyph> Eq for StringGlyph<G> {}

impl<G: Glyph> PartialOrd for StringGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for StringGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    let a = self.get();
    let b = other.get();
    a.cmp(b)
  }
}

impl<G> FromGlyph<G> for char
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::UnicodeChar)?;
    let value: u32 =
      U32::bbrd(&source.header().short_content()[..], &mut 0)?.into();
    match char::try_from(value) {
      Ok(c) => Ok(c),
      Err(_err) => Err(GlyphErr::IllegalValue),
    }
  }
}

impl ToGlyph for char {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let value = unsafe { core::mem::transmute::<&char, &[u8; 4]>(&self) };
    GlyphHeader::new_short(GlyphType::UnicodeChar, *value)
      .bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

/// A glyph containing a unicode character `char`.
pub struct CharGlyph<G: Glyph>(G);

impl<G: Glyph> CharGlyph<G> {
  /// The `char` contained by this glyph.
  pub fn get(&self) -> char {
    let bytes = self.0.header().short_content();
    // SAFETY: A valid value was confirmed when the CharGlyph was created.
    unsafe { char::from_u32_unchecked(u32::from_le_bytes(bytes)) }
  }
}

impl<G: Glyph> FromGlyph<G> for CharGlyph<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::UnicodeChar)?;
    // Check for valid unicode char.
    let _value = <char>::from_glyph(source.borrow())?;
    Ok(CharGlyph(source))
  }
}

impl<G: Glyph> Debug for CharGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "CharGlyph({:?})", self.get())
  }
}

impl<G: Glyph> PartialEq for CharGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.get() == other.get()
  }
}

impl<G: Glyph> Eq for CharGlyph<G> {}

impl<G: Glyph> PartialOrd for CharGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for CharGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.get().cmp(&other.get())
  }
}

#[cfg(feature = "alloc")]
#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    glyph_new, glyph_read,
    util::{simple_codec_slice_test, simple_codec_test, BENCH_BUF_SIZE},
    FromGlyph, Glyph, GlyphErr,
  };
  use ::test::Bencher;
  use alloc::boxed::Box;
  use std::{dbg, hint::black_box, iter::repeat, string::String};

  #[test]
  fn codec_basic() -> Result<(), GlyphErr> {
    //== Simple Scalar Values ==/
    simple_codec_test(());
    simple_codec_test(Unknown);
    simple_codec_test(Redacted);
    simple_codec_test(Option::<u32>::None);
    simple_codec_test(Option::<u32>::Some(0xDEAD_BEEF));
    simple_codec_test(42u8);
    simple_codec_test(0xF00Du16);
    simple_codec_test(0xDEADBEEFu32);
    simple_codec_test(0xF00DDEADBEEFF00Du64);
    simple_codec_test(0x0102030405060708090A0B0C0D0E0Fu128);
    simple_codec_test(-8i8);
    simple_codec_test(-16i16);
    simple_codec_test(-32i32);
    simple_codec_test(-64i64);
    simple_codec_test(-128i128);

    //== Simple Slices ==/
    simple_codec_slice_test::<3, u8, u8>(42u8);
    simple_codec_slice_test::<3, u16, U16>(0xF00D);
    simple_codec_slice_test::<3, u32, U32>(0xDEAD_BEEF);
    simple_codec_slice_test::<3, u64, U64>(0xF00DDEADBEEFF00D);
    simple_codec_slice_test::<3, u128, U128>(123);
    simple_codec_slice_test::<3, i8, i8>(-1);
    simple_codec_slice_test::<3, i16, I16>(-1);
    simple_codec_slice_test::<3, i32, I32>(-1);
    simple_codec_slice_test::<3, i64, I64>(-1);
    simple_codec_slice_test::<3, i128, I128>(-1234);
    simple_codec_slice_test::<3, f32, F32>(core::f32::consts::E);
    simple_codec_slice_test::<3, f64, F64>(core::f64::consts::E);

    //== Bit Vector ==/
    let mut bv = BitVector::new(100).unwrap();
    for i in 0..100 {
      bv.set(i, (i % 3) == 0).unwrap();
    }
    let bvg = glyph_new(&bv).unwrap();
    let decoded = BitVector::<&[u8]>::from_glyph(bvg.borrow()).unwrap();
    assert_eq!(bv.as_ref(), decoded.as_ref());

    Ok(())
  }

  macro_rules! gen_bench {
    ($enc_bench_name:ident, $dec_bench_name:ident, $prim:ty) => {
      #[bench]
      fn $enc_bench_name(b: &mut Bencher) -> Result<(), $crate::GlyphErr> {
        let mut buf: Box<[u8]> = repeat(0).take(BENCH_BUF_SIZE).collect();

        // let mut buf =
        //   $crate::buffers::ByteBuffer::new(BENCH_BUF_SIZE, true).unwrap();
        let value: $prim = Default::default();

        // Write the buffer
        b.bytes = BENCH_BUF_SIZE as u64;
        b.iter(|| {
          let cursor = &mut 0;
          loop {
            $crate::ToGlyph::glyph_encode(&value, buf.as_mut(), cursor)?;
          }
          #[allow(unreachable_code)]
          Result::<(), $crate::GlyphErr>::Ok(())
        });
        let _ = black_box(buf);
        Ok(())
      }

      #[bench]
      fn $dec_bench_name(b: &mut Bencher) -> Result<(), $crate::GlyphErr> {
        let mut buf: alloc::boxed::Box<[u8]> =
          core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
        // let mut buf = ByteBuffer::new(BENCH_BUF_SIZE, true).unwrap();
        let value: $prim = Default::default();

        // Write the buffer
        let cursor = &mut 0;
        while *cursor
          <= BENCH_BUF_SIZE
            - size_of::<$prim>()
            - size_of::<$crate::GlyphHeader>()
        {
          $crate::ToGlyph::glyph_encode(&value, buf.as_mut(), cursor)?;
        }

        // Read all the glyphs from the buffer
        b.bytes = BENCH_BUF_SIZE as u64;
        b.iter(|| {
          let cursor = &mut 0;
          loop {
            let glyph = $crate::glyph_read(&buf, cursor)?;
            let _decoded = <$prim>::from_glyph(glyph)?;
          }
          #[allow(unreachable_code)]
          Ok::<(), $crate::GlyphErr>(())
        });
        Ok(())
      }
    };
  }

  gen_bench!(enc_glyph_u8, dec_glyph_u8, u8);
  gen_bench!(enc_glyph_u16, dec_glyph_u16, u16);
  gen_bench!(enc_glyph_u32, dec_glyph_u32, u32);
  gen_bench!(enc_glyph_u64, dec_glyph_u64, u64);

  #[bench]
  fn dec_basic_glyph_i32(b: &mut Bencher) -> Result<(), GlyphErr> {
    let mut buf: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
    let value: i32 = 1;

    // Write the buffer
    let cursor = &mut 0;
    while *cursor <= BENCH_BUF_SIZE - size_of::<i32>() {
      value.glyph_encode(buf.as_mut(), cursor).unwrap();
    }

    dbg!(&HexDump(buf.as_ref()));

    let mut outside = 0i128;

    // Read all the glyphs from the buffer
    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      loop {
        let glyph = glyph_read(&buf, cursor)?;
        let decoded = IntGlyph::from_glyph(glyph)?;
        outside = *decoded;
      }
      #[allow(unreachable_code)]
      Ok::<(), GlyphErr>(())
    });
    Ok(())
  }

  #[test]
  fn codec_glyph_str() -> Result<(), GlyphErr> {
    // Basic encoding
    let text = "hunter2";
    let glyph = glyph_new(text)?;
    dbg!(&glyph);

    let read_str = <&str>::from_glyph(glyph.borrow())?;
    assert_eq!(read_str, text);

    let read_string = String::from_glyph(glyph.borrow())?;
    assert_eq!(read_string.as_str(), text);

    let str_glyph = StringGlyph::from_glyph(glyph.borrow())?;
    assert_eq!(str_glyph.get(), text);

    Ok(())
  }

  #[bench]
  fn enc_glyph_str(b: &mut Bencher) -> Result<(), GlyphErr> {
    let mut buf: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
    let value = "My xenoscience studies range from urban to agrarian, \
                 I am the very model of a scientist Salarian!";

    let target = buf.as_mut();
    let glyph = glyph_new(value)?;
    let iterations = BENCH_BUF_SIZE / glyph.glyph_len();

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      loop {
        value.glyph_encode(target, cursor)?
      }
      #[allow(unreachable_code)]
      Result::<(), GlyphErr>::Ok(())
    });

    let cursor = &mut 0;
    for _ in 0..iterations {
      let glyph = glyph_read(&buf, cursor)?;
      let as_read = <&str>::from_glyph(glyph)?;
      assert_eq!(value, as_read);
    }
    Ok(())
  }

  #[bench]
  fn dec_glyph_str(b: &mut Bencher) -> Result<(), GlyphErr> {
    let mut buf: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
    let value = "My xenoscience studies range from urban to agrarian, \
                 I am the very model of a scientist Salarian!";

    let glyph = glyph_new(value)?;
    let iterations = BENCH_BUF_SIZE / glyph.glyph_len();

    let cursor = &mut 0;
    for _ in 0..iterations {
      value.glyph_encode(buf.as_mut(), cursor)?;
    }

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      for _ in 0..iterations {
        let glyph = glyph_read(&buf, cursor)?;
        let _ = <&str>::from_glyph(glyph)?;
      }
      Ok::<(), GlyphErr>(())
    });
    Ok(())
  }

  #[test]
  fn codec_glyph_char() {
    let value = 'K';
    let glyph = glyph_new(&value).unwrap();
    let as_read = char::from_glyph(glyph).unwrap();
    assert_eq!(value, as_read);
  }

  #[bench]
  fn enc_glyph_char(b: &mut Bencher) {
    let mut buf: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
    let value = 'K';

    let glyph = glyph_new(&value).unwrap();
    let iterations = BENCH_BUF_SIZE / glyph.glyph_len();

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      loop {
        value.glyph_encode(buf.as_mut(), cursor)?
      }
      #[allow(unreachable_code)]
      Ok::<(), GlyphErr>(())
    });

    let cursor = &mut 0;
    for _ in 0..iterations {
      let glyph = glyph_read(&buf, cursor).unwrap();
      let as_read = char::from_glyph(glyph).unwrap();
      assert_eq!(value, as_read);
    }
  }

  #[bench]
  fn dec_glyph_char(b: &mut Bencher) {
    let mut buf: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
    let value = 'K';

    let glyph = glyph_new(&value).unwrap();
    let iterations = BENCH_BUF_SIZE / glyph.glyph_len();

    let cursor = &mut 0;
    for _ in 0..iterations {
      value.glyph_encode(buf.as_mut(), cursor).unwrap();
    }

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      for _ in 0..iterations {
        let glyph = glyph_read(&buf, cursor)?;
        let _ = char::from_glyph(glyph)?;
      }
      Ok::<(), GlyphErr>(())
    });
  }

  #[bench]
  fn validate_utf8(b: &mut Bencher) {
    let value = b"My xenoscience studies range from urban to agrarian, \
               I am the very model of a scientist Salarian!";

    let iterations = BENCH_BUF_SIZE / value.len();

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let mut sum: u64 = 0;
      for _ in 0..iterations {
        let as_str = from_utf8(&value[..])?;
        sum += as_str.as_bytes()[0] as u64;
      }
      Ok::<u64, core::str::Utf8Error>(sum)
    })
  }
}
