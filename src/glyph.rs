#[cfg(feature = "alloc")]
use alloc::string::FromUtf8Error;

use crate::{
  crypto::{CryptographicHash, GlyphHash},
  util::debug::{HexDump, ShortHexDump},
  zerocopy::{
    bounds_check, pad_to_word, round_to_word, ArcGlyphBuf,
    ArcGlyphBufFinalized, ArcGlyphBufUninit, GlyphAlloc, HasZeroCopyID,
    ZeroCopy, ZeroCopyTypeID, U16, U32,
  },
};
use alloc::{alloc::AllocError, boxed::Box, sync::Arc};
use core::{
  fmt::{Debug, Display, Formatter},
  mem::size_of,
  num::TryFromIntError,
  ptr::NonNull,
  slice::from_raw_parts,
  str::Utf8Error,
};

/// The common header for every glyph.
///
/// The format is documented [here](http://www.glifs.org/docs/books/format/general.html).
#[repr(C)]
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct GlyphHeader {
  flags:    u8,
  reserved: u8,
  type_id:  [u8; 2],
  len_data: [u8; 4],
}

unsafe impl ZeroCopy for GlyphHeader {}

impl GlyphHeader {
  /// If set, this is a long glyph.
  const LONG_BIT: u8 = 0b0000_1000;
  /// The maximum content length that can be expressed in a glyph header.
  const MAX_CONTENT_LEN: u64 = (u32::MAX as u64) << 3;
  /// Bits to store the number of padding bytes at the end of a glyph.
  ///
  /// Useful primarily for UTF-8 strings and other types which can have an
  /// arbitrary byte length.
  const PADDING_BITS: u8 = 0b0000_0111;
  /// Bits to store the glyph version, for future compatibility.  Currently,
  /// these bits must be zero.
  const VERSION_BITS: u8 = 0b1111_0000;

  /// Creates a new glyph header, containing content_len bytes.
  ///
  /// The caller must ensure that `content_len <= GLYPH_MAX_CONTENT_LEN`, or
  /// the resulting header will not be inaccurate (as longer lengths cannot be
  /// represented in the existing format).
  #[inline]
  pub const fn new(
    glyph_type: GlyphType,
    content_len: usize,
  ) -> Result<GlyphHeader, GlyphErr> {
    if content_len as u64 <= Self::MAX_CONTENT_LEN {
      let padded_len = (content_len + 7) & !7;
      let padding = padded_len - content_len; // always 0-7.
      let flags = (padding as u8) | Self::LONG_BIT; // ver0, long, padding
      let word_len = (padded_len >> 3) as u32;
      Ok(GlyphHeader {
        flags,
        reserved: 0,
        type_id: (glyph_type as u16).to_le_bytes(),
        len_data: word_len.to_le_bytes(),
      })
    } else {
      Err(GlyphErr::GlyphLenOverflow(content_len))
    }
  }

  /// Creates a new header for a short glyph, with the content fully specified.
  pub const fn new_short(
    glyph_type: GlyphType,
    content: [u8; 4],
  ) -> GlyphHeader {
    GlyphHeader {
      flags:    0, // ver0, padding0, long0
      reserved: 0,
      type_id:  (glyph_type as u16).to_le_bytes(),
      len_data: content,
    }
  }

  /// Returns the GLIFS version specified in the header.
  #[inline(always)]
  pub const fn version(self) -> u8 {
    (self.flags & Self::VERSION_BITS) >> 4
  }

  /// Returns the numerical glyph type id.  See [`GlyphType`].
  #[inline(always)]
  pub fn glyph_type(self) -> GlyphType {
    unsafe {
      let id = u16::from_le_bytes(self.type_id);
      core::mem::transmute::<u16, GlyphType>(id)
    }
  }

  /// Returns `GlyphErr::UnexpectedType` if the header's type does not match
  /// the provided `type_id`.
  #[inline]
  pub fn confirm_type(self, type_id: GlyphType) -> Result<(), GlyphErr> {
    let id = u16::from_le_bytes(self.type_id);
    if (type_id as u16) == id {
      Ok(())
    } else {
      Err(err!(
        trace,
        GlyphErr::UnexpectedType {
          expected_type_id: type_id as u16,
          observed_type_id: id,
        }
      ))
    }
  }

  /// Returns `true` iff this header describes a short glyph.
  #[inline(always)]
  pub const fn is_short(self) -> bool {
    (self.flags & Self::LONG_BIT) == 0
  }

  #[inline(always)]
  pub const fn content_len(self) -> usize {
    let len_factor = (self.flags & Self::LONG_BIT) as u64;
    let content_words = u32::from_le_bytes(self.len_data) as u64;
    (content_words * len_factor) as usize
  }

  pub const fn padding(self) -> usize {
    (self.flags & Self::PADDING_BITS) as usize
  }

  /// Returns the length of the glyph, in bytes, including the header.
  #[inline(always)]
  pub fn glyph_len(self) -> usize {
    size_of::<GlyphHeader>() + self.content_len()
  }

  #[inline(always)]
  pub fn short_content(self) -> [u8; 4] {
    self.len_data
  }

  #[inline(always)]
  pub fn short_content_ref(&self) -> &[u8; 4] {
    &self.len_data
  }

  /// Advances the cursor by the size of the header and returns the position
  /// at which it would have been written.
  ///
  /// ```
  /// use glyphs::GlyphHeader;
  ///
  /// let cursor = &mut 8usize;
  /// let offset = GlyphHeader::skip(cursor);
  /// assert_eq!(offset, 8);
  /// assert_eq!(*cursor, 16);
  ///
  /// ```
  pub fn skip(cursor: &mut usize) -> usize {
    let glyph_start = *cursor;
    *cursor += size_of::<Self>();
    glyph_start
  }
}

impl Debug for GlyphHeader {
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    let mut builder = f.debug_struct("GlyphHeader");
    builder.field("version", &format_args!("0x{:X}", self.version()));
    builder.field("type", &self.glyph_type());
    builder.field("type_id", &format_args!("0x{:X}", self.glyph_type() as u16));
    builder.field("short", &self.is_short());
    if self.is_short() {
      builder.field("content", &ShortHexDump(&self.len_data, 4));
    } else {
      builder.field("content_length", &self.content_len());
    }
    builder.finish()
  }
}

/// Describes an offset in a glyph at which some other data is present.
#[repr(transparent)]
#[derive(Copy, Clone, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct GlyphOffset(U32);

/// Safety: All components are also `ZeroCopy`
unsafe impl ZeroCopy for GlyphOffset {}

impl HasZeroCopyID for GlyphOffset {
  const ZERO_COPY_ID: ZeroCopyTypeID = ZeroCopyTypeID::GlyphOffset;
}

impl GlyphOffset {
  pub fn new(start: usize, position: usize) -> Result<Self, GlyphErr> {
    if (start % 8 != 0) || (position % 8 != 0) {
      return Err(err!(
        error,
        GlyphErr::GlyphOffsetInvalid { start, position }
      ));
    }

    let len = position.saturating_sub(start);
    let len_words = u32::try_from(len / 8)?;
    Ok(Self(len_words.into()))
  }

  /// Generate a cursor an offset number of bytes past `start`.
  pub fn cursor(&self, start: usize) -> usize {
    let words: usize = self.0.get() as usize;
    let bytes = words * 8;
    start + bytes
  }

  // TODO: Revise glyph_encode functions to use this rather than doing it
  //       manually each time.
  pub(crate) fn skip(
    target: &mut [u8],
    cursor: &mut usize,
    num: usize,
    zero_pad: bool,
  ) -> Result<usize, GlyphErr> {
    let offsets_cursor = *cursor;
    let offsets_len = size_of::<Self>().saturating_mul(num);
    *cursor = (*cursor).saturating_add(offsets_len);
    if zero_pad {
      pad_to_word(target, cursor)?;
    }
    Ok(offsets_cursor)
  }

  /// Returns the length of an offsets table with the specified number of items.
  ///
  /// This will be equal to the number of items, multiplied by the size of a
  /// `GlyphOffset`, and rounded to the nearest word.
  // TODO: Revise glyph_len functions to use this rather than doing it manually
  pub(crate) fn table_len(num_items: usize) -> usize {
    round_to_word(size_of::<Self>().saturating_mul(num_items))
  }
}

impl Debug for GlyphOffset {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "GlyphOffset(0x{:x} bytes)", self.cursor(0))
  }
}

/// Semi-structured data designed to be read without deserialization.
/* === IMPORTANT: SAFETY ===

While there is relatively little unsafe code in the Glyph type itself, other
unsafe code relies on a few invariants which must be maintained:

- The contents of a glyph, once created, must remain immutable.
- The underlying buffer must be at least `size_of::<GlyphHeader>()` bytes long.
- The first `size_of::<GlyphHeader>()` bytes must actually contain this header.
- The length specified by the header must not overflow the bounds of the
  underlying buffer.
- The underlying buffer _MUST BE PINNED_.

Let's discuss this last restriction in more detail.  In other words, the
underlying buffer's memory allocation must remain valid and unchanged until the
Glyph goes out of scope.

Note that this restriction prevents the existence of a `Glyph<[u8; N]>`, as
moving this type (e.g., by returning it from a function) would move the
underlying buffer (an array) to a different location on the stack.  This would,
in turn, invalidate various internal self-referenced pointers to zero-copy
types, which would still refer to the original allocation.

If you need to work with Glyph data on the stack, you'll need to create an
array and a `Glyph<&'a [u8]>` separately.  This will let you pass the glyph
down the stack, but not back up any further than the stack frame in which the
buffer was created--rust won't allow this because the lifetime of the reference
to the array would no longer be valid.

*/
// TOOD: Transfer safety information to this doc comment.
pub unsafe trait Glyph: AsRef<[u8]> + Debug + ToGlyph {
  #[inline(always)]
  fn content_padded(&self) -> &[u8] {
    let glyph_bytes = self.as_ref();
    // SAFETY: Bounds were checked once upon creation.
    unsafe { glyph_bytes.get_unchecked(size_of::<GlyphHeader>()..) }
  }

  /// Returns the glyph's content bytes, not including padding.
  ///
  /// ```
  /// use glyphs::*;
  ///
  /// let message = "Hello, World!";
  /// let glyph = glyph_new(message).unwrap();
  /// println!("Glyph encoded as: {:?}", &glyph);
  /// assert_eq!(glyph.content(), message.as_bytes());
  /// ```
  #[inline(always)]
  fn content(&self) -> &[u8] {
    let content_padded = self.content_padded();
    let padding = self.header().padding();
    let end = content_padded.len().saturating_sub(padding);
    // SAFETY: Bounds were checked once upon creation.
    unsafe { content_padded.get_unchecked(..end) }
  }

  /// Returns the content of short glyphs.
  ///
  /// If this is not a short glyph, this function will return the glyph's
  /// length bytes (a little-endian u32).
  #[inline(always)]
  fn short_content(&self) -> [u8; 4] {
    self.header().short_content()
  }

  /// The header for this glyph
  #[inline(always)]
  fn header(&self) -> &GlyphHeader {
    // SAFETY: Bounds already checked once upon creation
    unsafe { GlyphHeader::bbrf_u(self.as_ref(), &mut 0) }
  }

  /// Returns the total length of the glyph, in bytes.
  #[inline(always)]
  fn len(&self) -> usize {
    self.as_ref().len()
  }

  #[inline(always)]
  fn glyph_type(&self) -> GlyphType {
    let id = u16::from_le_bytes(self.header().type_id);
    id.into()
  }

  #[inline(always)]
  fn confirm_type(&self, glyph_type: GlyphType) -> Result<(), GlyphErr> {
    self.header().confirm_type(glyph_type)
  }

  /// Confirms this is a valid and correct glyph (including bounds checking).
  fn validate(&self) -> Result<(), GlyphErr> {
    let buffer = self.as_ref();
    let _ = glyph_read(buffer, &mut 0)?;
    Ok(())
  }

  fn borrow(&self) -> ParsedGlyph<'_> {
    let glyph_bytes = self.as_ref();
    ParsedGlyph { glyph_bytes }
  }

  fn glyph_hash(&self) -> GlyphHash {
    GlyphHash::new(self.as_ref())
  }

  /// Returns a glyph referencing the same bytes but with a(n unsafe) 'static
  /// lifetime useful for, e.g., internal self-references.
  ///
  /// Note that the returned glyph is _not_ bound by Rust's lifetime rules, and
  /// is thus not protected by them.  Allowing the resulting glyph to escape
  /// outside of a closely-guarded API and into user code will quickly lead
  /// to undefined behavior.
  ///
  /// This type is primarily intended for use in internal self-references, which
  /// currently (AFAIK) cannot be represented within Rust's lifetimes system.
  unsafe fn detach(self) -> ParsedGlyph<'static>
  where
    Self: Sized,
  {
    let glyph_bytes = NonNull::from(self.as_ref());
    ParsedGlyph {
      glyph_bytes: glyph_bytes.as_ref(),
    }
  }

  /// Copy this glyph to a new buffer on the heap.
  fn copy(&self) -> Result<BoxGlyph, GlyphErr> {
    // SAFETY: Since we're copying from something that's already a `Glyph`,
    //         the buffer has already been checked.
    let mut b = BoxGlyph::new_buffer(self.len())?;
    b.as_mut().copy_from_slice(self.as_ref());
    Ok(BoxGlyph(b))
  }
}

/// A glyph parsed from a byte buffer
#[derive(Clone, Copy)]
pub struct ParsedGlyph<'a> {
  glyph_bytes: &'a [u8],
}

impl<'a> ParsedGlyph<'a> {
  pub fn header_parsed(&self) -> &'a GlyphHeader {
    unsafe { GlyphHeader::bbrf_u(self.glyph_bytes, &mut 0) }
  }

  pub fn content_parsed(&self) -> &'a [u8] {
    // TODO: Document safety, potentially simplify?
    let content = NonNull::from(self.content());
    unsafe { content.as_ref() }
  }

  // TODO: Document safety, potentially simplify?
  pub fn content_padded_parsed(&self) -> &'a [u8] {
    let content_padded = NonNull::from(self.content_padded());
    unsafe { content_padded.as_ref() }
  }
}

unsafe impl<'a> Glyph for ParsedGlyph<'a> {}

impl<'a> ToGlyph for ParsedGlyph<'a> {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    u8::bbwrs(self.glyph_bytes, target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    self.glyph_bytes.len()
  }
}

impl<'a> AsRef<[u8]> for ParsedGlyph<'a> {
  fn as_ref(&self) -> &[u8] {
    self.glyph_bytes
  }
}

impl<'a> Debug for ParsedGlyph<'a> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    glyph_debug(self, f)
  }
}

/// A pointer to a [`Glyph`].
///
/// A `GlyphPtr` is just a pointer to a glyph somewhere in memory.  It's
/// typically used for an internal self-reference
#[derive(Clone, Copy)]
pub struct GlyphPtr(NonNull<[u8]>);

impl GlyphPtr {
  /// Creates a new pointer from a [`ParsedGlyph`].
  pub fn from_parsed(parsed: ParsedGlyph) -> Self {
    GlyphPtr(NonNull::from(parsed.as_ref()))
  }

  /// Dereference the pointer into a [`ParsedGlyph`].
  pub unsafe fn deref<'a>(self) -> ParsedGlyph<'a> {
    ParsedGlyph {
      glyph_bytes: self.0.as_ref(),
    }
  }
}

#[cfg(feature = "alloc")]
#[derive(Clone, Copy, Debug)]
struct GlyphAlloc;

#[cfg(feature = "alloc")]
unsafe impl Allocator for GlyphAlloc {
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
    Global.allocate(layout.align_to(8).unwrap())
  }

  unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
    Global.deallocate(ptr, layout.align_to(8).unwrap())
  }
}

/// For glyphs stored separately on the heap, we maintain a header that
/// header memoizing its [`GlyphHash`].
#[cfg(feature = "alloc")]
#[derive(Clone, Default)]
struct HeapGlyphHeader {
  glyph_hash: MemoizedInvariant<GlyphHash>,
}

/// A buffer used to write glyphs on the heap.
///
/// `BoxGlyphBuf` is responsible for creating and managing a glyph buffer stored
/// on the heap. It ensures proper alignment and memory safety during glyph
/// creation, modification, and finalization. The buffer is initialized with
/// space for both the glyph's contents and its corresponding metadata,
/// including memoization for the [`GlyphHash`].
///
/// # Examples
///
/// Creating a new unsigned integer glyph from a `u64`.
///
/// ```
/// use glyphs::{BoxGlyphBuf, FromGlyph, GlyphHeader, GlyphType, ToGlyph};
/// use glyphs::zerocopy::{ZeroCopy, U64};
///
/// let header = GlyphHeader::new(GlyphType::UnsignedInt, 8).unwrap();
/// let value = U64::from(0xDEAD_BEEF_DEAD_BEEF);
///
/// let mut glyph_buf = BoxGlyphBuf::new(value.glyph_len())
///                       .expect("Failed to create buffer");
/// let mut cursor = 0usize;
/// header.bbwr(glyph_buf.as_mut(), &mut cursor).unwrap();
/// value.bbwr(glyph_buf.as_mut(), &mut cursor).unwrap();
/// let glyph = glyph_buf.finalize().unwrap();
/// let value = U64::from_glyph(glyph).unwrap().get();
/// assert_eq!(value, 0xDEAD_BEEF_DEAD_BEEF);
/// ```
#[cfg(feature = "alloc")]
pub struct BoxGlyphBuf(Box<[u8], GlyphAlloc>);

#[cfg(feature = "alloc")]
impl BoxGlyphBuf {
  /// Creates a new buffer on the heap of size `length` for a [`BoxGlyph`].
  pub fn new(length: usize) -> Result<Self, GlyphErr> {
    if length % 8 != 0 {
      return Err(GlyphErr::GlyphLenUnaligned(length));
    };

    unsafe {
      let mut b = Box::<[u8], GlyphAlloc>::try_new_uninit_slice_in(
        size_of::<HeapGlyphHeader>() + length,
        GlyphAlloc,
      )?
      .assume_init();
      let ptr = b.as_mut_ptr();
      let hgh = transmute::<_, *mut HeapGlyphHeader>(ptr);
      hgh.write(Default::default());
      Ok(BoxGlyphBuf(b))
    }
  }

  /// Sets the glyph hash if it is already known.
  ///
  /// In situations where the glyph hash is already known (e.g., from message
  /// authentication in decryption), it can be set here to avoid future
  /// computation.
  pub fn set_known_hash(&mut self, hash: &GlyphHash) {
    unsafe {
      let ptr = transmute::<_, *mut HeapGlyphHeader>(self.0.as_ref().as_ptr());
      (*ptr).glyph_hash.set(*hash);
    }
  }

  /// Finalize the buffer into a glyph, checking for a valid header & buffer.
  pub fn finalize(self) -> Result<BoxGlyph, GlyphErr> {
    // Make sure it reads correctly.
    let _ = glyph_read(self.as_ref(), &mut 0)?;
    // SAFETY: We just did the check, using unchecked version to DRY.
    unsafe { Ok(self.finalize_unchecked()) }
  }

  /// Finalize the buffer into a glyph, skipping validity checks.
  pub unsafe fn finalize_unchecked(self) -> BoxGlyph {
    BoxGlyph(self.0)
  }
}

#[cfg(feature = "alloc")]
impl AsRef<[u8]> for BoxGlyphBuf {
  fn as_ref(&self) -> &[u8] {
    &self.0.as_ref()[size_of::<HeapGlyphHeader>()..]
  }
}

#[cfg(feature = "alloc")]
impl AsMut<[u8]> for BoxGlyphBuf {
  fn as_mut(&mut self) -> &mut [u8] {
    &mut self.0.as_mut()[size_of::<HeapGlyphHeader>()..]
  }
}

/// A glyph stored on the heap.
#[cfg(feature = "alloc")]
pub struct BoxGlyph(Box<[u8], GlyphAlloc>);

#[cfg(feature = "alloc")]
impl BoxGlyph {
  /// Creates a new [`Box`]`<[u8]>` with the alignment required for [`Glyph`]s.
  ///
  /// - Length can be no greater than `u32::MAX * 8` and must be a multiple
  ///   of 8.
  /// - The contents of the buffer will not be zeroed.  Take care to overwrite
  ///   the entire buffer, or you may leak secrets into the encoded glyph.
  /// - Once the buffer contains a well-formed glyph, it can be converted into
  ///   a [`BoxGlyph`] by calling [`BoxGlyph::from_buffer`].
  pub fn new_buffer(length: usize) -> Result<Box<[u8], GlyphAlloc>, GlyphErr> {
    if length % 8 != 0 {
      Err(GlyphErr::GlyphLenUnaligned(length))
    } else if length > u32::MAX as usize * 8 {
      Err(GlyphErr::GlyphLenOverflow(length))
    } else {
      unsafe {
        let b =
          Box::<[u8], GlyphAlloc>::try_new_uninit_slice_in(length, GlyphAlloc)?
            .assume_init();
        Ok(b)
      }
    }
  }

  /// Converts a [`Box`]`<[u8]>` created by [`BoxGlyph::new_buffer()`]
  /// containing a well-formed glyph into a [`BoxGlyph`].
  ///
  /// - The buffer must contain a well-formed glyph--i.e., it must start with
  ///   a [`GlyphHeader`] with a length matching the size of the buffer itself.
  /// - A regular `Box<[u8]>` cannot be used directly due to alignment concerns.
  pub fn from_buffer(
    buffer: Box<[u8], GlyphAlloc>,
  ) -> Result<BoxGlyph, GlyphErr> {
    let _parsed = glyph_read(buffer.as_ref(), &mut 0)?;
    unsafe { Ok(Self::from_unchecked_buf(buffer)) }
  }

  /// Create a new glyph by copying parsed bytes from another buffer onto the
  /// heap.
  pub fn copy_from_parsed(parsed: ParsedGlyph) -> Result<Self, GlyphErr> {
    unsafe {
      let mut b = Box::<[u8], GlyphAlloc>::try_new_uninit_slice_in(
        parsed.len(),
        GlyphAlloc,
      )?
      .assume_init();
      b.as_mut().copy_from_slice(parsed.as_ref());
      Ok(BoxGlyph(b))
    }
  }

  pub unsafe fn from_unchecked_buf(buf: Box<[u8], GlyphAlloc>) -> Self {
    BoxGlyph(buf)
  }
}

#[cfg(feature = "alloc")]
impl AsRef<[u8]> for BoxGlyph {
  fn as_ref(&self) -> &[u8] {
    self.0.as_ref()
  }
}

impl ToGlyph for BoxGlyph {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    u8::bbwrs(self.as_ref(), target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    self.as_ref().len()
  }
}

impl TryFrom<Box<[u8], GlyphAlloc>> for BoxGlyph {
  type Error = GlyphErr;

  fn try_from(value: Box<[u8], GlyphAlloc>) -> Result<Self, Self::Error> {
    // SAFETY: glyph_read does our bounds checking (header vs buffer)
    let _ = glyph_read(value.as_ref(), &mut 0)?;
    Ok(BoxGlyph(value))
  }
}

unsafe impl Glyph for BoxGlyph {}

impl Debug for BoxGlyph {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    glyph_debug(self, f)
  }
}

#[cfg(feature = "alloc")]
#[derive(Clone)]
pub struct ArcGlyph(ArcGlyphBuf<ArcGlyphBufFinalized>);

#[cfg(feature = "alloc")]
impl ArcGlyph {
  pub fn new_buffer(
    length: usize,
  ) -> Result<ArcGlyphBuf<ArcGlyphBufUninit>, GlyphErr> {
    ArcGlyphBuf::new(length)
  }

  /// Create a new glyph by copying parsed bytes from another buffer onto the
  /// heap.
  pub fn from_parsed(parsed: ParsedGlyph) -> Result<Self, GlyphErr> {
    unsafe {
      let mut buf = Self::new_buffer(parsed.len())?;
      buf.as_mut().copy_from_slice(parsed.as_ref());
      let buf = buf.finalize();
      Ok(ArcGlyph::from_unchecked_buf(buf))
    }
  }

  pub unsafe fn from_unchecked_buf(
    buf: ArcGlyphBuf<ArcGlyphBufFinalized>,
  ) -> Self {
    ArcGlyph(buf)
  }

  pub fn strong_count(&self) -> usize {
    Arc::<[u8], GlyphAlloc>::strong_count(&self.0.inner())
  }

  pub fn weak_count(&self) -> usize {
    Arc::<[u8], GlyphAlloc>::weak_count(&self.0.inner())
  }
}

impl AsRef<[u8]> for ArcGlyph {
  fn as_ref(&self) -> &[u8] {
    self.0.as_ref()
  }
}

impl Debug for ArcGlyph {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut d = f.debug_struct(core::any::type_name::<ArcGlyph>());
    let addr = self.as_ref().as_ptr();
    d.field("address", &addr);
    d.field(
      "strong_references",
      &Arc::<[u8], GlyphAlloc>::strong_count(&self.0.inner()),
    );
    d.field(
      "weak_references",
      &Arc::<[u8], GlyphAlloc>::weak_count(&self.0.inner()),
    );
    d.field("glifs_hash", &self.glyph_hash());
    d.field("header", &self.header());
    #[cfg(feature = "alloc")]
    if !self.header().is_short() {
      d.field("content", &HexDump(self.content_padded()));
    } else {
      d.field("content", &self.short_content());
    }
    d.finish()
  }
}

impl ToGlyph for ArcGlyph {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    u8::bbwrs(self.as_ref(), target, cursor)
  }

  fn glyph_len(&self) -> usize {
    self.as_ref().len()
  }
}

unsafe impl Glyph for ArcGlyph {
  fn glyph_hash(&self) -> GlyphHash {
    *self.0.glyph_hash()
  }
}

pub(crate) fn glyph_debug<G>(
  glyph: &G,
  f: &mut Formatter<'_>,
) -> core::fmt::Result
where
  G: Glyph,
{
  let mut d = f.debug_struct(core::any::type_name::<G>());
  let addr = glyph.as_ref().as_ptr();
  d.field("address", &addr);
  d.field("glifs_hash", &GlyphHash::new(glyph.as_ref()));
  d.field("header", &glyph.header());
  #[cfg(feature = "alloc")]
  if !glyph.header().is_short() {
    d.field("content", &HexDump(glyph.content_padded()));
  } else {
    d.field("content", &glyph.short_content());
  }
  d.finish()
}

/// Creates a new glyph in its own, heap-allocated buffer.
#[cfg(feature = "alloc")]
pub fn glyph_new<T>(src: T) -> Result<BoxGlyph, GlyphErr>
where
  T: ToGlyph,
{
  let buf_len = src.glyph_len();
  debug_assert_eq!(buf_len % 8, 0);
  let mut buf = BoxGlyph::new_buffer(buf_len)?;
  let cursor = &mut 0;
  src.glyph_encode(buf.as_mut(), cursor)?;

  #[cfg(test)]
  {
    if *cursor != buf_len {
      std::dbg!(HexDump(buf.as_ref()));
    }
  }

  // Check for (1) buffer overflows and (2) missing zero padding to the word.
  if *cursor != buf_len {
    panic!(
      "Glyph requested {} bytes but wrote {} bytes",
      buf_len, *cursor
    );
  }

  // glyph reads correctly.
  debug_assert!(glyph_read(buf.as_ref(), &mut 0).is_ok());
  let glyph = unsafe { BoxGlyph::from_unchecked_buf(buf) };
  Ok(glyph)
}

/// Creates a new glyph in its own, heap-allocated buffer.
#[cfg(feature = "alloc")]
pub fn glyph_new_arc<T>(src: T) -> Result<ArcGlyph, GlyphErr>
where
  T: ToGlyph,
{
  let buf_len = src.glyph_len();
  debug_assert_eq!(buf_len % 8, 0);
  let mut buf = ArcGlyph::new_buffer(buf_len)?;
  let cursor = &mut 0;
  src.glyph_encode(buf.as_mut(), cursor)?;
  let buf = buf.finalize();

  #[cfg(test)]
  {
    if *cursor != buf_len {
      std::dbg!(HexDump(buf.as_ref()));
    }
  }

  // Check for (1) buffer overflows and (2) missing zero padding to the word.
  if *cursor != buf_len {
    panic!(
      "Glyph requested {} bytes but wrote {} bytes",
      buf_len, *cursor
    );
  }

  // glyph reads correctly.
  debug_assert!(glyph_read(buf.as_ref(), &mut 0).is_ok());
  let glyph = unsafe { ArcGlyph::from_unchecked_buf(buf) };
  Ok(glyph)
}

/// Reads a glyph from a byte buffer.
pub fn glyph_read<'a, T>(
  source: &'a T,
  cursor: &mut usize,
) -> Result<ParsedGlyph<'a>, GlyphErr>
where
  T: AsRef<[u8]> + ?Sized,
{
  let source = source.as_ref();
  let offset = *cursor;

  // At the very least, a glyph must start with an 8 byte header.
  let header = GlyphHeader::bbrf(source, cursor)?;
  *cursor += header.content_len();

  // SAFETY: We're going to do our own bounds check here, so we can return a
  // GlyphErr instead of panicking.  We've already done bounds checks for
  // the headers we've read with tha calls to `SafelyReadable::bbrf`, now we
  // just need to check the cursor, which we've advanced based on the glyphs'
  // stated lengths.
  unsafe {
    bounds_check(source, *cursor)?;
    let ptr = source.as_ptr().add(offset);
    let length = *cursor - offset;
    let bytes = from_raw_parts(ptr, length);
    Ok(ParsedGlyph { glyph_bytes: bytes })
  }
}

/// Types that can be encoded into glyphs.
///
/// SAFETY:
pub trait ToGlyph {
  /// Encodes the glyph to the buffer `target` at position `offset`.
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr>;

  /// Returns the number of bytes necessary to encode the type into a glyph.
  fn glyph_len(&self) -> usize;
}

impl<T> ToGlyph for &T
where
  T: ToGlyph + ?Sized,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    (*self).glyph_encode(target, cursor)
  }

  fn glyph_len(&self) -> usize {
    (*self).glyph_len()
  }
}

/// Types based on data read that can be read directly from a glyph, without deserialization.
pub trait FromGlyph<G>: Sized
where
  G: Glyph,
{
  //  /// Create a new instance of the type from a source glyph.
  //  ///
  //  /// ```
  //  /// use glifs::glyph::*;
  //  /// use glifs::buffers::U32;
  //  ///
  //  /// let number: u32 = 42;
  //  /// let glyph = glyph_new(&number).unwrap();
  //  /// let decoded = U32::from_glyph(glyph).unwrap();
  //  /// assert_eq!(decoded, number);
  //  /// ```
  //  ///
  /// This function must return an error if the target type cannot be
  /// definitively decoded.  E.g., because the glyph's type id is not
  /// appropriate for the target type.
  // This is a `T` and not a `&T` because we want to be able to have something
  // like a `VectorGlyph` take a `HashGlyph` in which case the `VectorGlyph`'s
  // lifetime won't be bound to some other object.
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr>;
}

// /// A generic type for all decoded glyphs (e.g., [`DocGlyph`]) that allows
// /// access to the underlying glyph.
// pub trait DecodedGlyph<T>
// where
//   T: AsRef<[u8]>,
// {
//   fn into_glyph(self) -> Glyph<T>;
// }

/// Finishes encoding a glyph by writing the header and (optionally) zeroing
/// any unused bytes.
///
/// This function writes a glyph header to `target` at position `offset`, with
/// length of the glyph's content calculated from `cursor`.
///
#[inline(always)]
pub(crate) fn glyph_close<B>(
  glyph_type: GlyphType,
  target: &mut B,
  mut offset: usize,
  cursor: &mut usize,
  pad: bool,
) -> Result<(), GlyphErr>
where
  B: AsRef<[u8]> + AsMut<[u8]> + ?Sized,
{
  let header =
    GlyphHeader::new(glyph_type, *cursor - offset - size_of::<GlyphHeader>())?;
  header.bbwr(target, &mut offset)?;
  if pad {
    pad_to_word(target.as_mut(), cursor)?;
  }
  Ok(())
}

/// The mapping of glyph types to `u16` values for the `type_id` field of
/// [`GlyphHeader`].
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum GlyphType {
  // =========================
  // === Fundamental Types ===
  // =========================
  /// A glyph signifying the concept of "nothing".
  Nothing = 0x0000u16,

  /// A glyph indicating that something is "unknown" or
  Unknown = 0x0001,

  /// A glyph indicating that a value was available in principle but was
  /// kept secret, or "redacted".
  Redacted = 0x0002,

  // ==============================
  // === GLIFS Filesystem Types ===
  // ==============================
  /// A glyph containing a command issued to a GLIFS node, e.g., to read an object.
  ///
  /// See the suite of binary formats defined [here](http://www.glifs.org/docs/books/format/commands.html)
  GlifsRequest = 0x0010,

  /// A glyph containing a command issued to a GLIFS node, e.g., to read an object.
  ///
  /// See the suite of binary formats defined [here](http://www.glifs.org/docs/books/format/commands.html)
  GlifsResponse = 0x0011,

  /// A record of a single transaction
  GlifsTxLog = 0x0012,

  // ==================
  // === Containers ===
  // ==================
  /// A glyph that contains a series of other glyphs.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/containers/tuple_vec.html)
  TupleGlyph = 0x0020,

  /// A glyph that contains a series of other glyphs.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/containers/tuple_vec.html)
  VecGlyph = 0x0021,

  /// A glyph that contains a associative map of unique keys to values.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/containers/map.html)
  MapGlyph = 0x0022,

  /// A glyph that contains a single key/value pair, apart from a map.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/containers/map.html)
  MapEntry = 0x0023,

  /// A glyph that contains a (specific version of a) document.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/containers/document.html)
  DocumentGlyph = 0x0024,

  /// A user-defined structured data type.
  ///
  /// TODO: Reference binary format documentation (after written!)
  ObjGlyph = 0x0025,

  BeTreeNode = 0x0026,
  BeTreeLeaf = 0x0027,

  /// Vectors of basic types.  See [`BasicType`].
  BasicVecGlyph = 0x0028,

  // ==================
  // === Primitives ===
  // ==================
  /// A glyph containing a binary value (`bool`).
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  Bool = 0x0040,

  /// A glyph containing a signed 32-bit little-endian integer (`i32`).
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  I32 = 0x0041,

  /// A glyph containing a signed 64-bit little-endian integer (`i64`).
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  I64 = 0x0042,

  /// A glyph containing a signed 128-bit little-endian integer (`i128`).
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  I128 = 0x0043,

  /// A glyph containing an unsigned 32-bit little-endian integer (`u32`).
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  U32 = 0x0044,

  /// A glyph containing an unsigned 64-bit little-endian integer (`u64`).
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  U64 = 0x0045,

  /// A glyph containing an unsigned 128-bit little-endian integer (`u128`).
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  U128 = 0x0046,

  /// A glyph containing a 32-bit floating point number.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  F32 = 0x0047,

  /// A glyph containing a 64-bit floating point number.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  F64 = 0x0048,

  /// A glyph containing a 128-bit floating point number.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  F128 = 0x0049,

  /// A glyph containing a 256-bit floating point number.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  F256 = 0x004a,

  SignedInt = 0x004b,
  UnsignedInt = 0x004c,
  Float = 0x004d,

  // =============================
  // === Vectors of Primitives ===
  // =============================
  /// A glyph containing a dense vector of bits.
  ///
  /// See the [`BitVector`] type and the binary format defined
  /// [here](http://www.glifs.org/docs/books/format/primitives.html#bit-vectors)
  VecBool = 0x0050,

  /// A glyph containing a vector of signed 8-bit integers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecI8 = 0x0051,

  /// A glyph containing a vector of signed little-endian 16-bit integers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecI16 = 0x0052,

  /// A glyph containing a vector of signed little-endian 32-bit integers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecI32 = 0x0053,

  /// A glyph containing a vector of signed little-endian 64-bit integers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecI64 = 0x0054,

  /// A glyph containing a vector of signed little-endian 128-bit integers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecI128 = 0x0055,

  /// A glyph containing a vector of unsigned 8-bit integers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecU8 = 0x0056,

  /// A glyph containing a vector of unsigned little-endian 16-bit integers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecU16 = 0x0057,

  /// A glyph containing a vector of unsigned little-endian 32-bit integers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecU32 = 0x0058,

  /// A glyph containing a vector of unsigned little-endian 64-bit integers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecU64 = 0x0059,

  /// A glyph containing a vector of unsigned little-endian 128-bit integers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecU128 = 0x005a,

  /// A glyph containing a vector of 16-bit floating point numbers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecF16 = 0x005b,

  /// A glyph containing a vector of 32-bit floating point numbers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecF32 = 0x005c,

  /// A glyph containing a vector of 64-bit floating point numbers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecF64 = 0x005d,

  /// A glyph containing a vector of 128-bit floating point numbers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecF128 = 0x005e,

  /// A glyph containing a vector of 256-bit floating point numbers.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/primitives.html)
  VecF256 = 0x005f,

  // ======================
  // === Human Language ===
  // ======================
  /// A glyph containing a single unicode code point.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/language.html)
  UnicodeChar = 0x0060,

  /// A glyph containing a string encoded in UTF-8.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/language.html)
  StringUTF8 = 0x0061,

  /// A glyph containing a string encoded in UTF-16.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/language.html)
  StringUTF16 = 0x0062,

  /// A glyph containing a string encoded in UTF-32.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/language.html)
  StringUTF32 = 0x0063,

  // ============================
  // === Common Complex Types ===
  // ============================
  /// A glyph containing a UUID.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/uuid.html)
  UUID = 0x0070,

  /// A glyph containing a vector of UUIDs.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/uuid.html)
  VecUUID = 0x0071,

  /// A glyph specifying an instant in time.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/time.html)
  DateTime = 0x0072,

  /// A glyph specifying a length of time.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/time.html)
  Duration = 0x0073,

  /// A glyph specifying an IPv4 Internet address.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/network.html)
  IpAddrV4 = 0x0074,

  /// A glyph specifying an IPv6 Internet address
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/network.html)
  IpAddrV6 = 0x0075,

  // ============================
  // === Cryptographic Hashes ===
  // ============================
  /// A glyph specifying an MD5 hash value.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/hash.html)
  HashMD5 = 0x00a0,

  /// A glyph specifying an SHA1 hash value.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/hash.html)
  HashSha1 = 0x00a1,

  /// A glyph specifying an SHA2-256 hash value.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/hash.html)
  #[allow(non_camel_case_types)]
  HashSha2 = 0x00a2,

  /// A glyph specifying an SHA3-256 hash value.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/hash.html)
  #[allow(non_camel_case_types)]
  HashSha3 = 0x00a3,

  /// A glyph specifying an SHA3-512 hash value.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/hash.html)
  #[allow(non_camel_case_types)]
  HashBlake3 = 0x00a4,

  // === Vectors of Cryptographic Hashes ===
  /// A glyph containing a vector of MD5 hash values.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/hash.html)
  VecHashMd5 = 0x00b0,

  /// A glyph containing a vector of SHA1 hash values.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/hash.html)
  VecHashSha1 = 0x00b1,

  /// A glyph containing a vector of SHA2-256 hash values.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/hash.html)
  #[allow(non_camel_case_types)]
  VecHashSha2 = 0x00b2,

  /// A glyph containing a vector of SHA3-256 hash values.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/hash.html)
  #[allow(non_camel_case_types)]
  VecHashSha3 = 0x00b3,

  /// A glyph containing a vector of Blake3 hash values.
  ///
  /// See the binary format [here](http://www.glifs.org/docs/books/format/types/hash.html)
  #[allow(non_camel_case_types)]
  VecHashBlake3 = 0x00b4,

  /// One or more cryptographic hashes.
  HashGlyph = 0x00b5,

  // ====================
  // === Crypto Types ===
  // ====================
  EncryptedPassword = 0x00c0,
  PublicKey = 0x00c1,
  PrivateKey = 0x00c2,
  KeyPair = 0x00c3,
  Signature = 0x00c4,
  SignedExtent = 0x00c5,
  SignedGlyph = 0x00c6,
  EncryptedExtent = 0x00c7,
  EncryptedGlyph = 0x00c8,

  /// Information about a ciphertext (e.g., initialization vectors, ephemeral
  /// keys, etc...)
  CiphertextMetadata = 0x00c9,

  /// === Merkle Structures ===
  CLiMBTreeNode = 0x0100,
}

impl From<U16> for GlyphType {
  fn from(value: U16) -> Self {
    unsafe { std::mem::transmute(value.get()) }
  }
}

impl From<u16> for GlyphType {
  fn from(value: u16) -> Self {
    unsafe { std::mem::transmute(value) }
  }
}

impl From<GlyphType> for U16 {
  fn from(value: GlyphType) -> Self {
    U16::from(value as u16)
  }
}

/// Various errors associated with handling glyphs.
//
// Note:  Early micro-benchmarks indicated that codec performance can be
// significantly affected by what kinds of variants are included, as this
// enum may be returned from those functions.  Specifically, the addition of
// an `Other(Option<String>)` slowed these functions down by a factor of 3x.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(C, u32)]
pub enum GlyphErr {
  /// User type labels may not have user type labels themselves.
  RecursiveUserTypeLabel,

  /// The header contained invalid data (illegal version, reserved bytes not
  /// zero, etc...)
  InvalidHeader,

  /// Offsets into glyphs must be multiples of 8 bytes and less than
  /// `core::u32::MAX << 3` bytes.
  GlyphOffsetInvalid {
    start:    usize,
    position: usize,
  },

  InvalidUserTypeLabel,

  /// The content length is larger than the maximum `core::u32::MAX << 3`
  TooLarge(usize),

  /// There was an attempt to create a glyph smaller than the minimum size.
  TooSmall(usize),

  TooManyItems {
    num_items: usize,
    allowed:   usize,
  },

  /// A specific type of glyph was expected, but some other type was observed.
  ///
  /// The `type_id`s correspond to the same field in the glyph header.
  UnexpectedType {
    expected_type_id: u16,
    observed_type_id: u16,
  },

  /// A specific subtype of glyph was expected, but some other subtype was
  /// observed.
  ///
  /// Similar to [`Self::UnexpectedType`], but where the `type_id` in the glyph header
  /// was as expected, but where the subtype observed was not as expected.
  UnexpectedSubType {
    type_index:       u32,
    expected_type_id: u32,
    observed_type_id: u32,
  },

  UnknownSubType {
    type_index:       u8,
    observed_type_id: u32,
  },

  /// When deserializing an object to a user structure, the stored type didn't
  /// match what was expected.
  UnexpectedStructure,

  /// An out of bounds error occurred, e.g., indexing past the end of a
  /// [`VecGlyph`]
  OutOfBounds {
    index:  usize,
    length: usize,
  },

  /// A length was required to be a multiple of 8 bytes, but was not.
  WordLengthError(usize),

  /// The glyph contained some value which was not allowed when decoding.
  IllegalValue,

  /// Some data was not or could not be sorted as required.
  SortErr,

  /// Some `BufferError` occurred
  // BufferErr(BufferErr),

  /// The glyph header asserted that some bytes were padding bytes, but those
  /// bytes were not set equal to zero.
  PaddingNonZero,

  /// The glyph was of a version that was not recognized by this software.
  UnknownVersion,

  /// A user type label was requested, but none was present.
  UserTypeLabelNotPresent,

  // /// An error occurred while working with cryptographic data.
  // CryptoErr(CryptoErr),
  /// A type cannot be decoded because it is encrypted.
  ///
  /// Use an intermediate type that has a more specific decoding function
  /// providing for decryption.
  NeedsDecryption,

  /// Data in the glyph did not match an expected hash.
  ///
  /// This should typically be caused by corrupt (or malicious) data.
  HashMismatch,

  /// An error occurred obtaining a necessary mutex.
  MutexErr,

  /// An error occurred inside the Tokio runtime.
  TokioJoinErr,

  /// An internal error occurred.
  ///
  /// This is likely a condition that should be impossible, and an error was
  /// returned rather than a fail-fast assert failure panic.
  InternalError,

  /// An overflow occurred during a checked integer type conversion.
  IntConversionOverflow,

  /// Attempted to calculate a hash value using an algorithm that is not
  /// available to running code.
  HashAlgorithmMissing,

  #[cfg(feature = "serde")]
  /// An unspecified error occurred while (de-)serializing through serde.
  SerdeErr,

  /// When encoding an object glyph, names of types, variants, and fields must
  /// be less than 255 bytes.
  ObjGlyphNameLen,

  /// An attempt to decrypt ciphertext failed because the decrypted data
  /// did not match the message authentication code (MAC).
  CiphertextInvalid,

  /// Decryption was attempted with the wrong kind of key.
  ///
  /// E.g., The user attempted to use an AES key to decrypt something that was
  /// encrypted using an X25519 public key.
  WrongCryptoScheme,

  /// A key was provided that did not have the correct number of bytes for the
  /// encryption used.
  CryptoKeyLength,

  /// Unexpected crypto key type
  CryptoKeyType,

  /// Invalid Signature
  SignatureInvalid,

  /// A decoding failed, because the target fingerprint does not match.
  FingerprintMismatch,

  /// LATER: Description
  Ed25519Error,

  GlyphNotFound(GlyphHash),

  /// When writing a BeTreeNode, provided bloom filters had different lengths.
  BloomFilterLengthMismatch {
    expected: usize,
    observed: usize,
  },

  /// Attempt to serialize a tiny string larger than 2^8-1 bytes long.
  TinyStringOverflow(usize),

  /// Attempt to serialize a short string larger than 2^16-1 bytes long.
  ShortStringOverflow(usize),

  // === Now for CLiMBTrees ===
  /// Fixed key length overflow. Upper limit is (u8::MAX - 1) 8-byte words.
  CLiMBTreeKeyLenOverflow(usize),

  /// Fixed value length overflow. Upper limit is (u8::MAX - 1) 8-byte words.
  CLiMBTreeValueLenOverflow(usize),

  /// Too many deletes in a node. Upper limit is `u32::MAX`
  CLiMBTreeNumDeletesOverflow(usize),

  /// Too many entries in a node. Upper limit is `u32::MAX`
  CLiMBTreeNumEntriesOverflow(usize),

  /// Too many node-level SSTable links. Upper limit is `u16::MAX`
  CLiMBTreeNumSSLinksOverflow(usize),

  /// Too many links to child nodes.  Upper _expressible_ limit is `u16::MAX`,
  /// but realistically this should only be a handful, and even then temporarily,
  /// because it _dramatically_ increases search overhead.
  CLiMBTreeNumNodeLinksOverflow(usize),

  /// Too many pivot keys in a node.  Upper limit is `u16::MAX`.
  CLiMBTreeNumPivotsOverflow(usize),

  /// Bloom filters in CLiMB Trees must be a multiple of 32 bytes with a
  /// maximum of `u16::MAX * 32` bytes in total.
  CLiMBTreeIllegalBloomLen(usize),

  /// An attempt was made to do a leaf update on a CLiMB tree node other than a leaf.
  CLiMBTreeLeafUpdateNonLeaf(GlyphHash),

  /// A single entry was bigger than the maximum node size.
  ///
  /// The value is a tuple of `(bytes needed, maximum size)`
  CLiMBTreeEntryTooBigForLeaf(usize, usize),

  /// A CLiMBTree node cannot have both an entry and tombstone with the same key.
  CLiMBTreeTombstoneCollision,

  /// An overflow occurred of the number of hash functions
  CLiMBTreeIllegalBloomK(usize),

  /// An operation required an iterator to have an exact length, checked at
  /// runtime, but it did not.
  ///
  /// This will typically happen if [`Iterator::size_hint`] doesn't return
  /// `(x, Some(x))`.  In many cases, this can be caught statically at compile
  /// time by using the [`ExactSizeIterator`] trait, but there are some cases
  /// where (1) this can't technically be implemented correctly due to combining
  /// other iterators, and (2) we still need to know an exact length for the
  /// iterator.
  UnknownIteratorLength(usize, Option<usize>),
  CLiMBTreePivotBoundMissing,
  CLiMBTreeNumPivotChildrenOverflow(usize),
  CLiMBTreeNumPivotSSTablesOverflow(usize),

  /// Attempted to load an Ed25519 verification key, but the key was invalid.
  Ed25519VerificationKeyInvalid,

  /// When writing a CLiMBTreeNode, an attempt was made to write more tombstone
  /// entries than had been allocated when the writer was initialized.
  CLiMBTreeNodeNumTombstoneOverflow(usize),
  CLiMBTreeNodeEntriesOverflow,
  CLiMBTreeNodeSSTableLinksOverflow,
  CLiMBTreeNodePivotsOverflow,
  CLiMBTreeNodePivotKeyMissing,
  CLiMBTreeNodePivotChildLinksOverflow,
  CLiMBTreeNodePivotSSTableLinksOverflow,
  CLiMBTreeNodePivotSSTableLinksIncomplete,
  CLiMBTreeNodePivotChildLinksIncomplete,

  /// When writing successive pivots in [`CLiMBTreeNode`]s, the keys must be
  /// in ascending order.
  CLiMBTreeNodePivotKeysOrder,
  CLiMBTreeNodeTombstoneIncomplete,
  CLiMBTreeNodeEntriesIncomplete,
  CLiMBTreeNodeSSTableLinksIncomplete,
  InvalidIntType(GlyphType),
  Infalliable,
  BasicGlyphTypeMissing,
  BasicTypeLenOverflow,
  UnexpectedZeroCopyType {
    expected: ZeroCopyTypeID,
    observed: ZeroCopyTypeID,
  },
  UnalignedSlice {
    needed: usize,
    addr:   usize,
  },
  UnexpectedCryptoHashType {
    expected: crate::crypto::CryptographicHashTypeID,
    observed: crate::crypto::CryptographicHashTypeID,
  },
  CryptoHashOverflow {
    expected: usize,
    observed: usize,
  },
  InvalidHashPrefixLen(usize),
  InvalidHashPrefixN(usize),
  InvalidHashPrefixExtension(usize),
  AllocationFailed,
  MapLenOverflow {
    num_items: usize,
  },
  VecGlyphLenOverflow {
    num_items: usize,
  },
  GlyphLenOverflow(usize),
  ObjGlyphNumFieldsOverflow(usize),

  /// When writing a [`CLiMBTreeGlyph`], the bloom filter length did not match the expected length.[
  CLiMBTreeBloomMismatch {
    expected: usize,
    actual:   usize,
  },
  /// The length of a glyph must be a multiple of 8 bytes.
  GlyphLenUnaligned(usize),
}

impl Display for GlyphErr {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    Debug::fmt(self, f)
  }
}

impl From<Utf8Error> for GlyphErr {
  fn from(_src: Utf8Error) -> Self {
    GlyphErr::IllegalValue
  }
}

#[cfg(feature = "alloc")]
impl From<FromUtf8Error> for GlyphErr {
  fn from(_src: FromUtf8Error) -> Self {
    GlyphErr::IllegalValue
  }
}

impl From<TryFromIntError> for GlyphErr {
  fn from(_value: TryFromIntError) -> Self {
    GlyphErr::IntConversionOverflow
  }
}

impl From<core::convert::Infallible> for GlyphErr {
  fn from(_value: core::convert::Infallible) -> Self {
    GlyphErr::Infalliable
  }
}

#[cfg(feature = "std")]
impl<T> From<std::sync::PoisonError<T>> for GlyphErr {
  fn from(_src: std::sync::PoisonError<T>) -> Self {
    GlyphErr::MutexErr
  }
}

impl From<AllocError> for GlyphErr {
  fn from(_err: AllocError) -> Self {
    GlyphErr::AllocationFailed
  }
}

#[allow(unused)]
#[cfg(test)]
mod test {
  use super::*;
  use std::dbg;

  // Sentinel code to ensure `&dyn ToGlyph` works.
  pub fn dyn_to_glyph() -> Result<(), GlyphErr> {
    let number = 42i32;
    let tg = &number as &dyn ToGlyph;
    glyph_new(tg)?;
    Ok(())
  }
}
