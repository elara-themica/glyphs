use crate::{
  zerocopy::{
    bounds_check, round_to_word, HasZeroCopyID, ZeroCopy, ZeroCopyGlyph,
    ZeroCopyTypeID, U16, U32,
  },
  EncodedGlyph, FromGlyph, Glyph, GlyphErr, GlyphType, ParsedGlyph,
};
use core::fmt::{Debug, Formatter};
use std::{cmp::Ordering, marker::PhantomData, ops::Deref, ptr::NonNull};

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
        &self.0.header().short_content()[..]
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
        &self.0.header_parsed().short_content()[..]
      };
      T::bbrf_u(buf, &mut 0)
    }
  }
}

impl<G: Glyph, T: ZeroCopyGlyph> PartialEq for BasicGlyph<G, T> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Glyph, T: ZeroCopyGlyph> Eq for BasicGlyph<G, T> {}

impl<G: Glyph, T: ZeroCopyGlyph> PartialOrd for BasicGlyph<G, T> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph, T: ZeroCopyGlyph> Ord for BasicGlyph<G, T> {
  fn cmp(&self, other: &Self) -> Ordering {
    self
      .glyph()
      .glyph_type()
      .cmp(&other.glyph().glyph_type())
      .then_with(|| self.deref().cmp(other.deref()))
  }
}

impl<G: Glyph, T: ZeroCopyGlyph> Debug for BasicGlyph<G, T> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    Debug::fmt(self.deref(), f)
  }
}

impl<G: Glyph, T: ZeroCopyGlyph> EncodedGlyph for BasicGlyph<G, T> {
  fn glyph(&self) -> ParsedGlyph<'_> {
    self.0.borrow()
  }
}

#[derive(Copy, Clone, Eq, PartialOrd, PartialEq, Debug)]
#[repr(packed)]
pub(crate) struct BasicVecGlyphHeader {
  reserved: u8,

  /// The number of dimensions in a multidimensional array.
  pub tensor_rank: u8,

  /// A type identifier.  See [`ZeroCopyTypeID`].
  pub basic_type_id: U16,

  /// The length of the basic type, in bytes.
  pub type_len: U16,

  reserved2: [u8; 2],
}

impl BasicVecGlyphHeader {
  pub(crate) fn tensor_rank(&self) -> usize {
    self.tensor_rank as usize
  }
}

impl BasicVecGlyphHeader {
  pub fn new_vec<T: HasZeroCopyID>() -> Result<Self, GlyphErr> {
    let type_len = U16::from(
      u16::try_from(size_of::<T>())
        .map_err(|_t| GlyphErr::BasicTypeLenOverflow)?,
    );

    Ok(Self {
      reserved: Default::default(),
      basic_type_id: T::ZERO_COPY_ID.into(),
      type_len,
      tensor_rank: Default::default(),
      reserved2: Default::default(),
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

pub struct BasicVecGlyph<G: Glyph, T: ZeroCopy> {
  glyph:          G,
  header:         NonNull<BasicVecGlyphHeader>,
  tensor_lengths: NonNull<[U32]>,
  data:           NonNull<[T]>,
}

impl<G: Glyph, T: ZeroCopy> BasicVecGlyph<G, T> {
  /// Returns the ZeroCopy type contained in the glyph.
  pub fn type_id(&self) -> ZeroCopyTypeID {
    unsafe { self.header.as_ref().basic_type_id.into() }
  }

  /// Returns the length of the zero copy type contained in the glyph.
  pub fn type_len(&self) -> usize {
    unsafe { self.header.as_ref().type_len.get() as usize }
  }

  /// Returns the number of dimensions if this is a tensor
  pub fn tensor_rank(&self) -> usize {
    unsafe { self.header.as_ref().tensor_rank as usize }
  }
}

impl<G, T> FromGlyph<G> for BasicVecGlyph<G, T>
where
  G: Glyph,
  T: Debug + Eq + PartialEq + PartialOrd + Ord + ZeroCopy + HasZeroCopyID,
{
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::VecBasic)?;
    let cursor = &mut 0;
    let content = glyph.content();
    let header = BasicVecGlyphHeader::bbrf(content, cursor)?;
    header.confirm_zero_copy_type(T::ZERO_COPY_ID)?;
    let tensor_lengths = NonNull::from(U32::bbrfs(
      content,
      cursor,
      header.tensor_rank().saturating_sub(1),
    )?);
    *cursor = round_to_word(*cursor);
    let data = NonNull::from(T::bbrfs_i(content, cursor));
    let header = NonNull::from(header);
    Ok(Self {
      glyph,
      header,
      tensor_lengths,
      data,
    })
  }
}

impl<G: Glyph, T: ZeroCopy> Deref for BasicVecGlyph<G, T> {
  type Target = [T];

  fn deref(&self) -> &Self::Target {
    // SAFETY: Glyph referenced is immutable and pinned.
    unsafe { self.data.as_ref() }
  }
}

impl<'a, T: ZeroCopy> BasicVecGlyph<ParsedGlyph<'a>, T> {
  /// Get a reference to the contained array, but with a lifetime bound by
  /// the underlying byte buffer.
  pub fn get_parsed(&self) -> &'a [T] {
    // SAFETY: Glyph referenced is immutable, pinned, and result's lifetime is
    //         bound by that of the underlying buffer.
    unsafe { self.data.as_ref() }
  }
}

impl<G: Glyph, T: ZeroCopy + Debug> Debug for BasicVecGlyph<G, T> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    if !f.alternate() {
      core::fmt::Debug::fmt(self.deref(), f)
    } else {
      let mut df = f.debug_struct(core::any::type_name::<Self>());
      df.field("type_id", &self.type_id());
      df.field("type_len", &self.type_len());
      df.field("tensor_rank", &self.tensor_rank());
      df.field("data", &self.deref());
      df.finish()
    }
  }
}
