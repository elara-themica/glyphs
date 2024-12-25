use crate::{
  zerocopy::{
    bounds_check, round_to_word, HasZeroCopyID, ZeroCopy, ZeroCopyGlyph,
    ZeroCopyTypeID, U16, U32,
  },
  FromGlyph, Glyph, GlyphErr, GlyphType, ParsedGlyph,
};
use core::fmt::{Debug, Formatter};
use std::{marker::PhantomData, ops::Deref, ptr::NonNull};

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
pub struct ZcG<G: Glyph, T: ZeroCopyGlyph>(G, PhantomData<T>);

impl<G: Glyph, T: ZeroCopyGlyph> FromGlyph<G> for ZcG<G, T> {
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

impl<G: Glyph, T: ZeroCopyGlyph> Deref for ZcG<G, T> {
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

impl<'a, T: ZeroCopyGlyph> ZcG<ParsedGlyph<'a>, T> {
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

#[derive(Copy, Clone, Eq, PartialOrd, PartialEq, Debug)]
#[repr(packed)]
pub(crate) struct ZcVecGHeader {
  /// A type identifier.  See [`ZeroCopyTypeID`].
  pub basic_type_id: U16,

  /// The length of the basic type, in bytes.
  pub type_len: U16,

  /// Allows the specification of arbitrary dimensionality.
  ///
  /// See the documentation on [`ZcVecG`].
  pub tensor_rank: u8,

  /// Reserved for future use.
  pub _reserved: [u8; 3],
}

impl ZcVecGHeader {
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

unsafe impl ZeroCopy for ZcVecGHeader {}

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

pub struct ZcVecG<G: Glyph, T: ZeroCopy>(G, NonNull<[T]>);

impl<G: Glyph, T: HasZeroCopyID> FromGlyph<G> for ZcVecG<G, T> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::BasicVecGlyph)?;
    let cursor = &mut 0;
    let content = glyph.content();
    let header = ZcVecGHeader::bbrf(content, cursor)?;
    header.confirm_zero_copy_type(T::ZERO_COPY_ID)?;
    *cursor += header.tensor_rank as usize * size_of::<U32>();
    *cursor = round_to_word(*cursor);
    let slice_ptr = NonNull::from(T::bbrfs_i(content, cursor));
    Ok(Self(glyph, slice_ptr))
  }
}

impl<G: Glyph, T: ZeroCopy> Deref for ZcVecG<G, T> {
  type Target = [T];

  fn deref(&self) -> &Self::Target {
    // SAFETY: Glyph referenced is immutable and pinned.
    unsafe { self.1.as_ref() }
  }
}

impl<'a, T: ZeroCopy> ZcVecG<ParsedGlyph<'a>, T> {
  /// Get a reference to the contained array, but with a lifetime bound by
  /// the underlying byte buffer.
  pub fn get_parsed(&self) -> &'a [T] {
    // SAFETY: Glyph referenced is immutable, pinned, and result's lifetime is
    //         bound by that of the underlying buffer.
    unsafe { self.1.as_ref() }
  }
}

impl<G: Glyph, T: ZeroCopy + Debug> Debug for ZcVecG<G, T> {
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