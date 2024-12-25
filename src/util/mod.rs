//! Misc non-public utility code for the glyphs crate itself.
mod bloom;
pub(crate) mod debug;
mod log;
mod memoize;
mod sorting;

#[cfg(test)]
mod test;

#[cfg(test)]
pub(crate) use self::test::*;
#[allow(unused_imports)]
pub(crate) use self::{bloom::*, log::*, memoize::*, sorting::*};
#[allow(unused_imports)]
#[cfg(feature = "alloc")]
use crate::BoxGlyph;
use crate::{
  util::debug::ShortHexDump,
  zerocopy::{pad_to_word, round_to_word, ZeroCopy},
  FromGlyph, Glyph, GlyphErr, GlyphOffset, ParsedGlyph, ToGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  ops::Deref,
  str::from_utf8,
};

pub(crate) trait SmallStrings {
  /// Returns the number of bytes necessary to serialize a small string.
  ///
  /// Returns an `Err` if the string is longer than 255 bytes.
  fn glyph_tiny_str_len(&self) -> Result<usize, GlyphErr>;
  fn glyph_tiny_str_write<'a>(
    &self,
    target: &'a mut [u8],
    cursor: &'a mut usize,
  ) -> Result<(), GlyphErr>;

  fn glyph_tiny_str_read<'a, 'b>(
    source: &'a [u8],
    cursor: &'b mut usize,
  ) -> Result<&'a str, GlyphErr> {
    let len = u8::bbrd(source, cursor)? as usize;
    let bytes = u8::bbrfs(source, cursor, len)?;
    let result = from_utf8(bytes)?;
    Ok(result)
  }

  fn glyph_tiny_str_from_offset(
    source: &[u8],
    offset: GlyphOffset,
  ) -> Result<&str, GlyphErr> {
    let mut cursor = offset.cursor(0);
    str::glyph_tiny_str_read(source, &mut cursor)
  }
}

impl SmallStrings for str {
  fn glyph_tiny_str_len(&self) -> Result<usize, GlyphErr> {
    let _ = u8::try_from(self.as_bytes().len())
      .map_err(|_| GlyphErr::TinyStringOverflow(self.as_bytes().len()))?;
    Ok(round_to_word(size_of::<u8>() + self.as_bytes().len()))
  }

  fn glyph_tiny_str_write<'a>(
    &self,
    target: &'a mut [u8],
    cursor: &'a mut usize,
  ) -> Result<(), GlyphErr> {
    debug_assert_eq!(*cursor % 8, 0);
    let str_len = u8::try_from(self.as_bytes().len())
      .map_err(|_| GlyphErr::TinyStringOverflow(self.as_bytes().len()))?;
    str_len.bbwr(target, cursor)?;
    u8::bbwrs(self.as_bytes(), target, cursor)?;
    pad_to_word(target, cursor)?;
    Ok(())
  }
}

pub struct LikelyStr<'a>(pub &'a [u8]);

impl<'a> Debug for LikelyStr<'a> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    match core::str::from_utf8(self.0) {
      Ok(s) => {
        write!(f, "Utf8({})", s)
      },
      Err(_) => {
        write!(f, "Bytes({:?})", ShortHexDump(self.0, 8))
      },
    }
  }
}

#[derive(Debug)]
pub struct OwnedCell<T>(pub T);

impl<T> Deref for OwnedCell<T> {
  type Target = T;

  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

/// Returns `Some(# items)` if the `size_hint()` on the iterator returns a
/// matching upper and lower bound, and `None` otherwise.
pub(crate) fn known_iter_len<I: Iterator>(iter: &I) -> Option<usize> {
  let (lower_bound, upper_bound) = iter.size_hint();
  if let Some(upper_bound) = upper_bound {
    if lower_bound == upper_bound {
      Some(upper_bound)
    } else {
      None
    }
  } else {
    None
  }
}

// TODO: Refactor this to use `known_iter_len()` above.
pub(crate) fn checked_iter_len<I: Iterator>(
  iter: &I,
) -> Result<usize, GlyphErr> {
  let (lower_bound, upper_bound) = iter.size_hint();
  let upper_bound = upper_bound.ok_or_log(
    ::log::Level::Error,
    GlyphErr::UnknownIteratorLength(lower_bound, upper_bound),
  )?;
  if upper_bound != lower_bound {
    Err(err!(
      error,
      GlyphErr::UnknownIteratorLength(lower_bound, Some(upper_bound))
    ))
  } else {
    Ok(upper_bound)
  }
}

/// When doing codec tests, the size of the buffer to read/write.
pub(crate) const BENCH_BUF_SIZE: usize = 8192;

/// Does a round trip codec test for a simple
#[cfg(all(test, feature = "alloc"))]
pub fn simple_codec_test<T: Debug + Eq + ToGlyph + FromGlyph<BoxGlyph>>(
  value: T,
) {
  let glyph = crate::glyph_new(&value).unwrap();
  let decoded = T::from_glyph(glyph).unwrap();
  assert_eq!(decoded, value);
}

/// Does a round trip codec test for a simple
#[cfg(all(test, feature = "alloc"))]
pub fn simple_codec_test_debug<
  T: Debug + Eq + ToGlyph + FromGlyph<BoxGlyph>,
>(
  value: T,
) {
  std::dbg!(&value);
  let glyph = crate::glyph_new(&value).unwrap();
  std::dbg!(&glyph);
  let decoded = T::from_glyph(glyph).unwrap();
  std::dbg!(&decoded);
  assert_eq!(decoded, value);
}

pub fn simple_codec_slice_test<const L: usize, T, ZCT>(value: T)
where
  T: Copy + Sized,
  ZCT: ZeroCopy + From<T> + Eq + Debug,
  [ZCT]: ToGlyph,
  for<'a> &'a [ZCT]: FromGlyph<ParsedGlyph<'a>>,
{
  let array = [ZCT::from(value); L];
  let slice = &array[..];
  let vg = crate::glyph_new(slice).unwrap();
  let decoded = <&[ZCT]>::from_glyph(vg.borrow()).unwrap();
  assert_eq!(slice, decoded);
}

pub fn simple_codec_slice_test_debug<const L: usize, T, ZCT>(value: T)
where
  T: Copy + Sized,
  ZCT: ZeroCopy + From<T> + Eq + Debug,
  [ZCT]: ToGlyph,
  for<'a> &'a [ZCT]: FromGlyph<ParsedGlyph<'a>>,
{
  let array = [ZCT::from(value); L];
  let slice = &array[..];
  std::dbg!(&slice);
  let vg = crate::glyph_new(slice).unwrap();
  std::dbg!(&vg);
  let decoded = <&[ZCT]>::from_glyph(vg.borrow()).unwrap();
  std::dbg!(&decoded);
  assert_eq!(slice, decoded);
}
