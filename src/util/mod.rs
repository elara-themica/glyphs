//! Misc non-public utility code for the glyphs crate itself.
mod bloom;
pub(crate) mod debug;

mod log;
mod memoize;
mod sorting;

#[cfg(test)]
pub(crate) mod test;

#[allow(unused_imports)]
pub(crate) use self::{bloom::*, log::*, memoize::*, sorting::*};
#[allow(unused_imports)]
use crate::{
  util::debug::ShortHexDump,
  zerocopy::{pad_to_word, round_to_word, ZeroCopy},
  FromGlyph, Glyph, GlyphErr, GlyphOffset, ToGlyph,
};
use core::str::from_utf8;

///
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
