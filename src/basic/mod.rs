//! Numbers, strings, boolean, nothing, option, etc...
use crate::{
  zerocopy::{F32, F64, I128, I16, I32, I64, U128, U16, U32, U64},
  FromGlyph, Glyph, GlyphErr, GlyphType, ToGlyph,
};
use core::str::from_utf8;

mod bool;
pub use bool::*;

mod lang;
pub use lang::*;

mod numeric;
pub use numeric::*;

mod unit;
pub use unit::*;

mod zc;
pub use zc::*;

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
    if type_id == GlyphType::Unit {
      let unit = UnitG::from_glyph(source)?;
      if unit.type_id().eq(&UnitTypes::Nothing) {
        Ok(None)
      } else {
        Err(err!(debug, GlyphErr::UnexpectedUnitType(*unit.type_id())))
      }
    } else {
      let val = T::from_glyph(source)?;
      Ok(Some(val))
    }
  }
}

#[cfg(feature = "alloc")]
#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    glyph_new, glyph_read,
    util::{
      debug::HexDump, simple_codec_slice_test, simple_codec_test,
      BENCH_BUF_SIZE,
    },
    FromGlyph, Glyph, GlyphErr,
  };
  use ::test::Bencher;
  use alloc::boxed::Box;
  use std::{dbg, hint::black_box, iter::repeat, string::String};

  #[test]
  fn codec_basic() {
    //== Simple Scalar Values ==/
    simple_codec_test(());
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
        let decoded = IntG::from_glyph(glyph)?;
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
