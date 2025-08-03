//! Code useful for testing.

use crate::{zerocopy::ZeroCopy, FromGlyph, Glyph, ToGlyph};
use core::{
  fmt::Debug,
  sync::atomic::{AtomicBool, Ordering::SeqCst},
};

pub const TEST_PLAINTEXT: &[u8; 39] =
  b"Deutsche truppen sind jetzt in England.";

pub const TEST_IMPOSTER_TEXT: &[u8; 39] =
  b"Deutsche Truppen sind jetzt in England.";

/// Tracks whether the global default logger is initialized.
static TEST_LOGGER_INIT: AtomicBool = AtomicBool::new(false);

/// Ensures the test logger is initialized.
///
/// This function uses atomics to ensure that the test logger is only
/// ever initialized once.
pub fn init_test_logger() {
  match TEST_LOGGER_INIT.compare_exchange(false, true, SeqCst, SeqCst) {
    Ok(false) => {
      // We need to initialize
      let result = env_logger::Builder::from_default_env()
        .default_format()
        .format_timestamp_nanos()
        .try_init();
      match result {
        Ok(_) => log::info!("Initialized test logger"),
        Err(_) => panic!(),
      }
      return;
    },
    Ok(true) => panic!(), // Should be impossible
    Err(true) => return,  // Already initialized
    Err(false) => {
      core::hint::spin_loop();
      #[cfg(feature = "std")]
      std::thread::yield_now();
      // If it's taking this long, something's wrong...
    },
  }
}

/// When doing codec tests, the size of the buffer to read/write.
pub const BENCH_BUF_SIZE: usize = 8192;

/// Does a round trip codec test for a simple
#[cfg(all(test, feature = "alloc"))]
pub fn simple_codec_test<
  T: Debug + Eq + ToGlyph + FromGlyph<alloc::boxed::Box<Glyph>>,
>(
  value: T,
) {
  let glyph = crate::Glyph::new(&value).unwrap();
  let decoded = T::from_glyph(glyph).unwrap();
  assert_eq!(decoded, value);
}

/// Does a round trip codec test for a simple
#[cfg(all(test, feature = "alloc"))]
pub fn simple_codec_test_debug<
  T: Debug + Eq + ToGlyph + FromGlyph<alloc::boxed::Box<Glyph>>,
>(
  value: T,
) {
  std::dbg!(&value);
  let glyph = crate::Glyph::new(&value).unwrap();
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
  for<'a> &'a [ZCT]: FromGlyph<&'a Glyph>,
{
  let array = [ZCT::from(value); L];
  let slice = &array[..];
  let vg = crate::Glyph::new(slice).unwrap();
  std::dbg!(&vg);
  let decoded = <&[ZCT]>::from_glyph(&*vg).unwrap();
  assert_eq!(slice, decoded);
}

pub fn simple_codec_slice_test_debug<const L: usize, T, ZCT>(value: T)
where
  T: Copy + Sized,
  ZCT: ZeroCopy + From<T> + Eq + Debug,
  [ZCT]: ToGlyph,
  for<'a> &'a [ZCT]: FromGlyph<&'a Glyph>,
{
  let array = [ZCT::from(value); L];
  let slice = &array[..];
  std::dbg!(&slice);
  let vg = crate::Glyph::new(slice).unwrap();
  std::dbg!(&vg);
  let decoded = <&[ZCT]>::from_glyph(&*vg).unwrap();
  std::dbg!(&decoded);
  assert_eq!(slice, decoded);
}
