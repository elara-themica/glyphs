use core::fmt::Debug;
use log::{Level, STATIC_MAX_LEVEL};

/// When enabling backtraces (but not feature `backtrace_full`), the number of
/// stack frames to log.
const SHORT_BACKTRACE_LOG_FRAMES: usize = 2;

/// Utility trait for error reporting, primarily used with [`Option`].
///
/// This provides an alternative to `Option`'s `or_or()` and `ok_or_else()`, and
/// addresses the following issues:
///
/// - With `ok_or`, the error is not at the point it is generated.  This is
///   frequently very useful for debugging, as catching and reporting errors
///   further up the call stack frequently does not provide enough information
///   to be useful for debugging purposes.  Further, it's not possible to embed
///   the error reporting in the predicate (i.e., as the argument to `ok_or()`)
///   because in doing so it is "eagerly" evaluated regardless of whether the
///   error condition triggers.
/// - While `ok_or_else`, addresses the above issue, it requires more verbose
///   syntax (a closure) at each and every call location.
/// - In addition, when used deep inside heavily used functions, we'd like the
///   error reporting to be compiled only with debug builds, which further
///   complicates the issues above.
///
/// Any implementors should call `log_err()` to actually report the error, which
/// will report the error using the `log` crate/feature is present, and a
/// backtrace (always at the `trace` level) if the `backtrace` crate/feature is
/// present.
pub(crate) trait OkOrLog<O, E>: Sized
where
  E: Debug,
{
  fn ok_or_log(self, level: log::Level, error: E) -> Result<O, E>;
}

impl<O, E> OkOrLog<O, E> for Option<O>
where
  E: Debug,
{
  #[inline(always)]
  fn ok_or_log(self, level: log::Level, error: E) -> Result<O, E> {
    if let Some(value) = self {
      Ok(value)
    } else {
      if cfg!(feature = "log") {
        log::log!(level, "{:?}", error);
        if cfg!(feature = "backtrace") {
          let mut bt = backtrace::Backtrace::new_unresolved();
          bt.resolve();
          log::trace!("{:?}", bt);
        }
      }
      Err(error)
    }
  }
}

// LATER: Add this optional log / back-tracing to most errors.
// LATER: Test which and how many stack frames to output.
pub(crate) trait LogErr<O, E>
where
  E: Debug,
{
  fn log_err(self, level: log::Level) -> Result<O, E>;
}

impl<O, E> LogErr<O, E> for Result<O, E>
where
  E: Debug,
{
  #[inline(always)]
  fn log_err(self, level: Level) -> Result<O, E> {
    match self {
      Ok(value) => Ok(value),
      Err(error) => {
        // Const comparison allows dead code elimination.
        if level > STATIC_MAX_LEVEL {
          if cfg!(feature = "log") {
            log::log!(level, "{:?}", error);
            if cfg!(feature = "backtrace") {
              let mut bt = backtrace::Backtrace::new_unresolved();
              bt.resolve();
              if cfg!(feature = "backtrace_full") {
                log::trace!("{:?}", bt);
              } else {
                for frame in
                  bt.frames().iter().skip(1).take(SHORT_BACKTRACE_LOG_FRAMES)
                {
                  log::trace!("{frame:?}");
                }
              }
            }
          }
        }
        Err(error)
      },
    }
  }
}
