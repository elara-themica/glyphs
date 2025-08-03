use core::fmt::Debug;
use log::{Level, STATIC_MAX_LEVEL};

/// When enabling backtraces (but not feature `backtrace_full`), the number of
/// stack frames to log.
const SHORT_BACKTRACE_LOG_FRAMES: usize = 2;

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
          if cfg!(test) {
            std::eprintln!("Err({error:?}");
            if cfg!(feature = "backtrace") {
              let mut bt = backtrace::Backtrace::new_unresolved();
              bt.resolve();
              std::eprintln!("{:?}", bt);
            }
          } else if cfg!(feature = "log") {
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
