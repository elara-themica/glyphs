//! Code useful for testing.
use core::sync::atomic::{AtomicBool, Ordering::SeqCst};

/// Tracks whether the global default logger is initialized.
static LOGGER_INIT: AtomicBool = AtomicBool::new(false);

/// Ensures the test logger is initialized.
///
/// This function uses atomics to ensure that the test logger is only
/// ever initialized once.
#[cfg(test)]
pub(crate) fn init_test_logger() {
  match LOGGER_INIT.compare_exchange(false, true, SeqCst, SeqCst) {
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
