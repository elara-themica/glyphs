use core::{
  cell::UnsafeCell,
  fmt::{Debug, Formatter},
  sync::atomic::{
    AtomicUsize,
    Ordering::{Acquire, Relaxed, Release},
  },
};

/// Stores a memoized value calculated from an invariant source.
///
/// Currently, the primary use of this type is for memoization of hash values.
pub(crate) struct MemoizedInvariant<T>
where
  T: Default,
{
  computed: AtomicUsize,
  value:    UnsafeCell<T>,
}

impl<T> MemoizedInvariant<T>
where
  T: Default,
{
  /// Create a new instance, which will be calculated on demand when `get()` is called.
  pub fn empty() -> MemoizedInvariant<T> {
    MemoizedInvariant {
      computed: AtomicUsize::new(0),
      value:    UnsafeCell::new(T::default()),
    }
  }

  /// Sets the value, if it becomes known through other means.
  pub fn set(&self, value: T) {
    self.computed.store(2, Release);
    unsafe {
      *self.value.get() = value;
    }
  }

  /// Create a new instance with a pre-computed result. `get()` will always return this result.
  #[allow(dead_code)]
  pub fn pre_computed(value: T) -> MemoizedInvariant<T> {
    MemoizedInvariant {
      computed: AtomicUsize::new(2),
      value:    UnsafeCell::new(value),
    }
  }

  /// Returns `true` if the value has already been computed
  pub fn is_computed(&self) -> bool {
    self.computed.load(Relaxed) == 2
  }

  /// The first time this is called, it performs the calculation in `calc_fn`. A cached
  /// result is returned thereafter, without repeating the call to `calc_fn`.
  pub fn get<F>(&self, calc_fn: F) -> &T
  where
    F: Fn() -> T,
  {
    unsafe {
      if self.is_computed() {
        // Already Computed
        &*self.value.get()
      } else {
        match self.computed.compare_exchange(0, 1, Acquire, Relaxed) {
          Ok(_) => {
            // We've obtained a lock; compute the invariant
            *self.value.get() = calc_fn();
            self.computed.store(2, Release);
            &*self.value.get()
          },
          Err(1) => {
            // Other thread is responsible; wait
            while self.computed.load(Relaxed) != 2 {
              core::hint::spin_loop();
              #[cfg(feature = "std")]
              std::thread::yield_now();
            }
            &*self.value.get()
          },
          Err(2) => {
            // Hash done already?! We probably got preempted?
            &*self.value.get()
          },
          Err(_) => unreachable!(),
        }
      }
    }
  }
}

impl<T> Default for MemoizedInvariant<T>
where
  T: Default,
{
  fn default() -> Self {
    Self::empty()
  }
}

impl<T> Clone for MemoizedInvariant<T>
where
  T: Clone + Default,
{
  fn clone(&self) -> Self {
    if self.is_computed() {
      Self {
        computed: AtomicUsize::new(2),
        value:    UnsafeCell::new(unsafe { (&*self.value.get()).clone() }),
      }
    } else {
      Self::empty()
    }
  }
}

impl<T> Debug for MemoizedInvariant<T>
where
  T: Default + Debug,
{
  fn fmt(&self, f: &mut Formatter) -> Result<(), core::fmt::Error> {
    let mut df = f.debug_struct("MemoizedInvariant");
    match self.computed.load(Relaxed) {
      0 => {
        df.field("status", &"empty");
      },
      1 => {
        df.field("status", &"calculating");
      },
      2 => {
        df.field("status", &"completed");
        df.field("value", unsafe { &*self.value.get() });
      },
      _ => {
        df.field("status", &"error");
      },
    }
    df.finish()
  }
}

unsafe impl<T> Sync for MemoizedInvariant<T> where T: Default {}

