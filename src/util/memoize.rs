use alloc::boxed::Box;
use core::{
  cell::UnsafeCell,
  fmt::{Debug, Formatter},
  marker::PhantomData,
  sync::atomic::{
    AtomicUsize, Ordering,
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

#[cfg(feature = "alloc")]
pub struct BoxedMemoizedInvariant<T> {
  ptr:      AtomicUsize,
  _phantom: PhantomData<T>,
}

#[cfg(feature = "alloc")]
impl<T> BoxedMemoizedInvariant<T>
where
  T: Copy,
{
  /// Returns `true` iff a value has already been computed and stored.
  pub fn is_computed(&self) -> bool {
    self.ptr.load(Relaxed) != 0
  }

  /// If a memoized value has been previously stored, return a reference.
  ///
  /// This function is not guaranteed to return [`Some`] even after a call to
  /// `set()` because that function may fail.
  pub fn get<F>(&self, calc_fn: F) -> T
  where
    F: FnOnce() -> T,
  {
    unsafe {
      // First, we'll try to reference the existing value, if it's already been
      // calculated.
      let current = self.ptr.load(Relaxed);
      if current != 0 {
        *(current as *const T)
      } else {
        // Otherwise, we'll have to calculate it and store the result.
        let value: T = calc_fn();
        if let Ok(boxed) = Box::try_new(value) {
          let as_ptr: *mut T = Box::into_raw(boxed);
          if let Err(_) = self.ptr.compare_exchange(
            0,
            as_ptr as usize,
            Ordering::SeqCst,
            Ordering::SeqCst,
          ) {
            // Re-create the box so it get dropped.
            let _boxed = Box::from_raw(as_ptr);
          }
        }
        value
      }
    }
  }
}

#[cfg(feature = "alloc")]
impl<T> BoxedMemoizedInvariant<T>
where
  T: Copy,
{
  pub fn pre_computed(value: T) -> Self {
    if let Ok(boxed) = Box::try_new(value) {
      let as_ptr = Box::into_raw(boxed);
      Self {
        ptr:      AtomicUsize::new(as_ptr as usize),
        _phantom: Default::default(),
      }
    } else {
      Default::default()
    }
  }
}

#[cfg(feature = "alloc")]
impl<T> Clone for BoxedMemoizedInvariant<T>
where
  T: Copy + Clone,
{
  fn clone(&self) -> Self {
    let ptr = self.ptr.load(Ordering::Relaxed) as *const T;
    if !ptr.is_null() {
      let cloned = unsafe { (*ptr).clone() };
      Self::pre_computed(cloned)
    } else {
      Default::default()
    }
  }
}

#[cfg(feature = "alloc")]
impl<T> Debug for BoxedMemoizedInvariant<T>
where
  T: Debug,
{
  fn fmt(&self, f: &mut Formatter) -> Result<(), core::fmt::Error> {
    write!(f, "BoxedMemoizedInvariant: {{ ")?;
    let ptr = self.ptr.load(Ordering::Relaxed) as *const T;
    if ptr.is_null() {
      writeln!(f, "not computed }}")?;
    } else {
      let val = unsafe { &*ptr };
      writeln!(f, "{:?} }}", &val)?;
    }
    Ok(())
  }
}

#[cfg(feature = "alloc")]
impl<T> Default for BoxedMemoizedInvariant<T> {
  fn default() -> Self {
    Self {
      ptr:      Default::default(),
      _phantom: Default::default(),
    }
  }
}

#[cfg(feature = "alloc")]
impl<T> Drop for BoxedMemoizedInvariant<T> {
  fn drop(&mut self) {
    let cur_ptr = self.ptr.load(Ordering::Relaxed);
    if cur_ptr != 0 {
      // Create box so it's dropped.
      let _boxed = unsafe { Box::from_raw(cur_ptr as *mut T) };
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use ::test::Bencher;
  use std::println;

  #[derive(Debug)]
  struct HasMemoizedValue {
    base:      u64,
    multiples: MemoizedInvariant<[u64; 8]>,
  }

  impl HasMemoizedValue {
    fn calculate_multiples(&self) -> &[u64; 8] {
      self.multiples.get(|| {
        [
          self.base,
          self.base * 2,
          self.base * 3,
          self.base * 4,
          self.base * 5,
          self.base * 6,
          self.base * 7,
          self.base * 8,
        ]
      })
    }
  }

  #[bench]
  fn memoized_invariant(b: &mut Bencher) {
    // Test portion
    let hmv = HasMemoizedValue {
      base:      256,
      multiples: MemoizedInvariant::empty(),
    };
    println!("Before memoized call: {:?}", &hmv);
    let multiples = hmv.calculate_multiples();
    println!("Calculated multiples as: {:?}", multiples);
    println!("After memoized call: {:?}", &hmv);

    // Bench portion
    let mut sum: u64 = 0;
    b.iter(|| {
      for _ in 0..16 {
        let hmv = HasMemoizedValue {
          base:      256,
          multiples: MemoizedInvariant::empty(),
        };
        sum += hmv.base;
      }
    });
    println!("Sum was {:?}", &sum);
  }

  #[test]
  #[cfg(feature = "alloc")]
  fn boxed_memoized_invariant() {
    let b = BoxedMemoizedInvariant::default();
    let val = b.get(|| 5);
    assert_eq!(val, 5);

    // Shouldn't re-compute
    let val = b.get(|| 6);
    assert_eq!(val, 5);
  }
}
