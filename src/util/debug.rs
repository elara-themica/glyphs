use core::fmt::{Debug, Display, Formatter, Write};

/// A container for `&[u8]` that formats itself as a hex dump on output via
/// [`Debug`] and [`Display`].
pub(crate) struct HexDump<'a>(pub &'a [u8]);

impl<'a> From<&'a [u8]> for HexDump<'a> {
  fn from(src: &'a [u8]) -> Self {
    HexDump(src)
  }
}

#[cfg(feature = "alloc")]
impl<'a> Display for HexDump<'a> {
  fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
    Debug::fmt(self, f)
  }
}

#[cfg(feature = "alloc")]
impl<'a> Debug for HexDump<'a> {
  fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
    extern crate alloc;
    use alloc::{format, string::String};

    let mut b = f.debug_struct("[u8]");
    let mut line = String::with_capacity(100);
    let mut start = 0usize;

    for (count, &byte) in self.0.iter().enumerate() {
      // End of line
      if (count % 32) == 0 && count != 0 {
        let linenum = format!("{:04X?}", start);
        b.field(linenum.as_str(), &line.as_str());
        start += 32;
        line.clear();
      }
      if (count % 8) == 0 && count != start {
        write!(&mut line, " ")?;
      }
      if (count % 4) == 0 && count != start {
        write!(&mut line, " ")?;
      }
      write!(&mut line, "{:02X?}", byte)?;
    }
    // Last remaining line
    if line.len() != 0 {
      let linenum = format!("{:04X?}", start);
      b.field(linenum.as_str(), &line.as_str());
    }

    b.finish()
  }
}

/// Hex dump for short (i.e., single-line) byte strings.
///
/// The output will be a continuous string of hex digits, interleaved by a `:`
/// character every `self.1` bytes.
pub(crate) struct ShortHexDump<'a>(pub &'a [u8], pub usize);

impl<'a> Debug for ShortHexDump<'a> {
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    for (i, byte) in self.0.iter().enumerate() {
      if self.1 != 0 {
        if i != 0 && (i % self.1) == 0 && i != self.0.len() - 1 {
          write!(f, ":")?;
        }
      }
      write!(f, "{:02X}", byte)?;
    }
    Ok(())
  }
}

impl<'a> Display for ShortHexDump<'a> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    Debug::fmt(self, f)
  }
}

pub(crate) struct DebugIter<T>(T)
where
  T: Iterator + Clone,
  T::Item: Debug;

impl<T> DebugIter<T>
where
  T: Iterator + Clone,
  T::Item: Debug,
{
  pub(crate) fn new(iter: T) -> DebugIter<T> {
    DebugIter(iter)
  }
}

impl<T> Debug for DebugIter<T>
where
  T: Iterator + Clone,
  T::Item: Debug,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_list();
    for item in self.0.clone() {
      df.entry(&item);
    }
    df.finish()
  }
}

pub(crate) trait CloneDebugIterator: Iterator + Clone
where
  <Self as Iterator>::Item: Debug,
{
  fn clone_debug(&self) -> DebugIter<Self>
  where
    Self: Sized,
  {
    DebugIter(self.clone())
  }
}

impl<T> CloneDebugIterator for T
where
  T: Iterator + Clone,
  T::Item: Debug,
{
}

pub(crate) struct SimpleMapDebug<K: Debug, V: Debug>(pub K, pub V);

impl<K: Debug, V: Debug> Debug for SimpleMapDebug<K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "{:?} -> {:?}", &self.0, &self.1)
  }
}
