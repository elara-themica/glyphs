use crate::{
  zerocopy::{ZeroCopy, I128},
  EncodedGlyph, FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader,
  GlyphSorting, GlyphType, ParsedGlyph, ToGlyph,
};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
};
#[cfg(feature = "std")]
use std::time::SystemTime;

const DATE_TIME_GLYPH_LEN: usize = size_of::<GlyphHeader>() + size_of::<i128>();

/// Describes a specific date and time, with nanosecond precision.
pub struct DateTimeGlyph<G: Glyph>(G);

impl<G: Glyph> DateTimeGlyph<G> {
  /// Returns the number of nanoseconds since the unix epoch (Jan 1, 1970 00:00)
  pub fn timestamp(&self) -> i128 {
    // SAFETY: FromGlyph has guaranteed the content length for us.
    let content = self.0.content_padded();
    unsafe { I128::bbrd_u(content, &mut 0).get() }
  }

  /// Convert
  #[cfg(feature = "chrono")]
  pub fn get_chrono_date_time(
    &self,
  ) -> Result<chrono::DateTime<chrono::Utc>, GlyphErr> {
    let ts = self.timestamp();
    let secs = ts / 1_000_000_000;
    let nanos = (ts % 1_000_000_000) as u32;
    match i64::try_from(secs) {
      Ok(secs) => {
        let dt =
          chrono::DateTime::<chrono::Utc>::from_timestamp(secs, nanos).unwrap();
        Ok(dt)
      },
      Err(_err) => Err(GlyphErr::DateTimeOverflow(ts)),
    }
  }
}

impl<G: Glyph> FromGlyph<G> for DateTimeGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = glyph.confirm_type(GlyphType::DateTime) {
      return Err(err.into_fge(glyph));
    }
    // SAFETY: We're going to guarantee that the content is exactly 16 bytes.
    //         This guarantee is used in Self::timestamp().
    if glyph.content().len() != size_of::<i128>() {
      Err(GlyphErr::InvalidDateTime.into_fge(glyph))
    } else {
      Ok(DateTimeGlyph(glyph))
    }
  }
}

fn timestamp_to_glyph(
  target: &mut [u8],
  cursor: &mut usize,
  timestamp: i128,
) -> Result<(), GlyphErr> {
  let nanos = I128::from(timestamp);
  let header = GlyphHeader::new(GlyphType::DateTime, size_of::<i128>())?;
  header.bbwr(target, cursor)?;
  nanos.bbwr(target, cursor)?;
  Ok(())
}

#[cfg(feature = "std")]
impl ToGlyph for SystemTime {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    // Convert into nanos since epoch
    let timestamp: i128 = match self.cmp(&SystemTime::UNIX_EPOCH) {
      Ordering::Greater => {
        let duration = self.duration_since(SystemTime::UNIX_EPOCH).unwrap();
        duration.as_nanos() as i128
      },
      Ordering::Less => {
        let duration = SystemTime::UNIX_EPOCH.duration_since(*self).unwrap();
        (0 - duration.as_nanos()) as i128
      },
      Ordering::Equal => 0,
    };
    timestamp_to_glyph(target, cursor, timestamp)
  }

  fn glyph_len(&self) -> usize {
    DATE_TIME_GLYPH_LEN
  }
}

impl<G: Glyph> PartialEq for DateTimeGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Glyph> Eq for DateTimeGlyph<G> {}

impl<G: Glyph> PartialOrd for DateTimeGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for DateTimeGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.glyph_ord(other, Default::default())
  }
}

impl<G: Glyph> Debug for DateTimeGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    if cfg!(feature = "chrono") {
      match self.get_chrono_date_time() {
        Ok(time) => write!(f, "DateTimeGlyph({:?})", time)?,
        Err(_) => write!(f, "DateTimeGlyph({:?})", self.timestamp())?,
      }
    } else {
      write!(f, "DateTimeGlyph({:?})", self.timestamp())?
    };
    Ok(())
  }
}

impl<G: Glyph> EncodedGlyph<G> for DateTimeGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> ParsedGlyph<'_> {
    self.0.borrow()
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    match sorting {
      GlyphSorting::ByteOrder => self
        .0
        .borrow()
        .content_padded()
        .cmp(&other.0.borrow().content_padded()),
      GlyphSorting::Experimental => self.timestamp().cmp(&other.timestamp()),
    }
  }
}

#[cfg(feature = "std")]
impl<G: Glyph> FromGlyph<G> for SystemTime {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    let dtg = DateTimeGlyph::from_glyph(glyph)?;
    let ts = dtg.timestamp();
    match ts.cmp(&0) {
      Ordering::Less => {
        let ts = 0 - ts;
        let secs = ts / 1_000_000_000;
        if secs > u64::MAX as i128 {
          Err(GlyphErr::DateTimeOverflow(0 - ts).into_fge(dtg.into_inner()))
        } else {
          let secs = secs as u64;
          let nanos = (ts % 1_000_000_000) as u32;
          let duration = std::time::Duration::new(secs, nanos);
          match SystemTime::UNIX_EPOCH.checked_sub(duration) {
            None => {
              Err(GlyphErr::DateTimeOverflow(0 - ts).into_fge(dtg.into_inner()))
            },
            Some(time) => Ok(time),
          }
        }
      },
      Ordering::Greater => {
        let secs = ts / 1_000_000_000;
        if secs > u64::MAX as i128 {
          Err(GlyphErr::DateTimeOverflow(ts).into_fge(dtg.into_inner()))
        } else {
          let secs = secs as u64;
          let nanos = (ts % 1_000_000_000) as u32;
          let duration = std::time::Duration::new(secs, nanos);
          match SystemTime::UNIX_EPOCH.checked_add(duration) {
            None => {
              Err(GlyphErr::DateTimeOverflow(ts).into_fge(dtg.into_inner()))
            },
            Some(time) => Ok(time),
          }
        }
      },
      Ordering::Equal => Ok(SystemTime::UNIX_EPOCH),
    }
  }
}

#[cfg(feature = "chrono")]
impl<TZ: chrono::TimeZone> ToGlyph for chrono::DateTime<TZ> {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let secs = self.timestamp() as i128 * 1_000_000_000;
    let nanos = self.timestamp_subsec_nanos() as i128;
    let timestamp = secs + nanos;
    timestamp_to_glyph(target, cursor, timestamp)
  }

  fn glyph_len(&self) -> usize {
    DATE_TIME_GLYPH_LEN
  }
}

#[cfg(feature = "chrono")]
impl<G: Glyph> FromGlyph<G> for chrono::DateTime<chrono::Utc> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    let dtg = DateTimeGlyph::from_glyph(glyph)?;
    match dtg.get_chrono_date_time() {
      Ok(time) => Ok(time),
      Err(err) => Err(err.into_fge(dtg.into_inner())),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::glyph_new;
  use chrono::DateTime;
  use std::dbg;

  #[test]
  fn date_time() {
    let dt = SystemTime::now();
    dbg!(&dt);
    let dtg = glyph_new(&dt).unwrap();
    dbg!(&dtg);
    let dt2 = SystemTime::from_glyph(dtg.borrow()).unwrap();
    dbg!(&dt2);
    assert_eq!(dt, dt2);
    let dt3 = DateTime::<chrono::Utc>::from_glyph(dtg.borrow()).unwrap();
    dbg!(&dt3);
    let dt4 = DateTimeGlyph::from_glyph(dtg.borrow()).unwrap();
    dbg!(&dt4);
  }
}
