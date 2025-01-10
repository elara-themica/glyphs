use crate::{
  zerocopy::{bounds_check, round_to_word, ZeroCopy, U32, U64},
  EncodedGlyph, FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType,
  ParsedGlyph, ToGlyph,
};
use alloc::boxed::Box;
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
  str::from_utf8,
  sync::atomic::{
    AtomicUsize,
    Ordering::{Relaxed, SeqCst},
  },
};
use icu_collator::{Collator, CollatorOptions};

pub(crate) static COLLATOR: DefaultCollator =
  DefaultCollator(AtomicUsize::new(0));

pub(crate) struct DefaultCollator(AtomicUsize);

impl DefaultCollator {
  pub(crate) fn get(&self) -> &'static Collator {
    unsafe {
      if self.0.load(Relaxed) == 0 {
        let options = CollatorOptions::new();
        let locale = Default::default();
        let c = Box::new(Collator::try_new(&locale, options).unwrap());
        let ptr = c.as_ref() as *const Collator;
        match self.0.compare_exchange(0, ptr as usize, SeqCst, SeqCst) {
          Ok(old) => {
            debug_assert_eq!(old, 0);
            Box::leak(c);
            &*ptr
          },
          Err(old) => {
            // Someone beat us here!  Let c go out of scope, use theirs.
            let ptr = old as *const Collator;
            &*ptr
          },
        }
      } else {
        let ptr = self.0.load(Relaxed) as *const Collator;
        &*ptr
      }
    }
  }
}

/// Human Languages (e.g., English, Spanish, etc...)
#[repr(u8)]
#[allow(non_camel_case_types)]
#[non_exhaustive]
#[allow(missing_docs)]
pub enum Language {
  None,
  Afrikaans_AF,
  Albanian_SQ,
  Amharic_AM,
  Arabic_AR,
  Armenian_HY,
  Assamese_AS,
  Azeri_AZ,
  Basque_EU,
  Belarusian_BE,
  Bengali,
  Bengali_BN,
  Bosnian_BS,
  Bulgarian_BG,
  Burmese_MY,
  Catalan_CA,
  Chinese_ZH,
  Croatian_HR,
  Czech_CS,
  Danish_DA,
  Divehi_DV,
  Dutch_NL,
  English_EN,
  Estonian_ET,
  FYRO_MK,
  Faroese_FO,
  Farsi_FA,
  Finnish_FI,
  French_FR,
  Gaelic,
  Gaelic_GD,
  Galician_GL,
  Georgian_KA,
  German_DE,
  Greek_EL,
  Guarani_GN,
  Gujarati_GU,
  Hebrew_HE,
  Hindi_HI,
  Hungarian_HU,
  Icelandic_IS,
  Indonesian_ID,
  Italian_it,
  Japanese_JA,
  Kannada_KN,
  Kashmiri_KS,
  Kazakh_KK,
  Khmer_KM,
  Korean_KO,
  Lao_LO,
  Latin_LA,
  Latvian_LV,
  Lithuanian_LT,
  Malay_MS,
  Malayalam_ML,
  Maltes_MTe,
  Maori_MI,
  Marathi_MR,
  Mongolian_MN,
  Nepali_NE,
  Norwegian_NB,
  Norwegian_NN,
  Oriya_OR,
  Polish_PL,
  Portuguese_PT,
  Punjabi_PA,
  RaetoRomance_RM,
  Romanian_RO,
  Russian_RU,
  Sanskrit_SA,
  Serbian_SR,
  Setsuana_TN,
  Sindhi_SD,
  Sinhala_SI,
  Slovak_SK,
  Slovenian_SL,
  Somali_SO,
  Sorbian_SB,
  Spanish_ES,
  Swahili_SW,
  Swedish_SV,
  Tajik_TG,
  Tamil_TA,
  Tatar_TT,
  Telugu_TE,
  Thai_TH,
  Tibetan_BO,
  Tsonga_TS,
  Turkish_TR,
  Turkmen_TK,
  Ukrainian_UK,
  Urdu_UR,
  Uzbek_UZ,
  Vietnamese_VI,
  Welsh_CY,
  Xhosa_XH,
  Yiddish_YI,
  Zulu_ZU,
}

/// These are full locales, language + region.  Currently, unimplemented.
///
// Populating this enum will require some care.  The first (least) significant
// byte will come from the language field, while the most significant two bits
// of the second byte will specify the encoding (and thus be masked off before
// reading this.  This means the value assigned to the full locale should match
// the language, leaving the upper byte to vary
///
/// Populating this enum will depend on the encoding of the [`StringG`]
/// type for the `u16` values and an external reference source for the list of
/// active language / location pairs.
#[allow(missing_docs, non_camel_case_types)]
#[non_exhaustive]
#[repr(u16)]
pub enum Locale {
  EN_US,
  EN_GB,
  EN_CA,
  EN_AU,
  EN_NZ,
  EN_IE,
  EN_ZA,
  EN_IN,
  EN_PH,
}

impl<'a> FromGlyph<ParsedGlyph<'a>> for &'a str {
  fn from_glyph(source: ParsedGlyph<'a>) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::String)?;
    let str_bytes = source.content_parsed();
    let valid_str = from_utf8(str_bytes)?;
    Ok(valid_str)
  }
}

impl ToGlyph for str {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    // SAFETY: So we can do one bounds check.
    unsafe {
      let str_bytes = self.as_bytes();
      let header = GlyphHeader::new(GlyphType::String, str_bytes.len())?;
      let bounds =
        round_to_word(*cursor + size_of::<GlyphHeader>() + str_bytes.len());
      bounds_check(target, bounds)?;
      let mut zero_idx = bounds - 8;
      U64::from(0).bbwr_u(target, &mut zero_idx);
      header.bbwr_u(target, cursor);
      u8::bbwrs_u(str_bytes, target, cursor);
      *cursor = round_to_word(*cursor);
      // pad_to_word_u(target, cursor);
    }
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    round_to_word(size_of::<GlyphHeader>() + self.len())
  }
}

#[cfg(feature = "alloc")]
impl<G> FromGlyph<G> for alloc::string::String
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::String)?;
    let bytes = source.content();
    let bytes_v = u8::bbrds_i(bytes, &mut 0)?;
    let valid_string = alloc::string::String::from_utf8(bytes_v)?;
    Ok(valid_string)
  }
}

#[cfg(feature = "alloc")]
impl ToGlyph for alloc::string::String {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    self.as_str().glyph_encode(target, cursor)
  }

  fn glyph_len(&self) -> usize {
    self.as_str().glyph_len()
  }
}

/// A glyph containing a valid UTF-8 string.
pub struct StringGlyph<G>(G)
where
  G: Glyph;

impl<G> StringGlyph<G>
where
  G: Glyph,
{
  /// The string contained in the glyph.
  pub fn get_str(&self) -> &str {
    let bytes = self.0.content();
    // Validity was already checked during `glyph_decode`.
    unsafe { core::str::from_utf8_unchecked(bytes) }
  }

  /// Returns the raw bytes of the string
  pub fn get_bytes(&self) -> &[u8] {
    self.0.content()
  }
}

impl<G> Debug for StringGlyph<G>
where
  G: Glyph,
{
  fn fmt(&self, f: &mut Formatter) -> Result<(), core::fmt::Error> {
    write!(f, "Utf8Glyph(\"{}\")", self.get_str())
  }
}

impl<G> FromGlyph<G> for StringGlyph<G>
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::String)?;
    // Check for valid UTF-8 string.
    let _ = from_utf8(source.content())?;
    Ok(StringGlyph(source))
  }
}

impl<G: Glyph> PartialEq for StringGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.get_str() == other.get_str()
  }
}

impl<G: Glyph> Eq for StringGlyph<G> {}

impl<G: Glyph> PartialOrd for StringGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for StringGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    let a = self.get_bytes();
    let b = other.get_bytes();
    let c = COLLATOR.get();
    c.compare_utf8(a, b)
  }
}

impl<G: Glyph> EncodedGlyph for StringGlyph<G> {
  fn glyph(&self) -> ParsedGlyph<'_> {
    self.0.borrow()
  }
}

impl<G> FromGlyph<G> for char
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::UnicodeChar)?;
    let value: u32 =
      U32::bbrd(&source.header().short_content()[..], &mut 0)?.into();
    match char::try_from(value) {
      Ok(c) => Ok(c),
      Err(_err) => Err(GlyphErr::IllegalValue),
    }
  }
}

impl ToGlyph for char {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let value = unsafe { core::mem::transmute::<&char, &[u8; 4]>(&self) };
    GlyphHeader::new_short(GlyphType::UnicodeChar, *value)
      .bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

/// A glyph containing a unicode character `char`.
pub struct CharGlyph<G: Glyph>(G);

impl<G: Glyph> CharGlyph<G> {
  /// The `char` contained by this glyph.
  pub fn get(&self) -> char {
    let bytes = self.0.header().short_content();
    // SAFETY: A valid value was confirmed when the CharGlyph was created.
    unsafe { char::from_u32_unchecked(u32::from_le_bytes(*bytes)) }
  }
}

impl<G: Glyph> FromGlyph<G> for CharGlyph<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::UnicodeChar)?;
    // Check for valid unicode char.
    let _value = <char>::from_glyph(source.borrow())?;
    Ok(CharGlyph(source))
  }
}

impl<G: Glyph> Debug for CharGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "CharGlyph({:?})", self.get())
  }
}

impl<G: Glyph> PartialEq for CharGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.get() == other.get()
  }
}

impl<G: Glyph> Eq for CharGlyph<G> {}

impl<G: Glyph> PartialOrd for CharGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for CharGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.get().cmp(&other.get())
  }
}

impl<G: Glyph> EncodedGlyph for CharGlyph<G> {
  fn glyph(&self) -> ParsedGlyph<'_> {
    self.0.borrow()
  }
}

#[cfg(test)]
#[allow(unused)]
mod tests {
  use super::*;
  use std::thread;

  #[test]
  fn icu_collation() {
    let names = [
      "Kaiden Alenko",
      "Jane Shepard",
      "Ashley Williams",
      "Garrus Vakarian",
      "Urdnox Wrex",
      "Tali vas Normandy",
      "Liara T'Soni",
    ];

    let c = COLLATOR.get();
    let result = c.compare(names[0], names[1]);
    std::dbg!(&result);
    let mut new_names = names.clone();
    new_names.sort_by(|a, b| c.compare(a, b));
    std::dbg!(&new_names);

    // Disabled long-running test for thread safety.
    // for _i in 0..2000 {
    //   thread::spawn(move || {
    //     let c = COLLATOR.get();
    //     for _ in 0..100_000 {
    //       let mut new_names = names.clone();
    //       new_names.sort_by(|a, b| c.compare(a, b));
    //     }
    //   });
    // }
  }
}
