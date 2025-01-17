use crate::{
  glyph::glyph_close,
  zerocopy::{bounds_check, round_to_word, ZeroCopy, U32, U64},
  EncodedGlyph, FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader,
  GlyphType, ParsedGlyph, ToGlyph,
};
use alloc::boxed::Box;
#[cfg(feature = "alloc")]
use alloc::string::String;
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

/// IDs for Human Languages (e.g., English, Spanish, etc...)
///
/// These were from the List of ISO 639 Language Codes, taken
/// from Wikipedia on 2025.01.10.
#[derive(Copy, Clone, Default, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[allow(missing_docs, non_camel_case_types)]
#[repr(u16)]
enum Language {
  #[default]
  Unknown = 0x0000,
  NonLinguistic = 0x0001,
  Abkhazian_AB = 0x0002,
  Afar_AA = 0x0003,
  Afrikaans_AF = 0x0004,
  Akan_AK = 0x0005,
  Albanian_SQ = 0x0006,
  Amharic_AM = 0x0007,
  Arabic_AR = 0x0008,
  Aragonese_AN = 0x0009,
  Armenian_HY = 0x000a,
  Assamese_AS = 0x000b,
  Avaric_AV = 0x000c,
  Avestan_AE = 0x000d,
  Aymara_AY = 0x000e,
  Azerbaijani_AZ = 0x000f,
  Bambara_BM = 0x0010,
  Bashkir_BA = 0x0011,
  Basque_EU = 0x0012,
  Belarusian_BE = 0x0013,
  Bengali_BN = 0x0014,
  Bislama_BI = 0x0015,
  Bosnian_BS = 0x0016,
  Breton_BR = 0x0017,
  Bulgarian_BG = 0x0018,
  Burmese_MY = 0x0019,
  Catalan_CA = 0x0053,
  CentralKhmer_KM = 0x001a,
  Chamorro_CH = 0x001b,
  Chechen_CE = 0x001c,
  Chichewa_NY = 0x001d,
  Chinese_ZH = 0x001e,
  ChurchSlavonic_CU = 0x001f,
  Chuvash_CV = 0x0020,
  Cornish_KW = 0x0021,
  Corsican_CO = 0x0022,
  Cree_CR = 0x0023,
  Croatian_HR = 0x0024,
  Czech_CS = 0x0025,
  Danish_DA = 0x0026,
  Divehi_DV = 0x0027,
  Dutch_NL = 0x0028,
  Dzongkha_DZ = 0x0029,
  English_EN = 0x002a,
  Esperanto_EO = 0x002b,
  Estonian_ET = 0x002c,
  Ewe_EE = 0x002d,
  Faroese_FO = 0x002e,
  Fijian_FJ = 0x002f,
  Finnish_FI = 0x0030,
  French_FR = 0x0032,
  Fulah_FF = 0x0033,
  Gaelic_GD = 0x0034,
  Galician_GL = 0x0035,
  Ganda_LG = 0x0036,
  Georgian_KA = 0x0037,
  German_DE = 0x0038,
  Greek_EL = 0x003a,
  Guarani_GN = 0x003b,
  Gujarati_GU = 0x003c,
  Haitian_HT = 0x003d,
  Hausa_HA = 0x003e,
  Hebrew_HE = 0x003f,
  Herero_HZ = 0x0040,
  Hindi_HI = 0x0041,
  HiriMotu_HO = 0x0042,
  Hungarian_HU = 0x0043,
  Icelandic_IS = 0x0044,
  Ido_IO = 0x0045,
  Igbo_IG = 0x0046,
  Indonesian_ID = 0x0047,
  Interlingua_IA = 0x0048,
  Interlingue_IE = 0x0049,
  Inuktitut_IU = 0x004a,
  Inupiaq_IK = 0x004b,
  Irish_GA = 0x004c,
  Italian_IT = 0x004d,
  Japanese_JA = 0x004e,
  Javanese_JV = 0x0039,
  Kalaallisut_KL = 0x004f,
  Kannada_KN = 0x0050,
  Kanuri_KR = 0x0051,
  Kashmiri_KS = 0x0052,
  Kazakh_KK = 0x0054,
  Kikuyu_KI = 0x0055,
  Kinyarwanda_RW = 0x0057,
  Komi_KV = 0x0058,
  Kongo_KG = 0x0059,
  Korean_KO = 0x005a,
  Kuanyama_KJ = 0x005b,
  Kurdish_KU = 0x0056,
  Kyrgyz_KY = 0x005c,
  Lao_LO = 0x005d,
  Latin_LA = 0x005e,
  Latvian_LV = 0x005f,
  Limburgan_LI = 0x0060,
  Lingala_LN = 0x0061,
  Lithuanian_LT = 0x0062,
  LubaKatanga_LU = 0x0063,
  Luxembourgish_LB = 0x0064,
  Macedonian_MK = 0x0065,
  Malagasy_MG = 0x0066,
  Malay_MS = 0x0067,
  Malayalam_ML = 0x0068,
  Maltese_MT = 0x0069,
  Manx_GV = 0x006a,
  Maori_MI = 0x006b,
  Marathi_MR = 0x006c,
  Marshallese_MH = 0x006d,
  Mongolian_MN = 0x006e,
  Nauru_NA = 0x006f,
  Navajo_NV = 0x0072,
  Ndonga_NG = 0x0073,
  Nepali_NE = 0x0070,
  NorthNdebele_ND = 0x0086,
  NorthernSami_SE = 0x0075,
  NorwegianBokmal_NB = 0x0076,
  NorwegianNynorsk_NN = 0x0074,
  Norwegian_NO = 0x0077,
  Occitan_OC = 0x0078,
  Ojibwa_OJ = 0x0079,
  Oriya_OR = 0x007a,
  Oromo_OM = 0x007b,
  Ossetian_OS = 0x007c,
  Pali_PI = 0x007d,
  Pashto_PS = 0x007e,
  Persian_FA = 0x007f,
  Polish_PL = 0x0080,
  Portuguese_PT = 0x0081,
  Punjabi_PA = 0x0082,
  Romanian_RO = 0x0083,
  Romansh_RM = 0x0084,
  Rundi_RN = 0x0085,
  Russian_RU = 0x0087,
  Samoan_SM = 0x0088,
  Sango_SG = 0x0089,
  Sanskrit_SA = 0x008a,
  Sardinian_SC = 0x008b,
  Serbian_SR = 0x008c,
  Shona_SN = 0x00b1,
  SichuanYi_II = 0x008d,
  Sindhi_SD = 0x008e,
  Sinhala_SI = 0x008f,
  Slovak_SK = 0x0090,
  Slovenian_SL = 0x0091,
  Somali_SO = 0x0071,
  SouthNdebele_NR = 0x0092,
  SouthernSotho_ST = 0x0093,
  Spanish_ES = 0x0094,
  Sudanese_SU = 0x0095,
  Swahili_SW = 0x0096,
  Swati_SS = 0x0097,
  Tagalog_TL = 0x0098,
  Tahitian_TY = 0x0099,
  Tajik_TG = 0x009a,
  Tamil_TA = 0x009b,
  Tatar_TT = 0x009c,
  Telugu_TE = 0x009d,
  Thai_TH = 0x009e,
  Tibetan_BO = 0x009f,
  Tigrinya_TI = 0x00a0,
  Tonga_TO = 0x00a1,
  Tsonga_TS = 0x00a2,
  Tswana_TN = 0x00a3,
  Turkish_TR = 0x00a4,
  Turkmen_TK = 0x00a5,
  Twi_TW = 0x00a6,
  Uighur_UG = 0x00a7,
  Ukrainian_UK = 0x00a8,
  Urdu_UR = 0x00a9,
  Uzbek_UZ = 0x00aa,
  Venda_VE = 0x00ab,
  Vietnamese_VI = 0x00ac,
  Volapuk_VO = 0x00ad,
  Walloon_WA = 0x00ae,
  Welsh_CY = 0x0031,
  WesternFrisian_FY = 0x00af,
  Wolof_WO = 0x00b0,
  Xhosa_XH = 0x00b2,
  Yiddish_YI = 0x00b3,
  Yoruba_YO = 0x00b4,
  Zhuang_ZA = 0x00b5,
  Zulu_ZU = 0x00b6,
}

#[derive(Copy, Clone, Default, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[allow(missing_docs, non_camel_case_types)]
#[repr(u8)]
pub enum StringDirection {
  #[default]
  Unspecified = 0,
  Auto = 1,
  LeftToRight = 2,
  RightToLeft = 3,
}

/// Writes a string glyph.
///
/// A generic function, as there are several string types, which do not always
/// include all the information.
///
/// - If both are present, `locale` will overwrite `lang`.
fn str_glyph_encode<S: AsRef<[u8]>>(
  content: &S,
  language: Option<Language>,
  direction: Option<StringDirection>,
  target: &mut [u8],
  cursor: &mut usize,
) -> Result<(), GlyphErr> {
  let language = language.unwrap_or_default();
  let direction = direction.unwrap_or_default();

  let glyph_offset = *cursor;
  *cursor += size_of::<GlyphHeader>();
  (language as u8).bbwr(target, cursor)?;
  ((direction as u8) << 6).bbwr(target, cursor)?;
  u8::bbwrs(content.as_ref(), target, cursor)?;
  glyph_close(GlyphType::String, target, glyph_offset, cursor, true)
}

fn str_glyph_len<S: AsRef<[u8]>>(content: &S) -> usize {
  size_of::<GlyphHeader>() + round_to_word(2 + content.as_ref().len())
}

impl<'a> FromGlyph<ParsedGlyph<'a>> for &'a str {
  fn from_glyph(
    source: ParsedGlyph<'a>,
  ) -> Result<Self, FromGlyphErr<ParsedGlyph<'a>>> {
    if let Err(err) = source.header().confirm_type(GlyphType::String) {
      return Err(err.into_fge(source));
    }
    let str_bytes = source.content_parsed();
    let valid_str = match from_utf8(str_bytes) {
      Ok(valid_str) => valid_str,
      Err(err) => return Err(FromGlyphErr::new(source, err.into())),
    };
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
impl<G> FromGlyph<G> for String
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = source.header().confirm_type(GlyphType::String) {
      return Err(err.into_fge(source));
    }
    let bytes = source.content();
    let bytes_v = match u8::bbrds_i(bytes, &mut 0) {
      Ok(bytes_v) => bytes_v,
      Err(err) => return Err(err.into_fge(source)),
    };
    let valid_string = match String::from_utf8(bytes_v) {
      Ok(valid_string) => valid_string,
      Err(err) => return Err(FromGlyphErr::new(source, err.into())),
    };
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
  fn from_glyph(source: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = source.header().confirm_type(GlyphType::String) {
      return Err(err.into_fge(source));
    }

    // Check for valid UTF-8 string.
    if let Err(err) = from_utf8(source.content()) {
      return Err(FromGlyphErr::new(source, err.into()));
    }
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
  fn from_glyph(source: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = source.header().confirm_type(GlyphType::UnicodeChar) {
      return Err(err.into_fge(source));
    }
    let value: u32 =
      match U32::bbrd(&source.header().short_content()[..], &mut 0) {
        Ok(value) => value.into(),
        Err(err) => return Err(err.into_fge(source)),
      };
    match char::try_from(value) {
      Ok(c) => Ok(c),
      Err(_err) => Err(FromGlyphErr::new(source, GlyphErr::IllegalValue)),
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
  fn from_glyph(source: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = source.header().confirm_type(GlyphType::UnicodeChar) {
      return Err(err.into_fge(source));
    }
    // Check for valid unicode char.
    unsafe {
      if let Err(err) = <char>::from_glyph(source.borrow().detach()) {
        return Err(FromGlyphErr::new(source, err.into()));
      }
    }
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
