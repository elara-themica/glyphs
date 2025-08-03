use crate::{
  zerocopy::{pad_to_word, round_to_word, ZeroCopy, U16, U32},
  DecodeErr, EncodedGlyph, FromGlyph, Glyph, GlyphErr, GlyphHeader,
  GlyphSorting, GlyphType, ToGlyph,
};
use alloc::boxed::Box;
#[cfg(feature = "alloc")]
use alloc::string::String;
use core::{
  cell::UnsafeCell,
  cmp::Ordering,
  fmt::{Debug, Formatter},
  ops::Deref,
  str::{from_utf8, from_utf8_unchecked},
  sync::atomic::{
    AtomicUsize,
    Ordering::{Relaxed, SeqCst},
  },
};
use icu_collator::{Collator, CollatorOptions};

pub(crate) static COLLATOR: StringCollator =
  StringCollator(AtomicUsize::new(0));

#[cfg(feature = "alloc")]
pub struct LocalizedString {
  language:  Language,
  direction: StringDirection,
  content:   String,
}

#[cfg(feature = "alloc")]
impl LocalizedString {
  /// Creates a new localized string
  pub fn new(
    language: Language,
    direction: StringDirection,
    content: String,
  ) -> Self {
    Self {
      language,
      direction,
      content,
    }
  }

  /// Returns the natural language in which the string is written
  pub fn language(&self) -> Language {
    self.language
  }

  /// Returns the direction in which the string is written
  pub fn direction(&self) -> StringDirection {
    self.direction
  }

  /// Returns the contents of the string
  pub fn content(&self) -> &str {
    &self.content
  }

  /// Sets the natural language in which the string is written
  pub fn set_language(&mut self, language: Language) {
    self.language = language;
  }

  /// Sets the direction in which the string is written
  pub fn set_direction(&mut self, direction: StringDirection) {
    self.direction = direction;
  }

  /// Sets the content of the string
  pub fn set_content(&mut self, content: String) {
    self.content = content;
  }
}

#[cfg(feature = "alloc")]
impl ToGlyph for LocalizedString {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    str_glyph_encode(
      self.content.as_bytes(),
      Some(self.language),
      Some(self.direction),
      target,
      cursor,
    )
  }

  fn glyph_len(&self) -> usize {
    str_glyph_len(self.content.as_bytes().len())
  }
}

pub struct LocalizedStr<'a> {
  language:  Language,
  direction: StringDirection,
  content:   &'a str,
}

impl<'a> LocalizedStr<'a> {
  /// Creates a new localized string
  pub fn new(
    language: Language,
    direction: StringDirection,
    content: &'a str,
  ) -> Self {
    Self {
      language,
      direction,
      content,
    }
  }

  /// Returns the natural language in which the string is written
  pub fn language(&self) -> Language {
    self.language
  }

  /// Returns the direction in which the string is written
  pub fn direction(&self) -> StringDirection {
    self.direction
  }

  /// Returns the contents of the string
  pub fn content(&self) -> &str {
    &self.content
  }

  /// Sets the natural language in which the string is written
  pub fn set_language(&mut self, language: Language) {
    self.language = language;
  }

  /// Sets the direction in which the string is written
  pub fn set_direction(&mut self, direction: StringDirection) {
    self.direction = direction;
  }

  /// Sets the content of the string
  pub fn set_content(&mut self, content: &'a str) {
    self.content = content;
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for LocalizedStr<'static> {
  type Error = GlyphErr;

  fn from_glyph(glyph: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    todo!()
  }
}

impl<'a> ToGlyph for LocalizedStr<'a> {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    str_glyph_encode(
      self.content.as_bytes(),
      Some(self.language),
      Some(self.direction),
      target,
      cursor,
    )
  }

  fn glyph_len(&self) -> usize {
    str_glyph_len(self.content.as_bytes().len())
  }
}

#[cfg(feature = "alloc")]
impl<'a> From<&'a LocalizedString> for LocalizedStr<'a> {
  fn from(source: &'a LocalizedString) -> Self {
    Self {
      language:  source.language(),
      direction: source.direction(),
      content:   source.content(),
    }
  }
}

#[cfg(feature = "alloc")]
impl<'a, 'b> From<&'a LocalizedStr<'b>> for LocalizedString {
  fn from(value: &'a LocalizedStr<'b>) -> Self {
    LocalizedString::new(
      value.language,
      value.direction,
      String::from(value.content),
    )
  }
}

/// A glyph containing a valid UTF-8 string.
pub struct StringGlyph<G>
where
  G: Deref<Target = Glyph>,
{
  glyph:      G,
  valid_utf8: UnsafeCell<bool>,
}

impl<G> StringGlyph<G>
where
  G: Deref<Target = Glyph>,
{
  /// The language in which the string is written.
  pub fn language(&self) -> Language {
    match StringMetadata::bbrf(self.glyph.content_padded(), &mut 0) {
      Ok(md) => md.language(),
      Err(_err) => Language::Unknown,
    }
  }

  /// The direction of the text (i.e., left-to-right, etc...)
  pub fn direction(&self) -> StringDirection {
    match StringMetadata::bbrf(self.glyph.content_padded(), &mut 0) {
      Ok(md) => md.direction(),
      Err(_err) => StringDirection::Unspecified,
    }
  }

  /// Returns the raw bytes of the string
  pub fn get_str_bytes(&self) -> &[u8] {
    let metadata_len = size_of::<StringMetadata>();
    match self.glyph.content().get(metadata_len..) {
      None => &[],
      Some(bytes) => bytes,
    }
  }

  /// Returns the value as a valid UTF-8 [`str`], or an error if glyph does
  /// not contain only valid UTF-8.
  pub fn get_str(&self) -> Result<&str, GlyphErr> {
    match self.glyph.content().get(2..) {
      None => Ok(""),
      Some(bytes) => {
        // SAFETY: The only impact of a data race here is duplicated work.
        unsafe {
          match *self.valid_utf8.get() {
            true => Ok(from_utf8_unchecked(bytes)),
            false => match from_utf8(bytes) {
              Ok(string) => {
                *self.valid_utf8.get() = true;
                Ok(string)
              },
              Err(err) => Err(err.into()),
            },
          }
        }
      },
    }
  }
}

impl<G> Debug for StringGlyph<G>
where
  G: Deref<Target = Glyph>,
{
  fn fmt(&self, f: &mut Formatter) -> Result<(), core::fmt::Error> {
    write!(f, "StringGlyph(\"{}\")", self.deref())
  }
}

impl<G> Deref for StringGlyph<G>
where
  G: Deref<Target = Glyph>,
{
  type Target = str;

  fn deref(&self) -> &Self::Target {
    match self.glyph.content().get(2..) {
      None => {
        // Empty String
        ""
      },
      Some(bytes) => {
        // Validity was already checked during `glyph_decode`.
        unsafe { core::str::from_utf8_unchecked(bytes) }
      },
    }
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for StringGlyph<G> {
  fn into_inner(self) -> G {
    self.glyph
  }

  fn glyph(&self) -> &Glyph {
    &self.glyph.deref()
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    match sorting {
      GlyphSorting::TypeAndBytes => self
        .language()
        .cmp(&other.language())
        .then(self.direction().cmp(&other.direction()))
        .then(self.get_str_bytes().cmp(other.get_str_bytes())),
      GlyphSorting::Experimental => {
        let collator = COLLATOR.get();
        self
          .language()
          .cmp(&other.language())
          .then(self.direction().cmp(&other.direction()))
          .then(
            collator.compare_utf8(self.get_str_bytes(), other.get_str_bytes()),
          )
      },
    }
  }
}

impl<G: Deref<Target = Glyph>> Eq for StringGlyph<G> {}

impl<G> FromGlyph<G> for StringGlyph<G>
where
  G: Deref<Target = Glyph>,
{
  type Error = GlyphErr;

  fn from_glyph(source: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    // Decoding is infallible; StringGlyph handles any (or no) content values.
    let decode_result = (|| {
      source.header().confirm_type(GlyphType::String)?;
      Result::<_, GlyphErr>::Ok(())
    })();

    match decode_result {
      Ok(()) => Ok(StringGlyph {
        glyph:      source,
        valid_utf8: UnsafeCell::new(false),
      }),
      Err(err) => Err(DecodeErr::new(source, err)),
    }
  }
}

impl<G: Deref<Target = Glyph>> Ord for StringGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self
      .language()
      .cmp(&other.language())
      .then(self.direction().cmp(&other.direction()))
      .then_with(|| {
        let a = self.get_str_bytes();
        let b = other.get_str_bytes();
        let c = COLLATOR.get();
        c.compare_utf8(a, b)
      })
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for StringGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.glyph.content() == other.glyph.content()
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for StringGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

/// IDs for Human Languages (e.g., English, Spanish, etc...)
///
/// These were from the List of ISO 639 Language Codes, taken
/// from Wikipedia on 2025.01.10.
///
/// These language identifiers are encoded as the first 14 bits of a
/// [`StringGlyph`].
// SAFETY: When updating this list, you must ensure that (1) the implementation
// of From<u16> is updated to reflect the highest known value and (2) that all
// possible lower numbered identifiers have an entry in this enum.
#[derive(Copy, Clone, Default, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[allow(missing_docs, non_camel_case_types)]
#[repr(u16)]
#[non_exhaustive]
pub enum Language {
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

impl From<u16> for Language {
  fn from(value: u16) -> Self {
    if value > Self::Zhuang_ZA as u16 {
      Self::Unknown
    } else {
      // SAFETY: There are contiguous known/specified values
      unsafe { std::mem::transmute(value) }
    }
  }
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

impl From<u8> for StringDirection {
  fn from(value: u8) -> Self {
    if value > Self::RightToLeft as u8 {
      Self::Unspecified
    } else {
      // SAFETY: There are contiguous known/specified values
      unsafe { std::mem::transmute(value) }
    }
  }
}

#[derive(Copy, Clone)]
struct StringMetadata(U16);

impl StringMetadata {
  fn language(&self) -> Language {
    let id = self.0.get() & 0b0001_1111_1111_1111;
    Language::from(id)
  }

  fn direction(&self) -> StringDirection {
    let id = (self.0.get() >> 14) as u8;
    StringDirection::from(id)
  }

  fn new(
    language: Option<Language>,
    direction: Option<StringDirection>,
  ) -> StringMetadata {
    let language = language.unwrap_or_default();
    let direction = direction.unwrap_or_default();
    let lang_id = language as u16 & 0b0001_1111_1111_1111;
    let dir_id = direction as u8 & 0b0000_0111;

    let value = lang_id | ((dir_id as u16) << 14);
    StringMetadata(U16::from(value))
  }
}

unsafe impl ZeroCopy for StringMetadata {}

/// A glyph containing a Unicode character `char`.
pub struct CharGlyph<G: Deref<Target = Glyph>>(G);

impl<G: Deref<Target = Glyph>> CharGlyph<G> {
  /// The code point encoded by this `CharGlyph`.
  pub fn code_point(&self) -> u32 {
    let bytes = self.0.header().short_content();
    u32::from_le_bytes(*bytes)
  }
}

impl<G: Deref<Target = Glyph>> CharGlyph<G> {
  /// The `char` contained by this glyph.
  // TODO: Docs
  pub fn get(&self) -> Result<char, GlyphErr> {
    let bytes = self.0.header().short_content();
    let code_point = u32::from_le_bytes(*bytes);
    match char::from_u32(code_point) {
      None => Err(GlyphErr::UnicodeCharIllegalCodepoint(code_point)),
      Some(c) => Ok(c),
    }
  }
}

impl<G: Deref<Target = Glyph>> Debug for CharGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    match self.get() {
      Ok(c) => write!(f, "CharGlyph({:?})", &c),
      Err(err) => write!(f, "CharGlyph({:?})", &err),
    }
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for CharGlyph<G> {
  type Error = GlyphErr;

  fn from_glyph(source: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    let decode_result = (|| {
      source.header().confirm_type(GlyphType::UnicodeChar)?;
      if !source.header().is_short() {
        Err(GlyphErr::UnicodeCharInvalidGlyphLen(source.as_ref().len()))
      } else {
        Result::<(), GlyphErr>::Ok(())
      }
    })();

    match decode_result {
      Ok(()) => Ok(CharGlyph(source)),
      Err(err) => Err(DecodeErr::new(source, err)),
    }
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for CharGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.get() == other.get()
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for CharGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> &Glyph {
    &self.0.deref()
  }
}

impl<G: Deref<Target = Glyph>> Eq for CharGlyph<G> {}

impl<G: Deref<Target = Glyph>> PartialOrd for CharGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Deref<Target = Glyph>> Ord for CharGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.code_point().cmp(&other.code_point())
  }
}

pub enum StringGlyphErr {}

pub(crate) struct StringCollator(AtomicUsize);

impl StringCollator {
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

// impl<G> FromGlyph<G> for char
// where
//   G: Deref<Target = Glyph>,
// {
//   fn from_glyph(source: G) -> Result<Self, FromGlyphErr<G>> {
//     if let Err(err) = source.header().confirm_type(GlyphType::UnicodeChar) {
//       return Err(err.into_fge(source));
//     }
//     let value: u32 =
//       match U32::bbrd(&source.header().short_content()[..], &mut 0) {
//         Ok(value) => value.into(),
//         Err(err) => return Err(FromGlyphErr::new(source, err.into())),
//       };
//     match char::try_from(value) {
//       Ok(c) => Ok(c),
//       Err(_err) => Err(FromGlyphErr::new(source, GlyphErr::IllegalValue)),
//     }
//   }
// }

impl<'a> FromGlyph<&'a Glyph> for &'a str {
  type Error = GlyphErr;

  fn from_glyph(
    source: &'a Glyph,
  ) -> Result<Self, DecodeErr<&'a Glyph, Self::Error>> {
    // TODO: Use closure to consolidate return of FromGlyphErr

    if let Err(err) = source.header().confirm_type(GlyphType::String) {
      return Err(DecodeErr::new(source, err.into()));
    }
    match source.content().get(2..) {
      None => Ok(""),
      Some(bytes) => match from_utf8(bytes) {
        Ok(valid_str) => Ok(valid_str),
        Err(err) => Err(DecodeErr::new(source, err.into())),
      },
    }
  }
}

#[cfg(feature = "alloc")]
impl<G> FromGlyph<G> for String
where
  G: Deref<Target = Glyph>,
{
  type Error = GlyphErr;

  fn from_glyph(source: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    match <&str>::from_glyph(source.deref()) {
      Ok(as_str) => Ok(String::from(as_str)),
      Err(err) => {
        let err = err.into_parts().1;
        Err(DecodeErr::new(source, err))
      },
    }
  }
}

impl<G> FromGlyph<G> for char
where
  G: Deref<Target = Glyph>,
{
  type Error = GlyphErr;

  fn from_glyph(source: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    if let Err(err) = source.header().confirm_type(GlyphType::UnicodeChar) {
      return Err(DecodeErr::new(source, err));
    }
    let value: u32 =
      match U32::bbrd(&source.header().short_content()[..], &mut 0) {
        Ok(value) => value.into(),
        Err(err) => return Err(DecodeErr::new(source, err.into())),
      };
    match char::try_from(value) {
      Ok(c) => Ok(c),
      Err(_err) => Err(DecodeErr::new(source, GlyphErr::IllegalValue)),
    }
  }
}

impl ToGlyph for str {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    str_glyph_encode(self.as_bytes(), None, None, target, cursor)
  }

  fn glyph_len(&self) -> usize {
    str_glyph_len(self.as_bytes().len())
    // round_to_word(size_of::<GlyphHeader>() + self.len())
  }
}

#[cfg(feature = "alloc")]
impl ToGlyph for String {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    str_glyph_encode(self.as_bytes(), None, None, target, cursor)
    // self.as_str().glyph_encode(target, cursor)
  }

  fn glyph_len(&self) -> usize {
    str_glyph_len(self.as_bytes().len())
    // self.as_str().glyph_len()
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

/// Writes a string glyph.
///
/// # Parameters:
///
/// - `content`.  The contents of the string.  The caller is responsible for
///   ensuring that the contents are valid UTF-8 bytes.
/// - `language`.  The human language of the string, if any.  This is not only
///   useful metadata for the user, but can influence collation.  If not
///   provided, the resulting glyph will indicate an unknown language.
/// - `direction`.  The direction of the text can be specified, if desired. If
///   not provided, the resulting glyph will indicate an unspecified text
///   direction.
fn str_glyph_encode(
  content: &[u8],
  language: Option<Language>,
  direction: Option<StringDirection>,
  target: &mut [u8],
  cursor: &mut usize,
) -> Result<(), GlyphErr> {
  GlyphHeader::new(
    GlyphType::String,
    size_of::<StringMetadata>() + content.len(),
  )?
  .bbwr(target, cursor)?;
  StringMetadata::new(language, direction).bbwr(target, cursor)?;
  u8::bbwrs(content, target, cursor)?;
  pad_to_word(target, cursor)?;
  Ok(())
}

/// Returns the length of a contemplated string glyph, in bytes.
///
/// `content_len` is the length of the string's UTF-8 content, in bytes.  The
/// resulting length is this content length plus headers, rounded to the nearest
/// word.
#[inline]
fn str_glyph_len(content_len: usize) -> usize {
  size_of::<GlyphHeader>() + round_to_word(2 + content_len)
}

#[cfg(test)]
#[allow(unused)]
mod tests {
  use super::*;
  use alloc::vec::Vec;
  use std::thread;

  const NAMES: [&str; 7] = [
    "Kaiden Alenko",
    "Jane Shepard",
    "Ashley Williams",
    "Garrus Vakarian",
    "Urdnox Wrex",
    "Tali vas Normandy",
    "Liara T'Soni",
  ];

  #[test]
  fn icu_collation() {
    let c = COLLATOR.get();
    let result = c.compare(NAMES[0], NAMES[1]);
    std::dbg!(&result);
    let mut new_names = NAMES.clone();
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

  #[test]
  fn string_glyph() {
    // Encode the list of names into glyphs, both from `str` and `String`.
    let mut str_glyphs = Vec::new();
    let mut string_glyphs = Vec::new();
    for name in NAMES {
      str_glyphs.push(Glyph::new(name).unwrap());
      string_glyphs.push(Glyph::new(String::from(name)).unwrap());
    }

    // Ensure all combinations of round-trip codecs match.
    for ((name, str_glyph), string_glyph) in NAMES
      .iter()
      .zip(str_glyphs.iter())
      .zip(string_glyphs.iter())
    {
      let decoded1 = <&str>::from_glyph(str_glyph.as_ref()).unwrap();
      assert_eq!(*name, decoded1);
      let decoded2 = <&str>::from_glyph(string_glyph.as_ref()).unwrap();
      assert_eq!(*name, decoded2);
      let decoded3 = String::from_glyph(string_glyph.as_ref()).unwrap();
      assert_eq!(*name, decoded3);
      let decoded4 = String::from_glyph(string_glyph.as_ref()).unwrap();
      assert_eq!(*name, decoded4);

      let sg = StringGlyph::from_glyph(string_glyph.as_ref()).unwrap();
      let decoded5 = sg.get_str().unwrap();
      assert_eq!(*name, decoded5);
      assert_eq!(sg.get_str_bytes(), name.as_bytes());

      let sg = StringGlyph::from_glyph(str_glyph.as_ref()).unwrap();
      let decoded6 = sg.get_str().unwrap();
      assert_eq!(*name, decoded6);
      assert_eq!(sg.get_str_bytes(), name.as_bytes());
    }
  }
}
