//! # Crypto Key Glyph Encoding
//!
//! This file implements structures and logic related to cryptographic key
//! glyphs.  Specifically, it provides (1) serialization functions
//! [`crypto_key_glyph_len()`] and [`crypto_key_glyph_encode`] that write a
//! valid cryptographic key glyph for any specific type implementing
//! [`GlyphsCryptographicKey`], and (2) the [`CryptoKeyGlyph`] type which
//! facilitates working with encoded keys.
//!
//! - [`CryptoKeyHeader`].  A packed structure, aligned for zero-copy memory
//!   usage, representing !   the metadata and configuration of a cryptographic
//!   key. Stores key attributes like type, flags, lengths for public and
//!   private key components, fingerprints for identification, and expiration.
//! - [`CryptoKeyGlyph`].  Stores an encoded cryptographic key, along with
//!   optional metadata about the key (e.g., identifying the owner) and
//!   signatures (e.g., authenticating the key as belonging to some other
//!   entity).
//!
//! ## Design and Safety
//! - Unlike other glyphs, the keys themselves are intended to be de-serialized
//!   rather accessed with zero-copy semantics, due to the sensitivity of
//!   cryptographic functions and specialized libraries.
//! - Includes traits and functions intended to perform basic operations, such
//!   as ([`ToGlyph`], [`FromGlyph`], [`EncodedGlyph`],
//!   [`crypto_key_glyph_len()`] and [`crypto_key_glyph_encode()`].
//! - Standard traits for type-aware sorting ([`Ord`] and friends).
use crate::{
  crypto::{
    algos::CryptoKey, CryptoKeyTypes, CryptographicHash, Key, Sha3Hash,
  },
  dynamic::DynGlyph,
  misc::DateTime,
  util::debug::{ShortHexDump, UnquotedDebugString},
  zerocopy::{pad_to_word, round_to_word, ZeroCopy, U16},
  EncodedGlyph, FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader,
  GlyphType, ToGlyph,
};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
  slice::from_raw_parts,
};
use std::ops::Deref;

/// A zero-copy header containing metadata for cryptographic key glyphs.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(packed)]
struct CryptoKeyHeader {
  version:     u8,
  flags:       u8,
  type_id:     U16,
  public_len:  U16,
  secret_len:  U16,
  expires:     DateTime,
  fingerprint: Sha3Hash,
}

impl CryptoKeyHeader {
  /// Key contains a metadata glyph.
  const FLAG_HAS_METADATA: u8 = 0b0000_0001;
  /// Key is signed by another key (ends with a signature glyph).
  const FLAG_HAS_SIGNATURE: u8 = 0b0000_0010;

  /// Returns a newly created key header.
  ///
  /// - Returns a [`GlyphErr::CryptoKeyLengthOverflow`] if the length of the
  ///   keys is greater than `u16::MAX`.
  fn new(
    key_type: CryptoKeyTypes,
    flags: u8,
    public_len: usize,
    secret_len: usize,
    fingerprint: Sha3Hash,
    expires: DateTime,
  ) -> Result<Self, GlyphErr> {
    let public_len = public_len
      .try_into()
      .map_err(|_| GlyphErr::CryptoKeyLengthOverflow(public_len))?;
    let secret_len = secret_len
      .try_into()
      .map_err(|_| GlyphErr::CryptoKeyLengthOverflow(secret_len))?;
    Ok(Self {
      version: 0,
      flags,
      type_id: key_type.into(),
      public_len,
      secret_len,
      expires,
      fingerprint,
    })
  }

  /// Returns the key type specified in the header.
  fn key_type(&self) -> CryptoKeyTypes {
    CryptoKeyTypes::from(u16::from(self.type_id))
  }

  /// If the key type specified in the header does not match the provided key
  /// type, return an error.
  fn confirm_key_type(&self, key_type: CryptoKeyTypes) -> Result<(), GlyphErr> {
    if key_type as u16 == u16::from(self.type_id) {
      Ok(())
    } else {
      Err(err!(debug, GlyphErr::CryptoKeyType))
    }
  }

  /// Returns the length of the public key component (if any), in bytes.
  fn public_len(&self) -> usize {
    self.public_len.get() as usize
  }

  /// Returns the length of the private key component (if any), in bytes.
  fn secret_len(&self) -> usize {
    self.secret_len.get() as usize
  }

  /// Returns the date and time at which the key expires
  fn expires(&self) -> &DateTime {
    &self.expires
  }

  /// Returns the key's fingerprint
  ///
  /// For public key cryptography, the fingerprint is the SHA3-256 hash of the
  /// serialized public key bytes.  For symmetric keys, this has not yet been
  /// defined.
  fn fingerprint(&self) -> &Sha3Hash {
    &self.fingerprint
  }

  /// The key contains a metadata glyph.
  fn has_metadata(&self) -> bool {
    (self.flags & Self::FLAG_HAS_METADATA) != 0
  }

  /// The key has been signed by another (i.e., ends with a signature glyph).
  fn has_signature(&self) -> bool {
    (self.flags & Self::FLAG_HAS_SIGNATURE) != 0
  }
}

// SAFETY: All components are zero copy.
unsafe impl ZeroCopy for CryptoKeyHeader {}

/// A glyph containing a cryptographic key.
/* SAFETY:

  - Everything other than the glyph is a reference into it.  The targets are
    guaranteed to be pinned and immutable by invariants required by the `Glyph`
    trait.
  - Lengths for the public and private byte slices are stored in the header,
    so we only need a `*const u8` rather than a `*const [u8]`.
  - The bounds checks for all of these things must take place upon object
    creation (i.e., `FromGlyph`), as this is assumed by accessors.
*/
pub struct CryptoKeyGlyph<G: Deref<Target = Glyph>> {
  glyph:        G,
  header:       *const CryptoKeyHeader,
  public_bytes: *const u8,
  secret_bytes: *const u8,
  metadata:     Option<*const Glyph>,
  signature:    Option<*const Glyph>,
}

impl<G: Deref<Target = Glyph>> CryptoKeyGlyph<G> {
  /// Returns the glyph type header.
  fn header(&self) -> &CryptoKeyHeader {
    // SAFETY: Internal self ref of pinned (via `Glyph`) and immutable data.
    unsafe { &*self.header }
  }

  /// Returns the key's expiration date.
  pub fn expires(&self) -> &DateTime {
    self.header().expires()
  }

  /// Returns the type of cryptographic key this glyph contains.
  pub fn key_type(&self) -> CryptoKeyTypes {
    self.header().key_type()
  }

  /// Returns the serialized bytes of the key.
  pub fn public_bytes(&self) -> &[u8] {
    // SAFETY: Internal self ref of pinned (via `Glyph`) and immutable data,
    //         bounds were checked upon object creation.
    unsafe { from_raw_parts(self.public_bytes, self.header().public_len()) }
  }

  pub fn secret_bytes(&self) -> &[u8] {
    // SAFETY: Internal self ref of pinned (via `Glyph`) and immutable data,
    //         bounds were checked upon object creation.
    unsafe { from_raw_parts(self.secret_bytes, self.header().secret_len()) }
  }

  /// Returns the metadata stored with the key, if present.
  pub fn metadata(&self) -> Option<&Glyph> {
    // SAFETY: Internal self-reference, protected by invariants from G
    unsafe { self.metadata.as_ref().map(|m| &**m) }
  }

  /// Returns the metadata stored with the key, if present.
  pub fn signature(&self) -> Option<&Glyph> {
    // SAFETY: Internal self-reference, protected by invariants from G
    unsafe { self.signature.as_ref().map(|m| &**m) }
  }

  pub fn fingerprint(&self) -> &Sha3Hash {
    self.header().fingerprint()
  }
}

impl<G: Deref<Target = Glyph>> ToGlyph for CryptoKeyGlyph<G> {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    self.glyph.glyph_encode(target, cursor)
  }

  fn glyph_len(&self) -> usize {
    self.glyph.glyph_len()
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for CryptoKeyGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    // SAFETY: Remember, everything must be bounds checked here.
    if let Err(e) = glyph.header().confirm_type(GlyphType::CryptoKey) {
      return Err(FromGlyphErr::new(glyph, e));
    }

    let content = glyph.content_padded();
    let mut cursor = 0;

    let ckh = match CryptoKeyHeader::bbrf(content, &mut cursor) {
      Ok(ckh) => ckh,
      Err(e) => return Err(FromGlyphErr::new(glyph, e.into())),
    };

    let public_bytes = match u8::bbrfs(content, &mut cursor, ckh.public_len()) {
      Ok(public_bytes) => public_bytes,
      Err(e) => return Err(FromGlyphErr::new(glyph, e.into())),
    };
    cursor = round_to_word(cursor);

    let secret_bytes = match u8::bbrfs(content, &mut cursor, ckh.secret_len()) {
      Ok(secret_bytes) => secret_bytes,
      Err(e) => return Err(FromGlyphErr::new(glyph, e.into())),
    };
    cursor = round_to_word(cursor);

    let metadata = if ckh.has_metadata() {
      let mg = match Glyph::read(content, &mut cursor) {
        Ok(mg) => mg,
        Err(e) => return Err(FromGlyphErr::new(glyph, e)),
      };
      Some(mg as *const Glyph)
    } else {
      None
    };
    let signature = if ckh.has_signature() {
      let mg = match Glyph::read(content, &mut cursor) {
        Ok(mg) => mg,
        Err(e) => return Err(FromGlyphErr::new(glyph, e)),
      };
      Some(mg as *const Glyph)
    } else {
      None
    };

    let header = ckh as *const CryptoKeyHeader;
    let public_bytes = public_bytes.as_ptr();
    let secret_bytes = secret_bytes.as_ptr();
    Ok(Self {
      glyph,
      header,
      public_bytes,
      secret_bytes,
      metadata,
      signature,
    })
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for CryptoKeyGlyph<G> {
  fn into_inner(self) -> G {
    self.glyph
  }

  fn glyph(&self) -> &Glyph {
    self.glyph.deref()
  }
}

impl<G: Deref<Target = Glyph>> Debug for CryptoKeyGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("CryptoKeyGlyph");
    df.field("type", &self.header().key_type());
    df.field("fingerprint", &self.header().fingerprint());

    let mut flags_str = alloc::string::String::new();
    flags_str.push_str(&alloc::format!("0x{:02x} (", self.header().flags));
    if self.header().has_metadata() {
      flags_str.push_str("HAS_METADATA,");
    }
    if self.header().has_signature() {
      flags_str.push_str("HAS_SIGNATURE,");
    }
    if self.header().flags == 0 {
      flags_str.push_str("NONE");
    }
    flags_str.push_str(")");

    df.field("flags", &UnquotedDebugString(flags_str.as_str()));
    if self.public_bytes().len() > 0 {
      df.field("public_bytes", &ShortHexDump(&self.public_bytes(), 0));
    } else {
      df.field("public_bytes", &Option::<&[u8]>::None);
    }
    if self.secret_bytes().len() > 0 {
      df.field("secret_key_len", &self.secret_bytes().len());
      df.field("secret_key_hash", &Sha3Hash::new(&self.secret_bytes()));
    } else {
      df.field("private_bytes", &Option::<&[u8]>::None);
    }
    df.field("expires", &self.header().expires());
    df.field("metadata", &self.metadata());
    df.field("signature", &self.signature());
    df.finish()
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for CryptoKeyGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.glyph.as_ref() == other.glyph.as_ref()
  }
}

impl<G: Deref<Target = Glyph>> Eq for CryptoKeyGlyph<G> {}

impl<G: Deref<Target = Glyph>> PartialOrd for CryptoKeyGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Deref<Target = Glyph>> Ord for CryptoKeyGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self
      .header()
      .fingerprint()
      .cmp(other.header().fingerprint())
      .then_with(|| self.expires().cmp(other.expires()))
      .then_with(|| self.public_bytes().cmp(other.public_bytes()))
      .then_with(|| self.secret_bytes().cmp(other.secret_bytes()))
      .then_with(|| {
        self
          .metadata()
          .map(|pg| DynGlyph::new(pg))
          .cmp(&other.metadata().map(|pg| DynGlyph::new(pg)))
      })
      .then_with(|| {
        self
          .signature()
          .map(|pg| DynGlyph::new(pg))
          .cmp(&other.signature().map(|pg| DynGlyph::new(pg)))
      })
      .then_with(|| self.glyph.as_ref().cmp(other.glyph.as_ref()))
  }
}

// Needed b/c struct contains raw pointers.
unsafe impl<G: Deref<Target = Glyph>> Send for CryptoKeyGlyph<G> {}

impl<C: CryptoKey> ToGlyph for Key<C> {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    crypto_key_glyph_encode(&self.key, &self.expires, target, cursor)
  }

  fn glyph_len(&self) -> usize {
    crypto_key_glyph_len(self.key.public_len(), self.key.secret_len())
  }
}

/// A [`ToGlyph::glyph_len`] implementation for [`GlyphsCryptographicKey`]s.
pub(super) fn crypto_key_glyph_len(
  public_len: usize,
  private_len: usize,
) -> usize {
  size_of::<GlyphHeader>()
    + size_of::<CryptoKeyHeader>()
    + round_to_word(public_len)
    + round_to_word(private_len)
}

/// A [`ToGlyph::glyph_encode`] implementation for [`GlyphsCryptographicKey`]s.
pub(super) fn crypto_key_glyph_encode<K>(
  key: &K,
  expires: &DateTime,
  target: &mut [u8],
  cursor: &mut usize,
) -> Result<(), GlyphErr>
where
  K: CryptoKey,
{
  let public_bytes = key.public_bytes();
  let secret_bytes = key.secret_bytes();
  let glyph_len = crypto_key_glyph_len(
    public_bytes.as_ref().len(),
    secret_bytes.as_ref().len(),
  );

  GlyphHeader::new(GlyphType::CryptoKey, glyph_len)?.bbwr(target, cursor)?;
  CryptoKeyHeader::new(
    key.key_type(),
    0,
    public_bytes.as_ref().len(),
    secret_bytes.as_ref().len(),
    *key.fingerprint(),
    *expires,
  )?
  .bbwr(target, cursor)?;
  u8::bbwrs(public_bytes.as_ref(), target, cursor)?;
  pad_to_word(target, cursor)?;
  u8::bbwrs(secret_bytes.as_ref(), target, cursor)?;
  pad_to_word(target, cursor)?;
  Ok(())
}
