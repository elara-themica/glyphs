//! Serialization of Cryptographic Keys
//!
//! # Binary Format
//!
//! The contents of these glyphs are the following:
//!
//! - A `CryptoKeyHeader`.
//! -
//!
//!

use crate::{
  crypto::{AesKey, CryptoErr, CryptographicHash, GlyphSigner, Sha3Hash},
  glyph_read,
  misc::DateTime,
  util::debug::ShortHexDump,
  zerocopy::{pad_to_word, round_to_word, ZeroCopy, U16},
  BoxGlyph, BoxGlyphBuf, FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader,
  GlyphType, ParsedGlyph, ToGlyph, UnsafeGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  mem::transmute,
  slice::from_raw_parts,
};
use ed25519_dalek::{SigningKey, VerifyingKey};
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use smallvec::SmallVec;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(packed)]
pub struct CryptoKeyHeader {
  version:     u8,
  flags:       u8,
  type_id:     U16,
  public_len:  U16,
  private_len: U16,
  expires:     DateTime,
  fingerprint: Sha3Hash,
}

// SAFETY: All components are zero copy.
unsafe impl ZeroCopy for CryptoKeyHeader {}

impl CryptoKeyHeader {
  pub const FLAG_CAN_DECRYPT: u8 = 0b0000_0010;
  pub const FLAG_CAN_ENCRYPT: u8 = 0b0000_0001;
  pub const FLAG_CAN_SIGN: u8 = 0b0000_0100;
  pub const FLAG_CAN_VERIFY: u8 = 0b0000_1000;
  pub const FLAG_HAS_METADATA: u8 = 0b0001_0000;
  pub const FLAG_IS_REVOKED: u8 = 0b0100_0000;
  pub const FLAG_IS_SIGNED: u8 = 0b0010_0000;

  /// Returns a newly created key header.
  ///
  /// - Returns a [`GlyphErr::CryptoKeyLengthOverflow`] if the length of the
  ///   keys is greater than `u16::MAX`.
  pub fn new(
    key_type: CryptoKeyTypes,
    flags: u8,
    public_len: usize,
    private_len: usize,
    fingerprint: Sha3Hash,
    expires: Option<DateTime>,
  ) -> Result<Self, GlyphErr> {
    let public_len = public_len
      .try_into()
      .map_err(|_| GlyphErr::CryptoKeyLengthOverflow(public_len))?;
    let private_len = private_len
      .try_into()
      .map_err(|_| GlyphErr::CryptoKeyLengthOverflow(private_len))?;
    Ok(Self {
      version: 0,
      flags,
      type_id: key_type.into(),
      public_len,
      private_len,
      expires: expires.unwrap_or(DateTime::NEVER),
      fingerprint,
    })
  }

  /// Returns the key type specified in the header.
  pub fn key_type(&self) -> CryptoKeyTypes {
    CryptoKeyTypes::from(u16::from(self.type_id))
  }

  /// If the key type specified in the header does not match the provided key
  /// type, return an error.
  pub fn confirm_key_type(
    &self,
    key_type: CryptoKeyTypes,
  ) -> Result<(), GlyphErr> {
    if key_type as u16 == u16::from(self.type_id) {
      Ok(())
    } else {
      Err(err!(debug, GlyphErr::CryptoKeyType))
    }
  }

  /// Returns `true` if the key is intended to be used for
  /// encryption.
  pub fn flag_can_encrypt(&self) -> bool {
    self.flags & Self::FLAG_CAN_ENCRYPT != 0
  }

  /// Returns `true` if the key is intended to be used for
  /// decryption.
  pub fn flag_can_decrypt(&self) -> bool {
    self.flags & Self::FLAG_CAN_DECRYPT != 0
  }

  /// Returns `true` if the key is intended to be used for
  /// generating cryptographic signatures.
  pub fn flag_can_sign(&self) -> bool {
    self.flags & Self::FLAG_CAN_SIGN != 0
  }

  /// Returns `true` if the key is intended to be used for
  /// verifying cryptographic signatures.
  pub fn flag_can_verify(&self) -> bool {
    self.flags & Self::FLAG_CAN_VERIFY != 0
  }

  /// Returns `true` if the key is known to have been revoked.
  pub fn flag_is_revoked(&self) -> bool {
    self.flags & Self::FLAG_IS_REVOKED != 0
  }

  /// Returns `true` if the key contains metadata.
  pub fn flag_has_metadata(&self) -> bool {
    self.flags & Self::FLAG_HAS_METADATA != 0
  }

  /// Returns the length of the serialized public key (if any) in bytes.
  pub fn public_len(&self) -> usize {
    self.public_len.get().into()
  }

  /// Returns the length of the serialized private key (if any) in bytes.
  pub fn private_len(&self) -> usize {
    self.private_len.get().into()
  }

  /// Returns the date and time at which the key expires
  pub fn expires(&self) -> &DateTime {
    &self.expires
  }

  /// Returns the key's fingerprint
  ///
  /// For public key cryptography, the fingerprint is the SHA3-256 hash of the
  /// serialized public key bytes.  For symmetric keys, this has not yet been
  /// defined.
  pub fn fingerprint(&self) -> &Sha3Hash {
    &self.fingerprint
  }
}

/// A cryptographic key
pub struct CryptoKeyGlyph<G: Glyph = BoxGlyph> {
  glyph:         G,
  header:        *const CryptoKeyHeader,
  public_bytes:  *const u8,
  private_bytes: *const u8,
  metadata:      Option<UnsafeGlyph>,
}

impl CryptoKeyGlyph<BoxGlyph> {
  /// Generate a new private key for signing using the ed25519 elliptic curve.
  pub fn gen_ed25519_private<R: RngCore + CryptoRng>(
    rng: &mut R,
    expires: Option<DateTime>,
    metadata: Option<&dyn ToGlyph>,
  ) -> Result<Self, GlyphErr> {
    let private_key = SigningKey::generate(rng);
    let private_bytes = private_key.to_bytes();
    let public_key = VerifyingKey::from(&private_key);
    let public_bytes = public_key.to_bytes();
    Self::from_ed25519_private(
      &public_bytes[..],
      &private_bytes[..],
      expires,
      metadata,
    )
  }

  /// Writes a private key for signing using the ed25519 elliptic curve.
  pub fn from_ed25519_private(
    public: &[u8],
    private: &[u8],
    expires: Option<DateTime>,
    metadata: Option<&dyn ToGlyph>,
  ) -> Result<Self, GlyphErr> {
    let key_flags =
      CryptoKeyHeader::FLAG_CAN_SIGN | CryptoKeyHeader::FLAG_CAN_VERIFY;
    let glyph = Self::write_new_key(
      &public[..],
      &private[..],
      expires,
      CryptoKeyTypes::Ed25519Private,
      key_flags,
      metadata,
    )?;
    let ckg = CryptoKeyGlyph::from_glyph(glyph)?;
    Ok(ckg)
  }

  /// Writes a public key for signing using the ed25519 elliptic curve.
  pub fn from_ed25519_public(
    public: &[u8],
    expires: Option<DateTime>,
    metadata: Option<&dyn ToGlyph>,
  ) -> Result<Self, GlyphErr> {
    let key_flags =
      CryptoKeyHeader::FLAG_CAN_SIGN | CryptoKeyHeader::FLAG_CAN_VERIFY;
    let glyph = Self::write_new_key(
      &public[..],
      &[],
      expires,
      CryptoKeyTypes::Ed25519Public,
      key_flags,
      metadata,
    )?;
    let ckg = CryptoKeyGlyph::from_glyph(glyph)?;
    Ok(ckg)
  }
}

impl<G: Glyph> CryptoKeyGlyph<G> {
  /// Returns the glyph type header.
  fn header(&self) -> &CryptoKeyHeader {
    // SAFETY: Internal self ref of pinned (via `Glyph`) and immutable data.
    unsafe { &*self.header }
  }

  /// Returns the key's fingerprint.
  pub fn key_fingerprint(&self) -> &Sha3Hash {
    self.header().fingerprint()
  }

  /// Returns the key's expiration date.
  pub fn expires(&self) -> &DateTime {
    self.header().expires()
  }

  /// Returns the serialized bytes of the public key, if any.
  pub fn public_bytes(&self) -> &[u8] {
    // SAFETY: Internal self ref of pinned (via `Glyph`) and immutable data,
    //         bounds checked upon object creation.
    unsafe { from_raw_parts(self.public_bytes, self.header().public_len()) }
  }

  /// Returns the serialized bytes of the private key, if any.
  pub fn private_bytes(&self) -> &[u8] {
    // SAFETY: Internal self ref of pinned (via `Glyph`) and immutable data,
    //         bounds checked upon object creation.
    unsafe { from_raw_parts(self.private_bytes, self.header().private_len()) }
  }

  /// Returns the metadata stored with the key, if present.
  pub fn metadata(&self) -> Option<ParsedGlyph<'_>> {
    unsafe { self.metadata.as_ref().map(|m| m.into_parsed()) }
  }

  /// Decode the raw key into a native type, if possible.
  fn decode_key(&self) -> Result<CryptoKeyDecoded, CryptoErr> {
    CryptoKeyDecoded::read(
      self.header().key_type(),
      self.public_bytes(),
      self.private_bytes(),
    )
  }

  // TODO: Add an option for a signature here.
  fn write_new_key(
    public: &[u8],
    private: &[u8],
    expiry: Option<DateTime>,
    key_type: CryptoKeyTypes,
    mut flags: u8,
    metadata: Option<&dyn ToGlyph>,
  ) -> Result<BoxGlyph, GlyphErr> {
    let content_len = size_of::<CryptoKeyHeader>()
      + round_to_word(public.len())
      + round_to_word(private.len())
      + metadata.map(|m| m.glyph_len()).unwrap_or(0);

    let mut buf = BoxGlyphBuf::new(size_of::<GlyphHeader>() + content_len)?;
    let mut cursor = 0;

    let glyph_header = GlyphHeader::new(GlyphType::CryptoKey, content_len)?;
    glyph_header.bbwr(&mut buf, &mut cursor)?;

    if metadata.is_some() {
      flags |= CryptoKeyHeader::FLAG_HAS_METADATA;
    }

    let key_header = CryptoKeyHeader::new(
      key_type,
      flags,
      public.len(),
      private.len(),
      Sha3Hash::new(public),
      expiry,
    )?;
    key_header.bbwr(&mut buf, &mut cursor)?;
    u8::bbwrs(public, &mut buf, &mut cursor)?;
    pad_to_word(buf.as_mut(), &mut cursor)?;
    u8::bbwrs(private, &mut buf, &mut cursor)?;
    pad_to_word(buf.as_mut(), &mut cursor)?;

    if let Some(metadata) = metadata {
      metadata.glyph_encode(buf.as_mut(), &mut cursor)?;
    }
    let glyph = buf.finalize()?;
    Ok(glyph)
  }

  /// Returns an object that can cryptographically sign glyphs.
  pub fn signer(&self) -> Result<GlyphSigner, CryptoErr> {
    let decoded = self.decode_key()?;
    if let CryptoKeyDecoded::Ed25519Private(key) = decoded {
      let signer = GlyphSigner::new(key);
      Ok(signer)
    } else {
      Err(CryptoErr::UnsupportedSigningKey(self.header().key_type()))
    }
  }

  // /// Returns an object that can verify cryptographically signed glyphs.
  // pub fn verifier(&self) -> Result<impl GlyphVerifier, GlyphErr> {
  //   todo!()
  // }
  //
  // /// Returns an object that can encrypt glyphs.
  // pub fn encryptor(&self) -> Result<impl GlyphEncryptor, GlyphErr> {
  //   todo!()
  // }
  //
  // /// Returns an object that can decrypt glyphs.
  // pub fn decryptor(&self) -> Result<impl GlyphDecryptor, GlyphErr> {
  //   todo!()
  // }
}

impl ToGlyph for CryptoKeyGlyph {
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

impl<G: Glyph> FromGlyph<G> for CryptoKeyGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(e) = glyph.confirm_type(GlyphType::CryptoKey) {
      return Err(FromGlyphErr::new(glyph, e));
    }

    let content = glyph.content_padded();
    let mut cursor = 0;

    let ckh = match CryptoKeyHeader::bbrf(content, &mut cursor) {
      Ok(ckh) => ckh,
      Err(e) => return Err(FromGlyphErr::new(glyph, e)),
    };

    let public_bytes = match u8::bbrfs(content, &mut cursor, ckh.public_len()) {
      Ok(public_bytes) => public_bytes,
      Err(e) => return Err(FromGlyphErr::new(glyph, e)),
    };

    cursor = round_to_word(cursor);
    let private_bytes = match u8::bbrfs(content, &mut cursor, ckh.private_len())
    {
      Ok(private_bytes) => private_bytes,
      Err(e) => return Err(FromGlyphErr::new(glyph, e)),
    };
    let metadata = if ckh.flag_has_metadata() {
      let mg = match glyph_read(content, &mut cursor) {
        Ok(mg) => mg,
        Err(e) => return Err(FromGlyphErr::new(glyph, e)),
      };
      unsafe { Some(UnsafeGlyph::from_parsed(mg)) }
    } else {
      None
    };
    let header = ckh as *const CryptoKeyHeader;
    let public_bytes = public_bytes.as_ptr();
    let private_bytes = private_bytes.as_ptr();
    Ok(Self {
      glyph,
      header,
      public_bytes,
      private_bytes,
      metadata,
    })
  }
}

impl<G: Glyph> Debug for CryptoKeyGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("CryptoKeyGlyph");
    df.field("type", &self.header().key_type());
    df.field("fingerprint", &self.header().fingerprint());
    df.field("flags", &ShortHexDump(&[self.header().flags][..], 0));
    if self.public_bytes().len() > 0 {
      df.field("public_bytes", &ShortHexDump(&self.public_bytes(), 0));
    }
    if self.private_bytes().len() > 0 {
      df.field("private_bytes", &ShortHexDump(&self.private_bytes(), 0));
    }
    df.field("expires", &self.header().expires());
    df.field("metadata", &self.metadata());
    df.finish()
  }
}

enum CryptoKeyDecoded {
  Aes256(AesKey),
  Ed25519Public(VerifyingKey),
  Ed25519Private(SigningKey),
  // X25519Public(X),
  // X25519Private,
}

impl CryptoKeyDecoded {
  fn read(
    key_type: CryptoKeyTypes,
    public: &[u8],
    private: &[u8],
  ) -> Result<Self, CryptoErr> {
    match key_type {
      CryptoKeyTypes::Aes256 => {
        let key = AesKey::from_bytes(private)
          .map_err(|_| CryptoErr::Aes256WrongKeyLength(private.len()))?;
        Ok(Self::Aes256(key))
      },
      CryptoKeyTypes::Ed25519Public => {
        let pk_bytes: &[u8; 32] = u8::bbrfa(public, &mut 0)
          .map_err(|_| CryptoErr::Ed25519PublicWrongKeyLength(public.len()))?;
        let key = VerifyingKey::from_bytes(pk_bytes)
          .map_err(|_| CryptoErr::Ed25519InvalidKey)?;
        Ok(Self::Ed25519Public(key))
      },
      CryptoKeyTypes::Ed25519Private => {
        let sk_bytes: &[u8; 32] = u8::bbrfa(private, &mut 0)
          .map_err(|_| CryptoErr::Ed25519PrivateWrongKeyLength(public.len()))?;
        let key = SigningKey::from_bytes(sk_bytes);
        Ok(Self::Ed25519Private(key))
      },
      // CryptoKeyTypes::X25519Public => {
      //   todo!()
      // },
      // CryptoKeyTypes::X25519Private => {
      //   todo!()
      // },
      _ => Err(CryptoErr::UnsupportedCryptoScheme(key_type)),
    }
  }

  fn key_type(&self) -> CryptoKeyTypes {
    match self {
      CryptoKeyDecoded::Aes256(_) => CryptoKeyTypes::Aes256,
      CryptoKeyDecoded::Ed25519Public(_) => CryptoKeyTypes::Ed25519Public,
      CryptoKeyDecoded::Ed25519Private(_) => CryptoKeyTypes::Ed25519Private,
    }
  }

  fn public_len(&self) -> usize {
    match self {
      CryptoKeyDecoded::Aes256(_) => 0,
      CryptoKeyDecoded::Ed25519Public(_) => 32,
      CryptoKeyDecoded::Ed25519Private(_) => 32,
    }
  }

  fn public_bytes(&self) -> SmallVec<u8, 64> {
    match self {
      CryptoKeyDecoded::Aes256(key) => SmallVec::from_slice(key.bytes()),
      CryptoKeyDecoded::Ed25519Public(key) => {
        SmallVec::from_slice(&key.to_bytes()[..])
      },
      CryptoKeyDecoded::Ed25519Private(key) => {
        SmallVec::from_slice(&key.as_bytes()[..])
      },
    }
  }

  fn private_bytes(&self) -> SmallVec<u8, 64> {
    match self {
      CryptoKeyDecoded::Aes256(key) => SmallVec::from_slice(key.bytes()),
      CryptoKeyDecoded::Ed25519Public(key) => {
        SmallVec::from_slice(&key.as_bytes()[..])
      },
      CryptoKeyDecoded::Ed25519Private(key) => {
        SmallVec::from_slice(&key.to_bytes()[..])
      },
    }
  }

  fn private_len(&self) -> usize {
    match self {
      CryptoKeyDecoded::Aes256(_) => 32,
      CryptoKeyDecoded::Ed25519Public(_) => 0,
      CryptoKeyDecoded::Ed25519Private(_) => 32,
    }
  }
}

/// A list of cryptographic key types and corresponding type ids.
//
// SAFETY:  Updating this?  Remember to keep the list and IDs contiguous and
// update the `From<u16>` implementation below with the highest ID.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum CryptoKeyTypes {
  /// The type of the key is deliberately unspecified.
  Unspecified = 0x0000,
  /// A 256-bit AES key
  Aes256 = 0x0001,
  /// An Ed25519 Public Key
  Ed25519Public = 0x0002,
  /// An Ed25519 Private Key
  Ed25519Private = 0x0003,
  /// An X25519 Public Key
  X25519Public = 0x0004,
  /// An X25519 Private Key
  X25519Private = 0x0005,
  /// An unknown key type.
  Unknown = 0x0006,
}

impl From<u16> for CryptoKeyTypes {
  fn from(type_id: u16) -> Self {
    if type_id > CryptoKeyTypes::Unknown as u16 {
      CryptoKeyTypes::Unknown
    } else {
      // SAFETY: Depends on highest known ID being checked, safety note
      // left in that code.
      unsafe { transmute::<u16, Self>(type_id) }
    }
  }
}

impl From<U16> for CryptoKeyTypes {
  fn from(value: U16) -> Self {
    value.get().into()
  }
}

impl From<CryptoKeyTypes> for U16 {
  fn from(value: CryptoKeyTypes) -> Self {
    U16::from(value as u16)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::glyph_new;

  #[test]
  fn crypto_key_codec() {
    let mut rng = ChaCha20Rng::from_seed([0; 32]);

    // Ed25519 keys
    let key =
      CryptoKeyGlyph::gen_ed25519_private(&mut rng, None, None).unwrap();
    let glyph = glyph_new(&key).unwrap();
    std::dbg!(&glyph);
    let key2 = CryptoKeyGlyph::from_glyph(glyph).unwrap();
    std::dbg!(&key2);
  }
}
