use crate::{
  crypto::{
    algos::CryptoKeyTypes,
    key_codec::{crypto_key_glyph_encode, crypto_key_glyph_len},
    CryptoErr, CryptoKeyGlyph, CryptoSignatureOldTrait, CryptographicHash,
    GlyphsAuthenticationKey, GlyphsCryptographicKey, GlyphsSigningKey,
    HashContext, Sha3Hash,
  },
  misc::DateTime,
  util::debug::ShortHexDump,
  zerocopy::ZeroCopy,
  EncodedGlyph, FromGlyph, FromGlyphErr, Glyph, GlyphErr, ToGlyph,
};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
};
use ed25519_dalek::{Signer, Verifier};
use rand::{CryptoRng, Rng};

pub(in crate::crypto) const ED25519_KEY_LEN: usize = 32;
pub(in crate::crypto) const ED25519_SIGNATURE_LEN: usize = 64;

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Ed25519PublicKey {
  expires:     DateTime,
  fingerprint: Sha3Hash,
  pk:          ed25519_dalek::VerifyingKey,
}

impl ToGlyph for Ed25519PublicKey {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    crypto_key_glyph_encode(self, target, cursor)
  }

  fn glyph_len(&self) -> usize {
    crypto_key_glyph_len(self)
  }
}

impl<'a, G: Glyph> TryFrom<&'a CryptoKeyGlyph<G>> for Ed25519PublicKey {
  type Error = GlyphErr;

  fn try_from(value: &'a CryptoKeyGlyph<G>) -> Result<Self, Self::Error> {
    Ed25519PublicKey::read(
      value.key_type(),
      value.expires(),
      value.public_key_bytes(),
      value.private_key_bytes(),
    )
  }
}

impl<G: Glyph> FromGlyph<G> for Ed25519PublicKey {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    let key_glyph = CryptoKeyGlyph::from_glyph(glyph)?;
    let pk = match Ed25519PublicKey::try_from(&key_glyph) {
      Ok(pk) => pk,
      Err(err) => return Err(FromGlyphErr::new(key_glyph.into_inner(), err)),
    };
    Ok(pk)
  }
}

impl GlyphsCryptographicKey for Ed25519PublicKey {
  fn key_type(&self) -> CryptoKeyTypes {
    CryptoKeyTypes::Ed25519Public
  }

  fn fingerprint(&self) -> Sha3Hash {
    self.fingerprint
  }

  fn expires(&self) -> &DateTime {
    &self.expires
  }

  fn read(
    key_type: CryptoKeyTypes,
    expires: &DateTime,
    public: &[u8],
    _private: &[u8],
  ) -> Result<Self, GlyphErr> {
    if key_type != CryptoKeyTypes::Ed25519Public
      && key_type != CryptoKeyTypes::Ed25519Private
    {
      Err(GlyphErr::CryptoErr(CryptoErr::WrongKeyType {
        expected: CryptoKeyTypes::Ed25519Public,
        observed: key_type,
      }))
    } else {
      let pk_bytes: &[u8; ED25519_KEY_LEN] = u8::bbrfa(public, &mut 0)?;
      let pk = ed25519_dalek::VerifyingKey::from_bytes(pk_bytes)
        .map_err(|_| GlyphErr::CryptoErr(CryptoErr::Ed25519InvalidKey))?;
      let fingerprint = Sha3Hash::new(&pk.to_bytes());
      Ok(Self {
        expires: expires.clone(),
        fingerprint,
        pk,
      })
    }
  }

  fn key_len_public(&self) -> usize {
    ED25519_KEY_LEN
  }

  fn write_public(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    u8::bbwrs(self.pk.as_bytes(), target, cursor)?;
    Ok(())
  }

  fn key_len_private(&self) -> usize {
    0
  }

  fn write_private(
    &self,
    _target: &mut [u8],
    _cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    Ok(())
  }
}

impl GlyphsAuthenticationKey for Ed25519PublicKey {
  type HashContext = ed25519_dalek::Sha512;
  type Signature = Ed25519Signature;

  fn verify(
    &self,
    bytes: &[u8],
    signature: &Self::Signature,
  ) -> Result<(), CryptoErr> {
    self
      .pk
      .verify(bytes, &signature.signature)
      .map_err(|_| CryptoErr::VerificationFailed)
  }

  fn new_hash_context(&self) -> Self::HashContext {
    <ed25519_dalek::Sha512 as ed25519_dalek::Digest>::new()
  }

  fn verify_pre_hashed(
    &self,
    context: Self::HashContext,
    signature: &Self::Signature,
  ) -> Result<(), CryptoErr> {
    self
      .pk
      .verify_prehashed(context, None, &signature.signature)
      .map_err(|_| CryptoErr::SignatureInvalid)?;
    Ok(())
  }
}

impl PartialOrd for Ed25519PublicKey {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Ed25519PublicKey {
  fn cmp(&self, other: &Self) -> Ordering {
    self.fingerprint.cmp(&other.fingerprint)
  }
}

impl Debug for Ed25519PublicKey {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_tuple("Ed25519PublicKey");
    df.field(&self.fingerprint);
    df.finish()
  }
}

#[derive(Clone, Eq, PartialEq)]
pub struct Ed25519PrivateKey {
  pk: Ed25519PublicKey,
  sk: ed25519_dalek::SigningKey,
}

impl Ed25519PrivateKey {
  pub fn generate<R: Rng + CryptoRng>(
    rng: &mut R,
    expires: Option<DateTime>,
  ) -> Self {
    let expires = expires.unwrap_or(DateTime::NEVER);
    let sk = ed25519_dalek::SigningKey::generate(rng);
    let pk = sk.verifying_key();
    let fingerprint = Sha3Hash::new(&pk.to_bytes());

    Self {
      pk: Ed25519PublicKey {
        expires,
        fingerprint,
        pk,
      },
      sk,
    }
  }

  pub fn public_key(&self) -> &Ed25519PublicKey {
    &self.pk
  }
}

impl ToGlyph for Ed25519PrivateKey {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    crypto_key_glyph_encode(self, target, cursor)
  }

  fn glyph_len(&self) -> usize {
    crypto_key_glyph_len(self)
  }
}

impl<G: Glyph> FromGlyph<G> for Ed25519PrivateKey {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    let key_glyph = CryptoKeyGlyph::from_glyph(glyph)?;
    let sk = match Ed25519PrivateKey::try_from(&key_glyph) {
      Ok(sk) => sk,
      Err(err) => return Err(FromGlyphErr::new(key_glyph.into_inner(), err)),
    };
    Ok(sk)
  }
}

impl<'a, G: Glyph> TryFrom<&'a CryptoKeyGlyph<G>> for Ed25519PrivateKey {
  type Error = GlyphErr;

  fn try_from(value: &'a CryptoKeyGlyph<G>) -> Result<Self, Self::Error> {
    if value.key_type() != CryptoKeyTypes::Ed25519Private {
      Err(GlyphErr::CryptoErr(CryptoErr::WrongKeyType {
        expected: CryptoKeyTypes::Ed25519Private,
        observed: value.key_type(),
      }))
    } else {
      Ed25519PrivateKey::read(
        value.key_type(),
        value.expires(),
        value.public_key_bytes(),
        value.private_key_bytes(),
      )
    }
  }
}

impl GlyphsCryptographicKey for Ed25519PrivateKey {
  fn key_type(&self) -> CryptoKeyTypes {
    CryptoKeyTypes::Ed25519Private
  }

  fn fingerprint(&self) -> Sha3Hash {
    self.pk.fingerprint()
  }

  fn expires(&self) -> &DateTime {
    self.pk.expires()
  }

  fn read(
    key_type: CryptoKeyTypes,
    expires: &DateTime,
    _public: &[u8],
    private: &[u8],
  ) -> Result<Self, GlyphErr> {
    if key_type != CryptoKeyTypes::Ed25519Private {
      Err(GlyphErr::CryptoErr(CryptoErr::WrongKeyType {
        expected: CryptoKeyTypes::Ed25519Private,
        observed: key_type,
      }))
    } else {
      let sk_bytes: &[u8; ED25519_KEY_LEN] = u8::bbrfa(private, &mut 0)?;
      let sk = ed25519_dalek::SigningKey::from_bytes(sk_bytes);
      let pk = sk.verifying_key();
      let fingerprint = Sha3Hash::new(&pk.to_bytes());
      Ok(Self {
        pk: Ed25519PublicKey {
          expires: expires.clone(),
          fingerprint,
          pk,
        },
        sk,
      })
    }
  }

  fn key_len_public(&self) -> usize {
    ED25519_KEY_LEN
  }

  fn write_public(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    u8::bbwrs(self.public_key().pk.as_bytes(), target, cursor)?;
    Ok(())
  }

  fn key_len_private(&self) -> usize {
    ED25519_KEY_LEN
  }

  fn write_private(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    u8::bbwrs(self.sk.as_bytes(), target, cursor)?;
    Ok(())
  }
}

impl GlyphsSigningKey for Ed25519PrivateKey {
  type HashContext = ed25519_dalek::Sha512;
  type Signature = Ed25519Signature;

  fn sign(&self, bytes: &[u8]) -> Self::Signature {
    let signature = self.sk.sign(bytes);
    Ed25519Signature { signature }
  }

  fn new_hash_context(&self) -> Self::HashContext {
    ed25519_dalek::Sha512::new()
  }

  fn sign_pre_hashed(
    &self,
    context: Self::HashContext,
  ) -> Result<Self::Signature, CryptoErr> {
    let sig = self
      .sk
      .sign_prehashed(context, None)
      .map_err(|_| CryptoErr::InternalErrorEd25519)?;
    Ok(Ed25519Signature { signature: sig })
  }
}

impl PartialOrd for Ed25519PrivateKey {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Ed25519PrivateKey {
  fn cmp(&self, other: &Self) -> Ordering {
    // Same sort order as the public keys.
    self.pk.cmp(&other.pk)
  }
}

impl Debug for Ed25519PrivateKey {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "Ed25519PrivateKey(fingerprint={:?})",
      &self.pk.fingerprint
    )
  }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Ed25519Signature {
  signature: ed25519_dalek::Signature,
}

impl CryptoSignatureOldTrait for Ed25519Signature {
  fn len(&self) -> usize {
    ED25519_SIGNATURE_LEN
  }

  fn read(source: &[u8], cursor: &mut usize) -> Result<Self, GlyphErr> {
    let bytes: &[u8; 64] = u8::bbrfa(&source, cursor)?;
    let signature = ed25519_dalek::Signature::from_bytes(bytes);
    Ok(Self { signature })
  }

  fn write(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let bytes = self.signature.to_bytes();
    u8::bbwrs(&bytes, target, cursor)?;
    Ok(())
  }
}

impl PartialOrd for Ed25519Signature {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Ed25519Signature {
  fn cmp(&self, other: &Self) -> Ordering {
    let self_bytes = self.signature.to_bytes();
    let other_bytes = other.signature.to_bytes();
    self_bytes.cmp(&other_bytes)
  }
}

impl Debug for Ed25519Signature {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "Ed25519Signature({:?})",
      &ShortHexDump(&self.signature.to_bytes()[..], 0)
    )
  }
}

impl HashContext for ed25519_dalek::Sha512 {
  type Output = ();

  fn new() -> Self {
    <ed25519_dalek::Sha512 as ed25519_dalek::Digest>::new()
  }

  fn update(&mut self, bytes: &[u8]) {
    <Self as ed25519_dalek::Digest>::update(self, bytes);
  }

  fn finish(self) -> Self::Output {
    <Self as ed25519_dalek::Digest>::finalize(self);
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::crypto::test::TEST_PLAINTEXT;
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;
  use std::dbg;

  #[test]
  fn ed25519() {
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);
    let sk = Ed25519PrivateKey::generate(&mut rng, None);
    let pk = sk.public_key();
    dbg!(&pk, &sk);
    let sig = sk.sign(TEST_PLAINTEXT);
    dbg!(&sig);
    let check = pk.verify(TEST_PLAINTEXT, &sig);
    dbg!(&check);
    assert!(check.is_ok());
    let check = pk.verify(b"IMPOSTER!", &sig);
    dbg!(&check);
    assert!(check.is_err());
  }
}
