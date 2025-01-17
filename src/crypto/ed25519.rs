use crate::{
  crypto::{
    AuthenticationKey, CryptoKeyHeader, CryptoKeyTypes, CryptoSignature,
    CryptoSignatureTypes, CryptographicHash, FingerprintKey, Sha3Hash,
    SigningKey,
  },
  glyph_close,
  util::LogErr,
  zerocopy::ZeroCopy,
  FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader, GlyphType, ToGlyph,
};
use core::mem::size_of;
use ed25519_dalek::{SigningKey as ed25519_SigningKey, Verifier, VerifyingKey};
use log::Level;
use rand::{CryptoRng, RngCore};

/// Generates a new [`::ed22519_dalek::Keypair`].
///
/// Necessary due to the `ed22519_dalek` crate being stuck with an outdated
/// and incompatible version of `rand`.
pub fn ed25519_keypair_generate<R>(
  mut rng: R,
) -> (ed25519_SigningKey, VerifyingKey)
where
  R: RngCore + CryptoRng,
{
  let sk = ed25519_SigningKey::generate(&mut rng);
  let pk = sk.verifying_key();
  (sk, pk)
}

impl ToGlyph for VerifyingKey {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();
    CryptoKeyHeader::new(CryptoKeyTypes::Ed25519Public).bbwr(target, cursor)?;
    u8::bbwrs(&self.to_bytes()[..], target, cursor)?;
    glyph_close(GlyphType::PublicKey, target, offset, cursor, false)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<CryptoKeyHeader>()
      + ed25519_dalek::PUBLIC_KEY_LENGTH
  }
}

impl<T> FromGlyph<T> for VerifyingKey
where
  T: Glyph,
{
  fn from_glyph(glyph: T) -> Result<Self, FromGlyphErr<T>> {
    if let Err(err) = glyph.confirm_type(GlyphType::PublicKey) {
      return Err(err.into_fge(glyph));
    }
    let source = glyph.content_padded();
    let cursor = &mut 0;
    let ckh = match CryptoKeyHeader::bbrf(source, cursor).log_err(Level::Debug)
    {
      Ok(ckh) => ckh,
      Err(err) => return Err(err.into_fge(glyph)),
    };
    if let Err(err) = ckh.confirm_type(CryptoKeyTypes::Ed25519Public) {
      return Err(err.into_fge(glyph));
    }
    let pk_bytes = match u8::bbrda::<_, 32>(source, cursor) {
      Ok(pk_bytes) => pk_bytes,
      Err(err) => return Err(err.into_fge(glyph)),
    };
    let pk = match ::ed25519_dalek::VerifyingKey::from_bytes(&pk_bytes)
      .map_err(|_err| GlyphErr::Ed25519VerificationKeyInvalid)
    {
      Ok(pk) => pk,
      Err(err) => return Err(err.into_fge(glyph)),
    };
    Ok(pk)
  }
}

impl FingerprintKey for VerifyingKey {
  fn key_fingerprint(&self) -> Sha3Hash {
    Sha3Hash::new(&self.as_bytes()[..])
  }
}

impl AuthenticationKey for VerifyingKey {
  fn verify(&self, message: &[u8], signature: &CryptoSignature) -> bool {
    if let CryptoSignature::Ed25519(_key, sig) = signature {
      Verifier::verify(self, message, sig).is_ok()
    } else {
      false
    }
  }
}

impl ToGlyph for ed25519_SigningKey {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();
    CryptoKeyHeader::new(CryptoKeyTypes::Ed25519Private)
      .bbwr(target, cursor)?;
    u8::bbwrs(&self.to_bytes()[..], target, cursor)?;
    glyph_close(GlyphType::PrivateKey, target, offset, cursor, false)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<CryptoKeyHeader>()
      + ::ed25519_dalek::SECRET_KEY_LENGTH
  }
}

impl<T> FromGlyph<T> for ed25519_SigningKey
where
  T: Glyph,
{
  fn from_glyph(glyph: T) -> Result<Self, FromGlyphErr<T>> {
    if let Err(err) = glyph.confirm_type(GlyphType::PrivateKey) {
      return Err(err.into_fge(glyph));
    }
    let source = glyph.content_padded();
    let cursor = &mut 0;
    let ckh = match CryptoKeyHeader::bbrf(source, cursor) {
      Ok(ckh) => ckh,
      Err(err) => return Err(err.into_fge(glyph)),
    };
    if let Err(err) = ckh.confirm_type(CryptoKeyTypes::Ed25519Private) {
      return Err(err.into_fge(glyph));
    }
    let sk_bytes: &[u8; ::ed25519_dalek::SECRET_KEY_LENGTH] =
      match u8::bbrfa(source, cursor) {
        Ok(sk_bytes) => sk_bytes,
        Err(err) => return Err(err.into_fge(glyph)),
      };
    let sk = ed25519_SigningKey::from_bytes(sk_bytes);
    Ok(sk)
  }
}

impl FingerprintKey for ed25519_SigningKey {
  fn key_fingerprint(&self) -> Sha3Hash {
    let pk = ::ed25519_dalek::VerifyingKey::from(self);
    pk.key_fingerprint()
  }
}

impl SigningKey for ed25519_SigningKey {
  fn sign(&self, message: &[u8]) -> Result<CryptoSignature, GlyphErr> {
    let sig = ::ed25519_dalek::Signer::sign(self, message);
    Ok(CryptoSignature::new_ed25519(self.verifying_key(), sig))
  }

  fn crypto_sig_type(&self) -> CryptoSignatureTypes {
    CryptoSignatureTypes::Ed25519
  }
}

impl AuthenticationKey for ed25519_SigningKey {
  fn verify(&self, message: &[u8], signature: &CryptoSignature) -> bool {
    let pk = self.verifying_key();
    if let CryptoSignature::Ed25519(_key, sig) = signature {
      Verifier::verify(&pk, message, sig).is_ok()
    } else {
      false
    }
  }
}

// impl From<Error> for GlyphErr {
//   fn from(_src: Error) -> Self {
//     GlyphErr::Ed25519Error
//   }
// }

#[cfg(test)]
mod test {
  use super::*;
  use crate::{crypto::TEST_PLAINTEXT, glyph_new, util::init_test_logger};
  use ::test::Bencher;
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;
  use std::dbg;

  #[test]
  fn ed25519_codec() -> Result<(), GlyphErr> {
    init_test_logger();

    let rng = ChaCha20Rng::from_seed([32; 32]);
    let (sk, pk) = ed25519_keypair_generate(rng);

    let sk_g = glyph_new(&sk)?;
    let pk_g = glyph_new(&pk)?;
    dbg!(&sk_g);
    dbg!(&pk_g);

    let sk_d = ed25519_SigningKey::from_glyph(sk_g)?;
    let pk_d = VerifyingKey::from_glyph(pk_g)?;

    assert_eq!(sk.to_bytes(), sk_d.to_bytes());
    assert_eq!(pk.as_bytes(), pk_d.as_bytes());

    Ok(())
  }

  #[bench]
  fn ed25519_signature(b: &mut Bencher) -> Result<(), GlyphErr> {
    init_test_logger();

    let rng = ChaCha20Rng::from_seed([32; 32]);
    let (sk, pk) = ed25519_keypair_generate(rng);

    let cs = SigningKey::sign(&sk, TEST_PLAINTEXT)?;
    assert_eq!(cs.valid_for(TEST_PLAINTEXT).unwrap(), sk.key_fingerprint());
    assert!(AuthenticationKey::verify(&pk, TEST_PLAINTEXT, &cs));

    b.iter(|| {
      let cs = SigningKey::sign(&sk, TEST_PLAINTEXT)?;
      Ok::<CryptoSignature, GlyphErr>(cs)
    });

    Ok(())
  }
}
