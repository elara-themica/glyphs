use crate::{
  crypto::{
    aes_256ctr_decrypt, aes_256ctr_encrypt, AesIv, AesKey, CiphertextMetadata,
    CiphertextMetadataInner, CryptoKeyHeader, CryptoKeyTypes,
    CryptographicHash, DecryptionKey, EncryptionKey, EncryptionSchemes,
    FingerprintKey, GlyphHash, Sha3Hash,
  },
  glyph_close,
  zerocopy::ZeroCopy,
  FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType, ToGlyph,
};
use core::mem::size_of;
use rand::{CryptoRng, RngCore};
use x25519_dalek::{PublicKey, StaticSecret};

/// The length of X25519 public and private keys
pub const X25519_KEY_LEN: usize = 32;

impl ToGlyph for PublicKey {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();
    CryptoKeyHeader::new(CryptoKeyTypes::X25519Public).bbwr(target, cursor)?;
    u8::bbwrs(&self.to_bytes()[..], target, cursor)?;
    glyph_close(GlyphType::PublicKey, target, offset, cursor, false)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>() + size_of::<CryptoKeyHeader>() + X25519_KEY_LEN
  }
}

impl<T> FromGlyph<T> for PublicKey
where
  T: Glyph,
{
  fn from_glyph(glyph: T) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::PublicKey)?;
    let source = glyph.content_padded();
    let cursor = &mut 0;
    let ckh = CryptoKeyHeader::bbrf(source, cursor)?;
    ckh.confirm_type(CryptoKeyTypes::X25519Public)?;
    let pk_bytes: [u8; X25519_KEY_LEN] = u8::bbrda(source, cursor)?;
    let pk = ::x25519_dalek::PublicKey::from(pk_bytes);
    Ok(pk)
  }
}

impl FingerprintKey for PublicKey {
  fn key_fingerprint(&self) -> Sha3Hash {
    Sha3Hash::new(&self.as_bytes()[..])
  }
}

impl EncryptionKey for ::x25519_dalek::PublicKey {
  fn metadata_glyph_len(&self) -> usize {
    CiphertextMetadata::glyph_len(EncryptionSchemes::X25519Aes256Ctr)
  }

  fn encrypt<R: RngCore + CryptoRng>(
    &self,
    rng: R,
    data: &mut [u8],
  ) -> Result<(GlyphHash, CiphertextMetadata), GlyphErr> {
    let fingerprint = self.key_fingerprint();

    let eph_sk = ::x25519_dalek::EphemeralSecret::random_from_rng(rng);
    let eph_pk = ::x25519_dalek::PublicKey::from(&eph_sk);
    let ss = eph_sk.diffie_hellman(self);
    let ss_hash = Sha3Hash::new(ss.as_bytes());
    let ss_key = AesKey::from_bytes(&ss_hash.hash_bytes()[..])?;
    let iv = AesIv::from_ephemeral_key(&ss_key);

    let (hash, mac) = aes_256ctr_encrypt(&ss_key, &iv, data);
    let ctm =
      CiphertextMetadata::new_x25519(fingerprint, eph_pk.to_bytes(), mac);
    Ok((hash, ctm))
  }
}

impl FingerprintKey for StaticSecret {
  fn key_fingerprint(&self) -> Sha3Hash {
    let pk = ::x25519_dalek::PublicKey::from(self);
    pk.key_fingerprint()
  }
}

impl DecryptionKey for StaticSecret {
  fn decrypt(
    &self,
    metadata: &CiphertextMetadata,
    data: &mut [u8],
  ) -> Result<GlyphHash, GlyphErr> {
    if let CiphertextMetadataInner::X25519Aes256Ctr { eph_pk, mac } =
      &metadata.inner
    {
      let eph_pk = x25519_dalek::PublicKey::from(*eph_pk);
      let ss = self.diffie_hellman(&eph_pk);
      let ss_hash = Sha3Hash::new(ss.as_bytes());
      let key = AesKey::from_bytes(&ss_hash.hash_bytes()[..])?;
      let iv = AesIv::from_ephemeral_key(&key);
      aes_256ctr_decrypt(&key, &iv, mac, data)
    } else {
      Err(err!(debug, GlyphErr::WrongCryptoScheme))
    }
  }
}

impl ToGlyph for StaticSecret {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();
    CryptoKeyHeader::new(CryptoKeyTypes::X25519Private).bbwr(target, cursor)?;
    u8::bbwrs(&self.to_bytes()[..], target, cursor)?;
    glyph_close(GlyphType::PrivateKey, target, offset, cursor, false)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>() + size_of::<CryptoKeyHeader>() + X25519_KEY_LEN
  }
}

impl<T> FromGlyph<T> for StaticSecret
where
  T: Glyph,
{
  fn from_glyph(glyph: T) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::PrivateKey)?;
    let source = glyph.content_padded();
    let cursor = &mut 0;
    let ckh = CryptoKeyHeader::bbrf(source, cursor)?;
    ckh.confirm_type(CryptoKeyTypes::X25519Private)?;
    let sk_bytes: [u8; X25519_KEY_LEN] = u8::bbrda(source, cursor)?;
    let sk = ::x25519_dalek::StaticSecret::from(sk_bytes);
    Ok(sk)
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    collections::BasicVecGlyph,
    crypto::{EncryptedGlyph, GlyphCrypter, TEST_PLAINTEXT},
    glyph_new,
    util::{
      debug::{HexDump, ShortHexDump},
      init_test_logger,
    },
  };
  use alloc::boxed::Box;
  use rand::{rngs::OsRng, SeedableRng};
  use rand_chacha::ChaCha20Rng;
  use std::dbg;

  /// Test round-trip encoding of x25519 cryptographic keys
  #[test]
  fn x25519_codec() {
    init_test_logger();

    // Set up keys
    let mut rng = OsRng::default();
    let sk = ::x25519_dalek::StaticSecret::random_from_rng(&mut rng);
    let pk = ::x25519_dalek::PublicKey::from(&sk);

    let skg = glyph_new(&sk).unwrap();
    let pkg = glyph_new(&pk).unwrap();

    let skd = StaticSecret::from_glyph(skg.borrow()).unwrap();
    let pkd = PublicKey::from_glyph(pkg.borrow()).unwrap();

    assert_eq!(sk.to_bytes(), skd.to_bytes());
    assert_eq!(pk, pkd);
  }

  /// Test round-trip encryption/decryption using an X25519 key.
  #[test]
  fn x25519_crypto() {
    init_test_logger();

    // Set up keys
    let mut rng_seed = [42u8; 32];
    let mut rng = ChaCha20Rng::from_seed(rng_seed);
    rng.fill_bytes(&mut rng_seed[..]);
    let mut rng = ChaCha20Rng::from_seed(rng_seed);
    let sk = ::x25519_dalek::StaticSecret::random_from_rng(&mut rng);
    let pk = ::x25519_dalek::PublicKey::from(&sk);

    // Encrypt
    let as_glyph = glyph_new(&TEST_PLAINTEXT[..]).unwrap();
    let mut buf: Box<[u8]> = Box::from(as_glyph.as_ref());

    let (pt_hash_enc, metadata) = pk.encrypt(rng, buf.as_mut()).unwrap();
    let ct_buf = buf;

    // Decrypt
    let mut buf = Box::<[u8]>::from(ct_buf.as_ref());
    let pt_hash_dec = sk.decrypt(&metadata, buf.as_mut()).unwrap();
    let pt_buf = buf;

    dbg!(HexDump(as_glyph.as_ref()));
    dbg!(as_glyph.as_ref().len());
    dbg!(&metadata);
    dbg!(ShortHexDump(ct_buf.as_ref(), 8));
    dbg!(ShortHexDump(pt_buf.as_ref(), 8));
    dbg!(pt_hash_enc);
    dbg!(pt_hash_dec);

    let rng = ChaCha20Rng::from_seed([42u8; 32]);
    let ge = GlyphCrypter::new(&TEST_PLAINTEXT[..], &pk, rng);
    let glyph = glyph_new(&ge).unwrap();
    dbg!(&glyph);

    let eg = EncryptedGlyph::from_glyph(glyph).unwrap();
    dbg!(eg.ciphertext_metadata());
    dbg!(eg.ciphertext().len());
    dbg!(ShortHexDump(eg.ciphertext(), 8));

    let dg = eg.decrypt(&sk).unwrap();
    let decoded = BasicVecGlyph::<_>::from_glyph(dg).unwrap();

    assert_eq!(decoded.get::<u8>().unwrap(), &TEST_PLAINTEXT[..]);
  }
}
