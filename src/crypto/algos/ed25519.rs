//! Module for Ed25519 cryptographic keys and signatures.
//!
//! These types should generally not be used directly.  They are intended to
//! be generics used with the generic cryptographic types, as they are here to
//! provide access to low-level primitives through a generic (trait) interface.
//! For example, generate a new key with [`Key::<Ed25519SecretKey>::generate()`]
//! instead of using [`Ed25519SecretKey`] directly.
//!
//! [`Ed25519SecretKey`], [`Ed25519PublicKey`], and [`Ed25519Signature`] are
//! adaptors for the `SigningKey`, `VerifyingKey`, and `Signature` types from
//! the `ed25519-dalek` crate, respectively.
use crate::{
  crypto::{
    algos::{
      AuthenticationKey, CryptoKey, CryptoSignature, GenerableCryptoKey,
      SigningKey,
    },
    CryptoErr, CryptoKeyTypes, CryptoSignatureTypes, CryptographicHash,
    Sha3Hash,
  },
  util::debug::ShortHexDump,
  zerocopy::ZeroCopy,
};
use core::fmt::{Debug, Formatter};
use ed25519_dalek::{Signer, Verifier};
use rand::{CryptoRng, Rng};

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Ed25519PublicKey {
  fingerprint: Sha3Hash,
  public_key:  ed25519_dalek::VerifyingKey,
}

impl AuthenticationKey for Ed25519PublicKey {
  type Signature = Ed25519Signature;

  fn authenticate(
    &self,
    bytes: &[u8],
    signature: &Self::Signature,
  ) -> Result<(), CryptoErr> {
    self
      .public_key
      .verify(bytes, &signature.0)
      .map_err(|_| CryptoErr::VerificationFailed)?;
    Ok(())
  }
}

impl CryptoKey for Ed25519PublicKey {
  type PublicBytes<'a> = &'a [u8; 32];
  type SecretBytes<'a> = &'a [u8];

  fn fingerprint(&self) -> &Sha3Hash {
    &self.fingerprint
  }

  fn key_type(&self) -> CryptoKeyTypes {
    CryptoKeyTypes::Ed25519Public
  }

  fn public_len(&self) -> usize {
    ed25519_dalek::PUBLIC_KEY_LENGTH
  }

  fn secret_len(&self) -> usize {
    0
  }

  fn public_bytes(&self) -> Self::PublicBytes<'_> {
    self.public_key.as_bytes()
  }

  fn secret_bytes(&self) -> Self::SecretBytes<'_> {
    &[]
  }

  fn deserialize(
    key_type: CryptoKeyTypes,
    public_bytes: &[u8],
    private_bytes: &[u8],
  ) -> Result<Self, CryptoErr> {
    if key_type == CryptoKeyTypes::Ed25519Public {
      let fingerprint = Sha3Hash::new(public_bytes);
      let public_bytes: &[u8; 32] = u8::bbrfa(public_bytes, &mut 0)?;
      let public_key = ed25519_dalek::VerifyingKey::from_bytes(public_bytes)
        .map_err(|_| CryptoErr::Ed25519InvalidKey)?;
      Ok(Self {
        fingerprint,
        public_key,
      })
    } else if key_type == CryptoKeyTypes::Ed25519Private {
      let sk =
        Ed25519SecretKey::deserialize(key_type, public_bytes, private_bytes)?;
      Ok(*sk.authentication_key())
    } else {
      Err(CryptoErr::WrongKeyType {
        expected: CryptoKeyTypes::Ed25519Public,
        observed: key_type,
      })
    }
  }
}

impl Debug for Ed25519PublicKey {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "Ed25519PublicKey({:?})",
      &ShortHexDump(self.fingerprint.as_ref(), 0)
    )
  }
}

#[derive(Clone, Eq, PartialEq)]
pub struct Ed25519SecretKey {
  public_key: Ed25519PublicKey,
  secret_key: ed25519_dalek::SigningKey,
}

impl AuthenticationKey for Ed25519SecretKey {
  type Signature = Ed25519Signature;

  fn authenticate(
    &self,
    bytes: &[u8],
    signature: &Self::Signature,
  ) -> Result<(), CryptoErr> {
    self.public_key.authenticate(bytes, signature)
  }
}

impl CryptoKey for Ed25519SecretKey {
  type PublicBytes<'a> = &'a [u8; 32];
  type SecretBytes<'a> = [u8; 32];

  fn fingerprint(&self) -> &Sha3Hash {
    self.public_key.fingerprint()
  }

  fn key_type(&self) -> CryptoKeyTypes {
    CryptoKeyTypes::Ed25519Private
  }

  fn public_len(&self) -> usize {
    ed25519_dalek::PUBLIC_KEY_LENGTH
  }

  fn secret_len(&self) -> usize {
    ed25519_dalek::SECRET_KEY_LENGTH
  }

  fn public_bytes(&self) -> Self::PublicBytes<'_> {
    self.public_key.public_bytes()
  }

  fn secret_bytes(&self) -> Self::SecretBytes<'_> {
    self.secret_key.to_bytes()
  }

  fn deserialize(
    key_type: CryptoKeyTypes,
    public_bytes: &[u8],
    secret_bytes: &[u8],
  ) -> Result<Self, CryptoErr> {
    if key_type == CryptoKeyTypes::Ed25519Private {
      let pk_bytes: &[u8; 32] = u8::bbrfa(public_bytes, &mut 0)?;
      let public_key_deserialized =
        ed25519_dalek::VerifyingKey::from_bytes(pk_bytes)
          .map_err(|_| CryptoErr::Ed25519InvalidKey)?;

      let sk_bytes: &[u8; 32] = u8::bbrfa(secret_bytes, &mut 0)?;
      let secret_key = ed25519_dalek::SigningKey::from(sk_bytes);

      let public_key_calculated = secret_key.verifying_key();

      if public_key_calculated != public_key_deserialized {
        std::dbg!(public_key_calculated, public_key_deserialized);
        return Err(CryptoErr::Ed25519InvalidKey);
      }
      let fingerprint = Sha3Hash::new(public_bytes);
      Ok(Self {
        public_key: Ed25519PublicKey {
          fingerprint,
          public_key: public_key_calculated,
        },
        secret_key,
      })
    } else {
      Err(CryptoErr::WrongKeyType {
        expected: CryptoKeyTypes::Ed25519Private,
        observed: key_type,
      })
    }
  }
}

impl GenerableCryptoKey for Ed25519SecretKey {
  fn generate<R: Rng + CryptoRng>(rng: &mut R) -> Self {
    let sk = ed25519_dalek::SigningKey::generate(rng);
    let pk = sk.verifying_key();
    let fingerprint = Sha3Hash::new(&pk.to_bytes());

    Self {
      public_key: Ed25519PublicKey {
        fingerprint,
        public_key: pk,
      },
      secret_key: sk,
    }
  }
}

impl Debug for Ed25519SecretKey {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "Ed25519PrivateKey({:?})",
      &ShortHexDump(self.public_key.fingerprint.as_ref(), 0)
    )
  }
}

impl SigningKey for Ed25519SecretKey {
  type AuthenticationKey = Ed25519PublicKey;
  type Signature = Ed25519Signature;

  fn authentication_key(&self) -> &Self::AuthenticationKey {
    &self.public_key
  }

  fn sign(&self, bytes: &[u8]) -> Self::Signature {
    let sig = self.secret_key.sign(bytes);
    Ed25519Signature(sig)
  }
}

#[derive(Clone, Eq, PartialEq)]
pub struct Ed25519Signature(ed25519_dalek::Signature);

impl CryptoSignature for Ed25519Signature {
  type AuthenticationKey = Ed25519PublicKey;
  type SignatureBytes<'a> = [u8; 64];

  fn signature_type(&self) -> CryptoSignatureTypes {
    CryptoSignatureTypes::Ed25519
  }

  fn signature_length(&self) -> usize {
    ed25519_dalek::SIGNATURE_LENGTH
  }

  fn signature_bytes(&self) -> Self::SignatureBytes<'_> {
    self.0.to_bytes()
  }

  fn deserialize(
    sig_type: CryptoSignatureTypes,
    source: &[u8],
  ) -> Result<Self, CryptoErr> {
    if sig_type == CryptoSignatureTypes::Ed25519 {
      let bytes: &[u8; 64] = u8::bbrfa(source, &mut 0)?;
      let sig = ed25519_dalek::Signature::from_bytes(bytes);
      Ok(Self(sig))
    } else {
      Err(CryptoErr::WrongSignatureType {
        expected: CryptoSignatureTypes::Ed25519,
        observed: sig_type,
      })
    }
  }
}

impl Debug for Ed25519Signature {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "Ed25519Signature({:?})",
      &ShortHexDump(&self.0.to_bytes()[..], 0)
    )
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::crypto::{algos::SigningKey, test::TEST_PLAINTEXT};
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;

  #[test]
  fn crypto_ed25519() {
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);
    let secret_key = Ed25519SecretKey::generate(&mut rng);
    let public_key = secret_key.authentication_key();
    let signature = secret_key.sign(TEST_PLAINTEXT);

    public_key.authenticate(TEST_PLAINTEXT, &signature).unwrap();
    secret_key.authenticate(TEST_PLAINTEXT, &signature).unwrap();
    assert!(public_key.authenticate(b"IMPOSTER!", &signature).is_err());
    assert!(secret_key.authenticate(b"IMPOSTER!", &signature).is_err());

    // Serialize keys and the signature.
    let secret_bytes = secret_key.secret_bytes();
    let public_bytes = public_key.public_bytes();
    let signature_bytes = signature.signature_bytes();

    // The serialized public key should be the same as the public component of
    // the secret key.
    assert_eq!(public_bytes, secret_key.public_bytes());

    // Deserialize the public key from the public key bytes.
    let public_key_deserialized = Ed25519PublicKey::deserialize(
      public_key.key_type(),
      public_bytes.as_ref(),
      &[],
    )
    .unwrap();
    assert_eq!(public_key, &public_key_deserialized);

    // Deserialize the secret key from the serialized secret key bytes.
    let secret_key_deserialized = Ed25519SecretKey::deserialize(
      secret_key.key_type(),
      public_bytes.as_ref(),
      secret_bytes.as_ref(),
    )
    .unwrap();
    assert_eq!(secret_key, secret_key_deserialized);

    // Deserialize the public key from the private key.
    let public_key_deserialized = Ed25519PublicKey::deserialize(
      secret_key.key_type(),
      public_bytes.as_ref(),
      secret_bytes.as_ref(),
    )
    .unwrap();
    assert_eq!(public_key, &public_key_deserialized);

    // Deserialize the signature from the signature bytes.
    let signature_deserialized = Ed25519Signature::deserialize(
      signature.signature_type(),
      signature_bytes.as_ref(),
    )
    .unwrap();
    assert_eq!(signature, signature_deserialized);
  }
}
