use crate::crypto::algos::ed25519::Ed25519PublicKey;

/// A cryptographic key that can be used to authenticate a message.
pub enum AuthenticationKey {
  Ed25519(Ed25519PublicKey),
}
