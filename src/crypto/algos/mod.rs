use crate::zerocopy::U16;
use std::intrinsics::transmute;

pub mod aes;
pub mod ed25519;

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
