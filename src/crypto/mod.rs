mod hash;
pub use self::hash::*;

#[cfg(feature = "md5")]
pub use crate::crypto::hash::md5::*;

#[cfg(feature = "sha1")]
pub use crate::crypto::hash::sha1::*;

#[cfg(feature = "sha2")]
pub use crate::crypto::hash::sha2::*;

#[cfg(feature = "sha3")]
pub use crate::crypto::hash::sha3::*;

#[cfg(feature = "blake3")]
pub use crate::crypto::hash::blake3::*;

mod password;
pub use self::password::*;

#[cfg(test)]
pub(crate) const TEST_PLAINTEXT: &[u8; 39] =
  b"Deutsche Truppen sind jetzt in England.";
