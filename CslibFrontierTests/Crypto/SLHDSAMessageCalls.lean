/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SLHDSA.MessageCalls
public meta import CslibFrontier.Crypto.Primitives.SLHDSA.MessageCalls

/-!
# SLH-DSA message-call clients

These clients exercise the exact FIPS 205 `PRF_msg` and `H_msg` byte packages for every distinct
dispatch and all six digest lengths. Expected outputs were independently computed from Sections
11.1--11.2.2 with Python's standard-library SHAKE256, SHA-256, SHA-512, and HMAC functions plus a
direct MGF1 loop. They are packaging fixtures, not NIST validation vectors or security evidence.
-/

set_option linter.privateModule false

public section

namespace SLHDSAMessageCallTests

open Cslib.Crypto Cslib.Crypto.SLHDSA

set_option linter.hashCommand false

private def sequence (start n : ℕ) : FixedBytes n := fun i =>
  ⟨(start + i.val) % 256, Nat.mod_lt _ (by decide)⟩

private def secretPRF (p : SecurityBytes) : NBytes p := sequence 0x10 p.count
private def publicSeed (p : SecurityBytes) : NBytes p := sequence 0x20 p.count
private def optionalRandomness (p : SecurityBytes) : NBytes p := sequence 0x40 p.count
private def randomizer (p : SecurityBytes) : NBytes p := sequence 0x70 p.count
private def publicRoot (p : SecurityBytes) : NBytes p := sequence 0xa0 p.count

private def message : List Byte := [0x00, 0x01, 0x02, 0xfe]

/-! ### Exact packages and parameter lengths -/

#guard prfMessageText (optionalRandomness .bytes16) message ==
  (optionalRandomness .bytes16).toList ++ message
#guard shakePRFMessageInput (secretPRF .bytes24) (optionalRandomness .bytes24) message ==
  (secretPRF .bytes24).toList ++ (optionalRandomness .bytes24).toList ++ message
#guard hMessageDigestInput (randomizer .bytes32) (publicSeed .bytes32)
    (publicRoot .bytes32) message ==
  (randomizer .bytes32).toList ++ (publicSeed .bytes32).toList ++
    (publicRoot .bytes32).toList ++ message

-- Algorithm 19's deterministic variant is the ordinary call with `opt_rand = PK.seed`.
#guard shakePRFMessageInput (secretPRF .bytes16) (publicSeed .bytes16) message ==
  (secretPRF .bytes16).toList ++ (publicSeed .bytes16).toList ++ message

#guard ParameterShape.digestBytes .bytes16 .small == 30
#guard ParameterShape.digestBytes .bytes16 .fast == 34
#guard ParameterShape.digestBytes .bytes24 .small == 39
#guard ParameterShape.digestBytes .bytes24 .fast == 42
#guard ParameterShape.digestBytes .bytes32 .small == 47
#guard ParameterShape.digestBytes .bytes32 .fast == 49

/-! ### Independent `PRF_msg` oracles -/

private def shakePRF16 : List Byte :=
  [0xac, 0x33, 0x81, 0x74, 0xfb, 0x27, 0x5d, 0x17,
    0xa4, 0xa8, 0x1a, 0x94, 0x0f, 0x6a, 0x84, 0x13]

private def shakePRF24 : List Byte :=
  [0xff, 0x60, 0x01, 0xa3, 0xa3, 0x58, 0xee, 0x62,
    0x00, 0x85, 0x62, 0xe1, 0x0c, 0xa4, 0x3c, 0x97,
    0xab, 0xc1, 0xa3, 0x95, 0xb2, 0xa0, 0x97, 0x72]

private def shakePRF32 : List Byte :=
  [0x29, 0x8d, 0x7a, 0x07, 0x08, 0xc7, 0xc8, 0x79,
    0xa2, 0x6b, 0x89, 0x99, 0x3a, 0x74, 0x7a, 0x78,
    0x9e, 0x48, 0xc4, 0x45, 0x98, 0x73, 0xb9, 0x69,
    0x17, 0x6b, 0x35, 0xe4, 0x31, 0x88, 0xb5, 0x2c]

private def sha2PRF16 : List Byte :=
  [0x10, 0xfa, 0x1a, 0x87, 0x42, 0x10, 0xc1, 0x4f,
    0xba, 0xe7, 0x3d, 0xd6, 0x61, 0x60, 0x0e, 0x05]

private def sha2PRF24 : List Byte :=
  [0xe3, 0x1d, 0xdd, 0x28, 0x80, 0x4d, 0x1b, 0x37,
    0x34, 0x57, 0xa1, 0x38, 0xb3, 0x86, 0x3e, 0x09,
    0xb0, 0xee, 0xa5, 0xef, 0xc4, 0x76, 0xdd, 0xf7]

private def sha2PRF32 : List Byte :=
  [0xe9, 0xcb, 0x94, 0x42, 0x69, 0x16, 0x9c, 0x83,
    0x9b, 0xf0, 0xe3, 0x2c, 0x25, 0x7b, 0x74, 0xf1,
    0x3d, 0xf8, 0xc0, 0xbc, 0xef, 0x0f, 0xd4, 0x68,
    0x55, 0x65, 0xd4, 0xee, 0x61, 0xc3, 0x56, 0xd2]

#guard (prfMessage .shake (secretPRF .bytes16) (optionalRandomness .bytes16) message
  (by decide)).toList == shakePRF16
#guard (prfMessage .shake (secretPRF .bytes24) (optionalRandomness .bytes24) message
  (by decide)).toList == shakePRF24
#guard (prfMessage .shake (secretPRF .bytes32) (optionalRandomness .bytes32) message
  (by decide)).toList == shakePRF32
#guard (prfMessage .sha2 (secretPRF .bytes16) (optionalRandomness .bytes16) message
  (by decide)).toList == sha2PRF16
#guard (prfMessage .sha2 (secretPRF .bytes24) (optionalRandomness .bytes24) message
  (by decide)).toList == sha2PRF24
#guard (prfMessage .sha2 (secretPRF .bytes32) (optionalRandomness .bytes32) message
  (by decide)).toList == sha2PRF32

private def shakePRFEmpty16 : List Byte :=
  [0x4c, 0xae, 0x59, 0x68, 0x24, 0xbc, 0x11, 0x07,
    0xa2, 0x28, 0xc8, 0xf5, 0x9a, 0xcc, 0x3f, 0xe6]

#guard (prfMessage .shake (secretPRF .bytes16) (optionalRandomness .bytes16) []
  (by decide)).toList == shakePRFEmpty16

private def shakeDeterministicPRF16 : List Byte :=
  [0x8c, 0xc3, 0x18, 0xb1, 0x38, 0xe8, 0xe9, 0xc3,
    0xf6, 0x65, 0x99, 0x64, 0x9b, 0xaf, 0xcb, 0x14]

private def sha2DeterministicPRF16 : List Byte :=
  [0x5e, 0xfd, 0xbc, 0x8f, 0x19, 0x2a, 0x04, 0x09,
    0xd8, 0xb8, 0x34, 0x08, 0x9e, 0xa9, 0xa8, 0x93]

#guard (prfMessage .shake (secretPRF .bytes16) (publicSeed .bytes16) message
  (by decide)).toList == shakeDeterministicPRF16
#guard (prfMessage .sha2 (secretPRF .bytes16) (publicSeed .bytes16) message
  (by decide)).toList == sha2DeterministicPRF16

/-! ### Independent `H_msg` oracles -/

private def shakeH16Fast : List Byte :=
  [0x34, 0x13, 0x67, 0x96, 0xa4, 0x49, 0x25, 0x2b,
    0xaa, 0x4f, 0x99, 0xf2, 0x9b, 0xf1, 0x4a, 0x87,
    0xed, 0x1c, 0x30, 0xbb, 0xb1, 0xff, 0xe6, 0xfd,
    0x66, 0xa6, 0x5e, 0xbf, 0x13, 0x0f, 0x47, 0x21,
    0x5b, 0xff]

private def sha2H16Fast : List Byte :=
  [0x72, 0x63, 0x74, 0xef, 0xb3, 0x8b, 0x8d, 0x8b,
    0x69, 0x3d, 0x74, 0x26, 0x1d, 0x8d, 0xa3, 0x7b,
    0x58, 0x5a, 0x3a, 0x83, 0xc0, 0xdd, 0xb8, 0x19,
    0x99, 0x51, 0xbc, 0x9f, 0xb6, 0xdf, 0x80, 0x85,
    0xd3, 0x3a]

private def shakeH24Fast : List Byte :=
  [0x7f, 0x1f, 0xea, 0x1a, 0xe4, 0x80, 0xb9, 0x48,
    0x57, 0x8e, 0xe9, 0x88, 0x6f, 0xed, 0xf3, 0xaa,
    0x0b, 0x67, 0x1e, 0x27, 0xcd, 0xbb, 0x52, 0xab,
    0xbf, 0xb7, 0x9c, 0x4f, 0xa2, 0x4c, 0x36, 0xc6,
    0x2e, 0x83, 0xd9, 0xe6, 0x81, 0xd5, 0xeb, 0x4f,
    0x1d, 0x38]

private def sha2H24Fast : List Byte :=
  [0x47, 0x4a, 0x0c, 0x19, 0x16, 0xea, 0x19, 0xa4,
    0xfa, 0xc8, 0xda, 0x77, 0x02, 0xc7, 0x3a, 0x56,
    0x50, 0xff, 0x0e, 0x04, 0x2b, 0xf2, 0x72, 0x5e,
    0x57, 0xd6, 0x61, 0x4b, 0x00, 0x30, 0x90, 0xb8,
    0xde, 0x7c, 0x7a, 0xa4, 0x53, 0xb2, 0xcd, 0x9b,
    0x13, 0xf0]

private def shakeH32Fast : List Byte :=
  [0x8d, 0x4e, 0xf7, 0x8b, 0xa6, 0x7b, 0xd1, 0x67,
    0xb2, 0xf3, 0x67, 0x94, 0xc2, 0xc0, 0x23, 0x9c,
    0x0a, 0x86, 0x6d, 0x8a, 0xfe, 0x52, 0xa3, 0x01,
    0x11, 0x03, 0x78, 0xd9, 0xc4, 0xd0, 0x9e, 0x04,
    0x07, 0xf6, 0xa9, 0x34, 0xdb, 0xc7, 0x11, 0x73,
    0x2a, 0x3b, 0x44, 0xfd, 0xe9, 0xb7, 0x61, 0x84,
    0x6b]

private def sha2H32Fast : List Byte :=
  [0xef, 0x9b, 0x92, 0xde, 0xac, 0xc4, 0xdb, 0xb4,
    0x47, 0xbf, 0xaa, 0x0e, 0x39, 0x3e, 0x44, 0x50,
    0xa7, 0x61, 0x03, 0xb0, 0xcf, 0x6e, 0x94, 0x7f,
    0xd0, 0xcf, 0x49, 0x24, 0x1a, 0x2c, 0xc9, 0xc5,
    0xab, 0x71, 0x61, 0x0e, 0xef, 0xa3, 0xa5, 0x66,
    0x6f, 0x9c, 0x8c, 0xac, 0xa6, 0x7c, 0xc1, 0x86,
    0x08]

#guard (hMessage .shake .small (randomizer .bytes16) (publicSeed .bytes16)
  (publicRoot .bytes16) message (by decide)).toList == shakeH16Fast.take 30
#guard (hMessage .shake .fast (randomizer .bytes16) (publicSeed .bytes16)
  (publicRoot .bytes16) message (by decide)).toList == shakeH16Fast
#guard (hMessage .sha2 .small (randomizer .bytes16) (publicSeed .bytes16)
  (publicRoot .bytes16) message (by decide)).toList == sha2H16Fast.take 30
#guard (hMessage .sha2 .fast (randomizer .bytes16) (publicSeed .bytes16)
  (publicRoot .bytes16) message (by decide)).toList == sha2H16Fast

#guard (hMessage .shake .small (randomizer .bytes24) (publicSeed .bytes24)
  (publicRoot .bytes24) message (by decide)).toList == shakeH24Fast.take 39
#guard (hMessage .shake .fast (randomizer .bytes24) (publicSeed .bytes24)
  (publicRoot .bytes24) message (by decide)).toList == shakeH24Fast
#guard (hMessage .sha2 .small (randomizer .bytes24) (publicSeed .bytes24)
  (publicRoot .bytes24) message (by decide)).toList == sha2H24Fast.take 39
#guard (hMessage .sha2 .fast (randomizer .bytes24) (publicSeed .bytes24)
  (publicRoot .bytes24) message (by decide)).toList == sha2H24Fast

#guard (hMessage .shake .small (randomizer .bytes32) (publicSeed .bytes32)
  (publicRoot .bytes32) message (by decide)).toList == shakeH32Fast.take 47
#guard (hMessage .shake .fast (randomizer .bytes32) (publicSeed .bytes32)
  (publicRoot .bytes32) message (by decide)).toList == shakeH32Fast
#guard (hMessage .sha2 .small (randomizer .bytes32) (publicSeed .bytes32)
  (publicRoot .bytes32) message (by decide)).toList == sha2H32Fast.take 47
#guard (hMessage .sha2 .fast (randomizer .bytes32) (publicSeed .bytes32)
  (publicRoot .bytes32) message (by decide)).toList == sha2H32Fast

private def sha2H16SmallEmpty : List Byte :=
  [0xbe, 0xc9, 0xd0, 0x3c, 0x57, 0xdb, 0xc9, 0xbc,
    0x15, 0x54, 0xa7, 0xb6, 0x82, 0x16, 0x17, 0x51,
    0x32, 0xca, 0xdd, 0xd4, 0x03, 0xa6, 0x28, 0x9a,
    0x34, 0xe3, 0xf8, 0x73, 0xf2, 0x7a]

#guard (hMessage .sha2 .small (randomizer .bytes16) (publicSeed .bytes16)
  (publicRoot .bytes16) [] (by decide)).toList == sha2H16SmallEmpty

/-! ### Source-component counts -/

#guard prfMessageCost .shake .bytes16 message.length ==
  MessageCallCost.mk 36 16 1 0 0
#guard prfMessageCost .sha2 .bytes16 message.length ==
  MessageCallCost.mk 180 16 0 4 0
#guard prfMessageCost .sha2 .bytes24 message.length ==
  MessageCallCost.mk 348 24 0 0 4
#guard prfMessageCost .sha2 .bytes32 message.length ==
  MessageCallCost.mk 356 32 0 0 4

#guard hMessageCost .shake .bytes32 .fast message.length ==
  MessageCallCost.mk 100 49 1 0 0
#guard hMessageCost .sha2 .bytes16 .small message.length ==
  MessageCallCost.mk 120 30 0 3 0
#guard hMessageCost .sha2 .bytes16 .fast message.length ==
  MessageCallCost.mk 188 34 0 5 0
#guard hMessageCost .sha2 .bytes24 .fast message.length ==
  MessageCallCost.mk 192 42 0 0 3
#guard hMessageCost .sha2 .bytes32 .fast message.length ==
  MessageCallCost.mk 232 49 0 0 3

#guard keccakRotationTableEntries == 25
#guard keccakRoundConstantEntries == 24
#guard sha256RoundConstantEntries == 64
#guard sha512RoundConstantEntries == 80
#guard sha2InitialStateWords == 8
#guard hmacPadConstants == 2
#guard mgfCounterBytes == 4
#guard digestLengthTableEntries == 6
#guard oracleHandlerCount == 0

example (family : HashFamily) (p : SecurityBytes) (shape : ParameterShape)
    (secret optional R seed root : NBytes p) (M : List Byte)
    (hprf : ValidPRFMessageInput family secret optional M)
    (hmsg : ValidHMessageInput family shape R seed root M) :
    (prfMessage family secret optional M hprf).toList.length = p.count ∧
      (hMessage family shape R seed root M hmsg).toList.length =
        ParameterShape.digestBytes p shape := by
  simp

end SLHDSAMessageCallTests
