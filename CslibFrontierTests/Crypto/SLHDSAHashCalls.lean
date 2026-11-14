/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SLHDSA.HashCalls
public meta import CslibFrontier.Crypto.Primitives.SLHDSA.HashCalls

/-!
# Addressed SLH-DSA hash-call clients

These clients exercise the byte packages prescribed by FIPS 205, Sections 11.1--11.2.2. The
expected outputs were independently computed from those equations with Python's standard-library
SHAKE256, SHA-256, and SHA-512 implementations; they are packaging fixtures, not NIST vectors or
end-to-end SLH-DSA calls. The patterned address fields are well-formed but intentionally make byte
positions visible rather than modeling bounds from one particular approved parameter set. Likewise,
`T_3` is a compact packaging fixture; three is not an approved WOTS+ `len` or FORS `k` value.
-/

set_option linter.privateModule false

public section

namespace SLHDSAHashCallTests

open Cslib.Crypto Cslib.Crypto.SLHDSA

set_option linter.hashCommand false

private def sequence (start n : ℕ) : FixedBytes n := fun i =>
  ⟨(start + i.val) % 256, Nat.mod_lt _ (by decide)⟩

private def publicSeed (p : SecurityBytes) : NBytes p := sequence 0x20 p.count
private def secretSeed (p : SecurityBytes) : NBytes p := sequence 0x60 p.count
private def message1 (p : SecurityBytes) : NBytes p := sequence 0xc0 p.count

private def message2 (p : SecurityBytes) : TwoNBytes p :=
  FixedBytes.pairBlocks (sequence 0xc0 p.count) (sequence (0xc0 + p.count) p.count)

private def message3Blocks (p : SecurityBytes) : Fin 3 → NBytes p := fun block offset =>
  ⟨(0xd0 + p.count * block.val + offset.val) % 256, Nat.mod_lt _ (by decide)⟩

private def message3 (p : SecurityBytes) : LBlocksBytes p 3 :=
  Cslib.BitString.blocksEquiv.symm (message3Blocks p)

private def prfAddress : Address :=
  Address.wotsPRF 0x00000003 0x0102030405060708 0x11223344 0x55667788

private def fAddress : Address :=
  Address.wotsHash 0x00000003 0x0102030405060708 0x11223344 0x55667788 0x99aabbcc

private def hAddress : Address :=
  Address.tree 0x00000003 0x0102030405060708 0x55667788 0x99aabbcc

private def tAddress : Address :=
  Address.wotsPK 0x00000003 0x0102030405060708 0x11223344

/-! ### Exact input packages -/

private def fAddressBytes : List Byte :=
  [0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00,
    0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
    0x00, 0x00, 0x00, 0x00, 0x11, 0x22, 0x33, 0x44,
    0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc]

private def fCompressedAddressBytes : List Byte :=
  [0x03, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x00, 0x11,
    0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc]

#guard shakeInput (publicSeed .bytes16) fAddress (message1 .bytes16) ==
  (publicSeed .bytes16).toList ++ fAddressBytes ++ (message1 .bytes16).toList

#guard sha256Input (publicSeed .bytes24) fAddress (message1 .bytes24) ==
  (publicSeed .bytes24).toList ++ List.replicate 40 0 ++ fCompressedAddressBytes ++
    (message1 .bytes24).toList

/-! ### Independent call oracles -/

private def shakeF16 : List Byte :=
  [0xce, 0x6e, 0x66, 0xd1, 0x9d, 0x54, 0x0a, 0x17,
    0xc0, 0xe9, 0x75, 0x5d, 0x58, 0x5b, 0x2b, 0x88]

private def shakePRF16 : List Byte :=
  [0x58, 0xed, 0xb1, 0x3c, 0xe3, 0x5b, 0xd7, 0x93,
    0x6d, 0x28, 0x54, 0x94, 0x9c, 0x30, 0xd5, 0x3d]

private def shakeH16 : List Byte :=
  [0x74, 0x6d, 0x13, 0x30, 0x15, 0xae, 0xc7, 0xce,
    0x3a, 0x59, 0xdc, 0xae, 0x2a, 0x16, 0xfd, 0xa9]

private def shakeT16 : List Byte :=
  [0x27, 0x49, 0x6e, 0x1b, 0x8c, 0xcf, 0xb6, 0x3d,
    0x2d, 0x6f, 0x9f, 0x64, 0xdc, 0x11, 0x40, 0xfd]

private def sha2PRF16 : List Byte :=
  [0x14, 0xb0, 0x7c, 0xfe, 0xf2, 0x53, 0x86, 0x82,
    0x94, 0x66, 0x5c, 0x71, 0xf3, 0xf1, 0x6f, 0x55]

private def sha2F24 : List Byte :=
  [0x16, 0xae, 0xda, 0x01, 0x93, 0x6f, 0x0f, 0xa6,
    0x80, 0x95, 0xaf, 0x04, 0x58, 0x6a, 0x17, 0x85,
    0xbe, 0x5b, 0x60, 0x74, 0x69, 0xde, 0x99, 0xb4]

private def sha2F32 : List Byte :=
  [0x9c, 0xc1, 0xc3, 0xda, 0xb7, 0x37, 0xa6, 0xe6,
    0x19, 0x3d, 0x36, 0x27, 0x4e, 0xaf, 0x1f, 0x4b,
    0x86, 0x67, 0xcf, 0xa9, 0x94, 0x1c, 0xf8, 0xe9,
    0xa1, 0x45, 0x0c, 0xfd, 0x49, 0xb4, 0xa3, 0xcd]

private def sha2H16 : List Byte :=
  [0x6a, 0xce, 0x77, 0x51, 0xac, 0xbc, 0x93, 0xe0,
    0x4e, 0x58, 0xd2, 0x1f, 0x98, 0x8d, 0x4c, 0x1c]

private def sha2H24 : List Byte :=
  [0xe9, 0x9e, 0xd9, 0xf0, 0x1c, 0x98, 0x95, 0xd8,
    0xcc, 0x61, 0xec, 0x3d, 0xeb, 0xc1, 0x31, 0x3d,
    0xe4, 0xc1, 0x48, 0xf6, 0xd2, 0x66, 0xa3, 0xe8]

private def sha2H32 : List Byte :=
  [0x3f, 0x46, 0x9b, 0xc7, 0x7b, 0xe2, 0x71, 0xef,
    0xf6, 0x4f, 0x44, 0x30, 0x71, 0x8e, 0xc3, 0x6f,
    0x52, 0x3f, 0x26, 0xdc, 0x08, 0x42, 0x53, 0x24,
    0x2c, 0x62, 0x1a, 0x78, 0x42, 0xea, 0xb4, 0x5e]

private def sha2T24 : List Byte :=
  [0x68, 0x63, 0x28, 0x02, 0x94, 0x18, 0x16, 0x6f,
    0xf3, 0x34, 0x86, 0xb6, 0x5c, 0xc0, 0x54, 0x75,
    0x66, 0x0c, 0x6c, 0xf0, 0xa2, 0x76, 0x8e, 0x1d]

private def sha2T16 : List Byte :=
  [0x8c, 0xde, 0x50, 0x04, 0x55, 0x1a, 0xba, 0x45,
    0x62, 0xb8, 0x7c, 0xbc, 0x60, 0xac, 0x1b, 0xd6]

private def sha2T32 : List Byte :=
  [0xc5, 0x73, 0xb4, 0x23, 0x8a, 0x89, 0x24, 0x91,
    0xe6, 0xd9, 0xe0, 0xbb, 0x23, 0x9b, 0xad, 0x87,
    0xda, 0xd3, 0xbd, 0x00, 0x72, 0x42, 0x66, 0xf0,
    0x40, 0xda, 0xa3, 0x82, 0x0e, 0x8e, 0xc6, 0xc3]

#guard (f .shake (publicSeed .bytes16) fAddress (message1 .bytes16)).toList == shakeF16
#guard (prf .shake (publicSeed .bytes16) (secretSeed .bytes16) prfAddress).toList == shakePRF16
#guard (h .shake (publicSeed .bytes16) hAddress (message2 .bytes16)).toList == shakeH16
#guard (tL .shake 3 (publicSeed .bytes16) tAddress (message3 .bytes16)
  (validTInput_of_blocks_le_67 .shake (publicSeed .bytes16) tAddress
    (message3 .bytes16) (by decide))).toList == shakeT16
#guard (prf .sha2 (publicSeed .bytes16) (secretSeed .bytes16) prfAddress).toList == sha2PRF16
#guard (f .sha2 (publicSeed .bytes24) fAddress (message1 .bytes24)).toList == sha2F24
#guard (f .sha2 (publicSeed .bytes32) fAddress (message1 .bytes32)).toList == sha2F32
#guard (h .sha2 (publicSeed .bytes16) hAddress (message2 .bytes16)).toList == sha2H16
#guard (h .sha2 (publicSeed .bytes24) hAddress (message2 .bytes24)).toList == sha2H24
#guard (h .sha2 (publicSeed .bytes32) hAddress (message2 .bytes32)).toList == sha2H32

#guard (tL .sha2 3 (publicSeed .bytes16) tAddress (message3 .bytes16)
  (validTInput_of_blocks_le_67 .sha2 (publicSeed .bytes16) tAddress
    (message3 .bytes16) (by decide))).toList == sha2T16
#guard (tL .sha2 3 (publicSeed .bytes24) tAddress (message3 .bytes24)
  (validTInput_of_blocks_le_67 .sha2 (publicSeed .bytes24) tAddress
    (message3 .bytes24) (by decide))).toList == sha2T24
#guard (tL .sha2 3 (publicSeed .bytes32) tAddress (message3 .bytes32)
  (validTInput_of_blocks_le_67 .sha2 (publicSeed .bytes32) tAddress
    (message3 .bytes32) (by decide))).toList == sha2T32

/-! ### Typed public clients -/

example (family : HashFamily) (p : SecurityBytes) (seed message : NBytes p)
    (address : Address) : (f family seed address message).toList.length = p.count := by
  simp

example (family : HashFamily) (p : SecurityBytes) (seed : NBytes p)
    (address : Address) (message : TwoNBytes p) :
    h family seed address message =
      tL family 2 seed address message
        (validTInput_of_blocks_le_67 family seed address message (by decide)) :=
  h_eq_tL_two family seed address message

-- The maximum standardized WOTS+ block count has no hidden SHA2 failure.
example (p : SecurityBytes) (seed : NBytes p) (address : Address)
    (message : LBlocksBytes p 67) : ValidTInput .sha2 seed address message :=
  validTInput_of_blocks_le_67 .sha2 seed address message (by decide)

end SLHDSAHashCallTests
