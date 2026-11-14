/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.ByteString
public import CslibFrontier.Crypto.Primitives.SDitH.TweakSalt
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.Nat.CeilDiv

/-!
# SDitH counter-mode byte generation

SDitH v3 Algorithm 6 expands a seed by encrypting a sequence of plaintext blocks. The initial
plaintext is either zero or a tweaked salt; successive plaintexts XOR that value with a
little-endian counter. Parsed cipher blocks are concatenated and truncated to the requested byte
length.

The source is internally inconsistent about the block width. Algorithm 6 line 1 refers to an
undefined `nblock-bitsize`, while line 5 uses `lambda / 8` bytes. These differ in Category III,
where Section 3.2.1 gives `Enc` a 256-bit output for a 192-bit seed. The reference implementation
uses the full 32-byte Rijndael-256 output. Accordingly, this API keeps `cipherBits` and
`blockBytes` independent and makes the parsing boundary explicit.

This module specifies only the deterministic function. It does not instantiate AES or Rijndael,
assert pseudorandomness, or model `SampleIntegers` rejection sampling or the XOF-based
Fiat--Shamir challenges. It has no probabilistic abort term. For `B = ceil(nbytes / blockBytes)`,
the block list exposes exactly `B` calls each to the supplied cipher and parser and `B` counter
blocks. No native/uniform implementation or cost certificate is provided here.

## Main definitions

* `Cslib.Crypto.SDitH.prgTweak`: embed the eight-bit PRG tweak above the low 16 counter bits.
* `Cslib.Crypto.SDitH.prgInitialBlock`: the unsalted zero block or salted Algorithm 5 block.
* `Cslib.Crypto.SDitH.prgCounterWord`: a little-endian counter reduced modulo `2^securityBits`.
* `Cslib.Crypto.SDitH.prgBlocks`: the parsed full blocks used by Algorithm 6.
* `Cslib.Crypto.SDitH.prg`: the requested prefix of the concatenated block stream.

## Main results

* `Cslib.Crypto.SDitH.length_prgBlocks`: the block list has the requested block count.
* `Cslib.Crypto.SDitH.length_prgStream`: each parsed block contributes exactly `blockBytes` bytes.
* `Cslib.Crypto.SDitH.length_prg`: the output has exactly the requested byte length.
* `Cslib.Crypto.SDitH.take_prg`: longer requests preserve every byte of shorter requests.
* `Cslib.Crypto.SDitH.prgStream_discard_lt`: the truncated suffix is shorter than one block.

## References

* [*The Syndrome Decoding in the Head Signature Scheme*, v3.0, Sections 3.2.1--3.2.2,
  Algorithm 6, pp. 15, 17][SDitH2026]
-/

public section

namespace Cslib.Crypto.SDitH

/-- Embed Algorithm 6's eight-bit tweak above the 16 low counter bits. -/
@[expose]
def prgTweak (twk : Fin 256) : Fin (2 ^ 24) :=
  ⟨2 ^ 16 * twk.val, by
    have htwk := twk.isLt
    norm_num at htwk ⊢
    omega⟩

/-- The embedded PRG tweak has numeric value `2^16 * twk`. -/
@[simp]
theorem prgTweak_val (twk : Fin 256) : (prgTweak twk : Nat) = 2 ^ 16 * twk.val :=
  rfl

/-- The initial plaintext block for Algorithm 6.

The source pairs the optional salt and tweak: without them the block is zero; with them,
`TweakSalt` writes `2^16 * twk` into the low 24 bits and uses tag zero. The grinding variant is
kept explicit because the specification has distinct hash- and cipher-grinding layouts. -/
@[expose]
def prgInitialBlock (variant : GrindingVariant) {securityBits : Nat} :
    Option (BitString securityBits × Fin 256) → BitString securityBits
  | none => fun _ => false
  | some (salt, twk) => tweakSalt variant salt (prgTweak twk) false

/-- An unsalted Algorithm 6 stream starts from the all-zero plaintext. -/
@[simp]
theorem prgInitialBlock_none (variant : GrindingVariant) {securityBits : Nat} :
    prgInitialBlock variant (none : Option (BitString securityBits × Fin 256)) =
      (fun _ => false) :=
  rfl

/-- A salted Algorithm 6 stream starts from `TweakSalt(salt, 2^16 * twk, 0)`. -/
@[simp]
theorem prgInitialBlock_some (variant : GrindingVariant) {securityBits : Nat}
    (salt : BitString securityBits) (twk : Fin 256) :
    prgInitialBlock variant (some (salt, twk)) =
      tweakSalt variant salt (prgTweak twk) false :=
  rfl

/-- The little-endian `securityBits`-bit representation of a counter, reduced modulo
`2^securityBits` when the natural-number counter wraps. -/
@[expose]
def prgCounterWord (securityBits index : Nat) : BitString securityBits :=
  (BitString.equivFin securityBits).symm
    ⟨index % 2 ^ securityBits, Nat.mod_lt _ (by positivity)⟩

/-- Reading a counter word recovers the counter modulo its bit width. -/
@[simp]
theorem prgCounterWord_value (securityBits index : Nat) :
    (BitString.equivFin securityBits (prgCounterWord securityBits index) : Nat) =
      index % 2 ^ securityBits := by
  simp only [prgCounterWord, Equiv.apply_symm_apply]

/-- Before the counter wraps, `prgCounterWord` is the direct little-endian encoding of `index`. -/
theorem prgCounterWord_of_lt {securityBits index : Nat} (hindex : index < 2 ^ securityBits) :
    prgCounterWord securityBits index =
      (BitString.equivFin securityBits).symm ⟨index, hindex⟩ := by
  simp only [prgCounterWord, Nat.mod_eq_of_lt hindex]

/-- Algorithm 6's plaintext for counter `index`: XOR the initial block with its little-endian
counter word. This is deliberately not the modular-addition counter used by generic CTR mode. -/
@[expose]
def prgCounterBlock {securityBits : Nat} (initial : BitString securityBits) (index : Nat) :
    BitString securityBits :=
  initial + prgCounterWord securityBits index

/-- The numeric view of the plaintext block uses bitwise XOR, not modular addition. -/
theorem prgCounterBlock_value {securityBits : Nat} (initial : BitString securityBits)
    (index : Nat) :
    (BitString.equivFin securityBits (prgCounterBlock initial index) : Nat) =
      (BitString.equivFin securityBits initial : Nat) ^^^ (index % 2 ^ securityBits) := by
  rw [prgCounterBlock, BitString.val_equivFin_add, prgCounterWord_value]

/-- Before wraparound, the numeric plaintext is the initial block XOR the natural counter. -/
theorem prgCounterBlock_value_of_lt {securityBits index : Nat}
    (initial : BitString securityBits) (hindex : index < 2 ^ securityBits) :
    (BitString.equivFin securityBits (prgCounterBlock initial index) : Nat) =
      (BitString.equivFin securityBits initial : Nat) ^^^ index := by
  rw [prgCounterBlock_value, Nat.mod_eq_of_lt hindex]

/-- One parsed full block of the Algorithm 6 stream. The explicit parser resolves the boundary
between the source's cipher-output width and byte-block width. -/
@[expose]
def prgBlock {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed initial : BitString securityBits) (index : Nat) : FixedBytes blockBytes :=
  parseBlock (enc seed (prgCounterBlock initial index))

/-- The `blockCount` parsed full blocks of the Algorithm 6 stream. -/
@[expose]
def prgBlocks {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256))
    (blockCount : Nat) : List (FixedBytes blockBytes) :=
  (List.range blockCount).map fun index =>
    prgBlock enc parseBlock seed (prgInitialBlock variant context) index

/-- The parsed block list has exactly the requested number of blocks. -/
@[simp]
theorem length_prgBlocks {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256)) (blockCount : Nat) :
    (prgBlocks enc parseBlock seed variant context blockCount).length = blockCount := by
  simp only [prgBlocks, List.length_map, List.length_range]

/-- Taking an initial number of full blocks commutes with their generation. -/
theorem take_prgBlocks {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256)) {m n : Nat} (h : m ≤ n) :
    (prgBlocks enc parseBlock seed variant context n).take m =
      prgBlocks enc parseBlock seed variant context m := by
  simp only [prgBlocks, List.take_map, List.take_range, Nat.min_eq_left h]

/-- The byte stream obtained by concatenating the parsed full blocks. -/
@[expose]
def prgStream {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256))
    (blockCount : Nat) : List Byte :=
  (prgBlocks enc parseBlock seed variant context blockCount).flatMap FixedBytes.toList

/-- Concatenating `blockCount` parsed blocks materializes exactly
`blockBytes * blockCount` bytes. -/
@[simp]
theorem length_prgStream {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256)) (blockCount : Nat) :
    (prgStream enc parseBlock seed variant context blockCount).length =
      blockBytes * blockCount := by
  rw [prgStream,
    List.length_flatMap_of_forall_length_eq (k := blockBytes)
      (fun block _ => FixedBytes.length_toList block),
    length_prgBlocks, Nat.mul_comm]

/-- Requesting more full blocks preserves every byte of the earlier blocks. -/
theorem take_prgStream {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256)) {m n : Nat} (h : m ≤ n) :
    (prgStream enc parseBlock seed variant context n).take (blockBytes * m) =
      prgStream enc parseBlock seed variant context m := by
  rw [prgStream,
    List.take_flatMap_of_forall_length_eq m (fun block _ => FixedBytes.length_toList block),
    take_prgBlocks enc parseBlock seed variant context h, prgStream]

/-- SDitH v3 Algorithm 6's requested byte output.

`blockBytes` must be positive for the length and truncation contracts below. Keeping it independent
of `securityBits` records the Category III source discrepancy rather than silently choosing one of
the two conflicting widths. -/
@[expose]
def prg {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256))
    (outputBytes : Nat) : List Byte :=
  (prgStream enc parseBlock seed variant context (outputBytes ⌈/⌉ blockBytes)).take outputBytes

/-- For a positive parsed block width, Algorithm 6 returns exactly the requested number of
bytes. -/
@[simp]
theorem length_prg {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256))
    (hblockBytes : 0 < blockBytes) (outputBytes : Nat) :
    (prg enc parseBlock seed variant context outputBytes).length = outputBytes := by
  rw [prg, List.length_take, length_prgStream, Nat.min_eq_left]
  exact le_smul_ceilDiv (a := blockBytes) (b := outputBytes) hblockBytes

/-- Algorithm 6 is prefix-consistent: requesting more output never changes preceding bytes. -/
theorem take_prg {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256))
    (hblockBytes : 0 < blockBytes) {m n : Nat} (h : m ≤ n) :
    (prg enc parseBlock seed variant context n).take m =
      prg enc parseBlock seed variant context m := by
  rw [prg, List.take_take, Nat.min_eq_left h, prg]
  have hk : m ⌈/⌉ blockBytes ≤ n ⌈/⌉ blockBytes := by
    rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_le_div_right (by omega)
  have hm : m ≤ blockBytes * (m ⌈/⌉ blockBytes) :=
    le_smul_ceilDiv (a := blockBytes) (b := m) hblockBytes
  calc
    (prgStream enc parseBlock seed variant context (n ⌈/⌉ blockBytes)).take m =
        ((prgStream enc parseBlock seed variant context (n ⌈/⌉ blockBytes)).take
          (blockBytes * (m ⌈/⌉ blockBytes))).take m := by
      rw [List.take_take, Nat.min_eq_left hm]
    _ = (prgStream enc parseBlock seed variant context (m ⌈/⌉ blockBytes)).take m := by
      rw [take_prgStream enc parseBlock seed variant context hk]

/-- The full block stream materialized for a positive block width discards fewer than one block
when truncated to the requested output length. -/
theorem prgStream_discard_lt {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256))
    (hblockBytes : 0 < blockBytes) (outputBytes : Nat) :
    (prgStream enc parseBlock seed variant context
      (outputBytes ⌈/⌉ blockBytes)).length - outputBytes < blockBytes := by
  rw [length_prgStream, Nat.mul_comm]
  have hcover := Nat.le_ceilDiv_mul (a := outputBytes) hblockBytes
  have hover := Nat.ceilDiv_mul_lt (a := outputBytes) hblockBytes
  omega

/-- Requesting no bytes returns the empty output. -/
@[simp]
theorem prg_zero_output {securityBits cipherBits blockBytes : Nat}
    (enc : BitString securityBits → BitString securityBits → BitString cipherBits)
    (parseBlock : BitString cipherBits → FixedBytes blockBytes)
    (seed : BitString securityBits) (variant : GrindingVariant)
    (context : Option (BitString securityBits × Fin 256)) :
    prg enc parseBlock seed variant context 0 = [] := by
  simp only [prg, List.take_zero]

end Cslib.Crypto.SDitH
