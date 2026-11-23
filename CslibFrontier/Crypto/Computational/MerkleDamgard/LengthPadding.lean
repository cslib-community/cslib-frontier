/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.BinaryWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Foundations.Data.BitString.List.Rows
import CslibFrontier.Foundations.Data.List.Append
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Length-strengthened Merkle–Damgård padding

This module defines the length-strengthened padding block and `n`-bit block partition of
[BonehShoup2023], §8.4, Fig. 8.5 (pp. 296–297), proves that the padded message is block-aligned and
that the partition is suffix-free when the block count fits in the length field, and certifies that
the partition is computable in polynomial time. The hash built from it and Theorem 8.3 (p. 297) for
it are not in this module.

## Differences from Boneh–Shoup §8.4

* **Block and length-field widths**: the block width `ℓ` is taken to equal the parameter `n`, and
  the length field `⟨s⟩` has `n / 2` bits. In the book `⟨s⟩` is "a fixed-length bit string" and
  "Typically this field is 64-bits" (p. 296): its width does not depend on the block width.
* **Encoded count**: `mdLengthBlockCount n msg` counts the blocks of the padded message
  `M̂ = m_1 ‖ ⋯ ‖ m_s` (matching `u` and `v` in the proof of Theorem 8.3, p. 297), whereas p. 296
  describes `⟨s⟩` as the number of `ℓ`-bit blocks in `M`.
* **Total domain**: `mdLengthPad` and `mdLengthBlocks` are total over `msg : List Bool`. When
  `mdLengthBlockCount n msg ≥ 2 ^ (n / 2)` (including `n < 2`), `BitString.binaryWord (n / 2) s`
  exceeds `n / 2` bits and `BitString.listRows` drops bits past `s * n`, so the result outside the
  non-overflow range is not the book's padded message over `{0,1}^{≤L}`.

## Main definitions

* `Cslib.Crypto.mdLengthBlockCount`: the number of `n`-bit blocks produced by length-strengthened
  padding.
* `Cslib.Crypto.mdLengthPad`: the padded bit string `M ‖ PB`, where `PB = 1 ‖ 0^k ‖ ⟨s⟩`.
* `Cslib.Crypto.mdLengthBlocks`: the first `mdLengthBlockCount n msg` blocks of `n` bits of
  `mdLengthPad n msg`.

## Main results

* `Cslib.Crypto.length_mdLengthPad`: when the block count fits in the length field, the padded
  message has exactly `mdLengthBlockCount n msg * n` bits.
* `Cslib.Crypto.flatten_mdLengthBlocks`: in that case the blocks concatenate to the padded message.
* `Cslib.Crypto.mdLengthBlocks_suffix_iff`: suffix-freeness on messages whose padded block count is
  less than `2 ^ (n / 2)`.
* `Cslib.Crypto.computableInPolyTime_mdLengthBlocks`: `mdLengthBlocks` is computable in polynomial
  time.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], v0.6,
  §8.4, Fig. 8.5 and Theorem 8.3, pp. 296–297
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- Number of `n`-bit blocks produced by length-strengthened padding at block size `n` with an
`(n / 2)`-bit length field. -/
@[expose]
def mdLengthBlockCount (n : ℕ) (msg : List Bool) : ℕ :=
  (msg.length + n / 2) / n + 1

/-- Length-strengthened Merkle–Damgård padded message `M ‖ PB`, where `PB = 1 ‖ 0^k ‖ ⟨s⟩`:
`1`, the minimal number `k < n` of zeros making the total length a multiple of `n` when `⟨s⟩` fits
in `n / 2` bits, and the `(n / 2)`-bit big-endian encoding of `s = mdLengthBlockCount n msg`. -/
@[expose]
def mdLengthPad (n : ℕ) (msg : List Bool) : List Bool :=
  let w := n / 2
  let s := mdLengthBlockCount n msg
  let k := (n - (msg.length + 1 + w) % n) % n
  msg ++ true :: List.replicate k false ++ Cslib.BitString.binaryWord w s

/-- The first `s = mdLengthBlockCount n msg` consecutive `n`-bit blocks of `mdLengthPad n msg`.
When `s < 2 ^ (n / 2)` they are all of it (`flatten_mdLengthBlocks`). -/
@[expose]
def mdLengthBlocks (n : ℕ) (msg : List Bool) : List (List Bool) :=
  Cslib.BitString.listRows (mdLengthBlockCount n msg) n (mdLengthPad n msg)

@[simp]
theorem length_mdLengthBlocks (n : ℕ) (msg : List Bool) :
    (mdLengthBlocks n msg).length = mdLengthBlockCount n msg := by
  simp [mdLengthBlocks]

private theorem mdLengthBlockCount_pos (n : ℕ) (msg : List Bool) :
    0 < mdLengthBlockCount n msg := by
  simp [mdLengthBlockCount]

private theorem two_le_of_mdLengthBlockCount_lt {n : ℕ} {msg : List Bool}
    (hs : mdLengthBlockCount n msg < 2 ^ (n / 2)) : 2 ≤ n := by
  by_contra hn
  have h0 : n / 2 = 0 := by omega
  rw [h0] at hs
  have := mdLengthBlockCount_pos n msg
  omega

/-- Every block produced by `mdLengthBlocks n msg` has length `n`. -/
theorem length_of_mem_mdLengthBlocks {n : ℕ} {msg b : List Bool}
    (hb : b ∈ mdLengthBlocks n msg) : b.length = n :=
  Cslib.BitString.length_of_mem_listRows hb

/-- Block alignment: when the block count fits in the length field, the padded message consists of
exactly `mdLengthBlockCount n msg` blocks of `n` bits. -/
theorem length_mdLengthPad {n : ℕ} {msg : List Bool}
    (hs : mdLengthBlockCount n msg < 2 ^ (n / 2)) :
    (mdLengthPad n msg).length = mdLengthBlockCount n msg * n := by
  have hn : 0 < n := by have := two_le_of_mdLengthBlockCount_lt hs; omega
  have hdiv := Nat.div_add_mod' (msg.length + n / 2) n
  have hr := Nat.mod_lt (msg.length + n / 2) hn
  have ha : msg.length + 1 + n / 2 =
      (msg.length + n / 2) / n * n + ((msg.length + n / 2) % n + 1) := by omega
  simp only [mdLengthPad, List.length_append, List.length_cons, List.length_replicate,
    Cslib.BitString.length_binaryWord hs]
  simp only [mdLengthBlockCount, ha, Nat.mul_add_mod', Nat.add_mul, Nat.one_mul]
  rcases Nat.lt_or_ge ((msg.length + n / 2) % n + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show (msg.length + n / 2) % n + 1 = n by omega, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
    omega

/-- When the block count fits in the length field, the blocks of `mdLengthBlocks n msg` concatenate
to `mdLengthPad n msg`: no bit is dropped. -/
theorem flatten_mdLengthBlocks {n : ℕ} {msg : List Bool}
    (hs : mdLengthBlockCount n msg < 2 ^ (n / 2)) :
    (mdLengthBlocks n msg).flatten = mdLengthPad n msg :=
  Cslib.BitString.flatten_listRows_of_length (length_mdLengthPad hs)

/-- **The length-strengthened blocks are suffix-free**: when the longer message's padded block count
is less than `2 ^ (n / 2)`, `mdLengthBlocks n m₁` is a suffix of `mdLengthBlocks n m₂` if and only
if `m₁ = m₂`. The proof of [BonehShoup2023], Theorem 8.3 (p. 297) uses this property of the padding
when it deduces `u = v` from equal last blocks; the book does not state it separately. -/
theorem mdLengthBlocks_suffix_iff {n : ℕ} {m₁ m₂ : List Bool}
    (hs₂ : mdLengthBlockCount n m₂ < 2 ^ (n / 2)) :
    mdLengthBlocks n m₁ <:+ mdLengthBlocks n m₂ ↔ m₁ = m₂ := by
  refine ⟨fun hsuf => ?_, fun h => h ▸ List.suffix_refl _⟩
  have hs₁ : mdLengthBlockCount n m₁ < 2 ^ (n / 2) :=
    lt_of_le_of_lt (by simpa using hsuf.length_le) hs₂
  obtain ⟨p, hp⟩ := hsuf
  have hflat := congrArg List.flatten hp
  rw [List.flatten_append, flatten_mdLengthBlocks hs₁, flatten_mdLengthBlocks hs₂] at hflat
  simp only [mdLengthPad, ← List.append_assoc] at hflat
  obtain ⟨hpre, hbw⟩ := List.append_inj' hflat (by
    rw [Cslib.BitString.length_binaryWord hs₁, Cslib.BitString.length_binaryWord hs₂])
  have hcnt : mdLengthBlockCount n m₁ = mdLengthBlockCount n m₂ := by
    simpa [Cslib.BitString.binaryValue_binaryWord] using
      congrArg Cslib.BitString.binaryValue hbw
  obtain rfl : p = [] := by
    have hlen := congrArg List.length hp
    rw [List.length_append, length_mdLengthBlocks, length_mdLengthBlocks, hcnt] at hlen
    exact List.length_eq_zero_iff.mp (by omega)
  have hrev := congrArg List.reverse hpre
  simp only [List.flatten_nil, List.nil_append, List.reverse_append, List.reverse_cons,
    List.reverse_replicate, List.append_assoc, List.singleton_append] at hrev
  have hk := congrArg (List.idxOf true) hrev
  rw [List.idxOf_true_replicate_false_append, List.idxOf_true_replicate_false_append] at hk
  rw [hk] at hrev
  exact List.reverse_inj.mp (by simpa using hrev)

/-- The length-strengthened block partition `mdLengthBlocks n msg` is computable in polynomial time
from `(n, msg)` with `n` in unary and `msg` as a raw bit list. -/
@[program_certificate]
theorem computableInPolyTime_mdLengthBlocks :
    ComputableInPolyTime (fun p : ℕ × List Bool => mdLengthBlocks p.1 p.2)
      (encPair encUnary encBits) (encList encBits) := by
  have hs : ComputableInPolyTime (fun p : ℕ × List Bool => mdLengthBlockCount p.1 p.2)
      (encPair encUnary encBits) encUnary := by
    unfold mdLengthBlockCount
    fun_prop
  have hpre : ComputableInPolyTime (fun p : ℕ × List Bool => p.2 ++
      true :: List.replicate ((p.1 - (p.2.length + 1 + p.1 / 2) % p.1) % p.1) false)
      (encPair encUnary encBits) encBits := by
    fun_prop
  exact .bitsRowsWithInput hs (.fst _ _) (hpre.bitsAppend
    (Cslib.Complexity.binaryWord_polyTime (by fun_prop)
      (ComputableInPolyTime.unary_to_binary.comp hs)))

end Cslib.Crypto
