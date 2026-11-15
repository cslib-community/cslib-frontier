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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Foundations.Data.List.Append
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Length-strengthened Merkle–Damgård padding

This module defines the length-strengthened padding block and `n`-bit block partition from
[Boneh–Shoup, §8.4, Fig. 8.5, pp. 296–297][BonehShoup2023], proves its suffix-freeness when the
block count fits in the length field, and certifies that the block partition is computable in
polynomial time.

## Differences from Boneh–Shoup §8.4

* **Block and length-field widths**: the block width `ℓ` is taken to equal the parameter `n`, and
  the length field `⟨s⟩` has width `n / 2` bits rather than a fixed 64-bit width.
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
* `Cslib.Crypto.mdLengthBlocks`: the partition of `mdLengthPad n msg` into `n`-bit blocks.

## Main results

* `Cslib.Crypto.length_mdLengthBlocks`: `mdLengthBlocks n msg` has `mdLengthBlockCount n msg`
  blocks.
* `Cslib.Crypto.length_of_mem_mdLengthBlocks`: every block of `mdLengthBlocks n msg` has length `n`.
* `Cslib.Crypto.mdLengthBlocks_suffix_iff`: suffix-freeness on messages whose padded block count is
  less than `2 ^ (n / 2)`.
* `Cslib.Crypto.computableInPolyTime_mdLengthBlocks`: `mdLengthBlocks` is computable in polynomial
  time.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography* (v0.6),
  §8.4, Fig. 8.5, pp. 296–297][BonehShoup2023]
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

/-- Partition `mdLengthPad n msg` into `s = mdLengthBlockCount n msg` consecutive `n`-bit blocks. -/
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

private theorem mdLengthPad_length_eq {n : ℕ} {msg : List Bool}
    (hs : mdLengthBlockCount n msg < 2 ^ (n / 2)) :
    (mdLengthPad n msg).length = mdLengthBlockCount n msg * n := by
  have hn : 2 ≤ n := two_le_of_mdLengthBlockCount_lt hs
  have hn0 : 0 < n := by omega
  have hbw : (Cslib.BitString.binaryWord (n / 2) (mdLengthBlockCount n msg)).length = n / 2 :=
    Cslib.BitString.length_binaryWord hs
  simp only [mdLengthPad]
  rw [List.length_append, List.length_append, List.length_cons, List.length_replicate, hbw]
  simp only [mdLengthBlockCount]
  set m := msg.length
  set w := n / 2
  set q := (m + 1 + w) / n
  set r := (m + 1 + w) % n
  have hr : r < n := Nat.mod_lt _ hn0
  have hdiv : m + 1 + w = q * n + r := by
    simpa [q, r, Nat.mul_comm] using (Nat.div_add_mod (m + 1 + w) n).symm
  by_cases hr0 : r = 0
  · have hq0 : 1 ≤ q := Nat.pos_of_ne_zero fun hq => by
      rw [hq, hr0] at hdiv
      simp at hdiv
    set q' := q - 1
    have hq_eq : q = q' + 1 := (Nat.sub_add_cancel hq0).symm
    have hmul : q * n = q' * n + n := by
      rw [hq_eq, Nat.add_mul, Nat.one_mul]
    have hsub : m + w = q' * n + (n - 1) := by omega
    have hquot : (m + w) / n = q' := by
      rw [hsub, Nat.mul_comm q' n, Nat.mul_add_div hn0, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have hrem0 : (n - (m + 1 + w) % n) % n = 0 := by
      change (n - r) % n = 0
      rw [hr0]
      simp
    have hquot_mul : ((m + w) / n + 1) * n = q' * n + n := by
      rw [hquot, Nat.add_mul, Nat.one_mul]
    rw [hrem0, hquot_mul]
    omega
  · have hrem : (n - (m + 1 + w) % n) % n = n - r := by
      change (n - r) % n = n - r
      exact Nat.mod_eq_of_lt (by omega)
    have hsub : m + w = q * n + (r - 1) := by omega
    have hquot : (m + w) / n = q := by
      rw [hsub, Nat.mul_comm q n, Nat.mul_add_div hn0, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have hquot_mul : ((m + w) / n + 1) * n = q * n + n := by
      rw [hquot, Nat.add_mul, Nat.one_mul]
    rw [hrem, hquot_mul]
    omega

private theorem flatten_listRows_of_length_eq :
    ∀ (count n : ℕ) (word : List Bool),
      word.length = count * n → (Cslib.BitString.listRows count n word).flatten = word
  | 0, n, word, h => by
    simp only [Nat.zero_mul, List.length_eq_zero_iff] at h
    subst h
    simp [Cslib.BitString.listRows]
  | count + 1, n, word, h => by
    have htake : (word.take n).length = n := by
      apply List.length_take_of_le
      rw [h, Nat.succ_mul]
      omega
    have hdrop : (word.drop n).length = count * n := by
      rw [List.length_drop, h, Nat.succ_mul]
      omega
    conv_lhs => rw [← List.take_append_drop n word]
    rw [Cslib.BitString.listRows_succ_append count n htake (word.drop n), List.flatten_cons,
      flatten_listRows_of_length_eq count n (word.drop n) hdrop, List.take_append_drop]

private theorem flatten_mdLengthBlocks {n : ℕ} {msg : List Bool}
    (hs : mdLengthBlockCount n msg < 2 ^ (n / 2)) :
    (mdLengthBlocks n msg).flatten = mdLengthPad n msg :=
  flatten_listRows_of_length_eq (mdLengthBlockCount n msg) n (mdLengthPad n msg)
    (mdLengthPad_length_eq hs)

private theorem getLastD_mdLengthBlocks_drop_eq {n : ℕ} {msg : List Bool}
    (hs : mdLengthBlockCount n msg < 2 ^ (n / 2)) :
    ((mdLengthBlocks n msg).getLast?.getD []).drop (n - n / 2) =
      Cslib.BitString.binaryWord (n / 2) (mdLengthBlockCount n msg) := by
  have hlen_blocks : (mdLengthBlocks n msg).length = mdLengthBlockCount n msg :=
    length_mdLengthBlocks n msg
  have hlast_idx :
      (mdLengthBlocks n msg).getLast?.getD [] =
        Cslib.BitString.listRow n (mdLengthBlockCount n msg - 1) (mdLengthPad n msg) := by
    have hlt : mdLengthBlockCount n msg - 1 < (mdLengthBlocks n msg).length := by
      rw [hlen_blocks]
      have hpos : 0 < mdLengthBlockCount n msg := mdLengthBlockCount_pos n msg
      omega
    have hlen_sub : (mdLengthBlocks n msg).length - 1 = mdLengthBlockCount n msg - 1 := by
      rw [hlen_blocks]
    rw [List.getLast?_eq_getElem?, hlen_sub, List.getElem?_eq_getElem (by rw [hlen_blocks]; omega),
      Option.getD_some]
    simp only [mdLengthBlocks, Cslib.BitString.listRows, List.getElem_map, List.getElem_range]
  rw [hlast_idx]
  have hpad_len := mdLengthPad_length_eq hs
  have hw_len : (Cslib.BitString.binaryWord (n / 2) (mdLengthBlockCount n msg)).length = n / 2 :=
    Cslib.BitString.length_binaryWord hs
  apply List.ext_getElem
  · rw [List.length_drop, Cslib.BitString.length_listRow, hw_len]
    omega
  · intro i hi₁ hi₂
    have hi_w : i < n / 2 := by simpa [hw_len] using hi₂
    have hi_n : n - n / 2 + i < n := by omega
    rw [List.getElem_drop, Cslib.BitString.getElem_listRow hi_n]
    set s := mdLengthBlockCount n msg
    set k := (n - (msg.length + 1 + n / 2) % n) % n
    set pref := msg ++ true :: List.replicate k false
    have hpad_def : mdLengthPad n msg = pref ++ Cslib.BitString.binaryWord (n / 2) s := by
      simp [mdLengthPad, pref, k, s, List.append_assoc]
    have hpref_len : pref.length = s * n - n / 2 := by
      have hlen_sum : pref.length + n / 2 = s * n := by
        simpa [hpad_def, List.length_append, hw_len] using hpad_len
      omega
    have hns : n ≤ s * n := by
      have hspos : 1 ≤ s := mdLengthBlockCount_pos n msg
      calc n = 1 * n := (Nat.one_mul n).symm
        _ ≤ s * n := Nat.mul_le_mul_right n hspos
    have hsn : n / 2 ≤ s * n := (Nat.div_le_self n 2).trans hns
    have hidx_eq : (s - 1) * n + (n - n / 2 + i) = pref.length + i := by
      rw [hpref_len, Nat.sub_mul, Nat.one_mul]
      omega
    rw [hidx_eq, hpad_def, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp [List.length_append, hw_len, hi_w]),
      Option.getD_some, List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, s]

/-- **Suffix-freeness of length-strengthened Merkle–Damgård blocks ([BonehShoup2023], §8.4)**:
when the longer message's padded block count does not overflow `2 ^ (n / 2)`, `mdLengthBlocks n m₁`
is a suffix of `mdLengthBlocks n m₂` if and only if `m₁ = m₂`. -/
theorem mdLengthBlocks_suffix_iff {n : ℕ} {m₁ m₂ : List Bool}
    (hs₂ : mdLengthBlockCount n m₂ < 2 ^ (n / 2)) :
    mdLengthBlocks n m₁ <:+ mdLengthBlocks n m₂ ↔ m₁ = m₂ := by
  constructor
  · intro hsuf
    have hlen₁ : mdLengthBlockCount n m₁ ≤ mdLengthBlockCount n m₂ := by
      simpa [length_mdLengthBlocks] using hsuf.length_le
    have hs₁ : mdLengthBlockCount n m₁ < 2 ^ (n / 2) := lt_of_le_of_lt hlen₁ hs₂
    have hne₁ : mdLengthBlocks n m₁ ≠ [] := by
      intro h
      have := congrArg List.length h
      simp [length_mdLengthBlocks, mdLengthBlockCount] at this
    obtain ⟨p, hp⟩ := hsuf
    have hlast : (mdLengthBlocks n m₁).getLast? = (mdLengthBlocks n m₂).getLast? := by
      rw [← hp, List.getLast?_append_of_ne_nil p hne₁]
    have hbw :
        Cslib.BitString.binaryWord (n / 2) (mdLengthBlockCount n m₁) =
          Cslib.BitString.binaryWord (n / 2) (mdLengthBlockCount n m₂) := by
      rw [← getLastD_mdLengthBlocks_drop_eq hs₁, ← getLastD_mdLengthBlocks_drop_eq hs₂, hlast]
    have hcnt : mdLengthBlockCount n m₁ = mdLengthBlockCount n m₂ := by
      have := congrArg Cslib.BitString.binaryValue hbw
      simpa [Cslib.BitString.binaryValue_binaryWord] using this
    have hp_nil : p = [] := by
      have hlen := congrArg List.length hp
      rw [List.length_append, length_mdLengthBlocks, length_mdLengthBlocks, hcnt] at hlen
      exact List.length_eq_zero_iff.mp (by omega)
    subst hp_nil
    rw [List.nil_append] at hp
    have hpad_eq : mdLengthPad n m₁ = mdLengthPad n m₂ := by
      rw [← flatten_mdLengthBlocks hs₁, ← flatten_mdLengthBlocks hs₂, hp]
    simp only [mdLengthPad, hcnt] at hpad_eq
    have hstrip := List.append_cancel_right hpad_eq
    have hrev := congrArg List.reverse hstrip
    simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, List.singleton_append] at hrev
    have hk := congrArg (List.idxOf true) hrev
    rw [List.idxOf_true_replicate_false_append, List.idxOf_true_replicate_false_append] at hk
    rw [hk] at hrev
    exact List.reverse_inj.mp (by simpa using hrev)
  · rintro rfl
    exact List.suffix_refl _

private theorem computableInPolyTime_mdLengthBlockCount_comp {α : Type} {encIn : α ↪ List Bool}
    {n : α → ℕ} {msg : α → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    ComputableInPolyTime (fun a => mdLengthBlockCount (n a) (msg a)) encIn encUnary := by
  have hm_len : ComputableInPolyTime (fun a => (msg a).length) encIn encUnary :=
    ComputableInPolyTime.length_bits_comp hmsg
  have hw : ComputableInPolyTime (fun a => n a / 2) encIn encUnary :=
    (ComputableInPolyTime.unary_div_const 2).comp hn
  have hdiv : ComputableInPolyTime (fun a => ((msg a).length + n a / 2) / n a) encIn encUnary :=
    ComputableInPolyTime.unary_div' (ComputableInPolyTime.unary_add' hm_len hw) hn
  exact ComputableInPolyTime.unary_add' hdiv (.const 1)

private theorem computableInPolyTime_mdLengthPad_comp {α : Type} {encIn : α ↪ List Bool}
    {n : α → ℕ} {msg : α → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    ComputableInPolyTime (fun a => mdLengthPad (n a) (msg a)) encIn encBits := by
  have hm_len : ComputableInPolyTime (fun a => (msg a).length) encIn encUnary :=
    ComputableInPolyTime.length_bits_comp hmsg
  have hw : ComputableInPolyTime (fun a => n a / 2) encIn encUnary :=
    (ComputableInPolyTime.unary_div_const 2).comp hn
  have hsum : ComputableInPolyTime (fun a => (msg a).length + 1 + n a / 2) encIn encUnary :=
    ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hm_len (.const 1)) hw
  have hrem : ComputableInPolyTime (fun a => ((msg a).length + 1 + n a / 2) % n a)
      encIn encUnary :=
    ComputableInPolyTime.unary_mod' hsum hn
  have hk : ComputableInPolyTime (fun a => (n a - ((msg a).length + 1 + n a / 2) % n a) % n a)
      encIn encUnary :=
    ComputableInPolyTime.unary_mod' (ComputableInPolyTime.unary_sub' hn hrem) hn
  have hrep : ComputableInPolyTime
      (fun a => List.replicate ((n a - ((msg a).length + 1 + n a / 2) % n a) % n a) false)
      encIn encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp hk
  have hs := computableInPolyTime_mdLengthBlockCount_comp hn hmsg
  have hbw : ComputableInPolyTime
      (fun a => Cslib.BitString.binaryWord (n a / 2) (mdLengthBlockCount (n a) (msg a)))
      encIn encBits :=
    Cslib.Complexity.binaryWord_polyTime hw
      (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp hs.tidy))
  exact (hmsg.bitsAppend (ComputableInPolyTime.bitsCons (.const true) hrep)).bitsAppend hbw

/-- The length-strengthened block partition `mdLengthBlocks n msg` is computable in polynomial time
from `(n, msg)` with `n` in unary and `msg` as a raw bit list. -/
@[program_certificate]
theorem computableInPolyTime_mdLengthBlocks :
    ComputableInPolyTime (fun p : ℕ × List Bool => mdLengthBlocks p.1 p.2)
      (encPair encUnary encBits) (encList encBits) :=
  ComputableInPolyTime.bitsRowsWithInput
    (computableInPolyTime_mdLengthBlockCount_comp (.fst _ _) (.snd _ _))
    (.fst _ _)
    (computableInPolyTime_mdLengthPad_comp (.fst _ _) (.snd _ _))

end Cslib.Crypto
