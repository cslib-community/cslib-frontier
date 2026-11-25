/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Crypto.Computational.OneTimeSignature.ContainmentFree
public import CslibFrontier.Foundations.Data.BitString.Counter
public import CslibFrontier.Init
public import Mathlib.Data.Fin.Tuple.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.BitString.Weight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fintype.EquivFin

/-!
# Domination-free encodings and the Winternitz encoding

This module formalizes domination-free encodings and the Winternitz checksum encoding from
Boneh–Shoup, Section 14.3 (Definition 14.4, Section 14.3.1, and Lemma 14.5, pp. 591–593).

A function `P : M → Fin n → Fin (d + 1)` is *domination-free* (`DominationFree`) when no pair of
distinct messages `m ≠ m'` satisfies `P m ≤ P m'` coordinatewise. The Winternitz encoding
(`winternitzDigits d n0 n1 m`) decomposes `m < (d + 1) ^ n0` into `n0` base-`(d + 1)` message
digits `radixDigits d n0 m`, computes the complement checksum
`∑ i : Fin n0, (d - (radixDigits d n0 m i).val)`, and appends its `n1` base-`(d + 1)` digits.
When `d * n0 < (d + 1) ^ n1` and `f : M → ℕ` injects `M` into `{x | x < (d + 1) ^ n0}`, the
resulting encoding is domination-free (`winternitzDigits_dominationFree`).

We also provide an executable list form `winternitzDigitList` together with its `List.ofFn`
characterization (`winternitzDigitList_eq_ofFn`), length and entry agreements
(`winternitzDigitList_length`, `getElem_winternitzDigitList`), and a polynomial-time certificate
`winternitzDigitList_polyTime` in binary `d, m` and unary `n0, n1`.

## Main definitions

* `Cslib.Crypto.OneTimeSignature.DominationFree`: domination-free encodings
  `M → Fin n → Fin (d + 1)`.
* `Cslib.Crypto.OneTimeSignature.radixDigits`: little-endian base-`(d + 1)` digit vector of length
  `width`.
* `Cslib.Crypto.OneTimeSignature.winternitzDigits`: Winternitz message-and-checksum digit vector of
  length `n0 + n1`.
* `Cslib.Crypto.OneTimeSignature.winternitzDigitList`: executable list of Winternitz
  message-and-checksum digits.

## Main results

* `Cslib.Crypto.OneTimeSignature.dominationFree_of_append_checksum`: append-checksum criterion for
  domination-freeness (argument of Lemma 14.5, p. 593).
* `Cslib.Crypto.OneTimeSignature.sum_radixDigits_mul_pow`: positional reconstruction of
  `x < (d + 1) ^ width`.
* `Cslib.Crypto.OneTimeSignature.radixDigits_injOn`: injectivity of `radixDigits d width` below
  `(d + 1) ^ width`.
* `Cslib.Crypto.OneTimeSignature.le_of_radixDigits_le`: coordinatewise digit comparison implies
  numeric comparison.
* `Cslib.Crypto.OneTimeSignature.winternitzDigits_dominationFree`: Lemma 14.5 (p. 593), for any
  `n1` with `d * n0 < (d + 1) ^ n1`.
* `Cslib.Crypto.OneTimeSignature.winternitzDigitList_eq_ofFn`: `List.ofFn` agreement with
  `winternitzDigits`.
* `Cslib.Crypto.OneTimeSignature.winternitzDigitList_polyTime`: polynomial-time computability of
  `winternitzDigitList`.
* `Cslib.Crypto.OneTimeSignature.winternitzDigits_one_eq_one_iff_mem_optSet`: equivalence of
  `winternitzDigits 1` with `optSet` ([BonehShoup2023], Section 14.3.1, p. 593).

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.3 (Definition 14.4, Section 14.3.1, and Lemma 14.5, pp. 591–593).
-/

public section

namespace Cslib.Crypto.OneTimeSignature

open Turing.MultiTapeTM

/-- A function `P : M → Fin n → Fin (d + 1)` is *domination-free* ([BonehShoup2023],
Definition 14.4, p. 591) if no distinct messages `m ≠ m'` satisfy `P m ≤ P m'` coordinatewise. -/
@[expose] def DominationFree {M : Type*} {n d : ℕ} (P : M → Fin n → Fin (d + 1)) : Prop :=
  ∀ ⦃m m' : M⦄, m ≠ m' → ¬ P m ≤ P m'

/-- Append-checksum criterion, the argument of the proof of Lemma 14.5 in [BonehShoup2023]
(p. 593): if `P0` is injective, `∑ i, (P0 m i).val + checksum m` is the same number `C` for every
`m`, and `P1 m ≤ P1 m'` implies `checksum m ≤ checksum m'`, then
`fun m => Fin.append (P0 m) (P1 m)` is domination-free. -/
theorem dominationFree_of_append_checksum {M : Type*} {n0 n1 d : ℕ}
    {P0 : M → Fin n0 → Fin (d + 1)} {P1 : M → Fin n1 → Fin (d + 1)} {checksum : M → ℕ} {C : ℕ}
    (h0 : Function.Injective P0)
    (hsum : ∀ m, ∑ i, (P0 m i).val + checksum m = C)
    (hmono : ∀ ⦃m m' : M⦄, P1 m ≤ P1 m' → checksum m ≤ checksum m') :
    DominationFree (fun m => Fin.append (P0 m) (P1 m)) := by
  intro m m' hne hle
  have hle0 : P0 m ≤ P0 m' := fun i => by
    simpa [Fin.append_left] using hle (Fin.castAdd n1 i)
  have hle1 : P1 m ≤ P1 m' := fun j => by
    simpa [Fin.append_right] using hle (Fin.natAdd n0 j)
  obtain ⟨-, j, hj⟩ := Pi.lt_def.mp (lt_of_le_of_ne hle0 fun h => hne (h0 h))
  have hlt : ∑ i, (P0 m i).val < ∑ i, (P0 m' i).val :=
    Finset.sum_lt_sum (fun i _ => hle0 i) ⟨j, Finset.mem_univ j, hj⟩
  have := hmono hle1
  have := hsum m
  have := hsum m'
  lia

/-- Little-endian base-`(d + 1)` digit representation of `x` in `width` digits, taking digit `i`
to `(x / (d + 1) ^ i) % (d + 1)`. -/
@[expose] def radixDigits (d width x : ℕ) : Fin width → Fin (d + 1) :=
  fun i => ⟨(x / (d + 1) ^ i.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩

private theorem finFunctionFinEquiv_symm_eq_radixDigits {d width x : ℕ}
    (hx : x < (d + 1) ^ width) :
    finFunctionFinEquiv.symm (⟨x, hx⟩ : Fin ((d + 1) ^ width)) = radixDigits d width x := by
  ext i
  exact finFunctionFinEquiv_symm_apply_val (⟨x, hx⟩ : Fin ((d + 1) ^ width)) i

/-- Positional reconstruction of `x < (d + 1) ^ width` from `radixDigits d width x`. -/
theorem sum_radixDigits_mul_pow {d width x : ℕ} (hx : x < (d + 1) ^ width) :
    ∑ i : Fin width, (radixDigits d width x i).val * (d + 1) ^ i.val = x := by
  have h := congrArg Fin.val
    (finFunctionFinEquiv.apply_symm_apply (⟨x, hx⟩ : Fin ((d + 1) ^ width)))
  rw [finFunctionFinEquiv_symm_eq_radixDigits hx, finFunctionFinEquiv_apply] at h
  exact h

/-- `radixDigits d width` is injective on `{x | x < (d + 1) ^ width}`. -/
theorem radixDigits_injOn (d width : ℕ) :
    Set.InjOn (radixDigits d width) {x | x < (d + 1) ^ width} := by
  intro x hx y hy hxy
  have hsymm :
      finFunctionFinEquiv.symm (⟨x, hx⟩ : Fin ((d + 1) ^ width)) =
        finFunctionFinEquiv.symm (⟨y, hy⟩ : Fin ((d + 1) ^ width)) := by
    rw [finFunctionFinEquiv_symm_eq_radixDigits hx,
      finFunctionFinEquiv_symm_eq_radixDigits hy, hxy]
  exact congrArg Fin.val (finFunctionFinEquiv.symm.injective hsymm)

/-- Coordinatewise order on `radixDigits` implies numeric order below `(d + 1) ^ width`. -/
theorem le_of_radixDigits_le {d width x y : ℕ}
    (hx : x < (d + 1) ^ width) (hy : y < (d + 1) ^ width)
    (hle : radixDigits d width x ≤ radixDigits d width y) : x ≤ y := by
  rw [← sum_radixDigits_mul_pow hx, ← sum_radixDigits_mul_pow hy]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (hle i)

private theorem sum_radixDigits_add_sum_sub (d n0 x : ℕ) :
    ∑ i : Fin n0, (radixDigits d n0 x i).val + ∑ i : Fin n0, (d - (radixDigits d n0 x i).val) =
      d * n0 := by
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ =>
    Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (radixDigits d n0 x i).isLt)]
  simp [Nat.mul_comm]

/-- The function `P` of [BonehShoup2023], Section 14.3.1 (pp. 592–593), on a message `m : ℕ`:
the `n0` base-`(d + 1)` digits of `m`, then the `n1` base-`(d + 1)` digits of the checksum
`∑ i : Fin n0, (d - (radixDigits d n0 m i).val)`, which equals the printed
`d * n0 - (s_1 + ... + s_n0)`. Both blocks are least significant first, a choice made here:
domination-freeness does not depend on the order within a block. -/
@[expose] def winternitzDigits (d n0 n1 m : ℕ) : Fin (n0 + n1) → Fin (d + 1) :=
  let m0 := radixDigits d n0 m
  let checksum := ∑ i : Fin n0, (d - (m0 i).val)
  Fin.append m0 (radixDigits d n1 checksum)

/-- Lemma 14.5 of [BonehShoup2023] (p. 593): `fun m => winternitzDigits d n0 n1 (f m)` is
domination-free when `f : M → ℕ` is injective with values below `(d + 1) ^ n0` and
`d * n0 < (d + 1) ^ n1`.

The book states it for the messages `{0,1}^v` read as the integers below `2 ^ v`, with `n0`
the least integer such that `2 ^ v ≤ (d + 1) ^ n0` and `n1 = ⌈log_(d+1) (d * n0)⌉ + 1`: the
instance `f = Fin.val` on `Fin (2 ^ v)` with `n1 = Nat.clog (d + 1) (d * n0) + 1`. Minimality
of `n0` is not used. The table on p. 592 takes the least `n1` with `d * n0 < (d + 1) ^ n1`,
one less than the printed formula for `d = 3, 15, 1023`. -/
theorem winternitzDigits_dominationFree {M : Type*} {d n0 n1 : ℕ}
    {f : M → ℕ} (hf_inj : Function.Injective f)
    (hf_bound : ∀ m, f m < (d + 1) ^ n0) (hn1 : d * n0 < (d + 1) ^ n1) :
    DominationFree (fun m => winternitzDigits d n0 n1 (f m)) := by
  have hlt (m : M) : ∑ i : Fin n0, (d - (radixDigits d n0 (f m) i).val) < (d + 1) ^ n1 := by
    have := sum_radixDigits_add_sum_sub d n0 (f m)
    lia
  exact dominationFree_of_append_checksum
    (fun m m' h => hf_inj (radixDigits_injOn d n0 (hf_bound m) (hf_bound m') h))
    (fun m => sum_radixDigits_add_sum_sub d n0 (f m))
    (fun m m' h => le_of_radixDigits_le (hlt m) (hlt m') h)

-- Executable list of `width` little-endian base-`(d + 1)` digits of `x`.
private def radixDigitList (d width x : ℕ) : List ℕ :=
  (List.range width).map (fun i => (x / (d + 1) ^ i) % (d + 1))

/-- Executable list of `n0 + n1` Winternitz message-and-checksum digits for `m`. -/
def winternitzDigitList (d n0 n1 m : ℕ) : List ℕ :=
  let m0 := radixDigitList d n0 m
  m0 ++ radixDigitList d n1 (d * n0 - m0.sum)

private theorem radixDigitList_length (d width x : ℕ) :
    (radixDigitList d width x).length = width := by
  simp [radixDigitList]

private theorem sum_radixDigitList_eq (d n0 m : ℕ) :
    (radixDigitList d n0 m).sum = ∑ i : Fin n0, (radixDigits d n0 m i).val := by
  dsimp only [radixDigitList, radixDigits]
  rw [Fin.sum_univ_eq_sum_range (fun i => m / (d + 1) ^ i % (d + 1))]
  induction n0 with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      Finset.sum_range_succ, ih]

private theorem checksum_eq_sub_sum_radixDigitList (d n0 m : ℕ) :
    ∑ i : Fin n0, (d - (radixDigits d n0 m i).val) =
      d * n0 - (radixDigitList d n0 m).sum := by
  have := sum_radixDigits_add_sum_sub d n0 m
  rw [sum_radixDigitList_eq]
  lia

/-- Length of `winternitzDigitList d n0 n1 m`. -/
theorem winternitzDigitList_length (d n0 n1 m : ℕ) :
    (winternitzDigitList d n0 n1 m).length = n0 + n1 := by
  simp [winternitzDigitList, radixDigitList_length]

/-- Every entry of `winternitzDigitList d n0 n1 m` equals the corresponding coordinate of
`winternitzDigits d n0 n1 m`. -/
theorem getElem_winternitzDigitList (d n0 n1 m : ℕ) (i : ℕ)
    (hi : i < (winternitzDigitList d n0 n1 m).length) :
    (winternitzDigitList d n0 n1 m)[i] =
      (winternitzDigits d n0 n1 m ⟨i, by simpa [winternitzDigitList_length] using hi⟩).val := by
  have hi' : i < n0 + n1 := by simpa [winternitzDigitList_length] using hi
  revert hi
  dsimp only [winternitzDigitList, winternitzDigits]
  intro hi
  by_cases h0 : i < n0
  · rw [List.getElem_append_left (by simpa [radixDigitList_length] using h0)]
    have hidx : (⟨i, hi'⟩ : Fin (n0 + n1)) = Fin.castAdd n1 ⟨i, h0⟩ := rfl
    rw [hidx, Fin.append_left]
    simp [radixDigitList, radixDigits]
  · have hge : (radixDigitList d n0 m).length ≤ i := by
      simpa [radixDigitList_length] using Nat.le_of_not_lt h0
    rw [List.getElem_append_right hge]
    have hsub : i - n0 < n1 := by lia
    have hidx : (⟨i, hi'⟩ : Fin (n0 + n1)) = Fin.natAdd n0 ⟨i - n0, hsub⟩ := by
      ext
      dsimp
      lia
    rw [hidx, Fin.append_right, checksum_eq_sub_sum_radixDigitList]
    simp [radixDigitList, radixDigits]

/-- `winternitzDigitList d n0 n1 m` as `List.ofFn` of `winternitzDigits d n0 n1 m`. -/
theorem winternitzDigitList_eq_ofFn (d n0 n1 m : ℕ) :
    winternitzDigitList d n0 n1 m = List.ofFn fun i => (winternitzDigits d n0 n1 m i).val := by
  apply List.ext_getElem
  · simp [winternitzDigitList_length]
  · intro i h1 h2
    simp [getElem_winternitzDigitList]

private theorem radixDigitList_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => radixDigitList p.1 p.2.1 p.2.2)
      (encPair encNat (encPair encUnary encNat)) (encList encNat) := by
  let encIn := encPair encNat (encPair encUnary encNat)
  have hwidth : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => p.2.1) encIn encUnary := by fun_prop
  refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hwidth) ?_
  have hd1 : ComputableInPolyTime (fun q : (ℕ × ℕ × ℕ) × ℕ => q.1.1 + 1)
      (encPair encIn encUnary) encNat :=
    ComputableInPolyTime.binary_add' (by fun_prop) (ComputableInPolyTime.const 1)
  have hpow : ComputableInPolyTime (fun q : (ℕ × ℕ × ℕ) × ℕ => (q.1.1 + 1) ^ q.2)
      (encPair encIn encUnary) encNat :=
    ComputableInPolyTime.binary_pow' hd1 (by fun_prop)
  have hxq : ComputableInPolyTime (fun q : (ℕ × ℕ × ℕ) × ℕ => q.1.2.2)
      (encPair encIn encUnary) encNat := by fun_prop
  have hdiv : ComputableInPolyTime (fun q : (ℕ × ℕ × ℕ) × ℕ => q.1.2.2 / (q.1.1 + 1) ^ q.2)
      (encPair encIn encUnary) encNat :=
    ComputableInPolyTime.binary_div.comp (hxq.prod hpow)
  exact ComputableInPolyTime.binary_mod.comp (hdiv.prod hd1)

/-- `winternitzDigitList` is computable in polynomial time when `d` and `m` are encoded in
binary (`encNat`) and the digit counts `n0` and `n1` are encoded in unary (`encUnary`). -/
theorem winternitzDigitList_polyTime :
    ComputableInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ => winternitzDigitList p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encNat (encPair encUnary (encPair encUnary encNat))) (encList encNat) := by
  let encIn := encPair encNat (encPair encUnary (encPair encUnary encNat))
  have hd : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => p.1) encIn encNat := by fun_prop
  have hn0 : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => p.2.1) encIn encUnary := by fun_prop
  have hn1 : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.1) encIn encUnary := by fun_prop
  have hm0 : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => radixDigitList p.1 p.2.1 p.2.2.2)
      encIn (encList encNat) :=
    radixDigitList_polyTime.comp (hd.prod (hn0.prod (by fun_prop)))
  have hcs : ComputableInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ => p.1 * p.2.1 - (radixDigitList p.1 p.2.1 p.2.2.2).sum)
      encIn encNat :=
    ComputableInPolyTime.binary_sub'
      (ComputableInPolyTime.binary_mul' hd (ComputableInPolyTime.unary_to_binary.comp hn0))
      (ComputableInPolyTime.binary_sum.comp hm0)
  exact ComputableInPolyTime.listAppend' hm0
    (radixDigitList_polyTime.comp (hd.prod (hn1.prod hcs)))

private theorem radixDigits_one_val (n x : ℕ) (i : Fin n) :
    (radixDigits 1 n x i).val = (x.testBit i.val).toNat := by
  dsimp only [radixDigits]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i.val) with h | h <;> simp [h]

section
open Cslib.BitString

/-- For `d = 1`, `winternitzDigits 1 v w` on the little-endian integer value of `m` is `1` at
coordinate `k` if and only if `k ∈ optSet v w m` ([BonehShoup2023], Section 14.3.1, p. 593). -/
theorem winternitzDigits_one_eq_one_iff_mem_optSet {v w : ℕ} (m : BitString v)
    (k : Fin (v + w)) :
    winternitzDigits 1 v w (lsbValue (List.ofFn m)) k = 1 ↔ k ∈ optSet v w m := by
  have hm (i : Fin v) :
      (radixDigits 1 v (lsbValue (List.ofFn m)) i).val = (m i).toNat := by
    rw [radixDigits_one_val, testBit_lsbValue, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp only [List.length_ofFn, i.isLt]),
      List.getElem_ofFn, Option.getD_some]
  have hsum :
      (∑ i : Fin v, (1 - (radixDigits 1 v (lsbValue (List.ofFn m)) i).val)) =
        (List.ofFn m).count false := by
    have hadd :
        (∑ i : Fin v, (m i).toNat) + ∑ i : Fin v, (1 - (m i).toNat) = v := by
      simpa only [hm, Nat.one_mul] using sum_radixDigits_add_sum_sub 1 v (lsbValue (List.ofFn m))
    have hcount := List.count_true_add_count_false (List.ofFn m)
    rw [List.length_ofFn, count_true_ofFn, weight_eq_sum_toNat] at hcount
    simp only [hm]
    lia
  induction k using Fin.addCases with
  | left i =>
    rw [mem_optSet_castAdd, winternitzDigits, Fin.append_left, Fin.ext_iff, hm i]
    cases m i <;> decide
  | right j =>
    rw [mem_optSet_natAdd, winternitzDigits, Fin.append_right, Fin.ext_iff, hsum,
      radixDigits_one_val]
    cases ((List.ofFn m).count false).testBit j.val <;> decide

end

end Cslib.Crypto.OneTimeSignature
