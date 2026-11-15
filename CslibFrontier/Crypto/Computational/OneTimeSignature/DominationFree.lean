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
public import CslibFrontier.Init
public import Mathlib.Data.Fin.Tuple.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin

/-!
# Domination-free encodings and the Winternitz encoding

This module formalizes domination-free encodings and the Winternitz checksum encoding from
Boneh–Shoup, Section 14.3 (Definition 14.4, Section 14.3.1, and Lemma 14.5).

A function `P : M → Fin n → Fin (d + 1)` is *domination-free* (`DominationFree`) when no pair of
distinct messages `m ≠ m'` satisfies `P m ≤ P m'` coordinatewise. The Winternitz encoding
(`winternitzDigits d n0 n1 m`) decomposes `m < (d + 1) ^ n0` into `n0` base-`(d + 1)` message
digits `radixDigits d n0 m`, computes the complement checksum
`∑ i : Fin n0, (d - (radixDigits d n0 m i).val)`, and appends its `n1` base-`(d + 1)` digits.
When `d * n0 < (d + 1) ^ n1` and `f : M → ℕ` injects `M` into `{x | x < (d + 1) ^ n0}`, the
resulting encoding is domination-free (`winternitzDigits_dominationFree`).

We also provide an executable list form `winternitzDigitList` together with its length and entry
agreements (`winternitzDigitList_length`, `getElem_winternitzDigitList`) and a polynomial-time
certificate `winternitzDigitList_polyTime` in binary `d, m` and unary `n0, n1`.

## Main definitions

* `Cslib.Crypto.DominationFree`: domination-free encodings `M → Fin n → Fin (d + 1)`.
* `Cslib.Crypto.radixDigits`: little-endian base-`(d + 1)` digit vector of length `width`.
* `Cslib.Crypto.winternitzDigits`: Winternitz message-and-checksum digit vector of length
  `n0 + n1`.
* `Cslib.Crypto.radixDigitList`: executable list of base-`(d + 1)` digits.
* `Cslib.Crypto.winternitzDigitList`: executable list of Winternitz message-and-checksum digits.

## Main results

* `Cslib.Crypto.dominationFree_of_append_checksum`: structural append-checksum criterion for
  domination-freeness.
* `Cslib.Crypto.sum_radixDigits_mul_pow`: positional reconstruction of `x < (d + 1) ^ width`.
* `Cslib.Crypto.radixDigits_injOn`: injectivity of `radixDigits d width` below `(d + 1) ^ width`.
* `Cslib.Crypto.le_of_radixDigits_le`: coordinatewise digit comparison implies numeric comparison.
* `Cslib.Crypto.winternitzDigits_dominationFree`: Boneh–Shoup Lemma 14.5.
* `Cslib.Crypto.winternitzDigitList_polyTime`: polynomial-time computability of
  `winternitzDigitList`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.3 (Definition 14.4, Section 14.3.1, and Lemma 14.5).
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- A function `P : M → Fin n → Fin (d + 1)` is *domination-free* (Boneh–Shoup, Definition 14.4)
if no distinct messages `m ≠ m'` satisfy `P m ≤ P m'` coordinatewise. -/
@[expose] def DominationFree {M : Type*} {n d : ℕ} (P : M → Fin n → Fin (d + 1)) : Prop :=
  ∀ ⦃m m' : M⦄, m ≠ m' → ¬ P m ≤ P m'

/-- Structural append-checksum criterion: if `P0` is injective and any strict coordinatewise
increase `P0 m < P0 m'` prevents `P1 m ≤ P1 m'`, then `fun m => Fin.append (P0 m) (P1 m)` is
domination-free. -/
theorem dominationFree_of_append_checksum {M : Type*} {n0 n1 d : ℕ}
    {P0 : M → Fin n0 → Fin (d + 1)} {P1 : M → Fin n1 → Fin (d + 1)}
    (h0 : Function.Injective P0)
    (h1 : ∀ ⦃m m' : M⦄, P0 m < P0 m' → ¬ P1 m ≤ P1 m') :
    DominationFree (fun m => Fin.append (P0 m) (P1 m)) := by
  intro m m' hne hle
  have hle0 : P0 m ≤ P0 m' := fun i => by
    simpa [Fin.append_left] using hle (Fin.castAdd n1 i)
  have hle1 : P1 m ≤ P1 m' := fun j => by
    simpa [Fin.append_right] using hle (Fin.natAdd n0 j)
  have hne0 : P0 m ≠ P0 m' := fun h => hne (h0 h)
  exact h1 (lt_of_le_of_ne hle0 hne0) hle1

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

/-- The Winternitz digit vector of length `n0 + n1` for `m`: `n0` base-`(d + 1)` message digits
followed by `n1` base-`(d + 1)` digits of the complement checksum
`∑ i : Fin n0, (d - (radixDigits d n0 m i).val)`. -/
@[expose] def winternitzDigits (d n0 n1 m : ℕ) : Fin (n0 + n1) → Fin (d + 1) :=
  let m0 := radixDigits d n0 m
  let checksum := ∑ i : Fin n0, (d - (m0 i).val)
  Fin.append m0 (radixDigits d n1 checksum)

/-- Boneh–Shoup Lemma 14.5: if `f : M → ℕ` is injective with `f m < (d + 1) ^ n0` for every `m`,
and `d * n0 < (d + 1) ^ n1`, then `fun m => winternitzDigits d n0 n1 (f m)` is domination-free. -/
theorem winternitzDigits_dominationFree {M : Type*} {d n0 n1 : ℕ}
    {f : M → ℕ} (hf_inj : Function.Injective f)
    (hf_bound : ∀ m, f m < (d + 1) ^ n0) (hn1 : d * n0 < (d + 1) ^ n1) :
    DominationFree (fun m => winternitzDigits d n0 n1 (f m)) := by
  let P0 : M → Fin n0 → Fin (d + 1) := fun m => radixDigits d n0 (f m)
  let cs : M → ℕ := fun m => ∑ i : Fin n0, (d - (P0 m i).val)
  let P1 : M → Fin n1 → Fin (d + 1) := fun m => radixDigits d n1 (cs m)
  have h0 : Function.Injective P0 := fun m m' h =>
    hf_inj (radixDigits_injOn d n0 (hf_bound m) (hf_bound m') h)
  have hcs_lt : ∀ m, cs m < (d + 1) ^ n1 := fun m => by
    have hle : cs m ≤ n0 * d := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin n0))
          (fun i => d - (P0 m i).val) d (fun i _ => Nat.sub_le d _)
    lia
  have h1 : ∀ ⦃m m' : M⦄, P0 m < P0 m' → ¬ P1 m ≤ P1 m' := by
    intro m m' hlt hle1
    rw [Pi.lt_def] at hlt
    obtain ⟨hle0, j, hj_lt⟩ := hlt
    have hcomp_le : ∀ i : Fin n0, d - (P0 m' i).val ≤ d - (P0 m i).val :=
      fun i => Nat.sub_le_sub_left (hle0 i) d
    have hjm' : (P0 m' j).val ≤ d := Nat.lt_succ_iff.mp (P0 m' j).isLt
    have hcomp_lt : d - (P0 m' j).val < d - (P0 m j).val := by
      have hjv : (P0 m j).val < (P0 m' j).val := hj_lt
      lia
    have hcs_strict : cs m' < cs m :=
      Finset.sum_lt_sum (fun i _ => hcomp_le i) ⟨j, Finset.mem_univ j, hcomp_lt⟩
    have hcs_le : cs m ≤ cs m' := le_of_radixDigits_le (hcs_lt m) (hcs_lt m') hle1
    lia
  simpa [winternitzDigits, P0, cs, P1] using dominationFree_of_append_checksum h0 h1

/-- Executable list of `width` little-endian base-`(d + 1)` digits of `x`. -/
def radixDigitList (d width x : ℕ) : List ℕ :=
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
  rw [sum_radixDigitList_eq]
  have hsum :
      ∑ i : Fin n0, (d - (radixDigits d n0 m i).val) +
        ∑ i : Fin n0, (radixDigits d n0 m i).val = d * n0 := by
    rw [← Finset.sum_add_distrib]
    have hpt : ∀ i : Fin n0,
        d - (radixDigits d n0 m i).val + (radixDigits d n0 m i).val = d := fun i =>
      Nat.sub_add_cancel (Nat.lt_succ_iff.mp (radixDigits d n0 m i).isLt)
    simp [hpt, Nat.mul_comm]
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

private theorem radixDigitList_polyTime :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => radixDigitList p.1 p.2.1 p.2.2)
      (encPair encNat (encPair encUnary encNat)) (encList encNat) := by
  let encIn := encPair encNat (encPair encUnary encNat)
  have hd : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => p.1) encIn encNat :=
    ComputableTidilyInPolyTime.fst encNat (encPair encUnary encNat)
  have hwidth : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => p.2.1) encIn encUnary :=
    (ComputableTidilyInPolyTime.fst encUnary encNat).comp
      (ComputableTidilyInPolyTime.snd encNat (encPair encUnary encNat))
  have hx : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => p.2.2) encIn encNat :=
    (ComputableTidilyInPolyTime.snd encUnary encNat).comp
      (ComputableTidilyInPolyTime.snd encNat (encPair encUnary encNat))
  have hrange : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => List.range p.2.1)
      encIn (encList encUnary) :=
    ComputableTidilyInPolyTime.range.comp hwidth
  refine ComputableTidilyInPolyTime.mapWithInput hrange ?_
  have hd1 : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ × ℕ) × ℕ => q.1.1 + 1) (encPair encIn encUnary) encNat :=
    ComputableTidilyInPolyTime.binary_add'
      (hd.comp (ComputableTidilyInPolyTime.fst encIn encUnary))
      (ComputableTidilyInPolyTime.const 1)
  have hi : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ × ℕ) × ℕ => q.2) (encPair encIn encUnary) encUnary :=
    ComputableTidilyInPolyTime.snd encIn encUnary
  have hpow : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ × ℕ) × ℕ => (q.1.1 + 1) ^ q.2) (encPair encIn encUnary) encNat :=
    ComputableTidilyInPolyTime.binary_pow' hd1 hi
  have hxq : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ × ℕ) × ℕ => q.1.2.2) (encPair encIn encUnary) encNat :=
    hx.comp (ComputableTidilyInPolyTime.fst encIn encUnary)
  have hdiv : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ × ℕ) × ℕ => q.1.2.2 / (q.1.1 + 1) ^ q.2)
      (encPair encIn encUnary) encNat :=
    ComputableTidilyInPolyTime.binary_div.comp (hxq.prod hpow)
  exact ComputableTidilyInPolyTime.binary_mod.comp (hdiv.prod hd1)

/-- `winternitzDigitList` is computable in polynomial time when `d` and `m` are encoded in
binary (`encNat`) and the digit counts `n0` and `n1` are encoded in unary (`encUnary`). -/
theorem winternitzDigitList_polyTime :
    ComputableInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ => winternitzDigitList p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encNat (encPair encUnary (encPair encUnary encNat))) (encList encNat) := by
  refine ComputableInPolyTime.of_tidy ?_
  let encIn := encPair encNat (encPair encUnary (encPair encUnary encNat))
  have hd : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => p.1) encIn encNat :=
    ComputableTidilyInPolyTime.fst encNat (encPair encUnary (encPair encUnary encNat))
  have hn0 : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => p.2.1) encIn encUnary :=
    (ComputableTidilyInPolyTime.fst encUnary (encPair encUnary encNat)).comp
      (ComputableTidilyInPolyTime.snd encNat (encPair encUnary (encPair encUnary encNat)))
  have hn1 : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.1) encIn encUnary :=
    (ComputableTidilyInPolyTime.fst encUnary encNat).comp
      ((ComputableTidilyInPolyTime.snd encUnary (encPair encUnary encNat)).comp
        (ComputableTidilyInPolyTime.snd encNat (encPair encUnary (encPair encUnary encNat))))
  have hm : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.2) encIn encNat :=
    (ComputableTidilyInPolyTime.snd encUnary encNat).comp
      ((ComputableTidilyInPolyTime.snd encUnary (encPair encUnary encNat)).comp
        (ComputableTidilyInPolyTime.snd encNat (encPair encUnary (encPair encUnary encNat))))
  have hm0 : ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ => radixDigitList p.1 p.2.1 p.2.2.2) encIn (encList encNat) :=
    radixDigitList_polyTime.comp (hd.prod (hn0.prod hm))
  have hsum : ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ => (radixDigitList p.1 p.2.1 p.2.2.2).sum) encIn encNat :=
    ComputableInPolyTime.binary_sum.tidy.comp hm0
  have hdn0 : ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ => p.1 * p.2.1) encIn encNat :=
    ComputableTidilyInPolyTime.binary_mul'
      hd (ComputableTidilyInPolyTime.unary_to_binary.comp hn0)
  have hcs : ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ => p.1 * p.2.1 - (radixDigitList p.1 p.2.1 p.2.2.2).sum)
      encIn encNat :=
    ComputableTidilyInPolyTime.binary_sub' hdn0 hsum
  have hm1 : ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ =>
        radixDigitList p.1 p.2.2.1 (p.1 * p.2.1 - (radixDigitList p.1 p.2.1 p.2.2.2).sum))
      encIn (encList encNat) :=
    radixDigitList_polyTime.comp (hd.prod (hn1.prod hcs))
  exact ComputableTidilyInPolyTime.listAppend' hm0 hm1

end Cslib.Crypto
