/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Foundations.Data.BitString.Combination
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Foundations.Data.BitString.Support
import CslibFrontier.Computability.GenericRAM.Native.SubsetPairFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Foundations.Data.BitString.Weight
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Bool.Count

/-!
# Containment-free encodings

This module formalizes containment-free subset encodings used for one-time signatures
([BonehShoup2023], Sections 14.2 and 14.4). No cryptographic primitives or security experiments
are defined here.

A map `P : M → Finset α` is containment free (`ContainmentFree P`) when no image `P m` is a
subset of another image `P m'` for distinct `m ≠ m'` (Definition 14.3). Equivalently, `P` is
injective and its range is an antichain under `⊆` (`containmentFree_iff`). Any injective map into
constant-size subsets is containment free (`containmentFree_of_injective_of_card_eq`). By the
finite-cardinality form of Sperner's theorem (`card_le_choose_half_of_containmentFree`, proved from
Mathlib's `IsAntichain.sperner`, underlying the `n_min ≈ v + (log₂ v) / 2` estimate in Section
14.2.1, which is not formalized here), `Fintype.card M ≤ Nat.choose n (n / 2)` where
`n = Fintype.card α`; conversely, any finite message space satisfying that bound admits a
containment-free encoding via `unrankCombination` (`exists_containmentFree_of_card_le`, existence
only with no polynomial-time claim; not stated in the book).

Two explicit computable encodings are provided:

* `optWord` / `optSet` (`P_opt`, Section 14.2.1, Lemma 14.3): appends the `w`-bit little-endian
  (`lowBits`, LSB-first) checksum `(List.ofFn m).count false` (`v - weight m`) to `m` and takes
  its support in `Fin (v + w)`. Unlike Figure 14.2 (p. 589), which prints the checksum MSB-first
  (`5` as `0101`), `optWord` appends checksum bits LSB-first. Whenever `v < 2 ^ w` (for example
  `w = 1 + Nat.clog 2 v`), `optSet v w` is containment free (`optSet_containmentFree`) and
  `optWord` is computable in polynomial time in `w` (unary) and `m` (`optWord_polyTime`).
* `horsWord` / `horsSet` (Section 14.4): maps a `v`-bit message via its big-endian binary value
  into `unrankCombination n ℓ`. Whenever `2 ^ v ≤ n.choose ℓ`, `horsSet n ℓ` produces `ℓ`-element
  subsets (`card_horsSet`), is containment free (`horsSet_containmentFree`), and `horsWord` is
  computable in polynomial time in `(n, ℓ)` (unary) and `m` (`horsWord_polyTime`). This uses the
  library's `unrankCombination` (ordered with `false` first via `Nat.choose m k`), satisfying the
  §14.4 requirement of an efficient injective map into fixed-size subsets; the specific unranking
  loop of Exercise 14.3 is not formalized here.

## Main definitions

* `Cslib.Crypto.OneTimeSignature.ContainmentFree`: containment-free property for subset maps.
* `Cslib.Crypto.OneTimeSignature.optWord`, `Cslib.Crypto.OneTimeSignature.optSet`: the `P_opt`
  word and subset encodings.
* `Cslib.Crypto.OneTimeSignature.horsWord`, `Cslib.Crypto.OneTimeSignature.horsSet`: fixed-size
  subset encodings via `unrankCombination`.

## Main results

* `Cslib.Crypto.OneTimeSignature.containmentFree_iff`: characterization via injectivity and
  `⊆`-antichains.
* `Cslib.Crypto.OneTimeSignature.containmentFree_of_injective_of_card_eq`: constant-cardinality
  criterion.
* `Cslib.Crypto.OneTimeSignature.card_le_choose_half_of_containmentFree`: Sperner's upper bound.
* `Cslib.Crypto.OneTimeSignature.exists_containmentFree_of_card_le`: Sperner converse.
* `Cslib.Crypto.OneTimeSignature.optSet_containmentFree`: Lemma 14.3 for `v < 2 ^ w`.
* `Cslib.Crypto.OneTimeSignature.optWord_polyTime`: polynomial-time certificate for `optWord`.
* `Cslib.Crypto.OneTimeSignature.card_horsSet`: constant output cardinality `ℓ` under
  `2 ^ v ≤ n.choose ℓ`.
* `Cslib.Crypto.OneTimeSignature.horsSet_containmentFree`: containment freeness when
  `2 ^ v ≤ n.choose ℓ`.
* `Cslib.Crypto.OneTimeSignature.horsWord_polyTime`: polynomial-time certificate for `horsWord`.

## References

* [BonehShoup2023]: Dan Boneh and Victor Shoup, *A Graduate Course in Applied Cryptography*
  (v0.6), Section 14.2 (Definition 14.3, p. 587), Section 14.2.1 (Sperner's theorem, p. 588;
  `P_opt` and Lemma 14.3, pp. 588–589), and Section 14.4 (p. 593).
-/

public section

namespace Cslib.Crypto.OneTimeSignature

open Cslib.BitString
open Turing.MultiTapeTM

/-- Definition 14.3 ([BonehShoup2023], Section 14.2, p. 587): a map `P : M → Finset α` is
containment free if no image is a subset of the image of a distinct message. -/
@[expose] def ContainmentFree {M α : Type*} (P : M → Finset α) : Prop :=
  ∀ ⦃m m' : M⦄, m ≠ m' → ¬ P m ⊆ P m'

/-- A subset encoding is containment free if and only if it is injective and its range is an
antichain under subset inclusion. -/
theorem containmentFree_iff {M α : Type*} (P : M → Finset α) :
    ContainmentFree P ↔ Function.Injective P ∧ IsAntichain (· ⊆ ·) (Set.range P) :=
  ⟨fun h => ⟨fun _ _ heq => by_contra fun hne => h hne heq.le,
      by rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩ hne; exact h fun hm => hne (congrArg P hm)⟩,
    fun ⟨hinj, hant⟩ _ _ hne => hant ⟨_, rfl⟩ ⟨_, rfl⟩ fun hP => hne (hinj hP)⟩

/-- Any injective map into subsets of a common cardinality `ℓ` is containment free. -/
theorem containmentFree_of_injective_of_card_eq {M α : Type*} {P : M → Finset α} {ℓ : ℕ}
    (hinj : Function.Injective P) (hcard : ∀ m, (P m).card = ℓ) : ContainmentFree P :=
  fun _ _ hne hsub => hne (hinj (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard])))

/-- Finite-cardinality form of Sperner's theorem, proved from Mathlib's `IsAntichain.sperner`:
any containment-free family into `Finset α` has message space cardinality at most
`(Fintype.card α).choose (Fintype.card α / 2)`. ([BonehShoup2023], Section 14.2.1, p. 588, invokes
Sperner's theorem only for the `n_min ≈ v + (log₂ v) / 2` estimate, which is not formalized
here.) -/
theorem card_le_choose_half_of_containmentFree {M α : Type*} [Fintype M] [Fintype α]
    {P : M → Finset α} (hP : ContainmentFree P) :
    Fintype.card M ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  classical
  obtain ⟨hinj, hant⟩ := (containmentFree_iff P).1 hP
  have hant_img : IsAntichain (· ⊆ ·)
      ((Finset.univ.image P : Finset (Finset α)) : Set (Finset α)) :=
    hant.subset fun _ hs => let ⟨m, _, hm⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs); ⟨m, hm⟩
  simpa [Finset.card_image_of_injective _ hinj] using hant_img.sperner

/-- The word construction underlying `P_opt` ([BonehShoup2023], Section 14.2.1, pp. 588–589):
appends the `w`-bit little-endian (`lowBits`, LSB-first) binary encoding of `m.count false`
(`v - weight m` on `v`-bit messages) to `m`. Unlike Figure 14.2 (p. 589), which prints the
checksum MSB-first, checksum bits are appended LSB-first here. -/
def optWord (w : ℕ) (m : List Bool) : List Bool :=
  m ++ lowBits w (m.count false)

/-- The set-valued `P_opt` encoding on `v`-bit strings with `w`-bit checksum. -/
def optSet (v w : ℕ) (m : BitString v) : Finset (Fin (v + w)) :=
  supportOfList (v + w) (optWord w (List.ofFn m))

/-- Membership in the message coordinates of `optSet v w m`. -/
theorem mem_optSet_castAdd {v w : ℕ} (m : BitString v) (i : Fin v) :
    Fin.castAdd w i ∈ optSet v w m ↔ m i = true := by
  rw [optSet, mem_supportOfList]
  simp [optWord, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (i.isLt.trans_eq List.length_ofFn.symm)]

/-- Membership in the checksum coordinates of `optSet v w m`. -/
theorem mem_optSet_natAdd {v w : ℕ} (m : BitString v) (j : Fin w) :
    Fin.natAdd v j ∈ optSet v w m ↔ ((List.ofFn m).count false).testBit j.val = true := by
  rw [optSet, mem_supportOfList]
  simp only [Fin.val_natAdd, optWord, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), List.length_ofFn, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by simp [length_lowBits])]
  simp [lowBits_eq_ofFn]

/-- Lemma 14.3 ([BonehShoup2023], Section 14.2.1, pp. 588–589): `P_opt` is containment free
whenever `v < 2 ^ w` (in particular for the book's choice `w = 1 + Nat.clog 2 v`). -/
theorem optSet_containmentFree {v w : ℕ} (hv : v < 2 ^ w) :
    ContainmentFree (optSet v w) := by
  intro m m' hne hsub
  have hcoord (i : Fin v) (hi : m i = true) : m' i = true :=
    (mem_optSet_castAdd m' i).1 (hsub ((mem_optSet_castAdd m i).2 hi))
  obtain ⟨i0, hm0, hm'0⟩ : ∃ i0 : Fin v, m i0 = false ∧ m' i0 = true := by
    by_contra hnone
    refine hne (funext fun i => ?_)
    have := not_exists.1 hnone i
    have := hcoord i
    cases hm : m i <;> cases hm' : m' i <;> simp_all
  have hweight : weight m < weight m' := Finset.card_lt_card <|
    (Finset.ssubset_iff_of_subset fun i hi =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hcoord i (Finset.mem_filter.1 hi).2⟩).2
      ⟨i0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hm'0⟩, by simp [hm0]⟩
  have hsum := List.count_true_add_count_false (List.ofFn m)
  have hsum' := List.count_true_add_count_false (List.ofFn m')
  simp only [List.length_ofFn, count_true_ofFn] at hsum hsum'
  have hc_lt : (List.ofFn m).count false < 2 ^ w :=
    lt_of_le_of_lt (by simpa [List.length_ofFn] using (List.ofFn m).count_le_length) hv
  have hle : (List.ofFn m).count false ≤ (List.ofFn m').count false :=
    Nat.le_of_testBit fun j hj => by
      have hjw : j < w := by_contra fun hge => Bool.false_ne_true <|
        (Nat.testBit_lt_two_pow
          (hc_lt.trans_le (Nat.pow_le_pow_right two_pos (not_lt.mp hge)))).symm.trans hj
      exact (mem_optSet_natAdd m' ⟨j, hjw⟩).1 (hsub ((mem_optSet_natAdd m ⟨j, hjw⟩).2 hj))
  omega

/-- Efficiency certificate for `P_opt`: computing `optWord w m` runs in polynomial time in
`w` (unary) and `m` (bitstring). -/
theorem optWord_polyTime :
    ComputableInPolyTime (fun p : ℕ × List Bool => optWord p.1 p.2)
      (encPair encUnary encBits) encBits :=
  .bitsAppend (.snd encUnary encBits) (.bitsLow (.fst encUnary encBits)
    (ComputableInPolyTime.unary_to_binary.comp
      (.bitsCountWithInput (.snd encUnary encBits) (.const false))))

/-- A fixed-size subset word encoding ([BonehShoup2023], Section 14.4, p. 593): maps a bitstring
message via its big-endian binary value into `unrankCombination n ℓ`. This uses the library's
unranking order (`false` before `true`) rather than the loop of Exercise 14.3. -/
@[expose] def horsWord (n ℓ : ℕ) (m : List Bool) : List Bool :=
  unrankCombination n ℓ (binaryValue m)

/-- The subset encoding on `v`-bit strings derived from `horsWord`; its image has constant
cardinality `ℓ` (`card_horsSet`) and is containment free (`horsSet_containmentFree`) whenever
`2 ^ v ≤ n.choose ℓ`. -/
@[expose] def horsSet (n ℓ : ℕ) {v : ℕ} (m : BitString v) : Finset (Fin n) :=
  supportOfList n (horsWord n ℓ (List.ofFn m))

private theorem containmentFree_supportOfList_unrankCombination {M : Type*} {n ℓ : ℕ}
    {f : M → ℕ} (hf_inj : Function.Injective f) (hf_lt : ∀ m, f m < n.choose ℓ) :
    ContainmentFree (fun m => supportOfList n (unrankCombination n ℓ (f m))) :=
  containmentFree_of_injective_of_card_eq (ℓ := ℓ)
    (fun m m' heq => hf_inj (unrankCombination_injective (hf_lt m) (hf_lt m')
      (supportOfList_injective_of_length (length_unrankCombination n ℓ _)
        (length_unrankCombination n ℓ _) heq)))
    fun m => by rw [card_supportOfList_of_length (length_unrankCombination n ℓ _),
      count_true_unrankCombination (hf_lt m)]

private theorem binaryValue_ofFn_lt_choose {n ℓ v : ℕ}
    (hbound : 2 ^ v ≤ n.choose ℓ) (m : BitString v) :
    binaryValue (List.ofFn m) < n.choose ℓ :=
  lt_of_lt_of_le (by simpa [List.length_ofFn] using binaryValue_lt_two_pow (List.ofFn m)) hbound

/-- Under `2 ^ v ≤ n.choose ℓ`, `horsSet n ℓ` produces subsets of cardinality `ℓ`
([BonehShoup2023], Section 14.4, p. 593). -/
theorem card_horsSet {n ℓ v : ℕ} (hbound : 2 ^ v ≤ n.choose ℓ) (m : BitString v) :
    (horsSet n ℓ m).card = ℓ := by
  rw [horsSet, horsWord, card_supportOfList_of_length (length_unrankCombination _ _ _)]
  exact count_true_unrankCombination (binaryValue_ofFn_lt_choose hbound m)

/-- Any bitstring message space with `2 ^ v ≤ n.choose ℓ` admits a containment-free encoding
into `ℓ`-element subsets of `Fin n` via `horsSet` ([BonehShoup2023], Section 14.4, p. 593). -/
theorem horsSet_containmentFree {n ℓ v : ℕ} (hbound : 2 ^ v ≤ n.choose ℓ) :
    ContainmentFree (horsSet n ℓ (v := v)) := by
  have hf_inj : Function.Injective (fun m : BitString v => binaryValue (List.ofFn m)) :=
    fun _ _ h => List.ofFn_injective (binaryValue_injective_of_length_eq (by simp) h)
  exact containmentFree_supportOfList_unrankCombination hf_inj (binaryValue_ofFn_lt_choose hbound)

/-- Efficiency certificate for `horsWord`: computing `horsWord n ℓ m` runs in polynomial time
in `(n, ℓ)` (unary) and `m` (bitstring). -/
theorem horsWord_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × List Bool => horsWord p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encBits) encBits :=
  Cslib.GenericRAM.SubsetPairFold.unrankCombination_polyTime.comp
    ((ComputableInPolyTime.fst (encPair encUnary encUnary) encBits).prod
      (ComputableInPolyTime.bitsBinaryValue.comp
        (.snd (encPair encUnary encUnary) encBits)))

/-- Converse to the finite-cardinality form of Sperner's theorem (not stated in
[BonehShoup2023]): any finite message space with cardinality at most `n.choose (n / 2)` admits a
containment-free encoding into `Finset (Fin n)`. This is a pure existence result and makes no
polynomial-time claim. -/
theorem exists_containmentFree_of_card_le {M : Type*} [Fintype M] {n : ℕ}
    (hM : Fintype.card M ≤ n.choose (n / 2)) :
    ∃ P : M → Finset (Fin n), ContainmentFree P :=
  ⟨_, containmentFree_supportOfList_unrankCombination (f := fun m => (Fintype.equivFin M m).val)
    (fun _ _ h => (Fintype.equivFin M).injective (Fin.ext h))
    fun m => (Fintype.equivFin M m).isLt.trans_le hM⟩

end Cslib.Crypto.OneTimeSignature
