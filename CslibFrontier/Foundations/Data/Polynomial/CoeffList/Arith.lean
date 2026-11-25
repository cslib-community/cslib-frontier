/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.List.GetD

/-!
# Computable polynomial arithmetic on little-endian coefficient lists

This file equips little-endian coefficient lists (`List R`, constant coefficient first) with
canonical trailing-zero trimming (`Polynomial.CoeffList.trim`) and computable polynomial operations
(`add`, `neg`, `sub`, `smul`, `shift`, `mul`, `deriv`) over semirings and rings with decidable
equality. Every operation returns a trimmed list (`Polynomial.CoeffList.IsTrimmed`) and commutes
with `Polynomial.ofCoeffList` (`ofCoeffList_add`, `ofCoeffList_sub`, `ofCoeffList_smul`,
`ofCoeffList_shift`, `ofCoeffList_mul`, `ofCoeffList_deriv`).

Because trimmed coefficient lists have no trailing zero, two trimmed lists represent the same
polynomial under `Polynomial.ofCoeffList` if and only if they are equal
(`Polynomial.CoeffList.IsTrimmed.eq_of_ofCoeffList_eq`).

## Main definitions

* `Polynomial.CoeffList.IsTrimmed`: predicate asserting that a coefficient list has no trailing `0`.
* `Polynomial.CoeffList.trim`: strip trailing zeros from a coefficient list.
* `Polynomial.CoeffList.add`, `Polynomial.CoeffList.neg`, `Polynomial.CoeffList.sub`: trimmed
  addition, negation, and subtraction of coefficient lists.
* `Polynomial.CoeffList.smul`, `Polynomial.CoeffList.shift`: trimmed scalar multiplication and
  monomial shift (`X ^ k * ·`).
* `Polynomial.CoeffList.mul`: trimmed Cauchy-product multiplication of coefficient lists.
* `Polynomial.CoeffList.deriv`: trimmed formal derivative of a coefficient list.

## Main results

* `Polynomial.CoeffList.ofCoeffList_trim`, `Polynomial.CoeffList.trim_eq_nil_iff`: trimming
  preserves `ofCoeffList`, and `trim p = []` characterizes the zero polynomial.
* `Polynomial.CoeffList.IsTrimmed.natDegree_ofCoeffList`,
  `Polynomial.CoeffList.IsTrimmed.leadingCoeff_ofCoeffList`,
  `Polynomial.CoeffList.IsTrimmed.eq_of_ofCoeffList_eq`: exact degree, leading coefficient, and
  canonicity of trimmed coefficient lists.
* `Polynomial.CoeffList.ofCoeffList_add`, `Polynomial.CoeffList.ofCoeffList_neg`,
  `Polynomial.CoeffList.ofCoeffList_sub`, `Polynomial.CoeffList.ofCoeffList_smul`,
  `Polynomial.CoeffList.ofCoeffList_shift`, `Polynomial.CoeffList.ofCoeffList_mul`,
  `Polynomial.CoeffList.ofCoeffList_deriv`: homomorphisms to `R[X]`.
-/

public section

namespace Polynomial.CoeffList

open Polynomial

/-! ### Trailing-zero trimming and canonical lists -/

section Zero

variable {R : Type*} [Zero R]

/-- Predicate asserting that a little-endian coefficient list has no trailing `0`. -/
def IsTrimmed (p : List R) : Prop :=
  p.getLast? ≠ some 0

/-- The empty coefficient list is trimmed. -/
theorem isTrimmed_nil : IsTrimmed ([] : List R) := by
  simp [IsTrimmed]

/-- Appending a nonzero leading coefficient produces a trimmed list. -/
theorem isTrimmed_append_singleton (l : List R) {a : R} (ha : a ≠ 0) :
    IsTrimmed (l ++ [a]) := by
  simp [IsTrimmed, ha]

/-- Every nonempty trimmed list decomposes as `l ++ [a]` with `a ≠ 0`. -/
theorem IsTrimmed.exists_append_singleton {p : List R} (hp : IsTrimmed p) (hne : p ≠ []) :
    ∃ l a, a ≠ 0 ∧ p = l ++ [a] := by
  obtain ⟨l, a, rfl⟩ := (List.eq_nil_or_concat p).resolve_left hne
  exact ⟨l, a, fun ha => hp (by simp [ha]), by simp⟩

/-- Mapping along a zero-reflecting function preserves `IsTrimmed`. -/
theorem IsTrimmed.map {S : Type*} [Zero S] {p : List R} (hp : IsTrimmed p) (f : R → S)
    (hf : ∀ a, f a = 0 → a = 0) : IsTrimmed (p.map f) := by
  rcases eq_or_ne p [] with rfl | hne
  · exact isTrimmed_nil
  · obtain ⟨l, a, ha, rfl⟩ := hp.exists_append_singleton hne
    rw [List.map_append, List.map_singleton]
    exact isTrimmed_append_singleton _ fun hfa => ha (hf a hfa)

section DecidableEq

variable [DecidableEq R]

/-- Strip trailing `0` entries from a little-endian coefficient list. -/
@[expose] def trim : List R → List R
  | [] => []
  | a :: p =>
    let t := trim p
    if a = 0 ∧ t.isEmpty then [] else a :: t

/-- Trimming the empty list yields `[]`. -/
@[simp] theorem trim_nil : trim ([] : List R) = [] := rfl

/-- Unfolding step for `trim` on `a :: p`. -/
theorem trim_cons (a : R) (p : List R) :
    trim (a :: p) = if a = 0 ∧ (trim p).isEmpty then [] else a :: trim p := rfl

/-- Every output of `trim` is trimmed. -/
theorem isTrimmed_trim (p : List R) : IsTrimmed (trim p) := by
  induction p with
  | nil => exact isTrimmed_nil
  | cons a p ih =>
    rw [trim_cons]
    split_ifs with h
    · exact isTrimmed_nil
    · rcases eq_or_ne (trim p) [] with hnil | hne
      · simpa [IsTrimmed, hnil] using fun ha => h ⟨ha, List.isEmpty_iff.mpr hnil⟩
      · rwa [IsTrimmed, List.getLast?_cons_of_ne_nil hne]

/-- A list ending in a nonzero element is unchanged by `trim`. -/
theorem trim_append_singleton (l : List R) {a : R} (ha : a ≠ 0) :
    trim (l ++ [a]) = l ++ [a] := by
  induction l with
  | nil => simp [trim_cons, ha]
  | cons b l ih => simp [trim_cons, ih]

/-- Appending a trailing zero does not change `trim`. -/
@[simp] theorem trim_append_zero (l : List R) : trim (l ++ [0]) = trim l := by
  induction l with
  | nil => simp [trim_cons]
  | cons b l ih => simp [trim_cons, ih]

/-- `trim p = p` if and only if `p` is already trimmed. -/
@[simp] theorem trim_eq_self_iff {p : List R} : trim p = p ↔ IsTrimmed p := by
  refine ⟨fun h => h ▸ isTrimmed_trim p, fun hp => ?_⟩
  rcases eq_or_ne p [] with rfl | hne
  · rfl
  · obtain ⟨l, a, ha, rfl⟩ := hp.exists_append_singleton hne
    exact trim_append_singleton l ha

alias ⟨_, IsTrimmed.trim_eq⟩ := trim_eq_self_iff

/-- `trim` is idempotent. -/
@[simp] theorem trim_trim (p : List R) : trim (trim p) = trim p :=
  (isTrimmed_trim p).trim_eq

/-- `trim p` is a sublist of `p`. -/
theorem trim_sublist (p : List R) : (trim p).Sublist p := by
  induction p with
  | nil => exact List.Sublist.slnil
  | cons a p ih =>
    rw [trim_cons]
    split_ifs
    · exact List.nil_sublist _
    · exact ih.cons_cons a

/-- Trimming never increases list length. -/
theorem length_trim_le (p : List R) : (trim p).length ≤ p.length :=
  (trim_sublist p).length_le

/-- `trim` commutes with any map that preserves and reflects `0`. -/
theorem trim_map {S : Type*} [Zero S] [DecidableEq S] (f : R → S)
    (hf : ∀ a, f a = 0 ↔ a = 0) (p : List R) :
    trim (p.map f) = (trim p).map f := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons, trim_cons, ih, List.isEmpty_map, hf]
    split_ifs <;> simp

end DecidableEq

end Zero

/-! ### Degree, leading coefficient, and uniqueness of trimmed lists -/

section SemiringTrim

variable {R : Type*} [Semiring R]

private theorem coeff_last_of_ne_nil {p : List R} (hne : p ≠ []) :
    (ofCoeffList p).coeff (p.length - 1) = p.getLastD 0 := by
  have hlt : p.length - 1 < p.length := Nat.sub_lt (List.length_pos_of_ne_nil hne) zero_lt_one
  rw [coeff_ofCoeffList, List.getD_eq_getElem _ _ hlt, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlt, Option.getD_some]

/-- For a nonempty trimmed list `p`, coefficient `p.length - 1` of `ofCoeffList p` is nonzero. -/
theorem IsTrimmed.coeff_last_ne_zero {p : List R} (hp : IsTrimmed p) (hne : p ≠ []) :
    (ofCoeffList p).coeff (p.length - 1) ≠ 0 := by
  obtain ⟨l, a, ha, rfl⟩ := hp.exists_append_singleton hne
  rwa [coeff_last_of_ne_nil hne, List.getLastD_concat]

/-- Every nonempty trimmed list represents a nonzero polynomial. -/
theorem IsTrimmed.ofCoeffList_ne_zero {p : List R} (hp : IsTrimmed p) (hne : p ≠ []) :
    ofCoeffList p ≠ 0 := fun h0 =>
  hp.coeff_last_ne_zero hne (by rw [h0, coeff_zero])

/-- A trimmed list is empty if and only if its polynomial is `0`. -/
theorem IsTrimmed.eq_nil_iff {p : List R} (hp : IsTrimmed p) :
    p = [] ↔ ofCoeffList p = 0 :=
  ⟨by rintro rfl; exact ofCoeffList_nil,
    fun h0 => by_contra fun hne => hp.ofCoeffList_ne_zero hne h0⟩

/-- A nonempty trimmed list `p` has `natDegree (ofCoeffList p) = p.length - 1`. -/
theorem IsTrimmed.natDegree_ofCoeffList {p : List R} (hp : IsTrimmed p) (hne : p ≠ []) :
    (ofCoeffList p).natDegree = p.length - 1 :=
  le_antisymm (natDegree_ofCoeffList_le p) (le_natDegree_of_ne_zero (hp.coeff_last_ne_zero hne))

/-- The leading coefficient of `ofCoeffList p` for trimmed `p` is `p.getLastD 0`. -/
theorem IsTrimmed.leadingCoeff_ofCoeffList {p : List R} (hp : IsTrimmed p) :
    (ofCoeffList p).leadingCoeff = p.getLastD 0 := by
  rcases eq_or_ne p [] with rfl | hne
  · simp
  · rw [Polynomial.leadingCoeff, hp.natDegree_ofCoeffList hne, coeff_last_of_ne_nil hne]

/-- Shorter trimmed lists have strictly smaller polynomial `degree` than nonempty trimmed `q`. -/
theorem IsTrimmed.degree_lt_of_length_lt {p q : List R} (hp : IsTrimmed p) (hq : IsTrimmed q)
    (hq0 : q ≠ []) (hlt : p.length < q.length) :
    (ofCoeffList p).degree < (ofCoeffList q).degree := by
  rcases eq_or_ne p [] with rfl | hp0
  · rw [ofCoeffList_nil, degree_zero, degree_eq_natDegree (hq.ofCoeffList_ne_zero hq0)]
    exact WithBot.bot_lt_coe _
  · have hplen := List.length_pos_of_ne_nil hp0
    have hqlen := List.length_pos_of_ne_nil hq0
    rw [degree_eq_natDegree (hp.ofCoeffList_ne_zero hp0),
      degree_eq_natDegree (hq.ofCoeffList_ne_zero hq0), Nat.cast_lt,
      hp.natDegree_ofCoeffList hp0, hq.natDegree_ofCoeffList hq0]
    omega

/-- Two trimmed lists representing the same polynomial are equal. -/
theorem IsTrimmed.eq_of_ofCoeffList_eq {p q : List R} (hp : IsTrimmed p) (hq : IsTrimmed q)
    (h : ofCoeffList p = ofCoeffList q) : p = q := by
  rcases eq_or_ne p [] with rfl | hp0
  · exact (hq.eq_nil_iff.mpr (h.symm.trans ofCoeffList_nil)).symm
  · have hq0 : q ≠ [] := fun hnil => hp.ofCoeffList_ne_zero hp0 (by simp [h, hnil])
    have hdeg := (hp.natDegree_ofCoeffList hp0).symm.trans
      ((congrArg natDegree h).trans (hq.natDegree_ofCoeffList hq0))
    have hplen := List.length_pos_of_ne_nil hp0
    have hqlen := List.length_pos_of_ne_nil hq0
    refine List.ext_getElem (by omega) fun i hi hi' => ?_
    simpa only [coeff_ofCoeffList, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi']
      using congrArg (fun P => P.coeff i) h

section DecidableEq

variable [DecidableEq R]

/-- Trimming trailing zeros preserves `ofCoeffList`. -/
@[simp] theorem ofCoeffList_trim (p : List R) : ofCoeffList (trim p) = ofCoeffList p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [trim_cons]
    split_ifs with h
    · rcases h with ⟨rfl, hemp⟩
      rw [ofCoeffList_nil, ofCoeffList_zero_cons, ← ih, List.isEmpty_iff.mp hemp,
        ofCoeffList_nil, mul_zero]
    · rw [ofCoeffList_cons, ofCoeffList_cons, ih]

/-- `trim p = []` if and only if `ofCoeffList p = 0`. -/
@[simp] theorem trim_eq_nil_iff (p : List R) : trim p = [] ↔ ofCoeffList p = 0 := by
  rw [(isTrimmed_trim p).eq_nil_iff, ofCoeffList_trim]

/-- Coefficient lists with equal `ofCoeffList` have the same `trim`. -/
theorem trim_eq_of_ofCoeffList_eq {p q : List R} (h : ofCoeffList p = ofCoeffList q) :
    trim p = trim q :=
  (isTrimmed_trim p).eq_of_ofCoeffList_eq (isTrimmed_trim q) (by simp [h])

/-- For `ofCoeffList p ≠ 0`, `(trim p).length = (ofCoeffList p).natDegree + 1`. -/
theorem length_trim_eq_natDegree_add_one {p : List R} (hp : ofCoeffList p ≠ 0) :
    (trim p).length = (ofCoeffList p).natDegree + 1 := by
  have hne : trim p ≠ [] := mt (trim_eq_nil_iff p).mp hp
  have hpos := List.length_pos_of_ne_nil hne
  have hdeg := (isTrimmed_trim p).natDegree_ofCoeffList hne
  rw [ofCoeffList_trim] at hdeg; omega

/-- Vanishing of coefficients at and above `n` bounds `(trim p).length ≤ n`. -/
theorem length_trim_le_of_coeff_eq_zero {p : List R} {n : ℕ}
    (h : ∀ k ≥ n, (ofCoeffList p).coeff k = 0) : (trim p).length ≤ n := by
  rcases eq_or_ne (trim p) [] with hnil | hne
  · simp [hnil]
  · refine not_lt.mp fun hlt => (isTrimmed_trim p).coeff_last_ne_zero hne ?_
    rw [ofCoeffList_trim]
    exact h _ (Nat.le_sub_one_of_lt hlt)

end DecidableEq

end SemiringTrim

/-! ### Semiring operations: `add`, `smul`, `shift`, `mul`, `deriv` -/

private theorem length_zipWithAll {α β γ : Type*} (f : Option α → Option β → γ)
    (p : List α) (q : List β) : (List.zipWithAll f p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp
  | cons a p ih => cases q <;> simp [ih, Nat.succ_max_succ]

private theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

section Semiring

variable {R : Type*} [Semiring R] [DecidableEq R]

/-- Addition of coefficient lists, returning a trimmed list. -/
@[expose] def add (p q : List R) : List R :=
  trim (List.zipWithAll (fun a b => a.getD 0 + b.getD 0) p q)

/-- `add p q` is trimmed. -/
theorem isTrimmed_add (p q : List R) : IsTrimmed (add p q) :=
  isTrimmed_trim _

/-- `trim` is the identity on `add p q`. -/
@[simp] theorem trim_add (p q : List R) : trim (add p q) = add p q :=
  (isTrimmed_add p q).trim_eq

/-- Length bound on `add p q`. -/
theorem length_add_le (p q : List R) : (add p q).length ≤ max p.length q.length :=
  (length_trim_le _).trans_eq (length_zipWithAll _ p q)

/-- `add` represents polynomial addition under `ofCoeffList`. -/
@[simp] theorem ofCoeffList_add (p q : List R) :
    ofCoeffList (add p q) = ofCoeffList p + ofCoeffList q := by
  rw [add, ofCoeffList_trim, ofCoeffList_zipWithAll_add]

/-- Left scalar multiplication of a coefficient list by `c : R`, trimmed. -/
@[expose] def smul (c : R) (p : List R) : List R :=
  trim (p.map (c * ·))

/-- `smul c p` is trimmed. -/
theorem isTrimmed_smul (c : R) (p : List R) : IsTrimmed (smul c p) :=
  isTrimmed_trim _

/-- `trim` is the identity on `smul c p`. -/
@[simp] theorem trim_smul (c : R) (p : List R) : trim (smul c p) = smul c p :=
  (isTrimmed_smul c p).trim_eq

/-- Length bound on `smul c p`. -/
theorem length_smul_le (c : R) (p : List R) : (smul c p).length ≤ p.length :=
  (length_trim_le _).trans (by simp)

/-- `smul` represents multiplication by `C c` under `ofCoeffList`. -/
@[simp] theorem ofCoeffList_smul (c : R) (p : List R) :
    ofCoeffList (smul c p) = C c * ofCoeffList p := by
  rw [smul, ofCoeffList_trim, ofCoeffList_map_mul]

/-- Monomial shift `X ^ k * ·` by prepending `k` low-degree zeros and trimming. -/
@[expose] def shift (k : ℕ) (p : List R) : List R :=
  trim (List.replicate k 0 ++ p)

/-- `shift k p` is trimmed. -/
theorem isTrimmed_shift (k : ℕ) (p : List R) : IsTrimmed (shift k p) :=
  isTrimmed_trim _

/-- `trim` is the identity on `shift k p`. -/
@[simp] theorem trim_shift (k : ℕ) (p : List R) : trim (shift k p) = shift k p :=
  (isTrimmed_shift k p).trim_eq

/-- Length bound on `shift k p`. -/
theorem length_shift_le (k : ℕ) (p : List R) : (shift k p).length ≤ k + p.length :=
  (length_trim_le _).trans (by simp)

/-- `shift k p` represents `X ^ k * ofCoeffList p`. -/
@[simp] theorem ofCoeffList_shift (k : ℕ) (p : List R) :
    ofCoeffList (shift k p) = X ^ k * ofCoeffList p := by
  rw [shift, ofCoeffList_trim, ofCoeffList_append, ofCoeffList_replicate_zero,
    List.length_replicate, zero_add]

/-- Multiplication of coefficient lists via the Cauchy product, returning a trimmed list. -/
@[expose] def mul (p q : List R) : List R :=
  if p.isEmpty || q.isEmpty then []
  else
    trim ((List.range (p.length + q.length - 1)).map fun k =>
      ((List.range (k + 1)).map fun i => p.getD i 0 * q.getD (k - i) 0).sum)

/-- `mul p q` is trimmed. -/
theorem isTrimmed_mul (p q : List R) : IsTrimmed (mul p q) := by
  unfold mul
  split_ifs
  exacts [isTrimmed_nil, isTrimmed_trim _]

/-- `trim` is the identity on `mul p q`. -/
@[simp] theorem trim_mul (p q : List R) : trim (mul p q) = mul p q :=
  (isTrimmed_mul p q).trim_eq

/-- Length bound on `mul p q`. -/
theorem length_mul_le (p q : List R) : (mul p q).length ≤ p.length + q.length - 1 := by
  unfold mul
  split_ifs
  · simp
  · exact (length_trim_le _).trans (by simp)

/-- `mul` represents polynomial multiplication under `ofCoeffList`. -/
@[simp] theorem ofCoeffList_mul (p q : List R) :
    ofCoeffList (mul p q) = ofCoeffList p * ofCoeffList q := by
  unfold mul
  split_ifs with h
  · rcases (by simpa [List.isEmpty_iff] using h : p = [] ∨ q = []) with rfl | rfl <;> simp
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, List.isEmpty_eq_false_iff] at h
    have hp_pos := List.length_pos_of_ne_nil h.1
    have hq_pos := List.length_pos_of_ne_nil h.2
    rw [ofCoeffList_trim]
    ext k
    rw [coeff_ofCoeffList, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (ofCoeffList p).coeff i * (ofCoeffList q).coeff j)]
    simp_rw [coeff_ofCoeffList]
    by_cases hk : k < p.length + q.length - 1
    · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range,
        sum_map_range]
    · rw [List.getD_eq_default _ _ (by simp only [List.length_map, List.length_range]; omega)]
      refine (Finset.sum_eq_zero fun i hi => ?_).symm
      by_cases hip : i < p.length
      · rw [List.getD_eq_default q _ (by rw [Finset.mem_range] at hi; omega), mul_zero]
      · rw [List.getD_eq_default p _ (by omega), zero_mul]

/-- Formal derivative of a coefficient list, returning a trimmed list. -/
@[expose] def deriv (p : List R) : List R :=
  trim ((List.range (p.length - 1)).map fun i => p.getD (i + 1) 0 * (i + 1 : R))

/-- `deriv p` is trimmed. -/
theorem isTrimmed_deriv (p : List R) : IsTrimmed (deriv p) :=
  isTrimmed_trim _

/-- `trim` is the identity on `deriv p`. -/
@[simp] theorem trim_deriv (p : List R) : trim (deriv p) = deriv p :=
  (isTrimmed_deriv p).trim_eq

/-- Length bound on `deriv p`. -/
theorem length_deriv_le (p : List R) : (deriv p).length ≤ p.length - 1 :=
  (length_trim_le _).trans (by simp)

/-- `deriv` represents the formal polynomial derivative under `ofCoeffList`. -/
@[simp] theorem ofCoeffList_deriv (p : List R) :
    ofCoeffList (deriv p) = derivative (ofCoeffList p) := by
  rw [deriv, ofCoeffList_trim]
  ext i
  rw [coeff_ofCoeffList, coeff_derivative, coeff_ofCoeffList]
  by_cases hi : i < p.length - 1
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  · rw [List.getD_eq_default _ _ (by simp only [List.length_map, List.length_range]; omega),
      List.getD_eq_default p _ (by omega), zero_mul]

end Semiring

/-! ### Ring operations: `neg`, `sub` -/

section Ring

variable {R : Type*} [Ring R] [DecidableEq R]

/-- Negation of a coefficient list, returning a trimmed list. -/
@[expose] def neg (p : List R) : List R :=
  trim (p.map (-·))

/-- `neg p` is trimmed. -/
theorem isTrimmed_neg (p : List R) : IsTrimmed (neg p) :=
  isTrimmed_trim _

/-- `trim` is the identity on `neg p`. -/
@[simp] theorem trim_neg (p : List R) : trim (neg p) = neg p :=
  (isTrimmed_neg p).trim_eq

/-- Length bound on `neg p`. -/
theorem length_neg_le (p : List R) : (neg p).length ≤ p.length :=
  (length_trim_le _).trans (by simp)

/-- `neg` represents polynomial negation under `ofCoeffList`. -/
@[simp] theorem ofCoeffList_neg (p : List R) :
    ofCoeffList (neg p) = -ofCoeffList p := by
  rw [neg, ofCoeffList_trim, ofCoeffList_map_neg]

/-- Subtraction of coefficient lists, returning a trimmed list. -/
@[expose] def sub (p q : List R) : List R :=
  trim (List.zipWithAll (fun a b => a.getD 0 - b.getD 0) p q)

/-- `sub p q` is trimmed. -/
theorem isTrimmed_sub (p q : List R) : IsTrimmed (sub p q) :=
  isTrimmed_trim _

/-- `trim` is the identity on `sub p q`. -/
@[simp] theorem trim_sub (p q : List R) : trim (sub p q) = sub p q :=
  (isTrimmed_sub p q).trim_eq

/-- Length bound on `sub p q`. -/
theorem length_sub_le (p q : List R) : (sub p q).length ≤ max p.length q.length :=
  (length_trim_le _).trans_eq (length_zipWithAll _ p q)

/-- `sub` represents polynomial subtraction under `ofCoeffList`. -/
@[simp] theorem ofCoeffList_sub (p q : List R) :
    ofCoeffList (sub p q) = ofCoeffList p - ofCoeffList q := by
  rw [sub, ofCoeffList_trim, ofCoeffList_zipWithAll_sub]

end Ring

end Polynomial.CoeffList
