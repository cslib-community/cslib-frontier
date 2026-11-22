/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RootBound
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.Sturm
public import CslibFrontier.Foundations.Data.Polynomial.CoeffList
public import Mathlib.Data.List.SignVariations
public import Mathlib.Data.Nat.Log

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.Cast.Order

/-!
# Computable Rational Polynomial Arithmetic and Sturm Evaluation

This module provides computable coefficient-list operations on `ℚ[X]` (trimming, arithmetic,
formal derivative, Euclidean division, Sturm sequences, rational sign-variation counting, Cauchy
root bounds, integer denominator clearing, and Mignotte bisection-depth computation) and proves
their exact algebraic correspondence with Mathlib's `Polynomial` and `Polynomial.sturmVariations`
over `ℝ`.

## Main definitions

* `Cslib.RealRoot.IsTrimmed`: predicate asserting that a coefficient list has no trailing zero.
* `Cslib.RealRoot.trim`, `Cslib.RealRoot.addList`, `Cslib.RealRoot.negList`,
  `Cslib.RealRoot.subList`, `Cslib.RealRoot.scaleList`, `Cslib.RealRoot.shiftZero`,
  `Cslib.RealRoot.derivList`, `Cslib.RealRoot.divModList`, `Cslib.RealRoot.negModList`:
  computable dense-list operations representing polynomials in `ℚ[X]`.
* `Cslib.RealRoot.sturmSeqList`, `Cslib.RealRoot.sturmVariationsList`: computable Sturm sequence
  and rational sign-variation evaluation over `ℚ`.
* `Cslib.RealRoot.cauchyBoundNat`, `Cslib.RealRoot.lcmDens`, `Cslib.RealRoot.clearDenomsList`,
  `Cslib.RealRoot.sqNormList`, `Cslib.RealRoot.mignotteSepSqInv`,
  `Cslib.RealRoot.mignotteBisectionDepth`: computable Cauchy root bound, integer clearing,
  Mignotte separation denominator, and bisection-depth bound.

## Main results

* `Cslib.RealRoot.ofCoeffList_negModList` and `Cslib.RealRoot.sturmSeqList_map_ofCoeffList`:
  exact correspondence between list operations and `Polynomial.mod` / `Polynomial.sturmSeq`.
* `Cslib.RealRoot.sturmVariationsList_eq_sturmVariations`:
  `sturmVariationsList (sturmSeqList cs) x` equals
  `sturmVariations ((ofCoeffList cs).map (algebraMap ℚ ℝ)) x`.
* `Cslib.RealRoot.abs_lt_cauchyBoundNat_of_isRoot`, `Cslib.RealRoot.dyadic_width_lt_root_sep`,
  and `Cslib.RealRoot.mignotteBisectionDepth_le`: verified Cauchy root enclosure, Mignotte
  bisection separation guarantee, and logarithmic depth bound.

## References

* [BasuPollackRoy2006] (locator unverified)
* [Mahler1964] (originator of the Mahler-measure root-separation inequality; locator unverified)
* [Mignotte1982] (locator unverified)
-/

public section

namespace Cslib.RealRoot

open Polynomial

/-- Predicate asserting that a coefficient list has no trailing zero. -/
def IsTrimmed {R : Type*} [Zero R] (l : List R) : Prop :=
  l.getLast? ≠ some 0

/-- The empty coefficient list `[]` is trimmed. -/
theorem isTrimmed_nil {R : Type*} [Zero R] : IsTrimmed ([] : List R) := by
  simp only [IsTrimmed, List.getLast?_nil, ne_eq, reduceCtorEq, not_false_eq_true]

/-- Remove trailing zero coefficients from a rational coefficient list. -/
@[expose] def trim : List ℚ → List ℚ
  | [] => []
  | a :: as =>
    let t := trim as
    if t.isEmpty then (if a = 0 then [] else [a]) else a :: t

/-- `trim as` has length at most `as.length`. -/
theorem trim_length_le (as : List ℚ) : (trim as).length ≤ as.length := by
  induction as with
  | nil => simp only [trim, List.length_nil, le_refl]
  | cons a as ih =>
    simp only [trim]
    split_ifs <;> simp only [List.length_nil, List.length_cons] <;> omega

/-- Trimming trailing zeros preserves the polynomial denoted by `ofCoeffList`. -/
theorem ofCoeffList_trim (as : List ℚ) : ofCoeffList (trim as) = ofCoeffList as := by
  fun_induction trim as with
  | case1 => rfl
  | case2 as t he ih | case3 a as t he ha ih =>
    change (trim as).isEmpty = true at he
    have h0 : ofCoeffList as = 0 := by rw [← ih, List.isEmpty_iff.mp he, ofCoeffList_nil]
    simp only [ofCoeffList_cons, ofCoeffList_nil, h0, mul_zero, add_zero, C_0]
  | case4 a as t he ih => simp only [ofCoeffList_cons, t, ih]

/-- Every output of `trim` is trimmed (`IsTrimmed`). -/
theorem isTrimmed_trim (as : List ℚ) : IsTrimmed (trim as) := by
  fun_induction trim as with
  | case1 | case2 => exact isTrimmed_nil
  | case3 a _ _ _ ha _ =>
    simp only [IsTrimmed, List.getLast?_singleton, ne_eq, Option.some.injEq]
    exact ha
  | case4 a as t he ih =>
    have hne : trim as ≠ [] := fun h => he (by simp only [t, h, List.isEmpty_nil])
    rcases h : trim as with _ | ⟨b, bs⟩
    · exact absurd h hne
    · simpa only [IsTrimmed, List.getLast?_cons, Option.getD_some, t, h] using ih

private theorem trim_ne_nil_of_ne_zero {cs : List ℚ} (h : ofCoeffList cs ≠ 0) : trim cs ≠ [] :=
  fun hnil => h (by rw [← ofCoeffList_trim cs, hnil, ofCoeffList_nil])

/-- Any nonempty trimmed list has a nonzero last element. -/
theorem IsTrimmed.getLast?_ne_zero {l : List ℚ} (ht : IsTrimmed l) (hl : l ≠ []) :
    ∃ x, l.getLast? = some x ∧ x ≠ 0 := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp fun h => hl (List.getLast?_eq_none_iff.mp h)
  exact ⟨x, hx, fun hx0 => ht (hx0 ▸ hx)⟩

private theorem coeff_last_of_getLast?_eq {l : List ℚ} {x : ℚ} (hx : l.getLast? = some x) :
    (ofCoeffList l).coeff (l.length - 1) = x := by
  have hl : l ≠ [] := fun h => by simp only [h, List.getLast?_nil, reduceCtorEq] at hx
  have hlt : l.length - 1 < l.length := Nat.sub_lt (List.length_pos_of_ne_nil hl) zero_lt_one
  rw [coeff_ofCoeffList, List.getD_eq_getElem _ _ hlt]
  exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans
    (List.getLast?_eq_getElem?.symm.trans hx))

/-- Leading-position coefficient `(ofCoeffList l).coeff (l.length - 1)` is nonzero for nonempty
trimmed `l`. -/
theorem IsTrimmed.coeff_last_ne_zero {l : List ℚ} (ht : IsTrimmed l) (hl : l ≠ []) :
    (ofCoeffList l).coeff (l.length - 1) ≠ 0 := by
  obtain ⟨x, hx, hx0⟩ := ht.getLast?_ne_zero hl
  rwa [coeff_last_of_getLast?_eq hx]

/-- A nonempty trimmed list represents a nonzero polynomial. -/
theorem IsTrimmed.ofCoeffList_ne_zero {l : List ℚ} (ht : IsTrimmed l) (hl : l ≠ []) :
    ofCoeffList l ≠ 0 :=
  fun h0 => ht.coeff_last_ne_zero hl (by rw [h0, coeff_zero])

/-- A trimmed list is empty if and only if its polynomial is `0`. -/
theorem IsTrimmed.eq_nil_iff {l : List ℚ} (ht : IsTrimmed l) :
    l = [] ↔ ofCoeffList l = 0 :=
  ⟨fun h => h ▸ ofCoeffList_nil, fun h0 => by_contra fun hne => ht.ofCoeffList_ne_zero hne h0⟩

/-- For nonempty trimmed `l`, `(ofCoeffList l).natDegree + 1 = l.length`. -/
theorem IsTrimmed.natDegree_add_one {l : List ℚ} (ht : IsTrimmed l) (hl : l ≠ []) :
    (ofCoeffList l).natDegree + 1 = l.length := by
  have := natDegree_ofCoeffList_le l
  have := le_natDegree_of_ne_zero (ht.coeff_last_ne_zero hl)
  have := List.length_pos_of_ne_nil hl
  omega

private theorem natDegree_add_one_trim {cs : List ℚ} (h : ofCoeffList cs ≠ 0) :
    (ofCoeffList cs).natDegree + 1 = (trim cs).length := by
  rw [← ofCoeffList_trim cs]
  exact (isTrimmed_trim cs).natDegree_add_one (trim_ne_nil_of_ne_zero h)

/-- Shorter trimmed lists have strictly smaller polynomial degree than nonempty trimmed `v`. -/
theorem IsTrimmed.degree_lt_of_length_lt {u v : List ℚ} (hu : IsTrimmed u) (hv : IsTrimmed v)
    (hv0 : v ≠ []) (huv : u.length < v.length) :
    (ofCoeffList u).degree < (ofCoeffList v).degree := by
  by_cases hu0 : u = []
  · rw [hu0, ofCoeffList_nil, degree_zero]
    exact bot_lt_iff_ne_bot.mpr (Polynomial.degree_ne_bot.mpr (hv.ofCoeffList_ne_zero hv0))
  · exact Polynomial.degree_lt_degree (by
      have := hu.natDegree_add_one hu0; have := hv.natDegree_add_one hv0; omega)

/-- Coefficients of `ofCoeffList l` at indices `≥ l.length` are zero. -/
theorem coeff_ofCoeffList_eq_zero_of_le {R : Type*} [Semiring R] (l : List R) {i : ℕ}
    (hi : l.length ≤ i) : (ofCoeffList l).coeff i = 0 := by
  rw [coeff_ofCoeffList, List.getD_eq_default _ _ hi]

/-- Pointwise addition of rational coefficient lists. -/
@[expose] def addList : List ℚ → List ℚ → List ℚ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addList as bs

/-- Pointwise negation of a rational coefficient list. -/
@[expose] def negList : List ℚ → List ℚ := List.map Neg.neg

/-- Pointwise subtraction of rational coefficient lists. -/
@[expose] def subList (as bs : List ℚ) : List ℚ := addList as (negList bs)

/-- Scalar multiplication of a rational coefficient list. -/
@[expose] def scaleList (c : ℚ) : List ℚ → List ℚ := List.map (c * ·)

/-- Multiplication by `X ^ k` via prepending `k` zeros. -/
@[expose] def shiftZero (k : ℕ) (bs : List ℚ) : List ℚ := List.replicate k 0 ++ bs

/-- Auxiliary shifted-derivative pass over a coefficient list. -/
@[expose] def derivAux (k : ℕ) : List ℚ → List ℚ
  | [] => []
  | a :: as => ((k : ℚ) * a) :: derivAux (k + 1) as

/-- Computable formal derivative of a rational coefficient list, trimmed. -/
@[expose] def derivList : List ℚ → List ℚ
  | [] => []
  | _ :: as => trim (derivAux 1 as)

/-- Pointwise `addList` corresponds to polynomial addition under `ofCoeffList`. -/
theorem ofCoeffList_addList (as bs : List ℚ) :
    ofCoeffList (addList as bs) = ofCoeffList as + ofCoeffList bs := by
  fun_induction addList as bs with
  | case1 | case2 => simp
  | case3 a as b bs ih =>
    simp only [ofCoeffList_cons, ih, C_add, mul_add]
    ring

/-- Pointwise `subList` corresponds to polynomial subtraction under `ofCoeffList`. -/
theorem ofCoeffList_subList (as bs : List ℚ) :
    ofCoeffList (subList as bs) = ofCoeffList as - ofCoeffList bs := by
  rw [subList, ofCoeffList_addList, negList, ofCoeffList_map_neg, sub_eq_add_neg]

/-- Prepending `k` zeros via `shiftZero` multiplies `ofCoeffList bs` by `X ^ k`. -/
theorem ofCoeffList_shiftZero (k : ℕ) (bs : List ℚ) :
    ofCoeffList (shiftZero k bs) = X ^ k * ofCoeffList bs := by
  rw [shiftZero, ofCoeffList_append, ofCoeffList_replicate_zero, zero_add, List.length_replicate]

theorem derivAux_length (k : ℕ) (as : List ℚ) :
    (derivAux k as).length = as.length := by
  fun_induction derivAux k as <;> simp_all

private theorem coeff_ofCoeffList_derivAux (k : ℕ) (as : List ℚ) (i : ℕ) :
    (ofCoeffList (derivAux k as)).coeff i = ((k + i : ℕ) : ℚ) * (ofCoeffList as).coeff i := by
  induction as generalizing k i with
  | nil => simp only [derivAux, ofCoeffList_nil, coeff_zero, mul_zero]
  | cons _ _ ih =>
    cases i with
    | zero => simp only [derivAux, ofCoeffList_cons, coeff_add, coeff_C_zero, coeff_X_mul_zero,
        add_zero]
    | succ i =>
      simp only [derivAux, ofCoeffList_cons, coeff_add, coeff_C_succ, zero_add, coeff_X_mul,
        ih (k + 1) i, Nat.add_assoc, Nat.add_comm 1 i]

/-- `derivList as` represents `derivative (ofCoeffList as)`. -/
theorem ofCoeffList_derivList (as : List ℚ) :
    ofCoeffList (derivList as) = derivative (ofCoeffList as) := by
  cases as with
  | nil => simp only [derivList, ofCoeffList_nil, derivative_zero]
  | cons _ as =>
    rw [derivList, ofCoeffList_trim]; ext i
    rw [coeff_ofCoeffList_derivAux 1 as i, ofCoeffList_cons, coeff_derivative,
      coeff_add, coeff_C_succ, zero_add, coeff_X_mul, mul_comm, Nat.add_comm 1 i,
      Nat.cast_add, Nat.cast_one]

/-- Every output of `derivList` is trimmed (`IsTrimmed`). -/
theorem isTrimmed_derivList (as : List ℚ) : IsTrimmed (derivList as) := by
  cases as with
  | nil => exact isTrimmed_nil
  | cons _ as => exact isTrimmed_trim _

/-- `derivList as` has length at most `as.length - 1`. -/
theorem derivList_length_le (as : List ℚ) : (derivList as).length ≤ as.length - 1 := by
  cases as with
  | nil => simp only [derivList, List.length_nil, Nat.zero_sub, le_refl]
  | cons _ as =>
    simp only [derivList, List.length_cons, Nat.add_sub_cancel]
    exact (trim_length_le _).trans (derivAux_length 1 as).le

/-- Fuel-bounded polynomial Euclidean division on trimmed lists (`u` by nonempty `v`). -/
@[expose] def divModAux : ℕ → List ℚ → List ℚ → List ℚ × List ℚ
  | 0, u, _ => ([], trim u)
  | n + 1, u, v =>
    let u' := trim u
    if u'.length < v.length then
      ([], u')
    else
      match v.getLast?, u'.getLast? with
      | some lc, some lu =>
        let shift := u'.length - v.length
        let factor := lu / lc
        let subtrahend := scaleList factor (shiftZero shift v)
        let uNext := trim (subList u' subtrahend)
        let res := divModAux n uNext v
        (addList res.1 (shiftZero shift [factor]), res.2)
      | _, _ => ([], u')

/-- Computable Euclidean quotient and remainder on `List ℚ`. -/
@[expose] def divModList (u v : List ℚ) : List ℚ × List ℚ :=
  let u' := trim u
  let v' := trim v
  divModAux u'.length u' v'

/-- Computable negated remainder `-u % v` on `List ℚ`, trimmed. -/
@[expose] def negModList (u v : List ℚ) : List ℚ :=
  Prod.snd (divModList (negList u) v)

private theorem subList_step_length_lt {u' v : List ℚ} (_hu' : IsTrimmed u') (hv : IsTrimmed v)
    (hv0 : v ≠ []) (huv : v.length ≤ u'.length) {lc lu : ℚ}
    (hlc : v.getLast? = some lc) (hlu : u'.getLast? = some lu) :
    (trim (subList u' (scaleList (lu / lc) (shiftZero (u'.length - v.length) v)))).length <
      u'.length := by
  let shift := u'.length - v.length
  let uNext := trim (subList u' (scaleList (lu / lc) (shiftZero shift v)))
  have hu0 : u' ≠ [] :=
    List.ne_nil_of_length_pos (lt_of_lt_of_le (List.length_pos_of_ne_nil hv0) huv)
  have hlc0 : lc ≠ 0 := fun h0 => hv (h0 ▸ hlc)
  have hv1 : 1 ≤ v.length := List.length_pos_of_ne_nil hv0
  have hcoeff_zero : ∀ i, u'.length - 1 ≤ i → (ofCoeffList uNext).coeff i = 0 := by
    intro i hi
    simp only [uNext, ofCoeffList_trim, ofCoeffList_subList, coeff_sub, scaleList,
      ofCoeffList_map_mul, ofCoeffList_shiftZero, coeff_C_mul, coeff_X_pow_mul']
    rcases eq_or_lt_of_le hi with rfl | hLt
    · have hs : shift ≤ u'.length - 1 := by omega
      simp only [hs, ↓reduceIte, show u'.length - 1 - shift = v.length - 1 by omega,
        coeff_last_of_getLast?_eq hlu, coeff_last_of_getLast?_eq hlc, div_mul_cancel₀ lu hlc0,
        sub_self]
    · have hi_ge : u'.length ≤ i := by have := List.length_pos_of_ne_nil hu0; omega
      rw [coeff_ofCoeffList_eq_zero_of_le u' hi_ge]
      split_ifs with hs
      · rw [coeff_ofCoeffList_eq_zero_of_le v (by omega), mul_zero, sub_self]
      · rw [mul_zero, sub_self]
  change uNext.length < u'.length
  by_cases hun : uNext = []
  · rw [hun, List.length_nil]; exact List.length_pos_of_ne_nil hu0
  · have hlt : uNext.length - 1 < u'.length - 1 := by
      by_contra hge
      exact (isTrimmed_trim _).coeff_last_ne_zero hun (hcoeff_zero _ (Nat.le_of_not_lt hge))
    have := List.length_pos_of_ne_nil hun
    omega

private theorem divModAux_spec : ∀ (n : ℕ) (u v : List ℚ),
    IsTrimmed v → v ≠ [] → (trim u).length ≤ n →
    let res := divModAux n u v
    IsTrimmed res.2 ∧ res.2.length < v.length ∧
      ofCoeffList u = ofCoeffList res.1 * ofCoeffList v + ofCoeffList res.2
  | 0, u, v, _, hv0, hlen => by
    have hu' : trim u = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    simp only [divModAux, ofCoeffList_nil, zero_mul, zero_add]
    exact ⟨isTrimmed_trim u, hu' ▸ List.length_pos_of_ne_nil hv0, (ofCoeffList_trim u).symm⟩
  | n + 1, u, v, hv, hv0, hlen => by
    simp only [divModAux]
    by_cases hlt : (trim u).length < v.length
    · simp only [hlt, ↓reduceIte, ofCoeffList_nil, zero_mul, zero_add, true_and]
      exact ⟨isTrimmed_trim u, (ofCoeffList_trim u).symm⟩
    · have huv : v.length ≤ (trim u).length := Nat.le_of_not_lt hlt
      have hu0 : trim u ≠ [] :=
        List.ne_nil_of_length_pos (lt_of_lt_of_le (List.length_pos_of_ne_nil hv0) huv)
      obtain ⟨lc, hlc, _⟩ := hv.getLast?_ne_zero hv0
      obtain ⟨lu, hlu, _⟩ := (isTrimmed_trim u).getLast?_ne_zero hu0
      simp only [hlt, ↓reduceIte, hlc, hlu]
      let shift := (trim u).length - v.length
      let factor := lu / lc
      let uNext := trim (subList (trim u) (scaleList factor (shiftZero shift v)))
      have huNext_lt := subList_step_length_lt (isTrimmed_trim u) hv hv0 huv hlc hlu
      obtain ⟨htr, hrlen, heq⟩ :=
        divModAux_spec n uNext v hv hv0 ((trim_length_le uNext).trans (Nat.lt_succ_iff.mp
          (lt_of_lt_of_le huNext_lt hlen)))
      refine ⟨htr, hrlen, ?_⟩
      have huNext_eq : ofCoeffList uNext =
          ofCoeffList (trim u) - C factor * (X ^ shift * ofCoeffList v) := by
        simp only [uNext, ofCoeffList_trim, ofCoeffList_subList, scaleList, ofCoeffList_map_mul,
          ofCoeffList_shiftZero]
      rw [← ofCoeffList_trim u,
        show ofCoeffList (trim u) = C factor * (X ^ shift * ofCoeffList v) + ofCoeffList uNext by
          rw [huNext_eq]; ring,
        heq, ofCoeffList_addList, ofCoeffList_shiftZero, ofCoeffList_cons, ofCoeffList_nil,
        mul_zero, add_zero]
      ring

/-- Correctness of `divModList u v` when `ofCoeffList v ≠ 0`: trimmed remainder of strictly
shorter length satisfying `ofCoeffList u = ofCoeffList q * ofCoeffList v + ofCoeffList r`. -/
theorem divModList_spec {u v : List ℚ} (hv0 : ofCoeffList v ≠ 0) :
    let res := divModList u v
    IsTrimmed res.2 ∧ res.2.length < (trim v).length ∧
      ofCoeffList u = ofCoeffList res.1 * ofCoeffList v + ofCoeffList res.2 := by
  have hspec := divModAux_spec (trim u).length (trim u) (trim v) (isTrimmed_trim v)
    (trim_ne_nil_of_ne_zero hv0) (trim_length_le (trim u))
  simpa only [divModList, ofCoeffList_trim] using hspec

/-- `negModList u v` represents the negated Euclidean remainder `-(ofCoeffList u) % ofCoeffList v`
with a trimmed, shorter coefficient list. -/
theorem ofCoeffList_negModList {u v : List ℚ} (hv0 : ofCoeffList v ≠ 0) :
    IsTrimmed (negModList u v) ∧ (negModList u v).length < (trim v).length ∧
      ofCoeffList (negModList u v) = -(ofCoeffList u) % ofCoeffList v := by
  have ⟨htr, hrlen, heq⟩ := divModList_spec (u := negList u) hv0
  refine ⟨htr, hrlen, ?_⟩
  have hdeg_lt : (ofCoeffList (negModList u v)).degree < (ofCoeffList v).degree := by
    rw [← ofCoeffList_trim v]
    exact htr.degree_lt_of_length_lt (isTrimmed_trim v) (trim_ne_nil_of_ne_zero hv0) hrlen
  have hneg : -(ofCoeffList u) =
      ofCoeffList (divModList (negList u) v).1 * ofCoeffList v + ofCoeffList (negModList u v) :=
    (ofCoeffList_map_neg u).symm.trans heq
  rw [hneg, Polynomial.add_mod, EuclideanDomain.mod_eq_zero.mpr (dvd_mul_left _ _), zero_add,
    (Polynomial.mod_eq_self_iff hv0).mpr hdeg_lt]

/-- Fuel-bounded computable Sturm sequence on trimmed lists. -/
@[expose] def sturmSeqAux : ℕ → List ℚ → List ℚ → List (List ℚ)
  | 0, p, _ => [p]
  | n + 1, p, q =>
    if q.isEmpty then [p]
    else p :: sturmSeqAux n q (negModList p q)

/-- Computable Sturm sequence of a rational coefficient list `cs`. -/
@[expose] def sturmSeqList (cs : List ℚ) : List (List ℚ) :=
  let p := trim cs
  if p.isEmpty then []
  else
    let dp := derivList p
    sturmSeqAux dp.length p dp

private theorem sturmSeqAux_spec : ∀ (n : ℕ) (p q : List ℚ),
    IsTrimmed p → p ≠ [] → IsTrimmed q → q.length ≤ n →
    (sturmSeqAux n p q).map ofCoeffList = Polynomial.sturmSeq (ofCoeffList p) (ofCoeffList q) ∧
      (sturmSeqAux n p q).length ≤ n + 1 ∧
      ∀ f ∈ sturmSeqAux n p q, f.length ≤ max p.length q.length := by
  have base {k : ℕ} {p : List ℚ} (hp : IsTrimmed p) (hp0 : p ≠ []) :
      ([p] : List (List ℚ)).map ofCoeffList = Polynomial.sturmSeq (ofCoeffList p) (ofCoeffList []) ∧
        ([p] : List (List ℚ)).length ≤ k + 1 ∧
        ∀ f ∈ ([p] : List (List ℚ)), f.length ≤ max p.length 0 := by
    simp only [List.map_cons, List.map_nil, ofCoeffList_nil, Polynomial.sturmSeq_zero_right,
      ite_eq_right (fun h => absurd h (hp.ofCoeffList_ne_zero hp0)), List.length_singleton,
      List.mem_singleton, forall_eq, Nat.le_add_left, le_max_left, and_self]
  intro n
  induction n with
  | zero =>
    intro p q hp hp0 _ hqn
    obtain rfl : q = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hqn)
    exact base hp hp0
  | succ n ih =>
    intro p q hp hp0 hq hqn
    by_cases hqe : q.isEmpty = true
    · have hnil : q = [] := List.isEmpty_iff.mp hqe
      subst hnil
      simpa only [sturmSeqAux, hqe, ↓reduceIte, List.length_nil] using base hp hp0
    · have hq0 : q ≠ [] := fun hnil => hqe (List.isEmpty_iff.mpr hnil)
      obtain ⟨hr_trim, hr_len, hr_mod⟩ :=
        ofCoeffList_negModList (u := p) (hq.ofCoeffList_ne_zero hq0)
      have hr_len_q : (negModList p q).length < q.length :=
        lt_of_lt_of_le hr_len (trim_length_le q)
      obtain ⟨ih_map, ih_len, ih_mem⟩ := ih q (negModList p q) hq hq0 hr_trim (by omega)
      simp only [sturmSeqAux, hqe, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.length_cons,
        List.mem_cons]
      refine ⟨?_, by omega, ?_⟩
      · rw [Polynomial.sturmSeq_cons (hp.ofCoeffList_ne_zero hp0), ih_map, hr_mod]
      · rintro f (rfl | hf)
        · exact le_max_left _ _
        · exact (ih_mem f hf).trans
            (max_le (le_max_right _ _) (hr_len_q.le.trans (le_max_right _ _)))

/-- `sturmSeqList cs` represents
`Polynomial.sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs))` elementwise under
`ofCoeffList`. -/
theorem sturmSeqList_map_ofCoeffList (cs : List ℚ) :
    (sturmSeqList cs).map ofCoeffList =
      Polynomial.sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs)) := by
  simp only [sturmSeqList]
  by_cases he : (trim cs).isEmpty = true
  · have h0 : ofCoeffList cs = 0 := by
      rw [← ofCoeffList_trim cs, List.isEmpty_iff.mp he, ofCoeffList_nil]
    simp only [he, ↓reduceIte, List.map_nil, h0, derivative_zero, Polynomial.sturmSeq_zero_left]
  · have hspec := sturmSeqAux_spec (derivList (trim cs)).length (trim cs) (derivList (trim cs))
      (isTrimmed_trim cs) (fun h => he (List.isEmpty_iff.mpr h))
      (isTrimmed_derivList (trim cs)) le_rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte, hspec.1, ofCoeffList_derivList, ofCoeffList_trim]

/-- Length bound `(sturmSeqList cs).length ≤ (ofCoeffList cs).natDegree + 1`. -/
theorem sturmSeqList_length_le (cs : List ℚ) :
    (sturmSeqList cs).length ≤ (ofCoeffList cs).natDegree + 1 := by
  simp only [sturmSeqList]
  by_cases he : (trim cs).isEmpty = true
  · simp only [he, ↓reduceIte, List.length_nil, Nat.zero_le]
  · have hne : trim cs ≠ [] := fun h => he (List.isEmpty_iff.mpr h)
    have hspec := sturmSeqAux_spec (derivList (trim cs)).length (trim cs) (derivList (trim cs))
      (isTrimmed_trim cs) hne (isTrimmed_derivList (trim cs)) le_rfl
    have hdp_len := derivList_length_le (trim cs)
    have hdeg := (ofCoeffList_trim cs).symm ▸ (isTrimmed_trim cs).natDegree_add_one hne
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    omega

/-- Entry length bound: every list in `sturmSeqList cs` has length at most `(trim cs).length`. -/
theorem sturmSeqList_entry_length_le (cs : List ℚ) {f : List ℚ} (hf : f ∈ sturmSeqList cs) :
    f.length ≤ (trim cs).length := by
  simp only [sturmSeqList] at hf
  by_cases he : (trim cs).isEmpty = true
  · simp only [he, ↓reduceIte, List.not_mem_nil] at hf
  · have hne : trim cs ≠ [] := fun h => he (List.isEmpty_iff.mpr h)
    have hspec := sturmSeqAux_spec (derivList (trim cs)).length (trim cs) (derivList (trim cs))
      (isTrimmed_trim cs) hne (isTrimmed_derivList (trim cs)) le_rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte] at hf
    exact (hspec.2.2 f hf).trans
      (max_le le_rfl ((derivList_length_le (trim cs)).trans (Nat.sub_le _ _)))

/-- Rational Sturm sign variations of a precomputed Sturm sequence at `x : ℚ`. -/
@[expose] def sturmVariationsList (seq : List (List ℚ)) (x : ℚ) : ℕ :=
  (seq.map (evalCoeffList x)).signVariations

/-- `sturmVariationsList (sturmSeqList cs) x` equals the real Sturm sign-variation count
`Polynomial.sturmVariations ((ofCoeffList cs).map (algebraMap ℚ ℝ)) (x : ℝ)`. -/
theorem sturmVariationsList_eq_sturmVariations (cs : List ℚ) (x : ℚ) :
    sturmVariationsList (sturmSeqList cs) x =
      Polynomial.sturmVariations ((ofCoeffList cs).map (algebraMap ℚ ℝ)) (x : ℝ) := by
  rw [Polynomial.sturmVariations, Polynomial.derivative_map,
    Polynomial.sturmSeq_map (algebraMap ℚ ℝ), ← sturmSeqList_map_ofCoeffList cs, List.map_map,
    List.map_map]
  have hlist : ((sturmSeqList cs).map (evalCoeffList x)).map (algebraMap ℚ ℝ) =
      (sturmSeqList cs).map ((eval (x : ℝ) ∘ Polynomial.map (algebraMap ℚ ℝ)) ∘ ofCoeffList) := by
    rw [List.map_map]
    refine List.map_congr_left fun g _ => ?_
    change _ = eval ((algebraMap ℚ ℝ) x) ((ofCoeffList g).map (algebraMap ℚ ℝ))
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, eval_ofCoeffList]
    rfl
  rw [← hlist, sturmVariationsList]
  refine (List.signVariations_map (fun q => ?_) _).symm
  change SignType.sign (q : ℝ) = SignType.sign q
  rcases lt_trichotomy q 0 with hlt | rfl | hgt
  · rw [sign_neg hlt, sign_neg (Rat.cast_lt_zero.mpr hlt)]
  · simp only [Rat.cast_zero, sign_zero]
  · rw [sign_pos hgt, sign_pos (Rat.cast_pos.mpr hgt)]

/-- Maximum absolute value among a list of rational numbers (`0` on `[]`). -/
@[expose] def maxAbsList : List ℚ → ℚ
  | [] => 0
  | a :: as => max |a| (maxAbsList as)

/-- Nonnegativity of `maxAbsList l`. -/
theorem maxAbsList_nonneg (l : List ℚ) : 0 ≤ maxAbsList l := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact le_trans (abs_nonneg a) (le_max_left _ _)

/-- Every indexed entry `l.getD i 0` has absolute value at most `maxAbsList l`. -/
theorem abs_getD_le_maxAbsList (l : List ℚ) (i : ℕ) : |l.getD i 0| ≤ maxAbsList l := by
  induction l generalizing i with
  | nil => simp only [List.getD_nil, abs_zero, maxAbsList, le_refl]
  | cons a l ih =>
    cases i with
    | zero => simp only [List.getD_cons_zero, maxAbsList, le_max_left]
    | succ i => simp only [List.getD_cons_succ, maxAbsList]; exact (ih i).trans (le_max_right _ _)

/-- Computable positive integer upper bound strictly greater than the absolute value of every
real root of `ofCoeffList cs`. -/
@[expose] def cauchyBoundNat (cs : List ℚ) : ℕ :=
  let t := trim cs
  if t.length ≤ 1 then 1
  else
    let lc := Option.getD t.getLast? 1
    let m := maxAbsList t.dropLast
    let b := m / |lc| + 1
    Int.natAbs b.num / b.den + 1

/-- `cauchyBoundNat cs` is always at least `1`. -/
theorem one_le_cauchyBoundNat (cs : List ℚ) : 1 ≤ cauchyBoundNat cs := by
  simp only [cauchyBoundNat]
  split_ifs
  · exact le_rfl
  · exact Nat.le_add_left 1 _

private theorem getD_dropLast_of_lt {α : Type*} (l : List α) (d : α) {i : ℕ}
    (hi : i < l.length - 1) : l.dropLast.getD i d = l.getD i d := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_dropLast]; exact hi),
    List.getD_eq_getElem _ _ (Nat.lt_of_lt_of_le hi (Nat.sub_le _ _)), List.getElem_dropLast]

/-- Every real root `r` of `(ofCoeffList cs).map (algebraMap ℚ ℝ)` (when nonzero) satisfies
`|r| < cauchyBoundNat cs`. -/
theorem abs_lt_cauchyBoundNat_of_isRoot {cs : List ℚ} (hcs : ofCoeffList cs ≠ 0) {r : ℝ}
    (hr : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r) :
    |r| < (cauchyBoundNat cs : ℝ) := by
  let t := trim cs
  have ht : IsTrimmed t := isTrimmed_trim cs
  have ht0 : ofCoeffList t ≠ 0 := (ofCoeffList_trim cs).symm ▸ hcs
  have htnil := trim_ne_nil_of_ne_zero hcs
  have hdeg : (ofCoeffList t).natDegree + 1 = t.length := ht.natDegree_add_one htnil
  have hr' : ((ofCoeffList t).map (algebraMap ℚ ℝ)).IsRoot r := (ofCoeffList_trim cs).symm ▸ hr
  dsimp only [cauchyBoundNat]
  split_ifs with hlen
  · change t.length ≤ 1 at hlen
    have hc := eq_C_of_natDegree_eq_zero (by omega : (ofCoeffList t).natDegree = 0)
    rw [hc, Polynomial.map_C, IsRoot.def, eval_C, eq_ratCast] at hr'
    have h0 := Rat.cast_injective (α := ℝ) (hr'.trans Rat.cast_zero.symm)
    exact absurd (by rw [hc, h0, C_0]) ht0
  · obtain ⟨lc, hlc, _⟩ := ht.getLast?_ne_zero htnil
    have hlead : (ofCoeffList t).leadingCoeff = lc := by
      rw [leadingCoeff, (by omega : (ofCoeffList t).natDegree = t.length - 1),
        coeff_last_of_getLast?_eq hlc]
    have hcb := abs_lt_cauchyBound_of_forall_coeff_le ht0 (maxAbsList_nonneg _)
      (fun i hi => by
        rw [coeff_ofCoeffList, ← getD_dropLast_of_lt t 0 (by omega)]
        exact abs_getD_le_maxAbsList t.dropLast i) hr'
    rw [hlead] at hcb
    let b := maxAbsList t.dropLast / |lc| + 1
    have hb_nonneg : 0 ≤ b :=
      add_nonneg (div_nonneg (maxAbsList_nonneg _) (abs_nonneg _)) zero_le_one
    have hrat_lt : b < ((Int.natAbs b.num / b.den + 1 : ℕ) : ℚ) := by
      have hnum_eq : (Int.natAbs b.num : ℚ) / (b.den : ℚ) = |b| := by
        rw [← Int.cast_natCast, ← Int.abs_eq_natAbs, Int.cast_abs,
          ← abs_of_pos (by positivity : (0 : ℚ) < b.den), ← abs_div, Rat.num_div_den]
      conv_lhs => rw [← abs_of_nonneg hb_nonneg, ← hnum_eq]
      rw [div_lt_iff₀ (by exact_mod_cast b.den_pos)]
      exact_mod_cast
        (Nat.lt_div_mul_add (a := b.num.natAbs) b.den_pos).trans_eq (Nat.add_one_mul ..).symm
    rw [hlc, Option.getD_some]
    exact lt_trans hcb (by exact_mod_cast hrat_lt)

/-- Lowest common multiple of all denominators in a rational coefficient list. -/
@[expose] def lcmDens : List ℚ → ℕ
  | [] => 1
  | q :: qs => Nat.lcm q.den (lcmDens qs)

/-- `lcmDens cs` is always positive (`1 ≤ lcmDens cs`). -/
theorem one_le_lcmDens (cs : List ℚ) : 1 ≤ lcmDens cs := by
  induction cs with
  | nil => simp only [lcmDens, le_refl]
  | cons q qs ih =>
    simp only [lcmDens]
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Rat.den_nz q) (by omega))

/-- Every element's denominator divides `lcmDens cs`. -/
theorem dvd_lcmDens {cs : List ℚ} {q : ℚ} (hq : q ∈ cs) : q.den ∣ lcmDens cs := by
  induction cs with
  | nil => cases hq
  | cons a as ih =>
    simp only [lcmDens]
    rcases List.mem_cons.mp hq with rfl | hmem
    · exact Nat.dvd_lcm_left _ _
    · exact dvd_trans (ih hmem) (Nat.dvd_lcm_right _ _)

/-- Clear denominators of `cs : List ℚ`, returning `(D, ns)` with `1 ≤ D` and
`ns.map (↑) = cs.map (D * ·)`. -/
@[expose] def clearDenomsList (cs : List ℚ) : ℕ × List ℤ :=
  let D := lcmDens cs
  (D, cs.map fun q => q.num * ((D / q.den : ℕ) : ℤ))

private theorem ofCoeffList_clearDenoms_aux (D : ℕ) (cs : List ℚ)
    (hD : ∀ q ∈ cs, q.den ∣ D) :
    (ofCoeffList (cs.map fun q => q.num * ((D / q.den : ℕ) : ℤ))).map (algebraMap ℤ ℚ) =
      C (D : ℚ) * ofCoeffList cs := by
  induction cs with
  | nil => simp only [List.map_nil, ofCoeffList_nil, Polynomial.map_zero, mul_zero]
  | cons q cs ih =>
    simp only [List.map_cons, ofCoeffList_cons, Polynomial.map_add, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_X]
    have hcast_div : ((D / q.den : ℕ) : ℚ) = (D : ℚ) / (q.den : ℚ) := by
      have hd_pos : (q.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz q
      rw [eq_div_iff hd_pos]
      exact_mod_cast Nat.div_mul_cancel (hD q List.mem_cons_self)
    have hterm : ((q.num * ((D / q.den : ℕ) : ℤ) : ℤ) : ℚ) = (D : ℚ) * q := by
      rw [Int.cast_mul, Int.cast_natCast, hcast_div, mul_div_assoc',
        mul_comm (q.num : ℚ) (D : ℚ), mul_div_assoc, Rat.num_div_den]
    change C ((q.num * ((D / q.den : ℕ) : ℤ) : ℤ) : ℚ) +
        X * (ofCoeffList (cs.map fun q => q.num * ((D / q.den : ℕ) : ℤ))).map (algebraMap ℤ ℚ) =
      C (D : ℚ) * (C q + X * ofCoeffList cs)
    rw [hterm, ih (fun a ha => hD a (List.mem_cons_of_mem q ha)), C_mul]
    ring

/-- `(clearDenomsList cs).2` represents `(clearDenomsList cs).1 * ofCoeffList cs` over `ℚ[X]`. -/
theorem ofCoeffList_clearDenomsList (cs : List ℚ) :
    (ofCoeffList (clearDenomsList cs).2).map (algebraMap ℤ ℚ) =
      C ((clearDenomsList cs).1 : ℚ) * ofCoeffList cs :=
  ofCoeffList_clearDenoms_aux (lcmDens cs) cs (fun _ hq => dvd_lcmDens hq)

/-- The clearing multiplier `(clearDenomsList cs).1` is always at least `1`. -/
theorem one_le_clearDenomsList_fst (cs : List ℚ) : 1 ≤ (clearDenomsList cs).1 :=
  one_le_lcmDens cs

/-- Sum of squares of an integer coefficient list. -/
@[expose] def sqNormList (ns : List ℤ) : ℕ :=
  ns.foldl (fun acc a => acc + Int.natAbs a ^ 2) 0

private theorem foldl_sqNorm (acc : ℕ) (ns : List ℤ) :
    ns.foldl (fun s a => s + Int.natAbs a ^ 2) acc =
      acc + ∑ i ∈ Finset.range ns.length, (Int.natAbs (ns.getD i 0)) ^ 2 := by
  induction ns generalizing acc with
  | nil => simp only [List.foldl_nil, List.length_nil, Finset.range_zero, Finset.sum_empty,
      add_zero]
  | cons a ns ih =>
    simp only [List.foldl_cons, List.length_cons, ih (acc + Int.natAbs a ^ 2),
      Finset.sum_range_succ', List.getD_cons_zero, List.getD_cons_succ]
    omega

/-- `coeffSqNorm (ofCoeffList ns)` is bounded above by `sqNormList ns`. -/
theorem coeffSqNorm_ofCoeffList_le (ns : List ℤ) :
    coeffSqNorm (ofCoeffList ns) ≤ sqNormList ns := by
  rw [sqNormList, foldl_sqNorm, zero_add, coeffSqNorm_eq_sum_range]
  by_cases h0 : ofCoeffList ns = 0
  · simp only [h0, natDegree_zero, zero_add, Finset.range_one, Finset.sum_singleton, coeff_zero,
      Int.natAbs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Nat.zero_le]
  · have hne : ns ≠ [] := fun hnil => h0 (by rw [hnil, ofCoeffList_nil])
    have := natDegree_ofCoeffList_le ns
    have := List.length_pos_of_ne_nil hne
    exact (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))).trans_eq
      (Finset.sum_congr rfl fun i _ => by rw [coeff_ofCoeffList])

/-- Mignotte squared-separation denominator `d ^ (d + 2) * sqNormList ns ^ (d - 1)`. -/
@[expose] def mignotteSepSqInv (cs : List ℚ) : ℕ :=
  let t := trim cs
  let d := t.length - 1
  let ns := Prod.snd (clearDenomsList t)
  d ^ (d + 2) * (sqNormList ns) ^ (d - 1)

/-- Computable Mignotte bisection depth `K` ensuring dyadic width `2 * B / 2 ^ K` is strictly
smaller than any root gap when `2 ≤ deg p` (`0` when `deg p ≤ 1`). -/
@[expose] def mignotteBisectionDepth (cs : List ℚ) : ℕ :=
  let t := trim cs
  if t.length ≤ 2 then 0
  else
    let b := cauchyBoundNat cs
    let s := mignotteSepSqInv cs
    Nat.clog 4 (4 * b ^ 2 * s / 3 + 1)

/-- `mignotteBisectionDepth cs` vanishes whenever `(ofCoeffList cs).natDegree ≤ 1`. -/
theorem mignotteBisectionDepth_eq_zero_of_natDegree_le_one {cs : List ℚ}
    (hd : (ofCoeffList cs).natDegree ≤ 1) : mignotteBisectionDepth cs = 0 := by
  simp only [mignotteBisectionDepth]
  by_cases h0 : trim cs = []
  · simp only [h0, List.length_nil, Nat.reduceLeDiff, ↓reduceIte]
  · have := (ofCoeffList_trim cs).symm ▸ (isTrimmed_trim cs).natDegree_add_one h0
    simp only [show (trim cs).length ≤ 2 by omega, ↓reduceIte]

/-- For nonzero `ofCoeffList cs`, the cleared-denominator integer coefficient squared norm is
at least `1`. -/
theorem one_le_sqNormList_clearDenoms_trim {cs : List ℚ} (hcs : ofCoeffList cs ≠ 0) :
    1 ≤ sqNormList (Prod.snd (clearDenomsList (trim cs))) := by
  let res := clearDenomsList (trim cs)
  have ht0 : ofCoeffList (trim cs) ≠ 0 := by rwa [ofCoeffList_trim]
  have hD0 : (res.1 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (one_le_clearDenomsList_fst (trim cs))
  have hp0 : ofCoeffList res.2 ≠ 0 := fun h0 => by
    have hmap := ofCoeffList_clearDenomsList (trim cs)
    rw [h0, Polynomial.map_zero] at hmap
    exact mul_ne_zero (C_ne_zero.mpr hD0) ht0 hmap.symm
  have hle := Finset.single_le_sum
    (f := fun i => Int.natAbs ((ofCoeffList res.2).coeff i) ^ 2)
    (fun _ _ => Nat.zero_le _) (mem_support_iff.mpr (leadingCoeff_ne_zero.mpr hp0))
  have hpow : 1 ≤ Int.natAbs (ofCoeffList res.2).leadingCoeff ^ 2 :=
    Nat.pow_pos (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hp0))
  exact (hpow.trans hle).trans (coeffSqNorm_ofCoeffList_le res.2)

private theorem mignotteBisectionDepth_of_two_le {cs : List ℚ}
    (hd : 2 ≤ (ofCoeffList cs).natDegree) :
    (trim cs).length - 1 = (ofCoeffList cs).natDegree ∧
      mignotteSepSqInv cs = (ofCoeffList cs).natDegree ^ ((ofCoeffList cs).natDegree + 2) *
        sqNormList (clearDenomsList (trim cs)).2 ^ ((ofCoeffList cs).natDegree - 1) ∧
      mignotteBisectionDepth cs =
        Nat.clog 4 (4 * cauchyBoundNat cs ^ 2 * mignotteSepSqInv cs / 3 + 1) := by
  have hcs0 : ofCoeffList cs ≠ 0 := fun h0 => by simp only [h0, natDegree_zero] at hd; omega
  have hdeg := natDegree_add_one_trim hcs0
  have hlen : ¬(trim cs).length ≤ 2 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · simp only [mignotteSepSqInv, show (trim cs).length - 1 = (ofCoeffList cs).natDegree by omega]
  · change (if (trim cs).length ≤ 2 then 0 else _) = _
    exact ite_eq_right (fun h => absurd h hlen)

/-- Dyadic bisection at depth `mignotteBisectionDepth cs` shrinks the interval width
`2 * cauchyBoundNat cs / 2 ^ K` strictly below the Mignotte separation between any two distinct
real roots of separable `ofCoeffList cs` (`2 ≤ natDegree`). -/
theorem dyadic_width_lt_root_sep {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (hd : 2 ≤ (ofCoeffList cs).natDegree) {α β : ℝ}
    (hα : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot α)
    (hβ : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot β) (hne : α ≠ β) :
    2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ mignotteBisectionDepth cs < |α - β| := by
  let t := trim cs; let b := cauchyBoundNat cs; let s := mignotteSepSqInv cs
  let k := mignotteBisectionDepth cs; let res := clearDenomsList t
  obtain ⟨_, hs_eq, hk_eq⟩ := mignotteBisectionDepth_of_two_le hd
  have hD0 : (res.1 : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (one_le_clearDenomsList_fst t)
  have hmignotte := mignotte_sep_sqNorm_rat hd hsep hD0
    (by rw [← ofCoeffList_trim cs]; exact ofCoeffList_clearDenomsList t) hα hβ hne
  have hs_ge : (ofCoeffList cs).natDegree ^ ((ofCoeffList cs).natDegree + 2) *
      coeffSqNorm (ofCoeffList res.2) ^ ((ofCoeffList cs).natDegree - 1) ≤ s := by
    rw [show s = _ from hs_eq]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (coeffSqNorm_ofCoeffList_le res.2) _)
  have hmignotte_s : (3 : ℝ) ≤ |α - β| ^ 2 * (s : ℝ) :=
    hmignotte.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hs_ge) (sq_nonneg _))
  have hs_pos : (0 : ℝ) < (s : ℝ) := by
    by_contra hle
    rw [le_antisymm (le_of_not_gt hle) (Nat.cast_nonneg _), mul_zero] at hmignotte_s
    linarith
  have hlt_nat : 4 * b ^ 2 * s < 3 * 4 ^ k := by
    change k = Nat.clog 4 (4 * b ^ 2 * s / 3 + 1) at hk_eq
    have := hk_eq ▸ Nat.le_pow_clog (by decide : 1 < 4) (4 * b ^ 2 * s / 3 + 1); omega
  have h4_eq : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
  have hwidth_sq : (2 * (b : ℝ) / (2 : ℝ) ^ k) ^ 2 * (s : ℝ) < 3 := by
    rw [show (2 * (b : ℝ) / (2 : ℝ) ^ k) ^ 2 * (s : ℝ) =
      ((4 : ℝ) * (b : ℝ) ^ 2 * (s : ℝ)) / ((2 : ℝ) ^ k) ^ 2 by ring,
      div_lt_iff₀ (by positivity), ← h4_eq]
    exact_mod_cast hlt_nat
  exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _)
    ((mul_lt_mul_iff_left₀ hs_pos).mp (hwidth_sq.trans_le hmignotte_s))

/-- Logarithmic upper bound on `mignotteBisectionDepth cs` in terms of `cauchyBoundNat cs`,
`natDegree`, and cleared-denominator `sqNormList`. -/
theorem mignotteBisectionDepth_le (cs : List ℚ) (hd : 2 ≤ (ofCoeffList cs).natDegree) :
    mignotteBisectionDepth cs ≤
      1 + 2 * Nat.clog 4 (cauchyBoundNat cs) +
        ((ofCoeffList cs).natDegree + 2) * Nat.clog 4 (ofCoeffList cs).natDegree +
        ((ofCoeffList cs).natDegree - 1) *
          Nat.clog 4 (sqNormList (Prod.snd (clearDenomsList (trim cs)))) := by
  let d := (ofCoeffList cs).natDegree; let b := cauchyBoundNat cs
  let sn := sqNormList (Prod.snd (clearDenomsList (trim cs)))
  obtain ⟨_, hs_eq, hk_eq⟩ := mignotteBisectionDepth_of_two_le hd
  have hcs0 : ofCoeffList cs ≠ 0 := fun h0 => by simp only [h0, natDegree_zero] at hd; omega
  have hsn_ge1 : 1 ≤ sn := one_le_sqNormList_clearDenoms_trim hcs0
  have hx_ge1 : 1 ≤ b ^ 2 * mignotteSepSqInv cs :=
    Nat.mul_pos (Nat.pow_pos (one_le_cauchyBoundNat cs))
      (hs_eq ▸ Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos hsn_ge1))
  have hdiv_le : 4 * b ^ 2 * mignotteSepSqInv cs / 3 + 1 ≤
      4 * b ^ 2 * mignotteSepSqInv cs := by
    have : 4 * b ^ 2 * mignotteSepSqInv cs = 4 * (b ^ 2 * mignotteSepSqInv cs) := by ring
    omega
  have clog_pow (a m : ℕ) : a ^ m ≤ 4 ^ (m * Nat.clog 4 a) := by
    rw [mul_comm m _, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 4) a) m
  have hpow_all : 4 * b ^ 2 * mignotteSepSqInv cs ≤
      4 ^ (1 + 2 * Nat.clog 4 b + (d + 2) * Nat.clog 4 d + (d - 1) * Nat.clog 4 sn) := by
    rw [hs_eq]
    calc 4 * b ^ 2 * (d ^ (d + 2) * sn ^ (d - 1))
        ≤ 4 * 4 ^ (2 * Nat.clog 4 b) *
            (4 ^ ((d + 2) * Nat.clog 4 d) * 4 ^ ((d - 1) * Nat.clog 4 sn)) := by
          have := clog_pow b 2; have := clog_pow d (d + 2); have := clog_pow sn (d - 1); gcongr
      _ = _ := by simp only [pow_add, pow_one]; ring
  exact hk_eq ▸ Nat.clog_le_of_le_pow (hdiv_le.trans hpow_all)

end Cslib.RealRoot
