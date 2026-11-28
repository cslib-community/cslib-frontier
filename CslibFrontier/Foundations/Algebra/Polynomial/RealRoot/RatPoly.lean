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
public import CslibFrontier.Foundations.Data.Polynomial.CoeffList.DivMod
public import Mathlib.Data.List.SignVariations
public import Mathlib.Data.Nat.Log

import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.Cast.Order

/-!
# Computable Rational Sturm Evaluation, Cauchy Bounds, and Mignotte Depth

Building on the general coefficient-list polynomial arithmetic and Euclidean division in
`Polynomial.CoeffList`, this module provides computable Sturm sequences (`sturmSeqList`), rational
sign-variation counting (`sturmVariationsList`), Cauchy root bounds (`cauchyBoundNat`), integer
denominator clearing (`clearDenomsList`), and Mignotte bisection-depth computation
(`mignotteBisectionDepth`) on `List ℚ`, and proves their correspondence with Mathlib's `Polynomial`
and `Polynomial.sturmVariations` over `ℝ`.

## Main definitions

* `Cslib.RealRoot.sturmSeqList`, `Cslib.RealRoot.sturmVariationsList`: computable Sturm sequence
  and rational sign-variation evaluation over `ℚ`.
* `Cslib.RealRoot.cauchyBoundNat`, `Cslib.RealRoot.lcmDens`, `Cslib.RealRoot.clearDenomsList`,
  `Cslib.RealRoot.sqNormList`, `Cslib.RealRoot.mignotteSepSqInv`,
  `Cslib.RealRoot.mignotteBisectionDepth`: computable Cauchy root bound, integer clearing,
  Mignotte separation denominator, and bisection-depth bound.

## Main results

* `Cslib.RealRoot.sturmSeqList_map_ofCoeffList`: `sturmSeqList` computes `Polynomial.sturmSeq`
  elementwise under `Polynomial.ofCoeffList`.
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

/-- Fuel-bounded computable Sturm sequence on trimmed lists. -/
@[expose] def sturmSeqAux : ℕ → List ℚ → List ℚ → List (List ℚ)
  | 0, p, _ => [p]
  | n + 1, p, q =>
    if q.isEmpty then [p]
    else p :: sturmSeqAux n q (CoeffList.negMod p q)

/-- Computable Sturm sequence of a rational coefficient list `cs`. -/
@[expose] def sturmSeqList (cs : List ℚ) : List (List ℚ) :=
  let p := CoeffList.trim cs
  if p.isEmpty then []
  else
    let dp := CoeffList.deriv p
    sturmSeqAux dp.length p dp

private theorem sturmSeqAux_spec : ∀ (n : ℕ) (p q : List ℚ),
    CoeffList.IsTrimmed p → p ≠ [] → CoeffList.IsTrimmed q → q.length ≤ n →
    (sturmSeqAux n p q).map ofCoeffList = Polynomial.sturmSeq (ofCoeffList p) (ofCoeffList q) ∧
      (sturmSeqAux n p q).length ≤ n + 1 ∧
      ∀ f ∈ sturmSeqAux n p q, f.length ≤ max p.length q.length := by
  have base {k : ℕ} {p : List ℚ} (hp : CoeffList.IsTrimmed p) (hp0 : p ≠ []) :
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
    · obtain rfl := List.isEmpty_iff.mp hqe
      simpa only [sturmSeqAux, List.isEmpty_nil, ↓reduceIte, List.length_nil] using base hp hp0
    · have hq0 : q ≠ [] := fun hnil => hqe (List.isEmpty_iff.mpr hnil)
      have hr_len_q : (CoeffList.negMod p q).length < q.length :=
        (CoeffList.length_negMod_lt (hq.ofCoeffList_ne_zero hq0)).trans_le
          (CoeffList.length_trim_le q)
      obtain ⟨ih_map, ih_len, ih_mem⟩ :=
        ih q (CoeffList.negMod p q) hq hq0 (CoeffList.isTrimmed_negMod p q) (by omega)
      simp only [sturmSeqAux, hqe, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.length_cons,
        List.mem_cons]
      refine ⟨?_, by omega, ?_⟩
      · rw [Polynomial.sturmSeq_cons (hp.ofCoeffList_ne_zero hp0), ih_map,
          CoeffList.ofCoeffList_negMod]
      · rintro f (rfl | hf)
        · exact le_max_left _ _
        · exact (ih_mem f hf).trans
            (max_le (le_max_right _ _) (hr_len_q.le.trans (le_max_right _ _)))

private theorem sturmSeqList_of_ne_nil {cs : List ℚ} (hne : CoeffList.trim cs ≠ []) :
    (sturmSeqList cs).map ofCoeffList =
        Polynomial.sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs)) ∧
      (sturmSeqList cs).length ≤ (CoeffList.deriv (CoeffList.trim cs)).length + 1 ∧
      ∀ f ∈ sturmSeqList cs, f.length ≤ (CoeffList.trim cs).length := by
  have he : (CoeffList.trim cs).isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  obtain ⟨hmap, hlen, hmem⟩ := sturmSeqAux_spec (CoeffList.deriv (CoeffList.trim cs)).length
    (CoeffList.trim cs) (CoeffList.deriv (CoeffList.trim cs))
    (CoeffList.isTrimmed_trim cs) hne (CoeffList.isTrimmed_deriv (CoeffList.trim cs)) le_rfl
  simp only [sturmSeqList, he, Bool.false_eq_true, ↓reduceIte]
  exact ⟨by simpa only [CoeffList.ofCoeffList_deriv, CoeffList.ofCoeffList_trim] using hmap,
    hlen, fun f hf => (hmem f hf).trans
      (max_le le_rfl ((CoeffList.length_deriv_le _).trans (Nat.sub_le _ _)))⟩

/-- `sturmSeqList cs` represents
`Polynomial.sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs))` elementwise under
`ofCoeffList`. -/
theorem sturmSeqList_map_ofCoeffList (cs : List ℚ) :
    (sturmSeqList cs).map ofCoeffList =
      Polynomial.sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs)) := by
  by_cases hne : CoeffList.trim cs = []
  · simp [sturmSeqList, hne, (CoeffList.trim_eq_nil_iff cs).mp hne]
  · exact (sturmSeqList_of_ne_nil hne).1

/-- Length bound `(sturmSeqList cs).length ≤ (ofCoeffList cs).natDegree + 1`. -/
theorem sturmSeqList_length_le (cs : List ℚ) :
    (sturmSeqList cs).length ≤ (ofCoeffList cs).natDegree + 1 := by
  by_cases hne : CoeffList.trim cs = []
  · simp [sturmSeqList, hne]
  · have hlen := (sturmSeqList_of_ne_nil hne).2.1
    have hdp := CoeffList.length_deriv_le (CoeffList.trim cs)
    have hdeg := CoeffList.length_trim_eq_natDegree_add_one
      (mt (CoeffList.trim_eq_nil_iff cs).mpr hne)
    omega

/-- Entry length bound: every list in `sturmSeqList cs` has length at most
`(CoeffList.trim cs).length`. -/
theorem sturmSeqList_entry_length_le (cs : List ℚ) {f : List ℚ} (hf : f ∈ sturmSeqList cs) :
    f.length ≤ (CoeffList.trim cs).length := by
  by_cases hne : CoeffList.trim cs = []
  · simp [sturmSeqList, hne] at hf
  · exact (sturmSeqList_of_ne_nil hne).2.2 f hf

/-- Rational Sturm sign variations of a precomputed Sturm sequence at `x : ℚ`. -/
@[expose] def sturmVariationsList (seq : List (List ℚ)) (x : ℚ) : ℕ :=
  (seq.map (evalCoeffList x)).signVariations

/-- `sturmVariationsList (sturmSeqList cs) x` equals the real Sturm sign-variation count
`Polynomial.sturmVariations ((ofCoeffList cs).map (algebraMap ℚ ℝ)) (x : ℝ)`. -/
theorem sturmVariationsList_eq_sturmVariations (cs : List ℚ) (x : ℚ) :
    sturmVariationsList (sturmSeqList cs) x =
      Polynomial.sturmVariations ((ofCoeffList cs).map (algebraMap ℚ ℝ)) (x : ℝ) := by
  rw [sturmVariationsList, Polynomial.sturmVariations, Polynomial.derivative_map,
    Polynomial.sturmSeq_map (algebraMap ℚ ℝ), ← sturmSeqList_map_ofCoeffList cs,
    ← List.signVariations_map (f := algebraMap ℚ ℝ) fun q => by
      rcases lt_trichotomy q 0 with h | rfl | h <;> simp [eq_ratCast, sign_neg, sign_pos, *]]
  simp only [List.map_map]
  refine congrArg List.signVariations (List.map_congr_left fun g _ => ?_)
  simpa only [Function.comp_apply, Polynomial.eval_map, eval_ofCoeffList, eq_ratCast] using
    (Polynomial.eval₂_hom (p := ofCoeffList g) (algebraMap ℚ ℝ) x).symm

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
  let t := CoeffList.trim cs
  if t.length ≤ 1 then 1
  else
    let lc := Option.getD t.getLast? 1
    let m := maxAbsList t.dropLast
    let b := m / |lc| + 1
    Int.natAbs b.num / b.den + 1

/-- `cauchyBoundNat cs` is always at least `1`. -/
theorem one_le_cauchyBoundNat (cs : List ℚ) : 1 ≤ cauchyBoundNat cs := by
  simp only [cauchyBoundNat]
  split_ifs <;> exact Nat.succ_pos _

private theorem getD_dropLast_of_lt {α : Type*} (l : List α) (d : α) {i : ℕ}
    (hi : i < l.length - 1) : l.dropLast.getD i d = l.getD i d := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_dropLast]; exact hi),
    List.getD_eq_getElem _ _ (Nat.lt_of_lt_of_le hi (Nat.sub_le _ _)), List.getElem_dropLast]

/-- Every real root `r` of `(ofCoeffList cs).map (algebraMap ℚ ℝ)` (when nonzero) satisfies
`|r| < cauchyBoundNat cs`. -/
theorem abs_lt_cauchyBoundNat_of_isRoot {cs : List ℚ} (hcs : ofCoeffList cs ≠ 0) {r : ℝ}
    (hr : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r) :
    |r| < (cauchyBoundNat cs : ℝ) := by
  let t := CoeffList.trim cs
  have ht : CoeffList.IsTrimmed t := CoeffList.isTrimmed_trim cs
  have ht0 : ofCoeffList t ≠ 0 := (CoeffList.ofCoeffList_trim cs).symm ▸ hcs
  have htnil : t ≠ [] := mt (CoeffList.trim_eq_nil_iff cs).mp hcs
  have hdeg : t.length = (ofCoeffList t).natDegree + 1 :=
    CoeffList.ofCoeffList_trim cs ▸ CoeffList.length_trim_eq_natDegree_add_one hcs
  have hr' : ((ofCoeffList t).map (algebraMap ℚ ℝ)).IsRoot r :=
    (CoeffList.ofCoeffList_trim cs).symm ▸ hr
  dsimp only [cauchyBoundNat]
  split_ifs with hlen
  · change t.length ≤ 1 at hlen
    have hc := eq_C_of_natDegree_eq_zero (by omega : (ofCoeffList t).natDegree = 0)
    rw [hc, Polynomial.map_C, IsRoot.def, eval_C, eq_ratCast, Rat.cast_eq_zero] at hr'
    exact absurd (by rw [hc, hr', C_0]) ht0
  · obtain ⟨l, lc, _, hteq⟩ := ht.exists_append_singleton htnil
    have hlead : (ofCoeffList t).leadingCoeff = lc := by
      rw [ht.leadingCoeff_ofCoeffList, hteq, List.getLastD_concat]
    have hlc : t.getLast? = some lc := by simp [hteq]
    have hcb := abs_lt_cauchyBound_of_forall_coeff_le ht0 (maxAbsList_nonneg _)
      (fun i hi => by
        rw [coeff_ofCoeffList, ← getD_dropLast_of_lt t 0 (by omega)]
        exact abs_getD_le_maxAbsList t.dropLast i) hr'
    rw [hlead] at hcb
    let b := maxAbsList t.dropLast / |lc| + 1
    have hrat_lt : b < ((Int.natAbs b.num / b.den + 1 : ℕ) : ℚ) := by
      have hlt : b.num < ((b.num.natAbs / b.den + 1) * b.den : ℕ) :=
        Int.le_natAbs.trans_lt (Int.ofNat_lt.mpr
          ((Nat.lt_div_mul_add b.den_pos).trans_eq (Nat.add_one_mul ..).symm))
      conv_lhs => rw [← Rat.num_div_den b]
      rw [div_lt_iff₀ (Nat.cast_pos.mpr b.den_pos), ← Nat.cast_mul, ← Int.cast_natCast]
      exact Int.cast_lt.mpr hlt
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
  | cons q qs ih => exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Rat.den_nz q) (by omega))

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
      rw [eq_div_iff (by exact_mod_cast Rat.den_nz q)]
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
  · have := natDegree_ofCoeffList_le ns
    have := List.length_pos_of_ne_nil (l := ns) fun hnil => h0 (by rw [hnil, ofCoeffList_nil])
    exact (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))).trans_eq
      (Finset.sum_congr rfl fun i _ => by rw [coeff_ofCoeffList])

/-- Mignotte squared-separation denominator `d ^ (d + 2) * sqNormList ns ^ (d - 1)`. -/
@[expose] def mignotteSepSqInv (cs : List ℚ) : ℕ :=
  let t := CoeffList.trim cs
  let d := t.length - 1
  let ns := Prod.snd (clearDenomsList t)
  d ^ (d + 2) * (sqNormList ns) ^ (d - 1)

/-- Computable Mignotte bisection depth `K` ensuring dyadic width `2 * B / 2 ^ K` is strictly
smaller than any root gap when `2 ≤ deg p` (`0` when `deg p ≤ 1`). -/
@[expose] def mignotteBisectionDepth (cs : List ℚ) : ℕ :=
  let t := CoeffList.trim cs
  if t.length ≤ 2 then 0
  else
    let b := cauchyBoundNat cs
    let s := mignotteSepSqInv cs
    Nat.clog 4 (4 * b ^ 2 * s / 3 + 1)

/-- `mignotteBisectionDepth cs` vanishes whenever `(ofCoeffList cs).natDegree ≤ 1`. -/
theorem mignotteBisectionDepth_eq_zero_of_natDegree_le_one {cs : List ℚ}
    (hd : (ofCoeffList cs).natDegree ≤ 1) : mignotteBisectionDepth cs = 0 := by
  have hlen : (CoeffList.trim cs).length ≤ 2 := by
    by_cases h0 : CoeffList.trim cs = []
    · simp [h0]
    · have := CoeffList.length_trim_eq_natDegree_add_one (mt (CoeffList.trim_eq_nil_iff cs).mpr h0)
      omega
  exact ite_eq_left hlen

/-- For nonzero `ofCoeffList cs`, the cleared-denominator integer coefficient squared norm is
at least `1`. -/
theorem one_le_sqNormList_clearDenoms_trim {cs : List ℚ} (hcs : ofCoeffList cs ≠ 0) :
    1 ≤ sqNormList (Prod.snd (clearDenomsList (CoeffList.trim cs))) := by
  let res := clearDenomsList (CoeffList.trim cs)
  have ht0 : ofCoeffList (CoeffList.trim cs) ≠ 0 := by rwa [CoeffList.ofCoeffList_trim]
  have hD0 : (res.1 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (one_le_clearDenomsList_fst (CoeffList.trim cs))
  have hp0 : ofCoeffList res.2 ≠ 0 := fun h0 => by
    have hmap := ofCoeffList_clearDenomsList (CoeffList.trim cs)
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
    (CoeffList.trim cs).length - 1 = (ofCoeffList cs).natDegree ∧
      mignotteSepSqInv cs = (ofCoeffList cs).natDegree ^ ((ofCoeffList cs).natDegree + 2) *
        sqNormList (clearDenomsList (CoeffList.trim cs)).2 ^ ((ofCoeffList cs).natDegree - 1) ∧
      mignotteBisectionDepth cs =
        Nat.clog 4 (4 * cauchyBoundNat cs ^ 2 * mignotteSepSqInv cs / 3 + 1) := by
  have hcs0 : ofCoeffList cs ≠ 0 := fun h0 => by simp [h0] at hd
  have hdeg := CoeffList.length_trim_eq_natDegree_add_one hcs0
  have hd1 : (CoeffList.trim cs).length - 1 = (ofCoeffList cs).natDegree := by omega
  have hlen : ¬(CoeffList.trim cs).length ≤ 2 := by omega
  exact ⟨hd1, by simp only [mignotteSepSqInv, hd1], ite_eq_right hlen⟩

/-- Dyadic bisection at depth `mignotteBisectionDepth cs` shrinks the interval width
`2 * cauchyBoundNat cs / 2 ^ K` strictly below the Mignotte separation between any two distinct
real roots of separable `ofCoeffList cs` (`2 ≤ natDegree`). -/
theorem dyadic_width_lt_root_sep {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (hd : 2 ≤ (ofCoeffList cs).natDegree) {α β : ℝ}
    (hα : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot α)
    (hβ : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot β) (hne : α ≠ β) :
    2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ mignotteBisectionDepth cs < |α - β| := by
  obtain ⟨_, hs_eq, hk_eq⟩ := mignotteBisectionDepth_of_two_le hd
  set t := CoeffList.trim cs
  set b := cauchyBoundNat cs
  set s := mignotteSepSqInv cs
  set k := mignotteBisectionDepth cs
  let res := clearDenomsList t
  have hD0 : (res.1 : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (one_le_clearDenomsList_fst t)
  have hmignotte := mignotte_sep_sqNorm_rat hd hsep hD0
    (by rw [← CoeffList.ofCoeffList_trim cs]; exact ofCoeffList_clearDenomsList t) hα hβ hne
  have hs_ge : (ofCoeffList cs).natDegree ^ ((ofCoeffList cs).natDegree + 2) *
      coeffSqNorm (ofCoeffList res.2) ^ ((ofCoeffList cs).natDegree - 1) ≤ s :=
    hs_eq.symm ▸ Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (coeffSqNorm_ofCoeffList_le res.2) _)
  have hmignotte_s : (3 : ℝ) ≤ |α - β| ^ 2 * (s : ℝ) :=
    hmignotte.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hs_ge) (sq_nonneg _))
  have hs_pos : (0 : ℝ) < (s : ℝ) := pos_of_mul_pos_right (by linarith) (sq_nonneg |α - β|)
  have hlt : 4 * b ^ 2 * s < 3 * 4 ^ k := by
    have := hk_eq ▸ Nat.le_pow_clog (by decide : 1 < 4) (4 * b ^ 2 * s / 3 + 1)
    omega
  have hwidth_sq : (2 * (b : ℝ) / (2 : ℝ) ^ k) ^ 2 * (s : ℝ) < 3 := by
    rw [div_pow, mul_pow, div_mul_eq_mul_div, div_lt_iff₀ (by positivity), ← pow_mul,
      mul_comm k 2, pow_mul]
    norm_num only
    exact_mod_cast hlt
  exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _)
    ((mul_lt_mul_iff_left₀ hs_pos).mp (hwidth_sq.trans_le hmignotte_s))

/-- Logarithmic upper bound on `mignotteBisectionDepth cs` in terms of `cauchyBoundNat cs`,
`natDegree`, and cleared-denominator `sqNormList`. -/
theorem mignotteBisectionDepth_le (cs : List ℚ) (hd : 2 ≤ (ofCoeffList cs).natDegree) :
    mignotteBisectionDepth cs ≤
      1 + 2 * Nat.clog 4 (cauchyBoundNat cs) +
        ((ofCoeffList cs).natDegree + 2) * Nat.clog 4 (ofCoeffList cs).natDegree +
        ((ofCoeffList cs).natDegree - 1) *
          Nat.clog 4 (sqNormList (Prod.snd (clearDenomsList (CoeffList.trim cs)))) := by
  let d := (ofCoeffList cs).natDegree; let b := cauchyBoundNat cs
  let sn := sqNormList (Prod.snd (clearDenomsList (CoeffList.trim cs)))
  obtain ⟨_, hs_eq, hk_eq⟩ := mignotteBisectionDepth_of_two_le hd
  have hcs0 : ofCoeffList cs ≠ 0 := fun h0 => by simp only [h0, natDegree_zero] at hd; omega
  have hsn_ge1 : 1 ≤ sn := one_le_sqNormList_clearDenoms_trim hcs0
  have hx_ge1 : 1 ≤ b ^ 2 * mignotteSepSqInv cs :=
    Nat.mul_pos (Nat.pow_pos (one_le_cauchyBoundNat cs))
      (hs_eq ▸ Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos hsn_ge1))
  have hdiv_le : 4 * b ^ 2 * mignotteSepSqInv cs / 3 + 1 ≤ 4 * b ^ 2 * mignotteSepSqInv cs := by
    rw [mul_assoc]; omega
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
