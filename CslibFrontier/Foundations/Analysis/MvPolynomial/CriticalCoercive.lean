/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, real multivariate polynomial minima)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CriticalSystem
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
import CslibFrontier.Foundations.Analysis.MvPolynomial.CoordinateDerivative
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

/-!
# Coercive minima of the separated critical deformation

The separated even-power potential is nonnegative and has compact sublevels for nonnegative
centers. Perturbing it by a nonnegative multiple of a nonnegative input preserves compact
sublevels, so the actual deformed polynomial attains its minimum. These minima are uniformly
bounded over nonnegative parameters exactly when the input has a real zero.
On a closed set containing a zero, constrained minimizers have a subsequence tending
to a zero in the set as the deformation parameter tends to infinity.
Normal separation lets the limit lie in a chosen relatively clopen zero-set piece, with
the minimizers eventually satisfying the normalized critical equations.

Adapted from `SeparatedPowerPotential`, `CoerciveMinimum`, and `CriticalMinimum` in lean-canny
at `970f28a5ecefc1327402ade16c068aa4b1b2c183`. For the boundedness criterion, minimizing the
input on one compact sublevel gives a positive uniform lower bound if there is no zero.
Constrained sampling adapts `CoerciveConstrainedSampling` and `UnboundedCoerciveComponents`
at the same revision.
-/

public section

namespace MvPolynomial.CriticalSystem

open Filter Set
open scoped BigOperators Topology

variable {n : ℕ}

private noncomputable def potentialTerm (ell : ℕ) (a t : ℝ) : ℝ :=
  t ^ (ell + 1) - (ell + 1 : ℕ) * a ^ ell * t + (ell + 1 : ℕ) * a ^ (ell + 1)

private theorem potentialTerm_nonneg (ell : ℕ) (he : Even (ell + 1)) {a : ℝ} (ha : 0 ≤ a)
    (t : ℝ) : 0 ≤ potentialTerm ell a t := by
  by_cases ht : 0 ≤ t
  · have h := pow_add_mul_le_add_pow ha
      (show 0 ≤ 2 * a + (t - a) by linarith) (ell + 1)
    rw [show a + (t - a) = t by ring, Nat.add_sub_cancel] at h
    unfold potentialTerm
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] at h ⊢
    nlinarith [pow_nonneg ha ell]
  · exact add_nonneg (sub_nonneg.mpr
      ((mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge ht)).trans
        (he.pow_nonneg t))) (by positivity)

private theorem abs_le_potentialTerm (ell : ℕ) (hell : 1 ≤ ell) (he : Even (ell + 1))
    {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    |t| ≤ potentialTerm ell a t + (ell + 1 : ℕ) * a ^ ell + 1 := by
  let c : ℝ := (ell + 1 : ℕ) * a ^ ell
  have hc : 0 ≤ c := by positivity
  change |t| ≤ potentialTerm ell a t + c + 1
  by_cases ht : |t| ≤ c + 1
  · linarith [potentialTerm_nonneg ell he ha t]
  · have hlarge : c + 1 ≤ |t| := (lt_of_not_ge ht).le
    have hp : |t| ^ 2 ≤ t ^ (ell + 1) := calc
      _ ≤ |t| ^ (ell + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      _ = _ := by rw [← abs_pow, abs_of_nonneg (he.pow_nonneg t)]
    have hquad := mul_le_mul_of_nonneg_right hlarge (abs_nonneg t)
    have hlin := mul_le_mul_of_nonneg_left (le_abs_self t) hc
    have hconst : 0 ≤ (ell + 1 : ℕ) * a ^ (ell + 1) := by positivity
    change |t| ≤ (t ^ (ell + 1) - c * t + (ell + 1 : ℕ) * a ^ (ell + 1)) + c + 1
    nlinarith

private theorem eval_potential_eq_sum (ell : ℕ) (a x : Fin n → ℝ) :
    eval x (potentialPolynomial ell a) = ∑ i, potentialTerm ell (a i) (x i) := by
  classical
  simp only [potentialPolynomial, map_sum, map_add, map_sub, map_mul, map_pow, eval_X, eval_C,
    potentialTerm]

/-- With nonnegative centers and an even leading exponent, the real potential is nonnegative. -/
theorem eval_potentialPolynomial_nonneg (ell : ℕ) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (x : Fin n → ℝ) :
    0 ≤ eval x (potentialPolynomial ell a) := by
  rw [eval_potential_eq_sum]
  exact Finset.sum_nonneg fun i _ => potentialTerm_nonneg ell he (ha i) (x i)

/-- Each sublevel of the separated potential is compact. -/
theorem isCompact_sublevel_eval_potentialPolynomial (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (B : ℝ) :
    IsCompact {x | eval x (potentialPolynomial ell a) ≤ B} := by
  have hclosed : IsClosed {x | eval x (potentialPolynomial ell a) ≤ B} :=
    isClosed_le (continuous_eval _) continuous_const
  let bound (i : Fin n) := B + (ell + 1 : ℕ) * a i ^ ell + 1
  apply (isCompact_Icc : IsCompact (Icc (fun i => -bound i) bound)).of_isClosed_subset hclosed
  intro x hx
  change eval x (potentialPolynomial ell a) ≤ B at hx
  rw [eval_potential_eq_sum] at hx
  have hbound (i : Fin n) : |x i| ≤ bound i := by
    have hterm : potentialTerm ell (a i) (x i) ≤ ∑ j, potentialTerm ell (a j) (x j) :=
      Finset.single_le_sum (fun j _ => potentialTerm_nonneg ell he (ha j) (x j)) (Finset.mem_univ i)
    exact (abs_le_potentialTerm ell hell he (ha i) (x i)).trans
      (add_le_add (add_le_add (hterm.trans hx) le_rfl) le_rfl)
  exact ⟨fun i => (abs_le.mp (hbound i)).1, fun i => (abs_le.mp (hbound i)).2⟩

private theorem eval_potential_le_eval_deformed (ell : ℕ) (a x : Fin n → ℝ)
    (F : MvPolynomial (Fin n) ℝ) (hF : 0 ≤ eval x F) {u : ℝ} (hu : 0 ≤ u) :
    eval x (potentialPolynomial ell a) ≤ eval x (deformedPolynomial ell a u F) := by
  rw [eval_deformedPolynomial]
  exact le_add_of_nonneg_right (by positivity)

/-- Perturbing by a nonnegative multiple of a nonnegative polynomial preserves compact
sublevels of the separated potential. -/
theorem isCompact_sublevel_eval_deformedPolynomial (ell : ℕ) (hell : 1 ≤ ell) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (F : MvPolynomial (Fin n) ℝ)
    (hF : ∀ x, 0 ≤ eval x F) (u : ℝ) (hu : 0 ≤ u) (B : ℝ) :
    IsCompact {x | eval x (deformedPolynomial ell a u F) ≤ B} :=
  (isCompact_sublevel_eval_potentialPolynomial ell hell he a ha B).of_isClosed_subset
    (isClosed_le (continuous_eval _) continuous_const)
    (fun x hx => (eval_potential_le_eval_deformed ell a x F (hF x) hu).trans hx)

/-- The real deformed polynomial attains its minimum on any nonempty closed set. -/
theorem exists_isMinOn_eval_deformedPolynomial_on_closed
    (ell : ℕ) (hell : 1 ≤ ell) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (F : MvPolynomial (Fin n) ℝ)
    (hF : ∀ x, 0 ≤ eval x F) (u : ℝ) (hu : 0 ≤ u)
    {S : Set (Fin n → ℝ)} (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ x ∈ S, IsMinOn (fun y => eval y (deformedPolynomial ell a u F)) S x := by
  let f (x : Fin n → ℝ) := eval x (deformedPolynomial ell a u F)
  obtain ⟨x₀, hx₀⟩ := hne
  have hk : IsCompact ({x | f x ≤ f x₀} ∩ S) :=
    (isCompact_sublevel_eval_deformedPolynomial ell hell he a ha F hF u hu (f x₀)).inter_right hS
  have hx₀' : x₀ ∈ {x | f x ≤ f x₀} ∩ S := ⟨show f x₀ ≤ f x₀ from le_rfl, hx₀⟩
  obtain ⟨x, hx, hmin⟩ := hk.exists_isMinOn ⟨x₀, hx₀'⟩ (continuous_eval _).continuousOn
  refine ⟨x, hx.2, fun y hy => ?_⟩
  by_cases h : f y ≤ f x₀
  · exact hmin ⟨h, hy⟩
  · have hxVal : f x ≤ f x₀ := hx.1
    exact hxVal.trans (le_of_not_ge h)

/-- The real deformed polynomial attains a global minimum. -/
theorem exists_isMinOn_eval_deformedPolynomial (ell : ℕ) (hell : 1 ≤ ell) (he : Even (ell + 1))
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (F : MvPolynomial (Fin n) ℝ)
    (hF : ∀ x, 0 ≤ eval x F) (u : ℝ) (hu : 0 ≤ u) :
    ∃ x, IsMinOn (fun y => eval y (deformedPolynomial ell a u F)) univ x := by
  obtain ⟨x, _, hmin⟩ := exists_isMinOn_eval_deformedPolynomial_on_closed ell hell he a ha F hF
    u hu isClosed_univ ⟨0, mem_univ 0⟩
  exact ⟨x, hmin⟩

/-- On a closed set containing a zero of a nonnegative input, constrained minimizers have a
subsequence converging to a zero in that set as the deformation parameter tends to infinity. -/
theorem exists_deformedPolynomial_minimizers_subseq (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hF : ∀ x, 0 ≤ eval x F)
    {S : Set (Fin n → ℝ)} (hS : IsClosed S) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ S)
    (hzero : eval x₀ F = 0) {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (huTop : Tendsto u atTop atTop) :
    ∃ (y : ℕ → Fin n → ℝ) (z : Fin n → ℝ) (φ : ℕ → ℕ),
      (∀ k, y k ∈ S) ∧ (∀ k, IsMinOn (fun x => eval x (deformedPolynomial ell a (u k) F)) S (y k)) ∧
      StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 z) ∧ z ∈ S ∧ eval z F = 0 := by
  choose y hy hymin using fun k => exists_isMinOn_eval_deformedPolynomial_on_closed ell hell he
    a ha F hF (u k) (hu k) hS ⟨x₀, hx₀⟩
  let B := eval x₀ (potentialPolynomial ell a)
  have hcompare (k : ℕ) : eval (y k) (deformedPolynomial ell a (u k) F) ≤ B := by
    have h : eval (y k) (deformedPolynomial ell a (u k) F) ≤
        eval x₀ (deformedPolynomial ell a (u k) F) := hymin k hx₀
    simpa only [eval_deformedPolynomial ell a x₀, hzero, mul_zero, add_zero] using h
  have hb (k : ℕ) : eval (y k) (potentialPolynomial ell a) ≤ B :=
    (eval_potential_le_eval_deformed ell a (y k) F (hF (y k)) (hu k)).trans (hcompare k)
  have hcompact := (isCompact_sublevel_eval_potentialPolynomial ell hell he a ha B).inter_right hS
  obtain ⟨z, hz, φ, hφ, hyLimit⟩ := hcompact.tendsto_subseq (fun k => ⟨hb k, hy k⟩)
  refine ⟨y, z, φ, hy, hymin, hφ, hyLimit, hz.2, ?_⟩
  have huSubseq := huTop.comp hφ.tendsto_atTop
  let c : ℝ := (ell + 1 : ℕ)
  have hvalue : Tendsto (fun k => c * eval (y (φ k)) F) atTop (𝓝 (c * eval z F)) :=
    ((continuous_eval F).continuousAt.tendsto.comp hyLimit).const_mul c
  have hbound : Tendsto (fun k => (u (φ k))⁻¹ * B) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_mul] using
      (tendsto_inv_atTop_zero.comp huSubseq).mul_const B
  have hle : c * eval z F ≤ 0 := by
    apply le_of_tendsto_of_tendsto hvalue hbound
    filter_upwards [huSubseq.eventually_gt_atTop (0 : ℝ)] with k hk
    apply (le_inv_mul_iff₀ hk).2
    have h := hcompare (φ k)
    rw [eval_deformedPolynomial] at h
    exact (le_add_of_nonneg_left (eval_potentialPolynomial_nonneg ell he a ha _)).trans h
  have hcz : c * eval z F = 0 := le_antisymm hle (mul_nonneg (by positivity) (hF z))
  exact (mul_eq_zero.mp hcz).resolve_left (by positivity)

/-- A local minimum of the real deformation satisfies each normalized critical equation. -/
theorem aeval_criticalLower_eq_pow_of_isLocalMin_eval_deformedPolynomial (ell : ℕ)
    (a : Fin n → ℝ) (u : ℝ) (F : MvPolynomial (Fin n) ℝ) {x : Fin n → ℝ}
    (hmin : IsLocalMin (fun y => eval y (deformedPolynomial ell a u F)) x) (i : Fin n) :
    aeval x (criticalLower ell a u F i) = x i ^ ell := by
  let p := deformedPolynomial ell a u F
  have hsection : IsLocalMin (fun t => eval (Function.update x i t) p) (x i) := by
    have hx : IsLocalMin (fun y => eval y p) (Function.update x i (x i)) := by
      rwa [Function.update_eq_self]
    exact hx.comp_continuous (continuous_const.update i continuous_id).continuousAt
  have hzero : eval x (pderiv i (deformedPolynomial ell a u F)) = 0 :=
    hsection.hasDerivAt_eq_zero (hasDerivAt_eval_update p x i)
  rw [pderiv_deformedPolynomial, map_mul, eval_C, map_sub, map_pow, eval_X] at hzero
  have hscale : ((ell + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [aeval_eq_eval]
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hscale)).symm

/-- Each nonempty relatively clopen piece of the zero set of a nonnegative input contains
a limit of deformed samples that eventually satisfy the normalized critical equations. -/
theorem exists_deformedPolynomial_critical_subseq_in_clopen
    (ell : ℕ) (hell : 1 ≤ ell) (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hF : ∀ x, 0 ≤ eval x F)
    (C : Set {x : Fin n → ℝ // eval x F = 0}) (hC : IsClopen C) (hCne : C.Nonempty)
    {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (huTop : Tendsto u atTop atTop) :
    ∃ (y : ℕ → Fin n → ℝ) (z : {x : Fin n → ℝ // eval x F = 0}) (φ : ℕ → ℕ),
      z ∈ C ∧ StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 z.val) ∧
      ∀ᶠ k in atTop, ∀ i, aeval (y (φ k)) (criticalLower ell a (u (φ k)) F i) =
        y (φ k) i ^ ell := by
  let A : Set (Fin n → ℝ) := Subtype.val '' C
  let B : Set (Fin n → ℝ) := Subtype.val '' Cᶜ
  have hZ : IsClosed {x : Fin n → ℝ | eval x F = 0} :=
    isClosed_eq (continuous_eval F) continuous_const
  have hA : IsClosed A := hZ.isClosedEmbedding_subtypeVal.isClosedMap C hC.isClosed
  have hB : IsClosed B := hZ.isClosedEmbedding_subtypeVal.isClosedMap Cᶜ hC.compl.isClosed
  have hAB : A ⊆ Bᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    exact hw (Subtype.ext hwz ▸ hz : w ∈ C)
  obtain ⟨U, hU, hAU, hUB⟩ := normal_exists_closure_subset hA hB.isOpen_compl hAB
  obtain ⟨x₀, hx₀⟩ := hCne
  obtain ⟨y, z, φ, _, hmin, hφ, hlim, hz, hFz⟩ :=
    exists_deformedPolynomial_minimizers_subseq ell hell he a ha F hF isClosed_closure
      (subset_closure (hAU ⟨x₀, hx₀, rfl⟩)) x₀.property hu huTop
  let z₀ : {x : Fin n → ℝ // eval x F = 0} := ⟨z, hFz⟩
  have hzC : z₀ ∈ C := by
    by_contra hzC
    exact (hUB hz) ⟨z₀, hzC, rfl⟩
  have hzU : z ∈ U := hAU ⟨z₀, hzC, rfl⟩
  refine ⟨y, z₀, φ, hzC, hφ, hlim, ?_⟩
  filter_upwards [hlim.eventually (hU.mem_nhds hzU)] with k hk
  have hnhds : closure U ∈ 𝓝 (y (φ k)) :=
    mem_of_superset (hU.mem_nhds hk) subset_closure
  exact aeval_criticalLower_eq_pow_of_isLocalMin_eval_deformedPolynomial ell a _ F
    ((hmin (φ k)).isLocalMin hnhds)

/-- A nonnegative real input has a zero exactly when there is a common bound such that,
for each nonnegative parameter, some point has deformed value at most that bound. -/
theorem exists_zero_iff_bounded_eval_deformedPolynomial (ell : ℕ) (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : MvPolynomial (Fin n) ℝ) (hF : ∀ x, 0 ≤ eval x F) :
    (∃ x, eval x F = 0) ↔
      ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → ∃ x, eval x (deformedPolynomial ell a u F) ≤ B := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨eval x (potentialPolynomial ell a), fun u _ => ⟨x, ?_⟩⟩
    rw [eval_deformedPolynomial, hx, mul_zero, mul_zero, add_zero]
  · rintro ⟨B, hB⟩
    obtain ⟨x₀, hx₀⟩ := hB 0 le_rfl
    have hx₀' := (eval_potential_le_eval_deformed ell a x₀ F (hF x₀) le_rfl).trans hx₀
    have hnonneg := (eval_potentialPolynomial_nonneg ell he a ha x₀).trans hx₀'
    obtain ⟨x, _, hmin⟩ :=
      (isCompact_sublevel_eval_potentialPolynomial ell hell he a ha B).exists_isMinOn
        ⟨x₀, hx₀'⟩ (continuous_eval F).continuousOn
    refine ⟨x, le_antisymm ?_ (hF x)⟩
    by_contra! hpos
    let c : ℝ := (ell + 1 : ℕ) * eval x F
    have hc : 0 < c := by positivity
    let u := (B + 1) / c
    have hu : 0 ≤ u := by positivity
    obtain ⟨y, hy⟩ := hB u hu
    have hyK := (eval_potential_le_eval_deformed ell a y F (hF y) hu).trans hy
    have hle : u * c ≤ u * ((ell + 1 : ℕ) * eval y F) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hmin hyK) (by positivity)) hu
    have hu_eq : u * c = B + 1 := div_mul_cancel₀ _ hc.ne'
    rw [eval_deformedPolynomial] at hy
    linarith [eval_potentialPolynomial_nonneg ell he a ha y]

end MvPolynomial.CriticalSystem
