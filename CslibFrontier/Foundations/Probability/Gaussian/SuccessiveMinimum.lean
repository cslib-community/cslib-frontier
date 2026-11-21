/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Lattice.Minimum
public import CslibFrontier.Foundations.Probability.Gaussian.Discrete
public import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice

import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Successive-minimum smoothing parameter bound

This module proves [MicciancioRegev2007], Lemma 3.3 (pp. 11–12 of the December 27, 2005 author's
copy): for every full-rank discrete lattice `L` in a finite-dimensional real inner product space
`E` of dimension `n = finrank ℝ E` and every `ε > 0`,
`η_ε(L) ≤ √(ln (2 n (1 + 1 / ε)) / π) * λ_n(L)`
(`ZLattice.smoothingParameter_le_sqrt_log_mul_successiveMinimum`), together with its underlying
dual-mass inequality `ρ_{1/s}(L* \ {0}) ≤ ε` for every width `s > 0` above that threshold
(`ZLattice.gaussianMass_dual_sub_one_le_of_successiveMinimum`). Both results hold in every
dimension including zero and require no `MeasurableSpace E` instance. The asymptotic `ω(log n)` /
negligible-`ε` remark of Lemma 3.3 is not formalized here.

## Main results

* `ZLattice.gaussianMass_dual_sub_one_le_of_successiveMinimum`: dual-mass core of the
  Micciancio–Regev `λ_n` smoothing bound, including dimension zero.
* `ZLattice.smoothingParameter_le_sqrt_log_mul_successiveMinimum`: Micciancio–Regev Lemma 3.3,
  `η_ε(L) ≤ √(ln (2 n (1 + 1 / ε)) / π) * λ_n(L)`, including dimension zero.

## References

* [MicciancioRegev2007], Lemma 3.3 (pp. 11–12 of the December 27, 2005 author's copy;
  `SIAM J. Comput.` 37(1):267–302, 2007).
-/

public section

noncomputable section

open Module ProbabilityTheory MeasureTheory
open scoped RealInnerProductSpace

namespace ZLattice

section SuccessiveMinimumBound

private def intNeZeroEquiv : Bool × ℕ ≃ {k : ℤ // k ≠ 0} where
  toFun p := if p.1 then ⟨(p.2 : ℤ) + 1, by omega⟩ else ⟨-((p.2 : ℤ) + 1), by omega⟩
  invFun k := (decide (0 < k.1), k.1.natAbs - 1)
  left_inv := by
    rintro ⟨b, m⟩
    cases b <;> simp only [↓reduceIte, Bool.false_eq_true, Prod.mk.injEq, decide_eq_true_eq,
      decide_eq_false_iff_not]
    · constructor <;> omega
    · constructor <;> omega
  right_inv := by
    rintro ⟨k, hk⟩
    by_cases hpos : 0 < k
    · simp only [decide_eq_true hpos, ↓reduceIte, Subtype.mk.injEq]; omega
    · simp only [decide_eq_false hpos, Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq]; omega

private theorem exp_neg_pi_mul_sq_intNeZeroEquiv (t : ℝ) (p : Bool × ℕ) :
    Real.exp (-Real.pi * t ^ 2 * ((intNeZeroEquiv p : ℤ) : ℝ) ^ 2) =
      Real.exp (-Real.pi * t ^ 2 * ((p.2 : ℝ) + 1) ^ 2) := by
  cases hb : p.1 <;> simp only [intNeZeroEquiv, Equiv.coe_fn_mk, hb, ↓reduceIte,
    Bool.false_eq_true, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_sq]

private theorem exp_neg_pi_mul_sq_add_one_le (t : ℝ) (m : ℕ) :
    Real.exp (-Real.pi * t ^ 2 * ((m : ℝ) + 1) ^ 2) ≤
      Real.exp (-Real.pi * t ^ 2) * Real.exp (-Real.pi * t ^ 2) ^ m := by
  have hpow : Real.exp (-Real.pi * t ^ 2) * Real.exp (-Real.pi * t ^ 2) ^ m =
      Real.exp (-Real.pi * t ^ 2 * ((m : ℝ) + 1)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hpow]
  apply Real.exp_le_exp.mpr
  have hm : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hpt : 0 ≤ Real.pi * t ^ 2 := by positivity
  nlinarith

private theorem summable_nat_exp_neg_pi_mul_sq {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ ↦ Real.exp (-Real.pi * t ^ 2 * ((m : ℝ) + 1) ^ 2)) := by
  let u : ℝ := Real.exp (-Real.pi * t ^ 2)
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hu1 : u < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos ht])
  exact Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) (exp_neg_pi_mul_sq_add_one_le t)
    ((summable_geometric_of_lt_one hu0 hu1).mul_left u)

private theorem summable_int_ne_zero_exp_neg_pi_mul_sq {t : ℝ} (ht : 0 < t) :
    Summable (fun k : {k : ℤ // k ≠ 0} ↦ Real.exp (-Real.pi * t ^ 2 * (k : ℝ) ^ 2)) := by
  rw [← intNeZeroEquiv.summable_iff]
  have heq : (fun p : Bool × ℕ ↦
      Real.exp (-Real.pi * t ^ 2 * ((intNeZeroEquiv p : ℤ) : ℝ) ^ 2)) =
      fun p : Bool × ℕ ↦ Real.exp (-Real.pi * t ^ 2 * ((p.2 : ℝ) + 1) ^ 2) :=
    funext (exp_neg_pi_mul_sq_intNeZeroEquiv t)
  rw [Function.comp_def, heq]
  exact (summable_prod_of_nonneg fun _ ↦ (Real.exp_pos _).le).mpr
    ⟨fun _ ↦ summable_nat_exp_neg_pi_mul_sq ht, Summable.of_finite⟩

private theorem tsum_int_ne_zero_exp_neg_pi_mul_sq_le {t : ℝ} (ht : 0 < t) :
    (∑' k : {k : ℤ // k ≠ 0}, Real.exp (-Real.pi * t ^ 2 * (k : ℝ) ^ 2)) ≤
      2 / (Real.exp (Real.pi * t ^ 2) - 1) := by
  let u : ℝ := Real.exp (-Real.pi * t ^ 2)
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hu1 : u < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos ht])
  have hgeom_sum : Summable (fun m : ℕ ↦ u * u ^ m) :=
    (summable_geometric_of_lt_one hu0 hu1).mul_left u
  have hnat : Summable (fun m : ℕ ↦ Real.exp (-Real.pi * t ^ 2 * ((m : ℝ) + 1) ^ 2)) :=
    summable_nat_exp_neg_pi_mul_sq ht
  have hnat_le : (∑' m : ℕ, Real.exp (-Real.pi * t ^ 2 * ((m : ℝ) + 1) ^ 2)) ≤
      u / (1 - u) := by
    calc
      _ ≤ ∑' m : ℕ, u * u ^ m :=
        Summable.tsum_le_tsum (exp_neg_pi_mul_sq_add_one_le t) hnat hgeom_sum
      _ = u * ∑' m : ℕ, u ^ m := tsum_mul_left
      _ = u * (1 - u)⁻¹ := by rw [tsum_geometric_of_lt_one hu0 hu1]
      _ = u / (1 - u) := by rw [div_eq_mul_inv]
  have hprod_sum : Summable (fun p : Bool × ℕ ↦
      Real.exp (-Real.pi * t ^ 2 * ((p.2 : ℝ) + 1) ^ 2)) :=
    (summable_prod_of_nonneg fun _ ↦ (Real.exp_pos _).le).mpr ⟨fun _ ↦ hnat, Summable.of_finite⟩
  have htsum_eq : (∑' k : {k : ℤ // k ≠ 0}, Real.exp (-Real.pi * t ^ 2 * (k : ℝ) ^ 2)) =
      2 * ∑' m : ℕ, Real.exp (-Real.pi * t ^ 2 * ((m : ℝ) + 1) ^ 2) := by
    rw [← intNeZeroEquiv.tsum_eq]
    simp_rw [exp_neg_pi_mul_sq_intNeZeroEquiv]
    rw [hprod_sum.tsum_prod' (fun _ ↦ hnat), tsum_bool]
    ring
  have hident : 2 * (u / (1 - u)) = 2 / (Real.exp (Real.pi * t ^ 2) - 1) := by
    have hx : 1 < Real.exp (Real.pi * t ^ 2) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    have hu_eq : u = (Real.exp (Real.pi * t ^ 2))⁻¹ := by
      dsimp only [u]
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [hu_eq]
    have hx0 : Real.exp (Real.pi * t ^ 2) ≠ 0 := by linarith
    have hx1 : Real.exp (Real.pi * t ^ 2) - 1 ≠ 0 := by linarith
    have hu1' : 1 - (Real.exp (Real.pi * t ^ 2))⁻¹ ≠ 0 := by
      have : (Real.exp (Real.pi * t ^ 2))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
      linarith
    field_simp
  rw [htsum_eq, ← hident]
  linarith

private def dualOrthSubmodule {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (v : E) : Submodule ℤ E where
  carrier := {x : E | x ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L ∧ ⟪x, v⟫ = 0}
  add_mem' hx hy := ⟨(LinearMap.BilinForm.dualSubmodule (innerₗ E) L).add_mem hx.1 hy.1,
    by rw [inner_add_left, hx.2, hy.2, add_zero]⟩
  zero_mem' := ⟨(LinearMap.BilinForm.dualSubmodule (innerₗ E) L).zero_mem, inner_zero_left v⟩
  smul_mem' a x hx := ⟨(LinearMap.BilinForm.dualSubmodule (innerₗ E) L).smul_mem a hx.1,
    by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hx.2, mul_zero]⟩

private theorem discreteTopology_dualOrthSubmodule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (v : E) :
    DiscreteTopology (dualOrthSubmodule L v) :=
  DiscreteTopology.of_subset (discreteTopology_dualSubmodule L) fun _ hx ↦ hx.1

private theorem dual_hyperplane_fiber_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {v : E} (hv0 : v ≠ 0) {s : ℝ} (hs : 0 < s) (j : ℤ) :
    (∑' w : {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ = (j : ℝ)},
        gaussianWeight (1 / s) (w.1 : E)) ≤
      Real.exp (-Real.pi * (s / ‖v‖) ^ 2 * (j : ℝ) ^ 2) *
        gaussianMass (dualOrthSubmodule L v) (1 / s) 0 := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  let P := dualOrthSubmodule L v
  have : DiscreteTopology P := discreteTopology_dualOrthSubmodule L v
  have hs' : 0 < 1 / s := one_div_pos.mpr hs
  have hv_norm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  by_cases hne : Nonempty {w : D // ⟪(w : E), v⟫ = (j : ℝ)}
  · obtain ⟨⟨w₀, hw₀⟩⟩ := hne
    let c : E := (w₀ : E) - ((j : ℝ) / ‖v‖ ^ 2) • v
    have hcv : ⟪c, v⟫ = 0 := by
      dsimp only [c]
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hw₀]
      have hvn : ‖v‖ ^ 2 ≠ 0 := (sq_pos_of_pos hv_norm).ne'
      field_simp
      ring
    let ej : P ≃ {w : D // ⟪(w : E), v⟫ = (j : ℝ)} := {
      toFun := fun u ↦ ⟨w₀ + ⟨u.1, u.2.1⟩, by
        rw [Submodule.coe_add, inner_add_left, hw₀, u.2.2, add_zero]⟩
      invFun := fun w ↦ ⟨(w.1 : E) - (w₀ : E),
        D.sub_mem w.1.2 w₀.2,
        by rw [inner_sub_left, w.2, hw₀, sub_self]⟩
      left_inv := fun u ↦ by ext; simp
      right_inv := fun w ↦ by ext; simp
    }
    have hweight (u : P) :
        gaussianWeight (1 / s) ((ej u).1 : E) =
          Real.exp (-Real.pi * (s / ‖v‖) ^ 2 * (j : ℝ) ^ 2) *
            gaussianWeight (1 / s) ((u : E) - (-c)) := by
      have hdecomp : ((ej u).1 : E) = ((j : ℝ) / ‖v‖ ^ 2) • v + ((u : E) - (-c)) := by
        simp only [ej, Equiv.coe_fn_mk, Submodule.coe_add, sub_neg_eq_add, c]
        rw [add_left_comm, add_sub_cancel, add_comm]
      have horth : ⟪((j : ℝ) / ‖v‖ ^ 2) • v, (u : E) - (-c)⟫ = 0 := by
        rw [real_inner_smul_left, sub_neg_eq_add, inner_add_right, ← real_inner_comm v (u : E),
          u.2.2, ← real_inner_comm v c, hcv, add_zero, mul_zero]
      have hnorm_sq : ‖((ej u).1 : E)‖ ^ 2 =
          (j : ℝ) ^ 2 / ‖v‖ ^ 2 + ‖(u : E) - (-c)‖ ^ 2 := by
        rw [hdecomp, norm_add_sq_real, horth, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        have hvn : ‖v‖ ≠ 0 := hv_norm.ne'
        field_simp
        ring
      simp only [gaussianWeight, ← Real.exp_add, hnorm_sq]
      congr 1
      have hsn : s ≠ 0 := hs.ne'
      have hvn : ‖v‖ ≠ 0 := hv_norm.ne'
      field_simp
      ring
    rw [← ej.tsum_eq]
    simp_rw [hweight]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left
      (gaussianMass_le_gaussianMass_zero P (1 / s) hs' (-c)) (Real.exp_pos _).le
  · have : IsEmpty {w : D // ⟪(w : E), v⟫ = (j : ℝ)} := not_nonempty_iff.mp hne
    rw [tsum_empty]
    exact mul_nonneg (Real.exp_pos _).le (gaussianMass_pos P (1 / s) hs' 0).le

private theorem solve_ratio_bound {a b c x : ℝ} (hx : 1 < x)
    (hsplit : a + b = c) (hb : b ≤ 2 / (x - 1) * a) :
    b ≤ 2 / (x + 1) * c := by
  have hsub : 0 < x - 1 := by linarith
  have hadd : 0 < x + 1 := by linarith
  have hmul : (x - 1) * b ≤ 2 * a := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsub] at hb
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hadd]
  linarith

private theorem dual_inner_int_floor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {v : E} (hvL : v ∈ L)
    (w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :
    ((Int.floor ⟪(w : E), v⟫ : ℤ) : ℝ) = ⟪(w : E), v⟫ := by
  obtain ⟨j, hj⟩ := Submodule.mem_one.mp (w.2 v hvL)
  have hinner : ⟪(w : E), v⟫ = (j : ℝ) := by
    simpa only [innerₗ_apply_apply, real_inner_comm, algebraMap_int_eq, eq_intCast] using hj.symm
  rw [hinner, Int.floor_intCast]

private def dualNeZeroFiberEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {v : E} (hvL : v ∈ L) :
    (Σ j : {j : ℤ // j ≠ 0},
        {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ = (j.1 : ℝ)}) ≃
      {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ ≠ 0} where
  toFun p := ⟨p.2.1, by rw [p.2.2]; exact Int.cast_ne_zero.mpr p.1.2⟩
  invFun w :=
    ⟨⟨Int.floor ⟪(w.1 : E), v⟫, by
      intro h0
      apply w.2
      rw [← dual_inner_int_floor L hvL w.1, h0, Int.cast_zero]⟩,
     ⟨w.1, (dual_inner_int_floor L hvL w.1).symm⟩⟩
  left_inv := by
    rintro ⟨⟨j, hj⟩, ⟨w, hw⟩⟩
    have hφj : Int.floor ⟪(w : E), v⟫ = j := by
      apply Int.cast_injective (α := ℝ)
      rw [dual_inner_int_floor L hvL w, hw]
    cases hφj
    rfl
  right_inv := by rintro ⟨w, hw⟩; rfl

private theorem dual_fiber_sum_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {v : E} (hvL : v ∈ L)
    (f : LinearMap.BilinForm.dualSubmodule (innerₗ E) L → ℝ) (hf : Summable f) :
    Summable (fun j : {j : ℤ // j ≠ 0} ↦
      ∑' w : {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ = (j.1 : ℝ)},
        f w.1) ∧
    (∑' w : {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ ≠ 0}, f w.1) =
      ∑' j : {j : ℤ // j ≠ 0},
        ∑' w : {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ = (j.1 : ℝ)},
          f w.1 := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  let eqv := dualNeZeroFiberEquiv L hvL
  have hsum_ne : Summable (fun w : {w : D // ⟪(w : E), v⟫ ≠ 0} ↦ f w.1) :=
    hf.comp_injective Subtype.val_injective
  have hsum_sigma : Summable (fun p : Σ j : {j : ℤ // j ≠ 0}, {w : D // ⟪(w : E), v⟫ = (j.1 : ℝ)} ↦
      f p.2.1) := by
    change Summable ((fun w : {w : D // ⟪(w : E), v⟫ ≠ 0} ↦ f w.1) ∘ eqv)
    exact eqv.summable_iff.mpr hsum_ne
  have hsum_fib (j : {j : ℤ // j ≠ 0}) :
      Summable (fun w : {w : D // ⟪(w : E), v⟫ = (j.1 : ℝ)} ↦ f w.1) :=
    hsum_sigma.comp_injective sigma_mk_injective
  refine ⟨hsum_sigma.sigma' hsum_fib, ?_⟩
  rw [← eqv.tsum_eq]
  exact hsum_sigma.tsum_sigma' hsum_fib

private theorem dual_hyperplane_compl_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {v : E} (hvL : v ∈ L) (hv0 : v ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∑' w : {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ ≠ 0},
        gaussianWeight (1 / s) (w.1 : E)) ≤
      2 / (Real.exp (Real.pi * (s / ‖v‖) ^ 2) + 1) *
        gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 := by
  classical
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  let P := dualOrthSubmodule L v
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  have : DiscreteTopology P := discreteTopology_dualOrthSubmodule L v
  have hs' : 0 < 1 / s := one_div_pos.mpr hs
  have hv_norm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hsumD : Summable (fun w : D ↦ gaussianWeight (1 / s) (w : E)) := by
    simpa only [sub_zero] using summable_gaussianWeight D (1 / s) hs' 0
  let e0 : P ≃ {w : D // ⟪(w : E), v⟫ = 0} := {
    toFun := fun u ↦ ⟨⟨u.1, u.2.1⟩, u.2.2⟩
    invFun := fun w ↦ ⟨w.1.1, w.1.2, w.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
  }
  have hM0 : (∑' w : {w : D // ⟪(w : E), v⟫ = 0}, gaussianWeight (1 / s) (w.1 : E)) =
      gaussianMass P (1 / s) 0 := by
    rw [← e0.tsum_eq]
    unfold gaussianMass
    refine tsum_congr fun u ↦ ?_
    simp only [e0, Equiv.coe_fn_mk, sub_zero]
  have hsplit : gaussianMass P (1 / s) 0 +
      (∑' w : {w : D // ⟪(w : E), v⟫ ≠ 0}, gaussianWeight (1 / s) (w.1 : E)) =
        gaussianMass D (1 / s) 0 := by
    have h := hsumD.tsum_subtype_add_tsum_subtype_compl {w : D | ⟪(w : E), v⟫ = 0}
    let eZero : {w : D // ⟪(w : E), v⟫ = 0} ≃ ↥{w : D | ⟪(w : E), v⟫ = 0} :=
      Equiv.subtypeEquivRight fun _ ↦ Iff.rfl
    let eCompl : {w : D // ⟪(w : E), v⟫ ≠ 0} ≃ ↥({w : D | ⟪(w : E), v⟫ = 0}ᶜ) :=
      Equiv.subtypeEquivRight fun _ ↦ by simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, ne_eq]
    have h1 : (∑' x : ↥{w : D | ⟪(w : E), v⟫ = 0}, gaussianWeight (1 / s) (x.1 : E)) =
        gaussianMass P (1 / s) 0 := by
      rw [← hM0]
      exact (eZero.tsum_eq fun x : ↥{w : D | ⟪(w : E), v⟫ = 0} ↦
        gaussianWeight (1 / s) (x.1 : E)).symm
    have h2 : (∑' x : ↥({w : D | ⟪(w : E), v⟫ = 0}ᶜ), gaussianWeight (1 / s) (x.1 : E)) =
        ∑' w : {w : D // ⟪(w : E), v⟫ ≠ 0}, gaussianWeight (1 / s) (w.1 : E) :=
      (eCompl.tsum_eq fun x : ↥({w : D | ⟪(w : E), v⟫ = 0}ᶜ) ↦
        gaussianWeight (1 / s) (x.1 : E)).symm
    rw [h1, h2] at h
    simpa only [gaussianMass, sub_zero] using h
  obtain ⟨hsum_outer, hne_eq⟩ := dual_fiber_sum_eq L hvL
    (fun w : D ↦ gaussianWeight (1 / s) (w : E)) hsumD
  have ht : 0 < s / ‖v‖ := div_pos hs hv_norm
  have hbound_ne : (∑' w : {w : D // ⟪(w : E), v⟫ ≠ 0}, gaussianWeight (1 / s) (w.1 : E)) ≤
      2 / (Real.exp (Real.pi * (s / ‖v‖) ^ 2) - 1) * gaussianMass P (1 / s) 0 := by
    calc
      (∑' w : {w : D // ⟪(w : E), v⟫ ≠ 0}, gaussianWeight (1 / s) (w.1 : E))
        = ∑' j : {j : ℤ // j ≠ 0},
            ∑' w : {w : D // ⟪(w : E), v⟫ = (j.1 : ℝ)}, gaussianWeight (1 / s) (w.1 : E) := hne_eq
      _ ≤ ∑' j : {j : ℤ // j ≠ 0},
            Real.exp (-Real.pi * (s / ‖v‖) ^ 2 * (j.1 : ℝ) ^ 2) * gaussianMass P (1 / s) 0 :=
          Summable.tsum_le_tsum (fun j ↦ dual_hyperplane_fiber_le L hv0 hs j.1) hsum_outer
            ((summable_int_ne_zero_exp_neg_pi_mul_sq ht).mul_right _)
      _ = (∑' j : {j : ℤ // j ≠ 0},
            Real.exp (-Real.pi * (s / ‖v‖) ^ 2 * (j.1 : ℝ) ^ 2)) * gaussianMass P (1 / s) 0 :=
          tsum_mul_right
      _ ≤ 2 / (Real.exp (Real.pi * (s / ‖v‖) ^ 2) - 1) * gaussianMass P (1 / s) 0 :=
          mul_le_mul_of_nonneg_right (tsum_int_ne_zero_exp_neg_pi_mul_sq_le ht)
            (gaussianMass_pos P (1 / s) hs' 0).le
  have hexp_gt : 1 < Real.exp (Real.pi * (s / ‖v‖) ^ 2) :=
    Real.one_lt_exp_iff.mpr (by positivity)
  exact solve_ratio_bound hexp_gt hsplit hbound_ne

/-- Dual-mass form of [MicciancioRegev2007], Lemma 3.3 (pp. 11–12 of the author's copy),
serving as a step toward the smoothing-parameter inequality
`η_ε(L) ≤ √(ln (2 n (1 + 1 / ε)) / π) · λ_n(L)`.

For every full-rank discrete lattice `L` in a finite-dimensional real inner product space `E` of
dimension `n = finrank ℝ E` (including `n = 0`), every `ε > 0`, and every positive width `s` with
`√(ln (2 n (1 + 1 / ε)) / π) * λ_n(L) ≤ s`, the nonzero dual Gaussian mass at width `1 / s` is at
most `ε`. The asymptotic `ω(log n)` / negligible-`ε` remark of Lemma 3.3 is not formalized here. -/
theorem gaussianMass_dual_sub_one_le_of_successiveMinimum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (ε : ℝ) (hε : 0 < ε) (s : ℝ) (hs : 0 < s)
    (hbound : Real.sqrt (Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) / Real.pi) *
      successiveMinimum L (finrank ℝ E) ≤ s) :
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε := by
  classical
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have hD_disc : DiscreteTopology D := discreteTopology_dualSubmodule L
  have hs' : 0 < 1 / s := one_div_pos.mpr hs
  by_cases hn : finrank ℝ E = 0
  · have : Subsingleton E := finrank_zero_iff.mp hn
    rw [gaussianMass_zero_sub_one_eq_tsum D (1 / s) hs']
    have : IsEmpty {w : D | w ≠ 0} := ⟨fun ⟨w, hw⟩ ↦ hw (Subsingleton.elim w 0)⟩
    rw [tsum_empty]
    exact hε.le
  · have hn_pos : 0 < finrank ℝ E := Nat.pos_of_ne_zero hn
    have : Nonempty (Fin (finrank ℝ E)) := ⟨⟨0, hn_pos⟩⟩
    have hn_real : (1 : ℝ) ≤ (finrank ℝ E : ℝ) := by exact_mod_cast hn_pos
    have hNontriv : Nontrivial E := finrank_pos_iff.mp hn_pos
    have hL_ne : L ≠ ⊥ := by
      intro hbot
      have htop : (⊤ : Submodule ℝ E) = ⊥ := by
        rw [← IsZLattice.span_top (K := ℝ) (L := L), hbot]
        simp
      exact top_ne_bot htop
    have : ProperSpace E := FiniteDimensional.proper ℝ E
    have hlam_pos : 0 < successiveMinimum L (finrank ℝ E) :=
      (minimum_pos hL_ne).trans_le
        (minimum_le_successiveMinimum L hL_ne hn_pos le_rfl)
    obtain ⟨v, hv_li, hv_mem, hv_norm⟩ :=
      exists_linearIndependent_norm_le_successiveMinimum L (le_refl (finrank ℝ E))
    have hv_ne (i : Fin (finrank ℝ E)) : v i ≠ 0 := hv_li.ne_zero i
    have hv_span : Submodule.span ℝ (Set.range v) = ⊤ := by
      simpa only [coe_basisOfLinearIndependentOfCardEqFinrank] using
        (basisOfLinearIndependentOfCardEqFinrank hv_li (Fintype.card_fin _)).span_eq
    have harg_gt : 1 < 2 * (finrank ℝ E : ℝ) * (1 + 1 / ε) := by
      have h1 : 0 < 1 / ε := one_div_pos.mpr hε
      nlinarith
    have hlog_pos : 0 < Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) :=
      Real.log_pos harg_gt
    have hlog_le : Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) ≤
        Real.pi * (s / successiveMinimum L (finrank ℝ E)) ^ 2 := by
      have hsq : (Real.sqrt (Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) / Real.pi) *
          successiveMinimum L (finrank ℝ E)) ^ 2 ≤ s ^ 2 :=
        pow_le_pow_left₀ (by positivity) hbound 2
      rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
      rw [div_pow, mul_div_assoc', le_div_iff₀ (sq_pos_of_pos hlam_pos)]
      have hpi : 0 < Real.pi := Real.pi_pos
      have hmul := mul_le_mul_of_nonneg_left hsq hpi.le
      have hcancel : Real.pi * (Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) / Real.pi *
          successiveMinimum L (finrank ℝ E) ^ 2) =
          Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) *
            successiveMinimum L (finrank ℝ E) ^ 2 := by
        field_simp
      linarith
    let x : ℝ := Real.exp (Real.pi * (s / successiveMinimum L (finrank ℝ E)) ^ 2)
    have hx_ge : 2 * (finrank ℝ E : ℝ) * (1 + 1 / ε) ≤ x := by
      calc
        2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)
          = Real.exp (Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε))) :=
            (Real.exp_log (by linarith)).symm
        _ ≤ x := Real.exp_le_exp.mpr hlog_le
    have hx_gt : 1 < x := by linarith
    have hx_add_pos : 0 < x + 1 := by linarith
    have hper_i (i : Fin (finrank ℝ E)) :
        (∑' w : {w : D // ⟪(w : E), v i⟫ ≠ 0}, gaussianWeight (1 / s) (w.1 : E)) ≤
          2 / (x + 1) * gaussianMass D (1 / s) 0 := by
      have hhi := dual_hyperplane_compl_le L (hv_mem i) (hv_ne i) hs
      refine hhi.trans (mul_le_mul_of_nonneg_right ?_ (gaussianMass_pos D (1 / s) hs' 0).le)
      have hv_pos : 0 < ‖v i‖ := norm_pos_iff.mpr (hv_ne i)
      have hdiv_le : s / successiveMinimum L (finrank ℝ E) ≤ s / ‖v i‖ :=
        div_le_div_of_nonneg_left hs.le hv_pos (hv_norm i)
      have hexp_le : x ≤ Real.exp (Real.pi * (s / ‖v i‖) ^ 2) := by
        apply Real.exp_le_exp.mpr
        gcongr
      exact div_le_div_of_nonneg_left (by norm_num) hx_add_pos (by linarith)
    have hsumD : Summable (fun w : D ↦ gaussianWeight (1 / s) (w : E)) := by
      simpa only [sub_zero] using summable_gaussianWeight D (1 / s) hs' 0
    have hcover : ∀ w : D, w ≠ 0 → ∃ i : Fin (finrank ℝ E), ⟪(w : E), v i⟫ ≠ 0 := by
      intro w hw0
      by_contra hall
      push Not at hall
      have horth : ∀ y : E, ⟪(w : E), y⟫ = 0 := by
        intro y
        have hy : y ∈ Submodule.span ℝ (Set.range v) := hv_span ▸ Submodule.mem_top
        refine Submodule.span_induction ?_ (inner_zero_right _)
          (fun a b _ _ ha hb ↦ by rw [inner_add_right, ha, hb, add_zero])
          (fun r a _ ha ↦ by rw [inner_smul_right, ha, mul_zero]) hy
        rintro _ ⟨i, rfl⟩
        exact hall i
      apply hw0
      apply Subtype.ext
      exact inner_self_eq_zero.mp (horth (w : E))
    let ind (i : Fin (finrank ℝ E)) (w : D) : ℝ :=
      if ⟪(w : E), v i⟫ ≠ 0 then gaussianWeight (1 / s) (w : E) else 0
    have hind_nonneg (i : Fin (finrank ℝ E)) (w : D) : 0 ≤ ind i w := by
      dsimp only [ind]
      split_ifs
      · exact (gaussianWeight_pos _ _).le
      · exact le_rfl
    have hind_sum (i : Fin (finrank ℝ E)) : Summable (ind i) :=
      Summable.of_nonneg_of_le (hind_nonneg i) (fun w ↦ by
        dsimp only [ind]; split_ifs <;> [exact le_rfl; exact (gaussianWeight_pos _ _).le]) hsumD
    have hind_tsum (i : Fin (finrank ℝ E)) :
        (∑' w : D, ind i w) =
          ∑' w : {w : D // ⟪(w : E), v i⟫ ≠ 0}, gaussianWeight (1 / s) (w.1 : E) := by
      let eS : {w : D // ⟪(w : E), v i⟫ ≠ 0} ≃ ↥{w : D | ⟪(w : E), v i⟫ ≠ 0} :=
        Equiv.subtypeEquivRight fun _ ↦ Iff.rfl
      have heq : (∑' w : {w : D // ⟪(w : E), v i⟫ ≠ 0}, gaussianWeight (1 / s) (w.1 : E)) =
          ∑' w : ↥{w : D | ⟪(w : E), v i⟫ ≠ 0}, gaussianWeight (1 / s) (w.1 : E) :=
        eS.tsum_eq fun w : ↥{w : D | ⟪(w : E), v i⟫ ≠ 0} ↦ gaussianWeight (1 / s) (w.1 : E)
      have hsub := tsum_subtype {w : D | ⟪(w : E), v i⟫ ≠ 0}
        (fun w : D ↦ gaussianWeight (1 / s) (w : E))
      rw [heq, hsub]
      refine tsum_congr fun w ↦ ?_
      by_cases hw : ⟪(w : E), v i⟫ ≠ 0
      · rw [Set.indicator_of_mem (show w ∈ {w : D | ⟪(w : E), v i⟫ ≠ 0} from hw)]
        dsimp only [ind]
        split_ifs
        rfl
      · rw [Set.indicator_of_notMem (show w ∉ {w : D | ⟪(w : E), v i⟫ ≠ 0} from hw)]
        dsimp only [ind]
        split_ifs
        rfl
    have hunion : gaussianMass D (1 / s) 0 - 1 ≤
        ∑ i : Fin (finrank ℝ E),
          ∑' w : {w : D // ⟪(w : E), v i⟫ ≠ 0}, gaussianWeight (1 / s) (w.1 : E) := by
      rw [gaussianMass_zero_sub_one_eq_tsum D (1 / s) hs']
      have hpt (w : {w : D | w ≠ 0}) :
          gaussianWeight (1 / s) (w.1 : E) ≤ ∑ i : Fin (finrank ℝ E), ind i w.1 := by
        obtain ⟨i, hi⟩ := hcover w.1 w.2
        calc
          gaussianWeight (1 / s) (w.1 : E) = ind i w.1 := by simp [ind, hi]
          _ ≤ ∑ j : Fin (finrank ℝ E), ind j w.1 :=
            Finset.single_le_sum (f := fun j ↦ ind j w.1) (fun j _ ↦ hind_nonneg j w.1)
              (Finset.mem_univ i)
      have hsub_le (i : Fin (finrank ℝ E)) :
          (∑' w : {w : D | w ≠ 0}, ind i w.1) ≤ ∑' w : D, ind i w := by
        rw [tsum_subtype {w : D | w ≠ 0} (ind i)]
        refine Summable.tsum_le_tsum (fun w ↦ ?_) ((hind_sum i).indicator _) (hind_sum i)
        by_cases hw : w ∈ {w : D | w ≠ 0}
        · rw [Set.indicator_of_mem hw]
        · rw [Set.indicator_of_notMem hw]; exact hind_nonneg i w
      calc
        (∑' w : {w : D | w ≠ 0}, gaussianWeight (1 / s) (w.1 : E))
          ≤ ∑' w : {w : D | w ≠ 0}, ∑ i : Fin (finrank ℝ E), ind i w.1 :=
            Summable.tsum_le_tsum hpt (hsumD.subtype _)
              (summable_sum fun i _ ↦ (hind_sum i).subtype _)
        _ = ∑ i : Fin (finrank ℝ E), ∑' w : {w : D | w ≠ 0}, ind i w.1 :=
            Summable.tsum_finsetSum fun i _ ↦ (hind_sum i).subtype _
        _ ≤ ∑ i : Fin (finrank ℝ E), ∑' w : D, ind i w :=
            Finset.sum_le_sum fun i _ ↦ hsub_le i
        _ = ∑ i : Fin (finrank ℝ E),
              ∑' w : {w : D // ⟪(w : E), v i⟫ ≠ 0}, gaussianWeight (1 / s) (w.1 : E) := by
            simp_rw [hind_tsum]
    have htotal : gaussianMass D (1 / s) 0 - 1 ≤
        (2 * (finrank ℝ E : ℝ)) / (x + 1) * gaussianMass D (1 / s) 0 := by
      calc
        gaussianMass D (1 / s) 0 - 1
          ≤ ∑ i : Fin (finrank ℝ E), (2 / (x + 1) * gaussianMass D (1 / s) 0) :=
            hunion.trans (Finset.sum_le_sum fun i _ ↦ hper_i i)
        _ = (2 * (finrank ℝ E : ℝ)) / (x + 1) * gaussianMass D (1 / s) 0 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    let M := gaussianMass D (1 / s) 0 - 1
    have hM_nonneg : 0 ≤ M := gaussianMass_zero_sub_one_nonneg D (1 / s) hs'
    have hmul : (x + 1) * M ≤ 2 * (finrank ℝ E : ℝ) * (1 + M) := by
      have h : M ≤ 2 * (finrank ℝ E : ℝ) * (1 + M) / (x + 1) := by
        have hD_eq : gaussianMass D (1 / s) 0 = 1 + M := by dsimp only [M]; ring
        rw [div_mul_eq_mul_div, hD_eq] at htotal
        linarith
      have h' := (le_div_iff₀' hx_add_pos).mp h
      linarith
    have hcoeff : 2 * (finrank ℝ E : ℝ) / ε ≤ x + 1 - 2 * (finrank ℝ E : ℝ) := by
      have h1 : 2 * (finrank ℝ E : ℝ) * (1 + 1 / ε) =
          2 * (finrank ℝ E : ℝ) + 2 * (finrank ℝ E : ℝ) / ε := by ring
      linarith
    have hprod : 2 * (finrank ℝ E : ℝ) / ε * M ≤ 2 * (finrank ℝ E : ℝ) := by
      calc
        2 * (finrank ℝ E : ℝ) / ε * M
          ≤ (x + 1 - 2 * (finrank ℝ E : ℝ)) * M :=
            mul_le_mul_of_nonneg_right hcoeff hM_nonneg
        _ ≤ 2 * (finrank ℝ E : ℝ) := by linarith
    have h2n : 0 < 2 * (finrank ℝ E : ℝ) := by positivity
    have hdiv : M / ε ≤ 1 := by
      have : 2 * (finrank ℝ E : ℝ) * (M / ε) ≤ 2 * (finrank ℝ E : ℝ) * 1 := by
        calc
          2 * (finrank ℝ E : ℝ) * (M / ε) = 2 * (finrank ℝ E : ℝ) / ε * M := by ring
          _ ≤ 2 * (finrank ℝ E : ℝ) := hprod
          _ = 2 * (finrank ℝ E : ℝ) * 1 := (mul_one _).symm
      exact le_of_mul_le_mul_left this h2n
    exact (div_le_one hε).mp hdiv

/-- Micciancio–Regev Lemma 3.3 ([MicciancioRegev2007], pp. 11–12 of the December 27, 2005 author's
copy): for every full-rank discrete lattice `L` in a finite-dimensional real inner product space of
dimension `n = finrank ℝ E` and every `ε > 0`,
`η_ε(L) ≤ √(ln (2 n (1 + 1 / ε)) / π) * λ_n(L)`. Holds in every dimension including zero (where
both sides vanish); the asymptotic `ω(log n)` / negligible-`ε` remark is not formalized here. -/
theorem smoothingParameter_le_sqrt_log_mul_successiveMinimum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (ε : ℝ) (hε : 0 < ε) :
    smoothingParameter L ε ≤
      Real.sqrt (Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) / Real.pi) *
        successiveMinimum L (finrank ℝ E) := by
  by_cases hn : finrank ℝ E = 0
  · have : Subsingleton E := finrank_zero_iff.mp hn
    simp [smoothingParameter_eq_zero_of_subsingleton, hn]
  · have hnpos : 0 < finrank ℝ E := Nat.pos_of_ne_zero hn
    have : Nontrivial E := finrank_pos_iff.mp hnpos
    have hLne : L ≠ ⊥ := fun hbot ↦
      top_ne_bot (by rw [← IsZLattice.span_top (K := ℝ) (L := L), hbot]; simp)
    have hlam : 0 < successiveMinimum L (finrank ℝ E) :=
      (minimum_pos hLne).trans_le (minimum_le_successiveMinimum L hLne hnpos le_rfl)
    have harg : 1 < 2 * (finrank ℝ E : ℝ) * (1 + 1 / ε) := by
      have hn1 : (1 : ℝ) ≤ (finrank ℝ E : ℝ) := by exact_mod_cast hnpos
      have hinv : 0 < 1 / ε := one_div_pos.mpr hε
      nlinarith
    have hsqrt : 0 < Real.sqrt (Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) / Real.pi) :=
      Real.sqrt_pos.mpr (div_pos (Real.log_pos harg) Real.pi_pos)
    let s := Real.sqrt (Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) / Real.pi) *
      successiveMinimum L (finrank ℝ E)
    have hs : 0 < s := mul_pos hsqrt hlam
    exact smoothingParameter_le_of_dual_mass_le L hs
      (gaussianMass_dual_sub_one_le_of_successiveMinimum L ε hε s hs le_rfl)

end SuccessiveMinimumBound

end ZLattice
