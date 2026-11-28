/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Probability.Gaussian.SmoothingParameter
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
import CslibFrontier.Tactic.LinarithCast
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
  invFun k := (decide (0 < k.val), k.val.natAbs - 1)
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
    rw [← Real.exp_natCast_mul, ← Real.exp_add]
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
    have hx : 0 < Real.exp (Real.pi * t ^ 2) - 1 := by
      linarith [Real.one_lt_exp_iff.mpr (by positivity : 0 < Real.pi * t ^ 2)]
    simp only [u, neg_mul, Real.exp_neg]
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
        gaussianWeight (1 / s) (w.val : E)) ≤
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
      toFun := fun u ↦ ⟨w₀ + ⟨u.val, u.property.1⟩, by
        rw [Submodule.coe_add, inner_add_left, hw₀, u.property.2, add_zero]⟩
      invFun := fun w ↦ ⟨(w.val : E) - (w₀ : E),
        D.sub_mem w.val.property w₀.property,
        by rw [inner_sub_left, w.property, hw₀, sub_self]⟩
      left_inv := fun u ↦ by ext; simp
      right_inv := fun w ↦ by ext; simp
    }
    have hweight (u : P) :
        gaussianWeight (1 / s) ((ej u).val : E) =
          Real.exp (-Real.pi * (s / ‖v‖) ^ 2 * (j : ℝ) ^ 2) *
            gaussianWeight (1 / s) ((u : E) - (-c)) := by
      have hdecomp : ((ej u).val : E) = ((j : ℝ) / ‖v‖ ^ 2) • v + ((u : E) - (-c)) := by
        simp only [ej, Equiv.coe_fn_mk, Submodule.coe_add, sub_neg_eq_add, c]
        rw [add_left_comm, add_sub_cancel, add_comm]
      have horth : ⟪((j : ℝ) / ‖v‖ ^ 2) • v, (u : E) - (-c)⟫ = 0 := by
        rw [real_inner_smul_left, sub_neg_eq_add, inner_add_right, ← real_inner_comm v (u : E),
          u.property.2, ← real_inner_comm v c, hcv, add_zero, mul_zero]
      have hnorm_sq : ‖((ej u).val : E)‖ ^ 2 =
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

private theorem dual_inner_int_floor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {v : E} (hvL : v ∈ L)
    (w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :
    ((Int.floor ⟪(w : E), v⟫ : ℤ) : ℝ) = ⟪(w : E), v⟫ := by
  obtain ⟨j, hj⟩ := Submodule.mem_one.mp (w.property v hvL)
  have hinner : ⟪(w : E), v⟫ = (j : ℝ) := by
    simpa only [innerₗ_apply_apply, real_inner_comm, algebraMap_int_eq, eq_intCast] using hj.symm
  rw [hinner, Int.floor_intCast]

private def dualNeZeroFiberEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {v : E} (hvL : v ∈ L) :
    (Σ j : {j : ℤ // j ≠ 0},
        {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ = (j.val : ℝ)}) ≃
      {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ ≠ 0} where
  toFun p := ⟨p.2.val, by rw [p.2.property]; exact Int.cast_ne_zero.mpr p.1.property⟩
  invFun w :=
    ⟨⟨Int.floor ⟪(w.val : E), v⟫, by
      intro h0
      apply w.property
      rw [← dual_inner_int_floor L hvL w.val, h0, Int.cast_zero]⟩,
     ⟨w.val, (dual_inner_int_floor L hvL w.val).symm⟩⟩
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
      ∑' w : {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ = (j.val : ℝ)},
        f w.val) ∧
    (∑' w : {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ ≠ 0}, f w.val) =
      ∑' j : {j : ℤ // j ≠ 0},
        ∑' w : {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ = (j.val : ℝ)},
          f w.val := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  let eqv := dualNeZeroFiberEquiv L hvL
  have hsum_ne : Summable (fun w : {w : D // ⟪(w : E), v⟫ ≠ 0} ↦ f w.val) :=
    hf.comp_injective Subtype.val_injective
  have hsum_sigma :
      Summable (fun p : Σ j : {j : ℤ // j ≠ 0}, {w : D // ⟪(w : E), v⟫ = (j.val : ℝ)} ↦
      f p.2.val) := by
    change Summable ((fun w : {w : D // ⟪(w : E), v⟫ ≠ 0} ↦ f w.val) ∘ eqv)
    exact eqv.summable_iff.mpr hsum_ne
  have hsum_fib (j : {j : ℤ // j ≠ 0}) :
      Summable (fun w : {w : D // ⟪(w : E), v⟫ = (j.val : ℝ)} ↦ f w.val) :=
    hsum_sigma.comp_injective sigma_mk_injective
  refine ⟨hsum_sigma.sigma' hsum_fib, ?_⟩
  rw [← eqv.tsum_eq]
  exact hsum_sigma.tsum_sigma' hsum_fib

private theorem dual_hyperplane_compl_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {v : E} (hvL : v ∈ L) (hv0 : v ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∑' w : {w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L // ⟪(w : E), v⟫ ≠ 0},
        gaussianWeight (1 / s) (w.val : E)) ≤
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
    toFun := fun u ↦ ⟨⟨u.val, u.property.1⟩, u.property.2⟩
    invFun := fun w ↦ ⟨w.val.val, w.val.property, w.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
  }
  have hM0 : (∑' w : {w : D // ⟪(w : E), v⟫ = 0}, gaussianWeight (1 / s) (w.val : E)) =
      gaussianMass P (1 / s) 0 := by
    rw [← e0.tsum_eq]
    simp only [gaussianMass, e0, Equiv.coe_fn_mk, sub_zero]
  have hsplit : gaussianMass P (1 / s) 0 +
      (∑' w : {w : D // ⟪(w : E), v⟫ ≠ 0}, gaussianWeight (1 / s) (w.val : E)) =
        gaussianMass D (1 / s) 0 := by
    rw [← hM0, gaussianMass]
    simp only [sub_zero]
    exact hsumD.tsum_subtype_add_tsum_subtype_compl {w : D | ⟪(w : E), v⟫ = 0}
  obtain ⟨hsum_outer, hne_eq⟩ := dual_fiber_sum_eq L hvL
    (fun w : D ↦ gaussianWeight (1 / s) (w : E)) hsumD
  have ht : 0 < s / ‖v‖ := div_pos hs hv_norm
  have hbound_ne : (∑' w : {w : D // ⟪(w : E), v⟫ ≠ 0}, gaussianWeight (1 / s) (w.val : E)) ≤
      2 / (Real.exp (Real.pi * (s / ‖v‖) ^ 2) - 1) * gaussianMass P (1 / s) 0 := by
    calc
      (∑' w : {w : D // ⟪(w : E), v⟫ ≠ 0}, gaussianWeight (1 / s) (w.val : E))
        = ∑' j : {j : ℤ // j ≠ 0},
            ∑' w : {w : D // ⟪(w : E), v⟫ = (j.val : ℝ)},
              gaussianWeight (1 / s) (w.val : E) := hne_eq
      _ ≤ ∑' j : {j : ℤ // j ≠ 0},
            Real.exp (-Real.pi * (s / ‖v‖) ^ 2 * (j.val : ℝ) ^ 2) * gaussianMass P (1 / s) 0 :=
          Summable.tsum_le_tsum (fun j ↦ dual_hyperplane_fiber_le L hv0 hs j.val) hsum_outer
            ((summable_int_ne_zero_exp_neg_pi_mul_sq ht).mul_right _)
      _ = (∑' j : {j : ℤ // j ≠ 0},
            Real.exp (-Real.pi * (s / ‖v‖) ^ 2 * (j.val : ℝ) ^ 2)) * gaussianMass P (1 / s) 0 :=
          tsum_mul_right
      _ ≤ 2 / (Real.exp (Real.pi * (s / ‖v‖) ^ 2) - 1) * gaussianMass P (1 / s) 0 :=
          mul_le_mul_of_nonneg_right (tsum_int_ne_zero_exp_neg_pi_mul_sq_le ht)
            (gaussianMass_pos P (1 / s) hs' 0).le
  have hexp_gt : 1 < Real.exp (Real.pi * (s / ‖v‖) ^ 2) :=
    Real.one_lt_exp_iff.mpr (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at hbound_ne
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), ← hsplit]
  linarith

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
    have hNontriv : Nontrivial E := finrank_pos_iff.mp hn_pos
    have hL_ne : L ≠ ⊥ := fun hbot ↦
      top_ne_bot (by rw [← IsZLattice.span_top (K := ℝ) (L := L), hbot]; simp)
    have : ProperSpace E := FiniteDimensional.proper ℝ E
    have hlam_pos : 0 < successiveMinimum L (finrank ℝ E) :=
      (minimum_pos hL_ne).trans_le (minimum_le_successiveMinimum L hL_ne hn_pos le_rfl)
    obtain ⟨v, hv_li, hv_mem, hv_norm⟩ :=
      exists_linearIndependent_norm_le_successiveMinimum L (le_refl (finrank ℝ E))
    have harg_gt : 1 < 2 * (finrank ℝ E : ℝ) * (1 + 1 / ε) := by
      have := one_div_pos.mpr hε
      cast_nlinarith [hn_pos]
    -- By the choice of `s`, `x = exp (π (s / λ_n)²)` is at least `2 n (1 + 1 / ε)`.
    set x : ℝ := Real.exp (Real.pi * (s / successiveMinimum L (finrank ℝ E)) ^ 2) with hx
    have hx_ge : 2 * (finrank ℝ E : ℝ) * (1 + 1 / ε) ≤ x := by
      refine (Real.log_le_iff_le_exp (by linarith)).1 ?_
      rw [← div_le_iff₀' Real.pi_pos, ← Real.sqrt_le_left (by positivity), le_div_iff₀ hlam_pos]
      exact hbound
    -- Each hyperplane complement `{w | ⟪w, v i⟫ ≠ 0}` has mass at most `2 / (x + 1)` of the total.
    have hper_i (i : Fin (finrank ℝ E)) :
        (∑' w : {w : D // ⟪(w : E), v i⟫ ≠ 0}, gaussianWeight (1 / s) (w.val : E)) ≤
          2 / (x + 1) * gaussianMass D (1 / s) 0 := by
      refine (dual_hyperplane_compl_le L (hv_mem i) (hv_li.ne_zero i) hs).trans
        (mul_le_mul_of_nonneg_right ?_ (gaussianMass_pos D (1 / s) hs' 0).le)
      have hv_pos : 0 < ‖v i‖ := norm_pos_iff.mpr (hv_li.ne_zero i)
      gcongr
      rw [hx]
      gcongr
      exact hv_norm i
    -- Union bound: the `v i` span `E`, so every nonzero `w` lies in some hyperplane complement.
    have hsumD : Summable (fun w : D ↦ gaussianWeight (1 / s) (w : E)) := by
      simpa only [sub_zero] using summable_gaussianWeight D (1 / s) hs' 0
    have : Nonempty (Fin (finrank ℝ E)) := ⟨⟨0, hn_pos⟩⟩
    let b := basisOfLinearIndependentOfCardEqFinrank hv_li (Fintype.card_fin _)
    let ind (i : Fin (finrank ℝ E)) : D → ℝ :=
      {w : D | ⟪(w : E), v i⟫ ≠ 0}.indicator fun w ↦ gaussianWeight (1 / s) (w : E)
    have hind_nonneg (i : Fin (finrank ℝ E)) (w : D) : 0 ≤ ind i w :=
      Set.indicator_nonneg (fun _ _ ↦ (gaussianWeight_pos _ _).le) w
    have hpt (w : {w : D | w ≠ 0}) : gaussianWeight (1 / s) (w.val : E) ≤ ∑ i, ind i w := by
      obtain ⟨i, hi⟩ : ∃ i, ⟪(w.val : E), v i⟫ ≠ 0 := by
        by_contra! hall
        refine w.property (Subtype.ext ((inner_self_eq_zero (𝕜 := ℝ)).1 ?_))
        nth_rw 2 [← b.sum_repr (w.val : E)]
        simp [inner_sum, inner_smul_right, b, hall]
      exact (Set.indicator_of_mem hi fun w : D ↦ gaussianWeight (1 / s) (w : E)).symm.le.trans
        (Finset.single_le_sum (fun j _ ↦ hind_nonneg j w) (Finset.mem_univ i))
    have htotal : gaussianMass D (1 / s) 0 - 1 ≤
        2 * (finrank ℝ E : ℝ) / (x + 1) * gaussianMass D (1 / s) 0 :=
      calc
        gaussianMass D (1 / s) 0 - 1 ≤ ∑' w : {w : D | w ≠ 0}, ∑ i, ind i w := by
          rw [gaussianMass_zero_sub_one_eq_tsum D (1 / s) hs']
          exact Summable.tsum_le_tsum hpt (hsumD.subtype _)
            (summable_sum fun i _ ↦ (hsumD.indicator _).subtype _)
        _ = ∑ i, ∑' w : {w : D | w ≠ 0}, ind i w :=
          Summable.tsum_finsetSum fun i _ ↦ (hsumD.indicator _).subtype _
        _ ≤ ∑ i, ∑' w, ind i w := Finset.sum_le_sum fun i _ ↦
          Summable.tsum_subtype_le _ _ (hind_nonneg i) (hsumD.indicator _)
        _ ≤ ∑ _i : Fin (finrank ℝ E), 2 / (x + 1) * gaussianMass D (1 / s) 0 :=
          Finset.sum_le_sum fun i _ ↦ (tsum_subtype _ _).symm.trans_le (hper_i i)
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    -- Solve `M ≤ 2 n (1 + M) / (x + 1)` for `M = ρ_{1/s}(D \ {0})`.
    have hM := gaussianMass_zero_sub_one_nonneg D (1 / s) hs'
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at htotal
    have hx' : 2 * (finrank ℝ E : ℝ) * (ε + 1) ≤ x * ε :=
      calc
        _ = 2 * (finrank ℝ E : ℝ) * (1 + 1 / ε) * ε := by field_simp
        _ ≤ x * ε := by gcongr
    have h2n : (0 : ℝ) < 2 * finrank ℝ E := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hx' hM, mul_le_mul_of_nonneg_left htotal hε.le]

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
      have hinv : 0 < 1 / ε := one_div_pos.mpr hε
      cast_nlinarith [hnpos]
    have hsqrt : 0 < Real.sqrt (Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) / Real.pi) :=
      Real.sqrt_pos.mpr (div_pos (Real.log_pos harg) Real.pi_pos)
    let s := Real.sqrt (Real.log (2 * (finrank ℝ E : ℝ) * (1 + 1 / ε)) / Real.pi) *
      successiveMinimum L (finrank ℝ E)
    have hs : 0 < s := mul_pos hsqrt hlam
    exact smoothingParameter_le_of_dual_mass_le L hs
      (gaussianMass_dual_sub_one_le_of_successiveMinimum L ε hε s hs le_rfl)

end SuccessiveMinimumBound

end ZLattice
