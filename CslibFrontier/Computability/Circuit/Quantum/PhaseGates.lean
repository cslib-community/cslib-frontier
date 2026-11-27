/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Basic
public import CslibFrontier.Foundations.Quantum.Pauli
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Controlled single-qubit gates, `Z` and `T` phase gates, and the `Clifford + T` decomposition

This module defines the controlled-`V` two-qubit gate (`Gate.controlled`), the single-qubit register
phase gates `Gate.pauliZ` (`diag(1, -1)`, obtained by reindexing `Cslib.Quantum.pauliZ`) and
`Gate.phaseT` (`diag(1, e^{i π / 4})`), and proves the exact `2`-term Clifford decomposition
`T = e^{i π / 8} cos (π / 8) · I - i e^{i π / 8} sin (π / 8) · Z` (`Gate.phaseT_eq_comb_pauliZ`)
together with its magic `ℓ₁` weight `cos (π / 8) + sin (π / 8) = √(1 + 1 / √2)`
(`Gate.cos_add_sin_pi_div_eight`).

## Main definitions

* `Cslib.Quantum.Gate.controlled`: the two-qubit controlled-`V` gate (`|0, b⟩ ↦ |0, b⟩`,
  `|1, b⟩ ↦ |1⟩ ⊗ V |b⟩`) for any `V : Gate 1`.
* `Cslib.Quantum.Gate.pauliZ`: the single-qubit Pauli-`Z` gate (`diag(1, -1)`), reindexing
  `Cslib.Quantum.pauliZ` along `Fin 1 → Bool ≃ Bool`.
* `Cslib.Quantum.Gate.phaseT`: the single-qubit `π / 4` phase (`T`) gate (`diag(1, e^{i π / 4})`).

## Main results

* `Cslib.Quantum.Gate.controlled_apply`, `Cslib.Quantum.Gate.pauliZ_apply`,
  `Cslib.Quantum.Gate.phaseT_apply`: matrix-entry characterizations of the three register gates.
* `Cslib.Quantum.Gate.cos_add_sin_pi_div_eight`: `cos (π / 8) + sin (π / 8) = √(1 + 1 / √2)`.
* `Cslib.Quantum.Gate.phaseT_eq_comb_pauliZ`: exact `2`-term Clifford linear combination for
  `Gate.phaseT` in `{1, Gate.pauliZ}`.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum.Gate

open Matrix Real
open scoped Finset

/-- The **controlled-`V` two-qubit gate** (`|0, b⟩ ↦ |0, b⟩`, `|1, b⟩ ↦ |1⟩ ⊗ V |b⟩`) for any
single-qubit gate `V : Gate 1`. -/
noncomputable def controlled (V : Gate 1) : Gate 2 :=
  ⟨Matrix.of fun y x =>
      if y 0 = x 0 then
        if x 0 then (V : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) (fun _ => y 1) (fun _ => x 1)
        else if y 1 = x 1 then 1 else 0
      else 0, by
    let vMat : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ := V
    rw [Matrix.mem_unitaryGroup_iff]
    have hV : vMat * star vMat = 1 := Matrix.mem_unitaryGroup_iff.mp V.2
    ext y x
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.star_apply, Matrix.of_apply]
    change (∑ z : Fin 2 → Bool,
        (if y 0 = z 0 then
          if z 0 then vMat (fun _ => y 1) (fun _ => z 1) else if y 1 = z 1 then 1 else 0
        else 0) *
        star (if x 0 = z 0 then
          if z 0 then vMat (fun _ => x 1) (fun _ => z 1) else if x 1 = z 1 then 1 else 0
        else 0)) = _
    have hsum : (∑ z : Fin 2 → Bool,
        (if y 0 = z 0 then
          if z 0 then vMat (fun _ => y 1) (fun _ => z 1) else if y 1 = z 1 then 1 else 0
        else 0) *
        star (if x 0 = z 0 then
          if z 0 then vMat (fun _ => x 1) (fun _ => z 1) else if x 1 = z 1 then 1 else 0
        else 0)) =
        ∑ b₀ : Bool, ∑ b₁ : Bool,
          (if y 0 = b₀ then
            if b₀ then vMat (fun _ => y 1) (fun _ => b₁) else if y 1 = b₁ then 1 else 0
          else 0) *
          star (if x 0 = b₀ then
            if b₀ then vMat (fun _ => x 1) (fun _ => b₁) else if x 1 = b₁ then 1 else 0
          else 0) := by
      let eqv : (Fin 2 → Bool) ≃ Bool × Bool :=
        { toFun := fun z => (z 0, z 1)
          invFun := fun p i => if i = 0 then p.1 else p.2
          left_inv := fun z => by ext i; fin_cases i <;> rfl
          right_inv := fun p => by ext <;> rfl }
      exact (Fintype.sum_equiv eqv _ (fun p =>
        (if y 0 = p.1 then
          if p.1 then vMat (fun _ => y 1) (fun _ => p.2) else if y 1 = p.2 then 1 else 0
        else 0) *
        star (if x 0 = p.1 then
          if p.1 then vMat (fun _ => x 1) (fun _ => p.2) else if x 1 = p.2 then 1 else 0
        else 0)) (fun _ => rfl)).trans (Fintype.sum_prod_type _)
    rw [hsum]
    have hunit (a c : Bool) :
        vMat (fun _ => a) (fun _ => true) * star (vMat (fun _ => c) (fun _ => true)) +
          vMat (fun _ => a) (fun _ => false) * star (vMat (fun _ => c) (fun _ => false)) =
          if a = c then 1 else 0 := by
      have h1 := congrFun (congrFun hV (fun _ => a)) (fun _ => c)
      rw [Matrix.mul_apply, Matrix.one_apply] at h1
      simp only [Matrix.star_apply] at h1
      have heq1 : ((fun _ : Fin 1 => a) = fun _ => c) ↔ a = c :=
        ⟨fun h => congrFun h 0, fun h => funext fun _ => h⟩
      let eqv1 : Bool ≃ (Fin 1 → Bool) := (Equiv.funUnique (Fin 1) Bool).symm
      have hsum1 : (∑ z : Fin 1 → Bool,
          vMat (fun _ => a) z * star (vMat (fun _ => c) z)) =
          vMat (fun _ => a) (fun _ => true) * star (vMat (fun _ => c) (fun _ => true)) +
            vMat (fun _ => a) (fun _ => false) * star (vMat (fun _ => c) (fun _ => false)) := by
        rw [← Fintype.sum_equiv eqv1
          (fun b => vMat (fun _ => a) (fun _ => b) * star (vMat (fun _ => c) (fun _ => b))) _
          (fun _ => rfl), Fintype.sum_bool]
      rw [← hsum1]
      exact h1.trans (if_congr heq1 rfl rfl)
    have hyx_iff : (y = x) ↔ (y 0 = x 0 ∧ y 1 = x 1) := by
      simp only [funext_iff, Fin.forall_fin_two, Fin.isValue]
    rw [if_congr hyx_iff rfl rfl, Fintype.sum_bool]
    simp only [Fintype.sum_bool]
    by_cases hy0 : y 0 = true <;> by_cases hx0 : x 0 = true
    · simp only [hy0, hx0, ↓reduceIte, Bool.true_eq_false, zero_mul, add_zero, true_and]
      exact hunit (y 1) (x 1)
    · simp [hy0, hx0]
    · simp [hy0, hx0]
    · simp only [Bool.not_eq_true] at hy0 hx0
      simp only [hy0, hx0, ↓reduceIte, Bool.false_eq_true, true_and, mul_zero, add_zero, star_zero]
      cases y 1 <;> cases x 1 <;> simp⟩

@[simp]
theorem controlled_apply (V : Gate 1) (y x : Fin 2 → Bool) :
    (controlled V : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ) y x =
      if y 0 = x 0 then
        if x 0 then (V : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) (fun _ => y 1) (fun _ => x 1)
        else if y 1 = x 1 then 1 else 0
      else 0 := by
  rfl

/-- Single-qubit Pauli-`Z` register gate (`diag(1, -1)`), reindexing `Cslib.Quantum.pauliZ` along
`Fin 1 → Bool ≃ Bool`. -/
noncomputable def pauliZ : Gate 1 :=
  ⟨Cslib.Quantum.pauliZ.submatrix (Equiv.funUnique (Fin 1) Bool) (Equiv.funUnique (Fin 1) Bool),
    Matrix.submatrix_equiv_mem_unitary.mpr pauliZ_mem_unitaryGroup⟩

@[simp]
theorem pauliZ_apply (y x : Fin 1 → Bool) :
    (pauliZ : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) y x =
      if y 0 = x 0 then (if y 0 then -1 else 1) else 0 := by
  change Cslib.Quantum.pauliZ (y 0) (x 0) = _
  rw [Cslib.Quantum.pauliZ_apply]

/-- Single-qubit `T` (`π / 4` phase) gate (`diag(1, e^{i π / 4})`). -/
noncomputable def phaseT : Gate 1 :=
  ⟨Matrix.of fun y x =>
      if y 0 = x 0 then (if x 0 then Complex.exp (Complex.I * (π / 4)) else 1) else 0, by
    have hnorm : Complex.exp (Complex.I * (π / 4)) *
        (starRingEnd ℂ) (Complex.exp (Complex.I * (π / 4))) = 1 := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      have h0 : Complex.I * ((π : ℂ) / 4) + (starRingEnd ℂ) (Complex.I * ((π : ℂ) / 4)) = 0 := by
        simp only [map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
        ring
      rw [h0, Complex.exp_zero]
    rw [Matrix.mem_unitaryGroup_iff]
    ext y x
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.star_apply, Matrix.of_apply]
    let eqv1 : (Fin 1 → Bool) ≃ Bool := Equiv.funUnique (Fin 1) Bool
    have hsum : (∑ z : Fin 1 → Bool,
        (if y 0 = z 0 then (if z 0 then Complex.exp (Complex.I * (π / 4)) else 1) else 0) *
          star (if x 0 = z 0 then (if z 0 then Complex.exp (Complex.I * (π / 4)) else 1) else 0)) =
        ∑ b : Bool,
          (if y 0 = b then (if b then Complex.exp (Complex.I * (π / 4)) else 1) else 0) *
            star (if x 0 = b then
              (if b then Complex.exp (Complex.I * (π / 4)) else 1) else 0) :=
      Fintype.sum_equiv eqv1 _ _ fun _ => rfl
    rw [hsum, Fintype.sum_bool, if_congr (show (y = x) ↔ y 0 = x 0 from
      ⟨fun h => congrFun h 0, fun h => funext fun i => by rw [Fin.eq_zero i, h]⟩) rfl rfl]
    cases y 0 <;> cases x 0
    · simp
    · simp
    · simp
    · simp [hnorm]⟩

@[simp]
theorem phaseT_apply (y x : Fin 1 → Bool) :
    (phaseT : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) y x =
      if y 0 = x 0 then (if x 0 then Complex.exp (Complex.I * (π / 4)) else 1) else 0 := by
  rfl

/-- Exact `Clifford + T` magic norm identity: `cos (π / 8) + sin (π / 8) = √(1 + 1 / √2)`. -/
theorem cos_add_sin_pi_div_eight : cos (π / 8) + sin (π / 8) = √(1 + 1 / √2) := by
  have hpi8_pos : 0 ≤ π / 8 := by positivity
  have hpi8_le : π / 8 ≤ π / 2 := by linarith [pi_pos]
  have hcos_nn : 0 ≤ cos (π / 8) := cos_nonneg_of_mem_Icc ⟨by linarith, hpi8_le⟩
  have hsin_nn : 0 ≤ sin (π / 8) := sin_nonneg_of_mem_Icc ⟨hpi8_pos, by linarith⟩
  have htwo : 2 * (π / 8) = π / 4 := by ring
  have hsq : (cos (π / 8) + sin (π / 8)) ^ 2 = 1 + 1 / √2 := by
    calc (cos (π / 8) + sin (π / 8)) ^ 2
        = (cos (π / 8) ^ 2 + sin (π / 8) ^ 2) + 2 * sin (π / 8) * cos (π / 8) := by ring
      _ = 1 + sin (2 * (π / 8)) := by rw [cos_sq_add_sin_sq, sin_two_mul]
      _ = 1 + √2 / 2 := by rw [htwo, sin_pi_div_four]
      _ = 1 + 1 / √2 := by
          congr 1
          rw [div_eq_div_iff (by norm_num) (by positivity)]
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [← hsq, Real.sqrt_sq (by positivity)]

/-- **Exact `2`-term Clifford decomposition of `Gate.phaseT`:**
`T = e^{i π / 8} cos (π / 8) · I - i e^{i π / 8} sin (π / 8) · Z`, whose absolute coefficients
sum to `cos (π / 8) + sin (π / 8) = √(1 + 1 / √2)`. -/
theorem phaseT_eq_comb_pauliZ :
    (phaseT : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) =
      (Complex.exp (Complex.I * (π / 8)) * (cos (π / 8) : ℂ)) • (1 : Matrix _ _ ℂ) +
        (-Complex.I * Complex.exp (Complex.I * (π / 8)) * (sin (π / 8) : ℂ)) •
          (pauliZ : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) := by
  ext y x
  have heq_iff : (y = x) ↔ y 0 = x 0 :=
    ⟨fun h => congrFun h 0, fun h => funext fun i => by rw [Fin.eq_zero i, h]⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, pauliZ_apply,
    phaseT_apply, if_congr heq_iff rfl rfl]
  by_cases hyx : y 0 = x 0
  · simp only [hyx, ↓reduceIte, mul_one]
    have hcos_sin_pos : Complex.exp (Complex.I * (π / 8)) *
        ((cos (π / 8) : ℂ) - Complex.I * (sin (π / 8) : ℂ)) = 1 := by
      have hm := (Complex.exp_mul_I (-((π / 8 : ℝ) : ℂ))).symm
      rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at hm
      have h1 : (cos (π / 8) : ℂ) - Complex.I * (sin (π / 8) : ℂ) =
          Complex.exp (-((π / 8 : ℝ) : ℂ) * Complex.I) := by linear_combination hm
      rw [h1, ← Complex.exp_add]
      have h0 : Complex.I * ((π : ℂ) / 8) + -((π / 8 : ℝ) : ℂ) * Complex.I = 0 := by
        push_cast; ring
      rw [h0, Complex.exp_zero]
    have hcos_sin_neg : Complex.exp (Complex.I * (π / 8)) *
        ((cos (π / 8) : ℂ) + Complex.I * (sin (π / 8) : ℂ)) =
        Complex.exp (Complex.I * (π / 4)) := by
      have hp := (Complex.exp_mul_I ((π / 8 : ℝ) : ℂ)).symm
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at hp
      have h1 : (cos (π / 8) : ℂ) + Complex.I * (sin (π / 8) : ℂ) =
          Complex.exp (((π / 8 : ℝ) : ℂ) * Complex.I) := by linear_combination hp
      rw [h1, ← Complex.exp_add]
      congr 1
      push_cast; ring
    cases x 0
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
      have hgoal : Complex.exp (Complex.I * ((π : ℂ) / 8)) * (cos (π / 8) : ℂ) +
          -Complex.I * Complex.exp (Complex.I * ((π : ℂ) / 8)) * (sin (π / 8) : ℂ) =
          Complex.exp (Complex.I * ((π : ℂ) / 8)) *
            ((cos (π / 8) : ℂ) - Complex.I * (sin (π / 8) : ℂ)) := by ring
      rw [hgoal, hcos_sin_pos]
    · simp only [↓reduceIte]
      have hgoal : Complex.exp (Complex.I * ((π : ℂ) / 8)) * (cos (π / 8) : ℂ) +
          -Complex.I * Complex.exp (Complex.I * ((π : ℂ) / 8)) * (sin (π / 8) : ℂ) * (-1) =
          Complex.exp (Complex.I * ((π : ℂ) / 8)) *
            ((cos (π / 8) : ℂ) + Complex.I * (sin (π / 8) : ℂ)) := by ring
      rw [hgoal, hcos_sin_neg]
  · simp only [hyx, ↓reduceIte, mul_zero, add_zero]

end Cslib.Quantum.Gate
