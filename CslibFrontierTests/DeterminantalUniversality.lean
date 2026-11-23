/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Computability.Circuit.Arithmetic.Determinant.Formula
import CslibFrontier.Computability.Circuit.Arithmetic.Determinant.Projection
import CslibFrontier.Computability.Circuit.Arithmetic.DeterminantalComplexity
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Determinantal universality and determinant projections of arithmetic formulas

Ordinary `module` clients of `Formula.isProjection_det`, `Formula.determinantalComplexity_eval_le`,
`isProjection_det_iff_exists_isSubstMatrix`, and Valiant's universality
(`exists_isProjection_det`, `exists_hasDeterminantalRepresentation`,
`determinantalComplexity_lt_top`, and
`exists_hasDeterminantalRepresentation_eq_determinantalComplexity`):

* **Input leaf (`F.size = 0`)**: `Formula.input 1` projects from the `1 × 1` generic determinant and
  has exact determinantal complexity `1` over `ℤ`.
* **Constant leaf (`n = 0`, `F.size = 1`)**: the constant `-5` projects from the `2 × 2` generic
  determinant via `Formula.isProjection_det` and has exact determinantal complexity `1`.
* **Subtraction and `IsProjection` vs `HasDeterminantalRepresentation` at `m = 1`**:
  `X₀ - X₁` has `HasDeterminantalRepresentation (X 0 - X 1) 1` (hence `dc(X₀ - X₁) = 1`), yet is
  not a single substitution entry (`¬ IsProjection (X 0 - X 1) (genericMatrix ℤ 1).det`), while an
  explicit `2 × 2` specialization matrix gives `IsProjection (X 0 - X 1) (genericMatrix ℤ 2).det`.
* **Nested product-of-sums formula**: `(X₀ + 1) * (X₁ - 2)` evaluates to `25` on `(4, 7)`, projects
  from `(genericMatrix ℤ 7).det`, and exercises `IsProjection.det_mul` and `isProjection_det_mono`.
* **Characteristic two (`ZMod 2`), non-domain (`ZMod 4`), subsingleton ring (`ZMod 1`), and infinite
  variable index type (`ℕ`)**: verifies that neither `char ≠ 2`, domain, nontriviality, nor
  `Fintype σ` is required.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.DeterminantalUniversality

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-! ### Boundary 1: input leaf (`F.size = 0`) -/

private def inputLeaf : Formula (arithSignature ℤ) 3 := .input 1

example : inputLeaf.size = 0 := rfl

-- Input leaf of size `0` projects from the `1 × 1` generic determinant (`0 + 1 = 1`).
example : IsProjection (X 1 : MvPolynomial (Fin 3) ℤ) (genericMatrix ℤ 1).det :=
  inputLeaf.isProjection_det

-- Exact determinantal complexity `dc(X₁) = 1` over `ℤ`: size `0` gives `det = 1 ≠ X₁`.
example : determinantalComplexity (X 1 : MvPolynomial (Fin 3) ℤ) = 1 := by
  refine le_antisymm inputLeaf.determinantalComplexity_eval_le ?_
  refine le_determinantalComplexity_iff.2 fun m hm => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · obtain ⟨A, -, hdet⟩ := hm
    rw [Matrix.det_fin_zero] at hdet
    have h0 := congrArg (MvPolynomial.eval (0 : Fin 3 → ℤ)) hdet
    norm_num at h0
  · exact_mod_cast hm_pos

/-! ### Boundary 2: zero-input negative constant formula (`n = 0`, `F.size = 1`) -/

private def negFiveFormula : Formula (arithSignature ℤ) 0 := .gate (.const (-5)) Fin.elim0

example : negFiveFormula.size = 1 := rfl

example : IsProjection (C (-5) : MvPolynomial (Fin 0) ℤ) (genericMatrix ℤ 2).det :=
  negFiveFormula.isProjection_det

example : determinantalComplexity (C (-5) : MvPolynomial (Fin 0) ℤ) = 1 := by
  have h1 : HasDeterminantalRepresentation (C (-5) : MvPolynomial (Fin 0) ℤ) 1 :=
    hasDeterminantalRepresentation_of_isProjection
      (isProjection_det_iff_exists_isSubstMatrix.mpr
        ⟨Matrix.of fun _ _ => C (-5), fun _ _ => .C (-5), Matrix.det_fin_one _⟩)
  refine le_antisymm (determinantalComplexity_le h1) ?_
  refine le_determinantalComplexity_iff.2 fun m hm => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · obtain ⟨A, -, hdet⟩ := hm
    rw [Matrix.det_fin_zero] at hdet
    have h0 := congrArg (MvPolynomial.eval Fin.elim0) hdet
    norm_num at h0
  · exact_mod_cast hm_pos

/-! ### Boundary 3: subtraction and `IsProjection` vs `HasDeterminantalRepresentation` at `m = 1` -/

private def subFormula : Formula (arithSignature ℤ) 2 :=
  .gate₂ .add rfl (.input 0)
    (.gate₂ .mul rfl (.gate (.const (-1)) Fin.elim0) (.input 1))

private theorem subFormula_size : subFormula.size = 3 := by
  simp [subFormula]

example : IsProjection (X 0 - X 1 : MvPolynomial (Fin 2) ℤ) (genericMatrix ℤ 4).det := by
  have h := subFormula.isProjection_det
  rw [subFormula_size] at h
  have heq : subFormula.eval (arithInterpretationWith ℤ C) X = X 0 - X 1 := by
    simp [subFormula, Formula.gate₂, arithInterpretationWith]
    ring
  rwa [heq] at h

-- `X₀ - X₁` is affine-linear, so `HasDeterminantalRepresentation (X 0 - X 1) 1` holds (`dc = 1`),
-- yet `X₀ - X₁` is NOT a single substitution entry, so `IsProjection` into the `1 × 1` generic
-- determinant fails while `2 × 2` succeeds via `!![X 0, X 1; 1, 1]`.
example : HasDeterminantalRepresentation (X 0 - X 1 : MvPolynomial (Fin 2) ℤ) 1 ∧
    ¬ IsProjection (X 0 - X 1 : MvPolynomial (Fin 2) ℤ) (genericMatrix ℤ 1).det ∧
    IsProjection (X 0 - X 1 : MvPolynomial (Fin 2) ℤ) (genericMatrix ℤ 2).det := by
  refine ⟨⟨!![X 0 - X 1], fun _ _ => ?_, Matrix.det_fin_one _⟩, ?_, ?_⟩
  · simp only [Matrix.of_apply, Matrix.cons_val_fin_one, sub_eq_add_neg]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_monomial_le _ _).trans (by simp)
    · rw [totalDegree_neg]
      exact (totalDegree_monomial_le _ _).trans (by simp)
  · intro hproj
    obtain ⟨M, hM, hdet⟩ := isProjection_det_iff_exists_isSubstMatrix.mp hproj
    rw [Matrix.det_fin_one] at hdet
    obtain ⟨s, hs⟩ := hM 0 0
    rw [hdet] at hs
    rcases s with i | c
    · fin_cases i
      · have h := congrArg (MvPolynomial.eval ![0, 1]) hs
        norm_num at h
      · have h := congrArg (MvPolynomial.eval ![1, 0]) hs
        norm_num at h
    · have h0 := congrArg (MvPolynomial.eval ![0, 0]) hs
      have h1 := congrArg (MvPolynomial.eval ![1, 0]) hs
      norm_num at h0 h1
      omega
  · refine isProjection_det_iff_exists_isSubstMatrix.mpr
      ⟨!![X 0, X 1; 1, 1], fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp
    · rw [Matrix.det_fin_two_of]
      ring

/-! ### Boundary 4: nested product-of-sums formula, circuit bridge, and projection closure -/

-- `(X₀ + 1) * (X₁ + (-2))` has 5 operation nodes (`2` constants, `2` additions, `1` product).
private def nested : Formula (arithSignature ℤ) 2 :=
  .gate₂ .mul rfl
    (.gate₂ .add rfl (.input 0) (.gate (.const 1) Fin.elim0))
    (.gate₂ .add rfl (.input 1) (.gate (.const (-2)) Fin.elim0))

private theorem nested_size : nested.size = 5 := by
  simp [nested]

example : nested.eval (arithInterpretation ℤ) ![4, 7] = 25 := by
  norm_num [nested, Formula.eval, Formula.gate₂, arithInterpretation, arithInterpretationWith]

private theorem nested_projection :
    IsProjection ((X 0 + 1) * (X 1 - 2) : MvPolynomial (Fin 2) ℤ) (genericMatrix ℤ 6).det := by
  have h := nested.isProjection_det
  rw [nested_size] at h
  have heq : nested.eval (arithInterpretationWith ℤ C) X = (X 0 + 1) * (X 1 - 2) := by
    simp [nested, Formula.gate₂, arithInterpretationWith, sub_eq_add_neg]
  rwa [heq] at h

example : IsProjection (nested.toCircuit.polynomial 0) (genericMatrix ℤ 6).det ∧
    determinantalComplexity (nested.toCircuit.polynomial 0) ≤ 6 := by
  have hp := nested.isProjection_det_toCircuit
  have hdc := nested.determinantalComplexity_toCircuit_le
  rw [nested_size] at hp hdc
  exact ⟨hp, hdc⟩

-- Multiplicative closure (`IsProjection.det_mul`) and dimension padding (`isProjection_det_mono`).
example : IsProjection (((X 0 + 1) * (X 1 - 2)) * X 0 : MvPolynomial (Fin 2) ℤ)
    (genericMatrix ℤ 9).det :=
  isProjection_det_mono (by decide : 6 + 1 ≤ 9) (nested_projection.det_mul
    (Formula.input (σ := arithSignature ℤ) (n := 2) 0).isProjection_det)

/-! ### Boundary 5: characteristic two (`ZMod 2`) and non-domain (`ZMod 4`) -/

private def charTwoFormula : Formula (arithSignature (ZMod 2)) 2 :=
  .gate₂ .mul rfl
    (.gate₂ .add rfl (.input 0) (.input 1))
    (.gate₂ .add rfl (.input 0) (.gate (.const 1) Fin.elim0))

example : IsProjection ((X 0 + X 1) * (X 0 + 1) : MvPolynomial (Fin 2) (ZMod 2))
    (genericMatrix (ZMod 2) 5).det := by
  have h := charTwoFormula.isProjection_det
  rw [show charTwoFormula.size = 4 by simp [charTwoFormula]] at h
  simpa [charTwoFormula, Formula.eval, Formula.gate₂, arithInterpretationWith] using h

-- Over the non-domain `ZMod 4` (`2 * 2 = 0`), `(2 X₀ + 1) * (2 X₁ + 3) = 2 X₀ + 2 X₁ + 3`
-- has size 9 and projects from `(genericMatrix (ZMod 4) 10).det`.
private def zmodFourFormula : Formula (arithSignature (ZMod 4)) 2 :=
  .gate₂ .mul rfl
    (.gate₂ .add rfl
      (.gate₂ .mul rfl (.gate (.const 2) Fin.elim0) (.input 0))
      (.gate (.const 1) Fin.elim0))
    (.gate₂ .add rfl
      (.gate₂ .mul rfl (.gate (.const 2) Fin.elim0) (.input 1))
      (.gate (.const 3) Fin.elim0))

example : zmodFourFormula.eval (arithInterpretationWith (ZMod 4) C) X =
    2 * X 1 + 2 * X 0 + 3 ∧
    IsProjection (zmodFourFormula.eval (arithInterpretationWith (ZMod 4) C) X)
      (genericMatrix (ZMod 4) 10).det := by
  refine ⟨?_, ?_⟩
  · have heval : zmodFourFormula.eval (arithInterpretationWith (ZMod 4) C) X =
        (2 * X 0 + 1) * (2 * X 1 + 3) := by
      simp [zmodFourFormula, Formula.gate₂, arithInterpretationWith, map_ofNat]
    have h4 : (4 : MvPolynomial (Fin 2) (ZMod 4)) = 0 := by
      rw [← map_ofNat C 4, show (OfNat.ofNat 4 : ZMod 4) = 0 by decide, map_zero]
    rw [heval]
    calc (2 * X 0 + 1 : MvPolynomial (Fin 2) (ZMod 4)) * (2 * X 1 + 3)
        = 4 * (X 0 * X 1 + X 0) + (2 * X 1 + 2 * X 0 + 3) := by ring
      _ = 2 * X 1 + 2 * X 0 + 3 := by rw [h4, zero_mul, zero_add]
  · have h := zmodFourFormula.isProjection_det
    rwa [show zmodFourFormula.size = 9 by simp [zmodFourFormula]] at h

/-! ### Boundary 6: subsingleton ring (`ZMod 1`) and infinite variable index type (`ℕ`) -/

-- Over the subsingleton ring `ZMod 1`, every polynomial has determinantal complexity `0`, and
-- `Formula.determinantalComplexity_toCircuit_le` holds without `[Nontrivial K]`.
example (f : MvPolynomial ℕ (ZMod 1)) (F : Formula (arithSignature (ZMod 1)) 2) :
    determinantalComplexity f = 0 ∧
      determinantalComplexity (F.toCircuit.polynomial 0) ≤ F.size + 1 := by
  refine ⟨nonpos_iff_eq_zero.mp (determinantalComplexity_le ⟨!![], fun i => i.elim0, ?_⟩),
    F.determinantalComplexity_toCircuit_le⟩
  exact Subsingleton.elim _ _

-- Over an infinite non-`Fintype` variable type `σ = ℕ`, Valiant's universality produces a
-- projection, a finite determinantal complexity, and an attaining representation.
example :
    let p : MvPolynomial ℕ ℤ := X 0 ^ 3 + X 100 * X 999 - 7
    (∃ m, IsProjection p (genericMatrix ℤ m).det) ∧
      determinantalComplexity p < ⊤ ∧
      ∃ m : ℕ, HasDeterminantalRepresentation p m ∧ (m : ℕ∞) = determinantalComplexity p :=
  ⟨exists_isProjection_det _, determinantalComplexity_lt_top _,
    exists_hasDeterminantalRepresentation_eq_determinantalComplexity _⟩

end CslibFrontierTests.DeterminantalUniversality
