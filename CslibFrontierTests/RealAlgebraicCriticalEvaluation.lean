/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalJacobianEvaluation
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledBoundedSum
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledCoordinateLift
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledIndexedFeasibility
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledPositivity
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledPowerSection
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledRelativeCoefficient
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledRelativeValue
import CslibFrontier.Computability.Complexity.RealAlgebraic.CoordinateFingerprintWitness
import CslibFrontier.Computability.Complexity.RealAlgebraic.CoordinateSelection
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoordinateCandidates
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoordinateCoefficients
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoordinateCoefficientSign
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoordinateEvaluation
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalPolynomialEvaluation
import CslibFrontier.Computability.Complexity.RealAlgebraic.WordCoordinateFingerprintLabels
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.BranchGrowth
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.DegreePieceSeparation
import CslibFrontier.Foundations.Analysis.MvPolynomial.CoordinateCriticalLimit
import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalCoercive
import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalMinimumValue
import CslibFrontier.Foundations.Analysis.MvPolynomial.RelativeFiberSeparation
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.RelativeValueSection
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Mixed partials, singular determinants and the actual critical Jacobian -/

public section

namespace CslibFrontierTests.RealAlgebraicCriticalEvaluation

open Cslib Cslib.Complexity Cslib.Complexity.RealAlgebraic
open Turing.MultiTapeTM MvPolynomial MvPolynomial.CriticalSystem MvPolynomial.PurePower
open scoped Topology

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- A closed half-line retains a convergent subsequence of constrained minima of the deformation.
example :
    let F : MvPolynomial (Fin 1) ℝ := X 0 ^ 2
    let S : Set (Fin 1 → ℝ) := Set.Ici 0
    ∃ (y : ℕ → Fin 1 → ℝ) (z : Fin 1 → ℝ) (φ : ℕ → ℕ),
      (∀ k : ℕ, IsMinOn (fun x => eval x (deformedPolynomial 3 0 (k : ℝ) F)) S (y k)) ∧
      StrictMono φ ∧ Filter.Tendsto (y ∘ φ) Filter.atTop (𝓝 z) ∧ z ∈ S ∧ eval z F = 0 := by
  intro F S
  obtain ⟨y, z, φ, _, hmin, hφ, hlim, hz, hzero⟩ :=
    exists_deformedPolynomial_minimizers_subseq 3 (by decide) (by decide) 0 (fun _ => le_rfl)
      F (fun x => by simpa only [F, map_pow] using sq_nonneg (eval x (X 0)))
      (S := S) isClosed_Ici (x₀ := 0) (by simp [S]) (by simp [F])
      (u := fun k => (k : ℝ)) (fun _ => Nat.cast_nonneg _) tendsto_natCast_atTop_atTop
  exact ⟨y, z, φ, hmin, hφ, hlim, hz, hzero⟩

-- Sample the positive zero of (X² − 1)² in its relatively clopen piece.
open Filter in
example :
    let F : MvPolynomial (Fin 1) ℝ := (X 0 ^ 2 - 1) ^ 2
    ∃ (y : ℕ → Fin 1 → ℝ) (z : {x : Fin 1 → ℝ // eval x F = 0}) (φ : ℕ → ℕ),
      0 < z.val 0 ∧ Tendsto (y ∘ φ) atTop (𝓝 z.val) ∧
      ∀ᶠ k in atTop, ∀ i, aeval (y (φ k)) (criticalLower 5 0 (φ k : ℝ) F i) = y (φ k) i ^ 5 := by
  intro F
  let Z := {x : Fin 1 → ℝ // eval x F = 0}
  let coord (z : Z) := z.val 0
  let C : Set Z := coord ⁻¹' Set.Ioi 0
  have hcoord : Continuous coord := (continuous_apply 0).comp continuous_subtype_val
  have hne (z : Z) : coord z ≠ 0 := by
    intro hz
    have h := z.property
    have hz' : z.val 0 = 0 := hz
    norm_num [F, hz'] at h
  have hCeq : C = coord ⁻¹' Set.Ici 0 := by
    ext z
    change 0 < coord z ↔ 0 ≤ coord z
    exact ⟨le_of_lt, fun hz => lt_of_le_of_ne hz (Ne.symm (hne z))⟩
  have hC : IsClopen C := ⟨hCeq ▸ isClosed_Ici.preimage hcoord, isOpen_Ioi.preimage hcoord⟩
  have hCne : C.Nonempty := by
    refine ⟨⟨fun _ => 1, by simp [F]⟩, ?_⟩
    change (0 : ℝ) < 1
    norm_num
  obtain ⟨y, z, φ, hz, _, hlim, hcrit⟩ := exists_deformedPolynomial_critical_subseq_in_clopen
    5 (by decide) (by decide) 0 (fun _ => le_rfl) F
    (fun x => by simpa only [F, map_pow] using sq_nonneg (eval x (X 0 ^ 2 - 1))) C hC hCne
    (u := fun k => (k : ℝ)) (fun _ => Nat.cast_nonneg _) tendsto_natCast_atTop_atTop
  exact ⟨y, z, φ, hz, hlim, hcrit⟩

-- A fixed-width word selects a point in the finite coordinate root grid of X².
-- The selected point extends to a zero of the extra coordinate, but never of the constant one.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0 ^ 2
    let hF : F.totalDegree ≤ 3 := (totalDegree_pow (X (R := ℤ) (0 : Fin 1)) 2).trans
      (by
        have h := totalDegree_X_le (R := ℤ) (0 : Fin 1)
        omega)
    let G := coordinateRootGrid (by decide : 1 ≤ 3) F hF
    let p := (Polynomial.Bivariate.swap
      (parametricCoordinatePolynomial (by decide) F hF 0)).leadingCoeff.map (Int.castRingHom ℝ)
    G.Finite ∧ ∃ x ∈ G, eval x (F.map (Int.castRingHom ℝ)) = 0 ∧ p.IsRoot (x 0) ∧
      ∃ word : List Bool, word.length = coordinateFingerprintWitnessWidth 3 1 ∧
        0 < (wordCoordinateFingerprintLabel (d := 2) F hF 0 (by decide) word 0).eval₂
          (Int.castRingHom ℝ) (x 0) ∧
        (∃ z : Fin 3 → ℝ, eval₂ (Int.castRingHom ℝ) z
          (selectionCounterexamplePolynomial (d := 2) (u := 1) F (X 1) hF 0 (by decide) word) = 0) ∧
        ¬ ∃ z : Fin 3 → ℝ, eval₂ (Int.castRingHom ℝ) z
          (selectionCounterexamplePolynomial (d := 2) (u := 1) F 1 hF 0 (by decide) word) = 0 := by
  intro F hF G p
  refine ⟨coordinateRootGrid_finite _ F hF, ?_⟩
  have hFn (x : Fin 1 → ℝ) : 0 ≤ eval x (F.map (Int.castRingHom ℝ)) := by
    simpa only [F, map_pow, MvPolynomial.map_X, eval_X] using sq_nonneg (x 0)
  have hzero : eval (fun _ => 0) (F.map (Int.castRingHom ℝ)) = 0 := by simp [F]
  obtain ⟨z, _, hz⟩ := exists_mem_coordinateRootGrid_of_isClopen (by decide) (by decide) F hF hFn
    Set.univ isClopen_univ ⟨⟨fun _ => 0, hzero⟩, Set.mem_univ _⟩
  have hmass : F.coeffNorm1 ≤ 2 ^ 0 := by
    simpa only [F, coeffNorm1_X, one_pow, pow_zero] using
      coeffNorm1_pow_le (X (R := ℤ) (0 : Fin 1)) 2
  obtain ⟨word, hlen, hselect⟩ :=
    exists_coordinateSelectionWitness (d := 2) (mass := 0) F hF hmass (by decide) (by decide) hz
  have hlabels := ((hselect z.val).mpr rfl).2
  refine ⟨z.val, hz, z.property, mem_coordinateRootGrid.mp hz 0, word, hlen, hlabels 0, ?_, ?_⟩
  · apply (exists_selectionCounterexamplePolynomial_zero_iff (d := 2) (u := 1)
      F (X 1) hF 0 (by decide) word).mpr
    refine ⟨z.val, fun _ => 0, ?_, hz, hlabels, ?_⟩
    · simpa only [eval₂_eq_eval_map] using z.property
    · rw [eval₂_X]
      change Fin.addCases (motive := fun _ => ℝ) z.val (fun _ => 0) (Fin.natAdd 1 (0 : Fin 1)) = 0
      simp only [Fin.addCases_right]
  · intro h
    obtain ⟨_, _, _, _, _, hR⟩ := (exists_selectionCounterexamplePolynomial_zero_iff
      (d := 2) (u := 1) F 1 hF 0 (by decide) word).mp h
    simp at hR

-- Zero is a critical point of the deformation of X² at every parameter.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0 ^ 2
    let hF : F.totalDegree ≤ 2 := (totalDegree_pow (X (R := ℤ) (0 : Fin 1)) 2).trans
      (by simpa only [mul_one] using Nat.mul_le_mul_left 2 (totalDegree_X_le (R := ℤ) (0 : Fin 1)))
    Polynomial.eval₂ (Int.castRingHom ℝ) 0
      (Polynomial.Bivariate.swap (parametricCoordinatePolynomial (by decide) F hF 0)).leadingCoeff =
        0 := by
  intro F hF
  exact eval₂_coordinateLeadingCoeff_eq_zero_of_tendsto (by decide) F hF
    (u := fun k : ℕ => (k : ℝ)) (x := fun _ _ => 0) tendsto_natCast_atTop_atTop
    tendsto_const_nhds (Filter.Eventually.of_forall fun _ j => by
      fin_cases j
      simp [F, criticalLower]) 0

-- First derivatives also work at prime 3; the larger cutoff belongs to second derivatives.
example : (firstPartialResidue 3 1 0 [2] (fun z => z[0]?.getD 0) : ZMod 3) = 1 := by
  change (firstPartialResidue 3 1 (0 : Fin 1).val [2]
    (fun z => z[0]?.getD 0) : ZMod 3) = 1
  rw [firstPartialResidue_cast (X 0 : MvPolynomial (Fin 1) (ZMod 3)) 0 [2]
    (fun z => z[0]?.getD 0) ((totalDegree_X_le 0).trans_lt (by decide)) (by decide)
    (by intro z; simp)]
  simp

private noncomputable def inputPolynomial : MvPolynomial (Fin 2) (ZMod 7) :=
  X 0 ^ 2 + X 0 * X 1

private def inputValue (z : List ℕ) : ℕ :=
  ((z[0]?.getD 0) ^ 2 + (z[0]?.getD 0) * (z[1]?.getD 0)) % 7

private theorem input_degree : inputPolynomial.totalDegree < 7 - 1 := by
  have h0 : (X 0 : MvPolynomial (Fin 2) (ZMod 7)).totalDegree ≤ 1 := totalDegree_X_le 0
  have h1 : (X 1 : MvPolynomial (Fin 2) (ZMod 7)).totalDegree ≤ 1 := totalDegree_X_le 1
  have hp := totalDegree_pow (X 0 : MvPolynomial (Fin 2) (ZMod 7)) 2
  have hm := totalDegree_mul (X 0 : MvPolynomial (Fin 2) (ZMod 7)) (X 1)
  have hs := totalDegree_add (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 7)) (X 0 * X 1)
  change (X 0 ^ 2 + X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 7)).totalDegree < 7 - 1
  omega

private theorem input_correct (z : List ℕ) :
    (inputValue z : ZMod 7) =
      eval (fun i : Fin 2 => (z[i.val]?.getD 0 : ZMod 7)) inputPolynomial := by
  simp [inputValue, inputPolynomial]

private theorem derivative_two (i : Fin 2) :
    pderiv i (2 : MvPolynomial (Fin 2) (ZMod 7)) = 0 := by
  simpa only [Nat.cast_ofNat] using (Derivation.map_natCast (pderiv i) 2)

-- Repeating the differentiation coordinate contributes the explicit factor two.
example : (secondPartialResidue 7 2 0 0 [2, 3] inputValue : ZMod 7) = 2 := by
  change (secondPartialResidue 7 2 (0 : Fin 2).val (0 : Fin 2).val
    [2, 3] inputValue : ZMod 7) = 2
  rw [secondPartialResidue_cast inputPolynomial (0 : Fin 2) (0 : Fin 2)
    [2, 3] inputValue input_degree (by decide) input_correct]
  norm_num [inputPolynomial, pderiv_pow, pderiv_mul, derivative_two]

example : (secondPartialResidue 7 2 0 1 [2, 3] inputValue : ZMod 7) = 1 := by
  change (secondPartialResidue 7 2 (0 : Fin 2).val (1 : Fin 2).val
    [2, 3] inputValue : ZMod 7) = 1
  rw [secondPartialResidue_cast inputPolynomial (0 : Fin 2) (1 : Fin 2)
    [2, 3] inputValue input_degree (by decide) input_correct]
  norm_num [inputPolynomial, pderiv_pow, pderiv_mul, derivative_two]

-- Empty and singular matrices exercise the genuine integer determinant program.
example : (modularMatrixDeterminant 7 0 (fun _ => 3) : ZMod 7) = 1 := by
  rw [modularMatrixDeterminant_cast (Matrix.of (fun _ _ : Fin 0 => (0 : ZMod 7)))
    (fun _ => 3) (by intro i; exact i.elim0)]
  simp

example : (modularMatrixDeterminant 7 2 (fun _ => 1) : ZMod 7) = 0 := by
  rw [modularMatrixDeterminant_cast (Matrix.of (fun _ _ : Fin 2 => (1 : ZMod 7)))
    (fun _ => 1) (by intro i j; rfl)]
  simp [Matrix.det_fin_two]

-- For this coupled polynomial the derivative matrix is [[0,1],[1,6]], with determinant 6.
example : (criticalJacobianValue 7 2 3 1 [2, 3] inputValue : ZMod 7) = 6 := by
  rw [criticalJacobianValue_cast inputPolynomial (fun i => (separatedCenters 3 i : ℕ))
    3 1 [2, 3] inputValue
    input_degree (by decide) input_correct]
  norm_num [jacobian, criticalLower, inputPolynomial, Matrix.det_fin_two,
    pderiv_pow, pderiv_mul, derivative_two]
  decide

example : (criticalLowerValue 7 2 3 1 0 [2, 3] inputValue : ZMod 7) = 6 := by
  change (criticalLowerValue 7 2 3 1 (0 : Fin 2).val [2, 3] inputValue : ZMod 7) = 6
  rw [criticalLowerValue_cast inputPolynomial 3 1 (0 : Fin 2) [2, 3] inputValue
    input_degree (by decide) input_correct]
  norm_num [criticalLower, separatedCenters, inputPolynomial, pderiv_pow, pderiv_mul]
  decide

example : (criticalObjectiveValue 7 2 3 1 [2, 3] inputValue : ZMod 7) = 3 := by
  rw [criticalObjectiveValue_cast inputPolynomial 3 1 [2, 3] inputValue input_correct]
  norm_num [deformedPolynomial, potentialPolynomial, separatedCenters, inputPolynomial,
    Fin.sum_univ_succ]
  decide

example : (zeroObjectiveValue 7 2 3 1 [2, 3] inputValue : ZMod 7) = 4 := by
  rw [zeroObjectiveValue_cast inputPolynomial 3 1 (by decide) [2, 3] inputValue input_correct]
  norm_num [deformedPolynomial, potentialPolynomial, inputPolynomial, Fin.sum_univ_succ]
  decide

example : (fun p : ℕ => zeroObjectiveValue p 2 3 1 [2, 3] (fun _ => 0)) ∈
    CountingFunction 0 encNat encNat := by
  have hv : (fun _ : ℕ × List ℕ => 0) ∈ CountingFunction 0 (encInstancePoint encNat) encNat :=
    CountingFunction.of_polyTime (ComputableInPolyTime.const 0)
  exact zeroObjectiveValue_mem (ComputableInPolyTime.id') (.const 2) (.const 3) (.const 1)
    (.const [2, 3]) hv

-- One certificate handles all binary moduli and powers, including total default inputs.
theorem uniform_jacobian_mem :
    (fun w : ℕ × ℕ => criticalJacobianValue w.1 0 w.2 1 [] (fun _ => 0)) ∈
      CountingFunction 1 (encPair encNat encNat) encNat := by
  apply criticalJacobianValue_mem (a := 0) (p := fun w : ℕ × ℕ => w.1)
    (n := fun _ => 0) (ell := fun w => w.2) (u := fun _ => 1)
    (z := fun _ => []) (value := fun _ => 0) (Decoder.pair Decoder.nat Decoder.nat)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  exact CountingFunction.of_polyTime (ComputableInPolyTime.const 0)

-- For one coordinate and exponent two, the degree-two coefficient is monic.
example : criticalCoordinateCoefficientValue 11 1 1 1 0 2 (fun z => z[0]?.getD 0) = 1 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let : Fact (1 < 11) := ⟨by decide⟩
  change criticalCoordinateCoefficientValue 11 1 1 1 (0 : Fin 1).val 2 _ = 1
  rw [criticalCoordinateCoefficientValue_eq 1 (by decide) 1 2 (0 : Fin 1)
    (X 0) ((totalDegree_X_le 0).trans (by decide)) (by decide) (by decide)
    (fun z => z[0]?.getD 0) (by intro z; simp only [eval_X, Fin.val_zero])]
  have hdim : Fintype.card (NormalIndex 1 2) = 2 := by simp [NormalIndex]
  have hleading (A : Matrix (NormalIndex 1 2) (NormalIndex 1 2) (ZMod 11)) :
      (A.charpoly.coeff 2).val = 1 := by
    have hdegree := (Matrix.charpoly_natDegree_eq_dim A).trans hdim
    calc
      _ = (A.charpoly.coeff A.charpoly.natDegree).val :=
        congrArg (fun k => (A.charpoly.coeff k).val) hdegree.symm
      _ = 1 := by
        rw [Polynomial.coeff_natDegree, (Matrix.charpoly_monic A).leadingCoeff, ZMod.val_one]
  exact hleading _

example : (fun q : ℕ × ℕ => zeroObjectiveCoefficientValue 19 1 1 q.1 q.2 (fun _ => 0)) ∈
    CountingFunction 9 (encPair encNat encNat) encNat := by
  exact zeroObjectiveCoefficientValue_mem (a := 0) (Decoder.pair Decoder.nat Decoder.nat)
    (.const 19) (.const 1) (.const 1) (by fun_prop) (by fun_prop)
    (CountingFunction.of_polyTime (.const 0))

-- With no variables and zero input, the quotient has rank one and the multiplier is zero.
example : zeroObjectiveCoefficientValue 11 0 1 0 0 (fun _ => 0) = 0 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [zeroObjectiveCoefficientValue_eq 1 (by decide) 0 0 (0 : MvPolynomial (Fin 0) (ZMod 11))
    (by simp) (by decide) (by decide) (fun _ => 0) (by simp)]
  simp [deformedPolynomial, potentialPolynomial, Matrix.charpoly_zero]

-- The retained coordinate of a two-variable source is fixed while the coefficient address varies.
example :
    let C : Controlled (fun _ : ℕ => (X 1 : MvPolynomial (Fin (1 + 1)) ℤ)) encNat 0 :=
      Controlled.coordinate (.const 2) (fun _ => 1) (.const 1)
    C.relativeCoefficientValue (n := fun _ => 1) (m := fun _ => 1) (fun _ => 19)
      (fun _ => 1) (fun _ => 1) id (fun _ => [2]) ∈ CountingFunction 9 encNat encNat := by
  intro C
  exact C.relativeCoefficientValue_mem Decoder.nat (.const 1) (.const 19) (.const 1)
    (.const 1) ComputableInPolyTime.id' (.const [2])

-- The relative polynomial of the empty zero source is the critical-value variable itself.
example :
    let C : Controlled (fun _ : ℕ => (MvPolynomial.C 0 : MvPolynomial (Fin (0 + 0)) ℤ))
        encNat 0 := Controlled.constant (.const 0) (fun _ => 0) (.const 0)
    C.relativeValue (n := fun _ => 0) (m := fun _ => 0) (fun _ => 1) (0, 11, [3]) = 3 := by
  intro C
  rw [C.relativeValue_eq (fun _ => 1) 0 11 [3] (by decide)
    (by change 0 < 11; decide) (by decide) (by simp) (by decide) (by decide)]
  have hresidue : (3 : ZMod 11).val = 3 := by decide
  simp [flattenedRelativeValuePolynomial, relativeValuePolynomial, relativeSource, valuePolynomial,
    deformedPolynomial, potentialPolynomial, Matrix.charpoly_zero, NormalIndex, hresidue]

-- The packaged evaluator has one retained coordinate and the two distinguished slots.
example :
    let C : Controlled (fun _ : ℕ => (X 1 : MvPolynomial (Fin (1 + 1)) ℤ)) encNat 0 :=
      Controlled.coordinate (.const 2) (fun _ => 1) (.const 1)
    let Q : Controlled (n := fun _ => 3) _ encNat 10 :=
      C.relativeValueFamily (n := fun _ => 1) (m := fun _ => 1) Decoder.nat (.const 1) (.const 1)
    Q.evaluate ∈ CountingFunction 10 (encEvaluation encNat) encNat := by
  intro C Q
  exact Q.evaluate_mem

-- At u = 1, the equation for F = X is X² + 1 = 0. The value t = 5 is a root mod 13.
example : (criticalCoordinatePolynomialValue 13 1 1 1 0 5 (fun z => z[0]?.getD 0) :
    ZMod 13) = 0 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let F : MvPolynomial (Fin 1) ℤ := X 0
  let φ := Int.castRingHom (ZMod 13)
  have hF : F.totalDegree ≤ 1 + 1 := (totalDegree_X_le 0).trans (by decide)
  change (criticalCoordinatePolynomialValue 13 1 1 1 (0 : Fin 1).val 5 _ : ZMod 13) = 0
  rw [criticalCoordinatePolynomialValue_cast 1 (by decide) F hF (0 : Fin 1) 1 5
    (by decide) (by decide) (fun z => z[0]?.getD 0)
    (by intro z; simp only [F, eval₂_X, Fin.val_zero]),
    Polynomial.eval₂_eq_eval_map, parametricCoordinatePolynomial_map_eval₂]
  let r := criticalLower 2 (fun _ => 0) ((1 : ℕ) : ZMod 13) (F.map φ)
  have hr (j : Fin 1) : (r j).totalDegree < 2 :=
    criticalLower_degree 2 (by decide) _ _ _ ((totalDegree_map_le φ F).trans hF) j
  have hx (j : Fin 1) : aeval (fun _ => ((5 : ℕ) : ZMod 13)) (r j) = ((5 : ℕ) : ZMod 13) ^ 2 := by
    rw [Fin.eq_zero j]
    simp only [r, F, map_X, criticalLower, zero_pow (by decide : 2 ≠ 0),
      pderiv_X_self, map_sub, aeval_C, mul_one]
    decide
  simpa only [Polynomial.IsRoot.def, aeval_X] using
    isRoot_charpoly_multiplicationMatrix_of_aeval_eq (by decide) r hr
      (X 0) (fun _ => ((5 : ℕ) : ZMod 13)) hx

example : (fun j : ℕ => criticalCoordinateCandidateValue 13 1 1 0 j 5 (fun _ => 0)) ∈
    CountingFunction 11 encNat encNat := by
  apply criticalCoordinateCandidateValue_mem (a := 0) (p := fun _ => 13) (n := fun _ => 1)
    (d := fun _ => 1) (i := fun _ => 0) (j := fun j => j) (t := fun _ => 5) (value := fun _ => 0)
    Decoder.nat (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  exact CountingFunction.of_polyTime (ComputableInPolyTime.const 0)

example : ComputableInPolyTime (fun d : ℕ => coordinateParameterDegreeBound 1 d) encNat encNat :=
  coordinateParameterDegreeBound_polyTime (.const 1) ComputableInPolyTime.id'

-- At u = 0 the critical relation is X² = 0, so the constant coefficient in u is T².
example : (criticalCoordinateCandidateValue 13 1 1 0 0 5 (fun z => z[0]?.getD 0) :
    ZMod 13) = 12 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let F : MvPolynomial (Fin 1) ℤ := X 0
  have hF : F.totalDegree ≤ 1 + 1 := (totalDegree_X_le 0).trans (by decide)
  change (criticalCoordinateCandidateValue 13 1 1 (0 : Fin 1).val 0 5 _ : ZMod 13) = 12
  rw [criticalCoordinateCandidateValue_cast 1 (by decide) F hF (0 : Fin 1) 0 5
    (by decide) (by decide) (by decide) (by decide) (fun z => z[0]?.getD 0)
    (by intro z; simp only [F, eval₂_X, Fin.val_zero])]
  let P := parametricCoordinatePolynomial (by decide : 1 ≤ 2) F hF (0 : Fin 1)
  let φ := Int.castRingHom (ZMod 13)
  let t : ZMod 13 := (5 : ℕ)
  change Polynomial.eval₂RingHom φ t ((Polynomial.Bivariate.swap P).coeff 0) = 12
  rw [← Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_map,
    Polynomial.Bivariate.eval₂_eval₂RingHom_swap, ← Polynomial.eval_map]
  change ((parametricCoordinatePolynomial _ F hF (0 : Fin 1)).map
    (Polynomial.eval₂RingHom φ 0)).eval t = 12
  rw [parametricCoordinatePolynomial_map_eval₂]
  let r := criticalLower 2 (fun _ => 0) (0 : ZMod 13) (F.map φ)
  have hr (j : Fin 1) : (r j).totalDegree < 2 :=
    criticalLower_degree 2 (by decide) _ _ _ ((totalDegree_map_le φ F).trans hF) j
  let M := multiplicationMatrix (by decide : 1 ≤ 2) r hr (X 0)
  have hnil : IsNilpotent M := ⟨2, by
    dsimp only [M]
    rw [← map_pow]
    have hproj : projection 2 r ((X (0 : Fin 1)) ^ 2) = projection 2 r 0 := by
      rw [map_pow, projection_X_pow, map_zero]
      simp [r, criticalLower]
    rw [multiplicationMatrix_eq_of_projection_eq _ r hr hproj, map_zero]⟩
  have hchar := sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil).eq_zero
  have hcard : Fintype.card (NormalIndex 1 2) = 2 := by simp [NormalIndex]
  change M.charpoly.eval t = 12
  rw [hchar, hcard, Polynomial.eval_pow, Polynomial.eval_X]
  decide

-- Index seven is above the deformation-degree bound six and within the field cutoff.
example : (criticalCoordinateCandidateValue 13 1 1 0 7 5 (fun z => z[0]?.getD 0) :
    ZMod 13) = 0 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let F : MvPolynomial (Fin 1) ℤ := X 0
  have hF : F.totalDegree ≤ 1 + 1 := (totalDegree_X_le 0).trans (by decide)
  change (criticalCoordinateCandidateValue 13 1 1 (0 : Fin 1).val 7 5 _ : ZMod 13) = 0
  rw [criticalCoordinateCandidateValue_cast 1 (by decide) F hF (0 : Fin 1) 7 5
    (by decide) (by decide) (by decide) (by decide) (fun z => z[0]?.getD 0)
    (by intro z; simp only [F, eval₂_X, Fin.val_zero])]
  have hdegree := (parametricCoordinatePolynomial_natDegree_swap_le 1 (by decide) F hF
    (0 : Fin 1)).trans_lt (show coordinateParameterDegreeBound 1 1 < 7 by decide)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdegree, Polynomial.eval₂_zero]

-- One bound applies to all deformation coefficients of the characteristic polynomial of X.
example (j : ℕ) :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let P := parametricCoordinatePolynomial (by decide : 1 ≤ 2) F (totalDegree_X_le 0 |>.trans
      (by decide : 1 ≤ 2)) 0
    ((Polynomial.Bivariate.swap P).coeff j).coeffNorm1 ≤
      2 ^ parametricCoordinateCoeffNormExponent 1 2 0 := by
  dsimp only
  refine (Polynomial.coeffNorm1_coeff_swap_le _ j).trans ?_
  exact parametricCoordinatePolynomial_bivariateCoeffNorm1_le (by decide) (X 0) _ (by simp) 0

example : ComputableInPolyTime (fun b => parametricCoordinateCoeffNormExponent 1 2 b)
    encNat encNat :=
  parametricCoordinateCoeffNormExponent_polyTime (.const 1) (.const 2) ComputableInPolyTime.id'

-- A single certificate covers both binary indices for the controlled source F = X.
example :
    (fun w : ℕ × ℕ =>
      let F : MvPolynomial (Fin 1) ℤ := X 0
      let P := parametricCoordinatePolynomial (by decide : 1 ≤ 2) F
        ((totalDegree_X_le 0).trans (by decide)) 0
      (((Polynomial.Bivariate.swap P).coeff w.1).coeff w.2).sign) ∈
        CountingFunction 15 (encPair encNat encNat) encIntBin := by
  let C : Controlled (fun _ : ℕ × ℕ => (X 0 : MvPolynomial (Fin 1) ℤ))
      (encPair encNat encNat) 0 :=
    Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
  exact C.criticalCoordinateCandidateCoefficientSign_mem (d := fun _ => 1)
    (Decoder.pair Decoder.nat Decoder.nat) (fun _ => 0) (fun _ => by decide)
    (fun _ => (totalDegree_X_le 0).trans (by decide)) (.const 1) (.const 0)
    (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.snd _ _)

-- The deformation degree certificate can be used with a varying binary degree parameter.
example :
    (fun d : ℕ =>
      let F : MvPolynomial (Fin 1) ℤ := X 0
      let P := parametricCoordinatePolynomial (by omega : 1 ≤ (d + 1) + 1) F
        ((totalDegree_X_le 0).trans (by omega)) 0
      (Polynomial.Bivariate.swap P).natDegree) ∈
        CountingFunction 18 encNat encNat := by
  let C : Controlled (fun _ : ℕ => (X 0 : MvPolynomial (Fin 1) ℤ)) encNat 0 :=
    Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
  exact C.criticalCoordinateParameterNatDegree_mem (d := fun d => d + 1)
    Decoder.nat (fun _ => 0) (fun _ => by omega)
    (fun _ => (totalDegree_X_le 0).trans (by omega))
    (ComputableInPolyTime.binary_add' ComputableInPolyTime.id' (.const 1)) (.const 0)

-- Value, coefficient and derivative queries use binary inputs and the same level.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let hF : F.totalDegree ≤ 2 := (totalDegree_X_le 0).trans (by decide)
    let C : Controlled (fun _ : ℕ => F) encNat 0 :=
      Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
    let leading := C.criticalCoordinateLeadingValue (d := fun _ => 1) (fun _ => 0) (fun _ => hF)
    let residue :=
      C.criticalCoordinateLeadingCoefficientResidue (d := fun _ => 1) (fun _ => 0) (fun _ => hF)
    let derivative := fun k =>
      C.criticalCoordinateLeadingDerivativeResidue (d := fun _ => 1) (fun _ => 0) (fun _ => hF)
        k 101 k 5
    let P := Polynomial.Bivariate.swap (parametricCoordinatePolynomial (by decide) F hF 0)
    leading ∈ CountingFunction 18 (encPair encNat (encPair encNat encNat)) encNat ∧
      residue ∈ CountingFunction 18 (encPair encNat (encPair encNat encNat)) encNat ∧
      derivative ∈ CountingFunction 18 encNat encNat ∧
      (∀ t : ℕ, (leading (0, 101, t) : ZMod 101) =
        P.leadingCoeff.eval₂ (Int.castRingHom (ZMod 101)) (t : ZMod 101)) ∧
      (residue (0, 101, 3) : ZMod 101) = 0 ∧ (derivative 3 : ZMod 101) = 0 := by
  intro F hF C leading residue derivative P
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  have hdeg : P.leadingCoeff.natDegree < 3 := by
    rw [← Polynomial.coeff_natDegree]
    refine (Polynomial.Bivariate.natDegree_coeff_le_natDegree_swap _ _).trans_lt ?_
    rw [show Polynomial.Bivariate.swap P = parametricCoordinatePolynomial (by decide) F hF 0
      from Polynomial.Bivariate.swap_swap_apply _, parametricCoordinatePolynomial_natDegree]
    decide
  refine ⟨C.criticalCoordinateLeadingValue_mem Decoder.nat (fun _ => 0) (fun _ => by decide)
    (fun _ => hF) (.const 1) (.const 0),
    C.criticalCoordinateLeadingCoefficientResidue_mem Decoder.nat (fun _ => 0)
      (fun _ => by decide) (fun _ => hF) (.const 1) (.const 0),
    C.criticalCoordinateLeadingDerivativeResidue_mem Decoder.nat (fun _ => 0)
      (fun _ => by decide) (fun _ => hF) (.const 1) (.const 0) (.const 101)
      ComputableInPolyTime.id' (.const 5), ?_, ?_, ?_⟩
  · intro t
    exact C.criticalCoordinateLeadingValue_cast (fun _ => 0) (fun _ => hF) 0 (by decide) t
      (by decide) (by decide) (by decide) (by decide)
  -- The exponent is above the degree bound and below the interpolation cutoff.
  · rw [C.criticalCoordinateLeadingCoefficientResidue_cast (fun _ => 0) (fun _ => hF) 0
      (by decide) 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, Int.cast_zero]
  · rw [C.criticalCoordinateLeadingDerivativeResidue_cast (fun _ => 0) (fun _ => hF) 3
      (by decide) 3 5 (by decide) (by decide) (by decide) (by decide),
      Polynomial.iterate_derivative_eq_zero hdeg, Polynomial.eval₂_zero]

-- A varying binary evaluation point and a negative target exercise the fingerprint query.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let hF : F.totalDegree ≤ 2 := (totalDegree_X_le 0).trans (by decide)
    let C : Controlled (fun _ : ℕ => F) encNat 0 :=
      Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
    let residue := fun z =>
      C.criticalCoordinateFingerprintLabelResidue (d := fun _ => 1) (fun _ => 0)
        (fun _ => hF) z 101 5 2 z (-1)
    let Q := (Polynomial.Bivariate.swap
      (parametricCoordinatePolynomial (by decide) F hF 0)).leadingCoeff
    residue ∈ CountingFunction 20 encNat encNat ∧
      ∀ z : ℕ, (residue z : ZMod 101) =
        (Polynomial.fingerprintIntegerRootLabel Q 1 2
          (parametricCoordinateCoeffNormExponent 1 2 (C.massExponent z)) 5 2 (-1)).eval₂
            (Int.castRingHom (ZMod 101)) (z : ZMod 101) := by
  intro F hF C residue Q
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  refine ⟨C.criticalCoordinateFingerprintLabelResidue_mem Decoder.nat (fun _ => 0)
    (fun _ => by decide) (fun _ => hF) (.const 1) (.const 0) (.const 101) (.const 5)
    (.const 2) ComputableInPolyTime.id' (.const (-1)), ?_⟩
  intro z
  exact C.criticalCoordinateFingerprintLabelResidue_cast (fun _ => 0) (fun _ => hF) z
    (by decide) 5 2 z (by decide) (-1) (by change 0 < 101; decide)
    (by decide) (by decide) (by decide)

-- The assembled family exposes the counting certificate with ordinary imports.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let C : Controlled (fun _ : ℕ => F) encNat 0 :=
      Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
    let labels := C.criticalCoordinateFingerprintLabels (d := fun _ => 1) Decoder.nat
      (fun _ => 0) (fun _ => by decide) (fun _ => (totalDegree_X_le 0).trans (by decide))
      (.const 1) (.const 0) (.const 5) (.const 2) (.const (-1)) (fun _ => by decide)
      (.const 7) (fun _ => by decide) (fun _ => by decide)
    labels.evaluate ∈ CountingFunction 20 (encEvaluation encNat) encNat := by
  intro F C labels
  exact labels.evaluate_mem

-- A shared word represents different signed targets at two coordinate addresses.
example : ∃ word : List Bool, word.length = coordinateFingerprintWitnessWidth 2 2 ∧
    decodeCoordinateFingerprint 2 word 0 = ⟨3, 2, -5⟩ ∧
    decodeCoordinateFingerprint 2 word 1 = ⟨5, 4, 9⟩ := by
  let f : Fin 2 → CoordinateFingerprint := fun i => if i = 0 then ⟨3, 2, -5⟩ else ⟨5, 4, 9⟩
  have hf (i : Fin 2) : (f i).Bounded 2 := by
    fin_cases i <;> unfold CoordinateFingerprint.Bounded <;> decide
  obtain ⟨word, hw, hd⟩ := exists_coordinateFingerprintWitness f hf
  exact ⟨word, hw, hd 0, hd 1⟩

-- The word and address are evaluator inputs, but the bounds are shared by all addresses.
example (w : List Bool) (j : ℕ) :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let C : Controlled (fun _ : List Bool => F) encBits 0 :=
      Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
    let labels := C.wordCoordinateFingerprintTests (d := fun _ => 1) Decoder.bits
      (fun _ => by decide) (fun _ => by decide) (fun _ => (totalDegree_X_le 0).trans (by decide))
      (.const 1) id ComputableInPolyTime.id'
    labels.evaluate ∈ CountingFunction 20 (encEvaluation (encPair encBits encNat)) encNat ∧
      labels.degreeBound (w, j) = labels.degreeBound (w, 0) ∧
      labels.massExponent (w, j) = labels.massExponent (w, 0) ∧
      labels.cutoff (w, j) = labels.cutoff (w, 0) := by
  intro F C labels
  exact ⟨labels.evaluate_mem, C.wordCoordinateFingerprintTests_bounds_eq
    (n := fun _ : List Bool => 1) (d := fun _ => 1) Decoder.bits
    (fun _ => by decide) (fun _ => by decide) (fun _ => (totalDegree_X_le 0).trans (by decide))
    (.const 1) id ComputableInPolyTime.id' w j⟩

-- Lifting the single variable to coordinate 1 reads the second input with zero padding.
example (w p : ℕ) (z : List ℕ) (hp : p.Prime) :
    let C : Controlled (fun _ : ℕ => (X 0 : MvPolynomial (Fin 1) ℤ)) encNat 0 :=
      Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
    let lifted := C.onCoordinate (n := fun _ => 2) (.const 2) (fun _ => 1) (.const 1)
    lifted.evaluate (w, p, z) = z.getD 1 0 % p := by
  intro C lifted
  have hcut : lifted.cutoff w < p := by
    simpa only [lifted, Controlled.cutoff_onCoordinate, C, Controlled.coordinate] using hp.pos
  rw [lifted.evaluate_eq w p z hp hcut]
  simp only [evaluation, MvPolynomial.rename_X, MvPolynomial.eval₂_X, ZMod.val_natCast,
    List.getD_eq_getElem?_getD, Fin.val_one]

-- Address 3 selects coordinate 1 of the two-variable source.
example (w p : ℕ) (z : List ℕ) (hp : p.Prime) :
    let F : MvPolynomial (Fin 2) ℤ := X 0
    let hF : F.totalDegree ≤ 2 := (totalDegree_X_le 0).trans (by decide)
    let C : Controlled (fun _ : ℕ => F) encNat 0 :=
      Controlled.coordinate (.const 2) (fun _ => 0) (.const 0)
    let equations := C.indexedCoordinateEquations (d := fun _ => 1) Decoder.nat
      (fun _ => by decide) (fun _ => by decide) (fun _ => hF) (.const 1)
    let Q := (Polynomial.Bivariate.swap (parametricCoordinatePolynomial
      (by decide : 1 ≤ 2) F hF 1)).leadingCoeff
    equations.evaluate ∈ CountingFunction 18 (encEvaluation (encPair encNat encNat)) encNat ∧
      (equations.cutoff (w, 3) < p → equations.evaluate ((w, 3), p, z) =
        (Q.eval₂ (Int.castRingHom (ZMod p)) (z.getD 1 0 : ZMod p)).val) := by
  intro F hF C equations Q
  refine ⟨equations.evaluate_mem, fun hcut => ?_⟩
  rw [equations.evaluate_eq (w, 3) p z hp hcut]
  simp only [evaluation, eval₂_indexedCoordinateEquation]
  rw [List.getD_eq_getElem?_getD]
  rfl

-- The cutoff at any binary address suffices to evaluate the source at row zero.
example (w j p : ℕ) (z : List ℕ) (hp : p.Prime) :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let C : Controlled (fun _ : ℕ => F) encNat 0 :=
      Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
    let rows := C.selectionEquations (d := fun _ => 1) Decoder.nat
      (fun _ => by decide) (fun _ => by decide) (fun _ => (totalDegree_X_le 0).trans (by decide))
      (.const 1)
    rows.evaluate ∈ CountingFunction 18 (encEvaluation (encPair encNat encNat)) encNat ∧
      (rows.cutoff (w, j) < p → rows.evaluate ((w, 0), p, z) = z.getD 0 0 % p) := by
  intro F C rows
  refine ⟨rows.evaluate_mem, fun hcut => ?_⟩
  obtain ⟨_, _, hc⟩ := C.selectionEquations_bounds_eq
    (n := fun _ : ℕ => 1) (d := fun _ => 1) Decoder.nat
    (fun _ => by decide) (fun _ => by decide) (fun _ => (totalDegree_X_le 0).trans (by decide))
    (.const 1) w j
  rw [rows.evaluate_eq (w, 0) p z hp (hc ▸ hcut), selectionEquation_zero]
  simp only [F, evaluation, MvPolynomial.eval₂_X, ZMod.val_natCast,
    List.getD_eq_getElem?_getD, Fin.val_zero]

-- Squaring the two addressed rows and adding their values costs one counting level.
example (w p : ℕ) (z : List ℕ) (hp : p.Prime) :
    let C : Controlled (fun _ : ℕ × ℕ => (X 0 : MvPolynomial (Fin 1) ℤ))
        (encPair encNat encNat) 0 :=
      Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
    let squares := C.sumSquares Decoder.nat (.const 1) (fun _ => 2) (fun _ => 1)
      (fun _ => 0) (fun _ => 0) (.const 2) (.const 1) (.const 0) (.const 0)
      (fun _ _ _ => totalDegree_X_le 0) (fun _ _ _ => by simp) (fun _ _ _ => le_rfl)
    squares.evaluate ∈ CountingFunction 1 (encEvaluation encNat) encNat ∧
      (squares.cutoff w < p →
        squares.evaluate (w, p, z) = (z.getD 0 0 ^ 2 + z.getD 0 0 ^ 2) % p) := by
  intro C squares
  refine ⟨squares.evaluate_mem, fun hcut => ?_⟩
  rw [squares.evaluate_eq w p z hp hcut]
  simp only [evaluation, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
    Fin.val_zero, List.getD_eq_getElem?_getD]
  rw [Finset.sum_const, Finset.card_range, two_nsmul, ← Nat.cast_pow, ← Nat.cast_add,
    ZMod.val_natCast]

-- The in-range row reads the appended coordinate. Extra list entries do not extend the arity.
example (w p : ℕ) (z : List ℕ) (hp : p.Prime) :
    let CQ : Controlled (fun _ : ℕ × ℕ => (X 0 : MvPolynomial (Fin 1) ℤ))
        (encPair encNat encNat) 0 :=
      Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
    let rows := CQ.positivityEquations (n := fun _ : ℕ => 1) (fun _ => 1) (.const 1)
    rows.evaluate ∈ CountingFunction 0 (encEvaluation (encPair encNat encNat)) encNat ∧
      rows.evaluate ((w, 0), p, z) =
        ((z.getD 0 0 : ZMod p) * (z.getD 1 0 : ZMod p) ^ 2 - 1).val ∧
      rows.evaluate ((w, 2), p, z) = (-1 : ZMod p).val := by
  intro CQ rows
  have hcut (j : ℕ) : rows.cutoff (w, j) < p := by
    simpa only [rows, Controlled.cutoff_positivityEquations, CQ, Controlled.coordinate]
      using hp.pos
  refine ⟨rows.evaluate_mem, ?_, ?_⟩
  · rw [rows.evaluate_eq (w, 0) p z hp (hcut 0), positivityEquation_of_lt _ (by decide : 0 < 1)]
    simp [evaluation, List.getD_eq_getElem?_getD, sub_eq_add_neg]
  · rw [rows.evaluate_eq (w, 2) p z hp (hcut 2), positivityEquation_of_le _ (by decide : 1 ≤ 2)]
    simp [evaluation]

-- The system x = 0, 1 > 0 has a real zero and evaluates both rows modulo a prime.
example (w p : ℕ) (z : List ℕ) (hp : p.Prime) :
    let CP : Controlled (fun _ : ℕ × ℕ => (X 0 : MvPolynomial (Fin 1) ℤ))
        (encPair encNat encNat) 0 :=
      Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)
    let CQ : Controlled (fun _ : ℕ × ℕ => (1 : MvPolynomial (Fin 1) ℤ))
        (encPair encNat encNat) 0 :=
      Controlled.constant (.const 1) (fun _ => 1) (.const 1)
    let system := CP.indexedFeasibility (n := fun _ : ℕ => 1) CQ Decoder.nat
      (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 0)
      (.const 1) (.const 1) (.const 1) (.const 0) (.const 0)
      (fun _ _ _ => totalDegree_X_le 0) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
    system.evaluate ∈ CountingFunction 1 (encEvaluation encNat) encNat ∧
      (system.cutoff w < p → system.evaluate (w, p, z) =
        ((z.getD 0 0 : ZMod p) ^ 2 + ((z.getD 1 0 : ZMod p) ^ 2 - 1) ^ 2).val) ∧
      ∃ z : Fin 2 → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) z
        (indexedFeasibilityPolynomial (fun _ : ℕ => (X 0 : MvPolynomial (Fin 1) ℤ))
          (fun _ => 1) 1 1) = 0 := by
  intro CP CQ system
  refine ⟨system.evaluate_mem, fun hcut => ?_, ?_⟩
  · rw [system.evaluate_eq w p z hp hcut, evaluation,
      eval₂_indexedFeasibilityPolynomial (n := 1) _ (fun _ => X 0) (fun _ => 1) 1 1]
    simp [List.getD_eq_getElem?_getD]
  · apply (exists_indexedFeasibilityPolynomial_zero_iff (n := 1)
      (fun _ => X 0) (fun _ => 1) 1 1).mpr
    exact ⟨fun _ => 0, fun _ _ => by simp, fun _ _ => by simp⟩

-- The system x = 0, x > 0 has no real zero even with an auxiliary coordinate.
example :
    ¬ ∃ z : Fin 2 → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) z
      (indexedFeasibilityPolynomial (fun _ : ℕ => (X 0 : MvPolynomial (Fin 1) ℤ))
        (fun _ => X 0) 1 1) = 0 := by
  intro h
  obtain ⟨x, he, hq⟩ :=
    (exists_indexedFeasibilityPolynomial_zero_iff (n := 1) (fun _ => X 0) (fun _ => X 0) 1 1).mp h
  exact (ne_of_gt (hq 0 (by decide))) (he 0 (by decide))

-- The selection system has a level-21 evaluator for every word.
-- A nonzero constant source cannot gain a zero from its fingerprint or auxiliary variables.
example (word : List Bool) :
    let F : MvPolynomial (Fin 1) ℤ := 1
    let hF : F.totalDegree ≤ 2 := by simp [F]
    let C : Controlled (fun _ : List Bool => F) encBits 0 :=
      Controlled.constant (.const 1) (fun _ => 1) (.const 1)
    let system := C.selectionFeasibility (n := fun _ : List Bool => 1) (d := fun _ => 1)
      Decoder.bits (fun _ => by decide) (fun _ => by decide) (fun _ => hF) (.const 1)
      id ComputableInPolyTime.id'
    system.evaluate ∈ CountingFunction 21 (encEvaluation encBits) encNat ∧
      ¬ ∃ z : Fin 2 → ℝ,
        MvPolynomial.eval₂ (Int.castRingHom ℝ) z
          (selectionFeasibilityPolynomial (d := 1) F hF (C.massExponent word) (by decide) word)
          = 0 := by
  intro F hF C system
  refine ⟨system.evaluate_mem, fun hz => ?_⟩
  obtain ⟨_, hzero, _, _⟩ :=
    (exists_selectionFeasibilityPolynomial_zero_iff (d := 1) F hF
      (C.massExponent word) (by decide) word).mp hz
  simp [F] at hzero

-- The first parameter coordinate is unused, and the two remaining blocks retain their values.
example :
    let P : MvPolynomial (Fin (2 + 1)) ℤ := X (Fin.castAdd 1 1) + 2 * X (Fin.natAdd 2 0)
    let c (i : Fin (1 + 1)) : ℤ := if i = 0 then 99 else 3
    let z (i : Fin 2) : ℤ := if i = 0 then 10 else 20
    MvPolynomial.eval₂ (RingHom.id ℤ) (Fin.addCases c z)
      (counterexamplePolynomial (n := 2) (m := 1) P) = 26 := by
  intro P c z
  rw [eval₂_counterexamplePolynomial]
  norm_num [P, c, z, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
  decide

-- The reordered evaluator is available at the original counting level.
example (P : MvPolynomial (Fin (2 + 1)) ℤ) (a : ℕ)
    (C : Controlled (fun _ : List Bool => P) encBits a) :
    (C.counterexampleOrder (n := fun _ => 2) (m := fun _ => 1) (.const 2) (.const 1)).evaluate ∈
      CountingFunction a (encEvaluation encBits) encNat :=
  (C.counterexampleOrder (n := fun _ => 2) (m := fun _ => 1) (.const 2) (.const 1)).evaluate_mem

-- The penalty becomes a power of the value, and the parameter retains its own coordinate.
example :
    let P : MvPolynomial (Fin (1 + 2)) ℤ := X (Fin.succ 0) + X (Fin.succ (Fin.succ 0))
    eval₂ (RingHom.id ℤ) (Fin.cons 2 (fun _ => 5)) (MvPolynomial.powerSection 3 P) = 13 := by
  intro P
  rw [eval₂_powerSection]
  simp only [P, eval₂_add, eval₂_X, Fin.cons_succ, Fin.cons_zero]
  norm_num

-- Taking the fixed-power section of a relative family drops an arity slot at the same level.
example (P : MvPolynomial (Fin (1 + 1)) ℤ)
    (C : Controlled (fun _ : ℕ => P) encNat 0) :
    let Q : Controlled (n := fun _ => 2) _ encNat 10 :=
      C.relativeValueSection (n := fun _ => 1) (m := fun _ => 1) Decoder.nat (.const 1) (.const 1)
    Q.evaluate ∈ CountingFunction 10 (encEvaluation encNat) encNat := by
  intro Q
  exact Q.evaluate_mem

-- The degree-two coefficient survives specialization to a finite field, including at zero.
example (x : ZMod 7) :
    let F : MvPolynomial (Fin (1 + 1)) ℤ := X 1 ^ 2
    let hF : F.totalDegree ≤ 2 := (totalDegree_pow _ _).trans (by simp)
    let Q := specializedRelativeValueSection (ell := 2) (n := 1) (m := 1) (by decide)
      F hF (fun _ => x)
    Q.coeff 2 = 1 ∧ Q ≠ 0 := by
  intro F hF Q
  exact ⟨coeff_specializedRelativeValueSection _ F hF _, specializedRelativeValueSection_ne_zero
    _ F hF _⟩

-- The test x * v vanishes only at v = 0 and has both eventual signs as x varies.
example : IsClopen {x : {x : ℝ // x ≠ 0} | 0 < x.val} := by
  let P : {x : ℝ // x ≠ 0} → Polynomial ℝ := fun _ => Polynomial.X
  refine Polynomial.eventualSign_isClopen_of_fixed_degree P 1
    (fun _ => continuous_const) (fun _ => by simp [P]) (fun _ => by simp [P])
    (fun x v => x.val * v) ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)
    (fun x => 0 < x.val) ?_ ?_ ?_
  · intro x v hz
    have hv : v = 0 := (mul_eq_zero.mp hz).resolve_left x.property
    simp [P, hv]
  · intro x hx
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with v hv
    exact mul_pos hx hv
  · intro x hx
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with v hv
    exact mul_neg_of_neg_of_pos (lt_of_le_of_ne (le_of_not_gt hx) x.property) hv

-- The root branch of the relation u - t = 0 is t = v² at parameter u = v².
example : ∀ᶠ v : ℝ in Filter.atTop, v < v ^ 2 := by
  let P : Polynomial (Polynomial ℝ) := Polynomial.X - Polynomial.C Polynomial.X
  have hP : P ≠ 0 := by
    intro hz
    simpa [P] using congrArg (fun Q : Polynomial (Polynomial ℝ) => Q.coeff 1) hz
  have hdegree (j : ℕ) : (P.coeff j).natDegree ≤ 1 := by
    by_cases h0 : j = 0
    · subst j
      simp [P]
    by_cases h1 : j = 1
    · subst j
      simp [P]
    · simp [P, Polynomial.coeff_X, Polynomial.coeff_C, h0, Ne.symm h1]
  refine Polynomial.eventually_lt_of_eval₂_pow_eq_zero P hP hdegree Filter.tendsto_id
    (Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)) ?_
  exact Filter.Eventually.of_forall fun v => by simp [P]

-- For the constant input r², the minimum varies jointly and diverges exactly when r is nonzero.
example :
    let F (r : ℝ) : MvPolynomial (Fin 1) ℝ := C (r ^ 2)
    let a : Fin 1 → ℝ := fun _ => 0
    Continuous (fun q : ℝ × Set.Ici (0 : ℝ) => criticalMinimumValue 1 a (F q.1) q.2.val) ∧
      ∀ r, r ≠ 0 ↔ Filter.Tendsto (criticalMinimumValue 1 a (F r)) Filter.atTop Filter.atTop := by
  intro F a
  have hFn (r : ℝ) (z : Fin 1 → ℝ) : 0 ≤ eval z (F r) := by simp [F, sq_nonneg]
  refine ⟨continuous_criticalMinimumValue (by decide) (by decide) a (fun _ => le_rfl)
    F ?_ hFn, ?_⟩
  · simp only [F, eval_C]
    fun_prop
  · intro r
    simpa [F] using (not_exists_zero_iff_tendsto_criticalMinimumValue
      (by decide : 1 ≤ 1) (by decide) a (fun _ => le_rfl) (F r) (hFn r))

-- For the input r², the degree pieces containing 0 and 1 realize opposite fiber cases.
example :
    let P : MvPolynomial (Fin (1 + 1)) ℤ := X (Fin.natAdd 1 0) ^ 2
    let hP : P.totalDegree ≤ 3 := (totalDegree_pow _ _).trans (by simp)
    let Q (r : ℝ) := specializedRelativeValueSection (n := 1) (m := 1) (ell := 3) (by decide)
      P hP (fun _ => r)
    let Piece (k : ℕ) := {r : ℝ // (Q r).natDegree ≤ k ∧ (Q r).coeff k ≠ 0}
    let emptyFibers (k : ℕ) : Set (Piece k) := {r | ¬∃ z : Fin 1 → ℝ,
      eval₂ (Int.castRingHom ℝ) (Fin.addCases z (fun _ : Fin 1 => r.val)) P = 0}
    (∀ k, IsClopen (emptyFibers k)) ∧
      (∃ r : Piece (Q 0).natDegree, r.val = 0 ∧ r ∉ emptyFibers _) ∧
      (∃ r : Piece (Q 1).natDegree, r.val = 1 ∧ r ∈ emptyFibers _) := by
  intro P hP Q Piece emptyFibers
  have heval (r : ℝ) (z : Fin 1 → ℝ) :
      eval₂ (Int.castRingHom ℝ) (Fin.addCases z (fun _ : Fin 1 => r)) P = r ^ 2 := by
    simp only [P, eval₂_pow, eval₂_X, Fin.addCases_right]
  let atDegree (r : ℝ) : Piece (Q r).natDegree :=
    ⟨r, le_rfl, by
      change (Q r).leadingCoeff ≠ 0
      exact Polynomial.leadingCoeff_ne_zero.mpr
        (specializedRelativeValueSection_ne_zero (n := 1) (m := 1) (by decide) P hP (fun _ => r))⟩
  refine ⟨fun k => ?_, ⟨atDegree 0, rfl, ?_⟩, ⟨atDegree 1, rfl, ?_⟩⟩
  · exact isClopen_relative_emptyFibers_of_fixed_degree (by decide) (by decide) P hP
      (fun (r : Piece k) (_ : Fin 1) => r.val) (continuous_pi fun _ => continuous_subtype_val)
      (fun r z => by rw [heval]; exact sq_nonneg _) k
      (fun r => r.property.1) (fun r => r.property.2)
  · intro h
    exact h ⟨0, by rw [heval]; norm_num [atDegree]⟩
  · rintro ⟨z, hz⟩
    rw [heval] at hz
    norm_num [atDegree] at hz

end CslibFrontierTests.RealAlgebraicCriticalEvaluation
