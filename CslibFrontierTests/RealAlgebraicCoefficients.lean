/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (finite-field coefficient and controlled-access regression tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledCoefficients
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledSigns
import CslibFrontier.Computability.Complexity.RealAlgebraic.CoefficientEvaluation
import CslibFrontier.Computability.Complexity.RealAlgebraic.FormulaGateCoefficientEvaluation
import CslibFrontier.Computability.Complexity.RealAlgebraic.FormulaGateCoefficientSign
import CslibFrontier.Computability.Complexity.RealAlgebraic.FormulaGateCoordinateEvaluation
import Mathlib.Tactic.FinCases

/-! Extraction covers zero variables, absent coefficients, mixed terms and actual certificates. -/

public section
namespace CslibFrontierTests.RealAlgebraicCoefficients

open Cslib.Complexity Cslib.Complexity.RealAlgebraic Turing.MultiTapeTM MvPolynomial

-- A zero-variable grid has one empty tuple, rather than no tuples.
example : multivariateCoefficientResidue 5 0 [] (fun _ => 3) = 3 := by rfl

-- The unary extractor recovers an ordinary nonzero coefficient and an index above the degree.
example : coefficientResidue 5 1 (fun z => (2 * z + 3) % 5) = 2 := by rfl
example : coefficientResidue 5 3 (fun z => (2 * z + 3) % 5) = 0 := by rfl

-- Zero coordinate degrees allow radix one and the smallest prime.
open Cslib.Logic.RealArithmetic in
example (i j : ℕ) :
    formulaWordGateCoefficientResidue [] 0 2 (formulaWordGateKroneckerRadix [] 0)
      i j (fun _ => []) =
    ((((formulaWordGatePolynomial [] 0 (fun _ => 0)).coeff j).coeff i : ℤ) : ZMod 2).val := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨hradix, hdegree⟩ := formulaWordGateCoefficientPrimeCutoff_bounds [] 0 (fun _ => 0)
    (inner := 0) (outer := 0) (p := 2) (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)
    (by decide)
  exact formulaWordGateCoefficientResidue_eq_val [] 0 (fun _ => 0) i j (fun _ => [])
    hradix hdegree (fun _ _ k => Fin.elim0 k)

-- The sign certificate accepts a coordinate evaluator implemented by zero padding.
open Cslib.Logic.RealArithmetic in
example (a : ℕ) :
    (fun word : List Bool => (((formulaWordGatePolynomial word 0 (fun _ => 0)).coeff 0).coeff
      0).sign) ∈ CountingFunction (max (a + 1) 5 + 3) encBits encIntBin := by
  exact formulaWordGateCoefficientSign_mem (a := a) Decoder.bits (fun _ _ => 0)
    (inner := fun _ => 0) (outer := fun _ => 0) (massExponent := fun _ => 0)
    (pointCutoff := fun _ => 0) (point := fun _ => [])
    .id' (.const 0) (.const 0) (.const 0) (.const 0) (.const 0) (.const 0) (.const 0)
    (CountingFunction.of_polyTime (.const [])) (by simp) (by simp) (by simp) (by simp)

-- Radix eighteen gives the distinct field values two and four modulo five.
example : (formulaWordGateKroneckerCoordinates (List.replicate 17 false) () 5 2 1
    (fun q => q.innerValue + 2 * q.outerValue + q.index)).take 2 = [0, 1] := rfl

-- Defaulting absent exponent entries to zero selects the constant term.
example : multivariateCoefficientResidue 5 1 [] (fun z =>
    (2 * z[0]?.getD 0 + 3) % 5) = 3 := by rfl

/-- An actual controlled two-variable family with a mixed term and negative constant. -/
noncomputable def mixed :
    Controlled (fun _ : List Bool => X (0 : Fin 2) * X (1 : Fin 2) + C (-2)) encBits 0 :=
  ((Controlled.coordinate (.const 2) (fun _ => (0 : Fin 2)) (.const 0)).mul
    (Controlled.coordinate (.const 2) (fun _ => (1 : Fin 2)) (.const 1))).add
      (Controlled.constant (.const 2) (fun _ => -2) (.const (-2)))

private noncomputable def exponent : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

private theorem exponent_code (_w : List Bool) (i : Fin 2) :
    ([1, 1] : List ℕ)[i.val]?.getD 0 = exponent i := by
  fin_cases i <;> simp [exponent]

-- Certificate construction is uniform; neither polynomial coefficients nor a grid are inputs.
example : IntegerResidueAccess.InCountingFunction
    (mixed.coefficientAccess (fun _ => exponent) (fun _ => [1, 1]) exponent_code) 1 encBits :=
  mixed.coefficientAccess_mem Decoder.bits (fun _ => exponent)
    (ComputableInPolyTime.const [1, 1]) exponent_code

example : (fun _ : List Bool =>
    ((X (0 : Fin 2) * X (1 : Fin 2) + C (-2) : MvPolynomial (Fin 2) ℤ).coeff
      exponent).sign) ∈ CountingFunction 8 encBits encIntBin := by
  exact mixed.coefficientSign_mem Decoder.bits (fun _ => exponent)
    (ComputableInPolyTime.const [1, 1]) exponent_code

/-- A one-variable constant family exercises an address-independent admissible prime domain. -/
noncomputable def constantThree :
    Controlled (fun _ : List Bool => C 3 : List Bool → MvPolynomial (Fin 1) ℤ) encBits 0 :=
  Controlled.constant (.const 1) (fun _ => 3) (.const 3)

private theorem zero_code (_w : List Bool) (i : Fin 1) :
    ([0] : List ℕ)[i.val]?.getD 0 = (0 : Fin 1 →₀ ℕ) i := by
  fin_cases i
  simp

private theorem surplus_code (_w : List Bool) (i : Fin 1) :
    ([0, 9] : List ℕ)[i.val]?.getD 0 = (0 : Fin 1 →₀ ℕ) i := by
  fin_cases i
  simp

private theorem missing_code (_w : List Bool) (i : Fin 1) :
    ([] : List ℕ)[i.val]?.getD 0 = (0 : Fin 1 →₀ ℕ) i := by
  simp

private theorem above_code (_w : List Bool) (i : Fin 1) :
    ([1] : List ℕ)[i.val]?.getD 0 = (Finsupp.single 0 1 : Fin 1 →₀ ℕ) i := by
  fin_cases i
  simp

-- Every address has the same prime cutoff, including a list with an unused large entry.
example (w : List Bool) : constantThree.coefficientCutoff w = 1 := rfl

example (w : List Bool) (p : ℕ) :
    (constantThree.coefficientAccess (fun _ => 0) (fun _ => [0]) zero_code).admissible w p ↔
      (constantThree.coefficientAccess (fun _ => 0) (fun _ => [0, 9]) surplus_code).admissible
        w p := Iff.rfl

example (w : List Bool) :
    (constantThree.coefficientAccess (fun _ => 0) (fun _ => [0]) zero_code).admissible w 5 :=
  ⟨by decide, by change 1 < 5; decide⟩

example (w : List Bool) :
    (constantThree.coefficientAccess (fun _ => 0) (fun _ => [0, 9]) surplus_code).admissible
      w 5 := ⟨by decide, by change 1 < 5; decide⟩

example (w : List Bool) :
    (constantThree.coefficientAccess (fun _ => 0) (fun _ => [0]) zero_code).residue (w, 5) = 3 := by
  have h := (constantThree.coefficientAccess (fun _ => 0) (fun _ => [0]) zero_code).residue_eq
    w 5 ⟨by decide, by change 1 < 5; decide⟩
  simpa [coeff_C] using h

example (w : List Bool) :
    (constantThree.coefficientAccess (fun _ => 0) (fun _ => [0, 9]) surplus_code).residue
      (w, 5) = 3 := by
  have h :=
    (constantThree.coefficientAccess (fun _ => 0) (fun _ => [0, 9]) surplus_code).residue_eq
      w 5 ⟨by decide, by change 1 < 5; decide⟩
  simpa [coeff_C] using h

-- Padding a missing coordinate with zero still selects the constant term.
example (w : List Bool) :
    (constantThree.coefficientAccess (fun _ => 0) (fun _ => []) missing_code).residue
      (w, 5) = 3 := by
  have h := (constantThree.coefficientAccess (fun _ => 0) (fun _ => []) missing_code).residue_eq
    w 5 ⟨by decide, by change 1 < 5; decide⟩
  simpa [coeff_C] using h

-- An actual exponent above the degree bound takes the total zero branch before any grid sum.
example (w : List Bool) :
    (constantThree.coefficientAccess
      (fun _ => Finsupp.single 0 1) (fun _ => [1]) above_code).residue
      (w, 5) = 0 := rfl

/-- A zero-variable family uses its source evaluator directly for integer signs. -/
noncomputable def integerFamily :
    Controlled (fun _ : List Bool => C (-37) : List Bool → MvPolynomial (Fin 0) ℤ) encBits 0 :=
  Controlled.constant (.const 0) (fun _ => -37) (.const (-37))

example : (fun _ : List Bool => (-37 : ℤ).sign) ∈ CountingFunction 8 encBits encIntBin := by
  simpa [coeff_C] using integerFamily.sign_mem Decoder.bits

end CslibFrontierTests.RealAlgebraicCoefficients
