/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.MachineLearning.SingularLearning.ModularAddition.Problem

/-!
# Tests for the modular-addition network and the statement of open problem MAIS-O6

Checks for `CslibFrontier/MachineLearning/SingularLearning/ModularAddition/`:

* the first non-vacuous case of the problem, `p = 5` with nine neurons: the Fourier fit has
  nine neurons and is an exact fit, and the ball of the problem contains an exact fit of
  smallest local learning coefficient;
* a neuron with zero output vector is not active, whatever its tables;
* at `p = 5` the frequency of a single-frequency neuron may be taken to be `0`, `1` or `2`;
* the problem at its intended parameters holds for `p = 3`, where the direct form of a
  refutation therefore never applies.
-/

public section

namespace CslibFrontierTests.ModularAddition

open Cslib.MachineLearning Cslib.MachineLearning.ModularAddition

/-- For `p = 5` the Fourier fit has nine neurons. -/
example : Fintype.card (FourierIndex 5) = 9 := card_fourierIndex (by decide)

/-- For `p = 5` the Fourier fit is an exact fit. -/
example : IsExactFit (fourierFit 5) := isExactFit_fourierFit (by decide)

/-- The first non-vacuous case is not vacuous: at `p = 5` with nine neurons the ball of the
problem contains an exact fit of smallest local learning coefficient. -/
example : ∃ w ∈ exactFitsInBall 5 9 (fourierRadius 5),
    IsMinOn (learningCoeff loss) (exactFitsInBall 5 9 (fourierRadius 5)) w :=
  exists_isMinOn_exactFitsInBall (by decide) (by norm_num)

/-- A neuron with zero output vector is not active, whatever its tables. -/
example (l r : Fin 2 → ZMod 5 → ℝ) (j : Fin 2) : ¬ IsActive (Params.mk l r 0) j :=
  (not_isActive_iff _ j).2 (Or.inl rfl)

/-- A neuron with a nonzero output vector and tables that are not opposite constants is
active. -/
example : IsActive (Params.mk (fun (_ : Fin 1) (_ : ZMod 5) => (1 : ℝ)) (fun _ _ => 1)
    (fun _ _ => 1)) 0 :=
  ⟨0, 0, 0, by norm_num [contribution]⟩

/-- At `p = 5` the frequency of a single-frequency neuron may be taken at most `2`. -/
example (w : Params 5 (Fin 9)) (j : Fin 9) (h : IsSingleFrequency w j) :
    ∃ k ≤ 2, left w j ∈ freqSpace 5 k ∧ right w j ∈ freqSpace 5 k :=
  (isSingleFrequency_iff_exists_le (by decide) w j).1 h

/-- The direct form of a refutation never applies at `p = 3`: there no exact fit of smallest
coefficient has an active neuron that is not of single-frequency form. -/
example (H : ℕ) (R : ℝ) (w : Params 3 (Fin H)) (hw : w ∈ exactFitsInBall 3 H R)
    (hmin : IsMinOn (learningCoeff loss) (exactFitsInBall 3 H R) w) (j : Fin H)
    (hj : IsActive w j) : IsSingleFrequency w j :=
  not_not.1 fun hns =>
    not_fourierStructureForced_of_isMinOn hw hmin hj hns (fourierStructureForced_three H R)

/-- The problem at its intended parameters holds for `p = 3` at width five. -/
example : FourierStructureProblem 3 5 := fourierStructureProblem_three 5

end CslibFrontierTests.ModularAddition
