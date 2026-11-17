/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.PCP.TwoProverGame.MagicSquare

/-! # The magic square game

Checked clients of the magic square: the parity of answers and the rule of the game on specific
answers, the classical bound, the Mermin–Peres square as an operator solution (its corner
observable, row and column products), the transpose trick on two EPR pairs, the perfect strategy
in any commuting-operator model, and the separation of the classical and entangled values.
-/

namespace CslibFrontierTests.MagicSquare

open Cslib Cslib.Quantum Cslib.PCP Cslib.PCP.TwoProverGame Matrix
open scoped MatrixOrder ComplexOrder

/-- Alice's row `(1, 1, 0)` has even parity and Bob's column `(1, 0, 0)` odd parity; they agree on
the cell `(0, 0)`, so this round is won. -/
example : magicSquare.accepts 0 0 (true, true, false) (true, false, false) := by
  decide

/-- Disagreeing on the shared cell loses. -/
example : ¬ magicSquare.accepts 0 1 (true, true, false) (false, false, true) := by
  decide

/-- Every deterministic strategy loses on some question. -/
example (ha hb : Fin 3 → Bool × Bool × Bool) : ∃ r c, ¬ magicSquare.accepts r c (ha r) (hb c) :=
  exists_not_accepts_magicSquare ha hb

/-- The rows of the Mermin–Peres square multiply to `1` and its columns to `-1`. -/
example : pauliSolution.op 2 0 * pauliSolution.op 2 1 * pauliSolution.op 2 2 = 1 :=
  pauliSolution.row_mul 2

example : pauliSolution.op 0 2 * pauliSolution.op 1 2 * pauliSolution.op 2 2 = -1 :=
  pauliSolution.col_mul 2

/-- On two EPR pairs, Alice's corner observable agrees perfectly with Bob's transposed one. -/
example : kroneckerOne (pauliSolution.op 2 2) ≈[AlgState.vector (maxEntangled (Bool × Bool))
    norm_maxEntangled; 0] oneKronecker (pauliSolution.op 2 2)ᵀ :=
  AlgState.kroneckerOne_approx_oneKronecker_transpose (pauliSolution.isSelfAdjoint 2 2)
    (pauliSolution.mul_self 2 2)

/-- In any C⋆-algebra, perfectly agreeing operator solutions win with certainty. -/
example {𝒜 : Type} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (X Y : MagicSquareSolution 𝒜) (φ : AlgState 𝒜)
    (hXY : ∀ r c r' c', Commute (X.op r c) (Y.op r' c'))
    (h : ∀ r c, X.op r c ≈[φ; 0] Y.op r c) :
    magicSquare.commutingWinProb (X.strategy Y φ hXY) = 1 :=
  X.commutingWinProb_strategy Y φ hXY h

/-- Two EPR pairs win with certainty, and no classical strategy does. -/
example : magicSquare.quantumWinProb magicSquareStrategy = 1 :=
  quantumWinProb_magicSquareStrategy

example : magicSquare.value ≤ 8 / 9 ∧ magicSquare.quantumValue = 1 :=
  ⟨value_magicSquare_le, quantumValue_magicSquare⟩

example : magicSquare.value < magicSquare.quantumValue :=
  value_magicSquare_lt_quantumValue

end CslibFrontierTests.MagicSquare
