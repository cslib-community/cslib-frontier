/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.Seeded
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-! # Two-prover games with private verifier randomness

Checked clients: the winning probability as a sum, and the embedding of two-prover games. A
concrete instance: CHSH as a seeded game is won by the optimal EPR strategy with probability
`cos²(π/8)`, as before.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.SeededGame

open Cslib Cslib.PCP Cslib.Quantum
open scoped Real MatrixOrder ComplexOrder

/-- The winning probability of a seeded game as a sum over seeds and answers. -/
example {R X Y A B : Type} [Fintype R] [Fintype A] [Fintype B] (G : SeededGame R X Y A B)
    [∀ r a b, Decidable (G.accepts r a b)] (ans : X → Y → PMF (A × B)) :
    G.answersWinProb ans = ∑ r, (G.seed r).toReal * ∑ a, ∑ b,
      if G.accepts r a b then (ans (G.query r).1 (G.query r).2 (a, b)).toReal else 0 :=
  G.answersWinProb_eq_sum ans

/-- **Concrete instance**: CHSH as a seeded game, with the questions as the seed, is won by the
optimal EPR strategy with probability `cos²(π/8)`. -/
example : TwoProverGame.chsh.toSeeded.commutingWinProb TwoProverGame.chshEPR.toCommuting =
    Real.cos (π / 8) ^ 2 := by
  rw [SeededGame.commutingWinProb_toCommuting, SeededGame.quantumWinProb,
    TwoProverGame.answersWinProb_toSeeded]
  exact TwoProverGame.quantumWinProb_chsh_chshEPR

end CslibFrontierTests.SeededGame
