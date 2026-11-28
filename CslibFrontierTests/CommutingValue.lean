/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.CommutingValue

/-! # The commuting-operator value

Checked clients of `Cslib.PCP.TwoProverGame.commutingValue`: the chain of values
`ω ≤ ω* ≤ ω_qc ≤ 1`, a strategy in an arbitrary C⋆-algebra bounded by the value, and the values of
CHSH and the magic square, which agree with their entangled values.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CommutingValue

open Cslib Cslib.Quantum Cslib.PCP Cslib.PCP.TwoProverGame
open scoped Real

/-- The values of a game are ordered. -/
example {X Y A B : Type} [Finite X] [Finite Y] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (G : TwoProverGame X Y A B) :
    G.value ≤ G.quantumValue ∧ G.quantumValue ≤ G.commutingValue ∧ G.commutingValue ≤ 1 :=
  ⟨G.value_le_quantumValue, G.quantumValue_le_commutingValue, G.commutingValue_le_one⟩

/-- A strategy in any C⋆-algebra is bounded by the commuting-operator value. -/
example {𝒜 : Type} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (S : CommutingStrategy Bool Bool Bool Bool 𝒜) : chsh.commutingWinProb S ≤ chsh.commutingValue :=
  chsh.commutingWinProb_le_commutingValue S

/-- Tsirelson's bound is the commuting-operator value of CHSH, which equals its entangled value. -/
example : chsh.commutingValue = chsh.quantumValue := by
  rw [commutingValue_chsh, quantumValue_chsh]

/-- The commuting-operator value of CHSH exceeds the classical value `3/4`. -/
example : chsh.value < chsh.commutingValue := by
  rw [commutingValue_chsh, ← quantumValue_chsh]
  exact value_chsh_lt_quantumValue_chsh

example : magicSquare.commutingValue = 1 :=
  commutingValue_magicSquare

end CslibFrontierTests.CommutingValue
