/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.PCP.TwoProverGame.LinearSystemConverse

/-! # Perfect strategies and state-dependent operator solutions

Checked clients of the converse direction for linear constraint system games: orthogonality of
projective effects in a C⋆-algebra, the bound `‖cx‖_φ ≤ ‖c‖ ‖x‖_φ`, perfect strategies never
giving rejected answers, and Bob's observables of a perfect projective strategy forming an
operator solution in the state.
-/

namespace CslibFrontierTests.LinearSystemConverse

open Cslib Cslib.Quantum Cslib.PCP

variable {𝒜 : Type} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- Distinct effects of a projective measurement are orthogonal. -/
example {α : Type} [Fintype α] (M : Measurement α 𝒜) (hM : M.IsProjective) {a b : α}
    (hab : a ≠ b) : M.effect a * M.effect b = 0 :=
  hM.mul_eq_zero hab

/-- The state norm is controlled by the C⋆-norm. -/
example (φ : AlgState 𝒜) (c x : 𝒜) : φ.norm (c * x) ≤ ‖c‖ * φ.norm x :=
  φ.norm_mul_le c x

/-- A perfect projective strategy for a linear constraint system game gives Bob observables that
commute within every equation and multiply to `(-1)^{parity}`, in the shared state. -/
example {V E : Type} [Fintype V] [DecidableEq V] [Finite E] (L : LinearSystem V E)
    {μ : PMF (E × V)} (S : CommutingStrategy E V (V → Bool) Bool 𝒜) (hμ : ∀ q, μ q ≠ 0)
    (hA : ∀ e, (S.alice e).IsProjective) (hB : ∀ v, (S.bob v).IsProjective)
    (h : (L.game μ).commutingWinProb S = 1) (e : E) :
    ((L.support e).toList.map fun v => (S.bob v).observable).prod ≈[S.state; 0]
      boolSign (L.parity e) • 1 :=
  (CommutingStrategy.stateSolution L S hμ hA hB h).prod_eq e

/-- Rejected answers have probability `0` in a perfect strategy. -/
example {V E : Type} [Fintype V] [DecidableEq V] [Finite E] (L : LinearSystem V E)
    {μ : PMF (E × V)} (S : CommutingStrategy E V (V → Bool) Bool 𝒜) (hμ : ∀ q, μ q ≠ 0)
    (h : (L.game μ).commutingWinProb S = 1) {e : E} {v : V} {a : V → Bool} {b : Bool}
    (hrej : ¬ (L.game μ).accepts e v a b) : S.prob e v a b = 0 :=
  TwoProverGame.commutingProb_eq_zero_of_not_accepts (L.game μ) h (hμ (e, v)) hrej

end CslibFrontierTests.LinearSystemConverse
