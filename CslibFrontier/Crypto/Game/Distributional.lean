/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Distributional.Distinguishing
public import CslibFrontier.Crypto.Game.Concrete

/-!
# Distribution distinguishing in a chosen computational model

`Distributional.game` evaluates a represented algorithm on a sample from a distribution
distinguishing problem. The representation type, evaluator and admissibility predicate are
supplied by the client. The existing `Game.Indistinguishable`, `Game.IndistinguishableWithError`
and `Game.IndistinguishableWithin` then express asymptotic, concrete or resource-indexed bounds.
There is no separate security notion for distributional problems.

An extensional class of test families gives exactly the same statements when membership means
that one admissible algorithm realizes the entire family. For whole-family admissibility, the
realization quantifier precedes the parameter; replacing it by independent realizers at every
parameter would in general change a uniform model into a nonuniform one.

The existing computational-indistinguishability definition applies directly to the two law
families, including its whole-family PPT semantic tests. Circuit evaluation and gate-count
predicates can likewise be passed directly to `game`; the adapter fixes no computational model.
-/

public section

namespace Cslib.Crypto.Distributional

open Probability
open scoped NNReal

section Model

variable {Input : ℕ → Type*} {Algorithm Resource : Type*}

/-- Run a represented algorithm on the selected law of a problem family.
The model is specified by `Algorithm` and `eval`; admissibility and resource bounds are the
arguments to the shared Boolean-game predicates. -/
@[expose] noncomputable def game
    (P : ∀ n, DistinguishingProblem (Input n))
    (eval : Algorithm → ∀ n, Input n → PMF Bool)
    (hypothesis : Bool) (algorithm : Algorithm) (n : ℕ) : Game :=
  (P n).experiment hypothesis (eval algorithm n)

/-- Quantifying over representations is equivalent to quantifying over test families with one
admissible realizer for the whole family. This retains any uniformity imposed by the model. -/
theorem indistinguishable_iff_realized_tests
    (P : ∀ n, DistinguishingProblem (Input n))
    (eval : Algorithm → ∀ n, Input n → PMF Bool) (Admissible : Algorithm → Prop) :
    Game.Indistinguishable (game P eval false) (game P eval true) Admissible ↔
      Game.Indistinguishable (game P id false) (game P id true)
        (fun test => ∃ algorithm, Admissible algorithm ∧ eval algorithm = test) := by
  constructor
  · rintro h test ⟨algorithm, hadmissible, rfl⟩
    exact h algorithm hadmissible
  · intro h algorithm hadmissible
    exact h (eval algorithm) ⟨algorithm, hadmissible, rfl⟩

/-- A common error bound is unchanged by replacing algorithm representations with their
admissibly realized whole test families. -/
theorem indistinguishableWithError_iff_realized_tests
    (P : ∀ n, DistinguishingProblem (Input n))
    (eval : Algorithm → ∀ n, Input n → PMF Bool) (Admissible : Algorithm → Prop)
    (ε : ℕ → ℝ≥0) :
    Game.IndistinguishableWithError (game P eval false) (game P eval true) Admissible ε ↔
      Game.IndistinguishableWithError (game P id false) (game P id true)
        (fun test => ∃ algorithm, Admissible algorithm ∧ eval algorithm = test) ε := by
  constructor
  · rintro h test ⟨algorithm, hadmissible, rfl⟩
    exact h algorithm hadmissible
  · intro h algorithm hadmissible
    exact h (eval algorithm) ⟨algorithm, hadmissible, rfl⟩

/-- Resource bounds on represented algorithms can equivalently be stated on the test families
they realize, with a witness satisfying the same bound at the parameter under consideration. -/
theorem indistinguishableWithin_iff_realized_tests
    (P : ∀ n, DistinguishingProblem (Input n))
    (eval : Algorithm → ∀ n, Input n → PMF Bool)
    (Within : ℕ → Resource → Algorithm → Prop) (ε : ℕ → Resource → ℝ≥0) :
    Game.IndistinguishableWithin (game P eval false) (game P eval true) Within ε ↔
      Game.IndistinguishableWithin (game P id false) (game P id true)
        (fun n r test => ∃ algorithm, Within n r algorithm ∧ eval algorithm = test) ε := by
  constructor
  · rintro h n r test ⟨algorithm, hwithin, rfl⟩
    exact h n r algorithm hwithin
  · intro h n r algorithm hwithin
    exact h n r (eval algorithm) ⟨algorithm, hwithin, rfl⟩

end Model

end Cslib.Crypto.Distributional
