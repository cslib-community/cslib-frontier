/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.InaccessibleEntropy.OneWay

/-!
# Client check of the concrete Theorem 4.5 endpoint

An ordinary `module` client of `OneWay.rompelBase_logGap` ([HHRVW2020], Section 4.2,
Theorem 4.5, p. 21), for a length-preserving `OneWay` function `g`:

* the concrete function `F₀` reads `rompelBaseInLen n n = n ^ 2 + 2 * n + (Nat.log 2 n + 1)`
  bits, quadratic in `n` because of the affine hash seed;
* on inputs of exactly that width, the accessible-set family at threshold exponent
  `Nat.ceil (256 * 3) + 1` has an eventual `3 * log₂ n / n` entropy gap, and every uniform strict
  PPT adversary escapes it with negligible probability.
-/

namespace CslibFrontierTests.Crypto.RompelLogGap

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-- For a length-preserving one-way function, `F₀` reads `n` preimage bits, an `n * n + n`-bit
affine seed and a `(Nat.log 2 n + 1)`-bit prefix field. -/
example (n : ℕ) : rompelBaseInLen n n = n ^ 2 + 2 * n + (Nat.log 2 n + 1) := by
  simp only [rompelBaseInLen, rompelSeedWidth, rompelTruncWidth]
  ring

/-- `OneWay.rompelBase_logGap` at `d = 3` for a length-preserving `OneWay` function, stated on the
`rompelBaseInLen n n`-bit inputs of the concrete function. -/
example {g : List Bool → List Bool} (hg : OneWay g)
    (hlen : ∀ w : List Bool, (g w).length = w.length) :
    (∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      accessibleSetExpectation
          (rompelAccessibleSet (Nat.ceil (256 * (3 : ℝ)) + 1) g id n) ≤
        PMF.conditionalEntropy
          ((PMF.uniformOfFintype (BitString (rompelBaseInLen n n))).map fun b =>
            (wordToFinMap (rompelBaseInLen n n) (rompelBaseOutLen n n)
              (rompelBaseEvalWord g id n) b, b)) -
          3 * Real.logb 2 n / n) ∧
    ∀ A : ℕ → List Bool → ProbComp (List Bool), IsPPT encBits A →
      Negligible fun n => Game.succProbability (ProbComp.eval
        (accessibleEscapeGame (rompelBaseEvalWord g id) (fun k => rompelBaseInLen k k)
          (rompelAccessibleSet (Nat.ceil (256 * (3 : ℝ)) + 1) g id) A n)) :=
  hg.rompelBase_logGap hlen (by fun_prop) (by norm_num)

end CslibFrontierTests.Crypto.RompelLogGap
