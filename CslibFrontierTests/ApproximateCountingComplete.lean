/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.SharpP.ApproximateCounting
import CslibFrontier.Computability.Complexity.Problems.SAT.Padded

/-! The hypotheses of the counting half of Goldreich's Exercise 6.39
(`FNP.exists_approxCount_of_npHard`) are satisfiable: the padded SAT relation of Exercise 6.35 is
in `FNP` and PC-complete, so its solution-existence language is `NP`-hard and its solutions can be
counted approximately with an oracle for that language. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ApproximateCountingComplete

open Finset Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- Approximate counting of the padded SAT relation within the factor `1 ± 1 / (n + 1)`, with an
oracle for the encoded satisfiable formulas. -/
example : ∃ (ℓ : Polynomial ℕ) (E : CNF ℕ × List Bool → ℕ),
    ComputableInPolyTimeWithOracle (encCNF '' searchDomain SAT.paddedRelation.IsWitness) E
      (encPair encCNF encBits) encNat ∧
    ∀ φ, dens {r : BitString (ℓ.eval (encCNF φ).length) |
      (searchCount SAT.paddedRelation.IsWitness φ : ℚ) /
          (Polynomial.X + 1 : Polynomial ℕ).eval (encCNF φ).length <
        |(E (φ, List.ofFn r) : ℚ) - searchCount SAT.paddedRelation.IsWitness φ|} ≤
      (2 ^ (encCNF φ).length)⁻¹ :=
  FNP.exists_approxCount_of_npHard SAT.paddedRelation.isWitness_mem_FNP
    SAT.paddedRelation_levinHard.npHard _ fun n => by simp

end CslibFrontierTests.ApproximateCountingComplete
