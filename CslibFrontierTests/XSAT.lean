/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.XSAT

/-! [Goldreich2006DraftR1], Exercise 2.36(1): xSAT lies in promise-NP and promise-coNP. Read
through complements, the second membership says that the complement of xSAT (yes- and no-instances
swapped) lies in promise-NP. Pairs of equal formulas violate the promise. -/

set_option linter.privateModule false

namespace CslibFrontierTests.XSAT

open Cslib.Complexity Cslib.Logic.PL PromiseProblem Turing.MultiTapeTM

-- Both memberships of Exercise 2.36(1).
example : xSAT ∈ PromiseNP (encPair encCNF encCNF) :=
  xSAT_mem_PromiseNP_inter_promiseClass_coNP.1

-- Promise-coNP as complements in promise-NP: the complement of xSAT is in promise-NP.
example : xSATᶜ ∈ PromiseNP (encPair encCNF encCNF) := by
  obtain ⟨A, hA, hyes, hno⟩ := xSAT_mem_PromiseNP_inter_promiseClass_coNP.2
  exact ⟨Aᶜ, hA, fun _ h => Set.disjoint_right.1 hno h,
    Set.disjoint_compl_left_iff_subset.2 hyes⟩

-- A pair of equal formulas is neither a yes- nor a no-instance.
example (φ : CNF ℕ) : (φ, φ) ∉ xSAT.promise := by
  rintro (h | h)
  exacts [h.2 h.1, h.1 h.2]

end CslibFrontierTests.XSAT
