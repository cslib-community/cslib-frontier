/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.Lean.OnlineMatching.AdWords

/-!
# Collected results: Online budgeted ad allocation (AdWords / MSVV)
-/

register_result "adwords-msvv-competitive-ratio-upper-bound" where
  title := "MSVV Algorithm 1 (1 - 1/e) competitive-ratio guarantee (upper-bound half only) for \
    online budgeted ad allocation"
  topic := "algorithms"
  sources := [
    { paper := LahaiePennockSaberiVohra2007,
      theorem := "Theorem 28.3 (competitive-ratio guarantee / upper-bound half only) and \
        Exercise 28.6",
      locator := "§28.4.1, pp. 709–711, and p. 716" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.OnlineMatching.AdWords.msvvTrunc_competitive,
    Cslib.Algorithms.Lean.OnlineMatching.AdWords.msvvTrunc_competitive_countLP,
    Cslib.Algorithms.Lean.OnlineMatching.AdWords.msvvAllOrNothing_competitive,
    Cslib.Algorithms.Lean.OnlineMatching.AdWords.msvvAllOrNothing_competitive_countLP,
    Cslib.Algorithms.Lean.OnlineMatching.AdWords.tendsto_msvvTrunc_factor,
    Cslib.Algorithms.Lean.OnlineMatching.AdWords.tendsto_msvvAllOrNothing_factor
  ]
  scope := "Covers ONLY the revenue guarantee (upper-bound half) of Algorithm 1 (MSVV, \
    φ(x) = 1 - exp (x - 1)) against the offline fractional LP relaxation Eq. (28.11) on finite \
    advertiser type ι ([Fintype ι] [LinearOrder ι]) with positive budgets budget j > 0 and finite \
    query stream Fin T → ι → ℝ (or keyword-frequency LP.countLP with queries : Fin T → κ). Both \
    truncated-spend (`msvvTrunc_competitive`: factor (1 - exp (-1)) * exp (-R) for every R with \
    0 ≤ b t j ≤ R * budget j) and all-or-nothing (`msvvAllOrNothing_competitive`: factor \
    (1 - exp (-1)) * (1 - R) * exp (-R) for 0 ≤ R ≤ 1) bounds hold non-asymptotically for EVERY \
    feasible fractional LP solution x without assuming that the optimal solution exhausts budgets \
    (Exercise 28.6, p. 716); both factors converge to 1 - exp (-1) as R → 0. Deterministic \
    tie-breaking prefers the least advertiser in ι. The printed proof in §28.4.1 uses discrete \
    k-buckets (28.12)–(28.13) assuming budget exhaustion (with an inner sum index typo on p. 710); \
    these theorems use the continuous exponential primal-dual potential directly for exact finite \
    bids. Explicitly OUT OF SCOPE and remaining open under #7789: (1) the optimality lower bound \
    (remark before Theorem 28.3, p. 709: no deterministic or randomized online algorithm beats \
    1 - 1/e); (2) running-time / Word-RAM complexity bounds (the rules are pure noncomputable \
    functions over ℝ)."
