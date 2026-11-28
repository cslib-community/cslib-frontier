/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Probability.Fooling.DecisionTree.Separation

/-! The four-bit three-query exception and the first cyclic matching case both give
distinguishing gap one half while their fixed-query errors are strictly smaller. -/

set_option linter.privateModule false

namespace CslibFrontierTests.AdaptiveQuerySeparation

open Cslib Cslib.Probability Finset
open scoped Cslib.Probability.PMF

example (S : Finset (Fin 4)) (hS : #S = 3) :
    ∃ (X : PMF (Fin 4 → Bool)) (T : DecisionTree (Fin 4) Bool),
      T.depth ≤ 3 ∧
      dist (X.map S.restrict) (PMF.uniformOfFintype (S → Bool)) ≤ 3 / 8 ∧
      (((X.map T.eval) true).toReal -
        (((PMF.uniformOfFintype (Fin 4 → Bool)).map T.eval) true).toReal) = 1 / 2 := by
  obtain ⟨X, hX, T, hT, hP, hU⟩ :=
    DecisionTree.exists_dist_map_restrict_le_and_map_eval_eq_printed_length 3 (by decide)
  have hm := hX S hS
  norm_num at hm
  refine ⟨X, T, hT, hm, ?_⟩
  have hu : (PMF.uniformOfFintype (Fin 4 → Bool)).map T.eval = PMF.uniformOfFintype Bool := hU
  rw [hP, hu, PMF.pure_apply_self, PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num

example :
    ∃ (X : PMF (Fin 8 → Bool)) (T : DecisionTree (Fin 8) Bool),
      T.depth ≤ 4 ∧
      (∀ S : Finset (Fin 8), #S = 4 →
        dist (X.map S.restrict) (PMF.uniformOfFintype (S → Bool)) < 1 / 2) ∧
      X.map T.eval = PMF.pure true := by
  obtain ⟨X, hX, T, hT, hP, _⟩ :=
    DecisionTree.exists_dist_map_restrict_le_and_map_eval_eq_printed_length 4 (by decide)
  refine ⟨X, T, hT, fun S hS => (hX S hS).trans_lt ?_, hP⟩
  norm_num

end CslibFrontierTests.AdaptiveQuerySeparation
