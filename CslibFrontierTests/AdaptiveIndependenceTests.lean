/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Probability.Fooling.DecisionTree
import CslibFrontier.Probability.KWiseIndependent.Polynomial
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Field.ZMod

/-! Checked instances for adaptive tests of `t`-wise independence (Goldreich, Exercises 8.29 and
8.32): the pairwise independent line hash `x ↦ c₀ + c₁ x` over `ZMod 2`, with one-bit blocks,
satisfies the hypotheses of Exercise 8.29 for an adaptive test reading both blocks. The uniform
distribution meets the hypothesis of Exercise 8.32(2) with `ε = 0`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.AdaptiveIndependence

open Cslib Cslib.Probability Finset
open scoped Cslib.Probability.PMF

/-- One bit as a one-bit block. -/
noncomputable def bitBlock : ZMod 2 ≃ (Fin 1 → Bool) :=
  Fintype.equivOfCardEq (by simp)

/-- The line hash over `ZMod 2`, with each value written as a one-bit block. -/
noncomputable abbrev lineGen (c : Fin 2 → ZMod 2) (x : ZMod 2) : Fin 1 → Bool :=
  bitBlock (polynomialHash c x)

theorem isKWiseIndependentHash_lineGen : IsKWiseIndependentHash 2 lineGen :=
  IsKWiseIndependentHash.map_equiv (isKWiseIndependentHash_polynomialHash (F := ZMod 2) 2)
    bitBlock

/-- Read the bit of block `0`; if it is `1`, also read the bit of block `1`. -/
def twoBlockTest : DecisionTree (ZMod 2 × Fin 1) Bool :=
  .node (0, 0) (.leaf false) (.node (1, 0) (.leaf false) (.leaf true))

example :
    (PMF.uniformOfFintype (Fin 2 → ZMod 2)).map
        (fun s => twoBlockTest.eval (Function.uncurry (lineGen s))) =
      (PMF.uniformOfFintype (ZMod 2 × Fin 1 → Bool)).map twoBlockTest.eval :=
  isKWiseIndependentHash_lineGen.map_eval_eq twoBlockTest fun z =>
    card_image_le.trans ((twoBlockTest.card_queries_le_depth z).trans (by decide))

example (t : ℕ) (ht : t ≤ 3) (T : DecisionTree (Fin 3) Bool) (hT : ∀ z, #(T.queries z) ≤ t) :
    |(((PMF.uniformOfFintype (Fin 3 → Bool)).map T.eval) true).toReal -
        (((PMF.uniformOfFintype (Fin 3 → Bool)).map T.eval) true).toReal| ≤ 2 ^ t * 0 :=
  DecisionTree.abs_map_eval_apply_sub_le (by simpa using ht)
    (fun S _ => by rw [Probability.PMF.uniformOfFintype_pi_map_restrict, dist_self]) T hT

end CslibFrontierTests.AdaptiveIndependence
