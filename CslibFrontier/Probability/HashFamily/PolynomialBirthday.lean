/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily.Polynomial
public import CslibFrontier.Probability.IID
import CslibFrontier.Probability.IID.FunctionCollision

/-!
# Birthday collisions in the two-block polynomial hash

Even with the key fixed, the probability of a collision between distinct messages is bounded
away from zero at the birthday scale. The proof uses the birthday lower bound for any function
on uniform samples, subtracting the chance of sampling the same message twice.

## Main results

* `Cslib.Probability.one_eighth_le_polyHash_twoBlock_collision`: the lower bound with exactly
  `⌊√|F|⌋` independent uniform two-block messages.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 7.26(a), printed p. 284.
-/

public section

namespace Cslib.Probability

/-- **Boneh–Shoup Exercise 7.26(a).** For any fixed key `k`, exactly `⌊√|F|⌋` independent
uniform two-block messages contain two distinct messages with equal `Hpoly` digest with
probability at least `1/8` once `|F| ≥ 16`. As in Remark 7.2 (printed p. 263), the domain is
the fixed two-block space `F × F`: each pair is passed to the variable-length hash of equation
(7.3) (printed p. 255) as a list of exactly two blocks. This applies to finite semirings,
including the book's prime field `ZMod p`. -/
theorem one_eighth_le_polyHash_twoBlock_collision {F : Type} [Semiring F] [Fintype F]
    (k : F) (hcard : 16 ≤ Fintype.card F) :
    (1 / 8 : ℝ) ≤
      ((PMF.iid (PMF.uniformOfFintype (F × F)) (Nat.sqrt (Fintype.card F))).toOuterMeasure
        {ms | ∃ i j, polyHash k [(ms i).1, (ms i).2] = polyHash k [(ms j).1, (ms j).2] ∧
          ms i ≠ ms j}).toReal := by
  classical
  refine PMF.one_eighth_le_iid_uniformOfFintype_exists_collision
    (fun m : F × F => polyHash k [m.1, m.2]) Finset.univ (fun _ => Finset.mem_univ _) ?_ ?_
  · simpa only [Finset.card_univ] using hcard
  · rw [Finset.card_univ, Fintype.card_prod]

end Cslib.Probability
