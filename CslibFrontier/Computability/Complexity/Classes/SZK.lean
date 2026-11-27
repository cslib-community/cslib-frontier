/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.StatisticalDifference.PolyTime
import Mathlib.Tactic.NormNum

/-!
# Statistical zero knowledge via Statistical Difference

We present statistical zero knowledge as the class of promise problems that reduce to
Statistical Difference in polynomial time. The language class uses the total promise
with the language as its yes-set and the complement as its no-set. The correspondence
with zero-knowledge proof systems is the completeness theorem of [SahaiVadhan2003,
Theorem 3.1 and Corollary 4.3], which is used here as the source for the presentation.

We use the library's closed thresholds, 2/3 for yes and 1/3 for no. Its polynomial-time
polarization allows arbitrary constant thresholds with the usual quadratic gap.
Polarizing to a strictly larger yes threshold and strictly smaller no threshold also
recovers the strict inequalities in [SahaiVadhan2003, §3.1].

## Main definitions

* `Cslib.Complexity.PromiseSZK`: statistical zero knowledge for promise problems.
* `Cslib.Complexity.SZK`: its specialization to languages.

## Main results

* `Cslib.Complexity.mem_PromiseSZK_of_polyTimeReducible`: closure under promise reductions.
* `Cslib.Complexity.mem_PromiseSZK_iff_polyTimeReducible`: equivalence across constant
  thresholds with the quadratic gap.
* `Cslib.Complexity.statisticalDifference_mem_PromiseSZK`: Statistical Difference belongs
  to the class.
-/

public section

namespace Cslib.Complexity

/-- Statistical zero knowledge, presented using the polynomial-time many-one complete problem
Statistical Difference. The reduction maps yes- and no-instances into the respective sides of the
target promise. -/
@[expose] def PromiseSZK {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {X | PromiseProblem.PolyTimeReducible enc encSDInstance X
    (StatisticalDifference (2 / 3) (1 / 3))}

/-- A language belongs to SZK when its total promise belongs to `PromiseSZK`. -/
@[expose] def SZK {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseSZK enc}

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {X : PromiseProblem α} {Y : PromiseProblem β}

/-- Promise SZK is closed under polynomial-time many-one reductions. -/
theorem mem_PromiseSZK_of_polyTimeReducible (hXY : PromiseProblem.PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseSZK encB) : X ∈ PromiseSZK encA :=
  hXY.trans hY

/-- Any fixed internal thresholds with a quadratic gap give the same class. -/
theorem mem_PromiseSZK_iff_polyTimeReducible {hi lo : ℝ}
    (hlo : 0 < lo) (hgap : lo < hi ^ 2) (hhi : 0 ≤ hi) (hhi1 : hi < 1) :
    X ∈ PromiseSZK encA ↔
      PromiseProblem.PolyTimeReducible encA encSDInstance X (StatisticalDifference hi lo) := by
  have hlohi : lo < hi := hgap.trans_le (pow_le_of_le_one hhi hhi1.le two_ne_zero)
  constructor
  · intro hX
    exact PromiseProblem.PolyTimeReducible.trans hX
      (StatisticalDifference.polyTimeReducible (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hlo hlohi hhi1)
  · intro hX
    exact hX.trans (StatisticalDifference.polyTimeReducible hlo.le hgap hhi hhi1.le
      (by norm_num) (by norm_num) (by norm_num))

/-- The standard Statistical Difference promise belongs to SZK by the identity reduction. -/
theorem statisticalDifference_mem_PromiseSZK :
    StatisticalDifference (2 / 3) (1 / 3) ∈ PromiseSZK encSDInstance :=
  PromiseProblem.PolyTimeReducible.refl _ _

end Cslib.Complexity
