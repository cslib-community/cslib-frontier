/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.BooleanAnalysis.Noise
import CslibFrontier.Foundations.BooleanAnalysis.Variance
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # Noise sensitivity of nearly constant functions

Clients of O'Donnell's Exercise 2.39 under module encapsulation. The conjunction of two bits is
`true` on one of its four inputs, so its relative Hamming distance to the constant `false` is
`1 / 4`, and Exercise 2.39 bounds its noise sensitivity at any rate `δ ≤ 1` by `1 / 2`. At rate
`1` the noised string is the complement, and the conjunction changes on `00` and `11`, half of
the inputs, so the bound is attained. Chained with the lower bound of Proposition 1.15, the
exercise bounds the noise sensitivity of every Boolean function at every rate `δ ≤ 1` by its
variance read as signs.

The non-module `BooleanAnalysisExamples.noiseSensitivity_and₂` computes the noise sensitivity of
the conjunction at every rate, but a `module` client cannot import a non-module file, so the value
at rate `1` is recomputed here from the definition.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.BooleanAnalysisNearlyConstant

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- The conjunction of two bits. -/
private def and₂ (x : Fin 2 → Bool) : Bool :=
  x 0 && x 1

/-- The conjunction is `true` on exactly one of the four inputs. -/
private theorem hammingDist_and₂_false : hammingDist and₂ (fun _ => false) = 1 := by decide

/-- The conjunction is `false` on three of the four inputs. -/
private theorem hammingDist_and₂_true : hammingDist and₂ (fun _ => true) = 3 := by decide

/-- At rate `1` the noised string is the complement, so the conjunction changes on `00` and `11`,
half of the inputs. -/
private theorem noiseSensitivity_one_and₂ : noiseSensitivity 1 and₂ = 1 / 2 := by
  have h1 (g : (Fin 2 → Bool) → ℝ) : bernoulliAverage 1 g = g fun _ => true := by
    simpa [bernoulliAverage_zero] using bernoulliAverage_one_sub 0 g
  rw [noiseSensitivity, Finset.expect_congr rfl fun x _ => h1 _, Fintype.expect_boole, dens,
    show ({x | and₂ x ≠ and₂ (x + fun _ => true)} : Finset (Fin 2 → Bool)).card = 2 by decide]
  norm_num [Fintype.card_fun]

-- The distance `1 / 4` to the constant `false` bounds the noise sensitivity of the conjunction
-- at every rate `δ ≤ 1` by `1 / 2`.
example {δ : ℝ} (hδ : δ ≤ 1) : noiseSensitivity δ and₂ ≤ 1 / 2 := by
  have h := noiseSensitivity_le_two_mul_hammingDist_div hδ and₂ false
  rw [hammingDist_and₂_false, Fintype.card_fin] at h
  norm_num at h ⊢
  exact h

-- The bound is attained: at rate `1` the noise sensitivity `1 / 2` equals twice the distance
-- `1 / 4` to the nearer constant.
example : noiseSensitivity 1 and₂ =
    2 * min ((hammingDist and₂ (fun _ => false) : ℝ) / 2 ^ Fintype.card (Fin 2))
      (hammingDist and₂ (fun _ => true) / 2 ^ Fintype.card (Fin 2)) := by
  rw [noiseSensitivity_one_and₂, hammingDist_and₂_false, hammingDist_and₂_true, Fintype.card_fin]
  norm_num

-- Since the bound is attained at rate `1`, Exercise 2.39 in the form with the nearer constant
-- shows that no rate `δ ≤ 1` makes the conjunction more sensitive than rate `1`.
example {δ : ℝ} (hδ : δ ≤ 1) : noiseSensitivity δ and₂ ≤ noiseSensitivity 1 and₂ := by
  have h := noiseSensitivity_le_two_mul_min hδ and₂
  rw [hammingDist_and₂_false, hammingDist_and₂_true, Fintype.card_fin] at h
  rw [noiseSensitivity_one_and₂]
  norm_num at h ⊢
  exact h

-- Exercise 2.39 with the lower bound `2 ε ≤ Var[F]` of Proposition 1.15: at rates `δ ≤ 1`, the
-- noise sensitivity of a Boolean function is at most its variance read as signs.
example {ι : Type} [Fintype ι] [DecidableEq ι] {δ : ℝ} (hδ : δ ≤ 1) (f : (ι → Bool) → Bool) :
    noiseSensitivity δ f ≤ 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 :=
  (noiseSensitivity_le_two_mul_min hδ f).trans (two_mul_min_le_expect_sub_expect_sq_signVal f)

end CslibFrontierTests.BooleanAnalysisNearlyConstant
