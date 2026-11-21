/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Probability.MoserTardos.TotalVariation
import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Probability.Product
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The output law of Moser–Tardos runs.

* On one coin, resampled while it shows `true`, the table `true, true, false, …` outputs the
  assignment `false` (`output_eq_some_iff`), and the all-`true` table outputs `none`
  (`output_eq_none_iff`).
* The output law puts no mass on the bad assignment (`outputLaw_some_eq_zero`).
* Perturbing the coin of bias `1 / 4` to the coin of bias `1 / 2`, `dist_outputLaw_le_two_mul`
  bounds the distance of the output laws by `1 / 2`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MoserTardosTotalVariation

open Cslib.Probability.MoserTardos MeasureTheory
open Cslib.Probability.PMF (coin coin_apply_toReal)
open scoped Cslib.Probability.PMF

/-- The single event reads the single variable. -/
def vbl : Unit → Finset Unit := fun _ => {()}

/-- Resample while the coin shows `true`. -/
def r : List Unit → (Unit → Bool) → Option Unit :=
  fun _ a => if a () then some () else none

/-- The table `true, true, false, false, …`. -/
def T₀ : ∀ _ : Unit × ℕ, Bool := fun p => decide (p.2 < 2)

/-- The run on `T₀` stops after two resamplings, at the coin showing `false`. -/
example : output vbl r T₀ = some fun _ => false :=
  output_eq_some_iff.2 ⟨2, by decide, by funext u; cases u; decide⟩

/-- On the all-`true` table the run never stops. -/
example : output vbl r (fun _ : Unit × ℕ => true) = none :=
  output_eq_none_iff.2 fun n => by simp [historyRule, r, current_apply]

/-- The output law never gives the assignment in which the coin shows `true`. -/
example (P : Unit → PMF Bool) : outputLaw vbl r P (some fun _ => true) = 0 :=
  outputLaw_some_eq_zero vbl r (A := fun _ => {a | a () = true})
    (fun _ a h _ ha => by simp_all [r]) P (i := ()) rfl

/-- The event "the coin shows `true`". -/
def A : Unit → Set (Unit → Bool) := fun _ => {a | a () = true}

/-- Under the coin of bias `q`, the event has probability `q`. -/
theorem real_A (q : unitInterval) :
    (Measure.pi fun _ : Unit => (coin q).toMeasure).real (A ()) = q := by
  rw [← Cslib.Probability.PMF.toMeasure_pi, measureReal_def,
    PMF.toMeasure_apply_eq_toOuterMeasure,
    show A () = {fun _ => true} from Set.ext fun a => ⟨fun h => funext fun u => by
      cases u; exact h, fun h => by rw [Set.mem_singleton_iff.1 h]; rfl⟩,
    PMF.toOuterMeasure_apply_singleton, Cslib.Probability.PMF.pi_apply, Fintype.prod_unique,
    coin_apply_toReal]
  rfl

/-- **A perturbed coin.** Resampling while the coin shows `true`, with the coin of bias `1 / 4`
(which satisfies `e p (d + 1) ≤ 1` with `d = 0`) perturbed to the coin of bias `1 / 2`, the output
laws are at statistical distance at most `2 · 1 / 4 = 1 / 2`. -/
example : dist (outputLaw vbl r fun _ => coin ⟨1 / 4, by norm_num, by norm_num⟩)
    (outputLaw vbl r fun _ => coin ⟨1 / 2, by norm_num, by norm_num⟩) ≤ 1 / 2 := by
  have hp : Real.exp 1 * (1 / 4) * ((0 : ℕ) + 1) ≤ 1 := by
    have := Real.exp_one_lt_d9
    push_cast
    linarith
  have hd : dist (coin ⟨1 / 4, by norm_num, by norm_num⟩)
      (coin ⟨1 / 2, by norm_num, by norm_num⟩) = 1 / 4 := by
    rw [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool, coin_apply_toReal, coin_apply_toReal,
      coin_apply_toReal, coin_apply_toReal]
    norm_num [abs_of_nonneg, abs_of_nonpos]
  have h := dist_outputLaw_le_two_mul vbl r (fun _ => coin ⟨1 / 4, by norm_num, by norm_num⟩)
    (fun _ => coin ⟨1 / 2, by norm_num, by norm_num⟩) A
    (fun _ a b h => by
      have : a () = b () := h () (by simp [vbl])
      simp [A, this])
    (fun _ => ∅) (fun i j hji => absurd (Subsingleton.elim j i) hji) (d := 0) (fun _ => le_rfl)
    (p := 1 / 4) (fun _ => (real_A ⟨1 / 4, by norm_num, by norm_num⟩).le) hp
    (fun w a i h => by simpa [r, A] using h)
  rw [Fintype.sum_unique, hd] at h
  linarith

end CslibFrontierTests.MoserTardosTotalVariation
