/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.MachineLearning.Replicable.MoserTardos
import CslibFrontier.Probability.Product
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Correlated sampling of grid distributions and the budgeted Moser–Tardos learner.

* A coin showing `true` with probability `1 / 4` as a grid distribution with denominator `4`.
* With no perturbation, the grid parties never disagree (`gridSample_disagree_le`).
* One coin, resampled while it shows `true`, sampled from that grid distribution: the event has
  probability `1 / 4`, so the local-lemma hypothesis `e p (d + 1) ≤ 1` holds with `d = 0`. For an
  estimator ignoring the data the learner is perfectly replicable
  (`disagreeProb_budgetedMoserTardos_le`). -/

set_option linter.privateModule false

namespace CslibFrontierTests.ReplicableMoserTardos

open Cslib.Probability.CorrelatedSampling Cslib.MachineLearning.Replicable MeasureTheory
open scoped Cslib.Probability.PMF

/-- A coin showing `true` in one cell out of four. -/
def coin : GridDist Bool 4 := ⟨fun b => if b then 1 else 3, rfl⟩

example : coin.toPMF true = 1 / 4 := by
  simp [GridDist.toPMF_apply, coin]

/-- Without perturbation the parties never disagree. -/
example :
    ((Cslib.Probability.PMF.uniformOfFintype (Enumeration (Bool × Fin 4))).toOuterMeasure
      {σ | gridSample coin σ ≠ gridSample coin σ}).toReal = 0 := by
  simp

/-- The single event reads the single variable. -/
def vbl : Unit → Finset Unit := fun _ => {()}

/-- Resample while the coin shows `true`. -/
def r : List Unit → (Unit → Bool) → Option Unit :=
  fun _ a => if a () then some () else none

/-- The event "the coin shows `true`". -/
def A : Unit → Set (Unit → Bool) := fun _ => {a | a () = true}

/-- The event has probability `1 / 4` under the grid coin. -/
theorem real_A : (Measure.pi fun _ : Unit => coin.toPMF.toMeasure).real (A ()) = 1 / 4 := by
  rw [← Cslib.Probability.PMF.toMeasure_pi, measureReal_def,
    PMF.toMeasure_apply_eq_toOuterMeasure,
    show A () = {fun _ => true} from Set.ext fun a => ⟨fun h => funext fun u => by
      cases u; exact h, fun h => by rw [Set.mem_singleton_iff.1 h]; rfl⟩,
    PMF.toOuterMeasure_apply_singleton, Cslib.Probability.PMF.pi_apply]
  simp [GridDist.toPMF_apply, coin]

/-- **A satisfying instance.** For an estimator ignoring the data, the learner's two runs never
disagree: all hypotheses of `disagreeProb_budgetedMoserTardos_le` hold with `d = 0` and
`p = 1 / 4`. -/
example (B m : ℕ) (D : PMF Bool) :
    (budgetedMoserTardos B vbl r fun (_ : Fin m → Bool) _ => coin).disagreeProb D = 0 := by
  have hp : Real.exp 1 * (1 / 4) * ((0 : ℕ) + 1) ≤ 1 := by
    have := Real.exp_one_lt_d9
    push_cast
    linarith
  have h := disagreeProb_budgetedMoserTardos_le B vbl r (fun (_ : Fin m → Bool) _ => coin) A
    (fun _ => (Set.toFinite _).measurableSet)
    (fun _ a b h => by
      have : a () = b () := h () (by simp [vbl])
      simp [A, this])
    (fun _ => ∅) (fun i j hji => absurd (Subsingleton.elim j i) hji) (d := 0) (fun _ => le_rfl)
    (p := 1 / 4) (fun _ _ => real_A.le) hp
    (fun w a i h => by simpa [r, A] using h) D
  simp only [dist_self, ENNReal.ofReal_zero, mul_zero, tsum_zero, Finset.sum_const_zero]
    at h
  exact le_antisymm (ENNReal.ofReal_eq_zero.1 (le_antisymm h bot_le))
    (Algorithm.disagreeProb_nonneg _ _)

end CslibFrontierTests.ReplicableMoserTardos
