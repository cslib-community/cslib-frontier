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
* Grid coins of bias `1 / 4` and `2 / 4` disagree with probability at most `1 / 2`
  (`gridSample_disagree_le`).
* One coin, resampled while it shows `true`, sampled from that grid distribution: the event has
  probability `1 / 4`, so the local-lemma hypothesis `e p (d + 1) ≤ 1` holds with `d = 0`, and a
  run budgeted to `B` steps times out with probability at most `1 / (B + 1)`
  (`seedTable_timeout_le`).
* The empirical coin of four flips satisfies the hypothesis on the samples with at most one flip
  showing `true`; the learner using it is accurate (`isAccurateOn_budgetedMoserTardos`) and
  replicable (`disagreeProb_budgetedMoserTardos_le`) up to the probability of the other samples.
* For an estimator ignoring the data the learner is perfectly replicable. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ReplicableMoserTardos

open Cslib.Probability.CorrelatedSampling Cslib.MachineLearning.Replicable MeasureTheory
open Finset (univ)
open scoped Finset
open scoped Cslib.Probability.PMF

/-- A coin showing `true` in one cell out of four. -/
def coin : GridDist Bool 4 := ⟨fun b => if b then 1 else 3, rfl⟩

example : coin.toPMF true = 1 / 4 := by
  simp [GridDist.toPMF_apply, coin]

/-- A coin showing `true` in two cells out of four. -/
def coin₂ : GridDist Bool 4 := ⟨fun _ => 2, rfl⟩

/-- **A perturbed grid coin.** The grid coins of bias `1 / 4` and `2 / 4` are at statistical
distance `1 / 4`, so the parties holding them disagree with probability at most `1 / 2`. -/
example :
    ((Cslib.Probability.PMF.uniformOfFintype (Enumeration (Bool × Fin 4))).toOuterMeasure
      {σ | gridSample coin σ ≠ gridSample coin₂ σ}).toReal ≤ 1 / 2 := by
  have hd : dist coin.toPMF coin₂.toPMF = 1 / 4 := by
    rw [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool, GridDist.toPMF_apply_toReal,
      GridDist.toPMF_apply_toReal, GridDist.toPMF_apply_toReal, GridDist.toPMF_apply_toReal]
    norm_num [coin, coin₂, abs_of_nonneg, abs_of_nonpos]
  refine (gridSample_disagree_le coin coin₂).trans_eq ?_
  rw [hd]
  norm_num

/-- The single event reads the single variable. -/
def vbl : Unit → Finset Unit := fun _ => {()}

/-- Resample while the coin shows `true`. -/
def r : List Unit → (Unit → Bool) → Option Unit :=
  fun _ a => if a () then some () else none

/-- The event "the coin shows `true`". -/
def A : Unit → Set (Unit → Bool) := fun _ => {a | a () = true}

theorem hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set Unit) := fun _ a b h => by
  have : a () = b () := h () (by simp [vbl])
  simp [A, this]

theorem hΓ :
    ∀ i j : Unit, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ (fun _ => ∅ : Unit → Finset Unit) i :=
  fun i j hji => absurd (Subsingleton.elim j i) hji

theorem hr : ∀ w a i, r w a = some i → a ∈ A i := fun w a i h => by simpa [r, A] using h

theorem hstop : ∀ w a, r w a = none → ∀ i, a ∉ A i := fun w a h i ha => by simp_all [r, A]

theorem hp : Real.exp 1 * (1 / 4) * ((0 : ℕ) + 1) ≤ 1 := by
  have := Real.exp_one_lt_d9
  push_cast
  linarith

/-- Under a grid coin, the event has probability `count true / 4`. -/
theorem toReal_A (P : GridDist Bool 4) :
    ((Cslib.Probability.PMF.pi fun _ : Unit => P.toPMF).toOuterMeasure (A ())).toReal =
      P.count true / 4 := by
  rw [show A () = {fun _ => true} from Set.ext fun a => ⟨fun h => funext fun u => by
      cases u; exact h, fun h => by rw [Set.mem_singleton_iff.1 h]; rfl⟩,
    PMF.toOuterMeasure_apply_singleton, Cslib.Probability.PMF.pi_apply, Fintype.prod_unique,
    GridDist.toPMF_apply_toReal]
  norm_num

/-- **Timeouts are rare.** On the grid coin of bias `1 / 4`, a run budgeted to `B` steps times out
with probability at most `1 / (B + 1)`. -/
example (B : ℕ) :
    ((Cslib.Probability.PMF.uniformOfFintype
      (BudgetSeed (fun _ : Unit => Bool) 4 B)).toOuterMeasure
        {σ | budgetedOutput vbl r B (seedTable B (fun _ => coin) σ) = none}).toReal ≤
      1 / (B + 1) := by
  have h := seedTable_timeout_le B vbl r (fun _ => coin) A hA (fun _ => ∅) hΓ (d := 0)
    (fun _ => le_rfl) (p := 1 / 4) (fun _ => by rw [toReal_A]; norm_num [coin]) hp hr
  simpa using h

/-- The **empirical grid distribution** of four coin flips: one cell for each flip. -/
def empirical (S : Fin 4 → Bool) : GridDist Bool 4 :=
  ⟨fun b => #{j | S j = b}, by
    rw [Fintype.sum_bool]
    simpa using Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin 4)))
      (p := fun j => S j = true)⟩

/-- The samples with at most one flip showing `true`, on which the empirical coin satisfies the
local-lemma hypothesis. -/
def good : Set (Fin 4 → Bool) := {S | #{j | S j = true} ≤ 1}

theorem hP : ∀ S ∈ good, ∀ i,
    ((Cslib.Probability.PMF.pi fun _ : Unit => (empirical S).toPMF).toOuterMeasure (A i)).toReal ≤
      1 / 4 := fun S hS i => by
  rw [toReal_A]
  have : (#{j | S j = true} : ℝ) ≤ 1 := by exact_mod_cast hS
  simp only [empirical]
  linarith

/-- **Accuracy of the empirical learner.** On four flips of any coin `D`, the learner with the
empirical estimate fails to output an assignment avoiding the event with probability at most
`1 / (B + 1)` plus the probability of seeing two or more flips showing `true`. -/
example (B : ℕ) (D : PMF Bool) :
    IsAccurateOn (budgetedMoserTardos B vbl r fun S _ => empirical S) D (goodOutput A)
      (1 / ((0 + 1) * (B + 1)) +
        ((Cslib.Probability.PMF.iid D 4).toOuterMeasure goodᶜ).toReal) := by
  simpa using isAccurateOn_budgetedMoserTardos B vbl r (fun S _ => empirical S) A hA (fun _ => ∅)
    hΓ (d := 0) (fun _ => le_rfl) good hP hp hr hstop D

/-- **Replicability of the empirical learner.** Two runs on independent four-flip samples disagree
with probability at most four times the expected distance between the two empirical coins, plus
the probability that the first sample is not good. -/
example (B : ℕ) (D : PMF Bool) :
    (budgetedMoserTardos B vbl r fun S _ => empirical S).disagreeProb D ≤
      4 * ∑' S₁, ∑' S₂, (Cslib.Probability.PMF.iid D 4 S₁).toReal *
        (Cslib.Probability.PMF.iid D 4 S₂).toReal * dist (empirical S₁).toPMF (empirical S₂).toPMF +
      ((Cslib.Probability.PMF.iid D 4).toOuterMeasure goodᶜ).toReal := by
  simpa using disagreeProb_budgetedMoserTardos_le B vbl r (fun S _ => empirical S) A hA
    (fun _ => ∅) hΓ (d := 0) (fun _ => le_rfl) good hP hp hr D

/-- **A data-independent estimator.** With `good = Set.univ` the tail term vanishes and the
learner is perfectly replicable. -/
example (B m : ℕ) (D : PMF Bool) :
    (budgetedMoserTardos B vbl r fun (_ : Fin m → Bool) _ => coin).disagreeProb D = 0 := by
  have h := disagreeProb_budgetedMoserTardos_le B vbl r (fun (_ : Fin m → Bool) _ => coin) A hA
    (fun _ => ∅) hΓ (d := 0) (fun _ => le_rfl) (p := 1 / 4) Set.univ
    (fun _ _ _ => by rw [toReal_A]; norm_num [coin]) hp hr D
  simp only [dist_self, mul_zero, tsum_zero, Finset.sum_const_zero, Set.compl_univ,
    measure_empty, ENNReal.toReal_zero, add_zero] at h
  exact le_antisymm h (Algorithm.disagreeProb_nonneg _ _)

end CslibFrontierTests.ReplicableMoserTardos
