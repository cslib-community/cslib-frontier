/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Probability.MoserTardos.Coupling

/-! Coupled Moser–Tardos runs.

* A concrete run of a non-anticipating rule on one coin. The event "the coin shows `true`" is
  resampled until the table gives `false`. On the table `true, true, false, …` the run reads
  three samples and stops after two resamplings, which `decide` computes.
* Two tables that differ only at an entry the run never reads give the same log
  (`run_eq_of_agree`).
* With no perturbation (`P = Q`), correlated sampling makes the two runs never diverge
  (`correlated_diverge_le`).
* The symmetric weight bound for `d = 0`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MoserTardosCoupling

open Cslib.Probability.MoserTardos MeasureTheory
open scoped ENNReal

/-- The single event reads the single variable. -/
def vbl : Unit → Finset Unit := fun _ => {()}

/-- Resample while the coin shows `true`. -/
def r : List Unit → (Unit → Bool) → Option Unit :=
  fun _ a => if a () then some () else none

/-- The table `true, true, false, false, …`. -/
def T₀ : ∀ _ : Unit × ℕ, Bool := fun p => decide (p.2 < 2)

/-- `T₀` with entry `k = 5` flipped. -/
def T₁ : ∀ _ : Unit × ℕ, Bool := fun p => if p.2 = 5 then true else decide (p.2 < 2)

/-- The run resamples twice and stops. -/
example : run (historyRule vbl r) T₀ 4 = [(), ()] := by decide

/-- It reads samples `0`, `1` and `2` only. -/
example : ∀ n < 4, uses vbl (run (historyRule vbl r) T₀ n) () ≤ 2 := by decide

/-- Flipping an entry the run never reads does not change the run. -/
example : run (historyRule vbl r) T₀ 4 = run (historyRule vbl r) T₁ 4 :=
  run_eq_of_agree r 4 fun m hm u => by
    cases u
    have : uses vbl (run (historyRule vbl r) T₀ m) () ≠ 5 := by
      interval_cases m <;> decide
    simp [T₀, T₁, this]

open scoped Cslib.Probability.PMF in
/-- **No perturbation, no divergence.** If both runs sample from the same distributions, the
correlated-sampling coupling makes them identical almost surely. -/
example {V ι : Type*} [Fintype V] [DecidableEq V] [Finite ι] {α : V → Type*}
    [∀ v, Fintype (α v)] [∀ v, MeasurableSpace (α v)] [∀ v, MeasurableSingletonClass (α v)]
    (P : ∀ v, PMF (α v)) (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι)
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, (Measure.pi fun v => (P v).toMeasure).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    coupledTable (correlatedCoupling P P) {T | Diverge vbl r T} = 0 := by
  refine le_antisymm ?_ bot_le
  simpa using correlated_diverge_le P P vbl r A hAm hA Γ hΓ hΓd hP hp hr

/-- With no neighbours, `e p ≤ 1` gives `p ≤ 1 / 2`. -/
example {p : ℝ} (hp : Real.exp 1 * p * (0 + 1) ≤ 1) : p ≤ 1 / 2 := by
  simpa using le_weight_of_exp_mul_le 0 (by simpa using hp)

end CslibFrontierTests.MoserTardosCoupling
