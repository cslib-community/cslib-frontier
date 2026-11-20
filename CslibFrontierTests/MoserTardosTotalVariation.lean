/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Probability.MoserTardos.TotalVariation

/-! The output law of Moser–Tardos runs.

* On one coin, resampled while it shows `true`, the table `true, true, false, …` outputs the
  assignment `false` (`output_eq_some_iff`), and the all-`true` table outputs `none`
  (`output_eq_none_iff`).
* The output law puts no mass on the bad assignment (`outputLaw_some_eq_zero`).
* With no perturbation (`P = Q`), the bound of `dist_outputLaw_le_two_mul` is `0`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MoserTardosTotalVariation

open Cslib.Probability.MoserTardos MeasureTheory
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

/-- **No perturbation.** With `P = Q` the total-variation bound is `0`. -/
example {V ι : Type*} [Fintype V] [DecidableEq V] [Finite ι] {α : V → Type*}
    [∀ v, Fintype (α v)] [∀ v, MeasurableSpace (α v)] [∀ v, MeasurableSingletonClass (α v)]
    (P : ∀ v, PMF (α v)) (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι)
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, (Measure.pi fun v => (P v).toMeasure).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    2 * ∑ v, dist (P v) (P v) = 0 ∧
      dist (outputLaw vbl r P) (outputLaw vbl r P) ≤ 2 * ∑ v, dist (P v) (P v) :=
  ⟨by simp, dist_outputLaw_le_two_mul vbl r P P A hAm hA Γ hΓ hΓd hP hp hr⟩

end CslibFrontierTests.MoserTardosTotalVariation
