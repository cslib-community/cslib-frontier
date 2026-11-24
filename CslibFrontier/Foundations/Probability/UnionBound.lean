/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real

/-!
# The union bound as an existence statement

The probabilistic method finds an outcome that avoids a family of bad events by checking that
their probabilities sum to less than one. Under a probability measure, an event of probability
below one misses some outcome (`MeasureTheory.exists_notMem_of_measureReal_lt_one`), so the union
bound gives an outcome outside every event `A i`, `i ∈ s`, once `∑ i ∈ s, P(A i) < 1`
(`MeasureTheory.exists_forall_notMem_of_sum_le`). Neither statement needs measurability.

## Main results

* `MeasureTheory.exists_notMem_of_measureReal_lt_one`: an event of probability below one misses
  some outcome.
* `MeasureTheory.exists_forall_notMem_of_sum_le`: the union bound, as the existence of an outcome
  that avoids every event.
-/

public section

open Set

namespace MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Under a probability measure, an event of probability below one misses some outcome. -/
theorem exists_notMem_of_measureReal_lt_one {s : Set Ω} (h : P.real s < 1) : ∃ ω, ω ∉ s := by
  by_contra! hall
  simp [eq_univ_of_forall hall] at h

/-- **The union bound.** Under a probability measure, if the events `A i`, `i ∈ s`, have
probabilities at most `b i` and `∑ i ∈ s, b i < 1`, some outcome avoids all of them. -/
theorem exists_forall_notMem_of_sum_le {s : Finset ι} {A : ι → Set Ω} {b : ι → ℝ}
    (hA : ∀ i ∈ s, P.real (A i) ≤ b i) (hb : ∑ i ∈ s, b i < 1) : ∃ ω, ∀ i ∈ s, ω ∉ A i := by
  obtain ⟨ω, hω⟩ := exists_notMem_of_measureReal_lt_one
    (((measureReal_biUnion_finset_le s A).trans (Finset.sum_le_sum hA)).trans_lt hb)
  exact ⟨ω, fun i hi h => hω (mem_biUnion hi h)⟩

end MeasureTheory
