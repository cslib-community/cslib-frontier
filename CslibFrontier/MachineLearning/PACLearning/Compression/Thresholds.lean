/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Compression.Order
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds

/-!
# Compression for the thresholds of the mistake-bound development

The thresholds `x < θ` on an infinite linear order `α` (`thresholdClass α`) have infinite
Littlestone dimension (`littlestoneDim_thresholdClass`), so no deterministic online learner has a
finite mistake bound for them and the scheme from a mistake bound
(`SampleCompressionScheme.ofMistakeBound`) does not apply. On every linear order, however, they are
lower-set concepts (`thresholdClass_subset_lowerSetClass`), so the size-`1` threshold scheme
`lowerSetScheme` compresses them, and the compression bound makes them PAC learnable in the
realizable setting (`isPACLearnable_thresholdClass`).

This module joins the online and compression developments, so that the order schemes
(`CslibFrontier/MachineLearning/PACLearning/Compression/Order.lean`) and the online threshold module
need not import each other.

## Main results

- `thresholdClass_subset_lowerSetClass`: every threshold `x < θ` on a linear order `α` is a
  lower-set concept.
- `isPACLearnable_thresholdClass`: the thresholds on a countable linear order with measurable
  singletons (such as `ℕ` or `ℚ`) or a second-countable order topology (via
  `isPACLearnable_lowerSetClass`) are PAC learnable in the realizable setting.
-/

public section

namespace Cslib.MachineLearning.PACLearning

open OnlineLearning.MistakeBound

/-- The thresholds `x < θ` on any linear order `α` are lower-set concepts. When `α` is infinite
their Littlestone dimension is `⊤` (`littlestoneDim_thresholdClass`), so the scheme from a mistake
bound does not apply, whereas `lowerSetScheme` compresses them to one example. -/
theorem thresholdClass_subset_lowerSetClass {α : Type*} [LinearOrder α] :
    thresholdClass α ⊆ lowerSetClass α := by
  intro c hc
  obtain ⟨θ, rfl⟩ := mem_thresholdClass.1 hc
  refine mem_lowerSetClass.2 fun x y hyx hx => ?_
  simp only [thresholdConcept_apply, decide_eq_true_eq] at hx ⊢
  exact lt_of_le_of_lt hyx hx

/-- The thresholds `x < θ` on any countable linear order with measurable singletons (for instance
`ℕ` or `ℚ`) are PAC learnable in the realizable setting, although no online learner learns them
with finitely many mistakes when the order is infinite. -/
theorem isPACLearnable_thresholdClass {α : Type*} [LinearOrder α] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α] :
    IsPACLearnable (thresholdClass α) (realizableDistributions (thresholdClass α)) :=
  (lowerSetScheme.ofSubset thresholdClass_subset_lowerSetClass).isPACLearnable
    (measurableReconstruction_of_countable _)

end Cslib.MachineLearning.PACLearning
