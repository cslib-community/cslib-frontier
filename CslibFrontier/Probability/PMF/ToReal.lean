/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Init
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Real-valued probabilities

Real-valued probabilities `(μ a).toReal` and `(μ.toOuterMeasure s).toReal` of a discrete
distribution lie in `[0, 1]`. Nonnegativity is `ENNReal.toReal_nonneg`; this module supplies the
upper bounds and monotonicity in the event, so that clients working with real-valued probabilities
need not convert `μ a ≤ 1`, `μ.toOuterMeasure s ≤ 1` or `μ.toOuterMeasure s ≤ μ.toOuterMeasure t`
through `ENNReal.toReal` by hand.

## Main results

* `Cslib.Probability.PMF.toReal_apply_le_one`: an outcome has real-valued probability at most one;
  in particular `Pr[e] ≤ 1` for every Boolean experiment.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_le_one`: an event has real-valued probability at
  most one. The name puts `toOuterMeasure` first, as the `toOuterMeasure_toReal_*` lemmas of
  `CslibFrontier.Probability.PMF.Event` do, rather than Mathlib's head-first
  `toReal_toOuterMeasure_le_one`.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_mono`: a larger event has larger real-valued
  probability.
* `Cslib.Probability.PMF.sum_toReal_mul_mono_support`: a pointwise bound on the support
  bounds the corresponding finite real expectations.
* `Cslib.Probability.PMF.sum_toReal_mul_congr_support`: agreement on the support suffices
  for equality of finite real expectations.
* `Cslib.Probability.PMF.tsum_pure_toReal_mul`, `.sum_pure_toReal_mul`: a real expectation
  under a point mass is the score at that point.
-/

public section

namespace Cslib.Probability.PMF

/-- A probability is at most one; in particular `Pr[e] ≤ 1` for every Boolean experiment. -/
theorem toReal_apply_le_one {α : Type*} (μ : _root_.PMF α) (a : α) : (μ a).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using μ.coe_le_one a)

/-- An event has real-valued probability at most one. -/
theorem toOuterMeasure_toReal_le_one {α : Type*} (μ : _root_.PMF α) (s : Set α) :
    (μ.toOuterMeasure s).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one <| by
    rw [ENNReal.ofReal_one, ← (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)]
    exact μ.toOuterMeasure.mono (Set.subset_univ s)

/-- A larger event has larger real-valued probability. Unlike `ENNReal.toReal_mono`, this needs no
finiteness side condition, since every event has probability at most one. -/
theorem toOuterMeasure_toReal_mono {α : Type*} (μ : _root_.PMF α) {s t : Set α} (h : s ⊆ t) :
    (μ.toOuterMeasure s).toReal ≤ (μ.toOuterMeasure t).toReal := by
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top ?_) (μ.toOuterMeasure.mono h)
  rw [← (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)]
  exact μ.toOuterMeasure.mono (Set.subset_univ t)

/-- Finite real expectations are monotone under pointwise inequalities on the support. -/
theorem sum_toReal_mul_mono_support {α : Type*} [Fintype α] (p : _root_.PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a ≤ g a) :
    ∑ a, (p a).toReal * f a ≤ ∑ a, (p a).toReal * g a := by
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
  · rw [(p.apply_eq_zero_iff a).mpr ha, ENNReal.toReal_zero, zero_mul, zero_mul]

/-- Finite real expectations depend only on the values of the scores on the support. -/
theorem sum_toReal_mul_congr_support {α : Type*} [Fintype α] (p : _root_.PMF α)
    {f g : α → ℝ} (h : ∀ a ∈ p.support, f a = g a) :
    ∑ a, (p a).toReal * f a = ∑ a, (p a).toReal * g a :=
  le_antisymm (sum_toReal_mul_mono_support p fun a ha => (h a ha).le)
    (sum_toReal_mul_mono_support p fun a ha => (h a ha).ge)

/-- Summing a real score against a point mass gives the score at that point. -/
theorem tsum_pure_toReal_mul {α : Type*} (a : α) (f : α → ℝ) :
    ∑' x, ((_root_.PMF.pure a) x).toReal * f x = f a := by
  rw [tsum_eq_single a fun x hx => by simp [_root_.PMF.pure_apply_of_ne _ _ hx],
    _root_.PMF.pure_apply_self, ENNReal.toReal_one, one_mul]

/-- The same point-mass expectation can be summed over any finite set containing the point. -/
theorem sum_pure_toReal_mul {α : Type*} {s : Finset α} {a : α} (ha : a ∈ s) (f : α → ℝ) :
    ∑ x ∈ s, ((_root_.PMF.pure a) x).toReal * f x = f a := by
  rw [← tsum_pure_toReal_mul a f]
  exact (tsum_eq_sum fun x hx => by
    simp [_root_.PMF.pure_apply_of_ne a x (fun h => hx (h.symm ▸ ha))]).symm

end Cslib.Probability.PMF
