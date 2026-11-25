/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import CslibFrontier.Probability.StatisticalDistance.Coupling
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map

/-!
# Optimal couplings

On a finite type, two distributions have a coupling whose disagreement probability equals their
statistical distance (`Cslib.Probability.PMF.exists_coupling_toReal_eq_dist`). Together with the
coupling inequality `Cslib.Probability.PMF.CoupledWithin.dist_le` this characterizes statistical
distance as the minimum disagreement probability over all couplings. The coupling puts
`min (μ a) (ν a)` on each diagonal point `(a, a)` and spreads the excesses `μ - ν` and `ν - μ`
independently over the off-diagonal.

As a consequence, running a common kernel `K` from two coupled distributions moves them at most
the disagreement probability times the largest distance between two rows of `K`
(`Cslib.Probability.PMF.CoupledWithin.dist_bind_le`). With an optimal coupling this gives
`dist (μ.bind K) (ν.bind K) ≤ dist μ ν * D`, the step behind the submultiplicativity of the
pairwise distance of a Markov chain.

## Main results

* `Cslib.Probability.PMF.exists_coupling_toReal_eq_dist`: an optimal coupling exists.
* `Cslib.Probability.PMF.coupledWithin_dist`: two distributions are coupled within their
  statistical distance.
* `Cslib.Probability.PMF.CoupledWithin.dist_bind_le`: contraction of a common kernel through a
  coupling.
* `Cslib.Probability.PMF.dist_bind_le_mul`: contraction through an optimal coupling.

## References

* [LevinPeres2017], Proposition 4.7 and Remark 4.8 (optimal coupling).
-/

public section

open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.PMF

variable {α β : Type*}

/-- **Optimal coupling** ([LevinPeres2017], Proposition 4.7 and Remark 4.8). On a finite
type, two distributions have a coupling whose disagreement probability is exactly their
statistical distance. -/
theorem exists_coupling_toReal_eq_dist [Fintype α] (μ ν : PMF α) :
    ∃ ω : PMF (α × α), ω.map Prod.fst = μ ∧ ω.map Prod.snd = ν ∧
      (ω.toOuterMeasure {p | p.1 ≠ p.2}).toReal = dist μ ν := by
  obtain ⟨ω, hfst, hsnd, hdisagree⟩ := exists_coupling_toOuterMeasure_eq_tsum_tsub μ ν
  refine ⟨ω, hfst, hsnd, ?_⟩
  rw [hdisagree, ← ofReal_dist, ENNReal.toReal_ofReal dist_nonneg]

/-- Two distributions on a finite type are coupled within their statistical distance. -/
theorem coupledWithin_dist [Fintype α] (μ ν : PMF α) :
    CoupledWithin μ ν (ENNReal.ofReal (dist μ ν)) := by
  obtain ⟨ω, h1, h2, h3⟩ := exists_coupling_toReal_eq_dist μ ν
  exact ⟨ω, h1, h2, by rw [← h3, ENNReal.ofReal_toReal (toOuterMeasure_ne_top _ _)]⟩

/-- Running a common kernel `K` from two distributions coupled within `ε` moves them at most
`ε * D`, where `D` bounds the distance between any two rows of `K`. -/
theorem CoupledWithin.dist_bind_le [Finite α] [Fintype β] {μ ν : PMF α} {ε : ℝ≥0∞}
    (h : CoupledWithin μ ν ε) (hε : ε ≠ ⊤) (K : α → PMF β) {D : ℝ}
    (hD : ∀ x y, dist (K x) (K y) ≤ D) :
    dist (μ.bind K) (ν.bind K) ≤ ε.toReal * D := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨ω, rfl, rfl, hω⟩ := h
  have hD0 : 0 ≤ D := by
    obtain ⟨a, -⟩ := ω.support_nonempty
    simpa using hD a.1 a.1
  have hpair (g : α × α → α) :
      (ω.bind fun p => (K (g p)).map (p, ·)).map Prod.snd = ω.bind (K ∘ g) := by
    rw [PMF.map_bind]
    exact congrArg ω.bind (funext fun p => (PMF.map_comp _ _ _).trans (PMF.map_id _))
  rw [PMF.bind_map, PMF.bind_map, ← hpair Prod.fst, ← hpair Prod.snd]
  refine (dist_map_le _ _ _).trans ?_
  rw [dist_bind_pair]
  calc ∑ p, (ω p).toReal * dist (K p.1) (K p.2)
      ≤ ∑ p, (if p ∈ {p : α × α | p.1 ≠ p.2} then (ω p).toReal else 0) * D := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hp : p.1 = p.2
        · simp [hp]
        · simpa [hp] using mul_le_mul_of_nonneg_left (hD p.1 p.2) ENNReal.toReal_nonneg
    _ = (ω.toOuterMeasure {p | p.1 ≠ p.2}).toReal * D := by
        rw [toOuterMeasure_apply_toReal, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by split_ifs <;> rfl
    _ ≤ ε.toReal * D := by gcongr

/-- Running a common kernel `K` moves two distributions at most their statistical distance times
the largest distance `D` between two rows of `K`. -/
theorem dist_bind_le_mul [Fintype α] [Fintype β] (μ ν : PMF α) (K : α → PMF β) {D : ℝ}
    (hD : ∀ x y, dist (K x) (K y) ≤ D) :
    dist (μ.bind K) (ν.bind K) ≤ dist μ ν * D := by
  have h := (coupledWithin_dist μ ν).dist_bind_le ENNReal.ofReal_ne_top K hD
  rwa [ENNReal.toReal_ofReal dist_nonneg] at h

end Cslib.Probability.PMF
