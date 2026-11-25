/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Tail quantiles of a nonnegative discrete law

A level `q ∈ (0, 1]` has an upper quantile in every law `μ : PMF ℝ≥0`, even one with countably
infinite support and atoms: some cutoff `τ` has `P(X > τ) ≤ q ≤ P(X ≥ τ)`. Thresholds of
single-threshold stopping rules are chosen this way, for instance a median of the maximum
(`q = 1/2`) or the cutoff that accepts an i.i.d. value with probability `1/n`.

`Cslib.Probability.PMF.exists_quantile` is the analogous statement for laws on a finite type.
Mathlib's `ProbabilityTheory.cdf` concerns measures on `ℝ` and provides no quantile.

The proof takes `τ` to be the infimum of the cutoffs with `P(X > t) ≤ q`. That set is nonempty
because the tail tends to `0`. Continuity of `μ.toMeasure` from below gives `P(X > τ) ≤ q`, and
continuity from above gives `q ≤ P(X ≥ τ)`. The level `q = 0` is excluded: a law with unbounded
support has `P(X > t) > 0` for every `t`.

## Main results

* `Cslib.Probability.PMF.exists_tail_quantile`: an upper quantile exists at every
  positive level.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal NNReal
open MeasureTheory Set Filter

/-- **Tail quantiles exist.** For every level `0 < q ≤ 1` there is a cutoff `τ` with
`P(X > τ) ≤ q ≤ P(X ≥ τ)`. -/
theorem exists_tail_quantile (μ : PMF ℝ≥0) {q : ℝ≥0∞} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ τ : ℝ≥0, μ.toOuterMeasure (Ioi τ) ≤ q ∧ q ≤ μ.toOuterMeasure (Ici τ) := by
  simp only [← PMF.toMeasure_apply_eq_toOuterMeasure]
  set ν := μ.toMeasure
  have hlim : Tendsto (fun t : ℝ≥0 => ν (Ioi t)) atTop (nhds 0) := by
    have hinter : (⋂ t : ℝ≥0, Ioi t) = ∅ :=
      iInter_eq_empty_iff.2 fun x => ⟨x, lt_irrefl x⟩
    have h := tendsto_measure_iInter_atTop (μ := ν)
      (fun _ => measurableSet_Ioi.nullMeasurableSet) antitone_Ioi ⟨0, measure_ne_top _ _⟩
    rwa [hinter, measure_empty] at h
  obtain ⟨t, ht⟩ := (hlim.eventually (gt_mem_nhds hq)).exists
  set S := {t : ℝ≥0 | ν (Ioi t) ≤ q}
  have hS : S.Nonempty := ⟨t, ht.le⟩
  refine ⟨sInf S, ?_, ?_⟩
  · -- Approach the infimum by cutoffs already in `S`.
    obtain ⟨u, hu, _, hlim, hmem⟩ :=
      (isGLB_csInf hS (OrderBot.bddBelow S)).exists_seq_antitone_tendsto hS
    rw [← (isGLB_of_tendsto_atTop hu hlim).iUnion_Ioi_eq,
      hu.Ioi.measure_iUnion]
    exact iSup_le hmem
  · rcases eq_or_ne (sInf S) 0 with h0 | h0
    · rw [h0, show Ici (0 : ℝ≥0) = univ from eq_univ_of_forall fun x => by simp, measure_univ]
      exact hq1
    -- Cutoffs strictly below the infimum have tail mass greater than `q`.
    obtain ⟨u, hu, hmem, hlim⟩ :=
      exists_seq_strictMono_tendsto' (pos_iff_ne_zero.mpr h0)
    have hinter : (⋂ n, Ioi (u n)) = Ici (sInf S) := by
      ext x
      simp only [mem_iInter, mem_Ioi, mem_Ici]
      exact ⟨fun h => le_of_tendsto' hlim fun n => (h n).le,
        fun h n => (hmem n).2.trans_le h⟩
    rw [← hinter, hu.monotone.Ioi.measure_iInter
      (fun _ => measurableSet_Ioi.nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf fun n =>
      (not_le.1 (notMem_of_lt_csInf (hmem n).2 (OrderBot.bddBelow S))).le

end Cslib.Probability.PMF
