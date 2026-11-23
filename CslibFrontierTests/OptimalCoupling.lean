/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import CslibFrontier.Probability.StatisticalDistance.CouplingBind
import CslibFrontier.Probability.StatisticalDistance.OptimalCoupling
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Optimal couplings beyond finite spaces

The geometric law has positive mass at every natural number. Its optimal coupling with a point
mass disagrees with probability exactly `1 / 2`, and no coupling can improve this to `1 / 4`.
The zero-excess branch and sequential composition across different universes are also exercised.
-/

-- This test module deliberately exports no fixture API.
set_option linter.privateModule false

open Cslib.Probability Cslib.Probability.PMF
open scoped ENNReal Cslib.Probability.PMF

private noncomputable def geometric : PMF ℕ :=
  ⟨fun n => (2⁻¹ : ℝ≥0∞) ^ (n + 1), CompleteLattice.summable.hasSum_iff.mpr (by
    rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top)⟩

/-- This fixture has infinite support, rather than finite support embedded in `ℕ`. -/
example : geometric.support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  rw [PMF.mem_support_iff]
  change (2⁻¹ : ℝ≥0∞) ^ (n + 1) ≠ 0
  exact pow_ne_zero _ (by simp)

private theorem geometric_excess :
    ∑' n, ((PMF.pure 0 : PMF ℕ) n - geometric n) = (1 / 2 : ℝ≥0∞) := by
  classical
  have h (n : ℕ) : (PMF.pure 0 : PMF ℕ) n - geometric n =
      if n = 0 then (1 / 2 : ℝ≥0∞) else 0 := by
    by_cases hn : n = 0
    · subst n
      simp only [PMF.pure_apply, ↓reduceIte]
      change (1 : ℝ≥0∞) - 2⁻¹ ^ (0 + 1) = 1 / 2
      simpa only [zero_add, pow_one, one_div] using ENNReal.one_sub_inv_two
    · simp [PMF.pure_apply, hn]
  simp only [h, tsum_ite_eq]

/-- The general construction attains the exact optimum against an infinite-support law. -/
example : ∃ ω : PMF (ℕ × ℕ), ω.map Prod.fst = PMF.pure 0 ∧ ω.map Prod.snd = geometric ∧
    ω.toOuterMeasure {p | p.1 ≠ p.2} = (1 / 2 : ℝ≥0∞) := by
  obtain ⟨ω, hfst, hsnd, hdisagree⟩ :=
    exists_coupling_toOuterMeasure_eq_tsum_tsub (PMF.pure 0) geometric
  exact ⟨ω, hfst, hsnd, hdisagree.trans geometric_excess⟩

/-- The converse bridge cannot manufacture a coupling below the optimal error. -/
example : CoupledWithin (PMF.pure 0) geometric (1 / 2) ∧
    ¬ CoupledWithin (PMF.pure 0) geometric (1 / 4) := by
  simp only [coupledWithin_iff_closeTo, closeTo_iff_tsum_tsub_le, geometric_excess]
  norm_num

/-- The zero-excess branch still constructs a coupling with no disagreement. -/
example : ∃ ω : PMF (ℕ × ℕ), ω.map Prod.fst = geometric ∧ ω.map Prod.snd = geometric ∧
    ω.toOuterMeasure {p | p.1 ≠ p.2} = 0 := by
  simpa using exists_coupling_toOuterMeasure_eq_tsum_tsub geometric geometric

/-- `CloseTo` and coupling composition accept distinct, genuinely higher output universes. -/
example : CoupledWithin
    ((PMF.pure 0).bind fun n => PMF.pure (ULift.up.{1} (n + 1)))
    (geometric.bind fun n => PMF.pure (ULift.up.{1} (n + 1))) (1 / 2) := by
  have h : CloseTo (PMF.pure 0) geometric (1 / 2) :=
    closeTo_iff_tsum_tsub_le.mpr geometric_excess.le
  exact h.coupledWithin.bind_left _

/-- The real-valued total-variation consequence now applies to the same infinite-support law. -/
example : MeasureTheory.tvDist (PMF.pure 0).toMeasure geometric.toMeasure ≤ 1 := by
  have h : CoupledWithin (PMF.pure 0) geometric (1 / 2) :=
    (closeTo_iff_tsum_tsub_le.mpr geometric_excess.le).coupledWithin
  simpa using h.tvDist_le (by norm_num)

/-- Existing clients retain the finite metric specialization, including its exact equality. -/
example : ∃ ω : PMF (Bool × Bool), ω.map Prod.fst = PMF.pure true ∧
    ω.map Prod.snd = PMF.uniformOfFintype Bool ∧
    (ω.toOuterMeasure {p | p.1 ≠ p.2}).toReal = 1 / 2 := by
  obtain ⟨ω, hfst, hsnd, hdisagree⟩ :=
    exists_coupling_toReal_eq_dist (PMF.pure true) (PMF.uniformOfFintype Bool)
  refine ⟨ω, hfst, hsnd, hdisagree.trans ?_⟩
  norm_num [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool, PMF.pure_apply,
    PMF.uniformOfFintype_apply]
