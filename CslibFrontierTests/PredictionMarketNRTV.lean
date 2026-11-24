/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.PredictionMarket.LMSR
import Mathlib.Tactic.NormNum

/-!
# Checked witnesses for proper scoring rules and Hanson's LMSR

Non-vacuous concrete witnesses exercising `Cslib.GameTheory.PredictionMarket`:

* Strict propriety and score gap evaluations for the quadratic (Brier), logarithmic, and spherical
  scoring rules on `Fin 2` and `Fin 3`.
* Negative witnesses: a constant scoring rule is proper but not strictly proper; the identity score
  `p ω` is not proper; the real-valued logarithmic score violates propriety on the closed simplex
  because `Real.log 0 = 0`, confirming the necessity of `openProbSimplex`.
* Savage / Bregman divergence characterization on concrete differentiable convex potentials.
* Hanson's LMSR on `Fin 2` and `Fin 3`: softmax prices, translation equivariance, convexity,
  exact coordinate derivative, two-step sequential trading equivalence with logarithmic MSR,
  worst-case market-maker loss `≤ b * Real.log |Ω|`, and tightness witnesses.
-/

namespace CslibFrontierTests.PredictionMarketNRTV

open Finset Matrix Cslib.GameTheory Cslib.GameTheory.PredictionMarket

/-! ### Concrete distributions on `Fin 2` and `Fin 3` -/

/-- The binary distribution `(3/4, 1/4)`. -/
noncomputable def q2 : Fin 2 → ℝ := ![3 / 4, 1 / 4]

/-- The uniform binary distribution `(1/2, 1/2)`. -/
noncomputable def u2 : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- The degenerate point-mass distribution `(1, 0)` on `Fin 2`. -/
def e0 : Fin 2 → ℝ := ![1, 0]

/-- The opposite degenerate distribution `(0, 1)` on `Fin 2`. -/
def e1 : Fin 2 → ℝ := ![0, 1]

/-- A strictly positive 3-outcome distribution `(1/2, 1/3, 1/6)`. -/
noncomputable def q3 : Fin 3 → ℝ := ![1 / 2, 1 / 3, 1 / 6]

theorem q2_mem_open : q2 ∈ openProbSimplex (Fin 2) := by
  refine ⟨isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩, fun i => ?_⟩
  · fin_cases i <;> norm_num [q2]
  · norm_num [q2, Fin.sum_univ_two]
  · fin_cases i <;> norm_num [q2]

theorem u2_mem_open : u2 ∈ openProbSimplex (Fin 2) := by
  refine ⟨isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩, fun i => ?_⟩
  · fin_cases i <;> norm_num [u2]
  · norm_num [u2, Fin.sum_univ_two]
  · fin_cases i <;> norm_num [u2]

theorem e0_mem_simplex : e0 ∈ probSimplex (Fin 2) := by
  refine isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [e0]
  · norm_num [e0, Fin.sum_univ_two]

theorem e1_mem_simplex : e1 ∈ probSimplex (Fin 2) := by
  refine isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [e1]
  · norm_num [e1, Fin.sum_univ_two]

theorem q3_mem_open : q3 ∈ openProbSimplex (Fin 3) := by
  refine ⟨isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩, fun i => ?_⟩
  · fin_cases i <;> norm_num [q3]
  · norm_num [q3, Fin.sum_univ_three]
  · fin_cases i <;> norm_num [q3]

theorem u2_ne_q2 : u2 ≠ q2 := by
  intro h
  have := congrFun h 0
  norm_num [u2, q2] at this

/-! ### Quadratic (Brier), logarithmic, and spherical scoring witnesses -/

/-- Exact quadratic expected-score gap between `q2 = (3/4, 1/4)` and `u2 = (1/2, 1/2)` is `1/8`. -/
example :
    (quadraticScore (Fin 2)).expectedScore q2 q2 -
      (quadraticScore (Fin 2)).expectedScore q2 u2 = 1 / 8 := by
  rw [quadraticScore_expectedScore_sub q2_mem_open.1.sum_eq_one]
  norm_num [q2, u2, Fin.sum_univ_two]

/-- Brier score at `q2 = (3/4, 1/4)` on outcome `0` equals `-1/8`, matching `quadraticScore - 1`. -/
example : (brierScore (Fin 2)).score q2 0 = -1 / 8 ∧
    (brierScore (Fin 2)).score q2 0 = (quadraticScore (Fin 2)).score q2 0 - 1 := by
  norm_num [brierScore_score, quadraticScore_score, q2, Fin.sum_univ_two]

/-- Affine quadratic score `a + b * quadraticScore` with `a = 5, b = 3` is bounded in `[2, 8]`. -/
example (i : Fin 2) :
    2 ≤ ((quadraticScore (Fin 2)).affine 3 (fun _ => 5)).score q2 i ∧
      ((quadraticScore (Fin 2)).affine 3 (fun _ => 5)).score q2 i ≤ 8 := by
  have hb := quadraticScore_bounds q2_mem_open.1 i
  simp only [ScoringRule.affine_score]
  constructor <;> linarith

/-- Strict propriety of the logarithmic score on `q2` vs. `u2`. -/
example : (logScore (Fin 2)).expectedScore q2 u2 < (logScore (Fin 2)).expectedScore q2 q2 :=
  isStrictlyProperOn_logScore.expectedScore_lt q2_mem_open u2_mem_open u2_ne_q2

/-- Strict propriety of the spherical score on `q2` vs. `u2`. -/
example :
    (sphericalScore (Fin 2)).expectedScore q2 u2 < (sphericalScore (Fin 2)).expectedScore q2 q2 :=
  ScoringRule.IsStrictlyProperOn.expectedScore_lt isStrictlyProper_sphericalScore
    q2_mem_open.1 u2_mem_open.1 u2_ne_q2

/-- Boundary witness: because `Real.log 0 = 0` in Lean's real logarithm, `logScore` is NOT proper
on the full closed simplex `probSimplex (Fin 2)`. -/
example : ¬ (logScore (Fin 2)).IsProper := by
  intro h
  have hle := ScoringRule.IsProperOn.expectedScore_le h u2_mem_open.1 e1_mem_simplex
  simp only [ScoringRule.expectedScore_apply, logScore_score, Fin.sum_univ_two, u2, e1,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.log_zero, Real.log_one, mul_zero,
    add_zero] at hle
  have hlog_neg : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith

/-! ### Negative witnesses: constant rule and non-proper linear rule -/

/-- A constant scoring rule is proper but not strictly proper on `Fin 2`. -/
example :
    (⟨fun _ _ => (1 : ℝ)⟩ : ScoringRule (Fin 2)).IsProper ∧
      ¬ (⟨fun _ _ => (1 : ℝ)⟩ : ScoringRule (Fin 2)).IsStrictlyProper := by
  constructor
  · exact ScoringRule.isProperOn_iff.2 fun _ _ _ _ => le_rfl
  · intro h
    have hlt := ScoringRule.IsStrictlyProperOn.expectedScore_lt h
      q2_mem_open.1 u2_mem_open.1 u2_ne_q2
    simp only [ScoringRule.expectedScore_apply] at hlt
    exact lt_irrefl _ hlt

/-- The linear scoring rule `S(p, ω) = p ω` is NOT proper on `Fin 2`: under belief `(3/4, 1/4)`,
reporting `(1, 0)` beats truthful reporting (`3/4 > 5/8`). -/
example : ¬ (⟨fun p ω => p ω⟩ : ScoringRule (Fin 2)).IsProper := by
  intro h
  have hle := ScoringRule.IsProperOn.expectedScore_le h q2_mem_open.1 e0_mem_simplex
  norm_num [ScoringRule.expectedScore_apply, q2, e0, Fin.sum_univ_two] at hle

/-! ### Savage / Bregman divergence witness -/

/-- The Bregman divergence of `G(p) = ∑ p^2` between `q2` and `u2` is `1/8`, matching the
quadratic expected-score gap. -/
example :
    bregmanDivergence (fun p : Fin 2 → ℝ => ∑ i, p i ^ 2) (fun p i => 2 * p i) q2 u2 = 1 / 8 := by
  norm_num [bregmanDivergence_apply, dotProduct, q2, u2, Fin.sum_univ_two]

/-- The quadratic score satisfies the Savage characterization on `probSimplex (Fin 2)`. -/
example :
    ∃ G g, StrictConvexOn ℝ (probSimplex (Fin 2)) G ∧
      (∀ p ∈ probSimplex (Fin 2), ∀ q ∈ probSimplex (Fin 2), q ≠ p →
        G p + (q - p) ⬝ᵥ g p < G q) ∧
      (∀ p ∈ probSimplex (Fin 2), ∀ ω,
        (quadraticScore (Fin 2)).score p ω = (savageScoringRule G g).score p ω) :=
  (isStrictlyProperOn_iff_exists_savage (Set.Subset.refl _) convex_probSimplex
    (quadraticScore (Fin 2))).mp isStrictlyProper_quadraticScore

/-! ### Hanson's LMSR concrete witnesses -/

/-- At zero shares on `Fin 3`, LMSR prices are `(1/3, 1/3, 1/3)` and cost is `2 * log 3`. -/
example :
    (∀ i : Fin 3, lmsrPrice 2 (0 : Fin 3 → ℝ) i = 1 / 3) ∧
      lmsrCost 2 (0 : Fin 3 → ℝ) = 2 * Real.log 3 := by
  constructor
  · intro i
    rw [lmsrPrice_zero]
    norm_num
  · rw [lmsrCost_zero]
    norm_num

/-- Translation equivariance on `Fin 2`: shifting shares by `+3` adds `3` to LMSR cost and leaves
softmax prices invariant. -/
example :
    lmsrCost 2 (fun i : Fin 2 => ![1, 0] i + 3) = lmsrCost 2 ![1, 0] + 3 ∧
      lmsrPrice 2 (fun i : Fin 2 => ![1, 0] i + 3) = lmsrPrice 2 ![1, 0] :=
  ⟨lmsrCost_add_const two_pos ![1, 0] 3, lmsrPrice_add_const ![1, 0] 3⟩

/-- Sequential two-step LMSR trade on `Fin 3` matches two sequential logarithmic MSR updates
pointwise and has worst-case market-maker loss bounded by `2 * log 3`. -/
example (ω : Fin 3) :
    let qs : ℕ → Fin 3 → ℝ := fun t =>
      match t with
      | 0 => 0
      | 1 => ![1, 0, 0]
      | _ => ![1, 2, -1]
    ∑ t ∈ range 2, lmsrTraderPayoff 2 (qs t) (qs (t + 1)) ω =
      msrTotalPayoff ((logScore (Fin 3)).affine 2 0) (fun t => lmsrPrice 2 (qs t)) 2 ω ∧
    ∑ t ∈ range 2, lmsrTraderPayoff 2 (qs t) (qs (t + 1)) ω ≤ 2 * Real.log 3 := by
  refine ⟨sum_lmsrTraderPayoff_eq_msrTotalPayoff two_pos _ 2 ω, ?_⟩
  have h := lmsrTraderPayoff_zero_seq_le (Ω := Fin 3) two_pos (qs := fun t =>
    match t with
    | 0 => 0
    | 1 => ![1, 0, 0]
    | _ => ![1, 2, -1]) rfl 2 ω
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using h

/-- Concrete binary LMSR gradient at zero shares: `∂C / ∂q_0 = 1/2`. -/
example :
    HasDerivAt (fun t : ℝ => lmsrCost 1 (Function.update (0 : Fin 2 → ℝ) 0 t)) (1 / 2) 0 := by
  have h := hasDerivAt_lmsrCost_update (Ω := Fin 2) one_pos (0 : Fin 2 → ℝ) 0
  rw [lmsrPrice_zero] at h
  simpa only [Pi.zero_apply, Fintype.card_fin, Nat.cast_ofNat, one_div] using h

/-- Log-inversion on `q3 = (1/2, 1/3, 1/6)` recovers exact prices and zero LMSR cost. -/
example :
    lmsrPrice 2 (fun i => 2 * Real.log (q3 i)) = q3 ∧
      lmsrCost 2 (fun i => 2 * Real.log (q3 i)) = 0 :=
  ⟨lmsrPrice_log_eq two_pos q3_mem_open, lmsrCost_log_eq_zero two_pos q3_mem_open⟩

/-- Tightness witness on `Fin 2`: there exists a share vector whose market-maker loss under
`b = 1` exceeds `log 2 - 1 / 100`. -/
example : ∃ q : Fin 2 → ℝ, Real.log 2 - 1 / 100 < lmsrTraderPayoff 1 0 q 0 := by
  have h := exists_lmsrTraderPayoff_zero_gt (Ω := Fin 2) one_pos 0 (by norm_num : (0 : ℝ) < 1 / 100)
  simpa only [one_mul, Fintype.card_fin, Nat.cast_ofNat] using h

end CslibFrontierTests.PredictionMarketNRTV
