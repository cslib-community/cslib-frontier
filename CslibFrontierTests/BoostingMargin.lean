/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.MachineLearning.Boosting.Margin
public import CslibFrontier.MachineLearning.Rademacher.Linear

/-!
# Checked clients for convex-hull Rademacher complexity, uniform margin bounds, and AdaBoost margins

Exercises:
* `CslibFrontier.MachineLearning.Rademacher.ConvexHull`: equality of empirical and population
  Rademacher complexity for `convexHull ℝ (signClass stumps)` on `Fin 3`, together with a genuine
  strict interior convex combination not in `signClass stumps` (witnessing `convexHull ℝ F ≠ F`)
  and the empty-class boundary.
* `CslibFrontier.MachineLearning.Rademacher.UniformMargin`: strict monotonicity of `marginLoss` in
  `ρ`, and instantiations of `uniform_rademacherComplexity_margin_bound` and
  `uniform_empiricalRademacherComplexity_margin_bound` (including a `linearPredictors` client).
* `CslibFrontier.MachineLearning.Boosting.Margin`: the three-point sample
  `0 ↦ true, 1 ↦ false, 2 ↦ true` on `Fin 3` with three decision stumps (`vcDim ≤ 1`). No single
  stump is consistent with the sample, yet the least-weight stump learner has edge `1/6`. At
  `T = 45` rounds, `marginCount_normalizedScore_le_exp` certifies that **every** training point
  attains signed margin strictly greater than `1/12` (stronger than zero training error). Also
  instantiates `adaBoost_uniform_margin_bound_vc` and `adaBoost_generalization_bound_of_edge` at
  `d = 1`, `m = 3`.
-/

public section

namespace CslibFrontierTests.BoostingMargin

open Finset Real
open Cslib.BitString Cslib.MachineLearning Cslib.MachineLearning.Boosting
open Cslib.MachineLearning.PACLearning

/-- The three-point labeled sample `0 ↦ true, 1 ↦ false, 2 ↦ true` on `Fin 3`. -/
def sample : Fin 3 → Fin 3 × Bool := ![(0, true), (1, false), (2, true)]

/-- The constant stump `true`, which errs only on point `1`. -/
def constTrue : Fin 3 → Bool := fun _ => true

/-- The stump `x < 1`, which errs only on point `2`. -/
def below1 : Fin 3 → Bool := fun x => decide (x.val < 1)

/-- The stump `1 < x`, which errs only on point `0`. -/
def above1 : Fin 3 → Bool := fun x => decide (1 < x.val)

/-- The base concept class consisting of the three decision stumps. -/
def stumps : ConceptClass (Fin 3) Bool := {constTrue, below1, above1}

/-- The weighted errors of the three stumps on `sample`. -/
theorem weightedError_constTrue (D : Fin 3 → ℝ) : weightedError sample D constTrue = D 1 := by
  rw [weightedError, sum_filter, Fin.sum_univ_three]
  simp [sample, constTrue]

theorem weightedError_below1 (D : Fin 3 → ℝ) : weightedError sample D below1 = D 2 := by
  rw [weightedError, sum_filter, Fin.sum_univ_three]
  simp [sample, below1]

theorem weightedError_above1 (D : Fin 3 → ℝ) : weightedError sample D above1 = D 0 := by
  rw [weightedError, sum_filter, Fin.sum_univ_three]
  simp [sample, above1]

/-- None of the three stumps is consistent with the sample. -/
theorem no_stump_consistent :
    constTrue (sample 1).1 ≠ (sample 1).2 ∧
    below1 (sample 2).1 ≠ (sample 2).2 ∧
    above1 (sample 0).1 ≠ (sample 0).2 := by
  decide

/-- Weak learner returning a stump erring only on the point of least weight. -/
noncomputable def stumpLearner (D : Fin 3 → ℝ) : Fin 3 → Bool :=
  if D 1 ≤ D 0 ∧ D 1 ≤ D 2 then constTrue else if D 2 ≤ D 0 then below1 else above1

/-- Every hypothesis returned by `stumpLearner` belongs to `stumps`. -/
theorem stumpLearner_mem (D : Fin 3 → ℝ) : stumpLearner D ∈ stumps := by
  unfold stumpLearner stumps
  split_ifs <;> simp

/-- `stumpLearner` is a weak learner with edge `1 / 6`. -/
theorem isWeakLearner_stumpLearner : IsWeakLearner sample stumpLearner (1 / 6) := by
  intro D _ hD
  rw [Fin.sum_univ_three] at hD
  unfold stumpLearner
  split_ifs with h1 h2
  · rw [weightedError_constTrue]; linarith [h1.1, h1.2]
  · rw [weightedError_below1]
    have h2' : D 2 ≤ D 1 := by
      by_contra h
      push Not at h
      exact h1 ⟨by linarith, by linarith⟩
    linarith
  · rw [weightedError_above1]
    have h0' : D 0 ≤ D 1 := by
      by_contra h
      push Not at h
      exact h1 ⟨by linarith, by linarith⟩
    linarith

/-- Because `stumps` has cardinality `3 < 2 ^ 2`, every set it shatters has size at most `1`. -/
theorem stumps_shattered_card_le_one :
    ∀ W : Finset (Fin 3), SetShatters stumps ↑W → W.card ≤ 1 := by
  classical
  intro W hW
  by_contra hgt
  have h2 : 2 ≤ W.card := by omega
  let S : Finset (Fin 3 → Bool) := {constTrue, below1, above1}
  have hcard : S.card ≤ 3 :=
    card_insert_le _ _ |>.trans (Nat.succ_le_succ (card_insert_le _ _ |>.trans (by simp)))
  let restrict : (Fin 3 → Bool) → Finset (Fin 3) := fun c => W.filter fun x => c x = true
  have hpow : W.powerset ⊆ S.image restrict := by
    intro T hT
    have hTW : (T : Set (Fin 3)) ⊆ (W : Set (Fin 3)) := Finset.mem_powerset.mp hT
    obtain ⟨c, hc, hce⟩ := hW ↑T hTW
    refine mem_image.mpr ⟨c, ?_, ?_⟩
    · simp only [stumps, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      simpa [S] using hc
    · ext x
      simp only [restrict, mem_filter]
      have hx := Set.ext_iff.mp hce x
      simpa [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, and_comm] using hx
  have hle : 2 ^ W.card ≤ S.card := by
    calc 2 ^ W.card = W.powerset.card := (card_powerset W).symm
      _ ≤ (S.image restrict).card := card_le_card hpow
      _ ≤ S.card := card_image_le
  have h4 : 4 ≤ 2 ^ W.card := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W.card := Nat.pow_le_pow_right (by norm_num) h2
  omega

/-- A genuine midpoint convex combination of `constTrue` and `below1` lies in
`convexHull ℝ (signClass stumps)` yet is strictly outside `signClass stumps` (it takes value `0`
at `2`, while every function in `signClass stumps` is `±1`-valued). -/
noncomputable def midpointScore : Fin 3 → ℝ :=
  (1 / 2 : ℝ) • (fun x => signVal (constTrue x)) +
    (1 / 2 : ℝ) • (fun x => signVal (below1 x))

theorem midpointScore_mem_convexHull : midpointScore ∈ convexHull ℝ (signClass stumps) := by
  refine (convex_convexHull ℝ (signClass stumps))
    (subset_convexHull ℝ _ (mem_signClass.2 ⟨constTrue, by simp [stumps], rfl⟩))
    (subset_convexHull ℝ _ (mem_signClass.2 ⟨below1, by simp [stumps], rfl⟩))
    (by norm_num) (by norm_num) (by norm_num)

theorem midpointScore_not_mem_signClass : midpointScore ∉ signClass stumps := by
  intro h
  obtain ⟨c, -, hc⟩ := mem_signClass.1 h
  have h2 := congrFun hc 2
  have hm : midpointScore 2 = 0 := by
    simp [midpointScore, constTrue, below1, signVal]
  rw [hm] at h2
  have habs := abs_signVal (c 2)
  rw [h2, abs_zero] at habs
  norm_num at habs

theorem midpointScore_bounded (x : Fin 3) : |midpointScore x| ≤ 1 :=
  abs_le_of_mem_convexHull (fun _ hf => abs_le_one_of_mem_signClass hf)
    midpointScore_mem_convexHull x

/-- Empirical Rademacher complexity is invariant under taking `convexHull ℝ (signClass stumps)`. -/
theorem empirical_rademacher_convexHull_stumps :
    empiricalRademacherComplexity (convexHull ℝ (signClass stumps)) (fun i => (sample i).1) =
      empiricalRademacherComplexity (signClass stumps) (fun i => (sample i).1) :=
  empiricalRademacherComplexity_convexHull (fun _ hf => abs_le_one_of_mem_signClass hf) _

/-- Empty-class boundary check for `empiricalRademacherComplexity_convexHull`. -/
theorem empirical_rademacher_convexHull_empty :
    empiricalRademacherComplexity (convexHull ℝ (∅ : Set (Fin 3 → ℝ))) (fun i => (sample i).1) =
      0 := by
  rw [empiricalRademacherComplexity_convexHull (B := 0) (fun _ h => absurd h (Set.notMem_empty _)),
    empiricalRademacherComplexity_empty]

/-- Strict monotonicity check for `marginLoss` in `ρ` at `u = 1/4`. -/
theorem marginLoss_strict_step : marginLoss (1 / 2) (1 / 4) < marginLoss 1 (1 / 4) := by
  rw [marginLoss_of_mem_Icc (by norm_num) ⟨by norm_num, by norm_num⟩,
    marginLoss_of_mem_Icc one_pos ⟨by norm_num, by norm_num⟩]
  norm_num

/-- `normalizedScore` belongs to `convexHull ℝ (signClass stumps)` for every `T > 0`. -/
theorem stump_normalizedScore_mem_convexHull {T : ℕ} (hT : 0 < T) :
    normalizedScore sample stumpLearner T ∈ convexHull ℝ (signClass stumps) :=
  normalizedScore_mem_convexHull hT
    (fun t _ => by rw [rounds_hyp]; exact stumpLearner_mem _)
    (fun t _ => by
      have h := isWeakLearner_stumpLearner.rounds_error_le t
      linarith)

/-- Non-vacuous check of `marginFactor_lt_one` at `γ = 1/6, ρ = 1/6`. -/
theorem stump_marginFactor_lt_one :
    (1 - 2 * (1 / 6 : ℝ)) ^ (1 - (1 / 6 : ℝ)) *
      (1 + 2 * (1 / 6 : ℝ)) ^ (1 + (1 / 6 : ℝ)) < 1 :=
  marginFactor_lt_one (by norm_num) (by norm_num) (by norm_num) (le_refl _)

/-- Elementary check `exp (-(5 / 4)) < 1 / 3` via the degree-2 Taylor lower bound for `exp`. -/
private theorem exp_neg_five_fourths_lt_one_third : exp (-(5 / 4 : ℝ)) < 1 / 3 := by
  have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 5 / 4 by norm_num) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero, Nat.factorial_one,
    Nat.factorial_two, pow_zero, pow_one, Nat.cast_one, Nat.cast_ofNat, zero_add] at hsum
  have hgt : (3 : ℝ) < exp (5 / 4) := by norm_num at hsum; linarith
  rw [exp_neg, one_div]
  exact inv_lt_inv₀ (exp_pos _) (by norm_num) |>.mpr hgt

/-- After `45` rounds of AdaBoost on `sample` with `stumpLearner` (edge `1 / 6`), **every**
training point achieves signed margin strictly greater than `1 / 12` (stronger than zero training
error). -/
theorem stump_all_margins_gt_one_twelfth (i : Fin 3) :
    (1 / 12 : ℝ) < signVal (sample i).2 * normalizedScore sample stumpLearner 45 (sample i).1 := by
  have hbound := marginCount_normalizedScore_le_exp sample stumpLearner (T := 45)
    (by norm_num) (γ := 1 / 6) (ρ := 1 / 12) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) fun t _ => isWeakLearner_stumpLearner.rounds_error_le t
  have hexp : exp (-(2 * (1 / 6 : ℝ) * (1 / 6 - 1 / 12) * (45 : ℕ))) = exp (-(5 / 4 : ℝ)) := by
    push_cast
    congr 1
    norm_num
  rw [hexp] at hbound
  have hlt : ((univ.filter fun j : Fin 3 =>
      signVal (sample j).2 * normalizedScore sample stumpLearner 45 (sample j).1 ≤
        (1 / 12 : ℝ)).card : ℝ) / 3 < 1 / 3 :=
    hbound.trans_lt exp_neg_five_fourths_lt_one_third
  have hcard : (univ.filter fun j : Fin 3 =>
      signVal (sample j).2 * normalizedScore sample stumpLearner 45 (sample j).1 ≤
        (1 / 12 : ℝ)).card = 0 := by
    have hlt' : ((univ.filter fun j : Fin 3 =>
        signVal (sample j).2 * normalizedScore sample stumpLearner 45 (sample j).1 ≤
          (1 / 12 : ℝ)).card : ℝ) < 1 := by linarith
    exact Nat.lt_one_iff.mp (by exact_mod_cast hlt')
  rw [card_eq_zero, filter_eq_empty_iff] at hcard
  exact lt_of_not_ge (hcard (mem_univ i))

/-- Instantiation of `adaBoost_uniform_margin_bound_vc` on `Fin 3` (`d = 1`, `m = 3`). -/
theorem stumps_adaBoost_uniform_bound (D : PMF (Fin 3 × Bool)) :
    ((Cslib.Probability.PMF.pi fun _ : Fin 3 => D).toOuterMeasure
      {S | ∃ (A : (Fin 3 → ℝ) → Fin 3 → Bool) (T : ℕ), 0 < T ∧
        (∀ t < T, (rounds S A t).hyp ∈ stumps) ∧
        (∀ t < T, (rounds S A t).error S < 1 / 2) ∧
        ∃ ρ ∈ Set.Ioc (0 : ℝ) 1,
          empiricalMarginLoss ρ (normalizedScore S A T) S +
            4 / ρ * √(2 * ((1 : ℕ) * Real.log (Real.exp 1 * (3 : ℕ) / (1 : ℕ))) / (3 : ℕ)) +
            √(Real.log (Real.logb 2 (2 / ρ)) / (3 : ℕ)) +
            √(Real.log (2 / (1 / 10 : ℝ)) / (2 * (3 : ℕ))) <
          (D.toOuterMeasure {p | adaBoost S A T p.1 ≠ p.2}).toReal}).toReal ≤ (1 / 10 : ℝ) :=
  adaBoost_uniform_margin_bound_vc D (m := 3) (d := 1) (by norm_num)
    stumps_shattered_card_le_one (by norm_num) (by norm_num)

/-- Instantiation of the end-to-end `adaBoost_generalization_bound_of_edge` on `stumps`. -/
theorem stumps_adaBoost_edge_bound (D : PMF (Fin 3 × Bool)) :
    ((Cslib.Probability.PMF.pi fun _ : Fin 3 => D).toOuterMeasure
      {S | ∃ (A : (Fin 3 → ℝ) → Fin 3 → Bool) (T : ℕ) (γ ρ : ℝ),
        0 < T ∧ 0 < γ ∧ γ < 1 / 2 ∧ 0 < ρ ∧ ρ ≤ γ ∧
        (∀ t < T, (rounds S A t).hyp ∈ stumps) ∧
        (∀ t < T, (rounds S A t).error S ≤ 1 / 2 - γ) ∧
          exp (-(2 * γ * (γ - ρ) * T)) +
            4 / ρ * √(2 * ((1 : ℕ) * Real.log (Real.exp 1 * (3 : ℕ) / (1 : ℕ))) / (3 : ℕ)) +
            √(Real.log (Real.logb 2 (2 / ρ)) / (3 : ℕ)) +
            √(Real.log (2 / (1 / 10 : ℝ)) / (2 * (3 : ℕ))) <
          (D.toOuterMeasure {p | adaBoost S A T p.1 ≠ p.2}).toReal}).toReal ≤ (1 / 10 : ℝ) :=
  adaBoost_generalization_bound_of_edge D (m := 3) (d := 1) (by norm_num)
    stumps_shattered_card_le_one (by norm_num) (by norm_num)

/-- Early-stopping boundary check: against a consistent weak learner (`ε₀ = 0`), `normalizedScore`
stops at round `0` and attains signed margin `+1` on every sample point. -/
theorem consistent_learner_margin_eq_one (i : Fin 3) :
    signVal (sample i).2 *
      normalizedScore sample (fun _ x => decide (x ≠ 1)) 5 (sample i).1 = 1 := by
  have hzero : (rounds sample (fun _ x => decide (x ≠ 1)) 0).error sample = 0 := by
    have hcons : ∀ j : Fin 3, decide ((sample j).1 ≠ 1) = (sample j).2 := by decide
    rw [Round.error_def, rounds_hyp, weightedError]
    refine Finset.sum_eq_zero fun j hj => ?_
    exact absurd (hcons j) (Finset.mem_filter.mp hj).2
  have hex : ∃ t < 5, (rounds sample (fun _ x => decide (x ≠ 1)) t).error sample = 0 :=
    ⟨0, by norm_num, hzero⟩
  rw [normalizedScore_of_exists_error_zero sample _ hex]
  dsimp only
  have heq := hyp_eq_of_error_eq_zero sample (fun _ x => decide (x ≠ 1)) (Nat.find_spec hex).2 i
  rw [heq, signVal_mul_self]

/-- Interoperability client: uniform-in-`ρ` margin bound for `ℓ₂`-bounded `linearPredictors`. -/
theorem linear_uniform_margin_client (D : PMF (Fin 3 × Bool))
    (φ : Fin 3 → EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ R) :
    ((Cslib.Probability.PMF.pi fun _ : Fin 4 => D).toOuterMeasure
      {S | ∃ h ∈ linearPredictors φ 1, ∃ ρ ∈ Set.Ioc (0 : ℝ) 1,
        empiricalMarginLoss ρ h S +
          4 / ρ * rademacherComplexity (D.map Prod.fst) (linearPredictors φ 1) 4 +
          √(Real.log (Real.logb 2 (2 * 1 / ρ)) / 4) +
          √(Real.log (2 / (1 / 10 : ℝ)) / (2 * 4)) <
        (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal}).toReal ≤ (1 / 10 : ℝ) :=
  uniform_rademacherComplexity_margin_bound D (m := 4) (by norm_num)
    (fun _ hh z => abs_le_of_mem_linearPredictors hφ hh z) zero_lt_one (by norm_num)

end CslibFrontierTests.BoostingMargin
