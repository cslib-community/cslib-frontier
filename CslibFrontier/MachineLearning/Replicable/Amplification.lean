/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Finset.Median
public import CslibFrontier.MachineLearning.Replicable.Basic
public import CslibFrontier.MachineLearning.Replicable.Composition
public import CslibFrontier.MachineLearning.Replicable.Rounding
public import CslibFrontier.Probability.Collision
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.MachineLearning.Replicable.BiasEstimation
import CslibFrontier.Probability.IID.Event
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Markov
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Tactic.FinsetCard
import CslibFrontier.Tactic.PMFSwap

/-!
# Amplification of accuracy and replicability

This module formalizes confidence and replicability amplification theorems for shared-seed
replicable algorithms [ImpagliazzoLeiPitassiSorrell2022]:

* **Confidence amplification**: repeating an algorithm `2 * (r + 1)` times with independent shared
  seeds and taking `majorityVote` (for `Bool` outputs) or `medianOfRuns` (for `ℝ` outputs via
  `Cslib.median`) reduces failure probability from `β₀ ≤ 1 / 2` to `(4 * β₀ * (1 - β₀)) ^ (r + 1)`
  while scaling the disagreement parameter by `2 * (r + 1)`.
* **Finite-domain amplification (`amplifyFinite`)**: when the output space `α` is finite (`M = |α|`)
  and linearly ordered, any algorithm (with no replicability guarantee at all) whose failure
  probability satisfies `β₀ < 1 / (M + 1)` can be amplified to arbitrary `(ρ, β)` with **strong**
  (distribution-free) `ρ`-replicability by estimating empirical frequencies over `k` independent
  runs and thresholding against a single shared random threshold `i : Fin N`.
* **General-domain replicability amplification (`amplifyReplicability`)**:
  for any `[DecidableEq α]`, any algorithm that is weakly (or strongly) `ρ₀`-replicable with
  `ρ₀ < 1 / 2` can be amplified to arbitrary `ρ > 0` by sampling `T` candidate seeds, estimating
  collision rates and strict majorities, and picking the first candidate seed whose empirical
  collision rate crosses a single shared random threshold `i : Fin N`. When the input algorithm
  also has sufficiently small initial error `β₀ = O(β / T)` (with `β₀ / (a - δ)` union-bounded
  across the `T` candidate seeds by Markov's inequality in `isAccurateFor_amplifyReplicability`
  and `exists_amplifyReplicability_accurate`), `amplifyReplicability` also achieves `(good, β)`
  accuracy; unlike `amplifyFinite`, `pickFirstThresholded` does not assume `β₀ < 1 / (|α| + 1)`
  and therefore preserves small initial error rather than amplifying error from `≈ 1 / 2`.

## Main definitions

* `Cslib.MachineLearning.Replicable.majorityVote`: `Bool` confidence amplification.
* `Cslib.MachineLearning.Replicable.medianOfRuns`: `ℝ` confidence amplification via `Cslib.median`.
* `Cslib.MachineLearning.Replicable.amplifyFinite`: finite-domain heavy-hitter amplification.
* `Cslib.MachineLearning.Replicable.amplifyReplicability`: general-domain collision-threshold
  replicability amplification.

## Main results

* `Cslib.MachineLearning.Replicable.majorityVote_accurate`,
  `Cslib.MachineLearning.Replicable.majorityVote_replicable`,
  `Cslib.MachineLearning.Replicable.exists_majorityVote`: boolean majority amplification.
* `Cslib.MachineLearning.Replicable.medianOfRuns_accurate`,
  `Cslib.MachineLearning.Replicable.medianOfRuns_replicable`,
  `Cslib.MachineLearning.Replicable.exists_medianOfRuns`: median-of-runs amplification.
* `Cslib.MachineLearning.Replicable.isReplicable_amplifyFinite`,
  `Cslib.MachineLearning.Replicable.isAccurateFor_amplifyFinite`,
  `Cslib.MachineLearning.Replicable.exists_amplifyFinite`: finite-domain amplification from
  `β₀ < 1 / (|α| + 1)` to arbitrary strong `ρ` and accuracy `β`.
* `Cslib.MachineLearning.Replicable.disagreeProb_amplifyReplicability_le`,
  `Cslib.MachineLearning.Replicable.isAccurateFor_amplifyReplicability`,
  `Cslib.MachineLearning.Replicable.exists_amplifyReplicability`,
  `Cslib.MachineLearning.Replicable.exists_amplifyReplicability_accurate`: amplifying
  `ρ₀ < 1 / 2` to arbitrary `ρ > 0` over any `[DecidableEq α]`, with preserved accuracy under
  `O(β / T)` initial error.

## References

* [Impagliazzo, Lei, Pitassi, Sorrell (STOC 2022)][ImpagliazzoLeiPitassiSorrell2022],
  *Reproducibility in Learning* (paper PDF not directly inspected in this formalization;
  definitions and finite/general amplification theorems are formalized directly in Lean).
-/

public section

namespace Cslib.MachineLearning.Replicable

universe u v w

open Cslib.Probability
open scoped ENNReal

section Helpers

private theorem exists_pow_four_mul_le {β₀ β : ℝ} (hnn : 0 ≤ β₀) (hlt : β₀ < 1 / 2)
    (hβ : 0 < β) : ∃ r : ℕ, (4 * β₀ * (1 - β₀)) ^ (r + 1) ≤ β := by
  have hbase0 : 0 ≤ 4 * β₀ * (1 - β₀) := by nlinarith
  have hbase1 : 4 * β₀ * (1 - β₀) < 1 := by
    nlinarith [sq_pos_of_pos (show 0 < 1 - 2 * β₀ by linarith)]
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hβ hbase1
  exact ⟨r, (pow_le_pow_of_le_one hbase0 hbase1.le (Nat.le_succ r)).trans hr.le⟩

private theorem exists_neZero_mul_pow_le (M : ℝ) {r ε : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hε : 0 < ε) : ∃ (n : ℕ) (_ : NeZero n), M * r ^ n ≤ ε := by
  have hlim : Filter.Tendsto (fun n : ℕ => M * r ^ n) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).const_mul M
  obtain ⟨n, hlt, hn⟩ := (((tendsto_order.1 hlim).2 ε hε).and
    (Filter.eventually_ge_atTop (1 : ℕ))).exists
  exact ⟨n, ⟨(Nat.succ_le_iff.1 hn).ne'⟩, hlt.le⟩

private theorem exp_decay_exists (M : ℝ) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (_ : NeZero k), M * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)) ≤ ε := by
  have hr : Real.exp (-2 * δ ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hδ])
  obtain ⟨k, hk, hle⟩ := exists_neZero_mul_pow_le (M * 2) (Real.exp_nonneg _) hr hε
  refine ⟨k, hk, ?_⟩
  rwa [show -2 * (k : ℝ) * δ ^ 2 = k * (-2 * δ ^ 2) by ring, Real.exp_nat_mul, ← mul_assoc]

private theorem exists_nat_div_le (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : NeZero N), M / N ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (M / ε) 0)
  have hNpos : 0 < N := by exact_mod_cast (le_max_right (M / ε) 0).trans_lt hN
  refine ⟨N, ⟨hNpos.ne'⟩, (div_le_iff₀ (Nat.cast_pos.mpr hNpos)).mpr ?_⟩
  have hlt := (div_lt_iff₀ hε).mp ((le_max_left (M / ε) 0).trans_lt hN)
  linarith

private theorem isAccurateFor_replicate_map {X : Type u} {Ω : Type v} {α : Type w} {m : ℕ}
    {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)} {good : PMF X → Set α} {β₀ : ℝ}
    (hacc : IsAccurateFor A 𝒟 good β₀) (hβ₀ : β₀ ≤ 1 / 2) (r : ℕ)
    (agg : (Fin (2 * (r + 1)) → α) → α) (bad : PMF X → α → Bool)
    (hbad_eq : ∀ D x, bad D x = true ↔ x ∉ good D)
    (hsub : ∀ D ∈ 𝒟, ∀ v : Fin (2 * (r + 1)) → α, agg v ∉ good D →
      r + 1 ≤ (Finset.univ.filter fun j => bad D (v j) = true).card) :
    IsAccurateFor ((A.replicate (2 * (r + 1))).map agg) 𝒟 good
      ((4 * β₀ * (1 - β₀)) ^ (r + 1)) := by
  intro D hD
  have hq : (((A.marginal D).map (bad D)) true).toReal ≤ β₀ := by
    have hpre : bad D ⁻¹' {true} = (good D)ᶜ := Set.ext fun x => by simpa using hbad_eq D x
    simpa only [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, hpre] using
      hacc D hD
  rw [Algorithm.marginal_map, Algorithm.marginal_replicate, PMF.toOuterMeasure_map_apply]
  refine (Probability.PMF.toOuterMeasure_toReal_mono _
    (t := (fun v : Fin (2 * (r + 1)) → α => fun j => bad D (v j)) ⁻¹'
      {w : Fin (2 * (r + 1)) → Bool |
        r + 1 ≤ (Finset.univ.filter fun j => w j = true).card})
    fun v hv => hsub D hD v hv).trans ?_
  rw [← PMF.toOuterMeasure_map_apply, (Probability.PMF.iid_map (A.marginal D) (bad D) _).symm]
  exact Probability.PMF.iid_card_ge_le hq hβ₀ (r + 1)

private theorem thresholdRound_union_disagree_le {ι : Type*} [Fintype ι] {a b δ : ℝ}
    (hab : a < b) (N : ℕ) [NeZero N] {x₁ x₂ μ : ι → ℝ}
    (hx₁ : ∀ j, |x₁ j - μ j| ≤ δ) (hx₂ : ∀ j, |x₂ j - μ j| ≤ δ)
    {E : Set (Fin N)}
    (hpre : E ⊆ ⋃ j ∈ (Finset.univ : Finset ι),
      {i : Fin N | thresholdRound a b N i (x₁ j) ≠ thresholdRound a b N i (x₂ j)}) :
    ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure E).toReal ≤
      (Fintype.card ι : ℝ) * (2 * δ / (b - a) + 1 / N) := by
  refine ((Probability.PMF.toOuterMeasure_toReal_mono _ hpre).trans
    (Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le _ Finset.univ _)).trans ?_
  calc ∑ j : ι, ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
          {i : Fin N | thresholdRound a b N i (x₁ j) ≠ thresholdRound a b N i (x₂ j)}).toReal
      ≤ ∑ _j : ι, (2 * δ / (b - a) + 1 / N) := Finset.sum_le_sum fun j _ => by
        have hdist : |x₁ j - x₂ j| ≤ 2 * δ := (abs_sub_le (x₁ j) (μ j) (x₂ j)).trans
          (by rw [abs_sub_comm (μ j)]; linarith [hx₁ j, hx₂ j])
        have hba : 0 < b - a := sub_pos.mpr hab
        exact (thresholdRound_disagree_le hab (x₁ j) (x₂ j)).trans (by gcongr)
    _ = (Fintype.card ι : ℝ) * (2 * δ / (b - a) + 1 / N) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem paired_bind_disagree_le {β α : Type*} {N : ℕ} [NeZero N]
    (μ : PMF β) (good : Set β) (f : Fin N → β → α) {e₁ e₂ : ℝ}
    (he₁ : (μ.toOuterMeasure goodᶜ).toReal ≤ e₁) (he₂ : 0 ≤ e₂)
    (hstep : ∀ v₁ ∈ good, ∀ v₂ ∈ good,
      ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
        {i | f i v₁ ≠ f i v₂}).toReal ≤ e₂) :
    ((μ.bind fun v₁ => μ.bind fun v₂ =>
      (Probability.PMF.uniformOfFintype (Fin N)).map fun i => (f i v₁, f i v₂)).toOuterMeasure
      {p : α × α | p.1 ≠ p.2}).toReal ≤ 2 * e₁ + e₂ := by
  have he₁_nn : 0 ≤ e₁ := ENNReal.toReal_nonneg.trans he₁
  have houter := Probability.PMF.toOuterMeasure_bind_failure_toReal_le μ
    (fun v₁ => μ.bind fun v₂ =>
      (Probability.PMF.uniformOfFintype (Fin N)).map fun i => (f i v₁, f i v₂))
    good {p : α × α | p.1 ≠ p.2} (add_nonneg he₁_nn he₂) fun v₁ _ hv₁ => by
      refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le μ _ good _ he₂
        fun v₂ _ hv₂ => ?_).trans (add_le_add he₁ le_rfl)
      rw [PMF.toOuterMeasure_map_apply]
      exact hstep v₁ hv₁ v₂ hv₂
  linarith

end Helpers

/-! ### Confidence amplification: majority vote and median-of-runs -/

section ConfidenceAmplification

variable {X : Type u} {Ω : Type v} {m : ℕ}

/-- Run a Boolean algorithm `2 * (r + 1)` times on disjoint blocks with independent shared seeds
and return the majority bit (breaking ties toward `true`). -/
@[expose] noncomputable def majorityVote (A : Algorithm X Ω Bool m) (r : ℕ) :
    Algorithm X (Fin (2 * (r + 1)) → Ω) Bool (2 * (r + 1) * m) :=
  (A.replicate (2 * (r + 1))).map fun v =>
    decide (r + 1 ≤ (Finset.univ.filter fun j => v j = true).card)

theorem majorityVote_replicable {A : Algorithm X Ω Bool m} {𝒟 : Set (PMF X)} {ρ : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) (r : ℕ) :
    IsReplicableFor (majorityVote A r) 𝒟 ((2 * (r + 1) : ℕ) * ρ) :=
  (h.replicate (k := 2 * (r + 1))).map _

theorem majorityVote_accurate {A : Algorithm X Ω Bool m} {𝒟 : Set (PMF X)}
    {target : PMF X → Bool} {β₀ : ℝ} (hacc : IsAccurateFor A 𝒟 (fun D => {target D}) β₀)
    (hβ₀ : β₀ ≤ 1 / 2) (r : ℕ) :
    IsAccurateFor (majorityVote A r) 𝒟 (fun D => {target D}) ((4 * β₀ * (1 - β₀)) ^ (r + 1)) :=
  isAccurateFor_replicate_map hacc hβ₀ r _ (fun D b => decide (b ≠ target D))
    (fun _ _ => by simp) fun D _ v hv => by
      cases ht : target D <;> simp only [ht, Set.mem_singleton_iff, ne_eq, decide_eq_true_eq,
        Bool.not_eq_false, Bool.not_eq_true] at hv ⊢
      · exact hv
      · finset_card

/-- For any Boolean algorithm with error `β₀ < 1 / 2` and any target `β > 0`, taking the majority
of `2 * (r + 1)` independent repetitions achieves failure probability at most `β`. -/
theorem exists_majorityVote {A : Algorithm X Ω Bool m} {𝒟 : Set (PMF X)}
    {target : PMF X → Bool} {β₀ β : ℝ} (hacc : IsAccurateFor A 𝒟 (fun D => {target D}) β₀)
    (hβ₀_nonneg : 0 ≤ β₀) (hβ₀ : β₀ < 1 / 2) (hβ : 0 < β) :
    ∃ r : ℕ, IsAccurateFor (majorityVote A r) 𝒟 (fun D => {target D}) β :=
  let ⟨r, hr⟩ := exists_pow_four_mul_le hβ₀_nonneg hβ₀ hβ
  ⟨r, (majorityVote_accurate hacc hβ₀.le r).mono hr⟩

/-- Run a real-valued algorithm `2 * (r + 1)` times on disjoint blocks with independent shared
seeds and output `Cslib.median`. -/
@[expose] noncomputable def medianOfRuns (A : Algorithm X Ω ℝ m) (r : ℕ) :
    Algorithm X (Fin (2 * (r + 1)) → Ω) ℝ (2 * (r + 1) * m) :=
  (A.replicate (2 * (r + 1))).map Cslib.median

theorem medianOfRuns_replicable {A : Algorithm X Ω ℝ m} {𝒟 : Set (PMF X)} {ρ : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) (r : ℕ) :
    IsReplicableFor (medianOfRuns A r) 𝒟 ((2 * (r + 1) : ℕ) * ρ) :=
  (h.replicate (k := 2 * (r + 1))).map _

theorem medianOfRuns_accurate {A : Algorithm X Ω ℝ m} {𝒟 : Set (PMF X)}
    {target : PMF X → ℝ} {ε β₀ : ℝ} (hacc : EstimatesFor A 𝒟 target ε β₀) (hβ₀ : β₀ ≤ 1 / 2)
    (r : ℕ) :
    EstimatesFor (medianOfRuns A r) 𝒟 target ε ((4 * β₀ * (1 - β₀)) ^ (r + 1)) :=
  isAccurateFor_replicate_map hacc hβ₀ r Cslib.median
    (fun D y => decide (ε < |y - target D|)) (fun _ _ => by simp [not_le]) fun D _ v hv => by
      simp only [Set.mem_ofPred_eq, ← not_le, decide_eq_true_eq] at hv ⊢
      have hnot : ¬ Fintype.card (Fin (2 * (r + 1))) <
          2 * (Finset.univ.filter fun j : Fin (2 * (r + 1)) => |v j - target D| ≤ ε).card :=
        fun hlt => hv (Cslib.abs_median_sub_le hlt)
      finset_card

/-- For any real estimator within `ε` except with probability `β₀ < 1 / 2` and any `β > 0`,
`medianOfRuns` achieves `(ε, β)` estimation accuracy. -/
theorem exists_medianOfRuns {A : Algorithm X Ω ℝ m} {𝒟 : Set (PMF X)}
    {target : PMF X → ℝ} {ε β₀ β : ℝ} (hacc : EstimatesFor A 𝒟 target ε β₀)
    (hβ₀_nonneg : 0 ≤ β₀) (hβ₀ : β₀ < 1 / 2) (hβ : 0 < β) :
    ∃ r : ℕ, EstimatesFor (medianOfRuns A r) 𝒟 target ε β :=
  let ⟨r, hr⟩ := exists_pow_four_mul_le hβ₀_nonneg hβ₀ hβ
  ⟨r, (medianOfRuns_accurate hacc hβ₀.le r).mono le_rfl hr⟩

end ConfidenceAmplification

/-! ### Finite-domain heavy-hitter amplification -/

section FiniteDomainAmplification

variable {X : Type u} {Ω : Type v} {α : Type w} {m : ℕ}

/-- Empirical frequency of `y : α` in a tuple `v : Fin k → α`. -/
@[expose] noncomputable def empFreq [DecidableEq α] (k : ℕ) (v : Fin k → α) (y : α) : ℝ :=
  ((Finset.univ.filter fun j : Fin k => v j = y).card : ℝ) / k

/-- Least element of `α` whose empirical frequency crosses `thresholdValue a b N i`, falling back
to `Finset.univ.min'` if none qualifies. -/
@[expose] noncomputable def pickThresholded [Fintype α] [Nonempty α] [LinearOrder α]
    (a b : ℝ) (N k : ℕ) (i : Fin N) (v : Fin k → α) : α :=
  let cand := Finset.univ.filter fun y : α => thresholdRound a b N i (empFreq k v y) = true
  if h : cand.Nonempty then cand.min' h else Finset.univ.min' Finset.univ_nonempty

/-- Finite-domain heavy-hitter amplification: runs `A` independently with fresh internal seeds on
`k` disjoint `m`-sample blocks, shares a single threshold `i : Fin N` across `[a, b)`, and
outputs the least element whose empirical frequency crosses `thresholdValue a b N i`. -/
@[expose] noncomputable def amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) (a b : ℝ) (k N : ℕ) [NeZero N] :
    Algorithm X (Fin N) α (k * m) where
  seed := Probability.PMF.uniformOfFintype (Fin N)
  run S i :=
    (PMF.piFin fun j : Fin k => A.output (BitString.block (m := k) (k := m) S j)).map fun v =>
      pickThresholded a b N k i v

private theorem iid_splitBlocks_output_eq_iid (A : Algorithm X Ω α m) (D : PMF X) (k : ℕ) :
    ((Probability.PMF.iid D (k * m)).bind fun S =>
      PMF.piFin fun j => A.output (BitString.block (m := k) (k := m) S j)) =
      Probability.PMF.iid (A.marginal D) k := by
  rw [iid_bind_piFin_block D k m fun _ => A.output, PMF.piFin_const]
  rfl

private theorem marginal_amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) (a b : ℝ) (k N : ℕ) [NeZero N] (D : PMF X) :
    (amplifyFinite A a b k N).marginal D =
      (Probability.PMF.uniformOfFintype (Fin N)).bind fun i =>
        (Probability.PMF.iid (A.marginal D) k).map fun v => pickThresholded a b N k i v := by
  rw [Algorithm.marginal_eq_seed_bind]
  simp only [amplifyFinite, ← iid_splitBlocks_output_eq_iid A D k, pmf_norm]

private theorem pairedOutput_amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) (a b : ℝ) (k N : ℕ) [NeZero N] (D : PMF X) :
    (amplifyFinite A a b k N).pairedOutput D =
      (Probability.PMF.iid (A.marginal D) k).bind fun v₁ =>
        (Probability.PMF.iid (A.marginal D) k).bind fun v₂ =>
          (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
            (pickThresholded a b N k i v₁, pickThresholded a b N k i v₂) := by
  simp only [Algorithm.pairedOutput, amplifyFinite, ← iid_splitBlocks_output_eq_iid A D k,
    pmf_norm]
  pmf_swap

private theorem empFreq_concentrates [DecidableEq α] (q : PMF α) (k : ℕ) [NeZero k]
    {δ : ℝ} (hδ : 0 ≤ δ) (y : α) :
    ((Probability.PMF.iid q k).toOuterMeasure
      {v : Fin k → α | δ < |empFreq k v y - (q y).toReal|}).toReal ≤
      2 * Real.exp (-2 * (k : ℝ) * δ ^ 2) := by
  let f : α → ℝ := fun z => if z = y then 1 else 0
  have hfreq (v : Fin k → α) : empFreq k v y = empiricalMean f v := by
    simp only [empFreq, empiricalMean, f, Finset.card_filter, Nat.cast_sum]
    congr 1; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  have hexp : (q y).toReal = distExpectation q f := by
    rw [distExpectation, tsum_eq_single y fun z hz => by simp [f, hz]]
    simp [f]
  have hf : ∀ z ∈ q.support, f z ∈ Set.Icc (0 : ℝ) 1 := fun z _ => by
    dsimp only [f]; split_ifs <;> simp
  have hmax : max ((1 : ℝ) - 0) 1 = 1 := by norm_num
  simpa only [hfreq, hexp, hmax, one_pow, div_one] using boundedMean_concentrates q f hf k hδ

private theorem empFreq_all_concentrates [Fintype α] [DecidableEq α] (q : PMF α) (k : ℕ)
    [NeZero k] {δ : ℝ} (hδ : 0 ≤ δ) :
    ((Probability.PMF.iid q k).toOuterMeasure
      {v : Fin k → α | ∃ y : α, δ < |empFreq k v y - (q y).toReal|}).toReal ≤
      (Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)) := by
  have hunion : {v : Fin k → α | ∃ y : α, δ < |empFreq k v y - (q y).toReal|} =
      ⋃ y ∈ (Finset.univ : Finset α), {v : Fin k → α | δ < |empFreq k v y - (q y).toReal|} := by
    ext v; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_univ, exists_true_left]
  rw [hunion]
  refine (Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le _ Finset.univ _).trans ?_
  refine (Finset.sum_le_sum fun y _ => empFreq_concentrates q k hδ y).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Strong replicability of `amplifyFinite`**: for any `a < b`, `k, N ≥ 1`, and `δ ≥ 0`,
`amplifyFinite A a b k N` is strongly `ρ`-replicable over **all** distributions `D : PMF X` with
`ρ = 2 * |α| * (2 * exp(-2 * k * δ^2)) + |α| * (2 * δ / (b - a) + 1 / N)`. -/
theorem isReplicable_amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) {a b δ : ℝ} (hab : a < b) (hδ : 0 ≤ δ) (k N : ℕ)
    [NeZero k] [NeZero N] :
    IsReplicable (amplifyFinite A a b k N)
      (2 * ((Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2))) +
        (Fintype.card α : ℝ) * (2 * δ / (b - a) + 1 / N)) := by
  intro D _
  rw [Algorithm.disagreeProb, pairedOutput_amplifyFinite]
  let good : Set (Fin k → α) := {v | ∀ y : α, |empFreq k v y - (A.marginal D y).toReal| ≤ δ}
  have hgoodc : ((Probability.PMF.iid (A.marginal D) k).toOuterMeasure goodᶜ).toReal ≤
      (Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)) := by
    have heq : goodᶜ = {v | ∃ y, δ < |empFreq k v y - (A.marginal D y).toReal|} :=
      Set.ext fun _ => by simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le, good]
    exact heq ▸ empFreq_all_concentrates (A.marginal D) k hδ
  have hba : 0 < b - a := sub_pos.mpr hab
  refine paired_bind_disagree_le _ good (fun i v => pickThresholded a b N k i v) hgoodc
    (by positivity) fun v₁ hv₁ v₂ hv₂ => thresholdRound_union_disagree_le hab N hv₁ hv₂ ?_
  intro i hi
  simp only [Set.mem_ofPred_eq, ne_eq, Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hi ⊢
  by_contra hnone
  push Not at hnone
  exact hi (by simp only [pickThresholded, hnone])

/-- **Accuracy of `amplifyFinite`**: if `A` errs with probability at most `β₀ < 1 / (|α| + 1)`
on `𝒟` and the threshold window `[a, b)` satisfies `β₀ + δ < a ≤ b ≤ (1 - β₀) / |α| - δ`, then
`amplifyFinite A a b k N` errs on `𝒟` with probability at most
`|α| * (2 * exp (-2 * k * δ^2))`. -/
theorem isAccurateFor_amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) {𝒟 : Set (PMF X)} {good : PMF X → Set α} {β₀ a b δ : ℝ}
    (hacc : IsAccurateFor A 𝒟 good β₀) (hab : a ≤ b) (hδ : 0 ≤ δ)
    (ha : β₀ + δ < a) (hb : b ≤ (1 - β₀) / Fintype.card α - δ)
    (k N : ℕ) [NeZero k] [NeZero N] :
    IsAccurateFor (amplifyFinite A a b k N) 𝒟 good
      ((Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2))) := by
  classical
  intro D hD
  have hM : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hβ₀_nn : 0 ≤ β₀ := ENNReal.toReal_nonneg.trans (hacc D hD)
  have hdiv_pos : 0 < (1 - β₀) / Fintype.card α := by linarith
  obtain ⟨y₀, _, hy₀_mass⟩ :
      ∃ y₀ ∈ good D, (1 - β₀) / Fintype.card α ≤ (A.marginal D y₀).toReal := by
    have hsum := (isAccurateFor_iff_prob_good.mp hacc) D hD
    rw [Probability.PMF.toOuterMeasure_apply_toReal] at hsum
    obtain ⟨y, _, hy⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
      (f := fun _ : α => (1 - β₀) / Fintype.card α)
      (g := fun y : α => if y ∈ good D then (A.marginal D y).toReal else 0) (by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_div_cancel₀ _ hM.ne'] using hsum)
    split_ifs at hy with hgood
    · exact ⟨y, hgood, hy⟩
    · exact (hdiv_pos.not_ge hy).elim
  rw [marginal_amplifyFinite]
  refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ Set.univ _
    (error := (Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)))
    (by positivity) fun i _ _ => ?_).trans_eq (by simp)
  rw [PMF.toOuterMeasure_map_apply]
  refine (Probability.PMF.toOuterMeasure_toReal_mono _
    (t := {v : Fin k → α | ∃ y : α, δ < |empFreq k v y - (A.marginal D y).toReal|})
    fun v hv => ?_).trans (empFreq_all_concentrates (A.marginal D) k hδ)
  by_contra hconc
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_lt]
    at hv hconc
  have hy₀_pass : thresholdRound a b N i (empFreq k v y₀) = true :=
    thresholdRound_true_of_right_le hab i (by linarith [(abs_sub_le_iff.mp (hconc y₀)).2])
  let cand := Finset.univ.filter fun y : α => thresholdRound a b N i (empFreq k v y) = true
  have hcand : cand.Nonempty := ⟨y₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy₀_pass⟩⟩
  have hmem : pickThresholded a b N k i v ∈ cand := by
    dsimp only [pickThresholded]
    rw [dite_eq_left_of_eq_true (eq_true hcand)]
    exact Finset.min'_mem cand hcand
  have hbad_mass : (A.marginal D (pickThresholded a b N k i v)).toReal ≤ β₀ := by
    rw [← PMF.toOuterMeasure_apply_singleton]
    exact (Probability.PMF.toOuterMeasure_toReal_mono _
      (Set.singleton_subset_iff.mpr hv)).trans (hacc D hD)
  have hfalse := thresholdRound_false_of_lt_left hab i
    (show empFreq k v (pickThresholded a b N k i v) < a by
      linarith [(abs_sub_le_iff.mp (hconc (pickThresholded a b N k i v))).1])
  exact absurd (Finset.mem_filter.mp hmem).2 (by rw [hfalse]; decide)

/-- **Finite-domain amplification theorem** [ImpagliazzoLeiPitassiSorrell2022]: for any finite
nonempty linearly ordered output type `α`, if `A` achieves error `β₀ < 1 / (|α| + 1)` on `𝒟`
(with no replicability assumption at all on `A`), then for any target `ρ > 0` and `β > 0`, there
exist thresholds `a, b : ℝ` and `k, N ≥ 1` such that `amplifyFinite A a b k N` is **strongly
`ρ`-replicable** and `(good, β)`-accurate on `𝒟`. -/
theorem exists_amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) {𝒟 : Set (PMF X)} {good : PMF X → Set α} {β₀ ρ β : ℝ}
    (hacc : IsAccurateFor A 𝒟 good β₀) (_hβ₀_nonneg : 0 ≤ β₀)
    (hβ₀ : β₀ < 1 / ((Fintype.card α : ℝ) + 1)) (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ (a b : ℝ) (k N : ℕ) (_ : NeZero k) (_ : NeZero N),
      IsReplicable (amplifyFinite A a b k N) ρ ∧
      IsAccurateFor (amplifyFinite A a b k N) 𝒟 good β := by
  let M : ℝ := Fintype.card α
  have hM : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
  have hgap : 0 < (1 - β₀) / M - β₀ := by
    have hmul : β₀ * (M + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hβ₀
    rw [sub_pos, lt_div_iff₀ hM]; linarith
  let Δ : ℝ := ((1 - β₀) / M - β₀) / 4
  let a : ℝ := β₀ + Δ
  let b : ℝ := (1 - β₀) / M - Δ
  have hab : a < b := by dsimp only [a, b, Δ]; linarith
  have hba : 0 < b - a := sub_pos.mpr hab
  let δ : ℝ := min (Δ / 2) ((ρ / (4 * M)) * (b - a))
  have hδ : 0 < δ := lt_min (by positivity) (mul_pos (div_pos hρ (by positivity)) hba)
  obtain ⟨N, hN_inst, hN_bound⟩ := exists_nat_div_le M (by positivity : 0 < ρ / 4)
  obtain ⟨k, hk_inst, hk_bound⟩ := exp_decay_exists M hδ (lt_min (by positivity : 0 < ρ / 8) hβ)
  refine ⟨a, b, k, N, hk_inst, hN_inst,
    (isReplicable_amplifyFinite A hab hδ.le k N).mono ?_,
    (isAccurateFor_amplifyFinite A hacc hab.le hδ.le
      (by linarith [min_le_left (Δ / 2) ((ρ / (4 * M)) * (b - a))])
      (by linarith [min_le_left (Δ / 2) ((ρ / (4 * M)) * (b - a))]) k N).mono
      (hk_bound.trans (min_le_right _ _))⟩
  have h1 : M * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)) ≤ ρ / 8 := hk_bound.trans (min_le_left _ _)
  have h2 : M * (2 * δ / (b - a)) ≤ ρ / 2 := calc
    M * (2 * δ / (b - a)) ≤ M * (2 * ((ρ / (4 * M)) * (b - a)) / (b - a)) := by
      have := min_le_right (Δ / 2) ((ρ / (4 * M)) * (b - a)); gcongr
    _ = ρ / 2 := by field_simp [hM.ne', hba.ne']; ring
  have h3 : M * (2 * δ / (b - a) + 1 / N) = M * (2 * δ / (b - a)) + M / N := by ring
  dsimp only [M] at h1 h2 h3 hN_bound; linarith

end FiniteDomainAmplification

/-! ### General-domain replicability amplification (`DecidableEq α`, `ρ₀ < 1 / 2`) -/

section GeneralDomainAmplification

variable {X : Type u} {Ω : Type v} {α : Type w} {m : ℕ}

/-- Pick a candidate from `v : Fin k → α` appearing strictly more than `k / 2` times, or
`fallback` if no strict majority exists. -/
@[expose] def strictMajorityCandidate {k : ℕ} [DecidableEq α] (v : Fin k → α)
    (fallback : α) : α :=
  let cands := Finset.univ.filter fun j : Fin k =>
    k < 2 * (Finset.univ.filter fun j' => v j' = v j).card
  if h : cands.Nonempty then v (cands.min' h) else fallback

theorem strictMajorityCandidate_eq_of_lt_two_mul {k : ℕ} [DecidableEq α] (v : Fin k → α)
    (fallback y : α)
    (hy : k < 2 * (Finset.univ.filter fun j : Fin k => v j = y).card) :
    strictMajorityCandidate v fallback = y := by
  obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp (by omega :
    0 < (Finset.univ.filter fun j : Fin k => v j = y).card)
  let cands := Finset.univ.filter fun j : Fin k =>
    k < 2 * (Finset.univ.filter fun j' => v j' = v j).card
  have hne : cands.Nonempty := ⟨j₀, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, by simpa [(Finset.mem_filter.mp hj₀).2] using hy⟩⟩
  dsimp only [strictMajorityCandidate]
  split_ifs with h'
  swap; · exact absurd hne h'
  have hj_cond := (Finset.mem_filter.mp (Finset.min'_mem cands hne)).2
  finset_card

/-- Output distribution of `A` on `D` conditioned on a fixed seed `r`. -/
@[expose] noncomputable def seedOutput (A : Algorithm X Ω α m) (D : PMF X) (r : Ω) : PMF α :=
  (Probability.PMF.iid D m).bind fun S => A.run S r

/-- Collision probability of `A` on `D` at shared seed `r`:
`Probability.PMF.collisionProbability (seedOutput A D r)`. -/
noncomputable abbrev seedColl (A : Algorithm X Ω α m) (D : PMF X) (r : Ω) : ℝ :=
  Probability.PMF.collisionProbability (seedOutput A D r)

private theorem seedColl_nonneg (A : Algorithm X Ω α m) (D : PMF X) (r : Ω) :
    0 ≤ seedColl A D r :=
  Probability.PMF.collisionProbability_nonneg (seedOutput A D r)

private theorem seedColl_le_one (A : Algorithm X Ω α m) (D : PMF X) (r : Ω) :
    seedColl A D r ≤ 1 :=
  Probability.PMF.collisionProbability_le_one (seedOutput A D r)

private theorem seedColl_eq_collBool_true [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    (r : Ω) :
    (((seedOutput A D r).bind fun y₁ =>
      (seedOutput A D r).map fun y₂ => decide (y₁ = y₂)) true).toReal =
      seedColl A D r :=
  (Probability.PMF.collisionProbability_eq_probability (seedOutput A D r)).symm

private theorem agreeProb_eq_tsum_seedColl (A : Algorithm X Ω α m) (D : PMF X) :
    A.agreeProb D = ∑' r : Ω, (A.seed r).toReal * seedColl A D r := by
  classical
  have hpair : A.pairedOutput D = A.seed.bind fun r =>
      (seedOutput A D r).bind fun y₁ => (seedOutput A D r).map fun y₂ => (y₁, y₂) := by
    simp only [Algorithm.pairedOutput, seedOutput, pmf_norm]; pmf_swap
  have hinner (r : Ω) : (((seedOutput A D r).bind fun y₁ =>
      (seedOutput A D r).map fun y₂ => (y₁, y₂)).toOuterMeasure
      {p : α × α | p.1 = p.2}).toReal = seedColl A D r := by
    rw [PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq fun _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (Probability.PMF.toOuterMeasure_ne_top _ _)]
    refine tsum_congr fun y₁ => ?_
    have hset : (fun y₂ : α => (y₁, y₂)) ⁻¹' {p : α × α | p.1 = p.2} = {y₁} :=
      Set.ext fun y₂ => by simp [eq_comm]
    rw [ENNReal.toReal_mul, PMF.toOuterMeasure_map_apply, hset, PMF.toOuterMeasure_apply_singleton,
      sq]
  rw [Algorithm.agreeProb, hpair, PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq fun _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (Probability.PMF.toOuterMeasure_ne_top _ _)]
  exact tsum_congr fun r => by rw [ENNReal.toReal_mul, hinner r]

private theorem seed_markov_coll_lt (A : Algorithm X Ω α m) (D : PMF X) {c : ℝ} (hc : c < 1) :
    (A.seed.toOuterMeasure {r : Ω | seedColl A D r < c}).toReal ≤
      A.disagreeProb D / (1 - c) := by
  have h1c : 0 < 1 - c := sub_pos.mpr hc
  have hsum_agree : Summable fun r : Ω => (A.seed r).toReal * seedColl A D r :=
    (Probability.PMF.summable_toReal A.seed).of_nonneg_of_le
      (fun r => mul_nonneg ENNReal.toReal_nonneg (seedColl_nonneg A D r))
      (fun r => mul_le_of_le_one_right ENNReal.toReal_nonneg (seedColl_le_one A D r))
  have hdisagree : ∑' r : Ω, (A.seed r).toReal * (1 - seedColl A D r) = A.disagreeProb D := by
    rw [Algorithm.disagreeProb_eq_one_sub_agreeProb, agreeProb_eq_tsum_seedColl,
      tsum_congr fun r => show (A.seed r).toReal * (1 - seedColl A D r) =
        (A.seed r).toReal - (A.seed r).toReal * seedColl A D r by ring,
      (Probability.PMF.summable_toReal A.seed).tsum_sub hsum_agree,
      Probability.PMF.tsum_toReal A.seed]
  refine (Probability.PMF.toOuterMeasure_toReal_mono _
    (t := {r : Ω | 1 - c ≤ 1 - seedColl A D r}) fun r hr => by
      simp only [Set.mem_ofPred_eq] at hr ⊢; linarith).trans ?_
  exact (Probability.PMF.toOuterMeasure_toReal_le_tsum_div A.seed
    (fun r => sub_nonneg.mpr (seedColl_le_one A D r))
    (fun r => sub_le_self 1 (seedColl_nonneg A D r)) h1c).trans_eq (by rw [hdisagree])

/-- Single candidate-seed trial inside `amplifyReplicability`: using `k₁` independent sample
pairs to estimate the seed's collision probability and `k₂` independent samples to find its
strict-majority output. -/
@[expose] noncomputable def trialRun [DecidableEq α] (A : Algorithm X Ω α m) (k₁ k₂ : ℕ)
    [NeZero k₂] (S : Fin (k₁ * (m + m) + k₂ * m) → X) (r : Ω) : PMF (ℝ × α) :=
  let sp := splitSample (k₁ * (m + m)) (k₂ * m) S
  let csLaw : PMF (Fin k₁ → Bool) := PMF.piFin fun l : Fin k₁ =>
    let pair := splitSample m m (BitString.block (m := k₁) (k := m + m) sp.1 l)
    (A.run pair.1 r).bind fun y₁ => (A.run pair.2 r).map fun y₂ => decide (y₁ = y₂)
  let zsLaw : PMF (Fin k₂ → α) := PMF.piFin fun j : Fin k₂ =>
    A.run (BitString.block (m := k₂) (k := m) sp.2 j) r
  csLaw.bind fun cs =>
    zsLaw.map fun zs =>
      (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
        strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩))

private noncomputable def trialRunMarginal [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    (r : Ω) (k₁ k₂ : ℕ) [NeZero k₂] : PMF (ℝ × α) :=
  let μ := seedOutput A D r
  let collBool : PMF Bool := μ.bind fun y₁ => μ.map fun y₂ => decide (y₁ = y₂)
  (Probability.PMF.iid collBool k₁).bind fun cs =>
    (Probability.PMF.iid μ k₂).map fun zs =>
      (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
        strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩))

private theorem iid_bind_trialRun [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X) (r : Ω)
    (k₁ k₂ : ℕ) [NeZero k₂] :
    ((Probability.PMF.iid D (k₁ * (m + m) + k₂ * m)).bind fun S => trialRun A k₁ k₂ S r) =
      trialRunMarginal A D r k₁ k₂ := by
  let pairLaw (b : Fin (m + m) → X) := (A.run (splitSample m m b).1 r).bind fun y₁ =>
    (A.run (splitSample m m b).2 r).map fun y₂ => decide (y₁ = y₂)
  have hpair_eq : (Probability.PMF.iid D (m + m)).bind pairLaw =
      (seedOutput A D r).bind fun y₁ => (seedOutput A D r).map fun y₂ => decide (y₁ = y₂) := by
    rw [iid_bind_splitSample D m m fun U₁ U₂ =>
      (A.run U₁ r).bind fun y₁ => (A.run U₂ r).map fun y₂ => decide (y₁ = y₂)]
    simp only [seedOutput, pmf_norm]; pmf_swap
  have hS₁ : ((Probability.PMF.iid D (k₁ * (m + m))).bind fun S₁ =>
      PMF.piFin fun l : Fin k₁ => pairLaw (BitString.block (m := k₁) (k := m + m) S₁ l)) =
      Probability.PMF.iid ((seedOutput A D r).bind fun y₁ =>
        (seedOutput A D r).map fun y₂ => decide (y₁ = y₂)) k₁ := by
    rw [iid_bind_piFin_block D k₁ (m + m) (fun _ => pairLaw)]
    simp_rw [hpair_eq]; exact PMF.piFin_const _ k₁
  have hS₂ : ((Probability.PMF.iid D (k₂ * m)).bind fun S₂ =>
      PMF.piFin fun j : Fin k₂ => A.run (BitString.block (m := k₂) (k := m) S₂ j) r) =
      Probability.PMF.iid (seedOutput A D r) k₂ := by
    rw [iid_bind_piFin_block D k₂ m fun _ b => A.run b r, PMF.piFin_const]; rfl
  dsimp only [trialRun, trialRunMarginal]
  rw [iid_bind_splitSample D (k₁ * (m + m)) (k₂ * m) fun S₁ S₂ =>
    (PMF.piFin fun l : Fin k₁ => pairLaw (BitString.block (m := k₁) (k := m + m) S₁ l)).bind
      fun cs => (PMF.piFin fun j : Fin k₂ =>
        A.run (BitString.block (m := k₂) (k := m) S₂ j) r).map fun zs =>
          (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
            strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩)), ← hS₁, ← hS₂]
  simp only [pairLaw, pmf_norm]; pmf_swap

/-- Pick the first trial `t` whose empirical collision estimate passes `thresholdRound a b N i`,
falling back to trial `0` when none qualifies. -/
@[expose] noncomputable def pickFirstThresholded {T : ℕ} [NeZero T] (a b : ℝ) (N : ℕ)
    (i : Fin N) (trials : Fin T → ℝ × α) : α :=
  let cands := Finset.univ.filter fun t : Fin T =>
    thresholdRound a b N i (trials t).1 = true
  if h : cands.Nonempty then (trials (cands.min' h)).2 else (trials ⟨0, NeZero.pos T⟩).2

/-- General-domain replicability amplification [ImpagliazzoLeiPitassiSorrell2022]: draws `T`
independent shared seeds `r_t ~ A.seed` and one threshold `i ~ uniform (Fin N)`, runs
`trialRun` on each candidate seed over disjoint sample blocks, and outputs the strict-majority
candidate of the first seed passing `thresholdValue a b N i`. -/
@[expose] noncomputable def amplifyReplicability [DecidableEq α] (A : Algorithm X Ω α m)
    (a b : ℝ) (T k₁ k₂ N : ℕ) [NeZero T] [NeZero k₂] [NeZero N] :
    Algorithm X ((Fin T → Ω) × Fin N) α (T * (k₁ * (m + m) + k₂ * m)) where
  seed := (PMF.piFin fun _ : Fin T => A.seed).bind fun rs =>
    (Probability.PMF.uniformOfFintype (Fin N)).map fun i => (rs, i)
  run S seed :=
    (PMF.piFin fun t : Fin T =>
      trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S t)
        (seed.1 t)).map
      fun trials => pickFirstThresholded a b N seed.2 trials

private theorem iid_bind_trialRun_block [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    (T k₁ k₂ : ℕ) [NeZero k₂] (rs : Fin T → Ω) :
    ((Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m))).bind fun S =>
      PMF.piFin fun t : Fin T =>
        trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S t) (rs t)) =
      PMF.piFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂ := by
  rw [iid_bind_piFin_block D T (k₁ * (m + m) + k₂ * m) fun t b => trialRun A k₁ k₂ b (rs t)]
  exact congrArg PMF.piFin (funext fun t => iid_bind_trialRun A D (rs t) k₁ k₂)

private theorem marginal_amplifyReplicability [DecidableEq α] (A : Algorithm X Ω α m)
    (a b : ℝ) (T k₁ k₂ N : ℕ) [NeZero T] [NeZero k₂] [NeZero N] (D : PMF X) :
    (amplifyReplicability A a b T k₁ k₂ N).marginal D =
      (PMF.piFin fun _ : Fin T => A.seed).bind fun rs =>
        (PMF.piFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials =>
          (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
            pickFirstThresholded a b N i trials := by
  rw [Algorithm.marginal_eq_seed_bind]
  simp only [amplifyReplicability, ← iid_bind_trialRun_block A D T k₁ k₂, pmf_norm]
  pmf_swap

private theorem pairedOutput_amplifyReplicability [DecidableEq α] (A : Algorithm X Ω α m)
    (a b : ℝ) (T k₁ k₂ N : ℕ) [NeZero T] [NeZero k₂] [NeZero N] (D : PMF X) :
    (amplifyReplicability A a b T k₁ k₂ N).pairedOutput D =
      (PMF.piFin fun _ : Fin T => A.seed).bind fun rs =>
        (PMF.piFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₁ =>
          (PMF.piFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₂ =>
            (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
              (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂) := by
  simp only [Algorithm.pairedOutput, amplifyReplicability,
    ← iid_bind_trialRun_block A D T k₁ k₂, pmf_norm]
  pmf_swap

private theorem strictMajorityCandidate_fail_le [DecidableEq α] (μ : PMF α) (yStar : α)
    {c : ℝ} (hc_half : 1 / 2 < c) (hyStar : c ≤ (μ yStar).toReal) (k₂ : ℕ) [NeZero k₂] :
    ((Probability.PMF.iid μ k₂).toOuterMeasure
      {zs : Fin k₂ → α |
        strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩) ≠ yStar}).toReal ≤
      2 * Real.exp (-2 * (k₂ : ℝ) * ((c - 1 / 2) / 2) ^ 2) := by
  refine (Probability.PMF.toOuterMeasure_toReal_mono _
    (t := {zs : Fin k₂ → α | (c - 1 / 2) / 2 < |empFreq k₂ zs yStar - (μ yStar).toReal|})
    fun zs hzs => ?_).trans (empFreq_concentrates μ k₂ (by linarith) yStar)
  have hnot : 2 * (Finset.univ.filter fun j : Fin k₂ => zs j = yStar).card ≤ k₂ :=
    not_lt.mp fun hlt => hzs (strictMajorityCandidate_eq_of_lt_two_mul zs _ yStar hlt)
  have hemp : empFreq k₂ zs yStar ≤ 1 / 2 := by
    rw [empFreq, div_le_div_iff₀ (Nat.cast_pos.mpr (NeZero.pos k₂)) two_pos, one_mul]
    exact_mod_cast (by linarith : (Finset.univ.filter fun j => zs j = yStar).card * 2 ≤ k₂)
  exact (by linarith : (c - 1 / 2) / 2 < (μ yStar).toReal - empFreq k₂ zs yStar).trans_le
    ((le_abs_self _).trans_eq (abs_sub_comm _ _))

private theorem trialRunMarginal_single_fail [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    (r : Ω) {a δ : ℝ} (hδ : 0 ≤ δ) (ha_half : 1 / 2 + δ < a) (k₁ k₂ : ℕ)
    [NeZero k₁] [NeZero k₂] :
    ((trialRunMarginal A D r k₁ k₂).toOuterMeasure
      {pr : ℝ × α |
        |pr.1 - seedColl A D r| ≤ δ ∧
        (a - δ ≤ seedColl A D r →
          ∀ y : α, a - δ ≤ (seedOutput A D r y).toReal → pr.2 = y)}ᶜ).toReal ≤
      2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
        2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2) := by
  let μ := seedOutput A D r
  let collBool : PMF Bool := μ.bind fun y₁ => μ.map fun y₂ => decide (y₁ = y₂)
  let good₁ : Set (Fin k₁ → Bool) := {cs | |empFreq k₁ cs true - seedColl A D r| ≤ δ}
  have h1 : ((Probability.PMF.iid collBool k₁).toOuterMeasure good₁ᶜ).toReal ≤
      2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) := by
    have hconc := empFreq_concentrates collBool k₁ hδ true
    rw [seedColl_eq_collBool_true] at hconc
    simpa only [Set.compl_def, Set.mem_ofPred_eq, not_le, good₁] using hconc
  dsimp only [trialRunMarginal]
  refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ good₁ _
    (error := 2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2)) (by positivity)
    fun cs _ hcs => ?_).trans (add_le_add h1 le_rfl)
  rw [PMF.toOuterMeasure_map_apply]
  by_cases hcoll : a - δ ≤ seedColl A D r
  · obtain ⟨yStar, hyStar⟩ := Probability.PMF.exists_le_toReal_of_le_collisionProbability μ hcoll
    have huniq (y : α) (hy : a - δ ≤ (μ y).toReal) : y = yStar := by
      by_contra hne
      have hsum := ((Probability.PMF.summable_toReal μ).sum_le_tsum ({y, yStar} : Finset α)
        fun _ _ => ENNReal.toReal_nonneg).trans_eq (Probability.PMF.tsum_toReal μ)
      rw [Finset.sum_pair hne] at hsum; linarith
    refine (Probability.PMF.toOuterMeasure_toReal_mono _
      (t := {zs : Fin k₂ → α |
        strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩) ≠ yStar}) fun zs hzs hEq => ?_).trans
      (strictMajorityCandidate_fail_le μ yStar (by linarith) hyStar k₂)
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and] at hzs
    exact hzs hcs fun _ y hy => hEq.trans (huniq y hy).symm
  · refine (Probability.PMF.toOuterMeasure_toReal_mono _ (t := ∅) fun _ h => ?_).trans ?_
    · exact h ⟨hcs, fun hc => absurd hc hcoll⟩
    simp only [MeasureTheory.measure_empty, ENNReal.toReal_zero]; positivity

private theorem seed_markov_err_lt (A : Algorithm X Ω α m) (D : PMF X) (good : Set α)
    {c β₀ : ℝ} (hc : 0 < c) (hacc : ((A.marginal D).toOuterMeasure goodᶜ).toReal ≤ β₀) :
    (A.seed.toOuterMeasure
      {r : Ω | c ≤ ((seedOutput A D r).toOuterMeasure goodᶜ).toReal}).toReal ≤ β₀ / c := by
  have hm_sum :
      ∑' r : Ω, (A.seed r).toReal * ((seedOutput A D r).toOuterMeasure goodᶜ).toReal ≤ β₀ := by
    refine Eq.trans_le ?_ hacc
    rw [Algorithm.marginal_eq_seed_bind, PMF.toOuterMeasure_bind_apply,
      ENNReal.tsum_toReal_eq fun _ =>
        ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (Probability.PMF.toOuterMeasure_ne_top _ _)]
    exact tsum_congr fun r => ENNReal.toReal_mul.symm
  exact (Probability.PMF.toOuterMeasure_toReal_le_tsum_div A.seed
    (fun _ => ENNReal.toReal_nonneg) (fun r => Probability.PMF.toOuterMeasure_toReal_le_one _ _)
    hc).trans (div_le_div_of_nonneg_right hm_sum hc.le)

private theorem bad_goodSeeds_le (A : Algorithm X Ω α m) (D : PMF X) {θ_acc : ℝ}
    (hθ_lt : θ_acc < 1) (T : ℕ) :
    ((PMF.piFin fun _ : Fin T => A.seed).toOuterMeasure
      ({rs : Fin T → Ω | ∃ t : Fin T, θ_acc ≤ seedColl A D (rs t)})ᶜ).toReal ≤
      (A.disagreeProb D / (1 - θ_acc)) ^ T := by
  have heqc : ({rs : Fin T → Ω | ∃ t : Fin T, θ_acc ≤ seedColl A D (rs t)})ᶜ =
      {rs : Fin T → Ω | ∀ t : Fin T, rs t ∈ {r | seedColl A D r < θ_acc}} :=
    Set.ext fun _ => by simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_le]
  rw [heqc, PMF.piFin_const, PMF.toOuterMeasure_iid_forall, ENNReal.toReal_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (seed_markov_coll_lt A D hθ_lt) T

private noncomputable def goodTrialsSet (A : Algorithm X Ω α m) (D : PMF X)
    (a δ : ℝ) {T : ℕ} (rs : Fin T → Ω) : Set (Fin T → ℝ × α) :=
  {trials | ∀ t : Fin T,
    |(trials t).1 - seedColl A D (rs t)| ≤ δ ∧
    (a - δ ≤ seedColl A D (rs t) →
      ∀ y : α, a - δ ≤ (seedOutput A D (rs t) y).toReal → (trials t).2 = y)}

private theorem goodTrials_fail_le [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    {a δ : ℝ} (hδ : 0 ≤ δ) (ha_half : 1 / 2 + δ < a) (T k₁ k₂ : ℕ)
    [NeZero k₁] [NeZero k₂] (rs : Fin T → Ω) :
    ((PMF.piFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).toOuterMeasure
      (goodTrialsSet A D a δ rs)ᶜ).toReal ≤
      (T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
        2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2)) := by
  let bad (t : Fin T) : Set (ℝ × α) :=
    {pr | |pr.1 - seedColl A D (rs t)| ≤ δ ∧
      (a - δ ≤ seedColl A D (rs t) →
        ∀ y : α, a - δ ≤ (seedOutput A D (rs t) y).toReal → pr.2 = y)}ᶜ
  have hunion : (goodTrialsSet A D a δ rs)ᶜ = {trials | ∃ t, trials t ∈ bad t} :=
    Set.ext fun _ => by
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, goodTrialsSet, bad]
  rw [hunion]
  exact (PMF.toOuterMeasure_toReal_piFin_exists_le _ bad).trans <|
    (Finset.sum_le_sum fun t _ =>
      trialRunMarginal_single_fail A D (rs t) hδ ha_half k₁ k₂).trans_eq
      (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])

private theorem goodTrial_heavy_of_thresholdPass (A : Algorithm X Ω α m) (D : PMF X)
    {a b δ : ℝ} (hab : a ≤ b) {T N : ℕ} {rs : Fin T → Ω} {trials : Fin T → ℝ × α}
    (htr : trials ∈ goodTrialsSet A D a δ rs) (i : Fin N) (t : Fin T)
    (ht_pass : thresholdRound a b N i (trials t).1 = true) :
    ∃ yStar : α,
      a - δ ≤ seedColl A D (rs t) ∧
      a - δ ≤ (seedOutput A D (rs t) yStar).toReal ∧
      (trials t).2 = yStar := by
  have ht_ge : a ≤ (trials t).1 := le_of_not_gt fun hlt =>
    absurd ht_pass (by rw [thresholdRound_false_of_lt_left hab i hlt]; decide)
  have hcoll_ge : a - δ ≤ seedColl A D (rs t) := by linarith [(abs_sub_le_iff.mp (htr t).1).1]
  obtain ⟨yStar, hyStar⟩ :=
    Probability.PMF.exists_le_toReal_of_le_collisionProbability (seedOutput A D (rs t)) hcoll_ge
  exact ⟨yStar, hcoll_ge, hyStar, (htr t).2 hcoll_ge yStar hyStar⟩

private theorem pickFirstThresholded_eq_heavy (A : Algorithm X Ω α m) (D : PMF X)
    {a b θ_acc δ : ℝ} (hab : a ≤ b) (hb_acc : b ≤ θ_acc - δ) {T N : ℕ} [NeZero T]
    {rs : Fin T → Ω} {t₀ : Fin T} (ht₀ : θ_acc ≤ seedColl A D (rs t₀))
    {trials : Fin T → ℝ × α} (htr : trials ∈ goodTrialsSet A D a δ rs) (i : Fin N) :
    ∃ tStar : Fin T, ∃ yStar : α,
      pickFirstThresholded a b N i trials = yStar ∧
      a - δ ≤ (seedOutput A D (rs tStar) yStar).toReal := by
  have ht₀_pass : thresholdRound a b N i (trials t₀).1 = true :=
    thresholdRound_true_of_right_le hab i (by linarith [(abs_sub_le_iff.mp (htr t₀).1).2])
  let cands := Finset.univ.filter fun t : Fin T => thresholdRound a b N i (trials t).1 = true
  have hne : cands.Nonempty := ⟨t₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht₀_pass⟩⟩
  have hpick : pickFirstThresholded a b N i trials = (trials (cands.min' hne)).2 := by
    dsimp only [pickFirstThresholded]; rw [dite_eq_left_of_eq_true (eq_true hne)]
  obtain ⟨yStar, _, hyStar, heq⟩ := goodTrial_heavy_of_thresholdPass A D hab htr i (cands.min' hne)
    (Finset.mem_filter.mp (Finset.min'_mem cands hne)).2
  exact ⟨cands.min' hne, yStar, hpick.trans heq, hyStar⟩

private theorem pickFirstThresholded_eq_of_rounds_eq (A : Algorithm X Ω α m) (D : PMF X)
    {a b θ_acc δ : ℝ} (hab : a ≤ b) (hb_acc : b ≤ θ_acc - δ) {T N : ℕ} [NeZero T]
    {rs : Fin T → Ω} {t₀ : Fin T} (ht₀ : θ_acc ≤ seedColl A D (rs t₀))
    {trials₁ trials₂ : Fin T → ℝ × α}
    (htr₁ : trials₁ ∈ goodTrialsSet A D a δ rs) (htr₂ : trials₂ ∈ goodTrialsSet A D a δ rs)
    (i : Fin N)
    (hround : ∀ t : Fin T,
      thresholdRound a b N i (trials₁ t).1 = thresholdRound a b N i (trials₂ t).1) :
    pickFirstThresholded a b N i trials₁ = pickFirstThresholded a b N i trials₂ := by
  have ht₀_pass : thresholdRound a b N i (trials₁ t₀).1 = true :=
    thresholdRound_true_of_right_le hab i (by linarith [(abs_sub_le_iff.mp (htr₁ t₀).1).2])
  have hcand : (Finset.univ.filter fun t : Fin T => thresholdRound a b N i (trials₁ t).1 = true) =
      Finset.univ.filter fun t : Fin T => thresholdRound a b N i (trials₂ t).1 = true := by
    ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hround t]
  have hne₁ : (Finset.univ.filter fun t : Fin T =>
      thresholdRound a b N i (trials₁ t).1 = true).Nonempty :=
    ⟨t₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht₀_pass⟩⟩
  let tStar := (Finset.univ.filter fun t : Fin T =>
    thresholdRound a b N i (trials₁ t).1 = true).min' hne₁
  obtain ⟨yStar, hcoll_ge, hyStar, h1eq⟩ := goodTrial_heavy_of_thresholdPass A D hab htr₁ i tStar
    (Finset.mem_filter.mp (Finset.min'_mem _ hne₁)).2
  have hpick₁ : pickFirstThresholded a b N i trials₁ = (trials₁ tStar).2 := by
    dsimp only [pickFirstThresholded]; simp only [hne₁, ↓reduceDIte]; rfl
  have hpick₂ : pickFirstThresholded a b N i trials₂ = (trials₂ tStar).2 := by
    dsimp only [pickFirstThresholded]; simp only [← hcand, hne₁, ↓reduceDIte]; rfl
  rw [hpick₁, hpick₂, h1eq, (htr₂ tStar).2 hcoll_ge yStar hyStar]

/-- Disagreement probability upper bound for `amplifyReplicability`: if
`1 / 2 + δ < a < b ≤ θ_acc - δ` and `θ_acc < 1`, then
`(amplifyReplicability A a b T k₁ k₂ N).disagreeProb D` is bounded by the bad-seed probability
`(A.disagreeProb D / (1 - θ_acc)) ^ T`, twice the concentration error over `T` trials, and the
threshold discretization error `T * (2 * δ / (b - a) + 1 / N)`. -/
theorem disagreeProb_amplifyReplicability_le [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    {a b θ_acc δ : ℝ} (hab : a < b) (hδ : 0 ≤ δ) (ha_half : 1 / 2 + δ < a)
    (hb_acc : b ≤ θ_acc - δ) (hθ_lt : θ_acc < 1) (T k₁ k₂ N : ℕ)
    [NeZero T] [NeZero k₁] [NeZero k₂] [NeZero N] :
    (amplifyReplicability A a b T k₁ k₂ N).disagreeProb D ≤
      (A.disagreeProb D / (1 - θ_acc)) ^ T +
        2 * ((T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
          2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2))) +
        (T : ℝ) * (2 * δ / (b - a) + 1 / N) := by
  rw [Algorithm.disagreeProb, pairedOutput_amplifyReplicability]
  let trialFail : ℝ := (T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
    2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2))
  let seedFail : ℝ := (T : ℝ) * (2 * δ / (b - a) + 1 / N)
  have hba : 0 < b - a := sub_pos.mpr hab
  let goodSeeds : Set (Fin T → Ω) := {rs | ∃ t : Fin T, θ_acc ≤ seedColl A D (rs t)}
  have hfull := Probability.PMF.toOuterMeasure_bind_failure_toReal_le
    (PMF.piFin fun _ : Fin T => A.seed)
    (fun rs => (PMF.piFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₁ =>
      (PMF.piFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₂ =>
        (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
          (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂))
    goodSeeds {p : α × α | p.1 ≠ p.2} (error := 2 * trialFail + seedFail) (by positivity) ?_
  · exact hfull.trans (by linarith [bad_goodSeeds_le A D hθ_lt T])
  rintro rs _ ⟨t₀, ht₀⟩
  refine paired_bind_disagree_le _ (goodTrialsSet A D a δ rs) (pickFirstThresholded a b N)
    (goodTrials_fail_le A D hδ ha_half T k₁ k₂ rs) (by positivity) fun tr₁ htr₁ tr₂ htr₂ => ?_
  simpa only [Fintype.card_fin] using thresholdRound_union_disagree_le hab N
    (fun t => (htr₁ t).1) (fun t => (htr₂ t).1) fun i hi => by
      simp only [Set.mem_ofPred_eq, ne_eq, Set.mem_iUnion, Finset.mem_univ, exists_true_left]
        at hi ⊢
      by_contra hnone; push Not at hnone
      exact hi (pickFirstThresholded_eq_of_rounds_eq A D hab.le hb_acc ht₀ htr₁ htr₂ i hnone)

/-- **Accuracy preservation for `amplifyReplicability`**: under `IsReplicableFor A 𝒟 ρ₀` and
`IsAccurateFor A 𝒟 good β₀` with `1 / 2 + δ < a < b ≤ θ_acc - δ` and `θ_acc < 1`, the failure
probability of `amplifyReplicability` is bounded by the bad-seed probability
`(ρ₀ / (1 - θ_acc)) ^ T`, the Markov union bound `(T : ℝ) * (β₀ / (a - δ))` over the `T`
candidate seeds, and the per-trial concentration errors. -/
theorem isAccurateFor_amplifyReplicability [DecidableEq α] (A : Algorithm X Ω α m)
    {𝒟 : Set (PMF X)} {good : PMF X → Set α} {ρ₀ β₀ a b θ_acc δ : ℝ}
    (hrep : IsReplicableFor A 𝒟 ρ₀) (hacc : IsAccurateFor A 𝒟 good β₀)
    (hab : a < b) (hδ : 0 ≤ δ) (ha_half : 1 / 2 + δ < a) (hb_acc : b ≤ θ_acc - δ)
    (hθ_lt : θ_acc < 1) (T k₁ k₂ N : ℕ) [NeZero T] [NeZero k₁] [NeZero k₂] [NeZero N] :
    IsAccurateFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 good
      ((ρ₀ / (1 - θ_acc)) ^ T + (T : ℝ) * (β₀ / (a - δ)) +
        (T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
          2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2))) := by
  intro D hD
  rw [marginal_amplifyReplicability]
  have had_pos : 0 < a - δ := by linarith
  let seeds := PMF.piFin fun _ : Fin T => A.seed
  let goodSeeds : Set (Fin T → Ω) := {rs | ∃ t : Fin T, θ_acc ≤ seedColl A D (rs t)}
  let badErrSeeds : Set (Fin T → Ω) :=
    {rs | ∃ t : Fin T, a - δ ≤ ((seedOutput A D (rs t)).toOuterMeasure (good D)ᶜ).toReal}
  have hbad_coll : (seeds.toOuterMeasure goodSeedsᶜ).toReal ≤ (ρ₀ / (1 - θ_acc)) ^ T :=
    (bad_goodSeeds_le A D hθ_lt T).trans <| pow_le_pow_left₀
      (div_nonneg (A.disagreeProb_nonneg D) (sub_pos.mpr hθ_lt).le)
      (div_le_div_of_nonneg_right (hrep D hD) (sub_pos.mpr hθ_lt).le) T
  have hbad_err : (seeds.toOuterMeasure badErrSeeds).toReal ≤ (T : ℝ) * (β₀ / (a - δ)) :=
    (PMF.toOuterMeasure_toReal_piFin_exists_le (fun _ => A.seed) fun _ =>
      {r | a - δ ≤ ((seedOutput A D r).toOuterMeasure (good D)ᶜ).toReal}).trans <|
      (Finset.sum_le_sum fun _ _ => seed_markov_err_lt A D (good D) had_pos (hacc D hD)).trans_eq
        (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
  have hgoodRS_c : (seeds.toOuterMeasure (goodSeeds ∩ badErrSeedsᶜ)ᶜ).toReal ≤
      (ρ₀ / (1 - θ_acc)) ^ T + (T : ℝ) * (β₀ / (a - δ)) := by
    have hnt : ∀ s, seeds.toOuterMeasure s ≠ ⊤ := fun s => Probability.PMF.toOuterMeasure_ne_top _ s
    rw [Set.compl_inter, compl_compl]
    exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hnt _, hnt _⟩)
      (MeasureTheory.measure_union_le goodSeedsᶜ badErrSeeds)).trans
      ((ENNReal.toReal_add (hnt _) (hnt _)).trans_le (add_le_add hbad_coll hbad_err))
  let trialFail : ℝ := (T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
    2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2))
  refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le seeds _
    (goodSeeds ∩ badErrSeedsᶜ) (good D)ᶜ (error := trialFail) (by positivity) ?_).trans
    (add_le_add hgoodRS_c le_rfl)
  rintro rs _ ⟨⟨t₀, ht₀⟩, herr⟩
  refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ (goodTrialsSet A D a δ rs)
    (good D)ᶜ le_rfl fun trials _ htr => ?_).trans
    (by linarith [goodTrials_fail_le A D hδ ha_half T k₁ k₂ rs])
  rw [PMF.toOuterMeasure_map_apply]
  have hempty : (fun i : Fin N => pickFirstThresholded a b N i trials) ⁻¹' (good D)ᶜ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun i hy_bad => ?_
    obtain ⟨tStar, yStar, hpick, hyStar⟩ :=
      pickFirstThresholded_eq_heavy A D hab.le hb_acc ht₀ htr i
    rw [Set.mem_preimage, hpick] at hy_bad
    have hle_y : (seedOutput A D (rs tStar) yStar).toReal ≤
        ((seedOutput A D (rs tStar)).toOuterMeasure (good D)ᶜ).toReal := by
      rw [← PMF.toOuterMeasure_apply_singleton]
      exact Probability.PMF.toOuterMeasure_toReal_mono _ (Set.singleton_subset_iff.mpr hy_bad)
    exact herr ⟨tStar, hyStar.trans hle_y⟩
  simp [hempty]

/-- **General-domain replicability and accuracy-preserving amplification**: over any
`[DecidableEq α]`, for any initial `ρ₀ < 1 / 2` and target `ρ, β > 0`, there exist shared-seed
and trial parameters `(a, b, T, k₁, k₂, N)` together with an initial-error threshold `β₀_req > 0`
(of order `O(β / T)`) such that any `ρ₀`-replicable algorithm `A` whose error satisfies
`β₀ ≤ β₀_req` is amplified to `ρ`-replicability while preserving `(good, β)` accuracy. -/
theorem exists_amplifyReplicability_accurate {ρ₀ ρ β : ℝ} (hρ₀_nonneg : 0 ≤ ρ₀)
    (hρ₀ : ρ₀ < 1 / 2) (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ (a b : ℝ) (T k₁ k₂ N : ℕ) (_ : NeZero T) (_ : NeZero k₁) (_ : NeZero k₂) (_ : NeZero N)
      (β₀_req : ℝ), 0 < β₀_req ∧
      ∀ {X : Type u} {Ω : Type v} {α : Type w} {m : ℕ} [DecidableEq α]
        (A : Algorithm X Ω α m) {𝒟 : Set (PMF X)} {good : PMF X → Set α} {β₀ : ℝ},
        IsReplicableFor A 𝒟 ρ₀ → IsAccurateFor A 𝒟 good β₀ → β₀ ≤ β₀_req →
          IsReplicableFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 ρ ∧
          IsAccurateFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 good β := by
  let ε : ℝ := min ρ β
  have hε : 0 < ε := lt_min hρ hβ
  let γ : ℝ := (1 / 2 - ρ₀) / 4
  let a : ℝ := 1 / 2 + γ
  let b : ℝ := 1 / 2 + 2 * γ
  let θ_acc : ℝ := 1 / 2 + 3 * γ
  have hab : a < b := by dsimp only [a, b, γ]; linarith
  have hba : 0 < b - a := sub_pos.mpr hab
  have hθ_lt : θ_acc < 1 := by dsimp only [θ_acc, γ]; linarith
  let q : ℝ := ρ₀ / (1 - θ_acc)
  have hq0 : 0 ≤ q := div_nonneg hρ₀_nonneg (sub_pos.mpr hθ_lt).le
  have hq1 : q < 1 := (div_lt_one (sub_pos.mpr hθ_lt)).mpr (by dsimp only [θ_acc, γ]; linarith)
  obtain ⟨T, hT_inst, hT_pow⟩ :=
    exists_neZero_mul_pow_le 1 hq0 hq1 (show 0 < ε / 4 by positivity)
  rw [one_mul] at hT_pow
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr (NeZero.pos T)
  obtain ⟨N, hN_inst, hN_bound⟩ := exists_nat_div_le (T : ℝ) (by positivity : 0 < ρ / 4)
  let δ : ℝ := min (γ / 2) ((ρ / (8 * (T : ℝ))) * (b - a))
  have hδ : 0 < δ := lt_min (by dsimp only [γ]; linarith) (by positivity)
  have hδ_le_γ : δ ≤ γ / 2 := min_le_left _ _
  have ha_half : 1 / 2 + δ < a := by dsimp only [a, γ] at hδ_le_γ ⊢; linarith
  have hb_acc : b ≤ θ_acc - δ := by dsimp only [b, θ_acc]; linarith
  have had_pos : 0 < a - δ := by linarith
  obtain ⟨k₁, hk₁_inst, hk₁⟩ := exp_decay_exists (2 * (T : ℝ)) hδ (by positivity : 0 < ε / 8)
  obtain ⟨k₂, hk₂_inst, hk₂⟩ := exp_decay_exists (2 * (T : ℝ))
    (by linarith : 0 < (a - δ - 1 / 2) / 2) (by positivity : 0 < ε / 8)
  let β₀_req : ℝ := (β / 4) * (a - δ) / T
  refine ⟨a, b, T, k₁, k₂, N, hT_inst, hk₁_inst, hk₂_inst, hN_inst, β₀_req, by positivity, ?_⟩
  intro X Ω α m _ A 𝒟 good β₀ hrep hacc hβ₀_le
  have hε_rho : ε ≤ ρ := min_le_left _ _
  have hε_beta : ε ≤ β := min_le_right _ _
  refine ⟨fun D hD => ?_,
    (isAccurateFor_amplifyReplicability A hrep hacc hab hδ.le ha_half hb_acc hθ_lt
      T k₁ k₂ N).mono ?_⟩
  · have hpow : (A.disagreeProb D / (1 - θ_acc)) ^ T ≤ ρ / 4 :=
      (pow_le_pow_left₀ (div_nonneg (A.disagreeProb_nonneg D) (sub_pos.mpr hθ_lt).le)
        (div_le_div_of_nonneg_right (hrep D hD) (sub_pos.mpr hθ_lt).le) T).trans
        (by linarith [hT_pow])
    have hseed : (T : ℝ) * (2 * δ / (b - a)) ≤ ρ / 4 := calc
      (T : ℝ) * (2 * δ / (b - a))
          ≤ (T : ℝ) * (2 * ((ρ / (8 * (T : ℝ))) * (b - a)) / (b - a)) := by
            have := min_le_right (γ / 2) ((ρ / (8 * (T : ℝ))) * (b - a)); gcongr
      _ = ρ / 4 := by field_simp [hTR.ne', hba.ne']; ring
    have hsplit : (T : ℝ) * (2 * δ / (b - a) + 1 / N) =
        (T : ℝ) * (2 * δ / (b - a)) + (T : ℝ) / N := by ring
    linarith [disagreeProb_amplifyReplicability_le A D hab hδ.le ha_half hb_acc hθ_lt T k₁ k₂ N]
  · have h2 : (T : ℝ) * (β₀ / (a - δ)) ≤ β / 4 := calc
      (T : ℝ) * (β₀ / (a - δ)) ≤ (T : ℝ) * (β₀_req / (a - δ)) := by gcongr
      _ = β / 4 := by dsimp only [β₀_req]; field_simp [hTR.ne', had_pos.ne']
    linarith [hT_pow, (by positivity : 0 ≤ (T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2))),
      (by positivity : 0 ≤ (T : ℝ) * (2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2)))]

/-- **General-domain replicability amplification** [ImpagliazzoLeiPitassiSorrell2022]: over any
`[DecidableEq α]` output type, any algorithm `A` that is weakly (or strongly) `ρ₀`-replicable on
`𝒟` with `ρ₀ < 1 / 2` can be amplified to `ρ`-replicability for **any** target `ρ > 0`.
See `exists_amplifyReplicability_accurate` for preserved `(good, β)` accuracy under `O(β / T)`
initial error. -/
theorem exists_amplifyReplicability [DecidableEq α] (A : Algorithm X Ω α m) {𝒟 : Set (PMF X)}
    {ρ₀ ρ : ℝ} (hrep : IsReplicableFor A 𝒟 ρ₀) (hρ₀_nonneg : 0 ≤ ρ₀) (hρ₀ : ρ₀ < 1 / 2)
    (hρ : 0 < ρ) :
    ∃ (a b : ℝ) (T k₁ k₂ N : ℕ) (_ : NeZero T) (_ : NeZero k₁) (_ : NeZero k₂) (_ : NeZero N),
      IsReplicableFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 ρ := by
  obtain ⟨a, b, T, k₁, k₂, N, hT, hk₁, hk₂, hN, β₀_req, hβ₀_pos, hspec⟩ :=
    exists_amplifyReplicability_accurate.{u, v, w} hρ₀_nonneg hρ₀ hρ zero_lt_one
  have hacc_triv : IsAccurateFor A 𝒟 (fun _ => Set.univ) 0 := fun D _ => by simp
  exact ⟨a, b, T, k₁, k₂, N, hT, hk₁, hk₂, hN, (hspec A hrep hacc_triv hβ₀_pos.le).1⟩

end GeneralDomainAmplification

end Cslib.MachineLearning.Replicable
