/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.Bandits.Basic
public import CslibFrontier.MachineLearning.OnlineLearning.Hedge
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The EXP3 algorithm for adversarial multi-armed bandits

In the nonstochastic (oblivious adversarial) `K`-armed bandit problem, the learner observes only
the feedback of the single arm `I_t` it pulls in round `t`. Dividing that observed scalar by the
selection probability `p_t(I_t)` and zeroing out all unpulled arms gives the *importance-weighted
estimator* `importanceWeightedEst`:

  `ℓ̃_t(i) = (ℓ_t(I_t) / p_t(I_t)) * 1_{i = I_t}`,

which is conditionally unbiased (`𝔼_{I_t ∼ p_t}[ℓ̃_t(i)] = ℓ_t(i)`, `sum_importanceWeightedEst`)
with expected inner-product second moment `𝔼_{I_t ∼ p_t}[∑_i p_t(i) ℓ̃_t(i)²] = ∑_a ℓ_t(a)²`
(`sum_expected_sq_importanceWeightedEst`).

This module formalizes both standard presentations of **EXP3** as genuine partial-information
`RandomizedPolicy` learners (taking only `List (BanditStep ι)` as input):

1. **Loss-based pure-exponential `EXP3`** (`exp3Policy`, [BubeckCesaBianchi2012, §3.1, Theorem 3.1],
   locator not re-verified against primary PDF): updates weights multiplicatively by
   `exp (-η ℓ̃_t(i))` with no uniform mixing. Along every realized arm trajectory, its weights and
   probabilities coincide with `OnlineLearning.Experts.weight` / `prob` for `hedgeFactor η`
   (`exp3Weight_eq_experts_weight`, `exp3Prob_eq_experts_prob`). Averaging the nonnegative-loss
   Hedge inequality `Experts.hedge_regret_le_of_nonneg` over `trajectoryPMF` yields
   `E.pseudoRegret (exp3Policy η) T ≤ η T K / 2 + ln K / η` (`exp3_pseudoRegret_le`), and tuning
   `η = √(2 ln K / (T K))` (`exp3Rate`) gives `E.pseudoRegret ≤ √(2 T K ln K)` for every horizon
   `T : ℕ` (`exp3_pseudoRegret_le_sqrt`).
2. **Reward-based `γ`-mixed `Exp3`** (`exp3GammaPolicy`, [AuerCesaBianchiFreundSchapire2002, §3,
   Theorem 3.1 and Corollary 3.2], locators not re-verified against primary PDF): mixes exponential
   weights on estimated rewards `(1 - γ) w_i / W + γ / K` for `γ ∈ (0, 1]`, bounding expected weak
   regret by `(e - 1) γ G_max + K ln K / γ` (`exp3Gamma_rewardRegret_le`) and, under
   `γ = min 1 √(K ln K / ((e - 1) T))` (`exp3GammaRate`), by `2 √((e - 1) T K ln K)`
   (`exp3Gamma_rewardRegret_le_sqrt`).

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Bandits.importanceWeightedEst`: single-arm importance
  estimator `(value / p(arm)) * 1_{i = arm}`.
* `Cslib.MachineLearning.OnlineLearning.Bandits.exp3Weight`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.exp3Prob`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.exp3Policy`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.exp3Rate`: loss-based `EXP3` and its tuned rate
  `√(2 ln K / (T K))`.
* `Cslib.MachineLearning.OnlineLearning.Bandits.exp3GammaWeight`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.exp3GammaProb`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.exp3GammaPolicy`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.exp3GammaRate`: reward-based `γ`-mixed `Exp3` and
  its tuned exploration parameter `min 1 √(K ln K / ((e - 1) T))`.
* `Cslib.MachineLearning.OnlineLearning.Bandits.bestCumReward`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.obliviousRewardRegret`: hindsight maximum cumulative
  reward and expected weak regret on oblivious reward tables.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Bandits.sum_importanceWeightedEst`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.sum_expected_sq_importanceWeightedEst`:
  unbiasedness and second-moment identity of the importance-weighted estimator.
* `Cslib.MachineLearning.OnlineLearning.Bandits.exp3_regret_le_sq`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.exp3_pseudoRegret_le`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.exp3_pseudoRegret_le_sqrt`: finite-time second-order
  and `√(2 T K ln K)` pseudo-regret bounds of loss-based `EXP3`
  ([BubeckCesaBianchi2012, Theorem 3.1], locator not re-verified against primary PDF).
* `Cslib.MachineLearning.OnlineLearning.Bandits.exp3Gamma_rewardRegret_le`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.exp3Gamma_rewardRegret_le_sqrt`: finite-time
  `(e - 1) γ G_max + K ln K / γ` and `2 √((e - 1) T K ln K)` expected regret bounds of reward-based
  `Exp3` ([AuerCesaBianchiFreundSchapire2002, Theorem 3.1 and Corollary 3.2], locators not
  re-verified against primary PDF).

## References

* [P. Auer, N. Cesa-Bianchi, Y. Freund, R. E. Schapire, *The Nonstochastic Multiarmed Bandit
  Problem*][AuerCesaBianchiFreundSchapire2002]
* [S. Bubeck, N. Cesa-Bianchi, *Regret Analysis of Stochastic and Nonstochastic Multi-Armed Bandit
  Problems*][BubeckCesaBianchi2012]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Bandits

open Finset Real
open scoped BigOperators

/-! ### Importance-weighted single-arm estimator -/

section Estimator

variable {ι : Type*} [DecidableEq ι]

/-- Importance-weighted single-arm estimator `(step.value / p step.arm) * 1_{i = step.arm}`
([AuerCesaBianchiFreundSchapire2002, §3]; [BubeckCesaBianchi2012, §3.1], locators not re-verified
against primary PDF). -/
noncomputable def importanceWeightedEst (p : ι → ℝ) (step : BanditStep ι) (i : ι) : ℝ :=
  if i = step.arm then step.value / p step.arm else 0

@[simp]
theorem importanceWeightedEst_apply (p : ι → ℝ) (step : BanditStep ι) (i : ι) :
    importanceWeightedEst p step i = if i = step.arm then step.value / p step.arm else 0 := by
  rw [importanceWeightedEst]

theorem importanceWeightedEst_nonneg {p : ι → ℝ} {step : BanditStep ι}
    (hp : 0 ≤ p step.arm) (hv : 0 ≤ step.value) (i : ι) :
    0 ≤ importanceWeightedEst p step i := by
  rw [importanceWeightedEst_apply]
  split_ifs
  · exact div_nonneg hv hp
  · exact le_rfl

/-- **Unbiasedness of importance weighting**: drawing `a` with mass `p a` makes
`importanceWeightedEst p ⟨a, f a⟩ i` an unbiased estimator of `f i` whenever `p i ≠ 0`. -/
theorem sum_importanceWeightedEst [Fintype ι] {p : ι → ℝ} (f : ι → ℝ) {i : ι} (hp : p i ≠ 0) :
    ∑ a : ι, p a * importanceWeightedEst p ⟨a, f a⟩ i = f i := by
  rw [sum_eq_single i]
  · simp [importanceWeightedEst_apply, mul_div_cancel₀ _ hp]
  · intro a _ ha
    simp [importanceWeightedEst_apply, ha.symm]
  · simp

/-- Pathwise inner product `∑_i p(i) * ℓ̃(i)` recovers the realized scalar `step.value`. -/
theorem sum_mul_importanceWeightedEst [Fintype ι] {p : ι → ℝ} {step : BanditStep ι}
    (hp : p step.arm ≠ 0) :
    ∑ i : ι, p i * importanceWeightedEst p step i = step.value := by
  rw [sum_eq_single step.arm]
  · simp [importanceWeightedEst_apply, mul_div_cancel₀ _ hp]
  · intro i _ hi
    simp [importanceWeightedEst_apply, hi]
  · simp

/-- Pathwise weighted second moment `∑_i p(i) * ℓ̃(i)² = step.value² / p(step.arm)`. -/
theorem sum_mul_sq_importanceWeightedEst [Fintype ι] {p : ι → ℝ} {step : BanditStep ι}
    (hp : p step.arm ≠ 0) :
    ∑ i : ι, p i * importanceWeightedEst p step i ^ 2 = step.value ^ 2 / p step.arm := by
  rw [sum_eq_single step.arm]
  · simp only [importanceWeightedEst_apply, ↓reduceIte]
    field_simp
  · intro i _ hi
    simp [importanceWeightedEst_apply, hi]
  · simp

/-- Expected weighted second moment under `a ∼ p` equals `∑_a f(a)²`. -/
theorem sum_expected_sq_importanceWeightedEst [Fintype ι] {p : ι → ℝ} (f : ι → ℝ)
    (hp : ∀ a, p a ≠ 0) :
    ∑ a : ι, p a * (∑ i : ι, p i * importanceWeightedEst p ⟨a, f a⟩ i ^ 2) =
      ∑ a : ι, f a ^ 2 := by
  refine sum_congr rfl fun a _ => ?_
  rw [sum_mul_sq_importanceWeightedEst (hp a), mul_div_cancel₀ _ (hp a)]

end Estimator

/-! ### Loss-based `EXP3` ([BubeckCesaBianchi2012, Theorem 3.1]) -/

section LossEXP3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One-round multiplicative weight update of loss-based `EXP3` from a bandit observation `step`. -/
private noncomputable def exp3Step (η : ℝ) (w : ι → ℝ) (step : BanditStep ι) (i : ι) : ℝ :=
  w i * Experts.hedgeFactor η (importanceWeightedEst (fun j => w j / ∑ k, w k) step i)

/-- Cumulative exponential weights of loss-based `EXP3` after observing transcript `hist`. -/
noncomputable def exp3Weight (η : ℝ) (hist : List (BanditStep ι)) : ι → ℝ :=
  hist.foldl (exp3Step η) (fun _ => 1)

/-- Arm-selection probability distribution of loss-based `EXP3` after observing `hist`. -/
noncomputable def exp3Prob (η : ℝ) (hist : List (BanditStep ι)) (i : ι) : ℝ :=
  exp3Weight η hist i / ∑ j, exp3Weight η hist j

@[simp]
theorem exp3Weight_nil (η : ℝ) (i : ι) :
    exp3Weight η ([] : List (BanditStep ι)) i = 1 := by
  simp [exp3Weight]

theorem exp3Weight_append_singleton (η : ℝ) (hist : List (BanditStep ι)) (step : BanditStep ι)
    (i : ι) :
    exp3Weight η (hist ++ [step]) i =
      exp3Weight η hist i *
        Experts.hedgeFactor η (importanceWeightedEst (exp3Prob η hist) step i) := by
  simp [exp3Weight, exp3Step, exp3Prob]

theorem exp3Weight_pos (η : ℝ) (hist : List (BanditStep ι)) (i : ι) :
    0 < exp3Weight η hist i := by
  induction hist using List.reverseRecOn with
  | nil => simp
  | append_singleton hist step ih =>
    rw [exp3Weight_append_singleton, Experts.hedgeFactor_apply]
    exact mul_pos ih (exp_pos _)

theorem sum_exp3Weight_pos [Nonempty ι] (η : ℝ) (hist : List (BanditStep ι)) :
    0 < ∑ j, exp3Weight η hist j :=
  sum_pos (fun j _ => exp3Weight_pos η hist j) univ_nonempty

theorem exp3Prob_pos [Nonempty ι] (η : ℝ) (hist : List (BanditStep ι)) (i : ι) :
    0 < exp3Prob η hist i :=
  div_pos (exp3Weight_pos η hist i) (sum_exp3Weight_pos η hist)

theorem exp3Prob_nonneg (η : ℝ) (hist : List (BanditStep ι)) (i : ι) :
    0 ≤ exp3Prob η hist i :=
  div_nonneg (exp3Weight_pos η hist i).le (sum_nonneg fun j _ => (exp3Weight_pos η hist j).le)

@[simp]
theorem exp3Prob_nil (η : ℝ) (i : ι) :
    exp3Prob η ([] : List (BanditStep ι)) i = 1 / Fintype.card ι := by
  simp [exp3Prob]

theorem sum_exp3Prob [Nonempty ι] (η : ℝ) (hist : List (BanditStep ι)) :
    ∑ i, exp3Prob η hist i = 1 := by
  simp only [exp3Prob, ← sum_div]
  exact div_self (sum_exp3Weight_pos η hist).ne'

/-- Discrete `PMF` over arms played by loss-based `EXP3`. -/
private noncomputable def exp3PMF [Nonempty ι] (η : ℝ) (hist : List (BanditStep ι)) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (exp3Prob η hist i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => exp3Prob_nonneg η hist i,
      sum_exp3Prob η hist, ENNReal.ofReal_one])

private theorem toReal_exp3PMF_apply [Nonempty ι] (η : ℝ) (hist : List (BanditStep ι)) (i : ι) :
    (exp3PMF η hist i).toReal = exp3Prob η hist i := by
  rw [exp3PMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (exp3Prob_nonneg η hist i)]

/-- Loss-based `EXP3` as a partial-information `RandomizedPolicy`
([BubeckCesaBianchi2012, §3.1], locator not re-verified against primary PDF). -/
noncomputable def exp3Policy [Nonempty ι] (η : ℝ) : RandomizedPolicy ι where
  play := exp3PMF η

private theorem exp3Policy_play [Nonempty ι] (η : ℝ) (hist : List (BanditStep ι)) :
    (exp3Policy η).play hist = exp3PMF η hist := by
  rw [exp3Policy]

/-- Sequence of importance-weighted loss vectors reconstructed along an infinite arm sequence
`I : ℕ → ι` on loss table `ℓ : ℕ → ι → ℝ`. -/
noncomputable def exp3EstLossSeq (η : ℝ) (ℓ : ℕ → ι → ℝ) (I : ℕ → ι) (t : ℕ) : ι → ℝ :=
  importanceWeightedEst (exp3Prob η (List.ofFn fun r : Fin t => ⟨I r, ℓ r (I r)⟩))
    ⟨I t, ℓ t (I t)⟩

/-- Along every realized arm sequence `I`, `exp3Weight` equals `Experts.weight` for `hedgeFactor η`
on the estimated loss sequence `exp3EstLossSeq`. -/
theorem exp3Weight_eq_experts_weight (η : ℝ) (ℓ : ℕ → ι → ℝ) (I : ℕ → ι) (t : ℕ) :
    exp3Weight η (List.ofFn fun r : Fin t => ⟨I r, ℓ r (I r)⟩) =
      Experts.weight (Experts.hedgeFactor η) (exp3EstLossSeq η ℓ I) t := by
  induction t with
  | zero =>
    funext i
    simp [Experts.weight_zero]
  | succ t ih =>
    funext i
    rw [List.ofFn_succ_last, exp3Weight_append_singleton, Experts.weight_succ, ← ih]
    rfl

/-- Along every realized arm sequence `I`, `exp3Prob` equals `Experts.prob` for `hedgeFactor η` on
`exp3EstLossSeq`. -/
theorem exp3Prob_eq_experts_prob (η : ℝ) (ℓ : ℕ → ι → ℝ) (I : ℕ → ι) (t : ℕ) :
    exp3Prob η (List.ofFn fun r : Fin t => ⟨I r, ℓ r (I r)⟩) =
      Experts.prob (Experts.hedgeFactor η) (exp3EstLossSeq η ℓ I) t := by
  funext i
  simp only [exp3Prob, Experts.prob, Experts.potential, exp3Weight_eq_experts_weight]

/-- Prefix of a finite trajectory `traj : Fin T → ι` of length `s ≤ T`. -/
private def prefixHistory (ℓ : ℕ → ι → ℝ) {T : ℕ} (traj : Fin T → ι) (s : ℕ) (hs : s ≤ T) :
    List (BanditStep ι) :=
  List.ofFn fun r : Fin s => ⟨traj ⟨r.1, r.isLt.trans_le hs⟩,
    ℓ r.1 (traj ⟨r.1, r.isLt.trans_le hs⟩)⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem prefixHistory_succ (ℓ : ℕ → ι → ℝ) {T s : ℕ} (traj : Fin T → ι)
    (hs : s + 1 ≤ T) :
    prefixHistory ℓ traj (s + 1) hs =
      prefixHistory ℓ traj s (Nat.le_of_succ_le hs) ++
        [⟨traj ⟨s, hs⟩, ℓ s (traj ⟨s, hs⟩)⟩] :=
  List.ofFn_succ_last

omit [Fintype ι] [DecidableEq ι] in
private theorem prefixHistory_snoc_of_le (ℓ : ℕ → ι → ℝ) {T s : ℕ} (traj : Fin T → ι) (a : ι)
    {hs : s ≤ T} (hs' : s ≤ T + 1) :
    prefixHistory ℓ (Fin.snoc (α := fun _ => ι) traj a) s hs' = prefixHistory ℓ traj s hs := by
  unfold prefixHistory
  congr 1
  funext r
  have hcast : (⟨r.1, r.isLt.trans_le hs'⟩ : Fin (T + 1)) =
      (⟨r.1, r.isLt.trans_le hs⟩ : Fin T).castSucc := rfl
  rw [hcast, Fin.snoc_castSucc]

omit [Fintype ι] [DecidableEq ι] in
private theorem prefixHistory_snoc_last (ℓ : ℕ → ι → ℝ) {T : ℕ} (traj : Fin T → ι) (a : ι)
    (hT : T ≤ T + 1) :
    prefixHistory ℓ (Fin.snoc (α := fun _ => ι) traj a) T hT = historyOfArms ℓ traj := by
  rw [prefixHistory, historyOfArms_def]
  congr 1
  funext r
  have hcast : (⟨r.1, r.isLt.trans_le hT⟩ : Fin (T + 1)) = r.castSucc := rfl
  rw [hcast, Fin.snoc_castSucc]

omit [DecidableEq ι] in
/-- General tower-property expectation along `trajectoryPMF`: if each round's observable
`f t hist a` has constant conditional expectation `c t` under `pol.play hist`, then the expected
cumulative sum of `f t (prefixHistory env traj t) (traj t)` equals `∑ t < T, c t`. -/
private theorem expected_sum_prefix_eq (pol : RandomizedPolicy ι) (env : ℕ → ι → ℝ)
    (f : ℕ → List (BanditStep ι) → ι → ℝ) (c : ℕ → ℝ)
    (hcond : ∀ (t : ℕ) (hist : List (BanditStep ι)),
      ∑ a : ι, (pol.play hist a).toReal * f t hist a = c t)
    (T : ℕ) :
    (∑ traj : Fin T → ι, (trajectoryPMF pol env T traj).toReal *
      ∑ t : Fin T, f t (prefixHistory env traj t.1 t.isLt.le) (traj t)) =
      ∑ t ∈ range T, c t := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [trajectoryPMF_succ, Cslib.Probability.PMF.sum_bind_mul, sum_range_succ, ← ih]
    have hstep : ∀ prev : Fin T → ι,
        (∑ b : Fin (T + 1) → ι,
          (((pol.play (historyOfArms env prev)).map
            (Fin.snoc (α := fun _ => ι) prev)) b).toReal *
            ∑ t : Fin (T + 1), f t (prefixHistory env b t.1 t.isLt.le) (b t)) =
          (∑ t : Fin T, f t (prefixHistory env prev t.1 t.isLt.le) (prev t)) + c T := by
      intro prev
      rw [Cslib.Probability.PMF.sum_map_mul]
      have hsnoc : ∀ a : ι,
          (∑ t : Fin (T + 1), f t
            (prefixHistory env (Fin.snoc (α := fun _ => ι) prev a) t.1 t.isLt.le)
            (Fin.snoc (α := fun _ => ι) prev a t)) =
            (∑ t : Fin T, f t (prefixHistory env prev t.1 t.isLt.le) (prev t)) +
              f T (historyOfArms env prev) a := fun a => by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
        rw [prefixHistory_snoc_last]
        congr 1
        exact sum_congr rfl fun t _ => by rw [prefixHistory_snoc_of_le env prev a (hs := t.isLt.le)]
      simp only [hsnoc, mul_add, sum_add_distrib, ← sum_mul,
        Cslib.Probability.PMF.sum_toReal, one_mul, hcond T (historyOfArms env prev)]
    simp only [hstep, mul_add, sum_add_distrib, ← sum_mul,
      Cslib.Probability.PMF.sum_toReal, one_mul]

/-- Tower-property unbiasedness of cumulative importance-weighted estimates along `trajectoryPMF`
for any randomized policy `pol` with strictly positive arm probabilities `probFn`. -/
private theorem expected_sum_importanceWeightedEst_eq (pol : RandomizedPolicy ι)
    (probFn : List (BanditStep ι) → ι → ℝ)
    (hplay : ∀ hist a, (pol.play hist a).toReal = probFn hist a)
    (hne : ∀ hist a, probFn hist a ≠ 0)
    (env : ℕ → ι → ℝ) (T : ℕ) (i : ι) :
    (∑ traj : Fin T → ι, (trajectoryPMF pol env T traj).toReal *
      ∑ t : Fin T, importanceWeightedEst (probFn (prefixHistory env traj t.1 t.isLt.le))
        ⟨traj t, env t (traj t)⟩ i) =
      ∑ t ∈ range T, env t i :=
  expected_sum_prefix_eq pol env
    (fun t hist a => importanceWeightedEst (probFn hist) ⟨a, env t a⟩ i)
    (fun t => env t i)
    (fun t hist => by
      simp_rw [hplay]
      exact sum_importanceWeightedEst (env t) (hne hist i))
    T

omit [DecidableEq ι] in
/-- Tower-property second-moment identity `𝔼[∑_t v_t(I_t)² / p_t(I_t)] = ∑_{t < T} ∑_a v_t(a)²`
for any randomized policy `pol` with strictly positive arm probabilities `probFn`. -/
private theorem expected_sum_sq_div_probFn_eq (pol : RandomizedPolicy ι)
    (probFn : List (BanditStep ι) → ι → ℝ)
    (hplay : ∀ hist a, (pol.play hist a).toReal = probFn hist a)
    (hne : ∀ hist a, probFn hist a ≠ 0)
    (env : ℕ → ι → ℝ) (T : ℕ) :
    (∑ traj : Fin T → ι, (trajectoryPMF pol env T traj).toReal *
      ∑ t : Fin T, env t (traj t) ^ 2 / probFn (prefixHistory env traj t.1 t.isLt.le) (traj t)) =
      ∑ t ∈ range T, ∑ a : ι, env t a ^ 2 :=
  expected_sum_prefix_eq pol env
    (fun t hist a => env t a ^ 2 / probFn hist a)
    (fun t => ∑ a : ι, env t a ^ 2)
    (fun t hist => by
      simp_rw [hplay]
      exact sum_congr rfl fun a _ => mul_div_cancel₀ _ (hne hist a))
    T

omit [DecidableEq ι] in
/-- With a single arm (`Subsingleton ι`), every trajectory picks that arm, so `expectedTotal`
equals the arm's cumulative feedback. -/
private theorem expectedTotal_eq_sum_of_subsingleton [Subsingleton ι]
    (pol : RandomizedPolicy ι) (env : ℕ → ι → ℝ) (T : ℕ) (i : ι) :
    expectedTotal pol env T = ∑ t ∈ range T, env t i := by
  have htraj : ∀ traj : Fin T → ι,
      (∑ t : Fin T, env t (traj t)) = ∑ t ∈ range T, env t i := fun traj => by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun t _ => by rw [Subsingleton.elim (traj t) i]
  simp only [expectedTotal_def, htraj, ← sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]

/-- Expected cumulative estimated loss of arm `i` equals its true cumulative loss
`∑_{t < T} ℓ t i`. -/
private theorem expected_sum_estLoss_eq [Nonempty ι] (η : ℝ) (ℓ : ℕ → ι → ℝ) (T : ℕ) (i : ι) :
    (∑ traj : Fin T → ι, (trajectoryPMF (exp3Policy η) ℓ T traj).toReal *
      ∑ t : Fin T, importanceWeightedEst (exp3Prob η (prefixHistory ℓ traj t.1 t.isLt.le))
        ⟨traj t, ℓ t (traj t)⟩ i) =
      ∑ t ∈ range T, ℓ t i :=
  expected_sum_importanceWeightedEst_eq (exp3Policy η) (exp3Prob η)
    (fun hist a => by rw [exp3Policy_play, toReal_exp3PMF_apply])
    (fun hist a => (exp3Prob_pos η hist a).ne') ℓ T i

/-- Expected cumulative variance proxy `∑_t ℓ_t(I_t)² / p_t(I_t)` equals `∑_{t < T} ∑_a ℓ_t(a)²`. -/
private theorem expected_sum_sq_div_prob_eq [Nonempty ι] (η : ℝ) (ℓ : ℕ → ι → ℝ) (T : ℕ) :
    (∑ traj : Fin T → ι, (trajectoryPMF (exp3Policy η) ℓ T traj).toReal *
      ∑ t : Fin T,
        ℓ t (traj t) ^ 2 / exp3Prob η (prefixHistory ℓ traj t.1 t.isLt.le) (traj t)) =
      ∑ t ∈ range T, ∑ a : ι, ℓ t a ^ 2 :=
  expected_sum_sq_div_probFn_eq (exp3Policy η) (exp3Prob η)
    (fun hist a => by rw [exp3Policy_play, toReal_exp3PMF_apply])
    (fun hist a => (exp3Prob_pos η hist a).ne') ℓ T

/-- **Second-order regret of `EXP3`** (step of [BubeckCesaBianchi2012, Theorem 3.1], locator not
re-verified against primary PDF): for any `η > 0`, nonnegative losses `ℓ`, and arm `i`,
`𝔼[∑_{t < T} ℓ_t(I_t)] ≤ ∑_{t < T} ℓ_t(i) + (η / 2) ∑_{t < T} ∑_a ℓ_t(a)² + ln K / η`. -/
theorem exp3_regret_le_sq {η : ℝ} (hη : 0 < η) {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ s < T, ∀ a, 0 ≤ ℓ s a) (i : ι) :
    haveI : Nonempty ι := ⟨i⟩
    expectedTotal (exp3Policy η) ℓ T ≤
      ∑ t ∈ range T, ℓ t i + (η / 2) * ∑ t ∈ range T, ∑ a : ι, ℓ t a ^ 2 +
        log (Fintype.card ι) / η := by
  have : Nonempty ι := ⟨i⟩
  -- Pathwise Hedge inequality along each realized trajectory `traj : Fin T → ι`.
  have hpath : ∀ traj : Fin T → ι,
      (∑ t : Fin T, ℓ t (traj t)) ≤
        (∑ t : Fin T, importanceWeightedEst (exp3Prob η (prefixHistory ℓ traj t.1 t.isLt.le))
          ⟨traj t, ℓ t (traj t)⟩ i) +
          (η / 2) * (∑ t : Fin T,
            ℓ t (traj t) ^ 2 / exp3Prob η (prefixHistory ℓ traj t.1 t.isLt.le) (traj t)) +
          log (Fintype.card ι) / η := by
    intro traj
    let I : ℕ → ι := fun s => if hs : s < T then traj ⟨s, hs⟩ else i
    have hpre : ∀ t : Fin T,
        (List.ofFn fun r : Fin t.1 => (⟨I r, ℓ r (I r)⟩ : BanditStep ι)) =
          prefixHistory ℓ traj t.1 t.isLt.le := by
      intro t
      unfold prefixHistory
      congr 1
      funext r
      have hr : r.1 < T := r.isLt.trans t.isLt
      simp [I, hr]
    have hest_nonneg : ∀ s < T, ∀ j, 0 ≤ exp3EstLossSeq η ℓ I s j := by
      intro s hs j
      unfold exp3EstLossSeq
      have hI : 0 ≤ ℓ s (I s) := hℓ s hs (I s)
      exact importanceWeightedEst_nonneg (exp3Prob_nonneg η _ _) hI j
    have hhedge := Experts.hedge_regret_le_of_nonneg (T := T) hη hest_nonneg i
    have hlhs : (∑ t ∈ range T,
        ∑ j, Experts.prob (Experts.hedgeFactor η) (exp3EstLossSeq η ℓ I) t j *
          exp3EstLossSeq η ℓ I t j) = ∑ t : Fin T, ℓ t (traj t) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun t _ => ?_
      rw [← exp3Prob_eq_experts_prob, hpre t]
      unfold exp3EstLossSeq
      rw [hpre t]
      have hIt : I t.1 = traj t := by simp [I, t.isLt]
      rw [hIt]
      exact sum_mul_importanceWeightedEst (exp3Prob_pos η _ _).ne'
    have hcomp : (∑ t ∈ range T, exp3EstLossSeq η ℓ I t i) =
        ∑ t : Fin T, importanceWeightedEst (exp3Prob η (prefixHistory ℓ traj t.1 t.isLt.le))
          ⟨traj t, ℓ t (traj t)⟩ i := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun t _ => ?_
      unfold exp3EstLossSeq
      rw [hpre t]
      have hIt : I t.1 = traj t := by simp [I, t.isLt]
      rw [hIt]
    have hvar : (∑ t ∈ range T,
        ∑ j, Experts.prob (Experts.hedgeFactor η) (exp3EstLossSeq η ℓ I) t j *
          exp3EstLossSeq η ℓ I t j ^ 2) =
      ∑ t : Fin T,
        ℓ t (traj t) ^ 2 / exp3Prob η (prefixHistory ℓ traj t.1 t.isLt.le) (traj t) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun t _ => ?_
      rw [← exp3Prob_eq_experts_prob, hpre t]
      unfold exp3EstLossSeq
      rw [hpre t]
      have hIt : I t.1 = traj t := by simp [I, t.isLt]
      rw [hIt]
      exact sum_mul_sq_importanceWeightedEst (exp3Prob_pos η _ _).ne'
    rw [hlhs, hcomp, hvar] at hhedge
    exact hhedge
  rw [expectedTotal_def]
  calc ∑ traj : Fin T → ι, (trajectoryPMF (exp3Policy η) ℓ T traj).toReal *
        ∑ t : Fin T, ℓ t (traj t)
      ≤ ∑ traj : Fin T → ι, (trajectoryPMF (exp3Policy η) ℓ T traj).toReal *
          ((∑ t : Fin T, importanceWeightedEst (exp3Prob η (prefixHistory ℓ traj t.1 t.isLt.le))
            ⟨traj t, ℓ t (traj t)⟩ i) +
            (η / 2) * (∑ t : Fin T,
              ℓ t (traj t) ^ 2 / exp3Prob η (prefixHistory ℓ traj t.1 t.isLt.le) (traj t)) +
            log (Fintype.card ι) / η) :=
        sum_le_sum fun traj _ => mul_le_mul_of_nonneg_left (hpath traj) ENNReal.toReal_nonneg
    _ = ∑ t ∈ range T, ℓ t i + (η / 2) * ∑ t ∈ range T, ∑ a : ι, ℓ t a ^ 2 +
          log (Fintype.card ι) / η := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]
        congr 1
        congr 1
        · exact expected_sum_estLoss_eq η ℓ T i
        · rw [← expected_sum_sq_div_prob_eq η ℓ T, mul_sum]
          exact sum_congr rfl fun traj _ => by ring

/-- **Untuned pseudo-regret of `EXP3`** ([BubeckCesaBianchi2012, proof of Theorem 3.1], locator not
re-verified against primary PDF): for `[0, 1]`-bounded losses and any `η > 0`,
`E.pseudoRegret (exp3Policy η) T ≤ η * T * K / 2 + ln K / η`. -/
theorem exp3_pseudoRegret_le [Nonempty ι] (E : ObliviousBandit ι) {η : ℝ} (hη : 0 < η) (T : ℕ) :
    E.pseudoRegret (exp3Policy η) T ≤
      η * T * Fintype.card ι / 2 + log (Fintype.card ι) / η := by
  refine E.pseudoRegret_le_of_forall fun i => ?_
  rw [E.regretAt_def]
  have hsq_le : ∑ t ∈ range T, ∑ a : ι, E.loss t a ^ 2 ≤ T * Fintype.card ι := by
    calc ∑ t ∈ range T, ∑ a : ι, E.loss t a ^ 2
        ≤ ∑ _t ∈ range T, ∑ _a : ι, (1 : ℝ) := sum_le_sum fun t _ => sum_le_sum fun a _ => by
          have h01 := E.mem_unitInterval t a
          nlinarith [h01.1, h01.2]
      _ = T * Fintype.card ι := by simp
  have hmain := exp3_regret_le_sq (T := T) hη (fun s _ a => (E.mem_unitInterval s a).1) i
  have hmul : (η / 2) * ∑ t ∈ range T, ∑ a : ι, E.loss t a ^ 2 ≤
      η * T * Fintype.card ι / 2 := by
    calc (η / 2) * ∑ t ∈ range T, ∑ a : ι, E.loss t a ^ 2
        ≤ (η / 2) * (T * Fintype.card ι) :=
          mul_le_mul_of_nonneg_left hsq_le (by positivity)
      _ = η * T * Fintype.card ι / 2 := by ring
  linarith

/-- Horizon-tuned learning rate `√(2 ln K / (T K))` for loss-based `EXP3` (`1` in the trivial cases
`K ≤ 1` or `T = 0`). -/
noncomputable def exp3Rate (K T : ℕ) : ℝ :=
  if K ≤ 1 ∨ T = 0 then 1 else √(2 * log K / (T * K))

private theorem exp3Rate_of_two_le {K T : ℕ} (hK : 2 ≤ K) (hT : 0 < T) :
    exp3Rate K T = √(2 * log K / (T * K)) := by
  have hnot : ¬ (K ≤ 1 ∨ T = 0) := by omega
  simp [exp3Rate, hnot]

/-- **Pseudo-regret of `EXP3`** ([BubeckCesaBianchi2012, Theorem 3.1, eq. (3.2)], locator not
re-verified against primary PDF): on any `K`-armed oblivious bandit environment `E` with `[0, 1]`
losses and any horizon `T : ℕ`, `EXP3` with learning rate `exp3Rate K T` satisfies
`E.pseudoRegret ≤ √(2 T K ln K)`. -/
theorem exp3_pseudoRegret_le_sqrt [Nonempty ι] (E : ObliviousBandit ι) (T : ℕ) :
    E.pseudoRegret (exp3Policy (exp3Rate (Fintype.card ι) T)) T ≤
      √(2 * T * Fintype.card ι * log (Fintype.card ι)) := by
  set K := Fintype.card ι with hKdef
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · refine E.pseudoRegret_le_of_forall fun i => ?_
    simp [E.regretAt_def]
  by_cases hK : K ≤ 1
  · -- With a single arm, every trajectory plays that arm, so regret is identically `0`.
    have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hK
    refine (E.pseudoRegret_le_of_forall fun i => ?_).trans (sqrt_nonneg _)
    rw [E.regretAt_def, expectedTotal_eq_sum_of_subsingleton, sub_self]
  · have hK2 : 2 ≤ K := by omega
    have hL : 0 < log K := log_pos (by exact_mod_cast hK2)
    have hTK : (0 : ℝ) < T * K := by positivity
    rw [exp3Rate_of_two_le hK2 hT]
    set η := √(2 * log K / (T * K)) with hηdef
    have hη : 0 < η := sqrt_pos.mpr (div_pos (by positivity) hTK)
    refine (exp3_pseudoRegret_le E hη T).trans_eq ?_
    rw [← hKdef]
    have hηsq : η * η = 2 * log K / (T * K) := mul_self_sqrt (div_nonneg (by positivity) hTK.le)
    have hbal : η * T * K / 2 + log K / η = √(2 * T * K * log K) := by
      have hprod : η * √(2 * T * K * log K) = 2 * log K := by
        rw [hηdef, ← sqrt_mul (by positivity)]
        have h1 : 2 * log K / (T * K) * (2 * T * K * log K) = (2 * log K) ^ 2 := by
          field_simp
        rw [h1, sqrt_sq (by positivity)]
      apply mul_left_cancel₀ hη.ne'
      calc η * (η * T * K / 2 + log K / η)
          = (η * η) * (T * K) / 2 + log K := by field_simp
        _ = 2 * log K := by rw [hηsq]; field_simp; ring
        _ = η * √(2 * T * K * log K) := hprod.symm
    exact hbal

end LossEXP3

/-! ### Reward-based `γ`-mixed `Exp3` ([AuerCesaBianchiFreundSchapire2002, Theorem 3.1]) -/

section RewardEXP3

/-- Sharp scalar estimate `exp x ≤ 1 + x + (e - 2) x²` for `x ∈ [0, 1]`, obtained directly by
bounding `x ^ (n + 2) ≤ x ^ 2` termwise in the exponential power series. -/
private theorem exp_le_one_add_add_exp_one_sub_two_mul_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    exp x ≤ 1 + x + (exp 1 - 2) * x ^ 2 := by
  have hsum_x : HasSum (fun n : ℕ => x ^ n / n.factorial) (exp x) := by
    simpa only [Real.exp_eq_exp_ℝ, smul_eq_mul, inv_mul_eq_div] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have hsum_1 : HasSum (fun n : ℕ => (1 : ℝ) ^ n / n.factorial) (exp 1) := by
    simpa only [Real.exp_eq_exp_ℝ, smul_eq_mul, inv_mul_eq_div] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (1 : ℝ)
  have htail_x := (hasSum_nat_add_iff' 2).mpr hsum_x
  have htail_1 := (hasSum_nat_add_iff' 2).mpr hsum_1
  have hinit_x : (∑ i ∈ range 2, x ^ i / (i.factorial : ℝ)) = 1 + x := by
    simp [sum_range_succ, Nat.factorial]
  have hinit_1 : (∑ i ∈ range 2, (1 : ℝ) ^ i / (i.factorial : ℝ)) = 2 := by
    norm_num [sum_range_succ, Nat.factorial]
  rw [hinit_x] at htail_x
  rw [hinit_1] at htail_1
  have hle : (∑' n : ℕ, x ^ (n + 2) / (n + 2).factorial) ≤
      x ^ 2 * ∑' n : ℕ, (1 : ℝ) ^ (n + 2) / (n + 2).factorial := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) htail_x.summable (htail_1.summable.mul_left (x ^ 2))
    rw [one_pow, pow_add x n 2, mul_comm (x ^ n) (x ^ 2), mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (pow_le_one₀ hx0 hx1) (Nat.cast_nonneg _)) (sq_nonneg x)
  rw [htail_x.tsum_eq, htail_1.tsum_eq] at hle
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Mixing distribution `(1 - γ) * (w_i / ∑_k w_k) + γ / K` of reward-based `Exp3`, clamped to
`[0, 1]` outside `γ ∈ [0, 1]` so `exp3GammaPMF` is total without precondition proofs. -/
private noncomputable def exp3GammaMix (γ : ℝ) (w : ι → ℝ) (i : ι) : ℝ :=
  let γ' := max 0 (min 1 γ)
  (1 - γ') * (w i / ∑ k, w k) + γ' / Fintype.card ι

/-- One-round multiplicative weight update `w_i * exp ((γ / K) * ĝ_i)` of reward-based `Exp3`
([AuerCesaBianchiFreundSchapire2002, §3], locator not re-verified against primary PDF). -/
private noncomputable def exp3GammaStep (γ : ℝ) (w : ι → ℝ) (step : BanditStep ι) (i : ι) : ℝ :=
  let γ' := max 0 (min 1 γ)
  w i * exp ((γ' / Fintype.card ι) * importanceWeightedEst (exp3GammaMix γ w) step i)

/-- Cumulative weights of reward-based `Exp3` after observing `hist`. -/
noncomputable def exp3GammaWeight (γ : ℝ) (hist : List (BanditStep ι)) : ι → ℝ :=
  hist.foldl (exp3GammaStep γ) (fun _ => 1)

/-- Arm-selection probability distribution of reward-based `Exp3` after observing `hist`. -/
noncomputable def exp3GammaProb (γ : ℝ) (hist : List (BanditStep ι)) (i : ι) : ℝ :=
  exp3GammaMix γ (exp3GammaWeight γ hist) i

private theorem exp3GammaWeight_pos (γ : ℝ) (hist : List (BanditStep ι)) (i : ι) :
    0 < exp3GammaWeight γ hist i := by
  induction hist using List.reverseRecOn with
  | nil => simp [exp3GammaWeight]
  | append_singleton hist step ih =>
    simp only [exp3GammaWeight, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact mul_pos ih (exp_pos _)

private theorem sum_exp3GammaWeight_pos [Nonempty ι] (γ : ℝ) (hist : List (BanditStep ι)) :
    0 < ∑ k, exp3GammaWeight γ hist k :=
  sum_pos (fun k _ => exp3GammaWeight_pos γ hist k) univ_nonempty

private theorem exp3GammaProb_nonneg [Nonempty ι] (γ : ℝ) (hist : List (BanditStep ι)) (i : ι) :
    0 ≤ exp3GammaProb γ hist i := by
  unfold exp3GammaProb exp3GammaMix
  set γ' := max 0 (min 1 γ)
  have hγ0 : 0 ≤ γ' := le_max_left _ _
  have hγ1 : γ' ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have hw0 : 0 ≤ exp3GammaWeight γ hist i / ∑ k, exp3GammaWeight γ hist k :=
    div_nonneg (exp3GammaWeight_pos γ hist i).le (sum_exp3GammaWeight_pos γ hist).le
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hγ1) hw0) (div_nonneg hγ0 (Nat.cast_nonneg _))

private theorem exp3GammaProb_pos_of_pos [Nonempty ι] {γ : ℝ} (hγ0 : 0 < γ)
    (hist : List (BanditStep ι)) (i : ι) :
    0 < exp3GammaProb γ hist i := by
  unfold exp3GammaProb exp3GammaMix
  set γ' := max 0 (min 1 γ)
  have hγ' : 0 < γ' := lt_max_of_lt_right (lt_min zero_lt_one hγ0)
  have hγ1 : γ' ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have hw0 : 0 ≤ exp3GammaWeight γ hist i / ∑ k, exp3GammaWeight γ hist k :=
    div_nonneg (exp3GammaWeight_pos γ hist i).le (sum_exp3GammaWeight_pos γ hist).le
  have hK : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hγ1) hw0) (div_pos hγ' hK)

private theorem exp3GammaProb_ge_div_card [Nonempty ι] {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hist : List (BanditStep ι)) (i : ι) :
    γ / Fintype.card ι ≤ exp3GammaProb γ hist i := by
  unfold exp3GammaProb exp3GammaMix
  have hclamp : max 0 (min 1 γ) = γ := by rw [min_eq_right hγ1, max_eq_right hγ0]
  rw [hclamp]
  have hw0 : 0 ≤ exp3GammaWeight γ hist i / ∑ k, exp3GammaWeight γ hist k :=
    div_nonneg (exp3GammaWeight_pos γ hist i).le (sum_exp3GammaWeight_pos γ hist).le
  linarith [mul_nonneg (sub_nonneg.mpr hγ1) hw0]

private theorem sum_exp3GammaProb [Nonempty ι] (γ : ℝ) (hist : List (BanditStep ι)) :
    ∑ i, exp3GammaProb γ hist i = 1 := by
  unfold exp3GammaProb exp3GammaMix
  set γ' := max 0 (min 1 γ)
  have hK : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hW : (∑ k, exp3GammaWeight γ hist k) ≠ 0 := (sum_exp3GammaWeight_pos γ hist).ne'
  simp only [sum_add_distrib, ← mul_sum, ← sum_div, div_self hW, mul_one, sum_const, card_univ,
    nsmul_eq_mul]
  field_simp
  ring

/-- Discrete `PMF` over arms played by reward-based `Exp3`. -/
private noncomputable def exp3GammaPMF [Nonempty ι] (γ : ℝ) (hist : List (BanditStep ι)) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (exp3GammaProb γ hist i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => exp3GammaProb_nonneg γ hist i,
      sum_exp3GammaProb γ hist, ENNReal.ofReal_one])

private theorem toReal_exp3GammaPMF_apply [Nonempty ι] (γ : ℝ) (hist : List (BanditStep ι))
    (i : ι) :
    (exp3GammaPMF γ hist i).toReal = exp3GammaProb γ hist i := by
  rw [exp3GammaPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (exp3GammaProb_nonneg γ hist i)]

/-- Reward-based `γ`-mixed `Exp3` as a partial-information `RandomizedPolicy`
([AuerCesaBianchiFreundSchapire2002, §3], locator not re-verified against primary PDF). -/
noncomputable def exp3GammaPolicy [Nonempty ι] (γ : ℝ) : RandomizedPolicy ι where
  play := exp3GammaPMF γ

private theorem exp3GammaPolicy_play [Nonempty ι] (γ : ℝ) (hist : List (BanditStep ι)) :
    (exp3GammaPolicy γ).play hist = exp3GammaPMF γ hist := by
  rw [exp3GammaPolicy]

/-- Maximum single-arm cumulative reward `G_max = max_i ∑_{t < T} g t i`. -/
noncomputable def bestCumReward [Nonempty ι] (g : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  univ.sup' univ_nonempty fun i => ∑ t ∈ range T, g t i

/-- Expected weak regret `G_max - 𝔼[∑_{t < T} g_t(I_t)]` on oblivious rewards `g`. -/
noncomputable def obliviousRewardRegret [Nonempty ι] (pol : RandomizedPolicy ι)
    (g : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  bestCumReward g T - expectedTotal pol g T

private theorem expected_sum_gammaEst_eq [Nonempty ι] {γ : ℝ} (hγ0 : 0 < γ)
    (g : ℕ → ι → ℝ) (T : ℕ) (i : ι) :
    (∑ traj : Fin T → ι, (trajectoryPMF (exp3GammaPolicy γ) g T traj).toReal *
      ∑ t : Fin T, importanceWeightedEst (exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le))
        ⟨traj t, g t (traj t)⟩ i) =
      ∑ t ∈ range T, g t i :=
  expected_sum_importanceWeightedEst_eq (exp3GammaPolicy γ) (exp3GammaProb γ)
    (fun hist a => by rw [exp3GammaPolicy_play, toReal_exp3GammaPMF_apply])
    (fun hist a => (exp3GammaProb_pos_of_pos hγ0 hist a).ne') g T i

private theorem expected_sum_sq_div_gammaProb_eq [Nonempty ι] {γ : ℝ} (hγ0 : 0 < γ)
    (g : ℕ → ι → ℝ) (T : ℕ) :
    (∑ traj : Fin T → ι, (trajectoryPMF (exp3GammaPolicy γ) g T traj).toReal *
      ∑ t : Fin T,
        g t (traj t) ^ 2 / exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le) (traj t)) =
      ∑ t ∈ range T, ∑ a : ι, g t a ^ 2 :=
  expected_sum_sq_div_probFn_eq (exp3GammaPolicy γ) (exp3GammaProb γ)
    (fun hist a => by rw [exp3GammaPolicy_play, toReal_exp3GammaPMF_apply])
    (fun hist a => (exp3GammaProb_pos_of_pos hγ0 hist a).ne') g T

/-- Pathwise log-potential inequality for `exp3GammaWeight` when `0 < γ < 1` and `g ∈ [0, 1]`. -/
private theorem exp3Gamma_pathwise_bound [Nonempty ι] {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {g : ℕ → ι → ℝ} {T : ℕ} (hg : ∀ s < T, ∀ a, g s a ∈ Set.Icc (0 : ℝ) 1)
    (traj : Fin T → ι) (i : ι) :
    (1 - γ) * (∑ t : Fin T,
      importanceWeightedEst (exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le))
        ⟨traj t, g t (traj t)⟩ i) -
      (1 - γ) * Fintype.card ι * log (Fintype.card ι) / γ ≤
      (∑ t : Fin T, g t (traj t)) +
        (exp 1 - 2) * (γ / Fintype.card ι) *
          ∑ t : Fin T,
            g t (traj t) ^ 2 / exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le) (traj t) := by
  set K : ℝ := (Fintype.card ι : ℝ)
  have hK : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  have hclamp : max 0 (min 1 γ) = γ := by rw [min_eq_right hγ1.le, max_eq_right hγ0.le]
  have h1γ : 0 < 1 - γ := sub_pos.mpr hγ1
  -- Telescoping potential `W_s = ∑_j exp3GammaWeight γ (prefixHistory g traj s _) j`.
  have hstep_pot : ∀ t : Fin T,
      log (∑ j, exp3GammaWeight γ (prefixHistory g traj (t.1 + 1) t.isLt) j) -
        log (∑ j, exp3GammaWeight γ (prefixHistory g traj t.1 t.isLt.le) j) ≤
        ((γ / K) / (1 - γ)) * g t (traj t) +
          ((exp 1 - 2) * (γ / K) ^ 2 / (1 - γ)) *
            (g t (traj t) ^ 2 / exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le) (traj t)) := by
    intro t
    set hist := prefixHistory g traj t.1 t.isLt.le
    set step : BanditStep ι := ⟨traj t, g t (traj t)⟩
    rw [prefixHistory_succ g traj t.isLt]
    change log (∑ j, exp3GammaWeight γ (hist ++ [step]) j) - log (∑ j, exp3GammaWeight γ hist j) ≤
      _
    set W := ∑ k, exp3GammaWeight γ hist k
    have hW : 0 < W := sum_exp3GammaWeight_pos γ hist
    have hW1 : 0 < ∑ j, exp3GammaWeight γ (hist ++ [step]) j :=
      sum_exp3GammaWeight_pos γ (hist ++ [step])
    rw [← log_div hW1.ne' hW.ne']
    have hratio : (∑ j, exp3GammaWeight γ (hist ++ [step]) j) / W ≤
        1 + ((γ / K) / (1 - γ)) * g t (traj t) +
          ((exp 1 - 2) * (γ / K) ^ 2 / (1 - γ)) *
            (g t (traj t) ^ 2 / exp3GammaProb γ hist (traj t)) := by
      rw [sum_div]
      have hterm : ∀ j : ι,
          exp3GammaWeight γ (hist ++ [step]) j / W ≤
            (exp3GammaWeight γ hist j / W) +
              (exp3GammaProb γ hist j / (1 - γ)) *
                ((γ / K) * importanceWeightedEst (exp3GammaMix γ (exp3GammaWeight γ hist)) step j +
                  (exp 1 - 2) *
                    ((γ / K) * importanceWeightedEst (exp3GammaProb γ hist) step j) ^ 2) := by
        intro j
        have hrec : exp3GammaWeight γ (hist ++ [step]) j =
            exp3GammaWeight γ hist j *
              exp ((γ / K) * importanceWeightedEst (exp3GammaProb γ hist) step j) := by
          simp [exp3GammaWeight, exp3GammaStep, exp3GammaProb, hclamp, K]
        rw [hrec, mul_div_right_comm]
        set x := (γ / K) * importanceWeightedEst (exp3GammaProb γ hist) step j
        have hx0 : 0 ≤ x := mul_nonneg (div_nonneg hγ0.le hK.le)
          (importanceWeightedEst_nonneg (exp3GammaProb_nonneg γ hist _) (hg t t.isLt _).1 j)
        have hx1 : x ≤ 1 := by
          dsimp only [x]
          rw [importanceWeightedEst_apply]
          split_ifs
          · have hp_ge := exp3GammaProb_ge_div_card hγ0.le hγ1.le hist step.arm
            have hg1 : step.value ≤ 1 := (hg t t.isLt (traj t)).2
            calc (γ / K) * (step.value / exp3GammaProb γ hist step.arm)
                ≤ (γ / K) * (1 / (γ / K)) := by gcongr
              _ = 1 := by field_simp
          · simp
        have hexp := exp_le_one_add_add_exp_one_sub_two_mul_sq hx0 hx1
        have hw_le_p : exp3GammaWeight γ hist j / W ≤ exp3GammaProb γ hist j / (1 - γ) := by
          rw [le_div_iff₀ h1γ]
          unfold exp3GammaProb exp3GammaMix
          rw [hclamp, mul_comm (exp3GammaWeight γ hist j / W) (1 - γ)]
          linarith [div_nonneg hγ0.le hK.le]
        have hnonneg_quad : 0 ≤ x + (exp 1 - 2) * x ^ 2 := by
          have he2 : 0 ≤ exp 1 - 2 := by linarith [add_one_le_exp (1 : ℝ)]
          positivity
        have hw0 : 0 ≤ exp3GammaWeight γ hist j / W :=
          div_nonneg (exp3GammaWeight_pos γ hist j).le hW.le
        calc (exp3GammaWeight γ hist j / W) * exp x
            ≤ (exp3GammaWeight γ hist j / W) * (1 + (x + (exp 1 - 2) * x ^ 2)) :=
              mul_le_mul_of_nonneg_left (by linarith) hw0
          _ = (exp3GammaWeight γ hist j / W) +
                (exp3GammaWeight γ hist j / W) * (x + (exp 1 - 2) * x ^ 2) := by ring
          _ ≤ (exp3GammaWeight γ hist j / W) +
                (exp3GammaProb γ hist j / (1 - γ)) * (x + (exp 1 - 2) * x ^ 2) := by
              gcongr
      calc ∑ j, exp3GammaWeight γ (hist ++ [step]) j / W
          ≤ ∑ j, ((exp3GammaWeight γ hist j / W) +
              (exp3GammaProb γ hist j / (1 - γ)) *
                ((γ / K) * importanceWeightedEst (exp3GammaProb γ hist) step j +
                  (exp 1 - 2) *
                    ((γ / K) * importanceWeightedEst (exp3GammaProb γ hist) step j) ^ 2)) :=
            sum_le_sum fun j _ => hterm j
        _ = 1 + ((γ / K) / (1 - γ)) * g t (traj t) +
              ((exp 1 - 2) * (γ / K) ^ 2 / (1 - γ)) *
                (g t (traj t) ^ 2 / exp3GammaProb γ hist (traj t)) := by
            simp only [sum_add_distrib, ← sum_div]
            have hWW : (∑ j, exp3GammaWeight γ hist j) / W = 1 := div_self hW.ne'
            have hp_ne : exp3GammaProb γ hist step.arm ≠ 0 :=
              (exp3GammaProb_pos_of_pos hγ0 hist step.arm).ne'
            have hlin : (∑ j, (exp3GammaProb γ hist j / (1 - γ)) *
                ((γ / K) * importanceWeightedEst (exp3GammaProb γ hist) step j +
                  (exp 1 - 2) *
                    ((γ / K) * importanceWeightedEst (exp3GammaProb γ hist) step j) ^ 2)) =
                ((γ / K) / (1 - γ)) *
                  (∑ j, exp3GammaProb γ hist j *
                    importanceWeightedEst (exp3GammaProb γ hist) step j) +
                ((exp 1 - 2) * (γ / K) ^ 2 / (1 - γ)) *
                  (∑ j, exp3GammaProb γ hist j *
                    importanceWeightedEst (exp3GammaProb γ hist) step j ^ 2) := by
              rw [mul_sum, mul_sum, ← sum_add_distrib]
              exact sum_congr rfl fun j _ => by ring
            rw [hWW, hlin, sum_mul_importanceWeightedEst hp_ne,
              sum_mul_sq_importanceWeightedEst hp_ne]
            dsimp only [step]
            ring
    have hlog := (log_le_sub_one_of_pos (div_pos hW1 hW)).trans (sub_le_sub_right hratio 1)
    linarith
  -- Sum the telescoping log-potential bound across `t : Fin T`.
  have htel : log (∑ j, exp3GammaWeight γ (prefixHistory g traj T le_rfl) j) - log K =
      ∑ t : Fin T, (log (∑ j, exp3GammaWeight γ (prefixHistory g traj (t.1 + 1) t.isLt) j) -
        log (∑ j, exp3GammaWeight γ (prefixHistory g traj t.1 t.isLt.le) j)) := by
    let pot (s : ℕ) : ℝ :=
      if hs : s ≤ T then log (∑ j, exp3GammaWeight γ (prefixHistory g traj s hs) j) else 0
    have hpot0 : pot 0 = log K := by simp [pot, prefixHistory, exp3GammaWeight, K]
    have hpotT : pot T = log (∑ j, exp3GammaWeight γ (prefixHistory g traj T le_rfl) j) := by
      simp [pot]
    have hterm_eq : ∀ t : Fin T,
        log (∑ j, exp3GammaWeight γ (prefixHistory g traj (t.1 + 1) t.isLt) j) -
          log (∑ j, exp3GammaWeight γ (prefixHistory g traj t.1 t.isLt.le) j) =
          pot (t.1 + 1) - pot t.1 := fun t => by
      simp [pot, t.isLt, t.isLt.le]
    simp_rw [hterm_eq]
    rw [Fin.sum_univ_eq_sum_range (fun s => pot (s + 1) - pot s) T, sum_range_sub, hpotT, hpot0]
  -- Lower bound `log (∑_j w_T(j))` by `log w_T(i) = (γ / K) * ∑_t ĝ_t(i)`.
  have hlow : (γ / K) * (∑ t : Fin T,
      importanceWeightedEst (exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le))
        ⟨traj t, g t (traj t)⟩ i) ≤
      log (∑ j, exp3GammaWeight γ (prefixHistory g traj T le_rfl) j) := by
    have hle_sum : exp3GammaWeight γ (prefixHistory g traj T le_rfl) i ≤
        ∑ j, exp3GammaWeight γ (prefixHistory g traj T le_rfl) j :=
      single_le_sum (fun j _ => (exp3GammaWeight_pos γ _ j).le) (mem_univ i)
    refine le_trans ?_ (log_le_log (exp3GammaWeight_pos γ _ i) hle_sum)
    have hlog_w : ∀ (s : ℕ) (hs : s ≤ T),
        log (exp3GammaWeight γ (prefixHistory g traj s hs) i) =
          (γ / K) * ∑ r : Fin s,
            importanceWeightedEst (exp3GammaProb γ (prefixHistory g traj r.1 (r.isLt.le.trans hs)))
              ⟨traj ⟨r.1, r.isLt.trans_le hs⟩, g r.1 (traj ⟨r.1, r.isLt.trans_le hs⟩)⟩ i := by
      intro s hs
      induction s with
      | zero => simp [prefixHistory, exp3GammaWeight]
      | succ s ihs =>
        rw [prefixHistory_succ g traj hs]
        have hrec : exp3GammaWeight γ (prefixHistory g traj s (Nat.le_of_succ_le hs) ++
            [⟨traj ⟨s, hs⟩, g s (traj ⟨s, hs⟩)⟩]) i =
            exp3GammaWeight γ (prefixHistory g traj s (Nat.le_of_succ_le hs)) i *
              exp ((γ / K) * importanceWeightedEst
                (exp3GammaProb γ (prefixHistory g traj s (Nat.le_of_succ_le hs)))
                ⟨traj ⟨s, hs⟩, g s (traj ⟨s, hs⟩)⟩ i) := by
          simp [exp3GammaWeight, exp3GammaStep, exp3GammaProb, hclamp, K]
        rw [hrec, log_mul (exp3GammaWeight_pos γ _ i).ne' (exp_pos _).ne', log_exp,
          ihs (Nat.le_of_succ_le hs), Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        ring
    rw [hlog_w T le_rfl]
  have hsum_step := sum_le_sum (s := (univ : Finset (Fin T))) fun t _ => hstep_pot t
  simp only [sum_add_distrib, ← mul_sum] at hsum_step
  have hcomb : (γ / K) * (∑ t : Fin T,
      importanceWeightedEst (exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le))
        ⟨traj t, g t (traj t)⟩ i) -
      log K ≤
      ((γ / K) / (1 - γ)) * (∑ t : Fin T, g t (traj t)) +
        ((exp 1 - 2) * (γ / K) ^ 2 / (1 - γ)) *
          ∑ t : Fin T,
            g t (traj t) ^ 2 / exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le) (traj t) :=
    by linarith
  have hfac : 0 < K * (1 - γ) / γ := div_pos (mul_pos hK h1γ) hγ0
  have hmul := mul_le_mul_of_nonneg_left hcomb hfac.le
  have hsimp1 : (K * (1 - γ) / γ) *
      ((γ / K) * (∑ t : Fin T,
        importanceWeightedEst (exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le))
          ⟨traj t, g t (traj t)⟩ i) - log K) =
      (1 - γ) * (∑ t : Fin T,
        importanceWeightedEst (exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le))
          ⟨traj t, g t (traj t)⟩ i) - (1 - γ) * K * log K / γ := by
    field_simp
  have hsimp2 : (K * (1 - γ) / γ) *
      (((γ / K) / (1 - γ)) * (∑ t : Fin T, g t (traj t)) +
        ((exp 1 - 2) * (γ / K) ^ 2 / (1 - γ)) *
          ∑ t : Fin T,
            g t (traj t) ^ 2 / exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le) (traj t)) =
      (∑ t : Fin T, g t (traj t)) +
        (exp 1 - 2) * (γ / K) *
          ∑ t : Fin T,
            g t (traj t) ^ 2 / exp3GammaProb γ (prefixHistory g traj t.1 t.isLt.le) (traj t) := by
    field_simp
  linarith

/-- **Expected weak regret of `Exp3`** ([AuerCesaBianchiFreundSchapire2002, Theorem 3.1], locator
not re-verified against primary PDF): for `γ ∈ (0, 1]` and `[0, 1]` rewards `g`,
`G_max - 𝔼[G_Exp3] ≤ (e - 1) γ G_max + K ln K / γ`. -/
theorem exp3Gamma_rewardRegret_le [Nonempty ι] {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    {g : ℕ → ι → ℝ} (T : ℕ) (hg : ∀ s < T, ∀ a, g s a ∈ Set.Icc (0 : ℝ) 1) :
    obliviousRewardRegret (exp3GammaPolicy γ) g T ≤
      (exp 1 - 1) * γ * bestCumReward g T +
        Fintype.card ι * log (Fintype.card ι) / γ := by
  set K : ℝ := (Fintype.card ι : ℝ) with hKdef
  have hK : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  have hGmax_nonneg : 0 ≤ bestCumReward g T := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine le_trans ?_ (le_sup' (fun i => ∑ t ∈ range T, g t i) (mem_univ i₀))
    exact sum_nonneg fun t ht => (hg t (mem_range.mp ht) i₀).1
  have hlogK : 0 ≤ log K := by
    rw [hKdef]
    exact log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero)
  rcases eq_or_lt_of_le hγ1 with rfl | hγlt
  · -- Boundary `γ = 1`: `𝔼[G] ≥ 0` and `1 ≤ e - 1` (`e ≥ 5 / 2` by quadratic Taylor bound).
    unfold obliviousRewardRegret
    have hexp_ge : (5 : ℝ) / 2 ≤ exp 1 := by
      have hq := quadratic_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1)
      linarith
    have hE0 : 0 ≤ expectedTotal (exp3GammaPolicy 1) g T :=
      expectedTotal_nonneg _ fun t ht a => (hg t ht a).1
    have hKL0 : 0 ≤ K * log K / 1 := by positivity
    nlinarith
  · -- Main case `0 < γ < 1`: average the pathwise potential bound over `trajectoryPMF`.
    obtain ⟨iStar, _, hiStar⟩ :=
      exists_mem_eq_sup' univ_nonempty (fun i : ι => ∑ t ∈ range T, g t i)
    unfold obliviousRewardRegret
    have havg : (1 - γ) * (∑ t ∈ range T, g t iStar) - (1 - γ) * K * log K / γ ≤
        expectedTotal (exp3GammaPolicy γ) g T +
          (exp 1 - 2) * (γ / K) * ∑ t ∈ range T, ∑ a : ι, g t a ^ 2 := by
      rw [expectedTotal_def]
      have hsum := sum_le_sum fun traj (_ : traj ∈ (univ : Finset (Fin T → ι))) =>
        mul_le_mul_of_nonneg_left (exp3Gamma_pathwise_bound hγ0 hγlt hg traj iStar)
          (@ENNReal.toReal_nonneg (trajectoryPMF (exp3GammaPolicy γ) g T traj))
      simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib, ← sum_mul,
        Cslib.Probability.PMF.sum_toReal, one_mul] at hsum
      have hest : (∑ x : Fin T → ι, (trajectoryPMF (exp3GammaPolicy γ) g T x).toReal *
          ((1 - γ) * ∑ t : Fin T,
            importanceWeightedEst (exp3GammaProb γ (prefixHistory g x t.1 t.isLt.le))
              ⟨x t, g t (x t)⟩ iStar)) = (1 - γ) * ∑ t ∈ range T, g t iStar := by
        rw [← expected_sum_gammaEst_eq hγ0 g T iStar, mul_sum]
        exact sum_congr rfl fun x _ => by ring
      have hvar : (∑ x : Fin T → ι, (trajectoryPMF (exp3GammaPolicy γ) g T x).toReal *
          ((exp 1 - 2) * (γ / K) *
            ∑ t : Fin T,
              g t (x t) ^ 2 / exp3GammaProb γ (prefixHistory g x t.1 t.isLt.le) (x t))) =
          (exp 1 - 2) * (γ / K) * ∑ t ∈ range T, ∑ a : ι, g t a ^ 2 := by
        rw [← expected_sum_sq_div_gammaProb_eq hγ0 g T, mul_sum]
        exact sum_congr rfl fun x _ => by ring
      rw [hest, hvar] at hsum
      exact hsum
    have hsq_le_Gmax : ∑ t ∈ range T, ∑ a : ι, g t a ^ 2 ≤ K * bestCumReward g T := by
      calc ∑ t ∈ range T, ∑ a : ι, g t a ^ 2
          ≤ ∑ t ∈ range T, ∑ a : ι, g t a := sum_le_sum fun t ht => sum_le_sum fun a _ => by
            have h01 := hg t (mem_range.mp ht) a
            nlinarith [h01.1, h01.2]
        _ = ∑ a : ι, ∑ t ∈ range T, g t a := sum_comm
        _ ≤ ∑ _a : ι, bestCumReward g T := sum_le_sum fun a _ =>
            le_sup' (fun i => ∑ t ∈ range T, g t i) (mem_univ a)
        _ = K * bestCumReward g T := by simp [K]
    have he2 : 0 ≤ exp 1 - 2 := by linarith [add_one_le_exp (1 : ℝ)]
    have hvar_bound : (exp 1 - 2) * (γ / K) * ∑ t ∈ range T, ∑ a : ι, g t a ^ 2 ≤
        (exp 1 - 2) * γ * bestCumReward g T := by
      calc (exp 1 - 2) * (γ / K) * ∑ t ∈ range T, ∑ a : ι, g t a ^ 2
          ≤ (exp 1 - 2) * (γ / K) * (K * bestCumReward g T) :=
            mul_le_mul_of_nonneg_left hsq_le_Gmax (by positivity)
        _ = (exp 1 - 2) * γ * bestCumReward g T := by field_simp
    have hKL_le : (1 - γ) * K * log K / γ ≤ K * log K / γ := by
      have : (1 - γ) * (K * log K) ≤ 1 * (K * log K) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      rw [mul_assoc]
      exact div_le_div_of_nonneg_right (by linarith) hγ0.le
    have hGstar : ∑ t ∈ range T, g t iStar = bestCumReward g T := hiStar.symm
    rw [hGstar] at havg
    nlinarith

/-- Horizon-tuned exploration parameter `min 1 √(K ln K / ((e - 1) T))` of
[AuerCesaBianchiFreundSchapire2002, Corollary 3.2] (`1` in the trivial cases `K ≤ 1` or `T = 0`). -/
noncomputable def exp3GammaRate (K T : ℕ) : ℝ :=
  if K ≤ 1 ∨ T = 0 then 1 else min 1 √(K * log K / ((exp 1 - 1) * T))

/-- **Tuned expected weak regret of `Exp3`** ([AuerCesaBianchiFreundSchapire2002, Corollary 3.2],
locator not re-verified against primary PDF): for `[0, 1]` rewards `g` and any horizon `T : ℕ`,
`Exp3` with `γ = exp3GammaRate K T` satisfies
`obliviousRewardRegret ≤ 2 √((e - 1) T K ln K)`. -/
theorem exp3Gamma_rewardRegret_le_sqrt [Nonempty ι] {g : ℕ → ι → ℝ} (T : ℕ)
    (hg : ∀ s < T, ∀ a, g s a ∈ Set.Icc (0 : ℝ) 1) :
    obliviousRewardRegret (exp3GammaPolicy (exp3GammaRate (Fintype.card ι) T)) g T ≤
      2 * √((exp 1 - 1) * T * Fintype.card ι * log (Fintype.card ι)) := by
  set K := Fintype.card ι with hKdef
  have he1 : 1 < exp 1 - 1 := by
    have hq := quadratic_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1)
    linarith
  have he0 : 0 < exp 1 - 1 := by linarith
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [obliviousRewardRegret, bestCumReward]
  by_cases hK : K ≤ 1
  · have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hK
    refine le_trans ?_ (mul_nonneg zero_le_two (sqrt_nonneg _))
    unfold obliviousRewardRegret bestCumReward
    rw [sub_nonpos, Finset.sup'_le_iff]
    intro i _
    rw [expectedTotal_eq_sum_of_subsingleton _ g T i]
  · have hK2 : 2 ≤ K := by omega
    have hKL : 0 < (K : ℝ) * log K := mul_pos (by positivity) (log_pos (by exact_mod_cast hK2))
    have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
    have hGmax_le_T : bestCumReward g T ≤ T := by
      unfold bestCumReward
      rw [Finset.sup'_le_iff]
      intro i _
      calc ∑ t ∈ range T, g t i
          ≤ ∑ _t ∈ range T, (1 : ℝ) := sum_le_sum fun t ht => (hg t (mem_range.mp ht) i).2
        _ = T := by simp
    have hrate : exp3GammaRate K T = min 1 √((K : ℝ) * log K / ((exp 1 - 1) * T)) := by
      have hnot : ¬ (K ≤ 1 ∨ T = 0) := by omega
      simp [exp3GammaRate, hnot]
    rw [hrate]
    set γ₀ := √((K : ℝ) * log K / ((exp 1 - 1) * T)) with hγ₀def
    have hγ₀_pos : 0 < γ₀ := sqrt_pos.mpr (div_pos hKL (mul_pos he0 hTr))
    by_cases hle1 : γ₀ ≤ 1
    · rw [min_eq_right hle1]
      refine (exp3Gamma_rewardRegret_le hγ₀_pos hle1 T hg).trans ?_
      rw [← hKdef]
      have hGterm : (exp 1 - 1) * γ₀ * bestCumReward g T ≤ (exp 1 - 1) * γ₀ * T :=
        mul_le_mul_of_nonneg_left hGmax_le_T (by positivity)
      have hbal : (exp 1 - 1) * γ₀ * T + K * log K / γ₀ =
          2 * √((exp 1 - 1) * T * K * log K) := by
        have hsq : γ₀ * γ₀ = (K : ℝ) * log K / ((exp 1 - 1) * T) :=
          mul_self_sqrt (div_nonneg hKL.le (by positivity))
        have hprod : γ₀ * √((exp 1 - 1) * T * K * log K) = K * log K := by
          rw [hγ₀def, ← sqrt_mul (by positivity)]
          have h1 : (K : ℝ) * log K / ((exp 1 - 1) * T) * ((exp 1 - 1) * T * K * log K) =
              ((K : ℝ) * log K) ^ 2 := by field_simp
          rw [h1, sqrt_sq hKL.le]
        apply mul_left_cancel₀ hγ₀_pos.ne'
        calc γ₀ * ((exp 1 - 1) * γ₀ * T + K * log K / γ₀)
            = (exp 1 - 1) * T * (γ₀ * γ₀) + K * log K := by field_simp
          _ = 2 * (K * log K) := by rw [hsq]; field_simp; ring
          _ = γ₀ * (2 * √((exp 1 - 1) * T * K * log K)) := by linarith [hprod]
      linarith
    · push Not at hle1
      rw [min_eq_left hle1.le]
      -- When `γ₀ > 1`, `(e - 1) T < K ln K`, while regret is trivially at most `bestCumReward ≤ T`.
      have h1_lt_div : 1 < (K : ℝ) * log K / ((exp 1 - 1) * T) := by
        have hsq := mul_lt_mul_of_pos_left hle1 hγ₀_pos
        have hself : γ₀ * γ₀ = (K : ℝ) * log K / ((exp 1 - 1) * T) :=
          mul_self_sqrt (div_nonneg hKL.le (by positivity))
        linarith
      have heT_lt : (exp 1 - 1) * T < K * log K := by
        linarith [(lt_div_iff₀ (mul_pos he0 hTr)).mp h1_lt_div]
      have hreg_le_T : obliviousRewardRegret (exp3GammaPolicy 1) g T ≤ T := by
        unfold obliviousRewardRegret
        have hE0 : 0 ≤ expectedTotal (exp3GammaPolicy 1) g T :=
          expectedTotal_nonneg _ fun t ht a => (hg t ht a).1
        linarith
      refine hreg_le_T.trans ?_
      have hT_sq : (T : ℝ) ^ 2 ≤ (2 * √((exp 1 - 1) * T * K * log K)) ^ 2 := by
        rw [mul_pow, sq_sqrt (by positivity), show (2 : ℝ) ^ 2 = 4 by norm_num]
        have h1 : (T : ℝ) ≤ (exp 1 - 1) * T := le_mul_of_one_le_left hTr.le he1.le
        have h1sq : (T : ℝ) ^ 2 ≤ ((exp 1 - 1) * T) ^ 2 := pow_le_pow_left₀ hTr.le h1 2
        have h2 : ((exp 1 - 1) * T) ^ 2 ≤ (exp 1 - 1) * T * K * log K := by
          calc ((exp 1 - 1) * T) ^ 2
              = ((exp 1 - 1) * T) * ((exp 1 - 1) * T) := sq _
            _ ≤ ((exp 1 - 1) * T) * (K * log K) :=
                mul_le_mul_of_nonneg_left heT_lt.le (mul_pos he0 hTr).le
            _ = (exp 1 - 1) * T * K * log K := by ring
        have hpos_prod : 0 ≤ (exp 1 - 1) * T * K * log K := by positivity
        linarith
      exact le_of_sq_le_sq hT_sq (by positivity)

end RewardEXP3

end Cslib.MachineLearning.OnlineLearning.Bandits
