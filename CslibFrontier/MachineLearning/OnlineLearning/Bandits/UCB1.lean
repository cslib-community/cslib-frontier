/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.Bandits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The UCB1 algorithm for stochastic multi-armed bandits

The **UCB1** policy of Auer, Cesa-Bianchi and Fischer ([AuerCesaBianchiFischer2002, §2.1,
Figure 1 and Theorem 1], locator not re-verified against primary PDF) is a deterministic,
horizon-free index policy for `[0, 1]`-bounded stochastic `K`-armed bandits (`StochasticBandit ι`):

* **Initialization:** while any arm has not yet been pulled (`pullCount hist i = 0`), pull the
  least unpulled arm in the arm order `[LinearOrder ι]`. After `K = Fintype.card ι` plays every arm
  has been pulled once (`one_le_pullCount_ucb1`).
* **Upper-confidence loop:** once every arm has been pulled at least once (`t = hist.length ≥ K`),
  pull an arm maximizing the upper confidence index (`ucb1Index`) `x̄_i + √(2 ln t / n_i)`,
  breaking ties deterministically toward the least arm in `[LinearOrder ι]` (`ucb1Policy`).

Because `ucb1Policy` is a `DeterministicPolicy ι`, it accesses only the observed `(arm, value)`
pairs of previous pulls, and its deterministic tie-breaking makes it Borel-measurable
(`ucb1Policy_isMeasurable`).

## Proof overview

1. **Hoeffding sub-Gaussian tails on the reward stack**: under `B.sampleMeasure T`, the first `m`
   entries of arm `i`'s reward stack are independent `[0, 1]` a.e. random variables with mean
   `B.mean i`. Mathlib's `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` and
   `HasSubgaussianMGF.sum_of_iIndepFun` yield one-sided sub-Gaussian tails `≤ exp (-2 m c²)`; at
   the UCB radius `c = √(2 ln t / m)` (`t ≥ 2`), each tail is at most `1 / t ^ 4`.
2. **Expected pulls of suboptimal arms** (`ucb1_expectedPulls_le_add_two`): for any arm `i` with
   `Δ_i = B.gap i > 0`, partitioning the pulls of `i` before and after `ℓ = ⌈8 ln T / Δ_i²⌉₊` leaves
   only rounds `t ∈ [K, T)` where either the optimal arm `i*` under-performs by `√(2 ln t / s)` for
   some `s ∈ [1, t]` or arm `i` over-performs by `√(2 ln t / s_i)` for some `s_i ∈ [ℓ, t]`. Because
   the two events decouple across `s` and `s_i`, the union bound at round `t ≥ K ≥ 2` costs at most
   `2 t * t⁻⁴ = 2 / t³ ≤ 1 / (t - 1) - 1 / t`, which telescopes to at most `1`. Together with
   `ℓ ≤ 8 ln T / Δ_i² + 1`, this gives the sharp finite-time pull bound
   `B.expectedPulls ucb1Policy T i ≤ 8 * log T / (B.gap i) ^ 2 + 2` (sharpening `1 + π² / 3`
   since `2 < 4 < 1 + π² / 3`).
3. **Instance-dependent logarithmic regret and `O(√(K T ln T))` minimax regret**:
   - Combining `ucb1_expectedPulls_le_add_two` with Wald's identity
     (`B.stochasticRegret_eq_pseudoRegret`) proves both the sharpened bound with constant `2`
     (`ucb1_stochasticRegret_le_sharp`) and the exact display of
     [AuerCesaBianchiFischer2002, Theorem 1] (`ucb1_stochasticRegret_le`):
     `B.stochasticRegret ucb1Policy T ≤ ∑_{Δ_i > 0} (8 ln T / Δ_i) + (1 + π² / 3) ∑_i Δ_i`.
   - Applying Cauchy–Schwarz across arms
     (`(Δ_i 𝔼[N_i])² = 𝔼[N_i] (Δ_i² 𝔼[N_i]) ≤ 𝔼[N_i] (8 ln T + 2)`) yields problem-independent
     minimax bounds `√(K T (8 ln T + 2))` for all `T ≥ 1` (`ucb1_stochasticRegret_le_sqrt_add`)
     and `2 √(3 K T ln T)` for all `T ≥ 2` (`ucb1_stochasticRegret_le_sqrt`, compare
     [BubeckCesaBianchi2012, Theorem 2.1], locator not re-verified against primary PDF).

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Bandits.ucb1Index`: upper confidence index
  `empiricalMean hist i + √(2 * log hist.length / pullCount hist i)`.
* `Cslib.MachineLearning.OnlineLearning.Bandits.ucb1Policy`: deterministic `UCB1` policy.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Bandits.ucb1Policy_isMeasurable`: Borel measurability of
  `ucb1Policy`.
* `Cslib.MachineLearning.OnlineLearning.Bandits.one_le_pullCount_ucb1`: after `K` rounds, every arm
  has been pulled at least once.
* `Cslib.MachineLearning.OnlineLearning.Bandits.ucb1_expectedPulls_le_add_two`: suboptimal arm pull
  bound `𝔼[N_i(T)] ≤ 8 ln T / Δ_i² + 2`.
* `Cslib.MachineLearning.OnlineLearning.Bandits.ucb1_stochasticRegret_le`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.ucb1_stochasticRegret_le_sharp`: logarithmic
  instance-dependent expected regret ([AuerCesaBianchiFischer2002, Theorem 1], locator not
  re-verified against primary PDF).
* `Cslib.MachineLearning.OnlineLearning.Bandits.ucb1_stochasticRegret_le_sqrt_add`,
  `Cslib.MachineLearning.OnlineLearning.Bandits.ucb1_stochasticRegret_le_sqrt`: minimax
  `O(√(K T ln T))` expected regret bounds.

## References

* [P. Auer, N. Cesa-Bianchi, P. Fischer, *Finite-Time Analysis of the Multiarmed Bandit
  Problem*][AuerCesaBianchiFischer2002]
* [S. Bubeck, N. Cesa-Bianchi, *Regret Analysis of Stochastic and Nonstochastic Multi-Armed Bandit
  Problems*][BubeckCesaBianchi2012]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Bandits

open Finset MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

section Policy

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Upper confidence index `x̄_i + √(2 ln t / n_i)` of arm `i` after transcript `hist`
([AuerCesaBianchiFischer2002, Figure 1], locator not re-verified against primary PDF). -/
noncomputable def ucb1Index (hist : List (BanditStep ι)) (i : ι) : ℝ :=
  empiricalMean hist i + √(2 * log hist.length / pullCount hist i)

omit [Fintype ι] in
theorem ucb1Index_def (hist : List (BanditStep ι)) (i : ι) :
    ucb1Index hist i = empiricalMean hist i + √(2 * log hist.length / pullCount hist i) := by
  rw [ucb1Index]

/-- Arms not yet pulled in `hist`. -/
def unpulledArms (hist : List (BanditStep ι)) : Finset ι :=
  univ.filter fun i => pullCount hist i = 0

@[simp]
theorem mem_unpulledArms (hist : List (BanditStep ι)) (i : ι) :
    i ∈ unpulledArms hist ↔ pullCount hist i = 0 := by
  simp [unpulledArms]

/-- Deterministic arm selection of `UCB1`: pull the least unpulled arm if any exists; otherwise pull
the least arm maximizing `ucb1Index hist`. -/
private noncomputable def ucb1Choose [Nonempty ι] (hist : List (BanditStep ι)) : ι :=
  if h : (unpulledArms hist).Nonempty then
    (unpulledArms hist).min' h
  else
    let M := univ.filter fun i : ι => ∀ j : ι, ucb1Index hist j ≤ ucb1Index hist i
    have hM : M.Nonempty := by
      obtain ⟨i, _, hi⟩ := exists_max_image univ (ucb1Index hist) univ_nonempty
      exact ⟨i, mem_filter.mpr ⟨mem_univ i, fun j => hi j (mem_univ j)⟩⟩
    M.min' hM

/-- The deterministic `UCB1` bandit policy ([AuerCesaBianchiFischer2002, §2.1, Figure 1]). -/
noncomputable def ucb1Policy [Nonempty ι] : DeterministicPolicy ι where
  choose := ucb1Choose

private theorem ucb1Policy_choose [Nonempty ι] (hist : List (BanditStep ι)) :
    ucb1Policy.choose hist = ucb1Choose hist := by
  rw [ucb1Policy]

/-- While any arm is unpulled, `UCB1` selects the least unpulled arm. -/
theorem ucb1Policy_choose_of_nonempty [Nonempty ι] {hist : List (BanditStep ι)}
    (h : (unpulledArms hist).Nonempty) :
    ucb1Policy.choose hist = (unpulledArms hist).min' h := by
  simp only [ucb1Policy_choose, ucb1Choose, h, ↓reduceDIte]

/-- When all arms have been pulled (`unpulledArms hist = ∅`), the arm chosen by `UCB1` maximizes
`ucb1Index hist` across all arms. -/
theorem ucb1Index_le_choose_of_unpulled_empty [Nonempty ι] {hist : List (BanditStep ι)}
    (h : ¬ (unpulledArms hist).Nonempty) (j : ι) :
    ucb1Index hist j ≤ ucb1Index hist (ucb1Policy.choose hist) := by
  simp only [ucb1Policy_choose, ucb1Choose, h, ↓reduceDIte]
  exact (mem_filter.mp
    (min'_mem (univ.filter fun m : ι => ∀ k : ι, ucb1Index hist k ≤ ucb1Index hist m) _)).2 j

/-- Deterministic tie-breaking of `UCB1`: when all arms have been pulled,
`ucb1Policy.choose hist ≤ i` for every arm `i` maximizing `ucb1Index hist`. -/
theorem ucb1Policy_choose_le_of_unpulled_empty [Nonempty ι] {hist : List (BanditStep ι)}
    (h : ¬ (unpulledArms hist).Nonempty) {i : ι}
    (hi : ∀ j : ι, ucb1Index hist j ≤ ucb1Index hist i) :
    ucb1Policy.choose hist ≤ i := by
  simp only [ucb1Policy_choose, ucb1Choose, h, ↓reduceDIte]
  exact min'_le _ i (mem_filter.mpr ⟨mem_univ i, hi⟩)

/-- `ucb1Policy` is Borel-measurable: for fixed past arms `arms : Fin t → ι`, pull counts and
`unpulledArms` do not depend on the observed reward values `vals : Fin t → ℝ`, and the index
maximizer fiber is a finite Boolean combination of linear half-spaces. -/
theorem ucb1Policy_isMeasurable [Nonempty ι] : (ucb1Policy (ι := ι)).IsMeasurable := by
  rw [DeterministicPolicy.isMeasurable_def]
  intro t arms i
  let H (vals : Fin t → ℝ) : List (BanditStep ι) := List.ofFn fun r => ⟨arms r, vals r⟩
  have hpull_const : ∀ (vals : Fin t → ℝ) (j : ι),
      pullCount (H vals) j = (univ.filter fun r : Fin t => arms r = j).card := fun _ j =>
    pullCount_ofFn _ j
  have hunpulled_const : ∀ vals : Fin t → ℝ,
      unpulledArms (H vals) = unpulledArms (H 0) := fun vals => by
    ext j; simp [unpulledArms, hpull_const]
  by_cases hun : (unpulledArms (H 0)).Nonempty
  · have hconst : ∀ vals : Fin t → ℝ,
        ucb1Policy.choose (H vals) = (unpulledArms (H 0)).min' hun := fun vals => by
      have hun' : (unpulledArms (H vals)).Nonempty := by rwa [hunpulled_const]
      simp only [ucb1Policy_choose, ucb1Choose, hun', ↓reduceDIte]
      simp_rw [hunpulled_const vals]
    by_cases hi : (unpulledArms (H 0)).min' hun = i
    · rw [show {vals : Fin t → ℝ | ucb1Policy.choose (H vals) = i} = Set.univ by
        ext vals; simp [hconst vals, hi]]
      exact MeasurableSet.univ
    · rw [show {vals : Fin t → ℝ | ucb1Policy.choose (H vals) = i} = ∅ by
        ext vals; simp [hconst vals, hi]]
      exact MeasurableSet.empty
  · have hmeas_idx : ∀ j : ι, Measurable fun vals : Fin t → ℝ => ucb1Index (H vals) j := fun j => by
      have hmeas_sum : Measurable fun vals : Fin t → ℝ => feedbackSum (H vals) j := by
        rw [show (fun vals : Fin t → ℝ => feedbackSum (H vals) j) =
            fun vals => ∑ r : Fin t, if arms r = j then vals r else 0 from
          funext fun _ => feedbackSum_ofFn _ j]
        refine Finset.measurable_sum univ fun r _ => ?_
        by_cases hr : arms r = j <;> simp only [hr, ↓reduceIte]
        · exact measurable_pi_apply r
        · exact measurable_const
      rw [show (fun vals : Fin t → ℝ => ucb1Index (H vals) j) = fun vals =>
          feedbackSum (H vals) j / ((univ.filter fun r : Fin t => arms r = j).card : ℝ) +
            √(2 * log t / ((univ.filter fun r : Fin t => arms r = j).card : ℝ)) from
        funext fun _ => by simp [ucb1Index_def, empiricalMean_def, hpull_const, H]]
      exact (hmeas_sum.div_const _).add measurable_const
    have heq_set : {vals : Fin t → ℝ | ucb1Policy.choose (H vals) = i} =
        (⋂ j : ι, {vals | ucb1Index (H vals) j ≤ ucb1Index (H vals) i}) ∩
          ⋂ k ∈ univ.filter (· < i),
            (⋂ j : ι, {vals | ucb1Index (H vals) j ≤ ucb1Index (H vals) k})ᶜ := by
      ext vals
      have hun' : ¬ (unpulledArms (H vals)).Nonempty := by rwa [hunpulled_const]
      simp only [ucb1Policy_choose, ucb1Choose, hun', ↓reduceDIte, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_iInter, mem_filter, mem_univ, true_and, Set.mem_compl_iff,
        not_forall]
      set M := univ.filter fun m : ι => ∀ j : ι, ucb1Index (H vals) j ≤ ucb1Index (H vals) m
      have hM : M.Nonempty :=
        let ⟨m, _, hm⟩ := exists_max_image univ (ucb1Index (H vals)) univ_nonempty
        ⟨m, mem_filter.mpr ⟨mem_univ m, fun j => hm j (mem_univ j)⟩⟩
      constructor
      · intro hmin
        refine ⟨(mem_filter.mp (hmin ▸ min'_mem M hM)).2, fun k hki => by_contra fun hall =>
          not_le_of_gt hki (hmin ▸ min'_le M k (mem_filter.mpr ⟨mem_univ k, by simpa using hall⟩))⟩
      · rintro ⟨hi_max, hlt_not⟩
        refine le_antisymm (min'_le M i (mem_filter.mpr ⟨mem_univ i, hi_max⟩))
          (by_contra fun hlt => ?_)
        obtain ⟨j, hj⟩ := hlt_not (M.min' hM) (not_le.mp hlt)
        exact hj ((mem_filter.mp (min'_mem M hM)).2 j)
    rw [heq_set]
    exact (MeasurableSet.iInter fun j => measurableSet_le (hmeas_idx j) (hmeas_idx i)).inter <|
      Set.Finite.measurableSet_biInter (Finset.finite_toSet _) fun k _ =>
        (MeasurableSet.iInter fun j => measurableSet_le (hmeas_idx j) (hmeas_idx k)).compl

/-- Initialization invariant: at round `r`, either every arm has been pulled at least once or at
least `r` distinct arms have been pulled. -/
private theorem card_pulled_ge_min [Nonempty ι] {T : ℕ} (X : ι × Fin T → ℝ) (r : ℕ) :
    min r (Fintype.card ι) ≤
      (univ.filter fun i : ι => 0 < pullCount (runStochastic ucb1Policy X r) i).card := by
  induction r with
  | zero => simp
  | succ r ih =>
    set hist := runStochastic ucb1Policy X r
    set S := univ.filter fun i : ι => 0 < pullCount hist i
    set S' := univ.filter fun i : ι => 0 < pullCount (runStochastic ucb1Policy X (r + 1)) i
    have hsub : S ⊆ S' := fun j hj => by
      simp only [S, S', mem_filter, mem_univ, true_and] at hj ⊢
      exact hj.trans_le (pullCount_runStochastic_mono ucb1Policy X (Nat.le_succ r) j)
    by_cases hun : (unpulledArms hist).Nonempty
    · set a := ucb1Choose hist
      have ha_zero : pullCount hist a = 0 := by
        have ha_mem : a ∈ unpulledArms hist := by
          simp only [a, ucb1Choose, hun, ↓reduceDIte]; exact min'_mem _ hun
        exact (mem_filter.mp ha_mem).2
      have ha_not : a ∉ S := by simp [S, ha_zero]
      have ha_in : a ∈ S' := by
        simp only [S', mem_filter, mem_univ, true_and, runStochastic_succ, pullCount_append,
          pullCount_singleton, ucb1Policy_choose, ← show hist = runStochastic ucb1Policy X r from
            rfl, ← show a = ucb1Choose hist from rfl, ↓reduceIte]
        omega
      have hcard := card_le_card (insert_subset ha_in hsub)
      rw [card_insert_of_notMem ha_not] at hcard
      have hleK : S'.card ≤ Fintype.card ι := card_le_univ S'
      omega
    · have hall : S = univ := eq_univ_of_forall fun j => mem_filter.mpr ⟨mem_univ j, by
        by_contra h0; exact hun ⟨j, mem_filter.mpr ⟨mem_univ j, Nat.eq_zero_of_le_zero (by omega)⟩⟩⟩
      have hcard : Fintype.card ι ≤ S'.card :=
        (by simp [hall] : S.card = Fintype.card ι) ▸ card_le_card hsub
      omega

/-- After `K = Fintype.card ι` rounds, `UCB1` has pulled every arm at least once. -/
theorem one_le_pullCount_ucb1 [Nonempty ι] {T t : ℕ} (X : ι × Fin T → ℝ)
    (ht : Fintype.card ι ≤ t) (i : ι) :
    1 ≤ pullCount (runStochastic ucb1Policy X t) i := by
  have hcard := card_pulled_ge_min X t
  rw [min_eq_right ht] at hcard
  have heq : (univ.filter fun j : ι => 0 < pullCount (runStochastic ucb1Policy X t) j) = univ :=
    eq_of_subset_of_card_le (subset_univ _) hcard
  have hi : i ∈ univ.filter (fun j : ι => 0 < pullCount (runStochastic ucb1Policy X t) j) :=
    heq.symm ▸ mem_univ i
  exact Nat.succ_le_of_lt (mem_filter.mp hi).2

/-- In any round `r < Fintype.card ι` (and overall whenever an arm has `pullCount = 0`), `UCB1`
only pulls unpulled arms; hence if `pullCount hist i ≥ 1` and `UCB1` pulls `i` at round `t`, we must
have `Fintype.card ι ≤ t`. -/
private theorem card_le_of_choose_of_pos [Nonempty ι] {T t : ℕ} (X : ι × Fin T → ℝ) {i : ι}
    (hpos : 1 ≤ pullCount (runStochastic ucb1Policy X t) i)
    (hchoose : ucb1Policy.choose (runStochastic ucb1Policy X t) = i) :
    Fintype.card ι ≤ t := by
  by_contra hlt
  set hist := runStochastic ucb1Policy X t
  have hun : (unpulledArms hist).Nonempty := by_contra fun hemp => by
    have hall : ∀ j : ι, 1 ≤ pullCount hist j := fun j => by_contra fun hj0 =>
      hemp ⟨j, mem_filter.mpr ⟨mem_univ j, Nat.eq_zero_of_le_zero (by omega)⟩⟩
    have hsum : Fintype.card ι ≤ t := by
      calc Fintype.card ι = ∑ _j : ι, 1 := by simp
        _ ≤ ∑ j : ι, pullCount hist j := sum_le_sum fun j _ => hall j
        _ = t := (sum_pullCount_eq_length hist).trans (length_runStochastic ucb1Policy X t)
    omega
  have hmem : i ∈ unpulledArms hist := by
    simp only [← hchoose, ucb1Policy_choose, ucb1Choose, hun, ↓reduceDIte]
    exact min'_mem _ hun
  have h0 : pullCount hist i = 0 := (mem_filter.mp hmem).2
  omega

end Policy

/-! ### Hoeffding concentration on the reward stack and suboptimal pull bound -/

section Regret

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Prefix empirical average `(∑_{r < m} X (i, r)) / m` on arm `i`'s reward stack (`m ≤ T`). -/
private noncomputable def stackMean {T : ℕ} (X : ι × Fin T → ℝ) (i : ι) (m : ℕ) (hmT : m ≤ T) :
    ℝ :=
  (∑ r : Fin m, X (i, ⟨r.1, r.isLt.trans_le hmT⟩)) / m

omit [Fintype ι] in
/-- When `t ≤ T`, `empiricalMean (runStochastic pol X t) i` equals `stackMean` at `pullCount`. -/
private theorem empiricalMean_runStochastic_eq_stackMean (pol : DeterministicPolicy ι)
    {T t : ℕ} (ht : t ≤ T) (X : ι × Fin T → ℝ) (i : ι) :
    empiricalMean (runStochastic pol X t) i =
      stackMean X i (pullCount (runStochastic pol X t) i)
        ((pullCount_le_length _ i).trans (ht.trans_eq' (length_runStochastic pol X t).symm)) := by
  unfold stackMean
  rw [empiricalMean_def, feedbackSum_runStochastic_eq pol X ht i]
  congr 1
  set m := pullCount (runStochastic pol X t) i
  have hmT : m ≤ T :=
    (pullCount_le_length _ i).trans (ht.trans_eq' (length_runStochastic pol X t).symm)
  rw [← sum_filter]
  exact sum_bij (fun s hs => ⟨s.1, (mem_filter.mp hs).2⟩) (fun _ _ => mem_univ _)
    (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
    (fun r _ => ⟨⟨r.1, r.isLt.trans_le hmT⟩, mem_filter.mpr ⟨mem_univ _, r.isLt⟩, rfl⟩)
    (fun _ _ => rfl)

omit [LinearOrder ι] in
/-- Sub-Gaussian MGF of `∑_{r < m} (X (i, r) - μ_i)` and `∑_{r < m} (μ_i - X (i, r))` under
`B.sampleMeasure T` (`Variance proxy = m / 4`). -/
private theorem hasSubgaussianMGF_stack_sum_sub (B : StochasticBandit ι) {T : ℕ} (i : ι)
    {m : ℕ} (hmT : m ≤ T) :
    HasSubgaussianMGF
        (fun X : ι × Fin T → ℝ =>
          ∑ r : Fin m, (X (i, ⟨r.1, r.isLt.trans_le hmT⟩) - B.mean i))
        (m * (‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (B.sampleMeasure T) ∧
      HasSubgaussianMGF
        (fun X : ι × Fin T → ℝ =>
          ∑ r : Fin m, (B.mean i - X (i, ⟨r.1, r.isLt.trans_le hmT⟩)))
        (m * (‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (B.sampleMeasure T) := by
  rw [B.sampleMeasure_def]
  let emb (r : Fin m) : ι × Fin T := (i, ⟨r.1, r.isLt.trans_le hmT⟩)
  have hemb_inj : Function.Injective emb := fun a b h =>
    Fin.ext (Fin.mk.inj (Prod.mk.inj h).2)
  have hcoord_pos : ∀ r : Fin m,
      HasSubgaussianMGF (fun X : ι × Fin T → ℝ => X (emb r) - B.mean i)
        ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (Measure.pi fun p => B.law p.1) := by
    intro r
    have hmp := measurePreserving_eval (fun p : ι × Fin T => B.law p.1) (emb r)
    have hmean : ∫ X, X (emb r) ∂(Measure.pi fun p => B.law p.1) = B.mean i := by
      have hid := integral_map (μ := Measure.pi fun p : ι × Fin T => B.law p.1)
        (measurable_pi_apply (emb r)).aemeasurable (f := id) aestronglyMeasurable_id
      rw [B.mean_def, ← hmp.map_eq]
      exact hid.symm
    have hae : ∀ᵐ X ∂(Measure.pi fun p => B.law p.1), X (emb r) ∈ Set.Icc (0 : ℝ) 1 :=
      hmp.quasiMeasurePreserving.ae (B.mem_unitInterval i)
    have h := hasSubgaussianMGF_of_mem_Icc (μ := Measure.pi fun p => B.law p.1)
      (measurable_pi_apply (emb r)).aemeasurable hae
    simpa [hmean] using h
  have hind_pos : iIndepFun (fun (r : Fin m) (X : ι × Fin T → ℝ) => X (emb r) - B.mean i)
      (Measure.pi fun p => B.law p.1) := by
    have hpi : iIndepFun (fun (p : ι × Fin T) (X : ι × Fin T → ℝ) => X p - B.mean p.1)
        (Measure.pi fun p => B.law p.1) :=
      iIndepFun_pi (μ := fun p : ι × Fin T => B.law p.1) (X := fun p x => x - B.mean p.1)
        fun _ => (measurable_id.sub measurable_const).aemeasurable
    exact hpi.precomp hemb_inj
  have hsum_pos := HasSubgaussianMGF.sum_of_iIndepFun hind_pos (s := univ) fun r _ => hcoord_pos r
  have hsum_neg := hsum_pos.neg
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum_pos hsum_neg
  refine ⟨hsum_pos, hsum_neg.congr (ae_of_all _ fun X => ?_)⟩
  simp [Pi.neg_apply, emb]

omit [LinearOrder ι] in
/-- Upper and lower Hoeffding tail bounds at the UCB radius `√(2 ln t / m)` (`t ≥ 2`, `1 ≤ m ≤ T`):
both probabilities are at most `1 / t ^ 4`. -/
private theorem measureReal_stackMean_deviation_le (B : StochasticBandit ι) {T t m : ℕ}
    (ht2 : 2 ≤ t) (hm : 0 < m) (hmT : m ≤ T) (i : ι) :
    (B.sampleMeasure T).real
        {X | B.mean i + √(2 * log t / m) ≤ stackMean X i m hmT} ≤ 1 / (t : ℝ) ^ 4 ∧
      (B.sampleMeasure T).real
        {X | stackMean X i m hmT ≤ B.mean i - √(2 * log t / m)} ≤ 1 / (t : ℝ) ^ 4 := by
  obtain ⟨hpos, hneg⟩ := hasSubgaussianMGF_stack_sum_sub B i hmT
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have htR : (0 : ℝ) < t := by positivity
  have hlog : 0 < log t := log_pos (by exact_mod_cast ht2)
  set c := √(2 * log t / m)
  have hc0 : 0 ≤ m * c := by positivity
  have hexp : exp (-(m * c) ^ 2 / (2 * ((m * (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) =
      1 / (t : ℝ) ^ 4 := by
    have harg : -(m * c) ^ 2 / (2 * ((m * (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)) =
        -(4 * log t) := by
      push_cast
      rw [sub_zero, norm_one, mul_pow, sq_sqrt (by positivity)]
      field_simp; ring
    rw [harg, exp_neg, show (4 : ℝ) * log t = (4 : ℕ) * log t by norm_num, exp_nat_mul,
      exp_log htR, one_div]
  refine ⟨le_trans (measureReal_mono fun X hX => ?_) ((hpos.measure_ge_le hc0).trans_eq hexp),
    le_trans (measureReal_mono fun X hX => ?_) ((hneg.measure_ge_le hc0).trans_eq hexp)⟩
  · simp only [Set.mem_ofPred_eq, stackMean, le_div_iff₀ hmR, sum_sub_distrib, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul] at hX ⊢
    linarith
  · simp only [Set.mem_ofPred_eq, stackMean, div_le_iff₀ hmR, sum_sub_distrib, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul] at hX ⊢
    linarith

/-- Pathwise pull-count decomposition: for any positive threshold `ℓ ≥ 1`, arm `i` is pulled at most
`ℓ` times plus the number of post-initialization rounds `t ∈ [K, T)` at which `UCB1` selects `i`
while `ℓ ≤ pullCount hist_t i`. -/
private theorem pullCount_ucb1_le_add_sum [Nonempty ι] {T ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (X : ι × Fin T → ℝ) (i : ι) :
    pullCount (runStochastic ucb1Policy X T) i ≤
      ℓ + ∑ t ∈ Ico (Fintype.card ι) T,
        if ucb1Policy.choose (runStochastic ucb1Policy X t) = i ∧
            ℓ ≤ pullCount (runStochastic ucb1Policy X t) i
          then 1 else 0 := by
  have hcount : ∀ n, pullCount (runStochastic ucb1Policy X n) i =
      ((range n).filter fun t => ucb1Policy.choose (runStochastic ucb1Policy X t) = i).card := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [runStochastic_succ, pullCount_append, pullCount_singleton, range_add_one, filter_insert,
        ih]
      split_ifs <;> simp [card_insert_of_notMem]
  rw [hcount T]
  set S := (range T).filter fun t => ucb1Policy.choose (runStochastic ucb1Policy X t) = i
  set S₁ := S.filter fun t => pullCount (runStochastic ucb1Policy X t) i < ℓ
  set S₂ := S.filter fun t => ℓ ≤ pullCount (runStochastic ucb1Policy X t) i
  have hpart : S.card = S₁.card + S₂.card := by
    simpa only [not_lt] using (card_filter_add_card_filter_not (s := S)
      (p := fun t => pullCount (runStochastic ucb1Policy X t) i < ℓ)).symm
  have hcard₁ : S₁.card ≤ ℓ := by
    have hlt_ne : ∀ {a b}, a ∈ S → a < b →
        pullCount (runStochastic ucb1Policy X a) i <
          pullCount (runStochastic ucb1Policy X b) i := by
      intro a b ha hlt
      have hstep : pullCount (runStochastic ucb1Policy X a) i + 1 ≤
          pullCount (runStochastic ucb1Policy X (a + 1)) i := by
        simp only [runStochastic_succ, pullCount_append, pullCount_singleton, (mem_filter.mp ha).2,
          ↓reduceIte, le_rfl]
      exact (Nat.lt_of_lt_of_le (by omega) hstep).trans_le
        (pullCount_runStochastic_mono ucb1Policy X (by omega) i)
    have hinj : Set.InjOn (fun t => pullCount (runStochastic ucb1Policy X t) i) S₁ := by
      intro t₁ ht₁ t₂ ht₂ heq
      rcases lt_trichotomy t₁ t₂ with h | rfl | h
      · exact absurd heq (hlt_ne (mem_filter.mp ht₁).1 h).ne
      · rfl
      · exact absurd heq.symm (hlt_ne (mem_filter.mp ht₂).1 h).ne
    calc S₁.card = (S₁.image fun t => pullCount (runStochastic ucb1Policy X t) i).card :=
          (card_image_of_injOn hinj).symm
      _ ≤ (range ℓ).card := card_le_card fun u hu => by
          obtain ⟨t, ht, rfl⟩ := mem_image.mp hu; exact mem_range.mpr (mem_filter.mp ht).2
      _ = ℓ := card_range ℓ
  have hcard₂ : S₂.card ≤ ∑ t ∈ Ico (Fintype.card ι) T,
      if ucb1Policy.choose (runStochastic ucb1Policy X t) = i ∧
          ℓ ≤ pullCount (runStochastic ucb1Policy X t) i
        then 1 else 0 := by
    rw [← card_filter]
    refine card_le_card fun t ht => ?_
    obtain ⟨htS, hge⟩ := mem_filter.mp ht
    obtain ⟨htT, hch⟩ := mem_filter.mp htS
    exact mem_filter.mpr
      ⟨mem_Ico.mpr ⟨card_le_of_choose_of_pos X (hℓ.trans hge) hch, mem_range.mp htT⟩, hch, hge⟩
  omega

/-- Elementary telescoping bound `∑_{t ∈ Ico K T} 2 / t³ ≤ 1` for `2 ≤ K`. -/
private theorem sum_Ico_two_div_cube_le_one {K T : ℕ} (hK : 2 ≤ K) :
    ∑ t ∈ Ico K T, (2 / (t : ℝ) ^ 3) ≤ 1 := by
  by_cases hKT : K < T
  · have hle : ∑ t ∈ Ico K T, (2 / (t : ℝ) ^ 3) ≤
        ∑ t ∈ Ico 2 T, (1 / ((t : ℝ) - 1) - 1 / (t : ℝ)) := by
      refine (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_left hK)
        fun _ _ _ => by positivity).trans (sum_le_sum fun t ht => ?_)
      have htR : (2 : ℝ) ≤ t := by exact_mod_cast (mem_Ico.mp ht).1
      rw [div_sub_div 1 1 (by linarith) (by linarith),
        div_le_div_iff₀ (by positivity) (mul_pos (by linarith) (by linarith))]
      nlinarith [sq_nonneg ((t : ℝ) - 1)]
    have htel : ∑ t ∈ Ico 2 T, (1 / ((t : ℝ) - 1) - 1 / (t : ℝ)) = 1 - 1 / ((T : ℝ) - 1) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (hK.trans hKT.le)
      clear hK hKT hle
      induction m with
      | zero => norm_num
      | succ m ih =>
        rw [show 2 + (m + 1) = (2 + m) + 1 by omega, sum_Ico_succ_top (by omega), ih]
        push_cast; ring
    have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast (hK.trans hKT.le)
    have : 0 ≤ 1 / ((T : ℝ) - 1) := one_div_nonneg.mpr (by linarith)
    linarith
  · rw [Ico_eq_empty hKT, sum_empty]; norm_num

/-- **Expected pulls of a suboptimal arm under `UCB1`** (sharpened step of
[AuerCesaBianchiFischer2002, Theorem 1], locator not re-verified against primary PDF): for every
`T ≥ 1` and every suboptimal arm `i` (`B.gap i > 0`),
`B.expectedPulls ucb1Policy T i ≤ 8 * log T / (B.gap i) ^ 2 + 2`. -/
theorem ucb1_expectedPulls_le_add_two [Nonempty ι] (B : StochasticBandit ι) {T : ℕ} (hT : 1 ≤ T)
    {i : ι} (hgap : 0 < B.gap i) :
    B.expectedPulls ucb1Policy T i ≤ 8 * log T / B.gap i ^ 2 + 2 := by
  obtain ⟨iStar, hiStar_mean, _⟩ := B.exists_optimal_arm
  have hK2 : 2 ≤ Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨i, iStar, fun h => by
    subst h
    rw [B.gap_def, hiStar_mean, sub_self] at hgap
    exact lt_irrefl 0 hgap⟩
  rcases eq_or_lt_of_le hT with rfl | hT2
  · have hsum := B.sum_expectedPulls_eq ucb1Policy_isMeasurable 1
    have hsingle := single_le_sum (fun j _ => B.expectedPulls_nonneg ucb1Policy 1 j) (mem_univ i)
    simp only [Nat.cast_one, log_one, mul_zero, zero_div, zero_add] at hsum ⊢
    linarith
  have hlogT_pos : 0 < log T := log_pos (by exact_mod_cast hT2)
  set x := 8 * log T / B.gap i ^ 2
  have hx_pos : 0 < x := by positivity
  set ℓ := ⌈x⌉₊
  have hℓ1 : 1 ≤ ℓ := Nat.ceil_pos.mpr hx_pos
  have hx_le_ℓ : x ≤ ℓ := Nat.le_ceil x
  have hℓ_le : (ℓ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx_pos.le).le
  let badRound (t : ℕ) : Set (ι × Fin T → ℝ) :=
    {X | ucb1Policy.choose (runStochastic ucb1Policy X t) = i ∧
      ℓ ≤ pullCount (runStochastic ucb1Policy X t) i}
  have hbad_meas : ∀ t : ℕ, MeasurableSet (badRound t) := fun t =>
    (show MeasurableSet
        {X : ι × Fin T → ℝ | ucb1Policy.choose (runStochastic ucb1Policy X t) = i} by
      rw [show {X : ι × Fin T → ℝ | ucb1Policy.choose (runStochastic ucb1Policy X t) = i} =
        {X | ((runStochastic ucb1Policy X (t + 1))[(Fin.last t).1]'(by simp)).arm = i} by
          ext X; simp [runStochastic_succ]]
      exact (measurable_runStochastic_arms_and_vals ucb1Policy ucb1Policy_isMeasurable
        (t + 1)).1 (Fin.last t) i).inter
    ((measurable_pullCount ucb1Policy ucb1Policy_isMeasurable t i) measurableSet_Ici)
  have hbad_prob : ∀ t ∈ Ico (Fintype.card ι) T,
      (B.sampleMeasure T).real (badRound t) ≤ 2 / (t : ℝ) ^ 3 := by
    intro t ht
    obtain ⟨hKt, htT⟩ := mem_Ico.mp ht
    have ht2 : 2 ≤ t := hK2.trans hKt
    let E_star (s : ℕ) (hsT : s ≤ T) : Set (ι × Fin T → ℝ) :=
      {X | stackMean X iStar s hsT ≤ B.mean iStar - √(2 * log t / s)}
    let E_sub (s : ℕ) (hsT : s ≤ T) : Set (ι × Fin T → ℝ) :=
      {X | B.mean i + √(2 * log t / s) ≤ stackMean X i s hsT}
    have hsubset : badRound t ⊆
        (⋃ s : Fin t, E_star (s.1 + 1) (Nat.succ_le_of_lt (s.isLt.trans htT))) ∪
          (⋃ s : Fin t, E_sub (s.1 + 1) (Nat.succ_le_of_lt (s.isLt.trans htT))) := by
      intro X ⟨hch, hℓ_le_ni⟩
      let hist := runStochastic ucb1Policy X t
      have hun_empty : ¬ (unpulledArms hist).Nonempty := fun ⟨j, hj⟩ => by
        have h0 : pullCount hist j = 0 := (mem_filter.mp hj).2
        have h1 : 1 ≤ pullCount hist j := one_le_pullCount_ucb1 X hKt j
        omega
      have hidx_le : ucb1Index hist iStar ≤ ucb1Index hist i :=
        hch ▸ ucb1Index_le_choose_of_unpulled_empty hun_empty iStar
      set s_star := pullCount hist iStar
      set s_i := pullCount hist i
      have hs_star_1 : 1 ≤ s_star := one_le_pullCount_ucb1 X hKt iStar
      have hs_star_t : s_star ≤ t :=
        (pullCount_le_length hist iStar).trans_eq (length_runStochastic ucb1Policy X t)
      have hs_i_t : s_i ≤ t :=
        (pullCount_le_length hist i).trans_eq (length_runStochastic ucb1Policy X t)
      rw [ucb1Index_def, ucb1Index_def, length_runStochastic ucb1Policy X t,
        empiricalMean_runStochastic_eq_stackMean ucb1Policy htT.le X iStar,
        empiricalMean_runStochastic_eq_stackMean ucb1Policy htT.le X i] at hidx_le
      have hbonus_le : 2 * √(2 * log t / s_i) ≤ B.gap i := by
        have hlog_le : log t ≤ log T := log_le_log (by positivity) (by exact_mod_cast htT.le)
        have hsi_ge : 8 * log T / B.gap i ^ 2 ≤ s_i := hx_le_ℓ.trans (by exact_mod_cast hℓ_le_ni)
        have hsi_pos : (0 : ℝ) < s_i := by exact_mod_cast (hℓ1.trans hℓ_le_ni)
        have hfrac : 2 * log t / s_i ≤ (B.gap i / 2) ^ 2 := by
          rw [div_le_iff₀ hsi_pos]
          have hmul : (B.gap i / 2) ^ 2 * (8 * log T / B.gap i ^ 2) = 2 * log T := by
            have := hgap.ne'
            field_simp
            ring
          have := mul_le_mul_of_nonneg_left hsi_ge (sq_nonneg (B.gap i / 2))
          linarith
        linarith [(sqrt_le_sqrt hfrac).trans_eq (sqrt_sq (by positivity))]
      by_contra hneither
      simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hneither
      have h1 := hneither.1 ⟨s_star - 1, by omega⟩
      have h2 := hneither.2 ⟨s_i - 1, by omega⟩
      have hstar_gt : B.mean iStar - √(2 * log t / s_star) <
          stackMean X iStar s_star (hs_star_t.trans htT.le) := by_contra fun hle => h1 <| by
        simpa only [E_star, Set.mem_ofPred_eq, show s_star - 1 + 1 = s_star by omega] using
          not_lt.mp hle
      have hsub_lt : stackMean X i s_i (hs_i_t.trans htT.le) < B.mean i + √(2 * log t / s_i) :=
        by_contra fun hge => h2 <| by
          simpa only [E_sub, Set.mem_ofPred_eq, show s_i - 1 + 1 = s_i by omega] using not_lt.mp hge
      have hgap_eq : B.mean iStar - B.mean i = B.gap i := by rw [B.gap_def, hiStar_mean]
      linarith
    have hunion_le : (B.sampleMeasure T).real (badRound t) ≤
        (∑ s : Fin t, (B.sampleMeasure T).real
            (E_star (s.1 + 1) (Nat.succ_le_of_lt (s.isLt.trans htT)))) +
          (∑ s : Fin t, (B.sampleMeasure T).real
            (E_sub (s.1 + 1) (Nat.succ_le_of_lt (s.isLt.trans htT)))) :=
      (measureReal_mono hsubset).trans <| (measureReal_union_le _ _).trans <|
        add_le_add (measureReal_iUnion_fintype_le _) (measureReal_iUnion_fintype_le _)
    have hsum_star : (∑ s : Fin t, (B.sampleMeasure T).real
        (E_star (s.1 + 1) (Nat.succ_le_of_lt (s.isLt.trans htT)))) ≤ t * (1 / (t : ℝ) ^ 4) :=
      (sum_le_sum fun _ _ =>
        (measureReal_stackMean_deviation_le B ht2 (Nat.succ_pos _) _ iStar).2).trans_eq (by simp)
    have hsum_sub : (∑ s : Fin t, (B.sampleMeasure T).real
        (E_sub (s.1 + 1) (Nat.succ_le_of_lt (s.isLt.trans htT)))) ≤ t * (1 / (t : ℝ) ^ 4) :=
      (sum_le_sum fun _ _ =>
        (measureReal_stackMean_deviation_le B ht2 (Nat.succ_pos _) _ i).1).trans_eq (by simp)
    have ht_ne : (t : ℝ) ≠ 0 := by positivity
    have : t * (1 / (t : ℝ) ^ 4) + t * (1 / (t : ℝ) ^ 4) = 2 / (t : ℝ) ^ 3 := by field_simp; ring
    linarith
  have hint_bad : ∀ t ∈ Ico (Fintype.card ι) T,
      Integrable ((badRound t).indicator fun _ => (1 : ℝ)) (B.sampleMeasure T) := fun t _ =>
    Integrable.of_mem_Icc 0 1 (measurable_const.indicator (hbad_meas t)).aemeasurable
      (ae_of_all _ fun X => by by_cases h : X ∈ badRound t <;> simp [h])
  have hint_le := integral_mono (B.integrable_pullCount ucb1Policy_isMeasurable T i)
    ((integrable_const (ℓ : ℝ)).add (integrable_finsetSum _ hint_bad)) fun X => by
      have hnat : (pullCount (runStochastic ucb1Policy X T) i : ℝ) ≤
          (ℓ : ℝ) + ∑ t ∈ Ico (Fintype.card ι) T,
            if ucb1Policy.choose (runStochastic ucb1Policy X t) = i ∧
                ℓ ≤ pullCount (runStochastic ucb1Policy X t) i
              then (1 : ℝ) else 0 := by exact_mod_cast pullCount_ucb1_le_add_sum hℓ1 X i
      simpa [Set.indicator_apply, badRound] using hnat
  simp only [Pi.add_apply] at hint_le
  rw [← B.expectedPulls_def, integral_add (integrable_const _) (integrable_finsetSum _ hint_bad),
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_finsetSum _ hint_bad] at hint_le
  have hsum_prob : (∑ t ∈ Ico (Fintype.card ι) T,
      ∫ X, (badRound t).indicator (fun _ => (1 : ℝ)) X ∂(B.sampleMeasure T)) ≤ 1 := by
    calc _ = ∑ t ∈ Ico (Fintype.card ι) T, (B.sampleMeasure T).real (badRound t) :=
          sum_congr rfl fun t _ => by
            rw [integral_indicator_const _ (hbad_meas t), smul_eq_mul, mul_one]
      _ ≤ ∑ t ∈ Ico (Fintype.card ι) T, (2 / (t : ℝ) ^ 3) := sum_le_sum hbad_prob
      _ ≤ 1 := sum_Ico_two_div_cube_le_one hK2
  linarith

/-- **Sharpened logarithmic expected regret of `UCB1`** (sharpening the `1 + π² / 3` constant of
[AuerCesaBianchiFischer2002, Theorem 1] to `2`, locator not re-verified against primary PDF): for
every `T ≥ 1`,
`B.stochasticRegret ucb1Policy T ≤ ∑_{Δ_i > 0} (8 ln T / Δ_i) + 2 ∑_i Δ_i`. -/
theorem ucb1_stochasticRegret_le_sharp [Nonempty ι] (B : StochasticBandit ι) {T : ℕ}
    (hT : 1 ≤ T) :
    B.stochasticRegret ucb1Policy T ≤
      (∑ i ∈ univ.filter (fun i => 0 < B.gap i), 8 * log T / B.gap i) +
        2 * ∑ i : ι, B.gap i := by
  rw [B.stochasticRegret_eq_pseudoRegret ucb1Policy_isMeasurable T, B.pseudoRegret_def,
    sum_filter, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  by_cases hpos : 0 < B.gap i
  · simp only [hpos, ↓reduceIte]
    have hmul := mul_le_mul_of_nonneg_left (ucb1_expectedPulls_le_add_two B hT hpos) hpos.le
    have hsimp : B.gap i * (8 * log T / B.gap i ^ 2 + 2) = 8 * log T / B.gap i + 2 * B.gap i := by
      have := hpos.ne'; field_simp
    linarith
  · simp [le_antisymm (le_of_not_gt hpos) (B.gap_nonneg i)]

/-- **Instance-dependent logarithmic regret of `UCB1`** ([AuerCesaBianchiFischer2002, Theorem 1],
locator not re-verified against primary PDF): for any `[0, 1]`-bounded stochastic `K`-armed bandit
`B` and horizon `T ≥ 1`,
`B.stochasticRegret ucb1Policy T ≤ ∑_{Δ_i > 0} (8 ln T / Δ_i) + (1 + π² / 3) ∑_i Δ_i`. -/
theorem ucb1_stochasticRegret_le [Nonempty ι] (B : StochasticBandit ι) {T : ℕ} (hT : 1 ≤ T) :
    B.stochasticRegret ucb1Policy T ≤
      (∑ i ∈ univ.filter (fun i => 0 < B.gap i), 8 * log T / B.gap i) +
        (1 + π ^ 2 / 3) * ∑ i : ι, B.gap i := by
  refine (ucb1_stochasticRegret_le_sharp B hT).trans ?_
  have hpi : (2 : ℝ) ≤ 1 + π ^ 2 / 3 := by nlinarith [Real.pi_gt_three]
  have hsum_nonneg : 0 ≤ ∑ i : ι, B.gap i := sum_nonneg fun i _ => B.gap_nonneg i
  gcongr

/-- **Problem-independent (minimax) regret of `UCB1` for `T ≥ 1`**: for every `[0, 1]`-bounded
stochastic `K`-armed bandit `B` and `T ≥ 1`,
`B.stochasticRegret ucb1Policy T ≤ √(K T (8 ln T + 2))`. -/
theorem ucb1_stochasticRegret_le_sqrt_add [Nonempty ι] (B : StochasticBandit ι) {T : ℕ}
    (hT : 1 ≤ T) :
    B.stochasticRegret ucb1Policy T ≤
      √((Fintype.card ι : ℝ) * T * (8 * log T + 2)) := by
  rw [B.stochasticRegret_eq_pseudoRegret ucb1Policy_isMeasurable T, B.pseudoRegret_def]
  have hlog_nonneg : 0 ≤ log T := log_nonneg (by exact_mod_cast hT)
  have hsq_arm : ∀ i : ι,
      (B.gap i * B.expectedPulls ucb1Policy T i) ^ 2 ≤
        B.expectedPulls ucb1Policy T i * (8 * log T + 2) := fun i => by
    have hN0 := B.expectedPulls_nonneg ucb1Policy T i
    by_cases hpos : 0 < B.gap i
    · have hgap_sq1 : B.gap i ^ 2 ≤ 1 := by nlinarith [B.gap_le_one i]
      have hΔ2N : B.gap i ^ 2 * B.expectedPulls ucb1Policy T i ≤ 8 * log T + 2 := by
        have hmul := mul_le_mul_of_nonneg_left (ucb1_expectedPulls_le_add_two B hT hpos)
          (sq_nonneg (B.gap i))
        have : B.gap i ^ 2 * (8 * log T / B.gap i ^ 2 + 2) = 8 * log T + 2 * B.gap i ^ 2 := by
          have := (pow_pos hpos 2).ne'; field_simp
        linarith
      calc (B.gap i * B.expectedPulls ucb1Policy T i) ^ 2
          = B.expectedPulls ucb1Policy T i * (B.gap i ^ 2 * B.expectedPulls ucb1Policy T i) := by
            ring
        _ ≤ B.expectedPulls ucb1Policy T i * (8 * log T + 2) := mul_le_mul_of_nonneg_left hΔ2N hN0
    · rw [le_antisymm (le_of_not_gt hpos) (B.gap_nonneg i), zero_mul, sq, zero_mul]; positivity
  refine le_sqrt_of_sq_le ?_
  calc (∑ i : ι, B.gap i * B.expectedPulls ucb1Policy T i) ^ 2
      ≤ (univ.card : ℝ) * ∑ i ∈ univ, (B.gap i * B.expectedPulls ucb1Policy T i) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ (Fintype.card ι : ℝ) * ∑ i : ι, B.expectedPulls ucb1Policy T i * (8 * log T + 2) := by
        rw [card_univ]
        exact mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => hsq_arm i) (Nat.cast_nonneg _)
    _ = (Fintype.card ι : ℝ) * T * (8 * log T + 2) := by
        rw [← sum_mul, B.sum_expectedPulls_eq ucb1Policy_isMeasurable T, mul_assoc]

/-- **Minimax `O(√(K T ln T))` expected regret of `UCB1`** (compare [BubeckCesaBianchi2012,
Theorem 2.1], locator not re-verified against primary PDF): for every `[0, 1]`-bounded stochastic
`K`-armed bandit `B` and every horizon `T ≥ 2`,
`B.stochasticRegret ucb1Policy T ≤ 2 √(3 K T ln T)`. -/
theorem ucb1_stochasticRegret_le_sqrt [Nonempty ι] (B : StochasticBandit ι) {T : ℕ}
    (hT : 2 ≤ T) :
    B.stochasticRegret ucb1Policy T ≤
      2 * √(3 * (Fintype.card ι : ℝ) * T * log T) := by
  refine (ucb1_stochasticRegret_le_sqrt_add B (by omega)).trans ?_
  have hlog2 : (1 : ℝ) / 2 ≤ log T :=
    (by linarith [log_two_gt_d9] : (1 : ℝ) / 2 ≤ log 2).trans
      (log_le_log zero_lt_two (by exact_mod_cast hT))
  calc √((Fintype.card ι : ℝ) * T * (8 * log T + 2))
      ≤ √((Fintype.card ι : ℝ) * T * (12 * log T)) :=
        sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    _ = √((2 : ℝ) ^ 2 * (3 * (Fintype.card ι : ℝ) * T * log T)) := by congr 1; ring
    _ = 2 * √(3 * (Fintype.card ι : ℝ) * T * log T) := by
        rw [sqrt_mul (sq_nonneg 2), sqrt_sq zero_le_two]

end Regret

end Cslib.MachineLearning.OnlineLearning.Bandits
