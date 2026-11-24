/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.FTRL
public import CslibFrontier.MachineLearning.OnlineLearning.LowerBounds
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Follow the Perturbed Leader

In an online linear optimization problem ([KalaiVempala2005, §1–§2]; cited in
[BlumMansour2007AGT, §4.7.1, p. 98]), a learner chooses in each round `t` an element `a` from a
finite decision set `α` represented by action vectors `v : α → ι → ℝ` in `ℝ^ι`, observes a stage
cost vector `ℓ t : ι → ℝ`, and incurs linear cost `⟨v a, ℓ t⟩ = ∑ i, v a i * ℓ t i`.

*Follow the Perturbed Leader* (FPL, due to Hannan (1957) and analyzed for general online linear
problems by Kalai and Vempala [KalaiVempala2005, Theorem 1.1(a)]) draws a random perturbation `p`
uniformly from the cube `[0, 1 / ε]^ι` (equivalently `u / ε` for `u` uniform on the unit cube
`[0, 1]^ι`) and plays in round `t` the decision minimizing `⟨v a, ∑ s < t, ℓ s + u / ε⟩`
(`fplLeader`, inducing the explicit round-`t` distribution `fplProb v ε ℓ t : α → ℝ`).

## Proof architecture and connection to FTRL

1. **Deterministic Be-the-Perturbed-Leader via `IsFTRL`** (`isFTRL_fplLeader`):
   For any fixed `u : ι → ℝ` and `ε > 0`, scaling by `ε` preserves the lexicographic leader
   (`fplLeader_smul_pos`), so `t ↦ fplLeader v (ε • cumVec ℓ t + u)` is an instance of
   `Cslib.MachineLearning.OnlineLearning.OCO.IsFTRL` on `Set.univ` with linear regularizer
   `ψ a = (1 / ε) ⟨v a, u⟩`. Applying `IsFTRL.regret_le_add_sum_sub` bounds the realized regret on
   each trajectory cell by `D / ε` plus the per-round stability differences
   `⟨v (x_t u) - v (x_{t + 1} u), ℓ t⟩`.
2. **Cube translation-overlap stability** (`volume_unitCube_diff_shift_le`, `fpl_stability_step`):
   Between round `t` and round `t + 1`, the cumulative scaled cost shifts by `δ = ε • ℓ t`. By
   translation invariance of Lebesgue volume on `ℝ^ι`, the probability `fplProb v ε ℓ (t + 1) a`
   equals the volume of `leaderRegion` inside the shifted cube `[δ, 1 + δ]^ι`. Cancelling the
   overlap `[0, 1]^ι ∩ [δ, 1 + δ]^ι` leaves only `[0, 1]^ι \ [δ, 1 + δ]^ι`, which is covered by
   `|ι|` coordinate slabs of total volume at most `∑ i, |δ i| = ε ∑ i, |ℓ t i|`.
3. **Regret bounds** (`fpl_regret_le`, `fpl_regret_le_of_l1_diam`, `fpl_regret_le_sqrt`,
   `fpl_experts_regret_le_sqrt` — [KalaiVempala2005, Theorem 1.1(a)]):
   Combining the `D / ε` perturbation term with `T` rounds of `ε R A` stability gives expected
   regret `D / ε + ε R A T`, and tuning `ε = √(D / (R A T))` yields `2 √(D R A T)` (specializing on
   the `N`-expert simplex with `[0, 1]` losses to `2 √(N T)`).

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.FPL.fplDot`: linear cost `∑ i, v a i * c i`.
* `Cslib.MachineLearning.OnlineLearning.FPL.cumVec`: cumulative cost vector `∑ s < t, ℓ s`.
* `Cslib.MachineLearning.OnlineLearning.FPL.fplLeader`: lexicographic minimum-cost leader in `α`.
* `Cslib.MachineLearning.OnlineLearning.FPL.fplProb`: round-`t` action distribution of FPL under
  uniform cube perturbation `[0, 1 / ε]^ι`.
* `Cslib.MachineLearning.OnlineLearning.FPL.fplExpertsProb`: FPL specialized to the `N`-expert
  simplex (`v a i = if i = a then 1 else 0`).

## Main results

* `Cslib.MachineLearning.OnlineLearning.FPL.isFTRL_fplLeader`: fixed-perturbation FPL is an
  instance of `OCO.IsFTRL`.
* `Cslib.MachineLearning.OnlineLearning.FPL.fpl_regret_le`,
  `Cslib.MachineLearning.OnlineLearning.FPL.fpl_regret_le_of_l1_diam`: expected regret
  `D / ε + ε R A T` [KalaiVempala2005, Theorem 1.1(a)].
* `Cslib.MachineLearning.OnlineLearning.FPL.fpl_regret_le_sqrt`: tuned `2 √(D R A T)` expected
  regret [KalaiVempala2005, Theorem 1.1(a)].
* `Cslib.MachineLearning.OnlineLearning.FPL.isOnlineAlg_fplExpertsProb`,
  `Cslib.MachineLearning.OnlineLearning.FPL.fpl_experts_regret_le_sqrt`: experts specialization
  achieving `2 √(N T)` expected regret on `[0, 1]` losses.

## References

* [A. Kalai and S. Vempala, *Efficient algorithms for online decision problems*][KalaiVempala2005]
* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.FPL

open Finset MeasureTheory Real
open scoped ENNReal

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-! ### Linear costs, cumulative vectors, and lexicographic leader -/

/-- Linear pairing `⟨v a, c⟩ = ∑ i, v a i * c i` of decision `a`'s vector with cost vector `c`. -/
def fplDot (v : α → ι → ℝ) (a : α) (c : ι → ℝ) : ℝ :=
  ∑ i, v a i * c i

omit [Fintype α] in
theorem fplDot_add (v : α → ι → ℝ) (a : α) (c₁ c₂ : ι → ℝ) :
    fplDot v a (c₁ + c₂) = fplDot v a c₁ + fplDot v a c₂ := by
  simp only [fplDot, Pi.add_apply, mul_add, sum_add_distrib]

omit [Fintype α] in
theorem fplDot_smul (v : α → ι → ℝ) (a : α) (r : ℝ) (c : ι → ℝ) :
    fplDot v a (fun i => r * c i) = r * fplDot v a c := by
  simp only [fplDot, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- Cumulative cost vector `∑ s < t, ℓ s` before round `t`. -/
def cumVec (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  ∑ s ∈ range t, ℓ s i

omit [Fintype ι] in
@[simp] theorem cumVec_zero (ℓ : ℕ → ι → ℝ) : cumVec ℓ 0 = 0 := by
  funext i
  simp [cumVec]

omit [Fintype ι] in
theorem cumVec_succ (ℓ : ℕ → ι → ℝ) (t : ℕ) : cumVec ℓ (t + 1) = cumVec ℓ t + ℓ t := by
  funext i
  simp [cumVec, sum_range_succ]

omit [Fintype α] in
theorem fplDot_cumVec (v : α → ι → ℝ) (a : α) (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    fplDot v a (cumVec ℓ t) = ∑ s ∈ range t, fplDot v a (ℓ s) := by
  simp only [fplDot, cumVec, mul_sum]
  exact sum_comm

section Leader

variable [Nonempty α] [LinearOrder α]

omit [LinearOrder α] in
private theorem minimizers_nonempty (v : α → ι → ℝ) (c : ι → ℝ) :
    (univ.filter fun b =>
      fplDot v b c ≤ univ.inf' univ_nonempty fun b' => fplDot v b' c).Nonempty := by
  obtain ⟨b₀, hb₀, heq⟩ := exists_mem_eq_inf' univ_nonempty (fun b' => fplDot v b' c)
  exact ⟨b₀, mem_filter.mpr ⟨hb₀, heq.symm.le⟩⟩

/-- Deterministic leader choosing the smallest `a : α` (under `LinearOrder α`) minimizing
`fplDot v a c`. -/
noncomputable def fplLeader (v : α → ι → ℝ) (c : ι → ℝ) : α :=
  (univ.filter fun b =>
    fplDot v b c ≤ univ.inf' univ_nonempty fun b' => fplDot v b' c).min' (minimizers_nonempty v c)

theorem fplLeader_le (v : α → ι → ℝ) (c : ι → ℝ) (b : α) :
    fplDot v (fplLeader v c) c ≤ fplDot v b c := by
  have hmem := min'_mem _ (minimizers_nonempty v c)
  rw [mem_filter] at hmem
  exact hmem.2.trans (inf'_le (fun b' => fplDot v b' c) (mem_univ b))

/-- Exact characterization of `fplLeader`: `a` is chosen iff it minimizes `fplDot v · c` and has
strictly smaller cost than every `b < a`. -/
theorem fplLeader_eq_iff (v : α → ι → ℝ) (c : ι → ℝ) (a : α) :
    fplLeader v c = a ↔
      (∀ b : α, fplDot v a c ≤ fplDot v b c) ∧
      (∀ b : α, b < a → fplDot v a c < fplDot v b c) := by
  set S := univ.filter fun b => fplDot v b c ≤ univ.inf' univ_nonempty fun b' => fplDot v b' c
  constructor
  · rintro rfl
    refine ⟨fplLeader_le v c, fun b hlt => lt_of_le_of_ne (fplLeader_le v c b) fun heq => ?_⟩
    have hbS : b ∈ S := by
      refine mem_filter.mpr ⟨mem_univ b, ?_⟩
      rw [← heq]
      exact (mem_filter.mp (min'_mem S (minimizers_nonempty v c))).2
    exact not_le_of_gt hlt (min'_le S b hbS)
  · rintro ⟨hle, hlt⟩
    have haS : a ∈ S := mem_filter.mpr ⟨mem_univ a, Finset.le_inf' _ _ fun b _ => hle b⟩
    have hmin_le : fplLeader v c ≤ a := min'_le S a haS
    rcases eq_or_lt_of_le hmin_le with heq | hstrict
    · exact heq
    · exact absurd (fplLeader_le v c a) (not_le_of_gt (hlt _ hstrict))

/-- Positive scaling of the cost vector preserves `fplLeader`. -/
theorem fplLeader_smul_pos (v : α → ι → ℝ) {r : ℝ} (hr : 0 < r) (c : ι → ℝ) :
    fplLeader v (fun i => r * c i) = fplLeader v c := by
  rw [fplLeader_eq_iff]
  have h1 := (fplLeader_eq_iff v c (fplLeader v c)).mp rfl
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · rw [fplDot_smul, fplDot_smul]
    exact mul_le_mul_of_nonneg_left (h1.1 b) hr.le
  · rw [fplDot_smul, fplDot_smul]
    exact mul_lt_mul_of_pos_left (h1.2 b hb) hr

/-- **Fixed-perturbation FPL is an instance of `OCO.IsFTRL`**: for `ε > 0` and perturbation
`u : ι → ℝ`, `t ↦ fplLeader v (ε • cumVec ℓ t + u)` minimizes the FTRL objective with linear
regularizer `a ↦ (1 / ε) * fplDot v a u`. -/
theorem isFTRL_fplLeader (v : α → ι → ℝ) {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ → ι → ℝ) (u : ι → ℝ) :
    OCO.IsFTRL (Set.univ : Set α) (fun a => (1 / ε) * fplDot v a u)
      (fun t a => fplDot v a (ℓ t))
      (fun t => fplLeader v (fun i => ε * cumVec ℓ t i + u i)) where
  mem _ := Set.mem_univ _
  isMinOn t b _ := by
    have hscale : (fun i => ε * cumVec ℓ t i + u i) =
        fun i => ε * (cumVec ℓ t i + (1 / ε) * u i) := by
      funext i
      field_simp
    have hobj : ∀ a : α, OCO.ftrlObjective (fun a => (1 / ε) * fplDot v a u)
        (fun s a => fplDot v a (ℓ s)) t a =
        fplDot v a (fun i => cumVec ℓ t i + (1 / ε) * u i) := fun a => by
      rw [OCO.ftrlObjective_def, ← fplDot_cumVec, ← fplDot_smul, ← fplDot_add]
      congr 1
      funext i
      simp [Pi.add_apply, add_comm]
    change OCO.ftrlObjective _ _ t _ ≤ OCO.ftrlObjective _ _ t b
    rw [hobj, hobj, hscale, fplLeader_smul_pos v hε]
    exact fplLeader_le v _ b

/-! ### Measurability, unit-cube action distribution, and translation overlap -/

/-- The unit cube `[0, 1]^ι` in `ι → ℝ`. -/
def unitCube (ι : Type*) : Set (ι → ℝ) :=
  Set.Icc 0 1

omit [Fintype α] [Fintype ι] [Nonempty α] [LinearOrder α] in
theorem mem_unitCube_iff {u : ι → ℝ} : u ∈ unitCube ι ↔ ∀ i : ι, 0 ≤ u i ∧ u i ≤ 1 := by
  simp only [unitCube, Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
  exact ⟨fun ⟨h0, h1⟩ i => ⟨h0 i, h1 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

omit [Fintype α] [Fintype ι] [Nonempty α] [LinearOrder α] in
private theorem measurableSet_unitCube [Finite ι] : MeasurableSet (unitCube ι) :=
  isClosed_Icc.measurableSet

omit [Fintype α] [Nonempty α] [LinearOrder α] in
private theorem volume_unitCube : volume (unitCube ι) = 1 := by
  simp [unitCube, Real.volume_Icc_pi]

omit [Fintype α] [Nonempty α] [LinearOrder α] in
private theorem continuous_fplDot_shift (v : α → ι → ℝ) (a : α) (c₀ : ι → ℝ) :
    Continuous (fun u : ι → ℝ => fplDot v a (c₀ + u)) := by
  classical
  unfold fplDot
  have hrec : ∀ s : Finset ι, Continuous (fun u : ι → ℝ => ∑ i ∈ s, v a i * (c₀ + u) i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [sum_empty]
      exact continuous_const
    | insert i t hit ih =>
      simp only [sum_insert hit, Pi.add_apply]
      exact (continuous_const.mul (continuous_const.add (continuous_apply i))).add ih
  exact hrec univ

private theorem measurableSet_fplLeader_shift_eq (v : α → ι → ℝ) (c₀ : ι → ℝ) (a : α) :
    MeasurableSet {u : ι → ℝ | fplLeader v (c₀ + u) = a} := by
  have heq : {u : ι → ℝ | fplLeader v (c₀ + u) = a} =
      (⋂ b ∈ (univ : Finset α), {u : ι → ℝ | fplDot v a (c₀ + u) ≤ fplDot v b (c₀ + u)}) ∩
      (⋂ b ∈ univ.filter (· < a), {u : ι → ℝ | fplDot v a (c₀ + u) < fplDot v b (c₀ + u)}) := by
    ext u
    simp only [Set.mem_ofPred_eq, fplLeader_eq_iff, Set.mem_inter_iff, Set.mem_iInter,
      mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun b _ => h1 b, h2⟩, fun ⟨h1, h2⟩ => ⟨fun b => h1 b trivial, h2⟩⟩
  rw [heq]
  exact (Finset.measurableSet_biInter _ fun b _ =>
      (isClosed_le (continuous_fplDot_shift v a c₀) (continuous_fplDot_shift v b c₀)).measurableSet
    ).inter
    (Finset.measurableSet_biInter _ fun b _ =>
      (isOpen_lt (continuous_fplDot_shift v a c₀) (continuous_fplDot_shift v b c₀)).measurableSet)

/-- Probability that FPL with parameter `ε` plays decision `a : α` in round `t` under a uniform
perturbation `u` on `unitCube ι = [0, 1]^ι` [KalaiVempala2005, §2]. -/
noncomputable def fplProb (v : α → ι → ℝ) (ε : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (a : α) : ℝ :=
  (volume (unitCube ι ∩ {u : ι → ℝ | fplLeader v (ε • cumVec ℓ t + u) = a})).toReal

theorem fplProb_nonneg (v : α → ι → ℝ) (ε : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (a : α) :
    0 ≤ fplProb v ε ℓ t a :=
  ENNReal.toReal_nonneg

theorem fplProb_congr (v : α → ι → ℝ) (ε : ℝ) {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, ℓ s = ℓ' s) :
    fplProb v ε ℓ t = fplProb v ε ℓ' t := by
  have hcum : cumVec ℓ t = cumVec ℓ' t := by
    funext i
    exact sum_congr rfl fun s hs => congrFun (h s (mem_range.mp hs)) i
  funext a
  simp only [fplProb, hcum]

theorem sum_fplProb (v : α → ι → ℝ) (ε : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ a : α, fplProb v ε ℓ t a = 1 := by
  classical
  set c₀ : ι → ℝ := ε • cumVec ℓ t
  let cell : α → Set (ι → ℝ) := fun a => unitCube ι ∩ {u | fplLeader v (c₀ + u) = a}
  have hm : ∀ a, MeasurableSet (cell a) := fun a =>
    measurableSet_unitCube.inter (measurableSet_fplLeader_shift_eq v c₀ a)
  have hdisj : Pairwise fun a b => Disjoint (cell a) (cell b) := fun a b hab =>
    Set.disjoint_left.mpr fun u hua hub => hab (hua.2.symm.trans hub.2)
  have hunion : (⋃ a ∈ (univ : Finset α), cell a) = unitCube ι := by
    ext u
    simp only [cell, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, _, hu, _⟩ => hu, fun hu => ⟨fplLeader v (c₀ + u), mem_univ _, hu, rfl⟩⟩
  have hfin : ∀ a ∈ (univ : Finset α), volume (cell a) ≠ ⊤ := fun a _ =>
    ne_top_of_le_ne_top (by rw [volume_unitCube]; exact ENNReal.one_ne_top)
      (measure_mono Set.inter_subset_left)
  unfold fplProb
  rw [← ENNReal.toReal_sum hfin, ← measure_biUnion_finset (fun a _ b _ hab => hdisj hab)
    (fun a _ => hm a), hunion, volume_unitCube, ENNReal.toReal_one]

/-- Volume of `[0, 1]^ι \ [δ, 1 + δ]^ι` is at most `∑ i, |δ i|` (covered by `|ι|` coordinate slabs
each of volume `|δ i|`). -/
theorem volume_unitCube_diff_shift_le (δ : ι → ℝ) :
    volume (unitCube ι \ Set.Icc δ (1 + δ)) ≤ ENNReal.ofReal (∑ i : ι, |δ i|) := by
  classical
  let slab : ι → Set (ι → ℝ) := fun i =>
    if 0 ≤ δ i then Set.Icc 0 (fun j => if j = i then |δ i| else 1)
    else Set.Icc (fun j => if j = i then 1 - |δ i| else 0) 1
  have hsub : unitCube ι \ Set.Icc δ (1 + δ) ⊆ ⋃ i ∈ (univ : Finset ι), slab i := by
    intro u ⟨hu01, hnot⟩
    have hu_coord := mem_unitCube_iff.mp hu01
    have hex : ∃ i : ι, ¬ (δ i ≤ u i ∧ u i ≤ 1 + δ i) := by
      by_contra! hall
      exact hnot ⟨fun i => (hall i).1, fun i => (hall i).2⟩
    obtain ⟨i, hi⟩ := hex
    refine Set.mem_iUnion₂.mpr ⟨i, mem_univ i, ?_⟩
    dsimp only [slab]
    by_cases hδi : 0 ≤ δ i
    · simp only [hδi, ↓reduceIte]
      have hui_lt : u i < δ i := by
        have h2 : u i ≤ 1 + δ i := by linarith [(hu_coord i).2]
        by_contra! hge
        exact hi ⟨hge, h2⟩
      refine ⟨fun j => (hu_coord j).1, fun j => ?_⟩
      by_cases hji : j = i
      · subst hji
        simp only [↓reduceIte, abs_of_nonneg hδi]
        exact hui_lt.le
      · simp only [hji, ↓reduceIte]
        exact (hu_coord j).2
    · simp only [hδi, ↓reduceIte]
      have hδi_neg : δ i < 0 := lt_of_not_ge hδi
      have hui_gt : 1 + δ i < u i := by
        have h1 : δ i ≤ u i := by linarith [(hu_coord i).1]
        by_contra! hle
        exact hi ⟨h1, hle⟩
      refine ⟨fun j => ?_, fun j => (hu_coord j).2⟩
      by_cases hji : j = i
      · subst hji
        simp only [↓reduceIte, abs_of_neg hδi_neg]
        linarith
      · simp only [hji, ↓reduceIte]
        exact (hu_coord j).1
  have hslab_vol : ∀ i : ι, volume (slab i) = ENNReal.ofReal |δ i| := fun i => by
    dsimp only [slab]
    by_cases hδi : 0 ≤ δ i
    · simp only [hδi, ↓reduceIte, Real.volume_Icc_pi, Pi.zero_apply, sub_zero]
      rw [← mul_prod_erase univ _ (mem_univ i)]
      simp only [↓reduceIte]
      have hrest : ∏ x ∈ univ.erase i, ENNReal.ofReal (if x = i then |δ i| else 1) = 1 :=
        prod_eq_one fun x hx => by simp [ne_of_mem_erase hx]
      rw [hrest, mul_one]
    · simp only [hδi, ↓reduceIte, Real.volume_Icc_pi, Pi.one_apply]
      rw [← mul_prod_erase univ _ (mem_univ i)]
      simp only [↓reduceIte, sub_sub_cancel]
      have hrest : ∏ x ∈ univ.erase i, ENNReal.ofReal (1 - if x = i then 1 - |δ i| else 0) = 1 :=
        prod_eq_one fun x hx => by simp [ne_of_mem_erase hx]
      rw [hrest, mul_one]
  calc volume (unitCube ι \ Set.Icc δ (1 + δ))
      ≤ volume (⋃ i ∈ (univ : Finset ι), slab i) := measure_mono hsub
    _ ≤ ∑ i ∈ (univ : Finset ι), volume (slab i) := measure_biUnion_finset_le univ slab
    _ = ∑ i : ι, ENNReal.ofReal |δ i| := sum_congr rfl fun i _ => hslab_vol i
    _ = ENNReal.ofReal (∑ i : ι, |δ i|) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _).symm

/-- Per-round stability of `fplProb`: if `fplDot v a (ℓ t) - fplDot v b (ℓ t) ≤ R` for all
`a, b : α`, then for `ε ≥ 0`,
`∑ a, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * fplDot v a (ℓ t) ≤ ε * R * ∑ i, |ℓ t i|`. -/
theorem fpl_stability_step (v : α → ι → ℝ) {ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (ℓ : ℕ → ι → ℝ) (t : ℕ)
    (hspan : ∀ a b : α, fplDot v a (ℓ t) - fplDot v b (ℓ t) ≤ R) :
    ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * fplDot v a (ℓ t) ≤
      ε * R * ∑ i : ι, |ℓ t i| := by
  classical
  set c₀ : ι → ℝ := ε • cumVec ℓ t
  set δ : ι → ℝ := ε • ℓ t
  let A : α → Set (ι → ℝ) := fun a => {z | fplLeader v (c₀ + z) = a}
  have hA_meas : ∀ a, MeasurableSet (A a) := measurableSet_fplLeader_shift_eq v c₀
  have hA_disj : Pairwise fun a b => Disjoint (A a) (A b) := fun a b hab =>
    Set.disjoint_left.mpr fun z hza hzb => hab (hza.symm.trans hzb)
  -- Express `fplProb v ε ℓ (t + 1) a` as `volume (Icc δ (1 + δ) ∩ A a).toReal` via translation:
  have hprob_succ : ∀ a : α,
      fplProb v ε ℓ (t + 1) a = (volume (Set.Icc δ (1 + δ) ∩ A a)).toReal := fun a => by
    have hc_succ : ε • cumVec ℓ (t + 1) = c₀ + δ := by
      funext i
      simp only [cumVec_succ, Pi.smul_apply, Pi.add_apply, smul_eq_mul, c₀, δ]
      ring
    have hpre : unitCube ι ∩ {u | fplLeader v (ε • cumVec ℓ (t + 1) + u) = a} =
        (fun u i => u i + δ i) ⁻¹' (Set.Icc δ (1 + δ) ∩ A a) := by
      ext u
      have hassoc : c₀ + δ + u = c₀ + (fun j => u j + δ j) := by
        funext i
        simp [Pi.add_apply]
        ring
      simp only [hc_succ, hassoc, A, Set.mem_inter_iff, Set.mem_preimage, mem_unitCube_iff,
        Set.mem_Icc, Pi.le_def, Pi.add_apply, Pi.one_apply, Set.mem_ofPred_eq]
      exact ⟨fun ⟨hu, ha⟩ =>
          ⟨⟨fun i => by linarith [(hu i).1], fun i => by linarith [(hu i).2]⟩, ha⟩,
        fun ⟨⟨h0, h1⟩, ha⟩ => ⟨fun i => ⟨by linarith [h0 i], by linarith [h1 i]⟩, ha⟩⟩
    unfold fplProb
    rw [hpre]
    have hmp := volume_preserving_pi fun i : ι => measurePreserving_add_right volume (δ i)
    rw [hmp.measure_preimage (isClosed_Icc.measurableSet.inter (hA_meas a)).nullMeasurableSet]
  -- Subtract `m := min_b fplDot v b (ℓ t)` so all weights `h a := fplDot v a (ℓ t) - m` lie in
  -- `[0, R]`:
  set m := univ.inf' univ_nonempty fun b : α => fplDot v b (ℓ t)
  let h : α → ℝ := fun a => fplDot v a (ℓ t) - m
  have hh0 : ∀ a, 0 ≤ h a := fun a =>
    sub_nonneg.mpr (inf'_le (fun b => fplDot v b (ℓ t)) (mem_univ a))
  have hhR : ∀ a, h a ≤ R := fun a => by
    obtain ⟨b₀, _, hb₀⟩ := exists_mem_eq_inf' univ_nonempty (fun b : α => fplDot v b (ℓ t))
    dsimp only [h, m]
    rw [hb₀]
    exact hspan a b₀
  have hshift_m : ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * fplDot v a (ℓ t) =
      ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * h a := by
    have hdiff_zero : ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * m = 0 := by
      rw [← sum_mul, sum_sub_distrib, sum_fplProb, sum_fplProb, sub_self, zero_mul]
    calc ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * fplDot v a (ℓ t)
        = ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * h a +
            ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * m := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun a _ => by dsimp only [h]; ring
      _ = ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * h a := by
          rw [hdiff_zero, add_zero]
  rw [hshift_m]
  -- Bound `(volume (S ∩ A a)).toReal - (volume (S' ∩ A a)).toReal` by the difference `(S \ S')`:
  set S := unitCube ι
  set S' := Set.Icc δ (1 + δ)
  have hS_fin : volume S ≠ ⊤ := by rw [volume_unitCube]; exact ENNReal.one_ne_top
  have hS'_fin : volume S' ≠ ⊤ := by
    rw [Real.volume_Icc_pi]
    have hprod_fin : ∀ s : Finset ι, ∏ i ∈ s, ENNReal.ofReal ((1 + δ) i - δ i) ≠ ⊤ := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i t hit ih =>
        rw [prod_insert hit]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ih
    exact hprod_fin univ
  have hdiff_le : ∀ a : α,
      fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a ≤ (volume ((S \ S') ∩ A a)).toReal := fun a => by
    rw [hprob_succ a]
    change (volume (S ∩ A a)).toReal - (volume (S' ∩ A a)).toReal ≤ _
    have hsplit : S ∩ A a = ((S ∩ S') ∩ A a) ∪ ((S \ S') ∩ A a) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
      tauto
    have hdisj_part : Disjoint ((S ∩ S') ∩ A a) ((S \ S') ∩ A a) :=
      Set.disjoint_left.mpr fun u hu1 hu2 => hu2.1.2 hu1.1.2
    have hvol_split : volume (S ∩ A a) = volume ((S ∩ S') ∩ A a) + volume ((S \ S') ∩ A a) := by
      rw [hsplit, measure_union hdisj_part (measurableSet_unitCube.diff isClosed_Icc.measurableSet
        |>.inter (hA_meas a))]
    have h1_fin : volume ((S ∩ S') ∩ A a) ≠ ⊤ :=
      ne_top_of_le_ne_top hS_fin
        (measure_mono (Set.inter_subset_left.trans Set.inter_subset_left))
    have h2_fin : volume ((S \ S') ∩ A a) ≠ ⊤ :=
      ne_top_of_le_ne_top hS_fin
        (measure_mono (Set.inter_subset_left.trans Set.sdiff_subset))
    have htoReal_split : (volume (S ∩ A a)).toReal =
        (volume ((S ∩ S') ∩ A a)).toReal + (volume ((S \ S') ∩ A a)).toReal := by
      rw [hvol_split, ENNReal.toReal_add h1_fin h2_fin]
    have hmono : (volume ((S ∩ S') ∩ A a)).toReal ≤ (volume (S' ∩ A a)).toReal :=
      ENNReal.toReal_mono (ne_top_of_le_ne_top hS'_fin (measure_mono Set.inter_subset_left))
        (measure_mono (Set.inter_subset_inter_left (A a) Set.inter_subset_right))
    linarith
  calc ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * h a
      ≤ ∑ a : α, (volume ((S \ S') ∩ A a)).toReal * h a :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hdiff_le a) (hh0 a)
    _ ≤ ∑ a : α, (volume ((S \ S') ∩ A a)).toReal * R :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hhR a) ENNReal.toReal_nonneg
    _ = (∑ a : α, (volume ((S \ S') ∩ A a)).toReal) * R := (sum_mul _ _ _).symm
    _ = (volume (S \ S')).toReal * R := by
        congr 1
        let cell' : α → Set (ι → ℝ) := fun a => (S \ S') ∩ A a
        have hfin_part : ∀ a ∈ (univ : Finset α), volume (cell' a) ≠ ⊤ := fun a _ =>
          ne_top_of_le_ne_top hS_fin
            (measure_mono (Set.inter_subset_left.trans Set.sdiff_subset))
        have hdisj' : Pairwise fun a b => Disjoint (cell' a) (cell' b) := fun a b hab =>
          Set.disjoint_left.mpr fun u hu1 hu2 => hab (hu1.2.symm.trans hu2.2)
        have hmeas' : ∀ a, MeasurableSet (cell' a) := fun a =>
          (measurableSet_unitCube.diff isClosed_Icc.measurableSet).inter (hA_meas a)
        have hunion : (⋃ a ∈ (univ : Finset α), cell' a) = S \ S' := by
          ext u
          simp only [cell', A, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
          exact ⟨fun ⟨_, _, hu, _⟩ => hu, fun hu => ⟨fplLeader v (c₀ + u), mem_univ _, hu, rfl⟩⟩
        change (∑ a : α, (volume (cell' a)).toReal) = _
        rw [← ENNReal.toReal_sum hfin_part, ← measure_biUnion_finset
          (fun a _ b _ hab => hdisj' hab) (fun a _ => hmeas' a), hunion]
    _ ≤ (ENNReal.ofReal (∑ i : ι, |δ i|)).toReal * R :=
        mul_le_mul_of_nonneg_right
          (ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_unitCube_diff_shift_le δ)) hR
    _ = (∑ i : ι, |δ i|) * R := by
        rw [ENNReal.toReal_ofReal (sum_nonneg fun i _ => abs_nonneg _)]
    _ = ε * R * ∑ i : ι, |ℓ t i| := by
        have hδ_sum : ∑ i : ι, |δ i| = ε * ∑ i : ι, |ℓ t i| := by
          rw [mul_sum]
          exact sum_congr rfl fun i _ => by
            dsimp only [δ]
            rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hε]
        rw [hδ_sum]
        ring

/-! ### Main Kalai–Vempala expected regret bounds -/

/-- **Follow-the-Perturbed-Leader expected regret bound** [KalaiVempala2005, Theorem 1.1(a)]:
suppose on the unit cube `u ∈ [0, 1]^ι` every pair `a, b` satisfies `⟨v a - v b, u⟩ ≤ D`, and in
every round `t < T` the cost vector `ℓ t` has decision span `⟨v a - v b, ℓ t⟩ ≤ R` and `L¹` norm
`∑ i, |ℓ t i| ≤ A`. Then for every `ε > 0` and comparator `a_star : α`, expected cost is at most
`∑ t < T, ⟨v a_star, ℓ t⟩ + D / ε + ε * (R * A * T)`. -/
theorem fpl_regret_le (v : α → ι → ℝ) {ε D R A : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hD : ∀ a b : α, ∀ u ∈ unitCube ι, fplDot v a u - fplDot v b u ≤ D)
    (hspan : ∀ t < T, ∀ a b : α, fplDot v a (ℓ t) - fplDot v b (ℓ t) ≤ R)
    (hl1 : ∀ t < T, ∑ i : ι, |ℓ t i| ≤ A)
    (a_star : α) :
    ∑ t ∈ range T, ∑ a : α, fplProb v ε ℓ t a * fplDot v a (ℓ t) ≤
      ∑ t ∈ range T, fplDot v a_star (ℓ t) + D / ε + ε * (R * A * T) := by
  classical
  -- Partition `unitCube ι` into the finitely many trajectory cells `w : Fin (T + 1) → α`:
  let x : ℕ → (ι → ℝ) → α := fun k u => fplLeader v (ε • cumVec ℓ k + u)
  let trajCell : (Fin (T + 1) → α) → Set (ι → ℝ) := fun w =>
    unitCube ι ∩ ⋂ k ∈ (univ : Finset (Fin (T + 1))), {u | x k.1 u = w k}
  have hcell_meas : ∀ w, MeasurableSet (trajCell w) := fun w =>
    measurableSet_unitCube.inter (Finset.measurableSet_biInter _ fun k _ =>
      measurableSet_fplLeader_shift_eq v (ε • cumVec ℓ k.1) (w k))
  have hcell_disj : Pairwise fun w₁ w₂ => Disjoint (trajCell w₁) (trajCell w₂) :=
    fun w₁ w₂ hne => Set.disjoint_left.mpr fun u hu1 hu2 => hne <| funext fun k => by
      have h1 := Set.mem_iInter₂.mp hu1.2 k (mem_univ k)
      have h2 := Set.mem_iInter₂.mp hu2.2 k (mem_univ k)
      exact h1.symm.trans h2
  have hcell_fin : ∀ w, volume (trajCell w) ≠ ⊤ := fun w =>
    ne_top_of_le_ne_top (by rw [volume_unitCube]; exact ENNReal.one_ne_top)
      (measure_mono Set.inter_subset_left)
  let μw : (Fin (T + 1) → α) → ℝ := fun w => (volume (trajCell w)).toReal
  have hμw_nn : ∀ w, 0 ≤ μw w := fun _ => ENNReal.toReal_nonneg
  -- Marginal identity: summing `μw w * F (w k)` over `w` yields `∑ a, fplProb v ε ℓ k.1 a * F a`:
  have hmarg : ∀ (k : Fin (T + 1)) (F : α → ℝ),
      ∑ w : Fin (T + 1) → α, μw w * F (w k) = ∑ a : α, fplProb v ε ℓ k.1 a * F a := by
    intro k F
    have hprob_k : ∀ a : α, fplProb v ε ℓ k.1 a = ∑ w with w k = a, μw w := fun a => by
      have hunion_a : unitCube ι ∩ {u | x k.1 u = a} =
          ⋃ w ∈ univ.filter (fun w : Fin (T + 1) → α => w k = a), trajCell w := by
        ext u
        simp only [trajCell, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, mem_filter,
          mem_univ, true_and, Set.mem_iInter]
        constructor
        · rintro ⟨hu01, hxk⟩
          exact ⟨fun j => x j.1 u, hxk, hu01, fun j _ => rfl⟩
        · rintro ⟨w, rfl, hu01, hw⟩
          exact ⟨hu01, hw k trivial⟩
      unfold fplProb
      change (volume (unitCube ι ∩ {u | x k.1 u = a})).toReal = _
      rw [hunion_a, measure_biUnion_finset (fun w₁ _ w₂ _ hne => hcell_disj hne)
        (fun w _ => hcell_meas w), ENNReal.toReal_sum fun w _ => hcell_fin w]
    simp only [hprob_k, sum_mul]
    calc ∑ w : Fin (T + 1) → α, μw w * F (w k)
        = ∑ w : Fin (T + 1) → α, ∑ a : α, if w k = a then μw w * F a else 0 :=
          sum_congr rfl fun w _ => by simp only [sum_ite_eq, mem_univ, ↓reduceIte]
      _ = ∑ a : α, ∑ w : Fin (T + 1) → α, if w k = a then μw w * F a else 0 := sum_comm
      _ = ∑ a : α, ∑ w with w k = a, μw w * F a :=
          sum_congr rfl fun a _ => (sum_filter _ _).symm
  have hsum_μw : ∑ w : Fin (T + 1) → α, μw w = 1 := by
    have h1 := hmarg 0 (fun _ => 1)
    simp only [mul_one, Fin.val_zero, sum_fplProb] at h1
    exact h1
  -- On every cell `w`, `μw w * (BTL LHS) ≤ μw w * (BTL RHS)` via `IsFTRL.regret_le_add_sum_sub`:
  have hcell_btl : ∀ w : Fin (T + 1) → α,
      μw w * (∑ t : Fin T, fplDot v (w t.castSucc) (ℓ t.1)) ≤
        μw w * (∑ t : Fin T, fplDot v a_star (ℓ t.1) + D / ε +
          ∑ t : Fin T, (fplDot v (w t.castSucc) (ℓ t.1) - fplDot v (w t.succ) (ℓ t.1))) := by
    intro w
    by_cases hzero : volume (trajCell w) = 0
    · have hm0 : μw w = 0 := by simp [μw, hzero]
      rw [hm0, zero_mul, zero_mul]
    · obtain ⟨u, hu⟩ := nonempty_of_measure_ne_zero hzero
      have hu_cube : u ∈ unitCube ι := hu.1
      have hxu : ∀ k : Fin (T + 1), x k.1 u = w k := fun k =>
        Set.mem_iInter₂.mp hu.2 k (mem_univ k)
      refine mul_le_mul_of_nonneg_left ?_ (hμw_nn w)
      have hftrl := (isFTRL_fplLeader v hε ℓ u).regret_le_add_sum_sub (Set.mem_univ a_star) T
      rw [sum_sub_distrib, sum_range, sum_range, sum_range] at hftrl
      change (∑ t : Fin T, fplDot v (x t.1 u) (ℓ t.1)) - ∑ t : Fin T, fplDot v a_star (ℓ t.1) ≤
        (1 / ε) * fplDot v a_star u - (1 / ε) * fplDot v (x 0 u) u +
          ∑ t : Fin T, (fplDot v (x t.1 u) (ℓ t.1) - fplDot v (x (t.1 + 1) u) (ℓ t.1)) at hftrl
      have hlhs : (∑ t : Fin T, fplDot v (x t.1 u) (ℓ t.1)) =
          ∑ t : Fin T, fplDot v (w t.castSucc) (ℓ t.1) :=
        sum_congr rfl fun t _ => by
          have ht : x t.1 u = w t.castSucc := by simpa only [Fin.val_castSucc] using hxu t.castSucc
          rw [ht]
      have hstab : (∑ t : Fin T, (fplDot v (x t.1 u) (ℓ t.1) - fplDot v (x (t.1 + 1) u) (ℓ t.1))) =
          ∑ t : Fin T, (fplDot v (w t.castSucc) (ℓ t.1) - fplDot v (w t.succ) (ℓ t.1)) :=
        sum_congr rfl fun t _ => by
          have ht : x t.1 u = w t.castSucc := by simpa only [Fin.val_castSucc] using hxu t.castSucc
          have ht1 : x (t.1 + 1) u = w t.succ := by simpa only [Fin.val_succ] using hxu t.succ
          rw [ht, ht1]
      have hpert : (1 / ε) * fplDot v a_star u - (1 / ε) * fplDot v (x 0 u) u ≤ D / ε := by
        rw [← mul_sub, one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right (hD a_star (x 0 u) u hu_cube) hε.le
      rw [hlhs, hstab] at hftrl
      linarith
  -- Sum `hcell_btl` over all `w`:
  have hsum_btl := sum_le_sum fun w (_ : w ∈ univ) => hcell_btl w
  have hlhs_eq : (∑ w : Fin (T + 1) → α, μw w * ∑ t : Fin T, fplDot v (w t.castSucc) (ℓ t.1)) =
      ∑ t ∈ range T, ∑ a : α, fplProb v ε ℓ t a * fplDot v a (ℓ t) := by
    simp_rw [mul_sum]
    rw [sum_comm, sum_range]
    exact sum_congr rfl fun t _ => by
      simpa only [Fin.val_castSucc] using hmarg t.castSucc (fun a => fplDot v a (ℓ t.1))
  have hrhs_eq : (∑ w : Fin (T + 1) → α, μw w *
      (∑ t : Fin T, fplDot v a_star (ℓ t.1) + D / ε +
        ∑ t : Fin T, (fplDot v (w t.castSucc) (ℓ t.1) - fplDot v (w t.succ) (ℓ t.1)))) =
      ∑ t ∈ range T, fplDot v a_star (ℓ t) + D / ε +
        ∑ t ∈ range T, ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) *
          fplDot v a (ℓ t) := by
    simp only [mul_add, sum_add_distrib, ← sum_mul, hsum_μw, one_mul, sum_range]
    congr 1
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    simp only [mul_sub, sum_sub_distrib, sub_mul]
    rw [hmarg t.castSucc (fun a => fplDot v a (ℓ t.1)),
      hmarg t.succ (fun a => fplDot v a (ℓ t.1)), Fin.val_castSucc, Fin.val_succ]
  rw [hlhs_eq, hrhs_eq] at hsum_btl
  -- Bound each stability term by `ε * R * A`:
  have hstab_sum : ∑ t ∈ range T, ∑ a : α,
      (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * fplDot v a (ℓ t) ≤ ε * (R * A * T) := by
    calc ∑ t ∈ range T, ∑ a : α,
          (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * fplDot v a (ℓ t)
        ≤ ∑ _t ∈ range T, (ε * R * A) := sum_le_sum fun t ht => by
          have ht' := mem_range.mp ht
          exact (fpl_stability_step v hε.le hR ℓ t (hspan t ht')).trans
            (mul_le_mul_of_nonneg_left (hl1 t ht') (mul_nonneg hε.le hR))
      _ = ε * (R * A * T) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          ring
  linarith

/-- Specialization of `fpl_regret_le` under Kalai–Vempala's `L¹`-diameter assumption
`∀ a b, ∑ i, |v a i - v b i| ≤ D` [KalaiVempala2005, Theorem 1.1(a)]. -/
theorem fpl_regret_le_of_l1_diam (v : α → ι → ℝ) {ε D R A : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hD : ∀ a b : α, ∑ i : ι, |v a i - v b i| ≤ D)
    (hspan : ∀ t < T, ∀ a b : α, fplDot v a (ℓ t) - fplDot v b (ℓ t) ≤ R)
    (hl1 : ∀ t < T, ∑ i : ι, |ℓ t i| ≤ A)
    (a_star : α) :
    ∑ t ∈ range T, ∑ a : α, fplProb v ε ℓ t a * fplDot v a (ℓ t) ≤
      ∑ t ∈ range T, fplDot v a_star (ℓ t) + D / ε + ε * (R * A * T) := by
  refine fpl_regret_le v hε hR (fun a b u hu => ?_) hspan hl1 a_star
  calc fplDot v a u - fplDot v b u
      = ∑ i : ι, (v a i - v b i) * u i := by
        simp only [fplDot, ← sum_sub_distrib, sub_mul]
    _ ≤ ∑ i : ι, |v a i - v b i| * 1 := sum_le_sum fun i _ => by
        have huc := mem_unitCube_iff.mp hu i
        have hu0 : 0 ≤ u i := huc.1
        have hu1 : u i ≤ 1 := huc.2
        have hle := le_abs_self (v a i - v b i)
        nlinarith [abs_nonneg (v a i - v b i)]
    _ ≤ D := by simp only [mul_one]; exact hD a b

/-- **Tuned Kalai–Vempala expected regret `2 √(D R A T)`** [KalaiVempala2005, Theorem 1.1(a)]:
setting `ε = √(D / (R * A * T))` balances the perturbation and stability terms to `2 √(D R A T)`. -/
theorem fpl_regret_le_sqrt (v : α → ι → ℝ) {D R A : ℝ} (hD_pos : 0 < D) (hR_pos : 0 < R)
    (hA_pos : 0 < A) {ℓ : ℕ → ι → ℝ} {T : ℕ} (hT : 0 < T)
    (hD : ∀ a b : α, ∀ u ∈ unitCube ι, fplDot v a u - fplDot v b u ≤ D)
    (hspan : ∀ t < T, ∀ a b : α, fplDot v a (ℓ t) - fplDot v b (ℓ t) ≤ R)
    (hl1 : ∀ t < T, ∑ i : ι, |ℓ t i| ≤ A)
    (a_star : α) :
    let ε := √(D / (R * A * T))
    ∑ t ∈ range T, ∑ a : α, fplProb v ε ℓ t a * fplDot v a (ℓ t) ≤
      ∑ t ∈ range T, fplDot v a_star (ℓ t) + 2 * √(D * (R * A * T)) := by
  intro ε
  set M := R * A * T
  have hM : 0 < M := by
    dsimp only [M]
    have : (0 : ℝ) < T := Nat.cast_pos.mpr hT
    positivity
  have hε : 0 < ε := sqrt_pos.mpr (div_pos hD_pos hM)
  refine (fpl_regret_le v hε hR_pos.le hD hspan hl1 a_star).trans_eq ?_
  rw [add_assoc]
  congr 1
  change D / √(D / M) + √(D / M) * M = 2 * √(D * M)
  rw [add_comm]
  exact (Experts.sqrt_div_mul_add_div_sqrt_div hD_pos hM).trans (by rw [mul_comm M D])

end Leader

/-! ### Specialization to standard `N`-expert prediction -/

section ExpertsSpecialization

variable [Nonempty ι] [LinearOrder ι]

/-- Indicator vector `i ↦ if i = a then 1 else 0` of expert `a : ι`. -/
def expertVec (a i : ι) : ℝ :=
  if i = a then 1 else 0

omit [Nonempty ι] in
@[simp] theorem fplDot_expertVec (a : ι) (c : ι → ℝ) :
    fplDot (expertVec (ι := ι)) a c = c a := by
  simp [fplDot, expertVec]

/-- Follow-the-Perturbed-Leader specialized to the `N`-expert setting (`v = expertVec`). -/
noncomputable def fplExpertsProb (ε : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (a : ι) : ℝ :=
  fplProb (expertVec (ι := ι)) ε ℓ t a

/-- `fplExpertsProb ε` is a causal online experts algorithm (`Experts.IsOnlineAlg`). -/
theorem isOnlineAlg_fplExpertsProb (ε : ℝ) :
    Experts.IsOnlineAlg (fplExpertsProb (ι := ι) ε) where
  nonneg ℓ t a := fplProb_nonneg expertVec ε ℓ t a
  sum_eq_one ℓ t := sum_fplProb expertVec ε ℓ t
  congr h := fplProb_congr expertVec ε h

/-- **FPL expected regret `2 √(|ι| * T)` for `N` experts on `[0, 1]` losses**: on the simplex of
basis vectors `expertVec`, the one-sided cube bound is `D = 1`, the stage span is `R = 1`, and the
`L¹` loss bound is `A = |ι|`, giving `2 √(|ι| * T)` with `ε = √(1 / (|ι| * T))`. -/
theorem fpl_experts_regret_le_sqrt {ℓ : ℕ → ι → ℝ} {T : ℕ} (hT : 0 < T)
    (hℓ : ∀ t < T, ∀ i : ι, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (k : ι) :
    let ε := √(1 / ((Fintype.card ι : ℝ) * T))
    ∑ t ∈ range T, ∑ a : ι, fplExpertsProb ε ℓ t a * ℓ t a ≤
      Experts.cumLoss ℓ T k + 2 * √((Fintype.card ι : ℝ) * T) := by
  intro ε
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hD : ∀ a b : ι, ∀ u ∈ unitCube ι, fplDot expertVec a u - fplDot expertVec b u ≤ 1 := by
    intro a b u hu
    simp only [fplDot_expertVec]
    linarith [(mem_unitCube_iff.mp hu b).1, (mem_unitCube_iff.mp hu a).2]
  have hspan : ∀ t < T, ∀ a b : ι, fplDot expertVec a (ℓ t) - fplDot expertVec b (ℓ t) ≤ 1 := by
    intro t ht a b
    simp only [fplDot_expertVec]
    linarith [(hℓ t ht b).1, (hℓ t ht a).2]
  have hl1 : ∀ t < T, ∑ i : ι, |ℓ t i| ≤ Fintype.card ι := by
    intro t ht
    calc ∑ i : ι, |ℓ t i| ≤ ∑ _i : ι, (1 : ℝ) := sum_le_sum fun i _ => by
          rw [abs_of_nonneg (hℓ t ht i).1]
          exact (hℓ t ht i).2
      _ = Fintype.card ι := by simp
  have h := fpl_regret_le_sqrt (expertVec (ι := ι)) zero_lt_one zero_lt_one hN hT hD hspan hl1 k
  simpa only [one_mul, fplDot_expertVec, fplExpertsProb, Experts.cumLoss] using h

end ExpertsSpecialization

end Cslib.MachineLearning.OnlineLearning.FPL
