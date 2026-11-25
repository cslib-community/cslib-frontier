/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.FTRL
public import CslibFrontier.MachineLearning.OnlineLearning.LowerBounds
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Follow the Perturbed Leader

In an online linear optimization problem ([KalaiVempala2005]; discussed in prose in
[BlumMansour2007AGT, §4.7.1, p. 98]), a learner chooses in each round `t` an element `a` from a
finite decision set `α` represented by action vectors `v : α → ι → ℝ` in `ℝ^ι`, observes a stage
cost vector `ℓ t : ι → ℝ`, and incurs linear cost `v a ⬝ᵥ ℓ t = ∑ i, v a i * ℓ t i`.

*Follow the Perturbed Leader* (FPL, due to Hannan (1957) and analyzed for general online linear
decision problems by Kalai and Vempala [KalaiVempala2005]) draws a random perturbation uniformly
from the cube `[0, 1 / ε]^ι` (equivalently `(1 / ε) • u` for `u` uniform on the unit cube
`Set.Icc (0 : ι → ℝ) 1`) and plays in round `t` the decision minimizing
`v a ⬝ᵥ (∑ s ∈ range t, ℓ s + (1 / ε) • u)` (`fplLeader`, inducing the round-`t` distribution
`fplProb v ε ℓ t : α → ℝ`).

Source note: [BlumMansour2007AGT, §4.7.1, p. 98] summarizes the online linear optimization model of
Kalai and Vempala in prose without stating a numbered theorem, and [KalaiVempala2005] was not
directly inspected. The uniform-cube formulation and regret bounds below are self-contained
mathematical statements over real vectors and Lebesgue volume, without claiming offline-oracle
running time, and are not registered as a cited theorem.

## Proof architecture and connection to FTRL

1. **Fixed-perturbation FPL via `OCO.IsFTRL`** (`isFTRL_fplLeader`):
   For any fixed `u : ι → ℝ` and `ε > 0`, positive scaling by `ε` preserves the lexicographic
   leader (`fplLeader_smul_pos`), so `t ↦ fplLeader v (ε • ∑ s ∈ range t, ℓ s + u)` is an instance
   of `Cslib.MachineLearning.OnlineLearning.OCO.IsFTRL` on `Set.univ` with linear regularizer
   `ψ a = (1 / ε) * (v a ⬝ᵥ u)`. Applying `OCO.IsFTRL.regret_le_add_sum_sub` bounds the realized
   regret on each trajectory cell by `D / ε` plus the per-round stability differences
   `v (x_t u) ⬝ᵥ ℓ t - v (x_{t + 1} u) ⬝ᵥ ℓ t`.
2. **Cube translation-overlap stability** (`fpl_stability_step`):
   Between round `t` and round `t + 1`, the scaled cumulative cost shifts by `δ = ε • ℓ t`. By
   translation invariance of Lebesgue volume on `ℝ^ι`, `fplProb v ε ℓ (t + 1) a` equals the volume
   of the leader region inside the shifted cube `Set.Icc δ (1 + δ)`. Cancelling the overlap with
   `Set.Icc 0 1` leaves only `Set.Icc (0 : ι → ℝ) 1 \ Set.Icc δ (1 + δ)`, which is covered by `|ι|`
   coordinate slabs of total volume at most `∑ i, |δ i| = ε * ∑ i, |ℓ t i|`.
3. **Expected regret bounds** (`fpl_regret_le`, `fpl_regret_le_sqrt`, `fpl_experts_regret_le_sqrt`):
   Combining the `D / ε` perturbation term with `T` rounds of `ε * R * A` stability gives expected
   regret `D / ε + ε * (R * A * T)`, and tuning `ε = √(D / (R * A * T))` yields `2 * √(D * R * A *
   T)`. On the standard basis vectors `Pi.single a 1` (`fplExpertsProb`), `[0, 1]` losses have
   `D = 1`, `R = 1`, and `A = |ι|`, specializing to `2 * √(|ι| * T)`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.FPL.fplLeader`: lexicographic minimum-cost leader in `α`
  minimizing `v a ⬝ᵥ c`.
* `Cslib.MachineLearning.OnlineLearning.FPL.fplProb`: round-`t` action distribution of FPL under a
  uniform perturbation on `Set.Icc (0 : ι → ℝ) 1`.
* `Cslib.MachineLearning.OnlineLearning.FPL.fplExpertsProb`: FPL specialized to the `N`-expert
  setting (`v a = Pi.single a 1`).

## Main results

* `Cslib.MachineLearning.OnlineLearning.FPL.isFTRL_fplLeader`: fixed-perturbation FPL is an
  instance of `OCO.IsFTRL`.
* `Cslib.MachineLearning.OnlineLearning.FPL.fpl_stability_step`: per-round `ε * R * ‖ℓ t‖₁`
  distribution stability from unit-cube translation overlap.
* `Cslib.MachineLearning.OnlineLearning.FPL.fpl_regret_le`: expected regret bound
  `D / ε + ε * (R * A * T)`.
* `Cslib.MachineLearning.OnlineLearning.FPL.fpl_regret_le_sqrt`: tuned `2 * √(D * (R * A * T))`
  expected regret bound.
* `Cslib.MachineLearning.OnlineLearning.FPL.isOnlineAlgorithm_fplExpertsProb`,
  `Cslib.MachineLearning.OnlineLearning.FPL.fpl_experts_regret_le_sqrt`: experts specialization
  satisfying `Experts.IsOnlineAlgorithm` and achieving `2 * √(|ι| * T)` expected regret on `[0, 1]`
  losses.

## References

* [A. Kalai and S. Vempala, *Efficient Algorithms for Online Decision Problems*][KalaiVempala2005]
* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.FPL

open Finset MeasureTheory Real
open scoped ENNReal

variable {α ι : Type*} [Fintype α] [Fintype ι]

section Leader

variable [Nonempty α] [LinearOrder α]

omit [LinearOrder α] in
private theorem minimizers_nonempty (v : α → ι → ℝ) (c : ι → ℝ) :
    (univ.filter fun b =>
      v b ⬝ᵥ c ≤ univ.inf' univ_nonempty fun b' => v b' ⬝ᵥ c).Nonempty := by
  obtain ⟨b₀, hb₀, heq⟩ := exists_mem_eq_inf' univ_nonempty (fun b' => v b' ⬝ᵥ c)
  exact ⟨b₀, mem_filter.mpr ⟨hb₀, heq.symm.le⟩⟩

/-- Deterministic leader choosing the smallest `a : α` (under `LinearOrder α`) minimizing the
linear cost `v a ⬝ᵥ c`. -/
noncomputable def fplLeader (v : α → ι → ℝ) (c : ι → ℝ) : α :=
  (univ.filter fun b =>
    v b ⬝ᵥ c ≤ univ.inf' univ_nonempty fun b' => v b' ⬝ᵥ c).min' (minimizers_nonempty v c)

theorem fplLeader_le (v : α → ι → ℝ) (c : ι → ℝ) (b : α) :
    v (fplLeader v c) ⬝ᵥ c ≤ v b ⬝ᵥ c :=
  (mem_filter.mp (min'_mem _ (minimizers_nonempty v c))).2.trans (inf'_le _ (mem_univ b))

/-- Exact characterization of `fplLeader`: `a` is chosen iff it minimizes `v · ⬝ᵥ c` and has
strictly smaller cost than every `b < a`. -/
theorem fplLeader_eq_iff (v : α → ι → ℝ) (c : ι → ℝ) (a : α) :
    fplLeader v c = a ↔
      (∀ b : α, v a ⬝ᵥ c ≤ v b ⬝ᵥ c) ∧
      (∀ b : α, b < a → v a ⬝ᵥ c < v b ⬝ᵥ c) := by
  set S := univ.filter fun b => v b ⬝ᵥ c ≤ univ.inf' univ_nonempty fun b' => v b' ⬝ᵥ c
  refine ⟨?_, fun ⟨hle, hlt⟩ => ?_⟩
  · rintro rfl
    refine ⟨fplLeader_le v c, fun b hlt => lt_of_le_of_ne (fplLeader_le v c b) fun heq =>
      not_le_of_gt hlt (min'_le S b (mem_filter.mpr ⟨mem_univ b,
        heq ▸ (mem_filter.mp (min'_mem S (minimizers_nonempty v c))).2⟩))⟩
  · have haS : a ∈ S := mem_filter.mpr ⟨mem_univ a, Finset.le_inf' _ _ fun b _ => hle b⟩
    exact (min'_le S a haS).eq_or_lt.resolve_right fun h =>
      not_le_of_gt (hlt _ h) (fplLeader_le v c a)

/-- Positive scaling of the cost vector preserves `fplLeader`. -/
theorem fplLeader_smul_pos (v : α → ι → ℝ) {r : ℝ} (hr : 0 < r) (c : ι → ℝ) :
    fplLeader v (r • c) = fplLeader v c := by
  rw [fplLeader_eq_iff]
  have h1 := (fplLeader_eq_iff v c (fplLeader v c)).mp rfl
  simp only [dotProduct_smul, smul_eq_mul]
  exact ⟨fun b => mul_le_mul_of_nonneg_left (h1.1 b) hr.le,
    fun b hb => mul_lt_mul_of_pos_left (h1.2 b hb) hr⟩

/-- **Fixed-perturbation FPL is an instance of `OCO.IsFTRL`**: for `ε > 0` and perturbation
`u : ι → ℝ`, `t ↦ fplLeader v (ε • ∑ s ∈ range t, ℓ s + u)` minimizes the FTRL objective with
linear regularizer `a ↦ (1 / ε) * (v a ⬝ᵥ u)`. -/
theorem isFTRL_fplLeader (v : α → ι → ℝ) {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ → ι → ℝ) (u : ι → ℝ) :
    OCO.IsFTRL (Set.univ : Set α) (fun a => (1 / ε) * (v a ⬝ᵥ u))
      (fun t a => v a ⬝ᵥ ℓ t)
      (fun t => fplLeader v (ε • ∑ s ∈ range t, ℓ s + u)) where
  mem _ := Set.mem_univ _
  isMinOn t b _ := by
    have hscale : ε • ∑ s ∈ range t, ℓ s + u = ε • (∑ s ∈ range t, ℓ s + (1 / ε) • u) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    have hobj (a : α) : OCO.ftrlObjective (fun a => (1 / ε) * (v a ⬝ᵥ u))
        (fun s a => v a ⬝ᵥ ℓ s) t a = v a ⬝ᵥ (∑ s ∈ range t, ℓ s + (1 / ε) • u) := by
      rw [OCO.ftrlObjective_def, ← dotProduct_sum, dotProduct_add, dotProduct_smul, smul_eq_mul,
        add_comm]
    change OCO.ftrlObjective _ _ t _ ≤ OCO.ftrlObjective _ _ t b
    rw [hobj, hobj, hscale, fplLeader_smul_pos v hε]
    exact fplLeader_le v _ b

/-! ### Measurability, unit-cube action distribution, and translation overlap -/

omit [Fintype α] [Nonempty α] [LinearOrder α] in
private theorem continuous_dotProduct_shift (v : α → ι → ℝ) (a : α) (c₀ : ι → ℝ) :
    Continuous (fun u : ι → ℝ => v a ⬝ᵥ (c₀ + u)) := by
  unfold dotProduct; fun_prop

private theorem measurableSet_fplLeader_shift_eq (v : α → ι → ℝ) (c₀ : ι → ℝ) (a : α) :
    MeasurableSet {u : ι → ℝ | fplLeader v (c₀ + u) = a} := by
  have heq : {u : ι → ℝ | fplLeader v (c₀ + u) = a} =
      (⋂ b ∈ (univ : Finset α), {u | v a ⬝ᵥ (c₀ + u) ≤ v b ⬝ᵥ (c₀ + u)}) ∩
      (⋂ b ∈ univ.filter (· < a), {u | v a ⬝ᵥ (c₀ + u) < v b ⬝ᵥ (c₀ + u)}) := by
    ext u
    simp only [Set.mem_ofPred_eq, fplLeader_eq_iff, Set.mem_inter_iff, Set.mem_iInter,
      mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun b _ => h1 b, h2⟩, fun ⟨h1, h2⟩ => ⟨fun b => h1 b trivial, h2⟩⟩
  rw [heq]
  exact (Finset.measurableSet_biInter _ fun b _ =>
      (isClosed_le (continuous_dotProduct_shift v a c₀)
        (continuous_dotProduct_shift v b c₀)).measurableSet).inter
    (Finset.measurableSet_biInter _ fun b _ =>
      (isOpen_lt (continuous_dotProduct_shift v a c₀)
        (continuous_dotProduct_shift v b c₀)).measurableSet)

omit [Fintype α] [Nonempty α] [LinearOrder α] in
private theorem volume_unitIcc : volume (Set.Icc (0 : ι → ℝ) 1) = 1 := by
  simp only [Real.volume_Icc_pi, Pi.one_apply, Pi.zero_apply, sub_zero, ENNReal.ofReal_one,
    prod_const_one]

private theorem sum_volume_inter_fplLeader_toReal (v : α → ι → ℝ) (c₀ : ι → ℝ)
    {T : Set (ι → ℝ)} (hTm : MeasurableSet T) (hTf : volume T ≠ ⊤) :
    ∑ a : α, (volume (T ∩ {u : ι → ℝ | fplLeader v (c₀ + u) = a})).toReal =
      (volume T).toReal := by
  have hdisj : Pairwise fun a b : α =>
      Disjoint (T ∩ {u | fplLeader v (c₀ + u) = a}) (T ∩ {u | fplLeader v (c₀ + u) = b}) :=
    fun _ _ hab => Set.disjoint_left.mpr fun _ h1 h2 => hab (h1.2.symm.trans h2.2)
  have hunion : (⋃ a ∈ (univ : Finset α), T ∩ {u | fplLeader v (c₀ + u) = a}) = T := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, _, hu, _⟩ => hu, fun hu => ⟨fplLeader v (c₀ + u), mem_univ _, hu, rfl⟩⟩
  rw [← ENNReal.toReal_sum fun a _ => ne_top_of_le_ne_top hTf (measure_mono Set.inter_subset_left),
    ← measure_biUnion_finset (fun _ _ _ _ hab => hdisj hab)
      (fun a _ => hTm.inter (measurableSet_fplLeader_shift_eq v c₀ a)), hunion]

/-- Probability that FPL with parameter `ε` plays decision `a : α` in round `t` under a uniform
perturbation `u` on the unit cube `Set.Icc (0 : ι → ℝ) 1`. -/
noncomputable def fplProb (v : α → ι → ℝ) (ε : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (a : α) : ℝ :=
  (volume (Set.Icc (0 : ι → ℝ) 1 ∩
    {u : ι → ℝ | fplLeader v (ε • ∑ s ∈ range t, ℓ s + u) = a})).toReal

theorem fplProb_nonneg (v : α → ι → ℝ) (ε : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (a : α) :
    0 ≤ fplProb v ε ℓ t a :=
  ENNReal.toReal_nonneg

theorem fplProb_congr (v : α → ι → ℝ) (ε : ℝ) {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, ℓ s = ℓ' s) :
    fplProb v ε ℓ t = fplProb v ε ℓ' t := by
  funext a
  simp only [fplProb, sum_congr rfl fun s hs => h s (mem_range.mp hs)]

theorem sum_fplProb (v : α → ι → ℝ) (ε : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ a : α, fplProb v ε ℓ t a = 1 :=
  (sum_volume_inter_fplLeader_toReal v (ε • ∑ s ∈ range t, ℓ s) isClosed_Icc.measurableSet
    (by rw [volume_unitIcc]; exact ENNReal.one_ne_top)).trans
    (by rw [volume_unitIcc, ENNReal.toReal_one])

omit [Fintype α] [Nonempty α] [LinearOrder α] in
/-- Volume of `Set.Icc (0 : ι → ℝ) 1 \ Set.Icc δ (1 + δ)` is at most `∑ i, |δ i|` (covered by `|ι|`
coordinate slabs each of volume `|δ i|`). -/
private theorem volume_Icc_diff_shift_le (δ : ι → ℝ) :
    volume (Set.Icc (0 : ι → ℝ) 1 \ Set.Icc δ (1 + δ)) ≤ ENNReal.ofReal (∑ i : ι, |δ i|) := by
  classical
  let slab (i : ι) : Set (ι → ℝ) :=
    if 0 ≤ δ i then Set.Icc 0 (fun j => if j = i then |δ i| else 1)
    else Set.Icc (fun j => if j = i then 1 - |δ i| else 0) 1
  have hsub : Set.Icc (0 : ι → ℝ) 1 \ Set.Icc δ (1 + δ) ⊆ ⋃ i ∈ (univ : Finset ι), slab i := by
    intro u ⟨hu01, hnot⟩
    have ⟨i, hi⟩ : ∃ i : ι, ¬ (δ i ≤ u i ∧ u i ≤ 1 + δ i) := by
      by_contra! hall; exact hnot ⟨fun i => (hall i).1, fun i => (hall i).2⟩
    refine Set.mem_iUnion₂.mpr ⟨i, mem_univ i, ?_⟩
    have h0i : 0 ≤ u i := hu01.1 i
    have h1i : u i ≤ 1 := hu01.2 i
    dsimp only [slab]
    by_cases hδi : 0 ≤ δ i
    · simp only [hδi, ↓reduceIte]
      refine ⟨hu01.1, fun j => ?_⟩
      by_cases hji : j = i
      · subst hji
        simp only [↓reduceIte, abs_of_nonneg hδi]
        by_contra! h; exact hi ⟨h.le, by linarith⟩
      · simp only [hji, ↓reduceIte]
        exact hu01.2 j
    · simp only [hδi, ↓reduceIte]
      refine ⟨fun j => ?_, hu01.2⟩
      by_cases hji : j = i
      · subst hji
        simp only [↓reduceIte, abs_of_neg (lt_of_not_ge hδi)]
        by_contra! h; exact hi ⟨by linarith, by linarith⟩
      · simp only [hji, ↓reduceIte]
        exact hu01.1 j
  have hslab_vol (i : ι) : volume (slab i) = ENNReal.ofReal |δ i| := by
    dsimp only [slab]
    by_cases hδi : 0 ≤ δ i
    · simp only [hδi, ↓reduceIte, Real.volume_Icc_pi, Pi.zero_apply, sub_zero]
      rw [← mul_prod_erase univ _ (mem_univ i),
        prod_eq_one fun x hx => by simp only [ne_of_mem_erase hx, ↓reduceIte, ENNReal.ofReal_one],
        mul_one, ite_eq_left rfl]
    · simp only [hδi, ↓reduceIte, Real.volume_Icc_pi, Pi.one_apply]
      rw [← mul_prod_erase univ _ (mem_univ i),
        prod_eq_one fun x hx => by
          simp only [ne_of_mem_erase hx, ↓reduceIte, sub_zero, ENNReal.ofReal_one],
        mul_one, ite_eq_left rfl, sub_sub_cancel]
  calc volume (Set.Icc (0 : ι → ℝ) 1 \ Set.Icc δ (1 + δ))
      ≤ volume (⋃ i ∈ (univ : Finset ι), slab i) := measure_mono hsub
    _ ≤ ∑ i ∈ (univ : Finset ι), volume (slab i) := measure_biUnion_finset_le univ slab
    _ = ∑ i : ι, ENNReal.ofReal |δ i| := sum_congr rfl fun i _ => hslab_vol i
    _ = ENNReal.ofReal (∑ i : ι, |δ i|) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _).symm

/-- Per-round stability of `fplProb`: if `v a ⬝ᵥ ℓ t - v b ⬝ᵥ ℓ t ≤ R` for all `a, b : α`, then
for `ε ≥ 0`,
`∑ a, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * (v a ⬝ᵥ ℓ t) ≤ ε * R * ∑ i, |ℓ t i|`. -/
theorem fpl_stability_step (v : α → ι → ℝ) {ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (ℓ : ℕ → ι → ℝ) (t : ℕ)
    (hspan : ∀ a b : α, v a ⬝ᵥ ℓ t - v b ⬝ᵥ ℓ t ≤ R) :
    ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * (v a ⬝ᵥ ℓ t) ≤
      ε * R * ∑ i : ι, |ℓ t i| := by
  classical
  set c₀ : ι → ℝ := ε • ∑ s ∈ range t, ℓ s
  set δ : ι → ℝ := ε • ℓ t
  let A (a : α) : Set (ι → ℝ) := {z | fplLeader v (c₀ + z) = a}
  have hA_meas : ∀ a, MeasurableSet (A a) := measurableSet_fplLeader_shift_eq v c₀
  set S := Set.Icc (0 : ι → ℝ) 1
  set S' := Set.Icc δ (1 + δ)
  have hprob_succ (a : α) : fplProb v ε ℓ (t + 1) a = (volume (S' ∩ A a)).toReal := by
    have hpre : S ∩ {u | fplLeader v (ε • ∑ s ∈ range (t + 1), ℓ s + u) = a} =
        (fun u i => u i + δ i) ⁻¹' (S' ∩ A a) := by
      have hc : ∀ u, ε • ∑ s ∈ range (t + 1), ℓ s + u = c₀ + fun j => u j + δ j := fun u => by
        rw [sum_range_succ, smul_add]
        ext i
        simp only [Pi.add_apply]
        ring
      ext u
      simp only [S, S', A, hc, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, Pi.le_def,
        Pi.zero_apply, Pi.one_apply, Pi.add_apply, Set.mem_ofPred_eq]
      constructor <;> rintro ⟨⟨h0, h1⟩, ha⟩ <;>
        exact ⟨⟨fun i => by linarith [h0 i], fun i => by linarith [h1 i]⟩, ha⟩
    unfold fplProb
    rw [hpre, (volume_preserving_pi fun i : ι =>
      measurePreserving_add_right volume (δ i)).measure_preimage
        (isClosed_Icc.measurableSet.inter (hA_meas a)).nullMeasurableSet]
  set m := univ.inf' univ_nonempty fun b : α => v b ⬝ᵥ ℓ t
  let h (a : α) : ℝ := v a ⬝ᵥ ℓ t - m
  have hh0 (a : α) : 0 ≤ h a := sub_nonneg.mpr (inf'_le (fun b => v b ⬝ᵥ ℓ t) (mem_univ a))
  have hhR (a : α) : h a ≤ R := by
    obtain ⟨b₀, _, hb₀⟩ := exists_mem_eq_inf' univ_nonempty (fun b : α => v b ⬝ᵥ ℓ t)
    dsimp only [h, m]
    rw [hb₀]
    exact hspan a b₀
  have hshift_m : ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * (v a ⬝ᵥ ℓ t) =
      ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * h a := by
    have h0 : ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * m = 0 := by
      rw [← sum_mul, sum_sub_distrib, sum_fplProb, sum_fplProb, sub_self, zero_mul]
    rw [← add_zero (∑ a, _ * h a), ← h0, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by dsimp only [h]; ring
  rw [hshift_m]
  have hS_fin : volume S ≠ ⊤ := by rw [volume_unitIcc]; exact ENNReal.one_ne_top
  have hS'_fin : volume S' ≠ ⊤ := by
    have hv : volume S' = 1 := by
      simp only [S', Real.volume_Icc_pi, Pi.add_apply, Pi.one_apply, add_sub_cancel_right,
        ENNReal.ofReal_one, prod_const_one]
    rw [hv]
    exact ENNReal.one_ne_top
  have hdiff_le (a : α) :
      fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a ≤ (volume ((S \ S') ∩ A a)).toReal := by
    rw [hprob_succ a]
    change (volume (S ∩ A a)).toReal - (volume (S' ∩ A a)).toReal ≤ _
    have hsplit : S ∩ A a = ((S ∩ S') ∩ A a) ∪ ((S \ S') ∩ A a) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
      tauto
    have hvol : volume (S ∩ A a) = volume ((S ∩ S') ∩ A a) + volume ((S \ S') ∩ A a) := by
      rw [hsplit]
      exact measure_union (Set.disjoint_left.mpr fun _ h1 h2 => h2.1.2 h1.1.2)
        ((isClosed_Icc.measurableSet.diff isClosed_Icc.measurableSet).inter (hA_meas a))
    have htoReal : (volume (S ∩ A a)).toReal =
        (volume ((S ∩ S') ∩ A a)).toReal + (volume ((S \ S') ∩ A a)).toReal := by
      rw [hvol, ENNReal.toReal_add
        (ne_top_of_le_ne_top hS_fin
          (measure_mono (Set.inter_subset_left.trans Set.inter_subset_left)))
        (ne_top_of_le_ne_top hS_fin
          (measure_mono (Set.inter_subset_left.trans Set.sdiff_subset)))]
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
        rw [sum_volume_inter_fplLeader_toReal v c₀
          (isClosed_Icc.measurableSet.diff isClosed_Icc.measurableSet)
          (ne_top_of_le_ne_top hS_fin (measure_mono Set.sdiff_subset))]
    _ ≤ (ENNReal.ofReal (∑ i : ι, |δ i|)).toReal * R :=
        mul_le_mul_of_nonneg_right
          (ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_Icc_diff_shift_le δ)) hR
    _ = (∑ i : ι, |δ i|) * R := by
        rw [ENNReal.toReal_ofReal (sum_nonneg fun i _ => abs_nonneg _)]
    _ = ε * R * ∑ i : ι, |ℓ t i| := by
        have hδ_sum : ∑ i : ι, |δ i| = ε * ∑ i : ι, |ℓ t i| := by
          rw [mul_sum]
          exact sum_congr rfl fun i _ => by
            simp only [δ, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hε]
        rw [hδ_sum]; ring

/-! ### Expected regret bounds -/

/-- **Follow-the-Perturbed-Leader expected regret bound**: suppose on the unit cube
`u ∈ Set.Icc (0 : ι → ℝ) 1` every pair `a, b` satisfies `v a ⬝ᵥ u - v b ⬝ᵥ u ≤ D` (for example
when `∑ i, |v a i - v b i| ≤ D`), and in every round `t < T` the cost vector `ℓ t` has decision
span `v a ⬝ᵥ ℓ t - v b ⬝ᵥ ℓ t ≤ R` and `L¹` norm `∑ i, |ℓ t i| ≤ A`. Then for every `ε > 0` and
comparator `a_star : α`, expected cost is at most
`∑ t ∈ range T, v a_star ⬝ᵥ ℓ t + D / ε + ε * (R * A * T)`. -/
theorem fpl_regret_le (v : α → ι → ℝ) {ε D R A : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hD : ∀ a b : α, ∀ u ∈ Set.Icc (0 : ι → ℝ) 1, v a ⬝ᵥ u - v b ⬝ᵥ u ≤ D)
    (hspan : ∀ t < T, ∀ a b : α, v a ⬝ᵥ ℓ t - v b ⬝ᵥ ℓ t ≤ R)
    (hl1 : ∀ t < T, ∑ i : ι, |ℓ t i| ≤ A)
    (a_star : α) :
    ∑ t ∈ range T, ∑ a : α, fplProb v ε ℓ t a * (v a ⬝ᵥ ℓ t) ≤
      ∑ t ∈ range T, (v a_star ⬝ᵥ ℓ t) + D / ε + ε * (R * A * T) := by
  classical
  let x (k : ℕ) (u : ι → ℝ) : α := fplLeader v (ε • ∑ s ∈ range k, ℓ s + u)
  let trajCell (w : Fin (T + 1) → α) : Set (ι → ℝ) :=
    Set.Icc (0 : ι → ℝ) 1 ∩ ⋂ k ∈ (univ : Finset (Fin (T + 1))), {u | x k.1 u = w k}
  have hcell_meas (w : Fin (T + 1) → α) : MeasurableSet (trajCell w) :=
    isClosed_Icc.measurableSet.inter (Finset.measurableSet_biInter _ fun k _ =>
      measurableSet_fplLeader_shift_eq v (ε • ∑ s ∈ range k.1, ℓ s) (w k))
  have hcell_disj : Pairwise fun w₁ w₂ => Disjoint (trajCell w₁) (trajCell w₂) :=
    fun _ _ hne => Set.disjoint_left.mpr fun _ h1 h2 => hne <| funext fun k =>
      (Set.mem_iInter₂.mp h1.2 k (mem_univ k)).symm.trans (Set.mem_iInter₂.mp h2.2 k (mem_univ k))
  have hcell_fin (w : Fin (T + 1) → α) : volume (trajCell w) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [volume_unitIcc]; exact ENNReal.one_ne_top)
      (measure_mono Set.inter_subset_left)
  let μw (w : Fin (T + 1) → α) : ℝ := (volume (trajCell w)).toReal
  have hmarg (k : Fin (T + 1)) (F : α → ℝ) :
      ∑ w : Fin (T + 1) → α, μw w * F (w k) = ∑ a : α, fplProb v ε ℓ k.1 a * F a := by
    have hprob_k (a : α) : fplProb v ε ℓ k.1 a = ∑ w with w k = a, μw w := by
      have hunion_a : Set.Icc (0 : ι → ℝ) 1 ∩ {u | x k.1 u = a} =
          ⋃ w ∈ univ.filter (fun w : Fin (T + 1) → α => w k = a), trajCell w := by
        ext u
        simp only [trajCell, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, mem_filter,
          mem_univ, true_and, Set.mem_iInter]
        exact ⟨fun ⟨hu, hxk⟩ => ⟨fun j => x j.1 u, hxk, hu, fun _ _ => rfl⟩,
          fun ⟨_, hwk, hu, hw⟩ => ⟨hu, (hw k trivial).trans hwk⟩⟩
      unfold fplProb
      change (volume (Set.Icc (0 : ι → ℝ) 1 ∩ {u | x k.1 u = a})).toReal = _
      rw [hunion_a, measure_biUnion_finset (fun _ _ _ _ hne => hcell_disj hne)
        (fun w _ => hcell_meas w), ENNReal.toReal_sum fun w _ => hcell_fin w]
    simp only [hprob_k, sum_mul]
    calc ∑ w : Fin (T + 1) → α, μw w * F (w k)
        = ∑ w : Fin (T + 1) → α, ∑ a : α, if w k = a then μw w * F a else 0 :=
          sum_congr rfl fun w _ => by simp only [sum_ite_eq, mem_univ, ↓reduceIte]
      _ = ∑ a : α, ∑ w : Fin (T + 1) → α, if w k = a then μw w * F a else 0 := sum_comm
      _ = ∑ a : α, ∑ w with w k = a, μw w * F a :=
          sum_congr rfl fun a _ => (sum_filter _ _).symm
  have hsum_μw : ∑ w : Fin (T + 1) → α, μw w = 1 := by
    simpa only [mul_one, Fin.val_zero, sum_fplProb] using hmarg 0 (fun _ => 1)
  have hcell_btl (w : Fin (T + 1) → α) :
      μw w * (∑ t : Fin T, (v (w t.castSucc) ⬝ᵥ ℓ t.1)) ≤
        μw w * (∑ t : Fin T, (v a_star ⬝ᵥ ℓ t.1) + D / ε +
          ∑ t : Fin T, (v (w t.castSucc) ⬝ᵥ ℓ t.1 - v (w t.succ) ⬝ᵥ ℓ t.1)) := by
    by_cases hzero : volume (trajCell w) = 0
    · simp only [μw, hzero, ENNReal.toReal_zero, zero_mul, le_refl]
    · obtain ⟨u, hu⟩ := nonempty_of_measure_ne_zero hzero
      have hxu (k : Fin (T + 1)) : x k.1 u = w k := Set.mem_iInter₂.mp hu.2 k (mem_univ k)
      refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      have hftrl := (isFTRL_fplLeader v hε ℓ u).regret_le_add_sum_sub (Set.mem_univ a_star) T
      change ∑ t ∈ range T, (v (x t u) ⬝ᵥ ℓ t - v a_star ⬝ᵥ ℓ t) ≤
        (1 / ε) * (v a_star ⬝ᵥ u) - (1 / ε) * (v (x 0 u) ⬝ᵥ u) +
          ∑ t ∈ range T, (v (x t u) ⬝ᵥ ℓ t - v (x (t + 1) u) ⬝ᵥ ℓ t) at hftrl
      rw [sum_sub_distrib, sum_range (fun t => v (x t u) ⬝ᵥ ℓ t),
        sum_range (fun t => v a_star ⬝ᵥ ℓ t),
        sum_range (fun t => v (x t u) ⬝ᵥ ℓ t - v (x (t + 1) u) ⬝ᵥ ℓ t)] at hftrl
      have hpert : (1 / ε) * (v a_star ⬝ᵥ u) - (1 / ε) * (v (x 0 u) ⬝ᵥ u) ≤ D / ε := by
        rw [← mul_sub, one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right (hD a_star (x 0 u) u hu.1) hε.le
      simp_rw [show ∀ t : Fin T, x t.1 u = w t.castSucc from fun t => hxu t.castSucc,
        show ∀ t : Fin T, x (t.1 + 1) u = w t.succ from fun t => hxu t.succ] at hftrl
      linarith
  have hsum_btl := sum_le_sum fun w (_ : w ∈ univ) => hcell_btl w
  have hlhs_eq : (∑ w : Fin (T + 1) → α, μw w * ∑ t : Fin T, (v (w t.castSucc) ⬝ᵥ ℓ t.1)) =
      ∑ t ∈ range T, ∑ a : α, fplProb v ε ℓ t a * (v a ⬝ᵥ ℓ t) := by
    simp_rw [mul_sum]; rw [sum_comm, sum_range]
    exact sum_congr rfl fun t _ => by
      simpa only [Fin.val_castSucc] using hmarg t.castSucc (fun a => v a ⬝ᵥ ℓ t.1)
  have hrhs_eq : (∑ w : Fin (T + 1) → α, μw w *
      (∑ t : Fin T, (v a_star ⬝ᵥ ℓ t.1) + D / ε +
        ∑ t : Fin T, (v (w t.castSucc) ⬝ᵥ ℓ t.1 - v (w t.succ) ⬝ᵥ ℓ t.1))) =
      ∑ t ∈ range T, (v a_star ⬝ᵥ ℓ t) + D / ε +
        ∑ t ∈ range T, ∑ a : α, (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) *
          (v a ⬝ᵥ ℓ t) := by
    simp only [mul_add, sum_add_distrib, ← sum_mul, hsum_μw, one_mul, sum_range]
    congr 1
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    simp only [mul_sub, sum_sub_distrib, sub_mul]
    rw [hmarg t.castSucc (fun a => v a ⬝ᵥ ℓ t.1),
      hmarg t.succ (fun a => v a ⬝ᵥ ℓ t.1), Fin.val_castSucc, Fin.val_succ]
  rw [hlhs_eq, hrhs_eq] at hsum_btl
  have hstab_sum : ∑ t ∈ range T, ∑ a : α,
      (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * (v a ⬝ᵥ ℓ t) ≤ ε * (R * A * T) := by
    calc ∑ t ∈ range T, ∑ a : α,
          (fplProb v ε ℓ t a - fplProb v ε ℓ (t + 1) a) * (v a ⬝ᵥ ℓ t)
        ≤ ∑ _t ∈ range T, (ε * R * A) := sum_le_sum fun t ht =>
          (fpl_stability_step v hε.le hR ℓ t (hspan t (mem_range.mp ht))).trans
            (mul_le_mul_of_nonneg_left (hl1 t (mem_range.mp ht)) (mul_nonneg hε.le hR))
      _ = ε * (R * A * T) := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  linarith

/-- **Tuned FPL expected regret `2 * √(D * (R * A * T))`**: setting `ε = √(D / (R * A * T))`
balances the perturbation and stability terms to `2 * √(D * (R * A * T))`. -/
theorem fpl_regret_le_sqrt (v : α → ι → ℝ) {D R A : ℝ} (hD_pos : 0 < D) (hR_pos : 0 < R)
    (hA_pos : 0 < A) {ℓ : ℕ → ι → ℝ} {T : ℕ} (hT : 0 < T)
    (hD : ∀ a b : α, ∀ u ∈ Set.Icc (0 : ι → ℝ) 1, v a ⬝ᵥ u - v b ⬝ᵥ u ≤ D)
    (hspan : ∀ t < T, ∀ a b : α, v a ⬝ᵥ ℓ t - v b ⬝ᵥ ℓ t ≤ R)
    (hl1 : ∀ t < T, ∑ i : ι, |ℓ t i| ≤ A)
    (a_star : α) :
    let ε := √(D / (R * A * T))
    ∑ t ∈ range T, ∑ a : α, fplProb v ε ℓ t a * (v a ⬝ᵥ ℓ t) ≤
      ∑ t ∈ range T, (v a_star ⬝ᵥ ℓ t) + 2 * √(D * (R * A * T)) := by
  intro ε
  set M := R * A * T
  have hM : 0 < M := by have : (0 : ℝ) < T := Nat.cast_pos.mpr hT; positivity
  refine (fpl_regret_le v (sqrt_pos.mpr (div_pos hD_pos hM))
    hR_pos.le hD hspan hl1 a_star).trans_eq ?_
  rw [add_assoc]
  congr 1
  change D / √(D / M) + √(D / M) * M = 2 * √(D * M)
  rw [add_comm]
  exact (Experts.sqrt_div_mul_add_div_sqrt_div hD_pos hM).trans (by rw [mul_comm M D])

end Leader

/-! ### Specialization to `N`-expert prediction -/

section ExpertsSpecialization

variable [Nonempty ι] [LinearOrder ι]

/-- Follow-the-Perturbed-Leader specialized to the `N`-expert setting, representing each expert
`a : ι` by its standard basis vector `Pi.single a 1`. -/
noncomputable def fplExpertsProb (ε : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (a : ι) : ℝ :=
  fplProb (fun a => Pi.single a 1) ε ℓ t a

theorem fplExpertsProb_def (ε : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    fplExpertsProb (ι := ι) ε ℓ t = fplProb (fun a => Pi.single a 1) ε ℓ t := by rfl

/-- `fplExpertsProb ε` is a causal online experts algorithm (`Experts.IsOnlineAlgorithm`). -/
theorem isOnlineAlgorithm_fplExpertsProb (ε : ℝ) :
    Experts.IsOnlineAlgorithm (fplExpertsProb (ι := ι) ε) where
  nonneg _ a := fplProb_nonneg _ ε _ _ a
  sum_eq_one _ := sum_fplProb _ ε _ _
  congr _ h := fplProb_congr _ ε h

/-- **FPL expected regret `2 * √(|ι| * T)` for `N` experts on `[0, 1]` losses**: on the standard
basis vectors `Pi.single a 1`, the one-sided cube span is `D = 1`, the stage span is `R = 1`, and
the `L¹` loss bound is `A = |ι|`, giving `2 * √(|ι| * T)` with `ε = √(1 / (|ι| * T))`. -/
theorem fpl_experts_regret_le_sqrt {ℓ : ℕ → ι → ℝ} {T : ℕ} (hT : 0 < T)
    (hℓ : ∀ t < T, ∀ i : ι, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (k : ι) :
    let ε := √(1 / ((Fintype.card ι : ℝ) * T))
    ∑ t ∈ range T, ∑ a : ι, fplExpertsProb ε ℓ t a * ℓ t a ≤
      ∑ t ∈ range T, ℓ t k + 2 * √((Fintype.card ι : ℝ) * T) := by
  intro ε
  have hD (a b : ι) (u : ι → ℝ) (hu : u ∈ Set.Icc (0 : ι → ℝ) 1) :
      Pi.single a (1 : ℝ) ⬝ᵥ u - Pi.single b (1 : ℝ) ⬝ᵥ u ≤ 1 := by
    simp only [single_dotProduct, one_mul]
    have hb0 : 0 ≤ u b := hu.1 b
    have ha1 : u a ≤ 1 := hu.2 a
    linarith
  have hspan (t : ℕ) (ht : t < T) (a b : ι) :
      Pi.single a (1 : ℝ) ⬝ᵥ ℓ t - Pi.single b (1 : ℝ) ⬝ᵥ ℓ t ≤ 1 := by
    simp only [single_dotProduct, one_mul]; linarith [(hℓ t ht b).1, (hℓ t ht a).2]
  have hl1 (t : ℕ) (ht : t < T) : ∑ i : ι, |ℓ t i| ≤ Fintype.card ι := by
    calc ∑ i : ι, |ℓ t i| ≤ ∑ _i : ι, (1 : ℝ) :=
          sum_le_sum fun i _ => by
            rw [abs_of_nonneg (hℓ t ht i).1]
            exact (hℓ t ht i).2
      _ = Fintype.card ι := by simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
  simpa only [one_mul, single_dotProduct, fplExpertsProb] using
    fpl_regret_le_sqrt (fun a : ι => Pi.single a (1 : ℝ)) zero_lt_one zero_lt_one
      (Nat.cast_pos.mpr Fintype.card_pos) hT hD hspan hl1 k

end ExpertsSpecialization

end Cslib.MachineLearning.OnlineLearning.FPL
