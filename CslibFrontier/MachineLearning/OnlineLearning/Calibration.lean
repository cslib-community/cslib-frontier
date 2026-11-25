/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.Blackwell
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Calibrated forecasting and the Foster–Vohra theorem

Formalizes **binary online calibration** via Blackwell approachability [Blackwell1956,
FosterVohra1998]:

1. **Deterministic impossibility** (`deterministic_calError_ge_half`): every *deterministic*
   forecaster `f : List Bool → ℝ` incurs exact `ℓ₁` calibration error at least `1 / 2` against an
   adaptive binary adversary (`y_t = decide (f h < 1 / 2)`) for every horizon `T ≥ 1`. Hence
   randomization is strictly required for asymptotic calibration.
2. **Calibration payoff and `ℓ₁` ball** (`calPayoff`, `l1Ball`): on the uniform grid
   `gridPoint K i = i / K ∈ [0, 1]` (`i : Fin (K + 1)`), round-`t` prediction `i` against outcome
   `b : Bool` incurs the vector payoff `(outcome b - i / K) • e_i ∈ EuclideanSpace ℝ (Fin (K + 1))`.
   Its cumulative vector average has `ℓ₁` norm equal to the classic empirical `ℓ₁` calibration
   error `(1 / T) * ∑ k, |∑_{i_t = k} (outcome b_t - gridPoint K k)|`.
3. **Response condition & explicit two-point Foster–Vohra strategy** (`calPayoff_response`,
   `fosterVohraRule`, `fosterVohraRule_halfspace`): verifies both Blackwell's response condition
   (`SatisfiesResponseCondition`) for the `ℓ₁` ball `l1Ball K (1 / (2 * K))` (by rounding to the
   nearest grid point) and an *explicit* closed-form 2-point-supported distribution
   `fosterVohraDist K w` satisfying the supporting halfspace condition directly (handling endpoints
   `w 0 ≤ 0`, `0 ≤ w K` and adjacent sign change `w i ≥ 0 ≥ w (i + 1)` with exact weight balance
   canceling `outcome b`).
4. **Finite-sample and `ε`–`δ` calibration bounds** (`fosterVohra_expected_calError_le`,
   `fosterVohra_prob_calError_ge_le`, `exists_calibrated_forecaster`): against *every* adaptive
   binary adversary `adv : List (Fin (K + 1)) → Bool`,
   * `𝔼[calError_T] ≤ 1 / (2 * K) + 2 * √((K + 1) / T)` (giving `O(T ^ (-1 / 3))` when
     `K ≈ T ^ (1 / 3)`), and
   * `Pr[calError_T ≥ ε] ≤ 4 * (K + 1) / (T * (ε - 1 / (2 * K)) ^ 2)` whenever `1 / (2 * K) < ε`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Blackwell.outcome`: binary outcome `{false ↦ 0, true ↦ 1}`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.detCalError`: bucketed `ℓ₁` empirical calibration
  error of a deterministic real-valued forecaster `f : List Bool → ℝ`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.gridPoint`: uniform grid point `i / K` in
  `[0, 1]`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.calPayoff`: vector payoff in
  `EuclideanSpace ℝ (Fin (K + 1))`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.l1Ball`: closed `ℓ₁` ball `{x | ∑ k, |x k| ≤ r}`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.fosterVohraDist`: explicit 2-point-supported
  forecast distribution given dual direction `w`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.fosterVohraRule`: stationary Blackwell
  `FeedbackRule` for calibrated forecasting on the `K`-grid.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.empiricalCalError`: realized `ℓ₁` calibration
  error `(h.length : ℝ)⁻¹ * ∑ k, |(sumPayoff (calPayoff K) adv h) k|`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Blackwell.deterministic_calError_ge_half`: every
  deterministic forecaster suffers calibration error at least `1 / 2`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.calPayoff_response`: `calPayoff K` satisfies
  `SatisfiesResponseCondition` for `l1Ball K (1 / (2 * K))`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.fosterVohra_expected_calError_le`:
  `𝔼[calError_T] ≤ 1 / (2 * K) + 2 * √((K + 1) / T)` against arbitrary adaptive adversaries.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.fosterVohra_prob_calError_ge_le`:
  Markov probability bound `Pr[calError_T ≥ ε] ≤ 4 * (K + 1) / (T * (ε - 1 / (2 * K)) ^ 2)`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.exists_calibrated_forecaster`: for all
  `ε, δ > 0`, explicit `K` and horizon `T₀` with `𝔼[calError_T] ≤ ε` and
  `Pr[calError_T ≥ ε] ≤ δ` for all `T ≥ T₀` [FosterVohra1998].

## References

* [D. Blackwell, *An analog of the minimax theorem for vector payoffs*][Blackwell1956]
* [D. P. Foster and R. V. Vohra, *Asymptotic calibration*][FosterVohra1998]
-/

public section

open Finset Real
open scoped RealInnerProductSpace

namespace Cslib.MachineLearning.OnlineLearning.Blackwell

/-- Binary outcome in `{0, 1} ⊆ ℝ`. -/
@[expose] def outcome (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem outcome_true : outcome true = 1 := rfl
@[simp] theorem outcome_false : outcome false = 0 := rfl

theorem outcome_mem_Icc (b : Bool) : outcome b ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> norm_num [outcome]

section DeterministicImpossibility

/-- Adversarial prefix history (most-recent-first) generated against a deterministic forecaster
`f : List Bool → ℝ` by playing the opposite extreme bit `decide (f h < 1 / 2)`. -/
@[expose] noncomputable def detAdversaryHistory (f : List Bool → ℝ) : ℕ → List Bool
  | 0 => []
  | t + 1 =>
    let h := detAdversaryHistory f t
    open Classical in decide (f h < 1 / 2) :: h

/-- Exact bucketed `ℓ₁` calibration error `(1 / T) * ∑ q, |∑_{p t = q} (outcome (y t) - q)|` over
all distinct real forecasts `q` issued during the first `T` rounds. -/
@[expose] noncomputable def detCalError (p : ℕ → ℝ) (y : ℕ → Bool) (T : ℕ) : ℝ :=
  open Classical in
  (T : ℝ)⁻¹ * ∑ q ∈ (range T).image p,
    |∑ t ∈ (range T).filter fun t => p t = q, (outcome (y t) - q)|

/-- **Deterministic forecasters cannot be calibrated** [FosterVohra1998]: for *every*
deterministic forecaster `f : List Bool → ℝ` and *every* horizon `T ≥ 1`, the adaptive adversary
playing `y t = true` iff `f h_t < 1 / 2` forces exact bucketed `ℓ₁` calibration error at least
`1 / 2`. -/
theorem deterministic_calError_ge_half (f : List Bool → ℝ) {T : ℕ} (hT : 0 < T) :
    let y : ℕ → Bool := fun t => open Classical in decide (f (detAdversaryHistory f t) < 1 / 2)
    let p : ℕ → ℝ := fun t => f (detAdversaryHistory f t)
    (1 / 2 : ℝ) ≤ detCalError p y T := by
  classical
  intro y p
  have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hbucket : ∀ q : ℝ,
      ((range T).filter fun t => p t = q).card * (1 / 2 : ℝ) ≤
        |∑ t ∈ (range T).filter fun t => p t = q, (outcome (y t) - q)| := by
    intro q
    -- On the bucket `p t = q` the adversary's bit is `decide (q < 1 / 2)`.
    rw [sum_congr rfl fun t ht => show outcome (y t) - q = outcome (decide (q < 1 / 2)) - q by
      obtain ⟨-, hpt⟩ := mem_filter.mp ht; subst hpt; rfl, sum_const, nsmul_eq_mul, abs_mul,
      Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    by_cases hq : q < 1 / 2
    · simp only [hq, decide_true, outcome_true]
      exact le_abs.mpr (Or.inl (by linarith))
    · simp only [hq, decide_false, outcome_false]
      exact le_abs.mpr (Or.inr (by linarith))
  have hcard : (T : ℝ) =
      ∑ q ∈ (range T).image p, (((range T).filter fun t => p t = q).card : ℝ) := by
    rw [← Nat.cast_sum, ← card_eq_sum_card_image, card_range]
  rw [detCalError, le_inv_mul_iff₀ hTpos, hcard, sum_mul]
  exact sum_le_sum fun q _ => hbucket q

end DeterministicImpossibility

section GridCalibration

/-- Uniform grid point `i / K ∈ [0, 1]` indexed by `i : Fin (K + 1)`. -/
@[expose] noncomputable def gridPoint (K : ℕ) (i : Fin (K + 1)) : ℝ :=
  (i : ℝ) / (K : ℝ)

theorem gridPoint_zero (K : ℕ) : gridPoint K 0 = 0 := by
  simp [gridPoint]

theorem gridPoint_last {K : ℕ} (hK : 0 < K) : gridPoint K (Fin.last K) = 1 := by
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  simp [gridPoint, div_self hKne]

theorem gridPoint_mem_Icc {K : ℕ} (hK : 0 < K) (i : Fin (K + 1)) :
    gridPoint K i ∈ Set.Icc (0 : ℝ) 1 := by
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  refine ⟨div_nonneg (Nat.cast_nonneg _) hKpos.le, (div_le_one hKpos).mpr ?_⟩
  exact_mod_cast Nat.le_of_lt_succ i.isLt

theorem gridPoint_succ_sub {K : ℕ} (i : Fin K) :
    gridPoint K i.succ - gridPoint K i.castSucc = 1 / (K : ℝ) := by
  simp only [gridPoint, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

/-- Vector-valued calibration payoff for grid size `K`: forecasting `i : Fin (K + 1)` when binary
outcome `b : Bool` occurs produces `(outcome b - gridPoint K i) • e_i`. -/
@[expose] noncomputable def calPayoff (K : ℕ) (i : Fin (K + 1)) (b : Bool) :
    EuclideanSpace ℝ (Fin (K + 1)) :=
  WithLp.toLp 2 fun k => if k = i then outcome b - gridPoint K i else 0

theorem norm_calPayoff_le_one {K : ℕ} (hK : 0 < K) (i : Fin (K + 1)) (b : Bool) :
    ‖calPayoff K i b‖ ≤ 1 := by
  have ho := outcome_mem_Icc b
  have hg := gridPoint_mem_Icc hK i
  refine le_of_pow_le_pow_left₀ two_ne_zero zero_le_one ?_
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply,
    Fintype.sum_eq_single i fun k hki => by simp [calPayoff, hki],
    show ⟪(calPayoff K i b) i, (calPayoff K i b) i⟫ = (outcome b - gridPoint K i) ^ 2 by
      simp [calPayoff, sq]]
  nlinarith [ho.1, ho.2, hg.1, hg.2]

/-- Closed `ℓ₁` ball `{x : EuclideanSpace ℝ (Fin n) | ∑ k, |x k| ≤ r}`. -/
@[expose] def l1Ball (n : ℕ) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∑ k : Fin n, |x k| ≤ r}

theorem zero_mem_l1Ball {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ l1Ball n r := by
  simpa [l1Ball] using hr

theorem l1Ball_convex (n : ℕ) (r : ℝ) : Convex ℝ (l1Ball n r) := by
  intro x hx y hy a b ha hb hab
  change ∑ k : Fin n, |(a • x + b • y) k| ≤ r
  calc ∑ k : Fin n, |(a • x + b • y) k|
      ≤ ∑ k : Fin n, (a * |x k| + b * |y k|) := by
        refine sum_le_sum fun k _ => ?_
        calc |(a • x + b • y) k|
            = |a * x k + b * y k| := rfl
          _ ≤ |a * x k| + |b * y k| := abs_add_le _ _
          _ = a * |x k| + b * |y k| := by
              rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * ∑ k : Fin n, |x k| + b * ∑ k : Fin n, |y k| := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ a * r + b * r := add_le_add (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
    _ = r := by rw [← add_mul, hab, one_mul]

theorem l1Ball_isComplete (n : ℕ) (r : ℝ) : IsComplete (l1Ball n r) := by
  have hclosed : IsClosed (l1Ball n r) :=
    isClosed_le (by
      have hterm : ∀ k : Fin n, Continuous (fun x : EuclideanSpace ℝ (Fin n) => |x k|) :=
        fun k => (EuclideanSpace.proj k).continuous.abs
      fun_prop) continuous_const
  exact hclosed.isComplete

/-- Elementary `ℓ₁`–`ℓ₂` Cauchy–Schwarz inequality on `EuclideanSpace ℝ (Fin n)`. -/
private theorem sum_abs_le_sqrt_mul_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ∑ k : Fin n, |x k| ≤ Real.sqrt n * ‖x‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) (fun k => |x k|)
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hcs
  have hsq : ∑ k : Fin n, |x k| ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    refine sum_congr rfl fun k _ => ?_
    rw [RCLike.inner_apply, conj_trivial, sq_abs, sq]
  rw [hsq] at hcs
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Triangle bound relating `∑ |x k|` to Euclidean distance `distToSet (l1Ball n r) x`. -/
theorem sum_abs_le_add_sqrt_mul_distToSet {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∑ k : Fin n, |x k| ≤ r + Real.sqrt n * distToSet (l1Ball n r) x := by
  set s := metricProjection (l1Ball n r) x
  have hs_mem : s ∈ l1Ball n r :=
    metricProjection_mem ⟨0, zero_mem_l1Ball hr⟩ (l1Ball_isComplete n r) (l1Ball_convex n r) x
  have htri : ∑ k : Fin n, |x k| ≤ ∑ k : Fin n, |s k| + ∑ k : Fin n, |(x - s) k| := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun k _ => by simpa using abs_add_le (s k) (x k - s k)
  have h1 : ∑ k : Fin n, |s k| ≤ r := hs_mem
  have hcs : ∑ k : Fin n, |(x - s) k| ≤ Real.sqrt n * distToSet (l1Ball n r) x :=
    sum_abs_le_sqrt_mul_norm (x - s)
  linarith

/-- Rounding any `μ ∈ [0, 1]` to the nearest grid point `i / K` gives error `≤ 1 / (2 * K)`. -/
private theorem exists_gridPoint_dist_le {K : ℕ} (hK : 0 < K) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ1 : μ ≤ 1) : ∃ i : Fin (K + 1), |μ - gridPoint K i| ≤ 1 / (2 * (K : ℝ)) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  set m : ℕ := min K ⌊μ * (K : ℝ) + 1 / 2⌋₊
  refine ⟨⟨m, Nat.lt_succ_of_le (min_le_left _ _)⟩, ?_⟩
  have hnn : 0 ≤ μ * (K : ℝ) + 1 / 2 := by positivity
  -- Rounding error at scale `K`: `|μ * K - m| ≤ 1 / 2`.
  have key : |μ * K - m| ≤ 1 / 2 := by
    rw [abs_le]
    rcases le_total ⌊μ * (K : ℝ) + 1 / 2⌋₊ K with hle | hle
    · rw [show m = ⌊μ * (K : ℝ) + 1 / 2⌋₊ from min_eq_right hle]
      constructor <;> linarith [Nat.floor_le hnn, Nat.lt_floor_add_one (μ * (K : ℝ) + 1 / 2)]
    · rw [show m = K from min_eq_left hle]
      have := (Nat.cast_le (α := ℝ)).mpr hle
      constructor <;> nlinarith [Nat.floor_le hnn]
  rw [gridPoint, show μ - (m : ℝ) / K = (μ * K - m) / K by field_simp, abs_div,
    abs_of_pos hKpos, div_le_div_iff₀ hKpos (by positivity)]
  nlinarith

/-- **Blackwell's response condition holds for binary calibration** (`calPayoff K` targeting
`l1Ball (K + 1) (1 / (2 * K))`): against any mixed outcome `q ∈ Δ(Bool)`, placing mass `1` on the
grid point nearest to `q true` keeps the expected vector payoff inside the `ℓ₁` ball of radius
`1 / (2 * K)`. -/
theorem calPayoff_response {K : ℕ} (hK : 0 < K) :
    SatisfiesResponseCondition (calPayoff K) (l1Ball (K + 1) (1 / (2 * (K : ℝ)))) := by
  intro q hq0 hq1
  have hsum : q true + q false = 1 := by simpa [Fintype.sum_bool] using hq1
  obtain ⟨i₀, hi₀⟩ := exists_gridPoint_dist_le hK (hq0 true) (by linarith [hq0 false])
  refine ⟨fun i => if i = i₀ then 1 else 0, fun i => by dsimp only; split_ifs <;> norm_num,
    by simp, ?_⟩
  change ∑ k : Fin (K + 1), |(bilinearPayoff (calPayoff K)
      (fun i => if i = i₀ then 1 else 0) q) k| ≤ 1 / (2 * (K : ℝ))
  have heval : ∀ k : Fin (K + 1),
      (bilinearPayoff (calPayoff K) (fun i => if i = i₀ then 1 else 0) q) k =
        if k = i₀ then q true - gridPoint K i₀ else 0 := by
    intro k
    simp only [bilinearPayoff, Fintype.sum_bool]
    rw [Fintype.sum_eq_single i₀ fun i hi => by simp [hi]]
    simp only [↓reduceIte, one_mul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, calPayoff,
      outcome_true, outcome_false]
    split_ifs
    · linear_combination (-gridPoint K i₀) * hsum
    · simp
  simp_rw [heval]
  rw [Fintype.sum_eq_single i₀ fun k hk => by simp [hk]]
  simpa using hi₀

/-- Discrete intermediate value lemma: if `w 0 > 0` and `w (Fin.last K) < 0`, there is an adjacent
pair `(i.castSucc, i.succ)` with `w i.castSucc > 0` and `w i.succ ≤ 0`. -/
private theorem exists_adjacent_sign_change {K : ℕ} (w : Fin (K + 1) → ℝ)
    (h0 : 0 < w 0) (hlast : w (Fin.last K) < 0) :
    ∃ i : Fin K, 0 < w i.castSucc ∧ w i.succ ≤ 0 := by
  by_contra hnone
  push Not at hnone
  have hpos : ∀ j : ℕ, (hj : j < K + 1) → 0 < w ⟨j, hj⟩ := by
    intro j hj
    induction j with
    | zero => exact h0
    | succ q ih =>
      have hq : q < K := Nat.lt_of_succ_lt_succ hj
      have ih' : 0 < w ⟨q, Nat.lt_trans hq (Nat.lt_succ_self K)⟩ := ih _
      exact hnone ⟨q, hq⟩ ih'
  have := hpos K (Nat.lt_succ_self K)
  exact absurd this (not_lt_of_ge hlast.le)

/-- Explicit 2-point-supported distribution on `Fin (K + 1)` forcing the `l1Ball` supporting
halfspace of `w : EuclideanSpace ℝ (Fin (K + 1))` against both binary outcomes `true, false`
[FosterVohra1998]. -/
noncomputable def fosterVohraDist (K : ℕ) (w : EuclideanSpace ℝ (Fin (K + 1))) :
    Fin (K + 1) → ℝ :=
  open Classical in
  if h0 : w 0 ≤ 0 then fun k => if k = 0 then 1 else 0
  else if hlast : 0 ≤ w (Fin.last K) then fun k => if k = Fin.last K then 1 else 0
  else
    let hi : ∃ i : Fin K, 0 < w i.castSucc ∧ w i.succ ≤ 0 :=
      exists_adjacent_sign_change w (lt_of_not_ge h0) (lt_of_not_ge hlast)
    let i := hi.choose
    let a := w i.castSucc
    let b := -w i.succ
    fun k =>
      if k = i.castSucc then b / (a + b)
      else if k = i.succ then a / (a + b)
      else 0

theorem fosterVohraDist_nonneg (K : ℕ) (w : EuclideanSpace ℝ (Fin (K + 1)))
    (k : Fin (K + 1)) : 0 ≤ fosterVohraDist K w k := by
  classical
  dsimp only [fosterVohraDist]
  by_cases h0 : w 0 ≤ 0
  · simp only [dite_eq_left h0]
    split_ifs <;> norm_num
  · by_cases hlast : 0 ≤ w (Fin.last K)
    · simp only [dite_eq_right h0, dite_eq_left hlast]
      split_ifs <;> norm_num
    · simp only [dite_eq_right h0, dite_eq_right hlast]
      have hspec :=
        (exists_adjacent_sign_change w (lt_of_not_ge h0) (lt_of_not_ge hlast)).choose_spec
      have ha : 0 < w _ := hspec.1
      have hb : 0 ≤ -w _ := neg_nonneg.mpr hspec.2
      split_ifs
      · exact div_nonneg hb (by linarith)
      · exact div_nonneg ha.le (by linarith)
      · exact le_rfl

theorem sum_fosterVohraDist (K : ℕ) (w : EuclideanSpace ℝ (Fin (K + 1))) :
    ∑ k : Fin (K + 1), fosterVohraDist K w k = 1 := by
  classical
  dsimp only [fosterVohraDist]
  by_cases h0 : w 0 ≤ 0
  · simp [dite_eq_left h0]
  · by_cases hlast : 0 ≤ w (Fin.last K)
    · simp [dite_eq_right h0, dite_eq_left hlast]
    · simp only [dite_eq_right h0, dite_eq_right hlast]
      set hex := exists_adjacent_sign_change w (lt_of_not_ge h0) (lt_of_not_ge hlast)
      set i := hex.choose
      have ha : 0 < w i.castSucc := hex.choose_spec.1
      have hb : 0 ≤ -w i.succ := neg_nonneg.mpr hex.choose_spec.2
      have hne : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
      rw [Fintype.sum_eq_add _ _ hne fun k hk => by simp [hk.1, hk.2]]
      simp only [↓reduceIte, hne.symm]
      rw [← add_div, add_comm (-w i.succ), div_self (by linarith)]

/-- **Core Foster–Vohra halfspace lemma**: for *every* dual vector `w`, `fosterVohraDist K w`
forces `⟪w, expectedPayoff (calPayoff K) (fosterVohraDist K w) b⟫ ≤ ⟪w, s*⟫` for an explicit
`s* ∈ l1Ball (K + 1) (1 / (2 * K))` against *both* binary outcomes `b : Bool`. -/
theorem fosterVohraDist_inner_le {K : ℕ} (hK : 0 < K)
    (w : EuclideanSpace ℝ (Fin (K + 1))) (b : Bool) :
    ∃ s : EuclideanSpace ℝ (Fin (K + 1)), s ∈ l1Ball (K + 1) (1 / (2 * (K : ℝ))) ∧
      ⟪w, expectedPayoff (calPayoff K) (fosterVohraDist K w) b⟫ ≤ ⟪w, s⟫ := by
  classical
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hrnn : 0 ≤ 1 / (2 * (K : ℝ)) := by positivity
  have hexp_eval : ∀ (p : Fin (K + 1) → ℝ) (y : Bool),
      ⟪w, expectedPayoff (calPayoff K) p y⟫ =
        ∑ k : Fin (K + 1), w k * p k * (outcome y - gridPoint K k) := by
    intro p y
    rw [expectedPayoff, inner_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_right, PiLp.inner_apply,
      Fintype.sum_eq_single k fun j hjk => by simp [calPayoff, hjk]]
    simp only [calPayoff, WithLp.ofLp_toLp, ↓reduceIte, RCLike.inner_apply, conj_trivial]
    ring
  by_cases h0 : w 0 ≤ 0
  · refine ⟨0, zero_mem_l1Ball hrnn, ?_⟩
    rw [inner_zero_right, hexp_eval]
    simpa [fosterVohraDist, h0, gridPoint_zero] using
      mul_nonpos_of_nonpos_of_nonneg h0 (outcome_mem_Icc b).1
  · by_cases hlast : 0 ≤ w (Fin.last K)
    · refine ⟨0, zero_mem_l1Ball hrnn, ?_⟩
      rw [inner_zero_right, hexp_eval]
      simpa [fosterVohraDist, h0, hlast, gridPoint_last hK] using
        mul_nonpos_of_nonneg_of_nonpos hlast (sub_nonpos.mpr (outcome_mem_Icc b).2)
    · set hex := exists_adjacent_sign_change w (lt_of_not_ge h0) (lt_of_not_ge hlast)
      set i := hex.choose
      set a : ℝ := w i.castSucc
      set c : ℝ := -w i.succ
      have ha : 0 < a := hex.choose_spec.1
      have hc : 0 ≤ c := neg_nonneg.mpr hex.choose_spec.2
      have hac : 0 < a + c := by linarith
      have hne : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
      have hp_eq : ∀ k, fosterVohraDist K w k =
          if k = i.castSucc then c / (a + c) else if k = i.succ then a / (a + c) else 0 := by
        intro k
        simp only [fosterVohraDist, dite_eq_right h0, dite_eq_right hlast]
        rfl
      have hinner_eq :
          ⟪w, expectedPayoff (calPayoff K) (fosterVohraDist K w) b⟫ =
            a * c / (a + c) / (K : ℝ) := by
        rw [hexp_eval]
        simp_rw [hp_eq]
        rw [Fintype.sum_eq_add _ _ hne fun k hk => by simp [hk.1, hk.2]]
        simp only [↓reduceIte, hne.symm]
        rw [show w i.succ = -c by simp [c]]
        linear_combination (a * c / (a + c)) * gridPoint_succ_sub i
      have ham : a * c / (a + c) ≤ max a c / 2 := by
        rw [div_le_div_iff₀ hac two_pos]
        rcases le_total a c with h | h
        · rw [max_eq_right h]; nlinarith
        · rw [max_eq_left h]; nlinarith
      have hbasis : ∀ (j : Fin (K + 1)) (sgn : ℝ), |sgn| = 1 →
          let e : EuclideanSpace ℝ (Fin (K + 1)) :=
            WithLp.toLp 2 fun k => if k = j then sgn * (1 / (2 * (K : ℝ))) else 0
          e ∈ l1Ball (K + 1) (1 / (2 * (K : ℝ))) ∧
            ⟪w, e⟫ = sgn * w j / (2 * (K : ℝ)) := by
        intro j sgn hsgn e
        refine ⟨?_, ?_⟩
        · change ∑ k : Fin (K + 1), |(if k = j then sgn * (1 / (2 * (K : ℝ))) else 0 : ℝ)| ≤
              1 / (2 * (K : ℝ))
          rw [Fintype.sum_eq_single j fun k hk => by simp [hk]]
          simp [abs_mul, hsgn]
        · rw [PiLp.inner_apply, Fintype.sum_eq_single j fun k hk => by simp [e, hk]]
          simp only [e, ↓reduceIte, RCLike.inner_apply, conj_trivial]
          ring
      rcases le_total a c with h | h
      · obtain ⟨hm, hi⟩ := hbasis i.succ (-1) (by norm_num)
        rw [max_eq_right h] at ham
        exact ⟨_, hm, hinner_eq.trans_le ((div_le_div_of_nonneg_right ham hKpos.le).trans_eq
          (by simp only [hi, c]; ring))⟩
      · obtain ⟨hm, hi⟩ := hbasis i.castSucc 1 (by norm_num)
        rw [max_eq_left h] at ham
        exact ⟨_, hm, hinner_eq.trans_le ((div_le_div_of_nonneg_right ham hKpos.le).trans_eq
          (by simp only [hi, a]; ring))⟩

/-- Explicit stationary **Foster–Vohra feedback rule** targeting `l1Ball (K + 1) (1 / (2 * K))`:
given current realized average error vector `y`, returns `fosterVohraDist K (y - Π_S y)`. -/
@[expose] noncomputable def fosterVohraRule (K : ℕ) :
    FeedbackRule (Fin (K + 1)) (EuclideanSpace ℝ (Fin (K + 1))) where
  prob y := fosterVohraDist K (y - metricProjection (l1Ball (K + 1) (1 / (2 * (K : ℝ)))) y)
  nonneg _ k := fosterVohraDist_nonneg K _ k
  sum_eq_one _ := sum_fosterVohraDist K _

/-- `fosterVohraRule K` satisfies Blackwell's supporting-halfspace inequality for every `y` and
every binary outcome `b : Bool`. -/
theorem fosterVohraRule_halfspace {K : ℕ} (hK : 0 < K)
    (y : EuclideanSpace ℝ (Fin (K + 1))) (b : Bool) :
    let S := l1Ball (K + 1) (1 / (2 * (K : ℝ)))
    let s := metricProjection S y
    ⟪y - s, expectedPayoff (calPayoff K) ((fosterVohraRule K).prob y) b - s⟫ ≤ 0 := by
  set S := l1Ball (K + 1) (1 / (2 * (K : ℝ)))
  set s := metricProjection S y
  obtain ⟨s', hs'_mem, hs'_le⟩ := fosterVohraDist_inner_le hK (y - s) b
  have hvar := inner_sub_metricProjection_le_zero (l1Ball_isComplete (K + 1) _)
    (l1Ball_convex (K + 1) _) y hs'_mem
  dsimp only
  rw [inner_sub_right] at hvar ⊢
  change ⟪y - s, expectedPayoff (calPayoff K) (fosterVohraDist K (y - s)) b⟫ - ⟪y - s, s⟫ ≤ 0
  linarith

/-- Realized `ℓ₁` **empirical calibration error** along a reverse-ordered history
`h : List (Fin (K + 1))` against an adaptive binary adversary `adv : List (Fin (K + 1)) → Bool`:
`(1 / |h|) * ∑ k, |∑_{i_t = k} (outcome (y_t) - k / K)|`. -/
@[expose] noncomputable def empiricalCalError (K : ℕ) (adv : List (Fin (K + 1)) → Bool)
    (h : List (Fin (K + 1))) : ℝ :=
  ∑ k : Fin (K + 1), |((h.length : ℝ)⁻¹ • sumPayoff (calPayoff K) adv h) k|

theorem empiricalCalError_nonneg (K : ℕ) (adv : List (Fin (K + 1)) → Bool)
    (h : List (Fin (K + 1))) : 0 ≤ empiricalCalError K adv h :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- **Foster–Vohra finite-sample expected `ℓ₁` calibration bound** [FosterVohra1998]:
for every grid size `K ≥ 1`, horizon `T ≥ 1`, and *arbitrary adaptive binary adversary*
`adv : List (Fin (K + 1)) → Bool`, the explicit two-point-supported `fosterVohraRule K` achieves
`𝔼[empiricalCalError K adv h] ≤ 1 / (2 * K) + 2 * √((K + 1) / T)`. -/
theorem fosterVohra_expected_calError_le {K : ℕ} (hK : 0 < K)
    (adv : List (Fin (K + 1)) → Bool) {T : ℕ} (hT : 0 < T) :
    expectHistory ((fosterVohraRule K).toStrategy (calPayoff K) adv) T []
        (empiricalCalError K adv) ≤
      1 / (2 * (K : ℝ)) + 2 * Real.sqrt (((K + 1 : ℕ) : ℝ) / (T : ℝ)) := by
  have hrnn : 0 ≤ 1 / (2 * (K : ℝ)) := by positivity
  set S := l1Ball (K + 1) (1 / (2 * (K : ℝ)))
  set strat := (fosterVohraRule K).toStrategy (calPayoff K) adv
  have hbound := expectHistory_mono strat (t := T) (h := [])
    (f := empiricalCalError K adv)
    (g := fun h => 1 / (2 * (K : ℝ)) +
      Real.sqrt (K + 1 : ℕ) * distToSet S ((T : ℝ)⁻¹ • sumPayoff (calPayoff K) adv h))
    fun h hh => by
      rw [empiricalCalError, show h.length = T by simpa using hh]
      exact sum_abs_le_add_sqrt_mul_distToSet hrnn _
  rw [expectHistory_add, expectHistory_const, expectHistory_smul] at hbound
  have hdist := blackwell_expect_dist_le (l1Ball_isComplete (K + 1) _) (l1Ball_convex (K + 1) _)
    (zero_mem_l1Ball hrnn) (calPayoff K) zero_le_one
    (fun i b => by simpa using norm_calPayoff_le_one hK i b)
    strat adv (fun h _ => fosterVohraRule_halfspace hK _ (adv h)) T hT
  have hmul := mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg (K + 1 : ℕ))
  have hre : Real.sqrt (K + 1 : ℕ) * (2 * 1 / Real.sqrt T) =
      2 * Real.sqrt (((K + 1 : ℕ) : ℝ) / (T : ℝ)) := by
    rw [Real.sqrt_div (Nat.cast_nonneg _)]; ring
  linarith

/-- **Foster–Vohra high-probability calibration tail bound** [FosterVohra1998]: whenever `ε`
exceeds the grid discretization `1 / (2 * K)`, for every adaptive binary adversary `adv` and
horizon `T ≥ 1`,
`Pr[empiricalCalError K adv h ≥ ε] ≤ 4 * (K + 1) / (T * (ε - 1 / (2 * K)) ^ 2)`. -/
theorem fosterVohra_prob_calError_ge_le {K : ℕ} (hK : 0 < K)
    (adv : List (Fin (K + 1)) → Bool) {T : ℕ} (hT : 0 < T) {ε : ℝ}
    (hε : 1 / (2 * (K : ℝ)) < ε) :
    expectHistory ((fosterVohraRule K).toStrategy (calPayoff K) adv) T []
        (fun h => if ε ≤ empiricalCalError K adv h then (1 : ℝ) else 0) ≤
      4 * ((K + 1 : ℕ) : ℝ) / ((T : ℝ) * (ε - 1 / (2 * (K : ℝ))) ^ 2) := by
  have hrnn : 0 ≤ 1 / (2 * (K : ℝ)) := by positivity
  set S := l1Ball (K + 1) (1 / (2 * (K : ℝ)))
  set strat := (fosterVohraRule K).toStrategy (calPayoff K) adv
  set gap : ℝ := ε - 1 / (2 * (K : ℝ))
  have hgap : 0 < gap := sub_pos.mpr hε
  have hK1pos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos K)
  set η : ℝ := gap / Real.sqrt ((K + 1 : ℕ) : ℝ)
  have hη : 0 < η := div_pos hgap (Real.sqrt_pos.mpr hK1pos)
  have hdom : expectHistory strat T []
      (fun h => if ε ≤ empiricalCalError K adv h then (1 : ℝ) else 0) ≤
      expectHistory strat T [] (fun h =>
        if η ≤ distToSet S ((T : ℝ)⁻¹ • sumPayoff (calPayoff K) adv h) then 1 else 0) := by
    refine expectHistory_mono strat fun h hh => ?_
    have hlen : h.length = T := by simpa using hh
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      have htri : empiricalCalError K adv h ≤
          1 / (2 * (K : ℝ)) + Real.sqrt (K + 1 : ℕ) *
            distToSet S ((T : ℝ)⁻¹ • sumPayoff (calPayoff K) adv h) := by
        rw [empiricalCalError, hlen]
        exact sum_abs_le_add_sqrt_mul_distToSet hrnn _
      have hlt : distToSet S ((T : ℝ)⁻¹ • sumPayoff (calPayoff K) adv h) < η := lt_of_not_ge h2
      have hmul : Real.sqrt (K + 1 : ℕ) *
          distToSet S ((T : ℝ)⁻¹ • sumPayoff (calPayoff K) adv h) < gap := by
        have hpos : 0 < Real.sqrt ((K + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hK1pos
        calc Real.sqrt (K + 1 : ℕ) *
              distToSet S ((T : ℝ)⁻¹ • sumPayoff (calPayoff K) adv h)
            < Real.sqrt (K + 1 : ℕ) * (gap / Real.sqrt (K + 1 : ℕ)) :=
              mul_lt_mul_of_pos_left hlt hpos
          _ = gap := mul_div_cancel₀ _ hpos.ne'
      linarith
    · exact zero_le_one
    · exact le_rfl
  have hprob := blackwell_prob_dist_ge_le (l1Ball_isComplete (K + 1) _) (l1Ball_convex (K + 1) _)
    (zero_mem_l1Ball hrnn) (calPayoff K) zero_le_one
    (fun i b => by simpa using norm_calPayoff_le_one hK i b)
    strat adv (fun h _ => fosterVohraRule_halfspace hK _ (adv h)) T hT hη
  refine (hdom.trans hprob).trans_eq ?_
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hgne : gap ≠ 0 := hgap.ne'
  simp only [η, div_pow, Real.sq_sqrt hK1pos.le]
  field_simp
  ring

/-- **Existence of `(ε, δ)`-calibrated randomized forecasters** [FosterVohra1998]:
for every `ε > 0` and `δ > 0`, there exist an explicit grid resolution `K ≥ 1` and horizon
`T₀ ≥ 1` (`K = ⌈2 / ε⌉₊`, `T₀ = O(K / (δ * ε ^ 2))`) such that `fosterVohraRule K` achieves
both `𝔼[empiricalCalError K adv h] ≤ ε` and `Pr[empiricalCalError K adv h ≥ ε] ≤ δ` for *all*
`T ≥ T₀` and *every* adaptive binary adversary `adv`. -/
theorem exists_calibrated_forecaster {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (K T₀ : ℕ), 0 < K ∧ 0 < T₀ ∧
      ∀ (T : ℕ), T₀ ≤ T → ∀ (adv : List (Fin (K + 1)) → Bool),
        expectHistory ((fosterVohraRule K).toStrategy (calPayoff K) adv) T []
            (empiricalCalError K adv) ≤ ε ∧
        expectHistory ((fosterVohraRule K).toStrategy (calPayoff K) adv) T []
            (fun h => if ε ≤ empiricalCalError K adv h then (1 : ℝ) else 0) ≤ δ := by
  let K : ℕ := ⌈2 / ε⌉₊
  have hK : 0 < K := Nat.ceil_pos.mpr (by positivity)
  have hK_ge : 2 / ε ≤ (K : ℝ) := Nat.le_ceil _
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hgrid : 1 / (2 * (K : ℝ)) ≤ ε / 4 := by
    have h1 : 2 ≤ (K : ℝ) * ε := (div_le_iff₀ hε).mp hK_ge
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hgrid_lt : 1 / (2 * (K : ℝ)) < ε := by linarith
  let T₀ : ℕ := max ⌈16 * ((K + 1 : ℕ) : ℝ) / ε ^ 2⌉₊
    ⌈16 * ((K + 1 : ℕ) : ℝ) / (δ * ε ^ 2)⌉₊
  have hK1pos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos K)
  have hT₀ : 0 < T₀ := lt_of_lt_of_le (Nat.ceil_pos.mpr (by positivity)) (le_max_left _ _)
  refine ⟨K, T₀, hK, hT₀, fun T hT adv => ?_⟩
  have hTpos : 0 < T := lt_of_lt_of_le hT₀ hT
  have hTr : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hTpos
  refine ⟨?_, ?_⟩
  · have hT_bd : 16 * ((K + 1 : ℕ) : ℝ) / ε ^ 2 ≤ (T : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_left _ _).trans hT))
    have hsqrt : Real.sqrt (((K + 1 : ℕ) : ℝ) / (T : ℝ)) ≤ ε / 4 := by
      rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hTr]
      have hmul := (div_le_iff₀ (sq_pos_of_pos hε)).mp hT_bd
      nlinarith
    linarith [fosterVohra_expected_calError_le hK adv hTpos]
  · have hT_bd : 16 * ((K + 1 : ℕ) : ℝ) / (δ * ε ^ 2) ≤ (T : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hT))
    have hgap : (3 / 4 : ℝ) * ε ≤ ε - 1 / (2 * (K : ℝ)) := by linarith
    have hgap_sq : (9 / 16 : ℝ) * ε ^ 2 ≤ (ε - 1 / (2 * (K : ℝ))) ^ 2 := by
      nlinarith [pow_le_pow_left₀ (by positivity : 0 ≤ (3 / 4 : ℝ) * ε) hgap 2]
    refine (fosterVohra_prob_calError_ge_le hK adv hTpos hgrid_lt).trans
      ((div_le_iff₀ (mul_pos hTr (sq_pos_of_pos (sub_pos.mpr hgrid_lt)))).mpr ?_)
    have hmul := (div_le_iff₀ (mul_pos hδ (sq_pos_of_pos hε))).mp hT_bd
    nlinarith [mul_le_mul_of_nonneg_left hgap_sq (by positivity : 0 ≤ δ * (T : ℝ))]

end GridCalibration

end Cslib.MachineLearning.OnlineLearning.Blackwell
