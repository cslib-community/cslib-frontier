/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Foundations.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.MachineLearning.OnlineLearning.AdaGrad
import CslibFrontier.MachineLearning.OnlineLearning.DynamicRegret
import CslibFrontier.MachineLearning.OnlineLearning.OCOLowerBound
import CslibFrontier.MachineLearning.OnlineLearning.OnlineMirrorDescent
import CslibFrontier.Probability.BitString.Rademacher
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.privateModule false

/-!
# Checked tests for online convex optimization extensions

Ordinary-import client checks (no `import all`) exercising all four new online convex optimization
modules on non-vacuous concrete instances plus negative / boundary checks:

1. **Dynamic regret (`DynamicRegret`)**: `pathLength` on a switching sequence and a constant
   sequence, plus instantiations of `ogd_dynamic_regret_le_fixed`, `ogd_dynamic_regret_le_tuned`,
   `ogd_dynamic_regret_le_three_halves`, and `ogd_dynamic_regret_le_zinkevich` on `K = [-1, 1]`.
2. **Adaptive OGD (`AdaGrad`)**: `clampProj` values and non-Pythagorean counterexample,
   `sum_div_sqrt_cumsum_le` at `ε = 0` with a zero prefix, `adaGradNorm_regret_le_optimal`,
   `adaGradNorm_regret_le_sqrt`, and diagonal `adaGradBox_regret_le_optimal` on `Fin 2 → ℝ`
   illustrating strict slack `√S₀ < √(2 * S₀)` on sparse gradients.
3. **Online mirror descent (`OnlineMirrorDescent`)**: Euclidean `bregmanDiv_sq_norm_half`,
   three-point identity, `isOMDStep_metricProjection_euclidean`, a negative check showing a
   non-convex generator (`ψ x = -x ^ 2`) yields a negative Bregman divergence, and instantiations
   of `omd_regret_le_const`, `omd_regret_le_tuned`, and `omd_regret_le_sqrt`.
4. **Minimax lower bound (`OCOLowerBound`)**: Rademacher moments at `T = 2` via
   `Cslib.BitString`, `khintchine_rademacher_abs_sum`, and matching instantiations of BOTH
   `exists_oco_regret_ge` (`Ω(D * G * √T)`) — on a generic `CausalLearner`, the constant zero
   learner `constZeroLearner`, and an adaptive `ogdCausalLearner` — and
   `OnlineGradientDescent.ogd_regret_le_fixed` (`O(D * G * √T)`) on the same Rademacher linear
   loss family over `K = [-1, 1] ⊆ ℝ`.
-/

namespace CslibFrontierTests.OnlineConvexOpt

open Finset Real Set Cslib Cslib.BitString Cslib.MachineLearning.OnlineLearning.OCO
open scoped RealInnerProductSpace BigOperators

/-- The decision set `[-1, 1] ⊆ ℝ`. -/
private abbrev K : Set ℝ := Icc (-1) 1

private theorem K_nonempty : K.Nonempty := ⟨0, by norm_num⟩

private theorem K_isComplete : IsComplete K := isClosed_Icc.isComplete

private theorem K_convex : Convex ℝ K := convex_Icc _ _

private theorem real_inner_eq (a b : ℝ) : ⟪a, b⟫ = a * b := by
  rw [RCLike.inner_apply, conj_trivial, mul_comm]

private theorem K_diam : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ 2 := fun x hx y hy => by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

private theorem K_proj : IsPythagoreanProjection K (clampProj (-1) 1) :=
  isPythagoreanProjection_clampProj (by norm_num)

/-! ### Dynamic regret (`DynamicRegret`) -/

/-- Alternating comparator `0, 1, 0, 1, …` has path length `2` over 3 rounds. -/
private def switchSeq (t : ℕ) : ℝ := if t % 2 = 0 then 0 else 1

private theorem pathLength_switchSeq_three : pathLength switchSeq 3 = 2 := by
  simp only [pathLength, Nat.reduceSub, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add, switchSeq, Real.norm_eq_abs]
  norm_num

example : pathLength switchSeq 3 = 2 := pathLength_switchSeq_three

example : pathLength (fun _ : ℕ => (1 : ℝ)) 5 = 0 :=
  pathLength_const 1 5

/-- Fixed-step-size dynamic regret for linear losses on `[-1, 1]` with `D = 2`, `G = 1`. -/
example (c : ℕ → ℝ) (hc : ∀ t, |c t| ≤ 1) (u : ℕ → ℝ) (hu : ∀ t, u t ∈ K)
    {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T,
        (c t * ogd (clampProj (-1) 1) (fun _ => 2 / (1 * √(T : ℝ)))
            (fun t _ => c t) 0 t - c t * u t) ≤
      1 * (2 + pathLength u T) * √(T : ℝ) :=
  ogd_dynamic_regret_le_fixed (f := fun t x => c t * x) K_proj (by norm_num) two_pos one_pos
    K_diam (fun t _ _ => by rw [Real.norm_eq_abs]; exact hc t)
    (fun t x _ y _ => le_of_eq (by rw [real_inner_eq]; ring)) hu hT

/-- Tuned dynamic regret on `[-1, 1]` against `switchSeq` over `T = 3` (`P = 2`). -/
example (c : ℕ → ℝ) (hc : ∀ t, |c t| ≤ 1) :
    ∑ t ∈ range 3,
        (c t * ogd (clampProj (-1) 1)
            (fun _ => √(2 ^ 2 + 2 * 2 * 2) / (1 * √(3 : ℝ))) (fun t _ => c t) 0 t -
          c t * switchSeq t) ≤
      1 * √((3 : ℝ) * (2 ^ 2 + 2 * 2 * 2)) :=
  ogd_dynamic_regret_le_tuned (f := fun t x => c t * x) K_proj (by norm_num) two_pos one_pos
    K_diam (fun t _ _ => by rw [Real.norm_eq_abs]; exact hc t)
    (fun t x _ y _ => le_of_eq (by rw [real_inner_eq]; ring))
    (u := switchSeq) (fun t => by dsimp [switchSeq]; split_ifs <;> norm_num)
    (by decide) pathLength_switchSeq_three.le

/-- Horizon-independent `3/2`-constant dynamic regret on `[-1, 1]`. -/
example (c : ℕ → ℝ) (hc : ∀ t, |c t| ≤ 1) (u : ℕ → ℝ) (hu : ∀ t, u t ∈ K) (T : ℕ) :
    ∑ t ∈ range T,
        (c t * ogd (clampProj (-1) 1) (fun t => 2 / (1 * √((t : ℝ) + 1)))
            (fun t _ => c t) 0 t - c t * u t) ≤
      (3 / 2 * 2 + pathLength u T) * 1 * √(T : ℝ) :=
  ogd_dynamic_regret_le_three_halves (f := fun t x => c t * x) K_proj (by norm_num) two_pos
    one_pos K_diam (fun t _ _ => by rw [Real.norm_eq_abs]; exact hc t)
    (fun t x _ y _ => le_of_eq (by rw [real_inner_eq]; ring)) hu T

/-- Zinkevich's `1 / √(t + 1)` dynamic regret on `[-1, 1]`. -/
example (c : ℕ → ℝ) (hc : ∀ t, |c t| ≤ 1) (u : ℕ → ℝ) (hu : ∀ t, u t ∈ K)
    {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T,
        (c t * ogd (clampProj (-1) 1) (fun t => 1 / √((t : ℝ) + 1))
            (fun t _ => c t) 0 t - c t * u t) ≤
      (2 ^ 2 / 2 + 2 * pathLength u T) * √(T : ℝ) + (√(T : ℝ) - 1 / 2) * 1 ^ 2 :=
  ogd_dynamic_regret_le_zinkevich (f := fun t x => c t * x) K_proj (by norm_num) K_diam
    (fun t _ _ => by rw [Real.norm_eq_abs]; exact hc t)
    (fun t x _ y _ => le_of_eq (by rw [real_inner_eq]; ring)) hu hT

/-! ### Adaptive OGD (`AdaGrad`) -/

example : clampProj (-1) 1 3 = 1 := by simp [clampProj]
example : clampProj (-1) 1 (-5) = -1 := by simp [clampProj]
example : clampProj (-1) 1 (1 / 2) = 1 / 2 := by
  simp only [clampProj]; norm_num

/-- Negative check: `id` is not a Pythagorean projection onto `[0, 1]`. -/
example : ¬ IsPythagoreanProjection (Icc (0 : ℝ) 1) id := fun h => by
  have := h.mem 2
  norm_num at this

/-- Boundary check: `sum_div_sqrt_cumsum_le` holds at `ε = 0` even with a zero prefix. -/
example :
    let a : ℕ → ℝ := fun t => if t = 0 then 0 else 1
    ∑ t ∈ range 3, a t / √(0 + ∑ s ∈ range (t + 1), a s) ≤
      2 * (√(0 + ∑ t ∈ range 3, a t) - √0) :=
  sum_div_sqrt_cumsum_le (a := fun t => if t = 0 then 0 else 1)
    (fun t => by split_ifs <;> norm_num) le_rfl 3

/-- Scalar `AdaGrad-Norm` with optimal scale `γ = D / √2 = 2 / √2` on `[-1, 1]`. -/
example (c : ℕ → ℝ) (hc : ∀ t, |c t| ≤ 1) {u : ℝ} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T,
        (c t * adaGradNorm (clampProj (-1) 1) (fun t _ => c t) (2 / √2) 0 0 t - c t * u) ≤
      √2 * 1 * 2 * √(T : ℝ) :=
  adaGradNorm_regret_le_sqrt (f := fun t x => c t * x) K_proj (by norm_num) two_pos
    zero_le_one K_diam (fun t _ _ => by rw [Real.norm_eq_abs]; exact hc t)
    (fun t x _ y _ => le_of_eq (by rw [real_inner_eq]; ring)) hu T

/-- Optimal diagonal `AdaGrad` on the `2`-dimensional box `[-1, 1]^2` for sparse linear losses
supported only on coordinate `0` beats the isotropic factor `√2`. -/
example (T : ℕ) {u : Fin 2 → ℝ} (hu : u ∈ Box (fun _ => (-1 : ℝ)) (fun _ => 1)) :
    let l : Fin 2 → ℝ := fun _ => -1
    let r : Fin 2 → ℝ := fun _ => 1
    let g : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun _ _ i => if i = 0 then 1 else 0
    let f : ℕ → (Fin 2 → ℝ) → ℝ := fun t x => ∑ i : Fin 2, g t x i * x i
    ∑ t ∈ range T, (f t (adaGradBox l r g (2 / √2) 0 (fun _ => 0) t) - f t u) ≤
      √2 * 2 * √(T : ℝ) := by
  intro l r g f
  have h := adaGradBox_regret_le_optimal (ι := Fin 2) (l := l) (r := r)
    (fun _ => by norm_num [l, r]) (D := 2) (ε := 0) two_pos
    (fun _ => by norm_num [l, r]) le_rfl (f := f) (grad := g)
    (x₀ := fun _ => 0) (u := u) (fun _ => by norm_num [l, r]) hu
    (fun t x _ y _ => le_of_eq (by
      simp only [f, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)) T
  refine h.trans_eq ?_
  simp [g, Fin.sum_univ_two]

/-- Strict sparse-gradient comparison between `∑ i, √(a i)` and `√(d * ∑ i, a i)`. -/
example :
    let a : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    ∑ i : Fin 2, √(a i) < √((Fintype.card (Fin 2) : ℝ) * ∑ i : Fin 2, a i) := by
  intro a
  have hL : ∑ i : Fin 2, √(a i) = 1 := by
    simp [a, Fin.sum_univ_two]
  have hR : (Fintype.card (Fin 2) : ℝ) * ∑ i : Fin 2, a i = 2 := by
    simp [a]
  rw [hL, hR]
  have h12 : (1 : ℝ) < 2 := by norm_num
  simpa using Real.sqrt_lt_sqrt zero_le_one h12

/-- Concrete Cauchy–Schwarz comparison via `Finset.sum_sqrt_le_card_mul_sqrt` on sparse
coordinates `(1, 0)`. -/
example :
    let a : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    ∑ i ∈ (univ : Finset (Fin 2)), √(a i) ≤
      ((univ : Finset (Fin 2)).card : ℝ) * √(1 / 2) := by
  intro a
  refine Finset.sum_sqrt_le_card_mul_sqrt univ (fun i _ => by dsimp [a]; split_ifs <;> norm_num)
    (by norm_num) ?_
  simp [a]

/-! ### Bregman divergence & Online Mirror Descent (`OnlineMirrorDescent`) -/

example (x y : ℝ) :
    bregmanDiv (fun z : ℝ => ‖z‖ ^ 2 / 2) id x y = ‖x - y‖ ^ 2 / 2 :=
  bregmanDiv_sq_norm_half x y

/-- Three-point identity check for `bregmanDiv_three_point` on the quadratic `ψ x = x ^ 2 / 2`. -/
example (x y z : ℝ) :
    bregmanDiv (fun w : ℝ => ‖w‖ ^ 2 / 2) id x y +
        bregmanDiv (fun w : ℝ => ‖w‖ ^ 2 / 2) id y z -
        bregmanDiv (fun w : ℝ => ‖w‖ ^ 2 / 2) id x z =
      ⟪z - y, x - y⟫ :=
  bregmanDiv_three_point (fun w : ℝ => ‖w‖ ^ 2 / 2) id x y z

/-- Negative check: a strictly concave generator `ψ x = -x ^ 2` produces a negative Bregman
divergence, showing why convexity of `ψ` is required for nonnegativity. -/
example : bregmanDiv (fun x : ℝ => -(x ^ 2)) (fun x : ℝ => -2 * x) 1 0 < 0 := by
  simp only [bregmanDiv, real_inner_eq]
  norm_num

/-- Euclidean OMD with `metricProjection K` satisfies `IsOMDStep` and the horizon-tuned bound
`G * √(2 * B * T / μ) = G * D * √T` at `μ = 1`, `B = 2 = D ^ 2 / 2`, `D = 2`, `G = 1`. -/
example (c : ℕ → ℝ) (hc : ∀ t, |c t| ≤ 1) {u : ℝ} (hu : u ∈ K) {T : ℕ} (hT : 0 < T) :
    let η := √(2 * 1 * 2) / (1 * √(T : ℝ))
    let x := ogd (metricProjection K) (fun _ => η) (fun t _ => c t) 0
    ∑ t ∈ range T, (c t * x t - c t * u) ≤ 1 * √(2 * 2 * (T : ℝ) / 1) := by
  intro η x
  refine omd_regret_le_tuned (K := K) (ψ := fun z : ℝ => ‖z‖ ^ 2 / 2) (gradψ := id)
    (primal := fun z : ℝ => ‖z‖) (dual := fun z : ℝ => ‖z‖) (μ := 1) (B := 2) (G := 1)
    one_pos two_pos one_pos
    (fun a b => (le_abs_self _).trans (abs_real_inner_le_norm a b))
    (fun a _ b _ => by
      rw [bregmanDiv_sq_norm_half, norm_sub_rev b a]
      ring_nf
      exact le_rfl)
    (fun t z => c t * z) (fun t _ => c t) x T hT (by simp only [x, ogd_zero]; norm_num)
    (fun t _ => by
      have hsucc : x (t + 1) = metricProjection K (x t - η • c t) := ogd_succ ..
      rw [hsucc]
      exact isOMDStep_metricProjection_euclidean K_nonempty K_isComplete K_convex η (c t) (x t))
    (fun t _ a _ b _ => le_of_eq (by rw [real_inner_eq]; ring))
    (fun t _ => norm_nonneg _)
    (fun t _ => by rw [Real.norm_eq_abs]; exact hc t) hu ?_
  rw [bregmanDiv_sq_norm_half]
  simp only [x, ogd_zero]
  have hu2 : ‖u - 0‖ ≤ 2 := K_diam u hu 0 (by norm_num)
  have hsq : ‖u - 0‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (u - 0), hu2]
  linarith

/-- Horizon-independent `omd_regret_le_sqrt` instance on `[-1, 1]`. -/
example (c : ℕ → ℝ) (hc : ∀ t, |c t| ≤ 1) {u : ℝ} (hu : u ∈ K) (T : ℕ) :
    let η : ℕ → ℝ := fun t => √(1 * 2) / (1 * √((t : ℝ) + 1))
    let x := ogd (metricProjection K) η (fun t _ => c t) 0
    ∑ t ∈ range T, (c t * x t - c t * u) ≤ 2 * 1 * √(2 * (T : ℝ) / 1) := by
  intro η x
  refine omd_regret_le_sqrt (K := K) (ψ := fun z : ℝ => ‖z‖ ^ 2 / 2) (gradψ := id)
    (primal := fun z : ℝ => ‖z‖) (dual := fun z : ℝ => ‖z‖) (μ := 1) (D := 2) (G := 1)
    one_pos two_pos one_pos
    (fun a b => (le_abs_self _).trans (abs_real_inner_le_norm a b))
    (fun a _ b _ => by
      rw [bregmanDiv_sq_norm_half, norm_sub_rev b a]
      ring_nf
      exact le_rfl)
    (fun t z => c t * z) (fun t _ => c t) x T (by simp only [x, ogd_zero]; norm_num)
    (fun t _ => by
      have hsucc : x (t + 1) = metricProjection K (x t - η t • c t) := ogd_succ ..
      rw [hsucc]
      exact isOMDStep_metricProjection_euclidean K_nonempty K_isComplete K_convex (η t) (c t) (x t))
    (fun t _ a _ b _ => le_of_eq (by rw [real_inner_eq]; ring))
    (fun t _ => norm_nonneg _)
    (fun t _ => by rw [Real.norm_eq_abs]; exact hc t) hu ?_
  intro t _
  rw [bregmanDiv_sq_norm_half]
  have hx_mem : x t ∈ K := ogd_mem
    (isPythagoreanProjection_metricProjection K_nonempty K_isComplete K_convex) (by norm_num) t
  have hd : ‖u - x t‖ ≤ 2 := K_diam u hu (x t) hx_mem
  have hsq : ‖u - x t‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (u - x t), hd]
  linarith

/-! ### Minimax lower bound & upper/lower match (`OCOLowerBound`) -/

example : 𝔼 σ : Fin 2 → Bool, (∑ t : Fin 2, (1 : ℝ) * signVal (σ t)) ^ 2 = 2 := by
  rw [expect_sq_sum_mul_signVal]
  norm_num

example : 𝔼 σ : Fin 2 → Bool, (∑ t : Fin 2, (1 : ℝ) * signVal (σ t)) ^ 4 = 8 := by
  rw [expect_sum_mul_signVal_pow_four]
  norm_num

example : (2 : ℝ) ^ 2 * Real.sqrt ((2 : ℝ) / 3) ≤
    ∑ σ : Fin 2 → Bool, |∑ t : Fin 2, signVal (σ t)| :=
  khintchine_rademacher_abs_sum 2

/-- Any causal learner on `[-1, 1]` (`D = 2`) incurs at least `2 * √T / (2 * √3)` regret on some
Rademacher linear loss sequence (`G = 1`). -/
example (T : ℕ) (L : CausalLearner K T) :
    ∃ (σ : Fin T → Bool) (u : ℝ), u ∈ K ∧
      2 * 1 * Real.sqrt T / (2 * Real.sqrt 3) ≤
        ∑ t : Fin T,
          (rademacherLinear (1 : ℝ) 1 (σ t) (L.eval σ t) - rademacherLinear (1 : ℝ) 1 (σ t) u) :=
  exists_oco_regret_ge (x₀ := 0) (e := 1) (D := 2) (G := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) T L

/-- Concrete causal learner witness: the constant `0` learner on `[-1, 1]`. -/
private def constZeroLearner (T : ℕ) : CausalLearner K T where
  play _ _ := 0
  mem _ _ := by norm_num

/-- Non-vacuous check instantiating `exists_oco_regret_ge` on the concrete learner
`constZeroLearner` at `T = 4`. -/
example :
    ∃ (σ : Fin 4 → Bool) (u : ℝ), u ∈ K ∧
      2 * 1 * Real.sqrt 4 / (2 * Real.sqrt 3) ≤
        ∑ t : Fin 4,
          (rademacherLinear (1 : ℝ) 1 (σ t) ((constZeroLearner 4).eval σ t) -
            rademacherLinear (1 : ℝ) 1 (σ t) u) :=
  exists_oco_regret_ge (x₀ := 0) (e := 1) (D := 2) (G := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) 4 (constZeroLearner 4)

/-- Concrete adaptive causal learner witness: OGD with step size `η = 1` running on the strict
prefix of past Rademacher gradients over `K = [-1, 1]`. -/
private noncomputable def ogdCausalLearner (T : ℕ) : CausalLearner K T where
  play t h :=
    ogd (clampProj (-1) 1) (fun _ => 1)
      (fun s _ => if hs : s < t.val then rademacherGrad (1 : ℝ) 1 (h ⟨s, lt_trans hs t.isLt⟩ hs)
        else 0)
      0 t.val
  mem _ _ := ogd_mem K_proj (by norm_num) _

/-- Non-vacuous check instantiating `exists_oco_regret_ge` on `ogdCausalLearner 4`. -/
example :
    ∃ (σ : Fin 4 → Bool) (u : ℝ), u ∈ K ∧
      2 * 1 * Real.sqrt 4 / (2 * Real.sqrt 3) ≤
        ∑ t : Fin 4,
          (rademacherLinear (1 : ℝ) 1 (σ t) ((ogdCausalLearner 4).eval σ t) -
            rademacherLinear (1 : ℝ) 1 (σ t) u) :=
  exists_oco_regret_ge (x₀ := 0) (e := 1) (D := 2) (G := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) 4 (ogdCausalLearner 4)

/-- Companion OGD upper bound on the **same** Rademacher linear loss family (`K = [-1, 1]`,
`D = 2`, `G = 1`), matching the lower bound up to the factor `2 * √3`. -/
example {T : ℕ} (hT : 0 < T) (σ : Fin T → Bool) {u : ℝ} (hu : u ∈ K) :
    let s : ℕ → Bool := fun t => if h : t < T then σ ⟨t, h⟩ else true
    let f : ℕ → ℝ → ℝ := fun t x => rademacherLinear (1 : ℝ) 1 (s t) x
    let g : ℕ → ℝ → ℝ := fun t _ => rademacherGrad (1 : ℝ) 1 (s t)
    ∑ t ∈ range T, (f t (ogd (clampProj (-1) 1) (fun _ => 2 / (1 * √(T : ℝ))) g 0 t) - f t u) ≤
      1 * 2 * √(T : ℝ) := by
  intro s f g
  exact ogd_regret_le_fixed (f := f) (grad := g) K_proj (by norm_num) two_pos one_pos K_diam
    (fun t _ _ => norm_rademacherGrad_le (by norm_num) zero_le_one (s t))
    (fun t x _ y _ => le_of_eq (rademacherLinear_subgrad 1 1 (s t) x y)) hu hT

end CslibFrontierTests.OnlineConvexOpt
