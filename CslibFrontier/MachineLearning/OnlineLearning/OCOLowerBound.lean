/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.OnlineGradientDescent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Online convex optimization regret lower bound

Proves the minimax `Ω(D * G * √T)` regret lower bound for **online convex optimization** (OCO)
against linear (hence convex) `G`-Lipschitz losses over any convex set `K` in a real inner product
space containing two points at distance `D` [Hazan2022].

The proof runs an oblivious Rademacher adversary `f_t(x) = σ_t * G * ⟪e, x⟫` (`σ_t ∈ {-1, +1}`,
unit vector `e` parallel to a diameter segment `x₀ ± (D / 2) • e ∈ K`):

1. By causality (round `t` sees only `σ_0, …, σ_{t-1}`), flipping `σ_t` pairs realizations with
   opposite signs of `σ_t` and the same learner point `x_t`, so `∑ σ, f_t(x_t) = 0`.
2. Against the hindsight optimum `u_σ = x₀ - (sign (∑ σ_t) * D / 2) • e ∈ {x₀ ± (D / 2) • e} ⊆ K`,
   the cumulative comparator term sums to `-(D * G / 2) * |∑ σ_t|` (plus a zero-mean `x₀` shift).
3. The second and fourth moments of the Rademacher sum `S(σ) = ∑ t : Fin T, sign (σ t)` are
   computed exactly by induction: `∑ σ, S(σ)^2 = 2^T * T` and `∑ σ, S(σ)^4 = 2^T * (3T^2 - 2T)`.
4. Applying Cauchy–Schwarz twice yields the elementary Khintchine lower bound
   `(∑ S^2)^3 ≤ (∑ |S|)^2 * (∑ S^4)`, hence `2^T * √(T / 3) ≤ ∑ σ, |S(σ)|`.
5. Averaging over `σ : Fin T → Bool` produces a realization `σ` and a point `u ∈ K` with
   `D * G * √T / (2 * √3) ≤ ∑ t < T, (f_{σ t} (x_t) - f_{σ t} u)`.

(This elementary fourth-moment proof gives the constant `1 / (2 √3) ≈ 0.289` in place of the
asymptotic `1 / √(2 π) ≈ 0.399` or Littlewood/Szarek `1 / √2` constant, matching the exact
`D * G * √T` scaling of `ogd_regret_le_fixed`.)

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.OCO.rademacherSign`: maps `true ↦ 1`, `false ↦ -1`.
* `Cslib.MachineLearning.OnlineLearning.OCO.rademacherLinear`: linear loss `±G * ⟪e, x⟫`.
* `Cslib.MachineLearning.OnlineLearning.OCO.rademacherGrad`: constant gradient `(±G) • e`.
* `Cslib.MachineLearning.OnlineLearning.OCO.CausalLearner`: deterministic online learner whose
  round-`t` iterate depends only on the adversary's past signs `σ i` (`i < t`).

## Main results

* `Cslib.MachineLearning.OnlineLearning.OCO.sum_rademacherSum_sq`:
  `∑ σ : Fin T → Bool, (∑ t, rademacherSign (σ t)) ^ 2 = 2 ^ T * T`.
* `Cslib.MachineLearning.OnlineLearning.OCO.sum_rademacherSum_pow_four`:
  `∑ σ : Fin T → Bool, (∑ t, rademacherSign (σ t)) ^ 4 = 2 ^ T * (3 * T ^ 2 - 2 * T)`.
* `Cslib.MachineLearning.OnlineLearning.OCO.khintchine_rademacher_abs_sum`:
  `2 ^ T * √(T / 3) ≤ ∑ σ : Fin T → Bool, |∑ t, rademacherSign (σ t)|`.
* `Cslib.MachineLearning.OnlineLearning.OCO.exists_oco_regret_ge`:
  minimax `Ω(D * G * √T)` lower bound (`D * G * √T / (2 * √3)`).

## References

* [E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed.][Hazan2022]
-/

public section

open Finset Real
open scoped RealInnerProductSpace

namespace Cslib.MachineLearning.OnlineLearning.OCO

/-- Rademacher sign `{false ↦ -1, true ↦ 1}` in `ℝ`. -/
@[expose] def rademacherSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem rademacherSign_true : rademacherSign true = 1 := rfl
@[simp] theorem rademacherSign_false : rademacherSign false = -1 := rfl

@[simp] theorem rademacherSign_not (b : Bool) : rademacherSign (!b) = -rademacherSign b := by
  cases b <;> norm_num [rademacherSign]

@[simp] theorem rademacherSign_sq (b : Bool) : rademacherSign b ^ 2 = 1 := by
  cases b <;> norm_num [rademacherSign]

@[simp] theorem abs_rademacherSign (b : Bool) : |rademacherSign b| = 1 := by
  cases b <;> norm_num [rademacherSign]

/-- Rademacher sum `S(σ) = ∑ t : Fin T, rademacherSign (σ t)`. -/
@[expose] def rademacherSum {T : ℕ} (σ : Fin T → Bool) : ℝ :=
  ∑ t : Fin T, rademacherSign (σ t)

private def splitBoolEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun σ := (σ 0, fun i => σ i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv σ := by
    ext i
    refine Fin.cases rfl (fun j => rfl) i
  right_inv p := by
    ext
    · rfl
    · rfl

private theorem sum_rademacher_split {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) :
    ∑ σ : Fin (n + 1) → Bool, F σ =
      ∑ τ : Fin n → Bool, (F (Fin.cons true τ) + F (Fin.cons false τ)) := by
  rw [Fintype.sum_equiv (splitBoolEquiv n) F (fun p => F (Fin.cons p.1 p.2))
    (fun σ => congrArg F ((splitBoolEquiv n).left_inv σ).symm)]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun τ _ => by simp

private theorem rademacherSum_cons {n : ℕ} (b : Bool) (τ : Fin n → Bool) :
    rademacherSum (Fin.cons b τ) = rademacherSign b + rademacherSum τ := by
  simp only [rademacherSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Sum of Rademacher sums over `{±1}ᵀ` vanishes. -/
theorem sum_rademacherSum (T : ℕ) :
    ∑ σ : Fin T → Bool, rademacherSum σ = 0 := by
  induction T with
  | zero => simp [rademacherSum]
  | succ n ih =>
    rw [sum_rademacher_split]
    have : ∀ τ : Fin n → Bool,
        rademacherSum (Fin.cons true τ) + rademacherSum (Fin.cons false τ) =
          2 * rademacherSum τ := by
      intro τ
      rw [rademacherSum_cons, rademacherSum_cons]
      simp only [rademacherSign_true, rademacherSign_false]
      ring
    simp_rw [this, ← Finset.mul_sum, ih, mul_zero]

/-- Exact second moment over `{±1}ᵀ`: `∑ σ, (∑ t, σ t) ^ 2 = 2 ^ T * T`. -/
theorem sum_rademacherSum_sq (T : ℕ) :
    ∑ σ : Fin T → Bool, rademacherSum σ ^ 2 = (2 : ℝ) ^ T * (T : ℝ) := by
  induction T with
  | zero => simp [rademacherSum]
  | succ n ih =>
    rw [sum_rademacher_split]
    have hstep : ∀ τ : Fin n → Bool,
        rademacherSum (Fin.cons true τ) ^ 2 + rademacherSum (Fin.cons false τ) ^ 2 =
          2 * (rademacherSum τ ^ 2 + 1) := by
      intro τ
      rw [rademacherSum_cons, rademacherSum_cons]
      simp only [rademacherSign_true, rademacherSign_false]
      ring
    simp_rw [hstep, ← Finset.mul_sum, Finset.sum_add_distrib, ih, Finset.sum_const,
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    push_cast
    ring

/-- Exact fourth moment over `{±1}ᵀ`: `∑ σ, (∑ t, σ t) ^ 4 = 2 ^ T * (3 * T ^ 2 - 2 * T)`. -/
theorem sum_rademacherSum_pow_four (T : ℕ) :
    ∑ σ : Fin T → Bool, rademacherSum σ ^ 4 =
      (2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2 - 2 * (T : ℝ)) := by
  induction T with
  | zero => simp [rademacherSum]
  | succ n ih =>
    rw [sum_rademacher_split]
    have hstep : ∀ τ : Fin n → Bool,
        rademacherSum (Fin.cons true τ) ^ 4 + rademacherSum (Fin.cons false τ) ^ 4 =
          2 * (rademacherSum τ ^ 4 + 6 * rademacherSum τ ^ 2 + 1) := by
      intro τ
      rw [rademacherSum_cons, rademacherSum_cons]
      simp only [rademacherSign_true, rademacherSign_false]
      ring
    simp_rw [hstep, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
      ih, sum_rademacherSum_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring

/-- Elementary Khintchine `L¹`/`L²` inequality for Rademacher sums via Cauchy–Schwarz:
`2 ^ T * √(T / 3) ≤ ∑ σ : Fin T → Bool, |∑ t, rademacherSign (σ t)|`. -/
theorem khintchine_rademacher_abs_sum (T : ℕ) :
    (2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3) ≤
      ∑ σ : Fin T → Bool, |rademacherSum σ| := by
  by_cases hT : T = 0
  · subst hT
    simp [rademacherSum]
  have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hT)
  set S1 : ℝ := ∑ σ : Fin T → Bool, |rademacherSum σ|
  set S2 : ℝ := ∑ σ : Fin T → Bool, rademacherSum σ ^ 2
  set S3 : ℝ := ∑ σ : Fin T → Bool, |rademacherSum σ| ^ 3
  set S4 : ℝ := ∑ σ : Fin T → Bool, rademacherSum σ ^ 4
  have hS2_eq : S2 = (2 : ℝ) ^ T * (T : ℝ) := sum_rademacherSum_sq T
  have hS4_eq : S4 = (2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2 - 2 * (T : ℝ)) :=
    sum_rademacherSum_pow_four T
  have hS2_pos : 0 < S2 := by rw [hS2_eq]; positivity
  have hS1_nonneg : 0 ≤ S1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcs1 : S2 ^ 2 ≤ S1 * S3 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin T → Bool))
      (fun σ => Real.sqrt |rademacherSum σ|)
      (fun σ => |rademacherSum σ| * Real.sqrt |rademacherSum σ|)
    have hL : ∑ σ : Fin T → Bool,
        Real.sqrt |rademacherSum σ| * (|rademacherSum σ| * Real.sqrt |rademacherSum σ|) = S2 := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      calc Real.sqrt |rademacherSum σ| * (|rademacherSum σ| * Real.sqrt |rademacherSum σ|)
          = |rademacherSum σ| * (Real.sqrt |rademacherSum σ| * Real.sqrt |rademacherSum σ|) := by
            ring
        _ = |rademacherSum σ| * |rademacherSum σ| := by
            rw [Real.mul_self_sqrt (abs_nonneg _)]
        _ = rademacherSum σ ^ 2 := by rw [← sq, sq_abs]
    have hR1 : ∑ σ : Fin T → Bool, Real.sqrt |rademacherSum σ| ^ 2 = S1 := by
      refine Finset.sum_congr rfl fun σ _ => Real.sq_sqrt (abs_nonneg _)
    have hR2 : ∑ σ : Fin T → Bool,
        (|rademacherSum σ| * Real.sqrt |rademacherSum σ|) ^ 2 = S3 := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
      ring
    rwa [hL, hR1, hR2] at h
  have hcs2 : S3 ^ 2 ≤ S2 * S4 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin T → Bool))
      (fun σ => |rademacherSum σ|)
      (fun σ => rademacherSum σ ^ 2)
    have hL : ∑ σ : Fin T → Bool, |rademacherSum σ| * rademacherSum σ ^ 2 = S3 := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [← sq_abs (rademacherSum σ)]
      ring
    have hR1 : ∑ σ : Fin T → Bool, |rademacherSum σ| ^ 2 = S2 := by
      refine Finset.sum_congr rfl fun σ _ => sq_abs _
    have hR2 : ∑ σ : Fin T → Bool, (rademacherSum σ ^ 2) ^ 2 = S4 := by
      refine Finset.sum_congr rfl fun σ _ => by ring
    rwa [hL, hR1, hR2] at h
  have hholder : S2 ^ 3 ≤ S1 ^ 2 * S4 := by
    have h1sq : (S2 ^ 2) ^ 2 ≤ (S1 * S3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcs1 2
    have h2 : S2 ^ 4 ≤ S1 ^ 2 * (S2 * S4) := by
      calc S2 ^ 4 = (S2 ^ 2) ^ 2 := by ring
        _ ≤ (S1 * S3) ^ 2 := h1sq
        _ = S1 ^ 2 * S3 ^ 2 := by ring
        _ ≤ S1 ^ 2 * (S2 * S4) := mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
    have hmul : S2 * S2 ^ 3 ≤ S2 * (S1 ^ 2 * S4) := by linarith
    exact le_of_mul_le_mul_left hmul hS2_pos
  have hS4_le : S4 ≤ (2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2) := by
    rw [hS4_eq]
    have h2T : (0 : ℝ) ≤ (2 : ℝ) ^ T := by positivity
    nlinarith
  have hsq : ((2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3)) ^ 2 ≤ S1 ^ 2 := by
    have h3 : S2 ^ 3 ≤ S1 ^ 2 * ((2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2)) :=
      hholder.trans (mul_le_mul_of_nonneg_left hS4_le (sq_nonneg _))
    rw [hS2_eq] at h3
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (T : ℝ) / 3)]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2) := by positivity
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hS1_nonneg] at hsqrt

section LowerBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Hard linear Rademacher loss `f_b(x) = rademacherSign b * G * ⟪e, x⟫`. -/
@[expose] def rademacherLinear (e : E) (G : ℝ) (b : Bool) (x : E) : ℝ :=
  rademacherSign b * G * ⟪e, x⟫

/-- Gradient of `rademacherLinear e G b`, equal to `(rademacherSign b * G) • e`. -/
@[expose] def rademacherGrad (e : E) (G : ℝ) (b : Bool) : E :=
  (rademacherSign b * G) • e

/-- Exact affine identity for `rademacherLinear` (subgradient inequality with equality). -/
theorem rademacherLinear_subgrad (e : E) (G : ℝ) (b : Bool) (x y : E) :
    rademacherLinear e G b x + ⟪rademacherGrad e G b, y - x⟫ = rademacherLinear e G b y := by
  simp only [rademacherLinear, rademacherGrad, real_inner_smul_left, inner_sub_right]
  ring

/-- `rademacherLinear e G b` is convex on every convex set `K` (it is linear). -/
theorem rademacherLinear_convexOn (e : E) (G : ℝ) (b : Bool) {K : Set E} (hK : Convex ℝ K) :
    ConvexOn ℝ K (rademacherLinear e G b) := by
  refine ⟨hK, fun x _ y _ a c _ _ _ => ?_⟩
  simp only [rademacherLinear, smul_eq_mul, inner_add_right, real_inner_smul_right]
  ring_nf
  exact le_rfl

/-- Gradient norm bound `‖rademacherGrad e G b‖ ≤ G` when `‖e‖ ≤ 1` and `0 ≤ G`. -/
theorem norm_rademacherGrad_le {e : E} {G : ℝ} (he : ‖e‖ ≤ 1) (hG : 0 ≤ G) (b : Bool) :
    ‖rademacherGrad e G b‖ ≤ G := by
  rw [rademacherGrad, norm_smul, Real.norm_eq_abs, abs_mul, abs_rademacherSign, one_mul,
    abs_of_nonneg hG]
  exact (mul_le_mul_of_nonneg_left he hG).trans_eq (mul_one G)

/-- A deterministic **causal online learner** for horizon `T` against `Bool`-valued Rademacher
signs on a feasible set `K ⊆ E`: at round `t : Fin T`, its played point depends strictly on the
past signs `(i : Fin T) → i < t → Bool`. -/
structure CausalLearner (K : Set E) (T : ℕ) where
  /-- Round-`t` prediction as a function of the strict prefix of past signs. -/
  play : (t : Fin T) → ((i : Fin T) → i < t → Bool) → E
  /-- Every played point belongs to the feasible domain `K`. -/
  mem : ∀ t h, play t h ∈ K

/-- The point played by a `CausalLearner` at round `t` under sign sequence `σ : Fin T → Bool`. -/
@[expose] def CausalLearner.eval {K : Set E} {T : ℕ} (L : CausalLearner K T)
    (σ : Fin T → Bool) (t : Fin T) : E :=
  L.play t (fun i _ => σ i)

private theorem sum_flip_cancel {T : ℕ} (t : Fin T) (g : (Fin T → Bool) → ℝ)
    (hinv : ∀ σ : Fin T → Bool, g (Function.update σ t (!σ t)) = g σ) :
    ∑ σ : Fin T → Bool, rademacherSign (σ t) * g σ = 0 := by
  let flip : (Fin T → Bool) ≃ (Fin T → Bool) :=
    { toFun := fun σ => Function.update σ t (!σ t)
      invFun := fun σ => Function.update σ t (!σ t)
      left_inv := fun σ => by
        ext i
        by_cases hi : i = t
        · subst hi; simp
        · simp [Function.update, hi]
      right_inv := fun σ => by
        ext i
        by_cases hi : i = t
        · subst hi; simp
        · simp [Function.update, hi] }
  have hsum :
      ∑ σ : Fin T → Bool, rademacherSign (σ t) * g σ =
        ∑ σ : Fin T → Bool, -(rademacherSign (σ t) * g σ) := by
    refine Fintype.sum_equiv flip (fun σ => rademacherSign (σ t) * g σ)
      (fun σ => -(rademacherSign (σ t) * g σ)) fun σ => ?_
    have hft : flip σ t = !σ t := by simp [flip]
    have hgi : g (flip σ) = g σ := hinv σ
    rw [hft, rademacherSign_not, hgi]
    ring
  rw [Finset.sum_neg_distrib] at hsum
  linarith

/-- Total loss of any causal learner averaged over all `2 ^ T` Rademacher sequences vanishes. -/
theorem sum_rademacherLinear_eval_eq_zero {K : Set E} {T : ℕ} (L : CausalLearner K T)
    (e : E) (G : ℝ) :
    ∑ σ : Fin T → Bool, ∑ t : Fin T, rademacherLinear e G (σ t) (L.eval σ t) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  have heq : ∀ σ : Fin T → Bool,
      rademacherLinear e G (σ t) (L.eval σ t) =
        rademacherSign (σ t) * (G * ⟪e, L.eval σ t⟫) := fun σ => by
    simp only [rademacherLinear]; ring
  simp_rw [heq]
  refine sum_flip_cancel t (fun σ => G * ⟪e, L.eval σ t⟫) fun σ => ?_
  have hpref : (fun i (hi : i < t) => Function.update σ t (!σ t) i) = fun i _ => σ i := by
    ext i hi
    exact Function.update_of_ne (ne_of_lt hi) _ σ
  simp only [CausalLearner.eval, hpref]

/-- **Minimax `Ω(D * G * √T)` regret lower bound for online convex optimization** [Hazan2022]:
if `K` contains `x₀ ± (D / 2) • e` for a unit vector `e` (`‖e‖ = 1`), then for every causal learner
`L` and horizon `T : ℕ`, there exist a Rademacher sign sequence `σ : Fin T → Bool` and a
comparator `u ∈ K` whose linear `G`-Lipschitz losses `f_t = rademacherLinear e G (σ t)` incur
regret at least `D * G * √T / (2 * √3)`. -/
theorem exists_oco_regret_ge {K : Set E} {x₀ e : E} {D G : ℝ}
    (hD : 0 ≤ D) (hG : 0 ≤ G) (he : ‖e‖ = 1)
    (hplus : x₀ + (D / 2) • e ∈ K) (hminus : x₀ - (D / 2) • e ∈ K)
    (T : ℕ) (L : CausalLearner K T) :
    ∃ (σ : Fin T → Bool) (u : E), u ∈ K ∧
      D * G * Real.sqrt T / (2 * Real.sqrt 3) ≤
        ∑ t : Fin T,
          (rademacherLinear e G (σ t) (L.eval σ t) - rademacherLinear e G (σ t) u) := by
  let uOf : (Fin T → Bool) → E := fun σ =>
    if 0 ≤ rademacherSum σ then x₀ - (D / 2) • e else x₀ + (D / 2) • e
  have huOf_mem : ∀ σ, uOf σ ∈ K := by
    intro σ
    dsimp only [uOf]
    split_ifs <;> assumption
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have huOf_sum : ∀ σ : Fin T → Bool,
      ∑ t : Fin T, rademacherLinear e G (σ t) (uOf σ) =
        rademacherSum σ * G * ⟪e, x₀⟫ - D * G / 2 * |rademacherSum σ| := by
    intro σ
    have hfac :
        ∑ t : Fin T, rademacherLinear e G (σ t) (uOf σ) =
          rademacherSum σ * (G * ⟪e, uOf σ⟫) := by
      simp only [rademacherLinear, rademacherSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => by ring
    rw [hfac]
    dsimp only [uOf]
    split_ifs with hs
    · rw [inner_sub_right, real_inner_smul_right, hee, mul_one, abs_of_nonneg hs]
      ring
    · rw [inner_add_right, real_inner_smul_right, hee, mul_one, abs_of_neg (lt_of_not_ge hs)]
      ring
  have hsum_reg :
      ∑ σ : Fin T → Bool,
          ∑ t : Fin T,
            (rademacherLinear e G (σ t) (L.eval σ t) - rademacherLinear e G (σ t) (uOf σ)) =
        D * G / 2 * ∑ σ : Fin T → Bool, |rademacherSum σ| := by
    have hsplit : ∀ σ : Fin T → Bool,
        ∑ t : Fin T,
            (rademacherLinear e G (σ t) (L.eval σ t) - rademacherLinear e G (σ t) (uOf σ)) =
          (∑ t : Fin T, rademacherLinear e G (σ t) (L.eval σ t)) -
            (∑ t : Fin T, rademacherLinear e G (σ t) (uOf σ)) :=
      fun σ => Finset.sum_sub_distrib ..
    simp_rw [hsplit, Finset.sum_sub_distrib, sum_rademacherLinear_eval_eq_zero, zero_sub,
      huOf_sum, Finset.sum_sub_distrib]
    have hshift : ∑ σ : Fin T → Bool, rademacherSum σ * G * ⟪e, x₀⟫ = 0 := by
      have : ∑ σ : Fin T → Bool, rademacherSum σ * G * ⟪e, x₀⟫ =
          (∑ σ : Fin T → Bool, rademacherSum σ) * (G * ⟪e, x₀⟫) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun σ _ => by ring
      rw [this, sum_rademacherSum, zero_mul]
    rw [hshift, ← Finset.mul_sum]
    ring
  have hlow : (2 : ℝ) ^ T * (D * G * Real.sqrt T / (2 * Real.sqrt 3)) ≤
      ∑ σ : Fin T → Bool,
        ∑ t : Fin T,
          (rademacherLinear e G (σ t) (L.eval σ t) - rademacherLinear e G (σ t) (uOf σ)) := by
    rw [hsum_reg]
    have hk := khintchine_rademacher_abs_sum T
    have hDG : 0 ≤ D * G / 2 := by positivity
    calc (2 : ℝ) ^ T * (D * G * Real.sqrt T / (2 * Real.sqrt 3))
        = D * G / 2 * ((2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3)) := by
          rw [Real.sqrt_div (Nat.cast_nonneg T)]
          ring
      _ ≤ D * G / 2 * ∑ σ : Fin T → Bool, |rademacherSum σ| :=
          mul_le_mul_of_nonneg_left hk hDG
  have hcard : ((Finset.univ : Finset (Fin T → Bool)).card : ℝ) = (2 : ℝ) ^ T := by
    simp
  have hconst : ∑ _σ : Fin T → Bool, (D * G * Real.sqrt T / (2 * Real.sqrt 3)) ≤
      ∑ σ : Fin T → Bool,
        ∑ t : Fin T,
          (rademacherLinear e G (σ t) (L.eval σ t) - rademacherLinear e G (σ t) (uOf σ)) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    exact hlow
  by_contra hnot
  push Not at hnot
  have hlt : ∀ σ ∈ (Finset.univ : Finset (Fin T → Bool)),
      ∑ t : Fin T,
          (rademacherLinear e G (σ t) (L.eval σ t) - rademacherLinear e G (σ t) (uOf σ)) <
        D * G * Real.sqrt T / (2 * Real.sqrt 3) :=
    fun σ _ => hnot σ (uOf σ) (huOf_mem σ)
  have hstrict := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt
  linarith

end LowerBound

end Cslib.MachineLearning.OnlineLearning.OCO
