/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.BitString.Rademacher
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Online convex optimization regret lower bound

Proves the minimax `Ω(D * G * √T)` regret lower bound for **online convex optimization** (OCO)
against linear (hence convex) `G`-Lipschitz losses over any convex set `K` in a real inner product
space containing two points at distance `D` [Hazan2022] (locator unverified).

The proof runs an oblivious Rademacher adversary `f_t(x) = signVal (σ t) * G * ⟪e, x⟫`
(`signVal : Bool → ℝ` from `Cslib.BitString`, unit vector `e` parallel to a diameter segment
`x₀ ± (D / 2) • e ∈ K`):

1. By causality (round `t` sees only `σ 0, …, σ (t - 1)`), resampling `σ t` via
   `Fintype.expect_expect_update` pairs opposite signs with the same learner point `L.eval σ t`, so
   `𝔼 σ, f_t(x_t) = 0`.
2. Against the hindsight optimum `u_σ = x₀ - (sign (∑ t, signVal (σ t)) * D / 2) • e`, the
   cumulative comparator term equals `-(D * G / 2) * |∑ t, signVal (σ t)|` up to a zero-mean `x₀`
   shift.
3. The second and fourth moments of `S(σ) = ∑ t : Fin T, signVal (σ t)` are supplied directly by
   `Cslib.BitString.expect_sq_sum_mul_signVal` (`𝔼 S² = T`) and
   `Cslib.BitString.expect_sum_mul_signVal_pow_four_le` (`𝔼 S⁴ ≤ 3 T²`).
4. Applying Cauchy–Schwarz twice yields the elementary Khintchine lower bound
   `(∑ S²)³ ≤ (∑ |S|)² * (∑ S⁴)`, hence `√(T / 3) ≤ 𝔼 σ, |S(σ)|`.
5. Averaging over `σ : Fin T → Bool` produces a realization `σ` and a point `u ∈ K` with
   `D * G * √T / (2 * √3) ≤ ∑ t, (f_{σ t} (x_t) - f_{σ t} u)`.

(This elementary fourth-moment proof gives the constant `1 / (2 √3) ≈ 0.289` in place of the
asymptotic `1 / √(2 π) ≈ 0.399` or Littlewood/Szarek `1 / √2` constant, matching the exact
`D * G * √T` scaling of `ogd_regret_le_fixed`.)

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.OCO.rademacherLinear`: linear loss `signVal b * G * ⟪e, x⟫`.
* `Cslib.MachineLearning.OnlineLearning.OCO.rademacherGrad`: constant gradient
  `(signVal b * G) • e`.
* `Cslib.MachineLearning.OnlineLearning.OCO.CausalLearner`: deterministic online learner whose
  round-`t` iterate depends only on the adversary's past signs `σ i` (`i < t`).

## Main results

* `Cslib.MachineLearning.OnlineLearning.OCO.khintchine_rademacher_abs_sum`:
  `2 ^ T * √(T / 3) ≤ ∑ σ : Fin T → Bool, |∑ t : Fin T, signVal (σ t)|`.
* `Cslib.MachineLearning.OnlineLearning.OCO.sum_rademacherLinear_eval_eq_zero`: total loss of any
  causal learner averaged over all `2 ^ T` Rademacher sequences vanishes.
* `Cslib.MachineLearning.OnlineLearning.OCO.exists_oco_regret_ge`:
  minimax `Ω(D * G * √T)` lower bound (`D * G * √T / (2 * √3)`).

## References

Exact section, theorem, and page locators below are unverified against primary PDFs (pending an
outside-fleet source check).

* [E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed.][Hazan2022] (locator unverified)
-/

public section

open Finset Real Cslib.BitString
open scoped RealInnerProductSpace BigOperators

namespace Cslib.MachineLearning.OnlineLearning.OCO

/-- Elementary Khintchine `L¹`/`L²` inequality for unweighted Rademacher sums via Cauchy–Schwarz and
the exact second/fourth moments in `CslibFrontier.Probability.BitString.Rademacher`:
`2 ^ T * √(T / 3) ≤ ∑ σ : Fin T → Bool, |∑ t : Fin T, signVal (σ t)|`. -/
theorem khintchine_rademacher_abs_sum (T : ℕ) :
    (2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3) ≤
      ∑ σ : Fin T → Bool, |∑ t : Fin T, signVal (σ t)| := by
  by_cases hT : T = 0
  · subst hT; simp
  have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hT)
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hcard : (Fintype.card (Fin T → Bool) : ℝ) = (2 : ℝ) ^ T := by simp
  set radSum : (Fin T → Bool) → ℝ := fun σ => ∑ t : Fin T, signVal (σ t)
  set S1 : ℝ := ∑ σ : Fin T → Bool, |radSum σ|
  set S2 : ℝ := ∑ σ : Fin T → Bool, radSum σ ^ 2
  set S3 : ℝ := ∑ σ : Fin T → Bool, |radSum σ| ^ 3
  set S4 : ℝ := ∑ σ : Fin T → Bool, radSum σ ^ 4
  have hS2_eq : S2 = (2 : ℝ) ^ T * (T : ℝ) := by
    have h := expect_sq_sum_mul_signVal (fun _ : Fin T => (1 : ℝ))
    simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Fintype.expect_eq_sum_div_card, hcard] at h
    exact ((div_eq_iff h2pos.ne').mp h).trans (mul_comm _ _)
  have hS4_le : S4 ≤ (2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2) := by
    have h := expect_sum_mul_signVal_pow_four_le (fun _ : Fin T => (1 : ℝ))
    simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Fintype.expect_eq_sum_div_card, hcard, div_le_iff₀ h2pos] at h
    linarith
  have hS2_pos : 0 < S2 := by rw [hS2_eq]; positivity
  have hcs1 : S2 ^ 2 ≤ S1 * S3 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin T → Bool))
      (fun σ => Real.sqrt |radSum σ|) (fun σ => |radSum σ| * Real.sqrt |radSum σ|)
    rwa [Finset.sum_congr rfl fun σ _ => show
        Real.sqrt |radSum σ| * (|radSum σ| * Real.sqrt |radSum σ|) = radSum σ ^ 2 by
          rw [mul_left_comm, Real.mul_self_sqrt (abs_nonneg _), ← sq, sq_abs],
      Finset.sum_congr rfl fun σ _ => Real.sq_sqrt (abs_nonneg (radSum σ)),
      Finset.sum_congr rfl fun σ _ => show
        (|radSum σ| * Real.sqrt |radSum σ|) ^ 2 = |radSum σ| ^ 3 by
          rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]; ring] at h
  have hcs2 : S3 ^ 2 ≤ S2 * S4 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin T → Bool))
      (fun σ => |radSum σ|) (fun σ => radSum σ ^ 2)
    rwa [Finset.sum_congr rfl fun σ _ => show |radSum σ| * radSum σ ^ 2 = |radSum σ| ^ 3 by
        rw [← sq_abs (radSum σ)]; ring,
      Finset.sum_congr rfl fun σ _ => sq_abs (radSum σ),
      Finset.sum_congr rfl fun σ _ => show (radSum σ ^ 2) ^ 2 = radSum σ ^ 4 by ring] at h
  have hholder : S2 ^ 3 ≤ S1 ^ 2 * S4 := by
    have h2 : S2 * S2 ^ 3 ≤ S2 * (S1 ^ 2 * S4) := by
      nlinarith [pow_le_pow_left₀ (by positivity) hcs1 2,
        mul_le_mul_of_nonneg_left hcs2 (sq_nonneg S1)]
    exact le_of_mul_le_mul_left h2 hS2_pos
  have hsq : ((2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3)) ^ 2 ≤ S1 ^ 2 := by
    have h3 : S2 ^ 3 ≤ S1 ^ 2 * ((2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2)) :=
      hholder.trans (mul_le_mul_of_nonneg_left hS4_le (sq_nonneg _))
    rw [hS2_eq] at h3
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (T : ℝ) / 3)]
    nlinarith [(by positivity : (0 : ℝ) < (2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2))]
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity),
    Real.sqrt_sq (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at hsqrt

section LowerBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Hard linear Rademacher loss `f_b(x) = signVal b * G * ⟪e, x⟫`. -/
@[expose] def rademacherLinear (e : E) (G : ℝ) (b : Bool) (x : E) : ℝ :=
  signVal b * G * ⟪e, x⟫

/-- Gradient of `rademacherLinear e G b`, equal to `(signVal b * G) • e`. -/
@[expose] def rademacherGrad (e : E) (G : ℝ) (b : Bool) : E :=
  (signVal b * G) • e

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
  rw [rademacherGrad, norm_smul, Real.norm_eq_abs, abs_mul, abs_signVal, one_mul,
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

/-- Resampling a single bit cancels any factor invariant under changing coordinate `t`. -/
private theorem sum_signVal_mul_eq_zero {T : ℕ} (t : Fin T) (g : (Fin T → Bool) → ℝ)
    (hinv : ∀ σ b, g (Function.update σ t b) = g σ) :
    ∑ σ : Fin T → Bool, signVal (σ t) * g σ = 0 := by
  have hexp : 𝔼 σ : Fin T → Bool, signVal (σ t) * g σ = 0 := by
    rw [← Fintype.expect_expect_update (fun σ : Fin T → Bool => signVal (σ t) * g σ) t]
    refine Finset.expect_eq_zero fun σ _ => ?_
    simp only [Function.update_self, hinv, ← Finset.expect_mul, expect_bool_signVal, zero_mul]
  rw [Fintype.expect_eq_sum_div_card] at hexp
  have hcard : (Fintype.card (Fin T → Bool) : ℝ) ≠ 0 := by positivity
  exact (div_eq_zero_iff.mp hexp).resolve_right hcard

/-- Total loss of any causal learner averaged over all `2 ^ T` Rademacher sequences vanishes. -/
theorem sum_rademacherLinear_eval_eq_zero {K : Set E} {T : ℕ} (L : CausalLearner K T)
    (e : E) (G : ℝ) :
    ∑ σ : Fin T → Bool, ∑ t : Fin T, rademacherLinear e G (σ t) (L.eval σ t) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  have heq : ∀ σ : Fin T → Bool,
      rademacherLinear e G (σ t) (L.eval σ t) = signVal (σ t) * (G * ⟪e, L.eval σ t⟫) :=
    fun σ => by simp only [rademacherLinear]; ring
  rw [Finset.sum_congr rfl fun σ _ => heq σ]
  refine sum_signVal_mul_eq_zero t (fun σ => G * ⟪e, L.eval σ t⟫) fun σ b => ?_
  have hpref : (fun i (hi : i < t) => Function.update σ t b i) = fun i _ => σ i := by
    ext i hi
    exact Function.update_of_ne (ne_of_lt hi) b σ
  simp only [CausalLearner.eval, hpref]

/-- **Minimax `Ω(D * G * √T)` regret lower bound for online convex optimization** [Hazan2022]
(locator unverified): if `K` contains `x₀ ± (D / 2) • e` for a unit vector `e` (`‖e‖ = 1`), then
for every causal learner `L` and horizon `T : ℕ`, there exist a Rademacher sign sequence
`σ : Fin T → Bool` and a comparator `u ∈ K` whose linear `G`-Lipschitz losses
`f_t = rademacherLinear e G (σ t)` incur regret at least `D * G * √T / (2 * √3)`. -/
theorem exists_oco_regret_ge {K : Set E} {x₀ e : E} {D G : ℝ}
    (hD : 0 ≤ D) (hG : 0 ≤ G) (he : ‖e‖ = 1)
    (hplus : x₀ + (D / 2) • e ∈ K) (hminus : x₀ - (D / 2) • e ∈ K)
    (T : ℕ) (L : CausalLearner K T) :
    ∃ (σ : Fin T → Bool) (u : E), u ∈ K ∧
      D * G * Real.sqrt T / (2 * Real.sqrt 3) ≤
        ∑ t : Fin T,
          (rademacherLinear e G (σ t) (L.eval σ t) - rademacherLinear e G (σ t) u) := by
  set radSum : (Fin T → Bool) → ℝ := fun σ => ∑ t : Fin T, signVal (σ t)
  let uOf (σ : Fin T → Bool) : E := if 0 ≤ radSum σ then x₀ - (D / 2) • e else x₀ + (D / 2) • e
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have huOf_sum (σ : Fin T → Bool) :
      ∑ t : Fin T, rademacherLinear e G (σ t) (uOf σ) =
        radSum σ * G * ⟪e, x₀⟫ - D * G / 2 * |radSum σ| := by
    rw [show ∑ t : Fin T, rademacherLinear e G (σ t) (uOf σ) = radSum σ * (G * ⟪e, uOf σ⟫) by
      simp only [rademacherLinear, radSum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring]
    dsimp only [uOf]; split_ifs with hs
    · rw [inner_sub_right, real_inner_smul_right, hee, mul_one, abs_of_nonneg hs]; ring
    · rw [inner_add_right, real_inner_smul_right, hee, mul_one, abs_of_neg (lt_of_not_ge hs)]; ring
  have hsum_rad : ∑ σ : Fin T → Bool, radSum σ = 0 := by
    simp only [radSum]; rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun t _ => by
      simpa only [mul_one] using sum_signVal_mul_eq_zero t (fun _ => (1 : ℝ)) fun _ _ => rfl
  have hsum_reg :
      ∑ σ : Fin T → Bool, ∑ t : Fin T,
          (rademacherLinear e G (σ t) (L.eval σ t) - rademacherLinear e G (σ t) (uOf σ)) =
        D * G / 2 * ∑ σ : Fin T → Bool, |radSum σ| := by
    rw [Finset.sum_congr rfl fun σ _ => Finset.sum_sub_distrib _ _, Finset.sum_sub_distrib,
      sum_rademacherLinear_eval_eq_zero, zero_sub,
      Finset.sum_congr rfl fun σ _ => huOf_sum σ, Finset.sum_sub_distrib,
      show ∑ σ : Fin T → Bool, radSum σ * G * ⟪e, x₀⟫ =
        (∑ σ : Fin T → Bool, radSum σ) * (G * ⟪e, x₀⟫) by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring,
      hsum_rad, zero_mul, ← Finset.mul_sum]
    ring
  have hconst : ∑ _σ : Fin T → Bool, (D * G * Real.sqrt T / (2 * Real.sqrt 3)) ≤
      ∑ σ : Fin T → Bool, ∑ t : Fin T,
        (rademacherLinear e G (σ t) (L.eval σ t) - rademacherLinear e G (σ t) (uOf σ)) := by
    rw [Finset.sum_const, nsmul_eq_mul, card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, hsum_reg,
      show (2 : ℝ) ^ T * (D * G * Real.sqrt T / (2 * Real.sqrt 3)) =
        D * G / 2 * ((2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3)) by
        rw [Real.sqrt_div (Nat.cast_nonneg T)]; ring]
    exact mul_le_mul_of_nonneg_left (khintchine_rademacher_abs_sum T) (by positivity)
  by_contra! hnot
  linarith [Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun σ _ =>
    hnot σ (uOf σ) (by dsimp only [uOf]; split_ifs <;> assumption)]

end LowerBound

end Cslib.MachineLearning.OnlineLearning.OCO
