/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Gaussian.Slepian
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Basic
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Median
import CslibFrontier.Foundations.Analysis.InnerProductSpace.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos
import CslibFrontier.Foundations.Geometry.Euclidean.Angle.Cap
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Pure Euclidean and Combinatorial Helpers for Hypergraph Sheppard Bounds

Private Euclidean normalization, star-cone inner-product lower bounds, and `Measure.pi`
straddling probability bounds used via `import all` by the bipartite Gaussian kernel and
parameter-selection proofs.
-/

-- Internal proof-only helpers; downstream kernel and parameter-selection modules import all.
set_option linter.privateModule false

public section

namespace Cslib.Circuits.Frontier.Hypergraph

open MeasureTheory ProbabilityTheory Real Set Filter Cslib.Circuits
open scoped RealInnerProductSpace Interval

/-! ### Pure Euclidean and combinatorial helpers for Sheppard straddling bounds -/

section Helpers

private theorem norm_inv_smul_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ := by
  have hx0 : 0 < ‖x‖ := zero_lt_one.trans_le hx
  have hy0 : 0 < ‖y‖ := zero_lt_one.trans_le hy
  have hdecomp : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
      ‖x‖⁻¹ • (x - y) + ((‖y‖ - ‖x‖) / (‖x‖ * ‖y‖)) • y := by
    rw [smul_sub]
    have hscal : (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) = ‖x‖⁻¹ - ‖y‖⁻¹ := by
      field_simp
    rw [hscal, sub_smul]
    abel
  rw [hdecomp]
  calc ‖‖x‖⁻¹ • (x - y) + ((‖y‖ - ‖x‖) / (‖x‖ * ‖y‖)) • y‖
      ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖((‖y‖ - ‖x‖) / (‖x‖ * ‖y‖)) • y‖ := norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x - y‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hx0), abs_div, abs_of_pos (mul_pos hx0 hy0),
          div_mul_eq_mul_div, mul_div_mul_right _ _ hy0.ne']
    _ ≤ 1 * ‖x - y‖ + ‖x - y‖ / 1 := by
        gcongr
        · exact inv_le_one_of_one_le₀ hx
        · rw [abs_sub_comm]
          exact abs_norm_sub_norm_le x y
    _ = 2 * ‖x - y‖ := by ring

private theorem abs_inner_sub_inner_of_norm_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u₁ u₂ v₁ v₂ : E} (hu₂ : ‖u₂‖ = 1) (hv₁ : ‖v₁‖ = 1) :
    |⟪u₁, v₁⟫ - ⟪u₂, v₂⟫| ≤ ‖u₁ - u₂‖ + ‖v₁ - v₂‖ := by
  have hdecomp : ⟪u₁, v₁⟫ - ⟪u₂, v₂⟫ = ⟪u₁ - u₂, v₁⟫ + ⟪u₂, v₁ - v₂⟫ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [hdecomp]
  calc |⟪u₁ - u₂, v₁⟫ + ⟪u₂, v₁ - v₂⟫|
      ≤ |⟪u₁ - u₂, v₁⟫| + |⟪u₂, v₁ - v₂⟫| := abs_add_le _ _
    _ ≤ ‖u₁ - u₂‖ * ‖v₁‖ + ‖u₂‖ * ‖v₁ - v₂‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = ‖u₁ - u₂‖ + ‖v₁ - v₂‖ := by rw [hv₁, hu₂, mul_one, one_mul]

/-- Pointwise step-defect inequality shared by the 1-step and 2-step kernel inner-product bounds. -/
private theorem two_mul_div_step_defect_le {q a b a₀ b₀ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : q * b₀ ≤ a) (hba : q * a₀ ≤ b) :
    2 * q / (1 + q ^ 2) * (a ^ 2 + b ^ 2) / 2 - a * b ≤
      (if a₀ < a then a ^ 2 else 0) + (if b₀ < b then b ^ 2 else 0) := by
  have havg : 2 * q / (1 + q ^ 2) * (a ^ 2 + b ^ 2) / 2 - a * b ≤
      (a ^ 2 + b ^ 2) / 2 :=
    (sub_le_self _ (mul_nonneg ha hb)).trans <| div_le_div_of_nonneg_right
      (mul_le_of_le_one_left (by positivity) (Gaussian.two_mul_div_one_add_sq_le_one q))
      (by norm_num)
  have hleft : 0 ≤ if a₀ < a then a ^ 2 else 0 := by split <;> positivity
  have hright : 0 ≤ if b₀ < b then b ^ 2 else 0 := by split <;> positivity
  by_cases hqa : q * a ≤ b
  · by_cases hqb : q * b ≤ a
    · have hden : 0 < 1 + q ^ 2 := by positivity
      have hprod := mul_nonneg (sub_nonneg.mpr hqb) (sub_nonneg.mpr hqa)
      calc 2 * q / (1 + q ^ 2) * (a ^ 2 + b ^ 2) / 2 - a * b
          = -((a - q * b) * (b - q * a)) / (1 + q ^ 2) := by field_simp; ring
        _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hprod) hden.le
        _ ≤ _ := add_nonneg hleft hright
    · have hlt : b₀ < b :=
        lt_of_not_ge fun h => hqb ((mul_le_mul_of_nonneg_left h hq0).trans hab)
      have hab' : a ≤ b := (lt_of_not_ge hqb).le.trans (mul_le_of_le_one_left hb hq1)
      rw [ite_eq_left hlt]
      exact havg.trans ((by linarith [pow_le_pow_left₀ ha hab' 2] : _ ≤ b ^ 2).trans
        (le_add_of_nonneg_left hleft))
  · have hlt : a₀ < a :=
      lt_of_not_ge fun h => hqa ((mul_le_mul_of_nonneg_left h hq0).trans hba)
    have hba' : b ≤ a := (lt_of_not_ge hqa).le.trans (mul_le_of_le_one_left ha hq1)
    rw [ite_eq_left hlt]
    exact havg.trans ((by linarith [pow_le_pow_left₀ hb hba' 2] : _ ≤ a ^ 2).trans
      (le_add_of_nonneg_right hright))

private theorem sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {A B : Finset α} {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
  have h1 := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have h2 : 0 ≤ ∑ x ∈ A ∩ B, f x := Finset.sum_nonneg fun x _ => hf x
  linarith

/-- Tangent lower bound for `x + q / x` on `(0, 1]` at `x₀` when `q ≤ x₀²` and
`x₀² - q ≤ 2 q x₀`. -/
private theorem tangent_le_add_div {q x₀ x : ℝ} (_hq : 0 < q) (hx₀ : 0 < x₀) (hx0 : 0 < x)
    (hx1 : x ≤ 1) (hlo : q ≤ x₀ ^ 2) (hhi : x₀ ^ 2 - q ≤ 2 * q * x₀) :
    (x₀ + q / x₀) + (x₀ ^ 2 - q) / (2 * x₀ ^ 3) * (x ^ 2 - x₀ ^ 2) ≤ x + q / x := by
  have hden : 0 < 2 * x * x₀ ^ 3 := by positivity
  suffices h : 0 ≤ ((x + q / x) - ((x₀ + q / x₀) +
      (x₀ ^ 2 - q) / (2 * x₀ ^ 3) * (x ^ 2 - x₀ ^ 2))) * (2 * x * x₀ ^ 3) by
    have h0 := nonneg_of_mul_nonneg_left h hden
    linarith
  have hfac : ((x + q / x) - ((x₀ + q / x₀) +
      (x₀ ^ 2 - q) / (2 * x₀ ^ 3) * (x ^ 2 - x₀ ^ 2))) * (2 * x * x₀ ^ 3) =
      (x - x₀) ^ 2 * (2 * q * x₀ - (x₀ ^ 2 - q) * x) := by
    field_simp
    ring
  rw [hfac]
  refine mul_nonneg (sq_nonneg _) ?_
  have hsub : 0 ≤ x₀ ^ 2 - q := sub_nonneg.mpr hlo
  have hmul : (x₀ ^ 2 - q) * x ≤ (x₀ ^ 2 - q) * 1 := mul_le_mul_of_nonneg_left hx1 hsub
  linarith

/-- Pointwise quadratic cone inequality: `q M ≤ b ≤ M` implies `(1 + q) b M ≥ b² + q M²`. -/
private theorem mul_le_one_add_mul_of_mem_cone {q b M : ℝ} (hlo : q * M ≤ b) (hhi : b ≤ M) :
    b ^ 2 + q * M ^ 2 ≤ (1 + q) * (b * M) := by
  have hprod : 0 ≤ (b - q * M) * (M - b) := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith

/-- **Star-cone sum of inner products.** Given `s : Finset κ` with `k = s.card ≥ 3`, nonnegative
envelope `M : EuclideanSpace ℝ V` (`1 ≤ ‖M‖`), and vectors `b : κ → EuclideanSpace ℝ V`
(`1 ≤ ‖b v‖`) satisfying `q M(z) ≤ b v z ≤ M(z)` at every coordinate `z` with one `v* ∈ s`
attaining `b v* z = M(z)`, the normalized vectors `u v = ‖b v‖⁻¹ • b v` satisfy
`∑ p ∈ s.offDiag, ⟪u p.1, u p.2⟫ ≥ k (k - 1) (2 q + (k - 2) q²) / (1 + (k - 1) q²)` whenever the
cone tangent hypotheses hold. -/
private theorem starCone_sum_offDiag_inner_le {V κ : Type*} [Fintype V]
    {s : Finset κ} (hs : 3 ≤ s.card) {q : ℝ} (hq0 : 0 < q)
    {M : EuclideanSpace ℝ V} (hM1 : 1 ≤ ‖M‖) (hM_nn : ∀ z : V, 0 ≤ M z)
    {b : κ → EuclideanSpace ℝ V} (hb1 : ∀ v ∈ s, 1 ≤ ‖b v‖)
    (hcone_lo : ∀ v ∈ s, ∀ z : V, q * M z ≤ b v z)
    (hcone_hi : ∀ v ∈ s, ∀ z : V, b v z ≤ M z)
    (hattain : ∀ z : V, ∃ v ∈ s, b v z = M z)
    (htan_lo : q ≤ (1 + ((s.card : ℝ) - 1) * q ^ 2) / (s.card : ℝ))
    (htan_hi : (1 + ((s.card : ℝ) - 1) * q ^ 2) / (s.card : ℝ) - q ≤
      2 * q * √((1 + ((s.card : ℝ) - 1) * q ^ 2) / (s.card : ℝ))) :
    (s.card : ℝ) * ((s.card : ℝ) - 1) *
        ((2 * q + ((s.card : ℝ) - 2) * q ^ 2) / (1 + ((s.card : ℝ) - 1) * q ^ 2)) ≤
      ∑ p ∈ s.offDiag, ⟪‖b p.1‖⁻¹ • b p.1, ‖b p.2‖⁻¹ • b p.2⟫ := by
  classical
  set k : ℝ := (s.card : ℝ)
  have hk3 : (3 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hs
  have hk_pos : 0 < k := by linarith
  have hk1 : 0 ≤ k - 1 := by linarith
  have hM_pos : 0 < ‖M‖ := zero_lt_one.trans_le hM1
  have hM_sq_pos : 0 < ‖M‖ ^ 2 := sq_pos_of_pos hM_pos
  set w : EuclideanSpace ℝ V := ‖M‖⁻¹ • M
  have hw_norm : ‖w‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hM_pos.ne']
  let u : κ → EuclideanSpace ℝ V := fun v => ‖b v‖⁻¹ • b v
  have hu_norm (v : κ) (hv : v ∈ s) : ‖u v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (zero_lt_one.trans_le (hb1 v hv)).ne']
  set Q₀ : ℝ := (1 + (k - 1) * q ^ 2) / k
  have hQ₀_pos : 0 < Q₀ := lt_of_lt_of_le hq0 htan_lo
  set x₀ : ℝ := √Q₀
  have hx₀_pos : 0 < x₀ := sqrt_pos.mpr hQ₀_pos
  have hx₀_sq : x₀ ^ 2 = Q₀ := sq_sqrt hQ₀_pos.le
  let x : κ → ℝ := fun v => ‖b v‖ / ‖M‖
  have hx_pos (v : κ) (hv : v ∈ s) : 0 < x v :=
    div_pos (zero_lt_one.trans_le (hb1 v hv)) hM_pos
  have hx_le_one (v : κ) (hv : v ∈ s) : x v ≤ 1 := by
    rw [div_le_one hM_pos]
    have hsq : ‖b v‖ ^ 2 ≤ ‖M‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_le_sum fun z _ => ?_
      have hb0 : 0 ≤ b v z := (mul_nonneg hq0.le (hM_nn z)).trans (hcone_lo v hv z)
      exact pow_le_pow_left₀ hb0 (hcone_hi v hv z) 2
    nlinarith [norm_nonneg (b v)]
  have hinner_ge (v : κ) (hv : v ∈ s) : (x v + q / x v) / (1 + q) ≤ ⟪u v, w⟫ := by
    have hbv_pos : 0 < ‖b v‖ := zero_lt_one.trans_le (hb1 v hv)
    have hsum : ‖b v‖ ^ 2 + q * ‖M‖ ^ 2 ≤ (1 + q) * ⟪b v, M⟫ := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply]
      simp only [RCLike.inner_apply, conj_trivial]
      calc (∑ z, b v z ^ 2) + q * ∑ z, M z ^ 2
          = ∑ z, (b v z ^ 2 + q * M z ^ 2) := by rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        _ ≤ ∑ z, (1 + q) * (b v z * M z) :=
            Finset.sum_le_sum fun z _ =>
              mul_le_one_add_mul_of_mem_cone (hcone_lo v hv z) (hcone_hi v hv z)
        _ = (1 + q) * ∑ z, M z * b v z := by
            rw [← Finset.mul_sum]
            exact congrArg ((1 + q) * ·) (Finset.sum_congr rfl fun z _ => mul_comm _ _)
    rw [real_inner_smul_left, real_inner_smul_right]
    have hxv_pos := hx_pos v hv
    have hcalc : (x v + q / x v) / (1 + q) =
        (‖b v‖ ^ 2 + q * ‖M‖ ^ 2) / ((1 + q) * ‖b v‖ * ‖M‖) := by
      dsimp only [x]
      field_simp
    rw [hcalc, div_le_iff₀ (by positivity)]
    have h1 : ‖b v‖⁻¹ * (‖M‖⁻¹ * ⟪b v, M⟫) * ((1 + q) * ‖b v‖ * ‖M‖) = (1 + q) * ⟪b v, M⟫ := by
      field_simp
    linarith
  have hsum_x_sq : k * x₀ ^ 2 ≤ ∑ v ∈ s, x v ^ 2 := by
    have hcoord (z : V) : (1 + (k - 1) * q ^ 2) * M z ^ 2 ≤ ∑ v ∈ s, b v z ^ 2 := by
      obtain ⟨v₀, hv₀, hbv₀⟩ := hattain z
      rw [← Finset.add_sum_erase _ _ hv₀, hbv₀]
      have hrest : ∑ _v ∈ s.erase v₀, q ^ 2 * M z ^ 2 ≤ ∑ v ∈ s.erase v₀, b v z ^ 2 := by
        refine Finset.sum_le_sum fun v hv => ?_
        have hvs := Finset.mem_of_mem_erase hv
        exact (mul_pow q (M z) 2).symm.trans_le
          (pow_le_pow_left₀ (mul_nonneg hq0.le (hM_nn z)) (hcone_lo v hvs z) 2)
      have herase_card : ((s.erase v₀).card : ℝ) = k - 1 := by
        rw [Finset.card_erase_of_mem hv₀, Nat.cast_sub (by omega), Nat.cast_one]
      have hconst : ∑ _v ∈ s.erase v₀, q ^ 2 * M z ^ 2 = (k - 1) * q ^ 2 * M z ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, herase_card, mul_assoc]
      linarith
    have hsum_b : (1 + (k - 1) * q ^ 2) * ‖M‖ ^ 2 ≤ ∑ v ∈ s, ‖b v‖ ^ 2 := by
      simp_rw [EuclideanSpace.real_norm_sq_eq]
      rw [Finset.mul_sum, Finset.sum_comm]
      exact Finset.sum_le_sum fun z _ => hcoord z
    have hkx₀ : k * x₀ ^ 2 = 1 + (k - 1) * q ^ 2 := by rw [hx₀_sq]; dsimp only [Q₀]; field_simp
    calc k * x₀ ^ 2
        = ((1 + (k - 1) * q ^ 2) * ‖M‖ ^ 2) / ‖M‖ ^ 2 := by
          rw [hkx₀, mul_div_cancel_right₀ _ hM_sq_pos.ne']
      _ ≤ (∑ v ∈ s, ‖b v‖ ^ 2) / ‖M‖ ^ 2 := div_le_div_of_nonneg_right hsum_b hM_sq_pos.le
      _ = ∑ v ∈ s, x v ^ 2 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun v _ => (div_pow (‖b v‖) ‖M‖ 2).symm
  have hsum_tang : k * ((x₀ + q / x₀) / (1 + q)) ≤ ∑ v ∈ s, ⟪u v, w⟫ := by
    set slope := (x₀ ^ 2 - q) / (2 * x₀ ^ 3)
    have hslope_nn : 0 ≤ slope := div_nonneg (sub_nonneg.mpr (hx₀_sq ▸ htan_lo)) (by positivity)
    have hpt (v : κ) (hv : v ∈ s) :
        ((x₀ + q / x₀) + slope * (x v ^ 2 - x₀ ^ 2)) / (1 + q) ≤ ⟪u v, w⟫ :=
      (div_le_div_of_nonneg_right (tangent_le_add_div hq0 hx₀_pos (hx_pos v hv) (hx_le_one v hv)
        (hx₀_sq ▸ htan_lo) (by simpa only [hx₀_sq] using htan_hi)) (by positivity)).trans
        (hinner_ge v hv)
    calc k * ((x₀ + q / x₀) / (1 + q))
        ≤ (k * (x₀ + q / x₀) + slope * ((∑ v ∈ s, x v ^ 2) - k * x₀ ^ 2)) / (1 + q) := by
          rw [add_div (k * (x₀ + q / x₀)), mul_div_assoc]
          have hnn : 0 ≤ slope * ((∑ v ∈ s, x v ^ 2) - k * x₀ ^ 2) / (1 + q) :=
            div_nonneg (mul_nonneg hslope_nn (sub_nonneg.mpr hsum_x_sq)) (by positivity)
          linarith [hnn]
      _ = ∑ v ∈ s, ((x₀ + q / x₀) + slope * (x v ^ 2 - x₀ ^ 2)) / (1 + q) := by
          rw [← Finset.sum_div]
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
            Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ s, ⟪u v, w⟫ := Finset.sum_le_sum hpt
  have hsimp_tang : k * ((x₀ + q / x₀) / (1 + q)) = (1 + (k - 1) * q) / x₀ := by
    have hnum_id : k * (x₀ ^ 2 + q) = (1 + q) * (1 + (k - 1) * q) := by
      rw [hx₀_sq]; dsimp only [Q₀]; field_simp; ring
    rw [show x₀ + q / x₀ = (x₀ ^ 2 + q) / x₀ by field_simp]
    field_simp
    linarith
  rw [hsimp_tang] at hsum_tang
  have hnorm_sum : (1 + (k - 1) * q) / x₀ ≤ ‖∑ v ∈ s, u v‖ :=
    hsum_tang.trans ((sum_inner (𝕜 := ℝ) s u w).symm.trans_le
      ((real_inner_le_norm _ w).trans_eq (by rw [hw_norm, mul_one])))
  have h0_lhs : 0 ≤ (1 + (k - 1) * q) / x₀ := by positivity
  have hsq_sum := mul_le_mul hnorm_sum hnorm_sum h0_lhs (h0_lhs.trans hnorm_sum)
  have hexp := norm_sum_sq_real s u
  have hdiag : ∑ v ∈ s, ‖u v‖ ^ 2 = k := by
    rw [Finset.sum_congr rfl fun v hv => by rw [hu_norm v hv, one_pow], Finset.sum_const,
      nsmul_one]
  have hident : ((1 + (k - 1) * q) / x₀) ^ 2 - k =
      k * (k - 1) * ((2 * q + (k - 2) * q ^ 2) / (1 + (k - 1) * q ^ 2)) := by
    rw [div_pow, hx₀_sq]
    dsimp only [Q₀]
    have hden_pos : 0 < 1 + (k - 1) * q ^ 2 := by positivity
    field_simp
    ring
  linarith [sq (‖∑ v ∈ s, u v‖), sq ((1 + (k - 1) * q) / x₀)]

/-- **Combinatorial Sheppard bound for hyperedge straddling.** If `s : Finset V` (`2 ≤ s.card`) has
unit vectors `u : V → EuclideanSpace ℝ V` whose angles over `s.offDiag` sum to at most
`s.card * (s.card - 1) * θ_avg`, then for every threshold `t : ℝ`, `s` straddles `t` under
standard Gaussian projections with probability at most `(s.card / (2 π)) * θ_avg`. -/
private theorem measureReal_straddlesOn_le_of_sum_angle {V : Type*} [Fintype V]
    {s : Finset V} (hs : 2 ≤ s.card) {u : V → EuclideanSpace ℝ V} (hu : ∀ v ∈ s, ‖u v‖ = 1)
    {θ_avg : ℝ}
    (hangle : open Classical in ∑ p ∈ s.offDiag, InnerProductGeometry.angle (u p.1) (u p.2) ≤
      (s.card : ℝ) * ((s.card : ℝ) - 1) * θ_avg)
    (t : ℝ) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real
        {ω | StraddlesOn (fun v => ⟪u v, WithLp.toLp 2 ω⟫) t ↑s} ≤
      (s.card : ℝ) / (2 * π) * θ_avg := by
  classical
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  let score : (V → ℝ) → V → ℝ := fun ω v => ⟪u v, WithLp.toLp 2 ω⟫
  have hmeas_score (v : V) : Measurable fun ω : V → ℝ => score ω v := by
    dsimp only [score]
    fun_prop
  set E : Set (V → ℝ) := {ω | StraddlesOn (score ω) t ↑s}
  have hmeas_E : MeasurableSet E := by
    have heq : E = (⋃ v ∈ s, {ω | score ω v < t}) ∩ (⋃ v ∈ s, {ω | t ≤ score ω v}) := by
      ext ω
      simp [E, StraddlesOn]
    rw [heq]
    exact (s.measurableSet_biUnion fun v _ =>
      measurableSet_lt (hmeas_score v) measurable_const).inter
      (s.measurableSet_biUnion fun v _ => measurableSet_le measurable_const (hmeas_score v))
  let sepSet (p : V × V) : Set (V → ℝ) := {ω | t ∈ Ι (score ω p.1) (score ω p.2)}
  have hmeas_sep (p : V × V) : MeasurableSet (sepSet p) :=
    measurableSet_setOf_mem_uIoc (hmeas_score p.1) (hmeas_score p.2) t
  have hpt (ω : V → ℝ) :
      2 * ((s.card : ℝ) - 1) * E.indicator (fun _ => (1 : ℝ)) ω ≤
        ∑ p ∈ s.offDiag, (sepSet p).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      obtain ⟨⟨u₁, hu₁s, hu₁lt⟩, ⟨u₂, hu₂s, hu₂ge⟩⟩ := hω
      let L := s.filter fun v => score ω v < t
      let U := s.filter fun v => t ≤ score ω v
      have hL_pos : 1 ≤ L.card :=
        Finset.card_pos.mpr ⟨u₁, Finset.mem_filter.mpr ⟨hu₁s, hu₁lt⟩⟩
      have hU_pos : 1 ≤ U.card :=
        Finset.card_pos.mpr ⟨u₂, Finset.mem_filter.mpr ⟨hu₂s, hu₂ge⟩⟩
      have hLU_card : L.card + U.card = s.card := by
        have hpart := Finset.card_filter_add_card_filter_not (s := s) (fun v => score ω v < t)
        have hU_eq : (s.filter fun v => ¬score ω v < t) = U := by
          ext v
          simp [U]
        rwa [hU_eq] at hpart
      let active := s.offDiag.filter fun p => t ∈ Ι (score ω p.1) (score ω p.2)
      have hsub1 : L ×ˢ U ⊆ active := by
        rintro ⟨a, b⟩ hab
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
        obtain ⟨has, halt⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbs, hbge⟩ := Finset.mem_filter.mp hb
        have hab_ne : a ≠ b := fun h => by subst h; linarith
        dsimp only [active]
        refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨has, hbs, hab_ne⟩, ?_⟩
        rw [uIoc_of_le (halt.le.trans hbge)]
        exact ⟨halt, hbge⟩
      have hsub2 : U ×ˢ L ⊆ active := by
        rintro ⟨b, a⟩ hba
        obtain ⟨hb, ha⟩ := Finset.mem_product.mp hba
        obtain ⟨hbs, hbge⟩ := Finset.mem_filter.mp hb
        obtain ⟨has, halt⟩ := Finset.mem_filter.mp ha
        have hba_ne : b ≠ a := fun h => by subst h; linarith
        dsimp only [active]
        refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hbs, has, hba_ne⟩, ?_⟩
        rw [uIoc_comm, uIoc_of_le (halt.le.trans hbge)]
        exact ⟨halt, hbge⟩
      have hdisj : Disjoint (L ×ˢ U) (U ×ˢ L) := by
        rw [Finset.disjoint_left]
        rintro ⟨a, b⟩ h1 h2
        have halt := (Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2
        have hage := (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2
        linarith
      have hcard_act : 2 * (s.card - 1) ≤ active.card := by
        have hs1 : s.card = (s.card - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
        calc 2 * (s.card - 1) ≤ L.card * U.card + U.card * L.card := by nlinarith
          _ = (L ×ˢ U ∪ U ×ˢ L).card := by
              rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product]
          _ ≤ active.card := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
      have hsum_ind : ∑ p ∈ s.offDiag, (sepSet p).indicator (fun _ => (1 : ℝ)) ω = active.card := by
        have hcongr : ∑ p ∈ s.offDiag, (sepSet p).indicator (fun _ => (1 : ℝ)) ω =
            ∑ p ∈ s.offDiag, if t ∈ Ι (score ω p.1) (score ω p.2) then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl fun p _ => by simp [sepSet, indicator]
        rw [hcongr, Finset.sum_boole]
      rw [hsum_ind, mul_one]
      have hcast : (2 : ℝ) * ((s.card : ℝ) - 1) = ((2 * (s.card - 1) : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast]
      exact_mod_cast hcard_act
    · rw [indicator_of_notMem hω, mul_zero]
      exact Finset.sum_nonneg fun p _ => indicator_nonneg (fun _ _ => zero_le_one) ω
  have hint_lhs : Integrable (fun ω => 2 * ((s.card : ℝ) - 1) *
      E.indicator (fun _ => (1 : ℝ)) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hmeas_E).const_mul _
  have hint_rhs : ∀ p ∈ s.offDiag,
      Integrable (fun ω => (sepSet p).indicator (fun _ => (1 : ℝ)) ω) P :=
    fun p _ => (integrable_const (1 : ℝ)).indicator (hmeas_sep p)
  have hint_le := integral_mono hint_lhs (integrable_finsetSum _ hint_rhs) hpt
  rw [integral_const_mul, integral_indicator_const _ hmeas_E, smul_eq_mul, mul_one,
    integral_finsetSum _ hint_rhs] at hint_le
  have hsum_prob : ∑ p ∈ s.offDiag, ∫ ω, (sepSet p).indicator (fun _ => (1 : ℝ)) ω ∂P ≤
      ((s.card : ℝ) * ((s.card : ℝ) - 1) * θ_avg) / π := by
    calc ∑ p ∈ s.offDiag, ∫ ω, (sepSet p).indicator (fun _ => (1 : ℝ)) ω ∂P
        = ∑ p ∈ s.offDiag, P.real (sepSet p) :=
          Finset.sum_congr rfl fun p _ => by
            rw [integral_indicator_const _ (hmeas_sep p), smul_eq_mul, mul_one]
      _ ≤ ∑ p ∈ s.offDiag, InnerProductGeometry.angle (u p.1) (u p.2) / π :=
          Finset.sum_le_sum fun p hp => by
            obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hp
            exact Gaussian.measureReal_mem_uIoc_le ((hu p.1 h1).trans (hu p.2 h2).symm) t
      _ = (∑ p ∈ s.offDiag, InnerProductGeometry.angle (u p.1) (u p.2)) / π :=
          (Finset.sum_div _ _ _).symm
      _ ≤ ((s.card : ℝ) * ((s.card : ℝ) - 1) * θ_avg) / π :=
          div_le_div_of_nonneg_right hangle pi_pos.le
  have hk1_pos : (0 : ℝ) < (s.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ s.card := by exact_mod_cast hs
    linarith
  have hcomb := (le_div_iff₀ pi_pos).mp (hint_le.trans hsum_prob)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

end Helpers

end Cslib.Circuits.Frontier.Hypergraph
