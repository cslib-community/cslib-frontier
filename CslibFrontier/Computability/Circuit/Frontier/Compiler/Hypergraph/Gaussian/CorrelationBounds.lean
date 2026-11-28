/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Compiler
import all CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.EuclideanSheppard
import all CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.WalkKernel
import CslibFrontier.Foundations.Analysis.InnerProductSpace.Basic

/-!
# Unit Vertex Rows and the Three Correlation Lower Bounds

Private unit row embedding `hyperUnitRow` and the two-step pairwise, one-step spherical-cap
center, and two-step star-cone correlation lower bounds imported via `import all` by
`ParamSelection.lean` and `Layout.lean`.
-/

-- Internal proof-only helpers; downstream parameter-selection and layout modules import all.
set_option linter.privateModule false

public section

namespace Cslib.Circuits.Frontier.Hypergraph

open MeasureTheory ProbabilityTheory Real Set Filter Cslib.Circuits
open scoped RealInnerProductSpace Interval

section BipartiteKernel

variable {σ : Signature} {n : ℕ} (c : Circuit σ n 1) (K₀ : ℕ)

/-! ### Unit vertex rows and the three correlation lower bounds -/

/-- Unit row of vertex `v : HyperNode c` at radius `2 * S`. -/
private noncomputable def hyperUnitRow (r : ℕ) (θ : ℝ) (S : ℕ) (v : HyperNode c) :
    EuclideanSpace ℝ (HyperNode c) :=
  let a := WithLp.toLp 2 (walkMax c K₀ r θ (2 * S) (.inl v))
  ‖a‖⁻¹ • a

private theorem norm_hyperUnitRow (r : ℕ) (θ : ℝ) (S : ℕ) (v : HyperNode c) :
    ‖hyperUnitRow c K₀ r θ S v‖ = 1 := by
  have h1 := one_le_norm_walkMax c K₀ r θ (2 * S) v
  dsimp only [hyperUnitRow]
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (by linarith)]

private theorem hyperUnitRow_nonneg (r : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (S : ℕ) (v z : HyperNode c) :
    0 ≤ hyperUnitRow c K₀ r θ S v z :=
  mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (walkMax_nonneg c K₀ r hθ (2 * S) (.inl v) z)

private theorem inner_hyperUnitRow_nonneg (r : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (S : ℕ)
    (u v : HyperNode c) : 0 ≤ ⟪hyperUnitRow c K₀ r θ S u, hyperUnitRow c K₀ r θ S v⟫ := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  exact Finset.sum_nonneg fun z _ =>
    mul_nonneg (hyperUnitRow_nonneg c K₀ r hθ S v z) (hyperUnitRow_nonneg c K₀ r hθ S u z)

/-- Step-weight product `v → e → w` equals `θ² / √(r (k - 1))`. -/
private theorem stepWeight_mul_stepWeight {r : ℕ} (hr : 2 ≤ r) (θ : ℝ) (e : PrunedEdge c K₀)
    (u v : HyperNode c) :
    stepWeight c K₀ r θ (.inl u) (.inr e) * stepWeight c K₀ r θ (.inr e) (.inl v) =
      θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.val).card : ℝ) - 1)) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk2 : 2 ≤ (hyperEdge c e.val).card := e.property.1
  have hk1 : ((hyperEdge c e.val).card - 1 : ℕ) = ((hyperEdge c e.val).card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have _ := hr
  dsimp only [stepWeight, bipBranch]
  rw [hk1, mul_comm (√(((hyperEdge c e.val).card : ℝ) - 1)) (√(r : ℝ)), div_mul_div_comm,
    mul_self_sqrt (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)), ← sqrt_mul hr0, ← pow_two]

/-- Shared final step of the correlation bounds: if the nonnegative rows `a, b` dominate `q` times
the previous-step rows `b₀, a₀` coordinatewise, the boundary mass where `a > a₀` or `b > b₀` is at
most `E`, and `0 < P ≤ ‖a‖ ‖b‖`, then the normalized inner product is at least
`2 q / (1 + q²) - E / P`. -/
private theorem two_mul_div_sub_le_inner_normalize {ι : Type*} [Fintype ι] {q E P : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {a b a₀ b₀ : ι → ℝ} (ha : ∀ z, 0 ≤ a z) (hb : ∀ z, 0 ≤ b z)
    (hab : ∀ z, q * b₀ z ≤ a z) (hba : ∀ z, q * a₀ z ≤ b z)
    (hE : (∑ z with a₀ z < a z, a z ^ 2) + ∑ z with b₀ z < b z, b z ^ 2 ≤ E)
    (hP : 0 < P) (hPab : P ≤ ‖WithLp.toLp 2 a‖ * ‖WithLp.toLp 2 b‖) :
    2 * q / (1 + q ^ 2) - E / P ≤
      ⟪‖WithLp.toLp 2 a‖⁻¹ • WithLp.toLp 2 a, ‖WithLp.toLp 2 b‖⁻¹ • WithLp.toLp 2 b⟫ := by
  set A := WithLp.toLp 2 a
  set B := WithLp.toLp 2 b
  have hdef : 2 * q / (1 + q ^ 2) * (‖A‖ ^ 2 + ‖B‖ ^ 2) / 2 - ⟪A, B⟫ ≤ E := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    have hrew : 2 * q / (1 + q ^ 2) * ((∑ z, A z ^ 2) + ∑ z, B z ^ 2) / 2 - ∑ z, B z * A z =
        ∑ z, (2 * q / (1 + q ^ 2) * (A z ^ 2 + B z ^ 2) / 2 - A z * B z) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [mul_comm (B _)]
    rw [hrew]
    refine (Finset.sum_le_sum fun z _ =>
      two_mul_div_step_defect_le hq0 hq1 (ha z) (hb z) (hab z) (hba z)).trans ?_
    rwa [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  have hE0 : 0 ≤ E := (add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans hE
  have hκ0 : 0 ≤ 2 * q / (1 + q ^ 2) := by positivity
  have hamgm : 2 * ‖A‖ * ‖B‖ ≤ ‖A‖ ^ 2 + ‖B‖ ^ 2 := by nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
  have hinner : 2 * q / (1 + q ^ 2) * (‖A‖ * ‖B‖) - E ≤ ⟪A, B⟫ := by
    nlinarith [mul_le_mul_of_nonneg_left hamgm hκ0]
  have hEP : E ≤ E / P * (‖A‖ * ‖B‖) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hP]
    exact mul_le_mul_of_nonneg_left hPab hE0
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← mul_inv, inv_mul_eq_div,
    le_div_iff₀ (hP.trans_le hPab), sub_mul]
  linarith

/-- **Two-step pairwise correlation lower bound:** for `S ≥ 1` and `u, v ∈ hyperEdge c e.1`,
`⟪hyperUnitRow u, hyperUnitRow v⟫ ≥ 2 q₂' / (1 + q₂'²) - 4 D θ ^ (4S - 2)` where
`q₂' = θ² / √(r (k - 1))`. -/
private theorem twoStep_le_inner_hyperUnitRow {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {S : ℕ} (hS : 1 ≤ S) (e : PrunedEdge c K₀)
    {u v : HyperNode c} (hu : u ∈ hyperEdge c e.val) (hv : v ∈ hyperEdge c e.val) :
    let q₂' := θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.val).card : ℝ) - 1))
    2 * q₂' / (1 + q₂' ^ 2) - 4 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S - 2) ≤
      ⟪hyperUnitRow c K₀ r θ S u, hyperUnitRow c K₀ r θ S v⟫ := by
  classical
  intro q₂'
  have hq₂'_nn : 0 ≤ q₂' := div_nonneg (sq_nonneg θ) (sqrt_nonneg _)
  have hq₂'_le : q₂' ≤ 1 := by
    have hk2 : (2 : ℝ) ≤ (hyperEdge c e.val).card := by exact_mod_cast e.property.1
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have h1 : (1 : ℝ) ≤ √((r : ℝ) * (((hyperEdge c e.val).card : ℝ) - 1)) :=
      (le_sqrt zero_le_one (by nlinarith)).mpr (by nlinarith)
    exact (div_le_self (sq_nonneg θ) h1).trans (pow_le_one₀ hθ0.le hθ1)
  set m := 2 * S - 2
  have hm2 : m + 2 = 2 * S := by omega
  have hstep {x y : HyperNode c} (hx : x ∈ hyperEdge c e.1) (hy : y ∈ hyperEdge c e.1)
      (z : HyperNode c) :
      q₂' * walkMax c K₀ r θ m (.inl y) z ≤ walkMax c K₀ r θ (2 * S) (.inl x) z := by
    rw [← hm2, show q₂' = stepWeight c K₀ r θ (.inl x) (.inr e) *
        stepWeight c K₀ r θ (.inr e) (.inl y) from
      (stepWeight_mul_stepWeight c K₀ hr θ e x y).symm, mul_assoc]
    exact (mul_le_mul_of_nonneg_left
      (step_mul_walkMax_le c K₀ r θ m (x := .inr e) (y := .inl y) hy z)
      (stepWeight_nonneg c K₀ r hθ0.le _ _)).trans
      (step_mul_walkMax_le c K₀ r θ (m + 1) (x := .inl x) (y := .inr e) hx z)
  have hbu := sum_sq_walkMax_twoStep_strict_le c K₀ hr hfan hθ0 hθ1 m (.inl u)
  have hbv := sum_sq_walkMax_twoStep_strict_le c K₀ hr hfan hθ0 hθ1 m (.inl v)
  have hexp : 2 * m + 2 = 4 * S - 2 := by omega
  rw [hm2, hexp] at hbu hbv
  have h := two_mul_div_sub_le_inner_normalize (E := 4 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S - 2))
    hq₂'_nn hq₂'_le (walkMax_nonneg c K₀ r hθ0.le (2 * S) (.inl u))
    (walkMax_nonneg c K₀ r hθ0.le (2 * S) (.inl v)) (hstep hu hv) (hstep hv hu) (by linarith)
    one_pos (one_mul (1 : ℝ) ▸ mul_le_mul (one_le_norm_walkMax c K₀ r θ (2 * S) u)
      (one_le_norm_walkMax c K₀ r θ (2 * S) v) zero_le_one (norm_nonneg _))
  rw [div_one] at h
  exact h

/-- **One-step vertex-to-hyperedge center correlation lower bound:** for `S ≥ 1` and
`v ∈ hyperEdge c e.1`, there exists a unit center vector `w_e` (independent of `v`) with
`⟪hyperUnitRow v, w_e⟫ ≥ 2 q₁' / (1 + q₁'²) - 2 D θ ^ (4S) / q₁'` where
`q₁' = θ / √(√r * √(k - 1))`. -/
private theorem oneStep_le_inner_hyperUnitRow_center {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {S : ℕ} (hS : 1 ≤ S) (e : PrunedEdge c K₀) :
    let q₁' := stepWeight c K₀ r θ (.inr e) (.inl (Classical.choose
      (Finset.card_pos.mp (Nat.zero_lt_of_lt e.property.1))))
    ∃ w_e : EuclideanSpace ℝ (HyperNode c), ‖w_e‖ = 1 ∧
      ∀ v ∈ hyperEdge c e.val,
        2 * q₁' / (1 + q₁' ^ 2) - 2 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S) / q₁' ≤
          ⟪hyperUnitRow c K₀ r θ S v, w_e⟫ := by
  classical
  set v₀ := Classical.choose (Finset.card_pos.mp (Nat.zero_lt_of_lt e.property.1))
  have hv₀ : v₀ ∈ hyperEdge c e.val :=
    Classical.choose_spec (Finset.card_pos.mp (Nat.zero_lt_of_lt e.property.1))
  intro q₁'
  have hq₁'_eq_all (v : HyperNode c) : stepWeight c K₀ r θ (.inr e) (.inl v) = q₁' ∧
      stepWeight c K₀ r θ (.inl v) (.inr e) = q₁' := by
    dsimp only [q₁', stepWeight, bipBranch]
    exact ⟨rfl, by rw [mul_comm]⟩
  have hq₁'_pos : 0 < q₁' := by
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast Nat.zero_lt_of_lt hr
    have hk_pos : (0 : ℝ) < ((hyperEdge c e.val).card - 1 : ℕ) := by
      exact_mod_cast (show 0 < (hyperEdge c e.val).card - 1 by have := e.property.1; omega)
    dsimp only [q₁', stepWeight, bipBranch]
    exact div_pos hθ0 (sqrt_pos.mpr (mul_pos (sqrt_pos.mpr hk_pos) (sqrt_pos.mpr hr_pos)))
  have hq₁'_le : q₁' ≤ 1 := (stepWeight_le c K₀ hr hθ0.le _ _).trans hθ1
  set m := 2 * S - 1
  have hm1 : m + 1 = 2 * S := by omega
  let b := WithLp.toLp 2 (walkMax c K₀ r θ (2 * S) (.inr e))
  have hb_ge : q₁' ≤ ‖b‖ := by
    have hv₀_val : q₁' ≤ b v₀ := by
      have h1 := step_mul_walkMax_le c K₀ r θ m (x := .inr e) (y := .inl v₀) hv₀ v₀
      have h2 : 1 ≤ walkMax c K₀ r θ m (.inl v₀) v₀ := by
        simpa [walkMax] using walkMax_mono c K₀ r θ (Nat.zero_le m) (.inl v₀) v₀
      rw [hm1, (hq₁'_eq_all v₀).1] at h1
      nlinarith
    have hsq : q₁' ^ 2 ≤ ‖b‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc q₁' ^ 2 ≤ b v₀ ^ 2 := pow_le_pow_left₀ hq₁'_pos.le hv₀_val 2
        _ ≤ ∑ z, b z ^ 2 := Finset.single_le_sum (fun z _ => sq_nonneg _) (Finset.mem_univ v₀)
    nlinarith [norm_nonneg b]
  have hb_pos : 0 < ‖b‖ := hq₁'_pos.trans_le hb_ge
  refine ⟨‖b‖⁻¹ • b, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hb_pos.ne'], ?_⟩
  intro v hv
  have hstep_ve (z : HyperNode c) :
      q₁' * walkMax c K₀ r θ m (.inr e) z ≤ walkMax c K₀ r θ (2 * S) (.inl v) z := by
    rw [← hm1, ← (hq₁'_eq_all v).2]
    exact step_mul_walkMax_le c K₀ r θ m (x := .inl v) (y := .inr e) hv z
  have hstep_ev (z : HyperNode c) :
      q₁' * walkMax c K₀ r θ m (.inl v) z ≤ walkMax c K₀ r θ (2 * S) (.inr e) z := by
    rw [← hm1, ← (hq₁'_eq_all v).1]
    exact step_mul_walkMax_le c K₀ r θ m (x := .inr e) (y := .inl v) hv z
  have hbv := sum_sq_walkMax_strict_le c K₀ hr hfan hθ0 hθ1 m (.inl v)
  have hbe := sum_sq_walkMax_strict_le c K₀ hr hfan hθ0 hθ1 m (.inr e)
  have hexp : 2 * (m + 1) = 4 * S := by omega
  rw [hexp, hm1] at hbv hbe
  exact two_mul_div_sub_le_inner_normalize (E := 2 * (max (r + 1) K₀ : ℝ) * θ ^ (4 * S))
    hq₁'_pos.le hq₁'_le (walkMax_nonneg c K₀ r hθ0.le (2 * S) (.inl v))
    (walkMax_nonneg c K₀ r hθ0.le (2 * S) (.inr e)) hstep_ve hstep_ev (by linarith) hq₁'_pos
    (one_mul q₁' ▸ mul_le_mul (one_le_norm_walkMax c K₀ r θ (2 * S) v) hb_ge hq₁'_pos.le
      (norm_nonneg _))

/-- **Two-step star-cone sum of inner products on `hyperUnitRow`:** when `3 ≤ k` and the perturbed
cone tangent hypotheses hold at `q₂' = θ² / √(r (k - 1))`, the off-diagonal inner products of
`hyperUnitRow` on `hyperEdge c e.1` average at least
`(2 q₂' + (k - 2) q₂'²) / (1 + (k - 1) q₂'²) - 8 √D θ ^ (2S - 1)`. -/
private theorem starCone_le_sum_offDiag_inner_hyperUnitRow {r : ℕ} (hr : 2 ≤ r)
    (hfan : c.FanInAtMost r) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {S : ℕ} (hS : 1 ≤ S)
    (e : PrunedEdge c K₀) (hk : 3 ≤ (hyperEdge c e.val).card)
    (htan_lo : θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.val).card : ℝ) - 1)) ≤
      (1 + (((hyperEdge c e.val).card : ℝ) - 1) *
        (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.val).card : ℝ) - 1))) ^ 2) /
        (hyperEdge c e.val).card)
    (htan_hi : (1 + (((hyperEdge c e.val).card : ℝ) - 1) *
        (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.val).card : ℝ) - 1))) ^ 2) /
        (hyperEdge c e.val).card -
        θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.val).card : ℝ) - 1)) ≤
      2 * (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.val).card : ℝ) - 1))) *
        √((1 + (((hyperEdge c e.val).card : ℝ) - 1) *
          (θ ^ 2 / √((r : ℝ) * (((hyperEdge c e.val).card : ℝ) - 1))) ^ 2) /
          (hyperEdge c e.val).card)) :
    let s := hyperEdge c e.val
    let q₂' := θ ^ 2 / √((r : ℝ) * ((s.card : ℝ) - 1))
    (s.card : ℝ) * ((s.card : ℝ) - 1) *
        ((2 * q₂' + ((s.card : ℝ) - 2) * q₂' ^ 2) / (1 + ((s.card : ℝ) - 1) * q₂' ^ 2) -
          8 * √(max (r + 1) K₀ : ℝ) * θ ^ (2 * S - 1)) ≤
      ∑ p ∈ s.offDiag, ⟪hyperUnitRow c K₀ r θ S p.1, hyperUnitRow c K₀ r θ S p.2⟫ := by
  classical
  intro s q₂'
  have hs_ne : s.Nonempty := Finset.card_pos.mp (show 0 < s.card by dsimp only [s]; omega)
  have hq₂'_pos : 0 < q₂' := by
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast Nat.zero_lt_of_lt hr
    have hk_pos : (0 : ℝ) < (s.card : ℝ) - 1 := by
      have : (3 : ℝ) ≤ s.card := by exact_mod_cast hk
      linarith
    exact div_pos (sq_pos_of_pos hθ0) (sqrt_pos.mpr (mul_pos hr_pos hk_pos))
  set m := 2 * S - 2
  have hm2 : m + 2 = 2 * S := by omega
  let a : HyperNode c → EuclideanSpace ℝ (HyperNode c) :=
    fun v => WithLp.toLp 2 (walkMax c K₀ r θ (2 * S) (.inl v))
  let M : EuclideanSpace ℝ (HyperNode c) :=
    WithLp.toLp 2 fun z => (s.image fun v => walkMax c K₀ r θ m (.inl v) z).max' (hs_ne.image _)
  let b : HyperNode c → EuclideanSpace ℝ (HyperNode c) :=
    fun v => WithLp.toLp 2 fun z => min (a v z) (M z)
  have hle_M_of_mem (v : HyperNode c) (hv : v ∈ s) (z : HyperNode c) :
      walkMax c K₀ r θ m (.inl v) z ≤ M z :=
    Finset.le_max' (s.image fun u => walkMax c K₀ r θ m (.inl u) z)
      (walkMax c K₀ r θ m (.inl v) z) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  have ⟨v₀, hv₀⟩ := hs_ne
  have hM_nn (z : HyperNode c) : 0 ≤ M z :=
    (walkMax_nonneg c K₀ r hθ0.le m (.inl v₀) z).trans (hle_M_of_mem v₀ hv₀ z)
  have hone (n : ℕ) (v : HyperNode c) : 1 ≤ walkMax c K₀ r θ n (.inl v) v := by
    simpa [walkMax] using walkMax_mono c K₀ r θ (Nat.zero_le n) (.inl v) v
  have one_le_norm (x : EuclideanSpace ℝ (HyperNode c)) (v : HyperNode c) (h : 1 ≤ x v) :
      1 ≤ ‖x‖ :=
    h.trans ((Real.le_norm_self _).trans (PiLp.norm_apply_le x v))
  have hM1 : 1 ≤ ‖M‖ := one_le_norm M v₀ ((hone m v₀).trans (hle_M_of_mem v₀ hv₀ v₀))
  have hb1 (v : HyperNode c) (hv : v ∈ s) : 1 ≤ ‖b v‖ :=
    one_le_norm (b v) v (le_min (hone (2 * S) v) ((hone m v).trans (hle_M_of_mem v hv v)))
  have hattain_M (z : HyperNode c) : ∃ v ∈ s, walkMax c K₀ r θ m (.inl v) z = M z :=
    Finset.mem_image.mp (Finset.max'_mem _ (hs_ne.image _))
  have hcone_lo (v : HyperNode c) (hv : v ∈ s) (z : HyperNode c) : q₂' * M z ≤ b v z := by
    obtain ⟨v_star, hv_star, hv_star_eq⟩ := hattain_M z
    have hstep : q₂' * walkMax c K₀ r θ m (.inl v_star) z ≤ a v z := by
      dsimp only [a]
      rw [← hm2, show q₂' = stepWeight c K₀ r θ (.inl v) (.inr e) *
          stepWeight c K₀ r θ (.inr e) (.inl v_star) from
        (stepWeight_mul_stepWeight c K₀ hr θ e v v_star).symm, mul_assoc]
      exact (mul_le_mul_of_nonneg_left
        (step_mul_walkMax_le c K₀ r θ m (x := .inr e) (y := .inl v_star) hv_star z)
        (stepWeight_nonneg c K₀ r hθ0.le _ _)).trans
        (step_mul_walkMax_le c K₀ r θ (m + 1) (x := .inl v) (y := .inr e) hv z)
    rw [hv_star_eq] at hstep
    have hq₂'_le : q₂' ≤ 1 := by
      have hk3 : (3 : ℝ) ≤ s.card := by exact_mod_cast hk
      have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
      have h1 : (1 : ℝ) ≤ √((r : ℝ) * ((s.card : ℝ) - 1)) :=
        (le_sqrt zero_le_one (by nlinarith)).mpr (by nlinarith)
      exact (div_le_self (sq_nonneg θ) h1).trans (pow_le_one₀ hθ0.le hθ1)
    exact le_min hstep (mul_le_of_le_one_left (hM_nn z) hq₂'_le)
  have hcone_hi (v : HyperNode c) (_hv : v ∈ s) (z : HyperNode c) : b v z ≤ M z := min_le_right _ _
  have hattain (z : HyperNode c) : ∃ v ∈ s, b v z = M z := by
    obtain ⟨v_star, hv_star, hv_star_eq⟩ := hattain_M z
    refine ⟨v_star, hv_star, min_eq_right ?_⟩
    rw [← hv_star_eq]
    exact walkMax_mono c K₀ r θ (by omega : m ≤ 2 * S) (.inl v_star) z
  have hstar := starCone_sum_offDiag_inner_le hk hq₂'_pos hM1 hM_nn hb1 hcone_lo hcone_hi hattain
    htan_lo htan_hi
  have hdiff_u (v : HyperNode c) (hv : v ∈ s) :
      ‖hyperUnitRow c K₀ r θ S v - ‖b v‖⁻¹ • b v‖ ≤
        4 * √(max (r + 1) K₀ : ℝ) * θ ^ (2 * S - 1) := by
    have ha_ge : 1 ≤ ‖a v‖ := one_le_norm_walkMax c K₀ r θ (2 * S) v
    have h1 := norm_inv_smul_sub_le ha_ge (hb1 v hv)
    have hnorm_ab_sq : ‖a v - b v‖ ^ 2 ≤ 2 * (max (r + 1) K₀ : ℝ) * θ ^ (2 * m + 2) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      let Bv := Finset.univ.filter fun z =>
        walkMax c K₀ r θ m (.inl v) z < walkMax c K₀ r θ (m + 2) (.inl v) z
      calc ∑ z, (a v z - b v z) ^ 2
          ≤ ∑ z, if z ∈ Bv then walkMax c K₀ r θ (m + 2) (.inl v) z ^ 2 else 0 := by
            refine Finset.sum_le_sum fun z _ => ?_
            by_cases hz : z ∈ Bv
            · rw [ite_eq_left hz]
              have hle1 : 0 ≤ a v z - b v z := sub_nonneg.mpr (min_le_left _ _)
              have hle2 : a v z - b v z ≤ a v z := sub_le_self _
                (le_min (walkMax_nonneg c K₀ r hθ0.le (2 * S) (.inl v) z) (hM_nn z))
              have hsq := pow_le_pow_left₀ hle1 hle2 2
              simpa only [a, hm2] using hsq
            · rw [ite_eq_right hz]
              have heq_m := le_antisymm
                (not_lt.mp fun hlt => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hlt⟩))
                (walkMax_mono c K₀ r θ (by omega) (.inl v) z)
              have hle_M : a v z ≤ M z := by
                dsimp only [a]
                rw [← hm2, heq_m]
                exact hle_M_of_mem v hv z
              simp [show b v z = a v z from min_eq_left hle_M]
        _ = ∑ z ∈ Bv, walkMax c K₀ r θ (m + 2) (.inl v) z ^ 2 := by
            rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        _ ≤ 2 * (max (r + 1) K₀ : ℝ) * θ ^ (2 * m + 2) :=
            sum_sq_walkMax_twoStep_strict_le c K₀ hr hfan hθ0 hθ1 m (.inl v)
    have hnorm_ab : ‖a v - b v‖ ≤ 2 * √(max (r + 1) K₀ : ℝ) * θ ^ (2 * S - 1) := by
      refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (hnorm_ab_sq.trans ?_)
      rw [mul_pow, mul_pow, sq_sqrt (by positivity), show 2 * m + 2 = 2 * (2 * S - 1) by omega,
        pow_mul']
      linarith [(by positivity : 0 ≤ (max (r + 1) K₀ : ℝ) * (θ ^ (2 * S - 1)) ^ 2)]
    dsimp only [hyperUnitRow]
    linarith
  have hp_diff (p : HyperNode c × HyperNode c) (hp : p ∈ s.offDiag) :
      ⟪‖b p.1‖⁻¹ • b p.1, ‖b p.2‖⁻¹ • b p.2⟫ -
          8 * √(max (r + 1) K₀ : ℝ) * θ ^ (2 * S - 1) ≤
        ⟪hyperUnitRow c K₀ r θ S p.1, hyperUnitRow c K₀ r θ S p.2⟫ := by
    obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hp
    have habs := abs_inner_sub_inner_of_norm_eq_one (u₁ := hyperUnitRow c K₀ r θ S p.1)
      (u₂ := ‖b p.1‖⁻¹ • b p.1) (v₁ := hyperUnitRow c K₀ r θ S p.2) (v₂ := ‖b p.2‖⁻¹ • b p.2)
      (by
        have hp1 : 0 < ‖b p.1‖ := zero_lt_one.trans_le (hb1 p.1 h1)
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp1.ne'])
      (norm_hyperUnitRow c K₀ r θ S p.2)
    have hd1 := hdiff_u p.1 h1
    have hd2 := hdiff_u p.2 h2
    linarith [neg_abs_le (⟪hyperUnitRow c K₀ r θ S p.1, hyperUnitRow c K₀ r θ S p.2⟫ -
      ⟪‖b p.1‖⁻¹ • b p.1, ‖b p.2‖⁻¹ • b p.2⟫)]
  have hsum_diff := Finset.sum_le_sum hp_diff
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_diff
  have hoff_card : (s.offDiag.card : ℝ) = (s.card : ℝ) * ((s.card : ℝ) - 1) := by
    rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  rw [hoff_card] at hsum_diff
  linarith


end BipartiteKernel

end Cslib.Circuits.Frontier.Hypergraph
