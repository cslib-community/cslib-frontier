/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Peer-to-peer generosity equilibria, penalties, and welfare tradeoffs

This module formalizes the equilibrium and welfare analysis of peer-to-peer sharing under free
riding, service differentiation, and exclusion from [BabaioffChuangFeldman2007] (NRTV Chapter 23,
§23.3):

* **Minimalist generosity model (§23.3.1, Claim 23.1)**:
  `generosityEquilibrium`, `uniformTail`, `unifHighRoot`, `unifLowRoot`, complete threshold
  characterization `uniformEquilibrium_iff` (positive equilibria exist iff `4 ≤ θ_m`, collapsing
  from `1 / 2` to `0` below `4`), `uniform_stability` (showing `unifHighRoot` is locally stable
  while `unifLowRoot` is unstable), strict monotonicity `unifHighRoot_strictMono` and convergence
  to `1` (`unifHighRoot_tendsto_one`), alongside linear welfare scaling
  `minimalistWelfare α x = α * x - 1`.
* **Mixture generosity distributions (NRTV Exercise 23.1)**:
  `mixtureTail θ_m φ` (mixing uniform `[0, θ_m]` with point masses at `0` and `θ_m`),
  `mixLowRoot`, `mixHighRoot`, complete equilibrium characterization `mixtureEquilibrium_iff`, and
  two-regime existence threshold `exists_mixtureEquilibrium_iff` (`16 * φ / (1 + φ) ^ 2 ≤ θ_m`
  when `1 / 3 ≤ φ`, versus `2 / (1 - φ) ≤ θ_m` when `0 < φ < 1 / 3`), while capping equilibrium
  cooperation at `(1 + φ) / 2 < 1` for `φ < 1` (`mixture_upper_bound`).
* **Service differentiation and exclusion (§23.3.2, Claim 23.2, Exercise 23.2)**:
  `requestLoad`, `serviceRate`, `penaltyThreshold`, `penaltyEquilibrium`, and Claim 23.2
  (`fullCooperation_penalty_threshold`: penalty `p ≥ 1 / α` sustains `x = 1` for every nonnegative
  generosity distribution), together with uniform exclusion `exclEquilibrium`, threshold reduction
  `4 * (1 - z) ≤ θ_m`, rescue of subcritical networks (`θ_m < 4`), and a concrete comparison
  showing exclusion can strictly decrease social welfare (`excl_can_reduce_welfare`).

## References

* [M. Babaioff, J. Chuang, and M. Feldman, *Incentives in Peer-to-Peer
  Systems*][BabaioffChuangFeldman2007] (NRTV Chapter 23; exact source theorem/page locators
  unverified against the printed book beyond #7789's chapter index).
-/

public section

namespace Cslib.GameTheory.P2P

/-! ### Minimalist generosity model (NRTV §23.3.1) -/

/-- A positive equilibrium contribution fraction `x ∈ (0, 1]` under generosity tail distribution
`tail` (fraction of peers willing to bear net cost at least `t`): `x = tail (1 / x)`. -/
@[expose] def generosityEquilibrium (tail : ℝ → ℝ) (x : ℝ) : Prop :=
  0 < x ∧ x ≤ 1 ∧ x = tail (1 / x)

/-- Per-capita net welfare in the minimalist sharing model with per-service benefit `α` and
contributing fraction `x`: expected service benefit `α * x` minus total normalized request cost
`1`. -/
def minimalistWelfare (α x : ℝ) : ℝ :=
  α * x - 1

theorem minimalistWelfare_eq (α x : ℝ) : minimalistWelfare α x = α * x - 1 := by
  rfl

/-- Survival (tail) function `P(θ ≥ t)` of the uniform generosity distribution on `[0, θ_m]`. -/
noncomputable def uniformTail (θ_m t : ℝ) : ℝ :=
  if t ≤ 0 then 1 else if t ≤ θ_m then 1 - t / θ_m else 0

@[simp]
theorem uniformTail_of_le_zero {θ_m t : ℝ} (ht : t ≤ 0) : uniformTail θ_m t = 1 := by
  simp [uniformTail, ht]

theorem uniformTail_nonneg {θ_m : ℝ} (hθ : 0 < θ_m) (t : ℝ) : 0 ≤ uniformTail θ_m t := by
  dsimp [uniformTail]
  split_ifs with h0 ht
  · norm_num
  · linarith [(div_le_one hθ).mpr ht]
  · exact le_rfl

theorem uniformTail_le_one {θ_m : ℝ} (hθ : 0 < θ_m) (t : ℝ) : uniformTail θ_m t ≤ 1 := by
  dsimp [uniformTail]
  split_ifs with h0 ht
  · exact le_rfl
  · linarith [div_nonneg (lt_of_not_ge h0).le hθ.le]
  · norm_num

theorem uniformTail_antitone {θ_m : ℝ} (hθ : 0 < θ_m) : Antitone (uniformTail θ_m) := by
  intro t₁ t₂ hle
  by_cases h1 : t₁ ≤ 0
  · rw [uniformTail_of_le_zero h1]
    exact uniformTail_le_one hθ t₂
  · have ht1_pos : 0 < t₁ := lt_of_not_ge h1
    have h2 : ¬ t₂ ≤ 0 := not_le.mpr (lt_of_lt_of_le ht1_pos hle)
    by_cases h2θ : t₂ ≤ θ_m
    · simp only [uniformTail, h1, h2, hle.trans h2θ, h2θ, ↓reduceIte]
      linarith [div_le_div_of_nonneg_right hle hθ.le]
    · simp only [uniformTail, h2, h2θ, ↓reduceIte]
      exact uniformTail_nonneg hθ t₁

theorem uniformTail_of_pos_le {θ_m t : ℝ} (ht0 : 0 < t) (htθ : t ≤ θ_m) :
    uniformTail θ_m t = 1 - t / θ_m := by
  simp [uniformTail, ht0.not_ge, htθ]

theorem uniformTail_of_gt {θ_m t : ℝ} (ht0 : 0 < t) (htθ : θ_m < t) :
    uniformTail θ_m t = 0 := by
  simp [uniformTail, ht0.not_ge, htθ.not_ge]

/-- Upper positive equilibrium contribution root `(θ_m + √(θ_m (θ_m - 4))) / (2 θ_m)` of the
uniform generosity model (NRTV Claim 23.1). -/
noncomputable def unifHighRoot (θ_m : ℝ) : ℝ :=
  (θ_m + Real.sqrt (θ_m * (θ_m - 4))) / (2 * θ_m)

theorem unifHighRoot_eq (θ_m : ℝ) :
    unifHighRoot θ_m = (θ_m + Real.sqrt (θ_m * (θ_m - 4))) / (2 * θ_m) := by
  rfl

/-- Lower positive equilibrium contribution root `(θ_m - √(θ_m (θ_m - 4))) / (2 θ_m)` of the
uniform generosity model (NRTV Claim 23.1). -/
noncomputable def unifLowRoot (θ_m : ℝ) : ℝ :=
  (θ_m - Real.sqrt (θ_m * (θ_m - 4))) / (2 * θ_m)

theorem unifLowRoot_eq (θ_m : ℝ) :
    unifLowRoot θ_m = (θ_m - Real.sqrt (θ_m * (θ_m - 4))) / (2 * θ_m) := by
  rfl

private theorem quad_sol_iff {a b c x : ℝ} (ha : 0 < a) (hdisc : 0 ≤ b ^ 2 - 4 * a * c) :
    a * x ^ 2 - b * x + c = 0 ↔
      x = (b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) ∨
        x = (b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
  set d := Real.sqrt (b ^ 2 - 4 * a * c)
  have hd : d ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt hdisc
  have hfac : 4 * a * (a * x ^ 2 - b * x + c) =
      (2 * a * x - (b - d)) * (2 * a * x - (b + d)) := by linarith
  have h2a : 2 * a ≠ 0 := by positivity
  rw [← mul_right_inj' (show 4 * a ≠ 0 by positivity), mul_zero, hfac, mul_eq_zero, sub_eq_zero,
    sub_eq_zero, eq_div_iff h2a, eq_div_iff h2a, mul_comm x]

/-- Root identities and bounds for `unifLowRoot` and `unifHighRoot` when `4 ≤ θ_m`. -/
theorem unifRoot_props {θ_m : ℝ} (hθ : 4 ≤ θ_m) :
    0 < unifLowRoot θ_m ∧ unifLowRoot θ_m ≤ unifHighRoot θ_m ∧ unifHighRoot θ_m < 1 := by
  have hθ_pos : 0 < θ_m := by linarith
  have h2θ : 0 < 2 * θ_m := by positivity
  have hsq : Real.sqrt (θ_m * (θ_m - 4)) < θ_m := (Real.sqrt_lt' hθ_pos).mpr (by nlinarith)
  have hpos_sq : 0 ≤ Real.sqrt (θ_m * (θ_m - 4)) := Real.sqrt_nonneg _
  exact ⟨div_pos (by linarith) h2θ, div_le_div_of_nonneg_right (by linarith) h2θ.le,
    (div_lt_one h2θ).mpr (by linarith)⟩

private theorem uniformEquilibrium_of_quad {θ_m x : ℝ} (hθ : 0 < θ_m) (hx₀ : 0 < x)
    (hx₁ : x ≤ 1) (hquad : θ_m * x ^ 2 - θ_m * x + 1 = 0) :
    generosityEquilibrium (uniformTail θ_m) x := by
  have hle_θm : 1 / x ≤ θ_m := by
    rw [div_le_iff₀ hx₀]
    have hsq : 0 ≤ θ_m * x ^ 2 := mul_nonneg hθ.le (sq_nonneg x)
    linarith
  refine ⟨hx₀, hx₁, ?_⟩
  rw [uniformTail_of_pos_le (one_div_pos.mpr hx₀) hle_θm]
  field_simp [hx₀.ne', hθ.ne']
  linarith

/-- **Minimalist equilibrium characterization** (NRTV Claim 23.1): for a uniform generosity
distribution on `[0, θ_m]` (`θ_m > 0`), positive equilibrium contribution fractions exist iff
`θ_m ≥ 4`, and coincide with `{unifLowRoot θ_m, unifHighRoot θ_m}`. -/
theorem uniformEquilibrium_iff {θ_m x : ℝ} (hθ : 0 < θ_m) :
    generosityEquilibrium (uniformTail θ_m) x ↔
      4 ≤ θ_m ∧ (x = unifLowRoot θ_m ∨ x = unifHighRoot θ_m) := by
  have hdisc_eq : θ_m ^ 2 - 4 * θ_m * 1 = θ_m * (θ_m - 4) := by ring
  constructor
  · rintro ⟨hx0, _, hxeq⟩
    have hinv_pos : 0 < 1 / x := one_div_pos.mpr hx0
    have hle_θm : 1 / x ≤ θ_m := by
      by_contra hgt
      linarith [uniformTail_of_gt hinv_pos (lt_of_not_ge hgt)]
    rw [uniformTail_of_pos_le hinv_pos hle_θm] at hxeq
    have hquad : θ_m * x ^ 2 - θ_m * x + 1 = 0 := by
      field_simp [hx0.ne', hθ.ne'] at hxeq
      linarith
    have h4 : 4 ≤ θ_m := by nlinarith [mul_nonneg hθ.le (sq_nonneg (x - 1 / 2))]
    have hdisc : 0 ≤ θ_m ^ 2 - 4 * θ_m * 1 :=
      hdisc_eq ▸ mul_nonneg hθ.le (sub_nonneg.mpr h4)
    exact ⟨h4, by simpa only [unifLowRoot, unifHighRoot, hdisc_eq] using
      (quad_sol_iff hθ hdisc).mp hquad⟩
  · rintro ⟨hθ4, hroot⟩
    obtain ⟨hlow_pos, hlow_le, hhigh_lt⟩ := unifRoot_props hθ4
    have hdisc : 0 ≤ θ_m ^ 2 - 4 * θ_m * 1 :=
      hdisc_eq ▸ mul_nonneg hθ.le (sub_nonneg.mpr hθ4)
    obtain ⟨hx_pos, hx_le⟩ : 0 < x ∧ x ≤ 1 := by
      rcases hroot with rfl | rfl <;> constructor <;> linarith
    refine uniformEquilibrium_of_quad hθ hx_pos hx_le ((quad_sol_iff hθ hdisc).mpr ?_)
    exact hroot.imp (fun h => by rw [h, unifLowRoot, ← hdisc_eq])
      fun h => by rw [h, unifHighRoot, ← hdisc_eq]

/-- Critical point at `θ_m = 4`: the two equilibrium roots coalesce at `1 / 2`, and strictly below
`θ_m = 4` positive generosity collapses completely (NRTV Claim 23.1). -/
theorem uniform_at_four_and_collapse :
    (unifLowRoot 4 = 1 / 2 ∧ unifHighRoot 4 = 1 / 2) ∧
      ∀ {θ_m : ℝ}, 0 < θ_m → θ_m < 4 → ¬ ∃ x, generosityEquilibrium (uniformTail θ_m) x := by
  refine ⟨⟨by norm_num [unifLowRoot], ?_⟩, fun {θ_m} hθ hlt ⟨_, hx⟩ => ?_⟩
  · norm_num [unifHighRoot]
  · linarith [(uniformEquilibrium_iff hθ).mp hx]

/-- **Best-response stability of `unifHighRoot` vs instability of `unifLowRoot`** (NRTV Claim 23.1):
for `4 ≤ θ_m`, `uniformTail θ_m (1 / x) > x` strictly on `(unifLowRoot θ_m, unifHighRoot θ_m)`,
and `uniformTail θ_m (1 / x) < x` strictly on `(0, unifLowRoot θ_m)` and `(unifHighRoot θ_m, ∞)`. -/
theorem uniform_stability {θ_m : ℝ} (hθ4 : 4 ≤ θ_m) {x : ℝ} (hx₀ : 0 < x) :
    (unifLowRoot θ_m < x → x < unifHighRoot θ_m → x < uniformTail θ_m (1 / x)) ∧
      ((x < unifLowRoot θ_m ∨ unifHighRoot θ_m < x) → uniformTail θ_m (1 / x) < x) := by
  have hθ : 0 < θ_m := by linarith
  set d := Real.sqrt (θ_m * (θ_m - 4))
  have hd : d ^ 2 = θ_m * (θ_m - 4) := Real.sq_sqrt (mul_nonneg hθ.le (sub_nonneg.mpr hθ4))
  have hfac : θ_m * x ^ 2 - θ_m * x + 1 =
      θ_m * (x - unifLowRoot θ_m) * (x - unifHighRoot θ_m) := by
    dsimp [unifLowRoot, unifHighRoot]
    field_simp [hθ.ne']
    nlinarith [hd]
  have hinv_pos : 0 < 1 / x := one_div_pos.mpr hx₀
  constructor
  · intro hl hh
    have hquad_neg : θ_m * x ^ 2 - θ_m * x + 1 < 0 := by
      rw [hfac]
      exact mul_neg_of_pos_of_neg (mul_pos hθ (sub_pos.mpr hl)) (sub_neg.mpr hh)
    have hle_θm : 1 / x ≤ θ_m := by
      rw [div_le_iff₀ hx₀]
      have hsq_pos : 0 < θ_m * x ^ 2 := mul_pos hθ (sq_pos_of_pos hx₀)
      linarith
    rw [uniformTail_of_pos_le hinv_pos hle_θm, ← sub_pos]
    have hid : 1 - (1 / x) / θ_m - x = -(θ_m * x ^ 2 - θ_m * x + 1) / (θ_m * x) := by
      field_simp [hx₀.ne', hθ.ne']
      ring
    rw [hid]
    exact div_pos (by linarith) (mul_pos hθ hx₀)
  · intro hdisj
    have hquad_pos : 0 < θ_m * x ^ 2 - θ_m * x + 1 := by
      rw [hfac]
      obtain ⟨_, hle, _⟩ := unifRoot_props hθ4
      rcases hdisj with hl | hh
      · exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hθ (sub_neg.mpr hl))
          (sub_neg.mpr (hl.trans_le hle))
      · exact mul_pos (mul_pos hθ (sub_pos.mpr (hle.trans_lt hh))) (sub_pos.mpr hh)
    by_cases hle_θm : 1 / x ≤ θ_m
    · rw [uniformTail_of_pos_le hinv_pos hle_θm, ← sub_pos]
      have hid : x - (1 - (1 / x) / θ_m) = (θ_m * x ^ 2 - θ_m * x + 1) / (θ_m * x) := by
        field_simp [hx₀.ne', hθ.ne']
        ring
      rw [hid]
      exact div_pos hquad_pos (mul_pos hθ hx₀)
    · rw [uniformTail_of_gt hinv_pos (lt_of_not_ge hle_θm)]
      exact hx₀

private theorem unifHighRoot_eq_half_add {θ_m : ℝ} (hθ : 0 < θ_m) :
    unifHighRoot θ_m = 1 / 2 + Real.sqrt (1 / 4 - 1 / θ_m) := by
  have hid : (θ_m * (θ_m - 4)) / (2 * θ_m) ^ 2 = 1 / 4 - 1 / θ_m := by
    field_simp [hθ.ne']
    ring
  rw [unifHighRoot, add_div]
  have hdiv : Real.sqrt (θ_m * (θ_m - 4)) / (2 * θ_m) =
      Real.sqrt ((θ_m * (θ_m - 4)) / (2 * θ_m) ^ 2) := by
    rw [Real.sqrt_div', Real.sqrt_sq (by linarith)]
    · positivity
  have h1 : θ_m / (2 * θ_m) = 1 / 2 := by field_simp [hθ.ne']
  rw [h1, hdiv, hid]

/-- The stable equilibrium contribution fraction `unifHighRoot θ_m` is strictly increasing in
`θ_m` on `[4, ∞)` (NRTV Claim 23.1). -/
theorem unifHighRoot_strictMono {θ₁ θ₂ : ℝ} (hθ₁ : 4 ≤ θ₁) (hlt : θ₁ < θ₂) :
    unifHighRoot θ₁ < unifHighRoot θ₂ := by
  have h1 : 0 < θ₁ := by linarith
  have h2 : 0 < θ₂ := by linarith
  rw [unifHighRoot_eq_half_add h1, unifHighRoot_eq_half_add h2]
  have hsub : 1 / 4 - 1 / θ₁ < 1 / 4 - 1 / θ₂ := by
    linarith [div_lt_div_of_pos_left zero_lt_one h1 hlt]
  have hnn : 0 ≤ 1 / 4 - 1 / θ₁ := by
    linarith [div_le_div_of_nonneg_left zero_le_one (by norm_num : (0 : ℝ) < 4) hθ₁]
  linarith [Real.sqrt_lt_sqrt hnn hsub]

/-- As the generosity range `θ_m → ∞`, the stable equilibrium `unifHighRoot θ_m` approaches `1`
(NRTV Claim 23.1). -/
theorem unifHighRoot_tendsto_one :
    ∀ ε : ℝ, 0 < ε → ∃ Θ : ℝ, ∀ θ_m : ℝ, Θ ≤ θ_m →
      1 - ε < unifHighRoot θ_m ∧ unifHighRoot θ_m < 1 := by
  intro ε hε
  let δ := min ε (1 / 2)
  have hδ₀ : 0 < δ := lt_min hε (by norm_num)
  have hδ₁ : δ ≤ 1 / 2 := min_le_right ε (1 / 2)
  let c := 1 / 4 - (1 / 2 - δ) ^ 2
  have hc_pos : 0 < c := by
    dsimp [c]
    have hsq : (1 / 2 - δ) ^ 2 < (1 / 2 : ℝ) ^ 2 := by nlinarith
    linarith
  refine ⟨max 4 (1 / c + 1), fun θ_m hθ => ?_⟩
  have hθ4 : 4 ≤ θ_m := (le_max_left _ _).trans hθ
  have hθpos : 0 < θ_m := by linarith
  have hθbig : 1 / c < θ_m := lt_of_lt_of_le (by linarith [le_max_right 4 (1 / c + 1)]) hθ
  have hinv_lt : 1 / θ_m < c := (one_div_lt hθpos hc_pos).mpr hθbig
  have hlow_sq : (1 / 2 - δ) ^ 2 < 1 / 4 - 1 / θ_m := by dsimp [c] at hinv_lt; linarith
  have hsqrt_gt : 1 / 2 - δ < Real.sqrt (1 / 4 - 1 / θ_m) := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ 1 / 2 - δ)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hlow_sq
  refine ⟨?_, (unifRoot_props hθ4).2.2⟩
  rw [unifHighRoot_eq_half_add hθpos]
  linarith [min_le_left ε (1 / 2)]

/-! ### Mixture generosity distributions (NRTV Exercise 23.1) -/

/-- Mixture generosity survival function combining fraction `φ` of uniform `[0, θ_m]` peers,
`(1 - φ) / 2` completely selfish peers (`θ = 0`), and `(1 - φ) / 2` maximal-generosity peers
(`θ = θ_m`). -/
noncomputable def mixtureTail (θ_m φ t : ℝ) : ℝ :=
  φ * uniformTail θ_m t +
    ((1 - φ) / 2) * (if t ≤ 0 then 1 else 0) +
    ((1 - φ) / 2) * (if t ≤ θ_m then 1 else 0)

theorem mixtureTail_one (θ_m t : ℝ) : mixtureTail θ_m 1 t = uniformTail θ_m t := by
  simp [mixtureTail]

theorem mixtureTail_of_pos_le {θ_m φ t : ℝ} (ht₀ : 0 < t) (htθ : t ≤ θ_m) :
    mixtureTail θ_m φ t = (1 + φ) / 2 - φ * t / θ_m := by
  simp only [mixtureTail, uniformTail_of_pos_le ht₀ htθ, ht₀.not_ge, htθ, ↓reduceIte]
  ring

theorem mixtureTail_of_gt {θ_m φ t : ℝ} (hθ : 0 < θ_m) (ht : θ_m < t) :
    mixtureTail θ_m φ t = 0 := by
  have ht₀ : 0 < t := hθ.trans ht
  simp [mixtureTail, uniformTail_of_gt ht₀ ht, ht₀.not_ge, ht.not_ge]

/-- Lower root `(((1 + φ) / 2) θ_m - √((((1 + φ) / 2) θ_m)^2 - 4 θ_m φ)) / (2 θ_m)` of the
interior quadratic fixed-point equation for `mixtureTail θ_m φ` (NRTV Exercise 23.1). -/
noncomputable def mixLowRoot (θ_m φ : ℝ) : ℝ :=
  ((1 + φ) / 2 * θ_m - Real.sqrt (((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ)) / (2 * θ_m)

theorem mixLowRoot_eq (θ_m φ : ℝ) :
    mixLowRoot θ_m φ =
      ((1 + φ) / 2 * θ_m - Real.sqrt (((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ)) / (2 * θ_m) := by
  rfl

/-- Upper root `(((1 + φ) / 2) θ_m + √((((1 + φ) / 2) θ_m)^2 - 4 θ_m φ)) / (2 θ_m)` of the
interior quadratic fixed-point equation for `mixtureTail θ_m φ` (NRTV Exercise 23.1). -/
noncomputable def mixHighRoot (θ_m φ : ℝ) : ℝ :=
  ((1 + φ) / 2 * θ_m + Real.sqrt (((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ)) / (2 * θ_m)

theorem mixHighRoot_eq (θ_m φ : ℝ) :
    mixHighRoot θ_m φ =
      ((1 + φ) / 2 * θ_m + Real.sqrt (((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ)) / (2 * θ_m) := by
  rfl

/-- Positivity and ordering bounds for `mixLowRoot` and `mixHighRoot` when the interior quadratic
discriminant is nonnegative (`16 * φ / (1 + φ) ^ 2 ≤ θ_m`). -/
theorem mixRoot_props {θ_m φ : ℝ} (hθ : 0 < θ_m) (hφ₀ : 0 < φ) (hφ₁ : φ ≤ 1)
    (hthr : 16 * φ / (1 + φ) ^ 2 ≤ θ_m) :
    0 < mixLowRoot θ_m φ ∧ mixLowRoot θ_m φ ≤ mixHighRoot θ_m φ ∧
      mixHighRoot θ_m φ < (1 + φ) / 2 ∧ mixHighRoot θ_m φ < 1 := by
  have h1φ : 0 < 1 + φ := by linarith
  have hb_pos : 0 < (1 + φ) / 2 * θ_m := by positivity
  have hsq_lt :
      Real.sqrt (((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ) < (1 + φ) / 2 * θ_m := by
    rw [Real.sqrt_lt' hb_pos]
    have : 0 < 4 * θ_m * φ := by positivity
    linarith
  have hsq_nn : 0 ≤ Real.sqrt (((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ) := Real.sqrt_nonneg _
  have hlt_cap : mixHighRoot θ_m φ < (1 + φ) / 2 := by
    dsimp [mixHighRoot]
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have _ := hthr
  refine ⟨?_, ?_, hlt_cap, by linarith⟩
  · dsimp [mixLowRoot]
    exact div_pos (by linarith) (by linarith)
  · dsimp [mixLowRoot, mixHighRoot]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- Upper bound `x ≤ (1 + φ) / 2` for any positive equilibrium under `mixtureTail θ_m φ`
(`0 ≤ φ ≤ 1`, `θ_m > 0`), strictly capping equilibrium participation below `1` whenever `φ < 1`
(NRTV Exercise 23.1). -/
theorem mixture_upper_bound {θ_m φ x : ℝ} (hθ : 0 < θ_m) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ 1)
    (heq : generosityEquilibrium (mixtureTail θ_m φ) x) :
    x ≤ (1 + φ) / 2 := by
  rcases heq with ⟨hx₀, _, hxeq⟩
  have hm : (if 1 / x ≤ θ_m then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  rw [hxeq]
  simp only [mixtureTail, (one_div_pos.mpr hx₀).not_ge, ↓reduceIte]
  linarith [mul_le_mul_of_nonneg_left (uniformTail_le_one hθ (1 / x)) hφ₀,
    mul_le_mul_of_nonneg_left hm (show 0 ≤ (1 - φ) / 2 by linarith)]

private theorem mixture_disc_nonneg_iff {θ_m φ : ℝ} (hθ : 0 < θ_m) (hφ₀ : 0 < φ) :
    16 * φ / (1 + φ) ^ 2 ≤ θ_m ↔ 0 ≤ ((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ := by
  have h1φ_pos : 0 < 1 + φ := by linarith
  have hid : ((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ =
      (θ_m * (1 + φ) ^ 2 / 4) * (θ_m - 16 * φ / (1 + φ) ^ 2) := by
    field_simp [h1φ_pos.ne']
    ring
  have hcoeff : 0 < θ_m * (1 + φ) ^ 2 / 4 := by positivity
  rw [hid, mul_nonneg_iff_of_pos_left hcoeff, sub_nonneg]

/-- **Mixture equilibrium characterization** (NRTV Exercise 23.1): for `0 < θ_m` and
`0 < φ ≤ 1`, a fraction `x` is a positive generosity equilibrium under `mixtureTail θ_m φ` iff
`16 * φ / (1 + φ) ^ 2 ≤ θ_m`, the active cost `1 / x` lies in `[0, θ_m]` (`1 / x ≤ θ_m`), and `x`
is one of `{mixLowRoot θ_m φ, mixHighRoot θ_m φ}`. -/
theorem mixtureEquilibrium_iff {θ_m φ x : ℝ} (hθ : 0 < θ_m) (hφ₀ : 0 < φ) (hφ₁ : φ ≤ 1) :
    generosityEquilibrium (mixtureTail θ_m φ) x ↔
      16 * φ / (1 + φ) ^ 2 ≤ θ_m ∧ 1 / x ≤ θ_m ∧
        (x = mixLowRoot θ_m φ ∨ x = mixHighRoot θ_m φ) := by
  constructor
  · rintro ⟨hx₀, _, hxeq⟩
    have hinv_pos : 0 < 1 / x := one_div_pos.mpr hx₀
    have hle_θm : 1 / x ≤ θ_m := by
      by_contra hgt
      have h0 : mixtureTail θ_m φ (1 / x) = 0 := mixtureTail_of_gt hθ (lt_of_not_ge hgt)
      linarith
    rw [mixtureTail_of_pos_le hinv_pos hle_θm] at hxeq
    have hquad : θ_m * x ^ 2 - ((1 + φ) / 2 * θ_m) * x + φ = 0 := by
      field_simp [hx₀.ne', hθ.ne'] at hxeq
      linarith
    have hdisc : 0 ≤ ((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ := by
      linarith [sq_nonneg (2 * θ_m * x - (1 + φ) / 2 * θ_m), mul_eq_zero_of_right (4 * θ_m) hquad]
    exact ⟨(mixture_disc_nonneg_iff hθ hφ₀).mpr hdisc, hle_θm, (quad_sol_iff hθ hdisc).mp hquad⟩
  · rintro ⟨hthr, hle_θm, hroot⟩
    obtain ⟨hlow_pos, hlow_le, _, hhigh_lt⟩ := mixRoot_props hθ hφ₀ hφ₁ hthr
    obtain ⟨hx₀, hx₁⟩ : 0 < x ∧ x ≤ 1 := by
      rcases hroot with rfl | rfl <;> constructor <;> linarith
    have hdisc : 0 ≤ ((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ :=
      (mixture_disc_nonneg_iff hθ hφ₀).mp hthr
    have hquad : θ_m * x ^ 2 - ((1 + φ) / 2 * θ_m) * x + φ = 0 :=
      (quad_sol_iff hθ hdisc).mpr hroot
    refine ⟨hx₀, hx₁, ?_⟩
    rw [mixtureTail_of_pos_le (one_div_pos.mpr hx₀) hle_θm]
    have h1 : (x - ((1 + φ) / 2 - φ * (1 / x) / θ_m)) * (θ_m * x) = 0 := by
      field_simp [hx₀.ne', hθ.ne']
      linarith
    linarith [(mul_eq_zero.mp h1).resolve_right (mul_pos hθ hx₀).ne']

/-- **Two-regime positive-equilibrium threshold for mixture generosity** (NRTV Exercise 23.1):
for `0 < θ_m` and `0 < φ ≤ 1`, a positive generosity equilibrium exists under `mixtureTail θ_m φ`
iff either `1 / 3 ≤ φ` and `16 * φ / (1 + φ) ^ 2 ≤ θ_m`, or `φ < 1 / 3` and `2 / (1 - φ) ≤ θ_m`
(where `16 * φ / (1 + φ) ^ 2` alone does not suffice because both quadratic roots lie below
`1 / θ_m` whenever `θ_m < 2 / (1 - φ)`). -/
theorem exists_mixtureEquilibrium_iff {θ_m φ : ℝ} (hθ : 0 < θ_m) (hφ₀ : 0 < φ) (hφ₁ : φ ≤ 1) :
    (∃ x, generosityEquilibrium (mixtureTail θ_m φ) x) ↔
      (1 / 3 ≤ φ ∧ 16 * φ / (1 + φ) ^ 2 ≤ θ_m) ∨
        (φ < 1 / 3 ∧ 2 / (1 - φ) ≤ θ_m) := by
  constructor
  · rintro ⟨x, heq⟩
    obtain ⟨hthr, hle_θm, hroot⟩ := (mixtureEquilibrium_iff hθ hφ₀ hφ₁).mp heq
    by_cases hφ3 : 1 / 3 ≤ φ
    · exact Or.inl ⟨hφ3, hthr⟩
    · have hφ_lt : φ < 1 / 3 := lt_of_not_ge hφ3
      refine Or.inr ⟨hφ_lt, ?_⟩
      have h1φ_sub : 0 < 1 - φ := by linarith
      rw [div_le_iff₀ h1φ_sub]
      have hx₀ : 0 < x := heq.1
      have hy1 : 1 ≤ θ_m * x := by
        rwa [div_le_iff₀ hx₀] at hle_θm
      have hdisc : 0 ≤ ((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ :=
        (mixture_disc_nonneg_iff hθ hφ₀).mp hthr
      have hquad : θ_m * x ^ 2 - ((1 + φ) / 2 * θ_m) * x + φ = 0 :=
        (quad_sol_iff hθ hdisc).mpr hroot
      by_contra hlt
      have hlt2 : θ_m * (1 - φ) < 2 := lt_of_not_ge hlt
      have hsum_zero : (θ_m * x - 1) ^ 2 + (θ_m * x - 1) * (2 - (1 + φ) / 2 * θ_m) +
          (1 - θ_m * (1 - φ) / 2) = 0 := by linarith [mul_eq_zero_of_right θ_m hquad]
      have hcoef_pos : 0 < 2 - (1 + φ) / 2 * θ_m := by
        nlinarith [mul_lt_mul_of_pos_left (show 1 + φ < 2 * (1 - φ) by linarith) hθ]
      linarith [sq_nonneg (θ_m * x - 1), mul_nonneg (sub_nonneg.2 hy1) hcoef_pos.le]
  · rintro (⟨hφ3, hthr⟩ | ⟨hφ_lt, h2⟩)
    · refine ⟨mixHighRoot θ_m φ, (mixtureEquilibrium_iff hθ hφ₀ hφ₁).mpr ⟨hthr, ?_, Or.inr rfl⟩⟩
      obtain ⟨hlow_pos, hlow_le, _, _⟩ := mixRoot_props hθ hφ₀ hφ₁ hthr
      have hhigh_pos : 0 < mixHighRoot θ_m φ := lt_of_lt_of_le hlow_pos hlow_le
      rw [div_le_iff₀ hhigh_pos]
      have h1φ_pos : 0 < (1 + φ) ^ 2 := by positivity
      have hmul : 16 * φ ≤ θ_m * (1 + φ) ^ 2 := (div_le_iff₀ h1φ_pos).mp hthr
      have hb_ge : 2 ≤ (1 + φ) / 2 * θ_m := by nlinarith
      have hsq_nn : 0 ≤ Real.sqrt (((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ) := Real.sqrt_nonneg _
      have hid : θ_m * mixHighRoot θ_m φ =
          ((1 + φ) / 2 * θ_m + Real.sqrt (((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ)) / 2 := by
        dsimp [mixHighRoot]
        field_simp [hθ.ne']
      rw [hid]
      linarith
    · have h1φ_sub : 0 < 1 - φ := by linarith
      have h1φ_sq : 0 < (1 + φ) ^ 2 := by positivity
      have hthr : 16 * φ / (1 + φ) ^ 2 ≤ θ_m := by
        refine le_trans ?_ h2
        rw [div_le_div_iff₀ h1φ_sq h1φ_sub]
        have : 0 ≤ 2 * (3 * φ - 1) ^ 2 := by positivity
        nlinarith
      refine ⟨mixHighRoot θ_m φ, (mixtureEquilibrium_iff hθ hφ₀ hφ₁).mpr ⟨hthr, ?_, Or.inr rfl⟩⟩
      obtain ⟨hlow_pos, hlow_le, _, _⟩ := mixRoot_props hθ hφ₀ hφ₁ hthr
      have hhigh_pos : 0 < mixHighRoot θ_m φ := lt_of_lt_of_le hlow_pos hlow_le
      rw [div_le_iff₀ hhigh_pos]
      have h2mul : 2 ≤ θ_m * (1 - φ) := (div_le_iff₀ h1φ_sub).mp h2
      have hdisc : 0 ≤ ((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ :=
        (mixture_disc_nonneg_iff hθ hφ₀).mp hthr
      set b := (1 + φ) / 2 * θ_m
      set d := Real.sqrt (b ^ 2 - 4 * θ_m * φ)
      have hd_sq : d ^ 2 = b ^ 2 - 4 * θ_m * φ := Real.sq_sqrt hdisc
      have hsq_le : (2 - b) ^ 2 ≤ d ^ 2 := by
        have hid : d ^ 2 - (2 - b) ^ 2 = 2 * (θ_m * (1 - φ) - 2) := by
          rw [hd_sq]
          dsimp [b]
          ring
        linarith
      have hbd : 2 ≤ b + d := by
        have hle_d : 2 - b ≤ d := Real.le_sqrt_of_sq_le (hd_sq ▸ hsq_le)
        linarith
      have hid : θ_m * mixHighRoot θ_m φ = (b + d) / 2 := by
        dsimp [mixHighRoot, b, d]
        field_simp [hθ.ne']
      rw [hid]
      linarith

theorem mixture_threshold_le_four {φ : ℝ} (hφ₀ : 0 ≤ φ) :
    16 * φ / (1 + φ) ^ 2 ≤ 4 := by
  have hpos : 0 < (1 + φ) ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  have hsq : 0 ≤ 4 * (1 - φ) ^ 2 := by positivity
  linarith

/-! ### Service differentiation and exclusion (NRTV §23.3.2, Claim 23.2, Exercise 23.2) -/

/-- Aggregate request load per peer when contributors share `x` and free-rider requests suffer
dropping probability `p`: `R(x, p) = 1 - (1 - x) * p`. -/
def requestLoad (x p : ℝ) : ℝ :=
  1 - (1 - x) * p

theorem requestLoad_eq (x p : ℝ) : requestLoad x p = 1 - (1 - x) * p := by
  rfl

/-- Effective per-peer service rate `x * R(x, p)` when contributors serve at rate `x` on admitted
load `R(x, p)`. -/
def serviceRate (x p : ℝ) : ℝ :=
  x * requestLoad x p

theorem serviceRate_eq (x p : ℝ) : serviceRate x p = x * requestLoad x p := by
  rfl

/-- Net cost threshold `T(α, x, p) = R(x, p) / x - α * p * x` separating contributors from free
riders under penalty `p ∈ [0, 1]` and sharing benefit `α` (NRTV §23.3.2). -/
noncomputable def penaltyThreshold (α x p : ℝ) : ℝ :=
  requestLoad x p / x - α * p * x

theorem penaltyThreshold_eq (α x p : ℝ) :
    penaltyThreshold α x p = requestLoad x p / x - α * p * x := by
  rfl

/-- Equilibrium condition under service differentiation penalty `p`: `x ∈ (0, 1]` and
`x = tail (penaltyThreshold α x p)`. -/
@[expose] def penaltyEquilibrium (tail : ℝ → ℝ) (α p x : ℝ) : Prop :=
  0 < x ∧ x ≤ 1 ∧ x = tail (penaltyThreshold α x p)

/-- Per-capita utilitarian social welfare `α * serviceRate x p - requestLoad x p` under penalty
`p`, reducing to `minimalistWelfare α x` at `p = 0`. -/
def penaltyWelfare (α x p : ℝ) : ℝ :=
  α * serviceRate x p - requestLoad x p

theorem penaltyWelfare_eq (α x p : ℝ) :
    penaltyWelfare α x p = α * serviceRate x p - requestLoad x p := by
  rfl

@[simp]
theorem penaltyThreshold_zero (α x : ℝ) : penaltyThreshold α x 0 = 1 / x := by
  simp [penaltyThreshold, requestLoad]

theorem penaltyEquilibrium_zero (tail : ℝ → ℝ) (α x : ℝ) :
    penaltyEquilibrium tail α 0 x ↔ generosityEquilibrium tail x := by
  simp [penaltyEquilibrium, generosityEquilibrium]

theorem penaltyWelfare_zero (α x : ℝ) : penaltyWelfare α x 0 = minimalistWelfare α x := by
  simp [penaltyWelfare, serviceRate, requestLoad, minimalistWelfare]

/-- **Full cooperation under penalties** (NRTV Claim 23.2): for ANY generosity distribution with
nonnegative support (`∀ t ≤ 0, tail t = 1`), any benefit `α > 0`, and any penalty `p` with
`1 / α ≤ p`, `x = 1` (100% contribution) is an equilibrium. -/
theorem fullCooperation_penalty_threshold {tail : ℝ → ℝ} (htail : ∀ t ≤ 0, tail t = 1)
    {α p : ℝ} (hα : 0 < α) (hp : 1 / α ≤ p) :
    penaltyThreshold α 1 p ≤ 0 ∧ penaltyEquilibrium tail α p 1 := by
  have h1α : 1 ≤ α * p := by rwa [div_le_iff₀ hα, mul_comm] at hp
  have hthr : penaltyThreshold α 1 p ≤ 0 := by
    simp only [penaltyThreshold, requestLoad, sub_self, zero_mul, sub_zero, div_one, mul_one]
    linarith
  exact ⟨hthr, zero_lt_one, le_rfl, (htail _ hthr).symm⟩

/-- **Minimalist equilibrium with uniform exclusion** (NRTV Exercise 23.2): excluding fraction
`z ∈ [0, 1)` of incoming demand lowers per-contributor cost to `(1 - z) / x`, yielding fixed-point
equation `x = tail ((1 - z) / x)` and active-population welfare `(1 - z) * (α * x - 1)`. -/
@[expose] def exclEquilibrium (tail : ℝ → ℝ) (z x : ℝ) : Prop :=
  0 < x ∧ x ≤ 1 ∧ x = tail ((1 - z) / x)

/-- Upper positive equilibrium root under uniform exclusion fraction `z`:
`(θ_m + √(θ_m (θ_m - 4 (1 - z)))) / (2 θ_m)`. -/
noncomputable def exclHighRoot (θ_m z : ℝ) : ℝ :=
  (θ_m + Real.sqrt (θ_m * (θ_m - 4 * (1 - z)))) / (2 * θ_m)

theorem exclHighRoot_eq (θ_m z : ℝ) :
    exclHighRoot θ_m z = (θ_m + Real.sqrt (θ_m * (θ_m - 4 * (1 - z)))) / (2 * θ_m) := by
  rfl

/-- Total social welfare under uniform exclusion fraction `z`: `(1 - z) * (α * x - 1)`. -/
def exclWelfare (α x z : ℝ) : ℝ :=
  (1 - z) * (α * x - 1)

theorem exclWelfare_eq (α x z : ℝ) : exclWelfare α x z = (1 - z) * (α * x - 1) := by
  rfl

theorem exclHighRoot_zero (θ_m : ℝ) : exclHighRoot θ_m 0 = unifHighRoot θ_m := by
  simp [exclHighRoot, unifHighRoot]

/-- Under uniform exclusion `z < 1`, the critical generosity threshold drops from `4` to
`4 * (1 - z)`, and `exclHighRoot θ_m z` is an equilibrium whenever `4 * (1 - z) ≤ θ_m`
(NRTV Exercise 23.2). -/
theorem exclHighRoot_equilibrium {θ_m z : ℝ} (hθ_pos : 0 < θ_m) (hz₁ : z < 1)
    (hthr : 4 * (1 - z) ≤ θ_m) :
    exclEquilibrium (uniformTail θ_m) z (exclHighRoot θ_m z) ∧
      exclHighRoot θ_m z < 1 := by
  have h1z : 0 < 1 - z := sub_pos.mpr hz₁
  have hrad : 0 ≤ θ_m * (θ_m - 4 * (1 - z)) := mul_nonneg hθ_pos.le (sub_nonneg.mpr hthr)
  have hsq_lt : Real.sqrt (θ_m * (θ_m - 4 * (1 - z))) < θ_m := by
    rw [Real.sqrt_lt' hθ_pos]
    nlinarith
  have hpos : 0 < exclHighRoot θ_m z := by
    dsimp [exclHighRoot]
    have hnn := Real.sqrt_nonneg (θ_m * (θ_m - 4 * (1 - z)))
    positivity
  have hlt1 : exclHighRoot θ_m z < 1 := by
    dsimp [exclHighRoot]
    rw [div_lt_one (by linarith)]
    linarith
  have hdisc_eq : θ_m ^ 2 - 4 * θ_m * (1 - z) = θ_m * (θ_m - 4 * (1 - z)) := by ring
  have hdisc : 0 ≤ θ_m ^ 2 - 4 * θ_m * (1 - z) := by rw [hdisc_eq]; exact hrad
  have hquad : θ_m * (exclHighRoot θ_m z) ^ 2 - θ_m * exclHighRoot θ_m z + (1 - z) = 0 :=
    (quad_sol_iff hθ_pos hdisc).mpr (Or.inr (by unfold exclHighRoot; rw [← hdisc_eq]))
  have hle_θm : (1 - z) / exclHighRoot θ_m z ≤ θ_m := by
    rw [div_le_iff₀ hpos]
    have hlt_prod : exclHighRoot θ_m z ^ 2 < exclHighRoot θ_m z := by nlinarith
    nlinarith
  have hinv_pos : 0 < (1 - z) / exclHighRoot θ_m z := div_pos h1z hpos
  refine ⟨⟨hpos, hlt1.le, ?_⟩, hlt1⟩
  rw [uniformTail_of_pos_le hinv_pos hle_θm]
  field_simp [hpos.ne', hθ_pos.ne']
  linarith

/-- **Exclusion rescues subcritical sharing** (NRTV Exercise 23.2): at `θ_m = 3 < 4` and `α = 3`,
no positive equilibrium exists without exclusion (`z = 0`), whereas `z = 1 / 2` sustains a
positive equilibrium with strictly positive social welfare. -/
theorem excl_rescues_low_generosity :
    (¬ ∃ x, generosityEquilibrium (uniformTail 3) x) ∧
      exclEquilibrium (uniformTail 3) (1 / 2) (exclHighRoot 3 (1 / 2)) ∧
      0 < exclWelfare 3 (exclHighRoot 3 (1 / 2)) (1 / 2) := by
  refine ⟨uniform_at_four_and_collapse.2 (by norm_num) (by norm_num),
    (exclHighRoot_equilibrium (by norm_num) (by norm_num) (by norm_num)).1, ?_⟩
  have hroot : (1 / 2 : ℝ) < exclHighRoot 3 (1 / 2) := by
    dsimp [exclHighRoot]
    have hsqrt : 0 < Real.sqrt (3 * (3 - 4 * (1 - 1 / 2))) := Real.sqrt_pos.mpr (by norm_num)
    linarith
  dsimp [exclWelfare]
  linarith

/-- **Exclusion can reduce social welfare** (NRTV Exercise 23.2): at `θ_m = 5` and `α = 2`, the
system already sustains high cooperation at `z = 0`, and imposing exclusion `z = 1 / 2` strictly
lowers welfare: `exclWelfare 2 (exclHighRoot 5 (1 / 2)) (1 / 2) <
minimalistWelfare 2 (unifHighRoot 5)`. -/
theorem excl_can_reduce_welfare :
    exclWelfare 2 (exclHighRoot 5 (1 / 2)) (1 / 2) < minimalistWelfare 2 (unifHighRoot 5) := by
  have h1 : minimalistWelfare 2 (unifHighRoot 5) = Real.sqrt 5 / 5 := by
    simp only [minimalistWelfare, unifHighRoot]
    rw [show (5 : ℝ) * (5 - 4) = 5 by ring]
    ring
  have h2 : exclWelfare 2 (exclHighRoot 5 (1 / 2)) (1 / 2) = Real.sqrt 15 / 10 := by
    simp only [exclWelfare, exclHighRoot]
    rw [show (5 : ℝ) * (5 - 4 * (1 - 1 / 2)) = 15 by ring]
    ring
  rw [h1, h2]
  have hlt : Real.sqrt 15 < 2 * Real.sqrt 5 := by
    rw [Real.sqrt_lt' (by positivity), mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  linarith

end Cslib.GameTheory.P2P
