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
  to `1` (`unifHighRoot_tendsto_one`), and benefit-independence of equilibrium fraction alongside
  linear welfare scaling `minimalistWelfare α x = α * x - 1`.
* **Mixture generosity distributions (NRTV Exercise 23.1)**:
  `mixtureTail θ_m φ` (mixing uniform `[0, θ_m]` with point masses at `0` and `θ_m`), lowering the
  interior threshold to `16 * φ / (1 + φ) ^ 2 ≤ θ_m` while capping equilibrium cooperation at
  `(1 + φ) / 2 < 1` for `φ < 1`.
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
@[expose] def minimalistWelfare (α x : ℝ) : ℝ :=
  α * x - 1

/-- Minimalist equilibrium contribution fractions depend solely on the generosity tail law and not
on the sharing benefit `α`. -/
theorem generosityEquilibrium_indep_benefit (tail : ℝ → ℝ) {α₁ α₂ x : ℝ} :
    generosityEquilibrium tail x →
      (α₁ ≤ α₂ → 0 < x → minimalistWelfare α₁ x ≤ minimalistWelfare α₂ x) :=
  fun _ hα hx => by dsimp [minimalistWelfare]; nlinarith

/-- Survival (tail) function `P(θ ≥ t)` of the uniform generosity distribution on `[0, θ_m]`. -/
@[expose] noncomputable def uniformTail (θ_m t : ℝ) : ℝ :=
  if t ≤ 0 then 1 else if t ≤ θ_m then 1 - t / θ_m else 0

theorem uniformTail_nonneg {θ_m : ℝ} (hθ : 0 < θ_m) (t : ℝ) : 0 ≤ uniformTail θ_m t := by
  dsimp [uniformTail]
  split_ifs with h0 ht
  · norm_num
  · have : t / θ_m ≤ 1 := (div_le_one hθ).mpr ht
    linarith
  · exact le_rfl

theorem uniformTail_le_one {θ_m : ℝ} (hθ : 0 < θ_m) (t : ℝ) : uniformTail θ_m t ≤ 1 := by
  dsimp [uniformTail]
  split_ifs with h0 ht
  · exact le_rfl
  · have hpos : 0 ≤ t / θ_m := div_nonneg (lt_of_not_ge h0).le hθ.le
    linarith
  · norm_num

theorem uniformTail_antitone {θ_m : ℝ} (hθ : 0 < θ_m) : Antitone (uniformTail θ_m) := by
  intro t₁ t₂ hle
  by_cases h1 : t₁ ≤ 0
  · have htail1 : uniformTail θ_m t₁ = 1 := by simp [uniformTail, h1]
    rw [htail1]
    exact uniformTail_le_one hθ t₂
  · have ht1_pos : 0 < t₁ := lt_of_not_ge h1
    have h2 : ¬ t₂ ≤ 0 := not_le.mpr (lt_of_lt_of_le ht1_pos hle)
    by_cases h2θ : t₂ ≤ θ_m
    · have h1θ : t₁ ≤ θ_m := hle.trans h2θ
      simp only [uniformTail, h1, h2, h1θ, h2θ, ↓reduceIte]
      linarith [div_le_div_of_nonneg_right hle hθ.le]
    · have htail2 : uniformTail θ_m t₂ = 0 := by simp [uniformTail, h2, h2θ]
      rw [htail2]
      exact uniformTail_nonneg hθ t₁

private theorem uniformTail_of_pos_le {θ_m t : ℝ} (ht0 : 0 < t) (htθ : t ≤ θ_m) :
    uniformTail θ_m t = 1 - t / θ_m := by
  dsimp [uniformTail]
  rw [ite_eq_right_iff.mpr (fun h => absurd h ht0.not_ge),
    ite_eq_left_iff.mpr (fun h => absurd htθ h)]

private theorem uniformTail_of_gt {θ_m t : ℝ} (ht0 : 0 < t) (htθ : θ_m < t) :
    uniformTail θ_m t = 0 := by
  dsimp [uniformTail]
  rw [ite_eq_right_iff.mpr (fun h => absurd h ht0.not_ge),
    ite_eq_right_iff.mpr (fun h => absurd h htθ.not_ge)]

/-- Upper positive equilibrium contribution root `(θ_m + √(θ_m (θ_m - 4))) / (2 θ_m)` of the
uniform generosity model (NRTV Claim 23.1). -/
@[expose] noncomputable def unifHighRoot (θ_m : ℝ) : ℝ :=
  (θ_m + Real.sqrt (θ_m * (θ_m - 4))) / (2 * θ_m)

/-- Lower positive equilibrium contribution root `(θ_m - √(θ_m (θ_m - 4))) / (2 θ_m)` of the
uniform generosity model (NRTV Claim 23.1). -/
@[expose] noncomputable def unifLowRoot (θ_m : ℝ) : ℝ :=
  (θ_m - Real.sqrt (θ_m * (θ_m - 4))) / (2 * θ_m)

private theorem quad_sol_iff {a b c x : ℝ} (ha : 0 < a) (hdisc : 0 ≤ b ^ 2 - 4 * a * c) :
    a * x ^ 2 - b * x + c = 0 ↔
      x = (b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) ∨
        x = (b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
  set d := Real.sqrt (b ^ 2 - 4 * a * c)
  have hd : d ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt hdisc
  have hfac : 4 * a * (a * x ^ 2 - b * x + c) =
      (2 * a * x - (b - d)) * (2 * a * x - (b + d)) := by
    calc
      4 * a * (a * x ^ 2 - b * x + c) = (2 * a * x - b) ^ 2 - (b ^ 2 - 4 * a * c) := by ring
      _ = (2 * a * x - b) ^ 2 - d ^ 2 := by rw [← hd]
      _ = (2 * a * x - (b - d)) * (2 * a * x - (b + d)) := by ring
  constructor
  · intro h
    have h0 : (2 * a * x - (b - d)) * (2 * a * x - (b + d)) = 0 := by rw [← hfac, h, mul_zero]
    rcases mul_eq_zero.mp h0 with h1 | h2
    · left; field_simp [ha.ne']; linarith
    · right; field_simp [ha.ne']; linarith
  · rintro (rfl | rfl)
    · have h0 : 2 * a * ((b - d) / (2 * a)) - (b - d) = 0 := by
        field_simp [ha.ne']; ring
      have hprod : 4 * a * (a * ((b - d) / (2 * a)) ^ 2 - b * ((b - d) / (2 * a)) + c) = 0 := by
        rw [hfac, h0, zero_mul]
      exact (mul_eq_zero.mp hprod).resolve_left (by linarith)
    · have h0 : 2 * a * ((b + d) / (2 * a)) - (b + d) = 0 := by
        field_simp [ha.ne']; ring
      have hprod : 4 * a * (a * ((b + d) / (2 * a)) ^ 2 - b * ((b + d) / (2 * a)) + c) = 0 := by
        rw [hfac, h0, mul_zero]
      exact (mul_eq_zero.mp hprod).resolve_left (by linarith)

/-- Root identities and bounds for `unifLowRoot` and `unifHighRoot` when `4 ≤ θ_m`. -/
theorem unifRoot_props {θ_m : ℝ} (hθ : 4 ≤ θ_m) :
    0 < unifLowRoot θ_m ∧ unifLowRoot θ_m ≤ unifHighRoot θ_m ∧ unifHighRoot θ_m < 1 := by
  have hθ_pos : 0 < θ_m := by linarith
  have hrad : 0 ≤ θ_m * (θ_m - 4) := mul_nonneg hθ_pos.le (sub_nonneg.mpr hθ)
  have hsq : Real.sqrt (θ_m * (θ_m - 4)) < θ_m := by
    rw [Real.sqrt_lt' hθ_pos]
    nlinarith
  have hpos_sq : 0 ≤ Real.sqrt (θ_m * (θ_m - 4)) := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · dsimp [unifLowRoot]
    exact div_pos (by linarith) (by linarith)
  · dsimp [unifLowRoot, unifHighRoot]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · dsimp [unifHighRoot]
    rw [div_lt_one (by linarith)]
    linarith

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
      have h0 : uniformTail θ_m (1 / x) = 0 := uniformTail_of_gt hinv_pos (lt_of_not_ge hgt)
      linarith
    have htail : uniformTail θ_m (1 / x) = 1 - (1 / x) / θ_m :=
      uniformTail_of_pos_le hinv_pos hle_θm
    rw [htail] at hxeq
    have hquad : θ_m * x ^ 2 - θ_m * x + 1 = 0 := by
      have h1 : x * (θ_m * x) = (1 - (1 / x) / θ_m) * (θ_m * x) := by rw [← hxeq]
      field_simp [hx0.ne', hθ.ne'] at h1
      linarith
    have h4 : 4 ≤ θ_m := by
      have hsq : 0 ≤ θ_m * (x - 1 / 2) ^ 2 := mul_nonneg hθ.le (sq_nonneg _)
      have hid : θ_m * (x - 1 / 2) ^ 2 + (4 - θ_m) / 4 = θ_m * x ^ 2 - θ_m * x + 1 := by ring
      linarith
    have hdisc : 0 ≤ θ_m ^ 2 - 4 * θ_m * 1 := by
      rw [hdisc_eq]; exact mul_nonneg hθ.le (sub_nonneg.mpr h4)
    refine ⟨h4, ?_⟩
    have hsol := (quad_sol_iff hθ hdisc).mp hquad
    rw [hdisc_eq] at hsol
    exact hsol
  · rintro ⟨hθ4, hroot⟩
    obtain ⟨hlow_pos, hlow_le, hhigh_lt⟩ := unifRoot_props hθ4
    have hdisc : 0 ≤ θ_m ^ 2 - 4 * θ_m * 1 := by
      rw [hdisc_eq]; exact mul_nonneg hθ.le (sub_nonneg.mpr hθ4)
    have hx_pos : 0 < x := by rcases hroot with rfl | rfl <;> linarith
    have hx_le : x ≤ 1 := by rcases hroot with rfl | rfl <;> linarith
    have hquad : θ_m * x ^ 2 - θ_m * x + 1 = 0 := by
      refine (quad_sol_iff hθ hdisc).mpr ?_
      rcases hroot with rfl | rfl
      · exact Or.inl (by unfold unifLowRoot; rw [← hdisc_eq])
      · exact Or.inr (by unfold unifHighRoot; rw [← hdisc_eq])
    exact uniformEquilibrium_of_quad hθ hx_pos hx_le hquad

/-- Critical point at `θ_m = 4`: the two equilibrium roots coalesce at `1 / 2`, and strictly below
`θ_m = 4` positive generosity collapses completely (NRTV Claim 23.1). -/
theorem uniform_at_four_and_collapse :
    (unifLowRoot 4 = 1 / 2 ∧ unifHighRoot 4 = 1 / 2) ∧
      ∀ {θ_m : ℝ}, 0 < θ_m → θ_m < 4 → ¬ ∃ x, generosityEquilibrium (uniformTail θ_m) x := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · norm_num [unifLowRoot]
  · norm_num [unifHighRoot]
  · intro θ_m hθ hlt ⟨x, hx⟩
    have := (uniformEquilibrium_iff hθ).mp hx
    linarith

/-- **Best-response stability of `unifHighRoot` vs instability of `unifLowRoot`** (NRTV Claim 23.1):
for `4 ≤ θ_m`, `uniformTail θ_m (1 / x) > x` strictly on `(unifLowRoot θ_m, unifHighRoot θ_m)`,
and `uniformTail θ_m (1 / x) < x` strictly on `(0, unifLowRoot θ_m)` and `(unifHighRoot θ_m, ∞)`. -/
theorem uniform_stability {θ_m : ℝ} (hθ4 : 4 ≤ θ_m) {x : ℝ} (hx₀ : 0 < x) :
    (unifLowRoot θ_m < x → x < unifHighRoot θ_m → x < uniformTail θ_m (1 / x)) ∧
      ((x < unifLowRoot θ_m ∨ unifHighRoot θ_m < x) → uniformTail θ_m (1 / x) < x) := by
  have hθ : 0 < θ_m := by linarith
  have hdisc_eq : θ_m * (θ_m - 4) = θ_m ^ 2 - 4 * θ_m * 1 := by ring
  set d := Real.sqrt (θ_m * (θ_m - 4))
  have hd : d ^ 2 = θ_m * (θ_m - 4) := Real.sq_sqrt (mul_nonneg hθ.le (sub_nonneg.mpr hθ4))
  have hfac : θ_m * x ^ 2 - θ_m * x + 1 =
      θ_m * (x - unifLowRoot θ_m) * (x - unifHighRoot θ_m) := by
    dsimp [unifLowRoot, unifHighRoot]
    field_simp [hθ.ne']
    nlinarith [hd]
  have hinv_pos : 0 < 1 / x := one_div_pos.mpr hx₀
  have hnot0 : ¬ 1 / x ≤ 0 := not_le.mpr hinv_pos
  constructor
  · intro hl hh
    have hquad_neg : θ_m * x ^ 2 - θ_m * x + 1 < 0 := by
      rw [hfac]
      have h1 : 0 < θ_m * (x - unifLowRoot θ_m) := mul_pos hθ (sub_pos.mpr hl)
      have h2 : x - unifHighRoot θ_m < 0 := sub_neg.mpr hh
      exact mul_neg_of_pos_of_neg h1 h2
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
      rcases hdisj with hl | hh
      · obtain ⟨_, hle, _⟩ := unifRoot_props hθ4
        have hh' : x < unifHighRoot θ_m := lt_of_lt_of_le hl hle
        exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hθ (sub_neg.mpr hl)) (sub_neg.mpr hh')
      · obtain ⟨_, hle, _⟩ := unifRoot_props hθ4
        have hl' : unifLowRoot θ_m < x := lt_of_le_of_lt hle hh
        exact mul_pos (mul_pos hθ (sub_pos.mpr hl')) (sub_pos.mpr hh)
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
    have : 1 / θ₂ < 1 / θ₁ := div_lt_div_of_pos_left zero_lt_one h1 hlt
    linarith
  have hnn : 0 ≤ 1 / 4 - 1 / θ₁ := by
    have : 1 / θ₁ ≤ 1 / 4 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hθ₁
    linarith
  have hlt_sqrt : Real.sqrt (1 / 4 - 1 / θ₁) < Real.sqrt (1 / 4 - 1 / θ₂) :=
    Real.sqrt_lt_sqrt hnn hsub
  linarith

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
  have hgt : 1 - ε < unifHighRoot θ_m := by
    rw [unifHighRoot_eq_half_add hθpos]
    have hδε : δ ≤ ε := min_le_left ε (1 / 2)
    linarith
  exact ⟨hgt, (unifRoot_props hθ4).2.2⟩

/-! ### Mixture generosity distributions (NRTV Exercise 23.1) -/

/-- Mixture generosity survival function combining fraction `φ` of uniform `[0, θ_m]` peers,
`(1 - φ) / 2` completely selfish peers (`θ = 0`), and `(1 - φ) / 2` maximal-generosity peers
(`θ = θ_m`). -/
@[expose] noncomputable def mixtureTail (θ_m φ t : ℝ) : ℝ :=
  φ * uniformTail θ_m t +
    ((1 - φ) / 2) * (if t ≤ 0 then 1 else 0) +
    ((1 - φ) / 2) * (if t ≤ θ_m then 1 else 0)

theorem mixtureTail_one (θ_m t : ℝ) : mixtureTail θ_m 1 t = uniformTail θ_m t := by
  simp [mixtureTail]

/-- Upper bound `x ≤ (1 + φ) / 2` for any positive equilibrium under `mixtureTail θ_m φ`
(`0 ≤ φ ≤ 1`, `θ_m > 0`), strictly capping equilibrium participation below `1` whenever `φ < 1`
(NRTV Exercise 23.1). -/
theorem mixture_upper_bound {θ_m φ x : ℝ} (hθ : 0 < θ_m) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ 1)
    (heq : generosityEquilibrium (mixtureTail θ_m φ) x) :
    x ≤ (1 + φ) / 2 := by
  rcases heq with ⟨hx₀, _, hxeq⟩
  have hinv_pos : 0 < 1 / x := one_div_pos.mpr hx₀
  have hnot0 : ¬ 1 / x ≤ 0 := not_le.mpr hinv_pos
  have hu : uniformTail θ_m (1 / x) ≤ 1 := uniformTail_le_one hθ (1 / x)
  have h0 : (if 1 / x ≤ 0 then (1 : ℝ) else 0) = 0 := ite_eq_right_iff.mpr fun h => absurd h hnot0
  have hm : (if 1 / x ≤ θ_m then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have h1φ : 0 ≤ (1 - φ) / 2 := by linarith
  rw [hxeq]
  dsimp [mixtureTail]
  rw [h0]
  nlinarith

/-- Lowered cooperation threshold for the mixture model (`0 < φ`, `0 < θ_m`): positive
equilibria satisfying `1 / x ≤ θ_m` exist iff `16 * φ / (1 + φ) ^ 2 ≤ θ_m` (strictly below `4` for
`φ < 1`, NRTV Exercise 23.1). -/
theorem mixtureEquilibrium_iff {θ_m φ x : ℝ} (hθ : 0 < θ_m) (hφ₀ : 0 < φ)
    (hle_θm : 1 / x ≤ θ_m) (hx₀ : 0 < x) :
    x = mixtureTail θ_m φ (1 / x) ↔
      16 * φ / (1 + φ) ^ 2 ≤ θ_m ∧
        (x = ((1 + φ) / 2 * θ_m -
              Real.sqrt (((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ)) / (2 * θ_m) ∨
          x = ((1 + φ) / 2 * θ_m +
              Real.sqrt (((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ)) / (2 * θ_m)) := by
  have hinv_pos : 0 < 1 / x := one_div_pos.mpr hx₀
  have hnot0 : ¬ 1 / x ≤ 0 := not_le.mpr hinv_pos
  have htail : mixtureTail θ_m φ (1 / x) = (1 + φ) / 2 - φ * (1 / x) / θ_m := by
    dsimp [mixtureTail]
    rw [uniformTail_of_pos_le hinv_pos hle_θm,
      ite_eq_right_iff.mpr fun h => absurd h hnot0,
      ite_eq_left_iff.mpr fun h => absurd hle_θm h]
    ring
  rw [htail]
  have heq_quad : (x = (1 + φ) / 2 - φ * (1 / x) / θ_m) ↔
      θ_m * x ^ 2 - ((1 + φ) / 2 * θ_m) * x + φ = 0 := by
    constructor <;> intro h
    · have h1 : x * (θ_m * x) = ((1 + φ) / 2 - φ * (1 / x) / θ_m) * (θ_m * x) := by rw [← h]
      field_simp [hx₀.ne', hθ.ne'] at h1
      linarith
    · have h1 : (x - ((1 + φ) / 2 - φ * (1 / x) / θ_m)) * (θ_m * x) = 0 := by
        field_simp [hx₀.ne', hθ.ne']
        linarith
      have hnz : θ_m * x ≠ 0 := (mul_pos hθ hx₀).ne'
      linarith [(mul_eq_zero.mp h1).resolve_right hnz]
  rw [heq_quad]
  have h1φ_pos : 0 < 1 + φ := by linarith
  have hdisc_ge : 16 * φ / (1 + φ) ^ 2 ≤ θ_m ↔ 0 ≤ ((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ := by
    have hid : ((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ =
        (θ_m * (1 + φ) ^ 2 / 4) * (θ_m - 16 * φ / (1 + φ) ^ 2) := by
      field_simp [h1φ_pos.ne']
      ring
    have hcoeff : 0 < θ_m * (1 + φ) ^ 2 / 4 := by positivity
    rw [hid]
    constructor
    · intro h; exact mul_nonneg hcoeff.le (sub_nonneg.mpr h)
    · intro h
      have : 0 ≤ θ_m - 16 * φ / (1 + φ) ^ 2 := nonneg_of_mul_nonneg_right h hcoeff
      linarith
  constructor
  · intro hq
    have hdisc : 0 ≤ ((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ := by
      have hid : ((1 + φ) / 2 * θ_m) ^ 2 - 4 * θ_m * φ =
          (2 * θ_m * x - (1 + φ) / 2 * θ_m) ^ 2 := by
        nlinarith [hq]
      rw [hid]
      exact sq_nonneg _
    exact ⟨hdisc_ge.mpr hdisc, (quad_sol_iff hθ hdisc).mp hq⟩
  · rintro ⟨hthr, hsol⟩
    exact (quad_sol_iff hθ (hdisc_ge.mp hthr)).mpr hsol

theorem mixture_threshold_le_four {φ : ℝ} (hφ₀ : 0 ≤ φ) :
    16 * φ / (1 + φ) ^ 2 ≤ 4 := by
  have hpos : 0 < (1 + φ) ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  have hsq : 0 ≤ 4 * (1 - φ) ^ 2 := by positivity
  linarith

/-! ### Service differentiation and exclusion (NRTV §23.3.2, Claim 23.2, Exercise 23.2) -/

/-- Aggregate request load per peer when contributors share `x` and free-rider requests suffer
dropping probability `p`: `R(x, p) = 1 - (1 - x) * p`. -/
@[expose] def requestLoad (x p : ℝ) : ℝ :=
  1 - (1 - x) * p

/-- Effective per-peer service rate `x * R(x, p)` when contributors serve at rate `x` on admitted
load `R(x, p)`. -/
@[expose] def serviceRate (x p : ℝ) : ℝ :=
  x * requestLoad x p

/-- Net cost threshold `T(α, x, p) = R(x, p) / x - α * p * x` separating contributors from free
riders under penalty `p ∈ [0, 1]` and sharing benefit `α` (NRTV §23.3.2). -/
@[expose] noncomputable def penaltyThreshold (α x p : ℝ) : ℝ :=
  requestLoad x p / x - α * p * x

/-- Equilibrium condition under service differentiation penalty `p`: `x ∈ (0, 1]` and
`x = tail (penaltyThreshold α x p)`. -/
@[expose] def penaltyEquilibrium (tail : ℝ → ℝ) (α p x : ℝ) : Prop :=
  0 < x ∧ x ≤ 1 ∧ x = tail (penaltyThreshold α x p)

/-- Per-capita utilitarian social welfare `α * serviceRate x p - requestLoad x p` under penalty
`p`, reducing to `minimalistWelfare α x` at `p = 0`. -/
@[expose] def penaltyWelfare (α x p : ℝ) : ℝ :=
  α * serviceRate x p - requestLoad x p

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
  have h1α : 1 ≤ α * p := by
    have h := (div_le_iff₀ hα).mp hp
    linarith
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
@[expose] noncomputable def exclHighRoot (θ_m z : ℝ) : ℝ :=
  (θ_m + Real.sqrt (θ_m * (θ_m - 4 * (1 - z)))) / (2 * θ_m)

/-- Total social welfare under uniform exclusion fraction `z`: `(1 - z) * (α * x - 1)`. -/
@[expose] def exclWelfare (α x z : ℝ) : ℝ :=
  (1 - z) * (α * x - 1)

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
    have heq : (5 : ℝ) * (5 - 4) = 5 := by ring
    rw [heq]
    ring
  have h2 : exclWelfare 2 (exclHighRoot 5 (1 / 2)) (1 / 2) = Real.sqrt 15 / 10 := by
    simp only [exclWelfare, exclHighRoot]
    have heq : (5 : ℝ) * (5 - 4 * (1 - 1 / 2)) = 15 := by ring
    rw [heq]
    ring
  rw [h1, h2]
  have hlt : Real.sqrt 15 < 2 * Real.sqrt 5 := by
    have h2eq : 2 * Real.sqrt 5 = Real.sqrt 20 := by
      have : (20 : ℝ) = 2 ^ 2 * 5 := by norm_num
      rw [this, Real.sqrt_mul (sq_nonneg 2), Real.sqrt_sq (by norm_num)]
    rw [h2eq]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end Cslib.GameTheory.P2P
