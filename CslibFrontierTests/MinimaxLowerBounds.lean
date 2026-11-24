/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Probability.Minimax.Assouad
import CslibFrontier.Probability.Minimax.Fano
import CslibFrontier.Probability.Minimax.LeCam

/-!
# Checked tests for KL tensorization, Le Cam, Fano, and Assouad minimax lower bounds

Exercises `CslibFrontier.Probability.Divergence.Pi`, `CslibFrontier.Probability.Minimax.LeCam`,
`CslibFrontier.Probability.Minimax.Fano`, and `CslibFrontier.Probability.Minimax.Assouad` on
concrete finite instances and model boundaries:

1. Exact `n = 3` coin KL tensorization and the golden mixture identity.
2. Tightness witness for `leCam_max_ge`: on `coin (1/4)` vs. `coin (3/4)`, the maximum-likelihood
   estimator attains `(sep / 2) · (1 - dist p₀ p₁) = 1 / 4` with exact equality, plus concrete
   `n = 4` Bernoulli mean lower bounds (`≥ 1 / 288` in `L²` and `≥ 1 / 24` in `L¹`).
3. Non-vacuous `Fin 4` packing witness for `fano_minimax_risk_ge_of_klDiv_center` and
   `fano_randomized_minimax_risk_ge_of_klDiv_center` giving strictly positive risk `≥ 1 / 4`.
4. Concrete `Fin 3`, `n = 4` high-dimensional product-Bernoulli checks of Assouad's lemma
   (`≥ 1 / 96` in squared `ℓ₂` and `≥ 1 / 8` in `ℓ₁`), plus the `Fin 0` empty-cube boundary.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.MinimaxLowerBounds

open Cslib.Probability Cslib.Probability.PMF MeasureTheory InformationTheory Finset
open scoped BigOperators ENNReal unitInterval

/-! ### 1. KL tensorization on coins (`n = 3`) -/

theorem coin_iid_three_klDiv_checked :
    let p₀ : I := ⟨1 / 4, by norm_num⟩
    let p₁ : I := ⟨3 / 4, by norm_num⟩
    (klDiv (iid (coin p₀) 3).toMeasure (iid (coin p₁) 3).toMeasure).toReal =
      3 * (klDiv (coin p₀).toMeasure (coin p₁).toMeasure).toReal := by
  intro p₀ p₁
  have hsupp : (coin p₀).support ⊆ (coin p₁).support := fun b _ =>
    mem_support_coin_of_Ioo (p := p₁) (by norm_num [p₁]) (by norm_num [p₁]) b
  simpa only [Nat.cast_ofNat] using toReal_klDiv_iid hsupp 3

/-! ### 2. Sharpness of Le Cam's constant & `n = 4` Bernoulli bounds -/

/-- **Tightness witness for `leCam_max_ge`**: for `p₀ = coin (1/4)` and `p₁ = coin (3/4)` under
`0–1` loss (`sep = 1`), `dist p₀ p₁ = 1 / 2`, so Le Cam's bound is `(1 / 2) · (1 - 1 / 2) = 1 / 4`,
and the maximum-likelihood decoder `est b := b` achieves worst-case risk `1 / 4` with equality. -/
theorem leCam_max_tight_on_coins :
    let p₀ : I := ⟨1 / 4, by norm_num⟩
    let p₁ : I := ⟨3 / 4, by norm_num⟩
    let loss : Bool → Bool → ℝ := fun t θ => if t = θ then 0 else 1
    max (∑ b : Bool, (coin p₀ b).toReal * loss b false)
        (∑ b : Bool, (coin p₁ b).toReal * loss b true) = 1 / 4 ∧
      ∀ est : Bool → Bool,
        1 / 4 ≤ max (∑ b : Bool, (coin p₀ b).toReal * loss (est b) false)
          (∑ b : Bool, (coin p₁ b).toReal * loss (est b) true) := by
  intro p₀ p₁ loss
  have hdist : dist (coin p₀) (coin p₁) = 1 / 2 := by
    rw [dist_eq, Fintype.sum_bool]
    simp only [coin_apply_toReal, ↓reduceIte, Bool.false_eq_true, p₀, p₁]
    norm_num
  refine ⟨?_, fun est => ?_⟩
  · simp only [Fintype.sum_bool, coin_apply_toReal, ↓reduceIte, Bool.false_eq_true, loss,
      Bool.true_eq_false, p₀, p₁]
    norm_num
  · have h := leCam_max_ge (coin p₀) (coin p₁) (loss := loss) (θ₀ := false) (θ₁ := true) (sep := 1)
      (fun t => by cases t <;> simp [loss])
      (fun t => by cases t <;> simp [loss])
      (fun t => by cases t <;> norm_num [loss]) est
    rw [hdist] at h
    linarith

theorem bernoulli_n4_minimax_checked (est : (Fin 4 → Bool) → ℝ) :
    (∃ p : I, 1 / 288 ≤
      ∑ x : Fin 4 → Bool, (iid (coin p) 4 x).toReal * (est x - (p : ℝ)) ^ 2) ∧
    (∃ p : I, 1 / 24 ≤
      ∑ x : Fin 4 → Bool, (iid (coin p) 4 x).toReal * |est x - (p : ℝ)|) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp⟩ := bernoulli_mean_minimax_sq_lower_bound (n := 4) (by decide) est
    exact ⟨p, le_trans (by norm_num) hp⟩
  · obtain ⟨p, hp⟩ := bernoulli_mean_minimax_abs_lower_bound (n := 4) (by decide) est
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Nat.cast_ofNat, hsqrt4] at hp
    exact ⟨p, by linarith⟩

/-! ### 3. Non-vacuous `Fin 4` packing witness for KL-Fano (`risk ≥ 1 / 4 > 0`) -/

/-- Randomized-estimator Fano check on `V = Fin 4` under `0–1` loss (`Δ = 1 / 2`, `2 Δ = 1`): every
randomized estimator `est : Fin 4 → PMF (Fin 4)` on an uninformative observation incurs expected
error probability at least `1 / 4` at some `v : Fin 4`. -/
theorem fano_fin4_randomized_checked (est : Fin 4 → PMF (Fin 4)) :
    ∃ v : Fin 4, (1 / 4 : ℝ) ≤
      ∑ x : Fin 4, (uniformOfFintype (Fin 4) x).toReal *
        ∑ t : Fin 4, (est x t).toReal * (if t = v then (0 : ℝ) else 1) := by
  let : MeasurableSpace (Fin 4) := ⊤
  let P : Fin 4 → PMF (Fin 4) := fun _ => uniformOfFintype (Fin 4)
  obtain ⟨v, hv⟩ := fano_randomized_minimax_risk_ge_of_klDiv_center (V := Fin 4) (by decide) P
    (Q := uniformOfFintype (Fin 4)) (β := 0) (fun _ => Set.Subset.rfl)
    (by simp [P, klDiv_self])
    (loss := fun (t v : Fin 4) => if t = v then (0 : ℝ) else 1) (θ := id) (Δ := 1 / 2)
    (by norm_num) (fun t v => by split_ifs <;> norm_num)
    (fun t v w hne => by
      by_cases htv : t = v
      · subst htv; simp [hne]
      · by_cases htw : t = w
        · subst htw; simp [Ne.symm hne]
        · simp [htv, htw])
    est
  refine ⟨v, le_trans ?_ hv⟩
  have hlog4 : Real.log ((Fintype.card (Fin 4) : ℕ) : ℝ) = 2 * Real.log 2 := by
    rw [Fintype.card_fin, show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  have hlog2_ne : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [hlog4, zero_add]
  field_simp
  linarith

/-- On `V = Fin 4` with uninformative observations `P _ = uniformOfFintype (Fin 4)` (`β = 0`) and
`1`-separated targets `θ v = (v : ℝ)` (`Δ = 1 / 2`), `fano_minimax_risk_ge_of_klDiv_center` proves
that every estimator `est : Fin 4 → ℝ` incurs expected absolute error at least `1 / 4` at some
`v : Fin 4`. -/
theorem fano_fin4_positive_lower_bound_checked (est : Fin 4 → ℝ) :
    ∃ v : Fin 4, (1 / 4 : ℝ) ≤
      ∑ x : Fin 4, (uniformOfFintype (Fin 4) x).toReal * |est x - (v : ℝ)| := by
  let : MeasurableSpace (Fin 4) := ⊤
  let P : Fin 4 → PMF (Fin 4) := fun _ => uniformOfFintype (Fin 4)
  obtain ⟨v, hv⟩ := fano_minimax_risk_ge_of_klDiv_center (V := Fin 4) (by decide) P
    (Q := uniformOfFintype (Fin 4)) (β := 0) (fun _ => Set.Subset.rfl)
    (by simp [P, klDiv_self])
    (loss := fun t (θ : ℝ) => |t - θ|) (θ := fun v : Fin 4 => (v : ℝ)) (Δ := 1 / 2)
    (by norm_num) (fun _ _ => abs_nonneg _)
    (fun t v w hne => by
      have hv_ne_w : (v : ℕ) ≠ (w : ℕ) := Fin.val_ne_of_ne hne
      have hgap : (1 : ℝ) ≤ |(v : ℝ) - (w : ℝ)| := by
        rcases lt_or_gt_of_ne hv_ne_w with hlt | hgt
        · have hle : (v : ℕ) + 1 ≤ (w : ℕ) := hlt
          have hcast : (v : ℝ) + 1 ≤ (w : ℝ) := by exact_mod_cast hle
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
        · have hle : (w : ℕ) + 1 ≤ (v : ℕ) := hgt
          have hcast : (w : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast hle
          rw [abs_of_nonneg (by linarith)]
          linarith
      have htri := abs_sub_le (v : ℝ) t (w : ℝ)
      rw [abs_sub_comm (v : ℝ) t] at htri
      linarith)
    est
  refine ⟨v, le_trans ?_ hv⟩
  have hlog4 : Real.log ((Fintype.card (Fin 4) : ℕ) : ℝ) = 2 * Real.log 2 := by
    rw [Fintype.card_fin, show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  have hlog2_ne : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [hlog4, zero_add]
  field_simp
  linarith

/-! ### 4. Concrete `Fin 3, n = 4` and `Fin 0` checks for Assouad's lemma -/

theorem assouad_fin3_n4_checked (est : (Fin 4 → Fin 3 → Bool) → (Fin 3 → ℝ)) :
    (∃ p : Fin 3 → I, 1 / 96 ≤
      ∑ x : Fin 4 → Fin 3 → Bool,
        (iid (pi fun i => coin (p i)) 4 x).toReal * ∑ i : Fin 3, (est x i - (p i : ℝ)) ^ 2) ∧
    (∃ p : Fin 3 → I, 1 / 8 ≤
      ∑ x : Fin 4 → Fin 3 → Bool,
        (iid (pi fun i => coin (p i)) 4 x).toReal * ∑ i : Fin 3, |est x i - (p i : ℝ)|) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp⟩ := product_bernoulli_minimax_sq_l2_lower_bound (ι := Fin 3) (n := 4)
      (by decide) est
    rw [Fintype.card_fin] at hp
    exact ⟨p, le_trans (by norm_num) hp⟩
  · obtain ⟨p, hp⟩ := product_bernoulli_minimax_l1_lower_bound (ι := Fin 3) (n := 4)
      (by decide) est
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Fintype.card_fin, Nat.cast_ofNat, Nat.cast_ofNat, hsqrt4] at hp
    exact ⟨p, by linarith⟩

/-- Empty-cube boundary (`ι = Fin 0`): `product_bernoulli_minimax_sq_l2_lower_bound` degenerates
cleanly to `0 ≤ 0` without vacuity. -/
theorem assouad_fin0_boundary_checked (est : (Fin 1 → Fin 0 → Bool) → (Fin 0 → ℝ)) :
    ∃ p : Fin 0 → I, 0 ≤
      ∑ x : Fin 1 → Fin 0 → Bool,
        (iid (pi fun i => coin (p i)) 1 x).toReal * ∑ i : Fin 0, (est x i - (p i : ℝ)) ^ 2 := by
  obtain ⟨p, hp⟩ := product_bernoulli_minimax_sq_l2_lower_bound (ι := Fin 0) (n := 1)
    (by decide) est
  rw [Fintype.card_fin, Nat.cast_zero, zero_div] at hp
  exact ⟨p, hp⟩

end CslibFrontierTests.MinimaxLowerBounds
