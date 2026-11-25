/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Foundations.FieldTheory.Finite.Trinomial
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Dimensions of the binary Toeplitz packing

For a short cyclic axis of length `3 ^ (r + 1)`, the residue of `2` generates the unit group.
This makes the Frobenius conjugates distinct frequencies on that axis. Removing
the short factor from the binary field's multiplicative-group order leaves a
coprime long axis, so their product is cyclic.
-/

public section

namespace Cslib.Circuit.ToeplitzLowerBound

/-- Degree of the binary extension field used at stage `r`. -/
@[expose] def degree (r : ℕ) : ℕ := 2 * 3 ^ r

/-- Length of the Fourier axis separating the Frobenius conjugates. -/
@[expose] def short (r : ℕ) : ℕ := 3 ^ (r + 1)

/-- Order of the multiplicative group of the binary extension field. -/
@[expose] def size (r : ℕ) : ℕ := 2 ^ degree r - 1

/-- Length of each of the cyclic Fourier transforms packed at stage `r`. -/
@[expose] def long (r : ℕ) : ℕ := size r / short r

/-- Each stage has a positive extension degree. -/
theorem degree_pos (r : ℕ) : 0 < degree r := by unfold degree; positivity

/-- The short transform contains at least three coordinates. -/
theorem three_le_short (r : ℕ) : 3 ≤ short r := by
  have h : 0 < 3 ^ r := by positivity
  simp only [short, pow_succ]
  lia

/-- Adjoining zero to the multiplicative group recovers the whole field. -/
theorem size_add_one (r : ℕ) : size r + 1 = 2 ^ degree r := by
  have h : 0 < 2 ^ degree r := by positivity
  simp [size, Nat.sub_add_cancel h]

/-- The cyclic convolution at every stage has at least one coordinate. -/
theorem size_pos (r : ℕ) : 0 < size r := by
  have h := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (degree_pos r).ne'
  have := size_add_one r
  lia

/-- The conjugate frequencies use exactly two thirds of the short coordinates. -/
theorem degree_mul_three (r : ℕ) : degree r * 3 = 2 * short r := by
  simp [degree, short, pow_succ, Nat.mul_assoc]

/-- Successive field cardinalities are related by cubing. -/
theorem size_succ_add_one (r : ℕ) : size (r + 1) + 1 = (size r + 1) ^ 3 := by
  rw [size_add_one, size_add_one, ← pow_mul]
  simp [degree, pow_succ, Nat.mul_assoc]

private theorem short_dvd_pow_sub_one_iff (r e : ℕ) :
    short r ∣ 2 ^ e - 1 ↔ degree r ∣ e := by
  change 3 ^ (r + 1) ∣ 2 ^ e - 1 ↔ 2 * 3 ^ r ∣ e
  rw [← Cslib.orderOf_two_zmod_three_pow r, orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff]
  rw [Nat.cast_sub (Nat.one_le_pow e 2 (by decide)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    sub_eq_zero]

/-- The two cyclic axes fill all `size r` binary coordinates. -/
theorem long_mul_short (r : ℕ) : long r * short r = size r :=
  Nat.div_mul_cancel ((short_dvd_pow_sub_one_iff r _).2 dvd_rfl)

/-- The long axis is nonempty, including the first stage. -/
theorem long_pos (r : ℕ) : 0 < long r :=
  Nat.pos_of_mul_pos_right ((long_mul_short r).symm ▸ size_pos r)

/-- The long and short axes have coprime lengths, making their product cyclic. -/
theorem coprime_long_short (r : ℕ) : (long r).Coprime (short r) := by
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).2
  intro h
  have h' : short (r + 1) ∣ size r := by
    rw [← long_mul_short r]
    change 3 ^ ((r + 1) + 1) ∣ long r * 3 ^ (r + 1)
    rw [pow_succ, Nat.mul_comm (3 ^ (r + 1))]
    exact Nat.mul_dvd_mul_right h _
  have hd := Nat.le_of_dvd (degree_pos r) ((short_dvd_pow_sub_one_iff (r + 1) _).1 h')
  simp only [degree, pow_succ] at hd
  have hpos : 0 < 3 ^ r := by positivity
  lia

/-- Two is invertible modulo the long length, as required by the chirp identity. -/
theorem odd_long (r : ℕ) : Odd (long r) := by
  have hEven : Even (2 ^ degree r) := Even.pow_of_ne_zero (by decide : Even 2) (degree_pos r).ne'
  have hOdd : Odd (size r) := by
    rwa [← size_add_one, Nat.even_add_one, Nat.not_even_iff_odd] at hEven
  exact hOdd.of_dvd_nat ⟨short r, (long_mul_short r).symm⟩

/-- The Frobenius conjugate frequencies occupy distinct coordinates of the short transform. -/
theorem frobeniusFreq_injective (r : ℕ) :
    Function.Injective fun j : Fin (degree r) => (2 : ZMod (short r)) ^ j.val := by
  intro i j heq
  have h := Cslib.orderOf_two_zmod_three_pow r
  exact Fin.ext (pow_injOn_Iio_orderOf (h.symm ▸ i.isLt) (h.symm ▸ j.isLt) heq)

/-- The inverse Fourier transform on the short axis has normalization one in characteristic two. -/
theorem odd_short (r : ℕ) : Odd (short r) := (by decide : Odd 3).pow

/-- Largest stage fitting in dimension `m` when `m ≥ 3`, using two integer logarithms. -/
@[expose] def stage (m : ℕ) : ℕ := Nat.log 3 (Nat.log 2 (m + 1) / 2)

private theorem le_stage_iff {r m : ℕ} (hm : 3 ≤ m) : r ≤ stage m ↔ size r ≤ m := by
  have hlog : 2 ≤ Nat.log 2 (m + 1) :=
    Nat.le_log_of_pow_le (by decide) (by norm_num; lia)
  rw [stage, Nat.le_log_iff_pow_le (by decide) (by lia), Nat.le_div_iff_mul_le (by decide),
    Nat.mul_comm _ 2, ← degree, Nat.le_log_iff_pow_le (by decide) (by lia), ← size_add_one]
  lia

/-- The selected stage fits in the requested dimension and the next stage exceeds it. -/
theorem stage_bounds {m : ℕ} (hm : 3 ≤ m) :
    size (stage m) ≤ m ∧ m < size (stage m + 1) := by
  refine ⟨(le_stage_iff hm).1 le_rfl, ?_⟩
  by_contra! h
  have := (le_stage_iff hm).2 h
  lia

/-- Every fixed stage is eventually passed by the stage-selection algorithm. -/
theorem tendsto_stage : Filter.Tendsto stage Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro r
  filter_upwards [Filter.eventually_ge_atTop (max 3 (size r))] with m hm
  exact (le_stage_iff ((le_max_left ..).trans hm)).2 ((le_max_right ..).trans hm)

open Filter Real Asymptotics

private theorem logb_size_ge_one (r : ℕ) : 1 ≤ logb 2 (size r) := by
  have hdeg : 2 ≤ degree r := by
    have := Nat.one_le_pow r 3 (by decide)
    unfold degree
    lia
  have hexp : 2 ^ 2 ≤ 2 ^ degree r := Nat.pow_le_pow_right (by decide) hdeg
  rw [← size_add_one] at hexp
  have hd : (2 : ℝ) ≤ size r := by norm_num at hexp; exact_mod_cast (by lia : 2 ≤ size r)
  simpa only [logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
    logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num) hd

private theorem logb_size_add_one_le (r : ℕ) :
    logb 2 ((size r : ℝ) + 1) ≤ 1 + logb 2 (size r) := by
  have hpos : 0 < (size r : ℝ) := by exact_mod_cast size_pos r
  have hone : 1 ≤ (size r : ℝ) := by exact_mod_cast size_pos r
  calc logb 2 ((size r : ℝ) + 1)
    _ ≤ logb 2 (2 * (size r : ℝ)) :=
      logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
    _ = _ := by rw [logb_mul (by norm_num) hpos.ne', logb_self_eq_one (by norm_num)]

/-- The largest stage below an arbitrary dimension preserves its logarithm within a factor six. -/
theorem logb_le_stage (m : ℕ) (hm : 3 ≤ m) :
    logb 2 m ≤ 6 * logb 2 (size (stage m)) := by
  have hdim : m ≤ (size (stage m) + 1) ^ 3 := by
    have h := (stage_bounds hm).2
    have h' := size_succ_add_one (stage m)
    lia
  have hreal : (m : ℝ) ≤ ((size (stage m) : ℝ) + 1) ^ 3 := by exact_mod_cast hdim
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by lia : 0 < m)
  have h := logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hmpos hreal
  rw [logb_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [logb_size_add_one_le (stage m), logb_size_ge_one (stage m)]

private theorem short_le_logb_size (r : ℕ) : (short r : ℝ) ≤ 3 * logb 2 (size r) := by
  have hsize : (size r : ℝ) + 1 = (2 : ℝ) ^ degree r := by exact_mod_cast size_add_one r
  have h := logb_size_add_one_le r
  rw [hsize, logb_pow, logb_self_eq_one (by norm_num), mul_one] at h
  have hd : (degree r : ℝ) * 3 = 2 * (short r : ℝ) := by exact_mod_cast degree_mul_three r
  linarith [logb_size_ge_one r]

private theorem tendsto_short : Tendsto (fun r => (short r : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    ((tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (3 : ℕ))).comp (tendsto_add_atTop_nat 1))

private theorem logb_size_le_long : ∀ᶠ r in atTop, logb 2 (size r) ≤ 2 * logb 2 (long r) := by
  have h := (isLittleO_logb_id_atTop (b := 2)).bound (by norm_num : (0 : ℝ) < 1/6)
  filter_upwards [tendsto_short.eventually h] with r h
  have hs : 1 ≤ (short r : ℝ) := by
    exact_mod_cast (by have := three_le_short r; lia : 1 ≤ short r)
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg (logb_nonneg (by norm_num : (1 : ℝ) < 2) hs),
    abs_of_nonneg (by linarith : 0 ≤ (short r : ℝ))] at h
  have hm : (long r : ℝ) * (short r : ℝ) = size r := by exact_mod_cast long_mul_short r
  have hl : 0 < (long r : ℝ) := by exact_mod_cast long_pos r
  have hsum : logb 2 (size r) = logb 2 (long r) + logb 2 (short r) := by
    rw [← hm, logb_mul hl.ne' (by linarith)]
  linarith [short_le_logb_size r]

/-- At large stages the two short transforms cost a vanishing fraction of the long transform's
square-root logarithm. The dimension comparisons hold uniformly before choosing a batch size. -/
theorem eventually_log_bounds {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in atTop, 2 ≤ long r ∧ logb 2 (size r) ≤ 2 * logb 2 (long r) ∧
      1 + logb 2 (short r) ≤ ε * sqrt (logb 2 (long r)) := by
  have hlog : (logb 2) =o[atTop] sqrt := by
    rw [show logb 2 = (fun x => (log 2)⁻¹ * log x) by funext x; rw [Real.logb, div_eq_inv_mul],
      show sqrt = (fun x : ℝ => x ^ (1 / 2 : ℝ)) by funext x; exact sqrt_eq_rpow x]
    exact (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).const_mul_left (log 2)⁻¹
  have hone : (fun _ : ℝ => (1 : ℝ)) =o[atTop] sqrt :=
    (isLittleO_const_left_of_ne one_ne_zero).2 (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)] using Real.tendsto_sqrt_atTop)
  have h := (hone.add hlog).bound (by positivity : 0 < ε / 3)
  filter_upwards [tendsto_short.eventually h, logb_size_le_long] with r h hratio
  have hl : 1 ≤ (long r : ℝ) := by exact_mod_cast long_pos r
  have hs : 1 ≤ (short r : ℝ) := by exact_mod_cast (by have := three_le_short r; lia : 1 ≤ short r)
  have hlogl := logb_nonneg (by norm_num : (1 : ℝ) < 2) hl
  have hlogs := logb_nonneg (by norm_num : (1 : ℝ) < 2) hs
  have hlong : 2 ≤ long r := by
    by_contra! hlt
    have := long_pos r
    have heq : long r = 1 := by lia
    simp [heq] at hratio
    linarith [logb_size_ge_one r]
  refine ⟨hlong, hratio, ?_⟩
  simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 1 + logb 2 (short r) by linarith),
    abs_of_nonneg (sqrt_nonneg _)] at h
  have hsqrt : sqrt (short r) ≤ 3 * sqrt (logb 2 (long r)) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_sqrt hlogl, short_le_logb_size r]
  calc
    _ ≤ (ε / 3) * sqrt (short r) := h
    _ ≤ (ε / 3) * (3 * sqrt (logb 2 (long r))) := by gcongr
    _ = _ := by ring

/-- A batched long-transform lower estimate absorbs the two short-transform upper estimates.
Taking as many copies as fit gives the bound at every sufficiently large binary dimension. -/
theorem eventually_batch_bound {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, let r := stage m; let j := m / size r
      1 ≤ j ∧ j * size r ≤ m ∧ 2 ≤ long r ∧ ∀ p : ℕ,
        c * j * degree r * long r * sqrt (logb 2 (long r)) ≤
            p + 2 * C * j * long r * short r * (1 + logb 2 (short r)) →
        (c / 36) * m * sqrt (logb 2 m) ≤ p := by
  have εpos : 0 < c / (6 * C) := by positivity
  filter_upwards [eventually_ge_atTop 3, tendsto_stage.eventually (eventually_log_bounds εpos)]
    with m hm h
  let r := stage m
  let j := m / size r
  have hd : 0 < size r := size_pos r
  have hdm : size r ≤ m := (stage_bounds hm).1
  have hj : 1 ≤ j := (Nat.le_div_iff_mul_le hd).2 (by simpa using hdm)
  refine ⟨hj, Nat.div_mul_le_self .., h.1, ?_⟩
  intro p hp
  have hfill : m ≤ 2 * (j * size r) := by
    have hcovered : size r ≤ j * size r := by simpa using Nat.mul_le_mul_right (size r) hj
    have hrest := Nat.mod_lt m hd
    have hadd := Nat.mod_add_div m (size r)
    rw [Nat.mul_comm (size r)] at hadd
    change m % size r + j * size r = m at hadd
    lia
  have hfill' : (m : ℝ) ≤ 2 * ((j : ℝ) * (size r : ℝ)) := by exact_mod_cast hfill
  have hdim : (long r : ℝ) * short r = size r := by exact_mod_cast long_mul_short r
  have haxes : (degree r : ℝ) * long r = (2 / 3 : ℝ) * size r := by
    have heq : (degree r : ℝ) * 3 = 2 * short r := by exact_mod_cast degree_mul_three r
    linear_combination (long r : ℝ) / 3 * heq + (2 / 3 : ℝ) * hdim
  have hl : 0 ≤ logb 2 (long r) :=
    logb_nonneg (by norm_num) (by exact_mod_cast long_pos r)
  have hroot : sqrt (logb 2 m) ≤ 6 * sqrt (logb 2 (long r)) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hratio : logb 2 (size r) ≤ 2 * logb 2 (long r) := h.2.1
    have hstage : logb 2 m ≤ 6 * logb 2 (size r) := logb_le_stage m hm
    nlinarith [sq_sqrt hl]
  have hshort : 2 * C * j * long r * short r * (1 + logb 2 (short r)) ≤
      (c / 3) * ((j : ℝ) * size r) * sqrt (logb 2 (long r)) := by
    calc
      _ = (2 * C * ((j : ℝ) * size r)) * (1 + logb 2 (short r)) := by rw [← hdim]; ring
      _ ≤ (2 * C * ((j : ℝ) * size r)) * (c / (6 * C) * sqrt (logb 2 (long r))) :=
        mul_le_mul_of_nonneg_left h.2.2 (by positivity)
      _ = _ := by field_simp; ring
  have hlong : (c / 3) * ((j : ℝ) * size r) * sqrt (logb 2 (long r)) ≤ p := by
    change c * j * degree r * long r * sqrt (logb 2 (long r)) ≤
      p + 2 * C * j * long r * short r * (1 + logb 2 (short r)) at hp
    rw [mul_assoc (c * j) _ (long r : ℝ), haxes] at hp
    linarith
  calc
    _ ≤ (c / 36) * (2 * ((j : ℝ) * size r)) * (6 * sqrt (logb 2 (long r))) := by gcongr
    _ = (c / 3) * ((j : ℝ) * size r) * sqrt (logb 2 (long r)) := by ring
    _ ≤ _ := hlong

end Cslib.Circuit.ToeplitzLowerBound
