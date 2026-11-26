/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Polynomial-time fixed-point approximations of `π` and `exp(-z)`

Deterministic pure-`ℕ` fixed-point arithmetic certified under multi-tape Turing machine polynomial
time (`Turing.MultiTapeTM.ComputableInPolyTime`) in unary precision `qBits`:

1. `Cslib.FixedPointExp.piApprox`: Machin-formula fixed-point approximation of `π` to `qBits`
   fractional bits (using `Real.four_mul_arctan_inv_5_sub_arctan_inv_239`), with error at most
   `2 ^ (-qBits)`.
2. `Cslib.FixedPointExp.expNegSeries` and `Cslib.FixedPointExp.expNegPow`: alternating Taylor
   series for `exp(-z)` on `[0, 1]` (certified via `Real.exp_bound` and
   `Nat.factorial_mul_pow_le_factorial`) and `K`-fold range-reduced powering for `exp(-K * z)`.

## Main definitions

* `Cslib.FixedPointExp.piApprox`: `qBits`-bit fixed-point approximation of `π`.
* `Cslib.FixedPointExp.expNegSeries`: `qBits`-bit fixed-point approximation of `exp(-z)` for
  `z ∈ [0, 1]`.
* `Cslib.FixedPointExp.expNegPow`: `K`-fold range-reduced fixed-point approximation of
  `exp(-K * z)`.

## Main results

* `Cslib.FixedPointExp.abs_piApprox_div_sub_pi_le`,
  `Cslib.FixedPointExp.computableInPolyTime_piApprox`: error and polynomial-time certificates for
  `piApprox`.
* `Cslib.FixedPointExp.abs_expNegSeries_div_sub_exp_le`,
  `Cslib.FixedPointExp.computableInPolyTime_expNegSeries`: error and polynomial-time certificates
  for `expNegSeries`.
* `Cslib.FixedPointExp.abs_expNegPow_div_sub_exp_le`,
  `Cslib.FixedPointExp.computableInPolyTime_expNegPow`: error and polynomial-time certificates for
  `expNegPow`.
-/

public section

namespace Cslib.FixedPointExp

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Alternating `arctan` remainder bound -/

private theorem arctan_alternating_remainder {x : ℝ} (hx0 : 0 ≤ x) (N : ℕ) :
    |Real.arctan x - ∑ k ∈ Finset.range (2 * N),
        ((-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1 : ℝ))| ≤
      x ^ (4 * N + 1) / (4 * N + 1 : ℝ) := by
  let g : ℝ → ℝ := fun t =>
    Real.arctan t - ∑ k ∈ Finset.range (2 * N), ((-1 : ℝ) ^ k * t ^ (2 * k + 1) / (2 * k + 1 : ℝ))
  have hpow_div (t : ℝ) (m : ℕ) :
      HasDerivAt (fun y : ℝ => y ^ (m + 1) / (m + 1 : ℝ)) (t ^ m) t := by
    have h1 := (hasDerivAt_pow (m + 1) t).div_const (m + 1 : ℝ)
    convert h1 using 1
    have hnz : (m + 1 : ℝ) ≠ 0 := by positivity
    rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    exact (mul_div_cancel_left₀ _ hnz).symm
  have hderiv (t : ℝ) : HasDerivAt g (t ^ (4 * N) / (1 + t ^ 2)) t := by
    have hsum : HasDerivAt
        (fun y : ℝ => ∑ k ∈ Finset.range (2 * N),
          ((-1 : ℝ) ^ k * y ^ (2 * k + 1) / (2 * k + 1 : ℝ)))
        (∑ k ∈ Finset.range (2 * N), (-t ^ 2) ^ k) t := by
      have hterm (k : ℕ) :
          HasDerivAt (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (2 * k + 1) / (2 * k + 1 : ℝ))
            ((-t ^ 2) ^ k) t := by
        have hp := (hpow_div t (2 * k)).const_mul ((-1 : ℝ) ^ k)
        convert hp using 1
        · funext y
          rw [mul_div_assoc, Nat.cast_mul, Nat.cast_ofNat]
        · rw [pow_mul, ← mul_pow, neg_one_mul]
      exact HasDerivAt.fun_sum fun k _ => hterm k
    have hdiff := (Real.hasDerivAt_arctan t).sub hsum
    convert hdiff using 1
    have hden : 1 + t ^ 2 ≠ 0 := by positivity
    have hgeom : (∑ k ∈ Finset.range (2 * N), (-t ^ 2) ^ k) * (1 + t ^ 2) =
        1 - (-t ^ 2) ^ (2 * N) := by
      have h := geom_sum_mul (-t ^ 2) (2 * N)
      have hsub : (-t ^ 2 : ℝ) - 1 = -(1 + t ^ 2) := by ring
      rw [hsub] at h
      linarith
    have heven : (-t ^ 2) ^ (2 * N) = t ^ (4 * N) := by
      rw [pow_mul, neg_sq, ← pow_mul, ← pow_mul]
      congr 1; ring
    rw [heven] at hgeom
    field_simp
    linarith
  have hg0 : g 0 = 0 := by
    simp [g]
  have ht4_nn (t : ℝ) : 0 ≤ t ^ (4 * N) := by
    rw [show 4 * N = 2 * (2 * N) by ring, pow_mul]
    positivity
  have hlo : 0 ≤ g x := by
    have hmono : MonotoneOn g (Set.Icc 0 x) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
        (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
        (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt)
        fun t _ => ?_
      rw [(hderiv t).deriv]
      exact div_nonneg (ht4_nn t) (by positivity)
    simpa [hg0] using hmono (Set.left_mem_Icc.mpr hx0) (Set.right_mem_Icc.mpr hx0) hx0
  have hhi : g x ≤ x ^ (4 * N + 1) / (4 * N + 1 : ℝ) := by
    let h : ℝ → ℝ := fun t => t ^ (4 * N + 1) / (4 * N + 1 : ℝ) - g t
    have hhderiv (t : ℝ) : HasDerivAt h (t ^ (4 * N) - t ^ (4 * N) / (1 + t ^ 2)) t := by
      have hp : HasDerivAt (fun y : ℝ => y ^ (4 * N + 1) / (4 * N + 1 : ℝ)) (t ^ (4 * N)) t := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpow_div t (4 * N)
      exact hp.sub (hderiv t)
    have hmono : MonotoneOn h (Set.Icc 0 x) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
        (fun t _ => (hhderiv t).continuousAt.continuousWithinAt)
        (fun t _ => (hhderiv t).differentiableAt.differentiableWithinAt)
        fun t _ => ?_
      rw [(hhderiv t).deriv]
      have h1 : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
      have hdiv : t ^ (4 * N) / (1 + t ^ 2) ≤ t ^ (4 * N) :=
        div_le_self (ht4_nn t) h1
      linarith
    have hh0 : h 0 = 0 := by simp [h, hg0]
    have := hmono (Set.left_mem_Icc.mpr hx0) (Set.right_mem_Icc.mpr hx0) hx0
    dsimp only [h] at this
    linarith [hh0]
  rw [abs_of_nonneg hlo]
  exact hhi

/-! ### 2. Pure-`ℕ` alternating `arctan (1 / d)` fixed-point loop -/

/-- Floor division in `ℕ` lies within `1` below the real quotient. -/
private theorem cast_div_bounds (a b : ℕ) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b ∧ (a : ℝ) / b < ((a / b : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  rw [div_lt_iff₀ (Nat.cast_pos.mpr hb), mul_comm]
  exact_mod_cast Nat.lt_mul_div_succ a hb

/-- One step of an alternating fixed-point accumulator: adding (even `n`) or subtracting (odd `n`)
a term within `e'` of its real value `t` moves the accumulator error by at most `e'`. -/
private theorem abs_altStep_sub_le {acc term n : ℕ} {A t B e e' : ℝ}
    (hB : B = A + (-1) ^ n * t) (hle : n % 2 = 1 → term ≤ acc) (ih : |(acc : ℝ) - A| ≤ e)
    (ht : |(term : ℝ) - t| ≤ e') :
    |((if n % 2 = 0 then acc + term else acc - term : ℕ) : ℝ) - B| ≤ e + e' := by
  subst hB
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [ite_eq_left h, (Nat.even_iff.mpr h).neg_one_pow, Nat.cast_add, one_mul,
      show (acc : ℝ) + term - (A + t) = (acc - A) + (term - t) by ring]
    exact (abs_add_le _ _).trans (add_le_add ih ht)
  · rw [ite_eq_right (by omega), (Nat.odd_iff.mpr h).neg_one_pow, Nat.cast_sub (hle h), neg_one_mul,
      show (acc : ℝ) - term - (A + -t) = (acc - A) - (term - t) by ring]
    exact (abs_sub _ _).trans (add_le_add ih ht)

/-- One step of fixed-point `arctan(1/d)` series at scale `S`: state is `(k, (powTerm, acc))`. -/
private def arctanStep (dSq : ℕ) (st : ℕ × (ℕ × ℕ)) : ℕ × (ℕ × ℕ) :=
  let k := st.1
  let powTerm := st.2.1
  let acc := st.2.2
  let term := powTerm / (2 * k + 1)
  let acc' := if k % 2 = 0 then acc + term else acc - term
  (k + 1, (powTerm / dSq, acc'))

/-- Fixed-point approximation to `2 ^ M * arctan (1 / d)` using `2 * L` terms. -/
private def arctanInvApprox (d M L : ℕ) : ℕ :=
  ((arctanStep (d * d))^[2 * L] (0, (2 ^ M / d, 0))).2.2

private theorem arctanStep_fst (dSq : ℕ) (st : ℕ × (ℕ × ℕ)) (i : ℕ) :
    ((arctanStep dSq)^[i] st).1 = st.1 + i := by
  induction i generalizing st with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [arctanStep]; omega

private theorem arctanStep_inv (d M : ℕ) (i : ℕ) :
    let st := (arctanStep (d * d))^[i] (0, (2 ^ M / d, 0))
    let term := st.2.1 / (2 * st.1 + 1)
    st.2.1 ≤ 2 ^ M ∧
      (if i % 2 = 0 then st.2.2 + term ≤ 2 ^ M else term ≤ st.2.2 ∧ st.2.2 ≤ 2 ^ M) := by
  induction i with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.zero_mod, ↓reduceIte, zero_add]
    exact ⟨Nat.div_le_self _ _, (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)⟩
  | succ i ih =>
    set st := (arctanStep (d * d))^[i] (0, (2 ^ M / d, 0)) with hst_def
    have hfst : st.1 = i := by simpa [hst_def] using arctanStep_fst (d * d) (0, (2 ^ M / d, 0)) i
    have hterm_le : (st.2.1 / (d * d)) / (2 * (i + 1) + 1) ≤ st.2.1 / (2 * i + 1) :=
      (Nat.div_le_div_right (Nat.div_le_self _ _)).trans
        (Nat.div_le_div_left (by omega) (by omega))
    have := Nat.div_le_self st.2.1 (d * d)
    rw [Function.iterate_succ_apply']
    dsimp only [arctanStep] at ih ⊢
    rw [← hst_def, hfst] at ⊢
    rw [hfst] at ih
    split_ifs at ih ⊢ <;> omega

private theorem arctanStep_powTerm_error (d M : ℕ) (hd : 5 ≤ d) (i : ℕ) :
    let p := ((arctanStep (d * d))^[i] (0, (2 ^ M / d, 0))).2.1
    (p : ℝ) ≤ (2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1) ∧
      (2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1) - (p : ℝ) ≤ 2 := by
  have hd2 : (25 : ℝ) ≤ (d : ℝ) ^ 2 := by
    have : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  induction i with
  | zero =>
    simp only [Function.iterate_zero, id_eq, mul_zero, zero_add, pow_one]
    have h := cast_div_bounds (2 ^ M) d
    push_cast at h
    exact ⟨h.1, by linarith [h.2]⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    dsimp only [arctanStep]
    set p := ((arctanStep (d * d))^[i] (0, (2 ^ M / d, 0))).2.1
    have h := cast_div_bounds p (d * d)
    rw [Nat.cast_mul, ← sq (d : ℝ)] at h
    have hpow : (2 : ℝ) ^ M / (d : ℝ) ^ (2 * (i + 1) + 1) =
        ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1)) / (d : ℝ) ^ 2 := by
      rw [div_div, ← pow_add, show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by omega]
    rw [hpow]
    refine ⟨h.1.trans (div_le_div_of_nonneg_right ih.1 (by positivity)), ?_⟩
    have hstep : (2 : ℝ) ^ M / (d : ℝ) ^ (2 * i + 1) / (d : ℝ) ^ 2 - (p : ℝ) / (d : ℝ) ^ 2 ≤
        2 / 25 := by
      rw [← sub_div]
      exact (div_le_div_of_nonneg_right ih.2 (by positivity)).trans
        (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd2)
    linarith [h.2]

private theorem arctanInvApprox_series_error (d M L : ℕ) (hd : 5 ≤ d) :
    |((arctanInvApprox d M L : ℝ)) -
        (2 : ℝ) ^ M * ∑ k ∈ Finset.range (2 * L),
          ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))| ≤
      6 * (L : ℝ) := by
  have hgen : ∀ n : ℕ,
      |(((arctanStep (d * d))^[n] (0, (2 ^ M / d, 0))).2.2 : ℝ) -
          (2 : ℝ) ^ M * ∑ k ∈ Finset.range n,
            ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))| ≤
        3 * (n : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hinv := arctanStep_inv d M n
      have hp := arctanStep_powTerm_error d M hd n
      set st := (arctanStep (d * d))^[n] (0, (2 ^ M / d, 0))
      have hfst : st.1 = n := by simpa [st] using arctanStep_fst (d * d) (0, (2 ^ M / d, 0)) n
      dsimp only at hinv hp
      rw [hfst] at hinv
      have h := cast_div_bounds st.2.1 (2 * n + 1)
      set term : ℕ := st.2.1 / (2 * n + 1)
      push_cast at h
      have hterm_err :
          |(term : ℝ) - (2 : ℝ) ^ M * ((1 / (d : ℝ)) ^ (2 * n + 1) / (2 * n + 1 : ℝ))| ≤ 3 := by
        rw [one_div_pow, mul_div_assoc', mul_one_div]
        have h1 : ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * n + 1)) / (2 * n + 1 : ℝ) -
            (st.2.1 : ℝ) / (2 * n + 1 : ℝ) ≤ 2 := by
          rw [← sub_div]
          exact (div_le_self (by linarith [hp.1])
            (by linarith [Nat.cast_nonneg (α := ℝ) n])).trans hp.2
        have h2 : (st.2.1 : ℝ) / (2 * n + 1 : ℝ) ≤
            ((2 : ℝ) ^ M / (d : ℝ) ^ (2 * n + 1)) / (2 * n + 1 : ℝ) :=
          div_le_div_of_nonneg_right hp.1 (by positivity)
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]
      have hle : n % 2 = 1 → term ≤ st.2.2 := fun h => by
        rw [ite_eq_right (by omega)] at hinv; exact hinv.2.1
      rw [Function.iterate_succ_apply', Finset.sum_range_succ]
      dsimp only [arctanStep]
      rw [hfst]
      exact (abs_altStep_sub_le (by ring) hle ih hterm_err).trans_eq (by push_cast; ring)
  simpa only [arctanInvApprox, Nat.cast_mul, Nat.cast_ofNat,
    show (3 : ℝ) * (2 * (L : ℝ)) = 6 * (L : ℝ) by ring]
    using hgen (2 * L)

/-- Rounding-to-nearest error of `(raw + 2 ^ (g - 1)) / 2 ^ g` against `raw / 2 ^ g`. -/
theorem abs_div_two_pow_round_sub_le (raw g : ℕ) (hg : 1 ≤ g) :
    |(((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) - (raw : ℝ) / (2 : ℝ) ^ g| ≤ 1 / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  have h := cast_div_bounds (raw + 2 ^ k) (2 ^ (k + 1))
  have hhalf : (2 : ℝ) ^ k / 2 ^ (k + 1) = 1 / 2 := by rw [pow_succ]; field_simp
  push_cast at h
  rw [add_div, hhalf] at h
  rw [Nat.add_sub_cancel, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Guard bits for `piApprox qBits` ensuring total Machin rounding and truncation error
is strictly below `2 ^ (-qBits)`. -/
private def piGuard (qBits : ℕ) : ℕ := Nat.clog 2 (qBits + 8) + 10

/-- Pure-`ℕ` fixed-point Machin approximation to `2 ^ qBits * π` with round-to-nearest downshift. -/
def piApprox (qBits : ℕ) : ℕ :=
  let g := piGuard qBits
  let M := qBits + g
  let L := qBits + 4
  let raw := 16 * arctanInvApprox 5 M L - 4 * arctanInvApprox 239 M L
  (raw + 2 ^ (g - 1)) / 2 ^ g

/-- Fixed-point `π` approximation error is at most `2 ^ (-qBits)`. -/
theorem abs_piApprox_div_sub_pi_le (qBits : ℕ) :
    |(piApprox qBits : ℝ) / (2 : ℝ) ^ qBits - Real.pi| ≤ (2 : ℝ) ^ (-(qBits : ℤ)) := by
  set g := piGuard qBits
  set M := qBits + g
  set L := qBits + 4
  have hg10 : 10 ≤ g := by dsimp only [g, piGuard]; omega
  have h2g : (1024 : ℝ) * ((qBits : ℝ) + 8) ≤ (2 : ℝ) ^ g := by
    have hclog : qBits + 8 ≤ 2 ^ Nat.clog 2 (qBits + 8) := Nat.le_pow_clog (by omega) _
    have hpow : (2 : ℕ) ^ g = 2 ^ Nat.clog 2 (qBits + 8) * 1024 := by
      dsimp only [g, piGuard]
      rw [pow_add]
      norm_num
    have hmul : 1024 * (qBits + 8) ≤ 2 ^ g := by rw [hpow]; omega
    exact_mod_cast hmul
  have h2M : (2 : ℝ) ^ M = (2 : ℝ) ^ qBits * (2 : ℝ) ^ g := by
    dsimp only [M]; rw [pow_add]
  have hterm_full (d : ℕ) (hd : 5 ≤ d) :
      |(arctanInvApprox d M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / (d : ℝ))| ≤
        6 * (L : ℝ) / (2 : ℝ) ^ M + (1 / (d : ℝ)) ^ (4 * L + 1) / (4 * L + 1 : ℝ) := by
    have herr := arctanInvApprox_series_error d M L hd
    have htail := arctan_alternating_remainder (x := 1 / (d : ℝ)) (by positivity) L
    have h1 : |(arctanInvApprox d M L : ℝ) / (2 : ℝ) ^ M -
        ∑ k ∈ Finset.range (2 * L),
          ((-1 : ℝ) ^ k * (1 / (d : ℝ)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))| ≤
        6 * (L : ℝ) / (2 : ℝ) ^ M := by
      rw [← mul_div_cancel_left₀ (∑ k ∈ Finset.range (2 * L), _)
          (by positivity : (2 : ℝ) ^ M ≠ 0),
        ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)]
      exact div_le_div_of_nonneg_right herr (by positivity)
    exact (abs_sub_le _ _ _).trans (add_le_add h1 (by rwa [abs_sub_comm] at htail))
  have h5_full : |(arctanInvApprox 5 M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / 5)| ≤
      6 * (L : ℝ) / (2 : ℝ) ^ M + (1 / 5 : ℝ) ^ (4 * L + 1) / (4 * L + 1 : ℝ) := by
    simpa using hterm_full 5 (by omega)
  have h239_full : |(arctanInvApprox 239 M L : ℝ) / (2 : ℝ) ^ M - Real.arctan (1 / 239)| ≤
      6 * (L : ℝ) / (2 : ℝ) ^ M + (1 / 239 : ℝ) ^ (4 * L + 1) / (4 * L + 1 : ℝ) := by
    simpa using hterm_full 239 (by omega)
  have h5_pow : (1 / 5 : ℝ) ^ (4 * L + 1) ≤ (1 / 625 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
    have hpow1 : (1 / 5 : ℝ) ^ (4 * L + 1) ≤ (1 / 5 : ℝ) ^ (qBits + 4) := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      dsimp only [L]; omega
    have hpow2 : (1 / 5 : ℝ) ^ (qBits + 4) = (1 / 625 : ℝ) * (1 / 5 : ℝ) ^ qBits := by
      rw [pow_add]; norm_num; ring
    have hpow3 : (1 / 5 : ℝ) ^ qBits ≤ (1 / 2 : ℝ) ^ qBits :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    linarith [mul_le_mul_of_nonneg_left hpow3 (by norm_num : (0 : ℝ) ≤ 1 / 625)]
  have h239_pow : (1 / 239 : ℝ) ^ (4 * L + 1) ≤ (1 / 5 : ℝ) ^ (4 * L + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hround_small : 120 * (L : ℝ) / (2 : ℝ) ^ M ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) := by
    rw [h2M, zpow_neg, zpow_natCast, ← one_div, div_mul_eq_div_div, mul_one_div]
    have h1 : 120 * (L : ℝ) / (2 : ℝ) ^ g ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have hL : (L : ℝ) = (qBits : ℝ) + 4 := by dsimp only [L]; push_cast; ring
      linarith
    have h2 : 120 * (L : ℝ) / (2 : ℝ) ^ qBits / (2 : ℝ) ^ g =
        (120 * (L : ℝ) / (2 : ℝ) ^ g) / (2 : ℝ) ^ qBits := by ring
    rw [h2]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have hraw_real :
      |(16 * (arctanInvApprox 5 M L : ℝ) - 4 * (arctanInvApprox 239 M L : ℝ)) / (2 : ℝ) ^ M -
          Real.pi| ≤
        (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) := by
    have hpi := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    rw [← one_div, ← one_div] at hpi
    have hden1 : (1 : ℝ) ≤ (4 * L + 1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) L]
    have htail5 := (div_le_self (by positivity) hden1).trans h5_pow
    have htail239 := (div_le_self (by positivity) hden1).trans (h239_pow.trans h5_pow)
    have hzpos : (0 : ℝ) < (2 : ℝ) ^ (-(qBits : ℤ)) := by positivity
    have hcomb : 16 * (6 * (L : ℝ) / (2 : ℝ) ^ M) + 4 * (6 * (L : ℝ) / (2 : ℝ) ^ M) =
        120 * (L : ℝ) / (2 : ℝ) ^ M := by ring
    obtain ⟨h5l, h5r⟩ := abs_le.mp h5_full
    obtain ⟨h239l, h239r⟩ := abs_le.mp h239_full
    rw [abs_le, sub_div, mul_div_assoc, mul_div_assoc]
    constructor <;> linarith
  have hge : 4 * arctanInvApprox 239 M L ≤ 16 * arctanInvApprox 5 M L := by
    have hz1 : (2 : ℝ) ^ (-(qBits : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hpos : (0 : ℝ) < (16 * (arctanInvApprox 5 M L : ℝ) -
        4 * (arctanInvApprox 239 M L : ℝ)) / (2 : ℝ) ^ M := by
      linarith [(abs_le.mp hraw_real).1, Real.pi_gt_three]
    exact_mod_cast (sub_pos.mp ((div_pos_iff_of_pos_right (by positivity)).mp hpos)).le
  set raw : ℕ := 16 * arctanInvApprox 5 M L - 4 * arctanInvApprox 239 M L
  have hraw_cast : (raw : ℝ) =
      16 * (arctanInvApprox 5 M L : ℝ) - 4 * (arctanInvApprox 239 M L : ℝ) := by
    dsimp only [raw]
    rw [Nat.cast_sub hge, Nat.cast_mul, Nat.cast_mul]
    norm_num
  have hshift : |((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) - (raw : ℝ) / (2 : ℝ) ^ g| ≤ 1 / 2 :=
    abs_div_two_pow_round_sub_le raw g (by omega)
  have hpi_eq : piApprox qBits = (raw + 2 ^ (g - 1)) / 2 ^ g := rfl
  rw [hpi_eq]
  have hshift_scaled :
      |(((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) / (2 : ℝ) ^ qBits - (raw : ℝ) / (2 : ℝ) ^ M| ≤
        (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) := by
    rw [h2M, div_mul_eq_div_div, div_right_comm (raw : ℝ), ← sub_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ qBits),
      zpow_neg, zpow_natCast, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hshift (by positivity)
  rw [← hraw_cast] at hraw_real
  calc
    |(((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) / (2 : ℝ) ^ qBits - Real.pi| ≤
        |(((raw + 2 ^ (g - 1)) / 2 ^ g : ℕ) : ℝ) / (2 : ℝ) ^ qBits - (raw : ℝ) / (2 : ℝ) ^ M| +
          |(raw : ℝ) / (2 : ℝ) ^ M - Real.pi| := abs_sub_le _ _ _
    _ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) + (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qBits : ℤ)) := by gcongr
    _ = (2 : ℝ) ^ (-(qBits : ℤ)) := by ring

private theorem computableInPolyTime_arctanInvApprox (d : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => arctanInvApprox d p.1 p.2)
      (encPair encUnary encUnary) encNat := by
  have hcount : ComputableInPolyTime (fun p : ℕ × ℕ => 2 * p.2)
      (encPair encUnary encUnary) encUnary :=
    unary_mul' (const 2) (snd encUnary encUnary)
  have hinit : ComputableInPolyTime (fun p : ℕ × ℕ => (0, (2 ^ p.1 / d, 0)))
      (encPair encUnary encUnary) (encPair encNat (encPair encNat encNat)) :=
    (const 0).prod
      ((binary_div' (binary_two_pow.comp (fst encUnary encUnary)) (const d)).prod (const 0))
  have hstep : ComputableInPolyTime (arctanStep (d * d))
      (encPair encNat (encPair encNat encNat)) (encPair encNat (encPair encNat encNat)) := by
    unfold arctanStep
    have hk := fst encNat (encPair encNat encNat)
    have hpow := (snd encNat (encPair encNat encNat)).fst'
    have hacc := (snd encNat (encPair encNat encNat)).snd'
    have hterm := binary_div' hpow (binary_add' (binary_mul' (const 2) hk) (const 1))
    have hcond : ComputableInPolyTime (fun st : ℕ × (ℕ × ℕ) => decide (st.1 % 2 = 0))
        (encPair encNat (encPair encNat encNat)) encBool :=
      decide_eq' (binary_mod' hk (const 2)) (const 0)
    have hacc' := ite_decide hcond (binary_add' hacc hterm) (binary_sub' hacc hterm)
    exact (binary_add' hk (const 1)).prod ((binary_div' hpow (const (d * d))).prod hacc')
  have hiter := iterate hcount hinit hstep
    (bound := fun p => 12 * (encPair encUnary encUnary p).length + 20)
    (((PolyBounded.const 12).mul .self).add (.const 20))
    (fun p i hi => by
      have hinv := arctanStep_inv d p.1 i
      have hfst : ((arctanStep (d * d))^[i] (0, (2 ^ p.1 / d, 0))).1 = i := by
        simpa using arctanStep_fst (d * d) (0, (2 ^ p.1 / d, 0)) i
      dsimp only at hinv
      have hacc_le : ((arctanStep (d * d))^[i] (0, (2 ^ p.1 / d, 0))).2.2 ≤ 2 ^ p.1 := by
        split_ifs at hinv
        exacts [(Nat.le_add_right _ _).trans hinv.2, hinv.2.2]
      have hl1 := length_encNat_le_of_lt_two_pow (lt_of_le_of_lt hi Nat.lt_two_pow_self)
      have hl2 :=
        length_encNat_le_of_lt_two_pow (hinv.1.trans_lt (Nat.pow_lt_pow_succ one_lt_two))
      have hl3 :=
        length_encNat_le_of_lt_two_pow (hacc_le.trans_lt (Nat.pow_lt_pow_succ one_lt_two))
      simp only [length_encPair, encUnary_apply, List.length_replicate, hfst] at hl1 hl2 hl3 ⊢
      omega)
  exact hiter.snd'.snd'

private theorem computableInPolyTime_piGuard : ComputableInPolyTime piGuard encUnary encUnary := by
  unfold piGuard
  exact unary_add' (binary_clog_two.comp (unary_to_binary.comp (unary_add' id' (const 8))))
    (const 10)

/-- `piApprox` is computable in polynomial time in unary precision `qBits`. -/
theorem computableInPolyTime_piApprox : ComputableInPolyTime piApprox encUnary encNat := by
  unfold piApprox
  have hg := computableInPolyTime_piGuard
  have hM : ComputableInPolyTime (fun q => q + piGuard q) encUnary encUnary :=
    unary_add' id' hg
  have hL : ComputableInPolyTime (fun q => q + 4) encUnary encUnary :=
    unary_add' id' (const 4)
  have ha5 := (computableInPolyTime_arctanInvApprox 5).comp (hM.prod hL)
  have ha239 := (computableInPolyTime_arctanInvApprox 239).comp (hM.prod hL)
  have hraw := binary_sub' (binary_mul' (const 16) ha5) (binary_mul' (const 4) ha239)
  have hhalf := binary_two_pow.comp (unary_sub' hg (const 1))
  have hden := binary_two_pow.comp hg
  exact binary_div' (binary_add' hraw hhalf) hden


/-! ### 3. Pure-`ℕ` fixed-point `exp(-z)` and range-reduced powering -/

private def expNegStep (par : ℕ × ℕ) (st : ℕ × (ℕ × ℕ)) : ℕ × (ℕ × ℕ) :=
  let S := par.1
  let zFp := par.2
  let j := st.1
  let term := st.2.1
  let acc := st.2.2
  let acc' := if j % 2 = 0 then acc + term else acc - term
  let term' := (term * zFp) / ((j + 1) * S)
  (j + 1, (term', acc'))

/-- Fixed-point approximation to `2 ^ qBits * exp(-zFp / 2 ^ qBits)`
using `2 * (qBits + 2)` terms. -/
def expNegSeries (qBits zFp : ℕ) : ℕ :=
  let S := 2 ^ qBits
  let zC := min zFp S
  let (_, (_, acc)) := (expNegStep (S, zC))^[2 * (qBits + 2)] (0, (S, 0))
  acc

/-- Range-reduced fixed-point approximation of `exp(-K * zFp / 2 ^ qBits)` via `K`-fold
fixed-point multiplication `(P_r * base) / 2 ^ qBits` starting from `2 ^ qBits`. -/
def expNegPow (qBits zFp K : ℕ) : ℕ :=
  let S := 2 ^ qBits
  let b := expNegSeries qBits zFp
  (fun p => (p * b) / S)^[K] S

private theorem expNegStep_fst (par : ℕ × ℕ) (st : ℕ × (ℕ × ℕ)) (i : ℕ) :
    ((expNegStep par)^[i] st).1 = st.1 + i := by
  induction i generalizing st with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [expNegStep]; omega

private theorem expNegStep_inv (S zC : ℕ) (hz : zC ≤ S) (i : ℕ) :
    let st := (expNegStep (S, zC))^[i] (0, (S, 0))
    st.2.1 ≤ S ∧ (if i % 2 = 0 then st.2.2 + st.2.1 ≤ S else st.2.1 ≤ st.2.2 ∧ st.2.2 ≤ S) := by
  induction i with
  | zero => simp
  | succ i ih =>
    set st := (expNegStep (S, zC))^[i] (0, (S, 0)) with hst_def
    have hfst : st.1 = i := by simpa [hst_def] using expNegStep_fst (S, zC) (0, (S, 0)) i
    have hterm_le : (st.2.1 * zC) / ((i + 1) * S) ≤ st.2.1 := Nat.div_le_of_le_mul <| by
      nlinarith [Nat.mul_le_mul_left st.2.1 hz, Nat.zero_le (i * S * st.2.1)]
    rw [Function.iterate_succ_apply']
    dsimp only [expNegStep] at ih ⊢
    rw [← hst_def, hfst]
    split_ifs at ih ⊢ <;> omega

/-- `expNegSeries qBits zFp` stays in `[0, 2 ^ qBits]`. -/
theorem expNegSeries_le (qBits zFp : ℕ) : expNegSeries qBits zFp ≤ 2 ^ qBits := by
  have hinv := expNegStep_inv (2 ^ qBits) (min zFp (2 ^ qBits)) (min_le_right _ _) (2 * (qBits + 2))
  have hev : (2 * (qBits + 2)) % 2 = 0 := by omega
  simp only [hev, ↓reduceIte] at hinv
  change ((expNegStep (2 ^ qBits, min zFp (2 ^ qBits)))^[2 * (qBits + 2)]
    (0, (2 ^ qBits, 0))).2.2 ≤ _
  omega

private theorem expNegPow_step_le (S b : ℕ) (hb : b ≤ S) (p : ℕ) (hp : p ≤ S) :
    (p * b) / S ≤ S :=
  Nat.div_le_of_le_mul (Nat.mul_le_mul hp hb)

/-- `expNegPow qBits zFp K` stays in `[0, 2 ^ qBits]`. -/
theorem expNegPow_le (qBits zFp K : ℕ) : expNegPow qBits zFp K ≤ 2 ^ qBits := by
  unfold expNegPow
  have hb := expNegSeries_le qBits zFp
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Function.iterate_succ_apply']
    exact expNegPow_step_le _ _ hb _ ih

/-- `expNegSeries` is computable in polynomial time. -/
theorem computableInPolyTime_expNegSeries :
    ComputableInPolyTime (fun p : ℕ × ℕ => expNegSeries p.1 p.2)
      (encPair encUnary encNat) encNat := by
  have hS : ComputableInPolyTime (fun p : ℕ × ℕ => 2 ^ p.1)
      (encPair encUnary encNat) encNat :=
    binary_two_pow.comp (fst encUnary encNat)
  have hzC : ComputableInPolyTime (fun p : ℕ × ℕ => min p.2 (2 ^ p.1))
      (encPair encUnary encNat) encNat :=
    binary_min' (snd encUnary encNat) hS
  have hpar := hS.prod hzC
  have hcount : ComputableInPolyTime (fun p : ℕ × ℕ => 2 * (p.1 + 2))
      (encPair encUnary encNat) encUnary :=
    unary_mul' (const 2) (unary_add' (fst encUnary encNat) (const 2))
  have hinit : ComputableInPolyTime (fun p : ℕ × ℕ => (0, (2 ^ p.1, 0)))
      (encPair encUnary encNat) (encPair encNat (encPair encNat encNat)) :=
    (const 0).prod (hS.prod (const 0))
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => expNegStep q.1 q.2)
      (encPair (encPair encNat encNat) (encPair encNat (encPair encNat encNat)))
      (encPair encNat (encPair encNat encNat)) := by
    unfold expNegStep
    have hpar_q := fst (encPair encNat encNat) (encPair encNat (encPair encNat encNat))
    have hst_q := snd (encPair encNat encNat) (encPair encNat (encPair encNat encNat))
    have hSq := hpar_q.fst'
    have hzq := hpar_q.snd'
    have hj := hst_q.fst'
    have hterm := hst_q.snd'.fst'
    have hacc := hst_q.snd'.snd'
    have hcond : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) => decide (q.2.1 % 2 = 0))
        (encPair (encPair encNat encNat) (encPair encNat (encPair encNat encNat))) encBool :=
      decide_eq' (binary_mod' hj (const 2)) (const 0)
    have hacc' := ite_decide hcond (binary_add' hacc hterm) (binary_sub' hacc hterm)
    have hterm' := binary_div' (binary_mul' hterm hzq)
      (binary_mul' (binary_add' hj (const 1)) hSq)
    exact (binary_add' hj (const 1)).prod (hterm'.prod hacc')
  have hiter := iterateWith hpar hcount hinit hstep
    (bound := fun p => 12 * (encPair encUnary encNat p).length + 30)
    (((PolyBounded.const 12).mul .self).add (.const 30))
    (fun p i hi => by
      have hinv := expNegStep_inv (2 ^ p.1) (min p.2 (2 ^ p.1)) (min_le_right _ _) i
      have hfst : ((expNegStep (2 ^ p.1, min p.2 (2 ^ p.1)))^[i] (0, (2 ^ p.1, 0))).1 = i := by
        simpa using expNegStep_fst (2 ^ p.1, min p.2 (2 ^ p.1)) (0, (2 ^ p.1, 0)) i
      dsimp only at hinv
      have ha_le : ((expNegStep (2 ^ p.1, min p.2 (2 ^ p.1)))^[i] (0, (2 ^ p.1, 0))).2.2 ≤
          2 ^ p.1 := by
        split_ifs at hinv <;> omega
      have hl1 := length_encNat_le_of_lt_two_pow (lt_of_le_of_lt hi Nat.lt_two_pow_self)
      have hl2 :=
        length_encNat_le_of_lt_two_pow (hinv.1.trans_lt (Nat.pow_lt_pow_succ one_lt_two))
      have hl3 :=
        length_encNat_le_of_lt_two_pow (ha_le.trans_lt (Nat.pow_lt_pow_succ one_lt_two))
      simp only [length_encPair, encUnary_apply, List.length_replicate, hfst] at hl1 hl2 hl3 ⊢
      omega)
  exact hiter.snd'.snd'

/-- `expNegPow` is computable in polynomial time. -/
theorem computableInPolyTime_expNegPow :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => expNegPow p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encNat) encUnary) encNat := by
  have hS : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => 2 ^ p.1.1)
      (encPair (encPair encUnary encNat) encUnary) encNat :=
    binary_two_pow.comp (fst (encPair encUnary encNat) encUnary).fst'
  have hb : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => expNegSeries p.1.1 p.1.2)
      (encPair (encPair encUnary encNat) encUnary) encNat :=
    computableInPolyTime_expNegSeries.comp (fst (encPair encUnary encNat) encUnary)
  have hpar := hS.prod hb
  have hcount : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.2)
      (encPair (encPair encUnary encNat) encUnary) encUnary :=
    snd (encPair encUnary encNat) encUnary
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × ℕ => (q.2 * q.1.2) / q.1.1)
      (encPair (encPair encNat encNat) encNat) encNat := by
    have hpar_q := fst (encPair encNat encNat) encNat
    have hp_q := snd (encPair encNat encNat) encNat
    exact binary_div' (binary_mul' hp_q hpar_q.snd') hpar_q.fst'
  exact iterateWith (step := fun (par : ℕ × ℕ) (x : ℕ) => (x * par.2) / par.1) hpar hcount hS hstep
    (bound := fun p => (encPair (encPair encUnary encNat) encUnary p).length + 2)
    (PolyBounded.add .self (.const 2))
    (fun p i _ => by
      have hle : (fun x => (x * expNegSeries p.1.1 p.1.2) / 2 ^ p.1.1)^[i] (2 ^ p.1.1) ≤
          2 ^ p.1.1 :=
        expNegPow_le p.1.1 p.1.2 i
      have hlt : (fun x => (x * expNegSeries p.1.1 p.1.2) / 2 ^ p.1.1)^[i] (2 ^ p.1.1) <
          2 ^ (p.1.1 + 1) :=
        lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by omega) (by omega))
      have hl := length_encNat_le_of_lt_two_pow hlt
      simp only [length_encPair, encUnary_apply, List.length_replicate] at hl ⊢
      omega)


/-- `exp(-·)` is `1`-Lipschitz on `[0, ∞)`. -/
theorem abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a]
    exact this hb ha (le_of_not_ge hab)
  have hge : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr hge), abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
  have h1 : Real.exp (-a) - Real.exp (-b) = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2; ring
  have h2 : 1 - Real.exp (-(b - a)) ≤ b - a := by
    linarith [Real.add_one_le_exp (-(b - a))]
  have h3 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [h1]
  have hnn : 0 ≤ 1 - Real.exp (-(b - a)) := by
    have : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  exact (mul_le_of_le_one_left hnn h3).trans h2

/-- A fixed-point numerator `zFp ≤ 2 ^ qBits` represents a real ratio in `[0, 1]`. -/
private theorem fixedPoint_ratio_mem_unit (qBits zFp : ℕ) (hz : zFp ≤ 2 ^ qBits) :
    0 ≤ (zFp : ℝ) / ((2 ^ qBits : ℕ) : ℝ) ∧ (zFp : ℝ) / ((2 ^ qBits : ℕ) : ℝ) ≤ 1 :=
  ⟨by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast hz)⟩

private theorem expNegStep_term_error (qBits zFp : ℕ) (hz : zFp ≤ 2 ^ qBits) (j : ℕ) :
    let S : ℕ := 2 ^ qBits
    let z : ℝ := (zFp : ℝ) / (S : ℝ)
    let term := ((expNegStep (S, zFp))^[j] (0, (S, 0))).2.1
    (term : ℝ) ≤ (S : ℝ) * z ^ j / (Nat.factorial j : ℝ) ∧
      (S : ℝ) * z ^ j / (Nat.factorial j : ℝ) - (term : ℝ) ≤ if j = 0 then 0 else 2 := by
  obtain ⟨hz0, hz1⟩ := fixedPoint_ratio_mem_unit qBits zFp hz
  set S : ℕ := 2 ^ qBits
  set z : ℝ := (zFp : ℝ) / (S : ℝ)
  have hSpos : (0 : ℝ) < (S : ℝ) := by positivity
  induction j with
  | zero =>
    simp [S]
  | succ j ih =>
    dsimp only
    rw [Function.iterate_succ_apply']
    dsimp only [expNegStep]
    set st := (expNegStep (S, zFp))^[j] (0, (S, 0))
    have hfst : st.1 = j := by simpa [st] using expNegStep_fst (S, zFp) (0, (S, 0)) j
    rw [hfst]
    set term := st.2.1
    have h := cast_div_bounds (term * zFp) ((j + 1) * S)
    have hterm_eq : ((term * zFp : ℕ) : ℝ) / (((j + 1) * S : ℕ) : ℝ) =
        (term : ℝ) * z / (j + 1 : ℝ) := by
      simp only [z]
      push_cast
      field_simp [hSpos.ne']
    rw [hterm_eq] at h
    have hpow_step : (S : ℝ) * z ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) =
        ((S : ℝ) * z ^ j / (Nat.factorial j : ℝ)) * z / (j + 1 : ℝ) := by
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp [Nat.factorial_ne_zero j]
    rw [hpow_step, ite_eq_right (Nat.succ_ne_zero j)]
    refine ⟨h.1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right ih.1 hz0) (by positivity)), ?_⟩
    have herr_mul : ((S : ℝ) * z ^ j / (Nat.factorial j : ℝ) - (term : ℝ)) *
        (z / (j + 1 : ℝ)) ≤ 1 := by
      calc _ ≤ (if j = 0 then 0 else 2) * (1 / (j + 1 : ℝ)) :=
            mul_le_mul ih.2 (div_le_div_of_nonneg_right hz1 (by positivity))
              (div_nonneg hz0 (by positivity)) (by split_ifs <;> norm_num)
        _ ≤ 1 := by
          split_ifs with hj
          · norm_num
          · have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
            rw [mul_one_div, div_le_one (by positivity)]
            linarith
    have hsplit :
        ((S : ℝ) * z ^ j / (Nat.factorial j : ℝ)) * z / (j + 1 : ℝ) -
            (((term * zFp) / ((j + 1) * S) : ℕ) : ℝ) =
          ((S : ℝ) * z ^ j / (Nat.factorial j : ℝ) - (term : ℝ)) * (z / (j + 1 : ℝ)) +
            ((term : ℝ) * z / (j + 1 : ℝ) - (((term * zFp) / ((j + 1) * S) : ℕ) : ℝ)) := by
      ring
    linarith [h.2]

/-- Fixed-point error bound for `expNegSeries`. -/
theorem abs_expNegSeries_div_sub_exp_le (qBits zFp : ℕ) (hz : zFp ≤ 2 ^ qBits) :
    |(expNegSeries qBits zFp : ℝ) / (2 : ℝ) ^ qBits -
        Real.exp (-((zFp : ℝ) / (2 : ℝ) ^ qBits))| ≤
      (4 * ((qBits : ℝ) + 2) + 1) / (2 : ℝ) ^ qBits := by
  obtain ⟨hz0, hz1⟩ := fixedPoint_ratio_mem_unit qBits zFp hz
  set S : ℕ := 2 ^ qBits
  set z : ℝ := (zFp : ℝ) / (S : ℝ)
  have hSpos : (0 : ℝ) < (S : ℝ) := by positivity
  have hgen : ∀ n : ℕ,
      |(((expNegStep (S, zFp))^[n] (0, (S, 0))).2.2 : ℝ) -
          (S : ℝ) * ∑ k ∈ Finset.range n, (-z) ^ k / (Nat.factorial k : ℝ)| ≤
        2 * (n : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hinv := expNegStep_inv S zFp hz n
      have ht := expNegStep_term_error qBits zFp hz n
      set st := (expNegStep (S, zFp))^[n] (0, (S, 0))
      have hfst : st.1 = n := by simpa [st] using expNegStep_fst (S, zFp) (0, (S, 0)) n
      dsimp only at hinv ht
      have ht_err : |(st.2.1 : ℝ) - (S : ℝ) * (z ^ n / (Nat.factorial n : ℝ))| ≤ 2 := by
        have h2 : (S : ℝ) * z ^ n / (Nat.factorial n : ℝ) - (st.2.1 : ℝ) ≤ 2 := by
          have := ht.2
          split_ifs at this <;> linarith
        rw [← mul_div_assoc, abs_le]
        constructor <;> linarith [ht.1]
      have hle : n % 2 = 1 → st.2.1 ≤ st.2.2 := fun h => by
        rw [ite_eq_right (by omega)] at hinv; exact hinv.2.1
      rw [Function.iterate_succ_apply', Finset.sum_range_succ]
      dsimp only [expNegStep]
      rw [hfst]
      exact (abs_altStep_sub_le (by rw [neg_pow]; ring) hle ih ht_err).trans_eq
        (by push_cast; ring)
  have hsum_err :
      |(expNegSeries qBits zFp : ℝ) / (S : ℝ) -
          ∑ k ∈ Finset.range (2 * (qBits + 2)), (-z) ^ k / (Nat.factorial k : ℝ)| ≤
        4 * ((qBits : ℝ) + 2) / (S : ℝ) := by
    have hg := hgen (2 * (qBits + 2))
    have hEq : expNegSeries qBits zFp =
        ((expNegStep (S, zFp))^[2 * (qBits + 2)] (0, (S, 0))).2.2 := by
      dsimp only [expNegSeries]
      rw [min_eq_left hz]
    rw [hEq, ← mul_div_cancel_left₀ (∑ k ∈ Finset.range (2 * (qBits + 2)), _) hSpos.ne',
      ← sub_div, abs_div, abs_of_pos hSpos]
    refine div_le_div_of_nonneg_right ?_ hSpos.le
    calc
      _ ≤ 2 * ((2 * (qBits + 2) : ℕ) : ℝ) := hg
      _ = 4 * ((qBits : ℝ) + 2) := by push_cast; ring
  have htail :
      |Real.exp (-z) - ∑ k ∈ Finset.range (2 * (qBits + 2)), (-z) ^ k / (Nat.factorial k : ℝ)| ≤
        1 / (S : ℝ) := by
    set N : ℕ := 2 * (qBits + 2)
    have hN_pos : 0 < N := by dsimp only [N]; omega
    have h1 := Real.exp_bound (x := -z) (by rwa [abs_neg, abs_of_nonneg hz0]) hN_pos
    have hpow1 : |-z| ^ N ≤ 1 := by
      rw [abs_neg, abs_of_nonneg hz0]
      exact pow_le_one₀ hz0 hz1
    have hfac : 2 * 2 ^ qBits ≤ Nat.factorial N := by
      have h1_fac := Nat.factorial_mul_pow_le_factorial (m := 1) (n := N - 1)
      have hN1 : 1 + (N - 1) = N := by dsimp only [N]; omega
      rw [Nat.factorial_one, one_mul, hN1] at h1_fac
      calc
        2 * 2 ^ qBits = 2 ^ (qBits + 1) := by rw [pow_succ']
        _ ≤ 2 ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by dsimp only [N]; omega)
        _ ≤ Nat.factorial N := h1_fac
    have hfac' : 2 * (S : ℝ) ≤ (Nat.factorial N : ℝ) := by exact_mod_cast hfac
    have hratio :
        ((N.succ : ℝ) / ((Nat.factorial N : ℝ) * (N : ℝ))) ≤ 2 / (Nat.factorial N : ℝ) := by
      have hN_r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hNs : (N.succ : ℝ) ≤ 2 * (N : ℝ) := by push_cast; linarith
      nlinarith [show (0 : ℝ) < (Nat.factorial N : ℝ) by positivity]
    calc
      |Real.exp (-z) - ∑ k ∈ Finset.range N, (-z) ^ k / (Nat.factorial k : ℝ)|
          ≤ |-z| ^ N * ((N.succ : ℝ) / ((Nat.factorial N : ℝ) * (N : ℝ))) := h1
      _ ≤ 1 * (2 / (Nat.factorial N : ℝ)) :=
          mul_le_mul hpow1 hratio (by positivity) zero_le_one
      _ = 2 / (Nat.factorial N : ℝ) := one_mul _
      _ ≤ 2 / (2 * (S : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hfac'
      _ = 1 / (S : ℝ) := by field_simp [hSpos.ne']
  rw [abs_sub_comm] at htail
  have hadd := (abs_sub_le _ _ _).trans (add_le_add hsum_err htail)
  rw [← add_div] at hadd
  have hS_cast : (S : ℝ) = (2 : ℝ) ^ qBits := by dsimp only [S]; push_cast; rfl
  simpa only [z, hS_cast] using hadd

/-- Fixed-point error bound for range-reduced `expNegPow`. -/
theorem abs_expNegPow_div_sub_exp_le (qBits zFp K : ℕ) (hz : zFp ≤ 2 ^ qBits)
    {zReal : ℝ} (hzReal : 0 ≤ zReal)
    (hzErr : |zReal - (zFp : ℝ) / (2 : ℝ) ^ qBits| ≤ 2 / (2 : ℝ) ^ qBits) :
    |(expNegPow qBits zFp K : ℝ) / (2 : ℝ) ^ qBits - Real.exp (-(K : ℝ) * zReal)| ≤
      (K : ℝ) * (4 * ((qBits : ℝ) + 2) + 4) / (2 : ℝ) ^ qBits := by
  set S : ℕ := 2 ^ qBits
  set b : ℕ := expNegSeries qBits zFp
  have hS_cast : (S : ℝ) = (2 : ℝ) ^ qBits := by dsimp only [S]; push_cast; rfl
  have hSpos : (0 : ℝ) < (S : ℝ) := by positivity
  have hb_le : (b : ℝ) ≤ (S : ℝ) := by exact_mod_cast expNegSeries_le qBits zFp
  have hb_err : |(b : ℝ) / (S : ℝ) - Real.exp (-zReal)| ≤
      (4 * ((qBits : ℝ) + 2) + 3) / (S : ℝ) := by
    have h1 : |(b : ℝ) / (S : ℝ) - Real.exp (-((zFp : ℝ) / (S : ℝ)))| ≤
        (4 * ((qBits : ℝ) + 2) + 1) / (S : ℝ) := by
      simpa only [b, hS_cast] using abs_expNegSeries_div_sub_exp_le qBits zFp hz
    have h2 : |Real.exp (-((zFp : ℝ) / (S : ℝ))) - Real.exp (-zReal)| ≤ 2 / (S : ℝ) := by
      rw [abs_sub_comm]
      exact (abs_exp_neg_sub_exp_neg_le hzReal (by positivity)).trans
        (by simpa only [hS_cast] using hzErr)
    exact ((abs_sub_le _ _ _).trans (add_le_add h1 h2)).trans_eq (by ring)
  rw [← hS_cast]
  induction K with
  | zero =>
    rw [expNegPow, Function.iterate_zero, id_eq]
    rw [hS_cast]
    simp
  | succ K ih =>
    unfold expNegPow at ih ⊢
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    set p : ℕ := (fun x => (x * b) / S)^[K] S
    have hp_le : (p : ℝ) ≤ (S : ℝ) := by exact_mod_cast expNegPow_le qBits zFp K
    have hdiv_err :
        |(((p * b) / S : ℕ) : ℝ) / (S : ℝ) - ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ))| ≤
        1 / (S : ℝ) := by
      have h := cast_div_bounds (p * b) S
      have h1 : |(((p * b) / S : ℕ) : ℝ) - ((p * b : ℕ) : ℝ) / (S : ℝ)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [h.1, h.2]
      have hrew : ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ)) =
          (((p * b : ℕ) : ℝ) / (S : ℝ)) / (S : ℝ) := by
        push_cast; ring
      rw [hrew, ← sub_div, abs_div, abs_of_pos hSpos]
      exact div_le_div_of_nonneg_right h1 hSpos.le
    have hexp_step : Real.exp (-((K + 1 : ℕ) : ℝ) * zReal) =
        Real.exp (-(K : ℝ) * zReal) * Real.exp (-zReal) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have hsplit :
        (((p * b) / S : ℕ) : ℝ) / (S : ℝ) - Real.exp (-((K + 1 : ℕ) : ℝ) * zReal) =
          ((((p * b) / S : ℕ) : ℝ) / (S : ℝ) - ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ))) +
          ((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ) - Real.exp (-zReal)) +
          ((p : ℝ) / (S : ℝ) - Real.exp (-(K : ℝ) * zReal)) * Real.exp (-zReal) := by
      rw [hexp_step]; ring
    change |(((p * b) / S : ℕ) : ℝ) / (S : ℝ) - Real.exp (-((K + 1 : ℕ) : ℝ) * zReal)| ≤ _
    rw [hsplit]
    have hp1 : (p : ℝ) / (S : ℝ) ≤ 1 := (div_le_one hSpos).mpr hp_le
    have hexp1 : Real.exp (-zReal) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hm1 : |((p : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ) - Real.exp (-zReal))| ≤
        (4 * ((qBits : ℝ) + 2) + 3) / (S : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact (mul_le_of_le_one_left (abs_nonneg _) hp1).trans hb_err
    have hm2 : |((p : ℝ) / (S : ℝ) - Real.exp (-(K : ℝ) * zReal)) * Real.exp (-zReal)| ≤
        (K : ℝ) * (4 * ((qBits : ℝ) + 2) + 4) / (S : ℝ) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_of_le_one_right (abs_nonneg _) hexp1).trans ih
    calc
      _ ≤ 1 / (S : ℝ) + (4 * ((qBits : ℝ) + 2) + 3) / (S : ℝ) +
          (K : ℝ) * (4 * ((qBits : ℝ) + 2) + 4) / (S : ℝ) :=
        (abs_add_three _ _ _).trans (add_le_add_three hdiv_err hm1 hm2)
      _ = ((K + 1 : ℕ) : ℝ) * (4 * ((qBits : ℝ) + 2) + 4) / (S : ℝ) := by push_cast; ring


end Cslib.FixedPointExp
