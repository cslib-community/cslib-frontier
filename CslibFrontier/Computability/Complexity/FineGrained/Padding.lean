/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.PowerTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Foundations.Data.Nat.LogTwoRpow

/-!
# Exponential time by padding

A decision procedure that runs in polynomial time on padded inputs `(a, 2 ^ ν a)`, with the
padding in unary, gives a decision procedure for the original instances within time
`2 ^ (δ μ a)` times a polynomial, for an exponent `ν ≤ μ` computable in unary in polynomial time
(`Cslib.Complexity.DecidableInExpTime.of_computableInPolyTime_pad`). The machine writes the padding
and runs the polynomial-time procedure
(`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_pad`). The constant `δ` comes from
the degree of the polynomial bound, and is not explicit.

This is how a dynamic program over `2 ^ k` states, polynomial-time in the number of its states, is
stated as an exponential-time or fpt algorithm in the parameter `k` on multi-tape machines.
A padding length can also majorize a sublinear power exponential times a polynomial while
remaining computable in a sublinear power exponential time bound. This lets a randomized
algorithm allocate a common seed length given a bound on the seed lengths of all its calls.

## Main results

* `Cslib.Complexity.DecidableInExpTime.of_computableInPolyTime_pad`: polynomial time on inputs
  padded by `2 ^ ν a` gives `DecidableInExpTime` in any `μ ≥ ν`.
* `Cslib.Complexity.exists_computableInPowerExpTime_unary_majorant`: compute a unary length
  that dominates a power-exponential bound at a slightly larger power below one.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Exponential time by padding.** If `Ψ` is polynomial-time on pairs `(a, N)` with `N` in unary,
and `A` is decided by `Ψ` on the padded inputs `(a, 2 ^ ν a)`, for a unary exponent `ν ≤ μ`
computable in polynomial time, then `A` is decidable within time `2 ^ (δ μ a)` times a polynomial,
for some `δ`. -/
theorem DecidableInExpTime.of_computableInPolyTime_pad {α : Type} {enc : α ↪ List Bool}
    {A : Set α} {μ ν : α → ℕ} {Ψ : α × ℕ → Bool}
    (hΨ : ComputableInPolyTime Ψ (encPair enc encUnary) encBool)
    (hν : ComputableInPolyTime ν enc encUnary) (hνμ : ∀ a, ν a ≤ μ a)
    (hA : ∀ a, a ∈ A ↔ Ψ (a, 2 ^ ν a) = true) :
    ∃ δ : ℝ, DecidableInExpTime A enc μ δ := by
  obtain ⟨C, D, h⟩ := hΨ.exists_computableInO_pad hν
  refine ⟨D, DecidableInExpTime.of_computableInO h hA C D fun a => ?_⟩
  have h2 : (2 : ℝ) ^ (D * ν a) ≤ (2 : ℝ) ^ ((D : ℝ) * (μ a : ℝ)) := by
    rw [show (D : ℝ) * (μ a : ℝ) = ((D * μ a : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left D (hνμ a))
  push_cast
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)

/-- Given a polynomial-time unary parameter, a sublinear power-exponential bound times an
input-length polynomial has a unary majorant computable in time of the same form at some power
strictly between the original power and one. The majorant uses integer powers of fixed bases
and the ceiling logarithm of the parameter. -/
theorem exists_computableInPowerExpTime_unary_majorant {α : Type} {enc : α ↪ List Bool}
    {μ : α → ℕ} (hμ : ComputableInPolyTime μ enc encUnary) {p : ℝ} (hp : p < 1)
    (A e : ℕ) :
    ∃ (q : ℝ) (pad : α → ℕ), p < q ∧ 0 < q ∧ q < 1 ∧
      ComputableInPowerExpTime pad enc encUnary μ q ∧
      ∀ a, (2 : ℝ) ^ (A * (μ a + 1 : ℝ) ^ p) * ((enc a).length + 1) ^ e ≤ pad a := by
  obtain ⟨d, hd⟩ := exists_nat_gt (max 0 (p / (1 - p)))
  have hd₀ : (0 : ℝ) < d := (le_max_left _ _).trans_lt hd
  have hd' : 0 < d := Nat.cast_pos.mp hd₀
  let base : ℕ := 2 ^ (d + 1)
  let step : ℕ := 2 ^ d
  let q : ℝ := d / (d + 1)
  have hbase : 1 < base := Nat.one_lt_pow (by omega) (by decide)
  have hstep : 1 ≤ step := Nat.one_le_two_pow
  have hlog : Real.logb (base : ℝ) (step : ℝ) = q := by
    simp only [base, step, q, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      Real.logb, Real.log_pow]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  have hpq : p < q := by
    have h := (div_lt_iff₀ (sub_pos.mpr hp)).mp ((le_max_right _ _).trans_lt hd)
    exact (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  let exponent (a : α) := A * step * step ^ Nat.clog base (μ a + 1)
  let pad (a : α) := 2 ^ exponent a * ((enc a).length + 1) ^ e
  have hq₀ : 0 < q := div_pos hd₀ (by positivity)
  have hq₁ : q < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  refine ⟨q, pad, hpq, hq₀, hq₁, ?_, ?_⟩
  · have hexp : ComputableInPolyTime exponent enc encUnary := by
      open ComputableInPolyTime in
      exact unary_mul' (const (A * step))
        (unary_pow_clog_const (unary_add' hμ (const 1)) step base)
    have hpost : ComputableInPolyTime
        (fun a : α × ℕ => a.2 * ((enc a.1).length + 1) ^ e)
        (encPair enc encUnary) encUnary := by
      open ComputableInPolyTime in
      exact unary_mul' (snd _ _)
        ((unary_pow e).comp (unary_add' ((encoding_length enc).comp (fst _ _)) (const 1)))
    obtain ⟨C, D, hpad⟩ := hpost.exists_computableInO_pad hexp
    refine ⟨D * (A * step * step), D,
      (ComputableInTimeO.of_computableInO hpad (T := fun a =>
        C * ((2 : ℝ) ^ (((D * (A * step * step) : ℕ) : ℝ) * (μ a + 1 : ℝ) ^ q) *
          ((enc a).length + 1) ^ D)) ?_).mono C
        (fun _ => le_add_of_nonneg_right C.cast_nonneg) (fun _ => by positivity)⟩
    intro a
    have hup := Nat.pow_clog_le_mul_rpow_logb hbase hstep (Nat.succ_ne_zero (μ a))
    rw [hlog, Nat.cast_succ] at hup
    have hexpUp : (exponent a : ℝ) ≤ ((A * step * step : ℕ) : ℝ) * (μ a + 1 : ℝ) ^ q := by
      simp only [exponent, Nat.cast_mul]
      rw [mul_assoc ((A : ℝ) * step)]
      exact mul_le_mul_of_nonneg_left hup (by positivity)
    have hrate : (2 : ℝ) ^ (D * exponent a) ≤
        (2 : ℝ) ^ (((D * (A * step * step) : ℕ) : ℝ) * (μ a + 1 : ℝ) ^ q) := by
      rw [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_mul D, mul_assoc]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two
        (mul_le_mul_of_nonneg_left hexpUp (Nat.cast_nonneg D))
    have hpoly : 0 ≤ ((enc a).length + 1 : ℝ) ^ D := by positivity
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      mul_assoc] using
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrate hpoly) (Nat.cast_nonneg C)
  · intro a
    have hlo := Nat.rpow_logb_le_mul_pow_log hbase hstep (μ a + 1)
    rw [hlog, Nat.cast_succ] at hlo
    have hpow : (step : ℝ) ^ Nat.log base (μ a + 1) ≤
        (step : ℝ) ^ Nat.clog base (μ a + 1) :=
      pow_le_pow_right₀ (by exact_mod_cast hstep) (Nat.log_le_clog _ _)
    have hx : 1 ≤ (μ a + 1 : ℝ) := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have helow : (A : ℝ) * (μ a + 1 : ℝ) ^ p ≤ exponent a := by
      simp only [exponent, Nat.cast_mul, Nat.cast_pow, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le hx hpq.le).trans
        (hlo.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg step)))) (Nat.cast_nonneg A)
    simp only [pad, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    rw [← Real.rpow_natCast (2 : ℝ) (exponent a)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two helow)
      (by positivity)

end Cslib.Complexity
