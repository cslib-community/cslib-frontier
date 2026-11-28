/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations

/-!
# Strict best approximation by continued-fraction convergents

Convergents after the zeroth are strict best approximations among distinct rational numbers
with no larger positive denominator. This is the corrected form of [Arora and Barak][AroraBarak07],
Theorem 20.26 (web draft 2007-01-08, printed p. 432 / PDF p. 448): the printed inequality is
reversed, and distinctness and a positive convergent index are necessary.

The proof uses Mathlib's exact tail formula and determinant identity. If consecutive convergents
are `p/q` and `a/b`, then `x = (p + t*a)/(q + t*b)` with `t > 1` and `|p*b - q*a| = 1`.
For a competitor `c/d`, the integral coordinates `z = c*b - d*a` and `w = d*p - c*q` satisfy
`d*(p*b - q*a) = z*q + w*b`. An error no greater than that of `a/b` forces `z` and `w`
to have the same strict sign, contradicting `0 < d ≤ b`. Termination is handled separately by
Mathlib's exactness theorem. Thus rational inputs, including integers, require no exclusion.

## Main results

* `GenContFract.abs_sub_convs_lt`: the strict comparison using the continuant denominator.
* `Real.abs_sub_convergent_lt`: the corrected source statement using reduced denominators.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, draft of
  2007-01-08][AroraBarak07]
-/

public section

open GenContFract
open GenContFract (of compExactValue)

private theorem best_of_tail {p q a b c d : ℤ} {t x : ℝ}
    (hq : 0 < q) (hb : 0 < b) (hd : 0 < d) (hdb : d ≤ b)
    (hdet : |p * b - q * a| = 1) (ht : 1 < t)
    (hx : x = (p + t * a) / (q + t * b))
    (hne : (c : ℝ) / d ≠ (a : ℝ) / b) :
    |x - (a : ℝ) / b| < |x - (c : ℝ) / d| := by
  by_contra! hle
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdb' : (d : ℝ) ≤ b := by exact_mod_cast hdb
  -- Integral coordinates in the unimodular basis of consecutive convergents.
  let z : ℤ := c * b - d * a
  let w : ℤ := d * p - c * q
  have hD : 0 < (q : ℝ) + t * b := by positivity
  have hA : x - (a : ℝ) / b =
      ((p * b - q * a : ℤ) : ℝ) / (b * ((q : ℝ) + t * b)) := by
    rw [hx]; push_cast; field_simp; ring
  have hC : x - (c : ℝ) / d =
      - (t * z - w) / (d * ((q : ℝ) + t * b)) := by
    rw [hx]; dsimp [z, w]; push_cast; field_simp; ring
  have hz : z ≠ 0 := fun hz => hne <| (div_eq_div_iff hd'.ne' hb'.ne').mpr <| by
    exact_mod_cast (sub_eq_zero.mp hz).trans (mul_comm d a)
  have hden : (d : ℝ) * ((p * b - q * a : ℤ) : ℝ) = z * q + w * b := by
    dsimp [z, w]; push_cast; ring
  have hs : |((p * b - q * a : ℤ) : ℝ)| = 1 := by exact_mod_cast hdet
  rw [hA, hC, abs_div, abs_div, abs_neg, hs,
    abs_of_pos (mul_pos hb' hD), abs_of_pos (mul_pos hd' hD)] at hle
  have hsmall : |t * (z : ℝ) - w| ≤ 1 := by
    have hh := (div_le_div_iff₀ (mul_pos hd' hD) (mul_pos hb' hD)).mp hle
    have : |t * (z : ℝ) - w| * b ≤ d := by nlinarith
    nlinarith
  -- A competing error this small forces both coordinates to have the same sign.
  -- Their denominator would then have magnitude at least `q + b > b`.
  have hzsign : z ≤ -1 ∨ 1 ≤ z := by omega
  have hlarge : (b : ℝ) < |(z : ℝ) * q + w * b| := by
    rcases hzsign with hz | hz
    · have hz' : (z : ℝ) ≤ -1 := by exact_mod_cast hz
      have hw : w < 0 := by exact_mod_cast (show (w : ℝ) < 0 by nlinarith [(abs_le.mp hsmall).1])
      have hw' : (w : ℝ) ≤ -1 := by exact_mod_cast (show w ≤ -1 by omega)
      have hsum : (z : ℝ) * q + w * b < -(b : ℝ) := by nlinarith
      rw [abs_of_neg (by linarith)]
      linarith
    · have hz' : (1 : ℝ) ≤ z := by exact_mod_cast hz
      have hw : 0 < w := by exact_mod_cast (show (0 : ℝ) < w by nlinarith [(abs_le.mp hsmall).2])
      have hw' : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
      have hsum : (b : ℝ) < (z : ℝ) * q + w * b := by nlinarith
      exact hsum.trans_le (le_abs_self _)
  rw [← hden, abs_mul, abs_of_pos hd', hs, mul_one] at hlarge
  linarith

private theorem contsAux_int (x : ℝ) (n : ℕ) :
    ∃ a b : ℤ, (of x).contsAux n = ⟨a, b⟩ := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨1, 0, by simp⟩
  | one => exact ⟨⌊x⌋, 1, by simp⟩
  | more n ih ih' =>
    obtain ⟨a, b, hab⟩ := ih
    obtain ⟨a', b', hab'⟩ := ih'
    cases hs : (of x).s.get? n with
    | none => exact ⟨a', b', by simpa only [contsAux, hs] using hab'⟩
    | some gp =>
      obtain ⟨ha, k, hk⟩ := of_partNum_eq_one_and_exists_int_partDen_eq hs
      refine ⟨k * a' + a, k * b' + b, ?_⟩
      rw [contsAux_recurrence hs hab hab', ha, hk]
      simp

private theorem den_pos (x : ℝ) (n : ℕ) : 0 < (of x).dens n :=
  zero_lt_one.trans_le <| zeroth_den_eq_one.symm.trans_le <|
    monotone_nat_of_le_succ (f := (of x).dens) (fun _ => of_den_mono) n.zero_le

/-- Every convergent after the zeroth is strictly closer than any distinct fraction with a
positive denominator at most its continuant denominator. No irrationality assumption is needed;
a terminated convergent equals `x`. -/
theorem GenContFract.abs_sub_convs_lt (x : ℝ) {n : ℕ} (hn : 1 ≤ n) {c d : ℤ}
    (hd : 0 < d) (hdb : (d : ℝ) ≤ (of x).dens n)
    (hne : (c : ℝ) / d ≠ (of x).convs n) :
    |x - (of x).convs n| < |x - (c : ℝ) / d| := by
  by_cases hterm : (of x).TerminatedAt n
  · rw [← of_correctness_of_terminatedAt hterm, sub_self, abs_zero]
    exact abs_pos.mpr (sub_ne_zero.mpr ((of_correctness_of_terminatedAt hterm).trans_ne hne.symm))
  obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp hterm
  obtain ⟨f', hf', -⟩ := IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some hgp
  obtain ⟨f, hf, hf0, -⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hf'
  obtain ⟨p, q, hpq⟩ := contsAux_int x n
  obtain ⟨a, b, hab⟩ := contsAux_int x (n + 1)
  have hb : (of x).dens n = (b : ℝ) := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, hab]
  have hconv : (of x).convs n = (a : ℝ) / b := by
    rw [conv_eq_conts_a_div_conts_b, nth_cont_eq_succ_nth_contAux, hab]
  have hbp : 0 < b := by exact_mod_cast (hb ▸ den_pos x n)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hqp : 0 < q := by
    have h : 0 < ((of x).contsAux (m + 1)).b := den_pos x m
    simpa [hpq] using h
  have hdet := (SimpContFract.of x).determinant
    (mt (terminated_stable (Nat.le_succ m)) hterm)
  change ((of x).contsAux (m + 1)).a * ((of x).contsAux (m + 2)).b -
    ((of x).contsAux (m + 1)).b * ((of x).contsAux (m + 2)).a = _ at hdet
  rw [hpq, hab] at hdet
  have hdeta : |p * b - q * a| = 1 := by
    dsimp only at hdet; exact_mod_cast (congrArg abs hdet).trans (abs_neg_one_pow _)
  have hfr : 0 < f.fr := lt_of_le_of_ne (IntFractPair.nth_stream_fr_nonneg hf) hf0.symm
  have ht : 1 < f.fr⁻¹ := (one_lt_inv₀ hfr).mpr (IntFractPair.nth_stream_fr_lt_one hf)
  have hx := compExactValue_correctness_of_stream_eq_some hf
  rw [hpq, hab] at hx
  simp only [compExactValue, hf0, ↓reduceIte, nextConts, nextNum, nextDen, one_mul] at hx
  rw [hconv] at hne ⊢
  exact best_of_tail hqp hbp hd (by exact_mod_cast hb ▸ hdb) hdeta ht
    (by convert hx using 1; ring_nf) hne

/-- Corrected best approximation theorem ([Arora and Barak][AroraBarak07], Theorem 20.26,
web draft 2007-01-08, printed p. 432 / PDF p. 448).

For every real `x` and `n ≥ 1`, its `n`th convergent `a/b` is strictly closer to `x` than any
distinct `c/d` with `0 < d ≤ b`, where `b` is the reduced positive denominator. The draft reverses
the inequality and omits both distinctness and `n ≥ 1`. For `x = 7/10`, the zeroth convergent is
`0/1` and `1/1` is closer.

Rational inputs are included: before termination this is the same strict inequality; at and
after termination the convergent equals `x`, so its error is zero. In particular, integer inputs
have that value at every index. Mathlib extends finite expansions by repeating their last
convergent; no hypothetical further partial quotients or irrationality assumptions are used. -/
theorem Real.abs_sub_convergent_lt (x : ℝ) {n : ℕ} (hn : 1 ≤ n) {c d : ℤ}
    (hd : 0 < d) (hdb : d ≤ (x.convergent n).den)
    (hne : (c : ℝ) / d ≠ (x.convergent n : ℝ)) :
    |x - (x.convergent n : ℝ)| < |x - (c : ℝ) / d| := by
  obtain ⟨a, b, hab⟩ := contsAux_int x (n + 1)
  have hb : (of x).dens n = (b : ℝ) := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, hab]
  have hbpos : 0 < b := by exact_mod_cast (hb ▸ den_pos x n)
  have hconv : x.convergent n = (a : ℚ) / b := by
    apply Rat.cast_injective (α := ℝ)
    rw [← Real.convs_eq_convergent, conv_eq_conts_a_div_conts_b,
      nth_cont_eq_succ_nth_contAux, hab]
    push_cast
    rfl
  have hden : ((x.convergent n).den : ℤ) ≤ b := by
    have hdvd := Rat.den_dvd a b
    rw [Rat.divInt_eq_div, ← hconv] at hdvd
    exact Int.le_of_dvd hbpos hdvd
  rw [← Real.convs_eq_convergent] at hne ⊢
  exact GenContFract.abs_sub_convs_lt x hn hd (hb ▸ (by exact_mod_cast hdb.trans hden)) hne
