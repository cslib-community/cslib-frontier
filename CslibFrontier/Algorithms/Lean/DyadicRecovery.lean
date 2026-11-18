/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Rat.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Foundations.Data.Rat.Approximation
import CslibFrontier.Foundations.Data.Rat.Reconstruction
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Continued-fraction recovery from dyadic prefixes

A step towards [Arora and Barak][AroraBarak07], web draft 2007-01-08, Chapter 20, Exercise §11
(printed p. 432, PDF p. 448). Under the terminating-zero convention, the first
`2 * Nat.clog 2 N` fractional bits specify a half-open dyadic cell. For numbers at least one,
the cell index also includes the integer part. The decoder tests the included left endpoint
directly. Every interior point with denominator at most `N` satisfies Legendre's strict bound
at the midpoint, even when the bound at the left endpoint fails.

Write `t = (2 * k + 1).size + (2 * M).size + 1` for the Euclidean step budget, where
`M = 2 ^ (2 * Nat.clog 2 N)`. The search tests at most `t + 2` candidates, with
`t + 2 ≤ k.size + 2 * N.size + 6`. Each convergent at index `i` takes `i + 1` quotients,
at most `i` remainders, and `i` rational updates. Across all convergents the search uses at most
`(t + 1) * (t + 2) / 2` quotients. Each intermediate reduced numerator and denominator
in the recurrence has at most `(i + 1) * ((max (2 * k + 1) (2 * M)).size + 3)` bits.
The encoded machine certificate remains open.

## Main definitions

* `Rat.recoverDyadic`: the decoder returning an optional reduced rational.

## Main results

* `Rat.recoverDyadic_mem_cell`: every returned rational satisfies the cell and denominator tests.
* `Rat.recoverDyadic_eq_some`: recovery of any promised rational in the cell.
-/

public section

namespace Rat

open Turing.MultiTapeTM.BinaryGcd

private def euclidConvergent : ℕ → ℕ × ℕ → ℚ
  | 0, p => (p.1 / p.2 : ℕ)
  | i + 1, p => (p.1 / p.2 : ℕ) + (euclidConvergent i (gcdStep p))⁻¹

private theorem euclidConvergent_zero_den (i a : ℕ) : euclidConvergent i (a, 0) = 0 := by
  induction i with
  | zero => simp [euclidConvergent]
  | succ i ih => simp [euclidConvergent, gcdStep, ih]

private theorem floor_nat_div_nat (a b : ℕ) : ⌊(a : ℝ) / b⌋ = (a / b : ℕ) := by
  rw [← Rat.cast_natCast (α := ℝ) a, ← Rat.cast_natCast (α := ℝ) b, ← Rat.cast_div,
    Rat.floor_cast, Rat.floor_natCast_div_natCast, Int.ofNat_ediv_ofNat]

private theorem euclidConvergent_eq (i a b : ℕ) :
    euclidConvergent i (a, b) = Real.convergent ((a : ℝ) / b) i := by
  induction i generalizing a b with
  | zero =>
    simp only [euclidConvergent, Real.convergent_zero]
    rw [floor_nat_div_nat, Int.cast_natCast]
  | succ i ih =>
    by_cases hb : b = 0
    · subst b
      simp [euclidConvergent_zero_den]
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hfract : Int.fract ((a : ℝ) / b) = (a % b : ℕ) / (b : ℝ) := by
      rw [Int.fract, floor_nat_div_nat, Int.cast_natCast]
      apply (eq_div_iff hb').2
      rw [sub_mul, div_mul_cancel₀ _ hb']
      have hrem : ((a % b : ℕ) : ℝ) + b * ((a / b : ℕ) : ℝ) = a := by
        exact_mod_cast Nat.mod_add_div a b
      linarith
    simp only [euclidConvergent, gcdStep, hb, ite_false, Real.convergent_succ, floor_nat_div_nat,
      Int.cast_natCast, hfract, inv_div, ih]

private theorem euclidConvergent_stable (i extra : ℕ) (p : ℕ × ℕ)
    (h : (gcdStep^[i] p).2 = 0) : euclidConvergent (i + extra) p = euclidConvergent i p := by
  induction i generalizing p with
  | zero =>
    obtain ⟨a, b⟩ := p
    change b = 0 at h
    subst b
    simp [euclidConvergent_zero_den]
  | succ i ih =>
    rw [Function.iterate_succ_apply] at h
    rw [show i + 1 + extra = i + extra + 1 by omega, euclidConvergent, euclidConvergent, ih _ h]

private def cellCandidates (M k : ℕ) : List ℚ :=
  let midpoint := (2 * k + 1, 2 * M)
  (k : ℚ) / M :: (List.range (gcdCount midpoint + 1)).map
    (fun i => euclidConvergent i midpoint)

private theorem length_cellCandidates (M k : ℕ) :
    (cellCandidates M k).length = (2 * k + 1).size + (2 * M).size + 3 := by
  simp only [cellCandidates, List.length_cons, List.length_map, List.length_range,
    gcdCount, Nat.size_eq_bits_len]

private theorem length_dyadicCandidates_le (N k : ℕ) :
    (cellCandidates (2 ^ (2 * Nat.clog 2 N)) k).length ≤ k.size + 2 * N.size + 6 := by
  have hk : (2 * k + 1).size ≤ k.size + 1 := by
    apply Nat.size_le.mpr
    rw [pow_succ]
    have := Nat.lt_size_self k
    omega
  have hN : Nat.clog 2 N ≤ N.size :=
    Nat.clog_le_of_le_pow (Nat.lt_size_self N).le
  rw [length_cellCandidates, ← pow_succ', Nat.size_pow]
  omega

private theorem quotient_height_size (p : ℕ × ℕ) :
    ((p.1 / p.2 : ℕ) : ℚ).height.size ≤ (max p.1 p.2).size + 1 := by
  simp only [height_def, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast]
  rcases le_or_gt 1 (p.1 / p.2) with h | h
  · rw [max_eq_left h]
    exact (Nat.size_le_size ((Nat.div_le_self _ _).trans (le_max_left _ _))).trans
      (Nat.le_add_right _ _)
  · rw [max_eq_right h.le, Nat.size_one]
    omega

private theorem euclidConvergent_height_size (i : ℕ) (p : ℕ × ℕ) :
    (euclidConvergent i p).height.size ≤ (i + 1) * ((max p.1 p.2).size + 3) := by
  induction i generalizing p with
  | zero =>
    simp only [euclidConvergent, Nat.zero_add, one_mul]
    have := quotient_height_size p
    omega
  | succ i ih =>
    have hquot := quotient_height_size p
    let q := euclidConvergent i (gcdStep p)
    have hinv : (q⁻¹).height = q.height := by
      by_cases hq : q = 0
      · simp [hq]
      · exact height_inv hq
    have hq : q.height.size ≤ (i + 1) * ((max p.1 p.2).size + 3) :=
      (ih (gcdStep p)).trans
        (Nat.mul_le_mul_left (i + 1) (Nat.add_le_add_right
          (Nat.size_le_size (max_gcdStep_le p)) 3))
    change (((p.1 / p.2 : ℕ) : ℚ) + q⁻¹).height.size ≤ _
    calc
      _ ≤ (2 * ((p.1 / p.2 : ℕ) : ℚ).height * (q⁻¹).height).size :=
        Nat.size_le_size (height_add_le _ _)
      _ ≤ 2 + ((p.1 / p.2 : ℕ) : ℚ).height.size + q.height.size := by
        rw [hinv]
        simpa only [show (2 : ℕ).size = 2 from rfl] using
          (Nat.size_mul_le _ _).trans (Nat.add_le_add_right (Nat.size_mul_le 2 _) _)
      _ ≤ (i + 1 + 1) * ((max p.1 p.2).size + 3) := by
        rw [Nat.add_mul, one_mul]
        omega

private def inCell (N M k : ℕ) (q : ℚ) : Bool :=
  decide (q.den ≤ N ∧ (k : ℚ) / M ≤ q ∧ q < (k + 1 : ℚ) / M)

/-- Recover a fraction of denominator at most `N` from the dyadic cell indexed by `k`.
For a number in `[0, 1)`, `k` is the natural represented by the first
`2 * Nat.clog 2 N` fractional bits, with leading zeros allowed. At a dyadic boundary, use the
expansion ending in zeros. More generally, add the integer part times the cell scale to `k`.
Return `none` when no fraction of denominator at most `N` lies in the cell. -/
def recoverDyadic (N k : ℕ) : Option ℚ :=
  let M := 2 ^ (2 * Nat.clog 2 N)
  (cellCandidates M k).find? (inCell N M k)

private theorem mem_cellCandidates {N M k : ℕ} {q : ℚ}
    (hM : 0 < M) (hscale : N ^ 2 ≤ M) (hq : q.den ≤ N)
    (hlo : (k : ℚ) / M ≤ q) (hhi : q < (k + 1 : ℚ) / M) :
    q ∈ cellCandidates M k := by
  rcases eq_or_lt_of_le hlo with heq | hlo
  · simp [cellCandidates, heq]
  let a := 2 * k + 1
  let b := 2 * M
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlor : (k : ℝ) / M < q := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).2 hlo
  have hhir : (q : ℝ) < (k + 1 : ℝ) / M := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).2 hhi
  have hsq : (q.den : ℝ) ^ 2 ≤ M := by
    exact_mod_cast (Nat.pow_le_pow_left hq 2).trans hscale
  have hmid : (a : ℝ) / b = (k : ℝ) / M + 1 / (2 * M) := by
    push_cast [a, b]
    field_simp
  have hclose : |(a : ℝ) / b - q| < 1 / (2 * (q.den : ℝ) ^ 2) := by
    refine (show |(a : ℝ) / b - q| < 1 / (2 * (M : ℝ)) from ?_).trans_le ?_
    · rw [hmid, abs_lt]
      have hu : (k + 1 : ℝ) / M = (k : ℝ) / M + 2 * (1 / (2 * (M : ℝ))) := by
        field_simp
      rw [hu] at hhir
      constructor <;> linarith
    · exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  obtain ⟨i, hi⟩ := Real.exists_rat_eq_convergent hclose
  let p : ℕ × ℕ := (a, b)
  let j := min i (gcdCount p)
  have hj : euclidConvergent j p = q := by
    have hei : euclidConvergent i p = q := (euclidConvergent_eq i a b).trans hi.symm
    rcases le_or_gt i (gcdCount p) with h | h
    · simpa only [j, min_eq_left h] using hei
    · change euclidConvergent (min i (gcdCount p)) p = q
      rw [min_eq_right h.le, ← euclidConvergent_stable (gcdCount p)
        (i - gcdCount p) p (snd_iterate_gcdStep_gcdCount p),
        Nat.add_sub_of_le h.le]
      exact hei
  apply List.mem_cons_of_mem
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le (min_le_right ..)), hj⟩

private theorem eq_of_mem_cell {N M k : ℕ} {q r : ℚ} (hscale : N ^ 2 ≤ M)
    (hq : inCell N M k q = true) (hr : inCell N M k r = true) : q = r := by
  obtain ⟨hqd, hql, hqu⟩ := of_decide_eq_true hq
  obtain ⟨hrd, hrl, hru⟩ := of_decide_eq_true hr
  by_contra hne
  have hsep := one_div_sq_le_abs_sub_of_den_le hqd hrd hne
  have hwidthRat : |q - r| < 1 / (M : ℚ) := by
    rw [add_div] at hqu hru
    rw [abs_lt]
    constructor <;> linarith
  have hwidth : |(q : ℝ) - r| < 1 / (M : ℝ) := by
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
      (Rat.cast_lt (K := ℝ)).2 hwidthRat
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (q.den_pos.trans_le hqd)
  exact (hwidth.trans_le (one_div_le_one_div_of_le (pow_pos hN _)
    (by exact_mod_cast hscale))).not_ge hsep

/-- A returned rational passes the denominator bound and both endpoint tests. -/
theorem recoverDyadic_mem_cell {N k : ℕ} {q : ℚ} (h : recoverDyadic N k = some q) :
    q.den ≤ N ∧ (k : ℚ) / (2 : ℚ) ^ (2 * Nat.clog 2 N) ≤ q ∧
      q < (k + 1 : ℚ) / (2 : ℚ) ^ (2 * Nat.clog 2 N) := by
  unfold recoverDyadic at h
  have ht := List.find?_some h
  unfold inCell at ht
  have hq := of_decide_eq_true ht
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hq

/-- The decoder recovers any reduced rational of denominator at most `N` in the half-open
cell specified by the prefix. `Rat.num` and `Rat.den` give its reduced numerator and denominator. -/
theorem recoverDyadic_eq_some {N k : ℕ} {q : ℚ} (hq : q.den ≤ N)
    (hlo : (k : ℚ) / (2 : ℚ) ^ (2 * Nat.clog 2 N) ≤ q)
    (hhi : q < (k + 1 : ℚ) / (2 : ℚ) ^ (2 * Nat.clog 2 N)) :
    recoverDyadic N k = some q := by
  let M := 2 ^ (2 * Nat.clog 2 N)
  have hM : 0 < M := by positivity
  have hscale : N ^ 2 ≤ M := by
    dsimp only [M]
    rw [mul_comm 2, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) N) 2
  have hlo' : (k : ℚ) / M ≤ q := by simpa only [M, Nat.cast_pow, Nat.cast_ofNat] using hlo
  have hhi' : q < (k + 1 : ℚ) / M := by simpa only [M, Nat.cast_pow, Nat.cast_ofNat] using hhi
  have hm := mem_cellCandidates hM hscale hq hlo' hhi'
  have hp : inCell N M k q = true := decide_eq_true ⟨hq, hlo', hhi'⟩
  change (cellCandidates M k).find? (inCell N M k) = some q
  rcases he : (cellCandidates M k).find? (inCell N M k) with _ | r
  · exact (List.find?_eq_none.mp he q hm hp).elim
  · exact congrArg some (eq_of_mem_cell hscale (List.find?_some he) hp)

end Rat
