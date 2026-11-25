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
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Foundations.Data.Rat.Approximation
import CslibFrontier.Foundations.Data.Rat.Reconstruction
import Mathlib.Data.Rat.Floor
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Continued-fraction recovery from dyadic prefixes

[Arora and Barak][AroraBarak07], web draft 2007-01-08, Chapter 20, Exercise §11
(printed p. 432, PDF p. 448), asks for polynomial-time recovery of the unknown coprime pair
`j, r ≤ N` from the first `2 log N` bits of `j/r`. The draft leaves rounding implicit.
For positive `N`, `Nat.clog 2 (N ^ 2)` gives the ceiling of twice the base-two logarithm:
it is the least fractional bit count with dyadic cell width at most `1 / N ^ 2`.
We use half-open cells (terminating-zero expansions), with the integer part included in
the cell index for numbers at least one. The result encodes the reduced numerator and
denominator, available as `Rat.num` and `Rat.den`; the numerator may exceed `N`.
The original decoder uses `2 * Nat.clog 2 N` fractional bits.

The decoder tests the included left endpoint
directly. Every interior point with denominator at most `N` satisfies Legendre's strict bound
at the midpoint, even when the bound at the left endpoint fails.

At scale `M`, write `t = (2 * k + 1).size + (2 * M).size + 1` for the Euclidean step
budget. The search tests at most `t + 2` candidates. At scale `2 ^ bits` this is at most
`k.size + bits + 6`. Each convergent at index `i` takes `i + 1` quotients and `i` rational updates.
The machine evaluates the recurrence from the innermost quotient outwards. It recomputes
the Euclidean pair from the midpoint for each quotient, keeping a unary index and one
reduced rational in the outer loop. Each intermediate reduced numerator and denominator
has at most `(i + 1) * ((max (2 * k + 1) (2 * M)).size + 3)` bits. The certificate
also charges construction of the candidate list and the denominator and endpoint comparisons.

## Main definitions

* `Rat.recoverDyadicLogSq`: recovery using the ceiling of twice the base-two logarithm.
* `Rat.recoverDyadic`: recovery using twice the ceiling of the base-two logarithm.

## Main results

* `Rat.recoverDyadic_mem_cell`: every returned rational satisfies the cell and denominator tests.
* `Rat.recoverDyadic_eq_some`: recovery of any promised rational in the cell.
* `Rat.recoverDyadicLogSq_eq_some` and `Rat.recoverDyadicLogSq_mem_cell`: correctness for
  `recoverDyadicLogSq`.
* `Rat.recoverDyadic_polyTime` and `Rat.recoverDyadicLogSq_polyTime`: native polynomial-time
  certificates on binary inputs.
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
    simp only [euclidConvergent, Real.convergent_zero, floor_nat_div_nat, Int.cast_natCast]
  | succ i ih =>
    rcases eq_or_ne b 0 with rfl | hb
    · simp [euclidConvergent_zero_den]
    have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb
    have hfract : Int.fract ((a : ℝ) / b) = (a % b : ℕ) / (b : ℝ) := by
      rw [Int.fract, floor_nat_div_nat, Int.cast_natCast, eq_div_iff hb', sub_mul,
        div_mul_cancel₀ _ hb']
      linarith [show ((a % b : ℕ) : ℝ) + b * ((a / b : ℕ) : ℝ) = a by
        exact_mod_cast Nat.mod_add_div a b]
    simp only [euclidConvergent, gcdStep, hb, ite_false, Real.convergent_succ, floor_nat_div_nat,
      Int.cast_natCast, hfract, inv_div, ih]

private theorem euclidConvergent_stable (i extra : ℕ) (p : ℕ × ℕ)
    (h : (gcdStep^[i] p).2 = 0) : euclidConvergent (i + extra) p = euclidConvergent i p := by
  induction i generalizing p with
  | zero =>
    rcases p with ⟨a, b⟩
    obtain rfl : b = 0 := h
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

private theorem length_cellCandidates_pow_le (bits k : ℕ) :
    (cellCandidates (2 ^ bits) k).length ≤ k.size + bits + 6 := by
  have hk : (2 * k + 1).size ≤ k.size + 1 := by
    apply Nat.size_le.mpr
    rw [pow_succ]
    have := Nat.lt_size_self k
    omega
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

private def recoverInCell (N M k : ℕ) : Option ℚ :=
  (cellCandidates M k).find? (inCell N M k)

/-- Recover a fraction of denominator at most `N` from the dyadic cell indexed by `k`.
For a number in `[0, 1)`, `k` is the natural represented by the first
`2 * Nat.clog 2 N` fractional bits, with leading zeros allowed. At a dyadic boundary, use the
expansion ending in zeros. More generally, add the integer part times the cell scale to `k`.
Return `none` when no fraction of denominator at most `N` lies in the cell. -/
def recoverDyadic (N k : ℕ) : Option ℚ :=
  recoverInCell N (2 ^ (2 * Nat.clog 2 N)) k

/-- Recover a reduced rational of denominator at most `N` using `Nat.clog 2 (N ^ 2)`
fractional bits. The index `k` uses the terminating-zero and integer-part conventions
of `recoverDyadic`. Return `none` if the cell contains no such rational. -/
def recoverDyadicLogSq (N k : ℕ) : Option ℚ :=
  recoverInCell N (2 ^ Nat.clog 2 (N ^ 2)) k

private theorem mem_cellCandidates {N M k : ℕ} {q : ℚ}
    (hM : 0 < M) (hscale : N ^ 2 ≤ M) (hq : q.den ≤ N)
    (hlo : (k : ℚ) / M ≤ q) (hhi : q < (k + 1 : ℚ) / M) :
    q ∈ cellCandidates M k := by
  rcases eq_or_lt_of_le hlo with heq | hlo
  · simp [cellCandidates, heq]
  let a := 2 * k + 1
  let b := 2 * M
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hlor : (k : ℝ) / M < q := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using (Rat.cast_lt (K := ℝ)).2 hlo
  have hhir : (q : ℝ) < (k + 1 : ℝ) / M := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).2 hhi
  have hsq : (q.den : ℝ) ^ 2 ≤ M := mod_cast (Nat.pow_le_pow_left hq 2).trans hscale
  have hmid : (a : ℝ) / b = (k : ℝ) / M + 1 / (2 * M) := by
    push_cast [a, b]
    field_simp
  have hhu : (k + 1 : ℝ) / M = (k : ℝ) / M + 2 * (1 / (2 * (M : ℝ))) := by field_simp
  have hclose : |(a : ℝ) / b - q| < 1 / (2 * (q.den : ℝ) ^ 2) :=
    (abs_lt.mpr ⟨by linarith, by linarith⟩).trans_le
      (one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hsq zero_le_two))
  obtain ⟨i, hi⟩ := Real.exists_rat_eq_convergent hclose
  let p : ℕ × ℕ := (a, b)
  have hei : euclidConvergent i p = q := (euclidConvergent_eq i a b).trans hi.symm
  refine List.mem_cons_of_mem _ (List.mem_map.mpr
    ⟨min i (gcdCount p), List.mem_range.mpr (Nat.lt_succ_of_le (min_le_right ..)), ?_⟩)
  rcases le_or_gt i (gcdCount p) with h | h
  · simpa only [min_eq_left h] using hei
  · rw [min_eq_right h.le, ← euclidConvergent_stable (gcdCount p) (i - gcdCount p) p
      (snd_iterate_gcdStep_gcdCount p), Nat.add_sub_of_le h.le]
    exact hei

private theorem eq_of_mem_cell {N M k : ℕ} {q r : ℚ} (hscale : N ^ 2 ≤ M)
    (hq : inCell N M k q = true) (hr : inCell N M k r = true) : q = r := by
  obtain ⟨hqd, hql, hqu⟩ := of_decide_eq_true hq
  obtain ⟨hrd, hrl, hru⟩ := of_decide_eq_true hr
  by_contra hne
  have hwidthRat : |q - r| < 1 / (M : ℚ) := by
    rw [add_div] at hqu hru
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hwidth : |(q : ℝ) - r| < 1 / (M : ℝ) := by
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
      (Rat.cast_lt (K := ℝ)).2 hwidthRat
  exact (hwidth.trans_le (one_div_le_one_div_of_le
    (pow_pos (Nat.cast_pos.2 (q.den_pos.trans_le hqd)) _) (by exact_mod_cast hscale))).not_ge
    (one_div_sq_le_abs_sub_of_den_le hqd hrd hne)

private theorem recoverInCell_mem_cell {N M k : ℕ} {q : ℚ}
    (h : recoverInCell N M k = some q) :
    q.den ≤ N ∧ (k : ℚ) / M ≤ q ∧ q < (k + 1 : ℚ) / M := by
  rw [recoverInCell] at h
  simpa [inCell] using List.find?_some h

private theorem recoverInCell_eq_some {N M k : ℕ} {q : ℚ}
    (hM : 0 < M) (hscale : N ^ 2 ≤ M) (hq : q.den ≤ N)
    (hlo : (k : ℚ) / M ≤ q) (hhi : q < (k + 1 : ℚ) / M) :
    recoverInCell N M k = some q := by
  have hm := mem_cellCandidates hM hscale hq hlo hhi
  have hp : inCell N M k q = true := decide_eq_true ⟨hq, hlo, hhi⟩
  change (cellCandidates M k).find? (inCell N M k) = some q
  rcases he : (cellCandidates M k).find? (inCell N M k) with _ | r
  · exact (List.find?_eq_none.mp he q hm hp).elim
  · exact congrArg some (eq_of_mem_cell hscale (List.find?_some he) hp)

/-- A returned rational passes the denominator bound and both endpoint tests. -/
theorem recoverDyadic_mem_cell {N k : ℕ} {q : ℚ} (h : recoverDyadic N k = some q) :
    q.den ≤ N ∧ (k : ℚ) / (2 : ℚ) ^ (2 * Nat.clog 2 N) ≤ q ∧
      q < (k + 1 : ℚ) / (2 : ℚ) ^ (2 * Nat.clog 2 N) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    recoverInCell_mem_cell (M := 2 ^ (2 * Nat.clog 2 N)) h

/-- The decoder recovers any reduced rational of denominator at most `N` in the half-open
cell specified by the prefix. `Rat.num` and `Rat.den` give its reduced numerator and denominator. -/
theorem recoverDyadic_eq_some {N k : ℕ} {q : ℚ} (hq : q.den ≤ N)
    (hlo : (k : ℚ) / (2 : ℚ) ^ (2 * Nat.clog 2 N) ≤ q)
    (hhi : q < (k + 1 : ℚ) / (2 : ℚ) ^ (2 * Nat.clog 2 N)) :
    recoverDyadic N k = some q := by
  have hscale : N ^ 2 ≤ 2 ^ (2 * Nat.clog 2 N) := by
    rw [mul_comm 2, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) N) 2
  apply recoverInCell_eq_some (by positivity) hscale hq
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlo
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hhi

/-- A returned rational passes the denominator bound and both endpoint tests. -/
theorem recoverDyadicLogSq_mem_cell {N k : ℕ} {q : ℚ} (h : recoverDyadicLogSq N k = some q) :
    q.den ≤ N ∧ (k : ℚ) / (2 : ℚ) ^ Nat.clog 2 (N ^ 2) ≤ q ∧
      q < (k + 1 : ℚ) / (2 : ℚ) ^ Nat.clog 2 (N ^ 2) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    recoverInCell_mem_cell (M := 2 ^ Nat.clog 2 (N ^ 2)) h

/-- The decoder recovers any reduced rational of denominator at most `N` in the half-open
cell specified by the prefix. `Rat.num` and `Rat.den` give its reduced numerator and denominator. -/
theorem recoverDyadicLogSq_eq_some {N k : ℕ} {q : ℚ} (hq : q.den ≤ N)
    (hlo : (k : ℚ) / (2 : ℚ) ^ Nat.clog 2 (N ^ 2) ≤ q)
    (hhi : q < (k + 1 : ℚ) / (2 : ℚ) ^ Nat.clog 2 (N ^ 2)) :
    recoverDyadicLogSq N k = some q := by
  have hscale : N ^ 2 ≤ 2 ^ Nat.clog 2 (N ^ 2) := Nat.le_pow_clog (by decide) _
  apply recoverInCell_eq_some (by positivity) hscale hq
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlo
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hhi

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

section

attribute [local irreducible] encRat encNat encUnary

private abbrev encEuclidPair := encPair encNat encNat

private def convergentStep (p : ℕ × ℕ) (state : ℕ × ℚ) : ℕ × ℚ :=
  let j := state.1 - 1
  let r := gcdStep^[j] p
  (j, (r.1 / r.2 : ℕ) + state.2⁻¹)

private theorem convergentStep_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × (ℕ × ℚ) => convergentStep x.1 x.2)
      (encPair encEuclidPair (encPair encUnary encRat)) (encPair encUnary encRat) := by
  have hj : ComputableInPolyTime (fun x : (ℕ × ℕ) × (ℕ × ℚ) => x.2.1 - 1)
      (encPair encEuclidPair (encPair encUnary encRat)) encUnary := by
    unfold encEuclidPair
    fun_prop
  have hr : ComputableInPolyTime
      (fun x : (ℕ × ℕ) × (ℕ × ℚ) => gcdStep^[x.2.1 - 1] x.1)
      (encPair encEuclidPair (encPair encUnary encRat)) (encPair encNat encNat) :=
    binary_gcdIterate.comp ((fst encEuclidPair (encPair encUnary encRat)).prod hj)
  exact hj.prod (by dsimp only [convergentStep, encEuclidPair] at hr ⊢; fun_prop)

private theorem convergentStep_iterate (p : ℕ × ℕ) (i j : ℕ) (hj : j ≤ i) :
    (convergentStep p)^[j] (i, euclidConvergent 0 (gcdStep^[i] p)) =
      (i - j, euclidConvergent j (gcdStep^[i - j] p)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hsub : i - j = (i - (j + 1)).succ := by omega
    simp only [convergentStep, Nat.sub_sub, euclidConvergent]
    rw [← Function.iterate_succ_apply' gcdStep, ← hsub]

private theorem euclidConvergent_polyTime :
    ComputableInPolyTime (fun x : (ℕ × ℕ) × ℕ => euclidConvergent x.2 x.1)
      (encPair encEuclidPair encUnary) encRat := by
  let input := encPair encEuclidPair encUnary
  let init (x : (ℕ × ℕ) × ℕ) := (x.2, euclidConvergent 0 (gcdStep^[x.2] x.1))
  have hinit : ComputableInPolyTime init input (encPair encUnary encRat) := by
    have hquot := binary_div' binary_gcdIterate.fst' binary_gcdIterate.snd'
    exact (snd _ _).prod (rat_natCast.comp hquot)
  have hbound : PolyBounded (fun x => (input x).length)
      (fun x => 2 * (input x).length +
        3 * ((input x).length + 1) * ((input x).length + 3) + 4) := by growth_poly
  have hloop := iterateWith (fst encEuclidPair encUnary) (snd _ _) hinit
    convergentStep_polyTime hbound (fun x j hj => by
      dsimp only [init]
      rw [convergentStep_iterate _ _ _ hj]
      let n := (input x).length
      have hi := length_le_encPair_right encEuclidPair encUnary x
      rw [encUnary_apply, List.length_replicate] at hi
      change x.2 ≤ n at hi
      let operands := x.1
      have hp : (max operands.1 operands.2).size ≤ n := by
        have h : (encEuclidPair operands).length ≤ n :=
          length_le_encPair_left encEuclidPair encUnary x
        simp only [encEuclidPair, length_encPair, encNat_apply, Nat.size_eq_bits_len] at h
        rcases le_total operands.1 operands.2 with hle | hle
        · rw [max_eq_right hle]
          omega
        · rw [max_eq_left hle]
          omega
      let q := euclidConvergent j (gcdStep^[x.2 - j] x.1)
      have hq : q.height.size ≤ (n + 1) * (n + 3) :=
        (euclidConvergent_height_size j _).trans (Nat.mul_le_mul
          (by omega) (Nat.add_le_add_right
            ((Nat.size_le_size (max_iterate_gcdStep_le x.1 _)).trans hp) 3))
      have hword : (encRat q).length ≤ 2 * q.height.size + q.height.size + 3 :=
        length_encRat_le q (le_max_left _ _) (le_max_right _ _)
      change (encPair encUnary encRat (x.2 - j, q)).length ≤
        2 * n + 3 * (n + 1) * (n + 3) + 4
      rw [length_encPair]
      simp only [encUnary_apply, List.length_replicate]
      have := Nat.mul_le_mul_left 3 hq
      simp only [← Nat.mul_assoc] at this
      omega)
  refine hloop.snd'.of_enc_eq fun x => ?_
  dsimp only [init]
  rw [convergentStep_iterate _ _ _ le_rfl, Nat.sub_self]
  rfl

private theorem midpointConvergents_polyTime :
    ComputableInPolyTime
      (fun p : ℕ × ℕ => (List.range (gcdCount p + 1)).map (fun i => euclidConvergent i p))
      encEuclidPair (encList encRat) := by
  have hcount : ComputableInPolyTime gcdCount encEuclidPair encUnary := by
    unfold gcdCount encEuclidPair
    fun_prop
  have hrange := range.comp (unary_add' hcount (const 1))
  exact mapWithInput (f := fun p i => euclidConvergent i p) hrange euclidConvergent_polyTime

private theorem cellCandidates_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => cellCandidates p.1 p.2)
      encEuclidPair (encList encRat) :=
  cons' (by unfold encEuclidPair; fun_prop)
    (midpointConvergents_polyTime.comp (g := fun p : ℕ × ℕ => (2 * p.2 + 1, 2 * p.1))
      (by unfold encEuclidPair; fun_prop))

private theorem inDyadicCell_polyTime {scale : ℕ → ℕ}
    (hscale : ComputableInPolyTime scale encNat encNat) :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℚ =>
        let input := p.1
        inCell input.1 (scale input.1) input.2 p.2)
      (encPair encEuclidPair encRat) encBool := by
  fun_prop [inCell, encEuclidPair]

private theorem recoverInCell_polyTime {scale : ℕ → ℕ}
    (hscale : ComputableInPolyTime scale encNat encNat) :
    ComputableInPolyTime (fun p : ℕ × ℕ => recoverInCell p.1 (scale p.1) p.2)
      encEuclidPair (encOption encRat) :=
  findWithInput
    (test := fun (p : ℕ × ℕ) => inCell p.1 (scale p.1) p.2)
    (cellCandidates_polyTime.comp (g := fun p : ℕ × ℕ => (scale p.1, p.2))
      (by unfold encEuclidPair; fun_prop))
    (inDyadicCell_polyTime hscale)

/-- Recover a reduced rational in polynomial time from the binary denominator bound and cell
index. The machine tests the included endpoint and the same midpoint convergents as
`recoverDyadic`, returning an optional signed binary numerator and binary denominator. -/
@[fun_prop]
theorem recoverDyadic_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => recoverDyadic p.1 p.2)
      (encPair encNat encNat) (encOption encRat) :=
  recoverInCell_polyTime (scale := fun N => 2 ^ (2 * Nat.clog 2 N)) (by fun_prop)

/-- Polynomial-time recovery at the precision rounded after doubling, from the binary bound
and cell index to an optional reduced rational encoded as in `recoverDyadic_polyTime`. -/
@[fun_prop]
theorem recoverDyadicLogSq_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => recoverDyadicLogSq p.1 p.2)
      (encPair encNat encNat) (encOption encRat) :=
  recoverInCell_polyTime (scale := fun N => 2 ^ Nat.clog 2 (N ^ 2)) (by fun_prop)

end

end Rat
