/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.Int.DotProduct
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
public import Mathlib.Analysis.InnerProductSpace.PiL2
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rational normalization of integer vectors

A finite vector is represented by signed integer numerators and one natural denominator.
`normalize p z` multiplies the numerators by `p` and uses
`Nat.sqrt (p² * ∑ zᵢ²) + 1` as the denominator. The zero vector is represented with denominator
one. For every nonzero integer vector and positive precision scale `p`, this rational vector
is within Euclidean distance `1 / p` of the unit vector in the same direction.

The computation uses a binary integer square root and exact integer arithmetic. Its native
polynomial-time certificate charges both the precision scale and every coefficient in binary.
The real norm occurs only in the correctness statement.

## Main results

* `normalize_close`: dimension-independent Euclidean normalization error.
* `computableInPolyTime_normalize`: uniform native certificate for the rational output.
-/

public section

namespace Cslib.Algorithms.IntegerVector

open Finset Turing.MultiTapeTM Mathlib.Tactic.Matrix

/-- A finite rational vector with signed integer numerators and a common natural denominator.
The real interpretation is total, using zero when the denominator is zero. -/
structure RationalVector where
  /-- Numerators, in coordinate order. -/
  numerators : List ℤ
  /-- Common denominator; the normalization algorithm always returns a positive one. -/
  denominator : ℕ
  deriving DecidableEq

/-- Framed signed-binary numerator list, followed by the binary common denominator. -/
enc_structure encRationalVector : RationalVector where
  numerators : (encList encIntBin),
  denominator : encNat

/-- Interpret a common-denominator vector in a specified dimension, padding missing entries
with zeros and discarding any excess entries. -/
noncomputable def RationalVector.toEuclidean (v : RationalVector) (n : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => (v.numerators.getD i.val 0 : ℝ) / (v.denominator : ℝ)

/-- Approximate unit normalization using a common denominator and a binary integer square root.
The natural precision scale and all vector entries are runtime inputs. -/
@[expose] def normalize (p : ℕ) (z : List ℤ) : RationalVector where
  numerators := z.map fun a => (p : ℤ) * a
  denominator := (p ^ 2 * (ListMatrix.dotProduct z.length z z).natAbs).sqrt + 1

/-- Every output of rational normalization has a positive denominator. -/
theorem normalize_denominator_pos (p : ℕ) (z : List ℤ) :
    0 < (normalize p z).denominator := by
  simp [normalize]

/-- On a finite integer vector, the rational output is a single positive rescaling when
the precision scale is positive. In particular, normalization preserves coordinate ordering. -/
theorem normalize_toEuclidean_ofFn {n : ℕ} (p : ℕ) (z : Fin n → ℤ) :
    (normalize p (List.ofFn z)).toEuclidean n =
      ((p : ℝ) / (normalize p (List.ofFn z)).denominator) •
        WithLp.toLp 2 (fun i => (z i : ℝ)) := by
  ext i
  simp [RationalVector.toEuclidean, normalize, List.map_ofFn,
    mul_div_assoc, div_mul_eq_mul_div]

/-- Uniform native polynomial-time rational normalization, with the scale and signed
coefficients charged in binary. -/
@[fun_prop] theorem computableInPolyTime_normalize {α : Type} {encIn : α ↪ List Bool}
    {p : α → ℕ} {z : α → List ℤ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hz : ComputableInPolyTime z encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => normalize (p x) (z x)) encIn encRationalVector := by
  have hcast := ComputableInPolyTime.intBin_natCast.comp hp
  have hdot : ComputableInPolyTime
      (fun x => ListMatrix.dotProduct (z x).length (z x) (z x)) encIn encIntBin := by
    have hargs : ComputableInPolyTime (fun x => ((z x).length, z x, z x)) encIn
        (encPair encUnary (encPair (encList encIntBin) (encList encIntBin))) := by fun_prop
    exact ComputableInPolyTime.listDotProduct.comp hargs
  have habs := ComputableInPolyTime.intBin_natAbs.comp hdot
  have hsquare : ComputableInPolyTime
      (fun x => (p x) ^ 2 * (ListMatrix.dotProduct (z x).length (z x) (z x)).natAbs)
      encIn encNat := by
    fun_prop
  have hroot := ComputableInPolyTime.binary_sqrt.comp hsquare
  unfold normalize
  fun_prop

private theorem sqrt_scale_error {p q : ℕ} (hp : 0 < p) {r : ℝ}
    (hr : 1 ≤ r) (hq : r ^ 2 = (q : ℝ)) :
    |(p : ℝ) * r / ((p ^ 2 * q).sqrt + 1 : ℕ) - 1| ≤ 1 / (p : ℝ) := by
  let d : ℕ := (p ^ 2 * q).sqrt + 1
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hr0 : 0 ≤ r := by linarith
  have hdR : (0 : ℝ) < d := by dsimp [d]; positivity
  have hqR : (1 : ℝ) ≤ q := by nlinarith
  have hqN : 1 ≤ q := by exact_mod_cast hqR
  have hpd : p ≤ d := by
    have hroot : p ≤ (p ^ 2 * q).sqrt := Nat.le_sqrt.mpr (by
      simpa only [Nat.pow_two, mul_one] using Nat.mul_le_mul_left (p * p) hqN)
    omega
  have hpdR : (p : ℝ) ≤ d := by exact_mod_cast hpd
  have hlow : ((p ^ 2 * q).sqrt : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 * q := by
    exact_mod_cast Nat.sqrt_le' (p ^ 2 * q)
  have hupp : (p : ℝ) ^ 2 * q < (d : ℝ) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (p ^ 2 * q)
  have hsqrtR : (0 : ℝ) ≤ (p ^ 2 * q).sqrt := by positivity
  have hd_eq : (d : ℝ) = ((p ^ 2 * q).sqrt : ℝ) + 1 := by simp [d]
  rw [← hq, ← mul_pow] at hlow hupp
  have hpr : (p : ℝ) * r ≤ d :=
    ((sq_lt_sq₀ (mul_nonneg hpR.le hr0) hdR.le).mp hupp).le
  have hdiff : (d : ℝ) - p * r ≤ 1 := by
    have hroot := (sq_le_sq₀ hsqrtR (mul_nonneg hpR.le hr0)).mp hlow
    linarith
  change |(p : ℝ) * r / (d : ℝ) - 1| ≤ _
  rw [abs_of_nonpos (sub_nonpos.mpr ((div_le_one hdR).mpr hpr))]
  have heq : -((p : ℝ) * r / (d : ℝ) - 1) = ((d : ℝ) - p * r) / d := by
    field_simp [hdR.ne']
    ring
  rw [heq]
  exact (div_le_div_of_nonneg_right hdiff hdR.le).trans
    (one_div_le_one_div_of_le hpR hpdR)

/-- Rational normalization is within `1 / p` of unit normalization of any nonzero integer
vector. The error bound is independent of its dimension and coefficient magnitudes. -/
theorem normalize_close {n : ℕ} (p : ℕ) (hp : 0 < p) (z : Fin n → ℤ)
    (hz : (WithLp.toLp 2 (fun i => (z i : ℝ)) : EuclideanSpace ℝ (Fin n)) ≠ 0) :
    ‖(normalize p (List.ofFn z)).toEuclidean n -
      ‖WithLp.toLp 2 (fun i => (z i : ℝ))‖⁻¹ • WithLp.toLp 2 (fun i => (z i : ℝ))‖ ≤
      1 / (p : ℝ) := by
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => (z i : ℝ)
  let Q : ℤ := ∑ i, z i * z i
  let d : ℕ := (p ^ 2 * Q.natAbs).sqrt + 1
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
  have hQcast : (Q.natAbs : ℝ) = ‖x‖ ^ 2 := by
    have habs : (Q.natAbs : ℤ) = Q := by rw [Int.natCast_natAbs, abs_of_nonneg hQ]
    calc
      (Q.natAbs : ℝ) = ((Q.natAbs : ℤ) : ℝ) := by simp only [Int.cast_natCast]
      _ = (Q : ℝ) := congrArg (fun a : ℤ => (a : ℝ)) habs
      _ = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [Q, x, pow_two]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hz
  have hqpos : 0 < Q.natAbs := by
    by_contra h
    have hzero : Q.natAbs = 0 := by omega
    simp only [hzero, Nat.cast_zero] at hQcast
    nlinarith [sq_pos_of_pos hxpos]
  have hxone : 1 ≤ ‖x‖ := by
    have hqone : (1 : ℝ) ≤ Q.natAbs := by exact_mod_cast hqpos
    nlinarith
  have heq : (normalize p (List.ofFn z)).toEuclidean n = ((p : ℝ) / d) • x := by
    have hdot : ListMatrix.dotProduct (List.ofFn z).length (List.ofFn z) (List.ofFn z) = Q := by
      rw [List.length_ofFn, ListMatrix.dotProduct_ofFn]
    rw [normalize_toEuclidean_ofFn]
    simp only [normalize, hdot]
    rfl
  rw [heq]
  change ‖((p : ℝ) / d) • x - ‖x‖⁻¹ • x‖ ≤ _
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  have hnorm : |(p : ℝ) / d - ‖x‖⁻¹| * ‖x‖ = |(p : ℝ) * ‖x‖ / d - 1| := by
    calc
      _ = |((p : ℝ) / d - ‖x‖⁻¹) * ‖x‖| := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg x)]
      _ = _ := by
        congr 1
        rw [sub_mul, inv_mul_cancel₀ hxpos.ne']
        ring
  rw [hnorm]
  exact sqrt_scale_error hp hxone hQcast.symm

end Cslib.Algorithms.IntegerVector
