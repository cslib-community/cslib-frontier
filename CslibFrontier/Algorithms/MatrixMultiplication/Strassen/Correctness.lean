/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.MatrixMultiplication.Strassen.Coefficients
import Mathlib.Tactic.IntervalCases

/-!
# Correctness of the seven-product cyclic coefficient recursion

The finite recursion computes coefficients of ordinary matrix multiplication over the
existing cyclic integer quotient. Its inputs need agree with the matrix only inside the
occupied native coefficient blocks. There is no assumed multiplication implementation.

The block identity adapts pinned Spec/Sec3/Theorem17/Strassen.lean, lines 105–126, at revision
16a5ce41304fcdaea4e0be7c132e1c361dc26da5. This theorem is mathematical; the independent native
controller execution proof must additionally account for its actual forms, stack and calls.
-/

public section

namespace Cslib.Algorithms.MatrixMultiplication.Strassen

open Cslib.CyclicIntRing

private theorem sum_two_pow_succ {R : Type*} [AddCommMonoid R] (k : ℕ) (f : ℕ → R) :
    ∑ c ∈ Finset.range (2 ^ (k + 1)), f c =
      ∑ c ∈ Finset.range (2 ^ k), f c + ∑ c ∈ Finset.range (2 ^ k), f (c + 2 ^ k) := by
  rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
  simp only [Nat.add_comm]

/-- Every occupied coefficient of the seven-product recursion is the corresponding
coefficient of the ordinary ring-matrix product. -/
theorem multiply_eq_coefficients {p : ℕ} (hp : p ≠ 0) (k : ℕ)
    (M N : ℕ → ℕ → CyclicIntRing p) (a b : ℕ → ℤ)
    (hA : ∀ i < 4 ^ k * p, a i = coefficients hp M i)
    (hB : ∀ i < 4 ^ k * p, b i = coefficients hp N i)
    {i : ℕ} (hi : i < 4 ^ k * p) :
    multiply p k a b i =
      coefficients hp (fun r s => ∑ c ∈ Finset.range (2 ^ k), M r c * N c s) i := by
  induction k generalizing M N a b i with
  | zero =>
    have hip : i < p := by simpa using hi
    calc
      _ = convolution p (fun j => coeff hp j (M 0 0))
          (fun j => coeff hp j (N 0 0)) i := by
        apply convolution_congr hip
        · intro j hj
          exact (hA j (by simpa using hj)).trans (coefficients_of_lt hp M hj)
        · intro j hj
          exact (hB j (by simpa using hj)).trans (coefficients_of_lt hp N hj)
      _ = coeff hp i (M 0 0 * N 0 0) := (coeff_mul_eq_convolution hp _ _ hip).symm
      _ = _ := by rw [coefficients_of_lt hp _ hip]; simp
  | succ k ih =>
    let q := 4 ^ k * p
    let j := i % q
    have hq : 0 < q := Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero hp)
    have hs : 4 ^ (k + 1) * p = 4 * q := by dsimp [q]; rw [pow_succ]; ring
    have hqeq : 4 ^ k * p = q := rfl
    have hj : j < q := Nat.mod_lt _ hq
    have ht : i / q < 4 := (Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [← hs] using hi)
    generalize htdef : i / q = t at ht
    have he : t * q + j = i := by
      rw [← htdef, Nat.mul_comm]
      exact Nat.div_add_mod i q
    -- Each quarter of an input array agrees with the corresponding quadrant.
    have hquarter (M : ℕ → ℕ → CyclicIntRing p) (a : ℕ → ℤ)
        (hA : ∀ i < 4 ^ (k + 1) * p, a i = coefficients hp M i)
        (t : ℕ) (ht : t < 4) (s : ℕ) (hs' : s < q) :
        quarter q t a s = coefficients hp (submatrix k t M) s := by
      have hm := Nat.mul_le_mul_right q (show t ≤ 3 by omega)
      exact (hA (t * q + s) (by rw [hs]; omega)).trans
        (quarter_coefficients hp k M ht hs')
    have hqa (t : ℕ) (ht : t < 4 := by decide) := hquarter M a hA t ht
    have hqb (t : ℕ) (ht : t < 4 := by decide) := hquarter N b hB t ht
    -- Agreement is preserved by sums and differences of quadrants.
    have hadd {x y : ℕ → ℤ} {X Y : ℕ → ℕ → CyclicIntRing p}
        (hx : ∀ s < q, x s = coefficients hp X s) (hy : ∀ s < q, y s = coefficients hp Y s) :
        ∀ s < q, (x + y) s = coefficients hp (X + Y) s := fun s hs' => by
      rw [coefficients_add]
      exact congrArg₂ (· + ·) (hx s hs') (hy s hs')
    have hsub {x y : ℕ → ℤ} {X Y : ℕ → ℕ → CyclicIntRing p}
        (hx : ∀ s < q, x s = coefficients hp X s) (hy : ∀ s < q, y s = coefficients hp Y s) :
        ∀ s < q, (x - y) s = coefficients hp (X - Y) s := fun s hs' => by
      rw [coefficients_sub]
      exact congrArg₂ (· - ·) (hx s hs') (hy s hs')
    have ih' {X Y a' b'} (ha : ∀ s < q, a' s = coefficients hp X s)
        (hb : ∀ s < q, b' s = coefficients hp Y s) := ih X Y a' b' ha hb hj
    have h₁ := ih' (hadd (hqa 0) (hqa 3)) (hadd (hqb 0) (hqb 3))
    have h₂ := ih' (hadd (hqa 2) (hqa 3)) (hqb 0)
    have h₃ := ih' (hqa 0) (hsub (hqb 1) (hqb 3))
    have h₄ := ih' (hqa 3) (hsub (hqb 2) (hqb 0))
    have h₅ := ih' (hadd (hqa 0) (hqa 1)) (hqb 3)
    have h₆ := ih' (hsub (hqa 2) (hqa 0)) (hadd (hqb 0) (hqb 1))
    have h₇ := ih' (hsub (hqa 1) (hqa 3)) (hadd (hqb 2) (hqb 3))
    have hR : coefficients hp
        (fun r s => ∑ c ∈ Finset.range (2 ^ (k + 1)), M r c * N c s) i =
        coefficients hp (submatrix k t
          (fun r s => ∑ c ∈ Finset.range (2 ^ (k + 1)), M r c * N c s)) j := by
      rw [← he]
      exact quarter_coefficients hp k _ ht hj
    have hjeq : i % q = j := rfl
    rw [hR]
    simp only [multiply, hqeq, assemble, htdef, hjeq, Pi.add_apply, Pi.sub_apply]
    interval_cases t <;> simp only [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
    all_goals
      simp only [coefficients, submatrix, Pi.add_apply, Pi.sub_apply,
        Nat.reduceDiv, Nat.reduceMod, Nat.zero_mul, Nat.one_mul, Nat.add_zero,
        ← map_add, ← map_sub]
      congr 1
      rw [sum_two_pow_succ]
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring

end Cslib.Algorithms.MatrixMultiplication.Strassen
