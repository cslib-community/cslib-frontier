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
    rw [show multiply p 0 a b i =
        convolution p (coeff hp · (M 0 0)) (coeff hp · (N 0 0)) i from
      convolution_congr hip
        (fun j hj => (hA j (by simpa using hj)).trans (coefficients_of_lt hp M hj))
        (fun j hj => (hB j (by simpa using hj)).trans (coefficients_of_lt hp N hj)),
      ← coeff_mul_eq_convolution hp _ _ hip, coefficients_of_lt hp _ hip]
    simp
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
      have := Nat.mul_le_mul_right q (show t ≤ 3 by omega)
      exact (hA (t * q + s) (by rw [hs]; omega)).trans (quarter_coefficients hp k M ht hs')
    have hqa := hquarter M a hA
    have hqb := hquarter N b hB
    -- Agreement is preserved by sums and differences of quadrants.
    have hadd {x y : ℕ → ℤ} {X Y : ℕ → ℕ → CyclicIntRing p}
        (hx : ∀ s < q, x s = coefficients hp X s) (hy : ∀ s < q, y s = coefficients hp Y s) :
        ∀ s < q, (x + y) s = coefficients hp (X + Y) s :=
      fun s hs' => by simp only [Pi.add_apply, coefficients_add, hx s hs', hy s hs']
    have hsub {x y : ℕ → ℤ} {X Y : ℕ → ℕ → CyclicIntRing p}
        (hx : ∀ s < q, x s = coefficients hp X s) (hy : ∀ s < q, y s = coefficients hp Y s) :
        ∀ s < q, (x - y) s = coefficients hp (X - Y) s :=
      fun s hs' => by simp only [Pi.sub_apply, coefficients_sub, hx s hs', hy s hs']
    have h₁ := ih _ _ _ _ (hadd (hqa 0 (by decide)) (hqa 3 (by decide)))
      (hadd (hqb 0 (by decide)) (hqb 3 (by decide))) hj
    have h₂ := ih _ _ _ _ (hadd (hqa 2 (by decide)) (hqa 3 (by decide))) (hqb 0 (by decide)) hj
    have h₃ := ih _ _ _ _ (hqa 0 (by decide)) (hsub (hqb 1 (by decide)) (hqb 3 (by decide))) hj
    have h₄ := ih _ _ _ _ (hqa 3 (by decide)) (hsub (hqb 2 (by decide)) (hqb 0 (by decide))) hj
    have h₅ := ih _ _ _ _ (hadd (hqa 0 (by decide)) (hqa 1 (by decide))) (hqb 3 (by decide)) hj
    have h₆ := ih _ _ _ _ (hsub (hqa 2 (by decide)) (hqa 0 (by decide)))
      (hadd (hqb 0 (by decide)) (hqb 1 (by decide))) hj
    have h₇ := ih _ _ _ _ (hsub (hqa 1 (by decide)) (hqa 3 (by decide)))
      (hadd (hqb 2 (by decide)) (hqb 3 (by decide))) hj
    have hjeq : i % q = j := rfl
    rw [show coefficients hp (fun r s => ∑ c ∈ Finset.range (2 ^ (k + 1)), M r c * N c s) i =
        coefficients hp (submatrix k t _) j by rw [← he]; exact quarter_coefficients hp k _ ht hj]
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
