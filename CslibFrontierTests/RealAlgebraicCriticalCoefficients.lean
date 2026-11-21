/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoefficientEvaluation
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Constructed critical coefficient certificates and edge cases -/

public section
namespace CslibFrontierTests.RealAlgebraicCriticalCoefficients

open Cslib Cslib.Complexity Cslib.Complexity.RealAlgebraic Turing.MultiTapeTM
open MvPolynomial MvPolynomial.CriticalSystem MvPolynomial.PurePower

private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

-- Above-dimension addresses return zero even for arbitrary evaluators and nonprime moduli.
example (p n ell B m : ℕ) (hm : ell ^ n < m)
    (v J : List ℕ → ℕ) (r : ℕ → List ℕ → ℕ) :
    quotientCharacteristicValue p n ell B m v J r = 0 := by
  simp [quotientCharacteristicValue, traceExponentialCoefficient, Nat.not_le.mpr hm]

-- A single certificate handles binary deformation parameters and coefficient addresses.
example : (fun q : ℕ × ℕ => criticalCoefficientValue 101 1 1 q.1 q.2 (fun _ => 0)) ∈
    CountingFunction 9 (encPair encNat encNat) encNat := by
  simpa using criticalCoefficientValue_mem (a := 0) (Decoder.pair Decoder.nat Decoder.nat)
    (p := fun _ => 101) (n := fun _ => 1) (d := fun _ => 1)
    (u := fun q : ℕ × ℕ => q.1) (m := fun q => q.2) (value := fun _ => 0)
    (.const 101) (.const 1) (.const 1) (by fun_prop) (by fun_prop)
    (CountingFunction.of_polyTime (.const 0))

-- A positive-dimensional instance satisfies all cutoffs, including at zero deformation.
theorem positiveDimensionalInstance (u m : ℕ) : criticalCoefficientValue 101 1 1 u m (fun _ => 0) =
    ((multiplicationMatrix (by decide : 1 ≤ 2)
      (criticalLower 2 (fun i : Fin 1 => ((separatedCenters 2 i : ℕ) : ZMod 101))
        (u : ZMod 101) 0)
      (criticalLower_degree 2 (by decide) _ _ 0 (by simp))
      (deformedPolynomial 2 (fun i : Fin 1 => ((separatedCenters 2 i : ℕ) : ZMod 101))
        (u : ZMod 101) 0)).charpoly.coeff m).val := by
  apply criticalCoefficientValue_eq 1 (by decide) u 0 (by simp) (by decide) (by decide)
  intro y
  simp

-- Reducing the integer quotient modulo 101 preserves the constant coefficient of `X - 1`.
example : quotientCharacteristicValue 101 0 2 0 0 (fun _ => 1) (fun _ => 1)
    (fun _ _ => 0) = 100 := by
  have h := quotientCharacteristicValue_eq_specialization (p := 101) (n := 0) (B := 0) (m := 0)
    (Int.castRingHom (ZMod 101)) 1 (by decide) (fun _ => 0) (by simp)
    (1 : MvPolynomial (Fin 0) ℤ)
    (by intro k _ _; simp [jacobian, Matrix.det_isEmpty]) (by decide) (by decide)
    (fun _ => 1) (fun _ => 1) (fun _ _ => 0)
    (by simp) (by simp [jacobian, Matrix.det_isEmpty]) (by simp)
  have hdim : Fintype.card (NormalIndex 0 2) = 1 := by simp [NormalIndex]
  simpa [Matrix.charpoly_one, hdim, ZMod.val_neg_one] using h

-- The relation X₀² = 102 changes to X₀² = 1 modulo 101. Multiplication by X₀
-- has constant characteristic coefficient -102 over ℤ, which reduces to 100.
example : quotientCharacteristicValue 101 1 2 3 0
    (fun z => z[0]?.getD 0) (fun z => 2 * z[0]?.getD 0) (fun _ _ => 1) = 100 := by
  let r : Fin 1 → MvPolynomial (Fin 1) ℤ := fun _ => C 102
  let x : MvPolynomial (Fin 1) ℤ := X 0
  have hr (i : Fin 1) : (r i).totalDegree ≤ 1 := by
    simp only [r, totalDegree_C, Nat.zero_le]
  have hJ : jacobian 2 r = C 2 * x := by
    rw [jacobian, Matrix.det_fin_one]
    change pderiv (0 : Fin 1) (x ^ 2 - C 102) = C 2 * x
    rw [map_sub, pderiv_C, sub_zero, pderiv_pow]
    norm_num [x, C_eq_natCast]
  have hx : x.totalDegree ≤ 1 := totalDegree_X_le _
  have hCdeg (c : ℤ) : (C c * x).totalDegree ≤ 1 := by
    have hm := totalDegree_mul (C c) x
    rw [totalDegree_C, zero_add] at hm
    exact hm.trans hx
  have hdeg (k : ℕ) (_hk : 1 ≤ k) (hK : k ≤ 2 ^ 1) :
      (x ^ k * jacobian 2 r).totalDegree ≤ 3 := by
    rw [hJ]
    have hk : (x ^ k).totalDegree ≤ 2 := by
      refine (totalDegree_pow x k).trans ?_
      simpa only [pow_one, mul_one] using Nat.mul_le_mul hK hx
    exact (totalDegree_mul _ _).trans (Nat.add_le_add hk (hCdeg 2))
  have h := quotientCharacteristicValue_eq_specialization (p := 101) (n := 1) (B := 3) (m := 0)
    (Int.castRingHom (ZMod 101)) 1 (by decide) r hr x hdeg (by decide) (by decide)
    (fun z => z[0]?.getD 0) (fun z => 2 * z[0]?.getD 0) (fun _ _ => 1)
    (by simp [x]) (by simp [hJ, x]) (by
      intro i s hs
      simp only [r, map_C, eval_C]
      decide)
  let M := multiplicationMatrix (by decide : 1 ≤ 2) r
    (fun i => (hr i).trans_lt (by decide)) x
  have htrace (k : ℕ) : (M ^ k).trace = residue 2 r (x ^ k * (C 2 * x)) := by
    rw [multiplicationMatrix_trace_pow 1 (by decide) r hr, hJ]
  have htop : Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => 2 - 1) =
      Finsupp.single (0 : Fin 1) 1 := by
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  have ht1 : M.trace = 0 := by
    rw [← pow_one M, htrace, pow_one,
      show x * (C 2 * x) = C 2 * x ^ 2 by ring,
      residue_mul_X_pow (by decide) r (fun i => (hr i).trans_lt (by decide)),
      show r 0 = C 102 from rfl,
      ← map_mul, residue_low_degree (by decide) _ (fun i => (hr i).trans_lt (by decide)) _
        (by rw [totalDegree_C]; decide), htop]
    simp
  have ht2 : (M ^ 2).trace = 204 := by
    rw [htrace, show x ^ 2 * (C 2 * x) = (C 2 * x) * x ^ 2 by ring,
      residue_mul_X_pow (by decide) r (fun i => (hr i).trans_lt (by decide)),
      show r 0 = C 102 from rfl,
      show C 2 * x * C 102 = C 204 * x by rw [mul_right_comm, ← map_mul]; norm_num,
      residue_low_degree (by decide) r (fun i => (hr i).trans_lt (by decide)) _ (hCdeg 204),
      htop, show x = X 0 from rfl, C_mul_X_eq_monomial, coeff_monomial]
    simp
  have hdim : Fintype.card (NormalIndex 1 2) = 2 := by simp [NormalIndex]
  have hnewton := Matrix.charpolyRev_newton M 1
  have hc0 : M.charpolyRev.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hrev : M.charpolyRev.coeff 2 = M.charpoly.coeff 0 := by
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
      hdim, Polynomial.revAt_le (by decide : 2 ≤ 2)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one, ht1, mul_zero,
    hc0, ht2, one_mul, hrev] at hnewton
  have hcoeff : M.charpoly.coeff 0 = -102 := by omega
  change _ = (Int.castRingHom (ZMod 101) (M.charpoly.coeff 0)).val at h
  rw [h, hcoeff]
  decide

end CslibFrontierTests.RealAlgebraicCriticalCoefficients
