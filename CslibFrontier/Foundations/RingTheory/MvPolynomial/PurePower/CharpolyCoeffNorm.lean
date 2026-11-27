/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, pure-power polynomial quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.ParameterCoeffNorm
public import CslibFrontier.Foundations.Data.Polynomial.BivariateCoeffNorm1
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.MultiplicationMatrix
public import Mathlib.Data.Nat.Size
import CslibFrontier.Foundations.Data.MvPolynomial.CoeffSumBounds
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.CoeffNorm
import CslibFrontier.Foundations.LinearAlgebra.Matrix.DeterminantWeight
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.ResidueCoeffNorm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Coefficient norms of pure-power quotient characteristic polynomials

The Jacobian norm follows from the norms of the lower relations. The finite residue formula
then bounds the positive power traces, and Newton's identity bounds the characteristic
polynomial of multiplication in the quotient. The Jacobian and trace estimates permit
subadditive, submultiplicative coefficient weights invariant under negation. When the
weight scales exactly under natural scalar multiplication, the same binary budget
bounds the characteristic norm, including for multivariate polynomial parameters.

Adapted from `LeanCanny.CountingHierarchy.QuotientMassBounds` and
`LeanCanny.CountingHierarchy.MultivariateQuotientMass` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. The bounds keep their natural-number factors
explicit, use the sharper residue bound, and retain the power of the multiplier's norm.
-/

public section

namespace MvPolynomial.PurePower

private theorem jacobian_weight_sum_le {S : Type*} [CommRing S] {w : S → ℕ}
    (hzero : w 0 = 0) (hone : w 1 ≤ 1)
    (hadd : ∀ a b, w (a + b) ≤ w a + w b) (hmul : ∀ a b, w (a * b) ≤ w a * w b)
    (hneg : ∀ a, w (-a) = w a) {n d R : ℕ}
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (hR : ∀ i, (r i).coeff.sum (fun _ a => w a) ≤ R) :
    (jacobian (d + 1) r).coeff.sum (fun _ a => w a) ≤ n.factorial * ((d + 1) * (1 + R)) ^ n := by
  classical
  let norm (p : MvPolynomial (Fin n) S) := p.coeff.sum (fun _ a => w a)
  have hnorm_zero : norm 0 = 0 := by simp [norm]
  have hnorm_one : norm 1 ≤ 1 := by
    change (C (1 : S) : MvPolynomial (Fin n) S).coeff.sum (fun _ a => w a) ≤ 1
    rw [sum_C hzero]
    exact hone
  have hnorm_add (p q : MvPolynomial (Fin n) S) : norm (p + q) ≤ norm p + norm q :=
    sum_add_le_of_subadditive hzero hadd p q
  have hnorm_mul (p q : MvPolynomial (Fin n) S) : norm (p * q) ≤ norm p * norm q :=
    sum_mul_le_of_submultiplicative hzero hadd hmul p q
  have hnorm_neg (p : MvPolynomial (Fin n) S) : norm (-p) = norm p := by
    simp only [norm, sum_def, support_neg, coeff_neg, hneg]
  have hvar (i : Fin n) : norm (X i) ≤ 1 := by
    change (monomial (Finsupp.single i 1) (1 : S)).coeff.sum (fun _ a => w a) ≤ 1
    rw [sum_monomial_eq hzero]
    exact hone
  have hentry (i j : Fin n) : norm (pderiv j (X i ^ (d + 1) - r i)) ≤ (d + 1) * (1 + R) := by
    have hdeg : (X i ^ (d + 1) - r i).totalDegree ≤ d + 1 := by
      refine (totalDegree_sub _ _).trans (max_le ?_ ((hr i).trans (Nat.le_succ d)))
      exact (totalDegree_pow _ _).trans
        ((Nat.mul_le_mul_left _ (totalDegree_X_le i)).trans_eq (mul_one _))
    have hx : norm (X i ^ (d + 1)) ≤ 1 := by
      simpa only [one_pow] using
        (sum_pow_le_of_submultiplicative hzero hone hadd hmul
          (X i : MvPolynomial (Fin n) S) (d + 1)).trans (Nat.pow_le_pow_left (hvar i) _)
    have hnorm : norm (X i ^ (d + 1) - r i) ≤ 1 + R := by
      rw [sub_eq_add_neg]
      refine (hnorm_add _ _).trans ?_
      rw [hnorm_neg]
      exact Nat.add_le_add hx (hR i)
    exact (sum_pderiv_le_of_subadditive hzero hadd _ j).trans (Nat.mul_le_mul hdeg hnorm)
  unfold jacobian
  have h := Matrix.det_weight_le hnorm_zero hnorm_one hnorm_add hnorm_mul hnorm_neg
    (Matrix.of (fun i j => pderiv j (X i ^ (d + 1) - r i)))
    (fun i j => by simpa only [Matrix.of_apply] using hentry i j)
  rwa [Fintype.card_fin] at h

/-- Bound the parameter coefficient norm of the Jacobian of the actual pure-power relations. -/
theorem parameterCoeffNorm_jacobian_le {n d R : ℕ}
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree ≤ d) (hR : ∀ i, ParameterCoeffNorm.norm (r i) ≤ R) :
    ParameterCoeffNorm.norm (jacobian (d + 1) r) ≤ n.factorial * ((d + 1) * (1 + R)) ^ n := by
  simpa only [sum_def, ParameterCoeffNorm.norm] using
    jacobian_weight_sum_le Polynomial.coeffNorm1_zero Polynomial.coeffNorm1_one.le
      Polynomial.coeffNorm1_add_le Polynomial.coeffNorm1_mul_le Polynomial.coeffNorm1_neg r hr
      (fun i => by simpa only [sum_def, ParameterCoeffNorm.norm] using hR i)

/-- Bound the coefficient weight of the trace of the $k$th power of multiplication by
$v$ in the pure-power quotient with relations $X_i^{d+1} - r_i$. Here $D$ is the
quotient dimension, $B$ bounds the residue numerator degree through $D$, and $A$
bounds the geometric growth of the positive power traces. -/
theorem multiplicationMatrix_trace_pow_weight_le {S : Type*} [CommRing S] {w : S → ℕ}
    (hzero : w 0 = 0) (hone : w 1 ≤ 1)
    (hadd : ∀ a b, w (a + b) ≤ w a + w b) (hmul : ∀ a b, w (a * b) ≤ w a * w b)
    (hneg : ∀ a, w (-a) = w a) {n d Ω V R : ℕ} (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (hR : ∀ i, (r i).coeff.sum (fun _ a => w a) ≤ R) (hR1 : 1 ≤ R)
    (v : MvPolynomial (Fin n) S) (hdeg : v.totalDegree ≤ Ω)
    (hV : v.coeff.sum (fun _ a => w a) ≤ V) (k : ℕ) (hk : 1 ≤ k) (hkD : k ≤ (d + 1) ^ n) :
    let D := (d + 1) ^ n
    let B := D * Ω + n * d
    let A := (B + 1) ^ n * (n.factorial * ((d + 1) * (1 + R)) ^ n) * R ^ B * V
    w (((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v) ^ k).trace) ≤ A ^ k := by
  let D := (d + 1) ^ n
  let B := D * Ω + n * d
  let J := n.factorial * ((d + 1) * (1 + R)) ^ n
  let C := (B + 1) ^ n * J * R ^ B
  let norm (p : MvPolynomial (Fin n) S) := p.coeff.sum (fun _ a => w a)
  change _ ≤ (C * V) ^ k
  rw [multiplicationMatrix_trace_pow d hd r hr v k]
  have hB : (v ^ k * jacobian (d + 1) r).totalDegree ≤ B :=
    (totalDegree_mul _ _).trans (Nat.add_le_add ((totalDegree_pow _ _).trans
      (Nat.mul_le_mul hkD hdeg)) (totalDegree_jacobian_le d r hr))
  have hnum : norm (v ^ k * jacobian (d + 1) r) ≤ V ^ k * J :=
    (sum_mul_le_of_submultiplicative hzero hadd hmul _ _).trans (Nat.mul_le_mul
      ((sum_pow_le_of_submultiplicative hzero hone hadd hmul v k).trans
        (Nat.pow_le_pow_left hV _))
      (jacobian_weight_sum_le hzero hone hadd hmul hneg r hr hR))
  calc
    _ ≤ (B + 1) ^ n * (norm (v ^ k * jacobian (d + 1) r) * R ^ B) :=
      residue_weight_le hzero hone hadd hmul (by omega) hR1 r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) hR _ hB
    _ ≤ (B + 1) ^ n * ((V ^ k * J) * R ^ B) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hnum)
    _ = C * V ^ k := by dsimp only [C]; ac_rfl
    _ ≤ (C * V) ^ k := by
      rw [mul_pow]
      exact Nat.mul_le_mul_right _ (Nat.le_pow (by omega))

private theorem sum_multiplicationMatrix_charpoly_le {S : Type*} [CommRing S] {w : S → ℕ}
    (hzero : w 0 = 0) (hone : w 1 ≤ 1)
    (hadd : ∀ a b, w (a + b) ≤ w a + w b) (hmul : ∀ a b, w (a * b) ≤ w a * w b)
    (hneg : ∀ a, w (-a) = w a) (hnsmul : ∀ (j : ℕ) a, w (j • a) = j * w a)
    {n d Ω V R : ℕ} (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S)
    (hr : ∀ i, (r i).totalDegree ≤ d) (hR : ∀ i, (r i).coeff.sum (fun _ a => w a) ≤ R)
    (hR1 : 1 ≤ R) (v : MvPolynomial (Fin n) S) (hdeg : v.totalDegree ≤ Ω)
    (hV : v.coeff.sum (fun _ a => w a) ≤ V) (hV1 : 1 ≤ V) :
    let D := (d + 1) ^ n
    let B := D * Ω + n * d
    let A := (B + 1) ^ n * (n.factorial * ((d + 1) * (1 + R)) ^ n) * R ^ B * V
    (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.sum (fun _ a => w a) ≤
      (D + 1) * A ^ D := by
  classical
  dsimp only
  let D := (d + 1) ^ n
  let B := D * Ω + n * d
  let J := n.factorial * ((d + 1) * (1 + R)) ^ n
  let C := (B + 1) ^ n * J * R ^ B
  change _ ≤ (D + 1) * (C * V) ^ D
  have hcard : Fintype.card (NormalIndex n (d + 1)) = D := by
    simp [NormalIndex, D]
  have hC : 1 ≤ C := by
    have hpos : 0 < C := by
      dsimp only [C, J]
      exact Nat.mul_pos (Nat.mul_pos (by positivity) (by positivity)) (by positivity)
    omega
  have hA := Nat.mul_le_mul hC hV1
  rw [show (D + 1) * (C * V) ^ D =
    (Fintype.card (NormalIndex n (d + 1)) + 1) * (C * V) ^
      Fintype.card (NormalIndex n (d + 1)) by rw [hcard]]
  refine Matrix.sum_charpoly_coeff_le_of_trace_pow hzero hone hadd hmul hneg hnsmul _
    (by simpa only [one_mul] using hA) ?_
  intro k hk hkD
  rw [hcard] at hkD
  exact multiplicationMatrix_trace_pow_weight_le hzero hone hadd hmul hneg
    hd r hr hR hR1 v hdeg hV k hk hkD

/-- Bound the bivariate coefficient norm of the actual quotient characteristic polynomial.
Here `D` is the quotient dimension, `B` bounds the residue numerator degrees through `D`,
and `A` bounds the geometric growth of the positive power traces. -/
theorem bivariateCoeffNorm1_multiplicationMatrix_charpoly_le {n d Ω V R : ℕ} (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree ≤ d) (hR : ∀ i, ParameterCoeffNorm.norm (r i) ≤ R)
    (hR1 : 1 ≤ R) (v : MvPolynomial (Fin n) (Polynomial ℤ)) (hdeg : v.totalDegree ≤ Ω)
    (hV : ParameterCoeffNorm.norm v ≤ V) (hV1 : 1 ≤ V) :
    let D := (d + 1) ^ n
    let B := D * Ω + n * d
    let A := (B + 1) ^ n * (n.factorial * ((d + 1) * (1 + R)) ^ n) * R ^ B * V
    (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.bivariateCoeffNorm1 ≤
      (D + 1) * A ^ D :=
  sum_multiplicationMatrix_charpoly_le Polynomial.coeffNorm1_zero Polynomial.coeffNorm1_one.le
    Polynomial.coeffNorm1_add_le Polynomial.coeffNorm1_mul_le Polynomial.coeffNorm1_neg
    Polynomial.coeffNorm1_nsmul hd r hr hR hR1 v hdeg hV hV1

/-- A binary norm budget for quotient characteristic polynomials, with multiplier degree
at most `Ω`, multiplier norm at most `2 ^ bv` and relation norms at most `2 ^ br`. -/
@[expose] def multiplicationMatrixCharpolyCoeffNormExponent (n ell Ω bv br : ℕ) : ℕ :=
  let D := ell ^ n
  let B := D * Ω + n * (ell - 1)
  (D + 1).size + ((B + 1).size * n + (n.size + ell.size + (br + 1)) * n + br * B + bv) * D

/-- Bound the sum of the characteristic coefficient weights by a power of two using
binary budgets for the relation and multiplier weights. The coefficient weight must
scale exactly under natural scalar multiplication for Newton's identity. -/
theorem sum_multiplicationMatrix_charpoly_le_pow_two {S : Type*} [CommRing S] {w : S → ℕ}
    (hzero : w 0 = 0) (hone : w 1 ≤ 1)
    (hadd : ∀ a b, w (a + b) ≤ w a + w b) (hmul : ∀ a b, w (a * b) ≤ w a * w b)
    (hneg : ∀ a, w (-a) = w a) (hnsmul : ∀ (j : ℕ) a, w (j • a) = j * w a)
    {n ell Ω bv br : ℕ} (hell : 2 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S)
    (hr : ∀ i, (r i).totalDegree < ell) (hR : ∀ i, (r i).coeff.sum (fun _ a => w a) ≤ 2 ^ br)
    (v : MvPolynomial (Fin n) S) (hdeg : v.totalDegree ≤ Ω)
    (hV : v.coeff.sum (fun _ a => w a) ≤ 2 ^ bv) :
    (multiplicationMatrix (by omega : 1 ≤ ell) r hr v).charpoly.sum (fun _ a => w a) ≤
      2 ^ multiplicationMatrixCharpolyCoeffNormExponent n ell Ω bv br := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ell ≠ 0)
  let D := (d + 1) ^ n
  let B := D * Ω + n * d
  let A := (B + 1) ^ n * (n.factorial * ((d + 1) * (1 + 2 ^ br)) ^ n) * (2 ^ br) ^ B * 2 ^ bv
  have hq : _ ≤ (D + 1) * A ^ D :=
    sum_multiplicationMatrix_charpoly_le hzero hone hadd hmul hneg hnsmul (by omega) r
      (fun i => Nat.le_of_lt_succ (hr i)) hR Nat.one_le_two_pow v hdeg hV Nat.one_le_two_pow
  have hscale : (d + 1) * (1 + 2 ^ br) ≤ 2 ^ ((d + 1).size + (br + 1)) := by
    rw [pow_add 2 (d + 1).size, pow_succ (2 : ℕ) br]
    exact Nat.mul_le_mul (Nat.lt_size_self _).le (by have := Nat.one_le_two_pow (n := br); omega)
  have hJ : n.factorial * ((d + 1) * (1 + 2 ^ br)) ^ n ≤
      2 ^ ((n.size + (d + 1).size + (br + 1)) * n) := by
    rw [Nat.add_assoc, pow_mul, pow_add 2 n.size, mul_pow (2 ^ n.size)]
    exact Nat.mul_le_mul (n.factorial_le_pow.trans (Nat.pow_le_pow_left (Nat.lt_size_self _).le _))
      (Nat.pow_le_pow_left hscale _)
  have hA : A ≤ 2 ^ ((B + 1).size * n + (n.size + (d + 1).size + (br + 1)) * n +
      br * B + bv) := by
    dsimp only [A]
    conv_rhs =>
      rw [pow_add 2 _ bv, pow_add 2 _ (br * B),
        pow_add 2 ((B + 1).size * n), pow_mul 2 (B + 1).size, pow_mul 2 br B]
    gcongr; exact (Nat.lt_size_self _).le
  refine hq.trans ((Nat.mul_le_mul (Nat.lt_size_self _).le (Nat.pow_le_pow_left hA _)).trans_eq ?_)
  rw [← pow_mul, ← pow_add]
  simp only [multiplicationMatrixCharpolyCoeffNormExponent, Nat.succ_sub_one]
  rfl

/-- Bound the bivariate norm of a quotient characteristic polynomial by a power of two
using the binary budgets of the input norms. -/
theorem bivariateCoeffNorm1_multiplicationMatrix_charpoly_le_pow_two
    {n ell Ω bv br : ℕ} (hell : 2 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree < ell) (hR : ∀ i, ParameterCoeffNorm.norm (r i) ≤ 2 ^ br)
    (v : MvPolynomial (Fin n) (Polynomial ℤ)) (hdeg : v.totalDegree ≤ Ω)
    (hV : ParameterCoeffNorm.norm v ≤ 2 ^ bv) :
    (multiplicationMatrix (by omega : 1 ≤ ell) r hr v).charpoly.bivariateCoeffNorm1 ≤
      2 ^ multiplicationMatrixCharpolyCoeffNormExponent n ell Ω bv br :=
  sum_multiplicationMatrix_charpoly_le_pow_two
    Polynomial.coeffNorm1_zero Polynomial.coeffNorm1_one.le Polynomial.coeffNorm1_add_le
    Polynomial.coeffNorm1_mul_le Polynomial.coeffNorm1_neg Polynomial.coeffNorm1_nsmul
    hell r hr hR v hdeg hV

/-- Bound the integer determinant of multiplication in a pure-power quotient by the
characteristic polynomial norm budget. Embed the inputs as constant parameter polynomials
and use the degree-zero characteristic coefficient. -/
theorem natAbs_multiplicationMatrix_det_le_pow_two {n ell Ω bv br : ℕ} (hell : 2 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) ℤ)
    (hr : ∀ i, (r i).totalDegree < ell) (hR : ∀ i, (r i).coeffNorm1 ≤ 2 ^ br)
    (v : MvPolynomial (Fin n) ℤ) (hdeg : v.totalDegree ≤ Ω) (hV : v.coeffNorm1 ≤ 2 ^ bv) :
    (multiplicationMatrix (by omega : 1 ≤ ell) r hr v).det.natAbs ≤
      2 ^ multiplicationMatrixCharpolyCoeffNormExponent n ell Ω bv br := by
  let M := multiplicationMatrix (by omega : 1 ≤ ell) r hr v
  have h := bivariateCoeffNorm1_multiplicationMatrix_charpoly_le_pow_two hell
    (fun i => (r i).map Polynomial.C)
    (fun i => (totalDegree_map_le Polynomial.C _).trans_lt (hr i))
    (fun i => by simpa only [ParameterCoeffNorm.map_C] using hR i)
    (v.map Polynomial.C) ((totalDegree_map_le _ _).trans hdeg)
    (by simpa only [ParameterCoeffNorm.map_C] using hV)
  have hmap : (M.charpoly.map Polynomial.C).bivariateCoeffNorm1 ≤
      2 ^ multiplicationMatrixCharpolyCoeffNormExponent n ell Ω bv br := by
    dsimp only [M]
    rw [← Matrix.charpoly_map, multiplicationMatrix_map]
    exact h
  have hc := (Polynomial.coeffNorm1_coeff_le_bivariateCoeffNorm1 (M.charpoly.map Polynomial.C)
    0).trans hmap
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simpa only [Polynomial.coeff_map, Polynomial.coeffNorm1_C, Int.natAbs_mul, Int.natAbs_pow,
    Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul, M] using hc

end MvPolynomial.PurePower
