/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, pure-power polynomial quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.ParameterDegree
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValuePolynomial
import CslibFrontier.Foundations.Data.MvPolynomial.LowestComponent
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.ParameterDegree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Parameter degrees in the critical-value characteristic polynomial

The degrees in the coefficient parameter are bounded using the finite residue formula for
the power traces. Only residue indices whose sum is at most the spatial degree of the
numerator can contribute. For a positive power trace, the Jacobian's fixed degree cost can
be absorbed into a bound linear in the power. Newton's identity then gives a linear bound
in the reversed characteristic coefficient index. Scaling the retained parameters by a
fresh indeterminate transfers the same bound to their multivariate total degree.

Adapted from `QuotientParameterDegree`, `SeparatedPotentialDegree`, and
`ParametricCriticalBounds`, `MultivariateQuotientDegree`, and `RelativeCharacteristicBounds`
in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.PurePower

open scoped BigOperators

variable {n : ℕ} {R : Type*} [CommRing R]

private theorem natDegree_residue_le {ell B H K : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial R))
    (hr : ∀ i, (r i).totalDegree < ell) (hparam : ∀ i, HasParameterDegree (r i) H)
    (v : MvPolynomial (Fin n) (Polynomial R)) (hv : HasParameterDegree v K)
    (hB : v.totalDegree ≤ B) : (residue ell r v).natDegree ≤ K + B * H := by
  classical
  rw [residue_eq_truncated hell r hr v hB]
  change (∑ j ∈ indices n B, term ell r v j).natDegree ≤ _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  by_cases hj : (∑ i, j i) ≤ B
  · have hprod := HasParameterDegree.prod Finset.univ (fun i => r i ^ j i)
      (fun i => j i * H) (fun i _ => (hparam i).pow (j i))
    refine ((hv.mul hprod) (target ell j)).trans ?_
    rw [← Finset.sum_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right H hj) K
  · rw [term_eq_zero_of_degree_lt hell r hr v j (by omega), Polynomial.natDegree_zero]
    exact Nat.zero_le _

private theorem jacobian_hasParameterDegree {ell H : ℕ}
    (r : Fin n → MvPolynomial (Fin n) (Polynomial R))
    (hr : ∀ i, HasParameterDegree (r i) H) :
    HasParameterDegree (jacobian ell r) (n * H) := by
  classical
  have he (i j : Fin n) :
      HasParameterDegree (pderiv j (X i ^ ell - r i)) H := by
    have hx := ((HasParameterDegree.X (R := R) i).pow ell).mono
      (show ell * 0 ≤ H by simp)
    simpa only [max_self] using (hx.sub (hr i)).pderiv j
  unfold jacobian
  rw [Matrix.det_apply]
  apply HasParameterDegree.sum
  intro σ _
  have hp := HasParameterDegree.prod Finset.univ
    (fun i => pderiv i (X (σ i) ^ ell - r (σ i))) (fun _ => H)
    (fun i _ => he (σ i) i)
  have hp' : HasParameterDegree (∏ i, pderiv i (X (σ i) ^ ell - r (σ i))) (n * H) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      using hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa only [Matrix.of_apply, hs, one_smul] using hp'
  · simpa only [Matrix.of_apply, hs, Units.neg_smul, one_smul] using hp'.neg

/-- Each characteristic coefficient of a pure-power quotient multiplication operator has
parameter degree at most its reversed index times a bound from the lower relations and
the multiplier. The input bounds `H` and `K` refer to degrees in the parameter, while
`d` and `Ω` bound spatial total degrees. -/
theorem natDegree_multiplicationMatrix_charpoly_coeff_le [IsDomain R] [CharZero R]
    {d Ω H K : ℕ} (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial R)) (hr : ∀ i, (r i).totalDegree ≤ d)
    (hparam : ∀ i, HasParameterDegree (r i) H) (v : MvPolynomial (Fin n) (Polynomial R))
    (hdeg : v.totalDegree ≤ Ω) (hv : HasParameterDegree v K) (k : ℕ) :
    ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.coeff k).natDegree ≤
      ((d + 1) ^ n - k) * (K + (Ω + n * (d + 1)) * H) := by
  classical
  let M := multiplicationMatrix (by omega : 1 ≤ d + 1) r
    (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v
  let A := K + (Ω + n * (d + 1)) * H
  have ht (j : ℕ) (hj : 1 ≤ j) : ((M ^ j).trace).natDegree ≤ j * A := by
    rw [multiplicationMatrix_trace_pow d hd r hr v j]
    have hnum : (v ^ j * jacobian (d + 1) r).totalDegree ≤ j * Ω + n * d :=
      (totalDegree_mul _ _).trans (Nat.add_le_add ((totalDegree_pow _ _).trans
        (Nat.mul_le_mul_left j hdeg)) (totalDegree_jacobian_le d r hr))
    refine (natDegree_residue_le (by omega) r (fun i => (hr i).trans_lt (Nat.lt_succ_self d))
      hparam _ ((hv.pow j).mul (jacobian_hasParameterDegree r hparam)) hnum).trans ?_
    calc
      j * K + n * H + (j * Ω + n * d) * H = j * (K + Ω * H) + n * (d + 1) * H := by ring
      _ ≤ j * (K + Ω * H) + j * (n * (d + 1) * H) :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hj) _
      _ = j * A := by dsimp only [A]; ring
  simpa [NormalIndex, A] using Matrix.natDegree_charpoly_coeff_le_of_trace_pow M A
    (fun j hj _ => ht j hj) k

/-- For multivariate coefficient parameters, the same pure-power quotient bound
controls total degree in those parameters. Scaling the parameters turns total degree
into a univariate degree while leaving the witness degree bounds valid. -/
theorem totalDegree_multiplicationMatrix_charpoly_coeff_le {τ : Type*}
    [IsDomain R] [CharZero R] {d Ω H K : ℕ} (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) (MvPolynomial τ R))
    (hr : ∀ i, (r i).totalDegree ≤ d) (hparam : ∀ i s, ((r i).coeff s).totalDegree ≤ H)
    (v : MvPolynomial (Fin n) (MvPolynomial τ R)) (hdeg : v.totalDegree ≤ Ω)
    (hv : ∀ s, (v.coeff s).totalDegree ≤ K) (k : ℕ) :
    ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.coeff k).totalDegree ≤
      ((d + 1) ^ n - k) * (K + (Ω + n * (d + 1)) * H) := by
  let φ : MvPolynomial τ R →+* Polynomial (MvPolynomial τ R) :=
    (aeval fun i => Polynomial.X * Polynomial.C (X i)).toRingHom
  have hscaled (p : MvPolynomial (Fin n) (MvPolynomial τ R)) (b : ℕ)
      (hp : ∀ s, (p.coeff s).totalDegree ≤ b) : HasParameterDegree (p.map φ) b := by
    intro s
    rw [coeff_map]
    exact (natDegree_aeval_scale_X (p.coeff s)).trans_le (hp s)
  let r' (i : Fin n) := (r i).map φ
  let v' := v.map φ
  have hr' (i : Fin n) : (r' i).totalDegree ≤ d :=
    (totalDegree_map_le φ (r i)).trans (hr i)
  have hdegree := natDegree_multiplicationMatrix_charpoly_coeff_le hd r' hr'
    (fun i => hscaled (r i) H (hparam i)) v' ((totalDegree_map_le φ v).trans hdeg)
    (hscaled v K hv) k
  have hchar :
      (multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.map φ =
      (multiplicationMatrix (by omega : 1 ≤ d + 1) r'
        (fun i => (hr' i).trans_lt (Nat.lt_succ_self d)) v').charpoly := by
    rw [← Matrix.charpoly_map, multiplicationMatrix_map]
  rw [← hchar, Polynomial.coeff_map] at hdegree
  exact (natDegree_aeval_scale_X _).symm.trans_le hdegree

end MvPolynomial.PurePower

namespace MvPolynomial.CriticalSystem

open PurePower

/-- Critical lower relations with constant centers are affine in the deformation parameter. -/
theorem criticalLower_hasParameterDegree {n : ℕ} (ell : ℕ) (a : Fin n → ℤ)
    (F : MvPolynomial (Fin n) ℤ) (i : Fin n) :
    HasParameterDegree
      (criticalLower ell (fun j => Polynomial.C (a j)) Polynomial.X (F.map Polynomial.C) i) 1 := by
  have hc := HasParameterDegree.C (ι := Fin n) (Polynomial.C (a i) ^ ell) (h := 0) (by
    rw [← map_pow, Polynomial.natDegree_C])
  have hx := HasParameterDegree.C (ι := Fin n) (Polynomial.X : Polynomial ℤ)
    (h := 1) Polynomial.natDegree_X.le
  simpa only [criticalLower, Nat.add_zero, Nat.zero_max] using
    hc.sub (hx.mul ((HasParameterDegree.map_C F).pderiv i))

/-- The symbolic critical relations and objective are affine in the coefficient parameter. -/
theorem criticalSystem_hasParameterDegree {n : ℕ} (ell : ℕ)
    (F : MvPolynomial (Fin n) ℤ) :
    let a (i : Fin n) := Polynomial.C (separatedCenters ell i : ℤ)
    let G := F.map Polynomial.C
    (∀ i, HasParameterDegree (criticalLower ell a Polynomial.X G i) 1) ∧
      HasParameterDegree (deformedPolynomial ell a Polynomial.X G) 1 := by
  intro a G
  have hFparam : HasParameterDegree G 0 := HasParameterDegree.map_C F
  constructor
  · exact criticalLower_hasParameterDegree ell (fun i => (separatedCenters ell i : ℤ)) F
  · have hp := HasParameterDegree.map_C
      (potentialPolynomial ell (fun i : Fin n => (separatedCenters ell i : ℤ)))
    rw [potentialPolynomial_map] at hp
    have hx := HasParameterDegree.C (ι := Fin n)
      (((ell + 1 : ℕ) : Polynomial ℤ) * Polynomial.X) (h := 1) (by
        rw [← Polynomial.C_eq_natCast]
        exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X.le)
    simpa only [deformedPolynomial, Nat.add_zero, Nat.zero_max] using hp.add (hx.mul hFparam)

/-- A symbolic critical-value coefficient has parameter degree at most
`(ell ^ n - k) * (ell + 2 + n * ell)`. This bounds the powers of the parameter needed
to evaluate that coefficient. -/
theorem natDegree_parametricValuePolynomial_coeff_le {n ell : ℕ} (hell : 2 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (k : ℕ) :
    ((parametricValuePolynomial (by omega : 1 ≤ ell) F hF).coeff k).natDegree ≤
      (ell ^ n - k) * (ell + 2 + n * ell) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ell ≠ 0)
  let a (i : Fin n) := Polynomial.C (separatedCenters (d + 1) i : ℤ)
  let G := F.map Polynomial.C
  let r := criticalLower (d + 1) a Polynomial.X G
  let v := deformedPolynomial (d + 1) a Polynomial.X G
  have hG : G.totalDegree ≤ d + 1 := (totalDegree_map_le Polynomial.C F).trans hF
  have hr (i : Fin n) : (r i).totalDegree ≤ d :=
    Nat.le_of_lt_succ (criticalLower_degree _ (by omega) a Polynomial.X G hG i)
  obtain ⟨hrparam, hvparam⟩ := criticalSystem_hasParameterDegree (d + 1) F
  calc
    _ ≤ ((d + 1) ^ n - k) * (1 + ((d + 1 + 1) + n * (d + 1)) * 1) :=
      natDegree_multiplicationMatrix_charpoly_coeff_le (by omega) r hr hrparam v
        (totalDegree_deformedPolynomial_le _ a Polynomial.X G (hG.trans (Nat.le_succ _)))
        hvparam k
    _ = _ := by
      congr 1
      change 1 + ((d + 1 + 1) + n * (d + 1)) * 1 = (d + 1) + 2 + n * (d + 1)
      ring

/-- The total degree of a relative critical-value coefficient in the retained parameters
and penalty variable is bounded by a factor linear in its reversed characteristic index.
The witness relation exponent is `ell`, and the source has total degree at most `ell`. -/
theorem totalDegree_relativeValuePolynomial_coeff_le {n ell : ℕ} {κ : Type*} (hell : 2 ≤ ell)
    (F : MvPolynomial (Fin n ⊕ κ) ℤ) (hF : F.totalDegree ≤ ell) (k : ℕ) :
    ((relativeValuePolynomial (by omega : 1 ≤ ell) F hF).coeff k).totalDegree ≤
      (ell ^ n - k) * ((ell + 2 + n * ell) * (F.totalDegree + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ell ≠ 0)
  let G := relativeSource F
  let a : Fin n → MvPolynomial (Option κ) ℤ := fun _ => 0
  let u : MvPolynomial (Option κ) ℤ := X none
  let r := criticalLower (d + 1) a u G
  let v := deformedPolynomial (d + 1) a u G
  have hG : G.totalDegree ≤ d + 1 := (totalDegree_relativeSource_le F).trans hF
  have hr (i : Fin n) : (r i).totalDegree ≤ d :=
    Nat.le_of_lt_succ (criticalLower_degree _ (by omega) a u G hG i)
  have hrparam (i : Fin n) (s : Fin n →₀ ℕ) :
      ((r i).coeff s).totalDegree ≤ F.totalDegree + 1 :=
    totalDegree_coeff_relativeCriticalLower_le (ell := d + 1) (by omega) F i s
  have hvparam (s : Fin n →₀ ℕ) : (v.coeff s).totalDegree ≤ F.totalDegree + 1 :=
    totalDegree_coeff_relativeDeformedPolynomial_le (d + 1) F s
  calc
    _ ≤ ((d + 1) ^ n - k) *
        (F.totalDegree + 1 + (d + 1 + 1 + n * (d + 1)) * (F.totalDegree + 1)) :=
      totalDegree_multiplicationMatrix_charpoly_coeff_le (by omega) r hr hrparam v
        (totalDegree_deformedPolynomial_le _ a u G (hG.trans (Nat.le_succ _))) hvparam k
    _ = _ := by
      simp only [Nat.succ_eq_add_one]
      ring

end MvPolynomial.CriticalSystem
