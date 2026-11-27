/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, critical equations in pure-power quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValuePolynomial
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateKronecker
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap

/-!
# Nonvanishing of the relative critical-value section

Fixing the parameters leaves a bivariate polynomial in the penalty and the critical value.
It is monic in the critical value, with degree `ell ^ n` over a nontrivial ring. Substituting
the critical value to the power `ell ^ n + 1` for the penalty preserves the coefficient
at degree `ell ^ n`.
The coefficient identity holds over every commutative ring, so the univariate polynomial
is nonzero for every parameter choice over a nontrivial ring.

Adapted from `RelativeCriticalMinimum`, `MonicPowerSubstitution`, and
`RelativeSectionNonvanishing` in lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.CriticalSystem

variable {T κ : Type*} [CommRing T] {n m ell : ℕ}

/-- Fix the parameter coordinates, leaving the penalty as the inner variable and the critical
value as the outer variable. -/
noncomputable def relativeValueBivariate (hell : 1 ≤ ell) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ ell) (x : κ → T) : Polynomial (Polynomial T) :=
  (relativeValuePolynomial hell F hF).map
    (eval₂Hom (Int.castRingHom (Polynomial T))
      (fun i : Option κ => i.elim Polynomial.X (fun j => Polynomial.C (x j))))

/-- Each fixed parameter fiber is monic in the critical value. -/
theorem relativeValueBivariate_monic (hell : 1 ≤ ell) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ ell) (x : κ → T) : (relativeValueBivariate hell F hF x).Monic :=
  (valuePolynomial_monic hell _ _ _ _).map _

/-- The critical-value degree is the dimension of the witness quotient. -/
theorem relativeValueBivariate_natDegree [Nontrivial T] (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n ⊕ κ) ℤ) (hF : F.totalDegree ≤ ell) (x : κ → T) :
    (relativeValueBivariate hell F hF x).natDegree = ell ^ n := by
  rw [relativeValueBivariate, relativeValuePolynomial]
  rw [(valuePolynomial_monic hell _ _ _ _).natDegree_map _]
  exact valuePolynomial_natDegree hell _ _ _ _

/-- Evaluating the penalty in the bivariate fiber gives the polynomial of the specialized
witness system. -/
theorem relativeValueBivariate_map (hell : 1 ≤ ell) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ ell) (u : T) (x : κ → T) :
    (relativeValueBivariate hell F hF x).map (Polynomial.evalRingHom u) =
      valuePolynomial hell (fun _ => 0) u
        ((sumRingEquiv ℤ (Fin n) κ F).map (eval₂Hom (Int.castRingHom T) x))
        ((totalDegree_map_le _ _).trans ((totalDegree_sumRingEquiv_le F).trans hF)) := by
  rw [← relativeValuePolynomial_map hell F hF u x]
  rw [relativeValueBivariate, Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    cases i <;> simp

/-- Read the section as a univariate polynomial in the critical value by evaluating its
parameter coefficients at the chosen fiber. -/
noncomputable def specializedRelativeValueSection (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin (n + m)) ℤ) (hF : F.totalDegree ≤ ell) (x : Fin m → T) :
    Polynomial T :=
  (finSuccEquiv ℤ m (finiteRelativeValueSection hell F hF)).map
    (eval₂Hom (Int.castRingHom T) x)

/-- Each coefficient of the specialized section is the evaluation of its parameter polynomial. -/
theorem coeff_specializedRelativeValueSection_eq_eval₂ (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin (n + m)) ℤ) (hF : F.totalDegree ≤ ell) (x : Fin m → T) (i : ℕ) :
    (specializedRelativeValueSection hell F hF x).coeff i =
      eval₂ (Int.castRingHom T) x
        ((finSuccEquiv ℤ m (finiteRelativeValueSection hell F hF)).coeff i) :=
  Polynomial.coeff_map _ _

/-- The specialized degree is bounded by the total degree of the unspecialized section. -/
theorem natDegree_specializedRelativeValueSection_le (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin (n + m)) ℤ) (hF : F.totalDegree ≤ ell) (x : Fin m → T) :
    (specializedRelativeValueSection hell F hF x).natDegree ≤
      (finiteRelativeValueSection hell F hF).totalDegree := by
  rw [specializedRelativeValueSection]
  exact Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv _).le.trans
    (degreeOf_le_totalDegree _ _))

/-- The univariate fiber evaluates to the fixed-power section at the supplied critical value. -/
theorem eval_specializedRelativeValueSection (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin (n + m)) ℤ) (hF : F.totalDegree ≤ ell) (x : Fin m → T) (y : T) :
    (specializedRelativeValueSection hell F hF x).eval y =
      eval₂ (Int.castRingHom T) (Fin.cons y x) (finiteRelativeValueSection hell F hF) := by
  let φ := Int.castRingHom T
  have h : (Polynomial.eval₂RingHom (eval₂Hom φ x) y).comp (finSuccEquiv ℤ m).toRingHom =
      eval₂Hom φ (Fin.cons y x) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [φ]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [finSuccEquiv_X_zero]
      · simp [finSuccEquiv_X_succ]
  rw [specializedRelativeValueSection, Polynomial.eval_map]
  exact DFunLike.congr_fun h (finiteRelativeValueSection hell F hF)

/-- Evaluate the section by substituting the prescribed power of the critical value for the
penalty in the bivariate polynomial. -/
theorem eval_specializedRelativeValueSection_eq_bivariate (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin (n + m)) ℤ) (hF : F.totalDegree ≤ ell) (x : Fin m → T) (y : T) :
    (specializedRelativeValueSection hell F hF x).eval y =
      (relativeValueBivariate hell (rename finSumFinEquiv.symm F)
        ((totalDegree_rename_le _ _).trans hF) x).eval₂
          (Polynomial.evalRingHom (y ^ (ell ^ n + 1))) y := by
  rw [eval_specializedRelativeValueSection, eval₂_finiteRelativeValueSection,
    ← Polynomial.eval_map, relativeValueBivariate_map]

private theorem specializedRelativeValueSection_eq_eval [IsDomain T] [Infinite T] (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin (n + m)) ℤ) (hF : F.totalDegree ≤ ell) (x : Fin m → T) :
    specializedRelativeValueSection hell F hF x =
      (Polynomial.Bivariate.swap (relativeValueBivariate hell (rename finSumFinEquiv.symm F)
        ((totalDegree_rename_le _ _).trans hF) x)).eval (Polynomial.X ^ (ell ^ n + 1)) := by
  apply Polynomial.funext
  intro y
  rw [eval_specializedRelativeValueSection_eq_bivariate]
  symm
  conv_lhs => rw [← Polynomial.coe_aeval_eq_eval]
  rw [Polynomial.Bivariate.aeval_eval_X_pow,
    Polynomial.Bivariate.aevalAeval_swap, Polynomial.coe_aevalAeval_eq_evalEval,
    ← Polynomial.map_evalRingHom_eval, Polynomial.eval_map]

private theorem coeff_specializedRelativeValueSection_of_infinite [IsDomain T] [Infinite T]
    (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin (n + m)) ℤ) (hF : F.totalDegree ≤ ell) (x : Fin m → T) :
    (specializedRelativeValueSection hell F hF x).coeff (ell ^ n) = 1 := by
  let G := rename finSumFinEquiv.symm F
  have hG : G.totalDegree ≤ ell := (totalDegree_rename_le _ _).trans hF
  let Q := relativeValueBivariate hell G hG x
  have hdeg : Q.natDegree = ell ^ n := relativeValueBivariate_natDegree hell G hG x
  have hmonic : Q.Monic := relativeValueBivariate_monic hell G hG x
  have hradix : (Polynomial.Bivariate.swap (Polynomial.Bivariate.swap Q)).natDegree <
      ell ^ n + 1 := by
    rw [Polynomial.Bivariate.swap_swap_apply, hdeg]
    exact Nat.lt_succ_self _
  rw [specializedRelativeValueSection_eq_eval]
  change ((Polynomial.Bivariate.swap Q).eval (Polynomial.X ^ (ell ^ n + 1))).coeff (ell ^ n) = 1
  calc
    _ = (Q.coeff (ell ^ n)).coeff 0 := by
      simpa only [Nat.mul_zero, Nat.add_zero, Polynomial.Bivariate.coeff_coeff_swap] using
        Polynomial.Bivariate.coeff_eval_X_pow _ hradix (ell ^ n) 0 (Nat.lt_succ_self _)
    _ = 1 := by rw [← hdeg, hmonic.coeff_natDegree, AddMonoidAlgebra.coeff_one_zero]

/-- The degree-`ell ^ n` coefficient is one in every parameter fiber. It comes from the
monic critical-value term. Terms involving a positive penalty power have larger degree. -/
theorem coeff_specializedRelativeValueSection (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin (n + m)) ℤ) (hF : F.totalDegree ≤ ell) (x : Fin m → T) :
    (specializedRelativeValueSection hell F hF x).coeff (ell ^ n) = 1 := by
  -- Keep the parameters as indeterminates to obtain the identity before specialization.
  have h := coeff_specializedRelativeValueSection_of_infinite hell F hF
    (X : Fin m → MvPolynomial (Fin m) ℤ)
  have hcast : Int.castRingHom (MvPolynomial (Fin m) ℤ) =
      algebraMap ℤ (MvPolynomial (Fin m) ℤ) := Subsingleton.elim _ _
  simp only [specializedRelativeValueSection, Polynomial.coeff_map] at h ⊢
  rw [hcast, ← aeval_eq_eval₂Hom, aeval_X_left_apply] at h
  rw [h, map_one]

/-- Fixing any parameter point leaves a nonzero critical-value section. -/
theorem specializedRelativeValueSection_ne_zero [Nontrivial T] (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin (n + m)) ℤ) (hF : F.totalDegree ≤ ell) (x : Fin m → T) :
    specializedRelativeValueSection hell F hF x ≠ 0 := by
  intro hz
  have h := coeff_specializedRelativeValueSection hell F hF x
  rw [hz, Polynomial.coeff_zero] at h
  exact zero_ne_one h

end MvPolynomial.CriticalSystem
