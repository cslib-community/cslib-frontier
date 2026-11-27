/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Polynomials in the last variable

The last-variable equivalence represents a multivariate polynomial as a
univariate polynomial with multivariate coefficients in the prefix variables.
Evaluating the univariate variable specializes the last coordinate. Degree in
the last variable becomes univariate degree, and prefix-degree bounds become
bounds on every coefficient. The underlying option equivalence also gives a
total-degree bound when the outer variable is joined to the coefficient variables.

## Main definitions

* `MvPolynomial.lastVariableEquiv` isolates the last variable.
* `MvPolynomial.specializeLast` assigns a scalar to the last variable.

## Main results

* `MvPolynomial.eval_lastVariableEquiv` identifies evaluation with substitution.
* `MvPolynomial.natDegree_lastVariableEquiv` computes the resulting univariate degree.
* `MvPolynomial.degreeOf_castSucc_le_iff` characterizes bounds on the prefix variables.
-/

public section

namespace MvPolynomial

open Finset

variable {R : Type*} {m : ℕ} [CommSemiring R]

/-- Bound the total degree after bringing the univariate variable into the index type.
The degree of each coefficient contributes together with its own outer exponent. -/
theorem totalDegree_optionEquivLeft_symm_le {κ : Type*}
    (p : Polynomial (MvPolynomial κ R)) {D : ℕ}
    (h : ∀ k ∈ p.support, (p.coeff k).totalDegree + k ≤ D) :
    ((optionEquivLeft R κ).symm p).totalDegree ≤ D := by
  rw [totalDegree, Finset.sup_le_iff]
  intro m hm
  have hcoeff := optionEquivLeft_coeff_some_coeff_none R κ m ((optionEquivLeft R κ).symm p)
  rw [AlgEquiv.apply_symm_apply] at hcoeff
  have hm' : m.some ∈ (p.coeff (m none)).support := by
    apply mem_support_iff.mpr
    rw [hcoeff]
    exact mem_support_iff.mp hm
  have hk : m none ∈ p.support := Polynomial.mem_support_iff.mpr fun hz => by
    rw [hz, support_zero] at hm'
    exact Finset.notMem_empty _ hm'
  rw [Finsupp.sum_option_index _ (fun _ a => a) (fun _ => rfl) (fun _ _ _ => rfl), add_comm]
  exact (Nat.add_le_add_right (le_totalDegree hm') _).trans (h _ hk)

/-- Isolate the last variable of a multivariate polynomial. -/
noncomputable def lastVariableEquiv (R : Type*) [CommSemiring R] (m : ℕ) :
    MvPolynomial (Fin (m + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin m) R) :=
  (renameEquiv R finSuccEquivLast).trans (optionEquivLeft R (Fin m))

@[simp] theorem lastVariableEquiv_X_last :
    lastVariableEquiv R m (X (Fin.last m)) = Polynomial.X := by
  simp [lastVariableEquiv, finSuccEquivLast_last]

@[simp] theorem lastVariableEquiv_X_castSucc (i : Fin m) :
    lastVariableEquiv R m (X i.castSucc) = Polynomial.C (X i) := by
  simp [lastVariableEquiv, finSuccEquivLast_castSucc]

@[simp] theorem lastVariableEquiv_C (a : R) :
    lastVariableEquiv R m (C a) = Polynomial.C (C a) := by
  simpa only [Polynomial.algebraMap_apply, algebraMap_eq] using
    (lastVariableEquiv R m).commutes a

/-- Evaluating the last variable at a polynomial substitutes that polynomial
for the last variable and leaves the prefix variables fixed. -/
theorem eval_lastVariableEquiv (g : MvPolynomial (Fin m) R)
    (p : MvPolynomial (Fin (m + 1)) R) :
    (lastVariableEquiv R m p).eval g = aeval (Fin.lastCases g X : Fin (m + 1) → _) p := by
  have h : (Polynomial.evalRingHom g).comp (lastVariableEquiv R m).toRingHom =
      (aeval (Fin.lastCases g X : Fin (m + 1) → MvPolynomial (Fin m) R)).toRingHom :=
    ringHom_ext (fun a => by simp) fun i => by
      refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
  exact RingHom.congr_fun h p

/-- Substitute a scalar for the last variable, keeping all the preceding variables. -/
noncomputable def specializeLast (x : R) :
    MvPolynomial (Fin (m + 1)) R →+* MvPolynomial (Fin m) R :=
  (Polynomial.evalRingHom (C x)).comp (lastVariableEquiv R m).toRingHom

/-- Specializing the last variable is univariate evaluation at the corresponding constant. -/
theorem specializeLast_apply (x : R) (p : MvPolynomial (Fin (m + 1)) R) :
    specializeLast x p = (lastVariableEquiv R m p).eval (C x) := by
  unfold specializeLast
  rfl

@[simp] theorem specializeLast_X_last (x : R) :
    specializeLast x (X (Fin.last m)) = C x := by
  rw [specializeLast_apply, lastVariableEquiv_X_last, Polynomial.eval_X]

@[simp] theorem specializeLast_X_castSucc (x : R) (i : Fin m) :
    specializeLast x (X i.castSucc) = X i := by
  rw [specializeLast_apply, lastVariableEquiv_X_castSucc, Polynomial.eval_C]

/-- Specialization corresponds to evaluating on the last-coordinate slice. -/
theorem eval_specializeLast (x : R) (u : Fin m → R) (p : MvPolynomial (Fin (m + 1)) R) :
    eval u (specializeLast x p) = eval (Fin.snoc u x) p := by
  rw [specializeLast_apply, eval_lastVariableEquiv]
  have h : (eval u).comp
      (aeval (Fin.lastCases (C x) X : Fin (m + 1) → MvPolynomial (Fin m) R)).toRingHom =
      eval (Fin.snoc u x) :=
    ringHom_ext (fun r => by simp) fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  exact RingHom.congr_fun h p

/-- Retain the last variable and evaluate all preceding variables at `u`. -/
noncomputable def evalPrefix (u : Fin m → R) (p : MvPolynomial (Fin (m + 1)) R) : Polynomial R :=
  (lastVariableEquiv R m p).map (eval u)

theorem eval_evalPrefix (u : Fin m → R) (p : MvPolynomial (Fin (m + 1)) R) (x : R) :
    (evalPrefix u p).eval x = eval u (specializeLast x p) := by
  rw [evalPrefix, specializeLast_apply, Polynomial.eval_map, ← Polynomial.eval₂_id,
    Polynomial.hom_eval₂, RingHom.comp_id, eval_C]

theorem natDegree_lastVariableEquiv (p : MvPolynomial (Fin (m + 1)) R) :
    (lastVariableEquiv R m p).natDegree = p.degreeOf (Fin.last m) := by
  unfold lastVariableEquiv
  change (optionEquivLeft R _ (rename finSuccEquivLast p)).natDegree = _
  rw [natDegree_optionEquivLeft, ← finSuccEquivLast_last,
    degreeOf_rename_of_injective finSuccEquivLast.injective]

/-- Evaluating the prefix does not increase the degree in the remaining variable. -/
theorem natDegree_evalPrefix_le (u : Fin m → R) (p : MvPolynomial (Fin (m + 1)) R) :
    (evalPrefix u p).natDegree ≤ p.degreeOf (Fin.last m) :=
  Polynomial.natDegree_map_le.trans_eq (natDegree_lastVariableEquiv p)

/-- Evaluate all variables except the selected one, retaining it as a univariate variable. -/
noncomputable def evalCoordinate (u : Fin (m + 1) → R) (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) R) : Polynomial R :=
  let e := Equiv.swap i (Fin.last m)
  evalPrefix (Fin.init (u ∘ e)) (rename e p)

/-- Evaluating the coordinate restriction is the same as updating that coordinate. -/
theorem eval_evalCoordinate (u : Fin (m + 1) → R) (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) R) (t : R) :
    (evalCoordinate u i p).eval t = eval (Function.update u i t) p := by
  let e := Equiv.swap i (Fin.last m)
  have he : e i = Fin.last m := Equiv.swap_apply_left _ _
  have hsnoc : Fin.snoc (Fin.init (u ∘ e)) t = Function.update (u ∘ e) (Fin.last m) t := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.castSucc_ne_last, Fin.init]
  change (evalPrefix (Fin.init (u ∘ e)) (rename e p)).eval t = _
  rw [eval_evalPrefix, eval_specializeLast, hsnoc, eval_rename]
  apply congrArg (fun w => eval w p)
  funext j
  by_cases h : j = i
  · subst j
    simp only [Function.comp_apply, he, Function.update_self]
  · have hj : e j ≠ Fin.last m := fun h' => h (e.injective (h'.trans he.symm))
    rw [Function.comp_apply, Function.update_of_ne hj, Function.update_of_ne h]
    change u (e (e j)) = u j
    simp [e]

/-- Evaluating the other variables cannot increase the degree of the retained variable. -/
theorem natDegree_evalCoordinate_le (u : Fin (m + 1) → R) (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) R) :
    (evalCoordinate u i p).natDegree ≤ p.degreeOf i := by
  let e := Equiv.swap i (Fin.last m)
  have he : e i = Fin.last m := Equiv.swap_apply_left _ _
  change (evalPrefix (Fin.init (u ∘ e)) (rename e p)).natDegree ≤ _
  refine (natDegree_evalPrefix_le _ _).trans_eq ?_
  rw [← he, degreeOf_rename_of_injective e.injective]

/-- A prefix variable has degree at most `d` exactly when it has that bound in each
coefficient of the polynomial in the last variable. -/
theorem degreeOf_castSucc_le_iff (i : Fin m) (p : MvPolynomial (Fin (m + 1)) R)
    (d : ℕ) :
    p.degreeOf i.castSucc ≤ d ↔ ∀ k, ((lastVariableEquiv R m p).coeff k).degreeOf i ≤ d := by
  unfold lastVariableEquiv
  change p.degreeOf i.castSucc ≤ d ↔
    ∀ k, ((optionEquivLeft R _ (rename finSuccEquivLast p)).coeff k).degreeOf i ≤ d
  rw [← degreeOf_rename_of_injective finSuccEquivLast.injective i.castSucc,
    finSuccEquivLast_castSucc]
  simp only [degreeOf_le_iff, mem_support_coeff_optionEquivLeft]
  constructor
  · intro h k s hs
    simpa using h (s.optionElim k) hs
  · intro h s hs
    exact h (s none) s.some (by simpa using hs)

/-- Specializing the last variable preserves each bound on the prefix variables. -/
theorem degreeOf_specializeLast_le (x : R) (p : MvPolynomial (Fin (m + 1)) R) (i : Fin m) :
    (specializeLast x p).degreeOf i ≤ p.degreeOf i.castSucc := by
  have h := (degreeOf_castSucc_le_iff i p _).mp le_rfl
  unfold specializeLast
  change (Polynomial.eval (C x) (lastVariableEquiv R m p)).degreeOf i ≤ _
  rw [Polynomial.eval_eq_sum_range]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [← map_pow (C : R →+* MvPolynomial (Fin m) R) x j, degreeOf_C, add_zero]
  exact h j

end MvPolynomial
