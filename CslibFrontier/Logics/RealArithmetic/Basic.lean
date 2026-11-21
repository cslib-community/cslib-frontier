/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.Tuple.Take

/-!
# Integer polynomial formulas over the reals

Expression trees contain integer constants, finite variable indices, addition and
multiplication. Boolean formulas compare expressions with zero. Their semantics is a subset
of real coordinate space; quantification is performed by the problem using the formula.
This is the finite syntax and semantics of `edemaine/lean-canny`'s formal abstract at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.

A dedicated expression grammar retains integer coefficients and a concrete input encoding;
`Term.toPolynomial` connects it to Mathlib's mathematical polynomials.

## Main definitions

* `Cslib.Logic.RealArithmetic.Term`: integer polynomial expression trees.
* `Cslib.Logic.RealArithmetic.Formula`: Boolean combinations of polynomial comparisons.
* `Cslib.Logic.RealArithmetic.Formula.solutionSet`: the described real set.

## Main results

* `Cslib.Logic.RealArithmetic.Term.eval_toPolynomial`: evaluation agrees with the associated
  multivariate polynomial.
* `Cslib.Logic.RealArithmetic.Formula.solutionSet_rename`: renaming pulls back solution sets.
-/

public section
namespace Cslib.Logic.RealArithmetic

/-- Integer polynomial expressions use constants, variables, addition, and
multiplication. In dimension `n`, variables are the indices `Fin n`. -/
inductive Term (n : ℕ) where
  | const : ℤ → Term n
  | var : Fin n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n
  deriving DecidableEq, Repr

/-- Evaluate an integer polynomial expression at a real assignment `x`. -/
@[expose] def Term.eval {n : ℕ} (x : Fin n → ℝ) : Term n → ℝ
  | .const z => z
  | .var i => x i
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x

/-- A Boolean formula compares polynomial expressions with zero, using equality
or strict inequality, and combines these assertions by negation, conjunction,
and disjunction. ETR existentially quantifies all occurring variables;
a free formula describes a subset of real coordinate space. -/
inductive Formula (n : ℕ) where
  | false : Formula n
  | eqZero : Term n → Formula n
  | ltZero : Term n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n
  deriving DecidableEq, Repr

/-- A formula describes a solution set in `ℝⁿ`, represented by `Fin n → ℝ`.
Negation, conjunction, and disjunction give complement, intersection, and union. -/
@[expose] def Formula.solutionSet {n : ℕ} : Formula n → Set (Fin n → ℝ)
  | .false => ∅
  | .eqZero t => {x | t.eval x = 0}
  | .ltZero t => {x | t.eval x < 0}
  | .not p => p.solutionSetᶜ
  | .and p q => p.solutionSet ∩ q.solutionSet
  | .or p q => p.solutionSet ∪ q.solutionSet

/-- Rename the variables in an expression. -/
@[expose] def Term.rename {n m : ℕ} (f : Fin n → Fin m) : Term n → Term m
  | .const z => .const z
  | .var i => .var (f i)
  | .add a b => .add (a.rename f) (b.rename f)
  | .mul a b => .mul (a.rename f) (b.rename f)

@[simp] theorem Term.eval_rename {n m : ℕ} (f : Fin n → Fin m)
    (x : Fin m → ℝ) (t : Term n) : (t.rename f).eval x = t.eval (x ∘ f) := by
  induction t <;> simp_all [rename, eval, Function.comp_def]

/-- Interpret an expression as a mathematical polynomial with integer coefficients. -/
@[expose] noncomputable def Term.toPolynomial {n : ℕ} : Term n → MvPolynomial (Fin n) ℤ
  | .const z => MvPolynomial.C z
  | .var i => MvPolynomial.X i
  | .add a b => a.toPolynomial + b.toPolynomial
  | .mul a b => a.toPolynomial * b.toPolynomial

@[simp] theorem Term.eval_toPolynomial {n : ℕ} (x : Fin n → ℝ) (t : Term n) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) x t.toPolynomial = t.eval x := by
  induction t with
  | const z => exact MvPolynomial.eval₂_C (Int.castRingHom ℝ) x z
  | var i => exact MvPolynomial.eval₂_X (Int.castRingHom ℝ) x i
  | add a b ha hb => simp [toPolynomial, eval, ha, hb]
  | mul a b ha hb => simp [toPolynomial, eval, ha, hb]

/-- Rename the free coordinates of a formula. -/
@[expose] def Formula.rename {n m : ℕ} (f : Fin n → Fin m) : Formula n → Formula m
  | .false => .false
  | .eqZero t => .eqZero (t.rename f)
  | .ltZero t => .ltZero (t.rename f)
  | .not p => .not (p.rename f)
  | .and p q => .and (p.rename f) (q.rename f)
  | .or p q => .or (p.rename f) (q.rename f)

/-- A renamed formula holds exactly when the original holds on the selected coordinates. -/
@[simp] theorem Formula.solutionSet_rename {n m : ℕ} (f : Fin n → Fin m) (p : Formula n) :
    (p.rename f).solutionSet = (fun x => x ∘ f) ⁻¹' p.solutionSet := by
  ext x
  induction p <;> simp_all [rename, solutionSet]

/-- The existential assignments for which a formula holds for every universal assignment.
The existential coordinates precede the universal coordinates; either block may be empty. -/
@[expose] def Formula.existsForallSolutionSet {r s : ℕ} (p : Formula (r + s)) :
    Set (Fin r → ℝ) := {x | ∀ y : Fin s → ℝ, Fin.addCases x y ∈ p.solutionSet}

/-- An injective renaming preserves whether the real solution set is nonempty. -/
theorem Formula.solutionSet_nonempty_rename {n m : ℕ} {f : Fin n → Fin m}
    (hf : Function.Injective f) (p : Formula n) :
    (p.rename f).solutionSet.Nonempty ↔ p.solutionSet.Nonempty := by
  rw [solutionSet_rename]
  exact hf.surjective_comp_right.nonempty_preimage

/-- Adding unused universal coordinates preserves every existential solution. -/
theorem Formula.existsForallSolutionSet_rename_castLE {r s t : ℕ}
    (h : s ≤ t) (p : Formula (r + s)) :
    (p.rename (Fin.castLE (Nat.add_le_add_left h r))).existsForallSolutionSet
      (r := r) (s := t) = p.existsForallSolutionSet (r := r) (s := s) := by
  ext x
  have hrestriction (z : Fin t → ℝ) :
      Fin.addCases x z ∘ Fin.castLE (Nat.add_le_add_left h r) =
        Fin.addCases x (z ∘ Fin.castLE h) := by
    exact Fin.take_append_right (n := r) s h x z
  simp only [existsForallSolutionSet, Set.mem_ofPred_eq, solutionSet_rename,
    Set.mem_preimage, hrestriction]
  constructor
  · intro hx y
    obtain ⟨z, rfl⟩ := (Fin.castLE_injective h).surjective_comp_right y
    exact hx z
  · intro hx z
    exact hx (z ∘ Fin.castLE h)

end Cslib.Logic.RealArithmetic
