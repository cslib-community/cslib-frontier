/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledCoordinateLift
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Mathlib.Analysis.Real.Sqrt

/-!
# Controlled equations for strict positivity

Each strict inequality receives its own auxiliary variable. A label is positive at
the original point exactly when its product with the square of the auxiliary variable
can equal one. Modular evaluation of the resulting equations keeps the label family's
counting level, including with total binary address lookup.

Adapted from lean-canny's `ControlledOptionalCoordinate` and the inequality rows of
`ControlledIndexedSystem` at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial

private noncomputable def coordinateOrZero (n i : ℕ) : MvPolynomial (Fin n) ℤ :=
  if h : i < n then X ⟨i, h⟩ else 0

private theorem coordinateOrZero_bounds (n j : ℕ) :
    (coordinateOrZero n j).totalDegree ≤ 1 ∧ (coordinateOrZero n j).coeffNorm1 ≤ 1 := by
  unfold coordinateOrZero
  split <;> simp

private noncomputable def controlledCoordinateOrZero {α : Type} {n i : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hi : ComputableInPolyTime i enc encNat) :
    Controlled (fun w => coordinateOrZero (n w) (i w)) enc a where
  arity_computable := hn
  degreeBound _ := 1
  degree_computable := .const 1
  degree_le w := (coordinateOrZero_bounds _ _).1
  massExponent _ := 0
  mass_computable := .const 0
  mass_le w := (coordinateOrZero_bounds _ _).2
  cutoff _ := 0
  cutoff_computable := .const 0
  evaluate := fun (w, p, z) => (if i w < n w then z.getD (i w) 0 else 0) % p
  evaluate_mem := by
    let args := encPair encNat (encList encNat)
    have hw := fst enc args
    have hargs := snd enc args
    have hp := (fst encNat (encList encNat)).comp hargs
    have hz := (snd encNat (encList encNat)).comp hargs
    have hindex := hi.comp hw
    have hguard := binary_lt' hindex ((unary_to_binary.comp hn).comp hw)
    have hread := listGetD_binary (encA := encNat) 0 hz hindex
    exact CountingFunction.of_polyTime (binary_mod' (ite_decide hguard hread (.const 0)) hp)
  evaluate_eq w p z hp _ := by
    let : NeZero p := ⟨hp.ne_zero⟩
    by_cases h : i w < n w
    · simp [coordinateOrZero, evaluation, h, List.getD_eq_getElem?_getD, ZMod.val_natCast]
    · simp [coordinateOrZero, evaluation, h]

/-- The equation for one positive test in an appended block of `k` variables.
An out-of-range binary address has the constant equation `-1 = 0`. -/
noncomputable def positivityEquation {n : ℕ} (Q : MvPolynomial (Fin n) ℤ) (k j : ℕ) :
    MvPolynomial (Fin (n + k)) ℤ :=
  MvPolynomial.rename (Fin.castAdd k) Q * coordinateOrZero (n + k) (n + j) ^ 2 + C (-1)

/-- At a valid address the auxiliary variable belongs to the appended block. -/
theorem positivityEquation_of_lt {n k j : ℕ} (Q : MvPolynomial (Fin n) ℤ) (hj : j < k) :
    positivityEquation Q k j =
      MvPolynomial.rename (Fin.castAdd k) Q * X (Fin.natAdd n ⟨j, hj⟩) ^ 2 + C (-1) := by
  rw [positivityEquation, coordinateOrZero, dite_eq_left (Nat.add_lt_add_left hj n)]
  rfl

/-- Outside the auxiliary block the row is the impossible constant equation. -/
theorem positivityEquation_of_le {n k j : ℕ} (Q : MvPolynomial (Fin n) ℤ) (hj : k ≤ j) :
    positivityEquation Q k j = C (-1) := by
  simp [positivityEquation, coordinateOrZero, Nat.not_lt_of_ge (Nat.add_le_add_left hj n)]

/-- An auxiliary equation adds at most two to the original total degree. -/
theorem totalDegree_positivityEquation_le {n : ℕ} (Q : MvPolynomial (Fin n) ℤ) (k j : ℕ) :
    (positivityEquation Q k j).totalDegree ≤ Q.totalDegree + 2 := by
  unfold positivityEquation
  refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (totalDegree_rename_le _ _)
    ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (coordinateOrZero_bounds _ _).1)))

/-- An auxiliary equation adds at most one to the original coefficient norm. -/
theorem coeffNorm1_positivityEquation_le {n : ℕ} (Q : MvPolynomial (Fin n) ℤ) (k j : ℕ) :
    (positivityEquation Q k j).coeffNorm1 ≤ Q.coeffNorm1 + 1 := by
  unfold positivityEquation
  refine (coeffNorm1_add_le _ _).trans (Nat.add_le_add ?_ (by simp))
  have hs := (coeffNorm1_pow_le (coordinateOrZero (n + k) (n + j)) 2).trans
    (Nat.pow_le_pow_left (coordinateOrZero_bounds _ _).2 2)
  exact (coeffNorm1_mul_le _ _).trans ((Nat.mul_le_mul (coeffNorm1_rename_le _ _) hs).trans_eq
    (Nat.mul_one _))

/-- Turn indexed strict inequalities into equations using one auxiliary variable per
in-range index. The modular evaluator preserves the input counting level. -/
noncomputable def Controlled.positivityEquations {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {Q : (q : α × ℕ) → MvPolynomial (Fin (n q.1)) ℤ}
    (CQ : Controlled Q (encPair enc encNat) a)
    (k : α → ℕ) (hk : ComputableInPolyTime k enc encUnary) :
    Controlled (fun q : α × ℕ => positivityEquation (Q q) (k q.1) q.2)
      (encPair enc encNat) a :=
  let hw := fst enc encNat
  let hi := binary_add' (unary_to_binary.comp CQ.arity_computable) (snd enc encNat)
  let CQ' := CQ.appendVariables (fun q => k q.1) (hk.comp hw)
  let CS := controlledCoordinateOrZero (a := a) CQ'.arity_computable hi
  let CM := Controlled.constant (a := a) CQ'.arity_computable (fun _ => -1) (.const (-1))
  (CQ'.mul (CS.pow (fun _ => 2) (.const 2))).add CM

section PositivityBounds

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {Q : (q : α × ℕ) → MvPolynomial (Fin (n q.1)) ℤ}
  (CQ : Controlled Q (encPair enc encNat) a) (k : α → ℕ)
  (hk : ComputableInPolyTime k enc encUnary)

/-- The controlled equations increase the certified degree bound by two. -/
@[simp] theorem Controlled.degreeBound_positivityEquations :
    (CQ.positivityEquations k hk).degreeBound = fun q => CQ.degreeBound q + 2 := by
  funext q
  simp [Controlled.positivityEquations, Controlled.add, Controlled.mul, Controlled.pow,
    Controlled.constant, controlledCoordinateOrZero]

/-- The controlled equations increase the certified coefficient norm exponent by two. -/
@[simp] theorem Controlled.massExponent_positivityEquations :
    (CQ.positivityEquations k hk).massExponent = fun q => CQ.massExponent q + 2 := by
  funext q
  simp [Controlled.positivityEquations, Controlled.add, Controlled.mul, Controlled.pow,
    Controlled.constant, controlledCoordinateOrZero, Nat.add_assoc]

/-- The controlled equations preserve the input prime cutoff. -/
@[simp] theorem Controlled.cutoff_positivityEquations :
    (CQ.positivityEquations k hk).cutoff = CQ.cutoff := by
  funext q
  simp [Controlled.positivityEquations, Controlled.add, Controlled.mul, Controlled.pow,
    Controlled.constant, controlledCoordinateOrZero]

end PositivityBounds

/-- At a valid index the appended coordinate multiplies the original test by its square. -/
theorem eval₂_positivityEquation {n k : ℕ} {R : Type*} [CommRing R] (f : ℤ →+* R)
    (Q : MvPolynomial (Fin n) ℤ) (x : Fin n → R) (s : Fin k → R) (i : Fin k) :
    MvPolynomial.eval₂ f (Fin.addCases x s) (positivityEquation Q k i.val) =
      MvPolynomial.eval₂ f x Q * s i ^ 2 - 1 := by
  simp only [positivityEquation_of_lt Q i.isLt, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_neg, eval₂_one, eval₂_rename, Function.comp_def, Fin.addCases_left, Fin.addCases_right,
    map_neg, map_one, sub_eq_add_neg]

/-- A point satisfies all its strict inequalities exactly when it extends to a
solution of the corresponding auxiliary equations. Each inequality has its own variable. -/
theorem exists_positivityEquations_zero_iff {n : ℕ}
    (Q : ℕ → MvPolynomial (Fin n) ℤ) (k : ℕ) (x : Fin n → ℝ) :
    (∃ s : Fin k → ℝ, ∀ j < k, MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases x s)
      (positivityEquation (Q j) k j) = 0) ↔
    ∀ j < k, 0 < MvPolynomial.eval₂ (Int.castRingHom ℝ) x (Q j) := by
  constructor
  · rintro ⟨s, hs⟩ j hj
    let i : Fin k := ⟨j, hj⟩
    have he := (eval₂_positivityEquation (Int.castRingHom ℝ) (Q j) x s i).symm.trans (hs j hj)
    have hone := sub_eq_zero.mp he
    by_contra! h
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg (s i))
    rw [hone] at hnonpos
    exact (not_le_of_gt zero_lt_one) hnonpos
  · intro h
    let s (i : Fin k) := Real.sqrt ((MvPolynomial.eval₂ (Int.castRingHom ℝ) x (Q i.val))⁻¹)
    refine ⟨s, fun j hj => ?_⟩
    let i : Fin k := ⟨j, hj⟩
    change MvPolynomial.eval₂ _ _ (positivityEquation (Q j) k i.val) = 0
    rw [eval₂_positivityEquation, sub_eq_zero]
    change _ * (Real.sqrt ((MvPolynomial.eval₂ (Int.castRingHom ℝ) x (Q j))⁻¹)) ^ 2 = 1
    rw [Real.sq_sqrt (inv_nonneg.mpr (h j hj).le), mul_inv_cancel₀ (h j hj).ne']

end Cslib.Complexity.RealAlgebraic
