/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Foundations.Data.PFunctor.Free.Fold
public import CslibFrontier.Computability.DecisionTree.Basic

/-!
# Boolean decision trees as free query programs

Each internal node asks for one Boolean reply. `equivFreeM` identifies decision trees with the
free programs of this query interface. Evaluating the tree on an assignment folds the free
program by reading that assignment at each query.

Ported from the `PolyFunFrontier.PFunctor.Free.DecisionTree` module of `Verified-zkEVM/PolyFun`
at revision `713d8857e49d20927c1447b3ba7397acc5537319`.

## Main definitions

* `Cslib.DecisionTree.toFreeM` and `Cslib.DecisionTree.ofFreeM` translate in both directions.
* `Cslib.DecisionTree.equivFreeM` packages the translations as an equivalence.

## Main results

* `Cslib.DecisionTree.eval_toFreeM` identifies the fold of a translated tree with its evaluation.
* `Cslib.DecisionTree.eval_ofFreeM` evaluates the tree obtained from a free program.
-/

public section

universe u v

namespace Cslib.DecisionTree

open PFunctor

variable {ι : Type u} {β : Type v}

/-- A decision tree as a free program: a leaf returns its output, and a node queries its variable
and continues with the branch for the answer. -/
@[expose] def toFreeM : DecisionTree ι β → (monomial ι Bool).FreeM β
  | leaf b => .pure b
  | node i t₀ t₁ => .liftBind i fun b => cond b t₁.toFreeM t₀.toFreeM

/-- A free program over Boolean queries as a decision tree. -/
@[expose] def ofFreeM : (monomial ι Bool).FreeM β → DecisionTree ι β
  | .pure b => leaf b
  | .liftBind i k => node i (ofFreeM (k false)) (ofFreeM (k true))

@[simp] theorem toFreeM_leaf (b : β) : (leaf b : DecisionTree ι β).toFreeM = pure b := rfl

@[simp] theorem toFreeM_node (i : ι) (t₀ t₁ : DecisionTree ι β) :
    (node i t₀ t₁).toFreeM =
      (FreeM.lift (P := monomial ι Bool) i).bind fun b => cond b t₁.toFreeM t₀.toFreeM :=
  rfl

@[simp] theorem ofFreeM_pure (b : β) : ofFreeM (pure b : (monomial ι Bool).FreeM β) = leaf b :=
  rfl

@[simp] theorem ofFreeM_lift_bind (i : ι)
    (k : (monomial ι Bool).B i → (monomial ι Bool).FreeM β) :
    ofFreeM ((FreeM.lift (P := monomial ι Bool) i).bind
        (α := no_index (monomial ι Bool).B i) k) =
      node i (ofFreeM (k false)) (ofFreeM (k true)) :=
  rfl

@[simp] theorem ofFreeM_lift_bind' {β : Type} (i : ι) (k : Bool → (monomial ι Bool).FreeM β) :
    ofFreeM (Bind.bind (α := Bool) (FreeM.lift (P := monomial ι Bool) i) k) =
      node i (ofFreeM (k false)) (ofFreeM (k true)) :=
  rfl

@[simp] theorem ofFreeM_lift (i : ι) :
    ofFreeM (β := Bool) (FreeM.lift (P := monomial ι Bool) i) =
      node i (leaf false) (leaf true) :=
  rfl

@[simp] theorem ofFreeM_toFreeM (t : DecisionTree ι β) : ofFreeM t.toFreeM = t := by
  induction t with
  | leaf => rfl
  | node i t₀ t₁ ih₀ ih₁ => exact congrArg₂ (node i) ih₀ ih₁

@[simp] theorem toFreeM_ofFreeM (p : (monomial ι Bool).FreeM β) : (ofFreeM p).toFreeM = p := by
  induction p using FreeM.induction with
  | pure => rfl
  | lift_bind i k ih =>
    rw [ofFreeM_lift_bind, toFreeM_node]
    exact congrArg _ (funext fun b => by cases b <;> exact ih _)

/-- Decision trees over `ι` are exactly the free programs of the Boolean query interface
`monomial ι Bool`. -/
@[expose] def equivFreeM : DecisionTree ι β ≃ (monomial ι Bool).FreeM β where
  toFun := toFreeM
  invFun := ofFreeM
  left_inv := ofFreeM_toFreeM
  right_inv := toFreeM_ofFreeM

@[simp] theorem equivFreeM_apply (t : DecisionTree ι β) : equivFreeM t = t.toFreeM := rfl

@[simp] theorem equivFreeM_symm_apply (p : (monomial ι Bool).FreeM β) :
    equivFreeM.symm p = ofFreeM p :=
  rfl

/-- Evaluating a decision tree on `x` folds its free program, answering each query `i` by
`x i`. -/
theorem eval_toFreeM (t : DecisionTree ι β) (x : ι → Bool) :
    t.toFreeM.foldFreeM id (fun i k => k (x i)) = t.eval x := by
  induction t with
  | leaf => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    change FreeM.foldFreeM id _ (cond (x i) t₁.toFreeM t₀.toFreeM) = cond (x i) _ _
    cases x i <;> assumption

/-- A free program over Boolean queries, answered from `x`, returns what its decision tree
returns on `x`. -/
theorem eval_ofFreeM (p : (monomial ι Bool).FreeM β) (x : ι → Bool) :
    (ofFreeM p).eval x = p.foldFreeM id (fun i k => k (x i)) := by
  rw [← eval_toFreeM, toFreeM_ofFreeM]

end Cslib.DecisionTree
