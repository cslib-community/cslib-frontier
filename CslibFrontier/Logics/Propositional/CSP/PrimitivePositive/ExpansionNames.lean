/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Expansion
public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Replacement
import Mathlib.Data.List.Enum

/-!
# Ragged auxiliary labels and the numeric replacement namespaces

The existing semantic expansion concatenates actual auxiliary blocks. Its injection into
the existing compiler's padded blocks is derived here from those sizes. Thus separate source
occurrences remain separate even when their relation symbols and ordered scopes coincide.
No target-label injection is a caller-supplied premise.

## Main results

* `Cslib.Logic.PL.CSP.PPGadget.expansionName_injective`:
  the internally constructed naming injection.
* `Cslib.Logic.PL.CSP.PPGadget.expandList_body_numeric`: exact equality with numeric replacement.
-/

public section

namespace Cslib.Logic.PL.CSP.PPGadget

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- Embed actual concatenated auxiliary blocks into blocks of width `B`. This is an
internal representation map, not a new replacement algorithm. -/
@[expose] def expansionAuxName
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) {k : ℕ} (F : CSP Src (Fin k)) (hF : WellFormed srcArity F) :
    Fin (expandList gadgets F hF).numAux → ℕ :=
  match F with
  | [] => Fin.elim0
  | c :: cs =>
    let ht : WellFormed srcArity cs := fun d hd => hF d (List.mem_cons_of_mem c hd)
    Fin.addCases Fin.val (fun i => B + expansionAuxName gadgets B cs ht i)

/-- The actual ragged labels all lie in the finite padded occurrence range. Empty
auxiliary blocks require no positivity assumption on `B`. -/
theorem expansionAuxName_lt
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (hB : ∀ r, (gadgets r).numAux ≤ B)
    {k : ℕ} (F : CSP Src (Fin k)) (hF : WellFormed srcArity F)
    (i : Fin (expandList gadgets F hF).numAux) :
    expansionAuxName gadgets B F hF i < B * F.length := by
  induction F with
  | nil => exact Fin.elim0 i
  | cons c cs ih =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [expansionAuxName, Fin.addCases_left, List.length_cons, Nat.mul_succ]
      have hj := j.isLt.trans_le (hB c.rel)
      omega
    · simp only [expansionAuxName, Fin.addCases_right, List.length_cons, Nat.mul_succ]
      have hj := ih _ j
      omega

/-- Distinct occurrence-local auxiliary labels stay distinct in the existing padded
namespace. This includes repeated gadgets and repeated scopes. -/
theorem expansionAuxName_injective
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (hB : ∀ r, (gadgets r).numAux ≤ B)
    {k : ℕ} (F : CSP Src (Fin k)) (hF : WellFormed srcArity F) :
    Function.Injective (expansionAuxName gadgets B F hF) := by
  induction F with
  | nil => intro i; exact i.elim0
  | cons c cs ih =>
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [expansionAuxName, Fin.addCases_left]
      intro he
      exact congrArg (Fin.castAdd _) (Fin.ext he)
    · simp only [expansionAuxName, Fin.addCases_left, Fin.addCases_right]
      have hi := i.isLt.trans_le (hB c.rel)
      omega
    · simp only [expansionAuxName, Fin.addCases_right, Fin.addCases_left]
      have hj := j.isLt.trans_le (hB c.rel)
      omega
    · simp only [expansionAuxName, Fin.addCases_right]
      intro he
      exact congrArg (Fin.natAdd _) (ih _ (Nat.add_left_cancel he))

/-- Free source names occupy even numbers; each ragged auxiliary occupies the odd
number for its original source-constraint occurrence. -/
@[expose] def expansionName
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) {k : ℕ} (F : CSP Src (Fin k)) (hF : WellFormed srcArity F) :
    Fin k ⊕ Fin (expandList gadgets F hF).numAux → ℕ :=
  Sum.elim (fun i => 2 * i.val)
    (fun i => 2 * expansionAuxName gadgets B F hF i + 1)

/-- The free/auxiliary injection is constructed from parity and the actual ragged blocks. -/
theorem expansionName_injective
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (hB : ∀ r, (gadgets r).numAux ≤ B)
    {k : ℕ} (F : CSP Src (Fin k)) (hF : WellFormed srcArity F) :
    Function.Injective (expansionName gadgets B F hF) := by
  intro i j he
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (Fin.ext (by simpa [expansionName] using he))
    | inr j => simp only [expansionName, Sum.elim_inl, Sum.elim_inr] at he; omega
  | inr i =>
    cases j with
    | inl j => simp only [expansionName, Sum.elim_inl, Sum.elim_inr] at he; omega
    | inr j =>
      apply congrArg Sum.inr
      apply expansionAuxName_injective gadgets B hB F hF
      simpa [expansionName] using he

private theorem expandList_body_numeric_from
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B start : ℕ) {k : ℕ} (F : CSP Src (Fin k)) (hF : WellFormed srcArity F) :
    (expandList gadgets F hF).body.relabel
        (Sum.elim (fun i => 2 * i.val)
          (fun i => 2 * (B * start + expansionAuxName gadgets B F hF i) + 1)) =
      (F.zipIdx start).flatMap (fun (c, i) =>
        instantiate B i (c.scope.map Fin.val) (gadgets c.rel).template) := by
  induction F generalizing start with
  | nil => rfl
  | cons c cs ih =>
    let ht : WellFormed srcArity cs := fun d hd => hF d (List.mem_cons_of_mem c hd)
    change (((gadgets c.rel).relabelFree _).conj (expandList gadgets cs ht)).body.relabel _ = _
    simp only [expansionAuxName, conj, relabelFree, CSP.relabel, List.map_append, List.map_map,
      List.zipIdx_cons, List.flatMap_cons]
    congr 1
    · unfold instantiate template CSP.relabel
      simp only [List.map_map]
      apply List.map_congr_left
      intro d _
      apply Constraint.ext
      · rfl
      change List.map (Sum.elim (fun i : Fin k => 2 * i.val)
          (fun i : Fin ((gadgets c.rel).numAux + (expandList gadgets cs ht).numAux) =>
            2 * (B * start + Fin.addCases Fin.val
              (fun j => B + expansionAuxName gadgets B cs ht j) i) + 1))
          ((d.scope.map (Sum.map (fun i => c.scope[i.val]'(by
              rw [hF c List.mem_cons_self]; exact i.isLt)) id)).map
            (Sum.map id (Fin.castAdd (expandList gadgets cs ht).numAux))) =
        (d.scope.map (Sum.elim (fun i => (false, i.val)) (fun i => (true, i.val)))).map
          (fun p => if p.1 then 2 * (B * start + p.2) + 1
            else 2 * (c.scope.map Fin.val).getD p.2 0)
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v with
      | inl i =>
        have hi : i.val < c.scope.length := by
          rw [hF c List.mem_cons_self]
          exact i.isLt
        simp [List.getElem?_eq_getElem hi, Function.comp_def]
      | inr i => simp [Function.comp_def]
    · rw [← ih (start + 1) ht]
      simp only [CSP.relabel]
      apply List.map_congr_left
      intro d _
      apply Constraint.ext
      · rfl
      change List.map (Sum.elim (fun i : Fin k => 2 * i.val)
          (fun i : Fin ((gadgets c.rel).numAux + (expandList gadgets cs ht).numAux) =>
            2 * (B * start + Fin.addCases Fin.val
              (fun j => B + expansionAuxName gadgets B cs ht j) i) + 1))
          (d.scope.map (Sum.map id (Fin.natAdd (gadgets c.rel).numAux))) =
        d.scope.map (Sum.elim (fun i => 2 * i.val)
          (fun i => 2 * (B * (start + 1) + expansionAuxName gadgets B cs ht i) + 1))
      rw [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v with
      | inl i => rfl
      | inr i =>
        simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr,
          Fin.addCases_right, Nat.mul_add, Nat.mul_one]
        omega

/-- The finite semantic expansion, with its actual ragged blocks, is exactly the existing
numeric replacement after its internally constructed injective naming map. -/
theorem expandList_body_numeric
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) {k : ℕ} (F : CSP Src (Fin k)) (hF : WellFormed srcArity F) :
    (expandList gadgets F hF).body.relabel (expansionName gadgets B F hF) =
      replaceGadgets B (fun r => (gadgets r).template) (F.relabel Fin.val) := by
  have h := expandList_body_numeric_from gadgets B 0 F hF
  simpa only [expansionName, Nat.mul_zero, Nat.zero_add, replaceGadgets,
    CSP.relabel, List.zipIdx_map, List.flatMap_map, Function.comp_def,
    Prod.map, id_eq, Constraint.relabel] using h

end Cslib.Logic.PL.CSP.PPGadget
