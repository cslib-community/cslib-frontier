/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word

/-!
# Enumerating diagram edges

The creation-order numbering is a computable equivalence with a finite interval. Its inverse
lets move certificates use edge numbers while retaining the diagram's edge type.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.innerEquiv`: created edges in creation order.
* `Cslib.Complexity.NCL.Diagram.numEquiv`: top wires followed by created edges.

## Main results

* `Cslib.Complexity.NCL.Diagram.num_numEquiv_symm`: a numbered certificate reads back its number.

## References

* This enumerates the diagram representation used for [Hearn and Demaine][HearnDemaine2005].
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} {a b : List Color}

/-- Created wires, in the order counted by `innerCount`. -/
@[expose] def innerEquiv : {a b : List Color} → (D : Diagram Γ a b) → D.Inner ≃ Fin D.innerCount
  | _, _, .gen _ => .refl _
  | _, _, .id _ => (show Empty ≃ Fin 0 from Equiv.equivOfIsEmpty _ _)
  | _, _, .swap .. => (show Empty ≃ Fin 0 from Equiv.equivOfIsEmpty _ _)
  | _, _, .comp D₁ D₂ => ((innerEquiv D₁).sumCongr (innerEquiv D₂)).trans finSumFinEquiv
  | _, _, .tensor D₁ D₂ => ((innerEquiv D₁).sumCongr (innerEquiv D₂)).trans finSumFinEquiv

private theorem innerEquiv_val : {a b : List Color} → (D : Diagram Γ a b) → (e : D.Inner) →
    (D.innerEquiv e).val = D.idx e
  | _, _, .gen _, _ => rfl
  | _, _, .id _, e => e.elim
  | _, _, .swap .., e => e.elim
  | _, _, .comp D₁ D₂, e => by
    rcases e with e | e
    · exact innerEquiv_val D₁ e
    · exact congrArg (D₁.innerCount + ·) (innerEquiv_val D₂ e)
  | _, _, .tensor D₁ D₂, e => by
    rcases e with e | e
    · exact innerEquiv_val D₁ e
    · exact congrArg (D₁.innerCount + ·) (innerEquiv_val D₂ e)

/-- All diagram edges: the top wires first, followed by the created wires. -/
@[expose] def numEquiv (D : Diagram Γ a b) : D.Edge ≃ Fin (a.length + D.innerCount) :=
  ((Equiv.refl _).sumCongr D.innerEquiv).trans finSumFinEquiv

@[simp] theorem numEquiv_val (D : Diagram Γ a b) (e : D.Edge) :
    (D.numEquiv e).val = D.num e := by
  rcases e with i | e
  · rfl
  · simp [numEquiv, num, name, innerEquiv_val]

@[simp] theorem num_numEquiv_symm (D : Diagram Γ a b) (i : Fin (a.length + D.innerCount)) :
    D.num (D.numEquiv.symm i) = i.val := by
  rw [← numEquiv_val, Equiv.apply_symm_apply]

end Cslib.Complexity.NCL.Diagram
