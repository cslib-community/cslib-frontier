/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Finite
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Substitution
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Realization

/-!
# Serializing created edges and open simulations

Created edges are ordered by construction. Stacking and juxtaposition concatenate their local
serializations, including the canonical extensions supplied by open simulations.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.innerBits`: created-edge serialization.
* `Cslib.Complexity.NCL.Diagram.OpenSim.bits`: serialization of a canonical extension.

## Main results

* `Cslib.Complexity.NCL.Diagram.bits_closed`: serialization of a closed diagram.
* `Cslib.Complexity.NCL.Diagram.OpenSim.bits_comp_realization`: serialization respects stacking.
* `Cslib.Complexity.NCL.Diagram.OpenSim.bits_tensor_realization`: serialization respects
  juxtaposition.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} {I : Interp Γ} {a b c d : List Color}

/-- Serialize created edges in their creation order. -/
@[expose] def innerBits (D : Diagram Γ a b) (s : D.Edge → Bool) : List Bool :=
  List.ofFn (fun i => s (.inr (D.innerEquiv.symm i)))

private theorem innerBits_glueComp (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (s₁ : D₁.Edge → Bool) (s₂ : D₂.Edge → Bool) :
    (D₁.comp D₂).innerBits (glueComp D₁ D₂ s₁ s₂) = D₁.innerBits s₁ ++ D₂.innerBits s₂ := by
  unfold innerBits
  change (List.ofFn fun i : Fin (D₁.innerCount + D₂.innerCount) =>
    glueComp D₁ D₂ s₁ s₂ (.inr ((D₁.comp D₂).innerEquiv.symm i))) = _
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    change glueComp D₁ D₂ s₁ s₂
      (.inr (((D₁.innerEquiv.sumCongr D₂.innerEquiv).trans finSumFinEquiv).symm
        (Fin.castAdd D₂.innerCount i))) = _
    simp [finSumFinEquiv_symm_apply_castAdd, glueComp]
  · congr 1
    funext i
    change glueComp D₁ D₂ s₁ s₂
      (.inr (((D₁.innerEquiv.sumCongr D₂.innerEquiv).trans finSumFinEquiv).symm
        (Fin.natAdd D₁.innerCount i))) = _
    simp [finSumFinEquiv_symm_apply_natAdd, glueComp]

private theorem innerBits_glueTensor (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (s₁ : D₁.Edge → Bool) (s₂ : D₂.Edge → Bool) :
    (D₁.tensor D₂).innerBits (glueTensor D₁ D₂ s₁ s₂) = D₁.innerBits s₁ ++ D₂.innerBits s₂ := by
  unfold innerBits
  change (List.ofFn fun i : Fin (D₁.innerCount + D₂.innerCount) =>
    glueTensor D₁ D₂ s₁ s₂ (.inr ((D₁.tensor D₂).innerEquiv.symm i))) = _
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    change glueTensor D₁ D₂ s₁ s₂
      (.inr (((D₁.innerEquiv.sumCongr D₂.innerEquiv).trans finSumFinEquiv).symm
        (Fin.castAdd D₂.innerCount i))) = _
    simp [finSumFinEquiv_symm_apply_castAdd, glueTensor]
  · congr 1
    funext i
    change glueTensor D₁ D₂ s₁ s₂
      (.inr (((D₁.innerEquiv.sumCongr D₂.innerEquiv).trans finSumFinEquiv).symm
        (Fin.natAdd D₁.innerCount i))) = _
    simp [finSumFinEquiv_symm_apply_natAdd, glueTensor]

private theorem bits_eq_top_append_inner (D : Diagram Γ a b) (s : D.Edge → Bool) :
    D.bits s = List.ofFn (fun i => s (.inl i)) ++ D.innerBits s := by
  unfold bits innerBits
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    change s (((Equiv.refl (Fin a.length)).sumCongr D.innerEquiv).trans
      finSumFinEquiv |>.symm <| Fin.castAdd D.innerCount i) = _
    simp [finSumFinEquiv_symm_apply_castAdd]
  · congr 1
    funext i
    change s (((Equiv.refl (Fin a.length)).sumCongr D.innerEquiv).trans
      finSumFinEquiv |>.symm <| Fin.natAdd a.length i) = _
    simp [finSumFinEquiv_symm_apply_natAdd]

/-- A diagram with no incoming wires serializes exactly its created edges. -/
theorem bits_closed (D : Diagram Γ [] b) (s : D.Edge → Bool) : D.bits s = D.innerBits s := by
  rw [bits_eq_top_append_inner]
  rfl

namespace OpenSim

variable {Γ' : List Color → List Color → Type} {I' : Interp Γ'}
  {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c} {D₁' : Diagram Γ' a b} {D₂' : Diagram Γ' b c}

/-- Serialize the created-edge directions of the canonical extension. -/
@[expose] def bits {D : Diagram Γ a b} {D' : Diagram Γ' a b} (S : OpenSim I I' D D')
    (s : D.Edge → Bool) : List Bool := D'.innerBits (S.enc s)

/-- Identity wires create no configuration bits. -/
@[simp] theorem bits_idWires (a : List Color) (s : (Diagram.id (Γ := Γ) a).Edge → Bool) :
    (idWires (I := I) (I' := I') a).bits s = [] := rfl

/-- Crossing wires creates no configuration bits. -/
@[simp] theorem bits_swapWires (x y : Color)
    (s : (Diagram.swap (Γ := Γ) x y).Edge → Bool) :
    (swapWires (I := I) (I' := I') x y).bits s = [] := rfl

/-- Canonical extensions of a stack serialize as the concatenation of their local extensions. -/
theorem bits_comp (S₁ : OpenSim I I' D₁ D₁') (S₂ : OpenSim I I' D₂ D₂')
    (s : (D₁.comp D₂).Edge → Bool) :
    (S₁.comp S₂).bits s = S₁.bits (s ∘ compLeft D₁ D₂) ++ S₂.bits (s ∘ compRight D₁ D₂) :=
  innerBits_glueComp ..

/-- Canonical extensions of a juxtaposition serialize in left-to-right creation order. -/
theorem bits_tensor {D₃ : Diagram Γ c d} {D₃' : Diagram Γ' c d}
    (S₁ : OpenSim I I' D₁ D₁') (S₃ : OpenSim I I' D₃ D₃') (s : (D₁.tensor D₃).Edge → Bool) :
    (S₁.tensor S₃).bits s =
      S₁.bits (s ∘ tensorLeft D₁ D₃) ++ S₃.bits (s ∘ tensorRight D₁ D₃) :=
  innerBits_glueTensor ..

/-- Serializing the extension of stacked realizations concatenates their extensions. -/
theorem bits_comp_realization {x y z : List Bool}
    (S₁ : OpenSim I I' D₁ D₁') (S₂ : OpenSim I I' D₂ D₂')
    (R₁ : Realization I D₁ x y) (R₂ : Realization I D₂ y z) :
    (S₁.comp S₂).bits (R₁.comp R₂).orient = S₁.bits R₁.orient ++ S₂.bits R₂.orient := by
  rw [bits_comp, Realization.comp_orient_compLeft, Realization.comp_orient_compRight]

end OpenSim

end Cslib.Complexity.NCL.Diagram
