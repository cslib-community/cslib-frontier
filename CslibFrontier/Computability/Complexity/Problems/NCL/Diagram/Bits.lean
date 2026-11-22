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
* `Cslib.Complexity.NCL.Diagram.OpenSim.bits_comp`: serialization respects stacking.
* `Cslib.Complexity.NCL.Diagram.OpenSim.bits_tensor`: serialization respects juxtaposition.

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

private theorem ofFn_sumEquiv {α β γ : Type*} {m n : ℕ}
    (e₁ : α ≃ Fin m) (e₂ : β ≃ Fin n) (f : α ⊕ β → γ) :
    List.ofFn (fun i => f (((e₁.sumCongr e₂).trans finSumFinEquiv).symm i)) =
      List.ofFn (fun i => f (.inl (e₁.symm i))) ++
        List.ofFn (fun i => f (.inr (e₂.symm i))) := by
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    change f ((e₁.sumCongr e₂).symm (finSumFinEquiv.symm (Fin.castAdd n i))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  · congr 1
    funext i
    change f ((e₁.sumCongr e₂).symm (finSumFinEquiv.symm (Fin.natAdd m i))) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl

private theorem innerBits_glueComp (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (s₁ : D₁.Edge → Bool) (s₂ : D₂.Edge → Bool) :
    (D₁.comp D₂).innerBits (glueComp D₁ D₂ s₁ s₂) = D₁.innerBits s₁ ++ D₂.innerBits s₂ :=
  ofFn_sumEquiv D₁.innerEquiv D₂.innerEquiv
    (fun e => glueComp D₁ D₂ s₁ s₂ (.inr e))

private theorem innerBits_glueTensor (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (s₁ : D₁.Edge → Bool) (s₂ : D₂.Edge → Bool) :
    (D₁.tensor D₂).innerBits (glueTensor D₁ D₂ s₁ s₂) = D₁.innerBits s₁ ++ D₂.innerBits s₂ :=
  ofFn_sumEquiv D₁.innerEquiv D₂.innerEquiv
    (fun e => glueTensor D₁ D₂ s₁ s₂ (.inr e))

private theorem bits_eq_top_append_inner (D : Diagram Γ a b) (s : D.Edge → Bool) :
    D.bits s = List.ofFn (fun i => s (.inl i)) ++ D.innerBits s :=
  ofFn_sumEquiv (Equiv.refl (Fin a.length)) D.innerEquiv s

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

end OpenSim

end Cslib.Complexity.NCL.Diagram
