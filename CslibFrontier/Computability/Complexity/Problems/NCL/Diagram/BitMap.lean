/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Bits

/-!
# Compositional configuration serialization

A bit map serializes an orientation after a diagram transformation. Identity wires contribute
no created edges, and composition and tensor concatenate the serializations of their parts.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.BitMap`: compositional serialization of transformed orientations.

## Main results

* `Cslib.Complexity.NCL.Diagram.BitMap.bits_comp_realization`: stacked realizations concatenate.
* `Cslib.Complexity.NCL.Diagram.BitMap.bits_tensor_realization`: juxtaposed realizations
  concatenate.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

/-- A serialization of transformed orientations respecting the diagram operations. -/
structure BitMap (Γ : List Color → List Color → Type) where
  /-- Serialize the created edges of a transformed orientation. -/
  bits : {a b : List Color} → (D : Diagram Γ a b) → (D.Edge → Bool) → List Bool
  /-- Identity wires create no bits. -/
  bits_id (a : List Color) (s : (Diagram.id (Γ := Γ) a).Edge → Bool) :
    bits (Diagram.id a) s = []
  /-- A stack contributes the bits of its two parts in order. -/
  bits_comp {a b c : List Color} (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
      (s : (D₁.comp D₂).Edge → Bool) :
    bits (D₁.comp D₂) s = bits D₁ (s ∘ compLeft D₁ D₂) ++ bits D₂ (s ∘ compRight D₁ D₂)
  /-- A juxtaposition contributes the left bits before the right bits. -/
  bits_tensor {a b c d : List Color} (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
      (s : (D₁.tensor D₂).Edge → Bool) :
    bits (D₁.tensor D₂) s = bits D₁ (s ∘ tensorLeft D₁ D₂) ++ bits D₂ (s ∘ tensorRight D₁ D₂)

namespace BitMap

variable {Γ : List Color → List Color → Type} {I : Interp Γ} (B : BitMap Γ)
  {a b c d : List Color}

/-- Stacked realizations serialize by concatenation. -/
theorem bits_comp_realization {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    {x y z : List Bool} (R₁ : Realization I D₁ x y) (R₂ : Realization I D₂ y z) :
    B.bits (D₁.comp D₂) (R₁.comp R₂).orient = B.bits D₁ R₁.orient ++ B.bits D₂ R₂.orient := by
  rw [B.bits_comp, Realization.comp_orient_compLeft, Realization.comp_orient_compRight]

/-- Juxtaposed realizations serialize by concatenation. -/
theorem bits_tensor_realization {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d}
    {x y z u : List Bool} (R₁ : Realization I D₁ x y) (R₂ : Realization I D₂ z u) :
    B.bits (D₁.tensor D₂) (R₁.tensor R₂).orient = B.bits D₁ R₁.orient ++ B.bits D₂ R₂.orient := by
  rw [B.bits_tensor, Realization.tensor_orient_tensorLeft, Realization.tensor_orient_tensorRight]

/-- Inactive stacked orientations serialize by concatenation. -/
theorem bits_comp_zero (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) :
    B.bits (D₁.comp D₂) (fun _ => false) =
      B.bits D₁ (fun _ => false) ++ B.bits D₂ (fun _ => false) :=
  B.bits_comp D₁ D₂ (fun _ => false)

/-- Inactive juxtaposed orientations serialize by concatenation. -/
theorem bits_tensor_zero (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d) :
    B.bits (D₁.tensor D₂) (fun _ => false) =
      B.bits D₁ (fun _ => false) ++ B.bits D₂ (fun _ => false) :=
  B.bits_tensor D₁ D₂ (fun _ => false)

end BitMap

end Cslib.Complexity.NCL.Diagram
