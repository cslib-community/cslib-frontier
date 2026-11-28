/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.BitMap
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Expansion

/-!
# Configuration bits after circuit-gate expansion

The compositional open simulation supplies canonical primitive configurations. Their bits
concatenate in the same creation order as their diagrams.

## Main definitions

* `Cslib.Complexity.NCL.Gate.extendedBits`: created-edge bits of a primitive expansion.
* `Cslib.Complexity.NCL.Gate.bitMap`: the shared compositional bit-map interface.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Gate

open Diagram

variable {a b c d : List Color}

/-- Serialize the created edges of a circuit orientation after primitive expansion. -/
@[expose] def extendedBits (D : Diagram Gate a b) (s : D.Edge → Bool) : List Bool :=
  (openSimSubst Gate.expandOpenSim D).bits s

/-- Identity wires have no created-edge bits. -/
@[simp] theorem extendedBits_id (a : List Color) (s : (Diagram.id (Γ := Gate) a).Edge → Bool) :
    extendedBits (Diagram.id a) s = [] :=
  OpenSim.bits_idWires (I := Gate.interp) (I' := Prim.interp) a s

/-- Crossings have no created-edge bits. -/
@[simp] theorem extendedBits_swap (x y : Color) (s : (Diagram.swap (Γ := Gate) x y).Edge → Bool) :
    extendedBits (Diagram.swap x y) s = [] :=
  OpenSim.bits_swapWires (I := Gate.interp) (I' := Prim.interp) x y s

/-- Primitive expansion serializes a stack component by component. -/
private theorem extendedBits_comp (D₁ : Diagram Gate a b) (D₂ : Diagram Gate b c)
    (s : (D₁.comp D₂).Edge → Bool) :
    extendedBits (D₁.comp D₂) s =
      extendedBits D₁ (s ∘ compLeft D₁ D₂) ++ extendedBits D₂ (s ∘ compRight D₁ D₂) :=
  OpenSim.bits_comp (openSimSubst expandOpenSim D₁) (openSimSubst expandOpenSim D₂) s

/-- Primitive expansion serializes a juxtaposition component by component. -/
private theorem extendedBits_tensor (D₁ : Diagram Gate a b) (D₂ : Diagram Gate c d)
    (s : (D₁.tensor D₂).Edge → Bool) :
    extendedBits (D₁.tensor D₂) s =
      extendedBits D₁ (s ∘ tensorLeft D₁ D₂) ++ extendedBits D₂ (s ∘ tensorRight D₁ D₂) :=
  OpenSim.bits_tensor (openSimSubst expandOpenSim D₁) (openSimSubst expandOpenSim D₂) s

/-- Canonical primitive expansion as a compositional bit map. -/
@[expose] def bitMap : BitMap Gate where
  bits := extendedBits
  bits_id := extendedBits_id
  bits_comp D₁ D₂ s := by exact extendedBits_comp D₁ D₂ s
  bits_tensor D₁ D₂ s := by exact extendedBits_tensor D₁ D₂ s

end Cslib.Complexity.NCL.Gate
