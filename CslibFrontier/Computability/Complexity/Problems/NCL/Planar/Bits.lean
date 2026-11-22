/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Circuit
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.BitMap

/-!
# Configuration bits after circuit planarization

Routing repeats the directions of the source edges. The crossover and gate simulations then
extend each routed cell canonically. Serializing the result respects composition and tensor.

## Main definitions

* `Cslib.Complexity.NCL.Planar.Circuit.extendedBits`: created-edge bits after planarization.
* `Cslib.Complexity.NCL.Planar.Circuit.bitMap`: the compositional serialization interface.

## Main results

Canonical planar serialization preserves decomposition into sequential and parallel subdiagrams,
including the new edges of their crossovers.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Circuit

open Diagram

variable {a b c d : List Color}

/-- Serialize created-edge directions in the canonical planar circuit configuration. -/
@[expose] def extendedBits (D : Diagram Gate a b) (s : D.Edge → Bool) : List Bool :=
  (diagram D).innerBits ((simulation D).enc s)

/-- Planarizing identity wires creates no bits. -/
theorem extendedBits_id (a : List Color) (s : (Diagram.id (Γ := Gate) a).Edge → Bool) :
    extendedBits (Diagram.id a) s = [] := rfl

/-- Canonical planar extensions serialize a stack component by component. -/
theorem extendedBits_comp (D₁ : Diagram Gate a b) (D₂ : Diagram Gate b c)
    (s : (D₁.comp D₂).Edge → Bool) :
    extendedBits (D₁.comp D₂) s =
      extendedBits D₁ (s ∘ compLeft D₁ D₂) ++ extendedBits D₂ (s ∘ compRight D₁ D₂) := by
  change ((openSimSubst (Routed.expandOpenSim Gate.expandOpenSim) (Route.diagram D₁)).comp
    (openSimSubst (Routed.expandOpenSim Gate.expandOpenSim) (Route.diagram D₂))).bits
      (Route.enc (D₁.comp D₂) s) = _
  rw [OpenSim.bits_comp, Route.enc_compLeft, Route.enc_compRight]
  rfl

/-- Canonical planar extensions serialize a tensor component by component. -/
theorem extendedBits_tensor (D₁ : Diagram Gate a b) (D₂ : Diagram Gate c d)
    (s : (D₁.tensor D₂).Edge → Bool) :
    extendedBits (D₁.tensor D₂) s =
      extendedBits D₁ (s ∘ tensorLeft D₁ D₂) ++ extendedBits D₂ (s ∘ tensorRight D₁ D₂) := by
  change ((openSimSubst (Routed.expandOpenSim Gate.expandOpenSim) (Route.diagram D₁)).tensor
    (openSimSubst (Routed.expandOpenSim Gate.expandOpenSim) (Route.diagram D₂))).bits
      (Route.enc (D₁.tensor D₂) s) = _
  rw [OpenSim.bits_tensor, Route.enc_tensorLeft, Route.enc_tensorRight]
  rfl

/-- Canonical circuit planarization as a compositional bit map. -/
@[expose] def bitMap : BitMap Gate where
  bits := extendedBits
  bits_id := extendedBits_id
  bits_comp := extendedBits_comp
  bits_tensor := extendedBits_tensor

end Cslib.Complexity.NCL.Planar.Circuit
