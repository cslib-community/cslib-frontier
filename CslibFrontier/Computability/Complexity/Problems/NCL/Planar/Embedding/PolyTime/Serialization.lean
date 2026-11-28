/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Fragments
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.BitMap
import Mathlib.Tactic.FinCases

/-!
# Canonical configuration serialization for incidence drawings

Serialize the exact extension supplied by the canonical planarization simulation. It respects
composition and tensor for arbitrary source orientations, and its local values are precisely
the fixed source, cap, and crossover configuration table.

## Main definitions

* `Planar.Embedding.PolyTime.extendedBits`: created bits of the actual canonical extension.
* `Planar.Embedding.PolyTime.bitMap`: its compositional serialization interface.

## Main results

* `Planar.Embedding.PolyTime.extendedBits_source`, `extendedBits_cap`, `extendedBits_swap`:
  exact agreement with the finite configuration table.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding.PolyTime

open Diagram

/-- Created-edge bits of the actual canonical planarization of an incidence drawing. -/
@[expose] def extendedBits {a b : List Color} (D : Diagram Cell a b) (s : D.Edge → Bool) :
    List Bool :=
  (planarizeAlong Cell.expand D).innerBits
    ((planarizeAlongSimulation Cell.interp_forward Cell.expandOpenSim D).enc s)

/-- Canonical incidence planarization as a compositional created-edge bit map. -/
@[expose] def bitMap : BitMap Cell where
  bits := extendedBits
  bits_id _ _ := rfl
  bits_comp D₁ D₂ s := by
    change ((openSimSubst (Routed.expandOpenSim Cell.expandOpenSim) (Route.diagram D₁)).comp
      (openSimSubst (Routed.expandOpenSim Cell.expandOpenSim) (Route.diagram D₂))).bits
        (Route.enc (D₁.comp D₂) s) = _
    rw [OpenSim.bits_comp, Route.enc_compLeft, Route.enc_compRight]
    rfl
  bits_tensor D₁ D₂ s := by
    change ((openSimSubst (Routed.expandOpenSim Cell.expandOpenSim) (Route.diagram D₁)).tensor
      (openSimSubst (Routed.expandOpenSim Cell.expandOpenSim) (Route.diagram D₂))).bits
        (Route.enc (D₁.tensor D₂) s) = _
    rw [OpenSim.bits_tensor, Route.enc_tensorLeft, Route.enc_tensorRight]
    rfl

/-- Serialize the actual planar extension after assigning arbitrary directions to wire labels. -/
@[expose] def labelledBits {Label : Type} {a b : List Color} {xs ys : List Label}
    {D : Diagram Cell a b} (L : Labeling D xs ys) (u : Label → Bool) : List Bool :=
  bitMap.bits D (u ∘ L.label)

/-- Stacked labeled diagrams serialize componentwise for every label orientation. -/
theorem labelledBits_comp {Label : Type} {a b c : List Color}
    {xs ys zs : List Label} {D : Diagram Cell a b} {D' : Diagram Cell b c}
    (L : Labeling D xs ys) (L' : Labeling D' ys zs) (u : Label → Bool) :
    labelledBits (L.comp L') u = labelledBits L u ++ labelledBits L' u := by
  unfold labelledBits
  rw [bitMap.bits_comp]
  simp only [Function.comp_assoc, Labeling.comp_label_left, Labeling.comp_label_right]

/-- Juxtaposed labeled diagrams serialize from left to right. -/
theorem labelledBits_tensor {Label : Type} {a b c d : List Color}
    {xs ys zs ws : List Label} {D : Diagram Cell a b} {D' : Diagram Cell c d}
    (L : Labeling D xs ys) (L' : Labeling D' zs ws) (u : Label → Bool) :
    labelledBits (L.tensor L') u = labelledBits L u ++ labelledBits L' u := by
  unfold labelledBits
  rw [bitMap.bits_tensor]
  simp only [Function.comp_assoc, Labeling.tensor_label_left, Labeling.tensor_label_right]

/-- Straight labeled wires create no bits. -/
theorem labelledBits_id {Label : Type} (a : List Color) (xs : List Label)
    (h : xs.length = a.length) (u : Label → Bool) :
    labelledBits (Labeling.id (Γ := Cell) a xs h) u = [] := rfl

/-- The source template serializes its three original downward stubs. -/
theorem extendedBits_source (c d e : Color) (u : Fin 3 → Bool) :
    extendedBits (gen (.source [c, d, e] 2)) (Sum.elim Fin.elim0 u) =
      (Opcode.source c d e (u 0) (u 1) (u 2)).configuration := by
  rfl

/-- The cap uses exactly its fixed canonical two-input extension. -/
theorem extendedBits_cap (c : Color) (u : Fin 2 → Bool) :
    extendedBits (gen (.cap c)) (Sum.elim u Fin.elim0) =
      (Opcode.cap c (u 0) (u 1)).configuration := by
  change (Cell.expandOpenSim (.cap c)).bits (Sum.elim u Fin.elim0) = _
  apply congrArg (Cell.expandOpenSim (.cap c)).bits
  funext i
  rcases i with i | i
  · fin_cases i <;> rfl
  · exact i.elim0

/-- The crossover table follows the original top bits along the two routed wires. -/
theorem extendedBits_swap (c d : Color) (u : Fin 2 → Bool) :
    extendedBits (swap (Γ := Cell) c d) (Sum.elim u Empty.elim) =
      (Opcode.cross c d (u 0) (u 1)).configuration := by
  change ((Routed.expandOpenSim Cell.expandOpenSim) (Routed.cross c d)).bits
    (Route.enc (swap (Γ := Cell) c d) (Sum.elim u Empty.elim)) = _
  change (Crossover.openSim c d).bits
    ((Sum.elim u Empty.elim) ∘ Route.forget (swap (Γ := Cell) c d)) = _
  apply congrArg (Crossover.openSim c d).bits
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

end Cslib.Complexity.NCL.Planar.Embedding.PolyTime
