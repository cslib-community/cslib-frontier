/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Permutation
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Wire
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Gate
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Planarize

/-!
# Cells for a canonical incidence drawing

All original vertices are drawn as source cells. The two incidences of each original edge are
routed together and joined by a wire cap. This alphabet obeys the forward port convention, so
its drawing can be passed directly to the certified planarization pipeline.

## Main definitions

* `Planar.Embedding.Cell`: source vertices and same-color wire caps.
* `Planar.Embedding.Cell.expand`: primitive implementations of these cells.

## Main results

* `Planar.Embedding.Cell.expandOpenSim`: every cell has an open implementation.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding

open Diagram

/-- Source vertices and the wire caps joining pairs of incidences. -/
inductive Cell : List Color → List Color → Type
  /-- Draw all ports of an original vertex below it. -/
  | source (colors : List Color) (need : ℕ) : Cell [] colors
  /-- Join the two incidences of an edge with a degree-two wire vertex. -/
  | cap (color : Color) : Cell [color, color] []

namespace Cell

/-- The threshold of a source cell or a wire cap. -/
@[expose] def need : {a b : List Color} → Cell a b → ℕ
  | _, _, .source _ n => n
  | _, _, .cap c => c.weight

/-- Each cell is one threshold vertex with the standard boundary directions. -/
@[expose] def interp : Interp Cell := .threshold need

/-- The incidence-drawing cells obey the forward port convention. -/
theorem interp_forward : interp.Forward := by
  intro a b g v hv p hp
  exact Gate.interp_forward (Gate.vert (need g)) v hv p hp

/-- Draw sources as primitive vertices and expand caps into their AND/OR implementation. -/
@[expose] def expand : {a b : List Color} → Cell a b → Diagram Prim a b
  | _, _, .source cs n => .gen [genVertex [] cs n]
  | _, _, .cap c => Gadgets.Wire.cap c

/-- Every cell expansion preserves its open interface. -/
@[expose] def expandOpenSim {a b : List Color} (g : Cell a b) :
    OpenSim interp Prim.interp (gen g) (expand g) := by
  cases g with
  | source cs n => exact OpenSim.genOfVerts _ _ rfl
  | cap c =>
    exact (OpenSim.genOfVerts (I := interp) (I' := Prim.interp)
      (.cap c) (Gadgets.Wire.generator [c, c] [] c) rfl).trans (Gadgets.Wire.capOpenSim c)

/-- Cell expansions are plane drawings. -/
theorem expand_planar {a b : List Color} (g : Cell a b) : (expand g).Planar := by
  cases g with
  | source => trivial
  | cap c => exact Gadgets.Wire.cap_planar c

end Cell

end Cslib.Complexity.NCL.Planar.Embedding
