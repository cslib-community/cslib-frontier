/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Routing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership

/-!
# Polynomial-time incidence instruction emission

Enumerate edge pairs using the supplied initial bit list. Source ports retain binary edge
names; reading their directions uses binary list lookup. Every loop therefore ranges over an
explicit input list, including on arbitrary graph records.

## Main definitions

* `Planar.Embedding.PolyTime.Emit.program`: source, routing, and cap instructions.

## Main results

* `Planar.Embedding.PolyTime.Emit.computableInPolyTime_program`: standard PT emission.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding.PolyTime.Emit

open Diagram _root_.Turing.MultiTapeTM

/-- Determine an edge's color by scanning its explicit incidences for weight two. -/
@[expose] def edgeColor (g : AndOrGraph) (e : ℕ) : Color :=
  if (g.vertices.flatMap Vertex.ports).any (fun p => p.port.edge == e && p.weight == 2)
  then .blue else .red

/-- One original incidence, colored and oriented downward by the stub convention. -/
@[expose] def wire (g : AndOrGraph) (bits : List Bool) (p : Port ℕ) : Wire :=
  ⟨p, edgeColor g p.edge, xor (bits.getD p.edge false) p.dir⟩

/-- Original incidence order, retaining the original vertex and port order. -/
@[expose] def available (g : AndOrGraph) (bits : List Bool) : List Wire :=
  (g.vertices.flatMap Vertex.ports).map fun p => wire g bits p.port

/-- The requested false/true endpoint pairs; the bound is the explicit input bit-list length. -/
@[expose] def requested (x : AndOrNCL.Instance) (bits : List Bool) : List Wire :=
  (List.range x.initial.length).flatMap fun e =>
    [wire x.graph bits ⟨e, false⟩, wire x.graph bits ⟨e, true⟩]

private def firstPort (v : Vertex ℕ) (i : ℕ) : Port ℕ :=
  (v.ports.getD i ⟨⟨0, false⟩, 0⟩).port

/-- Source instructions, with three consecutive output stubs at each vertex. -/
def sources (x : AndOrNCL.Instance) (bits : List Bool) : Program :=
  x.graph.vertices.zipIdx.map fun p =>
    let a := wire x.graph bits (firstPort p.1 0)
    let b := wire x.graph bits (firstPort p.1 1)
    let c := wire x.graph bits (firstPort p.1 2)
    (3 * p.2, Opcode.source a.color b.color c.color a.bit b.bit c.bit)

/-- Cap one consecutive pair at a time at the leftmost remaining position. -/
@[expose] def caps (x : AndOrNCL.Instance) (bits : List Bool) : Program :=
  (List.range x.initial.length).map fun e =>
    (0, Opcode.cap (edgeColor x.graph e)
      (wire x.graph bits ⟨e, false⟩).bit (wire x.graph bits ⟨e, true⟩).bit)

/-- The actual source, adjacent-swap routing, and cap instruction stream. -/
@[expose] def program (x : AndOrNCL.Instance) (bits : List Bool) : Program :=
  sources x bits ++ RoutingData.program ⟨requested x bits, available x.graph bits, 0⟩ ++ caps x bits

@[fun_prop]
private theorem computableInPolyTime_edgeColor {α : Type} {input : α ↪ List Bool}
    {g : α → AndOrGraph} {e : α → ℕ}
    (hg : ComputableInPolyTime g input encAndOrGraph)
    (he : ComputableInPolyTime e input encNat) :
    ComputableInPolyTime (fun a => edgeColor (g a) (e a)) input encColor := by
  have hl : ComputableInPolyTime (fun a => (g a).vertices.flatMap Vertex.ports) input
      (encWeightedPorts encNat) := by fun_prop
  have hp : ComputableInPolyTime (fun p : α × WeightedPort ℕ => p.2.port.edge)
      (encPair input (encWeightedPort encNat)) encNat := by fun_prop
  have he' := he.comp (ComputableInPolyTime.fst input (encWeightedPort encNat))
  have hw : ComputableInPolyTime (fun p : α × WeightedPort ℕ => p.2.weight)
      (encPair input (encWeightedPort encNat)) encNat := by fun_prop
  have ht := ComputableInPolyTime.bool_and' (hp.beq he') (hw.beq (.const 2))
  have hc : ComputableInPolyTime (fun b => if b then Color.blue else Color.red)
      encBool encColor := .of_finite _
  exact hc.comp (ComputableInPolyTime.anyWithInput hl ht)

@[fun_prop]
private theorem computableInPolyTime_wire {α : Type} {input : α ↪ List Bool}
    {g : α → AndOrGraph} {bits : α → List Bool} {p : α → Port ℕ}
    (hg : ComputableInPolyTime g input encAndOrGraph)
    (hb : ComputableInPolyTime bits input (encList encBool))
    (hp : ComputableInPolyTime p input (encPort encNat)) :
    ComputableInPolyTime (fun a => wire (g a) (bits a) (p a)) input encWire := by
  have hread := ComputableInPolyTime.listGetD_binary (encA := encBool) false hb
    (by fun_prop : ComputableInPolyTime (fun a => (p a).edge) input encNat)
  unfold wire
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_firstPort {α : Type} {input : α ↪ List Bool}
    {v : α → Vertex ℕ} {i : α → ℕ}
    (hv : ComputableInPolyTime v input (encVertex encNat))
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => firstPort (v a) (i a)) input (encPort encNat) := by
  unfold firstPort
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_sources :
    ComputableInPolyTime (fun p : AndOrNCL.Instance × List Bool => sources p.1 p.2)
      (encPair encAndOrNCL (encList encBool)) encProgram := by
  unfold sources encProgram Word.Fixed.Language.encProgram
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_caps :
    ComputableInPolyTime (fun p : AndOrNCL.Instance × List Bool => caps p.1 p.2)
      (encPair encAndOrNCL (encList encBool)) encProgram := by
  unfold caps encProgram Word.Fixed.Language.encProgram
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_requested :
    ComputableInPolyTime (fun p : AndOrNCL.Instance × List Bool => requested p.1 p.2)
      (encPair encAndOrNCL (encList encBool)) encWires := by
  unfold requested
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_available :
    ComputableInPolyTime (fun p : AndOrGraph × List Bool => available p.1 p.2)
      (encPair encAndOrGraph (encList encBool)) encWires := by
  unfold available
  fun_prop

/-- Emit the complete instruction stream using standard framed encodings. -/
@[fun_prop]
theorem computableInPolyTime_program :
    ComputableInPolyTime (fun p : AndOrNCL.Instance × List Bool => program p.1 p.2)
      (encPair encAndOrNCL (encList encBool)) encProgram := by
  unfold program
  fun_prop

end Cslib.Complexity.NCL.Planar.Embedding.PolyTime.Emit
