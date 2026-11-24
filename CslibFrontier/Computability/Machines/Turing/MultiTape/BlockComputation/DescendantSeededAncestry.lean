/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantBirth
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantEndpointCorrect
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.SeededNativeChild
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# A common seeded ancestry for compressed vertices and endpoints

A split made with `Labels.nativePacking` has exactly the labels stored in `Frame.ofSeed`.
`NativeAncestry.cons_ofSeed` therefore constructs the descriptor ancestry without a separate
label-agreement premise. `Represents.cons_nativeChild` constructs the endpoint representation
for that same native described child, using its actual vertex count and reconstructed edge table.

Both constructors start with the existing empty ancestry and can be iterated: the seeded child
is rows-first by `Labels.isRowsFirstBipartite_nativeChild`. Thus the compressed vertex and edge
queries refer to the same descriptors and ports at each step. These are semantic constructions;
the finite native machines and their clocks are unchanged.
-/

public section

namespace Turing.MultiTapeTM.DescendantVertex

open Cslib BalancedSchedules Circuits.Frontier NativeChild NativeChild.EndpointQuery
open DescendantEndpoint (Frame)

variable {T : Type} {root D : DescribedNetwork (VertexDesc T)} {frames : List Frame}

/-- A split using the supplied seed extends the actual descriptor ancestry. Its word-table
agreement follows from the seed and is not supplied as a premise. -/
@[expose] noncomputable def NativeAncestry.cons_ofSeed (ancestry : NativeAncestry root frames D)
    {a : ℕ} (seed : SeededLabels.Seed D.vertices.length (6 * a)) (i : Fin a) (group : ℕ)
    (fl : List ℕ) (pt : ℕ) (t : ℤ) (ζ : List ℕ) (rows : ℕ) (β : List ℕ) :
    NativeAncestry root (Frame.ofSeed D.numEdges seed i group :: frames)
      (nativeChild fl a i pt t ζ rows D
        ((Labels.ofSeed D.vertices.length a seed i group).nativePacking rows D.edgeEnds)
        β group) :=
  .cons ancestry fl pt t ζ rows
    ((Labels.ofSeed D.vertices.length a seed i group).nativePacking rows D.edgeEnds)
    β rfl fun v hv => by
      change v < D.vertices.length at hv
      let l := Labels.ofSeed D.vertices.length a seed i group
      have hsymbol := symbol_ofSeed D.numEdges seed i group ⟨v, hv⟩
      have hgroups := l.groupsOf_nativePacking rows D.edgeEnds
      change groupsOf rows i D.vertices.length (l.nativePacking rows D.edgeEnds).1 =
        l.groups at hgroups
      change symbol (Frame.ofSeed D.numEdges seed i group) v =
        (groupsOf rows i D.vertices.length (l.nativePacking rows D.edgeEnds).1).getD v 0
      rw [hsymbol, hgroups]
      exact (List.getD_map_range _ 0 hv).symm

end Turing.MultiTapeTM.DescendantVertex

namespace Turing.MultiTapeTM.DescendantEndpoint

open Cslib BalancedSchedules Circuits.Frontier NativeChild NativeChild.EndpointQuery

/-- The compressed seeded endpoint stack represents the actual native child's vertices and
ports, for the same seed and packet/slot table used by its descriptor ancestry. -/
theorem Represents.cons_nativeChild {T : Type} {D : DescribedNetwork (VertexDesc T)}
    {rootVertices : ℕ} {rootEdges : List (ℕ × ℕ)} {frames : List Frame} {rows a : ℕ}
    (parent : Represents rootVertices rootEdges frames D.vertices.length D.edgeEnds)
    (hD : D.IsRowsFirstBipartite rows)
    (seed : SeededLabels.Seed D.vertices.length (6 * a)) (i : Fin a) (group : Fin 64)
    (fl : List ℕ) (pt : ℕ) (t : ℤ) (ζ β : List ℕ) :
    let l := Labels.ofSeed D.vertices.length a seed i group
    let child := nativeChild fl a i pt t ζ rows D (l.nativePacking rows D.edgeEnds) β group
    Represents rootVertices rootEdges (Frame.ofSeed D.numEdges seed i group :: frames)
      child.vertices.length child.edgeEnds := by
  let l := Labels.ofSeed D.vertices.length a seed i group
  have hkeys : ∀ p ∈ D.edgeEnds, p.1 < D.vertices.length ∧ p.2 < D.vertices.length := by
    rw [DescribedNetwork.edgeEnds_eq hD]
    intro p hp
    obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨(D.srcFin hD e).isLt, (D.tgtFin hD e).isLt⟩
  have h := parent.cons seed i group hkeys
  change Represents rootVertices rootEdges
    (Frame.ofSeed D.edgeEnds.length seed i group :: frames)
    (l.groups.count l.group + (l.packing D.edgeEnds).numPackets) (l.edges D.edgeEnds) at h
  have hvertices := l.length_vertices_nativeChild D rfl rows fl pt t ζ β
  have hends := l.edgeEnds_nativeChild D rfl rows hD group.isLt fl pt t ζ β
  rw [← hvertices, ← hends] at h
  have hcount : D.edgeEnds.length = D.numEdges := by
    simp only [DescribedNetwork.edgeEnds, List.length_map, List.length_range]
  rw [hcount] at h
  simpa only [l, Labels.ofSeed] using h

end Turing.MultiTapeTM.DescendantEndpoint

namespace Turing.MultiTapeTM.DescendantBirth

open Cslib BalancedSchedules Circuits.Frontier NativeChild NativeChild.EndpointQuery
open DescendantVertex DescendantEndpoint

/-- The runtime log of a seeded extension returns its creation parameters and selected exponent
slice at the appended birth stage, for every packet index. -/
theorem lookup_cons_ofSeed {T : Type} {root D : DescribedNetwork (VertexDesc T)}
    {frames : List Frame} (ancestry : NativeAncestry root frames D) {a : ℕ}
    (seed : SeededLabels.Seed D.vertices.length (6 * a)) (i : Fin a) (group : ℕ)
    (fl : List ℕ) (pt : ℕ) (t : ℤ) (ζ : List ℕ) (rows : ℕ) (β : List ℕ) (packet : ℕ) :
    lookup (calls (ancestry.cons_ofSeed seed i group fl pt t ζ rows β))
      ⟨frames.length + 1, packet⟩ =
        some ⟨⟨fl, a, i, pt, t, ζ, group⟩, packet, betaSlice i pt β packet⟩ := by
  simp [NativeAncestry.cons_ofSeed, lookup, calls, select, Frame.ofSeed]

end Turing.MultiTapeTM.DescendantBirth
