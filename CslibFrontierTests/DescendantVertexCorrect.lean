/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantVertexCorrect
import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantVertexGame
import Mathlib.Data.List.GetD

public section

namespace Turing.MultiTapeTM.DescendantVertex.Tests

open Cslib BalancedSchedules Circuits.Frontier NativeChild PacketPacking
open DescendantEndpoint (Frame)

private def zeroFrame (edges vertices : ℕ) : Frame :=
  Frame.ofSeed (U := vertices) (a := 1) edges (fun _ => 0) 0 0

private theorem zero_symbol (edges vertices v : ℕ) : symbol (zeroFrame edges vertices) v = 0 := by
  simp [zeroFrame, symbol, rankQuery, Frame.ofSeed, RootPortFinish.symbol,
    TrinomialArithmetic.runSelected, TrinomialArithmetic.hash4, TrinomialArithmetic.eval4,
    TrinomialArithmetic.mul, TrinomialArithmetic.reduce, clmul_zero_right]

private theorem zero_retained (edges vertices bound : ℕ) :
    retained (zeroFrame edges vertices) bound = min bound vertices := by
  unfold retained
  simp only [zero_symbol]
  simp [zeroFrame, Frame.ofSeed]

-- These words are fed to the executable native packing, including its complete packet universe.
private def zeroPacking (rows : ℕ) (D : DescribedNetwork (VertexDesc ℕ)) :
    (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ) :=
  let rowWords := List.replicate rows [0]
  let colWords := List.replicate (D.vertices.length - rows) [0]
  ((rowWords, colWords), packingOfWords 1 64 rowWords colWords
    (D.edgeEnds.map fun e => (e.1, e.2 - rows)))

private theorem groups_zero (rows vertices : ℕ) :
    groupsOf rows 0 vertices
        (List.replicate rows [0], List.replicate (vertices - rows) [0]) =
      List.replicate vertices 0 := by
  apply List.ext_getElem (by simp [groupsOf])
  intro v hv _
  have hv' : v < vertices := by simpa only [groupsOf, List.length_map, List.length_range] using hv
  simp only [groupsOf, List.getElem_map, List.getElem_range, List.getElem_replicate]
  by_cases hr : v < rows
  · rw [ite_eq_left hr, List.getD_replicate [0] hr]
    rfl
  · rw [ite_eq_right hr, List.getD_replicate [0] (show v - rows < vertices - rows by omega)]
    rfl

private theorem zero_labels (rows : ℕ) (D : DescribedNetwork (VertexDesc ℕ)) (v : ℕ)
    (hv : v < (zeroFrame D.numEdges D.vertices.length).vertices) :
    symbol (zeroFrame D.numEdges D.vertices.length) v =
      (groupsOf rows 0 D.vertices.length (zeroPacking rows D).1).getD v 0 := by
  rw [zero_symbol]
  change 0 = (groupsOf rows 0 D.vertices.length
    (List.replicate rows [0], List.replicate (D.vertices.length - rows) [0])).getD v 0
  rw [groups_zero, List.getD_replicate 0 (show v < D.vertices.length from hv)]

/-- One row-column edge with two equal original descriptors. -/
def rootNetwork : DescribedNetwork (VertexDesc ℕ) :=
  ⟨1, [([0], .inl 7), ([0], .inl 7)]⟩

private def firstFrame : Frame := zeroFrame rootNetwork.numEdges rootNetwork.vertices.length

private def firstChild : DescribedNetwork (VertexDesc ℕ) :=
  nativeChild [1] 1 0 3 (-1) [4] 1 rootNetwork (zeroPacking 1 rootNetwork)
    [10, 11, 12, 13, 14, 15] 0

private def firstTrace : NativeAncestry rootNetwork [firstFrame] firstChild :=
  .cons .nil [1] 3 (-1) [4] 1 (zeroPacking 1 rootNetwork) [10, 11, 12, 13, 14, 15]
    rfl (zero_labels 1 rootNetwork)

private theorem first_length : firstChild.vertices.length = 4098 := by
  rw [firstChild, length_vertices_nativeChild]
  decide

private theorem first_packet : firstChild.vertices[2]? =
    some ([0, 1], .inr (packetCtx [1] 1 0 3 (-1) [4] 0 0,
      [(true, 0), (false, 0)], [10, 11, 12, 13, 14, 15])) :=
  getElem?_vertices_nativeChild_packet [1] 1 0 3 (-1) [4] 1 rootNetwork
    (zeroPacking 1 rootNetwork) [10, 11, 12, 13, 14, 15] 0 (q := 0) (by decide)

private theorem first_packet_bound : 2 < firstChild.vertices.length := by
  rw [first_length]
  decide

private def secondFrame : Frame := zeroFrame firstChild.numEdges firstChild.vertices.length

private def secondChild : DescribedNetwork (VertexDesc ℕ) :=
  nativeChild [1] 1 0 9 (-3) [99] 2 firstChild (zeroPacking 2 firstChild) [] 0

private def secondTrace : NativeAncestry rootNetwork [secondFrame, firstFrame] secondChild :=
  .cons firstTrace [1] 9 (-3) [99] 2 (zeroPacking 2 firstChild) [] rfl
    (zero_labels 2 firstChild)

private theorem second_packet_bound : 2 < secondChild.vertices.length := by
  have hg : (groupsOf 2 0 firstChild.vertices.length (zeroPacking 2 firstChild).1).getD 2 0 = 0 :=
    (zero_labels 2 firstChild 2 first_packet_bound).symm.trans
      (zero_symbol firstChild.numEdges firstChild.vertices.length 2)
  have h := getElem?_vertices_nativeChild_retained [1] 1 0 9 (-3) [99] 2 firstChild
    (zeroPacking 2 firstChild) [] 0 first_packet_bound hg
  have hindex : ((groupsOf 2 0 firstChild.vertices.length
      (zeroPacking 2 firstChild).1).take 2).count 0 = 2 := by
    change ((groupsOf 2 0 firstChild.vertices.length
      (List.replicate 2 [0], List.replicate (firstChild.vertices.length - 2) [0])).take 2).count 0 =
        2
    rw [groups_zero, List.take_replicate, List.count_replicate_self, first_length]
    decide
  dsimp only at h
  rw [hindex] at h
  exact (List.getElem?_eq_some_iff.mp h).1

private theorem original_birth : HasOrigin firstChild.vertices.length 2 ⟨1, 0⟩ [firstFrame] := by
  refine ⟨first_packet_bound, Or.inl ⟨rfl, ?_⟩⟩
  change 2 = retained (zeroFrame 1 2) 2 + 0
  rw [zero_retained]
  decide

private theorem retained_birth :
    HasOrigin secondChild.vertices.length 2 ⟨1, 0⟩ [secondFrame, firstFrame] := by
  refine ⟨second_packet_bound, Or.inr ⟨by decide, 2, first_packet_bound, ?_, ?_, original_birth⟩⟩
  · exact zero_symbol firstChild.numEdges firstChild.vertices.length 2
  · change 2 = retained (zeroFrame firstChild.numEdges firstChild.vertices.length) 2
    rw [zero_retained]
    rw [first_length]
    decide

-- The supplied frames really are actual finite seeds; their native symbols agree with the
-- mathematical seed labels, rather than relying on an arbitrary symbol-agreement assumption.
example (v : Fin rootNetwork.vertices.length) :
    symbol firstFrame v =
      (NativeChild.EndpointQuery.Labels.ofSeed rootNetwork.vertices.length 1
        (fun _ => 0) 0 0).symbol v :=
  symbol_ofSeed (a := 1) rootNetwork.numEdges (fun _ => 0) 0 0 v

example : rootNetwork.IsRowsFirstBipartite 1 := by decide

/-- A packet born at precision three remains at that precision after retention through a
second genuine seeded native packing whose new packets use precision nine. -/
private theorem inherited_packet_keeps_birth_descriptor :
    (secondChild.vertices[2]?).map Prod.snd =
      some (.inr (packetCtx [1] 1 0 3 (-1) [4] 0 0,
        [(true, 0), (false, 0)], [10, 11, 12, 13, 14, 15])) := by
  rw [secondTrace.descriptor_eq_birthDescriptor retained_birth]
  change (firstChild.vertices[retained firstFrame firstFrame.vertices + 0]?).map Prod.snd = _
  have hrank : retained firstFrame firstFrame.vertices = 2 := by
    change retained (zeroFrame 1 2) 2 = 2
    rw [zero_retained]
    decide
  rw [hrank, Nat.add_zero, first_packet]
  rfl

example (origin : Origin)
    (h : HasOrigin secondChild.vertices.length 2 origin [secondFrame, firstFrame]) :
    origin = ⟨1, 0⟩ := h.unique retained_birth

example : ∃! origin, HasOrigin secondChild.vertices.length 2 origin [secondFrame, firstFrame] :=
  secondTrace.existsUnique_origin second_packet_bound

-- The complete fixed quantified program accepts this actual two-level provenance.
example : MultiTapeATM.QuantifiedWord.plays (fun xs =>
    program (⟨[secondFrame, firstFrame], secondChild.vertices.length, 2, ⟨1, 0⟩⟩, xs) = true)
    [] (flags [secondFrame, firstFrame]) := by
  have horigin := retained_birth
  generalize hframes : [secondFrame, firstFrame] = frames at horigin ⊢
  generalize hvertices : secondChild.vertices.length = vertices at horigin ⊢
  exact (plays_program ⟨frames, vertices, 2, ⟨1, 0⟩⟩).mpr horigin

-- The same real vertex cannot be claimed as a packet born at the newer split.
example : ¬ MultiTapeATM.QuantifiedWord.plays (fun xs =>
    program (⟨[secondFrame, firstFrame], secondChild.vertices.length, 2, ⟨2, 0⟩⟩, xs) = true)
    [] (flags [secondFrame, firstFrame]) := by
  have horigin := retained_birth
  generalize hframes : [secondFrame, firstFrame] = frames at horigin ⊢
  generalize hvertices : secondChild.vertices.length = vertices at horigin ⊢
  intro h
  have ho := (plays_program ⟨frames, vertices, 2, ⟨2, 0⟩⟩).mp h
  have heq := HasOrigin.unique ho horigin
  have hbad : (2 : ℕ) = 1 := congrArg Origin.stage heq
  omega

-- A query at the exact child length is rejected even with a genuine earlier packet origin.
example : ¬ MultiTapeATM.QuantifiedWord.plays (fun xs =>
    program (⟨[secondFrame, firstFrame], secondChild.vertices.length,
      secondChild.vertices.length, ⟨1, 0⟩⟩, xs) = true) [] (flags [secondFrame, firstFrame]) := by
  generalize hframes : [secondFrame, firstFrame] = frames
  generalize hvertices : secondChild.vertices.length = vertices
  intro h
  have ho := (plays_program ⟨frames, vertices, vertices, ⟨1, 0⟩⟩).mp h
  cases frames <;> exact Nat.lt_irrefl _ ho.1

end Turing.MultiTapeTM.DescendantVertex.Tests
