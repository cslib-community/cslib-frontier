/-
Copyright (c) 2026 Shriya Thakur, Hugo Akitaya, Freddy Stock,
Adriano Corbelino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Akitaya, Shriya Thakur, Freddy Stock, Adriano Corbelino
-/

module

import CslibFrontier.Computability.Complexity.Problems.HittingSet

/-!
# Hitting Set: tests

The hitting test and the verifier on the subsets `{1, 2}`, `{2, 3}`, `{3, 4}` of `{1, 2, 3, 4}`;
hitting sets of at most `2` but not `1` element there; a repeated ground entry, an empty
collection, an empty subset and a subset outside the ground list; the reduction from
`VertexCover` on a graph with a repeated vertex, a self-loop and an edge to an undeclared vertex,
including a target above its number of vertices, and on a triangle that one vertex cannot cover;
and the headline results.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.HittingSet

open Cslib.Complexity Turing.MultiTapeTM

/-- The subsets `{1, 2}`, `{2, 3}` and `{3, 4}` of `{1, 2, 3, 4}`. -/
private def chain : SetSystem := ⟨[1, 2, 3, 4], [[1, 2], [2, 3], [3, 4]]⟩

/-- The repeated vertex `0`, the self-loop at `0`, the edge `0 - 1` and an edge to the undeclared
vertex `5`. -/
private def junk : Graph := ⟨[0, 0, 1], [(0, 0), (0, 1), (1, 5)]⟩

/-- The triangle on `0`, `1` and `2`. -/
private def triangle : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2), (0, 2)]⟩

/-! ### Headline results -/

example : HittingSet ∈ NP encHittingSet ∧ NPHard encHittingSet HittingSet ∧
    PolyTimeReducible encVertexCoverInstance encHittingSet VertexCover HittingSet :=
  ⟨HittingSet_npComplete.1, HittingSet_npComplete.2, polyTimeReducible_VertexCover_HittingSet⟩

example : ComputableInPolyTime (fun x : HittingSetInstance => x.system.sets)
    encHittingSet encNatSetList := by fun_prop

example : ComputableInPolyTime (fun x : SetSystem × ℕ => HittingSetInstance.mk x.1 x.2)
    (encPair encSetSystem encNat) encHittingSet := by fun_prop

/-! ### The hitting test and the verifier -/

-- `{2, 3}` meets every subset; `{2}` misses `{3, 4}`.
example : HittingSet.isHitting chain.sets [2, 3] = true := by decide
example : HittingSet.isHitting chain.sets [2] = false := by decide

-- An empty collection is always hit, and an empty subset never is.
example : HittingSet.isHitting [] [] = true := by decide
example : HittingSet.isHitting [[]] [1, 2] = false := by decide

-- The certificate is a mask on the ground list: it selects `2` and `3`.
example : HittingSet.verifier (⟨chain, 2⟩, [false, true, true, false]) = true := by decide
-- Two selected elements are too many for `k = 1`, and `2` alone misses `{3, 4}`.
example : HittingSet.verifier (⟨chain, 1⟩, [false, true, true, false]) = false := by decide
example : HittingSet.verifier (⟨chain, 1⟩, [false, true, false, false]) = false := by decide

-- The repeated ground entry `1` counts once.
example : HittingSet.verifier (⟨⟨[1, 1, 2], [[1]]⟩, 1⟩, [true, true, false]) = true := by decide

/-! ### Hitting sets -/

example : (⟨chain, 2⟩ : HittingSetInstance) ∈ HittingSet :=
  (mem_HittingSet_iff _).2 ⟨{2, 3}, by decide, by decide, by decide⟩

-- One element cannot meet both `{1, 2}` and `{3, 4}`.
example : (⟨chain, 1⟩ : HittingSetInstance) ∉ HittingSet := by
  rw [mem_HittingSet_iff]
  rintro ⟨H, -, hcard, hhit⟩
  obtain ⟨a, ha, h12⟩ := hhit [1, 2] (by decide)
  obtain ⟨b, hb, h34⟩ := hhit [3, 4] (by decide)
  obtain rfl : a = b := Finset.card_le_one.1 hcard a ha b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h12 h34
  omega

-- With `k = 0`, only an empty collection is hit.
example : (⟨⟨[1], []⟩, 0⟩ : HittingSetInstance) ∈ HittingSet :=
  (mem_HittingSet_iff _).2 ⟨∅, by decide, by decide, by decide⟩

-- The subset `{5}` lies outside the ground list, so no choice of ground elements meets it.
example : (⟨⟨[1, 2], [[1], [5]]⟩, 2⟩ : HittingSetInstance) ∉ HittingSet := by
  rw [mem_HittingSet_iff]
  rintro ⟨H, hmem, -, hhit⟩
  obtain ⟨u, hu, h5⟩ := hhit [5] (by decide)
  obtain rfl : u = 5 := List.mem_singleton.1 h5
  exact absurd (hmem 5 hu) (by decide)

/-! ### The reduction from vertex cover -/

-- The declared vertices stay as the ground list, and only the edge `0 - 1` between distinct
-- declared vertices becomes a subset.
example : (VertexCover.toHittingSet ⟨junk, 1⟩).system.ground = [0, 0, 1] := by decide
example : (VertexCover.toHittingSet ⟨junk, 1⟩).system.sets = [[0, 1]] := by decide

-- `junk` has two distinct vertices, so the target `3` gives the fixed instance with only the
-- empty subset.
example : (VertexCover.toHittingSet ⟨junk, 3⟩).system.sets = [[]] := by decide

-- `{0}` hits the edge subsets, so it covers `junk`.
example : (⟨junk, 1⟩ : VertexCoverInstance) ∈ VertexCover :=
  (VertexCover.toHittingSet_mem_iff _).1
    ((mem_HittingSet_iff _).2 ⟨{0}, by decide, by decide, by decide⟩)

-- No set meets the empty subset, matching the absence of a cover of `3` distinct vertices.
example : VertexCover.toHittingSet ⟨junk, 3⟩ ∉ HittingSet := by
  rw [mem_HittingSet_iff]
  rintro ⟨H, -, -, hhit⟩
  obtain ⟨u, -, hu⟩ := hhit [] (by decide)
  exact List.not_mem_nil hu

example : (⟨junk, 3⟩ : VertexCoverInstance) ∉ VertexCover := fun h => by
  have := (mem_VertexCover_iff_exists_card_le.1 h).1
  revert this
  decide

-- `k = 1` is at most the `3` vertices of `triangle`, so no empty subset is added.
example : (VertexCover.toHittingSet ⟨triangle, 1⟩).system.sets = [[0, 1], [1, 2], [0, 2]] := by
  decide

-- One element cannot meet all three edge subsets, so one vertex cannot cover the triangle.
example : (⟨triangle, 1⟩ : VertexCoverInstance) ∉ VertexCover := fun h => by
  rw [← VertexCover.toHittingSet_mem_iff, mem_HittingSet_iff] at h
  obtain ⟨H, -, hcard, hhit⟩ := h
  obtain ⟨a, ha, h01⟩ := hhit [0, 1] (by decide)
  obtain ⟨b, hb, h12⟩ := hhit [1, 2] (by decide)
  obtain ⟨c, hc, h02⟩ := hhit [0, 2] (by decide)
  obtain rfl : a = b := Finset.card_le_one.1 hcard a ha b hb
  obtain rfl : a = c := Finset.card_le_one.1 hcard a ha c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h01 h12 h02
  omega

end CslibFrontierTests.HittingSet
