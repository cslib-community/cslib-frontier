/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The common neighborhood of a finite vertex set

`SimpleGraph.commonNeighborhood G T` consists of the vertices outside `T` adjacent to every
vertex of `T`. In particular, the common neighborhood of the empty set is the whole vertex set.
If `T` is contained in a clique `S`, its common neighborhood retains exactly `S \ T` from `S`.
-/

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The vertices outside `T` that are adjacent to every vertex in `T`. -/
@[expose] def commonNeighborhood (T : Finset V) : Finset V :=
  Finset.univ.filter fun v => v ∉ T ∧ ∀ t ∈ T, G.Adj t v

@[simp] theorem mem_commonNeighborhood {T : Finset V} {v : V} :
    v ∈ G.commonNeighborhood T ↔ v ∉ T ∧ ∀ t ∈ T, G.Adj t v := by
  simp [commonNeighborhood]

@[simp] theorem commonNeighborhood_empty : G.commonNeighborhood ∅ = Finset.univ := by
  ext v
  simp

/-- No seed vertex belongs to its common neighborhood. -/
theorem not_mem_of_mem_commonNeighborhood {T : Finset V} {v : V}
    (hv : v ∈ G.commonNeighborhood T) : v ∉ T :=
  (G.mem_commonNeighborhood.mp hv).1

/-- A seed inside a clique retains every other clique vertex in its common neighborhood. -/
theorem sdiff_subset_commonNeighborhood {S T : Finset V} (hT : T ⊆ S)
    (hS : G.IsClique (S : Set V)) : S \ T ⊆ G.commonNeighborhood T := by
  intro v hv
  obtain ⟨hvS, hvT⟩ := Finset.mem_sdiff.mp hv
  refine G.mem_commonNeighborhood.mpr ⟨hvT, fun t ht => ?_⟩
  exact hS (hT ht) hvS (fun h => hvT (h ▸ ht))

/-- Intersecting a clique with a seed's common neighborhood removes exactly the seed. -/
theorem inter_commonNeighborhood_eq_sdiff {S T : Finset V} (hT : T ⊆ S)
    (hS : G.IsClique (S : Set V)) : S ∩ G.commonNeighborhood T = S \ T := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨hvS, hvU⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_sdiff.mpr ⟨hvS, G.not_mem_of_mem_commonNeighborhood hvU⟩
  · intro v hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hv).1,
      G.sdiff_subset_commonNeighborhood hT hS hv⟩

end SimpleGraph
