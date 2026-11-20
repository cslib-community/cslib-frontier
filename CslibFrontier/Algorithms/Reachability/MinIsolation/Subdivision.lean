/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Digraph.Layered.Subdivision
public import CslibFrontier.Foundations.Combinatorics.Quiver.Path.Chain
public import CslibFrontier.Algorithms.Reachability.DoubleCounting

/-!
# Unique double-counting transcripts for subdivided min-isolating graphs

Vertex-chain subdivision transfers min-isolation to shortest vertex-list walks at every
reachable auxiliary vertex. Thus the existing unweighted double-counting scan contract
has exactly one successful transcript in each round. This is the mathematical transport
step of #6747; the streaming branch implementation and its native resource proof are separate.
-/

public section

namespace Cslib.LayeredDigraph.Subdivision

variable {V : Type*} [Fintype V] {G : LayeredDigraph V} {weight : V → ℕ} {bound : ℕ}

/-- Every breadth-first round of a subdivided min-isolating graph has exactly one successful
unweighted scan transcript, including its choices at auxiliary vertices. -/
theorem existsUnique_passes_of_isMinIsolating (hw : ∀ v, weight v ≤ bound)
    (hG : G.IsMinIsolating weight) (s : V) (k : ℕ) :
    ∃! w, DoubleCounting.Passes (graph G weight bound).Adj (root bound s) k w := by
  let _ := toQuiver G weight bound
  have hrel : (fun a b => Nonempty (@Quiver.Hom _ (toQuiver G weight bound) a b)) =
      (graph G weight bound).Adj := by
    funext a b
    exact propext ⟨fun h => h.some.down, fun h => ⟨⟨h⟩⟩⟩
  apply DoubleCounting.existsUnique_passes_iff.mpr
  intro v hv
  let E := @Quiver.Path.equivChain _ (toQuiver G weight bound) _ (root bound s) v
  obtain ⟨hsteps, _⟩ := DoubleCounting.distance_spec (DoubleCounting.mem_round.mp hv)
  obtain ⟨l, hl, hlen⟩ := hsteps.exists_isChainFromTo
  have hl' : l.IsChainFromTo (fun a b => Nonempty (@Quiver.Hom _ (toQuiver G weight bound) a b))
      (root bound s) v := by rw [hrel]; exact hl
  let p₀ := E.symm ⟨l, hl'⟩
  have hp₀ : p₀.vertices = l := by
    have h := congrArg Subtype.val (E.apply_symm_apply ⟨l, hl'⟩)
    simpa only [E, Quiver.Path.equivChain_apply] using h
  obtain ⟨p, hp, huniq⟩ := existsUnique_shortest_of_isMinIsolating hw hG s v ⟨p₀⟩
  have hchain (q : Path G weight bound (root bound s) v) :
      q.vertices.IsChainFromTo (graph G weight bound).Adj (root bound s) v := by
    have h := q.vertices_isChainFromTo
    change q.vertices.IsChainFromTo
      (fun a b => Nonempty (@Quiver.Hom _ (toQuiver G weight bound) a b)) _ _ at h
    rwa [hrel] at h
  have hpmin : p.length = DoubleCounting.distance (graph G weight bound).Adj (root bound s) v := by
    have hle := (DoubleCounting.distance_spec
      (show v ∈ Relation.reachableWithin (graph G weight bound).Adj (root bound s) p.length from
        ⟨_, le_rfl, (hchain p).relatesInSteps p.vertices_length⟩)).2
    have hle' := hp p₀
    have hplen := p₀.vertices_length
    rw [hp₀, hlen] at hplen
    omega
  refine ⟨p.vertices, ⟨hchain p, ?_⟩, ?_⟩
  · rw [p.vertices_length, hpmin]
  · intro l' hl'
    have hc' : l'.IsChainFromTo
        (fun a b => Nonempty (@Quiver.Hom _ (toQuiver G weight bound) a b))
        (root bound s) v := by rw [hrel]; exact hl'.1
    let q := E.symm ⟨l', hc'⟩
    have hqv : q.vertices = l' := by
      have h := congrArg Subtype.val (E.apply_symm_apply ⟨l', hc'⟩)
      simpa only [E, Quiver.Path.equivChain_apply] using h
    have hq : q.length = p.length := by
      have hlen' := q.vertices_length
      rw [hqv, hl'.2] at hlen'
      omega
    have heq : q = p := huniq q (fun r => hq ▸ hp r)
    exact hqv.symm.trans (congrArg Quiver.Path.vertices heq)

end Cslib.LayeredDigraph.Subdivision
