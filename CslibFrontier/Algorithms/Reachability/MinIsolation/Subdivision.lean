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
has exactly one successful transcript in each round. Conversely, unique transcripts at
every original source in a saturated round certify min-isolation. The criterion applies
under any relabeling, including consecutive row-major IDs for the streaming scans.

This is the mathematical transport
step of #6747; the streaming branch implementation and its native resource proof are separate.
-/

public section

namespace Cslib.LayeredDigraph.Subdivision

variable {V : Type*} [Fintype V] {G : LayeredDigraph V} {weight : V → ℕ} {bound : ℕ}

omit [Fintype V] in
private theorem nonempty_hom_eq_adj :
    (fun a b => Nonempty (@Quiver.Hom _ (toQuiver G weight bound) a b)) =
      (graph G weight bound).Adj := by
  funext a b
  exact propext ⟨fun h => h.some.down, fun h => ⟨⟨h⟩⟩⟩

omit [Fintype V] in
/-- The vertex list of a path is a chain of the subdivided graph. -/
private theorem path_isChainFromTo {a b : Vertex V bound} (q : Path G weight bound a b) :
    (@Quiver.Path.vertices _ (toQuiver G weight bound) _ _ q).IsChainFromTo
      (graph G weight bound).Adj a b := by
  let _ := toQuiver G weight bound
  rw [← nonempty_hom_eq_adj]
  exact q.vertices_isChainFromTo

omit [Fintype V] in
/-- Every chain of the subdivided graph is the vertex list of a path. -/
private theorem exists_path_vertices_eq {a b : Vertex V bound} {l : List (Vertex V bound)}
    (hl : l.IsChainFromTo (graph G weight bound).Adj a b) :
    ∃ q : Path G weight bound a b, @Quiver.Path.vertices _ (toQuiver G weight bound) _ _ q = l := by
  let _ := toQuiver G weight bound
  rw [← nonempty_hom_eq_adj] at hl
  obtain ⟨q, hq⟩ := (@Quiver.Path.equivChain _ (toQuiver G weight bound) _ a b).surjective ⟨l, hl⟩
  exact ⟨q, by simpa using congrArg Subtype.val hq⟩

/-- Every breadth-first round of a subdivided min-isolating graph has exactly one successful
unweighted scan transcript, including its choices at auxiliary vertices. -/
theorem existsUnique_passes_of_isMinIsolating (hw : ∀ v, weight v ≤ bound)
    (hG : G.IsMinIsolating weight) (s : V) (k : ℕ) :
    ∃! w, DoubleCounting.Passes (graph G weight bound).Adj (root bound s) k w := by
  let _ := toQuiver G weight bound
  apply DoubleCounting.existsUnique_passes_iff.mpr
  intro v hv
  obtain ⟨hsteps, _⟩ := DoubleCounting.distance_spec (DoubleCounting.mem_round.mp hv)
  obtain ⟨l, hl, hlen⟩ := hsteps.exists_isChainFromTo
  obtain ⟨p₀, hp₀⟩ := exists_path_vertices_eq hl
  obtain ⟨p, hp, huniq⟩ := existsUnique_shortest_of_isMinIsolating hw hG s v ⟨p₀⟩
  have hpmin : p.length = DoubleCounting.distance (graph G weight bound).Adj (root bound s) v := by
    have hle := (DoubleCounting.distance_spec
      (show v ∈ Relation.reachableWithin (graph G weight bound).Adj (root bound s) p.length from
        ⟨_, le_rfl, (path_isChainFromTo p).relatesInSteps p.vertices_length⟩)).2
    have hle' := hp p₀
    have hplen := p₀.vertices_length
    rw [hp₀, hlen] at hplen
    omega
  refine ⟨p.vertices, ⟨path_isChainFromTo p, ?_⟩, ?_⟩
  · rw [p.vertices_length, hpmin]
  · intro l' hl'
    obtain ⟨q, hqv⟩ := exists_path_vertices_eq hl'.1
    have hq : q.length = p.length := by
      have hlen' := q.vertices_length
      rw [hqv, hl'.2] at hlen'
      omega
    exact hqv.symm.trans (congrArg Quiver.Path.vertices (huniq q fun r => hq ▸ hp r))

omit [Fintype V] in
/-- A saturated scan from each original source detects exactly min-isolation. The indexing
equivalence can use `equivProd` followed by `finProdFinEquiv`, as required by a scan over
consecutive row-major vertex IDs. -/
theorem isMinIsolating_iff_indexedPasses {ι : Type*} [Fintype ι]
    (index : Vertex V bound ≃ ι) (hw : ∀ v, weight v ≤ bound)
    {k : ℕ} (hk : Fintype.card ι ≤ k + 1) :
    G.IsMinIsolating weight ↔ ∀ s : V, ∃! w, DoubleCounting.Passes
      (fun u v => (graph G weight bound).Adj (index.symm u) (index.symm v))
      (index (root bound s)) k w := by
  classical
  let _ : Finite V := Finite.of_injective (fun v : V => index (root bound v))
    (fun _ _ h => congrArg Vertex.vertex (index.injective h))
  let _ : Fintype V := Fintype.ofFinite V
  let r := (graph G weight bound).Adj
  have hcard : Nat.card (Vertex V bound) ≤ k + 1 := by
    rw [Nat.card_congr index, Nat.card_eq_fintype_card]
    exact hk
  have relabel (s : V) := DoubleCounting.existsUnique_passes_reindex index r (root bound s) k
  refine ⟨fun h s => (relabel s).mp (existsUnique_passes_of_isMinIsolating hw h s k), ?_⟩
  intro h s t hex
  let _ := toQuiver G weight bound
  let E := pathEquiv (G := G) hw s (root bound t) (Nat.zero_le _)
  obtain ⟨p⟩ := hex
  have ht : root bound t ∈ DoubleCounting.round r (root bound s) k := by
    rw [DoubleCounting.mem_round, Relation.reachableWithin_eq_of_card_le hcard]
    exact (path_isChainFromTo (E p)).reflTransGen
  obtain ⟨l, ⟨hl, llen⟩, huniq⟩ := (DoubleCounting.existsUnique_passes_iff.mp
    ((relabel s).mpr (h s))) _ ht
  obtain ⟨q, hqv⟩ := exists_path_vertices_eq hl
  have hqLen : q.length = DoubleCounting.distance r (root bound s) (root bound t) := by
    have h := q.vertices_length
    rw [hqv, llen] at h
    omega
  have hle (p' : Path G weight bound (root bound s) (root bound t)) :
      q.length ≤ p'.length := by
    rw [hqLen]
    exact (DoubleCounting.distance_spec
      ⟨_, le_rfl, (path_isChainFromTo p').relatesInSteps p'.vertices_length⟩).2
  refine ⟨E.symm q, isMinOn_univ_iff.mpr fun p' => ?_, fun p' hp' => ?_⟩
  · apply (length_pathEquiv_le_iff hw s (root bound t) (Nat.zero_le _) (E.symm q) p').mp
    change (E (E.symm q)).length ≤ (E p').length
    simpa only [E.apply_symm_apply] using hle (E p')
  · apply E.injective
    rw [E.apply_symm_apply]
    apply Quiver.Path.vertices_injective
    have hmin : (E p').length ≤ q.length := by
      have ho := (length_pathEquiv_le_iff hw s (root bound t) (Nat.zero_le _) p' (E.symm q)).mpr
        (isMinOn_univ_iff.mp hp' (E.symm q))
      change (E p').length ≤ (E (E.symm q)).length at ho
      simpa only [E.apply_symm_apply] using ho
    rw [hqv]
    exact huniq _ ⟨path_isChainFromTo (E p'), by
      rw [(E p').vertices_length, le_antisymm hmin (hle (E p')), hqLen]⟩

end Cslib.LayeredDigraph.Subdivision
