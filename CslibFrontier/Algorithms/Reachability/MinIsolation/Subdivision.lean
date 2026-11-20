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

private theorem nonempty_path_iff_reachable {W : Type*} (r : W → W → Prop) (a b : W) :
    Nonempty (@Quiver.Path W ⟨fun u v => PLift (r u v)⟩ a b) ↔
      Relation.ReflTransGen r a b := by
  let _ : Quiver W := ⟨fun u v => PLift (r u v)⟩
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl
    | cons _ e ih => exact ih.tail e.down
  · intro h
    induction h with
    | refl => exact ⟨.nil⟩
    | tail _ e ih => exact ih.map (fun p => p.cons ⟨e⟩)

omit [Fintype V] in
/-- Reachability between subdivision roots is exactly reachability between the original
vertices, for every weight assignment within the subdivision bound. -/
theorem reachable_root_iff (hw : ∀ v, weight v ≤ bound) (s t : V) :
    Relation.ReflTransGen (graph G weight bound).Adj (root bound s) (root bound t) ↔
      Relation.ReflTransGen G.Adj s t := by
  let e := pathEquiv (G := G) hw s (root bound t) (Nat.zero_le _)
  rw [← nonempty_path_iff_reachable, ← nonempty_path_iff_reachable]
  exact ⟨fun h => h.map e.symm, fun h => h.map e⟩

/-- Every breadth-first round of a subdivided min-isolating graph has exactly one successful
unweighted scan transcript, including its choices at auxiliary vertices. -/
theorem existsUnique_passes_of_isMinIsolating (hw : ∀ v, weight v ≤ bound)
    (hG : G.IsMinIsolating weight) (s : V) (k : ℕ) :
    ∃! w, DoubleCounting.Passes (graph G weight bound).Adj (root bound s) k w := by
  let _ := toQuiver G weight bound
  have hrel := nonempty_hom_eq_adj (G := G) (weight := weight) (bound := bound)
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
  have hrel := nonempty_hom_eq_adj (G := G) (weight := weight) (bound := bound)
  have hchain (p : Path G weight bound (root bound s) (root bound t)) :
      p.vertices.IsChainFromTo r (root bound s) (root bound t) := by
    have h := p.vertices_isChainFromTo
    change p.vertices.IsChainFromTo
      (fun a b => Nonempty (@Quiver.Hom _ (toQuiver G weight bound) a b)) _ _ at h
    rwa [hrel] at h
  obtain ⟨p⟩ := hex
  have ht : root bound t ∈ DoubleCounting.round r (root bound s) k := by
    rw [DoubleCounting.mem_round, Relation.reachableWithin_eq_of_card_le hcard]
    exact (hchain (E p)).reflTransGen
  obtain ⟨l, ⟨hl, llen⟩, huniq⟩ := (DoubleCounting.existsUnique_passes_iff.mp
    ((relabel s).mpr (h s))) _ ht
  let Q := @Quiver.Path.equivChain _ (toQuiver G weight bound) _ (root bound s) (root bound t)
  have hl' : l.IsChainFromTo
      (fun a b => Nonempty (@Quiver.Hom _ (toQuiver G weight bound) a b))
      (root bound s) (root bound t) := by rw [hrel]; exact hl
  let q := Q.symm ⟨l, hl'⟩
  have hqv : q.vertices = l := by
    simpa only [Q, Quiver.Path.equivChain_apply] using
      congrArg Subtype.val (Q.apply_symm_apply ⟨l, hl'⟩)
  have hqLen : q.length = DoubleCounting.distance r (root bound s) (root bound t) := by
    have h := q.vertices_length
    rw [hqv, llen] at h
    omega
  have hle (p' : Path G weight bound (root bound s) (root bound t)) :
      q.length ≤ p'.length := by
    rw [hqLen]
    exact (DoubleCounting.distance_spec
      ⟨_, le_rfl, (hchain p').relatesInSteps p'.vertices_length⟩).2
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
    exact huniq _ ⟨hchain (E p'), by
      rw [(E p').vertices_length, le_antisymm hmin (hle (E p')), hqLen]⟩

end Cslib.LayeredDigraph.Subdivision
