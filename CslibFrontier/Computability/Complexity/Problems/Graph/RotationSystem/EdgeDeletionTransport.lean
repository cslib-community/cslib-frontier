/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Equality
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletion
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionGenus

/-!
# Edge deletion between explicit positional transports

A literal view of the source as a prefix plus its last edge allows deletion, followed by
endpoint-fiber and reversal preserving reindexing into an actual target graph. All numerical
genus obligations are discharged internally by deletion and transport. A nonloop edge can
also be deleted at its original index, retaining the vertex list, dart coordinates and the
literal successor rule on the remaining rotation.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- A source equality, last-edge deletion and explicit target dart map preserve numerical
genus. Neither endpoint name injection nor a connectedness/cofaciality hypothesis is needed.
Endpoint declaration is required only on the actual source and actual target graphs. -/
theorem numericalGenusZero_deleteLastEdge_transport {S G T : Graph} {u v : ℕ}
    (r : RotationSystem S) (h : S = lastEdgeGraph G u v) (e : Dart G ≃ Dart T)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (he : ∀ a, e a.reverse = (e a).reverse)
    (hS : ∀ w ∈ S.incidenceVertices, w ∈ S.vertices)
    (hT : ∀ w ∈ T.incidenceVertices, w ∈ T.vertices) (hr : r.NumericalGenusZero) :
    (((r.transport (graphEqDartEquiv h)
      (by intro a b; rw [vertex_graphEqDartEquiv, vertex_graphEqDartEquiv])).deleteLastEdge
        (G := G) (u := u) (v := v)).transport e hv).NumericalGenusZero := by
  cases h
  exact r.deleteLastEdge.numericalGenusZero_transport (H := T) e hv he
    (endpoints_declared_deleteLastEdge hS) hT (r.numericalGenusZero_deleteLastEdge hS hr)

/-- Delete one nonloop occurrence in a genus-zero rotation. The surviving darts lift to
their original endpoint names, end tags, and edge indices. Their clockwise successor is
the original one unless it hits a deleted dart, in which case it skips that dart. -/
theorem exists_numericalGenusZero_deleteNonloopEdge {G : Graph} (r : RotationSystem G)
    (hG : ∀ w ∈ G.incidenceVertices, w ∈ G.vertices) (hr : r.NumericalGenusZero)
    (i : Fin G.edges.length) (hi : Dart.vertex (G := G) (i, false) ≠ Dart.vertex (i, true)) :
    ∃ (H : Graph) (s : RotationSystem H) (lift : Dart H ↪ Dart G),
      H.vertices = G.vertices ∧ H.edges = G.edges.eraseIdx i.val ∧ s.NumericalGenusZero ∧
      (∀ d, (lift d).vertex = d.vertex ∧ (lift d).2 = d.2 ∧
        (lift d).1.val = if d.1.val < i.val then d.1.val else d.1.val + 1) ∧
      ∀ a b, s.rotate a = b ↔ r.rotate (lift a) = lift b ∨
        ∃ tag, r.rotate (lift a) = (i, tag) ∧ r.rotate (i, tag) = lift b := by
  obtain ⟨H, u, v, p, hV, hEdges, _, hcoord, hpos, hlast, hu, hv⟩ := G.exists_lastEdge_reindex i
  let E : Dart G ≃ Dart (lastEdgeGraph H u v) := p.prodCongr (Equiv.refl Bool)
  have hvertex (d : Dart G) : (E d).vertex = d.vertex := hcoord d.1 d.2
  have hf (a b : Dart G) : (E a).vertex = (E b).vertex ↔ a.vertex = b.vertex := by
    rw [hvertex, hvertex]
  have hL := endpoints_declared_edge_reindex p hcoord (fun w => by
    change w ∈ G.vertices ↔ w ∈ H.vertices
    rw [hV]) hG
  let t := r.transport E hf
  have ht : t.NumericalGenusZero :=
    r.numericalGenusZero_transport E hf (fun _ => rfl) hG hL hr
  let retain := retainedLastEdgeDart H u v
  let lift : Dart H ↪ Dart G := ⟨fun d => E.symm (retain d),
    fun _ _ h => Option.some.inj (Option.some.inj
      ((lastEdgeDartEquiv H u v).symm.injective (E.symm.injective h)))⟩
  have drop (tag : Bool) : E (i, tag) = lastEdgeDart H u v tag := by
    cases tag <;> exact Prod.ext hlast rfl
  refine ⟨H, t.deleteLastEdge, lift, hV, hEdges,
    t.numericalGenusZero_deleteLastEdge hL ht, ?_, ?_⟩
  · intro d
    have hx : (E (lift d)).vertex = (lift d).vertex := hvertex (lift d)
    rw [show E (lift d) = retain d from E.apply_symm_apply _] at hx
    refine ⟨hx.symm.trans (vertex_retainedLastEdgeDart H u v d), ?_, ?_⟩
    · rcases d with ⟨_, _ | _⟩ <;> rfl
    · have hne : (lift d).1 ≠ i := fun he => by
        have hp : p (p.symm (retain d).1) = p i := congrArg p he
        rw [p.apply_symm_apply, hlast] at hp
        exact (Nat.ne_of_lt d.1.isLt) (congrArg Fin.val hp)
      have hp := hpos (lift d).1 hne
      change (p (p.symm (retain d).1)).val = _ at hp
      rw [p.apply_symm_apply] at hp
      change d.1.val = if (lift d).1 < i then (lift d).1.val else (lift d).1.val - 1 at hp
      have hn : (lift d).1.val ≠ i.val := fun h => hne (Fin.ext h)
      split at hp <;> split_ifs <;> omega
  · intro a b
    have skip (x y : Dart (lastEdgeGraph H u v)) :
        t.rotate x = y ↔ r.rotate (E.symm x) = E.symm y := by
      change E (r.rotate (E.symm x)) = y ↔ _
      exact E.eq_symm_apply.symm
    have drop' (tag : Bool) : E.symm (lastEdgeDart H u v tag) = (i, tag) :=
      E.symm_apply_eq.mpr (drop tag).symm
    have lift_apply (d : Dart H) : E.symm (retainedLastEdgeDart H u v d) = lift d := rfl
    have hne : u ≠ v := by rwa [hu, hv]
    simpa only [skip, drop', lift_apply] using t.rotate_deleteLastEdge_eq_iff hne a b

end Cslib.Complexity.Graph.RotationSystem
