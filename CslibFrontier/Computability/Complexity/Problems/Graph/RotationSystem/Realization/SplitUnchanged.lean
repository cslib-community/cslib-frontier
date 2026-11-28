/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.SplitBlocks

/-!
# Unchanged vertex cycles during actual nonloop contraction

Away from the contracted vertex, the literal successor and all its forward iterates
commute with the retained-dart lift. Distances and intervals are preserved on those
unchanged fibers only; no distance preservation is asserted across the deleted darts.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- A retained end away from the contracted vertex has its original source name. -/
theorem vertex_contractionLift_of_ne {G : Graph} {u v : ℕ}
    (d : Dart (contractLastEdgeGraph G u v)) (hd : d.vertex ≠ v) :
    (contractionLift G u v d).vertex = d.vertex := by
  have hu : (contractionLift G u v d).vertex ≠ u :=
    fun h => hd ((contractionLift_vertex_eq_iff G u v d).mpr (.inl h))
  simpa only [Function.update_of_ne hu, id_eq] using vertex_contractionLift G u v d

/-- The outgoing swap and deletions do not change any other vertex's successor. -/
theorem contractionLift_rotate_of_ne {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (d : Dart (contractLastEdgeGraph G u v)) (hd : d.vertex ≠ v) :
    r.rotate (contractionLift G u v d) =
      contractionLift G u v ((r.contractLastEdge huv).rotate d) := by
  have hlast (side : Bool) : r.rotate (contractionLift G u v d) ≠ lastEdgeDart G u v side :=
    fun h => hd <| (contractionLift_vertex_eq_iff G u v d).mpr <| by
      have hv := (r.vertex_rotate (contractionLift G u v d)).symm.trans (congrArg Dart.vertex h)
      cases side <;> simp only [vertex_lastEdgeDart, Bool.false_eq_true, ↓reduceIte] at hv
      · exact .inl hv
      · exact .inr hv
  rcases r.contractionLift_rotate_cases huv d with h | h | h | h | h
  exacts [h, (hlast true h.1).elim, (hlast false h.1).elim,
    (hlast true h.1).elim, (hlast false h.1).elim]

/-- Every forward iterate commutes with the retained lift on an unchanged vertex fiber. -/
theorem contractionLift_pow_of_ne {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (d : Dart (contractLastEdgeGraph G u v)) (hd : d.vertex ≠ v) (n : ℕ) :
    (r.rotate ^ n) (contractionLift G u v d) =
      contractionLift G u v (((r.contractLastEdge huv).rotate ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    exact r.contractionLift_rotate_of_ne huv _ fun hn => hd <|
      (((r.contractLastEdge huv).sameCycle_iff d _).mp
        (Equiv.Perm.sameCycle_pow_right.mpr .rfl)).trans hn

/-- First-hit distances agree only on vertex fibers untouched by contraction. -/
theorem rotationDistance_contractionLift_of_ne {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (a b : Dart (contractLastEdgeGraph G u v)) (hab : a.vertex = b.vertex) (ha : a.vertex ≠ v) :
    r.rotationDistance (contractionLift G u v a) (contractionLift G u v b) =
      (r.contractLastEdge huv).rotationDistance a b := by
  refine r.rotationDistance_eq _ _ ((vertex_contractionLift_of_ne a ha).trans
    (hab.trans (vertex_contractionLift_of_ne b (fun h => ha (hab.trans h))).symm)) _ ?_
    fun k hk heq => (r.contractLastEdge huv).pow_ne_of_lt_rotationDistance a b hab hk <|
      contractionLift_injective G u v ((r.contractionLift_pow_of_ne huv a ha k).symm.trans heq)
  rw [r.contractionLift_pow_of_ne huv a ha, (r.contractLastEdge huv).pow_rotationDistance a b hab]

/-- Literal directed intervals agree on every vertex cycle untouched by contraction. -/
theorem mem_rotationInterval_contractionLift_of_ne {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (a b c : Dart (contractLastEdgeGraph G u v)) (hac : a.vertex = c.vertex) (ha : a.vertex ≠ v) :
    b ∈ (r.contractLastEdge huv).rotationInterval a c ↔
      contractionLift G u v b ∈ r.rotationInterval (contractionLift G u v a)
        (contractionLift G u v c) := by
  classical
  simp only [rotationInterval, r.rotationDistance_contractionLift_of_ne huv a c hac ha,
    Finset.mem_image]
  exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, (r.contractionLift_pow_of_ne huv a ha (k + 1)).trans
    (congrArg _ h)⟩, fun ⟨k, hk, h⟩ => ⟨k, hk, contractionLift_injective G u v
    ((r.contractionLift_pow_of_ne huv a ha (k + 1)).symm.trans h)⟩⟩

/-- Every actual source dart is either a lifted retained occurrence or a selected end. -/
theorem contraction_dart_cases (G : Graph) (u v : ℕ) (d : Dart (lastEdgeGraph G u v)) :
    (∃ e : Dart (contractLastEdgeGraph G u v), d = contractionLift G u v e) ∨
      ∃ side : Bool, d = lastEdgeDart G u v side := by
  have h := (lastEdgeDartEquiv G u v).symm_apply_apply d
  rcases he : (lastEdgeDartEquiv G u v) d with _ | (_ | e) <;> rw [he] at h
  · exact Or.inr ⟨true, h.symm⟩
  · exact Or.inr ⟨false, h.symm⟩
  · refine Or.inl ⟨Dart.relabelEquiv G (Function.update id u v) e, ?_⟩
    rw [contractionLift_relabelEquiv]
    exact h.symm

end Cslib.Complexity.Graph.RotationSystem
