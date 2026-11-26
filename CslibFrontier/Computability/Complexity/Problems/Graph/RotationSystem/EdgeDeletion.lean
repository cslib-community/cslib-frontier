/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CornerInsertion
public import CslibFrontier.Foundations.GroupTheory.Perm.CycleSurgery
import Mathlib.Data.List.GetD
import CslibFrontier.Foundations.Data.List.OfFnPositions

/-!
# Deleting an indexed edge of a rotation

Move a selected edge to the end while retaining the order of every other edge.
The two ends of the last listed edge are removed from their actual vertex cycles, retaining
the direction of every remaining successor. Vertex declarations are retained, including
endpoints that become isolated points. For a nonloop edge, each surviving vertex successor
skips at most one deleted dart. The face successor is obtained by swapping the two deleted
ends in the old face permutation and then deleting both ends.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv Perm.CycleSurgery

/-- The actual graph before deleting its last edge; no corner darts are required at points. -/
@[expose] def lastEdgeGraph (G : Graph) (u v : ℕ) : Graph := ⟨G.vertices, G.edges ++ [(u, v)]⟩

/-- Old darts and the last two ends, in their original edge/end positions. -/
@[expose] def lastEdgeDartEquiv (G : Graph) (u v : ℕ) :
    Dart (lastEdgeGraph G u v) ≃ Option (Option (Dart G)) :=
  (Equiv.prodCongr
    (finCongr (show (lastEdgeGraph G u v).edges.length = G.edges.length + 1 by
      simp [lastEdgeGraph])) (Equiv.refl Bool)).trans (appendedDartEquiv G.edges.length)

/-- The two indexed ends of the last listed edge, including when the old graph has no darts. -/
@[expose] def lastEdgeDart (G : Graph) (u v : ℕ) (b : Bool) : Dart (lastEdgeGraph G u v) :=
  (lastEdgeDartEquiv G u v).symm (if b then none else some none)

/-- The last two actual endpoints are exactly the supplied names. -/
@[simp] theorem vertex_lastEdgeDart (G : Graph) (u v : ℕ) (b : Bool) :
    (lastEdgeDart G u v b).vertex = if b then v else u := by
  cases b
  · exact (by simp : ((G.edges ++ [(u, v)]).getD G.edges.length (0, 0)).1 = u)
  · exact (by simp : ((G.edges ++ [(u, v)]).getD G.edges.length (0, 0)).2 = v)

/-- Reversal interchanges the two last indexed ends. -/
theorem reverse_lastEdgeDart (G : Graph) (u v : ℕ) (b : Bool) :
    (lastEdgeDart G u v b).reverse = lastEdgeDart G u v (!b) := by
  cases b <;> rfl

/-- Move an indexed edge to the last position, retaining the order of the other edges.
The reindexing keeps both end tags and all declared names. Each edge before the selected
position keeps its index, and each edge after it moves back by one, even for equal edges. -/
theorem _root_.Cslib.Complexity.Graph.exists_lastEdge_reindex (G : Graph) (i : Fin G.edges.length) :
    ∃ H : Graph, ∃ u v : ℕ,
      ∃ e : Fin G.edges.length ≃ Fin (lastEdgeGraph H u v).edges.length,
        H.vertices = G.vertices ∧ H.edges = G.edges.eraseIdx i.val ∧
        H.edges.length + 1 = G.edges.length ∧
        (∀ j b, Dart.vertex (e j, b) = Dart.vertex (j, b)) ∧
        (∀ j, j ≠ i → (e j).val = if j < i then j.val else j.val - 1) ∧
        e i = (lastEdgeDart H u v false).1 ∧
        u = Dart.vertex (i, false) ∧ v = Dart.vertex (i, true) := by
  rcases G with ⟨V, E⟩
  cases E with
  | nil => exact Fin.elim0 i
  | cons edge E =>
    let f : Fin (E.length + 1) → ℕ × ℕ := (edge :: E).get
    let σ := (finSuccEquiv' i).trans (finSuccEquiv' (Fin.last E.length)).symm
    let H : Graph := ⟨V, (edge :: E).eraseIdx i.val⟩
    let u := (f i).1
    let v := (f i).2
    have hlenH : H.edges.length + 1 = E.length + 1 := by
      change ((edge :: E).eraseIdx i.val).length + 1 = E.length + 1
      rw [List.length_eraseIdx_of_lt i.isLt, List.length_cons]; omega
    have hσi : σ i = Fin.last E.length := by
      change (finSuccEquiv' (Fin.last E.length)).symm (finSuccEquiv' i i) = _
      rw [finSuccEquiv'_eq_none.mpr rfl, finSuccEquiv'_symm_none]
    have hσ (j : Fin E.length) : σ (i.succAbove j) = j.castSucc := by
      change (finSuccEquiv' (Fin.last E.length)).symm (finSuccEquiv' i (i.succAbove j)) = _
      rw [finSuccEquiv'_succAbove, ← finSuccEquiv'_last_apply_castSucc j, symm_apply_apply]
    have hlist : (lastEdgeGraph H u v).edges = List.ofFn (f ∘ σ.symm) := by
      have hrest : H.edges = List.ofFn (fun j => f (i.succAbove j)) := by
        change ((edge :: E).eraseIdx i.val) = _
        calc
          _ = (List.ofFn f).eraseIdx i.val := by rw [List.ofFn_get]
          _ = _ := List.eraseIdx_ofFn f i
      rw [List.ofFn_succ', List.concat_eq_append]
      change H.edges ++ [f i] = List.ofFn (fun j => f (σ.symm j.castSucc)) ++
        [f (σ.symm (Fin.last E.length))]
      rw [hrest, ← hσi, symm_apply_apply]
      exact congrArg (· ++ [f i]) (congrArg List.ofFn (funext fun j => by
        rw [← hσ j, symm_apply_apply]))
    have hlen : (lastEdgeGraph H u v).edges.length = E.length + 1 := by
      rw [hlist, List.length_ofFn]
    let e := σ.trans (finCongr hlen.symm)
    refine ⟨H, u, v, e, rfl, rfl, hlenH, fun j b => ?_, fun j hj => ?_, Fin.ext ?_, ?_, ?_⟩
    · change (if b then ((lastEdgeGraph H u v).edges.getD (σ j).val (0, 0)).2
        else ((lastEdgeGraph H u v).edges.getD (σ j).val (0, 0)).1) =
        if b then ((edge :: E).getD j.val (0, 0)).2 else ((edge :: E).getD j.val (0, 0)).1
      rw [hlist, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (σ j).isLt),
        List.getElem_ofFn, Function.comp_apply, symm_apply_apply, List.getD_eq_getElem _ _ j.isLt]
      rfl
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      change (σ (i.succAbove k)).val = _
      rw [hσ]
      by_cases hk : k.castSucc < i
      · rw [Fin.succAbove_of_castSucc_lt _ _ hk, ite_eq_left hk]
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hk),
          ite_eq_right (not_lt_of_ge (le_trans (le_of_not_gt hk) (Fin.castSucc_le_succ _)))]
        simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_sub_cancel]
    · change (σ i).val = H.edges.length
      rw [hσi]
      exact Nat.add_right_cancel (by simpa only [Fin.val_last] using hlenH.symm)
    · change (f i).1 = ((edge :: E).getD i.val (0, 0)).1
      rw [List.getD_eq_getElem _ _ i.isLt]; rfl
    · change (f i).2 = ((edge :: E).getD i.val (0, 0)).2
      rw [List.getD_eq_getElem _ _ i.isLt]; rfl

/-- Retain an old dart, without changing its edge-list index or end. -/
@[expose] def retainedLastEdgeDart (G : Graph) (u v : ℕ) (d : Dart G) :
    Dart (lastEdgeGraph G u v) := (lastEdgeDartEquiv G u v).symm (some (some d))

/-- Retained indexed ends keep their original endpoint names. -/
@[simp] theorem vertex_retainedLastEdgeDart (G : Graph) (u v : ℕ) (d : Dart G) :
    (retainedLastEdgeDart G u v d).vertex = d.vertex := by
  rcases d with ⟨⟨i, hi⟩, b⟩
  have hi' : i < (G.edges ++ [(u, v)]).length := by
    simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt hi
  change (if b then ((G.edges ++ [(u, v)]).getD i (0, 0)).2
    else ((G.edges ++ [(u, v)]).getD i (0, 0)).1) =
    if b then (G.edges.getD i (0, 0)).2 else (G.edges.getD i (0, 0)).1
  rw [List.getD_eq_getElem _ _ hi', List.getElem_append_left hi, List.getD_eq_getElem _ _ hi]

/-- Delete the last two indexed ends from their vertex cycles. The construction works when
either endpoint becomes isolated and when there are no remaining edges. -/
@[expose] def deleteLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) : RotationSystem G where
  rotate := removeNone (removeNone ((lastEdgeDartEquiv G u v).permCongr r.rotate))
  sameCycle_iff a b := by
    rw [sameCycle_removeNone, sameCycle_removeNone]
    have he := Perm.sameCycle_equiv_iff (lastEdgeDartEquiv G u v) r.rotate
      ((lastEdgeDartEquiv G u v).permCongr r.rotate) (fun d => by simp)
      (retainedLastEdgeDart G u v a) (retainedLastEdgeDart G u v b)
    simp only [retainedLastEdgeDart, Equiv.apply_symm_apply] at he
    rw [he, r.sameCycle_iff]
    change (retainedLastEdgeDart G u v a).vertex = (retainedLastEdgeDart G u v b).vertex ↔ _
    rw [vertex_retainedLastEdgeDart, vertex_retainedLastEdgeDart]

/-- The successor of a retained dart after deleting a nonloop edge is its original
successor, or the successor of the removed end that followed it. The two removed ends
lie at different vertices, so at most one end is skipped. -/
theorem rotate_deleteLastEdge_eq_iff {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) (a b : Dart G) :
    r.deleteLastEdge.rotate a = b ↔
      r.rotate (retainedLastEdgeDart G u v a) = retainedLastEdgeDart G u v b ∨
      ∃ endTag, r.rotate (retainedLastEdgeDart G u v a) = lastEdgeDart G u v endTag ∧
        r.rotate (lastEdgeDart G u v endTag) = retainedLastEdgeDart G u v b := by
  let e := lastEdgeDartEquiv G u v
  let f := e.permCongr r.rotate
  have hstep (x y : Option (Option (Dart G))) :
      f x = y ↔ r.rotate (e.symm x) = e.symm y := by
    change e (r.rotate (e.symm x)) = y ↔ _
    exact e.eq_symm_apply.symm
  have direct (d : Dart G) (h : f (some (some a)) = some (some d)) :
      r.deleteLastEdge.rotate a = d := by
    have h₁ : removeNone f (some a) = some d :=
      Option.some_injective _ ((removeNone_some f ⟨_, h⟩).trans h)
    exact Option.some_injective _ ((removeNone_some (removeNone f) ⟨_, h₁⟩).trans h₁)
  have skipFalse (d : Dart G) (h₁ : f (some (some a)) = some none)
      (h₂ : f (some none) = some (some d)) : r.deleteLastEdge.rotate a = d := by
    have h₁' : removeNone f (some a) = none :=
      Option.some_injective _ ((removeNone_some f ⟨_, h₁⟩).trans h₁)
    have h₂' : removeNone f none = some d :=
      Option.some_injective _ ((removeNone_some f ⟨_, h₂⟩).trans h₂)
    exact Option.some_injective _ ((removeNone_none (removeNone f) h₁').trans h₂')
  have skipTrue (d : Dart G) (h₁ : f (some (some a)) = none)
      (h₂ : f none = some (some d)) : r.deleteLastEdge.rotate a = d := by
    have h : removeNone f (some a) = some d :=
      Option.some_injective _ ((removeNone_none f h₁).trans h₂)
    exact Option.some_injective _ ((removeNone_some (removeNone f) ⟨_, h⟩).trans h)
  change r.deleteLastEdge.rotate a = b ↔
    r.rotate (e.symm (some (some a))) = e.symm (some (some b)) ∨
    ∃ endTag, r.rotate (e.symm (some (some a))) = lastEdgeDart G u v endTag ∧
      r.rotate (lastEdgeDart G u v endTag) = e.symm (some (some b))
  rw [← hstep (some (some a)) (some (some b))]
  -- When a retained dart reaches a removed end, injectivity excludes revisiting it,
  -- and preservation of the vertex excludes reaching the other removed end.
  have between : f (some none) ≠ none ∧ f none ≠ some none := by
    refine ⟨fun h => huv ?_, fun h => huv ?_⟩
    · have h' : r.rotate (lastEdgeDart G u v false) = lastEdgeDart G u v true := (hstep _ _).mp h
      simpa [h'] using (r.vertex_rotate (lastEdgeDart G u v false)).symm
    · have h' : r.rotate (lastEdgeDart G u v true) = lastEdgeDart G u v false := (hstep _ _).mp h
      simpa [h'] using r.vertex_rotate (lastEdgeDart G u v true)
  refine ⟨fun h => ?_, ?_⟩
  · rcases h₁ : f (some (some a)) with _ | (_ | d)
    · rcases h₂ : f none with _ | (_ | d)
      · exact (Option.some_ne_none _ (f.injective (h₁.trans h₂.symm))).elim
      · exact (between.2 h₂).elim
      · exact (skipTrue d h₁ h₂).symm.trans h ▸ Or.inr ⟨true, (hstep _ _).mp h₁, (hstep _ _).mp h₂⟩
    · rcases h₂ : f (some none) with _ | (_ | d)
      · exact (between.1 h₂).elim
      · exact (Option.some_ne_none _ (Option.some.inj (f.injective (h₁.trans h₂.symm)))).elim
      · exact (skipFalse d h₁ h₂).symm.trans h ▸
          Or.inr ⟨false, (hstep _ _).mp h₁, (hstep _ _).mp h₂⟩
    · exact Or.inl (congrArg (fun d => some (some d)) ((direct d h₁).symm.trans h))
  · rintro (h | ⟨_ | _, h₁, h₂⟩)
    · exact direct b h
    · exact skipFalse b ((hstep _ (some none)).mpr h₁) ((hstep (some none) _).mpr h₂)
    · exact skipTrue b ((hstep _ none).mpr h₁) ((hstep none _).mpr h₂)

/-- Exact reversal in the retained-plus-two-deleted coordinates. -/
theorem lastEdgeDartEquiv_reversal (G : Graph) (u v : ℕ) :
    (lastEdgeDartEquiv G u v).permCongr (Dart.reversal (lastEdgeGraph G u v)) =
      (Dart.reversal G).optionCongr.optionCongr * swap (some none) none := by
  ext (_ | _ | ⟨i, _ | _⟩) <;>
    simp [lastEdgeDartEquiv, appendedDartEquiv, Dart.reverse, Fin.is_lt, swap_apply_def,
      Dart.reversal]

/-- Deletion splices face successors with the original chirality. The preliminary outgoing
swap cancels reversal on the two deleted ends; it is essential even for a loop. -/
theorem faceNext_deleteLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) :
    r.deleteLastEdge.faceNext = removeNone (removeNone
      ((lastEdgeDartEquiv G u v).permCongr r.faceNext * swap (some none) none)) := by
  have hf : r.faceNext = r.rotate⁻¹ * Dart.reversal (lastEdgeGraph G u v) := rfl
  have hinv : (lastEdgeDartEquiv G u v).permCongr r.rotate⁻¹ =
      ((lastEdgeDartEquiv G u v).permCongr r.rotate)⁻¹ :=
    map_inv (lastEdgeDartEquiv G u v).permCongrHom _
  rw [hf, Equiv.permCongr_mul, hinv,
    lastEdgeDartEquiv_reversal, mul_assoc, mul_assoc, swap_mul_self, mul_one,
    removeNone_mul_optionCongr, removeNone_mul_optionCongr]
  change _ = (removeNone (removeNone
    (((lastEdgeDartEquiv G u v).permCongr r.rotate).symm))) * Dart.reversal G
  rw [← Equiv.removeNone_symm, ← Equiv.removeNone_symm]; rfl

/-- Exact accounting for faces lost at endpoints that become isolated. The old vertex
orbit count exceeds the retained one by precisely the number of deleted singleton cycles
in the preliminary face swap. This identity includes deletion of the only edge or loop. -/
theorem card_faces_deleteLastEdge_balance {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) :
    Nat.card r.deleteLastEdge.Face + Nat.card (Quotient (Perm.SameCycle.setoid r.rotate)) =
      Nat.card (Quotient (Perm.SameCycle.setoid
        ((lastEdgeDartEquiv G u v).permCongr r.faceNext * swap (some none) none))) +
          Nat.card (Quotient (Perm.SameCycle.setoid r.deleteLastEdge.rotate)) := by
  let f := ((lastEdgeDartEquiv G u v).permCongr r.rotate)⁻¹
  let a := Dart.reversal G
  have h₁ := card_orbits_removeNone_balance f a.optionCongr
  have h₂ := card_orbits_removeNone_balance (removeNone f) a
  have hf : (lastEdgeDartEquiv G u v).permCongr r.faceNext * swap (some none) none =
      f * a.optionCongr.optionCongr := by
    change (lastEdgeDartEquiv G u v).permCongr
      (r.rotate⁻¹ * Dart.reversal (lastEdgeGraph G u v)) * _ = _
    have hi : (lastEdgeDartEquiv G u v).permCongr r.rotate⁻¹ = f :=
      map_inv (lastEdgeDartEquiv G u v).permCongrHom _
    rw [Equiv.permCongr_mul, hi, lastEdgeDartEquiv_reversal]
    simp only [a, mul_assoc, swap_mul_self, mul_one]
  have hφ : r.deleteLastEdge.faceNext = removeNone (removeNone (f * a.optionCongr.optionCongr)) :=
    r.faceNext_deleteLastEdge.trans (congrArg (fun q => removeNone (removeNone q)) hf)
  have hc : Nat.card (Quotient (Perm.SameCycle.setoid f)) =
      Nat.card (Quotient (Perm.SameCycle.setoid r.rotate)) := by
    rw [card_orbits_inv, card_orbits_permCongr]
  rw [removeNone_mul_optionCongr, ← hf, hc] at h₁
  have hσ : removeNone (removeNone f) = r.deleteLastEdge.rotate⁻¹ := rfl
  rw [← removeNone_mul_optionCongr, ← hφ, hσ, card_orbits_inv, removeNone_mul_optionCongr] at h₂
  change Nat.card (Quotient (Perm.SameCycle.setoid r.deleteLastEdge.faceNext)) + _ = _
  omega

end Cslib.Complexity.Graph.RotationSystem
