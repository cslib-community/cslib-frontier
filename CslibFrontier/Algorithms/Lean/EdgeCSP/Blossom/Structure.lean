/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Contraction
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Visits
public import CslibFrontier.Logics.Propositional.CSP.Edge.DAGPaths.Blossom.Paths
import CslibFrontier.Foundations.Data.Finset.SymmDiff

/-!
# Internal ports of a closed edge-instance trail

Both occurrences of every blossom variable are used by the trail. Consequently the whole-instance
constructor gathers exactly the used ports, and every touched original constraint supplies at
least two internal coordinates, even when its copied node is visited repeatedly.
The proof using a constant labeling and the exact trail defect equation is an original
bookkeeping argument, independent of the delta-matroid axioms.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Finset

variable {F : CSP Table ℕ} {w : Walk F}

/-- A closed incidence trail uses both ports of each variable it visits. -/
theorem partner_mem_edges (hF : EdgeInstance F) (hw : w.IsWalk) (hc : w.finish = w.start)
    {o : Occurrence F} (ho : o ∈ w.edges) : hF.partner o ∈ w.edges := by
  have hz : defects (fun _ : Occurrence F => false) = ∅ := by
    ext v
    simp [Inconsistent]
  have hd : defects (w.flip (fun _ => false)) = ∅ := by
    rw [hw.defects_flip hF, hc, hz]
    simp
  have he := (defects_eq_empty_iff _).mp hd o (hF.partner o) (hF.partner_variable o)
  by_contra hn
  simp [Walk.flip, BitString.flipOn_apply, ho, hn] at he

/-- For a closed edge-instance trail, gathering by variable name includes exactly the used
original occurrences; it cannot accidentally include an unused port at a repeated constraint. -/
theorem var_mem_internal_iff (hF : EdgeInstance F) (hw : w.IsWalk)
    (hc : w.finish = w.start) (o : Occurrence F) : o.var ∈ internal w ↔ o ∈ w.edges := by
  simp only [internal, List.mem_dedup, List.mem_map]
  refine ⟨fun ⟨p, hp, he⟩ => ?_, fun ho => ⟨o, ho, rfl⟩⟩
  rcases hF.eq_or_eq_partner he with rfl | he
  · exact hp
  · simpa only [he, hF.partner_partner] using partner_mem_edges hF hw hc hp

/-- Membership in a selected position list is precisely occurrence-variable membership. -/
theorem mem_positions (vs : List ℕ) (i : Fin F.length) (j : Fin F[i.val].scope.length) :
    j.val ∈ positions vs F[i.val].scope ↔ Occurrence.var (F := F) ⟨i, j⟩ ∈ vs := by
  simp [positions, Occurrence.var, j.isLt]

/-- Each touched constraint contains a whole cycle step, not a single dangling blossom port. -/
theorem touched_has_step (hF : EdgeInstance F) (hw : w.IsWalk)
    (hc : w.finish = w.start) {i : Fin F.length} (hi : i ∈ touched F (internal w)) :
    ∃ s ∈ w.steps, let (input, _) := s; input.1 = i := by
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ (by simpa using (List.mem_filter.mp hi).2 :
    positions (internal w) F[i.val].scope ≠ [])
  have hjb := List.mem_range.mp (List.mem_filter.mp hj).1
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp
    ((var_mem_internal_iff hF hw hc ⟨i, j, hjb⟩).mp ((mem_positions _ i ⟨j, hjb⟩).mp hj))
  rcases List.mem_cons.mp he with he | he
  · exact ⟨s, hs, (congrArg Sigma.fst he).symm⟩
  · exact ⟨s, hs, (DAG.linked_constraint hw.1 hs).trans
      (congrArg Sigma.fst (List.mem_singleton.mp he)).symm⟩

/-- At least two distinct internal positions are gathered at every touched original constraint.
Repeated visits can increase this number; they never create duplicate connectors. -/
theorem two_le_positions (hF : EdgeInstance F) (hw : w.IsWalk)
    (hc : w.finish = w.start) {i : Fin F.length} (hi : i ∈ touched F (internal w)) :
    2 ≤ (positions (internal w) F[i.val].scope).length := by
  obtain ⟨⟨⟨ai, aj⟩, ⟨bi, bj⟩⟩, hs, ha⟩ := touched_has_step hF hw hc hi
  have hb : bi = i := (DAG.linked_constraint hw.1 hs).symm.trans ha
  dsimp only at ha
  subst ai
  subst bi
  have hae : ⟨i, aj⟩ ∈ w.edges := List.mem_flatMap.mpr ⟨_, hs, by simp⟩
  have hbe : ⟨i, bj⟩ ∈ w.edges := List.mem_flatMap.mpr ⟨_, hs, by simp⟩
  have hjne : aj.val ≠ bj.val := fun he => (List.nodup_cons.mp (hw.2.sublist <|
    (List.singleton_sublist.mpr hs).flatMap fun s => [s.1, s.2])).1
      (List.mem_singleton.mpr <| congrArg (Sigma.mk i) (Fin.ext he))
  have haj := (mem_positions (internal w) i aj).mpr ((var_mem_internal_iff hF hw hc _).mpr hae)
  have hbj := (mem_positions (internal w) i bj).mpr ((var_mem_internal_iff hF hw hc _).mpr hbe)
  refine (by simp [hjne] : 2 = ({aj.val, bj.val} : Finset ℕ).card).le.trans
    ((card_le_card ?_).trans (List.toFinset_card_le _))
  simp [Finset.insert_subset_iff, List.mem_toFinset, haj, hbj]

private theorem inconsistent_edge_endpoints {f : OccurrenceLabeling F Bool} {v : ℕ}
    {ss : List (Occurrence F × Occurrence F)} (hl : Walk.Linked v ss)
    (hi : Walk.InternallyConsistent f ss) {o : Occurrence F}
    (ho : o ∈ Walk.edgesOf ss) (hd : Inconsistent f o.var) :
    o.var = v ∨ o.var = Walk.finishFrom v ss := by
  induction ss generalizing v with
  | nil => simp [Walk.edgesOf] at ho
  | cons s ss ih =>
    rcases s with ⟨a, b⟩
    simp only [Walk.edgesOf_cons, List.mem_cons] at ho
    rcases ho with rfl | rfl | ho
    · exact Or.inl hl.1
    · rcases hi.1 with he | hb
      · subst ss
        exact Or.inr rfl
      · exact (hb hd).elim
    · have hn : ss ≠ [] := by
        rintro rfl
        simp [Walk.edgesOf] at ho
      rcases ih hl.2.2 hi.2 ho with hb | he
      · exact ((hi.1.resolve_left hn) (hb ▸ hd)).elim
      · exact Or.inr he

/-- A genuine prepared blossom has exactly one internal defective variable: its base. -/
theorem defects_inter_internal {f : OccurrenceLabeling F Bool}
    (hb : w.IsBlossom Table.sem f) : defects f ∩ (internal w).toFinset = {w.start} := by
  ext v
  simp only [mem_inter, mem_defects, List.mem_toFinset, mem_singleton]
  refine ⟨fun ⟨hd, hv⟩ => ?_, ?_⟩
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
    exact (inconsistent_edge_endpoints hb.1.1 hb.2.2.2.2.1 ho hd).elim id (·.trans hb.2.1)
  · rintro rfl
    exact ⟨hb.2.2.2.1, List.mem_dedup.mpr (hb.1.start_mem_vars hb.2.2.1)⟩

end Cslib.Logic.PL.CSP.Blossom
