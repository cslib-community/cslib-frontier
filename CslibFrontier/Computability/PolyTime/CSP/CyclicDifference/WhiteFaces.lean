/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CyclicDifference.Rotation
import Mathlib.Data.Nat.Find

/-!
# Complete bounded enumeration of white faces

Least-position scans enumerate every white orbit exactly once. The resulting boundary lists
partition the actual occurrence positions, even when source variables or constraint records
repeat. All uses of choice below are proof-only; the compiler executes the bounded scans.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table
open Graph.RotationCertificate Graph.RotationSystem

variable {Rel : Type} {F : CSP Rel ℕ} (cert : Graph.RotationCertificate)
    (h : verifyRotation (incidenceGraph F) cert = true)

private lemma exists_edge {i : ℕ} (hi : i < F.occurrences.length) :
    ∃ p : F.Occurrence, incidenceEdgeIndex p = i :=
  exists_incidenceEdgeIndex i (by simpa only [incidenceGraph_edges, List.length_map] using hi)

private lemma edge_lt (p : F.Occurrence) : incidenceEdgeIndex p < F.occurrences.length := by
  simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt p

include h

/-- The finite representative test means least original occurrence position in that white orbit. -/
theorem whiteRep_iff (o : F.Occurrence) :
    faceRepBool F.occurrences.length (whiteTable F cert) (incidenceEdgeIndex o) = true ↔
      ∀ p : F.Occurrence, (whitePermutation (decode _ cert h)).SameCycle o p →
        incidenceEdgeIndex o ≤ incidenceEdgeIndex p := by
  simp only [faceRepBool, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq]
  refine ⟨fun hr p hp => (hr _ (edge_lt p)).resolve_left
    (by simp [(orbitBool_white cert h o p).mpr hp]), fun hr i hi => ?_⟩
  obtain ⟨p, rfl⟩ := exists_edge hi
  by_cases ho : orbitBool F.occurrences.length (whiteTable F cert)
      (incidenceEdgeIndex o) (incidenceEdgeIndex p) = true
  · exact .inr (hr p ((orbitBool_white cert h o p).mp ho))
  · exact .inl (Bool.eq_false_iff.mpr ho)

/-- Every actual occurrence has a least representative in its complete white orbit. -/
theorem exists_whiteRep (o : F.Occurrence) :
    ∃ p : F.Occurrence, (whitePermutation (decode _ cert h)).SameCycle o p ∧
      faceRepBool F.occurrences.length (whiteTable F cert) (incidenceEdgeIndex p) = true := by
  classical
  have hex : ∃ n, ∃ p : F.Occurrence, incidenceEdgeIndex p = n ∧
      (whitePermutation (decode _ cert h)).SameCycle o p := ⟨incidenceEdgeIndex o, o, rfl, .rfl⟩
  obtain ⟨p, hp, ho⟩ := Nat.find_spec hex
  exact ⟨p, ho, (whiteRep_iff cert h p).mpr fun q hq =>
    hp ▸ Nat.find_min' hex ⟨q, rfl, ho.trans hq⟩⟩

/-- Two accepted representatives in the same orbit have the same original edge position. -/
theorem whiteRep_unique (o p : F.Occurrence)
    (ho : faceRepBool F.occurrences.length (whiteTable F cert) (incidenceEdgeIndex o) = true)
    (hp : faceRepBool F.occurrences.length (whiteTable F cert) (incidenceEdgeIndex p) = true)
    (hcycle : (whitePermutation (decode _ cert h)).SameCycle o p) : o = p := by
  apply incidenceEdgeIndex_injective
  exact Nat.le_antisymm ((whiteRep_iff cert h o).mp ho p hcycle)
    ((whiteRep_iff cert h p).mp hp o hcycle.symm)

/-- Changing the representative within a white orbit leaves its complete sorted scope unchanged. -/
theorem whiteScope_eq_of_sameCycle (o p : F.Occurrence)
    (hcycle : (whitePermutation (decode _ cert h)).SameCycle o p) :
    whiteScope F cert (incidenceEdgeIndex o) = whiteScope F cert (incidenceEdgeIndex p) := by
  refine List.filter_congr fun j hj => ?_
  obtain ⟨q, rfl⟩ := exists_edge (List.mem_range.mp hj)
  rw [Bool.eq_iff_iff, orbitBool_white cert h, orbitBool_white cert h]
  exact ⟨hcycle.symm.trans, hcycle.trans⟩

/-- The actual white lists cover every edge position and introduce no extra boundary name. -/
theorem mem_flatten_whiteScopes (v : ℕ) :
    v ∈ (whiteScopes F cert).flatten ↔ v < F.occurrences.length := by
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨scope, hs, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
    exact (whiteScope_bounds F cert i).2.2 v hv
  · obtain ⟨o, rfl⟩ := exists_edge hv
    obtain ⟨p, hp, hr⟩ := exists_whiteRep cert h o
    exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr
      ⟨_, List.mem_filter.mpr ⟨List.mem_range.mpr (edge_lt p), hr⟩, rfl⟩,
      List.mem_filter.mpr ⟨List.mem_range.mpr hv, (orbitBool_white cert h p o).mpr hp.symm⟩⟩

/-- The complete flattened boundary enumeration is duplicate free. -/
theorem nodup_flatten_whiteScopes : (whiteScopes F cert).flatten.Nodup := by
  let reps := (List.range F.occurrences.length).filter fun edge =>
    faceRepBool F.occurrences.length (whiteTable F cert) edge
  have hnd : reps.Nodup := List.nodup_range.filter _
  change (reps.flatMap (whiteScope F cert)).Nodup
  refine List.nodup_flatMap.mpr ⟨fun i _ => (whiteScope_bounds F cert i).1,
    List.pairwise_iff_getElem.mpr fun i j hi hj hij => List.disjoint_left.mpr fun v hvo hvp => ?_⟩
  have hri := List.mem_filter.mp (List.getElem_mem hi : reps[i] ∈ reps)
  have hrj := List.mem_filter.mp (List.getElem_mem hj : reps[j] ∈ reps)
  obtain ⟨o, ho⟩ := exists_edge (List.mem_range.mp hri.1)
  obtain ⟨p, hp⟩ := exists_edge (List.mem_range.mp hrj.1)
  obtain ⟨q, hq⟩ := exists_edge ((whiteScope_bounds F cert _).2.2 v hvo)
  have hc1 := (orbitBool_white cert h o q).mp
    (by simpa only [ho, hq] using (List.mem_filter.mp hvo).2)
  have hc2 := (orbitBool_white cert h p q).mp
    (by simpa only [hp, hq] using (List.mem_filter.mp hvp).2)
  have hop := whiteRep_unique cert h o p (ho ▸ hri.2) (hp ▸ hrj.2) (hc1.trans hc2.symm)
  have := hnd.getElem_inj_iff.mp (ho.symm.trans ((congrArg incidenceEdgeIndex hop).trans hp))
  omega

/-- Each actual edge occurs exactly once on the white side, with no spurious name. -/
theorem count_flatten_whiteScopes (v : ℕ) :
    (whiteScopes F cert).flatten.count v = if v < F.occurrences.length then 1 else 0 := by
  split_ifs with hv
  · exact List.count_eq_one_of_mem (nodup_flatten_whiteScopes cert h)
      ((mem_flatten_whiteScopes cert h v).mpr hv)
  · exact List.count_eq_zero.mpr fun hm => hv ((mem_flatten_whiteScopes cert h v).mp hm)

end Cslib.Complexity.CSP.CyclicCompiler
