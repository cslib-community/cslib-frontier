/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChild
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.Sort

/-!
# The endpoint table of a native child

The native child is defined by its ordered port lists and descriptors. Its endpoint table,
reconstructed from those ports, is exactly `ChildNumbering.childEdgeList`. The proof works for
any represented group, packet and slot functions; it does not require the canonical packing.

`edgeEnds_nativeChild` is the structural bridge from a native described child to a compressed
endpoint representation built with the same packing.
-/

public section

namespace Cslib.Circuits.Frontier.NativeChild

open ChildNumbering

private theorem edgeEnds_ofFn {T : Type} {k m : ℕ} (F : Fin k → List ℕ × T)
    (src tgt : Fin m → Fin k) (hstrict : ∀ e, (src e : ℕ) < tgt e)
    (hports : ∀ (e : Fin m) (v : Fin k), (e : ℕ) ∈ (F v).1 ↔ src e = v ∨ tgt e = v) :
    (⟨m, List.ofFn F⟩ : DescribedNetwork T).edgeEnds =
      List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ)) := by
  let D : DescribedNetwork T := ⟨m, List.ofFn F⟩
  have hincident (e : Fin m) : D.incident e = [src e, tgt e] := by
    have hsorted : (D.incident e).Pairwise (· < ·) := List.pairwise_lt_range.filter _
    have hst : [(src e : ℕ), (tgt e : ℕ)].Pairwise (· < ·) := by
      simpa using hstrict e
    apply hsorted.eq_of_mem_iff hst
    intro v
    simp only [D, DescribedNetwork.incident, List.length_ofFn, List.map_ofFn,
      List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_cons, List.not_mem_nil,
      or_false]
    constructor
    · rintro ⟨hv, hp⟩
      have hend := (hports e ⟨v, hv⟩).mp
        (by simpa only [List.getD_ofFn_of_lt _ hv, Function.comp_apply] using hp)
      exact hend.elim (fun h => Or.inl (congrArg Fin.val h).symm)
        (fun h => Or.inr (congrArg Fin.val h).symm)
    · rintro (rfl | rfl)
      · exact ⟨(src e).isLt, by simpa only [List.getD_ofFn, Function.comp_apply] using
          (hports e (src e)).mpr (Or.inl rfl)⟩
      · exact ⟨(tgt e).isLt, by simpa only [List.getD_ofFn, Function.comp_apply] using
          (hports e (tgt e)).mpr (Or.inr rfl)⟩
  change D.edgeEnds = _
  rw [DescribedNetwork.edgeEnds, ← List.map_coe_finRange_eq_range, List.map_map,
    ← List.ofFn_eq_map]
  congr 1 with e : 1
  simp [hincident]

/-- Reconstructing the endpoints from the native child's ports gives exactly the numbered
child edge table, for any represented group, packet and slot functions. -/
theorem edgeEnds_nativeChild {T : Type} {D : DescribedNetwork (VertexDesc T)} {r P : ℕ}
    (hD : D.IsRowsFirstBipartite r) (group : Fin D.vertices.length → Fin 64)
    (packet : Fin D.numEdges → Fin P) (slot : Fin D.numEdges → ℕ) (g : Fin 64)
    (fl : List ℕ) (a i pt : ℕ) (t : ℤ) (ζ β : List ℕ)
    (pk : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ))
    (hgroups : groupsOf r i D.vertices.length pk.1 = List.ofFn fun v => (group v : ℕ))
    (hpk1 : packingNumPackets pk = P)
    (hpk2 : packingPacketSlots pk = List.ofFn fun e => ((packet e : ℕ), slot e)) :
    (nativeChild fl a i pt t ζ r D pk β g).edgeEnds =
      childEdgeList (groupsOf r i D.vertices.length pk.1) g D.edgeEnds
        ((packingPacketSlots pk).map Prod.fst) := by
  have hpackets : (packingPacketSlots pk).map Prod.fst = List.ofFn fun e => (packet e : ℕ) := by
    rw [hpk2, List.map_ofFn]
    rfl
  rw [nativeChild_eq hD group packet slot g fl a i pt t ζ β pk hgroups hpk1 hpk2,
    hgroups, DescribedNetwork.edgeEnds_eq hD, hpackets,
    childEdgeList_eq (D.srcFin hD) (D.tgtFin hD) group packet g]
  apply edgeEnds_ofFn
  · intro j
    rcases (childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g).symm j with e | e <;>
      simp only [childSrc, childTgt, childVertexEquiv, Sum.elim_inl, Sum.elim_inr,
        Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
        rankEquiv_apply_val, Sum.map_inr] <;>
      have h := rank_lt (fun v => group v = g) _ e.2 <;> omega
  · intro j v
    simp only [List.mem_map, mem_numberedPorts]
    constructor
    · rintro ⟨e, he, hj⟩
      have heq : e = (childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g).symm j :=
        (Equiv.eq_symm_apply _).mpr (Fin.ext hj)
      subst e
      exact he.imp (fun h => (Equiv.eq_symm_apply _).mp h)
        (fun h => (Equiv.eq_symm_apply _).mp h)
    · intro h
      refine ⟨(childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g).symm j, ?_, by simp⟩
      exact h.imp (fun h => (Equiv.eq_symm_apply _).mpr h)
        (fun h => (Equiv.eq_symm_apply _).mpr h)

end Cslib.Circuits.Frontier.NativeChild
