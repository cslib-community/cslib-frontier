/-
Copyright (c) 2026 OpenAI, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
import CslibFrontier.Foundations.GroupTheory.Perm.FirstReturn
import CslibFrontier.Foundations.GroupTheory.Perm.InvariantPredicate
import CslibFrontier.Foundations.GroupTheory.Perm.ListSplice

/-!
# Literal cycle words of accepted rotation tables

The original bounded first-return scan retains the direction of the supplied successor
table, including singleton vertex cycles. Its clock is the table length, never a successor
entry or vertex name. Acceptance identifies the computed word with one complete orbit of
the existing decoded rotation.
-/

public section

namespace Cslib.Complexity.Graph.RotationCertificate

/-- List a cycle from its chosen start, stopping before its first return. The table length
funds every walk, including malformed tables and oversized binary starts. -/
@[expose] def cycleWord (c : RotationCertificate) (start : ℕ) : List ℕ :=
  let following := (List.range c.successor.length).map fun k =>
    walk c.successor (k + 1) start
  start :: following.take (following.idxOf start)

/-- Iterating an accepted raw table agrees with iterating the existing decoded rotation. -/
theorem walk_index {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d : Dart G) (steps : ℕ) :
    walk c.successor steps d.index = (((decode G c h).rotate)^[steps] d).index := by
  have hs : Function.Semiconj (Dart.index (G := G)) (decode G c h).rotate
      (fun i => c.successor.getD i 0) := index_decode_rotate h
  exact (hs.iterate_right steps d).symm

/-- A computed word is precisely one directed decoded vertex cycle, with no repeated start
at its end. The period is proved bounded by the accepted table's actual dart count. -/
theorem cycleWord_eq_map_range {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d : Dart G) :
    cycleWord c d.index =
      (List.range (Function.minimalPeriod (decode G c h).rotate d)).map fun k =>
        (((decode G c h).rotate)^[k] d).index := by
  let r := decode G c h
  let step (i : ℕ) := c.successor.getD i 0
  have hi : Function.Injective (Dart.index (G := G)) := fun a b hab =>
    (Dart.indexEquiv G).injective (Fin.ext hab)
  have hperiod : Function.minimalPeriod step d.index = Function.minimalPeriod r.rotate d := by
    apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
    intro k
    change step^[k] d.index = d.index ↔ r.rotate^[k] d = d
    rw [← show walk c.successor k d.index = step^[k] d.index from rfl, walk_index h]
    exact hi.eq_iff
  have hpos : 0 < Function.minimalPeriod step d.index := by
    rw [hperiod]
    exact Function.minimalPeriod_pos_of_mem_periodicPts (r.rotate.injective.mem_periodicPts d)
  have hbound : Function.minimalPeriod step d.index ≤ c.successor.length := by
    rw [hperiod, length_of_verifyRotation h]
    simpa only [Dart.card] using
      (Function.minimalPeriod_le_card (f := r.rotate) (x := d))
  have he := Function.firstReturnWord_eq step d.index c.successor.length hpos hbound
  change cycleWord c d.index = _
  change d.index :: ((List.range c.successor.length).map fun k =>
    step^[k + 1] d.index).take _ = _ at he
  rw [show cycleWord c d.index = d.index ::
    ((List.range c.successor.length).map fun k => step^[k + 1] d.index).take
      (((List.range c.successor.length).map fun k => step^[k + 1] d.index).idxOf d.index)
        from rfl, he, hperiod]
  apply List.map_congr_left
  intro k _
  exact walk_index h d k

/-- No dart is duplicated in the computed word of an accepted table. -/
theorem nodup_cycleWord {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d : Dart G) : (cycleWord c d.index).Nodup := by
  rw [cycleWord_eq_map_range h]
  apply List.nodup_map_iff_inj_on List.nodup_range |>.mpr
  intro i hi j hj he
  rw [List.mem_range] at hi hj
  have hinj : Function.Injective (Dart.index (G := G)) := fun a b hab =>
    (Dart.indexEquiv G).injective (Fin.ext hab)
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp (hinj he)

/-- The stored cycle contains exactly the selected endpoint fiber. This uses actual
indexed darts, so repeated labels on distinct edge occurrences remain distinct members. -/
theorem mem_cycleWord_iff {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d e : Dart G) :
    e.index ∈ cycleWord c d.index ↔ e.vertex = d.vertex := by
  let r := decode G c h
  have hinj : Function.Injective (Dart.index (G := G)) := fun a b hab =>
    (Dart.indexEquiv G).injective (Fin.ext hab)
  rw [cycleWord_eq_map_range h, List.mem_map]
  constructor
  · rintro ⟨k, _, hk⟩
    have he : r.rotate^[k] d = e := hinj hk
    have hc : r.rotate.SameCycle d e := ⟨(k : ℤ), by
      rw [zpow_natCast, ← Equiv.Perm.iterate_eq_pow]
      exact he⟩
    exact ((r.sameCycle_iff _ _).mp hc).symm
  · intro he
    obtain ⟨k, hk⟩ := ((r.sameCycle_iff _ _).mpr he.symm).exists_nat_pow_eq
    have hp := Function.minimalPeriod_pos_of_mem_periodicPts
      (r.rotate.injective.mem_periodicPts d)
    refine ⟨k % Function.minimalPeriod r.rotate d, List.mem_range.mpr
      (Nat.mod_lt _ hp), ?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq, Equiv.Perm.iterate_eq_pow, hk]

/-- Every entry of an accepted cycle word is the index of an actual dart in its endpoint
fiber. Malformed out-of-range table values therefore cannot occur in such a word. -/
theorem mem_cycleWord_iff_exists_dart {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d : Dart G) (index : ℕ) :
    index ∈ cycleWord c d.index ↔ ∃ e : Dart G, e.index = index ∧ e.vertex = d.vertex := by
  constructor
  · intro hm
    rw [cycleWord_eq_map_range h, List.mem_map] at hm
    obtain ⟨k, hkb, hk⟩ := hm
    let e := ((decode G c h).rotate)^[k] d
    refine ⟨e, hk, ?_⟩
    exact (mem_cycleWord_iff h d e).mp
      (by rw [cycleWord_eq_map_range h]; exact List.mem_map.mpr ⟨k, hkb, rfl⟩)
  · rintro ⟨e, rfl, he⟩
    exact (mem_cycleWord_iff h d e).mpr he

/-- The tail of the rooted cycle contains exactly the other darts at that endpoint. -/
theorem mem_tail_cycleWord_iff {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d e : Dart G) :
    e.index ∈ (cycleWord c d.index).tail ↔ e.vertex = d.vertex ∧ e ≠ d := by
  have hn := nodup_cycleWord h d
  have hhead : cycleWord c d.index = d.index :: (cycleWord c d.index).tail := rfl
  rw [hhead, List.nodup_cons] at hn
  constructor
  · intro hm
    refine ⟨(mem_cycleWord_iff h d e).mp (List.mem_of_mem_tail hm), ?_⟩
    intro he
    exact hn.1 (he ▸ hm)
  · rintro ⟨hv, he⟩
    have hm := (mem_cycleWord_iff h d e).mpr hv
    rw [hhead, List.mem_cons] at hm
    rcases hm with hm | hm
    · exact False.elim (he ((Dart.indexEquiv G).injective (Fin.ext hm)))
    · exact hm

/-- The directed word's cyclic successor is the supplied raw successor at every member.
This identifies the actual order, not only its set of darts or endpoint fiber. -/
theorem formPerm_cycleWord_apply {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d e : Dart G) (he : e.vertex = d.vertex) :
    (cycleWord c d.index).formPerm e.index = c.successor.getD e.index 0 := by
  let r := decode G c h
  let p := Function.minimalPeriod r.rotate d
  have hm := (mem_cycleWord_iff h d e).mpr he
  rw [cycleWord_eq_map_range h, List.mem_map] at hm
  obtain ⟨k, hk, hke⟩ := hm
  have hlen : (cycleWord c d.index).length = p := by
    simp [cycleWord_eq_map_range h, p, r]
  have hbound : k < (cycleWord c d.index).length := by
    rw [hlen]
    exact List.mem_range.mp hk
  have hget : (cycleWord c d.index)[k] = e.index := by
    simpa only [cycleWord_eq_map_range h, List.getElem_map, List.getElem_range] using hke
  rw [← hget, List.formPerm_apply_getElem _ (nodup_cycleWord h d) _ hbound]
  simp only [cycleWord_eq_map_range h, List.length_map, List.length_range,
    List.getElem_map, List.getElem_range]
  rw [Function.iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply']
  have hrot : r.rotate^[k] d = e := (Dart.indexEquiv G).injective (Fin.ext hke)
  rw [hrot, index_decode_rotate h]

/-- Roots at different vertices have disjoint words, even when their edges are parallel. -/
theorem disjoint_cycleWord {G : Graph} {c : RotationCertificate}
    (hc : verifyRotation G c = true) (a b : Dart G) (hab : a.vertex ≠ b.vertex) :
    (cycleWord c a.index).Disjoint (cycleWord c b.index) := by
  apply List.disjoint_left.mpr
  intro n ha hb
  obtain ⟨d, rfl, hd⟩ := (mem_cycleWord_iff_exists_dart hc a n).mp ha
  exact hab (hd.symm.trans ((mem_cycleWord_iff hc b d).mp hb))

open Equiv in
/-- The two ways of swapping successors around markers on different vertex cycles give
opposite block orders after skipping the second marker. The words come from the actual
rotation table, and the successor comparisons use the original dart coordinates. -/
theorem formPerm_cycleWord_join_skip_iff {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (a b x y : Dart G)
    (hab : a.vertex ≠ b.vertex) (hx : x.vertex = a.vertex ∨ x.vertex = b.vertex)
    (hxb : x ≠ b) (hyb : y ≠ b) :
    let A := cycleWord (ofRotation r) a.index
    let B := cycleWord (ofRotation r) b.index
    let before := r.rotate * swap (r.rotate.symm a) (r.rotate.symm b)
    let after := r.rotate * swap a b
    ((a.index :: (A.tail ++ B.tail)).formPerm x.index = y.index ↔
      before x = y ∨ before x = b ∧ before b = y) ∧
    ((a.index :: (B.tail ++ A.tail)).formPerm x.index = y.index ↔
      after x = y ∨ after x = b ∧ after b = y) := by
  dsimp only
  let c := ofRotation r
  let A := cycleWord c a.index
  let B := cycleWord c b.index
  have hc : verifyRotation G c = true := verifyRotation_ofRotation r hG
  have hidx : Function.Injective (Dart.index (G := G)) := fun _ _ h =>
    (Dart.indexEquiv G).injective (Fin.ext h)
  have hmem (root d : Dart G) : d.index ∈ cycleWord c root.index ↔ d.vertex = root.vertex :=
    mem_cycleWord_iff hc root d
  have hform (root d : Dart G) (hd : d.vertex = root.vertex) :
      (cycleWord c root.index).formPerm d.index = (r.rotate d).index := by
    rw [formPerm_cycleWord_apply hc root d hd, ← index_decode_rotate hc, decode_ofRotation r hG]
  have hn : (A ++ B).Nodup := List.nodup_append'.mpr
    ⟨nodup_cycleWord hc a, nodup_cycleWord hc b, disjoint_cycleWord hc a b hab⟩
  let p (d : Dart G) := d.vertex = a.vertex ∨ d.vertex = b.vertex
  have hproduct (d : Dart G) (hd : p d) :
      (r.rotate d).index = (A.formPerm * B.formPerm) d.index := by
    rw [Perm.mul_apply]
    rcases hd with hd | hd
    · have hnot : d.index ∉ B := fun hm => hab (hd.symm.trans ((hmem b d).mp hm))
      rw [List.formPerm_apply_of_notMem hnot]
      exact (hform a d hd).symm
    · have hnot : (r.rotate d).index ∉ A := fun hm =>
        hab (((hmem a (r.rotate d)).mp hm).symm.trans ((r.vertex_rotate d).trans hd))
      rw [hform b d hd, List.formPerm_apply_of_notMem hnot]
  have hcompare (u v : Dart G) (hu : p u) (hv : p v) :
      let q := A.formPerm * B.formPerm * swap u.index v.index
      let f := r.rotate * swap u v
      (q x.index = y.index ∨ q x.index = b.index ∧ q b.index = y.index) ↔
        f x = y ∨ f x = b ∧ f b = y := by
    have he (d : Dart G) (hd : p d) :
        ((r.rotate * swap u v) d).index =
          (A.formPerm * B.formPerm * swap u.index v.index) d.index := by
      change (r.rotate (swap u v d)).index = (A.formPerm * B.formPerm)
        (swap u.index v.index d.index)
      rw [← hidx.map_swap]
      exact hproduct _ ((Equiv.predicate_swap p u v (iff_of_true hu hv) d).mpr hd)
    simp only [← he x hx, ← he b (Or.inr rfl), hidx.eq_iff]
  have hprev (d : Dart G) : (r.rotate.symm d).vertex = d.vertex := by
    rw [← r.vertex_rotate (r.rotate.symm d), r.rotate.apply_symm_apply]
  have hlast (d : Dart G) :
      (cycleWord c d.index).getLast (by simp [cycleWord]) = (r.rotate.symm d).index := by
    have he := hform d (r.rotate.symm d) (hprev d)
    rw [r.rotate.apply_symm_apply] at he
    exact ((List.formPerm_eq_head_iff_eq_getLast _ _ _).mp he).symm
  obtain ⟨hBefore, hAfter⟩ := List.formPerm_join_skip_marker_iff A.tail B.tail a.index b.index
    x.index y.index hn (fun he => hxb (hidx he)) (fun he => hyb (hidx he))
  have hBefore' := hcompare (r.rotate.symm a) (r.rotate.symm b)
    (Or.inl (hprev a)) (Or.inr (hprev b))
  rw [← hlast a, ← hlast b] at hBefore'
  exact ⟨hBefore.trans hBefore', hAfter.trans (hcompare a b (Or.inl rfl) (Or.inr rfl))⟩

end Cslib.Complexity.Graph.RotationCertificate
