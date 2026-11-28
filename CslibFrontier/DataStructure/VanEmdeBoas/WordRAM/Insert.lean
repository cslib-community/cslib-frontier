/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Model
public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Program
public import CslibFrontier.DataStructure.VanEmdeBoas.Insert
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame
import CslibFrontier.Tactic.UpdateSimp

/-!
# Native van Emde Boas insertion descent

Insertion updates local extrema in place and recurses at most once per level: either into the
summary when the target cluster was empty (after installing the cluster's singleton extrema
directly), or into the already-occupied target cluster. Repeated insertion of a local minimum
terminates immediately.

## Main definitions

* `InsertEntry`: the insertion-loop register invariant.

## Main results

* `insertLoop_spec`: insertion takes at most `39 * (d + 1) + 2` loop instructions,
  produces a valid memory representation of `tree.insert key`, and preserves all memory outside
  `[base, base + span d)`.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.DataStructure.VanEmdeBoas.WordRAM

open Cslib.WordRAM
open Cslib.DataStructure.VanEmdeBoas

/-- The constant and traversal registers at entry to an unfinished insertion. -/
structure InsertEntry (base key : ℕ) (s : Data 32) : Prop where
  zero_eq : s.regs zero = 0
  one_eq : s.regs one = 1
  two_eq : s.regs two = 2
  three_eq : s.regs three = 3
  four_eq : s.regs four = 4
  five_eq : s.regs five = 5
  p_eq : s.regs p = base
  x_eq : s.regs x = key
  runFlag_eq : s.regs runFlag = 1

/-- Updating `base + 1` and `base + 2` in place on a valid occupied header agrees with
`writeBounds` at every memory cell. -/
private theorem writeBounds_update_min_max {mem : ℕ → ℕ} {base m M key : ℕ}
    (hpres : mem base = 1) (hm : mem (base + 1) = m) (hM : mem (base + 2) = M)
    (hle : m ≤ M) :
    (let m₁ := if key < m then Function.update mem (base + 1) key else mem
     let displaced := if key < m then m else key
     if M < displaced then Function.update m₁ (base + 2) displaced else m₁) =
      writeBounds mem base (some (min m key, max M key)) := by
  funext a
  dsimp only [writeBounds]
  rcases eq_or_ne a base with rfl | h0
  · update_simp; exact hpres
  rcases eq_or_ne a (base + 1) with rfl | h1
  · update_simp; split_ifs <;> omega
  rcases eq_or_ne a (base + 2) with rfl | h2
  · update_simp; split_ifs <;> omega
  update_simp

/-- An occupied node's displaced key `max m key` has valid cluster coordinates and lies in the
parent record interval whenever `key < universeSize (d + 1)`. -/
private theorem insert_descent_safe {d base m M key : ℕ} {s : Tree d}
    {c : Fin (universeSize d) → Tree d}
    (ht : (Tree.node (some (m, M)) s c).Valid) (hkey : key < universeSize (d + 1)) :
    let displaced := max m key
    displaced / universeSize d < universeSize d ∧
      displaced % universeSize d < universeSize d ∧
      base + clusterOffset d (displaced / universeSize d) + span d ≤ base + span (d + 1) := by
  have hm_lt : m < universeSize (d + 1) := ht.contains_lt (ht.contains_minimum rfl)
  have hdisp : max m key < universeSize d * universeSize d := by
    simpa only [universeSize_succ] using max_lt hm_lt hkey
  have hpos := universeSize_pos d
  have hi : max m key / universeSize d < universeSize d := by stride_omega
  refine ⟨hi, Nat.mod_lt _ hpos, ?_⟩
  simpa only [Nat.add_assoc] using Nat.add_le_add_left (cluster_end_le_span d hi) base

/-- Execute the header-check and extrema-update prefix of `insertBody` on an occupied record with
`key ≠ m`, joining the conditional paths into a single state `y` with
`InsertEntry base (max m key) y` and `y.mem = writeBounds s.mem base (some (min m key, max M key))`
before running `insertTail`. -/
private theorem exists_execWithin_insertBody_occupied {w base key m M : ℕ} {s : Data 32}
    {P : Data 32 → Prop}
    (hs : InsertEntry base key s) (hpres : s.mem base = 1)
    (hm : s.mem (base + 1) = m) (hM : s.mem (base + 2) = M) (hle : m ≤ M)
    (heq : key ≠ m) (hbase4 : Fits w (base + 4))
    (hrest : ∀ y, InsertEntry base (max m key) y →
      y.mem = writeBounds s.mem base (some (min m key, max M key)) →
      WP w insertTail y fun z T' => T' ≤ 21 ∧ P z) :
    ∃ z, ExecWithin w insertBody s z 37 ∧ P z := by
  apply WP.exists_execWithin
  unfold insertBody readAt writeAt
  have hp := hs.p_eq; have hx := hs.x_eq; have hz := hs.zero_eq
  have ho := hs.one_eq; have htwo := hs.two_eq; have hrun := hs.runFlag_eq
  wram_exec -split [hp, hx, hz, ho, htwo, hpres, hm, heq]
  let m₁ := if key < m then Function.update s.mem (base + 1) key else s.mem
  refine WP.cut (fun y₁ T₁ => T₁ ≤ 4 ∧ InsertEntry base (max m key) y₁ ∧ y₁.mem = m₁) ?_ ?_
  · wram_exec [hp, hx, ho]
    · refine ⟨by struct_frame hs; wram_simp [max_eq_left hc.le], ?_⟩
      dsimp only [m₁]; rw [ite_eq_left hc]; wram_simp
    · refine ⟨by struct_frame hs; wram_simp [hx, max_eq_right (not_lt.mp hc)], ?_⟩
      dsimp only [m₁]; rw [ite_eq_right hc]; wram_simp
  · rintro y₁ T₁ ⟨hT₁, hy₁, hm₁⟩
    have hy₁_M : y₁.mem (base + 2) = M := by
      rw [hm₁]; update_simp; exact hM
    have hy₁_p := hy₁.p_eq; have hy₁_x := hy₁.x_eq
    have hy₁_2 := hy₁.two_eq; have hy₁_run := hy₁.runFlag_eq
    wram_exec -split [hy₁_p, hy₁_x, hy₁_2, hy₁_M]
    have hdisp : (if key < m then m else key) = max m key := by
      split_ifs with h <;> [exact (max_eq_left h.le).symm; exact (max_eq_right (not_lt.mp h)).symm]
    refine WP.cut (fun y₂ T₂ => T₂ ≤ 3 ∧ InsertEntry base (max m key) y₂ ∧
      y₂.mem = writeBounds s.mem base (some (min m key, max M key))) ?_ ?_
    · wram_exec [hy₁_p, hy₁_2, hy₁_x]
      · refine ⟨by struct_frame hy₁, ?_⟩
        rw [← writeBounds_update_min_max hpres hm hM hle]
        dsimp only []
        rw [hdisp, ite_eq_left hc]
        wram_simp [hm₁]; rfl
      · refine ⟨by struct_frame hy₁, ?_⟩
        rw [← writeBounds_update_min_max hpres hm hM hle]
        dsimp only []
        rw [hdisp, ite_eq_right hc]
        wram_simp [hm₁]; rfl
    · rintro y₂ T₂ ⟨hT₂, hy₂, hm₂⟩
      exact (hrest y₂ hy₂ hm₂).mono fun z T' ⟨hT', hPz⟩ => ⟨by omega, hPz⟩

/-- Terminate `insertLoop` in one `insertBody` pass when the body clears `runFlag`, establishes
`Rep tree' base s₁.mem`, and frames memory outside `[base, base + span d)`. -/
private theorem insertLoop_finish {d w base key : ℕ} {tree' : Tree d} {s : Data 32}
    (hs : InsertEntry base key s)
    (hstep : ∃ s₁, ExecWithin w insertBody s s₁ 37 ∧
      s₁.regs zero = 0 ∧ s₁.regs runFlag = 0 ∧ Rep tree' base s₁.mem ∧
      (∀ a, a < base ∨ base + span d ≤ a → s₁.mem a = s.mem a)) :
    ∃ z, ExecWithin w insertLoop s z (39 * (d + 1) + 2) ∧
      Rep tree' base z.mem ∧
      (∀ a, a < base ∨ base + span d ≤ a → z.mem a = s.mem a) := by
  obtain ⟨s₁, he, hz0, hk, hrep, hframe⟩ := hstep
  refine ⟨s₁, (he.loop_once (cond := .lt zero runFlag) ?_ ?_).mono (by omega), hrep, hframe⟩
  · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
    decide
  · simp only [Cond.holds_lt, hz0, hk, lt_self_iff_false, not_false_eq_true]

/-- The insertion loop is correct for every depth and arbitrary surrounding memory.
It executes within `39 * (d + 1) + 2` instructions, establishes `Rep (tree.insert key) base z.mem`,
and leaves all memory outside `[base, base + span d)` unchanged. -/
theorem insertLoop_spec {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : InsertEntry base key s) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hkey : key < universeSize d) (ha : Fits w (base + span d)) :
    ∃ z, ExecWithin w insertLoop s z (39 * (d + 1) + 2) ∧
      Rep (tree.insert key) base z.mem ∧
      (∀ a, a < base ∨ base + span d ≤ a → z.mem a = s.mem a) := by
  have hp := hs.p_eq; have hx := hs.x_eq; have hz := hs.zero_eq
  have ho := hs.one_eq; have htwo := hs.two_eq; have hrun := hs.runFlag_eq
  have h5_le := five_le_span d
  have hbase4 : Fits w (base + 4) := ha.of_le (by omega)
  have hheader := hr.header
  rcases hb : tree.bounds with _ | ⟨m, M⟩ <;> rw [hb] at hheader
  · have hempty : s.mem base = 0 := hheader.1
    have hins : tree.insert key = tree.withBounds (some (key, key)) := by
      cases tree <;> simp_all [Tree.bounds, Tree.insert, Tree.withBounds]
    apply insertLoop_finish hs
    apply WP.exists_execWithin
    wram_exec [insertBody, writeAt, hp, hx, hz, ho, htwo, hempty]
    refine ⟨by wram_simp [hz], by wram_simp, ?_, ?_⟩
    · rw [hins]
      simpa only [writeBounds, Data.write_mem, Data.set_mem] using
        rep_writeBounds hr (some (key, key))
    · intro a ha'
      simpa only [writeBounds, Data.write_mem, Data.set_mem] using
        writeBounds_away (mem := s.mem) (p := base) (some (key, key)) (by omega)
  obtain ⟨hpres_raw, ⟨hm, hM⟩, hq, hspan⟩ := hheader
  have hpres : s.mem base = 1 := hpres_raw
  have hle : m ≤ M := (ht.extrema_of_bounds hb).1
  by_cases heq : key = m
  · have hins : tree.insert key = tree := by
      cases tree <;> simp_all [Tree.bounds, Tree.insert, min_self]
    apply insertLoop_finish hs
    apply WP.exists_execWithin
    unfold insertBody readAt
    wram_exec [hp, hx, hz, ho, hpres, hm, heq]
    exact ⟨by wram_simp [hz], by wram_simp, by wram_simp [hins, hr], fun _ _ => by wram_simp⟩
  cases tree with
  | leaf b =>
    obtain rfl : b = some (m, M) := hb
    apply insertLoop_finish hs
    refine exists_execWithin_insertBody_occupied hs hpres hm hM hle heq hbase4
      fun y hy hy_mem => ?_
    have hy_p := hy.p_eq; have hy_0 := hy.zero_eq; have hy_3 := hy.three_eq
    have hy_q : y.mem (base + 3) = 0 := by
      rw [hy_mem, writeBounds_away _ (Or.inr (by omega))]
      exact hq
    unfold insertTail readAt
    wram_exec [hy_p, hy_0, hy_3, hy_q]
    refine ⟨by wram_simp [hy_0], by wram_simp, ?_, ?_⟩
    · simpa only [Data.set_mem, hy_mem, Tree.insert, Tree.withBounds] using
        rep_writeBounds hr (some (min m key, max M key))
    · intro a ha'
      simpa only [Data.set_mem, hy_mem] using
        writeBounds_away (mem := s.mem) (p := base) (some (min m key, max M key))
          (by simp only [span_zero] at ha'; omega)
  | @node d b summary cluster =>
    obtain rfl : b = some (m, M) := hb
    obtain ⟨hi, hlo_lt, hend⟩ := insert_descent_safe (base := base) ht hkey
    have hqne : universeSize d ≠ 0 := Nat.ne_of_gt (universeSize_pos d)
    have hu := universeSize_le_span d
    have hu' := span_le_succ d
    have h5_d := five_le_span d
    have hlo_fit : Fits w (max m key % universeSize d) := ha.of_le (by omega)
    have hnext_fit : Fits w (max m key / universeSize d + 1) := ha.of_le (by omega)
    have hch2_fit : Fits w (base + 5 + (max m key / universeSize d + 1) * span d + 2) :=
      ha.of_le (by dsimp only [clusterOffset] at hend; omega)
    let i : Fin (universeSize d) := ⟨max m key / universeSize d, hi⟩
    let lo := max m key % universeSize d
    let ch := base + clusterOffset d i.val
    let m₁ := writeBounds s.mem base (some (min m key, max M key))
    have hr₁ : Rep (.node (some (min m key, max M key)) summary cluster) base m₁ :=
      rep_writeBounds hr (some (min m key, max M key))
    have hch_away : ∀ y : Data 32, y.mem = m₁ →
        y.mem (base + 3) = universeSize d ∧ y.mem (base + 4) = span d ∧
          y.mem (base + 5 + (max m key / universeSize d + 1) * span d) = s.mem ch := by
      intro y hy_mem
      rw [hy_mem]
      refine ⟨(writeBounds_away _ (Or.inr (by omega))).trans hq,
        (writeBounds_away _ (Or.inr (by omega))).trans hspan, ?_⟩
      simpa only [ch, clusterOffset, i, Nat.add_assoc] using
        writeBounds_away (mem := s.mem) (p := base) (some (min m key, max M key))
          (Or.inr (by omega))
    cases hcb : (cluster i).bounds with
    | none =>
      have hch0 : s.mem ch = 0 := by
        simpa only [ch, hcb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using
          (hr.2.2 i).header.1
      have hstep : ∃ next, ExecWithin w insertBody s next 37 ∧
          InsertEntry (base + summaryOffset) i.val next ∧
          next.mem = writeBounds m₁ ch (some (lo, lo)) := by
        refine exists_execWithin_insertBody_occupied hs hpres hm hM hle heq hbase4
          fun y hy hy_mem => ?_
        obtain ⟨hy_q, hy_t, hy_ch⟩ := hch_away y hy_mem
        have hy_ch0 : y.mem (base + 5 + (max m key / universeSize d + 1) * span d) = 0 :=
          hy_ch.trans hch0
        have hy_0 := hy.zero_eq; have hy_1 := hy.one_eq; have hy_2 := hy.two_eq
        have hy_3 := hy.three_eq; have hy_4 := hy.four_eq; have hy_5 := hy.five_eq
        have hy_p := hy.p_eq; have hy_x := hy.x_eq; have hy_run := hy.runFlag_eq
        unfold insertTail readAt writeAt coordinates
        wram_exec [hy_0, hy_1, hy_2, hy_3, hy_4, hy_5, hy_p, hy_x, hy_q, hy_t, hqne, hy_ch0]
        refine ⟨by struct_frame hy, ?_⟩
        simp only [Data.set_mem, Data.write_mem, hy_mem, m₁, writeBounds, ch, clusterOffset, i, lo,
          Nat.add_assoc]
      obtain ⟨next, he_step, hentry, hnext_mem⟩ := hstep
      have hr₂ : Rep (.node (some (min m key, max M key)) summary
          (Function.update cluster i ((cluster i).withBounds (some (lo, lo)))))
          base next.mem :=
        rep_replace_cluster hr₁ i (hnext_mem ▸ rep_writeBounds (hr₁.2.2 i) (some (lo, lo)))
          fun a ha' => hnext_mem ▸ writeBounds_away (some (lo, lo)) (by dsimp only [ch]; omega)
      have hfit_sum : Fits w (base + summaryOffset + span d) :=
        ha.of_le (by have := summary_end_le_span d; omega)
      obtain ⟨z, hz_loop, hrs_z, hframe_z⟩ :=
        insertLoop_spec hentry ht.2.1 hr₂.2.1 i.isLt hfit_sum
      refine ⟨z, (he_step.loop_iter (cond := .lt zero runFlag) ?_ hz_loop).mono (by omega), ?_, ?_⟩
      · simp only [Cond.holds_lt, hz, hrun]
        decide
      · have hr_final := rep_replace_summary hr₂ hrs_z hframe_z
        dsimp only [i] at hcb
        simpa only [Tree.insert, heq, ↓reduceIte, hi, ↓reduceDIte, i, lo, hcb] using hr_final
      · intro a ha'
        have hsum_end := summary_end_le_span d
        rw [hframe_z a (by dsimp only [summaryOffset] at hsum_end ⊢; omega), hnext_mem,
          writeBounds_away (some (lo, lo)) (by dsimp only [ch, i] at hend ⊢; omega)]
        exact writeBounds_away (some (min m key, max M key)) (by omega)
    | some cbounds =>
      have hch1 : s.mem ch = 1 := by
        simpa only [ch, hcb, Option.isSome_some, ↓reduceIte] using (hr.2.2 i).header.1
      have hstep : ∃ next, ExecWithin w insertBody s next 37 ∧
          InsertEntry ch lo next ∧ next.mem = m₁ := by
        refine exists_execWithin_insertBody_occupied hs hpres hm hM hle heq hbase4
          fun y hy hy_mem => ?_
        obtain ⟨hy_q, hy_t, hy_ch⟩ := hch_away y hy_mem
        have hy_ch_ne0 : y.mem (base + 5 + (max m key / universeSize d + 1) * span d) ≠ 0 := by
          rw [hy_ch, hch1]; decide
        have hy_0 := hy.zero_eq; have hy_1 := hy.one_eq; have hy_2 := hy.two_eq
        have hy_3 := hy.three_eq; have hy_4 := hy.four_eq; have hy_5 := hy.five_eq
        have hy_p := hy.p_eq; have hy_x := hy.x_eq; have hy_run := hy.runFlag_eq
        unfold insertTail readAt coordinates
        wram_exec [hy_0, hy_1, hy_2, hy_3, hy_4, hy_5, hy_p, hy_x, hy_q, hy_t, hqne, hy_ch_ne0]
        exact ⟨by struct_frame hy; wram_simp [ch, clusterOffset, i, Nat.add_assoc],
          by wram_simp [hy_mem]; rfl⟩
      obtain ⟨next, he_step, hentry, hnext_mem⟩ := hstep
      have hrc_next : Rep (cluster i) ch next.mem := hnext_mem ▸ hr₁.2.2 i
      have hfit_cl : Fits w (ch + span d) := ha.of_le hend
      obtain ⟨z, hz_loop, hrc_z, hframe_z⟩ :=
        insertLoop_spec hentry (ht.2.2.1 i) hrc_next hlo_lt hfit_cl
      refine ⟨z, (he_step.loop_iter (cond := .lt zero runFlag) ?_ hz_loop).mono (by omega), ?_, ?_⟩
      · simp only [Cond.holds_lt, hz, hrun]
        decide
      · have hr_final : Rep (.node (some (min m key, max M key)) summary
            (Function.update cluster i ((cluster i).insert lo))) base z.mem :=
          rep_replace_cluster hr₁ i hrc_z fun a ha' => hnext_mem ▸ hframe_z a ha'
        dsimp only [i] at hcb
        simpa only [Tree.insert, heq, ↓reduceIte, hi, ↓reduceDIte, i, lo, hcb] using hr_final
      · intro a ha'
        have hstart : 5 ≤ clusterOffset d i.val := by dsimp only [clusterOffset]; omega
        rw [hframe_z a (by dsimp only [ch, i] at hend ⊢; omega), hnext_mem]
        exact writeBounds_away (some (min m key, max M key)) (by omega)

end Cslib.DataStructure.VanEmdeBoas.WordRAM
