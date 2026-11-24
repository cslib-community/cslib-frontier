/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvTickB1
-- Unfolds `migrateStepProg` and `migrateBatchProg` to prove their `EpochSlotInv` specifications.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochProgs

/-!
# Background Tick Phase `8` (`DualEpochInvTickB2`)

Proves `migrateStepProg_eval`, `migrateStepProg_spec`, `migrateBatchProg_spec`, and
`tickPhase8_spec` (`BgTickPre` and `DualPostTickInv` for Phase `8` `tickMigrateProg`, covering `8 →
8` batch countdown and `8 → 9` `pageBeginUnpermBoundedProg` unpermutation entry).

## Main results

* `migrateStepProg_eval`, `migrateStepProg_spec`, `migrateBatchProg_spec`, `tickPhase8_spec`

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open EpochUpdate

/-! ## Section 1: `migrateStepProg` and `migrateBatchProg` Evaluation and `EpochSlotInv` Specs -/

/-- Exact state, result, and `memoryCost` unfolding of `migrateStepProg`. -/
theorem migrateStepProg_eval (pSrc pDst moved : ℕ) (s : Memory.State) :
    let nS := (Memory.spec 0).clientResult s (epochReadNSideProg pSrc)
    let qv := (Memory.spec 0).clientResult s (epochPopAnyProg pSrc)
    let s_pop := (Memory.spec 0).clientState s (epochPopAnyProg pSrc)
    (Memory.spec 0).clientResult s (migrateStepProg ((pSrc, pDst), moved)) = 0 ∧
    (Memory.spec 0).clientState s (migrateStepProg ((pSrc, pDst), moved)) =
      (if 0 < nS then (Memory.spec 0).clientState s_pop (epochInsertProg ((pDst, qv.1), qv.2))
       else s) ∧
    memoryCost (migrateStepProg ((pSrc, pDst), moved)) s =
      2 + (if 0 < nS then
        memoryCost (epochPopAnyProg pSrc) s +
          memoryCost (epochInsertProg ((pDst, qv.1), qv.2)) s_pop
       else 0) := by
  dsimp only
  unfold migrateStepProg; dsimp only
  rw [prog_clientResult_bind, StateTransitionSpec.clientState_bind,
    Realization.memoryCost_bind', clientState_epochReadNSideProg, memoryCost_epochReadNSideProg]
  set nS := (Memory.spec 0).clientResult s (epochReadNSideProg pSrc)
  by_cases hpos : 0 < nS
  · rw [ite_eq_left hpos, ite_eq_left hpos, ite_eq_left hpos,
      prog_clientResult_bind, prog_clientResult_bind, prog_clientResult_pure,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      Realization.memoryCost_bind', Realization.memoryCost_bind', memoryCost_pure]
    exact ⟨rfl, rfl, by omega⟩
  · rw [ite_eq_right hpos, ite_eq_right hpos, ite_eq_right hpos, prog_clientResult_pure,
      memoryCost_pure]
    exact ⟨rfl, rfl, rfl⟩

theorem migrateBatchProg_zero (pSrc pDst moved : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (migrateBatchProg (((pSrc, pDst), moved), 0)) = s ∧
    memoryCost (migrateBatchProg (((pSrc, pDst), moved), 0)) s = 0 := by
  unfold migrateBatchProg iterate
  exact ⟨rfl, memoryCost_pure moved s⟩

theorem migrateBatchProg_succ (pSrc pDst moved fuel : ℕ) (s : Memory.State) :
    let s1 := (Memory.spec 0).clientState s (migrateStepProg ((pSrc, pDst), moved))
    let r1 := (Memory.spec 0).clientResult s (migrateStepProg ((pSrc, pDst), moved))
    (Memory.spec 0).clientState s (migrateBatchProg (((pSrc, pDst), moved), fuel + 1)) =
      (Memory.spec 0).clientState s1 (migrateBatchProg (((pSrc, pDst), r1), fuel)) ∧
    memoryCost (migrateBatchProg (((pSrc, pDst), moved), fuel + 1)) s =
      memoryCost (migrateStepProg ((pSrc, pDst), moved)) s +
        memoryCost (migrateBatchProg (((pSrc, pDst), r1), fuel)) s1 := by
  dsimp only
  unfold migrateBatchProg; dsimp only
  rw [Cslib.WordRAM.Realization.iterate.eq_def,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  exact ⟨rfl, rfl⟩

attribute [local irreducible] migrateStepProg migrateBatchProg epochMetaWordsWhp

/-- Side `0` (`side = false`) of a valid paged `SlotIoLayout` always forces `cleanPhase = 0`. -/
theorem cleanPhase_zero_of_paged0 {c U V w fr pSrc mbSrc : ℕ} {pgHost : PageArenaLayout}
    {dr : Bool} {sl : SlotLatent c U V} {m : ℕ → ℕ}
    (hs : EpochSlotInv c U V w fr pSrc mbSrc (pagedSlotIo 0 pgHost) 0 dr sl m) :
    (extractPageUnperm pgHost m).cleanPhase = 0 := by
  have hi := hs.io_stateInv
  unfold SlotIoLayout.StateInv pagedSlotIo SlotIoLayout.side at hi
  simp only [Nat.reduceEqDiff, ne_eq, not_true_eq_false, decide_false, ↓reduceIte] at hi
  exact Nat.eq_zero_of_not_pos fun hp => Bool.noConfusion (hi.2.2.2.2.2.1 hp)

/-- Single-step specification of `migrateStepProg` across coupled `pagedSlotIo 0` / `pagedSlotIo 1`
slots. -/
theorem migrateStepProg_spec {c U V w pSrc mbSrc pDst mbDst moved : ℕ}
    {pgHost : PageArenaLayout} {slSrc slDst : SlotLatent c U V} {s : Memory.State}
    (hs : EpochSlotInv c U V w s.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc s.mem)
    (hd : EpochSlotInv c U V w s.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false slDst s.mem)
    (hdj : DisjointOpt slDst.s_abs slSrc.s_abs)
    (_hp_disj : pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc)
    (hpm_s : pDst + 64 ≤ mbSrc ∨
      mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ pDst)
    (hpm_d : pSrc + 64 ≤ mbDst ∨
      mbDst + (if slDst.nCap = 0 then 2 else offPageDir c w slDst.nCap) ≤ pSrc)
    (hmm_disj :
      mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ mbDst ∨
      mbDst + (if slDst.nCap = 0 then 2 else offPageDir c w slDst.nCap) ≤ mbSrc)
    (hcap_d : slDst.nCap ≠ 0 →
      (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card ≤ slDst.nCap)
    (hcap_pg : (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card ≤ pgHost.nCap) :
    let s' := (Memory.spec 0).clientState s (migrateStepProg ((pSrc, pDst), moved))
    MigrateStepPre w ((pSrc, pDst), moved) s ∧
    (Memory.spec 0).clientResult s (migrateStepProg ((pSrc, pDst), moved)) = 0 ∧
    s'.frontier = s.frontier ∧
    ∃ (s_src' s_dst' : Fin U → Option (Fin V)) (extra : List (EpochUpdate U V)),
      let slSrc' : SlotLatent c U V := ⟨slSrc.nCap, s_src', slSrc.seeds, slSrc.evs⟩
      let slDst' : SlotLatent c U V := ⟨slDst.nCap, s_dst', slDst.seeds, slDst.evs ++ extra⟩
      (liveDom s_src').card = (liveDom slSrc.s_abs).card - 1 ∧
      slDst'.evs.length + (liveDom s_src').card =
        slDst.evs.length + (liveDom slSrc.s_abs).card ∧
      DisjointOpt s_dst' s_src' ∧
      orOpt s_dst' s_src' = orOpt slDst.s_abs slSrc.s_abs ∧
      EpochSlotInv c U V w s'.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc' s'.mem ∧
      EpochSlotInv c U V w s'.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false slDst' s'.mem ∧
      (∀ addr,
        ¬slotOwnsAddr c w mbSrc slSrc.nCap (pagedSlotIo 0 pgHost) addr →
        ¬slotOwnsAddr c w mbDst slDst.nCap (pagedSlotIo 1 pgHost) addr →
        s'.mem addr = s.mem addr) ∧
      ((slDst.nCap = 0 →
          (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card ≤ 2 * whpThreshold c) →
        slSrc.GoodCovers → slDst'.GoodCovers →
        memoryCost (migrateStepProg ((pSrc, pDst), moved)) s ≤ 2 * epochStepCost c + 2) := by
  dsimp only
  have hup0 : (pagedSlotIo 0 pgHost).usePaged ≠ 0 := Nat.one_ne_zero
  have hup1 : (pagedSlotIo 1 pgHost).usePaged ≠ 0 := Nat.one_ne_zero
  have hcp0 := cleanPhase_zero_of_paged0 hs
  have hnS_eq := hs.readNSide_eq
  obtain ⟨hres_ev, hst_ev, hmc_ev⟩ := migrateStepProg_eval pSrc pDst moved s
  dsimp only at hres_ev hst_ev hmc_ev
  by_cases hpos : 0 < (liveDom slSrc.s_abs).card
  · have hnS_pos : 0 < (Memory.spec 0).clientResult s (epochReadNSideProg pSrc) :=
      hnS_eq.symm ▸ hpos
    obtain ⟨u, v, hqv_eq, hsu, hfr_pop, hs_pop_raw, hout_pop, hpg_pop, hmc_pop⟩ :=
      hs.popAny_spec hpos
    set s_pop := (Memory.spec 0).clientState s (epochPopAnyProg pSrc)
    have hslk0_s : (if (pagedSlotIo 0 pgHost).usePaged = 0 ∨
        (extractPageUnperm (pagedSlotIo 0 pgHost).pgL s.mem).cleanPhase = 0
        then 0 else 24) = 0 := ite_eq_left (Or.inr hcp0)
    have hs_pop : EpochSlotInv c U V w s_pop.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
        ⟨slSrc.nCap, Function.update slSrc.s_abs u none, slSrc.seeds, slSrc.evs⟩ s_pop.mem := by
      simpa only [hslk0_s] using hs_pop_raw
    have hcp_pop := cleanPhase_zero_of_paged0 hs_pop
    obtain ⟨hno_s_pDst, hno_s_mDst⟩ :=
      not_paged_slotOwnsAddr_partner (sbA := 0) (slA := slSrc) hd hpm_s hmm_disj
    obtain ⟨hno_d_pSrc, hno_d_mSrc⟩ :=
      not_paged_slotOwnsAddr_partner (sbA := 1) (slA := slDst) hs hpm_d hmm_disj.symm
    have hd_pop : EpochSlotInv c U V w s_pop.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        slDst s_pop.mem :=
      (hfr_pop ▸ hd).partner_paged_frame hs_pop.io_stateInv hcp_pop
        (fun a h1 h2 => hout_pop a (hno_s_pDst a h1 h2))
        (fun a ha => hout_pop a (hno_s_mDst a ha))
        (hpg_pop hup0).1 (hpg_pop hup0).2.2
    obtain ⟨hd_u_none, hor_eq, hdj'⟩ := orOpt_migrate_pop_insert hdj hsu
    have hsrc_card_pop :
        (liveDom (Function.update slSrc.s_abs u none)).card = (liveDom slSrc.s_abs).card - 1 := by
      rw [liveDom_delete_card, ite_eq_right (by rw [hsu]; exact Option.some_ne_none v)]
    have hti_pop : (extractPagePair pgHost s_pop.mem).totalItems =
        (liveDom (Function.update slSrc.s_abs u none)).card + (liveDom slDst.s_abs).card := by
      have hi0 := hs_pop.io_stateInv; have hi1 := hd_pop.io_stateInv
      unfold SlotIoLayout.StateInv at hi0 hi1
      rw [ite_eq_right hup0] at hi0; rw [ite_eq_right hup1] at hi1
      have h0_vl : (extractPagePair pgHost s_pop.mem).virtLen false = s_pop.mem (mbSrc + 1) :=
        hi0.2.2.2.2.1
      have h1_vl : (extractPagePair pgHost s_pop.mem).virtLen true = s_pop.mem (mbDst + 1) :=
        hi1.2.2.2.2.1
      have hns0 := hs_pop.mem_nSide_eq; have hns1 := hd_pop.mem_nSide_eq
      dsimp only at hns0
      unfold PagePairState.totalItems
      rw [h0_vl, h1_vl, hns0, hns1]
    have hcap_n_d : slDst.s_abs u = none → slDst.nCap ≠ 0 →
        (liveDom slDst.s_abs).card < slDst.nCap := fun _ hne_d => by
      have := hcap_d hne_d; clear *- hpos this; omega
    have hcap_io_d : slDst.s_abs u = none →
        (liveDom slDst.s_abs).card < (pagedSlotIo 1 pgHost).pgL.nCap ∧
        ((pagedSlotIo 1 pgHost).usePaged ≠ 0 →
          (extractPagePair (pagedSlotIo 1 pgHost).pgL s_pop.mem).totalItems + 1 ≤
            (pagedSlotIo 1 pgHost).pgL.nCap) := fun _ => by
      dsimp only [pagedSlotIo]; rw [hti_pop, hsrc_card_pop]
      exact ⟨by clear *- hpos hcap_pg; omega, fun _ => by clear *- hpos hcap_pg; omega⟩
    have hpre_step : MigrateStepPre w ((pSrc, pDst), moved) s :=
      ⟨hs.epochProgPre, fun _ => hd_pop.epochInsertProgPre⟩
    have hsp_ins := hd_pop.insert_spec u v hcap_n_d hcap_io_d
    dsimp only at hsp_ins
    set s_ins := (Memory.spec 0).clientState s_pop (epochInsertProg ((pDst, u.val), v.val))
    have hfr_ins : s_ins.frontier = s.frontier := hsp_ins.1.trans hfr_pop
    have hslk0_d : (if (pagedSlotIo 1 pgHost).usePaged = 0 ∨
        (extractPageUnperm (pagedSlotIo 1 pgHost).pgL s_pop.mem).cleanPhase = 0
        then 0 else 24) = 0 := ite_eq_left (Or.inr hcp_pop)
    have hd_ins : EpochSlotInv c U V w s_ins.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        ⟨slDst.nCap, Function.update slDst.s_abs u (some v), slDst.seeds,
          slDst.evs ++ [EpochUpdate.insert u v]⟩ s_ins.mem := by
      simpa only [hslk0_d] using hsp_ins.2.1
    have hcp_ins : (extractPageUnperm pgHost s_ins.mem).cleanPhase = 0 :=
      (hd_pop.insert_paged_unperm hup1 u v hcap_n_d
        (fun hnone => ⟨(hcap_io_d hnone).1, (hcap_io_d hnone).2 hup1⟩)).1 hcp_pop
    have hs_ins : EpochSlotInv c U V w s_ins.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
        ⟨slSrc.nCap, Function.update slSrc.s_abs u none, slSrc.seeds, slSrc.evs⟩ s_ins.mem :=
      (hsp_ins.1 ▸ hs_pop).partner_paged_frame
        hd_ins.io_stateInv hcp_ins
        (fun a h1 h2 => hsp_ins.2.2.1 a (hno_d_pSrc a h1 h2))
        (fun a ha => hsp_ins.2.2.1 a (hno_d_mSrc a ha))
        (hsp_ins.2.2.2.2.1 hup1).1 (hsp_ins.2.2.2.2.1 hup1).2
    rw [hst_ev, ite_eq_left hnS_pos, hqv_eq]
    refine ⟨hpre_step, hres_ev, hfr_ins, Function.update slSrc.s_abs u none,
      Function.update slDst.s_abs u (some v), [EpochUpdate.insert u v],
      hsrc_card_pop, by rw [List.length_append, List.length_singleton, hsrc_card_pop]; omega,
      hdj', hor_eq, hs_ins, hd_ins,
      fun addr hns hnd => (hsp_ins.2.2.1 addr hnd).trans (hout_pop addr hns),
      fun hd_sm hgc_s hgc_d => ?_⟩
    rw [hmc_ev, ite_eq_left hnS_pos, hqv_eq]
    dsimp only [s_pop] at *
    have hc1 := hmc_pop hgc_s
    have hc2 := hsp_ins.2.2.2.2.2
      (fun h0 => le_trans (Nat.le_add_right _ _) (hd_sm h0)) hgc_d
    clear *- hc1 hc2; omega
  · have hnS_np : ¬(0 < (Memory.spec 0).clientResult s (epochReadNSideProg pSrc)) :=
      hnS_eq.symm ▸ hpos
    have hc0 : (liveDom slSrc.s_abs).card = 0 := Nat.eq_zero_of_not_pos hpos
    have hpre_step : MigrateStepPre w ((pSrc, pDst), moved) s :=
      ⟨hs.epochProgPre, fun hp => absurd hp hnS_np⟩
    rw [hst_ev, ite_eq_right hnS_np]
    have hsl_s_eq : (⟨slSrc.nCap, slSrc.s_abs, slSrc.seeds, slSrc.evs⟩ : SlotLatent c U V) =
        slSrc := by cases slSrc; rfl
    have hsl_d_eq : (⟨slDst.nCap, slDst.s_abs, slDst.seeds, slDst.evs ++ []⟩ : SlotLatent c U V) =
        slDst := by cases slDst; simp
    refine ⟨hpre_step, hres_ev, rfl, slSrc.s_abs, slDst.s_abs, [],
      by rw [hc0], by simp, hdj, rfl,
      by rw [hsl_s_eq]; exact hs,
      by rw [hsl_d_eq]; exact hd,
      fun _ _ _ => rfl, fun _ _ _ => ?_⟩
    rw [hmc_ev, ite_eq_right hnS_np]; omega

/-- Batched `fuel`-step specification of `migrateBatchProg`. -/
theorem migrateBatchProg_spec {c U V w pSrc mbSrc pDst mbDst moved : ℕ}
    {pgHost : PageArenaLayout} {slSrc slDst : SlotLatent c U V} {s : Memory.State}
    (hs : EpochSlotInv c U V w s.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc s.mem)
    (hd : EpochSlotInv c U V w s.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false slDst s.mem)
    (hdj : DisjointOpt slDst.s_abs slSrc.s_abs)
    (hp_disj : pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc)
    (hpm_s : pDst + 64 ≤ mbSrc ∨
      mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ pDst)
    (hpm_d : pSrc + 64 ≤ mbDst ∨
      mbDst + (if slDst.nCap = 0 then 2 else offPageDir c w slDst.nCap) ≤ pSrc)
    (hmm_disj :
      mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ mbDst ∨
      mbDst + (if slDst.nCap = 0 then 2 else offPageDir c w slDst.nCap) ≤ mbSrc)
    (hcap_d : slDst.nCap ≠ 0 →
      (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card ≤ slDst.nCap)
    (hcap_pg : (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card ≤ pgHost.nCap)
    (fuel : ℕ) :
    let s' := (Memory.spec 0).clientState s (migrateBatchProg (((pSrc, pDst), moved), fuel))
    iterationSafe migrateStepProg MigrateStepPre w (pSrc, pDst) fuel moved s ∧
    s'.frontier = s.frontier ∧
    ∃ (s_src' s_dst' : Fin U → Option (Fin V)) (extra : List (EpochUpdate U V)),
      let slSrc' : SlotLatent c U V := ⟨slSrc.nCap, s_src', slSrc.seeds, slSrc.evs⟩
      let slDst' : SlotLatent c U V := ⟨slDst.nCap, s_dst', slDst.seeds, slDst.evs ++ extra⟩
      (liveDom s_src').card = (liveDom slSrc.s_abs).card - fuel ∧
      slDst'.evs.length + (liveDom s_src').card =
        slDst.evs.length + (liveDom slSrc.s_abs).card ∧
      DisjointOpt s_dst' s_src' ∧
      orOpt s_dst' s_src' = orOpt slDst.s_abs slSrc.s_abs ∧
      EpochSlotInv c U V w s'.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc' s'.mem ∧
      EpochSlotInv c U V w s'.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false slDst' s'.mem ∧
      (∀ addr,
        ¬slotOwnsAddr c w mbSrc slSrc.nCap (pagedSlotIo 0 pgHost) addr →
        ¬slotOwnsAddr c w mbDst slDst.nCap (pagedSlotIo 1 pgHost) addr →
        s'.mem addr = s.mem addr) ∧
      ((slDst.nCap = 0 →
          (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card ≤ 2 * whpThreshold c) →
        slSrc.GoodCovers → slDst'.GoodCovers →
        memoryCost (migrateBatchProg (((pSrc, pDst), moved), fuel)) s ≤
          fuel * (2 * epochStepCost c + 2)) := by
  dsimp only
  induction fuel generalizing s moved slSrc slDst with
  | zero =>
    obtain ⟨hst0, hmc0⟩ := migrateBatchProg_zero pSrc pDst moved s
    rw [hst0]
    have hsl_s_eq : (⟨slSrc.nCap, slSrc.s_abs, slSrc.seeds, slSrc.evs⟩ : SlotLatent c U V) =
        slSrc := by cases slSrc; rfl
    have hsl_d_eq : (⟨slDst.nCap, slDst.s_abs, slDst.seeds, slDst.evs ++ []⟩ : SlotLatent c U V) =
        slDst := by cases slDst; simp
    exact ⟨trivial, rfl, slSrc.s_abs, slDst.s_abs, [], Nat.sub_zero _, by simp,
      hdj, rfl,
      by rw [hsl_s_eq]; exact hs,
      by rw [hsl_d_eq]; exact hd,
      fun _ _ _ => rfl,
      fun _ _ _ => by rw [hmc0]; exact Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨hpre1, hres1, hfr1, s_src1, s_dst1, ex1, hcd1, hsum1, hdj1, hor1, hs1, hd1, hout1,
      hmc1⟩ := migrateStepProg_spec hs hd hdj hp_disj hpm_s hpm_d hmm_disj hcap_d hcap_pg
    set s1 := (Memory.spec 0).clientState s (migrateStepProg ((pSrc, pDst), moved))
    set slSrc1 : SlotLatent c U V := ⟨slSrc.nCap, s_src1, slSrc.seeds, slSrc.evs⟩
    set slDst1 : SlotLatent c U V := ⟨slDst.nCap, s_dst1, slDst.seeds, slDst.evs ++ ex1⟩
    have hcard_tot_eq :
        (liveDom s_dst1).card + (liveDom s_src1).card =
          (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card := by
      rw [← liveDom_orOpt_card hdj1, hor1, liveDom_orOpt_card hdj]
    have hih := ih (s := s1) (moved := 0) (slSrc := slSrc1) (slDst := slDst1)
      hs1 hd1 hdj1 hpm_s hpm_d hmm_disj
      (fun hne => hcard_tot_eq ▸ hcap_d hne) (hcard_tot_eq ▸ hcap_pg)
    obtain ⟨hsafe2, hfr2, s_src2, s_dst2, ex2, hcd2, hsum2, hdj2, hor2, hs2, hd2, hout2, hmc2⟩ :=
      hih
    obtain ⟨hst_b, hmc_b⟩ := migrateBatchProg_succ pSrc pDst moved k s
    dsimp only at hst_b hmc_b
    rw [hres1] at hst_b hmc_b
    have hsafe_tot : iterationSafe migrateStepProg MigrateStepPre w (pSrc, pDst) (k + 1) moved s :=
      by
        unfold iterationSafe
        rw [clientResult_width, clientState_width, hres1]
        exact ⟨hpre1, hsafe2⟩
    rw [hst_b]
    have hevs_assoc : (slDst.evs ++ ex1) ++ ex2 = slDst.evs ++ (ex1 ++ ex2) :=
      List.append_assoc _ _ _
    have hd2' : EpochSlotInv c U V w
        ((Memory.spec 0).clientState s1 (migrateBatchProg (((pSrc, pDst), 0), k))).frontier
        pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        ⟨slDst.nCap, s_dst2, slDst.seeds, slDst.evs ++ (ex1 ++ ex2)⟩
        ((Memory.spec 0).clientState s1 (migrateBatchProg (((pSrc, pDst), 0), k))).mem := by
      simpa only [slDst1, hevs_assoc] using hd2
    refine ⟨hsafe_tot, hfr2.trans hfr1, s_src2, s_dst2, ex1 ++ ex2,
      by rw [hcd2]; dsimp only [slSrc1]; rw [hcd1]; omega,
      by dsimp only [slDst1] at hsum2 ⊢; rw [← hevs_assoc]; exact hsum2.trans hsum1,
      hdj2, hor2.trans hor1, hs2, hd2',
      fun addr hns hnd => (hout2 addr hns hnd).trans (hout1 addr hns hnd),
      fun hd_sm hgc_s hgc_d2 => ?_⟩
    have hgc_d1 : slDst1.GoodCovers :=
      SlotLatent.GoodCovers.of_append (s₂ := s_dst2) (extra := ex2) (by
        simpa only [slDst1, hevs_assoc] using hgc_d2)
    have hc1 := hmc1 hd_sm hgc_s hgc_d1
    have hc2 := hmc2 (fun h0 => hcard_tot_eq ▸ hd_sm h0) hgc_s
      (by simpa only [slDst1, hevs_assoc] using hgc_d2)
    rw [hmc_b]
    calc memoryCost (migrateStepProg ((pSrc, pDst), moved)) s +
          memoryCost (migrateBatchProg (((pSrc, pDst), 0), k)) s1
        ≤ (2 * epochStepCost c + 2) + k * (2 * epochStepCost c + 2) := Nat.add_le_add hc1 hc2
      _ = (k + 1) * (2 * epochStepCost c + 2) := by ring

/-! ## Section 2: Phase `8` (`tickMigrateProg`) Specification -/

/-- Helper proving `DualPreShrinkInv` for the `8 → 9` (`pageBeginUnpermBoundedProg`) branch of
Phase `8`. -/
private theorem tickPhase8_finish_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s s1 s3 s_tick : Memory.State}
    {s_src1 s_dst1 : Fin U → Option (Fin V)} {ex1 : List (EpochUpdate U V)}
    (h : DualMidInv c U V w base s_dict L s)
    (hp8 : s.mem (base + hdrPhase) = 8)
    (h1 : ¬(1 < s.mem (base + hdrRem)))
    (hwf_tick : Memory.WellFormed w s_tick)
    (hfr_tick : s_tick.frontier = s.frontier)
    (hfr_s1 : s1.frontier = s.frontier)
    (hs1_hdr48 : ∀ off < 48, s1.mem (base + off) = s.mem (base + off))
    (hown_pg_ge :
      ∀ a, (dualPgHost c V w base (Dictionary.dom s_dict).card s.mem).OwnsAddr a → base + 210 ≤ a)
    (hcd1 : (liveDom s_src1).card = (liveDom L.slotSrc.s_abs).card - itemBatchWhp)
    (hsum1 : (L.slotDst.evs ++ ex1).length + (liveDom s_src1).card =
      L.slotDst.evs.length + (liveDom L.slotSrc.s_abs).card)
    (hor1 : orOpt s_dst1 s_src1 = orOpt L.slotDst.s_abs L.slotSrc.s_abs)
    (hs1 : EpochSlotInv c U V w s1.frontier (dualPSrc base s.mem) (dualMbSrc base s.mem)
      (pagedSlotIo 0 (dualPgHost c V w base (Dictionary.dom s_dict).card s.mem)) 0 true
      ⟨L.slotSrc.nCap, s_src1, L.slotSrc.seeds, L.slotSrc.evs⟩ s1.mem)
    (hd1 : EpochSlotInv c U V w s1.frontier
      (if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0)
      (dualMbDst base s.mem)
      (pagedSlotIo 1 (dualPgHost c V w base (Dictionary.dom s_dict).card s.mem)) 0 false
      ⟨L.slotDst.nCap, s_dst1, L.slotDst.seeds, L.slotDst.evs ++ ex1⟩ s1.mem)
    (hs3_def : (Memory.spec 0).clientState s1
      (pageBeginUnpermBoundedProg
        (dualPgHost c V w base (Dictionary.dom s_dict).card s.mem).toCtx) = s3)
    (hm_eq :
      let pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s.mem
      let uTicks := max (whpThreshold c) (s.mem (base + hdrNSrc)) / 240 + pgH.pgB / 8 + 4
      s_tick.mem =
        Function.update (Function.update
          (Function.update s3.mem (base + hdrUnpermDone) 0)
          (base + hdrRem) uTicks)
          (base + hdrPhase) 9) :
    let pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s.mem
    let u3 := extractPageUnperm pgH s3.mem
    DualPreShrinkInv c U V w base s_dict
      { L with
        slotSrc := ⟨L.slotSrc.nCap, s_src1, L.slotSrc.seeds, L.slotSrc.evs⟩
        slotDst := ⟨L.slotDst.nCap, s_dst1, L.slotDst.seeds, L.slotDst.evs ++ ex1⟩
        elapsed := L.elapsed + 1
        unpermBound := u3.unpermRank }
      s_tick := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hstg_le := h.stg_le; have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src
  have hnSrc_b := h.nSrc_bounds; have hpad_fits := h.pad_fits
  obtain ⟨hth_h, _, _, _, _, _, hv_hi, hv_fr, _⟩ :=
    dualPgHost_eval_valid h (by clear *- hp8; omega) (by clear *- hp8; omega)
  have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) h
    (by clear *- hp8; omega) (by clear *- hp8; omega)
  have hnH_ref := dualNHost_le_two_nRef h (by clear *- hp8; omega)
  have hpgB_ref := pageSizeWhp_host_le_ref hth_h.1 hnH_ref
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp8; omega)] at hsched
  obtain ⟨hfr_hi_lo, hfr_hi_hi⟩ := hsched.ph3_10 ⟨by clear *- hp8; omega, by clear *- hp8; omega⟩
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hd_logs, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp8; omega)
  obtain ⟨_, hb_tot, hb_el⟩ := hsched.budget
  obtain ⟨hrem_ge1, _, hcard_rem⟩ := h.ph8_inv hp8
  obtain ⟨_, hcap_d, _, hdict_or, _, _, _, _, hevs_d⟩ := h.sl_8 hp8
  obtain ⟨_, hvb_w, _, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits h
  have hw_pos : 0 < w := by clear *- hw11; omega
  have hnL_ref := (active_nLive_le_two_nRef hsched.post_trig hsched.trig_cap hsched.drift_hi
    hsched.drift_lo (by clear *- hb_el; simp only [↓reduceIte]; omega) hlive_le).2
  set nLive := (Dictionary.dom s_dict).card
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qLo := s.mem (base + hdrQLo)
  set qHi := s.mem (base + hdrQHi)
  set rem := s.mem (base + hdrRem)
  set vB := valBits V
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  set nHost := dualNHost base s.mem
  set pgH := dualPgHost c V w base nLive s.mem
  set pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
  set slSrc1 : SlotLatent c U V := ⟨L.slotSrc.nCap, s_src1, L.slotSrc.seeds, L.slotSrc.evs⟩
  set slDst1 : SlotLatent c U V := ⟨L.slotDst.nCap, s_dst1, L.slotDst.seeds, L.slotDst.evs ++ ex1⟩
  have hmD_pad : mDst ≤ pad := by rw [hpad_eq]; exact le_max_right _ _
  have hibHi_ge : base + 196 ≤ ibHi := by rw [hibHi_eq]; split_ifs <;> (clear *-; omega)
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    have hle1 : s.frontier ≤ ibHi + pairStreamWords (nLive + 1) qHi vB w := hfr_hi_hi
    have hstep := pairStreamWords_succ_le_add_two (n := nLive) (qb := qHi) (vb := vB) (w := w)
      hw_pos (by clear *- hqHi_w hvb_w; omega)
    dsimp only [hiFr, bulkBatchWhp]; clear *- hle1 hstep; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive := by
    have hib_pad := (dualCoreInv_ib_fits h).2.2.2.2.2.1
    rw [ite_eq_right (by clear *- hp8; omega)] at hib_pad
    exact hfr_hi_hi.trans hib_pad
  have hbu_frm := pageBeginUnpermBoundedProg_frame pgH
  have hrem1 : rem = 1 := by clear *- hrem_ge1 h1; omega
  have hcd1_zero : (liveDom s_src1).card = 0 := by
    rw [hrem1, Nat.one_mul] at hcard_rem
    clear *- hcd1 hcard_rem; omega
  have hsrc1_empty : s_src1 = fun _ => none := by
    funext u
    by_contra hne
    have hpos : 0 < (liveDom s_src1).card :=
      Finset.card_pos.mpr ⟨u, (mem_liveDom_iff _ _).mpr hne⟩
    clear *- hpos hcd1_zero; omega
  have hor1_dst : orOpt s_dst1 s_src1 = s_dst1 := by
    rw [hsrc1_empty]; unfold orOpt; funext x; cases s_dst1 x <;> rfl
  have hdict_dst1 : toDictState s_dst1 = s_dict := by
    rw [← hor1_dst, hor1, hdict_or]
  have hio_s1 := hs1.io_stateInv
  have hio_d1 := hd1.io_stateInv
  unfold SlotIoLayout.StateInv pagedSlotIo SlotIoLayout.side at hio_s1 hio_d1
  simp only [ne_eq, not_true_eq_false, decide_false, one_ne_zero,
    not_false_eq_true, decide_true, ↓reduceIte] at hio_s1 hio_d1
  have hvl1_f : (extractPageUnperm pgH s1.mem).st.virtLen false = 0 := by
    rw [hio_s1.2.2.2.2.1, hs1.mem_nSide_eq]; exact hcd1_zero
  have hvl1_t : (extractPageUnperm pgH s1.mem).st.virtLen true = nLive := by
    rw [hio_d1.2.2.2.2.1, hd1.mem_nSide_eq]; dsimp only [slDst1]
    rw [← dom_toDictState_card, hdict_dst1]
  have hcp_s1 : (extractPageUnperm pgH s1.mem).cleanPhase = 0 := cleanPhase_zero_of_paged0 hs1
  have hbu_sp := pageBeginUnpermBoundedProg_spec (L := pgH) (s := s1)
    (hfr_s1.symm ▸ hv_fr : pgH.Valid pgH.w s1.frontier) hio_s1.2.1
  dsimp only at hbu_sp
  rw [hs3_def] at hbu_sp
  obtain ⟨_, hu_s3_eq, har_s3_eq⟩ := hbu_sp
  have hbu_out : ∀ addr, ¬pgH.OwnsAddr addr → s3.mem addr = s1.mem addr := fun addr ha =>
    hs3_def ▸ hbu_frm.mem_outside s1 addr ha
  clear hs3_def
  obtain ⟨hu3_v, hu3_pos_imp, hu3_tp⟩ := PageUnpermState.beginUnperm_spec hio_s1.1
  have hu3_pos : 0 < (extractPageUnperm pgH s3.mem).cleanPhase := by
    rw [hu_s3_eq]; exact hu3_pos_imp ⟨hcp_s1, hvl1_f⟩
  have hu3_lt4 : (extractPageUnperm pgH s3.mem).cleanPhase < 4 := by
    rw [hu_s3_eq]; unfold PageUnpermState.beginUnperm
    rw [ite_eq_left ⟨hcp_s1, hvl1_f⟩]; dsimp only; split_ifs <;> decide
  have hu3_st : (extractPageUnperm pgH s3.mem).st = (extractPageUnperm pgH s1.mem).st := by
    rw [hu_s3_eq]; unfold PageUnpermState.beginUnperm
    rw [ite_eq_left ⟨hcp_s1, hvl1_f⟩]
  set u3 := extractPageUnperm pgH s3.mem
  set uTicks := max (whpThreshold c) nSrc / 240 + pgH.pgB / 8 + 4
  set L' : DualLatent c U V :=
    { L with
      slotSrc := slSrc1
      slotDst := slDst1
      elapsed := L.elapsed + 1
      unpermBound := u3.unpermRank }
  have hout_hdr : ∀ off, off ≠ hdrUnpermDone → off ≠ hdrRem → off ≠ hdrPhase → off < 48 →
      s_tick.mem (base + off) = s.mem (base + off) := fun off h_ud h_r h_p h48 => by
    rw [hm_eq, Function.update_of_ne (base_add_ne h_p),
      Function.update_of_ne (base_add_ne h_r),
      Function.update_of_ne (base_add_ne h_ud),
      hbu_out (base + off) (fun ha => by
        have := hown_pg_ge _ ha; clear *- h48 this; omega)]
    exact hs1_hdr48 off h48
  have hph_t : s_tick.mem (base + hdrPhase) = 9 := by rw [hm_eq]; exact Function.update_self ..
  have hrem_t : s_tick.mem (base + hdrRem) = uTicks := by
    rw [hm_eq, Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
  have hud_t : s_tick.mem (base + hdrUnpermDone) = 0 := by
    rw [hm_eq, Function.update_of_ne (base_add_ne (by decide)),
      Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
  have hst_t : s_tick.mem (base + hdrStage) = stg :=
    hout_hdr hdrStage (by decide) (by decide) (by decide) (by decide)
  have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
    hout_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide)
  have hnD_t : s_tick.mem (base + hdrNDst) = nDst :=
    hout_hdr hdrNDst (by decide) (by decide) (by decide) (by decide)
  have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
    hout_hdr hdrMSrc (by decide) (by decide) (by decide) (by decide)
  have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
    hout_hdr hdrMDst (by decide) (by decide) (by decide) (by decide)
  have hpad_t : s_tick.mem (base + hdrPad) = pad :=
    hout_hdr hdrPad (by decide) (by decide) (by decide) (by decide)
  have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
    hout_hdr hdrItemLo (by decide) (by decide) (by decide) (by decide)
  have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
    hout_hdr hdrItemHi (by decide) (by decide) (by decide) (by decide)
  have hqL_t : s_tick.mem (base + hdrQLo) = qLo :=
    hout_hdr hdrQLo (by decide) (by decide) (by decide) (by decide)
  have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
    hout_hdr hdrQHi (by decide) (by decide) (by decide) (by decide)
  have hpgH_t : dualPgHost c V w base nLive s_tick.mem = pgH := by
    dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
    rw [hnD_t, hnS_t, hst_t, hpad_t, hibH_t, hqH_t]
  have hm_ge48_s3 : ∀ a, base + 48 ≤ a → s_tick.mem a = s3.mem a := fun a h48 => by
    rw [hm_eq]
    iterate 3 rw [Function.update_of_ne (by
      dsimp only [hdrUnpermDone, hdrRem, hdrPhase]; clear *- h48; omega)]
  have hu_t : extractPageUnperm pgH s_tick.mem = u3 :=
    extractPageUnperm_congr hw_pos fun a ha =>
      hm_ge48_s3 a (by have := (hdisj_pg a ha).1; clear *- this; omega)
  have har_t : arenaPairAt pgH s_tick.mem = arenaPairAt pgH s1.mem := by
    refine (funext fun p => ?_)
    have hitem : ∀ a, ibHi ≤ a → s_tick.mem a = s3.mem a := fun a ha =>
      hm_ge48_s3 a (by clear *- ha hibHi_ge; omega)
    have ha3 : arenaPairAt pgH s_tick.mem p = arenaPairAt pgH s3.mem p := by
      unfold arenaPairAt pairQuotAt pairValAt readBitSlice
      have hib_pg : pgH.itemBase = ibHi := rfl
      rw [hib_pg, hitem _ (Nat.le_add_right _ _), hitem _ (by clear *-; omega),
        hitem _ (Nat.le_add_right _ _), hitem _ (by clear *-; omega)]
    exact ha3.trans (congrFun har_s3_eq p)
  have hpD_rng : base + 64 ≤ pDst ∧ pDst + 64 ≤ base + 192 := by
    dsimp only [pDst, hdrPBase0, hdrPBase1]
    split_ifs <;> (clear *-; exact ⟨by omega, by omega⟩)
  have h8_10 : s.mem (base + hdrPhase) < 10 := by clear *- hp8; omega
  have hd_hi : EpochSlotInv c U V w hiFr (dualPDst base s_tick.mem)
      (dualMbDst base s_tick.mem) (pagedSlotIo 1 pgH) 0 false slDst1 s_tick.mem := by
    have hpD_eq : dualPDst base s_tick.mem = pDst := by
      unfold dualPDst; rw [ite_eq_left (by rw [hph_t]; decide), hst_t]
    have hmD_mb : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
      unfold dualMbDst
      rw [ite_eq_left (by rw [hph_t]; decide), ite_eq_left h8_10, hnD_t, hst_t, hpad_t]
    rw [hpD_eq, hmD_mb]
    have hd1_hi : EpochSlotInv c U V w hiFr pDst (dualMbDst base s.mem)
        (pagedSlotIo 1 pgH) 0 false slDst1 s1.mem :=
      hd1.at_exact_frontier (fr₂ := hiFr)
        (by dsimp only [hiFr]; clear *- hpD_rng hibHi_ge; omega)
        (by dsimp only [slDst1]; rw [hcap_d]; unfold dualMbDst
            rw [ite_eq_left h8_10]
            by_cases hd0 : nDst = 0
            · rw [ite_eq_left hd0, ite_eq_left hd0]; dsimp only [hdrSmallMeta1, hiFr]
              clear *- hibHi_ge; omega
            · rw [ite_eq_right hd0, ite_eq_right hd0]; dsimp only [hiFr]
              rw [← hmDst_eq, hibHi_eq, ite_eq_right hd0]
              dsimp only [pad, mDst]; split_ifs <;> (clear *- hmD_pad; omega))
        (by dsimp only [pagedSlotIo, pgH, dualPgHost, hostPageLayout, epochPageArenaLayout]
            exact le_rfl)
    have hraw_d1 := hd1_hi; unfold EpochSlotInv at hraw_d1
    have hio_t : (pagedSlotIo 1 pgH).StateInv (s1.mem (dualMbDst base s.mem + 1)) 0
        s_tick.mem := by
      unfold SlotIoLayout.StateInv pagedSlotIo SlotIoLayout.side
      simp only [ne_eq, one_ne_zero, not_false_eq_true, decide_true, ↓reduceIte]
      rw [hu_t]
      exact ⟨hu_s3_eq ▸ hu3_v, hu3_st ▸ hio_d1.2.1, hu3_st ▸ hio_d1.2.2.1,
        hu3_st ▸ hio_d1.2.2.2.1, hu3_st ▸ hio_d1.2.2.2.2.1, fun _ => trivial, hu3_lt4⟩
    have hp_out_d : ∀ a, pDst ≤ a → a < pDst + 64 → s_tick.mem a = s1.mem a :=
      fun a hlo hhi =>
        (hm_ge48_s3 a (by clear *- hlo hpD_rng; omega)).trans
          (hbu_out a (fun ha => by
            have := hown_pg_ge a ha; clear *- hhi hpD_rng this; omega))
    have hm_out_d : ∀ a, slotOwnsNonPageMeta c w (dualMbDst base s.mem) slDst1.nCap a →
        s_tick.mem a = s1.mem a := fun a ha => by
      have ha_d : slotOwnsNonPageMeta c w (dualMbDst base s.mem) nDst a := by
        dsimp only [slDst1] at ha; rwa [hcap_d] at ha
      have ha48 : base + 48 ≤ a ∧ a < ibHi := by
        unfold slotOwnsNonPageMeta dualMbDst at ha_d
        rw [ite_eq_left h8_10] at ha_d
        by_cases hd0 : nDst = 0
        · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte, ne_eq,
            not_true_eq_false, false_and, or_false] at ha_d
          dsimp only [hdrSmallMeta1] at ha_d; clear *- ha_d hibHi_ge; exact ⟨by omega, by omega⟩
        · have hth_d : whpThreshold c ≤ nDst := (hsched.nDst_bounds.resolve_left hd0).1
          have hod_d := (epochMeta_offsets_le (c := c) (w := w) hth_d).2.2.2
          have h32 : 32 ≤ offPageDir c w nDst :=
            (epochMeta_offsets_le (w := w) hth_d).1.trans
              ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
                (epochMeta_offsets_le (w := w) hth_d).2.2.1)
          rw [← hmDst_eq] at hod_d
          simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte] at ha_d
          rw [hibHi_eq, ite_eq_right hd0]
          dsimp only [pad, mDst, nDst] at h32 hod_d hmD_pad ha_d ⊢
          rcases ha_d with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
            (split_ifs at g1 g2 <;>
              (clear *- g1 g2 hod_d hmD_pad h32; exact ⟨by omega, by omega⟩))
      exact (hm_ge48_s3 a ha48.1).trans (hbu_out a (fun hpg => by
        rcases hpg with hm | hi
        · exact (hdisj_pg a hm).2.2.2 ha_d
        · exact absurd hi.1 (Nat.not_le_of_gt ha48.2)))
    refine hd1_hi.transfer_io (io₂ := pagedSlotIo 1 pgH)
      (show (pagedSlotIo 1 pgH).Valid w hiFr from hv_hi) rfl
      ⟨fun h0 => by rw [ite_eq_left h0] at hraw_d1; exact hraw_d1.2.2.1.qBits_eq,
       fun h0 => by rw [ite_eq_right h0] at hraw_d1; exact hraw_d1.1.qBits_le⟩
      rfl
      ⟨fun h0 => by rw [ite_eq_left h0] at hraw_d1; exact hraw_d1.2.2.2.1.congr hp_out_d,
       fun h0 => by
        rw [ite_eq_right h0] at hraw_d1
        exact hraw_d1.2.1.1.congr fun a hlo hhi =>
          hp_out_d a hlo (by dsimp only at hlo hhi; clear *- hlo hhi; omega)⟩
      (fun a hlo hhi => by
        by_cases h0 : slDst1.nCap = 0
        · rw [ite_eq_left h0] at hraw_d1
          exact fun hia => hraw_d1.2.2.2.2.1 a hlo hhi (Or.inr (Or.inr hia))
        · rw [ite_eq_right h0] at hraw_d1; exact hraw_d1.1.disj_pBase_io a hlo hhi)
      (fun a ha => by
        unfold slotOwnsNonPageMeta at ha
        by_cases h0 : slDst1.nCap = 0
        · rw [ite_eq_left h0] at hraw_d1 ha
          rcases ha with ⟨g1, g2⟩ | ⟨hne, _⟩
          · exact hraw_d1.2.2.1.disjoint_hdr a (by dsimp only; clear *- g1 g2; omega)
          · exact absurd h0 hne
        · rw [ite_eq_right h0] at hraw_d1 ha
          exact hraw_d1.1.disj_fast_io a (ha.imp id And.right))
      hm_out_d hio_t
      (fun p _ => by
        unfold slotIoPairAt pagedSlotIo SlotIoLayout.side
        simp only [ne_eq, one_ne_zero, not_false_eq_true, decide_true, ↓reduceIte]
        have hv1 : PageUnpermState.virtAt (extractPageUnperm pgH s_tick.mem)
            (arenaPairAt pgH s_tick.mem) true p =
          PageUnpermState.virtAt ((extractPageUnperm pgH s1.mem).beginUnperm)
            (arenaPairAt pgH s1.mem) true p := by
          rw [hu_t, har_t]; exact congrArg (fun u => PageUnpermState.virtAt u _ true p) hu_s3_eq
        exact hv1.trans (congrArg (arenaPairAt pgH s1.mem) (hu3_tp true p)))
  refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
  · rw [hnS_t, hph_t, ite_eq_right (by decide : 9 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
  · rw [hph_t, ite_eq_right (by decide : ¬(9 < 2)), ite_eq_right (by decide : 9 ≠ 2),
      ite_eq_left (by decide : 9 ≤ 10), hibH_t, hqH_t, hfr_tick]
    refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
    exact
      { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
        wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, hwf_tick.2⟩
        base_fr := by dsimp only [hiFr]; clear *- hibHi_ge; omega
        hdr := rootStaticHeader_congr hhdr fun off hoff =>
          hout_hdr off (by dsimp only [hdrUnpermDone]; clear *- hoff; omega)
            (by dsimp only [hdrRem]; clear *- hoff; omega)
            (by dsimp only [hdrPhase]; clear *- hoff; omega)
            (by clear *- hoff; omega)
        live_eq := (hout_hdr hdrLive (by decide) (by decide) (by decide)
          (by decide)).trans hlive_eq
        live_le := hlive_le
        ph_le := by dsimp only; rw [hph_t]; decide
        stg_le := by dsimp only; rw [hst_t]; exact hstg_le
        mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
        cache_src := by
          dsimp only; rw [hnS_t]
          exact hostCacheValid_congr_mem hcache_s fun k hk => by
            rw [Nat.add_assoc]
            exact hout_hdr (hdrSrcOd + k)
              (by dsimp only [hdrSrcOd, hdrUnpermDone]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrRem]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd]; clear *- hk; omega)
        nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
        sched := by
          dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
          refine
            { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
              nDst_zero := fun hz => by
                dsimp only at hz ⊢
                obtain ⟨h1', h2', _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                rw [hnS_t, hst_t, hph_t]
                exact ⟨h1', h2', by decide, by decide, by decide⟩
              stg_one := fun hs_o => by
                dsimp only at hs_o ⊢; rw [hnD_t, hph_t]
                exact ⟨(hsched.stg_one (hst_t.symm.trans hs_o)).1, by decide, by decide⟩
              post_trig := by dsimp only [L']; rw [hnS_t]; exact hsched.post_trig
              trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t]; exact hsched.trig_cap
              drift_hi := by
                dsimp only [L']; have hd := hsched.drift_hi
                simp only [↓reduceIte] at hd ⊢; exact hd
              drift_lo := by
                dsimp only [L']; have hd := hsched.drift_lo
                simp only [↓reduceIte] at hd ⊢; exact hd
              ibLo_eq := by
                dsimp only; rw [hibL_t, hph_t, hmS_t, hmD_t]
                simpa only [hp8, Nat.reduceLT, ↓reduceIte] using hsched.ibLo_eq
              qLo_eq := by
                dsimp only; rw [hqL_t, hph_t, hnS_t, hnD_t]
                simpa only [hp8, Nat.reduceLT, ↓reduceIte] using hsched.qLo_eq
              ph1 := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
              ge2 := fun _ => by
                dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                    rw [Nat.add_assoc]
                    exact hout_hdr (hdrDstOd + k)
                      (by dsimp only [hdrDstOd, hdrUnpermDone]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrRem]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd]; clear *- hk; omega)
                · obtain ⟨hl, he, hp⟩ := hd_logs hd
                  exact ⟨(hout_hdr hdrLogN (by decide) (by decide) (by decide)
                      (by decide)).trans hl,
                    (hout_hdr hdrEll (by decide) (by decide) (by decide)
                      (by decide)).trans he,
                    (hout_hdr hdrPgB (by decide) (by decide) (by decide)
                      (by decide)).trans hp⟩
              ph2 := fun hp2 => absurd (hph_t.symm.trans hp2) (by decide)
              ph3_10 := fun _ => by
                dsimp only [hiFr]; rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
              ph11 := fun hp11 => absurd (hph_t.symm.trans hp11) (by decide)
              budget := by
                dsimp only [L']
                rw [hnS_t, hpgH_t, hst_t, hph_t, hnD_t, hmD_t, hrem_t]
                unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                simp only [hp8, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
                  ↓reduceIte] at hb_tot ⊢
                have h2t := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                have hpgH_eq_b : pgH.pgB = pageSizeWhp nHost := rfl
                have hpg_div : pgH.pgB / 8 ≤
                    max 32 (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 4) / 8 := by
                  rw [hpgH_eq_b]; exact Nat.div_le_div_right hpgB_ref
                dsimp only [uTicks]
                rw [hrem1] at hb_tot
                generalize max (whpThreshold c) nSrc = nRef at hb_tot h2t hpg_div ⊢
                refine ⟨by clear *- h2t; omega, ?_, ?_⟩ <;>
                  (clear *- hb_tot h2t hpg_div; omega) }
        pad_fits := by
          dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 9 ≠ 0)]
          simpa only [hp8, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
        ph1_inv := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
        ph3_inv := fun hp3 => absurd (hph_t.symm.trans hp3) (by decide)
        ph4_inv := fun hp4 => absurd (hph_t.symm.trans hp4) (by decide)
        pDst_pre := fun ⟨_, hp5⟩ => absurd (hph_t ▸ hp5) (by decide)
        ph5_inv := fun hp5 => absurd (hph_t.symm.trans hp5) (by decide)
        ph6_inv := fun hp6 => absurd (hph_t.symm.trans hp6) (by decide)
        ph7_inv := fun hp7 => absurd (hph_t.symm.trans hp7) (by decide)
        ph8_inv := fun hp8' => absurd (hph_t.symm.trans hp8') (by decide)
        ph9_inv := fun _ => by
          dsimp only [L']; rw [hpgH_t, hrem_t, hnS_t, hud_t, hu_t]
          refine ⟨by dsimp only [uTicks]; clear *-; omega, le_rfl, by decide, fun _ =>
            ⟨hu3_pos, hu3_lt4, le_rfl, ?_⟩⟩
          have hrk := unpermRank_le_of_inv (hu_s3_eq ▸ hu3_v : u3.InvWithSlack 0)
          dsimp only [u3] at hrk ⊢
          rw [hu3_st, hvl1_t, hio_s1.2.1] at hrk
          have hrk' : (extractPageUnperm pgH s3.mem).unpermRank ≤
              4 * max (whpThreshold c) nSrc + 66 * pgH.pgB + 512 := by
            dsimp only [nLive] at hrk hnL_ref
            generalize max (whpThreshold c) nSrc = nRef at hnL_ref ⊢
            clear *- hrk hnL_ref; omega
          have hz := unperm_rank_reaches_zero hrk'
          unfold calcUnpermTicks at hz
          dsimp only [uTicks]; clear *- hz; omega
        ph10_inv := fun hp10 => absurd (hph_t.symm.trans hp10) (by decide)
        sl_le7 := fun hp7 => absurd (hph_t ▸ hp7) (by decide)
        sl_67 := fun h67 => by
          dsimp only at h67; rcases h67 with h6 | h7 <;> exact absurd (hph_t.symm.trans ‹_›)
            (by decide)
        sl_8 := fun hp8' => absurd (hph_t.symm.trans hp8') (by decide)
        sl_ge9 := fun _ => by
          dsimp only [L', slDst1]; rw [hnD_t, hst_t, hph_t, hnS_t, hpad_t, hibL_t, hqL_t,
            hibH_t, hqH_t, hud_t]
          have hio_eq9 : activeDstIo c w vB base stg 9 nSrc nDst pad ibLo qLo ibHi qHi nLive 0 =
              pagedSlotIo 1 pgH := rfl
          rw [hio_eq9]; simp only [Bool.false_eq_true, false_and, ↓reduceIte]
          refine ⟨hcap_d, hdict_dst1, hd_hi, fun hd_pos => ?_⟩
          have hev_sum : (L.slotDst.evs ++ ex1).length =
              L.slotDst.evs.length + (liveDom L.slotSrc.s_abs).card := by
            rw [show (L.slotDst.evs ++ ex1).length = slDst1.evs.length from rfl,
              ← hsum1, hcd1_zero, Nat.add_zero]
          rw [hev_sum]
          have hd_old := hevs_d hd_pos
          simp only [↓reduceIte] at hd_old; clear *- hd_old; omega }

/-- Phase `8` (`migrate`) background tick specification. -/
theorem tickPhase8_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp8 : s.mem (base + hdrPhase) = 8) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf; have hb_fr := h.base_fr
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hstg_le := h.stg_le; have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src
  have hnSrc_b := h.nSrc_bounds; have hpad_fits := h.pad_fits
  obtain ⟨hth_h, _, hpad_w, hmb_ib, hctx0, _, _, hv_fr, _⟩ :=
    dualPgHost_eval_valid h (by clear *- hp8; omega) (by clear *- hp8; omega)
  have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) h
    (by clear *- hp8; omega) (by clear *- hp8; omega)
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp8; omega)] at hsched
  obtain ⟨hfr_hi_lo, hfr_hi_hi⟩ := hsched.ph3_10 ⟨by clear *- hp8; omega, by clear *- hp8; omega⟩
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hd_logs, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp8; omega)
  obtain ⟨_, hb_tot, _⟩ := hsched.budget
  obtain ⟨_, hrem_le, hcard_rem⟩ := h.ph8_inv hp8
  obtain ⟨hcap_s, hcap_d, hdj, hdict_or, _, hsl_s, hsl_d, hevs_s, hevs_d⟩ := h.sl_8 hp8
  obtain ⟨_, hvb_w, _, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits h
  obtain ⟨_, hdst_safe⟩ := dualCoreInv_cap_safe h
  rw [ite_eq_right (by clear *- hp8; omega)] at hdst_safe
  have hw_pos : 0 < w := by clear *- hw11; omega
  have hth_U : whpThreshold c ≤ U := hth_h.1.trans hth_h.2
  have hth_hdr : s.mem (base + hdrThresh) = whpThreshold c := by
    have ht := hhdr.2.2.2.2.2.1
    simpa only [hth_U, ↓reduceIte] using ht
  set nLive := (Dictionary.dom s_dict).card
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qLo := s.mem (base + hdrQLo)
  set qHi := s.mem (base + hdrQHi)
  set rem := s.mem (base + hdrRem)
  set vB := valBits V
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  set nHost := dualNHost base s.mem
  set mbHost := dualMbHost base s.mem
  set pgH := dualPgHost c V w base nLive s.mem
  set pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
  set pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
  have hh_ofCtx : PageArenaLayout.ofCtx pgH.toCtx = pgH := PageArenaLayout.ofCtx_toCtx pgH
  have h8_10 : s.mem (base + hdrPhase) < 10 := by clear *- hp8; omega
  have hpS_eq0 : dualPSrc base s.mem = pSrc := rfl
  have hpD_eq0 : dualPDst base s.mem = pDst := by
    unfold dualPDst; rw [ite_eq_left h8_10]
  rw [hpS_eq0] at hsl_s; rw [hpD_eq0] at hsl_d
  have hmS_pad : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
  have hmD_pad : mDst ≤ pad := by rw [hpad_eq]; exact le_max_right _ _
  have hibHi_ge : base + 196 ≤ ibHi := by rw [hibHi_eq]; split_ifs <;> (clear *-; omega)
  -- Disjointness between `(pSrc, mbSrc)` and `(pDst, mbDst)` for `migrateBatchProg_spec`
  have hp_disj : pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc := by
    dsimp only [pSrc, pDst, hdrPBase0, hdrPBase1]
    split_ifs <;> [exact Or.inl (by clear *-; omega); exact Or.inr (by clear *-; omega)]
  have hpm_s : pDst + 64 ≤ dualMbSrc base s.mem ∨
      dualMbSrc base s.mem +
        (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ pDst := by
    rw [hcap_s]; unfold dualMbSrc dualCapSrc
    dsimp only [pDst, hdrPBase0, hdrPBase1, hdrSmallMeta0]
    by_cases hst0 : stg = 0
    · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
      split_ifs <;> [exact Or.inr (by clear *-; omega); exact Or.inl (by clear *-; omega)]
    · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
      exact Or.inl (by clear *-; omega)
  have hpm_d : pSrc + 64 ≤ dualMbDst base s.mem ∨
      dualMbDst base s.mem +
        (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ pSrc := by
    rw [hcap_d]; unfold dualMbDst; rw [ite_eq_left h8_10]
    dsimp only [pSrc, hdrPBase0, hdrPBase1, hdrSmallMeta1]
    by_cases hd0 : nDst = 0
    · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte]
      split_ifs <;> exact Or.inr (by clear *-; omega)
    · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte]
      split_ifs <;> exact Or.inl (by clear *-; omega)
  have hmm_disj :
      dualMbSrc base s.mem +
        (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
          dualMbDst base s.mem ∨
      dualMbDst base s.mem +
        (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
          dualMbSrc base s.mem := by
    rw [hcap_s, hcap_d]; unfold dualMbSrc dualMbDst dualCapSrc
    rw [ite_eq_left h8_10]
    dsimp only [hdrSmallMeta0, hdrSmallMeta1]
    by_cases hd0 : nDst = 0
    · obtain ⟨hs_pos, hst0, _⟩ := hsched.nDst_zero hd0
      dsimp only [nDst, stg, nSrc] at hd0 ⊢
      simp only [hd0, hst0, hs_pos.ne', ↓reduceIte]
      exact Or.inr (by clear *-; omega)
    · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte]
      by_cases hst0 : stg = 0
      · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
        by_cases hs0 : nSrc = 0
        · simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, hs0, ↓reduceIte]
          exact Or.inl (by clear *-; omega)
        · have hth_s : whpThreshold c ≤ nSrc := (hnSrc_b.resolve_left hs0).1
          have hod_s : offPageDir c w nSrc ≤ pad :=
            (epochMeta_offsets_le hth_s).2.2.2.trans (hmSrc_eq.symm.le.trans hmS_pad)
          simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, hs0, ↓reduceIte]
          exact Or.inl (by clear *- hod_s; omega)
      · have hth_d : whpThreshold c ≤ nDst := (hsched.nDst_bounds.resolve_left hd0).1
        have hod_d : offPageDir c w nDst ≤ pad :=
          (epochMeta_offsets_le hth_d).2.2.2.trans (hmDst_eq.symm.le.trans hmD_pad)
        simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
        exact Or.inr (by clear *- hod_d; omega)
  have hsum_card : (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card = nLive := by
    rw [← liveDom_orOpt_card hdj, ← dom_toDictState_card, hdict_or]
  have hcap_d_m : L.slotDst.nCap ≠ 0 →
      (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card ≤ L.slotDst.nCap :=
    fun hne => by
      have hd_nz : nDst ≠ 0 := hcap_d ▸ hne
      unfold EpochCapSafe at hdst_safe; rw [ite_eq_right hd_nz] at hdst_safe
      rw [hsum_card, hcap_d]; exact hdst_safe.2.2.2
  have hcap_pg_m :
      (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card ≤ pgH.nCap := by
    rw [hsum_card]; exact le_rfl
  obtain ⟨hsafe_mb, hfr_s1, s_src1, s_dst1, ex1, hcd1, hsum1, hdj1, hor1, hs1, hd1, hout_s1,
    hmc_mb⟩ := migrateBatchProg_spec hsl_s hsl_d hdj hp_disj hpm_s hpm_d hmm_disj
    hcap_d_m hcap_pg_m itemBatchWhp
  set mb := migrateBatchProg (((pSrc, pDst), 0), itemBatchWhp)
  obtain ⟨s1, hs1_def⟩ : ∃ s1, (Memory.spec 0).clientState s mb = s1 := ⟨_, rfl⟩
  rw [hs1_def] at hfr_s1 hs1 hd1 hout_s1
  set slSrc1 : SlotLatent c U V := ⟨L.slotSrc.nCap, s_src1, L.slotSrc.seeds, L.slotSrc.evs⟩
  set slDst1 : SlotLatent c U V := ⟨L.slotDst.nCap, s_dst1, L.slotDst.seeds, L.slotDst.evs ++ ex1⟩
  have hmb_ge192 : base + 192 ≤ pgH.metaBase := by
    change base + 192 ≤ mbHost; dsimp only [mbHost]; unfold dualMbHost
    split_ifs <;> (clear *-; omega)
  have hs1_no_s : ∀ addr, (addr < base + 48 ∨ (base + 64 ≤ addr ∧ addr < base + 192)) →
      ¬slotOwnsAddr c w (dualMbSrc base s.mem) L.slotSrc.nCap (pagedSlotIo 0 pgH) addr := by
    intro addr hrng hown
    have hb := slotOwnsAddr_bounds (pBase := pSrc)
      (fun h0 => by
        rw [hcap_s] at h0; unfold dualMbSrc dualCapSrc at *
        by_cases hst0 : stg = 0
        · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at h0 ⊢
          rw [ite_eq_left h0]; exact Or.inl rfl
        · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at h0
          exact absurd h0 (fun hd0 => hst0 (hsched.nDst_zero hd0).2.1))
      (fun hne => by
        rw [hcap_s] at hne; unfold dualMbSrc dualCapSrc at *
        by_cases hst0 : stg = 0
        · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at hne ⊢
          rw [ite_eq_right hne]; exact Or.inl rfl
        · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
          exact Or.inr rfl)
      (fun _ => ⟨hmb_ge192, by change base + 192 ≤ ibHi; clear *- hibHi_ge; omega⟩)
      (fun h0 => absurd h0 Nat.one_ne_zero)
      (fun h0 => absurd h0 Nat.one_ne_zero) addr hown
    rcases hrng with hlt48 | h64
    · exact absurd (hb.2.1 hlt48).2.1 Nat.one_ne_zero
    · exact hb.2.2 h64
  have hs1_no_d : ∀ addr, (addr < base + 48 ∨ (base + 64 ≤ addr ∧ addr < base + 192)) →
      ¬slotOwnsAddr c w (dualMbDst base s.mem) L.slotDst.nCap (pagedSlotIo 1 pgH) addr := by
    intro addr hrng hown
    have hb := slotOwnsAddr_bounds (pBase := pDst)
      (fun h0 => by
        rw [hcap_d] at h0; unfold dualMbDst; rw [ite_eq_left h8_10,
          ite_eq_left h0]; exact Or.inr rfl)
      (fun hne => by
        rw [hcap_d] at hne; unfold dualMbDst
        rw [ite_eq_left h8_10, ite_eq_right hne]
        split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl])
      (fun _ => ⟨hmb_ge192, by change base + 192 ≤ ibHi; clear *- hibHi_ge; omega⟩)
      (fun h0 => absurd h0 Nat.one_ne_zero)
      (fun h0 => absurd h0 Nat.one_ne_zero) addr hown
    rcases hrng with hlt48 | h64
    · exact absurd (hb.2.1 hlt48).2.1 Nat.one_ne_zero
    · exact hb.2.2 h64
  have hs1_hdr48 : ∀ off < 48, s1.mem (base + off) = s.mem (base + off) := fun off h48 =>
    hout_s1 (base + off) (hs1_no_s _ (Or.inl (by clear *- h48; omega)))
      (hs1_no_d _ (Or.inl (by clear *- h48; omega)))
  have hs1_lt_b : ∀ addr < base, s1.mem addr = s.mem addr := fun addr hlt_b =>
    hout_s1 addr (hs1_no_s _ (Or.inl (by clear *- hlt_b; omega)))
      (hs1_no_d _ (Or.inl (by clear *- hlt_b; omega)))
  have hctx0_s1 : (Memory.spec 0).clientResult s1 (loadHostCtxProg (base, 0)) = pgH.toCtx := by
    rw [← hctx0, (loadHostCtxProg_eval base 0 s1).2.1, (loadHostCtxProg_eval base 0 s).2.1]
    simp only [↓reduceIte]
    have h_od : ∀ k ≤ 4,
        s1.mem (base + (if s.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) =
          s.mem (base + (if s.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) :=
      fun k hk => by
        rw [Nat.add_assoc]
        exact hs1_hdr48 _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> (clear *- hk; omega))
    rw [hs1_hdr48 hdrStage (by decide), hs1_hdr48 hdrNDst (by decide),
      hs1_hdr48 hdrPad (by decide), hs1_hdr48 hdrW (by decide),
      hs1_hdr48 hdrItemHi (by decide), hs1_hdr48 hdrQHi (by decide),
      hs1_hdr48 hdrValBits (by decide), hs1_hdr48 hdrLive (by decide),
      show s1.mem (base + if s.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) =
        s.mem (base + if s.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) by
        simpa only [Nat.add_zero] using h_od 0 (by decide),
      h_od 1 (by decide), h_od 2 (by decide), h_od 3 (by decide), h_od 4 (by decide)]
  have hpre_mig : TickMigratePre w base s := by
    refine ⟨hw11, hb_fr, hpad_w, hsafe_mb, fun _ => ?_⟩
    change base + 192 ≤ ((Memory.spec 0).clientState s mb).frontier ∧
      Fits w (base + 192 + ((Memory.spec 0).clientState s mb).mem (base + hdrPad)) ∧
      (PageArenaLayout.ofCtx
        ((Memory.spec 0).clientResult ((Memory.spec 0).clientState s mb)
          (loadHostCtxProg (base, 0)))).Valid
        w ((Memory.spec 0).clientState s mb).frontier
    rw [hs1_def, hfr_s1, hs1_hdr48 hdrPad (by decide), hctx0_s1, hh_ofCtx]
    exact ⟨hb_fr, hpad_w, hv_fr⟩
  have hpre : BgTickPre w (base, s.frontier) s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb_fr; omega, ?_⟩
    simp only [hp8, Nat.reduceEqDiff, ↓reduceIte]
    exact hpre_mig
  have hwf_tick : Memory.WellFormed w
      ((Memory.spec 0).clientState s (bgTickProg (base, s.frontier))) :=
    wf_step hwf (validHistory_bgTickProg hwf hpre)
  have hbgev := bgTickProg_eval base s.frontier s
  simp only [hp8, Nat.reduceEqDiff, ↓reduceIte] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  have htmev := tickMigrateProg_eval base s
  change _ ∧ _ at htmev
  rw [hs1_def, hctx0_s1, hh_ofCtx, hth_hdr] at htmev
  clear hs1_def
  obtain ⟨hst_tm, hmc_tm⟩ := htmev
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    have hle1 : s.frontier ≤ ibHi + pairStreamWords (nLive + 1) qHi vB w := hfr_hi_hi
    have hstep := pairStreamWords_succ_le_add_two (n := nLive) (qb := qHi) (vb := vB) (w := w)
      hw_pos (by clear *- hqHi_w hvb_w; omega)
    dsimp only [hiFr, bulkBatchWhp]; clear *- hle1 hstep; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive := by
    have hib_pad := (dualCoreInv_ib_fits h).2.2.2.2.2.1
    rw [ite_eq_right (by clear *- hp8; omega)] at hib_pad
    exact hfr_hi_hi.trans hib_pad
  have hd_sm_bound : L.slotDst.nCap = 0 →
      (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card ≤ 2 * whpThreshold c :=
    fun h0 => by
      have hd0 : nDst = 0 := hcap_d ▸ h0
      unfold EpochCapSafe at hdst_safe; rw [ite_eq_left hd0] at hdst_safe
      rw [hsum_card]; exact hdst_safe.1.le
  obtain ⟨s3, hs3_def⟩ :
      ∃ s3, (Memory.spec 0).clientState s1 (pageBeginUnpermBoundedProg pgH.toCtx) = s3 := ⟨_, rfl⟩
  rw [hs3_def] at hst_tm
  have hbu_frm := pageBeginUnpermBoundedProg_frame pgH
  have hfr_s3 : s3.frontier = s.frontier := (hs3_def ▸ hbu_frm.frontier_eq s1).trans hfr_s1
  have hmc_bu : memoryCost (pageBeginUnpermBoundedProg pgH.toCtx) s1 ≤ 10 := hbu_frm.cost_le s1
  have hown_pg_ge : ∀ a, pgH.OwnsAddr a → base + 210 ≤ a := fun a ha => by
    rcases ha with hm | hi
    · exact (hdisj_pg a hm).1
    · have hi1 : ibHi ≤ a := hi.1
      have h32 := (epochMeta_offsets_le (w := w) hth_h.1).1.trans
        ((epochMeta_offsets_le (w := w) hth_h.1).2.1.trans
          ((epochMeta_offsets_le (w := w) hth_h.1).2.2.1.trans
            (epochMeta_offsets_le (w := w) hth_h.1).2.2.2))
      have hmb_eq : pgH.metaBase = mbHost := rfl
      rw [hmb_eq] at hmb_ge192
      clear *- hi1 h32 hmb_ib hmb_ge192; omega
  obtain ⟨s_tick, hs_tick_def⟩ :
      ∃ s_tick, (Memory.spec 0).clientState s (bgTickProg (base, s.frontier)) = s_tick := ⟨_, rfl⟩
  rw [hs_tick_def] at hwf_tick hst_bg ⊢
  clear hs_tick_def
  have hfr_tick : s_tick.frontier = s.frontier := by
    rw [hst_bg, hst_tm]
    split_ifs <;> [exact hfr_s1; exact hfr_s3]
  have hlt_b_tick : ∀ addr < base, s_tick.mem addr = s.mem addr := fun addr hlt_b => by
    rw [hst_bg, hst_tm]
    split_ifs
    · dsimp only
      exact (Function.update_of_ne (by dsimp only [hdrRem]; clear *- hlt_b; omega) _ _).trans
        (hs1_lt_b addr hlt_b)
    · dsimp only
      iterate 3 rw [Function.update_of_ne
        (by dsimp only [hdrUnpermDone, hdrRem, hdrPhase]; clear *- hlt_b; omega)]
      rw [← hs3_def]
      exact (hbu_frm.mem_outside s1 addr (fun ha => by
        have := hown_pg_ge addr ha; clear *- hlt_b this; omega)).trans (hs1_lt_b addr hlt_b)
  refine ⟨hpre, hfr_tick, hwf_tick, hlt_b_tick, ?_⟩
  rw [ite_eq_left (by clear *- hp8; omega)]
  refine ⟨hres_bg, ?_⟩
  by_cases h1 : 1 < rem
  · -- `8 → 8`: `1 < rem`, decrementing `hdrRem := rem - 1`
    set L' : DualLatent c U V :=
      { L with slotSrc := slSrc1, slotDst := slDst1, elapsed := L.elapsed + 1 }
    have hpres_L' : PreservesEpochSeeds (s.mem (base + hdrPhase) = 8)
        (s.mem (base + hdrPhase) = 9 ∧ s_tick.mem (base + hdrPhase) = 4) L L' :=
      ⟨⟨fun _ => ⟨rfl, HEq.rfl, rfl⟩, fun ⟨h9, _⟩ => by rw [hp8] at h9; cases h9⟩,
       Or.inr ⟨rfl, HEq.rfl, ⟨ex1, rfl⟩, fun hne => absurd hp8 hne⟩⟩
    refine ⟨L', hpres_L', ?_, fun hg_s hgc_imp => ?_⟩
    · have hm_eq : s_tick.mem = Function.update s1.mem (base + hdrRem) (rem - 1) := by
        rw [hst_bg, hst_tm, ite_eq_left h1]
      have hout_hdr : ∀ off, off ≠ hdrRem → off < 48 →
          s_tick.mem (base + off) = s.mem (base + off) := fun off hne h48 => by
        rw [hm_eq, Function.update_of_ne (base_add_ne hne)]; exact hs1_hdr48 off h48
      have hph_t : s_tick.mem (base + hdrPhase) = 8 :=
        (hout_hdr hdrPhase (by decide) (by decide)).trans hp8
      have hrem_t : s_tick.mem (base + hdrRem) = rem - 1 := by
        rw [hm_eq]; exact Function.update_self ..
      have hst_t : s_tick.mem (base + hdrStage) = stg := hout_hdr hdrStage (by decide) (by decide)
      have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc := hout_hdr hdrNSrc (by decide) (by decide)
      have hnD_t : s_tick.mem (base + hdrNDst) = nDst := hout_hdr hdrNDst (by decide) (by decide)
      have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc := hout_hdr hdrMSrc (by decide) (by decide)
      have hmD_t : s_tick.mem (base + hdrMDst) = mDst := hout_hdr hdrMDst (by decide) (by decide)
      have hpad_t : s_tick.mem (base + hdrPad) = pad := hout_hdr hdrPad (by decide) (by decide)
      have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
        hout_hdr hdrItemLo (by decide) (by decide)
      have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
        hout_hdr hdrItemHi (by decide) (by decide)
      have hqL_t : s_tick.mem (base + hdrQLo) = qLo := hout_hdr hdrQLo (by decide) (by decide)
      have hqH_t : s_tick.mem (base + hdrQHi) = qHi := hout_hdr hdrQHi (by decide) (by decide)
      have hpgH_t : dualPgHost c V w base nLive s_tick.mem = pgH := by
        dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
        rw [hnD_t, hnS_t, hst_t, hpad_t, hibH_t, hqH_t]
      have hm_ge48 : ∀ a, base + 48 ≤ a → s_tick.mem a = s1.mem a := fun a h48 => by
        rw [hm_eq]; exact Function.update_of_ne (by dsimp only [hdrRem]; clear *- h48; omega) _ _
      have hu_t : extractPageUnperm pgH s_tick.mem = extractPageUnperm pgH s1.mem :=
        extractPageUnperm_congr hw_pos fun a ha =>
          hm_ge48 a (by have := (hdisj_pg a ha).1; clear *- this; omega)
      have hcp_t : (extractPageUnperm pgH s_tick.mem).cleanPhase = 0 := by
        rw [hu_t]; exact cleanPhase_zero_of_paged0 hs1
      have hpS_rng : base + 64 ≤ pSrc ∧ pSrc + 64 ≤ base + 192 := by
        dsimp only [pSrc, hdrPBase0, hdrPBase1]
        split_ifs <;> (clear *-; exact ⟨by omega, by omega⟩)
      have hpD_rng : base + 64 ≤ pDst ∧ pDst + 64 ≤ base + 192 := by
        dsimp only [pDst, hdrPBase0, hdrPBase1]
        split_ifs <;> (clear *-; exact ⟨by omega, by omega⟩)
      have hs_hi : EpochSlotInv c U V w hiFr (dualPSrc base s_tick.mem)
          (dualMbSrc base s_tick.mem) (pagedSlotIo 0 pgH) 0 true slSrc1 s_tick.mem := by
        have hpS_eq : dualPSrc base s_tick.mem = pSrc := by unfold dualPSrc; rw [hst_t]
        have hmS_mb : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
          unfold dualMbSrc; rw [hst_t, hnS_t, hpad_t]
        rw [hpS_eq, hmS_mb]
        exact (hs1.congr_mem
          (fun a hlo _ => hm_ge48 a (by clear *- hlo hpS_rng; omega))
          (fun a ha => hm_ge48 a (by
            rcases slotOwnsNonPageMeta_src_range hcap_s
              (fun hst_nz hd0 => hst_nz (hsched.nDst_zero hd0).2.1) ha with
              ⟨hlo, _⟩ | hlo <;> (clear *- hlo; omega)))
          (fun a ha => hm_ge48 a (by
            have := hown_pg_ge a
              (by simpa only [SlotIoLayout.OwnsAddr, pagedSlotIo, one_ne_zero, ↓reduceIte] using ha)
            clear *- this; omega))).at_exact_frontier (fr₂ := hiFr)
          (by dsimp only [hiFr]; clear *- hpS_rng hibHi_ge; omega)
          (by dsimp only [slSrc1]; rw [hcap_s]; unfold dualMbSrc dualCapSrc
              by_cases hst0 : stg = 0
              · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
                rw [← hmSrc_eq]
                by_cases hs0 : nSrc = 0
                · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only [hdrSmallMeta0, hiFr]
                  clear *- hibHi_ge; omega
                · rw [ite_eq_right hs0, ite_eq_right hs0]; dsimp only [hiFr]; rw [hibHi_eq]
                  dsimp only [pad, mSrc, mDst]; split_ifs <;> (clear *- hmS_pad; omega)
              · have hd_nz : nDst ≠ 0 := fun hd0 => hst0 (hsched.nDst_zero hd0).2.1
                simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
                dsimp only [hiFr]; rw [← hmDst_eq, hibHi_eq]
                simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd_nz, ↓reduceIte]
                dsimp only [pad, mDst]; clear *-; omega)
          (by dsimp only [pagedSlotIo, pgH, dualPgHost, hostPageLayout, epochPageArenaLayout]
              exact le_rfl)
      have h8_10 : s.mem (base + hdrPhase) < 10 := by clear *- hp8; omega
      have hd_hi : EpochSlotInv c U V w hiFr (dualPDst base s_tick.mem)
          (dualMbDst base s_tick.mem) (pagedSlotIo 1 pgH) 0 false slDst1 s_tick.mem := by
        have hpD_eq : dualPDst base s_tick.mem = pDst := by
          unfold dualPDst; rw [ite_eq_left (by rw [hph_t]; decide), hst_t]
        have hmD_mb : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
          unfold dualMbDst
          rw [ite_eq_left (by rw [hph_t]; decide), ite_eq_left h8_10, hnD_t, hst_t, hpad_t]
        rw [hpD_eq, hmD_mb]
        exact (hd1.congr_mem
          (fun a hlo _ => hm_ge48 a (by clear *- hlo hpD_rng; omega))
          (fun a ha => hm_ge48 a (by
            dsimp only [slDst1] at ha; rw [hcap_d] at ha
            unfold slotOwnsNonPageMeta dualMbDst at ha
            rw [ite_eq_left h8_10] at ha
            by_cases hd0 : nDst = 0
            · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte, ne_eq,
                not_true_eq_false, false_and, or_false] at ha
              dsimp only [hdrSmallMeta1] at ha; clear *- ha; omega
            · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte] at ha
              rcases ha with ⟨hlo, _⟩ | ⟨_, hlo, _⟩ <;>
                (split_ifs at hlo <;> (clear *- hlo; omega))))
          (fun a ha => hm_ge48 a (by
            have := hown_pg_ge a
              (by simpa only [SlotIoLayout.OwnsAddr, pagedSlotIo, one_ne_zero, ↓reduceIte] using ha)
            clear *- this; omega))).at_exact_frontier (fr₂ := hiFr)
          (by dsimp only [hiFr]; clear *- hpD_rng hibHi_ge; omega)
          (by dsimp only [slDst1]; rw [hcap_d]; unfold dualMbDst
              rw [ite_eq_left h8_10]
              by_cases hd0 : nDst = 0
              · rw [ite_eq_left hd0, ite_eq_left hd0]; dsimp only [hdrSmallMeta1, hiFr]
                clear *- hibHi_ge; omega
              · rw [ite_eq_right hd0, ite_eq_right hd0]; dsimp only [hiFr]
                rw [← hmDst_eq, hibHi_eq, ite_eq_right hd0]
                dsimp only [pad, mDst]; split_ifs <;> (clear *- hmD_pad; omega))
          (by dsimp only [pagedSlotIo, pgH, dualPgHost, hostPageLayout, epochPageArenaLayout]
              exact le_rfl)
      refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
      · rw [hnS_t, hph_t, ite_eq_right (by decide : 8 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
      · rw [hph_t, ite_eq_right (by decide : ¬(8 < 2)), ite_eq_right (by decide : 8 ≠ 2),
          ite_eq_left (by decide : 8 ≤ 10), hibH_t, hqH_t, hfr_tick]
        refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
        exact
          { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
            wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, hwf_tick.2⟩
            base_fr := by dsimp only [hiFr]; clear *- hibHi_ge; omega
            hdr := rootStaticHeader_congr hhdr fun off hoff =>
              hout_hdr off (by dsimp only [hdrRem]; clear *- hoff; omega) (by clear *- hoff; omega)
            live_eq := (hout_hdr hdrLive (by decide) (by decide)).trans hlive_eq
            live_le := hlive_le
            ph_le := by dsimp only; rw [hph_t]; decide
            stg_le := by dsimp only; rw [hst_t]; exact hstg_le
            mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
            cache_src := by
              dsimp only; rw [hnS_t]
              exact hostCacheValid_congr_mem hcache_s fun k hk => by
                rw [Nat.add_assoc]
                exact hout_hdr (hdrSrcOd + k)
                  (by dsimp only [hdrSrcOd, hdrRem]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd]; clear *- hk; omega)
            nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
            sched := by
              dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
              refine
                { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                  nDst_zero := fun hz => by
                    dsimp only at hz ⊢
                    obtain ⟨h1', h2', _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                    rw [hnS_t, hst_t, hph_t]
                    exact ⟨h1', h2', by decide, by decide, by decide⟩
                  stg_one := fun hs_o => by
                    dsimp only at hs_o ⊢; rw [hnD_t, hph_t]
                    exact ⟨(hsched.stg_one (hst_t.symm.trans hs_o)).1, by decide, by decide⟩
                  post_trig := by dsimp only [L']; rw [hnS_t]; exact hsched.post_trig
                  trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                  drift_hi := by
                    dsimp only [L']; have hd := hsched.drift_hi
                    simp only [↓reduceIte] at hd ⊢; exact hd
                  drift_lo := by
                    dsimp only [L']; have hd := hsched.drift_lo
                    simp only [↓reduceIte] at hd ⊢; exact hd
                  ibLo_eq := by
                    dsimp only; rw [hibL_t, hph_t, hmS_t, hmD_t]
                    simpa only [hp8, Nat.reduceLT, ↓reduceIte] using hsched.ibLo_eq
                  qLo_eq := by
                    dsimp only; rw [hqL_t, hph_t, hnS_t, hnD_t]
                    simpa only [hp8, Nat.reduceLT, ↓reduceIte] using hsched.qLo_eq
                  ph1 := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
                  ge2 := fun _ => by
                    dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                    refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                    · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                        rw [Nat.add_assoc]
                        exact hout_hdr (hdrDstOd + k)
                          (by dsimp only [hdrDstOd, hdrRem]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd]; clear *- hk; omega)
                    · obtain ⟨hl, he, hp⟩ := hd_logs hd
                      exact ⟨(hout_hdr hdrLogN (by decide) (by decide)).trans hl,
                        (hout_hdr hdrEll (by decide) (by decide)).trans he,
                        (hout_hdr hdrPgB (by decide) (by decide)).trans hp⟩
                  ph2 := fun hp2 => absurd (hph_t.symm.trans hp2) (by decide)
                  ph3_10 := fun _ => by
                    dsimp only [hiFr]; rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
                  ph11 := fun hp11 => absurd (hph_t.symm.trans hp11) (by decide)
                  budget := by
                    dsimp only [L']
                    rw [hnS_t, hpgH_t, hst_t, hph_t, hnD_t, hmD_t, hrem_t]
                    unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                    simp only [hp8, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
                      ↓reduceIte] at hb_tot ⊢
                    have h2t := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                    generalize max (whpThreshold c) nSrc = nRef at hb_tot h2t ⊢
                    refine ⟨by clear *- h2t; omega, ?_, ?_⟩ <;>
                      (clear *- h1 hb_tot h2t; omega) }
            pad_fits := by
              dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 8 ≠ 0)]
              simpa only [hp8, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
            ph1_inv := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
            ph3_inv := fun hp3 => absurd (hph_t.symm.trans hp3) (by decide)
            ph4_inv := fun hp4 => absurd (hph_t.symm.trans hp4) (by decide)
            pDst_pre := fun ⟨_, hp5⟩ => absurd (hph_t ▸ hp5) (by decide)
            ph5_inv := fun hp5 => absurd (hph_t.symm.trans hp5) (by decide)
            ph6_inv := fun hp6 => absurd (hph_t.symm.trans hp6) (by decide)
            ph7_inv := fun hp7 => absurd (hph_t.symm.trans hp7) (by decide)
            ph8_inv := fun _ => by
              dsimp only; rw [hrem_t, hnS_t]; dsimp only [L', slSrc1]
              rw [hcd1]
              refine ⟨by clear *- h1; omega, by clear *- hrem_le; omega, ?_⟩
              have hmul : (rem - 1) * itemBatchWhp = rem * itemBatchWhp - itemBatchWhp := by
                rw [Nat.sub_mul, Nat.one_mul]
              rw [hmul]; clear *- hcard_rem; omega
            ph9_inv := fun hp9 => absurd (hph_t.symm.trans hp9) (by decide)
            ph10_inv := fun hp10 => absurd (hph_t.symm.trans hp10) (by decide)
            sl_le7 := fun hp7 => absurd (hph_t ▸ hp7) (by decide)
            sl_67 := fun h67 => by
              dsimp only at h67; rcases h67 with h6 | h7 <;> exact absurd (hph_t.symm.trans ‹_›)
                (by decide)
            sl_8 := fun _ => by
              dsimp only [L', slSrc1, slDst1]; rw [hpgH_t, hnD_t]
              have hcap_eq : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
                unfold dualCapSrc; rw [hst_t, hnS_t, hnD_t]
              rw [hcap_eq]
              refine ⟨hcap_s, hcap_d, hdj1, by rw [hor1, hdict_or],
                hcp_t, hs_hi, hd_hi, hevs_s, fun hd_pos => ?_⟩
              · simp only [Bool.false_eq_true, ↓reduceIte]
                rw [show (L.slotDst.evs ++ ex1).length + (liveDom s_src1).card =
                  slDst1.evs.length + (liveDom s_src1).card from rfl, hsum1]
                have hd_old := hevs_d hd_pos
                simp only [↓reduceIte] at hd_old; clear *- hd_old; omega
            sl_ge9 := fun hp9 => absurd (hph_t ▸ hp9) (by decide) }
    · have hgc_d : slDst1.GoodCovers := hgc_imp hp8
      have hc_mb := hmc_mb hd_sm_bound (hg_s hp8) hgc_d
      rw [ite_eq_left h1] at hmc_tm
      dsimp only [mb, pSrc, pDst, stg, itemBatchWhp] at hmc_tm hc_mb ⊢
      clear *- hmc_bg hmc_tm hc_mb; omega
  · -- `8 → 9`: `rem = 1`, source drained (`card = 0`), running `pageBeginUnpermBoundedProg`
    set u3 := extractPageUnperm pgH s3.mem
    set L' : DualLatent c U V :=
      { L with
        slotSrc := slSrc1
        slotDst := slDst1
        elapsed := L.elapsed + 1
        unpermBound := u3.unpermRank }
    have hpres_L' : PreservesEpochSeeds (s.mem (base + hdrPhase) = 8)
        (s.mem (base + hdrPhase) = 9 ∧ s_tick.mem (base + hdrPhase) = 4) L L' :=
      ⟨⟨fun _ => ⟨rfl, HEq.rfl, rfl⟩, fun ⟨h9, _⟩ => by rw [hp8] at h9; cases h9⟩,
       Or.inr ⟨rfl, HEq.rfl, ⟨ex1, rfl⟩, fun hne => absurd hp8 hne⟩⟩
    refine ⟨L', hpres_L', ?_, fun hg_s hgc_imp => ?_⟩
    · exact tickPhase8_finish_spec h hp8 h1 hwf_tick hfr_tick hfr_s1 hs1_hdr48 hown_pg_ge
        hcd1 hsum1 hor1 hs1 hd1 hs3_def (by rw [hst_bg, hst_tm, ite_eq_right h1])
    · have hgc_d : slDst1.GoodCovers := hgc_imp hp8
      have hc_mb := hmc_mb hd_sm_bound (hg_s hp8) hgc_d
      rw [ite_eq_right h1] at hmc_tm
      dsimp only [mb, pSrc, pDst, stg, itemBatchWhp] at hmc_tm hc_mb hmc_bu ⊢
      clear *- hmc_bg hmc_tm hc_mb hmc_bu; omega

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
