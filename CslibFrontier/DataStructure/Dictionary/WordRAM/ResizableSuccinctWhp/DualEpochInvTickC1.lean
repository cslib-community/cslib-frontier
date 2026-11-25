/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvTickB2

/-!
# Background Tick Phase `9` Unpermutation Specification (`DualEpochInvTickC1`)

Proves `EpochSlotInv.slot_pair_bounds` and `tickPhase9_spec` (`tickUnpermProg`, `9 → 9`,
`9 → 4` Stage B, and `9 → 10`) for the 12-phase dual-epoch resizable succinct worst-case WHP
dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main results

* `EpochSlotInv.slot_pair_bounds`: raw quotient and value bounds on any live `EpochSlotInv` slot.
* `tickPhase9_spec`: Phase `9` (`tickUnpermProg`, `9 → 9`, `9 → 4` Stage B, and `9 → 10`).

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

attribute [local irreducible] epochMetaWordsWhp

/-! ## Section 1: Unpermutation & Quotient-Bound Helpers -/

private theorem rank_step_sub_le {a r0 b : ℕ}
    (h1 : a ≤ r0 - itemBatchWhp) (h2 : r0 ≤ b + 64) :
    a ≤ b - (itemBatchWhp - 64) := by
  have hle : r0 - (960 + 64) ≤ (b + 64) - (960 + 64) := Nat.sub_le_sub_right h2 (960 + 64)
  rw [Nat.add_sub_add_right] at hle
  exact h1.trans hle

private theorem runUnpermSteps_add :
    ∀ (a b : ℕ) (u : PageUnpermState),
      (PageUnpermState.runUnpermSteps (a + b) u).1 =
        (PageUnpermState.runUnpermSteps b (PageUnpermState.runUnpermSteps a u).1).1
  | 0, b, u => by rw [Nat.zero_add]; rfl
  | a + 1, b, u => by rw [Nat.succ_add]; exact runUnpermSteps_add a b u.unpermStep.1

private theorem runUnpermSteps_1024_valid {u : PageUnpermState}
    (hi : u.InvWithSlack 24) (hpos : 0 < u.cleanPhase) :
    (PageUnpermState.runUnpermSteps itemBatchWhp u).1.Valid := by
  change (PageUnpermState.runUnpermSteps (512 + 512) u).1.Valid
  rw [runUnpermSteps_add 512 512 u]
  exact (PageUnpermState.runUnpermSteps_spec.{0} 512
    (PageUnpermState.runUnpermSteps_restores_valid hi hpos)).1

private theorem cleanPhase_pos_unpermStep {u : PageUnpermState} (hpos : 0 < u.cleanPhase) :
    0 < u.unpermStep.1.cleanPhase := by
  unfold PageUnpermState.unpermStep
  dsimp only
  split_ifs <;> dsimp only <;> first | decide | exact hpos

private theorem cleanPhase_pos_runUnpermSteps :
    ∀ (k : ℕ) (u : PageUnpermState), 0 < u.cleanPhase →
      0 < (PageUnpermState.runUnpermSteps k u).1.cleanPhase
  | 0, _, hpos => hpos
  | k + 1, u, hpos =>
    cleanPhase_pos_runUnpermSteps k u.unpermStep.1 (cleanPhase_pos_unpermStep hpos)

/-- Every live slot `p < mem (metaBase + 1)` in an `EpochSlotInv` stores a quotient strictly below
`2 ^ (if sl.nCap = 0 then keyBits U else quotBitsWhp U sl.nCap)` and a value strictly below `V`. -/
theorem EpochSlotInv.slot_pair_bounds {c U V w fr pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem)
    {p : ℕ} (hp : p < mem (metaBase + 1)) :
    (slotIoPairAt io mem p).1 <
      2 ^ (if sl.nCap = 0 then keyBits U else quotBitsWhp U sl.nCap) ∧
    (slotIoPairAt io mem p).2 < V := by
  unfold EpochSlotInv at h
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h ⊢
    obtain ⟨_, hv, u, _, hkq⟩ := h.2.2.2.2.2.2.2.2.slot_valid p hp
    have hk0 : keyQuotient 0 u.val = u.val := by simp [keyQuotient]
    have hu_pow : u.val < 2 ^ keyBits U :=
      lt_of_lt_of_le u.isLt (Nat.le_pow_clog (by decide : 1 < 2) U)
    exact ⟨by rw [← hkq, hk0]; exact hu_pow, hv⟩
  · rw [ite_eq_right h0] at h ⊢
    have hv_fl := h.1
    have hbw_kb : bWhp sl.nCap ≤ keyBits U := by
      unfold bWhp keyBits
      exact (Nat.sub_le _ _).trans
        ((Nat.log_mono_right hv_fl.N_le_U).trans (Nat.log_le_clog 2 U))
    have hpow_eq : 2 ^ keyBits U = 2 ^ quotBitsWhp U sl.nCap * 2 ^ bWhp sl.nCap := by
      rw [← Nat.pow_add]; unfold quotBitsWhp; rw [Nat.sub_add_cancel hbw_kb]
    have href_valid :
        (slotIoPairAt io mem p).2 < V ∧
        ∃ u : Fin U, keyQuotient (bWhp sl.nCap) u.val = (slotIoPairAt io mem p).1 := by
      rcases h.2.1.2 with ⟨_, hf⟩ | ⟨_, hfb⟩
      · have sv := (hf.toGen 0).refines.slot_valid p hp
        exact ⟨sv.2.1, let ⟨u, _, hq⟩ := sv.2.2; ⟨u, hq⟩⟩
      · have sv := hfb.refines.slot_valid p hp
        exact ⟨sv.2.1, let ⟨u, _, hq⟩ := sv.2.2; ⟨u, hq⟩⟩
    obtain ⟨hv, u, hkq⟩ := href_valid
    have hu_pow : u.val < 2 ^ quotBitsWhp U sl.nCap * 2 ^ bWhp sl.nCap :=
      hpow_eq ▸ lt_of_lt_of_le u.isLt (Nat.le_pow_clog (by decide : 1 < 2) U)
    have hq_lt : keyQuotient (bWhp sl.nCap) u.val < 2 ^ quotBitsWhp U sl.nCap := by
      unfold keyQuotient
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr hu_pow
    exact ⟨hkq ▸ hq_lt, hv⟩

/-! ## Section 2: Phase `9` (`tickUnpermProg`) Specification -/

/-- Unified postcondition of `optStepUnpermProg` (`if done = 0 then stepUnpermBatchProg else pure`)
from `DualMidInv` at `ph = 9`: restores resting `slack = 0` on `L.slotDst`, preserves all root
headers except `hdrUnpermDone`, and forces `hdrUnpermDone = 1` whenever `rem = 1`. -/
private theorem optStepUnperm_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp9 : s.mem (base + hdrPhase) = 9) :
    let done := s.mem (base + hdrUnpermDone)
    let rem := s.mem (base + hdrRem)
    let nLive := (Dictionary.dom s_dict).card
    let pgH := dualPgHost c V w base nLive s.mem
    let s1 := if done = 0 then (Memory.spec 0).clientState s (stepUnpermBatchProg base) else s
    let done1 := s1.mem (base + hdrUnpermDone)
    (done = 0 → StepUnpermBatchPre w base s) ∧
    s1.frontier = s.frontier ∧
    (done = 0 → memoryCost (stepUnpermBatchProg base) s ≤ 36 + 100 * itemBatchWhp) ∧
    (∀ off < 48, off ≠ hdrUnpermDone → s1.mem (base + off) = s.mem (base + off)) ∧
    (∀ a, a < base → s1.mem a = s.mem a) ∧
    done1 ≤ 1 ∧
    (¬(1 < rem) → done1 = 1) ∧
    (done1 = 0 →
      0 < (extractPageUnperm pgH s1.mem).cleanPhase ∧
      (extractPageUnperm pgH s1.mem).cleanPhase < 4 ∧
      (extractPageUnperm pgH s1.mem).unpermRank ≤ L.unpermBound - (itemBatchWhp - 64)) ∧
    EpochSlotInv c U V w s.frontier (dualPDst base s.mem) (dualMbDst base s.mem)
      (activeDstIo c w (valBits V) base (s.mem (base + hdrStage)) 9
        (s.mem (base + hdrNSrc)) (s.mem (base + hdrNDst)) (s.mem (base + hdrPad))
        (s.mem (base + hdrItemLo)) (s.mem (base + hdrQLo)) (s.mem (base + hdrItemHi))
        (s.mem (base + hdrQHi)) nLive done1)
      0 false L.slotDst s1.mem := by
  dsimp only
  have hw11 := h.hw11; have hw_pos : 0 < w := by clear *- hw11; omega
  have hUw := h.U_lt; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hb192 := h.base_fr; have hhdr := h.hdr
  have hw_eq := hhdr.2.2.1; have hvb_eq := hhdr.2.2.2.2.1
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp9; omega)] at hsched
  obtain ⟨hmDst_eq, hpad_eq, _, _, hibHi_eq, hqHi_eq⟩ := hsched.ge2 (by clear *- hp9; omega)
  obtain ⟨hfr_hi_lo, _⟩ := hsched.ph3_10 ⟨by clear *- hp9; omega, by clear *- hp9; omega⟩
  obtain ⟨_, hvb_w, _, hqHi_w, _, _, _, hfit_hi1⟩ := dualCoreInv_ib_fits h
  obtain ⟨hrem1, _, hud_le, hud0_inv⟩ := h.ph9_inv hp9
  obtain ⟨hcap_d, hdict_d, hsl_d, _⟩ := h.sl_ge9 (by clear *- hp9; omega)
  set done := s.mem (base + hdrUnpermDone)
  set rem := s.mem (base + hdrRem)
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set nLive := (Dictionary.dom s_dict).card
  set pgH := dualPgHost c V w base nLive s.mem
  set pDst := dualPDst base s.mem
  set mbDst := dualMbDst base s.mem
  have hibHi_ge : base + 196 ≤ ibHi := by
    rw [hibHi_eq]; split_ifs <;> omega
  have hfit_pad : Fits w (base + 192 + pad) := by
    dsimp only [Fits] at hfit_hi1 ⊢
    by_cases hdz : nDst = 0
    · have hmD0 : s.mem (base + hdrMDst) = 0 := by
        rw [hmDst_eq, hdz]; unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
      have hp_eq : pad = s.mem (base + hdrMSrc) := by
        rw [hpad_eq, hmD0]; exact max_eq_left (Nat.zero_le _)
      rw [hibHi_eq, ite_eq_left hdz] at hfit_hi1
      clear *- hp_eq hfit_hi1; omega
    · rw [hibHi_eq, ite_eq_right hdz] at hfit_hi1
      clear *- hfit_hi1; omega
  have hpDst_eq : pDst = (if stg = 0 then base + hdrPBase1 else base + hdrPBase0) := by
    unfold pDst dualPDst; rw [hp9, ite_eq_left (by decide : 9 < 10)]
  by_cases hd0 : done = 0
  · simp only [hd0, ↓reduceIte]
    obtain ⟨hu0_pos, _, hu0_rk, hub_le⟩ := hud0_inv hd0
    simp only [↓reduceIte] at hu0_rk
    obtain ⟨hth_h, hnL_host, _, _, hctx, _, _, hv_pg, _⟩ :=
      dualPgHost_eval_valid h (by clear *- hp9; omega) (by clear *- hp9; omega)
    have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := nLive) h (by clear *- hp9; omega)
      (by clear *- hp9; omega)
    have hm_ofCtx : PageArenaLayout.ofCtx pgH.toCtx = pgH := PageArenaLayout.ofCtx_toCtx pgH
    have hpre_sub : StepUnpermBatchPre w base s := by
      refine ⟨hw11, hb192, hfit_pad, ?_⟩
      rw [hctx, hm_ofCtx]; exact hv_pg
    have hio_d0 : activeDstIo c w vB base stg (s.mem (base + hdrPhase)) nSrc nDst pad
        ibLo qLo ibHi qHi nLive done = pagedSlotIo 1 pgH := by
      unfold activeDstIo
      rw [hp9, hd0]
      simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]
      rfl
    have hsl_d0 : EpochSlotInv c U V w s.frontier pDst mbDst (pagedSlotIo 1 pgH) 24 false
        L.slotDst s.mem := by
      rw [hio_d0] at hsl_d
      simpa only [hp9, hd0, and_self, ↓reduceIte] using hsl_d
    have hns_d : s.mem (mbDst + 1) = nLive := by
      rw [hsl_d0.mem_nSide_eq, ← dom_toDictState_card, hdict_d]
    have hio0 := hsl_d0.io_stateInv
    unfold SlotIoLayout.StateInv at hio0
    simp only [pagedSlotIo, SlotIoLayout.side, one_ne_zero, ↓reduceIte] at hio0
    rw [hns_d] at hio0
    obtain ⟨hi0, hps0, _, hti0, hvl0, _, _⟩ := hio0
    have hev_sub := stepUnpermBatchProg_eval base s
    dsimp only at hev_sub
    have hctx' : (Memory.spec 0).clientResult s (loadHostCtxProg (base, 0)) = pgH.toCtx := hctx
    rw [hctx'] at hev_sub
    obtain ⟨hst_sub, hmc_sub⟩ := hev_sub
    set ub := pageRunUnpermBatchProg (pgH.toCtx, itemBatchWhp)
    have hub_frm := pageRunUnpermBatchProg_frame (L := pgH) hw_pos itemBatchWhp
    obtain ⟨hfr2, hu2_eq, har2_eq⟩ := pageRunUnpermBatchProg_spec itemBatchWhp
      (hvL := hv_pg) hi0 hps0 hti0
    have hs2_low : ∀ a < base + 192, ((Memory.spec 0).clientState s ub).mem a = s.mem a :=
      fun a ha => hub_frm.mem_outside s a fun hpg => by
        rcases hpg with hm | hi
        · have h210 := (hdisj_pg a hm).1; clear *- ha h210; omega
        · have hi1 : ibHi ≤ a := hi.1
          clear *- ha hi1 hibHi_ge; omega
    have hm_s2_d : ∀ a, slotOwnsNonPageMeta c w mbDst L.slotDst.nCap a →
        ((Memory.spec 0).clientState s ub).mem a = s.mem a :=
      fun a ha => hub_frm.mem_outside s a fun hpg => by
        rcases hpg with hm | hi
        · have ha_d : slotOwnsNonPageMeta c w mbDst nDst a := hcap_d ▸ ha
          exact (hdisj_pg a hm).2.2.2 ha_d
        · have hi1 : ibHi ≤ a := hi.1
          rw [hcap_d] at ha
          unfold slotOwnsNonPageMeta mbDst dualMbDst at ha
          rw [hp9, ite_eq_left (by decide : 9 < 10)] at ha
          by_cases hdz : nDst = 0
          · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hdz, ↓reduceIte,
              ne_eq, not_true_eq_false, false_and, or_false] at ha
            dsimp only [hdrSmallMeta1] at ha
            clear *- ha hi1 hibHi_ge; omega
          · have hth_d : whpThreshold c ≤ nDst := (hsched.nDst_bounds.resolve_left hdz).1
            have hod_le : offPageDir c w nDst ≤ s.mem (base + hdrMDst) :=
              (epochMeta_offsets_le (w := w) hth_d).2.2.2.trans hmDst_eq.symm.le
            have h32 : 32 ≤ offPageDir c w nDst :=
              (epochMeta_offsets_le (w := w) hth_d).1.trans
                ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
                  (epochMeta_offsets_le (w := w) hth_d).2.2.1)
            have hmD_pad : s.mem (base + hdrMDst) ≤ pad := hpad_eq ▸ le_max_right _ _
            simp only [show s.mem (base + hdrNDst) = nDst from rfl, hdz, ↓reduceIte] at ha
            rw [hibHi_eq, ite_eq_right hdz] at hi1
            rcases ha with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
              (split_ifs at g1 g2 <;>
                (clear *- g1 g2 hi1 hod_le h32 hmD_pad; omega))
    obtain ⟨s2, hs2_def⟩ : ∃ s2, (Memory.spec 0).clientState s ub = s2 := ⟨_, rfl⟩
    rw [hs2_def] at hfr2 hu2_eq har2_eq hs2_low hm_s2_d hst_sub
    clear hs2_def
    have hu2_val : (PageUnpermState.runUnpermSteps itemBatchWhp
        (extractPageUnperm pgH s.mem)).1.Valid := runUnpermSteps_1024_valid hi0 hu0_pos
    have hu2_pos : 0 < (PageUnpermState.runUnpermSteps itemBatchWhp
        (extractPageUnperm pgH s.mem)).1.cleanPhase :=
      cleanPhase_pos_runUnpermSteps itemBatchWhp (extractPageUnperm pgH s.mem) hu0_pos
    obtain ⟨_, hps2, hvl2, hti2, _, _, hvirt2⟩ :=
      PageUnpermState.runUnpermSteps_spec.{0} itemBatchWhp hi0
    have hr := unpermRank_runUnpermSteps_le itemBatchWhp hi0
    obtain ⟨u2, hu2_def⟩ :
        ∃ u2, (PageUnpermState.runUnpermSteps itemBatchWhp (extractPageUnperm pgH s.mem)).1 = u2 :=
      ⟨_, rfl⟩
    rw [hu2_def] at hu2_eq hu2_val hu2_pos hps2 hvl2 hti2 hvirt2 hr
    clear hu2_def
    have hrk2 : u2.unpermRank ≤ L.unpermBound - (itemBatchWhp - 64) :=
      rank_step_sub_le hr hu0_rk
    have hmc_tot : memoryCost (stepUnpermBatchProg base) s ≤ 36 + 100 * itemBatchWhp := by
      have hc := hub_frm.cost_le s
      dsimp only [ub] at hmc_sub
      clear *- hmc_sub hc; omega
    have hcph2_mem : s2.mem (pgH.metaBase + 18) = u2.cleanPhase := by
      have : (extractPageUnperm pgH s2.mem).cleanPhase = s2.mem (pgH.metaBase + 18) := rfl
      rw [← this, hu2_eq]
    have hpair_s2 : ∀ idx < nLive,
        u2.virtAt (arenaPairAt pgH s2.mem) true idx =
          slotIoPairAt (pagedSlotIo 1 pgH) s.mem idx := by
      intro idx hidx
      rw [har2_eq]
      exact hvirt2 (arenaPairAt pgH s.mem) true idx (hvl0.symm ▸ hidx)
    by_cases hc4 : s2.mem (pgH.metaBase + 18) = 4
    · -- `cleanPhase = 4`: switches `pDst` to `directSlotIo` and sets `hdrUnpermDone := 1`
      have hu2_c4 : u2.cleanPhase = 4 := hcph2_mem ▸ hc4
      have hid4 := (hu2_val.phase4_id hu2_c4).2.2
      rw [ite_eq_left hc4, ← hpDst_eq, hlive_eq] at hst_sub
      set io_dir := directSlotIo w vB base ibHi qHi nLive
      set s3_raw := (Memory.spec 0).clientState s2
        (setDirectSlotIoProg ((base, pDst), ((ibHi, qHi), nLive)))
      have hs3_eq : s3_raw =
          (Memory.spec 0).clientState s2 (setSlotIoProg (pDst, io_dir.toCtx)) := by
        have hev := (setDirectSlotIoProg_eval base pDst ibHi qHi nLive s2).1
        have hw2 : s2.mem (base + hdrW) = w :=
          (hs2_low _ (by dsimp only [hdrW]; omega)).trans hw_eq
        have hvb2 : s2.mem (base + hdrValBits) = vB :=
          (hs2_low _ (by dsimp only [hdrValBits]; omega)).trans hvb_eq
        dsimp only [s3_raw]
        rw [hev, hw2, hvb2]
      set s3 := (Memory.spec 0).clientState s2 (setSlotIoProg (pDst, io_dir.toCtx))
      rw [hs3_eq] at hst_sub
      have hfr3 : s3.frontier = s.frontier :=
        (runClient_frontier_setSlotIoProg _ s2).trans hfr2
      have hfrm3 := setSlotIoProg_frame pDst io_dir.toCtx
      have hvals3 := setSlotIoProg_mem_vals pDst io_dir s2
      set s1 := (Memory.spec 0).clientState s (stepUnpermBatchProg base)
      have hs1_fr : s1.frontier = s.frontier := by rw [hst_sub]; exact hfr3
      have hud1 : s1.mem (base + hdrUnpermDone) = 1 := by
        rw [hst_sub]; exact Function.update_self ..
      have hs1_out_p : ∀ a, a ≠ base + hdrUnpermDone →
          ¬(pDst + 48 ≤ a ∧ a < pDst + 61) → s1.mem a = s2.mem a := fun a h1 hp => by
        rw [hst_sub]; dsimp only
        rw [Function.update_of_ne h1, hfrm3.mem_outside s2 a hp]
      have hpDst_ge64 : base + 64 ≤ pDst ∧ pDst + 64 ≤ base + 192 := by
        rw [hpDst_eq]; dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega
      have hs1_hdr : ∀ off < 48, off ≠ hdrUnpermDone → s1.mem (base + off) = s.mem (base + off) :=
        fun off hoff hne =>
          (hs1_out_p (base + off) (base_add_ne hne)
            (by clear *- hoff hpDst_ge64; omega)).trans (hs2_low (base + off) (by omega))
      have hs1_lt_b : ∀ a < base, s1.mem a = s.mem a := fun a ha =>
        (hs1_out_p a (by dsimp only [hdrUnpermDone]; clear *- ha; omega)
          (by clear *- ha hpDst_ge64; omega)).trans (hs2_low a (by omega))
      have hio_d1 : activeDstIo c w vB base stg 9 nSrc nDst pad ibLo qLo ibHi qHi nLive 1 =
          io_dir := by
        unfold activeDstIo
        simp only [Nat.reduceLT, Nat.reduceEqDiff, one_ne_zero, ↓reduceIte]
        rfl
      have hv_dir : io_dir.Valid w s.frontier := by
        unfold SlotIoLayout.Valid; dsimp only [io_dir, directSlotIo]
        simp only [↓reduceIte]
        exact ⟨hw_pos, trivial, hqHi_w, hvb_w, lt_of_le_of_lt hlive_le hUw, hfr_hi_lo⟩
      have hq_dir :
          (L.slotDst.nCap = 0 → io_dir.pgL.qBits = keyBits U) ∧
          (L.slotDst.nCap ≠ 0 → quotBitsWhp U L.slotDst.nCap ≤ io_dir.pgL.qBits) := by
        rw [hcap_d]; dsimp only [io_dir, directSlotIo, qHi] at hqHi_eq ⊢
        refine ⟨fun h0 => ?_, fun h0 => ?_⟩
        · have hle_kb : (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc) ≤ keyBits U := by
            split_ifs <;> [exact le_rfl; exact Nat.sub_le _ _]
          rw [hqHi_eq, ite_eq_left h0]
          exact max_eq_right hle_kb
        · rw [hqHi_eq, ite_eq_right h0]
          exact le_max_right _ _
      have hsl_s1 : EpochSlotInv c U V w s.frontier pDst mbDst io_dir 0 false L.slotDst s1.mem := by
        refine hsl_d0.set_slotIo (io₂ := io_dir) hv_dir rfl hq_dir rfl
          (fun k hk => by
            have hk_out : ¬(pDst + 48 ≤ pDst + k ∧ pDst + k < pDst + 61) := by
              rcases hk with hlt | rfl | rfl <;> omega
            have hne_u : pDst + k ≠ base + hdrUnpermDone := by
              dsimp only [hdrUnpermDone]; clear *- hpDst_ge64; omega
            have hk64 : k < 64 := by rcases hk with hlt | rfl | rfl <;> omega
            exact (hs1_out_p (pDst + k) hne_u hk_out).trans
              (hs2_low (pDst + k) (by clear *- hk64 hpDst_ge64; omega)))
          (by
            obtain ⟨hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12⟩ := hvals3
            have hrw : ∀ j < 13, s1.mem (pDst + (48 + j)) = s3.mem (pDst + (48 + j)) :=
              fun j _ => by
                rw [hst_sub]; dsimp only
                exact Function.update_of_ne
                  (by dsimp only [hdrUnpermDone]; clear *- hpDst_ge64; omega) _ _
            exact ⟨(hrw 0 (by decide)).trans hv0, (hrw 1 (by decide)).trans hv1,
              (hrw 2 (by decide)).trans hv2, (hrw 3 (by decide)).trans hv3,
              (hrw 4 (by decide)).trans hv4, (hrw 5 (by decide)).trans hv5,
              (hrw 6 (by decide)).trans hv6, (hrw 7 (by decide)).trans hv7,
              (hrw 8 (by decide)).trans hv8, (hrw 9 (by decide)).trans hv9,
              (hrw 10 (by decide)).trans hv10, (hrw 11 (by decide)).trans hv11,
              (hrw 12 (by decide)).trans hv12⟩)
          (fun a h1 h2 hown => by
            unfold SlotIoLayout.OwnsAddr PageArenaLayout.OwnsItemAddr at hown
            dsimp only [io_dir, directSlotIo] at hown
            simp only [↓reduceIte] at hown
            clear *- h1 h2 hpDst_ge64 hown hibHi_ge; omega)
          (fun a ha hown => by
            have hraw := hsl_d0; unfold EpochSlotInv at hraw
            unfold SlotIoLayout.OwnsAddr PageArenaLayout.OwnsItemAddr at hown
            dsimp only [io_dir, directSlotIo] at hown; simp only [↓reduceIte] at hown
            have hpg_own : (pagedSlotIo 1 pgH).OwnsAddr a := by
              unfold SlotIoLayout.OwnsAddr pagedSlotIo
              simp only [one_ne_zero, ↓reduceIte]; exact Or.inr hown
            unfold slotOwnsNonPageMeta at ha
            by_cases h0 : L.slotDst.nCap = 0
            · rw [ite_eq_left h0] at hraw ha
              rcases ha with ⟨g1, g2⟩ | ⟨hne, _⟩
              · exact hraw.2.2.1.disjoint_hdr a (by dsimp only; omega) hpg_own
              · exact absurd h0 hne
            · rw [ite_eq_right h0] at hraw ha
              exact hraw.1.disj_fast_io a (ha.imp id And.right) hpg_own)
          (fun a ha => by
            have ha_r : (base + 50 ≤ a ∧ a < base + 52) ∨ base + 192 ≤ a := by
              rw [hcap_d] at ha
              unfold slotOwnsNonPageMeta mbDst dualMbDst at ha
              rw [hp9, ite_eq_left (by decide : 9 < 10)] at ha
              by_cases hdz : nDst = 0
              · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hdz, ↓reduceIte,
                  ne_eq, not_true_eq_false, false_and, or_false] at ha
                dsimp only [hdrSmallMeta1] at ha; exact Or.inl ha
              · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hdz, ↓reduceIte] at ha
                rcases ha with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;>
                  (split_ifs at g1 <;> (clear *- g1; exact Or.inr (by omega)))
            refine (hs1_out_p a ?_ ?_).trans (hm_s2_d a ha)
            · dsimp only [hdrUnpermDone]; clear *- ha_r; omega
            · clear *- ha_r hpDst_ge64; omega)
          (by
            unfold SlotIoLayout.StateInv; dsimp only [io_dir, directSlotIo]
            simp only [↓reduceIte]; rw [hns_d]; exact ⟨le_rfl, Or.inl trivial⟩)
          (fun p hp => by
            rw [hns_d] at hp
            have hhi_eq : ∀ a, ibHi ≤ a → a < ibHi + pairStreamWords nLive qHi vB w →
                s1.mem a = s2.mem a := fun a h1 _ =>
              hs1_out_p a (by dsimp only [hdrUnpermDone]; clear *- h1 hibHi_ge; omega)
                (by clear *- h1 hibHi_ge hpDst_ge64; omega)
            have hlt_q := wOffQ_add_one_lt_pairStreamWords (q_bits := qHi) (v_bits := vB)
              hw_pos hp
            have hlt_v := wOffV_add_one_lt_pairStreamWords (q_bits := qHi) (v_bits := vB)
              hw_pos hp
            have hs1_ar : slotIoPairAt io_dir s1.mem p = arenaPairAt pgH s2.mem p := by
              unfold slotIoPairAt arenaPairAt pairQuotAt pairValAt readBitSlice
              dsimp only [io_dir, directSlotIo, pgH, dualPgHost, hostPageLayout,
                epochPageArenaLayout]
              simp only [↓reduceIte]
              rw [hhi_eq _ (Nat.le_add_right _ _) (by clear *- hlt_q; omega),
                hhi_eq _ (by omega) (by clear *- hlt_q; omega),
                hhi_eq _ (Nat.le_add_right _ _) (by clear *- hlt_v; omega),
                hhi_eq _ (by omega) (by clear *- hlt_v; omega)]
            have htp_id : u2.toPhys true p = p := hid4 p (hvl2.symm ▸ hvl0.symm ▸ hp)
            have hvirt_eq := hpair_s2 p hp
            unfold PageUnpermState.virtAt at hvirt_eq
            rw [htp_id] at hvirt_eq
            exact hs1_ar.trans hvirt_eq)
      refine ⟨fun _ => hpre_sub, hs1_fr, fun _ => hmc_tot, hs1_hdr, hs1_lt_b, ?_,
        fun _ => hud1, fun hz => absurd (hud1.symm.trans hz) (by decide), ?_⟩
      · rw [hud1]
      · rw [hud1, hio_d1]; exact hsl_s1
    · -- `cleanPhase ≠ 4`: `s1 = s2`, `done1 = 0`, `slack` restored from `24` to `0`!
      have hu2_ne4 : u2.cleanPhase ≠ 4 := hcph2_mem ▸ hc4
      have hu2_lt4 : u2.cleanPhase < 4 := by
        have hle4 := hu2_val.phase_le; clear *- hle4 hu2_ne4; omega
      rw [ite_eq_right hc4] at hst_sub
      set s1 := (Memory.spec 0).clientState s (stepUnpermBatchProg base)
      have hs1_fr : s1.frontier = s.frontier :=
        (congrArg Memory.State.frontier hst_sub).trans hfr2
      have hud1 : s1.mem (base + hdrUnpermDone) = 0 := by
        rw [hst_sub]
        exact (hs2_low (base + hdrUnpermDone) (by dsimp only [hdrUnpermDone]; omega)).trans hd0
      have hs1_hdr : ∀ off < 48, off ≠ hdrUnpermDone → s1.mem (base + off) = s.mem (base + off) :=
        fun off hoff _ => by rw [hst_sub]; exact hs2_low (base + off) (by omega)
      have hs1_lt_b : ∀ a < base, s1.mem a = s.mem a := fun a ha => by
        rw [hst_sub]; exact hs2_low a (by omega)
      have hn1_imp : ¬(1 < rem) → s1.mem (base + hdrUnpermDone) = 1 := fun hn1 => by
        exfalso
        have hrem_eq : rem = 1 := by clear *- hrem1 hn1; omega
        rw [hrem_eq, one_mul] at hub_le
        have hrk_z : u2.unpermRank = 0 := by clear *- hrk2 hub_le; omega
        exact hu2_ne4 (cleanPhase_eq_four_of_unpermRank_zero hu2_val hu2_pos hrk_z)
      have htp2_lt : u2.st.totalPages < pgH.maxPages := by
        have htot : u2.st.totalPages = u2.st.fullPages true := by
          unfold PagePairState.totalPages; rw [(hu2_val.src_empty hu2_pos).1, zero_add]
        have hvl_t : u2.st.fullPages true * pgH.pgB ≤ nLive := by
          have hv_eq := (congrFun hvl2 true).trans hvl0
          unfold PagePairState.virtLen at hv_eq
          rw [hps2.trans hps0] at hv_eq; omega
        have hpg_pos : 0 < pgH.pgB := lt_of_lt_of_le (by decide : 0 < 32)
          ((hps2.trans hps0) ▸ hu2_val.pageSize_ge)
        have hdiv : u2.st.fullPages true ≤ dualNHost base s.mem / pgH.pgB :=
          (Nat.le_div_iff_mul_le hpg_pos).mpr (hvl_t.trans hnL_host)
        dsimp only [pgH, dualPgHost, hostPageLayout, epochPageArenaLayout] at hdiv ⊢
        rw [htot]; omega
      have hio_s2 : (pagedSlotIo 1 pgH).StateInv (s.mem (mbDst + 1)) 0 s2.mem := by
        unfold SlotIoLayout.StateInv
        simp only [pagedSlotIo, SlotIoLayout.side, one_ne_zero, ↓reduceIte]
        rw [hns_d, hu2_eq]
        exact ⟨hu2_val, hps2.trans hps0, htp2_lt, hti2.trans_le hti0,
          (congrFun hvl2 true).trans hvl0, fun _ => rfl, hu2_lt4⟩
      have hsl_s2 : EpochSlotInv c U V w s.frontier pDst mbDst (pagedSlotIo 1 pgH) 0 false
          L.slotDst s2.mem := by
        have hraw := hsl_d0; unfold EpochSlotInv at hraw
        have hp_s2 : ∀ a, pDst ≤ a → a < pDst + 64 → s2.mem a = s.mem a := fun a _ h2 => by
          have hp_hi : pDst + 64 ≤ base + 192 := by
            rw [hpDst_eq]; dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega
          exact hs2_low a (lt_of_lt_of_le h2 hp_hi)
        refine hsl_d0.transfer_io (io₂ := pagedSlotIo 1 pgH) hsl_d0.io_valid rfl
          ⟨fun h0 => by rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.qBits_eq,
           fun h0 => by rw [ite_eq_right h0] at hraw; exact hraw.1.qBits_le⟩
          rfl
          ⟨fun h0 => by rw [ite_eq_left h0] at hraw; exact hraw.2.2.2.1.congr hp_s2,
           fun h0 => by
            rw [ite_eq_right h0] at hraw
            exact hraw.2.1.1.congr fun a hlo hhi =>
              hp_s2 a hlo (by dsimp only at hlo hhi; omega)⟩
          (fun a hlo hhi => by
            by_cases h0 : L.slotDst.nCap = 0
            · rw [ite_eq_left h0] at hraw
              exact fun hia => hraw.2.2.2.2.1 a hlo hhi (Or.inr (Or.inr hia))
            · rw [ite_eq_right h0] at hraw; exact hraw.1.disj_pBase_io a hlo hhi)
          (fun a ha => by
            unfold slotOwnsNonPageMeta at ha
            by_cases h0 : L.slotDst.nCap = 0
            · rw [ite_eq_left h0] at hraw ha
              rcases ha with ⟨g1, g2⟩ | ⟨hne, _⟩
              · exact hraw.2.2.1.disjoint_hdr a (by dsimp only; omega)
              · exact absurd h0 hne
            · rw [ite_eq_right h0] at hraw ha
              exact hraw.1.disj_fast_io a (ha.imp id And.right))
          hm_s2_d hio_s2
          (fun p hp => by
            rw [hns_d] at hp
            unfold slotIoPairAt
            dsimp only [pagedSlotIo, SlotIoLayout.side]
            simp only [one_ne_zero, ↓reduceIte]
            rw [hu2_eq]
            exact hpair_s2 p hp)
      have hio_d0' : activeDstIo c w vB base stg 9 nSrc nDst pad ibLo qLo ibHi qHi nLive 0 =
          pagedSlotIo 1 pgH := rfl
      refine ⟨fun _ => hpre_sub, hs1_fr, fun _ => hmc_tot, hs1_hdr, hs1_lt_b,
        by rw [hud1]; decide, hn1_imp, fun _ => ?_, ?_⟩
      · rw [hst_sub, hu2_eq]; exact ⟨hu2_pos, hu2_lt4, hrk2⟩
      · rw [hud1, hio_d0', hst_sub]; exact hsl_s2
  · -- `done ≠ 0` (`done = 1`): `optStepUnpermProg` is `pure ()` (`s1 = s`)!
    have hd1 : done = 1 := by clear *- hud_le hd0; omega
    have hs1_eq : (if s.mem (base + hdrUnpermDone) = 0 then
        (Memory.spec 0).clientState s (stepUnpermBatchProg base) else s) = s :=
      ite_eq_right hd0
    have hsl_d1 : EpochSlotInv c U V w s.frontier pDst mbDst
        (activeDstIo c w vB base stg 9 nSrc nDst pad ibLo qLo ibHi qHi nLive done)
        0 false L.slotDst s.mem := by
      simpa only [hp9, hd0, and_false, ↓reduceIte] using hsl_d
    refine ⟨fun h0 => absurd h0 hd0, ?_, fun h0 => absurd h0 hd0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs1_eq]
    · intro _ _ _; rw [hs1_eq]
    · intro _ _; rw [hs1_eq]
    · rw [hs1_eq]; exact hud_le
    · intro _; rw [hs1_eq]; exact hd1
    · intro h0; rw [hs1_eq] at h0; exact absurd h0 hd0
    · rw [hs1_eq]; exact hsl_d1

private theorem tickPhase9_bg_setup {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp9 : s.mem (base + hdrPhase) = 9) :
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let vB := valBits V
    let nLive := (Dictionary.dom s_dict).card
    let hiFr := ibHi + pairStreamWords nLive qHi vB w
    let s1 :=
      if s.mem (base + hdrUnpermDone) = 0 then
        (Memory.spec 0).clientState s (stepUnpermBatchProg base)
      else s
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    base + 196 ≤ ibHi ∧
    s.frontier - hiFr ≤ bulkBatchWhp ∧
    s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive ∧
    BgTickPre w (base, s.frontier) s ∧
    s_tick = (Memory.spec 0).clientState s (tickUnpermProg base) ∧
    (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier)) = (0, (0, 0)) ∧
    (Memory.spec 0).clientState s (tickUnpermProg base) =
      (if 1 < s.mem (base + hdrRem) then
        { mem := Function.update s1.mem (base + hdrRem) (s.mem (base + hdrRem) - 1)
          frontier := s1.frontier }
       else (Memory.spec 0).clientState s1 (finishUnpermProg base)) ∧
    Memory.WellFormed w s_tick ∧
    memoryCost (bgTickProg (base, s.frontier)) s ≤
      itemBatchWhp * (2 * epochStepCost c + 20) + 20000 ∧
    nLive ≤ L.nTrig + (L.elapsed + 1) ∧
    L.nTrig ≤ nLive + (L.elapsed + 1) ∧
    16 * (L.elapsed + 1) ≤ max (whpThreshold c) nSrc ∧
    nDst ≤ 2 * max (whpThreshold c) nSrc ∧
    nLive ≤ 2 * max (whpThreshold c) nSrc ∧
    whpThreshold c ≤ dualNHost base s.mem := by
  dsimp only
  have hw11 := h.hw11; have hw_pos : 0 < w := by clear *- hw11; omega
  have hUw := h.U_lt; have hwf := h.wf; have hb192 := h.base_fr
  have hlive_le := h.live_le; have hnSrc_b := h.nSrc_bounds
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp9; omega)] at hsched
  obtain ⟨hmDst_eq, hpad_eq, _, hd_logs, hibHi_eq, _⟩ :=
    hsched.ge2 (by clear *- hp9; omega)
  obtain ⟨hfr_hi_lo, hfr_hi_mid⟩ := hsched.ph3_10 ⟨by clear *- hp9; omega, by clear *- hp9; omega⟩
  obtain ⟨_, hvb_w, _, hqHi_w, _, hpad_hi_s, _, _⟩ := dualCoreInv_ib_fits h
  have hbud_old := hsched.budget; dsimp only at hbud_old
  obtain ⟨_, _, hb_el2⟩ := hbud_old
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set nLive := (Dictionary.dom s_dict).card
  set done := s.mem (base + hdrUnpermDone)
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  have hibHi_ge : base + 196 ≤ ibHi := by rw [hibHi_eq]; split_ifs <;> omega
  have hpw2 := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
    (show qHi + vB ≤ 2 * w by clear *- hqHi_w hvb_w; omega)
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    simp only [↓reduceIte] at hfr_hi_mid
    dsimp only [hiFr, ibHi, qHi, vB, nLive] at hfr_hi_mid hpw2 ⊢
    unfold bulkBatchWhp; clear *- hfr_hi_mid hpw2; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive := by
    rw [ite_eq_right (by clear *- hp9; omega)] at hpad_hi_s
    simp only [↓reduceIte] at hfr_hi_mid
    exact hfr_hi_mid.trans hpad_hi_s
  obtain ⟨hpre_sub, hs1_fr, hmc_sub, hs1_hdr, _, _, _, _, _⟩ := optStepUnperm_spec h hp9
  have hs1_opt_raw : (Memory.spec 0).clientState s
      (if s.mem (base + hdrUnpermDone) = 0 then stepUnpermBatchProg base else pure ()) =
      (if done = 0 then (Memory.spec 0).clientState s (stepUnpermBatchProg base) else s) := by
    by_cases hd0 : done = 0
    · simp only [show s.mem (base + hdrUnpermDone) = done from rfl, hd0, ↓reduceIte]
    · simp only [show s.mem (base + hdrUnpermDone) = done from rfl, hd0, ↓reduceIte]
      rfl
  obtain ⟨s1, hs1_def⟩ : ∃ s1,
      (if s.mem (base + hdrUnpermDone) = 0 then
        (Memory.spec 0).clientState s (stepUnpermBatchProg base) else s) = s1 := ⟨_, rfl⟩
  rw [hs1_def] at hs1_fr hs1_hdr hs1_opt_raw
  have hmDst_s1 : s1.mem (base + hdrMDst) = mDst := hs1_hdr hdrMDst (by decide) (by decide)
  have hnDst_s1 : s1.mem (base + hdrNDst) = nDst := hs1_hdr hdrNDst (by decide) (by decide)
  have hell_s1 : s1.mem (base + hdrEll) = s.mem (base + hdrEll) :=
    hs1_hdr hdrEll (by decide) (by decide)
  have hfit_md192 : Fits w (base + 192 + mDst) := by
    have hle : base + 192 + mDst ≤ hiFr := by
      dsimp only [hiFr]; rw [hibHi_eq]
      have hm_pad : mDst ≤ pad := hpad_eq ▸ le_max_right _ _
      split_ifs with hdz
      · have h0 : mDst = 0 := by
          rw [hmDst_eq, hdz]; unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
        rw [h0]; omega
      · clear *- hm_pad; omega
    dsimp only [Fits]; exact lt_of_le_of_lt (hle.trans hfr_hi_lo) hwf.1
  have hfit_12ell : 0 < nDst → Fits w (12 * s.mem (base + hdrEll)) := fun hd_pos => by
    have hth_d : whpThreshold c ≤ nDst ∧ nDst ≤ U := by
      rcases hsched.nDst_bounds with hz | hbd
      · exact absurd hz hd_pos.ne'
      · exact hbd
    have hell_eq := (hd_logs hd_pos).2.1
    obtain ⟨_, _, _, hbc_w, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      largeEpoch_param_bounds hth_d.1 hth_d.2 hUw
    have hce := codeExpWhp_mul_ell_le_bCharWhp hth_d.1
    have h12 : 12 ≤ codeExpWhp c := by
      have hq := le_qTabWhp c; have hc := le_cTabWhp c
      clear *- hq hc; rw [codeExpWhp_eq]; nlinarith
    have hmul : 12 * Dynamic.logLogFactor nDst ≤ bCharWhp nDst :=
      (Nat.mul_le_mul_right _ h12).trans hce
    have hw_pow : w < 2 ^ w := Nat.lt_two_pow_self
    rw [hell_eq]; dsimp only [Fits]; clear *- hmul hbc_w hw_pow; omega
  have hpre_tu : TickUnpermPre w base s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb192; omega, hpre_sub, fun _ => ?_⟩
    rw [hs1_opt_raw]
    exact ⟨by clear *- hw11; omega, hs1_fr ▸ hb192, hmDst_s1 ▸ hfit_md192,
      fun hd => hell_s1 ▸ hfit_12ell (hnDst_s1 ▸ hd)⟩
  have hpre_bg : BgTickPre w (base, s.frontier) s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb192; omega, ?_⟩
    dsimp only; simp only [hp9, Nat.reduceEqDiff, ↓reduceIte]
    exact hpre_tu
  have hbgev := bgTickProg_eval base s.frontier s
  dsimp only at hbgev
  simp only [hp9, Nat.reduceEqDiff, ↓reduceIte] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  obtain ⟨hst_tu, hmc_tu⟩ := tickUnpermProg_eval base s
  dsimp only at hst_tu hmc_tu
  have hwf_tick :
      Memory.WellFormed w ((Memory.spec 0).clientState s (bgTickProg (base, s.frontier))) :=
    wf_step hwf (validHistory_bgTickProg hwf hpre_bg)
  have hmc_all : memoryCost (bgTickProg (base, s.frontier)) s ≤
      itemBatchWhp * (2 * epochStepCost c + 20) + 20000 := by
    have hesc : 1600 ≤ epochStepCost c := by
      unfold epochStepCost smallStepCost
      have hle := le_max_left (21 * (2 * whpThreshold c) + 1600) (largeFastStepCost c)
      omega
    by_cases hd0 : done = 0
    · have hc0 := hmc_sub hd0
      simp only [show s.mem (base + hdrUnpermDone) = done from rfl, hd0, ↓reduceIte] at hmc_tu
      unfold itemBatchWhp at hc0 ⊢; clear *- hmc_bg hmc_tu hc0 hesc; omega
    · simp only [show s.mem (base + hdrUnpermDone) = done from rfl, hd0, ↓reduceIte] at hmc_tu
      unfold itemBatchWhp; clear *- hmc_bg hmc_tu hesc; omega
  have hd_hi' : nLive ≤ L.nTrig + (L.elapsed + 1) := by
    have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
  have hd_lo' : L.nTrig ≤ nLive + (L.elapsed + 1) := by
    have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
  have hel_le' : 16 * (L.elapsed + 1) ≤ max (whpThreshold c) nSrc := by
    clear *- hb_el2; omega
  obtain ⟨hnD_2R, hnL_2R⟩ := active_nLive_le_two_nRef hsched.post_trig hsched.trig_cap
    hd_hi' hd_lo' hel_le' hlive_le
  have hth_host : whpThreshold c ≤ dualNHost base s.mem := by
    rcases hsched.nDst_bounds with hz | ⟨hth, _⟩
    · unfold dualNHost; rw [ite_eq_left hz]
      exact (hnSrc_b.resolve_left (hsched.nDst_zero hz).1.ne').1
    · unfold dualNHost; rw [ite_eq_right (lt_of_lt_of_le (whpThreshold_pos c) hth).ne']
      exact hth
  exact ⟨hibHi_ge, hdiff_le, hfr_le_pad, hpre_bg, hst_bg, hres_bg, hst_tu, hwf_tick, hmc_all,
    hd_hi', hd_lo', hel_le', hnD_2R, hnL_2R, hth_host⟩

private theorem tickPhase9_stay_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp9 : s.mem (base + hdrPhase) = 9)
    (h1 : 1 < s.mem (base + hdrRem)) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hw_pos : 0 < w := by clear *- hw11; omega
  have hU0 := h.U_pos; have hUw := h.U_lt; have hV0 := h.V_pos; have hVw := h.V_le
  have hwf := h.wf; have hhdr := h.hdr
  have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hstg_le := h.stg_le; have hmSrc_eq := h.mSrc_eq
  have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds; have hpad_fits := h.pad_fits
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp9; omega)] at hsched
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hd_logs, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp9; omega)
  obtain ⟨hfr_hi_lo, _⟩ := hsched.ph3_10 ⟨by clear *- hp9; omega, by clear *- hp9; omega⟩
  obtain ⟨_, hrem_ub, hud_le, hud0_inv⟩ := h.ph9_inv hp9
  obtain ⟨hcap_d, hdict_d, _, hevs_d⟩ := h.sl_ge9 (by clear *- hp9; omega)
  have hbud_old := hsched.budget; dsimp only at hbud_old
  obtain ⟨_, hb_tot, _⟩ := hbud_old
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set nLive := (Dictionary.dom s_dict).card
  set rem := s.mem (base + hdrRem)
  set done := s.mem (base + hdrUnpermDone)
  set pgH := dualPgHost c V w base nLive s.mem
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  obtain ⟨hibHi_ge, hdiff_le, hfr_le_pad, hpre_bg, hst_bg, hres_bg, hst_tu, hwf_tick, hmc_all,
    hd_hi', hd_lo', _, _, _, _⟩ := tickPhase9_bg_setup h hp9
  obtain ⟨_, hs1_fr, _, hs1_hdr, hs1_lt_b, hd1_le, _, hd1_0_inv, hsl_s1⟩ :=
    optStepUnperm_spec h hp9
  obtain ⟨s1, hs1_def⟩ : ∃ s1,
      (if s.mem (base + hdrUnpermDone) = 0 then
        (Memory.spec 0).clientState s (stepUnpermBatchProg base) else s) = s1 := ⟨_, rfl⟩
  rw [hs1_def] at hs1_fr hs1_hdr hs1_lt_b hd1_le hd1_0_inv hsl_s1 hst_tu
  set done1 := s1.mem (base + hdrUnpermDone)
  set s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
  have hdisj_pg9 := disjoint_pgHost_nonPageMeta (nc := nLive) h
    (by clear *- hp9; omega) (by clear *- hp9; omega)
  rw [ite_eq_left h1] at hst_tu
  have hs_tick_eq : s_tick =
      { mem := Function.update s1.mem (base + hdrRem) (rem - 1), frontier := s.frontier } := by
    rw [hst_bg, hst_tu, hs1_fr]
  have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
  have hout_hdr : ∀ off < 48, off ≠ hdrRem → off ≠ hdrUnpermDone →
      s_tick.mem (base + off) = s.mem (base + off) := fun off hoff hr hu => by
    rw [hs_tick_eq]; dsimp only
    rw [Function.update_of_ne (base_add_ne hr)]
    exact hs1_hdr off hoff hu
  have hph_t : s_tick.mem (base + hdrPhase) = 9 :=
    (hout_hdr hdrPhase (by decide) (by decide) (by decide)).trans hp9
  have hst_t : s_tick.mem (base + hdrStage) = stg :=
    hout_hdr hdrStage (by decide) (by decide) (by decide)
  have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
    hout_hdr hdrNSrc (by decide) (by decide) (by decide)
  have hnD_t : s_tick.mem (base + hdrNDst) = nDst :=
    hout_hdr hdrNDst (by decide) (by decide) (by decide)
  have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
    hout_hdr hdrMSrc (by decide) (by decide) (by decide)
  have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
    hout_hdr hdrMDst (by decide) (by decide) (by decide)
  have hpad_t : s_tick.mem (base + hdrPad) = pad :=
    hout_hdr hdrPad (by decide) (by decide) (by decide)
  have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
    hout_hdr hdrItemLo (by decide) (by decide) (by decide)
  have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
    hout_hdr hdrItemHi (by decide) (by decide) (by decide)
  have hqL_t : s_tick.mem (base + hdrQLo) = qLo :=
    hout_hdr hdrQLo (by decide) (by decide) (by decide)
  have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
    hout_hdr hdrQHi (by decide) (by decide) (by decide)
  have hrem_t : s_tick.mem (base + hdrRem) = rem - 1 := by
    rw [hs_tick_eq]; exact Function.update_self ..
  have hud_t : s_tick.mem (base + hdrUnpermDone) = done1 := by
    rw [hs_tick_eq]; dsimp only
    exact Function.update_of_ne (base_add_ne (by decide)) _ _
  have hpgH_t : dualPgHost c V w base nLive s_tick.mem = pgH := by
    unfold dualPgHost dualNHost dualMbHost
    rw [hnD_t, hnS_t, hst_t, hpad_t, hibH_t, hqH_t]
  have hs_ge48 : ∀ a, base + 48 ≤ a → s_tick.mem a = s1.mem a := fun a ha => by
    rw [hs_tick_eq]; dsimp only
    exact Function.update_of_ne (by dsimp only [hdrRem]; clear *- ha; omega) _ _
  have hu_t : extractPageUnperm pgH s_tick.mem = extractPageUnperm pgH s1.mem :=
    extractPageUnperm_congr hw_pos fun a ha =>
      hs_ge48 a (by have h210 := (hdisj_pg9 a ha).1; clear *- h210; omega)
  set ub' := if done = 0 then L.unpermBound - (itemBatchWhp - 64) else L.unpermBound
  set L' : DualLatent c U V := { L with elapsed := L.elapsed + 1, unpermBound := ub' }
  have hsl_hi : EpochSlotInv c U V w hiFr (dualPDst base s.mem) (dualMbDst base s.mem)
      (activeDstIo c w vB base stg 9 nSrc nDst pad ibLo qLo ibHi qHi nLive done1)
      0 false L.slotDst s_tick.mem := by
    have hpDst_ge64 : base + 64 ≤ dualPDst base s.mem ∧
        dualPDst base s.mem + 64 ≤ base + 192 := by
      unfold dualPDst; rw [hp9, ite_eq_left (by decide : 9 < 10)]
      dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega
    have hsl_t0 := hsl_s1.congr_mem
      (fun a hlo _ => hs_ge48 a (by clear *- hlo hpDst_ge64; omega))
      (fun a ha => hs_ge48 a (by
        rw [hcap_d] at ha
        unfold slotOwnsNonPageMeta dualMbDst at ha
        rw [hp9, ite_eq_left (by decide : 9 < 10)] at ha
        by_cases hdz : nDst = 0
        · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hdz, ↓reduceIte,
            ne_eq, not_true_eq_false, false_and, or_false] at ha
          dsimp only [hdrSmallMeta1] at ha; clear *- ha; omega
        · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hdz, ↓reduceIte] at ha
          rcases ha with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;> (split_ifs at g1 <;> (clear *- g1; omega))))
      (fun a ha => hs_ge48 a (by
        unfold activeDstIo at ha
        simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] at ha
        by_cases hd1z : done1 = 0
        · rw [ite_eq_left hd1z] at ha
          unfold SlotIoLayout.OwnsAddr pagedSlotIo at ha
          simp only [one_ne_zero, ↓reduceIte] at ha
          rcases ha with hm | hi
          · have h210 := (hdisj_pg9 a hm).1; clear *- h210; omega
          · have hi1 : ibHi ≤ a := hi.1; clear *- hi1 hibHi_ge; omega
        · rw [ite_eq_right hd1z] at ha
          unfold SlotIoLayout.OwnsAddr directSlotIo PageArenaLayout.OwnsItemAddr at ha
          simp only [↓reduceIte] at ha
          have hi1 := ha.1; clear *- hi1 hibHi_ge; omega))
    refine hsl_t0.at_exact_frontier (fr₂ := hiFr)
      (by clear *- hpDst_ge64 hibHi_ge; dsimp only [hiFr]; omega)
      (by
        rw [hcap_d]; unfold dualMbDst; rw [hp9, ite_eq_left (by decide : 9 < 10), ← hmDst_eq]
        by_cases hdz : nDst = 0
        · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hdz, ↓reduceIte]
          dsimp only [hdrSmallMeta1, hiFr]; clear *- hibHi_ge; omega
        · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hdz, ↓reduceIte]
          dsimp only [hiFr]; rw [hibHi_eq, ite_eq_right hdz]
          have hm_pad : mDst ≤ pad := hpad_eq ▸ le_max_right _ _
          split_ifs <;> (dsimp only [mDst, pad] at hm_pad ⊢; clear *- hm_pad; omega))
      (by
        unfold activeDstIo
        simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]
        by_cases hd1z : done1 = 0
        · rw [ite_eq_left hd1z]
          dsimp only [pagedSlotIo, pgH, dualPgHost, hostPageLayout, epochPageArenaLayout,
            hiFr, ibHi, nLive, qHi, vB]
          simp only [one_ne_zero, false_and, ↓reduceIte]
          exact le_rfl
        · rw [ite_eq_right hd1z]
          dsimp only [directSlotIo, hiFr, ibHi, nLive, qHi, vB]
          simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte]
          exact le_rfl)
  refine ⟨hpre_bg, hfr_tick, hwf_tick,
    fun addr hlt_b => by
      rw [hs_tick_eq]; dsimp only
      rw [Function.update_of_ne (by dsimp only [hdrRem]; clear *- hlt_b; omega)]
      exact hs1_lt_b addr hlt_b, ?_⟩
  rw [ite_eq_left (by clear *- hp9; omega)]
  refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
    (fun ⟨_, h4⟩ => by rw [hph_t] at h4; cases h4) rfl rfl, ?_, fun _ _ => hmc_all⟩
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
          hout_hdr off (by clear *- hoff; omega) (by dsimp only [hdrRem]; clear *- hoff; omega)
            (by dsimp only [hdrUnpermDone]; clear *- hoff; omega)
        live_eq := (hout_hdr hdrLive (by decide) (by decide) (by decide)).trans hlive_eq
        live_le := hlive_le
        ph_le := by dsimp only; rw [hph_t]; decide
        stg_le := by dsimp only; rw [hst_t]; exact hstg_le
        mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
        cache_src := by
          dsimp only; rw [hnS_t]
          exact hostCacheValid_congr_mem hcache_s fun k hk => by
            rw [Nat.add_assoc]
            exact hout_hdr (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrRem]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrUnpermDone]; clear *- hk; omega)
        nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
        sched := by
          dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
          refine
            { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
              nDst_zero := fun hz => by
                dsimp only at hz ⊢
                obtain ⟨h1', h2', _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                rw [hnS_t, hst_t, hph_t]; exact ⟨h1', h2', by decide, by decide, by decide⟩
              stg_one := fun hs_o => by
                dsimp only at hs_o ⊢; rw [hnD_t, hph_t]
                exact ⟨(hsched.stg_one (hst_t.symm.trans hs_o)).1, by decide, by decide⟩
              post_trig := by dsimp only; rw [hnS_t]; exact hsched.post_trig
              trig_cap := by dsimp only; rw [hnS_t, hnD_t]; exact hsched.trig_cap
              drift_hi := by dsimp only [L']; simpa using hd_hi'
              drift_lo := by dsimp only [L']; simpa using hd_lo'
              ibLo_eq := by
                dsimp only; rw [hibL_t, hph_t, hmS_t, hmD_t]
                simpa only [hp9, Nat.reduceLT, ↓reduceIte] using hsched.ibLo_eq
              qLo_eq := by
                dsimp only; rw [hqL_t, hph_t, hnS_t, hnD_t]
                simpa only [hp9, Nat.reduceLT, ↓reduceIte] using hsched.qLo_eq
              ph1 := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
              ge2 := fun _ => by
                dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                    rw [Nat.add_assoc]
                    exact hout_hdr (hdrDstOd + k)
                      (by dsimp only [hdrDstOd]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrRem]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrUnpermDone]; clear *- hk; omega)
                · obtain ⟨hl, he, hp⟩ := hd_logs hd
                  exact ⟨(hout_hdr hdrLogN (by decide) (by decide) (by decide)).trans hl,
                    (hout_hdr hdrEll (by decide) (by decide) (by decide)).trans he,
                    (hout_hdr hdrPgB (by decide) (by decide) (by decide)).trans hp⟩
              ph2 := fun hp2 => absurd (hph_t.symm.trans hp2) (by decide)
              ph3_10 := fun _ => by
                dsimp only [hiFr]; rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
              ph11 := fun hp11 => absurd (hph_t.symm.trans hp11) (by decide)
              budget := by
                dsimp only [L']
                rw [hnS_t, hpgH_t, hst_t, hph_t, hnD_t, hmD_t, hrem_t]
                unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                simp only [show s.mem (base + hdrPhase) = 9 from hp9,
                  Nat.reduceEqDiff, Nat.reduceLeDiff, and_self, ↓reduceIte] at hb_tot ⊢
                dsimp only [nSrc, stg, nDst, mDst, rem, pgH, nLive] at hb_tot ⊢
                have h2t :=
                  two_le_maxTailPhasesBudget (max (whpThreshold c) (s.mem (base + hdrNSrc)))
                generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef at hb_tot h2t ⊢
                refine ⟨by clear *- h1 h2t; omega, ?_, ?_⟩ <;>
                  (clear *- hb_tot h1 h2t; omega) }
        pad_fits := by
          dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 9 ≠ 0)]
          simpa only [hp9, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
        ph1_inv := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
        ph3_inv := fun hp3 => absurd (hph_t.symm.trans hp3) (by decide)
        ph4_inv := fun hp4 => absurd (hph_t.symm.trans hp4) (by decide)
        pDst_pre := fun ⟨_, hp5⟩ => absurd (hph_t ▸ hp5) (by decide)
        ph5_inv := fun hp5 => absurd (hph_t.symm.trans hp5) (by decide)
        ph6_inv := fun hp6 => absurd (hph_t.symm.trans hp6) (by decide)
        ph7_inv := fun hp7 => absurd (hph_t.symm.trans hp7) (by decide)
        ph8_inv := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
        ph9_inv := fun _ => by
          dsimp only [L']; rw [hpgH_t, hrem_t, hnS_t, hud_t, hu_t]
          refine ⟨by clear *- h1; omega, by clear *- hrem_ub; omega, hd1_le, fun hd1_z => ?_⟩
          obtain ⟨hc_pos, hc_lt4, hrk_u⟩ := hd1_0_inv hd1_z
          have hd0_orig : done = 0 := by
            by_contra hne
            have hd1_eq : done1 = 1 := by
              have hd_eq1 : done = 1 := by clear *- hud_le hne; omega
              dsimp only [done1]; rw [← hs1_def, ite_eq_right hne]; exact hd_eq1
            exact absurd (hd1_z.symm.trans hd1_eq) (by decide)
          have hub_orig := (hud0_inv hd0_orig).2.2.2
          dsimp only [ub']; rw [ite_eq_left hd0_orig]
          simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
          refine ⟨hc_pos, hc_lt4, hrk_u, ?_⟩
          have hmul : (rem - 1) * (itemBatchWhp - 64) =
              rem * (itemBatchWhp - 64) - (itemBatchWhp - 64) := Nat.sub_one_mul _ _
          rw [hmul]; exact Nat.sub_le_sub_right hub_orig _
        ph10_inv := fun hp10 => absurd (hph_t.symm.trans hp10) (by decide)
        sl_le7 := fun hp7 => absurd (hph_t ▸ hp7) (by decide)
        sl_67 := fun h67 => by
          dsimp only at h67
          rcases h67 with h6 | h7 <;> exact absurd (hph_t.symm.trans ‹_›) (by decide)
        sl_8 := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
        sl_ge9 := fun _ => by
          dsimp only [L']
          rw [hnD_t, hst_t, hph_t, hnS_t, hpad_t, hibL_t, hqL_t, hibH_t, hqH_t, hud_t]
          have hpD_eq : dualPDst base s_tick.mem = dualPDst base s.mem := by
            unfold dualPDst; rw [hph_t, hp9, hst_t]
          have hmbD_eq : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
            unfold dualMbDst; rw [hph_t, hp9, hnD_t, hst_t, hpad_t]
          rw [hpD_eq, hmbD_eq]
          simp only [Bool.false_eq_true, false_and, ↓reduceIte, add_zero]
          exact ⟨hcap_d, hdict_d, hsl_hi, fun hd_pos => by
            have he := hevs_d hd_pos; simp only [↓reduceIte] at he; exact he⟩ }

private theorem tickPhase9_goB_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp9 : s.mem (base + hdrPhase) = 9)
    (h1 : ¬(1 < s.mem (base + hdrRem)))
    (hgoB : s.mem (base + hdrStage) = 0 ∧ 0 < s.mem (base + hdrNDst)) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hw_pos : 0 < w := by clear *- hw11; omega
  have hU0 := h.U_pos; have hUw := h.U_lt; have hV0 := h.V_pos; have hVw := h.V_le
  have hwf := h.wf; have hhdr := h.hdr
  have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hmSrc_eq := h.mSrc_eq
  have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds; have hpad_fits := h.pad_fits
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp9; omega)] at hsched
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hd_logs, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp9; omega)
  obtain ⟨hfr_hi_lo, _⟩ := hsched.ph3_10 ⟨by clear *- hp9; omega, by clear *- hp9; omega⟩
  obtain ⟨hrem1, _, _, _⟩ := h.ph9_inv hp9
  obtain ⟨hcap_d, hdict_d, _, hevs_d⟩ := h.sl_ge9 (by clear *- hp9; omega)
  have hbud_old := hsched.budget; dsimp only at hbud_old
  obtain ⟨_, hb_tot, _⟩ := hbud_old
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set nLive := (Dictionary.dom s_dict).card
  set rem := s.mem (base + hdrRem)
  set pgH := dualPgHost c V w base nLive s.mem
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  obtain ⟨hibHi_ge, hdiff_le, hfr_le_pad, hpre_bg, hst_bg, hres_bg, hst_tu, hwf_tick, hmc_all,
    hd_hi', hd_lo', hel_le', hnD_2R, _, _⟩ := tickPhase9_bg_setup h hp9
  obtain ⟨_, hs1_fr, _, hs1_hdr, hs1_lt_b, _, hn1_d1, _, hsl_s1⟩ := optStepUnperm_spec h hp9
  obtain ⟨s1, hs1_def⟩ : ∃ s1,
      (if s.mem (base + hdrUnpermDone) = 0 then
        (Memory.spec 0).clientState s (stepUnpermBatchProg base) else s) = s1 := ⟨_, rfl⟩
  rw [hs1_def] at hs1_fr hs1_hdr hs1_lt_b hn1_d1 hsl_s1 hst_tu
  set done1 := s1.mem (base + hdrUnpermDone)
  have hnDst_s1 : s1.mem (base + hdrNDst) = nDst := hs1_hdr hdrNDst (by decide) (by decide)
  set s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
  have hrem_eq1 : rem = 1 := by clear *- hrem1 h1; omega
  have hdone1 : done1 = 1 := hn1_d1 h1
  rw [ite_eq_right h1] at hst_tu
  have hio_d1 : activeDstIo c w vB base stg 9 nSrc nDst pad ibLo qLo ibHi qHi nLive done1 =
      directSlotIo w vB base ibHi qHi nLive := by
    rw [hdone1]; unfold activeDstIo
    simp only [Nat.reduceLT, Nat.reduceEqDiff, one_ne_zero, ↓reduceIte]
  rw [hio_d1] at hsl_s1
  set io_dir := directSlotIo w vB base ibHi qHi nLive
  obtain ⟨hst_fu, _⟩ := finishUnpermProg_eval base s1
  dsimp only at hst_fu
  have hst_s1 : s1.mem (base + hdrStage) = stg := hs1_hdr hdrStage (by decide) (by decide)
  rw [hst_s1, hnDst_s1] at hst_fu
  obtain ⟨hst0, hd_pos⟩ := hgoB
  rw [ite_eq_left ⟨hst0, hd_pos⟩] at hst_fu
  have hs_tick_eq : s_tick =
      { mem := Function.update (Function.update
          (Function.update s1.mem (base + hdrStage) 1)
          (base + hdrCur) 0)
          (base + hdrPhase) 4,
        frontier := s.frontier } := by
    rw [hst_bg, hst_tu, hst_fu, hs1_fr]
  have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
  have hout_hdr : ∀ off < 48, off ≠ hdrPhase → off ≠ hdrCur → off ≠ hdrStage →
      off ≠ hdrUnpermDone → s_tick.mem (base + off) = s.mem (base + off) :=
    fun off hoff hph hc hs hu => by
      rw [hs_tick_eq]; dsimp only
      rw [Function.update_of_ne (base_add_ne hph), Function.update_of_ne (base_add_ne hc),
        Function.update_of_ne (base_add_ne hs)]
      exact hs1_hdr off hoff hu
  have hph_t : s_tick.mem (base + hdrPhase) = 4 := by
    rw [hs_tick_eq]; exact Function.update_self ..
  have hcur_t : s_tick.mem (base + hdrCur) = 0 := by
    rw [hs_tick_eq]; dsimp only
    rw [Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
  have hst_t : s_tick.mem (base + hdrStage) = 1 := by
    rw [hs_tick_eq]; dsimp only
    rw [Function.update_of_ne (base_add_ne (by decide)),
      Function.update_of_ne (base_add_ne (by decide))]
    exact Function.update_self ..
  have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
    hout_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide) (by decide)
  have hnD_t : s_tick.mem (base + hdrNDst) = nDst :=
    hout_hdr hdrNDst (by decide) (by decide) (by decide) (by decide) (by decide)
  have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
    hout_hdr hdrMSrc (by decide) (by decide) (by decide) (by decide) (by decide)
  have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
    hout_hdr hdrMDst (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpad_t : s_tick.mem (base + hdrPad) = pad :=
    hout_hdr hdrPad (by decide) (by decide) (by decide) (by decide) (by decide)
  have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
    hout_hdr hdrItemLo (by decide) (by decide) (by decide) (by decide) (by decide)
  have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
    hout_hdr hdrItemHi (by decide) (by decide) (by decide) (by decide) (by decide)
  have hqL_t : s_tick.mem (base + hdrQLo) = qLo :=
    hout_hdr hdrQLo (by decide) (by decide) (by decide) (by decide) (by decide)
  have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
    hout_hdr hdrQHi (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs_ge48 : ∀ a, base + 48 ≤ a → s_tick.mem a = s1.mem a := fun a ha => by
    rw [hs_tick_eq]; dsimp only
    iterate 3 rw [Function.update_of_ne
      (by dsimp only [hdrPhase, hdrCur, hdrStage]; clear *- ha; omega)]
  set L' : DualLatent c U V := { L with slotSrc := L.slotDst, elapsed := L.elapsed + 1 }
  have hpres : PreservesEpochSeeds (s.mem (base + hdrPhase) = 8)
      (s.mem (base + hdrPhase) = 9 ∧ s_tick.mem (base + hdrPhase) = 4) L L' :=
    ⟨⟨fun hnp => absurd ⟨hp9, hph_t⟩ hnp, fun _ => ⟨rfl, HEq.rfl, rfl⟩⟩,
     Or.inr ⟨rfl, HEq.rfl, ⟨[], (List.append_nil _).symm⟩, fun _ => rfl⟩⟩
  have hpS_eq : dualPSrc base s_tick.mem = dualPDst base s.mem := by
    unfold dualPSrc dualPDst; dsimp only [stg] at hst0
    rw [hst_t, hp9, ite_eq_left (by decide : 9 < 10), hst0]; rfl
  have hmbS_eq : dualMbSrc base s_tick.mem = dualMbDst base s.mem := by
    unfold dualMbSrc dualMbDst; dsimp only [stg, nDst, pad] at hst0 hd_pos hpad_t
    rw [hst_t, hpad_t, hp9, ite_eq_left (by decide : 9 < 10), ite_eq_right hd_pos.ne', hst0]
    rfl
  have hsl_src_hi : EpochSlotInv c U V w hiFr (dualPSrc base s_tick.mem)
      (dualMbSrc base s_tick.mem) io_dir 0 false L.slotDst s_tick.mem := by
    rw [hpS_eq, hmbS_eq]
    have hpD_eq1 : dualPDst base s.mem = base + hdrPBase1 := by
      unfold dualPDst; dsimp only [stg] at hst0
      rw [hp9, ite_eq_left (by decide : 9 < 10), ite_eq_left hst0]
    have hmbD_eq1 : dualMbDst base s.mem = base + 192 + pad := by
      unfold dualMbDst; dsimp only [stg, nDst] at hst0 hd_pos
      rw [hp9, ite_eq_left (by decide : 9 < 10), ite_eq_right hd_pos.ne', ite_eq_left hst0]
    have hsl_t0 := hsl_s1.congr_mem
      (fun a hlo _ => hs_ge48 a (by rw [hpD_eq1] at hlo; dsimp only [hdrPBase1] at hlo; omega))
      (fun a ha => hs_ge48 a (by
        rw [hcap_d, hmbD_eq1] at ha
        unfold slotOwnsNonPageMeta at ha
        simp only [hd_pos.ne', ↓reduceIte] at ha
        rcases ha with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;> (clear *- g1; omega)))
      (fun a ha => hs_ge48 a (by
        unfold SlotIoLayout.OwnsAddr PageArenaLayout.OwnsItemAddr at ha
        dsimp only [io_dir, directSlotIo] at ha
        simp only [↓reduceIte] at ha
        have := ha.1; clear *- this hibHi_ge; omega))
    refine hsl_t0.at_exact_frontier (fr₂ := hiFr)
      (by rw [hpD_eq1]; dsimp only [hdrPBase1, hiFr]; clear *- hibHi_ge; omega)
      (by
        rw [hcap_d, hmbD_eq1, ite_eq_right hd_pos.ne', ← hmDst_eq]
        dsimp only [hiFr]; rw [hibHi_eq, ite_eq_right hd_pos.ne']; clear *-; omega)
      (by
        dsimp only [io_dir, directSlotIo, hiFr]
        simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte]
        exact le_rfl)
  have hth_d : whpThreshold c ≤ nDst ∧ nDst ≤ U := by
    rcases hsched.nDst_bounds with hz | hbd
    · exact absurd hz hd_pos.ne'
    · exact hbd
  have hmD_2R : mDst ≤ 2 * max (whpThreshold c) nSrc + 512 := by
    have h1' : mDst ≤ nDst + 120 :=
      hmDst_eq.trans_le (epochMetaWordsWhp_le_self hth_d.1 (lt_of_le_of_lt hth_d.2 hUw))
    generalize max (whpThreshold c) nSrc = nRef at hnD_2R ⊢
    clear *- h1' hnD_2R; omega
  refine ⟨hpre_bg, hfr_tick, hwf_tick,
    fun addr hlt_b => by
      rw [hs_tick_eq]; dsimp only
      iterate 3 rw [Function.update_of_ne
        (by dsimp only [hdrPhase, hdrCur, hdrStage]; clear *- hlt_b; omega)]
      exact hs1_lt_b addr hlt_b, ?_⟩
  rw [ite_eq_left (by clear *- hp9; omega)]
  refine ⟨hres_bg, L', hpres, ?_, fun _ _ => hmc_all⟩
  refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
  · rw [hnS_t, hph_t, ite_eq_right (by decide : 4 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
  · rw [hph_t, ite_eq_right (by decide : ¬(4 < 2)), ite_eq_right (by decide : 4 ≠ 2),
      ite_eq_left (by decide : 4 ≤ 10), hibH_t, hqH_t, hfr_tick]
    refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
    exact
      { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
        wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, hwf_tick.2⟩
        base_fr := by dsimp only [hiFr]; clear *- hibHi_ge; omega
        hdr := rootStaticHeader_congr hhdr fun off hoff =>
          hout_hdr off (by clear *- hoff; omega)
            (by dsimp only [hdrPhase]; clear *- hoff; omega)
            (by dsimp only [hdrCur]; clear *- hoff; omega)
            (by dsimp only [hdrStage]; clear *- hoff; omega)
            (by dsimp only [hdrUnpermDone]; clear *- hoff; omega)
        live_eq := (hout_hdr hdrLive (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hlive_eq
        live_le := hlive_le
        ph_le := by dsimp only; rw [hph_t]; decide
        stg_le := by dsimp only; rw [hst_t]
        mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
        cache_src := by
          dsimp only; rw [hnS_t]
          exact hostCacheValid_congr_mem hcache_s fun k hk => by
            rw [Nat.add_assoc]
            exact hout_hdr (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrStage]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrUnpermDone]; clear *- hk; omega)
        nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
        sched := by
          dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
          refine
            { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
              nDst_zero := fun hz => absurd (hnD_t.symm.trans hz) hd_pos.ne'
              stg_one := fun _ => by
                dsimp only; rw [hnD_t, hph_t]; exact ⟨hd_pos, by decide, by decide⟩
              post_trig := by dsimp only; rw [hnS_t]; exact hsched.post_trig
              trig_cap := by dsimp only; rw [hnS_t, hnD_t]; exact hsched.trig_cap
              drift_hi := by dsimp only [L']; simpa using hd_hi'
              drift_lo := by dsimp only [L']; simpa using hd_lo'
              ibLo_eq := by
                dsimp only; rw [hibL_t, hph_t, hmS_t, hmD_t]
                simpa only [hp9, Nat.reduceLT, ↓reduceIte] using hsched.ibLo_eq
              qLo_eq := by
                dsimp only; rw [hqL_t, hph_t, hnS_t, hnD_t]
                simpa only [hp9, Nat.reduceLT, ↓reduceIte] using hsched.qLo_eq
              ph1 := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
              ge2 := fun _ => by
                dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                    rw [Nat.add_assoc]
                    exact hout_hdr (hdrDstOd + k)
                      (by dsimp only [hdrDstOd]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrCur]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrStage]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrUnpermDone]; clear *- hk; omega)
                · obtain ⟨hl, he, hp⟩ := hd_logs hd
                  exact ⟨(hout_hdr hdrLogN (by decide) (by decide) (by decide)
                      (by decide) (by decide)).trans hl,
                    (hout_hdr hdrEll (by decide) (by decide) (by decide)
                      (by decide) (by decide)).trans he,
                    (hout_hdr hdrPgB (by decide) (by decide) (by decide)
                      (by decide) (by decide)).trans hp⟩
              ph2 := fun hp2 => absurd (hph_t.symm.trans hp2) (by decide)
              ph3_10 := fun _ => by
                dsimp only [hiFr]; rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
              ph11 := fun hp11 => absurd (hph_t.symm.trans hp11) (by decide)
              budget := by
                dsimp only [L']
                rw [hnS_t, hst_t, hph_t, hmD_t, hcur_t, hnD_t]
                unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                dsimp only [stg, nSrc, nDst, mDst, rem] at hst0 hrem_eq1 hb_tot hmD_2R ⊢
                simp only [show s.mem (base + hdrPhase) = 9 from hp9, hst0, hrem_eq1,
                  Nat.reduceEqDiff, Nat.reduceLeDiff, and_self, ↓reduceIte,
                  Nat.sub_zero] at hb_tot ⊢
                have hdiv_mD := Nat.div_le_div_right (c := 1024) hmD_2R
                unfold maxStageBudget at hb_tot
                dsimp only at hb_tot ⊢
                have h2t :=
                  two_le_maxTailPhasesBudget (max (whpThreshold c) (s.mem (base + hdrNSrc)))
                generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef
                  at hb_tot hdiv_mD h2t ⊢
                refine ⟨by clear *- h2t; omega, ?_, ?_⟩ <;>
                  (clear *- hb_tot hdiv_mD h2t; omega) }
        pad_fits := by
          dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 4 ≠ 0)]
          simpa only [hp9, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
        ph1_inv := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
        ph3_inv := fun hp3 => absurd (hph_t.symm.trans hp3) (by decide)
        ph4_inv := fun _ => by
          dsimp only; rw [hnD_t, hcur_t, hmD_t]
          exact ⟨hd_pos, Nat.zero_le _, fun _ ho => absurd ho (Nat.not_lt_zero _)⟩
        pDst_pre := fun _ h50 => by
          dsimp only at h50; rw [hph_t, hst_t] at h50
          rcases h50 with h5 | h0 <;> exact absurd ‹_› (by decide)
        ph5_inv := fun hp5 => absurd (hph_t.symm.trans hp5) (by decide)
        ph6_inv := fun hp6 => absurd (hph_t.symm.trans hp6) (by decide)
        ph7_inv := fun hp7 => absurd (hph_t.symm.trans hp7) (by decide)
        ph8_inv := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
        ph9_inv := fun hp9' => absurd (hph_t.symm.trans hp9') (by decide)
        ph10_inv := fun hp10 => absurd (hph_t.symm.trans hp10) (by decide)
        sl_le7 := fun _ => by
          dsimp only [L']
          have hcap_t : dualCapSrc base s_tick.mem = nDst := by
            unfold dualCapSrc; rw [hst_t, ite_eq_right one_ne_zero, hnD_t]
          have hio_s4 : activeSrcIo c w vB base 1 4 nSrc nDst pad ibLo qLo ibHi qHi nLive =
              io_dir := by
            unfold activeSrcIo; simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]; rfl
          rw [hcap_t, hst_t, hph_t, hnS_t, hnD_t, hpad_t, hibL_t, hqL_t, hibH_t, hqH_t, hio_s4]
          refine ⟨hcap_d, hdict_d, hsl_src_hi, fun _ _ => ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
          have he := hevs_d hd_pos; simp only [↓reduceIte] at he
          clear *- he; omega
        sl_67 := fun h67 => by
          dsimp only at h67
          rcases h67 with h6 | h7 <;> exact absurd (hph_t.symm.trans ‹_›) (by decide)
        sl_8 := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
        sl_ge9 := fun h9 => absurd (hph_t ▸ h9) (by decide) }

private theorem tickPhase9_slide_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp9 : s.mem (base + hdrPhase) = 9)
    (h1 : ¬(1 < s.mem (base + hdrRem)))
    (hgoB : ¬(s.mem (base + hdrStage) = 0 ∧ 0 < s.mem (base + hdrNDst))) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hw_pos : 0 < w := by clear *- hw11; omega
  have hU0 := h.U_pos; have hUw := h.U_lt; have hV0 := h.V_pos; have hVw := h.V_le
  have hwf := h.wf; have hhdr := h.hdr
  have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hstg_le := h.stg_le; have hmSrc_eq := h.mSrc_eq
  have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds; have hpad_fits := h.pad_fits
  have hkb_eq := hhdr.2.2.2.1; have hvb_eq := hhdr.2.2.2.2.1; have hw_eq := hhdr.2.2.1
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp9; omega)] at hsched
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hd_logs, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp9; omega)
  obtain ⟨hfr_hi_lo, _⟩ := hsched.ph3_10 ⟨by clear *- hp9; omega, by clear *- hp9; omega⟩
  obtain ⟨_, hvb_w, _, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits h
  obtain ⟨hrem1, _, _, _⟩ := h.ph9_inv hp9
  obtain ⟨hcap_d, hdict_d, _, hevs_d⟩ := h.sl_ge9 (by clear *- hp9; omega)
  have hbud_old := hsched.budget; dsimp only at hbud_old
  obtain ⟨_, hb_tot, _⟩ := hbud_old
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set nLive := (Dictionary.dom s_dict).card
  set rem := s.mem (base + hdrRem)
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  obtain ⟨hibHi_ge, hdiff_le, hfr_le_pad, hpre_bg, hst_bg, hres_bg, hst_tu, hwf_tick, hmc_all,
    hd_hi', hd_lo', hel_le', hnD_2R, hnL_2R, _⟩ := tickPhase9_bg_setup h hp9
  obtain ⟨_, hs1_fr, _, hs1_hdr, hs1_lt_b, _, hn1_d1, _, hsl_s1⟩ := optStepUnperm_spec h hp9
  obtain ⟨s1, hs1_def⟩ : ∃ s1,
      (if s.mem (base + hdrUnpermDone) = 0 then
        (Memory.spec 0).clientState s (stepUnpermBatchProg base) else s) = s1 := ⟨_, rfl⟩
  rw [hs1_def] at hs1_fr hs1_hdr hs1_lt_b hn1_d1 hsl_s1 hst_tu
  set done1 := s1.mem (base + hdrUnpermDone)
  have hmDst_s1 : s1.mem (base + hdrMDst) = mDst := hs1_hdr hdrMDst (by decide) (by decide)
  have hnDst_s1 : s1.mem (base + hdrNDst) = nDst := hs1_hdr hdrNDst (by decide) (by decide)
  set s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
  have hrem_eq1 : rem = 1 := by clear *- hrem1 h1; omega
  have hdone1 : done1 = 1 := hn1_d1 h1
  rw [ite_eq_right h1] at hst_tu
  have hio_d1 : activeDstIo c w vB base stg 9 nSrc nDst pad ibLo qLo ibHi qHi nLive done1 =
      directSlotIo w vB base ibHi qHi nLive := by
    rw [hdone1]; unfold activeDstIo
    simp only [Nat.reduceLT, Nat.reduceEqDiff, one_ne_zero, ↓reduceIte]
  rw [hio_d1] at hsl_s1
  set io_dir := directSlotIo w vB base ibHi qHi nLive
  obtain ⟨hst_fu, _⟩ := finishUnpermProg_eval base s1
  dsimp only at hst_fu
  have hst_s1 : s1.mem (base + hdrStage) = stg := hs1_hdr hdrStage (by decide) (by decide)
  rw [hst_s1, hnDst_s1] at hst_fu
  rw [ite_eq_right hgoB] at hst_fu
  have hkb_s1 : s1.mem (base + hdrKeyBits) = keyBits U :=
    (hs1_hdr hdrKeyBits (by decide) (by decide)).trans hkb_eq
  have hlive_s1 : s1.mem (base + hdrLive) = nLive :=
    (hs1_hdr hdrLive (by decide) (by decide)).trans hlive_eq
  set ibLo' := base + 192 + mDst
  set qLo' := if nDst = 0 then keyBits U else quotBitsWhp U nDst
  have hqLo'_eval :
      (if nDst = 0 then s1.mem (base + hdrKeyBits)
       else s1.mem (base + hdrKeyBits) -
         (s1.mem (base + hdrLogN) - 12 * s1.mem (base + hdrEll))) = qLo' := by
    rw [hkb_s1]
    by_cases hdz : nDst = 0
    · simp only [hdz, ↓reduceIte, qLo']
    · have hd_pos := Nat.pos_of_ne_zero hdz
      obtain ⟨hl, he, _⟩ := hd_logs hd_pos
      have hl1 := (hs1_hdr hdrLogN (by decide) (by decide)).trans hl
      have he1 := (hs1_hdr hdrEll (by decide) (by decide)).trans he
      dsimp only [qLo']; rw [ite_eq_right hdz, ite_eq_right hdz]
      unfold quotBitsWhp bWhp; rw [hl1, he1]
  rw [hmDst_s1, hlive_s1, hqLo'_eval] at hst_fu
  set m_sm := if stg = 0 then
      Function.update (Function.update (Function.update
        (Function.update s1.mem (base + hdrSmallMeta0) 0)
        (base + hdrSmallMeta0 + 1) nLive)
        (base + hdrPBase0) 0)
        (base + hdrPBase0 + 1) (base + hdrSmallMeta0)
    else s1.mem
  set s_pre : Memory.State :=
    { mem := Function.update (Function.update
        (Function.update m_sm (base + hdrItemLo) ibLo')
        (base + hdrQLo) qLo')
        (base + hdrSplit) 0,
      frontier := s.frontier }
  set io_sp := splitSlotIo w vB base ibLo' qLo' ibHi qHi nLive
  have hs_sp_eq : (Memory.spec 0).clientState s_pre
      (setSplitSlotIoProg ((base, base + hdrPBase0), nLive)) =
      (Memory.spec 0).clientState s_pre (setSlotIoProg (base + hdrPBase0, io_sp.toCtx)) := by
    have hev := (setSplitSlotIoProg_eval base (base + hdrPBase0) nLive s_pre).1
    have hpre_hdr : ∀ off < 16, s_pre.mem (base + off) = s1.mem (base + off) := fun off ho => by
      dsimp only [s_pre, m_sm]
      iterate 3 rw [Function.update_of_ne
        (by dsimp only [hdrItemLo, hdrQLo, hdrSplit]; clear *- ho; omega)]
      split_ifs
      · iterate 4 rw [Function.update_of_ne
          (by dsimp only [hdrSmallMeta0, hdrPBase0]; clear *- ho; omega)]
      · rfl
    have hw_p : s_pre.mem (base + hdrW) = w :=
      (hpre_hdr hdrW (by decide)).trans ((hs1_hdr hdrW (by decide) (by decide)).trans hw_eq)
    have hvb_p : s_pre.mem (base + hdrValBits) = vB :=
      (hpre_hdr hdrValBits (by decide)).trans
        ((hs1_hdr hdrValBits (by decide) (by decide)).trans hvb_eq)
    have hil_p : s_pre.mem (base + hdrItemLo) = ibLo' := by
      dsimp only [s_pre]
      iterate 2 rw [Function.update_of_ne (base_add_ne (by decide))]
      exact Function.update_self ..
    have hql_p : s_pre.mem (base + hdrQLo) = qLo' := by
      dsimp only [s_pre]
      rw [Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
    have hih_p : s_pre.mem (base + hdrItemHi) = ibHi := by
      dsimp only [s_pre, m_sm]
      iterate 3 rw [Function.update_of_ne (base_add_ne (by decide))]
      split_ifs
      · iterate 4 rw [Function.update_of_ne
          (by dsimp only [hdrItemHi, hdrSmallMeta0, hdrPBase0]; omega)]
        exact hs1_hdr hdrItemHi (by decide) (by decide)
      · exact hs1_hdr hdrItemHi (by decide) (by decide)
    have hqh_p : s_pre.mem (base + hdrQHi) = qHi := by
      dsimp only [s_pre, m_sm]
      iterate 3 rw [Function.update_of_ne (base_add_ne (by decide))]
      split_ifs
      · iterate 4 rw [Function.update_of_ne
          (by dsimp only [hdrQHi, hdrSmallMeta0, hdrPBase0]; omega)]
        exact hs1_hdr hdrQHi (by decide) (by decide)
      · exact hs1_hdr hdrQHi (by decide) (by decide)
    rw [hev, hw_p, hvb_p, hil_p, hql_p, hih_p, hqh_p]
  have hfr_sp_raw : ((Memory.spec 0).clientState s_pre
      (setSlotIoProg (base + hdrPBase0, io_sp.toCtx))).frontier = s.frontier :=
    runClient_frontier_setSlotIoProg _ s_pre
  have hfrm_sp := setSlotIoProg_frame (base + hdrPBase0) io_sp.toCtx
  have hvals_sp := setSlotIoProg_mem_vals (base + hdrPBase0) io_sp s_pre
  dsimp only at hvals_sp
  obtain ⟨s_sp, hs_sp_def⟩ : ∃ s_sp,
      (Memory.spec 0).clientState s_pre (setSlotIoProg (base + hdrPBase0, io_sp.toCtx)) = s_sp :=
    ⟨_, rfl⟩
  rw [hs_sp_def] at hs_sp_eq hfr_sp_raw hvals_sp
  have hfr_sp : s_sp.frontier = s.frontier := hfr_sp_raw
  have hs_sp_out : ∀ a, ¬(base + hdrPBase0 + 48 ≤ a ∧ a < base + hdrPBase0 + 61) →
      s_sp.mem a = s_pre.mem a := fun a ha => hs_sp_def ▸ hfrm_sp.mem_outside s_pre a ha
  have hs_tick_eq : s_tick =
      { mem := Function.update s_sp.mem (base + hdrPhase) 10, frontier := s.frontier } := by
    rw [hs1_fr] at hst_fu
    rw [hst_bg, hst_tu, hst_fu]
    change ({ mem := Function.update ((Memory.spec 0).clientState s_pre
                (setSplitSlotIoProg ((base, base + hdrPBase0), nLive))).mem (base + hdrPhase) 10
              frontier := _ } : Memory.State) = _
    rw [hs_sp_eq, hfr_sp]
  have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
  have hout_hdr : ∀ off < 48, off ≠ hdrPhase → off ≠ hdrSplit → off ≠ hdrQLo →
      off ≠ hdrItemLo → off ≠ hdrUnpermDone →
      s_tick.mem (base + off) = s.mem (base + off) :=
    fun off hoff hph hsp hql hil hu => by
      rw [hs_tick_eq]; dsimp only
      rw [Function.update_of_ne (base_add_ne hph),
        hs_sp_out (base + off)
          (by dsimp only [hdrPBase0]; clear *- hoff; omega)]
      dsimp only [s_pre, m_sm]
      rw [Function.update_of_ne (base_add_ne hsp), Function.update_of_ne (base_add_ne hql),
        Function.update_of_ne (base_add_ne hil)]
      split_ifs
      · iterate 4 rw [Function.update_of_ne
          (by dsimp only [hdrSmallMeta0, hdrPBase0]; clear *- hoff; omega)]
        exact hs1_hdr off hoff hu
      · exact hs1_hdr off hoff hu
  have hph_t : s_tick.mem (base + hdrPhase) = 10 := by
    rw [hs_tick_eq]; exact Function.update_self ..
  have hsp_t : s_tick.mem (base + hdrSplit) = 0 := by
    rw [hs_tick_eq]; dsimp only
    rw [Function.update_of_ne (base_add_ne (by decide)),
      hs_sp_out (base + hdrSplit) (by dsimp only [hdrPBase0, hdrSplit]; omega)]
    exact Function.update_self ..
  have hqL_t : s_tick.mem (base + hdrQLo) = qLo' := by
    rw [hs_tick_eq]; dsimp only
    rw [Function.update_of_ne (base_add_ne (by decide)),
      hs_sp_out (base + hdrQLo) (by dsimp only [hdrPBase0, hdrQLo]; omega)]
    dsimp only [s_pre]
    rw [Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
  have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo' := by
    rw [hs_tick_eq]; dsimp only
    rw [Function.update_of_ne (base_add_ne (by decide)),
      hs_sp_out (base + hdrItemLo)
        (by dsimp only [hdrPBase0, hdrItemLo]; omega)]
    dsimp only [s_pre]
    iterate 2 rw [Function.update_of_ne (base_add_ne (by decide))]
    exact Function.update_self ..
  have hst_t : s_tick.mem (base + hdrStage) = stg :=
    hout_hdr hdrStage (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
    hout_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hnD_t : s_tick.mem (base + hdrNDst) = nDst :=
    hout_hdr hdrNDst (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
    hout_hdr hdrMSrc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
    hout_hdr hdrMDst (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpad_t : s_tick.mem (base + hdrPad) = pad :=
    hout_hdr hdrPad (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
    hout_hdr hdrItemHi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
    hout_hdr hdrQHi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs_ge192 : ∀ a, base + 192 ≤ a → s_tick.mem a = s1.mem a := fun a ha => by
    rw [hs_tick_eq]; dsimp only
    rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- ha; omega),
      hs_sp_out a (by dsimp only [hdrPBase0]; clear *- ha; omega)]
    dsimp only [s_pre, m_sm]
    iterate 3 rw [Function.update_of_ne
      (by dsimp only [hdrItemLo, hdrQLo, hdrSplit]; clear *- ha; omega)]
    split_ifs
    · iterate 4 rw [Function.update_of_ne
        (by dsimp only [hdrSmallMeta0, hdrPBase0]; clear *- ha; omega)]
    · rfl
  have hqLo'_le_qHi : qLo' ≤ qHi := by
    dsimp only [qLo', qHi] at hqHi_eq ⊢; rw [hqHi_eq]; exact le_max_right _ _
  have hqLo'_w : qLo' ≤ w := hqLo'_le_qHi.trans hqHi_w
  have hibLo'_le_ibHi : ibLo' + 4 ≤ ibHi := by
    dsimp only [ibLo']; rw [hibHi_eq]
    by_cases hdz : nDst = 0
    · rw [ite_eq_left hdz]
      have hm0 : mDst = 0 := by
        rw [hmDst_eq, hdz]; unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
      rw [hm0]; omega
    · rw [ite_eq_right hdz]; omega
  have hv_sp_hi : io_sp.Valid w hiFr := by
    unfold SlotIoLayout.Valid; dsimp only [io_sp, splitSlotIo]
    simp only [↓reduceIte, one_ne_zero]
    exact ⟨hw_pos, trivial, hqLo'_w, hvb_w, lt_of_le_of_lt hlive_le hUw,
      hqLo'_le_qHi, hqHi_w, by dsimp only [hdrSplit, ibLo']; omega,
      by clear *- hibLo'_le_ibHi; omega, le_rfl⟩
  have hns_d1 : s1.mem (dualMbDst base s.mem + 1) = nLive := by
    rw [hsl_s1.mem_nSide_eq, ← dom_toDictState_card, hdict_d]
  have hhi_quot_s1 : ∀ idx < nLive,
      pairQuotAt ibHi qHi vB w s1.mem idx < 2 ^ qLo' := fun idx hidx => by
    have hb := (hsl_s1.slot_pair_bounds (hns_d1.symm ▸ hidx)).1
    rw [hcap_d] at hb
    simpa only [io_dir, directSlotIo, slotIoPairAt, arenaPairAt, ↓reduceIte] using hb
  have hhi_quot_t : SplitHiQuotBounded io_sp nLive s_tick.mem := by
    intro idx _ hidx
    dsimp only [io_sp, splitSlotIo]
    have hq_eq : pairQuotAt ibHi qHi vB w s_tick.mem idx =
        pairQuotAt ibHi qHi vB w s1.mem idx := by
      unfold pairQuotAt readBitSlice; dsimp only
      rw [hs_ge192 _ (by clear *- hibHi_ge; omega),
        hs_ge192 _ (by clear *- hibHi_ge; omega)]
    rw [hq_eq]; exact hhi_quot_s1 idx hidx
  have hpair_sp : ∀ p < nLive,
      slotIoPairAt io_sp s_tick.mem p = slotIoPairAt io_dir s1.mem p := fun p hp => by
    have hq_eq : pairQuotAt ibHi qHi vB w s_tick.mem p = pairQuotAt ibHi qHi vB w s1.mem p := by
      unfold pairQuotAt readBitSlice; dsimp only
      rw [hs_ge192 _ (by clear *- hibHi_ge; omega),
        hs_ge192 _ (by clear *- hibHi_ge; omega)]
    have hv_eq : pairValAt ibHi qHi vB w s_tick.mem p = pairValAt ibHi qHi vB w s1.mem p := by
      unfold pairValAt readBitSlice; dsimp only
      rw [hs_ge192 _ (by clear *- hibHi_ge; omega),
        hs_ge192 _ (by clear *- hibHi_ge; omega)]
    unfold slotIoPairAt; dsimp only [io_sp, splitSlotIo, io_dir, directSlotIo,
      SlotIoLayout.splitCfg, arenaPairAt]
    simp only [↓reduceIte, one_ne_zero]
    rw [hsp_t]
    unfold splitPairRead; dsimp only
    rw [ite_eq_right (Nat.not_lt_zero p), hq_eq, hv_eq, Nat.mod_eq_of_lt (hhi_quot_s1 p hp)]
  have hvals_t : ∀ j < 13, s_tick.mem (base + hdrPBase0 + (48 + j)) =
      s_sp.mem (base + hdrPBase0 + (48 + j)) := fun j _ => by
    rw [hs_tick_eq]; dsimp only
    exact Function.update_of_ne (by dsimp only [hdrPBase0, hdrPhase]; omega) _ _
  have hp_io_t :
      s_tick.mem (base + hdrPBase0 + 48) = io_sp.usePaged ∧
      s_tick.mem (base + hdrPBase0 + 49) = io_sp.sideBit ∧
      s_tick.mem (base + hdrPBase0 + 50) = io_sp.pgL.metaBase ∧
      s_tick.mem (base + hdrPBase0 + 51) = io_sp.pgL.offDir ∧
      s_tick.mem (base + hdrPBase0 + 52) = io_sp.pgL.offTail ∧
      s_tick.mem (base + hdrPBase0 + 53) = io_sp.pgL.ptrB ∧
      s_tick.mem (base + hdrPBase0 + 54) = io_sp.pgL.w ∧
      s_tick.mem (base + hdrPBase0 + 55) = io_sp.pgL.pgB ∧
      s_tick.mem (base + hdrPBase0 + 56) = io_sp.pgL.maxPages ∧
      s_tick.mem (base + hdrPBase0 + 57) = io_sp.pgL.itemBase ∧
      s_tick.mem (base + hdrPBase0 + 58) = io_sp.pgL.qBits ∧
      s_tick.mem (base + hdrPBase0 + 59) = io_sp.pgL.vBits ∧
      s_tick.mem (base + hdrPBase0 + 60) = io_sp.pgL.nCap :=
    ⟨(hvals_t 0 (by decide)).trans hvals_sp.1,
     (hvals_t 1 (by decide)).trans hvals_sp.2.1,
     (hvals_t 2 (by decide)).trans hvals_sp.2.2.1,
     (hvals_t 3 (by decide)).trans hvals_sp.2.2.2.1,
     (hvals_t 4 (by decide)).trans hvals_sp.2.2.2.2.1,
     (hvals_t 5 (by decide)).trans hvals_sp.2.2.2.2.2.1,
     (hvals_t 6 (by decide)).trans hvals_sp.2.2.2.2.2.2.1,
     (hvals_t 7 (by decide)).trans hvals_sp.2.2.2.2.2.2.2.1,
     (hvals_t 8 (by decide)).trans hvals_sp.2.2.2.2.2.2.2.2.1,
     (hvals_t 9 (by decide)).trans hvals_sp.2.2.2.2.2.2.2.2.2.1,
     (hvals_t 10 (by decide)).trans hvals_sp.2.2.2.2.2.2.2.2.2.2.1,
     (hvals_t 11 (by decide)).trans hvals_sp.2.2.2.2.2.2.2.2.2.2.2.1,
     (hvals_t 12 (by decide)).trans hvals_sp.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hsl_dst_hi : EpochSlotInv c U V w hiFr (base + hdrPBase0)
      (if nDst = 0 then base + hdrSmallMeta0 else base + 192) io_sp 0 false
      L.slotDst s_tick.mem := by
    by_cases hdz : nDst = 0
    · -- `nDst = 0` (`stg = 0`): small slot initialized in `hdrSmallMeta0` + `hdrPBase0`
      have hst0 : stg = 0 := (hsched.nDst_zero hdz).2.1
      rw [ite_eq_left hdz]
      have hcap0 : L.slotDst.nCap = 0 := hcap_d.trans hdz
      have hraw := hsl_s1; unfold EpochSlotInv at hraw; rw [ite_eq_left hcap0] at hraw
      have href1 := hraw.2.2.2.2.2.2.2.2
      rw [hns_d1] at href1
      have hsm0_0 : s_tick.mem (base + hdrSmallMeta0) = 0 := by
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)),
          hs_sp_out (base + hdrSmallMeta0)
            (by dsimp only [hdrPBase0, hdrSmallMeta0]; omega)]
        dsimp only [s_pre, m_sm]; rw [ite_eq_left hst0]
        iterate 6 rw [Function.update_of_ne
          (by dsimp only [hdrItemLo, hdrQLo, hdrSplit, hdrSmallMeta0, hdrPBase0]; omega)]
        exact Function.update_self ..
      have hsm0_1 : s_tick.mem (base + hdrSmallMeta0 + 1) = nLive := by
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne (by dsimp only [hdrSmallMeta0, hdrPhase]; omega),
          hs_sp_out (base + hdrSmallMeta0 + 1)
            (by dsimp only [hdrPBase0, hdrSmallMeta0]; omega)]
        dsimp only [s_pre, m_sm]; rw [ite_eq_left hst0]
        iterate 5 rw [Function.update_of_ne
          (by dsimp only [hdrItemLo, hdrQLo, hdrSplit, hdrSmallMeta0, hdrPBase0]; omega)]
        exact Function.update_self ..
      have hp0_0 : s_tick.mem (base + hdrPBase0) = 0 := by
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)),
          hs_sp_out (base + hdrPBase0) (by omega)]
        dsimp only [s_pre, m_sm]; rw [ite_eq_left hst0]
        iterate 4 rw [Function.update_of_ne
          (by dsimp only [hdrItemLo, hdrQLo, hdrSplit, hdrSmallMeta0, hdrPBase0]; omega)]
        exact Function.update_self ..
      have hp0_1 : s_tick.mem (base + hdrPBase0 + 1) = base + hdrSmallMeta0 := by
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne (by dsimp only [hdrPBase0, hdrPhase]; omega),
          hs_sp_out (base + hdrPBase0 + 1) (by omega)]
        dsimp only [s_pre, m_sm]; rw [ite_eq_left hst0]
        iterate 3 rw [Function.update_of_ne
          (by dsimp only [hdrItemLo, hdrQLo, hdrSplit, hdrSmallMeta0, hdrPBase0]; omega)]
        exact Function.update_self ..
      unfold EpochSlotInv; rw [ite_eq_left hcap0]
      refine ⟨by clear *- hw11; omega,
        by dsimp only [hdrPBase0, hiFr]; clear *- hibHi_ge; omega,
        { io_valid := hv_sp_hi
          w_eq := rfl
          qBits_eq := by dsimp only [io_sp, splitSlotIo, qLo']; rw [ite_eq_left hdz]
          vBits_eq := rfl
          hdr_frontier := by dsimp only [hdrSmallMeta0, hiFr]; clear *- hibHi_ge; omega
          disjoint_hdr := fun addr hmb hia => by
            unfold SlotIoLayout.OwnsAddr at hia
            dsimp only [io_sp, splitSlotIo, hdrSmallMeta0, hdrSplit, ibLo'] at hmb hia
            simp only [↓reduceIte, one_ne_zero] at hia
            clear *- hmb hia hibHi_ge; omega },
        ⟨hp0_0, hp0_1, hp_io_t⟩,
        fun a h1 h2 ha => by
          rcases ha with rfl | rfl | hia
          · dsimp only [hdrPBase0, hdrSmallMeta0] at h1 h2; omega
          · dsimp only [hdrPBase0, hdrSmallMeta0] at h1 h2; omega
          · unfold SlotIoLayout.OwnsAddr at hia
            dsimp only [io_sp, splitSlotIo, hdrPBase0, hdrSplit, ibLo'] at h1 h2 hia
            simp only [↓reduceIte, one_ne_zero] at hia
            clear *- h1 h2 hia hibHi_ge; omega,
        ⟨hsm0_0, by rw [hsm0_1]; exact le_rfl,
          by
            unfold SlotIoLayout.StateInv; dsimp only [io_sp, splitSlotIo]
            simp only [↓reduceIte, one_ne_zero]
            rw [hsm0_1]; exact ⟨le_rfl, Or.inr hqHi_w⟩,
          by rw [hsm0_1]; exact href1.congr (fun _ _ => rfl) hpair_sp⟩⟩
    · -- `nDst > 0`: since `¬(stg = 0 ∧ 0 < nDst)` and `stg ≤ 1`, `stg = 1`!
      have hd_pos := Nat.pos_of_ne_zero hdz
      have hst1 : stg = 1 := by
        by_cases hs0 : stg = 0
        · exact absurd ⟨hs0, hd_pos⟩ hgoB
        · clear *- hstg_le hs0; omega
      rw [ite_eq_right hdz]
      have hpD_eq0 : dualPDst base s.mem = base + hdrPBase0 := by
        unfold dualPDst; dsimp only [stg] at hst1
        rw [hp9, ite_eq_left (by decide : 9 < 10), ite_eq_right (by rw [hst1]; decide)]
      have hmbD_eq0 : dualMbDst base s.mem = base + 192 := by
        unfold dualMbDst; dsimp only [stg, nDst] at hst1 hdz
        rw [hp9, ite_eq_left (by decide : 9 < 10), ite_eq_right hdz,
          ite_eq_right (by rw [hst1]; decide)]
      rw [hpD_eq0, hmbD_eq0] at hsl_s1
      rw [hmbD_eq0] at hns_d1
      have hv_sp_fr : io_sp.Valid w s.frontier := by
        unfold SlotIoLayout.Valid; dsimp only [io_sp, splitSlotIo]
        simp only [↓reduceIte, one_ne_zero]
        exact ⟨hw_pos, trivial, hqLo'_w, hvb_w, lt_of_le_of_lt hlive_le hUw,
          hqLo'_le_qHi, hqHi_w, by dsimp only [hdrSplit, ibLo']; omega,
          by clear *- hibLo'_le_ibHi; omega, hfr_hi_lo⟩
      have hsl_fr := hsl_s1.set_slotIo (slack₂ := 0) (io₂ := io_sp) hv_sp_fr rfl
        ⟨fun h0 => absurd h0 (hcap_d ▸ hdz),
         fun _ => by
          rw [hcap_d]; dsimp only [io_sp, splitSlotIo, qLo']; rw [ite_eq_right hdz]⟩
        rfl
        (fun k hk => by
          have hk_out :
              ¬(base + hdrPBase0 + 48 ≤ base + hdrPBase0 + k ∧
                base + hdrPBase0 + k < base + hdrPBase0 + 61) := by
            rcases hk with hlt | rfl | rfl <;> omega
          rw [hs_tick_eq]; dsimp only
          rw [Function.update_of_ne (by dsimp only [hdrPBase0, hdrPhase]; omega),
            hs_sp_out (base + hdrPBase0 + k) hk_out]
          dsimp only [s_pre, m_sm]
          rw [ite_eq_right (by rw [hst1]; decide)]
          iterate 3 rw [Function.update_of_ne
            (by dsimp only [hdrPBase0, hdrItemLo, hdrQLo, hdrSplit]; omega)])
        hp_io_t
        (fun a h1 h2 hia => by
          unfold SlotIoLayout.OwnsAddr at hia
          dsimp only [io_sp, splitSlotIo, hdrPBase0, hdrSplit, ibLo'] at h1 h2 hia
          simp only [↓reduceIte, one_ne_zero] at hia
          clear *- h1 h2 hia hibHi_ge; omega)
        (fun a ha hia => by
          rw [hcap_d] at ha
          unfold slotOwnsNonPageMeta at ha
          simp only [hdz, ↓reduceIte] at ha
          unfold SlotIoLayout.OwnsAddr at hia
          dsimp only [io_sp, splitSlotIo, hdrSplit, ibLo'] at hia
          simp only [↓reduceIte, one_ne_zero] at hia
          have hth_d : whpThreshold c ≤ nDst := (hsched.nDst_bounds.resolve_left hdz).1
          have hod_le : offPageDir c w nDst ≤ mDst :=
            (epochMeta_offsets_le (w := w) hth_d).2.2.2.trans hmDst_eq.symm.le
          have h32 : 32 ≤ offPageDir c w nDst :=
            (epochMeta_offsets_le (w := w) hth_d).1.trans
              ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
                (epochMeta_offsets_le (w := w) hth_d).2.2.1)
          rcases ha with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
            (clear *- g1 g2 hia hod_le h32 hibLo'_le_ibHi; omega))
        (fun a ha => hs_ge192 a (by
          rw [hcap_d] at ha; unfold slotOwnsNonPageMeta at ha
          simp only [hdz, ↓reduceIte] at ha
          rcases ha with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;> (clear *- g1; omega)))
        (by
          unfold SlotIoLayout.StateInv; dsimp only [io_sp, splitSlotIo]
          simp only [↓reduceIte, one_ne_zero]
          rw [hns_d1]; exact ⟨le_rfl, Or.inr hqHi_w⟩)
        (fun p hp => hpair_sp p (hns_d1 ▸ hp))
      exact hsl_fr.at_exact_frontier (fr₂ := hiFr)
        (by dsimp only [hdrPBase0, hiFr]; clear *- hibHi_ge; omega)
        (by
          rw [hcap_d, ite_eq_right hdz, ← hmDst_eq]
          dsimp only [hiFr]; clear *- hibLo'_le_ibHi; omega)
        (by dsimp only [io_sp, splitSlotIo, hiFr]; exact le_rfl)
  set L' : DualLatent c U V := { L with elapsed := L.elapsed + 1 }
  refine ⟨hpre_bg, hfr_tick, hwf_tick,
    fun addr hlt_b => by
      rw [hs_tick_eq]; dsimp only
      rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- hlt_b; omega),
        hs_sp_out addr (by dsimp only [hdrPBase0]; clear *- hlt_b; omega)]
      dsimp only [s_pre, m_sm]
      iterate 3 rw [Function.update_of_ne
        (by dsimp only [hdrItemLo, hdrQLo, hdrSplit]; clear *- hlt_b; omega)]
      split_ifs
      · iterate 4 rw [Function.update_of_ne
          (by dsimp only [hdrSmallMeta0, hdrPBase0]; clear *- hlt_b; omega)]
        exact hs1_lt_b addr hlt_b
      · exact hs1_lt_b addr hlt_b, ?_⟩
  rw [ite_eq_left (by clear *- hp9; omega)]
  refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
    (fun ⟨_, h4⟩ => by rw [hph_t] at h4; cases h4) rfl rfl, ?_, fun _ _ => hmc_all⟩
  refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
  · rw [hnS_t, hph_t, ite_eq_right (by decide : 10 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
  · rw [hph_t, ite_eq_right (by decide : ¬(10 < 2)), ite_eq_right (by decide : 10 ≠ 2),
      ite_eq_left (by decide : 10 ≤ 10), hibH_t, hqH_t, hfr_tick]
    refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
    exact
      { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
        wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, hwf_tick.2⟩
        base_fr := by dsimp only [hiFr]; clear *- hibHi_ge; omega
        hdr := rootStaticHeader_congr hhdr fun off hoff =>
          hout_hdr off (by clear *- hoff; omega)
            (by dsimp only [hdrPhase]; clear *- hoff; omega)
            (by dsimp only [hdrSplit]; clear *- hoff; omega)
            (by dsimp only [hdrQLo]; clear *- hoff; omega)
            (by dsimp only [hdrItemLo]; clear *- hoff; omega)
            (by dsimp only [hdrUnpermDone]; clear *- hoff; omega)
        live_eq := (hout_hdr hdrLive (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans hlive_eq
        live_le := hlive_le
        ph_le := by dsimp only; rw [hph_t]; decide
        stg_le := by dsimp only; rw [hst_t]; exact hstg_le
        mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
        cache_src := by
          dsimp only; rw [hnS_t]
          exact hostCacheValid_congr_mem hcache_s fun k hk => by
            rw [Nat.add_assoc]
            exact hout_hdr (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrSplit]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrQLo]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrItemLo]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrUnpermDone]; clear *- hk; omega)
        nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
        sched := by
          dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
          refine
            { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
              nDst_zero := fun hz => by
                dsimp only at hz ⊢
                obtain ⟨h1', h2', _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                rw [hnS_t, hst_t, hph_t]; exact ⟨h1', h2', by decide, by decide, by decide⟩
              stg_one := fun hs_o => by
                dsimp only at hs_o ⊢; rw [hnD_t, hph_t]
                exact ⟨(hsched.stg_one (hst_t.symm.trans hs_o)).1, by decide, by decide⟩
              post_trig := by dsimp only; rw [hnS_t]; exact hsched.post_trig
              trig_cap := by dsimp only; rw [hnS_t, hnD_t]; exact hsched.trig_cap
              drift_hi := by dsimp only [L']; simpa using hd_hi'
              drift_lo := by dsimp only [L']; simpa using hd_lo'
              ibLo_eq := by
                dsimp only; rw [hibL_t, hph_t, ite_eq_right (by decide : ¬(10 < 10)), hmD_t]
              qLo_eq := by
                dsimp only; rw [hqL_t, hph_t, ite_eq_right (by decide : ¬(10 < 10)), hnD_t]
              ph1 := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
              ge2 := fun _ => by
                dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                    rw [Nat.add_assoc]
                    exact hout_hdr (hdrDstOd + k)
                      (by dsimp only [hdrDstOd]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrSplit]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrQLo]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrItemLo]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrUnpermDone]; clear *- hk; omega)
                · obtain ⟨hl, he, hp⟩ := hd_logs hd
                  exact ⟨(hout_hdr hdrLogN (by decide) (by decide) (by decide)
                      (by decide) (by decide) (by decide)).trans hl,
                    (hout_hdr hdrEll (by decide) (by decide) (by decide)
                      (by decide) (by decide) (by decide)).trans he,
                    (hout_hdr hdrPgB (by decide) (by decide) (by decide)
                      (by decide) (by decide) (by decide)).trans hp⟩
              ph2 := fun hp2 => absurd (hph_t.symm.trans hp2) (by decide)
              ph3_10 := fun _ => by
                dsimp only [hiFr]; rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
              ph11 := fun hp11 => absurd (hph_t.symm.trans hp11) (by decide)
              budget := by
                dsimp only [L']
                rw [hnS_t, hst_t, hph_t, hsp_t, hnD_t, hmD_t]
                unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                dsimp only [stg, nSrc, nDst, mDst, rem, nLive] at hrem_eq1 hb_tot hnL_2R ⊢
                simp only [show s.mem (base + hdrPhase) = 9 from hp9, hrem_eq1,
                  Bool.false_eq_true, Nat.sub_zero, Nat.reduceEqDiff, Nat.reduceLeDiff,
                  and_self, and_false, ↓reduceIte] at hb_tot ⊢
                unfold maxTailPhasesBudget at hb_tot
                have hdiv_nL : nLive / 1023 ≤
                    (2 * max (whpThreshold c) nSrc + 512) / 1023 :=
                  Nat.div_le_div_right (by clear *- hnL_2R; omega)
                have hstg_nonneg : 0 ≤ (if stg = 0 then maxStageBudget
                    (max (whpThreshold c) nSrc) else 0) := Nat.zero_le _
                dsimp only [nLive, nSrc, stg] at hdiv_nL hstg_nonneg ⊢
                generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef
                  at hb_tot hdiv_nL hstg_nonneg ⊢
                generalize (if s.mem (base + hdrStage) = 0 then maxStageBudget nRef else 0) =
                  msb at hb_tot hstg_nonneg
                refine ⟨?_, ?_, ?_⟩ <;> (clear *- hb_tot hdiv_nL hstg_nonneg; omega) }
        pad_fits := by
          dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 10 ≠ 0)]
          simpa only [hp9, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
        ph1_inv := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
        ph3_inv := fun hp3 => absurd (hph_t.symm.trans hp3) (by decide)
        ph4_inv := fun hp4 => absurd (hph_t.symm.trans hp4) (by decide)
        pDst_pre := fun ⟨_, hp5⟩ => absurd (hph_t ▸ hp5) (by decide)
        ph5_inv := fun hp5 => absurd (hph_t.symm.trans hp5) (by decide)
        ph6_inv := fun hp6 => absurd (hph_t.symm.trans hp6) (by decide)
        ph7_inv := fun hp7 => absurd (hph_t.symm.trans hp7) (by decide)
        ph8_inv := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
        ph9_inv := fun hp9' => absurd (hph_t.symm.trans hp9') (by decide)
        ph10_inv := fun _ => by
          dsimp only; rw [hsp_t, hibL_t, hqL_t, hibH_t, hqH_t]
          exact ⟨Nat.zero_le _, hhi_quot_t⟩
        sl_le7 := fun hp7 => absurd (hph_t ▸ hp7) (by decide)
        sl_67 := fun h67 => by
          dsimp only at h67
          rcases h67 with h6 | h7 <;> exact absurd (hph_t.symm.trans ‹_›) (by decide)
        sl_8 := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
        sl_ge9 := fun _ => by
          dsimp only [L']
          have hpD10 : dualPDst base s_tick.mem = base + hdrPBase0 := by
            unfold dualPDst; rw [hph_t, ite_eq_right (by decide : ¬(10 < 10))]
          have hmbD10 : dualMbDst base s_tick.mem =
              (if nDst = 0 then base + hdrSmallMeta0 else base + 192) := by
            unfold dualMbDst; rw [hph_t, ite_eq_right (by decide : ¬(10 < 10)), hnD_t]
          have hio10 : activeDstIo c w vB base stg 10 nSrc nDst pad ibLo' qLo' ibHi qHi nLive
              (s_tick.mem (base + hdrUnpermDone)) = io_sp := by
            unfold activeDstIo; simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]; rfl
          rw [hnD_t, hst_t, hph_t, hnS_t, hpad_t, hibL_t, hqL_t, hibH_t, hqH_t,
            hpD10, hmbD10, hio10]
          simp only [Bool.false_eq_true, false_and, ↓reduceIte, add_zero]
          exact ⟨hcap_d, hdict_d, hsl_dst_hi, fun hd_pos => by
            have he := hevs_d hd_pos; simp only [↓reduceIte] at he; exact he⟩ }

/-- Phase `9` (`unperm`) background tick specification (`9 → 9`, `9 → 4` Stage B, and `9 → 10`). -/
theorem tickPhase9_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp9 : s.mem (base + hdrPhase) = 9) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  by_cases h1 : 1 < s.mem (base + hdrRem)
  · exact tickPhase9_stay_spec h hp9 h1
  · by_cases hgoB : s.mem (base + hdrStage) = 0 ∧ 0 < s.mem (base + hdrNDst)
    · exact tickPhase9_goB_spec h hp9 h1 hgoB
    · exact tickPhase9_slide_spec h hp9 h1 hgoB
end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
