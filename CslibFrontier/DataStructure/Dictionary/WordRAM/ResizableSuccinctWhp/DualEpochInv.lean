/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvTickC

/-!
# Full Single-Operation Dual-Epoch Invariant Stack (`DualEpochInv`)

Completes the deterministic and post-randomization `Memory.Prog` invariant stack for the
deamortized 12-phase dual-epoch resizable succinct worst-case WHP dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]):

1. **Below-frontier congruence & `shrinkCode` `clear` (`DualStateInv.congr_lt_frontier`,
   `DualStateInv.clear_above`):**
   Every word read by a resting `DualStateInv` state lies strictly below `s.frontier`, so clearing
   reclaimed trailing words `[fr', s.frontier)` via `shrinkCode` preserves `DualStateInv`.
2. **Post-`randFill` activation (`finishRandFillProg_spec`):**
   At `ph = 5` with `cur = offBktMeta c w nDst`, `finishRandFillProg` masks the two Stage-1 odd
   multipliers modulo `2 ^ (redWidthWhp U - 1)`, sets `pDst`'s direct `SlotIoCtx` at `(ibHi, qHi)`,
   initializes `L_rf.slotDst` with `extractEpochSeeds` via `epochInitZeroedProg`, and enters
   `DualPreShrinkInv` at `ph = 6`.
3. **Post-shrink & rebuild-completion (`calcPostShrinkProg_spec`, `postRandShrinkProg_spec`):**
   Computes `k_sh ≤ bulkBatchWhp`, runs `finishShrinkPostProg` at `11 → 0` (`diffLo ≤ bulkBatchWhp`)
   promoting `L.slotDst` to `L_fin.slotSrc` under `DualIdleSafe`, and restores resting
   `DualStateInv` at `{ mem := clear s_ps.mem (s_pre.frontier - k_sh) k_sh, frontier :=
   s_pre.frontier - k_sh }`.
4. **Unified `stepOpProg` specifications (`stepOpProg_query_spec`, `stepOpProg_mutate_spec`):**
   Combines `userQueryProg_spec`, `prepGrow_userMutate_spec`, and `bgTickProg_spec` into top-level
   `StepOpPre` + transition theorems ready for `DualEpochExec`.

## Main results

* `DualStateInv.congr_lt_frontier`, `DualStateInv.clear_above`
* `finishRandFillProg_spec`
* `calcPostShrinkProg_spec`, `postRandShrinkProg_spec`
* `stepOpProg_query_spec`, `stepOpProg_mutate_spec`

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

/-! ## Section 1: Below-Frontier Congruence and `clear` Preservation (`DualStateInv.clear_above`) -/

private theorem slotIoOwnsAddr_lt_frontier {io : SlotIoLayout} {w fr addr : ℕ}
    (hv : io.Valid w fr)
    (hlo : io.usePaged = 0 → io.sideBit ≠ 0 →
      io.pgL.offDir + pairStreamWords io.pgL.nCap io.pgL.qBits io.pgL.vBits io.pgL.w ≤ fr)
    (ha : io.OwnsAddr addr) :
    addr < fr := by
  unfold SlotIoLayout.Valid at hv
  unfold SlotIoLayout.OwnsAddr at ha
  by_cases hup : io.usePaged = 0
  · rw [ite_eq_left hup] at hv ha
    obtain ⟨_, _, _, _, _, hs_v⟩ := hv
    by_cases hsb : io.sideBit = 0
    · rw [ite_eq_left hsb] at hs_v ha
      unfold PageArenaLayout.OwnsItemAddr at ha
      clear *- hs_v ha; omega
    · rw [ite_eq_right hsb] at hs_v ha
      have hlo_fr := hlo hup hsb
      have hhi_fr := hs_v.2.2.2.2
      have hm_lt := hs_v.2.2.1
      have hd_lt := hs_v.2.2.2.1
      rcases ha with rfl | ⟨_, hlt⟩ | ⟨_, hlt⟩
      · clear *- hm_lt hd_lt hhi_fr; omega
      · exact lt_of_lt_of_le hlt hlo_fr
      · exact lt_of_lt_of_le hlt hhi_fr
  · rw [ite_eq_right hup] at hv ha
    unfold PageArenaLayout.Valid at hv
    unfold PageArenaLayout.OwnsAddr PageArenaLayout.OwnsMetaAddr PageArenaLayout.OwnsItemAddr at ha
    have ho1 := hv.2.2.2.2.2.2.2.2.2.2.2.1
    have ho2 := hv.2.2.2.2.2.2.2.2.2.2.2.2.1
    have ho3 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have ho4 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rcases ha with (⟨_, hlt⟩ | ⟨_, hlt⟩ | ⟨_, hlt⟩) | ⟨_, hlt⟩ <;>
      (clear *- ho1 ho2 ho3 ho4 hlt; omega)

private theorem EpochSlotInv.congr_lt_frontier {c U V w fr pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem₁ mem₂ : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem₁)
    (hlo : io.usePaged = 0 → io.sideBit ≠ 0 →
      io.pgL.offDir + pairStreamWords io.pgL.nCap io.pgL.qBits io.pgL.vBits io.pgL.w ≤ fr)
    (heq : ∀ a < fr, mem₂ a = mem₁ a) :
    EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem₂ := by
  have hv_io := h.io_valid
  have hp_fr : pBase + 64 ≤ fr := by
    unfold EpochSlotInv at h
    by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at h; exact h.2.1
    · rw [ite_eq_right h0] at h
      exact (h.1.pBase_lt_meta.trans (Nat.le_add_right _ _)).trans h.1.meta_frontier
  have hm_lt : ∀ a, slotOwnsNonPageMeta c w metaBase sl.nCap a → a < fr := by
    intro a ha
    unfold EpochSlotInv at h; unfold slotOwnsNonPageMeta at ha
    by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at h ha
      have hhf : metaBase + 2 ≤ fr := h.2.2.1.hdr_frontier
      rcases ha with ⟨_, hlt⟩ | ⟨hne, _⟩
      · clear *- hlt hhf; omega
      · exact absurd h0 hne
    · rw [ite_eq_right h0] at h ha
      have hmf := h.1.meta_frontier
      have hod_le : offPageDir c w sl.nCap ≤ epochMetaWordsWhp c w sl.nCap :=
        (epochMeta_offsets_le (w := w) h.1.thresh_le).2.2.2
      have h32_le : 32 ≤ offPageDir c w sl.nCap :=
        (epochMeta_offsets_le (w := w) h.1.thresh_le).1.trans
          ((epochMeta_offsets_le (w := w) h.1.thresh_le).2.1.trans
            (epochMeta_offsets_le (w := w) h.1.thresh_le).2.2.1)
      dsimp only at hmf
      rcases ha with ⟨_, hlt⟩ | ⟨_, _, hlt⟩ <;> (clear *- hlt hod_le h32_le hmf; omega)
  exact h.congr_mem
    (fun a _ h2 => heq a (lt_of_lt_of_le h2 hp_fr))
    (fun a ha => heq a (hm_lt a ha))
    (fun a ha => heq a (slotIoOwnsAddr_lt_frontier hv_io hlo ha))

/-- Resting `DualStateInv` depends only on memory words strictly below `fr`. -/
theorem DualStateInv.congr_lt_frontier {c U V w base fr : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {mem₁ mem₂ : ℕ → ℕ}
    (h : DualStateInv c U V w base s_dict L { mem := mem₁, frontier := fr })
    (heq : ∀ addr < fr, mem₂ addr = mem₁ addr)
    (hfits : ∀ addr, Fits w (mem₂ addr)) :
    DualStateInv c U V w base s_dict L { mem := mem₂, frontier := fr } := by
  have hw11 := h.hw11; have hb192 := h.base_fr
  have hw_pos : 0 < w := by clear *- hw11; omega
  have hoff_eq : ∀ off < 192, mem₂ (base + off) = mem₁ (base + off) :=
    fun off hoff => heq (base + off) (by dsimp only at hb192; clear *- hoff hb192; omega)
  set nLive := (Dictionary.dom s_dict).card
  set ph := mem₁ (base + hdrPhase)
  have hph_m2 : mem₂ (base + hdrPhase) = ph := hoff_eq hdrPhase (by decide)
  have hst_m2 : mem₂ (base + hdrStage) = mem₁ (base + hdrStage) := hoff_eq hdrStage (by decide)
  have hnS_m2 : mem₂ (base + hdrNSrc) = mem₁ (base + hdrNSrc) := hoff_eq hdrNSrc (by decide)
  have hnD_m2 : mem₂ (base + hdrNDst) = mem₁ (base + hdrNDst) := hoff_eq hdrNDst (by decide)
  have hmS_m2 : mem₂ (base + hdrMSrc) = mem₁ (base + hdrMSrc) := hoff_eq hdrMSrc (by decide)
  have hmD_m2 : mem₂ (base + hdrMDst) = mem₁ (base + hdrMDst) := hoff_eq hdrMDst (by decide)
  have hpad_m2 : mem₂ (base + hdrPad) = mem₁ (base + hdrPad) := hoff_eq hdrPad (by decide)
  have hibL_m2 : mem₂ (base + hdrItemLo) = mem₁ (base + hdrItemLo) := hoff_eq hdrItemLo (by decide)
  have hibH_m2 : mem₂ (base + hdrItemHi) = mem₁ (base + hdrItemHi) := hoff_eq hdrItemHi (by decide)
  have hqL_m2 : mem₂ (base + hdrQLo) = mem₁ (base + hdrQLo) := hoff_eq hdrQLo (by decide)
  have hqH_m2 : mem₂ (base + hdrQHi) = mem₁ (base + hdrQHi) := hoff_eq hdrQHi (by decide)
  have hud_m2 : mem₂ (base + hdrUnpermDone) = mem₁ (base + hdrUnpermDone) :=
    hoff_eq hdrUnpermDone (by decide)
  have hpS_eq : dualPSrc base mem₂ = dualPSrc base mem₁ := by unfold dualPSrc; rw [hst_m2]
  have hmbS_eq : dualMbSrc base mem₂ = dualMbSrc base mem₁ := by
    unfold dualMbSrc; rw [hst_m2, hnS_m2, hpad_m2]
  have hcapS_eq : dualCapSrc base mem₂ = dualCapSrc base mem₁ := by
    unfold dualCapSrc; rw [hst_m2, hnS_m2, hnD_m2]
  have hpD_eq : dualPDst base mem₂ = dualPDst base mem₁ := by
    unfold dualPDst; rw [hph_m2, hst_m2]
  have hmbD_eq : dualMbDst base mem₂ = dualMbDst base mem₁ := by
    unfold dualMbDst; rw [hph_m2, hnD_m2, hst_m2, hpad_m2]
  have hpgH_eq : dualPgHost c V w base nLive mem₂ = dualPgHost c V w base nLive mem₁ := by
    unfold dualPgHost dualNHost dualMbHost
    rw [hnD_m2, hnS_m2, hst_m2, hpad_m2, hibH_m2, hqH_m2]
  have hlo_le_hi : ∀ (hp3 : 3 ≤ ph) (hp10 : ph ≤ 10),
      mem₁ (base + hdrItemLo) + pairStreamWords nLive (mem₁ (base + hdrQLo)) (valBits V) w ≤ fr :=
    fun hp3 hp10 => by
      have hsched := h.sched; dsimp only at hsched
      rw [ite_eq_right (show ph ≠ 0 by clear *- hp3; omega)] at hsched
      have hfr_hi := (hsched.ph3_10 ⟨hp3, hp10⟩).1
      obtain ⟨hmD_e, hpad_e, _, _, hibH_e, hqH_e⟩ :=
        hsched.ge2 (show 2 ≤ ph by clear *- hp3; omega)
      have hibL_e := hsched.ibLo_eq
      have hqL_e := hsched.qLo_eq
      dsimp only at hfr_hi hmD_e hpad_e hibH_e hqH_e hibL_e hqL_e
      have hib_le : mem₁ (base + hdrItemLo) ≤ mem₁ (base + hdrItemHi) := by
        have hm1 : mem₁ (base + hdrMSrc) ≤ mem₁ (base + hdrPad) := by
          rw [hpad_e]; exact le_max_left _ _
        have hm2 : mem₁ (base + hdrMDst) ≤ mem₁ (base + hdrPad) := by
          rw [hpad_e]; exact le_max_right _ _
        by_cases hdz : mem₁ (base + hdrNDst) = 0
        · have hmD0 : mem₁ (base + hdrMDst) = 0 := by rw [hmD_e, hdz, epochMetaWordsWhp_zero_eq]
          rw [hibL_e, hibH_e, ite_eq_left hdz]
          split_ifs <;> (clear *- hm1 hmD0; omega)
        · rw [hibL_e, hibH_e, ite_eq_right hdz]
          split_ifs <;> (clear *- hm1 hm2; omega)
      have hq_le : mem₁ (base + hdrQLo) ≤ mem₁ (base + hdrQHi) := by
        rw [hqL_e, hqH_e]
        by_cases h10 : ph < 10
        · rw [ite_eq_left h10]; exact le_max_left _ _
        · rw [ite_eq_right h10]; exact le_max_right _ _
      exact (Nat.add_le_add hib_le (pairStreamWords_mono_q hq_le)).trans hfr_hi
  have hpg_meta_eq : 3 ≤ ph → ph ≤ 10 →
      extractPageUnperm (dualPgHost c V w base nLive mem₁) mem₂ =
        extractPageUnperm (dualPgHost c V w base nLive mem₁) mem₁ := fun hp3 hp10 => by
    have hv_pg := (dualPgHost_eval_valid h hp3 hp10).2.2.2.2.2.2.2.1
    dsimp only at hv_pg
    refine extractPageUnperm_congr
      (show 0 < (dualPgHost c V w base nLive mem₁).w from hw_pos) fun a ha => heq a ?_
    unfold PageArenaLayout.Valid at hv_pg
    unfold PageArenaLayout.OwnsMetaAddr at ha
    dsimp only [nLive] at ha
    have ho1 := hv_pg.2.2.2.2.2.2.2.2.2.2.2.1
    have ho2 := hv_pg.2.2.2.2.2.2.2.2.2.2.2.2.1
    have ho3 := hv_pg.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have ho4 := hv_pg.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rcases ha with ⟨_, hlt⟩ | ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> (clear *- ho1 ho2 ho3 ho4 hlt; omega)
  have hsplit_congr : ∀ (hp3 : 3 ≤ ph) (hp10 : ph ≤ 10),
      SplitHiQuotBounded
        (splitSlotIo w (valBits V) base (mem₁ (base + hdrItemLo)) (mem₁ (base + hdrQLo))
          (mem₁ (base + hdrItemHi)) (mem₁ (base + hdrQHi)) nLive) nLive mem₁ →
      SplitHiQuotBounded
        (splitSlotIo w (valBits V) base (mem₁ (base + hdrItemLo)) (mem₁ (base + hdrQLo))
          (mem₁ (base + hdrItemHi)) (mem₁ (base + hdrQHi)) nLive) nLive mem₂ :=
    fun hp3 hp10 hsh idx hlo_i hhi_i => by
      have hsp_m2 : mem₂ (base + hdrSplit) = mem₁ (base + hdrSplit) :=
        hoff_eq hdrSplit (by decide)
      dsimp only [splitSlotIo] at hlo_i ⊢
      rw [hsp_m2] at hlo_i
      have hsched := h.sched; dsimp only at hsched
      rw [ite_eq_right (show ph ≠ 0 by clear *- hp3; omega)] at hsched
      have hfr_hi := (hsched.ph3_10 ⟨hp3, hp10⟩).1
      dsimp only at hfr_hi
      have hq_eq :
          pairQuotAt (mem₁ (base + hdrItemHi)) (mem₁ (base + hdrQHi)) (valBits V) w mem₂ idx =
          pairQuotAt (mem₁ (base + hdrItemHi)) (mem₁ (base + hdrQHi)) (valBits V) w mem₁ idx := by
        have hq_lt := wOffQ_add_one_lt_pairStreamWords
          (n := nLive) (q_bits := mem₁ (base + hdrQHi)) (v_bits := valBits V) hw_pos hhi_i
        dsimp only [nLive] at hq_lt
        unfold pairQuotAt readBitSlice; dsimp only
        rw [heq _ (lt_of_lt_of_le (by clear *- hq_lt; omega) hfr_hi),
          heq _ (lt_of_lt_of_le (by clear *- hq_lt; omega) hfr_hi)]
      have hidx1 := hsh idx hlo_i hhi_i
      dsimp only [splitSlotIo] at hidx1
      rwa [hq_eq]
  have hsched₂ :
      if ({ mem := mem₂, frontier := fr } : Memory.State).mem (base + hdrPhase) = 0 then
        DualIdleSched false c U V w base nLive L { mem := mem₂, frontier := fr }
      else
        DualActiveSched false c U V w base nLive L { mem := mem₂, frontier := fr } := by
    have hsc := h.sched
    dsimp only at hsc ⊢
    simp only [hph_m2] at hsc ⊢
    by_cases hp0 : ph = 0
    · rw [ite_eq_left hp0] at hsc ⊢
      exact
        { stg_zero := hst_m2.trans hsc.stg_zero
          nDst_zero := hnD_m2.trans hsc.nDst_zero
          mDst_zero := hmD_m2.trans hsc.mDst_zero
          ibLo_eq := by dsimp only; rw [hibL_m2, hmS_m2]; exact hsc.ibLo_eq
          ibHi_eq := by dsimp only; rw [hibH_m2, hibL_m2]; exact hsc.ibHi_eq
          qLo_eq := by dsimp only; simp only [hqL_m2, hnS_m2]; exact hsc.qLo_eq
          qHi_eq := by dsimp only; rw [hqH_m2, hqL_m2]; exact hsc.qHi_eq
          elapsed_zero := hsc.elapsed_zero
          safe_fr := by
            dsimp only; rw [hnS_m2, hibL_m2, hqL_m2]; exact hsc.safe_fr
          ops_evs := by
            dsimp only; rw [hnS_m2, hoff_eq hdrEpochOps (by decide)]; exact hsc.ops_evs }
    · rw [ite_eq_right hp0] at hsc ⊢
      exact
        { nDst_bounds := by dsimp only; rw [hnD_m2]; exact hsc.nDst_bounds
          nDst_zero := by
            dsimp only; rw [hnD_m2, hnS_m2, hst_m2, hph_m2]; exact hsc.nDst_zero
          stg_one := by
            dsimp only; rw [hst_m2, hnD_m2, hph_m2]; exact hsc.stg_one
          post_trig := by dsimp only; rw [hnS_m2]; exact hsc.post_trig
          trig_cap := by dsimp only; rw [hnS_m2, hnD_m2]; exact hsc.trig_cap
          drift_hi := hsc.drift_hi
          drift_lo := hsc.drift_lo
          ibLo_eq := by
            dsimp only; simp only [hibL_m2, hph_m2, hmS_m2, hmD_m2]; exact hsc.ibLo_eq
          qLo_eq := by
            dsimp only; simp only [hqL_m2, hph_m2, hnS_m2, hnD_m2]; exact hsc.qLo_eq
          ph1 := by
            dsimp only
            rw [hph_m2, hst_m2, hnD_m2, hmD_m2, hibH_m2, hibL_m2, hqH_m2, hqL_m2]
            exact hsc.ph1
          ge2 := fun hge => by
            dsimp only at hge ⊢; rw [hph_m2] at hge
            obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hsc.ge2 hge
            dsimp only at g1 g2 g3 g4 g5 g6
            simp only [hmD_m2, hnD_m2, hpad_m2, hmS_m2, hibH_m2, hqH_m2, hnS_m2,
              hoff_eq hdrLogN (by decide), hoff_eq hdrEll (by decide),
              hoff_eq hdrPgB (by decide)]
            refine ⟨g1, g2, ?_, g4, g5, g6⟩
            exact hostCacheValid_congr_mem g3 fun k hk => by
              rw [Nat.add_assoc]
              exact hoff_eq (hdrDstOd + k) (by dsimp only [hdrDstOd]; clear *- hk; omega)
          ph2 := by
            dsimp only; rw [hph_m2, hst_m2, hibL_m2, hqL_m2, hibH_m2, hqH_m2]; exact hsc.ph2
          ph3_10 := by dsimp only; rw [hph_m2, hibH_m2, hqH_m2]; exact hsc.ph3_10
          ph11 := by dsimp only; rw [hph_m2, hibL_m2, hqL_m2, hibH_m2, hqH_m2]; exact hsc.ph11
          budget := by
            have hb := hsc.budget; dsimp only at hb ⊢
            simp only [hnS_m2, hpgH_eq, hibH_m2, hqH_m2, hoff_eq hdrSplit (by decide),
              hibL_m2, hqL_m2, hnD_m2, hst_m2, hph_m2, hoff_eq hdrLogSub (by decide),
              hoff_eq hdrLogK (by decide), hmD_m2, hoff_eq hdrCur (by decide),
              hoff_eq hdrRem (by decide)]
            exact hb }
  refine
    { hw11 := hw11
      U_pos := h.U_pos
      U_lt := h.U_lt
      V_pos := h.V_pos
      V_le := h.V_le
      wf := ⟨h.wf.1, hfits⟩
      base_fr := hb192
      hdr := rootStaticHeader_congr h.hdr fun off hoff =>
        hoff_eq off (by clear *- hoff; omega)
      live_eq := (hoff_eq hdrLive (by decide)).trans h.live_eq
      live_le := h.live_le
      ph_le := by dsimp only; rw [hph_m2]; exact h.ph_le
      stg_le := by dsimp only; rw [hst_m2]; exact h.stg_le
      mSrc_eq := by dsimp only; rw [hmS_m2, hnS_m2]; exact h.mSrc_eq
      cache_src := by
        dsimp only; rw [hnS_m2]
        exact hostCacheValid_congr_mem h.cache_src fun k hk => by
          rw [Nat.add_assoc]
          exact hoff_eq (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
      nSrc_bounds := by dsimp only; rw [hnS_m2]; exact h.nSrc_bounds
      sched := hsched₂
      pad_fits := by
        have hp := h.pad_fits; dsimp only at hp ⊢
        simp only [hnS_m2, hph_m2, hnD_m2] at hp ⊢
        exact hp
      ph1_inv := ?_
      ph3_inv := ?_
      ph4_inv := ?_
      pDst_pre := ?_
      ph5_inv := ?_
      ph6_inv := ?_
      ph7_inv := ?_
      ph8_inv := ?_
      ph9_inv := ?_
      ph10_inv := ?_
      sl_le7 := ?_
      sl_67 := ?_
      sl_8 := ?_
      sl_ge9 := ?_ }
  · have hp1 := h.ph1_inv; dsimp only at hp1 ⊢
    rw [hph_m2, hnD_m2, hoff_eq hdrLogSub (by decide), hoff_eq hdrLogAcc (by decide),
      hoff_eq hdrLogK (by decide), hoff_eq hdrLogN (by decide),
      hoff_eq hdrClogN (by decide), hoff_eq hdrPtrB (by decide),
      hoff_eq hdrPgB (by decide), hoff_eq hdrEll (by decide)]
    exact hp1
  · intro hp3
    dsimp only at hp3 ⊢
    rw [hph_m2] at hp3
    obtain ⟨hsp_le, hsh⟩ := h.ph3_inv hp3
    dsimp only at hsp_le hsh
    rw [hoff_eq hdrSplit (by decide), hibL_m2, hqL_m2, hibH_m2, hqH_m2]
    exact ⟨hsp_le, hsplit_congr (by clear *- hp3; omega) (by clear *- hp3; omega) hsh⟩
  · intro hp4
    dsimp only at hp4 ⊢
    rw [hph_m2] at hp4
    obtain ⟨hd_pos, hcur_le, hzero⟩ := h.ph4_inv hp4
    dsimp only at hd_pos hcur_le hzero
    rw [hnD_m2, hoff_eq hdrCur (by decide), hmD_m2, hmbD_eq]
    refine ⟨hd_pos, hcur_le, fun off hoff => ?_⟩
    have hsched := h.sched; dsimp only at hsched
    rw [ite_eq_right (show ph ≠ 0 by clear *- hp4; omega)] at hsched
    have hfr_hi := (hsched.ph3_10
      ⟨show 3 ≤ ph by clear *- hp4; omega, show ph ≤ 10 by clear *- hp4; omega⟩).1
    obtain ⟨_, hpad_e, _, _, hibH_e, _⟩ := hsched.ge2 (show 2 ≤ ph by clear *- hp4; omega)
    dsimp only at hfr_hi hpad_e hibH_e
    have hmD_pad : mem₁ (base + hdrMDst) ≤ mem₁ (base + hdrPad) := by
      rw [hpad_e]; exact le_max_right _ _
    rw [ite_eq_right hd_pos.ne'] at hibH_e
    have hmb_lt : dualMbDst base mem₁ + off < fr := by
      unfold dualMbDst; dsimp only [ph] at hp4
      rw [hp4, ite_eq_left (by decide : 4 < 10), ite_eq_right hd_pos.ne']
      split_ifs <;> (clear *- hoff hcur_le hmD_pad hibH_e hfr_hi; omega)
    exact (heq _ hmb_lt).trans (hzero off hoff)
  · intro h25 h50 hd0
    dsimp only at h25 h50 hd0 ⊢
    rw [hph_m2] at h25 h50; rw [hst_m2] at h50; rw [hnD_m2] at hd0
    rw [hnD_m2, hmbD_eq, hpD_eq, hibH_m2, hqH_m2]
    have hpt1 := h.pDst_pre h25 h50 hd0
    dsimp only at hpt1
    refine fastParamTable_mask_congr hpt1 fun k hk => ?_
    have hp_lt : dualPDst base mem₁ + k < base + 192 := by
      unfold dualPDst; dsimp only [hdrPBase0, hdrPBase1]
      rcases hk with h48 | rfl | rfl <;> split_ifs <;> omega
    exact heq _ (lt_of_lt_of_le hp_lt hb192)
  · intro hp5
    dsimp only at hp5 ⊢
    rw [hph_m2] at hp5
    obtain ⟨hd_pos, hc32, hc_bm, hpt5, hzh, hzp⟩ := h.ph5_inv hp5
    dsimp only at hd_pos hc32 hc_bm hpt5 hzh hzp
    rw [hnD_m2, hmbD_eq, hpD_eq, hibH_m2, hqH_m2, hoff_eq hdrCur (by decide)]
    have hsched := h.sched; dsimp only at hsched
    rw [ite_eq_right (show ph ≠ 0 by clear *- hp5; omega)] at hsched
    have hfr_hi := (hsched.ph3_10
      ⟨show 3 ≤ ph by clear *- hp5; omega, show ph ≤ 10 by clear *- hp5; omega⟩).1
    obtain ⟨hmD_e, hpad_e, _, _, hibH_e, _⟩ :=
      hsched.ge2 (show 2 ≤ ph by clear *- hp5; omega)
    dsimp only at hfr_hi hmD_e hpad_e hibH_e
    have hth_d : whpThreshold c ≤ mem₁ (base + hdrNDst) := by
      rcases hsched.nDst_bounds with hz | ⟨hth, _⟩
      · exact absurd hz hd_pos.ne'
      · exact hth
    have hod_m : offPageDir c w (mem₁ (base + hdrNDst)) ≤ mem₁ (base + hdrMDst) :=
      (epochMeta_offsets_le (w := w) hth_d).2.2.2.trans hmD_e.symm.le
    have h32_od : 32 ≤ offPageDir c w (mem₁ (base + hdrNDst)) :=
      (epochMeta_offsets_le (w := w) hth_d).1.trans
        ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
        (epochMeta_offsets_le (w := w) hth_d).2.2.1)
    have hmD_pad : mem₁ (base + hdrMDst) ≤ mem₁ (base + hdrPad) := by
      rw [hpad_e]; exact le_max_right _ _
    rw [ite_eq_right hd_pos.ne'] at hibH_e
    have hmb_m_lt : dualMbDst base mem₁ + mem₁ (base + hdrMDst) < fr := by
      unfold dualMbDst; dsimp only [ph] at hp5
      rw [hp5, ite_eq_left (by decide : 5 < 10), ite_eq_right hd_pos.ne']
      split_ifs <;> (clear *- hmD_pad hibH_e hfr_hi; omega)
    refine ⟨hd_pos, hc32, hc_bm, ?_, fun k hk1 hk32 => ?_, fun off hlo hhi => ?_⟩
    · refine fastParamTable_mask_congr hpt5 fun k hk => ?_
      have hp_lt : dualPDst base mem₁ + k < base + 192 := by
        unfold dualPDst; dsimp only [hdrPBase0, hdrPBase1]
        rcases hk with h48 | rfl | rfl <;> split_ifs <;> omega
      exact heq _ (lt_of_lt_of_le hp_lt hb192)
    · exact (heq _ (by clear *- hk32 h32_od hod_m hmb_m_lt; omega)).trans (hzh k hk1 hk32)
    · exact (heq _ (by clear *- hhi hod_m hmb_m_lt; omega)).trans (hzp off hlo hhi)
  · intro hp6
    dsimp only at hp6 ⊢; rw [hph_m2] at hp6
    have hpg2 : extractPagePair (dualPgHost c V w base nLive mem₁) mem₂ =
        extractPagePair (dualPgHost c V w base nLive mem₁) mem₁ :=
      congrArg PageUnpermState.st (hpg_meta_eq (by clear *- hp6; omega)
        (by clear *- hp6; omega))
    rw [hpgH_eq, hoff_eq hdrCur (by decide)]
    simp_rw [hpg2]
    exact h.ph6_inv hp6
  · intro hp7
    dsimp only at hp7 ⊢; rw [hph_m2] at hp7
    have hpg2 : extractPagePair (dualPgHost c V w base nLive mem₁) mem₂ =
        extractPagePair (dualPgHost c V w base nLive mem₁) mem₁ :=
      congrArg PageUnpermState.st (hpg_meta_eq (by clear *- hp7; omega)
        (by clear *- hp7; omega))
    have hnH_eq : dualNHost base mem₂ = dualNHost base mem₁ := by
      unfold dualNHost; rw [hnD_m2, hnS_m2]
    rw [hpgH_eq, hoff_eq hdrNSnap (by decide), hoff_eq hdrQSnap (by decide), hnH_eq,
      hoff_eq hdrCur (by decide)]
    simp_rw [hpg2]
    exact h.ph7_inv hp7
  · have hp8 := h.ph8_inv; dsimp only at hp8 ⊢
    rw [hph_m2, hoff_eq hdrRem (by decide), hnS_m2]; exact hp8
  · intro hp9
    dsimp only at hp9 ⊢; rw [hph_m2] at hp9
    have hu2 := hpg_meta_eq (by clear *- hp9; omega) (by clear *- hp9; omega)
    rw [hpgH_eq, hoff_eq hdrRem (by decide), hnS_m2, hud_m2, hu2]
    exact h.ph9_inv hp9
  · intro hp10
    dsimp only at hp10 ⊢; rw [hph_m2] at hp10
    obtain ⟨hsp_le, hsh⟩ := h.ph10_inv hp10
    dsimp only at hsp_le hsh
    rw [hoff_eq hdrSplit (by decide), hibL_m2, hqL_m2, hibH_m2, hqH_m2]
    exact ⟨hsp_le, hsplit_congr (by clear *- hp10; omega) (by clear *- hp10; omega) hsh⟩
  · intro hle7
    dsimp only at hle7 ⊢; rw [hph_m2] at hle7
    obtain ⟨hc1, hc2, hsl, hlen⟩ := h.sl_le7 hle7
    dsimp only at hc1 hc2 hsl hlen
    rw [hcapS_eq, hpS_eq, hmbS_eq, hst_m2, hph_m2, hnS_m2, hnD_m2, hpad_m2,
      hibL_m2, hqL_m2, hibH_m2, hqH_m2]
    refine ⟨hc1, hc2, hsl.congr_lt_frontier (fun hup hsb => ?_) heq, hlen⟩
    unfold activeSrcIo at hup hsb ⊢
    by_cases hlt3 : ph < 3
    · rw [ite_eq_left hlt3] at hsb; exact absurd rfl hsb
    · rw [ite_eq_right hlt3] at hup hsb ⊢
      by_cases heq3 : ph = 3
      · rw [ite_eq_left heq3]; dsimp only [splitSlotIo]
        exact hlo_le_hi (by clear *- heq3; omega) (by clear *- heq3; omega)
      · rw [ite_eq_right heq3, ite_eq_left (by clear *- hle7; omega)] at hsb
        exact absurd rfl hsb
  · intro h67
    dsimp only at h67 ⊢; rw [hph_m2] at h67
    obtain ⟨hz_sm, hd_sl⟩ := h.sl_67 h67
    dsimp only at hz_sm hd_sl
    rw [hnD_m2, hpD_eq, hmbD_eq, hibH_m2, hqH_m2]
    refine ⟨fun hd0 => ?_, fun hd_pos => ?_⟩
    · obtain ⟨z0, z1⟩ := hz_sm hd0
      have hz1_m : mem₂ (base + hdrSmallMeta1 + 1) = mem₁ (base + hdrSmallMeta1 + 1) := by
        rw [Nat.add_assoc]; exact hoff_eq (hdrSmallMeta1 + 1) (by decide)
      exact ⟨(hoff_eq hdrSmallMeta1 (by decide)).trans z0, hz1_m.trans z1⟩
    · obtain ⟨c1, c2, c3, hsl⟩ := hd_sl hd_pos
      exact ⟨c1, c2, c3, hsl.congr_lt_frontier (fun _ hsb => absurd rfl hsb) heq⟩
  · intro hp8
    dsimp only at hp8 ⊢; rw [hph_m2] at hp8
    obtain ⟨c1, c2, hdisj, hdict, hcp0, hslS, hslD, hlS, hlD⟩ := h.sl_8 hp8
    dsimp only at c1 c2 hcp0 hslS hslD hlS hlD
    have hu2 := hpg_meta_eq (by clear *- hp8; omega) (by clear *- hp8; omega)
    rw [hpgH_eq, hcapS_eq, hnD_m2, hu2, hpS_eq, hmbS_eq, hpD_eq, hmbD_eq]
    exact ⟨c1, c2, hdisj, hdict, hcp0,
      hslS.congr_lt_frontier (fun hup _ => absurd hup.symm Nat.zero_ne_one) heq,
      hslD.congr_lt_frontier (fun hup _ => absurd hup.symm Nat.zero_ne_one) heq, hlS, hlD⟩
  · intro hge9
    dsimp only at hge9 ⊢; rw [hph_m2] at hge9
    obtain ⟨c1, c2, hsl, hlD⟩ := h.sl_ge9 hge9
    dsimp only at c1 c2 hsl hlD
    simp only [hnD_m2, hpD_eq, hmbD_eq, hst_m2, hph_m2, hnS_m2, hpad_m2,
      hibL_m2, hqL_m2, hibH_m2, hqH_m2, hud_m2]
    refine ⟨c1, c2, hsl.congr_lt_frontier (fun hup hsb => ?_) heq, hlD⟩
    unfold activeDstIo at hup hsb ⊢
    rw [ite_eq_right (by clear *- hge9; omega), ite_eq_right (by clear *- hge9; omega)]
      at hup hsb ⊢
    by_cases hp9 : ph = 9
    · rw [ite_eq_left hp9] at hup hsb
      by_cases hud0 : mem₁ (base + hdrUnpermDone) = 0
      · rw [ite_eq_left hud0] at hup; dsimp only [pagedSlotIo] at hup; omega
      · rw [ite_eq_right hud0] at hsb; dsimp only [directSlotIo] at hsb; exact absurd rfl hsb
    · rw [ite_eq_right hp9] at hup hsb ⊢
      by_cases hp10 : ph = 10
      · rw [ite_eq_left hp10]; dsimp only [splitSlotIo]
        exact hlo_le_hi (by clear *- hp10; omega) (by clear *- hp10; omega)
      · rw [ite_eq_right hp10] at hsb; dsimp only [directSlotIo] at hsb; exact absurd rfl hsb

/-- Clearing `[fr, fr + k)` (as produced by `shrinkCode`) preserves resting `DualStateInv` at `fr`.
-/
theorem DualStateInv.clear_above {c U V w base fr k : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {mem : ℕ → ℕ}
    (h : DualStateInv c U V w base s_dict L { mem := mem, frontier := fr }) :
    DualStateInv c U V w base s_dict L { mem := clear mem fr k, frontier := fr } :=
  h.congr_lt_frontier
    (fun addr hlt => clear_of_not_owns (by simp only [Block.Owns]; omega))
    (fun addr => by
      by_cases ho : (Block.mk fr k).Owns addr
      · rw [clear_of_owns ho]; exact Nat.two_pow_pos w
      · rw [clear_of_not_owns ho]; exact h.wf.2 addr)

/-! ## Section 2: Post-`randFill` Finalization (`finishRandFillProg_spec`) -/

private theorem finishRandFillProg_raw {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp5 : s.mem (base + hdrPhase) = 5)
    (hdone : s.mem (dualPDst base s.mem + 31) ≤ s.mem (base + hdrCur)) :
    let nDst := s.mem (base + hdrNDst)
    let pDst := dualPDst base s.mem
    let metaDst := dualMbDst base s.mem
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let nLive := (Dictionary.dom s_dict).card
    let hiFr := ibHi + pairStreamWords nLive qHi (valBits V) w
    let io_hi := directSlotIo w (valBits V) base ibHi qHi nLive
    let mask := 2 ^ (redWidthWhp U - 1) - 1
    let mem_masked := Function.update
      (Function.update s.mem (metaDst + 32) (s.mem (metaDst + 32) &&& mask))
      (metaDst + offFpHash c w nDst) (s.mem (metaDst + offFpHash c w nDst) &&& mask)
    let seedsDst := extractEpochSeeds c U w nDst metaDst mem_masked
    let s_rf := (Memory.spec 0).clientState s (finishRandFillProg base)
    FinishRandFillPre w base s ∧
    s_rf.frontier = s.frontier ∧
    Memory.WellFormed w s_rf ∧
    (∀ addr < base, s_rf.mem addr = s.mem addr) ∧
    (∀ off < 48, off ≠ hdrPhase → off ≠ hdrCur → s_rf.mem (base + off) = s.mem (base + off)) ∧
    s_rf.mem (base + hdrPhase) = 6 ∧
    s_rf.mem (base + hdrCur) = 0 ∧
    s.mem (base + hdrCur) = offBktMeta c w nDst ∧
    0 < nDst ∧
    memoryCost (finishRandFillProg base) s ≤ 75 ∧
    extractEpochSeeds c U w nDst metaDst s_rf.mem = seedsDst ∧
    EpochSlotInv c U V w hiFr pDst metaDst io_hi 0 false
      ⟨nDst, fun _ => none, seedsDst, []⟩ s_rf.mem ∧
    EpochSlotInv c U V w hiFr (dualPSrc base s.mem) (dualMbSrc base s.mem) io_hi 0 false
      L.slotSrc s_rf.mem := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf; have hb192 := h.base_fr
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds
  have hstg_le := h.stg_le
  have hw_pos : 0 < w := by clear *- hw11; omega
  have hw_eq : s.mem (base + hdrW) = w := hhdr.2.2.1
  have hred_eq : s.mem (base + hdrRedW) = redWidthWhp U := hhdr.2.2.2.2.2.2.2.2.1
  have hred_1 : 1 ≤ redWidthWhp U := by unfold redWidthWhp; exact le_max_left 1 _
  have hred_w : redWidthWhp U ≤ w :=
    max_le (by clear *- hw11; omega) (Nat.clog_le_of_le_pow hUw.le)
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp5; omega)] at hsched
  obtain ⟨hfr_hi_lo, hfr_hi_mid⟩ := hsched.ph3_10 ⟨by clear *- hp5; omega, by clear *- hp5; omega⟩
  simp only [↓reduceIte] at hfr_hi_mid
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hlog_d, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp5; omega)
  obtain ⟨hvb_eq, hvb_w, _, hqHi_w, _, hpad_hi_s, _, _⟩ := dualCoreInv_ib_fits h
  rw [ite_eq_right (by clear *- hp5; omega)] at hpad_hi_s
  obtain ⟨hd_pos, _, hcur_le_bm, hpt_s, hz_hdr, hz_post⟩ := h.ph5_inv hp5
  have hth_d : whpThreshold c ≤ s.mem (base + hdrNDst) ∧ s.mem (base + hdrNDst) ≤ U := by
    rcases hsched.nDst_bounds with hz | hb
    · exact absurd hz hd_pos.ne'
    · exact hb
  obtain ⟨hlog_e, hell_e, hpg_e⟩ := hlog_d hd_pos
  obtain ⟨hoff32_fp, hoffFp_bm, hoffBm_od, hoffOd_m⟩ := epochMeta_offsets_le (w := w) hth_d.1
  set nLive := (Dictionary.dom s_dict).card
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
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  set offBM := offBktMeta c w nDst
  set pDst := dualPDst base s.mem
  set metaDst := dualMbDst base s.mem
  set io_hi := directSlotIo w vB base ibHi qHi nLive
  let fl : FastEpochLayout := ⟨c, U, V, w, nDst, metaDst, pDst, io_hi⟩
  have hpDst_if : pDst = (if stg = 0 then base + hdrPBase1 else base + hdrPBase0) := by
    dsimp only [pDst]; unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
  have hmetaDst_if : metaDst = (if stg = 0 then base + 192 + pad else base + 192) := by
    dsimp only [metaDst]; unfold dualMbDst
    rw [hp5, ite_eq_left (by decide : 5 < 10), ite_eq_right hd_pos.ne']
  have hpDst_30 : s.mem (pDst + 30) = offFpHash c w nDst := by
    have h30 := hpt_s 30 (by decide)
    dsimp only [FastEpochLayout.paramWord] at h30
    unfold dualPh5MaskMem at h30
    iterate 13 rw [Function.update_of_ne (by omega)] at h30
    exact h30
  have hpDst_31 : s.mem (pDst + 31) = offBM := by
    have h31 := hpt_s 31 (by decide)
    dsimp only [FastEpochLayout.paramWord] at h31
    unfold dualPh5MaskMem at h31
    iterate 13 rw [Function.update_of_ne (by omega)] at h31
    exact h31
  have hcur_eq_bm : s.mem (base + hdrCur) = offBM :=
    le_antisymm hcur_le_bm (hpDst_31 ▸ hdone)
  have hibHi_val : ibHi = base + 192 + pad + mDst + 4 := by
    rw [hibHi_eq, ite_eq_right hd_pos.ne']
  have hmDst_pad : mDst ≤ pad := by rw [hpad_eq]; exact le_max_right _ _
  have hmSrc_pad : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
  have hmd_end_lt : metaDst + mDst < ibHi := by
    rw [hmetaDst_if]; split_ifs <;> (clear *- hibHi_val hmDst_pad; omega)
  have hmd_hiFr : metaDst + epochMetaWordsWhp c w nDst ≤ hiFr := by
    rw [← hmDst_eq]; dsimp only [hiFr]; clear *- hmd_end_lt; omega
  have hmd_fr : metaDst + epochMetaWordsWhp c w nDst ≤ s.frontier :=
    hmd_hiFr.trans hfr_hi_lo
  have hoff32_lt_fp : 32 < offFpHash c w nDst := by
    have hsp := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
      (bCharWhp nDst) (bWhp nDst)
    have heq_fp : 32 + BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c)
        (bCharWhp nDst) (bWhp nDst) = offFpHash c w nDst := rfl
    clear *- hsp heq_fp; omega
  have hfp_lt_bm : offFpHash c w nDst < offBM := by
    have hsp := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
      (bCharWhp nDst) (fpBitsWhp nDst)
    have heq_bm : offFpHash c w nDst + BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c)
        (bCharWhp nDst) (fpBitsWhp nDst) = offBM := rfl
    clear *- hsp heq_bm; omega
  have hbm_le_m : offBM ≤ mDst := (hoffBm_od.trans hoffOd_m).trans hmDst_eq.symm.le
  have hm32_lt_fr : metaDst + 32 < s.frontier := by
    have hmd_m := hmDst_eq ▸ hmd_fr
    clear *- hoff32_lt_fp hfp_lt_bm hbm_le_m hmd_m; omega
  have hmfp_lt_fr : metaDst + offFpHash c w nDst < s.frontier := by
    have hmd_m := hmDst_eq ▸ hmd_fr
    clear *- hfp_lt_bm hbm_le_m hmd_m; omega
  have hmask_shift : ((1 : ℕ) <<< (s.mem (base + hdrRedW) - 1)) - 1 =
      2 ^ (redWidthWhp U - 1) - 1 := by
    rw [hred_eq, shift_one_eq]
  set mask := 2 ^ (redWidthWhp U - 1) - 1
  set mem_masked := Function.update
    (Function.update s.mem (metaDst + 32) (s.mem (metaDst + 32) &&& mask))
    (metaDst + offFpHash c w nDst) (s.mem (metaDst + offFpHash c w nDst) &&& mask)
  set s1 : Memory.State := { mem := mem_masked, frontier := s.frontier }
  set s2 := (Memory.spec 0).clientState s1
    (setDirectSlotIoProg ((base, pDst), ((ibHi, qHi), nLive)))
  have hpDst_bounds : base + 64 ≤ pDst ∧ pDst + 64 ≤ base + 192 := by
    rw [hpDst_if]; dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega
  have hs1_low : ∀ a < base + 192, s1.mem a = s.mem a := fun a ha => by
    dsimp only [s1, mem_masked]
    rw [Function.update_of_ne (by rw [hmetaDst_if]; split_ifs <;> (clear *- ha; omega)),
      Function.update_of_ne (by rw [hmetaDst_if]; split_ifs <;> (clear *- ha; omega))]
  have hs2_slot_eq : s2 = (Memory.spec 0).clientState s1 (setSlotIoProg (pDst, io_hi.toCtx)) := by
    have hev := (setDirectSlotIoProg_eval base pDst ibHi qHi nLive s1).1
    have hw_s1 : s1.mem (base + hdrW) = w :=
      (hs1_low (base + hdrW) (by dsimp only [hdrW]; omega)).trans hw_eq
    have hvb_s1 : s1.mem (base + hdrValBits) = vB :=
      (hs1_low (base + hdrValBits) (by dsimp only [hdrValBits]; omega)).trans hvb_eq
    dsimp only [s2]
    rw [hev, hw_s1, hvb_s1]
  have hfr_s2 : s2.frontier = s.frontier := by
    rw [hs2_slot_eq]; exact runClient_frontier_setSlotIoProg _ s1
  have hfrm_s2 := setSlotIoProg_frame pDst io_hi.toCtx
  have hvals_s2 := setSlotIoProg_mem_vals pDst io_hi s1
  have hs2_out : ∀ a, ¬(pDst + 48 ≤ a ∧ a < pDst + 61) → s2.mem a = s1.mem a :=
    fun a ha => by rw [hs2_slot_eq]; exact hfrm_s2.mem_outside s1 a ha
  have hnLive_w : Fits w nLive := lt_of_le_of_lt hlive_le hUw
  have hv_io_fr : io_hi.Valid w s.frontier := by
    unfold SlotIoLayout.Valid; dsimp only [io_hi, directSlotIo]
    simp only [↓reduceIte]
    exact ⟨hw_pos, trivial, hqHi_w, hvb_w, hnLive_w, hfr_hi_lo⟩
  have hv_fl_fr : fl.Valid w s.frontier :=
    { thresh_le := hth_d.1
      N_le_U := hth_d.2
      fits_U := hUw
      V_pos := hV0
      V_le_pow := hVw
      w_eq := rfl
      redWidth_le := hred_w
      pBase_lt_meta := by
        dsimp only [fl]; rw [hmetaDst_if]; split_ifs <;> (clear *- hpDst_bounds; omega)
      meta_frontier := hmd_fr
      io_valid := hv_io_fr
      w_eq_io := rfl
      qBits_le := by dsimp only [fl, io_hi, directSlotIo]; rw [hqHi_eq, ite_eq_right hd_pos.ne']
                     exact le_max_right _ _
      vBits_eq := rfl
      disj_pBase_io := fun a _ h2 ha => by
        simp only [fl, io_hi, directSlotIo, SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr,
          ↓reduceIte] at ha
        dsimp only [fl] at h2
        have ha1 := ha.1; dsimp only [ibHi] at hibHi_val ha1
        clear *- h2 hpDst_bounds hibHi_val ha1; omega
      disj_fast_io := fun a ha hio => by
        simp only [fl, io_hi, directSlotIo, SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr,
          ↓reduceIte] at hio
        have ha1 := hio.1
        have hod_m : offPageDir c w nDst ≤ mDst := hoffOd_m.trans hmDst_eq.symm.le
        have h32_od : 32 ≤ offPageDir c w nDst := hoff32_fp.trans (hoffFp_bm.trans hoffBm_od)
        dsimp only [fl] at ha
        rcases ha with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;>
          (clear *- hlt hod_m h32_od hmd_end_lt ha1; omega) }
  have hpt_s2 : fl.ParamTable s2.mem := by
    intro k hk
    by_cases hmid : 48 ≤ k ∧ k < 61
    · obtain ⟨hlo_k, hhi_k⟩ := hmid
      rw [hs2_slot_eq]
      interval_cases k
      · exact hvals_s2.1
      · exact hvals_s2.2.1
      · exact hvals_s2.2.2.1
      · exact hvals_s2.2.2.2.1
      · exact hvals_s2.2.2.2.2.1
      · exact hvals_s2.2.2.2.2.2.1
      · exact hvals_s2.2.2.2.2.2.2.1
      · exact hvals_s2.2.2.2.2.2.2.2.1
      · exact hvals_s2.2.2.2.2.2.2.2.2.1
      · exact hvals_s2.2.2.2.2.2.2.2.2.2.1
      · exact hvals_s2.2.2.2.2.2.2.2.2.2.2.1
      · exact hvals_s2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact hvals_s2.2.2.2.2.2.2.2.2.2.2.2.2
    · rw [hs2_out (pDst + k) (by clear *- hmid; omega),
        hs1_low (pDst + k) (by clear *- hk hpDst_bounds; omega)]
      have hpk := hpt_s k hk
      dsimp only [fl, FastEpochLayout.paramWord] at hpk ⊢
      unfold dualPh5MaskMem at hpk
      iterate 13 rw [Function.update_of_ne (by clear *- hmid; omega)] at hpk
      exact hpk
  have hand_lt : ∀ x : ℕ, x &&& mask < 2 ^ (redWidthWhp U - 1) := fun x => by
    dsimp only [mask]; rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hs2_meta_eq : ∀ a, base + 192 ≤ a → s2.mem a = mem_masked a := fun a ha =>
    hs2_out a (by clear *- ha hpDst_bounds; omega)
  have hbkt_lt_s2 : s2.mem fl.bktHashBase < 2 ^ (redWidthWhp U - 1) := by
    dsimp only [fl, FastEpochLayout.bktHashBase]; unfold offBktHash
    rw [hs2_meta_eq _ (by rw [hmetaDst_if]; split_ifs <;> omega)]
    dsimp only [mem_masked]
    rw [Function.update_of_ne (by clear *- hoff32_lt_fp; omega), Function.update_self]
    exact hand_lt _
  have hfp_lt_s2 : s2.mem fl.fpHashBase < 2 ^ (redWidthWhp U - 1) := by
    dsimp only [fl, FastEpochLayout.fpHashBase]
    rw [hs2_meta_eq _ (by rw [hmetaDst_if]; unfold offFpHash offBktHash; split_ifs <;> omega)]
    dsimp only [mem_masked]
    rw [Function.update_self]
    exact hand_lt _
  have hr_s2 : FastLayoutReady w fl s2 := ⟨hfr_s2 ▸ hv_fl_fr, hpt_s2, hbkt_lt_s2, hfp_lt_s2⟩
  have hpre_rf : FinishRandFillPre w base s := by
    refine ⟨by clear *- hw11; omega, hb192, hred_eq ▸ hred_1, hred_eq ▸ hred_w, ?_⟩
    dsimp only
    rw [← hpDst_if, ← hmetaDst_if, hpDst_30, hmask_shift, hlive_eq]
    exact ⟨hm32_lt_fr, hmfp_lt_fr, EpochProgPre.of_large hr_s2⟩
  obtain ⟨hst_rf, hmc_rf⟩ := finishRandFillProg_eval base s
  dsimp only at hst_rf hmc_rf
  rw [← hpDst_if, ← hmetaDst_if, hpDst_30, hmask_shift, hlive_eq] at hst_rf hmc_rf
  set seedsDst := extractEpochSeeds c U w nDst metaDst mem_masked
  have hseeds_s2 : extractEpochSeeds c U w nDst metaDst s2.mem = seedsDst := by
    dsimp only [seedsDst]; unfold extractEpochSeeds
    have hb_eq : BitPackedDoubleTabulation.extractSeed (metaDst + offBktHash) w (redWidthWhp U)
        (cTabWhp c) (dTabWhp c) (bCharWhp nDst) (bWhp nDst) s2.mem =
        BitPackedDoubleTabulation.extractSeed (metaDst + offBktHash) w (redWidthWhp U)
        (cTabWhp c) (dTabWhp c) (bCharWhp nDst) (bWhp nDst) mem_masked := by
      have hrep := BitPackedDoubleTabulation.seedRep_extractSeed (w := w)
        (c_tab := cTabWhp c) (d := dTabWhp c) (b_char := bCharWhp nDst) (M_out := bWhp nDst)
        hbkt_lt_s2
      exact (BitPackedDoubleTabulation.extractSeed_eq_of_seedRep
        (hrep.congr_on hw_pos fun a h1 _ =>
          (hs2_meta_eq a (by
            have hmb_ge : base + 192 ≤ metaDst := by rw [hmetaDst_if]; split_ifs <;> omega
            dsimp only [fl, FastEpochLayout.bktHashBase] at h1
            clear *- h1 hmb_ge; omega)).symm)).symm
    have hf_eq : BitPackedDoubleTabulation.extractSeed (metaDst + offFpHash c w nDst) w
        (redWidthWhp U) (cTabWhp c) (dTabWhp c) (bCharWhp nDst) (fpBitsWhp nDst) s2.mem =
        BitPackedDoubleTabulation.extractSeed (metaDst + offFpHash c w nDst) w
        (redWidthWhp U) (cTabWhp c) (dTabWhp c) (bCharWhp nDst) (fpBitsWhp nDst) mem_masked := by
      have hrep := BitPackedDoubleTabulation.seedRep_extractSeed (w := w)
        (c_tab := cTabWhp c) (d := dTabWhp c) (b_char := bCharWhp nDst) (M_out := fpBitsWhp nDst)
        hfp_lt_s2
      exact (BitPackedDoubleTabulation.extractSeed_eq_of_seedRep
        (hrep.congr_on hw_pos fun a h1 _ =>
          (hs2_meta_eq a (by
            have hmb_ge : base + 192 ≤ metaDst := by rw [hmetaDst_if]; split_ifs <;> omega
            dsimp only [fl, FastEpochLayout.fpHashBase] at h1
            clear *- h1 hmb_ge; omega)).symm)).symm
    rw [hb_eq, hf_eq]
  have hbkt_rep_s2 : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seedsDst.bkt s2.mem := by
    rw [← hseeds_s2]; exact BitPackedDoubleTabulation.seedRep_extractSeed hbkt_lt_s2
  have hfp_rep_s2 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seedsDst.fp s2.mem := by
    rw [← hseeds_s2]; exact BitPackedDoubleTabulation.seedRep_extractSeed hfp_lt_s2
  have hz_hdr_s2 : ∀ k, 1 ≤ k → k < 32 → s2.mem (metaDst + k) = 0 := fun k hk1 hk32 => by
    have hmb_ge : base + 192 ≤ metaDst := by rw [hmetaDst_if]; split_ifs <;> omega
    rw [hs2_meta_eq _ (by clear *- hmb_ge; omega)]
    dsimp only [mem_masked]
    rw [Function.update_of_ne (by clear *- hk32 hoff32_lt_fp; omega),
      Function.update_of_ne (by clear *- hk32; omega)]
    exact hz_hdr k hk1 hk32
  have hz_tab_s2 : ∀ addr, metaDst + offBM ≤ addr → addr < metaDst + offPageDir c w nDst →
      s2.mem addr = 0 := fun addr hlo hhi => by
    have hmb_ge : base + 192 ≤ metaDst := by rw [hmetaDst_if]; split_ifs <;> omega
    rw [hs2_meta_eq _ (by clear *- hmb_ge hlo; omega)]
    dsimp only [mem_masked]
    rw [Function.update_of_ne (by clear *- hlo hfp_lt_bm; omega),
      Function.update_of_ne (by clear *- hlo hoff32_lt_fp hfp_lt_bm; omega)]
    have hsub : metaDst + (addr - metaDst) = addr := by omega
    rw [← hsub]
    exact hz_post (addr - metaDst) (by omega) (by omega)
  have hio_s2 : fl.io.StateInv 0 0 s2.mem := by
    unfold SlotIoLayout.StateInv; dsimp only [fl, io_hi, directSlotIo]
    simp only [↓reduceIte]; exact ⟨Nat.zero_le _, Or.inl trivial⟩
  obtain ⟨hfr_s3_s2, hmc_iz, hfast_s3, hout_iz_fast, _⟩ :=
    epochInitZeroedProg_spec_large (hfr_s2 ▸ hv_fl_fr) hpt_s2 hbkt_rep_s2 hfp_rep_s2
      hz_hdr_s2 hz_tab_s2 hio_s2
  have hgd_s3 := GoodEpochAt.of_initZeroed (hfr_s2 ▸ hv_fl_fr) hpt_s2 hbkt_rep_s2 hfp_rep_s2
    hz_hdr_s2 hz_tab_s2 hio_s2
  have hmconf := epochInitZeroedProg_meta_confine hr_s2
  obtain ⟨s3, hs3_def⟩ : ∃ s3, (Memory.spec 0).clientState s2 (epochInitZeroedProg pDst) = s3 :=
    ⟨_, rfl⟩
  rw [hs3_def] at hfr_s3_s2 hfast_s3 hout_iz_fast hgd_s3 hmconf hst_rf
  clear hs3_def
  have hwf_rf : Memory.WellFormed w ((Memory.spec 0).clientState s (finishRandFillProg base)) :=
    wf_step hwf (validHistory_finishRandFillProg hwf hpre_rf)
  obtain ⟨s_rf, hs_rf_def⟩ :
      ∃ s_rf, (Memory.spec 0).clientState s (finishRandFillProg base) = s_rf := ⟨_, rfl⟩
  rw [hs_rf_def] at hst_rf hwf_rf ⊢
  clear hs_rf_def
  have hfr_rf : s_rf.frontier = s.frontier := by
    rw [hst_rf]; exact hfr_s3_s2.trans hfr_s2
  have hout_rf_meta : ∀ a, a ≠ base + hdrPhase → a ≠ base + hdrCur →
      ¬(pDst + 48 ≤ a ∧ a < pDst + 61) →
      ¬(metaDst ≤ a ∧ a < metaDst + offPageDir c w nDst) →
      s_rf.mem a = s.mem a := fun a hph hcur hp_io hmd_od => by
    rw [hst_rf]; dsimp only
    rw [Function.update_of_ne hph, Function.update_of_ne hcur,
      hmconf a hmd_od, hs2_out a hp_io]
    dsimp only [s1, mem_masked]
    have h32_od : 32 < offPageDir c w nDst :=
      lt_of_lt_of_le (hoff32_lt_fp.trans hfp_lt_bm) hoffBm_od
    have hfp_od : offFpHash c w nDst < offPageDir c w nDst :=
      lt_of_lt_of_le hfp_lt_bm hoffBm_od
    rw [Function.update_of_ne (fun he => hmd_od ⟨by clear *- he; omega,
        by clear *- he hfp_od; omega⟩),
      Function.update_of_ne (fun he => hmd_od ⟨by clear *- he; omega,
        by clear *- he h32_od; omega⟩)]
  have hout_hdr : ∀ off < 48, off ≠ hdrPhase → off ≠ hdrCur →
      s_rf.mem (base + off) = s.mem (base + off) := fun off hoff hph hcur =>
    hout_rf_meta (base + off) (base_add_ne hph) (base_add_ne hcur)
      (by clear *- hoff hpDst_bounds; omega)
      (by rw [hmetaDst_if]; split_ifs <;> (clear *- hoff; omega))
  have hph_rf : s_rf.mem (base + hdrPhase) = 6 := by
    rw [hst_rf]; exact Function.update_self ..
  have hcur_rf : s_rf.mem (base + hdrCur) = 0 := by
    rw [hst_rf]; dsimp only
    rw [Function.update_of_ne (base_add_ne (by decide)), Function.update_self]
  have hst_rf_v : s_rf.mem (base + hdrStage) = stg :=
    hout_hdr hdrStage (by decide) (by decide) (by decide)
  have hnS_rf : s_rf.mem (base + hdrNSrc) = nSrc :=
    hout_hdr hdrNSrc (by decide) (by decide) (by decide)
  have hnD_rf : s_rf.mem (base + hdrNDst) = nDst :=
    hout_hdr hdrNDst (by decide) (by decide) (by decide)
  have hmS_rf : s_rf.mem (base + hdrMSrc) = mSrc :=
    hout_hdr hdrMSrc (by decide) (by decide) (by decide)
  have hmD_rf : s_rf.mem (base + hdrMDst) = mDst :=
    hout_hdr hdrMDst (by decide) (by decide) (by decide)
  have hpad_rf : s_rf.mem (base + hdrPad) = pad :=
    hout_hdr hdrPad (by decide) (by decide) (by decide)
  have hibL_rf : s_rf.mem (base + hdrItemLo) = ibLo :=
    hout_hdr hdrItemLo (by decide) (by decide) (by decide)
  have hibH_rf : s_rf.mem (base + hdrItemHi) = ibHi :=
    hout_hdr hdrItemHi (by decide) (by decide) (by decide)
  have hqL_rf : s_rf.mem (base + hdrQLo) = qLo :=
    hout_hdr hdrQLo (by decide) (by decide) (by decide)
  have hqH_rf : s_rf.mem (base + hdrQHi) = qHi :=
    hout_hdr hdrQHi (by decide) (by decide) (by decide)
  have hseeds_rf : extractEpochSeeds c U w nDst metaDst s_rf.mem = seedsDst := by
    have hs3_rf_seeds : ∀ a, metaDst + 32 ≤ a → a < metaDst + offBM → s_rf.mem a = s2.mem a :=
      fun a hlo hhi => by
        rw [hst_rf]; dsimp only
        have hm192 : base + 192 ≤ metaDst := by
          rw [hmetaDst_if]; split_ifs <;> (clear *-; omega)
        rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- hm192 hlo; omega),
          Function.update_of_ne (by dsimp only [hdrCur]; clear *- hm192 hlo; omega)]
        exact hout_iz_fast a (hv_fl_fr.not_ownsFast_seeds hlo hhi)
          (by dsimp only [fl]; clear *- hlo; omega)
    unfold extractEpochSeeds
    have hb_eq : BitPackedDoubleTabulation.extractSeed (metaDst + offBktHash) w (redWidthWhp U)
        (cTabWhp c) (dTabWhp c) (bCharWhp nDst) (bWhp nDst) s_rf.mem = seedsDst.bkt :=
      BitPackedDoubleTabulation.extractSeed_eq_of_seedRep
        (hbkt_rep_s2.congr_on hw_pos fun a h1 h2 => by
          dsimp only [fl, FastEpochLayout.bktHashBase] at h1 h2
          exact hs3_rf_seeds a (by unfold offBktHash at h1; clear *- h1; omega)
            (by unfold offFpHash offBktHash at hfp_lt_bm; unfold offBktHash at h2
                clear *- h2 hfp_lt_bm; omega))
    have hf_eq : BitPackedDoubleTabulation.extractSeed (metaDst + offFpHash c w nDst) w
        (redWidthWhp U) (cTabWhp c) (dTabWhp c) (bCharWhp nDst) (fpBitsWhp nDst) s_rf.mem =
        seedsDst.fp :=
      BitPackedDoubleTabulation.extractSeed_eq_of_seedRep
        (hfp_rep_s2.congr_on hw_pos fun a h1 h2 => by
          dsimp only [fl, FastEpochLayout.fpHashBase] at h1 h2
          exact hs3_rf_seeds a (by unfold offFpHash offBktHash at h1; clear *- h1; omega)
            (by dsimp only [offBM]; unfold offBktMeta; clear *- h2; omega))
    rw [hb_eq, hf_eq]
  set slDst : SlotLatent c U V := ⟨nDst, fun _ => none, seedsDst, []⟩
  have hsl_dst_s3 : EpochSlotInv c U V w s.frontier pDst metaDst io_hi 0 false slDst s3.mem := by
    unfold EpochSlotInv; dsimp only [slDst]
    rw [ite_eq_right hd_pos.ne']
    have hfp_s3 : s3.mem fl.fpHashBase = s2.mem fl.fpHashBase :=
      hout_iz_fast fl.fpHashBase
        (hv_fl_fr.not_ownsFast_seeds
          (by dsimp only [fl, FastEpochLayout.fpHashBase]; exact Nat.add_le_add_left hoff32_fp _)
          (by dsimp only [fl, FastEpochLayout.fpHashBase]; exact Nat.add_lt_add_left hfp_lt_bm _))
        (by dsimp only [fl, FastEpochLayout.fpHashBase]; clear *- hoff32_fp; omega)
    refine ⟨hv_fl_fr, LargeEpochInv.fast hfast_s3, hfp_s3 ▸ hfp_lt_s2, ?_, rfl, hgd_s3⟩
    intro k hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    have hemp : liveDom (EpochUpdate.eval ([] : List (EpochUpdate U V))) = ∅ := by
      ext x; simp [liveDom, EpochUpdate.eval]
    simp only [List.take_nil, hemp, Finset.card_empty, zero_le]
  have hsl_dst_rf_fr : EpochSlotInv c U V w s.frontier pDst metaDst io_hi 0 false slDst s_rf.mem :=
    hsl_dst_s3.congr_mem
      (fun a h1 _ => by
        rw [hst_rf]; dsimp only
        rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- h1 hpDst_bounds; omega),
          Function.update_of_ne (by dsimp only [hdrCur]; clear *- h1 hpDst_bounds; omega)])
      (fun a ha => by
        have hm_ge : metaDst ≤ a := by
          unfold slotOwnsNonPageMeta at ha
          rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> (clear *- h1; omega)
        have hm192 : base + 192 ≤ metaDst := by
          rw [hmetaDst_if]; split_ifs <;> (clear *-; omega)
        rw [hst_rf]; dsimp only
        rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- hm_ge hm192; omega),
          Function.update_of_ne (by dsimp only [hdrCur]; clear *- hm_ge hm192; omega)])
      (fun a ha => by
        simp only [io_hi, directSlotIo, SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr,
          ↓reduceIte] at ha
        have ha1 := ha.1
        rw [hst_rf]; dsimp only
        rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- ha1 hibHi_val; omega),
          Function.update_of_ne (by dsimp only [hdrCur]; clear *- ha1 hibHi_val; omega)])
  have hsl_dst_hi : EpochSlotInv c U V w hiFr pDst metaDst io_hi 0 false slDst s_rf.mem :=
    hsl_dst_rf_fr.at_exact_frontier (fr₂ := hiFr)
      (by dsimp only [hiFr]; clear *- hpDst_bounds hibHi_val; omega)
      (by dsimp only [slDst]; rw [ite_eq_right hd_pos.ne']; exact hmd_hiFr)
      (by
        dsimp only [io_hi, directSlotIo, hiFr]
        simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte]
        exact le_rfl)
  obtain ⟨hcap_s, hdict_s, hsl_s, hlen_s⟩ := h.sl_le7 (by clear *- hp5; omega)
  have hio_s : activeSrcIo c w vB base stg (s.mem (base + hdrPhase))
      nSrc nDst pad ibLo qLo ibHi qHi nLive = io_hi := by
    unfold activeSrcIo
    rw [ite_eq_right (by clear *- hp5; omega), ite_eq_right (by clear *- hp5; omega),
      ite_eq_left (by clear *- hp5; omega)]
  rw [hio_s] at hsl_s
  have hsl_src_rf_fr : EpochSlotInv c U V w s.frontier (dualPSrc base s.mem)
      (dualMbSrc base s.mem) io_hi 0 false L.slotSrc s_rf.mem := by
    refine hsl_s.congr_mem
      (fun a h1 h2 => by
        have hp_lt : a < base + 192 := by
          unfold dualPSrc at h2; split_ifs at h2 <;>
            (dsimp only [hdrPBase0, hdrPBase1] at h2; clear *- h2; omega)
        have hp_ge : base + 64 ≤ a := by
          unfold dualPSrc at h1; split_ifs at h1 <;>
            (dsimp only [hdrPBase0, hdrPBase1] at h1; clear *- h1; omega)
        have hp_ne : ¬(pDst + 48 ≤ a ∧ a < pDst + 61) := by
          rw [hpDst_if]; unfold dualPSrc at h1 h2
          by_cases hs0 : stg = 0
          · simp only [show s.mem (base + hdrStage) = stg from rfl, hs0, ↓reduceIte,
              hdrPBase0, hdrPBase1] at h1 h2 ⊢
            clear *- h1 h2; omega
          · simp only [show s.mem (base + hdrStage) = stg from rfl, hs0, ↓reduceIte,
              hdrPBase0, hdrPBase1] at h1 h2 ⊢
            clear *- h1 h2; omega
        exact hout_rf_meta a (by dsimp only [hdrPhase]; clear *- hp_ge; omega)
          (by dsimp only [hdrCur]; clear *- hp_ge; omega) hp_ne
          (by rw [hmetaDst_if]; split_ifs <;> (clear *- hp_lt; omega)))
      (fun a ha => by
        have ha_r := slotOwnsNonPageMeta_src_range hcap_s (fun _ => hd_pos.ne') ha
        have ha48 : base + 48 ≤ a := by
          rcases ha_r with ⟨h1, _⟩ | h192 <;> [exact h1; (clear *- h192; omega)]
        have hp_ne : ¬(pDst + 48 ≤ a ∧ a < pDst + 61) := by
          rcases ha_r with ⟨_, h2⟩ | h192
          · clear *- h2 hpDst_bounds; omega
          · clear *- h192 hpDst_bounds; omega
        have hmd_ne : ¬(metaDst ≤ a ∧ a < metaDst + offPageDir c w nDst) := by
          intro hmd_in
          unfold slotOwnsNonPageMeta dualMbSrc at ha
          rw [hcap_s] at ha; unfold dualCapSrc at ha
          by_cases hst0 : stg = 0
          · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at ha
            have hmd_eq : metaDst = base + 192 + pad := by rw [hmetaDst_if, ite_eq_left hst0]
            by_cases hs0 : nSrc = 0
            · simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, hs0, ↓reduceIte,
                ne_eq, not_true_eq_false, false_and, or_false] at ha
              dsimp only [hdrSmallMeta0] at ha
              clear *- ha hmd_in hmd_eq; omega
            · have hth_s : whpThreshold c ≤ nSrc := by
                rcases hnSrc_b with hz | ⟨hth, _⟩
                · exact absurd hz hs0
                · exact hth
              have hod_s : offPageDir c w nSrc ≤ mSrc :=
                (epochMeta_offsets_le (w := w) hth_s).2.2.2.trans hmSrc_eq.symm.le
              have hmS32 : 32 ≤ mSrc :=
                (epochMeta_offsets_le (w := w) hth_s).1.trans
                  ((epochMeta_offsets_le (w := w) hth_s).2.1.trans
                    ((epochMeta_offsets_le (w := w) hth_s).2.2.1.trans hod_s))
              simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, hs0, ↓reduceIte] at ha
              dsimp only [mSrc, pad] at ha hmSrc_pad hod_s hmS32 hmd_in hmd_eq
              rcases ha with ⟨_, h2⟩ | ⟨_, _, h2⟩ <;>
                (clear *- h2 hmS32 hod_s hmSrc_pad hmd_in hmd_eq; omega)
          · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at ha
            have hmd_eq : metaDst = base + 192 := by rw [hmetaDst_if, ite_eq_right hst0]
            have hod_d : offPageDir c w nDst ≤ mDst := hoffOd_m.trans hmDst_eq.symm.le
            dsimp only [pad, mDst] at ha hod_d hmDst_pad hmd_in
            rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;>
              (clear *- h1 hod_d hmDst_pad hmd_in hmd_eq; omega)
        exact hout_rf_meta a (by dsimp only [hdrPhase]; clear *- ha48; omega)
          (by dsimp only [hdrCur]; clear *- ha48; omega) hp_ne hmd_ne)
      (fun a ha => by
        simp only [io_hi, directSlotIo, SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr,
          ↓reduceIte] at ha
        have ha1 := ha.1
        have hod_d : offPageDir c w nDst ≤ mDst := hoffOd_m.trans hmDst_eq.symm.le
        exact hout_rf_meta a (by dsimp only [hdrPhase]; clear *- ha1 hibHi_val; omega)
          (by dsimp only [hdrCur]; clear *- ha1 hibHi_val; omega)
          (by clear *- ha1 hibHi_val hpDst_bounds; omega)
          (by clear *- ha1 hod_d hmd_end_lt; omega))
  have hsl_src_hi : EpochSlotInv c U V w hiFr (dualPSrc base s.mem)
      (dualMbSrc base s.mem) io_hi 0 false L.slotSrc s_rf.mem :=
    hsl_src_rf_fr.at_exact_frontier (fr₂ := hiFr)
      (by unfold dualPSrc; dsimp only [hiFr, hdrPBase0, hdrPBase1]
          split_ifs <;> (clear *- hibHi_val; omega))
      (by unfold dualMbSrc; rw [hcap_s]; unfold dualCapSrc
          by_cases hst0 : stg = 0
          · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
            rw [← hmSrc_eq]
            by_cases hs0 : nSrc = 0
            · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only [hdrSmallMeta0, hiFr]
              clear *- hibHi_val; omega
            · rw [ite_eq_right hs0, ite_eq_right hs0]; dsimp only [hiFr]
              clear *- hmSrc_pad hibHi_val; omega
          · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
            rw [ite_eq_right hd_pos.ne', ← hmDst_eq]; dsimp only [hiFr]
            clear *- hibHi_val; omega)
      (by
        dsimp only [io_hi, directSlotIo, hiFr]
        simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte]
        exact le_rfl)
  have hmc_tot : memoryCost (finishRandFillProg base) s ≤ 75 := by
    change memoryCost (epochInitZeroedProg pDst) s2 ≤ 45 at hmc_iz
    change memoryCost (finishRandFillProg base) s =
      28 + memoryCost (epochInitZeroedProg pDst) s2 at hmc_rf
    clear *- hmc_rf hmc_iz; omega
  exact ⟨hpre_rf, hfr_rf, hwf_rf,
    fun addr hlt_b => hout_rf_meta addr
      (by dsimp only [hdrPhase]; clear *- hlt_b; omega)
      (by dsimp only [hdrCur]; clear *- hlt_b; omega)
      (by clear *- hlt_b hpDst_bounds; omega)
      (by rw [hmetaDst_if]; split_ifs <;> (clear *- hlt_b; omega)),
    hout_hdr, hph_rf, hcur_rf, hcur_eq_bm, hd_pos, hmc_tot, hseeds_rf, hsl_dst_hi, hsl_src_hi⟩

/-- At `ph = 5` with `s.mem (pDst + 31) ≤ s.mem (base + hdrCur)` (`cur = offBktMeta c w nDst`),
`finishRandFillProg` masks the two Stage-1 odd multipliers, initializes `pDst` with
`extractEpochSeeds`, and transitions to `DualPreShrinkInv` at `ph = 6`. -/
theorem finishRandFillProg_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp5 : s.mem (base + hdrPhase) = 5)
    (hdone : s.mem (dualPDst base s.mem + 31) ≤ s.mem (base + hdrCur)) :
    let nDst := s.mem (base + hdrNDst)
    let metaDst := dualMbDst base s.mem
    let mask := 2 ^ (redWidthWhp U - 1) - 1
    let mem_masked := Function.update
      (Function.update s.mem (metaDst + 32) (s.mem (metaDst + 32) &&& mask))
      (metaDst + offFpHash c w nDst) (s.mem (metaDst + offFpHash c w nDst) &&& mask)
    let seedsDst := extractEpochSeeds c U w nDst metaDst mem_masked
    let L_rf : DualLatent c U V :=
      { L with
        slotDst := ⟨nDst, fun _ => none, seedsDst, []⟩
        elapsed := L.elapsed + 1 }
    let s_rf := (Memory.spec 0).clientState s (finishRandFillProg base)
    FinishRandFillPre w base s ∧
    s_rf.frontier = s.frontier ∧
    (∀ addr < base, s_rf.mem addr = s.mem addr) ∧
    memoryCost (finishRandFillProg base) s ≤ 75 ∧
    extractEpochSeeds c U w nDst metaDst s_rf.mem = seedsDst ∧
    DualPreShrinkInv c U V w base s_dict L_rf s_rf := by
  dsimp only
  obtain ⟨hpre_rf, hfr_rf, hwf_rf, hout_lt_b, hout_hdr, hph_rf, hcur_rf, hcur_eq_bm, hd_pos,
    hmc_tot, hseeds_rf, hsl_dst_hi, hsl_src_hi⟩ := finishRandFillProg_raw h hp5 hdone
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds
  have hstg_le := h.stg_le
  have hw_pos : 0 < w := by clear *- hw11; omega
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp5; omega)] at hsched
  obtain ⟨hfr_hi_lo, hfr_hi_mid⟩ := hsched.ph3_10 ⟨by clear *- hp5; omega, by clear *- hp5; omega⟩
  simp only [↓reduceIte] at hfr_hi_mid
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hlog_d, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp5; omega)
  obtain ⟨hvb_eq, hvb_w, _, hqHi_w, _, hpad_hi_s, _, _⟩ := dualCoreInv_ib_fits h
  rw [ite_eq_right (by clear *- hp5; omega)] at hpad_hi_s
  obtain ⟨hlog_e, hell_e, hpg_e⟩ := hlog_d hd_pos
  obtain ⟨hcap_s, hdict_s, _, hlen_s⟩ := h.sl_le7 (by clear *- hp5; omega)
  set nLive := (Dictionary.dom s_dict).card
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
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  set pDst := dualPDst base s.mem
  set metaDst := dualMbDst base s.mem
  set io_hi := directSlotIo w vB base ibHi qHi nLive
  obtain ⟨seedsDst, hseeds_def⟩ :
      ∃ sd, extractEpochSeeds c U w nDst metaDst
        (Function.update
          (Function.update s.mem (metaDst + 32)
            (s.mem (metaDst + 32) &&& (2 ^ (redWidthWhp U - 1) - 1)))
          (metaDst + offFpHash c w nDst)
          (s.mem (metaDst + offFpHash c w nDst) &&& (2 ^ (redWidthWhp U - 1) - 1))) = sd :=
    ⟨_, rfl⟩
  rw [hseeds_def] at hseeds_rf hsl_dst_hi ⊢
  clear hseeds_def
  obtain ⟨s_rf, hs_rf_def⟩ :
      ∃ s_rf, (Memory.spec 0).clientState s (finishRandFillProg base) = s_rf := ⟨_, rfl⟩
  rw [hs_rf_def] at hfr_rf hwf_rf hout_lt_b hout_hdr hph_rf hcur_rf
  rw [hs_rf_def] at hseeds_rf hsl_dst_hi hsl_src_hi ⊢
  clear hs_rf_def
  set slDst : SlotLatent c U V := ⟨nDst, fun _ => none, seedsDst, []⟩
  set L_rf : DualLatent c U V := { L with slotDst := slDst, elapsed := L.elapsed + 1 }
  have hst_rf_v : s_rf.mem (base + hdrStage) = stg :=
    hout_hdr hdrStage (by decide) (by decide) (by decide)
  have hnS_rf : s_rf.mem (base + hdrNSrc) = nSrc :=
    hout_hdr hdrNSrc (by decide) (by decide) (by decide)
  have hnD_rf : s_rf.mem (base + hdrNDst) = nDst :=
    hout_hdr hdrNDst (by decide) (by decide) (by decide)
  have hmS_rf : s_rf.mem (base + hdrMSrc) = mSrc :=
    hout_hdr hdrMSrc (by decide) (by decide) (by decide)
  have hmD_rf : s_rf.mem (base + hdrMDst) = mDst :=
    hout_hdr hdrMDst (by decide) (by decide) (by decide)
  have hpad_rf : s_rf.mem (base + hdrPad) = pad :=
    hout_hdr hdrPad (by decide) (by decide) (by decide)
  have hibL_rf : s_rf.mem (base + hdrItemLo) = ibLo :=
    hout_hdr hdrItemLo (by decide) (by decide) (by decide)
  have hibH_rf : s_rf.mem (base + hdrItemHi) = ibHi :=
    hout_hdr hdrItemHi (by decide) (by decide) (by decide)
  have hqL_rf : s_rf.mem (base + hdrQLo) = qLo :=
    hout_hdr hdrQLo (by decide) (by decide) (by decide)
  have hqH_rf : s_rf.mem (base + hdrQHi) = qHi :=
    hout_hdr hdrQHi (by decide) (by decide) (by decide)
  have hibHi_val : ibHi = base + 192 + pad + mDst + 4 := by
    rw [hibHi_eq, ite_eq_right hd_pos.ne']
  have hpw2 := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
    (show qHi + vB ≤ 2 * w by clear *- hqHi_w hvb_w; omega)
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    unfold bulkBatchWhp; clear *- hfr_hi_mid hpw2; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive :=
    hfr_hi_mid.trans hpad_hi_s
  refine ⟨hpre_rf, hfr_rf, hout_lt_b, hmc_tot, hseeds_rf, ?_⟩
  refine ⟨hwf_rf, ?_, fun h5 => absurd (hph_rf.symm.trans h5) (by decide), ?_⟩
  · rw [hnS_rf, hph_rf, ite_eq_right (by decide : 6 ≠ 0), hnD_rf, hfr_rf]; exact hfr_le_pad
  · rw [hph_rf, ite_eq_right (by decide : ¬(6 < 2)), ite_eq_right (by decide : 6 ≠ 2),
      ite_eq_left (by decide : 6 ≤ 10), hibH_rf, hqH_rf, hfr_rf]
    refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
    have hpD_rf : dualPDst base s_rf.mem = pDst := by
      unfold pDst dualPDst; rw [hph_rf, hp5, hst_rf_v]
      simp only [Nat.reduceLT, ↓reduceIte]; rfl
    have hmbD_rf : dualMbDst base s_rf.mem = metaDst := by
      unfold metaDst dualMbDst
      rw [hph_rf, hp5, hnD_rf, hst_rf_v, hpad_rf]
      simp only [Nat.reduceLT, ↓reduceIte]; rfl
    have hpS_rf : dualPSrc base s_rf.mem = dualPSrc base s.mem := by
      unfold dualPSrc; rw [hst_rf_v]
    have hmbS_rf : dualMbSrc base s_rf.mem = dualMbSrc base s.mem := by
      unfold dualMbSrc; rw [hst_rf_v, hnS_rf, hpad_rf]
    have hcapS_rf : dualCapSrc base s_rf.mem = dualCapSrc base s.mem := by
      unfold dualCapSrc; rw [hst_rf_v, hnS_rf, hnD_rf]
    have hsched_rf :
        if ({ mem := s_rf.mem, frontier := hiFr } : Memory.State).mem (base + hdrPhase) = 0 then
          DualIdleSched false c U V w base nLive L_rf { mem := s_rf.mem, frontier := hiFr }
        else
          DualActiveSched false c U V w base nLive L_rf { mem := s_rf.mem, frontier := hiFr } := by
      dsimp only; rw [ite_eq_right (by rw [hph_rf]; decide)]
      refine
        { nDst_bounds := by dsimp only; rw [hnD_rf]; exact hsched.nDst_bounds
          nDst_zero := fun hz => absurd (hnD_rf.symm.trans hz) hd_pos.ne'
          stg_one := fun _ => by
            dsimp only; rw [hnD_rf, hph_rf]; exact ⟨hd_pos, by decide, by decide⟩
          post_trig := by dsimp only [L_rf]; rw [hnS_rf]; exact hsched.post_trig
          trig_cap := by dsimp only [L_rf]; rw [hnS_rf, hnD_rf]; exact hsched.trig_cap
          drift_hi := by
            dsimp only [L_rf]; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
            have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
          drift_lo := by
            dsimp only [L_rf]; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
            have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
          ibLo_eq := by
            dsimp only; rw [hibL_rf, hph_rf, ite_eq_left (by decide : 6 < 10), hmS_rf]
            have hib := hsched.ibLo_eq; rwa [ite_eq_left (by clear *- hp5; omega)] at hib
          qLo_eq := by
            dsimp only; rw [hqL_rf, hph_rf, ite_eq_left (by decide : 6 < 10), hnS_rf]
            have hq := hsched.qLo_eq; rwa [ite_eq_left (by clear *- hp5; omega)] at hq
          ph1 := fun h1 => absurd (hph_rf.symm.trans h1) (by decide)
          ge2 := fun _ => by
            dsimp only
            rw [hmD_rf, hnD_rf, hpad_rf, hmS_rf, hibH_rf, hqH_rf, hnS_rf]
            refine ⟨hmDst_eq, hpad_eq, ?_, fun _ => ?_, hibHi_eq, hqHi_eq⟩
            · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                rw [Nat.add_assoc]
                exact hout_hdr (hdrDstOd + k) (by dsimp only [hdrDstOd]; clear *- hk; omega)
                  (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                  (by dsimp only [hdrDstOd, hdrCur]; clear *- hk; omega)
            · exact ⟨(hout_hdr hdrLogN (by decide) (by decide) (by decide)).trans hlog_e,
                (hout_hdr hdrEll (by decide) (by decide) (by decide)).trans hell_e,
                (hout_hdr hdrPgB (by decide) (by decide) (by decide)).trans hpg_e⟩
          ph2 := fun h2 => absurd (hph_rf.symm.trans h2) (by decide)
          ph3_10 := fun _ => by
            dsimp only; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
            rw [hibH_rf, hqH_rf]; exact ⟨le_rfl, le_rfl⟩
          ph11 := fun h11 => absurd (hph_rf.symm.trans h11) (by decide)
          budget := by
            obtain ⟨_, hb_tot, _⟩ := hsched.budget
            have hcur_bm' : s.mem (base + hdrCur) = offBktMeta c w (s.mem (base + hdrNDst)) :=
              hcur_eq_bm
            have hnH_rf : dualNHost base s_rf.mem = nDst := by
              unfold dualNHost; rw [hnD_rf, ite_eq_right hd_pos.ne']
            have hmp_rf : (dualPgHost c V w base nLive s_rf.mem).maxPages =
                nDst / pageSizeWhp nDst + 4 := by
              unfold dualPgHost hostPageLayout epochPageArenaLayout; rw [hnH_rf]
            have hnD_2R : nDst ≤ 2 * max (whpThreshold c) nSrc := by
              have hh := dualNHost_le_two_nRef h (by clear *- hp5; omega)
              unfold dualNHost at hh; rwa [ite_eq_right hd_pos.ne'] at hh
            have hmp_le : nDst / pageSizeWhp nDst + 4 ≤
                max (whpThreshold c) nSrc / 16 + 16 := by
              have h1 : nDst / pageSizeWhp nDst ≤ nDst / 32 :=
                Nat.div_le_div_left (le_max_left 32 _) (by decide)
              have h2 : nDst / 32 ≤ (2 * max (whpThreshold c) nSrc) / (2 * 16) :=
                Nat.div_le_div_right (c := 32) hnD_2R
              rw [Nat.mul_div_mul_left _ _ (by decide : 0 < 2)] at h2
              clear *- h1 h2; omega
            have hdiv_mp := Nat.div_le_div_right (c := 1024) hmp_le
            have hf2 := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
            have hel_rf : L_rf.elapsed = L.elapsed + 1 := rfl
            have hm_eq : ({ mem := s_rf.mem, frontier := hiFr } : Memory.State).mem = s_rf.mem :=
              rfl
            rw [hm_eq]
            unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
            simp only [hp5, hcur_bm', hnS_rf, hst_rf_v, hph_rf, hcur_rf, hmp_rf, hel_rf,
              Nat.reduceEqDiff, Nat.reduceLeDiff, and_self, ↓reduceIte] at hb_tot ⊢
            dsimp only [nDst, nSrc] at hdiv_mp hf2 ⊢
            generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef
              at hb_tot hdiv_mp hf2 ⊢
            by_cases hst0 : stg = 0
            · have hst0' : s.mem (base + hdrStage) = 0 := hst0
              simp only [hst0, hst0', ↓reduceIte] at hb_tot ⊢
              refine ⟨by clear *- hf2; omega, ?_, ?_⟩ <;>
                (clear *- hb_tot hdiv_mp hf2; omega)
            · have hst0' : s.mem (base + hdrStage) ≠ 0 := hst0
              simp only [hst0, hst0', ↓reduceIte] at hb_tot ⊢
              refine ⟨by clear *- hf2; omega, ?_, ?_⟩ <;>
                (clear *- hb_tot hdiv_mp hf2; omega) }
    refine
      { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
        wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, hwf_rf.2⟩
        base_fr := by dsimp only [hiFr]; clear *- hibHi_val; omega
        hdr := rootStaticHeader_congr hhdr fun off hoff =>
          hout_hdr off (by clear *- hoff; omega)
            (by dsimp only [hdrPhase]; clear *- hoff; omega)
            (by dsimp only [hdrCur]; clear *- hoff; omega)
        live_eq := (hout_hdr hdrLive (by decide) (by decide) (by decide)).trans hlive_eq
        live_le := hlive_le
        ph_le := by dsimp only; rw [hph_rf]; decide
        stg_le := by dsimp only; rw [hst_rf_v]; exact hstg_le
        mSrc_eq := by dsimp only; rw [hmS_rf, hnS_rf]; exact hmSrc_eq
        cache_src := by
          dsimp only; rw [hnS_rf]
          exact hostCacheValid_congr_mem hcache_s fun k hk => by
            rw [Nat.add_assoc]
            exact hout_hdr (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
        nSrc_bounds := by dsimp only; rw [hnS_rf]; exact hnSrc_b
        sched := hsched_rf
        pad_fits := by
          dsimp only; rw [hnS_rf, hph_rf, ite_eq_right (by decide : 6 ≠ 0), hnD_rf]
          have hp := h.pad_fits; rwa [ite_eq_right (by clear *- hp5; omega)] at hp
        ph1_inv := fun h1 => absurd (hph_rf.symm.trans h1) (by decide)
        ph3_inv := fun h3 => absurd (hph_rf.symm.trans h3) (by decide)
        ph4_inv := fun h4 => absurd (hph_rf.symm.trans h4) (by decide)
        pDst_pre := fun ⟨_, h5⟩ => absurd (hph_rf ▸ h5) (by decide)
        ph5_inv := fun h5 => absurd (hph_rf.symm.trans h5) (by decide)
        ph6_inv := fun _ => by
          dsimp only; rw [hcur_rf]; exact ⟨Nat.zero_le _, fun _ hlt => absurd hlt (by omega)⟩
        ph7_inv := fun h7 => absurd (hph_rf.symm.trans h7) (by decide)
        ph8_inv := fun h8 => absurd (hph_rf.symm.trans h8) (by decide)
        ph9_inv := fun h9 => absurd (hph_rf.symm.trans h9) (by decide)
        ph10_inv := fun h10 => absurd (hph_rf.symm.trans h10) (by decide)
        sl_le7 := ?_
        sl_67 := ?_
        sl_8 := fun h8 => absurd (hph_rf.symm.trans h8) (by decide)
        sl_ge9 := fun h9 => absurd (hph_rf ▸ h9) (by decide) }
    · intro _
      dsimp only [L_rf]
      rw [hcapS_rf, hpS_rf, hmbS_rf, hph_rf]
      refine ⟨hcap_s, hdict_s, ?_, fun _ hs_p => by
        have hl := hlen_s (by clear *- hp5; omega) hs_p
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl ⊢
        exact hl⟩
      unfold activeSrcIo
      rw [ite_eq_right (by decide : ¬(6 < 3)), ite_eq_right (by decide : 6 ≠ 3),
        ite_eq_left (by decide : 6 < 8), hibH_rf, hqH_rf]
      exact hsl_src_hi
    · intro _
      dsimp only [L_rf, slDst]
      rw [hnD_rf, hpD_rf, hmbD_rf, hibH_rf, hqH_rf]
      exact ⟨fun hz => absurd hz hd_pos.ne', fun _ => ⟨rfl, rfl, rfl, hsl_dst_hi⟩⟩

/-! ## Section 3: Post-Shrink & Rebuild Completion (`calcPostShrinkProg_spec`,
`postRandShrinkProg_spec`) -/

private theorem dualPaddedWords_dst_le {c U V w nSrc nDst nLive : ℕ} :
    dualPaddedWords c U V w nDst nDst nLive ≤ dualPaddedWords c U V w nSrc nDst nLive := by
  unfold dualPaddedWords
  have hm : max (epochMetaWordsWhp c w nDst) (epochMetaWordsWhp c w nDst) ≤
      max (epochMetaWordsWhp c w nSrc) (epochMetaWordsWhp c w nDst) := by
    rw [max_self]; exact le_max_right _ _
  have hi : max (epochItemBitsWhp c U V nDst) (epochItemBitsWhp c U V nDst) ≤
      max (epochItemBitsWhp c U V nSrc) (epochItemBitsWhp c U V nDst) := by
    rw [max_self]; exact le_max_right _ _
  have hpw : packedWords nLive
      (max (epochItemBitsWhp c U V nDst) (epochItemBitsWhp c U V nDst)) w ≤
      packedWords nLive
        (max (epochItemBitsWhp c U V nSrc) (epochItemBitsWhp c U V nDst)) w := by
    unfold packedWords
    have hm1 := Nat.mul_le_mul_left nLive hi
    exact Nat.add_le_add_right
      (Nat.div_le_div_right (c := w) (Nat.sub_le_sub_right (Nat.add_le_add_right hm1 w) 1)) 2
  omega

private theorem dualPreShrinkInv_hdr_fits {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (hpre : DualPreShrinkInv c U V w base s_dict L s) :
    11 ≤ w ∧ base + 192 ≤ s.frontier ∧
    s.mem (base + hdrW) = w ∧ s.mem (base + hdrValBits) ≤ w ∧
    s.mem (base + hdrQLo) ≤ w ∧ s.mem (base + hdrQHi) ≤ w ∧
    Fits w (s.mem (base + hdrItemLo) +
      pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQLo))
        (s.mem (base + hdrValBits)) w) ∧
    Fits w (s.mem (base + hdrItemHi) +
      pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQHi))
        (s.mem (base + hdrValBits)) w) := by
  have from_core : ∀ {isMid : Bool} {L₀ : DualLatent c U V} {fr₀ : ℕ},
      fr₀ ≤ s.frontier →
      DualCoreInv isMid c U V w base s_dict L₀ { mem := s.mem, frontier := fr₀ } →
      11 ≤ w ∧ base + 192 ≤ s.frontier ∧
      s.mem (base + hdrW) = w ∧ s.mem (base + hdrValBits) ≤ w ∧
      s.mem (base + hdrQLo) ≤ w ∧ s.mem (base + hdrQHi) ≤ w ∧
      Fits w (s.mem (base + hdrItemLo) +
        pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQLo))
          (s.mem (base + hdrValBits)) w) ∧
      Fits w (s.mem (base + hdrItemHi) +
        pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQHi))
          (s.mem (base + hdrValBits)) w) := fun hfr_le hc => by
    obtain ⟨hvb_eq, hvb_w, hqL_w, hqH_w, _, _, hfit_lo1, hfit_hi1⟩ := dualCoreInv_ib_fits hc
    dsimp only at hvb_eq hvb_w hqL_w hqH_w hfit_lo1 hfit_hi1
    have hlive_eq : s.mem (base + hdrLive) = (Dictionary.dom s_dict).card := hc.live_eq
    have hpw_le : ∀ n b, pairStreamWords n b (valBits V) w ≤
        pairStreamWords (n + 1) b (valBits V) w := fun n b => by
      unfold pairStreamWords packedWords
      have hm := Nat.mul_le_mul_right (b + valBits V) (Nat.le_succ n)
      exact Nat.add_le_add_right
        (Nat.div_le_div_right (c := w) (Nat.sub_le_sub_right (Nat.add_le_add_right hm w) 1)) 2
    rw [hlive_eq, hvb_eq]
    exact ⟨hc.hw11, hc.base_fr.trans hfr_le, hc.hdr.2.2.1, hvb_w, hqL_w, hqH_w,
      hfit_lo1.of_le (Nat.add_le_add_left (hpw_le _ _) _),
      hfit_hi1.of_le (Nat.add_le_add_left (hpw_le _ _) _)⟩
  obtain ⟨_, _, _, hbr⟩ := hpre
  by_cases hlt2 : s.mem (base + hdrPhase) < 2
  · rw [ite_eq_left hlt2] at hbr; exact from_core hbr.1 hbr.2.2
  · rw [ite_eq_right hlt2] at hbr
    by_cases hp2 : s.mem (base + hdrPhase) = 2
    · rw [ite_eq_left hp2] at hbr; exact from_core le_rfl hbr.2
    · rw [ite_eq_right hp2] at hbr
      by_cases hle10 : s.mem (base + hdrPhase) ≤ 10
      · rw [ite_eq_left hle10] at hbr; exact from_core hbr.1 hbr.2.2
      · rw [ite_eq_right hle10] at hbr
        obtain ⟨_, hlo_le, hgt_b, hle_b⟩ := hbr
        by_cases hb : bulkBatchWhp < s.frontier -
            (s.mem (base + hdrItemLo) +
              pairStreamWords (Dictionary.dom s_dict).card (s.mem (base + hdrQLo)) (valBits V) w)
        · exact from_core (Nat.sub_le _ _) (hgt_b hb)
        · exact from_core le_rfl (hle_b (Nat.not_lt.mp hb)).1

/-- Evaluates `calcPostShrinkProg (base, s_pre.frontier)` on `DualPreShrinkInv`, proving bounded
`k_sh ≤ bulkBatchWhp`, `k_sh ≤ s_pre.frontier`, `PreservesEpochSeeds`, and resting `DualStateInv`
(both before and after `clear` by `shrinkCode`), including `11 → 0` completion via
`finishShrinkPostProg`. -/
theorem calcPostShrinkProg_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s_pre : Memory.State}
    (hpre : DualPreShrinkInv c U V w base s_dict L s_pre) :
    let s_ps := (Memory.spec 0).clientState s_pre (calcPostShrinkProg (base, s_pre.frontier))
    let k_sh := (Memory.spec 0).clientResult s_pre (calcPostShrinkProg (base, s_pre.frontier))
    s_ps.frontier = s_pre.frontier ∧
    k_sh ≤ bulkBatchWhp ∧
    k_sh ≤ s_pre.frontier ∧
    (∀ addr < base, s_ps.mem addr = s_pre.mem addr) ∧
    memoryCost (calcPostShrinkProg (base, s_pre.frontier)) s_pre ≤ 31 ∧
    ∃ L_post : DualLatent c U V,
      PreservesEpochSeeds False
        (s_pre.mem (base + hdrPhase) = 11 ∧ s_ps.mem (base + hdrPhase) = 0) L L_post ∧
      DualStateInv c U V w base s_dict L_post
        { mem := s_ps.mem, frontier := s_pre.frontier - k_sh } ∧
      DualStateInv c U V w base s_dict L_post
        { mem := clear s_ps.mem (s_pre.frontier - k_sh) k_sh,
          frontier := s_pre.frontier - k_sh } := by
  dsimp only
  obtain ⟨hw11, hb192, hw_eq, _, _, _, _, _⟩ := dualPreShrinkInv_hdr_fits hpre
  have hw_pos : 0 < w := by clear *- hw11; omega
  obtain ⟨hst_cps, hres_cps, hmc_cps⟩ := calcPostShrinkProg_eval (curFr := s_pre.frontier)
    (hw_eq ▸ hw_pos)
  dsimp only at hst_cps hres_cps
  rw [hw_eq] at hst_cps hres_cps
  obtain ⟨hwf_pre, _, _, hbr⟩ := hpre
  set nLive := (Dictionary.dom s_dict).card
  set ph := s_pre.mem (base + hdrPhase)
  by_cases hlt2 : ph < 2
  · rw [ite_eq_left hlt2] at hbr hres_cps
    obtain ⟨hlo_le, hdiff_le, hinv_lo⟩ := hbr
    have hlive_eq : s_pre.mem (base + hdrLive) = nLive := hinv_lo.live_eq
    have hvb_eq : s_pre.mem (base + hdrValBits) = valBits V := hinv_lo.hdr.2.2.2.2.1
    rw [hlive_eq, hvb_eq] at hst_cps hres_cps
    rw [ite_eq_right (fun h11 => absurd h11.1 (by clear *- hlt2; omega))] at hst_cps
    have hsub_eq : s_pre.frontier -
        (s_pre.frontier -
          (s_pre.mem (base + hdrItemLo) +
            pairStreamWords nLive (s_pre.mem (base + hdrQLo)) (valBits V) w)) =
        s_pre.mem (base + hdrItemLo) +
          pairStreamWords nLive (s_pre.mem (base + hdrQLo)) (valBits V) w := by
      clear *- hlo_le; omega
    rw [hst_cps, hres_cps]
    have hinv_lo' : DualStateInv c U V w base s_dict L
        { mem := s_pre.mem,
          frontier := s_pre.frontier - (s_pre.frontier -
            (s_pre.mem (base + hdrItemLo) +
              pairStreamWords nLive (s_pre.mem (base + hdrQLo)) (valBits V) w)) } := by
      rw [hsub_eq]; exact hinv_lo
    exact ⟨rfl, hdiff_le, Nat.sub_le _ _, fun _ _ => rfl, hmc_cps, L,
      preservesEpochSeeds_refl (fun ⟨h11, _⟩ => absurd h11 (by clear *- hlt2; omega)) L,
      hinv_lo', hinv_lo'.clear_above⟩
  · rw [ite_eq_right hlt2] at hbr hres_cps
    by_cases hp2 : ph = 2
    · rw [ite_eq_left hp2] at hbr
      obtain ⟨hfr_lt_hi, hinv2⟩ := hbr
      have hlive_eq : s_pre.mem (base + hdrLive) = nLive := hinv2.live_eq
      have hvb_eq : s_pre.mem (base + hdrValBits) = valBits V := hinv2.hdr.2.2.2.2.1
      rw [hlive_eq, hvb_eq, ite_eq_right (fun h11 => absurd (hp2.symm.trans h11.1) (by decide))]
        at hst_cps
      rw [hlive_eq, hvb_eq, ite_eq_right (show ph ≠ 11 by clear *- hp2; omega)] at hres_cps
      have hdiff0 : s_pre.frontier -
          (s_pre.mem (base + hdrItemHi) +
            pairStreamWords nLive (s_pre.mem (base + hdrQHi)) (valBits V) w) = 0 :=
        Nat.sub_eq_zero_of_le hfr_lt_hi.le
      rw [hst_cps, hres_cps, hdiff0, Nat.sub_zero]
      exact ⟨rfl, Nat.zero_le _, Nat.zero_le _, fun _ _ => rfl, hmc_cps, L,
        preservesEpochSeeds_refl (fun ⟨h11, _⟩ => absurd (hp2.symm.trans h11) (by decide)) L,
        hinv2, hinv2.clear_above⟩
    · rw [ite_eq_right hp2] at hbr
      by_cases hle10 : ph ≤ 10
      · rw [ite_eq_left hle10] at hbr
        obtain ⟨hhi_le, hdiff_le, hinv_hi⟩ := hbr
        have hlive_eq : s_pre.mem (base + hdrLive) = nLive := hinv_hi.live_eq
        have hvb_eq : s_pre.mem (base + hdrValBits) = valBits V := hinv_hi.hdr.2.2.2.2.1
        rw [hlive_eq, hvb_eq,
          ite_eq_right (fun h11 => absurd h11.1 (by clear *- hle10; omega))] at hst_cps
        rw [hlive_eq, hvb_eq, ite_eq_right (show ph ≠ 11 by clear *- hle10; omega)] at hres_cps
        have hsub_eq : s_pre.frontier -
            (s_pre.frontier -
              (s_pre.mem (base + hdrItemHi) +
                pairStreamWords nLive (s_pre.mem (base + hdrQHi)) (valBits V) w)) =
            s_pre.mem (base + hdrItemHi) +
              pairStreamWords nLive (s_pre.mem (base + hdrQHi)) (valBits V) w := by
          clear *- hhi_le; omega
        rw [hst_cps, hres_cps]
        have hinv_hi' : DualStateInv c U V w base s_dict L
            { mem := s_pre.mem,
              frontier := s_pre.frontier - (s_pre.frontier -
                (s_pre.mem (base + hdrItemHi) +
                  pairStreamWords nLive (s_pre.mem (base + hdrQHi)) (valBits V) w)) } := by
          rw [hsub_eq]; exact hinv_hi
        exact ⟨rfl, hdiff_le, Nat.sub_le _ _, fun _ _ => rfl, hmc_cps, L,
          preservesEpochSeeds_refl (fun ⟨h11, _⟩ => absurd h11 (by clear *- hle10; omega)) L,
          hinv_hi', hinv_hi'.clear_above⟩
      · rw [ite_eq_right hle10] at hbr
        obtain ⟨hp11, hlo_le, hgt_b, hle_b⟩ := hbr
        dsimp only [ph] at hp11
        rw [ite_eq_left hp11] at hres_cps
        set loFr := s_pre.mem (base + hdrItemLo) +
          pairStreamWords nLive (s_pre.mem (base + hdrQLo)) (valBits V) w
        set diffLo := s_pre.frontier - loFr
        by_cases hgt : bulkBatchWhp < diffLo
        · have hinv_sh := hgt_b hgt
          have hlive_eq : s_pre.mem (base + hdrLive) = nLive := hinv_sh.live_eq
          have hvb_eq : s_pre.mem (base + hdrValBits) = valBits V := hinv_sh.hdr.2.2.2.2.1
          rw [hlive_eq, hvb_eq,
            ite_eq_right (fun h11 => (Nat.not_le.mpr hgt) h11.2)] at hst_cps
          rw [hlive_eq, hvb_eq, min_eq_right hgt.le] at hres_cps
          rw [hst_cps, hres_cps]
          exact ⟨rfl, le_rfl, (hgt.le).trans (Nat.sub_le _ _), fun _ _ => rfl, hmc_cps, L,
            preservesEpochSeeds_refl (fun ⟨_, h0⟩ => absurd (hp11.symm.trans h0) (by decide)) L,
            hinv_sh, hinv_sh.clear_above⟩
        · -- Branch `11 → 0`: rebuild completes via `finishShrinkPostProg base`!
          have hd_le : diffLo ≤ bulkBatchWhp := Nat.not_lt.mp hgt
          obtain ⟨hmid11, hel_1, hel_16⟩ := hle_b hd_le
          have hlive_eq : s_pre.mem (base + hdrLive) = nLive := hmid11.live_eq
          have hvb_eq : s_pre.mem (base + hdrValBits) = valBits V := hmid11.hdr.2.2.2.2.1
          rw [hlive_eq, hvb_eq, ite_eq_left ⟨hp11, hd_le⟩] at hst_cps
          rw [hlive_eq, hvb_eq, min_eq_left hd_le] at hres_cps
          obtain ⟨hst_fsp, _⟩ := finishShrinkPostProg_eval base s_pre
          dsimp only at hst_fsp
          set nSrc := s_pre.mem (base + hdrNSrc)
          set nDst := s_pre.mem (base + hdrNDst)
          set mDst := s_pre.mem (base + hdrMDst)
          set ibLo := s_pre.mem (base + hdrItemLo)
          set qLo := s_pre.mem (base + hdrQLo)
          set s1 := if 0 < nDst then (Memory.spec 0).clientState s_pre (copyDstToSrcHostProg base)
            else s_pre
          have hfr_s1 : s1.frontier = s_pre.frontier := by
            dsimp only [s1]; split_ifs
            · exact (copyDstToSrcHostProg_spec base s_pre).1
            · rfl
          have hs1_out : ∀ a, ¬(base + 38 ≤ a ∧ a < base + 43) → s1.mem a = s_pre.mem a :=
            fun a ha => by
              dsimp only [s1]; split_ifs
              · exact (copyDstToSrcHostProg_spec base s_pre).2.2.2.2.2.2.2 a ha
              · rfl
          set s_ps := (Memory.spec 0).clientState s_pre (calcPostShrinkProg (base, s_pre.frontier))
          have hs_ps_eq : s_ps = (Memory.spec 0).clientState s_pre (finishShrinkPostProg base) :=
            hst_cps
          have hfr_ps : s_ps.frontier = s_pre.frontier := by
            rw [hs_ps_eq, hst_fsp]; exact hfr_s1
          have hwf_ps : Memory.WellFormed w s_ps := by
            rw [hs_ps_eq]
            exact wf_step hwf_pre (validHistory_finishShrinkPostProg hwf_pre (by omega))
          have hout_ps : ∀ a, ¬(base + 38 ≤ a ∧ a < base + 43) →
              a ≠ base + hdrNSrc → a ≠ base + hdrMSrc → a ≠ base + hdrNDst → a ≠ base + hdrMDst →
              a ≠ base + hdrStage → a ≠ base + hdrEpochOps → a ≠ base + hdrItemHi →
              a ≠ base + hdrQHi → a ≠ base + hdrPhase →
              s_ps.mem a = s_pre.mem a :=
            fun a hc h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
              rw [hs_ps_eq, hst_fsp]; dsimp only
              rw [Function.update_of_ne h9, Function.update_of_ne h8, Function.update_of_ne h7,
                Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4,
                Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
              exact hs1_out a hc
          have hph_ps : s_ps.mem (base + hdrPhase) = 0 := by
            rw [hs_ps_eq, hst_fsp]; exact Function.update_self ..
          have hqH_ps : s_ps.mem (base + hdrQHi) = qLo := by
            rw [hs_ps_eq, hst_fsp]; dsimp only
            rw [Function.update_of_ne (base_add_ne (by decide)), Function.update_self]
          have hibH_ps : s_ps.mem (base + hdrItemHi) = ibLo := by
            rw [hs_ps_eq, hst_fsp]; dsimp only
            iterate 2 rw [Function.update_of_ne (base_add_ne (by decide))]
            exact Function.update_self ..
          have hops_ps : s_ps.mem (base + hdrEpochOps) = 0 := by
            rw [hs_ps_eq, hst_fsp]; dsimp only
            iterate 3 rw [Function.update_of_ne (base_add_ne (by decide))]
            exact Function.update_self ..
          have hst_ps : s_ps.mem (base + hdrStage) = 0 := by
            rw [hs_ps_eq, hst_fsp]; dsimp only
            iterate 4 rw [Function.update_of_ne (base_add_ne (by decide))]
            exact Function.update_self ..
          have hmD_ps : s_ps.mem (base + hdrMDst) = 0 := by
            rw [hs_ps_eq, hst_fsp]; dsimp only
            iterate 5 rw [Function.update_of_ne (base_add_ne (by decide))]
            exact Function.update_self ..
          have hnD_ps : s_ps.mem (base + hdrNDst) = 0 := by
            rw [hs_ps_eq, hst_fsp]; dsimp only
            iterate 6 rw [Function.update_of_ne (base_add_ne (by decide))]
            exact Function.update_self ..
          have hmS_ps : s_ps.mem (base + hdrMSrc) = mDst := by
            rw [hs_ps_eq, hst_fsp]; dsimp only
            iterate 7 rw [Function.update_of_ne (base_add_ne (by decide))]
            exact Function.update_self ..
          have hnS_ps : s_ps.mem (base + hdrNSrc) = nDst := by
            rw [hs_ps_eq, hst_fsp]; dsimp only
            iterate 8 rw [Function.update_of_ne (base_add_ne (by decide))]
            exact Function.update_self ..
          have hibL_ps : s_ps.mem (base + hdrItemLo) = ibLo :=
            hout_ps (base + hdrItemLo) (by dsimp only [hdrItemLo]; omega)
              (base_add_ne (by decide)) (base_add_ne (by decide)) (base_add_ne (by decide))
              (base_add_ne (by decide)) (base_add_ne (by decide)) (base_add_ne (by decide))
              (base_add_ne (by decide)) (base_add_ne (by decide)) (base_add_ne (by decide))
          have hqL_ps : s_ps.mem (base + hdrQLo) = qLo :=
            hout_ps (base + hdrQLo) (by dsimp only [hdrQLo]; omega)
              (base_add_ne (by decide)) (base_add_ne (by decide)) (base_add_ne (by decide))
              (base_add_ne (by decide)) (base_add_ne (by decide)) (base_add_ne (by decide))
              (base_add_ne (by decide)) (base_add_ne (by decide)) (base_add_ne (by decide))
          have hsched11 := hmid11.sched
          rw [ite_eq_right (by clear *- hp11; omega)] at hsched11
          obtain ⟨hmDst_eq, _, hcache_d, _, _, _⟩ := hsched11.ge2 (by clear *- hp11; omega)
          have hibLo_eq : ibLo = base + 192 + mDst := by
            have hib := hsched11.ibLo_eq
            rwa [hp11, ite_eq_right (by decide : ¬(11 < 10))] at hib
          have hqLo_eq : qLo = (if nDst = 0 then keyBits U else quotBitsWhp U nDst) := by
            have hq := hsched11.qLo_eq
            rwa [hp11, ite_eq_right (by decide : ¬(11 < 10))] at hq
          have hcache_src_ps : HostCacheValid c w nDst hdrSrcOd base s_ps.mem := fun hd_pos => by
            obtain ⟨c0, c1, c2, c3, c4⟩ := hcache_d hd_pos
            have hcp := copyDstToSrcHostProg_spec base s_pre
            have hs1_eq : s1 = (Memory.spec 0).clientState s_pre (copyDstToSrcHostProg base) :=
              ite_eq_left hd_pos
            have hup_out : ∀ o, 38 ≤ o → o < 43 → s_ps.mem (base + o) = s1.mem (base + o) :=
              fun o hlo hhi => by
                rw [hs_ps_eq, hst_fsp]; dsimp only
                iterate 9 rw [Function.update_of_ne
                  (by dsimp only [hdrPhase, hdrQHi, hdrItemHi, hdrEpochOps, hdrStage, hdrMDst,
                        hdrNDst, hdrMSrc, hdrNSrc]; clear *- hlo hhi; omega)]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · exact (hup_out 38 (by decide) (by decide)).trans (hs1_eq ▸ hcp.2.2.1 |>.trans c0)
            · exact (hup_out 39 (by decide) (by decide)).trans (hs1_eq ▸ hcp.2.2.2.1 |>.trans c1)
            · exact (hup_out 40 (by decide) (by decide)).trans (hs1_eq ▸ hcp.2.2.2.2.1 |>.trans c2)
            · exact (hup_out 41 (by decide) (by decide)).trans
                (hs1_eq ▸ hcp.2.2.2.2.2.1 |>.trans c3)
            · exact (hup_out 42 (by decide) (by decide)).trans
                (hs1_eq ▸ hcp.2.2.2.2.2.2.1 |>.trans c4)
          have hd_hi : nLive ≤ L.nTrig + L.elapsed := by
            have hd := hsched11.drift_hi; dsimp only at hd
            simp only [↓reduceIte] at hd
            rw [Nat.sub_add_cancel hel_1] at hd; exact hd
          have hd_lo : L.nTrig ≤ nLive + L.elapsed := by
            have hd := hsched11.drift_lo; dsimp only at hd
            simp only [↓reduceIte] at hd
            rw [Nat.sub_add_cancel hel_1] at hd; exact hd
          have hidle_safe : DualIdleSafe c U nDst nLive :=
            (active_rebuild_safe hsched11.post_trig hsched11.trig_cap hd_hi hd_lo hel_16
              hmid11.live_le).2.2.2
          obtain ⟨hcap_d, hdict_d, hsl_d, hevs_d⟩ := hmid11.sl_ge9 (by clear *- hp11; omega)
          dsimp only at hcap_d hdict_d hsl_d hevs_d
          have hpD11 : dualPDst base s_pre.mem = base + hdrPBase0 := by
            unfold dualPDst; rw [hp11, ite_eq_right (by decide : ¬(11 < 10))]
          have hmbD11 : dualMbDst base s_pre.mem =
              (if nDst = 0 then base + hdrSmallMeta0 else base + 192) := by
            unfold dualMbDst; rw [hp11, ite_eq_right (by decide : ¬(11 < 10))]
          have hio11 : activeDstIo c w (valBits V) base (s_pre.mem (base + hdrStage))
              (s_pre.mem (base + hdrPhase)) nSrc nDst (s_pre.mem (base + hdrPad)) ibLo qLo
              (s_pre.mem (base + hdrItemHi)) (s_pre.mem (base + hdrQHi)) nLive
              (s_pre.mem (base + hdrUnpermDone)) =
              directSlotIo w (valBits V) base ibLo qLo nLive := by
            rw [hp11]; unfold activeDstIo; simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]
          have hsl_d0 : EpochSlotInv c U V w s_pre.frontier (base + hdrPBase0)
              (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
              (directSlotIo w (valBits V) base ibLo qLo nLive) 0 false L.slotDst s_pre.mem := by
            rw [hpD11, hmbD11, hio11] at hsl_d
            simpa only [hp11, Bool.false_eq_true, Nat.reduceEqDiff, false_and, and_false,
              ↓reduceIte] using hsl_d
          have hsl_ps_fr : EpochSlotInv c U V w s_pre.frontier (base + hdrPBase0)
              (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
              (directSlotIo w (valBits V) base ibLo qLo nLive) 0 false L.slotDst s_ps.mem := by
            refine hsl_d0.congr_mem
              (fun a h1 _ => hout_ps a
                (by dsimp only [hdrPBase0] at h1; clear *- h1; omega)
                (by dsimp only [hdrPBase0, hdrNSrc] at h1 ⊢; omega)
                (by dsimp only [hdrPBase0, hdrMSrc] at h1 ⊢; omega)
                (by dsimp only [hdrPBase0, hdrNDst] at h1 ⊢; omega)
                (by dsimp only [hdrPBase0, hdrMDst] at h1 ⊢; omega)
                (by dsimp only [hdrPBase0, hdrStage] at h1 ⊢; omega)
                (by dsimp only [hdrPBase0, hdrEpochOps] at h1 ⊢; omega)
                (by dsimp only [hdrPBase0, hdrItemHi] at h1 ⊢; omega)
                (by dsimp only [hdrPBase0, hdrQHi] at h1 ⊢; omega)
                (by dsimp only [hdrPBase0, hdrPhase] at h1 ⊢; omega))
              (fun a ha => by
                have ha48 : base + 48 ≤ a := by
                  unfold slotOwnsNonPageMeta at ha; rw [hcap_d] at ha
                  by_cases hd0 : nDst = 0
                  · rw [ite_eq_left hd0] at ha
                    rcases ha with ⟨h1, _⟩ | ⟨hne, _⟩
                    · dsimp only [hdrSmallMeta0] at h1; omega
                    · exact absurd hd0 hne
                  · rw [ite_eq_right hd0] at ha
                    rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> omega
                exact hout_ps a
                  (by clear *- ha48; omega)
                  (by dsimp only [hdrNSrc]; clear *- ha48; omega)
                  (by dsimp only [hdrMSrc]; clear *- ha48; omega)
                  (by dsimp only [hdrNDst]; clear *- ha48; omega)
                  (by dsimp only [hdrMDst]; clear *- ha48; omega)
                  (by dsimp only [hdrStage]; clear *- ha48; omega)
                  (by dsimp only [hdrEpochOps]; clear *- ha48; omega)
                  (by dsimp only [hdrItemHi]; clear *- ha48; omega)
                  (by dsimp only [hdrQHi]; clear *- ha48; omega)
                  (by dsimp only [hdrPhase]; clear *- ha48; omega))
              (fun a ha => by
                simp only [directSlotIo, SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr,
                  ↓reduceIte] at ha
                have ha1 := ha.1
                exact hout_ps a
                  (by clear *- ha1 hibLo_eq; omega)
                  (by dsimp only [hdrNSrc]; clear *- ha1 hibLo_eq; omega)
                  (by dsimp only [hdrMSrc]; clear *- ha1 hibLo_eq; omega)
                  (by dsimp only [hdrNDst]; clear *- ha1 hibLo_eq; omega)
                  (by dsimp only [hdrMDst]; clear *- ha1 hibLo_eq; omega)
                  (by dsimp only [hdrStage]; clear *- ha1 hibLo_eq; omega)
                  (by dsimp only [hdrEpochOps]; clear *- ha1 hibLo_eq; omega)
                  (by dsimp only [hdrItemHi]; clear *- ha1 hibLo_eq; omega)
                  (by dsimp only [hdrQHi]; clear *- ha1 hibLo_eq; omega)
                  (by dsimp only [hdrPhase]; clear *- ha1 hibLo_eq; omega))
          have hpw_ge2 : 2 ≤ pairStreamWords nLive qLo (valBits V) w := by
            unfold pairStreamWords packedWords; exact Nat.le_add_left 2 _
          have hsl_lo : EpochSlotInv c U V w loFr (base + hdrPBase0)
              (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
              (directSlotIo w (valBits V) base ibLo qLo nLive) 0 false L.slotDst s_ps.mem :=
            hsl_ps_fr.at_exact_frontier (fr₂ := loFr)
              (by dsimp only [loFr, hdrPBase0]; clear *- hibLo_eq; omega)
              (by
                rw [hcap_d, ← hmDst_eq]
                by_cases hd0 : nDst = 0
                · rw [ite_eq_left hd0, ite_eq_left hd0]; dsimp only [hdrSmallMeta0, loFr]
                  clear *- hibLo_eq; omega
                · rw [ite_eq_right hd0, ite_eq_right hd0]; dsimp only [loFr]
                  clear *- hibLo_eq; omega)
              (by
                dsimp only [directSlotIo, loFr]
                simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte]
                exact le_rfl)
          have hel_le_nDst : 0 < nDst → 2 * L.elapsed ≤ nDst := fun hd_pos => by
            have hpost : DualPostUpdateSafe c U nSrc L.nTrig := hsched11.post_trig
            have htrig : dualTriggerCap c U nSrc L.nTrig L.trigOps = some nDst :=
              hsched11.trig_cap
            have hnt_U : L.nTrig ≤ U := by
              unfold DualPostUpdateSafe at hpost
              by_cases hs0 : nSrc = 0
              · rw [ite_eq_left hs0] at hpost; exact hpost.1
              · rw [ite_eq_right hs0] at hpost; exact hpost.2.2.1
            have hdst_sf : EpochCapSafe (whpThreshold c) U nDst L.nTrig :=
              (active_rebuild_safe hpost htrig (Nat.le_add_right _ 0)
                (Nat.le_add_right _ 0) (Nat.zero_le _) hnt_U).2.2.1
            unfold EpochCapSafe at hdst_sf
            rw [ite_eq_right hd_pos.ne'] at hdst_sf
            obtain ⟨hth_d, _, _, hnt_d⟩ := hdst_sf
            by_cases hs0 : nSrc = 0
            · rw [hs0, max_eq_left (Nat.zero_le _)] at hel_16
              clear *- hel_16 hth_d; omega
            · have hth_s : whpThreshold c ≤ nSrc := by
                rcases hmid11.nSrc_bounds with hz | ⟨hth, _⟩
                · exact absurd hz hs0
                · exact hth
              rw [max_eq_right hth_s] at hel_16
              unfold DualPostUpdateSafe at hpost
              rw [ite_eq_right hs0] at hpost
              have h27 := hpost.2.2.2.1
              clear *- hel_16 h27 hnt_d; omega
          have hsm_lt_th : nDst = 0 → nLive < whpThreshold c := fun hd0 => by
            have hs_pos : 0 < nSrc := (hsched11.nDst_zero hd0).1
            have hth_s : whpThreshold c ≤ nSrc := by
              rcases hmid11.nSrc_bounds with hz | ⟨hth, _⟩
              · exact absurd hz hs_pos.ne'
              · exact hth
            have hpost : DualPostUpdateSafe c U nSrc L.nTrig := hsched11.post_trig
            unfold DualPostUpdateSafe at hpost
            rw [ite_eq_right hs_pos.ne'] at hpost
            obtain ⟨_, _, hntU, h27, h16⟩ := hpost
            have htrig : dualTriggerCap c U nSrc L.nTrig L.trigOps = some 0 :=
              hd0 ▸ hsched11.trig_cap
            unfold dualTriggerCap at htrig
            rw [ite_eq_right hs_pos.ne'] at htrig
            have hng : ¬(nSrc < U ∧ 3 * nSrc ≤ 4 * L.nTrig) := fun hg => by
              rw [ite_eq_left hg, Option.some.injEq] at htrig
              have hhi := h16 hg.1
              have h20 := whpThreshold_ge_pow20 c
              clear *- hth_s hhi hg h20 htrig; omega
            rw [ite_eq_right hng] at htrig
            by_cases hs : 5 * L.nTrig ≤ 2 * nSrc
            · rw [ite_eq_left hs] at htrig
              by_cases hsm : 2 * L.nTrig < whpThreshold c
              · have hel_s : 16 * L.elapsed ≤ nSrc := by
                  have h := hel_16
                  rwa [max_eq_right hth_s] at h
                have h20 := whpThreshold_ge_pow20 c
                clear *- hsm h27 hel_s hd_hi h20; omega
              · rw [ite_eq_right hsm, Option.some.injEq] at htrig
                have h20 := whpThreshold_ge_pow20 c
                clear *- hsm hntU h20 htrig hs hth_s; omega
            · rw [ite_eq_right hs] at htrig
              split_ifs at htrig with href
              · injection htrig with heq; exact absurd heq hs_pos.ne'
          set L_fin : DualLatent c U V :=
            { slotSrc := L.slotDst
              slotDst := SlotLatent.emptySmall c U V
              nTrig := 0
              trigOps := 0
              elapsed := 0
              unpermBound := 0 }
          have hpres_fin : PreservesEpochSeeds False
              (s_pre.mem (base + hdrPhase) = 11 ∧ s_ps.mem (base + hdrPhase) = 0) L L_fin :=
            ⟨⟨fun hnp => absurd ⟨hp11, hph_ps⟩ hnp, fun _ => ⟨rfl, HEq.rfl, rfl⟩⟩, Or.inl rfl⟩
          have hsub_lo : s_pre.frontier - diffLo = loFr := by
            dsimp only [diffLo]; clear *- hlo_le; omega
          have hinv_fin : DualStateInv c U V w base s_dict L_fin
              { mem := s_ps.mem, frontier := loFr } :=
            { hw11 := hw11
              U_pos := hmid11.U_pos
              U_lt := hmid11.U_lt
              V_pos := hmid11.V_pos
              V_le := hmid11.V_le
              wf := ⟨lt_of_le_of_lt hlo_le hwf_pre.1, hwf_ps.2⟩
              base_fr := by dsimp only [loFr]; clear *- hibLo_eq; omega
              hdr := rootStaticHeader_congr hmid11.hdr fun off hoff =>
                hout_ps (base + off) (by clear *- hoff; omega)
                  (base_add_ne (by clear *- hoff; unfold hdrNSrc; omega))
                  (base_add_ne (by clear *- hoff; unfold hdrMSrc; omega))
                  (base_add_ne (by clear *- hoff; unfold hdrNDst; omega))
                  (base_add_ne (by clear *- hoff; unfold hdrMDst; omega))
                  (base_add_ne (by clear *- hoff; unfold hdrStage; omega))
                  (base_add_ne (by clear *- hoff; unfold hdrEpochOps; omega))
                  (base_add_ne (by clear *- hoff; unfold hdrItemHi; omega))
                  (base_add_ne (by clear *- hoff; unfold hdrQHi; omega))
                  (base_add_ne (by clear *- hoff; unfold hdrPhase; omega))
              live_eq := (hout_ps (base + hdrLive) (by dsimp only [hdrLive]; omega)
                (base_add_ne (by decide)) (base_add_ne (by decide)) (base_add_ne (by decide))
                (base_add_ne (by decide)) (base_add_ne (by decide)) (base_add_ne (by decide))
                (base_add_ne (by decide)) (base_add_ne (by decide))
                (base_add_ne (by decide))).trans hlive_eq
              live_le := hmid11.live_le
              ph_le := by dsimp only; rw [hph_ps]; decide
              stg_le := by dsimp only; rw [hst_ps]; decide
              mSrc_eq := by dsimp only; rw [hmS_ps, hnS_ps]; exact hmDst_eq
              cache_src := by dsimp only; rw [hnS_ps]; exact hcache_src_ps
              nSrc_bounds := by dsimp only; rw [hnS_ps]; exact hsched11.nDst_bounds
              sched := by
                dsimp only; rw [ite_eq_left hph_ps]
                refine
                  { stg_zero := hst_ps
                    nDst_zero := hnD_ps
                    mDst_zero := hmD_ps
                    ibLo_eq := by dsimp only; rw [hibL_ps, hmS_ps]; exact hibLo_eq
                    ibHi_eq := by dsimp only; rw [hibH_ps, hibL_ps]
                    qLo_eq := by dsimp only; rw [hqL_ps, hnS_ps]; exact hqLo_eq
                    qHi_eq := by dsimp only; rw [hqH_ps, hqL_ps]
                    elapsed_zero := rfl
                    safe_fr := by
                      dsimp only
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      rw [hnS_ps, hibL_ps, hqL_ps]
                      exact ⟨hidle_safe, hsm_lt_th, rfl⟩
                    ops_evs := fun hpos => by
                      dsimp only [L_fin]
                      rw [hnS_ps] at hpos ⊢
                      rw [hops_ps]
                      simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
                      have he := hevs_d hpos
                      simp only [↓reduceIte] at he
                      have hel2 := hel_le_nDst hpos
                      dsimp only [nDst] at hel2 ⊢
                      clear *- he hel_1 hel2; omega }
              pad_fits := by
                dsimp only; rw [hnS_ps, ite_eq_left hph_ps]
                have hp := hmid11.pad_fits; rw [ite_eq_right (by clear *- hp11; omega)] at hp
                exact lt_of_le_of_lt (Nat.add_le_add_left dualPaddedWords_dst_le base) hp
              ph1_inv := fun h1 => by dsimp only at h1; rw [hph_ps] at h1; cases h1
              ph3_inv := fun h3 => by dsimp only at h3; rw [hph_ps] at h3; cases h3
              ph4_inv := fun h4 => by dsimp only at h4; rw [hph_ps] at h4; cases h4
              pDst_pre := fun h25 _ _ => by dsimp only at h25; rw [hph_ps] at h25; omega
              ph5_inv := fun h5 => by dsimp only at h5; rw [hph_ps] at h5; cases h5
              ph6_inv := fun h6 => by dsimp only at h6; rw [hph_ps] at h6; cases h6
              ph7_inv := fun h7 => by dsimp only at h7; rw [hph_ps] at h7; cases h7
              ph8_inv := fun h8 => by dsimp only at h8; rw [hph_ps] at h8; cases h8
              ph9_inv := fun h9 => by dsimp only at h9; rw [hph_ps] at h9; cases h9
              ph10_inv := fun h10 => by dsimp only at h10; rw [hph_ps] at h10; cases h10
              sl_le7 := fun _ => by
                dsimp only [L_fin]
                unfold dualCapSrc dualPSrc dualMbSrc
                rw [hst_ps, hnS_ps, hph_ps, hibL_ps, hibH_ps, hqL_ps, hqH_ps]
                simp only [↓reduceIte]
                refine ⟨hcap_d, hdict_d, ?_, fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩
                unfold activeSrcIo
                rw [ite_eq_left (by decide : 0 < 3)]
                exact hsl_lo
              sl_67 := fun h67 => by
                dsimp only at h67; rw [hph_ps] at h67; rcases h67 with h | h <;> cases h
              sl_8 := fun h8 => by dsimp only at h8; rw [hph_ps] at h8; cases h8
              sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_ps] at h9; omega }
          rw [hres_cps]
          exact ⟨hfr_ps, hd_le, Nat.sub_le _ _,
            fun addr hlt_b => hout_ps addr
              (by clear *- hlt_b; omega)
              (by dsimp only [hdrNSrc]; clear *- hlt_b; omega)
              (by dsimp only [hdrMSrc]; clear *- hlt_b; omega)
              (by dsimp only [hdrNDst]; clear *- hlt_b; omega)
              (by dsimp only [hdrMDst]; clear *- hlt_b; omega)
              (by dsimp only [hdrStage]; clear *- hlt_b; omega)
              (by dsimp only [hdrEpochOps]; clear *- hlt_b; omega)
              (by dsimp only [hdrItemHi]; clear *- hlt_b; omega)
              (by dsimp only [hdrQHi]; clear *- hlt_b; omega)
              (by dsimp only [hdrPhase]; clear *- hlt_b; omega),
            hmc_cps, L_fin, hpres_fin, hsub_lo ▸ hinv_fin,
            (hsub_lo ▸ hinv_fin).clear_above⟩

/-- Specification of `postRandShrinkProg` for a mutation (`opTag ≠ 0`) already satisfying
`DualPreShrinkInv`. -/
theorem postRandShrinkProg_spec_pre {c U V w base opTag : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (hop_nz : opTag ≠ 0)
    (hpre : DualPreShrinkInv c U V w base s_dict L s) :
    let s_ps := (Memory.spec 0).clientState s (postRandShrinkProg ((base, s.frontier), opTag))
    let k_sh := (Memory.spec 0).clientResult s (postRandShrinkProg ((base, s.frontier), opTag))
    PostRandShrinkPre w ((base, s.frontier), opTag) s ∧
    s_ps.frontier = s.frontier ∧
    k_sh ≤ bulkBatchWhp ∧
    k_sh ≤ s.frontier ∧
    (∀ addr < base, s_ps.mem addr = s.mem addr) ∧
    memoryCost (postRandShrinkProg ((base, s.frontier), opTag)) s ≤ 35 ∧
    ∃ L_post : DualLatent c U V,
      PreservesEpochSeeds False
        (s.mem (base + hdrPhase) = 11 ∧ s_ps.mem (base + hdrPhase) = 0) L L_post ∧
      DualStateInv c U V w base s_dict L_post
        { mem := clear s_ps.mem (s.frontier - k_sh) k_sh,
          frontier := s.frontier - k_sh } := by
  dsimp only
  obtain ⟨hw11, hb192, hw_eq, hvb_w, hqL_w, hqH_w, hf_lo, hf_hi⟩ := dualPreShrinkInv_hdr_fits hpre
  have hwf := hpre.1
  have hnot_rf : ¬(s.mem (base + hdrPhase) = 5 ∧
      s.mem ((if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) + 31) ≤
        s.mem (base + hdrCur)) := by
    rintro ⟨hp5, hle⟩
    have hpD : (if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
        dualPDst base s.mem := by
      unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
    rw [hpD] at hle
    exact absurd (lt_of_lt_of_le (hpre.2.2.1 hp5) hle) (Nat.lt_irrefl _)
  have hprs_pre : PostRandShrinkPre w ((base, s.frontier), opTag) s := by
    refine Or.inr ⟨hw11, hb192, hwf.1, fun hp5 hle => absurd ⟨hp5, hle⟩ hnot_rf, ?_⟩
    dsimp only
    by_cases hp5 : s.mem (base + hdrPhase) = 5
    · rw [ite_eq_left hp5, ite_eq_right (fun hle => hnot_rf ⟨hp5, hle⟩)]
      exact ⟨hw_eq, hvb_w, hqL_w, hqH_w, hf_lo, hf_hi⟩
    · rw [ite_eq_right hp5]
      exact ⟨hw_eq, hvb_w, hqL_w, hqH_w, hf_lo, hf_hi⟩
  obtain ⟨hst_prs, hres_prs, hmc_prs⟩ := postRandShrinkProg_eval base s.frontier opTag s
  dsimp only at hst_prs hres_prs hmc_prs
  rw [ite_eq_right hop_nz, ite_eq_right hnot_rf] at hst_prs hres_prs
  rw [ite_eq_right hop_nz, ite_eq_right hnot_rf, ite_eq_right hnot_rf] at hmc_prs
  obtain ⟨hfr_cps, hk_b, hk_fr, hout_cps, hmc_cps, L_post, hpres, _, hinv_cl⟩ :=
    calcPostShrinkProg_spec hpre
  rw [hst_prs, hres_prs]
  exact ⟨hprs_pre, hfr_cps, hk_b, hk_fr, hout_cps, by clear *- hmc_prs hmc_cps; omega,
    L_post, hpres, hinv_cl⟩

/-- Specification of `postRandShrinkProg` at `ph = 5` completion (`endOff = offBM`), running both
`finishRandFillProg` (`seedsDst := extractEpochSeeds ...`) and `calcPostShrinkProg`. -/
theorem postRandShrinkProg_spec {c U V w base opTag : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (hop_nz : opTag ≠ 0)
    (h : DualMidInv c U V w base s_dict L s)
    (hp5 : s.mem (base + hdrPhase) = 5)
    (hdone : s.mem (dualPDst base s.mem + 31) ≤ s.mem (base + hdrCur)) :
    let nDst := s.mem (base + hdrNDst)
    let metaDst := dualMbDst base s.mem
    let mask := 2 ^ (redWidthWhp U - 1) - 1
    let mem_masked := Function.update
      (Function.update s.mem (metaDst + 32) (s.mem (metaDst + 32) &&& mask))
      (metaDst + offFpHash c w nDst) (s.mem (metaDst + offFpHash c w nDst) &&& mask)
    let seedsDst := extractEpochSeeds c U w nDst metaDst mem_masked
    let L_rf : DualLatent c U V :=
      { L with
        slotDst := ⟨nDst, fun _ => none, seedsDst, []⟩
        elapsed := L.elapsed + 1 }
    let s_ps := (Memory.spec 0).clientState s (postRandShrinkProg ((base, s.frontier), opTag))
    let k_sh := (Memory.spec 0).clientResult s (postRandShrinkProg ((base, s.frontier), opTag))
    PostRandShrinkPre w ((base, s.frontier), opTag) s ∧
    s_ps.frontier = s.frontier ∧
    k_sh ≤ bulkBatchWhp ∧
    k_sh ≤ s.frontier ∧
    (∀ addr < base, s_ps.mem addr = s.mem addr) ∧
    memoryCost (postRandShrinkProg ((base, s.frontier), opTag)) s ≤ 115 ∧
    DualStateInv c U V w base s_dict L_rf
      { mem := clear s_ps.mem (s.frontier - k_sh) k_sh,
        frontier := s.frontier - k_sh } := by
  dsimp only
  obtain ⟨hpre_rf, hfr_rf, hout_rf, hmc_rf, _, hpre_sh⟩ := finishRandFillProg_spec h hp5 hdone
  obtain ⟨hw11, hb192, hw_eq1, hvb_w1, hqL_w1, hqH_w1, hf_lo1, hf_hi1⟩ :=
    dualPreShrinkInv_hdr_fits hpre_sh
  have hpD : (if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
      dualPDst base s.mem := by
    unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
  have hdone_if : s.mem ((if s.mem (base + hdrStage) = 0 then base + hdrPBase1
      else base + hdrPBase0) + 31) ≤ s.mem (base + hdrCur) := by
    rwa [hpD]
  have hprs_pre : PostRandShrinkPre w ((base, s.frontier), opTag) s := by
    refine Or.inr ⟨hw11, h.base_fr, h.wf.1, fun _ _ => hpre_rf, ?_⟩
    dsimp only
    rw [ite_eq_left hp5, ite_eq_left hdone_if]
    exact ⟨hw_eq1, hvb_w1, hqL_w1, hqH_w1, hf_lo1, hf_hi1⟩
  obtain ⟨hst_prs, hres_prs, hmc_prs⟩ := postRandShrinkProg_eval base s.frontier opTag s
  dsimp only at hst_prs hres_prs hmc_prs
  rw [ite_eq_right hop_nz, ite_eq_left ⟨hp5, hdone_if⟩] at hst_prs hres_prs
  rw [ite_eq_right hop_nz, ite_eq_left ⟨hp5, hdone_if⟩, ite_eq_left ⟨hp5, hdone_if⟩] at hmc_prs
  set s_rf := (Memory.spec 0).clientState s (finishRandFillProg base)
  set s_ps := (Memory.spec 0).clientState s (postRandShrinkProg ((base, s.frontier), opTag))
  set k_sh := (Memory.spec 0).clientResult s (postRandShrinkProg ((base, s.frontier), opTag))
  have hph_rf : s_rf.mem (base + hdrPhase) = 6 := by
    obtain ⟨hst_e, _⟩ := finishRandFillProg_eval base s
    dsimp only [s_rf]
    rw [hst_e]; exact Function.update_self ..
  obtain ⟨hfr_cps, hk_b, hk_fr, hout_cps, hmc_cps, _, _, _, _⟩ :=
    calcPostShrinkProg_spec hpre_sh
  have hs_ps_eq :
      s_ps = (Memory.spec 0).clientState s_rf (calcPostShrinkProg (base, s_rf.frontier)) := by
    rw [hst_prs, hfr_rf]
  have hk_sh_eq :
      k_sh = (Memory.spec 0).clientResult s_rf (calcPostShrinkProg (base, s_rf.frontier)) := by
    rw [hres_prs, hfr_rf]
  have hmc_cps_eq : memoryCost (calcPostShrinkProg (base, s.frontier)) s_rf ≤ 31 := by
    rw [← hfr_rf]; exact hmc_cps
  -- At `ph = 6`, `calcPostShrinkProg` is read-only (`s_ps = s_rf`) and `DualPreShrinkInv` gives
  -- `L_rf`.
  have hinv_rf : DualStateInv c U V w base s_dict
      { L with
        slotDst := ⟨s.mem (base + hdrNDst), fun _ => none,
          extractEpochSeeds c U w (s.mem (base + hdrNDst)) (dualMbDst base s.mem)
            (Function.update
              (Function.update s.mem (dualMbDst base s.mem + 32)
                (s.mem (dualMbDst base s.mem + 32) &&& (2 ^ (redWidthWhp U - 1) - 1)))
              (dualMbDst base s.mem + offFpHash c w (s.mem (base + hdrNDst)))
              (s.mem (dualMbDst base s.mem + offFpHash c w (s.mem (base + hdrNDst))) &&&
                (2 ^ (redWidthWhp U - 1) - 1))), []⟩
        elapsed := L.elapsed + 1 }
      { mem := clear s_ps.mem (s.frontier - k_sh) k_sh,
        frontier := s.frontier - k_sh } := by
    obtain ⟨_, _, _, hbr6⟩ := hpre_sh
    rw [hph_rf, ite_eq_right (by decide : ¬(6 < 2)), ite_eq_right (by decide : 6 ≠ 2),
      ite_eq_left (by decide : 6 ≤ 10)] at hbr6
    obtain ⟨hhi_le, _, hinv6⟩ := hbr6
    have hw_pos : 0 < w := by clear *- hw11; omega
    obtain ⟨hst_c6, hres_c6, _⟩ := calcPostShrinkProg_eval (curFr := s_rf.frontier)
      (hw_eq1 ▸ hw_pos)
    dsimp only at hst_c6 hres_c6
    rw [hw_eq1, hinv6.live_eq, hinv6.hdr.2.2.2.2.1, hph_rf] at hst_c6 hres_c6
    rw [ite_eq_right (fun h11 => absurd h11.1 (by decide))] at hst_c6
    rw [ite_eq_right (by decide : ¬(6 < 2)), ite_eq_right (by decide : 6 ≠ 11)] at hres_c6
    have hs_ps_rf : s_ps = s_rf := hs_ps_eq.trans hst_c6
    have hsub6 : s.frontier - k_sh =
        s_rf.mem (base + hdrItemHi) +
          pairStreamWords (Dictionary.dom s_dict).card (s_rf.mem (base + hdrQHi))
            (valBits V) w := by
      rw [hk_sh_eq, hres_c6, hfr_rf]
      rw [hfr_rf] at hhi_le
      clear *- hhi_le; omega
    rw [hs_ps_rf, hsub6]
    exact hinv6.clear_above
  exact ⟨hprs_pre, (congrArg Memory.State.frontier hs_ps_eq).trans (hfr_cps.trans hfr_rf),
    hk_sh_eq ▸ hk_b, hfr_rf ▸ (hk_sh_eq ▸ hk_fr),
    fun addr hlt => ((congrArg (fun st => st.mem addr) hs_ps_eq).trans
      (hout_cps addr hlt)).trans (hout_rf addr hlt),
    by clear *- hmc_prs hmc_rf hmc_cps_eq; omega,
    hinv_rf⟩

/-! ## Section 4: Unified `stepOpProg` Query & Mutation Specifications -/

/-- Full `prepGrowProg` + `stepOpProg` + `postRandShrinkProg` specification for `opTag = 0`
(`query u`): deterministic read-only execution (`k_grow = 0, rArgs = (0, (0, 0)), k_sh = 0`). -/
theorem stepOpProg_query_spec {c U V w base v_val : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s) (u : Fin U) :
    let ph := s.mem (base + hdrPhase)
    PrepGrowPre w (((base, s.frontier), 0), u.val) s ∧
    (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), 0), u.val)) = s ∧
    (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), 0), u.val)) = 0 ∧
    memoryCost (prepGrowProg (((base, s.frontier), 0), u.val)) s ≤ 5 ∧
    StepOpPre w (((base, s.frontier), 0), (u.val, v_val)) s ∧
    (Memory.spec 0).clientState s (stepOpProg (((base, s.frontier), 0), (u.val, v_val))) = s ∧
    (Memory.spec 0).clientResult s (stepOpProg (((base, s.frontier), 0), (u.val, v_val))) =
      ((match s_dict u with | none => (0, 0) | some v => (1, v)), (0, (0, 0))) ∧
    (L.ActiveGood ph →
      memoryCost (stepOpProg (((base, s.frontier), 0), (u.val, v_val))) s ≤
        2 * epochStepCost c + 35) ∧
    PostRandShrinkPre w ((base, s.frontier), 0) s ∧
    (Memory.spec 0).clientState s (postRandShrinkProg ((base, s.frontier), 0)) = s ∧
    (Memory.spec 0).clientResult s (postRandShrinkProg ((base, s.frontier), 0)) = 0 ∧
    memoryCost (postRandShrinkProg ((base, s.frontier), 0)) s = 0 := by
  dsimp only
  obtain ⟨hpre_pg, hpre_uq, hst_uq, hres_uq, hmc_uq⟩ := userQueryProg_spec h u
  have hw11 := h.hw11
  have hpg_q := prepGrowProg_query_eval base s.frontier u.val s
  obtain ⟨hst_so, hres_so, hmc_so⟩ := stepOpProg_eval base s.frontier 0 u.val v_val s
  simp only [↓reduceIte] at hst_so hres_so hmc_so
  have hprs_ev := postRandShrinkProg_eval base s.frontier 0 s
  dsimp only at hprs_ev
  simp only [↓reduceIte, Nat.le_zero_eq] at hprs_ev
  exact ⟨hpre_pg, hpg_q.1, hpg_q.2.1, by rw [hpg_q.2.2]; decide,
    by unfold StepOpPre; exact ⟨by clear *- hw11; omega, by rw [ite_eq_left rfl]; exact hpre_uq⟩,
    hst_so.trans hst_uq, hres_so.trans (congrArg (·, (0, (0, 0))) hres_uq),
    fun hg => by rw [hmc_so]; have := hmc_uq hg; omega,
    Or.inl rfl, hprs_ev.1, hprs_ev.2.1, hprs_ev.2.2⟩

/-- Full `prepGrowProg` + `growZero` + `stepOpProg` specification for `opTag ≠ 0` (`insert u v` or
`delete u`), combining `prepGrow_userMutate_spec` with `bgTickProg_spec` across phases `0..11`. -/
theorem stepOpProg_mutate_spec {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsucc_fits' :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w
        (Dictionary.dom s_dict').card < 2 ^ w)
    (hpad_fits' :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
        (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc)
         else s.mem (base + hdrNDst)) (Dictionary.dom s_dict').card < 2 ^ w) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let ph := s.mem (base + hdrPhase)
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let s_mid := (Memory.spec 0).clientState s_grow (userMutateProg ((base, opTag), (u.val, v_val)))
    let L_mid := L.applyFG ph opTag u v
    let s_tick := (Memory.spec 0).clientState s_grow
      (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val)))
    let res_so := (Memory.spec 0).clientResult s_grow
      (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val)))
    PrepGrowPre w (((base, s.frontier), opTag), u.val) s ∧
    s_prep.frontier = s.frontier ∧
    k_grow ≤ bulkBatchWhp ∧
    memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s ≤ 40 ∧
    s_grow.frontier ≤ base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
      (if ph = 0 then s.mem (base + hdrNSrc) else s.mem (base + hdrNDst))
      (Dictionary.dom s_dict).card ∧
    Memory.WellFormed w s_grow ∧
    StepOpPre w (((base, s_grow.frontier), opTag), (u.val, v_val)) s_grow ∧
    res_so.1 = (0, 0) ∧
    (∀ addr < base, s_grow.mem addr = s.mem addr) ∧
    (∀ addr < base, s_mid.mem addr = s.mem addr) ∧
    DualMidInv c U V w base s_dict' L_mid s_mid ∧
    DualPostTickInv c U V w base s_dict' L_mid s_mid s_tick res_so.2 ∧
    memoryCost (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) s_grow =
      memoryCost (userMutateProg ((base, opTag), (u.val, v_val))) s_grow +
        memoryCost (bgTickProg (base, s_mid.frontier)) s_mid ∧
    ((ph ≤ 7 → L_mid.slotSrc.GoodCovers) →
      (ph = 8 → L_mid.slotSrc.GoodCovers ∧ L_mid.slotDst.GoodCovers) →
      (9 ≤ ph → L_mid.slotDst.GoodCovers) →
      memoryCost (userMutateProg ((base, opTag), (u.val, v_val))) s_grow ≤
        2 * epochStepCost c + 80) := by
  dsimp only
  obtain ⟨hpre_pg, hfr_prep, hk_grow, hmc_pg, hfr_grow_pad, hwf_grow, hpre_um, hfr_mid,
    hout_grow, hout_mid, hmid, hmc_um⟩ :=
    prepGrow_userMutate_spec h hop_nz u v hv_eq hpad_fits'
  set s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
  set k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  set s_mid := (Memory.spec 0).clientState s_grow (userMutateProg ((base, opTag), (u.val, v_val)))
  obtain ⟨hpre_bg, hpost_tick⟩ := bgTickProg_spec hmid hsucc_fits'
  obtain ⟨hst_so, hres_so, hmc_so⟩ := stepOpProg_eval base s_grow.frontier opTag u.val v_val s_grow
  rw [ite_eq_right hop_nz] at hst_so hres_so hmc_so
  have hw1 : 1 ≤ w := by have := h.hw11; omega
  have hpre_so : StepOpPre w (((base, s_grow.frontier), opTag), (u.val, v_val)) s_grow := by
    unfold StepOpPre
    exact ⟨hw1, by rw [ite_eq_right hop_nz]; exact ⟨hpre_um, hfr_mid ▸ hpre_bg⟩⟩
  rw [hst_so, hres_so, hmc_so]
  dsimp only
  rw [← hfr_mid]
  exact ⟨hpre_pg, hfr_prep, hk_grow, hmc_pg, hfr_grow_pad, hwf_grow, hpre_so, rfl,
    hout_grow, hout_mid, hmid, hpost_tick, rfl, hmc_um⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
