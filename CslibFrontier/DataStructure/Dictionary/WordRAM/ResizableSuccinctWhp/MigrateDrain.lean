/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.MigrateCongr

/-!
# Phases `6..7` Directory and Tail Initialization Congruence (`MigrateDrain`)

This module steps the dual-epoch cross-seed congruence invariant across Phases `6` and `7` up to
the `7 → 8` draining entry of the deamortized worst-case WHP resizable succinct dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]):

1. **Phase `8` coupling (`Coupled8Region`, `Coupled8`):**
   Pairs `SchedEq` with `SlotStateCoupled` on `Coupled8Region` and `pagedSlotIo 0`.
2. **Phases `6..7` (`Coupled67 → Coupled67 / Coupled8`, `coupled67_mutate_step`):**
   Steps `Coupled67` across `6 → 6`, `6 → 7`, and `7 → 7` mutations, and establishes `Coupled8`
   upon `7 → 8` (`finishInitTailProg`). Phase-`8` draining congruence (`coupled8_mutate_step`) is
   proved in `MigratePhase8`.

## Main definitions

* `Coupled8Region`: Phase-`8` source-slot metadata + parameter-table envelope (`SlotSrcMetaRegion`).
* `Coupled8`: Phase-`8` draining coupling (`SchedEq` + `SlotStateCoupled` on `pagedSlotIo 0`).

## Main results

* `coupled67_mutate_step`: Phases `6..7` mutation congruence (`Coupled67` / `7 → 8` `Coupled8`).

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

/-! ## Section 1: `Coupled8` and Phases `6..7` Mutation Congruence (`coupled67_mutate_step`) -/

/-- Source non-page metadata + `pSrc` 64-word parameter-table envelope in Phase `8`. -/
@[expose] def Coupled8Region (c w base : ℕ) (m : ℕ → ℕ) (addr : ℕ) : Prop :=
  SlotSrcMetaRegion c w (dualPSrc base m) (dualMbSrc base m) (dualCapSrc base m) addr

/-- Phase-`8` draining coupling: `SchedEq` plus `SlotStateCoupled` on `Coupled8Region` and
`pagedSlotIo 0 (dualPgHost c V w base nLive s₁.mem)`. -/
@[expose] def Coupled8 (c V w base nLive : ℕ) (s₁ s₂ : Memory.State) : Prop :=
  SchedEq base s₁ s₂ ∧
  SlotStateCoupled (Coupled8Region c w base s₁.mem)
    (pagedSlotIo 0 (dualPgHost c V w base nLive s₁.mem))
    (s₁.mem (dualMbSrc base s₁.mem + 1)) s₁ s₂

theorem coupled8Region_of_hdr_eq {c w base : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hst : m₁ (base + hdrStage) = m₂ (base + hdrStage))
    (hnS : m₁ (base + hdrNSrc) = m₂ (base + hdrNSrc))
    (hnD : m₁ (base + hdrNDst) = m₂ (base + hdrNDst))
    (hpad : m₁ (base + hdrPad) = m₂ (base + hdrPad)) :
    Coupled8Region c w base m₁ = Coupled8Region c w base m₂ := by
  funext addr
  unfold Coupled8Region dualPSrc dualMbSrc dualCapSrc
  rw [hst, hnS, hnD, hpad]

private theorem coupled67_fg_step_aux {c U V w base opTag v_val k_grow₁ k_grow₂ : ℕ}
    {s_dict : Dictionary.State U} {L₁ L₂ : DualLatent c U V}
    {s₁ s₂ sp₁ sp₂ sr₁ sr₂ sm₁ sm₂ : Memory.State}
    (h₁ : DualStateInv c U V w base s_dict L₁ s₁)
    (h₂ : DualStateInv c U V w base s_dict L₂ s₂)
    (hc67 : Coupled67 c w base s₁ s₂)
    (hp67 : s₁.mem (base + hdrPhase) = 6 ∨ s₁.mem (base + hdrPhase) = 7)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsp₁ : sp₁ =
      (Memory.spec 0).clientState s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)))
    (hkg₁ : k_grow₁ =
      (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)))
    (hsp₂ : sp₂ =
      (Memory.spec 0).clientState s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val)))
    (hkg₂ : k_grow₂ =
      (Memory.spec 0).clientResult s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val)))
    (hsr₁ : sr₁ = (Memory.spec 0).clientState { mem := sp₁.mem, frontier := s₁.frontier + k_grow₁ }
      (userMutateRawProg ((base, opTag), (u.val, v_val))))
    (hsr₂ : sr₂ = (Memory.spec 0).clientState { mem := sp₂.mem, frontier := s₂.frontier + k_grow₂ }
      (userMutateRawProg ((base, opTag), (u.val, v_val))))
    (hsm₁ : sm₁ = (Memory.spec 0).clientState { mem := sp₁.mem, frontier := s₁.frontier + k_grow₁ }
      (userMutateProg ((base, opTag), (u.val, v_val))))
    (hsm₂ : sm₂ = (Memory.spec 0).clientState { mem := sp₂.mem, frontier := s₂.frontier + k_grow₂ }
      (userMutateProg ((base, opTag), (u.val, v_val)))) :
    k_grow₁ = k_grow₂ ∧ Coupled67 c w base sm₁ sm₂ := by
  have hsch := hc67.1
  have hp47_₁ : 4 ≤ s₁.mem (base + hdrPhase) ∧ s₁.mem (base + hdrPhase) ≤ 7 := by
    rcases hp67 with h | h <;> (clear *- h; omega)
  have hp_s₂ : s₂.mem (base + hdrPhase) = s₁.mem (base + hdrPhase) :=
    (hsch.2 hdrPhase (by decide) (by decide)).symm
  have hp47_₂ : 4 ≤ s₂.mem (base + hdrPhase) ∧ s₂.mem (base + hdrPhase) ≤ 7 :=
    hp_s₂ ▸ hp47_₁
  obtain ⟨hkg_eq0, _, _⟩ := schedEq_foreground h₁ h₂ hsch hop_nz u v hv_eq
  have hkg_eq : k_grow₁ = k_grow₂ := hkg₁.trans (hkg_eq0.trans hkg₂.symm)
  set sg₁ : Memory.State := { mem := sp₁.mem, frontier := s₁.frontier + k_grow₁ }
  set sg₂ : Memory.State := { mem := sp₂.mem, frontier := s₂.frontier + k_grow₂ }
  have hw_pos : 0 < w := by have := h₁.hw11; omega
  have hu1_1 : s₁.mem (base + hdrU1) + 1 ≤ 2 ^ w := by
    have := h₁.hdr.1; have := h₁.U_pos; have := h₁.U_lt; omega
  have hnL_1 : s₁.mem (base + hdrLive) ≤ s₁.mem (base + hdrU1) + 1 := by
    rw [h₁.live_eq, h₁.hdr.1]; have := h₁.U_pos; have := h₁.live_le; omega
  have hu1_2 : s₂.mem (base + hdrU1) + 1 ≤ 2 ^ w := by
    have := h₂.hdr.1; have := h₂.U_pos; have := h₂.U_lt; omega
  have hnL_2 : s₂.mem (base + hdrLive) ≤ s₂.mem (base + hdrU1) + 1 := by
    rw [h₂.live_eq, h₂.hdr.1]; have := h₂.U_pos; have := h₂.live_le; omega
  have hpg_ev₁ := (prepGrowProg_eval (opTag := opTag) (u_val := u.val) hop_nz hw_pos
    h₁.hdr.2.2.1 hu1_1 hnL_1).1
  have hpg_ev₂ := (prepGrowProg_eval (opTag := opTag) (u_val := u.val) hop_nz hw_pos
    h₂.hdr.2.2.1 hu1_2 hnL_2).1
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hpg_ev₁ hpg_ev₂
  rw [← hsp₁] at hpg_ev₁
  rw [← hsp₂, ← hsch.2 hdrLive (by decide) (by decide),
    ← hsch.2 hdrU1 (by decide) (by decide)] at hpg_ev₂
  have hsg_agree : ∀ addr, Coupled67Region c w base s₁.mem addr → sg₁.mem addr = sg₂.mem addr := by
    intro addr hreg
    dsimp only [sg₁, sg₂]
    rw [hpg_ev₁, hpg_ev₂]
    dsimp only [Memory.State.mem]
    split_ifs
    · by_cases h1 : addr = base + hdrPBase1 + 60
      · subst h1; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h1, Function.update_of_ne h1]
        by_cases h0 : addr = base + hdrPBase0 + 60
        · subst h0; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne h0, Function.update_of_ne h0]
          exact hc67.2 addr hreg
    · exact hc67.2 addr hreg
  have hsg_fr : sg₁.frontier = sg₂.frontier := by
    dsimp only [sg₁, sg₂]; rw [hsch.1, hkg_eq]
  have hfg₁ := fg_direct_rw_of_47 (v_val := v_val) h₁ hop_nz u v hp47_₁
  have hfg₂ := fg_direct_rw_of_47 (v_val := v_val) h₂ hop_nz u v hp47_₂
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hfg₁ hfg₂
  rw [← hsp₁, ← hkg₁, ← hsr₁] at hfg₁
  rw [← hsp₂, ← hkg₂, ← hsr₂] at hfg₂
  have hpSrc_eq : dualPSrc base s₂.mem = dualPSrc base s₁.mem := by
    unfold dualPSrc; rw [hsch.2 hdrStage (by decide) (by decide)]
  have hact_eq :
      (if opTag = 1 then epochInsertProg ((dualPSrc base s₂.mem, u.val), v_val)
       else epochDeleteProg (dualPSrc base s₂.mem, u.val)) =
      (if opTag = 1 then epochInsertProg ((dualPSrc base s₁.mem, u.val), v_val)
       else epochDeleteProg (dualPSrc base s₁.mem, u.val)) := by rw [hpSrc_eq]
  rw [hact_eq] at hfg₂
  have hsub_reg : ∀ addr,
      SlotDirectRegion c w (dualPSrc base s₁.mem) (dualMbSrc base s₁.mem) (dualCapSrc base s₁.mem)
        (directSlotIo w (valBits V) base (s₁.mem (base + hdrItemHi)) (s₁.mem (base + hdrQHi))
          (if opTag = 1 then min ((Dictionary.dom s_dict).card + 1) U
           else (Dictionary.dom s_dict).card)) addr →
      Coupled67Region c w base s₁.mem addr := by
    intro addr hsd
    have hdisj := srcDirect_disj_dstMeta (opTag := opTag) h₁ hp47_₁ addr hsd
    exact ⟨hdisj.1, hdisj.2.1, hdisj.2.2⟩
  obtain ⟨_, hsr_fr, hsr_agree⟩ :=
    hfg₁.2.step_agree (s₂ := sg₂) (fun _ h => h) hsub_reg hsg_fr hsg_agree
  rw [← hfg₁.1, ← hfg₂.1] at hsr_fr hsr_agree
  have hsr_ph₁ : sr₁.mem (base + hdrPhase) = s₁.mem (base + hdrPhase) := by
    have hsetup₁ := fgSetup_of_dualStateInv h₁ hop_nz u v
    have hlow₁ : sg₁.mem (base + hdrPhase) = s₁.mem (base + hdrPhase) := by
      dsimp only [sg₁]; rw [hsp₁]; exact hsetup₁.grow_low hdrPhase (by decide)
    have hnr : ¬SlotDirectRegion c w (dualPSrc base s₁.mem) (dualMbSrc base s₁.mem)
        (dualCapSrc base s₁.mem)
        (directSlotIo w (valBits V) base (s₁.mem (base + hdrItemHi)) (s₁.mem (base + hdrQHi))
          (if opTag = 1 then min ((Dictionary.dom s_dict).card + 1) U
           else (Dictionary.dom s_dict).card)) (base + hdrPhase) := by
      rintro (⟨h1, _⟩ | hmeta | hio)
      · unfold dualPSrc at h1; dsimp only [hdrPBase0, hdrPBase1, hdrPhase] at h1
        split_ifs at h1 <;> (clear *- h1; omega)
      · unfold slotOwnsNonPageMeta dualMbSrc dualCapSrc at hmeta
        dsimp only [hdrPhase, hdrSmallMeta0] at hmeta
        split_ifs at hmeta <;>
          (rcases hmeta with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> (clear *- h1; omega))
      · simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
          ↓reduceIte] at hio
        have hib : base + 192 ≤ s₁.mem (base + hdrItemHi) :=
          hsetup₁.ibLo_ge.trans hsetup₁.ibHi_ge_ibLo.1
        have h1 := hio.1; dsimp only [hdrPhase] at h1; clear *- hib h1; omega
    rw [hfg₁.1, hfg₁.2.out₁ _ hnr, hlow₁]
  have hph_in_reg : Coupled67Region c w base s₁.mem (base + hdrPhase) := by
    have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := 0) h₁ (by clear *- hp47_₁; omega)
      (by clear *- hp47_₁; omega)
    refine ⟨?_, fun hpg => by have := (hdisj_pg _ hpg).1; dsimp only [hdrPhase] at this; omega, ?_⟩
    · unfold slotOwnsNonPageMeta dualMbDst
      rw [ite_eq_left (by clear *- hp47_₁; omega)]
      dsimp only [hdrPhase, hdrSmallMeta1]
      split_ifs <;> (rintro (⟨h1, _⟩ | ⟨_, h1, _⟩) <;> (clear *- h1; omega))
    · rintro ⟨hd0, hlo, _⟩
      unfold dualMbDst at hlo
      rw [ite_eq_left (by clear *- hp47_₁; omega), ite_eq_right hd0] at hlo
      dsimp only [hdrPhase] at hlo
      split_ifs at hlo <;> (clear *- hlo; omega)
  have hsr_ph₂ : sr₂.mem (base + hdrPhase) = s₂.mem (base + hdrPhase) :=
    (hsr_agree _ hph_in_reg).symm.trans (hsr_ph₁.trans hp_s₂.symm)
  have hne3_₁ : s₁.mem (base + hdrPhase) ≠ 3 := by clear *- hp47_₁; omega
  have hne10_₁ : s₁.mem (base + hdrPhase) ≠ 10 := by clear *- hp47_₁; omega
  have hsync₁ := syncLive_mem_eq_of_ne3_10 (v_val := v_val) h₁ hop_nz u v hv_eq hne3_₁ hne10_₁
  have hsync₂ := syncLive_mem_eq_of_ne3_10 (v_val := v_val) h₂ hop_nz u v hv_eq
    (hp_s₂ ▸ hne3_₁) (hp_s₂ ▸ hne10_₁)
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hsync₁ hsync₂
  rw [← hsp₁, ← hkg₁, ← hsr₁, ← hsm₁] at hsync₁
  rw [← hsp₂, ← hkg₂, ← hsr₂, ← hsm₂] at hsync₂
  have hsm₁_eq := hsync₁ hsr_ph₁
  have hsm₂_eq := hsync₂ hsr_ph₂
  clear hsync₁ hsync₂ hfg₁ hfg₂ hpg_ev₁ hpg_ev₂
  have hsm_fr : sm₁.frontier = sm₂.frontier := by
    rw [hsm₁_eq, hsm₂_eq]; exact hsr_fr
  have hsm_agree_s₁ : ∀ addr, Coupled67Region c w base s₁.mem addr → sm₁.mem addr = sm₂.mem addr :=
    fun addr hreg => by
      rw [hsm₁_eq, hsm₂_eq]; dsimp only [Memory.State.mem]
      by_cases hp1 : addr = base + hdrPBase1 + 60
      · subst hp1; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hp1, Function.update_of_ne hp1]
        by_cases hp0 : addr = base + hdrPBase0 + 60
        · subst hp0; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hp0, Function.update_of_ne hp0]
          by_cases hl : addr = base + hdrLive
          · subst hl; rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hl, Function.update_of_ne hl]
            exact hsr_agree addr hreg
  have hlow_in_reg : ∀ off < 48, Coupled67Region c w base s₁.mem (base + off) := by
    intro off hoff
    have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := 0) h₁ (by clear *- hp47_₁; omega)
      (by clear *- hp47_₁; omega)
    refine ⟨?_, fun hpg => by have := (hdisj_pg _ hpg).1; clear *- hoff this; omega, ?_⟩
    · unfold slotOwnsNonPageMeta dualMbDst
      rw [ite_eq_left (by clear *- hp47_₁; omega)]
      dsimp only [hdrSmallMeta1]
      split_ifs <;> (rintro (⟨h1, _⟩ | ⟨_, h1, _⟩) <;> (clear *- hoff h1; omega))
    · rintro ⟨hd0, hlo, _⟩
      unfold dualMbDst at hlo
      rw [ite_eq_left (by clear *- hp47_₁; omega), ite_eq_right hd0] at hlo
      split_ifs at hlo <;> (clear *- hoff hlo; omega)
  have hsch_sm : SchedEq base sm₁ sm₂ :=
    ⟨hsm_fr, fun off hoff _ => hsm_agree_s₁ (base + off) (hlow_in_reg off hoff)⟩
  have hsm₁_hdr : ∀ off < 48, off ≠ hdrLive → sm₁.mem (base + off) = s₁.mem (base + off) := by
    intro off hoff hne_l
    have hstep₁ := fgStep_le7_aux h₁ u v hv_eq (fgSetup_of_dualStateInv h₁ hop_nz u v)
      hsp₁ hkg₁ hsm₁ (by clear *- hp47_₁; omega)
    by_cases hsp_o : off = hdrSplit
    · subst hsp_o; exact hstep₁.2.2.2.2.1 hne3_₁ hne10_₁
    · exact hstep₁.2.2.2.1 (base + off) (by clear *- hoff; omega)
        (base_add_ne hne_l) (base_add_ne hsp_o)
  have hreg_sm₁ : Coupled67Region c w base sm₁.mem = Coupled67Region c w base s₁.mem := by
    funext addr
    unfold Coupled67Region dualMbDst dualPgHost dualNHost dualMbHost
    rw [hsm₁_hdr hdrPhase (by decide) (by decide),
      hsm₁_hdr hdrNDst (by decide) (by decide),
      hsm₁_hdr hdrNSrc (by decide) (by decide),
      hsm₁_hdr hdrStage (by decide) (by decide),
      hsm₁_hdr hdrPad (by decide) (by decide),
      hsm₁_hdr hdrItemHi (by decide) (by decide),
      hsm₁_hdr hdrQHi (by decide) (by decide)]
  exact ⟨hkg_eq, hsch_sm, fun addr hreg => hsm_agree_s₁ addr (hreg_sm₁ ▸ hreg)⟩

private theorem finishInitTail_coupled8_aux {c U V w base nLive : ℕ}
    {s_dict : Dictionary.State U} {L₁ L₂ L_post₁ L_post₂ : DualLatent c U V}
    {sm₁ sm₂ st₁ st₂ sp₁ sp₂ : Memory.State} {k_sh : ℕ}
    (hm₁ : DualMidInv c U V w base s_dict L₁ sm₁)
    (hm₂ : DualMidInv c U V w base s_dict L₂ sm₂)
    (hc67 : Coupled67 c w base sm₁ sm₂)
    (hp7₁ : sm₁.mem (base + hdrPhase) = 7)
    (hnLive : nLive = (Dictionary.dom s_dict).card)
    (hst₁ : st₁ = (Memory.spec 0).clientState sm₁ (bgTickProg (base, sm₁.frontier)))
    (hst₂ : st₂ = (Memory.spec 0).clientState sm₂ (bgTickProg (base, sm₂.frontier)))
    (_hksh₁ : k_sh = (Memory.spec 0).clientResult st₁
      (postRandShrinkProg ((base, st₁.frontier), 1)))
    (hsp₁_eq : sp₁ = { mem := clear st₁.mem (st₁.frontier - k_sh) k_sh,
                       frontier := st₁.frontier - k_sh })
    (hsp₂_eq : sp₂ = { mem := clear st₂.mem (st₂.frontier - k_sh) k_sh,
                       frontier := st₂.frontier - k_sh })
    (hsch_post : SchedEq base sp₁ sp₂)
    (hp8_post₁ : sp₁.mem (base + hdrPhase) = 8)
    (h_post₁ : DualStateInv c U V w base s_dict L_post₁ sp₁)
    (h_post₂ : DualStateInv c U V w base s_dict L_post₂ sp₂) :
    Coupled8 c V w base nLive sp₁ sp₂ := by
  subst hnLive
  have hsch_m := hc67.1
  have hp7₂ : sm₂.mem (base + hdrPhase) = 7 :=
    (hsch_m.2 hdrPhase (by decide) (by decide)).symm.trans hp7₁
  have hp8_post₂ : sp₂.mem (base + hdrPhase) = 8 :=
    (hsch_post.2 hdrPhase (by decide) (by decide)).symm.trans hp8_post₁
  have hw_pos : 0 < w := by have := hm₁.hw11; omega
  obtain ⟨hth_h₁, _, _, _, hctx0_₁, hctx1_₁, _, hv_fr₁, hv_m₁⟩ :=
    dualPgHost_eval_valid hm₁ (by clear *- hp7₁; omega) (by clear *- hp7₁; omega)
  obtain ⟨_, _, _, _, hctx0_₂, hctx1_₂, _, _, hv_m₂⟩ :=
    dualPgHost_eval_valid hm₂ (by clear *- hp7₂; omega) (by clear *- hp7₂; omega)
  have hdisj_pg₁ := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) hm₁
    (by clear *- hp7₁; omega) (by clear *- hp7₁; omega)
  have hdisj_pg₂ := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) hm₂
    (by clear *- hp7₂; omega) (by clear *- hp7₂; omega)
  set nLive := (Dictionary.dom s_dict).card
  set nHost := dualNHost base sm₁.mem
  set mbHost := dualMbHost base sm₁.mem
  set ibHi := sm₁.mem (base + hdrItemHi)
  set qHi := sm₁.mem (base + hdrQHi)
  set pgH := dualPgHost c V w base nLive sm₁.mem
  set pgM := hostPageLayout c w nHost mbHost ibHi 0 0 nHost
  have hnH_eq : dualNHost base sm₂.mem = nHost := by
    unfold dualNHost nHost
    rw [← hsch_m.2 hdrNDst (by decide) (by decide), ← hsch_m.2 hdrNSrc (by decide) (by decide)]
  have hmbH_eq : dualMbHost base sm₂.mem = mbHost := by
    unfold dualMbHost mbHost
    rw [← hsch_m.2 hdrNDst (by decide) (by decide),
      ← hsch_m.2 hdrStage (by decide) (by decide),
      ← hsch_m.2 hdrPad (by decide) (by decide)]
  have hibH_eq₂ : sm₂.mem (base + hdrItemHi) = ibHi :=
    (hsch_m.2 hdrItemHi (by decide) (by decide)).symm
  have hqH_eq₂ : sm₂.mem (base + hdrQHi) = qHi :=
    (hsch_m.2 hdrQHi (by decide) (by decide)).symm
  have hpgH_m₂ : dualPgHost c V w base nLive sm₂.mem = pgH := by
    dsimp only [pgH]; unfold dualPgHost
    rw [hnH_eq, hmbH_eq, hibH_eq₂, hqH_eq₂]
  have hpgM_m₂ : hostPageLayout c w (dualNHost base sm₂.mem) (dualMbHost base sm₂.mem)
      (sm₂.mem (base + hdrItemHi)) 0 0 (dualNHost base sm₂.mem) = pgM := by
    dsimp only [pgM]; rw [hnH_eq, hmbH_eq, hibH_eq₂]
  rw [hpgH_m₂] at hctx0_₂ hdisj_pg₂
  rw [hpgM_m₂] at hctx1_₂ hv_m₂
  have hm_ofCtx : PageArenaLayout.ofCtx pgM.toCtx = pgM := PageArenaLayout.ofCtx_toCtx pgM
  have hh_ofCtx : PageArenaLayout.ofCtx pgH.toCtx = pgH := PageArenaLayout.ofCtx_toCtx pgH
  set cur := sm₁.mem (base + hdrCur)
  set nSnap := sm₁.mem (base + hdrNSnap)
  set qSnap := sm₁.mem (base + hdrQSnap)
  have hcur_m₂ : sm₂.mem (base + hdrCur) = cur := (hsch_m.2 hdrCur (by decide) (by decide)).symm
  have hns_m₂ : sm₂.mem (base + hdrNSnap) = nSnap :=
    (hsch_m.2 hdrNSnap (by decide) (by decide)).symm
  have hqs_m₂ : sm₂.mem (base + hdrQSnap) = qSnap :=
    (hsch_m.2 hdrQSnap (by decide) (by decide)).symm
  obtain ⟨hns_h₁, hqSnap_eq₁, hdir_pre₁, ⟨_, _, hcur_lt8₁, _, _⟩, htail_pre₁⟩ := hm₁.ph7_inv hp7₁
  obtain ⟨_, _, hdir_pre₂, _, htail_pre₂⟩ := hm₂.ph7_inv hp7₂
  rw [hpgH_m₂] at hdir_pre₂
  rw [hpgH_m₂, hcur_m₂, hqs_m₂] at htail_pre₂
  have htb_sp₁ := pageInitTailBatchProg_spec (L := pgM) (n_0 := nSnap) (cur := cur) (s := sm₁)
    hv_m₁ hns_h₁ hcur_lt8₁.le tailBatchWhp
  have htb_sp₂ := pageInitTailBatchProg_spec (L := pgM) (n_0 := nSnap) (cur := cur) (s := sm₂)
    hv_m₂ hns_h₁ hcur_lt8₁.le tailBatchWhp
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at htb_sp₁ htb_sp₂
  set tb := pageInitTailBatchProg (((pgM.toCtx, nSnap), cur), tailBatchWhp)
  set s2₁ := (Memory.spec 0).clientState sm₁ tb
  set s2₂ := (Memory.spec 0).clientState sm₂ tb
  set cur' := (Memory.spec 0).clientResult sm₁ tb
  have hcur'_res₂ : (Memory.spec 0).clientResult sm₂ tb = cur' :=
    htb_sp₂.2.1.trans htb_sp₁.2.1.symm
  have hs2_pg₁ : ∀ a, ¬pgH.OwnsMetaAddr a → s2₁.mem a = sm₁.mem a := fun a ha =>
    htb_sp₁.2.2.2.2.1 a (fun htl => ha (Or.inr (Or.inr htl)))
  have hs2_pg₂ : ∀ a, ¬pgH.OwnsMetaAddr a → s2₂.mem a = sm₂.mem a := fun a ha =>
    htb_sp₂.2.2.2.2.1 a (fun htl => ha (Or.inr (Or.inr htl)))
  have hs2_hdr₁ : ∀ off < 192, s2₁.mem (base + off) = sm₁.mem (base + off) := fun off h192 =>
    hs2_pg₁ (base + off) (fun hpg => by have := (hdisj_pg₁ _ hpg).1; clear *- h192 this; omega)
  have hs2_hdr₂ : ∀ off < 192, s2₂.mem (base + off) = sm₂.mem (base + off) := fun off h192 =>
    hs2_pg₂ (base + off) (fun hpg => by have := (hdisj_pg₂ _ hpg).1; clear *- h192 this; omega)
  have hbgev₁ := (bgTickProg_eval base sm₁.frontier sm₁).1
  have hbgev₂ := (bgTickProg_eval base sm₂.frontier sm₂).1
  simp only [hp7₁, hp7₂, Nat.reduceEqDiff, ↓reduceIte] at hbgev₁ hbgev₂
  have httev₁ := (tickInitTailProg_eval base sm₁).1
  have httev₂ := (tickInitTailProg_eval base sm₂).1
  rw [hctx1_₁, hm_ofCtx] at httev₁
  rw [hctx1_₂, hm_ofCtx, hns_m₂, hcur_m₂, hcur'_res₂] at httev₂
  have hnlt8 : ¬(cur' < 8 * pgM.pgB) := by
    intro hlt8
    rw [hbgev₁, httev₁, ite_eq_left hlt8] at hst₁
    have hph7_st₁ : st₁.mem (base + hdrPhase) = 7 := by
      rw [hst₁]; dsimp only [Memory.State.mem]
      rw [Function.update_of_ne (base_add_ne (by decide))]
      exact (hs2_hdr₁ hdrPhase (by decide)).trans hp7₁
    have hb192 : base + 192 ≤ st₁.frontier - k_sh := by
      have := h_post₁.base_fr; rw [hsp₁_eq] at this; exact this
    have hp7_sp₁ : sp₁.mem (base + hdrPhase) = 7 := by
      rw [hsp₁_eq]; dsimp only [Memory.State.mem]
      rw [clear_of_not_owns
        (by simp only [Block.Owns]; dsimp only [hdrPhase]; clear *- hb192; omega)]
      exact hph7_st₁
    exact absurd (hp7_sp₁.symm.trans hp8_post₁) (by decide)
  have hcur'_eq8 : cur' = 8 * pgH.pgB := by
    have h1 := htb_sp₁.2.1
    have hpgB_eq : pgM.pgB = pgH.pgB := rfl
    rw [hpgB_eq] at h1 hnlt8
    have hle := min_le_left (8 * pgH.pgB) (cur + tailBatchWhp)
    clear *- h1 hnlt8 hle; omega
  have hctx0_s2₁ : (Memory.spec 0).clientResult s2₁ (loadHostCtxProg (base, 0)) = pgH.toCtx := by
    rw [← hctx0_₁, (loadHostCtxProg_eval base 0 s2₁).2.1, (loadHostCtxProg_eval base 0 sm₁).2.1]
    simp only [↓reduceIte]
    have h_od : ∀ k ≤ 4,
        s2₁.mem (base + (if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) =
          sm₁.mem (base + (if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) :=
      fun k hk => by
        rw [Nat.add_assoc]
        exact hs2_hdr₁ _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> (clear *- hk; omega))
    rw [hs2_hdr₁ hdrStage (by decide), hs2_hdr₁ hdrNDst (by decide), hs2_hdr₁ hdrPad (by decide),
      hs2_hdr₁ hdrW (by decide), hs2_hdr₁ hdrItemHi (by decide), hs2_hdr₁ hdrQHi (by decide),
      hs2_hdr₁ hdrValBits (by decide), hs2_hdr₁ hdrLive (by decide),
      show s2₁.mem (base + if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) =
        sm₁.mem (base + if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) by
        simpa only [Nat.add_zero] using h_od 0 (by decide),
      h_od 1 (by decide), h_od 2 (by decide), h_od 3 (by decide), h_od 4 (by decide)]
  have hctx0_s2₂ : (Memory.spec 0).clientResult s2₂ (loadHostCtxProg (base, 0)) = pgH.toCtx := by
    rw [← hctx0_₂, (loadHostCtxProg_eval base 0 s2₂).2.1, (loadHostCtxProg_eval base 0 sm₂).2.1]
    simp only [↓reduceIte]
    have h_od : ∀ k ≤ 4,
        s2₂.mem (base + (if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) =
          sm₂.mem (base + (if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) :=
      fun k hk => by
        rw [Nat.add_assoc]
        exact hs2_hdr₂ _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> (clear *- hk; omega))
    rw [hs2_hdr₂ hdrStage (by decide), hs2_hdr₂ hdrNDst (by decide), hs2_hdr₂ hdrPad (by decide),
      hs2_hdr₂ hdrW (by decide), hs2_hdr₂ hdrItemHi (by decide), hs2_hdr₂ hdrQHi (by decide),
      hs2_hdr₂ hdrValBits (by decide), hs2_hdr₂ hdrLive (by decide),
      show s2₂.mem (base + if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) =
        sm₂.mem (base + if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) by
        simpa only [Nat.add_zero] using h_od 0 (by decide),
      h_od 1 (by decide), h_od 2 (by decide), h_od 3 (by decide), h_od 4 (by decide)]
  have hf_ev₁ := (finishInitTailProg_eval base s2₁).1
  have hf_ev₂ := (finishInitTailProg_eval base s2₂).1
  rw [hctx0_s2₁, hh_ofCtx, hs2_hdr₁ hdrStage (by decide), hs2_hdr₁ hdrNDst (by decide),
    hs2_hdr₁ hdrLive (by decide), hm₁.live_eq, hs2_hdr₁ hdrQSnap (by decide)] at hf_ev₁
  rw [hctx0_s2₂, hh_ofCtx, hs2_hdr₂ hdrStage (by decide),
    ← hsch_m.2 hdrStage (by decide) (by decide),
    hs2_hdr₂ hdrNDst (by decide), ← hsch_m.2 hdrNDst (by decide) (by decide),
    hs2_hdr₂ hdrLive (by decide), hm₂.live_eq,
    hs2_hdr₂ hdrQSnap (by decide), hqs_m₂] at hf_ev₂
  have hst₁_fin : st₁ = (Memory.spec 0).clientState s2₁ (finishInitTailProg base) := by
    rw [hst₁, hbgev₁, httev₁, ite_eq_right hnlt8]
  have hst₂_fin : st₂ = (Memory.spec 0).clientState s2₂ (finishInitTailProg base) := by
    rw [hst₂, hbgev₂, httev₂, ite_eq_right hnlt8]
  set stg := sm₁.mem (base + hdrStage)
  set nDst := sm₁.mem (base + hdrNDst)
  set pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
  set pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
  set sb₁ := (Memory.spec 0).clientState s2₁
    (pageInitScalarsBandProg ((pgH.metaBase, pgH.pgB), (qSnap, nLive - qSnap * pgH.pgB)))
  set sb₂ := (Memory.spec 0).clientState s2₂
    (pageInitScalarsBandProg ((pgH.metaBase, pgH.pgB), (qSnap, nLive - qSnap * pgH.pgB)))
  set s3₁ := (Memory.spec 0).clientState sb₁ (setSlotIoProg (pSrc, ((1, 0), pgH.toCtx)))
  set s3₂ := (Memory.spec 0).clientState sb₂ (setSlotIoProg (pSrc, ((1, 0), pgH.toCtx)))
  set actDst : Memory.Prog Unit :=
    if nDst = 0 then writeSmallParamTableProg ((pDst, base + hdrSmallMeta1), ((1, 1), pgH.toCtx))
    else setSlotIoProg (pDst, ((1, 1), pgH.toCtx))
  set s4₁ := (Memory.spec 0).clientState s3₁ actDst
  set s4₂ := (Memory.spec 0).clientState s3₂ actDst
  set rem8 := nLive / itemBatchWhp + 1
  have hm_st₁ : st₁.mem =
      Function.update (Function.update s4₁.mem (base + hdrRem) rem8) (base + hdrPhase) 8 := by
    rw [hst₁_fin, hf_ev₁]
  have hm_st₂ : st₂.mem =
      Function.update (Function.update s4₂.mem (base + hdrRem) rem8) (base + hdrPhase) 8 := by
    rw [hst₂_fin, hf_ev₂]
  have hpS_rng : base + 64 ≤ pSrc ∧ pSrc + 64 ≤ base + 192 := by
    dsimp only [pSrc, hdrPBase0, hdrPBase1]; split_ifs <;> (clear *-; exact ⟨by omega, by omega⟩)
  have hpD_rng : base + 64 ≤ pDst ∧ pDst + 64 ≤ base + 192 := by
    dsimp only [pDst, hdrPBase0, hdrPBase1]; split_ifs <;> (clear *-; exact ⟨by omega, by omega⟩)
  have hpSD_disj : pDst + 64 ≤ pSrc ∨ pSrc + 64 ≤ pDst := by
    dsimp only [pSrc, pDst, hdrPBase0, hdrPBase1]
    split_ifs <;> [exact Or.inr (by clear *-; omega); exact Or.inl (by clear *-; omega)]
  have hs4_out₁ : ∀ a, ¬(pDst ≤ a ∧ a < pDst + 61) → s4₁.mem a = s3₁.mem a := fun a ha => by
    dsimp only [s4₁, actDst]
    by_cases hd0 : nDst = 0
    · rw [ite_eq_left hd0]
      exact (writeSmallParamTableProg_spec pDst
        ⟨base + hdrSmallMeta1, 0, 0, ⟨1, 1, pgH⟩⟩ s3₁).2.2.2 a ha
    · rw [ite_eq_right hd0]
      exact (setSlotIoProg_frame pDst ((1, 1), pgH.toCtx)).mem_outside s3₁ a
        (by clear *- ha; omega)
  have hs4_out₂ : ∀ a, ¬(pDst ≤ a ∧ a < pDst + 61) → s4₂.mem a = s3₂.mem a := fun a ha => by
    dsimp only [s4₂, actDst]
    by_cases hd0 : nDst = 0
    · rw [ite_eq_left hd0]
      exact (writeSmallParamTableProg_spec pDst
        ⟨base + hdrSmallMeta1, 0, 0, ⟨1, 1, pgH⟩⟩ s3₂).2.2.2 a ha
    · rw [ite_eq_right hd0]
      exact (setSlotIoProg_frame pDst ((1, 1), pgH.toCtx)).mem_outside s3₂ a
        (by clear *- ha; omega)
  have hsb_sp₁ := pageInitScalarsBandProg_spec pgH.metaBase pgH.pgB qSnap
    (nLive - qSnap * pgH.pgB) s2₁
  have hsb_sp₂ := pageInitScalarsBandProg_spec pgH.metaBase pgH.pgB qSnap
    (nLive - qSnap * pgH.pgB) s2₂
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hsb_sp₁ hsb_sp₂
  have hmb_ge192 : base + 192 ≤ pgH.metaBase := by
    change base + 192 ≤ mbHost; dsimp only [mbHost]; unfold dualMbHost
    split_ifs <;> (clear *-; omega)
  have hst_sb_out₁ : ∀ a, a ≠ base + hdrPhase → a ≠ base + hdrRem →
      ¬(base + 64 ≤ a ∧ a < base + 192) → st₁.mem a = sb₁.mem a := fun a h1 h2 h64 => by
    rw [hm_st₁, Function.update_of_ne h1, Function.update_of_ne h2,
      hs4_out₁ a (by clear *- h64 hpD_rng; omega)]
    exact (setSlotIoProg_frame pSrc ((1, 0), pgH.toCtx)).mem_outside sb₁ a
      (by clear *- h64 hpS_rng; omega)
  have hst_sb_out₂ : ∀ a, a ≠ base + hdrPhase → a ≠ base + hdrRem →
      ¬(base + 64 ≤ a ∧ a < base + 192) → st₂.mem a = sb₂.mem a := fun a h1 h2 h64 => by
    rw [hm_st₂, Function.update_of_ne h1, Function.update_of_ne h2,
      hs4_out₂ a (by clear *- h64 hpD_rng; omega)]
    exact (setSlotIoProg_frame pSrc ((1, 0), pgH.toCtx)).mem_outside sb₂ a
      (by clear *- h64 hpS_rng; omega)
  have hsp_hdr₁ : ∀ off < 64, off ≠ hdrPhase → off ≠ hdrRem →
      sp₁.mem (base + off) = sm₁.mem (base + off) := fun off hoff h1 h2 => by
    have hb192 : base + 192 ≤ st₁.frontier - k_sh := by
      have := h_post₁.base_fr; rw [hsp₁_eq] at this; exact this
    rw [hsp₁_eq]; dsimp only [Memory.State.mem]
    rw [clear_of_not_owns (by simp only [Block.Owns]; clear *- hoff hb192; omega),
      hst_sb_out₁ (base + off) (base_add_ne h1) (base_add_ne h2) (by clear *- hoff; omega),
      hsb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (base + off) (by clear *- hoff hmb_ge192; omega),
      hs2_hdr₁ off (by clear *- hoff; omega)]
  have hpgH_sp₁ : dualPgHost c V w base nLive sp₁.mem = pgH := by
    dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
    rw [hsp_hdr₁ hdrNDst (by decide) (by decide) (by decide),
      hsp_hdr₁ hdrNSrc (by decide) (by decide) (by decide),
      hsp_hdr₁ hdrStage (by decide) (by decide) (by decide),
      hsp_hdr₁ hdrPad (by decide) (by decide) (by decide),
      hsp_hdr₁ hdrItemHi (by decide) (by decide) (by decide),
      hsp_hdr₁ hdrQHi (by decide) (by decide) (by decide)]
  have hpgH_sp₂ : dualPgHost c V w base nLive sp₂.mem = pgH := by
    have h1 : dualPgHost c V w base nLive sp₂.mem = dualPgHost c V w base nLive sp₁.mem := by
      unfold dualPgHost dualNHost dualMbHost
      rw [← hsch_post.2 hdrNDst (by decide) (by decide),
        ← hsch_post.2 hdrNSrc (by decide) (by decide),
        ← hsch_post.2 hdrStage (by decide) (by decide),
        ← hsch_post.2 hdrPad (by decide) (by decide),
        ← hsch_post.2 hdrItemHi (by decide) (by decide),
        ← hsch_post.2 hdrQHi (by decide) (by decide)]
    exact h1.trans hpgH_sp₁
  have hsl8_₁ := h_post₁.sl_8 hp8_post₁
  have hsl8_₂ := h_post₂.sl_8 hp8_post₂
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hsl8_₁ hsl8_₂
  rw [hpgH_sp₁] at hsl8_₁
  rw [hpgH_sp₂] at hsl8_₂
  have hsl_src₁ := hsl8_₁.2.2.2.2.2.1
  have hsl_src₂ := hsl8_₂.2.2.2.2.2.1
  -- Prove `mem_eq` on `Coupled8Region c w base sp₁.mem`
  have hmem_c8 : ∀ addr, Coupled8Region c w base sp₁.mem addr → sp₁.mem addr = sp₂.mem addr := by
    intro addr hreg
    have hpS_sp₁ : dualPSrc base sp₁.mem = pSrc := by
      unfold dualPSrc; rw [hsp_hdr₁ hdrStage (by decide) (by decide) (by decide)]
    have hmbS_sp₁ : dualMbSrc base sp₁.mem = dualMbSrc base sm₁.mem := by
      unfold dualMbSrc
      rw [hsp_hdr₁ hdrStage (by decide) (by decide) (by decide),
        hsp_hdr₁ hdrNSrc (by decide) (by decide) (by decide),
        hsp_hdr₁ hdrPad (by decide) (by decide) (by decide)]
    have hcapS_sp₁ : dualCapSrc base sp₁.mem = dualCapSrc base sm₁.mem := by
      unfold dualCapSrc
      rw [hsp_hdr₁ hdrStage (by decide) (by decide) (by decide),
        hsp_hdr₁ hdrNSrc (by decide) (by decide) (by decide),
        hsp_hdr₁ hdrNDst (by decide) (by decide) (by decide)]
    unfold Coupled8Region SlotSrcMetaRegion at hreg
    rw [hpS_sp₁, hmbS_sp₁, hcapS_sp₁] at hreg
    have hst_fr_eq : st₁.frontier = st₂.frontier := by
      have hf₁ := (h_post₁.sched)
      rw [hsp₁_eq, hsp₂_eq] at hsch_post
      -- Or directly from `sb`/`s3`/`s4` frontier conservation:
      have hf_s2₁ : s2₁.frontier = sm₁.frontier := htb_sp₁.2.2.1
      have hf_s2₂ : s2₂.frontier = sm₂.frontier := htb_sp₂.2.2.1
      have hf_sb₁ : sb₁.frontier = sm₁.frontier := hsb_sp₁.1.trans hf_s2₁
      have hf_sb₂ : sb₂.frontier = sm₂.frontier := hsb_sp₂.1.trans hf_s2₂
      have hf_s3₁ : s3₁.frontier = sm₁.frontier :=
        (runClient_frontier_setSlotIoProg _ _).trans hf_sb₁
      have hf_s3₂ : s3₂.frontier = sm₂.frontier :=
        (runClient_frontier_setSlotIoProg _ _).trans hf_sb₂
      have hf_s4₁ : s4₁.frontier = sm₁.frontier := by
        dsimp only [s4₁, actDst]
        by_cases hd0 : nDst = 0
        · rw [ite_eq_left hd0]
          exact (writeSmallParamTableProg_spec pDst
            ⟨base + hdrSmallMeta1, 0, 0, ⟨1, 1, pgH⟩⟩ s3₁).1.trans hf_s3₁
        · rw [ite_eq_right hd0]
          exact (runClient_frontier_setSlotIoProg _ _).trans hf_s3₁
      have hf_s4₂ : s4₂.frontier = sm₂.frontier := by
        dsimp only [s4₂, actDst]
        by_cases hd0 : nDst = 0
        · rw [ite_eq_left hd0]
          exact (writeSmallParamTableProg_spec pDst
            ⟨base + hdrSmallMeta1, 0, 0, ⟨1, 1, pgH⟩⟩ s3₂).1.trans hf_s3₂
        · rw [ite_eq_right hd0]
          exact (runClient_frontier_setSlotIoProg _ _).trans hf_s3₂
      have h1 : st₁.frontier = s4₁.frontier := by rw [hst₁_fin, hf_ev₁]
      have h2 : st₂.frontier = s4₂.frontier := by rw [hst₂_fin, hf_ev₂]
      exact h1.trans (hf_s4₁.trans (hsch_m.1.trans (hf_s4₂.symm.trans h2.symm)))
    rw [hsp₁_eq, hsp₂_eq, ← hst_fr_eq]
    dsimp only [Memory.State.mem]
    by_cases hown_cl : (Block.mk (st₁.frontier - k_sh) k_sh).Owns addr
    · rw [clear_of_owns hown_cl, clear_of_owns hown_cl]
    · rw [clear_of_not_owns hown_cl, clear_of_not_owns hown_cl]
      -- Show `addr` is in `Coupled67Region c w base sm₁.mem`
      have hin67 : Coupled67Region c w base sm₁.mem addr := by
        have hsd : SlotDirectRegion c w (dualPSrc base sm₁.mem) (dualMbSrc base sm₁.mem)
            (dualCapSrc base sm₁.mem)
            (directSlotIo w (valBits V) base ibHi qHi nLive) addr := by
          have hpS_m : dualPSrc base sm₁.mem = pSrc := rfl
          rw [hpS_m]
          rcases hreg with hp | hm
          · exact Or.inl hp
          · exact Or.inr (Or.inl hm)
        -- Use `disjoint_pgHost_nonPageMeta` and schedule separation directly on `hm₁`:
        have hsched₁ := hm₁.sched; rw [ite_eq_right (by clear *- hp7₁; omega)] at hsched₁
        obtain ⟨hmDst_eq, hpad_eq, _, _, _, _⟩ := hsched₁.ge2 (by clear *- hp7₁; omega)
        have hlt10 : sm₁.mem (base + hdrPhase) < 10 := by clear *- hp7₁; omega
        rcases hreg with ⟨h1, h2⟩ | hmeta_s
        · refine ⟨?_, fun hpg => by have := (hdisj_pg₁ _ hpg).1; clear *- h2 hpS_rng this; omega,
            ?_⟩
          · unfold slotOwnsNonPageMeta dualMbDst; rw [ite_eq_left hlt10]
            by_cases hd0 : sm₁.mem (base + hdrNDst) = 0
            · simp only [hd0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
                hdrSmallMeta1]
              rintro ⟨g1, g2⟩; clear *- h1 h2 hpS_rng g1 g2; omega
            · simp only [hd0, ↓reduceIte]
              split_ifs <;>
                (rintro (⟨g1, _⟩ | ⟨_, g1, _⟩) <;> (clear *- h1 h2 hpS_rng g1; omega))
          · rintro ⟨hd0, hlo, _⟩
            unfold dualMbDst at hlo; rw [ite_eq_left hlt10, ite_eq_right hd0] at hlo
            split_ifs at hlo <;> (clear *- h2 hpS_rng hlo; omega)
        · have hn_pg : ¬(dualPgHost c 1 w base 0 sm₁.mem).OwnsMetaAddr addr :=
            fun hpg => (hdisj_pg₁ addr hpg).2.2.1 hmeta_s
          have hnot_d : ¬(sm₁.mem (base + hdrNDst) ≠ 0 ∧ dualMbDst base sm₁.mem ≤ addr ∧
              addr < dualMbDst base sm₁.mem + offPageDir c w (sm₁.mem (base + hdrNDst))) := by
            rintro ⟨hd0, hlo, hhi⟩
            unfold dualMbDst at hlo hhi; rw [ite_eq_left hlt10, ite_eq_right hd0] at hlo hhi
            unfold slotOwnsNonPageMeta dualMbSrc dualCapSrc at hmeta_s
            by_cases hst0 : sm₁.mem (base + hdrStage) = 0
            · simp only [hst0, ↓reduceIte] at hlo hhi hmeta_s
              by_cases hs0 : sm₁.mem (base + hdrNSrc) = 0
              · simp only [hs0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
                  hdrSmallMeta0] at hmeta_s; clear *- hlo hmeta_s; omega
              · have hth_s := (hm₁.nSrc_bounds.resolve_left hs0).1
                have hod_s := (epochMeta_offsets_le (w := w) hth_s).2.2.2
                have h32_s : 32 ≤ offPageDir c w (sm₁.mem (base + hdrNSrc)) :=
                  (epochMeta_offsets_le (w := w) hth_s).1.trans
                    ((epochMeta_offsets_le (w := w) hth_s).2.1.trans
                      (epochMeta_offsets_le (w := w) hth_s).2.2.1)
                have hmS_p : sm₁.mem (base + hdrMSrc) ≤ sm₁.mem (base + hdrPad) := by
                  rw [hpad_eq]; exact le_max_left _ _
                rw [← hm₁.mSrc_eq] at hod_s
                simp only [hs0, ↓reduceIte] at hmeta_s
                rcases hmeta_s with ⟨_, g2⟩ | ⟨_, _, g2⟩ <;>
                  (clear *- hlo g2 hod_s h32_s hmS_p; omega)
            · simp only [hst0, ↓reduceIte] at hlo hhi hmeta_s
              have hth_d := (hsched₁.nDst_bounds.resolve_left hd0).1
              have hod_d := (epochMeta_offsets_le (w := w) hth_d).2.2.2
              have hmD_p : sm₁.mem (base + hdrMDst) ≤ sm₁.mem (base + hdrPad) := by
                rw [hpad_eq]; exact le_max_right _ _
              rw [← hmDst_eq] at hod_d
              simp only [hd0, ↓reduceIte] at hmeta_s
              rcases hmeta_s with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;>
                (clear *- hhi g1 hod_d hmD_p; omega)
          refine ⟨?_, hn_pg, hnot_d⟩
          intro hmeta_d
          by_cases hd0 : sm₁.mem (base + hdrNDst) = 0
          · obtain ⟨hs_pos, hst0, _⟩ := hsched₁.nDst_zero hd0
            unfold slotOwnsNonPageMeta dualMbDst at hmeta_d
            rw [ite_eq_left hlt10] at hmeta_d
            simp only [hd0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
              hdrSmallMeta1] at hmeta_d
            unfold slotOwnsNonPageMeta dualMbSrc dualCapSrc at hmeta_s
            simp only [hst0, hs_pos.ne', ↓reduceIte] at hmeta_s
            rcases hmeta_s with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;> (clear *- hmeta_d g1; omega)
          · unfold slotOwnsNonPageMeta at hmeta_d
            simp only [hd0, ↓reduceIte] at hmeta_d
            have h32_d : 32 ≤ offPageDir c w (sm₁.mem (base + hdrNDst)) := by
              have hth_d := (hsched₁.nDst_bounds.resolve_left hd0).1
              exact (epochMeta_offsets_le (w := w) hth_d).1.trans
                ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
                  (epochMeta_offsets_le (w := w) hth_d).2.2.1)
            rcases hmeta_d with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
              exact hnot_d ⟨hd0, by clear *- g1; omega, by clear *- g2 h32_d; omega⟩
      rcases hreg with ⟨h1, h2⟩ | hmeta_s
      · -- `addr ∈ [pSrc, pSrc + 64)`
        rw [hm_st₁, hm_st₂,
          Function.update_of_ne (by dsimp only [hdrPhase]; clear *- h1 hpS_rng; omega),
          Function.update_of_ne (by dsimp only [hdrRem]; clear *- h1 hpS_rng; omega),
          Function.update_of_ne (by dsimp only [hdrPhase]; clear *- h1 hpS_rng; omega),
          Function.update_of_ne (by dsimp only [hdrRem]; clear *- h1 hpS_rng; omega),
          hs4_out₁ addr (by clear *- h1 h2 hpSD_disj; omega),
          hs4_out₂ addr (by clear *- h1 h2 hpSD_disj; omega)]
        by_cases h48 : pSrc + 48 ≤ addr ∧ addr < pSrc + 61
        · have hv1 := setSlotIoProg_mem_vals pSrc (pagedSlotIo 0 pgH) sb₁
          have hv2 := setSlotIoProg_mem_vals pSrc (pagedSlotIo 0 pgH) sb₂
          dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hv1 hv2
          have hj : addr - (pSrc + 48) < 13 := by clear *- h48; omega
          have ha_off : addr = pSrc + (48 + (addr - (pSrc + 48))) := by clear *- h48; omega
          dsimp only [s3₁, s3₂]; rw [ha_off]
          interval_cases (addr - (pSrc + 48))
          · exact hv1.1.trans hv2.1.symm
          · exact hv1.2.1.trans hv2.2.1.symm
          · exact hv1.2.2.1.trans hv2.2.2.1.symm
          · exact hv1.2.2.2.1.trans hv2.2.2.2.1.symm
          · exact hv1.2.2.2.2.1.trans hv2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.1.trans hv2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.2.2.2.2.2.trans hv2.2.2.2.2.2.2.2.2.2.2.2.2.symm
        · dsimp only [s3₁, s3₂]
          rw [(setSlotIoProg_frame pSrc ((1, 0), pgH.toCtx)).mem_outside sb₁ addr h48,
            (setSlotIoProg_frame pSrc ((1, 0), pgH.toCtx)).mem_outside sb₂ addr h48,
            hsb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 addr (by clear *- h2 hpS_rng hmb_ge192; omega),
            hsb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 addr (by clear *- h2 hpS_rng hmb_ge192; omega),
            hs2_pg₁ addr hin67.2.1, hs2_pg₂ addr hin67.2.1]
          exact hc67.2 addr hin67
      · -- `addr ∈ slotOwnsNonPageMeta Src`
        have ha_no64 : ¬(base + 64 ≤ addr ∧ addr < base + 192) := by
          unfold slotOwnsNonPageMeta dualMbSrc dualCapSrc at hmeta_s
          by_cases hst0 : sm₁.mem (base + hdrStage) = 0
          · simp only [hst0, ↓reduceIte] at hmeta_s
            by_cases hs0 : sm₁.mem (base + hdrNSrc) = 0
            · simp only [hs0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
                hdrSmallMeta0] at hmeta_s
              clear *- hmeta_s; omega
            · simp only [hs0, ↓reduceIte] at hmeta_s
              rcases hmeta_s with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;> (clear *- g1; omega)
          · simp only [hst0, ↓reduceIte] at hmeta_s
            split_ifs at hmeta_s <;>
              (rcases hmeta_s with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;> (clear *- g1; omega))
        have ha_ge48 : base + 48 ≤ addr := by
          unfold slotOwnsNonPageMeta dualMbSrc dualCapSrc at hmeta_s
          dsimp only [hdrSmallMeta0] at hmeta_s
          split_ifs at hmeta_s <;>
            (rcases hmeta_s with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;> (clear *- g1; omega))
        have hnot_sb : ¬(pgH.metaBase + 18 ≤ addr ∧ addr < pgH.metaBase + 32) :=
          fun h18 => hin67.2.1 (Or.inl h18)
        rw [hst_sb_out₁ addr (by dsimp only [hdrPhase]; clear *- ha_ge48; omega)
            (by dsimp only [hdrRem]; clear *- ha_ge48; omega) ha_no64,
          hst_sb_out₂ addr (by dsimp only [hdrPhase]; clear *- ha_ge48; omega)
            (by dsimp only [hdrRem]; clear *- ha_ge48; omega) ha_no64,
          hsb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 addr hnot_sb,
          hsb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 addr hnot_sb,
          hs2_pg₁ addr hin67.2.1, hs2_pg₂ addr hin67.2.1]
        exact hc67.2 addr hin67
  -- Prove `extractPageUnperm pgH sp₁.mem = extractPageUnperm pgH sp₂.mem`
  have hibHi_ge : base + 196 ≤ ibHi := by
    have hsched₁ := hm₁.sched; rw [ite_eq_right (by clear *- hp7₁; omega)] at hsched₁
    dsimp only [ibHi]
    rw [(hsched₁.ge2 (by clear *- hp7₁; omega)).2.2.2.2.1]
    split_ifs <;> (clear *-; omega)
  have hfr_sp₁ : sp₁.frontier = ibHi + pairStreamWords nLive qHi (valBits V) w := by
    have hsched_p₁ := h_post₁.sched
    rw [ite_eq_right (by rw [hp8_post₁]; decide)] at hsched_p₁
    obtain ⟨hlo, hhi⟩ := hsched_p₁.ph3_10 ⟨by rw [hp8_post₁]; decide, by rw [hp8_post₁]; decide⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hhi
    rw [hsp_hdr₁ hdrItemHi (by decide) (by decide) (by decide),
      hsp_hdr₁ hdrQHi (by decide) (by decide) (by decide)] at hlo hhi
    dsimp only [ibHi, qHi, nLive] at hlo hhi ⊢
    clear *- hlo hhi; omega
  have h32_od : 32 ≤ pgH.offDir := hv_fr₁.2.2.2.2.2.2.2.2.2.2.2.1
  have hod_ot : pgH.offDir ≤ pgH.offTail := Nat.le_add_right _ _
  have hm_ib : pgH.metaBase + 32 ≤ ibHi := by
    have h32 := (epochMeta_offsets_le (w := w) hth_h₁.1).1.trans
      ((epochMeta_offsets_le (w := w) hth_h₁.1).2.1.trans
        ((epochMeta_offsets_le (w := w) hth_h₁.1).2.2.1.trans
          (epochMeta_offsets_le (w := w) hth_h₁.1).2.2.2))
    have hmb_ib := (dualPgHost_eval_valid hm₁ (by clear *- hp7₁; omega)
      (by clear *- hp7₁; omega)).2.2.2.1
    change mbHost + epochMetaWordsWhp c w nHost ≤ ibHi at hmb_ib
    change mbHost + 32 ≤ ibHi; clear *- h32 hmb_ib; omega
  have hsp_sb₁ : ∀ a, pgH.OwnsMetaAddr a → sp₁.mem a = sb₁.mem a := fun a ha => by
    have ha210 := (hdisj_pg₁ a ha).1
    have ha_lt_ib : a < ibHi := (hdisj_pg₁ a ha).2.1
    have hst_fr_ge : sp₁.frontier = st₁.frontier - k_sh := by rw [hsp₁_eq]
    rw [hsp₁_eq]; dsimp only [Memory.State.mem]
    rw [clear_of_not_owns (by
        simp only [Block.Owns]; rw [← hst_fr_ge, hfr_sp₁]; clear *- ha_lt_ib; omega),
      hst_sb_out₁ a (by dsimp only [hdrPhase]; clear *- ha210; omega)
        (by dsimp only [hdrRem]; clear *- ha210; omega) (by clear *- ha210; omega)]
  have hsp_sb₂ : ∀ a, pgH.OwnsMetaAddr a → sp₂.mem a = sb₂.mem a := fun a ha => by
    have ha210 := (hdisj_pg₁ a ha).1
    have ha_lt_ib : a < ibHi := (hdisj_pg₁ a ha).2.1
    have hfr_sp₂ : sp₂.frontier = sp₁.frontier := hsch_post.1.symm
    have hst_fr_ge : sp₂.frontier = st₂.frontier - k_sh := by rw [hsp₂_eq]
    rw [hsp₂_eq]; dsimp only [Memory.State.mem]
    rw [clear_of_not_owns (by
        simp only [Block.Owns]; rw [← hst_fr_ge, hfr_sp₂, hfr_sp₁]; clear *- ha_lt_ib; omega),
      hst_sb_out₂ a (by dsimp only [hdrPhase]; clear *- ha210; omega)
        (by dsimp only [hdrRem]; clear *- ha210; omega) (by clear *- ha210; omega)]
  have hu_sp₁ : extractPageUnperm pgH sp₁.mem = extractPageUnperm pgH sb₁.mem :=
    extractPageUnperm_congr hw_pos hsp_sb₁
  have hu_sp₂ : extractPageUnperm pgH sp₂.mem = extractPageUnperm pgH sb₂.mem :=
    extractPageUnperm_congr hw_pos hsp_sb₂
  have hdir_s2₁ : ∀ vp < pgH.maxPages,
      (extractPagePair pgH s2₁.mem).pageOf false vp = vp ∧
      (extractPagePair pgH s2₁.mem).pageOf true vp = 0 ∧
      (extractPagePair pgH s2₁.mem).ownerSide vp = false ∧
      (extractPagePair pgH s2₁.mem).ownerVp vp = vp := fun vp hvp => by
    have hp_eq : extractPagePair pgH s2₁.mem = (extractPageUnperm pgM s2₁.mem).st := rfl
    have hp0_eq : (extractPageUnperm pgM sm₁.mem).st = extractPagePair pgH sm₁.mem := rfl
    rw [hp_eq, htb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, htb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      htb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp0_eq]
    exact hdir_pre₁ vp hvp
  have hdir_s2₂ : ∀ vp < pgH.maxPages,
      (extractPagePair pgH s2₂.mem).pageOf false vp = vp ∧
      (extractPagePair pgH s2₂.mem).pageOf true vp = 0 ∧
      (extractPagePair pgH s2₂.mem).ownerSide vp = false ∧
      (extractPagePair pgH s2₂.mem).ownerVp vp = vp := fun vp hvp => by
    have hp_eq : extractPagePair pgH s2₂.mem = (extractPageUnperm pgM s2₂.mem).st := rfl
    have hp0_eq : (extractPageUnperm pgM sm₂.mem).st = extractPagePair pgH sm₂.mem := rfl
    rw [hp_eq, htb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, htb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      htb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp0_eq]
    exact hdir_pre₂ vp hvp
  have htail_eq_s2 : ∀ idx < 8 * pgH.pgB,
      (idx < 4 * pgH.pgB →
        (extractPagePair pgH s2₁.mem).tailRes false idx =
          (extractPagePair pgH s2₂.mem).tailRes false idx ∧
        (extractPagePair pgH s2₁.mem).tailRes true idx =
          (extractPagePair pgH s2₂.mem).tailRes true idx) ∧
      (extractPagePair pgH s2₁.mem).tailOwnerSide idx =
        (extractPagePair pgH s2₂.mem).tailOwnerSide idx ∧
      (extractPagePair pgH s2₁.mem).tailOwnerRing idx =
        (extractPagePair pgH s2₂.mem).tailOwnerRing idx := fun idx hidx => by
    have hidxM : idx < 8 * pgM.pgB := hidx
    have hp1 : extractPagePair pgH s2₁.mem = (extractPageUnperm pgM s2₁.mem).st := rfl
    have hp2 : extractPagePair pgH s2₂.mem = (extractPageUnperm pgM s2₂.mem).st := rfl
    have hp0_1 : (extractPageUnperm pgM sm₁.mem).st = extractPagePair pgH sm₁.mem := rfl
    have hp0_2 : (extractPageUnperm pgM sm₂.mem).st = extractPagePair pgH sm₂.mem := rfl
    obtain ⟨htos1, htor1⟩ := htb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hidxM
    obtain ⟨htos2, htor2⟩ := htb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hidxM
    have htr1 := htb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have htr2 := htb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [hp1, hp2]
    rw [← htb_sp₁.2.1, hcur'_eq8, hp0_1] at htos1 htor1 htr1
    rw [← htb_sp₂.2.1, hcur'_res₂, hcur'_eq8, hp0_2] at htos2 htor2 htr2
    by_cases hge : cur ≤ idx
    · have hc : cur ≤ idx ∧ idx < 8 * pgH.pgB := ⟨hge, hidx⟩
      rw [htos1, htos2, htor1, htor2, ite_eq_left hc, ite_eq_left hc,
        ite_eq_left hc, ite_eq_left hc]
      refine ⟨fun h4 => ?_, rfl, rfl⟩
      have hf1 := htr1 false idx h4; have hf2 := htr2 false idx h4
      have ht1 := htr1 true idx h4; have ht2 := htr2 true idx h4
      rw [ite_eq_left hc] at hf1 hf2 ht1 ht2
      exact ⟨hf1.trans hf2.symm, ht1.trans ht2.symm⟩
    · have hnc : ¬(cur ≤ idx ∧ idx < 8 * pgH.pgB) := fun h => hge h.1
      have hlt_c : idx < cur := Nat.lt_of_not_le hge
      have hp_i1 := htail_pre₁ idx hlt_c
      have hp_i2 := htail_pre₂ idx hlt_c
      rw [htos1, htos2, htor1, htor2, ite_eq_right hnc, ite_eq_right hnc,
        ite_eq_right hnc, ite_eq_right hnc,
        hp_i1.2.1, hp_i2.2.1, hp_i1.2.2, hp_i2.2.2]
      refine ⟨fun h4 => ?_, rfl, rfl⟩
      have hf1 := htr1 false idx h4; have hf2 := htr2 false idx h4
      have ht1 := htr1 true idx h4; have ht2 := htr2 true idx h4
      rw [ite_eq_right hnc] at hf1 hf2 ht1 ht2
      exact ⟨(hf1.trans (hp_i1.1 h4).1).trans ((hp_i2.1 h4).1.symm.trans hf2.symm),
        (ht1.trans (hp_i1.1 h4).2).trans ((hp_i2.1 h4).2.symm.trans ht2.symm)⟩
  have hu_eq : extractPageUnperm pgH sb₁.mem = extractPageUnperm pgH sb₂.mem := by
    have hdir_b : ∀ s_x s2_x,
        (∀ a, ¬(pgH.metaBase + 18 ≤ a ∧ a < pgH.metaBase + 32) →
          (s_x : Memory.State).mem a = (s2_x : Memory.State).mem a) →
        ∀ idx < 4 * pgH.maxPages,
          readPacked (pgH.metaBase + pgH.offDir) pgH.ptrB pgH.w s_x.mem idx =
            readPacked (pgH.metaBase + pgH.offDir) pgH.ptrB pgH.w s2_x.mem idx :=
      fun s_x s2_x hout idx hidx => readPacked_congr hw_pos
        (fun a ha => hout a (by have h1 := ha.1; clear *- h1 h32_od; omega)) hidx
    have htail_b : ∀ s_x s2_x,
        (∀ a, ¬(pgH.metaBase + 18 ≤ a ∧ a < pgH.metaBase + 32) →
          (s_x : Memory.State).mem a = (s2_x : Memory.State).mem a) →
        ∀ idx < 16 * pgH.pgB,
          readPacked (pgH.metaBase + pgH.offTail) pgH.ptrB pgH.w s_x.mem idx =
            readPacked (pgH.metaBase + pgH.offTail) pgH.ptrB pgH.w s2_x.mem idx :=
      fun s_x s2_x hout idx hidx => readPacked_congr hw_pos
        (fun a ha => hout a (by have h1 := ha.1; clear *- h1 h32_od hod_ot; omega)) hidx
    have hd1 := hdir_b sb₁ s2₁ hsb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hd2 := hdir_b sb₂ s2₂ hsb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have ht1 := htail_b sb₁ s2₁ hsb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have ht2 := htail_b sb₂ s2₂ hsb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hst_eq : extractPagePair pgH sb₁.mem = extractPagePair pgH sb₂.mem := by
      unfold extractPagePair
      congr 1
      · exact hsb_sp₁.2.2.2.2.1.trans hsb_sp₂.2.2.2.2.1.symm
      · funext side; cases side
        · exact hsb_sp₁.2.2.2.2.2.1.trans hsb_sp₂.2.2.2.2.2.1.symm
        · exact hsb_sp₁.2.2.2.2.2.2.1.trans hsb_sp₂.2.2.2.2.2.2.1.symm
      · funext side; cases side
        · exact hsb_sp₁.2.2.2.2.2.2.2.1.trans hsb_sp₂.2.2.2.2.2.2.2.1.symm
        · exact hsb_sp₁.2.2.2.2.2.2.2.2.1.trans hsb_sp₂.2.2.2.2.2.2.2.2.1.symm
      · funext side; cases side
        · exact hsb_sp₁.2.2.2.2.2.2.2.2.2.1.trans hsb_sp₂.2.2.2.2.2.2.2.2.2.1.symm
        · exact hsb_sp₁.2.2.2.2.2.2.2.2.2.2.1.trans hsb_sp₂.2.2.2.2.2.2.2.2.2.2.1.symm
      · funext side vp
        by_cases hvp : vp < pgH.maxPages
        · have he1 : (extractPagePair pgH sb₁.mem).pageOf side vp =
              (extractPagePair pgH s2₁.mem).pageOf side vp := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hvp, ite_eq_left hvp]
            cases side <;> exact hd1 _ (by dsimp only; clear *- hvp; omega)
          have he2 : (extractPagePair pgH sb₂.mem).pageOf side vp =
              (extractPagePair pgH s2₂.mem).pageOf side vp := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hvp, ite_eq_left hvp]
            cases side <;> exact hd2 _ (by dsimp only; clear *- hvp; omega)
          change (extractPagePair pgH sb₁.mem).pageOf side vp =
            (extractPagePair pgH sb₂.mem).pageOf side vp
          rw [he1, he2]
          cases side
          · exact (hdir_s2₁ vp hvp).1.trans (hdir_s2₂ vp hvp).1.symm
          · exact (hdir_s2₁ vp hvp).2.1.trans (hdir_s2₂ vp hvp).2.1.symm
        · simp only [hvp, ↓reduceIte]
      · funext P
        by_cases hP : P < pgH.maxPages
        · have he1 : (extractPagePair pgH sb₁.mem).ownerSide P =
              (extractPagePair pgH s2₁.mem).ownerSide P := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hP, ite_eq_left hP,
              hd1 (4 * P + 2) (by clear *- hP; omega)]
          have he2 : (extractPagePair pgH sb₂.mem).ownerSide P =
              (extractPagePair pgH s2₂.mem).ownerSide P := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hP, ite_eq_left hP,
              hd2 (4 * P + 2) (by clear *- hP; omega)]
          change (extractPagePair pgH sb₁.mem).ownerSide P =
            (extractPagePair pgH sb₂.mem).ownerSide P
          rw [he1, he2, (hdir_s2₁ P hP).2.2.1, (hdir_s2₂ P hP).2.2.1]
        · simp only [hP, ↓reduceIte]
      · funext P
        by_cases hP : P < pgH.maxPages
        · have he1 : (extractPagePair pgH sb₁.mem).ownerVp P =
              (extractPagePair pgH s2₁.mem).ownerVp P := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hP, ite_eq_left hP,
              hd1 (4 * P + 3) (by clear *- hP; omega)]
          have he2 : (extractPagePair pgH sb₂.mem).ownerVp P =
              (extractPagePair pgH s2₂.mem).ownerVp P := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hP, ite_eq_left hP,
              hd2 (4 * P + 3) (by clear *- hP; omega)]
          change (extractPagePair pgH sb₁.mem).ownerVp P =
            (extractPagePair pgH sb₂.mem).ownerVp P
          rw [he1, he2, (hdir_s2₁ P hP).2.2.2, (hdir_s2₂ P hP).2.2.2]
        · simp only [hP, ↓reduceIte]
      · funext side k
        by_cases hk : k < 4 * pgH.pgB
        · have hk8 : k < 8 * pgH.pgB := by clear *- hk; omega
          have he1 : (extractPagePair pgH sb₁.mem).tailRes side k =
              (extractPagePair pgH s2₁.mem).tailRes side k := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hk, ite_eq_left hk]
            cases side <;> exact ht1 _ (by dsimp only; clear *- hk; omega)
          have he2 : (extractPagePair pgH sb₂.mem).tailRes side k =
              (extractPagePair pgH s2₂.mem).tailRes side k := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hk, ite_eq_left hk]
            cases side <;> exact ht2 _ (by dsimp only; clear *- hk; omega)
          change (extractPagePair pgH sb₁.mem).tailRes side k =
            (extractPagePair pgH sb₂.mem).tailRes side k
          rw [he1, he2]
          cases side
          · exact ((htail_eq_s2 k hk8).1 hk).1
          · exact ((htail_eq_s2 k hk8).1 hk).2
        · simp only [hk, ↓reduceIte]
      · funext res
        by_cases hr : res < 8 * pgH.pgB
        · have he1 : (extractPagePair pgH sb₁.mem).tailOwnerSide res =
              (extractPagePair pgH s2₁.mem).tailOwnerSide res := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hr, ite_eq_left hr,
              ht1 (8 * pgH.pgB + res) (by clear *- hr; omega)]
          have he2 : (extractPagePair pgH sb₂.mem).tailOwnerSide res =
              (extractPagePair pgH s2₂.mem).tailOwnerSide res := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hr, ite_eq_left hr,
              ht2 (8 * pgH.pgB + res) (by clear *- hr; omega)]
          change (extractPagePair pgH sb₁.mem).tailOwnerSide res =
            (extractPagePair pgH sb₂.mem).tailOwnerSide res
          rw [he1, he2]; exact (htail_eq_s2 res hr).2.1
        · simp only [hr, ↓reduceIte]
      · funext res
        by_cases hr : res < 8 * pgH.pgB
        · have he1 : (extractPagePair pgH sb₁.mem).tailOwnerRing res =
              (extractPagePair pgH s2₁.mem).tailOwnerRing res := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hr, ite_eq_left hr,
              ht1 (8 * pgH.pgB + res) (by clear *- hr; omega)]
          have he2 : (extractPagePair pgH sb₂.mem).tailOwnerRing res =
              (extractPagePair pgH s2₂.mem).tailOwnerRing res := by
            unfold extractPagePair; dsimp only; rw [ite_eq_left hr, ite_eq_left hr,
              ht2 (8 * pgH.pgB + res) (by clear *- hr; omega)]
          change (extractPagePair pgH sb₁.mem).tailOwnerRing res =
            (extractPagePair pgH sb₂.mem).tailOwnerRing res
          rw [he1, he2]; exact (htail_eq_s2 res hr).2.2
        · simp only [hr, ↓reduceIte]
      · rw [hsb_sp₁.2.2.2.2.2.2.2.2.2.2.2.1, hsb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hsb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hsb_sp₂.2.2.2.2.2.2.2.2.2.2.2.1, hsb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hsb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    unfold extractPageUnperm
    rw [hst_eq, hsb_sp₁.2.2.1, hsb_sp₂.2.2.1, hsb_sp₁.2.2.2.1, hsb_sp₂.2.2.2.1,
      hsb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hsb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  -- Prove `arenaPairAt pgH sp₁.mem = arenaPairAt pgH sp₂.mem`
  have har_eq : arenaPairAt pgH sp₁.mem = arenaPairAt pgH sp₂.mem := by
    have hitem_eq : ∀ a, ibHi ≤ a → sp₁.mem a = sp₂.mem a := fun a ha => by
      have hin67 : Coupled67Region c w base sm₁.mem a := by
        have hsched₁ := hm₁.sched; rw [ite_eq_right (by clear *- hp7₁; omega)] at hsched₁
        obtain ⟨hmDst_eq, hpad_eq, _, _, hibHi_eq, _⟩ := hsched₁.ge2 (by clear *- hp7₁; omega)
        have hlt10 : sm₁.mem (base + hdrPhase) < 10 := by clear *- hp7₁; omega
        have hn_pg : ¬(dualPgHost c 1 w base 0 sm₁.mem).OwnsMetaAddr a := fun hpg =>
          absurd ha (Nat.not_le_of_gt (hdisj_pg₁ a hpg).2.1)
        have hnot_d : ¬(sm₁.mem (base + hdrNDst) ≠ 0 ∧ dualMbDst base sm₁.mem ≤ a ∧
            a < dualMbDst base sm₁.mem + offPageDir c w (sm₁.mem (base + hdrNDst))) := by
          rintro ⟨hd0, _, hhi⟩
          have hth_d := (hsched₁.nDst_bounds.resolve_left hd0).1
          have hod_d := (epochMeta_offsets_le (w := w) hth_d).2.2.2
          have hmD_p : sm₁.mem (base + hdrMDst) ≤ sm₁.mem (base + hdrPad) := by
            rw [hpad_eq]; exact le_max_right _ _
          rw [← hmDst_eq] at hod_d
          unfold dualMbDst at hhi; rw [ite_eq_left hlt10, ite_eq_right hd0] at hhi
          have hi_lo : sm₁.mem (base + hdrItemHi) ≤ a := ha
          rw [hibHi_eq, ite_eq_right hd0] at hi_lo
          split_ifs at hhi <;> (clear *- hod_d hmD_p hhi hi_lo; omega)
        refine ⟨?_, hn_pg, hnot_d⟩
        intro hmeta_d
        by_cases hd0 : sm₁.mem (base + hdrNDst) = 0
        · unfold slotOwnsNonPageMeta dualMbDst at hmeta_d
          rw [ite_eq_left hlt10] at hmeta_d
          simp only [hd0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
            hdrSmallMeta1] at hmeta_d
          have hi_lo : sm₁.mem (base + hdrItemHi) ≤ a := ha
          rw [hibHi_eq, ite_eq_left hd0] at hi_lo; clear *- hmeta_d hi_lo; omega
        · unfold slotOwnsNonPageMeta at hmeta_d
          simp only [hd0, ↓reduceIte] at hmeta_d
          have h32_d : 32 ≤ offPageDir c w (sm₁.mem (base + hdrNDst)) := by
            have hth_d := (hsched₁.nDst_bounds.resolve_left hd0).1
            exact (epochMeta_offsets_le (w := w) hth_d).1.trans
              ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
                (epochMeta_offsets_le (w := w) hth_d).2.2.1)
          rcases hmeta_d with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
            exact hnot_d ⟨hd0, by clear *- g1; omega, by clear *- g2 h32_d; omega⟩
      have hst_fr_eq : st₁.frontier = st₂.frontier := by
        have h1 : sp₁.frontier = st₁.frontier - k_sh := by rw [hsp₁_eq]
        have h2 : sp₂.frontier = st₂.frontier - k_sh := by rw [hsp₂_eq]
        -- Even simpler: compare `clear` on `sp₁` and `sp₂` via `sp₁.frontier = sp₂.frontier`:
        have hf_s2₁ : s2₁.frontier = sm₁.frontier := htb_sp₁.2.2.1
        have hf_s2₂ : s2₂.frontier = sm₂.frontier := htb_sp₂.2.2.1
        have hf_sb₁ : sb₁.frontier = sm₁.frontier := hsb_sp₁.1.trans hf_s2₁
        have hf_sb₂ : sb₂.frontier = sm₂.frontier := hsb_sp₂.1.trans hf_s2₂
        have hf_s3₁ : s3₁.frontier = sm₁.frontier :=
          (runClient_frontier_setSlotIoProg _ _).trans hf_sb₁
        have hf_s3₂ : s3₂.frontier = sm₂.frontier :=
          (runClient_frontier_setSlotIoProg _ _).trans hf_sb₂
        have hf_s4₁ : s4₁.frontier = sm₁.frontier := by
          dsimp only [s4₁, actDst]
          by_cases hd0 : nDst = 0
          · rw [ite_eq_left hd0]
            exact (writeSmallParamTableProg_spec pDst
              ⟨base + hdrSmallMeta1, 0, 0, ⟨1, 1, pgH⟩⟩ s3₁).1.trans hf_s3₁
          · rw [ite_eq_right hd0]
            exact (runClient_frontier_setSlotIoProg _ _).trans hf_s3₁
        have hf_s4₂ : s4₂.frontier = sm₂.frontier := by
          dsimp only [s4₂, actDst]
          by_cases hd0 : nDst = 0
          · rw [ite_eq_left hd0]
            exact (writeSmallParamTableProg_spec pDst
              ⟨base + hdrSmallMeta1, 0, 0, ⟨1, 1, pgH⟩⟩ s3₂).1.trans hf_s3₂
          · rw [ite_eq_right hd0]
            exact (runClient_frontier_setSlotIoProg _ _).trans hf_s3₂
        have ht1 : st₁.frontier = s4₁.frontier := by rw [hst₁_fin, hf_ev₁]
        have ht2 : st₂.frontier = s4₂.frontier := by rw [hst₂_fin, hf_ev₂]
        exact ht1.trans (hf_s4₁.trans (hsch_m.1.trans (hf_s4₂.symm.trans ht2.symm)))
      rw [hsp₁_eq, hsp₂_eq, ← hst_fr_eq]
      dsimp only [Memory.State.mem]
      by_cases hown : (Block.mk (st₁.frontier - k_sh) k_sh).Owns a
      · rw [clear_of_owns hown, clear_of_owns hown]
      · rw [clear_of_not_owns hown, clear_of_not_owns hown,
          hst_sb_out₁ a (by dsimp only [hdrPhase]; clear *- ha hibHi_ge; omega)
            (by dsimp only [hdrRem]; clear *- ha hibHi_ge; omega) (by clear *- ha hibHi_ge; omega),
          hst_sb_out₂ a (by dsimp only [hdrPhase]; clear *- ha hibHi_ge; omega)
            (by dsimp only [hdrRem]; clear *- ha hibHi_ge; omega) (by clear *- ha hibHi_ge; omega),
          hsb_sp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a (by clear *- ha hm_ib; omega),
          hsb_sp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a (by clear *- ha hm_ib; omega),
          hs2_pg₁ a hin67.2.1, hs2_pg₂ a hin67.2.1]
        exact hc67.2 a hin67
    funext p
    unfold arenaPairAt pairQuotAt pairValAt readBitSlice
    have hib_pg : pgH.itemBase = ibHi := rfl
    rw [hib_pg, hitem_eq _ (Nat.le_add_right _ _), hitem_eq _ (by clear *-; omega),
      hitem_eq _ (Nat.le_add_right _ _), hitem_eq _ (by clear *-; omega)]
  -- Assemble `Coupled8`
  refine ⟨hsch_post, ?_⟩
  rw [hpgH_sp₁]
  have hmbS_1_in : Coupled8Region c w base sp₁.mem (dualMbSrc base sp₁.mem + 1) :=
    Or.inr (Or.inl ⟨by clear *-; omega, by split_ifs <;> (clear *-; omega)⟩)
  have hns_eq : sp₂.mem (dualMbSrc base sp₂.mem + 1) = sp₁.mem (dualMbSrc base sp₁.mem + 1) := by
    have hmbS_eq : dualMbSrc base sp₂.mem = dualMbSrc base sp₁.mem := by
      unfold dualMbSrc
      rw [← hsch_post.2 hdrStage (by decide) (by decide),
        ← hsch_post.2 hdrNSrc (by decide) (by decide),
        ← hsch_post.2 hdrPad (by decide) (by decide)]
    rw [hmbS_eq]; exact (hmem_c8 _ hmbS_1_in).symm
  have hdisj_c8 : ∀ addr, Coupled8Region c w base sp₁.mem addr →
      ¬(pagedSlotIo 0 pgH).OwnsAddr addr := by
    intro addr hreg
    have hraw₁ := hsl_src₁; unfold EpochSlotInv at hraw₁
    have hcap_s₁ := hsl8_₁.1
    rcases hreg with ⟨h1, h2⟩ | hmeta
    · by_cases hc0 : L_post₁.slotSrc.nCap = 0
      · rw [ite_eq_left hc0] at hraw₁
        exact fun hia => hraw₁.2.2.2.2.1 addr h1 h2 (Or.inr (Or.inr hia))
      · rw [ite_eq_right hc0] at hraw₁
        exact hraw₁.1.disj_pBase_io addr h1 h2
    · rw [← hcap_s₁] at hmeta
      unfold slotOwnsNonPageMeta at hmeta
      by_cases hc0 : L_post₁.slotSrc.nCap = 0
      · rw [ite_eq_left hc0] at hraw₁ hmeta
        rcases hmeta with ⟨g1, g2⟩ | ⟨hne, _⟩
        · exact hraw₁.2.2.1.disjoint_hdr addr (by dsimp only; clear *- g1 g2; omega)
        · exact absurd hc0 hne
      · rw [ite_eq_right hc0] at hraw₁ hmeta
        exact hraw₁.1.disj_fast_io addr (hmeta.imp id And.right)
  exact
    { fr_eq := hsch_post.1
      side_zero := rfl
      valid₁ := by
        have hv := hsl_src₁.io_valid
        have hw_pg : (pagedSlotIo 0 pgH).pgL.w = w := rfl
        rwa [hw_pg]
      disj := hdisj_c8
      mem_eq := hmem_c8
      inv₁ := hsl_src₁.io_stateInv
      inv₂ := hns_eq ▸ hsl_src₂.io_stateInv
      pair_eq := fun idx _ => by
        unfold slotIoPairAt pagedSlotIo SlotIoLayout.side
        simp only [ne_eq, one_ne_zero, ↓reduceIte]
        rw [hu_sp₁, hu_sp₂, hu_eq, har_eq] }

private theorem coupled67_mutate_step_aux {c U V w base opTag k_sh : ℕ}
    {s_dict' : Dictionary.State U}
    {Lm₁ Lm₂ Lt₁ Lt₂ Lp₁ Lp₂ : DualLatent c U V}
    {sm₁ sm₂ st₁ st₂ sps₁ sps₂ s_post₁ s_post₂ : Memory.State}
    (hop_nz : opTag ≠ 0)
    (hp67 : sm₁.mem (base + hdrPhase) = 6 ∨ sm₁.mem (base + hdrPhase) = 7)
    (hc67_mid : Coupled67 c w base sm₁ sm₂)
    (hmid₁ : DualMidInv c U V w base s_dict' Lm₁ sm₁)
    (hmid₂ : DualMidInv c U V w base s_dict' Lm₂ sm₂)
    (hst₁_bg : st₁ = (Memory.spec 0).clientState sm₁ (bgTickProg (base, sm₁.frontier)))
    (hst₂_bg : st₂ = (Memory.spec 0).clientState sm₂ (bgTickProg (base, sm₂.frontier)))
    (hpre₁ : DualPreShrinkInv c U V w base s_dict' Lt₁ st₁)
    (hpre₂ : DualPreShrinkInv c U V w base s_dict' Lt₂ st₂)
    (hksh_def : k_sh = (Memory.spec 0).clientResult st₁
      (postRandShrinkProg ((base, st₁.frontier), opTag)))
    (hsps₁_def : sps₁ = (Memory.spec 0).clientState st₁
      (postRandShrinkProg ((base, st₁.frontier), opTag)))
    (hsps₂_def : sps₂ = (Memory.spec 0).clientState st₂
      (postRandShrinkProg ((base, st₂.frontier), opTag)))
    (hpost₁_def : s_post₁ = { mem := clear sps₁.mem (st₁.frontier - k_sh) k_sh,
                              frontier := st₁.frontier - k_sh })
    (hpost₂_def : s_post₂ = { mem := clear sps₂.mem (st₂.frontier - k_sh) k_sh,
                              frontier := st₂.frontier - k_sh })
    (hsch_post : SchedEq base s_post₁ s_post₂)
    (h_post₁ : DualStateInv c U V w base s_dict' Lp₁ s_post₁)
    (h_post₂ : DualStateInv c U V w base s_dict' Lp₂ s_post₂) :
    ((s_post₁.mem (base + hdrPhase) = 6 ∨ s_post₁.mem (base + hdrPhase) = 7) ∧
      Coupled67 c w base s_post₁ s_post₂) ∨
    (s_post₁.mem (base + hdrPhase) = 8 ∧
      Coupled8 c V w base (Dictionary.dom s_dict').card s_post₁ s_post₂) := by
  have hsm₁_ph : sm₁.mem (base + hdrPhase) = sm₁.mem (base + hdrPhase) := rfl
  have hsm₂_ph : sm₂.mem (base + hdrPhase) = sm₁.mem (base + hdrPhase) :=
    (hc67_mid.1.2 hdrPhase (by decide) (by decide)).symm
  -- Note `sps₁ = st₁` and `sps₂ = st₂` when `ph ∈ {6, 7, 8}`
  have hsps_eq : ∀ {st : Memory.State} {L : DualLatent c U V},
      DualPreShrinkInv c U V w base s_dict' L st →
      6 ≤ st.mem (base + hdrPhase) → st.mem (base + hdrPhase) ≤ 8 →
      (Memory.spec 0).clientState st (postRandShrinkProg ((base, st.frontier), opTag)) = st ∧
      (Memory.spec 0).clientResult st (postRandShrinkProg ((base, st.frontier), opTag)) =
        (Memory.spec 0).clientResult st (postRandShrinkProg ((base, st.frontier), 1)) := by
    intro st L hpre hge6 hle8
    have hbr := hpre.2.2.2
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)] at hbr
    have hw_st : st.mem (base + hdrW) = w := hbr.2.2.hdr.2.2.1
    have hw_pos : 0 < w := by have := hmid₁.hw11; omega
    have hnr_op : ¬(st.mem (base + hdrPhase) = 5 ∧
        st.mem ((if st.mem (base + hdrStage) = 0 then base + hdrPBase1
          else base + hdrPBase0) + 31) ≤ st.mem (base + hdrCur)) := fun h => by omega
    obtain ⟨hs1, hr1, _⟩ := postRandShrinkProg_eval base st.frontier opTag st
    obtain ⟨_, hr2, _⟩ := postRandShrinkProg_eval base st.frontier 1 st
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hs1 hr1 hr2
    rw [ite_eq_right hop_nz, ite_eq_right hnr_op] at hs1 hr1
    rw [ite_eq_right Nat.one_ne_zero, ite_eq_right hnr_op] at hr2
    obtain ⟨hc_s, _, _⟩ := calcPostShrinkProg_eval (curFr := st.frontier) (hw_st ▸ hw_pos)
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hc_s
    rw [ite_eq_right (fun h => by have := h.1; omega)] at hc_s
    exact ⟨hs1.trans hc_s, hr1.trans hr2.symm⟩
  -- Determine `st₁.mem (base + hdrPhase) ∈ {6, 7, 8}`
  rcases hp67 with hp6 | hp7
  · -- `ph = 6`: `tickInitDirProg` transitions to `6` or `7`, modifying only `pgH.OwnsMetaAddr`
    -- and `< base + 48`
    left
    obtain ⟨_, _, _, _, _, hctx1_₁, _, _, hv_m₁⟩ :=
      dualPgHost_eval_valid hmid₁ (by rw [hp6]; decide) (by rw [hp6]; decide)
    obtain ⟨_, _, _, _, _, hctx1_₂, _, _, hv_m₂⟩ :=
      dualPgHost_eval_valid hmid₂ (by rw [hsm₂_ph, hp6]; decide) (by rw [hsm₂_ph, hp6]; decide)
    have hdisj_pg₁ := disjoint_pgHost_nonPageMeta (nc := 0) hmid₁
      (by rw [hp6]; decide) (by rw [hp6]; decide)
    set nHost := dualNHost base sm₁.mem
    set mbHost := dualMbHost base sm₁.mem
    set ibHi := sm₁.mem (base + hdrItemHi)
    set pgM := hostPageLayout c w nHost mbHost ibHi 0 0 nHost
    have hpgM_eq₂ : hostPageLayout c w (dualNHost base sm₂.mem) (dualMbHost base sm₂.mem)
        (sm₂.mem (base + hdrItemHi)) 0 0 (dualNHost base sm₂.mem) = pgM := by
      dsimp only [pgM]; unfold dualNHost dualMbHost
      rw [← hc67_mid.1.2 hdrNDst (by decide) (by decide),
        ← hc67_mid.1.2 hdrNSrc (by decide) (by decide),
        ← hc67_mid.1.2 hdrStage (by decide) (by decide),
        ← hc67_mid.1.2 hdrPad (by decide) (by decide),
        ← hc67_mid.1.2 hdrItemHi (by decide) (by decide)]
    rw [hpgM_eq₂] at hctx1_₂ hv_m₂
    have hm_ofCtx : PageArenaLayout.ofCtx pgM.toCtx = pgM := PageArenaLayout.ofCtx_toCtx pgM
    have hcur_eq₂ : sm₂.mem (base + hdrCur) = sm₁.mem (base + hdrCur) :=
      (hc67_mid.1.2 hdrCur (by decide) (by decide)).symm
    have hcur_le₁ : sm₁.mem (base + hdrCur) ≤ pgM.maxPages := (hmid₁.ph6_inv hp6).1
    have hdb_sp₁ := pageInitDirBatchProg_spec (L := pgM) (cur := sm₁.mem (base + hdrCur))
      (s := sm₁) hv_m₁ hcur_le₁ bulkBatchWhp
    have hdb_sp₂ := pageInitDirBatchProg_spec (L := pgM) (cur := sm₁.mem (base + hdrCur))
      (s := sm₂) hv_m₂ hcur_le₁ bulkBatchWhp
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hdb_sp₁ hdb_sp₂
    have hbgev₁ := (bgTickProg_eval base sm₁.frontier sm₁).1
    have hbgev₂ := (bgTickProg_eval base sm₂.frontier sm₂).1
    rw [hp6] at hbgev₁; rw [hsm₂_ph, hp6] at hbgev₂
    simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev₁ hbgev₂
    have htdev₁ := (tickInitDirProg_eval base sm₁).1
    have htdev₂ := (tickInitDirProg_eval base sm₂).1
    rw [hctx1_₁, hm_ofCtx, hmid₁.live_eq] at htdev₁
    rw [hctx1_₂, hm_ofCtx, hmid₂.live_eq, hcur_eq₂, hdb_sp₂.2.1, ← hdb_sp₁.2.1] at htdev₂
    set db := pageInitDirBatchProg ((pgM.toCtx, sm₁.mem (base + hdrCur)), bulkBatchWhp)
    set cur' := (Memory.spec 0).clientResult sm₁ db
    have hst₁_ph67 : st₁.mem (base + hdrPhase) = 6 ∨ st₁.mem (base + hdrPhase) = 7 := by
      rw [hst₁_bg, hbgev₁, htdev₁]
      by_cases hlt_c : cur' < pgM.maxPages
      · rw [ite_eq_left hlt_c]; left
        dsimp only [Memory.State.mem]
        rw [Function.update_of_ne (base_add_ne (by decide)),
          hdb_sp₁.2.2.2.2.1 _ (fun hd => by
            have := (hdisj_pg₁ _ (Or.inr (Or.inl hd))).1; dsimp only [hdrPhase] at this; omega)]
        exact hp6
      · rw [ite_eq_right hlt_c]; right; dsimp only [Memory.State.mem]; exact Function.update_self ..
    obtain ⟨hsps₁_id0, _⟩ := hsps_eq hpre₁
      (by rcases hst₁_ph67 with h | h <;> omega) (by rcases hst₁_ph67 with h | h <;> omega)
    have hsps₁_id : sps₁ = st₁ := hsps₁_def.trans hsps₁_id0
    have hst₂_ph_eq : st₂.mem (base + hdrPhase) = st₁.mem (base + hdrPhase) := by
      rw [hst₁_bg, hbgev₁, htdev₁, hst₂_bg, hbgev₂, htdev₂]
      by_cases hlt_c : cur' < pgM.maxPages
      · rw [ite_eq_left hlt_c, ite_eq_left hlt_c]; dsimp only [Memory.State.mem]
        rw [Function.update_of_ne (base_add_ne (by decide)),
          Function.update_of_ne (base_add_ne (by decide)),
          hdb_sp₁.2.2.2.2.1 _ (fun hd => by
            have := (hdisj_pg₁ _ (Or.inr (Or.inl hd))).1; dsimp only [hdrPhase] at this; omega),
          hdb_sp₂.2.2.2.2.1 _ (fun hd => by
            have := (hdisj_pg₁ _ (Or.inr (Or.inl hd))).1; dsimp only [hdrPhase] at this; omega),
          hsm₂_ph]
      · rw [ite_eq_right hlt_c, ite_eq_right hlt_c]
        dsimp only [Memory.State.mem]; rw [Function.update_self, Function.update_self]
    obtain ⟨hsps₂_id0, _⟩ := hsps_eq hpre₂
      (by rw [hst₂_ph_eq]; rcases hst₁_ph67 with h | h <;> omega)
      (by rw [hst₂_ph_eq]; rcases hst₁_ph67 with h | h <;> omega)
    have hsps₂_id : sps₂ = st₂ := hsps₂_def.trans hsps₂_id0
    have hb192_post : base + 192 ≤ st₁.frontier - k_sh := by
      have hb := h_post₁.base_fr; rw [hpost₁_def] at hb; exact hb
    have hpost₁_ph : s_post₁.mem (base + hdrPhase) = st₁.mem (base + hdrPhase) := by
      rw [hpost₁_def, hsps₁_id]; dsimp only [Memory.State.mem]
      rw [clear_of_not_owns
        (by simp only [Block.Owns]; dsimp only [hdrPhase]; clear *- hb192_post; omega)]
    refine ⟨hpost₁_ph ▸ hst₁_ph67, hsch_post, fun addr hreg => ?_⟩
    have hst_fr_eq : st₁.frontier = st₂.frontier := by
      rw [hst₁_bg, hbgev₁, htdev₁, hst₂_bg, hbgev₂, htdev₂]
      by_cases hlt_c : cur' < pgM.maxPages
      · rw [ite_eq_left hlt_c, ite_eq_left hlt_c]
        exact hdb_sp₁.2.2.1.trans (hc67_mid.1.1.trans hdb_sp₂.2.2.1.symm)
      · rw [ite_eq_right hlt_c, ite_eq_right hlt_c]
        exact hdb_sp₁.2.2.1.trans (hc67_mid.1.1.trans hdb_sp₂.2.2.1.symm)
    have hpost₁_hdr : ∀ off < 48, off ≠ hdrPhase → off ≠ hdrCur → off ≠ hdrQSnap → off ≠ hdrNSnap →
        s_post₁.mem (base + off) = sm₁.mem (base + off) := fun off hoff h1 h2 h3 h4 => by
      rw [hpost₁_def, hsps₁_id]; dsimp only [Memory.State.mem]
      rw [clear_of_not_owns (by simp only [Block.Owns]; clear *- hoff hb192_post; omega),
        hst₁_bg, hbgev₁, htdev₁]
      by_cases hlt_c : cur' < pgM.maxPages
      · rw [ite_eq_left hlt_c]; dsimp only [Memory.State.mem]
        rw [Function.update_of_ne (base_add_ne h2)]
        exact hdb_sp₁.2.2.2.2.1 _ (fun hd => by
          have := (hdisj_pg₁ _ (Or.inr (Or.inl hd))).1; clear *- hoff this; omega)
      · rw [ite_eq_right hlt_c]; dsimp only [Memory.State.mem]
        rw [Function.update_of_ne (base_add_ne h1), Function.update_of_ne (base_add_ne h2),
          Function.update_of_ne (base_add_ne h3), Function.update_of_ne (base_add_ne h4)]
        exact hdb_sp₁.2.2.2.2.1 _ (fun hd => by
          have := (hdisj_pg₁ _ (Or.inr (Or.inl hd))).1; clear *- hoff this; omega)
    have hreg_m : Coupled67Region c w base sm₁.mem addr := by
      unfold Coupled67Region dualMbDst dualPgHost dualNHost dualMbHost at hreg ⊢
      have hp_lt10_p : s_post₁.mem (base + hdrPhase) < 10 := by
        rw [hpost₁_ph]; rcases hst₁_ph67 with h | h <;> omega
      have hp_lt10_m : sm₁.mem (base + hdrPhase) < 10 := by rw [hp6]; decide
      rw [ite_eq_left hp_lt10_p,
        hpost₁_hdr hdrNDst (by decide) (by decide) (by decide) (by decide) (by decide),
        hpost₁_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide) (by decide),
        hpost₁_hdr hdrStage (by decide) (by decide) (by decide) (by decide) (by decide),
        hpost₁_hdr hdrPad (by decide) (by decide) (by decide) (by decide) (by decide),
        hpost₁_hdr hdrItemHi (by decide) (by decide) (by decide) (by decide) (by decide),
        hpost₁_hdr hdrQHi (by decide) (by decide) (by decide) (by decide) (by decide)] at hreg
      rw [ite_eq_left hp_lt10_m]; exact hreg
    by_cases hh4 : addr = base + hdrPhase ∨ addr = base + hdrCur ∨
        addr = base + hdrQSnap ∨ addr = base + hdrNSnap
    · rcases hh4 with rfl | rfl | rfl | rfl
      · exact hsch_post.2 hdrPhase (by decide) (by decide)
      · exact hsch_post.2 hdrCur (by decide) (by decide)
      · exact hsch_post.2 hdrQSnap (by decide) (by decide)
      · exact hsch_post.2 hdrNSnap (by decide) (by decide)
    · simp only [not_or] at hh4
      obtain ⟨hn_ph, hn_cur, hn_qs, hn_ns⟩ := hh4
      rw [hpost₁_def, hpost₂_def, hsps₁_id, hsps₂_id, ← hst_fr_eq]
      dsimp only [Memory.State.mem]
      by_cases hown : (Block.mk (st₁.frontier - k_sh) k_sh).Owns addr
      · rw [clear_of_owns hown, clear_of_owns hown]
      · rw [clear_of_not_owns hown, clear_of_not_owns hown,
          hst₁_bg, hbgev₁, htdev₁, hst₂_bg, hbgev₂, htdev₂]
        have hn_dir := fun hd => hreg_m.2.1 (Or.inr (Or.inl hd))
        by_cases hlt_c : cur' < pgM.maxPages
        · rw [ite_eq_left hlt_c, ite_eq_left hlt_c]; dsimp only [Memory.State.mem]
          rw [Function.update_of_ne hn_cur, Function.update_of_ne hn_cur,
            hdb_sp₁.2.2.2.2.1 addr hn_dir, hdb_sp₂.2.2.2.2.1 addr hn_dir]
          exact hc67_mid.2 addr hreg_m
        · rw [ite_eq_right hlt_c, ite_eq_right hlt_c]; dsimp only [Memory.State.mem]
          rw [Function.update_of_ne hn_ph, Function.update_of_ne hn_cur,
            Function.update_of_ne hn_qs, Function.update_of_ne hn_ns,
            Function.update_of_ne hn_ph, Function.update_of_ne hn_cur,
            Function.update_of_ne hn_qs, Function.update_of_ne hn_ns,
            hdb_sp₁.2.2.2.2.1 addr hn_dir, hdb_sp₂.2.2.2.2.1 addr hn_dir]
          exact hc67_mid.2 addr hreg_m
  · -- `ph = 7`: either `7 → 7` (`Coupled67`) or `7 → 8` (`Coupled8`)
    obtain ⟨_, _, _, _, _, hctx1_₁, _, _, hv_m₁⟩ :=
      dualPgHost_eval_valid hmid₁ (by rw [hp7]; decide) (by rw [hp7]; decide)
    obtain ⟨_, _, _, _, _, hctx1_₂, _, _, hv_m₂⟩ :=
      dualPgHost_eval_valid hmid₂ (by rw [hsm₂_ph, hp7]; decide) (by rw [hsm₂_ph, hp7]; decide)
    have hdisj_pg₁ := disjoint_pgHost_nonPageMeta (nc := 0) hmid₁
      (by rw [hp7]; decide) (by rw [hp7]; decide)
    set nHost := dualNHost base sm₁.mem
    set mbHost := dualMbHost base sm₁.mem
    set ibHi := sm₁.mem (base + hdrItemHi)
    set pgM := hostPageLayout c w nHost mbHost ibHi 0 0 nHost
    have hpgM_eq₂ : hostPageLayout c w (dualNHost base sm₂.mem) (dualMbHost base sm₂.mem)
        (sm₂.mem (base + hdrItemHi)) 0 0 (dualNHost base sm₂.mem) = pgM := by
      dsimp only [pgM]; unfold dualNHost dualMbHost
      rw [← hc67_mid.1.2 hdrNDst (by decide) (by decide),
        ← hc67_mid.1.2 hdrNSrc (by decide) (by decide),
        ← hc67_mid.1.2 hdrStage (by decide) (by decide),
        ← hc67_mid.1.2 hdrPad (by decide) (by decide),
        ← hc67_mid.1.2 hdrItemHi (by decide) (by decide)]
    rw [hpgM_eq₂] at hctx1_₂ hv_m₂
    have hm_ofCtx : PageArenaLayout.ofCtx pgM.toCtx = pgM := PageArenaLayout.ofCtx_toCtx pgM
    obtain ⟨hns_h₁, _, _, ⟨_, _, hcur_lt8₁, _, _⟩, _⟩ := hmid₁.ph7_inv hp7
    have hcur_eq₂ : sm₂.mem (base + hdrCur) = sm₁.mem (base + hdrCur) :=
      (hc67_mid.1.2 hdrCur (by decide) (by decide)).symm
    have hns_eq₂ : sm₂.mem (base + hdrNSnap) = sm₁.mem (base + hdrNSnap) :=
      (hc67_mid.1.2 hdrNSnap (by decide) (by decide)).symm
    have htb_sp₁ := pageInitTailBatchProg_spec (L := pgM) (n_0 := sm₁.mem (base + hdrNSnap))
      (cur := sm₁.mem (base + hdrCur)) (s := sm₁) hv_m₁ hns_h₁ hcur_lt8₁.le tailBatchWhp
    have htb_sp₂ := pageInitTailBatchProg_spec (L := pgM) (n_0 := sm₁.mem (base + hdrNSnap))
      (cur := sm₁.mem (base + hdrCur)) (s := sm₂) hv_m₂ hns_h₁ hcur_lt8₁.le tailBatchWhp
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at htb_sp₁ htb_sp₂
    have hbgev₁ := (bgTickProg_eval base sm₁.frontier sm₁).1
    have hbgev₂ := (bgTickProg_eval base sm₂.frontier sm₂).1
    rw [hp7] at hbgev₁; rw [hsm₂_ph, hp7] at hbgev₂
    simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev₁ hbgev₂
    have httev₁ := (tickInitTailProg_eval base sm₁).1
    have httev₂ := (tickInitTailProg_eval base sm₂).1
    rw [hctx1_₁, hm_ofCtx] at httev₁
    rw [hctx1_₂, hm_ofCtx, hns_eq₂, hcur_eq₂, htb_sp₂.2.1, ← htb_sp₁.2.1] at httev₂
    set tb := pageInitTailBatchProg
      (((pgM.toCtx, sm₁.mem (base + hdrNSnap)), sm₁.mem (base + hdrCur)), tailBatchWhp)
    by_cases hlt8 : (Memory.spec 0).clientResult sm₁ tb < 8 * pgM.pgB
    · -- `7 → 7`: stays in `Coupled67`
      left
      have hst₁_ph7 : st₁.mem (base + hdrPhase) = 7 := by
        rw [hst₁_bg, hbgev₁, httev₁, ite_eq_left hlt8]; dsimp only [Memory.State.mem]
        rw [Function.update_of_ne (base_add_ne (by decide)),
          htb_sp₁.2.2.2.2.1 _ (fun ht => by
            have := (hdisj_pg₁ _ (Or.inr (Or.inr ht))).1; dsimp only [hdrPhase] at this; omega)]
        exact hp7
      have hst₂_ph7 : st₂.mem (base + hdrPhase) = 7 := by
        rw [hst₂_bg, hbgev₂, httev₂, ite_eq_left hlt8]; dsimp only [Memory.State.mem]
        rw [Function.update_of_ne (base_add_ne (by decide)),
          htb_sp₂.2.2.2.2.1 _ (fun ht => by
            have := (hdisj_pg₁ _ (Or.inr (Or.inr ht))).1; dsimp only [hdrPhase] at this; omega)]
        exact hsm₂_ph.trans hp7
      obtain ⟨hsps₁_id0, _⟩ := hsps_eq hpre₁ (by omega) (by omega)
      obtain ⟨hsps₂_id0, _⟩ := hsps_eq hpre₂ (by omega) (by omega)
      have hsps₁_id : sps₁ = st₁ := hsps₁_def.trans hsps₁_id0
      have hsps₂_id : sps₂ = st₂ := hsps₂_def.trans hsps₂_id0
      have hb192_post : base + 192 ≤ st₁.frontier - k_sh := by
        have hb := h_post₁.base_fr; rw [hpost₁_def] at hb; exact hb
      have hpost₁_ph7 : s_post₁.mem (base + hdrPhase) = 7 := by
        rw [hpost₁_def, hsps₁_id]; dsimp only [Memory.State.mem]
        rw [clear_of_not_owns
          (by simp only [Block.Owns]; dsimp only [hdrPhase]; clear *- hb192_post; omega)]
        exact hst₁_ph7
      refine ⟨Or.inr hpost₁_ph7, hsch_post, fun addr hreg => ?_⟩
      have hst_fr_eq : st₁.frontier = st₂.frontier := by
        rw [hst₁_bg, hbgev₁, httev₁, ite_eq_left hlt8, hst₂_bg, hbgev₂, httev₂, ite_eq_left hlt8]
        exact htb_sp₁.2.2.1.trans (hc67_mid.1.1.trans htb_sp₂.2.2.1.symm)
      have hpost₁_hdr : ∀ off < 48, off ≠ hdrCur →
          s_post₁.mem (base + off) = sm₁.mem (base + off) := fun off hoff hc => by
        rw [hpost₁_def, hsps₁_id]; dsimp only [Memory.State.mem]
        rw [clear_of_not_owns (by simp only [Block.Owns]; clear *- hoff hb192_post; omega),
          hst₁_bg, hbgev₁, httev₁, ite_eq_left hlt8]; dsimp only [Memory.State.mem]
        rw [Function.update_of_ne (base_add_ne hc)]
        exact htb_sp₁.2.2.2.2.1 _ (fun ht => by
          have := (hdisj_pg₁ _ (Or.inr (Or.inr ht))).1; clear *- hoff this; omega)
      have hreg_m : Coupled67Region c w base sm₁.mem addr := by
        unfold Coupled67Region dualMbDst dualPgHost dualNHost dualMbHost at hreg ⊢
        rw [hpost₁_ph7,
          hpost₁_hdr hdrNDst (by decide) (by decide),
          hpost₁_hdr hdrNSrc (by decide) (by decide),
          hpost₁_hdr hdrStage (by decide) (by decide),
          hpost₁_hdr hdrPad (by decide) (by decide),
          hpost₁_hdr hdrItemHi (by decide) (by decide),
          hpost₁_hdr hdrQHi (by decide) (by decide)] at hreg
        rw [hp7]; exact hreg
      rw [hpost₁_def, hpost₂_def, hsps₁_id, hsps₂_id, ← hst_fr_eq]
      dsimp only [Memory.State.mem]
      by_cases hown : (Block.mk (st₁.frontier - k_sh) k_sh).Owns addr
      · rw [clear_of_owns hown, clear_of_owns hown]
      · rw [clear_of_not_owns hown, clear_of_not_owns hown,
          hst₁_bg, hbgev₁, httev₁, ite_eq_left hlt8,
          hst₂_bg, hbgev₂, httev₂, ite_eq_left hlt8]
        dsimp only [Memory.State.mem]
        by_cases hc_a : addr = base + hdrCur
        · subst hc_a; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hc_a, Function.update_of_ne hc_a,
            htb_sp₁.2.2.2.2.1 addr (fun ht => hreg_m.2.1 (Or.inr (Or.inr ht))),
            htb_sp₂.2.2.2.2.1 addr (fun ht => hreg_m.2.1 (Or.inr (Or.inr ht)))]
          exact hc67_mid.2 addr hreg_m
    · -- `7 → 8`: `finishInitTailProg` runs, entering `Coupled8`
      right
      have hst₁_ph8 : st₁.mem (base + hdrPhase) = 8 := by
        obtain ⟨_, _, _, _, hctx0_₁, _, _, _, _⟩ :=
          dualPgHost_eval_valid hmid₁ (by rw [hp7]; decide) (by rw [hp7]; decide)
        have hdisj_pg_live := disjoint_pgHost_nonPageMeta
          (nc := (Dictionary.dom s_dict').card) hmid₁
          (by rw [hp7]; decide) (by rw [hp7]; decide)
        set s2₁ := (Memory.spec 0).clientState sm₁ tb
        have hs2_hdr₁ : ∀ off < 192, s2₁.mem (base + off) = sm₁.mem (base + off) := fun off h192 =>
          htb_sp₁.2.2.2.2.1 (base + off) (fun ht => by
            have := (hdisj_pg_live _ (Or.inr (Or.inr ht))).1; clear *- h192 this; omega)
        have hctx0_s2₁ : (Memory.spec 0).clientResult s2₁ (loadHostCtxProg (base, 0)) =
            (dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem).toCtx := by
          rw [← hctx0_₁, (loadHostCtxProg_eval base 0 s2₁).2.1,
            (loadHostCtxProg_eval base 0 sm₁).2.1]
          simp only [↓reduceIte]
          have h_od : ∀ k ≤ 4,
              s2₁.mem (base +
                (if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) =
              sm₁.mem (base +
                (if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) :=
            fun k hk => by
              rw [Nat.add_assoc]
              exact hs2_hdr₁ _
                (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> (clear *- hk; omega))
          rw [hs2_hdr₁ hdrStage (by decide), hs2_hdr₁ hdrNDst (by decide),
            hs2_hdr₁ hdrPad (by decide), hs2_hdr₁ hdrW (by decide),
            hs2_hdr₁ hdrItemHi (by decide), hs2_hdr₁ hdrQHi (by decide),
            hs2_hdr₁ hdrValBits (by decide), hs2_hdr₁ hdrLive (by decide),
            show s2₁.mem (base + if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) =
              sm₁.mem (base + if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) by
              simpa only [Nat.add_zero] using h_od 0 (by decide),
            h_od 1 (by decide), h_od 2 (by decide), h_od 3 (by decide), h_od 4 (by decide)]
        have hf_ev₁ := (finishInitTailProg_eval base s2₁).1
        rw [hctx0_s2₁, PageArenaLayout.ofCtx_toCtx] at hf_ev₁
        rw [hst₁_bg, hbgev₁, httev₁, ite_eq_right hlt8, hf_ev₁]
        dsimp only [Memory.State.mem]; exact Function.update_self ..
      have hst₂_ph8 : st₂.mem (base + hdrPhase) = 8 := by
        obtain ⟨_, _, _, _, hctx0_₂, _, _, _, _⟩ :=
          dualPgHost_eval_valid hmid₂ (by rw [hsm₂_ph, hp7]; decide) (by rw [hsm₂_ph, hp7]; decide)
        set s2₂ := (Memory.spec 0).clientState sm₂ tb
        have hs2_hdr₂ : ∀ off < 192, s2₂.mem (base + off) = sm₂.mem (base + off) := fun off h192 =>
          htb_sp₂.2.2.2.2.1 (base + off) (fun ht => by
            have := (hdisj_pg₁ _ (Or.inr (Or.inr ht))).1; clear *- h192 this; omega)
        have hctx0_s2₂ : (Memory.spec 0).clientResult s2₂ (loadHostCtxProg (base, 0)) =
            (dualPgHost c V w base (Dictionary.dom s_dict').card sm₂.mem).toCtx := by
          rw [← hctx0_₂, (loadHostCtxProg_eval base 0 s2₂).2.1,
            (loadHostCtxProg_eval base 0 sm₂).2.1]
          simp only [↓reduceIte]
          have h_od : ∀ k ≤ 4,
              s2₂.mem (base +
                (if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) =
              sm₂.mem (base +
                (if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) :=
            fun k hk => by
              rw [Nat.add_assoc]
              exact hs2_hdr₂ _
                (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> (clear *- hk; omega))
          rw [hs2_hdr₂ hdrStage (by decide), hs2_hdr₂ hdrNDst (by decide),
            hs2_hdr₂ hdrPad (by decide), hs2_hdr₂ hdrW (by decide),
            hs2_hdr₂ hdrItemHi (by decide), hs2_hdr₂ hdrQHi (by decide),
            hs2_hdr₂ hdrValBits (by decide), hs2_hdr₂ hdrLive (by decide),
            show s2₂.mem (base + if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) =
              sm₂.mem (base + if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) by
              simpa only [Nat.add_zero] using h_od 0 (by decide),
            h_od 1 (by decide), h_od 2 (by decide), h_od 3 (by decide), h_od 4 (by decide)]
        have hf_ev₂ := (finishInitTailProg_eval base s2₂).1
        rw [hctx0_s2₂, PageArenaLayout.ofCtx_toCtx] at hf_ev₂
        rw [hst₂_bg, hbgev₂, httev₂, ite_eq_right hlt8, hf_ev₂]
        dsimp only [Memory.State.mem]; exact Function.update_self ..
      obtain ⟨hsps₁_id0, hksh_1⟩ := hsps_eq hpre₁ (by omega) (by omega)
      obtain ⟨hsps₂_id0, _⟩ := hsps_eq hpre₂ (by omega) (by omega)
      have hsps₁_id : sps₁ = st₁ := hsps₁_def.trans hsps₁_id0
      have hsps₂_id : sps₂ = st₂ := hsps₂_def.trans hsps₂_id0
      have hb192_post : base + 192 ≤ st₁.frontier - k_sh := by
        have hb := h_post₁.base_fr; rw [hpost₁_def] at hb; exact hb
      have hpost₁_ph8 : s_post₁.mem (base + hdrPhase) = 8 := by
        rw [hpost₁_def, hsps₁_id]; dsimp only [Memory.State.mem]
        rw [clear_of_not_owns
          (by simp only [Block.Owns]; dsimp only [hdrPhase]; clear *- hb192_post; omega)]
        exact hst₁_ph8
      refine ⟨hpost₁_ph8, finishInitTail_coupled8_aux hmid₁ hmid₂ hc67_mid hp7
        rfl hst₁_bg hst₂_bg (hksh_def.trans hksh_1) ?_ ?_ hsch_post hpost₁_ph8 h_post₁ h_post₂⟩
      · rw [hpost₁_def, hsps₁_id]
      · rw [hpost₂_def, hsps₂_id]

/-- Phases `6..7` mutation congruence: preserves `Coupled67` across `6 → 6`, `6 → 7`, and `7 → 7`,
and establishes `Coupled8` upon `7 → 8`. -/
theorem coupled67_mutate_step {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L₁ L₂ : DualLatent c U V}
    {s₁ s₂ : Memory.State}
    (h₁ : DualStateInv c U V w base s_dict L₁ s₁)
    (h₂ : DualStateInv c U V w base s_dict L₂ s₂)
    (hc67 : Coupled67 c w base s₁ s₂)
    (hp67 : s₁.mem (base + hdrPhase) = 6 ∨ s₁.mem (base + hdrPhase) = 7)
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
      base + dualPaddedWords c U V w (s₁.mem (base + hdrNSrc))
        (if s₁.mem (base + hdrPhase) = 0 then s₁.mem (base + hdrNSrc)
         else s₁.mem (base + hdrNDst)) (Dictionary.dom s_dict').card < 2 ^ w) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let k_grow :=
      (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))
    let sp₁ :=
      (Memory.spec 0).clientState s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))
    let sp₂ :=
      (Memory.spec 0).clientState s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val))
    let sg₁ : Memory.State := { mem := sp₁.mem, frontier := s₁.frontier + k_grow }
    let sg₂ : Memory.State := { mem := sp₂.mem, frontier := s₂.frontier + k_grow }
    let st₁ :=
      (Memory.spec 0).clientState sg₁ (stepOpProg (((base, sg₁.frontier), opTag), (u.val, v_val)))
    let st₂ :=
      (Memory.spec 0).clientState sg₂ (stepOpProg (((base, sg₂.frontier), opTag), (u.val, v_val)))
    let k_sh :=
      (Memory.spec 0).clientResult st₁ (postRandShrinkProg ((base, st₁.frontier), opTag))
    let sps₁ :=
      (Memory.spec 0).clientState st₁ (postRandShrinkProg ((base, st₁.frontier), opTag))
    let sps₂ :=
      (Memory.spec 0).clientState st₂ (postRandShrinkProg ((base, st₂.frontier), opTag))
    let s_post₁ : Memory.State :=
      { mem := clear sps₁.mem (st₁.frontier - k_sh) k_sh, frontier := st₁.frontier - k_sh }
    let s_post₂ : Memory.State :=
      { mem := clear sps₂.mem (st₂.frontier - k_sh) k_sh, frontier := st₂.frontier - k_sh }
    ((s_post₁.mem (base + hdrPhase) = 6 ∨ s_post₁.mem (base + hdrPhase) = 7) ∧
      Coupled67 c w base s_post₁ s_post₂) ∨
    (s_post₁.mem (base + hdrPhase) = 8 ∧
      Coupled8 c V w base (Dictionary.dom s_dict').card s_post₁ s_post₂) := by
  dsimp only
  have hsch := hc67.1
  have hpad_fits₂ :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + dualPaddedWords c U V w (s₂.mem (base + hdrNSrc))
        (if s₂.mem (base + hdrPhase) = 0 then s₂.mem (base + hdrNSrc)
         else s₂.mem (base + hdrNDst)) (Dictionary.dom s_dict').card < 2 ^ w := by
    dsimp only at hpad_fits' ⊢
    rwa [← hsch.2 hdrNSrc (by decide) (by decide),
      ← hsch.2 hdrPhase (by decide) (by decide),
      ← hsch.2 hdrNDst (by decide) (by decide)]
  obtain ⟨hkg_eq, hc67_mid⟩ :=
    coupled67_fg_step_aux h₁ h₂ hc67 hp67 hop_nz u v hv_eq rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmid₁, hpt₁, _, _⟩ :=
    stepOpProg_mutate_spec h₁ hop_nz u v hv_eq hsucc_fits' hpad_fits'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmid₂, hpt₂, _, _⟩ :=
    stepOpProg_mutate_spec h₂ hop_nz u v hv_eq hsucc_fits' hpad_fits₂
  dsimp only at hmid₁ hpt₁ hmid₂ hpt₂
  rw [← hkg_eq] at hc67_mid hmid₂ hpt₂
  obtain ⟨_, _, _, hpost_sch_ne5, _⟩ :=
    schedEq_mutate_step (v_val := v_val) h₁ h₂ hsch hop_nz u v hv_eq hsucc_fits' hpad_fits'
  have hne5 : s₁.mem (base + hdrPhase) ≠ 5 := by rcases hp67 with h | h <;> omega
  obtain ⟨hksh_eq, hsch_post⟩ := hpost_sch_ne5 hne5
  dsimp only at hksh_eq hsch_post
  rw [← hkg_eq] at hksh_eq hsch_post
  rw [← hksh_eq] at hsch_post
  have hsm₁_ph :=
    (fgStep_le7_aux h₁ u v hv_eq (fgSetup_of_dualStateInv h₁ hop_nz u v) rfl rfl rfl
      (by rcases hp67 with h | h <;> omega)).2.2.2.1 (base + hdrPhase)
      (by dsimp only [hdrPhase]; omega) (base_add_ne (by decide)) (base_add_ne (by decide))
  have hsm₂_ph := (hc67_mid.1.2 hdrPhase (by decide) (by decide)).symm.trans hsm₁_ph
  have hpt₁_br := hpt₁.2.2.2; rw [ite_eq_left (hsm₁_ph.symm ▸ hne5)] at hpt₁_br
  have hpt₂_br := hpt₂.2.2.2; rw [ite_eq_left (hsm₂_ph.symm ▸ hne5)] at hpt₂_br
  obtain ⟨_, _, _, hpre₁, _⟩ := hpt₁_br
  obtain ⟨_, _, _, hpre₂, _⟩ := hpt₂_br
  obtain ⟨_, _, _, _, _, _, _, _, h_post₁⟩ :=
    postRandShrinkProg_spec_pre (opTag := opTag) hop_nz hpre₁
  obtain ⟨_, _, _, _, _, _, _, _, h_post₂⟩ :=
    postRandShrinkProg_spec_pre (opTag := opTag) hop_nz hpre₂
  rw [← hksh_eq] at h_post₂
  have hfr_m₁ :=
    (fgStep_le7_aux h₁ u v hv_eq (fgSetup_of_dualStateInv h₁ hop_nz u v) rfl rfl rfl
      (by rcases hp67 with h | h <;> omega)).2.1
  have hp_s₂ : s₂.mem (base + hdrPhase) = s₁.mem (base + hdrPhase) :=
    (hsch.2 hdrPhase (by decide) (by decide)).symm
  have hfr_m₂ :=
    (fgStep_le7_aux h₂ u v hv_eq (fgSetup_of_dualStateInv h₂ hop_nz u v) rfl hkg_eq rfl
      (by rw [hp_s₂]; rcases hp67 with h | h <;> omega)).2.1
  exact coupled67_mutate_step_aux hop_nz (hsm₁_ph.symm ▸ hp67) hc67_mid hmid₁ hmid₂
    (by rw [(stepOpProg_eval _ _ _ _ _ _).1, ite_eq_right hop_nz, hfr_m₁])
    (by rw [(stepOpProg_eval _ _ _ _ _ _).1, ite_eq_right hop_nz, hfr_m₂])
    hpre₁ hpre₂ rfl rfl rfl rfl rfl hsch_post h_post₁ h_post₂

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
