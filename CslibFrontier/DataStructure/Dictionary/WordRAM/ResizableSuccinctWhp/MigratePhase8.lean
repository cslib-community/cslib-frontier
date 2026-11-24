/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.MigrateDrain
import Mathlib.Tactic.Ring

/-!
# Phase-`8` Draining Congruence (`MigratePhase8`)

This module completes the cross-seed congruence chain across Phase `8` (`migrate`) and the `8 → 9`
unpermutation transition of the deamortized worst-case WHP resizable succinct dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]):

1. **Background `migrateBatchProg` coupling (`migrateStepProg_coupled`,
   `migrateBatchProg_coupled`):** Proves that `epochPopAnyProg` pops the identical `(u, v)`
   sequence on all states coupled to an ancestor `s₁`, appending a single canonical
   `extra : List (EpochUpdate U V)` independent of `slotDst.seeds` while preserving
   `SlotStateCoupled` and fast-path `memoryCost` bounds.
2. **Foreground Phase-`8` coupling (`fg8_coupled_step_aux`):**
   Couples `prepGrowProg` + `grow` + `userMutateProg` across any two `Coupled8` states sharing
   `slotSrc`.
3. **Full Phase-`8` mutation step (`coupled8_mutate_step`):**
   Delivers simultaneous `extra`-independence, `DualStateInv`, fast-path `memoryCost` bounds, and
   `8 → 8` `Coupled8` / `8 → 9` `SchedEq` across all destination seed fibers.

## Main results

* `Coupled8.refl`: reflexivity of `Coupled8` on any resting `DualStateInv` state at Phase `8`.
* `coupled8_mutate_step`: Phase-`8` mutation congruence (`8 → 8` `Coupled8` and `8 → 9` `SchedEq`
  with seed-independent `slotDst.evs`).

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

/-! ## Section 1: Reflexivity and Partner-Side `SlotStateCoupled` Preservation -/

/-- Reflexivity of `Coupled8` on any resting `DualStateInv` state in Phase `8`. -/
theorem Coupled8.refl {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (hp8 : s.mem (base + hdrPhase) = 8) :
    Coupled8 c V w base (Dictionary.dom s_dict).card s s := by
  obtain ⟨hcap_s, _, _, _, _, hsl_s, _, _, _⟩ := h.sl_8 hp8
  have hraw := hsl_s; unfold EpochSlotInv at hraw
  refine ⟨SchedEq.refl base s,
    { fr_eq := rfl
      side_zero := rfl
      valid₁ := by
        have hv := hsl_s.io_valid
        have hw_pg : (pagedSlotIo 0
          (dualPgHost c V w base (Dictionary.dom s_dict).card s.mem)).pgL.w = w := rfl
        rwa [hw_pg]
      disj := fun addr hreg => by
        rcases hreg with ⟨h1, h2⟩ | hmeta
        · by_cases hc0 : L.slotSrc.nCap = 0
          · rw [ite_eq_left hc0] at hraw
            exact fun hia => hraw.2.2.2.2.1 addr h1 h2 (Or.inr (Or.inr hia))
          · rw [ite_eq_right hc0] at hraw; exact hraw.1.disj_pBase_io addr h1 h2
        · rw [← hcap_s] at hmeta; unfold slotOwnsNonPageMeta at hmeta
          by_cases hc0 : L.slotSrc.nCap = 0
          · rw [ite_eq_left hc0] at hraw hmeta
            rcases hmeta with ⟨g1, g2⟩ | ⟨hne, _⟩
            · exact hraw.2.2.1.disjoint_hdr addr (by dsimp only; clear *- g1 g2; omega)
            · exact absurd hc0 hne
          · rw [ite_eq_right hc0] at hraw hmeta
            exact hraw.1.disj_fast_io addr (hmeta.imp id And.right)
      mem_eq := fun _ _ => rfl
      inv₁ := hsl_s.io_stateInv
      inv₂ := hsl_s.io_stateInv
      pair_eq := fun _ _ => rfl }⟩

/-- Preserves `SlotStateCoupled M (pagedSlotIo 0 pgHost)` across a mutation executed on the partner
destination slot (`pagedSlotIo 1 pgHost`). -/
private theorem partner_dst_coupled {M : ℕ → Prop} {c U V w pSrc mbSrc : ℕ}
    {pgHost : PageArenaLayout} {slSrc' : SlotLatent c U V}
    {s₁ s₂ s₁' s₂' : Memory.State}
    (hc : SlotStateCoupled M (pagedSlotIo 0 pgHost) (s₁.mem (mbSrc + 1)) s₁ s₂)
    (hs₁' : EpochSlotInv c U V w s₁'.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc'
      s₁'.mem)
    (hs₂' : EpochSlotInv c U V w s₂'.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc'
      s₂'.mem)
    (hfr₁ : s₁'.frontier = s₁.frontier)
    (hfr₂ : s₂'.frontier = s₂.frontier)
    (hm₁ : ∀ addr, M addr → s₁'.mem addr = s₁.mem addr)
    (hm₂ : ∀ addr, M addr → s₂'.mem addr = s₂.mem addr)
    (hvl_pres₁ : (extractPagePair pgHost s₁'.mem).virtLen false =
      (extractPagePair pgHost s₁.mem).virtLen false)
    (hp₁ : ∀ idx < (extractPagePair pgHost s₁.mem).virtLen false,
      slotIoPairAt (pagedSlotIo 0 pgHost) s₁'.mem idx =
        slotIoPairAt (pagedSlotIo 0 pgHost) s₁.mem idx)
    (hp₂ : ∀ idx < (extractPagePair pgHost s₂.mem).virtLen false,
      slotIoPairAt (pagedSlotIo 0 pgHost) s₂'.mem idx =
        slotIoPairAt (pagedSlotIo 0 pgHost) s₂.mem idx) :
    SlotStateCoupled M (pagedSlotIo 0 pgHost) (s₁'.mem (mbSrc + 1)) s₁' s₂' := by
  have hup0 : (pagedSlotIo 0 pgHost).usePaged ≠ 0 := Nat.one_ne_zero
  have hi₁ := hc.inv₁; have hi₂ := hc.inv₂; have hi₁' := hs₁'.io_stateInv
  unfold SlotIoLayout.StateInv at hi₁ hi₂ hi₁'
  rw [ite_eq_right hup0] at hi₁ hi₂ hi₁'
  have hvl₁ : (extractPagePair pgHost s₁.mem).virtLen false = s₁.mem (mbSrc + 1) := hi₁.2.2.2.2.1
  have hvl₂ : (extractPagePair pgHost s₂.mem).virtLen false = s₁.mem (mbSrc + 1) := hi₂.2.2.2.2.1
  have hvl₁' : (extractPagePair pgHost s₁'.mem).virtLen false = s₁'.mem (mbSrc + 1) :=
    hi₁'.2.2.2.2.1
  have hns_eq' : s₂'.mem (mbSrc + 1) = s₁'.mem (mbSrc + 1) :=
    hs₂'.mem_nSide_eq.trans hs₁'.mem_nSide_eq.symm
  have hns_pres : s₁'.mem (mbSrc + 1) = s₁.mem (mbSrc + 1) :=
    hvl₁'.symm.trans (hvl_pres₁.trans hvl₁)
  exact
    { fr_eq := hfr₁.trans (hc.fr_eq.trans hfr₂.symm)
      side_zero := rfl
      valid₁ := hfr₁ ▸ hc.valid₁
      disj := hc.disj
      mem_eq := fun addr ha => (hm₁ addr ha).trans ((hc.mem_eq addr ha).trans (hm₂ addr ha).symm)
      inv₁ := hs₁'.io_stateInv
      inv₂ := hns_eq' ▸ hs₂'.io_stateInv
      pair_eq := fun idx hidx => by
        have hidx₀ : idx < s₁.mem (mbSrc + 1) := hns_pres ▸ hidx
        exact (hp₁ idx (hvl₁.symm ▸ hidx₀)).trans
          ((hc.pair_eq idx hidx₀).trans (hp₂ idx (hvl₂.symm ▸ hidx₀)).symm) }

/-! ## Section 2: Coupled `migrateStepProg` and `migrateBatchProg` Specifications -/

/-- Coupled single-step specification of `migrateStepProg`: produces a canonical `(s_src', s_dst',
extra)` determined by `s₁` alone and proves that every coupled state `s₂` transitions to the
identical `(s_src', s_dst', extra)` while preserving `SlotStateCoupled` and fast-path cost. -/
private theorem migrateStepProg_coupled {c U V w pSrc mbSrc pDst mbDst moved : ℕ}
    {pgHost : PageArenaLayout} {slSrc slDst₁ : SlotLatent c U V} {s₁ : Memory.State}
    (hs₁ : EpochSlotInv c U V w s₁.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc s₁.mem)
    (hd₁ : EpochSlotInv c U V w s₁.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false slDst₁
      s₁.mem)
    (hdj : DisjointOpt slDst₁.s_abs slSrc.s_abs)
    (_hp_disj : pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc)
    (hpm_s : pDst + 64 ≤ mbSrc ∨
      mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ pDst)
    (hpm_d : pSrc + 64 ≤ mbDst ∨
      mbDst + (if slDst₁.nCap = 0 then 2 else offPageDir c w slDst₁.nCap) ≤ pSrc)
    (hmm_disj :
      mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ mbDst ∨
      mbDst + (if slDst₁.nCap = 0 then 2 else offPageDir c w slDst₁.nCap) ≤ mbSrc)
    (hcap_d : slDst₁.nCap ≠ 0 →
      (liveDom slDst₁.s_abs).card + (liveDom slSrc.s_abs).card ≤ slDst₁.nCap)
    (hcap_pg : (liveDom slDst₁.s_abs).card + (liveDom slSrc.s_abs).card ≤ pgHost.nCap) :
    let s₁' := (Memory.spec 0).clientState s₁ (migrateStepProg ((pSrc, pDst), moved))
    ∃ (s_src' s_dst' : Fin U → Option (Fin V)) (extra : List (EpochUpdate U V)),
      (liveDom s_src').card = (liveDom slSrc.s_abs).card - 1 ∧
      (slDst₁.evs ++ extra).length + (liveDom s_src').card =
        slDst₁.evs.length + (liveDom slSrc.s_abs).card ∧
      DisjointOpt s_dst' s_src' ∧
      orOpt s_dst' s_src' = orOpt slDst₁.s_abs slSrc.s_abs ∧
      EpochSlotInv c U V w s₁'.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
        ⟨slSrc.nCap, s_src', slSrc.seeds, slSrc.evs⟩ s₁'.mem ∧
      EpochSlotInv c U V w s₁'.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        ⟨slDst₁.nCap, s_dst', slDst₁.seeds, slDst₁.evs ++ extra⟩ s₁'.mem ∧
      (Memory.spec 0).clientResult s₁ (migrateStepProg ((pSrc, pDst), moved)) = 0 ∧
      s₁'.frontier = s₁.frontier ∧
      ∀ {slDst₂ : SlotLatent c U V} {s₂ : Memory.State} {M : ℕ → Prop},
        slDst₂.nCap = slDst₁.nCap →
        slDst₂.s_abs = slDst₁.s_abs →
        EpochSlotInv c U V w s₂.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc s₂.mem →
        EpochSlotInv c U V w s₂.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false slDst₂
          s₂.mem →
        (∀ addr, SlotSrcMetaRegion c w pSrc mbSrc slSrc.nCap addr → M addr) →
        (∀ addr, M addr → ¬slotOwnsAddr c w mbDst slDst₁.nCap (pagedSlotIo 1 pgHost) addr) →
        SlotStateCoupled M (pagedSlotIo 0 pgHost) (s₁.mem (mbSrc + 1)) s₁ s₂ →
        let s₂' := (Memory.spec 0).clientState s₂ (migrateStepProg ((pSrc, pDst), moved))
        MigrateStepPre w ((pSrc, pDst), moved) s₂ ∧
        (Memory.spec 0).clientResult s₂ (migrateStepProg ((pSrc, pDst), moved)) = 0 ∧
        s₂'.frontier = s₂.frontier ∧
        EpochSlotInv c U V w s₂'.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
          ⟨slSrc.nCap, s_src', slSrc.seeds, slSrc.evs⟩ s₂'.mem ∧
        EpochSlotInv c U V w s₂'.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
          ⟨slDst₂.nCap, s_dst', slDst₂.seeds, slDst₂.evs ++ extra⟩ s₂'.mem ∧
        SlotStateCoupled M (pagedSlotIo 0 pgHost) (s₁'.mem (mbSrc + 1)) s₁' s₂' ∧
        (∀ addr,
          ¬slotOwnsAddr c w mbSrc slSrc.nCap (pagedSlotIo 0 pgHost) addr →
          ¬slotOwnsAddr c w mbDst slDst₂.nCap (pagedSlotIo 1 pgHost) addr →
          s₂'.mem addr = s₂.mem addr) ∧
        ((slDst₂.nCap = 0 →
            (liveDom slDst₂.s_abs).card + (liveDom slSrc.s_abs).card ≤ 2 * whpThreshold c) →
          slSrc.GoodCovers →
          (⟨slDst₂.nCap, s_dst', slDst₂.seeds, slDst₂.evs ++ extra⟩ :
            SlotLatent c U V).GoodCovers →
          memoryCost (migrateStepProg ((pSrc, pDst), moved)) s₂ ≤ 2 * epochStepCost c + 2) := by
  dsimp only
  have hup0 : (pagedSlotIo 0 pgHost).usePaged ≠ 0 := Nat.one_ne_zero
  have hup1 : (pagedSlotIo 1 pgHost).usePaged ≠ 0 := Nat.one_ne_zero
  obtain ⟨hres_ev₁, hst_ev₁, _⟩ := migrateStepProg_eval pSrc pDst moved s₁
  dsimp only at hres_ev₁ hst_ev₁
  by_cases hpos : 0 < (liveDom slSrc.s_abs).card
  · have hnS₁_pos : 0 < (Memory.spec 0).clientResult s₁ (epochReadNSideProg pSrc) :=
      hs₁.readNSide_eq.symm ▸ hpos
    obtain ⟨u₁, v₁, hqv₁, hsu₁, hfr_p₁, hs_p₁_raw, hout_p₁, hpg_p₁, _⟩ := hs₁.popAny_spec hpos
    set s_pop₁ := (Memory.spec 0).clientState s₁ (epochPopAnyProg pSrc)
    have hcp0_₁ := cleanPhase_zero_of_paged0 hs₁
    have hslk0_s₁ : (if (pagedSlotIo 0 pgHost).usePaged = 0 ∨
        (extractPageUnperm (pagedSlotIo 0 pgHost).pgL s₁.mem).cleanPhase = 0
        then 0 else 24) = 0 := ite_eq_left (Or.inr hcp0_₁)
    have hs_pop₁ : EpochSlotInv c U V w s_pop₁.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
        ⟨slSrc.nCap, Function.update slSrc.s_abs u₁ none, slSrc.seeds, slSrc.evs⟩ s_pop₁.mem := by
      simpa only [hslk0_s₁] using hs_p₁_raw
    have hcp_pop₁ := cleanPhase_zero_of_paged0 hs_pop₁
    obtain ⟨hno_s_pDst₁, hno_s_mDst₁⟩ :=
      not_paged_slotOwnsAddr_partner (sbA := 0) (slA := slSrc) hd₁ hpm_s hmm_disj
    obtain ⟨hno_d_pSrc₁, hno_d_mSrc₁⟩ :=
      not_paged_slotOwnsAddr_partner (sbA := 1) (slA := slDst₁) hs₁ hpm_d hmm_disj.symm
    have hd_pop₁ : EpochSlotInv c U V w s_pop₁.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        slDst₁ s_pop₁.mem :=
      (hfr_p₁ ▸ hd₁).partner_paged_frame hs_pop₁.io_stateInv hcp_pop₁
        (fun a h1 h2 => hout_p₁ a (hno_s_pDst₁ a h1 h2))
        (fun a ha => hout_p₁ a (hno_s_mDst₁ a ha))
        (hpg_p₁ hup0).1 (hpg_p₁ hup0).2.2
    obtain ⟨_, hor_eq, hdj'⟩ := orOpt_migrate_pop_insert hdj hsu₁
    have hsrc_card_pop :
        (liveDom (Function.update slSrc.s_abs u₁ none)).card =
          (liveDom slSrc.s_abs).card - 1 := by
      rw [liveDom_delete_card, ite_eq_right (by rw [hsu₁]; exact Option.some_ne_none v₁)]
    have hti_pop₁ : (extractPagePair pgHost s_pop₁.mem).totalItems =
        (liveDom (Function.update slSrc.s_abs u₁ none)).card + (liveDom slDst₁.s_abs).card := by
      have hi0 := hs_pop₁.io_stateInv; have hi1 := hd_pop₁.io_stateInv
      unfold SlotIoLayout.StateInv at hi0 hi1
      rw [ite_eq_right hup0] at hi0; rw [ite_eq_right hup1] at hi1
      have hvl0 : (extractPagePair pgHost s_pop₁.mem).virtLen false =
        s_pop₁.mem (mbSrc + 1) := hi0.2.2.2.2.1
      have hvl1 : (extractPagePair pgHost s_pop₁.mem).virtLen true =
        s_pop₁.mem (mbDst + 1) := hi1.2.2.2.2.1
      have hns0 := hs_pop₁.mem_nSide_eq; have hns1 := hd_pop₁.mem_nSide_eq
      dsimp only at hns0
      unfold PagePairState.totalItems
      rw [hvl0, hvl1, hns0, hns1]
    have hcap_n_d₁ : slDst₁.s_abs u₁ = none → slDst₁.nCap ≠ 0 →
        (liveDom slDst₁.s_abs).card < slDst₁.nCap := fun _ hne_d => by
      have := hcap_d hne_d; clear *- hpos this; omega
    have hcap_io_d₁ : slDst₁.s_abs u₁ = none →
        (liveDom slDst₁.s_abs).card < (pagedSlotIo 1 pgHost).pgL.nCap ∧
        ((pagedSlotIo 1 pgHost).usePaged ≠ 0 →
          (extractPagePair (pagedSlotIo 1 pgHost).pgL s_pop₁.mem).totalItems + 1 ≤
            (pagedSlotIo 1 pgHost).pgL.nCap) := fun _ => by
      dsimp only [pagedSlotIo]; rw [hti_pop₁, hsrc_card_pop]
      exact ⟨by clear *- hpos hcap_pg; omega, fun _ => by clear *- hpos hcap_pg; omega⟩
    have hsp_ins₁ := hd_pop₁.insert_spec u₁ v₁ hcap_n_d₁ hcap_io_d₁
    dsimp only at hsp_ins₁
    set s_ins₁ := (Memory.spec 0).clientState s_pop₁ (epochInsertProg ((pDst, u₁.val), v₁.val))
    have hslk0_d₁ : (if (pagedSlotIo 1 pgHost).usePaged = 0 ∨
        (extractPageUnperm (pagedSlotIo 1 pgHost).pgL s_pop₁.mem).cleanPhase = 0
        then 0 else 24) = 0 := ite_eq_left (Or.inr hcp_pop₁)
    have hd_ins₁ : EpochSlotInv c U V w s_ins₁.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        ⟨slDst₁.nCap, Function.update slDst₁.s_abs u₁ (some v₁), slDst₁.seeds,
          slDst₁.evs ++ [EpochUpdate.insert u₁ v₁]⟩ s_ins₁.mem := by
      simpa only [hslk0_d₁] using hsp_ins₁.2.1
    have hcp_ins₁ : (extractPageUnperm pgHost s_ins₁.mem).cleanPhase = 0 :=
      (hd_pop₁.insert_paged_unperm hup1 u₁ v₁ hcap_n_d₁
        (fun hnone => ⟨(hcap_io_d₁ hnone).1, (hcap_io_d₁ hnone).2 hup1⟩)).1 hcp_pop₁
    have hs_ins₁ : EpochSlotInv c U V w s_ins₁.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
        ⟨slSrc.nCap, Function.update slSrc.s_abs u₁ none, slSrc.seeds, slSrc.evs⟩ s_ins₁.mem :=
      (hsp_ins₁.1 ▸ hs_pop₁).partner_paged_frame hd_ins₁.io_stateInv hcp_ins₁
        (fun a h1 h2 => hsp_ins₁.2.2.1 a (hno_d_pSrc₁ a h1 h2))
        (fun a ha => hsp_ins₁.2.2.1 a (hno_d_mSrc₁ a ha))
        (hsp_ins₁.2.2.2.2.1 hup1).1 (hsp_ins₁.2.2.2.2.1 hup1).2
    have hst₁_eq :
        (Memory.spec 0).clientState s₁ (migrateStepProg ((pSrc, pDst), moved)) = s_ins₁ := by
      rw [hst_ev₁, ite_eq_left hnS₁_pos, hqv₁]
    refine ⟨Function.update slSrc.s_abs u₁ none, Function.update slDst₁.s_abs u₁ (some v₁),
      [EpochUpdate.insert u₁ v₁], hsrc_card_pop,
      by rw [List.length_append, List.length_singleton, hsrc_card_pop]; omega,
      hdj', hor_eq, hst₁_eq ▸ hs_ins₁, hst₁_eq ▸ hd_ins₁, hres_ev₁,
      hst₁_eq ▸ hsp_ins₁.1.trans hfr_p₁, ?_⟩
    intro slDst₂ s₂ M hnc₂ habs₂ hs₂ hd₂ hsub_src hdisj_dst hc
    obtain ⟨hres_ev₂, hst_ev₂, hmc_ev₂⟩ := migrateStepProg_eval pSrc pDst moved s₂
    dsimp only at hres_ev₂ hst_ev₂ hmc_ev₂
    have hnS₂_pos : 0 < (Memory.spec 0).clientResult s₂ (epochReadNSideProg pSrc) :=
      hs₂.readNSide_eq.symm ▸ hpos
    have hcs_pop := epochPopAny_src_coupled hs₁ hpos hsub_src hc
    obtain ⟨u₂, v₂, hqv₂, _, hfr_p₂, hs_p₂_raw, hout_p₂, hpg_p₂, hmc_p₂⟩ := hs₂.popAny_spec hpos
    have hqv_pair : (u₂.val, v₂.val) = (u₁.val, v₁.val) :=
      hqv₂.symm.trans (hcs_pop.res_eq.symm.trans hqv₁)
    have hu_eq : u₂ = u₁ := Fin.ext (Prod.mk.inj hqv_pair).1
    have hv_eq2 : v₂ = v₁ := Fin.ext (Prod.mk.inj hqv_pair).2
    subst u₂; subst v₂
    set s_pop₂ := (Memory.spec 0).clientState s₂ (epochPopAnyProg pSrc)
    have hcp0_₂ := cleanPhase_zero_of_paged0 hs₂
    have hslk0_s₂ : (if (pagedSlotIo 0 pgHost).usePaged = 0 ∨
        (extractPageUnperm (pagedSlotIo 0 pgHost).pgL s₂.mem).cleanPhase = 0
        then 0 else 24) = 0 := ite_eq_left (Or.inr hcp0_₂)
    have hs_pop₂ : EpochSlotInv c U V w s_pop₂.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
        ⟨slSrc.nCap, Function.update slSrc.s_abs u₁ none, slSrc.seeds, slSrc.evs⟩ s_pop₂.mem := by
      simpa only [hslk0_s₂] using hs_p₂_raw
    have hcp_pop₂ := cleanPhase_zero_of_paged0 hs_pop₂
    have hpm_d₂ : pSrc + 64 ≤ mbDst ∨
        mbDst + (if slDst₂.nCap = 0 then 2 else offPageDir c w slDst₂.nCap) ≤ pSrc :=
      hnc₂ ▸ hpm_d
    have hmm_disj₂ :
        mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ mbDst ∨
        mbDst + (if slDst₂.nCap = 0 then 2 else offPageDir c w slDst₂.nCap) ≤ mbSrc :=
      hnc₂ ▸ hmm_disj
    obtain ⟨hno_s_pDst₂, hno_s_mDst₂⟩ :=
      not_paged_slotOwnsAddr_partner (sbA := 0) (slA := slSrc) hd₂ hpm_s hmm_disj₂
    obtain ⟨hno_d_pSrc₂, hno_d_mSrc₂⟩ :=
      not_paged_slotOwnsAddr_partner (sbA := 1) (slA := slDst₂) hs₂ hpm_d₂ hmm_disj₂.symm
    have hd_pop₂ : EpochSlotInv c U V w s_pop₂.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        slDst₂ s_pop₂.mem :=
      (hfr_p₂ ▸ hd₂).partner_paged_frame hs_pop₂.io_stateInv hcp_pop₂
        (fun a h1 h2 => hout_p₂ a (hno_s_pDst₂ a h1 h2))
        (fun a ha => hout_p₂ a (hno_s_mDst₂ a ha))
        (hpg_p₂ hup0).1 (hpg_p₂ hup0).2.2
    have hpre_step₂ : MigrateStepPre w ((pSrc, pDst), moved) s₂ :=
      ⟨hs₂.epochProgPre, fun _ => hd_pop₂.epochInsertProgPre⟩
    have hti_pop₂ : (extractPagePair pgHost s_pop₂.mem).totalItems =
        (liveDom (Function.update slSrc.s_abs u₁ none)).card + (liveDom slDst₁.s_abs).card := by
      have hi0 := hs_pop₂.io_stateInv; have hi1 := hd_pop₂.io_stateInv
      unfold SlotIoLayout.StateInv at hi0 hi1
      rw [ite_eq_right hup0] at hi0; rw [ite_eq_right hup1] at hi1
      have hvl0 : (extractPagePair pgHost s_pop₂.mem).virtLen false =
        s_pop₂.mem (mbSrc + 1) := hi0.2.2.2.2.1
      have hvl1 : (extractPagePair pgHost s_pop₂.mem).virtLen true =
        s_pop₂.mem (mbDst + 1) := hi1.2.2.2.2.1
      have hns0 := hs_pop₂.mem_nSide_eq; have hns1 := hd_pop₂.mem_nSide_eq
      dsimp only at hns0
      unfold PagePairState.totalItems
      rw [hvl0, hvl1, hns0, hns1, habs₂]
    have hcap_n_d₂ : slDst₂.s_abs u₁ = none → slDst₂.nCap ≠ 0 →
        (liveDom slDst₂.s_abs).card < slDst₂.nCap := fun hnone hne_d => by
      rw [habs₂, hnc₂]; exact hcap_n_d₁ (habs₂ ▸ hnone) (hnc₂ ▸ hne_d)
    have hcap_io_d₂ : slDst₂.s_abs u₁ = none →
        (liveDom slDst₂.s_abs).card < (pagedSlotIo 1 pgHost).pgL.nCap ∧
        ((pagedSlotIo 1 pgHost).usePaged ≠ 0 →
          (extractPagePair (pagedSlotIo 1 pgHost).pgL s_pop₂.mem).totalItems + 1 ≤
            (pagedSlotIo 1 pgHost).pgL.nCap) := fun _ => by
      dsimp only [pagedSlotIo]; rw [habs₂, hti_pop₂, hsrc_card_pop]
      exact ⟨by clear *- hpos hcap_pg; omega, fun _ => by clear *- hpos hcap_pg; omega⟩
    have hsp_ins₂ := hd_pop₂.insert_spec u₁ v₁ hcap_n_d₂ hcap_io_d₂
    dsimp only at hsp_ins₂
    set s_ins₂ := (Memory.spec 0).clientState s_pop₂ (epochInsertProg ((pDst, u₁.val), v₁.val))
    have hslk0_d₂ : (if (pagedSlotIo 1 pgHost).usePaged = 0 ∨
        (extractPageUnperm (pagedSlotIo 1 pgHost).pgL s_pop₂.mem).cleanPhase = 0
        then 0 else 24) = 0 := ite_eq_left (Or.inr hcp_pop₂)
    have hd_ins₂ : EpochSlotInv c U V w s_ins₂.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        ⟨slDst₂.nCap, Function.update slDst₁.s_abs u₁ (some v₁), slDst₂.seeds,
          slDst₂.evs ++ [EpochUpdate.insert u₁ v₁]⟩ s_ins₂.mem := by
      rw [← habs₂]; simpa only [hslk0_d₂] using hsp_ins₂.2.1
    have hcp_ins₂ : (extractPageUnperm pgHost s_ins₂.mem).cleanPhase = 0 :=
      (hd_pop₂.insert_paged_unperm hup1 u₁ v₁ hcap_n_d₂
        (fun hnone => ⟨(hcap_io_d₂ hnone).1, (hcap_io_d₂ hnone).2 hup1⟩)).1 hcp_pop₂
    have hs_ins₂ : EpochSlotInv c U V w s_ins₂.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
        ⟨slSrc.nCap, Function.update slSrc.s_abs u₁ none, slSrc.seeds, slSrc.evs⟩ s_ins₂.mem :=
      (hsp_ins₂.1 ▸ hs_pop₂).partner_paged_frame hd_ins₂.io_stateInv hcp_ins₂
        (fun a h1 h2 => hsp_ins₂.2.2.1 a (hno_d_pSrc₂ a h1 h2))
        (fun a ha => hsp_ins₂.2.2.1 a (hno_d_mSrc₂ a ha))
        (hsp_ins₂.2.2.2.2.1 hup1).1 (hsp_ins₂.2.2.2.2.1 hup1).2
    have hst₂_eq :
        (Memory.spec 0).clientState s₂ (migrateStepProg ((pSrc, pDst), moved)) = s_ins₂ := by
      rw [hst_ev₂, ite_eq_left hnS₂_pos, hqv₂]
    have hns_pop₁ : s_pop₁.mem (mbSrc + 1) = s₁.mem (mbSrc + 1) - 1 := by
      have h1 := hs_pop₁.mem_nSide_eq; dsimp only at h1
      rw [h1, hsrc_card_pop, hs₁.mem_nSide_eq]
    have hc_pop : SlotStateCoupled M (pagedSlotIo 0 pgHost) (s_pop₁.mem (mbSrc + 1))
        s_pop₁ s_pop₂ := hcs_pop.coupled.cast_n hns_pop₁.symm
    have hc_ins : SlotStateCoupled M (pagedSlotIo 0 pgHost) (s_ins₁.mem (mbSrc + 1))
        s_ins₁ s_ins₂ :=
      partner_dst_coupled hc_pop hs_ins₁ hs_ins₂ hsp_ins₁.1 hsp_ins₂.1
        (fun addr hm => hsp_ins₁.2.2.1 addr (hdisj_dst addr hm))
        (fun addr hm => hsp_ins₂.2.2.1 addr (hnc₂ ▸ hdisj_dst addr hm))
        (hsp_ins₁.2.2.2.2.1 hup1).1 (hsp_ins₁.2.2.2.2.1 hup1).2 (hsp_ins₂.2.2.2.2.1 hup1).2
    rw [hst₁_eq, hst₂_eq]
    refine ⟨hpre_step₂, hres_ev₂, hsp_ins₂.1.trans hfr_p₂, hs_ins₂, hd_ins₂, hc_ins,
      fun addr hns hnd => (hsp_ins₂.2.2.1 addr hnd).trans (hout_p₂ addr hns),
      fun hd_sm hgc_s hgc_d => ?_⟩
    rw [hmc_ev₂, ite_eq_left hnS₂_pos, hqv₂]
    dsimp only [s_pop₂] at *
    have hc1 := hmc_p₂ hgc_s
    have hc2 := hsp_ins₂.2.2.2.2.2
      (fun h0 => le_trans (Nat.le_add_right _ _) (hd_sm h0))
      (by rw [habs₂]; exact hgc_d)
    clear *- hc1 hc2; omega
  · have hnS₁_np : ¬(0 < (Memory.spec 0).clientResult s₁ (epochReadNSideProg pSrc)) :=
      hs₁.readNSide_eq.symm ▸ hpos
    have hc0 : (liveDom slSrc.s_abs).card = 0 := Nat.eq_zero_of_not_pos hpos
    have hst₁_eq : (Memory.spec 0).clientState s₁ (migrateStepProg ((pSrc, pDst), moved)) = s₁ := by
      rw [hst_ev₁, ite_eq_right hnS₁_np]
    have hsl_s_eq : (⟨slSrc.nCap, slSrc.s_abs, slSrc.seeds, slSrc.evs⟩ : SlotLatent c U V) =
        slSrc := by cases slSrc; rfl
    have hsl_d₁_eq : (⟨slDst₁.nCap, slDst₁.s_abs, slDst₁.seeds, slDst₁.evs ++ []⟩ :
        SlotLatent c U V) = slDst₁ := by cases slDst₁; simp
    refine ⟨slSrc.s_abs, slDst₁.s_abs, [], by rw [hc0], by simp, hdj, rfl,
      by rw [hst₁_eq, hsl_s_eq]; exact hs₁,
      by rw [hst₁_eq, hsl_d₁_eq]; exact hd₁,
      hres_ev₁, by rw [hst₁_eq], ?_⟩
    intro slDst₂ s₂ M _ habs₂ hs₂ hd₂ _ _ hc
    obtain ⟨hres_ev₂, hst_ev₂, hmc_ev₂⟩ := migrateStepProg_eval pSrc pDst moved s₂
    dsimp only at hres_ev₂ hst_ev₂ hmc_ev₂
    have hnS₂_np : ¬(0 < (Memory.spec 0).clientResult s₂ (epochReadNSideProg pSrc)) :=
      hs₂.readNSide_eq.symm ▸ hpos
    have hpre_step₂ : MigrateStepPre w ((pSrc, pDst), moved) s₂ :=
      ⟨hs₂.epochProgPre, fun hp => absurd hp hnS₂_np⟩
    have hsl_d₂_eq : (⟨slDst₂.nCap, slDst₁.s_abs, slDst₂.seeds, slDst₂.evs ++ []⟩ :
        SlotLatent c U V) = slDst₂ := by rw [← habs₂]; cases slDst₂; simp
    rw [hst₁_eq, hst_ev₂, ite_eq_right hnS₂_np]
    refine ⟨hpre_step₂, hres_ev₂, rfl,
      by rw [hsl_s_eq]; exact hs₂,
      by rw [hsl_d₂_eq]; exact hd₂,
      hc, fun _ _ _ => rfl, fun _ _ _ => ?_⟩
    rw [hmc_ev₂, ite_eq_right hnS₂_np]; omega

/-- Coupled `fuel`-step specification of `migrateBatchProg`: appends the identical `extra` list
across all coupled states `s₂`, preserving `SlotStateCoupled`, `EpochSlotInv`, and fast-path
`memoryCost` bounds. -/
private theorem migrateBatchProg_coupled {c U V w pSrc mbSrc pDst mbDst moved : ℕ}
    {pgHost : PageArenaLayout} {slSrc slDst₁ : SlotLatent c U V} {s₁ : Memory.State}
    (hs₁ : EpochSlotInv c U V w s₁.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc s₁.mem)
    (hd₁ : EpochSlotInv c U V w s₁.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false slDst₁
      s₁.mem)
    (hdj : DisjointOpt slDst₁.s_abs slSrc.s_abs)
    (hp_disj : pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc)
    (hpm_s : pDst + 64 ≤ mbSrc ∨
      mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ pDst)
    (hpm_d : pSrc + 64 ≤ mbDst ∨
      mbDst + (if slDst₁.nCap = 0 then 2 else offPageDir c w slDst₁.nCap) ≤ pSrc)
    (hmm_disj :
      mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ mbDst ∨
      mbDst + (if slDst₁.nCap = 0 then 2 else offPageDir c w slDst₁.nCap) ≤ mbSrc)
    (hcap_d : slDst₁.nCap ≠ 0 →
      (liveDom slDst₁.s_abs).card + (liveDom slSrc.s_abs).card ≤ slDst₁.nCap)
    (hcap_pg : (liveDom slDst₁.s_abs).card + (liveDom slSrc.s_abs).card ≤ pgHost.nCap)
    (fuel : ℕ) :
    let s₁' := (Memory.spec 0).clientState s₁ (migrateBatchProg (((pSrc, pDst), moved), fuel))
    ∃ (s_src' s_dst' : Fin U → Option (Fin V)) (extra : List (EpochUpdate U V)),
      (liveDom s_src').card = (liveDom slSrc.s_abs).card - fuel ∧
      (slDst₁.evs ++ extra).length + (liveDom s_src').card =
        slDst₁.evs.length + (liveDom slSrc.s_abs).card ∧
      DisjointOpt s_dst' s_src' ∧
      orOpt s_dst' s_src' = orOpt slDst₁.s_abs slSrc.s_abs ∧
      EpochSlotInv c U V w s₁'.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
        ⟨slSrc.nCap, s_src', slSrc.seeds, slSrc.evs⟩ s₁'.mem ∧
      EpochSlotInv c U V w s₁'.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        ⟨slDst₁.nCap, s_dst', slDst₁.seeds, slDst₁.evs ++ extra⟩ s₁'.mem ∧
      s₁'.frontier = s₁.frontier ∧
      ∀ {slDst₂ : SlotLatent c U V} {s₂ : Memory.State} {M : ℕ → Prop},
        slDst₂.nCap = slDst₁.nCap →
        slDst₂.s_abs = slDst₁.s_abs →
        EpochSlotInv c U V w s₂.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc s₂.mem →
        EpochSlotInv c U V w s₂.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false slDst₂
          s₂.mem →
        (∀ addr, SlotSrcMetaRegion c w pSrc mbSrc slSrc.nCap addr → M addr) →
        (∀ addr, M addr → ¬slotOwnsAddr c w mbDst slDst₁.nCap (pagedSlotIo 1 pgHost) addr) →
        SlotStateCoupled M (pagedSlotIo 0 pgHost) (s₁.mem (mbSrc + 1)) s₁ s₂ →
        let s₂' := (Memory.spec 0).clientState s₂ (migrateBatchProg (((pSrc, pDst), moved), fuel))
        iterationSafe migrateStepProg MigrateStepPre w (pSrc, pDst) fuel moved s₂ ∧
        s₂'.frontier = s₂.frontier ∧
        EpochSlotInv c U V w s₂'.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
          ⟨slSrc.nCap, s_src', slSrc.seeds, slSrc.evs⟩ s₂'.mem ∧
        EpochSlotInv c U V w s₂'.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
          ⟨slDst₂.nCap, s_dst', slDst₂.seeds, slDst₂.evs ++ extra⟩ s₂'.mem ∧
        SlotStateCoupled M (pagedSlotIo 0 pgHost) (s₁'.mem (mbSrc + 1)) s₁' s₂' ∧
        (∀ addr,
          ¬slotOwnsAddr c w mbSrc slSrc.nCap (pagedSlotIo 0 pgHost) addr →
          ¬slotOwnsAddr c w mbDst slDst₂.nCap (pagedSlotIo 1 pgHost) addr →
          s₂'.mem addr = s₂.mem addr) ∧
        ((slDst₂.nCap = 0 →
            (liveDom slDst₂.s_abs).card + (liveDom slSrc.s_abs).card ≤ 2 * whpThreshold c) →
          slSrc.GoodCovers →
          (⟨slDst₂.nCap, s_dst', slDst₂.seeds, slDst₂.evs ++ extra⟩ :
            SlotLatent c U V).GoodCovers →
          memoryCost (migrateBatchProg (((pSrc, pDst), moved), fuel)) s₂ ≤
            fuel * (2 * epochStepCost c + 2)) := by
  dsimp only
  induction fuel generalizing s₁ moved slSrc slDst₁ with
  | zero =>
    obtain ⟨hst0_₁, _⟩ := migrateBatchProg_zero pSrc pDst moved s₁
    have hsl_s_eq : (⟨slSrc.nCap, slSrc.s_abs, slSrc.seeds, slSrc.evs⟩ : SlotLatent c U V) =
        slSrc := by cases slSrc; rfl
    have hsl_d₁_eq : (⟨slDst₁.nCap, slDst₁.s_abs, slDst₁.seeds, slDst₁.evs ++ []⟩ :
        SlotLatent c U V) = slDst₁ := by cases slDst₁; simp
    refine ⟨slSrc.s_abs, slDst₁.s_abs, [], Nat.sub_zero _, by simp, hdj, rfl,
      by rw [hst0_₁, hsl_s_eq]; exact hs₁,
      by rw [hst0_₁, hsl_d₁_eq]; exact hd₁,
      by rw [hst0_₁], ?_⟩
    intro slDst₂ s₂ M _ habs₂ hs₂ hd₂ _ _ hc
    obtain ⟨hst0_₂, hmc0_₂⟩ := migrateBatchProg_zero pSrc pDst moved s₂
    have hsl_d₂_eq : (⟨slDst₂.nCap, slDst₁.s_abs, slDst₂.seeds, slDst₂.evs ++ []⟩ :
        SlotLatent c U V) = slDst₂ := by rw [← habs₂]; cases slDst₂; simp
    rw [hst0_₁, hst0_₂]
    exact ⟨trivial, rfl,
      by rw [hsl_s_eq]; exact hs₂,
      by rw [hsl_d₂_eq]; exact hd₂,
      hc, fun _ _ _ => rfl,
      fun _ _ _ => by rw [hmc0_₂]; exact Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨s_src1, s_dst1, ex1, hcd1, hsum1, hdj1, hor1, hs1_₁, hd1_₁, hres1_₁, hfr1_₁,
      hstep_all⟩ :=
      migrateStepProg_coupled hs₁ hd₁ hdj hp_disj hpm_s hpm_d hmm_disj hcap_d hcap_pg
    set s1₁ := (Memory.spec 0).clientState s₁ (migrateStepProg ((pSrc, pDst), moved))
    set slSrc1 : SlotLatent c U V := ⟨slSrc.nCap, s_src1, slSrc.seeds, slSrc.evs⟩
    set slDst1₁ : SlotLatent c U V := ⟨slDst₁.nCap, s_dst1, slDst₁.seeds, slDst₁.evs ++ ex1⟩
    have hcard_tot_eq :
        (liveDom s_dst1).card + (liveDom s_src1).card =
          (liveDom slDst₁.s_abs).card + (liveDom slSrc.s_abs).card := by
      rw [← liveDom_orOpt_card hdj1, hor1, liveDom_orOpt_card hdj]
    obtain ⟨s_src2, s_dst2, ex2, hcd2, hsum2, hdj2, hor2, hs2_₁, hd2_₁, hfr2_₁, hih_all⟩ :=
      ih (s₁ := s1₁) (moved := 0) (slSrc := slSrc1) (slDst₁ := slDst1₁)
        hs1_₁ hd1_₁ hdj1 hpm_s hpm_d hmm_disj
        (fun hne => hcard_tot_eq ▸ hcap_d hne) (hcard_tot_eq ▸ hcap_pg)
    obtain ⟨hst_b₁, _⟩ := migrateBatchProg_succ pSrc pDst moved k s₁
    dsimp only at hst_b₁
    rw [hres1_₁] at hst_b₁
    have hevs_assoc₁ : (slDst₁.evs ++ ex1) ++ ex2 = slDst₁.evs ++ (ex1 ++ ex2) :=
      List.append_assoc _ _ _
    refine ⟨s_src2, s_dst2, ex1 ++ ex2,
      by rw [hcd2]; dsimp only [slSrc1]; rw [hcd1]; omega,
      by dsimp only [slDst1₁] at hsum2; rw [← hevs_assoc₁]; exact hsum2.trans hsum1,
      hdj2, hor2.trans hor1,
      by rw [hst_b₁]; exact hs2_₁,
      by rw [hst_b₁]; simpa only [slDst1₁, hevs_assoc₁] using hd2_₁,
      by rw [hst_b₁]; exact hfr2_₁.trans hfr1_₁, ?_⟩
    intro slDst₂ s₂ M hnc₂ habs₂ hs₂ hd₂ hsub_src hdisj_dst hc
    obtain ⟨hpre1_₂, hres1_₂, hfr1_₂, hs1_₂, hd1_₂, hc1, hout1_₂, hmc1_₂⟩ :=
      hstep_all hnc₂ habs₂ hs₂ hd₂ hsub_src hdisj_dst hc
    set s1₂ := (Memory.spec 0).clientState s₂ (migrateStepProg ((pSrc, pDst), moved))
    set slDst1₂ : SlotLatent c U V := ⟨slDst₂.nCap, s_dst1, slDst₂.seeds, slDst₂.evs ++ ex1⟩
    obtain ⟨hsafe2_₂, hfr2_₂, hs2_₂, hd2_₂, hc2, hout2_₂, hmc2_₂⟩ :=
      hih_all (slDst₂ := slDst1₂) (s₂ := s1₂) hnc₂ rfl hs1_₂ hd1_₂ hsub_src hdisj_dst hc1
    obtain ⟨hst_b₂, hmc_b₂⟩ := migrateBatchProg_succ pSrc pDst moved k s₂
    dsimp only at hst_b₂ hmc_b₂
    rw [hres1_₂] at hst_b₂ hmc_b₂
    have hsafe_tot₂ : iterationSafe migrateStepProg MigrateStepPre w (pSrc, pDst) (k + 1)
        moved s₂ := by
      unfold iterationSafe
      rw [clientResult_width, clientState_width, hres1_₂]
      exact ⟨hpre1_₂, hsafe2_₂⟩
    have hevs_assoc₂ : (slDst₂.evs ++ ex1) ++ ex2 = slDst₂.evs ++ (ex1 ++ ex2) :=
      List.append_assoc _ _ _
    rw [hst_b₁, hst_b₂]
    refine ⟨hsafe_tot₂, hfr2_₂.trans hfr1_₂, hs2_₂,
      by simpa only [slDst1₂, hevs_assoc₂] using hd2_₂, hc2,
      fun addr hns hnd => (hout2_₂ addr hns hnd).trans (hout1_₂ addr hns hnd),
      fun hd_sm hgc_s hgc_d2 => ?_⟩
    have hgc_d1 : slDst1₂.GoodCovers :=
      SlotLatent.GoodCovers.of_append (s₂ := s_dst2) (extra := ex2) (by
        simpa only [slDst1₂, hevs_assoc₂] using hgc_d2)
    have hc_step := hmc1_₂ hd_sm hgc_s hgc_d1
    have hc_rest :=
      hmc2_₂ (fun h0 => by rw [← habs₂] at hcard_tot_eq; exact hcard_tot_eq ▸ hd_sm h0)
        hgc_s (by simpa only [slDst1₂, hevs_assoc₂] using hgc_d2)
    rw [hmc_b₂]
    calc memoryCost (migrateStepProg ((pSrc, pDst), moved)) s₂ +
          memoryCost (migrateBatchProg (((pSrc, pDst), 0), k)) s1₂
        ≤ (2 * epochStepCost c + 2) + k * (2 * epochStepCost c + 2) :=
          Nat.add_le_add hc_step hc_rest
      _ = (k + 1) * (2 * epochStepCost c + 2) := by ring

/-! ## Section 3: Phase-`8` Foreground Coupling (`fg8_coupled_step_aux`) -/

private theorem fg8_coupled_step_aux {c U V w base opTag v_val k_grow₁ k_grow₂ : ℕ}
    {s_dict : Dictionary.State U} {L₁ L₂ : DualLatent c U V}
    {s₁ s₂ sp₁ sp₂ sr₁ sr₂ sm₁ sm₂ : Memory.State}
    (h₁ : DualStateInv c U V w base s_dict L₁ s₁)
    (h₂ : DualStateInv c U V w base s_dict L₂ s₂)
    (hc8 : Coupled8 c V w base (Dictionary.dom s_dict).card s₁ s₂)
    (hp8 : s₁.mem (base + hdrPhase) = 8)
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
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    k_grow₁ = k_grow₂ ∧
    Coupled8 c V w base (Dictionary.dom s_dict').card sm₁ sm₂ := by
  intro s_dict'
  have hsch := hc8.1
  have hp8_₂ : s₂.mem (base + hdrPhase) = 8 :=
    (hsch.2 hdrPhase (by decide) (by decide)).symm.trans hp8
  obtain ⟨hkg_eq0, hsch_g0, hsch_m0⟩ := schedEq_foreground h₁ h₂ hsch hop_nz u v hv_eq
  have hkg_eq : k_grow₁ = k_grow₂ := hkg₁.trans (hkg_eq0.trans hkg₂.symm)
  set sg₁ : Memory.State := { mem := sp₁.mem, frontier := s₁.frontier + k_grow₁ }
  set sg₂ : Memory.State := { mem := sp₂.mem, frontier := s₂.frontier + k_grow₂ }
  have hsch_mid : SchedEq base sm₁ sm₂ := by
    dsimp only [SchedEq] at hsch_m0 ⊢
    rw [← hsp₁, ← hkg₁, ← hsm₁] at hsch_m0
    rw [← hsp₂, ← hkg₂, ← hsm₂] at hsch_m0
    exact hsch_m0
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
  -- Lift `EpochSlotInv` to `sg₁` and `sg₂` using `FGSetup.lift_grow_slot`
  have hsetup₁ := fgSetup_of_dualStateInv h₁ hop_nz u v
  have hsetup₂ := fgSetup_of_dualStateInv h₂ hop_nz u v
  set nLive := (Dictionary.dom s_dict).card
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set pSrc := dualPSrc base s₁.mem
  set mbSrc := dualMbSrc base s₁.mem
  set pDst := dualPDst base s₁.mem
  set mbDst := dualMbDst base s₁.mem
  set pgH := dualPgHost c V w base nLive s₁.mem
  set pgH_al := hostPageLayout c w (dualNHost base s₁.mem) (dualMbHost base s₁.mem)
    (s₁.mem (base + hdrItemHi)) (s₁.mem (base + hdrQHi)) (valBits V) nAlloc
  have hpS_eq₂ : dualPSrc base s₂.mem = pSrc := by
    unfold dualPSrc pSrc; rw [← hsch.2 hdrStage (by decide) (by decide)]
  have hmbS_eq₂ : dualMbSrc base s₂.mem = mbSrc := by
    unfold dualMbSrc mbSrc
    rw [← hsch.2 hdrStage (by decide) (by decide),
      ← hsch.2 hdrNSrc (by decide) (by decide),
      ← hsch.2 hdrPad (by decide) (by decide)]
  have hpD_eq₂ : dualPDst base s₂.mem = pDst := by
    unfold dualPDst pDst
    rw [← hsch.2 hdrPhase (by decide) (by decide), ← hsch.2 hdrStage (by decide) (by decide)]
  have hmbD_eq₂ : dualMbDst base s₂.mem = mbDst := by
    unfold dualMbDst mbDst
    rw [← hsch.2 hdrPhase (by decide) (by decide),
      ← hsch.2 hdrNDst (by decide) (by decide),
      ← hsch.2 hdrStage (by decide) (by decide),
      ← hsch.2 hdrPad (by decide) (by decide)]
  have hpgH_eq₂ : dualPgHost c V w base nLive s₂.mem = pgH := by
    unfold dualPgHost dualNHost dualMbHost pgH
    rw [← hsch.2 hdrNDst (by decide) (by decide),
      ← hsch.2 hdrNSrc (by decide) (by decide),
      ← hsch.2 hdrStage (by decide) (by decide),
      ← hsch.2 hdrPad (by decide) (by decide),
      ← hsch.2 hdrItemHi (by decide) (by decide),
      ← hsch.2 hdrQHi (by decide) (by decide)]
  obtain ⟨hcap_s₁, hcap_d₁, hdj₁, hdict_or₁, hcp0_₁, hsl_s₁, hsl_d₁, _, _⟩ := h₁.sl_8 hp8
  obtain ⟨hcap_s₂, hcap_d₂, hdj₂, hdict_or₂, hcp0_₂, hsl_s₂, hsl_d₂, _, _⟩ := h₂.sl_8 hp8_₂
  rw [hpS_eq₂, hmbS_eq₂, hpgH_eq₂] at hsl_s₂
  rw [hpD_eq₂, hmbD_eq₂, hpgH_eq₂] at hsl_d₂
  rw [hpgH_eq₂] at hcp0_₂
  have hpSrc_or : pSrc = base + hdrPBase0 ∨ pSrc = base + hdrPBase1 := by
    unfold pSrc dualPSrc; split_ifs <;> simp
  have hpDst_or : pDst = base + hdrPBase0 ∨ pDst = base + hdrPBase1 := by
    unfold pDst dualPDst; rw [ite_eq_left (by omega : s₁.mem (base + hdrPhase) < 10)]
    split_ifs <;> simp
  have hmbHost_192 : base + 192 ≤ pgH.metaBase := by
    change base + 192 ≤ dualMbHost base s₁.mem; unfold dualMbHost; split_ifs <;> omega
  have hibHi_192 : base + 192 ≤ pgH.itemBase := hsetup₁.ibLo_ge.trans hsetup₁.ibHi_ge_ibLo.1
  have hpg_cap₁ := hsetup₁.pgHost_cap (by omega) (by omega)
  have hfr_b₁ := hsetup₁.fr_bounds
  have hpos_s₁ := (hsetup₁.mbSrc_info (by omega)).2.1
  have hm_hi_s₁ := (hsetup₁.mbSrc_info (by omega)).2.2.2 (by omega)
  have hpos_d₁ := (hsetup₁.mbDst_info (by omega)).2.1
  have hm_hi_d₁ := (hsetup₁.mbDst_info (by omega)).2.2.1 (by omega)
  have hsl_sg₁ : EpochSlotInv c U V w sg₁.frontier pSrc mbSrc (pagedSlotIo 0 pgH_al) 0 true
      L₁.slotSrc sg₁.mem := by
    have hl := hsetup₁.lift_grow_slot hsl_s₁ rfl hpSrc_or hpos_s₁
      ⟨fun hup => absurd hup Nat.one_ne_zero, fun _ => hmbHost_192, hibHi_192⟩
      (fun hup => absurd hup Nat.one_ne_zero) (fun hup => absurd hup Nat.one_ne_zero)
      (fun _ => ⟨hpg_cap₁.1, hfr_b₁.2.2.2.1 ⟨by omega, by omega⟩⟩)
      ⟨hm_hi_s₁, fun hup => absurd hup Nat.one_ne_zero⟩
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hl
    rwa [← hsp₁, ← hkg₁] at hl
  have hsl_dg₁ : EpochSlotInv c U V w sg₁.frontier pDst mbDst (pagedSlotIo 1 pgH_al) 0 false
      L₁.slotDst sg₁.mem := by
    have hl := hsetup₁.lift_grow_slot hsl_d₁ rfl hpDst_or hpos_d₁
      ⟨fun hup => absurd hup Nat.one_ne_zero, fun _ => hmbHost_192, hibHi_192⟩
      (fun hup => absurd hup Nat.one_ne_zero) (fun hup => absurd hup Nat.one_ne_zero)
      (fun _ => ⟨hpg_cap₁.1, hfr_b₁.2.2.2.1 ⟨by omega, by omega⟩⟩)
      ⟨hm_hi_d₁, fun hup => absurd hup Nat.one_ne_zero⟩
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hl
    rwa [← hsp₁, ← hkg₁] at hl
  have hpg_cap₂ := hsetup₂.pgHost_cap (by omega) (by omega)
  have hfr_b₂ := hsetup₂.fr_bounds
  have hpos_s₂ : (L₂.slotSrc.nCap = 0 ∧
      (mbSrc = base + hdrSmallMeta0 ∨ mbSrc = base + hdrSmallMeta1)) ∨
      (L₂.slotSrc.nCap ≠ 0 ∧ base + 192 ≤ mbSrc) := by
    have hp := (hsetup₂.mbSrc_info (by omega)).2.1
    rw [← hmbS_eq₂]; exact hp
  have hib_eq : pgH.itemBase = s₂.mem (base + hdrItemHi) :=
    hsch.2 hdrItemHi (by decide) (by decide)
  have hm_hi_s₂ : mbSrc +
      (if L₂.slotSrc.nCap = 0 then 2 else offPageDir c w L₂.slotSrc.nCap) ≤ pgH.itemBase := by
    have hm := (hsetup₂.mbSrc_info (by omega)).2.2.2 (by omega)
    rw [← hmbS_eq₂, hib_eq]; exact hm
  have hpos_d₂ : (L₂.slotDst.nCap = 0 ∧
      (mbDst = base + hdrSmallMeta0 ∨ mbDst = base + hdrSmallMeta1)) ∨
      (L₂.slotDst.nCap ≠ 0 ∧ base + 192 ≤ mbDst) := by
    have hp := (hsetup₂.mbDst_info (by omega)).2.1
    rw [← hmbD_eq₂]; exact hp
  have hm_hi_d₂ : mbDst +
      (if L₂.slotDst.nCap = 0 then 2 else offPageDir c w L₂.slotDst.nCap) ≤ pgH.itemBase := by
    have hm := (hsetup₂.mbDst_info (by omega)).2.2.1 (by omega)
    rw [← hmbD_eq₂, hib_eq]; exact hm
  have hsl_sg₂ : EpochSlotInv c U V w sg₂.frontier pSrc mbSrc (pagedSlotIo 0 pgH_al) 0 true
      L₂.slotSrc sg₂.mem := by
    have hpg_c2 : nAlloc ≤ (pgH.maxPages - 2) * pgH.pgB := hpg_cap₁.1
    have hfr_c2 := hfr_b₂.2.2.2.1 ⟨by omega, by omega⟩
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hfr_c2
    rw [← hkg₂, ← hsch.2 hdrItemHi (by decide) (by decide),
      ← hsch.2 hdrQHi (by decide) (by decide)] at hfr_c2
    have hl := hsetup₂.lift_grow_slot hsl_s₂ rfl hpSrc_or hpos_s₂
      ⟨fun hup => absurd hup Nat.one_ne_zero, fun _ => hmbHost_192, hibHi_192⟩
      (fun hup => absurd hup Nat.one_ne_zero) (fun hup => absurd hup Nat.one_ne_zero)
      (fun _ => ⟨hpg_c2, by dsimp -failIfUnchanged only [Memory.State.frontier]; rwa [← hkg₂]⟩)
      ⟨hm_hi_s₂, fun hup => absurd hup Nat.one_ne_zero⟩
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hl
    rwa [← hsp₂, ← hkg₂] at hl
  have hsl_dg₂ : EpochSlotInv c U V w sg₂.frontier pDst mbDst (pagedSlotIo 1 pgH_al) 0 false
      L₂.slotDst sg₂.mem := by
    have hpg_c2 : nAlloc ≤ (pgH.maxPages - 2) * pgH.pgB := hpg_cap₁.1
    have hfr_c2 := hfr_b₂.2.2.2.1 ⟨by omega, by omega⟩
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hfr_c2
    rw [← hkg₂, ← hsch.2 hdrItemHi (by decide) (by decide),
      ← hsch.2 hdrQHi (by decide) (by decide)] at hfr_c2
    have hl := hsetup₂.lift_grow_slot hsl_d₂ rfl hpDst_or hpos_d₂
      ⟨fun hup => absurd hup Nat.one_ne_zero, fun _ => hmbHost_192, hibHi_192⟩
      (fun hup => absurd hup Nat.one_ne_zero) (fun hup => absurd hup Nat.one_ne_zero)
      (fun _ => ⟨hpg_c2, by dsimp -failIfUnchanged only [Memory.State.frontier]; rwa [← hkg₂]⟩)
      ⟨hm_hi_d₂, fun hup => absurd hup Nat.one_ne_zero⟩
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hl
    rwa [← hsp₂, ← hkg₂] at hl
  -- Lift `SlotStateCoupled` from `(s₁, s₂)` to `(sg₁, sg₂)`
  have hsg_mem_eq : ∀ addr, Coupled8Region c w base s₁.mem addr → sg₁.mem addr = sg₂.mem addr := by
    intro addr hreg
    dsimp only [sg₁, sg₂]; rw [hpg_ev₁, hpg_ev₂]; dsimp only [Memory.State.mem]
    split_ifs
    · by_cases h1 : addr = base + hdrPBase1 + 60
      · subst h1; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h1, Function.update_of_ne h1]
        by_cases h0 : addr = base + hdrPBase0 + 60
        · subst h0; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne h0, Function.update_of_ne h0]
          exact hc8.2.mem_eq addr hreg
    · exact hc8.2.mem_eq addr hreg
  have hsg_io_out : ∀ {st stg : Memory.State},
      (∀ addr, base + 192 ≤ addr → stg.mem addr = st.mem addr) →
      ∀ addr, (pagedSlotIo 0 pgH).OwnsAddr addr → stg.mem addr = st.mem addr := by
    intro st stg heq192 addr hia
    refine heq192 addr ?_
    rcases hia with hm | hi
    · have h1 : pgH.metaBase ≤ addr := by
        rcases hm with h | h | h <;> exact le_trans (Nat.le_add_right _ _) h.1
      clear *- hmbHost_192 h1; omega
    · have h1 : pgH.itemBase ≤ addr := hi.1
      clear *- hibHi_192 h1; omega
  have hsg₁_192 : ∀ addr, base + 192 ≤ addr → sg₁.mem addr = s₁.mem addr := fun addr hge => by
    dsimp only [sg₁]; rw [hpg_ev₁]; dsimp only [Memory.State.mem]; split_ifs
    · rw [Function.update_of_ne (by dsimp only [hdrPBase1]; clear *- hge; omega),
        Function.update_of_ne (by dsimp only [hdrPBase0]; clear *- hge; omega)]
    · rfl
  have hsg₂_192 : ∀ addr, base + 192 ≤ addr → sg₂.mem addr = s₂.mem addr := fun addr hge => by
    dsimp only [sg₂]; rw [hpg_ev₂]; dsimp only [Memory.State.mem]; split_ifs
    · rw [Function.update_of_ne (by dsimp only [hdrPBase1]; clear *- hge; omega),
        Function.update_of_ne (by dsimp only [hdrPBase0]; clear *- hge; omega)]
    · rfl
  have hns_sg₁ : sg₁.mem (mbSrc + 1) = s₁.mem (mbSrc + 1) := by
    have hmb_ne : mbSrc + 1 ≠ base + hdrPBase0 + 60 ∧ mbSrc + 1 ≠ base + hdrPBase1 + 60 := by
      unfold mbSrc dualMbSrc; dsimp only [hdrSmallMeta0, hdrPBase0, hdrPBase1]
      split_ifs <;> (clear *-; exact ⟨by omega, by omega⟩)
    dsimp only [sg₁]; rw [hpg_ev₁]; dsimp only [Memory.State.mem]
    split_ifs
    · rw [Function.update_of_ne hmb_ne.2, Function.update_of_ne hmb_ne.1]
    · rfl
  have hns_sg₂ : sg₂.mem (mbSrc + 1) = sg₁.mem (mbSrc + 1) :=
    (hsg_mem_eq (mbSrc + 1) (Or.inr (Or.inl ⟨by omega, by split_ifs <;> omega⟩))).symm
  have hc_grow : SlotStateCoupled (Coupled8Region c w base s₁.mem) (pagedSlotIo 0 pgH_al)
      (sg₁.mem (mbSrc + 1)) sg₁ sg₂ :=
    { fr_eq := by dsimp only [sg₁, sg₂]; rw [hsch.1, hkg_eq]
      side_zero := rfl
      valid₁ := by
        have hv := hsl_sg₁.io_valid
        have hw_pg : (pagedSlotIo 0 pgH_al).pgL.w = w := rfl
        rwa [hw_pg]
      disj := fun addr hreg => by
        have hraw := hsl_sg₁; unfold EpochSlotInv at hraw
        rcases hreg with ⟨h1, h2⟩ | hmeta
        · by_cases hc0 : L₁.slotSrc.nCap = 0
          · rw [ite_eq_left hc0] at hraw
            exact fun hia => hraw.2.2.2.2.1 addr h1 h2 (Or.inr (Or.inr hia))
          · rw [ite_eq_right hc0] at hraw; exact hraw.1.disj_pBase_io addr h1 h2
        · rw [← hcap_s₁] at hmeta; unfold slotOwnsNonPageMeta at hmeta
          by_cases hc0 : L₁.slotSrc.nCap = 0
          · rw [ite_eq_left hc0] at hraw hmeta
            rcases hmeta with ⟨g1, g2⟩ | ⟨hne, _⟩
            · exact hraw.2.2.1.disjoint_hdr addr (by dsimp only; clear *- g1 g2; omega)
            · exact absurd hc0 hne
          · rw [ite_eq_right hc0] at hraw hmeta
            exact hraw.1.disj_fast_io addr (hmeta.imp id And.right)
      mem_eq := hsg_mem_eq
      inv₁ := hsl_sg₁.io_stateInv
      inv₂ := hns_sg₂ ▸ hsl_sg₂.io_stateInv
      pair_eq := fun idx hidx => by
        have hidx0 : idx < s₁.mem (mbSrc + 1) := hns_sg₁ ▸ hidx
        have hp1 := ((pagedSlotIo 0 pgH).congr_of_outside hw_pos hc8.2.inv₁
          (hsg_io_out hsg₁_192)).2 idx hidx0
        have hp2 := ((pagedSlotIo 0 pgH).congr_of_outside hw_pos hc8.2.inv₂
          (hsg_io_out hsg₂_192)).2 idx hidx0
        exact hp1.trans ((hc8.2.pair_eq idx hidx0).trans hp2.symm) }
  -- Step `userMutateRawProg`: `epochDeleteProg (pSrc, u.val)` then `pDst` mutation
  have hsg₁_ph : sg₁.mem (base + hdrPhase) = 8 := by
    dsimp only [sg₁]; rw [hsp₁]; exact (hsetup₁.grow_low hdrPhase (by decide)).trans hp8
  have hsg₁_stg : sg₁.mem (base + hdrStage) = s₁.mem (base + hdrStage) := by
    dsimp only [sg₁]; rw [hsp₁]; exact hsetup₁.grow_low hdrStage (by decide)
  have hsg₂_ph : sg₂.mem (base + hdrPhase) = 8 := by
    dsimp only [sg₂]; rw [hsp₂]; exact (hsetup₂.grow_low hdrPhase (by decide)).trans hp8_₂
  have hsg₂_stg : sg₂.mem (base + hdrStage) = s₁.mem (base + hdrStage) := by
    dsimp only [sg₂]; rw [hsp₂]
    exact (hsetup₂.grow_low hdrStage (by decide)).trans
      (hsch.2 hdrStage (by decide) (by decide)).symm
  have hpD_if : pDst = (if s₁.mem (base + hdrStage) = 0 then base + hdrPBase1
      else base + hdrPBase0) := by
    unfold pDst dualPDst; rw [ite_eq_left (by omega : s₁.mem (base + hdrPhase) < 10)]
  have hsr₁_ev : sr₁ = (Memory.spec 0).clientState sg₁
      (if opTag = 1 then
         epochDeleteProg (pSrc, u.val) >>= fun _ => epochInsertProg ((pDst, u.val), v_val)
       else
         epochDeleteProg (pSrc, u.val) >>= fun _ => epochDeleteProg (pDst, u.val)) := by
    rw [hsr₁, (userMutateRawProg_eval (opTag := opTag) (u_val := u.val) (v_val := v_val)
      sg₁ hsg₁_ph hsg₁_stg).1]
    have hpS_def : (if s₁.mem (base + hdrStage) = 0 then base + hdrPBase0
      else base + hdrPBase1) = pSrc := rfl
    rw [hpS_def, ← hpD_if]
    by_cases hop1 : opTag = 1
    · rw [ite_eq_left hop1, ite_eq_left hop1, ite_eq_left rfl]
    · rw [ite_eq_right hop1, ite_eq_right hop1, ite_eq_left rfl]
  have hsr₂_ev : sr₂ = (Memory.spec 0).clientState sg₂
      (if opTag = 1 then
         epochDeleteProg (pSrc, u.val) >>= fun _ => epochInsertProg ((pDst, u.val), v_val)
       else
         epochDeleteProg (pSrc, u.val) >>= fun _ => epochDeleteProg (pDst, u.val)) := by
    rw [hsr₂, (userMutateRawProg_eval (opTag := opTag) (u_val := u.val) (v_val := v_val)
      sg₂ hsg₂_ph hsg₂_stg).1]
    have hpS_def : (if s₁.mem (base + hdrStage) = 0 then base + hdrPBase0
      else base + hdrPBase1) = pSrc := rfl
    rw [hpS_def, ← hpD_if]
    by_cases hop1 : opTag = 1
    · rw [ite_eq_left hop1, ite_eq_left hop1, ite_eq_left rfl]
    · rw [ite_eq_right hop1, ite_eq_right hop1, ite_eq_left rfl]
  -- Disjointness facts for `dualPagedMutate_raw` and `partner_dst_coupled`
  have hp_disj : pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc := by
    rw [hpD_if]; unfold pSrc dualPSrc; dsimp only [hdrPBase0, hdrPBase1]
    split_ifs <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
  have hpm_s : pDst + 64 ≤ mbSrc ∨
      mbSrc + (if L₁.slotSrc.nCap = 0 then 2 else offPageDir c w L₁.slotSrc.nCap) ≤ pDst := by
    rw [hpD_if, hcap_s₁]; unfold mbSrc dualMbSrc dualCapSrc
    dsimp only [hdrPBase0, hdrPBase1, hdrSmallMeta0]
    by_cases hst0 : s₁.mem (base + hdrStage) = 0
    · simp only [hst0, ↓reduceIte]; split_ifs <;> [exact Or.inr (by omega); exact Or.inl (by omega)]
    · simp only [hst0, ↓reduceIte]; exact Or.inl (by omega)
  have hpm_d : pSrc + 64 ≤ mbDst ∨
      mbDst + (if L₁.slotDst.nCap = 0 then 2 else offPageDir c w L₁.slotDst.nCap) ≤ pSrc := by
    rw [hcap_d₁]; unfold mbDst dualMbDst pSrc dualPSrc
    rw [ite_eq_left (by omega : s₁.mem (base + hdrPhase) < 10)]
    dsimp only [hdrPBase0, hdrPBase1, hdrSmallMeta1]
    by_cases hd0 : s₁.mem (base + hdrNDst) = 0
    · simp only [hd0, ↓reduceIte]; split_ifs <;> exact Or.inr (by omega)
    · simp only [hd0, ↓reduceIte]; split_ifs <;> exact Or.inl (by omega)
  have hmm_disj :
      mbSrc + (if L₁.slotSrc.nCap = 0 then 2 else offPageDir c w L₁.slotSrc.nCap) ≤ mbDst ∨
      mbDst + (if L₁.slotDst.nCap = 0 then 2 else offPageDir c w L₁.slotDst.nCap) ≤ mbSrc := by
    have hsched₁ := h₁.sched; rw [ite_eq_right (by omega)] at hsched₁
    obtain ⟨hmDst_eq, hpad_eq, _, _, _, _⟩ := hsched₁.ge2 (by omega)
    rw [hcap_s₁, hcap_d₁]; unfold mbSrc dualMbSrc mbDst dualMbDst dualCapSrc
    rw [ite_eq_left (by omega : s₁.mem (base + hdrPhase) < 10)]
    dsimp only [hdrSmallMeta0, hdrSmallMeta1]
    by_cases hd0 : s₁.mem (base + hdrNDst) = 0
    · obtain ⟨hs_pos, hst0, _⟩ := hsched₁.nDst_zero hd0
      simp only [hd0, hst0, hs_pos.ne', ↓reduceIte]; exact Or.inr (by omega)
    · simp only [hd0, ↓reduceIte]
      by_cases hst0 : s₁.mem (base + hdrStage) = 0
      · simp only [hst0, ↓reduceIte]
        by_cases hs0 : s₁.mem (base + hdrNSrc) = 0
        · simp only [hs0, ↓reduceIte]; exact Or.inl (by omega)
        · have hod_s := hsetup₁.od_le_nSrc hs0
          have hmS_p : s₁.mem (base + hdrMSrc) ≤ s₁.mem (base + hdrPad) := by
            rw [hpad_eq]; exact le_max_left _ _
          rw [← h₁.mSrc_eq] at hod_s
          simp only [hs0, ↓reduceIte]; exact Or.inl (by omega)
      · have hod_d := hsetup₁.od_le_nDst (by omega) hd0
        have hmD_p : s₁.mem (base + hdrMDst) ≤ s₁.mem (base + hdrPad) := by
          rw [hpad_eq]; exact le_max_right _ _
        rw [← hmDst_eq] at hod_d
        simp only [hst0, ↓reduceIte]; exact Or.inr (by omega)
  have hnc_d_eq : L₂.slotDst.nCap = L₁.slotDst.nCap := by
    rw [hcap_d₂, hcap_d₁, hsch.2 hdrNDst (by decide) (by decide)]
  have hnc_s_eq : L₂.slotSrc.nCap = L₁.slotSrc.nCap := by
    rw [hcap_s₂, hcap_s₁]; unfold dualCapSrc
    rw [hsch.2 hdrStage (by decide) (by decide),
      hsch.2 hdrNSrc (by decide) (by decide),
      hsch.2 hdrNDst (by decide) (by decide)]
  -- Step A: `epochDeleteProg (pSrc, u.val)` on `(sg₁, sg₂)`
  have hsub_c8 : ∀ addr, SlotSrcMetaRegion c w pSrc mbSrc L₁.slotSrc.nCap addr →
      Coupled8Region c w base s₁.mem addr := by
    rw [hcap_s₁]; exact fun _ h => h
  have hcs_del := epochDelete_src_coupled hsl_sg₁ hsub_c8 hc_grow u
  set s_del₁ := (Memory.spec 0).clientState sg₁ (epochDeleteProg (pSrc, u.val))
  set s_del₂ := (Memory.spec 0).clientState sg₂ (epochDeleteProg (pSrc, u.val))
  have hc_del : SlotStateCoupled (Coupled8Region c w base s₁.mem) (pagedSlotIo 0 pgH_al)
      (s_del₁.mem (mbSrc + 1)) s_del₁ s_del₂ := hcs_del.coupled
  -- Invoke `dualPagedMutate_raw` on `sg₁` and `sg₂` to get post-state `EpochSlotInv`s!
  have hcp_sg₁ : (extractPageUnperm pgH_al sg₁.mem).cleanPhase = 0 :=
    cleanPhase_zero_of_paged0 hsl_sg₁
  have hcp_sg₂ : (extractPageUnperm pgH_al sg₂.mem).cleanPhase = 0 :=
    cleanPhase_zero_of_paged0 hsl_sg₂
  have hsum_card₁ : (liveDom L₁.slotDst.s_abs).card + (liveDom L₁.slotSrc.s_abs).card = nLive := by
    rw [← liveDom_orOpt_card hdj₁, ← dom_toDictState_card, hdict_or₁]
  have hsum_card₂ : (liveDom L₂.slotDst.s_abs).card + (liveDom L₂.slotSrc.s_abs).card = nLive := by
    rw [← liveDom_orOpt_card hdj₂, ← dom_toDictState_card, hdict_or₂]
  have hcap_d_8_₁ : opTag = 1 → (orOpt L₁.slotDst.s_abs L₁.slotSrc.s_abs) u = none →
      (L₁.slotDst.nCap ≠ 0 →
        (liveDom L₁.slotDst.s_abs).card + (liveDom L₁.slotSrc.s_abs).card < L₁.slotDst.nCap) ∧
      (liveDom L₁.slotDst.s_abs).card + (liveDom L₁.slotSrc.s_abs).card + 1 ≤ pgH_al.nCap := by
    intro hop1 hor_none
    have hnone_d : s_dict u = none := by rw [← hdict_or₁]; simp [toDictState, hor_none]
    have hcap := cap_lt_on_insert_none h₁ hnone_d
    rw [hsum_card₁, hcap_d₁]
    dsimp only [pgH_al, hostPageLayout, epochPageArenaLayout, nAlloc]
    rw [ite_eq_left hop1, min_eq_left hcap.1]
    exact ⟨hcap.2.2 (by omega), le_rfl⟩
  have hcap_ov_8_₁ : opTag = 1 →
      (L₁.slotDst.nCap ≠ 0 →
        (liveDom L₁.slotDst.s_abs).card + (liveDom L₁.slotSrc.s_abs).card ≤ L₁.slotDst.nCap) ∧
      (liveDom L₁.slotDst.s_abs).card + (liveDom L₁.slotSrc.s_abs).card ≤ pgH_al.nCap := by
    intro hop1
    rw [hsum_card₁, hcap_d₁]
    dsimp only [pgH_al, hostPageLayout, epochPageArenaLayout, nAlloc]
    rw [ite_eq_left hop1]
    refine ⟨fun hd_nz => ?_, le_min (Nat.le_succ _) h₁.live_le⟩
    have hds := hsetup₁.dst_safe; rw [ite_eq_right (by omega)] at hds
    simp only [EpochCapSafe, hd_nz, ↓reduceIte] at hds; exact hds.2.2.2
  have hcap_d_8_₂ : opTag = 1 → (orOpt L₂.slotDst.s_abs L₂.slotSrc.s_abs) u = none →
      (L₂.slotDst.nCap ≠ 0 →
        (liveDom L₂.slotDst.s_abs).card + (liveDom L₂.slotSrc.s_abs).card < L₂.slotDst.nCap) ∧
      (liveDom L₂.slotDst.s_abs).card + (liveDom L₂.slotSrc.s_abs).card + 1 ≤ pgH_al.nCap := by
    intro hop1 hor_none
    have hnone_d : s_dict u = none := by rw [← hdict_or₂]; simp [toDictState, hor_none]
    have hcap := cap_lt_on_insert_none h₁ hnone_d
    rw [hsum_card₂, hnc_d_eq, hcap_d₁]
    dsimp only [pgH_al, hostPageLayout, epochPageArenaLayout, nAlloc]
    rw [ite_eq_left hop1, min_eq_left hcap.1]
    exact ⟨hcap.2.2 (by omega), le_rfl⟩
  have hcap_ov_8_₂ : opTag = 1 →
      (L₂.slotDst.nCap ≠ 0 →
        (liveDom L₂.slotDst.s_abs).card + (liveDom L₂.slotSrc.s_abs).card ≤ L₂.slotDst.nCap) ∧
      (liveDom L₂.slotDst.s_abs).card + (liveDom L₂.slotSrc.s_abs).card ≤ pgH_al.nCap := by
    intro hop1
    rw [hsum_card₂, ← hsum_card₁, hnc_d_eq]
    exact hcap_ov_8_₁ hop1
  have hmut₁ := dualPagedMutate_raw hsl_sg₁ hsl_dg₁ hdj₁ hcp_sg₁ hp_disj hpm_s hpm_d hmm_disj
    u v hv_eq hcap_d_8_₁ hcap_ov_8_₁
  have hmut₂ := dualPagedMutate_raw hsl_sg₂ hsl_dg₂ hdj₂ hcp_sg₂ hp_disj
    (hnc_s_eq ▸ hpm_s) (hnc_d_eq ▸ hpm_d) (hnc_s_eq ▸ hnc_d_eq ▸ hmm_disj)
    u v hv_eq hcap_d_8_₂ hcap_ov_8_₂
  dsimp only at hmut₁ hmut₂
  rw [← hsr₁_ev] at hmut₁; rw [← hsr₂_ev] at hmut₂
  -- Also extract `hsl_d1_₁`, `hsl_d1_₂` on `s_del₁`, `s_del₂` to step `hc_del → hc_raw`!
  have hsp_del₁ := hsl_sg₁.delete_spec u
  have hsp_del₂ := hsl_sg₂.delete_spec u
  dsimp only at hsp_del₁ hsp_del₂
  have hslk0_del₁ : (if (pagedSlotIo 0 pgH_al).usePaged = 0 ∨
      (extractPageUnperm (pagedSlotIo 0 pgH_al).pgL sg₁.mem).cleanPhase = 0
      then 0 else 24) = 0 := ite_eq_left (Or.inr hcp_sg₁)
  have hslk0_del₂ : (if (pagedSlotIo 0 pgH_al).usePaged = 0 ∨
      (extractPageUnperm (pagedSlotIo 0 pgH_al).pgL sg₂.mem).cleanPhase = 0
      then 0 else 24) = 0 := ite_eq_left (Or.inr hcp_sg₂)
  have hsl_s_del₁ : EpochSlotInv c U V w s_del₁.frontier pSrc mbSrc (pagedSlotIo 0 pgH_al) 0 true
      ⟨L₁.slotSrc.nCap, Function.update L₁.slotSrc.s_abs u none, L₁.slotSrc.seeds, L₁.slotSrc.evs⟩
      s_del₁.mem := by simpa only [hslk0_del₁, ↓reduceIte] using hsp_del₁.2.1
  have hsl_s_del₂ : EpochSlotInv c U V w s_del₂.frontier pSrc mbSrc (pagedSlotIo 0 pgH_al) 0 true
      ⟨L₂.slotSrc.nCap, Function.update L₂.slotSrc.s_abs u none, L₂.slotSrc.seeds, L₂.slotSrc.evs⟩
      s_del₂.mem := by simpa only [hslk0_del₂, ↓reduceIte] using hsp_del₂.2.1
  have hup0 : (pagedSlotIo 0 pgH_al).usePaged ≠ 0 := Nat.one_ne_zero
  have hup1 : (pagedSlotIo 1 pgH_al).usePaged ≠ 0 := Nat.one_ne_zero
  have hcp_del₁ : (extractPageUnperm pgH_al s_del₁.mem).cleanPhase = 0 :=
    cleanPhase_zero_of_paged0 hsl_s_del₁
  have hcp_del₂ : (extractPageUnperm pgH_al s_del₂.mem).cleanPhase = 0 :=
    cleanPhase_zero_of_paged0 hsl_s_del₂
  obtain ⟨hno_s_pDst₁, hno_s_mDst₁⟩ :=
    not_paged_slotOwnsAddr_partner (sbA := 0) (slA := L₁.slotSrc) hsl_dg₁ hpm_s hmm_disj
  obtain ⟨hno_s_pDst₂, hno_s_mDst₂⟩ :=
    not_paged_slotOwnsAddr_partner (sbA := 0) (slA := L₂.slotSrc) hsl_dg₂
      (hnc_s_eq ▸ hpm_s) (hnc_s_eq ▸ hnc_d_eq ▸ hmm_disj)
  obtain ⟨hno_d_pSrc₁, hno_d_mSrc₁⟩ :=
    not_paged_slotOwnsAddr_partner (sbA := 1) (slA := L₁.slotDst) hsl_sg₁ hpm_d hmm_disj.symm
  have hdisj_c8_d : ∀ addr, Coupled8Region c w base s₁.mem addr →
      ¬slotOwnsAddr c w mbDst L₁.slotDst.nCap (pagedSlotIo 1 pgH_al) addr := by
    intro addr hreg
    rcases hreg with ⟨h1, h2⟩ | hm
    · exact hno_d_pSrc₁ addr h1 h2
    · exact hno_d_mSrc₁ addr (hcap_s₁.symm ▸ hm)
  have hsl_d_del₁ : EpochSlotInv c U V w s_del₁.frontier pDst mbDst (pagedSlotIo 1 pgH_al) 0 false
      L₁.slotDst s_del₁.mem :=
    (hsp_del₁.1 ▸ hsl_dg₁).partner_paged_frame hsl_s_del₁.io_stateInv hcp_del₁
      (fun a h1 h2 => hsp_del₁.2.2.1 a (hno_s_pDst₁ a h1 h2))
      (fun a ha => hsp_del₁.2.2.1 a (hno_s_mDst₁ a ha))
      (hsp_del₁.2.2.2.2.1 hup0).1 (hsp_del₁.2.2.2.2.1 hup0).2
  have hsl_d_del₂ : EpochSlotInv c U V w s_del₂.frontier pDst mbDst (pagedSlotIo 1 pgH_al) 0 false
      L₂.slotDst s_del₂.mem :=
    (hsp_del₂.1 ▸ hsl_dg₂).partner_paged_frame hsl_s_del₂.io_stateInv hcp_del₂
      (fun a h1 h2 => hsp_del₂.2.2.1 a (hno_s_pDst₂ a h1 h2))
      (fun a ha => hsp_del₂.2.2.1 a (hno_s_mDst₂ a ha))
      (hsp_del₂.2.2.2.2.1 hup0).1 (hsp_del₂.2.2.2.2.1 hup0).2
  -- Notice `s_del₂.mem (mbSrc + 1) = s_del₁.mem (mbSrc + 1)` via `hc_del.mem_eq`!
  have hmb1_in_c8 : Coupled8Region c w base s₁.mem (mbSrc + 1) :=
    Or.inr (Or.inl ⟨by omega, by split_ifs <;> omega⟩)
  -- Step B: `pDst` mutation (`epochInsertProg` or `epochDeleteProg`) preserves `SlotStateCoupled`
  have hc_raw : SlotStateCoupled (Coupled8Region c w base s₁.mem) (pagedSlotIo 0 pgH_al)
      (sr₁.mem (mbSrc + 1)) sr₁ sr₂ := by
    by_cases hop1 : opTag = 1
    · have hsr₁_d : sr₁ =
          (Memory.spec 0).clientState s_del₁ (epochInsertProg ((pDst, u.val), v.val)) := by
        rw [hsr₁_ev, ite_eq_left hop1, hv_eq hop1, StateTransitionSpec.clientState_bind]
      have hsr₂_d : sr₂ =
          (Memory.spec 0).clientState s_del₂ (epochInsertProg ((pDst, u.val), v.val)) := by
        rw [hsr₂_ev, ite_eq_left hop1, hv_eq hop1, StateTransitionSpec.clientState_bind]
      have hti_d₁ : (extractPagePair pgH_al s_del₁.mem).totalItems =
          (liveDom (Function.update L₁.slotSrc.s_abs u none)).card +
            (liveDom L₁.slotDst.s_abs).card := by
        have hi0 := hsl_s_del₁.io_stateInv; have hi1 := hsl_d_del₁.io_stateInv
        unfold SlotIoLayout.StateInv at hi0 hi1
        rw [ite_eq_right hup0] at hi0; rw [ite_eq_right hup1] at hi1
        have hvl0 : (extractPagePair pgH_al s_del₁.mem).virtLen false =
          s_del₁.mem (mbSrc + 1) := hi0.2.2.2.2.1
        have hvl1 : (extractPagePair pgH_al s_del₁.mem).virtLen true =
          s_del₁.mem (mbDst + 1) := hi1.2.2.2.2.1
        have hns0 := hsl_s_del₁.mem_nSide_eq; have hns1 := hsl_d_del₁.mem_nSide_eq
        dsimp only at hns0; unfold PagePairState.totalItems
        rw [hvl0, hvl1, hns0, hns1]
      have hti_d₂ : (extractPagePair pgH_al s_del₂.mem).totalItems =
          (liveDom (Function.update L₂.slotSrc.s_abs u none)).card +
            (liveDom L₂.slotDst.s_abs).card := by
        have hi0 := hsl_s_del₂.io_stateInv; have hi1 := hsl_d_del₂.io_stateInv
        unfold SlotIoLayout.StateInv at hi0 hi1
        rw [ite_eq_right hup0] at hi0; rw [ite_eq_right hup1] at hi1
        have hvl0 : (extractPagePair pgH_al s_del₂.mem).virtLen false =
          s_del₂.mem (mbSrc + 1) := hi0.2.2.2.2.1
        have hvl1 : (extractPagePair pgH_al s_del₂.mem).virtLen true =
          s_del₂.mem (mbDst + 1) := hi1.2.2.2.2.1
        have hns0 := hsl_s_del₂.mem_nSide_eq; have hns1 := hsl_d_del₂.mem_nSide_eq
        dsimp only at hns0; unfold PagePairState.totalItems
        rw [hvl0, hvl1, hns0, hns1]
      have hsp_i₁ := hsl_d_del₁.insert_spec u v
        (fun hd_n hne_d => by
          by_cases hs_n : L₁.slotSrc.s_abs u = none
          · have := (hcap_d_8_₁ hop1 (by simp [orOpt, Option.or, hd_n, hs_n])).1 hne_d; omega
          · have hp_s : 0 < (liveDom L₁.slotSrc.s_abs).card :=
              Finset.card_pos.mpr ⟨u, (mem_liveDom_iff _ _).mpr hs_n⟩
            have := (hcap_ov_8_₁ hop1).1 hne_d; omega)
        (fun hd_n => by
          dsimp only [pagedSlotIo]; rw [hti_d₁]
          by_cases hs_n : L₁.slotSrc.s_abs u = none
          · have hc := (hcap_d_8_₁ hop1 (by simp [orOpt, Option.or, hd_n, hs_n])).2
            rw [liveDom_delete_card, ite_eq_left hs_n]; exact ⟨by omega, fun _ => by omega⟩
          · have hp_s : 0 < (liveDom L₁.slotSrc.s_abs).card :=
              Finset.card_pos.mpr ⟨u, (mem_liveDom_iff _ _).mpr hs_n⟩
            have hc := (hcap_ov_8_₁ hop1).2
            rw [liveDom_delete_card, ite_eq_right hs_n]; exact ⟨by omega, fun _ => by omega⟩)
      have hsp_i₂ := hsl_d_del₂.insert_spec u v
        (fun hd_n hne_d => by
          by_cases hs_n : L₂.slotSrc.s_abs u = none
          · have := (hcap_d_8_₂ hop1 (by simp [orOpt, Option.or, hd_n, hs_n])).1 hne_d; omega
          · have hp_s : 0 < (liveDom L₂.slotSrc.s_abs).card :=
              Finset.card_pos.mpr ⟨u, (mem_liveDom_iff _ _).mpr hs_n⟩
            have := (hcap_ov_8_₂ hop1).1 hne_d; omega)
        (fun hd_n => by
          dsimp only [pagedSlotIo]; rw [hti_d₂]
          by_cases hs_n : L₂.slotSrc.s_abs u = none
          · have hc := (hcap_d_8_₂ hop1 (by simp [orOpt, Option.or, hd_n, hs_n])).2
            rw [liveDom_delete_card, ite_eq_left hs_n]; exact ⟨by omega, fun _ => by omega⟩
          · have hp_s : 0 < (liveDom L₂.slotSrc.s_abs).card :=
              Finset.card_pos.mpr ⟨u, (mem_liveDom_iff _ _).mpr hs_n⟩
            have hc := (hcap_ov_8_₂ hop1).2
            rw [liveDom_delete_card, ite_eq_right hs_n]; exact ⟨by omega, fun _ => by omega⟩)
      dsimp only at hsp_i₁ hsp_i₂
      rw [← hsr₁_d] at hsp_i₁; rw [← hsr₂_d] at hsp_i₂
      have hm₁ : ∀ addr, Coupled8Region c w base s₁.mem addr → sr₁.mem addr = s_del₁.mem addr :=
        fun addr ha => hsp_i₁.2.2.1 addr (hdisj_c8_d addr ha)
      have hm₂ : ∀ addr, Coupled8Region c w base s₁.mem addr → sr₂.mem addr = s_del₂.mem addr :=
        fun addr ha => hsp_i₂.2.2.1 addr (hnc_d_eq ▸ hdisj_c8_d addr ha)
      have hns_sr : sr₂.mem (mbSrc + 1) = sr₁.mem (mbSrc + 1) :=
        (hm₂ _ hmb1_in_c8).trans ((hc_del.mem_eq _ hmb1_in_c8).symm.trans (hm₁ _ hmb1_in_c8).symm)
      have hi₁' := hmut₁.2.2.2.2.2.2.1.io_stateInv
      have hi₂' := hmut₂.2.2.2.2.2.2.1.io_stateInv
      have hvl_pres₁ := (hsp_i₁.2.2.2.2.1 hup1).1
      have hp₁ := (hsp_i₁.2.2.2.2.1 hup1).2
      have hp₂ := (hsp_i₂.2.2.2.2.1 hup1).2
      have hi_del₁ := hc_del.inv₁; have hi_del₂ := hc_del.inv₂
      unfold SlotIoLayout.StateInv at hi_del₁ hi_del₂
      rw [ite_eq_right hup0] at hi_del₁ hi_del₂
      have hvl_del₁ := hi_del₁.2.2.2.2.1; have hvl_del₂ := hi_del₂.2.2.2.2.1
      have hns_pres₁ : sr₁.mem (mbSrc + 1) = s_del₁.mem (mbSrc + 1) := hm₁ _ hmb1_in_c8
      exact
        { fr_eq := hsp_i₁.1.trans (hc_del.fr_eq.trans hsp_i₂.1.symm)
          side_zero := rfl
          valid₁ := hsp_i₁.1 ▸ hc_del.valid₁
          disj := hc_del.disj
          mem_eq := fun addr ha =>
            (hm₁ addr ha).trans ((hc_del.mem_eq addr ha).trans (hm₂ addr ha).symm)
          inv₁ := hi₁'
          inv₂ := hns_sr ▸ hi₂'
          pair_eq := fun idx hidx => by
            have hidx₀ : idx < s_del₁.mem (mbSrc + 1) := hns_pres₁ ▸ hidx
            exact (hp₁ idx (hvl_del₁.symm ▸ hidx₀)).trans
              ((hc_del.pair_eq idx hidx₀).trans (hp₂ idx (hvl_del₂.symm ▸ hidx₀)).symm) }
    · have hsr₁_d : sr₁ = (Memory.spec 0).clientState s_del₁ (epochDeleteProg (pDst, u.val)) := by
        rw [hsr₁_ev, ite_eq_right hop1, StateTransitionSpec.clientState_bind]
      have hsr₂_d : sr₂ = (Memory.spec 0).clientState s_del₂ (epochDeleteProg (pDst, u.val)) := by
        rw [hsr₂_ev, ite_eq_right hop1, StateTransitionSpec.clientState_bind]
      have hsp_d₁ := hsl_d_del₁.delete_spec u
      have hsp_d₂ := hsl_d_del₂.delete_spec u
      dsimp only at hsp_d₁ hsp_d₂
      rw [← hsr₁_d] at hsp_d₁; rw [← hsr₂_d] at hsp_d₂
      have hm₁ : ∀ addr, Coupled8Region c w base s₁.mem addr → sr₁.mem addr = s_del₁.mem addr :=
        fun addr ha => hsp_d₁.2.2.1 addr (hdisj_c8_d addr ha)
      have hm₂ : ∀ addr, Coupled8Region c w base s₁.mem addr → sr₂.mem addr = s_del₂.mem addr :=
        fun addr ha => hsp_d₂.2.2.1 addr (hnc_d_eq ▸ hdisj_c8_d addr ha)
      have hns_sr : sr₂.mem (mbSrc + 1) = sr₁.mem (mbSrc + 1) :=
        (hm₂ _ hmb1_in_c8).trans ((hc_del.mem_eq _ hmb1_in_c8).symm.trans (hm₁ _ hmb1_in_c8).symm)
      have hi₁' := hmut₁.2.2.2.2.2.2.1.io_stateInv
      have hi₂' := hmut₂.2.2.2.2.2.2.1.io_stateInv
      have hp₁ := (hsp_d₁.2.2.2.2.1 hup1).2
      have hp₂ := (hsp_d₂.2.2.2.2.1 hup1).2
      have hi_del₁ := hc_del.inv₁; have hi_del₂ := hc_del.inv₂
      unfold SlotIoLayout.StateInv at hi_del₁ hi_del₂
      rw [ite_eq_right hup0] at hi_del₁ hi_del₂
      have hvl_del₁ := hi_del₁.2.2.2.2.1; have hvl_del₂ := hi_del₂.2.2.2.2.1
      have hns_pres₁ : sr₁.mem (mbSrc + 1) = s_del₁.mem (mbSrc + 1) := hm₁ _ hmb1_in_c8
      exact
        { fr_eq := hsp_d₁.1.trans (hc_del.fr_eq.trans hsp_d₂.1.symm)
          side_zero := rfl
          valid₁ := hsp_d₁.1 ▸ hc_del.valid₁
          disj := hc_del.disj
          mem_eq := fun addr ha =>
            (hm₁ addr ha).trans ((hc_del.mem_eq addr ha).trans (hm₂ addr ha).symm)
          inv₁ := hi₁'
          inv₂ := hns_sr ▸ hi₂'
          pair_eq := fun idx hidx => by
            have hidx₀ : idx < s_del₁.mem (mbSrc + 1) := hns_pres₁ ▸ hidx
            exact (hp₁ idx (hvl_del₁.symm ▸ hidx₀)).trans
              ((hc_del.pair_eq idx hidx₀).trans (hp₂ idx (hvl_del₂.symm ▸ hidx₀)).symm) }
  -- Step C: `syncLiveCountsProg` lifts `hc_raw` from `(sr₁, sr₂)` to `Coupled8` on `(sm₁, sm₂)`
  have hstep₁ := fgStep_eq8_aux h₁ u v hv_eq hsetup₁ hsp₁ hkg₁ hsm₁ hp8
  have hstep₂ := fgStep_eq8_aux h₂ u v hv_eq hsetup₂ hsp₂ hkg₂ hsm₂ hp8_₂
  have hsr₁_ph : sr₁.mem (base + hdrPhase) = 8 := by
    have hno_s : ¬slotOwnsAddr c w mbSrc L₁.slotSrc.nCap (pagedSlotIo 0 pgH_al) (base + hdrPhase) :=
      fun ha => by
        have hb := slotOwnsAddr_bounds (pBase := pSrc)
          (fun h0 => by rcases hpos_s₁ with ⟨_, h⟩ | ⟨hne, _⟩ <;> [exact h; exact absurd h0 hne])
          (fun hne => by
            rw [hcap_s₁] at hne; unfold dualCapSrc at hne; unfold mbSrc dualMbSrc
            by_cases hst0 : s₁.mem (base + hdrStage) = 0
            · simp only [hst0, ↓reduceIte] at hne ⊢; rw [ite_eq_right hne]; exact Or.inl rfl
            · simp only [hst0, ↓reduceIte]; exact Or.inr rfl)
          (fun _ => ⟨hmbHost_192, hibHi_192⟩)
          (fun h => absurd h Nat.one_ne_zero) (fun h => absurd h Nat.one_ne_zero) _ ha
        exact absurd (hb.2.1 (by dsimp only [hdrPhase]; omega)).2.1 Nat.one_ne_zero
    have hno_d : ¬slotOwnsAddr c w mbDst L₁.slotDst.nCap (pagedSlotIo 1 pgH_al) (base + hdrPhase) :=
      fun ha => by
        have hb := slotOwnsAddr_bounds (pBase := pDst)
          (fun h0 => by rcases hpos_d₁ with ⟨_, h⟩ | ⟨hne, _⟩ <;> [exact h; exact absurd h0 hne])
          (fun hne => by
            rw [hcap_d₁] at hne; unfold mbDst dualMbDst
            rw [ite_eq_left (by omega : s₁.mem (base + hdrPhase) < 10), ite_eq_right hne]
            split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl])
          (fun _ => ⟨hmbHost_192, hibHi_192⟩)
          (fun h => absurd h Nat.one_ne_zero) (fun h => absurd h Nat.one_ne_zero) _ ha
        exact absurd (hb.2.1 (by dsimp only [hdrPhase]; omega)).2.1 Nat.one_ne_zero
    exact (hmut₁.2.2.2.2.2.2.2.2.1 _ hno_s hno_d).trans hsg₁_ph
  have hsr₂_ph : sr₂.mem (base + hdrPhase) = 8 := by
    have hno_s : ¬slotOwnsAddr c w mbSrc L₂.slotSrc.nCap (pagedSlotIo 0 pgH_al) (base + hdrPhase) :=
      hnc_s_eq ▸ fun ha => by
        have hb := slotOwnsAddr_bounds (pBase := pSrc)
          (fun h0 => by rcases hpos_s₁ with ⟨_, h⟩ | ⟨hne, _⟩ <;> [exact h; exact absurd h0 hne])
          (fun hne => by
            rw [hcap_s₁] at hne; unfold dualCapSrc at hne; unfold mbSrc dualMbSrc
            by_cases hst0 : s₁.mem (base + hdrStage) = 0
            · simp only [hst0, ↓reduceIte] at hne ⊢; rw [ite_eq_right hne]; exact Or.inl rfl
            · simp only [hst0, ↓reduceIte]; exact Or.inr rfl)
          (fun _ => ⟨hmbHost_192, hibHi_192⟩)
          (fun h => absurd h Nat.one_ne_zero) (fun h => absurd h Nat.one_ne_zero) _ ha
        exact absurd (hb.2.1 (by dsimp only [hdrPhase]; omega)).2.1 Nat.one_ne_zero
    have hno_d : ¬slotOwnsAddr c w mbDst L₂.slotDst.nCap (pagedSlotIo 1 pgH_al) (base + hdrPhase) :=
      hnc_d_eq ▸ fun ha => by
        have hb := slotOwnsAddr_bounds (pBase := pDst)
          (fun h0 => by rcases hpos_d₁ with ⟨_, h⟩ | ⟨hne, _⟩ <;> [exact h; exact absurd h0 hne])
          (fun hne => by
            rw [hcap_d₁] at hne; unfold mbDst dualMbDst
            rw [ite_eq_left (by omega : s₁.mem (base + hdrPhase) < 10), ite_eq_right hne]
            split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl])
          (fun _ => ⟨hmbHost_192, hibHi_192⟩)
          (fun h => absurd h Nat.one_ne_zero) (fun h => absurd h Nat.one_ne_zero) _ ha
        exact absurd (hb.2.1 (by dsimp only [hdrPhase]; omega)).2.1 Nat.one_ne_zero
    exact (hmut₂.2.2.2.2.2.2.2.2.1 _ hno_s hno_d).trans hsg₂_ph
  have hsync₁ := syncLive_mem_eq_of_ne3_10 (v_val := v_val) h₁ hop_nz u v hv_eq
    (by omega) (by omega)
  have hsync₂ := syncLive_mem_eq_of_ne3_10 (v_val := v_val) h₂ hop_nz u v hv_eq
    (by omega) (by omega)
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hsync₁ hsync₂
  rw [← hsp₁, ← hkg₁, ← hsr₁, ← hsm₁] at hsync₁
  rw [← hsp₂, ← hkg₂, ← hsr₂, ← hsm₂] at hsync₂
  have hsm₁_eq := hsync₁ (hsr₁_ph.trans hp8.symm)
  have hsm₂_eq := hsync₂ (hsr₂_ph.trans hp8_₂.symm)
  have hhdr_m₁ : ∀ off < 48, off ≠ hdrLive → off ≠ hdrSplit →
      sm₁.mem (base + off) = s₁.mem (base + off) :=
    fun off hoff h1 h2 => hstep₁.2.2.2.1 (base + off) (by omega) (base_add_ne h1) (base_add_ne h2)
  have hreg_m₁ : Coupled8Region c w base sm₁.mem = Coupled8Region c w base s₁.mem :=
    coupled8Region_of_hdr_eq
      (hhdr_m₁ hdrStage (by decide) (by decide) (by decide))
      (hhdr_m₁ hdrNSrc (by decide) (by decide) (by decide))
      (hhdr_m₁ hdrNDst (by decide) (by decide) (by decide))
      (hhdr_m₁ hdrPad (by decide) (by decide) (by decide))
  have hpgH_m₁ : dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem =
      hostPageLayout c w (dualNHost base s₁.mem) (dualMbHost base s₁.mem)
        (s₁.mem (base + hdrItemHi)) (s₁.mem (base + hdrQHi)) (valBits V)
        (Dictionary.dom s_dict').card := by
    unfold dualPgHost dualNHost dualMbHost
    rw [hhdr_m₁ hdrNDst (by decide) (by decide) (by decide),
      hhdr_m₁ hdrNSrc (by decide) (by decide) (by decide),
      hhdr_m₁ hdrStage (by decide) (by decide) (by decide),
      hhdr_m₁ hdrPad (by decide) (by decide) (by decide),
      hhdr_m₁ hdrItemHi (by decide) (by decide) (by decide),
      hhdr_m₁ hdrQHi (by decide) (by decide) (by decide)]
  have hmbS_m₁ : dualMbSrc base sm₁.mem = mbSrc := by
    unfold dualMbSrc mbSrc
    rw [hhdr_m₁ hdrStage (by decide) (by decide) (by decide),
      hhdr_m₁ hdrNSrc (by decide) (by decide) (by decide),
      hhdr_m₁ hdrPad (by decide) (by decide) (by decide)]
  have hmbS_m₂ : dualMbSrc base sm₂.mem = mbSrc := by
    unfold dualMbSrc
    rw [← hsch_mid.2 hdrStage (by decide) (by decide),
      ← hsch_mid.2 hdrNSrc (by decide) (by decide),
      ← hsch_mid.2 hdrPad (by decide) (by decide)]
    exact hmbS_m₁
  have hsl_sm₁ := (hstep₁.2.2.2.2.2.2.2.2.2.2.2.1 hp8).2.2.2.2.2.1
  have hsl_sm₂ := (hstep₂.2.2.2.2.2.2.2.2.2.2.2.1 hp8_₂).2.2.2.2.2.1
  have hpgH_m₂ : dualPgHost c V w base (Dictionary.dom s_dict').card sm₂.mem =
      dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem := by
    unfold dualPgHost dualNHost dualMbHost
    rw [← hsch_mid.2 hdrNDst (by decide) (by decide),
      ← hsch_mid.2 hdrNSrc (by decide) (by decide),
      ← hsch_mid.2 hdrStage (by decide) (by decide),
      ← hsch_mid.2 hdrPad (by decide) (by decide),
      ← hsch_mid.2 hdrItemHi (by decide) (by decide),
      ← hsch_mid.2 hdrQHi (by decide) (by decide)]
  have hpS_m₁ : (if s₁.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1) =
      dualPSrc base sm₁.mem := by
    unfold dualPSrc; rw [hhdr_m₁ hdrStage (by decide) (by decide) (by decide)]
  have hpS_m₂ : (if s₂.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1) =
      dualPSrc base sm₁.mem := by
    unfold dualPSrc
    rw [← hsch.2 hdrStage (by decide) (by decide),
      hhdr_m₁ hdrStage (by decide) (by decide) (by decide)]
  have hmbS_s₁_eq : (if s₁.mem (base + hdrStage) = 0 then
        if s₁.mem (base + hdrNSrc) = 0 then base + hdrSmallMeta0 else base + 192
      else base + 192 + s₁.mem (base + hdrPad)) = mbSrc := rfl
  have hmbS_s₂_eq : (if s₂.mem (base + hdrStage) = 0 then
        if s₂.mem (base + hdrNSrc) = 0 then base + hdrSmallMeta0 else base + 192
      else base + 192 + s₂.mem (base + hdrPad)) = mbSrc := hmbS_eq₂
  have hpgH_s₁_eq : hostPageLayout c w
      (if s₁.mem (base + hdrNDst) = 0 then s₁.mem (base + hdrNSrc) else s₁.mem (base + hdrNDst))
      (if s₁.mem (base + hdrNDst) = 0 then base + 192
       else if s₁.mem (base + hdrStage) = 0 then base + 192 + s₁.mem (base + hdrPad)
       else base + 192)
      (s₁.mem (base + hdrItemHi)) (s₁.mem (base + hdrQHi)) (valBits V)
      (Dictionary.dom s_dict').card =
      dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem := hpgH_m₁.symm
  have hpgH_s₂_eq : hostPageLayout c w
      (if s₂.mem (base + hdrNDst) = 0 then s₂.mem (base + hdrNSrc) else s₂.mem (base + hdrNDst))
      (if s₂.mem (base + hdrNDst) = 0 then base + 192
       else if s₂.mem (base + hdrStage) = 0 then base + 192 + s₂.mem (base + hdrPad)
       else base + 192)
      (s₂.mem (base + hdrItemHi)) (s₂.mem (base + hdrQHi)) (valBits V)
      (Dictionary.dom s_dict').card =
      dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem := by
    rw [← hsch.2 hdrNDst (by decide) (by decide),
      ← hsch.2 hdrNSrc (by decide) (by decide),
      ← hsch.2 hdrStage (by decide) (by decide),
      ← hsch.2 hdrPad (by decide) (by decide),
      ← hsch.2 hdrItemHi (by decide) (by decide),
      ← hsch.2 hdrQHi (by decide) (by decide)]
    exact hpgH_m₁.symm
  rw [hpS_m₁, hmbS_s₁_eq, hpgH_s₁_eq] at hsl_sm₁
  rw [hpS_m₂, hmbS_s₂_eq, hpgH_s₂_eq] at hsl_sm₂
  have hsm_mem_eq : ∀ addr, Coupled8Region c w base sm₁.mem addr → sm₁.mem addr = sm₂.mem addr := by
    rw [hreg_m₁]; intro addr hreg
    rw [hsm₁_eq, hsm₂_eq]; dsimp only [Memory.State.mem]
    by_cases h1 : addr = base + hdrPBase1 + 60
    · subst h1; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne h1, Function.update_of_ne h1]
      by_cases h0 : addr = base + hdrPBase0 + 60
      · subst h0; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h0, Function.update_of_ne h0]
        by_cases hl : addr = base + hdrLive
        · subst hl; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hl, Function.update_of_ne hl]
          exact hc_raw.mem_eq addr hreg
  have hsm_io_out : ∀ {sr sm : Memory.State},
      (sm.mem = Function.update
        (Function.update (Function.update sr.mem (base + hdrLive) (Dictionary.dom s_dict').card)
          (base + hdrPBase0 + 60) (Dictionary.dom s_dict').card)
        (base + hdrPBase1 + 60) (Dictionary.dom s_dict').card) →
      ∀ addr, (pagedSlotIo 0 pgH_al).OwnsAddr addr → sm.mem addr = sr.mem addr := by
    intro sr sm heq addr hia
    have hge192 : base + 192 ≤ addr := by
      rcases hia with hm | hi
      · have h1 : pgH.metaBase ≤ addr := by
          rcases hm with h | h | h <;> exact le_trans (Nat.le_add_right _ _) h.1
        clear *- hmbHost_192 h1; omega
      · have h1 : pgH.itemBase ≤ addr := hi.1
        clear *- hibHi_192 h1; omega
    rw [heq]
    rw [Function.update_of_ne (by dsimp only [hdrPBase1]; clear *- hge192; omega),
      Function.update_of_ne (by dsimp only [hdrPBase0]; clear *- hge192; omega),
      Function.update_of_ne (by dsimp only [hdrLive]; clear *- hge192; omega)]
  have hns_sm₁ : sm₁.mem (mbSrc + 1) = sr₁.mem (mbSrc + 1) := by
    have hmb_ne : mbSrc + 1 ≠ base + hdrLive ∧ mbSrc + 1 ≠ base + hdrPBase0 + 60 ∧
        mbSrc + 1 ≠ base + hdrPBase1 + 60 := by
      unfold mbSrc dualMbSrc; dsimp only [hdrLive, hdrSmallMeta0, hdrPBase0, hdrPBase1]
      split_ifs <;> (clear *-; exact ⟨by omega, by omega, by omega⟩)
    rw [hsm₁_eq]; dsimp only [Memory.State.mem]
    rw [Function.update_of_ne hmb_ne.2.2, Function.update_of_ne hmb_ne.2.1,
      Function.update_of_ne hmb_ne.1]
  have hns_sm₂ : sm₂.mem (mbSrc + 1) = sm₁.mem (mbSrc + 1) :=
    (hsm_mem_eq (mbSrc + 1) (hreg_m₁.symm ▸ hmb1_in_c8)).symm
  refine ⟨hkg_eq, hsch_mid, ?_⟩
  rw [hmbS_m₁]
  exact
    { fr_eq := hsch_mid.1
      side_zero := rfl
      valid₁ := by
        have hv := hsl_sm₁.io_valid
        have hw_pg : (pagedSlotIo 0
          (dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem)).pgL.w = w := rfl
        rwa [hw_pg]
      disj := fun addr hreg => by
        have hcap_sm₁ := (hstep₁.2.2.2.2.2.2.2.2.2.2.2.1 hp8).1
        have hcap_eq : dualCapSrc base sm₁.mem =
            (if s₁.mem (base + hdrStage) = 0 then s₁.mem (base + hdrNSrc)
             else s₁.mem (base + hdrNDst)) := by
          unfold dualCapSrc
          rw [hhdr_m₁ hdrStage (by decide) (by decide) (by decide),
            hhdr_m₁ hdrNSrc (by decide) (by decide) (by decide),
            hhdr_m₁ hdrNDst (by decide) (by decide) (by decide)]
        have hraw := hsl_sm₁; unfold EpochSlotInv at hraw
        rcases hreg with ⟨h1, h2⟩ | hmeta
        · by_cases hc0 : (L₁.applyFG (s₁.mem (base + hdrPhase)) opTag u v).slotSrc.nCap = 0
          · rw [ite_eq_left hc0] at hraw
            exact fun hia => hraw.2.2.2.2.1 addr h1 h2 (Or.inr (Or.inr hia))
          · rw [ite_eq_right hc0] at hraw; exact hraw.1.disj_pBase_io addr h1 h2
        · rw [hcap_eq, ← hcap_sm₁, hmbS_m₁] at hmeta; unfold slotOwnsNonPageMeta at hmeta
          by_cases hc0 : (L₁.applyFG (s₁.mem (base + hdrPhase)) opTag u v).slotSrc.nCap = 0
          · rw [ite_eq_left hc0] at hraw hmeta
            rcases hmeta with ⟨g1, g2⟩ | ⟨hne, _⟩
            · exact hraw.2.2.1.disjoint_hdr addr (by dsimp only; clear *- g1 g2; omega)
            · exact absurd hc0 hne
          · rw [ite_eq_right hc0] at hraw hmeta
            exact hraw.1.disj_fast_io addr (hmeta.imp id And.right)
      mem_eq := hsm_mem_eq
      inv₁ := hsl_sm₁.io_stateInv
      inv₂ := hns_sm₂ ▸ hsl_sm₂.io_stateInv
      pair_eq := fun idx hidx => by
        have hidx0 : idx < sr₁.mem (mbSrc + 1) := hns_sm₁ ▸ hidx
        have hp1 := ((pagedSlotIo 0 pgH_al).congr_of_outside hw_pos hc_raw.inv₁
          (hsm_io_out (congrArg Memory.State.mem hsm₁_eq))).2 idx hidx0
        have hp2 := ((pagedSlotIo 0 pgH_al).congr_of_outside hw_pos hc_raw.inv₂
          (hsm_io_out (congrArg Memory.State.mem hsm₂_eq))).2 idx hidx0
        rw [hpgH_m₁]
        exact hp1.trans ((hc_raw.pair_eq idx hidx0).trans hp2.symm) }

/-! ## Section 4: Post-Tick `8 → 8` and `8 → 9` Coupling and `coupled8_mutate_step` -/

private theorem coupled8_tick_step_aux {c U V w base opTag k_sh : ℕ}
    {s_dict' : Dictionary.State U}
    {Lm₁ Lm₂ Lp_any₁ Lp_any₂ : DualLatent c U V}
    {sm₁ sm₂ st₁ st₂ sps₁ sps₂ s_post₁ s_post₂ : Memory.State}
    {s_src1 s_dst1 : Fin U → Option (Fin V)} {ex1 : List (EpochUpdate U V)}
    (hop_nz : opTag ≠ 0)
    (hp8₁ : sm₁.mem (base + hdrPhase) = 8)
    (hc8_mid : Coupled8 c V w base (Dictionary.dom s_dict').card sm₁ sm₂)
    (hmid₁ : DualMidInv c U V w base s_dict' Lm₁ sm₁)
    (hmid₂ : DualMidInv c U V w base s_dict' Lm₂ sm₂)
    (hsrc_eq : Lm₂.slotSrc = Lm₁.slotSrc)
    (hdst_abs_eq : Lm₂.slotDst.s_abs = Lm₁.slotDst.s_abs)
    (hdst_evs_eq : Lm₂.slotDst.evs = Lm₁.slotDst.evs)
    (hcd1 : (liveDom s_src1).card = (liveDom Lm₁.slotSrc.s_abs).card - itemBatchWhp)
    (hsum1 : (Lm₁.slotDst.evs ++ ex1).length + (liveDom s_src1).card =
      Lm₁.slotDst.evs.length + (liveDom Lm₁.slotSrc.s_abs).card)
    (hdj1 : DisjointOpt s_dst1 s_src1)
    (hor1 : orOpt s_dst1 s_src1 = orOpt Lm₁.slotDst.s_abs Lm₁.slotSrc.s_abs)
    (hs1_₂ : EpochSlotInv c U V w
      ((Memory.spec 0).clientState sm₂
        (migrateBatchProg (((dualPSrc base sm₁.mem,
          if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0), 0),
          itemBatchWhp))).frontier
      (dualPSrc base sm₁.mem) (dualMbSrc base sm₁.mem)
      (pagedSlotIo 0 (dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem)) 0 true
      ⟨Lm₁.slotSrc.nCap, s_src1, Lm₁.slotSrc.seeds, Lm₁.slotSrc.evs⟩
      ((Memory.spec 0).clientState sm₂
        (migrateBatchProg (((dualPSrc base sm₁.mem,
          if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0), 0),
          itemBatchWhp))).mem)
    (hd1_₂ : EpochSlotInv c U V w
      ((Memory.spec 0).clientState sm₂
        (migrateBatchProg (((dualPSrc base sm₁.mem,
          if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0), 0),
          itemBatchWhp))).frontier
      (if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0)
      (dualMbDst base sm₁.mem)
      (pagedSlotIo 1 (dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem)) 0 false
      ⟨Lm₂.slotDst.nCap, s_dst1, Lm₂.slotDst.seeds, Lm₂.slotDst.evs ++ ex1⟩
      ((Memory.spec 0).clientState sm₂
        (migrateBatchProg (((dualPSrc base sm₁.mem,
          if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0), 0),
          itemBatchWhp))).mem)
    (hc_s1 :
      let mb := migrateBatchProg (((dualPSrc base sm₁.mem,
        if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0), 0),
        itemBatchWhp)
      let s1₁ := (Memory.spec 0).clientState sm₁ mb
      let s1₂ := (Memory.spec 0).clientState sm₂ mb
      SlotStateCoupled (Coupled8Region c w base sm₁.mem)
        (pagedSlotIo 0 (dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem))
        (s1₁.mem (dualMbSrc base sm₁.mem + 1)) s1₁ s1₂)
    (hfr_s1_₁ :
      ((Memory.spec 0).clientState sm₁
        (migrateBatchProg (((dualPSrc base sm₁.mem,
          if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0), 0),
          itemBatchWhp))).frontier = sm₁.frontier)
    (hout_s1_₁ : ∀ addr,
      ¬slotOwnsAddr c w (dualMbSrc base sm₁.mem) Lm₁.slotSrc.nCap
        (pagedSlotIo 0 (dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem)) addr →
      ¬slotOwnsAddr c w (dualMbDst base sm₁.mem) Lm₁.slotDst.nCap
        (pagedSlotIo 1 (dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem)) addr →
      ((Memory.spec 0).clientState sm₁
        (migrateBatchProg (((dualPSrc base sm₁.mem,
          if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0), 0),
          itemBatchWhp))).mem addr = sm₁.mem addr)
    (hfr_s1_₂ :
      ((Memory.spec 0).clientState sm₂
        (migrateBatchProg (((dualPSrc base sm₁.mem,
          if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0), 0),
          itemBatchWhp))).frontier = sm₂.frontier)
    (hout_s1_₂ : ∀ addr,
      ¬slotOwnsAddr c w (dualMbSrc base sm₁.mem) Lm₁.slotSrc.nCap
        (pagedSlotIo 0 (dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem)) addr →
      ¬slotOwnsAddr c w (dualMbDst base sm₁.mem) Lm₂.slotDst.nCap
        (pagedSlotIo 1 (dualPgHost c V w base (Dictionary.dom s_dict').card sm₁.mem)) addr →
      ((Memory.spec 0).clientState sm₂
        (migrateBatchProg (((dualPSrc base sm₁.mem,
          if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0), 0),
          itemBatchWhp))).mem addr = sm₂.mem addr)
    (hmc_mb_₂ :
      (Lm₂.slotDst.nCap = 0 →
        (liveDom Lm₂.slotDst.s_abs).card + (liveDom Lm₁.slotSrc.s_abs).card ≤
          2 * whpThreshold c) →
      Lm₁.slotSrc.GoodCovers →
      (⟨Lm₂.slotDst.nCap, s_dst1, Lm₂.slotDst.seeds, Lm₂.slotDst.evs ++ ex1⟩ :
        SlotLatent c U V).GoodCovers →
      memoryCost (migrateBatchProg (((dualPSrc base sm₁.mem,
        if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0), 0),
        itemBatchWhp)) sm₂ ≤ itemBatchWhp * (2 * epochStepCost c + 2))
    (hst₁_bg : st₁ = (Memory.spec 0).clientState sm₁ (bgTickProg (base, sm₁.frontier)))
    (hst₂_bg : st₂ = (Memory.spec 0).clientState sm₂ (bgTickProg (base, sm₂.frontier)))
    (hsps₁_id : sps₁ = st₁)
    (hsps₂_id : sps₂ = st₂)
    (hpost₁_def : s_post₁ = { mem := clear sps₁.mem (st₁.frontier - k_sh) k_sh,
                              frontier := st₁.frontier - k_sh })
    (hpost₂_def : s_post₂ = { mem := clear sps₂.mem (st₂.frontier - k_sh) k_sh,
                              frontier := st₂.frontier - k_sh })
    (hsch_post : SchedEq base s_post₁ s_post₂)
    (h_any₁ : DualStateInv c U V w base s_dict' Lp_any₁ s_post₁)
    (h_any₂ : DualStateInv c U V w base s_dict' Lp_any₂ s_post₂) :
    let slSrc_p : SlotLatent c U V :=
      ⟨Lm₁.slotSrc.nCap, s_src1, Lm₁.slotSrc.seeds, Lm₁.slotSrc.evs⟩
    let slDst_p₂ : SlotLatent c U V :=
      ⟨Lm₂.slotDst.nCap, s_dst1, Lm₂.slotDst.seeds, Lm₁.slotDst.evs ++ ex1⟩
    (∃ L_post₂ : DualLatent c U V,
      L_post₂.slotSrc = slSrc_p ∧
      L_post₂.slotDst = slDst_p₂ ∧
      DualStateInv c U V w base s_dict' L_post₂ s_post₂ ∧
      (Lm₁.slotSrc.GoodCovers → slDst_p₂.GoodCovers →
        memoryCost (bgTickProg (base, sm₂.frontier)) sm₂ ≤
          itemBatchWhp * (2 * epochStepCost c + 20) + 20000)) ∧
    ((s_post₁.mem (base + hdrPhase) = 8 ∧
        Coupled8 c V w base (Dictionary.dom s_dict').card s_post₁ s_post₂) ∨
     (s_post₁.mem (base + hdrPhase) = 9 ∧ SchedEq base s_post₁ s_post₂)) := by
  intro slSrc_p slDst_p₂
  have _ := hop_nz; have _ := hsrc_eq
  have hp8₂ : sm₂.mem (base + hdrPhase) = 8 :=
    (hc8_mid.1.2 hdrPhase (by decide) (by decide)).symm.trans hp8₁
  have hw_pos : 0 < w := by have := hmid₁.hw11; omega
  set nLive := (Dictionary.dom s_dict').card
  set stg := sm₁.mem (base + hdrStage)
  set pSrc := dualPSrc base sm₁.mem
  set pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
  set pgH := dualPgHost c V w base nLive sm₁.mem
  set mb := migrateBatchProg (((pSrc, pDst), 0), itemBatchWhp)
  set s1₁ := (Memory.spec 0).clientState sm₁ mb
  set s1₂ := (Memory.spec 0).clientState sm₂ mb
  obtain ⟨hth_h₁, _, _, hmb_ib₁, hctx0_₁, _, hv_hi₁, hv_fr₁, _⟩ :=
    dualPgHost_eval_valid hmid₁ (by omega) (by omega)
  obtain ⟨_, _, _, _, hctx0_₂, _, _, hv_fr₂, _⟩ :=
    dualPgHost_eval_valid hmid₂ (by omega) (by omega)
  have hdisj_pg₁ := disjoint_pgHost_nonPageMeta (nc := nLive) hmid₁ (by omega) (by omega)
  have hpgH_m₂ : dualPgHost c V w base nLive sm₂.mem = pgH := by
    dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
    rw [← hc8_mid.1.2 hdrNDst (by decide) (by decide),
      ← hc8_mid.1.2 hdrNSrc (by decide) (by decide),
      ← hc8_mid.1.2 hdrStage (by decide) (by decide),
      ← hc8_mid.1.2 hdrPad (by decide) (by decide),
      ← hc8_mid.1.2 hdrItemHi (by decide) (by decide),
      ← hc8_mid.1.2 hdrQHi (by decide) (by decide)]
  rw [hpgH_m₂] at hctx0_₂ hv_fr₂
  have hh_ofCtx : PageArenaLayout.ofCtx pgH.toCtx = pgH := PageArenaLayout.ofCtx_toCtx pgH
  have hsched₁ := hmid₁.sched; rw [ite_eq_right (by omega)] at hsched₁
  have hsched₂ := hmid₂.sched; rw [ite_eq_right (by omega)] at hsched₂
  obtain ⟨hmDst_eq₁, hpad_eq₁, _, _, hibHi_eq₁, _⟩ := hsched₁.ge2 (by omega)
  obtain ⟨hrem_ge1, hrem_le₁, hcard_rem⟩ := hmid₁.ph8_inv hp8₁
  obtain ⟨hcap_s₁, hcap_d₁, hdj_m₁, hdict_or₁, _, _, _, hevs_s₁, _⟩ := hmid₁.sl_8 hp8₁
  obtain ⟨_, hcap_d₂, _, _, _, _, _, _, hevs_d₂⟩ := hmid₂.sl_8 hp8₂
  obtain ⟨_, hdst_safe₂⟩ := dualCoreInv_cap_safe hmid₂
  rw [ite_eq_right (by omega)] at hdst_safe₂
  have hnc_d_eq : Lm₂.slotDst.nCap = Lm₁.slotDst.nCap := by
    rw [hcap_d₂, hcap_d₁, hc8_mid.1.2 hdrNDst (by decide) (by decide)]
  have hibHi_ge : base + 196 ≤ sm₁.mem (base + hdrItemHi) := by
    rw [hibHi_eq₁]; split_ifs <;> omega
  have hmb_ge192 : base + 192 ≤ pgH.metaBase := by
    change base + 192 ≤ dualMbHost base sm₁.mem; unfold dualMbHost; split_ifs <;> omega
  have hown_pg_ge : ∀ a, pgH.OwnsAddr a → base + 192 ≤ a := fun a ha => by
    rcases ha with hm | hi
    · have := (hdisj_pg₁ a hm).1; omega
    · have hi1 : sm₁.mem (base + hdrItemHi) ≤ a := hi.1
      clear *- hi1 hibHi_ge; omega
  have hs1_no_s : ∀ addr, (addr < base + 48 ∨ (base + 64 ≤ addr ∧ addr < base + 192)) →
      ¬slotOwnsAddr c w (dualMbSrc base sm₁.mem) Lm₁.slotSrc.nCap (pagedSlotIo 0 pgH) addr := by
    intro addr hrng hown
    have hb := slotOwnsAddr_bounds (pBase := pSrc)
      (fun h0 => by
        rw [hcap_s₁] at h0; unfold dualMbSrc dualCapSrc at *
        by_cases hst0 : stg = 0
        · simp only [show sm₁.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at h0 ⊢
          rw [ite_eq_left h0]; exact Or.inl rfl
        · simp only [show sm₁.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at h0
          exact absurd h0 (fun hd0 => hst0 (hsched₁.nDst_zero hd0).2.1))
      (fun hne => by
        rw [hcap_s₁] at hne; unfold dualMbSrc dualCapSrc at *
        by_cases hst0 : stg = 0
        · simp only [show sm₁.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at hne ⊢
          rw [ite_eq_right hne]; exact Or.inl rfl
        · simp only [show sm₁.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
          exact Or.inr rfl)
      (fun _ => ⟨hmb_ge192, by change base + 192 ≤ sm₁.mem (base + hdrItemHi); omega⟩)
      (fun h0 => absurd h0 Nat.one_ne_zero)
      (fun h0 => absurd h0 Nat.one_ne_zero) addr hown
    rcases hrng with hlt48 | h64
    · exact absurd (hb.2.1 hlt48).2.1 Nat.one_ne_zero
    · exact hb.2.2 h64
  have hs1_no_d₁ : ∀ addr, (addr < base + 48 ∨ (base + 64 ≤ addr ∧ addr < base + 192)) →
      ¬slotOwnsAddr c w (dualMbDst base sm₁.mem) Lm₁.slotDst.nCap (pagedSlotIo 1 pgH) addr := by
    intro addr hrng hown
    have hb := slotOwnsAddr_bounds (pBase := pDst)
      (fun h0 => by
        rw [hcap_d₁] at h0; unfold dualMbDst
        rw [ite_eq_left (by omega : sm₁.mem (base + hdrPhase) < 10), ite_eq_left h0]
        exact Or.inr rfl)
      (fun hne => by
        rw [hcap_d₁] at hne; unfold dualMbDst
        rw [ite_eq_left (by omega : sm₁.mem (base + hdrPhase) < 10), ite_eq_right hne]
        split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl])
      (fun _ => ⟨hmb_ge192, by change base + 192 ≤ sm₁.mem (base + hdrItemHi); omega⟩)
      (fun h0 => absurd h0 Nat.one_ne_zero)
      (fun h0 => absurd h0 Nat.one_ne_zero) addr hown
    rcases hrng with hlt48 | h64
    · exact absurd (hb.2.1 hlt48).2.1 Nat.one_ne_zero
    · exact hb.2.2 h64
  have hs1₁_hdr48 : ∀ off < 48, s1₁.mem (base + off) = sm₁.mem (base + off) := fun off h48 =>
    hout_s1_₁ (base + off) (hs1_no_s _ (Or.inl (by omega))) (hs1_no_d₁ _ (Or.inl (by omega)))
  have hs1₂_hdr48 : ∀ off < 48, s1₂.mem (base + off) = sm₂.mem (base + off) := fun off h48 =>
    hout_s1_₂ (base + off) (hs1_no_s _ (Or.inl (by omega)))
      (hnc_d_eq ▸ hs1_no_d₁ _ (Or.inl (by omega)))
  have hctx0_s1₁ : (Memory.spec 0).clientResult s1₁ (loadHostCtxProg (base, 0)) = pgH.toCtx := by
    rw [← hctx0_₁, (loadHostCtxProg_eval base 0 s1₁).2.1, (loadHostCtxProg_eval base 0 sm₁).2.1]
    simp only [↓reduceIte]
    have h_od : ∀ k ≤ 4,
        s1₁.mem (base +
          (if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) =
        sm₁.mem (base +
          (if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) :=
      fun k hk => by
        rw [Nat.add_assoc]
        exact hs1₁_hdr48 _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> omega)
    rw [hs1₁_hdr48 hdrStage (by decide), hs1₁_hdr48 hdrNDst (by decide),
      hs1₁_hdr48 hdrPad (by decide), hs1₁_hdr48 hdrW (by decide),
      hs1₁_hdr48 hdrItemHi (by decide), hs1₁_hdr48 hdrQHi (by decide),
      hs1₁_hdr48 hdrValBits (by decide), hs1₁_hdr48 hdrLive (by decide),
      show s1₁.mem (base + if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) =
        sm₁.mem (base + if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) by
        simpa only [Nat.add_zero] using h_od 0 (by decide),
      h_od 1 (by decide), h_od 2 (by decide), h_od 3 (by decide), h_od 4 (by decide)]
  have hctx0_s1₂ : (Memory.spec 0).clientResult s1₂ (loadHostCtxProg (base, 0)) = pgH.toCtx := by
    rw [← hctx0_₂, (loadHostCtxProg_eval base 0 s1₂).2.1, (loadHostCtxProg_eval base 0 sm₂).2.1]
    simp only [↓reduceIte]
    have h_od : ∀ k ≤ 4,
        s1₂.mem (base +
          (if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) =
        sm₂.mem (base +
          (if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) :=
      fun k hk => by
        rw [Nat.add_assoc]
        exact hs1₂_hdr48 _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> omega)
    rw [hs1₂_hdr48 hdrStage (by decide), hs1₂_hdr48 hdrNDst (by decide),
      hs1₂_hdr48 hdrPad (by decide), hs1₂_hdr48 hdrW (by decide),
      hs1₂_hdr48 hdrItemHi (by decide), hs1₂_hdr48 hdrQHi (by decide),
      hs1₂_hdr48 hdrValBits (by decide), hs1₂_hdr48 hdrLive (by decide),
      show s1₂.mem (base + if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) =
        sm₂.mem (base + if sm₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) by
        simpa only [Nat.add_zero] using h_od 0 (by decide),
      h_od 1 (by decide), h_od 2 (by decide), h_od 3 (by decide), h_od 4 (by decide)]
  have hth_U : whpThreshold c ≤ U := hth_h₁.1.trans hth_h₁.2
  have hth_hdr₁ : sm₁.mem (base + hdrThresh) = whpThreshold c := by
    simpa only [hth_U, ↓reduceIte] using hmid₁.hdr.2.2.2.2.2.1
  have hth_hdr₂ : sm₂.mem (base + hdrThresh) = whpThreshold c := by
    simpa only [hth_U, ↓reduceIte] using hmid₂.hdr.2.2.2.2.2.1
  have hbgev₁ := bgTickProg_eval base sm₁.frontier sm₁
  have hbgev₂ := bgTickProg_eval base sm₂.frontier sm₂
  simp only [hp8₁, hp8₂, Nat.reduceEqDiff, ↓reduceIte] at hbgev₁ hbgev₂
  have htmev₁ := tickMigrateProg_eval base sm₁
  have htmev₂ := tickMigrateProg_eval base sm₂
  change _ ∧ _ at htmev₁ htmev₂
  have hpS_sm₂ : (if sm₂.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1) =
      pSrc := by unfold pSrc dualPSrc; rw [hc8_mid.1.2 hdrStage (by decide) (by decide)]
  have hpD_sm₂ : (if sm₂.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
      pDst := by simp only [pDst, stg, hc8_mid.1.2 hdrStage (by decide) (by decide)]
  rw [show (if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1) =
      pSrc from rfl,
    show (if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
      pDst from rfl,
    show (Memory.spec 0).clientState sm₁ mb = s1₁ from rfl,
    hctx0_s1₁, hh_ofCtx, hth_hdr₁] at htmev₁
  rw [hpS_sm₂, hpD_sm₂, show (Memory.spec 0).clientState sm₂ mb = s1₂ from rfl,
    hctx0_s1₂, hh_ofCtx, hth_hdr₂] at htmev₂
  set rem := sm₁.mem (base + hdrRem)
  have hrem_sm₂ : sm₂.mem (base + hdrRem) = rem :=
    (hc8_mid.1.2 hdrRem (by decide) (by decide)).symm
  rw [hrem_sm₂, ← hc8_mid.1.2 hdrNSrc (by decide) (by decide)] at htmev₂
  have hd_sm_bound : Lm₂.slotDst.nCap = 0 →
      (liveDom Lm₂.slotDst.s_abs).card + (liveDom Lm₁.slotSrc.s_abs).card ≤ 2 * whpThreshold c :=
    fun h0 => by
      have hd0 : sm₂.mem (base + hdrNDst) = 0 := hcap_d₂ ▸ h0
      unfold EpochCapSafe at hdst_safe₂; rw [ite_eq_left hd0] at hdst_safe₂
      have hsum : (liveDom Lm₂.slotDst.s_abs).card + (liveDom Lm₁.slotSrc.s_abs).card = nLive := by
        rw [hdst_abs_eq, ← liveDom_orOpt_card hdj_m₁, ← dom_toDictState_card, hdict_or₁]
      rw [hsum]; exact hdst_safe₂.1.le
  set hiFr := sm₁.mem (base + hdrItemHi) +
    pairStreamWords nLive (sm₁.mem (base + hdrQHi)) (valBits V) w
  have hb192_p₁ : base + 192 ≤ st₁.frontier - k_sh := by
    have hb := h_any₁.base_fr; rw [hpost₁_def] at hb; exact hb
  have hb192_p₂ : base + 192 ≤ st₂.frontier - k_sh := by
    have hb := h_any₂.base_fr; rw [hpost₂_def] at hb; exact hb
  have hmS_pad : sm₁.mem (base + hdrMSrc) ≤ sm₁.mem (base + hdrPad) := by
    rw [hpad_eq₁]; exact le_max_left _ _
  have hmD_pad : sm₁.mem (base + hdrMDst) ≤ sm₁.mem (base + hdrPad) := by
    rw [hpad_eq₁]; exact le_max_right _ _
  have hpS_rng : base + 64 ≤ pSrc ∧ pSrc + 64 ≤ base + 192 := by
    unfold pSrc dualPSrc; dsimp only [hdrPBase0, hdrPBase1]
    split_ifs <;> (clear *-; exact ⟨by omega, by omega⟩)
  have hpD_rng : base + 64 ≤ pDst ∧ pDst + 64 ≤ base + 192 := by
    dsimp only [pDst, hdrPBase0, hdrPBase1]
    split_ifs <;> (clear *-; exact ⟨by omega, by omega⟩)
  -- Split on `1 < rem` (`8 → 8` vs `8 → 9`)
  by_cases h1 : 1 < rem
  · -- Branch `8 → 8`
    have hst₁_eq : st₁ =
        { mem := Function.update s1₁.mem (base + hdrRem) (rem - 1), frontier := s1₁.frontier } := by
      rw [hst₁_bg, hbgev₁.1, htmev₁.1, ite_eq_left h1]
    have hst₂_eq : st₂ =
        { mem := Function.update s1₂.mem (base + hdrRem) (rem - 1), frontier := s1₂.frontier } := by
      rw [hst₂_bg, hbgev₂.1, htmev₂.1, ite_eq_left h1]
    have hst_fr_eq : st₁.frontier = st₂.frontier := by
      rw [hst₁_eq, hst₂_eq]; exact hfr_s1_₁.trans (hc8_mid.1.1.trans hfr_s1_₂.symm)
    have hpost₁_hdr : ∀ off < 48, off ≠ hdrRem →
        s_post₁.mem (base + off) = sm₁.mem (base + off) := fun off hoff hne => by
      rw [hpost₁_def, hsps₁_id]; dsimp only [Memory.State.mem]
      rw [clear_of_not_owns (by simp only [Block.Owns]; clear *- hoff hb192_p₁; omega),
        hst₁_eq]; dsimp only [Memory.State.mem]
      rw [Function.update_of_ne (base_add_ne hne)]
      exact hs1₁_hdr48 off hoff
    have hpost₂_hdr : ∀ off < 48, off ≠ hdrRem → off ≠ hdrUnpermDone →
        s_post₂.mem (base + off) = sm₁.mem (base + off) := fun off hoff h1' h2' =>
      (hsch_post.2 off hoff h2').symm.trans (hpost₁_hdr off hoff h1')
    have hp8_p₁ : s_post₁.mem (base + hdrPhase) = 8 :=
      (hpost₁_hdr hdrPhase (by decide) (by decide)).trans hp8₁
    have hp8_p₂ : s_post₂.mem (base + hdrPhase) = 8 :=
      (hsch_post.2 hdrPhase (by decide) (by decide)).symm.trans hp8_p₁
    have hrem_p₂ : s_post₂.mem (base + hdrRem) = rem - 1 := by
      rw [hpost₂_def, hsps₂_id]; dsimp only [Memory.State.mem]
      rw [clear_of_not_owns
        (by simp only [Block.Owns]; dsimp only [hdrRem]; clear *- hb192_p₂; omega), hst₂_eq]
      exact Function.update_self ..
    have hfr_p₂_hi : s_post₂.frontier = hiFr := by
      have hsc := h_any₂.sched; rw [ite_eq_right (by rw [hp8_p₂]; decide)] at hsc
      obtain ⟨hlo, hhi⟩ := hsc.ph3_10 ⟨by rw [hp8_p₂]; decide, by rw [hp8_p₂]; decide⟩
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hhi
      rw [hpost₂_hdr hdrItemHi (by decide) (by decide) (by decide),
        hpost₂_hdr hdrQHi (by decide) (by decide) (by decide)] at hlo hhi
      dsimp only [hiFr, nLive] at hlo hhi ⊢; clear *- hlo hhi; omega
    have hfr_p₁_hi : s_post₁.frontier = hiFr := hsch_post.1.trans hfr_p₂_hi
    have hm_p₂_s1₂ : ∀ a, base + 48 ≤ a → a < hiFr → s_post₂.mem a = s1₂.mem a :=
      fun a h48 hlt => by
        have hfr_st : st₂.frontier - k_sh = hiFr := by
          have : s_post₂.frontier = st₂.frontier - k_sh := by rw [hpost₂_def]
          exact this.symm.trans hfr_p₂_hi
        rw [hpost₂_def, hsps₂_id]; dsimp only [Memory.State.mem]
        rw [clear_of_not_owns (by simp only [Block.Owns]; rw [hfr_st]; clear *- hlt; omega),
          hst₂_eq]; dsimp only [Memory.State.mem]
        exact Function.update_of_ne (by dsimp only [hdrRem]; clear *- h48; omega) _ _
    have hm_p₁_s1₁ : ∀ a, base + 48 ≤ a → a < hiFr → s_post₁.mem a = s1₁.mem a :=
      fun a h48 hlt => by
        have hfr_st : st₁.frontier - k_sh = hiFr := by
          have : s_post₁.frontier = st₁.frontier - k_sh := by rw [hpost₁_def]
          exact this.symm.trans hfr_p₁_hi
        rw [hpost₁_def, hsps₁_id]; dsimp only [Memory.State.mem]
        rw [clear_of_not_owns (by simp only [Block.Owns]; rw [hfr_st]; clear *- hlt; omega),
          hst₁_eq]; dsimp only [Memory.State.mem]
        exact Function.update_of_ne (by dsimp only [hdrRem]; clear *- h48; omega) _ _
    have hown_pg_lt_hi : ∀ a, pgH.OwnsAddr a → a < hiFr := fun a ha => by
      rcases ha with hm | hi
      · exact lt_of_lt_of_le (hdisj_pg₁ a hm).2.1 (Nat.le_add_right _ _)
      · exact hi.2
    have hpgH_p₁ : dualPgHost c V w base nLive s_post₁.mem = pgH := by
      dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
      rw [hpost₁_hdr hdrNDst (by decide) (by decide),
        hpost₁_hdr hdrNSrc (by decide) (by decide),
        hpost₁_hdr hdrStage (by decide) (by decide),
        hpost₁_hdr hdrPad (by decide) (by decide),
        hpost₁_hdr hdrItemHi (by decide) (by decide),
        hpost₁_hdr hdrQHi (by decide) (by decide)]
    have hpgH_p₂ : dualPgHost c V w base nLive s_post₂.mem = pgH := by
      dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
      rw [hpost₂_hdr hdrNDst (by decide) (by decide) (by decide),
        hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide),
        hpost₂_hdr hdrStage (by decide) (by decide) (by decide),
        hpost₂_hdr hdrPad (by decide) (by decide) (by decide),
        hpost₂_hdr hdrItemHi (by decide) (by decide) (by decide),
        hpost₂_hdr hdrQHi (by decide) (by decide) (by decide)]
    have hpS_p₂ : dualPSrc base s_post₂.mem = pSrc := by
      unfold dualPSrc pSrc; rw [hpost₂_hdr hdrStage (by decide) (by decide) (by decide)]
    have hmbS_p₂ : dualMbSrc base s_post₂.mem = dualMbSrc base sm₁.mem := by
      unfold dualMbSrc
      rw [hpost₂_hdr hdrStage (by decide) (by decide) (by decide),
        hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide),
        hpost₂_hdr hdrPad (by decide) (by decide) (by decide)]
    have hpD_p₂ : dualPDst base s_post₂.mem = pDst := by
      unfold dualPDst; rw [hp8_p₂, ite_eq_left (by decide : 8 < 10),
        hpost₂_hdr hdrStage (by decide) (by decide) (by decide)]
    have hmbD_p₂ : dualMbDst base s_post₂.mem = dualMbDst base sm₁.mem := by
      unfold dualMbDst
      simp only [hp8_p₂, hp8₁, Nat.reduceLT, ↓reduceIte]
      rw [hpost₂_hdr hdrNDst (by decide) (by decide) (by decide),
        hpost₂_hdr hdrStage (by decide) (by decide) (by decide),
        hpost₂_hdr hdrPad (by decide) (by decide) (by decide)]
    have hs_meta_b : ∀ a, slotOwnsNonPageMeta c w (dualMbSrc base sm₁.mem) Lm₁.slotSrc.nCap a →
        base + 48 ≤ a ∧ a < hiFr := fun a ha => by
      rw [hcap_s₁] at ha; unfold slotOwnsNonPageMeta dualMbSrc dualCapSrc at ha
      by_cases hst0 : stg = 0
      · simp only [show sm₁.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at ha
        by_cases hs0 : sm₁.mem (base + hdrNSrc) = 0
        · simp only [hs0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
            hdrSmallMeta0] at ha
          dsimp only [hiFr]; clear *- ha hibHi_ge; exact ⟨by omega, by omega⟩
        · have hth_s := (hmid₁.nSrc_bounds.resolve_left hs0).1
          have hod_s := (epochMeta_offsets_le (w := w) hth_s).2.2.2
          have h32_s : 32 ≤ offPageDir c w (sm₁.mem (base + hdrNSrc)) :=
            (epochMeta_offsets_le (w := w) hth_s).1.trans
              ((epochMeta_offsets_le (w := w) hth_s).2.1.trans
                (epochMeta_offsets_le (w := w) hth_s).2.2.1)
          rw [← hmid₁.mSrc_eq] at hod_s
          simp only [hs0, ↓reduceIte] at ha
          dsimp only [hiFr]; rw [hibHi_eq₁]
          rcases ha with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
            (split_ifs <;> (clear *- g1 g2 hod_s hmS_pad h32_s; exact ⟨by omega, by omega⟩))
      · have hd_nz : sm₁.mem (base + hdrNDst) ≠ 0 := fun hd0 => hst0 (hsched₁.nDst_zero hd0).2.1
        have hth_d := (hsched₁.nDst_bounds.resolve_left hd_nz).1
        have hod_d := (epochMeta_offsets_le (w := w) hth_d).2.2.2
        have h32_d : 32 ≤ offPageDir c w (sm₁.mem (base + hdrNDst)) :=
          (epochMeta_offsets_le (w := w) hth_d).1.trans
            ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
              (epochMeta_offsets_le (w := w) hth_d).2.2.1)
        rw [← hmDst_eq₁] at hod_d
        simp only [show sm₁.mem (base + hdrStage) = stg from rfl, hst0, hd_nz, ↓reduceIte] at ha
        dsimp only [hiFr]; rw [hibHi_eq₁, ite_eq_right hd_nz]
        rcases ha with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
          (clear *- g1 g2 hod_d hmD_pad h32_d; exact ⟨by omega, by omega⟩)
    have hd_meta_b : ∀ a, slotOwnsNonPageMeta c w (dualMbDst base sm₁.mem) Lm₂.slotDst.nCap a →
        base + 48 ≤ a ∧ a < hiFr := fun a ha => by
      rw [hnc_d_eq, hcap_d₁] at ha; unfold slotOwnsNonPageMeta dualMbDst at ha
      rw [hp8₁, ite_eq_left (by decide : 8 < 10)] at ha
      by_cases hd0 : sm₁.mem (base + hdrNDst) = 0
      · simp only [hd0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
          hdrSmallMeta1] at ha
        dsimp only [hiFr]; clear *- ha hibHi_ge; exact ⟨by omega, by omega⟩
      · have hth_d := (hsched₁.nDst_bounds.resolve_left hd0).1
        have hod_d := (epochMeta_offsets_le (w := w) hth_d).2.2.2
        have h32_d : 32 ≤ offPageDir c w (sm₁.mem (base + hdrNDst)) :=
          (epochMeta_offsets_le (w := w) hth_d).1.trans
            ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
              (epochMeta_offsets_le (w := w) hth_d).2.2.1)
        rw [← hmDst_eq₁] at hod_d
        simp only [hd0, ↓reduceIte] at ha
        dsimp only [hiFr]; rw [hibHi_eq₁, ite_eq_right hd0]
        rcases ha with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
          (split_ifs at g1 g2 <;>
            (clear *- g1 g2 hod_d hmD_pad h32_d; exact ⟨by omega, by omega⟩))
    have hs_p₂ : EpochSlotInv c U V w s_post₂.frontier (dualPSrc base s_post₂.mem)
        (dualMbSrc base s_post₂.mem) (pagedSlotIo 0 (dualPgHost c V w base nLive s_post₂.mem))
        0 true slSrc_p s_post₂.mem := by
      rw [hpS_p₂, hmbS_p₂, hpgH_p₂, hfr_p₂_hi]
      exact (hs1_₂.congr_mem
        (fun a hlo hhi => hm_p₂_s1₂ a (by clear *- hlo hpS_rng; omega)
          (by dsimp only [hiFr]; clear *- hhi hpS_rng hibHi_ge; omega))
        (fun a ha => hm_p₂_s1₂ a (hs_meta_b a ha).1 (hs_meta_b a ha).2)
        (fun a ha => hm_p₂_s1₂ a (by have := hown_pg_ge a ha; omega) (hown_pg_lt_hi a ha))
        ).at_exact_frontier (fr₂ := hiFr)
          (by dsimp only [hiFr]; clear *- hpS_rng hibHi_ge; omega)
          (by dsimp only [slSrc_p]; rw [hcap_s₁]; unfold dualMbSrc dualCapSrc
              by_cases hst0 : stg = 0
              · simp only [show sm₁.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
                rw [← hmid₁.mSrc_eq]
                by_cases hs0 : sm₁.mem (base + hdrNSrc) = 0
                · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only [hdrSmallMeta0, hiFr]
                  clear *- hibHi_ge; omega
                · rw [ite_eq_right hs0, ite_eq_right hs0]; dsimp only [hiFr]; rw [hibHi_eq₁]
                  split_ifs <;> (clear *- hmS_pad; omega)
              · have hd_nz : sm₁.mem (base + hdrNDst) ≠ 0 :=
                  fun hd0 => hst0 (hsched₁.nDst_zero hd0).2.1
                simp only [show sm₁.mem (base + hdrStage) = stg from rfl, hst0, hd_nz, ↓reduceIte]
                dsimp only [hiFr]; rw [← hmDst_eq₁, hibHi_eq₁, ite_eq_right hd_nz]
                clear *- hmD_pad; omega)
          (by dsimp only [pagedSlotIo, pgH, dualPgHost, hostPageLayout, epochPageArenaLayout]
              exact le_rfl)
    have hd_p₂ : EpochSlotInv c U V w s_post₂.frontier (dualPDst base s_post₂.mem)
        (dualMbDst base s_post₂.mem) (pagedSlotIo 1 (dualPgHost c V w base nLive s_post₂.mem))
        0 false slDst_p₂ s_post₂.mem := by
      have hd1_₂' : EpochSlotInv c U V w s1₂.frontier pDst (dualMbDst base sm₁.mem)
          (pagedSlotIo 1 pgH) 0 false slDst_p₂ s1₂.mem := by
        dsimp only [slDst_p₂]; rwa [← hdst_evs_eq]
      rw [hpD_p₂, hmbD_p₂, hpgH_p₂, hfr_p₂_hi]
      exact (hd1_₂'.congr_mem
        (fun a hlo hhi => hm_p₂_s1₂ a (by clear *- hlo hpD_rng; omega)
          (by dsimp only [hiFr]; clear *- hhi hpD_rng hibHi_ge; omega))
        (fun a ha => hm_p₂_s1₂ a (hd_meta_b a ha).1 (hd_meta_b a ha).2)
        (fun a ha => hm_p₂_s1₂ a (by have := hown_pg_ge a ha; omega) (hown_pg_lt_hi a ha))
        ).at_exact_frontier (fr₂ := hiFr)
          (by dsimp only [hiFr]; clear *- hpD_rng hibHi_ge; omega)
          (by dsimp only [slDst_p₂]; rw [hnc_d_eq, hcap_d₁]; unfold dualMbDst
              rw [hp8₁, ite_eq_left (by decide : 8 < 10)]
              by_cases hd0 : sm₁.mem (base + hdrNDst) = 0
              · rw [ite_eq_left hd0, ite_eq_left hd0]; dsimp only [hdrSmallMeta1, hiFr]
                clear *- hibHi_ge; omega
              · rw [ite_eq_right hd0, ite_eq_right hd0]; dsimp only [hiFr]
                rw [← hmDst_eq₁, hibHi_eq₁, ite_eq_right hd0]
                split_ifs <;> (clear *- hmD_pad; omega))
          (by dsimp only [pagedSlotIo, pgH, dualPgHost, hostPageLayout, epochPageArenaLayout]
              exact le_rfl)
    set L_post₂ : DualLatent c U V :=
      { Lm₂ with slotSrc := slSrc_p, slotDst := slDst_p₂, elapsed := Lm₂.elapsed + 1 }
    have hsc_any₂ := h_any₂.sched; rw [ite_eq_right (by rw [hp8_p₂]; decide)] at hsc_any₂
    obtain ⟨_, hb_tot₂, _⟩ := hsched₂.budget
    have hinv_p₂ : DualStateInv c U V w base s_dict' L_post₂ s_post₂ :=
      { hw11 := h_any₂.hw11, U_pos := h_any₂.U_pos, U_lt := h_any₂.U_lt
        V_pos := h_any₂.V_pos, V_le := h_any₂.V_le, wf := h_any₂.wf
        base_fr := h_any₂.base_fr, hdr := h_any₂.hdr, live_eq := h_any₂.live_eq
        live_le := h_any₂.live_le, ph_le := h_any₂.ph_le, stg_le := h_any₂.stg_le
        mSrc_eq := h_any₂.mSrc_eq, cache_src := h_any₂.cache_src
        nSrc_bounds := h_any₂.nSrc_bounds
        sched := by
          rw [ite_eq_right (by rw [hp8_p₂]; decide)]
          refine
            { nDst_bounds := hsc_any₂.nDst_bounds
              nDst_zero := hsc_any₂.nDst_zero
              stg_one := hsc_any₂.stg_one
              post_trig := by
                dsimp only [L_post₂]
                rw [hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide),
                  hc8_mid.1.2 hdrNSrc (by decide) (by decide)]
                exact hsched₂.post_trig
              trig_cap := by
                dsimp only [L_post₂]
                rw [hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide),
                  hpost₂_hdr hdrNDst (by decide) (by decide) (by decide),
                  hc8_mid.1.2 hdrNSrc (by decide) (by decide),
                  hc8_mid.1.2 hdrNDst (by decide) (by decide)]
                exact hsched₂.trig_cap
              drift_hi := by
                dsimp only [L_post₂]; have hd := hsched₂.drift_hi
                simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero] at hd ⊢; exact hd
              drift_lo := by
                dsimp only [L_post₂]; have hd := hsched₂.drift_lo
                simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero] at hd ⊢; exact hd
              ibLo_eq := hsc_any₂.ibLo_eq
              qLo_eq := hsc_any₂.qLo_eq
              ph1 := hsc_any₂.ph1
              ge2 := hsc_any₂.ge2
              ph2 := hsc_any₂.ph2
              ph3_10 := hsc_any₂.ph3_10
              ph11 := hsc_any₂.ph11
              budget := by
                dsimp only [L_post₂]
                rw [hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide),
                  hpgH_p₂, hpost₂_hdr hdrStage (by decide) (by decide) (by decide),
                  hp8_p₂, hpost₂_hdr hdrNDst (by decide) (by decide) (by decide),
                  hpost₂_hdr hdrMDst (by decide) (by decide) (by decide), hrem_p₂]
                rw [← hc8_mid.1.2 hdrNSrc (by decide) (by decide),
                  hpgH_m₂, ← hc8_mid.1.2 hdrStage (by decide) (by decide),
                  hp8₂, ← hc8_mid.1.2 hdrNDst (by decide) (by decide),
                  ← hc8_mid.1.2 hdrMDst (by decide) (by decide), hrem_sm₂] at hb_tot₂
                unfold remRebuildBudget futureRebuildBudget at hb_tot₂ ⊢
                simp only [Nat.reduceEqDiff, Nat.reduceLeDiff, and_self, ↓reduceIte] at hb_tot₂ ⊢
                have h2t := two_le_maxTailPhasesBudget
                  (max (whpThreshold c) (sm₁.mem (base + hdrNSrc)))
                generalize max (whpThreshold c) (sm₁.mem (base + hdrNSrc)) = nRef at hb_tot₂ h2t ⊢
                refine ⟨by clear *- h2t; omega, ?_, ?_⟩ <;>
                  (clear *- h1 hb_tot₂ h2t; omega) }
        pad_fits := h_any₂.pad_fits
        ph1_inv := h_any₂.ph1_inv
        ph3_inv := h_any₂.ph3_inv
        ph4_inv := h_any₂.ph4_inv
        pDst_pre := h_any₂.pDst_pre
        ph5_inv := h_any₂.ph5_inv
        ph6_inv := h_any₂.ph6_inv
        ph7_inv := h_any₂.ph7_inv
        ph8_inv := fun _ => by
          dsimp only [L_post₂, slSrc_p]
          rw [hrem_p₂, hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide), hcd1]
          have hmul : (rem - 1) * itemBatchWhp = rem * itemBatchWhp - itemBatchWhp := by
            rw [Nat.sub_mul, Nat.one_mul]
          refine ⟨by clear *- h1; omega, by clear *- hrem_le₁; omega, ?_⟩
          rw [hmul]; clear *- hcard_rem; omega
        ph9_inv := fun hp9' => absurd (hp8_p₂.symm.trans hp9') (by decide)
        ph10_inv := h_any₂.ph10_inv
        sl_le7 := fun hle7 => by rw [hp8_p₂] at hle7; omega
        sl_67 := fun h67 => by rw [hp8_p₂] at h67; omega
        sl_8 := fun _ => by
          dsimp only [L_post₂, slSrc_p, slDst_p₂]
          have hcap_eq : dualCapSrc base s_post₂.mem = dualCapSrc base sm₁.mem := by
            unfold dualCapSrc
            rw [hpost₂_hdr hdrStage (by decide) (by decide) (by decide),
              hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide),
              hpost₂_hdr hdrNDst (by decide) (by decide) (by decide)]
          rw [hcap_eq, hpost₂_hdr hdrNDst (by decide) (by decide) (by decide)]
          refine ⟨hcap_s₁, hnc_d_eq.trans hcap_d₁, hdj1, by rw [hor1, hdict_or₁],
            cleanPhase_zero_of_paged0 hs_p₂, hs_p₂, hd_p₂, hevs_s₁, fun hd_pos => ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          rw [hsum1, ← hdst_evs_eq, ← hsrc_eq]
          have hd2_pos : 0 < sm₂.mem (base + hdrNDst) :=
            (hc8_mid.1.2 hdrNDst (by decide) (by decide)) ▸ hd_pos
          have hd_old := hevs_d₂ hd2_pos
          simp only [↓reduceIte] at hd_old
          rw [hc8_mid.1.2 hdrNDst (by decide) (by decide)]
          clear *- hd_old; omega
        sl_ge9 := fun hge9 => by rw [hp8_p₂] at hge9; omega }
    -- Prove `Coupled8` on `(s_post₁, s_post₂)` from `hc_s1`
    have hc8_post : Coupled8 c V w base nLive s_post₁ s_post₂ := by
      have hreg_p₁ : Coupled8Region c w base s_post₁.mem = Coupled8Region c w base sm₁.mem :=
        coupled8Region_of_hdr_eq
          (hpost₁_hdr hdrStage (by decide) (by decide))
          (hpost₁_hdr hdrNSrc (by decide) (by decide))
          (hpost₁_hdr hdrNDst (by decide) (by decide))
          (hpost₁_hdr hdrPad (by decide) (by decide))
      have hmbS_p₁ : dualMbSrc base s_post₁.mem = dualMbSrc base sm₁.mem := by
        unfold dualMbSrc
        rw [hpost₁_hdr hdrStage (by decide) (by decide),
          hpost₁_hdr hdrNSrc (by decide) (by decide),
          hpost₁_hdr hdrPad (by decide) (by decide)]
      have hc8_mem : ∀ addr, Coupled8Region c w base s_post₁.mem addr →
          s_post₁.mem addr = s_post₂.mem addr := by
        rw [hreg_p₁]; intro addr hreg
        have hb : base + 48 ≤ addr ∧ addr < hiFr := by
          rcases hreg with ⟨g1, g2⟩ | hm
          · exact ⟨by clear *- g1 hpS_rng; omega,
              by dsimp only [hiFr]; clear *- g2 hpS_rng hibHi_ge; omega⟩
          · exact hs_meta_b addr (hcap_s₁.symm ▸ hm)
        rw [hm_p₁_s1₁ addr hb.1 hb.2, hm_p₂_s1₂ addr hb.1 hb.2]
        exact hc_s1.mem_eq addr hreg
      have hmb1_meta :
          slotOwnsNonPageMeta c w (dualMbSrc base sm₁.mem) Lm₁.slotSrc.nCap
            (dualMbSrc base sm₁.mem + 1) :=
        Or.inl ⟨by omega, by split_ifs <;> omega⟩
      have hmb1_in : Coupled8Region c w base sm₁.mem (dualMbSrc base sm₁.mem + 1) :=
        Or.inr (hcap_s₁ ▸ hmb1_meta)
      have hns_p₁_s1 : s_post₁.mem (dualMbSrc base sm₁.mem + 1) =
          s1₁.mem (dualMbSrc base sm₁.mem + 1) :=
        hm_p₁_s1₁ _ (hs_meta_b _ hmb1_meta).1 (hs_meta_b _ hmb1_meta).2
      have hns_p₂_p₁ : s_post₂.mem (dualMbSrc base sm₁.mem + 1) =
          s_post₁.mem (dualMbSrc base sm₁.mem + 1) :=
        (hc8_mem _ (hreg_p₁.symm ▸ hmb1_in)).symm
      have hsl_s_p₁ := (h_any₁.sl_8 hp8_p₁).2.2.2.2.2.1
      rw [hmbS_p₁, hpgH_p₁] at hsl_s_p₁
      have hp1_pair := ((pagedSlotIo 0 pgH).congr_of_outside hw_pos hc_s1.inv₁
        (fun a ha => hm_p₁_s1₁ a (by have := hown_pg_ge a ha; omega) (hown_pg_lt_hi a ha))).2
      have hp2_pair := ((pagedSlotIo 0 pgH).congr_of_outside hw_pos hc_s1.inv₂
        (fun a ha => hm_p₂_s1₂ a (by have := hown_pg_ge a ha; omega) (hown_pg_lt_hi a ha))).2
      refine ⟨hsch_post, ?_⟩
      rw [hmbS_p₁, hpgH_p₁]
      exact
        { fr_eq := hsch_post.1
          side_zero := rfl
          valid₁ := by
            have hv := hsl_s_p₁.io_valid
            have hw_pg : (pagedSlotIo 0 pgH).pgL.w = w := rfl
            rwa [hw_pg]
          disj := fun addr hreg => hc_s1.disj addr (hreg_p₁ ▸ hreg)
          mem_eq := hc8_mem
          inv₁ := hsl_s_p₁.io_stateInv
          inv₂ := by
            have hi := hs_p₂.io_stateInv
            rw [hmbS_p₂, hpgH_p₂, hns_p₂_p₁] at hi; exact hi
          pair_eq := fun idx hidx => by
            have hidx0 : idx < s1₁.mem (dualMbSrc base sm₁.mem + 1) := hns_p₁_s1 ▸ hidx
            exact (hp1_pair idx hidx0).trans
              ((hc_s1.pair_eq idx hidx0).trans (hp2_pair idx hidx0).symm) }
    refine ⟨⟨L_post₂, rfl, rfl, hinv_p₂, fun hg_s hg_d => ?_⟩, Or.inl ⟨hp8_p₁, hc8_post⟩⟩
    have hc_mb := hmc_mb_₂ hd_sm_bound hg_s (by dsimp only [slDst_p₂] at hg_d; rwa [hdst_evs_eq])
    have hmc_tm := htmev₂.2; rw [ite_eq_left h1] at hmc_tm
    have hmc_bg := hbgev₂.2.2
    dsimp only [mb, pSrc, pDst, stg, itemBatchWhp] at hmc_bg hmc_tm hc_mb ⊢
    clear *- hmc_bg hmc_tm hc_mb; omega
  · -- Branch `8 → 9`: `rem = 1`, `pageBeginUnpermBoundedProg` runs
    have hrem1 : rem = 1 := by clear *- hrem_ge1 h1; omega
    have hcd1_zero : (liveDom s_src1).card = 0 := by
      rw [hrem1, Nat.one_mul] at hcard_rem; clear *- hcd1 hcard_rem; omega
    have hsrc1_empty : s_src1 = fun _ => none := by
      funext u; by_contra hne
      have hpos : 0 < (liveDom s_src1).card :=
        Finset.card_pos.mpr ⟨u, (mem_liveDom_iff _ _).mpr hne⟩
      clear *- hpos hcd1_zero; omega
    have hdict_dst1 : toDictState s_dst1 = s_dict' := by
      have hor1_dst : orOpt s_dst1 s_src1 = s_dst1 := by
        rw [hsrc1_empty]; unfold orOpt; funext x; cases s_dst1 x <;> rfl
      rw [← hor1_dst, hor1, hdict_or₁]
    set s3₁ := (Memory.spec 0).clientState s1₁ (pageBeginUnpermBoundedProg pgH.toCtx)
    set s3₂ := (Memory.spec 0).clientState s1₂ (pageBeginUnpermBoundedProg pgH.toCtx)
    set uTicks := max (whpThreshold c) (sm₁.mem (base + hdrNSrc)) / 240 + pgH.pgB / 8 + 4
    have hbu_frm := pageBeginUnpermBoundedProg_frame pgH
    have hst₁_eq : st₁ =
        { mem := Function.update (Function.update
            (Function.update s3₁.mem (base + hdrUnpermDone) 0) (base + hdrRem) uTicks)
            (base + hdrPhase) 9
          frontier := s3₁.frontier } := by
      rw [hst₁_bg, hbgev₁.1, htmev₁.1, ite_eq_right h1]
    have hst₂_eq : st₂ =
        { mem := Function.update (Function.update
            (Function.update s3₂.mem (base + hdrUnpermDone) 0) (base + hdrRem) uTicks)
            (base + hdrPhase) 9
          frontier := s3₂.frontier } := by
      rw [hst₂_bg, hbgev₂.1, htmev₂.1, ite_eq_right h1]
    have hpost₁_ph9 : s_post₁.mem (base + hdrPhase) = 9 := by
      rw [hpost₁_def, hsps₁_id]; dsimp only [Memory.State.mem]
      rw [clear_of_not_owns
        (by simp only [Block.Owns]; dsimp only [hdrPhase]; clear *- hb192_p₁; omega), hst₁_eq]
      exact Function.update_self ..
    have hpost₂_ph9 : s_post₂.mem (base + hdrPhase) = 9 :=
      (hsch_post.2 hdrPhase (by decide) (by decide)).symm.trans hpost₁_ph9
    have hpost₂_ud0 : s_post₂.mem (base + hdrUnpermDone) = 0 := by
      rw [hpost₂_def, hsps₂_id]; dsimp only [Memory.State.mem]
      rw [clear_of_not_owns
        (by simp only [Block.Owns]; dsimp only [hdrUnpermDone]; clear *- hb192_p₂; omega),
        hst₂_eq]; dsimp only [Memory.State.mem]
      rw [Function.update_of_ne (base_add_ne (by decide)),
        Function.update_of_ne (base_add_ne (by decide))]
      exact Function.update_self ..
    have hpost₂_rem : s_post₂.mem (base + hdrRem) = uTicks := by
      rw [hpost₂_def, hsps₂_id]; dsimp only [Memory.State.mem]
      rw [clear_of_not_owns
        (by simp only [Block.Owns]; dsimp only [hdrRem]; clear *- hb192_p₂; omega),
        hst₂_eq]; dsimp only [Memory.State.mem]
      rw [Function.update_of_ne (base_add_ne (by decide))]
      exact Function.update_self ..
    have hpost₁_hdr : ∀ off < 48, off ≠ hdrUnpermDone → off ≠ hdrRem → off ≠ hdrPhase →
        s_post₁.mem (base + off) = sm₁.mem (base + off) := fun off hoff h_ud h_r h_p => by
      rw [hpost₁_def, hsps₁_id]; dsimp only [Memory.State.mem]
      rw [clear_of_not_owns (by simp only [Block.Owns]; clear *- hoff hb192_p₁; omega),
        hst₁_eq]; dsimp only [Memory.State.mem]
      rw [Function.update_of_ne (base_add_ne h_p),
        Function.update_of_ne (base_add_ne h_r),
        Function.update_of_ne (base_add_ne h_ud),
        hbu_frm.mem_outside s1₁ (base + off) (fun ha => by
          have := hown_pg_ge _ ha; clear *- hoff this; omega)]
      exact hs1₁_hdr48 off hoff
    have hpost₂_hdr : ∀ off < 48, off ≠ hdrUnpermDone → off ≠ hdrRem → off ≠ hdrPhase →
        s_post₂.mem (base + off) = sm₁.mem (base + off) := fun off hoff h_ud h_r h_p =>
      (hsch_post.2 off hoff h_ud).symm.trans (hpost₁_hdr off hoff h_ud h_r h_p)
    have hfr_p₂_hi : s_post₂.frontier = hiFr := by
      have hsc := h_any₂.sched; rw [ite_eq_right (by rw [hpost₂_ph9]; decide)] at hsc
      obtain ⟨hlo, hhi⟩ := hsc.ph3_10 ⟨by rw [hpost₂_ph9]; decide, by rw [hpost₂_ph9]; decide⟩
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hhi
      rw [hpost₂_hdr hdrItemHi (by decide) (by decide) (by decide) (by decide),
        hpost₂_hdr hdrQHi (by decide) (by decide) (by decide) (by decide)] at hlo hhi
      dsimp only [hiFr, nLive] at hlo hhi ⊢; clear *- hlo hhi; omega
    have hm_p₂_s3₂ : ∀ a, base + 48 ≤ a → a < hiFr → s_post₂.mem a = s3₂.mem a :=
      fun a h48 hlt => by
        have hfr_st : st₂.frontier - k_sh = hiFr := by
          have : s_post₂.frontier = st₂.frontier - k_sh := by rw [hpost₂_def]
          exact this.symm.trans hfr_p₂_hi
        rw [hpost₂_def, hsps₂_id]; dsimp only [Memory.State.mem]
        rw [clear_of_not_owns (by simp only [Block.Owns]; rw [hfr_st]; clear *- hlt; omega),
          hst₂_eq]; dsimp only [Memory.State.mem]
        iterate 3 rw [Function.update_of_ne (by
          dsimp only [hdrUnpermDone, hdrRem, hdrPhase]; clear *- h48; omega)]
    -- Unperm state and destination `EpochSlotInv` on `s_post₂`
    have hd1_₂' : EpochSlotInv c U V w s1₂.frontier pDst (dualMbDst base sm₁.mem)
        (pagedSlotIo 1 pgH) 0 false slDst_p₂ s1₂.mem := by
      dsimp only [slDst_p₂]; rwa [← hdst_evs_eq]
    have hio_s1₂ := hs1_₂.io_stateInv
    have hio_d1₂ := hd1_₂'.io_stateInv
    unfold SlotIoLayout.StateInv at hio_s1₂ hio_d1₂
    have hside0 : (pagedSlotIo 0 pgH).side = false := rfl
    have hside1 : (pagedSlotIo 1 pgH).side = true := rfl
    have hup0 : (pagedSlotIo 0 pgH).usePaged ≠ 0 := Nat.one_ne_zero
    have hup1 : (pagedSlotIo 1 pgH).usePaged ≠ 0 := Nat.one_ne_zero
    rw [ite_eq_right hup0, hside0] at hio_s1₂
    rw [ite_eq_right hup1, hside1] at hio_d1₂
    dsimp only [pagedSlotIo] at hio_s1₂ hio_d1₂
    have hvl1_f₂ : (extractPageUnperm pgH s1₂.mem).st.virtLen false = 0 := by
      rw [hio_s1₂.2.2.2.2.1, hs1_₂.mem_nSide_eq]; exact hcd1_zero
    have hvl1_t₂ : (extractPageUnperm pgH s1₂.mem).st.virtLen true = nLive := by
      rw [hio_d1₂.2.2.2.2.1, hd1_₂'.mem_nSide_eq]; dsimp only [slDst_p₂]
      rw [← dom_toDictState_card, hdict_dst1]
    have hcp_s1₂ : (extractPageUnperm pgH s1₂.mem).cleanPhase = 0 :=
      cleanPhase_zero_of_paged0 hs1_₂
    have hbu_sp₂ := pageBeginUnpermBoundedProg_spec (L := pgH) (s := s1₂)
      (hfr_s1_₂.symm ▸ hv_fr₂ : pgH.Valid pgH.w s1₂.frontier) hio_s1₂.2.1
    dsimp only at hbu_sp₂
    obtain ⟨_, hu_s3₂_eq, har_s3₂_eq⟩ := hbu_sp₂
    obtain ⟨hu3₂_v, hu3₂_pos_imp, hu3₂_tp⟩ := PageUnpermState.beginUnperm_spec hio_s1₂.1
    have hu3₂_pos : 0 < (extractPageUnperm pgH s3₂.mem).cleanPhase := by
      rw [hu_s3₂_eq]; exact hu3₂_pos_imp ⟨hcp_s1₂, hvl1_f₂⟩
    have hu3₂_lt4 : (extractPageUnperm pgH s3₂.mem).cleanPhase < 4 := by
      rw [hu_s3₂_eq]; unfold PageUnpermState.beginUnperm
      rw [ite_eq_left ⟨hcp_s1₂, hvl1_f₂⟩]; dsimp only; split_ifs <;> decide
    have hu3₂_st : (extractPageUnperm pgH s3₂.mem).st = (extractPageUnperm pgH s1₂.mem).st := by
      rw [hu_s3₂_eq]; unfold PageUnpermState.beginUnperm
      rw [ite_eq_left ⟨hcp_s1₂, hvl1_f₂⟩]
    have hu_p₂ : extractPageUnperm pgH s_post₂.mem = extractPageUnperm pgH s3₂.mem :=
      extractPageUnperm_congr hw_pos fun a ha =>
        hm_p₂_s3₂ a (by have := (hdisj_pg₁ a ha).1; omega)
          (lt_of_lt_of_le (hdisj_pg₁ a ha).2.1 (Nat.le_add_right _ _))
    have hpgH_p₂ : dualPgHost c V w base nLive s_post₂.mem = pgH := by
      dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
      rw [hpost₂_hdr hdrNDst (by decide) (by decide) (by decide) (by decide),
        hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide),
        hpost₂_hdr hdrStage (by decide) (by decide) (by decide) (by decide),
        hpost₂_hdr hdrPad (by decide) (by decide) (by decide) (by decide),
        hpost₂_hdr hdrItemHi (by decide) (by decide) (by decide) (by decide),
        hpost₂_hdr hdrQHi (by decide) (by decide) (by decide) (by decide)]
    have hpD_p₂ : dualPDst base s_post₂.mem = pDst := by
      unfold dualPDst; rw [hpost₂_ph9, ite_eq_left (by decide : 9 < 10),
        hpost₂_hdr hdrStage (by decide) (by decide) (by decide) (by decide)]
    have hmbD_p₂ : dualMbDst base s_post₂.mem = dualMbDst base sm₁.mem := by
      unfold dualMbDst
      rw [hpost₂_ph9, hp8₁, ite_eq_left (by decide : 9 < 10), ite_eq_left (by decide : 8 < 10),
        hpost₂_hdr hdrNDst (by decide) (by decide) (by decide) (by decide),
        hpost₂_hdr hdrStage (by decide) (by decide) (by decide) (by decide),
        hpost₂_hdr hdrPad (by decide) (by decide) (by decide) (by decide)]
    have hd_p₂ : EpochSlotInv c U V w s_post₂.frontier (dualPDst base s_post₂.mem)
        (dualMbDst base s_post₂.mem) (pagedSlotIo 1 pgH) 0 false slDst_p₂ s_post₂.mem := by
      rw [hpD_p₂, hmbD_p₂, hfr_p₂_hi]
      have hd1_hi₂ : EpochSlotInv c U V w hiFr pDst (dualMbDst base sm₁.mem)
          (pagedSlotIo 1 pgH) 0 false slDst_p₂ s1₂.mem :=
        hd1_₂'.at_exact_frontier (fr₂ := hiFr)
          (by dsimp only [hiFr]; clear *- hpD_rng hibHi_ge; omega)
          (by dsimp only [slDst_p₂]; rw [hnc_d_eq, hcap_d₁]; unfold dualMbDst
              rw [hp8₁, ite_eq_left (by decide : 8 < 10)]
              by_cases hd0 : sm₁.mem (base + hdrNDst) = 0
              · rw [ite_eq_left hd0, ite_eq_left hd0]; dsimp only [hdrSmallMeta1, hiFr]
                clear *- hibHi_ge; omega
              · rw [ite_eq_right hd0, ite_eq_right hd0]; dsimp only [hiFr]
                rw [← hmDst_eq₁, hibHi_eq₁, ite_eq_right hd0]
                split_ifs <;> (clear *- hmD_pad; omega))
          (by dsimp only [pagedSlotIo, pgH, dualPgHost, hostPageLayout, epochPageArenaLayout]
              exact le_rfl)
      have hraw_d1 := hd1_hi₂; unfold EpochSlotInv at hraw_d1
      have hio_p₂ : (pagedSlotIo 1 pgH).StateInv (s1₂.mem (dualMbDst base sm₁.mem + 1)) 0
          s_post₂.mem := by
        unfold SlotIoLayout.StateInv
        rw [ite_eq_right hup1, hside1]
        dsimp only [pagedSlotIo]
        rw [hu_p₂]
        exact ⟨hu_s3₂_eq ▸ hu3₂_v, hu3₂_st ▸ hio_d1₂.2.1, hu3₂_st ▸ hio_d1₂.2.2.1,
          hu3₂_st ▸ hio_d1₂.2.2.2.1, hu3₂_st ▸ hio_d1₂.2.2.2.2.1, fun _ => rfl, hu3₂_lt4⟩
      have hp_out_d : ∀ a, pDst ≤ a → a < pDst + 64 → s_post₂.mem a = s1₂.mem a :=
        fun a hlo hhi =>
          (hm_p₂_s3₂ a (by clear *- hlo hpD_rng; omega)
            (by dsimp only [hiFr]; clear *- hhi hpD_rng hibHi_ge; omega)).trans
            (hbu_frm.mem_outside s1₂ a (fun ha => by
              have := hown_pg_ge a ha; clear *- hhi hpD_rng this; omega))
      have hm_out_d : ∀ a, slotOwnsNonPageMeta c w (dualMbDst base sm₁.mem) slDst_p₂.nCap a →
          s_post₂.mem a = s1₂.mem a := fun a ha => by
        have ha_d : slotOwnsNonPageMeta c w (dualMbDst base sm₁.mem) (sm₁.mem (base + hdrNDst)) a :=
          by dsimp only [slDst_p₂] at ha; rwa [hnc_d_eq, hcap_d₁] at ha
        have ha48 : base + 48 ≤ a ∧ a < sm₁.mem (base + hdrItemHi) := by
          unfold slotOwnsNonPageMeta dualMbDst at ha_d
          rw [hp8₁, ite_eq_left (by decide : 8 < 10)] at ha_d
          by_cases hd0 : sm₁.mem (base + hdrNDst) = 0
          · simp only [hd0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
              hdrSmallMeta1] at ha_d
            clear *- ha_d hibHi_ge; exact ⟨by omega, by omega⟩
          · have hth_d := (hsched₁.nDst_bounds.resolve_left hd0).1
            have hod_d := (epochMeta_offsets_le (w := w) hth_d).2.2.2
            have h32_d : 32 ≤ offPageDir c w (sm₁.mem (base + hdrNDst)) :=
              (epochMeta_offsets_le (w := w) hth_d).1.trans
                ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
                  (epochMeta_offsets_le (w := w) hth_d).2.2.1)
            rw [← hmDst_eq₁] at hod_d
            simp only [hd0, ↓reduceIte] at ha_d
            rw [hibHi_eq₁, ite_eq_right hd0]
            rcases ha_d with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
              (split_ifs at g1 g2 <;>
                (clear *- g1 g2 hod_d hmD_pad h32_d; exact ⟨by omega, by omega⟩))
        exact (hm_p₂_s3₂ a ha48.1 (lt_of_lt_of_le ha48.2 (Nat.le_add_right _ _))).trans
          (hbu_frm.mem_outside s1₂ a (fun hpg => by
            rcases hpg with hm | hi
            · exact (hdisj_pg₁ a hm).2.2.2 ha_d
            · exact absurd hi.1 (Nat.not_le_of_gt ha48.2)))
      refine hd1_hi₂.transfer_io (io₂ := pagedSlotIo 1 pgH)
        (show (pagedSlotIo 1 pgH).Valid w hiFr from hv_hi₁) rfl
        ⟨fun h0 => by rw [ite_eq_left h0] at hraw_d1; exact hraw_d1.2.2.1.qBits_eq,
         fun h0 => by rw [ite_eq_right h0] at hraw_d1; exact hraw_d1.1.qBits_le⟩
        rfl
        ⟨fun h0 => by rw [ite_eq_left h0] at hraw_d1; exact hraw_d1.2.2.2.1.congr hp_out_d,
         fun h0 => by
          rw [ite_eq_right h0] at hraw_d1
          exact hraw_d1.2.1.1.congr fun a hlo hhi =>
            hp_out_d a hlo (by dsimp only at hlo hhi; clear *- hlo hhi; omega)⟩
        (fun a hlo hhi => by
          by_cases h0 : slDst_p₂.nCap = 0
          · rw [ite_eq_left h0] at hraw_d1
            exact fun hia => hraw_d1.2.2.2.2.1 a hlo hhi (Or.inr (Or.inr hia))
          · rw [ite_eq_right h0] at hraw_d1; exact hraw_d1.1.disj_pBase_io a hlo hhi)
        (fun a ha => by
          unfold slotOwnsNonPageMeta at ha
          by_cases h0 : slDst_p₂.nCap = 0
          · rw [ite_eq_left h0] at hraw_d1 ha
            rcases ha with ⟨g1, g2⟩ | ⟨hne, _⟩
            · exact hraw_d1.2.2.1.disjoint_hdr a (by dsimp only; clear *- g1 g2; omega)
            · exact absurd h0 hne
          · rw [ite_eq_right h0] at hraw_d1 ha
            exact hraw_d1.1.disj_fast_io a (ha.imp id And.right))
        hm_out_d hio_p₂
        (fun p hp_lt => by
          have hp_nc : (extractPageUnperm pgH s1₂.mem).beginUnperm.toPhys true p < pgH.nCap := by
            rw [hu3₂_tp true p]
            have hti_lt := hio_d1₂.1.toPhys_lt (hio_d1₂.2.2.2.2.1.symm ▸ hp_lt)
            exact hti_lt.trans_le hio_d1₂.2.2.2.1
          have hpair_s3 : arenaPairAt pgH s_post₂.mem
              ((extractPageUnperm pgH s1₂.mem).beginUnperm.toPhys true p) =
              arenaPairAt pgH s1₂.mem
                ((extractPageUnperm pgH s1₂.mem).beginUnperm.toPhys true p) := by
            have ha3 := arenaPairAt_congr hw_pos
              (fun a ha => hm_p₂_s3₂ a
                (by have := hown_pg_ge a (Or.inr ha); omega) ha.2) hp_nc
            exact ha3.trans (congrFun har_s3₂_eq _)
          unfold slotIoPairAt
          rw [ite_eq_right hup1, hside1]
          dsimp only [pagedSlotIo]
          rw [hu_p₂, hu_s3₂_eq]
          unfold PageUnpermState.virtAt
          exact hpair_s3.trans (congrArg (arenaPairAt pgH s1₂.mem) (hu3₂_tp true p)))
    set L_post₂ : DualLatent c U V :=
      { Lm₂ with
        slotSrc := slSrc_p
        slotDst := slDst_p₂
        elapsed := Lm₂.elapsed + 1
        unpermBound := (extractPageUnperm pgH s3₂.mem).unpermRank }
    have hsc_any₂ := h_any₂.sched; rw [ite_eq_right (by rw [hpost₂_ph9]; decide)] at hsc_any₂
    obtain ⟨_, hb_tot₂, hb_el₂⟩ := hsched₂.budget
    have hnH_ref := dualNHost_le_two_nRef hmid₁ (by omega)
    have hpgB_ref := pageSizeWhp_host_le_ref hth_h₁.1 hnH_ref
    have hnL_ref := (active_nLive_le_two_nRef hsched₂.post_trig hsched₂.trig_cap hsched₂.drift_hi
      hsched₂.drift_lo (by clear *- hb_el₂; simp only [↓reduceIte]; omega) hmid₂.live_le).2
    rw [← hc8_mid.1.2 hdrNSrc (by decide) (by decide)] at hnL_ref
    have hinv_p₂ : DualStateInv c U V w base s_dict' L_post₂ s_post₂ :=
      { hw11 := h_any₂.hw11, U_pos := h_any₂.U_pos, U_lt := h_any₂.U_lt
        V_pos := h_any₂.V_pos, V_le := h_any₂.V_le, wf := h_any₂.wf
        base_fr := h_any₂.base_fr, hdr := h_any₂.hdr, live_eq := h_any₂.live_eq
        live_le := h_any₂.live_le, ph_le := h_any₂.ph_le, stg_le := h_any₂.stg_le
        mSrc_eq := h_any₂.mSrc_eq, cache_src := h_any₂.cache_src
        nSrc_bounds := h_any₂.nSrc_bounds
        sched := by
          rw [ite_eq_right (by rw [hpost₂_ph9]; decide)]
          refine
            { nDst_bounds := hsc_any₂.nDst_bounds
              nDst_zero := hsc_any₂.nDst_zero
              stg_one := hsc_any₂.stg_one
              post_trig := by
                dsimp only [L_post₂]
                rw [hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide),
                  hc8_mid.1.2 hdrNSrc (by decide) (by decide)]
                exact hsched₂.post_trig
              trig_cap := by
                dsimp only [L_post₂]
                rw [hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide),
                  hpost₂_hdr hdrNDst (by decide) (by decide) (by decide) (by decide),
                  hc8_mid.1.2 hdrNSrc (by decide) (by decide),
                  hc8_mid.1.2 hdrNDst (by decide) (by decide)]
                exact hsched₂.trig_cap
              drift_hi := by
                dsimp only [L_post₂]; have hd := hsched₂.drift_hi
                simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero] at hd ⊢; exact hd
              drift_lo := by
                dsimp only [L_post₂]; have hd := hsched₂.drift_lo
                simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero] at hd ⊢; exact hd
              ibLo_eq := hsc_any₂.ibLo_eq
              qLo_eq := hsc_any₂.qLo_eq
              ph1 := hsc_any₂.ph1
              ge2 := hsc_any₂.ge2
              ph2 := hsc_any₂.ph2
              ph3_10 := hsc_any₂.ph3_10
              ph11 := hsc_any₂.ph11
              budget := by
                dsimp only [L_post₂]
                rw [hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide),
                  hpgH_p₂, hpost₂_hdr hdrStage (by decide) (by decide) (by decide) (by decide),
                  hpost₂_ph9, hpost₂_hdr hdrNDst (by decide) (by decide) (by decide) (by decide),
                  hpost₂_hdr hdrMDst (by decide) (by decide) (by decide) (by decide), hpost₂_rem]
                rw [← hc8_mid.1.2 hdrNSrc (by decide) (by decide),
                  hpgH_m₂, ← hc8_mid.1.2 hdrStage (by decide) (by decide),
                  hp8₂, ← hc8_mid.1.2 hdrNDst (by decide) (by decide),
                  ← hc8_mid.1.2 hdrMDst (by decide) (by decide), hrem_sm₂, hrem1] at hb_tot₂
                unfold remRebuildBudget futureRebuildBudget at hb_tot₂ ⊢
                simp only [Nat.reduceEqDiff, Nat.reduceLeDiff, and_self, ↓reduceIte] at hb_tot₂ ⊢
                have h2t := two_le_maxTailPhasesBudget
                  (max (whpThreshold c) (sm₁.mem (base + hdrNSrc)))
                have hpgH_eq_b : pgH.pgB = pageSizeWhp (dualNHost base sm₁.mem) := rfl
                have hpg_div : pgH.pgB / 8 ≤
                    max 32 (Nat.log 2 (2 * max (whpThreshold c)
                      (sm₁.mem (base + hdrNSrc))) + 4) / 8 := by
                  rw [hpgH_eq_b]; exact Nat.div_le_div_right hpgB_ref
                dsimp only [uTicks]
                generalize max (whpThreshold c) (sm₁.mem (base + hdrNSrc)) = nRef
                  at hb_tot₂ h2t hpg_div ⊢
                refine ⟨by clear *- h2t; omega, ?_, ?_⟩ <;>
                  (clear *- hb_tot₂ h2t hpg_div; omega) }
        pad_fits := h_any₂.pad_fits
        ph1_inv := h_any₂.ph1_inv
        ph3_inv := h_any₂.ph3_inv
        ph4_inv := h_any₂.ph4_inv
        pDst_pre := h_any₂.pDst_pre
        ph5_inv := h_any₂.ph5_inv
        ph6_inv := h_any₂.ph6_inv
        ph7_inv := h_any₂.ph7_inv
        ph8_inv := fun hp8' => absurd (hpost₂_ph9.symm.trans hp8') (by decide)
        ph9_inv := fun _ => by
          dsimp only [L_post₂]
          rw [hpgH_p₂, hpost₂_rem,
            hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide),
            hpost₂_ud0, hu_p₂]
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          refine ⟨by dsimp only [uTicks]; clear *-; omega, le_rfl, by decide,
            fun _ => ⟨hu3₂_pos, hu3₂_lt4, le_rfl, ?_⟩⟩
          have hrk := unpermRank_le_of_inv (u := extractPageUnperm pgH s3₂.mem)
            (hu_s3₂_eq ▸ hu3₂_v)
          rw [hu3₂_st, hvl1_t₂, hio_s1₂.2.1] at hrk
          have hrk' : (extractPageUnperm pgH s3₂.mem).unpermRank ≤
              4 * max (whpThreshold c) (sm₁.mem (base + hdrNSrc)) + 66 * pgH.pgB + 512 := by
            dsimp only [nLive] at hrk hnL_ref
            generalize max (whpThreshold c) (sm₁.mem (base + hdrNSrc)) = nRef at hnL_ref ⊢
            clear *- hrk hnL_ref; omega
          have hz := unperm_rank_reaches_zero hrk'
          unfold calcUnpermTicks at hz
          dsimp only [uTicks]; clear *- hz; omega
        ph10_inv := h_any₂.ph10_inv
        sl_le7 := fun hle7 => by rw [hpost₂_ph9] at hle7; omega
        sl_67 := fun h67 => by rw [hpost₂_ph9] at h67; omega
        sl_8 := fun hp8' => absurd (hpost₂_ph9.symm.trans hp8') (by decide)
        sl_ge9 := fun _ => by
          dsimp only [L_post₂, slDst_p₂]
          rw [hpost₂_hdr hdrNDst (by decide) (by decide) (by decide) (by decide),
            hpost₂_hdr hdrStage (by decide) (by decide) (by decide) (by decide),
            hpost₂_ph9,
            hpost₂_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide),
            hpost₂_hdr hdrPad (by decide) (by decide) (by decide) (by decide),
            hpost₂_hdr hdrItemLo (by decide) (by decide) (by decide) (by decide),
            hpost₂_hdr hdrQLo (by decide) (by decide) (by decide) (by decide),
            hpost₂_hdr hdrItemHi (by decide) (by decide) (by decide) (by decide),
            hpost₂_hdr hdrQHi (by decide) (by decide) (by decide) (by decide),
            hpost₂_ud0]
          have hio_eq9 : activeDstIo c w (valBits V) base stg 9
              (sm₁.mem (base + hdrNSrc)) (sm₁.mem (base + hdrNDst)) (sm₁.mem (base + hdrPad))
              (sm₁.mem (base + hdrItemLo)) (sm₁.mem (base + hdrQLo))
              (sm₁.mem (base + hdrItemHi)) (sm₁.mem (base + hdrQHi)) nLive 0 =
              pagedSlotIo 1 pgH := rfl
          rw [hio_eq9]; simp only [Bool.false_eq_true, false_and, ↓reduceIte, Nat.add_zero]
          refine ⟨hnc_d_eq.trans hcap_d₁, hdict_dst1, hd_p₂, fun hd_pos => ?_⟩
          have hev_sum : (Lm₁.slotDst.evs ++ ex1).length =
              Lm₁.slotDst.evs.length + (liveDom Lm₁.slotSrc.s_abs).card := by
            rw [← hsum1, hcd1_zero, Nat.add_zero]
          rw [hev_sum, ← hdst_evs_eq, ← hsrc_eq]
          have hd2_pos : 0 < sm₂.mem (base + hdrNDst) :=
            (hc8_mid.1.2 hdrNDst (by decide) (by decide)) ▸ hd_pos
          have hd_old := hevs_d₂ hd2_pos
          simp only [↓reduceIte] at hd_old
          rw [hc8_mid.1.2 hdrNDst (by decide) (by decide)]
          clear *- hd_old; omega }
    refine ⟨⟨L_post₂, rfl, rfl, hinv_p₂, fun hg_s hg_d => ?_⟩, Or.inr ⟨hpost₁_ph9, hsch_post⟩⟩
    have hc_mb := hmc_mb_₂ hd_sm_bound hg_s (by dsimp only [slDst_p₂] at hg_d; rwa [hdst_evs_eq])
    have hmc_tm := htmev₂.2; rw [ite_eq_right h1] at hmc_tm
    have hmc_bu : memoryCost (pageBeginUnpermBoundedProg pgH.toCtx) s1₂ ≤ 10 := hbu_frm.cost_le s1₂
    have hmc_bg := hbgev₂.2.2
    dsimp only [mb, pSrc, pDst, stg, itemBatchWhp] at hmc_bg hmc_tm hc_mb hmc_bu ⊢
    clear *- hmc_bg hmc_tm hc_mb hmc_bu; omega

/-- Full Phase-`8` mutation congruence: produces canonical `(s_src1, s_dst1, extra)` determined by
`s₁` alone and proves that EVERY coupled state `(L₂, s₂)` sharing `slotSrc`, `slotDst.s_abs`, and
`slotDst.evs` transitions to `(s_src1, s_dst1, extra)` with `DualStateInv`, fast-path `memoryCost`
bounds, and `8 → 8` `Coupled8` / `8 → 9` `SchedEq`. -/
theorem coupled8_mutate_step {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L₁ : DualLatent c U V} {s₁ : Memory.State}
    (h₁ : DualStateInv c U V w base s_dict L₁ s₁)
    (hp8 : s₁.mem (base + hdrPhase) = 8)
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
    let sg₁ : Memory.State := { mem := sp₁.mem, frontier := s₁.frontier + k_grow }
    let st₁ :=
      (Memory.spec 0).clientState sg₁ (stepOpProg (((base, sg₁.frontier), opTag), (u.val, v_val)))
    let k_sh :=
      (Memory.spec 0).clientResult st₁ (postRandShrinkProg ((base, st₁.frontier), opTag))
    let sps₁ :=
      (Memory.spec 0).clientState st₁ (postRandShrinkProg ((base, st₁.frontier), opTag))
    let s_post₁ : Memory.State :=
      { mem := clear sps₁.mem (st₁.frontier - k_sh) k_sh, frontier := st₁.frontier - k_sh }
    ∃ (s_src1 s_dst1 : Fin U → Option (Fin V)) (extra : List (EpochUpdate U V)),
      ∀ {L₂ : DualLatent c U V} {s₂ : Memory.State},
        DualStateInv c U V w base s_dict L₂ s₂ →
        Coupled8 c V w base (Dictionary.dom s_dict).card s₁ s₂ →
        L₂.slotSrc = L₁.slotSrc →
        L₂.slotDst.s_abs = L₁.slotDst.s_abs →
        L₂.slotDst.evs = L₁.slotDst.evs →
        let sp₂ :=
          (Memory.spec 0).clientState s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val))
        let sg₂ : Memory.State := { mem := sp₂.mem, frontier := s₂.frontier + k_grow }
        let st₂ := (Memory.spec 0).clientState sg₂
          (stepOpProg (((base, sg₂.frontier), opTag), (u.val, v_val)))
        let sps₂ :=
          (Memory.spec 0).clientState st₂ (postRandShrinkProg ((base, st₂.frontier), opTag))
        let s_post₂ : Memory.State :=
          { mem := clear sps₂.mem (st₂.frontier - k_sh) k_sh, frontier := st₂.frontier - k_sh }
        let slSrc_p : SlotLatent c U V :=
          ⟨L₁.slotSrc.nCap, s_src1, L₁.slotSrc.seeds, L₁.slotSrc.evs⟩
        let slDst_p₂ : SlotLatent c U V :=
          ⟨L₂.slotDst.nCap, s_dst1, L₂.slotDst.seeds,
            (L₁.slotDst.applyFG false opTag u v).evs ++ extra⟩
        (∃ L_post₂ : DualLatent c U V,
          L_post₂.slotSrc = slSrc_p ∧
          L_post₂.slotDst = slDst_p₂ ∧
          DualStateInv c U V w base s_dict' L_post₂ s_post₂ ∧
          memoryCost (prepGrowProg (((base, s₂.frontier), opTag), u.val)) s₂ ≤ 40 ∧
          memoryCost (postRandShrinkProg ((base, st₂.frontier), opTag)) st₂ ≤ 35 ∧
          (L₁.slotSrc.GoodCovers → slDst_p₂.GoodCovers →
            memoryCost (stepOpProg (((base, sg₂.frontier), opTag), (u.val, v_val))) sg₂ ≤
              (2 * epochStepCost c + 80) + (itemBatchWhp * (2 * epochStepCost c + 20) + 20000))) ∧
        ((s_post₁.mem (base + hdrPhase) = 8 ∧
            Coupled8 c V w base (Dictionary.dom s_dict').card s_post₁ s_post₂) ∨
         (s_post₁.mem (base + hdrPhase) = 9 ∧ SchedEq base s_post₁ s_post₂)) := by
  dsimp only
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmid₁, hpt₁, _, _⟩ :=
    stepOpProg_mutate_spec h₁ hop_nz u v hv_eq hsucc_fits' hpad_fits'
  dsimp only at hmid₁ hpt₁
  have hfg₁ := fgStep_eq8_aux h₁ u v hv_eq (fgSetup_of_dualStateInv h₁ hop_nz u v) rfl rfl rfl hp8
  have hsm₁_ph :
      ((Memory.spec 0).clientState
        { mem := ((Memory.spec 0).clientState s₁
            (prepGrowProg (((base, s₁.frontier), opTag), u.val))).mem
          frontier := s₁.frontier +
            (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)) }
        (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrPhase) = 8 :=
    (hfg₁.2.2.2.1 (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))).trans hp8
  set sm₁ := (Memory.spec 0).clientState
    { mem := ((Memory.spec 0).clientState s₁
        (prepGrowProg (((base, s₁.frontier), opTag), u.val))).mem
      frontier := s₁.frontier +
        (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)) }
    (userMutateProg ((base, opTag), (u.val, v_val)))
  set Lm₁ := L₁.applyFG (s₁.mem (base + hdrPhase)) opTag u v
  change DualMidInv _ _ _ _ _ _ Lm₁ sm₁ at hmid₁
  change sm₁.mem (base + hdrPhase) = 8 at hsm₁_ph
  -- Extract `migrateBatchProg_coupled` on `sm₁` once for all `(L₂, s₂)`!
  have hsched_m₁ := hmid₁.sched; rw [ite_eq_right (by omega)] at hsched_m₁
  obtain ⟨hmDst_eq₁, hpad_eq₁, _, _, _, _⟩ := hsched_m₁.ge2 (by omega)
  obtain ⟨hcap_s₁, hcap_d₁, hdj_m₁, hdict_or₁, _, hsl_sm₁, hsl_dm₁, _, _⟩ := hmid₁.sl_8 hsm₁_ph
  obtain ⟨_, hdst_safe₁⟩ := dualCoreInv_cap_safe hmid₁
  rw [ite_eq_right (by omega)] at hdst_safe₁
  set pSrc := dualPSrc base sm₁.mem
  set pDst := if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
  have hpD_m₁ : dualPDst base sm₁.mem = pDst := by
    unfold dualPDst; rw [hsm₁_ph, ite_eq_left (by decide : 8 < 10)]
  rw [hpD_m₁] at hsl_dm₁
  have hp_disj : pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc := by
    unfold pSrc dualPSrc; dsimp only [pDst, hdrPBase0, hdrPBase1]
    split_ifs <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
  have hpm_s : pDst + 64 ≤ dualMbSrc base sm₁.mem ∨
      dualMbSrc base sm₁.mem +
        (if Lm₁.slotSrc.nCap = 0 then 2 else offPageDir c w Lm₁.slotSrc.nCap) ≤ pDst := by
    rw [hcap_s₁]; unfold dualMbSrc dualCapSrc
    dsimp only [pDst, hdrPBase0, hdrPBase1, hdrSmallMeta0]
    by_cases hst0 : sm₁.mem (base + hdrStage) = 0
    · simp only [hst0, ↓reduceIte]; split_ifs <;> [exact Or.inr (by omega); exact Or.inl (by omega)]
    · simp only [hst0, ↓reduceIte]; exact Or.inl (by omega)
  have hpm_d : pSrc + 64 ≤ dualMbDst base sm₁.mem ∨
      dualMbDst base sm₁.mem +
        (if Lm₁.slotDst.nCap = 0 then 2 else offPageDir c w Lm₁.slotDst.nCap) ≤ pSrc := by
    rw [hcap_d₁]; unfold dualMbDst pSrc dualPSrc
    rw [hsm₁_ph, ite_eq_left (by decide : 8 < 10)]
    dsimp only [hdrPBase0, hdrPBase1, hdrSmallMeta1]
    by_cases hd0 : sm₁.mem (base + hdrNDst) = 0
    · simp only [hd0, ↓reduceIte]; split_ifs <;> exact Or.inr (by omega)
    · simp only [hd0, ↓reduceIte]; split_ifs <;> exact Or.inl (by omega)
  have hmm_disj :
      dualMbSrc base sm₁.mem +
        (if Lm₁.slotSrc.nCap = 0 then 2 else offPageDir c w Lm₁.slotSrc.nCap) ≤
          dualMbDst base sm₁.mem ∨
      dualMbDst base sm₁.mem +
        (if Lm₁.slotDst.nCap = 0 then 2 else offPageDir c w Lm₁.slotDst.nCap) ≤
          dualMbSrc base sm₁.mem := by
    rw [hcap_s₁, hcap_d₁]; unfold dualMbSrc dualMbDst dualCapSrc
    rw [hsm₁_ph, ite_eq_left (by decide : 8 < 10)]
    dsimp only [hdrSmallMeta0, hdrSmallMeta1]
    by_cases hd0 : sm₁.mem (base + hdrNDst) = 0
    · obtain ⟨hs_pos, hst0, _⟩ := hsched_m₁.nDst_zero hd0
      simp only [hd0, hst0, hs_pos.ne', ↓reduceIte]; exact Or.inr (by omega)
    · simp only [hd0, ↓reduceIte]
      by_cases hst0 : sm₁.mem (base + hdrStage) = 0
      · simp only [hst0, ↓reduceIte]
        by_cases hs0 : sm₁.mem (base + hdrNSrc) = 0
        · simp only [hs0, ↓reduceIte]; exact Or.inl (by omega)
        · have hth_s := (hmid₁.nSrc_bounds.resolve_left hs0).1
          have hod_s := (epochMeta_offsets_le (w := w) hth_s).2.2.2
          have hmS_p : sm₁.mem (base + hdrMSrc) ≤ sm₁.mem (base + hdrPad) := by
            rw [hpad_eq₁]; exact le_max_left _ _
          rw [← hmid₁.mSrc_eq] at hod_s
          simp only [hs0, ↓reduceIte]; exact Or.inl (by omega)
      · have hth_d := (hsched_m₁.nDst_bounds.resolve_left hd0).1
        have hod_d := (epochMeta_offsets_le (w := w) hth_d).2.2.2
        have hmD_p : sm₁.mem (base + hdrMDst) ≤ sm₁.mem (base + hdrPad) := by
          rw [hpad_eq₁]; exact le_max_right _ _
        rw [← hmDst_eq₁] at hod_d
        simp only [hst0, ↓reduceIte]; exact Or.inr (by omega)
  have hsum_m₁ : (liveDom Lm₁.slotDst.s_abs).card + (liveDom Lm₁.slotSrc.s_abs).card =
      (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none)).card := by
    rw [← liveDom_orOpt_card hdj_m₁, ← dom_toDictState_card, hdict_or₁]
  have hcap_d_m₁ : Lm₁.slotDst.nCap ≠ 0 →
      (liveDom Lm₁.slotDst.s_abs).card + (liveDom Lm₁.slotSrc.s_abs).card ≤ Lm₁.slotDst.nCap :=
    fun hne => by
      have hd_nz : sm₁.mem (base + hdrNDst) ≠ 0 := hcap_d₁ ▸ hne
      unfold EpochCapSafe at hdst_safe₁; rw [ite_eq_right hd_nz] at hdst_safe₁
      rw [hsum_m₁, hcap_d₁]; exact hdst_safe₁.2.2.2
  have hcap_pg_m₁ : (liveDom Lm₁.slotDst.s_abs).card + (liveDom Lm₁.slotSrc.s_abs).card ≤
      (dualPgHost c V w base
        (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
          else Function.update s_dict u none)).card sm₁.mem).nCap := by
    rw [hsum_m₁]; exact le_rfl
  obtain ⟨s_src1, s_dst1, extra, hcd1, hsum1, hdj1, hor1, _, _, hfr_s1_₁, hbatch_all⟩ :=
    migrateBatchProg_coupled hsl_sm₁ hsl_dm₁ hdj_m₁ hp_disj hpm_s hpm_d hmm_disj
      hcap_d_m₁ hcap_pg_m₁ itemBatchWhp
  have hsub_c8_m₁ : ∀ addr,
      SlotSrcMetaRegion c w pSrc (dualMbSrc base sm₁.mem) Lm₁.slotSrc.nCap addr →
      Coupled8Region c w base sm₁.mem addr := by
    rw [hcap_s₁]; exact fun _ h => h
  obtain ⟨hno_d_pSrc, hno_d_mSrc⟩ :=
    not_paged_slotOwnsAddr_partner (sbA := 1) (slA := Lm₁.slotDst) hsl_sm₁ hpm_d hmm_disj.symm
  have hdisj_c8_dm₁ : ∀ addr, Coupled8Region c w base sm₁.mem addr →
      ¬slotOwnsAddr c w (dualMbDst base sm₁.mem) Lm₁.slotDst.nCap
        (pagedSlotIo 1 (dualPgHost c V w base
          (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
            else Function.update s_dict u none)).card sm₁.mem)) addr := by
    intro addr hreg
    rcases hreg with ⟨g1, g2⟩ | hm
    · exact hno_d_pSrc addr g1 g2
    · exact hno_d_mSrc addr (hcap_s₁.symm ▸ hm)
  -- Self-apply `hbatch_all` to `sm₁` to obtain `hout_s1_₁`!
  have hc_self_m₁ : SlotStateCoupled (Coupled8Region c w base sm₁.mem)
      (pagedSlotIo 0 (dualPgHost c V w base
        (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
          else Function.update s_dict u none)).card sm₁.mem))
      (sm₁.mem (dualMbSrc base sm₁.mem + 1)) sm₁ sm₁ :=
    { fr_eq := rfl
      side_zero := rfl
      valid₁ := by
        have hv := hsl_sm₁.io_valid
        have hw_pg : (pagedSlotIo 0 (dualPgHost c V w base
          (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
            else Function.update s_dict u none)).card sm₁.mem)).pgL.w = w := rfl
        rwa [hw_pg]
      disj := fun addr hreg => by
        have hraw := hsl_sm₁; unfold EpochSlotInv at hraw
        rcases hreg with ⟨g1, g2⟩ | hm
        · by_cases hc0 : Lm₁.slotSrc.nCap = 0
          · rw [ite_eq_left hc0] at hraw
            exact fun hia => hraw.2.2.2.2.1 addr g1 g2 (Or.inr (Or.inr hia))
          · rw [ite_eq_right hc0] at hraw; exact hraw.1.disj_pBase_io addr g1 g2
        · rw [← hcap_s₁] at hm; unfold slotOwnsNonPageMeta at hm
          by_cases hc0 : Lm₁.slotSrc.nCap = 0
          · rw [ite_eq_left hc0] at hraw hm
            rcases hm with ⟨g1, g2⟩ | ⟨hne, _⟩
            · exact hraw.2.2.1.disjoint_hdr addr (by dsimp only; clear *- g1 g2; omega)
            · exact absurd hc0 hne
          · rw [ite_eq_right hc0] at hraw hm
            exact hraw.1.disj_fast_io addr (hm.imp id And.right)
      mem_eq := fun _ _ => rfl
      inv₁ := hsl_sm₁.io_stateInv
      inv₂ := hsl_sm₁.io_stateInv
      pair_eq := fun _ _ => rfl }
  obtain ⟨_, _, _, _, _, hout_s1_₁, _⟩ :=
    hbatch_all rfl rfl hsl_sm₁ hsl_dm₁ hsub_c8_m₁ hdisj_c8_dm₁ hc_self_m₁
  have hLm₁_src : Lm₁.slotSrc =
      ⟨L₁.slotSrc.nCap, Function.update L₁.slotSrc.s_abs u none,
        L₁.slotSrc.seeds, L₁.slotSrc.evs⟩ := by
    dsimp only [Lm₁]; rw [hp8]; unfold DualLatent.applyFG SlotLatent.applyFG
    simp only [Nat.reduceLeDiff, ↓reduceIte]
    split_ifs <;> rfl
  have hLm₁_dst : Lm₁.slotDst = L₁.slotDst.applyFG false opTag u v := by
    dsimp only [Lm₁]; rw [hp8]; unfold DualLatent.applyFG; simp only [Nat.reduceLeDiff, ↓reduceIte]
  refine ⟨s_src1, s_dst1, extra, ?_⟩
  intro L₂ s₂ h₂ hc8 hsrc_eq hdst_abs_eq hdst_evs_eq
  have hsch := hc8.1
  have hp8_₂ : s₂.mem (base + hdrPhase) = 8 :=
    (hsch.2 hdrPhase (by decide) (by decide)).symm.trans hp8
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
  obtain ⟨hkg_eq, hc8_mid⟩ :=
    fg8_coupled_step_aux h₁ h₂ hc8 hp8 hop_nz u v hv_eq rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨_, _, _, hmc_pg₂, _, _, _, _, _, _, hmid₂, hpt₂, hmc_so₂, hmc_um₂⟩ :=
    stepOpProg_mutate_spec h₂ hop_nz u v hv_eq hsucc_fits' hpad_fits₂
  dsimp only at hmc_pg₂ hmid₂ hpt₂ hmc_so₂ hmc_um₂
  rw [← hkg_eq] at hc8_mid hmid₂ hpt₂ hmc_so₂ hmc_um₂
  obtain ⟨_, _, _, hpost_sch_ne5, _⟩ :=
    schedEq_mutate_step (v_val := v_val) h₁ h₂ hsch hop_nz u v hv_eq hsucc_fits' hpad_fits'
  obtain ⟨hksh_eq, hsch_post⟩ := hpost_sch_ne5 (by omega)
  dsimp only at hksh_eq hsch_post
  rw [← hkg_eq] at hksh_eq hsch_post
  rw [← hksh_eq] at hsch_post
  have hfg₂ := fgStep_eq8_aux h₂ u v hv_eq (fgSetup_of_dualStateInv h₂ hop_nz u v)
    rfl hkg_eq rfl hp8_₂
  have hsm₂_ph := (hc8_mid.1.2 hdrPhase (by decide) (by decide)).symm.trans hsm₁_ph
  have hpt₁_br := hpt₁.2.2.2; rw [ite_eq_left (by rw [hsm₁_ph]; decide)] at hpt₁_br
  have hpt₂_br := hpt₂.2.2.2; rw [ite_eq_left (by rw [hsm₂_ph]; decide)] at hpt₂_br
  obtain ⟨_, _, _, hpre₁, _⟩ := hpt₁_br
  obtain ⟨_, _, _, hpre₂, _⟩ := hpt₂_br
  obtain ⟨_, _, _, _, _, _, _, _, h_any₁⟩ :=
    postRandShrinkProg_spec_pre (opTag := opTag) hop_nz hpre₁
  obtain ⟨_, _, _, _, _, hmc_prs₂, _, _, h_any₂⟩ :=
    postRandShrinkProg_spec_pre (opTag := opTag) hop_nz hpre₂
  rw [← hksh_eq] at h_any₂
  -- `sps₁ = st₁` and `sps₂ = st₂` since `st.mem (base + hdrPhase) ∈ {8, 9}` (`≠ 5, ≠ 11`)
  have hsps_id : ∀ {st : Memory.State} {Lt : DualLatent c U V},
      DualPreShrinkInv c U V w base
        (if opTag = 1 then Function.update s_dict u (some v.val)
         else Function.update s_dict u none) Lt st →
      (st.mem (base + hdrPhase) = 8 ∨ st.mem (base + hdrPhase) = 9) →
      (Memory.spec 0).clientState st (postRandShrinkProg ((base, st.frontier), opTag)) = st := by
    intro st Lt hpre hp89
    have hbr := hpre.2.2.2
    rw [ite_eq_right (by rcases hp89 with h | h <;> omega),
      ite_eq_right (by rcases hp89 with h | h <;> omega),
      ite_eq_left (by rcases hp89 with h | h <;> omega)] at hbr
    have hw_st : st.mem (base + hdrW) = w := hbr.2.2.hdr.2.2.1
    have hw_pos : 0 < w := by have := h₁.hw11; omega
    obtain ⟨hs1, _, _⟩ := postRandShrinkProg_eval base st.frontier opTag st
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hs1
    rw [ite_eq_right hop_nz,
      ite_eq_right (fun h => by rcases hp89 with hp | hp <;> (have := h.1; omega))] at hs1
    obtain ⟨hc_s, _, _⟩ := calcPostShrinkProg_eval (curFr := st.frontier) (hw_st ▸ hw_pos)
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hc_s
    rw [ite_eq_right (fun h => by rcases hp89 with hp | hp <;> (have := h.1; omega))] at hc_s
    exact hs1.trans hc_s
  have hst₁_bg :
      (Memory.spec 0).clientState
        { mem := ((Memory.spec 0).clientState s₁
            (prepGrowProg (((base, s₁.frontier), opTag), u.val))).mem
          frontier := s₁.frontier +
            (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)) }
        (stepOpProg
          (((base, s₁.frontier +
              (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))),
            opTag), (u.val, v_val))) =
      (Memory.spec 0).clientState sm₁ (bgTickProg (base, sm₁.frontier)) := by
    rw [(stepOpProg_eval _ _ _ _ _ _).1, ite_eq_right hop_nz, hfg₁.2.1]
  have hst₂_bg :
      (Memory.spec 0).clientState
        { mem := ((Memory.spec 0).clientState s₂
            (prepGrowProg (((base, s₂.frontier), opTag), u.val))).mem
          frontier := s₂.frontier +
            (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)) }
        (stepOpProg
          (((base, s₂.frontier +
              (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))),
            opTag), (u.val, v_val))) =
      (Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          { mem := ((Memory.spec 0).clientState s₂
              (prepGrowProg (((base, s₂.frontier), opTag), u.val))).mem
            frontier := s₂.frontier +
              (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)) }
          (userMutateProg ((base, opTag), (u.val, v_val))))
        (bgTickProg (base,
          ((Memory.spec 0).clientState
            { mem := ((Memory.spec 0).clientState s₂
                (prepGrowProg (((base, s₂.frontier), opTag), u.val))).mem
              frontier := s₂.frontier +
                (Memory.spec 0).clientResult s₁
                  (prepGrowProg (((base, s₁.frontier), opTag), u.val)) }
            (userMutateProg ((base, opTag), (u.val, v_val)))).frontier)) := by
    rw [(stepOpProg_eval _ _ _ _ _ _).1, ite_eq_right hop_nz, hfg₂.2.1]
  -- Check `st₁.mem (base + hdrPhase) ∈ {8, 9}` and `st₂.mem (base + hdrPhase) ∈ {8, 9}`
  have hst₁_ph89 :
      ((Memory.spec 0).clientState sm₁ (bgTickProg (base, sm₁.frontier))).mem (base + hdrPhase) =
        8 ∨
      ((Memory.spec 0).clientState sm₁ (bgTickProg (base, sm₁.frontier))).mem (base + hdrPhase) =
        9 := by
    obtain ⟨hth_h₁, _, _, _, hctx0_₁, _, _, _, _⟩ :=
      dualPgHost_eval_valid hmid₁ (by omega) (by omega)
    have hdisj_pg₁ := disjoint_pgHost_nonPageMeta
      (nc := (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none)).card) hmid₁ (by omega) (by omega)
    have hth_U : whpThreshold c ≤ U := hth_h₁.1.trans hth_h₁.2
    have hth_hdr₁ : sm₁.mem (base + hdrThresh) = whpThreshold c := by
      simpa only [hth_U, ↓reduceIte] using hmid₁.hdr.2.2.2.2.2.1
    have hibHi_ge : base + 196 ≤ sm₁.mem (base + hdrItemHi) := by
      rw [(hsched_m₁.ge2 (by omega)).2.2.2.2.1]; split_ifs <;> omega
    have hmb_ge192 : base + 192 ≤ dualMbHost base sm₁.mem := by
      unfold dualMbHost; split_ifs <;> omega
    have hs1₁_hdr48 : ∀ off < 48,
        ((Memory.spec 0).clientState sm₁
          (migrateBatchProg (((pSrc, pDst), 0), itemBatchWhp))).mem (base + off) =
        sm₁.mem (base + off) := fun off h48 =>
      hout_s1_₁ (base + off)
        (fun hown => by
          have hb := slotOwnsAddr_bounds (pBase := pSrc)
            (fun h0 => by
              rw [hcap_s₁] at h0; unfold dualMbSrc dualCapSrc at *
              by_cases hst0 : sm₁.mem (base + hdrStage) = 0
              · simp only [hst0, ↓reduceIte] at h0 ⊢; rw [ite_eq_left h0]; exact Or.inl rfl
              · simp only [hst0, ↓reduceIte] at h0
                exact absurd h0 (fun hd0 => hst0 (hsched_m₁.nDst_zero hd0).2.1))
            (fun hne => by
              rw [hcap_s₁] at hne; unfold dualMbSrc dualCapSrc at *
              by_cases hst0 : sm₁.mem (base + hdrStage) = 0
              · simp only [hst0, ↓reduceIte] at hne ⊢; rw [ite_eq_right hne]; exact Or.inl rfl
              · simp only [hst0, ↓reduceIte]; exact Or.inr rfl)
            (fun _ => ⟨hmb_ge192, by change base + 192 ≤ sm₁.mem (base + hdrItemHi); omega⟩)
            (fun h0 => absurd h0 Nat.one_ne_zero)
            (fun h0 => absurd h0 Nat.one_ne_zero) _ hown
          exact absurd (hb.2.1 (by omega)).2.1 Nat.one_ne_zero)
        (fun hown => by
          have hb := slotOwnsAddr_bounds (pBase := pDst)
            (fun h0 => by
              rw [hcap_d₁] at h0; unfold dualMbDst
              rw [hsm₁_ph, ite_eq_left (by decide : 8 < 10), ite_eq_left h0]; exact Or.inr rfl)
            (fun hne => by
              rw [hcap_d₁] at hne; unfold dualMbDst
              rw [hsm₁_ph, ite_eq_left (by decide : 8 < 10), ite_eq_right hne]
              split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl])
            (fun _ => ⟨hmb_ge192, by change base + 192 ≤ sm₁.mem (base + hdrItemHi); omega⟩)
            (fun h0 => absurd h0 Nat.one_ne_zero)
            (fun h0 => absurd h0 Nat.one_ne_zero) _ hown
          exact absurd (hb.2.1 (by omega)).2.1 Nat.one_ne_zero)
    have hctx0_s1₁ : (Memory.spec 0).clientResult
        ((Memory.spec 0).clientState sm₁ (migrateBatchProg (((pSrc, pDst), 0), itemBatchWhp)))
        (loadHostCtxProg (base, 0)) =
        (dualPgHost c V w base
          (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
            else Function.update s_dict u none)).card sm₁.mem).toCtx := by
      rw [← hctx0_₁, (loadHostCtxProg_eval base 0 _).2.1, (loadHostCtxProg_eval base 0 sm₁).2.1]
      simp only [↓reduceIte]
      have h_od : ∀ k ≤ 4,
          ((Memory.spec 0).clientState sm₁
            (migrateBatchProg (((pSrc, pDst), 0), itemBatchWhp))).mem
            (base + (if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) =
          sm₁.mem (base + (if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) :=
        fun k hk => by
          rw [Nat.add_assoc]
          exact hs1₁_hdr48 _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> omega)
      rw [hs1₁_hdr48 hdrStage (by decide), hs1₁_hdr48 hdrNDst (by decide),
        hs1₁_hdr48 hdrPad (by decide), hs1₁_hdr48 hdrW (by decide),
        hs1₁_hdr48 hdrItemHi (by decide), hs1₁_hdr48 hdrQHi (by decide),
        hs1₁_hdr48 hdrValBits (by decide), hs1₁_hdr48 hdrLive (by decide),
        show ((Memory.spec 0).clientState sm₁
            (migrateBatchProg (((pSrc, pDst), 0), itemBatchWhp))).mem
            (base + if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) =
          sm₁.mem (base + if sm₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) by
          simpa only [Nat.add_zero] using h_od 0 (by decide),
        h_od 1 (by decide), h_od 2 (by decide), h_od 3 (by decide), h_od 4 (by decide)]
    have hbgev := (bgTickProg_eval base sm₁.frontier sm₁).1
    simp only [hsm₁_ph, Nat.reduceEqDiff, ↓reduceIte] at hbgev
    have htmev := (tickMigrateProg_eval base sm₁).1
    rw [show (if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1) =
        pSrc from rfl,
      show (if sm₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
        pDst from rfl,
      hctx0_s1₁, PageArenaLayout.ofCtx_toCtx, hth_hdr₁] at htmev
    rw [hbgev, htmev]
    by_cases hrem : 1 < sm₁.mem (base + hdrRem)
    · rw [ite_eq_left hrem]; left; dsimp only [Memory.State.mem]
      rw [Function.update_of_ne (base_add_ne (by decide))]
      exact (hs1₁_hdr48 hdrPhase (by decide)).trans hsm₁_ph
    · rw [ite_eq_right hrem]; right; dsimp only [Memory.State.mem]; exact Function.update_self ..
  -- Instantiate `hbatch_all` on `sm₂`!
  set sm₂ := (Memory.spec 0).clientState
    { mem := ((Memory.spec 0).clientState s₂
        (prepGrowProg (((base, s₂.frontier), opTag), u.val))).mem
      frontier := s₂.frontier +
        (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)) }
    (userMutateProg ((base, opTag), (u.val, v_val)))
  set Lm₂ := L₂.applyFG (s₂.mem (base + hdrPhase)) opTag u v
  have hLm₂_src : Lm₂.slotSrc = Lm₁.slotSrc := by
    dsimp only [Lm₂, Lm₁]; rw [hp8_₂, hp8]; unfold DualLatent.applyFG SlotLatent.applyFG
    simp only [Nat.reduceLeDiff, ↓reduceIte]
    split_ifs <;> rw [hsrc_eq]
  have hLm₂_dst_abs : Lm₂.slotDst.s_abs = Lm₁.slotDst.s_abs := by
    dsimp only [Lm₂, Lm₁]; rw [hp8_₂, hp8]; unfold DualLatent.applyFG SlotLatent.applyFG
    simp only [Nat.reduceLeDiff, ↓reduceIte]
    split_ifs <;> rw [hdst_abs_eq]
  have hLm₂_dst_evs : Lm₂.slotDst.evs = Lm₁.slotDst.evs := by
    dsimp only [Lm₂, Lm₁]; rw [hp8_₂, hp8]; unfold DualLatent.applyFG SlotLatent.applyFG
    simp only [Nat.reduceLeDiff, ↓reduceIte]
    split_ifs <;> rw [hdst_evs_eq]
  obtain ⟨_, hcap_d_m₂, _, _, _, hsl_sm₂, hsl_dm₂, _, _⟩ := hmid₂.sl_8 hsm₂_ph
  have hnc_dm : Lm₂.slotDst.nCap = Lm₁.slotDst.nCap := by
    rw [hcap_d_m₂, hcap_d₁, hc8_mid.1.2 hdrNDst (by decide) (by decide)]
  have hpS_m₂ : dualPSrc base sm₂.mem = pSrc := by
    unfold dualPSrc pSrc; rw [← hc8_mid.1.2 hdrStage (by decide) (by decide)]
  have hmbS_m₂ : dualMbSrc base sm₂.mem = dualMbSrc base sm₁.mem := by
    unfold dualMbSrc
    rw [← hc8_mid.1.2 hdrStage (by decide) (by decide),
      ← hc8_mid.1.2 hdrNSrc (by decide) (by decide),
      ← hc8_mid.1.2 hdrPad (by decide) (by decide)]
  have hpD_m₂ : dualPDst base sm₂.mem = pDst := by
    unfold dualPDst; rw [hsm₂_ph, ite_eq_left (by decide : 8 < 10),
      ← hc8_mid.1.2 hdrStage (by decide) (by decide)]
  have hmbD_m₂ : dualMbDst base sm₂.mem = dualMbDst base sm₁.mem := by
    unfold dualMbDst
    simp only [hsm₂_ph, hsm₁_ph, Nat.reduceLT, ↓reduceIte]
    rw [← hc8_mid.1.2 hdrNDst (by decide) (by decide),
      ← hc8_mid.1.2 hdrStage (by decide) (by decide),
      ← hc8_mid.1.2 hdrPad (by decide) (by decide)]
  have hpgH_m₂ : dualPgHost c V w base
      (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none)).card sm₂.mem =
      dualPgHost c V w base
        (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
          else Function.update s_dict u none)).card sm₁.mem := by
    unfold dualPgHost dualNHost dualMbHost
    rw [← hc8_mid.1.2 hdrNDst (by decide) (by decide),
      ← hc8_mid.1.2 hdrNSrc (by decide) (by decide),
      ← hc8_mid.1.2 hdrStage (by decide) (by decide),
      ← hc8_mid.1.2 hdrPad (by decide) (by decide),
      ← hc8_mid.1.2 hdrItemHi (by decide) (by decide),
      ← hc8_mid.1.2 hdrQHi (by decide) (by decide)]
  rw [hpS_m₂, hmbS_m₂, hpgH_m₂, hLm₂_src] at hsl_sm₂
  rw [hpD_m₂, hmbD_m₂, hpgH_m₂] at hsl_dm₂
  obtain ⟨_, hfr_s1_₂, hs1_₂, hd1_₂, hc_s1, hout_s1_₂, hmc_mb_₂⟩ :=
    hbatch_all hnc_dm hLm₂_dst_abs hsl_sm₂ hsl_dm₂ hsub_c8_m₁ hdisj_c8_dm₁ hc8_mid.2
  have hsch_tick := (schedEq_mutate_step (v_val := v_val) h₁ h₂ hsch hop_nz u v hv_eq
    hsucc_fits' hpad_fits').2.2.1
  dsimp only at hsch_tick
  rw [← hkg_eq] at hsch_tick
  have hst₂_ph89 :
      ((Memory.spec 0).clientState
        { mem := ((Memory.spec 0).clientState s₂
            (prepGrowProg (((base, s₂.frontier), opTag), u.val))).mem
          frontier := s₂.frontier +
            (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)) }
        (stepOpProg
          (((base, s₂.frontier +
              (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))),
            opTag), (u.val, v_val)))).mem (base + hdrPhase) = 8 ∨
      ((Memory.spec 0).clientState
        { mem := ((Memory.spec 0).clientState s₂
            (prepGrowProg (((base, s₂.frontier), opTag), u.val))).mem
          frontier := s₂.frontier +
            (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)) }
        (stepOpProg
          (((base, s₂.frontier +
              (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))),
            opTag), (u.val, v_val)))).mem (base + hdrPhase) = 9 := by
    rw [← hsch_tick.2 hdrPhase (by decide) (by decide), hst₁_bg]
    exact hst₁_ph89
  have hsps₁_id := hsps_id hpre₁ (by rwa [hst₁_bg])
  have hsps₂_id := hsps_id hpre₂ hst₂_ph89
  obtain ⟨⟨L_post₂, hs_eq_p, hd_eq_p, hinv_p₂, hmc_bg₂⟩, hout_branch⟩ :=
    coupled8_tick_step_aux hop_nz hsm₁_ph hc8_mid hmid₁ hmid₂
      hLm₂_src hLm₂_dst_abs hLm₂_dst_evs hcd1 hsum1 hdj1 hor1
      hs1_₂ hd1_₂ hc_s1 hfr_s1_₁ hout_s1_₁ hfr_s1_₂ hout_s1_₂ hmc_mb_₂
      hst₁_bg hst₂_bg hsps₁_id hsps₂_id rfl rfl hsch_post h_any₁ h_any₂
  have hnc_s_m₁ : Lm₁.slotSrc.nCap = L₁.slotSrc.nCap := by rw [hLm₁_src]
  have hsd_s_m₁ : HEq Lm₁.slotSrc.seeds L₁.slotSrc.seeds := by rw [hLm₁_src]
  have hev_s_m₁ : Lm₁.slotSrc.evs = L₁.slotSrc.evs := by rw [hLm₁_src]
  have hslSrc_p_eq : (⟨Lm₁.slotSrc.nCap, s_src1, Lm₁.slotSrc.seeds, Lm₁.slotSrc.evs⟩ :
      SlotLatent c U V) = ⟨L₁.slotSrc.nCap, s_src1, L₁.slotSrc.seeds, L₁.slotSrc.evs⟩ := by
    rw [hLm₁_src]
  have hLm₂_dst : Lm₂.slotDst = L₂.slotDst.applyFG false opTag u v := by
    dsimp only [Lm₂]; rw [hp8_₂]; unfold DualLatent.applyFG
    simp only [Nat.reduceLeDiff, ↓reduceIte]
  have hLm₂_dst_rec :
      Lm₂.slotDst = ⟨L₂.slotDst.nCap, Lm₂.slotDst.s_abs, L₂.slotDst.seeds, Lm₂.slotDst.evs⟩ := by
    rw [hLm₂_dst]; unfold SlotLatent.applyFG
    by_cases hop1 : opTag = 1
    · rw [ite_eq_left hop1, ite_eq_right Bool.false_ne_true]
    · rw [ite_eq_right hop1]
  have hslDst_p₂_eq : (⟨Lm₂.slotDst.nCap, s_dst1, Lm₂.slotDst.seeds, Lm₁.slotDst.evs ++ extra⟩ :
      SlotLatent c U V) =
      ⟨L₂.slotDst.nCap, s_dst1, L₂.slotDst.seeds,
        (L₁.slotDst.applyFG false opTag u v).evs ++ extra⟩ := by
    rw [hLm₂_dst_rec, hLm₁_dst]
  refine ⟨⟨L_post₂, hs_eq_p.trans hslSrc_p_eq, hd_eq_p.trans hslDst_p₂_eq, hinv_p₂,
    hmc_pg₂, hmc_prs₂, fun hg_s hg_d => ?_⟩, hout_branch⟩
  have hg_s_m₁ : Lm₁.slotSrc.GoodCovers := by
    rw [hLm₁_src]; exact SlotLatent.GoodCovers.congr_abs _ hg_s
  have hg_s_m₂ : Lm₂.slotSrc.GoodCovers := hLm₂_src ▸ hg_s_m₁
  have hg_d_p : (⟨Lm₂.slotDst.nCap, s_dst1, Lm₂.slotDst.seeds, Lm₁.slotDst.evs ++ extra⟩ :
      SlotLatent c U V).GoodCovers := hslDst_p₂_eq ▸ hg_d
  have hg_d_m₂ : Lm₂.slotDst.GoodCovers := by
    have h1 : (⟨Lm₂.slotDst.nCap, Lm₂.slotDst.s_abs, Lm₂.slotDst.seeds,
        Lm₂.slotDst.evs ++ extra⟩ : SlotLatent c U V).GoodCovers := by
      rw [hLm₂_dst_evs]; exact SlotLatent.GoodCovers.congr_abs _ hg_d_p
    have h2 := SlotLatent.GoodCovers.of_append (s₁ := Lm₂.slotDst.s_abs) h1
    have heq_sl : (⟨Lm₂.slotDst.nCap, Lm₂.slotDst.s_abs, Lm₂.slotDst.seeds,
        Lm₂.slotDst.evs⟩ : SlotLatent c U V) = Lm₂.slotDst := by cases Lm₂.slotDst; rfl
    rwa [heq_sl] at h2
  have hc1 := hmc_um₂ (fun _ => hg_s_m₂) (fun _ => ⟨hg_s_m₂, hg_d_m₂⟩)
    (fun h9 => absurd (hp8_₂ ▸ h9) (by decide))
  have hc2 := hmc_bg₂ hg_s_m₁ hg_d_p
  rw [hmc_so₂]; exact Nat.add_le_add hc1 hc2

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
