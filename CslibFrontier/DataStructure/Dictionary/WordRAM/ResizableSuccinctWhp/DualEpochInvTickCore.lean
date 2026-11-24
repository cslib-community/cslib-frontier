/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvFG
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochStepEval

/-!
# Post-Tick Invariants and Background Tick Phases `0..1` (`DualEpochInvTickCore`)

Defines `extractEpochSeeds`, `DualPreShrinkInv`, and `DualPostTickInv`, provides uniform
shrunk-frontier and `setSlotIoProg` transport helpers (`EpochSlotInv.at_exact_frontier`,
`EpochSlotInv.set_slotIo`), and proves the Phase `0` (`tickIdleProg`) and Phase `1`
(`tickLogProg`) background tick specifications for
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024].

## Main definitions

* `extractEpochSeeds`: decodes `EpochHashSeeds c U N` from `[metaBase + offBktHash, ...)`.
* `DualPreShrinkInv`: unified pre-shrink invariant feeding `calcPostShrinkProg` + `shrinkCode`.
* `DualPostTickInv`: unified post-`bgTickProg` invariant feeding `randFillBatchCode`.

## Main results

* `EpochSlotInv.at_exact_frontier`, `EpochSlotInv.set_slotIo`
* `tickPhase0_spec`, `tickPhase1_spec`

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

/-! ## Section 1: Seed Extraction, `DualPreShrinkInv`, and `DualPostTickInv` -/

/-- Decodes `EpochHashSeeds c U N` from `[metaBase + offBktHash, metaBase + offBktMeta c w N)`. -/
@[expose] noncomputable def extractEpochSeeds (c U w N metaBase : ℕ) (mem : ℕ → ℕ) :
    EpochHashSeeds c U N :=
  ⟨BitPackedDoubleTabulation.extractSeed (metaBase + offBktHash) w (redWidthWhp U)
     (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) mem,
   BitPackedDoubleTabulation.extractSeed (metaBase + offFpHash c w N) w (redWidthWhp U)
     (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) mem⟩

/-- Provenance of active slot capacities, hash seeds, and event streams across non-randomizing
transitions (`isPh8` marks Phase `8` item migration; `isProm` marks `slotDst → slotSrc` promotion
at `9 → 4` Stage B or `11 → 0` rebuild completion). -/
@[expose] def PreservesEpochSeeds {c U V : ℕ} (isPh8 isProm : Prop)
    (L L' : DualLatent c U V) : Prop :=
  ((¬isProm →
      L'.slotSrc.nCap = L.slotSrc.nCap ∧ HEq L'.slotSrc.seeds L.slotSrc.seeds ∧
        L'.slotSrc.evs = L.slotSrc.evs) ∧
   (isProm →
      L'.slotSrc.nCap = L.slotDst.nCap ∧ HEq L'.slotSrc.seeds L.slotDst.seeds ∧
        L'.slotSrc.evs = L.slotDst.evs)) ∧
  (L'.slotDst.nCap = 0 ∨
    (L'.slotDst.nCap = L.slotDst.nCap ∧ HEq L'.slotDst.seeds L.slotDst.seeds ∧
      (∃ extra, L'.slotDst.evs = L.slotDst.evs ++ extra) ∧
      (¬isPh8 → L'.slotDst.evs = L.slotDst.evs)))

/-- Reflexivity of `PreservesEpochSeeds` when `¬isProm`. -/
theorem preservesEpochSeeds_refl {c U V : ℕ} {isPh8 isProm : Prop} (hnp : ¬isProm)
    (L : DualLatent c U V) :
    PreservesEpochSeeds isPh8 isProm L L :=
  ⟨⟨fun _ => ⟨rfl, HEq.rfl, rfl⟩, fun hp => absurd hp hnp⟩,
   Or.inr ⟨rfl, HEq.rfl, ⟨[], (List.append_nil _).symm⟩, fun _ => rfl⟩⟩

/-- Equality of `slotSrc` and `slotDst` implies `PreservesEpochSeeds` when `¬isProm`. -/
theorem preservesEpochSeeds_of_eq_slots {c U V : ℕ} {isPh8 isProm : Prop}
    {L L' : DualLatent c U V} (hnp : ¬isProm)
    (hs : L'.slotSrc = L.slotSrc) (hd : L'.slotDst = L.slotDst) :
    PreservesEpochSeeds isPh8 isProm L L' :=
  ⟨⟨fun _ => ⟨by rw [hs], by rw [hs], by rw [hs]⟩, fun hp => absurd hp hnp⟩,
   Or.inr ⟨by rw [hd], by rw [hd], ⟨[], by rw [hd, List.append_nil]⟩, fun _ => by rw [hd]⟩⟩

/-- Offset inequality lifts to `base + o₁ ≠ base + o₂`. -/
theorem base_add_ne {base o₁ o₂ : ℕ} (h : o₁ ≠ o₂) : base + o₁ ≠ base + o₂ := by omega

/-- Linear upper bound `pairStreamWords n qB vB w ≤ 2 * n + 3` when `qB + vB ≤ 2 * w`. -/
theorem pairStreamWords_le_two_mul_add_three {n qB vB w : ℕ}
    (hw_pos : 0 < w) (hsum : qB + vB ≤ 2 * w) :
    pairStreamWords n qB vB w ≤ 2 * n + 3 := by
  unfold pairStreamWords packedWords
  have hm : n * (qB + vB) + w - 1 ≤ w * (2 * n) + (w - 1) := by
    have h1 := Nat.mul_le_mul_left n hsum
    have h2 : n * (2 * w) = w * (2 * n) := by ring
    omega
  have hd := Nat.div_le_div_right (c := w) hm
  have hd_rhs : (w * (2 * n) + (w - 1)) / w = 2 * n := by
    rw [Nat.mul_add_div hw_pos, Nat.div_eq_of_lt (by omega)]; omega
  omega

/-- Pre-shrink invariant right before `calcPostShrinkProg` + `shrinkCode` (after
`finishRandFillProg` if `ph = 5` completed). Reduces directly to resting `DualStateInv` at the
target shrunk frontier. -/
@[expose] def DualPreShrinkInv (c U V w base : ℕ) (s_dict : Dictionary.State U)
    (L : DualLatent c U V) (s_pre : Memory.State) : Prop :=
  let nLive := (Dictionary.dom s_dict).card
  let ph := s_pre.mem (base + hdrPhase)
  let nSrc := s_pre.mem (base + hdrNSrc)
  let nDst := s_pre.mem (base + hdrNDst)
  let loFr := s_pre.mem (base + hdrItemLo) +
    pairStreamWords nLive (s_pre.mem (base + hdrQLo)) (valBits V) w
  let hiFr := s_pre.mem (base + hdrItemHi) +
    pairStreamWords nLive (s_pre.mem (base + hdrQHi)) (valBits V) w
  Memory.WellFormed w s_pre ∧
  s_pre.frontier ≤
    base + dualPaddedWords c U V w nSrc (if ph = 0 then nSrc else nDst) nLive ∧
  (ph = 5 → s_pre.mem (base + hdrCur) < s_pre.mem (dualPDst base s_pre.mem + 31)) ∧
  if ph < 2 then
    loFr ≤ s_pre.frontier ∧ s_pre.frontier - loFr ≤ bulkBatchWhp ∧
    DualStateInv c U V w base s_dict L { mem := s_pre.mem, frontier := loFr }
  else if ph = 2 then
    s_pre.frontier < hiFr ∧ DualStateInv c U V w base s_dict L s_pre
  else if ph ≤ 10 then
    hiFr ≤ s_pre.frontier ∧ s_pre.frontier - hiFr ≤ bulkBatchWhp ∧
    DualStateInv c U V w base s_dict L { mem := s_pre.mem, frontier := hiFr }
  else
    ph = 11 ∧ loFr ≤ s_pre.frontier ∧
    (bulkBatchWhp < s_pre.frontier - loFr →
      DualStateInv c U V w base s_dict L
        { mem := s_pre.mem, frontier := s_pre.frontier - bulkBatchWhp }) ∧
    (s_pre.frontier - loFr ≤ bulkBatchWhp →
      DualMidInv c U V w base s_dict { L with elapsed := L.elapsed - 1 } s_pre ∧
      1 ≤ L.elapsed ∧ 16 * L.elapsed ≤ max (whpThreshold c) nSrc)

/-- Unified post-`bgTickProg` invariant on `(s_tick, rArgs)` before `randFillBatchCode`. -/
@[expose] def DualPostTickInv (c U V w base : ℕ) (s_dict : Dictionary.State U)
    (L : DualLatent c U V) (s_mid s_tick : Memory.State) (rArgs : ℕ × (ℕ × ℕ)) : Prop :=
  s_tick.frontier = s_mid.frontier ∧
  Memory.WellFormed w s_tick ∧
  (∀ addr < base, s_tick.mem addr = s_mid.mem addr) ∧
  if s_mid.mem (base + hdrPhase) ≠ 5 then
    rArgs = (0, (0, 0)) ∧
    ∃ L' : DualLatent c U V,
      PreservesEpochSeeds (s_mid.mem (base + hdrPhase) = 8)
        (s_mid.mem (base + hdrPhase) = 9 ∧ s_tick.mem (base + hdrPhase) = 4) L L' ∧
      DualPreShrinkInv c U V w base s_dict L' s_tick ∧
      ((s_mid.mem (base + hdrPhase) = 8 → L.slotSrc.GoodCovers) →
        (s_mid.mem (base + hdrPhase) = 8 → L'.slotDst.GoodCovers) →
        memoryCost (bgTickProg (base, s_mid.frontier)) s_mid ≤
          itemBatchWhp * (2 * epochStepCost c + 20) + 20000)
  else
    let cur := s_mid.mem (base + hdrCur)
    let nDst := s_mid.mem (base + hdrNDst)
    let offBM := offBktMeta c w nDst
    let metaDst := dualMbDst base s_mid.mem
    let pDst := dualPDst base s_mid.mem
    let endOff := cur + min bulkBatchWhp (offBM - cur)
    0 < nDst ∧ 32 ≤ cur ∧ cur ≤ endOff ∧ endOff ≤ offBM ∧ endOff - cur ≤ bulkBatchWhp ∧
    rArgs = (metaDst + cur, (metaDst + endOff, 2 ^ w - 1)) ∧
    metaDst + endOff ≤ s_tick.frontier ∧
    memoryCost (bgTickProg (base, s_mid.frontier)) s_mid ≤ 20 ∧
    (∀ off, 32 ≤ off → off < cur → s_tick.mem (metaDst + off) = s_mid.mem (metaDst + off)) ∧
    ∀ words : Fin (endOff - cur) → Fin (2 ^ w),
      let s_rand : Memory.State :=
        { mem := writeWords s_tick.mem (metaDst + cur) words, frontier := s_tick.frontier }
      Memory.WellFormed w s_rand ∧
      (∀ addr < base, s_rand.mem addr = s_mid.mem addr) ∧
      s_rand.mem (base + hdrPhase) = 5 ∧
      s_rand.mem (base + hdrStage) = s_mid.mem (base + hdrStage) ∧
      s_rand.mem (base + hdrCur) = endOff ∧
      s_rand.mem (pDst + 31) = offBM ∧
      (endOff < offBM →
        DualPreShrinkInv c U V w base s_dict { L with elapsed := L.elapsed + 1 } s_rand) ∧
      (endOff = offBM → DualMidInv c U V w base s_dict L s_rand)

/-! ## Section 2: `EpochSlotInv` Shrunk-Frontier and `setSlotIoProg` Transport Helpers -/

/-- Adjusts the frontier parameter of `EpochSlotInv` to any `fr₂` covering `pBase`, `metaBase`,
and the active `io` item stream. -/
theorem EpochSlotInv.at_exact_frontier {c U V w fr₁ fr₂ pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr₁ pBase metaBase io slack draining sl mem)
    (hp_fr : pBase + 64 ≤ fr₂)
    (hm_fr :
      (if sl.nCap = 0 then metaBase + 2
       else metaBase + epochMetaWordsWhp c w sl.nCap) ≤ fr₂)
    (hio_fr :
      io.pgL.itemBase +
        pairStreamWords io.pgL.nCap
          (if io.usePaged = 0 ∧ io.sideBit ≠ 0 then io.pgL.offTail else io.pgL.qBits)
          io.pgL.vBits io.pgL.w ≤ fr₂) :
    EpochSlotInv c U V w fr₂ pBase metaBase io slack draining sl mem := by
  have hio_v2 : io.Valid w fr₂ := by
    have hv := h.io_valid
    unfold SlotIoLayout.Valid at hv ⊢
    by_cases hup : io.usePaged = 0
    · rw [ite_eq_left hup] at hv ⊢
      refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, ?_⟩
      have hs := hv.2.2.2.2.2
      by_cases hsb : io.sideBit = 0
      · rw [ite_eq_left hsb]
        simpa only [hup, hsb, ne_eq, not_true_eq_false, and_false, ↓reduceIte] using hio_fr
      · rw [ite_eq_right hsb] at hs ⊢
        refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
        simpa only [hup, hsb, ne_eq, not_false_eq_true, and_self, ↓reduceIte] using hio_fr
    · rw [ite_eq_right hup] at hv ⊢
      unfold PageArenaLayout.Valid at hv ⊢
      refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2.1,
        hv.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.1,
        hv.2.2.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.2.2.1,
        hv.2.2.2.2.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
      simpa only [hup, false_and, ↓reduceIte] using hio_fr
  unfold EpochSlotInv at h ⊢
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h hm_fr ⊢
    obtain ⟨hw6, _, hv, hpt, hdisj, hst⟩ := h
    exact ⟨hw6, hp_fr, ⟨hio_v2, hv.w_eq, hv.qBits_eq, hv.vBits_eq, hm_fr, hv.disjoint_hdr⟩,
      hpt, hdisj, hst⟩
  · rw [ite_eq_right h0] at h hm_fr ⊢
    obtain ⟨hv, hinv, hfp, hcd, hgd⟩ := h
    exact ⟨{ hv with
        meta_frontier := hm_fr
        io_valid := hio_v2 }, hinv, hfp, hcd, hgd⟩

/-- Transports `EpochSlotInv` across a `setSlotIoProg` update on `pBase` (`48..60 := io₂`). -/
theorem EpochSlotInv.set_slotIo {c U V w fr pBase metaBase slack₁ slack₂ : ℕ}
    {io₁ io₂ : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem₁ mem₂ : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io₁ slack₁ draining sl mem₁)
    (hv_io₂ : io₂.Valid w fr)
    (hw_io₂ : io₂.pgL.w = w)
    (hq_io₂ : (sl.nCap = 0 → io₂.pgL.qBits = keyBits U) ∧
      (sl.nCap ≠ 0 → quotBitsWhp U sl.nCap ≤ io₂.pgL.qBits))
    (hvb_io₂ : io₂.pgL.vBits = valBits V)
    (hp_rest : ∀ k, (k < 48 ∨ k = 61 ∨ k = 62) → mem₂ (pBase + k) = mem₁ (pBase + k))
    (hp_io :
      mem₂ (pBase + 48) = io₂.usePaged ∧ mem₂ (pBase + 49) = io₂.sideBit ∧
      mem₂ (pBase + 50) = io₂.pgL.metaBase ∧ mem₂ (pBase + 51) = io₂.pgL.offDir ∧
      mem₂ (pBase + 52) = io₂.pgL.offTail ∧ mem₂ (pBase + 53) = io₂.pgL.ptrB ∧
      mem₂ (pBase + 54) = io₂.pgL.w ∧ mem₂ (pBase + 55) = io₂.pgL.pgB ∧
      mem₂ (pBase + 56) = io₂.pgL.maxPages ∧ mem₂ (pBase + 57) = io₂.pgL.itemBase ∧
      mem₂ (pBase + 58) = io₂.pgL.qBits ∧ mem₂ (pBase + 59) = io₂.pgL.vBits ∧
      mem₂ (pBase + 60) = io₂.pgL.nCap)
    (hdisj_p₂ : ∀ a, pBase ≤ a → a < pBase + 64 → ¬io₂.OwnsAddr a)
    (hdisj_m₂ : ∀ a, slotOwnsNonPageMeta c w metaBase sl.nCap a → ¬io₂.OwnsAddr a)
    (hm : ∀ a, slotOwnsNonPageMeta c w metaBase sl.nCap a → mem₂ a = mem₁ a)
    (hio₂ : io₂.StateInv (mem₁ (metaBase + 1)) slack₂ mem₂)
    (hpair : ∀ p < mem₁ (metaBase + 1), slotIoPairAt io₂ mem₂ p = slotIoPairAt io₁ mem₁ p) :
    EpochSlotInv c U V w fr pBase metaBase io₂ slack₂ draining sl mem₂ := by
  have hraw := h; unfold EpochSlotInv at hraw
  refine h.transfer_io hv_io₂ hw_io₂ hq_io₂ hvb_io₂ ⟨fun h0 => ?_, fun h0 => ?_⟩
    hdisj_p₂ hdisj_m₂ hm hio₂ hpair
  · rw [ite_eq_left h0] at hraw
    have hpt1 := hraw.2.2.2.1
    exact ⟨(hp_rest 0 (Or.inl (by decide))).trans hpt1.1,
      (hp_rest 1 (Or.inl (by decide))).trans hpt1.2.1,
      hp_io.1, hp_io.2.1, hp_io.2.2.1, hp_io.2.2.2.1, hp_io.2.2.2.2.1, hp_io.2.2.2.2.2.1,
      hp_io.2.2.2.2.2.2.1, hp_io.2.2.2.2.2.2.2.1, hp_io.2.2.2.2.2.2.2.2.1,
      hp_io.2.2.2.2.2.2.2.2.2.1, hp_io.2.2.2.2.2.2.2.2.2.2.1,
      hp_io.2.2.2.2.2.2.2.2.2.2.2.1, hp_io.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · rw [ite_eq_right h0] at hraw
    have hpt1 := hraw.2.1.1
    intro k hk
    by_cases h48 : k < 48
    · rw [hp_rest k (Or.inl h48)]
      exact (hpt1 k hk).trans (by interval_cases k <;> rfl)
    · by_cases h61 : k = 61
      · subst h61; rw [hp_rest 61 (Or.inr (Or.inl rfl))]; exact hpt1 61 hk
      · by_cases h62 : k = 62
        · subst h62; rw [hp_rest 62 (Or.inr (Or.inr rfl))]; exact hpt1 62 hk
        · have hk61 : k < 61 := by omega
          interval_cases k
          · exact hp_io.1
          · exact hp_io.2.1
          · exact hp_io.2.2.1
          · exact hp_io.2.2.2.1
          · exact hp_io.2.2.2.2.1
          · exact hp_io.2.2.2.2.2.1
          · exact hp_io.2.2.2.2.2.2.1
          · exact hp_io.2.2.2.2.2.2.2.1
          · exact hp_io.2.2.2.2.2.2.2.2.1
          · exact hp_io.2.2.2.2.2.2.2.2.2.1
          · exact hp_io.2.2.2.2.2.2.2.2.2.2.1
          · exact hp_io.2.2.2.2.2.2.2.2.2.2.2.1
          · exact hp_io.2.2.2.2.2.2.2.2.2.2.2.2

theorem rootStaticHeader_congr {c U V w base : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hhdr : RootStaticHeader c U V w base m₁)
    (heq : ∀ off < 10, m₂ (base + off) = m₁ (base + off)) :
    RootStaticHeader c U V w base m₂ :=
  ⟨(heq 0 (by decide)).trans hhdr.1, (heq 1 (by decide)).trans hhdr.2.1,
   (heq 2 (by decide)).trans hhdr.2.2.1, (heq 3 (by decide)).trans hhdr.2.2.2.1,
   (heq 4 (by decide)).trans hhdr.2.2.2.2.1, (heq 5 (by decide)).trans hhdr.2.2.2.2.2.1,
   (heq 6 (by decide)).trans hhdr.2.2.2.2.2.2.1,
   (heq 7 (by decide)).trans hhdr.2.2.2.2.2.2.2.1,
   (heq 8 (by decide)).trans hhdr.2.2.2.2.2.2.2.2.1,
   (heq 9 (by decide)).trans hhdr.2.2.2.2.2.2.2.2.2⟩

theorem hostCacheValid_congr_mem {c w N off0 base : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hc : HostCacheValid c w N off0 base m₁)
    (heq : ∀ k ≤ 4, m₂ (base + off0 + k) = m₁ (base + off0 + k)) :
    HostCacheValid c w N off0 base m₂ := fun hN => by
  obtain ⟨c0, c1, c2, c3, c4⟩ := hc hN
  have h0 := heq 0 (by decide); rw [add_zero] at h0
  exact ⟨h0.trans c0, (heq 1 (by decide)).trans c1, (heq 2 (by decide)).trans c2,
    (heq 3 (by decide)).trans c3, (heq 4 (by decide)).trans c4⟩

theorem epochMetaWordsWhp_eq_of_cEff {c₁ c₂ w N : ℕ} (hce : cEff c₁ = cEff c₂) :
    epochMetaWordsWhp c₁ w N = epochMetaWordsWhp c₂ w N := by
  have hct : cTabWhp c₁ = cTabWhp c₂ := by unfold cTabWhp; rw [hce]
  have hqt : qTabWhp c₁ = qTabWhp c₂ := by unfold qTabWhp; rw [hce]
  have hdt : dTabWhp c₁ = dTabWhp c₂ := by unfold dTabWhp; rw [hqt, hct]
  have hcexp : codeExpWhp c₁ = codeExpWhp c₂ := by rw [codeExpWhp_eq, codeExpWhp_eq, hct, hqt]
  have hbm : bMinWhp c₁ = bMinWhp c₂ := by rw [bMinWhp_eq, bMinWhp_eq, hcexp]
  have hth : whpThreshold c₁ = whpThreshold c₂ := by rw [whpThreshold_eq, whpThreshold_eq, hbm]
  have htr : maxTrieNodesWhp c₁ N = maxTrieNodesWhp c₂ N := by unfold maxTrieNodesWhp; rw [hct]
  unfold epochMetaWordsWhp
  rw [hth, hct, hdt, htr]

attribute [local irreducible] epochMetaWordsWhp

theorem slotOwnsNonPageMeta_src_range {c w base nCap a : ℕ} {mem : ℕ → ℕ}
    (hcap : nCap = dualCapSrc base mem)
    (h1 : mem (base + hdrStage) ≠ 0 → mem (base + hdrNDst) ≠ 0)
    (ha : slotOwnsNonPageMeta c w (dualMbSrc base mem) nCap a) :
    (base + 48 ≤ a ∧ a < base + 50) ∨ base + 192 ≤ a := by
  rw [hcap] at ha
  unfold slotOwnsNonPageMeta dualMbSrc dualCapSrc at ha
  by_cases hst : mem (base + hdrStage) = 0
  · simp only [hst, ↓reduceIte] at ha
    by_cases hn0 : mem (base + hdrNSrc) = 0
    · simp only [hn0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false] at ha
      dsimp only [hdrSmallMeta0] at ha; exact Or.inl ha
    · simp only [hn0, ↓reduceIte] at ha
      rcases ha with ⟨hlo, _⟩ | ⟨_, hlo, _⟩ <;> (clear *- hlo; exact Or.inr (by omega))
  · have hd0 := h1 hst
    simp only [hst, hd0, ↓reduceIte] at ha
    rcases ha with ⟨hlo, _⟩ | ⟨_, hlo, _⟩ <;> (clear *- hlo; exact Or.inr (by omega))

theorem dualPh5MaskMem_eq_setSlotIo (V w base pDst ibHi qHi nLive : ℕ) (s : Memory.State) :
    dualPh5MaskMem V w base pDst ibHi qHi nLive s.mem =
      ((Memory.spec 0).clientState s
        (setSlotIoProg (pDst, (directSlotIo w (valBits V) base ibHi qHi nLive).toCtx))).mem := by
  have hvals := setSlotIoProg_mem_vals pDst (directSlotIo w (valBits V) base ibHi qHi nLive) s
  have hframe := setSlotIoProg_frame pDst (directSlotIo w (valBits V) base ibHi qHi nLive).toCtx
  funext addr
  by_cases hin : pDst + 48 ≤ addr ∧ addr < pDst + 61
  · obtain ⟨j, hj13, rfl⟩ : ∃ j < 13, addr = pDst + (48 + j) :=
      ⟨addr - (pDst + 48), by omega, by omega⟩
    unfold dualPh5MaskMem
    interval_cases j
    · iterate 12 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 0) = pDst + 48 by omega, Function.update_self]; exact hvals.1.symm
    · iterate 11 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 1) = pDst + 49 by omega, Function.update_self]; exact hvals.2.1.symm
    · iterate 10 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 2) = pDst + 50 by omega, Function.update_self]; exact hvals.2.2.1.symm
    · iterate 9 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 3) = pDst + 51 by omega, Function.update_self]; exact hvals.2.2.2.1.symm
    · iterate 8 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 4) = pDst + 52 by omega, Function.update_self]
      exact hvals.2.2.2.2.1.symm
    · iterate 7 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 5) = pDst + 53 by omega, Function.update_self]
      exact hvals.2.2.2.2.2.1.symm
    · iterate 6 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 6) = pDst + 54 by omega, Function.update_self]
      exact hvals.2.2.2.2.2.2.1.symm
    · iterate 5 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 7) = pDst + 55 by omega, Function.update_self]
      exact hvals.2.2.2.2.2.2.2.1.symm
    · iterate 4 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 8) = pDst + 56 by omega, Function.update_self]
      exact hvals.2.2.2.2.2.2.2.2.1.symm
    · iterate 3 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 9) = pDst + 57 by omega, Function.update_self]
      exact hvals.2.2.2.2.2.2.2.2.2.1.symm
    · iterate 2 rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 10) = pDst + 58 by omega, Function.update_self]
      exact hvals.2.2.2.2.2.2.2.2.2.2.1.symm
    · rw [Function.update_of_ne (by omega)]
      rw [show pDst + (48 + 11) = pDst + 59 by omega, Function.update_self]
      exact hvals.2.2.2.2.2.2.2.2.2.2.2.1.symm
    · rw [show pDst + (48 + 12) = pDst + 60 by omega, Function.update_self]
      exact hvals.2.2.2.2.2.2.2.2.2.2.2.2.symm
  · rw [hframe.mem_outside s addr hin]
    unfold dualPh5MaskMem
    iterate 13 rw [Function.update_of_ne (by omega)]

/-! ## Section 3: Phase `0` (`tickIdleProg`) Specification -/

private theorem idle_post_no_trigger {c U nSrc nLive ops : ℕ}
    (hp : DualPostUpdateSafe c U nSrc nLive)
    (hno : dualTriggerCap c U nSrc nLive ops = none) :
    DualIdleSafe c U nSrc nLive ∧
    (nSrc = 0 → nLive < whpThreshold c) ∧
    (0 < nSrc → 4 * ops < nSrc) := by
  by_cases h0 : nSrc = 0
  · subst h0
    simp only [DualPostUpdateSafe, DualIdleSafe, ↓reduceIte] at hp ⊢
    unfold dualTriggerCap at hno; simp only [↓reduceIte] at hno
    have hlt : nLive < whpThreshold c := by
      by_cases hU : whpThreshold c ≤ U
      · by_cases hn : whpThreshold c ≤ nLive
        · simp [hU, hn] at hno
        · omega
      · omega
    exact ⟨⟨hp.1, by omega⟩, fun _ => hlt, fun h => absurd h (Nat.lt_irrefl 0)⟩
  · simp only [DualPostUpdateSafe, DualIdleSafe, h0, ↓reduceIte] at hp ⊢
    obtain ⟨hth, hNU, hnU, _, _⟩ := hp
    unfold dualTriggerCap at hno; simp only [h0, ↓reduceIte] at hno
    by_cases hg : nSrc < U ∧ 3 * nSrc ≤ 4 * nLive
    · simp [hg] at hno
    · rw [ite_eq_right hg] at hno
      by_cases hs : 5 * nLive ≤ 2 * nSrc
      · rw [ite_eq_left hs] at hno; split_ifs at hno
      · rw [ite_eq_right hs] at hno
        by_cases hr : nSrc ≤ 4 * ops
        · simp [hr] at hno
        · exact ⟨⟨hth, hNU, hnU, by omega,
            fun hlt => by have : ¬(3 * nSrc ≤ 4 * nLive) := fun hh => hg ⟨hlt, hh⟩; omega⟩,
            False.elim, fun _ => by omega⟩

private theorem trigger_evs_len_le {nSrc ops len : ℕ}
    (_hpos : 0 < nSrc) (hops : 4 * ops < nSrc + 4)
    (hlen : 2 * len ≤ 3 * nSrc + 2 * ops + 2) (hbig : 2 ^ 20 ≤ nSrc) :
    len ≤ 2 * nSrc := by omega

/-- Phase `0` (`idle`) background tick specification. -/
theorem tickPhase0_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp0 : s.mem (base + hdrPhase) = 0)
    (hsucc_fits : base + Dynamic.succinctWords (whpResizableSpaceFactor c)
      whpResizableSpaceConst U V w (Dictionary.dom s_dict).card < 2 ^ w) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf; have hb192 := h.base_fr
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds
  have hsched := h.sched; rw [ite_eq_left hp0] at hsched
  obtain ⟨hpost, hfr_pad_s, hfr_lo, hfr_hi⟩ := hsched.safe_fr
  obtain ⟨_, hvb_w, hqLo_w, _, _, _, _, _⟩ := dualCoreInv_ib_fits h
  set nLive := (Dictionary.dom s_dict).card
  set nSrc := s.mem (base + hdrNSrc)
  set mSrc := s.mem (base + hdrMSrc)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set vB := valBits V
  set loFr := ibLo + pairStreamWords nLive qLo vB w
  have hw_pos : 0 < w := by omega
  have hth_big := whpThreshold_ge_pow20 c
  have hu1_succ : s.mem (base + hdrU1) + 1 = U := by rw [hhdr.1]; omega
  have hnSrc_U : nSrc ≤ U := by rcases hnSrc_b with h0 | ⟨_, hU⟩ <;> [omega; exact hU]
  have hops_fit : nSrc ≠ 0 → Fits w (s.mem (base + hdrEpochOps) + 1) := fun hnz => by
    have ho := (hsched.ops_evs (Nat.pos_of_ne_zero hnz)).1
    simp only [↓reduceIte] at ho
    dsimp only [Fits]; omega
  have hm196_fit : Fits w (base + 196 + mSrc) := by
    have hpad_f := h.pad_fits; rw [ite_eq_left hp0] at hpad_f
    have hm_eq' : epochMetaWordsWhp c w (s.mem (base + hdrNSrc)) = mSrc := hmSrc_eq.symm
    unfold dualPaddedWords rootHdrWhp at hpad_f
    rw [Nat.max_self, hm_eq'] at hpad_f
    dsimp only [Fits] at hpad_f ⊢; omega
  have hpre_idle : TickIdlePre w base s :=
    ⟨by omega, hb192, hu1_succ ▸ hUw, by rw [hlive_eq, hu1_succ]; exact hlive_le,
     by rw [hu1_succ]; exact hnSrc_U, hops_fit, hm196_fit⟩
  have hpre_bg : BgTickPre w (base, s.frontier) s := by
    refine ⟨by omega, by omega, ?_⟩; dsimp only; rw [ite_eq_left hp0]; exact hpre_idle
  have hbgev := bgTickProg_eval base s.frontier s
  dsimp only at hbgev; rw [ite_eq_left hp0, ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 5),
    ite_eq_left hp0] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  obtain ⟨hst_idle, hmc_idle⟩ := tickIdleProg_eval base s
  set s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
  have hs_tick_eq : s_tick = (Memory.spec 0).clientState s (tickIdleProg base) := hst_bg
  have hwf_tick : Memory.WellFormed w s_tick :=
    wf_step hwf (validHistory_bgTickProg hwf hpre_bg)
  have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq, hst_idle]
  have hpw2 := pairStreamWords_succ_le_add_two (n := nLive) hw_pos (show qLo + vB ≤ 2 * w by omega)
  have hdiff_le : s.frontier - loFr ≤ bulkBatchWhp := by unfold bulkBatchWhp; omega
  set ops' := if nSrc = 0 then 0 else s.mem (base + hdrEpochOps) + 1
  set s1 : Memory.State :=
    { mem := Function.update s.mem (base + hdrEpochOps) ops', frontier := s.frontier }
  have hhdr1 : RootStaticHeader c U V w base s1.mem :=
    rootStaticHeader_congr hhdr fun off hoff =>
      Function.update_of_ne (by unfold hdrEpochOps; omega) _ _
  have hs1_ns : s1.mem (base + hdrNSrc) = nSrc :=
    Function.update_of_ne (by unfold hdrNSrc hdrEpochOps; omega) _ _
  have hs1_nl : s1.mem (base + hdrLive) = nLive :=
    (Function.update_of_ne (by unfold hdrLive hdrEpochOps; omega) _ _).trans hlive_eq
  have hs1_ops : s1.mem (base + hdrEpochOps) = ops' := Function.update_self ..
  have hct_res := (checkTriggerProg_spec hU0 hhdr1 (hs1_ns.symm ▸ hnSrc_b)).2.2
  rw [hs1_ns, hs1_nl, hs1_ops] at hct_res
  obtain ⟨hcap_s, _, hsl_s, _⟩ := h.sl_le7 (by omega)
  have hcap_eq : dualCapSrc base s.mem = nSrc := by
    unfold dualCapSrc; rw [ite_eq_left hsched.stg_zero]
  have hio_s : activeSrcIo c w vB base (s.mem (base + hdrStage)) (s.mem (base + hdrPhase))
      nSrc (s.mem (base + hdrNDst)) (s.mem (base + hdrPad)) ibLo qLo (s.mem (base + hdrItemHi))
      (s.mem (base + hdrQHi)) nLive = directSlotIo w vB base ibLo qLo nLive := by
    unfold activeSrcIo; rw [ite_eq_left (by omega)]
  rw [hio_s] at hsl_s
  have hibL_eq : ibLo = base + 192 + mSrc := hsched.ibLo_eq
  have hsl_lo : EpochSlotInv c U V w loFr (dualPSrc base s.mem) (dualMbSrc base s.mem)
      (directSlotIo w vB base ibLo qLo nLive) 0 false L.slotSrc s.mem := by
    refine hsl_s.at_exact_frontier
      (by unfold dualPSrc; rw [ite_eq_left hsched.stg_zero]
          dsimp only [loFr]; rw [hibL_eq]; unfold hdrPBase0; omega)
      (by unfold dualMbSrc; rw [ite_eq_left hsched.stg_zero, hcap_s, hcap_eq]
          change (if nSrc = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192) + 2
            else (if nSrc = 0 then base + hdrSmallMeta0 else base + 192) +
              epochMetaWordsWhp c w nSrc) ≤ ibLo + pairStreamWords nLive qLo vB w
          rw [hibL_eq, ← show epochMetaWordsWhp c w nSrc = mSrc from hmSrc_eq.symm]
          by_cases h0 : nSrc = 0
          · rw [ite_eq_left h0, ite_eq_left h0]; unfold hdrSmallMeta0; omega
          · rw [ite_eq_right h0, ite_eq_right h0]; omega)
      (by simp only [directSlotIo, ne_eq, not_true_eq_false, and_false, ↓reduceIte]; exact le_rfl)
  refine ⟨hpre_bg, hfr_tick, hwf_tick, ?_, ?_⟩
  · intro addr hlt
    rw [hs_tick_eq, hst_idle]; dsimp only
    split_ifs <;>
      (repeat rw [Function.update_of_ne (by omega)]) <;>
      exact Function.update_of_ne (by omega) _ _
  · rw [ite_eq_left (by omega : s.mem (base + hdrPhase) ≠ 5)]
    refine ⟨hres_bg, ?_⟩
    cases htrig : dualTriggerCap c U nSrc nLive ops' with
    | none =>
      rw [htrig] at hct_res
      have hno := idle_post_no_trigger hpost htrig
      have hmem_t : s_tick.mem = s1.mem := by
        rw [hs_tick_eq, hst_idle, hct_res, ite_eq_left rfl]
      have hne_ops : ∀ addr, addr ≠ base + hdrEpochOps → s_tick.mem addr = s.mem addr :=
        fun addr ha => by rw [hmem_t]; exact Function.update_of_ne ha _ _
      have hph_t : s_tick.mem (base + hdrPhase) = 0 :=
        (hne_ops _ (by simp [hdrPhase, hdrEpochOps])).trans hp0
      have hsl_t : EpochSlotInv c U V w loFr (dualPSrc base s_tick.mem) (dualMbSrc base s_tick.mem)
          (directSlotIo w vB base ibLo qLo nLive) 0 false L.slotSrc s_tick.mem := by
        have hpS : dualPSrc base s_tick.mem = dualPSrc base s.mem := by
          unfold dualPSrc; rw [hne_ops _ (by simp [hdrStage, hdrEpochOps])]
        have hmS : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
          unfold dualMbSrc
          rw [hne_ops _ (by simp [hdrStage, hdrEpochOps]),
            hne_ops _ (by simp [hdrNSrc, hdrEpochOps]),
            hne_ops _ (by simp [hdrPad, hdrEpochOps])]
        rw [hpS, hmS]
        exact hsl_lo.congr_mem
          (fun a h1 _ => hne_ops a (by
            unfold dualPSrc at h1; split_ifs at h1 <;>
              (dsimp only [hdrPBase0, hdrPBase1, hdrEpochOps] at *; omega)))
          (fun a ha => hne_ops a (by
            unfold slotOwnsNonPageMeta dualMbSrc at ha
            rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;>
              (split_ifs at h1 <;> dsimp only [hdrSmallMeta0, hdrEpochOps] at * <;> omega)))
          (fun a ha => hne_ops a (by
            simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
              ↓reduceIte] at ha
            dsimp only [hdrEpochOps] at *; omega))
      refine ⟨L, preservesEpochSeeds_refl (fun ⟨h9, _⟩ => by rw [hp0] at h9; cases h9) L,
        ?_, fun _ _ => by rw [hmc_bg]; omega⟩
      refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
      · rw [hne_ops _ (by simp [hdrNSrc, hdrEpochOps]), hph_t, ite_eq_left rfl, hfr_tick]
        exact hfr_pad_s
      · rw [hph_t, ite_eq_left (by decide : 0 < 2),
          hne_ops _ (by simp [hdrItemLo, hdrEpochOps]),
          hne_ops _ (by simp [hdrQLo, hdrEpochOps]), hfr_tick]
        refine ⟨hfr_lo, hdiff_le, ?_⟩
        exact
          { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
            wf := ⟨lt_of_le_of_lt hfr_lo hwf.1, fun a => by
              by_cases ha : a = base + hdrEpochOps
              · subst ha; rw [hmem_t]; dsimp only [s1]; rw [Function.update_self]
                dsimp only [ops']; split_ifs with h0
                · exact Nat.two_pow_pos w
                · exact hops_fit h0
              · rw [hne_ops a ha]; exact hwf.2 a⟩
            base_fr := by
              dsimp only; rw [show s.mem (base + hdrItemLo) = ibLo from rfl, hibL_eq]; omega
            hdr := rootStaticHeader_congr hhdr fun off hoff =>
              hne_ops _ (by unfold hdrEpochOps; omega)
            live_eq := (hne_ops _ (by simp [hdrLive, hdrEpochOps])).trans hlive_eq
            live_le := hlive_le
            ph_le := by dsimp only; rw [hph_t]; decide
            stg_le := by
              dsimp only; rw [hne_ops _ (by simp [hdrStage, hdrEpochOps]), hsched.stg_zero]; decide
            mSrc_eq := by
              dsimp only
              rw [hne_ops _ (by simp [hdrMSrc, hdrEpochOps]),
                hne_ops _ (by simp [hdrNSrc, hdrEpochOps])]
              exact hmSrc_eq
            cache_src := by
              dsimp only; rw [hne_ops _ (by simp [hdrNSrc, hdrEpochOps])]
              exact hostCacheValid_congr_mem hcache_s fun k hk =>
                hne_ops _ (by unfold hdrSrcOd hdrEpochOps; omega)
            nSrc_bounds := by
              dsimp only; rw [hne_ops _ (by simp [hdrNSrc, hdrEpochOps])]; exact hnSrc_b
            sched := by
              dsimp only; rw [ite_eq_left hph_t]
              refine
                { stg_zero := (hne_ops _ (by simp [hdrStage, hdrEpochOps])).trans hsched.stg_zero
                  nDst_zero := (hne_ops _ (by simp [hdrNDst, hdrEpochOps])).trans hsched.nDst_zero
                  mDst_zero := (hne_ops _ (by simp [hdrMDst, hdrEpochOps])).trans hsched.mDst_zero
                  ibLo_eq := by
                    dsimp only
                    rw [hne_ops _ (by simp [hdrItemLo, hdrEpochOps]),
                      hne_ops _ (by simp [hdrMSrc, hdrEpochOps])]
                    exact hsched.ibLo_eq
                  ibHi_eq := by
                    dsimp only
                    rw [hne_ops _ (by simp [hdrItemHi, hdrEpochOps]),
                      hne_ops _ (by simp [hdrItemLo, hdrEpochOps])]
                    exact hsched.ibHi_eq
                  qLo_eq := by
                    dsimp only
                    rw [hne_ops _ (by simp [hdrQLo, hdrEpochOps]),
                      hne_ops _ (by simp [hdrNSrc, hdrEpochOps])]
                    exact hsched.qLo_eq
                  qHi_eq := by
                    dsimp only
                    rw [hne_ops _ (by simp [hdrQHi, hdrEpochOps]),
                      hne_ops _ (by simp [hdrQLo, hdrEpochOps])]
                    exact hsched.qHi_eq
                  elapsed_zero := hsched.elapsed_zero
                  safe_fr := by
                    dsimp only
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    rw [hne_ops _ (by simp [hdrNSrc, hdrEpochOps]),
                      hne_ops _ (by simp [hdrItemLo, hdrEpochOps]),
                      hne_ops _ (by simp [hdrQLo, hdrEpochOps])]
                    exact ⟨hno.1, hno.2.1, rfl⟩
                  ops_evs := by
                    dsimp only
                    rw [hne_ops _ (by simp [hdrNSrc, hdrEpochOps]), hmem_t, hs1_ops]
                    intro hs_pos
                    have ho_old := hsched.ops_evs hs_pos
                    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at ho_old ⊢
                    refine ⟨hno.2.2 hs_pos, ?_⟩
                    dsimp only [ops']; rw [ite_eq_right hs_pos.ne']; omega }
            pad_fits := by
              dsimp only
              rw [hne_ops _ (by simp [hdrNSrc, hdrEpochOps]), hph_t, ite_eq_left rfl]
              have hp := h.pad_fits; rwa [ite_eq_left hp0] at hp
            ph1_inv := fun h1 => by dsimp only at h1; rw [hph_t] at h1; cases h1
            ph3_inv := fun h3 => by dsimp only at h3; rw [hph_t] at h3; cases h3
            ph4_inv := fun h4 => by dsimp only at h4; rw [hph_t] at h4; cases h4
            pDst_pre := fun h25 _ _ => by dsimp only at h25; rw [hph_t] at h25; omega
            ph5_inv := fun h5 => by dsimp only at h5; rw [hph_t] at h5; cases h5
            ph6_inv := fun h6 => by dsimp only at h6; rw [hph_t] at h6; cases h6
            ph7_inv := fun h7 => by dsimp only at h7; rw [hph_t] at h7; cases h7
            ph8_inv := fun h8 => by dsimp only at h8; rw [hph_t] at h8; cases h8
            ph9_inv := fun h9 => by dsimp only at h9; rw [hph_t] at h9; cases h9
            ph10_inv := fun h10 => by dsimp only at h10; rw [hph_t] at h10; cases h10
            sl_le7 := fun _ => by
              dsimp only
              have hcap_t : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
                unfold dualCapSrc
                rw [hne_ops _ (by simp [hdrStage, hdrEpochOps]),
                  hne_ops _ (by simp [hdrNSrc, hdrEpochOps]),
                  hne_ops _ (by simp [hdrNDst, hdrEpochOps])]
              rw [hcap_t, hph_t]
              refine ⟨hcap_s, (h.sl_le7 (by omega)).2.1, ?_, fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩
              unfold activeSrcIo; rw [ite_eq_left (by decide : 0 < 3),
                hne_ops _ (by simp [hdrItemLo, hdrEpochOps]),
                hne_ops _ (by simp [hdrQLo, hdrEpochOps])]
              exact hsl_t
            sl_67 := fun h67 => by dsimp only at h67; rw [hph_t] at h67; omega
            sl_8 := fun h8 => by dsimp only at h8; rw [hph_t] at h8; cases h8
            sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_t] at h9; omega }
    | some nDst =>
      rw [htrig] at hct_res
      set L' : DualLatent c U V :=
        { L with nTrig := nLive, trigOps := ops', elapsed := 0, unpermBound := 0 }
      have har := active_rebuild_safe hpost htrig (nCur := nLive) (d := 0)
        le_rfl le_rfl (by omega) hlive_le
      have hpad_new_le : dualPaddedWords c U V w nSrc nDst nLive ≤
          Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w nLive :=
        dualPaddedWords_le_succinctWords har.2.1 har.2.2.1
      have hpad_new_fits : base + dualPaddedWords c U V w nSrc nDst nLive < 2 ^ w :=
        lt_of_le_of_lt (Nat.add_le_add_left hpad_new_le base) hsucc_fits
      have hfr_le_pad_new : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive := by
        have hqSrc_ib : qLo + vB = epochItemBitsWhp c U V nSrc := by
          dsimp only [qLo]; rw [hsched.qLo_eq]; unfold epochItemBitsWhp
          by_cases h0 : nSrc = 0
          · rw [ite_eq_left h0, h0, ite_eq_left (whpThreshold_pos c)]
          · have hth_s : whpThreshold c ≤ nSrc := by
              simp only [EpochCapSafe, h0, ↓reduceIte] at har; exact har.2.1.1
            rw [ite_eq_right h0, ite_eq_right (Nat.not_lt.mpr hth_s)]
        have hpw_m : packedWords nLive (epochItemBitsWhp c U V nSrc) w ≤
            packedWords nLive (max (epochItemBitsWhp c U V nSrc) (epochItemBitsWhp c U V nDst)) w :=
          by unfold packedWords
             have hm := Nat.mul_le_mul_left nLive (le_max_left (epochItemBitsWhp c U V nSrc)
               (epochItemBitsWhp c U V nDst))
             have hd := Nat.div_le_div_right (c := w)
               (show nLive * epochItemBitsWhp c U V nSrc + w - 1 ≤
                 nLive * max (epochItemBitsWhp c U V nSrc) (epochItemBitsWhp c U V nDst) + w - 1
                 by omega)
             omega
        have hm_m := le_max_left (epochMetaWordsWhp c w nSrc) (epochMetaWordsWhp c w nDst)
        have h1 : s.frontier ≤ ibLo + pairStreamWords nLive qLo vB w + 2 :=
          hfr_hi.trans (Nat.add_le_add_left hpw2 ibLo)
        have hm_eq' : mSrc = epochMetaWordsWhp c w nSrc := hmSrc_eq
        rw [hibL_eq, hm_eq'] at h1
        unfold pairStreamWords at h1; rw [hqSrc_ib] at h1
        unfold dualPaddedWords rootHdrWhp; omega
      have hnRef_big : 2 ^ 20 ≤ max (whpThreshold c) nSrc :=
        hth_big.trans (le_max_left _ _)
      have htot_bud := totalRebuildBudget_mul16_le hnRef_big
      have hevs_le : 0 < nSrc → L.slotSrc.evs.length ≤ 2 * nSrc := fun hs_pos => by
        obtain ⟨ho1, ho2⟩ := hsched.ops_evs hs_pos
        simp only [↓reduceIte] at ho1 ho2
        exact trigger_evs_len_le hs_pos ho1 ho2
          (hth_big.trans (by rcases hnSrc_b with h0 | ⟨hth, _⟩ <;> [omega; exact hth]))
      by_cases hd0 : nDst = 0
      · -- Trigger `0 → 2` (`nDst = 0`, shrinking large `nSrc > 0` to small):
        subst hd0
        have hs_pos : 0 < nSrc := by
          by_contra hz; have h0 : nSrc = 0 := by omega
          rw [h0] at htrig; unfold dualTriggerCap at htrig; simp only [↓reduceIte] at htrig
          split_ifs at htrig with hc
          · injection htrig with hm; have := whpThreshold_pos c; omega
        have hnLive_sm : 2 * nLive < whpThreshold c := by
          unfold dualTriggerCap at htrig; simp only [hs_pos.ne', ↓reduceIte] at htrig
          by_cases hg : nSrc < U ∧ 3 * nSrc ≤ 4 * nLive
          · rw [ite_eq_left hg] at htrig; injection htrig with hm
            have := whpThreshold_pos c; omega
          · rw [ite_eq_right hg] at htrig
            by_cases hs : 5 * nLive ≤ 2 * nSrc
            · rw [ite_eq_left hs] at htrig
              by_cases hsm : 2 * nLive < whpThreshold c
              · exact hsm
              · rw [ite_eq_right hsm] at htrig; injection htrig with hm
                have := whpThreshold_pos c; omega
            · rw [ite_eq_right hs] at htrig
              split_ifs at htrig with hr
              · injection htrig with hm; omega
        have hmem_t : s_tick.mem =
            Function.update (Function.update (Function.update (Function.update
              (Function.update (Function.update (Function.update
                (Function.update s1.mem (base + hdrNDst) 0)
                (base + hdrStage) 0) (base + hdrEpochOps) 0)
                (base + hdrMDst) 0) (base + hdrPad) mSrc)
                (base + hdrItemHi) (base + 196 + mSrc))
                (base + hdrQHi) (keyBits U)) (base + hdrPhase) 2 := by
          rw [hs_tick_eq, hst_idle, hct_res, ite_eq_right Nat.one_ne_zero, ite_eq_left rfl,
            hhdr.2.2.2.1]
        have hout_t : ∀ a, a ≠ base + hdrPhase → a ≠ base + hdrQHi → a ≠ base + hdrItemHi →
            a ≠ base + hdrPad → a ≠ base + hdrMDst → a ≠ base + hdrEpochOps →
            a ≠ base + hdrStage → a ≠ base + hdrNDst → s_tick.mem a = s.mem a := by
          intro a h1 h2 h3 h4 h5 h6 h7 h8; rw [hmem_t]
          rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
            Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
            Function.update_of_ne h7, Function.update_of_ne h8]
          exact Function.update_of_ne h6 _ _
        have hph_t : s_tick.mem (base + hdrPhase) = 2 := by
          rw [hmem_t]; exact Function.update_self ..
        have hqH_t : s_tick.mem (base + hdrQHi) = keyBits U := by
          rw [hmem_t, Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hibH_t : s_tick.mem (base + hdrItemHi) = base + 196 + mSrc := by
          rw [hmem_t]; iterate 2 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hpad_t : s_tick.mem (base + hdrPad) = mSrc := by
          rw [hmem_t]; iterate 3 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hmD_t : s_tick.mem (base + hdrMDst) = 0 := by
          rw [hmem_t]; iterate 4 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hst_t : s_tick.mem (base + hdrStage) = 0 := by
          rw [hmem_t]; iterate 6 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hnD_t : s_tick.mem (base + hdrNDst) = 0 := by
          rw [hmem_t]; iterate 7 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc := by
          apply hout_t <;> exact base_add_ne (by decide)
        have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc := by
          apply hout_t <;> exact base_add_ne (by decide)
        have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo := by
          apply hout_t <;> exact base_add_ne (by decide)
        have hqL_t : s_tick.mem (base + hdrQLo) = qLo := by
          apply hout_t <;> exact base_add_ne (by decide)
        have hqL_le_kb : qLo ≤ keyBits U := by
          dsimp only [qLo]; rw [hsched.qLo_eq, ite_eq_right hs_pos.ne']
          exact Nat.sub_le _ _
        have hlt_hiFr : s.frontier < base + 196 + mSrc + pairStreamWords nLive (keyBits U) vB w :=
          by have hpw_q := pairStreamWords_mono_q (n := nLive) (vb := vB) (w := w) hqL_le_kb
             omega
        have hgrow_le : (base + 196 + mSrc + pairStreamWords nLive (keyBits U) vB w) -
            s.frontier ≤ 9 * max (whpThreshold c) nSrc := by
          have hkb_w : keyBits U ≤ w := Nat.clog_le_of_le_pow hUw.le
          have hpw_bound := pairStreamWords_le_two_mul_add_three (n := nLive) hw_pos
            (show keyBits U + vB ≤ 2 * w by omega)
          have hlo_ge : base + 192 + mSrc ≤ s.frontier := by omega
          have := le_max_left (whpThreshold c) nSrc
          omega
        have hsl_t : EpochSlotInv c U V w s_tick.frontier (dualPSrc base s_tick.mem)
            (dualMbSrc base s_tick.mem)
            (directSlotIo w vB base ibLo qLo nLive) 0 false L.slotSrc s_tick.mem := by
          have hpS : dualPSrc base s_tick.mem = dualPSrc base s.mem := by
            unfold dualPSrc; rw [hst_t, hsched.stg_zero]
          have hmS : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
            unfold dualMbSrc; rw [hst_t, hnS_t, hsched.stg_zero]; rfl
          rw [hpS, hmS, hfr_tick]
          exact hsl_s.congr_mem
            (fun a h1 _ => by
              unfold dualPSrc at h1; rw [ite_eq_left hsched.stg_zero] at h1
              apply hout_t <;> (dsimp only [hdrPBase0, hdrPhase, hdrQHi, hdrItemHi, hdrPad,
                hdrMDst, hdrEpochOps, hdrStage, hdrNDst] at *; omega))
            (fun a ha => by
              unfold slotOwnsNonPageMeta dualMbSrc at ha
              rw [ite_eq_left hsched.stg_zero, ite_eq_right hs_pos.ne'] at ha
              apply hout_t <;>
                (rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;>
                  dsimp only [hdrPhase, hdrQHi, hdrItemHi, hdrPad, hdrMDst, hdrEpochOps,
                    hdrStage, hdrNDst] at * <;> omega))
            (fun a ha => by
              simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
                ↓reduceIte] at ha
              apply hout_t <;>
                (dsimp only [hdrPhase, hdrQHi, hdrItemHi, hdrPad, hdrMDst, hdrEpochOps,
                  hdrStage, hdrNDst] at *; omega))
        refine ⟨L', preservesEpochSeeds_of_eq_slots
          (fun ⟨h9, _⟩ => by rw [hp0] at h9; cases h9) rfl rfl, ?_,
          fun _ _ => by rw [hmc_bg]; omega⟩
        refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
        · rw [hnS_t, hph_t, ite_eq_right (by decide : 2 ≠ 0), hnD_t, hfr_tick]
          exact hfr_le_pad_new
        · rw [hph_t, ite_eq_right (by decide : ¬(2 < 2)), ite_eq_left rfl,
            hibH_t, hqH_t, hfr_tick]
          refine ⟨hlt_hiFr, ?_⟩
          exact
            { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
              wf := hwf_tick, base_fr := by rw [hfr_tick]; exact hb192
              hdr := rootStaticHeader_congr hhdr fun off hoff => by
                apply hout_t <;>
                  (dsimp only [hdrPhase, hdrQHi, hdrItemHi, hdrPad, hdrMDst, hdrEpochOps,
                    hdrStage, hdrNDst] at *; omega)
              live_eq := by
                rw [show s_tick.mem (base + hdrLive) = s.mem (base + hdrLive) by
                  apply hout_t <;> exact base_add_ne (by decide)]
                exact hlive_eq
              live_le := hlive_le
              ph_le := by rw [hph_t]; decide
              stg_le := by rw [hst_t]; decide
              mSrc_eq := by rw [hmS_t, hnS_t]; exact hmSrc_eq
              cache_src := by
                rw [hnS_t]
                exact hostCacheValid_congr_mem hcache_s fun k hk => by
                  apply hout_t <;>
                    (dsimp only [hdrSrcOd, hdrPhase, hdrQHi, hdrItemHi, hdrPad, hdrMDst,
                      hdrEpochOps, hdrStage, hdrNDst] at *; omega)
              nSrc_bounds := hnS_t.symm ▸ hnSrc_b
              sched := by
                rw [ite_eq_right (by rw [hph_t]; decide)]
                refine
                  { nDst_bounds := Or.inl hnD_t
                    nDst_zero := fun _ =>
                      ⟨hnS_t.symm ▸ hs_pos, hst_t, by rw [hph_t]; decide,
                       by rw [hph_t]; decide, by rw [hph_t]; decide⟩
                    stg_one := fun h1 => absurd (hst_t.symm.trans h1) (by decide)
                    post_trig := hnS_t.symm ▸ hpost
                    trig_cap := by rw [hnS_t, hnD_t]; exact htrig
                    drift_hi := by
                      dsimp only [L', nLive]
                      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]; exact le_rfl
                    drift_lo := by
                      dsimp only [L', nLive]
                      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]; exact le_rfl
                    ibLo_eq := by
                      rw [hibL_t, hph_t, ite_eq_left (by decide : 2 < 10), hmS_t]
                      exact hsched.ibLo_eq
                    qLo_eq := by
                      rw [hqL_t, hph_t, ite_eq_left (by decide : 2 < 10), hnS_t]
                      exact hsched.qLo_eq
                    ph1 := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
                    ge2 := fun _ => by
                      rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                      have hm0 : epochMetaWordsWhp c w 0 = 0 := by
                        unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
                      refine ⟨hm0.symm, (max_eq_left (Nat.zero_le _)).symm,
                        fun h0 => absurd h0 (Nat.lt_irrefl 0),
                        fun h0 => absurd h0 (Nat.lt_irrefl 0),
                        by rw [ite_eq_left rfl],
                        by rw [ite_eq_right hs_pos.ne', ite_eq_left rfl]
                           exact (max_eq_right (Nat.sub_le _ _)).symm⟩
                    ph2 := fun _ => by
                      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                      rw [hst_t, hibL_t, hqL_t, hibH_t, hqH_t, hfr_tick]
                      exact ⟨rfl, hfr_lo, hlt_hiFr.le⟩
                    ph3_10 := fun h3 => by rw [hph_t] at h3; omega
                    ph11 := fun h11 => absurd (hph_t.symm.trans h11) (by decide)
                    budget := by
                      dsimp only [L']
                      rw [hnS_t, hst_t, hph_t, hibH_t, hqH_t, hfr_tick]
                      unfold remRebuildBudget futureRebuildBudget
                      dsimp only
                      simp only [show (2 : ℕ) ≠ 1 by decide, Bool.false_eq_true, false_and,
                        ↓reduceIte, zero_add, add_zero]
                      have hdiv := Nat.div_le_div_right (c := 1022) hgrow_le
                      change (base + 196 + mSrc +
                          pairStreamWords (Dictionary.dom s_dict).card (keyBits U) (valBits V) w -
                          s.frontier) / 1022 ≤
                        9 * max (whpThreshold c) nSrc / 1022 at hdiv
                      have htb := htot_bud
                      unfold totalRebuildBudget at htb
                      have hf2 : 2 ≤ maxTailPhasesBudget (max (whpThreshold c) nSrc) := by
                        unfold maxTailPhasesBudget; omega
                      generalize max (whpThreshold c) nSrc = nRef at htb hdiv hf2 ⊢
                      clear *- htb hdiv hf2
                      omega }
              pad_fits := by
                rw [hnS_t, hph_t, ite_eq_right (by decide : 2 ≠ 0), hnD_t]; exact hpad_new_fits
              ph1_inv := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
              ph3_inv := fun h3 => absurd (hph_t.symm.trans h3) (by decide)
              ph4_inv := fun h4 => absurd (hph_t.symm.trans h4) (by decide)
              pDst_pre := fun _ _ hd_pos => by rw [hnD_t] at hd_pos; exact absurd hd_pos (by decide)
              ph5_inv := fun h5 => absurd (hph_t.symm.trans h5) (by decide)
              ph6_inv := fun h6 => absurd (hph_t.symm.trans h6) (by decide)
              ph7_inv := fun h7 => absurd (hph_t.symm.trans h7) (by decide)
              ph8_inv := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
              ph9_inv := fun h9 => absurd (hph_t.symm.trans h9) (by decide)
              ph10_inv := fun h10 => absurd (hph_t.symm.trans h10) (by decide)
              sl_le7 := fun _ => by
                have hcap_t : dualCapSrc base s_tick.mem = nSrc := by
                  unfold dualCapSrc; rw [hst_t, hnS_t, ite_eq_left rfl]
                rw [hcap_t, hph_t]
                refine ⟨hcap_s.trans hcap_eq, (h.sl_le7 (by omega)).2.1, ?_,
                  fun _ hs_p => by dsimp only [L']; exact (hevs_le hs_p).trans (by omega)⟩
                unfold activeSrcIo; rw [ite_eq_left (by decide : 2 < 3), hibL_t, hqL_t]
                exact hsl_t
              sl_67 := fun h67 => by rw [hph_t] at h67; omega
              sl_8 := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
              sl_ge9 := fun h9 => by rw [hph_t] at h9; omega }
      · -- Trigger `0 → 1` (`0 < nDst`, entering `log2Calc`):
        have hd_pos : 0 < nDst := Nat.pos_of_ne_zero hd0
        have hd_safe := har.2.2.1
        simp only [EpochCapSafe, hd0, ↓reduceIte] at hd_safe
        have hmem_t : s_tick.mem =
            Function.update (Function.update (Function.update (Function.update
              (Function.update (Function.update
                (Function.update s1.mem (base + hdrNDst) nDst)
                (base + hdrStage) 0) (base + hdrEpochOps) 0)
                (base + hdrLogSub) 0) (base + hdrLogAcc) nDst)
                (base + hdrLogK) 0) (base + hdrPhase) 1 := by
          rw [hs_tick_eq, hst_idle, hct_res, ite_eq_right Nat.one_ne_zero, ite_eq_right hd0]
        have hout_t : ∀ a, a ≠ base + hdrPhase → a ≠ base + hdrLogK → a ≠ base + hdrLogAcc →
            a ≠ base + hdrLogSub → a ≠ base + hdrEpochOps → a ≠ base + hdrStage →
            a ≠ base + hdrNDst → s_tick.mem a = s.mem a := by
          intro a h1 h2 h3 h4 h5 h6 h7; rw [hmem_t]
          rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
            Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
            Function.update_of_ne h7]
          exact Function.update_of_ne h5 _ _
        have hph_t : s_tick.mem (base + hdrPhase) = 1 := by
          rw [hmem_t]; exact Function.update_self ..
        have hlk_t : s_tick.mem (base + hdrLogK) = 0 := by
          rw [hmem_t, Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hlacc_t : s_tick.mem (base + hdrLogAcc) = nDst := by
          rw [hmem_t]; iterate 2 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hlsub_t : s_tick.mem (base + hdrLogSub) = 0 := by
          rw [hmem_t]; iterate 3 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hst_t : s_tick.mem (base + hdrStage) = 0 := by
          rw [hmem_t]; iterate 5 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hnD_t : s_tick.mem (base + hdrNDst) = nDst := by
          rw [hmem_t]; iterate 6 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
          exact Function.update_self ..
        have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc := by
          apply hout_t <;> exact base_add_ne (by decide)
        have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc := by
          apply hout_t <;> exact base_add_ne (by decide)
        have hmD_t : s_tick.mem (base + hdrMDst) = 0 := by
          rw [show s_tick.mem (base + hdrMDst) = s.mem (base + hdrMDst) by
            apply hout_t <;> exact base_add_ne (by decide)]
          exact hsched.mDst_zero
        have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo := by
          apply hout_t <;> exact base_add_ne (by decide)
        have hibH_t : s_tick.mem (base + hdrItemHi) = ibLo := by
          rw [show s_tick.mem (base + hdrItemHi) = s.mem (base + hdrItemHi) by
            apply hout_t <;> exact base_add_ne (by decide)]
          exact hsched.ibHi_eq
        have hqL_t : s_tick.mem (base + hdrQLo) = qLo := by
          apply hout_t <;> exact base_add_ne (by decide)
        have hqH_t : s_tick.mem (base + hdrQHi) = qLo := by
          rw [show s_tick.mem (base + hdrQHi) = s.mem (base + hdrQHi) by
            apply hout_t <;> exact base_add_ne (by decide)]
          exact hsched.qHi_eq
        have hsl_t : EpochSlotInv c U V w loFr (dualPSrc base s_tick.mem)
            (dualMbSrc base s_tick.mem)
            (directSlotIo w vB base ibLo qLo nLive) 0 false L.slotSrc s_tick.mem := by
          have hpS : dualPSrc base s_tick.mem = dualPSrc base s.mem := by
            unfold dualPSrc; rw [hst_t, hsched.stg_zero]
          have hmS : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
            unfold dualMbSrc; rw [hst_t, hnS_t, hsched.stg_zero]; rfl
          rw [hpS, hmS]
          exact hsl_lo.congr_mem
            (fun a h1 _ => by
              unfold dualPSrc at h1; rw [ite_eq_left hsched.stg_zero] at h1
              apply hout_t <;> (dsimp only [hdrPBase0, hdrPhase, hdrLogK, hdrLogAcc, hdrLogSub,
                hdrEpochOps, hdrStage, hdrNDst] at *; omega))
            (fun a ha => by
              unfold slotOwnsNonPageMeta dualMbSrc at ha
              rw [ite_eq_left hsched.stg_zero] at ha
              apply hout_t <;>
                (rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> split_ifs at h1 <;>
                  dsimp only [hdrSmallMeta0, hdrPhase, hdrLogK, hdrLogAcc, hdrLogSub,
                    hdrEpochOps, hdrStage, hdrNDst] at * <;> omega))
            (fun a ha => by
              simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
                ↓reduceIte] at ha
              apply hout_t <;>
                (dsimp only [hdrPhase, hdrLogK, hdrLogAcc, hdrLogSub, hdrEpochOps,
                  hdrStage, hdrNDst] at *; omega))
        refine ⟨L', preservesEpochSeeds_of_eq_slots
          (fun ⟨h9, _⟩ => by rw [hp0] at h9; cases h9) rfl rfl, ?_,
          fun _ _ => by rw [hmc_bg]; omega⟩
        refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
        · rw [hnS_t, hph_t, ite_eq_right (by decide : 1 ≠ 0), hnD_t, hfr_tick]
          exact hfr_le_pad_new
        · rw [hph_t, ite_eq_left (by decide : 1 < 2), hibL_t, hqL_t, hfr_tick]
          refine ⟨hfr_lo, hdiff_le, ?_⟩
          exact
            { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
              wf := ⟨lt_of_le_of_lt hfr_lo hwf.1, fun a => hwf_tick.2 a⟩
              base_fr := by dsimp only [loFr]; rw [hibL_eq]; omega
              hdr := rootStaticHeader_congr hhdr fun off hoff => by
                apply hout_t <;>
                  (dsimp only [hdrPhase, hdrLogK, hdrLogAcc, hdrLogSub, hdrEpochOps,
                    hdrStage, hdrNDst] at *; omega)
              live_eq := by
                rw [show s_tick.mem (base + hdrLive) = s.mem (base + hdrLive) by
                  apply hout_t <;> exact base_add_ne (by decide)]
                exact hlive_eq
              live_le := hlive_le
              ph_le := by dsimp only; rw [hph_t]; decide
              stg_le := by dsimp only; rw [hst_t]; decide
              mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
              cache_src := by
                dsimp only; rw [hnS_t]
                exact hostCacheValid_congr_mem hcache_s fun k hk => by
                  apply hout_t <;>
                    (dsimp only [hdrSrcOd, hdrPhase, hdrLogK, hdrLogAcc, hdrLogSub,
                      hdrEpochOps, hdrStage, hdrNDst] at *; omega)
              nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
              sched := by
                dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
                refine
                  { nDst_bounds := Or.inr ⟨hnD_t.symm ▸ hd_safe.1, hnD_t.symm ▸ hd_safe.2.1⟩
                    nDst_zero := fun hz => absurd (hnD_t.symm.trans hz) hd0
                    stg_one := fun h1 => absurd (hst_t.symm.trans h1) (by decide)
                    post_trig := by dsimp only [L']; rw [hnS_t]; exact hpost
                    trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t]; exact htrig
                    drift_hi := by
                      dsimp only [L', nLive]
                      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]; exact le_rfl
                    drift_lo := by
                      dsimp only [L', nLive]
                      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]; exact le_rfl
                    ibLo_eq := by
                      dsimp only; rw [hibL_t, hph_t, ite_eq_left (by decide : 1 < 10), hmS_t]
                      exact hsched.ibLo_eq
                    qLo_eq := by
                      dsimp only; rw [hqL_t, hph_t, ite_eq_left (by decide : 1 < 10), hnS_t]
                      exact hsched.qLo_eq
                    ph1 := fun _ => by
                      dsimp only
                      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                      rw [hst_t, hnD_t, hmD_t, hibH_t, hibL_t, hqH_t, hqL_t]
                      exact ⟨rfl, hd_pos, rfl, rfl, rfl, le_rfl, le_rfl⟩
                    ge2 := fun h2 => by dsimp only at h2; rw [hph_t] at h2; omega
                    ph2 := fun h2 => absurd (hph_t.symm.trans h2) (by decide)
                    ph3_10 := fun h3 => by dsimp only at h3; rw [hph_t] at h3; omega
                    ph11 := fun h11 => absurd (hph_t.symm.trans h11) (by decide)
                    budget := by
                      dsimp only [L', remRebuildBudget, futureRebuildBudget]
                      rw [hnS_t, hst_t, hph_t, hlsub_t, hlk_t]
                      simp only [↓reduceIte, zero_add, Nat.sub_zero]
                      unfold totalRebuildBudget maxStageBudget maxTailPhasesBudget at htot_bud
                      unfold maxStageBudget maxTailPhasesBudget
                      dsimp only at htot_bud ⊢
                      omega }
              pad_fits := by
                dsimp only
                rw [hnS_t, hph_t, ite_eq_right (by decide : 1 ≠ 0), hnD_t]; exact hpad_new_fits
              ph1_inv := fun _ => by
                dsimp only; rw [hnD_t, hlsub_t, hlacc_t, hlk_t]
                exact ⟨by decide, fun _ => ⟨hd_pos, by simp, by simp⟩,
                  fun h1 => absurd h1 (by decide), fun h2 => absurd h2 (by decide)⟩
              ph3_inv := fun h3 => absurd (hph_t.symm.trans h3) (by decide)
              ph4_inv := fun h4 => absurd (hph_t.symm.trans h4) (by decide)
              pDst_pre := fun h25 _ _ => by dsimp only at h25; rw [hph_t] at h25; omega
              ph5_inv := fun h5 => absurd (hph_t.symm.trans h5) (by decide)
              ph6_inv := fun h6 => absurd (hph_t.symm.trans h6) (by decide)
              ph7_inv := fun h7 => absurd (hph_t.symm.trans h7) (by decide)
              ph8_inv := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
              ph9_inv := fun h9 => absurd (hph_t.symm.trans h9) (by decide)
              ph10_inv := fun h10 => absurd (hph_t.symm.trans h10) (by decide)
              sl_le7 := fun _ => by
                dsimp only
                have hcap_t : dualCapSrc base s_tick.mem = nSrc := by
                  unfold dualCapSrc; rw [hst_t, hnS_t, ite_eq_left rfl]
                rw [hcap_t, hph_t]
                refine ⟨hcap_s.trans hcap_eq, (h.sl_le7 (by omega)).2.1, ?_,
                  fun _ hs_p => by dsimp only [L']; exact (hevs_le hs_p).trans (by omega)⟩
                unfold activeSrcIo; rw [ite_eq_left (by decide : 1 < 3), hibL_t, hqL_t]
                exact hsl_t
              sl_67 := fun h67 => by dsimp only at h67; rw [hph_t] at h67; omega
              sl_8 := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
              sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_t] at h9; omega }

/-! ## Section 4: Phase `1` (`tickLogProg`) Specification -/

private theorem remRebuildBudget_ph1_eq (nRef sub lk g sp sr mD ob mp pg cur rem sd : ℕ) :
    remRebuildBudget nRef 0 1 sub lk g sp sr mD ob mp pg cur rem sd =
      remRebuildBudget nRef 0 1 sub lk 0 0 0 0 0 0 0 0 0 0 := rfl

private theorem two_le_remRebuildBudget_ph1 (nRef sub lk : ℕ) :
    2 ≤ remRebuildBudget nRef 0 1 sub lk 0 0 0 0 0 0 0 0 0 0 := by
  unfold remRebuildBudget futureRebuildBudget maxTailPhasesBudget
  dsimp only
  split_ifs <;> omega

private theorem log_finish_growDiff_le {c U w base trigOps nSrc nDst nTrig nLive d mSrc mDst
    ibHi qHi qLo vB fr : ℕ}
    (hpost : DualPostUpdateSafe c U nSrc nTrig)
    (htrig : dualTriggerCap c U nSrc nTrig trigOps = some nDst)
    (hd_hi : nLive ≤ nTrig + d) (hd_lo : nTrig ≤ nLive + d)
    (hd_le : 16 * d ≤ max (whpThreshold c) nSrc) (hnU : nLive ≤ U)
    (hth_d : whpThreshold c ≤ nDst) (hnD_w : nDst < 2 ^ w)
    (hw_pos : 0 < w) (hqHi_vB : qHi + vB ≤ 2 * w)
    (hmDst : mDst = epochMetaWordsWhp c w nDst)
    (hibHi : ibHi = base + 192 + max mSrc mDst + mDst + 4)
    (hfr_lo : base + 192 + mSrc + pairStreamWords nLive qLo vB w ≤ fr) :
    ibHi + pairStreamWords nLive qHi vB w - fr ≤ 9 * max (whpThreshold c) nSrc := by
  have har := active_rebuild_safe hpost htrig hd_hi hd_lo hd_le hnU
  have hnD_le : nDst ≤ 2 * max (whpThreshold c) nSrc := har.1
  have hnt_le : nTrig ≤ max (whpThreshold c) nSrc := by
    by_cases h0 : nSrc = 0
    · subst h0; simp only [DualPostUpdateSafe, ↓reduceIte] at hpost
      exact hpost.2.trans (le_max_left _ _)
    · simp only [DualPostUpdateSafe, h0, ↓reduceIte] at hpost
      have hs_pos : 1 ≤ nSrc := Nat.pos_of_ne_zero h0
      have hnt_s : nTrig ≤ nSrc := by
        by_cases hlt : nSrc < U
        · have h16 := hpost.2.2.2.2 hlt; clear *- hs_pos h16; omega
        · have hnU' := hpost.2.2.1; clear *- hlt hnU'; omega
      exact hnt_s.trans (le_max_right _ _)
  have hmD_le : mDst ≤ nDst + 120 := hmDst ▸ epochMetaWordsWhp_le_self hth_d hnD_w
  have hpw_le := pairStreamWords_le_two_mul_add_three (n := nLive) hw_pos hqHi_vB
  have hmax_le : max mSrc mDst ≤ mSrc + mDst :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hpw_lo_ge : 2 ≤ pairStreamWords nLive qLo vB w := Nat.le_add_left 2 _
  have hth_1k : 1024 ≤ whpThreshold c :=
    ((by decide : 1024 = 2 ^ 10) ▸
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by decide : 10 ≤ 20)).trans
      (whpThreshold_ge_pow20 c)
  have hR_1k : 1024 ≤ max (whpThreshold c) nSrc := hth_1k.trans (le_max_left _ _)
  subst hibHi
  generalize max (whpThreshold c) nSrc = nRef at hnD_le hnt_le hd_le hR_1k ⊢
  clear *- hd_hi hd_lo hd_le hnD_le hnt_le hmD_le hpw_le hmax_le hpw_lo_ge hR_1k hfr_lo
  omega

/-- Phase `1` (`log2Calc`) background tick specification (`sub ∈ {0, 1}` shift steps and `sub = 2`
`tickLogFinishProg` `1 → 2` transition). -/
theorem tickPhase1_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp1 : s.mem (base + hdrPhase) = 1) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf; have hb192 := h.base_fr
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds
  have hsched := h.sched; rw [ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 0)] at hsched
  obtain ⟨hst0, hd_pos, hmD0, hibH1, hqH1, hfr_lo, hfr_hi⟩ := hsched.ph1 hp1
  simp only [↓reduceIte] at hfr_hi
  obtain ⟨_, hvb_w, hqLo_w, _, hpad_lo_s, _, _, _⟩ := dualCoreInv_ib_fits h
  rw [ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 0)] at hpad_lo_s
  obtain ⟨hsub_le, hsub0, hsub1, hsub2⟩ := h.ph1_inv hp1
  set nLive := (Dictionary.dom s_dict).card
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set sub := s.mem (base + hdrLogSub)
  set acc := s.mem (base + hdrLogAcc)
  set lk := s.mem (base + hdrLogK)
  set vB := valBits V
  set loFr := ibLo + pairStreamWords nLive qLo vB w
  have hw_pos : 0 < w := by omega
  have hth_d : whpThreshold c ≤ nDst ∧ nDst ≤ U := by
    rcases hsched.nDst_bounds with hz | hb <;> [omega; exact hb]
  have hnDst_w : nDst < 2 ^ w := lt_of_le_of_lt hth_d.2 hUw
  have hd_ge4 : 4 ≤ nDst := four_le_of_whpThreshold_le hth_d.1
  have hpw2 := pairStreamWords_succ_le_add_two (n := nLive) hw_pos (show qLo + vB ≤ 2 * w by omega)
  have hdiff_le : s.frontier - loFr ≤ bulkBatchWhp := by unfold bulkBatchWhp; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive :=
    hfr_hi.trans hpad_lo_s
  have hrem_b := hsched.budget
  dsimp only [remRebuildBudget] at hrem_b
  rw [hp1, hst0, ite_eq_left rfl] at hrem_b
  have har := active_rebuild_safe hsched.post_trig hsched.trig_cap
    (by simpa using hsched.drift_hi) (by simpa using hsched.drift_lo)
    (by have := hrem_b.2.2; omega) hlive_le
  have hlk_bounds : sub < 2 → lk < w ∧ lk ≤ Nat.log 2 (2 * max (whpThreshold c) nSrc) := by
    intro hlt2
    by_cases hs0 : sub = 0
    · obtain ⟨hacc1, hlo_k, _⟩ := hsub0 hs0
      have hpow_le : 2 ^ lk ≤ nDst :=
        (Nat.one_mul (2 ^ lk)) ▸ Nat.mul_le_mul_right (2 ^ lk) hacc1 |>.trans hlo_k
      have hlk_log : lk ≤ Nat.log 2 nDst := Nat.le_log_of_pow_le Nat.one_lt_two hpow_le
      refine ⟨(Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (lt_of_le_of_lt hpow_le hnDst_w), ?_⟩
      exact hlk_log.trans (Nat.log_mono_right har.1)
    · have hs1 : sub = 1 := by omega
      obtain ⟨_, _, _, _, hlo_k, _, hacc0⟩ := hsub1 hs1
      have hcl_ge2 : 2 ≤ Nat.clog 2 nDst :=
        (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega)
      have hacc1 : 1 ≤ acc := by
        by_cases ha0 : acc = 0
        · have := (hacc0 ha0).2; omega
        · omega
      have hcl_le : Nat.clog 2 nDst - 1 ≤ nDst :=
        (Nat.sub_le _ _).trans (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := nDst)).le |>.trans
          (by omega))
      have hcl_nDst : Nat.clog 2 nDst - 1 ≤ Nat.log 2 nDst := by
        have := clog_eq_of_log hd_pos; split_ifs at this <;> omega
      have hpow_le : 2 ^ lk ≤ nDst := by
        have h1 : 2 ^ lk ≤ Nat.clog 2 nDst - 1 :=
          (Nat.one_mul (2 ^ lk)) ▸ Nat.mul_le_mul_right (2 ^ lk) hacc1 |>.trans hlo_k
        have hlog_le : Nat.log 2 nDst ≤ nDst := Nat.log_le_self 2 nDst
        omega
      refine ⟨(Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (lt_of_le_of_lt hpow_le hnDst_w), ?_⟩
      exact (Nat.le_log_of_pow_le Nat.one_lt_two hpow_le).trans (Nat.log_mono_right har.1)
  obtain ⟨hcap_s, _, hsl_s, hlen_s⟩ := h.sl_le7 (by omega)
  have hcap_eq : dualCapSrc base s.mem = nSrc := by
    unfold dualCapSrc; rw [ite_eq_left hst0]
  have hio_s : activeSrcIo c w vB base (s.mem (base + hdrStage)) (s.mem (base + hdrPhase))
      nSrc nDst (s.mem (base + hdrPad)) ibLo qLo (s.mem (base + hdrItemHi))
      (s.mem (base + hdrQHi)) nLive = directSlotIo w vB base ibLo qLo nLive := by
    unfold activeSrcIo; rw [ite_eq_left (by omega)]
  rw [hio_s] at hsl_s
  have hibL_eq : ibLo = base + 192 + mSrc := by
    dsimp only [ibLo]; rw [hsched.ibLo_eq, ite_eq_left (by omega)]
  have hsl_lo : EpochSlotInv c U V w loFr (dualPSrc base s.mem) (dualMbSrc base s.mem)
      (directSlotIo w vB base ibLo qLo nLive) 0 false L.slotSrc s.mem := by
    refine hsl_s.at_exact_frontier
      (by unfold dualPSrc; rw [ite_eq_left hst0]
          dsimp only [loFr]; rw [hibL_eq]; unfold hdrPBase0; omega)
      (by unfold dualMbSrc; rw [ite_eq_left hst0, hcap_s, hcap_eq]
          change (if nSrc = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192) + 2
            else (if nSrc = 0 then base + hdrSmallMeta0 else base + 192) +
              epochMetaWordsWhp c w nSrc) ≤ ibLo + pairStreamWords nLive qLo vB w
          rw [hibL_eq, ← show epochMetaWordsWhp c w nSrc = mSrc from hmSrc_eq.symm]
          by_cases h0 : nSrc = 0
          · rw [ite_eq_left h0, ite_eq_left h0]; unfold hdrSmallMeta0; omega
          · rw [ite_eq_right h0, ite_eq_right h0]; omega)
      (by simp only [directSlotIo, ne_eq, not_true_eq_false, and_false, ↓reduceIte]; exact le_rfl)
  have hpre_log : TickLogPre w base s := by
    refine ⟨by omega, by omega, ?_⟩
    by_cases hlt2 : sub < 2
    · rw [ite_eq_left hlt2]
      exact ⟨by omega, by omega, (hlk_bounds hlt2).1⟩
    · rw [ite_eq_right hlt2]
      have hs2 : sub = 2 := by omega
      obtain ⟨hlog_e, hell_e, _, hpg_e⟩ := hsub2 hs2
      have hpb := largeEpoch_param_bounds hth_d.1 hth_d.2 hUw
      have hell12 : Fits w (12 * s.mem (base + hdrEll)) := by
        rw [hell_e]
        have h320 : 320 * Dynamic.logLogFactor nDst ≤ bCharWhp nDst :=
          (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth_d.1)
        have hbw : 12 * Dynamic.logLogFactor nDst ≤ Nat.log 2 nDst := by
          unfold bCharWhp at h320; omega
        have hlog_w : Nat.log 2 nDst < 2 ^ w :=
          lt_of_le_of_lt (Nat.log_le_self 2 nDst) hnDst_w
        dsimp only [Fits]; omega
      have hpg_pos : 0 < s.mem (base + hdrPgB) := by rw [hpg_e]; unfold pageSizeWhp; omega
      have hm_fit : Fits w (base + 192 + epochMetaWordsWhp c w nDst) := by
        have hp := h.pad_fits; rw [ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 0)] at hp
        change base + dualPaddedWords c U V w nSrc nDst nLive < 2 ^ w at hp
        have hm2 := le_max_right (epochMetaWordsWhp c w nSrc) (epochMetaWordsWhp c w nDst)
        unfold dualPaddedWords rootHdrWhp at hp; dsimp only [Fits] at hp ⊢; omega
      have hwlp : WriteLargeParamPre w ((base, base + hdrPBase1),
          ((nDst, base + 192), ((s.mem (base + hdrLogN), s.mem (base + hdrEll)),
            s.mem (base + hdrPgB)))) s :=
        ⟨c, U, V, Or.inl (by unfold hdrPBase1; omega), hth_d.1, hth_d.2, hUw, hV0, hVw,
         hlog_e, hell_e, hpg_e, hm_fit,
         max_le (by omega) (Nat.clog_le_of_le_pow hUw.le),
         by omega, by unfold hdrPBase1; omega, hhdr⟩
      refine ⟨hw11, hb192, hpg_pos, hell12, hwlp, fun c' U' V' hhdr' hth' hNU' => ?_⟩
      have hce_eq : cEff c' = cEff c := by
        have h1 := hhdr'.2.2.2.2.2.2.2.2.2; rw [ite_eq_left (hth'.trans hNU')] at h1
        have h2 := hhdr.2.2.2.2.2.2.2.2.2; rw [ite_eq_left (hth_d.1.trans hth_d.2)] at h2
        exact h1.symm.trans h2
      rw [epochMetaWordsWhp_eq_of_cEff hce_eq]
      have hp := h.pad_fits; rw [ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 0)] at hp
      change base + dualPaddedWords c U V w nSrc nDst nLive < 2 ^ w at hp
      change Fits w (base + 192 + max mSrc (epochMetaWordsWhp c w nDst) +
        epochMetaWordsWhp c w nDst + 4)
      rw [hmSrc_eq]; unfold dualPaddedWords rootHdrWhp at hp; dsimp only [Fits] at hp ⊢; omega
  have hpre_bg : BgTickPre w (base, s.frontier) s := by
    refine ⟨by omega, by omega, ?_⟩
    dsimp only; rw [ite_eq_right (by omega), ite_eq_left hp1]; exact hpre_log
  have hbgev := bgTickProg_eval base s.frontier s
  dsimp only at hbgev
  rw [ite_eq_right (by omega), ite_eq_left hp1,
    ite_eq_right (by omega : s.mem (base + hdrPhase) ≠ 5),
    ite_eq_right (by omega), ite_eq_left hp1] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  obtain ⟨hst_log, hmc_log⟩ := tickLogProg_eval base s
  set s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
  have hwf_tick : Memory.WellFormed w s_tick :=
    wf_step hwf (validHistory_bgTickProg hwf hpre_bg)
  set L' : DualLatent c U V := { L with elapsed := L.elapsed + 1 }
  by_cases hlt2 : sub < 2
  · -- Shift step (`sub ∈ {0, 1}`, stays in `ph = 1`):
    have hlog_eq0 : ¬(1 < acc) → sub = 0 → lk = Nat.log 2 nDst := fun hn1 hs0 => by
      obtain ⟨ha1, hlo, hhi⟩ := hsub0 hs0
      have ha_eq : acc = 1 := by omega
      rw [ha_eq] at hlo hhi; rw [one_mul] at hlo
      exact ((Nat.log_eq_iff (Or.inr ⟨by decide, hd_pos.ne'⟩)).mpr
        ⟨hlo, by rw [Nat.pow_succ]; omega⟩).symm
    obtain ⟨hst_sh, hmc_sh⟩ := tickLogShiftProg_eval s (by omega) hlog_eq0
    have hs_tick_sh : s_tick = (Memory.spec 0).clientState s (tickLogShiftProg base) := by
      rw [hst_bg, hst_log, ite_eq_left hlt2]
    have hfr_tick : s_tick.frontier = s.frontier := by
      rw [hs_tick_sh, hst_sh]; split_ifs <;> rfl
    have hout_sh : ∀ a, a ≠ base + hdrLogAcc → a ≠ base + hdrLogK → a ≠ base + hdrLogN →
        a ≠ base + hdrClogN → a ≠ base + hdrPtrB → a ≠ base + hdrPgB →
        a ≠ base + hdrLogSub → a ≠ base + hdrEll → s_tick.mem a = s.mem a := by
      intro a h1 h2 h3 h4 h5 h6 h7 h8
      rw [hs_tick_sh, hst_sh]
      split_ifs <;> dsimp only
      · rw [Function.update_of_ne h2, Function.update_of_ne h1]
      · rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h7,
          Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4,
          Function.update_of_ne h3]
      · rw [Function.update_of_ne h7, Function.update_of_ne h8]
    have hph_t : s_tick.mem (base + hdrPhase) = 1 := by
      rw [show s_tick.mem (base + hdrPhase) = s.mem (base + hdrPhase) by
        apply hout_sh <;> exact base_add_ne (by decide)]
      exact hp1
    have hst_t : s_tick.mem (base + hdrStage) = 0 := by
      rw [show s_tick.mem (base + hdrStage) = s.mem (base + hdrStage) by
        apply hout_sh <;> exact base_add_ne (by decide)]
      exact hst0
    have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc := by
      apply hout_sh <;> exact base_add_ne (by decide)
    have hnD_t : s_tick.mem (base + hdrNDst) = nDst := by
      apply hout_sh <;> exact base_add_ne (by decide)
    have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc := by
      apply hout_sh <;> exact base_add_ne (by decide)
    have hmD_t : s_tick.mem (base + hdrMDst) = 0 := by
      rw [show s_tick.mem (base + hdrMDst) = s.mem (base + hdrMDst) by
        apply hout_sh <;> exact base_add_ne (by decide)]
      exact hmD0
    have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo := by
      apply hout_sh <;> exact base_add_ne (by decide)
    have hibH_t : s_tick.mem (base + hdrItemHi) = ibLo := by
      rw [show s_tick.mem (base + hdrItemHi) = s.mem (base + hdrItemHi) by
        apply hout_sh <;> exact base_add_ne (by decide)]
      exact hibH1
    have hqL_t : s_tick.mem (base + hdrQLo) = qLo := by
      apply hout_sh <;> exact base_add_ne (by decide)
    have hqH_t : s_tick.mem (base + hdrQHi) = qLo := by
      rw [show s_tick.mem (base + hdrQHi) = s.mem (base + hdrQHi) by
        apply hout_sh <;> exact base_add_ne (by decide)]
      exact hqH1
    have hsl_t : EpochSlotInv c U V w loFr (dualPSrc base s_tick.mem) (dualMbSrc base s_tick.mem)
        (directSlotIo w vB base ibLo qLo nLive) 0 false L.slotSrc s_tick.mem := by
      have hpS : dualPSrc base s_tick.mem = dualPSrc base s.mem := by
        unfold dualPSrc; rw [hst_t, hst0]
      have hmS : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
        unfold dualMbSrc; rw [hst_t, hnS_t, hst0]; rfl
      rw [hpS, hmS]
      exact hsl_lo.congr_mem
        (fun a h1 _ => by
          unfold dualPSrc at h1; rw [ite_eq_left hst0] at h1
          apply hout_sh <;> (dsimp only [hdrPBase0, hdrLogAcc, hdrLogK, hdrLogN, hdrClogN,
            hdrPtrB, hdrPgB, hdrLogSub, hdrEll] at *; omega))
        (fun a ha => by
          unfold slotOwnsNonPageMeta dualMbSrc at ha; rw [ite_eq_left hst0] at ha
          apply hout_sh <;>
            (rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> split_ifs at h1 <;>
              dsimp only [hdrSmallMeta0, hdrLogAcc, hdrLogK, hdrLogN, hdrClogN, hdrPtrB, hdrPgB,
                hdrLogSub, hdrEll] at * <;> omega))
        (fun a ha => by
          simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
            ↓reduceIte] at ha
          apply hout_sh <;>
            (dsimp only [hdrLogAcc, hdrLogK, hdrLogN, hdrClogN, hdrPtrB, hdrPgB, hdrLogSub,
              hdrEll] at *; omega))
    have hph1_step :
        let sub' := s_tick.mem (base + hdrLogSub)
        let acc' := s_tick.mem (base + hdrLogAcc)
        let lk' := s_tick.mem (base + hdrLogK)
        (sub' ≤ 2 ∧
          (sub' = 0 → 1 ≤ acc' ∧ acc' * 2 ^ lk' ≤ nDst ∧ nDst < (acc' + 1) * 2 ^ lk') ∧
          (sub' = 1 →
            s_tick.mem (base + hdrLogN) = Nat.log 2 nDst ∧
            s_tick.mem (base + hdrClogN) = Nat.clog 2 nDst ∧
            s_tick.mem (base + hdrPtrB) = globalPtrBits nDst ∧
            s_tick.mem (base + hdrPgB) = pageSizeWhp nDst ∧
            acc' * 2 ^ lk' ≤ Nat.clog 2 nDst - 1 ∧
            (1 ≤ acc' → Nat.clog 2 nDst - 1 < (acc' + 1) * 2 ^ lk') ∧
            (acc' = 0 → lk' = 0 ∧ Nat.clog 2 nDst ≤ 1)) ∧
          (sub' = 2 →
            s_tick.mem (base + hdrLogN) = Nat.log 2 nDst ∧
            s_tick.mem (base + hdrEll) = Dynamic.logLogFactor nDst ∧
            s_tick.mem (base + hdrPtrB) = globalPtrBits nDst ∧
            s_tick.mem (base + hdrPgB) = pageSizeWhp nDst)) ∧
        remRebuildBudget (max (whpThreshold c) nSrc) 0 1 sub' lk' 0 0 0 0 0 0 0 0 0 0 + 1 ≤
          remRebuildBudget (max (whpThreshold c) nSrc) 0 1 sub lk 0 0 0 0 0 0 0 0 0 0 := by
      dsimp only
      have hlk_le := (hlk_bounds hlt2).2
      rw [hs_tick_sh, hst_sh]
      by_cases ha1 : 1 < acc
      · rw [ite_eq_left ha1]; dsimp only
        have hsub' : Function.update (Function.update s.mem (base + hdrLogAcc) (acc / 2))
            (base + hdrLogK) (lk + 1) (base + hdrLogSub) = sub := by
          rw [Function.update_of_ne (by exact base_add_ne (by decide)),
            Function.update_of_ne (by exact base_add_ne (by decide))]
        have hacc' : Function.update (Function.update s.mem (base + hdrLogAcc) (acc / 2))
            (base + hdrLogK) (lk + 1) (base + hdrLogAcc) = acc / 2 := by
          rw [Function.update_of_ne (by exact base_add_ne (by decide)), Function.update_self]
        have hlk' : Function.update (Function.update s.mem (base + hdrLogAcc) (acc / 2))
            (base + hdrLogK) (lk + 1) (base + hdrLogK) = lk + 1 := Function.update_self ..
        rw [hsub', hacc', hlk']
        refine ⟨⟨hsub_le, fun hs0 => ?_, fun hs1 => ?_, fun hs2 => absurd hs2 (by omega)⟩, ?_⟩
        · obtain ⟨_, hlo, hhi⟩ := hsub0 hs0
          have hd2 := Nat.div_add_mod acc 2
          exact ⟨by omega,
            by rw [Nat.pow_succ]; calc acc / 2 * (2 ^ lk * 2) = (acc / 2 * 2) * 2 ^ lk := by ring
                 _ ≤ acc * 2 ^ lk := Nat.mul_le_mul_right _ (by omega)
                 _ ≤ nDst := hlo,
            by rw [Nat.pow_succ]; calc nDst < (acc + 1) * 2 ^ lk := hhi
                 _ ≤ ((acc / 2 + 1) * 2) * 2 ^ lk := Nat.mul_le_mul_right _ (by omega)
                 _ = (acc / 2 + 1) * (2 ^ lk * 2) := by ring⟩
        · obtain ⟨e1, e2, e3, e4, hlo, hhi, _⟩ := hsub1 hs1
          have hd2 := Nat.div_add_mod acc 2
          exact ⟨by
              rw [Function.update_of_ne (by exact base_add_ne (by decide)),
                Function.update_of_ne (by exact base_add_ne (by decide))]; exact e1,
            by rw [Function.update_of_ne (by exact base_add_ne (by decide)),
                 Function.update_of_ne (by exact base_add_ne (by decide))]; exact e2,
            by rw [Function.update_of_ne (by exact base_add_ne (by decide)),
                 Function.update_of_ne (by exact base_add_ne (by decide))]; exact e3,
            by rw [Function.update_of_ne (by exact base_add_ne (by decide)),
                 Function.update_of_ne (by exact base_add_ne (by decide))]; exact e4,
            by rw [Nat.pow_succ]; calc acc / 2 * (2 ^ lk * 2) = (acc / 2 * 2) * 2 ^ lk := by ring
                 _ ≤ acc * 2 ^ lk := Nat.mul_le_mul_right _ (by omega)
                 _ ≤ Nat.clog 2 nDst - 1 := hlo,
            fun _ => by
              rw [Nat.pow_succ]
              calc Nat.clog 2 nDst - 1 < (acc + 1) * 2 ^ lk := hhi (by omega)
                _ ≤ ((acc / 2 + 1) * 2) * 2 ^ lk := Nat.mul_le_mul_right _ (by omega)
                _ = (acc / 2 + 1) * (2 ^ lk * 2) := by ring,
            fun hz => absurd hz (by omega)⟩
        · unfold remRebuildBudget; dsimp only
          by_cases hs0 : sub = 0
          · simp only [hs0, ↓reduceIte]; omega
          · have hs1 : sub = 1 := by omega
            simp only [hs1, Nat.one_ne_zero, ↓reduceIte]; omega
      · rw [ite_eq_right ha1]
        by_cases hs0 : sub = 0
        · rw [ite_eq_left hs0]; dsimp only
          have hk_eq := hlog_eq0 ha1 hs0
          set m' := Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update s.mem (base + hdrLogN) lk)
              (base + hdrClogN) (Nat.clog 2 nDst)) (base + hdrPtrB) (lk + 1))
              (base + hdrPgB) (pageSizeWhp nDst)) (base + hdrLogSub) 1)
              (base + hdrLogAcc) (Nat.clog 2 nDst - 1)) (base + hdrLogK) 0
          have hm_lk : m' (base + hdrLogK) = 0 := Function.update_self ..
          have hm_la : m' (base + hdrLogAcc) = Nat.clog 2 nDst - 1 := by
            dsimp only [m']
            rw [Function.update_of_ne (by exact base_add_ne (by decide))]
            exact Function.update_self ..
          have hm_ls : m' (base + hdrLogSub) = 1 := by
            dsimp only [m']
            iterate 2 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
            exact Function.update_self ..
          have hm_pg : m' (base + hdrPgB) = pageSizeWhp nDst := by
            dsimp only [m']
            iterate 3 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
            exact Function.update_self ..
          have hm_pb : m' (base + hdrPtrB) = lk + 1 := by
            dsimp only [m']
            iterate 4 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
            exact Function.update_self ..
          have hm_cl : m' (base + hdrClogN) = Nat.clog 2 nDst := by
            dsimp only [m']
            iterate 5 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
            exact Function.update_self ..
          have hm_ln : m' (base + hdrLogN) = lk := by
            dsimp only [m']
            iterate 6 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
            exact Function.update_self ..
          rw [hm_ls, hm_la, hm_lk, hm_ln, hm_cl, hm_pb, hm_pg]
          have hpb_eq : lk + 1 = globalPtrBits nDst := by
            rw [hk_eq]; unfold globalPtrBits; exact (clog_succ_eq_of_log hd_pos).symm
          refine ⟨⟨by decide, fun h0 => absurd h0 (by decide),
            fun _ => ⟨hk_eq, rfl, hpb_eq, rfl, by simp, fun _ => by simp,
              fun hz => ⟨rfl, by omega⟩⟩,
            fun h2 => absurd h2 (by decide)⟩, ?_⟩
          unfold remRebuildBudget; simp only [hs0, Nat.one_ne_zero, ↓reduceIte, Nat.sub_zero]; omega
        · have hs1 : sub = 1 := by omega
          rw [ite_eq_right hs0]; dsimp only
          obtain ⟨e1, _, e3, e4, hlo, hhi, hacc0⟩ := hsub1 hs1
          have hcl_ge2 : 2 ≤ Nat.clog 2 nDst :=
            (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega)
          have ha_eq : acc = 1 := by
            by_cases hz : acc = 0
            · have := (hacc0 hz).2; omega
            · omega
          rw [ha_eq, one_mul] at hlo
          have hhi' := hhi (by omega); rw [ha_eq] at hhi'
          have hk_eq : lk = Nat.log 2 (Nat.clog 2 nDst - 1) :=
            ((Nat.log_eq_iff (Or.inr ⟨by decide, by omega⟩)).mpr
              ⟨hlo, by rw [Nat.pow_succ]; omega⟩).symm
          have hell_eq : lk + 1 = Dynamic.logLogFactor nDst := by
            rw [hk_eq, logLogFactor_eq_of_log hd_ge4]
          set m' := Function.update (Function.update s.mem (base + hdrEll) (lk + 1))
            (base + hdrLogSub) 2
          have hm_ls : m' (base + hdrLogSub) = 2 := Function.update_self ..
          have hm_el : m' (base + hdrEll) = lk + 1 := by
            dsimp only [m']
            rw [Function.update_of_ne (by exact base_add_ne (by decide))]
            exact Function.update_self ..
          rw [hm_ls, hm_el]
          refine ⟨⟨by decide, fun h0 => absurd h0 (by decide), fun h1 => absurd h1 (by decide),
            fun _ => ⟨by
                dsimp only [m']
                rw [Function.update_of_ne (by exact base_add_ne (by decide)),
                  Function.update_of_ne (by exact base_add_ne (by decide))]; exact e1,
              hell_eq,
              by dsimp only [m']
                 rw [Function.update_of_ne (by exact base_add_ne (by decide)),
                   Function.update_of_ne (by exact base_add_ne (by decide))]; exact e3,
              by dsimp only [m']
                 rw [Function.update_of_ne (by exact base_add_ne (by decide)),
                   Function.update_of_ne (by exact base_add_ne (by decide))]; exact e4⟩⟩, ?_⟩
          unfold remRebuildBudget; simp only [hs1, Nat.one_ne_zero, show (2 : ℕ) ≠ 0 by decide,
            show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]; omega
    refine ⟨hpre_bg, hfr_tick, hwf_tick, ?_, ?_⟩
    · intro addr hlt
      apply hout_sh <;>
        (dsimp only [hdrLogAcc, hdrLogK, hdrLogN, hdrClogN, hdrPtrB, hdrPgB, hdrLogSub,
          hdrEll] at *; omega)
    · rw [ite_eq_left (by omega : s.mem (base + hdrPhase) ≠ 5)]
      refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
          (fun ⟨h9, _⟩ => by rw [hp1] at h9; cases h9) rfl rfl, ?_,
        fun _ _ => by rw [hmc_bg, hmc_log, ite_eq_left hlt2]; omega⟩
      refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
      · rw [hnS_t, hph_t, ite_eq_right (by decide : 1 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
      · rw [hph_t, ite_eq_left (by decide : 1 < 2), hibL_t, hqL_t, hfr_tick]
        refine ⟨hfr_lo, hdiff_le, ?_⟩
        exact
          { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
            wf := ⟨lt_of_le_of_lt hfr_lo hwf.1, fun a => hwf_tick.2 a⟩
            base_fr := by dsimp only [loFr]; rw [hibL_eq]; omega
            hdr := rootStaticHeader_congr hhdr fun off hoff => by
              apply hout_sh <;>
                (dsimp only [hdrLogAcc, hdrLogK, hdrLogN, hdrClogN, hdrPtrB, hdrPgB, hdrLogSub,
                  hdrEll] at *; omega)
            live_eq := by
              rw [show s_tick.mem (base + hdrLive) = s.mem (base + hdrLive) by
                apply hout_sh <;> exact base_add_ne (by decide)]
              exact hlive_eq
            live_le := hlive_le
            ph_le := by dsimp only; rw [hph_t]; decide
            stg_le := by dsimp only; rw [hst_t]; decide
            mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
            cache_src := by
              dsimp only; rw [hnS_t]
              exact hostCacheValid_congr_mem hcache_s fun k hk => by
                apply hout_sh <;>
                  (dsimp only [hdrSrcOd, hdrLogAcc, hdrLogK, hdrLogN, hdrClogN, hdrPtrB, hdrPgB,
                    hdrLogSub, hdrEll] at *; omega)
            nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
            sched := by
              dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
              refine
                { nDst_bounds := Or.inr ⟨hnD_t.symm ▸ hth_d.1, hnD_t.symm ▸ hth_d.2⟩
                  nDst_zero := fun hz => absurd (hnD_t.symm.trans hz) hd_pos.ne'
                  stg_one := fun h1 => absurd (hst_t.symm.trans h1) (by decide)
                  post_trig := by dsimp only [L']; rw [hnS_t]; exact hsched.post_trig
                  trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                  drift_hi := by
                    dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    simpa using hsched.drift_hi
                  drift_lo := by
                    dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    simpa using hsched.drift_lo
                  ibLo_eq := by
                    dsimp only; rw [hibL_t, hph_t, ite_eq_left (by decide : 1 < 10), hmS_t]
                    exact hibL_eq
                  qLo_eq := by
                    dsimp only; rw [hqL_t, hph_t, ite_eq_left (by decide : 1 < 10), hnS_t]
                    have hq := hsched.qLo_eq; rwa [ite_eq_left (by omega)] at hq
                  ph1 := fun _ => by
                    dsimp only
                    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    rw [hst_t, hnD_t, hmD_t, hibH_t, hibL_t, hqH_t, hqL_t]
                    exact ⟨rfl, hd_pos, rfl, rfl, rfl, le_rfl, le_rfl⟩
                  ge2 := fun h2 => by dsimp only at h2; rw [hph_t] at h2; omega
                  ph2 := fun h2 => absurd (hph_t.symm.trans h2) (by decide)
                  ph3_10 := fun h3 => by dsimp only at h3; rw [hph_t] at h3; omega
                  ph11 := fun h11 => absurd (hph_t.symm.trans h11) (by decide)
                  budget := by
                    dsimp only [L']
                    rw [hnS_t, hst_t, hph_t, remRebuildBudget_ph1_eq]
                    have h2 := two_le_remRebuildBudget_ph1 (max (whpThreshold c) nSrc)
                      (s_tick.mem (base + hdrLogSub)) (s_tick.mem (base + hdrLogK))
                    have hstep_b := hph1_step.2
                    have hrem_eq : remRebuildBudget (max (whpThreshold c) nSrc) 0 1 sub lk
                        0 0 0 0 0 0 0 0 0 0 =
                        (if sub = 0 then (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 2 - lk) +
                            (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 3) + 1
                         else if sub = 1 then
                            (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 2 - lk) + 1
                         else 1) +
                        futureRebuildBudget (max (whpThreshold c) nSrc) 0 1 := rfl
                    rw [hrem_eq] at hstep_b
                    have hrb := hrem_b.2.1
                    change 16 * (L.elapsed + ((if sub = 0 then
                        (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 2 - lk) +
                          (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 3) + 1
                      else if sub = 1 then
                        (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 2 - lk) + 1
                      else 1) + futureRebuildBudget (max (whpThreshold c) nSrc) 0 1)) ≤
                      max (whpThreshold c) nSrc at hrb
                    generalize max (whpThreshold c) nSrc = nRef at h2 hstep_b hrb ⊢
                    clear *- h2 hstep_b hrb
                    omega }
            pad_fits := by
              dsimp only
              rw [hnS_t, hph_t, ite_eq_right (by decide : 1 ≠ 0), hnD_t]
              have hp := h.pad_fits; rwa [ite_eq_right (by omega)] at hp
            ph1_inv := fun _ => by dsimp only; rw [hnD_t]; exact hph1_step.1
            ph3_inv := fun h3 => absurd (hph_t.symm.trans h3) (by decide)
            ph4_inv := fun h4 => absurd (hph_t.symm.trans h4) (by decide)
            pDst_pre := fun h25 _ _ => by dsimp only at h25; rw [hph_t] at h25; omega
            ph5_inv := fun h5 => absurd (hph_t.symm.trans h5) (by decide)
            ph6_inv := fun h6 => absurd (hph_t.symm.trans h6) (by decide)
            ph7_inv := fun h7 => absurd (hph_t.symm.trans h7) (by decide)
            ph8_inv := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
            ph9_inv := fun h9 => absurd (hph_t.symm.trans h9) (by decide)
            ph10_inv := fun h10 => absurd (hph_t.symm.trans h10) (by decide)
            sl_le7 := fun _ => by
              dsimp only
              have hcap_t : dualCapSrc base s_tick.mem = nSrc := by
                unfold dualCapSrc; rw [hst_t, hnS_t, ite_eq_left rfl]
              rw [hcap_t, hph_t]
              refine ⟨hcap_s.trans hcap_eq, (h.sl_le7 (by omega)).2.1, ?_,
                fun _ hs_p => by
                  dsimp only [L']
                  have hl := hlen_s (by omega) (hcap_eq ▸ hs_p)
                  simp only [Bool.false_eq_true, ↓reduceIte, add_zero, hcap_eq] at hl ⊢
                  omega⟩
              unfold activeSrcIo; rw [ite_eq_left (by decide : 1 < 3), hibL_t, hqL_t]
              exact hsl_t
            sl_67 := fun h67 => by dsimp only at h67; rw [hph_t] at h67; omega
            sl_8 := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
            sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_t] at h9; omega }
  · -- Finish step (`sub = 2`, `tickLogFinishProg` transitions `1 → 2`):
    have hs2 : sub = 2 := by omega
    obtain ⟨hlog_e, hell_e, hptr_e, hpg_e⟩ := hsub2 hs2
    obtain ⟨hst_fin, hmc_fin⟩ := tickLogFinishProg_eval base s
    have hs_tick_fin : s_tick = (Memory.spec 0).clientState s (tickLogFinishProg base) := by
      rw [hst_bg, hst_log, ite_eq_right hlt2]
    set mDst := epochMetaWordsWhp c w nDst
    set pad := max mSrc mDst
    set meta1 := base + 192 + pad
    set ibHi := meta1 + mDst + 4
    set qDst := quotBitsWhp U nDst
    set qHi := max qLo qDst
    let fl0 : FastEpochLayout := ⟨c, U, V, w, nDst, base + 192, base + hdrPBase1,
      directSlotIo w vB base ibHi qHi nLive⟩
    let fl1 : FastEpochLayout := ⟨c, U, V, w, nDst, meta1, base + hdrPBase1,
      directSlotIo w vB base ibHi qHi nLive⟩
    have hwlp_sp := writeLargeParamTableProg_spec (fl := fl0) (s := s)
      (Or.inl (by dsimp only [fl0, hdrPBase1]; omega)) hth_d.1 hth_d.2 hw_pos hhdr
    dsimp only [fl0] at hwlp_sp
    rw [← hlog_e, ← hell_e, ← hpg_e] at hwlp_sp
    obtain ⟨hwlp_res, hwlp_fr, hwlp_mc, hwlp_k48, _, _, hwlp_out⟩ := hwlp_sp
    have hfr_tick : s_tick.frontier = s.frontier := by
      rw [hs_tick_fin, hst_fin]; exact hwlp_fr
    have hm32 : 32 ≤ mDst := thirtyTwo_le_epochMetaWordsWhp hth_d.1
    have hqDst_eq :
        s.mem (base + hdrKeyBits) - (s.mem (base + hdrLogN) - 12 * s.mem (base + hdrEll)) =
        qDst := by
      rw [hhdr.2.2.2.1, hlog_e, hell_e]; rfl
    set s_wlp := (Memory.spec 0).clientState s
      (writeLargeParamTableProg ((base, base + hdrPBase1),
        ((nDst, base + 192), ((s.mem (base + hdrLogN), s.mem (base + hdrEll)),
          s.mem (base + hdrPgB)))))
    have hoffFp_w : s_wlp.mem (base + hdrPBase1 + 30) = offFpHash c w nDst :=
      hwlp_k48 30 (by decide)
    have hs_tick_mem : s_tick.mem =
        Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update
            (Function.update s_wlp.mem (base + hdrPBase1 + 1) meta1)
            (base + hdrPBase1 + 61) (meta1 + 32))
            (base + hdrPBase1 + 62) (meta1 + offFpHash c w nDst))
            (base + hdrMDst) mDst)
            (base + hdrPad) pad)
            (base + hdrItemHi) ibHi)
            (base + hdrQHi) qHi)
            (base + hdrDstOd) (offPageDir c w nDst))
            (base + hdrDstOt) (offPageTail c w nDst))
            (base + hdrDstPb) (globalPtrBits nDst))
            (base + hdrDstPg) (pageSizeWhp nDst))
            (base + hdrDstMp) (nDst / pageSizeWhp nDst + 4))
            (base + hdrPhase) 2 := by
      rw [hs_tick_fin, hst_fin]; dsimp only
      rw [hwlp_res, hoffFp_w, hqDst_eq, hptr_e, hpg_e]
    have hout_fin : ∀ a,
        ¬(base + hdrPBase1 ≤ a ∧ a < base + hdrPBase1 + 48 ∨
          a = base + hdrPBase1 + 61 ∨ a = base + hdrPBase1 + 62) →
        a ≠ base + hdrMDst → a ≠ base + hdrPad → a ≠ base + hdrItemHi → a ≠ base + hdrQHi →
        a ≠ base + hdrDstOd → a ≠ base + hdrDstOt → a ≠ base + hdrDstPb →
        a ≠ base + hdrDstPg → a ≠ base + hdrDstMp → a ≠ base + hdrPhase →
        s_tick.mem a = s.mem a := by
      intro a hp1_not h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rw [hs_tick_mem]
      rw [Function.update_of_ne h10, Function.update_of_ne h9, Function.update_of_ne h8,
        Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h5,
        Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
        Function.update_of_ne h1,
        Function.update_of_ne (fun he => hp1_not (Or.inr (Or.inr he))),
        Function.update_of_ne (fun he => hp1_not (Or.inr (Or.inl he))),
        Function.update_of_ne (fun he => hp1_not (Or.inl ⟨by omega, by omega⟩))]
      exact hwlp_out a hp1_not
    have hout_fin_off : ∀ off < 128,
        off ≠ hdrMDst → off ≠ hdrPad → off ≠ hdrItemHi → off ≠ hdrQHi →
        off ≠ hdrDstOd → off ≠ hdrDstOt → off ≠ hdrDstPb →
        off ≠ hdrDstPg → off ≠ hdrDstMp → off ≠ hdrPhase →
        s_tick.mem (base + off) = s.mem (base + off) :=
      fun off hoff h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
        hout_fin (base + off) (by dsimp only [hdrPBase1]; omega)
          (base_add_ne h1) (base_add_ne h2) (base_add_ne h3) (base_add_ne h4) (base_add_ne h5)
          (base_add_ne h6) (base_add_ne h7) (base_add_ne h8) (base_add_ne h9) (base_add_ne h10)
    have hph_t : s_tick.mem (base + hdrPhase) = 2 := by
      rw [hs_tick_mem]; exact Function.update_self ..
    have hmD_t : s_tick.mem (base + hdrMDst) = mDst := by
      rw [hs_tick_mem]; iterate 9 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
      exact Function.update_self ..
    have hpad_t : s_tick.mem (base + hdrPad) = pad := by
      rw [hs_tick_mem]; iterate 8 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
      exact Function.update_self ..
    have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi := by
      rw [hs_tick_mem]; iterate 7 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
      exact Function.update_self ..
    have hqH_t : s_tick.mem (base + hdrQHi) = qHi := by
      rw [hs_tick_mem]; iterate 6 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
      exact Function.update_self ..
    have hcache_d_t : HostCacheValid c w nDst hdrDstOd base s_tick.mem := fun _ => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hs_tick_mem]; iterate 5 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
        exact Function.update_self ..
      · rw [Nat.add_assoc, hs_tick_mem]
        iterate 4 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
        exact Function.update_self ..
      · rw [Nat.add_assoc, hs_tick_mem]
        iterate 3 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
        exact Function.update_self ..
      · rw [Nat.add_assoc, hs_tick_mem]
        iterate 2 rw [Function.update_of_ne (by exact base_add_ne (by decide))]
        exact Function.update_self ..
      · rw [Nat.add_assoc, hs_tick_mem, Function.update_of_ne (by exact base_add_ne (by decide))]
        exact Function.update_self ..
    have hst_t : s_tick.mem (base + hdrStage) = 0 := by
      rw [show s_tick.mem (base + hdrStage) = s.mem (base + hdrStage) by
        apply hout_fin_off <;> decide]
      exact hst0
    have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc := by apply hout_fin_off <;> decide
    have hnD_t : s_tick.mem (base + hdrNDst) = nDst := by apply hout_fin_off <;> decide
    have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc := by apply hout_fin_off <;> decide
    have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo := by apply hout_fin_off <;> decide
    have hqL_t : s_tick.mem (base + hdrQLo) = qLo := by apply hout_fin_off <;> decide
    have hlt_hiFr : s.frontier < ibHi + pairStreamWords nLive qHi vB w := by
      have hpw_q : pairStreamWords nLive qLo vB w ≤ pairStreamWords nLive qHi vB w :=
        pairStreamWords_mono_q (le_max_left qLo qDst)
      have hmS_pad : mSrc ≤ pad := le_max_left mSrc mDst
      dsimp only [ibHi, meta1]
      omega
    have hqHi_w : qHi ≤ w :=
      max_le hqLo_w ((Nat.sub_le _ _).trans (Nat.clog_le_of_le_pow hUw.le))
    have hgrow_le : ibHi + pairStreamWords nLive qHi vB w - s.frontier ≤
        9 * max (whpThreshold c) nSrc := by
      have hd_hi' : nLive ≤ L.nTrig + (L.elapsed + 1) := by
        have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
      have hd_lo' : L.nTrig ≤ nLive + (L.elapsed + 1) := by
        have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
      have hel_le' : 16 * (L.elapsed + 1) ≤ max (whpThreshold c) nSrc := by
        have hel := hrem_b.2.2
        change 16 * (L.elapsed + 2) ≤ max (whpThreshold c) nSrc at hel
        omega
      have hfr_lo' : base + 192 + mSrc + pairStreamWords nLive qLo vB w ≤ s.frontier := by
        have hf : ibLo + pairStreamWords nLive qLo vB w ≤ s.frontier := hfr_lo
        rwa [hibL_eq] at hf
      exact log_finish_growDiff_le hsched.post_trig hsched.trig_cap hd_hi' hd_lo' hel_le'
        hlive_le hth_d.1 hnDst_w hw_pos (by omega) rfl rfl hfr_lo'
    have hpDst_pt : fl1.ParamTable
        (dualPh5MaskMem V w base (base + hdrPBase1) ibHi qHi nLive s_tick.mem) := by
      have hp1_k48 : ∀ k < 48, s_tick.mem (base + hdrPBase1 + k) = fl1.paramWord k := by
        intro k hk
        rw [hs_tick_mem]
        iterate 10 rw [Function.update_of_ne (by dsimp only [hdrPBase1, hdrMDst, hdrPad,
          hdrItemHi, hdrQHi, hdrDstOd, hdrDstOt, hdrDstPb, hdrDstPg, hdrDstMp, hdrPhase]; omega)]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        by_cases hk1 : k = 1
        · subst hk1; exact Function.update_self ..
        · rw [Function.update_of_ne (by omega), hwlp_k48 k hk]
          interval_cases k <;> first | rfl | exact absurd rfl hk1
      have hp1_61 : s_tick.mem (base + hdrPBase1 + 61) = fl1.paramWord 61 := by
        rw [hs_tick_mem]
        iterate 10 rw [Function.update_of_ne (by dsimp only [hdrPBase1, hdrMDst, hdrPad,
          hdrItemHi, hdrQHi, hdrDstOd, hdrDstOt, hdrDstPb, hdrDstPg, hdrDstMp, hdrPhase]; omega)]
        rw [Function.update_of_ne (by omega), Function.update_self]; rfl
      have hp1_62 : s_tick.mem (base + hdrPBase1 + 62) = fl1.paramWord 62 := by
        rw [hs_tick_mem]
        iterate 10 rw [Function.update_of_ne (by dsimp only [hdrPBase1, hdrMDst, hdrPad,
          hdrItemHi, hdrQHi, hdrDstOd, hdrDstOt, hdrDstPb, hdrDstPg, hdrDstMp, hdrPhase]; omega)]
        exact Function.update_self ..
      rw [dualPh5MaskMem_eq_setSlotIo]
      exact paramTable_of_writeLarge_and_setSlotIo hp1_k48 hp1_61 hp1_62
    have hsl_t : EpochSlotInv c U V w s_tick.frontier (dualPSrc base s_tick.mem)
        (dualMbSrc base s_tick.mem)
        (directSlotIo w vB base ibLo qLo nLive) 0 false L.slotSrc s_tick.mem := by
      have hpS : dualPSrc base s_tick.mem = dualPSrc base s.mem := by
        unfold dualPSrc; rw [hst_t, hst0]
      have hmS : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
        unfold dualMbSrc; rw [hst_t, hnS_t, hst0]; rfl
      rw [hpS, hmS, hfr_tick]
      exact hsl_s.congr_mem
        (fun a h1 h2 => by
          have hp0 : base + hdrPBase0 ≤ a ∧ a < base + hdrPBase0 + 64 := by
            unfold dualPSrc at h1 h2; rw [ite_eq_left hst0] at h1 h2; exact ⟨h1, h2⟩
          apply hout_fin <;>
            (dsimp only [hdrPBase0, hdrPBase1, hdrMDst, hdrPad, hdrItemHi, hdrQHi, hdrDstOd,
              hdrDstOt, hdrDstPb, hdrDstPg, hdrDstMp, hdrPhase] at hp0 ⊢; omega))
        (fun a ha => by
          have ha_r := slotOwnsNonPageMeta_src_range hcap_s
            (fun hne => absurd hst0 hne) ha
          rcases ha_r with ⟨h1, h2⟩ | h192
          · apply hout_fin <;>
              (dsimp only [hdrPBase1, hdrMDst, hdrPad, hdrItemHi, hdrQHi, hdrDstOd, hdrDstOt,
                hdrDstPb, hdrDstPg, hdrDstMp, hdrPhase]; clear *- h1 h2; omega)
          · apply hout_fin <;>
              (dsimp only [hdrPBase1, hdrMDst, hdrPad, hdrItemHi, hdrQHi, hdrDstOd, hdrDstOt,
                hdrDstPb, hdrDstPg, hdrDstMp, hdrPhase]; clear *- h192; omega))
        (fun a ha => by
          have ha_lo : base + 192 ≤ a := by
            simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
              ↓reduceIte] at ha
            have ha1 := ha.1; clear *- ha1 hibL_eq; omega
          apply hout_fin <;>
            (dsimp only [hdrPBase1, hdrMDst, hdrPad, hdrItemHi, hdrQHi, hdrDstOd, hdrDstOt,
              hdrDstPb, hdrDstPg, hdrDstMp, hdrPhase]; clear *- ha_lo; omega))
    refine ⟨hpre_bg, hfr_tick, hwf_tick, ?_, ?_⟩
    · intro addr hlt
      apply hout_fin <;>
        (dsimp only [hdrPBase1, hdrMDst, hdrPad, hdrItemHi, hdrQHi, hdrDstOd, hdrDstOt, hdrDstPb,
          hdrDstPg, hdrDstMp, hdrPhase]; clear *- hlt; omega)
    · rw [ite_eq_left (by omega : s.mem (base + hdrPhase) ≠ 5)]
      refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
          (fun ⟨h9, _⟩ => by rw [hp1] at h9; cases h9) rfl rfl, ?_,
        fun _ _ => by rw [hmc_bg, hmc_log, ite_eq_right hlt2, hmc_fin, hwlp_mc]; omega⟩
      refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
      · rw [hnS_t, hph_t, ite_eq_right (by decide : 2 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
      · rw [hph_t, ite_eq_right (by decide : ¬(2 < 2)), ite_eq_left rfl,
          hibH_t, hqH_t, hfr_tick]
        refine ⟨hlt_hiFr, ?_⟩
        exact
          { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
            wf := hwf_tick, base_fr := by rw [hfr_tick]; exact hb192
            hdr := rootStaticHeader_congr hhdr fun off hoff =>
              hout_fin_off off (by clear *- hoff; omega)
                (by dsimp only [hdrMDst]; clear *- hoff; omega)
                (by dsimp only [hdrPad]; clear *- hoff; omega)
                (by dsimp only [hdrItemHi]; clear *- hoff; omega)
                (by dsimp only [hdrQHi]; clear *- hoff; omega)
                (by dsimp only [hdrDstOd]; clear *- hoff; omega)
                (by dsimp only [hdrDstOt]; clear *- hoff; omega)
                (by dsimp only [hdrDstPb]; clear *- hoff; omega)
                (by dsimp only [hdrDstPg]; clear *- hoff; omega)
                (by dsimp only [hdrDstMp]; clear *- hoff; omega)
                (by dsimp only [hdrPhase]; clear *- hoff; omega)
            live_eq := by
              rw [show s_tick.mem (base + hdrLive) = s.mem (base + hdrLive) by
                apply hout_fin_off <;> decide]
              exact hlive_eq
            live_le := hlive_le
            ph_le := by rw [hph_t]; decide
            stg_le := by rw [hst_t]; decide
            mSrc_eq := by rw [hmS_t, hnS_t]; exact hmSrc_eq
            cache_src := by
              rw [hnS_t]
              exact hostCacheValid_congr_mem hcache_s fun k hk => by
                rw [show base + hdrSrcOd + k = base + (hdrSrcOd + k) by omega]
                apply hout_fin_off <;> (dsimp only [hdrSrcOd, hdrMDst, hdrPad, hdrItemHi, hdrQHi,
                  hdrDstOd, hdrDstOt, hdrDstPb, hdrDstPg, hdrDstMp, hdrPhase]; omega)
            nSrc_bounds := hnS_t.symm ▸ hnSrc_b
            sched := by
              rw [ite_eq_right (by rw [hph_t]; decide)]
              refine
                { nDst_bounds := Or.inr ⟨hnD_t.symm ▸ hth_d.1, hnD_t.symm ▸ hth_d.2⟩
                  nDst_zero := fun hz => absurd (hnD_t.symm.trans hz) hd_pos.ne'
                  stg_one := fun h1 => absurd (hst_t.symm.trans h1) (by decide)
                  post_trig := by dsimp only [L']; rw [hnS_t]; exact hsched.post_trig
                  trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                  drift_hi := by
                    dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                  drift_lo := by
                    dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                  ibLo_eq := by
                    rw [hibL_t, hph_t, ite_eq_left (by decide : 2 < 10), hmS_t]; exact hibL_eq
                  qLo_eq := by
                    rw [hqL_t, hph_t, ite_eq_left (by decide : 2 < 10), hnS_t]
                    have hq := hsched.qLo_eq; rwa [ite_eq_left (by omega)] at hq
                  ph1 := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
                  ge2 := fun _ => by
                    rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                    have hqL_src : qLo = (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc) := by
                      have hq := hsched.qLo_eq; rwa [ite_eq_left (by omega)] at hq
                    refine ⟨rfl, rfl, hcache_d_t, fun _ => ⟨?_, ?_, ?_⟩,
                      by rw [ite_eq_right hd_pos.ne'],
                      by rw [ite_eq_right hd_pos.ne', ← hqL_src]⟩
                    · rw [show s_tick.mem (base + hdrLogN) = s.mem (base + hdrLogN) by
                        apply hout_fin_off <;> decide]; exact hlog_e
                    · rw [show s_tick.mem (base + hdrEll) = s.mem (base + hdrEll) by
                        apply hout_fin_off <;> decide]; exact hell_e
                    · rw [show s_tick.mem (base + hdrPgB) = s.mem (base + hdrPgB) by
                        apply hout_fin_off <;> decide]; exact hpg_e
                  ph2 := fun _ => by
                    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    rw [hst_t, hibL_t, hqL_t, hibH_t, hqH_t, hfr_tick]
                    exact ⟨rfl, hfr_lo, hlt_hiFr.le⟩
                  ph3_10 := fun h3 => by rw [hph_t] at h3; omega
                  ph11 := fun h11 => absurd (hph_t.symm.trans h11) (by decide)
                  budget := by
                    dsimp only [L']
                    rw [hnS_t, hst_t, hph_t, hibH_t, hqH_t, hfr_tick]
                    unfold remRebuildBudget futureRebuildBudget
                    dsimp only
                    simp only [show (2 : ℕ) ≠ 1 by decide, Bool.false_eq_true, false_and,
                      ↓reduceIte, add_zero]
                    have hrb := hrem_b.2.1
                    change 16 * (L.elapsed + ((if sub = 0 then
                        (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 2 - lk) +
                          (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 3) + 1
                      else if sub = 1 then
                        (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 2 - lk) + 1
                      else 1) + futureRebuildBudget (max (whpThreshold c) nSrc) 0 1)) ≤
                      max (whpThreshold c) nSrc at hrb
                    rw [hs2] at hrb
                    simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
                      ↓reduceIte] at hrb
                    unfold futureRebuildBudget at hrb
                    dsimp only at hrb
                    simp only [↓reduceIte] at hrb
                    have hdiv := Nat.div_le_div_right (c := 1022) hgrow_le
                    change (ibHi + pairStreamWords (Dictionary.dom s_dict).card qHi (valBits V) w -
                        s.frontier) / 1022 ≤
                      9 * max (whpThreshold c) nSrc / 1022 at hdiv
                    have hf2 : 2 ≤ maxTailPhasesBudget (max (whpThreshold c) nSrc) := by
                      unfold maxTailPhasesBudget; omega
                    generalize max (whpThreshold c) nSrc = nRef at hrb hdiv hf2 ⊢
                    clear *- hrb hdiv hf2
                    omega }
            pad_fits := by
              rw [hnS_t, hph_t, ite_eq_right (by decide : 2 ≠ 0), hnD_t]
              have hp := h.pad_fits; rwa [ite_eq_right (by omega)] at hp
            ph1_inv := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
            ph3_inv := fun h3 => absurd (hph_t.symm.trans h3) (by decide)
            ph4_inv := fun h4 => absurd (hph_t.symm.trans h4) (by decide)
            pDst_pre := fun _ _ _ => by
              dsimp only
              have hmbD : dualMbDst base s_tick.mem = meta1 := by
                unfold dualMbDst
                rw [hph_t, ite_eq_left (by decide : 2 < 10), hnD_t, ite_eq_right hd_pos.ne',
                  hst_t, ite_eq_left rfl, hpad_t]
              have hpD : dualPDst base s_tick.mem = base + hdrPBase1 := by
                unfold dualPDst
                rw [hph_t, ite_eq_left (by decide : 2 < 10), hst_t, ite_eq_left rfl]
              rw [hnD_t, hmbD, hpD, hibH_t, hqH_t]
              exact hpDst_pt
            ph5_inv := fun h5 => absurd (hph_t.symm.trans h5) (by decide)
            ph6_inv := fun h6 => absurd (hph_t.symm.trans h6) (by decide)
            ph7_inv := fun h7 => absurd (hph_t.symm.trans h7) (by decide)
            ph8_inv := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
            ph9_inv := fun h9 => absurd (hph_t.symm.trans h9) (by decide)
            ph10_inv := fun h10 => absurd (hph_t.symm.trans h10) (by decide)
            sl_le7 := fun _ => by
              have hcap_t : dualCapSrc base s_tick.mem = nSrc := by
                unfold dualCapSrc; rw [hst_t, hnS_t, ite_eq_left rfl]
              rw [hcap_t, hph_t]
              refine ⟨hcap_s.trans hcap_eq, (h.sl_le7 (by omega)).2.1, ?_,
                fun _ hs_p => by
                  dsimp only [L']
                  have hl := hlen_s (by omega) (hcap_eq ▸ hs_p)
                  simp only [Bool.false_eq_true, ↓reduceIte, add_zero, hcap_eq] at hl ⊢
                  omega⟩
              unfold activeSrcIo; rw [ite_eq_left (by decide : 2 < 3), hibL_t, hqL_t]
              exact hsl_t
            sl_67 := fun h67 => by rw [hph_t] at h67; omega
            sl_8 := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
            sl_ge9 := fun h9 => by rw [hph_t] at h9; omega }

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
