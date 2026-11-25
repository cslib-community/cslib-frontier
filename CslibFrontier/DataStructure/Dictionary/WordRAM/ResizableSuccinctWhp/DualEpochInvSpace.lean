/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvBase

/-!
# Dual-Epoch `EpochCapSafe` and `1 · OPT` Frontier Space Bounds (`DualEpochInvSpace`)

Proves the capacity-safety and `1 · OPT` word-footprint extraction lemmas from `DualCoreInv`
(`dualCoreInv_cap_safe`, `dualStateInv_frontier_le_succinctWords`, `dualCoreInv_ib_fits`) across all
12 phases (`0..11`) of the deamortized dual-epoch resizable succinct worst-case WHP dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main results

* `dualCoreInv_cap_safe`, `dualStateInv_frontier_le_succinctWords`, `dualCoreInv_ib_fits`

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

/-! ## Section 1: `EpochCapSafe`, `dualPaddedWords`, and `pairStreamWords` Bounds -/

/-- `DualPostUpdateSafe` implies `EpochCapSafe` at threshold `whpThreshold c`. -/
theorem dualPostUpdateSafe_to_epochCapSafe {c U nSrc nLive : ℕ}
    (h : DualPostUpdateSafe c U nSrc nLive) :
    EpochCapSafe (whpThreshold c) U nSrc nLive := by
  have hth_big := whpThreshold_ge_pow20 c
  by_cases h0 : nSrc = 0
  · subst h0
    simp only [DualPostUpdateSafe, EpochCapSafe, ↓reduceIte] at h ⊢
    exact ⟨by omega, h.1⟩
  · simp only [DualPostUpdateSafe, EpochCapSafe, h0, ↓reduceIte] at h ⊢
    obtain ⟨hth, hNU, hnU, hlo, hhi⟩ := h
    refine ⟨hth, hNU, by omega, ?_⟩
    by_cases hlt : nSrc < U
    · have := hhi hlt; omega
    · omega

/-- Every `DualCoreInv` state (`isMid = false` or `isMid = true`) maintains `EpochCapSafe` for both
`nSrc` and `if ph = 0 then nSrc else nDst` at `nLive = (Dictionary.dom s_dict).card`. -/
theorem dualCoreInv_cap_safe {isMid : Bool} {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualCoreInv isMid c U V w base s_dict L s) :
    let ph := s.mem (base + hdrPhase)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := if ph = 0 then nSrc else s.mem (base + hdrNDst)
    let nLive := (Dictionary.dom s_dict).card
    EpochCapSafe (whpThreshold c) U nSrc nLive ∧
    EpochCapSafe (whpThreshold c) U nDst nLive := by
  dsimp only
  have hnU := h.live_le
  have hsched := h.sched
  by_cases hph0 : s.mem (base + hdrPhase) = 0
  · rw [ite_eq_left hph0] at hsched ⊢
    have hsafe0 := hsched.safe_fr
    have hs : EpochCapSafe (whpThreshold c) U (s.mem (base + hdrNSrc))
        (Dictionary.dom s_dict).card := by
      cases isMid
      · exact dualIdleSafe_to_epochCapSafe hsafe0.1
      · exact dualPostUpdateSafe_to_epochCapSafe hsafe0.1
    exact ⟨hs, hs⟩
  · rw [ite_eq_right hph0] at hsched ⊢
    have hel := hsched.budget.2.2
    set dMax := L.elapsed + (if isMid then 1 else 0)
    have hd_le : 16 * dMax ≤ max (whpThreshold c) (s.mem (base + hdrNSrc)) := by
      dsimp only [dMax]; cases isMid <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have har := active_rebuild_safe hsched.post_trig hsched.trig_cap
      hsched.drift_hi hsched.drift_lo hd_le hnU
    exact ⟨har.2.1, har.2.2.1⟩

/-- Every resting `DualStateInv` state satisfies `s.frontier ≤ base + succinctWords ... nLive`. -/
theorem dualStateInv_frontier_le_succinctWords {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s) :
    let nLive := (Dictionary.dom s_dict).card
    s.frontier ≤ base +
      Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w nLive := by
  dsimp only
  obtain ⟨hsrc_safe, hdst_safe⟩ := dualCoreInv_cap_safe h
  have hpad_le := dualPaddedWords_le_succinctWords (V := V) (w := w) hsrc_safe hdst_safe
  have hmSrc_eq := h.mSrc_eq
  have hsched := h.sched
  set nLive := (Dictionary.dom s_dict).card
  set ph := s.mem (base + hdrPhase)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set vB := valBits V
  have hqSrc_eq : (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc) + vB =
      epochItemBitsWhp c U V nSrc := by
    unfold epochItemBitsWhp
    by_cases h0 : nSrc = 0
    · rw [ite_eq_left h0, h0, ite_eq_left (whpThreshold_pos c)]
    · have hth : whpThreshold c ≤ nSrc := by
        simp only [EpochCapSafe, h0, ↓reduceIte] at hsrc_safe; exact hsrc_safe.1
      rw [ite_eq_right h0, ite_eq_right (Nat.not_lt.mpr hth)]
  have hpw_mono : ∀ b₁ b₂, b₁ ≤ b₂ → packedWords nLive b₁ w ≤ packedWords nLive b₂ w :=
    fun b₁ b₂ hle => by
      unfold packedWords
      have hm := Nat.mul_le_mul_left nLive hle
      have hd := Nat.div_le_div_right (c := w)
        (show nLive * b₁ + w - 1 ≤ nLive * b₂ + w - 1 by omega)
      omega
  by_cases hph0 : ph = 0
  · rw [ite_eq_left hph0] at hsched hpad_le
    have hib := hsched.ibLo_eq
    have hqL := hsched.qLo_eq
    have hfr_eq : s.frontier = s.mem (base + hdrItemLo) +
        pairStreamWords nLive (s.mem (base + hdrQLo)) vB w := hsched.safe_fr.2.2
    have hfr_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nSrc nLive := by
      rw [hfr_eq, hib, hmSrc_eq, hqL]
      unfold pairStreamWords dualPaddedWords rootHdrWhp
      rw [hqSrc_eq, Nat.max_self, Nat.max_self]
      omega
    exact hfr_pad.trans (Nat.add_le_add_left hpad_le base)
  · rw [ite_eq_right hph0] at hsched hpad_le hdst_safe
    have hibLo_eq := hsched.ibLo_eq
    have hqLo_eq := hsched.qLo_eq
    by_cases hph1 : ph = 1
    · have hfr_hi : s.frontier ≤ s.mem (base + hdrItemLo) +
          pairStreamWords nLive (s.mem (base + hdrQLo)) vB w := by
        simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using (hsched.ph1 hph1).2.2.2.2.2.2
      have hib : s.mem (base + hdrItemLo) = base + 192 + s.mem (base + hdrMSrc) := by
        rw [hibLo_eq, ite_eq_left (show s.mem (base + hdrPhase) < 10 by change ph < 10; omega)]
      have hqL : s.mem (base + hdrQLo) = (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc) := by
        rw [hqLo_eq, ite_eq_left (show s.mem (base + hdrPhase) < 10 by change ph < 10; omega)]
      have hpw_le := hpw_mono _ _ (le_max_left (epochItemBitsWhp c U V nSrc)
        (epochItemBitsWhp c U V nDst))
      have hfr_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive := by
        have h1 : s.frontier ≤ s.mem (base + hdrItemLo) +
            pairStreamWords nLive (s.mem (base + hdrQLo)) vB w := hfr_hi
        rw [hib, hmSrc_eq, hqL] at h1
        unfold pairStreamWords at h1
        unfold dualPaddedWords rootHdrWhp
        rw [hqSrc_eq] at h1
        have hm_le := le_max_left (epochMetaWordsWhp c w nSrc) (epochMetaWordsWhp c w nDst)
        omega
      exact hfr_pad.trans (Nat.add_le_add_left hpad_le base)
    · obtain ⟨hmDst_eq, hpad_eq, _, _, hibHi_eq, hqHi_eq⟩ :=
        hsched.ge2 (show 2 ≤ s.mem (base + hdrPhase) by change 2 ≤ ph; omega)
      change s.mem (base + hdrMDst) = epochMetaWordsWhp c w nDst at hmDst_eq
      change s.mem (base + hdrItemHi) =
        (if nDst = 0 then base + 196 + s.mem (base + hdrMSrc)
         else base + 192 + s.mem (base + hdrPad) + s.mem (base + hdrMDst) + 4) at hibHi_eq
      change s.mem (base + hdrQHi) =
        max (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc)
          (if nDst = 0 then keyBits U else quotBitsWhp U nDst) at hqHi_eq
      have hqDst_eq : (if nDst = 0 then keyBits U else quotBitsWhp U nDst) + vB =
          epochItemBitsWhp c U V nDst := by
        unfold epochItemBitsWhp
        by_cases hd0 : nDst = 0
        · rw [ite_eq_left hd0, hd0, ite_eq_left (whpThreshold_pos c)]
        · have hth : whpThreshold c ≤ nDst := by
            simp only [EpochCapSafe, hd0, ↓reduceIte] at hdst_safe; exact hdst_safe.1
          rw [ite_eq_right hd0, ite_eq_right (Nat.not_lt.mpr hth)]
      have hqHi_add : s.mem (base + hdrQHi) + vB =
          max (epochItemBitsWhp c U V nSrc) (epochItemBitsWhp c U V nDst) := by
        rw [hqHi_eq, ← Nat.add_max_add_right, hqSrc_eq, hqDst_eq]
      have hfr_hi : s.frontier ≤ s.mem (base + hdrItemHi) +
          pairStreamWords nLive (s.mem (base + hdrQHi)) vB w := by
        have hp_le := h.ph_le; change ph ≤ 11 at hp_le
        by_cases hp2 : ph = 2
        · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using (hsched.ph2 hp2).2.2
        · by_cases hp10 : ph ≤ 10
          · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
              (hsched.ph3_10 ⟨by change 3 ≤ ph; omega, hp10⟩).2
          · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
              (hsched.ph11 (show s.mem (base + hdrPhase) = 11 by change ph = 11; omega)).2
      have hibHi_le : s.mem (base + hdrItemHi) ≤
          base + 192 + max (epochMetaWordsWhp c w nSrc) (epochMetaWordsWhp c w nDst) +
            epochMetaWordsWhp c w nDst + 4 := by
        rw [hibHi_eq, hpad_eq, hmSrc_eq, hmDst_eq]
        split_ifs with hd0
        · have hm0 : epochMetaWordsWhp c w 0 = 0 := by
            unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
          rw [hd0, hm0]; omega
        · omega
      have hfr_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive := by
        unfold pairStreamWords at hfr_hi
        unfold dualPaddedWords rootHdrWhp
        rw [hqHi_add] at hfr_hi
        omega
      exact hfr_pad.trans (Nat.add_le_add_left hpad_le base)

theorem pairStreamWords_succ_le_add_two {n qb vb w : ℕ}
    (hw : 0 < w) (hb : qb + vb ≤ 2 * w) :
    pairStreamWords (n + 1) qb vb w ≤ pairStreamWords n qb vb w + 2 := by
  unfold pairStreamWords packedWords
  have h1 : (n + 1) * (qb + vb) + w - 1 ≤ (n * (qb + vb) + w - 1) + 2 * w := by
    rw [Nat.succ_mul]
    omega
  have hd : ((n + 1) * (qb + vb) + w - 1) / w ≤ (n * (qb + vb) + w - 1) / w + 2 := by
    calc ((n + 1) * (qb + vb) + w - 1) / w
        ≤ ((n * (qb + vb) + w - 1) + 2 * w) / w := Nat.div_le_div_right h1
      _ = (n * (qb + vb) + w - 1) / w + 2 := by
        rw [show (n * (qb + vb) + w - 1) + 2 * w = (n * (qb + vb) + w - 1) + w * 2 by omega,
          Nat.add_mul_div_left _ _ hw]
  omega

theorem pairStreamWords_mono_n {n₁ n₂ qb vb w : ℕ} (hle : n₁ ≤ n₂) :
    pairStreamWords n₁ qb vb w ≤ pairStreamWords n₂ qb vb w := by
  unfold pairStreamWords packedWords
  have hm := Nat.mul_le_mul_right (qb + vb) hle
  have hd := Nat.div_le_div_right (c := w)
    (show n₁ * (qb + vb) + w - 1 ≤ n₂ * (qb + vb) + w - 1 by omega)
  omega

theorem pairStreamWords_mono_q {n q₁ q₂ vb w : ℕ} (hle : q₁ ≤ q₂) :
    pairStreamWords n q₁ vb w ≤ pairStreamWords n q₂ vb w := by
  unfold pairStreamWords packedWords
  have hm := Nat.mul_le_mul_left n (show q₁ + vb ≤ q₂ + vb by omega)
  have hd := Nat.div_le_div_right (c := w)
    (show n * (q₁ + vb) + w - 1 ≤ n * (q₂ + vb) + w - 1 by omega)
  omega

theorem qBits_le_w_of_valid {U w N : ℕ} (hUw : U < 2 ^ w) (_hNU : N ≤ U) :
    (if N = 0 then keyBits U else quotBitsWhp U N) ≤ w := by
  have hkb : keyBits U ≤ w := Nat.clog_le_of_le_pow hUw.le
  split_ifs with h0
  · exact hkb
  · unfold quotBitsWhp
    exact (Nat.sub_le _ _).trans (Nat.clog_le_of_le_pow (by omega))

/-- From `DualCoreInv`, both `ibLo + pairStreamWords (nLive + 1) qLo vB w` and
`ibHi + pairStreamWords (nLive + 1) qHi vB w` lie strictly below `2 ^ w`, and `qLo, qHi, vB ≤ w`. -/
theorem dualCoreInv_ib_fits {isMid : Bool} {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualCoreInv isMid c U V w base s_dict L s) :
    let nLive := (Dictionary.dom s_dict).card
    s.mem (base + hdrValBits) = valBits V ∧
    valBits V ≤ w ∧
    s.mem (base + hdrQLo) ≤ w ∧
    s.mem (base + hdrQHi) ≤ w ∧
    s.mem (base + hdrItemLo) +
      pairStreamWords (nLive + 1) (s.mem (base + hdrQLo)) (valBits V) w ≤
      base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
        (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc)
         else s.mem (base + hdrNDst)) nLive ∧
    s.mem (base + hdrItemHi) +
      pairStreamWords (nLive + 1) (s.mem (base + hdrQHi)) (valBits V) w ≤
      base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
        (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc)
         else s.mem (base + hdrNDst)) nLive ∧
    Fits w (s.mem (base + hdrItemLo) +
      pairStreamWords (nLive + 1) (s.mem (base + hdrQLo)) (valBits V) w) ∧
    Fits w (s.mem (base + hdrItemHi) +
      pairStreamWords (nLive + 1) (s.mem (base + hdrQHi)) (valBits V) w) := by
  dsimp only
  obtain ⟨hsrc_safe, hdst_safe⟩ := dualCoreInv_cap_safe h
  have hw11 := h.hw11; have hUw := h.U_lt; have hVw := h.V_le; have hhdr := h.hdr
  have hmSrc_eq := h.mSrc_eq; have hnSrc_b := h.nSrc_bounds
  have hsched := h.sched; have hpad_fits := h.pad_fits
  have hw_pos : 0 < w := by omega
  have hvb_eq : s.mem (base + hdrValBits) = valBits V := hhdr.2.2.2.2.1
  have hvb_le : valBits V ≤ w := Nat.clog_le_of_le_pow hVw
  set nLive := (Dictionary.dom s_dict).card
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set ph := s.mem (base + hdrPhase)
  have hnSrc_U : nSrc ≤ U := by
    rcases hnSrc_b with h0 | ⟨_, hU⟩ <;> [omega; exact hU]
  have hqSrc_w : (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc) ≤ w :=
    qBits_le_w_of_valid hUw hnSrc_U
  have hqSrc_ib : (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc) + valBits V =
      epochItemBitsWhp c U V nSrc := by
    unfold epochItemBitsWhp
    by_cases h0 : nSrc = 0
    · rw [ite_eq_left h0, h0, ite_eq_left (whpThreshold_pos c)]
    · have hth : whpThreshold c ≤ nSrc := by
        simp only [EpochCapSafe, h0, ↓reduceIte] at hsrc_safe; exact hsrc_safe.1
      rw [ite_eq_right h0, ite_eq_right (Nat.not_lt.mpr hth)]
  have hpw_mono_b : ∀ b₁ b₂, b₁ ≤ b₂ → packedWords nLive b₁ w ≤ packedWords nLive b₂ w :=
    fun b₁ b₂ hle => by
      unfold packedWords
      have hm := Nat.mul_le_mul_left nLive hle
      have hd := Nat.div_le_div_right (c := w)
        (show nLive * b₁ + w - 1 ≤ nLive * b₂ + w - 1 by omega)
      omega
  suffices hmain :
      s.mem (base + hdrQLo) ≤ w ∧ s.mem (base + hdrQHi) ≤ w ∧
      s.mem (base + hdrItemLo) +
        pairStreamWords (nLive + 1) (s.mem (base + hdrQLo)) (valBits V) w ≤
        base + dualPaddedWords c U V w nSrc (if ph = 0 then nSrc else nDst) nLive ∧
      s.mem (base + hdrItemHi) +
        pairStreamWords (nLive + 1) (s.mem (base + hdrQHi)) (valBits V) w ≤
        base + dualPaddedWords c U V w nSrc (if ph = 0 then nSrc else nDst) nLive by
    exact ⟨hvb_eq, hvb_le, hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2,
      lt_of_le_of_lt hmain.2.2.1 hpad_fits, lt_of_le_of_lt hmain.2.2.2 hpad_fits⟩
  by_cases hph0 : ph = 0
  · rw [ite_eq_left hph0] at hsched ⊢
    have hibL := hsched.ibLo_eq; have hibH := hsched.ibHi_eq
    have hqL := hsched.qLo_eq; have hqH := hsched.qHi_eq
    have hpw_s := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
      (show (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc) + valBits V ≤ 2 * w by omega)
    have hbound : s.mem (base + hdrItemLo) +
        pairStreamWords (nLive + 1) (s.mem (base + hdrQLo)) (valBits V) w ≤
        base + dualPaddedWords c U V w nSrc nSrc nLive := by
      rw [hibL, hmSrc_eq, hqL]
      unfold pairStreamWords at hpw_s ⊢
      unfold dualPaddedWords rootHdrWhp
      rw [hqSrc_ib] at hpw_s
      rw [hqSrc_ib, Nat.max_self, Nat.max_self]
      omega
    exact ⟨hqL ▸ hqSrc_w, (hqH.trans hqL) ▸ hqSrc_w, hbound,
      by rw [hibH, hqH]; exact hbound⟩
  · rw [ite_eq_right hph0] at hsched hdst_safe ⊢
    have hnDst_b : nDst = 0 ∨ whpThreshold c ≤ nDst ∧ nDst ≤ U := hsched.nDst_bounds
    have hibLo_eq : s.mem (base + hdrItemLo) =
        (if ph < 10 then base + 192 + s.mem (base + hdrMSrc)
         else base + 192 + s.mem (base + hdrMDst)) := hsched.ibLo_eq
    have hqLo_eq : s.mem (base + hdrQLo) =
        (if ph < 10 then if nSrc = 0 then keyBits U else quotBitsWhp U nSrc
         else if nDst = 0 then keyBits U else quotBitsWhp U nDst) := hsched.qLo_eq
    have h1_i := hsched.ph1
    have hge2_i := hsched.ge2
    have hnDst_U : nDst ≤ U := by
      rcases hnDst_b with hd0 | ⟨_, hU⟩ <;> [omega; exact hU]
    have hqDst_w : (if nDst = 0 then keyBits U else quotBitsWhp U nDst) ≤ w :=
      qBits_le_w_of_valid hUw hnDst_U
    have hqDst_ib : (if nDst = 0 then keyBits U else quotBitsWhp U nDst) + valBits V =
        epochItemBitsWhp c U V nDst := by
      unfold epochItemBitsWhp
      by_cases hd0 : nDst = 0
      · rw [ite_eq_left hd0, hd0, ite_eq_left (whpThreshold_pos c)]
      · have hth : whpThreshold c ≤ nDst := by
          simp only [EpochCapSafe, hd0, ↓reduceIte] at hdst_safe; exact hdst_safe.1
        rw [ite_eq_right hd0, ite_eq_right (Nat.not_lt.mpr hth)]
    have hqLo_w : s.mem (base + hdrQLo) ≤ w := by
      rw [hqLo_eq]
      by_cases h10 : ph < 10
      · rw [ite_eq_left h10]; exact hqSrc_w
      · rw [ite_eq_right h10]; exact hqDst_w
    have hibLo_le : s.mem (base + hdrItemLo) ≤
        base + 192 + max (epochMetaWordsWhp c w nSrc) (epochMetaWordsWhp c w nDst) := by
      rw [hibLo_eq]
      by_cases h10 : ph < 10
      · rw [ite_eq_left h10, hmSrc_eq]
        have := le_max_left (epochMetaWordsWhp c w nSrc) (epochMetaWordsWhp c w nDst)
        omega
      · have hmD_e : s.mem (base + hdrMDst) = epochMetaWordsWhp c w nDst :=
          (hge2_i (show 2 ≤ s.mem (base + hdrPhase) by change 2 ≤ ph; omega)).1
        rw [ite_eq_right h10, hmD_e]
        have := le_max_right (epochMetaWordsWhp c w nSrc) (epochMetaWordsWhp c w nDst)
        omega
    have hqLo_ib_le : s.mem (base + hdrQLo) + valBits V ≤
        max (epochItemBitsWhp c U V nSrc) (epochItemBitsWhp c U V nDst) := by
      rw [hqLo_eq]
      by_cases h10 : ph < 10
      · rw [ite_eq_left h10, hqSrc_ib]; exact le_max_left _ _
      · rw [ite_eq_right h10, hqDst_ib]; exact le_max_right _ _
    have hpwLo_s := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
      (show s.mem (base + hdrQLo) + valBits V ≤ 2 * w by omega)
    have hlo_bound : s.mem (base + hdrItemLo) +
        pairStreamWords (nLive + 1) (s.mem (base + hdrQLo)) (valBits V) w ≤
        base + dualPaddedWords c U V w nSrc nDst nLive := by
      have hpm := hpw_mono_b _ _ hqLo_ib_le
      unfold pairStreamWords at hpwLo_s ⊢
      unfold dualPaddedWords rootHdrWhp
      omega
    by_cases hph1 : ph = 1
    · obtain ⟨_, _, _, hibH1, hqH1, _, _⟩ := h1_i hph1
      exact ⟨hqLo_w, hqH1 ▸ hqLo_w, hlo_bound, by rw [hibH1, hqH1]; exact hlo_bound⟩
    · obtain ⟨hmDst_eq, hpad_eq, _, _, hibHi_eq, hqHi_eq⟩ :=
        hge2_i (show 2 ≤ s.mem (base + hdrPhase) by change 2 ≤ ph; omega)
      change s.mem (base + hdrMDst) = epochMetaWordsWhp c w nDst at hmDst_eq
      change s.mem (base + hdrItemHi) =
        (if nDst = 0 then base + 196 + s.mem (base + hdrMSrc)
         else base + 192 + s.mem (base + hdrPad) + s.mem (base + hdrMDst) + 4) at hibHi_eq
      change s.mem (base + hdrQHi) =
        max (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc)
          (if nDst = 0 then keyBits U else quotBitsWhp U nDst) at hqHi_eq
      have hqHi_w : s.mem (base + hdrQHi) ≤ w := by
        rw [hqHi_eq]; exact max_le hqSrc_w hqDst_w
      have hqHi_ib : s.mem (base + hdrQHi) + valBits V =
          max (epochItemBitsWhp c U V nSrc) (epochItemBitsWhp c U V nDst) := by
        rw [hqHi_eq, ← Nat.add_max_add_right, hqSrc_ib, hqDst_ib]
      have hibHi_le : s.mem (base + hdrItemHi) ≤
          base + 192 + max (epochMetaWordsWhp c w nSrc) (epochMetaWordsWhp c w nDst) +
            epochMetaWordsWhp c w nDst + 4 := by
        rw [hibHi_eq, hpad_eq, hmSrc_eq, hmDst_eq]
        split_ifs with hd0
        · have hm0 : epochMetaWordsWhp c w 0 = 0 := by
            unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
          rw [hd0, hm0]; omega
        · omega
      have hpwHi_s := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
        (show s.mem (base + hdrQHi) + valBits V ≤ 2 * w by omega)
      have hhi_bound : s.mem (base + hdrItemHi) +
          pairStreamWords (nLive + 1) (s.mem (base + hdrQHi)) (valBits V) w ≤
          base + dualPaddedWords c U V w nSrc nDst nLive := by
        unfold pairStreamWords at hpwHi_s ⊢
        unfold dualPaddedWords rootHdrWhp
        rw [hqHi_ib] at hpwHi_s ⊢
        omega
      exact ⟨hqLo_w, hqHi_w, hlo_bound, hhi_bound⟩

/-! ## Section 2: `SlotIoLayout.withNCap` Lifting & `clampSplitIfSlideProg` Transport -/

theorem activeSrcIo_withNCap (c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nc nc' : ℕ) :
    (activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nc).withNCap nc' =
      activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nc' := by
  unfold activeSrcIo; dsimp only
  split_ifs <;> rfl

theorem activeDstIo_withNCap (c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nc nc' uD : ℕ) :
    (activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nc uD).withNCap nc' =
      activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nc' uD := by
  unfold activeDstIo; dsimp only
  split_ifs <;> rfl

theorem SlotIoLayout.Valid.with_nCap {io : SlotIoLayout} {w fr nc' : ℕ}
    (hv : io.Valid w fr) (hnc_w : nc' < 2 ^ w)
    (hfr_dir : io.usePaged = 0 → io.sideBit = 0 →
      io.pgL.itemBase + pairStreamWords nc' io.pgL.qBits io.pgL.vBits io.pgL.w ≤ fr)
    (hfr_spl : io.usePaged = 0 → io.sideBit ≠ 0 →
      io.pgL.itemBase + pairStreamWords nc' io.pgL.offTail io.pgL.vBits io.pgL.w ≤ fr)
    (hpg : io.usePaged ≠ 0 →
      nc' ≤ (io.pgL.maxPages - 2) * io.pgL.pgB ∧
      io.pgL.itemBase + pairStreamWords nc' io.pgL.qBits io.pgL.vBits io.pgL.w ≤ fr) :
    (io.withNCap nc').Valid w fr := by
  rcases io with ⟨up, sb, pgL⟩
  dsimp only [SlotIoLayout.withNCap] at *
  unfold SlotIoLayout.Valid at hv ⊢
  dsimp only at hv ⊢
  by_cases hup : up = 0
  · rw [ite_eq_left hup] at hv ⊢
    refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hnc_w, ?_⟩
    have hs := hv.2.2.2.2.2
    by_cases hsb : sb = 0
    · rw [ite_eq_left hsb]; exact hfr_dir hup hsb
    · rw [ite_eq_right hsb] at hs ⊢
      exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hfr_spl hup hsb⟩
  · rw [ite_eq_right hup] at hv ⊢
    unfold PageArenaLayout.Valid at hv ⊢
    dsimp only
    exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2.1,
      hv.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.1, (hpg hup).1, hnc_w,
      hv.2.2.2.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hv.2.2.2.2.2.2.2.2.2.2.2.2.2.1, (hpg hup).2⟩

private theorem not_ownsAddr_withNCap {io : SlotIoLayout} {nc' addr : ℕ}
    (hlt_ib : addr < io.pgL.itemBase)
    (hlt_od : io.usePaged = 0 → io.sideBit ≠ 0 → addr < io.pgL.offDir)
    (hnot : ¬io.OwnsAddr addr) :
    ¬(io.withNCap nc').OwnsAddr addr := by
  rcases io with ⟨up, sb, pgL⟩
  dsimp only [SlotIoLayout.withNCap] at *
  unfold SlotIoLayout.OwnsAddr at hnot ⊢
  dsimp only at hnot ⊢
  by_cases hup : up = 0
  · rw [ite_eq_left hup] at hnot ⊢
    by_cases hsb : sb = 0
    · rw [ite_eq_left hsb]
      unfold PageArenaLayout.OwnsItemAddr; dsimp only; omega
    · rw [ite_eq_right hsb] at hnot ⊢
      have hod := hlt_od hup hsb
      rintro (hme | ⟨h1, _⟩ | ⟨h1, _⟩)
      · exact hnot (Or.inl hme)
      · omega
      · omega
  · rw [ite_eq_right hup] at hnot ⊢
    unfold PageArenaLayout.OwnsAddr PageArenaLayout.OwnsItemAddr at hnot ⊢
    dsimp only at hnot ⊢
    rintro (hm | ⟨h1, _⟩)
    · exact hnot (Or.inl hm)
    · omega

/-- Wrapper around `EpochSlotInv.update_nCap` deriving `hdisj_p'` and `hdisj_m'` automatically
whenever `[pBase, pBase + 64)` and `slotOwnsNonPageMeta` lie below `io.pgL.itemBase` (and
`io.pgL.offDir` in `SplitPair` mode). -/
theorem EpochSlotInv.lift_nCap {c U V w fr pBase metaBase slack nc' : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem)
    (hnc_w : nc' < 2 ^ w)
    (hfr_dir : io.usePaged = 0 → io.sideBit = 0 →
      io.pgL.itemBase + pairStreamWords nc' io.pgL.qBits io.pgL.vBits io.pgL.w ≤ fr)
    (hfr_spl : io.usePaged = 0 → io.sideBit ≠ 0 →
      io.pgL.itemBase + pairStreamWords nc' io.pgL.offTail io.pgL.vBits io.pgL.w ≤ fr)
    (hpg_fr : io.usePaged ≠ 0 →
      nc' ≤ (io.pgL.maxPages - 2) * io.pgL.pgB ∧
      io.pgL.itemBase + pairStreamWords nc' io.pgL.qBits io.pgL.vBits io.pgL.w ≤ fr)
    (hp_ib : pBase + 64 ≤ io.pgL.itemBase ∧
      (io.usePaged = 0 → io.sideBit ≠ 0 → pBase + 64 ≤ io.pgL.offDir))
    (hm_ib : metaBase + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ io.pgL.itemBase ∧
      (io.usePaged = 0 → io.sideBit ≠ 0 →
        metaBase + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ io.pgL.offDir))
    (hdisj_pm : pBase + 64 ≤ metaBase ∨
      metaBase + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ pBase)
    (hnc_ge : mem (metaBase + 1) ≤ nc')
    (hnc_pg : io.usePaged ≠ 0 → (extractPagePair io.pgL mem).totalItems ≤ nc') :
    EpochSlotInv c U V w fr pBase metaBase (io.withNCap nc') slack draining sl
      (Function.update mem (pBase + 60) nc') := by
  have hv_io' := h.io_valid.with_nCap hnc_w hfr_dir hfr_spl hpg_fr
  have hraw := h; unfold EpochSlotInv at hraw
  have hdisj_p₀ : ∀ a, pBase ≤ a → a < pBase + 64 → ¬io.OwnsAddr a := by
    by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at hraw
      exact fun a h1 h2 hia => hraw.2.2.2.2.1 a h1 h2 (Or.inr (Or.inr hia))
    · rw [ite_eq_right h0] at hraw; exact hraw.1.disj_pBase_io
  have hdisj_m₀ : ∀ a, slotOwnsNonPageMeta c w metaBase sl.nCap a → ¬io.OwnsAddr a := by
    intro a ha; unfold slotOwnsNonPageMeta at ha
    by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at hraw ha
      rcases ha with ⟨h1, h2⟩ | ⟨hne, _⟩
      · exact hraw.2.2.1.disjoint_hdr a (by dsimp only; omega)
      · exact absurd h0 hne
    · rw [ite_eq_right h0] at hraw ha
      exact hraw.1.disj_fast_io a (ha.imp id And.right)
  have hm_lt : ∀ a, slotOwnsNonPageMeta c w metaBase sl.nCap a →
      a < metaBase + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) := by
    intro a ha; unfold slotOwnsNonPageMeta at ha
    by_cases h0 : sl.nCap = 0
    · simp only [h0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false] at ha ⊢; omega
    · simp only [h0, ↓reduceIte, ne_eq, not_false_eq_true, true_and] at ha ⊢
      have h32 : 32 ≤ offPageDir c w sl.nCap := by
        unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
          offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
          offBktHash
        omega
      rcases ha with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
  exact h.update_nCap hv_io'
    (fun a h1 h2 => not_ownsAddr_withNCap (by omega)
      (fun hup hsb => by have := hp_ib.2 hup hsb; omega) (hdisj_p₀ a h1 h2))
    (fun a ha => not_ownsAddr_withNCap (lt_of_lt_of_le (hm_lt a ha) hm_ib.1)
      (fun hup hsb => lt_of_lt_of_le (hm_lt a ha) (hm_ib.2 hup hsb)) (hdisj_m₀ a ha))
    hdisj_pm hnc_ge hnc_pg

/-- Clamping `base + hdrSplit` from `sp` down to `nLive'` when `nLive' < sp` (`ph ∈ {3, 10}`)
preserves `EpochSlotInv` on `splitSlotIo` because every live slot `p < nLive'` lies strictly below
both `sp` and `nLive'`. -/
theorem EpochSlotInv.clamp_split_cursor
    {c U V w fr pBase metaBase base ibLo qLo ibHi qHi nLive' : ℕ}
    {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase
      (splitSlotIo w (valBits V) base ibLo qLo ibHi qHi nLive') 0 draining sl mem)
    (hp_gt : base + 48 ≤ pBase)
    (hm_gt : base + 48 ≤ metaBase)
    (hib_gt : base + 48 ≤ ibLo)
    (hns_eq : mem (metaBase + 1) = nLive')
    (hlt_sp : nLive' < mem (base + hdrSplit)) :
    let io := splitSlotIo w (valBits V) base ibLo qLo ibHi qHi nLive'
    let mem' := Function.update mem (base + hdrSplit) nLive'
    EpochSlotInv c U V w fr pBase metaBase io 0 draining sl mem' ∧
    SplitHiQuotBounded io nLive' mem' := by
  dsimp only
  set io := splitSlotIo w (valBits V) base ibLo qLo ibHi qHi nLive'
  set mem' := Function.update mem (base + hdrSplit) nLive'
  have hv_io := h.io_valid
  have hio_old := h.io_stateInv
  have hraw := h; unfold EpochSlotInv at hraw
  have hne_sp : ∀ a, base + 48 ≤ a → mem' a = mem a := fun a ha =>
    Function.update_of_ne (by unfold hdrSplit; omega) _ _
  have hio' : io.StateInv (mem (metaBase + 1)) 0 mem' := by
    unfold SlotIoLayout.StateInv at hio_old ⊢
    dsimp only [io, splitSlotIo, ↓reduceIte] at hio_old ⊢
    exact hio_old
  have hpair : ∀ p < mem (metaBase + 1), slotIoPairAt io mem' p = slotIoPairAt io mem p := by
    intro p hp
    rw [hns_eq] at hp
    have hp_sp : p < mem (base + hdrSplit) := lt_trans hp hlt_sp
    have hm_sp' : mem' (base + hdrSplit) = nLive' := Function.update_self ..
    unfold slotIoPairAt splitPairRead SlotIoLayout.splitCfg
    simp only [io, splitSlotIo, ↓reduceIte, Nat.one_ne_zero]
    rw [hm_sp', ite_eq_left hp, ite_eq_left hp_sp]
    have hq_eq : pairQuotAt ibLo qLo (valBits V) w mem' p =
        pairQuotAt ibLo qLo (valBits V) w mem p := by
      unfold pairQuotAt readBitSlice
      rw [hne_sp _ (by omega), hne_sp _ (by omega)]
    have hv_eq : pairValAt ibLo qLo (valBits V) w mem' p =
        pairValAt ibLo qLo (valBits V) w mem p := by
      unfold pairValAt readBitSlice
      rw [hne_sp _ (by omega), hne_sp _ (by omega)]
    rw [hq_eq, hv_eq]
  have hsl' : EpochSlotInv c U V w fr pBase metaBase io 0 draining sl mem' := by
    refine h.transfer_io hv_io rfl ⟨fun h0 => ?_, fun h0 => ?_⟩ rfl
      ⟨fun h0 => ?_, fun h0 => ?_⟩ (fun a h1 h2 => ?_) (fun a ha => ?_)
      (fun a ha => ?_) hio' hpair
    · rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.qBits_eq
    · rw [ite_eq_right h0] at hraw; exact hraw.1.qBits_le
    · rw [ite_eq_left h0] at hraw
      exact hraw.2.2.2.1.congr fun a h1 _ => hne_sp a (by omega)
    · rw [ite_eq_right h0] at hraw
      exact hraw.2.1.1.congr fun a h1 _ => hne_sp a (by dsimp only at h1; omega)
    · by_cases h0 : sl.nCap = 0
      · rw [ite_eq_left h0] at hraw
        exact fun hia => hraw.2.2.2.2.1 a h1 h2 (Or.inr (Or.inr hia))
      · rw [ite_eq_right h0] at hraw; exact hraw.1.disj_pBase_io a h1 h2
    · unfold slotOwnsNonPageMeta at ha
      by_cases h0 : sl.nCap = 0
      · rw [ite_eq_left h0] at hraw ha
        rcases ha with ⟨h1, h2⟩ | ⟨hne, _⟩
        · exact hraw.2.2.1.disjoint_hdr a (by dsimp only; omega)
        · exact absurd h0 hne
      · rw [ite_eq_right h0] at hraw ha
        exact hraw.1.disj_fast_io a (ha.imp id And.right)
    · unfold slotOwnsNonPageMeta at ha
      rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> exact hne_sp a (by omega)
  refine ⟨hsl', fun idx hge hlt => ?_⟩
  dsimp only [io, splitSlotIo, mem'] at hge
  rw [Function.update_self] at hge
  omega

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
