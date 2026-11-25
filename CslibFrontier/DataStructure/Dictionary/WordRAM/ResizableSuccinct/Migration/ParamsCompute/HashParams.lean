/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.Primitives
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.HashCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Runtime 19-Word `HashParams` Writer (`writeHashParamsSubProg`)

Populates the 19-word `mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3` header
block at `[dstMetaBase + 8, dstMetaBase + 27)` and returns `epochHashSpace U w N`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
open Cslib.Probability

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

private def writeHashParamsLoProg : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((hpBase, w0), (minW0, c)), (l0, p)) => do
    let botW := l0 * 6
    let seedW := 1 + botW
    let hSpace := seedW + (1 <<< (c + c - p))
    let m := w0 - 1
    let h := m >>> 1
    writeBlock4Prog (hpBase, ((hSpace, seedW), (botW, (1 <<< m) - 1)))
    writeBlock4Prog (hpBase + 4,
      ((h, (1 <<< h) - 1), ((1 <<< (m - h)) - 1, (1 <<< (m - (h + h))) - 1)))
    writeBlock4Prog (hpBase + 8, ((w0 - minW0, c), ((1 <<< c) - 1, c + c)))
    pure hSpace

private def WriteHashParamsLoPre (w : ℕ) :
    ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((hpBase, w0), (minW0, c)), (l0, p)), s =>
    ∃ U N dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      hpBase = dstMetaBase + 8 ∧ w0 = epochQBits U N ∧
      minW0 = min (epochQBits U N) (3 * epochHashB N) ∧
      c = reducedChunkBits
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) ∧
      l0 = reducedHalfLimbs
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) ∧
      p = reducedPackShift
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) w ∧
      dstMetaBase + 27 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem fits_epoch_mkHashParams {w U N dstMetaBase : ℕ}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    ∀ i : Fin 19,
      Fits w (mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i) := by
  obtain ⟨_, hw0_le, hb'_le, _, hc_lt, _, _, _, _, _, _⟩ :=
    computeHashCore_arith hw hN hNU hU hfit_dst
  have hfit_hash := fits_hash_of_fits_offCompItems hfit_dst
  have hfit_scr : Fits w (dstMetaBase + offScratch + scratchWords) :=
    (fits_add_of_fits_offCompItems hfit_dst le_rfl).of_le (by unfold offScratch scratchWords; omega)
  exact fits_mkHashParams (k := 3) (qBits_pos U N) hw0_le hb'_le hc_lt hfit_hash hfit_scr

private theorem writeHashParamsLoProg_spec {w U N dstMetaBase : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (h27 : dstMetaBase + 27 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    let d := (((dstMetaBase + 8, epochQBits U N),
      (min (epochQBits U N) (3 * epochHashB N), reducedChunkBits t)),
      (reducedHalfLimbs t, reducedPackShift t w))
    let prog := writeHashParamsLoProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteHashParamsLoPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = epochHashSpace U w N ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 12),
      s'.mem (dstMetaBase + 8 + j) =
        mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 ⟨j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 8 ≤ a ∧ a < dstMetaBase + 20) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 12 := by
  intro t d prog s'
  have hfit27 : Fits w (dstMetaBase + 27) := fits_add_of_fits_offCompItems hfit_dst (by decide)
  have hhp := fits_epoch_mkHashParams hw hN hNU hU hfit_dst
  set hp := mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3
  have heq_sp : (1 + reducedHalfLimbs t * 6) +
      (1 <<< (reducedChunkBits t + reducedChunkBits t - reducedPackShift t w)) =
      epochHashSpace U w N := by
    dsimp only [epochHashSpace, ReducedKWise.space, ReducedKWise.seedWords,
      ReducedKWise.tableWords, reducedTableWords, reducedLimbCount]
    rw [Nat.shiftLeft_eq, one_mul, ← two_mul]; ring
  have heq0 : epochHashSpace U w N = hp 0 := by
    change epochHashSpace U w N = hpSpace hp; rw [hpSpace_mk]
  have heq1 : 1 + reducedHalfLimbs t * 6 = hp 1 := by
    change _ = hpSeedWords hp
    rw [hpSeedWords_mk]; dsimp only [ReducedKWise.seedWords, reducedLimbCount]; ring
  have heq2 : reducedHalfLimbs t * 6 = hp 2 := by
    change _ = hpBotWords hp; rw [hpBotWords_mk]; dsimp only [reducedLimbCount]; ring
  have heq3 : (1 <<< (epochQBits U N - 1)) - 1 = hp 3 := by
    change _ = hpMaskM hp; rw [hpMaskM_mk, Nat.shiftLeft_eq, one_mul]
  have heq4 : (epochQBits U N - 1) >>> 1 = hp 4 := by
    change _ = hpHalfM hp; rw [hpHalfM_mk, Nat.shiftRight_eq_div_pow, pow_one]
  have heq5 : (1 <<< ((epochQBits U N - 1) >>> 1)) - 1 = hp 5 := by
    change _ = hpMaskH hp
    rw [hpMaskH_mk, Nat.shiftRight_eq_div_pow, pow_one, Nat.shiftLeft_eq, one_mul]
  have heq6 : (1 <<< ((epochQBits U N - 1) - ((epochQBits U N - 1) >>> 1))) - 1 = hp 6 := by
    change _ = hpMaskMH hp
    rw [hpMaskMH_mk, Nat.shiftRight_eq_div_pow, pow_one, Nat.shiftLeft_eq, one_mul]
  have heq7 : (1 <<< ((epochQBits U N - 1) -
      (((epochQBits U N - 1) >>> 1) + ((epochQBits U N - 1) >>> 1)))) - 1 = hp 7 := by
    change _ = hpMaskM2H hp
    rw [hpMaskM2H_mk, Nat.shiftRight_eq_div_pow, pow_one, Nat.shiftLeft_eq, one_mul, two_mul]
  have heq8 : epochQBits U N - min (epochQBits U N) (3 * epochHashB N) = hp 8 := by
    change _ = hpRemShift hp; rw [hpRemShift_mk]
  have heq9 : reducedChunkBits t = hp 9 := by
    change _ = hpC hp; rw [hpC_mk]
  have heq10 : (1 <<< reducedChunkBits t) - 1 = hp 10 := by
    change _ = hpMaskC hp; rw [hpMaskC_mk, Nat.shiftLeft_eq, one_mul]
  have heq11 : reducedChunkBits t + reducedChunkBits t = hp 11 := by
    change _ = hpTwoC hp; rw [hpTwoC_mk]; ring
  set p01 := writeBlock4Prog (dstMetaBase + 8, ((hp 0, hp 1), (hp 2, hp 3))) >>= fun _ =>
    writeBlock4Prog (dstMetaBase + 8 + 4, ((hp 4, hp 5), (hp 6, hp 7)))
  set s2 := (Memory.spec 0).clientState s p01
  obtain ⟨hv01, hfr01, hm01, hframe01, hc01⟩ :=
    writeTwoBlock4Fin_spec (dstMetaBase + 8) hp 0 (by decide) (s := s)
      (by omega) (hfit27.of_le (by omega)) hhp
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p01) at hv01
  change s2.frontier = s.frontier at hfr01
  change ∀ (j : ℕ) (hj : j < 8), s2.mem (dstMetaBase + 8 + j) = hp ⟨0 + j, by omega⟩ at hm01
  change ∀ a, ¬(dstMetaBase + 8 ≤ a ∧ a < dstMetaBase + 8 + 8) → s2.mem a = s.mem a at hframe01
  change memoryCost p01 s = 8 at hc01
  obtain ⟨_, hv2, hfr2, hm2, hframe2, hc2⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 8 + 8) (hp 8) (hp 9) (hp 10) (hp 11) (s := s2)
      (by omega) (hfit27.of_le (by omega)) (hhp 8) (hhp 9) (hhp 10) (hhp 11)
  have hb0_eq : writeBlock4Prog (dstMetaBase + 8,
      (((1 + reducedHalfLimbs t * 6) +
        (1 <<< (reducedChunkBits t + reducedChunkBits t - reducedPackShift t w)),
        1 + reducedHalfLimbs t * 6),
       (reducedHalfLimbs t * 6, (1 <<< (epochQBits U N - 1)) - 1))) =
      writeBlock4Prog (dstMetaBase + 8, ((hp 0, hp 1), (hp 2, hp 3))) := by
    rw [heq_sp, heq0, heq1, heq2, heq3]
  have hb1_eq : writeBlock4Prog (dstMetaBase + 8 + 4,
      (((epochQBits U N - 1) >>> 1, (1 <<< ((epochQBits U N - 1) >>> 1)) - 1),
       ((1 <<< ((epochQBits U N - 1) - ((epochQBits U N - 1) >>> 1))) - 1,
        (1 <<< ((epochQBits U N - 1) -
          (((epochQBits U N - 1) >>> 1) + ((epochQBits U N - 1) >>> 1)))) - 1))) =
      writeBlock4Prog (dstMetaBase + 8 + 4, ((hp 4, hp 5), (hp 6, hp 7))) := by
    rw [heq7, heq6, heq5, heq4]
  have hb2_eq : writeBlock4Prog (dstMetaBase + 8 + 8,
      ((epochQBits U N - min (epochQBits U N) (3 * epochHashB N), reducedChunkBits t),
       ((1 <<< reducedChunkBits t) - 1, reducedChunkBits t + reducedChunkBits t))) =
      writeBlock4Prog (dstMetaBase + 8 + 8, ((hp 8, hp 9), (hp 10, hp 11))) := by
    rw [heq11, heq10, heq8, heq9]
  have hprog_eq : prog =
      p01 >>= fun _ =>
        writeBlock4Prog (dstMetaBase + 8 + 8, ((hp 8, hp 9), (hp 10, hp 11))) >>= fun _ =>
          pure (epochHashSpace U w N) := by
    dsimp only [prog, d, writeHashParamsLoProg, p01]
    rw [hb0_eq, hb1_eq, hb2_eq, heq_sp, bind_assoc]
  set s3 := (Memory.spec 0).clientState s2
    (writeBlock4Prog (dstMetaBase + 8 + 8, ((hp 8, hp 9), (hp 10, hp 11))))
  have hs'_eq : s' = s3 := by
    dsimp only [s']
    rw [hprog_eq, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
  refine ⟨⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprog_eq, validHistory_bind']; refine ⟨hv01, ?_⟩
    rw [validHistory_bind']; exact ⟨hv2, trivial⟩
  · rw [hprog_eq, prog_clientResult_bind, prog_clientResult_bind, prog_clientResult_pure]
  · rw [hs'_eq, hfr2, hfr01]
  · intro j hj
    rw [hs'_eq]
    by_cases hj8 : j < 8
    · rw [hframe2 _ (by omega)]
      exact (hm01 j hj8).trans (congrArg hp (Fin.ext (Nat.zero_add j)))
    · obtain ⟨m20, m21, m22, m23⟩ := hm2
      rcases (show j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 by omega) with rfl | rfl | rfl | rfl
      · exact m20
      · rw [show dstMetaBase + 8 + 9 = dstMetaBase + 8 + 8 + 1 by omega]; exact m21
      · rw [show dstMetaBase + 8 + 10 = dstMetaBase + 8 + 8 + 2 by omega]; exact m22
      · rw [show dstMetaBase + 8 + 11 = dstMetaBase + 8 + 8 + 3 by omega]; exact m23
  · intro a ha
    rw [hs'_eq, hframe2 a (by omega), hframe01 a (by omega)]
  · rw [hprog_eq, Realization.memoryCost_bind', hc01, Realization.memoryCost_bind',
      memoryCost_pure]
    change 8 + (memoryCost (writeBlock4Prog (dstMetaBase + 8 + 8, ((hp 8, hp 9), (hp 10, hp 11))))
      s2 + 0) = 12
    rw [hc2]

private theorem realizesBounded_writeHashParamsLo :
    RealizesBounded .exact writeHashParamsLoProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      WriteHashParamsLoPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨⟨⟨hpBase, w0⟩, ⟨minW0, c⟩⟩, ⟨l0, p⟩⟩
    obtain ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩ := h
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    obtain ⟨_, hw0_le, _, _, hc_lt, _, _, _, _, _, _⟩ :=
      computeHashCore_arith hw hN hNU hU hfit_dst
    have hfit_hash := fits_hash_of_fits_offCompItems hfit_dst
    have hfit27 : Fits w (dstMetaBase + 27) := fits_add_of_fits_offCompItems hfit_dst (by decide))
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hfit27.of_le (by omega)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
  all_goals (
    set t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    change 2 * reducedChunkBits t < w at hc_lt
    have hpow2c : Fits w (2 ^ (2 * reducedChunkBits t)) := Nat.pow_lt_pow_right one_lt_two hc_lt
    have hpowm : Fits w (2 ^ (epochQBits U N - 1)) :=
      Nat.pow_lt_pow_right one_lt_two (by have := qBits_pos U N; omega)
    have hl0_le : reducedHalfLimbs t ≤ 27 := reducedHalfLimbs_le t
    have hspace_fit : Fits w (epochHashSpace U w N) := hfit_hash.of_le (by omega)
    have hp_le : reducedPackShift t w ≤ reducedChunkBits t + reducedChunkBits t := by
      dsimp only [reducedPackShift]
      have := Nat.min_le_left (2 * reducedChunkBits t) (Nat.log 2 (w / (2 * reducedChunkBits t)))
      omega
    have h2c_eq : reducedChunkBits t + reducedChunkBits t = 2 * reducedChunkBits t := by ring
    have h6l_eq : reducedHalfLimbs t * 6 = 3 * reducedLimbCount t := by
      dsimp only [reducedLimbCount]; ring
    try rw [Nat.shiftLeft_eq, one_mul]
    try rw [Nat.shiftRight_eq_div_pow, pow_one]
    first
    | exact hp_le
    | exact qBits_pos U N
    | exact Nat.min_le_left _ _
    | exact Nat.div_le_self _ _
    | exact (by omega :
        (epochQBits U N - 1) / 2 + (epochQBits U N - 1) / 2 ≤ epochQBits U N - 1)
    | exact hw_fit.of_le (by omega)
    | exact h225.of_le (by omega)
    | exact hpow2c.of_le (Nat.pow_le_pow_right two_pos (by omega))
    | exact hpowm.of_le (Nat.pow_le_pow_right two_pos (by omega))
    | (rw [h2c_eq]
       exact hspace_fit.of_le (by
         change 1 + reducedHalfLimbs t * 6 +
           2 ^ (2 * reducedChunkBits t - reducedPackShift t w) ≤
           (1 + 3 * (2 * reducedHalfLimbs t)) +
           2 ^ (2 * reducedChunkBits t - reducedPackShift t w)
         omega))
    | (refine ⟨?_, hfit27.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

private def writeHashParamsHiProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((hpBase, c), (l0, (p, logN))) => do
    let pow2C := 1 <<< (c + c)
    writeBlock4Prog (hpBase + 12, ((pow2C, pow2C - 1), (p, (1 <<< p) - 1)))
    writeBlock3Prog (hpBase + 16, (l0, (3, logN)))

private def WriteHashParamsHiPre (w : ℕ) : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((hpBase, c), (l0, (p, logN))), s =>
    ∃ U N dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      hpBase = dstMetaBase + 8 ∧
      c = reducedChunkBits
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) ∧
      l0 = reducedHalfLimbs
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) ∧
      p = reducedPackShift
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) w ∧
      logN = Nat.log 2 N ∧
      dstMetaBase + 27 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeHashParamsHiProg_spec {w U N dstMetaBase : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (h27 : dstMetaBase + 27 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    let d := ((dstMetaBase + 8, reducedChunkBits t),
      (reducedHalfLimbs t, (reducedPackShift t w, Nat.log 2 N)))
    let prog := writeHashParamsHiProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteHashParamsHiPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 7),
      s'.mem (dstMetaBase + 20 + j) =
        mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3
          ⟨12 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 20 ≤ a ∧ a < dstMetaBase + 27) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 7 := by
  intro t d prog s'
  have hfit27 : Fits w (dstMetaBase + 27) := fits_add_of_fits_offCompItems hfit_dst (by decide)
  have hhp := fits_epoch_mkHashParams hw hN hNU hU hfit_dst
  set hp := mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3
  have heq12 : 1 <<< (reducedChunkBits t + reducedChunkBits t) = hp 12 := by
    change _ = hpPow2C hp; rw [hpPow2C_mk, Nat.shiftLeft_eq, one_mul, two_mul]
  have heq13 : (1 <<< (reducedChunkBits t + reducedChunkBits t)) - 1 = hp 13 := by
    change _ = hpMask2C hp; rw [hpMask2C_mk, Nat.shiftLeft_eq, one_mul, two_mul]
  have heq14 : reducedPackShift t w = hp 14 := by
    change _ = hpP hp; rw [hpP_mk]
  have heq15 : (1 <<< reducedPackShift t w) - 1 = hp 15 := by
    change _ = hpMaskP hp; rw [hpMaskP_mk, Nat.shiftLeft_eq, one_mul]
  have heq16 : reducedHalfLimbs t = hp 16 := by
    change _ = hpL0 hp; rw [hpL0_mk]
  have heq17 : 3 = hp 17 := by
    change _ = hpK hp; rw [hpK_mk]
  have heq18 : Nat.log 2 N = hp 18 := by
    change _ = hpB' hp; rw [hpB'_mk]; exact (totalMicroBits_eq_log N).symm
  obtain ⟨_, hv0, hfr0, hm0, hframe0, hc0⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 8 + 12) (hp 12) (hp 13) (hp 14) (hp 15) (s := s)
      (by omega) (hfit27.of_le (by omega)) (hhp 12) (hhp 13) (hhp 14) (hhp 15)
  set s1 := (Memory.spec 0).clientState s
    (writeBlock4Prog (dstMetaBase + 8 + 12, ((hp 12, hp 13), (hp 14, hp 15))))
  obtain ⟨_, hv1, hfr1, hm1, hframe1, hc1⟩ :=
    writeBlock3Prog_spec (dstMetaBase + 8 + 16) (hp 16) (hp 17) (hp 18) (s := s1)
      (by omega) (hfit27.of_le (by omega)) (hhp 16) (hhp 17) (hhp 18)
  set s2 := (Memory.spec 0).clientState s1
    (writeBlock3Prog (dstMetaBase + 8 + 16, (hp 16, (hp 17, hp 18))))
  have hb0_eq : writeBlock4Prog (dstMetaBase + 8 + 12,
      ((1 <<< (reducedChunkBits t + reducedChunkBits t),
        (1 <<< (reducedChunkBits t + reducedChunkBits t)) - 1),
       (reducedPackShift t w, (1 <<< reducedPackShift t w) - 1))) =
      writeBlock4Prog (dstMetaBase + 8 + 12, ((hp 12, hp 13), (hp 14, hp 15))) := by
    rw [heq13, heq12, heq15, heq14]
  have hb1_eq : writeBlock3Prog (dstMetaBase + 8 + 16,
      (reducedHalfLimbs t, (3, Nat.log 2 N))) =
      writeBlock3Prog (dstMetaBase + 8 + 16, (hp 16, (hp 17, hp 18))) := by
    rw [heq16, heq17, heq18]
  have hs'_eq : s' = s2 := by
    dsimp only [s', prog, d, writeHashParamsHiProg]
    rw [hb0_eq, hb1_eq, StateTransitionSpec.clientState_bind]
  refine ⟨⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeHashParamsHiProg]
    rw [hb0_eq, hb1_eq, validHistory_bind']
    exact ⟨hv0, hv1⟩
  · rw [hs'_eq, hfr1, hfr0]
  · intro j hj
    rw [hs'_eq]
    obtain ⟨m00, m01, m02, m03⟩ := hm0
    obtain ⟨m10, m11, m12⟩ := hm1
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show dstMetaBase + 20 + 0 = dstMetaBase + 8 + 12 by omega, hframe1 _ (by omega)]
      exact m00
    · rw [show dstMetaBase + 20 + 1 = dstMetaBase + 8 + 12 + 1 by omega, hframe1 _ (by omega)]
      exact m01
    · rw [show dstMetaBase + 20 + 2 = dstMetaBase + 8 + 12 + 2 by omega, hframe1 _ (by omega)]
      exact m02
    · rw [show dstMetaBase + 20 + 3 = dstMetaBase + 8 + 12 + 3 by omega, hframe1 _ (by omega)]
      exact m03
    · rw [show dstMetaBase + 20 + 4 = dstMetaBase + 8 + 16 by omega]; exact m10
    · rw [show dstMetaBase + 20 + 5 = dstMetaBase + 8 + 16 + 1 by omega]; exact m11
    · rw [show dstMetaBase + 20 + 6 = dstMetaBase + 8 + 16 + 2 by omega]; exact m12
  · intro a ha
    rw [hs'_eq, hframe1 a (by omega), hframe0 a (by omega)]
  · dsimp only [prog, d, writeHashParamsHiProg]
    rw [hb0_eq, hb1_eq, Realization.memoryCost_bind']
    change memoryCost (writeBlock4Prog _) s + memoryCost (writeBlock3Prog _) s1 = 7
    rw [hc0, hc1]

private theorem realizesBounded_writeHashParamsHi :
    RealizesBounded .exact writeHashParamsHiProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      WriteHashParamsHiPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  have hb3 := realizesBounded_writeBlock3
  realize
  all_goals (
    rcases d with ⟨⟨hpBase, c⟩, ⟨l0, ⟨p, logN⟩⟩⟩
    obtain ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩ := h
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    obtain ⟨_, _, _, _, hc_lt, _, _, _, _, _, _⟩ :=
      computeHashCore_arith hw hN hNU hU hfit_dst
    have hfit27 : Fits w (dstMetaBase + 27) := fits_add_of_fits_offCompItems hfit_dst (by decide))
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hfit27.of_le (by omega)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
  all_goals (
    set t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    change 2 * reducedChunkBits t < w at hc_lt
    have hpow2c : Fits w (2 ^ (2 * reducedChunkBits t)) := Nat.pow_lt_pow_right one_lt_two hc_lt
    have hp_le : reducedPackShift t w ≤ 2 * reducedChunkBits t := reducedPackShift_le t w
    try rw [Nat.shiftLeft_eq, one_mul]
    first
    | exact hw_fit.of_le (by omega)
    | (rw [← two_mul]; exact hpow2c)
    | exact hpow2c.of_le (Nat.pow_le_pow_right two_pos hp_le)
    | (refine ⟨?_, hfit27.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

/-- Compute and write the 19-word `mkHashParams` block at `[dstMetaBase + 8, +19)`, returning
`epochHashSpace U w N`. -/
def writeHashParamsSubProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog ℕ
  | ((hdrBase, dstMetaBase), (wVal, (qBitsVal, logN))) => do
    let ((w0, minW0), (c, (l0, p))) ←
      computeHashCoreProg ((hdrBase, wVal), (qBitsVal, logN))
    let hpBase := dstMetaBase + 8
    let hSpace ← writeHashParamsLoProg (((hpBase, w0), (minW0, c)), (l0, p))
    writeHashParamsHiProg ((hpBase, c), (l0, (p, logN)))
    pure hSpace

/-- Precondition for `writeHashParamsSubProg`. -/
@[expose] def WriteHashParamsSubPre (w : ℕ) :
    (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((hdrBase, dstMetaBase), (wVal, (qBitsVal, logN))), s =>
    ∃ U N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      wVal = w ∧ qBitsVal = quotientBits U N ∧ logN = Nat.log 2 N ∧
      hdrBase < s.frontier ∧ dstMetaBase + 27 ≤ s.frontier ∧
      Fits w (dstMetaBase + offCompItems U w N)

/-- Functional specification and `≤ 7 * N + 39` cost bound for `writeHashParamsSubProg`. -/
theorem writeHashParamsSubProg_props {w U N hdrBase dstMetaBase : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hhdr : hdrBase < s.frontier) (h27 : dstMetaBase + 27 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((hdrBase, dstMetaBase), (w, (quotientBits U N, Nat.log 2 N)))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeHashParamsSubProg d)) ∧
    (Memory.spec 0).clientResult s (writeHashParamsSubProg d) = epochHashSpace U w N ∧
    ((Memory.spec 0).clientState s (writeHashParamsSubProg d)).frontier = s.frontier ∧
    (∀ i : Fin 19,
      ((Memory.spec 0).clientState s (writeHashParamsSubProg d)).mem
        (dstMetaBase + offHashParams + i.val) =
        mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i) ∧
    (∀ a, ¬(dstMetaBase + offHashParams ≤ a ∧ a < dstMetaBase + offCompParams) →
      ((Memory.spec 0).clientState s (writeHashParamsSubProg d)).mem a = s.mem a) ∧
    memoryCost (writeHashParamsSubProg d) s ≤ 7 * N + 39 := by
  intro d
  obtain ⟨hv_core, hst_core, hres_core, hc_core⟩ :=
    computeHashCoreProg_exec (s := s) hw hN hNU hU hhdr hfit_dst
  obtain ⟨_, hv_lo, hres_lo, hfr_lo, hmem_lo, hframe_lo, hc_lo⟩ :=
    writeHashParamsLoProg_spec (s := s) hw hN hNU hU h27 hfit_dst
  set t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
  set d_lo := (((dstMetaBase + 8, epochQBits U N),
    (min (epochQBits U N) (3 * epochHashB N), reducedChunkBits t)),
    (reducedHalfLimbs t, reducedPackShift t w))
  set s1 := (Memory.spec 0).clientState s (writeHashParamsLoProg d_lo)
  obtain ⟨_, hv_hi, hfr_hi, hmem_hi, hframe_hi, hc_hi⟩ :=
    writeHashParamsHiProg_spec (s := s1) hw hN hNU hU (hfr_lo.symm ▸ h27) hfit_dst
  set d_hi := ((dstMetaBase + 8, reducedChunkBits t),
    (reducedHalfLimbs t, (reducedPackShift t w, Nat.log 2 N)))
  set s2 := (Memory.spec 0).clientState s1 (writeHashParamsHiProg d_hi)
  have hs_final : (Memory.spec 0).clientState s (writeHashParamsSubProg d) = s2 := by
    dsimp only [d, writeHashParamsSubProg]
    rw [StateTransitionSpec.clientState_bind, hst_core, hres_core]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, hres_lo, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [d, writeHashParamsSubProg]
    rw [validHistory_bind', hst_core, hres_core]
    refine ⟨hv_core, ?_⟩
    dsimp only; rw [validHistory_bind']
    refine ⟨hv_lo, ?_⟩
    rw [validHistory_bind']; exact ⟨hv_hi, trivial⟩
  · dsimp only [d, writeHashParamsSubProg]
    rw [prog_clientResult_bind, hst_core, hres_core]
    dsimp only
    rw [prog_clientResult_bind, hres_lo, prog_clientResult_bind, prog_clientResult_pure]
  · rw [hs_final, hfr_hi, hfr_lo]
  · intro ⟨j, hj⟩
    rw [hs_final]
    dsimp only [offHashParams]
    by_cases hj12 : j < 12
    · rw [hframe_hi _ (by omega)]
      exact hmem_lo j hj12
    · have hk : j - 12 < 7 := by omega
      have hhi := hmem_hi (j - 12) hk
      rw [show dstMetaBase + 20 + (j - 12) = dstMetaBase + 8 + j by omega] at hhi
      exact hhi.trans (congrArg _ (Fin.ext (by dsimp only; omega)))
  · intro a ha
    rw [hs_final]
    unfold offHashParams offCompParams at ha
    rw [hframe_hi a (by omega), hframe_lo a (by omega)]
  · dsimp only [d, writeHashParamsSubProg]
    rw [Realization.memoryCost_bind', hst_core, hres_core]
    dsimp only
    rw [Realization.memoryCost_bind', Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (computeHashCoreProg _) s +
      (memoryCost (writeHashParamsLoProg d_lo) s +
        (memoryCost (writeHashParamsHiProg d_hi) s1 + 0)) ≤ _
    omega

/-- `writeHashParamsSubProg` compiles via `RealizesBounded .exact`. -/
theorem realizesBounded_writeHashParamsSub :
    RealizesBounded .exact writeHashParamsSubProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) (WordEncoding.encode (α := ℕ))
      WriteHashParamsSubPre (fun _ _ => 0) := by
  have hcore := realizesBounded_computeHashCore
  have hlo := realizesBounded_writeHashParamsLo
  have hhi := realizesBounded_writeHashParamsHi
  realize
  all_goals (
    rcases d with ⟨⟨hdrBase, dstMetaBase⟩, ⟨wVal, ⟨qBitsVal, logN⟩⟩⟩
    obtain ⟨U, N, hw, hN, hNU, hU, hwVal, rfl, rfl, hhdr, h27, hfit_dst⟩ := h
    subst wVal
    dsimp only at *
    have hfit27 : Fits w (dstMetaBase + 27) := fits_add_of_fits_offCompItems hfit_dst (by decide))
  all_goals try exact hfit27.of_le (by omega)
  · exact ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, hhdr, hfit_dst⟩
  · obtain ⟨_, hst_core, hres_core, _⟩ :=
      computeHashCoreProg_exec (s := s) hw hN hNU hU hhdr hfit_dst
    rw [hst_core, hres_core]; dsimp only
    exact ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩
  · obtain ⟨_, hst_core, hres_core, _⟩ :=
      computeHashCoreProg_exec (s := s) hw hN hNU hU hhdr hfit_dst
    rw [hst_core, hres_core]; dsimp only
    obtain ⟨_, _, _, hfr_lo, _, _, _⟩ :=
      writeHashParamsLoProg_spec (s := s) hw hN hNU hU h27 hfit_dst
    exact ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl,
      by rw [hfr_lo]; exact h27, hfit_dst⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux
