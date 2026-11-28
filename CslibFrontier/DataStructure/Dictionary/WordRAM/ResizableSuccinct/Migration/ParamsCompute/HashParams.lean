/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.Primitives
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.HashCore
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Tactic.UpdateSimp
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
    memoryCost prog s ≤ 12 := by
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
  have heq0 : epochHashSpace U w N = hp 0 := (hpSpace_mk ..).symm
  have heq1 : 1 + reducedHalfLimbs t * 6 = hp 1 := by
    change _ = hpSeedWords hp
    rw [hpSeedWords_mk, ReducedKWise.seedWords, reducedLimbCount]; ring
  have heq2 : reducedHalfLimbs t * 6 = hp 2 := by
    change _ = hpBotWords hp
    rw [hpBotWords_mk, reducedLimbCount]; ring
  have heq3 : (1 <<< (epochQBits U N - 1)) - 1 = hp 3 := by
    simpa only [Nat.shiftLeft_eq, one_mul] using (hpMaskM_mk ..).symm
  have heq4 : (epochQBits U N - 1) >>> 1 = hp 4 := by
    simpa only [Nat.shiftRight_eq_div_pow, pow_one] using (hpHalfM_mk ..).symm
  have heq5 : (1 <<< ((epochQBits U N - 1) >>> 1)) - 1 = hp 5 := by
    simpa only [Nat.shiftRight_eq_div_pow, pow_one, Nat.shiftLeft_eq, one_mul] using
      (hpMaskH_mk ..).symm
  have heq6 : (1 <<< ((epochQBits U N - 1) - ((epochQBits U N - 1) >>> 1))) - 1 = hp 6 := by
    simpa only [Nat.shiftRight_eq_div_pow, pow_one, Nat.shiftLeft_eq, one_mul] using
      (hpMaskMH_mk ..).symm
  have heq7 : (1 <<< ((epochQBits U N - 1) -
      (((epochQBits U N - 1) >>> 1) + ((epochQBits U N - 1) >>> 1)))) - 1 = hp 7 := by
    simpa only [Nat.shiftRight_eq_div_pow, pow_one, Nat.shiftLeft_eq, one_mul, two_mul] using
      (hpMaskM2H_mk ..).symm
  have heq8 : epochQBits U N - min (epochQBits U N) (3 * epochHashB N) = hp 8 :=
    (hpRemShift_mk ..).symm
  have heq9 : reducedChunkBits t = hp 9 := (hpC_mk ..).symm
  have heq10 : (1 <<< reducedChunkBits t) - 1 = hp 10 := by
    simpa only [Nat.shiftLeft_eq, one_mul] using (hpMaskC_mk ..).symm
  have heq11 : reducedChunkBits t + reducedChunkBits t = hp 11 :=
    (two_mul _).symm.trans (hpTwoC_mk ..).symm
  clear_value hp
  obtain ⟨hv, hc, hfr, hS, hres, hm⟩ := FramedTriple.realization_of_frontier_eq (w := w)
    (s := s) (c := 12) (p := prog) (S := Set.Ico (dstMetaBase + 8) (dstMetaBase + 20))
    (Q := fun r t => r = epochHashSpace U w N ∧
      ∀ (j : ℕ) (hj : j < 12), t.mem (dstMetaBase + 8 + j) = hp ⟨j, by omega⟩) (by
    dsimp only [prog, d, writeHashParamsLoProg, writeBlock4Prog]
    rw [heq_sp, heq0, heq1, heq2, heq3, heq7, heq6, heq5, heq4, heq11, heq10, heq8, heq9]
    framed_triple
    all_goals try exact hhp _
    refine ⟨rfl, rfl, fun j hj => ?_⟩
    interval_cases j <;> update_simp)
  exact ⟨⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩,
    hv, hres, hfr, hm, fun a ha => by_contra fun h => ha (hS a h), hc⟩

private theorem realizesBounded_writeHashParamsLo :
    RealizesBounded .exact writeHashParamsLoProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      WriteHashParamsLoPre (fun _ _ => 0) := by
  realize [realizesBounded_writeBlock4]
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
    have hp_le : reducedPackShift t w ≤ reducedChunkBits t + reducedChunkBits t :=
      (reducedPackShift_le t w).trans_eq (two_mul _)
    have h2c_eq : reducedChunkBits t + reducedChunkBits t = 2 * reducedChunkBits t := by ring
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
    memoryCost prog s ≤ 7 := by
  intro t d prog s'
  have hfit27 : Fits w (dstMetaBase + 27) := fits_add_of_fits_offCompItems hfit_dst (by decide)
  have hhp := fits_epoch_mkHashParams hw hN hNU hU hfit_dst
  set hp := mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3
  have heq12 : 1 <<< (reducedChunkBits t + reducedChunkBits t) = hp 12 := by
    simpa only [Nat.shiftLeft_eq, one_mul, two_mul] using (hpPow2C_mk ..).symm
  have heq13 : (1 <<< (reducedChunkBits t + reducedChunkBits t)) - 1 = hp 13 := by
    simpa only [Nat.shiftLeft_eq, one_mul, two_mul] using (hpMask2C_mk ..).symm
  have heq14 : reducedPackShift t w = hp 14 := (hpP_mk ..).symm
  have heq15 : (1 <<< reducedPackShift t w) - 1 = hp 15 := by
    simpa only [Nat.shiftLeft_eq, one_mul] using (hpMaskP_mk ..).symm
  have heq16 : reducedHalfLimbs t = hp 16 := (hpL0_mk ..).symm
  have heq17 : 3 = hp 17 := (hpK_mk ..).symm
  have heq18 : Nat.log 2 N = hp 18 := (totalMicroBits_eq_log N).symm.trans (hpB'_mk ..).symm
  clear_value hp
  obtain ⟨hv, hc, hfr, hS, hm⟩ := FramedTriple.realization_of_frontier_eq (w := w)
    (s := s) (c := 7) (p := prog) (S := Set.Ico (dstMetaBase + 20) (dstMetaBase + 27))
    (Q := fun _ t => ∀ (j : ℕ) (hj : j < 7), t.mem (dstMetaBase + 20 + j) = hp ⟨12 + j, by omega⟩)
    (by
    dsimp only [prog, d, writeHashParamsHiProg]
    rw [heq13, heq12, heq15, heq14, heq16, heq17, heq18]
    dsimp only [writeBlock4Prog, writeBlock3Prog]
    framed_triple
    all_goals try exact hhp _
    refine ⟨rfl, fun j hj => ?_⟩
    interval_cases j <;> update_simp)
  exact ⟨⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩,
    hv, hfr, hm, fun a ha => by_contra fun h => ha (hS a h), hc⟩

private theorem realizesBounded_writeHashParamsHi :
    RealizesBounded .exact writeHashParamsHiProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      WriteHashParamsHiPre (fun _ _ => 0) := by
  realize [realizesBounded_writeBlock4, realizesBounded_writeBlock3]
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
  dsimp only [d, writeHashParamsSubProg, offHashParams, offCompParams]
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', hst_core, hres_core]
  dsimp only
  rw [validHistory_bind', validHistory_bind', StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure,
    prog_clientResult_bind, prog_clientResult_bind, prog_clientResult_pure, hres_lo,
    Realization.memoryCost_bind', Realization.memoryCost_bind', memoryCost_pure]
  refine ⟨⟨hv_core, hv_lo, hv_hi, trivial⟩, rfl, hfr_hi.trans hfr_lo, fun ⟨j, hj⟩ => ?_,
    fun a ha => (hframe_hi a (by omega)).trans (hframe_lo a (by omega)), ?_⟩
  · dsimp only
    by_cases hj12 : j < 12
    · exact (hframe_hi _ (by omega)).trans (hmem_lo j hj12)
    · have hj_eq : dstMetaBase + 8 + j = dstMetaBase + 20 + (j - 12) := by omega
      exact (congrArg _ hj_eq).trans ((hmem_hi (j - 12) (by omega)).trans
        (congrArg _ (Fin.ext (Nat.add_sub_of_le (Nat.not_lt.mp hj12)))))
  · dsimp only [d_lo, t, s1] at hc_lo hc_hi ⊢; omega

/-- `writeHashParamsSubProg` compiles via `RealizesBounded .exact`. -/
theorem realizesBounded_writeHashParamsSub :
    RealizesBounded .exact writeHashParamsSubProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) (WordEncoding.encode (α := ℕ))
      WriteHashParamsSubPre (fun _ _ => 0) := by
  realize [realizesBounded_computeHashCore, realizesBounded_writeHashParamsLo,
    realizesBounded_writeHashParamsHi]
  all_goals (
    rcases d with ⟨⟨hdrBase, dstMetaBase⟩, ⟨wVal, ⟨qBitsVal, logN⟩⟩⟩
    obtain ⟨U, N, hw, hN, hNU, hU, hwVal, rfl, rfl, hhdr, h27, hfit_dst⟩ := h
    subst wVal
    dsimp only at *
    have hfit27 : Fits w (dstMetaBase + 27) := fits_add_of_fits_offCompItems hfit_dst (by decide)
    obtain ⟨_, hst_core, hres_core, _⟩ :=
      computeHashCoreProg_exec (s := s) hw hN hNU hU hhdr hfit_dst)
  all_goals try exact hfit27.of_le (by omega)
  · exact ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, hhdr, hfit_dst⟩
  · rw [hst_core, hres_core]
    exact ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩
  · rw [hst_core, hres_core]
    obtain ⟨_, _, _, hfr_lo, _, _, _⟩ :=
      writeHashParamsLoProg_spec (s := s) hw hN hNU hU h27 hfit_dst
    exact ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, hfr_lo.symm ▸ h27,
      hfit_dst⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux
