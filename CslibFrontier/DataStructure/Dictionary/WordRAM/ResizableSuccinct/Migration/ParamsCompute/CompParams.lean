/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.Primitives
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.Scales
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Runtime 36-Word `CompParams` Writer (`writeCompParamsSubProg`)

Implements overflow-free `packedWords` evaluation (`compPackedWordsProg`), metadata word-count
computation (`computeMetaWordsProg`), and the 36-word `mkCompParams U V w N` block writer
(`writeCompParamsSubProg`) at `[dstMetaBase + 27, dstMetaBase + 63)`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

private abbrev Tup3 := ℕ × (ℕ × ℕ)
private abbrev Tup4 := (ℕ × ℕ) × (ℕ × ℕ)

/-! ## Overflow-Free `packedWords` and `computeMetaWordsProg` -/

private theorem packedWords_eq_wordOffset_add {len k w : ℕ} (hw : 0 < w) :
    packedWords len k w =
      wordOffset k w len + (if bitOffset k w len = 0 then 2 else 3) := by
  unfold packedWords
  have hb_lt : bitOffset k w len < w := bitOffset_lt hw
  rw [← wordOffset_mul_add_bitOffset (k := k) (w := w) (idx := len)]
  set W := wordOffset k w len
  set B := bitOffset k w len
  split_ifs with hB0
  · have heq : W * w + B + w - 1 = (w - 1) + W * w := by omega
    rw [heq, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega : w - 1 < w), Nat.zero_add]
  · have heq : W * w + B + w - 1 = (B - 1) + (W + 1) * w := by
      rw [Nat.add_one_mul]; omega
    rw [heq, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega : B - 1 < w), Nat.zero_add]

private def compPackedWordsProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((len, k), wVal) => do
    let prodMod := (len % wVal) * k
    let wOff := (len / wVal) * k + prodMod / wVal
    let bOff := prodMod % wVal
    let z0 ← pure 0
    if bOff = z0 then pure (wOff + 2) else pure (wOff + 3)

@[simp] private theorem clientResult_compPackedWordsProg {len k w : ℕ} (hw : 0 < w)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (compPackedWordsProg ((len, k), w)) = packedWords len k w := by
  rw [packedWords_eq_wordOffset_add hw]
  unfold compPackedWordsProg wordOffset bitOffset
  simp only [pure_bind, Nat.mod_mul_mod]
  split_ifs <;> simp only [prog_clientResult_pure]

private theorem clientState_compPackedWordsProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compPackedWordsProg d) = s := by
  rcases d with ⟨⟨len, k⟩, wVal⟩
  simp only [compPackedWordsProg, pure_bind]
  split_ifs <;> rfl

@[simp] private theorem runClient_state_compPackedWordsProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compPackedWordsProg d))) = s :=
  clientState_compPackedWordsProg d s

@[simp] private theorem memoryCost_compPackedWordsProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compPackedWordsProg d) s = 0 := by
  rcases d with ⟨⟨len, k⟩, wVal⟩
  simp only [compPackedWordsProg, pure_bind]
  split_ifs <;> rfl

private def CompPackedWordsPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((len, k), wVal), _s =>
    0 < w ∧ wVal = w ∧ k ≤ w ∧ Fits w len ∧ Fits w (packedWords len k w) ∧ Fits w 3

private theorem realizesBounded_compPackedWords :
    RealizesBounded .exact compPackedWordsProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompPackedWordsPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨len, k⟩, wVal⟩
    obtain ⟨hw, hwVal, hkw, _, hpw, _⟩ := h
    subst wVal
    dsimp only at *
    rw [packedWords_eq_wordOffset_add hw] at hpw
    simp only [wordOffset, bitOffset, Nat.mod_mul_mod] at *)
  all_goals try exact hw.ne'
  all_goals try exact mod_mul_lt_two_pow hw hkw len
  all_goals (
    split_ifs at hpw
    exact hpw.of_le (by omega))

private def maxSlabsProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (bBits, (N, sSize)) => do
    let z0 ← pure 0
    if bBits = z0 then pure 0 else pure (N / sSize)

@[simp] private theorem clientResult_maxSlabsProg (N : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (maxSlabsProg (bucketBits N, (N, slabSize N))) =
      maxFullSlabs N := by
  dsimp only [maxSlabsProg, maxFullSlabs]; simp only [pure_bind]
  split_ifs <;> simp only [prog_clientResult_pure]

private theorem clientState_maxSlabsProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (maxSlabsProg p) = s := by
  rcases p with ⟨b, ⟨N, sz⟩⟩; dsimp only [maxSlabsProg]; simp only [pure_bind]
  split_ifs <;> rfl

@[simp] private theorem runClient_state_maxSlabsProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (maxSlabsProg p))) = s :=
  clientState_maxSlabsProg p s

@[simp] private theorem memoryCost_maxSlabsProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (maxSlabsProg p) s = 0 := by
  rcases p with ⟨b, ⟨N, sz⟩⟩; dsimp only [maxSlabsProg]; simp only [pure_bind]
  split_ifs <;> rfl

private theorem validHistory_maxSlabsProg {w : ℕ} (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (maxSlabsProg p)) := by
  rcases p with ⟨b, ⟨N, sz⟩⟩; dsimp only [maxSlabsProg]; simp only [pure_bind]
  split_ifs <;> trivial

private def MaxSlabsPre (_w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (bBits, (_N, sSize)), _ => bBits ≠ 0 → 0 < sSize

private theorem realizesBounded_maxSlabs :
    RealizesBounded .exact maxSlabsProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      MaxSlabsPre (fun _ _ => 0) := by
  realize
  rcases d with ⟨bBits, ⟨N, sSize⟩⟩
  dsimp only at *
  exact (h hc).ne'

private def computeMetaWordsProg : (Tup4 × Tup4) → Memory.Prog Tup3
  | (((wVal, N), (bBits, lmBits)), ((logN, sSize), (maxTail, gmSlabMeta))) => do
    let maxSlabs ← maxSlabsProg (bBits, (N, sSize))
    let gmLen ← ifEqZeroProg (bBits, (4, gmSlabMeta + maxSlabs * 4))
    let lmSubW ← compPackedWordsProg ((1 <<< logN, lmBits), wVal)
    let gmWords ← compPackedWordsProg ((gmLen, logN + 1), wVal)
    let tailWords ← compPackedWordsProg ((maxTail, logN + 1), wVal)
    pure (lmSubW, (gmWords, tailWords))

private def ComputeMetaWordsPre (w : ℕ) : (Tup4 × Tup4) → Memory.State → Prop
  | (((wVal, N), (bBits, lmBits)), ((logN, sSize), (maxTail, gmSlabMeta))), _s =>
    ∃ U dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      wVal = w ∧ bBits = bucketBits N ∧ lmBits = effBucketPosBits N ∧
      logN = Nat.log 2 N ∧ sSize = slabSize N ∧ maxTail = maxTailItems N ∧
      gmSlabMeta = gmSlabMetaBase N ∧
      Fits w (dstMetaBase + offCompItems U w N)

private theorem computeMetaWordsProg_spec {w U dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (_hNU : N ≤ U) (_hU : Fits w U)
    (_hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (((w, N), (bucketBits N, effBucketPosBits N)),
      ((Nat.log 2 N, slabSize N), (maxTailItems N, gmSlabMetaBase N)))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeMetaWordsProg d)) ∧
    (Memory.spec 0).clientState s (computeMetaWordsProg d) = s ∧
    (Memory.spec 0).clientResult s (computeMetaWordsProg d) =
      (lmSubWords N w,
        (packedWords (globalMetaLen N) (globalPtrBits N) w,
          packedWords (maxTailItems N) (globalPtrBits N) w)) ∧
    memoryCost (computeMetaWordsProg d) s = 0 := by
  intro d
  have hgmBits_eq : Nat.log 2 N + 1 = globalPtrBits N := (clog2_succ_eq_log2_add_one hN).symm
  have htotMicro_eq : (1 <<< Nat.log 2 N) = totalMicroBuckets N := by
    rw [Nat.shiftLeft_eq, one_mul, ← totalMicroBits_eq_log]; rfl
  have hgmLen_eq := globalMetaLen_cond_eq N
  have hv_pw : ∀ p st, (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (compPackedWordsProg p)) := by
    rintro ⟨⟨len, k⟩, wV⟩ st
    simp only [compPackedWordsProg, pure_bind]
    split_ifs <;> trivial
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [d, computeMetaWordsProg]
    rw [htotMicro_eq, hgmBits_eq, validHistory_bind', clientState_maxSlabsProg,
      clientResult_maxSlabsProg, validHistory_bind', clientState_ifEqZeroProg,
      clientResult_ifEqZeroProg, hgmLen_eq]
    repeat rw [validHistory_bind', clientState_compPackedWordsProg]
    exact ⟨validHistory_maxSlabsProg _ _, validHistory_ifEqZeroProg _ _,
      hv_pw _ s, hv_pw _ s, hv_pw _ s, trivial⟩
  · simpa only [d, computeMetaWordsProg, prog_runClient_state_bind, runClient_state_maxSlabsProg,
      runClient_state_compPackedWordsProg, prog_runClient_state_pure] using
      clientState_ifEqZeroProg _ _
  all_goals simp only [d, computeMetaWordsProg, prog_clientResult_bind,
    Realization.memoryCost_bind', clientResult_maxSlabsProg, memoryCost_maxSlabsProg,
    clientResult_ifEqZeroProg, memoryCost_ifEqZeroProg, clientResult_compPackedWordsProg hw,
    memoryCost_compPackedWordsProg, prog_clientResult_pure, memoryCost_pure, hgmLen_eq,
    htotMicro_eq, hgmBits_eq, lmSubWords]

private theorem realizesBounded_computeMetaWords :
    RealizesBounded .exact computeMetaWordsProg
      (WordEncoding.encode (α := Tup4 × Tup4))
      (WordEncoding.encode (α := Tup3))
      ComputeMetaWordsPre (fun _ _ => 0) := by
  have hms := realizesBounded_maxSlabs
  have hifz := realizesBounded_ifEqZero
  have hpw := realizesBounded_compPackedWords
  realize
  all_goals (
    rcases d with ⟨⟨⟨wVal, N⟩, ⟨bBits, lmBits⟩⟩, ⟨⟨logN, sSize⟩, ⟨maxTail, gmSlabMeta⟩⟩⟩
    obtain ⟨U, dstMetaBase, hw, hN, hNU, hU, hwVal, rfl, rfl, rfl, rfl, rfl, rfl, hfit_dst⟩ := h
    subst wVal
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hmax_fit : Fits w (max N 1) := max_n_one_lt_two_pow_w hw hNU hU
    obtain ⟨hgmLen_fit, _, _, _, _⟩ := computeGmBasesProg_spec (s := s) hw hN hNU hU hfit_dst
    obtain ⟨hlogN_lt, _, _, _, _, _, _⟩ := computeLogScales_arith hN hNU hU h225
    have hgmBits_eq : Nat.log 2 N + 1 = globalPtrBits N := (clog2_succ_eq_log2_add_one hN).symm
    have htotMicro_eq : (1 <<< Nat.log 2 N) = totalMicroBuckets N := by
      rw [Nat.shiftLeft_eq, one_mul, ← totalMicroBits_eq_log, ← totalMicroBuckets]
    repeat first
      | rw [hgmBits_eq] | rw [htotMicro_eq]
      | rw [clientState_maxSlabsProg] | rw [clientResult_maxSlabsProg]
      | rw [clientState_ifEqZeroProg] | rw [clientResult_ifEqZeroProg]
      | rw [globalMetaLen_cond_eq] | rw [clientState_compPackedWordsProg])
  all_goals try exact fun _ => Nat.two_pow_pos _
  all_goals try (
    dsimp only [CompPackedWordsPre]
    refine ⟨hw, rfl, ?_, ?_, ?_, h225.of_le (u := 3) (by decide)⟩
    · first
      | exact effBucketPosBits_le_of_lt_pow hNU hU
      | exact globalPtrBits_le_of_lt_pow hNU hU
    · first
      | exact hmax_fit.of_le (totalMicroBuckets_le N)
      | exact hgmLen_fit
      | exact hU.of_le ((maxTailItems_le N).trans hNU)
    · refine hfit_dst.of_le ?_
      (try change lmSubWords N w ≤ _)
      unfold offCompItems offDenseToTail offTailToDense offCompGM
      omega)
  all_goals (
    have hgmBits_le : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hNU hU
    first
    | exact h225.of_le (by decide)
    | exact hw_fit.of_le (by omega)
    | exact hmax_fit.of_le (totalMicroBuckets_le N)
    | (by_cases hb0 : bucketBits N = 0
       · simp only [gmSlabMetaBase, gmTailOwnerBase, gmTailPtrBase, gmSlabDirBase, maxTailItems,
           tailCapPerBucket, dirSlabsPerBucket, maxFullSlabs, numBuckets, hb0, ↓reduceIte,
           pow_zero, mul_zero, add_zero]
         exact h225.of_le (by decide)
       · simpa only [← globalMetaLen_cond_eq N, hb0, ↓reduceIte] using hgmLen_fit))

/-! ## Sub-Block Writers (`SubA`..`SubE`, `writeCompScalesGmDProg`, `writeCompABProg`) -/

private def writeCompSubAProg : Tup4 × Tup3 → Memory.Prog ℕ
  | (((cpBase, wVal), (N, qBitsVal)), (vBits, (hSpace, lmSubW))) => do
    let off0 := 225 + hSpace
    writeBlock4Prog (cpBase, ((wVal, N), (N - 1, qBitsVal)))
    writeBlock4Prog (cpBase + 4, ((vBits, off0), (off0 + lmSubW, off0 + lmSubW * 2)))
    pure (off0 + lmSubW * 3)

private def WriteCompSubAPre (w : ℕ) : Tup4 × Tup3 → Memory.State → Prop
  | (((cpBase, wVal), (N, qBitsVal)), (vBits, (hSpace, lmSubW))), s =>
    ∃ U V dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      cpBase = dstMetaBase + 27 ∧ wVal = w ∧ qBitsVal = quotientBits U N ∧ vBits = valBits V ∧
      hSpace = epochHashSpace U w N ∧ lmSubW = lmSubWords N w ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompSubAProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (((dstMetaBase + 27, w), (N, quotientBits U N)),
      (valBits V, (epochHashSpace U w N, lmSubWords N w)))
    let prog := writeCompSubAProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompSubAPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = offCompLMSub U w N 3 ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8),
      s'.mem (dstMetaBase + 27 + j) = mkCompParams U V w N ⟨j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 27 ≤ a ∧ a < dstMetaBase + 35) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 8 := by
  intro d prog s'
  have hcp := fits_mkCompParams (V := V) hw hNU hU hV hfit_dst
  have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide)
  set cp := mkCompParams U V w N
  have ho (i : ℕ) : 225 + epochHashSpace U w N + lmSubWords N w * i = offCompLMSub U w N i := by
    dsimp only [offCompLMSub, offCompLM, epochHdrWords]
    ring
  obtain ⟨hv, hres, hfr, hmem, hframe, hc⟩ :=
    writeTwoBlock4FinRet_spec (dstMetaBase + 27) cp 0 (by decide) (offCompLMSub U w N 3) (s := s)
      (by omega) (hfit63.of_le (by omega)) hcp
  refine ⟨⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, h63, hfit_dst⟩, ?_⟩
  dsimp only [s', prog, d, writeCompSubAProg]
  rw [ho 3, ho 2, ← mul_one (lmSubWords N w), ho 1, ← add_zero (225 + epochHashSpace U w N),
    ← mul_zero (lmSubWords N w), ho 0]
  exact ⟨hv, hres, hfr, fun j hj => (hmem j hj).trans (congrArg cp (Fin.ext (Nat.zero_add j))),
    fun a ha => hframe a (by omega), hc⟩

private theorem realizesBounded_writeCompSubA :
    RealizesBounded .exact writeCompSubAProg
      (WordEncoding.encode (α := Tup4 × Tup3)) (WordEncoding.encode (α := ℕ))
      WriteCompSubAPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨⟨⟨cpBase, wVal⟩, ⟨N, qBitsVal⟩⟩, ⟨vBits, ⟨hSpace, lmSubW⟩⟩⟩
    obtain ⟨U, V, dstMetaBase, hw, hN, hNU, hU, _hV, rfl, hwVal, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩ := h
    subst wVal
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hN_fit : Fits w N := hU.of_le hNU
    have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide))
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hfit63.of_le (by omega)
  all_goals try exact hN
  all_goals (
    first
    | (refine hfit_dst.of_le ?_
       unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
       omega)
    | (refine ⟨?_, hfit63.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

private def writeCompSubBProg : Tup4 → Memory.Prog ℕ
  | ((cpBase, off3), (lmSubW, lmBits)) => do
    writeBlock4Prog (cpBase + 8,
      ((off3, off3 + lmSubW), (off3 + lmSubW * 2, off3 + lmSubW * 3)))
    writeBlock4Prog (cpBase + 12,
      ((off3 + lmSubW * 4, off3 + lmSubW * 5), (lmBits, off3 + lmSubW * 6)))
    pure (off3 + lmSubW * 6)

private def WriteCompSubBPre (w : ℕ) : Tup4 → Memory.State → Prop
  | ((cpBase, off3), (lmSubW, lmBits)), s =>
    ∃ U V dstMetaBase N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      cpBase = dstMetaBase + 27 ∧ off3 = offCompLMSub U w N 3 ∧
      lmSubW = lmSubWords N w ∧ lmBits = effBucketPosBits N ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompSubBProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((dstMetaBase + 27, offCompLMSub U w N 3), (lmSubWords N w, effBucketPosBits N))
    let prog := writeCompSubBProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompSubBPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = offCompGM U w N ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8),
      s'.mem (dstMetaBase + 35 + j) = mkCompParams U V w N ⟨8 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 35 ≤ a ∧ a < dstMetaBase + 43) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 8 := by
  intro d prog s'
  have hcp := fits_mkCompParams (V := V) hw hNU hU hV hfit_dst
  have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide)
  set cp := mkCompParams U V w N
  have ho (i : ℕ) :
      offCompLMSub U w N 3 + lmSubWords N w * i = offCompLMSub U w N (3 + i) := by
    dsimp only [offCompLMSub]
    ring
  have hogm : offCompLMSub U w N 3 + lmSubWords N w * 6 = offCompGM U w N := by
    dsimp only [offCompGM, offCompLMSub]
    ring
  obtain ⟨hv, hres, hfr, hmem, hframe, hc⟩ :=
    writeTwoBlock4FinRet_spec (dstMetaBase + 35) cp 8 (by decide) (offCompGM U w N) (s := s)
      (by omega) (hfit63.of_le (by omega)) hcp
  have hb35 : dstMetaBase + 27 + 8 = dstMetaBase + 35 := by omega
  have hb39 : dstMetaBase + 27 + 12 = dstMetaBase + 35 + 4 := by omega
  refine ⟨⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, h63, hfit_dst⟩, ?_⟩
  dsimp only [s', prog, d, writeCompSubBProg]
  rw [hogm, ho 5, ho 4, ho 3, ho 2, ← mul_one (lmSubWords N w), ho 1, hb35, hb39]
  exact ⟨hv, hres, hfr, hmem, fun a ha => hframe a (by omega), hc⟩

private theorem realizesBounded_writeCompSubB :
    RealizesBounded .exact writeCompSubBProg
      (WordEncoding.encode (α := Tup4)) (WordEncoding.encode (α := ℕ))
      WriteCompSubBPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨⟨cpBase, off3⟩, ⟨lmSubW, lmBits⟩⟩
    obtain ⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, _hV, rfl, rfl, rfl, rfl, h63, hfit_dst⟩ := h
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide))
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hfit63.of_le (by omega)
  all_goals (
    first
    | (refine hfit_dst.of_le ?_
       unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLMSub
       omega)
    | (refine ⟨?_, hfit63.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

private def writeCompSubCProg : Tup4 × Tup4 → Memory.Prog ℕ
  | (((cpBase, offGM), (gmWords, tailWords)), ((logN, maxTail), (bBits, sSize))) => do
    let offTD := offGM + gmWords
    let offDT := offTD + tailWords
    writeBlock4Prog (cpBase + 16, ((logN + 1, offTD), (offDT, maxTail)))
    writeBlock4Prog (cpBase + 20, ((bBits, (1 <<< bBits) - 1), (sSize, sSize - 1)))
    pure (offDT + tailWords)

private def WriteCompSubCPre (w : ℕ) : Tup4 × Tup4 → Memory.State → Prop
  | (((cpBase, offGM), (gmWords, tailWords)), ((logN, maxTail), (bBits, sSize))), s =>
    ∃ U V dstMetaBase N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      cpBase = dstMetaBase + 27 ∧ offGM = offCompGM U w N ∧
      gmWords = packedWords (globalMetaLen N) (globalPtrBits N) w ∧
      tailWords = packedWords (maxTailItems N) (globalPtrBits N) w ∧
      logN = Nat.log 2 N ∧ maxTail = maxTailItems N ∧
      bBits = bucketBits N ∧ sSize = slabSize N ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompSubCProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (((dstMetaBase + 27, offCompGM U w N),
      (packedWords (globalMetaLen N) (globalPtrBits N) w,
       packedWords (maxTailItems N) (globalPtrBits N) w)),
      ((Nat.log 2 N, maxTailItems N), (bucketBits N, slabSize N)))
    let prog := writeCompSubCProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompSubCPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = offCompItems U w N ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8),
      s'.mem (dstMetaBase + 43 + j) = mkCompParams U V w N ⟨16 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 43 ≤ a ∧ a < dstMetaBase + 51) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 8 := by
  intro d prog s'
  have hcp := fits_mkCompParams (V := V) hw hNU hU hV hfit_dst
  have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide)
  set cp := mkCompParams U V w N
  have h16 : Nat.log 2 N + 1 = globalPtrBits N := (clog2_succ_eq_log2_add_one hN).symm
  have h21 : (1 <<< bucketBits N) - 1 = 2 ^ bucketBits N - 1 := by
    rw [Nat.shiftLeft_eq, one_mul]
  obtain ⟨hv, hres, hfr, hmem, hframe, hc⟩ :=
    writeTwoBlock4FinRet_spec (dstMetaBase + 43) cp 16 (by decide) (offCompItems U w N) (s := s)
      (by omega) (hfit63.of_le (by omega)) hcp
  have hb43 : dstMetaBase + 27 + 16 = dstMetaBase + 43 := by omega
  have hb47 : dstMetaBase + 27 + 20 = dstMetaBase + 43 + 4 := by omega
  refine ⟨⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩, ?_⟩
  dsimp only [s', prog, d, writeCompSubCProg]
  rw [h16, h21, hb43, hb47]
  exact ⟨hv, hres, hfr, hmem, fun a ha => hframe a (by omega), hc⟩

private theorem realizesBounded_writeCompSubC :
    RealizesBounded .exact writeCompSubCProg
      (WordEncoding.encode (α := Tup4 × Tup4)) (WordEncoding.encode (α := ℕ))
      WriteCompSubCPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨⟨⟨cpBase, offGM⟩, ⟨gmWords, tailWords⟩⟩, ⟨⟨logN, maxTail⟩, ⟨bBits, sSize⟩⟩⟩
    obtain ⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, _hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩ := h
    dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hmax_fit : Fits w (max N 1) := max_n_one_lt_two_pow_w hw hNU hU
    have hlogN_lt : Nat.log 2 N < w := (computeLogScales_arith hN hNU hU h225).1
    have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide))
  all_goals try exact hfit63.of_le (by omega)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
  all_goals (
    first
    | exact (by unfold slabSize; exact Nat.one_le_two_pow : 1 ≤ slabSize N)
    | exact hw_fit.of_le (by omega)
    | (rw [Nat.shiftLeft_eq, one_mul]
       have h2b : 2 ^ bucketBits N ≤ max N 1 :=
         (Nat.pow_le_pow_right two_pos (bucketBits_le_totalMicroBits N)).trans
           (totalMicroBuckets_le N)
       exact hmax_fit.of_le (by omega))
    | (refine hfit_dst.of_le ?_
       unfold offCompItems offDenseToTail offTailToDense offCompGM; omega)
    | (refine ⟨?_, hfit63.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

private def writeCompSubDProg : Tup4 × Tup4 → Memory.Prog Unit
  | (((cpBase, sSize), (dirSlabs, tailCap)), ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta))) =>
    do
      let dirSlabsSub1 ← subSatProg (dirSlabs, 1)
      writeBlock4Prog (cpBase + 24, ((sSize + sSize, dirSlabs), (dirSlabsSub1, tailCap)))
      writeBlock4Prog (cpBase + 28, ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta)))

private def WriteCompSubDPre (w : ℕ) : Tup4 × Tup4 → Memory.State → Prop
  | (((cpBase, sSize), (dirSlabs, tailCap)),
      ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta))), s =>
    ∃ U V dstMetaBase N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      cpBase = dstMetaBase + 27 ∧ sSize = slabSize N ∧ dirSlabs = dirSlabsPerBucket N ∧
      tailCap = tailCapPerBucket N ∧ gmDirBase = gmSlabDirBase N ∧
      gmTailPtr = gmTailPtrBase N ∧ gmTailOwn = gmTailOwnerBase N ∧
      gmSlabMeta = gmSlabMetaBase N ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompSubDProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (((dstMetaBase + 27, slabSize N), (dirSlabsPerBucket N, tailCapPerBucket N)),
      ((gmSlabDirBase N, gmTailPtrBase N), (gmTailOwnerBase N, gmSlabMetaBase N)))
    let prog := writeCompSubDProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompSubDPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8),
      s'.mem (dstMetaBase + 51 + j) = mkCompParams U V w N ⟨24 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 51 ≤ a ∧ a < dstMetaBase + 59) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 8 := by
  intro d prog s'
  have hcp := fits_mkCompParams (V := V) hw hNU hU hV hfit_dst
  have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide)
  set cp := mkCompParams U V w N
  have h24 : slabSize N + slabSize N = 2 * slabSize N := by ring
  obtain ⟨hv, hfr, hmem, hframe, hc⟩ :=
    writeTwoBlock4Fin_spec (dstMetaBase + 51) cp 24 (by decide) (s := s)
      (by omega) (hfit63.of_le (by omega)) hcp
  have hb51 : dstMetaBase + 27 + 24 = dstMetaBase + 51 := by omega
  have hb55 : dstMetaBase + 27 + 28 = dstMetaBase + 51 + 4 := by omega
  dsimp only [s', prog, d, writeCompSubDProg]
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_subSatProg, clientResult_subSatProg, memoryCost_subSatProg, zero_add,
    h24, hb51, hb55]
  exact ⟨⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩, ⟨validHistory_subSatProg _ _, hv⟩, hfr, hmem, fun a ha => hframe a (by omega),
    hc⟩

private theorem realizesBounded_writeCompSubD :
    RealizesBounded .exact writeCompSubDProg
      (WordEncoding.encode (α := Tup4 × Tup4)) (WordEncoding.encode (α := Unit))
      WriteCompSubDPre (fun _ _ => 0) := by
  have hsub := realizesBounded_subSat
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨⟨⟨cpBase, sSize⟩, ⟨dirSlabs, tailCap⟩⟩,
      ⟨⟨gmDirBase, gmTailPtr⟩, ⟨gmTailOwn, gmSlabMeta⟩⟩⟩
    obtain ⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, _hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩ := h
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide)
    obtain ⟨_, _, _, _, h2s_fit⟩ := computeCompScales_arith hw hN hNU hU h225
    repeat rw [clientState_subSatProg]
    repeat rw [clientResult_subSatProg])
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hfit63.of_le (by omega)
  all_goals (
    first
    | exact h2s_fit.of_le (by omega)
    | (refine ⟨?_, hfit63.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

private def writeCompSubEProg : ℕ × Tup4 → Memory.Prog Unit
  | (cpBase, ((numMicro, minCap), (offItemsVal, hSpace))) =>
    writeBlock4Prog (cpBase + 32, ((numMicro, minCap), (offItemsVal, hSpace)))

private def WriteCompSubEPre (w : ℕ) : ℕ × Tup4 → Memory.State → Prop
  | (cpBase, _), s =>
    ∃ U dstMetaBase N,
      cpBase = dstMetaBase + 27 ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompSubEProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (dstMetaBase + 27,
      ((numMicroPerBucket N, min N (effBucketCap N)),
       (offCompItems U w N, epochHashSpace U w N)))
    let prog := writeCompSubEProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompSubEPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 4),
      s'.mem (dstMetaBase + 59 + j) = mkCompParams U V w N ⟨32 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 59 ≤ a ∧ a < dstMetaBase + 63) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 4 := by
  intro d prog s'
  have hcp := fits_mkCompParams (V := V) hw hNU hU hV hfit_dst
  have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide)
  obtain ⟨_, hv, hfr, hm, hframe, hc⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 27 + 32)
      (numMicroPerBucket N) (min N (effBucketCap N)) (offCompItems U w N) (epochHashSpace U w N)
      (s := s) (by omega) (hfit63.of_le (by omega))
      (hcp 32) (hcp 33) (hcp 34) (hcp 35)
  refine ⟨⟨U, dstMetaBase, N, rfl, h63, hfit_dst⟩, hv, hfr, fun j hj => ?_,
    fun a ha => hframe a (by omega), hc⟩
  obtain ⟨m0, m1, m2, m3⟩ := hm
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    [exact m0; exact m1; exact m2; exact m3]

private theorem realizesBounded_writeCompSubE :
    RealizesBounded .exact writeCompSubEProg
      (WordEncoding.encode (α := ℕ × Tup4)) (WordEncoding.encode (α := Unit))
      WriteCompSubEPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨cpBase, ⟨⟨numMicro, minCap⟩, ⟨offItemsVal, hSpace⟩⟩⟩
    obtain ⟨U, dstMetaBase, N, rfl, h63, hfit_dst⟩ := h
    dsimp only at *
    have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide))
  all_goals first | exact hfit63.of_le (by omega) | exact ⟨by omega, hfit63.of_le (by omega)⟩

private def writeCompScalesGmDProg :
    Tup4 → Memory.Prog ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
  | ((dstMetaBase, N), (logN, llf)) => do
    let ((bBits, lmBits), ((numMicro, minCap), (sSize, (dirSlabs, tailCap)))) ←
      computeCompScalesProg ((dstMetaBase, N), (logN, llf))
    let (maxTail, ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta))) ←
      computeGmBasesProg (bBits, (dirSlabs, tailCap))
    writeCompSubDProg
      (((dstMetaBase + 27, sSize), (dirSlabs, tailCap)),
       ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta)))
    pure ((bBits, lmBits), ((numMicro, minCap), (sSize, (maxTail, gmSlabMeta))))

private def WriteCompScalesGmDPre (w : ℕ) : Tup4 → Memory.State → Prop
  | ((dstMetaBase, N), (logN, llf)), s =>
    ∃ U,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      logN = Nat.log 2 N ∧ llf = Dynamic.logLogFactor N ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompScalesGmDProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((dstMetaBase, N), (Nat.log 2 N, Dynamic.logLogFactor N))
    let prog := writeCompScalesGmDProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompScalesGmDPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog =
      ((bucketBits N, effBucketPosBits N),
        ((numMicroPerBucket N, min N (effBucketCap N)),
          (slabSize N, (maxTailItems N, gmSlabMetaBase N)))) ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8),
      s'.mem (dstMetaBase + 51 + j) = mkCompParams U V w N ⟨24 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 51 ≤ a ∧ a < dstMetaBase + 59) → s'.mem a = s.mem a) ∧
    memoryCost prog s ≤ N + 12 := by
  intro d prog s'
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  obtain ⟨hv_sc, hst_sc, hres_sc, hc_sc⟩ :=
    computeCompScalesProg_exec (s := s) (dstMetaBase := dstMetaBase) hw hN hNU hU (by omega) h225
  obtain ⟨_, hv_gm, hst_gm, hres_gm, hc_gm⟩ :=
    computeGmBasesProg_spec (s := s) hw hN hNU hU hfit_dst
  obtain ⟨_, hvD, hfrD, hmD, hframeD, hcD⟩ :=
    writeCompSubDProg_spec (V := V) (s := s) hw hN hNU hU hV h63 hfit_dst
  dsimp only [s', prog, d, writeCompScalesGmDProg]
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', hst_sc, hres_sc]
  dsimp only
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', hst_gm, hres_gm]
  dsimp only
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', StateTransitionSpec.clientState_pure, prog_clientResult_pure,
    memoryCost_pure]
  exact ⟨⟨U, hw, hN, hNU, hU, rfl, rfl, h63, hfit_dst⟩, ⟨hv_sc, hv_gm, hvD, trivial⟩, rfl, hfrD,
    hmD, hframeD, by omega⟩

private theorem realizesBounded_writeCompScalesGmD :
    RealizesBounded .exact writeCompScalesGmDProg
      (WordEncoding.encode (α := Tup4))
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      WriteCompScalesGmDPre (fun _ _ => 0) := by
  have hsc := realizesBounded_computeCompScales
  have hgm := realizesBounded_computeGmBases
  have hD := realizesBounded_writeCompSubD
  realize
  all_goals (
    rcases d with ⟨⟨dstMetaBase, N⟩, ⟨logN, llf⟩⟩
    obtain ⟨U, hw, hN, hNU, hU, rfl, rfl, h63, hfit_dst⟩ := h
    dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hdst_lt : dstMetaBase < s.frontier := by omega
    have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide)
    obtain ⟨_, hst_sc, hres_sc, _⟩ :=
      computeCompScalesProg_exec (s := s) hw hN hNU hU hdst_lt h225
    obtain ⟨_, _, hst_gm, hres_gm, _⟩ :=
      computeGmBasesProg_spec (s := s) hw hN hNU hU hfit_dst)
  all_goals try (refine hfit63.of_le ?_; omega)
  · exact ⟨U, hw, hN, hNU, hU, rfl, rfl, hdst_lt, h225⟩
  · rw [hst_sc, hres_sc]; dsimp only
    exact ⟨U, dstMetaBase, N, hw, hN, hNU, hU, rfl, rfl, rfl, hfit_dst⟩
  · rw [hst_sc, hres_sc]; dsimp only
    rw [hst_gm, hres_gm]; dsimp only
    exact ⟨U, 1, dstMetaBase, N, hw, hN, hNU, hU, Nat.one_le_two_pow,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h63, hfit_dst⟩

private def writeCompABProg : Tup4 × Tup4 → Memory.Prog ℕ
  | (((cpBase, wVal), (N, qBitsVal)), ((vBits, hSpace), (lmSubW, lmBits))) => do
    let off3 ← writeCompSubAProg (((cpBase, wVal), (N, qBitsVal)), (vBits, (hSpace, lmSubW)))
    writeCompSubBProg ((cpBase, off3), (lmSubW, lmBits))

private def WriteCompABPre (w : ℕ) : Tup4 × Tup4 → Memory.State → Prop
  | (((cpBase, wVal), (N, qBitsVal)), ((vBits, hSpace), (lmSubW, lmBits))), s =>
    ∃ U V dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      cpBase = dstMetaBase + 27 ∧ wVal = w ∧ qBitsVal = quotientBits U N ∧ vBits = valBits V ∧
      hSpace = epochHashSpace U w N ∧ lmSubW = lmSubWords N w ∧ lmBits = effBucketPosBits N ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompABProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (((dstMetaBase + 27, w), (N, quotientBits U N)),
      ((valBits V, epochHashSpace U w N), (lmSubWords N w, effBucketPosBits N)))
    let prog := writeCompABProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompABPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = offCompGM U w N ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 16),
      s'.mem (dstMetaBase + 27 + j) = mkCompParams U V w N ⟨j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 27 ≤ a ∧ a < dstMetaBase + 43) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 16 := by
  intro d prog s'
  obtain ⟨_, hvA, hresA, hfrA, hmA, hframeA, hcA⟩ :=
    writeCompSubAProg_spec (s := s) hw hN hNU hU hV h63 hfit_dst
  set sA := (Memory.spec 0).clientState s (writeCompSubAProg
    (((dstMetaBase + 27, w), (N, quotientBits U N)),
     (valBits V, (epochHashSpace U w N, lmSubWords N w))))
  obtain ⟨_, hvB, hresB, hfrB, hmB, hframeB, hcB⟩ :=
    writeCompSubBProg_spec (s := sA) hw hN hNU hU hV (hfrA.symm ▸ h63) hfit_dst
  set sB := (Memory.spec 0).clientState sA (writeCompSubBProg
    ((dstMetaBase + 27, offCompLMSub U w N 3), (lmSubWords N w, effBucketPosBits N)))
  dsimp only [s', prog, d, writeCompABProg]
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', hresA, hcA, hcB]
  refine ⟨⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩, ⟨hvA, hvB⟩, hresB, hfrB.trans hfrA, fun j hj => ?_,
    fun a ha => (hframeB a (by omega)).trans (hframeA a (by omega)), rfl⟩
  by_cases hj8 : j < 8
  · rw [hframeB _ (by omega)]; exact hmA j hj8
  · have hB := hmB (j - 8) (by omega)
    rw [show dstMetaBase + 35 + (j - 8) = dstMetaBase + 27 + j by omega] at hB
    exact hB.trans (congrArg _ (Fin.ext (by dsimp only; omega)))

private theorem realizesBounded_writeCompAB :
    RealizesBounded .exact writeCompABProg
      (WordEncoding.encode (α := Tup4 × Tup4)) (WordEncoding.encode (α := ℕ))
      WriteCompABPre (fun _ _ => 0) := by
  have hA := realizesBounded_writeCompSubA
  have hB := realizesBounded_writeCompSubB
  realize
  all_goals
    rcases d with ⟨⟨⟨cpBase, wVal⟩, ⟨N, qBitsVal⟩⟩, ⟨⟨vBits, hSpace⟩, ⟨lmSubW, lmBits⟩⟩⟩
    obtain ⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, hwVal, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩ := h
    subst wVal
  · exact ⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, h63, hfit_dst⟩
  · obtain ⟨_, _, hresA, hfrA, _, _, _⟩ :=
      writeCompSubAProg_spec (s := s) hw hN hNU hU hV h63 hfit_dst
    dsimp only at *
    rw [hresA]
    exact ⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl,
      hfrA.symm ▸ h63, hfit_dst⟩

/-! ## Combined 36-Word `CompParams` Writer (`writeCompParamsSubProg`) -/

/-- Compute and write the 36-word `mkCompParams U V w N` block at `[dstMetaBase + 27, +36)`,
returning `offCompItems U w N`. -/
def writeCompParamsSubProg :
    (ℕ × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.Prog ℕ
  | ((dstMetaBase, (wVal, N)), ((qBitsVal, vBits), (logN, (llf, hSpace)))) => do
    let ((bBits, lmBits), ((numMicro, minCap), (sSize, (maxTail, gmSlabMeta)))) ←
      writeCompScalesGmDProg ((dstMetaBase, N), (logN, llf))
    let (lmSubW, (gmWords, tailWords)) ←
      computeMetaWordsProg
        (((wVal, N), (bBits, lmBits)), ((logN, sSize), (maxTail, gmSlabMeta)))
    let cpBase := dstMetaBase + 27
    let offGM ← writeCompABProg
      (((cpBase, wVal), (N, qBitsVal)), ((vBits, hSpace), (lmSubW, lmBits)))
    let offItemsVal ← writeCompSubCProg
      (((cpBase, offGM), (gmWords, tailWords)), ((logN, maxTail), (bBits, sSize)))
    writeCompSubEProg (cpBase, ((numMicro, minCap), (offItemsVal, hSpace)))
    pure offItemsVal

/-- Precondition for `writeCompParamsSubProg`. -/
@[expose] def WriteCompParamsSubPre (w : ℕ) :
    (ℕ × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.State → Prop
  | ((dstMetaBase, (wVal, N)), ((qBitsVal, vBits), (logN, (llf, hSpace)))), s =>
    ∃ U V,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      wVal = w ∧ qBitsVal = quotientBits U N ∧ vBits = valBits V ∧
      logN = Nat.log 2 N ∧ llf = Dynamic.logLogFactor N ∧
      hSpace = epochHashSpace U w N ∧
      dstMetaBase + 63 ≤ s.frontier ∧
      Fits w (dstMetaBase + offCompItems U w N)

/-- Functional specification and `≤ N + 40` cost bound for `writeCompParamsSubProg`. -/
theorem writeCompParamsSubProg_props {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((dstMetaBase, (w, N)), ((quotientBits U N, valBits V),
      (Nat.log 2 N, (Dynamic.logLogFactor N, epochHashSpace U w N))))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeCompParamsSubProg d)) ∧
    (Memory.spec 0).clientResult s (writeCompParamsSubProg d) = offCompItems U w N ∧
    ((Memory.spec 0).clientState s (writeCompParamsSubProg d)).frontier = s.frontier ∧
    (∀ i : Fin 36,
      ((Memory.spec 0).clientState s (writeCompParamsSubProg d)).mem
        (dstMetaBase + offCompParams + i.val) = mkCompParams U V w N i) ∧
    (∀ a, ¬(dstMetaBase + offCompParams ≤ a ∧ a < dstMetaBase + offScratch) →
      ((Memory.spec 0).clientState s (writeCompParamsSubProg d)).mem a = s.mem a) ∧
    memoryCost (writeCompParamsSubProg d) s ≤ N + 40 := by
  intro d
  obtain ⟨_, hvD, hresD, hfrD, hmD, hframeD, hcD⟩ :=
    writeCompScalesGmDProg_spec (V := V) (s := s) hw hN hNU hU hV h63 hfit_dst
  set sD := (Memory.spec 0).clientState s
    (writeCompScalesGmDProg ((dstMetaBase, N), (Nat.log 2 N, Dynamic.logLogFactor N)))
  obtain ⟨hv_mw, hst_mw, hres_mw, hc_mw⟩ :=
    computeMetaWordsProg_spec (s := sD) hw hN hNU hU hfit_dst
  obtain ⟨_, hvAB, hresAB, hfrAB, hmAB, hframeAB, hcAB⟩ :=
    writeCompABProg_spec hw hN hNU hU hV (hfrD.symm ▸ h63) hfit_dst
  obtain ⟨_, hvC, hresC, hfrC, hmC, hframeC, hcC⟩ :=
    writeCompSubCProg_spec hw hN hNU hU hV (hfrAB.symm ▸ hfrD.symm ▸ h63) hfit_dst
  obtain ⟨_, hvE, hfrE, hmE, hframeE, hcE⟩ :=
    writeCompSubEProg_spec (V := V) hw hNU hU hV
      (hfrC.symm ▸ hfrAB.symm ▸ hfrD.symm ▸ h63) hfit_dst
  dsimp only [d, writeCompParamsSubProg, offCompParams, offScratch]
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', hresD]
  dsimp only
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', hst_mw, hres_mw]
  dsimp only
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', hresAB, validHistory_bind', StateTransitionSpec.clientState_bind,
    prog_clientResult_bind, Realization.memoryCost_bind', hresC, validHistory_bind',
    StateTransitionSpec.clientState_bind, prog_clientResult_bind, Realization.memoryCost_bind',
    StateTransitionSpec.clientState_pure, prog_clientResult_pure, memoryCost_pure, hc_mw, hcAB,
    hcC, hcE]
  refine ⟨⟨hvD, hv_mw, hvAB, hvC, hvE, trivial⟩, rfl, by rw [hfrE, hfrC, hfrAB, hfrD],
    fun ⟨j, hj⟩ => ?_, fun a ha => ?_, by omega⟩
  · dsimp only
    by_cases hj16 : j < 16
    · rw [hframeE _ (by omega), hframeC _ (by omega)]; exact hmAB j hj16
    · by_cases hj24 : j < 24
      · rw [hframeE _ (by omega)]
        have hC := hmC (j - 16) (by omega)
        rw [show dstMetaBase + 43 + (j - 16) = dstMetaBase + 27 + j by omega] at hC
        exact hC.trans (congrArg _ (Fin.ext (by dsimp only; omega)))
      · by_cases hj32 : j < 32
        · rw [hframeE _ (by omega), hframeC _ (by omega), hframeAB _ (by omega)]
          have hD := hmD (j - 24) (by omega)
          rw [show dstMetaBase + 51 + (j - 24) = dstMetaBase + 27 + j by omega] at hD
          exact hD.trans (congrArg _ (Fin.ext (by dsimp only; omega)))
        · have hE := hmE (j - 32) (by omega)
          rw [show dstMetaBase + 59 + (j - 32) = dstMetaBase + 27 + j by omega] at hE
          exact hE.trans (congrArg _ (Fin.ext (by dsimp only; omega)))
  · rw [hframeE a (by omega), hframeC a (by omega), hframeAB a (by omega), hframeD a (by omega)]

/-- `writeCompParamsSubProg` compiles via `RealizesBounded .exact`. -/
theorem realizesBounded_writeCompParamsSub :
    RealizesBounded .exact writeCompParamsSubProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ))
      WriteCompParamsSubPre (fun _ _ => 0) := by
  have hD := realizesBounded_writeCompScalesGmD
  have hmw := realizesBounded_computeMetaWords
  have hAB := realizesBounded_writeCompAB
  have hC := realizesBounded_writeCompSubC
  have hE := realizesBounded_writeCompSubE
  realize
  all_goals (
    rcases d with ⟨⟨dstMetaBase, ⟨wVal, N⟩⟩, ⟨⟨qBitsVal, vBits⟩, ⟨logN, ⟨llf, hSpace⟩⟩⟩⟩
    obtain ⟨U, V, hw, hN, hNU, hU, hV, hwVal, rfl, rfl, rfl, rfl, rfl, h63, hfit_dst⟩ := h
    subst wVal
    dsimp only at *
    have hfit63 : Fits w (dstMetaBase + 63) := fits_add_of_fits_offCompItems hfit_dst (by decide))
  all_goals try exact hfit63.of_le (by omega)
  · exact ⟨U, hw, hN, hNU, hU, rfl, rfl, h63, hfit_dst⟩
  all_goals (
    obtain ⟨_, _, hresD, hfrD, _, _, _⟩ :=
      writeCompScalesGmDProg_spec (V := V) (s := s) hw hN hNU hU hV h63 hfit_dst
    rw [hresD]; dsimp only)
  · exact ⟨U, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfit_dst⟩
  all_goals (
    set sD := (Memory.spec 0).clientState s
      (writeCompScalesGmDProg ((dstMetaBase, N), (Nat.log 2 N, Dynamic.logLogFactor N)))
    obtain ⟨_, hst_mw, hres_mw, _⟩ := computeMetaWordsProg_spec (s := sD) hw hN hNU hU hfit_dst
    rw [hst_mw, hres_mw]; dsimp only)
  · exact ⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hfrD.symm ▸ h63, hfit_dst⟩
  all_goals (
    obtain ⟨_, _, hresAB, hfrAB, _, _, _⟩ :=
      writeCompABProg_spec (s := sD) hw hN hNU hU hV (hfrD.symm ▸ h63) hfit_dst
    rw [hresAB])
  · exact ⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hfrAB.symm ▸ hfrD.symm ▸ h63, hfit_dst⟩
  · obtain ⟨_, _, hresC, hfrC, _, _, _⟩ :=
      writeCompSubCProg_spec hw hN hNU hU hV (hfrAB.symm ▸ hfrD.symm ▸ h63) hfit_dst
    rw [hresC]
    exact ⟨U, dstMetaBase, N, rfl, hfrC.symm ▸ hfrAB.symm ▸ hfrD.symm ▸ h63, hfit_dst⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux
