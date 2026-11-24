/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
-- Unfolds `compQOffsetProg` and `packedOffsetProg` in `Accessors` for `validProg_compItemWordsGen`.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Compacted Item-Word Evaluation and Feistel Quotient Extraction

Implements `compItemWordsGenProg` and `compExtractQuotGenProg` in `Memory.Prog` (`¬ReadsWidth`),
together with their `RealizesBounded .exact` and `ValidProg w 0` certificates.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compItemWordsGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompItemWordsPre`:
  overflow-free evaluation of `compactedItemWords U V w N m` and its precondition.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compExtractQuotGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompExtractQuotPre`:
  Feistel key-quotient extraction in `Memory.Prog` and its precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compactedItemWords_eq_wOffQ_add`:
  overflow-free decomposition of `compactedItemWords` via `wOffQ` and `bOffQ`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compItemWordsGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compItemWordsGen`:
  `RealizesBounded .exact` and `ValidProg w 0` certificates for `compItemWordsGenProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.realizesBounded_compExtractQuotGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_compExtractQuotGen`:
  `RealizesBounded .exact` and `ValidProg w 0` certificates for `compExtractQuotGenProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure StateTransitionSpec.clientResult_map
  StateTransitionSpec.fst_snd_runClient_map
attribute [local simp] Realization.memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-- Exact overflow-free decomposition of `compactedItemWords U V w N m` in terms of `wOffQ` and
`bOffQ` for all `0 < w`. -/
theorem compactedItemWords_eq_wOffQ_add {U V w N m : ℕ} (hw : 0 < w) :
    compactedItemWords U V w N m =
      wOffQ (quotientBits U N) (valBits V) w m +
        (if bOffQ (quotientBits U N) (valBits V) w m = 0 then 2 else 3) := by
  unfold compactedItemWords
  have hid := wOffQ_mul_add_bOffQ (q_bits := quotientBits U N) (v_bits := valBits V) (w := w)
    (d := m)
  have hb_lt : bOffQ (quotientBits U N) (valBits V) w m < w := bOffQ_lt hw
  rw [← hid]
  set W := wOffQ (quotientBits U N) (valBits V) w m
  set B := bOffQ (quotientBits U N) (valBits V) w m
  split_ifs with hB0
  · have heq : W * w + B + w - 1 = (w - 1) + W * w := by omega
    rw [heq, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega : w - 1 < w), Nat.zero_add]
  · have hB_pos : 0 < B := Nat.pos_of_ne_zero hB0
    have heq : W * w + B + w - 1 = (B - 1) + (W + 1) * w := by
      rw [Nat.add_one_mul]; omega
    rw [heq, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega : B - 1 < w), Nat.zero_add]

/-- Evaluate `compactedItemWords U V w N m` overflow-free in `Memory.Prog` (`¬ReadsWidth`). -/
def compItemWordsGenProg : CompParams × ℕ → Memory.Prog ℕ
  | (cp, m) => do
    let q_bits ← pure (cpQuotBits cp)
    let v_bits ← pure (cpValBits cp)
    let wVal ← pure (cpW cp)
    let wb ← compQOffsetProg (((q_bits, v_bits), wVal), m)
    let z0 ← pure 0
    if wb.2 = z0 then
      pure (wb.1 + 2)
    else
      pure (wb.1 + 3)

@[simp] theorem clientResult_compItemWordsGenProg {U V w N m : ℕ} (hw : 0 < w)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (compItemWordsGenProg (mkCompParams U V w N, m)) =
      compactedItemWords U V w N m := by
  rw [compactedItemWords_eq_wOffQ_add hw]
  dsimp only [compItemWordsGenProg, cpQuotBits_mk, cpValBits_mk, cpW_mk]
  simp only [pure_bind, prog_clientResult_bind, clientResult_compQOffsetProg]
  split_ifs <;> rfl

theorem clientState_compItemWordsGenProg (d : CompParams × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compItemWordsGenProg d) = s := by
  rcases d with ⟨cp, m⟩
  unfold StateTransitionSpec.clientState
  dsimp only [compItemWordsGenProg]; simp only [pure_bind, prog_runClient_state_bind,
    StateTransitionSpec.clientState, runClient_state_compQOffsetProg]
  split_ifs <;> rfl

@[simp] theorem runClient_state_compItemWordsGenProg (d : CompParams × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compItemWordsGenProg d))) = s :=
  clientState_compItemWordsGenProg d s

@[simp] theorem memoryCost_compItemWordsGenProg (d : CompParams × ℕ) (s : Memory.State) :
    memoryCost (compItemWordsGenProg d) s = 0 := by
  rcases d with ⟨cp, m⟩
  dsimp only [compItemWordsGenProg]; simp only [pure_bind, Realization.memoryCost_bind',
    memoryCost_compQOffsetProg, zero_add]
  split_ifs <;> rfl

/-- Precondition for `compItemWordsGenProg`, independent of `s.frontier`. -/
@[expose] def CompItemWordsPre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, m), _s =>
    ∃ U V N,
      0 < w ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      Fits w (wOffQ (quotientBits U N) (valBits V) w m + 3)

theorem realizesBounded_compItemWordsGen :
    RealizesBounded .exact compItemWordsGenProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := ℕ))
      CompItemWordsPre (fun _ _ => 0) := by
  have hqo := realizesBounded_compQOffset
  realize
  all_goals (
    rcases d with ⟨cp, m⟩
    obtain ⟨U, V, N, hw, _hnU, hU, hV, rfl, hfit⟩ := h
    have hq : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU.le
    have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
    simp only [cpQuotBits_mk, cpValBits_mk, cpW_mk, clientResult_compQOffsetProg] at *)
  all_goals try exact ⟨hw, rfl, hq, hv, hfit.of_le (by omega)⟩
  all_goals exact hfit.of_le (by omega)

theorem validProg_compItemWordsGen {w : ℕ} (d : CompParams × ℕ) (s : Memory.State) :
    ValidProg w 0 s (compItemWordsGenProg d) := by
  rcases d with ⟨cp, m⟩
  intro _; dsimp only [compItemWordsGenProg, compQOffsetProg, packedOffsetProg]
  simp only [pure_bind]
  split_ifs <;> trivial

/-- Extract the Feistel key quotient `keyQuotient (bucketBits N) u = u >>> cpBucketBits cp`
in `Memory.Prog` (`¬ReadsWidth`). -/
@[expose] def compExtractQuotGenProg : CompParams × ℕ → Memory.Prog ℕ
  | (cp, u) => pure (u >>> cpBucketBits cp)

@[simp] theorem clientResult_compExtractQuotGenProg (U V w N u : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (compExtractQuotGenProg (mkCompParams U V w N, u)) =
      keyQuotient (bucketBits N) u := by
  simp [compExtractQuotGenProg, keyQuotient, Nat.shiftRight_eq_div_pow]

theorem clientState_compExtractQuotGenProg (d : CompParams × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compExtractQuotGenProg d) = s := by
  rcases d with ⟨cp, u⟩; rfl

@[simp] theorem runClient_state_compExtractQuotGenProg (d : CompParams × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compExtractQuotGenProg d))) = s :=
  clientState_compExtractQuotGenProg d s

@[simp] theorem memoryCost_compExtractQuotGenProg (d : CompParams × ℕ) (s : Memory.State) :
    memoryCost (compExtractQuotGenProg d) s = 0 := by
  rcases d with ⟨cp, u⟩; rfl

/-- Precondition for `compExtractQuotGenProg`. -/
@[expose] def CompExtractQuotPre (w : ℕ) : CompParams × ℕ → Memory.State → Prop
  | (cp, u), _s => Fits w u ∧ Fits w (cpBucketBits cp)

theorem realizesBounded_compExtractQuotGen :
    RealizesBounded .exact compExtractQuotGenProg
      (WordEncoding.encode (α := CompParams × ℕ)) (WordEncoding.encode (α := ℕ))
      CompExtractQuotPre (fun _ _ => 0) := by
  realize

theorem validProg_compExtractQuotGen {w : ℕ} (d : CompParams × ℕ) (s : Memory.State) :
    ValidProg w 0 s (compExtractQuotGenProg d) :=
  fun _ => trivial

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
