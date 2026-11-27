/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.ExecCtx
public import CslibFrontier.Computability.WordRAM.Resizable.Randomized
public import CslibFrontier.DataStructure.WordRAM.Resizable.StateTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# In-Epoch Operational Dispatcher on the Resizable Word RAM

This module formalizes the in-epoch operational dispatcher of the resizable succinct dynamic
dictionary on the word-granular **Resizable Word RAM** (`Cslib.WordRAM.Resizable`), wiring the
`RealizesBounded .exact` (`¬ReadsWidth`) subroutines from `Accessors.lean`, `SlotOps.lean`,
`BucketOps.lean`, and `RuntimeReducedKWise.lean` into parameter-free native `RCode .exact rEpoch`
operational dispatchers:

1. **Parameter-Free Native Dispatchers (`inEpochQueryCode`, `inEpochInsertCode`,
   `inEpochDeleteCode`, `inEpochOpCode`)**:
   Relocatable `RCode .exact rEpoch` programs independent of `(U, V, w, N, n, base)`:
   * `inEpochQueryCode`: reads `n` from `base + 6`, returns `none` in `O(1)` steps when `n = 0`,
     and otherwise loads `HashParams`/`CompParams` from `[base + 8, base + 63)`, reconstructs
     `x.frontier` into `rFr`, evaluates `h_q`, and runs `compQueryWithHashGenProg`;
   * `inEpochInsertCode`: searches `(b, m)` via `compInsertSearchWithHashGenProg`, updates the
     existing slot in place via `compWritePhysValGenProg` on a hit, and on a miss grows the item
     stream by `Δ ≤ 2` zeroed words via `growZeroCode`, appends the new slot via
     `compInsertAppendNewGenProg`, and increments `n` at `base + 6`;
   * `inEpochDeleteCode`: returns immediately when `n = 0`, and otherwise executes two-phase
     deletion (`compDeletePrepWithHashGenProg`, second hash evaluation on `q_last`, and
     `compDeleteFinishWithHashGenProg`), shrinking the item stream by `Δ ≤ 2` words via
     `shrinkCode` and decrementing `n` at `base + 6` when `found = 1`;
   * `inEpochOpCode`: unified per-operation dispatcher branching on `rTag`.
2. **Operational Invariant, `1 · OPT` Peak Space, and Expected Amortized $O(1)$ Cost**:
   * `inEpochOpCode_active_demonicExec` and `inEpochOpCode_demonicExec`: preserve
     `CompactedSplitRep` (with the same latent seed `θ`) and `CompactedRep` across every
     `InEpochValid` operation;
   * `inEpochPeakWords_le_succinctWords` and `inEpochOpCode_peakFrontierLe`: bound the hardware
     word frontier at every intermediate step by `base + Dynamic.succinctWords 1355 441 U V w
     (max n n')` (`1 · OPT`, never `2 · OPT`);
   * `inEpochOpCode_execRCodeDist` and `inEpochOpCode_expected_amortized`: lift execution to
     `ExecRCodeDist` and prove a parameter-free $O(1)$ expected amortized instruction bound
     `inEpochCharge` under a uniform `QuotHashSeed U N`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.rEpoch`: parameter-free register count.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.inEpochQueryCode`,
  `inEpochInsertCode`, `inEpochDeleteCode`, `inEpochOpCode`: parameter-free `RCode .exact rEpoch`
  operational dispatchers.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpochValid`, `inEpochPeakWords`,
  `inEpochPotential`, `inEpochBaseCharge`, `inEpochCharge`: admissibility, peak-space, potential,
  and parameter-free $O(1)$ charge definitions.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.encode`, `argMatch`, `decode`:
  ABI register conventions for `Dynamic.Op U`.

## Main results

* `not_readsWidth_inEpochOpCode`: `inEpochOpCode` does not inspect the ambient word width `w`.
* `inEpochPeakWords_le_succinctWords`: `inEpochPeakWords` is bounded by `1 · OPT` succinct words.
* `inEpochOpCode_active_demonicExec`, `inEpochOpCode_demonicExec`: deterministic `RDemonicExec`
  preserving `CompactedSplitRep` / `CompactedRep` with `O(1 + probeExcess)` potential-amortized
  step bound.
* `inEpochOpCode_execRCodeDist`, `inEpochOpCode_peakFrontierLe`: non-vacuous distributional
  execution and stepwise `1 · OPT` `PeakFrontierLe` certificates.
* `inEpochOpCode_expected_amortized`: uniform-seed $O(1)$ expected amortized instruction bound.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select*, SODA 2026,
  Section 5.1][KuszmaulLiangZhou2026]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
open Cslib.Probability
open scoped BigOperators ENNReal


/-! ## Section 1: Native `RCode .exact rEpoch` Operational Dispatchers -/

/-- In-epoch query operational code (`RCode .exact rEpoch`, parameter-free):
loads `n` from `base + 6`, returns `none` when `n = 0`, and otherwise runs
`compQueryWithHashGenProg` to write `(rOutTag, rOutVal)`. -/
noncomputable def inEpochQueryCode : RCode .exact rEpoch :=
  .seq (loadAtOffCode rBase rCnt rCur 6) <|
  .seq (.op (.const rZero 0)) <|
  .branch (.eq rCnt rZero)
    (.seq (.op (.const rOutTag 0)) (.op (.const rOutVal 0)))
    (.seq loadActiveCtxCode
      (.seq evalKeyHashCode
            (RCode.ofCode (wQuery.code rFr srcKeyHashOp tmpQuery))))

private noncomputable def inEpochInsertMissTailCode : RCode .exact rEpoch :=
  .seq (RCode.ofCode (wGrowDelta.code rFr srcGrowDelta tmpGrowDelta)) <|
  .seq (growZeroCode rK rRes rCur rIdx rZero rOne) <|
  .seq (.op (.exactBin .add rFr rFr rK)) <|
  .seq (RCode.ofCode (wInsAppend.code rFr srcInsAppend tmpInsAppend)) <|
  .seq (.op (.const rOne 1)) <|
  .seq (.op (.exactBin .add rCnt rCnt rOne))
       (storeAtOffCode rBase rCnt rCur 6)

/-- In-epoch insert operational code (`RCode .exact rEpoch`, parameter-free):
searches `(b, m)` via `compInsertSearchWithHashGenProg`, overwrites the value in place on a hit,
and on a miss grows `[0, frontier)` by `Δ ≤ 2` zeroed words (`growZeroCode`), appends the new
entry (`compInsertAppendNewGenProg`), and increments `n` at `base + 6`. -/
noncomputable def inEpochInsertCode : RCode .exact rEpoch :=
  .seq (loadAtOffCode rBase rCnt rCur 6) <|
  .seq loadActiveCtxCode <|
  .seq evalKeyHashCode <|
  .seq (RCode.ofCode (wInsSearch.code rFr srcKeyHashOp tmpInsSearch)) <|
  .seq (.op (.const rOne 1)) <|
  .branch (.eq rFound rOne)
    (RCode.ofCode (wWriteVal.code rFr srcWriteVal tmpWriteVal))
    inEpochInsertMissTailCode

private noncomputable def inEpochDeleteHitTailCode : RCode .exact rEpoch :=
  .seq (RCode.ofCode (wShrinkDelta.code rFr srcShrinkDelta tmpShrinkDelta)) <|
  .seq (shrinkCode rK rIdx rZero rOne) <|
  .seq (.op (.const rOne 1)) <|
  .seq (.op (.exactBin .sub rCnt rCnt rOne))
       (storeAtOffCode rBase rCnt rCur 6)

/-- In-epoch delete operational code (`RCode .exact rEpoch`, parameter-free):
no-op when `n = 0`, and otherwise runs two-phase deletion (`compDeletePrepWithHashGenProg`,
second hash evaluation on `q_last`, and `compDeleteFinishWithHashGenProg`), shrinking
`[0, frontier)` by `Δ ≤ 2` words (`shrinkCode`) and decrementing `n` at `base + 6` on a hit. -/
noncomputable def inEpochDeleteCode : RCode .exact rEpoch :=
  .seq (loadAtOffCode rBase rCnt rCur 6) <|
  .seq (.op (.const rZero 0)) <|
  .branch (.eq rCnt rZero)
    (.op (.copy rZero rZero))
    (.seq loadActiveCtxCode <|
     .seq evalKeyHashCode <|
     .seq (.op (.copy rHq rHashOut)) <|
     .seq (RCode.ofCode (wDelPrep.code rFr srcDelPrep tmpDelPrep)) <|
     .seq (RCode.ofCode (wEvalHash.code rFr srcEvalHash tmpEvalHash)) <|
     .seq (RCode.ofCode (wDelFin.code rFr srcDelFin tmpDelFin)) <|
     .seq (.op (.const rOne 1)) <|
     .branch (.eq rFound rOne)
       inEpochDeleteHitTailCode
       (.op (.copy rZero rZero)))

/-- Unified parameter-free in-epoch operational dispatcher (`RCode .exact rEpoch`):
branches on `rTag` between `inEpochQueryCode` (`0`), `inEpochInsertCode` (`1`), and
`inEpochDeleteCode` (`2`). -/
noncomputable def inEpochOpCode : RCode .exact rEpoch :=
  .seq (.op (.const rZero 0)) <|
  .seq (.op (.const rOne 1)) <|
  .branch (.eq rTag rZero)
    inEpochQueryCode
    (.branch (.eq rTag rOne)
      inEpochInsertCode
      inEpochDeleteCode)


/-! ## Section 2: Width-Independence (`¬inEpochOpCode.ReadsWidth`) -/

/-- `inEpochQueryCode` does not inspect the ambient word width `w`. -/
theorem not_readsWidth_inEpochQueryCode : ¬inEpochQueryCode.ReadsWidth := by
  have h4 : ¬(RCode.ofCode (wQuery.code rFr srcKeyHashOp tmpQuery)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wQuery.code_spec rFr srcKeyHashOp tmpQuery
      tmpQuery_inj srcKeyHashOp_ne_tmpQuery tmpQuery_ne_rFr srcKeyHashOp_ne_rFr).1
  simp [inEpochQueryCode, RCode.ReadsWidth, Op.ReadsWidth, not_readsWidth_loadAtOffCode,
    not_readsWidth_loadActiveCtxCode, not_readsWidth_evalKeyHashCode, h4]

private theorem not_readsWidth_inEpochInsertMissTailCode :
    ¬inEpochInsertMissTailCode.ReadsWidth := by
  have h6 : ¬(RCode.ofCode (wGrowDelta.code rFr srcGrowDelta tmpGrowDelta)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wGrowDelta.code_spec rFr srcGrowDelta tmpGrowDelta
      tmpGrowDelta_inj srcGrowDelta_ne_tmp tmpGrowDelta_ne_rFr srcGrowDelta_ne_rFr).1
  have h7 : ¬(RCode.ofCode (wInsAppend.code rFr srcInsAppend tmpInsAppend)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wInsAppend.code_spec rFr srcInsAppend tmpInsAppend
      tmpInsAppend_inj srcInsAppend_ne_tmp tmpInsAppend_ne_rFr srcInsAppend_ne_rFr).1
  simp [inEpochInsertMissTailCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    growZeroCode_not_readsWidth, not_readsWidth_storeAtOffCode, h6, h7]

/-- `inEpochInsertCode` does not inspect the ambient word width `w`. -/
theorem not_readsWidth_inEpochInsertCode : ¬inEpochInsertCode.ReadsWidth := by
  have h4 : ¬(RCode.ofCode (wInsSearch.code rFr srcKeyHashOp tmpInsSearch)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wInsSearch.code_spec rFr srcKeyHashOp tmpInsSearch
      tmpInsSearch_inj srcKeyHashOp_ne_tmpInsSearch tmpInsSearch_ne_rFr srcKeyHashOp_ne_rFr).1
  have h5 : ¬(RCode.ofCode (wWriteVal.code rFr srcWriteVal tmpWriteVal)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wWriteVal.code_spec rFr srcWriteVal tmpWriteVal
      tmpWriteVal_inj srcWriteVal_ne_tmp tmpWriteVal_ne_rFr srcWriteVal_ne_rFr).1
  simp [inEpochInsertCode, RCode.ReadsWidth, Op.ReadsWidth,
    not_readsWidth_loadAtOffCode, not_readsWidth_loadActiveCtxCode,
    not_readsWidth_evalKeyHashCode, not_readsWidth_inEpochInsertMissTailCode, h4, h5]

private theorem not_readsWidth_inEpochDeleteHitTailCode :
    ¬inEpochDeleteHitTailCode.ReadsWidth := by
  have h6 : ¬(RCode.ofCode (wShrinkDelta.code rFr srcShrinkDelta tmpShrinkDelta)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wShrinkDelta.code_spec rFr srcShrinkDelta tmpShrinkDelta
      tmpShrinkDelta_inj srcShrinkDelta_ne_tmp tmpShrinkDelta_ne_rFr srcShrinkDelta_ne_rFr).1
  simp [inEpochDeleteHitTailCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    shrinkCode_not_readsWidth, not_readsWidth_storeAtOffCode, h6]

/-- `inEpochDeleteCode` does not inspect the ambient word width `w`. -/
theorem not_readsWidth_inEpochDeleteCode : ¬inEpochDeleteCode.ReadsWidth := by
  have h3 : ¬(RCode.ofCode (wEvalHash.code rFr srcEvalHash tmpEvalHash)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wEvalHash.code_spec rFr srcEvalHash tmpEvalHash
      tmpEvalHash_inj srcEvalHash_ne_tmp tmpEvalHash_ne_rFr srcEvalHash_ne_rFr).1
  have h4 : ¬(RCode.ofCode (wDelPrep.code rFr srcDelPrep tmpDelPrep)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wDelPrep.code_spec rFr srcDelPrep tmpDelPrep
      tmpDelPrep_inj srcDelPrep_ne_tmp tmpDelPrep_ne_rFr srcDelPrep_ne_rFr).1
  have h5 : ¬(RCode.ofCode (wDelFin.code rFr srcDelFin tmpDelFin)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wDelFin.code_spec rFr srcDelFin tmpDelFin
      tmpDelFin_inj srcDelFin_ne_tmp tmpDelFin_ne_rFr srcDelFin_ne_rFr).1
  simp [inEpochDeleteCode, RCode.ReadsWidth, Op.ReadsWidth,
    not_readsWidth_loadAtOffCode, not_readsWidth_loadActiveCtxCode,
    not_readsWidth_evalKeyHashCode, not_readsWidth_inEpochDeleteHitTailCode, h3, h4, h5]

/-- `inEpochOpCode` does not inspect the ambient word width `w` (`¬inEpochOpCode.ReadsWidth`). -/
theorem not_readsWidth_inEpochOpCode : ¬inEpochOpCode.ReadsWidth := by
  simp [inEpochOpCode, RCode.ReadsWidth, Op.ReadsWidth, not_readsWidth_inEpochQueryCode,
    not_readsWidth_inEpochInsertCode, not_readsWidth_inEpochDeleteCode]


/-! ## Section 3: Per-Operation Execution and Main Certificates -/

private theorem fits_four_add_compactedItemWords {U V w N m base : ℕ}
    (hm : 0 < m) (hfit : Fits w (base + compactedEpochWords U V w N m)) :
    Fits w (4 + compactedItemWords U V w N m) := by
  have hce : compactedEpochWords U V w N m =
      offCompItems U w N + compactedItemWords U V w N m := by
    unfold compactedEpochWords; rw [ite_eq_right hm.ne']
  have hoff : 225 ≤ offCompItems U w N := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
  rw [hce] at hfit
  exact hfit.of_le (by omega)

private theorem insert_miss_tail_steps_le {k c_app pot_y pot₃ : ℕ} (hk : k ≤ 2)
    (happ : c_app + pot_y ≤ (98 * inEpochFactor) * pot₃ + 201 * inEpochFactor) :
    (inEpochFactor + ((5 * k + 6) + (1 + (c_app + (1 + (1 + 3)))))) + pot_y ≤
      (98 * inEpochFactor) * pot₃ + 202 * inEpochFactor + 22 := by
  omega

private theorem delete_hit_tail_steps_le {k : ℕ} (hk : k ≤ 2) :
    inEpochFactor + ((4 * k + 5) + (1 + (1 + 3))) ≤ inEpochFactor + 18 := by
  omega

private theorem insert_hit_steps_le {c_sr c_wv pot pe : ℕ}
    (hsr : c_sr ≤ 33 * inEpochFactor + (12 * inEpochFactor) * pe)
    (hwv : c_wv ≤ 9 * inEpochFactor) :
    (3 + ((inEpochFactor + 172) + (45207 * inEpochFactor + (c_sr + (1 + (c_wv + 1)))))) + pot ≤
      pot + (inEpochBaseCharge - 10) + (12 * inEpochFactor) * pe := by
  have hf := one_le_inEpochFactor
  unfold inEpochBaseCharge; omega

private theorem insert_miss_steps_le {c_sr steps_m pot_y pot_x pe : ℕ}
    (hsr : c_sr ≤ 33 * inEpochFactor + (12 * inEpochFactor) * pe)
    (hm : steps_m + pot_y ≤ pot_x + 202 * inEpochFactor + 22) :
    (3 + ((inEpochFactor + 172) + (45207 * inEpochFactor + (c_sr + (1 + (steps_m + 2)))))) +
        pot_y ≤
      pot_x + (inEpochBaseCharge - 10) + (12 * inEpochFactor) * pe := by
  have hf := one_le_inEpochFactor
  unfold inEpochBaseCharge; omega

private theorem delete_hit_steps_le {c_prep c_fin steps_h pot_y pot_x pe : ℕ}
    (hh : steps_h ≤ inEpochFactor + 18)
    (hdel : c_prep + c_fin + pot_y ≤ pot_x + 356 * inEpochFactor + (12 * inEpochFactor) * pe) :
    (3 + (1 + (((inEpochFactor + 172) + (45207 * inEpochFactor +
      (1 + (c_prep + (45206 * inEpochFactor + (c_fin + (1 + (steps_h + 1)))))))) + 2))) + pot_y ≤
      pot_x + (inEpochBaseCharge - 10) + (12 * inEpochFactor) * pe := by
  have hf := one_le_inEpochFactor
  unfold inEpochBaseCharge; omega

private theorem delete_miss_steps_le {c_prep c_fin pot_y pot_x pe : ℕ}
    (hdel : c_prep + c_fin + pot_y ≤ pot_x + 356 * inEpochFactor + (12 * inEpochFactor) * pe) :
    (3 + (1 + (((inEpochFactor + 172) + (45207 * inEpochFactor +
      (1 + (c_prep + (45206 * inEpochFactor + (c_fin + (1 + (1 + 2)))))))) + 2))) + pot_y ≤
      pot_x + (inEpochBaseCharge - 10) + (12 * inEpochFactor) * pe := by
  have hf := one_le_inEpochFactor
  unfold inEpochBaseCharge; omega

private theorem inEpochInsertMissTailCode_exec {U V w N n n_init base L_peak : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} (u : Fin U) (v : ℕ)
    {s_fix₃ : Memory.State} {x₃ x₅ : RData rEpoch}
    (hx₅b : x₅.Bounded w) (hn : 0 < n) (hn_lt_N : n < N)
    (henv₃ : CompEpochEnv U V w N base (base + offCompItems U w N) n ⟨x₃.mem, x₃.frontier⟩)
    (hfit1 : Fits w 1) (hfit6 : Fits w 6)
    (hL : base + compactedEpochWords U V w N n ≤ L_peak)
    (hL_peak : base + compactedEpochWords U V w N (n + 1) ≤ L_peak)
    (hfit_peak : Fits w (base + compactedEpochWords U V w N (n + 1)))
    (hsplit₃ : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x₃.mem, x₃.frontier⟩)
    (hinv₃ : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix₃)
    (htot₃ : totalSlots N (compGmAt base U w N x₃.mem) = n)
    (hcpl₃ : FixedCoupled base (base + offCompItems U w N) U V w N s_fix₃ ⟨x₃.mem, x₃.frontier⟩)
    (hms₅ : memoryState rFr x₅.toData = ⟨x₃.mem, x₃.frontier⟩)
    (hx₅_ff : x₅.frontier = base + compactedEpochWords U V w N n)
    (hx₅_fr : x₅.regs rFr = x₅.frontier)
    (hx₅_base : x₅.regs rBase = base) (hx₅_cnt : x₅.regs rCnt = n)
    (hx₅_item : x₅.regs rItemBase = base + offCompItems U w N)
    (hx₅_b : x₅.regs rBucket = feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val)
    (hx₅_m : x₅.regs rMicro = mOfSeed U N θ (keyQuotient (bucketBits N) u.val))
    (hx₅_u : x₅.regs rArgU = u.val) (hx₅_v : x₅.regs rArgV = v)
    (hx₅_cp : ∀ i : Fin 36, x₅.regs (cpReg i) = mkCompParams U V w N i)
    (hv_lt_V : v < V) (hvals' : Dictionary.ValuesBounded V (Function.update s_abs u (some v)))
    (hn'_eq : (Dictionary.dom (Function.update s_abs u (some v))).card = n + 1)
    (hhit : ((Memory.spec 0).clientResult s_fix₃
      (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val),
          keyQuotient (bucketBits N) u.val),
          mOfSeed U N θ (keyQuotient (bucketBits N) u.val)))).1.1 ≠ 1) :
    ∃ (y : RData rEpoch) (steps_m : ℕ),
      RDemonicExec w L_peak inEpochInsertMissTailCode x₅ steps_m (· = y) ∧
      y.Bounded w ∧
      y.frontier = base + compactedEpochWords U V w N (n + 1) ∧
      CompactedSplitRep base (base + offCompItems U w N) U V w N (n + 1) n_init θ
        (Function.update s_abs u (some v)) ⟨y.mem, y.frontier⟩ ∧
      y.regs rBase = base ∧
      (∀ addr < base, y.mem addr = x₃.mem addr) ∧
      steps_m + inEpochPotential U w N base y ≤
        (98 * inEpochFactor) * slotPotential N (compGmAt base U w N x₃.mem) +
          202 * inEpochFactor + 22 := by
  set b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
  set m := mOfSeed U N θ (keyQuotient (bucketBits N) u.val)
  have hce_pos1 : compactedEpochWords U V w N (n + 1) =
      offCompItems U w N + compactedItemWords U V w N (n + 1) := by
    unfold compactedEpochWords; simp
  have hce_pos0' : compactedEpochWords U V w N n =
      offCompItems U w N + compactedItemWords U V w N n := by
    unfold compactedEpochWords; rw [ite_eq_right hn.ne']
  have hfit_iw1 : Fits w (4 + compactedItemWords U V w N (n + 1)) :=
    fits_four_add_compactedItemWords (Nat.succ_pos n) hfit_peak
  have hin_gd : x₅.regs ∘ srcGrowDelta = WordEncoding.encode (mkCompParams U V w N, n) :=
    (regs_pairSrc (regs_cp_eq hx₅_cp) (regs_reg1_eq rCnt hx₅_cnt)).eq
  have hsafe_gd : CompGrowDeltaPre w (mkCompParams U V w N, n) (memoryState rFr x₅.toData) :=
    ⟨U, V, N, henv₃.pos_w, hn_lt_N, henv₃.le_U, henv₃.lt_pow_U, henv₃.le_pow_V, rfl, hfit_iw1⟩
  have hv_gd : (Memory.spec w).ValidHistory (memoryState rFr x₅.toData)
      ((Memory.spec w).clientHistory (memoryState rFr x₅.toData)
        (compGrowDeltaGenProg (mkCompParams U V w N, n))) :=
    validProg_compGrowDeltaGen _ _ ⟨wellFormed_memoryState hx₅b.1, Nat.zero_le _⟩
  have hnoalloc_gd : ((Memory.spec 0).clientState (memoryState rFr x₅.toData)
      (compGrowDeltaGenProg (mkCompParams U V w N, n))).frontier ≤ x₅.frontier := by
    rw [clientState_compGrowDeltaGenProg]; exact hx₅_fr.le
  obtain ⟨x₆, hex_gd, hx₆b, hx₆f, hm_gd, hout_gd, hframe_gd⟩ :=
    execWitness wGrowDelta factor_wGrowDelta_le rFr srcGrowDelta tmpGrowDelta
      tmpGrowDelta_inj srcGrowDelta_ne_tmp tmpGrowDelta_ne_rFr srcGrowDelta_ne_rFr
      (mkCompParams U V w N, n) hx₅b (hx₅_ff.le.trans hL)
      hin_gd hsafe_gd hv_gd hnoalloc_gd
  rw [memoryCost_compGrowDeltaGenProg, zero_add, mul_one] at hex_gd
  rw [clientState_compGrowDeltaGenProg] at hm_gd
  have hx₆m : x₆.mem = x₃.mem :=
    (congrArg Memory.State.mem hm_gd).trans (congrArg Memory.State.mem hms₅)
  have hx₆_ff : x₆.frontier = base + compactedEpochWords U V w N n := hx₆f.trans hx₅_ff
  have hx₆_fr : x₆.regs rFr = x₆.frontier := by
    have hfm := congrArg Memory.State.frontier hm_gd
    change x₆.regs rFr = x₅.regs rFr at hfm
    rw [hfm, hx₅_fr, hx₆f]
  set Δ := compactedItemWords U V w N (n + 1) - compactedItemWords U V w N n
  have hΔ_le2 : Δ ≤ 2 :=
    compactedItemWords_succ_sub_le_two henv₃.pos_w henv₃.lt_pow_U.le henv₃.le_pow_V
  have hx₆_k : x₆.regs rK = Δ := by
    have h0 := hout_gd 0
    rw [tmpGrowDelta_out, clientResult_compGrowDeltaGenProg henv₃.pos_w] at h0
    exact h0
  have hfr_plus_Δ : x₆.frontier + Δ = base + compactedEpochWords U V w N (n + 1) := by
    have hm_iw := compactedItemWords_mono (U := U) (V := V) (w := w) (N := N) (by omega : n ≤ n + 1)
    rw [hx₆_ff, hce_pos0', hce_pos1]
    dsimp only [Δ]; omega
  have hL_gz : x₆.frontier + x₆.regs rK ≤ L_peak := by
    rw [hx₆_k, hfr_plus_Δ]; exact hL_peak
  have hfit_gz : Fits w (x₆.frontier + x₆.regs rK) := by
    rw [hx₆_k, hfr_plus_Δ]; exact hfit_peak
  have hex_gz := growZeroCode_exec hx₆b rGrow_nodup hfit1 hL_gz hfit_gz
  set x₇ := growZeroPost rK rRes rCur rIdx rZero rOne x₆
  have hx₇b : x₇.Bounded w := growZeroPost_bounded hx₆b hfit1 hfit_gz
  have hx₇m : x₇.mem = x₃.mem := hx₆m
  have hx₇_ff : x₇.frontier = base + compactedEpochWords U V w N (n + 1) := by
    change x₆.frontier + x₆.regs rK = _
    rw [hx₆_k, hfr_plus_Δ]
  have hx₆_pres : ∀ reg, reg ≠ rFr → reg.val < 88 → reg ≠ rK → x₆.regs reg = x₅.regs reg :=
    fun reg h1 h88 hk => hframe_gd reg h1 (tmpGrowDelta_ne_reg h88 hk)
  have hx₇_fr_old : x₇.regs rFr = x₆.frontier := by
    simp [x₇, growZeroPost, hx₆_fr]
  have hx₇_k : x₇.regs rK = Δ := by
    simp [x₇, growZeroPost, hx₆_k]
  set x₈ := x₇.set rFr (base + compactedEpochWords U V w N (n + 1))
  have hex_add_fr := RDemonicExec.exactBin (f := .add) (d := rFr) (i := rFr) (j := rK)
    (w := w) (L_peak := L_peak) (x := x₇) (by rw [hx₇_ff]; exact hL_peak)
    (v := base + compactedEpochWords U V w N (n + 1))
    (by simp [BinOp.evalExact, hx₇_fr_old, hx₇_k, hfr_plus_Δ]) hfit_peak
  have hx₈b : x₈.Bounded w := hx₇b.set hfit_peak
  have hx₈_ff : x₈.frontier = base + compactedEpochWords U V w N (n + 1) := hx₇_ff
  have hms₈ : memoryState rFr x₈.toData = ⟨x₃.mem, base + compactedEpochWords U V w N (n + 1)⟩ :=
    Memory.State.ext hx₇m (by change x₈.regs rFr = _; simp [x₈, RData.set])
  set s_grown : Memory.State := ⟨x₃.mem, base + compactedEpochWords U V w N (n + 1)⟩
  have henv_grown : CompEpochEnv U V w N base (base + offCompItems U w N) (n + 1) s_grown :=
    ⟨henv₃.pos_w, henv₃.pos_N, henv₃.le_U, henv₃.lt_pow_U, henv₃.le_pow_V, le_rfl,
      by change _ ≤ base + compactedEpochWords U V w N (n + 1); rw [hce_pos1]; omega⟩
  obtain ⟨hpre_app, hfr_app, hcost_app, s_fix', hinv', hcpl'⟩ :=
    compInsertMiss_dict_spec (s := ⟨x₃.mem, x₃.frontier⟩) henv_grown rfl hinv₃ hcpl₃
      (htot₃.symm ▸ hn_lt_N) (by rw [htot₃]) u v hv_lt_V hhit
  set d_app := ((((mkCompParams U V w N, (base, base + offCompItems U w N)), (b, m)), (u.val, v)))
  have hx₈_unch : ∀ {c : Fin 88}, c.val < 32 →
      c ≠ 1 → c ≠ 7 → c ≠ 8 → c ≠ 9 → c ≠ 10 → c ≠ 11 → c ≠ 12 →
      x₈.regs (eReg c) = x₅.regs (eReg c) := fun {c} hc h1 h7 h8' h9 h10 h11 h12 => by
    simp only [x₈, x₇, growZeroPost, RData.set_regs,
      Function.update_of_ne (eReg_ne h1), Function.update_of_ne (eReg_ne h9),
      Function.update_of_ne (eReg_ne h10), Function.update_of_ne (eReg_ne h8'),
      Function.update_of_ne (eReg_ne h12), Function.update_of_ne (eReg_ne h11)]
    exact hx₆_pres (eReg c) (eReg_ne h1) (eReg_lt_88 c) (eReg_ne h7)
  have hx₈_cp : ∀ i : Fin 36, x₈.regs (cpReg i) = mkCompParams U V w N i := fun i => by
    simp only [x₈, x₇, growZeroPost, RData.set_regs,
      Function.update_of_ne (cpReg_ne_eReg (c := 1) i (by decide)),
      Function.update_of_ne (cpReg_ne_eReg (c := 9) i (by decide)),
      Function.update_of_ne (cpReg_ne_eReg (c := 10) i (by decide)),
      Function.update_of_ne (cpReg_ne_eReg (c := 8) i (by decide)),
      Function.update_of_ne (cpReg_ne_eReg (c := 12) i (by decide)),
      Function.update_of_ne (cpReg_ne_eReg (c := 11) i (by decide))]
    exact (hx₆_pres (cpReg i) (cpReg_ne_eReg i (by decide)) (cpReg_lt_88 i)
      (cpReg_ne_eReg i (by decide))).trans (hx₅_cp i)
  have hx₈_base : x₈.regs rBase = base :=
    (hx₈_unch (c := 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hx₅_base
  have hx₈_cnt : x₈.regs rCnt = n :=
    (hx₈_unch (c := 13) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hx₅_cnt
  have hx₈_item : x₈.regs rItemBase = base + offCompItems U w N :=
    (hx₈_unch (c := 14) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hx₅_item
  have hx₈_b : x₈.regs rBucket = b :=
    (hx₈_unch (c := 23) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hx₅_b
  have hx₈_m : x₈.regs rMicro = m :=
    (hx₈_unch (c := 24) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hx₅_m
  have hx₈_u : x₈.regs rArgU = u.val :=
    (hx₈_unch (c := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hx₅_u
  have hx₈_v : x₈.regs rArgV = v :=
    (hx₈_unch (c := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hx₅_v
  have hin_app : x₈.regs ∘ srcInsAppend = WordEncoding.encode d_app :=
    (regs_pairSrc
      (regs_pairSrc
        (regs_pairSrc (regs_cp_eq hx₈_cp)
          (regs_pairSrc (regs_reg1_eq rBase hx₈_base) (regs_reg1_eq rItemBase hx₈_item)))
        (regs_pairSrc (regs_reg1_eq rBucket hx₈_b) (regs_reg1_eq rMicro hx₈_m)))
      (regs_pairSrc (regs_reg1_eq rArgU hx₈_u) (regs_reg1_eq rArgV hx₈_v))).eq
  have hv_app : (Memory.spec w).ValidHistory (memoryState rFr x₈.toData)
      ((Memory.spec w).clientHistory (memoryState rFr x₈.toData)
        (compInsertAppendNewGenProg d_app)) :=
    validProg_compInsertAppendNewGen (hms₈ ▸ hpre_app)
      ⟨wellFormed_memoryState hx₈b.1, Nat.zero_le _⟩
  have hnoalloc_app : ((Memory.spec 0).clientState (memoryState rFr x₈.toData)
      (compInsertAppendNewGenProg d_app)).frontier ≤ x₈.frontier := by
    rw [hms₈, hfr_app.frontier_eq, hx₈_ff]
  obtain ⟨x₉, hex_app, hx₉b, hx₉f, hm_app, _, hframe_app⟩ :=
    execWitness wInsAppend factor_wInsAppend_le rFr srcInsAppend tmpInsAppend
      tmpInsAppend_inj srcInsAppend_ne_tmp tmpInsAppend_ne_rFr srcInsAppend_ne_rFr
      d_app hx₈b (hx₈_ff.le.trans hL_peak) hin_app
      (hms₈ ▸ hpre_app) hv_app hnoalloc_app
  rw [hms₈] at hm_app
  have hx₉_ff : x₉.frontier = base + compactedEpochWords U V w N (n + 1) := hx₉f.trans hx₈_ff
  have hx₉m_app : x₉.mem =
      ((Memory.spec 0).clientState s_grown (compInsertAppendNewGenProg d_app)).mem :=
    congrArg Memory.State.mem hm_app
  have hs9_eq : (⟨x₉.mem, x₉.frontier⟩ : Memory.State) =
      (Memory.spec 0).clientState s_grown (compInsertAppendNewGenProg d_app) :=
    Memory.State.ext hx₉m_app (by rw [hx₉_ff, hfr_app.frontier_eq])
  have hx₉_base : x₉.regs rBase = base :=
    (hframe_app rBase (eReg_ne (by decide)) (tmpInsAppend_ne_reg (eReg_lt_88 _))).trans hx₈_base
  have hx₉_cnt : x₉.regs rCnt = n :=
    (hframe_app rCnt (eReg_ne (by decide)) (tmpInsAppend_ne_reg (eReg_lt_88 _))).trans hx₈_cnt
  have hfit_n1 : Fits w (n + 1) :=
    lt_of_le_of_lt (by have := henv₃.le_U; omega : n + 1 ≤ U) henv₃.lt_pow_U
  set x₁₀ := x₉.set rOne 1
  set x₁₁ := x₁₀.set rCnt (n + 1)
  have hex_o2 := RDemonicExec.const (B := .exact) (d := rOne) (x := x₉)
    (hx₉_ff.le.trans hL_peak) hfit1
  have hex_inc := RDemonicExec.exactBin (f := .add) (d := rCnt) (i := rCnt) (j := rOne)
    (w := w) (L_peak := L_peak) (x := x₁₀)
    (show x₁₀.frontier ≤ L_peak from hx₉_ff.le.trans hL_peak)
    (v := n + 1)
    (by simp [BinOp.evalExact, x₁₀, RData.set, hx₉_cnt])
    hfit_n1
  have hx₁₁b : x₁₁.Bounded w := (hx₉b.set hfit1).set hfit_n1
  have hx₁₁_base : x₁₁.regs rBase = base := by
    simp [x₁₁, x₁₀, RData.set, hx₉_base]
  have h8_1 : 8 ≤ compactedEpochWords U V w N (n + 1) :=
    eight_le_compactedEpochWords U V w N (n + 1)
  obtain ⟨hex_st, hyb⟩ := storeAtOffCode_exec (rAddr := rBase) (rSrc := rCnt) (rTmp := rCur)
    (val := n + 1) hx₁₁b (show x₁₁.frontier ≤ L_peak from hx₉_ff.le.trans hL_peak)
    (eReg_ne (by decide)) (eReg_ne (by decide)) hx₁₁_base (by simp [x₁₁, RData.set]) hfit6
    (by simp only [x₁₁, x₁₀, RData.set_frontier, hx₉_ff]; omega)
  set y := (x₁₁.set rCur (base + 6)).write (base + 6) (n + 1)
  have hy_ff : y.frontier = base + compactedEpochWords U V w N (n + 1) := hx₉_ff
  have hy_base : y.regs rBase = base := by
    simp [y, RData.write, RData.set,
      hx₁₁_base]
  obtain ⟨hhdr9, hpar9, hhash9, hbelow9⟩ :=
    hdr_params_hash_of_opFrame (s := s_grown) (s' := ⟨x₉.mem, x₉.frontier⟩)
      hsplit₃.root_hdr hsplit₃.params_stored hsplit₃.hash_rep
      (by rw [hs9_eq]; exact hfr_app)
  obtain ⟨hsplit_y, hgm_y⟩ := update_hdr_n_preserves_split (n_new := n + 1)
    henv₃.pos_w hhdr9 hpar9 hhash9 hn'_eq hvals' hinv' (by rw [hs9_eq]; exact hcpl')
  have hcost_app_mul :
      inEpochFactor *
          (memoryCost (compInsertAppendNewGenProg d_app) (memoryState rFr x₈.toData) + 1) +
        inEpochPotential U w N base y ≤
      (98 * inEpochFactor) * slotPotential N (compGmAt base U w N x₃.mem) +
        201 * inEpochFactor := by
    unfold inEpochPotential
    have hym_eq : y.mem = Function.update x₉.mem (base + 6) (n + 1) := rfl
    rw [hms₈, hym_eq, hgm_y, hx₉m_app]
    calc inEpochFactor * (memoryCost (compInsertAppendNewGenProg d_app) s_grown + 1) +
          (98 * inEpochFactor) *
            slotPotential N
              (compGmAt base U w N
                ((Memory.spec 0).clientState s_grown (compInsertAppendNewGenProg d_app)).mem)
        = inEpochFactor *
            (memoryCost (compInsertAppendNewGenProg d_app) s_grown +
              98 * slotPotential N
                (compGmAt base U w N
                  ((Memory.spec 0).clientState s_grown (compInsertAppendNewGenProg d_app)).mem)) +
            inEpochFactor := by ring
      _ ≤ inEpochFactor * (98 * slotPotential N (compGmAt base U w N x₃.mem) + 200) +
            inEpochFactor :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hcost_app) _
      _ = (98 * inEpochFactor) * slotPotential N (compGmAt base U w N x₃.mem) +
            201 * inEpochFactor := by ring
  have hex_miss := hex_gd.seq_eq (hex_gz.seq_eq (hex_add_fr.seq_eq
    (hex_app.seq_eq (hex_o2.seq_eq (hex_inc.seq_eq hex_st)))))
  refine ⟨y, _, hex_miss, hyb, hy_ff, hsplit_y, hy_base,
    fun addr haddr => by
      have h1 : y.mem addr = x₉.mem addr :=
        Function.update_of_ne (Nat.ne_of_lt (Nat.lt_add_right 6 haddr)) _ _
      rw [h1]; exact hbelow9 addr haddr,
    insert_miss_tail_steps_le (hx₆_k.symm ▸ hΔ_le2) hcost_app_mul⟩

private theorem inEpochQueryCode_active_exec {U V w N n n_init base L_peak : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} (u : Fin U) {x : RData rEpoch}
    (hx : x.Bounded w) (hn : 0 < n) (hev : EpochValid U n N)
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hL : x.frontier ≤ L_peak)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hbase : x.regs rBase = base) (hu_reg : x.regs rArgU = u.val) :
    ∃ (y : RData rEpoch) (steps : ℕ),
      RDemonicExec w L_peak inEpochQueryCode x steps (· = y) ∧
      decode (.query u) y.regs = some (s_abs u) ∧
      y.Bounded w ∧
      y.frontier = base + compactedEpochWords U V w N n ∧
      CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
        ⟨y.mem, y.frontier⟩ ∧
      y.regs rBase = base ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      steps + inEpochPotential U w N base y ≤
        inEpochPotential U w N base x + (inEpochBaseCharge - 10) +
          (12 * inEpochFactor) *
            probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
  have h8 : 8 ≤ compactedEpochWords U V w N n := eight_le_compactedEpochWords U V w N n
  have hfit6 : Fits w 6 := hx.frontier_fits.of_le (by omega)
  obtain ⟨hex_ld, hx₁b⟩ := loadAtOffCode_exec (rAddr := rBase) (rDst := rCnt) (rTmp := rCur) hx hL
    (eReg_ne (by decide)) hbase hfit6 (by omega)
  set x₁ := (x.set rCur (base + 6)).set rCnt (x.mem (base + 6))
  have hx₁_cnt : x₁.regs rCnt = n := by
    simp only [x₁, RData.set_regs, Function.update_self]
    exact hsplit.root_hdr.hdr_n
  set x₂ := x₁.set rZero 0
  have hex_z := RDemonicExec.const (B := .exact) (d := rZero) (x := x₁) hL (fits_zero w)
  have hx₂b : x₂.Bounded w := hx₁b.set (fits_zero w)
  have hcond_neg : ¬(Cond.eq rCnt rZero).Holds x₂.toData := by
    change x₂.regs rCnt ≠ x₂.regs rZero
    simp [x₂, hx₁_cnt, hn.ne']
  have hx₂_base : x₂.regs rBase = base := by
    simp [x₂, x₁, RData.set, hbase]
  have hx₂_cnt : x₂.regs rCnt = n := by
    simp [x₂, RData.set, hx₁_cnt]
  have hx₂_u : x₂.regs rArgU = u.val := by
    simp [x₂, x₁, RData.set, hu_reg]
  obtain ⟨x₃, hex_ctx, hx₃b, hx₃m, hx₃f, hx₃_base, _, hx₃_scr, hx₃_hash, hx₃_item, hx₃_fr,
      _, hx₃_u, _, hx₃_hp, hx₃_cp⟩ :=
    loadActiveCtxCode_exec hx₂b hn hev hfr hL hsplit hx₂_base hx₂_cnt
  obtain ⟨x₄, hex_kh, hx₄b, hx₄f, hx₄_fr, hx₄_hout, hsplit₄, hx₄_out_mem, hx₄_pres⟩ :=
    evalKeyHashCode_exec u hx₃b hn hev (hx₃f.trans hfr) (hx₃f.le.trans hL)
      (by rw [hx₃m, hx₃f]; exact hsplit) (hx₃_fr.trans hx₃f.symm) hx₃_hash hx₃_scr
      (hx₃_u.trans hx₂_u) hx₃_hp hx₃_cp
  have hx₄_ff : x₄.frontier = base + compactedEpochWords U V w N n :=
    hx₄f.trans (hx₃f.trans hfr)
  obtain ⟨henv₄, hfit_off⟩ := compEpochEnv_of_split hx₄b hn hev hx₄_ff hsplit₄
  obtain ⟨s_fix₄, hinv₄, htot₄, hcpl₄⟩ := hsplit₄.coupled
  have hms₄ : memoryState rFr x₄.toData = ⟨x₄.mem, x₄.frontier⟩ :=
    Memory.State.ext rfl hx₄_fr
  obtain ⟨hpre_q, hst_q, hres_q, hcost_q⟩ :=
    compQueryWithHashGenProg_dict_spec henv₄ hfit_off hinv₄ hcpl₄ htot₄.le u
  set h_q := hValOfSeed U N θ (keyQuotient (bucketBits N) u.val)
  set d_q := ((mkCompParams U V w N, (base, base + offCompItems U w N)), (u.val, h_q))
  have hx₄_base : x₄.regs rBase = base :=
    (hx₄_pres rBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans hx₃_base
  have hx₄_item : x₄.regs rItemBase = base + offCompItems U w N :=
    (hx₄_pres rItemBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans hx₃_item
  have hx₄_u : x₄.regs rArgU = u.val :=
    (hx₄_pres rArgU (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans (hx₃_u.trans hx₂_u)
  have hx₄_cp : ∀ i : Fin 36, x₄.regs (cpReg i) = mkCompParams U V w N i := fun i =>
    (hx₄_pres (cpReg i) (cpReg_ne_eReg i (by decide)) (cpReg_lt_88 i)
      (cpReg_ne_eReg i (by decide)) (cpReg_ne_eReg i (by decide))).trans (hx₃_cp i)
  have hin_q : x₄.regs ∘ srcKeyHashOp = WordEncoding.encode d_q :=
    (regs_pairSrc
      (regs_pairSrc (regs_cp_eq hx₄_cp)
        (regs_pairSrc (regs_reg1_eq rBase hx₄_base) (regs_reg1_eq rItemBase hx₄_item)))
      (regs_pairSrc (regs_reg1_eq rArgU hx₄_u) (regs_reg1_eq rHashOut hx₄_hout))).eq
  have hv_q : (Memory.spec w).ValidHistory (memoryState rFr x₄.toData)
      ((Memory.spec w).clientHistory (memoryState rFr x₄.toData) (compQueryWithHashGenProg d_q)) :=
    validProg_compQueryWithHashGen (hms₄ ▸ hpre_q)
      ⟨wellFormed_memoryState hx₄b.1, Nat.zero_le _⟩
  have hnoalloc_q : ((Memory.spec 0).clientState (memoryState rFr x₄.toData)
      (compQueryWithHashGenProg d_q)).frontier ≤ x₄.frontier := by
    rw [hms₄, hst_q]
  obtain ⟨y, hex_q, hyb, hyf, hm_q, hout_q, hframe_q⟩ :=
    execWitness wQuery factor_wQuery_le rFr srcKeyHashOp tmpQuery
      tmpQuery_inj srcKeyHashOp_ne_tmpQuery tmpQuery_ne_rFr srcKeyHashOp_ne_rFr
      d_q hx₄b ((hx₄f.trans hx₃f).le.trans hL) hin_q (hms₄ ▸ hpre_q) hv_q hnoalloc_q
  rw [hms₄, hst_q] at hm_q
  rw [hms₄, hres_q] at hout_q
  have hym : y.mem = x₄.mem := congrArg Memory.State.mem hm_q
  have hy_dec : decode (.query u) y.regs = some (s_abs u) :=
    decode_query_optionWords u (s_abs u) y.regs
      (by have h0 := hout_q 0; rw [tmpQuery_out_0] at h0; exact h0)
      (by have h1 := hout_q 1; rw [tmpQuery_out_1] at h1; exact h1)
  have hy_base : y.regs rBase = base :=
    (hframe_q rBase (eReg_ne (by decide))
      (tmpQuery_ne_reg (eReg_lt_88 _) (eReg_ne (by decide)) (eReg_ne (by decide)))).trans hx₄_base
  have hex_tot : RDemonicExec w L_peak inEpochQueryCode x _ (· = y) :=
    hex_ld.seq_eq (hex_z.seq_eq
      (RDemonicExec.branch_neg hcond_neg (hex_ctx.seq_eq (hex_kh.seq_eq hex_q))))
  have hpot_eq : inEpochPotential U w N base y = inEpochPotential U w N base x := by
    unfold inEpochPotential
    rw [hym, compGmAt_eq_of_scratch_mod henv₄.pos_w hx₄_out_mem, hx₃m]; rfl
  have hcost_mul :
      inEpochFactor * (memoryCost (compQueryWithHashGenProg d_q) (memoryState rFr x₄.toData) + 1) ≤
        39 * inEpochFactor +
          (12 * inEpochFactor) *
            probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
    rw [hms₄]
    calc inEpochFactor * (memoryCost (compQueryWithHashGenProg d_q) ⟨x₄.mem, x₄.frontier⟩ + 1)
        ≤ inEpochFactor *
            (38 + 12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
              (Dictionary.dom s_abs) u + 1) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right hcost_q 1)
      _ = 39 * inEpochFactor +
            (12 * inEpochFactor) *
              probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
          ring
  have hf1 := one_le_inEpochFactor
  refine ⟨y, _, hex_tot, hy_dec, hyb, hyf.trans hx₄_ff,
    by rw [hym, hyf]; exact hsplit₄,
    hy_base,
    fun addr haddr => by
      rw [hym]; exact (hx₄_out_mem addr (Or.inl (by omega))).trans (congrFun hx₃m addr),
    by rw [hpot_eq]; unfold inEpochBaseCharge; omega⟩

private theorem inEpochInsertCode_active_exec {U V w N n n_init base L_peak : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} (u : Fin U) (v : ℕ) {x : RData rEpoch}
    (hx : x.Bounded w) (hn : 0 < n) (hev : EpochValid U n N)
    (hval : InEpochValid V N s_abs (.insert u v))
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hL_peak : base + inEpochPeakWords V w N n s_abs (.insert u v) ≤ L_peak)
    (hfit_peak : Fits w (base + inEpochPeakWords V w N n s_abs (.insert u v)))
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hbase : x.regs rBase = base) (hu_reg : x.regs rArgU = u.val) (hv_reg : x.regs rArgV = v) :
    let s_abs' := Function.update s_abs u (some v)
    let n' := (Dictionary.dom s_abs').card
    ∃ (y : RData rEpoch) (steps : ℕ),
      RDemonicExec w L_peak inEpochInsertCode x steps (· = y) ∧
      decode (.insert u v) y.regs = some () ∧
      y.Bounded w ∧
      y.frontier = base + compactedEpochWords U V w N n' ∧
      CompactedSplitRep base (base + offCompItems U w N) U V w N n' n_init θ s_abs'
        ⟨y.mem, y.frontier⟩ ∧
      y.regs rBase = base ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      steps + inEpochPotential U w N base y ≤
        inEpochPotential U w N base x + (inEpochBaseCharge - 10) +
          (12 * inEpochFactor) *
            probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
  intro s_abs' n'
  have hv_lt_V : v < V := hval.1.2
  have hvals' : Dictionary.ValuesBounded V s_abs' :=
    Dynamic.valuesBounded_step_of_valid (n_max := U) hsplit.vals_lt hval.1
  have hL : x.frontier ≤ L_peak := by
    rw [hfr]
    exact (Nat.add_le_add_left (compactedEpochWords_mono (le_max_left n n')) base).trans hL_peak
  have h8 : 8 ≤ compactedEpochWords U V w N n := eight_le_compactedEpochWords U V w N n
  have hfit1 : Fits w 1 := hx.frontier_fits.of_le (by omega)
  have hfit6 : Fits w 6 := hx.frontier_fits.of_le (by omega)
  obtain ⟨hex_ld, hx₁b⟩ := loadAtOffCode_exec (rAddr := rBase) (rDst := rCnt) (rTmp := rCur) hx hL
    (eReg_ne (by decide)) hbase hfit6 (by omega)
  set x₁ := (x.set rCur (base + 6)).set rCnt (x.mem (base + 6))
  have hx₁_base : x₁.regs rBase = base := by
    simp [x₁, RData.set, hbase]
  have hx₁_cnt : x₁.regs rCnt = n := by
    simp only [x₁, RData.set_regs, Function.update_self]
    exact hsplit.root_hdr.hdr_n
  have hx₁_u : x₁.regs rArgU = u.val := by
    simp [x₁, RData.set, hu_reg]
  have hx₁_v : x₁.regs rArgV = v := by
    simp [x₁, RData.set, hv_reg]
  obtain ⟨x₂, hex_ctx, hx₂b, hx₂m, hx₂f, hx₂_base, hx₂_cnt, hx₂_scr, hx₂_hash, hx₂_item, hx₂_fr,
      _, hx₂_u, hx₂_v, hx₂_hp, hx₂_cp⟩ :=
    loadActiveCtxCode_exec hx₁b hn hev hfr hL hsplit hx₁_base hx₁_cnt
  obtain ⟨x₃, hex_kh, hx₃b, hx₃f, hx₃_fr, hx₃_hout, hsplit₃, hx₃_out_mem, hx₃_pres⟩ :=
    evalKeyHashCode_exec u hx₂b hn hev (hx₂f.trans hfr) (hx₂f.le.trans hL)
      (by rw [hx₂m, hx₂f]; exact hsplit) (hx₂_fr.trans hx₂f.symm) hx₂_hash hx₂_scr
      (hx₂_u.trans hx₁_u) hx₂_hp hx₂_cp
  have hx₃_ff : x₃.frontier = base + compactedEpochWords U V w N n :=
    hx₃f.trans (hx₂f.trans hfr)
  obtain ⟨henv₃, hfit_off⟩ := compEpochEnv_of_split hx₃b hn hev hx₃_ff hsplit₃
  obtain ⟨s_fix₃, hinv₃, htot₃, hcpl₃⟩ := hsplit₃.coupled
  have hms₃ : memoryState rFr x₃.toData = ⟨x₃.mem, x₃.frontier⟩ :=
    Memory.State.ext rfl hx₃_fr
  obtain ⟨hpre_sr, hst_sr, hres_sr, hf_iff, _, hcost_sr⟩ :=
    compInsertSearchWithHashGenProg_dict_spec henv₃ hfit_off hinv₃ hcpl₃ htot₃.le u
  set q := keyQuotient (bucketBits N) u.val
  set h_q := hValOfSeed U N θ q
  set b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
  set m := mOfSeed U N θ q
  set res_sb := (Memory.spec 0).clientResult s_fix₃
    (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m))
  set d_sr := ((mkCompParams U V w N, (base, base + offCompItems U w N)), (u.val, h_q))
  have hx₃_base : x₃.regs rBase = base :=
    (hx₃_pres rBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans hx₂_base
  have hx₃_cnt : x₃.regs rCnt = n :=
    (hx₃_pres rCnt (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans hx₂_cnt
  have hx₃_item : x₃.regs rItemBase = base + offCompItems U w N :=
    (hx₃_pres rItemBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans hx₂_item
  have hx₃_u : x₃.regs rArgU = u.val :=
    (hx₃_pres rArgU (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans (hx₂_u.trans hx₁_u)
  have hx₃_v : x₃.regs rArgV = v :=
    (hx₃_pres rArgV (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans (hx₂_v.trans hx₁_v)
  have hx₃_cp : ∀ i : Fin 36, x₃.regs (cpReg i) = mkCompParams U V w N i := fun i =>
    (hx₃_pres (cpReg i) (cpReg_ne_eReg i (by decide)) (cpReg_lt_88 i)
      (cpReg_ne_eReg i (by decide)) (cpReg_ne_eReg i (by decide))).trans (hx₂_cp i)
  have hin_sr : x₃.regs ∘ srcKeyHashOp = WordEncoding.encode d_sr :=
    (regs_pairSrc
      (regs_pairSrc (regs_cp_eq hx₃_cp)
        (regs_pairSrc (regs_reg1_eq rBase hx₃_base) (regs_reg1_eq rItemBase hx₃_item)))
      (regs_pairSrc (regs_reg1_eq rArgU hx₃_u) (regs_reg1_eq rHashOut hx₃_hout))).eq
  have hv_sr : (Memory.spec w).ValidHistory (memoryState rFr x₃.toData)
      ((Memory.spec w).clientHistory (memoryState rFr x₃.toData)
        (compInsertSearchWithHashGenProg d_sr)) :=
    validProg_compInsertSearchWithHashGen (hms₃ ▸ hpre_sr)
      ⟨wellFormed_memoryState hx₃b.1, Nat.zero_le _⟩
  have hnoalloc_sr : ((Memory.spec 0).clientState (memoryState rFr x₃.toData)
      (compInsertSearchWithHashGenProg d_sr)).frontier ≤ x₃.frontier := by
    rw [hms₃, hst_sr]
  obtain ⟨x₄, hex_sr, hx₄b, hx₄f, hm_sr, hout_sr, hframe_sr⟩ :=
    execWitness wInsSearch factor_wInsSearch_le rFr srcKeyHashOp tmpInsSearch
      tmpInsSearch_inj srcKeyHashOp_ne_tmpInsSearch tmpInsSearch_ne_rFr srcKeyHashOp_ne_rFr
      d_sr hx₃b ((hx₃f.trans hx₂f).le.trans hL) hin_sr (hms₃ ▸ hpre_sr) hv_sr hnoalloc_sr
  rw [hms₃, hst_sr] at hm_sr
  rw [hms₃, hres_sr] at hout_sr
  have hx₄m : x₄.mem = x₃.mem := congrArg Memory.State.mem hm_sr
  have hx₄_fr : x₄.regs rFr = x₄.frontier := by
    have hfm := congrArg Memory.State.frontier hm_sr
    change x₄.regs rFr = x₃.frontier at hfm
    rw [hfm, hx₄f]
  have hx₄_found : x₄.regs rFound = res_sb.1.1 := by
    have h0 := hout_sr 0
    rw [tmpInsSearch_out] at h0
    exact h0.trans (encode_pair2_0 _ _ _ _)
  have hx₄_phys : x₄.regs rPhys = res_sb.2 := by
    have h1 := hout_sr 1
    rw [tmpInsSearch_out] at h1
    exact h1.trans (encode_pair2_1 _ _ _ _)
  have hx₄_b : x₄.regs rBucket = b := by
    have h2 := hout_sr 2
    rw [tmpInsSearch_out] at h2
    exact h2.trans (encode_pair2_2 _ _ _ _)
  have hx₄_m : x₄.regs rMicro = m := by
    have h3 := hout_sr 3
    rw [tmpInsSearch_out] at h3
    exact h3.trans (encode_pair2_3 _ _ _ _)
  have hx₄_pres : ∀ reg, reg ≠ rFr → reg.val < 88 →
      reg ≠ rFound → reg ≠ rPhys → reg ≠ rBucket → reg ≠ rMicro → x₄.regs reg = x₃.regs reg :=
    fun reg h1 h88 hf hp hb hm => hframe_sr reg h1 (tmpInsSearch_ne_reg h88 hf hp hb hm)
  set x₅ := x₄.set rOne 1
  have hex_o := RDemonicExec.const (B := .exact) (d := rOne) (x := x₄)
    ((hx₄f.trans (hx₃f.trans hx₂f)).le.trans hL) hfit1
  have hx₅b : x₅.Bounded w := hx₄b.set hfit1
  have hx₅_ff : x₅.frontier = base + compactedEpochWords U V w N n := hx₄f.trans hx₃_ff
  have hx₅_fr : x₅.regs rFr = x₅.frontier := by
    simp [x₅, RData.set, hx₄_fr]
  have hms₅ : memoryState rFr x₅.toData = ⟨x₃.mem, x₃.frontier⟩ :=
    Memory.State.ext hx₄m (hx₅_fr.trans hx₄f)
  have hx₅_base : x₅.regs rBase = base := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rBase ≠ rOne)]
    exact (hx₄_pres rBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₃_base
  have hx₅_cnt : x₅.regs rCnt = n := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rCnt ≠ rOne)]
    exact (hx₄_pres rCnt (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₃_cnt
  have hx₅_item : x₅.regs rItemBase = base + offCompItems U w N := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rItemBase ≠ rOne)]
    exact (hx₄_pres rItemBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₃_item
  have hx₅_u : x₅.regs rArgU = u.val := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rArgU ≠ rOne)]
    exact (hx₄_pres rArgU (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₃_u
  have hx₅_v : x₅.regs rArgV = v := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rArgV ≠ rOne)]
    exact (hx₄_pres rArgV (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₃_v
  have hx₅_cp : ∀ i : Fin 36, x₅.regs (cpReg i) = mkCompParams U V w N i := fun i => by
    simp only [x₅, RData.set_regs, Function.update_of_ne (cpReg_ne_eReg (c := 12) i (by decide))]
    exact (hx₄_pres (cpReg i) (cpReg_ne_eReg i (by decide)) (cpReg_lt_88 i)
      (cpReg_ne_eReg i (by decide)) (cpReg_ne_eReg i (by decide))
      (cpReg_ne_eReg i (by decide)) (cpReg_ne_eReg i (by decide))).trans (hx₃_cp i)
  have hcost_sr_mul :
      inEpochFactor *
          (memoryCost (compInsertSearchWithHashGenProg d_sr) (memoryState rFr x₃.toData) + 1) ≤
        33 * inEpochFactor +
          (12 * inEpochFactor) *
            probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
    rw [hms₃]
    calc inEpochFactor * (memoryCost (compInsertSearchWithHashGenProg d_sr) ⟨x₃.mem, x₃.frontier⟩ +
          1)
        ≤ inEpochFactor *
            (32 + 12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
              (Dictionary.dom s_abs) u + 1) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right hcost_sr 1)
      _ = 33 * inEpochFactor +
            (12 * inEpochFactor) *
              probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
          ring
  have hgm_x₃ : compGmAt base U w N x₃.mem = compGmAt base U w N x.mem := by
    rw [compGmAt_eq_of_scratch_mod henv₃.pos_w hx₃_out_mem, hx₂m]; rfl
  have hf1_ge := one_le_inEpochFactor
  by_cases hhit : res_sb.1.1 = 1
  · have hsome : (s_abs u).isSome := hf_iff.mp hhit
    have hn'_eq : n' = n := by
      dsimp only [n', s_abs']
      rw [Dictionary.dom_insert s_abs u v,
        Finset.insert_eq_of_mem (Dictionary.mem_dom_iff_isSome.mpr hsome), hsplit.card_eq]
    have hcond_pos : (Cond.eq rFound rOne).Holds x₅.toData := by
      change x₅.regs rFound = x₅.regs rOne
      simp [x₅, RData.set,
        hx₄_found, hhit]
    obtain ⟨hpre_wv, hfr_wv, hgm_wv, hcost_wv, s_fix', hinv', hcpl'⟩ :=
      compInsertHit_dict_spec henv₃ hfit_off hinv₃ hcpl₃ htot₃.le u v hv_lt_V hhit
    set d_wv := (((mkCompParams U V w N, (base, base + offCompItems U w N)), res_sb.2), v)
    have hp₅ : x₅.regs rPhys = res_sb.2 := by
      simp [x₅, RData.set, hx₄_phys]
    have hin_wv : x₅.regs ∘ srcWriteVal = WordEncoding.encode d_wv :=
      (regs_pairSrc
        (regs_pairSrc
          (regs_pairSrc (regs_cp_eq hx₅_cp)
            (regs_pairSrc (regs_reg1_eq rBase hx₅_base) (regs_reg1_eq rItemBase hx₅_item)))
          (regs_reg1_eq rPhys hp₅))
        (regs_reg1_eq rArgV hx₅_v)).eq
    have hv_wv : (Memory.spec w).ValidHistory (memoryState rFr x₅.toData)
        ((Memory.spec w).clientHistory (memoryState rFr x₅.toData)
          (compWritePhysValGenProg d_wv)) :=
      validProg_compWritePhysValGen (hms₅ ▸ hpre_wv)
        ⟨wellFormed_memoryState hx₅b.1, Nat.zero_le _⟩
    have hnoalloc_wv : ((Memory.spec 0).clientState (memoryState rFr x₅.toData)
        (compWritePhysValGenProg d_wv)).frontier ≤ x₅.frontier := by
      rw [hms₅, hfr_wv.frontier_eq]; exact (hx₃_ff.trans hx₅_ff.symm).le
    obtain ⟨y, hex_wv, hyb, hyf, hm_wv, _, hframe_wv⟩ :=
      execWitness wWriteVal factor_wWriteVal_le rFr srcWriteVal tmpWriteVal
        tmpWriteVal_inj srcWriteVal_ne_tmp tmpWriteVal_ne_rFr srcWriteVal_ne_rFr
        d_wv hx₅b ((hx₅_ff.trans hfr.symm).le.trans hL) hin_wv (hms₅ ▸ hpre_wv) hv_wv hnoalloc_wv
    rw [hms₅] at hm_wv
    have hym_wv : y.mem =
        ((Memory.spec 0).clientState ⟨x₃.mem, x₃.frontier⟩ (compWritePhysValGenProg d_wv)).mem :=
      congrArg Memory.State.mem hm_wv
    have hs'_eq : (⟨y.mem, y.frontier⟩ : Memory.State) =
        (Memory.spec 0).clientState ⟨x₃.mem, x₃.frontier⟩ (compWritePhysValGenProg d_wv) := by
      refine Memory.State.ext hym_wv ?_
      rw [hyf, hx₅_ff, ← hx₃_ff, hfr_wv.frontier_eq]
    obtain ⟨hhdr_y, hpar_y, hhash_y, hbelow_y⟩ :=
      hdr_params_hash_of_opFrame (s' := ⟨y.mem, y.frontier⟩)
        hsplit₃.root_hdr hsplit₃.params_stored hsplit₃.hash_rep
        (by rw [hs'_eq]; exact hfr_wv)
    have hsplit_y : CompactedSplitRep base (base + offCompItems U w N) U V w N n' n_init θ s_abs'
        ⟨y.mem, y.frontier⟩ := by
      rw [hn'_eq]
      refine ⟨hhdr_y, hpar_y, hhash_y, hn'_eq ▸ rfl, hvals', s_fix', hinv', ?_,
        by rw [hs'_eq]; exact hcpl'⟩
      have hym_gm : compGmAt base U w N y.mem = compGmAt base U w N x₃.mem := by
        rw [hym_wv]; exact hgm_wv
      rw [hym_gm]; exact htot₃
    have hy_base : y.regs rBase = base :=
      (hframe_wv rBase (eReg_ne (by decide)) (tmpWriteVal_ne_reg (eReg_lt_88 _))).trans hx₅_base
    have hpot_eq : inEpochPotential U w N base y = inEpochPotential U w N base x := by
      unfold inEpochPotential
      rw [hym_wv, hgm_wv, hgm_x₃]
    have hcost_wv_mul :
        inEpochFactor *
          (memoryCost (compWritePhysValGenProg d_wv) (memoryState rFr x₅.toData) + 1) ≤
          9 * inEpochFactor := by
      rw [hms₅]
      calc inEpochFactor * (memoryCost (compWritePhysValGenProg d_wv) ⟨x₃.mem, x₃.frontier⟩ + 1)
          ≤ inEpochFactor * (8 + 1) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add_right hcost_wv 1)
        _ = 9 * inEpochFactor := by ring
    have hex_tot : RDemonicExec w L_peak inEpochInsertCode x _ (· = y) :=
      hex_ld.seq_eq (hex_ctx.seq_eq (hex_kh.seq_eq (hex_sr.seq_eq
        (hex_o.seq_eq (RDemonicExec.branch_pos (neg := inEpochInsertMissTailCode)
          hcond_pos hex_wv)))))
    refine ⟨y, _, hex_tot, rfl, hyb, by rw [hyf, hx₅_ff, hn'_eq], hsplit_y, hy_base,
      fun addr haddr => (hbelow_y addr haddr).trans
        ((hx₃_out_mem addr (Or.inl (Nat.lt_add_right offScratch haddr))).trans
          (congrFun hx₂m addr)),
      by rw [hpot_eq]; exact insert_hit_steps_le hcost_sr_mul hcost_wv_mul⟩
  · have hnot_some : ¬(s_abs u).isSome := mt hf_iff.mpr hhit
    have hnot_mem : u ∉ Dictionary.dom s_abs := mt Dictionary.mem_dom_iff_isSome.mp hnot_some
    have hn'_eq : n' = n + 1 := by
      dsimp only [n', s_abs']
      rw [Dictionary.dom_insert s_abs u v, Finset.card_insert_of_notMem hnot_mem,
        hsplit.card_eq]
    have hn_lt_N : n < N := by
      have hev' : EpochValid U n' N := hval.2
      rw [hn'_eq] at hev'
      rcases hev' with ⟨hn0, _⟩ | ⟨_, hn1N, _, _⟩
      · exact absurd hn0 (Nat.succ_ne_zero n)
      · exact hn1N
    have hcond_neg : ¬(Cond.eq rFound rOne).Holds x₅.toData := by
      change x₅.regs rFound ≠ x₅.regs rOne
      simp [x₅, RData.set,
        hx₄_found, hhit]
    have hpeak_eq : inEpochPeakWords V w N n s_abs (.insert u v) =
        compactedEpochWords U V w N (n + 1) := by
      unfold inEpochPeakWords
      change compactedEpochWords U V w N (max n n') = _
      rw [hn'_eq, max_eq_right (Nat.le_succ n)]
    have hx₅_b : x₅.regs rBucket = b := by
      simp [x₅, RData.set, hx₄_b]
    have hx₅_m : x₅.regs rMicro = m := by
      simp [x₅, RData.set, hx₄_m]
    obtain ⟨y, steps_m, hex_miss, hyb, hy_ff, hsplit_y, hy_base, hbelow9, hcost_m⟩ :=
      inEpochInsertMissTailCode_exec u v hx₅b hn hn_lt_N henv₃ hfit1 hfit6
        (hfr.symm.le.trans hL)
        (by rw [← hpeak_eq]; exact hL_peak)
        (by rw [← hpeak_eq]; exact hfit_peak)
        hsplit₃ hinv₃ htot₃ hcpl₃ hms₅ hx₅_ff hx₅_fr hx₅_base hx₅_cnt hx₅_item
        hx₅_b hx₅_m hx₅_u hx₅_v hx₅_cp hv_lt_V hvals' hn'_eq hhit
    have hpot_x : inEpochPotential U w N base x =
        (98 * inEpochFactor) * slotPotential N (compGmAt base U w N x₃.mem) := by
      unfold inEpochPotential; rw [hgm_x₃]
    have hex_tot : RDemonicExec w L_peak inEpochInsertCode x _ (· = y) :=
      hex_ld.seq_eq (hex_ctx.seq_eq (hex_kh.seq_eq (hex_sr.seq_eq
        (hex_o.seq_eq (RDemonicExec.branch_neg
          (pos := RCode.ofCode (wWriteVal.code rFr srcWriteVal tmpWriteVal))
          hcond_neg hex_miss)))))
    refine ⟨y, _, hex_tot, rfl, hyb, by rw [hy_ff, hn'_eq],
      by rw [hn'_eq]; exact hsplit_y, hy_base,
      fun addr haddr => (hbelow9 addr haddr).trans
        ((hx₃_out_mem addr (Or.inl (Nat.lt_add_right offScratch haddr))).trans
          (congrFun hx₂m addr)),
      insert_miss_steps_le hcost_sr_mul (by rw [hpot_x]; exact hcost_m)⟩

private theorem inEpochDeleteHitTailCode_exec {U V w N n n' n_init base L_peak : ℕ}
    {θ : QuotHashSeed U N} {s_abs' : Dictionary.State U}
    {s_fix' : Memory.State} {x₈ x₉ : RData rEpoch}
    (hx₉b : x₉.Bounded w) (hn : 0 < n) (hn'_pos : 0 < n') (hn'_eq : n' = n - 1)
    (hcard' : (Dictionary.dom s_abs').card = n')
    (hvals' : Dictionary.ValuesBounded V s_abs')
    (hev : EpochValid U n N)
    (hw : 0 < w) (hNU : N ≤ U) (hltU : U < 2 ^ w) (hleV : V ≤ 2 ^ w)
    (hfit1 : Fits w 1) (hfit6 : Fits w 6)
    (hL : base + compactedEpochWords U V w N n ≤ L_peak)
    (hhdr8 : RootHeaderValid U V w N n n_init base x₈.mem)
    (hpar8 : EpochParamsStored U V w N base x₈.mem)
    (hhash8 : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ x₈.mem)
    (hinv' : DictStateInv U V (ghostW w) N 0 θ s_abs' s_fix')
    (hcpl8 : FixedCoupled base (base + offCompItems U w N) U V w N s_fix' ⟨x₈.mem, x₈.frontier⟩)
    (hx₉m : x₉.mem = x₈.mem)
    (hx₉_ff : x₉.frontier = base + compactedEpochWords U V w N n)
    (hx₉_fr : x₉.regs rFr = x₉.frontier)
    (hx₉_base : x₉.regs rBase = base) (hx₉_cnt : x₉.regs rCnt = n)
    (hx₉_cp : ∀ i : Fin 36, x₉.regs (cpReg i) = mkCompParams U V w N i) :
    ∃ (y : RData rEpoch) (steps_h : ℕ),
      RDemonicExec w L_peak inEpochDeleteHitTailCode x₉ steps_h (· = y) ∧
      y.Bounded w ∧
      y.frontier = base + compactedEpochWords U V w N n' ∧
      CompactedSplitRep base (base + offCompItems U w N) U V w N n' n_init θ s_abs'
        ⟨y.mem, y.frontier⟩ ∧
      y.regs rBase = base ∧
      (∀ addr < base, y.mem addr = x₈.mem addr) ∧
      inEpochPotential U w N base y =
        (98 * inEpochFactor) * slotPotential N (compGmAt base U w N x₈.mem) ∧
      steps_h ≤ inEpochFactor + 18 := by
  have hce_n : compactedEpochWords U V w N n =
      offCompItems U w N + compactedItemWords U V w N n := by
    unfold compactedEpochWords; rw [ite_eq_right hn.ne']
  have hce_n' : compactedEpochWords U V w N n' =
      offCompItems U w N + compactedItemWords U V w N n' := by
    unfold compactedEpochWords; rw [ite_eq_right hn'_pos.ne']
  have hfit_iw0 : Fits w (4 + compactedItemWords U V w N n) :=
    fits_four_add_compactedItemWords hn (by rw [← hx₉_ff]; exact hx₉b.frontier_fits)
  have hin_sd : x₉.regs ∘ srcShrinkDelta = WordEncoding.encode (mkCompParams U V w N, n) :=
    (regs_pairSrc (regs_cp_eq hx₉_cp) (regs_reg1_eq rCnt hx₉_cnt)).eq
  have hsafe_sd : CompShrinkDeltaPre w (mkCompParams U V w N, n) (memoryState rFr x₉.toData) :=
    ⟨U, V, N, hw, hn, hNU, hltU, hleV, rfl, hfit_iw0⟩
  have hv_sd : (Memory.spec w).ValidHistory (memoryState rFr x₉.toData)
      ((Memory.spec w).clientHistory (memoryState rFr x₉.toData)
        (compShrinkDeltaGenProg (mkCompParams U V w N, n))) :=
    validProg_compShrinkDeltaGen _ _ ⟨wellFormed_memoryState hx₉b.1, Nat.zero_le _⟩
  have hnoalloc_sd : ((Memory.spec 0).clientState (memoryState rFr x₉.toData)
      (compShrinkDeltaGenProg (mkCompParams U V w N, n))).frontier ≤ x₉.frontier := by
    rw [clientState_compShrinkDeltaGenProg]; exact hx₉_fr.le
  obtain ⟨x₁₀, hex_sd, hx₁₀b, hx₁₀f, hm_sd, hout_sd, hframe_sd⟩ :=
    execWitness wShrinkDelta factor_wShrinkDelta_le rFr srcShrinkDelta tmpShrinkDelta
      tmpShrinkDelta_inj srcShrinkDelta_ne_tmp tmpShrinkDelta_ne_rFr srcShrinkDelta_ne_rFr
      (mkCompParams U V w N, n) hx₉b (hx₉_ff.le.trans hL)
      hin_sd hsafe_sd hv_sd hnoalloc_sd
  rw [memoryCost_compShrinkDeltaGenProg, zero_add, mul_one] at hex_sd
  rw [clientState_compShrinkDeltaGenProg] at hm_sd
  have hx₁₀m : x₁₀.mem = x₈.mem := (congrArg Memory.State.mem hm_sd).trans hx₉m
  have hx₁₀_ff : x₁₀.frontier = base + compactedEpochWords U V w N n := hx₁₀f.trans hx₉_ff
  set Δ := compactedItemWords U V w N n - compactedItemWords U V w N (n - 1)
  have hΔ_le2 : Δ ≤ 2 := by
    have hn_eq : n = (n - 1) + 1 := by omega
    dsimp only [Δ]
    conv_lhs => rw [hn_eq]
    exact compactedItemWords_succ_sub_le_two hw hltU.le hleV
  have hx₁₀_k : x₁₀.regs rK = Δ := by
    have h0 := hout_sd 0
    rw [tmpShrinkDelta_out, clientResult_compShrinkDeltaGenProg hw] at h0
    exact h0
  have hfr_sub_Δ : x₁₀.frontier - Δ = base + compactedEpochWords U V w N n' := by
    have hm_iw := compactedItemWords_mono (U := U) (V := V) (w := w) (N := N) (Nat.sub_le n 1)
    rw [hx₁₀_ff, hce_n, hce_n', hn'_eq]
    dsimp only [Δ]; omega
  have hk_le_fr : x₁₀.regs rK ≤ x₁₀.frontier := by
    have hm_iw := compactedItemWords_mono (U := U) (V := V) (w := w) (N := N) (Nat.sub_le n 1)
    rw [hx₁₀_k, hx₁₀_ff, hce_n]; dsimp only [Δ]; omega
  have hex_sh := shrinkCode_exec hx₁₀b rShrink_nodup hfit1 (hx₁₀_ff.le.trans hL) hk_le_fr
  set x₁₁ := shrinkPost rK rIdx rZero rOne x₁₀
  have hx₁₁b : x₁₁.Bounded w := shrinkPost_bounded hx₁₀b hfit1 hk_le_fr
  have hx₁₁_ff : x₁₁.frontier = base + compactedEpochWords U V w N n' := by
    change x₁₀.frontier - x₁₀.regs rK = _
    rw [hx₁₀_k, hfr_sub_Δ]
  have hx₁₁_base : x₁₁.regs rBase = base := by
    simp only [x₁₁, shrinkPost,
      Function.update_of_ne (eReg_ne (by decide) : rBase ≠ rIdx),
      Function.update_of_ne (eReg_ne (by decide) : rBase ≠ rOne),
      Function.update_of_ne (eReg_ne (by decide) : rBase ≠ rZero)]
    exact (hframe_sd rBase (eReg_ne (by decide))
      (tmpShrinkDelta_ne_reg (eReg_lt_88 _) (eReg_ne (by decide)))).trans hx₉_base
  have hx₁₁_cnt : x₁₁.regs rCnt = n := by
    simp only [x₁₁, shrinkPost,
      Function.update_of_ne (eReg_ne (by decide) : rCnt ≠ rIdx),
      Function.update_of_ne (eReg_ne (by decide) : rCnt ≠ rOne),
      Function.update_of_ne (eReg_ne (by decide) : rCnt ≠ rZero)]
    exact (hframe_sd rCnt (eReg_ne (by decide))
      (tmpShrinkDelta_ne_reg (eReg_lt_88 _) (eReg_ne (by decide)))).trans hx₉_cnt
  have hL_sh : x₁₁.frontier ≤ L_peak := by
    rw [hx₁₁_ff]
    exact (Nat.add_le_add_left (compactedEpochWords_mono (by omega : n' ≤ n)) base).trans hL
  have hfit_n' : Fits w n' := lt_of_le_of_lt
    (by rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, _⟩ <;> omega : n' ≤ U) hltU
  have hn1 : 1 ≤ n := hn
  set x₁₂ := x₁₁.set rOne 1
  set x₁₃ := x₁₂.set rCnt n'
  have hex_o2 := RDemonicExec.const (B := .exact) (d := rOne) (x := x₁₁) hL_sh hfit1
  have hex_dec := RDemonicExec.exactBin (f := .sub) (d := rCnt) (i := rCnt) (j := rOne)
    (w := w) (L_peak := L_peak) (x := x₁₂) hL_sh (v := n')
    (by simp [BinOp.evalExact, x₁₂, RData.set, hx₁₁_cnt, hn1, hn'_eq])
    hfit_n'
  have hx₁₃b : x₁₃.Bounded w := (hx₁₁b.set hfit1).set hfit_n'
  have hx₁₃_base : x₁₃.regs rBase = base := by
    simp [x₁₃, x₁₂, RData.set, hx₁₁_base]
  have h8_n' : 8 ≤ compactedEpochWords U V w N n' := eight_le_compactedEpochWords U V w N n'
  obtain ⟨hex_st, hyb⟩ := storeAtOffCode_exec (rAddr := rBase) (rSrc := rCnt) (rTmp := rCur)
    (val := n') hx₁₃b hL_sh (eReg_ne (by decide)) (eReg_ne (by decide)) hx₁₃_base
    (by simp [x₁₃, RData.set]) hfit6
    (by simp only [x₁₃, x₁₂, RData.set_frontier, hx₁₁_ff]; omega)
  set y := (x₁₃.set rCur (base + 6)).write (base + 6) n'
  have hy_ff : y.frontier = base + compactedEpochWords U V w N n' := hx₁₁_ff
  have hy_base : y.regs rBase = base := by
    simp [y, RData.write, RData.set, hx₁₃_base]
  have hclr_below : ∀ a < base + compactedEpochWords U V w N n', x₁₁.mem a = x₈.mem a :=
    fun a ha => by
      change clear x₁₀.mem (x₁₀.frontier - x₁₀.regs rK) (x₁₀.regs rK) a = x₈.mem a
      rw [hx₁₀_k, hfr_sub_Δ, clear_of_not_owns (by simp only [Block.Owns]; omega), hx₁₀m]
  have h0_off : epochHdrWords ≤ offCompLM U w N := Nat.le_add_right _ _
  have h1_off : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h2_off : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h3_off : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h4_off : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  have hhdr11 : RootHeaderValid U V w N n n_init base x₁₁.mem :=
    ⟨hhdr8.fits_U, hhdr8.pos_U, hhdr8.pos_V,
      (hclr_below base (by omega)).trans hhdr8.hdr_U,
      (hclr_below (base + 1) (by omega)).trans hhdr8.hdr_V,
      (hclr_below (base + 2) (by omega)).trans hhdr8.hdr_w,
      (hclr_below (base + 3) (by omega)).trans hhdr8.hdr_keyBits,
      (hclr_below (base + 4) (by omega)).trans hhdr8.hdr_valBits,
      (hclr_below (base + 5) (by omega)).trans hhdr8.hdr_N,
      (hclr_below (base + 6) (by omega)).trans hhdr8.hdr_n,
      (hclr_below (base + 7) (by omega)).trans hhdr8.hdr_n_init⟩
  have hpar11 : EpochParamsStored U V w N base x₁₁.mem :=
    ⟨fun i => (hclr_below (base + offHashParams + i.val)
        (by rw [hce_n']; unfold offHashParams; unfold epochHdrWords at h0_off; omega)).trans
          (hpar8.hp_eq i),
     fun i => (hclr_below (base + offCompParams + i.val)
        (by rw [hce_n']; unfold offCompParams; unfold epochHdrWords at h0_off; omega)).trans
          (hpar8.cp_eq i)⟩
  have hhash11 : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ x₁₁.mem :=
    ⟨ReducedKWise.tableRep_congr hhash8.1 (fun a _ h2 =>
        (hclr_below a (by rw [hce_n']; dsimp only [offCompLM, epochHashSpace, qBits, hashB,
          epochQBits, epochHashB] at *; omega)).symm),
     ReducedKWise.seedRep_congr (w := w) hhash8.2 (fun a _ h2 =>
        (hclr_below a (by rw [hce_n']; dsimp only [offCompLM, epochHashSpace, qBits, hashB,
          epochQBits, epochHashB, ReducedKWise.space] at *; omega)).symm)⟩
  have hlm11 := compLmAt_congr (metaBase := base) (U := U) (N := N) hw
    fun a ha => hclr_below a (by rw [hce_n']; omega)
  have hgm11 := compGmAt_congr (metaBase := base) (U := U) (N := N) hw
    fun a ha => hclr_below a (by rw [hce_n']; omega)
  have htd11 := compTDAt_congr (metaBase := base) (U := U) (N := N) hw
    fun a ha => hclr_below a (by rw [hce_n']; omega)
  have hdt11 := compDTAt_congr (metaBase := base) (U := U) (N := N) hw
    fun a ha => hclr_below a (by rw [hce_n']; omega)
  have htot11 : epochTotalSlots N (compGmAt base U w N x₁₁.mem) = n' := by
    change totalSlots N (compGmAt base U w N x₁₁.mem) = n'
    rw [hgm11, hcpl8.gm_eq]
    exact hinv'.htot.trans hcard'
  have htot8 : epochTotalSlots N (compGmAt base U w N x₈.mem) = n' := hgm11 ▸ htot11
  have hq11 : compQuotAt (base + offCompItems U w N) U V w N n' x₁₁.mem =
      compQuotAt (base + offCompItems U w N) U V w N n' x₈.mem :=
    compQuotAt_congr hw fun a ha => hclr_below a (by rw [hce_n']; omega)
  have hv11 : compValAt (base + offCompItems U w N) U V w N n' x₁₁.mem =
      compValAt (base + offCompItems U w N) U V w N n' x₈.mem :=
    compValAt_congr hw fun a ha => hclr_below a (by rw [hce_n']; omega)
  have hcpl11 : FixedCoupled base (base + offCompItems U w N) U V w N s_fix'
      ⟨x₁₁.mem, x₁₁.frontier⟩ :=
    ⟨hgm11.trans hcpl8.gm_eq, hlm11.trans hcpl8.lm_eq,
      by rw [hgm11, htd11, hdt11]; exact hcpl8.win_inv,
      fun i => by rw [htd11]; exact hcpl8.td_lt i,
      fun i => by rw [hdt11]; exact hcpl8.dt_lt i,
      fun d hd => by
        have hd8 : d < epochTotalSlots N (compGmAt base U w N x₈.mem) := hgm11 ▸ hd
        change compQuotAt _ U V w N (epochTotalSlots N (compGmAt base U w N x₁₁.mem)) x₁₁.mem d =
          quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem
            (physByBase N (compGmAt base U w N x₁₁.mem 0 * slabSize N)
              (compDTAt base U w N x₁₁.mem) d)
        rw [htot11, hq11, ← htot8, hgm11, hdt11]
        exact hcpl8.quot_eq d hd8,
      fun d hd => by
        have hd8 : d < epochTotalSlots N (compGmAt base U w N x₈.mem) := hgm11 ▸ hd
        change compValAt _ U V w N (epochTotalSlots N (compGmAt base U w N x₁₁.mem)) x₁₁.mem d =
          valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix'.mem
            (physByBase N (compGmAt base U w N x₁₁.mem 0 * slabSize N)
              (compDTAt base U w N x₁₁.mem) d)
        rw [htot11, hv11, ← htot8, hgm11, hdt11]
        exact hcpl8.val_eq d hd8⟩
  obtain ⟨hsplit_y, hgm_y⟩ := update_hdr_n_preserves_split (n_new := n')
    hw hhdr11 hpar11 hhash11 hcard' hvals' hinv' hcpl11
  have hpot_y : inEpochPotential U w N base y =
      (98 * inEpochFactor) * slotPotential N (compGmAt base U w N x₈.mem) := by
    unfold inEpochPotential
    have hym_eq : y.mem = Function.update x₁₁.mem (base + 6) n' := rfl
    rw [hym_eq, hgm_y, hgm11]
  have hex_hit := hex_sd.seq_eq (hex_sh.seq_eq (hex_o2.seq_eq (hex_dec.seq_eq hex_st)))
  refine ⟨y, _, hex_hit, hyb, hy_ff, hsplit_y, hy_base,
    fun addr haddr => by
      have h1 : y.mem addr = x₁₁.mem addr :=
        Function.update_of_ne (Nat.ne_of_lt (Nat.lt_add_right 6 haddr)) _ _
      rw [h1, hclr_below addr (Nat.lt_add_right _ haddr)]
    , hpot_y, delete_hit_tail_steps_le (hx₁₀_k.symm ▸ hΔ_le2)⟩

private theorem inEpochDeleteCode_active_exec {U V w N n n_init base L_peak : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} (u : Fin U) {x : RData rEpoch}
    (hx : x.Bounded w) (hn : 0 < n) (hev : EpochValid U n N)
    (hval : InEpochValid V N s_abs (.delete u))
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hL : x.frontier ≤ L_peak)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hbase : x.regs rBase = base) (hu_reg : x.regs rArgU = u.val) :
    let s_abs' := Function.update s_abs u none
    let n' := (Dictionary.dom s_abs').card
    ∃ (y : RData rEpoch) (steps : ℕ),
      RDemonicExec w L_peak inEpochDeleteCode x steps (· = y) ∧
      decode (.delete u) y.regs = some () ∧
      y.Bounded w ∧
      y.frontier = base + compactedEpochWords U V w N n' ∧
      CompactedSplitRep base (base + offCompItems U w N) U V w N n' n_init θ s_abs'
        ⟨y.mem, y.frontier⟩ ∧
      y.regs rBase = base ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      steps + inEpochPotential U w N base y ≤
        inEpochPotential U w N base x + (inEpochBaseCharge - 10) +
          (12 * inEpochFactor) *
            probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
  intro s_abs' n'
  have hvals' : Dictionary.ValuesBounded V s_abs' :=
    Dynamic.valuesBounded_delete hsplit.vals_lt u
  have h8 : 8 ≤ compactedEpochWords U V w N n := eight_le_compactedEpochWords U V w N n
  have hfit1 : Fits w 1 := hx.frontier_fits.of_le (by omega)
  have hfit6 : Fits w 6 := hx.frontier_fits.of_le (by omega)
  obtain ⟨hex_ld, hx₁b⟩ := loadAtOffCode_exec (rAddr := rBase) (rDst := rCnt) (rTmp := rCur) hx hL
    (eReg_ne (by decide)) hbase hfit6 (by omega)
  set x₁ := (x.set rCur (base + 6)).set rCnt (x.mem (base + 6))
  have hx₁_cnt : x₁.regs rCnt = n := by
    simp only [x₁, RData.set_regs, Function.update_self]
    exact hsplit.root_hdr.hdr_n
  set x₂ := x₁.set rZero 0
  have hex_z := RDemonicExec.const (B := .exact) (d := rZero) (x := x₁) hL (fits_zero w)
  have hx₂b : x₂.Bounded w := hx₁b.set (fits_zero w)
  have hcond_neg0 : ¬(Cond.eq rCnt rZero).Holds x₂.toData := by
    change x₂.regs rCnt ≠ x₂.regs rZero
    simp [x₂, hx₁_cnt, hn.ne']
  have hx₂_base : x₂.regs rBase = base := by
    simp [x₂, x₁, RData.set, hbase]
  have hx₂_cnt : x₂.regs rCnt = n := by
    simp [x₂, RData.set, hx₁_cnt]
  have hx₂_u : x₂.regs rArgU = u.val := by
    simp [x₂, x₁, RData.set, hu_reg]
  obtain ⟨x₃, hex_ctx, hx₃b, hx₃m, hx₃f, hx₃_base, hx₃_cnt, hx₃_scr, hx₃_hash, hx₃_item, hx₃_fr,
      _, hx₃_u, _, hx₃_hp, hx₃_cp⟩ :=
    loadActiveCtxCode_exec hx₂b hn hev hfr hL hsplit hx₂_base hx₂_cnt
  obtain ⟨x₄, hex_kh, hx₄b, hx₄f, hx₄_fr, hx₄_hout, hsplit₄, hx₄_out_mem, hx₄_pres⟩ :=
    evalKeyHashCode_exec u hx₃b hn hev (hx₃f.trans hfr) (hx₃f.le.trans hL)
      (by rw [hx₃m, hx₃f]; exact hsplit) (hx₃_fr.trans hx₃f.symm) hx₃_hash hx₃_scr
      (hx₃_u.trans hx₂_u) hx₃_hp hx₃_cp
  have hx₄_ff : x₄.frontier = base + compactedEpochWords U V w N n :=
    hx₄f.trans (hx₃f.trans hfr)
  set x₅ := x₄.set rHq (x₄.regs rHashOut)
  have hex_cp_hq := RDemonicExec.copy (B := .exact) (w := w) (d := rHq) (s := rHashOut) (x := x₄)
    ((hx₄_ff.trans hfr.symm).le.trans hL)
  have hx₅b : x₅.Bounded w := hx₄b.set (hx₄b.regs_fits rHashOut)
  have hx₅_ff : x₅.frontier = base + compactedEpochWords U V w N n := hx₄_ff
  have hx₅_fr : x₅.regs rFr = x₅.frontier := by
    simp [x₅, RData.set, hx₄_fr]
  have hms₅ : memoryState rFr x₅.toData = ⟨x₄.mem, x₄.frontier⟩ :=
    Memory.State.ext rfl hx₅_fr
  obtain ⟨henv₄, hfit_off⟩ := compEpochEnv_of_split hx₄b hn hev hx₄_ff hsplit₄
  obtain ⟨s_fix₄, hinv₄, htot₄, hcpl₄⟩ := hsplit₄.coupled
  set q := keyQuotient (bucketBits N) u.val
  set h_q := hValOfSeed U N θ q
  set d_prep := ((mkCompParams U V w N, (base, base + offCompItems U w N)), (u.val, h_q))
  obtain ⟨found0, j_del0, phys_del0, q_last0, hres_prep0, _, hpre_prep, hst_prep,
      hq_last0_lt, _, _, _, _⟩ :=
    compDeleteWithHashGenProg_dict_spec (s_mid := ⟨x₄.mem, x₄.frontier⟩)
      henv₄ hfit_off hinv₄ hcpl₄ htot₄.le rfl (fun _ _ => rfl) u
  have hx₅_base : x₅.regs rBase = base := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rBase ≠ rHq)]
    exact (hx₄_pres rBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans hx₃_base
  have hx₅_cnt : x₅.regs rCnt = n := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rCnt ≠ rHq)]
    exact (hx₄_pres rCnt (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans hx₃_cnt
  have hx₅_item : x₅.regs rItemBase = base + offCompItems U w N := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rItemBase ≠ rHq)]
    exact (hx₄_pres rItemBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans hx₃_item
  have hx₅_hash : x₅.regs rHashBase = base + epochHdrWords := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rHashBase ≠ rHq)]
    exact (hx₄_pres rHashBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans hx₃_hash
  have hx₅_scr : x₅.regs rScratchBase = base + offScratch := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rScratchBase ≠ rHq)]
    exact (hx₄_pres rScratchBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans hx₃_scr
  have hx₅_u : x₅.regs rArgU = u.val := by
    simp only [x₅, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rArgU ≠ rHq)]
    exact (hx₄_pres rArgU (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
      (eReg_ne (by decide))).trans (hx₃_u.trans hx₂_u)
  have hx₅_hq : x₅.regs rHq = h_q := by simp [x₅, RData.set, hx₄_hout]
  have hx₅_hp : ∀ i : Fin 19, x₅.regs (hpReg i) =
      mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i := fun i => by
    simp only [x₅, RData.set_regs, Function.update_of_ne (hpReg_ne_eReg (c := 19) i (by decide))]
    exact (hx₄_pres (hpReg i) (hpReg_ne_eReg i (by decide)) (hpReg_lt_88 i)
      (hpReg_ne_eReg i (by decide)) (hpReg_ne_eReg i (by decide))).trans (hx₃_hp i)
  have hx₅_cp : ∀ i : Fin 36, x₅.regs (cpReg i) = mkCompParams U V w N i := fun i => by
    simp only [x₅, RData.set_regs, Function.update_of_ne (cpReg_ne_eReg (c := 19) i (by decide))]
    exact (hx₄_pres (cpReg i) (cpReg_ne_eReg i (by decide)) (cpReg_lt_88 i)
      (cpReg_ne_eReg i (by decide)) (cpReg_ne_eReg i (by decide))).trans (hx₃_cp i)
  have hin_prep : x₅.regs ∘ srcDelPrep = WordEncoding.encode d_prep :=
    (regs_pairSrc
      (regs_pairSrc (regs_cp_eq hx₅_cp)
        (regs_pairSrc (regs_reg1_eq rBase hx₅_base) (regs_reg1_eq rItemBase hx₅_item)))
      (regs_pairSrc (regs_reg1_eq rArgU hx₅_u) (regs_reg1_eq rHq hx₅_hq))).eq
  have hv_prep : (Memory.spec w).ValidHistory (memoryState rFr x₅.toData)
      ((Memory.spec w).clientHistory (memoryState rFr x₅.toData)
        (compDeletePrepWithHashGenProg d_prep)) :=
    validProg_compDeletePrepWithHashGen (hms₅ ▸ hpre_prep)
      ⟨wellFormed_memoryState hx₅b.1, Nat.zero_le _⟩
  have hnoalloc_prep : ((Memory.spec 0).clientState (memoryState rFr x₅.toData)
      (compDeletePrepWithHashGenProg d_prep)).frontier ≤ x₅.frontier := by
    rw [hms₅, hst_prep]; exact le_rfl
  obtain ⟨x₆, hex_prep, hx₆b, hx₆f, hm_prep, hout_prep, hframe_prep⟩ :=
    execWitness wDelPrep factor_wDelPrep_le rFr srcDelPrep tmpDelPrep
      tmpDelPrep_inj srcDelPrep_ne_tmp tmpDelPrep_ne_rFr srcDelPrep_ne_rFr
      d_prep hx₅b ((hx₅_ff.trans hfr.symm).le.trans hL) hin_prep
      (hms₅ ▸ hpre_prep) hv_prep hnoalloc_prep
  rw [hms₅, hst_prep] at hm_prep
  rw [hms₅, hres_prep0] at hout_prep
  have hx₆m : x₆.mem = x₄.mem := congrArg Memory.State.mem hm_prep
  have hx₆_ff : x₆.frontier = base + compactedEpochWords U V w N n := hx₆f.trans hx₅_ff
  have hx₆_fr : x₆.regs rFr = x₆.frontier := by
    have hfm := congrArg Memory.State.frontier hm_prep
    change x₆.regs rFr = x₄.frontier at hfm
    rw [hfm, hx₆f]; rfl
  have hx₆_found : x₆.regs rFound = found0 := by
    have h0 := hout_prep 0
    rw [tmpDelPrep_out] at h0
    exact h0.trans (encode_left4_0 _ _ _ _)
  have hx₆_jdel : x₆.regs rJDel = j_del0 := by
    have h1 := hout_prep 1
    rw [tmpDelPrep_out] at h1
    exact h1.trans (encode_left4_1 _ _ _ _)
  have hx₆_phys : x₆.regs rPhys = phys_del0 := by
    have h2 := hout_prep 2
    rw [tmpDelPrep_out] at h2
    exact h2.trans (encode_left4_2 _ _ _ _)
  have hx₆_quot : x₆.regs rQuot = q_last0 := by
    have h3 := hout_prep 3
    rw [tmpDelPrep_out] at h3
    exact h3.trans (encode_left4_3 _ _ _ _)
  have hx₆_pres : ∀ reg, reg ≠ rFr → reg.val < 88 →
      reg ≠ rFound → reg ≠ rJDel → reg ≠ rPhys → reg ≠ rQuot → x₆.regs reg = x₅.regs reg :=
    fun reg h1 h88 hf hj hp hq => hframe_prep reg h1 (tmpDelPrep_ne_reg h88 hf hj hp hq)
  obtain ⟨x₇, hex_h2, hx₇b, hx₇f, hx₇_fr, hx₇_hout, hsplit₇, hx₇_out_mem, hx₇_pres⟩ :=
    runEvalHashAtQuot hx₆b hn hev hx₆_ff ((hx₆_ff.trans hfr.symm).le.trans hL)
      (by rw [hx₆m, hx₆_ff, ← hx₄_ff]; exact hsplit₄) hx₆_fr
      ((hx₆_pres rHashBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
        (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₅_hash)
      ((hx₆_pres rScratchBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
        (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₅_scr)
      hx₆_quot
      (fun i => (hx₆_pres (hpReg i) (hpReg_ne_eReg i (by decide)) (hpReg_lt_88 i)
        (hpReg_ne_eReg i (by decide)) (hpReg_ne_eReg i (by decide))
        (hpReg_ne_eReg i (by decide)) (hpReg_ne_eReg i (by decide))).trans (hx₅_hp i))
      hq_last0_lt
  have hx₇_ff : x₇.frontier = base + compactedEpochWords U V w N n := hx₇f.trans hx₆_ff
  have hms₇ : memoryState rFr x₇.toData = ⟨x₇.mem, x₇.frontier⟩ :=
    Memory.State.ext rfl hx₇_fr
  have hmid_fr : (⟨x₇.mem, x₇.frontier⟩ : Memory.State).frontier = x₄.frontier :=
    hx₇_ff.trans hx₄_ff.symm
  have hmid_out : ∀ a, base + offCompLM U w N ≤ a → x₇.mem a = x₄.mem a := fun a ha => by
    have : epochHdrWords ≤ offCompLM U w N := Nat.le_add_right _ _
    exact (hx₇_out_mem a (Or.inr (by omega))).trans (congrFun hx₆m a)
  obtain ⟨found, j_del, phys_del, q_last, hres_prep, hf_iff, _, _, _,
      hpre_fin, hfr_fin, ⟨s_fix', hinv', hcpl'⟩, hcost_del⟩ :=
    compDeleteWithHashGenProg_dict_spec (s_mid := ⟨x₇.mem, x₇.frontier⟩)
      henv₄ hfit_off hinv₄ hcpl₄ htot₄.le hmid_fr hmid_out u
  have hquad_eq : (((found, j_del), phys_del), q_last) =
      (((found0, j_del0), phys_del0), q_last0) := hres_prep.symm.trans hres_prep0
  have hf_eq : found = found0 := congrArg (fun t => t.1.1.1) hquad_eq
  have hj_eq : j_del = j_del0 := congrArg (fun t => t.1.1.2) hquad_eq
  have hp_eq : phys_del = phys_del0 := congrArg (fun t => t.1.2) hquad_eq
  have hql_eq : q_last = q_last0 := congrArg Prod.snd hquad_eq
  subst hf_eq hj_eq hp_eq hql_eq
  set h_q_last := hValOfSeed U N θ q_last
  set d_fin := ((((mkCompParams U V w N, (base, base + offCompItems U w N)), (u.val, h_q)),
    ((found, j_del), phys_del)), h_q_last)
  have hx₇_base : x₇.regs rBase = base :=
    (hx₇_pres rBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))).trans
      ((hx₆_pres rBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
        (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₅_base)
  have hx₇_cnt : x₇.regs rCnt = n :=
    (hx₇_pres rCnt (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))).trans
      ((hx₆_pres rCnt (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
        (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₅_cnt)
  have hx₇_item : x₇.regs rItemBase = base + offCompItems U w N :=
    (hx₇_pres rItemBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))).trans
      ((hx₆_pres rItemBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
        (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₅_item)
  have hx₇_u : x₇.regs rArgU = u.val :=
    (hx₇_pres rArgU (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))).trans
      ((hx₆_pres rArgU (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
        (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₅_u)
  have hx₇_hq : x₇.regs rHq = h_q :=
    (hx₇_pres rHq (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))).trans
      ((hx₆_pres rHq (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))
        (eReg_ne (by decide)) (eReg_ne (by decide)) (eReg_ne (by decide))).trans hx₅_hq)
  have hx₇_found : x₇.regs rFound = found :=
    (hx₇_pres rFound (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))).trans hx₆_found
  have hx₇_jdel : x₇.regs rJDel = j_del :=
    (hx₇_pres rJDel (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))).trans hx₆_jdel
  have hx₇_phys : x₇.regs rPhys = phys_del :=
    (hx₇_pres rPhys (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))).trans hx₆_phys
  have hx₇_cp : ∀ i : Fin 36, x₇.regs (cpReg i) = mkCompParams U V w N i := fun i =>
    (hx₇_pres (cpReg i) (cpReg_ne_eReg i (by decide)) (cpReg_lt_88 i)
      (cpReg_ne_eReg i (by decide))).trans
      ((hx₆_pres (cpReg i) (cpReg_ne_eReg i (by decide)) (cpReg_lt_88 i)
        (cpReg_ne_eReg i (by decide)) (cpReg_ne_eReg i (by decide))
        (cpReg_ne_eReg i (by decide)) (cpReg_ne_eReg i (by decide))).trans (hx₅_cp i))
  have hin_fin : x₇.regs ∘ srcDelFin = WordEncoding.encode d_fin :=
    (regs_pairSrc
      (regs_pairSrc
        (regs_pairSrc
          (regs_pairSrc (regs_cp_eq hx₇_cp)
            (regs_pairSrc (regs_reg1_eq rBase hx₇_base) (regs_reg1_eq rItemBase hx₇_item)))
          (regs_pairSrc (regs_reg1_eq rArgU hx₇_u) (regs_reg1_eq rHq hx₇_hq)))
        (regs_pairSrc
          (regs_pairSrc (regs_reg1_eq rFound hx₇_found) (regs_reg1_eq rJDel hx₇_jdel))
          (regs_reg1_eq rPhys hx₇_phys)))
      (regs_reg1_eq rHashOut hx₇_hout)).eq
  have hv_fin : (Memory.spec w).ValidHistory (memoryState rFr x₇.toData)
      ((Memory.spec w).clientHistory (memoryState rFr x₇.toData)
        (compDeleteFinishWithHashGenProg d_fin)) :=
    validProg_compDeleteFinishWithHashGen (hms₇ ▸ hpre_fin)
      ⟨wellFormed_memoryState hx₇b.1, Nat.zero_le _⟩
  have hnoalloc_fin : ((Memory.spec 0).clientState (memoryState rFr x₇.toData)
      (compDeleteFinishWithHashGenProg d_fin)).frontier ≤ x₇.frontier := by
    rw [hms₇, hfr_fin.frontier_eq]
  obtain ⟨x₈, hex_fin, hx₈b, hx₈f, hm_fin, _, hframe_fin⟩ :=
    execWitness wDelFin factor_wDelFin_le rFr srcDelFin tmpDelFin
      tmpDelFin_inj srcDelFin_ne_tmp tmpDelFin_ne_rFr srcDelFin_ne_rFr
      d_fin hx₇b ((hx₇_ff.trans hfr.symm).le.trans hL) hin_fin (hms₇ ▸ hpre_fin) hv_fin hnoalloc_fin
  rw [hms₇] at hm_fin
  have hx₈m_fin : x₈.mem =
      ((Memory.spec 0).clientState ⟨x₇.mem, x₇.frontier⟩
        (compDeleteFinishWithHashGenProg d_fin)).mem :=
    congrArg Memory.State.mem hm_fin
  have hx₈_ff : x₈.frontier = base + compactedEpochWords U V w N n := hx₈f.trans hx₇_ff
  have hx₈_fr : x₈.regs rFr = x₈.frontier := by
    have hfm := congrArg Memory.State.frontier hm_fin
    change x₈.regs rFr = _ at hfm
    rw [hfm, hfr_fin.frontier_eq, hx₈f]
  have hs8_eq : (⟨x₈.mem, x₈.frontier⟩ : Memory.State) =
      (Memory.spec 0).clientState ⟨x₇.mem, x₇.frontier⟩ (compDeleteFinishWithHashGenProg d_fin) :=
    Memory.State.ext hx₈m_fin (by rw [hx₈f, hfr_fin.frontier_eq])
  obtain ⟨hhdr8, hpar8, hhash8, hbelow8⟩ :=
    hdr_params_hash_of_opFrame (s' := ⟨x₈.mem, x₈.frontier⟩)
      hsplit₇.root_hdr hsplit₇.params_stored hsplit₇.hash_rep
      (by rw [hs8_eq]; exact hfr_fin)
  have hx₈_unch : ∀ reg, reg ≠ rFr → reg.val < 88 → x₈.regs reg = x₇.regs reg :=
    fun reg h1 h88 => hframe_fin reg h1 (tmpDelFin_ne_reg h88)
  set x₉ := x₈.set rOne 1
  have hex_o := RDemonicExec.const (B := .exact) (d := rOne) (x := x₈)
    ((hx₈_ff.trans hfr.symm).le.trans hL) hfit1
  have hx₉b : x₉.Bounded w := hx₈b.set hfit1
  have hx₉_ff : x₉.frontier = base + compactedEpochWords U V w N n := hx₈_ff
  have hx₉_fr : x₉.regs rFr = x₉.frontier := by
    simp [x₉, RData.set, hx₈_fr]
  have hx₉_base : x₉.regs rBase = base := by
    simp only [x₉, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rBase ≠ rOne)]
    exact (hx₈_unch rBase (eReg_ne (by decide)) (eReg_lt_88 _)).trans hx₇_base
  have hx₉_cnt : x₉.regs rCnt = n := by
    simp only [x₉, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rCnt ≠ rOne)]
    exact (hx₈_unch rCnt (eReg_ne (by decide)) (eReg_lt_88 _)).trans hx₇_cnt
  have hx₉_found : x₉.regs rFound = found := by
    simp only [x₉, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rFound ≠ rOne)]
    exact (hx₈_unch rFound (eReg_ne (by decide)) (eReg_lt_88 _)).trans hx₇_found
  have hx₉_cp : ∀ i : Fin 36, x₉.regs (cpReg i) = mkCompParams U V w N i := fun i => by
    simp only [x₉, RData.set_regs, Function.update_of_ne (cpReg_ne_eReg (c := 12) i (by decide))]
    exact (hx₈_unch (cpReg i) (cpReg_ne_eReg i (by decide)) (cpReg_lt_88 i)).trans (hx₇_cp i)
  have hgm_x₄ : compGmAt base U w N x₄.mem = compGmAt base U w N x.mem := by
    rw [compGmAt_eq_of_scratch_mod henv₄.pos_w hx₄_out_mem, hx₃m]; rfl
  have hcost_del_mul :
      inEpochFactor *
          (memoryCost (compDeletePrepWithHashGenProg d_prep) (memoryState rFr x₅.toData) + 1) +
        inEpochFactor *
          (memoryCost (compDeleteFinishWithHashGenProg d_fin) (memoryState rFr x₇.toData) + 1) +
        (98 * inEpochFactor) * slotPotential N (compGmAt base U w N x₈.mem) ≤
      inEpochPotential U w N base x + 356 * inEpochFactor +
        (12 * inEpochFactor) *
          probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
    unfold inEpochPotential
    rw [hms₅, hms₇, hx₈m_fin, ← hgm_x₄]
    calc inEpochFactor * (memoryCost (compDeletePrepWithHashGenProg d_prep) ⟨x₄.mem, x₄.frontier⟩ +
            1) +
          inEpochFactor *
            (memoryCost (compDeleteFinishWithHashGenProg d_fin) ⟨x₇.mem, x₇.frontier⟩ + 1) +
          (98 * inEpochFactor) *
            slotPotential N
              (compGmAt base U w N
                ((Memory.spec 0).clientState ⟨x₇.mem, x₇.frontier⟩
                  (compDeleteFinishWithHashGenProg d_fin)).mem)
        = inEpochFactor *
            (memoryCost (compDeletePrepWithHashGenProg d_prep) ⟨x₄.mem, x₄.frontier⟩ +
              memoryCost (compDeleteFinishWithHashGenProg d_fin) ⟨x₇.mem, x₇.frontier⟩ +
              98 * slotPotential N
                (compGmAt base U w N
                  ((Memory.spec 0).clientState ⟨x₇.mem, x₇.frontier⟩
                    (compDeleteFinishWithHashGenProg d_fin)).mem)) +
            2 * inEpochFactor := by ring
      _ ≤ inEpochFactor *
            (98 * slotPotential N (compGmAt base U w N x₄.mem) + 354 +
              12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
                (Dictionary.dom s_abs) u) +
            2 * inEpochFactor :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hcost_del) _
      _ = (98 * inEpochFactor) * slotPotential N (compGmAt base U w N x₄.mem) +
            356 * inEpochFactor +
            (12 * inEpochFactor) *
              probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
          ring
  have hf1_ge := one_le_inEpochFactor
  have hbelow_x₈ : ∀ addr < base, x₈.mem addr = x.mem addr := fun addr haddr =>
    (hbelow8 addr haddr).trans
      ((hx₇_out_mem addr (Or.inl (Nat.lt_add_right offScratch haddr))).trans
        ((congrFun hx₆m addr).trans
          ((hx₄_out_mem addr (Or.inl (Nat.lt_add_right offScratch haddr))).trans
            (congrFun hx₃m addr))))
  have hcpl8 : FixedCoupled base (base + offCompItems U w N) U V w N s_fix'
      ⟨x₈.mem, x₈.frontier⟩ := by rw [hs8_eq]; exact hcpl'
  by_cases hhit : found = 1
  · have hsome : (s_abs u).isSome := hf_iff.mp hhit
    have hn'_eq : n' = n - 1 := by
      dsimp only [n', s_abs']
      rw [Dynamic.card_dom_delete_eq_of_isSome hsome, hsplit.card_eq]
    have hn'_pos : 0 < n' := by
      have hev' := hval.2
      change EpochValid U n' N at hev'
      rcases hev' with ⟨hn0, hN0⟩ | ⟨hn1, _, _, _⟩
      · rcases hev with ⟨rfl, _⟩ | ⟨_, _, hN4, _⟩
        · exact absurd rfl hn.ne'
        · exfalso; subst hN0; exact absurd (Nat.eq_zero_of_le_zero (by omega : n ≤ 0)) hn.ne'
      · exact hn1
    have hcond_pos : (Cond.eq rFound rOne).Holds x₉.toData := by
      change x₉.regs rFound = x₉.regs rOne
      rw [hx₉_found, hhit]
      simp [x₉, RData.set]
    obtain ⟨y, steps_h, hex_hit, hyb, hy_ff, hsplit_y, hy_base, hbelow_y, hpot_y, hsteps_h⟩ :=
      inEpochDeleteHitTailCode_exec hx₉b hn hn'_pos hn'_eq rfl hvals' hev
        henv₄.pos_w henv₄.le_U henv₄.lt_pow_U henv₄.le_pow_V hfit1 hfit6
        (hfr.symm.le.trans hL) hhdr8 hpar8 hhash8 hinv' hcpl8 rfl hx₉_ff hx₉_fr
        hx₉_base hx₉_cnt hx₉_cp
    have hex_tot : RDemonicExec w L_peak inEpochDeleteCode x _ (· = y) :=
      hex_ld.seq_eq (hex_z.seq_eq (RDemonicExec.branch_neg (pos := .op (.copy rZero rZero))
        hcond_neg0 (hex_ctx.seq_eq (hex_kh.seq_eq (hex_cp_hq.seq_eq (hex_prep.seq_eq
          (hex_h2.seq_eq (hex_fin.seq_eq (hex_o.seq_eq
            (RDemonicExec.branch_pos (neg := .op (.copy rZero rZero))
              hcond_pos hex_hit))))))))))
    refine ⟨y, _, hex_tot, rfl, hyb, hy_ff, hsplit_y, hy_base,
      fun addr haddr => (hbelow_y addr haddr).trans (hbelow_x₈ addr haddr),
      delete_hit_steps_le hsteps_h (by rw [hpot_y]; exact hcost_del_mul)⟩
  · have hnot_some : ¬(s_abs u).isSome := mt hf_iff.mpr hhit
    have hs_abs'_eq : s_abs' = s_abs := by
      dsimp only [s_abs']
      funext k
      by_cases hku : k = u
      · subst hku; simp [Option.not_isSome_iff_eq_none.mp hnot_some]
      · simp [Function.update_of_ne hku]
    have hn'_eq : n' = n := by dsimp only [n']; rw [hs_abs'_eq, hsplit.card_eq]
    have hcond_neg : ¬(Cond.eq rFound rOne).Holds x₉.toData := by
      change x₉.regs rFound ≠ x₉.regs rOne
      rw [hx₉_found]
      simp [x₉, RData.set, hhit]
    set y := x₉.set rZero (x₉.regs rZero)
    have hex_nop := RDemonicExec.copy (B := .exact) (w := w) (d := rZero) (s := rZero) (x := x₉)
      ((hx₉_ff.trans hfr.symm).le.trans hL)
    have hyb : y.Bounded w := hx₉b.set (hx₉b.regs_fits rZero)
    have hy_base : y.regs rBase = base := by
      simp [y, RData.set, hx₉_base]
    have hsplit_y : CompactedSplitRep base (base + offCompItems U w N) U V w N n' n_init θ s_abs'
        ⟨y.mem, y.frontier⟩ := by
      rw [hn'_eq]
      refine ⟨hhdr8, hpar8, hhash8, by rw [hs_abs'_eq, hsplit.card_eq], hvals', s_fix', hinv', ?_,
        hcpl8⟩
      change totalSlots N (compGmAt base U w N x₈.mem) = n
      rw [hcpl8.gm_eq]
      exact hinv'.htot.trans hn'_eq
    have hpot_y : inEpochPotential U w N base y =
        (98 * inEpochFactor) * slotPotential N (compGmAt base U w N x₈.mem) := rfl
    have hex_tot : RDemonicExec w L_peak inEpochDeleteCode x _ (· = y) :=
      hex_ld.seq_eq (hex_z.seq_eq (RDemonicExec.branch_neg (pos := .op (.copy rZero rZero))
        hcond_neg0 (hex_ctx.seq_eq (hex_kh.seq_eq (hex_cp_hq.seq_eq (hex_prep.seq_eq
          (hex_h2.seq_eq (hex_fin.seq_eq (hex_o.seq_eq
            (RDemonicExec.branch_neg (pos := inEpochDeleteHitTailCode)
              hcond_neg hex_nop))))))))))
    refine ⟨y, _, hex_tot, rfl, hyb, by change x₈.frontier = _; rw [hx₈_ff, hn'_eq],
      hsplit_y, hy_base, hbelow_x₈,
      delete_miss_steps_le (by rw [hpot_y]; exact hcost_del_mul)⟩

/-! ## Section 4: Main Operational Execution, `1 · OPT` `PeakFrontierLe`, and `O(1)` Expectation -/

/-- **Active-Epoch Seeded Operational Execution (`inEpochOpCode_active_demonicExec`):**
For any active epoch (`0 < n`, latent seed `θ : QuotHashSeed U N`) and any `o : Dynamic.Op U`
satisfying `InEpochValid V N s_abs o`, `inEpochOpCode` executes deterministically in `steps`
instructions, keeps the hardware frontier `≤ base + inEpochPeakWords V w N n s_abs o` at every
step, decodes the exact `Dynamic.spec` result, preserves `CompactedSplitRep` at the **same** latent
seed `θ`, preserves `rBase` and caller memory `< base`, and satisfies the potential-amortized step
bound `steps + Φ(y) ≤ Φ(x) + inEpochBaseCharge + (12 * inEpochFactor) * probeExcess`. -/
theorem inEpochOpCode_active_demonicExec {U V w N n n_init base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} (o : Dynamic.Op U) {x : RData rEpoch}
    (hx : x.Bounded w) (hn : 0 < n) (hev : EpochValid U n N)
    (hval : InEpochValid V N s_abs o)
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hbase : x.regs rBase = base) (harg : argMatch o x.regs)
    (hfit : Fits w (base + inEpochPeakWords V w N n s_abs o)) :
    let s_abs' := ((Dynamic.spec U V U).stepFn s_abs o).1
    let n' := (Dictionary.dom s_abs').card
    ∃ (y : RData rEpoch) (steps : ℕ),
      RDemonicExec w (base + inEpochPeakWords V w N n s_abs o) inEpochOpCode x steps (· = y) ∧
      decode o y.regs = some ((Dynamic.spec U V U).stepFn s_abs o).2 ∧
      y.Bounded w ∧
      y.frontier = base + compactedEpochWords U V w N n' ∧
      CompactedSplitRep base (base + offCompItems U w N) U V w N n' n_init θ s_abs'
        ⟨y.mem, y.frontier⟩ ∧
      y.regs rBase = base ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      steps + inEpochPotential U w N base y ≤
        inEpochPotential U w N base x + inEpochBaseCharge +
          (12 * inEpochFactor) *
            probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
              (Dictionary.dom s_abs) (opKey o) := by
  intro s_abs' n'
  set L_peak := base + inEpochPeakWords V w N n s_abs o
  have hL : x.frontier ≤ L_peak := by
    rw [hfr]
    exact Nat.add_le_add_left (compactedEpochWords_mono (le_max_left n n')) base
  have h8 : 8 ≤ compactedEpochWords U V w N n := eight_le_compactedEpochWords U V w N n
  have hfit1 : Fits w 1 := hx.frontier_fits.of_le (by omega)
  set x₁ := (x.set rZero 0).set rOne 1
  have s_z0 := RDemonicExec.const (B := .exact) (d := rZero) (x := x) hL (fits_zero w)
  have s_o1 := RDemonicExec.const (B := .exact) (d := rOne) (x := x.set rZero 0) hL hfit1
  have hx₁b : x₁.Bounded w := (hx.set (fits_zero w)).set hfit1
  have hx₁_base : x₁.regs rBase = base := by
    simp [x₁, RData.set, hbase]
  have hpot1 : inEpochPotential U w N base x₁ = inEpochPotential U w N base x := rfl
  have hf1_ge := one_le_inEpochFactor
  cases o with
  | query u =>
    obtain ⟨htag, hu_reg⟩ := harg
    have hc0 : (Cond.eq rTag rZero).Holds x₁.toData := by
      change x₁.regs rTag = x₁.regs rZero
      simp [x₁, RData.set, htag]
    have hx₁_u : x₁.regs rArgU = u.val := by
      simp [x₁, RData.set, hu_reg]
    obtain ⟨y, st, hex_q, hdec, hyb, hyf, hsplit_y, hy_base, hbelow, hcost⟩ :=
      inEpochQueryCode_active_exec u hx₁b hn hev hfr hL hsplit hx₁_base hx₁_u
    rw [hpot1] at hcost
    have hn'_eq : n' = n := hsplit.card_eq
    refine ⟨y, _, s_z0.seq_eq (s_o1.seq_eq (RDemonicExec.branch_pos hc0 hex_q)), hdec, hyb,
      by rw [hn'_eq]; exact hyf, by rw [hn'_eq]; exact hsplit_y, hy_base, hbelow,
      by dsimp only [opKey]; unfold inEpochBaseCharge at hcost ⊢; omega⟩
  | insert u v =>
    obtain ⟨htag, hu_reg, hv_reg⟩ := harg
    have hnc0 : ¬(Cond.eq rTag rZero).Holds x₁.toData := by
      change x₁.regs rTag ≠ x₁.regs rZero
      simp [x₁, RData.set, htag]
    have hc1 : (Cond.eq rTag rOne).Holds x₁.toData := by
      change x₁.regs rTag = x₁.regs rOne
      simp [x₁, RData.set, htag]
    have hx₁_u : x₁.regs rArgU = u.val := by
      simp [x₁, RData.set, hu_reg]
    have hx₁_v : x₁.regs rArgV = v := by
      simp [x₁, RData.set, hv_reg]
    obtain ⟨y, st, hex_i, hdec, hyb, hyf, hsplit_y, hy_base, hbelow, hcost⟩ :=
      inEpochInsertCode_active_exec u v hx₁b hn hev hval hfr le_rfl hfit hsplit
        hx₁_base hx₁_u hx₁_v
    rw [hpot1] at hcost
    refine ⟨y, _, s_z0.seq_eq (s_o1.seq_eq
        (RDemonicExec.branch_neg hnc0 (RDemonicExec.branch_pos hc1 hex_i))),
      hdec, hyb, hyf, hsplit_y, hy_base, hbelow,
      by dsimp only [opKey]; unfold inEpochBaseCharge at hcost ⊢; omega⟩
  | delete u =>
    obtain ⟨htag, hu_reg⟩ := harg
    have hnc0 : ¬(Cond.eq rTag rZero).Holds x₁.toData := by
      change x₁.regs rTag ≠ x₁.regs rZero
      simp [x₁, RData.set, htag]
    have hnc1 : ¬(Cond.eq rTag rOne).Holds x₁.toData := by
      change x₁.regs rTag ≠ x₁.regs rOne
      simp [x₁, RData.set, htag]
    have hx₁_u : x₁.regs rArgU = u.val := by
      simp [x₁, RData.set, hu_reg]
    obtain ⟨y, st, hex_d, hdec, hyb, hyf, hsplit_y, hy_base, hbelow, hcost⟩ :=
      inEpochDeleteCode_active_exec u hx₁b hn hev hval hfr hL hsplit hx₁_base hx₁_u
    rw [hpot1] at hcost
    refine ⟨y, _,
      s_z0.seq_eq (s_o1.seq_eq
        (RDemonicExec.branch_neg hnc0 (RDemonicExec.branch_neg hnc1 hex_d))),
      hdec, hyb, hyf, hsplit_y, hy_base, hbelow,
      by dsimp only [opKey]; unfold inEpochBaseCharge at hcost ⊢; omega⟩

/-- **In-Epoch Compacted Representation Execution (`inEpochOpCode_demonicExec`):**
For every resting `CompactedRep U V w N n n_init base s_abs x` (both `n = 0` and `0 < n`) and every
`o : Dynamic.Op U` satisfying `InEpochValid V N s_abs o`, `inEpochOpCode` executes without faulting
under peak hardware frontier `base + inEpochPeakWords V w N n s_abs o`, returns the `Dynamic.spec`
output via `decode o`, and preserves `CompactedRep`, `rBase`, and caller memory `< base`. -/
theorem inEpochOpCode_demonicExec {U V w N n n_init base : ℕ}
    {s_abs : Dictionary.State U} (o : Dynamic.Op U) {x : RData rEpoch}
    (hrep : CompactedRep U V w N n n_init base s_abs x)
    (hval : InEpochValid V N s_abs o)
    (hbase : x.regs rBase = base) (harg : argMatch o x.regs)
    (hfit : Fits w (base + inEpochPeakWords V w N n s_abs o)) :
    let s_abs' := ((Dynamic.spec U V U).stepFn s_abs o).1
    let n' := (Dictionary.dom s_abs').card
    ∃ (y : RData rEpoch) (steps : ℕ),
      RDemonicExec w (base + inEpochPeakWords V w N n s_abs o) inEpochOpCode x steps (· = y) ∧
      decode o y.regs = some ((Dynamic.spec U V U).stepFn s_abs o).2 ∧
      CompactedRep U V w N n' n_init base s_abs' y ∧
      y.regs rBase = base ∧
      (∀ addr < base, y.mem addr = x.mem addr) := by
  intro s_abs' n'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hN0 : N = 0 := by rcases hrep.epoch_inv with ⟨_, hN0⟩ | ⟨h1, _, _, _⟩ <;> omega
    subst hN0
    have hdom_empty : Dictionary.dom s_abs = ∅ := Finset.card_eq_zero.mp hrep.card_eq
    have hs_none : ∀ u : Fin U, s_abs u = none := fun u => by
      by_contra hne
      have : u ∈ Dictionary.dom s_abs :=
        Dictionary.mem_dom_iff_isSome.mpr (Option.ne_none_iff_isSome.mp hne)
      rw [hdom_empty] at this; exact Finset.notMem_empty u this
    set L_peak := base + inEpochPeakWords V w 0 0 s_abs o
    have hL : x.frontier ≤ L_peak := by
      rw [hrep.frontier_eq]
      exact Nat.add_le_add_left (compactedEpochWords_mono (Nat.zero_le _)) base
    have h8 : 8 ≤ compactedEpochWords U V w 0 0 := eight_le_compactedEpochWords U V w 0 0
    have hx := hrep.bounded
    have hfit1 : Fits w 1 := hx.frontier_fits.of_le (by rw [hrep.frontier_eq]; omega)
    have hfit6 : Fits w 6 := hx.frontier_fits.of_le (by rw [hrep.frontier_eq]; omega)
    set x₁ := (x.set rZero 0).set rOne 1
    have s_z0 := RDemonicExec.const (B := .exact) (d := rZero) (x := x) hL (fits_zero w)
    have s_o1 := RDemonicExec.const (B := .exact) (d := rOne) (x := x.set rZero 0) hL hfit1
    have hx₁b : x₁.Bounded w := (hx.set (fits_zero w)).set hfit1
    have hx₁_base : x₁.regs rBase = base := by
      simp [x₁, RData.set, hbase]
    cases o with
    | query u =>
      obtain ⟨htag, _⟩ := harg
      have hc0 : (Cond.eq rTag rZero).Holds x₁.toData := by
        change x₁.regs rTag = x₁.regs rZero
        simp [x₁, RData.set, htag]
      obtain ⟨hex_ld, hx₂b⟩ := loadAtOffCode_exec (rAddr := rBase) (rDst := rCnt) (rTmp := rCur)
        hx₁b hL (eReg_ne (by decide)) hx₁_base hfit6
        (by simp only [x₁, RData.set_frontier, hrep.frontier_eq]; omega)
      set x₂ := (x₁.set rCur (base + 6)).set rCnt (x₁.mem (base + 6))
      set x₃ := x₂.set rZero 0
      have hex_z := RDemonicExec.const (B := .exact) (d := rZero) (x := x₂) hL (fits_zero w)
      have hc_cnt : (Cond.eq rCnt rZero).Holds x₃.toData := by
        change x₃.regs rCnt = x₃.regs rZero
        simp [x₃, x₂, x₁, RData.set, hrep.root_hdr.hdr_n]
      set y := (x₃.set rOutTag 0).set rOutVal 0
      have hex_out :=
        (RDemonicExec.const (B := .exact) (d := rOutTag) (x := x₃) hL (fits_zero w)).seq_eq
        (RDemonicExec.const (B := .exact) (d := rOutVal) (x := x₃.set rOutTag 0) hL (fits_zero w))
      have hyb : y.Bounded w := ((hx₂b.set (fits_zero w)).set (fits_zero w)).set (fits_zero w)
      have hex_q : RDemonicExec w L_peak inEpochQueryCode x₁ _ (· = y) :=
        hex_ld.seq_eq (hex_z.seq_eq (RDemonicExec.branch_pos hc_cnt hex_out))
      have hn'_eq : n' = 0 := hrep.card_eq
      refine ⟨y, _, s_z0.seq_eq (s_o1.seq_eq (RDemonicExec.branch_pos hc0 hex_q)),
        by simp [decode, y, RData.set, hs_none u],
        ?_, ?_, fun _ _ => rfl⟩
      · rw [hn'_eq]
        exact ⟨hyb, hrep.frontier_eq, hrep.root_hdr, hrep.fits_U, hrep.pos_U, hrep.pos_V,
          hrep.card_eq, hrep.vals_lt, hrep.epoch_inv,
          fun h0 => (Nat.not_lt_zero 0 h0).elim⟩
      · simp [y, x₃, x₂, RData.set, hx₁_base]
    | insert u v =>
      exfalso
      have hu_in : u ∈ Dictionary.dom s_abs' := by
        dsimp only [s_abs']; rw [Dictionary.dom_insert]; exact Finset.mem_insert_self u _
      have hn'_pos : 1 ≤ n' := Finset.card_pos.mpr ⟨u, hu_in⟩
      have hev' : EpochValid U n' 0 := hval.2
      rcases hev' with ⟨hn0, _⟩ | ⟨_, hnN, _, _⟩ <;> omega
    | delete u =>
      obtain ⟨htag, _⟩ := harg
      have hnc0 : ¬(Cond.eq rTag rZero).Holds x₁.toData := by
        change x₁.regs rTag ≠ x₁.regs rZero
        simp [x₁, RData.set, htag]
      have hnc1 : ¬(Cond.eq rTag rOne).Holds x₁.toData := by
        change x₁.regs rTag ≠ x₁.regs rOne
        simp [x₁, RData.set, htag]
      obtain ⟨hex_ld, hx₂b⟩ := loadAtOffCode_exec (rAddr := rBase) (rDst := rCnt) (rTmp := rCur)
        hx₁b hL (eReg_ne (by decide)) hx₁_base hfit6
        (by simp only [x₁, RData.set_frontier, hrep.frontier_eq]; omega)
      set x₂ := (x₁.set rCur (base + 6)).set rCnt (x₁.mem (base + 6))
      set x₃ := x₂.set rZero 0
      have hex_z := RDemonicExec.const (B := .exact) (d := rZero) (x := x₂) hL (fits_zero w)
      have hc_cnt : (Cond.eq rCnt rZero).Holds x₃.toData := by
        change x₃.regs rCnt = x₃.regs rZero
        simp [x₃, x₂, x₁, RData.set, hrep.root_hdr.hdr_n]
      set y := x₃.set rZero (x₃.regs rZero)
      have hex_nop := RDemonicExec.copy (B := .exact) (w := w) (d := rZero) (s := rZero)
        (x := x₃) hL
      have hx₃b : x₃.Bounded w := hx₂b.set (fits_zero w)
      have hyb : y.Bounded w := hx₃b.set (hx₃b.regs_fits rZero)
      have hex_d : RDemonicExec w L_peak inEpochDeleteCode x₁ _ (· = y) :=
        hex_ld.seq_eq (hex_z.seq_eq (RDemonicExec.branch_pos hc_cnt hex_nop))
      have hs_eq : s_abs' = s_abs := by
        dsimp only [s_abs']; funext k
        by_cases hk : k = u
        · subst hk; simp [hs_none k]
        · simp [Function.update_of_ne hk]
      have hn'_eq : n' = 0 := by dsimp only [n']; rw [hs_eq, hrep.card_eq]
      refine ⟨y, _,
        s_z0.seq_eq (s_o1.seq_eq
          (RDemonicExec.branch_neg hnc0 (RDemonicExec.branch_neg hnc1 hex_d))),
        rfl, ?_, ?_, fun _ _ => rfl⟩
      · rw [hn'_eq, hs_eq]
        exact ⟨hyb, hrep.frontier_eq, hrep.root_hdr, hrep.fits_U, hrep.pos_U, hrep.pos_V,
          hrep.card_eq, hrep.vals_lt, hrep.epoch_inv,
          fun h0 => (Nat.not_lt_zero 0 h0).elim⟩
      · simp [y, x₃, x₂, RData.set, hx₁_base]
  · obtain ⟨θ, hsplit⟩ := hrep.active_inv hn
    obtain ⟨y, steps, hex, hdec, hyb, hyf, hsplit_y, hy_base, hbelow, _⟩ :=
      inEpochOpCode_active_demonicExec o hrep.bounded hn hrep.epoch_inv hval hrep.frontier_eq
        hsplit hbase harg hfit
    exact ⟨y, steps, hex, hdec, compactedRep_of_split hyb hyf hval.2 hsplit_y, hy_base, hbelow⟩

/-- **In-Epoch Distributional Execution (`inEpochOpCode_execRCodeDist`):**
Lifts `inEpochOpCode_demonicExec` directly to `ExecRCodeDist`, certifying fault-freedom across all
adaptive adversaries, exact `CompactedRep` preservation, and `1 · OPT` peak hardware frontier
bounded by `base + Dynamic.succinctWords 1355 441 U V w (max n n')`. -/
theorem inEpochOpCode_execRCodeDist {U V w N n n_init base : ℕ}
    {s_abs : Dictionary.State U} (o : Dynamic.Op U) {x : RData rEpoch}
    (hrep : CompactedRep U V w N n n_init base s_abs x)
    (hval : InEpochValid V N s_abs o)
    (hbase : x.regs rBase = base) (harg : argMatch o x.regs)
    (hfit : Fits w (base + inEpochPeakWords V w N n s_abs o)) :
    let s_abs' := ((Dynamic.spec U V U).stepFn s_abs o).1
    let n' := (Dictionary.dom s_abs').card
    ∃ (y : RData rEpoch) (steps : ℕ),
      ExecRCodeDist w inEpochOpCode x (PMF.pure y) steps
        (base + Dynamic.succinctWords 1355 441 U V w (max n n')) ∧
      decode o y.regs = some ((Dynamic.spec U V U).stepFn s_abs o).2 ∧
      CompactedRep U V w N n' n_init base s_abs' y ∧
      y.regs rBase = base ∧
      (∀ addr < base, y.mem addr = x.mem addr) := by
  obtain ⟨hw, _, _⟩ := rootHeaderValid_bounds hrep.bounded hrep.root_hdr
  obtain ⟨y, steps, hex, hdec, hy_rep, hy_base, hbelow⟩ :=
    inEpochOpCode_demonicExec o hrep hval hbase harg hfit
  have hle_succ := Nat.add_le_add_left
    (inEpochPeakWords_le_succinctWords hw hrep.fits_U hrep.pos_U hrep.pos_V hrep.epoch_inv hval)
    base
  exact ⟨y, steps, (ExecRCodeDist.of_demonicExec hex).mono_peak hle_succ,
    hdec, hy_rep, hy_base, hbelow⟩

/-- **Stepwise `1 · OPT` Hardware-Frontier Certificate (`inEpochOpCode_peakFrontierLe`):**
Throughout execution of `inEpochOpCode.program rOutTag` on any valid in-epoch operation, the active
hardware word frontier never exceeds `base + Dynamic.succinctWords 1355 441 U V w (max n n')`. -/
theorem inEpochOpCode_peakFrontierLe {U V w N n n_init base : ℕ}
    {s_abs : Dictionary.State U} (o : Dynamic.Op U) {x : RData rEpoch}
    (hrep : CompactedRep U V w N n n_init base s_abs x)
    (hval : InEpochValid V N s_abs o)
    (hbase : x.regs rBase = base) (harg : argMatch o x.regs)
    (hfit : Fits w (base + inEpochPeakWords V w N n s_abs o)) :
    PeakFrontierLe w
      (base + Dynamic.succinctWords 1355 441 U V w
        (max n (Dictionary.dom ((Dynamic.spec U V U).stepFn s_abs o).1).card))
      (inEpochOpCode.program rOutTag) ⟨0, x⟩ := by
  obtain ⟨_, _, hex_dist, _, _, _, _⟩ :=
    inEpochOpCode_execRCodeDist o hrep hval hbase harg hfit
  exact (hex_dist.toExecRProgramDist rOutTag).peakFrontierLe

/-- **Uniform-Seed $O(1)$ Expected Amortized In-Epoch Bound (`inEpochOpCode_expected_amortized`):**
For any seed-indexed family `xOf : QuotHashSeed U N → RData rEpoch` representing `s_abs` in an
active epoch (`0 < n`, `EpochValid U n N`, `InEpochValid V N s_abs o`), `inEpochOpCode` transitions
each `xOf θ` to `yOf θ` in `stepsOf θ` instructions with expected amortized cost at most the
parameter-free constant `inEpochCharge` under `PMF.uniformOfFintype (QuotHashSeed U N)`. -/
theorem inEpochOpCode_expected_amortized {U V w N n n_init base : ℕ}
    {s_abs : Dictionary.State U} (o : Dynamic.Op U)
    (xOf : QuotHashSeed U N → RData rEpoch)
    (hn : 0 < n) (hev : EpochValid U n N) (hval : InEpochValid V N s_abs o)
    (hfit : Fits w (base + inEpochPeakWords V w N n s_abs o))
    (hx_bdd : ∀ θ, (xOf θ).Bounded w)
    (hx_fr : ∀ θ, (xOf θ).frontier = base + compactedEpochWords U V w N n)
    (hx_split : ∀ θ, CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨(xOf θ).mem, (xOf θ).frontier⟩)
    (hx_base : ∀ θ, (xOf θ).regs rBase = base)
    (hx_arg : ∀ θ, argMatch o (xOf θ).regs) :
    let s_abs' := ((Dynamic.spec U V U).stepFn s_abs o).1
    let n' := (Dictionary.dom s_abs').card
    let μ := PMF.uniformOfFintype (QuotHashSeed U N)
    ∃ (yOf : QuotHashSeed U N → RData rEpoch) (stepsOf : QuotHashSeed U N → ℕ),
      (∀ θ,
        RDemonicExec w (base + inEpochPeakWords V w N n s_abs o) inEpochOpCode
          (xOf θ) (stepsOf θ) (· = yOf θ) ∧
        decode o (yOf θ).regs = some ((Dynamic.spec U V U).stepFn s_abs o).2 ∧
        (yOf θ).Bounded w ∧
        (yOf θ).frontier = base + compactedEpochWords U V w N n' ∧
        CompactedSplitRep base (base + offCompItems U w N) U V w N n' n_init θ s_abs'
          ⟨(yOf θ).mem, (yOf θ).frontier⟩ ∧
        (yOf θ).regs rBase = base ∧
        (∀ addr < base, (yOf θ).mem addr = (xOf θ).mem addr)) ∧
      (∑' θ, μ θ * ((stepsOf θ + inEpochPotential U w N base (yOf θ) : ℕ) : ℝ≥0∞)) ≤
        (∑' θ, μ θ * (inEpochPotential U w N base (xOf θ) : ℝ≥0∞)) + inEpochCharge := by
  intro s_abs' n' μ
  have hex_all := fun θ =>
    inEpochOpCode_active_demonicExec o (hx_bdd θ) hn hev hval (hx_fr θ) (hx_split θ)
      (hx_base θ) (hx_arg θ) hfit
  choose yOf stepsOf hspec using hex_all
  refine ⟨yOf, stepsOf, fun θ => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := hspec θ
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · obtain ⟨hnN, _, hNU⟩ := epochValid_iff_capacity_bounds.mp hev
    obtain ⟨θ₀⟩ : Nonempty (QuotHashSeed U N) := inferInstance
    have hcard : (Dictionary.dom s_abs).card = n := (hx_split θ₀).card_eq
    have hS_le : ((Dictionary.dom s_abs).erase (opKey o)).card ≤ N :=
      (Finset.card_erase_le (s := Dictionary.dom s_abs) (a := opKey o)).trans (hcard ▸ hnN)
    have hpr_le :=
      tsum_uniform_probeExcess_reducedPolyHash_le_five hNU (Dictionary.dom s_abs) (opKey o) hS_le
    have hpt : ∀ θ,
        μ θ * ((stepsOf θ + inEpochPotential U w N base (yOf θ) : ℕ) : ℝ≥0∞) ≤
          μ θ * (inEpochPotential U w N base (xOf θ) : ℝ≥0∞) +
            (μ θ * (inEpochBaseCharge : ℝ≥0∞) +
              (12 * inEpochFactor : ℝ≥0∞) *
                (μ θ * (probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
                  (Dictionary.dom s_abs) (opKey o) : ℝ≥0∞))) := fun θ => by
      have hle_nat := (hspec θ).2.2.2.2.2.2.2
      have hle_enn : ((stepsOf θ + inEpochPotential U w N base (yOf θ) : ℕ) : ℝ≥0∞) ≤
          (inEpochPotential U w N base (xOf θ) : ℝ≥0∞) +
            ((inEpochBaseCharge : ℝ≥0∞) +
              (12 * inEpochFactor : ℝ≥0∞) *
                (probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
                  (Dictionary.dom s_abs) (opKey o) : ℝ≥0∞)) := by
        have hc := (Nat.cast_le (α := ℝ≥0∞)).mpr hle_nat
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc
        rw [add_assoc] at hc
        rw [Nat.cast_add]
        exact hc
      calc μ θ * ((stepsOf θ + inEpochPotential U w N base (yOf θ) : ℕ) : ℝ≥0∞)
          ≤ μ θ * ((inEpochPotential U w N base (xOf θ) : ℝ≥0∞) +
              ((inEpochBaseCharge : ℝ≥0∞) +
                (12 * inEpochFactor : ℝ≥0∞) *
                  (probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
                    (Dictionary.dom s_abs) (opKey o) : ℝ≥0∞))) :=
            by gcongr
        _ = μ θ * (inEpochPotential U w N base (xOf θ) : ℝ≥0∞) +
              (μ θ * (inEpochBaseCharge : ℝ≥0∞) +
                (12 * inEpochFactor : ℝ≥0∞) *
                  (μ θ * (probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
                    (Dictionary.dom s_abs) (opKey o) : ℝ≥0∞))) := by ring
    calc (∑' θ, μ θ * ((stepsOf θ + inEpochPotential U w N base (yOf θ) : ℕ) : ℝ≥0∞))
        ≤ ∑' θ, (μ θ * (inEpochPotential U w N base (xOf θ) : ℝ≥0∞) +
            (μ θ * (inEpochBaseCharge : ℝ≥0∞) +
              (12 * inEpochFactor : ℝ≥0∞) *
                (μ θ * (probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
                  (Dictionary.dom s_abs) (opKey o) : ℝ≥0∞)))) :=
          tsum_le_tsum hpt
      _ = (∑' θ, μ θ * (inEpochPotential U w N base (xOf θ) : ℝ≥0∞)) +
            ((∑' θ, μ θ * (inEpochBaseCharge : ℝ≥0∞)) +
              (12 * inEpochFactor : ℝ≥0∞) *
                ∑' θ, μ θ * (probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
                  (Dictionary.dom s_abs) (opKey o) : ℝ≥0∞)) := by
          rw [CompleteLattice.summable.tsum_add CompleteLattice.summable,
            CompleteLattice.summable.tsum_add CompleteLattice.summable, ENNReal.tsum_mul_left]
      _ ≤ (∑' θ, μ θ * (inEpochPotential U w N base (xOf θ) : ℝ≥0∞)) +
            ((inEpochBaseCharge : ℝ≥0∞) + (12 * inEpochFactor : ℝ≥0∞) * 5) := by
          rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
          gcongr
      _ = (∑' θ, μ θ * (inEpochPotential U w N base (xOf θ) : ℝ≥0∞)) + inEpochCharge := by
          unfold inEpochCharge
          push_cast
          ring

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
