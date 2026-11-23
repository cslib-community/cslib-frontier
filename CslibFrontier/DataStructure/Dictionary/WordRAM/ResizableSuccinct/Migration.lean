/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.ObliviousSequence
public import Mathlib.Data.Nat.Dist
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.SupportTsum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Single-Tape `1 · OPT` Capacity Migration and Trajectory-Relative Dispatcher

This module formalizes single-tape capacity migration and trajectory-relative operational dispatch
for the resizable succinct dynamic dictionary on the word-granular **Resizable Word RAM**
(`Cslib.WordRAM.Resizable`), combining the in-epoch dispatcher `inEpochOpCode` (`Dispatch`) with the
single-tape `1 · OPT` streaming rebuild `migrateActiveCode`, empty-to-active initializer
`initFirstEpochCode`, and singleton collapse `deleteLastOneCode` (`Migration.Exec`) into the unified
parameter-free operational dispatcher `resizableOpCode : RCode .exact rResize`
(`¬resizableOpCode.ReadsWidth`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.resizableOpCode`: unified parameter-free
  `RCode .exact rResize` dispatcher across `query`, `insert`, and `delete` at all capacities.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.EpochAnchorInv`, `EpochState`,
  `ReachedEpochsFit`: deterministic epoch-capacity trajectory `(dict, cap, initCount)` and
  trajectory-relative peak-frontier admissibility predicate.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.stepExactPeakWords`,
  `resizablePotential`, `resizableBaseCharge`, `resizableCharge`: exact stepwise peak word bound,
  combined hysteresis + migration potential, and parameter-free $O(1)$ expected amortized charge.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.LatentSeed`, `EpochRep`,
  `EpochSeqInv`: latent quotient-hash seed bundle and uniform-marginal sequence invariant.

## Main results

* `not_readsWidth_resizableOpCode`: `resizableOpCode` does not inspect the ambient word width `w`.
* `stepExactPeakWords_inEpoch_le_succinctWords`, `stepExactPeakWords_le_succinctWords`,
  `w_mul_stepExactPeakWords_le_bits`: strict `1 · OPT` peak hardware-frontier bounds (`1355, 441`
  in-epoch and `2699, 888` across capacity-doubling/halving migrations; never `2 · OPT`).
* `resizableOpCode_step_pointwise`: per-state `ExecRCodeDist` step specification with pointwise
  potential-amortized cost bound and uniform-seed preservation/resampling.
* `resizableOpCode_step_expected_amortized`, `resizableOpCode_steps_expected_amortized`:
  single-step and multi-step trajectory-relative expected amortized $O(1)$ execution bounds under
  `ReachedEpochsFit`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability
open scoped BigOperators ENNReal

/-! ## Section 1: ABI Register Wrappers and `RCode.rename epochEmb` Bridge -/

/-- Caller-overwritable input mask on `Fin rResize`: `false` on persistent `mBase` (`0`), `true`
on all other registers `1 .. rResize - 1`. -/
@[expose]
def resizableInput (i : Fin rResize) : Bool :=
  decide (0 < i.val)

@[simp]
theorem resizableInput_mBase : resizableInput mBase = false := by
  simp [resizableInput, mBase]

/-- Standalone register encoding for `Dynamic.Op U` on `Fin rResize`. -/
@[expose]
noncomputable def resizableEncode {U : ℕ} : Dynamic.Op U → Fin rResize → ℕ
  | .query u, r => if r = mTag then 0 else if r = mArgU then u.val else 0
  | .insert u v, r =>
    if r = mTag then 1 else if r = mArgU then u.val else if r = mArgV then v else 0
  | .delete u, r => if r = mTag then 2 else if r = mArgU then u.val else 0

/-- Entry argument-agreement predicate on `Fin rResize` (`mTag`, `mArgU`, `mArgV`). -/
@[expose]
noncomputable def resizableArgMatch {U : ℕ} : Dynamic.Op U → (Fin rResize → ℕ) → Prop
  | .query u, regs => regs mTag = 0 ∧ regs mArgU = u.val
  | .insert u v, regs => regs mTag = 1 ∧ regs mArgU = u.val ∧ regs mArgV = v
  | .delete u, regs => regs mTag = 2 ∧ regs mArgU = u.val

private theorem argMatch_comp_epochEmb {U : ℕ} (o : Dynamic.Op U) (regs : Fin rResize → ℕ)
    (h : resizableArgMatch o regs) : argMatch o (regs ∘ epochEmb) := by
  cases o with
  | query u =>
    exact ⟨by change regs (epochEmb rTag) = 0; rw [epochEmb_rTag]; exact h.1,
      by change regs (epochEmb rArgU) = u.val; rw [epochEmb_rArgU]; exact h.2⟩
  | insert u v =>
    exact ⟨by change regs (epochEmb rTag) = 1; rw [epochEmb_rTag]; exact h.1,
      by change regs (epochEmb rArgU) = u.val; rw [epochEmb_rArgU]; exact h.2.1,
      by change regs (epochEmb rArgV) = v; rw [epochEmb_rArgV]; exact h.2.2⟩
  | delete u =>
    exact ⟨by change regs (epochEmb rTag) = 2; rw [epochEmb_rTag]; exact h.1,
      by change regs (epochEmb rArgU) = u.val; rw [epochEmb_rArgU]; exact h.2⟩

/-- Output decoder on `Fin rResize`, delegating to `decode` along `epochEmb`. -/
@[expose]
noncomputable def resizableDecode {U : ℕ} (o : Dynamic.Op U) (regs : Fin rResize → ℕ) :
    Option o.Result :=
  decode o (regs ∘ epochEmb)

theorem resizableArgMatch_prepare {U : ℕ} (o : Dynamic.Op U) (regs : Fin rResize → ℕ) :
    resizableArgMatch o (fun i => if resizableInput i then resizableEncode o i else regs i) := by
  have ht : resizableInput mTag = true := by simp [resizableInput, mTag]
  have hu : resizableInput mArgU = true := by simp [resizableInput, mArgU]
  have hv : resizableInput mArgV = true := by simp [resizableInput, mArgV]
  cases o with
  | query u =>
    exact ⟨by simp [resizableEncode, ht],
      by simp [resizableEncode, hu, show mArgU ≠ mTag from mReg_ne (by decide)]⟩
  | insert u v =>
    exact ⟨by simp [resizableEncode, ht],
      by simp [resizableEncode, hu, show mArgU ≠ mTag from mReg_ne (by decide)],
      by simp [resizableEncode, hv, show mArgV ≠ mTag from mReg_ne (by decide),
          show mArgV ≠ mArgU from mReg_ne (by decide)]⟩
  | delete u =>
    exact ⟨by simp [resizableEncode, ht],
      by simp [resizableEncode, hu, show mArgU ≠ mTag from mReg_ne (by decide)]⟩

theorem fits_resizableEncode {U V w : ℕ} {s_abs : Dictionary.State U} {o : Dynamic.Op U}
    (hw2 : Fits w 2) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hval : (Dynamic.spec U V U).valid s_abs o) :
    ∀ i, resizableInput i = true → Fits w (resizableEncode o i) := by
  intro i _
  cases o with
  | query u =>
    dsimp only [resizableEncode]
    split_ifs <;> [exact fits_zero w; exact u.isLt.trans hU; exact fits_zero w]
  | insert u v =>
    have hv_lt : v < V := hval.2
    dsimp only [resizableEncode]
    split_ifs
    · exact hw2.of_le (by decide)
    · exact u.isLt.trans hU
    · exact lt_of_lt_of_le hv_lt hV
    · exact fits_zero w
  | delete u =>
    dsimp only [resizableEncode]
    split_ifs <;> [exact hw2; exact u.isLt.trans hU; exact fits_zero w]

/-- Lift `inEpochOpCode_active_demonicExec` from `Fin rEpoch` to `Fin rResize` along `epochEmb`. -/
private theorem inEpochOpCode_rename_active_demonicExec {U V w N n n_init base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} (o : Dynamic.Op U) {x : RData rResize}
    (hx : x.Bounded w) (hn : 0 < n) (hev : EpochValid U n N)
    (hval : InEpochValid V N s_abs o)
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base) (harg : resizableArgMatch o x.regs)
    (hfit : Fits w (base + inEpochPeakWords V w N n s_abs o)) :
    let s_abs' := ((Dynamic.spec U V U).stepFn s_abs o).1
    let n' := (Dictionary.dom s_abs').card
    ∃ (z : RData rResize) (steps : ℕ),
      RDemonicExec w (base + inEpochPeakWords V w N n s_abs o)
        (inEpochOpCode.rename epochEmb) x steps (· = z) ∧
      resizableDecode o z.regs = some ((Dynamic.spec U V U).stepFn s_abs o).2 ∧
      z.Bounded w ∧
      z.frontier = base + compactedEpochWords U V w N n' ∧
      CompactedSplitRep base (base + offCompItems U w N) U V w N n' n_init θ s_abs'
        ⟨z.mem, z.frontier⟩ ∧
      z.regs mBase = base ∧
      (∀ addr < base, z.mem addr = x.mem addr) ∧
      steps + inEpochPotential U w N base z ≤
        inEpochPotential U w N base x + inEpochBaseCharge +
          (12 * inEpochFactor) *
            probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2
              (Dictionary.dom s_abs) (opKey o) := by
  intro s_abs' n'
  have hbase_sub : (x.comap epochEmb).regs rBase = base := by
    change x.regs (epochEmb rBase) = base; rwa [epochEmb_rBase]
  obtain ⟨y, steps, hex, hdec, hyb, hyf, hsplit_y, hy_base, hbelow, hcost⟩ :=
    inEpochOpCode_active_demonicExec o (hx.comap epochEmb) hn hev hval hfr hsplit
      hbase_sub (argMatch_comp_epochEmb o x.regs harg) hfit
  refine ⟨y.extend epochEmb x, steps, hex.rename_eq epochEmb_injective, ?_,
    hyb.extend epochEmb_injective hx, hyf, hsplit_y, ?_, hbelow, hcost⟩
  · dsimp only [resizableDecode]
    have hregs : (y.extend epochEmb x).regs ∘ epochEmb = y.regs :=
      congrArg RData.regs (RData.comap_extend epochEmb_injective y x)
    rwa [hregs]
  · rw [← epochEmb_rBase, RData.extend_regs_apply epochEmb_injective]
    exact hy_base

/-! ## Section 2: Unified Parameter-Free Operational Dispatcher (`resizableOpCode`) -/

private noncomputable abbrev mNNew : Fin rResize := mReg 149
private noncomputable abbrev mTmpA : Fin rResize := mReg 156
private noncomputable abbrev mTmpB : Fin rResize := mReg 157

private noncomputable def resizableInsertActiveCode : RCode .exact rResize :=
  .seq (loadAtOffCode mBase mNNew mCur 5) <|
  .seq (loadAtOffCode mBase mTmpA mCur 0) <|
  .branch (.eq mCnt mNNew)
    (.branch (.lt mTmpA mNNew)
      (inEpochOpCode.rename epochEmb)
      (.seq migrateActiveCode (inEpochOpCode.rename epochEmb)))
    (inEpochOpCode.rename epochEmb)

private noncomputable def resizableDeleteGeTwoCode : RCode .exact rResize :=
  .seq (loadAtOffCode mBase mNNew mCur 5) <|
  .seq (.op (.exactBin .sub mTmpA mCnt mOne)) <|
  .seq (.op (.exactBin .sub mTmpB mNNew mOne)) <|
  .seq (.op (.const mCur 2)) <|
  .seq (.op (.exactBin .shiftRight mTmpB mTmpB mCur)) <|
  .branch (.lt mTmpB mTmpA)
    (inEpochOpCode.rename epochEmb)
    (.seq migrateActiveCode (inEpochOpCode.rename epochEmb))

/-- Unified parameter-free operational dispatcher (`RCode .exact rResize`) for `query`, `insert`,
and `delete` across empty, in-epoch, `0 → 1`, `1 → 0`, and capacity-doubling/halving states. -/
noncomputable def resizableOpCode : RCode .exact rResize :=
  .seq (loadAtOffCode mBase mCnt mCur 6) <|
  .seq (.op (.const mZero 0)) <|
  .seq (.op (.const mOne 1)) <|
  .branch (.eq mCnt mZero)
    (.branch (.eq mTag mZero)
      (.seq (.op (.const mOutTag 0)) (.op (.const mOutVal 0)))
      (.branch (.eq mTag mOne)
        initFirstEpochCode
        (.op (.copy mZero mZero))))
    (.branch (.eq mTag mZero)
      (inEpochOpCode.rename epochEmb)
      (.branch (.eq mTag mOne)
        resizableInsertActiveCode
        (.branch (.eq mCnt mOne)
          deleteLastOneCode
          resizableDeleteGeTwoCode)))

/-- `resizableOpCode` does not inspect the ambient word width `w` (`¬resizableOpCode.ReadsWidth`).
-/
theorem not_readsWidth_resizableOpCode : ¬resizableOpCode.ReadsWidth := by
  have hin : ¬(inEpochOpCode.rename epochEmb).ReadsWidth := by
    rw [RCode.readsWidth_rename]; exact not_readsWidth_inEpochOpCode
  simp [resizableOpCode, resizableInsertActiveCode, resizableDeleteGeTwoCode,
    RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    not_readsWidth_loadAtOffCode, not_readsWidth_initFirstEpochCode,
    not_readsWidth_deleteLastOneCode, not_readsWidth_migrateActiveCode, hin]

/-! ## Section 3: Epoch Trajectory, `1 · OPT` Peak Space, Potential, and Charges -/

/-- Epoch capacity and anchor-count invariant (`N = targetCap U n_init`):
`EpochValid U n N`, `N = targetCap U n_init`, `n = 0 ↔ n_init = 0`, and `n_init ≤ U`. -/
@[expose]
def EpochAnchorInv (U n N n_init : ℕ) : Prop :=
  EpochValid U n N ∧ N = targetCap U n_init ∧ (n = 0 ↔ n_init = 0) ∧ n_init ≤ U

/-- Deterministic post-step epoch capacity `N'` on `o : Dynamic.Op U`. -/
@[expose]
def nextEpochCap {U : ℕ} (N : ℕ) (s_abs : Dictionary.State U) (o : Dynamic.Op U) : ℕ :=
  let n := (Dictionary.dom s_abs).card
  match o with
  | .query _ => N
  | .insert _ _ =>
    if n = 0 then targetCap U 1
    else if n = N ∧ N < U then targetCap U n
    else N
  | .delete u =>
    if n = 0 then 0
    else if n = 1 then if (s_abs u).isSome then 0 else N
    else if 4 * (n - 1) < N then targetCap U n
    else N

/-- Deterministic post-step epoch anchor count `n_init'` on `o : Dynamic.Op U`. -/
@[expose]
def nextEpochInit {U : ℕ} (N n_init : ℕ) (s_abs : Dictionary.State U) (o : Dynamic.Op U) : ℕ :=
  let n := (Dictionary.dom s_abs).card
  match o with
  | .query _ => n_init
  | .insert _ _ =>
    if n = 0 then 1
    else if n = N ∧ N < U then n
    else n_init
  | .delete u =>
    if n = 0 then 0
    else if n = 1 then if (s_abs u).isSome then 0 else n_init
    else if 4 * (n - 1) < N then n
    else n_init

/-- Deterministic epoch-trajectory state `(dict, cap, initCount)`. -/
structure EpochState (U : ℕ) where
  /-- Current abstract dictionary `Fin U → Option ℕ`. -/
  dict : Dictionary.State U
  /-- Current epoch capacity (`0` when empty, `targetCap U initCount` when active). -/
  cap : ℕ
  /-- Live key count when the current epoch was initialized (`0` when empty). -/
  initCount : ℕ

/-- Initial empty `EpochState`. -/
@[expose]
def EpochState.empty (U : ℕ) : EpochState U where
  dict := Dictionary.empty U
  cap := 0
  initCount := 0

/-- Single-operation transition of `EpochState U`. -/
@[expose]
def EpochState.step {U : ℕ} (V : ℕ) (st : EpochState U) (o : Dynamic.Op U) : EpochState U where
  dict := ((Dynamic.spec U V U).stepFn st.dict o).1
  cap := nextEpochCap st.cap st.dict o
  initCount := nextEpochInit st.cap st.initCount st.dict o

/-- Epoch state reached after executing `ops : List (Dynamic.Op U)` from `st`. -/
@[expose]
def EpochState.run {U : ℕ} (V : ℕ) (st : EpochState U) : List (Dynamic.Op U) → EpochState U
  | [] => st
  | o :: os => EpochState.run V (st.step V o) os

@[simp]
theorem EpochState.run_nil {U : ℕ} (V : ℕ) (st : EpochState U) :
    EpochState.run V st [] = st := rfl

@[simp]
theorem EpochState.run_cons {U : ℕ} (V : ℕ) (st : EpochState U) (o : Dynamic.Op U)
    (os : List (Dynamic.Op U)) :
    EpochState.run V st (o :: os) = EpochState.run V (st.step V o) os := rfl

theorem EpochState.run_append {U : ℕ} (V : ℕ) (st : EpochState U)
    (xs ys : List (Dynamic.Op U)) :
    EpochState.run V st (xs ++ ys) = EpochState.run V (EpochState.run V st xs) ys := by
  induction xs generalizing st with
  | nil => rfl
  | cons o os ih => exact ih (st.step V o)

theorem EpochState.dict_run {U : ℕ} (V : ℕ) (st : EpochState U) (ops : List (Dynamic.Op U)) :
    (EpochState.run V st ops).dict = ((Dynamic.spec U V U).run st.dict ops).1 := by
  induction ops generalizing st with
  | nil => rfl
  | cons o os ih =>
    rw [EpochState.run_cons, ih]
    rfl

theorem epochAnchorInv_empty (U : ℕ) :
    EpochAnchorInv U (Dictionary.dom (EpochState.empty U).dict).card
      (EpochState.empty U).cap (EpochState.empty U).initCount := by
  refine ⟨Or.inl ⟨?_, rfl⟩, ?_, ⟨fun _ => rfl, fun _ => ?_⟩, Nat.zero_le U⟩
  · simp [EpochState.empty, Dictionary.dom_empty]
  · simp [EpochState.empty, targetCap]
  · simp [EpochState.empty, Dictionary.dom_empty]

private theorem dict_eq_empty_of_card_zero {U : ℕ} {s_abs : Dictionary.State U}
    (h0 : (Dictionary.dom s_abs).card = 0) :
    s_abs = Dictionary.empty U := by
  have hdom : Dictionary.dom s_abs = ∅ := Finset.card_eq_zero.mp h0
  funext u
  by_contra hne
  have hmem : u ∈ Dictionary.dom s_abs :=
    Dictionary.mem_dom_iff_isSome.mpr (Option.ne_none_iff_isSome.mp hne)
  rw [hdom] at hmem
  exact Finset.notMem_empty u hmem

private theorem card_dom_insert_bounds {U : ℕ} (s_abs : Dictionary.State U) (u : Fin U) (v : ℕ) :
    (Dictionary.dom s_abs).card ≤ (Dictionary.dom (Function.update s_abs u (some v))).card ∧
    (Dictionary.dom (Function.update s_abs u (some v))).card ≤ (Dictionary.dom s_abs).card + 1 := by
  rw [Dictionary.dom_insert]
  exact ⟨Finset.card_le_card (Finset.subset_insert u _), Finset.card_insert_le u _⟩

private theorem card_dom_insert_eq_of_card_eq_U {U : ℕ} {s_abs : Dictionary.State U}
    (hU : (Dictionary.dom s_abs).card = U) (u : Fin U) (v : ℕ) :
    (Dictionary.dom (Function.update s_abs u (some v))).card = U := by
  have huniv : Dictionary.dom s_abs = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hU])
  rw [Dictionary.dom_insert, huniv, Finset.insert_eq_of_mem (Finset.mem_univ u)]
  simp

private theorem card_dom_delete_bounds {U : ℕ} (s_abs : Dictionary.State U) (u : Fin U) :
    (Dictionary.dom s_abs).card - 1 ≤ (Dictionary.dom (Function.update s_abs u none)).card ∧
    (Dictionary.dom (Function.update s_abs u none)).card ≤ (Dictionary.dom s_abs).card := by
  by_cases hu : (s_abs u).isSome
  · rw [Dynamic.card_dom_delete_eq_of_isSome hu]
    exact ⟨le_rfl, Nat.sub_le _ _⟩
  · have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hu
    rw [Dynamic.card_dom_delete_eq_of_eq_none hnone]
    exact ⟨Nat.sub_le _ _, le_rfl⟩

theorem epochAnchorInv_step {U V : ℕ} {st : EpochState U} {o : Dynamic.Op U}
    (hU_pos : 0 < U)
    (hinv : EpochAnchorInv U (Dictionary.dom st.dict).card st.cap st.initCount)
    (hval : (Dynamic.spec U V U).valid st.dict o) :
    let st' := st.step V o
    EpochAnchorInv U (Dictionary.dom st'.dict).card st'.cap st'.initCount := by
  intro st'
  obtain ⟨hev, hcap_eq, hzero_iff, hinit_le⟩ := hinv
  set n := (Dictionary.dom st.dict).card
  cases o with
  | query u =>
    exact ⟨hev, hcap_eq, hzero_iff, hinit_le⟩
  | insert u v =>
    dsimp only [st', EpochState.step, nextEpochCap, nextEpochInit]
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0, ite_eq_left hn0]
      have hs_emp := dict_eq_empty_of_card_zero hn0
      have hcard1 : (Dictionary.dom (Function.update st.dict u (some v))).card = 1 := by
        rw [hs_emp, Dictionary.dom_insert, Dictionary.dom_empty]; rfl
      rw [hcard1]
      exact ⟨epochValid_targetCap hU_pos, rfl, by decide, hU_pos⟩
    · rw [ite_eq_right hn0, ite_eq_right hn0]
      have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn0
      have hn_le_cap : n ≤ st.cap := by rcases hev with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
      have hcap_le_4n : st.cap ≤ 4 * n := by rcases hev with ⟨h0, _⟩ | ⟨_, _, h4, _⟩ <;> omega
      have hcap_le_U : st.cap ≤ U := by rcases hev with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
      obtain ⟨hn_le_n', hn'_le_n1⟩ := card_dom_insert_bounds st.dict u v
      by_cases hmig : n = st.cap ∧ st.cap < U
      · rw [ite_eq_left hmig, ite_eq_left hmig]
        have hn_lt_U : n < U := hmig.1 ▸ hmig.2
        have htc_ge : n + 1 ≤ targetCap U n := by
          unfold targetCap; rw [ite_eq_right hn0]; exact le_min (by omega) hn_lt_U
        have htc_2n : targetCap U n ≤ 2 * n := by
          unfold targetCap; rw [ite_eq_right hn0]; exact min_le_left _ _
        have htc_U : targetCap U n ≤ U := by
          unfold targetCap; rw [ite_eq_right hn0]; exact min_le_right _ _
        dsimp only [n] at htc_ge htc_2n htc_U
        exact ⟨Or.inr ⟨by omega, hn'_le_n1.trans htc_ge, by omega, htc_U⟩,
          rfl, ⟨by omega, by omega⟩, hn_lt_U.le⟩
      · rw [ite_eq_right hmig, ite_eq_right hmig]
        have hn'_le_cap : (Dictionary.dom (Function.update st.dict u (some v))).card ≤ st.cap := by
          rcases lt_or_eq_of_le hn_le_cap with hlt | heq_n
          · omega
          · have hcap_U : st.cap = U := by omega
            rw [card_dom_insert_eq_of_card_eq_U (heq_n.trans hcap_U), hcap_U]
        exact ⟨Or.inr ⟨by omega, hn'_le_cap, by omega, hcap_le_U⟩,
          hcap_eq, ⟨fun h => absurd h (by omega), fun h => absurd (hzero_iff.mpr h) hn0⟩, hinit_le⟩
  | delete u =>
    dsimp only [st', EpochState.step, nextEpochCap, nextEpochInit]
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0, ite_eq_left hn0]
      have hs_emp := dict_eq_empty_of_card_zero hn0
      have hcard0 : (Dictionary.dom (Function.update st.dict u none)).card = 0 := by
        rw [hs_emp, Dynamic.dom_delete, Dictionary.dom_empty]; rfl
      rw [hcard0]
      exact ⟨Or.inl ⟨rfl, rfl⟩, by simp [targetCap], ⟨fun _ => rfl, fun _ => rfl⟩, Nat.zero_le U⟩
    · rw [ite_eq_right hn0, ite_eq_right hn0]
      by_cases hn1 : n = 1
      · rw [ite_eq_left hn1, ite_eq_left hn1]
        by_cases hsome : (st.dict u).isSome
        · rw [ite_eq_left hsome, ite_eq_left hsome]
          have hcard0 : (Dictionary.dom (Function.update st.dict u none)).card = 0 := by
            rw [Dynamic.card_dom_delete_eq_of_isSome hsome]; omega
          rw [hcard0]
          exact ⟨Or.inl ⟨rfl, rfl⟩, by simp [targetCap], ⟨fun _ => rfl, fun _ => rfl⟩,
            Nat.zero_le U⟩
        · rw [ite_eq_right hsome, ite_eq_right hsome]
          have hnone : st.dict u = none := Option.not_isSome_iff_eq_none.mp hsome
          have hcard1 : (Dictionary.dom (Function.update st.dict u none)).card = n :=
            Dynamic.card_dom_delete_eq_of_eq_none hnone
          rw [hcard1]
          exact ⟨hev, hcap_eq, hzero_iff, hinit_le⟩
      · rw [ite_eq_right hn1, ite_eq_right hn1]
        have hn2 : 2 ≤ n := by omega
        have hn_le_cap : n ≤ st.cap := by rcases hev with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
        have hcap_le_U : st.cap ≤ U := by rcases hev with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
        obtain ⟨hn1_le_n', hn'_le_n⟩ := card_dom_delete_bounds st.dict u
        by_cases hmig : 4 * (n - 1) < st.cap
        · rw [ite_eq_left hmig, ite_eq_left hmig]
          have hnU : n ≤ U := hn_le_cap.trans hcap_le_U
          have htc_ge : n ≤ targetCap U n := by
            unfold targetCap; rw [ite_eq_right hn0]; exact le_min (by omega) hnU
          have htc_2n : targetCap U n ≤ 2 * n := by
            unfold targetCap; rw [ite_eq_right hn0]; exact min_le_left _ _
          have htc_U : targetCap U n ≤ U := by
            unfold targetCap; rw [ite_eq_right hn0]; exact min_le_right _ _
          dsimp only [n] at htc_ge htc_2n htc_U
          exact ⟨Or.inr ⟨by omega, hn'_le_n.trans htc_ge, by omega, htc_U⟩,
            rfl, ⟨by omega, by omega⟩, hnU⟩
        · rw [ite_eq_right hmig, ite_eq_right hmig]
          exact ⟨Or.inr ⟨by omega, hn'_le_n.trans hn_le_cap, by omega, hcap_le_U⟩,
            hcap_eq, ⟨fun h => absurd h (by omega), fun h => absurd (hzero_iff.mpr h) hn0⟩,
            hinit_le⟩

/-- Exact peak hardware word footprint above `base` during `resizableOpCode` on `o`. -/
@[expose]
def stepExactPeakWords {U : ℕ} (V w N : ℕ) (s_abs : Dictionary.State U)
    (o : Dynamic.Op U) : ℕ :=
  let n := (Dictionary.dom s_abs).card
  match o with
  | .query u => inEpochPeakWords V w N n s_abs (.query u)
  | .insert u v =>
    if n = 0 then compactedEpochWords U V w (targetCap U 1) 1
    else if n = N ∧ N < U then
      max (migratePeakWords U V w N n)
          (inEpochPeakWords V w (targetCap U n) n s_abs (.insert u v))
    else inEpochPeakWords V w N n s_abs (.insert u v)
  | .delete u =>
    if n = 0 then compactedEpochWords U V w 0 0
    else if n = 1 then compactedEpochWords U V w N 1
    else if 4 * (n - 1) < N then
      max (migratePeakWords U V w N n)
          (inEpochPeakWords V w (targetCap U n) n s_abs (.delete u))
    else inEpochPeakWords V w N n s_abs (.delete u)

private theorem succinctWords_mono_const {C₁ C₂ C₀₁ C₀₂ U V w m : ℕ}
    (hC : C₁ ≤ C₂) (hC₀ : C₀₁ ≤ C₀₂) :
    Dynamic.succinctWords C₁ C₀₁ U V w m ≤ Dynamic.succinctWords C₂ C₀₂ U V w m := by
  unfold Dynamic.succinctWords
  have hmul : C₁ * m * Dynamic.logLogFactor m ≤ C₂ * m * Dynamic.logLogFactor m :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC)
  exact Nat.add_le_add (Nat.div_le_div_right (by omega)) hC₀

private theorem quotientBits_le_succ_add_one (U : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    quotientBits U n ≤ quotientBits U (n + 1) + 1 := by
  have hlt_pow : 2 * n < 2 ^ (Nat.log 2 n + 2) := by
    have h1 := Nat.lt_pow_succ_log_self Nat.one_lt_two n
    rw [Nat.pow_succ']
    omega
  have hlog_2n : Nat.log 2 (2 * n) ≤ Nat.log 2 n + 1 :=
    Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hlt_pow)
  have hlog_n1 : Nat.log 2 (n + 1) ≤ Nat.log 2 n + 1 :=
    (Nat.log_mono_right (by omega : n + 1 ≤ 2 * n)).trans hlog_2n
  have hll : Dynamic.logLogFactor n ≤ Dynamic.logLogFactor (n + 1) :=
    Dynamic.logLogFactor_mono (Nat.le_succ n)
  unfold quotientBits bucketBits
  omega

private theorem migratePeakWords_le_succinctWords_succ {U V w N_old n : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hn : 1 ≤ n) (hn_eq : n = N_old) (hN_lt : N_old < U) :
    migratePeakWords U V w N_old n ≤ Dynamic.succinctWords 2699 888 U V w (n + 1) := by
  subst hn_eq
  have hn1_U : n + 1 ≤ U := hN_lt
  set N_new := targetCap U n
  have hN_new_ge : n + 1 ≤ N_new := by
    unfold N_new targetCap; rw [ite_eq_right (by omega)]; exact le_min (by omega) hN_lt
  have hN_new_2n : N_new ≤ 2 * n := by
    unfold N_new targetCap; rw [ite_eq_right (by omega)]; exact min_le_left _ _
  have hN_new_U : N_new ≤ U := by
    unfold N_new targetCap; rw [ite_eq_right (by omega)]; exact min_le_right _ _
  have hll_mono : Dynamic.logLogFactor n ≤ Dynamic.logLogFactor (n + 1) :=
    Dynamic.logLogFactor_mono (Nat.le_succ n)
  have hm_le : 1344 * n * Dynamic.logLogFactor n ≤ 1344 * (n + 1) * Dynamic.logLogFactor (n + 1) :=
    Nat.mul_le_mul (by omega) hll_mono
  have hq_old : quotientBits U n ≤ quotientBits U (n + 1) + 6 :=
    (quotientBits_le_succ_add_one U hn).trans (by omega)
  have hq_new : quotientBits U N_new ≤ quotientBits U (n + 1) + 6 :=
    quotientBits_le_add_six_of_le_four_mul U hN_new_ge (by omega)
  have hqv_opt := quotient_val_bits_le_optBits (U := U) (V := V) (n := n + 1)
  have hll_n1 := Dynamic.one_le_logLogFactor (n + 1)
  have h_ibits : ∀ N_k, quotientBits U N_k ≤ quotientBits U (n + 1) + 6 →
      compactedItemWords U V w N_k n ≤
        (Dynamic.optBits U V (n + 1) + 11 * (n + 1) * Dynamic.logLogFactor (n + 1) + w - 1) / w +
          2 := by
    intro N_k hqk
    have hm1 : n * (quotientBits U N_k + valBits V) ≤
        (n + 1) * (quotientBits U (n + 1) + valBits V) + 6 * (n + 1) := by
      calc n * (quotientBits U N_k + valBits V)
          ≤ (n + 1) * (quotientBits U (n + 1) + 6 + valBits V) :=
            Nat.mul_le_mul (Nat.le_succ n) (by omega)
        _ = (n + 1) * (quotientBits U (n + 1) + valBits V) + 6 * (n + 1) := by ring
    have h6 : 6 * (n + 1) ≤ 6 * (n + 1) * Dynamic.logLogFactor (n + 1) := by
      calc 6 * (n + 1) = 6 * (n + 1) * 1 := by ring
        _ ≤ 6 * (n + 1) * Dynamic.logLogFactor (n + 1) := by gcongr
    have hnum0 : n * (quotientBits U N_k + valBits V) ≤
        Dynamic.optBits U V (n + 1) + 11 * (n + 1) * Dynamic.logLogFactor (n + 1) := by
      linarith only [hm1, hqv_opt, h6]
    have hnum : n * (quotientBits U N_k + valBits V) + w - 1 ≤
        Dynamic.optBits U V (n + 1) + 11 * (n + 1) * Dynamic.logLogFactor (n + 1) + w - 1 := by
      omega
    unfold compactedItemWords
    exact Nat.add_le_add_right (Nat.div_le_div_right hnum) 2
  have har : migrateArenaWords U V w n N_new n ≤
      (Dynamic.optBits U V (n + 1) + 11 * (n + 1) * Dynamic.logLogFactor (n + 1) + w - 1) / w +
        8 := by
    unfold migrateArenaWords
    have hmax := max_le (h_ibits n hq_old) (h_ibits N_new hq_new)
    omega
  have h_meta_div : ∀ N_k, N_k ≤ 4 * n → N_k ≤ U →
      offCompItems U w N_k ≤
        (1344 * (n + 1) * Dynamic.logLogFactor (n + 1) + w - 1) / w + 439 :=
    fun N_k hN4 hNU =>
      offCompItems_le_div_metaBits hw hNU hU.le (by omega : N_k ≤ 4 * (n + 1))
  have hm_old := h_meta_div n (by omega) hN_lt.le
  have hm_new := h_meta_div N_new (by omega) hN_new_U
  set M := 1344 * (n + 1) * Dynamic.logLogFactor (n + 1)
  set I := Dynamic.optBits U V (n + 1) + 11 * (n + 1) * Dynamic.logLogFactor (n + 1)
  have hc1 := div_add_div_le (a := M + w - 1) (b := M + w - 1) hw
  have hc1' : (M + w - 1) / w + (M + w - 1) / w ≤ (M + M + w - 1) / w + 1 :=
    hc1.trans ((Nat.div_le_div_right (b := M + M + w - 1 + 1 * w) (by omega)).trans_eq
      (Nat.add_mul_div_right (M + M + w - 1) 1 hw))
  have hc2 := div_add_div_le (a := M + M + w - 1) (b := I + w - 1) hw
  have hc2' : (M + M + w - 1) / w + (I + w - 1) / w ≤ (M + M + I + w - 1) / w + 1 :=
    hc2.trans ((Nat.div_le_div_right (b := M + M + I + w - 1 + 1 * w) (by omega)).trans_eq
      (Nat.add_mul_div_right (M + M + I + w - 1) 1 hw))
  have htot : M + M + I =
      Dynamic.optBits U V (n + 1) + 2699 * (n + 1) * Dynamic.logLogFactor (n + 1) := by
    dsimp only [M, I]; ring
  rw [htot] at hc2'
  unfold migratePeakWords Dynamic.succinctWords
  dsimp only [N_new] at hm_new har
  omega

/-- **`1 · OPT` Stepwise Peak Word-Space Bound (`stepExactPeakWords_le_succinctWords`):**
Across **every** admissible operation `o` (in-epoch, `0 → 1`, `1 → 0`, capacity-doubling, and
capacity-halving migrations), `stepExactPeakWords V w N s_abs o` never exceeds
`Dynamic.succinctWords 2699 888 U V w (max n n')` — strictly `1 · OPT(U, V, max n n')` plus
`O((max n n') log log (max n n'))` bits, never `2 · OPT`. -/
theorem stepExactPeakWords_le_succinctWords {U V w N : ℕ}
    {s_abs : Dictionary.State U} {o : Dynamic.Op U}
    (hw : 0 < w) (hU : Fits w U) (hU_pos : 0 < U) (hV_pos : 0 < V)
    (hev : EpochValid U (Dictionary.dom s_abs).card N)
    (hval : (Dynamic.spec U V U).valid s_abs o) :
    let n := (Dictionary.dom s_abs).card
    let n' := (Dictionary.dom ((Dynamic.spec U V U).stepFn s_abs o).1).card
    stepExactPeakWords V w N s_abs o ≤ Dynamic.succinctWords 2699 888 U V w (max n n') := by
  intro n n'
  have hlift : ∀ m, Dynamic.succinctWords 1355 441 U V w m ≤
      Dynamic.succinctWords 2699 888 U V w m :=
    fun _ => succinctWords_mono_const (by decide) (by decide)
  cases o with
  | query u =>
    exact (inEpochPeakWords_le_succinctWords hw hU hU_pos hV_pos hev ⟨hval, hev⟩).trans (hlift _)
  | insert u v =>
    dsimp only [stepExactPeakWords]
    change (if n = 0 then _ else _) ≤ _
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0]
      have hs_emp := dict_eq_empty_of_card_zero hn0
      have hn'1 : n' = 1 := by
        dsimp only [n', Dynamic.spec, StateTransitionSpec.stepFn, Dynamic.step]
        rw [hs_emp, Dictionary.dom_insert, Dictionary.dom_empty]; rfl
      have hmax : max n n' = 1 := by omega
      rw [hmax]
      exact (compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos
        (epochValid_targetCap hU_pos)).trans (hlift 1)
    · rw [ite_eq_right hn0]
      have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn0
      have hn_le_cap : n ≤ N := by rcases hev with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
      have hcap_le_4n : N ≤ 4 * n := by rcases hev with ⟨h0, _⟩ | ⟨_, _, h4, _⟩ <;> omega
      have hcap_le_U : N ≤ U := by rcases hev with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
      obtain ⟨hn_le_n', hn'_le_n1⟩ := card_dom_insert_bounds s_abs u v
      change n ≤ n' at hn_le_n'
      change n' ≤ n + 1 at hn'_le_n1
      by_cases hmig : n = N ∧ N < U
      · rw [ite_eq_left hmig]
        have hn_lt_U : n < U := hmig.1 ▸ hmig.2
        have hev_tc : EpochValid U n (targetCap U n) := epochValid_targetCap hn_lt_U.le
        have hval_tc : InEpochValid V (targetCap U n) s_abs (.insert u v) := by
          refine ⟨hval, Or.inr ⟨by omega, ?_, ?_, ?_⟩⟩
          · unfold targetCap; rw [ite_eq_right hn0]
            exact hn'_le_n1.trans (le_min (by omega) hn_lt_U)
          · unfold targetCap; rw [ite_eq_right hn0]
            exact (min_le_left _ _).trans (by omega)
          · unfold targetCap; rw [ite_eq_right hn0]; exact min_le_right _ _
        refine max_le ?_ ((inEpochPeakWords_le_succinctWords hw hU hU_pos hV_pos
          hev_tc hval_tc).trans (hlift _))
        have hmax_eq : max n n' = n' := Nat.max_eq_right hn_le_n'
        rw [hmax_eq]
        rcases eq_or_lt_of_le hn_le_n' with hn'_eq | hn'_gt
        · rw [← hn'_eq]; exact migratePeakWords_le_succinctWords hw hU hn_pos hev
        · have hn'_succ : n' = n + 1 := by omega
          rw [hn'_succ]
          exact migratePeakWords_le_succinctWords_succ hw hU hn_pos hmig.1 hmig.2
      · rw [ite_eq_right hmig]
        have hn'_le_cap : n' ≤ N := by
          rcases lt_or_eq_of_le hn_le_cap with hlt | heq_n
          · omega
          · have hN_U : N = U := by omega
            dsimp only [n', Dynamic.spec, StateTransitionSpec.stepFn, Dynamic.step]
            rw [card_dom_insert_eq_of_card_eq_U (heq_n.trans hN_U), hN_U]
        have hval_in : InEpochValid V N s_abs (.insert u v) :=
          ⟨hval, Or.inr ⟨by omega, hn'_le_cap, by omega, hcap_le_U⟩⟩
        exact (inEpochPeakWords_le_succinctWords hw hU hU_pos hV_pos hev hval_in).trans (hlift _)
  | delete u =>
    dsimp only [stepExactPeakWords]
    change (if n = 0 then _ else _) ≤ _
    obtain ⟨hn1_le_n', hn'_le_n⟩ := card_dom_delete_bounds s_abs u
    change n - 1 ≤ n' at hn1_le_n'
    change n' ≤ n at hn'_le_n
    have hmax_eq : max n n' = n := Nat.max_eq_left hn'_le_n
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0, hmax_eq, hn0]
      exact (compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos (Or.inl ⟨rfl, rfl⟩)).trans
        (hlift 0)
    · rw [ite_eq_right hn0]
      by_cases hn1 : n = 1
      · rw [ite_eq_left hn1, hmax_eq, hn1]
        exact (compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos (hn1 ▸ hev)).trans
          (hlift 1)
      · rw [ite_eq_right hn1]
        have hn2 : 2 ≤ n := by omega
        have hn_le_cap : n ≤ N := by rcases hev with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
        have hcap_le_U : N ≤ U := by rcases hev with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
        by_cases hmig : 4 * (n - 1) < N
        · rw [ite_eq_left hmig]
          have hnU : n ≤ U := hn_le_cap.trans hcap_le_U
          have hev_tc : EpochValid U n (targetCap U n) := epochValid_targetCap hnU
          have hval_tc : InEpochValid V (targetCap U n) s_abs (.delete u) := by
            refine ⟨hval, Or.inr ⟨by omega, ?_, ?_, ?_⟩⟩
            · unfold targetCap; rw [ite_eq_right hn0]
              exact hn'_le_n.trans (le_min (by omega) hnU)
            · unfold targetCap; rw [ite_eq_right hn0]
              exact (min_le_left _ _).trans (by omega)
            · unfold targetCap; rw [ite_eq_right hn0]; exact min_le_right _ _
          refine max_le ?_ ((inEpochPeakWords_le_succinctWords hw hU hU_pos hV_pos
            hev_tc hval_tc).trans (hlift _))
          rw [hmax_eq]
          exact migratePeakWords_le_succinctWords hw hU (by omega) hev
        · rw [ite_eq_right hmig]
          have hval_in : InEpochValid V N s_abs (.delete u) :=
            ⟨hval, Or.inr ⟨by omega, hn'_le_n.trans hn_le_cap, by omega, hcap_le_U⟩⟩
          exact (inEpochPeakWords_le_succinctWords hw hU hU_pos hV_pos hev hval_in).trans
            (hlift _)

/-- **In-Epoch Tight `1 · OPT` Peak Word-Space Bound
(`stepExactPeakWords_inEpoch_le_succinctWords`):**
Whenever `(Dynamic.spec U V U).valid s_abs o` holds and `o` does not trigger active capacity
migration, `stepExactPeakWords V w N s_abs o ≤ Dynamic.succinctWords 1355 441 U V w (max n n')`. -/
theorem stepExactPeakWords_inEpoch_le_succinctWords {U V w N : ℕ}
    {s_abs : Dictionary.State U} {o : Dynamic.Op U}
    (hw : 0 < w) (hU : Fits w U) (hU_pos : 0 < U) (hV_pos : 0 < V)
    (hev : EpochValid U (Dictionary.dom s_abs).card N)
    (hval : (Dynamic.spec U V U).valid s_abs o)
    (hno_mig :
      (∀ u v, o = .insert u v → (Dictionary.dom s_abs).card ≠ 0 →
        ¬((Dictionary.dom s_abs).card = N ∧ N < U)) ∧
      (∀ u, o = .delete u → 2 ≤ (Dictionary.dom s_abs).card →
        ¬(4 * ((Dictionary.dom s_abs).card - 1) < N))) :
    let n := (Dictionary.dom s_abs).card
    let n' := (Dictionary.dom ((Dynamic.spec U V U).stepFn s_abs o).1).card
    stepExactPeakWords V w N s_abs o ≤ Dynamic.succinctWords 1355 441 U V w (max n n') := by
  intro n n'
  cases o with
  | query u =>
    exact inEpochPeakWords_le_succinctWords hw hU hU_pos hV_pos hev ⟨hval, hev⟩
  | insert u v =>
    dsimp only [stepExactPeakWords]
    change (if n = 0 then _ else _) ≤ _
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0]
      have hs_emp := dict_eq_empty_of_card_zero hn0
      have hn'1 : n' = 1 := by
        dsimp only [n', Dynamic.spec, StateTransitionSpec.stepFn, Dynamic.step]
        rw [hs_emp, Dictionary.dom_insert, Dictionary.dom_empty]; rfl
      rw [show max n n' = 1 by omega]
      exact compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos (epochValid_targetCap hU_pos)
    · rw [ite_eq_right hn0, ite_eq_right (hno_mig.1 u v rfl hn0)]
      have hn_le_N : n ≤ N := by rcases hev with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
      have hN_le_4n : N ≤ 4 * n := by rcases hev with ⟨h0, _⟩ | ⟨_, _, h4, _⟩ <;> omega
      have hN_le_U : N ≤ U := by rcases hev with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
      obtain ⟨hn_le_n', hn'_le_n1⟩ := card_dom_insert_bounds s_abs u v
      have hn'_le_N : (Dictionary.dom (Function.update s_abs u (some v))).card ≤ N := by
        rcases lt_or_eq_of_le hn_le_N with hlt | heq_n
        · omega
        · have hnot := hno_mig.1 u v rfl hn0
          have hN_U : N = U := by omega
          rw [card_dom_insert_eq_of_card_eq_U (heq_n.trans hN_U), hN_U]
      have hev' : EpochValid U
          (Dictionary.dom ((Dynamic.spec U V U).stepFn s_abs (.insert u v)).1).card N :=
        Or.inr ⟨by dsimp only [Dynamic.spec, StateTransitionSpec.stepFn, Dynamic.step]; omega,
          hn'_le_N,
          by dsimp only [Dynamic.spec, StateTransitionSpec.stepFn, Dynamic.step]; omega,
          hN_le_U⟩
      exact inEpochPeakWords_le_succinctWords hw hU hU_pos hV_pos hev ⟨hval, hev'⟩
  | delete u =>
    dsimp only [stepExactPeakWords]
    change (if n = 0 then _ else _) ≤ _
    obtain ⟨hn1_le_n', hn'_le_n⟩ := card_dom_delete_bounds s_abs u
    change n - 1 ≤ n' at hn1_le_n'
    change n' ≤ n at hn'_le_n
    have hmax_eq : max n n' = n := Nat.max_eq_left hn'_le_n
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0, hmax_eq, hn0]
      exact compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos (Or.inl ⟨rfl, rfl⟩)
    · rw [ite_eq_right hn0]
      by_cases hn1 : n = 1
      · rw [ite_eq_left hn1, hmax_eq, hn1]
        exact compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos (hn1 ▸ hev)
      · rw [ite_eq_right hn1, ite_eq_right (hno_mig.2 u rfl (by omega))]
        have hn_le_N : n ≤ N := by rcases hev with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
        have hN_le_U : N ≤ U := by rcases hev with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
        have hnot := hno_mig.2 u rfl (by omega)
        have hev' : EpochValid U n' N := Or.inr ⟨by omega, by omega, by omega, hN_le_U⟩
        exact inEpochPeakWords_le_succinctWords hw hU hU_pos hV_pos hev ⟨hval, hev'⟩

/-- **`1 · OPT` Stepwise Peak Bit-Space Bound (`w_mul_stepExactPeakWords_le_bits`):**
Multiplying `stepExactPeakWords V w N s_abs o` by `w` never exceeds
`Dynamic.optBits U V (max n n') + 2699 * (max n n') * Dynamic.logLogFactor (max n n') + 889 * w`
bits across all dynamic operations and capacity migrations. -/
theorem w_mul_stepExactPeakWords_le_bits {U V w N : ℕ}
    {s_abs : Dictionary.State U} {o : Dynamic.Op U}
    (hw : 0 < w) (hU : Fits w U) (hU_pos : 0 < U) (hV_pos : 0 < V)
    (hev : EpochValid U (Dictionary.dom s_abs).card N)
    (hval : (Dynamic.spec U V U).valid s_abs o) :
    let m := max (Dictionary.dom s_abs).card
      (Dictionary.dom ((Dynamic.spec U V U).stepFn s_abs o).1).card
    w * stepExactPeakWords V w N s_abs o ≤
      Dynamic.optBits U V m + 2699 * m * Dynamic.logLogFactor m + 889 * w := by
  intro m
  calc w * stepExactPeakWords V w N s_abs o
      ≤ w * Dynamic.succinctWords 2699 888 U V w m :=
        Nat.mul_le_mul_left w (stepExactPeakWords_le_succinctWords hw hU hU_pos hV_pos hev hval)
    _ ≤ Dynamic.optBits U V m + 2699 * m * Dynamic.logLogFactor m + (888 + 1) * w :=
        succinctWords_mul_w_le_bits 2699 888 U V w m

/-- Trajectory-relative address-space fit predicate (`ReachedEpochsFit`): requires
`Fits w (base + stepExactPeakWords V w st_t.cap st_t.dict o_t)` only at epoch states `st_t`
reached along `ops`, never globally across `U`. -/
@[expose]
def ReachedEpochsFit {U : ℕ} (V w base : ℕ) (st : EpochState U) :
    List (Dynamic.Op U) → Prop
  | [] => True
  | o :: os =>
    Fits w (base + stepExactPeakWords V w st.cap st.dict o) ∧
      ReachedEpochsFit V w base (st.step V o) os

@[simp]
theorem reachedEpochsFit_nil {U : ℕ} (V w base : ℕ) (st : EpochState U) :
    ReachedEpochsFit V w base st [] ↔ True := Iff.rfl

@[simp]
theorem reachedEpochsFit_cons {U : ℕ} (V w base : ℕ) (st : EpochState U)
    (o : Dynamic.Op U) (os : List (Dynamic.Op U)) :
    ReachedEpochsFit V w base st (o :: os) ↔
      Fits w (base + stepExactPeakWords V w st.cap st.dict o) ∧
        ReachedEpochsFit V w base (st.step V o) os := Iff.rfl

/-- Combined potential function for the resizable succinct dictionary:
`inEpochPotential` (slab/tail hysteresis) plus `(2 * migLinearFactor) * Nat.dist n n_init`
(epoch-migration potential, zero at epoch creation `n = n_init` and when empty `n = n_init = 0`). -/
@[expose]
noncomputable def resizablePotential (U w N n n_init base : ℕ) {r : ℕ} (x : RData r) : ℕ :=
  inEpochPotential U w N base x + (2 * migLinearFactor) * Nat.dist n n_init

@[simp]
theorem resizablePotential_zero (U w base : ℕ) {r : ℕ} (x : RData r) :
    resizablePotential U w 0 0 0 base x = 0 := by
  unfold resizablePotential inEpochPotential slotPotential numBuckets bucketBits
  simp

/-- Parameter-free base charge before adding `(12 * inEpochFactor) * probeExcess`. -/
noncomputable def resizableBaseCharge : ℕ :=
  max initFirstCharge (max deleteLastOneCharge (inEpochCharge + 2 * migLinearFactor)) + 50

/-- Parameter-free $O(1)$ expected amortized instruction charge per operation across all
`query`, `insert`, and `delete` steps (including capacity-doubling and capacity-halving rebuilds).
-/
noncomputable def resizableCharge : ℕ :=
  resizableBaseCharge + 60 * inEpochFactor

/-! ## Section 4: Latent Seed Bundle, Pointwise Step Execution, and Expected Amortized Bounds -/

/-- Latent quotient-hash seed coupled with its active epoch capacity `cap`. -/
structure LatentSeed (U : ℕ) where
  /-- Current epoch capacity (`0` when the dictionary is empty). -/
  cap : ℕ
  /-- Quotient-hash seed for capacity `cap`. -/
  seed : QuotHashSeed U cap

/-- Extract a `QuotHashSeed U N` from `ls : LatentSeed U` without dependent casts in callers. -/
noncomputable def LatentSeed.seedAt {U : ℕ} (N : ℕ) (ls : LatentSeed U) : QuotHashSeed U N :=
  if h : ls.cap = N then h ▸ ls.seed else Classical.arbitrary (QuotHashSeed U N)

@[simp]
theorem LatentSeed.seedAt_mk {U : ℕ} (N : ℕ) (θ : QuotHashSeed U N) :
    (LatentSeed.mk N θ).seedAt N = θ :=
  dite_eq_left rfl

/-- Canonical empty latent seed (`cap = 0`). -/
noncomputable def LatentSeed.empty (U : ℕ) : LatentSeed U :=
  ⟨0, Classical.arbitrary (QuotHashSeed U 0)⟩

@[simp]
theorem LatentSeed.empty_cap (U : ℕ) : (LatentSeed.empty U).cap = 0 := by rfl

/-- Per-state representation coupling `st : EpochState U`, `ls : LatentSeed U`, and
`x : RData rResize`. -/
structure EpochRep (U V w base : ℕ) (st : EpochState U)
    (ls : LatentSeed U) (x : RData rResize) : Prop where
  cap_eq : ls.cap = st.cap
  compacted_rep : CompactedRep U V w st.cap (Dictionary.dom st.dict).card st.initCount base
    st.dict x
  base_reg_eq : x.regs mBase = base
  active_split : 0 < (Dictionary.dom st.dict).card →
    CompactedSplitRep base (base + offCompItems U w st.cap) U V w st.cap
      (Dictionary.dom st.dict).card st.initCount (ls.seedAt st.cap) st.dict ⟨x.mem, x.frontier⟩

theorem EpochRep.prepare {U V w base : ℕ} {st : EpochState U} {ls : LatentSeed U}
    {x : RData rResize} {o : Dynamic.Op U}
    (hrep : EpochRep U V w base st ls x)
    (hbdd : (⟨fun i => if resizableInput i then resizableEncode o i else x.regs i,
      x.mem, x.frontier⟩ : RData rResize).Bounded w) :
    EpochRep U V w base st ls
      ⟨fun i => if resizableInput i then resizableEncode o i else x.regs i, x.mem, x.frontier⟩ :=
  ⟨hrep.cap_eq,
    ⟨hbdd, hrep.compacted_rep.frontier_eq, hrep.compacted_rep.root_hdr,
      hrep.compacted_rep.fits_U, hrep.compacted_rep.pos_U, hrep.compacted_rep.pos_V,
      hrep.compacted_rep.card_eq, hrep.compacted_rep.vals_lt, hrep.compacted_rep.epoch_inv,
      hrep.compacted_rep.active_inv⟩,
    by simp [resizableInput_mBase, hrep.base_reg_eq],
    hrep.active_split⟩

private theorem nat_dist_step_le_add_one {a b c : ℕ} (hab : Nat.dist a b ≤ 1) :
    Nat.dist b c ≤ Nat.dist a c + 1 := by
  unfold Nat.dist at *; omega

private theorem insert_mig_dist_eq {U n N n_init : ℕ}
    (hn : 1 ≤ n) (hanc : EpochAnchorInv U n N n_init) (hn_eq : n = N) (hN_lt : N < U) :
    n = 2 * Nat.dist n n_init := by
  obtain ⟨_, hcap, hzero, _⟩ := hanc
  have hni_ne : n_init ≠ 0 := fun h => absurd (hzero.mpr h) (by omega)
  unfold targetCap at hcap
  rw [ite_eq_right hni_ne] at hcap
  have h2ni : N = 2 * n_init := by
    by_cases hle : 2 * n_init ≤ U
    · rwa [min_eq_left hle] at hcap
    · rw [min_eq_right (Nat.le_of_not_le hle)] at hcap; omega
  have hn_2ni : n = 2 * n_init := hn_eq.trans h2ni
  unfold Nat.dist; omega

private theorem delete_mig_le_two_dist {U n N n_init : ℕ}
    (hn2 : 2 ≤ n) (hanc : EpochAnchorInv U n N n_init) (hmig : 4 * (n - 1) < N) :
    n ≤ 2 * Nat.dist n n_init := by
  obtain ⟨_, hcap, hzero, _⟩ := hanc
  have hni_ne : n_init ≠ 0 := fun h => absurd (hzero.mpr h) (by omega)
  unfold targetCap at hcap
  rw [ite_eq_right hni_ne] at hcap
  have hN_2ni : N ≤ 2 * n_init := hcap.le.trans (min_le_left _ _)
  have hlt : 4 * (n - 1) < 2 * n_init := lt_of_lt_of_le hmig hN_2ni
  unfold Nat.dist; omega

/-- Execute `migrateActiveCode` followed by `inEpochOpCode.rename epochEmb` when an active insert
or delete triggers single-tape `1 · OPT` capacity migration. -/
private theorem exec_migrate_then_inEpoch {U V w base overhead : ℕ}
    {st : EpochState U} {ls : LatentSeed U} (o : Dynamic.Op U) {x₀ x : RData rResize}
    (hx : x.Bounded w)
    (hn : 1 ≤ (Dictionary.dom st.dict).card)
    (hanc : EpochAnchorInv U (Dictionary.dom st.dict).card st.cap st.initCount)
    (hval_tc : InEpochValid V (targetCap U (Dictionary.dom st.dict).card) st.dict o)
    (hfr : x.frontier = base + compactedEpochWords U V w st.cap (Dictionary.dom st.dict).card)
    (hsplit : CompactedSplitRep base (base + offCompItems U w st.cap) U V w st.cap
      (Dictionary.dom st.dict).card st.initCount (ls.seedAt st.cap) st.dict ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base)
    (harg : resizableArgMatch o x.regs)
    (hbelow_x : ∀ addr < base, x.mem addr = x₀.mem addr)
    (hdist_rel : (Dictionary.dom st.dict).card ≤
      2 * Nat.dist (Dictionary.dom st.dict).card st.initCount)
    (hdist_post : Nat.dist (Dictionary.dom ((Dynamic.spec U V U).stepFn st.dict o).1).card
      (Dictionary.dom st.dict).card ≤ 1)
    (hpeak_eq : stepExactPeakWords V w st.cap st.dict o =
      max (migratePeakWords U V w st.cap (Dictionary.dom st.dict).card)
        (inEpochPeakWords V w (targetCap U (Dictionary.dom st.dict).card)
          (Dictionary.dom st.dict).card st.dict o))
    (hfit_peak : Fits w (base + stepExactPeakWords V w st.cap st.dict o))
    (hst'_cap : (st.step V o).cap = targetCap U (Dictionary.dom st.dict).card)
    (hst'_init : (st.step V o).initCount = (Dictionary.dom st.dict).card)
    (h_ov : overhead ≤ 25) :
    let n := (Dictionary.dom st.dict).card
    let st' := st.step V o
    let n' := (Dictionary.dom st'.dict).card
    let L_peak := base + stepExactPeakWords V w st.cap st.dict o
    ∃ (μ_out : PMF (StepROutcome (LatentSeed U) o.Result rResize)) (T_mig_op : ℝ≥0∞),
      ExecRCodeDist w (.seq migrateActiveCode (inEpochOpCode.rename epochEmb)) x
        (μ_out.map StepROutcome.data) T_mig_op L_peak ∧
      (∀ q ∈ μ_out.support,
        EpochRep U V w base st' q.latent q.data ∧
        q.result = ((Dynamic.spec U V U).stepFn st.dict o).2 ∧
        resizableDecode o q.data.regs = some q.result ∧
        (∀ addr < base, q.data.mem addr = x₀.mem addr)) ∧
      μ_out.map (fun q => q.latent.seedAt st'.cap) =
        PMF.uniformOfFintype (QuotHashSeed U st'.cap) ∧
      ((overhead : ℝ≥0∞) + T_mig_op) +
          (∑' q, μ_out q *
            (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)) ≤
        (resizablePotential U w st.cap n st.initCount base x₀ : ℝ≥0∞) +
          (resizableBaseCharge : ℝ≥0∞) := by
  intro n st' n' L_peak
  set N_new := targetCap U n
  have hle_m : base + migratePeakWords U V w st.cap n ≤ L_peak := by
    dsimp only [L_peak]; rw [hpeak_eq]; exact Nat.add_le_add_left (le_max_left _ _) base
  have hle_in : base + inEpochPeakWords V w N_new n st.dict o ≤ L_peak := by
    dsimp only [L_peak]; rw [hpeak_eq]; exact Nat.add_le_add_left (le_max_right _ _) base
  obtain ⟨zMid, T_mig, hex_mig, hmid_all, hcost_mig⟩ :=
    migrateActiveCode_execRCodeDist hx hn hanc.1 hfr (hfit_peak.of_le hle_m) hsplit hbase
  have hev_tc : EpochValid U n N_new := by
    have hNU : st.cap ≤ U := by rcases hanc.1 with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
    have hn_le : n ≤ st.cap := by rcases hanc.1 with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
    exact epochValid_targetCap (hn_le.trans hNU)
  have hop_all : ∀ θ_new : QuotHashSeed U N_new,
      ∃ (zFin : RData rResize) (stepsOp : ℕ),
        RDemonicExec w (base + inEpochPeakWords V w N_new n st.dict o)
          (inEpochOpCode.rename epochEmb) (zMid θ_new) stepsOp (· = zFin) ∧
        resizableDecode o zFin.regs = some ((Dynamic.spec U V U).stepFn st.dict o).2 ∧
        zFin.Bounded w ∧
        zFin.frontier = base + compactedEpochWords U V w N_new n' ∧
        CompactedSplitRep base (base + offCompItems U w N_new) U V w N_new n' n θ_new st'.dict
          ⟨zFin.mem, zFin.frontier⟩ ∧
        zFin.regs mBase = base ∧
        (∀ addr < base, zFin.mem addr = (zMid θ_new).mem addr) ∧
        stepsOp + inEpochPotential U w N_new base zFin ≤
          inEpochPotential U w N_new base (zMid θ_new) + inEpochBaseCharge +
            (12 * inEpochFactor) *
              probeExcess N_new (qStage1 U N_new θ_new.1) (polyStage2 U N_new) θ_new.2
                (Dictionary.dom st.dict) (opKey o) := fun θ_new => by
    obtain ⟨hb, hzf, hsp, hb_reg, ht_eq, hu_eq, hv_eq, _⟩ := hmid_all θ_new
    have harg_mid : resizableArgMatch o (zMid θ_new).regs := by
      cases o with
      | query _ => exact ⟨ht_eq.trans harg.1, hu_eq.trans harg.2⟩
      | insert _ _ => exact ⟨ht_eq.trans harg.1, hu_eq.trans harg.2.1, hv_eq.trans harg.2.2⟩
      | delete _ => exact ⟨ht_eq.trans harg.1, hu_eq.trans harg.2⟩
    exact inEpochOpCode_rename_active_demonicExec o hb hn hev_tc hval_tc hzf hsp hb_reg harg_mid
      (hfit_peak.of_le hle_in)
  choose zFin stepsOp hop_spec using hop_all
  set μ_u := PMF.uniformOfFintype (QuotHashSeed U N_new)
  have hext_id : ∀ θ_new : QuotHashSeed U N_new,
      ReducedKWise.extractSeed (base + epochHdrWords) (qBits U N_new) (hashB N_new)
        (totalMicroBits N_new) 3 (zMid θ_new).mem = θ_new :=
    fun θ_new => ReducedKWise.extractSeed_of_seedRep (hmid_all θ_new).2.2.1.hash_rep.2
  let extMid (y : RData rResize) : QuotHashSeed U N_new :=
    ReducedKWise.extractSeed (base + epochHdrWords) (qBits U N_new) (hashB N_new)
      (totalMicroBits N_new) 3 y.mem
  have hex_op_supp : ∀ y ∈ (μ_u.map zMid).support,
      ExecRCodeDist w (inEpochOpCode.rename epochEmb) y
        (PMF.pure (zFin (extMid y))) ((stepsOp (extMid y) : ℕ) : ℝ≥0∞) L_peak := by
    intro y hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨θ_new, _, rfl⟩ := hy
    have hid : extMid (zMid θ_new) = θ_new := hext_id θ_new
    rw [hid]
    exact (ExecRCodeDist.of_demonicExec (hop_spec θ_new).1).mono_peak hle_in
  have hex_seq := (hex_mig.mono_peak hle_m).seq hex_op_supp
  let mkOut (θ_new : QuotHashSeed U N_new) : StepROutcome (LatentSeed U) o.Result rResize :=
    ⟨⟨N_new, θ_new⟩, zFin θ_new, ((Dynamic.spec U V U).stepFn st.dict o).2⟩
  let μ_out : PMF (StepROutcome (LatentSeed U) o.Result rResize) := μ_u.map mkOut
  have hmap_data : (μ_u.map zMid).bind (fun y => PMF.pure (zFin (extMid y))) =
      μ_out.map StepROutcome.data := by
    have h1 : (μ_u.map zMid).bind (fun y => PMF.pure (zFin (extMid y))) =
        (μ_u.map zMid).map (zFin ∘ extMid) := rfl
    rw [h1, PMF.map_comp, PMF.map_comp]
    refine congrArg (μ_u.map ·) (funext fun θ_new => ?_)
    dsimp only [Function.comp_apply, mkOut, StepROutcome.data, extMid]
    rw [hext_id θ_new]
  have htsum_op : (∑' y, (μ_u.map zMid) y * ((stepsOp (extMid y) : ℕ) : ℝ≥0∞)) =
      ∑' θ_new, μ_u θ_new * ((stepsOp θ_new : ℕ) : ℝ≥0∞) := by
    rw [Cslib.Probability.PMF.tsum_map_mul]
    exact tsum_congr fun θ_new => by dsimp only [extMid]; rw [hext_id θ_new]
  -- Bound expected `stepsOp + inEpochPotential` under `μ_u`
  have hN_new_U : N_new ≤ U := by
    rcases hev_tc with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
  have hn_N_new : n ≤ N_new := by
    rcases hev_tc with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
  have hS_le : ((Dictionary.dom st.dict).erase (opKey o)).card ≤ N_new :=
    (Finset.card_erase_le (s := Dictionary.dom st.dict) (a := opKey o)).trans hn_N_new
  have hpr_le :=
    tsum_uniform_probeExcess_reducedPolyHash_le_five hN_new_U (Dictionary.dom st.dict) (opKey o)
      hS_le
  have hop_expect :
      (∑' θ_new, μ_u θ_new * ((stepsOp θ_new : ℕ) : ℝ≥0∞)) +
        (∑' θ_new, μ_u θ_new * (inEpochPotential U w N_new base (zFin θ_new) : ℝ≥0∞)) ≤
      (∑' θ_new, μ_u θ_new * (inEpochPotential U w N_new base (zMid θ_new) : ℝ≥0∞)) +
        (inEpochCharge : ℝ≥0∞) := by
    rw [← CompleteLattice.summable.tsum_add CompleteLattice.summable]
    have hpt : ∀ θ_new,
        μ_u θ_new * (((stepsOp θ_new : ℕ) : ℝ≥0∞) +
            (inEpochPotential U w N_new base (zFin θ_new) : ℝ≥0∞)) ≤
          μ_u θ_new * (inEpochPotential U w N_new base (zMid θ_new) : ℝ≥0∞) +
            (μ_u θ_new * (inEpochBaseCharge : ℝ≥0∞) +
              (12 * inEpochFactor : ℝ≥0∞) *
                (μ_u θ_new * (probeExcess N_new (qStage1 U N_new θ_new.1)
                  (polyStage2 U N_new) θ_new.2 (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞))) :=
      fun θ_new => by
        have hc := (Nat.cast_le (α := ℝ≥0∞)).mpr (hop_spec θ_new).2.2.2.2.2.2.2
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc
        calc μ_u θ_new * (((stepsOp θ_new : ℕ) : ℝ≥0∞) +
                (inEpochPotential U w N_new base (zFin θ_new) : ℝ≥0∞))
            ≤ μ_u θ_new * ((inEpochPotential U w N_new base (zMid θ_new) : ℝ≥0∞) +
                (inEpochBaseCharge : ℝ≥0∞) +
                  (12 * inEpochFactor : ℝ≥0∞) *
                    (probeExcess N_new (qStage1 U N_new θ_new.1) (polyStage2 U N_new) θ_new.2
                      (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞)) := by gcongr
          _ = μ_u θ_new * (inEpochPotential U w N_new base (zMid θ_new) : ℝ≥0∞) +
                (μ_u θ_new * (inEpochBaseCharge : ℝ≥0∞) +
                  (12 * inEpochFactor : ℝ≥0∞) *
                    (μ_u θ_new * (probeExcess N_new (qStage1 U N_new θ_new.1)
                      (polyStage2 U N_new) θ_new.2 (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞))) :=
              by ring
    calc (∑' θ_new, (μ_u θ_new * ((stepsOp θ_new : ℕ) : ℝ≥0∞) +
            μ_u θ_new * (inEpochPotential U w N_new base (zFin θ_new) : ℝ≥0∞)))
        = ∑' θ_new, μ_u θ_new * (((stepsOp θ_new : ℕ) : ℝ≥0∞) +
            (inEpochPotential U w N_new base (zFin θ_new) : ℝ≥0∞)) :=
          tsum_congr fun _ => (mul_add _ _ _).symm
      _ ≤ ∑' θ_new, (μ_u θ_new * (inEpochPotential U w N_new base (zMid θ_new) : ℝ≥0∞) +
            (μ_u θ_new * (inEpochBaseCharge : ℝ≥0∞) +
              (12 * inEpochFactor : ℝ≥0∞) *
                (μ_u θ_new * (probeExcess N_new (qStage1 U N_new θ_new.1)
                  (polyStage2 U N_new) θ_new.2 (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞)))) :=
          tsum_le_tsum hpt
      _ = (∑' θ_new, μ_u θ_new * (inEpochPotential U w N_new base (zMid θ_new) : ℝ≥0∞)) +
            ((∑' θ_new, μ_u θ_new * (inEpochBaseCharge : ℝ≥0∞)) +
              (12 * inEpochFactor : ℝ≥0∞) *
                ∑' θ_new, μ_u θ_new * (probeExcess N_new (qStage1 U N_new θ_new.1)
                  (polyStage2 U N_new) θ_new.2 (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞)) := by
          rw [CompleteLattice.summable.tsum_add CompleteLattice.summable,
            CompleteLattice.summable.tsum_add CompleteLattice.summable, ENNReal.tsum_mul_left]
      _ ≤ (∑' θ_new, μ_u θ_new * (inEpochPotential U w N_new base (zMid θ_new) : ℝ≥0∞)) +
            ((inEpochBaseCharge : ℝ≥0∞) + (12 * inEpochFactor : ℝ≥0∞) * 5) := by
          rw [ENNReal.tsum_mul_right, μ_u.tsum_coe, one_mul]; gcongr
      _ = (∑' θ_new, μ_u θ_new * (inEpochPotential U w N_new base (zMid θ_new) : ℝ≥0∞)) +
            (inEpochCharge : ℝ≥0∞) := by
          unfold inEpochCharge; push_cast; ring
  refine ⟨μ_out, _, hex_seq.congr_dist hmap_data le_rfl, fun q hq => ?_, ?_, ?_⟩
  · dsimp only [μ_out] at hq
    rw [PMF.mem_support_map_iff] at hq
    obtain ⟨θ_new, _, rfl⟩ := hq
    obtain ⟨_, hdec, hzb, hzf, hsp_fin, hzb_reg, hbel_fin, _⟩ := hop_spec θ_new
    have hcap_eq_N : st'.cap = N_new := hst'_cap
    have hinit_eq_n : st'.initCount = n := hst'_init
    refine ⟨⟨hcap_eq_N.symm, ?_, hzb_reg, fun _ => ?_⟩, rfl, hdec, fun addr haddr =>
      (hbel_fin addr haddr).trans (((hmid_all θ_new).2.2.2.2.2.2.2 addr haddr).trans
        (hbelow_x addr haddr))⟩
    · rw [hcap_eq_N, hinit_eq_n]
      exact compactedRep_of_split hzb hzf hval_tc.2 hsp_fin
    · rw [hinit_eq_n]
      have htr : ∀ (C : ℕ), C = N_new →
          CompactedSplitRep base (base + offCompItems U w C) U V w C n' n
            ((mkOut θ_new).latent.seedAt C) st'.dict ⟨(zFin θ_new).mem, (zFin θ_new).frontier⟩ := by
        rintro _ rfl
        simpa only [mkOut, LatentSeed.seedAt_mk] using hsp_fin
      exact htr st'.cap hcap_eq_N
  · have htr : ∀ (C : ℕ), C = N_new →
        μ_out.map (fun q => q.latent.seedAt C) = PMF.uniformOfFintype (QuotHashSeed U C) := by
      rintro _ rfl
      dsimp only [μ_out]
      rw [PMF.map_comp]
      have hid_fn : (fun q : StepROutcome (LatentSeed U) o.Result rResize =>
          q.latent.seedAt N_new) ∘ mkOut = id :=
        funext fun θ_new => LatentSeed.seedAt_mk _ θ_new
      rw [hid_fn, PMF.map_id]
    exact htr st'.cap hst'_cap
  · rw [htsum_op]
    have hcap_eq_N : st'.cap = N_new := hst'_cap
    have hinit_eq_n : st'.initCount = n := hst'_init
    have htsum_pot : (∑' q, μ_out q *
        (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)) =
        (∑' θ_new, μ_u θ_new * (inEpochPotential U w N_new base (zFin θ_new) : ℝ≥0∞)) +
          (((2 * migLinearFactor) * Nat.dist n' n : ℕ) : ℝ≥0∞) := by
      dsimp only [μ_out]
      rw [Cslib.Probability.PMF.tsum_map_mul]
      have h1 : (∑' θ_new, μ_u θ_new *
          (resizablePotential U w st'.cap n' st'.initCount base (zFin θ_new) : ℝ≥0∞)) =
          ∑' θ_new, (μ_u θ_new * (inEpochPotential U w N_new base (zFin θ_new) : ℝ≥0∞) +
            μ_u θ_new * (((2 * migLinearFactor) * Nat.dist n' n : ℕ) : ℝ≥0∞)) :=
        tsum_congr fun θ_new => by
          rw [hcap_eq_N, hinit_eq_n]
          unfold resizablePotential
          rw [Nat.cast_add, mul_add]
      rw [h1, CompleteLattice.summable.tsum_add CompleteLattice.summable,
        ENNReal.tsum_mul_right, μ_u.tsum_coe, one_mul]
    rw [htsum_pot]
    set E_mid := ∑' θ_new, μ_u θ_new * (inEpochPotential U w N_new base (zMid θ_new) : ℝ≥0∞)
    set E_op := ∑' θ_new, μ_u θ_new * ((stepsOp θ_new : ℕ) : ℝ≥0∞)
    set E_fin := ∑' θ_new, μ_u θ_new * (inEpochPotential U w N_new base (zFin θ_new) : ℝ≥0∞)
    have h_comb : T_mig + E_op + E_fin ≤
        ((migLinearFactor * n : ℕ) : ℝ≥0∞) + (inEpochCharge : ℝ≥0∞) := by
      calc T_mig + E_op + E_fin
          = T_mig + (E_op + E_fin) := by ac_rfl
        _ ≤ T_mig + (E_mid + (inEpochCharge : ℝ≥0∞)) := add_le_add le_rfl hop_expect
        _ = (T_mig + E_mid) + (inEpochCharge : ℝ≥0∞) := by ac_rfl
        _ ≤ ((migLinearFactor * n : ℕ) : ℝ≥0∞) + (inEpochCharge : ℝ≥0∞) :=
            add_le_add hcost_mig le_rfl
    have hmig_le_pot : ((migLinearFactor * n : ℕ) : ℝ≥0∞) ≤
        (resizablePotential U w st.cap n st.initCount base x₀ : ℝ≥0∞) := by
      refine (Nat.cast_le (α := ℝ≥0∞)).mpr ?_
      unfold resizablePotential
      have hmul : migLinearFactor * n ≤ (2 * migLinearFactor) * Nat.dist n st.initCount := by
        calc migLinearFactor * n
            ≤ migLinearFactor * (2 * Nat.dist n st.initCount) :=
              Nat.mul_le_mul_left migLinearFactor hdist_rel
          _ = (2 * migLinearFactor) * Nat.dist n st.initCount := by ring
      exact hmul.trans (Nat.le_add_left _ _)
    have hrem_le : (overhead : ℝ≥0∞) + (inEpochCharge : ℝ≥0∞) +
        (((2 * migLinearFactor) * Nat.dist n' n : ℕ) : ℝ≥0∞) ≤ (resizableBaseCharge : ℝ≥0∞) := by
      rw [← Nat.cast_add, ← Nat.cast_add]
      refine (Nat.cast_le (α := ℝ≥0∞)).mpr ?_
      have hd_le : (2 * migLinearFactor) * Nat.dist n' n ≤ 2 * migLinearFactor := by
        calc (2 * migLinearFactor) * Nat.dist n' n
            ≤ (2 * migLinearFactor) * 1 := Nat.mul_le_mul_left _ hdist_post
          _ = 2 * migLinearFactor := Nat.mul_one _
      have hb_ge : inEpochCharge + 2 * migLinearFactor + 50 ≤ resizableBaseCharge := by
        unfold resizableBaseCharge
        exact Nat.add_le_add_right (le_max_of_le_right (le_max_right _ _)) 50
      linarith only [h_ov, hd_le, hb_ge]
    calc ((overhead : ℝ≥0∞) + (T_mig + E_op)) +
          (E_fin + (((2 * migLinearFactor) * Nat.dist n' n : ℕ) : ℝ≥0∞))
        = (T_mig + E_op + E_fin) +
            ((overhead : ℝ≥0∞) + (((2 * migLinearFactor) * Nat.dist n' n : ℕ) : ℝ≥0∞)) := by
            ac_rfl
      _ ≤ (((migLinearFactor * n : ℕ) : ℝ≥0∞) + (inEpochCharge : ℝ≥0∞)) +
            ((overhead : ℝ≥0∞) + (((2 * migLinearFactor) * Nat.dist n' n : ℕ) : ℝ≥0∞)) :=
            add_le_add h_comb le_rfl
      _ = ((migLinearFactor * n : ℕ) : ℝ≥0∞) +
            ((overhead : ℝ≥0∞) + (inEpochCharge : ℝ≥0∞) +
              (((2 * migLinearFactor) * Nat.dist n' n : ℕ) : ℝ≥0∞)) := by ac_rfl
      _ ≤ (resizablePotential U w st.cap n st.initCount base x₀ : ℝ≥0∞) +
            (resizableBaseCharge : ℝ≥0∞) := add_le_add hmig_le_pot hrem_le

/-- Execute an active in-epoch branch (`inEpochOpCode.rename epochEmb`) with no migration. -/
private theorem exec_inEpoch_branch {U V w base overhead : ℕ}
    {st : EpochState U} {ls : LatentSeed U} (o : Dynamic.Op U) {x₀ x : RData rResize}
    (hx : x.Bounded w)
    (hn : 0 < (Dictionary.dom st.dict).card)
    (hev : EpochValid U (Dictionary.dom st.dict).card st.cap)
    (hval : InEpochValid V st.cap st.dict o)
    (hfr : x.frontier = base + compactedEpochWords U V w st.cap (Dictionary.dom st.dict).card)
    (hsplit : CompactedSplitRep base (base + offCompItems U w st.cap) U V w st.cap
      (Dictionary.dom st.dict).card st.initCount (ls.seedAt st.cap) st.dict ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base)
    (harg : resizableArgMatch o x.regs)
    (hbelow_x : ∀ addr < base, x.mem addr = x₀.mem addr)
    (hpot_x : inEpochPotential U w st.cap base x = inEpochPotential U w st.cap base x₀)
    (hdist_post : Nat.dist (Dictionary.dom st.dict).card
      (Dictionary.dom ((Dynamic.spec U V U).stepFn st.dict o).1).card ≤ 1)
    (hpeak_eq : stepExactPeakWords V w st.cap st.dict o =
      inEpochPeakWords V w st.cap (Dictionary.dom st.dict).card st.dict o)
    (hfit_peak : Fits w (base + stepExactPeakWords V w st.cap st.dict o))
    (hcap_same : (st.step V o).cap = st.cap)
    (hinit_same : (st.step V o).initCount = st.initCount)
    (hls_cap : ls.cap = st.cap)
    (h_ov : overhead ≤ 25) :
    let n := (Dictionary.dom st.dict).card
    let st' := st.step V o
    let n' := (Dictionary.dom st'.dict).card
    let L_peak := base + stepExactPeakWords V w st.cap st.dict o
    let θ := ls.seedAt st.cap
    ∃ (q_out : StepROutcome (LatentSeed U) o.Result rResize) (stepsOp : ℕ),
      RDemonicExec w L_peak (inEpochOpCode.rename epochEmb) x stepsOp (· = q_out.data) ∧
      q_out.latent = ls ∧
      EpochRep U V w base st' q_out.latent q_out.data ∧
      q_out.result = ((Dynamic.spec U V U).stepFn st.dict o).2 ∧
      resizableDecode o q_out.data.regs = some q_out.result ∧
      (∀ addr < base, q_out.data.mem addr = x₀.mem addr) ∧
      (overhead + stepsOp) + resizablePotential U w st'.cap n' st'.initCount base q_out.data ≤
        resizablePotential U w st.cap n st.initCount base x₀ + resizableBaseCharge +
          (12 * inEpochFactor) *
            probeExcess st.cap (qStage1 U st.cap θ.1) (polyStage2 U st.cap) θ.2
              (Dictionary.dom st.dict) (opKey o) := by
  intro n st' n' L_peak θ
  obtain ⟨z, stepsOp, hex, hdec, hzb, hzf, hsplit_z, hz_base, hbel_z, hcost⟩ :=
    inEpochOpCode_rename_active_demonicExec o hx hn hev hval hfr hsplit hbase harg
      (hpeak_eq ▸ hfit_peak)
  have hd_step : Nat.dist n' st.initCount ≤ Nat.dist n st.initCount + 1 :=
    nat_dist_step_le_add_one hdist_post
  let q_out : StepROutcome (LatentSeed U) o.Result rResize :=
    ⟨ls, z, ((Dynamic.spec U V U).stepFn st.dict o).2⟩
  have hex_L : RDemonicExec w L_peak (inEpochOpCode.rename epochEmb) x stepsOp (· = q_out.data) :=
    by dsimp only [L_peak]; rwa [hpeak_eq]
  refine ⟨q_out, stepsOp, hex_L, rfl, ?_, rfl, hdec,
    fun addr haddr => (hbel_z addr haddr).trans (hbelow_x addr haddr), ?_⟩
  · refine ⟨hls_cap.trans hcap_same.symm, ?_, hz_base, fun _ => ?_⟩
    · rw [hcap_same, hinit_same]
      exact compactedRep_of_split hzb hzf hval.2 hsplit_z
    · rw [hcap_same, hinit_same]
      exact hsplit_z
  · rw [hcap_same, hinit_same]
    unfold resizablePotential
    rw [← hpot_x]
    have hd_mul : (2 * migLinearFactor) * Nat.dist n' st.initCount ≤
        (2 * migLinearFactor) * Nat.dist n st.initCount + 2 * migLinearFactor := by
      calc (2 * migLinearFactor) * Nat.dist n' st.initCount
          ≤ (2 * migLinearFactor) * (Nat.dist n st.initCount + 1) :=
            Nat.mul_le_mul_left _ hd_step
        _ = (2 * migLinearFactor) * Nat.dist n st.initCount + 2 * migLinearFactor := by ring
    have hb_ge : inEpochBaseCharge + 2 * migLinearFactor + 50 ≤ resizableBaseCharge := by
      unfold resizableBaseCharge inEpochCharge
      have hmax : inEpochBaseCharge + 60 * inEpochFactor + 2 * migLinearFactor ≤
          max initFirstCharge
            (max deleteLastOneCharge (inEpochBaseCharge + 60 * inEpochFactor +
              2 * migLinearFactor)) :=
        le_max_of_le_right (le_max_right _ _)
      omega
    dsimp only [q_out, θ]
    omega

private theorem execRCodeDist_of_demonic_outcome {U : ℕ} {α : Type*} {w L_peak steps : ℕ}
    {c : RCode .exact rResize} {x : RData rResize}
    (q_out : StepROutcome (LatentSeed U) α rResize)
    (h : RDemonicExec w L_peak c x steps (· = q_out.data)) :
    ExecRCodeDist w c x ((PMF.pure q_out).map StepROutcome.data) steps L_peak :=
  (ExecRCodeDist.of_demonicExec h).congr_dist (by simp) le_rfl

private theorem package_active_inEpoch_step {U V w base overhead stepsOp : ℕ}
    {st : EpochState U} {ls : LatentSeed U} {o : Dynamic.Op U} {x : RData rResize}
    {q_out : StepROutcome (LatentSeed U) o.Result rResize}
    (hn_pos : 1 ≤ (Dictionary.dom st.dict).card)
    (hcap_same : (st.step V o).cap = st.cap)
    (hex_all : RDemonicExec w (base + stepExactPeakWords V w st.cap st.dict o)
      resizableOpCode x (overhead + stepsOp) (· = q_out.data))
    (hqls : q_out.latent = ls)
    (hqrep : EpochRep U V w base (st.step V o) q_out.latent q_out.data)
    (hqres : q_out.result = ((Dynamic.spec U V U).stepFn st.dict o).2)
    (hqdec : resizableDecode o q_out.data.regs = some q_out.result)
    (hqbel : ∀ addr < base, q_out.data.mem addr = x.mem addr)
    (hqcost : (overhead + stepsOp) +
        resizablePotential U w (st.step V o).cap (Dictionary.dom (st.step V o).dict).card
          (st.step V o).initCount base q_out.data ≤
        resizablePotential U w st.cap (Dictionary.dom st.dict).card st.initCount base x +
          resizableBaseCharge +
          12 * inEpochFactor *
            probeExcess st.cap (qStage1 U st.cap (ls.seedAt st.cap).1)
              (polyStage2 U st.cap) (ls.seedAt st.cap).2 (Dictionary.dom st.dict) (opKey o)) :
    let n := (Dictionary.dom st.dict).card
    let st' := st.step V o
    let n' := (Dictionary.dom st'.dict).card
    let L_peak := base + stepExactPeakWords V w st.cap st.dict o
    let θ := ls.seedAt st.cap
    ∃ (μ_out : PMF (StepROutcome (LatentSeed U) o.Result rResize)) (T_out : ℝ≥0∞),
      ExecRCodeDist w resizableOpCode x (μ_out.map StepROutcome.data) T_out L_peak ∧
      (∀ q ∈ μ_out.support,
        EpochRep U V w base st' q.latent q.data ∧
        q.result = ((Dynamic.spec U V U).stepFn st.dict o).2 ∧
        resizableDecode o q.data.regs = some q.result ∧
        (∀ addr < base, q.data.mem addr = x.mem addr)) ∧
      (0 < n' →
        if st'.cap = st.cap then
          0 < n ∧ μ_out.map (fun q => q.latent.seedAt st.cap) = PMF.pure θ
        else
          μ_out.map (fun q => q.latent.seedAt st'.cap) =
            PMF.uniformOfFintype (QuotHashSeed U st'.cap)) ∧
      T_out + (∑' q, μ_out q *
          (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)) ≤
        (resizablePotential U w st.cap n st.initCount base x : ℝ≥0∞) +
          ((resizableBaseCharge : ℝ≥0∞) +
            if 0 < n then
              (12 * inEpochFactor : ℝ≥0∞) *
                (probeExcess st.cap (qStage1 U st.cap θ.1) (polyStage2 U st.cap) θ.2
                  (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞)
            else 0) := by
  refine ⟨PMF.pure q_out, _, execRCodeDist_of_demonic_outcome q_out hex_all,
    fun q hq => ?_, fun _ => ?_, ?_⟩
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hq; subst hq
    exact ⟨hqrep, hqres, hqdec, hqbel⟩
  · rw [ite_eq_left hcap_same]; exact ⟨hn_pos, by simp [hqls]⟩
  · rw [ite_eq_left (show 0 < (Dictionary.dom st.dict).card from hn_pos),
      tsum_eq_single q_out (fun b hb => by simp [PMF.pure_apply, hb])]
    simp only [PMF.pure_apply_self, one_mul]
    have hc := (Nat.cast_le (α := ℝ≥0∞)).mpr hqcost
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc
    calc ((overhead + stepsOp : ℕ) : ℝ≥0∞) +
          (resizablePotential U w (st.step V o).cap (Dictionary.dom (st.step V o).dict).card
            (st.step V o).initCount base q_out.data : ℝ≥0∞)
        = ((overhead : ℝ≥0∞) + (stepsOp : ℝ≥0∞)) +
          (resizablePotential U w (st.step V o).cap (Dictionary.dom (st.step V o).dict).card
            (st.step V o).initCount base q_out.data : ℝ≥0∞) := by push_cast; ring
      _ ≤ (resizablePotential U w st.cap (Dictionary.dom st.dict).card st.initCount base x : ℝ≥0∞) +
          (resizableBaseCharge : ℝ≥0∞) +
          (12 * inEpochFactor : ℝ≥0∞) *
            (probeExcess st.cap (qStage1 U st.cap (ls.seedAt st.cap).1)
              (polyStage2 U st.cap) (ls.seedAt st.cap).2
              (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞) := hc
      _ = _ := by ac_rfl

/-- **Pointwise Distributional Step Certificate (`resizableOpCode_step_pointwise`):**
From any state `(ls, x)` satisfying `EpochRep U V w base st ls x` and `resizableArgMatch o x.regs`,
`resizableOpCode` executes under `ExecRCodeDist` within `base + stepExactPeakWords`, establishes
`EpochRep` for `st' = st.step V o`, either resamples a uniform `QuotHashSeed U st'.cap` or preserves
`ls` identically, and satisfies the potential-amortized bound with `probeExcess`. -/
theorem resizableOpCode_step_pointwise {U V w base : ℕ}
    {st : EpochState U} {ls : LatentSeed U} (o : Dynamic.Op U) {x : RData rResize}
    (hanc : EpochAnchorInv U (Dictionary.dom st.dict).card st.cap st.initCount)
    (hrep : EpochRep U V w base st ls x)
    (hval : (Dynamic.spec U V U).valid st.dict o)
    (harg : resizableArgMatch o x.regs)
    (hfit_peak : Fits w (base + stepExactPeakWords V w st.cap st.dict o)) :
    let n := (Dictionary.dom st.dict).card
    let st' := st.step V o
    let n' := (Dictionary.dom st'.dict).card
    let L_peak := base + stepExactPeakWords V w st.cap st.dict o
    let θ := ls.seedAt st.cap
    ∃ (μ_out : PMF (StepROutcome (LatentSeed U) o.Result rResize)) (T_out : ℝ≥0∞),
      ExecRCodeDist w resizableOpCode x (μ_out.map StepROutcome.data) T_out L_peak ∧
      (∀ q ∈ μ_out.support,
        EpochRep U V w base st' q.latent q.data ∧
        q.result = ((Dynamic.spec U V U).stepFn st.dict o).2 ∧
        resizableDecode o q.data.regs = some q.result ∧
        (∀ addr < base, q.data.mem addr = x.mem addr)) ∧
      (0 < n' →
        if st'.cap = st.cap then
          0 < n ∧ μ_out.map (fun q => q.latent.seedAt st.cap) = PMF.pure θ
        else
          μ_out.map (fun q => q.latent.seedAt st'.cap) =
            PMF.uniformOfFintype (QuotHashSeed U st'.cap)) ∧
      T_out + (∑' q, μ_out q *
          (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)) ≤
        (resizablePotential U w st.cap n st.initCount base x : ℝ≥0∞) +
          ((resizableBaseCharge : ℝ≥0∞) +
            if 0 < n then
              (12 * inEpochFactor : ℝ≥0∞) *
                (probeExcess st.cap (qStage1 U st.cap θ.1) (polyStage2 U st.cap) θ.2
                  (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞)
            else 0) := by
  intro n st' n' L_peak θ
  have hx : x.Bounded w := hrep.compacted_rep.bounded
  have hfr : x.frontier = base + compactedEpochWords U V w st.cap n :=
    hrep.compacted_rep.frontier_eq
  have hhdr : RootHeaderValid U V w st.cap n st.initCount base x.mem :=
    hrep.compacted_rep.root_hdr
  have hbase : x.regs mBase = base := hrep.base_reg_eq
  have h8 : 8 ≤ compactedEpochWords U V w st.cap n := eight_le_compactedEpochWords U V w st.cap n
  have hfit_fr : Fits w x.frontier := hx.frontier_fits
  have hfit6 : Fits w 6 := hfit_fr.of_le (by rw [hfr]; omega)
  have hfit2 : Fits w 2 := hfit6.of_le (by decide)
  have hfit1 : Fits w 1 := hfit6.of_le (by decide)
  have hL_x : x.frontier ≤ L_peak := by
    rw [hfr]; dsimp only [L_peak, stepExactPeakWords]
    cases o with
    | query u =>
      exact Nat.add_le_add_left (compactedEpochWords_mono (le_max_left _ _)) base
    | insert u v =>
      change base + compactedEpochWords U V w st.cap n ≤ base + (if n = 0 then _ else _)
      by_cases hn0 : n = 0
      · rw [ite_eq_left hn0, hn0]
        have hN0 : st.cap = 0 := by rcases hanc.1 with ⟨_, hN0⟩ | ⟨h1, _, _, _⟩ <;> omega
        rw [hN0]
        exact Nat.add_le_add_left (eight_le_compactedEpochWords U V w _ 1) base
      · rw [ite_eq_right hn0]
        split_ifs
        · refine (Nat.add_le_add_left ?_ base).trans (Nat.add_le_add_left (le_max_left _ _) base)
          unfold compactedEpochWords migratePeakWords migrateArenaWords
          rw [ite_eq_right hn0]
          have hc_le : compactedItemWords U V w st.cap n ≤
              max (compactedItemWords U V w st.cap n)
                (compactedItemWords U V w (targetCap U n) n) + 6 :=
            (le_max_left _ _).trans (Nat.le_add_right _ 6)
          dsimp only [n] at hc_le ⊢
          omega
        · exact Nat.add_le_add_left (compactedEpochWords_mono (le_max_left _ _)) base
    | delete u =>
      change base + compactedEpochWords U V w st.cap n ≤ base + (if n = 0 then _ else _)
      by_cases hn0 : n = 0
      · rw [ite_eq_left hn0, hn0]
        have hN0 : st.cap = 0 := by rcases hanc.1 with ⟨_, hN0⟩ | ⟨h1, _, _, _⟩ <;> omega
        rw [hN0]
      · rw [ite_eq_right hn0]
        by_cases hn1 : n = 1
        · rw [ite_eq_left hn1, hn1]
        · rw [ite_eq_right hn1]
          split_ifs
          · refine (Nat.add_le_add_left ?_ base).trans (Nat.add_le_add_left (le_max_left _ _) base)
            unfold compactedEpochWords migratePeakWords migrateArenaWords
            rw [ite_eq_right hn0]
            have hc_le : compactedItemWords U V w st.cap n ≤
                max (compactedItemWords U V w st.cap n)
                  (compactedItemWords U V w (targetCap U n) n) + 6 :=
              (le_max_left _ _).trans (Nat.le_add_right _ 6)
            dsimp only [n] at hc_le ⊢
            omega
          · have ⟨hn1_le, _⟩ := card_dom_delete_bounds st.dict u
            have hmax_n : max n (Dictionary.dom (Function.update st.dict u none)).card = n :=
              Nat.max_eq_left (card_dom_delete_bounds st.dict u).2
            dsimp only [inEpochPeakWords, Dynamic.spec, StateTransitionSpec.stepFn, Dynamic.step]
            rw [hmax_n]
  -- Prefix: `loadAtOffCode mBase mCnt mCur 6; mZero := 0; mOne := 1` (5 steps)
  obtain ⟨hex_ldn, hx₁b⟩ := loadAtOffCode_exec (rAddr := mBase) (rDst := mCnt) (rTmp := mCur)
    (off := 6) hx hL_x (mReg_ne (by decide)) hbase hfit6 (by rw [hfr]; omega)
  set x₁ := (x.set mCur (base + 6)).set mCnt (x.mem (base + 6))
  set x₂ := (x₁.set mZero 0).set mOne 1
  have hex_z0 := RDemonicExec.const (B := .exact) (d := mZero) (v := 0) (x := x₁) hL_x (fits_zero w)
  have hex_o1 := RDemonicExec.const (B := .exact) (d := mOne) (v := 1) (x := x₁.set mZero 0)
    hL_x hfit1
  have hx₂b : x₂.Bounded w := (hx₁b.set (fits_zero w)).set hfit1
  have hx₂_cnt : x₂.regs mCnt = n := by simp [x₂, x₁, RData.set, hhdr.hdr_n]
  have hx₂_base : x₂.regs mBase = base := by simp [x₂, x₁, RData.set, hbase]
  have hx₂_z : x₂.regs mZero = 0 := by simp [x₂, RData.set]
  have hx₂_o : x₂.regs mOne = 1 := by simp [x₂, RData.set]
  have hx₂_arg : resizableArgMatch o x₂.regs := by
    have htag : x₂.regs mTag = x.regs mTag := by simp [x₂, x₁, RData.set]
    have hu : x₂.regs mArgU = x.regs mArgU := by simp [x₂, x₁, RData.set]
    have hv : x₂.regs mArgV = x.regs mArgV := by simp [x₂, x₁, RData.set]
    cases o with
    | query _ => exact ⟨htag.trans harg.1, hu.trans harg.2⟩
    | insert _ _ => exact ⟨htag.trans harg.1, hu.trans harg.2.1, hv.trans harg.2.2⟩
    | delete _ => exact ⟨htag.trans harg.1, hu.trans harg.2⟩
  -- Branch on `n = 0` vs `1 ≤ n`
  by_cases hn0 : n = 0
  · have hc_n0 : (Cond.eq mCnt mZero).Holds x₂.toData := by
      change x₂.regs mCnt = x₂.regs mZero; rw [hx₂_cnt, hx₂_z, hn0]
    have hN0 : st.cap = 0 := by rcases hanc.1 with ⟨_, hN0⟩ | ⟨h1, _, _, _⟩ <;> omega
    have hinit0 : st.initCount = 0 := hanc.2.2.1.mp hn0
    have hs_emp : st.dict = Dictionary.empty U := dict_eq_empty_of_card_zero hn0
    have hfr8 : x.frontier = base + 8 := by
      rw [hfr, hN0, hn0]; unfold compactedEpochWords rootHdrWords; simp
    have hhdr0 : RootHeaderValid U V w 0 0 0 base x.mem := by
      have h0 : RootHeaderValid U V w st.cap n st.initCount base x.mem := hhdr
      rwa [hN0, hn0, hinit0] at h0
    have hpot_x_zero : resizablePotential U w st.cap n st.initCount base x = 0 := by
      rw [hN0, hn0, hinit0]; exact resizablePotential_zero U w base x
    cases o with
    | query u =>
      have hc_t0 : (Cond.eq mTag mZero).Holds x₂.toData := by
        change x₂.regs mTag = x₂.regs mZero; rw [hx₂_arg.1, hx₂_z]
      set z := (x₂.set mOutTag 0).set mOutVal 0
      have hex_out :=
        (RDemonicExec.const (B := .exact) (d := mOutTag) (v := 0) (x := x₂) hL_x
          (fits_zero w)).seq_eq
        (RDemonicExec.const (B := .exact) (d := mOutVal) (v := 0) (x := x₂.set mOutTag 0) hL_x
          (fits_zero w))
      have hzb : z.Bounded w := (hx₂b.set (fits_zero w)).set (fits_zero w)
      have hex_all : RDemonicExec w L_peak resizableOpCode x 9 (· = z) :=
        (hex_ldn.seq_eq <| hex_z0.seq_eq <| hex_o1.seq_eq <|
          RDemonicExec.branch_pos hc_n0 (RDemonicExec.branch_pos hc_t0 hex_out)).mono
          (by decide) (fun _ h => h)
      let q_out : StepROutcome (LatentSeed U) (Option ℕ) rResize := ⟨ls, z, none⟩
      have hres_none : ((Dynamic.spec U V U).stepFn st.dict (.query u)).2 = none := by
        change st.dict u = none; rw [hs_emp]; rfl
      refine ⟨PMF.pure q_out, _, execRCodeDist_of_demonic_outcome q_out hex_all, fun q hq => ?_,
        fun hn'_pos => absurd hn0 hn'_pos.ne', ?_⟩
      · rw [PMF.support_pure, Set.mem_singleton_iff] at hq; subst hq
        refine ⟨⟨hrep.cap_eq, ?_, by simp [q_out, z, RData.set, hx₂_base],
          fun hn'_pos => absurd hn0 hn'_pos.ne'⟩, hres_none.symm,
          by simp [q_out, z, resizableDecode, decode, RData.set], fun _ _ => rfl⟩
        dsimp only [st', EpochState.step, nextEpochCap, nextEpochInit]
        rw [hN0, hinit0, hs_emp, Dictionary.dom_empty]
        exact compactedRep_empty hzb hfr8 hhdr0
      · rw [ite_eq_right (by omega : ¬0 < n), add_zero, hpot_x_zero, Nat.cast_zero, zero_add]
        rw [tsum_eq_single q_out (fun b hb => by simp [PMF.pure_apply, hb])]
        simp only [PMF.pure_apply_self, one_mul]
        dsimp only [st', EpochState.step, nextEpochCap, nextEpochInit, n']
        rw [hN0, hinit0, show (Dictionary.dom st.dict).card = 0 from hn0,
          resizablePotential_zero, Nat.cast_zero, add_zero]
        exact (Nat.cast_le (α := ℝ≥0∞)).mpr (by unfold resizableBaseCharge; omega)
    | insert u v =>
      have hnc_t0 : ¬(Cond.eq mTag mZero).Holds x₂.toData := by
        change x₂.regs mTag ≠ x₂.regs mZero; rw [hx₂_arg.1, hx₂_z]; decide
      have hc_t1 : (Cond.eq mTag mOne).Holds x₂.toData := by
        change x₂.regs mTag = x₂.regs mOne; rw [hx₂_arg.1, hx₂_o]
      have hle_ins : base + compactedEpochWords U V w (targetCap U 1) 1 ≤ L_peak := by
        dsimp only [L_peak, stepExactPeakWords]; rw [ite_eq_left hn0]
      obtain ⟨zOf, T_init, hex_init, hinit_all, hcost_init⟩ :=
        initFirstEpochCode_execRCodeDist u v hx₂b hfr8 hhdr0 hval.2
          (hfit_peak.of_le hle_ins) hx₂_base hx₂_arg.2.1 hx₂_arg.2.2
      let μ_u := PMF.uniformOfFintype (QuotHashSeed U (targetCap U 1))
      have hex_code : ExecRCodeDist w resizableOpCode x (μ_u.map zOf) (T_init + 9) L_peak :=
        ((ExecRCodeDist.of_demonicExec hex_ldn).seq_pure <|
          (ExecRCodeDist.of_demonicExec hex_z0).seq_pure <|
          (ExecRCodeDist.of_demonicExec hex_o1).seq_pure <|
          ExecRCodeDist.branch_pos hc_n0 <|
          ExecRCodeDist.branch_neg hnc_t0 <|
          ExecRCodeDist.branch_pos hc_t1 (hex_init.mono_peak hle_ins)).mono
          (le_of_eq (by push_cast; ring))
      have hst'_cap : st'.cap = targetCap U 1 := by
        dsimp only [st', EpochState.step, nextEpochCap]; rw [ite_eq_left hn0]
      have hst'_init : st'.initCount = 1 := by
        dsimp only [st', EpochState.step, nextEpochInit]; rw [ite_eq_left hn0]
      have hn'1 : n' = 1 := by
        dsimp only [n', st', EpochState.step, Dynamic.spec, StateTransitionSpec.stepFn,
          Dynamic.step]
        rw [hs_emp, Dictionary.dom_insert, Dictionary.dom_empty]; rfl
      let mkOut (θ' : QuotHashSeed U (targetCap U 1)) :
          StepROutcome (LatentSeed U) Unit rResize :=
        ⟨⟨targetCap U 1, θ'⟩, zOf θ', ()⟩
      let μ_out := μ_u.map mkOut
      have hmap_data : μ_u.map zOf = μ_out.map StepROutcome.data := by
        dsimp only [μ_out]; rw [PMF.map_comp]; rfl
      have hcap_ne : st'.cap ≠ st.cap := by
        rw [hst'_cap, hN0]; unfold targetCap; have := hhdr.pos_U; simp; omega
      refine ⟨μ_out, _, hex_code.congr_dist hmap_data le_rfl, fun q hq => ?_,
        fun _ => ?_, ?_⟩
      · dsimp only [μ_out] at hq
        rw [PMF.mem_support_map_iff] at hq; obtain ⟨θ', _, rfl⟩ := hq
        obtain ⟨hzb, hzf, hsp, hzb_reg, hbel⟩ := hinit_all θ'
        have hs_eq : st'.dict = Function.update (Dictionary.empty U) u (some v) := by
          dsimp only [st', EpochState.step, Dynamic.spec, StateTransitionSpec.stepFn,
            Dynamic.step]
          rw [hs_emp]
        have hcard1 : (Dictionary.dom (Function.update (Dictionary.empty U) u (some v))).card =
            1 := by
          rw [Dictionary.dom_insert, Dictionary.dom_empty]; rfl
        refine ⟨⟨hst'_cap.symm, ?_, hzb_reg, fun _ => ?_⟩, rfl, rfl, hbel⟩
        · rw [hst'_cap, hst'_init, hs_eq, hcard1]
          exact compactedRep_of_split hzb hzf (epochValid_targetCap hhdr.pos_U) hsp
        · rw [hst'_init, hs_eq, hcard1]
          have htr : ∀ (C : ℕ), C = targetCap U 1 →
              CompactedSplitRep base (base + offCompItems U w C) U V w C 1 1
                ((mkOut θ').latent.seedAt C) (Function.update (Dictionary.empty U) u (some v))
                ⟨(zOf θ').mem, (zOf θ').frontier⟩ := by
            rintro _ rfl
            simpa only [mkOut, LatentSeed.seedAt_mk] using hsp
          exact htr st'.cap hst'_cap
      · rw [ite_eq_right hcap_ne]
        have htr : ∀ (C : ℕ), C = targetCap U 1 →
            μ_out.map (fun q => q.latent.seedAt C) = PMF.uniformOfFintype (QuotHashSeed U C) := by
          rintro _ rfl
          dsimp only [μ_out]; rw [PMF.map_comp]
          have hid_fn : (fun q : StepROutcome (LatentSeed U) Unit rResize =>
              q.latent.seedAt (targetCap U 1)) ∘ mkOut = id :=
            funext fun θ' => LatentSeed.seedAt_mk _ θ'
          rw [hid_fn, PMF.map_id]
        exact htr st'.cap hst'_cap
      · rw [ite_eq_right (by omega : ¬0 < n), add_zero, hpot_x_zero, Nat.cast_zero, zero_add]
        have htsum_pot : (∑' q, μ_out q *
            (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)) =
            ∑' θ', μ_u θ' * (inEpochPotential U w (targetCap U 1) base (zOf θ') : ℝ≥0∞) := by
          dsimp only [μ_out]; rw [Cslib.Probability.PMF.tsum_map_mul]
          refine tsum_congr fun θ' => ?_
          rw [hst'_cap, hst'_init, hn'1]
          dsimp only [mkOut]
          unfold resizablePotential
          rw [Nat.dist_self, Nat.mul_zero, Nat.add_zero]
        rw [htsum_pot]
        have hb_ge :
            (initFirstCharge : ℝ≥0∞) + ((10 : ℕ) : ℝ≥0∞) ≤ (resizableBaseCharge : ℝ≥0∞) := by
          rw [← Nat.cast_add]
          exact (Nat.cast_le (α := ℝ≥0∞)).mpr
            (Nat.add_le_add (le_max_left _ _) (by decide : 10 ≤ 50))
        have h9_le_10 : (9 : ℝ≥0∞) ≤ ((10 : ℕ) : ℝ≥0∞) :=
          (Nat.cast_le (α := ℝ≥0∞)).mpr (by decide : 9 ≤ 10)
        calc (T_init + 9) +
              (∑' θ', μ_u θ' * (inEpochPotential U w (targetCap U 1) base (zOf θ') : ℝ≥0∞))
            = (T_init + ∑' θ', μ_u θ' *
                (inEpochPotential U w (targetCap U 1) base (zOf θ') : ℝ≥0∞)) + 9 :=
                add_right_comm T_init 9 _
          _ ≤ (initFirstCharge : ℝ≥0∞) + ((10 : ℕ) : ℝ≥0∞) := add_le_add hcost_init h9_le_10
          _ ≤ (resizableBaseCharge : ℝ≥0∞) := hb_ge
    | delete u =>
      have hnc_t0 : ¬(Cond.eq mTag mZero).Holds x₂.toData := by
        change x₂.regs mTag ≠ x₂.regs mZero; rw [hx₂_arg.1, hx₂_z]; decide
      have hnc_t1 : ¬(Cond.eq mTag mOne).Holds x₂.toData := by
        change x₂.regs mTag ≠ x₂.regs mOne; rw [hx₂_arg.1, hx₂_o]; decide
      set z := x₂.set mZero (x₂.regs mZero)
      have hex_nop := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak)
        (d := mZero) (s := mZero) (x := x₂) hL_x
      have hzb : z.Bounded w := hx₂b.set (hx₂b.regs_fits mZero)
      have hex_all : RDemonicExec w L_peak resizableOpCode x 11 (· = z) :=
        (hex_ldn.seq_eq <| hex_z0.seq_eq <| hex_o1.seq_eq <|
          RDemonicExec.branch_pos hc_n0
            (RDemonicExec.branch_neg hnc_t0 (RDemonicExec.branch_neg hnc_t1 hex_nop))).mono
          (by decide) (fun _ h => h)
      let q_out : StepROutcome (LatentSeed U) Unit rResize := ⟨ls, z, ()⟩
      have hs'_emp : st'.dict = Dictionary.empty U := by
        dsimp only [st', EpochState.step, Dynamic.spec, StateTransitionSpec.stepFn, Dynamic.step]
        rw [hs_emp]; funext k
        by_cases hku : k = u <;> simp [hku, Dictionary.empty]
      have hn'0 : n' = 0 := by dsimp only [n']; rw [hs'_emp, Dictionary.dom_empty]; rfl
      refine ⟨PMF.pure q_out, _, execRCodeDist_of_demonic_outcome q_out hex_all, fun q hq => ?_,
        fun hn'_pos => absurd hn'0 hn'_pos.ne', ?_⟩
      · rw [PMF.support_pure, Set.mem_singleton_iff] at hq; subst hq
        have hcap0 : st'.cap = 0 := by
          dsimp only [st', EpochState.step, nextEpochCap]; rw [ite_eq_left hn0]
        have hinit0' : st'.initCount = 0 := by
          dsimp only [st', EpochState.step, nextEpochInit]; rw [ite_eq_left hn0]
        refine ⟨⟨hrep.cap_eq.trans (hN0.trans hcap0.symm), ?_,
          by simp [q_out, z, RData.set, hx₂_base],
          fun hn'_pos => absurd hn'0 hn'_pos.ne'⟩, rfl, rfl, fun _ _ => rfl⟩
        rw [hcap0, hinit0', hs'_emp, Dictionary.dom_empty]
        exact compactedRep_empty hzb hfr8 hhdr0
      · rw [ite_eq_right (by omega : ¬0 < n), add_zero, hpot_x_zero, Nat.cast_zero, zero_add]
        rw [tsum_eq_single q_out (fun b hb => by simp [PMF.pure_apply, hb])]
        simp only [PMF.pure_apply_self, one_mul]
        have hcap0 : st'.cap = 0 := by
          dsimp only [st', EpochState.step, nextEpochCap]; rw [ite_eq_left hn0]
        have hinit0' : st'.initCount = 0 := by
          dsimp only [st', EpochState.step, nextEpochInit]; rw [ite_eq_left hn0]
        rw [hcap0, hinit0', hn'0, resizablePotential_zero, Nat.cast_zero, add_zero]
        exact (Nat.cast_le (α := ℝ≥0∞)).mpr (by unfold resizableBaseCharge; omega)
  · -- Active epoch: `1 ≤ n`
    have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have hnc_n0 : ¬(Cond.eq mCnt mZero).Holds x₂.toData := by
      change x₂.regs mCnt ≠ x₂.regs mZero; rw [hx₂_cnt, hx₂_z]; exact hn0
    have hsplit := hrep.active_split hn_pos
    cases o with
    | query u =>
      have hc_t0 : (Cond.eq mTag mZero).Holds x₂.toData := by
        change x₂.regs mTag = x₂.regs mZero; rw [hx₂_arg.1, hx₂_z]
      obtain ⟨q_out, stepsOp, hex_op, hqls, hqrep, hqres, hqdec, hqbel, hqcost⟩ :=
        exec_inEpoch_branch (overhead := 8) (.query u) hx₂b hn_pos hanc.1 ⟨hval, hanc.1⟩
          hfr hsplit hx₂_base hx₂_arg (fun _ _ => rfl) rfl (by simp) rfl hfit_peak rfl rfl
          hrep.cap_eq (by decide)
      have hex_all : RDemonicExec w L_peak resizableOpCode x (8 + stepsOp) (· = q_out.data) :=
        (hex_ldn.seq_eq <| hex_z0.seq_eq <| hex_o1.seq_eq <|
          RDemonicExec.branch_neg hnc_n0 (RDemonicExec.branch_pos hc_t0 hex_op)).mono
          (by omega) (fun _ h => h)
      exact package_active_inEpoch_step hn_pos rfl hex_all hqls hqrep hqres hqdec hqbel hqcost
    | insert u v =>
      have hnc_t0 : ¬(Cond.eq mTag mZero).Holds x₂.toData := by
        change x₂.regs mTag ≠ x₂.regs mZero; rw [hx₂_arg.1, hx₂_z]; decide
      have hc_t1 : (Cond.eq mTag mOne).Holds x₂.toData := by
        change x₂.regs mTag = x₂.regs mOne; rw [hx₂_arg.1, hx₂_o]
      -- Load `N` from `base + 5` and `U - 1` from `base + 0` (6 steps)
      obtain ⟨hex_ldN, hx₃b⟩ := loadAtOffCode_exec (rAddr := mBase) (rDst := mNNew) (rTmp := mCur)
        (off := 5) hx₂b hL_x (mReg_ne (by decide)) hx₂_base (hfit6.of_le (by decide))
        (by change base + 5 < x.frontier; rw [hfr]; omega)
      set x₃ := (x₂.set mCur (base + 5)).set mNNew (x.mem (base + 5))
      have hx₃_base : x₃.regs mBase = base := by
        rw [show x₃.regs mBase = x₂.regs mBase by simp [x₃, RData.set], hx₂_base]
      obtain ⟨hex_ldU, hx₄b⟩ := loadAtOffCode_exec (rAddr := mBase) (rDst := mTmpA) (rTmp := mCur)
        (off := 0) hx₃b hL_x (mReg_ne (by decide)) hx₃_base (fits_zero w)
        (by change base + 0 < x.frontier; rw [hfr]; omega)
      set x₄ := (x₃.set mCur (base + 0)).set mTmpA (x.mem (base + 0))
      have hx₄_cnt : x₄.regs mCnt = n := by
        rw [show x₄.regs mCnt = x₂.regs mCnt by simp [x₄, x₃, RData.set], hx₂_cnt]
      have hx₄_nn : x₄.regs mNNew = st.cap := by simp [x₄, x₃, RData.set, hhdr.hdr_N]
      have hx₄_u1 : x₄.regs mTmpA = U - 1 := by
        change x.mem (base + 0) = U - 1; rw [Nat.add_zero]; exact hhdr.hdr_U
      have hx₄_base : x₄.regs mBase = base := by
        rw [show x₄.regs mBase = x₃.regs mBase by simp [x₄, RData.set], hx₃_base]
      have hx₄_arg : resizableArgMatch (.insert u v) x₄.regs := by
        exact ⟨by rw [show x₄.regs mTag = x₂.regs mTag by simp [x₄, x₃, RData.set], hx₂_arg.1],
          by rw [show x₄.regs mArgU = x₂.regs mArgU by simp [x₄, x₃, RData.set], hx₂_arg.2.1],
          by rw [show x₄.regs mArgV = x₂.regs mArgV by simp [x₄, x₃, RData.set], hx₂_arg.2.2]⟩
      have hn_le_cap : n ≤ st.cap := by rcases hanc.1 with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
      have hcap_le_4n : st.cap ≤ 4 * n := by rcases hanc.1 with ⟨h0, _⟩ | ⟨_, _, h4, _⟩ <;> omega
      have hcap_le_U : st.cap ≤ U := by rcases hanc.1 with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
      obtain ⟨hn_le_n', hn'_le_n1⟩ := card_dom_insert_bounds st.dict u v
      change n ≤ n' at hn_le_n'
      change n' ≤ n + 1 at hn'_le_n1
      have hdist_ins : Nat.dist n n' ≤ 1 := by unfold Nat.dist; omega
      by_cases hn_eq : n = st.cap
      · have hc_eq : (Cond.eq mCnt mNNew).Holds x₄.toData := by
          change x₄.regs mCnt = x₄.regs mNNew; rw [hx₄_cnt, hx₄_nn]; exact hn_eq
        by_cases hU_lt : U - 1 < st.cap
        · -- `st.cap = U` (`n = U`): hit in place, no migration
          have hc_lt : (Cond.lt mTmpA mNNew).Holds x₄.toData := by
            change x₄.regs mTmpA < x₄.regs mNNew; rw [hx₄_u1, hx₄_nn]; exact hU_lt
          have hcap_U : st.cap = U := by have := hhdr.pos_U; omega
          have hnot_mig : ¬(n = st.cap ∧ st.cap < U) := by omega
          have hn'_eq_U : n' = st.cap := by
            dsimp only [n', st', EpochState.step, Dynamic.spec, StateTransitionSpec.stepFn,
              Dynamic.step]
            rw [card_dom_insert_eq_of_card_eq_U (hn_eq.trans hcap_U), hcap_U]
          have hval_in : InEpochValid V st.cap st.dict (.insert u v) :=
            ⟨hval, show EpochValid U n' st.cap from
              Or.inr ⟨by omega, hn'_eq_U.le, by omega, hcap_le_U⟩⟩
          have hpeak_eq : stepExactPeakWords V w st.cap st.dict (.insert u v) =
              inEpochPeakWords V w st.cap n st.dict (.insert u v) := by
            dsimp only [stepExactPeakWords]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_right hnot_mig]
          have hcap_same : st'.cap = st.cap := by
            dsimp only [st', EpochState.step, nextEpochCap]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_right hnot_mig]
          have hinit_same : st'.initCount = st.initCount := by
            dsimp only [st', EpochState.step, nextEpochInit]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_right hnot_mig]
          obtain ⟨q_out, stepsOp, hex_op, hqls, hqrep, hqres, hqdec, hqbel, hqcost⟩ :=
            exec_inEpoch_branch (overhead := 18) (.insert u v) hx₄b hn_pos hanc.1 hval_in
              hfr hsplit hx₄_base hx₄_arg (fun _ _ => rfl) rfl hdist_ins hpeak_eq hfit_peak
              hcap_same hinit_same hrep.cap_eq (by decide)
          have hex_ins : RDemonicExec w L_peak resizableInsertActiveCode x₂ (8 + stepsOp)
              (· = q_out.data) :=
            (hex_ldN.seq_eq (hex_ldU.seq_eq
              (RDemonicExec.branch_pos hc_eq (RDemonicExec.branch_pos hc_lt hex_op)))).mono
              (by omega) (fun _ h => h)
          have hex_all : RDemonicExec w L_peak resizableOpCode x (18 + stepsOp)
              (· = q_out.data) :=
            (hex_ldn.seq_eq <| hex_z0.seq_eq <| hex_o1.seq_eq <|
              RDemonicExec.branch_neg hnc_n0
                (RDemonicExec.branch_neg hnc_t0 (RDemonicExec.branch_pos hc_t1 hex_ins))).mono
              (by omega) (fun _ h => h)
          exact package_active_inEpoch_step hn_pos hcap_same hex_all hqls hqrep hqres hqdec hqbel
            hqcost
        · -- `n = st.cap < U`: capacity-doubling migration!
          have hnc_lt : ¬(Cond.lt mTmpA mNNew).Holds x₄.toData := by
            change ¬(x₄.regs mTmpA < x₄.regs mNNew); rw [hx₄_u1, hx₄_nn]; exact hU_lt
          have hcap_lt_U : st.cap < U := by have := hhdr.pos_U; omega
          have hmig : n = st.cap ∧ st.cap < U := ⟨hn_eq, hcap_lt_U⟩
          have hn_lt_U : n < U := hn_eq ▸ hcap_lt_U
          have hval_tc : InEpochValid V (targetCap U n) st.dict (.insert u v) := by
            refine ⟨hval, show EpochValid U n' (targetCap U n) from
              Or.inr ⟨by omega, ?_, ?_, ?_⟩⟩
            · unfold targetCap; rw [ite_eq_right hn0]
              exact hn'_le_n1.trans (le_min (by omega) hn_lt_U)
            · unfold targetCap; rw [ite_eq_right hn0]
              exact (min_le_left _ _).trans (by omega)
            · unfold targetCap; rw [ite_eq_right hn0]; exact min_le_right _ _
          have hpeak_eq : stepExactPeakWords V w st.cap st.dict (.insert u v) =
              max (migratePeakWords U V w st.cap n)
                (inEpochPeakWords V w (targetCap U n) n st.dict (.insert u v)) := by
            dsimp only [stepExactPeakWords]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_left hmig]
          have hst'_cap : st'.cap = targetCap U n := by
            dsimp only [st', EpochState.step, nextEpochCap]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_left hmig]
          have hst'_init : st'.initCount = n := by
            dsimp only [st', EpochState.step, nextEpochInit]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_left hmig]
          have hdist_rel : n ≤ 2 * Nat.dist n st.initCount :=
            (insert_mig_dist_eq hn_pos hanc hn_eq hcap_lt_U).le
          have hdist_post : Nat.dist n' n ≤ 1 := by rw [Nat.dist_comm]; exact hdist_ins
          obtain ⟨μ_out, T_mig_op, hex_mig_op, hout_all, hmap_u, hcost_mig_op⟩ :=
            exec_migrate_then_inEpoch (overhead := 19) (.insert u v) hx₄b hn_pos hanc hval_tc
              hfr hsplit hx₄_base hx₄_arg (fun _ _ => rfl) hdist_rel hdist_post hpeak_eq
              hfit_peak hst'_cap hst'_init (by decide)
          have hex_ins : ExecRCodeDist w resizableInsertActiveCode x₂
              (μ_out.map StepROutcome.data) (9 + T_mig_op) L_peak :=
            ((ExecRCodeDist.of_demonicExec hex_ldN).seq_pure <|
              (ExecRCodeDist.of_demonicExec hex_ldU).seq_pure <|
              ExecRCodeDist.branch_pos hc_eq <|
              ExecRCodeDist.branch_neg hnc_lt hex_mig_op).mono (le_of_eq (by push_cast; ring))
          have hex_all : ExecRCodeDist w resizableOpCode x
              (μ_out.map StepROutcome.data) (19 + T_mig_op) L_peak :=
            ((ExecRCodeDist.of_demonicExec hex_ldn).seq_pure <|
              (ExecRCodeDist.of_demonicExec hex_z0).seq_pure <|
              (ExecRCodeDist.of_demonicExec hex_o1).seq_pure <|
              ExecRCodeDist.branch_neg hnc_n0 <|
              ExecRCodeDist.branch_neg hnc_t0 <|
              ExecRCodeDist.branch_pos hc_t1 hex_ins).mono (le_of_eq (by push_cast; ring))
          have hcap_ne : st'.cap ≠ st.cap := by
            rw [hst'_cap, ← hn_eq]; unfold targetCap; rw [ite_eq_right hn0]
            have : n + 1 ≤ min (2 * n) U := le_min (by omega) hn_lt_U
            omega
          refine ⟨μ_out, _, hex_all, hout_all,
            fun _ => by rw [ite_eq_right hcap_ne]; exact hmap_u, ?_⟩
          calc ((19 : ℝ≥0∞) + T_mig_op) +
                (∑' q, μ_out q *
                  (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞))
              ≤ (resizablePotential U w st.cap n st.initCount base x : ℝ≥0∞) +
                (resizableBaseCharge : ℝ≥0∞) := hcost_mig_op
            _ ≤ _ := add_le_add le_rfl le_self_add
      · -- `n < st.cap`: active in-epoch insert, no migration
        have hnc_eq : ¬(Cond.eq mCnt mNNew).Holds x₄.toData := by
          change x₄.regs mCnt ≠ x₄.regs mNNew; rw [hx₄_cnt, hx₄_nn]; exact hn_eq
        have hn_lt_cap : n < st.cap := lt_of_le_of_ne hn_le_cap hn_eq
        have hnot_mig : ¬(n = st.cap ∧ st.cap < U) := fun h => hn_eq h.1
        have hval_in : InEpochValid V st.cap st.dict (.insert u v) :=
          ⟨hval, show EpochValid U n' st.cap from
            Or.inr ⟨by omega, by omega, by omega, hcap_le_U⟩⟩
        have hpeak_eq : stepExactPeakWords V w st.cap st.dict (.insert u v) =
            inEpochPeakWords V w st.cap n st.dict (.insert u v) := by
          dsimp only [stepExactPeakWords]
          change (if n = 0 then _ else _) = _
          rw [ite_eq_right hn0, ite_eq_right hnot_mig]
        have hcap_same : st'.cap = st.cap := by
          dsimp only [st', EpochState.step, nextEpochCap]
          change (if n = 0 then _ else _) = _
          rw [ite_eq_right hn0, ite_eq_right hnot_mig]
        have hinit_same : st'.initCount = st.initCount := by
          dsimp only [st', EpochState.step, nextEpochInit]
          change (if n = 0 then _ else _) = _
          rw [ite_eq_right hn0, ite_eq_right hnot_mig]
        obtain ⟨q_out, stepsOp, hex_op, hqls, hqrep, hqres, hqdec, hqbel, hqcost⟩ :=
          exec_inEpoch_branch (overhead := 18) (.insert u v) hx₄b hn_pos hanc.1 hval_in
            hfr hsplit hx₄_base hx₄_arg (fun _ _ => rfl) rfl hdist_ins hpeak_eq hfit_peak
            hcap_same hinit_same hrep.cap_eq (by decide)
        have hex_ins : RDemonicExec w L_peak resizableInsertActiveCode x₂ (8 + stepsOp)
            (· = q_out.data) :=
          (hex_ldN.seq_eq (hex_ldU.seq_eq (RDemonicExec.branch_neg hnc_eq hex_op))).mono
            (by omega) (fun _ h => h)
        have hex_all : RDemonicExec w L_peak resizableOpCode x (18 + stepsOp)
            (· = q_out.data) :=
          (hex_ldn.seq_eq <| hex_z0.seq_eq <| hex_o1.seq_eq <|
            RDemonicExec.branch_neg hnc_n0
              (RDemonicExec.branch_neg hnc_t0 (RDemonicExec.branch_pos hc_t1 hex_ins))).mono
            (by omega) (fun _ h => h)
        exact package_active_inEpoch_step hn_pos hcap_same hex_all hqls hqrep hqres hqdec hqbel
          hqcost
    | delete u =>
      have hnc_t0 : ¬(Cond.eq mTag mZero).Holds x₂.toData := by
        change x₂.regs mTag ≠ x₂.regs mZero; rw [hx₂_arg.1, hx₂_z]; decide
      have hnc_t1 : ¬(Cond.eq mTag mOne).Holds x₂.toData := by
        change x₂.regs mTag ≠ x₂.regs mOne; rw [hx₂_arg.1, hx₂_o]; decide
      by_cases hn1 : n = 1
      · -- Singleton delete (`n = 1`): `deleteLastOneCode`
        have hc_n1 : (Cond.eq mCnt mOne).Holds x₂.toData := by
          change x₂.regs mCnt = x₂.regs mOne; rw [hx₂_cnt, hx₂_o, hn1]
        have hpeak_d1 : L_peak = x₂.frontier := by
          dsimp only [L_peak, stepExactPeakWords, x₂, x₁, RData.set]
          change base + (if n = 0 then _ else _) = x.frontier
          rw [ite_eq_right hn0, ite_eq_left hn1, hfr, hn1]
        have hev1 : EpochValid U 1 st.cap := by
          have h0 : EpochValid U n st.cap := hanc.1
          rwa [hn1] at h0
        have hfr1 : x₂.frontier = base + compactedEpochWords U V w st.cap 1 := by
          change x.frontier = _; rw [hfr, hn1]
        have hsplit1 : CompactedSplitRep base (base + offCompItems U w st.cap) U V w st.cap
            1 st.initCount θ st.dict ⟨x₂.mem, x₂.frontier⟩ := by
          have h0 : CompactedSplitRep base (base + offCompItems U w st.cap) U V w st.cap
              n st.initCount θ st.dict ⟨x.mem, x.frontier⟩ := hsplit
          rwa [hn1] at h0
        obtain ⟨z, steps_d1, hex_d1, hzb, hz_base, hbel_z, hd1_cases⟩ :=
          deleteLastOneCode_demonicExec u hx₂b hev1 hfr1 hsplit1 hx₂_base hx₂_arg.2
        have hex_d1_L : RDemonicExec w L_peak deleteLastOneCode x₂ steps_d1 (· = z) := by
          rw [hpeak_d1]; exact hex_d1
        have hex_all : RDemonicExec w L_peak resizableOpCode x (12 + steps_d1) (· = z) :=
          (hex_ldn.seq_eq <| hex_z0.seq_eq <| hex_o1.seq_eq <|
            RDemonicExec.branch_neg hnc_n0
              (RDemonicExec.branch_neg hnc_t0
                (RDemonicExec.branch_neg hnc_t1
                  (RDemonicExec.branch_pos hc_n1 hex_d1_L)))).mono
            (by omega) (fun _ h => h)
        by_cases hsome : (st.dict u).isSome
        · rw [ite_eq_left hsome] at hd1_cases
          obtain ⟨hs_empty, hrep_z, _⟩ := hd1_cases
          have hs'_emp : st'.dict = Dictionary.empty U := hs_empty
          have hn'0 : n' = 0 := by dsimp only [n']; rw [hs'_emp, Dictionary.dom_empty]; rfl
          have hcap0 : st'.cap = 0 := by
            dsimp only [st', EpochState.step, nextEpochCap]
            change (if n = 0 then _ else _) = 0
            rw [ite_eq_right hn0, ite_eq_left hn1, ite_eq_left hsome]
          have hinit0' : st'.initCount = 0 := by
            dsimp only [st', EpochState.step, nextEpochInit]
            change (if n = 0 then _ else _) = 0
            rw [ite_eq_right hn0, ite_eq_left hn1, ite_eq_left hsome]
          let q_out : StepROutcome (LatentSeed U) Unit rResize := ⟨LatentSeed.empty U, z, ()⟩
          refine ⟨PMF.pure q_out, _, execRCodeDist_of_demonic_outcome q_out hex_all,
            fun q hq => ?_, fun hn'_pos => absurd hn'0 hn'_pos.ne', ?_⟩
          · rw [PMF.support_pure, Set.mem_singleton_iff] at hq; subst hq
            refine ⟨⟨hcap0.symm, ?_, hz_base, fun hn'_pos => absurd hn'0 hn'_pos.ne'⟩,
              rfl, rfl, hbel_z⟩
            rw [hcap0, hinit0', hs'_emp, Dictionary.dom_empty]
            exact hrep_z
          · rw [ite_eq_left (show 0 < n from hn_pos),
              tsum_eq_single q_out (fun b hb => by simp [PMF.pure_apply, hb])]
            simp only [PMF.pure_apply_self, one_mul]
            rw [hcap0, hinit0', hn'0, resizablePotential_zero, Nat.cast_zero, add_zero]
            have hle_b : 12 + steps_d1 ≤ resizableBaseCharge := by
              unfold resizableBaseCharge
              have := le_max_of_le_right (b := initFirstCharge)
                (le_max_left deleteLastOneCharge (inEpochCharge + 2 * migLinearFactor))
              omega
            exact ((Nat.cast_le (α := ℝ≥0∞)).mpr hle_b).trans (le_self_add.trans le_add_self)
        · rw [ite_eq_right hsome] at hd1_cases
          obtain ⟨hs_same, hzf_same, hsplit_z, hpot_eq, _⟩ := hd1_cases
          have hs'_same : st'.dict = st.dict := hs_same
          have hn'1 : n' = 1 := by dsimp only [n']; rw [hs'_same]; exact hn1
          have hcap_same : st'.cap = st.cap := by
            dsimp only [st', EpochState.step, nextEpochCap]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_left hn1, ite_eq_right hsome]
          have hinit_same : st'.initCount = st.initCount := by
            dsimp only [st', EpochState.step, nextEpochInit]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_left hn1, ite_eq_right hsome]
          let q_out : StepROutcome (LatentSeed U) Unit rResize := ⟨ls, z, ()⟩
          refine ⟨PMF.pure q_out, _, execRCodeDist_of_demonic_outcome q_out hex_all,
            fun q hq => ?_, fun _ => ?_, ?_⟩
          · rw [PMF.support_pure, Set.mem_singleton_iff] at hq; subst hq
            refine ⟨⟨hrep.cap_eq.trans hcap_same.symm, ?_, hz_base, fun _ => ?_⟩,
              rfl, rfl, hbel_z⟩
            · rw [hcap_same, hinit_same, hs'_same, show (Dictionary.dom st.dict).card = 1 from hn1]
              exact compactedRep_of_split hzb hzf_same hev1 hsplit_z
            · rw [hcap_same, hinit_same, hs'_same, show (Dictionary.dom st.dict).card = 1 from hn1]
              exact hsplit_z
          · rw [ite_eq_left hcap_same]; exact ⟨hn_pos, by simp [q_out, θ]⟩
          · rw [ite_eq_left (show 0 < n from hn_pos),
              tsum_eq_single q_out (fun b hb => by simp [PMF.pure_apply, hb])]
            simp only [PMF.pure_apply_self, one_mul]
            have hpot_full : resizablePotential U w st'.cap n' st'.initCount base q_out.data =
                resizablePotential U w st.cap n st.initCount base x := by
              rw [hcap_same, hinit_same, hn'1, hn1]
              unfold resizablePotential
              dsimp only [q_out]
              rw [hpot_eq]
              rfl
            rw [hpot_full]
            have hle_b : 12 + steps_d1 ≤ resizableBaseCharge := by
              unfold resizableBaseCharge
              have := le_max_of_le_right (b := initFirstCharge)
                (le_max_left deleteLastOneCharge (inEpochCharge + 2 * migLinearFactor))
              omega
            calc ((12 + steps_d1 : ℕ) : ℝ≥0∞) +
                  (resizablePotential U w st.cap n st.initCount base x : ℝ≥0∞)
                = (resizablePotential U w st.cap n st.initCount base x : ℝ≥0∞) +
                  ((12 + steps_d1 : ℕ) : ℝ≥0∞) := by ring
              _ ≤ (resizablePotential U w st.cap n st.initCount base x : ℝ≥0∞) +
                  (resizableBaseCharge : ℝ≥0∞) :=
                add_le_add le_rfl ((Nat.cast_le (α := ℝ≥0∞)).mpr hle_b)
              _ ≤ _ := add_le_add le_rfl le_self_add
      · -- `2 ≤ n`: `resizableDeleteGeTwoCode`
        have hn2 : 2 ≤ n := by omega
        have hnc_n1 : ¬(Cond.eq mCnt mOne).Holds x₂.toData := by
          change x₂.regs mCnt ≠ x₂.regs mOne; rw [hx₂_cnt, hx₂_o]; exact hn1
        have hn_le_cap : n ≤ st.cap := by rcases hanc.1 with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
        have hcap_le_U : st.cap ≤ U := by rcases hanc.1 with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
        have hnU : n ≤ U := hn_le_cap.trans hcap_le_U
        obtain ⟨hn1_le_n', hn'_le_n⟩ := card_dom_delete_bounds st.dict u
        change n - 1 ≤ n' at hn1_le_n'
        change n' ≤ n at hn'_le_n
        have hdist_del : Nat.dist n n' ≤ 1 := by unfold Nat.dist; omega
        -- 1. `loadAtOffCode mBase mNNew mCur 5` (3 steps)
        obtain ⟨hex_ldN, hx₃b⟩ := loadAtOffCode_exec (rAddr := mBase) (rDst := mNNew)
          (rTmp := mCur) (off := 5) hx₂b hL_x (mReg_ne (by decide)) hx₂_base
          (hfit6.of_le (by decide)) (by change base + 5 < x.frontier; rw [hfr]; omega)
        set x₃ := (x₂.set mCur (base + 5)).set mNNew (x.mem (base + 5))
        have hx₃_cnt : x₃.regs mCnt = n := by
          rw [show x₃.regs mCnt = x₂.regs mCnt by simp [x₃, RData.set], hx₂_cnt]
        have hx₃_nn : x₃.regs mNNew = st.cap := by simp [x₃, RData.set, hhdr.hdr_N]
        have hx₃_one : x₃.regs mOne = 1 := by
          rw [show x₃.regs mOne = x₂.regs mOne by simp [x₃, RData.set], hx₂_o]
        -- 2. `mTmpA := mCnt - mOne; mTmpB := mNNew - mOne; mCur := 2; mTmpB := mTmpB >>> mCur`
        set x₄ := x₃.set mTmpA (n - 1)
        have hex_s1 := RDemonicExec.exactBin (f := .sub) (d := mTmpA) (i := mCnt) (j := mOne)
          (w := w) (L_peak := L_peak) (x := x₃) hL_x (v := n - 1)
          (by simp [BinOp.evalExact, hx₃_cnt, hx₃_one, show 1 ≤ n by omega])
          (hhdr.fits_U.of_le (by omega))
        set x₅ := x₄.set mTmpB (st.cap - 1)
        have hex_s2 := RDemonicExec.exactBin (f := .sub) (d := mTmpB) (i := mNNew) (j := mOne)
          (w := w) (L_peak := L_peak) (x := x₄) hL_x (v := st.cap - 1)
          (by
            have h4n : x₄.regs mNNew = st.cap := by
              rw [show x₄.regs mNNew = x₃.regs mNNew by simp [x₄, RData.set], hx₃_nn]
            have h4o : x₄.regs mOne = 1 := by
              rw [show x₄.regs mOne = x₃.regs mOne by simp [x₄, RData.set], hx₃_one]
            simp [BinOp.evalExact, h4n, h4o, show 1 ≤ st.cap by omega])
          (hhdr.fits_U.of_le (by omega))
        set x₆ := x₅.set mCur 2
        have hex_c2 := RDemonicExec.const (B := .exact) (d := mCur) (v := 2) (x := x₅) hL_x hfit2
        set x₇ := x₆.set mTmpB ((st.cap - 1) / 4)
        have hex_shr := RDemonicExec.exactBin (f := .shiftRight) (d := mTmpB) (i := mTmpB)
          (j := mCur) (w := w) (L_peak := L_peak) (x := x₆) hL_x (v := (st.cap - 1) / 4)
          (by
            change some (x₆.regs mTmpB >>> x₆.regs mCur) = some ((st.cap - 1) / 4)
            simp [x₆, x₅, RData.set, Nat.shiftRight_eq_div_pow])
          (hhdr.fits_U.of_le (by omega))
        have hx₇b : x₇.Bounded w :=
          (((hx₃b.set (hhdr.fits_U.of_le (by omega))).set (hhdr.fits_U.of_le (by omega))).set
            hfit2).set (hhdr.fits_U.of_le (by omega))
        have hx₇_ta : x₇.regs mTmpA = n - 1 := by simp [x₇, x₆, x₅, x₄, RData.set]
        have hx₇_tb : x₇.regs mTmpB = (st.cap - 1) / 4 := by simp [x₇, RData.set]
        have hx₇_base : x₇.regs mBase = base := by
          rw [show x₇.regs mBase = x₂.regs mBase by simp [x₇, x₆, x₅, x₄, x₃, RData.set], hx₂_base]
        have hx₇_arg : resizableArgMatch (.delete u) x₇.regs :=
          ⟨by rw [show x₇.regs mTag = x₂.regs mTag by simp [x₇, x₆, x₅, x₄, x₃, RData.set],
                hx₂_arg.1],
           by rw [show x₇.regs mArgU = x₂.regs mArgU by simp [x₇, x₆, x₅, x₄, x₃, RData.set],
                hx₂_arg.2]⟩
        by_cases hmig : 4 * (n - 1) < st.cap
        · -- Capacity-halving migration!
          have hnc_lt : ¬(Cond.lt mTmpB mTmpA).Holds x₇.toData := by
            change ¬(x₇.regs mTmpB < x₇.regs mTmpA)
            rw [hx₇_tb, hx₇_ta]; omega
          have hval_tc : InEpochValid V (targetCap U n) st.dict (.delete u) := by
            refine ⟨hval, show EpochValid U n' (targetCap U n) from
              Or.inr ⟨by omega, ?_, ?_, ?_⟩⟩
            · unfold targetCap; rw [ite_eq_right hn0]
              exact hn'_le_n.trans (le_min (by omega) hnU)
            · unfold targetCap; rw [ite_eq_right hn0]
              exact (min_le_left _ _).trans (by omega)
            · unfold targetCap; rw [ite_eq_right hn0]; exact min_le_right _ _
          have hpeak_eq : stepExactPeakWords V w st.cap st.dict (.delete u) =
              max (migratePeakWords U V w st.cap n)
                (inEpochPeakWords V w (targetCap U n) n st.dict (.delete u)) := by
            dsimp only [stepExactPeakWords]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_right hn1, ite_eq_left hmig]
          have hst'_cap : st'.cap = targetCap U n := by
            dsimp only [st', EpochState.step, nextEpochCap]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_right hn1, ite_eq_left hmig]
          have hst'_init : st'.initCount = n := by
            dsimp only [st', EpochState.step, nextEpochInit]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_right hn1, ite_eq_left hmig]
          have hdist_rel : n ≤ 2 * Nat.dist n st.initCount :=
            delete_mig_le_two_dist hn2 hanc hmig
          have hdist_post : Nat.dist n' n ≤ 1 := by rw [Nat.dist_comm]; exact hdist_del
          obtain ⟨μ_out, T_mig_op, hex_mig_op, hout_all, hmap_u, hcost_mig_op⟩ :=
            exec_migrate_then_inEpoch (overhead := 22) (.delete u) hx₇b hn_pos hanc hval_tc
              hfr hsplit hx₇_base hx₇_arg (fun _ _ => rfl) hdist_rel hdist_post hpeak_eq
              hfit_peak hst'_cap hst'_init (by decide)
          have hex_ge2 : ExecRCodeDist w resizableDeleteGeTwoCode x₂
              (μ_out.map StepROutcome.data) (9 + T_mig_op) L_peak :=
            ((ExecRCodeDist.of_demonicExec hex_ldN).seq_pure <|
              (ExecRCodeDist.of_demonicExec hex_s1).seq_pure <|
              (ExecRCodeDist.of_demonicExec hex_s2).seq_pure <|
              (ExecRCodeDist.of_demonicExec hex_c2).seq_pure <|
              (ExecRCodeDist.of_demonicExec hex_shr).seq_pure <|
              ExecRCodeDist.branch_neg hnc_lt hex_mig_op).mono (le_of_eq (by push_cast; ring))
          have hex_all : ExecRCodeDist w resizableOpCode x
              (μ_out.map StepROutcome.data) (22 + T_mig_op) L_peak :=
            ((ExecRCodeDist.of_demonicExec hex_ldn).seq_pure <|
              (ExecRCodeDist.of_demonicExec hex_z0).seq_pure <|
              (ExecRCodeDist.of_demonicExec hex_o1).seq_pure <|
              ExecRCodeDist.branch_neg hnc_n0 <|
              ExecRCodeDist.branch_neg hnc_t0 <|
              ExecRCodeDist.branch_neg hnc_t1 <|
              ExecRCodeDist.branch_neg hnc_n1 hex_ge2).mono (le_of_eq (by push_cast; ring))
          have hcap_ne : st'.cap ≠ st.cap := by
            rw [hst'_cap]; unfold targetCap; rw [ite_eq_right hn0]
            have : min (2 * n) U ≤ 2 * n := min_le_left _ _
            omega
          refine ⟨μ_out, _, hex_all, hout_all,
            fun _ => by rw [ite_eq_right hcap_ne]; exact hmap_u, ?_⟩
          calc ((22 : ℝ≥0∞) + T_mig_op) +
                (∑' q, μ_out q *
                  (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞))
              ≤ (resizablePotential U w st.cap n st.initCount base x : ℝ≥0∞) +
                (resizableBaseCharge : ℝ≥0∞) := hcost_mig_op
            _ ≤ _ := add_le_add le_rfl le_self_add
        · -- `4 * (n - 1) ≥ st.cap`: active in-epoch delete, no migration
          have hc_lt : (Cond.lt mTmpB mTmpA).Holds x₇.toData := by
            change x₇.regs mTmpB < x₇.regs mTmpA
            rw [hx₇_tb, hx₇_ta]; omega
          have hval_in : InEpochValid V st.cap st.dict (.delete u) :=
            ⟨hval, show EpochValid U n' st.cap from
              Or.inr ⟨by omega, hn'_le_n.trans hn_le_cap, by omega, hcap_le_U⟩⟩
          have hpeak_eq : stepExactPeakWords V w st.cap st.dict (.delete u) =
              inEpochPeakWords V w st.cap n st.dict (.delete u) := by
            dsimp only [stepExactPeakWords]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_right hn1, ite_eq_right hmig]
          have hcap_same : st'.cap = st.cap := by
            dsimp only [st', EpochState.step, nextEpochCap]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_right hn1, ite_eq_right hmig]
          have hinit_same : st'.initCount = st.initCount := by
            dsimp only [st', EpochState.step, nextEpochInit]
            change (if n = 0 then _ else _) = _
            rw [ite_eq_right hn0, ite_eq_right hn1, ite_eq_right hmig]
          obtain ⟨q_out, stepsOp, hex_op, hqls, hqrep, hqres, hqdec, hqbel, hqcost⟩ :=
            exec_inEpoch_branch (overhead := 21) (.delete u) hx₇b hn_pos hanc.1 hval_in
              hfr hsplit hx₇_base hx₇_arg (fun _ _ => rfl) rfl hdist_del hpeak_eq hfit_peak
              hcap_same hinit_same hrep.cap_eq (by decide)
          have hex_ge2 : RDemonicExec w L_peak resizableDeleteGeTwoCode x₂ (8 + stepsOp)
              (· = q_out.data) :=
            (hex_ldN.seq_eq <| hex_s1.seq_eq <| hex_s2.seq_eq <| hex_c2.seq_eq <|
              hex_shr.seq_eq <| RDemonicExec.branch_pos hc_lt hex_op).mono
              (by omega) (fun _ h => h)
          have hex_all : RDemonicExec w L_peak resizableOpCode x (21 + stepsOp)
              (· = q_out.data) :=
            (hex_ldn.seq_eq <| hex_z0.seq_eq <| hex_o1.seq_eq <|
              RDemonicExec.branch_neg hnc_n0
                (RDemonicExec.branch_neg hnc_t0
                  (RDemonicExec.branch_neg hnc_t1
                    (RDemonicExec.branch_neg hnc_n1 hex_ge2)))).mono
              (by omega) (fun _ h => h)
          exact package_active_inEpoch_step hn_pos hcap_same hex_all hqls hqrep hqres hqdec hqbel
            hqcost

/-! ## Section 5: Multi-Step Trajectory-Relative Expected Amortized Execution -/

/-- Exact resting word footprint above `base` after executing `prefOps` from `EpochState.empty U`.
-/
@[expose]
def epochSpaceBound (U V w : ℕ) (prefOps : List (Dynamic.Op U)) : ℕ :=
  let st := EpochState.run V (EpochState.empty U) prefOps
  compactedEpochWords U V w st.cap (Dictionary.dom st.dict).card

/-- Exact stepwise peak word footprint above `base` on `o` after executing `prefOps` from
`EpochState.empty U`. -/
@[expose]
def epochPeakSpaceBound (U V w : ℕ) (prefOps : List (Dynamic.Op U)) (o : Dynamic.Op U) : ℕ :=
  let st := EpochState.run V (EpochState.empty U) prefOps
  stepExactPeakWords V w st.cap st.dict o

@[simp]
theorem epochSpaceBound_nil (U V w : ℕ) :
    epochSpaceBound U V w [] = 8 := by
  simp [epochSpaceBound, EpochState.run, EpochState.empty, compactedEpochWords, rootHdrWords]

/-- `ObliviousPeakFits` with `epochPeakSpaceBound` is equivalent to `ReachedEpochsFit`. -/
theorem obliviousPeakFits_iff_reachedEpochsFit {U V w base : ℕ}
    (prefOps remOps : List (Dynamic.Op U)) :
    ObliviousPeakFits w base (epochPeakSpaceBound U V w) prefOps remOps ↔
      ReachedEpochsFit V w base (EpochState.run V (EpochState.empty U) prefOps) remOps := by
  induction remOps generalizing prefOps with
  | nil => simp
  | cons o os ih =>
    rw [obliviousPeakFits_cons, reachedEpochsFit_cons, ih (prefOps ++ [o]),
      EpochState.run_append, EpochState.run_cons, EpochState.run_nil]
    rfl

theorem epochAnchorInv_run {U V : ℕ} (hU_pos : 0 < U) {st : EpochState U}
    {ops : List (Dynamic.Op U)}
    (hanc : EpochAnchorInv U (Dictionary.dom st.dict).card st.cap st.initCount)
    (hvh : (Dynamic.spec U V U).ValidHistory st.dict ops) :
    let st' := EpochState.run V st ops
    EpochAnchorInv U (Dictionary.dom st'.dict).card st'.cap st'.initCount := by
  induction ops generalizing st with
  | nil => exact hanc
  | cons o os ih =>
    exact ih (epochAnchorInv_step hU_pos hanc hvh.1) hvh.2

/-- Distributional sequence invariant on `ν : PMF (SeqROutcome (LatentSeed U) Dynamic.Op.Result
rResize)` after executing a prefix reaching `st : EpochState U` with canonical output trace
`out_pref` and initial caller memory `mem₀`:
1. Every `t ∈ ν.support` satisfies `EpochRep U V w base st t.latent t.data`, `t.transcript =
   out_pref`, and `∀ addr < base, t.data.mem addr = mem₀ addr`;
2. Whenever `0 < (Dictionary.dom st.dict).card`, the marginal of `t.latent.seedAt st.cap` under `ν`
   is uniform (`PMF.uniformOfFintype (QuotHashSeed U st.cap)`). -/
@[expose]
def EpochSeqInv {U : ℕ} (V w base : ℕ) (st : EpochState U)
    (out_pref : List (Sigma (Dynamic.Op.Result (U := U)))) (mem₀ : ℕ → ℕ)
    (ν : PMF (SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize)) : Prop :=
  (∀ t ∈ ν.support,
    EpochRep U V w base st t.latent t.data ∧
    t.transcript = out_pref ∧
    (∀ addr < base, t.data.mem addr = mem₀ addr)) ∧
  (0 < (Dictionary.dom st.dict).card →
    ν.map (fun t => t.latent.seedAt st.cap) = PMF.uniformOfFintype (QuotHashSeed U st.cap))

/-- **Single-Step Expected Amortized Bound (`resizableOpCode_step_expected_amortized`):**
From any sequence distribution `ν` satisfying `EpochSeqInv V w base st out_pref mem₀ ν`, executing
one admissible operation `o` via `P.code = resizableOpCode` preserves `EpochSeqInv` at
`st' = st.step V o` and pays expected instruction cost plus expected potential change at most
`resizableCharge = O(1)`. -/
theorem resizableOpCode_step_expected_amortized {U V w base k_init : ℕ}
    (P : Cslib.DataStructure.WordRAM.Resizable.SubroutineCode .exact rResize k_init)
    (hP_base : P.baseReg = mBase) (hP_in : P.input = resizableInput)
    (hP_code : P.code = resizableOpCode)
    {st : EpochState U} {out_pref : List (Sigma (Dynamic.Op.Result (U := U)))}
    {mem₀ : ℕ → ℕ}
    {ν : PMF (SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize)}
    (o : Dynamic.Op U)
    (hw2 : Fits w 2) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hanc : EpochAnchorInv U (Dictionary.dom st.dict).card st.cap st.initCount)
    (hval : (Dynamic.spec U V U).valid st.dict o)
    (hfit_peak : Fits w (base + stepExactPeakWords V w st.cap st.dict o))
    (hinv : EpochSeqInv V w base st out_pref mem₀ ν) :
    let n := (Dictionary.dom st.dict).card
    let st' := st.step V o
    let n' := (Dictionary.dom st'.dict).card
    let a := ((Dynamic.spec U V U).stepFn st.dict o).2
    ∃ (μ_step : SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize →
        PMF (StepROutcome (LatentSeed U) o.Result rResize))
      (T_step : SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize → ℝ≥0∞),
      (∀ t ∈ ν.support,
        t.data.Bounded w ∧
        (∀ i, P.input i = true → Fits w (resizableEncode o i)) ∧
        (P.prepare resizableEncode o t.data).Bounded w ∧
        ExecRCodeDist w P.code (P.prepare resizableEncode o t.data)
          ((μ_step t).map StepROutcome.data) (T_step t)
          (base + stepExactPeakWords V w st.cap st.dict o) ∧
        ∀ q ∈ (μ_step t).support,
          q.data.Bounded w ∧
          (base ≤ q.data.frontier ∧
            q.data.frontier = base + compactedEpochWords U V w st'.cap n' ∧
            q.data.regs P.baseReg = base) ∧
          resizableDecode o q.data.regs = some q.result ∧
          (∀ addr < base, q.data.mem addr = t.data.mem addr)) ∧
      EpochSeqInv V w base st' (out_pref ++ [⟨o, a⟩]) mem₀
        (ν.bind fun t => (μ_step t).map (t.appendStep o)) ∧
      (∑' t, ν t * T_step t) +
          (∑' q_seq, (ν.bind fun t => (μ_step t).map (t.appendStep o)) q_seq *
            (resizablePotential U w st'.cap n' st'.initCount base q_seq.data : ℝ≥0∞)) ≤
        (∑' t, ν t * (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞)) +
          (resizableCharge : ℝ≥0∞) := by
  classical
  intro n st' n' a
  have hfit_in : ∀ i, P.input i = true → Fits w (resizableEncode o i) := by
    rw [hP_in]; exact fits_resizableEncode hw2 hU hV hval
  have hpt_all : ∀ t : SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize,
      t ∈ ν.support →
      ∃ (μ_out : PMF (StepROutcome (LatentSeed U) o.Result rResize)) (T_out : ℝ≥0∞),
        ExecRCodeDist w resizableOpCode (P.prepare resizableEncode o t.data)
          (μ_out.map StepROutcome.data) T_out (base + stepExactPeakWords V w st.cap st.dict o) ∧
        (∀ q ∈ μ_out.support,
          EpochRep U V w base st' q.latent q.data ∧
          q.result = a ∧
          resizableDecode o q.data.regs = some q.result ∧
          (∀ addr < base, q.data.mem addr = t.data.mem addr)) ∧
        (0 < n' →
          if st'.cap = st.cap then
            0 < n ∧ μ_out.map (fun q => q.latent.seedAt st.cap) = PMF.pure (t.latent.seedAt st.cap)
          else
            μ_out.map (fun q => q.latent.seedAt st'.cap) =
              PMF.uniformOfFintype (QuotHashSeed U st'.cap)) ∧
        T_out + (∑' q, μ_out q *
            (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)) ≤
          (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞) +
            ((resizableBaseCharge : ℝ≥0∞) +
              if 0 < n then
                (12 * inEpochFactor : ℝ≥0∞) *
                  (probeExcess st.cap (qStage1 U st.cap (t.latent.seedAt st.cap).1)
                    (polyStage2 U st.cap) (t.latent.seedAt st.cap).2
                    (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞)
              else 0) := by
    intro t ht
    obtain ⟨hrep_t, _, _⟩ := hinv.1 t ht
    have hbdd_t : t.data.Bounded w := hrep_t.compacted_rep.bounded
    have hbdd_prep : (P.prepare resizableEncode o t.data).Bounded w :=
      P.prepare_bounded hbdd_t hfit_in
    have hprep_eq : P.prepare resizableEncode o t.data =
        ⟨fun i => if resizableInput i then resizableEncode o i else t.data.regs i,
          t.data.mem, t.data.frontier⟩ := by
      unfold Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.prepare
        Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.prepareRegs
      rw [hP_in]
    have hrep_prep : EpochRep U V w base st t.latent (P.prepare resizableEncode o t.data) := by
      rw [hprep_eq]; exact hrep_t.prepare (hprep_eq ▸ hbdd_prep)
    have harg_prep : resizableArgMatch o (P.prepare resizableEncode o t.data).regs := by
      rw [hprep_eq]; exact resizableArgMatch_prepare o t.data.regs
    exact resizableOpCode_step_pointwise o hanc hrep_prep hval harg_prep hfit_peak
  let dfltOut : PMF (StepROutcome (LatentSeed U) o.Result rResize) :=
    PMF.pure ⟨LatentSeed.empty U,
      { regs := fun _ => 0, mem := fun _ => 0, frontier := 0 }, a⟩
  let μ_step (t : SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize) :
      PMF (StepROutcome (LatentSeed U) o.Result rResize) :=
    if ht : t ∈ ν.support then (hpt_all t ht).choose else dfltOut
  let T_step (t : SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize) : ℝ≥0∞ :=
    if ht : t ∈ ν.support then (hpt_all t ht).choose_spec.choose else 0
  have hstep_spec (t : SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize)
      (ht : t ∈ ν.support) :
      ExecRCodeDist w resizableOpCode (P.prepare resizableEncode o t.data)
        ((μ_step t).map StepROutcome.data) (T_step t)
        (base + stepExactPeakWords V w st.cap st.dict o) ∧
      (∀ q ∈ (μ_step t).support,
        EpochRep U V w base st' q.latent q.data ∧
        q.result = a ∧
        resizableDecode o q.data.regs = some q.result ∧
        (∀ addr < base, q.data.mem addr = t.data.mem addr)) ∧
      (0 < n' →
        if st'.cap = st.cap then
          0 < n ∧
            (μ_step t).map (fun q => q.latent.seedAt st.cap) = PMF.pure (t.latent.seedAt st.cap)
        else
          (μ_step t).map (fun q => q.latent.seedAt st'.cap) =
            PMF.uniformOfFintype (QuotHashSeed U st'.cap)) ∧
      T_step t + (∑' q, (μ_step t) q *
          (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)) ≤
        (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞) +
          ((resizableBaseCharge : ℝ≥0∞) +
            if 0 < n then
              (12 * inEpochFactor : ℝ≥0∞) *
                (probeExcess st.cap (qStage1 U st.cap (t.latent.seedAt st.cap).1)
                  (polyStage2 U st.cap) (t.latent.seedAt st.cap).2
                  (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞)
            else 0) := by
    simpa only [μ_step, T_step, dite_eq_left ht] using (hpt_all t ht).choose_spec.choose_spec
  refine ⟨μ_step, T_step, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨hrep_t, _, _⟩ := hinv.1 t ht
    have hbdd_t : t.data.Bounded w := hrep_t.compacted_rep.bounded
    obtain ⟨hex, hout_all, _, _⟩ := hstep_spec t ht
    refine ⟨hbdd_t, hfit_in, P.prepare_bounded hbdd_t hfit_in, hP_code.symm ▸ hex,
      fun q hq => ?_⟩
    obtain ⟨hrep_q, _, hdec_q, hbel_q⟩ := hout_all q hq
    have hfr_q : q.data.frontier = base + compactedEpochWords U V w st'.cap n' :=
      hrep_q.compacted_rep.frontier_eq
    have hreg_q : q.data.regs P.baseReg = base := by
      rw [hP_base]; exact hrep_q.base_reg_eq
    exact ⟨hrep_q.compacted_rep.bounded,
      ⟨by rw [hfr_q]; exact Nat.le_add_right _ _, hfr_q, hreg_q⟩,
      hdec_q, hbel_q⟩
  · intro q_seq hq_seq
    rw [PMF.mem_support_bind_iff] at hq_seq; obtain ⟨t, ht, hq_map⟩ := hq_seq
    rw [PMF.mem_support_map_iff] at hq_map; obtain ⟨q, hq, rfl⟩ := hq_map
    obtain ⟨_, htr_t, hbel_t⟩ := hinv.1 t ht
    obtain ⟨_, hout_all, _, _⟩ := hstep_spec t ht
    obtain ⟨hrep_q, hres_q, _, hbel_q⟩ := hout_all q hq
    exact ⟨hrep_q, by simp [SeqROutcome.appendStep, htr_t, hres_q],
      fun addr hlt => (hbel_q addr hlt).trans (hbel_t addr hlt)⟩
  · intro hn'_pos
    rw [PMF.map_bind]
    have hcomp : ∀ t, ((μ_step t).map (t.appendStep o)).map (fun q_seq => q_seq.latent.seedAt
        st'.cap) = (μ_step t).map (fun q => q.latent.seedAt st'.cap) :=
      fun t => by rw [PMF.map_comp]; rfl
    simp_rw [hcomp]
    by_cases hcap : st'.cap = st.cap
    · obtain ⟨t₀, ht₀⟩ := ν.support_nonempty
      have hs₀ := (hstep_spec t₀ ht₀).2.2.1 hn'_pos
      rw [ite_eq_left hcap] at hs₀
      have hn_pos : 0 < n := hs₀.1
      have hbind_eq : (ν.bind fun t => (μ_step t).map (fun q => q.latent.seedAt st.cap)) =
          ν.bind (fun t => PMF.pure (t.latent.seedAt st.cap)) := by
        refine Cslib.Probability.PMF.bind_congr_on_support ν _ _ fun t ht => ?_
        have hst := (hstep_spec t ht).2.2.1 hn'_pos
        rw [ite_eq_left hcap] at hst
        exact hst.2
      have h_at_st : (ν.bind fun t => (μ_step t).map (fun q => q.latent.seedAt st.cap)) =
          PMF.uniformOfFintype (QuotHashSeed U st.cap) := by
        rw [hbind_eq]; exact hinv.2 hn_pos
      have htr : ∀ (C : ℕ), C = st.cap →
          (ν.bind fun t => (μ_step t).map (fun q => q.latent.seedAt C)) =
            PMF.uniformOfFintype (QuotHashSeed U C) := by
        rintro _ rfl; exact h_at_st
      exact htr st'.cap hcap
    · have hbind_eq : (ν.bind fun t => (μ_step t).map (fun q => q.latent.seedAt st'.cap)) =
          ν.bind (fun _ => PMF.uniformOfFintype (QuotHashSeed U st'.cap)) := by
        refine Cslib.Probability.PMF.bind_congr_on_support ν _ _ fun t ht => ?_
        have hst := (hstep_spec t ht).2.2.1 hn'_pos
        rw [ite_eq_right hcap] at hst
        exact hst
      rw [hbind_eq, PMF.bind_const]
  · rw [Cslib.Probability.PMF.tsum_bind_mul]
    have hmap_pot : ∀ t, (∑' q_seq, ((μ_step t).map (t.appendStep o)) q_seq *
        (resizablePotential U w st'.cap n' st'.initCount base q_seq.data : ℝ≥0∞)) =
        ∑' q, (μ_step t) q *
          (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞) :=
      fun t => Cslib.Probability.PMF.tsum_map_mul (μ_step t) (t.appendStep o) _
    simp_rw [hmap_pot]
    rw [← CompleteLattice.summable.tsum_add CompleteLattice.summable]
    have hcomb_lhs : (∑' t, (ν t * T_step t + ν t * ∑' q, (μ_step t) q *
        (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞))) =
        ∑' t, ν t * (T_step t + ∑' q, (μ_step t) q *
          (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)) :=
      tsum_congr fun _ => (mul_add _ _ _).symm
    rw [hcomb_lhs]
    by_cases hn_pos : 0 < n
    · have hpt_le : ∀ t,
          ν t * (T_step t + ∑' q, (μ_step t) q *
              (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)) ≤
            ν t * (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞) +
              (ν t * (resizableBaseCharge : ℝ≥0∞) +
                (12 * inEpochFactor : ℝ≥0∞) *
                  (ν t * (probeExcess st.cap (qStage1 U st.cap (t.latent.seedAt st.cap).1)
                    (polyStage2 U st.cap) (t.latent.seedAt st.cap).2
                    (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞))) := by
        intro t
        by_cases ht : t ∈ ν.support
        · have hc := (hstep_spec t ht).2.2.2
          rw [ite_eq_left hn_pos] at hc
          calc ν t * (T_step t + ∑' q, (μ_step t) q *
                  (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞))
              ≤ ν t * ((resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞) +
                  ((resizableBaseCharge : ℝ≥0∞) +
                    (12 * inEpochFactor : ℝ≥0∞) *
                      (probeExcess st.cap (qStage1 U st.cap (t.latent.seedAt st.cap).1)
                        (polyStage2 U st.cap) (t.latent.seedAt st.cap).2
                        (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞))) :=
                mul_le_mul_right hc (ν t)
            _ = _ := by ring
        · simp [(PMF.apply_eq_zero_iff ν t).mpr ht]
      have hcap_U : st.cap ≤ U := by rcases hanc.1 with ⟨h0, _⟩ | ⟨_, _, _, hU'⟩ <;> omega
      have hn_le_cap : n ≤ st.cap := by rcases hanc.1 with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega
      have hS_le : ((Dictionary.dom st.dict).erase (opKey o)).card ≤ st.cap :=
        (Finset.card_erase_le (s := Dictionary.dom st.dict) (a := opKey o)).trans hn_le_cap
      let prFn (θ₀ : QuotHashSeed U st.cap) : ℝ≥0∞ :=
        (probeExcess st.cap (qStage1 U st.cap θ₀.1) (polyStage2 U st.cap) θ₀.2
          (Dictionary.dom st.dict) (opKey o) : ℝ≥0∞)
      have hpr_sum :
          (∑' t, ν t * prFn (t.latent.seedAt st.cap)) ≤ 5 := by
        rw [← Cslib.Probability.PMF.tsum_map_mul ν (fun t => t.latent.seedAt st.cap) prFn,
          hinv.2 hn_pos]
        exact tsum_uniform_probeExcess_reducedPolyHash_le_five hcap_U
          (Dictionary.dom st.dict) (opKey o) hS_le
      calc (∑' t, ν t * (T_step t + ∑' q, (μ_step t) q *
              (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)))
          ≤ ∑' t, (ν t * (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞) +
              (ν t * (resizableBaseCharge : ℝ≥0∞) +
                (12 * inEpochFactor : ℝ≥0∞) *
                  (ν t * prFn (t.latent.seedAt st.cap)))) := tsum_le_tsum hpt_le
        _ = (∑' t, ν t * (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞)) +
              ((∑' t, ν t * (resizableBaseCharge : ℝ≥0∞)) +
                (12 * inEpochFactor : ℝ≥0∞) *
                  ∑' t, ν t * prFn (t.latent.seedAt st.cap)) := by
            rw [CompleteLattice.summable.tsum_add CompleteLattice.summable,
              CompleteLattice.summable.tsum_add CompleteLattice.summable, ENNReal.tsum_mul_left]
        _ ≤ (∑' t, ν t * (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞)) +
              ((resizableBaseCharge : ℝ≥0∞) + (12 * inEpochFactor : ℝ≥0∞) * 5) := by
            rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]; gcongr
        _ = (∑' t, ν t * (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞)) +
              (resizableCharge : ℝ≥0∞) := by
            unfold resizableCharge; push_cast; ring
    · have hpt_le : ∀ t,
          ν t * (T_step t + ∑' q, (μ_step t) q *
              (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)) ≤
            ν t * (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞) +
              ν t * (resizableCharge : ℝ≥0∞) := by
        intro t
        by_cases ht : t ∈ ν.support
        · have hc := (hstep_spec t ht).2.2.2
          rw [ite_eq_right hn_pos, add_zero] at hc
          have hb_le : (resizableBaseCharge : ℝ≥0∞) ≤ (resizableCharge : ℝ≥0∞) :=
            (Nat.cast_le (α := ℝ≥0∞)).mpr (by unfold resizableCharge; omega)
          calc ν t * (T_step t + ∑' q, (μ_step t) q *
                  (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞))
              ≤ ν t * ((resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞) +
                  (resizableCharge : ℝ≥0∞)) :=
                mul_le_mul_right (hc.trans (add_le_add le_rfl hb_le)) (ν t)
            _ = _ := mul_add _ _ _
        · simp [(PMF.apply_eq_zero_iff ν t).mpr ht]
      calc (∑' t, ν t * (T_step t + ∑' q, (μ_step t) q *
              (resizablePotential U w st'.cap n' st'.initCount base q.data : ℝ≥0∞)))
          ≤ ∑' t, (ν t * (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞) +
              ν t * (resizableCharge : ℝ≥0∞)) := tsum_le_tsum hpt_le
        _ = (∑' t, ν t * (resizablePotential U w st.cap n st.initCount base t.data : ℝ≥0∞)) +
              (resizableCharge : ℝ≥0∞) := by
            rw [CompleteLattice.summable.tsum_add CompleteLattice.summable,
              ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]

/-- **Multi-Step Trajectory-Relative Expected Amortized Execution
(`resizableOpCode_steps_expected_amortized`):**
Across any admissible operation sequence `remOps` from prefix `prefOps` whose trajectory peaks fit
in `w`-bit words (`ReachedEpochsFit V w base st remOps`), `resizableOpCode` executes under
`Resizable.Randomized.ExecSteps`, produces the exact canonical dictionary transcript, preserves
`EpochSeqInv`, and executes in at most `E[Φ_init] + remOps.length * resizableCharge` expected
instructions. -/
theorem resizableOpCode_steps_expected_amortized {U V w base k_init : ℕ}
    (P : Cslib.DataStructure.WordRAM.Resizable.SubroutineCode .exact rResize k_init)
    (hP_base : P.baseReg = mBase) (hP_in : P.input = resizableInput)
    (hP_code : P.code = resizableOpCode)
    (prefOps remOps : List (Dynamic.Op U))
    {out_pref : List (Sigma (Dynamic.Op.Result (U := U)))} {mem₀ : ℕ → ℕ}
    (ν : PMF (SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize))
    (hw2 : Fits w 2) (hU_pos : 0 < U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hvh : (Dynamic.spec U V U).ValidHistory
      (EpochState.run V (EpochState.empty U) prefOps).dict remOps)
    (hfit : ReachedEpochsFit V w base (EpochState.run V (EpochState.empty U) prefOps) remOps)
    (hanc : EpochAnchorInv U
      (Dictionary.dom (EpochState.run V (EpochState.empty U) prefOps).dict).card
      (EpochState.run V (EpochState.empty U) prefOps).cap
      (EpochState.run V (EpochState.empty U) prefOps).initCount)
    (hinv : EpochSeqInv V w base (EpochState.run V (EpochState.empty U) prefOps)
      out_pref mem₀ ν) :
    let st := EpochState.run V (EpochState.empty U) prefOps
    let st_fin := EpochState.run V st remOps
    ∃ (ν_final : PMF (SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize))
      (T_ops : ℝ≥0∞),
      ExecSteps P ((Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U))
        (LatentSeed U) w base (epochSpaceBound U V w) (epochPeakSpaceBound U V w)
        resizableEncode resizableDecode prefOps remOps ν ν_final T_ops ∧
      EpochSeqInv V w base st_fin (out_pref ++ ((Dynamic.spec U V U).run st.dict remOps).2)
        mem₀ ν_final ∧
      T_ops + (∑' q_seq, ν_final q_seq *
          (resizablePotential U w st_fin.cap (Dictionary.dom st_fin.dict).card st_fin.initCount
            base q_seq.data : ℝ≥0∞)) ≤
        (∑' t, ν t * (resizablePotential U w st.cap (Dictionary.dom st.dict).card st.initCount
            base t.data : ℝ≥0∞)) + ((remOps.length * resizableCharge : ℕ) : ℝ≥0∞) := by
  induction remOps generalizing prefOps out_pref ν with
  | nil =>
    refine ⟨ν, 0, ?_, ?_, ?_⟩
    · exact ExecSteps.nil
        (P := P) (S := (Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U))
        prefOps ν
    · simpa only [EpochState.run_nil, StateTransitionSpec.run_nil, List.append_nil] using hinv
    · simp only [EpochState.run_nil, zero_add, List.length_nil, Nat.zero_mul, Nat.cast_zero,
        add_zero, le_rfl]
  | cons o os ih =>
    set st := EpochState.run V (EpochState.empty U) prefOps
    obtain ⟨hv_o, hvh_os⟩ := hvh
    obtain ⟨hfit_o, hfit_os⟩ := hfit
    obtain ⟨μ_step, T_step, hstep_exec, hinv_next, hcost_step⟩ :=
      resizableOpCode_step_expected_amortized P hP_base hP_in hP_code o hw2 hU hV hanc hv_o
        hfit_o hinv
    have hrun_next : EpochState.run V (EpochState.empty U) (prefOps ++ [o]) = st.step V o := by
      rw [EpochState.run_append, EpochState.run_cons, EpochState.run_nil]
    have hanc_next : EpochAnchorInv U
        (Dictionary.dom (EpochState.run V (EpochState.empty U) (prefOps ++ [o])).dict).card
        (EpochState.run V (EpochState.empty U) (prefOps ++ [o])).cap
        (EpochState.run V (EpochState.empty U) (prefOps ++ [o])).initCount := by
      rw [hrun_next]; exact epochAnchorInv_step hU_pos hanc hv_o
    obtain ⟨ν_final, T_rest, hex_rest, hinv_fin, hcost_rest⟩ :=
      ih (prefOps ++ [o]) (ν.bind fun t => (μ_step t).map (t.appendStep o))
        (by rw [hrun_next]; exact hvh_os)
        (by rw [hrun_next]; exact hfit_os)
        hanc_next
        (by rw [hrun_next]; exact hinv_next)
    refine ⟨ν_final, (∑' t, ν t * T_step t) + T_rest, ?_, ?_, ?_⟩
    · refine .cons (fun t ht => ?_) hex_rest
      obtain ⟨hbdd_t, hfit_in, hbdd_prep, hex_t, hq_all⟩ := hstep_exec t ht
      refine ⟨hbdd_t, hfit_in, hbdd_prep, hex_t, fun q hq => ?_⟩
      obtain ⟨hbdd_q, ⟨hlo_q, hfr_q, hreg_q⟩, hdec_q, hbel_q⟩ := hq_all q hq
      have hsp_eq : epochSpaceBound U V w (prefOps ++ [o]) =
          compactedEpochWords U V w (st.step V o).cap
            (Dictionary.dom (st.step V o).dict).card := by
        unfold epochSpaceBound; rw [hrun_next]
      exact ⟨hbdd_q, ⟨hlo_q, by rw [hfr_q, hsp_eq], hreg_q⟩, hdec_q, hbel_q⟩
    · rw [hrun_next, List.append_assoc, List.singleton_append] at hinv_fin
      exact hinv_fin
    · rw [hrun_next] at hcost_rest
      set E_mid := ∑' q_seq, (ν.bind fun t => (μ_step t).map (t.appendStep o)) q_seq *
        (resizablePotential U w (st.step V o).cap (Dictionary.dom (st.step V o).dict).card
          (st.step V o).initCount base q_seq.data : ℝ≥0∞)
      set st_fin := EpochState.run V (st.step V o) os
      set E_fin := ∑' q_seq, ν_final q_seq *
        (resizablePotential U w st_fin.cap (Dictionary.dom st_fin.dict).card st_fin.initCount
          base q_seq.data : ℝ≥0∞)
      set E_init := ∑' t, ν t *
        (resizablePotential U w st.cap (Dictionary.dom st.dict).card st.initCount base t.data :
          ℝ≥0∞)
      calc ((∑' t, ν t * T_step t) + T_rest) + E_fin
          = (∑' t, ν t * T_step t) + (T_rest + E_fin) := by ac_rfl
        _ ≤ (∑' t, ν t * T_step t) + (E_mid + ((os.length * resizableCharge : ℕ) : ℝ≥0∞)) :=
            add_le_add le_rfl hcost_rest
        _ = ((∑' t, ν t * T_step t) + E_mid) + ((os.length * resizableCharge : ℕ) : ℝ≥0∞) := by
            ac_rfl
        _ ≤ (E_init + (resizableCharge : ℝ≥0∞)) + ((os.length * resizableCharge : ℕ) : ℝ≥0∞) :=
            add_le_add hcost_step le_rfl
        _ = E_init + (((o :: os).length * resizableCharge : ℕ) : ℝ≥0∞) := by
            rw [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.cast_add]; ac_rfl

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
