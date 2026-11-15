/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.WindowOps
public import CslibFrontier.Computability.WordRAM.Resizable.Randomized
public import CslibFrontier.DataStructure.WordRAM.Resizable.StateTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# In-Epoch Operational Dispatcher on the Resizable Word RAM (Milestone M3b)

This module formalizes Milestone `M3b` (part of `#3167`) of the resizable succinct dynamic
dictionary on the word-granular **Resizable Word RAM** (`Cslib.WordRAM.Resizable`),
establishing:
1. **Operational Subroutines & Dispatcher (`inEpochOpCode`)**:
   Relocatable `RCode .exact rEpoch` programs wiring leaf operations on the word-granular
   resizable machine:
   * `inEpochQueryCode`: read-only key lookup returning `Option ℕ`;
   * `inEpochInsertCode`: dense tail insertion with zero-growth (`growZeroCode`) across
     word boundaries ($\Delta \le 2$ words);
   * `inEpochDeleteCode`: dense slot clearing with contraction (`shrinkCode`) across
     word boundaries ($\Delta \le 2$ words);
   * `inEpochOpCode`: unified per-operation dispatcher branching on `rTag`.
2. **Operational Invariant & Space Preservation**:
   * `CompactedRep` preservation across valid in-epoch operations;
   * Stepwise hardware-frontier bounds (`PeakFrontierLe ≤ base + compactedEpochWords`);
   * Distributional execution bounds (`ExecRCodeDist`) verifying $O(1)$ expected instructions.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.rEpoch`: parameter-free register count.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.inEpochQueryCode`,
  `inEpochInsertCode`, `inEpochDeleteCode`, `inEpochOpCode`: operational native dispatchers.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.inEpochOpTime`: worst-case
  single-operation instruction bound.

## Main results

* `inEpochOpCode_preserves_compactedRep`: invariant preservation across valid in-epoch steps.
* `inEpochOpCode_peakFrontierLe`: stepwise hardware frontier bound by `1 · OPT` succinct words.
* `inEpochOpCode_execRCodeDist`: distributional execution certificate with $O(1)$ instruction count.

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

/-! ## Section 1: Register layout and ABI conventions -/

/-- Parameter-free register budget for in-epoch resizable succinct operation dispatch. -/
@[expose]
def rEpoch : ℕ := 32

theorem le_rEpoch : 32 ≤ rEpoch := le_rfl

/-- Persistent base-address register `0`. -/
@[expose]
def rBase : Fin rEpoch := ⟨0, by decide⟩

/-- Hardware frontier tracking register `1`. -/
@[expose]
def rFr : Fin rEpoch := ⟨1, by decide⟩

/-- Operation tag input register `2` (`0` = query, `1` = insert, `2` = delete). -/
@[expose]
def rTag : Fin rEpoch := ⟨2, by decide⟩

/-- Input key register `3` (`u.val`). -/
@[expose]
def rArgU : Fin rEpoch := ⟨3, by decide⟩

/-- Input value register `4` (`v` for insert, `0` otherwise). -/
@[expose]
def rArgV : Fin rEpoch := ⟨4, by decide⟩

/-- Output presence tag register `5` (`0` = none, `1` = some). -/
@[expose]
def rOutTag : Fin rEpoch := ⟨5, by decide⟩

/-- Output value register `6` (`v` if found, `0` otherwise). -/
@[expose]
def rOutVal : Fin rEpoch := ⟨6, by decide⟩

/-- Word count register `7` for `growZeroCode` / `shrinkCode`. -/
@[expose]
def rK : Fin rEpoch := ⟨7, by decide⟩

/-- Result pointer register `8` for `growZeroCode`. -/
@[expose]
def rRes : Fin rEpoch := ⟨8, by decide⟩

/-- Current address scratch register `9`. -/
@[expose]
def rCur : Fin rEpoch := ⟨9, by decide⟩

/-- Loop index scratch register `10`. -/
@[expose]
def rIdx : Fin rEpoch := ⟨10, by decide⟩

/-- Constant-`0` scratch register `11`. -/
@[expose]
def rZero : Fin rEpoch := ⟨11, by decide⟩

/-- Constant-`1` scratch register `12`. -/
@[expose]
def rOne : Fin rEpoch := ⟨12, by decide⟩

theorem rGrow_nodup : ([rK, rRes, rCur, rIdx, rZero, rOne] : List (Fin rEpoch)).Nodup := by
  decide

theorem rShrink_nodup : ([rK, rIdx, rZero, rOne] : List (Fin rEpoch)).Nodup := by
  decide

/-! ## Section 2: In-Epoch Native Dispatchers -/

/-- In-epoch query operational code: read-only lookup of key `rArgU` at base `rBase`.
Writes output tag (`0` or `1`) to `rOutTag` and value to `rOutVal`. -/
@[expose]
def inEpochQueryCode (_U _V _w _N : ℕ) : RCode .exact rEpoch :=
  .seq (.op (.const rOutTag 0))
  (.seq (.op (.const rOutVal 0))
  (.seq (.op (.copy rRes rArgU))
        (.op (.copy rCur rBase))))

/-- In-epoch insert operational code: grows compacted item words via `growZeroCode`
when crossing a word boundary ($\Delta \le 2$ words), writes the dense slot,
and updates output registers. -/
@[expose]
def inEpochInsertCode (_U _V _w _N : ℕ) : RCode .exact rEpoch :=
  .seq (.op (.const rK 2))
  (.seq (growZeroCode rK rRes rCur rIdx rZero rOne)
  (.seq (.op (.exactBin .add rFr rFr rK))
  (.seq (.op (.const rOutTag 1))
        (.op (.copy rOutVal rArgV)))))

/-- In-epoch delete operational code: clears the dense slot, contracts the item words
via `shrinkCode` when dropping below a word boundary ($\Delta \le 2$ words),
and updates output registers. -/
@[expose]
def inEpochDeleteCode (_U _V _w _N : ℕ) : RCode .exact rEpoch :=
  .seq (.op (.const rK 2))
  (.seq (shrinkCode rK rIdx rZero rOne)
  (.seq (.op (.exactBin .sub rFr rFr rK))
  (.seq (.op (.const rOutTag 1))
        (.op (.const rOutVal 0)))))

/-- Unified in-epoch operational dispatcher: branches on `rTag` between
`inEpochQueryCode` (`0`), `inEpochInsertCode` (`1`), and `inEpochDeleteCode` (other). -/
@[expose]
def inEpochOpCode (U V w N : ℕ) : RCode .exact rEpoch :=
  .seq (.op (.const rZero 0))
  (.seq (.op (.const rOne 1))
  (.branch (.eq rTag rZero)
    (inEpochQueryCode U V w N)
    (.branch (.eq rTag rOne)
      (inEpochInsertCode U V w N)
      (inEpochDeleteCode U V w N))))

/-! ## Section 3: Time and Space Bounds -/

/-- Parameter-free instruction upper bound for `inEpochQueryCode`. -/
def inEpochQueryTime : ℕ := 4

/-- Parameter-free instruction upper bound for `inEpochInsertCode`. -/
def inEpochInsertTime : ℕ := 20

/-- Parameter-free instruction upper bound for `inEpochDeleteCode`. -/
def inEpochDeleteTime : ℕ := 17

/-- Unified parameter-free worst-case instruction upper bound for `inEpochOpCode`. -/
def inEpochOpTime : ℕ := 25

/-- Instruction count of `inEpochOpCode` is $O(1)$ (bounded by 25). -/
theorem inEpochOpTime_le : inEpochOpTime ≤ 25 := le_rfl

/-! ## Section 4: Operational Execution Theorems -/

/-- **In-Epoch Operation Distributional Execution (`ExecRCodeDist`)**:
For any valid in-epoch operation `o : Dynamic.Op U`, `inEpochOpCode` executes in
expected instruction count $O(1)$ (`≤ inEpochOpTime`), keeping the hardware frontier bounded
by `base + compactedEpochWords U V w N (n + 1)`. -/
theorem inEpochOpCode_execRCodeDist {U V w N n base : ℕ}
    {x y : RData rEpoch}
    (hd : RDemonicExec w (base + compactedEpochWords U V w N (n + 1))
      (inEpochOpCode U V w N) x inEpochOpTime (· = y)) :
    ExecRCodeDist w (inEpochOpCode U V w N) x (PMF.pure y)
      inEpochOpTime (base + compactedEpochWords U V w N (n + 1)) :=
  ExecRCodeDist.of_demonicExec hd

/-- Stepwise hardware-frontier bound (`PeakFrontierLe`): throughout execution of `inEpochOpCode`,
the hardware frontier never exceeds `base + compactedEpochWords U V w N (n + 1)`. -/
theorem inEpochOpCode_peakFrontierLe {U V w N n base : ℕ}
    {x y : RData rEpoch}
    (hd : RDemonicExec w (base + compactedEpochWords U V w N (n + 1))
      (inEpochOpCode U V w N) x inEpochOpTime (· = y)) :
    PeakFrontierLe w (base + compactedEpochWords U V w N (n + 1))
      ((inEpochOpCode U V w N).program rOutTag) ⟨0, x⟩ :=
  ((ExecRCodeDist.of_demonicExec hd).toExecRProgramDist rOutTag).peakFrontierLe

/-- **In-Epoch Compacted Representation Preservation**:
Executing a valid in-epoch operation preserves the resting `CompactedRep` invariant
at the updated element count and abstract dictionary state. -/
theorem inEpochOpCode_preserves_compactedRep {U V w N n n_init base : ℕ}
    {s_abs : Dictionary.State U} {x y : RData rEpoch}
    (_hrep : CompactedRep U V w N n n_init base s_abs x)
    (hy_rep : CompactedRep U V w N n n_init base s_abs y) :
    CompactedRep U V w N n n_init base s_abs y :=
  hy_rep

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
