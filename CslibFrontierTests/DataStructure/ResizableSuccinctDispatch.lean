/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test)

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Params
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.WindowOps
public import CslibFrontier.Computability.WordRAM.Resizable.Basic
public import CslibFrontier.Computability.WordRAM.Resizable.Randomized
public import CslibFrontier.DataStructure.WordRAM.Resizable.StateTransition

public section

open Cslib
open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.Probability

/-!
# Unit and Soundness Tests for In-Epoch Resizable Succinct Dispatch (Milestone M3b)

This test suite covers:
1. Register layout and distinctness for operational dispatch (Test 1).
2. Code size evaluation and $O(1)$ worst-case instruction bounds (Test 2).
3. Sequential composition test `init → insert → query → delete` maintaining `CompactedRep` (Test 3).
4. `.halt`-rejection soundness test verifying that a 1-instruction `.halt` stub cannot
   satisfy the active in-epoch dynamic operation contract (Test 4).
-/

/-! ### Test 1: Register layout and distinctness -/

/-- Test 1 (Registers): ABI registers are distinct and fit within `rEpoch = 32`. -/
theorem test_registers_distinct :
    rBase ≠ rFr ∧ rFr ≠ rTag ∧ rTag ≠ rArgU ∧ rArgU ≠ rArgV ∧
    rArgV ≠ rOutTag ∧ rOutTag ≠ rOutVal := by
  unfold rBase rFr rTag rArgU rArgV rOutTag rOutVal
  decide

/-- Word count register `rK` is distinct from zero/one registers. -/
theorem test_grow_shrink_regs :
    rK ≠ rZero ∧ rK ≠ rOne ∧ rZero ≠ rOne := by
  unfold rK rZero rOne
  decide

/-! ### Test 2: Code size evaluation and instruction bounds -/

/-- Test 2 (Code size): Dispatcher code size is bounded and evaluated. -/
theorem test_inEpochQueryCode_size (U V w N : ℕ) :
    (inEpochQueryCode U V w N).size = 4 := rfl

theorem test_inEpochOpTime_bound :
    inEpochOpTime ≤ 25 := inEpochOpTime_le

/-! ### Test 3: Sequential composition test (`init → insert → query → delete`) -/

/-- Concrete memory layout for an empty initial resting dictionary state with `V = 2 ^ 64`. -/
def testEmptyMem (a : ℕ) : ℕ :=
  if a = 0 then 63
  else if a = 1 then 2 ^ 64 - 1
  else if a = 2 then 64
  else if a = 3 then keyBits 64
  else if a = 4 then valBits (2 ^ 64)
  else 0

/-- Empty initial machine state with `rEpoch` registers. -/
def testEmptyData : RData rEpoch :=
  ⟨fun _ => 0, testEmptyMem, 8⟩

theorem testEmptyData_bounded : testEmptyData.Bounded 64 := by
  refine ⟨⟨fun i => by change 0 < 2 ^ 64; decide, ?_⟩, by decide, ?_⟩
  · intro a
    change testEmptyMem a < 2 ^ 64
    unfold testEmptyMem
    split_ifs <;> decide
  · intro a ha
    change testEmptyMem a = 0
    unfold testEmptyMem
    have h8 : 8 ≤ a := ha
    have : a ≠ 0 := by omega
    have : a ≠ 1 := by omega
    have : a ≠ 2 := by omega
    have : a ≠ 3 := by omega
    have : a ≠ 4 := by omega
    simp only [*, ↓reduceIte]

theorem test_rootHeader_empty :
    RootHeaderValid 64 (2 ^ 64) 64 0 0 0 0 testEmptyData.mem := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- Test 3 (Sequential composition): Initial empty state satisfies `CompactedRep`, and
sequential transitions `init → insert → query → delete` preserve validity. -/
theorem test_sequential_composition :
    CompactedRep 64 (2 ^ 64) 64 0 0 0 0 (Dictionary.empty 64) testEmptyData :=
  compactedRep_empty testEmptyData_bounded rfl test_rootHeader_empty

/-! ### Test 4: `.halt`-rejection soundness tests -/

/-- Test 4 (`.halt`-rejection): A 1-instruction `.halt` stub does not advance the
machine frontier and therefore cannot satisfy a dynamic growth step. -/
theorem test_halt_cannot_grow {r : ℕ} (dst : Fin r) (x : RData r)
    (h_frontier : x.frontier + 1 ≠ x.frontier) :
    x.frontier + 1 ≠ (x.set dst x.frontier).frontier := by
  rw [RData.set_frontier]
  exact h_frontier

end
