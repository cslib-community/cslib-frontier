/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Params
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.While
public import CslibFrontier.Computability.WordRAM.Realization.Loop
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.Computability.WordRAM.Realization.LoopCongr
import CslibFrontier.Tactic.Realize
import CslibFrontier.DataStructure.Memory.Frame
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame

/-!
# Word-RAM `Memory.Prog` Operations and Certificates for Soft Heaps

Low-level memory layout (`+0..+2` stride-3 item slots and `+0..+11` stride-12 node slots),
`SHHandle`, `Memory.Prog` implementations of pool allocation, iterative `defill`,
lazy binomial-style
insertion (`shInsert`), minimum extraction (`shExtractMin`), and corrupted-item harvesting
(`shCollectCorrupted`), together with uniform `Realizes .exact` (`work := 0`) compilation
certificates.

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHHandle`: 6-word handle for bump-allocated
  item and node pools plus rank threshold (`WordEncoding.ofEquiv SHHandle.equiv`).
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHExtractResult`: named 9-word return record
  for `shExtractMin` (`WordEncoding.ofEquiv SHExtractResult.equiv`).
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.allocPool`, `defill`, `shInsert`,
  `shExtractMin`, `shCollectCorrupted`: memory-oracle operations and safety domains.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.realizes_allocPool`, `realizes_defill`,
  `realizes_shInsert`, `realizes_shExtractMin`, `realizes_shCollectCorrupted`: uniform
  `Realizes .exact` native code certificates.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory

/-- Soft-heap pool handle storing bump pool bases, root-list head, allocated counts, and
corruption rank threshold `rankThreshold`. -/
structure SHHandle where
  /-- Base address of the stride-3 item pool. -/
  itemBase : ℕ
  /-- Base address of the stride-12 node pool. -/
  nodeBase : ℕ
  /-- 1-based index of the minimum-rank root in the doubly-linked root list (`0` = empty). -/
  firstRoot : ℕ
  /-- Number of allocated item slots (`1..itemCount`). -/
  itemCount : ℕ
  /-- Number of allocated node slots (`1..nodeCount`). -/
  nodeCount : ℕ
  /-- Corruption rank threshold `r` (items at rank `≤ r` stay uncorrupted). -/
  rankThreshold : ℕ
  deriving DecidableEq

/-- Canonical 6-word tuple equivalence for `SHHandle`. -/
@[expose] def SHHandle.equiv : SHHandle ≃ ℕ × ℕ × ℕ × ℕ × ℕ × ℕ where
  toFun h := (h.itemBase, h.nodeBase, h.firstRoot, h.itemCount, h.nodeCount, h.rankThreshold)
  invFun := fun (itemBase, nodeBase, firstRoot, itemCount, nodeCount, rankThreshold) =>
    ⟨itemBase, nodeBase, firstRoot, itemCount, nodeCount, rankThreshold⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding SHHandle := .ofEquiv SHHandle.equiv

/-- Allocate dirty Soft Heap item and node pools of capacities `maxItems` and `maxNodes`. -/
def allocPool (maxItems maxNodes : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let ib ← Memory.allocDirty (3 * (maxItems + 1))
  let nb ← Memory.allocDirty (12 * (maxNodes + 1))
  pure (ib, nb)

/-- `allocPool` admits a uniform `Realizes .exact` compilation certificate (`work := 0`). -/
theorem realizes_allocPool : Realizes .exact
    (fun d : Fin 2 → ℕ => allocPool (d 0) (d 1))
    (.refl _) (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d s => Fits w (s.frontier + 3 * (d 0 + 1) + 12 * (d 1 + 1) + 16))
    (fun _ _ => 0) := by
  realize
  all_goals exact h.of_le (by omega)

/-- Helper `defillPickChild d` (`d = ![nodeBase, cur, l, r]`): selects smaller-`ckey` child
of `cur` (with `l ≠ 0 ∨ r ≠ 0`) and swaps it into `cur.left` if needed, returning its index. -/
private def defillPickChild (d : Fin 4 → ℕ) : Memory.Prog ℕ := do
  if d 2 = 0 then
    Memory.write (d 0 + 12 * d 1 + 6) (d 3)
    Memory.write (d 0 + 12 * d 1 + 7) 0
    pure (d 3)
  else if d 3 = 0 then
    Memory.read (d 0 + 12 * d 1 + 6)
  else
    let lc ← Memory.read (d 0 + 12 * d 2)
    let rc ← Memory.read (d 0 + 12 * d 3)
    if rc < lc then
      Memory.write (d 0 + 12 * d 1 + 6) (d 3)
      Memory.write (d 0 + 12 * d 1 + 7) (d 2)
      pure (d 3)
    else
      pure (d 2)

/-- Helper `defillSplice d` (`d = ![itemBase, nodeBase, cur, c, curSz]`): appends `c`'s item
list onto `cur`'s item list in `O(1)` memory operations, updates `cur.ckey` and `cur.size`,
and clears `c`. -/
private def defillSplice (d : Fin 5 → ℕ) : Memory.Prog Unit := do
  let cCk ← Memory.read (d 1 + 12 * d 3)
  let cSz ← Memory.read (d 1 + 12 * d 3 + 3)
  let cHead ← Memory.read (d 1 + 12 * d 3 + 4)
  let cTail ← Memory.read (d 1 + 12 * d 3 + 5)
  let curHead ← Memory.read (d 1 + 12 * d 2 + 4)
  if curHead = 0 then
    Memory.write (d 1 + 12 * d 2 + 4) cHead
  else
    let curTail ← Memory.read (d 1 + 12 * d 2 + 5)
    Memory.write (d 0 + 3 * curTail + 2) cHead
  Memory.write (d 1 + 12 * d 2 + 5) cTail
  Memory.write (d 1 + 12 * d 2 + 3) (d 4 + cSz)
  Memory.write (d 1 + 12 * d 2) cCk
  Memory.write (d 1 + 12 * d 3 + 4) 0
  Memory.write (d 1 + 12 * d 3 + 5) 0
  Memory.write (d 1 + 12 * d 3 + 3) 0

/-- Helper `defillFinish d` (`d = ![nodeBase, cur, c]`): deletes child `c` if leaf and returns
`cur`, otherwise sets `c.parent := cur` and returns `c`. -/
private def defillFinish (d : Fin 3 → ℕ) : Memory.Prog ℕ := do
  let cl ← Memory.read (d 0 + 12 * d 2 + 6)
  let cr ← Memory.read (d 0 + 12 * d 2 + 7)
  if cl = 0 ∧ cr = 0 then
    let nr ← Memory.read (d 0 + 12 * d 1 + 7)
    Memory.write (d 0 + 12 * d 1 + 6) nr
    Memory.write (d 0 + 12 * d 1 + 7) 0
    pure (d 1)
  else
    Memory.write (d 0 + 12 * d 2 + 8) (d 1)
    pure (d 2)

/-- Single `defill` step on node `cur` (`d = ![itemBase, nodeBase, cur]`), returning the next
node (`cur`, child `c`, or `cur.parent`) or `0` when done. -/
private def defillStep (d : Fin 3 → ℕ) : Memory.Prog ℕ := do
  let sz ← Memory.read (d 1 + 12 * d 2 + 3)
  let tgt ← Memory.read (d 1 + 12 * d 2 + 2)
  let l ← Memory.read (d 1 + 12 * d 2 + 6)
  let r ← Memory.read (d 1 + 12 * d 2 + 7)
  if sz < tgt ∧ (l ≠ 0 ∨ r ≠ 0) then
    let c ← defillPickChild ![d 1, d 2, l, r]
    defillSplice ![d 0, d 1, d 2, c, sz]
    defillFinish ![d 1, d 2, c]
  else
    Memory.read (d 1 + 12 * d 2 + 8)

private theorem realizes_defillPickChild_history : Realizes .exact
    defillPickChild (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w d s => Fits w 16 ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defillPickChild d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [defillPickChild] at hv
    simp_all only [ite_true, ite_false, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.runClient_lift,
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.valid]
    fits

private theorem realizes_defillPickChild : Realizes .exact
    defillPickChild (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w _ _ => Fits w 16) (fun _ _ => 0) :=
  realizes_defillPickChild_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private theorem realizes_defillSplice_history : Realizes .exact
    defillSplice (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => Fits w 16 ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defillSplice d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [defillSplice] at hv
    simp_all only [ite_true, ite_false, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.runClient_lift,
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_defillSplice : Realizes .exact
    defillSplice (.refl _) (WordEncoding.encode (α := Unit))
    (fun w _ _ => Fits w 16) (fun _ _ => 0) :=
  realizes_defillSplice_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private theorem realizes_defillFinish_history : Realizes .exact
    defillFinish (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w d s => Fits w 16 ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defillFinish d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [defillFinish] at hv
    simp_all only [ite_true, and_self, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.valid]
    fits

private theorem realizes_defillFinish : Realizes .exact
    defillFinish (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w _ _ => Fits w 16) (fun _ _ => 0) :=
  realizes_defillFinish_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private theorem realizes_defillStep_history : Realizes .exact
    defillStep (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w d s => Fits w 16 ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defillStep d)))
    (fun _ _ => 0) := by
  realize [realizes_defillPickChild, realizes_defillSplice, realizes_defillFinish]
  all_goals
    obtain ⟨h16, hv⟩ := h
    first
    | exact h16
    | (have hfront := hmem.frontier_fits
       dsimp only [defillStep] at hv
       simp_all only [StateTransitionSpec.clientHistory,
         StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
         StateTransitionSpec.stepFn, Memory.read, Memory.step_read, Memory.valid]
       fits)

/-- `defillStep` is uniformly realized over `Fits w 16` once source memory admissibility holds. -/
private theorem realizes_defillStep : Realizes .exact
    defillStep (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w _ _ => Fits w 16) (fun _ _ => 0) :=
  realizes_defillStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Refill node `rootIdx` (`d = ![itemBase, nodeBase, rootIdx, fuel]`) along its smallest-`ckey`
child chain up to `targetSize`, clearing `rootIdx.parent := 0` before ascending back to `0`. -/
def defill (d : Fin 4 → ℕ) : Memory.Prog Unit := do
  Memory.write (d 1 + 12 * d 2 + 8) 0
  let _ ← boundedWhile (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
    (fun x => defillStep ![d 0, d 1, x.2]) () (d 3) (d 2)
  pure ()

/-- Native safety domain for `defill d` (`d = ![itemBase, nodeBase, rootIdx, fuel]`). -/
def defillSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    whileSafe (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
      (fun x : Unit × ℕ => defillStep ![d 0, d 1, x.2])
      (fun w _ _ => Fits w 16)
      w () (d 3) (d 2) ⟨Function.update s.mem (d 1 + 12 * d 2 + 8) 0, s.frontier⟩

private theorem realizes_defill_history : Realizes .exact
    defill (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => defillSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defill d)))
    (fun _ _ => 0) := by
  unfold defill
  realize [realizes_defillStep]
  all_goals
    obtain ⟨hs, hv⟩ := h
    have hfront := hmem.frontier_fits
    simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.write,
      Memory.valid] at hv
    first
    | exact hs.1.of_le (by omega)
    | exact hfront.of_le (by have := hv.1.1; omega)
    | exact fun _ => hs.2

/-- `defill` is uniformly realized on `defillSafe`. -/
theorem realizes_defill : Realizes .exact
    defill (.refl _) (WordEncoding.encode (α := Unit)) defillSafe (fun _ _ => 0) :=
  realizes_defill_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Single suffix-min update step on root `cur` (`d = ![nodeBase, cur]`), returning
`cur.prevRoot`. -/
private def updateSuffixMinStep (d : Fin 2 → ℕ) : Memory.Prog ℕ := do
  let nxt ← Memory.read (d 0 + 12 * d 1 + 10)
  let ck ← Memory.read (d 0 + 12 * d 1)
  if nxt = 0 then
    Memory.write (d 0 + 12 * d 1 + 11) (d 1)
  else
    let sm ← Memory.read (d 0 + 12 * nxt + 11)
    let smCk ← Memory.read (d 0 + 12 * sm)
    if ck ≤ smCk then
      Memory.write (d 0 + 12 * d 1 + 11) (d 1)
    else
      Memory.write (d 0 + 12 * d 1 + 11) sm
  Memory.read (d 0 + 12 * d 1 + 9)

private theorem realizes_updateSuffixMinStep_history : Realizes .exact
    updateSuffixMinStep (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w d s => Fits w 16 ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (updateSuffixMinStep d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [updateSuffixMinStep] at hv
    simp_all only [ite_true, ite_false, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.valid]
    fits

private theorem realizes_updateSuffixMinStep : Realizes .exact
    updateSuffixMinStep (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w _ _ => Fits w 16) (fun _ _ => 0) :=
  realizes_updateSuffixMinStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Propagate suffix-min pointers from `startIdx` up `prevRoot` links (`d = ![nodeBase, startIdx,
fuel]`). -/
private def updateSuffixMinUp (d : Fin 3 → ℕ) : Memory.Prog Unit := do
  let _ ← boundedWhile (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
    (fun x => updateSuffixMinStep ![d 0, x.2]) () (d 2) (d 1)
  pure ()

/-- Native safety domain for `updateSuffixMinUp d` (`d = ![nodeBase, startIdx, fuel]`). -/
private def updateSuffixMinSafe (w : ℕ) (d : Fin 3 → ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    whileSafe (fun (_ : Unit) (cur : ℕ) => cur ≠ 0)
      (fun x : Unit × ℕ => updateSuffixMinStep ![d 0, x.2])
      (fun w _ _ => Fits w 16)
      w () (d 2) (d 1) s

/-- `updateSuffixMinUp` is uniformly realized on `updateSuffixMinSafe`. -/
private theorem realizes_updateSuffixMinUp : Realizes .exact
    updateSuffixMinUp (.refl _) (WordEncoding.encode (α := Unit))
    updateSuffixMinSafe (fun _ _ => 0) := by
  unfold updateSuffixMinUp
  realize [realizes_updateSuffixMinStep]
  exact fun _ => h.2

/-- Initialize a new item slot and rank-0 node (`d = ![itemBase, nodeBase, itemIdx, nodeIdx,
val, origKey]`). -/
private def shInsertInit (d : Fin 6 → ℕ) : Memory.Prog Unit := do
  Memory.write (d 0 + 3 * d 2) (d 4)
  Memory.write (d 0 + 3 * d 2 + 1) (d 5)
  Memory.write (d 0 + 3 * d 2 + 2) 0
  Memory.write (d 1 + 12 * d 3) (d 5)
  Memory.write (d 1 + 12 * d 3 + 1) 0
  Memory.write (d 1 + 12 * d 3 + 2) 1
  Memory.write (d 1 + 12 * d 3 + 3) 1
  Memory.write (d 1 + 12 * d 3 + 4) (d 2)
  Memory.write (d 1 + 12 * d 3 + 5) (d 2)
  Memory.write (d 1 + 12 * d 3 + 6) 0
  Memory.write (d 1 + 12 * d 3 + 7) 0
  Memory.write (d 1 + 12 * d 3 + 8) 0
  Memory.write (d 1 + 12 * d 3 + 9) 0
  Memory.write (d 1 + 12 * d 3 + 10) 0
  Memory.write (d 1 + 12 * d 3 + 11) (d 3)

private theorem realizes_shInsertInit_history : Realizes .exact
    shInsertInit (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => Fits w 16 ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (shInsertInit d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [shInsertInit] at hv
    simp_all only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.runClient_lift, StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.write, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_shInsertInit : Realizes .exact
    shInsertInit (.refl _) (WordEncoding.encode (α := Unit))
    (fun w _ _ => Fits w 16) (fun _ _ => 0) :=
  realizes_shInsertInit_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Write all 12 fields of a fresh combined node (`d = ![nodeBase, z, y, p, rank, target]`). -/
private def combineWriteParent (d : Fin 6 → ℕ) : Memory.Prog Unit := do
  Memory.write (d 0 + 12 * d 3) 0
  Memory.write (d 0 + 12 * d 3 + 1) (d 4)
  Memory.write (d 0 + 12 * d 3 + 2) (d 5)
  Memory.write (d 0 + 12 * d 3 + 3) 0
  Memory.write (d 0 + 12 * d 3 + 4) 0
  Memory.write (d 0 + 12 * d 3 + 5) 0
  Memory.write (d 0 + 12 * d 3 + 6) (d 1)
  Memory.write (d 0 + 12 * d 3 + 7) (d 2)
  Memory.write (d 0 + 12 * d 3 + 8) 0
  Memory.write (d 0 + 12 * d 3 + 9) 0
  Memory.write (d 0 + 12 * d 3 + 10) 0
  Memory.write (d 0 + 12 * d 3 + 11) 0

private theorem realizes_combineWriteParent_history : Realizes .exact
    combineWriteParent (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => Fits w 16 ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (combineWriteParent d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [combineWriteParent] at hv
    simp_all only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.runClient_lift, StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.write, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_combineWriteParent : Realizes .exact
    combineWriteParent (.refl _) (WordEncoding.encode (α := Unit))
    (fun w _ _ => Fits w 16) (fun _ _ => 0) :=
  realizes_combineWriteParent_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Initialize parent node `p` combining `z` and `y` (`d = ![nodeBase, z, y, p, zRank,
zTarget, rankThreshold]`). -/
private def combineInitParent (d : Fin 7 → ℕ) : Memory.Prog Unit :=
  if d 4 + 1 ≤ d 6 then combineWriteParent ![d 0, d 1, d 2, d 3, d 4 + 1, 1]
  else if (d 4 + 1 - d 6) % 2 = 1 then
    combineWriteParent ![d 0, d 1, d 2, d 3, d 4 + 1, d 5 + d 5]
  else combineWriteParent ![d 0, d 1, d 2, d 3, d 4 + 1, d 5]

private theorem validHistory_combineWriteParent {w : ℕ} {d : Fin 6 → ℕ} {s : Memory.State}
    (hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (combineWriteParent d))) :
    Fits w (d 4) ∧ Fits w (d 5) := by
  simp only [combineWriteParent, StateTransitionSpec.clientHistory,
    StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
    StateTransitionSpec.stepFn, Memory.write, Memory.step_write, Memory.valid] at hv
  exact ⟨hv.2.1.2, hv.2.2.1.2⟩

private theorem validHistory_combineInitParent {w : ℕ} {d : Fin 7 → ℕ} {s : Memory.State}
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (if d 4 + 1 ≤ d 6 then combineWriteParent ![d 0, d 1, d 2, d 3, d 4 + 1, 1]
       else if (d 4 + 1 - d 6) % 2 = 1 then
         combineWriteParent ![d 0, d 1, d 2, d 3, d 4 + 1, d 5 + d 5]
       else combineWriteParent ![d 0, d 1, d 2, d 3, d 4 + 1, d 5]))) :
    Fits w (d 4 + 1) ∧ (d 6 < d 4 + 1 → (d 4 + 1 - d 6) % 2 = 1 → Fits w (d 5 + d 5)) := by
  split_ifs at hv with hr hmod
  · have ⟨h4, _⟩ := validHistory_combineWriteParent hv
    exact ⟨h4, fun h => absurd h (Nat.not_lt.mpr hr)⟩
  · have ⟨h4, h5⟩ := validHistory_combineWriteParent hv
    exact ⟨h4, fun _ _ => h5⟩
  · have ⟨h4, _⟩ := validHistory_combineWriteParent hv
    exact ⟨h4, fun _ hm => absurd hm hmod⟩

private theorem realizes_combineInitParent_history : Realizes .exact
    combineInitParent (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => Fits w 16 ∧ Fits w (d 6) ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (combineInitParent d)))
    (fun _ _ => 0) := by
  unfold combineInitParent
  realize [realizes_combineWriteParent]
  all_goals
    obtain ⟨h16, h6, hv⟩ := h
    have ⟨h4, h5⟩ := validHistory_combineInitParent hv
    first
    | exact h4
    | exact h4.of_le (by omega)
    | exact h5 (by assumption) (by assumption)
    | omega
    | fits

private theorem realizes_combineInitParent : Realizes .exact
    combineInitParent (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d _ => Fits w 16 ∧ Fits w (d 6)) (fun _ _ => 0) :=
  realizes_combineInitParent_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h.1, h.2, hv⟩)

/-- Unlink `firstRoot` from the front of the root list (`d = ![nodeBase, firstRoot]`), returning
the new `firstRoot` (`nextRoot`). -/
private def combinePopFront (d : Fin 2 → ℕ) : Memory.Prog ℕ := do
  let nxt ← Memory.read (d 0 + 12 * d 1 + 10)
  if nxt ≠ 0 then
    Memory.write (d 0 + 12 * nxt + 9) 0
  else
    pure ()
  pure nxt

private theorem realizes_combinePopFront_history : Realizes .exact
    combinePopFront (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w d s => Fits w 16 ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (combinePopFront d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [combinePopFront] at hv
    simp_all only [ne_eq, not_false_eq_true, ite_true, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.valid]
  all_goals fits

private theorem realizes_combinePopFront : Realizes .exact
    combinePopFront (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w _ _ => Fits w 16) (fun _ _ => 0) :=
  realizes_combinePopFront_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Prepare combined parent node `nodeCount + 1` before calling `defill` (`d = ![itemBase,
nodeBase, z, firstRoot, nodeCount, fuel, rankThreshold]`), returning `nextFirst`. -/
private def combinePreInit (d : Fin 7 → ℕ) : Memory.Prog ℕ := do
  let zRank ← Memory.read (d 1 + 12 * d 2 + 1)
  let zTgt ← Memory.read (d 1 + 12 * d 2 + 2)
  let nextFirst ← combinePopFront ![d 1, d 3]
  combineInitParent ![d 1, d 2, d 3, d 4 + 1, zRank, zTgt, d 6]
  pure nextFirst

private theorem realizes_combinePreInit_history : Realizes .exact
    combinePreInit (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w d s => Fits w 16 ∧ Fits w (d 4 + 1) ∧ Fits w (d 6) ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (combinePreInit d)))
    (fun _ _ => 0) := by
  realize [realizes_combinePopFront, realizes_combineInitParent]
  all_goals
    obtain ⟨h16, hp, h6, hv⟩ := h
    first
    | exact h16
    | exact h6
    | exact hp
    | (have hfront := hmem.frontier_fits
       dsimp only [combinePreInit] at hv
       simp_all only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind',
         StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
         Memory.step_read, Memory.valid]
       fits)

private theorem realizes_combinePreInit : Realizes .exact
    combinePreInit (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w d _ => Fits w 16 ∧ Fits w (d 4 + 1) ∧ Fits w (d 6)) (fun _ _ => 0) :=
  realizes_combinePreInit_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h.1, h.2.1, h.2.2, hv⟩)

/-- Combine `z` and `firstRoot` into `nodeCount + 1` and run `defill` (`d = ![itemBase, nodeBase,
z, firstRoot, nodeCount, fuel, rankThreshold]`), returning `(newNode, nextFirst)`. -/
private def combineOne (d : Fin 7 → ℕ) : Memory.Prog (ℕ × ℕ) := do
  let nextFirst ← combinePreInit d
  defill ![d 0, d 1, d 4 + 1, d 5]
  pure (d 4 + 1, nextFirst)

/-- Native safety domain for `combineOne`. -/
private def combineOneSafe (w : ℕ) (d : Fin 7 → ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d 4 + 1) ∧ Fits w (d 6) ∧
    defillSafe w ![d 0, d 1, d 4 + 1, d 5]
      ((Memory.spec 0).clientState s (combinePreInit d))

private theorem realizes_combineOne : Realizes .exact
    combineOne (.refl _) (WordEncoding.encode (α := ℕ × ℕ))
    combineOneSafe (fun _ _ => 0) := by
  unfold combineOne
  realize [realizes_combinePreInit, realizes_defill]
  all_goals first
    | exact h.1
    | exact h.2.1
    | exact h.2.2.1
    | exact h.2.2.2

/-- Item pool base in `combineStep` input `((itemBase, nodeBase, rankThreshold, fuel),
(z, firstRoot, nodeCount, cont))`. -/
private abbrev combineItemBase (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) : ℕ := d.1.1

/-- Node pool base in `combineStep` input. -/
private abbrev combineNodeBase (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) : ℕ := d.1.2.1

/-- Corruption rank threshold in `combineStep` input. -/
private abbrev combineRankThreshold (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) : ℕ := d.1.2.2.1

/-- Defill fuel in `combineStep` input. -/
private abbrev combineFuel (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) : ℕ := d.1.2.2.2

/-- Candidate root index `z` in `combineStep` input. -/
private abbrev combineZ (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) : ℕ := d.2.1

/-- Root-list cursor `firstRoot` in `combineStep` input. -/
private abbrev combineFirstRoot (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) : ℕ := d.2.2.1

/-- Current allocated node count in `combineStep` input. -/
private abbrev combineNodeCount (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) : ℕ := d.2.2.2.1

/-- Next root-list cursor `firstRoot` in `combineStep` state `(z, firstRoot, nodeCount, cont)`. -/
private abbrev combineStateFirstRoot (a : ℕ × ℕ × ℕ × ℕ) : ℕ := a.2.1

/-- Allocated node count in `combineStep` state `(z, firstRoot, nodeCount, cont)`. -/
private abbrev combineStateNodeCount (a : ℕ × ℕ × ℕ × ℕ) : ℕ := a.2.2.1

/-- Continuation flag in `combineStep` state `(z, firstRoot, nodeCount, cont)`. -/
private abbrev combineStateCont (a : ℕ × ℕ × ℕ × ℕ) : ℕ := a.2.2.2

/-- Single step of `shInsert` binomial-style root combining: `d.1 = (itemBase, nodeBase,
rankThreshold, fuel)`, `d.2 = (z, firstRoot, nodeCount, cont)`. -/
private def combineStep (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) :
    Memory.Prog (ℕ × ℕ × ℕ × ℕ) := do
  let zRank ← Memory.read (combineNodeBase d + 12 * combineZ d + 1)
  if combineFirstRoot d = 0 then
    pure (combineZ d, 0, combineNodeCount d, 0)
  else
    let yRank ← Memory.read (combineNodeBase d + 12 * combineFirstRoot d + 1)
    if yRank ≠ zRank then
      pure (combineZ d, combineFirstRoot d, combineNodeCount d, 0)
    else
      let res ← combineOne ![combineItemBase d, combineNodeBase d, combineZ d,
        combineFirstRoot d, combineNodeCount d, combineFuel d, combineRankThreshold d]
      pure (res.1, res.2, res.1, 1)

/-- Native safety domain for one `combineStep`. -/
private def combineStepSafe (w : ℕ)
    (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    (combineFirstRoot d ≠ 0 →
      s.mem (combineNodeBase d + 12 * combineFirstRoot d + 1) =
        s.mem (combineNodeBase d + 12 * combineZ d + 1) →
      combineOneSafe w ![combineItemBase d, combineNodeBase d, combineZ d,
        combineFirstRoot d, combineNodeCount d, combineFuel d, combineRankThreshold d] s)

private theorem realizes_combineStep_history : Realizes .exact
    combineStep (appendWords (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ))
    (fun w d s => combineStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (combineStep d)))
    (fun _ _ => 0) := by
  unfold combineStep
  realize [realizes_combineOne]
  all_goals
    obtain ⟨hs, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [ite_false, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.step_read, Memory.valid]
    first
    | exact hs.1.of_le (by decide)
    | exact hs.2 (by assumption) (by assumption)
    | fits

private theorem realizes_combineStep : Realizes .exact
    combineStep (appendWords (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ))
    combineStepSafe (fun _ _ => 0) :=
  realizes_combineStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Link root `z` onto the front of `firstRoot` and update `z.suffixMin` (`d = ![nodeBase, z,
firstRoot]`). -/
private def shInsertLinkRoot (d : Fin 3 → ℕ) : Memory.Prog Unit := do
  if d 2 = 0 then
    Memory.write (d 0 + 12 * d 1 + 9) 0
    Memory.write (d 0 + 12 * d 1 + 10) 0
    Memory.write (d 0 + 12 * d 1 + 11) (d 1)
  else
    let zCk ← Memory.read (d 0 + 12 * d 1)
    let sm ← Memory.read (d 0 + 12 * d 2 + 11)
    let smCk ← Memory.read (d 0 + 12 * sm)
    Memory.write (d 0 + 12 * d 1 + 9) 0
    Memory.write (d 0 + 12 * d 1 + 10) (d 2)
    Memory.write (d 0 + 12 * d 2 + 9) (d 1)
    if zCk ≤ smCk then
      Memory.write (d 0 + 12 * d 1 + 11) (d 1)
    else
      Memory.write (d 0 + 12 * d 1 + 11) sm

private theorem realizes_shInsertLinkRoot_history : Realizes .exact
    shInsertLinkRoot (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => Fits w 16 ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (shInsertLinkRoot d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [shInsertLinkRoot] at hv
    simp_all only [ite_true, ite_false, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.runClient_lift,
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_shInsertLinkRoot : Realizes .exact
    shInsertLinkRoot (.refl _) (WordEncoding.encode (α := Unit))
    (fun w _ _ => Fits w 16) (fun _ _ => 0) :=
  realizes_shInsertLinkRoot_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Flat-parameter `shInsert` (`d = ![itemBase, nodeBase, firstRoot, itemCount, nodeCount, val,
origKey, fuel, rankThreshold]`), returning `(newFirstRoot, newItemCount, newNodeCount)`. -/
private def shInsertRaw (d : Fin 9 → ℕ) : Memory.Prog (ℕ × ℕ × ℕ) := do
  shInsertInit ![d 0, d 1, d 3 + 1, d 4 + 1, d 5, d 6]
  let st ← boundedWhile (fun (_ : ℕ × ℕ × ℕ × ℕ) (a : ℕ × ℕ × ℕ × ℕ) => combineStateCont a ≠ 0)
    combineStep (d 0, d 1, d 8, d 7) (d 7) (d 4 + 1, d 2, d 4 + 1, 1)
  shInsertLinkRoot ![d 1, st.1, combineStateFirstRoot st]
  pure (st.1, d 3 + 1, combineStateNodeCount st)

/-- Native safety domain for `shInsertRaw`. -/
private def shInsertRawSafe (w : ℕ) (d : Fin 9 → ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d 3 + 1) ∧ Fits w (d 4 + 1) ∧
    let s₁ := (Memory.spec 0).clientState s
      (shInsertInit ![d 0, d 1, d 3 + 1, d 4 + 1, d 5, d 6])
    whileSafe (fun (_ : ℕ × ℕ × ℕ × ℕ) (a : ℕ × ℕ × ℕ × ℕ) => combineStateCont a ≠ 0)
      combineStep combineStepSafe w (d 0, d 1, d 8, d 7) (d 7) (d 4 + 1, d 2, d 4 + 1, 1) s₁

private theorem realizes_shInsertRaw : Realizes .exact
    shInsertRaw (.refl _) (WordEncoding.encode (α := ℕ × ℕ × ℕ))
    shInsertRawSafe (fun _ _ => 0) := by
  unfold shInsertRaw
  realize [realizes_shInsertInit, realizes_combineStep, realizes_shInsertLinkRoot]
  all_goals first
    | exact h.1
    | exact h.1.of_le (by decide)
    | exact h.2.1
    | exact h.2.2.1
    | exact fun _ => whileSafe_imp _ _ (fun _ => Iff.rfl) (fun _ => rfl)
        (fun ⟨_, _, _, _⟩ _ _ hs => hs) h.2.2.2

/-- Payload value argument `val` in `shInsert` input `(h, val, origKey, fuel)`. -/
private abbrev shInsertVal (d : SHHandle × ℕ × ℕ × ℕ) : ℕ := d.2.1

/-- Original key argument `origKey` in `shInsert` input `(h, val, origKey, fuel)`. -/
private abbrev shInsertOrigKey (d : SHHandle × ℕ × ℕ × ℕ) : ℕ := d.2.2.1

/-- Defill fuel argument `fuel` in `shInsert` input `(h, val, origKey, fuel)`. -/
private abbrev shInsertFuel (d : SHHandle × ℕ × ℕ × ℕ) : ℕ := d.2.2.2

/-- Updated item count field in `shInsertRaw` result `(firstRoot, itemCount, nodeCount)`. -/
private abbrev shInsertResItemCount (res : ℕ × ℕ × ℕ) : ℕ := res.2.1

/-- Updated node count field in `shInsertRaw` result `(firstRoot, itemCount, nodeCount)`. -/
private abbrev shInsertResNodeCount (res : ℕ × ℕ × ℕ) : ℕ := res.2.2

/-- Insert item `(val, origKey)` into soft heap `h` (`d = (h, val, origKey, fuel)`). -/
def shInsert (d : SHHandle × ℕ × ℕ × ℕ) : Memory.Prog SHHandle := do
  let res ← shInsertRaw ![d.1.itemBase, d.1.nodeBase, d.1.firstRoot, d.1.itemCount,
    d.1.nodeCount, shInsertVal d, shInsertOrigKey d, shInsertFuel d, d.1.rankThreshold]
  pure ⟨d.1.itemBase, d.1.nodeBase, res.1, shInsertResItemCount res,
    shInsertResNodeCount res, d.1.rankThreshold⟩

/-- Native safety domain for `shInsert`. -/
def shInsertSafe (w : ℕ) (d : SHHandle × ℕ × ℕ × ℕ) (s : Memory.State) : Prop :=
  shInsertRawSafe w ![d.1.itemBase, d.1.nodeBase, d.1.firstRoot, d.1.itemCount,
    d.1.nodeCount, shInsertVal d, shInsertOrigKey d, shInsertFuel d, d.1.rankThreshold] s

/-- `shInsert` admits a uniform `Realizes .exact` compilation certificate (`work := 0`). -/
theorem realizes_shInsert : Realizes .exact
    shInsert (WordEncoding.encode (α := SHHandle × ℕ × ℕ × ℕ))
    (WordEncoding.encode (α := SHHandle)) shInsertSafe (fun _ _ => 0) := by
  unfold shInsert
  realize [realizes_shInsertRaw]
  exact h

/-- Pop the head item of root `x` (`d = ![itemBase, nodeBase, x]`), returning
`(val, popKey)`. -/
private def extractPopItem (d : Fin 3 → ℕ) : Memory.Prog (ℕ × ℕ) := do
  let popKey ← Memory.read (d 1 + 12 * d 2)
  let it ← Memory.read (d 1 + 12 * d 2 + 4)
  let xSz ← Memory.read (d 1 + 12 * d 2 + 3)
  let val ← Memory.read (d 0 + 3 * it)
  let nextIt ← Memory.read (d 0 + 3 * it + 2)
  Memory.write (d 1 + 12 * d 2 + 4) nextIt
  if nextIt = 0 then
    Memory.write (d 1 + 12 * d 2 + 5) 0
  else
    pure ()
  Memory.write (d 1 + 12 * d 2 + 3) (xSz - 1)
  pure (val, popKey)

private theorem realizes_extractPopItem_history : Realizes .exact
    extractPopItem (.refl _) (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d s => Fits w 16 ∧ 1 ≤ s.mem (d 1 + 12 * d 2 + 3) ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (extractPopItem d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, hsz, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [extractPopItem] at hv
    simp_all only [ite_true, ite_false, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals first | omega | fits

private theorem realizes_extractPopItem : Realizes .exact
    extractPopItem (.refl _) (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d s => Fits w 16 ∧ 1 ≤ s.mem (d 1 + 12 * d 2 + 3)) (fun _ _ => 0) :=
  realizes_extractPopItem_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h.1, h.2, hv⟩)

/-- Unlink root `x` from the doubly-linked root list (`d = ![nodeBase, firstRoot, x]`),
returning `(newFirstRoot, xPrevRoot)`. -/
private def unlinkLinks (d : Fin 3 → ℕ) : Memory.Prog (ℕ × ℕ) := do
  let p ← Memory.read (d 0 + 12 * d 2 + 9)
  let q ← Memory.read (d 0 + 12 * d 2 + 10)
  if q ≠ 0 then
    Memory.write (d 0 + 12 * q + 9) p
  else
    pure ()
  if p ≠ 0 then
    Memory.write (d 0 + 12 * p + 10) q
    pure (d 1, p)
  else
    pure (q, 0)

private theorem realizes_unlinkLinks_history : Realizes .exact
    unlinkLinks (.refl _) (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d s => Fits w 16 ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (unlinkLinks d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [unlinkLinks] at hv
    simp_all only [ne_eq, not_false_eq_true, not_true_eq_false, ite_true, ite_false,
      StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_unlinkLinks : Realizes .exact
    unlinkLinks (.refl _) (WordEncoding.encode (α := ℕ × ℕ))
    (fun w _ _ => Fits w 16) (fun _ _ => 0) :=
  realizes_unlinkLinks_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Unlink leaf root `x` and propagate suffix-min updates (`d = ![nodeBase, firstRoot, x, fuel]`),
returning the new `firstRoot`. -/
private def extractUnlinkLeaf (d : Fin 4 → ℕ) : Memory.Prog ℕ := do
  let res ← unlinkLinks ![d 0, d 1, d 2]
  updateSuffixMinUp ![d 0, res.2, d 3]
  pure res.1

/-- Native safety domain for `extractUnlinkLeaf`. -/
private def extractUnlinkLeafSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    let res := (Memory.spec 0).clientResult s (unlinkLinks ![d 0, d 1, d 2])
    let s₁ := (Memory.spec 0).clientState s (unlinkLinks ![d 0, d 1, d 2])
    updateSuffixMinSafe w ![d 0, res.2, d 3] s₁

private theorem realizes_extractUnlinkLeaf : Realizes .exact
    extractUnlinkLeaf (.refl _) (WordEncoding.encode (α := ℕ))
    extractUnlinkLeafSafe (fun _ _ => 0) := by
  unfold extractUnlinkLeaf
  realize [realizes_unlinkLinks, realizes_updateSuffixMinUp]
  all_goals first
    | exact h.1
    | exact h.2

/-- Restore root `x` after popping its head item (`d = ![itemBase, nodeBase, firstRoot, x,
fuel]`), returning the new `firstRoot`. -/
private def extractFixup (d : Fin 5 → ℕ) : Memory.Prog ℕ := do
  let xl ← Memory.read (d 1 + 12 * d 3 + 6)
  let xr ← Memory.read (d 1 + 12 * d 3 + 7)
  let xSz ← Memory.read (d 1 + 12 * d 3 + 3)
  let xTgt ← Memory.read (d 1 + 12 * d 3 + 2)
  if xl = 0 ∧ xr = 0 then
    if xSz = 0 then extractUnlinkLeaf ![d 1, d 2, d 3, d 4]
    else pure (d 2)
  else if xSz + xSz < xTgt then
    defill ![d 0, d 1, d 3, d 4]
    updateSuffixMinUp ![d 1, d 3, d 4]
    pure (d 2)
  else
    pure (d 2)

/-- Native safety domain for `extractFixup`. -/
private def extractFixupSafe (w : ℕ) (d : Fin 5 → ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    let xl := s.mem (d 1 + 12 * d 3 + 6)
    let xr := s.mem (d 1 + 12 * d 3 + 7)
    let xSz := s.mem (d 1 + 12 * d 3 + 3)
    let xTgt := s.mem (d 1 + 12 * d 3 + 2)
    (¬ (xl = 0 ∧ xr = 0) → Fits w (xSz + xSz)) ∧
    (xl = 0 ∧ xr = 0 → xSz = 0 → extractUnlinkLeafSafe w ![d 1, d 2, d 3, d 4] s) ∧
    (¬ (xl = 0 ∧ xr = 0) → xSz + xSz < xTgt →
      defillSafe w ![d 0, d 1, d 3, d 4] s ∧
      updateSuffixMinSafe w ![d 1, d 3, d 4]
        ((Memory.spec 0).clientState s (defill ![d 0, d 1, d 3, d 4])))

private theorem realizes_extractFixup_history : Realizes .exact
    extractFixup (.refl _) (WordEncoding.encode (α := ℕ))
    (fun w d s => extractFixupSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (extractFixup d)))
    (fun _ _ => 0) := by
  unfold extractFixup
  realize [realizes_extractUnlinkLeaf, realizes_defill, realizes_updateSuffixMinUp]
  all_goals
    obtain ⟨hs, hv⟩ := h
    obtain ⟨h16, h2sz, hs1, hs2⟩ := hs
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [and_self, true_and, and_false, false_and, not_false_eq_true,
      not_true_eq_false, true_implies, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.step_read, Memory.valid]
  all_goals fits

private theorem realizes_extractFixup : Realizes .exact
    extractFixup (.refl _) (WordEncoding.encode (α := ℕ))
    extractFixupSafe (fun _ _ => 0) :=
  realizes_extractFixup_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Flat-parameter `shExtractMin` (`d = ![itemBase, nodeBase, firstRoot, fuel]`), returning
`(newFirstRoot, found, val, popKey)`. -/
private def shExtractMinRaw (d : Fin 4 → ℕ) : Memory.Prog (ℕ × ℕ × ℕ × ℕ) := do
  if d 2 = 0 then
    pure (0, 0, 0, 0)
  else
    let x ← Memory.read (d 1 + 12 * d 2 + 11)
    let popped ← extractPopItem ![d 0, d 1, x]
    let nf ← extractFixup ![d 0, d 1, d 2, x, d 3]
    pure (nf, 1, popped.1, popped.2)

/-- Native safety domain for `shExtractMinRaw`. -/
private def shExtractMinRawSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    (d 2 ≠ 0 →
      let x := s.mem (d 1 + 12 * d 2 + 11)
      1 ≤ s.mem (d 1 + 12 * x + 3) ∧
      extractFixupSafe w ![d 0, d 1, d 2, x, d 3]
        ((Memory.spec 0).clientState s (extractPopItem ![d 0, d 1, x])))

private theorem realizes_shExtractMinRaw_history : Realizes .exact
    shExtractMinRaw (.refl _) (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ))
    (fun w d s => shExtractMinRawSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (shExtractMinRaw d)))
    (fun _ _ => 0) := by
  unfold shExtractMinRaw
  realize [realizes_extractPopItem, realizes_extractFixup]
  all_goals
    obtain ⟨hs, hv⟩ := h
    obtain ⟨h16, hs2⟩ := hs
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [ite_false, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.step_read, Memory.valid]
  all_goals first
    | exact h16.of_le (by decide)
    | exact (hs2 (by assumption)).1
    | exact (hs2 (by assumption)).2
    | fits

private theorem realizes_shExtractMinRaw : Realizes .exact
    shExtractMinRaw (.refl _) (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ))
    shExtractMinRawSafe (fun _ _ => 0) :=
  realizes_shExtractMinRaw_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Result returned by `shExtractMin`: updated handle, found flag (`1` iff non-empty),
extracted item payload `val`, and extracted corrupted key `key`. -/
structure SHExtractResult where
  /-- Updated soft-heap handle after extraction. -/
  handle : SHHandle
  /-- `1` if an item was extracted, `0` if the heap was empty. -/
  found : ℕ
  /-- Payload value of the extracted item (`0` if empty). -/
  val : ℕ
  /-- Corrupted key of the extracted item (`0` if empty). -/
  key : ℕ
  deriving DecidableEq

/-- Canonical 9-word tuple equivalence for `SHExtractResult`. -/
@[expose] def SHExtractResult.equiv : SHExtractResult ≃ SHHandle × ℕ × ℕ × ℕ where
  toFun r := (r.handle, r.found, r.val, r.key)
  invFun := fun (handle, found, val, key) => ⟨handle, found, val, key⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding SHExtractResult := .ofEquiv SHExtractResult.equiv

private abbrev shExtractRawFound (res : ℕ × ℕ × ℕ × ℕ) : ℕ := res.2.1

private abbrev shExtractRawVal (res : ℕ × ℕ × ℕ × ℕ) : ℕ := res.2.2.1

private abbrev shExtractRawKey (res : ℕ × ℕ × ℕ × ℕ) : ℕ := res.2.2.2

/-- Extract a minimum-key item from soft heap `d.1` (`d = (h, fuel)`). -/
def shExtractMin (d : SHHandle × ℕ) : Memory.Prog SHExtractResult := do
  let res ← shExtractMinRaw ![d.1.itemBase, d.1.nodeBase, d.1.firstRoot, d.2]
  pure ⟨⟨d.1.itemBase, d.1.nodeBase, res.1, d.1.itemCount, d.1.nodeCount, d.1.rankThreshold⟩,
    shExtractRawFound res, shExtractRawVal res, shExtractRawKey res⟩

/-- Native safety domain for `shExtractMin`. -/
def shExtractMinSafe (w : ℕ) (d : SHHandle × ℕ) (s : Memory.State) : Prop :=
  shExtractMinRawSafe w ![d.1.itemBase, d.1.nodeBase, d.1.firstRoot, d.2] s

/-- `shExtractMin` admits a uniform `Realizes .exact` compilation certificate (`work := 0`). -/
theorem realizes_shExtractMin : Realizes .exact
    shExtractMin (WordEncoding.encode (α := SHHandle × ℕ))
    (WordEncoding.encode (α := SHExtractResult)) shExtractMinSafe (fun _ _ => 0) := by
  unfold shExtractMin
  realize [realizes_shExtractMinRaw]
  exact h

/-- Item pool base in `collectItemsStep` input `((itemBase, ck, outBase), (it, curOut))`. -/
private abbrev collectItemBase (d : (ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.1.1

/-- Node corrupted key `ck` in `collectItemsStep` input. -/
private abbrev collectCKey (d : (ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.1.2.1

/-- Output array base `outBase` in `collectItemsStep` input. -/
private abbrev collectOutBase (d : (ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.1.2.2

/-- Current item cursor `it` in `collectItemsStep` input. -/
private abbrev collectCurItem (d : (ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.2.1

/-- Current output cursor `curOut` in `collectItemsStep` input. -/
private abbrev collectCurOut (d : (ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.2.2

/-- Single step walking an item list to collect corrupted items (`ok < ck`): `d.1 = (itemBase, ck,
outBase)`, `d.2 = (it, curOut)`. -/
private def collectItemsStep (d : (ℕ × ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let ok ← Memory.read (collectItemBase d + 3 * collectCurItem d + 1)
  let v ← Memory.read (collectItemBase d + 3 * collectCurItem d)
  let nxt ← Memory.read (collectItemBase d + 3 * collectCurItem d + 2)
  if ok < collectCKey d then
    Memory.write (collectOutBase d + collectCurOut d) v
    pure (nxt, collectCurOut d + 1)
  else
    pure (nxt, collectCurOut d)

private theorem realizes_collectItemsStep_history : Realizes .exact
    collectItemsStep (appendWords (WordEncoding.encode (α := ℕ × ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d s => Fits w 16 ∧ Fits w (collectCurOut d + 1) ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (collectItemsStep d)))
    (fun _ _ => 0) := by
  realize
  all_goals
    obtain ⟨h16, ho, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [collectItemsStep] at hv
    simp_all only [ite_true, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_collectItemsStep : Realizes .exact
    collectItemsStep (appendWords (WordEncoding.encode (α := ℕ × ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d _ => Fits w 16 ∧ Fits w (collectCurOut d + 1)) (fun _ _ => 0) :=
  realizes_collectItemsStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h.1, h.2, hv⟩)

/-- Scan the linked item list starting at `head` (`d = ![itemBase, ck, outBase, head, curOut,
fuel]`), appending corrupted payload values `val` to `outBase[curOut..]`. -/
private def collectItems (d : Fin 6 → ℕ) : Memory.Prog ℕ := do
  let st ← boundedWhile (fun (_ : ℕ × ℕ × ℕ) (a : ℕ × ℕ) => a.1 ≠ 0)
    collectItemsStep (d 0, d 1, d 2) (d 5) (d 3, d 4)
  pure st.2

/-- Native safety domain for `collectItems`. -/
private def collectItemsSafe (w : ℕ) (d : Fin 6 → ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    whileSafe (fun (_ : ℕ × ℕ × ℕ) (a : ℕ × ℕ) => a.1 ≠ 0)
      collectItemsStep (fun w a _ => Fits w 16 ∧ Fits w (collectCurOut a + 1))
      w (d 0, d 1, d 2) (d 5) (d 3, d 4) s

private theorem realizes_collectItems : Realizes .exact
    collectItems (.refl _) (WordEncoding.encode (α := ℕ))
    collectItemsSafe (fun _ _ => 0) := by
  unfold collectItems
  realize [realizes_collectItemsStep]
  exact fun _ => h.2

/-- Item pool base in `collectNodeStep` input `((itemBase, nodeBase, outBase, fuel),
(idx, curOut))`. -/
private abbrev collectNodeItemBase (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.1.1

/-- Node pool base in `collectNodeStep` input. -/
private abbrev collectNodeBase (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.1.2.1

/-- Output array base in `collectNodeStep` input. -/
private abbrev collectNodeOutBase (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.1.2.2.1

/-- Item-scan fuel in `collectNodeStep` input. -/
private abbrev collectNodeFuel (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.1.2.2.2

/-- Node index `idx` in `collectNodeStep` input. -/
private abbrev collectNodeIdx (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.2.1

/-- Output cursor `curOut` in `collectNodeStep` input. -/
private abbrev collectNodeOutCount (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.2.2

/-- Scan one node slot `idx` for corrupted items (`d.1 = (itemBase, nodeBase, outBase, fuel)`,
`d.2 = (idx, curOut)`). -/
private def collectNodeStep (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let ck ← Memory.read (collectNodeBase d + 12 * collectNodeIdx d)
  let hd ← Memory.read (collectNodeBase d + 12 * collectNodeIdx d + 4)
  let nextOut ←
    if hd = 0 then pure (collectNodeOutCount d)
    else collectItems ![collectNodeItemBase d, ck, collectNodeOutBase d, hd,
      collectNodeOutCount d, collectNodeFuel d]
  pure (collectNodeIdx d + 1, nextOut)

/-- Native safety domain for `collectNodeStep`. -/
private def collectNodeStepSafe (w : ℕ)
    (d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (collectNodeIdx d + 1) ∧
    (s.mem (collectNodeBase d + 12 * collectNodeIdx d + 4) ≠ 0 →
      collectItemsSafe w ![collectNodeItemBase d, s.mem (collectNodeBase d + 12 * collectNodeIdx d),
        collectNodeOutBase d, s.mem (collectNodeBase d + 12 * collectNodeIdx d + 4),
        collectNodeOutCount d, collectNodeFuel d] s)

private theorem realizes_collectNodeStep_history : Realizes .exact
    collectNodeStep (appendWords (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d s => collectNodeStepSafe w d s ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (collectNodeStep d)))
    (fun _ _ => 0) := by
  unfold collectNodeStep
  realize [realizes_collectItems]
  all_goals
    obtain ⟨hs, hv⟩ := h
    obtain ⟨h16, ho, hs2⟩ := hs
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.step_read, Memory.valid]
  all_goals first
    | exact hs2 (by assumption)
    | fits

private theorem realizes_collectNodeStep : Realizes .exact
    collectNodeStep (appendWords (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    collectNodeStepSafe (fun _ _ => 0) :=
  realizes_collectNodeStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Flat-parameter `shCollectCorrupted` (`d = ![itemBase, nodeBase, nodeStart, nodeCount, outBase,
outCount, fuel]`), scanning nodes `(nodeStart, nodeCount]` and returning the new `outCount`. -/
private def shCollectCorruptedRaw (d : Fin 7 → ℕ) : Memory.Prog ℕ := do
  let st ← iterate collectNodeStep (d 0, d 1, d 4, d 6) (d 3 - d 2) (d 2 + 1, d 5)
  pure st.2

/-- Native safety domain for `shCollectCorruptedRaw`. -/
private def shCollectCorruptedRawSafe (w : ℕ) (d : Fin 7 → ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d 2 ≤ d 3 ∧ Fits w (d 2 + 1) ∧
    iterationSafe collectNodeStep collectNodeStepSafe
      w (d 0, d 1, d 4, d 6) (d 3 - d 2) (d 2 + 1, d 5) s

private theorem realizes_shCollectCorruptedRaw : Realizes .exact
    shCollectCorruptedRaw (.refl _) (WordEncoding.encode (α := ℕ))
    shCollectCorruptedRawSafe (fun _ _ => 0) := by
  unfold shCollectCorruptedRaw
  realize [realizes_collectNodeStep]
  all_goals first
    | exact h.2.2.1
    | exact h.2.1
    | exact iterationSafe_imp h.2.2.2 (fun _ => rfl) (fun _ _ hs => hs)

/-- Starting node index bound `nodeStart` in `shCollectCorrupted` input
`(h, nodeStart, outBase, outCount, fuel)`. -/
private abbrev shCollectNodeStart (d : SHHandle × ℕ × ℕ × ℕ × ℕ) : ℕ := d.2.1

/-- Output array base `outBase` in `shCollectCorrupted` input. -/
private abbrev shCollectOutBase (d : SHHandle × ℕ × ℕ × ℕ × ℕ) : ℕ := d.2.2.1

/-- Initial output count `outCount` in `shCollectCorrupted` input. -/
private abbrev shCollectOutCount (d : SHHandle × ℕ × ℕ × ℕ × ℕ) : ℕ := d.2.2.2.1

/-- Item-scan fuel in `shCollectCorrupted` input. -/
private abbrev shCollectFuel (d : SHHandle × ℕ × ℕ × ℕ × ℕ) : ℕ := d.2.2.2.2

/-- Scan nodes allocated since `nodeStart` (`(nodeStart, h.nodeCount]`), appending corrupted
payload values `val` (`origKey < ckey`) to `outBase[outCount..]` and returning the new `outCount`
(`d = (h, nodeStart, outBase, outCount, fuel)`). -/
def shCollectCorrupted (d : SHHandle × ℕ × ℕ × ℕ × ℕ) : Memory.Prog ℕ :=
  shCollectCorruptedRaw ![d.1.itemBase, d.1.nodeBase, shCollectNodeStart d, d.1.nodeCount,
    shCollectOutBase d, shCollectOutCount d, shCollectFuel d]

/-- Native safety domain for `shCollectCorrupted`. -/
def shCollectCorruptedSafe (w : ℕ) (d : SHHandle × ℕ × ℕ × ℕ × ℕ)
    (s : Memory.State) : Prop :=
  shCollectCorruptedRawSafe w ![d.1.itemBase, d.1.nodeBase, shCollectNodeStart d, d.1.nodeCount,
    shCollectOutBase d, shCollectOutCount d, shCollectFuel d] s

/-- `shCollectCorrupted` admits a uniform `Realizes .exact` compilation certificate
(`work := 0`). -/
theorem realizes_shCollectCorrupted : Realizes .exact
    shCollectCorrupted (WordEncoding.encode (α := SHHandle × ℕ × ℕ × ℕ × ℕ))
    (WordEncoding.encode (α := ℕ)) shCollectCorruptedSafe (fun _ _ => 0) := by
  unfold shCollectCorrupted
  realize [realizes_shCollectCorruptedRaw]
  exact h

end Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
