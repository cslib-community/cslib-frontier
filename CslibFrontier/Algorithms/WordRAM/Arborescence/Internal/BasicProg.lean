/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.Workspace
public import CslibFrontier.Computability.WordRAM.Realization.Signed
public import CslibFrontier.Computability.WordRAM.Realization.Structure
import CslibFrontier.Tactic.Realize

/-!
# Low-level Word-RAM subroutines and `Realizes` certificates (internal)

Defines array copy/zero, argmin, minimum-cost incoming/outgoing parent selection, cycle
detection, and cycle-mask programs over `Memory.Prog`, together with their `Realizes .exact`
certificates.
-/

namespace Cslib.Algorithms.WordRAM.Arborescence.Internal

open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.WordRAM.Realization.Signed

/-! ### Subroutines and `Realizes` certificates -/

-- 1. `copyWordsProg` and `zeroWordsProg`

/-- Parameters for copying `len` contiguous words from `src` to `dst`. -/
public structure CopyArgs where
  /-- Source base address. -/
  src : ℕ
  /-- Destination base address. -/
  dst : ℕ
  /-- Number of words to copy. -/
  len : ℕ

/-- Word encoding of `CopyArgs` into 3 consecutive registers. -/
public word_enc_structure encCopyArgs : CopyArgs where
  src : wordWords, dst : wordWords, len : wordWords

private instance : WordEncoding CopyArgs := ⟨3, encCopyArgs⟩

/-- Single loop body copying word `i` from `src + i` to `dst + i`. -/
@[expose] public def copyStep (x : CopyArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let i := Prod.snd x
  let v ← Memory.read (env.src + i)
  Memory.write (env.dst + i) v
  pure (i + 1)

/-- Address-fit safety precondition for one step of `copyStep`. -/
public abbrev CopyStepSafe (w : ℕ) (x : CopyArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let i := Prod.snd x
  Fits w (env.src + i) ∧ Fits w (env.dst + i) ∧ Fits w (i + 1)

private theorem copyStep_realizes :
    Realizes .exact copyStep (appendWords encCopyArgs wordWords) wordWords
      CopyStepSafe (fun _ _ => 0) := by
  unfold copyStep
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2

/-- Loop copying `a.len` words from `a.src` to `a.dst`. -/
@[expose] public def copyWordsProg (a : CopyArgs) : Memory.Prog ℕ :=
  iterate copyStep a a.len 0

public theorem copyWordsProg_realizes :
    Realizes .exact copyWordsProg encCopyArgs wordWords
      (fun w a s => iterationSafe copyStep CopyStepSafe w a a.len 0 s)
      (fun _ _ => 0) := by
  unfold copyWordsProg
  realize [copyStep_realizes]
  exact h

/-- Parameters for zero-filling `len` contiguous words starting at `dst`. -/
public structure ZeroArgs where
  /-- Destination base address. -/
  dst : ℕ
  /-- Number of words to zero. -/
  len : ℕ

/-- Word encoding of `ZeroArgs` into 2 consecutive registers. -/
public word_enc_structure encZeroArgs : ZeroArgs where
  dst : wordWords, len : wordWords

private instance : WordEncoding ZeroArgs := ⟨2, encZeroArgs⟩

/-- Single loop body writing `0` to `dst + i`. -/
@[expose] public def zeroStep (x : ZeroArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let i := Prod.snd x
  Memory.write (env.dst + i) 0
  pure (i + 1)

/-- Address-fit safety precondition for one step of `zeroStep`. -/
public abbrev ZeroStepSafe (w : ℕ) (x : ZeroArgs × ℕ) (_ : Memory.State) : Prop :=
  Fits w ((Prod.fst x).dst + Prod.snd x) ∧ Fits w (Prod.snd x + 1)

private theorem zeroStep_realizes :
    Realizes .exact zeroStep (appendWords encZeroArgs wordWords) wordWords
      ZeroStepSafe (fun _ _ => 0) := by
  unfold zeroStep
  realize
  all_goals first | exact h.1 | exact h.2

/-- Loop zero-filling `a.len` words starting at `a.dst`. -/
@[expose] public def zeroWordsProg (a : ZeroArgs) : Memory.Prog ℕ :=
  iterate zeroStep a a.len 0

public theorem zeroWordsProg_realizes :
    Realizes .exact zeroWordsProg encZeroArgs wordWords
      (fun w a s => iterationSafe zeroStep ZeroStepSafe w a a.len 0 s)
      (fun _ _ => 0) := by
  unfold zeroWordsProg
  realize [zeroStep_realizes]
  exact h

-- 2. `argMinArrayProg`

/-- Parameters for finding the minimum-cost active index across length `n`. -/
public structure ArgMinArgs where
  /-- Array length and sentinel value for no active index. -/
  n : ℕ
  /-- Base address of the `0`/`1` candidate indicator array. -/
  predBase : ℕ
  /-- Base address of the `Signed.encode`-valued candidate cost array. -/
  costBase : ℕ

/-- Word encoding of `ArgMinArgs` into 3 consecutive registers. -/
public word_enc_structure encArgMinArgs : ArgMinArgs where
  n : wordWords, predBase : wordWords, costBase : wordWords

private instance : WordEncoding ArgMinArgs := ⟨3, encArgMinArgs⟩

/-- Loop state carried by `argMinStep`. -/
public structure ArgMinState where
  /-- Current index being inspected. -/
  idx : ℕ
  /-- Best active index seen so far (`n` if none). -/
  bestIdx : ℕ
  /-- Encoded cost of `bestIdx`. -/
  bestCost : ℕ

private word_enc_structure encArgMinState : ArgMinState where
  idx : wordWords, bestIdx : wordWords, bestCost : wordWords

private instance : WordEncoding ArgMinState := ⟨3, encArgMinState⟩

/-- Single step inspecting index `st.idx` and updating the running minimum. -/
@[expose] public def argMinStep (x : ArgMinArgs × ArgMinState) : Memory.Prog ArgMinState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let p ← Memory.read (env.predBase + st.idx)
  let c ← Memory.read (env.costBase + st.idx)
  if p = 1 then
    if st.bestIdx = env.n then
      pure ⟨st.idx + 1, st.idx, c⟩
    else if SignedLtWord c st.bestCost then
      pure ⟨st.idx + 1, st.idx, c⟩
    else
      pure ⟨st.idx + 1, st.bestIdx, st.bestCost⟩
  else
    pure ⟨st.idx + 1, st.bestIdx, st.bestCost⟩

/-- Address-fit safety precondition for one step of `argMinStep`. -/
public abbrev ArgMinStepSafe (w : ℕ) (x : ArgMinArgs × ArgMinState) (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 2 ∧ Fits w (env.predBase + st.idx) ∧ Fits w (env.costBase + st.idx) ∧ Fits w (st.idx + 1)

private theorem argMinStep_realizes :
    Realizes .exact argMinStep (appendWords encArgMinArgs encArgMinState) encArgMinState
      ArgMinStepSafe (fun _ _ => 0) := by
  unfold argMinStep
  realize
  all_goals
    first | omega | exact h.1.of_le (by omega) | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2

/-- Returns the minimum-cost active index in `[0, a.n)`, or `a.n` if none is active. -/
@[expose] public def argMinArrayProg (a : ArgMinArgs) : Memory.Prog ℕ := do
  let res ← iterate argMinStep a a.n ⟨0, a.n, 0⟩
  pure res.bestIdx

public theorem argMinArrayProg_realizes :
    Realizes .exact argMinArrayProg encArgMinArgs wordWords
      (fun w a s => iterationSafe argMinStep ArgMinStepSafe w a a.n ⟨0, a.n, 0⟩ s)
      (fun _ _ => 0) := by
  unfold argMinArrayProg
  realize [argMinStep_realizes]
  exact h

-- 3. `selectParentsProg`

/-- Parameters for scanning vertex `v`'s incoming arcs in row `v` into `candPred`/`candCost`. -/
public structure SelectRowArgs where
  /-- Matrix dimension (number of vertices). -/
  n : ℕ
  /-- Row index (target vertex). -/
  v : ℕ
  /-- Base address of the working `n × n` adjacency table. -/
  adjBase : ℕ
  /-- Base address of the working `n × n` cost table. -/
  costBase : ℕ
  /-- Output base address for candidate feasibility indicators (`n` words). -/
  predOut : ℕ
  /-- Output base address for candidate signed costs (`n` words). -/
  costOut : ℕ

private word_enc_structure encSelectRowArgs : SelectRowArgs where
  n : wordWords, v : wordWords, adjBase : wordWords, costBase : wordWords,
  predOut : wordWords, costOut : wordWords

private instance : WordEncoding SelectRowArgs := ⟨6, encSelectRowArgs⟩

/-- Writes candidate feasibility `(avw = 1 ∧ col ≠ v)` and cost for column `col` of row `v`. -/
@[expose] public def selectRowStep (x : SelectRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let col := Prod.snd x
  let avw ← Memory.read (env.adjBase + env.v * env.n + col)
  let cvw ← Memory.read (env.costBase + env.v * env.n + col)
  let pv := if avw = 1 ∧ col ≠ env.v then 1 else 0
  Memory.write (env.predOut + col) pv
  Memory.write (env.costOut + col) cvw
  pure (col + 1)

/-- Address-fit safety precondition for one step of `selectRowStep`. -/
public abbrev SelectRowStepSafe (w : ℕ) (x : SelectRowArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let col := Prod.snd x
  Fits w 1 ∧ Fits w (env.adjBase + env.v * env.n + col) ∧
    Fits w (env.costBase + env.v * env.n + col) ∧
    Fits w (env.predOut + col) ∧ Fits w (env.costOut + col) ∧ Fits w (col + 1)

private theorem selectRowStep_realizes :
    Realizes .exact selectRowStep (appendWords encSelectRowArgs wordWords) wordWords
      SelectRowStepSafe (fun _ _ => 0) := by
  unfold selectRowStep
  realize
  all_goals tauto

/-- Fills candidate feasibility and cost arrays for row `a.v`. -/
@[expose] public def fillSelectRowProg (a : SelectRowArgs) : Memory.Prog ℕ :=
  iterate selectRowStep a a.n 0

private theorem fillSelectRowProg_realizes :
    Realizes .exact fillSelectRowProg encSelectRowArgs wordWords
      (fun w a s => iterationSafe selectRowStep SelectRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillSelectRowProg
  realize [selectRowStep_realizes]
  exact h

/-- Parameters for greedy parent selection across all non-root vertices at frame `k`. -/
public structure SelectArgs where
  /-- Matrix dimension (number of vertices). -/
  n : ℕ
  /-- Designated root vertex index. -/
  r : ℕ
  /-- Workspace base address. -/
  ws : ℕ
  /-- Active contraction stack frame index. -/
  k : ℕ

/-- Word encoding of `SelectArgs` into 4 consecutive registers. -/
public word_enc_structure encSelectArgs : SelectArgs where
  n : wordWords, r : wordWords, ws : wordWords, k : wordWords

private instance : WordEncoding SelectArgs := ⟨4, encSelectArgs⟩

/-- Outer-loop state tracking current vertex `v` and feasibility flag `feas` (`1` iff feasible). -/
public structure SelectState where
  /-- Current vertex index being processed. -/
  v : ℕ
  /-- Feasibility flag (`1` if every vertex processed so far found a parent, `0` otherwise). -/
  feas : ℕ

private word_enc_structure encSelectState : SelectState where
  v : wordWords, feas : wordWords

private instance : WordEncoding SelectState := ⟨2, encSelectState⟩

/-- Selects the minimum-cost active non-self outgoing parent for vertex `st.v`. -/
@[expose] public def selectOuterStep (x : SelectArgs × SelectState) : Memory.Prog SelectState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let _ ← Memory.read 0
  let pBase := frameParentBase env.ws env.n env.k
  if st.v = env.r then
    Memory.write (pBase + st.v) env.r
    pure ⟨st.v + 1, st.feas⟩
  else
    let rowArgs : SelectRowArgs :=
      ⟨env.n, st.v, curAdjBase env.ws env.n, curCostBase env.ws env.n,
        candPredBase env.ws env.n, candCostBase env.ws env.n⟩
    let _ ← fillSelectRowProg rowArgs
    let best ← argMinArrayProg ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩
    if best < env.n then
      Memory.write (pBase + st.v) best
      pure ⟨st.v + 1, st.feas⟩
    else
      Memory.write (pBase + st.v) st.v
      pure ⟨st.v + 1, 0⟩

/-- Safety precondition for one vertex step of `selectOuterStep`. -/
public abbrev SelectOuterStepSafe (w : ℕ) (x : SelectArgs × SelectState)
    (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  let rowArgs : SelectRowArgs :=
    ⟨env.n, st.v, curAdjBase env.ws env.n, curCostBase env.ws env.n,
      candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  let s1 := (Memory.spec 0).clientState s (fillSelectRowProg rowArgs)
  st.v < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n ∧
    iterationSafe selectRowStep SelectRowStepSafe w rowArgs env.n 0 s ∧
    iterationSafe argMinStep ArgMinStepSafe w
      ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩ env.n ⟨0, env.n, 0⟩ s1

private theorem selectOuterStep_realizes :
    Realizes .exact selectOuterStep (appendWords encSelectArgs encSelectState) encSelectState
      SelectOuterStepSafe (fun _ _ => 0) := by
  unfold selectOuterStep
  realize [fillSelectRowProg_realizes, argMinArrayProg_realizes]
  all_goals
    obtain ⟨hv, hk, hws, hrow, harg⟩ := h
    first
    | exact hrow
    | exact harg
    | exact hws.of_le (by
        dsimp only [wsSize, frameParentBase, frameBase, curAdjBase, curCostBase,
          candPredBase, candCostBase]
        nlinarith)

/-- Populates frame `a.k`'s greedy parent table and returns `1` iff all non-root vertices have an
active outgoing edge. -/
@[expose] public def selectParentsProg (a : SelectArgs) : Memory.Prog ℕ := do
  let res ← iterate selectOuterStep a a.n ⟨0, 1⟩
  pure res.feas

public theorem selectParentsProg_realizes :
    Realizes .exact selectParentsProg encSelectArgs wordWords
      (fun w a s => Fits w 1 ∧
        iterationSafe selectOuterStep SelectOuterStepSafe w a a.n ⟨0, 1⟩ s)
      (fun _ _ => 0) := by
  unfold selectParentsProg
  realize [selectOuterStep_realizes]
  all_goals first | exact h.1 | exact h.2

-- 4. `hasCycleFromProg` and `findCycleProg`

/-- Parameters for checking whether vertex `start` lies on a directed cycle in `parentBase`. -/
public structure HasCycleArgs where
  /-- Number of vertices and maximum pointer-walk length. -/
  n : ℕ
  /-- Base address of the `n`-word parent array. -/
  parentBase : ℕ
  /-- Starting vertex to follow for `n` steps. -/
  start : ℕ

private word_enc_structure encHasCycleArgs : HasCycleArgs where
  n : wordWords, parentBase : wordWords, start : wordWords

private instance : WordEncoding HasCycleArgs := ⟨3, encHasCycleArgs⟩

/-- Loop state carried by `hasCycleStep`. -/
public structure HasCycleState where
  /-- Step counter along the walk. -/
  step : ℕ
  /-- Current vertex in the parent pointer walk. -/
  cur : ℕ
  /-- Indicator (`1` once the walk has returned to `start`). -/
  hit : ℕ

private word_enc_structure encHasCycleState : HasCycleState where
  step : wordWords, cur : wordWords, hit : wordWords

private instance : WordEncoding HasCycleState := ⟨3, encHasCycleState⟩

/-- Advances the parent pointer walk by one step and records if it returned to `env.start`. -/
@[expose] public def hasCycleStep (x : HasCycleArgs × HasCycleState) :
    Memory.Prog HasCycleState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let nxt ← Memory.read (env.parentBase + st.cur)
  if st.hit = 1 ∨ nxt = env.start then
    pure ⟨st.step + 1, nxt, 1⟩
  else
    pure ⟨st.step + 1, nxt, 0⟩

/-- Address-fit safety precondition for one step of `hasCycleStep`. -/
public abbrev HasCycleStepSafe (w : ℕ) (x : HasCycleArgs × HasCycleState)
    (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 1 ∧ Fits w (env.parentBase + st.cur) ∧ Fits w (st.step + 1)

private theorem hasCycleStep_realizes :
    Realizes .exact hasCycleStep (appendWords encHasCycleArgs encHasCycleState) encHasCycleState
      HasCycleStepSafe (fun _ _ => 0) := by
  unfold hasCycleStep
  realize
  all_goals tauto

/-- Walks `a.n` parent pointers from `a.start` and returns `1` iff `a.start` lies on a cycle. -/
@[expose] public def hasCycleFromProg (a : HasCycleArgs) : Memory.Prog ℕ := do
  let res ← iterate hasCycleStep a a.n ⟨0, a.start, 0⟩
  pure res.hit

private theorem hasCycleFromProg_realizes :
    Realizes .exact hasCycleFromProg encHasCycleArgs wordWords
      (fun w a s => iterationSafe hasCycleStep HasCycleStepSafe w a a.n ⟨0, a.start, 0⟩ s)
      (fun _ _ => 0) := by
  unfold hasCycleFromProg
  realize [hasCycleStep_realizes]
  exact h

/-- Parameters for finding the smallest cycle vertex in `parentBase` (excluding root `r`). -/
public structure FindCycleArgs where
  /-- Number of vertices and sentinel when acyclic. -/
  n : ℕ
  /-- Root vertex index (never tested). -/
  r : ℕ
  /-- Base address of the `n`-word parent array. -/
  parentBase : ℕ

/-- Word encoding of `FindCycleArgs` into 3 consecutive registers. -/
public word_enc_structure encFindCycleArgs : FindCycleArgs where
  n : wordWords, r : wordWords, parentBase : wordWords

private instance : WordEncoding FindCycleArgs := ⟨3, encFindCycleArgs⟩

/-- Outer-loop state tracking candidate vertex `v` and first cycle vertex `found`. -/
public structure FindCycleState where
  /-- Current vertex index being tested. -/
  v : ℕ
  /-- First cycle vertex found (`n` if none yet). -/
  found : ℕ

private word_enc_structure encFindCycleState : FindCycleState where
  v : wordWords, found : wordWords

private instance : WordEncoding FindCycleState := ⟨2, encFindCycleState⟩

/-- Tests `st.v ≠ env.r` for cycle membership unless an earlier cycle vertex was already found. -/
@[expose] public def findCycleOuterStep (x : FindCycleArgs × FindCycleState) :
    Memory.Prog FindCycleState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let _ ← Memory.read 0
  if st.found < env.n then
    pure ⟨st.v + 1, st.found⟩
  else if st.v = env.r then
    pure ⟨st.v + 1, env.n⟩
  else
    let hit ← hasCycleFromProg ⟨env.n, env.parentBase, st.v⟩
    if hit = 1 then
      pure ⟨st.v + 1, st.v⟩
    else
      pure ⟨st.v + 1, env.n⟩

/-- Safety precondition for one vertex test in `findCycleOuterStep`. -/
public abbrev FindCycleOuterStepSafe (w : ℕ) (x : FindCycleArgs × FindCycleState)
    (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 1 ∧ Fits w (st.v + 1) ∧
    iterationSafe hasCycleStep HasCycleStepSafe w ⟨env.n, env.parentBase, st.v⟩ env.n
      ⟨0, st.v, 0⟩ s

private theorem findCycleOuterStep_realizes :
    Realizes .exact findCycleOuterStep (appendWords encFindCycleArgs encFindCycleState)
      encFindCycleState FindCycleOuterStepSafe (fun _ _ => 0) := by
  unfold findCycleOuterStep
  realize [hasCycleFromProg_realizes]
  all_goals tauto

/-- Returns the least non-root vertex lying on a cycle, or `a.n` if the parent map is acyclic. -/
@[expose] public def findCycleProg (a : FindCycleArgs) : Memory.Prog ℕ := do
  let res ← iterate findCycleOuterStep a a.n ⟨0, a.n⟩
  pure res.found

public theorem findCycleProg_realizes :
    Realizes .exact findCycleProg encFindCycleArgs wordWords
      (fun w a s => iterationSafe findCycleOuterStep FindCycleOuterStepSafe w a a.n ⟨0, a.n⟩ s)
      (fun _ _ => 0) := by
  unfold findCycleProg
  realize [findCycleOuterStep_realizes]
  exact h

-- 5. `cycleMaskProg`

/-- Parameters for marking all vertices of the cycle containing `x0` into `maskBase`. -/
public structure CycleMaskArgs where
  /-- Number of vertices and walk bound. -/
  n : ℕ
  /-- Base address of the `n`-word parent array. -/
  parentBase : ℕ
  /-- Output base address of the `n`-word `0`/`1` cycle-membership mask array. -/
  maskBase : ℕ
  /-- Representative vertex known to lie on the target cycle. -/
  x0 : ℕ

/-- Word encoding of `CycleMaskArgs` into 4 consecutive registers. -/
public word_enc_structure encCycleMaskArgs : CycleMaskArgs where
  n : wordWords, parentBase : wordWords, maskBase : wordWords, x0 : wordWords

private instance : WordEncoding CycleMaskArgs := ⟨4, encCycleMaskArgs⟩

/-- Loop state carried by `cycleMaskStep`. -/
public structure CycleMaskState where
  /-- Step counter along the cycle walk. -/
  step : ℕ
  /-- Current cycle vertex being marked. -/
  cur : ℕ

private word_enc_structure encCycleMaskState : CycleMaskState where
  step : wordWords, cur : wordWords

private instance : WordEncoding CycleMaskState := ⟨2, encCycleMaskState⟩

/-- Marks `st.cur` in `maskBase` and steps to its parent. -/
@[expose] public def cycleMaskStep (x : CycleMaskArgs × CycleMaskState) :
    Memory.Prog CycleMaskState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let nxt ← Memory.read (env.parentBase + st.cur)
  Memory.write (env.maskBase + st.cur) 1
  pure ⟨st.step + 1, nxt⟩

/-- Address-fit safety precondition for one step of `cycleMaskStep`. -/
public abbrev CycleMaskStepSafe (w : ℕ) (x : CycleMaskArgs × CycleMaskState)
    (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 1 ∧ Fits w (env.parentBase + st.cur) ∧
    Fits w (env.maskBase + st.cur) ∧ Fits w (st.step + 1)

private theorem cycleMaskStep_realizes :
    Realizes .exact cycleMaskStep (appendWords encCycleMaskArgs encCycleMaskState)
      encCycleMaskState CycleMaskStepSafe (fun _ _ => 0) := by
  unfold cycleMaskStep
  realize
  all_goals tauto

/-- Walks `a.n` steps from `a.x0`, setting `maskBase[v] := 1` along the cycle. -/
@[expose] public def cycleMaskLoopProg (a : CycleMaskArgs) : Memory.Prog ℕ := do
  let res ← iterate cycleMaskStep a a.n ⟨0, a.x0⟩
  pure res.step

private theorem cycleMaskLoopProg_realizes :
    Realizes .exact cycleMaskLoopProg encCycleMaskArgs wordWords
      (fun w a s => iterationSafe cycleMaskStep CycleMaskStepSafe w a a.n ⟨0, a.x0⟩ s)
      (fun _ _ => 0) := by
  unfold cycleMaskLoopProg
  realize [cycleMaskStep_realizes]
  exact h

/-- Zeros `a.maskBase[0..a.n)` and marks every vertex on `a.x0`'s cycle with `1`. -/
@[expose] public def cycleMaskProg (a : CycleMaskArgs) : Memory.Prog ℕ := do
  let _ ← zeroWordsProg ⟨a.maskBase, a.n⟩
  cycleMaskLoopProg a

public theorem cycleMaskProg_realizes :
    Realizes .exact cycleMaskProg encCycleMaskArgs wordWords
      (fun w a s =>
        let s1 := (Memory.spec 0).clientState s (zeroWordsProg ⟨a.maskBase, a.n⟩)
        iterationSafe zeroStep ZeroStepSafe w ⟨a.maskBase, a.n⟩ a.n 0 s ∧
          iterationSafe cycleMaskStep CycleMaskStepSafe w a a.n ⟨0, a.x0⟩ s1)
      (fun _ _ => 0) := by
  unfold cycleMaskProg
  realize [zeroWordsProg_realizes, cycleMaskLoopProg_realizes]
  all_goals first | exact h.1 | exact h.2

end Cslib.Algorithms.WordRAM.Arborescence.Internal
