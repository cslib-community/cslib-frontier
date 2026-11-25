/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.Range
import CslibFrontier.Tactic.Realize

/-!
# Split-network capacity, residual BFS, and minimum-separator programs

This module defines the `Memory.Prog` subroutines for the `(2n + 2)`-vertex unit-capacity split
network (`readSplitCap`, `readResCap`, `bfsProg`, `pushUnitStep`, `augRoundStep`,
`extractSepStep`, `minSepProg`) and certifies exact-basis realization (`minSepProg_realizes`).

## Main definitions

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.readSplitCap`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.readResCap`: capacity and residual-capacity queries.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.bfsProg`: layered residual-graph BFS.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.minSepProg`: unit-capacity max-flow separator.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.minSepProg_realizes`: exact-basis realization of
  `minSepProg`.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.preservesAt_minSepProg`: frame preservation below
  `flowBase n`.
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write StateTransitionSpec.clientState_map

/-! ### Split-network capacity, residual capacity, BFS, and unit augmentation -/

/-- Graph dimension `n` in a `(((n, m), x), y)` split-network query tuple. -/
abbrev SplitNetArgs.n (d : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.1

/-- Subgraph prefix size `m` in a `(((n, m), x), y)` split-network query tuple. -/
abbrev SplitNetArgs.m (d : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.2

/-- First query node or BFS layer in a `(((n, m), u), v)` tuple. -/
abbrev SplitNetArgs.arg1 (d : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := d.1.2

/-- Graph dimension `n` in a `((((n, m), layer), u), v)` BFS inner-loop tuple. -/
abbrev BfsInnerArgs.n (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.1.1

/-- Subgraph prefix size `m` in a `((((n, m), layer), u), v)` BFS inner-loop tuple. -/
abbrev BfsInnerArgs.m (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.1.2

/-- Current BFS distance `layer` in a `((((n, m), layer), u), v)` tuple. -/
abbrev BfsInnerArgs.layer (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.2

/-- Source vertex `u` in a `((((n, m), layer), u), v)` BFS inner-loop tuple. -/
abbrev BfsInnerArgs.u (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := d.1.2

/-- Query the split-network capacity `c(x, y)` for `d = (((n, m), x), y)`. -/
@[expose] def readSplitCap (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := SplitNetArgs.n d
  let m := SplitNetArgs.m d
  let x := SplitNetArgs.arg1 d
  let y := d.2
  let _ ← Memory.read 0
  if x = 0 then
    if 2 ≤ y ∧ y < n + 2 then
      let a ← Memory.read (keepBase n + (y - 2))
      if a = 1 then pure (n + 1) else pure 0
    else pure 0
  else if y = 1 then
    if n + 2 ≤ x ∧ x < splitCount n then
      let b ← Memory.read (flipBase n + (x - (n + 2)))
      if b = 1 then pure (n + 1) else pure 0
    else pure 0
  else if 2 ≤ x ∧ x < n + 2 then
    if y = x + n then
      let z ← Memory.read (wBase n + (x - 2))
      if z = 0 then pure 1 else pure 0
    else pure 0
  else if n + 2 ≤ x ∧ x < splitCount n ∧ 2 ≤ y ∧ y < n + 2 then
    let u := x - (n + 2)
    let v := y - 2
    if u < m ∧ v < m then
      let e ← Memory.read (3 + u * n + v)
      if e = 1 then pure (n + 1) else pure 0
    else pure 0
  else pure 0

private theorem readSplitCap_realizes :
    Realizes .exact readSplitCap (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.1.2 < splitCount d.1.1.1 ∧
        d.2 < splitCount d.1.1.1)
      (fun _ _ => 0) := by
  unfold readSplitCap
  realize
  all_goals
    obtain ⟨hw, hx, hy⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, splitCount, keepBase, flipBase, wBase,
      SplitNetArgs.n, SplitNetArgs.m, SplitNetArgs.arg1] at *
    first
    | omega
    | (apply hw.of_le
       first
       | omega
       | (have hu : d.1.2 - (d.1.1.1 + 2) < d.1.1.1 := by omega
          have hmul : (d.1.2 - (d.1.1.1 + 2)) * d.1.1.1 < d.1.1.1 * d.1.1.1 :=
            Nat.mul_lt_mul_of_pos_right hu (by omega)
          omega))

theorem clientState_readSplitCap (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readSplitCap d) = s := by
  unfold readSplitCap
  rw [clientState_bind_read]
  dsimp only
  split_ifs <;> try rfl
  all_goals rw [clientState_bind_read]; split_ifs <;> rfl

private theorem preservesAt_readSplitCap (a : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    PreservesAt a (readSplitCap d) := fun s => by
  rw [clientState_readSplitCap]

/-- Query the residual capacity of arc `(x, y)` in the split network. -/
@[expose] def readResCap (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := SplitNetArgs.n d
  let x := SplitNetArgs.arg1 d
  let y := d.2
  let cap ← readSplitCap d
  let M := splitCount n
  let fxy ← Memory.read (flowBase n + x * M + y)
  let fyx ← Memory.read (flowBase n + y * M + x)
  if cap ≤ n + 1 ∧ fxy ≤ cap ∧ fyx ≤ n + 1 then
    pure ((cap - fxy) + fyx)
  else pure 0

private theorem readResCap_realizes :
    Realizes .exact readResCap (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.1.2 < splitCount d.1.1.1 ∧
        d.2 < splitCount d.1.1.1)
      (fun _ _ => 0) := by
  unfold readResCap
  realize [readSplitCap_realizes]
  all_goals
    obtain ⟨hw, hx, hy⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, flowBase, splitCount,
      SplitNetArgs.n, SplitNetArgs.arg1] at *
    first | omega | (apply hw.of_le; first | omega | nlinarith)

private theorem preservesAt_readResCap (a : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    PreservesAt a (readResCap d) := by
  unfold readResCap
  refine preservesAt_bind (preservesAt_readSplitCap a d) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  exact preservesAt_ite _ (preservesAt_pure _ _) (preservesAt_pure _ _)

/-- Inner BFS neighbor-relaxation step scanning target node `v`. -/
@[expose] def bfsInnerStep (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := BfsInnerArgs.n d
  let m := BfsInnerArgs.m d
  let layer := BfsInnerArgs.layer d
  let u := BfsInnerArgs.u d
  let v := d.2
  let M := splitCount n
  let dv ← Memory.read (distBase n + v)
  let rc ← readResCap (((n, m), u), v)
  if dv = M ∧ 0 < rc then
    Memory.write (distBase n + v) (layer + 1)
    Memory.write (parBase n + v) u
    pure (v + 1)
  else
    pure (v + 1)

private theorem bfsInnerStep_realizes :
    Realizes .exact bfsInnerStep (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1.1) ∧ d.1.1.2 < splitCount d.1.1.1.1 ∧
        d.1.2 < splitCount d.1.1.1.1 ∧ d.2 < splitCount d.1.1.1.1)
      (fun _ _ => 0) := by
  unfold bfsInnerStep
  realize [readResCap_realizes]
  all_goals
    obtain ⟨hw, hl, hu, hv⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, distBase, parBase, flowBase, splitCount,
      BfsInnerArgs.n, BfsInnerArgs.m, BfsInnerArgs.layer, BfsInnerArgs.u] at *
    have hsq := splitCount_sq d.1.1.1.1
    first | omega | (apply hw.of_le; omega)

theorem clientResult_bfsInnerStep (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bfsInnerStep d) = d.2 + 1 := by
  unfold bfsInnerStep
  rw [clientResult_bind_read, clientResult_bind]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

/-- Middle BFS frontier scan checking node `u` at distance `layer`. -/
@[expose] def bfsMidStep (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := SplitNetArgs.n d
  let m := SplitNetArgs.m d
  let layer := SplitNetArgs.arg1 d
  let u := d.2
  let du ← Memory.read (distBase n + u)
  if du = layer then
    let _ ← iterate bfsInnerStep (((n, m), layer), u) (splitCount n) 0
    pure (u + 1)
  else
    pure (u + 1)

private theorem bfsMidStep_realizes :
    Realizes .exact bfsMidStep (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.1.2 < splitCount d.1.1.1 ∧
        d.2 < splitCount d.1.1.1)
      (fun _ _ => 0) := by
  unfold bfsMidStep
  realize [bfsInnerStep_realizes]
  all_goals
    obtain ⟨hw, hl, hu⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, distBase, flowBase, splitCount,
      SplitNetArgs.n, SplitNetArgs.m, SplitNetArgs.arg1] at *
    have hsq := splitCount_sq d.1.1.1
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (v : ℕ) _ => v + rem = splitCount d.1.1.1) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp -failIfUnchanged only [octWorkspace, splitCount] at *
  refine ⟨⟨hw, hl, hu, by omega⟩, ?_⟩
  rw [clientResult_bfsInnerStep]
  omega

theorem clientResult_bfsMidStep (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bfsMidStep d) = d.2 + 1 := by
  unfold bfsMidStep
  rw [clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

/-- Outer BFS layer step advancing from `layer` to `layer + 1`. -/
@[expose] def bfsLayerStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := GraphStepArgs.n d
  let m := GraphStepArgs.m d
  let layer := d.2
  let _ ← Memory.read 0
  let _ ← iterate bfsMidStep ((n, m), layer) (splitCount n) 0
  pure (layer + 1)

private theorem bfsLayerStep_realizes :
    Realizes .exact bfsLayerStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1) ∧ d.2 < splitCount d.1.1)
      (fun _ _ => 0) := by
  unfold bfsLayerStep
  realize [bfsMidStep_realizes]
  all_goals
    obtain ⟨hw, hl⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, splitCount, GraphStepArgs.n, GraphStepArgs.m] at *
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (u : ℕ) _ => u + rem = splitCount d.1.1) ?_ (Nat.zero_add _)
  intro rem u t hsum
  dsimp -failIfUnchanged only [octWorkspace, splitCount] at *
  refine ⟨⟨hw, hl, by omega⟩, ?_⟩
  rw [clientResult_bfsMidStep]
  omega

/-- Layered residual-graph BFS computing shortest distances and parents from source `0`. -/
@[expose] def bfsProg (d : ℕ × ℕ) : Memory.Prog Unit := do
  let n := d.1
  let M := splitCount n
  fillRange ((distBase n, M), M)
  Memory.write (distBase n) 0
  Memory.write (parBase n) 0
  let _ ← iterate bfsLayerStep d (M - 1) 0
  pure ()

private theorem bfsProg_realizes :
    Realizes .exact bfsProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => Fits w (octWorkspace d.1)) (fun _ _ => 0) := by
  unfold bfsProg
  realize [fillRange_realizes, bfsLayerStep_realizes]
  all_goals
    dsimp -failIfUnchanged only [octWorkspace, parBase, distBase, flowBase, splitCount] at *
    have hsq := splitCount_sq d.1
    try omega
    try (apply h.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (layer : ℕ) _ => layer + rem = splitCount d.1 - 1) ?_ (Nat.zero_add _)
  intro rem layer t hsum
  dsimp -failIfUnchanged only [bfsLayerStep, octWorkspace, splitCount] at *
  refine ⟨⟨h, by omega⟩, ?_⟩
  simp only [client_simps]
  omega

theorem preservesAt_bfsProg {a : ℕ} {d : ℕ × ℕ}
    (ha : a < distBase d.1 ∨ parBase d.1 + splitCount d.1 ≤ a) :
    PreservesAt a (bfsProg d) := by
  have h1 : a < distBase d.1 ∨ distBase d.1 + splitCount d.1 ≤ a := by
    dsimp only [parBase] at ha; omega
  unfold bfsProg
  refine preservesAt_bind (preservesAt_fillRange h1) fun _ => ?_
  refine preservesAt_bind (preservesAt_write _ (by dsimp only [parBase, splitCount] at ha ⊢; omega))
    fun _ => ?_
  refine preservesAt_bind (preservesAt_write _ (by dsimp only [parBase, splitCount] at ha ⊢; omega))
    fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate_nat fun layer _ => ⟨?_, fun s => ?_⟩)
    fun _ => preservesAt_pure _ _
  · unfold bfsLayerStep
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_bind (preservesAt_iterate_nat fun u _ => ⟨?_, fun s => ?_⟩)
      fun _ => preservesAt_pure _ _
    · unfold bfsMidStep
      refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
      refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
      refine preservesAt_bind (preservesAt_iterate_nat fun v hv => ⟨?_, fun s => ?_⟩)
        fun _ => preservesAt_pure _ _
      · unfold bfsInnerStep
        refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
        refine preservesAt_bind (preservesAt_readResCap a _) fun _ => ?_
        refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
        refine preservesAt_bind (preservesAt_write _
          (by dsimp only [parBase, distBase, splitCount,
            BfsInnerArgs.n, SplitNetArgs.n, GraphStepArgs.n] at ha hv ⊢; omega)) fun _ => ?_
        refine preservesAt_bind (preservesAt_write _
          (by dsimp only [parBase, distBase, splitCount,
            BfsInnerArgs.n, SplitNetArgs.n, GraphStepArgs.n] at ha hv ⊢; omega))
          fun _ => preservesAt_pure _ _
      · exact clientResult_bfsInnerStep _ s
    · exact clientResult_bfsMidStep _ s
  · unfold bfsLayerStep
    simp only [client_simps]

/-- Walk one parent edge back from `cur` and push one unit of flow. -/
@[expose] def pushUnitStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let cur := d.2
  let M := splitCount n
  let _ ← Memory.read 0
  if cur < M then
    let u ← Memory.read (parBase n + cur)
    if u < M then
      let f_rev ← Memory.read (flowBase n + cur * M + u)
      if 0 < f_rev then
        Memory.write (flowBase n + cur * M + u) (f_rev - 1)
        pure u
      else
        let f_fwd ← Memory.read (flowBase n + u * M + cur)
        if f_fwd ≤ n then
          Memory.write (flowBase n + u * M + cur) (f_fwd + 1)
          pure u
        else pure u
    else pure 0
  else pure 0

private theorem pushUnitStep_realizes :
    Realizes .exact pushUnitStep (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1)) (fun _ _ => 0) := by
  unfold pushUnitStep
  realize
  all_goals
    dsimp -failIfUnchanged only [octWorkspace, parBase, distBase, flowBase, splitCount] at *
    have hsq := splitCount_sq d.1
    first | omega | (apply h.of_le; first | omega | nlinarith)

theorem preservesAt_pushUnitStep {a : ℕ} {d : ℕ × ℕ}
    (ha : a < flowBase d.1 ∨ distBase d.1 ≤ a) :
    PreservesAt a (pushUnitStep d) := by
  unfold pushUnitStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  by_cases hcur : d.2 < splitCount d.1
  · rw [ite_eq_left hcur]
    refine preservesAt_bind (preservesAt_read _ _) fun u => ?_
    by_cases hu : u < splitCount d.1
    · rw [ite_eq_left hu]
      refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
      refine preservesAt_ite _ ?_ ?_
      · refine preservesAt_bind (preservesAt_write _ ?_) fun _ => preservesAt_pure _ _
        dsimp only [distBase] at ha
        have : d.2 * splitCount d.1 + u < splitCount d.1 * splitCount d.1 := by nlinarith
        omega
      · refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
        refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
        refine preservesAt_bind (preservesAt_write _ ?_) fun _ => preservesAt_pure _ _
        dsimp only [distBase] at ha
        have : u * splitCount d.1 + d.2 < splitCount d.1 * splitCount d.1 := by nlinarith
        omega
    · rw [ite_eq_right hu]; exact preservesAt_pure _ _
  · rw [ite_eq_right hcur]; exact preservesAt_pure _ _

/-- One Edmonds-Karp unit-augmentation round on the vertex-split network. -/
@[expose] def augRoundStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := GraphStepArgs.n d
  let m := GraphStepArgs.m d
  bfsProg (n, m)
  let M := splitCount n
  let d1 ← Memory.read (distBase n + 1)
  if d1 < M then
    let _ ← iterate pushUnitStep n d1 1
    pure (d.2 + 1)
  else
    pure (d.2 + 1)

private theorem augRoundStep_realizes :
    Realizes .exact augRoundStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1) ∧ d.2 < d.1.1) (fun _ _ => 0) := by
  unfold augRoundStep
  realize [bfsProg_realizes, pushUnitStep_realizes]
  all_goals
    obtain ⟨hw, hr⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, distBase, flowBase, splitCount,
      GraphStepArgs.n, GraphStepArgs.m] at *
    have hsq := splitCount_sq d.1.1
    try exact hw
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _ (fun _ (_ : ℕ) _ => True) ?_ trivial
  intro _ _ _ _
  exact ⟨hw, trivial⟩

private theorem clientResult_augRoundStep (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (augRoundStep d) = d.2 + 1 := by
  unfold augRoundStep
  rw [clientResult_bind, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

/-- Extract one vertex into `sepOutBase` when its split edge crosses the BFS cut. -/
@[expose] def extractSepStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1
  let v := LoopAccArgs.idx d
  let count := LoopAccArgs.acc d
  let M := splitCount n
  let z ← Memory.read (wBase n + v)
  let din ← Memory.read (distBase n + (v + 2))
  let dout ← Memory.read (distBase n + (v + n + 2))
  if z = 0 ∧ din < M ∧ dout = M then
    Memory.write (sepOutBase n + v) 1
    pure (v + 1, count + 1)
  else
    Memory.write (sepOutBase n + v) 0
    pure (v + 1, count)

private theorem extractSepStep_realizes :
    Realizes .exact extractSepStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2.1 < d.1 ∧ d.2.2 ≤ d.2.1)
      (fun _ _ => 0) := by
  unfold extractSepStep
  realize
  all_goals
    obtain ⟨hw, hv, hc⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wBase, distBase, sepOutBase, parBase, flowBase,
      splitCount, LoopAccArgs.idx, LoopAccArgs.acc] at *
    have hsq := splitCount_sq d.1
    first | omega | (apply hw.of_le; omega)

theorem clientResult_extractSepStep (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    let res := (Memory.spec 0).clientResult s (extractSepStep d)
    res.1 = LoopAccArgs.idx d + 1 ∧ res.2 ≤ LoopAccArgs.acc d + 1 := by
  unfold extractSepStep
  rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure] <;> exact ⟨trivial, by omega⟩

/-- Minimum vertex-separator solver on the `(2n + 2)`-vertex split network. -/
@[expose] def minSepProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let M := splitCount n
  fillRange ((flowBase n, 0), M * M)
  let _ ← iterate augRoundStep d n 0
  bfsProg d
  let res ← iterate extractSepStep n n (0, 0)
  pure res.2

theorem minSepProg_realizes :
    Realizes .exact minSepProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1)) (fun _ _ => 0) := by
  unfold minSepProg
  realize [fillRange_realizes, augRoundStep_realizes, bfsProg_realizes, extractSepStep_realizes]
  all_goals
    dsimp -failIfUnchanged only [octWorkspace, flowBase, splitCount] at *
    have hsq := splitCount_sq d.1
    try exact h
    try (apply h.of_le; omega)
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (r : ℕ) _ => r + rem = d.1) ?_ (Nat.zero_add _)
    intro rem r t hsum
    dsimp only
    refine ⟨⟨h, by omega⟩, ?_⟩
    rw [clientResult_augRoundStep]
    omega
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (vc : ℕ × ℕ) _ => vc.1 + rem = d.1 ∧ vc.2 ≤ vc.1) ?_ ⟨Nat.zero_add _, le_rfl⟩
    intro rem vc t ⟨hsum, hc⟩
    dsimp only
    refine ⟨⟨h, by omega, hc⟩, ?_⟩
    obtain ⟨h1, h2⟩ := clientResult_extractSepStep (d.1, vc) t
    dsimp only [LoopAccArgs.idx, LoopAccArgs.acc] at h1 h2
    exact ⟨by omega, by omega⟩

theorem preservesAt_minSepProg {a : ℕ} {d : ℕ × ℕ} (ha : a < flowBase d.1) :
    PreservesAt a (minSepProg d) := by
  unfold minSepProg
  refine preservesAt_bind (preservesAt_fillRange (Or.inl ha)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun r => ?_) _ _) fun _ => ?_
  · unfold augRoundStep
    refine preservesAt_bind (preservesAt_bfsProg (Or.inl (by
      dsimp only [distBase, GraphStepArgs.n]; omega)))
      fun _ => ?_
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
    refine preservesAt_bind
      (preservesAt_iterate (fun cur => preservesAt_pushUnitStep (Or.inl ha)) _ _)
      fun _ => preservesAt_pure _ _
  · refine preservesAt_bind (preservesAt_bfsProg (Or.inl (by dsimp only [distBase]; omega)))
      fun _ => ?_
    refine preservesAt_bind (preservesAt_iterate (fun vc => ?_) _ _) fun _ => preservesAt_pure _ _
    unfold extractSepStep
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_ite _ ?_ ?_ <;>
      exact preservesAt_bind
        (preservesAt_write _
          (by dsimp only [sepOutBase, parBase, distBase, flowBase] at ha ⊢; omega))
        fun _ => preservesAt_pure _ _

end Cslib.Algorithms.WordRAM.OddCycleTransversal
