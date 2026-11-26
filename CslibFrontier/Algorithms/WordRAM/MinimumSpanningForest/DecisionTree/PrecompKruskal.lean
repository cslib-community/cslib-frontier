/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.Layout
public import CslibFrontier.Computability.WordRAM.Realization.ArrayOps
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.WramOmega
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith

/-!
# Bitmask Decoding, Enumeration Primitives, and In-Memory Kruskal for DT Precomputation

Implements and verifies the Word-RAM subroutines supporting optimal MSF decision-tree
precomputation ([PettieRamachandran2002], Section 4.1 and Section 5.1).

## Main definitions

* `DTPairsArgs`, `DTPowArgs`, `DTDecodeMaskArgs`, `DTKruskalProgArgs`: `word_enc_structure`
  argument bundles for the precomputation primitives.
* `dtFillAllPairsProg`: enumerates all `v.choose 2` unordered pairs `0 ≤ a < b < v` into
  `(arrA, arrB)`.
* `dtFillPowProg`: fills `powArr[0..len]` with `base ^ 0 .. base ^ len`.
* `dtDecodeMaskProg`: decodes a `maxE`-bit graph mask into edge endpoints `(edgeU, edgeV)` and
  pair indices `edgePair`.
* `dtKruskalMaskProg`: executes in-memory Kruskal over `orderArr[0..e-1]` and returns the
  `maskOfFinset (Cslib.Multigraph.msf ends p Finset.univ)` bitmask.

## Main results

* `dtFillAllPairsProg_spec`, `realizes_dtFillAllPairsProg`: pair enumeration specification and
  `work = 0` Word-RAM realization.
* `dtFillPowProg_spec`, `realizes_dtFillPowProg`: power-table specification and `work = 0`
  Word-RAM realization.
* `dtDecodeMaskProg_spec`, `realizes_dtDecodeMaskProg`: bitmask decoding specification and
  `work = 0` Word-RAM realization.
* `dtKruskalMaskProg_spec`, `realizes_dtKruskalMaskProg`: in-memory Kruskal specification against
  `Cslib.Multigraph.msf` and `work = 0` Word-RAM realization.

## References

* [Pettie and Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), 2002][PettieRamachandran2002]
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.DataStructure
open Cslib.Query.MinimumSpanningForest
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ## Section 1: Public Argument Structures -/

/-- Arguments for `dtFillAllPairsProg`. -/
structure DTPairsArgs where
  /-- Base of first-endpoint array. -/
  arrA : ℕ
  /-- Base of second-endpoint array. -/
  arrB : ℕ
  /-- Vertex count `numV`. -/
  numV : ℕ
  deriving DecidableEq

/-- Three-word encoding for `DTPairsArgs`. -/
word_enc_structure dtPairsArgsWords : DTPairsArgs where
  arrA : wordWords,
  arrB : wordWords,
  numV : wordWords

instance : WordEncoding DTPairsArgs := ⟨3, dtPairsArgsWords⟩

/-- Arguments for `dtFillPowProg`. -/
structure DTPowArgs where
  /-- Base of powers array. -/
  powArr : ℕ
  /-- Base of exponentiation. -/
  base : ℕ
  /-- Maximum exponent `len` (`len + 1` entries written). -/
  len : ℕ
  deriving DecidableEq

/-- Three-word encoding for `DTPowArgs`. -/
word_enc_structure dtPowArgsWords : DTPowArgs where
  powArr : wordWords,
  base : wordWords,
  len : wordWords

instance : WordEncoding DTPowArgs := ⟨3, dtPowArgsWords⟩

/-- Arguments for `dtDecodeMaskProg`. -/
structure DTDecodeMaskArgs where
  /-- Base of `allPairs r0` first endpoints. -/
  r0PairA : ℕ
  /-- Base of `allPairs r0` second endpoints. -/
  r0PairB : ℕ
  /-- Base of decoded edge first endpoints. -/
  edgeU : ℕ
  /-- Base of decoded edge second endpoints. -/
  edgeV : ℕ
  /-- Base of decoded edge `pairIdx` values. -/
  edgePair : ℕ
  /-- Graph bitmask. -/
  mask : ℕ
  /-- Number of unordered pairs `r0.choose 2`. -/
  maxE : ℕ
  deriving DecidableEq

/-- Seven-word encoding for `DTDecodeMaskArgs`. -/
word_enc_structure dtDecodeMaskArgsWords : DTDecodeMaskArgs where
  r0PairA : wordWords,
  r0PairB : wordWords,
  edgeU : wordWords,
  edgeV : wordWords,
  edgePair : wordWords,
  mask : wordWords,
  maxE : wordWords

instance : WordEncoding DTDecodeMaskArgs := ⟨7, dtDecodeMaskArgsWords⟩

/-- Arguments for `dtKruskalMaskProg`. -/
structure DTKruskalProgArgs where
  /-- Outer vertex bound `r0`. -/
  r0 : ℕ
  /-- Edge count `e`. -/
  e : ℕ
  /-- Base of `edgeU`. -/
  edgeU : ℕ
  /-- Base of `edgeV`. -/
  edgeV : ℕ
  /-- Base of edge ordering `orderArr`. -/
  orderArr : ℕ
  /-- Base of component scratch array `compArr`. -/
  compArr : ℕ
  deriving DecidableEq

/-- Six-word encoding for `DTKruskalProgArgs`. -/
word_enc_structure dtKruskalProgArgsWords : DTKruskalProgArgs where
  r0 : wordWords,
  e : wordWords,
  edgeU : wordWords,
  edgeV : wordWords,
  orderArr : wordWords,
  compArr : wordWords

instance : WordEncoding DTKruskalProgArgs := ⟨6, dtKruskalProgArgsWords⟩

/-! ## Section 2: Private Step Programs and Pure Arithmetic Helpers -/

private theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ]
  simp [Nat.add_comm]

private theorem testBit_eq_decide_shift_and (m j : ℕ) :
    ((m >>> j) &&& 1 = 1) ↔ m.testBit j = true := by
  rw [Nat.and_one_is_mod, Nat.testBit, Nat.and_comm 1 (m >>> j), Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (m >>> j) with h | h <;> simp [h]

private theorem testBit_or_one_shiftLeft (m k b : ℕ) :
    (m ||| (1 <<< k)).testBit b = (m.testBit b || decide (b = k)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases hbk : b = k
  · subst hbk; simp
  · have hkb : k ≠ b := Ne.symm hbk
    simp [hbk, hkb]

private structure DTIdxPair where
  idx : ℕ
  acc : ℕ
  deriving DecidableEq

private word_enc_structure dtIdxPairWords : DTIdxPair where
  idx : wordWords,
  acc : wordWords

private instance : WordEncoding DTIdxPair := ⟨2, dtIdxPairWords⟩

private structure DTPairsInnerEnv where
  arrA : ℕ
  arrB : ℕ
  b : ℕ
  deriving DecidableEq

private word_enc_structure dtPairsInnerEnvWords : DTPairsInnerEnv where
  arrA : wordWords,
  arrB : wordWords,
  b : wordWords

private instance : WordEncoding DTPairsInnerEnv := ⟨3, dtPairsInnerEnvWords⟩

private structure DTPairsOuterEnv where
  arrA : ℕ
  arrB : ℕ
  deriving DecidableEq

private word_enc_structure dtPairsOuterEnvWords : DTPairsOuterEnv where
  arrA : wordWords,
  arrB : wordWords

private instance : WordEncoding DTPairsOuterEnv := ⟨2, dtPairsOuterEnvWords⟩

private structure DTPowEnv where
  powArr : ℕ
  base : ℕ
  deriving DecidableEq

private word_enc_structure dtPowEnvWords : DTPowEnv where
  powArr : wordWords,
  base : wordWords

private instance : WordEncoding DTPowEnv := ⟨2, dtPowEnvWords⟩

private structure DTDecodeMaskEnv where
  r0PairA : ℕ
  r0PairB : ℕ
  edgeU : ℕ
  edgeV : ℕ
  edgePair : ℕ
  mask : ℕ
  deriving DecidableEq

private word_enc_structure dtDecodeMaskEnvWords : DTDecodeMaskEnv where
  r0PairA : wordWords,
  r0PairB : wordWords,
  edgeU : wordWords,
  edgeV : wordWords,
  edgePair : wordWords,
  mask : wordWords

private instance : WordEncoding DTDecodeMaskEnv := ⟨6, dtDecodeMaskEnvWords⟩

private structure DTMergeEnv where
  compArr : ℕ
  cu : ℕ
  cv : ℕ
  deriving DecidableEq

private word_enc_structure dtMergeEnvWords : DTMergeEnv where
  compArr : wordWords,
  cu : wordWords,
  cv : wordWords

private instance : WordEncoding DTMergeEnv := ⟨3, dtMergeEnvWords⟩

private structure DTKruskalMergeArgs where
  r0 : ℕ
  compArr : ℕ
  cu : ℕ
  cv : ℕ
  rk : ℕ
  idx : ℕ
  msfMask : ℕ
  deriving DecidableEq

private word_enc_structure dtKruskalMergeArgsWords : DTKruskalMergeArgs where
  r0 : wordWords,
  compArr : wordWords,
  cu : wordWords,
  cv : wordWords,
  rk : wordWords,
  idx : wordWords,
  msfMask : wordWords

private instance : WordEncoding DTKruskalMergeArgs := ⟨7, dtKruskalMergeArgsWords⟩

private structure DTKruskalEnv where
  r0 : ℕ
  edgeU : ℕ
  edgeV : ℕ
  orderArr : ℕ
  compArr : ℕ
  deriving DecidableEq

private word_enc_structure dtKruskalEnvWords : DTKruskalEnv where
  r0 : wordWords,
  edgeU : wordWords,
  edgeV : wordWords,
  orderArr : wordWords,
  compArr : wordWords

private instance : WordEncoding DTKruskalEnv := ⟨5, dtKruskalEnvWords⟩

private def dtFillPairsInnerStep (x : DTPairsInnerEnv × DTIdxPair) : Memory.Prog DTIdxPair := do
  Memory.write (x.1.arrA + x.2.acc) x.2.idx
  Memory.write (x.1.arrB + x.2.acc) x.1.b
  pure ⟨x.2.idx + 1, x.2.acc + 1⟩

private def dtFillPairsInnerStepSafe (w : ℕ) (x : DTPairsInnerEnv × DTIdxPair)
    (s : Memory.State) : Prop :=
  Fits w (x.2.idx + 1) ∧ Fits w (x.2.acc + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtFillPairsInnerStep x))

private theorem realizes_dtFillPairsInnerStep : Realizes .exact
    dtFillPairsInnerStep
    (appendWords dtPairsInnerEnvWords dtIdxPairWords)
    dtIdxPairWords dtFillPairsInnerStepSafe (fun _ _ => 0) := by
  unfold dtFillPairsInnerStep
  realize
  all_goals
    obtain ⟨h1, h2, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtFillPairsInnerStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.write, Memory.step_write, Memory.valid] at hv
    fits

private def dtFillPairsOuterStep (x : DTPairsOuterEnv × DTIdxPair) : Memory.Prog DTIdxPair := do
  let _ ← Memory.read x.1.arrA
  let r ← iterate dtFillPairsInnerStep ⟨x.1.arrA, x.1.arrB, x.2.idx⟩ x.2.idx ⟨0, x.2.acc⟩
  pure ⟨x.2.idx + 1, r.acc⟩

private def dtFillPairsOuterStepSafe (w : ℕ) (x : DTPairsOuterEnv × DTIdxPair)
    (s : Memory.State) : Prop :=
  x.1.arrA < s.frontier ∧ Fits w (x.2.idx + 1) ∧
  iterationSafe dtFillPairsInnerStep dtFillPairsInnerStepSafe w
    ⟨x.1.arrA, x.1.arrB, x.2.idx⟩ x.2.idx ⟨0, x.2.acc⟩ s

private theorem realizes_dtFillPairsOuterStep : Realizes .exact
    dtFillPairsOuterStep
    (appendWords dtPairsOuterEnvWords dtIdxPairWords)
    dtIdxPairWords dtFillPairsOuterStepSafe (fun _ _ => 0) := by
  unfold dtFillPairsOuterStep
  realize [realizes_dtFillPairsInnerStep]
  all_goals
    obtain ⟨hlt, hidx, hit⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact iterationSafe_imp hit (fun _ => rfl) (fun _ _ hs => hs)
    | fits

private def dtFillPowStep (x : DTPowEnv × ℕ) : Memory.Prog ℕ := do
  let v ← Memory.read (x.1.powArr + x.2)
  Memory.write (x.1.powArr + x.2 + 1) (v * x.1.base)
  pure (x.2 + 1)

private def dtFillPowStepSafe (w : ℕ) (x : DTPowEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w (x.2 + 1) ∧ Fits w (s.mem (x.1.powArr + x.2) * x.1.base) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtFillPowStep x))

private theorem realizes_dtFillPowStep : Realizes .exact
    dtFillPowStep (appendWords dtPowEnvWords WordEncoding.encode)
    WordEncoding.encode dtFillPowStepSafe (fun _ _ => 0) := by
  unfold dtFillPowStep
  realize
  all_goals
    obtain ⟨hidx, hmul, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtFillPowStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.valid] at hv
    fits

private def dtDecodeMaskStep (x : DTDecodeMaskEnv × DTIdxPair) : Memory.Prog DTIdxPair := do
  let a ← Memory.read (x.1.r0PairA + x.2.idx)
  let b ← Memory.read (x.1.r0PairB + x.2.idx)
  if (x.1.mask >>> x.2.idx) &&& 1 = 1 then
    Memory.write (x.1.edgeU + x.2.acc) a
    Memory.write (x.1.edgeV + x.2.acc) b
    Memory.write (x.1.edgePair + x.2.acc) x.2.idx
    pure ⟨x.2.idx + 1, x.2.acc + 1⟩
  else
    pure ⟨x.2.idx + 1, x.2.acc⟩

private def dtDecodeMaskStepSafe (w : ℕ) (x : DTDecodeMaskEnv × DTIdxPair)
    (s : Memory.State) : Prop :=
  Fits w 2 ∧ Fits w (x.2.idx + 1) ∧ Fits w (x.2.acc + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtDecodeMaskStep x))

private theorem realizes_dtDecodeMaskStep : Realizes .exact
    dtDecodeMaskStep
    (appendWords dtDecodeMaskEnvWords dtIdxPairWords)
    dtIdxPairWords dtDecodeMaskStepSafe (fun _ _ => 0) := by
  unfold dtDecodeMaskStep
  realize
  all_goals
    obtain ⟨h2, h1, hacc, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtDecodeMaskStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.valid] at hv
    try simp only [hc, ite_true] at hv
    try simp only [ite_false] at hv
    try simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.step_write, Memory.valid] at hv
    fits

private def dtInitIdStep (x : ℕ × ℕ) : Memory.Prog ℕ := do
  Memory.write (x.1 + x.2) x.2
  pure (x.2 + 1)

private def dtInitIdStepSafe (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) : Prop :=
  Fits w (x.2 + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtInitIdStep x))

private theorem realizes_dtInitIdStep : Realizes .exact
    dtInitIdStep (appendWords WordEncoding.encode WordEncoding.encode)
    WordEncoding.encode dtInitIdStepSafe (fun _ _ => 0) := by
  unfold dtInitIdStep
  realize
  all_goals
    obtain ⟨hidx, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtInitIdStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.write, Memory.step_write, Memory.valid] at hv
    fits

private def dtMergeCompStep (x : DTMergeEnv × ℕ) : Memory.Prog ℕ := do
  let c ← Memory.read (x.1.compArr + x.2)
  if c = x.1.cu then
    Memory.write (x.1.compArr + x.2) x.1.cv
    pure (x.2 + 1)
  else
    pure (x.2 + 1)

private def dtMergeCompStepSafe (w : ℕ) (x : DTMergeEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w (x.2 + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtMergeCompStep x))

private theorem realizes_dtMergeCompStep : Realizes .exact
    dtMergeCompStep (appendWords dtMergeEnvWords WordEncoding.encode)
    WordEncoding.encode dtMergeCompStepSafe (fun _ _ => 0) := by
  unfold dtMergeCompStep
  realize
  all_goals
    obtain ⟨hidx, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtMergeCompStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.valid] at hv
    try simp only [hc, ite_true] at hv
    try simp only [ite_false] at hv
    try simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.step_write, Memory.valid] at hv
    fits

private def dtKruskalMerge (d : DTKruskalMergeArgs) : Memory.Prog DTIdxPair := do
  if d.cu = d.cv then pure ⟨d.rk + 1, d.msfMask⟩
  else
    let _ ← iterate dtMergeCompStep ⟨d.compArr, d.cu, d.cv⟩ d.r0 0
    pure ⟨d.rk + 1, d.msfMask ||| (1 <<< d.idx)⟩

private def dtKruskalMergeSafe (w : ℕ) (d : DTKruskalMergeArgs) (s : Memory.State) : Prop :=
  Fits w 2 ∧ Fits w (d.rk + 1) ∧
  (d.cu ≠ d.cv → Fits w (d.msfMask ||| (1 <<< d.idx)) ∧
    iterationSafe dtMergeCompStep dtMergeCompStepSafe w ⟨d.compArr, d.cu, d.cv⟩ d.r0 0 s)

private theorem realizes_dtKruskalMerge : Realizes .exact
    dtKruskalMerge dtKruskalMergeArgsWords dtIdxPairWords
    dtKruskalMergeSafe (fun _ _ => 0) := by
  unfold dtKruskalMerge
  realize [realizes_dtMergeCompStep]
  all_goals
    obtain ⟨h2, hrk, hm⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact iterationSafe_imp (hm hc).2 (fun _ => rfl) (fun _ _ hs => hs)
    | exact (hm hc).1
    | fits

private def dtKruskalEdgeStep (x : DTKruskalEnv × DTIdxPair) : Memory.Prog DTIdxPair := do
  let idx ← Memory.read (x.1.orderArr + x.2.idx)
  let u ← Memory.read (x.1.edgeU + idx)
  let v ← Memory.read (x.1.edgeV + idx)
  let cu ← Memory.read (x.1.compArr + u)
  let cv ← Memory.read (x.1.compArr + v)
  dtKruskalMerge ⟨x.1.r0, x.1.compArr, cu, cv, x.2.idx, idx, x.2.acc⟩

private def dtKruskalEdgeStepSafe (w : ℕ) (x : DTKruskalEnv × DTIdxPair)
    (s : Memory.State) : Prop :=
  let idx := s.mem (x.1.orderArr + x.2.idx)
  let u := s.mem (x.1.edgeU + idx)
  let v := s.mem (x.1.edgeV + idx)
  let cu := s.mem (x.1.compArr + u)
  let cv := s.mem (x.1.compArr + v)
  x.1.orderArr + x.2.idx < s.frontier ∧ x.1.edgeU + idx < s.frontier ∧
  x.1.edgeV + idx < s.frontier ∧ x.1.compArr + u < s.frontier ∧ x.1.compArr + v < s.frontier ∧
  dtKruskalMergeSafe w ⟨x.1.r0, x.1.compArr, cu, cv, x.2.idx, idx, x.2.acc⟩ s

private theorem realizes_dtKruskalEdgeStep : Realizes .exact
    dtKruskalEdgeStep (appendWords dtKruskalEnvWords dtIdxPairWords)
    dtIdxPairWords dtKruskalEdgeStepSafe (fun _ _ => 0) := by
  unfold dtKruskalEdgeStep
  realize [realizes_dtKruskalMerge]
  all_goals
    obtain ⟨h0, h1, h2, h3, h4, hm⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact hm
    | fits

/-! ## Section 3: Enumerating All Unordered Pairs (`dtFillAllPairsProg`) -/

/-- Fills `(d.arrA, d.arrB)` with all unordered pairs `(a, b)` for `0 ≤ a < b < d.numV`. -/
def dtFillAllPairsProg (d : DTPairsArgs) : Memory.Prog ℕ := do
  let r ← iterate dtFillPairsOuterStep ⟨d.arrA, d.arrB⟩ d.numV ⟨0, 0⟩
  pure r.acc

/-- Word-RAM safety precondition for `dtFillAllPairsProg`. -/
def dtFillAllPairsProgSafe (w : ℕ) (d : DTPairsArgs) (s : Memory.State) : Prop :=
  Fits w 2 ∧ Fits w (d.numV + 1) ∧ Fits w (d.numV.choose 2 + 1) ∧
  (0 < d.numV → d.arrA < s.frontier) ∧
  d.arrA + d.numV.choose 2 ≤ s.frontier ∧ d.arrB + d.numV.choose 2 ≤ s.frontier ∧
  (d.arrA + d.numV.choose 2 ≤ d.arrB ∨ d.arrB + d.numV.choose 2 ≤ d.arrA)

/-- Unfolding equivalence for `dtFillAllPairsProgSafe`. -/
theorem dtFillAllPairsProgSafe_iff (w : ℕ) (d : DTPairsArgs) (s : Memory.State) :
    dtFillAllPairsProgSafe w d s ↔
      Fits w 2 ∧ Fits w (d.numV + 1) ∧ Fits w (d.numV.choose 2 + 1) ∧
      (0 < d.numV → d.arrA < s.frontier) ∧
      d.arrA + d.numV.choose 2 ≤ s.frontier ∧ d.arrB + d.numV.choose 2 ≤ s.frontier ∧
      (d.arrA + d.numV.choose 2 ≤ d.arrB ∨ d.arrB + d.numV.choose 2 ≤ d.arrA) := Iff.rfl

private theorem dtFillAllPairsProg_core {w arrA arrB numV : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (_h2 : Fits w 2) (hnumV : Fits w (numV + 1))
    (hmax : Fits w (numV.choose 2 + 1)) (ha_pos : 0 < numV → arrA < s.frontier)
    (ha_lt : arrA + numV.choose 2 ≤ s.frontier) (hb_lt : arrB + numV.choose 2 ≤ s.frontier)
    (hdisj : arrA + numV.choose 2 ≤ arrB ∨ arrB + numV.choose 2 ≤ arrA) :
    iterationSafe dtFillPairsOuterStep dtFillPairsOuterStepSafe w
      ⟨arrA, arrB⟩ numV ⟨0, 0⟩ s ∧
    Memory.FramedTriple w s (dtFillAllPairsProg ⟨arrA, arrB, numV⟩) (numV * (1 + 2 * numV))
      (Set.Ico arrA (arrA + numV.choose 2) ∪ Set.Ico arrB (arrB + numV.choose 2))
      fun res s' =>
        res = numV.choose 2 ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ k (hk : k < numV.choose 2),
          s'.mem (arrA + k) = ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
          s'.mem (arrB + k) = ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk)).2.val := by
  let S : Set ℕ := Set.Ico arrA (arrA + numV.choose 2) ∪ Set.Ico arrB (arrB + numV.choose 2)
  let inv (b : ℕ) (st : DTIdxPair) (t : Memory.State) : Prop :=
    st.idx = b ∧ st.acc = b.choose 2 ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    ∀ k (hk : k < b.choose 2), ∀ (hbm : b ≤ numV),
      let hk' : k < numV.choose 2 := hk.trans_le (Nat.choose_le_choose 2 hbm)
      t.mem (arrA + k) = ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk')).1.val ∧
      t.mem (arrB + k) = ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk')).2.val
  have hstep : ∀ b < numV, ∀ st t, inv b st t →
      dtFillPairsOuterStepSafe w (⟨arrA, arrB⟩, st) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (dtFillPairsOuterStep (⟨arrA, arrB⟩, st))) ∧
      let a' := (Memory.spec 0).clientResult t (dtFillPairsOuterStep (⟨arrA, arrB⟩, st))
      let t' := (Memory.spec 0).clientState t (dtFillPairsOuterStep (⟨arrA, arrB⟩, st))
      memoryCost (dtFillPairsOuterStep (⟨arrA, arrB⟩, st)) t + 0 ≤ 0 + (1 + 2 * numV) ∧
      Memory.Modifies S t t' ∧
      inv (b + 1) a' t' := by
    intro b hb st t ⟨hidx, hacc, htfr, hwt, hprev⟩
    rcases st with ⟨sidx, sacc⟩
    dsimp only at hidx hacc
    subst sidx
    have hch_b1 : (b + 1).choose 2 ≤ numV.choose 2 := Nat.choose_le_choose 2 hb
    have hsucc : (b + 1).choose 2 = b.choose 2 + b := choose_two_succ b
    let innEnv : DTPairsInnerEnv := ⟨arrA, arrB, b⟩
    let innInv (i : ℕ) (ist : DTIdxPair) (it : Memory.State) : Prop :=
      ist.idx = i ∧ ist.acc = b.choose 2 + i ∧ it.frontier = t.frontier ∧
      Memory.WellFormed w it ∧
      ∀ k (hk1 : k < b.choose 2 + i) (hk2 : k < b.choose 2 + b),
        let hk' : k < numV.choose 2 := (hk2.trans_eq hsucc.symm).trans_le hch_b1
        it.mem (arrA + k) = ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk')).1.val ∧
        it.mem (arrB + k) = ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk')).2.val
    have hinn : ∀ i < b, ∀ ist it, innInv i ist it →
        dtFillPairsInnerStepSafe w (innEnv, ist) it ∧
        (Memory.spec w).ValidHistory it
          ((Memory.spec w).clientHistory it (dtFillPairsInnerStep (innEnv, ist))) ∧
        let a' := (Memory.spec 0).clientResult it (dtFillPairsInnerStep (innEnv, ist))
        let it' := (Memory.spec 0).clientState it (dtFillPairsInnerStep (innEnv, ist))
        memoryCost (dtFillPairsInnerStep (innEnv, ist)) it + 0 ≤ 0 + 2 ∧
        Memory.Modifies S it it' ∧
        innInv (i + 1) a' it' := by
      intro i hi ist it ⟨hiidx, hiacc, hitfr, hiwt, hiprev⟩
      rcases ist with ⟨iidx, iacc⟩
      dsimp only at hiidx hiacc
      subst iidx
      have hpos_acc : b.choose 2 + i < numV.choose 2 := by omega
      have htri_raw : Memory.FramedTriple w it (dtFillPairsInnerStep (innEnv, ⟨i, iacc⟩)) 2 S
          fun a' it' =>
            a' = ⟨i + 1, iacc + 1⟩ ∧ it'.frontier = t.frontier ∧
            (∀ k (hk1 : k < b.choose 2 + (i + 1)) (hk2 : k < b.choose 2 + b),
              let hk' : k < numV.choose 2 := (hk2.trans_eq hsucc.symm).trans_le hch_b1
              it'.mem (arrA + k) =
                ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk')).1.val ∧
              it'.mem (arrB + k) =
                ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk')).2.val) := by
        dsimp only [dtFillPairsInnerStep, innEnv]
        refine Memory.FramedTriple.write_bind_of_mem (by omega) (by fits)
          (Set.mem_union_left _ ⟨by omega, by omega⟩) ?_
        refine Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega) (by fits)
          (Set.mem_union_right _ ⟨by omega, by omega⟩) ?_
        refine Memory.FramedTriple.pure ⟨rfl, hitfr, fun k hk1 hk2 => ?_⟩
        dsimp only
        by_cases hki : k < b.choose 2 + i
        · have hne1 : arrA + k ≠ arrB + iacc := by rcases hdisj with h | h <;> omega
          have hne2 : arrA + k ≠ arrA + iacc := by omega
          have hne3 : arrB + k ≠ arrB + iacc := by omega
          have hne4 : arrB + k ≠ arrA + iacc := by rcases hdisj with h | h <;> omega
          rw [Function.update_of_ne hne1, Function.update_of_ne hne2,
            Function.update_of_ne hne3, Function.update_of_ne hne4]
          exact hiprev k hki hk2
        · have hkeq : k = b.choose 2 + i := by omega
          have hget := getElem_allPairs_pairIdx (r := numV)
            (a := ⟨i, by omega⟩) (b := ⟨b, hb⟩) hi
          have hpidx : pairIdx i b = b.choose 2 + i := by
            rw [pairIdx, Nat.choose_two_right, Nat.mul_comm]
          have hne_ab : arrA + k ≠ arrB + iacc := by rcases hdisj with h | h <;> omega
          have heqA : (Function.update (Function.update it.mem (arrA + iacc) i)
              (arrB + iacc) b) (arrA + k) = i := by
            rw [hkeq, ← hiacc, Function.update_of_ne (by rcases hdisj with h | h <;> omega),
              Function.update_self]
          have heqB : (Function.update (Function.update it.mem (arrA + iacc) i)
              (arrB + iacc) b) (arrB + k) = b := by
            rw [hkeq, ← hiacc]; exact Function.update_self _ _ _
          rw [heqA, heqB]
          have hc1 := congrArg (fun p : Fin numV × Fin numV => p.1.val) hget
          have hc2 := congrArg (fun p : Fin numV × Fin numV => p.2.val) hget
          dsimp only at hc1 hc2
          have hk_eq : k = pairIdx i b := hkeq.trans hpidx.symm
          exact ⟨by simp only [← hk_eq] at hc1; exact hc1.symm,
            by simp only [← hk_eq] at hc2; exact hc2.symm⟩
      have htri : Memory.FramedTriple w it (dtFillPairsInnerStep (innEnv, ⟨i, iacc⟩)) 2 S
          fun a' it' => innInv (i + 1) a' it' := by
        refine (htri_raw.wellFormed hiwt).mono le_rfl ?_
        rintro _ _ ⟨⟨rfl, hfr, hk⟩, hwf'⟩
        exact ⟨rfl, by dsimp only; omega, hfr, hwf', hk⟩
      obtain ⟨hvh, hcost, hmod, hinv_next⟩ := framedTriple_iff_realization.mp htri
      have hi1_fit : Fits w (i + 1) := hnumV.of_le (by omega)
      have hacc1_fit : Fits w (iacc + 1) := hmax.of_le (by omega)
      exact ⟨⟨hi1_fit, hacc1_fit, hvh⟩, hvh, by omega, hmod, hinv_next⟩
    have hinit : innInv 0 ⟨0, b.choose 2⟩ t := by
      refine ⟨rfl, rfl, rfl, hwt, fun k hk1 hk2 => ?_⟩
      rw [Nat.add_zero] at hk1
      exact hprev k hk1 hb.le
    obtain ⟨hisafe, hiv, him, himod, hiend⟩ :=
      iterate_potential_spec dtFillPairsInnerStep dtFillPairsInnerStepSafe w innEnv 2 b
        innInv (fun _ _ _ => 0) S hinn ⟨0, b.choose 2⟩ t hinit
    have hloop : Memory.FramedTriple w t (iterate dtFillPairsInnerStep innEnv b ⟨0, b.choose 2⟩)
        (2 * b) S fun a' t' =>
          a'.acc = (b + 1).choose 2 ∧ t'.frontier = s.frontier ∧ Memory.WellFormed w t' ∧
          ∀ k (hk : k < (b + 1).choose 2),
            let hk' : k < numV.choose 2 := hk.trans_le hch_b1
            t'.mem (arrA + k) =
              ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk')).1.val ∧
            t'.mem (arrB + k) =
              ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk')).2.val := by
      refine framedTriple_iff_realization.mpr ⟨hiv, by simpa [Nat.mul_comm] using him, himod, ?_⟩
      refine ⟨by rw [hiend.2.1, hsucc], hiend.2.2.1.trans htfr, hiend.2.2.2.1, fun k hk => ?_⟩
      rw [hsucc] at hk
      exact hiend.2.2.2.2 k hk hk
    have ha_t : arrA < t.frontier := (ha_pos (by omega)).trans_eq htfr.symm
    have houter : Memory.FramedTriple w t (dtFillPairsOuterStep (⟨arrA, arrB⟩, ⟨b, sacc⟩))
        (1 + 2 * numV) S (inv (b + 1)) := by
      dsimp only [dtFillPairsOuterStep]
      have hread : Memory.FramedTriple w t
          (Memory.read arrA >>= fun _ =>
            iterate dtFillPairsInnerStep ⟨arrA, arrB, b⟩ b ⟨0, sacc⟩ >>= fun r =>
              pure ⟨b + 1, r.acc⟩)
          (2 * b + 1) S (inv (b + 1)) := by
        refine Memory.FramedTriple.read_bind ha_t ?_
        rw [hacc]
        have hloop' : Memory.FramedTriple w t
            (iterate dtFillPairsInnerStep ⟨arrA, arrB, b⟩ b ⟨0, b.choose 2⟩) (2 * b) S
            fun a' t' =>
              Memory.FramedTriple w t' (pure (⟨b + 1, a'.acc⟩ : DTIdxPair)) 0 S (inv (b + 1)) :=
          hloop.mono le_rfl fun _ _ h =>
            Memory.FramedTriple.pure ⟨rfl, h.1, h.2.1, h.2.2.1, fun k hk _ => h.2.2.2 k hk⟩
        exact hloop'.bind_same.mono (by omega) fun _ _ h => h
      exact hread.mono (by omega) fun _ _ h => h
    obtain ⟨hvh, hcost, hmod, hinv_next⟩ := framedTriple_iff_realization.mp houter
    refine ⟨⟨ha_t, hnumV.of_le (by dsimp only; omega), by rw [hacc]; exact hisafe⟩,
      hvh, by omega, hmod, hinv_next⟩
  obtain ⟨hsafe, hv, hm, hmod, inv_end⟩ :=
    iterate_potential_spec dtFillPairsOuterStep dtFillPairsOuterStepSafe w ⟨arrA, arrB⟩
      (1 + 2 * numV) numV inv (fun _ _ _ => 0) S hstep ⟨0, 0⟩ s
      ⟨rfl, rfl, rfl, hwf, fun k hk _ => by simp at hk⟩
  have hloop : Memory.FramedTriple w s (iterate dtFillPairsOuterStep ⟨arrA, arrB⟩ numV ⟨0, 0⟩)
      (numV * (1 + 2 * numV)) S fun r s' =>
        r.acc = numV.choose 2 ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ k (hk : k < numV.choose 2),
          s'.mem (arrA + k) = ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
          s'.mem (arrB + k) = ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk)).2.val :=
    framedTriple_iff_realization.mpr
      ⟨hv, by simpa [Nat.mul_comm] using hm, hmod, inv_end.2.1, inv_end.2.2.1,
        inv_end.2.2.2.1, fun k hk => inv_end.2.2.2.2 k hk le_rfl⟩
  refine ⟨hsafe, ?_⟩
  dsimp only [dtFillAllPairsProg]
  have hloop' : Memory.FramedTriple w s
      (iterate dtFillPairsOuterStep ⟨arrA, arrB⟩ numV ⟨0, 0⟩) (numV * (1 + 2 * numV)) S
      fun r s' => Memory.FramedTriple w s' (pure r.acc) 0 S fun res s' =>
        res = numV.choose 2 ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ k (hk : k < numV.choose 2),
          s'.mem (arrA + k) = ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
          s'.mem (arrB + k) = ((allPairs numV)[k]'(by rw [length_allPairs]; exact hk)).2.val :=
    hloop.mono le_rfl fun _ _ h => Memory.FramedTriple.pure h
  exact hloop'.bind_same.mono (by omega) fun _ _ h => h

/-- Framed specification for `dtFillAllPairsProg`. -/
theorem dtFillAllPairsProg_spec {w : ℕ} {d : DTPairsArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtFillAllPairsProgSafe w d s) :
    Memory.FramedTriple w s (dtFillAllPairsProg d) (d.numV * (1 + 2 * d.numV))
      (Set.Ico d.arrA (d.arrA + d.numV.choose 2) ∪
        Set.Ico d.arrB (d.arrB + d.numV.choose 2))
      fun res s' =>
        res = d.numV.choose 2 ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ k (hk : k < d.numV.choose 2),
          s'.mem (d.arrA + k) =
            ((allPairs d.numV)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
          s'.mem (d.arrB + k) =
            ((allPairs d.numV)[k]'(by rw [length_allPairs]; exact hk)).2.val :=
  (dtFillAllPairsProg_core hwf hsafe.1 hsafe.2.1 hsafe.2.2.1 hsafe.2.2.2.1
    hsafe.2.2.2.2.1 hsafe.2.2.2.2.2.1 hsafe.2.2.2.2.2.2).2

private theorem realizes_dtFillAllPairsProg_raw : Realizes .exact
    dtFillAllPairsProg dtPairsArgsWords WordEncoding.encode
    (fun w d s => Fits w 2 ∧
      iterationSafe dtFillPairsOuterStep dtFillPairsOuterStepSafe w
        ⟨d.arrA, d.arrB⟩ d.numV ⟨0, 0⟩ s)
    (fun _ _ => 0) := by
  unfold dtFillAllPairsProg
  realize [realizes_dtFillPairsOuterStep]
  obtain ⟨h2, hit⟩ := h
  exact iterationSafe_imp hit (fun _ => rfl) (fun _ _ hs => hs)

/-- `dtFillAllPairsProg` is uniformly realized with `work = 0`. -/
theorem realizes_dtFillAllPairsProg : Realizes .exact
    dtFillAllPairsProg dtPairsArgsWords WordEncoding.encode
    dtFillAllPairsProgSafe (fun _ _ => 0) :=
  realizes_dtFillAllPairsProg_raw.consequence
    (fun _ _ _ _ hwf hs => ⟨hs.1,
      (dtFillAllPairsProg_core hwf hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
        hs.2.2.2.2.2.1 hs.2.2.2.2.2.2).1⟩)
    (fun _ _ => le_rfl)

/-! ## Section 4: Power-Table Filling (`dtFillPowProg`) -/

/-- Fills `d.powArr[0..d.len]` with `d.base ^ 0 .. d.base ^ d.len`. -/
def dtFillPowProg (d : DTPowArgs) : Memory.Prog ℕ := do
  Memory.write d.powArr 1
  iterate dtFillPowStep ⟨d.powArr, d.base⟩ d.len 0

/-- Word-RAM safety precondition for `dtFillPowProg`. -/
def dtFillPowProgSafe (w : ℕ) (d : DTPowArgs) (s : Memory.State) : Prop :=
  Fits w 2 ∧ Fits w (d.len + 1) ∧ 1 ≤ d.base ∧ Fits w (d.base ^ d.len) ∧
  d.powArr + d.len + 1 ≤ s.frontier

/-- Unfolding equivalence for `dtFillPowProgSafe`. -/
theorem dtFillPowProgSafe_iff (w : ℕ) (d : DTPowArgs) (s : Memory.State) :
    dtFillPowProgSafe w d s ↔
      Fits w 2 ∧ Fits w (d.len + 1) ∧ 1 ≤ d.base ∧ Fits w (d.base ^ d.len) ∧
      d.powArr + d.len + 1 ≤ s.frontier := Iff.rfl

private theorem dtFillPowProg_core {w powArr base len : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h2 : Fits w 2) (hlen : Fits w (len + 1))
    (hbase : 1 ≤ base) (hpow : Fits w (base ^ len)) (hbound : powArr + len + 1 ≤ s.frontier) :
    iterationSafe dtFillPowStep dtFillPowStepSafe w ⟨powArr, base⟩ len 0
      ⟨Function.update s.mem powArr 1, s.frontier⟩ ∧
    Memory.FramedTriple w s (dtFillPowProg ⟨powArr, base, len⟩) (1 + 2 * len)
      (Set.Ico powArr (powArr + len + 1)) fun res s' =>
        res = len ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ k ≤ len, s'.mem (powArr + k) = base ^ k := by
  let s0 : Memory.State := ⟨Function.update s.mem powArr 1, s.frontier⟩
  have hwf0 : Memory.WellFormed w s0 := by
    have h := wellFormed_clientState hwf
      (validHistory_write (a := powArr) (v := 1) (by omega) (by fits))
    rwa [clientState_write] at h
  let S : Set ℕ := Set.Ico powArr (powArr + len + 1)
  let inv (k idx : ℕ) (t : Memory.State) : Prop :=
    idx = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    ∀ j ≤ k, t.mem (powArr + j) = base ^ j
  have hstep : ∀ k < len, ∀ idx t, inv k idx t →
      dtFillPowStepSafe w (⟨powArr, base⟩, idx) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (dtFillPowStep (⟨powArr, base⟩, idx))) ∧
      let a' := (Memory.spec 0).clientResult t (dtFillPowStep (⟨powArr, base⟩, idx))
      let t' := (Memory.spec 0).clientState t (dtFillPowStep (⟨powArr, base⟩, idx))
      memoryCost (dtFillPowStep (⟨powArr, base⟩, idx)) t + 0 ≤ 0 + 2 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk idx t ⟨hidx, htfr, hwt, hprev⟩
    subst idx
    have hcur : t.mem (powArr + k) = base ^ k := hprev k le_rfl
    have hpow_le : base ^ (k + 1) ≤ base ^ len := Nat.pow_le_pow_right hbase (by omega)
    have hmul_fit : Fits w (t.mem (powArr + k) * base) := by
      rw [hcur, ← pow_succ]
      exact hpow.of_le hpow_le
    have htri_raw : Memory.FramedTriple w t (dtFillPowStep (⟨powArr, base⟩, k)) 2 S
        fun a' t' =>
          a' = k + 1 ∧ t'.frontier = s.frontier ∧
          ∀ j ≤ k + 1, t'.mem (powArr + j) = base ^ j := by
      dsimp only [dtFillPowStep]
      refine Memory.FramedTriple.read_bind (by omega) ?_
      refine Memory.FramedTriple.write_bind_of_mem (by omega) hmul_fit
        ⟨by omega, by omega⟩ ?_
      refine Memory.FramedTriple.pure ⟨rfl, htfr, fun j hj => ?_⟩
      dsimp only
      by_cases hjk : j ≤ k
      · rw [Function.update_of_ne (by omega)]
        exact hprev j hjk
      · have hje : j = k + 1 := by omega
        subst hje
        rw [show powArr + (k + 1) = powArr + k + 1 by omega, Function.update_self, hcur, pow_succ]
    have htri : Memory.FramedTriple w t (dtFillPowStep (⟨powArr, base⟩, k)) 2 S (inv (k + 1)) := by
      refine (htri_raw.wellFormed hwt).mono le_rfl ?_
      rintro _ _ ⟨⟨rfl, hfr, hvals⟩, hwf'⟩
      exact ⟨rfl, hfr, hwf', hvals⟩
    obtain ⟨hvh, hcost, hmod, hinv_next⟩ := framedTriple_iff_realization.mp htri
    exact ⟨⟨hlen.of_le (by omega), hmul_fit, hvh⟩, hvh, by omega, hmod, hinv_next⟩
  have hinit : inv 0 0 s0 :=
    ⟨rfl, rfl, hwf0, fun j hj => by
      cases j with
      | zero => simp [s0]
      | succ _ => omega⟩
  obtain ⟨hsafe, hv, hm, hmod, inv_end⟩ :=
    iterate_potential_spec dtFillPowStep dtFillPowStepSafe w ⟨powArr, base⟩ 2 len
      inv (fun _ _ _ => 0) S hstep 0 s0 hinit
  have hloop : Memory.FramedTriple w s0 (iterate dtFillPowStep ⟨powArr, base⟩ len 0)
      (2 * len) S fun res s' =>
        res = len ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ k ≤ len, s'.mem (powArr + k) = base ^ k :=
    framedTriple_iff_realization.mpr ⟨hv, by simpa [Nat.mul_comm] using hm, hmod, inv_end⟩
  refine ⟨hsafe, ?_⟩
  dsimp only [dtFillPowProg]
  rw [show 1 + 2 * len = 2 * len + 1 by omega]
  exact Memory.FramedTriple.write_bind_of_mem (by omega) (by fits)
    ⟨le_rfl, by omega⟩ hloop

/-- Framed specification for `dtFillPowProg`. -/
theorem dtFillPowProg_spec {w : ℕ} {d : DTPowArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtFillPowProgSafe w d s) :
    Memory.FramedTriple w s (dtFillPowProg d) (1 + 2 * d.len)
      (Set.Ico d.powArr (d.powArr + d.len + 1))
      fun res s' =>
        res = d.len ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ k ≤ d.len, s'.mem (d.powArr + k) = d.base ^ k :=
  (dtFillPowProg_core hwf hsafe.1 hsafe.2.1 hsafe.2.2.1 hsafe.2.2.2.1 hsafe.2.2.2.2).2

private theorem realizes_dtFillPowProg_raw : Realizes .exact
    dtFillPowProg dtPowArgsWords WordEncoding.encode
    (fun w d s => Fits w 2 ∧ d.powArr < s.frontier ∧
      iterationSafe dtFillPowStep dtFillPowStepSafe w ⟨d.powArr, d.base⟩ d.len 0
        ⟨Function.update s.mem d.powArr 1, s.frontier⟩)
    (fun _ _ => 0) := by
  unfold dtFillPowProg
  realize [realizes_dtFillPowStep]
  all_goals
    obtain ⟨h2, hlt, hit⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact iterationSafe_imp hit (fun _ => rfl) (fun _ _ hs => hs)
    | fits

/-- `dtFillPowProg` is uniformly realized with `work = 0`. -/
theorem realizes_dtFillPowProg : Realizes .exact
    dtFillPowProg dtPowArgsWords WordEncoding.encode
    dtFillPowProgSafe (fun _ _ => 0) :=
  realizes_dtFillPowProg_raw.consequence
    (fun _ _ _ _ hwf hs => ⟨hs.1, by have := hs.2.2.2.2; omega,
      (dtFillPowProg_core hwf hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2).1⟩)
    (fun _ _ => le_rfl)

/-! ## Section 5: Graph Bitmask Decoding (`dtDecodeMaskProg`) -/

/-- Decodes bits `0 .. d.maxE - 1` of `d.mask` into `(edgeU, edgeV, edgePair)` and returns the
decoded edge count. -/
def dtDecodeMaskProg (d : DTDecodeMaskArgs) : Memory.Prog ℕ := do
  let r ← iterate dtDecodeMaskStep
    ⟨d.r0PairA, d.r0PairB, d.edgeU, d.edgeV, d.edgePair, d.mask⟩ d.maxE ⟨0, 0⟩
  pure r.acc

/-- Word-RAM safety precondition for `dtDecodeMaskProg`. -/
def dtDecodeMaskProgSafe (w : ℕ) (d : DTDecodeMaskArgs) (s : Memory.State) : Prop :=
  Fits w 2 ∧ Fits w (d.maxE + 1) ∧
  d.r0PairA + d.maxE ≤ s.frontier ∧ d.r0PairB + d.maxE ≤ s.frontier ∧
  d.edgeU + d.maxE ≤ s.frontier ∧ d.edgeV + d.maxE ≤ s.frontier ∧
  d.edgePair + d.maxE ≤ s.frontier

/-- Unfolding equivalence for `dtDecodeMaskProgSafe`. -/
theorem dtDecodeMaskProgSafe_iff (w : ℕ) (d : DTDecodeMaskArgs) (s : Memory.State) :
    dtDecodeMaskProgSafe w d s ↔
      Fits w 2 ∧ Fits w (d.maxE + 1) ∧
      d.r0PairA + d.maxE ≤ s.frontier ∧ d.r0PairB + d.maxE ≤ s.frontier ∧
      d.edgeU + d.maxE ≤ s.frontier ∧ d.edgeV + d.maxE ≤ s.frontier ∧
      d.edgePair + d.maxE ≤ s.frontier := Iff.rfl

private def maskPrefixPairs (r mask k : ℕ) : List (Fin r × Fin r) :=
  (((allPairs r).take k).zipIdx.filter fun p => mask.testBit p.2).map Prod.fst

private theorem maskPrefixPairs_succ {r mask k : ℕ} (hk : k < r.choose 2) :
    maskPrefixPairs r mask (k + 1) =
      maskPrefixPairs r mask k ++
        (if mask.testBit k then
          [(allPairs r)[k]'(by rw [length_allPairs]; exact hk)]
        else []) := by
  have hk_all : k < (allPairs r).length := by rw [length_allPairs]; exact hk
  have htake : (allPairs r).take (k + 1) = (allPairs r).take k ++ [(allPairs r)[k]'hk_all] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk_all, Option.toList_some]
  dsimp only [maskPrefixPairs]
  rw [htake, List.zipIdx_append, List.length_take_of_le hk_all.le, Nat.zero_add,
    List.zipIdx_cons, List.zipIdx_nil, List.filter_append, List.map_append]
  simp only [List.filter_cons, List.filter_nil]
  split_ifs <;> simp

private theorem length_maskPrefixPairs_le (r mask k : ℕ) :
    (maskPrefixPairs r mask k).length ≤ k := by
  dsimp only [maskPrefixPairs]
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans
    (by rw [List.length_zipIdx, List.length_take]; exact Nat.min_le_left _ _)

private theorem dtDecodeMaskProg_core {w r0 r0PairA r0PairB edgeU edgeV edgePair mask : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (h2 : Fits w 2)
    (hmax : Fits w (r0.choose 2 + 1))
    (ha_lt : r0PairA + r0.choose 2 ≤ s.frontier)
    (hb_lt : r0PairB + r0.choose 2 ≤ s.frontier)
    (hu_lt : edgeU + r0.choose 2 ≤ s.frontier)
    (hv_lt : edgeV + r0.choose 2 ≤ s.frontier)
    (hp_lt : edgePair + r0.choose 2 ≤ s.frontier)
    (hpairs : ∀ k (hk : k < r0.choose 2),
      s.mem (r0PairA + k) = ((allPairs r0)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
      s.mem (r0PairB + k) = ((allPairs r0)[k]'(by rw [length_allPairs]; exact hk)).2.val)
    (hduv : edgeU + r0.choose 2 ≤ edgeV ∨ edgeV + r0.choose 2 ≤ edgeU)
    (hdup : edgeU + r0.choose 2 ≤ edgePair ∨ edgePair + r0.choose 2 ≤ edgeU)
    (hdvp : edgeV + r0.choose 2 ≤ edgePair ∨ edgePair + r0.choose 2 ≤ edgeV)
    (hdua : edgeU + r0.choose 2 ≤ r0PairA ∨ r0PairA + r0.choose 2 ≤ edgeU)
    (hdub : edgeU + r0.choose 2 ≤ r0PairB ∨ r0PairB + r0.choose 2 ≤ edgeU)
    (hdva : edgeV + r0.choose 2 ≤ r0PairA ∨ r0PairA + r0.choose 2 ≤ edgeV)
    (hdvb : edgeV + r0.choose 2 ≤ r0PairB ∨ r0PairB + r0.choose 2 ≤ edgeV)
    (hdpa : edgePair + r0.choose 2 ≤ r0PairA ∨ r0PairA + r0.choose 2 ≤ edgePair)
    (hdpb : edgePair + r0.choose 2 ≤ r0PairB ∨ r0PairB + r0.choose 2 ≤ edgePair) :
    let maxE := r0.choose 2
    let env : DTDecodeMaskEnv := ⟨r0PairA, r0PairB, edgeU, edgeV, edgePair, mask⟩
    let d : DTDecodeMaskArgs := ⟨r0PairA, r0PairB, edgeU, edgeV, edgePair, mask, maxE⟩
    let pairs := maskEdgePairs r0 mask
    iterationSafe dtDecodeMaskStep dtDecodeMaskStepSafe w env maxE ⟨0, 0⟩ s ∧
    Memory.FramedTriple w s (dtDecodeMaskProg d) (5 * maxE)
      (Set.Ico edgeU (edgeU + maxE) ∪ Set.Ico edgeV (edgeV + maxE) ∪
        Set.Ico edgePair (edgePair + maxE))
      fun res s' =>
        res = pairs.length ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j (hj : j < pairs.length),
          s'.mem (edgeU + j) = (pairs[j]).1.val ∧
          s'.mem (edgeV + j) = (pairs[j]).2.val ∧
          s'.mem (edgePair + j) = pairIdx (pairs[j]).1.val (pairs[j]).2.val := by
  let maxE := r0.choose 2
  let env : DTDecodeMaskEnv := ⟨r0PairA, r0PairB, edgeU, edgeV, edgePair, mask⟩
  let S : Set ℕ := Set.Ico edgeU (edgeU + maxE) ∪ Set.Ico edgeV (edgeV + maxE) ∪
    Set.Ico edgePair (edgePair + maxE)
  let inv (k : ℕ) (st : DTIdxPair) (t : Memory.State) : Prop :=
    st.idx = k ∧ st.acc = (maskPrefixPairs r0 mask k).length ∧
    t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ a < s.frontier, a ∉ S → t.mem a = s.mem a) ∧
    ∀ j (hj : j < (maskPrefixPairs r0 mask k).length),
      t.mem (edgeU + j) = ((maskPrefixPairs r0 mask k)[j]).1.val ∧
      t.mem (edgeV + j) = ((maskPrefixPairs r0 mask k)[j]).2.val ∧
      t.mem (edgePair + j) =
        pairIdx ((maskPrefixPairs r0 mask k)[j]).1.val ((maskPrefixPairs r0 mask k)[j]).2.val
  have hstep : ∀ k < maxE, ∀ st t, inv k st t →
      dtDecodeMaskStepSafe w (env, st) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (dtDecodeMaskStep (env, st))) ∧
      let a' := (Memory.spec 0).clientResult t (dtDecodeMaskStep (env, st))
      let t' := (Memory.spec 0).clientState t (dtDecodeMaskStep (env, st))
      memoryCost (dtDecodeMaskStep (env, st)) t + 0 ≤ 0 + 5 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk st t ⟨hidx, hacc, htfr, hwt, htmod, hprev⟩
    dsimp only [maxE] at hk
    rcases st with ⟨sidx, sacc⟩
    dsimp only at hidx hacc
    subst sidx
    have haccle : sacc ≤ k := hacc ▸ length_maskPrefixPairs_le r0 mask k
    have hpref_step := maskPrefixPairs_succ (r := r0) (mask := mask) hk
    have ha_not : r0PairA + k ∉ S := by
      dsimp only [S]
      simp only [Set.mem_union, Set.mem_Ico]
      rcases hdua with h | h <;> rcases hdva with h1 | h1 <;> rcases hdpa with h2 | h2 <;> omega
    have hb_not : r0PairB + k ∉ S := by
      dsimp only [S]
      simp only [Set.mem_union, Set.mem_Ico]
      rcases hdub with h | h <;> rcases hdvb with h1 | h1 <;> rcases hdpb with h2 | h2 <;> omega
    have hpa : t.mem (r0PairA + k) =
        ((allPairs r0)[k]'(by rw [length_allPairs]; exact hk)).1.val :=
      (htmod _ (by omega) ha_not).trans (hpairs k hk).1
    have hpb : t.mem (r0PairB + k) =
        ((allPairs r0)[k]'(by rw [length_allPairs]; exact hk)).2.val :=
      (htmod _ (by omega) hb_not).trans (hpairs k hk).2
    have htri_raw : Memory.FramedTriple w t (dtDecodeMaskStep (env, ⟨k, sacc⟩)) 5 S
        fun a' t' =>
          a'.idx = k + 1 ∧ a'.acc = (maskPrefixPairs r0 mask (k + 1)).length ∧
          t'.frontier = s.frontier ∧
          (∀ a < s.frontier, a ∉ S → t'.mem a = s.mem a) ∧
          ∀ j (hj : j < (maskPrefixPairs r0 mask (k + 1)).length),
            t'.mem (edgeU + j) = ((maskPrefixPairs r0 mask (k + 1))[j]).1.val ∧
            t'.mem (edgeV + j) = ((maskPrefixPairs r0 mask (k + 1))[j]).2.val ∧
            t'.mem (edgePair + j) =
              pairIdx ((maskPrefixPairs r0 mask (k + 1))[j]).1.val
                ((maskPrefixPairs r0 mask (k + 1))[j]).2.val := by
      dsimp only [dtDecodeMaskStep, env]
      have htri_inner : Memory.FramedTriple w t
          (Memory.read (r0PairA + k) >>= fun a =>
            Memory.read (r0PairB + k) >>= fun b =>
              if (mask >>> k) &&& 1 = 1 then
                Memory.write (edgeU + sacc) a >>= fun _ =>
                  Memory.write (edgeV + sacc) b >>= fun _ =>
                    Memory.write (edgePair + sacc) k >>= fun _ =>
                      pure (⟨k + 1, sacc + 1⟩ : DTIdxPair)
              else pure (⟨k + 1, sacc⟩ : DTIdxPair))
          (3 + 1 + 1) S fun a' t' =>
            a'.idx = k + 1 ∧ a'.acc = (maskPrefixPairs r0 mask (k + 1)).length ∧
            t'.frontier = s.frontier ∧
            (∀ a < s.frontier, a ∉ S → t'.mem a = s.mem a) ∧
            ∀ j (hj : j < (maskPrefixPairs r0 mask (k + 1)).length),
              t'.mem (edgeU + j) = ((maskPrefixPairs r0 mask (k + 1))[j]).1.val ∧
              t'.mem (edgeV + j) = ((maskPrefixPairs r0 mask (k + 1))[j]).2.val ∧
              t'.mem (edgePair + j) =
                pairIdx ((maskPrefixPairs r0 mask (k + 1))[j]).1.val
                  ((maskPrefixPairs r0 mask (k + 1))[j]).2.val := by
        refine Memory.FramedTriple.read_bind (by omega) ?_
        refine Memory.FramedTriple.read_bind (by omega) ?_
        refine Memory.FramedTriple.ite (c := 3) ?_ ?_
        · intro hbit
          have htb : mask.testBit k = true := (testBit_eq_decide_shift_and mask k).mp hbit
          refine Memory.FramedTriple.write_bind_of_mem (by omega) (hwt.mem_fits _)
            (Set.mem_union_left _ (Set.mem_union_left _ ⟨by omega, by omega⟩)) ?_
          refine Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega) (hwt.mem_fits _)
            (Set.mem_union_left _ (Set.mem_union_right _ ⟨by omega, by omega⟩)) ?_
          refine Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega)
            (hmax.of_le (by omega)) (Set.mem_union_right _ ⟨by omega, by omega⟩) ?_
          refine Memory.FramedTriple.pure ⟨rfl, ?_, htfr, fun a ha haS => ?_, fun j hj => ?_⟩
          · rw [hpref_step]; simp [htb, hacc]
          · dsimp only
            have ha1 : a ≠ edgeU + sacc := fun h => haS (h ▸ Set.mem_union_left _
              (Set.mem_union_left _ ⟨by omega, by omega⟩))
            have ha2 : a ≠ edgeV + sacc := fun h => haS (h ▸ Set.mem_union_left _
              (Set.mem_union_right _ ⟨by omega, by omega⟩))
            have ha3 : a ≠ edgePair + sacc := fun h => haS (h ▸ Set.mem_union_right _
              ⟨by omega, by omega⟩)
            rw [Function.update_of_ne ha3, Function.update_of_ne ha2, Function.update_of_ne ha1]
            exact htmod a ha haS
          · dsimp only
            simp only [hpref_step, htb, ↓reduceIte] at hj ⊢
            by_cases hjk : j < (maskPrefixPairs r0 mask k).length
            · rw [List.getElem_append_left hjk]
              have hne1 : edgeU + j ≠ edgePair + sacc := by rcases hdup with h | h <;> omega
              have hne2 : edgeU + j ≠ edgeV + sacc := by rcases hduv with h | h <;> omega
              have hne3 : edgeU + j ≠ edgeU + sacc := by omega
              have hne4 : edgeV + j ≠ edgePair + sacc := by rcases hdvp with h | h <;> omega
              have hne5 : edgeV + j ≠ edgeV + sacc := by omega
              have hne6 : edgeV + j ≠ edgeU + sacc := by rcases hduv with h | h <;> omega
              have hne7 : edgePair + j ≠ edgePair + sacc := by omega
              have hne8 : edgePair + j ≠ edgeV + sacc := by rcases hdvp with h | h <;> omega
              have hne9 : edgePair + j ≠ edgeU + sacc := by rcases hdup with h | h <;> omega
              rw [Function.update_of_ne hne1, Function.update_of_ne hne2,
                Function.update_of_ne hne3, Function.update_of_ne hne4,
                Function.update_of_ne hne5, Function.update_of_ne hne6,
                Function.update_of_ne hne7, Function.update_of_ne hne8,
                Function.update_of_ne hne9]
              exact hprev j hjk
            · have hje : j = (maskPrefixPairs r0 mask k).length := by
                rw [List.length_append, List.length_singleton] at hj; omega
              subst hje
              rw [List.getElem_append_right le_rfl]
              simp only [Nat.sub_self, List.getElem_singleton, ← hacc]
              have hu_eq : (Function.update (Function.update (Function.update t.mem
                  (edgeU + sacc) (t.mem (r0PairA + k))) (edgeV + sacc) (t.mem (r0PairB + k)))
                  (edgePair + sacc) k) (edgeU + sacc) = t.mem (r0PairA + k) := by
                rw [Function.update_of_ne (by rcases hdup with h | h <;> omega),
                  Function.update_of_ne (by rcases hduv with h | h <;> omega),
                  Function.update_self]
              have hv_eq : (Function.update (Function.update (Function.update t.mem
                  (edgeU + sacc) (t.mem (r0PairA + k))) (edgeV + sacc) (t.mem (r0PairB + k)))
                  (edgePair + sacc) k) (edgeV + sacc) = t.mem (r0PairB + k) := by
                rw [Function.update_of_ne (by rcases hdvp with h | h <;> omega),
                  Function.update_self]
              rw [hu_eq, hv_eq, Function.update_self, hpa, hpb,
                pairIdx_getElem_allPairs (by rw [length_allPairs]; exact hk)]
              exact ⟨rfl, rfl, rfl⟩
        · intro hbit
          have htb : mask.testBit k = false :=
            Bool.eq_false_iff.mpr fun h => hbit ((testBit_eq_decide_shift_and mask k).mpr h)
          refine Memory.FramedTriple.pure ⟨rfl, ?_, htfr, htmod, fun j hj => ?_⟩
          · rw [hpref_step]; simp [htb, hacc]
          · simp only [hpref_step, htb, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hj ⊢
            exact hprev j hj
      exact htri_inner
    have htri : Memory.FramedTriple w t (dtDecodeMaskStep (env, ⟨k, sacc⟩)) 5 S (inv (k + 1)) := by
      refine (htri_raw.wellFormed hwt).mono le_rfl ?_
      rintro _ _ ⟨⟨h1, h2', hfr, hmod', hvals⟩, hwf'⟩
      exact ⟨h1, h2', hfr, hwf', hmod', hvals⟩
    obtain ⟨hvh, hcost, hmod, hinv_next⟩ := framedTriple_iff_realization.mp htri
    exact ⟨⟨h2, hmax.of_le (by dsimp only; omega), hmax.of_le (by dsimp only; omega), hvh⟩,
      hvh, by omega, hmod, hinv_next⟩
  have hfull : maskPrefixPairs r0 mask maxE = maskEdgePairs r0 mask := by
    dsimp only [maskPrefixPairs, maskEdgePairs, maxE]
    rw [List.take_of_length_le (length_allPairs r0).le]
  obtain ⟨hsafe, hv, hm, hmod, inv_end⟩ :=
    iterate_potential_spec dtDecodeMaskStep dtDecodeMaskStepSafe w env 5 maxE
      inv (fun _ _ _ => 0) S hstep ⟨0, 0⟩ s
      ⟨rfl, by simp [maskPrefixPairs], rfl, hwf, fun _ _ _ => rfl,
        fun j hj => by simp [maskPrefixPairs] at hj⟩
  have hloop : Memory.FramedTriple w s (iterate dtDecodeMaskStep env maxE ⟨0, 0⟩) (5 * maxE) S
      fun res s' =>
        res.acc = (maskEdgePairs r0 mask).length ∧ s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j (hj : j < (maskEdgePairs r0 mask).length),
          s'.mem (edgeU + j) = ((maskEdgePairs r0 mask)[j]).1.val ∧
          s'.mem (edgeV + j) = ((maskEdgePairs r0 mask)[j]).2.val ∧
          s'.mem (edgePair + j) =
            pairIdx ((maskEdgePairs r0 mask)[j]).1.val ((maskEdgePairs r0 mask)[j]).2.val :=
    framedTriple_iff_realization.mpr
      ⟨hv, by simpa [Nat.mul_comm] using hm, hmod,
        by rw [inv_end.2.1, hfull], inv_end.2.2.1, inv_end.2.2.2.1,
        by simpa [hfull] using inv_end.2.2.2.2.2⟩
  refine ⟨hsafe, ?_⟩
  dsimp only [dtDecodeMaskProg]
  have hloop' : Memory.FramedTriple w s (iterate dtDecodeMaskStep env maxE ⟨0, 0⟩) (5 * maxE) S
      fun res s' => Memory.FramedTriple w s' (pure res.acc) 0 S fun res s' =>
        res = (maskEdgePairs r0 mask).length ∧ s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j (hj : j < (maskEdgePairs r0 mask).length),
          s'.mem (edgeU + j) = ((maskEdgePairs r0 mask)[j]).1.val ∧
          s'.mem (edgeV + j) = ((maskEdgePairs r0 mask)[j]).2.val ∧
          s'.mem (edgePair + j) =
            pairIdx ((maskEdgePairs r0 mask)[j]).1.val ((maskEdgePairs r0 mask)[j]).2.val :=
    hloop.mono le_rfl fun _ _ h => Memory.FramedTriple.pure h
  exact hloop'.bind_same.mono (by omega) fun _ _ h => h

/-- Framed specification for `dtDecodeMaskProg`. -/
theorem dtDecodeMaskProg_spec {w r0 : ℕ} {d : DTDecodeMaskArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtDecodeMaskProgSafe w d s)
    (hmaxE : d.maxE = r0.choose 2)
    (hpairs : ∀ k (hk : k < r0.choose 2),
      s.mem (d.r0PairA + k) = ((allPairs r0)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
      s.mem (d.r0PairB + k) = ((allPairs r0)[k]'(by rw [length_allPairs]; exact hk)).2.val)
    (hduv : d.edgeU + r0.choose 2 ≤ d.edgeV ∨ d.edgeV + r0.choose 2 ≤ d.edgeU)
    (hdup : d.edgeU + r0.choose 2 ≤ d.edgePair ∨ d.edgePair + r0.choose 2 ≤ d.edgeU)
    (hdvp : d.edgeV + r0.choose 2 ≤ d.edgePair ∨ d.edgePair + r0.choose 2 ≤ d.edgeV)
    (hdua : d.edgeU + r0.choose 2 ≤ d.r0PairA ∨ d.r0PairA + r0.choose 2 ≤ d.edgeU)
    (hdub : d.edgeU + r0.choose 2 ≤ d.r0PairB ∨ d.r0PairB + r0.choose 2 ≤ d.edgeU)
    (hdva : d.edgeV + r0.choose 2 ≤ d.r0PairA ∨ d.r0PairA + r0.choose 2 ≤ d.edgeV)
    (hdvb : d.edgeV + r0.choose 2 ≤ d.r0PairB ∨ d.r0PairB + r0.choose 2 ≤ d.edgeV)
    (hdpa : d.edgePair + r0.choose 2 ≤ d.r0PairA ∨ d.r0PairA + r0.choose 2 ≤ d.edgePair)
    (hdpb : d.edgePair + r0.choose 2 ≤ d.r0PairB ∨ d.r0PairB + r0.choose 2 ≤ d.edgePair) :
    Memory.FramedTriple w s (dtDecodeMaskProg d) (5 * d.maxE)
      (Set.Ico d.edgeU (d.edgeU + d.maxE) ∪ Set.Ico d.edgeV (d.edgeV + d.maxE) ∪
        Set.Ico d.edgePair (d.edgePair + d.maxE))
      fun res s' =>
        res = (maskEdgePairs r0 d.mask).length ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j (hj : j < (maskEdgePairs r0 d.mask).length),
          s'.mem (d.edgeU + j) = ((maskEdgePairs r0 d.mask)[j]).1.val ∧
          s'.mem (d.edgeV + j) = ((maskEdgePairs r0 d.mask)[j]).2.val ∧
          s'.mem (d.edgePair + j) =
            pairIdx ((maskEdgePairs r0 d.mask)[j]).1.val ((maskEdgePairs r0 d.mask)[j]).2.val := by
  rcases d with ⟨r0PairA, r0PairB, edgeU, edgeV, edgePair, mask, maxE⟩
  dsimp only at hmaxE hsafe hpairs hduv hdup hdvp hdua hdub hdva hdvb hdpa hdpb ⊢
  subst hmaxE
  have hmax : Fits w (r0.choose 2 + 1) := hsafe.2.1
  have ha_lt : r0PairA + r0.choose 2 ≤ s.frontier := hsafe.2.2.1
  have hb_lt : r0PairB + r0.choose 2 ≤ s.frontier := hsafe.2.2.2.1
  have hu_lt : edgeU + r0.choose 2 ≤ s.frontier := hsafe.2.2.2.2.1
  have hv_lt : edgeV + r0.choose 2 ≤ s.frontier := hsafe.2.2.2.2.2.1
  have hp_lt : edgePair + r0.choose 2 ≤ s.frontier := hsafe.2.2.2.2.2.2
  exact (dtDecodeMaskProg_core hwf hsafe.1 hmax ha_lt hb_lt hu_lt hv_lt hp_lt hpairs
    hduv hdup hdvp hdua hdub hdva hdvb hdpa hdpb).2

private theorem realizes_dtDecodeMaskProg_raw : Realizes .exact
    dtDecodeMaskProg dtDecodeMaskArgsWords WordEncoding.encode
    (fun w d s => iterationSafe dtDecodeMaskStep dtDecodeMaskStepSafe w
      ⟨d.r0PairA, d.r0PairB, d.edgeU, d.edgeV, d.edgePair, d.mask⟩ d.maxE ⟨0, 0⟩ s)
    (fun _ _ => 0) := by
  unfold dtDecodeMaskProg
  realize [realizes_dtDecodeMaskStep]
  exact iterationSafe_imp h (fun _ => rfl) (fun _ _ hs => hs)

private theorem dtDecodeMaskProg_safe_raw {w : ℕ} {d : DTDecodeMaskArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtDecodeMaskProgSafe w d s) :
    iterationSafe dtDecodeMaskStep dtDecodeMaskStepSafe w
      ⟨d.r0PairA, d.r0PairB, d.edgeU, d.edgeV, d.edgePair, d.mask⟩ d.maxE ⟨0, 0⟩ s := by
  rcases d with ⟨r0PairA, r0PairB, edgeU, edgeV, edgePair, mask, maxE⟩
  dsimp only [dtDecodeMaskProgSafe] at hsafe
  obtain ⟨h2, hmax, ha_lt, hb_lt, hu_lt, hv_lt, hp_lt⟩ := hsafe
  dsimp only
  let env : DTDecodeMaskEnv := ⟨r0PairA, r0PairB, edgeU, edgeV, edgePair, mask⟩
  let inv (k : ℕ) (st : DTIdxPair) (t : Memory.State) : Prop :=
    st.idx = k ∧ st.acc ≤ k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t
  have hstep : ∀ k < maxE, ∀ st t, inv k st t →
      dtDecodeMaskStepSafe w (env, st) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (dtDecodeMaskStep (env, st))) ∧
      let a' := (Memory.spec 0).clientResult t (dtDecodeMaskStep (env, st))
      let t' := (Memory.spec 0).clientState t (dtDecodeMaskStep (env, st))
      memoryCost (dtDecodeMaskStep (env, st)) t + 0 ≤ 0 + 5 ∧
      Memory.Modifies Set.univ t t' ∧
      inv (k + 1) a' t' := by
    intro k hk st t ⟨hidx, haccle, htfr, hwt⟩
    rcases st with ⟨sidx, sacc⟩
    dsimp only at hidx haccle
    subst sidx
    have htri_raw : Memory.FramedTriple w t (dtDecodeMaskStep (env, ⟨k, sacc⟩)) 5 Set.univ
        fun a' t' => a'.idx = k + 1 ∧ a'.acc ≤ k + 1 ∧ t'.frontier = s.frontier := by
      dsimp only [dtDecodeMaskStep, env]
      refine (Memory.FramedTriple.read_bind (by omega) ?_)
      refine Memory.FramedTriple.read_bind (by omega) ?_
      refine Memory.FramedTriple.ite (c := 3) ?_ ?_
      · intro _
        refine Memory.FramedTriple.write_bind_of_mem (by omega) (hwt.mem_fits _)
          (Set.mem_univ _) ?_
        refine Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega) (hwt.mem_fits _)
          (Set.mem_univ _) ?_
        refine Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega)
          (hmax.of_le (by omega)) (Set.mem_univ _) ?_
        exact Memory.FramedTriple.pure ⟨rfl, by dsimp only; omega, htfr⟩
      · intro _
        exact Memory.FramedTriple.pure ⟨rfl, by dsimp only; omega, htfr⟩
    have htri : Memory.FramedTriple w t (dtDecodeMaskStep (env, ⟨k, sacc⟩)) 5 Set.univ
        (inv (k + 1)) := by
      refine (htri_raw.wellFormed hwt).mono le_rfl ?_
      rintro _ _ ⟨⟨h1, h2', hfr⟩, hwf'⟩
      exact ⟨h1, h2', hfr, hwf'⟩
    obtain ⟨hvh, hcost, hmod, hinv_next⟩ := framedTriple_iff_realization.mp htri
    exact ⟨⟨h2, hmax.of_le (by dsimp only; omega), hmax.of_le (by dsimp only; omega), hvh⟩,
      hvh, by omega, hmod, hinv_next⟩
  exact (iterate_potential_spec dtDecodeMaskStep dtDecodeMaskStepSafe w env 5 maxE
    inv (fun _ _ _ => 0) Set.univ hstep ⟨0, 0⟩ s ⟨rfl, le_rfl, rfl, hwf⟩).1

/-- `dtDecodeMaskProg` is uniformly realized with `work = 0`. -/
theorem realizes_dtDecodeMaskProg : Realizes .exact
    dtDecodeMaskProg dtDecodeMaskArgsWords WordEncoding.encode
    dtDecodeMaskProgSafe (fun _ _ => 0) :=
  realizes_dtDecodeMaskProg_raw.consequence
    (fun _ _ _ _ hwf hs => dtDecodeMaskProg_safe_raw hwf hs)
    (fun _ _ => le_rfl)

/-! ## Section 6: In-Memory Kruskal (`dtKruskalMaskProg`) -/

private theorem merge_eq_iff (a b cu cv : ℕ) :
    (if a = cu then cv else a) = (if b = cu then cv else b) ↔
      a = b ∨ (a = cu ∧ b = cv) ∨ (a = cv ∧ b = cu) := by
  split_ifs <;> omega

private theorem dtKruskalMerge_core {w r0 compArr cu cv rk idx msfMask : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h2 : Fits w 2) (hr0_fit : Fits w (r0 + 1))
    (hrk : Fits w (rk + 1)) (hmsf : Fits w (msfMask ||| (1 <<< idx)))
    (hca : compArr + r0 ≤ s.frontier) (hcv : Fits w cv) :
    let d : DTKruskalMergeArgs := ⟨r0, compArr, cu, cv, rk, idx, msfMask⟩
    dtKruskalMergeSafe w d s ∧
    Memory.FramedTriple w s (dtKruskalMerge d) (2 * r0) (Set.Ico compArr (compArr + r0))
      fun res s' =>
        res = ⟨rk + 1, if cu = cv then msfMask else msfMask ||| (1 <<< idx)⟩ ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        (∀ a < s.frontier, a ∉ Set.Ico compArr (compArr + r0) → s'.mem a = s.mem a) ∧
        ∀ x < r0, s'.mem (compArr + x) =
          if s.mem (compArr + x) = cu then cv else s.mem (compArr + x) := by
  by_cases heq : cu = cv
  · refine ⟨⟨h2, hrk, fun hne => absurd heq hne⟩, ?_⟩
    dsimp only [dtKruskalMerge]
    simp only [heq, ↓reduceIte]
    exact Memory.FramedTriple.pure
      ⟨rfl, rfl, hwf, fun _ _ _ => rfl,
        fun x _ => by split_ifs with h <;> first | exact h | rfl⟩
  · let S : Set ℕ := Set.Ico compArr (compArr + r0)
    let inv (k st : ℕ) (t : Memory.State) : Prop :=
      st = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
      ∀ x < r0, t.mem (compArr + x) =
        if x < k then (if s.mem (compArr + x) = cu then cv else s.mem (compArr + x))
        else s.mem (compArr + x)
    have hstep : ∀ k < r0, ∀ st t, inv k st t →
        dtMergeCompStepSafe w (⟨compArr, cu, cv⟩, st) t ∧
        (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (dtMergeCompStep (⟨compArr, cu, cv⟩, st))) ∧
        let a' := (Memory.spec 0).clientResult t (dtMergeCompStep (⟨compArr, cu, cv⟩, st))
        let t' := (Memory.spec 0).clientState t (dtMergeCompStep (⟨compArr, cu, cv⟩, st))
        memoryCost (dtMergeCompStep (⟨compArr, cu, cv⟩, st)) t + 0 ≤ 0 + 2 ∧
        Memory.Modifies S t t' ∧
        inv (k + 1) a' t' := by
      intro k hk st t ⟨hst_eq, htfr, hwt, hprev⟩
      subst st
      have hcur : t.mem (compArr + k) = s.mem (compArr + k) := by rw [hprev k hk]; simp
      have htri_raw : Memory.FramedTriple w t (dtMergeCompStep (⟨compArr, cu, cv⟩, k)) 2 S
          fun a' t' =>
            a' = k + 1 ∧ t'.frontier = s.frontier ∧
            ∀ x < r0, t'.mem (compArr + x) =
              if x < k + 1 then (if s.mem (compArr + x) = cu then cv else s.mem (compArr + x))
              else s.mem (compArr + x) := by
        dsimp only [dtMergeCompStep]
        refine Memory.FramedTriple.read_bind (by omega) ?_
        refine Memory.FramedTriple.ite (c := 1) ?_ ?_
        · intro hcu
          refine Memory.FramedTriple.write_bind_of_mem (by omega) hcv ⟨by omega, by omega⟩ ?_
          refine Memory.FramedTriple.pure ⟨rfl, htfr, fun x hx => ?_⟩
          dsimp only
          by_cases hxk : x < k
          · rw [Function.update_of_ne (by omega), hprev x hx]; simp [hxk, show x < k + 1 by omega]
          · by_cases hxek : x = k
            · subst hxek; rw [Function.update_self, ← hcur]; simp [hcu]
            · rw [Function.update_of_ne (by omega), hprev x hx]
              simp [hxk, show ¬ x < k + 1 by omega]
        · intro hncu
          refine Memory.FramedTriple.pure ⟨rfl, htfr, fun x hx => ?_⟩
          rw [hprev x hx]
          by_cases hxk : x < k
          · simp [hxk, show x < k + 1 by omega]
          · by_cases hxek : x = k
            · subst hxek; rw [← hcur]; simp [hncu]
            · simp [hxk, show ¬ x < k + 1 by omega]
      have htri : Memory.FramedTriple w t (dtMergeCompStep (⟨compArr, cu, cv⟩, k)) 2 S
          (inv (k + 1)) := by
        refine (htri_raw.wellFormed hwt).mono le_rfl ?_
        rintro _ _ ⟨⟨h1, hfr, hvals⟩, hwf'⟩
        exact ⟨h1, hfr, hwf', hvals⟩
      obtain ⟨hvh, hcost, hmod, hinv_next⟩ := framedTriple_iff_realization.mp htri
      exact ⟨⟨hr0_fit.of_le (by omega), hvh⟩, hvh, by omega, hmod, hinv_next⟩
    obtain ⟨hsafe, hv, hm, hmod, inv_end⟩ :=
      iterate_potential_spec dtMergeCompStep dtMergeCompStepSafe w ⟨compArr, cu, cv⟩ 2 r0
        inv (fun _ _ _ => 0) S hstep 0 s ⟨rfl, rfl, hwf, fun x hx => by simp⟩
    have hloop : Memory.FramedTriple w s (iterate dtMergeCompStep ⟨compArr, cu, cv⟩ r0 0)
        (2 * r0) S fun _ s' =>
          s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
          (∀ a < s.frontier, a ∉ S → s'.mem a = s.mem a) ∧
          ∀ x < r0, s'.mem (compArr + x) =
            if s.mem (compArr + x) = cu then cv else s.mem (compArr + x) :=
      framedTriple_iff_realization.mpr ⟨hv, by simpa [Nat.mul_comm] using hm, hmod,
        inv_end.2.1, inv_end.2.2.1, fun a ha haS => hmod.mem_eq_of_not_mem ha haS,
        fun x hx => by simpa [hx] using inv_end.2.2.2 x hx⟩
    refine ⟨⟨h2, hrk, fun _ => ⟨hmsf, hsafe⟩⟩, ?_⟩
    dsimp only [dtKruskalMerge]
    simp only [heq, ↓reduceIte]
    have hloop' : Memory.FramedTriple w s (iterate dtMergeCompStep ⟨compArr, cu, cv⟩ r0 0)
        (2 * r0) S fun _ s' =>
          Memory.FramedTriple w s' (pure (⟨rk + 1, msfMask ||| (1 <<< idx)⟩ : DTIdxPair)) 0 S
            fun res s' =>
              res = (⟨rk + 1, msfMask ||| (1 <<< idx)⟩ : DTIdxPair) ∧
              s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
              (∀ a < s.frontier, a ∉ S → s'.mem a = s.mem a) ∧
              ∀ x < r0, s'.mem (compArr + x) =
                if s.mem (compArr + x) = cu then cv else s.mem (compArr + x) :=
      hloop.mono le_rfl fun _ _ h => Memory.FramedTriple.pure ⟨rfl, h⟩
    exact hloop'.bind_same.mono (by omega) fun _ _ h => h

private theorem dtKruskalEdgeStep_triple {w r0 edgeU edgeV orderArr compArr rk sacc : ℕ}
    {t : Memory.State} {S : Set ℕ} {Q : DTIdxPair → Memory.State → Prop}
    (ho : orderArr + rk < t.frontier)
    (hu : edgeU + t.mem (orderArr + rk) < t.frontier)
    (hv : edgeV + t.mem (orderArr + rk) < t.frontier)
    (hcu : compArr + t.mem (edgeU + t.mem (orderArr + rk)) < t.frontier)
    (hcv : compArr + t.mem (edgeV + t.mem (orderArr + rk)) < t.frontier)
    (hmerge : Memory.FramedTriple w t
      (dtKruskalMerge ⟨r0, compArr,
        t.mem (compArr + t.mem (edgeU + t.mem (orderArr + rk))),
        t.mem (compArr + t.mem (edgeV + t.mem (orderArr + rk))),
        rk, t.mem (orderArr + rk), sacc⟩)
      (2 * r0) S Q) :
    Memory.FramedTriple w t
      (dtKruskalEdgeStep (⟨r0, edgeU, edgeV, orderArr, compArr⟩, ⟨rk, sacc⟩))
      (5 + 2 * r0) S Q := by
  dsimp only [dtKruskalEdgeStep]
  rw [show 5 + 2 * r0 = 2 * r0 + 1 + 1 + 1 + 1 + 1 by omega]
  refine Memory.FramedTriple.read_bind ho ?_
  refine Memory.FramedTriple.read_bind hu ?_
  refine Memory.FramedTriple.read_bind hv ?_
  refine Memory.FramedTriple.read_bind hcu ?_
  exact Memory.FramedTriple.read_bind hcv hmerge

/-- Runs in-memory Kruskal on the edge permutation stored in `d.orderArr[0..d.e-1]`, returning the
bitmask `maskOfFinset (Cslib.Multigraph.msf ends p Finset.univ)`. -/
def dtKruskalMaskProg (d : DTKruskalProgArgs) : Memory.Prog ℕ := do
  let _ ← iterate dtInitIdStep d.compArr d.r0 0
  let res ← iterate dtKruskalEdgeStep ⟨d.r0, d.edgeU, d.edgeV, d.orderArr, d.compArr⟩ d.e ⟨0, 0⟩
  pure res.acc

/-- Word-RAM safety precondition for `dtKruskalMaskProg`. -/
def dtKruskalMaskProgSafe (w : ℕ) (d : DTKruskalProgArgs) (s : Memory.State) : Prop :=
  Fits w 2 ∧ Fits w (d.r0 + 1) ∧ Fits w (d.e + 1) ∧ Fits w (2 ^ d.e) ∧
  d.compArr + d.r0 ≤ s.frontier ∧ d.orderArr + d.e ≤ s.frontier ∧
  d.edgeU + d.e ≤ s.frontier ∧ d.edgeV + d.e ≤ s.frontier ∧
  (d.compArr + d.r0 ≤ d.orderArr ∨ d.orderArr + d.e ≤ d.compArr) ∧
  (d.compArr + d.r0 ≤ d.edgeU ∨ d.edgeU + d.e ≤ d.compArr) ∧
  (d.compArr + d.r0 ≤ d.edgeV ∨ d.edgeV + d.e ≤ d.compArr) ∧
  (∀ rk < d.e, s.mem (d.orderArr + rk) < d.e) ∧
  (∀ i < d.e, s.mem (d.edgeU + i) < d.r0 ∧ s.mem (d.edgeV + i) < d.r0)

/-- Unfolding equivalence for `dtKruskalMaskProgSafe`. -/
theorem dtKruskalMaskProgSafe_iff (w : ℕ) (d : DTKruskalProgArgs) (s : Memory.State) :
    dtKruskalMaskProgSafe w d s ↔
      Fits w 2 ∧ Fits w (d.r0 + 1) ∧ Fits w (d.e + 1) ∧ Fits w (2 ^ d.e) ∧
      d.compArr + d.r0 ≤ s.frontier ∧ d.orderArr + d.e ≤ s.frontier ∧
      d.edgeU + d.e ≤ s.frontier ∧ d.edgeV + d.e ≤ s.frontier ∧
      (d.compArr + d.r0 ≤ d.orderArr ∨ d.orderArr + d.e ≤ d.compArr) ∧
      (d.compArr + d.r0 ≤ d.edgeU ∨ d.edgeU + d.e ≤ d.compArr) ∧
      (d.compArr + d.r0 ≤ d.edgeV ∨ d.edgeV + d.e ≤ d.compArr) ∧
      (∀ rk < d.e, s.mem (d.orderArr + rk) < d.e) ∧
      (∀ i < d.e, s.mem (d.edgeU + i) < d.r0 ∧ s.mem (d.edgeV + i) < d.r0) := Iff.rfl

private theorem dtKruskalMaskProg_init_core {w r0 compArr : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hr0_fit : Fits w (r0 + 1)) (hca : compArr + r0 ≤ s.frontier) :
    let S : Set ℕ := Set.Ico compArr (compArr + r0)
    iterationSafe dtInitIdStep dtInitIdStepSafe w compArr r0 0 s ∧
    Memory.FramedTriple w s (iterate dtInitIdStep compArr r0 0) r0 S fun _ t =>
      t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
      ∀ x < r0, t.mem (compArr + x) = x := by
  let S : Set ℕ := Set.Ico compArr (compArr + r0)
  let initInv (k st : ℕ) (t : Memory.State) : Prop :=
    st = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    ∀ x < k, t.mem (compArr + x) = x
  have hstep : ∀ k < r0, ∀ st t, initInv k st t →
      dtInitIdStepSafe w (compArr, st) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (dtInitIdStep (compArr, st))) ∧
      let a' := (Memory.spec 0).clientResult t (dtInitIdStep (compArr, st))
      let t' := (Memory.spec 0).clientState t (dtInitIdStep (compArr, st))
      memoryCost (dtInitIdStep (compArr, st)) t + 0 ≤ 0 + 1 ∧
      Memory.Modifies S t t' ∧
      initInv (k + 1) a' t' := by
    intro k hk st t ⟨hst_eq, htfr, hwt, hprev⟩
    subst st
    have htri_raw : Memory.FramedTriple w t (dtInitIdStep (compArr, k)) 1 S fun a' t' =>
        a' = k + 1 ∧ t'.frontier = s.frontier ∧ ∀ x < k + 1, t'.mem (compArr + x) = x := by
      dsimp only [dtInitIdStep]
      refine Memory.FramedTriple.write_bind_of_mem (by omega) (hr0_fit.of_le (by omega))
        ⟨by omega, by omega⟩ ?_
      refine Memory.FramedTriple.pure ⟨rfl, htfr, fun x hx => ?_⟩
      dsimp only
      by_cases hxk : x < k
      · rw [Function.update_of_ne (by omega)]; exact hprev x hxk
      · have hxe : x = k := by omega
        subst hxe; exact Function.update_self _ _ _
    have htri : Memory.FramedTriple w t (dtInitIdStep (compArr, k)) 1 S (initInv (k + 1)) := by
      refine (htri_raw.wellFormed hwt).mono le_rfl ?_
      rintro _ _ ⟨⟨h1, hfr, hvals⟩, hwf'⟩
      exact ⟨h1, hfr, hwf', hvals⟩
    obtain ⟨hvh, hcost, hmod, hinv_next⟩ := framedTriple_iff_realization.mp htri
    exact ⟨⟨hr0_fit.of_le (by omega), hvh⟩, hvh, by omega, hmod, hinv_next⟩
  obtain ⟨hsafe, hv, hm, hmod, inv_end⟩ :=
    iterate_potential_spec dtInitIdStep dtInitIdStepSafe w compArr 1 r0 initInv
      (fun _ _ _ => 0) S hstep 0 s ⟨rfl, rfl, hwf, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe, framedTriple_iff_realization.mpr
    ⟨hv, by simpa using hm, hmod, inv_end.2.1, inv_end.2.2.1, inv_end.2.2.2⟩⟩

private theorem dtKruskalMaskProg_core {w r0 e edgeU edgeV orderArr compArr : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (h2 : Fits w 2) (hr0_fit : Fits w (r0 + 1)) (he_fit : Fits w (e + 1))
    (h2e_fit : Fits w (2 ^ e))
    (hca : compArr + r0 ≤ s.frontier) (hoa : orderArr + e ≤ s.frontier)
    (heu : edgeU + e ≤ s.frontier) (hev : edgeV + e ≤ s.frontier)
    (hco : compArr + r0 ≤ orderArr ∨ orderArr + e ≤ compArr)
    (hcu : compArr + r0 ≤ edgeU ∨ edgeU + e ≤ compArr)
    (hcv : compArr + r0 ≤ edgeV ∨ edgeV + e ≤ compArr)
    (p : Equiv.Perm (Fin e))
    (hord : ∀ rk (hrk : rk < e), s.mem (orderArr + rk) = (p.symm ⟨rk, hrk⟩).val)
    (ends : Fin e → Sym2 (Fin r0))
    (hends : ∀ i : Fin e, ∃ a b : Fin r0, ends i = s(a, b) ∧
      s.mem (edgeU + i.val) = a.val ∧ s.mem (edgeV + i.val) = b.val) :
    let d : DTKruskalProgArgs := ⟨r0, e, edgeU, edgeV, orderArr, compArr⟩
    (iterationSafe dtInitIdStep dtInitIdStepSafe w compArr r0 0 s ∧
      iterationSafe dtKruskalEdgeStep dtKruskalEdgeStepSafe w
        ⟨r0, edgeU, edgeV, orderArr, compArr⟩ e ⟨0, 0⟩
        ((Memory.spec 0).clientState s (iterate dtInitIdStep compArr r0 0))) ∧
    Memory.FramedTriple w s (dtKruskalMaskProg d) (r0 + e * (5 + 2 * r0))
      (Set.Ico compArr (compArr + r0)) fun res s' =>
        res = maskOfFinset (Cslib.Multigraph.msf ends p Finset.univ) ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' := by
  let S : Set ℕ := Set.Ico compArr (compArr + r0)
  obtain ⟨hsafe1, htri1⟩ := dtKruskalMaskProg_init_core hwf hr0_fit hca
  obtain ⟨hv1, hcost1, hmod1, hfr1, hwf1, hinit_vals⟩ := framedTriple_iff_realization.mp htri1
  let s1 := (Memory.spec 0).clientState s (iterate dtInitIdStep compArr r0 0)
  let prefE (rk : ℕ) : Set (Fin e) := {i : Fin e | (p i).val < rk}
  let prefM (rk : ℕ) : Finset (Fin e) :=
    (Cslib.Multigraph.msf ends p Finset.univ).filter fun i : Fin e => (p i).val < rk
  let kEnv : DTKruskalEnv := ⟨r0, edgeU, edgeV, orderArr, compArr⟩
  let kInv (rk : ℕ) (st : DTIdxPair) (t : Memory.State) : Prop :=
    st.idx = rk ∧ st.acc = maskOfFinset (prefM rk) ∧ t.frontier = s.frontier ∧
    Memory.WellFormed w t ∧
    (∀ a < s.frontier, a ∉ S → t.mem a = s.mem a) ∧
    (∀ x < r0, t.mem (compArr + x) < r0) ∧
    ∀ x y : Fin r0,
      t.mem (compArr + x.val) = t.mem (compArr + y.val) ↔
        Cslib.Multigraph.Joins ends (prefE rk) x y
  have hk_step : ∀ rk < e, ∀ st t, kInv rk st t →
      dtKruskalEdgeStepSafe w (kEnv, st) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (dtKruskalEdgeStep (kEnv, st))) ∧
      let a' := (Memory.spec 0).clientResult t (dtKruskalEdgeStep (kEnv, st))
      let t' := (Memory.spec 0).clientState t (dtKruskalEdgeStep (kEnv, st))
      memoryCost (dtKruskalEdgeStep (kEnv, st)) t + 0 ≤ 0 + (5 + 2 * r0) ∧
      Memory.Modifies S t t' ∧
      kInv (rk + 1) a' t' := by
    intro rk hrk st t ⟨hidx, hacc, htfr, hwt, htmod, hcomp_lt, hconn⟩
    rcases st with ⟨sidx, sacc⟩
    dsimp only at hidx hacc
    subst sidx
    let i0 : Fin e := p.symm ⟨rk, hrk⟩
    have hpi0 : (p i0).val = rk := by simp [i0]
    have hidx_val : t.mem (orderArr + rk) = i0.val := by
      rw [htmod _ (by omega)
        (by dsimp only [S]; simp only [Set.mem_Ico]; rcases hco with h | h <;> omega)]
      exact hord rk hrk
    obtain ⟨u, v, hui0, hu_orig, hv_orig⟩ := hends i0
    have hu_val : t.mem (edgeU + i0.val) = u.val := by
      rw [htmod _ (by have := i0.isLt; omega)
        (by dsimp only [S]; simp only [Set.mem_Ico]; rcases hcu with h | h <;> omega)]
      exact hu_orig
    have hv_val : t.mem (edgeV + i0.val) = v.val := by
      rw [htmod _ (by have := i0.isLt; omega)
        (by dsimp only [S]; simp only [Set.mem_Ico]; rcases hcv with h | h <;> omega)]
      exact hv_orig
    let cu := t.mem (compArr + u.val)
    let cv := t.mem (compArr + v.val)
    have hmsf_lt : sacc ||| (1 <<< i0.val) < 2 ^ e := by
      rw [hacc, Nat.shiftLeft_eq, one_mul]
      exact Nat.or_lt_two_pow (maskOfFinset_lt _) (Nat.pow_lt_pow_right (by decide) i0.isLt)
    obtain ⟨hm_safe, hm_tri⟩ := dtKruskalMerge_core (w := w) (r0 := r0) (compArr := compArr)
      (cu := cu) (cv := cv) (rk := rk) (idx := i0.val) (msfMask := sacc)
      hwt h2 hr0_fit (he_fit.of_le (by omega)) (h2e_fit.of_le hmsf_lt.le)
      (by omega) (hr0_fit.of_le (by have := hcomp_lt v.val v.isLt; omega))
    have hprefE_step : prefE (rk + 1) = insert i0 (prefE rk) := by
      ext j
      simp only [prefE, Set.mem_ofPred_eq, Set.mem_insert_iff]
      constructor
      · intro hj
        by_cases hjk : (p j).val = rk
        · left; exact p.injective (Fin.ext (hjk.trans hpi0.symm))
        · right; omega
      · rintro (rfl | hj)
        · rw [hpi0]; omega
        · omega
    have hflt_eq : {f | f ∈ (Finset.univ : Finset (Fin e)) ∧ p f < p i0} = prefE rk := by
      ext j
      simp only [Set.mem_ofPred_eq, Finset.mem_univ, true_and, prefE, Fin.lt_def, hpi0]
    have hi0_msf : i0 ∈ Cslib.Multigraph.msf ends p Finset.univ ↔ cu ≠ cv := by
      rw [Cslib.Multigraph.mem_msf_iff p hui0, hflt_eq, ← hconn u v]
      simp [cu, cv]
    have hprefM_step : prefM (rk + 1) =
        if cu = cv then prefM rk else insert i0 (prefM rk) := by
      split_ifs with heq
      · ext j
        simp only [prefM, Finset.mem_filter]
        constructor
        · rintro ⟨hj, hlt⟩
          refine ⟨hj, ?_⟩
          by_contra hge
          have hjeq : j = i0 := p.injective (Fin.ext (by omega))
          subst hjeq
          exact (hi0_msf.mp hj) heq
        · rintro ⟨hj, hlt⟩; exact ⟨hj, by omega⟩
      · ext j
        simp only [prefM, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hj, hlt⟩
          by_cases hje : (p j).val = rk
          · left; exact p.injective (Fin.ext (hje.trans hpi0.symm))
          · right; exact ⟨hj, by omega⟩
        · rintro (rfl | ⟨hj, hlt⟩)
          · exact ⟨hi0_msf.mpr heq, by rw [hpi0]; omega⟩
          · exact ⟨hj, by omega⟩
    have hacc_next : (if cu = cv then sacc else sacc ||| (1 <<< i0.val)) =
        maskOfFinset (prefM (rk + 1)) := by
      rw [hprefM_step]
      split_ifs with heq
      · exact hacc
      · rw [hacc]
        apply Nat.eq_of_testBit_eq
        intro b
        rw [testBit_or_one_shiftLeft, testBit_maskOfFinset, testBit_maskOfFinset]
        by_cases hbe : b < e
        · by_cases hbi : b = i0.val
          · subst hbi
            simp [i0.isLt, Finset.mem_insert]
          · simp [hbe, Finset.mem_insert, Fin.ext_iff, hbi]
        · simp [hbe, show b ≠ i0.val by have := i0.isLt; omega]
    have hstep_tri : Memory.FramedTriple w t (dtKruskalEdgeStep (kEnv, ⟨rk, sacc⟩))
        (5 + 2 * r0) S (kInv (rk + 1)) := by
      refine dtKruskalEdgeStep_triple (by omega) (by rw [hidx_val]; have := i0.isLt; omega)
        (by rw [hidx_val]; have := i0.isLt; omega)
        (by rw [hidx_val, hu_val]; have := u.isLt; omega)
        (by rw [hidx_val, hv_val]; have := v.isLt; omega) ?_
      rw [hidx_val, hu_val, hv_val]
      refine hm_tri.mono le_rfl fun res t' h => ?_
      rcases h with ⟨rfl, hfr, hwf', hmod_step, harr⟩
      refine ⟨rfl, hacc_next, hfr.trans htfr, hwf', fun a ha haS => ?_, fun x hx => ?_,
        fun x y => ?_⟩
      · exact (hmod_step a (by omega) haS).trans (htmod a ha haS)
      · rw [harr x hx]; split_ifs
        · exact hcomp_lt v.val v.isLt
        · exact hcomp_lt x hx
      · rw [harr x.val x.isLt, harr y.val y.isLt, merge_eq_iff, hprefE_step,
          Cslib.Multigraph.joins_insert_iff]
        simp only [← hconn]
        constructor
        · rintro (hxy | ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩)
          · exact Or.inl hxy
          · exact Or.inr ⟨u, v, hui0, hxu, hyv.symm⟩
          · exact Or.inr ⟨v, u, hui0.trans Sym2.eq_swap, hxv, hyu.symm⟩
        · rintro (hxy | ⟨a', b', hab', hxa', hb'y⟩)
          · exact Or.inl hxy
          · rw [hui0, Sym2.eq_iff] at hab'
            rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr (Or.inl ⟨hxa', hb'y.symm⟩)
            · exact Or.inr (Or.inr ⟨hxa', hb'y.symm⟩)
    obtain ⟨hvh, hcost, hmod, hinv_next⟩ := framedTriple_iff_realization.mp hstep_tri
    have hsafe_step : dtKruskalEdgeStepSafe w (kEnv, ⟨rk, sacc⟩) t := by
      dsimp only [dtKruskalEdgeStepSafe, kEnv]
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hidx_val]; have := i0.isLt; omega
      · rw [hidx_val]; have := i0.isLt; omega
      · rw [hidx_val, hu_val]; have := u.isLt; omega
      · rw [hidx_val, hv_val]; have := v.isLt; omega
      · simp only [hidx_val, hu_val, hv_val]; exact hm_safe
    exact ⟨hsafe_step, hvh, by omega, hmod, hinv_next⟩
  have hk_init : kInv 0 ⟨0, 0⟩ s1 := by
    refine ⟨rfl, by simp [prefM, maskOfFinset], hfr1, hwf1,
      fun a ha haS => hmod1.mem_eq_of_not_mem ha haS,
      fun x hx => by rw [hinit_vals x hx]; exact hx, fun x y => ?_⟩
    rw [hinit_vals x.val x.isLt, hinit_vals y.val y.isLt,
      show prefE 0 = ∅ from by ext z; simp [prefE], Cslib.Multigraph.joins_empty_iff]
    exact Fin.ext_iff.symm
  obtain ⟨hsafe2, hv2, hm2, hmod2, inv_end⟩ :=
    iterate_potential_spec dtKruskalEdgeStep dtKruskalEdgeStepSafe w kEnv (5 + 2 * r0) e
      kInv (fun _ _ _ => 0) S hk_step ⟨0, 0⟩ s1 hk_init
  have hprog : dtKruskalMaskProg ⟨r0, e, edgeU, edgeV, orderArr, compArr⟩ =
      (iterate dtInitIdStep compArr r0 0 >>= fun _ =>
        iterate dtKruskalEdgeStep kEnv e ⟨0, 0⟩ >>= fun res => pure res.acc) := rfl
  have hprefM_all : prefM e = Cslib.Multigraph.msf ends p Finset.univ := by
    ext i; simp [prefM]
  refine ⟨⟨hsafe1, hsafe2⟩, framedTriple_iff_realization.mpr ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hprog]
    exact validHistory_bind_step hv1 (validHistory_bind_step hv2 (validHistory_pure w _ _))
  · rw [hprog, memoryCost_bind', memoryCost_bind', memoryCost_pure]
    have hm2' : memoryCost (iterate dtKruskalEdgeStep kEnv e ⟨0, 0⟩) s1 ≤ e * (5 + 2 * r0) := by
      simpa [Nat.mul_comm] using hm2
    change memoryCost (iterate dtInitIdStep compArr r0 0) s +
      (memoryCost (iterate dtKruskalEdgeStep kEnv e ⟨0, 0⟩) s1 + 0) ≤ r0 + e * (5 + 2 * r0)
    omega
  · rw [hprog, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
    exact hmod1.trans hmod2
  · rw [hprog, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    exact ⟨by rw [inv_end.2.1, hprefM_all], inv_end.2.2.1, inv_end.2.2.2.1⟩

/-- Framed specification for `dtKruskalMaskProg`. -/
theorem dtKruskalMaskProg_spec {w : ℕ} {d : DTKruskalProgArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtKruskalMaskProgSafe w d s)
    (p : Equiv.Perm (Fin d.e))
    (hord : ∀ rk (hrk : rk < d.e), s.mem (d.orderArr + rk) = (p.symm ⟨rk, hrk⟩).val)
    (ends : Fin d.e → Sym2 (Fin d.r0))
    (hends : ∀ i : Fin d.e, ∃ a b : Fin d.r0, ends i = s(a, b) ∧
      s.mem (d.edgeU + i.val) = a.val ∧ s.mem (d.edgeV + i.val) = b.val) :
    Memory.FramedTriple w s (dtKruskalMaskProg d) (d.r0 + d.e * (5 + 2 * d.r0))
      (Set.Ico d.compArr (d.compArr + d.r0)) fun res s' =>
        res = maskOfFinset (Cslib.Multigraph.msf ends p Finset.univ) ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' :=
  (dtKruskalMaskProg_core hwf hsafe.1 hsafe.2.1 hsafe.2.2.1 hsafe.2.2.2.1
    hsafe.2.2.2.2.1 hsafe.2.2.2.2.2.1 hsafe.2.2.2.2.2.2.1 hsafe.2.2.2.2.2.2.2.1
    hsafe.2.2.2.2.2.2.2.2.1 hsafe.2.2.2.2.2.2.2.2.2.1 hsafe.2.2.2.2.2.2.2.2.2.2.1
    p hord ends hends).2

private theorem realizes_dtKruskalMaskProg_raw : Realizes .exact
    dtKruskalMaskProg dtKruskalProgArgsWords WordEncoding.encode
    (fun w d s =>
      let s1 := (Memory.spec 0).clientState s (iterate dtInitIdStep d.compArr d.r0 0)
      iterationSafe dtInitIdStep dtInitIdStepSafe w d.compArr d.r0 0 s ∧
      iterationSafe dtKruskalEdgeStep dtKruskalEdgeStepSafe w
        ⟨d.r0, d.edgeU, d.edgeV, d.orderArr, d.compArr⟩ d.e ⟨0, 0⟩ s1)
    (fun _ _ => 0) := by
  unfold dtKruskalMaskProg
  realize [realizes_dtInitIdStep, realizes_dtKruskalEdgeStep]
  all_goals
    obtain ⟨hi, hk⟩ := h
    first
    | exact iterationSafe_imp hi (fun _ => rfl) (fun _ _ hs => hs)
    | exact iterationSafe_imp hk (fun _ => rfl) (fun _ _ hs => hs)

private theorem dtKruskalMaskProg_safe_raw_aux {w r0 e edgeU edgeV orderArr compArr : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (h2 : Fits w 2)
    (hr0_fit : Fits w (r0 + 1)) (he_fit : Fits w (e + 1)) (h2e_fit : Fits w (2 ^ e))
    (hca : compArr + r0 ≤ s.frontier) (hoa : orderArr + e ≤ s.frontier)
    (heu : edgeU + e ≤ s.frontier) (hev : edgeV + e ≤ s.frontier)
    (hco : compArr + r0 ≤ orderArr ∨ orderArr + e ≤ compArr)
    (hcu : compArr + r0 ≤ edgeU ∨ edgeU + e ≤ compArr)
    (hcv : compArr + r0 ≤ edgeV ∨ edgeV + e ≤ compArr)
    (hord : ∀ rk < e, s.mem (orderArr + rk) < e)
    (hends : ∀ i < e, s.mem (edgeU + i) < r0 ∧ s.mem (edgeV + i) < r0) :
    let s1 := (Memory.spec 0).clientState s (iterate dtInitIdStep compArr r0 0)
    iterationSafe dtInitIdStep dtInitIdStepSafe w compArr r0 0 s ∧
    iterationSafe dtKruskalEdgeStep dtKruskalEdgeStepSafe w
      ⟨r0, edgeU, edgeV, orderArr, compArr⟩ e ⟨0, 0⟩ s1 := by
  let S : Set ℕ := Set.Ico compArr (compArr + r0)
  obtain ⟨hsafe1, htri1⟩ := dtKruskalMaskProg_init_core hwf hr0_fit hca
  obtain ⟨_, _, hmod1, hfr1, hwf1, _⟩ := framedTriple_iff_realization.mp htri1
  let s1 := (Memory.spec 0).clientState s (iterate dtInitIdStep compArr r0 0)
  let kEnv : DTKruskalEnv := ⟨r0, edgeU, edgeV, orderArr, compArr⟩
  let kInv (rk : ℕ) (st : DTIdxPair) (t : Memory.State) : Prop :=
    st.idx = rk ∧ st.acc < 2 ^ e ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ a < s.frontier, a ∉ S → t.mem a = s.mem a) ∧
    ∀ x < r0, t.mem (compArr + x) < r0
  have hk_step : ∀ rk < e, ∀ st t, kInv rk st t →
      dtKruskalEdgeStepSafe w (kEnv, st) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (dtKruskalEdgeStep (kEnv, st))) ∧
      let a' := (Memory.spec 0).clientResult t (dtKruskalEdgeStep (kEnv, st))
      let t' := (Memory.spec 0).clientState t (dtKruskalEdgeStep (kEnv, st))
      memoryCost (dtKruskalEdgeStep (kEnv, st)) t + 0 ≤ 0 + (5 + 2 * r0) ∧
      Memory.Modifies S t t' ∧
      kInv (rk + 1) a' t' := by
    intro rk hrk st t ⟨hidx, hacc_lt, htfr, hwt, htmod, hcomp_lt⟩
    rcases st with ⟨sidx, sacc⟩
    dsimp only at hidx hacc_lt
    subst sidx
    let idx := t.mem (orderArr + rk)
    have hidx_eq : idx = s.mem (orderArr + rk) := htmod _ (by omega)
      (by dsimp only [S]; simp only [Set.mem_Ico]; rcases hco with h | h <;> omega)
    have hidx_lt : idx < e := hidx_eq ▸ hord rk hrk
    let u := t.mem (edgeU + idx)
    let v := t.mem (edgeV + idx)
    have hu_eq : u = s.mem (edgeU + idx) := htmod _ (by omega)
      (by dsimp only [S]; simp only [Set.mem_Ico]; rcases hcu with h | h <;> omega)
    have hv_eq : v = s.mem (edgeV + idx) := htmod _ (by omega)
      (by dsimp only [S]; simp only [Set.mem_Ico]; rcases hcv with h | h <;> omega)
    have hu_lt : u < r0 := hu_eq ▸ (hends idx hidx_lt).1
    have hv_lt : v < r0 := hv_eq ▸ (hends idx hidx_lt).2
    let cu := t.mem (compArr + u)
    let cv := t.mem (compArr + v)
    have hmsf_lt : sacc ||| (1 <<< idx) < 2 ^ e := by
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.or_lt_two_pow hacc_lt (Nat.pow_lt_pow_right (by decide) hidx_lt)
    obtain ⟨hm_safe, hm_tri⟩ := dtKruskalMerge_core (w := w) (r0 := r0) (compArr := compArr)
      (cu := cu) (cv := cv) (rk := rk) (idx := idx) (msfMask := sacc)
      hwt h2 hr0_fit (he_fit.of_le (by omega)) (h2e_fit.of_le hmsf_lt.le)
      (by omega) (hr0_fit.of_le (by have := hcomp_lt v hv_lt; omega))
    have hstep_tri : Memory.FramedTriple w t (dtKruskalEdgeStep (kEnv, ⟨rk, sacc⟩))
        (5 + 2 * r0) S (kInv (rk + 1)) := by
      refine dtKruskalEdgeStep_triple (by omega)
        (by change edgeU + idx < t.frontier; omega)
        (by change edgeV + idx < t.frontier; omega)
        (by change compArr + u < t.frontier; omega)
        (by change compArr + v < t.frontier; omega) ?_
      refine hm_tri.mono le_rfl fun res t' h => ?_
      rcases h with ⟨rfl, hfr, hwf', hmod_step, harr⟩
      refine ⟨rfl, ?_, hfr.trans htfr, hwf',
        fun a ha haS => (hmod_step a (by omega) haS).trans (htmod a ha haS),
        fun x hx => ?_⟩
      · dsimp only
        split_ifs
        · exact hacc_lt
        · exact hmsf_lt
      · rw [harr x hx]; split_ifs
        · exact hcomp_lt v hv_lt
        · exact hcomp_lt x hx
    obtain ⟨hvh, hcost, hmod, hinv_next⟩ := framedTriple_iff_realization.mp hstep_tri
    have hsafe_step : dtKruskalEdgeStepSafe w (kEnv, ⟨rk, sacc⟩) t := by
      dsimp only [dtKruskalEdgeStepSafe, kEnv]
      refine ⟨by omega, by change edgeU + idx < t.frontier; omega,
        by change edgeV + idx < t.frontier; omega,
        by change compArr + u < t.frontier; omega,
        by change compArr + v < t.frontier; omega, ?_⟩
      change dtKruskalMergeSafe w ⟨r0, compArr, cu, cv, rk, idx, sacc⟩ t
      exact hm_safe
    exact ⟨hsafe_step, hvh, by omega, hmod, hinv_next⟩
  have hsafe2 := (iterate_potential_spec dtKruskalEdgeStep dtKruskalEdgeStepSafe w kEnv
    (5 + 2 * r0) e kInv (fun _ _ _ => 0) S hk_step ⟨0, 0⟩ s1
    ⟨rfl, Nat.two_pow_pos e, hfr1, hwf1, fun a ha haS => hmod1.mem_eq_of_not_mem ha haS,
      fun x hx => by
        rw [(framedTriple_iff_realization.mp htri1).2.2.2.2.2 x hx]; exact hx⟩).1
  exact ⟨hsafe1, hsafe2⟩

/-- `dtKruskalMaskProg` is uniformly realized with `work = 0`. -/
theorem realizes_dtKruskalMaskProg : Realizes .exact
    dtKruskalMaskProg dtKruskalProgArgsWords WordEncoding.encode
    dtKruskalMaskProgSafe (fun _ _ => 0) :=
  realizes_dtKruskalMaskProg_raw.consequence
    (fun _ _ _ _ hwf hs => dtKruskalMaskProg_safe_raw_aux hwf hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1
      hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1
      hs.2.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.2.1
      hs.2.2.2.2.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.2.2.2)
    (fun _ _ => le_rfl)

end Cslib.Algorithms.WordRAM.MinimumSpanningForest

end
