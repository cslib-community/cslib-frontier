/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Params
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Program
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Model
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Insert
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.ExtractMin
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Collect
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.Loop
import CslibFrontier.Computability.WordRAM.Realization.LoopCongr
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.DataStructure.Memory.Frame
import CslibFrontier.Tactic.Realize
import CslibFrontier.Foundations.Data.List.Counting
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Flat `Program .standard` Batch Driver for the Parametric Word-RAM Soft Heap

Single-heap Word-RAM batch driver step toward #8624, after [Chazelle2000], Theorem 1.1 and
Section 5.1, Lemmas 5.1–5.2 (NECI TR 99-097 preprint, pp. 2, 12–13), and [PettieRamachandran2002],
Section 2.4, p. 19, Lemma 2.2 and Section 3.2, pp. 21–22, Figure 1 and Lemma 3.3. Packages
`shInsert`, `shExtractMin`, and batch `shCollectCorrupted` (without
`meld` or arbitrary-handle `delete`) into a single flat deterministic width-blind standard-basis
program (`Program .standard r`, `¬prog.ReadsWidth`, `prog.IsRandFree`) operating directly on
`State.init I.encode` under `Fits w I.wordBound`, hiding `shFuelBound` internally and certifying
`O(N * (r + 1) + M + 1)` (and `O(N * (rankThresholdForEps ε + 1) + M + 1)` for arbitrary
`0 < ε : ℚ`, where `rankThresholdForEps ε = Nat.log 2 (Nat.ceil (12 / ε)) + 1`) native Word-RAM
step counts alongside per-step corruption bounds and multiset-coupled `ckey` monotonicity.

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHOp`, `SHBatchInput`: batch operation type
  and flat input encoding (`[rankThreshold, ops.length] ++ ops.flatMap SHOp.encode`) with fit
  envelope `SHBatchInput.wordBound`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHBatchResult`, `SHBatchExtract`,
  `SHBatchEntry`, `SHBatchStepRel`, `SHBatchTrace`: named output/trace structures
  (`SHBatchResult.equiv`), single-step transition relation, and trace witness.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.shBatchProg`, `SHBatchProgSafe`:
  self-contained `Memory.Prog` batch driver hiding `shFuelBound` internally.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.realizes_shBatchProg`: uniform
  `Realizes .exact` (`work := 0`) certificate for `shBatchProg`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.shBatchProg_spec`: end-to-end correctness,
  exact extract/corrupted output array layout, trace minimality/permutation/`ckey` monotonicity,
  per-step corruption bound, and amortized `memoryCost` bound for `shBatchProg`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.exists_singleSoftHeap_batch_standard_program`
  and `exists_singleSoftHeap_batch_standard_program_eps`: single-heap batch step
  `Program .standard r` for arbitrary `rankThreshold : ℕ` or `0 < ε : ℚ` (extending PR02
  Lemma 2.2's `0 < ε < 1 / 2`) with `O(N * (r + 1) + M + 1)` native steps and per-step bounds.

## References

* [B. Chazelle, *The Soft Heap: An Approximate Priority Queue with Optimal Error Rate*,
  Journal of the ACM 47(6), 2000][Chazelle2000], Theorem 1.1 and Section 5.1, Lemmas 5.1–5.2
  (NECI TR 99-097 preprint, pp. 2, 12–13).
* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), 2002][PettieRamachandran2002], Section 2.4, p. 19, Lemma 2.2 and
  Section 3.2, pp. 21–22, Figure 1 and Lemma 3.3.
-/

namespace Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory

public section

/-! ### Batch Input and Output Types -/

/-- Batch operation for a Word-RAM soft heap: insert `(val, origKey)` or extract minimum. -/
inductive SHOp where
  /-- Insert payload `val` with original key `origKey`. -/
  | insert (val origKey : ℕ)
  /-- Extract an item with minimum corrupted key. -/
  | extractMin
  deriving DecidableEq

/-- 3-word flat encoding of a batch operation (`[0, val, origKey]` or `[1, 0, 0]`). -/
@[expose] def SHOp.encode : SHOp → List ℕ
  | .insert v k => [0, v, k]
  | .extractMin => [1, 0, 0]

/-- `true` iff the operation is an insertion. -/
@[expose] def SHOp.isInsert : SHOp → Bool
  | .insert _ _ => true
  | .extractMin => false

/-- `true` iff the operation is a minimum extraction. -/
@[expose] def SHOp.isExtract : SHOp → Bool
  | .insert _ _ => false
  | .extractMin => true

/-- Batch Soft-Heap problem instance with corruption rank threshold `rankThreshold` and operation
list `ops`. -/
structure SHBatchInput where
  /-- Corruption rank threshold `r` (corrupted items bounded by `12 / 2 ^ r` times inserts). -/
  rankThreshold : ℕ
  /-- Sequence of `insert` and `extractMin` operations. -/
  ops : List SHOp

namespace SHBatchInput

/-- Number of insert operations in `I.ops`. -/
@[expose] def numInserts (I : SHBatchInput) : ℕ :=
  I.ops.countP SHOp.isInsert

/-- Number of extract-min operations in `I.ops`. -/
@[expose] def numExtracts (I : SHBatchInput) : ℕ :=
  I.ops.countP SHOp.isExtract

/-- Sequence of `(val, origKey)` pairs inserted by `I.ops`. -/
@[expose] def insertedItems (I : SHBatchInput) : List (ℕ × ℕ) :=
  I.ops.filterMap fun
    | .insert v k => some (v, k)
    | .extractMin => none

/-- Flat Word-RAM input word list `[rankThreshold, ops.length] ++ ops.flatMap SHOp.encode`. -/
@[expose] def encode (I : SHBatchInput) : List ℕ :=
  [I.rankThreshold, I.ops.length] ++ I.ops.flatMap SHOp.encode

/-- Maximum payload value or original key occurring in `I.ops`. -/
@[expose] def maxWord (I : SHBatchInput) : ℕ :=
  I.ops.foldl
    (fun acc op => match op with
      | .insert v k => max acc (max v k)
      | .extractMin => acc)
    0

/-- Word-value envelope sufficient for `I.encode`, internal pools, `shFuelBound`, and output
arrays (`w = O(log maxWord + log (r + 1) + log (ops.length + 1))`). -/
@[expose] def wordBound (I : SHBatchInput) : ℕ :=
  I.maxWord + shFuelBound I.rankThreshold I.ops.length + 34 * I.ops.length + 34

private theorem flatMap_encode_length (ops : List SHOp) :
    (ops.flatMap SHOp.encode).length = 3 * ops.length := by
  rw [Nat.mul_comm]
  exact List.length_flatMap_of_forall_length_eq fun op _ => by cases op <;> rfl

/-- Length of `I.encode` (`2 + 3 * I.ops.length`). -/
theorem encode_length (I : SHBatchInput) : I.encode.length = 2 + 3 * I.ops.length := by
  simp only [encode, List.length_append, List.length_cons, List.length_nil,
    flatMap_encode_length]

/-- Insert count plus extract count equals total operation count. -/
theorem numInserts_add_numExtracts (I : SHBatchInput) :
    I.numInserts + I.numExtracts = I.ops.length := by
  dsimp only [numInserts, numExtracts]
  induction I.ops with
  | nil => rfl
  | cons op rest ih =>
    cases op <;>
      simp only [List.countP_cons, SHOp.isInsert, SHOp.isExtract, List.length_cons,
        Bool.false_eq_true, ↓reduceIte] <;>
      omega

/-- Number of inserted items equals `I.numInserts`. -/
theorem insertedItems_length (I : SHBatchInput) : I.insertedItems.length = I.numInserts := by
  dsimp only [insertedItems, numInserts]
  induction I.ops with
  | nil => rfl
  | cons op rest ih =>
    cases op <;>
      simp only [List.filterMap_cons, List.countP_cons, SHOp.isInsert,
        List.length_cons, ih, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

private theorem foldl_max_spec (ops : List SHOp) (init : ℕ) :
    init ≤ ops.foldl (fun acc op => match op with
      | .insert v k => max acc (max v k)
      | .extractMin => acc) init ∧
    ∀ v k, SHOp.insert v k ∈ ops →
      v ≤ ops.foldl (fun acc op => match op with
        | .insert v k => max acc (max v k)
        | .extractMin => acc) init ∧
      k ≤ ops.foldl (fun acc op => match op with
        | .insert v k => max acc (max v k)
        | .extractMin => acc) init := by
  induction ops generalizing init with
  | nil =>
    refine ⟨le_rfl, fun _ _ h => nomatch h⟩
  | cons op rest ih =>
    cases op with
    | insert v₀ k₀ =>
      have hrec := ih (max init (max v₀ k₀))
      refine ⟨le_trans (le_max_left _ _) hrec.1, fun v k hmem => ?_⟩
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        exact ⟨le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hrec.1,
          le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hrec.1⟩
      · exact hrec.2 v k htail
    | extractMin =>
      have hrec := ih init
      refine ⟨hrec.1, fun v k hmem => ?_⟩
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
      · exact hrec.2 v k htail

/-- Every inserted `(val, origKey)` in `I.ops` is bounded by `I.maxWord`. -/
theorem le_maxWord_of_mem {I : SHBatchInput} {v k : ℕ} (hmem : SHOp.insert v k ∈ I.ops) :
    v ≤ I.maxWord ∧ k ≤ I.maxWord :=
  (foldl_max_spec I.ops 0).2 v k hmem

/-- Every word and length of `I.encode` fits in `w` bits when `Fits w I.wordBound`. -/
theorem inputFits_encode {w : ℕ} (I : SHBatchInput) (hw : Fits w I.wordBound) :
    InputFits w I.encode := by
  refine ⟨hw.of_le ?_, fun x hx => hw.of_le ?_⟩
  · rw [encode_length]
    unfold wordBound shFuelBound
    nlinarith
  · simp only [encode, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
      List.mem_flatMap] at hx
    rcases hx with (rfl | rfl) | ⟨op, hop, hxin⟩
    · unfold wordBound shFuelBound
      nlinarith
    · unfold wordBound shFuelBound
      nlinarith
    · cases op with
      | insert v k =>
        have hvk := le_maxWord_of_mem hop
        simp only [SHOp.encode, List.mem_cons, List.mem_nil_iff, or_false] at hxin
        rcases hxin with rfl | rfl | rfl
        · exact Nat.zero_le _
        · exact le_trans hvk.1 (by unfold wordBound; omega)
        · exact le_trans hvk.2 (by unfold wordBound; omega)
      | extractMin =>
        simp only [SHOp.encode, List.mem_cons, List.mem_nil_iff, or_false] at hxin
        rcases hxin with rfl | rfl | rfl <;> (unfold wordBound; omega)

private theorem flatMap_encode_getD (ops : List SHOp) (j c : ℕ) (hj : j < ops.length)
    (hc : c < 3) :
    (ops.flatMap SHOp.encode).getD (3 * j + c) 0 = (ops[j].encode).getD c 0 := by
  induction ops generalizing j with
  | nil => simp only [List.length_nil] at hj; omega
  | cons op rest ih =>
    have hlen : op.encode.length = 3 := by cases op <;> rfl
    cases j with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact List.getD_append _ _ _ _ (by omega)
    | succ j' =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      have hge : op.encode.length ≤ 3 * (j' + 1) + c := by omega
      rw [List.getD_append_right _ _ _ _ hge, hlen,
        show 3 * (j' + 1) + c - 3 = 3 * j' + c by omega]
      exact ih j' (by simp only [List.length_cons] at hj; omega)

/-- Initial memory readout for operation `j < I.ops.length` at offset `c < 3`. -/
private theorem mem_init_op (I : SHBatchInput) (j c : ℕ) (hj : j < I.ops.length) (hc : c < 3) :
    (Memory.State.init I.encode).mem (3 + 3 * j + c) = (I.ops[j].encode).getD c 0 := by
  rw [show 3 + 3 * j + c = (2 + 3 * j + c) + 1 by omega]
  change (Data.init (r := 0) I.encode).mem ((2 + 3 * j + c) + 1) = _
  rw [Data.init_mem_succ]
  dsimp only [encode]
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, show 2 + 3 * j + c - 2 = 3 * j + c by omega]
  exact flatMap_encode_getD I.ops j c hj hc

end SHBatchInput

/-- Output summary returned by `shBatchProg`: base address `extBase` of the `numExtracts`
3-word extract records `(found, val, key)`, base address `corBase` of the harvested corrupted
payload array, and its length `corCount`. -/
structure SHBatchResult where
  /-- Base address of the extract records array (`(found, val, key)` of stride `3`). -/
  extBase : ℕ
  /-- Base address of the harvested corrupted item payloads array. -/
  corBase : ℕ
  /-- Number of corrupted items written to `corBase[0..corCount)`. -/
  corCount : ℕ
  deriving DecidableEq

/-- Canonical 3-word tuple equivalence for `SHBatchResult`. -/
@[expose] def SHBatchResult.equiv : SHBatchResult ≃ ℕ × ℕ × ℕ where
  toFun r := (r.extBase, r.corBase, r.corCount)
  invFun := fun (extBase, corBase, corCount) => ⟨extBase, corBase, corCount⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding SHBatchResult := .ofEquiv SHBatchResult.equiv

/-- Single extraction outcome `(found, val, key)` stored at `extBase + 3 * j`. -/
structure SHBatchExtract where
  /-- `1` if an item was extracted, `0` if the heap was empty at that operation. -/
  found : ℕ
  /-- Extracted payload value (`0` if empty). -/
  val : ℕ
  /-- Extracted corrupted key (`0` if empty). -/
  key : ℕ
  deriving DecidableEq

/-- Read the `j`-th 3-word extraction record from `mem` at base address `base`. -/
@[expose] def SHBatchExtract.readFrom (mem : ℕ → ℕ) (base j : ℕ) : SHBatchExtract :=
  ⟨mem (base + 3 * j), mem (base + 3 * j + 1), mem (base + 3 * j + 2)⟩

/-- Surviving or extracted soft-heap entry `(val, origKey, ckey)`. -/
structure SHBatchEntry where
  /-- Item payload value. -/
  val : ℕ
  /-- Original key at insertion time. -/
  origKey : ℕ
  /-- Current (possibly corrupted) upper-bound key. -/
  ckey : ℕ
  deriving DecidableEq

/-- Single-step algebraic transition relation for `I.ops[j]?` from heap state `st` to `st'`,
with extraction sequence `extracts`. Enforces multiset-coupled `ckey` non-decrease
(`List.Forall₂` on a permutation) across both `.insert` and `.extractMin`, non-degradation
(`origKey ≤ ckey`), and minimum-`ckey` extraction. -/
@[expose] def SHBatchStepRel (I : SHBatchInput) (extracts : List SHBatchExtract) (j : ℕ)
    (st st' : List SHBatchEntry) : Prop :=
  match I.ops[j]? with
  | some (.insert v k) =>
      ∃ (e_new : SHBatchEntry) (st'_rest : List SHBatchEntry),
        e_new.val = v ∧ e_new.origKey = k ∧
        st'.Perm (e_new :: st'_rest) ∧
        List.Forall₂ (fun a b => a.val = b.val ∧ a.origKey = b.origKey ∧ a.ckey ≤ b.ckey)
          st st'_rest ∧
        ∀ e ∈ st', e.origKey ≤ e.ckey
  | some .extractMin =>
      ∃ ex : SHBatchExtract,
        extracts[(I.ops.take j).countP SHOp.isExtract]? = some ex ∧
        (st = [] → ex = ⟨0, 0, 0⟩ ∧ st' = []) ∧
        (st ≠ [] →
          ∃ (e : SHBatchEntry) (st_rest st'_perm : List SHBatchEntry),
            st.Perm (e :: st_rest) ∧
            ex = ⟨1, e.val, e.ckey⟩ ∧ e.origKey ≤ e.ckey ∧
            (∀ p ∈ st, e.ckey ≤ p.ckey) ∧
            st'.Perm st'_perm ∧
            List.Forall₂ (fun a b => a.val = b.val ∧ a.origKey = b.origKey ∧ a.ckey ≤ b.ckey)
              st_rest st'_perm)
  | none => False

/-- Full algebraic execution trace for `I : SHBatchInput`, certifying extract-min minimality,
key non-degradation (`origKey ≤ ckey`), multiset-coupled `ckey` monotonicity (`SHBatchStepRel`),
item conservation (`Perm I.insertedItems`), and the per-step corruption bound
`2 ^ I.rankThreshold * #corrupted ≤ 12 * #inserts`. -/
structure SHBatchTrace (I : SHBatchInput) where
  /-- Sequence of extraction outcomes in operation order. -/
  extracts : List SHBatchExtract
  /-- Items returned by non-empty extractions (`found = 1`). -/
  extractedEntries : List SHBatchEntry
  /-- Surviving items remaining in the soft heap after all operations. -/
  remaining : List SHBatchEntry
  /-- Payload values of surviving corrupted items (`origKey < ckey`). -/
  corrupted : List ℕ
  /-- Step-by-step heap entry states of length `I.ops.length + 1`. -/
  states : List (List SHBatchEntry)
  /-- Extract list length equals `I.numExtracts`. -/
  extracts_length : extracts.length = I.numExtracts
  /-- Non-empty extract records match `extractedEntries` in order. -/
  extracts_found :
    (extracts.filter (fun ex => decide (ex.found = 1))).map (fun ex => (ex.val, ex.key)) =
      extractedEntries.map (fun e => (e.val, e.ckey))
  /-- Extracted items satisfy `origKey ≤ ckey`. -/
  extracted_origKey_le : ∀ e ∈ extractedEntries, e.origKey ≤ e.ckey
  /-- Surviving items satisfy `origKey ≤ ckey`. -/
  remaining_origKey_le : ∀ e ∈ remaining, e.origKey ≤ e.ckey
  /-- Harvested corrupted list consists of `val` for surviving items with `origKey < ckey`. -/
  corrupted_eq :
    corrupted = (remaining.filter (fun e => decide (e.origKey < e.ckey))).map SHBatchEntry.val
  /-- All extracted and surviving `(val, origKey)` pairs form a permutation of `I.insertedItems`. -/
  items_perm :
    ((extractedEntries ++ remaining).map (fun e => (e.val, e.origKey))).Perm I.insertedItems
  /-- Final corruption bound after all operations. -/
  corrupted_bound : 2 ^ I.rankThreshold * corrupted.length ≤ 12 * I.numInserts
  /-- State trace length equals `I.ops.length + 1`. -/
  states_length : states.length = I.ops.length + 1
  /-- Initial heap state is empty. -/
  states_head : states.head? = some []
  /-- Final heap state equals `remaining`. -/
  states_last : states.getLast? = some remaining
  /-- Every intermediate heap state satisfies `origKey ≤ ckey` on all surviving items. -/
  states_origKey_le : ∀ j ≤ I.ops.length, ∀ st : List SHBatchEntry,
    states[j]? = some st → ∀ e ∈ st, e.origKey ≤ e.ckey
  /-- Per-step corruption bound at every step `j ≤ I.ops.length`. -/
  states_corrupted_bound : ∀ j ≤ I.ops.length, ∀ st : List SHBatchEntry,
    states[j]? = some st →
    2 ^ I.rankThreshold * (st.filter (fun e => decide (e.origKey < e.ckey))).length ≤
      12 * (I.ops.take j).countP SHOp.isInsert
  /-- Every operation step preserves heap membership with non-decreasing `ckey` and extracts a
  minimum `ckey`. -/
  step_spec : ∀ j : ℕ, j < I.ops.length →
    ∃ st st' : List SHBatchEntry,
      states[j]? = some st ∧ states[j + 1]? = some st' ∧
      SHBatchStepRel I extracts j st st'

/-- Rational per-step corruption bound when `I.rankThreshold = rankThresholdForEps ε`
with `0 < ε`. -/
theorem SHBatchTrace.states_corrupted_le_eps {I : SHBatchInput} (trace : SHBatchTrace I)
    {ε : ℚ} (hε : 0 < ε) (hrt : I.rankThreshold = rankThresholdForEps ε)
    {j : ℕ} (hj : j ≤ I.ops.length) {st : List SHBatchEntry}
    (hst : trace.states[j]? = some st) :
    ((st.filter (fun e => decide (e.origKey < e.ckey))).length : ℚ) ≤
      ε * (((I.ops.take j).countP SHOp.isInsert : ℕ) : ℚ) :=
  rat_le_eps_mul_of_pow_mul_le hε (hrt ▸ trace.states_corrupted_bound j hj st hst)

end

/-! ### Private Batch Driver and `realize` Certificates -/

private structure SHBatchEnv where
  fuel : ℕ
  extBase : ℕ
  deriving DecidableEq

private def SHBatchEnv.equiv : SHBatchEnv ≃ ℕ × ℕ where
  toFun e := (e.fuel, e.extBase)
  invFun := fun (fuel, extBase) => ⟨fuel, extBase⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SHBatchEnv := .ofEquiv SHBatchEnv.equiv

private structure SHBatchState where
  opIdx : ℕ
  extCount : ℕ
  handle : SHHandle
  deriving DecidableEq

private def SHBatchState.equiv : SHBatchState ≃ ℕ × ℕ × SHHandle where
  toFun s := (s.opIdx, s.extCount, s.handle)
  invFun := fun (opIdx, extCount, handle) => ⟨opIdx, extCount, handle⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SHBatchState := .ofEquiv SHBatchState.equiv

private theorem realizes_allocPool_pair : Realizes .exact
    (fun p : ℕ × ℕ => allocPool p.1 p.2)
    (WordEncoding.encode (α := ℕ × ℕ))
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w p s => Fits w (s.frontier + 3 * (p.1 + 1) + 12 * (p.2 + 1) + 16))
    (fun _ _ => 0) :=
  realizes_allocPool.reindex
    (fun p : ℕ × ℕ => fun i : Fin 2 => if i.val = 0 then p.1 else p.2)
    (WordEncoding.encode (α := ℕ × ℕ)) id
    (fun p i => by fin_cases i <;> rfl)

private def shBatchStep (x : SHBatchEnv × SHBatchState) : Memory.Prog SHBatchState := do
  let env := x.1
  let st := x.2
  let tag ← Memory.read (3 + 3 * st.opIdx)
  if tag = 0 then
    let val ← Memory.read (3 + 3 * st.opIdx + 1)
    let origKey ← Memory.read (3 + 3 * st.opIdx + 2)
    let h' ← shInsert (st.handle, val, origKey, env.fuel)
    pure ⟨st.opIdx + 1, st.extCount, h'⟩
  else
    let res ← shExtractMin (st.handle, env.fuel)
    Memory.write (env.extBase + 3 * st.extCount) res.found
    Memory.write (env.extBase + 3 * st.extCount + 1) res.val
    Memory.write (env.extBase + 3 * st.extCount + 2) res.key
    pure ⟨st.opIdx + 1, st.extCount + 1, res.handle⟩

private def SHBatchStepSafe (w : ℕ) (x : SHBatchEnv × SHBatchState) (s : Memory.State) : Prop :=
  let env := x.1
  let st := x.2
  Fits w (3 + 3 * st.opIdx + 2) ∧
  Fits w (st.opIdx + 1) ∧
  (s.mem (3 + 3 * st.opIdx) = 0 →
    shInsertSafe w (st.handle, s.mem (3 + 3 * st.opIdx + 1),
      s.mem (3 + 3 * st.opIdx + 2), env.fuel) s) ∧
  (s.mem (3 + 3 * st.opIdx) ≠ 0 →
    shExtractMinSafe w (st.handle, env.fuel) s ∧
    Fits w (env.extBase + 3 * st.extCount + 2) ∧
    Fits w (st.extCount + 1))

private theorem realizes_shBatchStep : Realizes .exact
    shBatchStep
    (appendWords (WordEncoding.encode (α := SHBatchEnv))
      (WordEncoding.encode (α := SHBatchState)))
    (WordEncoding.encode (α := SHBatchState))
    SHBatchStepSafe (fun _ _ => 0) := by
  unfold shBatchStep
  realize [realizes_shInsert, realizes_shExtractMin]
  all_goals
    obtain ⟨hop, hidx, hins, hext⟩ := h
    first
    | exact hop.of_le (by omega)
    | exact hins (by assumption)
    | exact (hext (by assumption)).1
    | exact (hext (by assumption)).2.1.of_le (by omega)

private theorem one_le_memoryCost_shBatchStep (x : SHBatchEnv × SHBatchState)
    (s : Memory.State) : 1 ≤ memoryCost (shBatchStep x) s := by
  dsimp only [shBatchStep]
  rw [memoryCost_bind', memoryCost_read]
  omega

/-! ### Public Batch Program and Certificates -/

public section

/-- Self-contained `Memory.Prog` batch Soft-Heap driver (`d = (rankThreshold, ops.length)`),
hiding `shFuelBound` internally and returning `(extBase, corBase, corCount)`. -/
def shBatchProg (d : ℕ × ℕ) : Memory.Prog SHBatchResult := do
  let pool ← allocPool d.2 (2 * d.2)
  let extBase ← Memory.allocDirty (3 * d.2)
  let corBase ← Memory.allocDirty d.2
  let fuel := shFuelBound d.1 d.2
  let initHandle : SHHandle := ⟨pool.1, pool.2, 0, 0, 0, d.1⟩
  let st ← iterate shBatchStep ⟨fuel, extBase⟩ d.2 ⟨0, 0, initHandle⟩
  let corCount ← shCollectCorrupted (st.handle, 0, corBase, 0, fuel)
  pure ⟨extBase, corBase, corCount⟩

/-- Native safety domain for `shBatchProg`. -/
def SHBatchProgSafe (w : ℕ) (d : ℕ × ℕ) (s : Memory.State) : Prop :=
  let pool := (Memory.spec 0).clientResult s (allocPool d.2 (2 * d.2))
  let s₁ := (Memory.spec 0).clientState s (allocPool d.2 (2 * d.2))
  let extBase := s₁.frontier
  let s₂ : Memory.State := ⟨s₁.mem, s₁.frontier + 3 * d.2⟩
  let corBase := s₂.frontier
  let s₃ : Memory.State := ⟨s₂.mem, s₂.frontier + d.2⟩
  let fuel := shFuelBound d.1 d.2
  let env : SHBatchEnv := ⟨fuel, extBase⟩
  let initSt : SHBatchState := ⟨0, 0, ⟨pool.1, pool.2, 0, 0, 0, d.1⟩⟩
  let st := (Memory.spec 0).clientResult s₃ (iterate shBatchStep env d.2 initSt)
  let s₄ := (Memory.spec 0).clientState s₃ (iterate shBatchStep env d.2 initSt)
  Fits w 16 ∧
  Fits w (s.frontier + 3 * (d.2 + 1) + 12 * (2 * d.2 + 1) + 16) ∧
  Fits w fuel ∧
  iterationSafe shBatchStep SHBatchStepSafe w env d.2 initSt s₃ ∧
  shCollectCorruptedSafe w (st.handle, 0, corBase, 0, fuel) s₄

/-- `shBatchProg` admits a uniform `Realizes .exact` compilation certificate (`work := 0`). -/
theorem realizes_shBatchProg : Realizes .exact
    shBatchProg
    (WordEncoding.encode (α := ℕ × ℕ))
    (WordEncoding.encode (α := SHBatchResult))
    SHBatchProgSafe (fun _ _ => 0) := by
  unfold shBatchProg shFuelBound
  realize [realizes_allocPool_pair, realizes_shBatchStep, realizes_shCollectCorrupted]
  all_goals
    obtain ⟨h16, hpool, hfuel, hiter, hcol⟩ := h
    first
    | exact hpool.of_le (by omega)
    | exact hfuel.of_le (by unfold shFuelBound; nlinarith)
    | refine iterationSafe_imp hiter (fun _ => rfl) (fun _ _ hs => ⟨⟨?_, ?_, ?_, ?_⟩, hs⟩)
      · exact hfuel
      · exact hfuel.of_le (by unfold shFuelBound; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      · exact hfuel.of_le (by unfold shFuelBound; nlinarith)
      · exact hfuel.of_le (by unfold shFuelBound; exact Nat.le_mul_of_pos_left _ (by omega))
    | exact hcol

end

/-! ### Framing and Proof Helpers for `shBatchProg_spec` -/

private theorem itemListRep_fits {w itemBase : ℕ} {mem : ℕ → ℕ} {head tail : ℕ}
    {items : List SHItem} (hmem_fits : ∀ a, Fits w (mem a))
    (hrep : ItemListRep itemBase mem head tail items) :
    ∀ it ∈ items, Fits w it.val := by
  induction items generalizing head with
  | nil => intro _ h; exact nomatch h
  | cons it rest ih =>
    cases rest with
    | nil =>
      rcases hrep with ⟨_, _, _, h0, _, _⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [← h0]; exact hmem_fits _
      · exact nomatch hx'
    | cons it2 rest2 =>
      rcases hrep with ⟨_, _, h0, _, _, htail⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [← h0]; exact hmem_fits _
      · exact ih htail x hx'

private theorem treeMemRep_fits {w rt itemBase nodeBase : ℕ} {s : Memory.State} {t : SHTree}
    (hwf : Memory.WellFormed w s) (hrep : TreeMemRep rt itemBase nodeBase s.mem t) :
    ∀ p ∈ t.allEntries, Fits w p.1.val ∧ Fits w p.2 := by
  induction hrep with
  | @node id r ck items l r' _ h0 _ _ _ h45 _ _ _ _ ihL ihR =>
    intro p hp
    simp only [SHTree.allEntries_node, List.mem_append, List.mem_map] at hp
    rcases hp with (⟨it, hit, rfl⟩ | hL) | hR
    · refine ⟨?_, ?_⟩
      · exact itemListRep_fits hwf.mem_fits h45 it hit
      · rw [← h0]; exact hwf.mem_fits _
    · cases l with
      | none => simp only [Option.elim_none, List.not_mem_nil] at hL
      | some c => exact ihL c rfl p hL
    · cases r' with
      | none => simp only [Option.elim_none, List.not_mem_nil] at hR
      | some c => exact ihR c rfl p hR

private theorem shInv_fits_entry {w ic₀ nc₀ maxItems maxNodes : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s) :
    ∀ p ∈ forestEntries roots, Fits w p.1.val ∧ Fits w p.2 := by
  intro p hp
  rcases List.mem_flatMap.mp hp with ⟨t, ht, hpt⟩
  exact treeMemRep_fits hinv.wf (hinv.trees_mem t ht) p hpt

private def rootsToEntries (roots : List SHTree) : List SHBatchEntry :=
  (forestEntries roots).map (fun p => ⟨p.1.val, p.1.origKey, p.2⟩)

private theorem rootsToEntries_map_pair (roots : List SHTree) :
    (rootsToEntries roots).map (fun e => (e.val, e.origKey)) =
      (forestItems roots).map (fun it => (it.val, it.origKey)) := by
  simp only [rootsToEntries, forestItems, List.map_map]
  rfl

private theorem forestItems_map_id (roots : List SHTree) :
    (forestItems roots).map SHItem.id = forestItemIds roots := by
  simp only [forestItems, forestEntries, forestItemIds, List.map_flatMap]
  rfl

private theorem forestItems_nodup {w ic₀ nc₀ maxItems maxNodes : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s) :
    (forestItems roots).Nodup := by
  refine List.Nodup.of_map SHItem.id ?_
  rw [forestItems_map_id]
  exact hinv.itemIds_nodup

private theorem rootsToEntries_corrupted_length (roots : List SHTree) :
    ((rootsToEntries roots).filter (fun e => decide (e.origKey < e.ckey))).length =
      ((forestEntries roots).filter (fun p => decide (p.1.origKey < p.2))).length := by
  dsimp only [rootsToEntries]
  induction forestEntries roots with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases hlt : p.1.origKey < p.2
    · simp only [hlt, decide_true, ↓reduceIte, List.length_cons, ih]
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, ih]

private theorem forall₂_perm_of_nodup_le {α : Type} :
    ∀ {L₀ L₁ : List (α × ℕ)},
      (L₁.map Prod.fst).Perm (L₀.map Prod.fst) →
      (L₀.map Prod.fst).Nodup →
      (∀ p ∈ L₁, ∃ c₀, (p.1, c₀) ∈ L₀ ∧ c₀ ≤ p.2) →
      ∃ L₁' : List (α × ℕ), L₁.Perm L₁' ∧
        List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) L₀ L₁'
  | [], L₁, hperm, _, _ => by
    have hlen := hperm.length_eq
    simp only [List.length_map, List.length_nil] at hlen
    have hnil : L₁ = [] := List.length_eq_zero_iff.mp hlen
    subst hnil
    exact ⟨[], List.Perm.refl _, List.Forall₂.nil⟩
  | a :: rest, L₁, hperm, hnd, hle => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have ha_mem : a.1 ∈ L₁.map Prod.fst :=
      hperm.mem_iff.mpr (by rw [List.map_cons]; exact List.mem_cons_self)
    rcases List.mem_map.mp ha_mem with ⟨b, hb_in, hba⟩
    obtain ⟨pre, suf, hL₁⟩ := List.append_of_mem hb_in
    let L₁r := pre ++ suf
    have hperm_b : L₁.Perm (b :: L₁r) := by
      rw [hL₁]
      exact List.perm_middle
    have hperm_rest : (L₁r.map Prod.fst).Perm (rest.map Prod.fst) := by
      have h1 : (b.1 :: L₁r.map Prod.fst).Perm (a.1 :: rest.map Prod.fst) := by
        simpa only [List.map_cons] using (hperm_b.symm.map Prod.fst).trans hperm
      rw [hba] at h1
      exact h1.cons_inv
    have ha_le_b : a.2 ≤ b.2 := by
      rcases hle b hb_in with ⟨c₀, hc₀_in, hc₀_le⟩
      rcases List.mem_cons.mp hc₀_in with heq | hrest_in
      · have hc_eq : c₀ = a.2 := (Prod.ext_iff.mp heq).2
        omega
      · exfalso
        have hmem_fst : a.1 ∈ rest.map Prod.fst := by
          rw [← hba]
          exact List.mem_map.mpr ⟨(b.1, c₀), hrest_in, rfl⟩
        exact hnd.1 hmem_fst
    have hle_rest : ∀ p ∈ L₁r, ∃ c₀, (p.1, c₀) ∈ rest ∧ c₀ ≤ p.2 := by
      intro p hp
      have hp_L₁ : p ∈ L₁ := hperm_b.symm.mem_iff.mp (List.mem_cons_of_mem _ hp)
      rcases hle p hp_L₁ with ⟨c₀, hc₀_in, hc₀_le⟩
      rcases List.mem_cons.mp hc₀_in with heq | hrest_in
      · exfalso
        have hp_fst : p.1 ∈ rest.map Prod.fst :=
          hperm_rest.mem_iff.mp (List.mem_map_of_mem hp)
        have heq1 : p.1 = a.1 := (Prod.ext_iff.mp heq).1
        rw [heq1] at hp_fst
        exact hnd.1 hp_fst
      · exact ⟨c₀, hrest_in, hc₀_le⟩
    obtain ⟨L_rest', hperm_r', hf2⟩ :=
      forall₂_perm_of_nodup_le hperm_rest hnd.2 hle_rest
    exact ⟨b :: L_rest', hperm_b.trans (List.Perm.cons b hperm_r'),
      List.Forall₂.cons ⟨hba.symm, ha_le_b⟩ hf2⟩

private theorem forall₂_rootsToEntries_map :
    ∀ {L₀ L₁ : List (SHItem × ℕ)},
      List.Forall₂ (fun a b : SHItem × ℕ => a.1 = b.1 ∧ a.2 ≤ b.2) L₀ L₁ →
      List.Forall₂
        (fun a b : SHBatchEntry => a.val = b.val ∧ a.origKey = b.origKey ∧ a.ckey ≤ b.ckey)
        (L₀.map (fun p : SHItem × ℕ => (⟨p.1.val, p.1.origKey, p.2⟩ : SHBatchEntry)))
        (L₁.map (fun p : SHItem × ℕ => (⟨p.1.val, p.1.origKey, p.2⟩ : SHBatchEntry)))
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hl =>
      .cons ⟨congrArg SHItem.val h.1, congrArg SHItem.origKey h.1, h.2⟩
        (forall₂_rootsToEntries_map hl)

private theorem shBatchStepRel_mono_extracts {I : SHBatchInput}
    {extracts₀ extracts₁ : List SHBatchExtract} {m' j extCount : ℕ}
    {st st' : List SHBatchEntry}
    (hj_lt : j < I.ops.length) (hm_lt : m' < j)
    (hext_cnt : (I.ops.take j).countP SHOp.isExtract = extCount)
    (hext_sub : ∀ k < extCount, extracts₁[k]? = extracts₀[k]?)
    (hrel : SHBatchStepRel I extracts₀ m' st st') :
    SHBatchStepRel I extracts₁ m' st st' := by
  dsimp only [SHBatchStepRel] at hrel ⊢
  cases hop : I.ops[m']? with
  | none => rw [hop] at hrel; exact hrel
  | some op =>
    rw [hop] at hrel
    cases op with
    | insert v k => exact hrel
    | extractMin =>
      rcases hrel with ⟨ex, hex_m, h1, h2⟩
      have hcnt_lt : (I.ops.take m').countP SHOp.isExtract < extCount := by
        rw [← hext_cnt]
        have hm_lt_len : m' < I.ops.length := by omega
        have htk := (List.take_append_getElem hm_lt_len).symm
        have hpre : I.ops.take (m' + 1) <+: I.ops.take j := by
          rw [show m' + 1 = min (m' + 1) j by omega, ← List.take_take]
          exact List.take_prefix _ _
        rw [htk] at hpre
        rcases hpre with ⟨tail, htail⟩
        have hget : I.ops[m'] = SHOp.extractMin := by
          have hsome : I.ops[m']? = some I.ops[m'] := List.getElem?_eq_getElem hm_lt_len
          rw [hsome] at hop
          exact Option.some.inj hop
        rw [← htail, hget]
        repeat rw [List.countP_append]
        simp only [List.countP_cons, SHOp.isExtract, List.countP_nil, ↓reduceIte]
        omega
      refine ⟨ex, ?_, h1, h2⟩
      rw [hext_sub _ hcnt_lt]
      exact hex_m

private theorem shBatch_states_append
    {I : SHBatchInput} {j : ℕ} (hj_lt : j < I.ops.length)
    {extracts₀ nextExtracts : List SHBatchExtract} {extCount : ℕ}
    {states₀ : List (List SHBatchEntry)} {prevState nextState : List SHBatchEntry}
    (hstates_len : states₀.length = j + 1)
    (hstates_head : states₀.head? = some [])
    (hstates_last : states₀[j]? = some prevState)
    (hstates_orig₀ : ∀ m' ≤ j, ∀ st : List SHBatchEntry,
      states₀[m']? = some st → ∀ e ∈ st, e.origKey ≤ e.ckey)
    (hstates_cor₀ : ∀ m' ≤ j, ∀ st : List SHBatchEntry,
      states₀[m']? = some st →
      2 ^ I.rankThreshold * (st.filter (fun e => decide (e.origKey < e.ckey))).length ≤
        12 * (I.ops.take m').countP SHOp.isInsert)
    (hext_cnt : (I.ops.take j).countP SHOp.isExtract = extCount)
    (hext_sub : ∀ k < extCount, nextExtracts[k]? = extracts₀[k]?)
    (hstep₀ : ∀ m' < j,
      ∃ st st' : List SHBatchEntry,
        states₀[m']? = some st ∧ states₀[m' + 1]? = some st' ∧
        SHBatchStepRel I extracts₀ m' st st')
    (horig_next : ∀ e ∈ nextState, e.origKey ≤ e.ckey)
    (hcor_next : 2 ^ I.rankThreshold *
        (nextState.filter (fun e => decide (e.origKey < e.ckey))).length ≤
      12 * (I.ops.take (j + 1)).countP SHOp.isInsert)
    (hrel_cur : SHBatchStepRel I nextExtracts j prevState nextState) :
    (states₀ ++ [nextState]).length = (j + 1) + 1 ∧
    (states₀ ++ [nextState]).head? = some [] ∧
    (states₀ ++ [nextState])[j + 1]? = some nextState ∧
    (∀ m' ≤ j + 1, ∀ st : List SHBatchEntry,
      (states₀ ++ [nextState])[m']? = some st → ∀ e ∈ st, e.origKey ≤ e.ckey) ∧
    (∀ m' ≤ j + 1, ∀ st : List SHBatchEntry,
      (states₀ ++ [nextState])[m']? = some st →
      2 ^ I.rankThreshold * (st.filter (fun e => decide (e.origKey < e.ckey))).length ≤
        12 * (I.ops.take m').countP SHOp.isInsert) ∧
    (∀ m' < j + 1,
      ∃ st st' : List SHBatchEntry,
        (states₀ ++ [nextState])[m']? = some st ∧
        (states₀ ++ [nextState])[m' + 1]? = some st' ∧
        SHBatchStepRel I nextExtracts m' st st') := by
  refine ⟨by simp only [List.length_append, List.length_singleton, hstates_len], ?_, ?_, ?_, ?_, ?_⟩
  · cases states₀ with
    | nil => simp only [List.length_nil] at hstates_len; omega
    | cons hd tl => simpa only [List.cons_append, List.head?_cons] using hstates_head
  · rw [List.getElem?_append_right (by omega), hstates_len, Nat.sub_self]
    rfl
  · intro m' hm' st hst
    rcases Nat.le_iff_lt_or_eq.mp hm' with hm_lt | rfl
    · have hm_le : m' ≤ j := by omega
      rw [List.getElem?_append_left (by omega)] at hst
      exact hstates_orig₀ m' hm_le st hst
    · rw [List.getElem?_append_right (by omega), hstates_len, Nat.sub_self] at hst
      simp only [List.getElem?_cons_zero] at hst
      rw [← Option.some.inj hst]
      exact horig_next
  · intro m' hm' st hst
    rcases Nat.le_iff_lt_or_eq.mp hm' with hm_lt | rfl
    · have hm_le : m' ≤ j := by omega
      rw [List.getElem?_append_left (by omega)] at hst
      exact hstates_cor₀ m' hm_le st hst
    · rw [List.getElem?_append_right (by omega), hstates_len, Nat.sub_self] at hst
      simp only [List.getElem?_cons_zero] at hst
      rw [← Option.some.inj hst]
      exact hcor_next
  · intro m' hm'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with hm_lt | rfl
    · obtain ⟨st, st', hst, hst', hrel⟩ := hstep₀ m' hm_lt
      refine ⟨st, st', ?_, ?_, shBatchStepRel_mono_extracts hj_lt hm_lt hext_cnt hext_sub hrel⟩
      · rw [List.getElem?_append_left (by omega)]; exact hst
      · rw [List.getElem?_append_left (by omega)]; exact hst'
    · refine ⟨prevState, nextState, ?_, ?_, hrel_cur⟩
      · rw [List.getElem?_append_left (by omega)]; exact hstates_last
      · rw [List.getElem?_append_right (by omega), hstates_len, Nat.sub_self]; rfl

private theorem shBatch_iterate_spec {w : ℕ} (I : SHBatchInput) (hw : Fits w I.wordBound)
    (s₀ : Memory.State) (extBase : ℕ)
    (hs₀_eq : ∀ a < s₀.frontier, s₀.mem a = (Memory.State.init I.encode).mem a)
    (hs₀_fr : s₀.frontier = I.encode.length + 1)
    (hext_ge : s₀.frontier ≤ extBase)
    (m : ℕ) (st₀ : SHBatchState) (s_cur : Memory.State)
    (hm_eq : st₀.opIdx + m = I.ops.length)
    (hfr_cur : extBase + 3 * I.ops.length ≤ s_cur.frontier)
    (hs_mem : ∀ a < s₀.frontier, s_cur.mem a = s₀.mem a)
    (hext_cnt : st₀.extCount = (I.ops.take st₀.opIdx).countP SHOp.isExtract)
    (hic_cnt : st₀.handle.itemCount = (I.ops.take st₀.opIdx).countP SHOp.isInsert)
    (hrt_eq : st₀.handle.rankThreshold = I.rankThreshold)
    (hitem_ge : s₀.frontier ≤ st₀.handle.itemBase)
    (hnode_ge : s₀.frontier ≤ st₀.handle.nodeBase)
    (hitem_ext : st₀.handle.itemBase + 3 * (I.ops.length + 1) ≤ extBase)
    (hnode_ext : st₀.handle.nodeBase + 12 * (2 * I.ops.length + 1) ≤ extBase)
    (hpool_disj : ∀ a, extBase ≤ a → a < extBase + 3 * I.ops.length →
      ¬ InSHPool 0 0 I.ops.length (2 * I.ops.length) st₀.handle a)
    (h16 : Fits w 16)
    (hfuel_fit : Fits w (shFuelBound I.rankThreshold I.ops.length))
    (roots₀ : List SHTree) (created₀ : ℕ → ℕ)
    (hinv₀ : SHInv w 0 0 I.ops.length (2 * I.ops.length) st₀.handle roots₀ created₀ s_cur)
    (extracts₀ : List SHBatchExtract)
    (extractedEntries₀ : List SHBatchEntry)
    (states₀ : List (List SHBatchEntry))
    (hexts_len : extracts₀.length = st₀.extCount)
    (hexts_mem : ∀ k < st₀.extCount,
      extracts₀[k]? = some (SHBatchExtract.readFrom s_cur.mem extBase k))
    (hexts_found :
      (extracts₀.filter (fun ex => decide (ex.found = 1))).map (fun ex => (ex.val, ex.key)) =
        extractedEntries₀.map (fun e => (e.val, e.ckey)))
    (hexts_orig : ∀ e ∈ extractedEntries₀, e.origKey ≤ e.ckey)
    (hperm₀ :
      ((extractedEntries₀ ++ rootsToEntries roots₀).map (fun e => (e.val, e.origKey))).Perm
        (SHBatchInput.insertedItems ⟨I.rankThreshold, I.ops.take st₀.opIdx⟩))
    (hstates_len : states₀.length = st₀.opIdx + 1)
    (hstates_head : states₀.head? = some [])
    (hstates_last : states₀[st₀.opIdx]? = some (rootsToEntries roots₀))
    (hstates_orig₀ : ∀ m' ≤ st₀.opIdx, ∀ st : List SHBatchEntry,
      states₀[m']? = some st → ∀ e ∈ st, e.origKey ≤ e.ckey)
    (hstates_cor₀ : ∀ m' ≤ st₀.opIdx, ∀ st : List SHBatchEntry,
      states₀[m']? = some st →
      2 ^ I.rankThreshold * (st.filter (fun e => decide (e.origKey < e.ckey))).length ≤
        12 * (I.ops.take m').countP SHOp.isInsert)
    (hstep₀ : ∀ m' < st₀.opIdx,
      ∃ st st' : List SHBatchEntry,
        states₀[m']? = some st ∧ states₀[m' + 1]? = some st' ∧
        SHBatchStepRel I extracts₀ m' st st') :
    let env : SHBatchEnv := ⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩
    let prog := iterate shBatchStep env m st₀
    let st' := (Memory.spec 0).clientResult s_cur prog
    let s' := (Memory.spec 0).clientState s_cur prog
    iterationSafe shBatchStep SHBatchStepSafe w env m st₀ s_cur ∧
    (Memory.spec w).ValidHistory s_cur ((Memory.spec w).clientHistory s_cur prog) ∧
    st'.opIdx = I.ops.length ∧
    st'.extCount = I.numExtracts ∧
    st'.handle.itemBase = st₀.handle.itemBase ∧
    st'.handle.nodeBase = st₀.handle.nodeBase ∧
    st'.handle.itemCount = I.numInserts ∧
    st'.handle.rankThreshold = I.rankThreshold ∧
    s'.frontier = s_cur.frontier ∧
    ∃ (roots' : List SHTree) (created' : ℕ → ℕ) (extracts' : List SHBatchExtract)
      (extractedEntries' : List SHBatchEntry) (states' : List (List SHBatchEntry)),
      SHInv w 0 0 I.ops.length (2 * I.ops.length) st'.handle roots' created' s' ∧
      extracts'.length = I.numExtracts ∧
      (List.range I.numExtracts).map (SHBatchExtract.readFrom s'.mem extBase) = extracts' ∧
      (extracts'.filter (fun ex => decide (ex.found = 1))).map (fun ex => (ex.val, ex.key)) =
        extractedEntries'.map (fun e => (e.val, e.ckey)) ∧
      (∀ e ∈ extractedEntries', e.origKey ≤ e.ckey) ∧
      ((extractedEntries' ++ rootsToEntries roots').map (fun e => (e.val, e.origKey))).Perm
        I.insertedItems ∧
      states'.length = I.ops.length + 1 ∧
      states'.head? = some [] ∧
      states'.getLast? = some (rootsToEntries roots') ∧
      (∀ m' ≤ I.ops.length, ∀ st : List SHBatchEntry,
        states'[m']? = some st → ∀ e ∈ st, e.origKey ≤ e.ckey) ∧
      (∀ m' ≤ I.ops.length, ∀ st : List SHBatchEntry,
        states'[m']? = some st →
        2 ^ I.rankThreshold * (st.filter (fun e => decide (e.origKey < e.ckey))).length ≤
          12 * (I.ops.take m').countP SHOp.isInsert) ∧
      (∀ j < I.ops.length,
        ∃ st st' : List SHBatchEntry,
          states'[j]? = some st ∧ states'[j + 1]? = some st' ∧
          SHBatchStepRel I extracts' j st st') ∧
      (memoryCost prog s_cur : ℚ) + totalPhi I.rankThreshold roots' ≤
        totalPhi I.rankThreshold roots₀ +
          (240 * (I.rankThreshold : ℚ) + 523) *
            (((I.ops.drop st₀.opIdx).countP SHOp.isInsert : ℕ) : ℚ) +
          254 * (((I.ops.drop st₀.opIdx).countP SHOp.isExtract : ℕ) : ℚ) := by
  induction m generalizing st₀ s_cur roots₀ created₀ extracts₀ extractedEntries₀ states₀ with
  | zero =>
    dsimp only
    have hop_eq : st₀.opIdx = I.ops.length := by omega
    have htake : I.ops.take st₀.opIdx = I.ops := by rw [hop_eq, List.take_length]
    have hdrop : I.ops.drop st₀.opIdx = [] := by
      rw [hop_eq, List.drop_eq_nil_iff]
    have hext_eq : st₀.extCount = I.numExtracts := by
      rw [hext_cnt, htake]; rfl
    have hic_eq : st₀.handle.itemCount = I.numInserts := by
      rw [hic_cnt, htake]; rfl
    have hlast : states₀.getLast? = some (rootsToEntries roots₀) := by
      rw [List.getLast?_eq_getElem?, hstates_len, Nat.add_sub_cancel]
      exact hstates_last
    have hrange :
        (List.range I.numExtracts).map (SHBatchExtract.readFrom s_cur.mem extBase) = extracts₀ := by
      refine List.ext_getElem ?_ (fun k hk1 hk2 => ?_)
      · rw [List.length_map, List.length_range, hexts_len, hext_eq]
      · rw [List.getElem_map, List.getElem_range]
        have hk1' : k < I.numExtracts := by
          simpa only [List.length_map, List.length_range] using hk1
        have hm := hexts_mem k (hext_eq ▸ hk1')
        have heq : extracts₀[k]? = some extracts₀[k] := List.getElem?_eq_getElem hk2
        rw [hm] at heq
        exact Option.some.inj heq
    refine ⟨trivial, validHistory_pure w s_cur st₀, hop_eq, hext_eq, rfl, rfl, hic_eq, hrt_eq, rfl,
      roots₀, created₀, extracts₀, extractedEntries₀, states₀, hinv₀, hext_eq ▸ hexts_len,
      hrange, hexts_found, hexts_orig, by simpa only [htake] using hperm₀,
      hop_eq ▸ hstates_len, hstates_head, hlast,
      by simpa only [hop_eq] using hstates_orig₀,
      by simpa only [hop_eq] using hstates_cor₀,
      by simpa only [hop_eq] using hstep₀, ?_⟩
    rw [hdrop]
    simp only [iterate, memoryCost_pure, Nat.cast_zero, zero_add, List.countP_nil, mul_zero,
      add_zero, le_rfl]
  | succ m ih =>
    dsimp only
    let j := st₀.opIdx
    have hj_lt : j < I.ops.length := by omega
    have htake_j : I.ops.take (j + 1) = I.ops.take j ++ [I.ops[j]] :=
      (List.take_append_getElem hj_lt).symm
    have hdrop_j : I.ops.drop j = I.ops[j] :: I.ops.drop (j + 1) := by
      exact List.drop_eq_getElem_cons hj_lt
    have haddr_lt : 3 + 3 * j + 2 < s₀.frontier := by
      rw [hs₀_fr, I.encode_length]; omega
    have haddr_fit : Fits w (3 + 3 * j + 2) :=
      hw.of_le (by unfold SHBatchInput.wordBound; omega)
    have hidx_fit : Fits w (j + 1) :=
      hw.of_le (by unfold SHBatchInput.wordBound; omega)
    have hmem_op : ∀ c < 3, s_cur.mem (3 + 3 * j + c) = (I.ops[j].encode).getD c 0 := by
      intro c hc
      rw [hs_mem _ (by omega), hs₀_eq _ (by omega)]
      exact I.mem_init_op j c hj_lt hc
    have htake_insert_le : (I.ops.take j).countP SHOp.isInsert +
        (if I.ops[j].isInsert then 1 else 0) ≤ I.numInserts := by
      have h1 : I.ops.take (j + 1) <+: I.ops := List.take_prefix (j + 1) I.ops
      rcases h1 with ⟨tail, htail⟩
      have hcnt : (I.ops.take (j + 1)).countP SHOp.isInsert ≤ I.numInserts := by
        dsimp only [SHBatchInput.numInserts]
        calc (I.ops.take (j + 1)).countP SHOp.isInsert
            ≤ (I.ops.take (j + 1) ++ tail).countP SHOp.isInsert := by
              rw [List.countP_append]; omega
          _ = I.ops.countP SHOp.isInsert := by rw [htail]
      rw [htake_j, List.countP_append] at hcnt
      simp only [List.countP_cons, List.countP_nil, Nat.zero_add] at hcnt
      by_cases his : I.ops[j].isInsert <;>
        simp only [his, ↓reduceIte, Bool.false_eq_true] at hcnt ⊢ <;> omega
    have htake_extract_le : (I.ops.take j).countP SHOp.isExtract +
        (if I.ops[j].isExtract then 1 else 0) ≤ I.numExtracts := by
      have h1 : I.ops.take (j + 1) <+: I.ops := List.take_prefix (j + 1) I.ops
      rcases h1 with ⟨tail, htail⟩
      have hcnt : (I.ops.take (j + 1)).countP SHOp.isExtract ≤ I.numExtracts := by
        dsimp only [SHBatchInput.numExtracts]
        calc (I.ops.take (j + 1)).countP SHOp.isExtract
            ≤ (I.ops.take (j + 1) ++ tail).countP SHOp.isExtract := by
              rw [List.countP_append]; omega
          _ = I.ops.countP SHOp.isExtract := by rw [htail]
      rw [htake_j, List.countP_append] at hcnt
      simp only [List.countP_cons, List.countP_nil, Nat.zero_add] at hcnt
      by_cases hext : I.ops[j].isExtract <;>
        simp only [hext, ↓reduceIte, Bool.false_eq_true] at hcnt ⊢ <;> omega
    cases hop_j : I.ops[j] with
    | insert v k =>
      have htag0 : s_cur.mem (3 + 3 * j) = 0 := by
        have := hmem_op 0 (by decide)
        rw [Nat.add_zero, hop_j] at this
        exact this
      have hval_eq : s_cur.mem (3 + 3 * j + 1) = v := by
        have := hmem_op 1 (by decide)
        rw [hop_j] at this
        exact this
      have hkey_eq : s_cur.mem (3 + 3 * j + 2) = k := by
        have := hmem_op 2 (by decide)
        rw [hop_j] at this
        exact this
      have hvk_mem : SHOp.insert v k ∈ I.ops := by
        rw [← hop_j]; exact List.getElem_mem hj_lt
      have hvk_max := SHBatchInput.le_maxWord_of_mem hvk_mem
      have hv_fit : Fits w v :=
        hw.of_le (le_trans hvk_max.1 (by unfold SHBatchInput.wordBound; omega))
      have hk_fit : Fits w k :=
        hw.of_le (le_trans hvk_max.2 (by unfold SHBatchInput.wordBound; omega))
      have hcap : st₀.handle.itemCount < I.ops.length := by
        have hlen_ie := I.numInserts_add_numExtracts
        have his : I.ops[j].isInsert = true := by simp [hop_j, SHOp.isInsert]
        simp only [his, ↓reduceIte] at htake_insert_le
        dsimp only [j] at htake_insert_le
        omega
      have hfuel_ge : shFuelBound st₀.handle.rankThreshold I.ops.length ≤
          shFuelBound I.rankThreshold I.ops.length := by
        rw [hrt_eq]
      obtain ⟨hv_ins, hsafe_ins, hib_ins, hnb_ins, hic_ins, _, hrt_ins, hfr_ins, hmem_ins,
          roots₁, created₁, hinv₁, hperm₁, hentries₁, hcost_ins⟩ :=
        shInsert_spec hinv₀ hcap hv_fit hk_fit hfuel_ge hfuel_fit
      let d_ins := (st₀.handle, v, k, shFuelBound I.rankThreshold I.ops.length)
      let h₁ := (Memory.spec 0).clientResult s_cur (shInsert d_ins)
      let s₁ := (Memory.spec 0).clientState s_cur (shInsert d_ins)
      have hstep_safe : SHBatchStepSafe w
          (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀) s_cur := by
        refine ⟨haddr_fit, hidx_fit, fun _ => ?_, fun hne => absurd htag0 hne⟩
        rw [hval_eq, hkey_eq]
        exact hsafe_ins
      have hstep_hv : (Memory.spec w).ValidHistory s_cur
          ((Memory.spec w).clientHistory s_cur
            (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀))) := by
        dsimp only [shBatchStep]
        refine validHistory_read_bind (by omega) ?_
        rw [htag0]
        simp only [↓reduceIte]
        refine validHistory_read_bind (by omega) ?_
        refine validHistory_read_bind (by omega) ?_
        rw [hval_eq, hkey_eq]
        exact validHistory_bind_step hv_ins (validHistory_pure w _ _)
      have hstep_res : (Memory.spec 0).clientResult s_cur
          (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀)) =
          ⟨j + 1, st₀.extCount, h₁⟩ := by
        dsimp only [shBatchStep]
        rw [clientResult_bind_read, htag0]
        simp only [↓reduceIte]
        rw [clientResult_bind_read, clientResult_bind_read, hval_eq, hkey_eq,
          StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
      have hstep_st : (Memory.spec 0).clientState s_cur
          (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀)) = s₁ := by
        dsimp only [shBatchStep]
        rw [clientState_bind_read, htag0]
        simp only [↓reduceIte]
        rw [clientState_bind_read, clientState_bind_read, hval_eq, hkey_eq,
          StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
      have hstep_cost : memoryCost
          (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀)) s_cur =
          3 + memoryCost (shInsert d_ins) s_cur := by
        dsimp only [shBatchStep, d_ins]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, htag0]
        simp only [↓reduceIte]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          hval_eq, hkey_eq, memoryCost_bind', memoryCost_pure]
        omega
      have hs₁_mem_in : ∀ a < s₀.frontier, s₁.mem a = s₀.mem a := by
        intro a ha
        have hnot : ¬ InSHPool 0 0 I.ops.length (2 * I.ops.length) st₀.handle a := by
          intro hin
          rcases hin with ⟨hlo, _⟩ | ⟨hlo, _⟩ <;> omega
        have heq : s₁.mem a = s_cur.mem a := by
          by_contra hne
          exact hnot (hmem_ins a hne)
        exact heq.trans (hs_mem a ha)
      have hs₁_mem_ext : ∀ a, extBase ≤ a → a < extBase + 3 * I.ops.length →
          s₁.mem a = s_cur.mem a := by
        intro a ha1 ha2
        by_contra hne
        exact hpool_disj a ha1 ha2 (hmem_ins a hne)
      have hdisj₁ : ∀ a, extBase ≤ a → a < extBase + 3 * I.ops.length →
          ¬ InSHPool 0 0 I.ops.length (2 * I.ops.length) h₁ a := by
        intro a ha1 ha2 hin
        apply hpool_disj a ha1 ha2
        dsimp only [InSHPool] at hin ⊢
        rw [hib_ins, hnb_ins] at hin
        exact hin
      have hitem_ge₁ : s₀.frontier ≤ h₁.itemBase := by rw [hib_ins]; exact hitem_ge
      have hnode_ge₁ : s₀.frontier ≤ h₁.nodeBase := by rw [hnb_ins]; exact hnode_ge
      have hitem_ext₁ : h₁.itemBase + 3 * (I.ops.length + 1) ≤ extBase := by
        rw [hib_ins]; exact hitem_ext
      have hnode_ext₁ : h₁.nodeBase + 12 * (2 * I.ops.length + 1) ≤ extBase := by
        rw [hnb_ins]; exact hnode_ext
      have hexts_mem₁ : ∀ k < st₀.extCount,
          extracts₀[k]? = some (SHBatchExtract.readFrom s₁.mem extBase k) := by
        intro k hk
        have hlt_n : k < I.ops.length := by
          have hcl := List.countP_le_length (p := SHOp.isExtract) (l := I.ops.take st₀.opIdx)
          have htl := List.length_take_le st₀.opIdx I.ops
          omega
        have hk0 := hexts_mem k hk
        have h0 : s₁.mem (extBase + 3 * k) = s_cur.mem (extBase + 3 * k) :=
          hs₁_mem_ext _ (by omega) (by omega)
        have h1 : s₁.mem (extBase + 3 * k + 1) = s_cur.mem (extBase + 3 * k + 1) :=
          hs₁_mem_ext _ (by omega) (by omega)
        have h2 : s₁.mem (extBase + 3 * k + 2) = s_cur.mem (extBase + 3 * k + 2) :=
          hs₁_mem_ext _ (by omega) (by omega)
        simpa only [SHBatchExtract.readFrom, h0, h1, h2] using hk0
      have hperm_next :
          ((extractedEntries₀ ++ rootsToEntries roots₁).map (fun e => (e.val, e.origKey))).Perm
            (SHBatchInput.insertedItems ⟨I.rankThreshold, I.ops.take (j + 1)⟩) := by
        have htake_items :
            SHBatchInput.insertedItems ⟨I.rankThreshold, I.ops.take (j + 1)⟩ =
              SHBatchInput.insertedItems ⟨I.rankThreshold, I.ops.take j⟩ ++ [(v, k)] := by
          dsimp only [SHBatchInput.insertedItems]
          rw [htake_j, List.filterMap_append]
          simp only [List.filterMap_cons, hop_j, List.filterMap_nil]
        rw [htake_items, List.map_append, rootsToEntries_map_pair]
        have hfi :
            ((forestItems roots₁).map (fun it => (it.val, it.origKey))).Perm
              ((v, k) :: (forestItems roots₀).map (fun it => (it.val, it.origKey))) := by
          simpa only [List.map_cons] using hperm₁.map (fun it => (it.val, it.origKey))
        have h1 : (extractedEntries₀.map (fun e => (e.val, e.origKey)) ++
            (forestItems roots₁).map (fun it => (it.val, it.origKey))).Perm
            (extractedEntries₀.map (fun e => (e.val, e.origKey)) ++
              ((v, k) :: (forestItems roots₀).map (fun it => (it.val, it.origKey)))) :=
          List.Perm.append_left _ hfi
        have h2 : (extractedEntries₀.map (fun e => (e.val, e.origKey)) ++
            ((v, k) :: (forestItems roots₀).map (fun it => (it.val, it.origKey)))).Perm
            ((extractedEntries₀ ++ rootsToEntries roots₀).map (fun e => (e.val, e.origKey)) ++
              [(v, k)]) := by
          rw [List.map_append, rootsToEntries_map_pair]
          have hmid : (extractedEntries₀.map (fun e => (e.val, e.origKey)) ++
              ((v, k) :: (forestItems roots₀).map (fun it => (it.val, it.origKey)))).Perm
              ((v, k) :: (extractedEntries₀.map (fun e => (e.val, e.origKey)) ++
                (forestItems roots₀).map (fun it => (it.val, it.origKey)))) :=
            List.perm_middle
          exact hmid.trans (List.perm_append_comm (l₁ := [(v, k)]))
        dsimp only [j]
        exact h1.trans (h2.trans (hperm₀.append_right [(v, k)]))
      have hic_next : st₀.handle.itemCount + 1 = (I.ops.take (j + 1)).countP SHOp.isInsert := by
        rw [htake_j, List.countP_append, hop_j]
        dsimp only [j]
        simp [SHOp.isInsert, hic_cnt]
      have horig_next : ∀ e ∈ rootsToEntries roots₁, e.origKey ≤ e.ckey := by
        intro e he
        simp only [rootsToEntries, List.mem_map] at he
        rcases he with ⟨p, hp, rfl⟩
        exact hinv₁.origKey_le_ckey p hp
      have hcor_next :
          2 ^ I.rankThreshold *
            ((rootsToEntries roots₁).filter (fun e => decide (e.origKey < e.ckey))).length ≤
            12 * (I.ops.take (j + 1)).countP SHOp.isInsert := by
        have hcb := shInv_corrupted_le hinv₁
        rw [hrt_ins, hrt_eq, hic_ins, Nat.sub_zero, hic_next] at hcb
        rw [rootsToEntries_corrupted_length]
        exact hcb
      have hrel_cur :
          SHBatchStepRel I extracts₀ j (rootsToEntries roots₀) (rootsToEntries roots₁) := by
        have hj_some : I.ops[j]? = some (.insert v k) := by
          rw [List.getElem?_eq_getElem hj_lt, hop_j]
        dsimp only [SHBatchStepRel]
        rw [hj_some]
        let it_new : SHItem := ⟨st₀.handle.itemCount + 1, v, k⟩
        have hit_mem : it_new ∈ forestItems roots₁ := by
          rw [hperm₁.mem_iff]
          exact List.mem_cons_self
        rcases List.mem_map.mp hit_mem with ⟨p_new, hp_new_in, hp_new_fst⟩
        obtain ⟨pre₁, suf₁, hfe₁⟩ := List.append_of_mem hp_new_in
        let restEntries₁ := pre₁ ++ suf₁
        have hfe₁_perm : (forestEntries roots₁).Perm (p_new :: restEntries₁) := by
          rw [hfe₁]
          exact List.perm_middle
        have hrest_fst_perm : (restEntries₁.map Prod.fst).Perm (forestItems roots₀) := by
          have h1 : (p_new.1 :: restEntries₁.map Prod.fst).Perm
              (it_new :: forestItems roots₀) := by
            simpa only [List.map_cons, forestItems] using
              (hfe₁_perm.symm.map Prod.fst).trans hperm₁
          rw [hp_new_fst] at h1
          exact h1.cons_inv
        have hrest_le : ∀ p ∈ restEntries₁, ∃ c₀, (p.1, c₀) ∈ forestEntries roots₀ ∧ c₀ ≤ p.2 := by
          intro p hp
          have hp_in : p ∈ forestEntries roots₁ :=
            hfe₁_perm.symm.mem_iff.mp (List.mem_cons_of_mem _ hp)
          rcases hentries₁ p hp_in with ⟨hp1, _⟩ | hold
          · exfalso
            have hp_fi : p.1 ∈ forestItems roots₀ :=
              hrest_fst_perm.mem_iff.mp (List.mem_map_of_mem hp)
            have hp_id : p.1.id ∈ forestItemIds roots₀ := by
              rw [← forestItems_map_id]
              exact List.mem_map_of_mem hp_fi
            have hlt := (hinv₀.itemIds_range p.1.id hp_id).2
            rw [hp1] at hlt
            dsimp only [it_new] at hlt
            omega
          · exact hold
        have hnd₀ : ((forestEntries roots₀).map Prod.fst).Nodup := forestItems_nodup hinv₀
        obtain ⟨L₁', hperm_L₁', hf2_L₁'⟩ :=
          forall₂_perm_of_nodup_le hrest_fst_perm hnd₀ hrest_le
        let toBatch : SHItem × ℕ → SHBatchEntry := fun p => ⟨p.1.val, p.1.origKey, p.2⟩
        refine ⟨toBatch p_new, L₁'.map toBatch, ?_, ?_, ?_,
          forall₂_rootsToEntries_map hf2_L₁', horig_next⟩
        · dsimp only [toBatch]; rw [hp_new_fst]
        · dsimp only [toBatch]; rw [hp_new_fst]
        · have hp1 : (rootsToEntries roots₁).Perm (toBatch p_new :: restEntries₁.map toBatch) := by
            simpa only [rootsToEntries, List.map_cons] using hfe₁_perm.map toBatch
          exact hp1.trans (List.Perm.cons _ (hperm_L₁'.map toBatch))
      let states₁ := states₀ ++ [rootsToEntries roots₁]
      obtain ⟨hstates₁_len, hstates₁_head, hstates₁_last, hstates_orig₁, hstates_cor₁, hstep₁⟩ :=
        shBatch_states_append hj_lt hstates_len hstates_head hstates_last
          hstates_orig₀ hstates_cor₀ hext_cnt.symm (fun _ _ => rfl) hstep₀
          horig_next hcor_next hrel_cur
      have hih := ih ⟨j + 1, st₀.extCount, h₁⟩ s₁ (by dsimp only [j]; omega)
        (by rw [hfr_ins]; exact hfr_cur) hs₁_mem_in
        (by
          rw [htake_j, List.countP_append, hop_j]
          dsimp only [j]
          simp [SHOp.isExtract, hext_cnt])
        (by rw [hic_ins]; exact hic_next)
        (by rw [hrt_ins, hrt_eq]) hitem_ge₁ hnode_ge₁ hitem_ext₁ hnode_ext₁ hdisj₁
        roots₁ created₁ hinv₁
        extracts₀ extractedEntries₀ states₁ hexts_len hexts_mem₁ hexts_found hexts_orig
        hperm_next hstates₁_len hstates₁_head hstates₁_last hstates_orig₁ hstates_cor₁ hstep₁
      rw [show iterate shBatchStep ⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩ (m + 1) st₀ =
          (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀) >>=
            iterate shBatchStep ⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩ m) from rfl]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hstep_res, hstep_st]
      obtain ⟨hih_safe, hih_hv, hih_op, hih_ext, hih_ib, hih_nb, hih_ic, hih_rt, hih_fr,
          roots', created', extracts', extractedEntries', states', hinv', hlen', hrange',
          hfound', horig', hperm', hslen', hshead', hslast', horig_s', hcor_s', hstep', hcost'⟩ :=
        hih
      refine ⟨⟨hstep_safe, by rw [hstep_res, hstep_st]; exact hih_safe⟩,
        validHistory_bind_step hstep_hv (by rw [hstep_res, hstep_st]; exact hih_hv),
        hih_op, hih_ext, hih_ib.trans hib_ins, hih_nb.trans hnb_ins, hih_ic, hih_rt,
        hih_fr.trans hfr_ins,
        roots', created', extracts', extractedEntries', states', hinv', hlen', hrange',
        hfound', horig', hperm', hslen', hshead', hslast', horig_s', hcor_s', hstep', ?_⟩
      rw [memoryCost_bind', hstep_res, hstep_st, hstep_cost]
      rw [hdrop_j]
      simp only [List.countP_cons, hop_j, SHOp.isInsert, SHOp.isExtract, ↓reduceIte,
        Bool.false_eq_true, Nat.add_zero]
      rw [hrt_eq] at hcost_ins
      push_cast
      linarith
    | extractMin =>
      have htag1 : s_cur.mem (3 + 3 * j) = 1 := by
        have := hmem_op 0 (by decide)
        rw [Nat.add_zero, hop_j] at this
        exact this
      have htag_ne0 : s_cur.mem (3 + 3 * j) ≠ 0 := by rw [htag1]; omega
      have hext_lt_num : st₀.extCount < I.numExtracts := by
        have his : I.ops[j].isExtract = true := by simp [hop_j, SHOp.isExtract]
        simp only [his, ↓reduceIte] at htake_extract_le
        dsimp only [j] at htake_extract_le
        omega
      have hext_lt_n : st₀.extCount < I.ops.length := by
        have := I.numInserts_add_numExtracts; omega
      have hext_addr_lt : extBase + 3 * st₀.extCount + 2 < s_cur.frontier := by omega
      have hext_addr_fit : Fits w (extBase + 3 * st₀.extCount + 2) :=
        hinv₀.wf.fits_of_lt_frontier hext_addr_lt
      have hext_cnt_fit : Fits w (st₀.extCount + 1) :=
        hw.of_le (by unfold SHBatchInput.wordBound; omega)
      have hfuel_ge : shFuelBound st₀.handle.rankThreshold I.ops.length ≤
          shFuelBound I.rankThreshold I.ops.length := by
        rw [hrt_eq]
      obtain ⟨hv_ext, hsafe_ext, hib_ext, hnb_ext, hic_ext, hnc_ext, hrt_ext, hfr_ext,
          hmem_ext, hemp_ext, hne_ext⟩ :=
        shExtractMin_spec hinv₀ hfuel_ge hfuel_fit
      let d_ext := (st₀.handle, shFuelBound I.rankThreshold I.ops.length)
      let res := (Memory.spec 0).clientResult s_cur (shExtractMin d_ext)
      let s_mid := (Memory.spec 0).clientState s_cur (shExtractMin d_ext)
      have hres_fits : Fits w res.found ∧ Fits w res.val ∧ Fits w res.key := by
        by_cases hemp : roots₀ = []
        · obtain ⟨hf0, hv0, hk0, _⟩ := hemp_ext hemp
          rw [hf0, hv0, hk0]
          exact ⟨fits_zero w, fits_zero w, fits_zero w⟩
        · obtain ⟨hf1, it₀, roots₁, hit_in, hval_it, _, _, _, _, _, _⟩ := hne_ext hemp
          have hfits := shInv_fits_entry hinv₀ (it₀, res.key) hit_in
          rw [hf1, ← hval_it]
          exact ⟨h16.of_le (by omega), hfits.1, hfits.2⟩
      have hstep_safe : SHBatchStepSafe w
          (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀) s_cur :=
        ⟨haddr_fit, hidx_fit, fun hz => absurd hz htag_ne0,
          fun _ => ⟨hsafe_ext, hext_addr_fit, hext_cnt_fit⟩⟩
      have hstep_hv : (Memory.spec w).ValidHistory s_cur
          ((Memory.spec w).clientHistory s_cur
            (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀))) := by
        dsimp only [shBatchStep]
        refine validHistory_read_bind (by omega) ?_
        rw [ite_eq_right (fun hz => absurd hz htag_ne0)]
        refine validHistory_bind_step hv_ext ?_
        refine validHistory_write_bind (by rw [hfr_ext]; omega) hres_fits.1 ?_
        refine validHistory_write_bind (by dsimp only; rw [hfr_ext]; omega) hres_fits.2.1 ?_
        refine validHistory_write_bind (by dsimp only; rw [hfr_ext]; omega) hres_fits.2.2 ?_
        exact validHistory_pure w _ _
      let s₁ : Memory.State :=
        ⟨Function.update (Function.update (Function.update s_mid.mem
          (extBase + 3 * st₀.extCount) res.found)
          (extBase + 3 * st₀.extCount + 1) res.val)
          (extBase + 3 * st₀.extCount + 2) res.key, s_mid.frontier⟩
      have hstep_res : (Memory.spec 0).clientResult s_cur
          (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀)) =
          ⟨j + 1, st₀.extCount + 1, res.handle⟩ := by
        dsimp only [shBatchStep]
        rw [clientResult_bind_read, ite_eq_right (fun hz => absurd hz htag_ne0),
          StateTransitionSpec.clientResult_bind,
          clientResult_bind_write, clientResult_bind_write, clientResult_bind_write,
          StateTransitionSpec.clientResult_pure]
      have hstep_st : (Memory.spec 0).clientState s_cur
          (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀)) = s₁ := by
        dsimp only [shBatchStep]
        rw [clientState_bind_read, ite_eq_right (fun hz => absurd hz htag_ne0),
          StateTransitionSpec.clientState_bind,
          clientState_bind_write, clientState_bind_write, clientState_bind_write,
          StateTransitionSpec.clientState_pure]
      have hstep_cost : memoryCost
          (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀)) s_cur =
          4 + memoryCost (shExtractMin d_ext) s_cur := by
        dsimp only [shBatchStep, d_ext]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          ite_eq_right (fun hz => absurd hz htag_ne0),
          memoryCost_bind', memoryCost_bind', memoryCost_write,
          memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write, memoryCost_pure]
        omega
      have hs_mid_mem_in : ∀ a < s₀.frontier, s_mid.mem a = s₀.mem a := by
        intro a ha
        have hnot : ¬ InSHPool 0 0 I.ops.length (2 * I.ops.length) st₀.handle a := by
          intro hin
          rcases hin with ⟨hlo, _⟩ | ⟨hlo, _⟩ <;> omega
        have heq : s_mid.mem a = s_cur.mem a := by
          by_contra hne
          exact hnot (hmem_ext a hne)
        exact heq.trans (hs_mem a ha)
      have hs₁_mem_in : ∀ a < s₀.frontier, s₁.mem a = s₀.mem a := by
        intro a ha
        have hne0 : a ≠ extBase + 3 * st₀.extCount := by omega
        have hne1 : a ≠ extBase + 3 * st₀.extCount + 1 := by omega
        have hne2 : a ≠ extBase + 3 * st₀.extCount + 2 := by omega
        dsimp only [s₁]
        rw [Function.update_of_ne hne2, Function.update_of_ne hne1, Function.update_of_ne hne0]
        exact hs_mid_mem_in a ha
      have hdisj₁ : ∀ a, extBase ≤ a → a < extBase + 3 * I.ops.length →
          ¬ InSHPool 0 0 I.ops.length (2 * I.ops.length) res.handle a := by
        intro a ha1 ha2 hin
        apply hpool_disj a ha1 ha2
        dsimp only [InSHPool] at hin ⊢
        rw [hib_ext, hnb_ext] at hin
        exact hin
      have hitem_ge₁ : s₀.frontier ≤ res.handle.itemBase := by rw [hib_ext]; exact hitem_ge
      have hnode_ge₁ : s₀.frontier ≤ res.handle.nodeBase := by rw [hnb_ext]; exact hnode_ge
      have hitem_ext₁ : res.handle.itemBase + 3 * (I.ops.length + 1) ≤ extBase := by
        rw [hib_ext]; exact hitem_ext
      have hnode_ext₁ : res.handle.nodeBase + 12 * (2 * I.ops.length + 1) ≤ extBase := by
        rw [hnb_ext]; exact hnode_ext
      let ex_cur : SHBatchExtract := ⟨res.found, res.val, res.key⟩
      have hex_cur_read : SHBatchExtract.readFrom s₁.mem extBase st₀.extCount = ex_cur := by
        dsimp only [SHBatchExtract.readFrom, ex_cur, s₁]
        congr 1
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [Function.update_self]
      have hexts_mem₁ : ∀ k < st₀.extCount + 1,
          (extracts₀ ++ [ex_cur])[k]? = some (SHBatchExtract.readFrom s₁.mem extBase k) := by
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | rfl
        · rw [List.getElem?_append_left (by omega)]
          have hk0 := hexts_mem k hk_lt
          have hmid : ∀ c < 3, s_mid.mem (extBase + 3 * k + c) =
              s_cur.mem (extBase + 3 * k + c) := by
            intro c hc
            by_contra hne
            exact hpool_disj _ (by omega) (by omega) (hmem_ext _ hne)
          have hwr : ∀ c < 3, s₁.mem (extBase + 3 * k + c) =
              s_mid.mem (extBase + 3 * k + c) := by
            intro c hc
            dsimp only [s₁]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
          have h0 : s₁.mem (extBase + 3 * k) = s_cur.mem (extBase + 3 * k) :=
            (hwr 0 (by decide)).trans (hmid 0 (by decide))
          have h1 : s₁.mem (extBase + 3 * k + 1) = s_cur.mem (extBase + 3 * k + 1) :=
            (hwr 1 (by decide)).trans (hmid 1 (by decide))
          have h2 : s₁.mem (extBase + 3 * k + 2) = s_cur.mem (extBase + 3 * k + 2) :=
            (hwr 2 (by decide)).trans (hmid 2 (by decide))
          simpa only [SHBatchExtract.readFrom, h0, h1, h2] using hk0
        · rw [List.getElem?_append_right (by omega), hexts_len, Nat.sub_self, hex_cur_read]
          rfl
      have hs₁_agree : ∀ a, InSHPool 0 0 I.ops.length (2 * I.ops.length) res.handle a →
          s₁.mem a = s_mid.mem a := by
        intro a ha
        have ha_lt_ext : a < extBase := by
          rcases ha with ⟨_, hlt⟩ | ⟨_, hlt⟩
          · rw [hib_ext] at hlt; omega
          · rw [hnb_ext] at hlt; omega
        dsimp only [s₁]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
      have hwf₁ : Memory.WellFormed w s₁ := by
        have hwf_mid : Memory.WellFormed w s_mid := wellFormed_clientState hinv₀.wf hv_ext
        refine ⟨hwf_mid.frontier_fits, fun a => ?_⟩
        dsimp only [s₁]
        by_cases h2 : a = extBase + 3 * st₀.extCount + 2
        · subst h2; rw [Function.update_self]; exact hres_fits.2.2
        · rw [Function.update_of_ne h2]
          by_cases h1 : a = extBase + 3 * st₀.extCount + 1
          · subst h1; rw [Function.update_self]; exact hres_fits.2.1
          · rw [Function.update_of_ne h1]
            by_cases h0 : a = extBase + 3 * st₀.extCount
            · subst h0; rw [Function.update_self]; exact hres_fits.1
            · rw [Function.update_of_ne h0]; exact hwf_mid.mem_fits a
      have htake_items :
          SHBatchInput.insertedItems ⟨I.rankThreshold, I.ops.take (j + 1)⟩ =
            SHBatchInput.insertedItems ⟨I.rankThreshold, I.ops.take j⟩ := by
        dsimp only [SHBatchInput.insertedItems]
        rw [htake_j, List.filterMap_append]
        simp only [List.filterMap_cons, hop_j, List.filterMap_nil, List.append_nil]
      have hic_next : res.handle.itemCount = (I.ops.take (j + 1)).countP SHOp.isInsert := by
        rw [htake_j, List.countP_append, hic_ext, hop_j]
        dsimp only [j]
        simp [SHOp.isInsert, hic_cnt]
      have hext_sub₁ : ∀ k < st₀.extCount, (extracts₀ ++ [ex_cur])[k]? = extracts₀[k]? :=
        fun _ hk => List.getElem?_append_left (hexts_len ▸ hk)
      have hj_some : I.ops[j]? = some .extractMin := by
        rw [List.getElem?_eq_getElem hj_lt, hop_j]
      have hex_idx :
          (extracts₀ ++ [ex_cur])[(I.ops.take j).countP SHOp.isExtract]? = some ex_cur := by
        rw [List.getElem?_append_right (by dsimp only [j]; rw [hexts_len, hext_cnt]),
          hexts_len, ← hext_cnt, Nat.sub_self]
        rfl
      by_cases hemp : roots₀ = []
      · subst hemp
        obtain ⟨hf0, hv0, hk0, hh_eq, hs_mid_eq, hm0⟩ := hemp_ext rfl
        have hinv_mid :
            SHInv w 0 0 I.ops.length (2 * I.ops.length) res.handle [] created₀ s_mid := by
          rw [show res.handle = st₀.handle from hh_eq, show s_mid = s_cur from hs_mid_eq]
          exact hinv₀
        have hinv₁ := hinv_mid.congr_outside hwf₁ rfl hs₁_agree
        have hfound₁ :
            ((extracts₀ ++ [ex_cur]).filter (fun ex => decide (ex.found = 1))).map
              (fun ex => (ex.val, ex.key)) =
              extractedEntries₀.map (fun e => (e.val, e.ckey)) := by
          rw [List.filter_append]
          simp only [List.filter_cons, List.filter_nil, ex_cur]
          rw [show res.found = 0 from hf0, decide_eq_false (by omega)]
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
          exact hexts_found
        have horig_next : ∀ e ∈ rootsToEntries [], e.origKey ≤ e.ckey :=
          fun _ h => nomatch h
        have hcor_next :
            2 ^ I.rankThreshold *
              ((rootsToEntries []).filter (fun e => decide (e.origKey < e.ckey))).length ≤
              12 * (I.ops.take (j + 1)).countP SHOp.isInsert := by
          simp only [rootsToEntries, forestEntries, List.flatMap_nil, List.map_nil,
            List.filter_nil, List.length_nil, Nat.mul_zero, Nat.zero_le]
        have hrel_cur :
            SHBatchStepRel I (extracts₀ ++ [ex_cur]) j
              (rootsToEntries []) (rootsToEntries []) := by
          dsimp only [SHBatchStepRel]
          rw [hj_some]
          refine ⟨ex_cur, hex_idx, fun _ => ⟨?_, rfl⟩, fun hne => absurd rfl hne⟩
          simp only [ex_cur]
          rw [show res.found = 0 from hf0, show res.val = 0 from hv0,
            show res.key = 0 from hk0]
        let states₁ := states₀ ++ [rootsToEntries []]
        obtain ⟨hstates₁_len, hstates₁_head, hstates₁_last, hstates_orig₁, hstates_cor₁, hstep₁⟩ :=
          shBatch_states_append hj_lt hstates_len hstates_head hstates_last
            hstates_orig₀ hstates_cor₀ hext_cnt.symm hext_sub₁ hstep₀
            horig_next hcor_next hrel_cur
        have hih := ih ⟨j + 1, st₀.extCount + 1, res.handle⟩ s₁ (by dsimp only [j]; omega)
          (by dsimp only [s₁]; rw [hfr_ext]; exact hfr_cur) hs₁_mem_in
          (by
            rw [htake_j, List.countP_append, hop_j]
            dsimp only [j]
            simp [SHOp.isExtract, hext_cnt])
          hic_next
          (by rw [hrt_ext, hrt_eq]) hitem_ge₁ hnode_ge₁ hitem_ext₁ hnode_ext₁ hdisj₁
          [] created₀ hinv₁
          (extracts₀ ++ [ex_cur]) extractedEntries₀ states₁
          (by simp only [List.length_append, List.length_singleton, hexts_len])
          hexts_mem₁ hfound₁ hexts_orig
          (by dsimp only [j]; rw [htake_items]; exact hperm₀)
          hstates₁_len hstates₁_head hstates₁_last hstates_orig₁ hstates_cor₁ hstep₁
        rw [show iterate shBatchStep ⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩
            (m + 1) st₀ =
            (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀) >>=
              iterate shBatchStep ⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩ m) from rfl]
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
          hstep_res, hstep_st]
        obtain ⟨hih_safe, hih_hv, hih_op, hih_ext, hih_ib, hih_nb, hih_ic, hih_rt, hih_fr,
            roots', created', extracts', extractedEntries', states', hinv', hlen', hrange',
            hfound', horig', hperm', hslen', hshead', hslast', horig_s', hcor_s', hstep', hcost'⟩ :=
          hih
        refine ⟨⟨hstep_safe, by rw [hstep_res, hstep_st]; exact hih_safe⟩,
          validHistory_bind_step hstep_hv (by rw [hstep_res, hstep_st]; exact hih_hv),
          hih_op, hih_ext, hih_ib.trans hib_ext, hih_nb.trans hnb_ext, hih_ic, hih_rt,
          hih_fr.trans hfr_ext,
          roots', created', extracts', extractedEntries', states', hinv', hlen', hrange',
          hfound', horig', hperm', hslen', hshead', hslast', horig_s', hcor_s', hstep', ?_⟩
        rw [memoryCost_bind', hstep_res, hstep_st, hstep_cost, hm0]
        rw [hdrop_j]
        simp only [List.countP_cons, hop_j, SHOp.isInsert, SHOp.isExtract, ↓reduceIte,
          Bool.false_eq_true, Nat.add_zero]
        push_cast
        linarith
      · obtain ⟨hf1, it₀, roots₁, hit_in, hval_it, horig_it, hmin_it, hinv_mid,
            hperm_it, hentries_ext, hcost_ext⟩ := hne_ext hemp
        have hinv₁ := hinv_mid.congr_outside hwf₁ rfl hs₁_agree
        let e_pop : SHBatchEntry := ⟨it₀.val, it₀.origKey, res.key⟩
        have hfound₁ :
            ((extracts₀ ++ [ex_cur]).filter (fun ex => decide (ex.found = 1))).map
              (fun ex => (ex.val, ex.key)) =
              (extractedEntries₀ ++ [e_pop]).map (fun e => (e.val, e.ckey)) := by
          rw [List.filter_append]
          simp only [List.filter_cons, List.filter_nil, ex_cur]
          rw [show res.found = 1 from hf1, decide_eq_true rfl]
          simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil, hexts_found]
          dsimp only [e_pop]
          rw [show it₀.val = res.val from hval_it]
        have horig₁ : ∀ e ∈ extractedEntries₀ ++ [e_pop], e.origKey ≤ e.ckey := by
          intro e he
          rcases List.mem_append.mp he with h1 | h2
          · exact hexts_orig e h1
          · simp only [List.mem_singleton] at h2
            rw [h2]; exact horig_it
        have hperm₁ :
            (((extractedEntries₀ ++ [e_pop]) ++ rootsToEntries roots₁).map
              (fun e => (e.val, e.origKey))).Perm
              (SHBatchInput.insertedItems ⟨I.rankThreshold, I.ops.take (j + 1)⟩) := by
          rw [htake_items]
          have hfi :
              ((e_pop :: rootsToEntries roots₁).map (fun e => (e.val, e.origKey))).Perm
                ((rootsToEntries roots₀).map (fun e => (e.val, e.origKey))) := by
            rw [List.map_cons, rootsToEntries_map_pair, rootsToEntries_map_pair]
            simpa only [e_pop, List.map_cons] using
              hperm_it.map (fun it => (it.val, it.origKey))
          have h1 : (((extractedEntries₀ ++ [e_pop]) ++ rootsToEntries roots₁).map
              (fun e => (e.val, e.origKey))).Perm
              (extractedEntries₀.map (fun e => (e.val, e.origKey)) ++
                (e_pop :: rootsToEntries roots₁).map (fun e => (e.val, e.origKey))) := by
            simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append]
            exact List.Perm.refl _
          have h2 : (extractedEntries₀.map (fun e => (e.val, e.origKey)) ++
              (e_pop :: rootsToEntries roots₁).map (fun e => (e.val, e.origKey))).Perm
              ((extractedEntries₀ ++ rootsToEntries roots₀).map (fun e => (e.val, e.origKey))) := by
            rw [List.map_append]
            exact List.Perm.append_left _ hfi
          exact h1.trans (h2.trans hperm₀)
        have horig_next : ∀ e ∈ rootsToEntries roots₁, e.origKey ≤ e.ckey := by
          intro e he
          simp only [rootsToEntries, List.mem_map] at he
          rcases he with ⟨p, hp, rfl⟩
          exact hinv₁.origKey_le_ckey p hp
        have hcor_next :
            2 ^ I.rankThreshold *
              ((rootsToEntries roots₁).filter (fun e => decide (e.origKey < e.ckey))).length ≤
              12 * (I.ops.take (j + 1)).countP SHOp.isInsert := by
          have hcb := shInv_corrupted_le hinv₁
          dsimp only [res] at hic_next
          rw [hrt_ext, hrt_eq, Nat.sub_zero, hic_next] at hcb
          rw [rootsToEntries_corrupted_length]
          exact hcb
        have hrel_cur :
            SHBatchStepRel I (extracts₀ ++ [ex_cur]) j
              (rootsToEntries roots₀) (rootsToEntries roots₁) := by
          dsimp only [SHBatchStepRel]
          rw [hj_some]
          refine ⟨ex_cur, hex_idx, fun hemp' => ?_, fun _ => ?_⟩
          · have hfe_empty : forestEntries roots₀ = [] := List.length_eq_zero_iff.mp (by
              simpa only [rootsToEntries, List.length_map, List.length_nil] using
                congrArg List.length hemp')
            rw [hfe_empty] at hit_in
            exact absurd hit_in List.not_mem_nil
          · obtain ⟨pre₀, suf₀, hfe₀⟩ := List.append_of_mem hit_in
            let L₀ := pre₀ ++ suf₀
            have hfe₀_perm : (forestEntries roots₀).Perm ((it₀, res.key) :: L₀) := by
              rw [hfe₀]
              exact List.perm_middle
            have hnd₀ : (it₀ :: L₀.map Prod.fst).Nodup := by
              have hpm : (it₀ :: L₀.map Prod.fst).Perm (forestItems roots₀) := by
                simpa only [List.map_cons, forestItems] using hfe₀_perm.symm.map Prod.fst
              exact hpm.nodup_iff.mpr (forestItems_nodup hinv₀)
            rw [List.nodup_cons] at hnd₀
            have hfst_perm : ((forestEntries roots₁).map Prod.fst).Perm (L₀.map Prod.fst) := by
              have h1 : (it₀ :: (forestEntries roots₁).map Prod.fst).Perm (forestItems roots₀) :=
                hperm_it
              have h2 : (forestItems roots₀).Perm (it₀ :: L₀.map Prod.fst) := by
                simpa only [List.map_cons, forestItems] using hfe₀_perm.map Prod.fst
              exact (h1.trans h2).cons_inv
            have hle_L₀ : ∀ p ∈ forestEntries roots₁, ∃ c₀, (p.1, c₀) ∈ L₀ ∧ c₀ ≤ p.2 := by
              intro p hp
              rcases hentries_ext p hp with ⟨c₀, hc₀_in, hc₀_le⟩
              have hc₀_in' : (p.1, c₀) ∈ (it₀, res.key) :: L₀ :=
                hfe₀_perm.mem_iff.mp hc₀_in
              rcases List.mem_cons.mp hc₀_in' with heq | hmem
              · exfalso
                have hp1 : p.1 ∈ L₀.map Prod.fst :=
                  hfst_perm.mem_iff.mp (List.mem_map_of_mem hp)
                have hpit : p.1 = it₀ := congrArg Prod.fst heq
                rw [hpit] at hp1
                exact hnd₀.1 hp1
              · exact ⟨c₀, hmem, hc₀_le⟩
            obtain ⟨L₁', hperm_L₁', hf2_L₁'⟩ :=
              forall₂_perm_of_nodup_le hfst_perm hnd₀.2 hle_L₀
            let toBatch : SHItem × ℕ → SHBatchEntry := fun p => ⟨p.1.val, p.1.origKey, p.2⟩
            refine ⟨e_pop, L₀.map toBatch, L₁'.map toBatch, ?_, ?_, horig_it, ?_, ?_,
              forall₂_rootsToEntries_map hf2_L₁'⟩
            · simpa only [rootsToEntries, List.map_cons, e_pop] using hfe₀_perm.map toBatch
            · simp only [ex_cur, e_pop]
              rw [show res.found = 1 from hf1, show it₀.val = res.val from hval_it]
            · intro p hp
              rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
              exact hmin_it q hq
            · simpa only [rootsToEntries] using hperm_L₁'.map toBatch
        let states₁ := states₀ ++ [rootsToEntries roots₁]
        obtain ⟨hstates₁_len, hstates₁_head, hstates₁_last, hstates_orig₁, hstates_cor₁, hstep₁⟩ :=
          shBatch_states_append hj_lt hstates_len hstates_head hstates_last
            hstates_orig₀ hstates_cor₀ hext_cnt.symm hext_sub₁ hstep₀
            horig_next hcor_next hrel_cur
        have hih := ih ⟨j + 1, st₀.extCount + 1, res.handle⟩ s₁ (by dsimp only [j]; omega)
          (by dsimp only [s₁]; rw [hfr_ext]; exact hfr_cur) hs₁_mem_in
          (by
            rw [htake_j, List.countP_append, hop_j]
            dsimp only [j]
            simp [SHOp.isExtract, hext_cnt])
          hic_next
          (by rw [hrt_ext, hrt_eq]) hitem_ge₁ hnode_ge₁ hitem_ext₁ hnode_ext₁ hdisj₁
          roots₁ created₀ hinv₁
          (extracts₀ ++ [ex_cur]) (extractedEntries₀ ++ [e_pop]) states₁
          (by simp only [List.length_append, List.length_singleton, hexts_len])
          hexts_mem₁ hfound₁ horig₁
          (by dsimp only [j] at hperm₁; exact hperm₁)
          hstates₁_len hstates₁_head hstates₁_last hstates_orig₁ hstates_cor₁ hstep₁
        rw [show iterate shBatchStep ⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩
            (m + 1) st₀ =
            (shBatchStep (⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩, st₀) >>=
              iterate shBatchStep ⟨shFuelBound I.rankThreshold I.ops.length, extBase⟩ m) from rfl]
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
          hstep_res, hstep_st]
        obtain ⟨hih_safe, hih_hv, hih_op, hih_ext, hih_ib, hih_nb, hih_ic, hih_rt, hih_fr,
            roots', created', extracts', extractedEntries', states', hinv', hlen', hrange',
            hfound', horig', hperm', hslen', hshead', hslast', horig_s', hcor_s', hstep', hcost'⟩ :=
          hih
        refine ⟨⟨hstep_safe, by rw [hstep_res, hstep_st]; exact hih_safe⟩,
          validHistory_bind_step hstep_hv (by rw [hstep_res, hstep_st]; exact hih_hv),
          hih_op, hih_ext, hih_ib.trans hib_ext, hih_nb.trans hnb_ext, hih_ic, hih_rt,
          hih_fr.trans hfr_ext,
          roots', created', extracts', extractedEntries', states', hinv', hlen', hrange',
          hfound', horig', hperm', hslen', hshead', hslast', horig_s', hcor_s', hstep', ?_⟩
        rw [memoryCost_bind', hstep_res, hstep_st, hstep_cost]
        rw [hdrop_j]
        simp only [List.countP_cons, hop_j, SHOp.isInsert, SHOp.isExtract, ↓reduceIte,
          Bool.false_eq_true, Nat.add_zero]
        rw [hrt_eq] at hcost_ext
        push_cast
        linarith
public section

/-- Full end-to-end specification of `shBatchProg` on `Memory.State.init I.encode` whenever
`Fits w I.wordBound`: proves `SHBatchProgSafe`, `ValidHistory`, output array bounds, exact trace
existence (`SHBatchTrace I`), per-step corruption bounds and `ckey` monotonicity, and
`O(N * (r + 1) + M + 1)` amortized `memoryCost`. -/
theorem shBatchProg_spec {w : ℕ} (I : SHBatchInput) (hw : Fits w I.wordBound) :
    let d := (I.rankThreshold, I.ops.length)
    let s₀ := Memory.State.init I.encode
    let res := (Memory.spec 0).clientResult s₀ (shBatchProg d)
    let s' := (Memory.spec 0).clientState s₀ (shBatchProg d)
    SHBatchProgSafe w d s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (shBatchProg d)) ∧
    memoryCost (shBatchProg d) s₀ ≤
      4 + (240 * I.rankThreshold + 531) * I.numInserts + 254 * I.numExtracts ∧
    res.extBase + 3 * I.numExtracts ≤ s'.frontier ∧
    res.corBase + res.corCount ≤ s'.frontier ∧
    ∃ trace : SHBatchTrace I,
      (List.range I.numExtracts).map (SHBatchExtract.readFrom s'.mem res.extBase) =
        trace.extracts ∧
      ((List.range res.corCount).map (fun i => s'.mem (res.corBase + i))).Perm
        trace.corrupted ∧
      res.corCount = trace.corrupted.length ∧
      2 ^ I.rankThreshold * res.corCount ≤ 12 * I.numInserts := by
  let rt := I.rankThreshold
  let n := I.ops.length
  let s₀ := Memory.State.init I.encode
  have hin : InputFits w I.encode := I.inputFits_encode hw
  have hfit_len : Fits w (I.encode.length + 1) :=
    hw.of_le (by rw [I.encode_length]; unfold SHBatchInput.wordBound shFuelBound; nlinarith)
  have hwf₀ : Memory.WellFormed w s₀ := Memory.wellFormed_init hin hfit_len
  have h16 : Fits w 16 := hw.of_le (by unfold SHBatchInput.wordBound; omega)
  have hfuel_fit : Fits w (shFuelBound rt n) :=
    hw.of_le (by dsimp only [rt, n]; unfold SHBatchInput.wordBound; omega)
  have halloc_fit : Fits w (s₀.frontier + 3 * (n + 1) + 12 * (2 * n + 1) + 16) := by
    refine hw.of_le ?_
    change I.encode.length + 1 + 3 * (n + 1) + 12 * (2 * n + 1) + 16 ≤ _
    rw [I.encode_length]
    unfold SHBatchInput.wordBound shFuelBound
    nlinarith
  obtain ⟨hv_alloc, hmc_alloc, hpool1, hpool2, hs₁_fr, hs₁_mem, hwf₁⟩ :=
    allocPool_spec hwf₀ halloc_fit
  obtain ⟨pool, hpool_def⟩ :
      ∃ pool, pool = (Memory.spec 0).clientResult s₀ (allocPool n (2 * n)) := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁_def⟩ :
      ∃ s₁, s₁ = (Memory.spec 0).clientState s₀ (allocPool n (2 * n)) := ⟨_, rfl⟩
  rw [← hpool_def] at hpool1 hpool2
  rw [← hs₁_def] at hs₁_fr hs₁_mem hwf₁
  let extBase := s₁.frontier
  let s₂ : Memory.State := ⟨s₁.mem, s₁.frontier + 3 * n⟩
  let corBase := s₂.frontier
  let s₃ : Memory.State := ⟨s₂.mem, s₂.frontier + n⟩
  have hs₂_fit : Fits w (s₁.frontier + 3 * n) := by
    refine hw.of_le ?_
    rw [hs₁_fr]
    change I.encode.length + 1 + 3 * (n + 1) + 12 * (2 * n + 1) + 3 * n ≤ _
    rw [I.encode_length]
    unfold SHBatchInput.wordBound shFuelBound
    nlinarith
  have hs₃_fit : Fits w (s₂.frontier + n) := by
    refine hw.of_le ?_
    change s₁.frontier + 3 * n + n ≤ _
    rw [hs₁_fr]
    change I.encode.length + 1 + 3 * (n + 1) + 12 * (2 * n + 1) + 3 * n + n ≤ _
    rw [I.encode_length]
    unfold SHBatchInput.wordBound shFuelBound
    nlinarith
  have hv_ext : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (Memory.allocDirty (3 * n))) :=
    validHistory_allocDirty hs₂_fit
  have hv_cor : (Memory.spec w).ValidHistory s₂
      ((Memory.spec w).clientHistory s₂ (Memory.allocDirty n)) :=
    validHistory_allocDirty hs₃_fit
  have hwf₃ : Memory.WellFormed w s₃ := ⟨hs₃_fit, hwf₁.mem_fits⟩
  let initHandle : SHHandle := ⟨pool.1, pool.2, 0, 0, 0, rt⟩
  have hinv₃ : SHInv w 0 0 n (2 * n) initHandle [] (fun _ => 0) s₃ := by
    refine shInit_inv h16 hwf₃ (Nat.zero_le n) (by omega) ?_ ?_ ?_ hfuel_fit
    · dsimp only [initHandle, s₃, s₂]
      rw [hpool1, hs₁_fr]; omega
    · dsimp only [initHandle, s₃, s₂]
      rw [hpool2, hs₁_fr]; omega
    · rw [hpool1, hpool2]; exact Or.inl le_rfl
  have hpool_disj : ∀ a, extBase ≤ a → a < extBase + 3 * n →
      ¬ InSHPool 0 0 n (2 * n) initHandle a := by
    intro a ha1 _ hin_p
    rcases hin_p with ⟨_, hlt⟩ | ⟨_, hlt⟩
    · dsimp only [initHandle] at hlt
      rw [hpool1] at hlt
      dsimp only [extBase] at ha1
      rw [hs₁_fr] at ha1
      omega
    · dsimp only [initHandle] at hlt
      rw [hpool2] at hlt
      dsimp only [extBase] at ha1
      rw [hs₁_fr] at ha1
      omega
  have hit := shBatch_iterate_spec I hw s₀ extBase
    (fun _ _ => rfl) rfl (by dsimp only [extBase]; rw [hs₁_fr]; omega) n ⟨0, 0, initHandle⟩ s₃
    (by simp only [Nat.zero_add]; rfl)
    (by dsimp only [s₃, s₂, extBase]; omega)
    (fun a ha => hs₁_mem a ha) (by simp only [List.take_zero, List.countP_nil])
    (by simp only [List.take_zero, List.countP_nil]; rfl) rfl
    (by dsimp only [initHandle]; rw [hpool1])
    (by dsimp only [initHandle]; rw [hpool2]; omega)
    (by dsimp only [initHandle, extBase]; rw [hpool1, hs₁_fr]; omega)
    (by dsimp only [initHandle, extBase]; rw [hpool2, hs₁_fr])
    hpool_disj
    h16 hfuel_fit [] (fun _ => 0) hinv₃ [] [] [[]]
    rfl (fun _ hk => absurd hk (Nat.not_lt_zero _)) rfl (fun _ h => nomatch h)
    (by
      simp only [List.take_zero, SHBatchInput.insertedItems, List.filterMap_nil, rootsToEntries,
        forestEntries, List.flatMap_nil, List.map_nil, List.append_nil, List.Perm.refl])
    rfl rfl rfl
    (fun m' hm' _ hst _ h => by
      dsimp only at hm'
      have hm0 : m' = 0 := by omega
      subst hm0
      simp only [List.getElem?_cons_zero] at hst
      rw [← Option.some.inj hst] at h
      exact nomatch h)
    (fun m' hm' _ hst => by
      dsimp only at hm'
      have hm0 : m' = 0 := by omega
      subst hm0
      simp only [List.getElem?_cons_zero] at hst
      rw [← Option.some.inj hst]
      simp)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  obtain ⟨hiter_safe, hv_iter, hop_end, hext_end, hib_end, hnb_end, hic_end, hrt_end, hs₄_fr,
      roots', created', extracts', extractedEntries', states', hinv₄, hlen', hrange', hfound',
      horig', hperm', hslen', hshead', hslast', horig_s', hcor_s', hstep', hcost_iter⟩ := hit
  let env : SHBatchEnv := ⟨shFuelBound rt n, extBase⟩
  obtain ⟨st_end, hst_end_def⟩ : ∃ st_end,
      st_end = (Memory.spec 0).clientResult s₃ (iterate shBatchStep env n ⟨0, 0, initHandle⟩) :=
    ⟨_, rfl⟩
  obtain ⟨s₄, hs₄_def⟩ : ∃ s₄,
      s₄ = (Memory.spec 0).clientState s₃ (iterate shBatchStep env n ⟨0, 0, initHandle⟩) :=
    ⟨_, rfl⟩
  rw [← hst_end_def] at hib_end hnb_end hic_end hrt_end hinv₄
  rw [← hs₄_def] at hs₄_fr hinv₄ hrange'
  have hs₄_fr_exact : s₄.frontier = corBase + n := by
    rw [hs₄_fr]
  have hcor_len_le : ((forestEntries roots').filter
      (fun p => decide (p.1.origKey < p.2))).length ≤ n := by
    have h1 := List.length_filter_le (fun p : SHItem × ℕ => decide (p.1.origKey < p.2))
      (forestEntries roots')
    have h2 : (forestEntries roots').length = (rootsToEntries roots').length := by
      simp only [rootsToEntries, List.length_map]
    have h3 : (rootsToEntries roots').length ≤ I.insertedItems.length := by
      have hplen := hperm'.length_eq
      simp only [List.length_map, List.length_append] at hplen
      omega
    have h4 := I.insertedItems_length
    have h5 := I.numInserts_add_numExtracts
    omega
  have hcol_disj : ∀ a, corBase + 0 ≤ a → a < corBase + n →
      ¬ InSHPool 0 0 n (2 * n) st_end.handle a := by
    intro a ha1 _ hin_p
    rcases hin_p with ⟨_, hlt⟩ | ⟨_, hlt⟩
    · rw [hib_end] at hlt
      dsimp only [initHandle] at hlt
      rw [hpool1] at hlt
      dsimp only [corBase, s₂, extBase] at ha1
      rw [hs₁_fr] at ha1
      omega
    · rw [hnb_end] at hlt
      dsimp only [initHandle] at hlt
      rw [hpool2] at hlt
      dsimp only [corBase, s₂, extBase] at ha1
      rw [hs₁_fr] at ha1
      omega
  have hcol_fuel : st_end.handle.itemCount - 0 ≤ shFuelBound rt n := by
    rw [hic_end, Nat.sub_zero]
    have := I.numInserts_add_numExtracts
    unfold shFuelBound
    nlinarith
  have hcol_fit : Fits w (n + 1) :=
    hw.of_le (by unfold SHBatchInput.wordBound shFuelBound; nlinarith)
  obtain ⟨hv_col, hsafe_col, hnewOut, hs₅_fr, hmem_col, hinv₅, hperm_col, hcost_col⟩ :=
    shCollectCorrupted_spec (outCount := 0) hinv₄ hcol_fuel
      (by rw [Nat.zero_add]; exact hcor_len_le)
      (by rw [hs₄_fr_exact]) hcol_fit hcol_disj
  obtain ⟨corCount, hcor_def⟩ : ∃ corCount, corCount = (Memory.spec 0).clientResult s₄
      (shCollectCorrupted (st_end.handle, 0, corBase, 0, shFuelBound rt n)) := ⟨_, rfl⟩
  obtain ⟨s₅, hs₅_def⟩ : ∃ s₅, s₅ = (Memory.spec 0).clientState s₄
      (shCollectCorrupted (st_end.handle, 0, corBase, 0, shFuelBound rt n)) := ⟨_, rfl⟩
  rw [← hcor_def] at hnewOut hperm_col hmem_col
  rw [← hs₅_def] at hs₅_fr hmem_col hinv₅ hperm_col
  have hprog_res : (Memory.spec 0).clientResult s₀ (shBatchProg (rt, n)) =
      ⟨extBase, corBase, corCount⟩ := by
    dsimp only [shBatchProg]
    rw [StateTransitionSpec.clientResult_bind, ← hpool_def, ← hs₁_def,
      StateTransitionSpec.clientResult_bind, clientState_allocDirty, clientResult_allocDirty,
      StateTransitionSpec.clientResult_bind, clientState_allocDirty, clientResult_allocDirty,
      StateTransitionSpec.clientResult_bind, ← hst_end_def, ← hs₄_def,
      StateTransitionSpec.clientResult_bind, ← hcor_def, StateTransitionSpec.clientResult_pure]
  have hprog_st : (Memory.spec 0).clientState s₀ (shBatchProg (rt, n)) = s₅ := by
    dsimp only [shBatchProg]
    rw [StateTransitionSpec.clientState_bind, ← hpool_def, ← hs₁_def,
      StateTransitionSpec.clientState_bind, clientState_allocDirty, clientResult_allocDirty,
      StateTransitionSpec.clientState_bind, clientState_allocDirty, clientResult_allocDirty,
      StateTransitionSpec.clientState_bind, ← hst_end_def, ← hs₄_def,
      StateTransitionSpec.clientState_bind, ← hcor_def, ← hs₅_def,
      StateTransitionSpec.clientState_pure]
  have hprog_safe : SHBatchProgSafe w (rt, n) s₀ := by
    dsimp only [SHBatchProgSafe]
    rw [← hpool_def, ← hs₁_def, ← hst_end_def, ← hs₄_def]
    exact ⟨h16, halloc_fit, hfuel_fit, hiter_safe, hsafe_col⟩
  have hprog_hv : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (shBatchProg (rt, n))) := by
    dsimp only [shBatchProg]
    refine validHistory_bind_step hv_alloc ?_
    rw [← hpool_def, ← hs₁_def]
    refine validHistory_bind_step hv_ext ?_
    rw [clientState_allocDirty, clientResult_allocDirty]
    refine validHistory_bind_step hv_cor ?_
    rw [clientState_allocDirty, clientResult_allocDirty]
    refine validHistory_bind_step hv_iter ?_
    rw [← hst_end_def, ← hs₄_def]
    exact validHistory_bind_step hv_col (validHistory_pure w _ _)
  have hprog_cost : memoryCost (shBatchProg (rt, n)) s₀ ≤
      4 + (240 * rt + 531) * I.numInserts + 254 * I.numExtracts := by
    have hmc_eq : memoryCost (shBatchProg (rt, n)) s₀ =
        2 + 1 + 1 + memoryCost (iterate shBatchStep env n ⟨0, 0, initHandle⟩) s₃ +
          memoryCost (shCollectCorrupted (st_end.handle, 0, corBase, 0, shFuelBound rt n)) s₄ := by
      dsimp only [shBatchProg]
      rw [memoryCost_bind', hmc_alloc, ← hpool_def, ← hs₁_def,
        memoryCost_bind', memoryCost_allocDirty, clientState_allocDirty, clientResult_allocDirty,
        memoryCost_bind', memoryCost_allocDirty, clientState_allocDirty, clientResult_allocDirty,
        memoryCost_bind', ← hst_end_def, ← hs₄_def,
        memoryCost_bind', memoryCost_pure]
      dsimp only [env, s₃, s₂, corBase, extBase, initHandle]
      omega
    have hiter_q : (memoryCost (iterate shBatchStep env n ⟨0, 0, initHandle⟩) s₃ : ℚ) ≤
        (240 * (rt : ℚ) + 523) * (I.numInserts : ℚ) + 254 * (I.numExtracts : ℚ) := by
      have hnn := totalPhi_nonneg rt roots'
      have hnil := totalPhi_nil rt
      simp only [List.drop_zero] at hcost_iter
      rw [hnil, zero_add] at hcost_iter
      change _ + totalPhi rt roots' ≤
        (240 * (rt : ℚ) + 523) * (I.numInserts : ℚ) + 254 * (I.numExtracts : ℚ) at hcost_iter
      linarith
    have hiter_nat : memoryCost (iterate shBatchStep env n ⟨0, 0, initHandle⟩) s₃ ≤
        (240 * rt + 523) * I.numInserts + 254 * I.numExtracts := by
      exact_mod_cast hiter_q
    rw [hmc_eq]
    rw [hic_end, Nat.sub_zero] at hcost_col
    have hmul : (240 * rt + 523) * I.numInserts + 8 * I.numInserts =
        (240 * rt + 531) * I.numInserts := by ring
    omega
  have hmem_ext_s5 :
      (List.range I.numExtracts).map (SHBatchExtract.readFrom s₅.mem extBase) = extracts' := by
    rw [← hrange']
    refine List.map_congr_left fun k hk => ?_
    rw [List.mem_range] at hk
    have hlt_n : k < n := by have := I.numInserts_add_numExtracts; omega
    have h0 : s₅.mem (extBase + 3 * k) = s₄.mem (extBase + 3 * k) := by
      by_contra hne
      have := (hmem_col _ hne).1
      dsimp only [corBase, s₂] at this
      omega
    have h1 : s₅.mem (extBase + 3 * k + 1) = s₄.mem (extBase + 3 * k + 1) := by
      by_contra hne
      have := (hmem_col _ hne).1
      dsimp only [corBase, s₂] at this
      omega
    have h2 : s₅.mem (extBase + 3 * k + 2) = s₄.mem (extBase + 3 * k + 2) := by
      by_contra hne
      have := (hmem_col _ hne).1
      dsimp only [corBase, s₂] at this
      omega
    simp only [SHBatchExtract.readFrom, h0, h1, h2]
  let rem := rootsToEntries roots'
  let corList := (rem.filter (fun e => decide (e.origKey < e.ckey))).map SHBatchEntry.val
  have hcor_list_eq : corList =
      ((forestEntries roots').filter (fun p => decide (p.1.origKey < p.2))).map
        (fun p => p.1.val) := by
    dsimp only [corList, rem, rootsToEntries]
    induction forestEntries roots' with
    | nil => rfl
    | cons p rest ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases hlt : p.1.origKey < p.2
      · simp only [hlt, decide_true, ↓reduceIte, List.map_cons, ih]
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, ih]
  have hcor_bound : 2 ^ rt * corList.length ≤ 12 * I.numInserts := by
    have hcb := shInv_corrupted_le hinv₅
    rw [hrt_end, hic_end, Nat.sub_zero] at hcb
    rw [hcor_list_eq, List.length_map]
    exact hcb
  let trace : SHBatchTrace I :=
    { extracts := extracts'
      extractedEntries := extractedEntries'
      remaining := rem
      corrupted := corList
      states := states'
      extracts_length := hlen'
      extracts_found := hfound'
      extracted_origKey_le := horig'
      remaining_origKey_le := fun e he => by
        simp only [rem, rootsToEntries, List.mem_map] at he
        rcases he with ⟨p, hp, rfl⟩
        exact hinv₅.origKey_le_ckey p hp
      corrupted_eq := rfl
      items_perm := hperm'
      corrupted_bound := hcor_bound
      states_length := hslen'
      states_head := hshead'
      states_last := hslast'
      states_origKey_le := horig_s'
      states_corrupted_bound := hcor_s'
      step_spec := hstep' }
  refine ⟨hprog_safe, hprog_hv, hprog_cost, ?_, ?_, trace, ?_, ?_, ?_, ?_⟩
  · rw [hprog_res, hprog_st, hs₅_fr, hs₄_fr_exact]
    dsimp only [corBase, s₂]
    have := I.numInserts_add_numExtracts
    omega
  · rw [hprog_res, hprog_st, hs₅_fr, hs₄_fr_exact]
    dsimp only
    rw [hnewOut, Nat.zero_add]
    exact Nat.add_le_add_left hcor_len_le corBase
  · rw [hprog_res, hprog_st]
    exact hmem_ext_s5
  · rw [hprog_res, hprog_st]
    dsimp only [trace]
    rw [hcor_list_eq]
    simpa only [Nat.sub_zero, Nat.add_zero] using hperm_col
  · rw [hprog_res]
    dsimp only [trace]
    rw [hnewOut, Nat.zero_add, hcor_list_eq, List.length_map]
  · rw [hprog_res]
    dsimp only
    rw [hnewOut, Nat.zero_add]
    have hcb := shInv_corrupted_le hinv₅
    rwa [hrt_end, hic_end, Nat.sub_zero] at hcb

/-! ### Uniform Standard-Basis Lowered Theorems -/

/-- Single-heap batch step toward `#8624` (supporting `insert`, `extractMin`, and
`collectCorrupted`, without `meld` or arbitrary-handle `delete`, matching
`[PettieRamachandran2002]`, Section 3.2, pp. 21–22, Figure 1 and the remark after Lemma 3.3 on
p. 22), after `[Chazelle2000]`, Theorem 1.1 and Section 5.1, Lemmas 5.1–5.2 (NECI TR 99-097
preprint, pp. 2, 12–13), and `[PettieRamachandran2002]`, Section 2.4, p. 19, Lemma 2.2. There is a
fixed deterministic width-blind standard-basis program
(`¬prog.ReadsWidth`, `prog.IsRandFree`) that, given `State.init I.encode` for any
`I : SHBatchInput` and any word width `w` satisfying `Fits w I.wordBound`, executes `I.ops` in
`n + 1 ≤ C * (I.numInserts * (I.rankThreshold + 1) + I.numExtracts + 1)` native instructions,
producing the exact extraction array at `res.extBase`, harvested corrupted array at
`res.corBase[0..res.corCount)` in `memoryState frontier y`, and trace witness `trace` with per-step
corruption bounds (`12 / 2 ^ r` self-contained `sizeCap` recurrence) and `ckey` monotonicity. -/
theorem exists_singleSoftHeap_batch_standard_program :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r,
      ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ out : Fin 3 → Fin r,
      ∀ {w : ℕ} (I : SHBatchInput), Fits w I.wordBound →
        ∃ y n, Runs w prog (State.init I.encode) ⟨pc, y⟩ n ∧
          let res : SHBatchResult := ⟨y.regs (out 0), y.regs (out 1), y.regs (out 2)⟩
          step w prog ⟨pc, y⟩ = .halt res.extBase ∧
          Memory.WellFormed w (memoryState frontier y) ∧
          res.extBase + 3 * I.numExtracts ≤ (memoryState frontier y).frontier ∧
          res.corBase + res.corCount ≤ (memoryState frontier y).frontier ∧
          (∃ trace : SHBatchTrace I,
            (List.range I.numExtracts).map
              (SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase) =
              trace.extracts ∧
            ((List.range res.corCount).map
              (fun i => (memoryState frontier y).mem (res.corBase + i))).Perm
              trace.corrupted ∧
            res.corCount = trace.corrupted.length ∧
            2 ^ I.rankThreshold * res.corCount ≤ 12 * I.numInserts) ∧
          n + 1 ≤ C * (I.numInserts * (I.rankThreshold + 1) + I.numExtracts + 1) := by
  obtain ⟨r, C₁, pc, prog₀, hnw₀, frontier, out, he⟩ :=
    realizes_shBatchProg.exists_standard_basis_init_program_state_from_words (0 : Fin 3)
  let prog := stripRand prog₀
  refine ⟨r, 531 * C₁ + 1, pc, prog, not_readsWidth_stripRand hnw₀,
    isRandFree_stripRand prog₀, frontier, out, ?_⟩
  intro w I hw
  have hin : InputFits w I.encode := I.inputFits_encode hw
  have hfit_len : Fits w (I.encode.length + 1) :=
    hw.of_le (by rw [I.encode_length]; unfold SHBatchInput.wordBound shFuelBound; nlinarith)
  have hlayout : ∀ j : Fin 2,
      I.encode.getD j.val 0 =
        WordEncoding.encode (α := ℕ × ℕ) (I.rankThreshold, I.ops.length) j := by
    rintro ⟨_ | _ | _, hj⟩
    · rfl
    · rfl
    · omega
  have hk : 2 ≤ I.encode.length := by rw [I.encode_length]; omega
  obtain ⟨hsafe, hv, hmc, hext_lt, hcor_lt, trace, htrace_ext, htrace_cor, htrace_len,
      htrace_bnd⟩ := shBatchProg_spec I hw
  obtain ⟨y, n, hruns₀, hhalt₀, hmem, hout, hsteps⟩ :=
    he w (I.rankThreshold, I.ops.length) I.encode hlayout hk hfit_len hin hsafe hv
  rw [clientState_width w] at hmem
  rw [clientResult_width w] at hhalt₀ hout
  let res₀ := (Memory.spec 0).clientResult (Memory.State.init I.encode)
    (shBatchProg (I.rankThreshold, I.ops.length))
  have hres_eq : (⟨y.regs (out 0), y.regs (out 1), y.regs (out 2)⟩ : SHBatchResult) = res₀ := by
    have h0 := hout 0
    have h1 := hout 1
    have h2 := hout 2
    cases hres₀ : res₀ with
    | mk eb cb cc =>
      have h0' : y.regs (out 0) = eb := by
        change y.regs (out 0) = WordEncoding.encode res₀ 0 at h0
        rw [hres₀] at h0; exact h0
      have h1' : y.regs (out 1) = cb := by
        change y.regs (out 1) = WordEncoding.encode res₀ 1 at h1
        rw [hres₀] at h1; exact h1
      have h2' : y.regs (out 2) = cc := by
        change y.regs (out 2) = WordEncoding.encode res₀ 2 at h2
        rw [hres₀] at h2; exact h2
      simp only [h0', h1', h2']
  have hwf_y : Memory.WellFormed w (memoryState frontier y) := by
    rw [hmem]
    exact wellFormed_clientState (Memory.wellFormed_init hin hfit_len) hv
  have hhalt_res : step w prog ⟨pc, y⟩ =
      .halt (⟨y.regs (out 0), y.regs (out 1), y.regs (out 2)⟩ : SHBatchResult).extBase := by
    rw [hres_eq]
    exact step_stripRand_of_halt hhalt₀
  have hmc_bound : memoryCost (shBatchProg (I.rankThreshold, I.ops.length))
      (Memory.State.init I.encode) + 0 + 1 ≤
      531 * (I.numInserts * (I.rankThreshold + 1) + I.numExtracts + 1) := by
    have hmul : (240 * I.rankThreshold + 531) * I.numInserts ≤
        531 * (I.numInserts * (I.rankThreshold + 1)) := by
      have h1 : 240 * I.rankThreshold + 531 ≤ 531 * (I.rankThreshold + 1) := by omega
      calc (240 * I.rankThreshold + 531) * I.numInserts
          ≤ (531 * (I.rankThreshold + 1)) * I.numInserts := Nat.mul_le_mul_right _ h1
        _ = 531 * (I.numInserts * (I.rankThreshold + 1)) := by ring
    omega
  have hsteps_bound : n + 1 ≤
      (531 * C₁ + 1) * (I.numInserts * (I.rankThreshold + 1) + I.numExtracts + 1) := by
    have hmul := Nat.mul_le_mul_left C₁ hmc_bound
    have hpos : 1 ≤ I.numInserts * (I.rankThreshold + 1) + I.numExtracts + 1 := Nat.succ_pos _
    nlinarith
  refine ⟨y, n, runs_stripRand hruns₀, ?_⟩
  dsimp only
  have h0_eq : y.regs (out 0) = res₀.extBase := congrArg SHBatchResult.extBase hres_eq
  have h1_eq : y.regs (out 1) = res₀.corBase := congrArg SHBatchResult.corBase hres_eq
  have h2_eq : y.regs (out 2) = res₀.corCount := congrArg SHBatchResult.corCount hres_eq
  rw [hmem]
  refine ⟨?_, ?_, ?_, ?_, ?_, hsteps_bound⟩
  · exact hhalt_res
  · rw [← hmem]; exact hwf_y
  · rw [h0_eq]; exact hext_lt
  · rw [h1_eq, h2_eq]; exact hcor_lt
  · rw [h0_eq, h1_eq, h2_eq]
    exact ⟨trace, htrace_ext, htrace_cor, htrace_len, htrace_bnd⟩

/-- Single-heap batch step toward `#8624` (supporting `insert`, `extractMin`, and
`collectCorrupted`, without `meld` or arbitrary-handle `delete`, matching
`[PettieRamachandran2002]`, Section 3.2, pp. 21–22, Figure 1 and the remark after Lemma 3.3 on
p. 22), after `[Chazelle2000]`, Theorem 1.1 and Section 5.1, Lemmas 5.1–5.2 (NECI TR 99-097
preprint, pp. 2, 12–13), and `[PettieRamachandran2002]`, Section 2.4, p. 19, Lemma 2.2.
Specializes `exists_singleSoftHeap_batch_standard_program` to any rational `0 < ε` (extending
Chazelle Theorem 1.1's `0 < ε ≤ 1 / 2` and PR02 Lemma 2.2's `0 < ε < 1 / 2` via this module's
self-contained `rankThresholdForEps ε` parameterization), guaranteeing at most `ε * #inserts`
corrupted items at every step and
`O(I.numInserts * (rankThresholdForEps ε + 1) + I.numExtracts + 1)` instructions. -/
theorem exists_singleSoftHeap_batch_standard_program_eps :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r,
      ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ out : Fin 3 → Fin r,
      ∀ (ε : ℚ), 0 < ε → ∀ {w : ℕ} (I : SHBatchInput),
        I.rankThreshold = rankThresholdForEps ε → Fits w I.wordBound →
        ∃ y n, Runs w prog (State.init I.encode) ⟨pc, y⟩ n ∧
          let res : SHBatchResult := ⟨y.regs (out 0), y.regs (out 1), y.regs (out 2)⟩
          step w prog ⟨pc, y⟩ = .halt res.extBase ∧
          Memory.WellFormed w (memoryState frontier y) ∧
          res.extBase + 3 * I.numExtracts ≤ (memoryState frontier y).frontier ∧
          res.corBase + res.corCount ≤ (memoryState frontier y).frontier ∧
          (∃ trace : SHBatchTrace I,
            (List.range I.numExtracts).map
              (SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase) =
              trace.extracts ∧
            ((List.range res.corCount).map
              (fun i => (memoryState frontier y).mem (res.corBase + i))).Perm
              trace.corrupted ∧
            res.corCount = trace.corrupted.length ∧
            (res.corCount : ℚ) ≤ ε * (I.numInserts : ℚ) ∧
            (∀ j ≤ I.ops.length, ∀ st : List SHBatchEntry,
              trace.states[j]? = some st →
              ((st.filter (fun e => decide (e.origKey < e.ckey))).length : ℚ) ≤
                ε * (((I.ops.take j).countP SHOp.isInsert : ℕ) : ℚ))) ∧
          n + 1 ≤ C * (I.numInserts * (rankThresholdForEps ε + 1) + I.numExtracts + 1) := by
  obtain ⟨r, C, pc, prog, hnw, hrf, frontier, out, hmain⟩ :=
    exists_singleSoftHeap_batch_standard_program
  refine ⟨r, C, pc, prog, hnw, hrf, frontier, out, ?_⟩
  intro ε hε w I hrt hw
  obtain ⟨y, n, hruns, hhalt, hwf, hext_lt, hcor_lt,
      ⟨trace, hexts, hcor_perm, hcor_len, hcor_bnd⟩, hsteps⟩ := hmain I hw
  exact ⟨y, n, hruns, hhalt, hwf, hext_lt, hcor_lt,
    ⟨trace, hexts, hcor_perm, hcor_len, rat_le_eps_mul_of_pow_mul_le hε (hrt ▸ hcor_bnd),
      fun _ hj _ hst => trace.states_corrupted_le_eps hε hrt hj hst⟩,
    hrt ▸ hsteps⟩

end

end Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
