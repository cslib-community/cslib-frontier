/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

import CslibFrontier.Algorithms.PointerMachine.MergeSort
import Mathlib.Data.List.Sort

/-! # A checked client of the native pointer-machine sorting theorem -/

set_option linter.privateModule false

namespace CslibFrontierTests.PointerMachineMergeSortProof

open Cslib.PointerMachine Cslib.Algorithms.PointerMachine.MergeSort

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Empty
  Test := Unit
  evalOp op := op.elim
  evalTest _ a b := decide (a < b)

private def node (next : Pointer) (k : ℕ) : Record model layout :=
  ⟨fun _ => next, fun _ => k⟩

-- The input chain starts at record two and visits records zero and one.
private def input : State model layout :=
  ⟨0, fun r => if r = head then some 2 else none, fun _ => 0,
    [node (some 1) 3, node none 1, node (some 0) 1]⟩

example : ∃ y time output, Executes (code (M := model) ()).program input y time ∧
    time ≤ 234 ∧ y.ptr head = output.head? ∧ Segment y output none ∧
    output.map (key y) = [1, 1, 3] := by
  have chain : Segment input [2, 0, 1] none := by
    rw [segment_cons_iff]
    refine ⟨by decide, rfl, ?_⟩
    rw [segment_cons_iff]
    refine ⟨by decide, rfl, ?_⟩
    rw [segment_cons_iff]
    exact ⟨by decide, rfl, segment_nil _ _⟩
  obtain ⟨y, time, output, he, hb, out⟩ := executes_sort () (fun _ _ => rfl) input [2, 0, 1] chain
    (by decide) rfl rfl
  have hsort : ([2, 0, 1].map (key input)).mergeSort = [1, 1, 3] := by
    have hp : ([2, 0, 1].map (key input)).Perm [1, 1, 3] := by decide
    exact ((List.mergeSort_perm _ _).trans hp).eq_of_pairwise'
      (List.pairwise_mergeSort' _ _) (by decide)
  exact ⟨y, time, output, he, hb.trans (by decide), out.head_eq, out.chain,
    out.payloads_eq.trans hsort⟩

end CslibFrontierTests.PointerMachineMergeSortProof
