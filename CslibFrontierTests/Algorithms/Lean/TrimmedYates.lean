/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Algorithms.Lean.TrimmedYates
import CslibFrontier.Algorithms.WordRAM.TrimmedYates

/-!
# Tests for the trimmed Yates passes (pure and Word-RAM)

Concrete checks on both `CslibFrontier.Algorithms.Lean.TrimmedYates` and
`CslibFrontier.Algorithms.WordRAM.TrimmedYates` as an encapsulated downstream `module` client:

* pure `solve` on `Fin 4` with ranked inputs (`t = 1`, `s = 1`) and `solve_eq_subsetConvolution`;
* separation between `coveringProduct` and `subsetConvolution` on unranked inputs;
* concrete `ExecutesList` witnesses for `WordRAM.TrimmedYates.program` on positive-weight,
  negative/duplicate-entry, empty-universe, and short-query (`#C < s`) boundary instances.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.TrimmedYates

open Finset Cslib.BitString Cslib.Algorithms.Lean.TrimmedYates Cslib.WordRAM
open Cslib.Algorithms.WordRAM.TrimmedYates

/-- Left input: weight `2` on `{0}` and `3` on `{1}`. -/
def f : Finset (Fin 4) → ℤ := fun A => if A = {0} then 2 else if A = {1} then 3 else 0

/-- Right input: weight `5` on `{1}` and `7` on `{2}`. -/
def g : Finset (Fin 4) → ℤ := fun B => if B = {1} then 5 else if B = {2} then 7 else 0

/-- Three queries of size `2t = 2`. -/
def queries : List (Finset (Fin 4)) := [{0, 1}, {1, 2}, {0, 3}]

theorem f_ranked : ∀ A, f A ≠ 0 → #A = 1 := by
  intro A h
  unfold f at h
  split_ifs at h with h₀ h₁ <;> simp_all

theorem g_ranked : ∀ B, g B ≠ 0 → #B = 1 := by
  intro B h
  unfold g at h
  split_ifs at h with h₀ h₁ <;> simp_all

theorem queries_ok : ∀ C ∈ queries, C ⊆ (List.finRange 4).toFinset ∧ #C = 1 + 1 := by
  decide

/-- Pure evaluation: `f{0} g{1} + f{1} g{0} = 10`, `f{1} g{2} = 21`, and `0` at `{0, 3}`. -/
example : solve (List.finRange 4) 1 f g queries = [10, 21, 0] := by decide +kernel

/-- The same answers equal the subset convolutions by `solve_eq_subsetConvolution`. -/
example : queries.map (subsetConvolution f g) = [10, 21, 0] := by
  rw [← solve_eq_subsetConvolution (List.nodup_finRange 4) f_ranked g_ranked queries_ok
    (by decide : 1 ≤ 1 + 1)]
  decide +kernel

/-- Unranked inputs: with `f = g = 1` on all sets, the covering product at `{0}` counts the three
covers `(∅, {0}), ({0}, ∅), ({0}, {0})`, while the subset convolution counts the two partitions. -/
example : coveringProduct (fun _ => (1 : ℤ)) (fun _ => 1) ({0} : Finset (Fin 1)) = 3 ∧
    subsetConvolution (fun _ => (1 : ℤ)) (fun _ => 1) ({0} : Finset (Fin 1)) = 2 := by
  decide +kernel

/-- Sparse Word-RAM instance corresponding to `f`, `g`, and `queries` on `Fin 4`. -/
def inst4 : Instance where
  d := 4
  s := 1
  leftEntries := [({0}, 2), ({1}, 3)]
  rightEntries := [({1}, 5), ({2}, 7)]
  queries := [{0, 1}, {1, 2}, {0, 3}]

/-- Concrete Word-RAM `ExecutesList` witness on `inst4` at word width `64`, bounding the halting
run by `250 * 5 ^ 2 * (4 + 5 + 3 * 3) = 112500` instructions via `executesList_program`. -/
example : ∃ n, ExecutesList 64 program (.init inst4.encode)
    [Signed.encode 10, Signed.encode 21, Signed.encode 0] n ∧ n ≤ 112500 := by
  have hrun := executesList_program (t₁ := 1) (t₂ := 1) (w := 64) inst4
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have hout : (inst4.queries.map (subsetConvolution inst4.leftFn inst4.rightFn)).map
      Signed.encode = [Signed.encode 10, Signed.encode 21, Signed.encode 0] := by decide +kernel
  have hbnd : 250 * (inst4.d + 1) ^ 2 *
      (inst4.numEntries + lowCount inst4.d inst4.s +
        inst4.queries.length * highCount (1 + 1) inst4.s) = 112500 := by decide +kernel
  rwa [hout, hbnd] at hrun

/-- Ranked instance with duplicate set keys (`5 + (-3) = 2` on `{0}`) and negative weights. -/
def negInst : Instance where
  d := 4
  s := 1
  leftEntries := [({0}, 5), ({0}, -3), ({1}, -4)]
  rightEntries := [({1}, 5), ({2}, -7)]
  queries := [{0, 1}, {1, 2}, {0, 2}]

/-- Word-RAM `ExecutesList` witness with negative weights and duplicate entry accumulation:
`f{0} g{1} = 10`, `f{1} g{2} = 28`, and `f{0} g{2} = -14`. -/
example : ∃ n, ExecutesList 64 program (.init negInst.encode)
    [Signed.encode 10, Signed.encode 28, Signed.encode (-14)] n ∧ n ≤ 118750 := by
  have hrun := executesList_program (t₁ := 1) (t₂ := 1) (w := 64) negInst
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have hout : (negInst.queries.map (subsetConvolution negInst.leftFn negInst.rightFn)).map
      Signed.encode =
      [Signed.encode 10, Signed.encode 28, Signed.encode (-14)] := by decide +kernel
  have hbnd : 250 * (negInst.d + 1) ^ 2 *
      (negInst.numEntries + lowCount negInst.d negInst.s +
        negInst.queries.length * highCount (1 + 1) negInst.s) = 118750 := by decide +kernel
  rwa [hout, hbnd] at hrun

/-- Boundary case: empty universe (`d = 0`), empty entries, and empty queries at minimal fitting
word width `w = 10`. -/
def emptyInst : Instance where
  d := 0
  s := 0
  leftEntries := []
  rightEntries := []
  queries := []

example : ∃ n, ExecutesList 6 program (.init emptyInst.encode) [] n ∧ n ≤ 250 := by
  have hw : emptyInst.FitsWidth 6 := ⟨by decide +kernel, by decide +kernel⟩
  have hrun := computesListInTime_program emptyInst 6 hw hw.inputFits
  have hout : (emptyInst.queries.map (coveringProduct emptyInst.leftFn emptyInst.rightFn)).map
      Signed.encode = [] := rfl
  have hbnd : emptyInst.timeBound = 250 := by decide +kernel
  dsimp only at hrun
  rwa [hout, hbnd] at hrun

/-- Boundary case: query with `#C < s` (`|{0}| = 1 < 2`) answered directly from preprocessing. -/
def shortQueryInst : Instance where
  d := 3
  s := 2
  leftEntries := [(∅, 3)]
  rightEntries := [({0}, 4)]
  queries := [{0}]

example : ∃ n, ExecutesList 64 program (.init shortQueryInst.encode)
    [Signed.encode 12] n ∧ n ≤ 40000 := by
  have hw : shortQueryInst.FitsWidth 64 := ⟨by decide +kernel, by decide +kernel⟩
  have hrun := computesListInTime_program shortQueryInst 64 hw hw.inputFits
  have hout : (shortQueryInst.queries.map
      (coveringProduct shortQueryInst.leftFn shortQueryInst.rightFn)).map
      Signed.encode = [Signed.encode 12] := by decide +kernel
  have hbnd : shortQueryInst.timeBound = 40000 := by decide +kernel
  dsimp only at hrun
  rwa [hout, hbnd] at hrun

end CslibFrontierTests.Algorithms.Lean.TrimmedYates
