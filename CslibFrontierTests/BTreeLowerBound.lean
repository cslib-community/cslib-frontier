/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.LowerBound

/-!
# Tests for the B-tree rank comparison lower bound

Checks that:
* both `rankQ` (linear in-node scan) and `rankBinQ` (binary in-node search) satisfy `IsRank`;
* `IsRank.lowerBound_wfInput_infinite` composes directly with `rankBinQ_upperBound_size` and
  `rankQ_upperBound_size` via `Cslib.Query.LowerBound.le_upperBound`;
* on an unsorted tree, `rankQ` can disagree with the full-list filter count, witnessing that the
  strict key-sortedness premise of `IsRank` is essential.
-/

public section

namespace CslibFrontierTests.BTreeLowerBound

open Cslib.DataStructure
open Cslib.DataStructure.BTree
open Cslib.Query (LEQuery LowerBound)

/-- Both B-tree rank programs satisfy `IsRank` on `(ℕ, String)`. -/
example : IsRank (rankQ (α := ℕ) (β := String)) := rankQ_isRank

example : IsRank (rankBinQ (α := ℕ) (β := String)) := rankBinQ_isRank

/-- Concrete evaluation through `IsRank.correct` on a well-formed two-level tree. -/
def sampleTree : BTree ℕ String :=
  .node (.node .leaf [(1, "a", .leaf), (2, "b", .leaf)])
    [(4, "c", .node .leaf [(6, "d", .leaf), (8, "e", .leaf)])]

example : (rankQ 5 sampleTree).eval orderOracle = 3 := by
  have hsorted : (sampleTree.toList.map Prod.fst).Pairwise (fun a b : ℕ => a ≤ b ∧ ¬ b ≤ a) := by
    decide
  rw [rankQ_isRank.correct 5 sampleTree orderOracle (· ≤ ·) (fun _ _ => rfl) hsorted]
  decide

example : (rankBinQ 5 sampleTree).eval orderOracle = 3 := by
  have hsorted : (sampleTree.toList.map Prod.fst).Pairwise (fun a b : ℕ => a ≤ b ∧ ¬ b ≤ a) := by
    decide
  rw [rankBinQ_isRank.correct 5 sampleTree orderOracle (· ≤ ·) (fun _ _ => rfl) hsorted]
  decide

/-- Per-tree lower bound on `sampleTree` (`size = 5`, so `⌈log₂(5 + 1)⌉ = 3` comparisons). -/
example : ∃ (k : ℕ) (oracle : {ι : Type} → LEQuery ℕ ι → ι),
    3 ≤ (rankBinQ k sampleTree).countQueries oracle := by
  have hnodup : (sampleTree.toList.map Prod.fst).Nodup := by decide
  obtain ⟨k, oracle, h⟩ := rank_lowerBound_infinite rankBinQ_isRank sampleTree hnodup
  exact ⟨k, oracle, (by decide : 3 ≤ Nat.clog 2 (sampleTree.size + 1)).trans h⟩

/-- Uncurried `LowerBound` for `rankQ` and `rankBinQ` without fixing a tree degree. -/
example : LowerBound (fun p : BTree ℕ Unit × ℕ => rankQ p.2 p.1) (fun p => p.1.size)
    (fun n => Nat.clog 2 (n + 1)) :=
  rankQ_isRank.lowerBound_infinite

example : LowerBound (fun p : BTree ℕ Unit × ℕ => rankBinQ p.2 p.1) (fun p => p.1.size)
    (fun n => Nat.clog 2 (n + 1)) :=
  rankBinQ_isRank.lowerBound_infinite

/-- Composing `IsRank.lowerBound_wfInput_infinite` with `rankBinQ_upperBound_size` via
`LowerBound.le_upperBound` directly yields the numeric comparison inequality at every `t ≥ 2`
and `n`. -/
example {t : ℕ} (ht : 2 ≤ t) (n : ℕ) :
    Nat.clog 2 (n + 1) ≤ Nat.clog 2 (2 * t) * (Nat.log t ((n + 1) / 2) + 1) :=
  ((rankBinQ_isRank (α := ℕ) (β := Unit)).lowerBound_wfInput_infinite ht).le_upperBound
    rankBinQ_upperBound_size n

/-- The same for linear in-node scan, with `rankQ_upperBound_size`. -/
example {t : ℕ} (ht : 2 ≤ t) (n : ℕ) :
    Nat.clog 2 (n + 1) ≤ 2 * t * (Nat.log t ((n + 1) / 2) + 1) :=
  ((rankQ_isRank (α := ℕ) (β := Unit)).lowerBound_wfInput_infinite ht).le_upperBound
    rankQ_upperBound_size n

/-- Without the sortedness hypothesis of `IsRank`, `rankQ` on an out-of-order B-tree misses a
smaller key placed in the right subtree (`3 > 2 > 0`, with `0` hidden to the right of `2`). -/
def outOfOrderTree : BTree ℕ Unit :=
  .node (.node .leaf [(3, (), .leaf)]) [(2, (), .node .leaf [(0, (), .leaf)])]

example : (rankQ 1 outOfOrderTree).eval orderOracle = 0 ∧
    (outOfOrderTree.toList.filter fun x => x.1 < 1).length = 1 := by
  refine ⟨?_, by decide⟩
  simp [outOfOrderTree, rankQ_def, rankM_node_cons, rankM_leaf, orderOracle]

end CslibFrontierTests.BTreeLowerBound
