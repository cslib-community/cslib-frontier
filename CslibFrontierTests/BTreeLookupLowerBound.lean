/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.LookupLowerBound

/-!
# Tests for the B-tree lookup comparison lower bound

Checks that:
* both `lookupQ` and `lookupBinQ` satisfy `IsLookup`;
* under a key oracle with a tie, lookup returns the value of the tied key, unlike under the order
  oracle;
* without ties the correctness predicate is vacuous: a program that asks nothing is correct under
  every injective key function and is not `IsLookup`;
* the strict-increase premise of `IsLookup` is needed, on an out-of-order tree;
* the per-tree bound holds on the empty tree and on a sample tree, and the lower bound composes
  with `lookupBinQ_upperBound_size` and `lookupQ_upperBound_size`.
-/

public section

namespace CslibFrontierTests.BTreeLookupLowerBound

open Cslib (FreeM)
open Cslib.DataStructure
open Cslib.DataStructure.BTree
open Cslib.Query (LEQuery LowerBound)

/-- Both B-tree lookup programs satisfy `IsLookup` on `(ℕ, ℕ)`. -/
example : IsLookup (lookupQ (α := ℕ) (β := ℕ)) := lookupQ_isLookup

example : IsLookup (lookupBinQ (α := ℕ) (β := ℕ)) := lookupBinQ_isLookup

/-- A well-formed two-level tree with keys `1, 2, 4, 6, 8`. -/
def sampleTree : BTree ℕ String :=
  .node (.node .leaf [(1, "a", .leaf), (2, "b", .leaf)])
    [(4, "c", .node .leaf [(6, "d", .leaf), (8, "e", .leaf)])]

-- Review Focus 1: under `· / 2` the keys 4 and 5 tie, so lookup of 5 returns the value at 4.
example : (lookupQ 5 sampleTree).eval (LEQuery.keyOracle (· / 2)) = some "c" := by
  simp [sampleTree, lookupQ_def, lookupM, LEQuery.keyOracle]

example : (lookupBinQ 5 sampleTree).eval (LEQuery.keyOracle (· / 2)) = some "c" := by
  have hs : ((sampleTree.mapKeys (· / 2)).toList).IsSortedAssoc := by
    rw [toList_mapKeys, List.isSortedAssoc_iff_pairwise, List.map_map]
    decide
  rw [eval_lookupBinQ_keyOracle, lookupBin_eq_lookup hs, lookup_eq_of_isSortedAssoc hs,
    toList_mapKeys]
  decide

-- Review Focus 1: the order oracle has no ties, so the same lookup finds nothing.
example : (lookupQ 5 sampleTree).eval orderOracle = none := by
  simp [sampleTree, lookupQ_def, lookupM, orderOracle]

-- Review Focus 2: without ties the predicate is vacuous. A program that asks nothing ...
def nativeLookup (k : ℕ) (tree : BTree ℕ String) : FreeM (LEQuery ℕ) (Option String) :=
  pure (tree.toList.lookup k)

-- ... makes zero comparisons under every oracle ...
example (oracle : {ι : Type} → LEQuery ℕ ι → ι) (k : ℕ) (tree : BTree ℕ String) :
    (nativeLookup k tree).countQueries oracle = 0 := rfl

-- ... and is correct under every injective key function ...
example {W : Type} [LinearOrder W] (key : ℕ → W) (hkey : Function.Injective key) (k : ℕ)
    (tree : BTree ℕ String) :
    (nativeLookup k tree).eval (LEQuery.keyOracle key) =
      (tree.toList.map fun x => (key x.1, x.2)).lookup (key k) := by
  simp only [nativeLookup, FreeM.eval_pure]
  generalize tree.toList = l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    by_cases h : k = a
    · simp [List.lookup, h]
    · have e1 : (k == a) = false := by simpa using h
      have e2 : (key k == key a) = false := by simpa using hkey.ne h
      simp only [List.lookup, List.map_cons, e1, e2, ih]

-- ... yet it is not `IsLookup`: under `· / 2` it misses the tied key 4 when asked for 5.
example : ¬ IsLookup nativeLookup := by
  intro h
  have := h.correct (fun n : ℕ => n / 2) 5 (.node .leaf [(4, "x", .leaf)])
    (by simp [BTree.toList])
  revert this
  simp only [nativeLookup, BTree.toList, FreeM.eval_pure]
  decide

/-- `lookupQ` on an out-of-order tree (`3 > 2 > 0`, with `0` hidden to the right of `2`). -/
def outOfOrderTree : BTree ℕ String :=
  .node (.node .leaf [(3, "a", .leaf)]) [(2, "b", .node .leaf [(0, "c", .leaf)])]

-- Review Focus 3: the strict-increase premise is needed; `0` is stored but `lookupQ 0` misses it.
example : (lookupQ 0 outOfOrderTree).eval orderOracle = none ∧
    outOfOrderTree.toList.lookup 0 = some "c" := by
  refine ⟨?_, by decide⟩
  simp [outOfOrderTree, lookupQ_def, lookupM, orderOracle]

-- Review Focus 4: the per-tree bound on the empty tree, obtained from the theorem at `n = 0`.
example : ∃ (k : ℕ) (oracle : {ι : Type} → LEQuery ℕ ι → ι),
    0 ≤ (lookupQ k (.leaf : BTree ℕ String)).countQueries oracle := by
  obtain ⟨k, oracle, h⟩ :=
    lookup_lowerBound_infinite (lookupQ_isLookup (α := ℕ) (β := String))
    .leaf (by simp [BTree.toList]) (by simp [BTree.toList])
  exact ⟨k, oracle, (Nat.zero_le _).trans h⟩

-- Per-tree bound on `sampleTree`: size 5, so 3 comparisons.
example : ∃ (k : ℕ) (oracle : {ι : Type} → LEQuery ℕ ι → ι),
    3 ≤ (lookupBinQ k sampleTree).countQueries oracle := by
  have hkeys : (sampleTree.toList.map Prod.fst).Nodup := by decide
  have hvals : (sampleTree.toList.map Prod.snd).Nodup := by decide
  obtain ⟨k, oracle, h⟩ := lookup_lowerBound_infinite lookupBinQ_isLookup sampleTree hkeys hvals
  exact ⟨k, oracle, (by decide : 3 ≤ Nat.clog 2 (sampleTree.size + 1)).trans h⟩

-- The lower bound composes with the upper bound.
example {t : ℕ} (ht : 2 ≤ t) (n : ℕ) :
    Nat.clog 2 (n + 1) ≤ (Nat.clog 2 (2 * t) + 1) * (Nat.log t ((n + 1) / 2) + 1) :=
  ((lookupBinQ_isLookup (α := ℕ) (β := ℕ)).lowerBound_wfInput_infinite ht).le_upperBound
    lookupBinQ_upperBound_size n

-- The same for linear in-node search.
example {t : ℕ} (ht : 2 ≤ t) (n : ℕ) :
    Nat.clog 2 (n + 1) ≤ 2 * t * (Nat.log t ((n + 1) / 2) + 1) :=
  ((lookupQ_isLookup (α := ℕ) (β := ℕ)).lowerBound_wfInput_infinite ht).le_upperBound
    lookupQ_upperBound_size n

end CslibFrontierTests.BTreeLookupLowerBound
