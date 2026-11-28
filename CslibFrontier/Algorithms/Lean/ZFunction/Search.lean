/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.KMP.Search
public import CslibFrontier.Algorithms.Lean.ZFunction.Basic
import Mathlib.Data.List.Sort

/-!
# Exact pattern matching with the Z-algorithm

The pattern `p` occurs in the text `t` at shift `i` iff the Z-function of `p ++ t` is at least
`|p|` at position `|p| + i` (`[Gusfield1997]`, Section 1.5). `zMatchesArray p t` and `zMatches p t`
compute the Z-function of `p ++ t` with the Z-algorithm and read off these shifts; the output agrees
with the KMP specification `KMP.kmpMatchesList p t` (`zMatches_eq_kmpMatchesList`).

Linear `O(|p| + |t|)` machine-level running-time bounds on word arrays are proved in
`CslibFrontier.Algorithms.WordRAM.ZFunction`.

## Source Conventions

* **Shifts:** `0`-indexed, as in `Cslib.Algorithms.Lean.KMP`. The shift `|t|` is reported exactly
  when `p` is empty.
* **No separator:** Gusfield uses `p $ t` with a separator `$` that occurs in neither word. Here
  there is no separator: values of the Z-function above `|p|` are allowed, and a shift `i` is
  reported when the value at `|p| + i` is at least `|p|`.

## Main definitions

* `Cslib.Algorithms.Lean.ZFunction.zMatchesArray`, `zMatches`: the shifts of `p` in `t` read off
  the Z-function of `p ++ t`.

## Main results

* `Cslib.Algorithms.Lean.ZFunction.mem_zMatches_iff` and `zMatches_eq_filter_range`:
  `i ∈ zMatches p t` iff `i ≤ |t|` and `p` is a prefix of `t.drop i`, giving a kernel-decidable
  closed form `(List.range (t.length + 1)).filter (fun i => decide (p <+: t.drop i))`.
* `Cslib.Algorithms.Lean.ZFunction.pairwise_lt_zMatches`: `zMatches p t` is strictly increasing.
* `Cslib.Algorithms.Lean.ZFunction.zMatches_eq_kmpMatchesList`: the Z-algorithm and KMP report
  the same shifts.

## References

* [D. Gusfield, *Algorithms on Strings, Trees, and Sequences*][Gusfield1997]
-/

public section

namespace Cslib.Algorithms.Lean.ZFunction

open Cslib.Algorithms.Lean

variable {α : Type*} [DecidableEq α]

/-- The shifts `i ≤ |t|` at which `p` occurs in `t`, read off the Z-array of `p ++ t`: those
whose value at `|p| + i` is at least `|p|`. The value past the end is taken to be `0`. -/
def zMatchesArray (p t : Array α) : List ℕ :=
  let z := zArray (p ++ t)
  (List.range (t.size + 1)).filter fun i => p.size ≤ z.getD (p.size + i) 0

/-- Exact pattern matching with the Z-algorithm on lists. -/
def zMatches (p t : List α) : List ℕ :=
  zMatchesArray p.toArray t.toArray

/-- **Correctness of Z-algorithm matching**: `i ∈ zMatches p t` iff `p` occurs in `t` at shift
`i`. -/
theorem mem_zMatches_iff (p t : List α) (i : ℕ) :
    i ∈ zMatches p t ↔ i ≤ t.length ∧ p <+: t.drop i := by
  simp only [zMatches, zMatchesArray, List.mem_filter, List.mem_range, Nat.lt_succ_iff,
    decide_eq_true_eq, List.size_toArray, getD_zArray, Array.toList_append,
    List.drop_length_add_append, List.length_le_lcpLen_append_iff]

/-- `zMatches p t` lists the shifts in strictly increasing order. -/
theorem pairwise_lt_zMatches (p t : List α) : (zMatches p t).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

/-- Explicit filter characterization of `zMatches`, useful for kernel `decide` evaluation in
downstream `module` clients without unfolding the Z-algorithm loop. -/
theorem zMatches_eq_filter_range (p t : List α) :
    zMatches p t = (List.range (t.length + 1)).filter fun i => decide (p <+: t.drop i) :=
  (pairwise_lt_zMatches p t).eq_of_mem_iff (List.pairwise_lt_range.filter _) fun i => by
    rw [mem_zMatches_iff, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun ⟨hle, hp⟩ => ⟨Nat.lt_succ_of_le hle, hp⟩,
      fun ⟨hlt, hp⟩ => ⟨Nat.le_of_lt_succ hlt, hp⟩⟩

/-- **Z-algorithm matching agrees with KMP**: both report the shifts of `p` in `t` in increasing
order. -/
theorem zMatches_eq_kmpMatchesList (p t : List α) : zMatches p t = KMP.kmpMatchesList p t :=
  (pairwise_lt_zMatches p t).eq_of_mem_iff (KMP.pairwise_lt_kmpMatchesList p t) fun i => by
    rw [mem_zMatches_iff, KMP.mem_kmpMatchesList_iff]

end Cslib.Algorithms.Lean.ZFunction
