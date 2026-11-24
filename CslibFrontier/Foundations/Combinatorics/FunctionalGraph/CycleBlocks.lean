/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.HittingTime
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Equally spaced blocks on the cycles reached from a finite set

One row identifies a cycle by its canonical representative and gives the index of a block of
`B` consecutive phases. Across the cycles reached from `H`, at most `|H|` final blocks are
partial, and the disjoint full blocks together occupy at most the whole state space.

## Main results

* `Cslib.FunctionalGraph.exists_cycleBlocks` supplies all the necessary cycle-block keys and
  bounds their total cardinality.
-/

public section

namespace Cslib.FunctionalGraph

open Function

variable {α : Type*} [Fintype α] [LinearOrder α] (f : α → α)

/-- The distinct cycles reached from `H` together contain at most the entire state space. -/
private theorem sum_cycleLength_image_le (H : Finset α) :
    ∑ r ∈ H.image (canonicalCycle f), cycleLength f r ≤ Fintype.card α := by
  classical
  let reps := H.image (canonicalCycle f)
  have hrep (r : ↥reps) : canonicalCycle f r.val = r.val ∧ r.val ∈ periodicPts f := by
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp r.property
    obtain ⟨j, hj⟩ := canonicalCycle_reachable f x
    refine ⟨?_, hx ▸ canonicalCycle_periodic f x⟩
    calc
      canonicalCycle f r.val = canonicalCycle f (f^[j] x) := by rw [hj, hx]
      _ = r.val := (canonicalCycle_iterate f x j).trans hx
  let point (v : Σ r : ↥reps, Fin (cycleLength f r.val)) := f^[v.2.val] v.1.val
  have hinj : Function.Injective point := by
    rintro ⟨r, i⟩ ⟨t, j⟩ he
    have hrt : r = t := Subtype.ext <| calc
      r.val = canonicalCycle f (f^[i.val] r.val) :=
        (hrep r).1.symm.trans (canonicalCycle_iterate f r.val i.val).symm
      _ = canonicalCycle f (f^[j.val] t.val) := congrArg (canonicalCycle f) he
      _ = t.val := (canonicalCycle_iterate f t.val j.val).trans (hrep t).1
    subst t
    have hper : minimalPeriod f r.val = cycleLength f r.val :=
      minimalPeriod_at_periodic_iterate (t := 0) f r.val (hrep r).2
    have hij : i = j := Fin.ext <| (iterate_eq_iterate_iff_of_lt_minimalPeriod
      (hper.symm ▸ i.isLt) (hper.symm ▸ j.isLt)).mp he
    cases hij
    rfl
  rw [← Finset.sum_attach]
  simpa [Fintype.card_sigma, reps] using Fintype.card_le_of_injective point hinj

/-- The canonical cycle and the block containing its target phase are enough to identify a
marker. There are at most `H.card + Fintype.card α / B` markers for all trajectories from `H`.
All block indices fit in the original state-space bound. -/
theorem exists_cycleBlocks (H : Finset α) (B : ℕ) (hB : 0 < B) :
    ∃ rows : Finset (α × ℕ), rows.card ≤ H.card + Fintype.card α / B ∧
      (∀ row ∈ rows, row.2 < Fintype.card α) ∧
      ∀ h ∈ H, ∀ p < cycleLength f h, (canonicalCycle f h, p / B) ∈ rows := by
  classical
  let reps := H.image (canonicalCycle f)
  let blocks (r : α) := (cycleLength f r - 1) / B + 1
  let entries (r : α) := (Finset.range (blocks r)).image fun j => (r, j)
  let rows := reps.biUnion entries
  have hsum := sum_cycleLength_image_le f H
  have hcomplete : ∑ r ∈ reps, (cycleLength f r - 1) / B ≤ Fintype.card α / B := by
    apply (Nat.le_div_iff_mul_le hB).mpr
    rw [Finset.sum_mul]
    exact (Finset.sum_le_sum fun r _ =>
      (Nat.div_mul_le_self (cycleLength f r - 1) B).trans (Nat.sub_le _ _)).trans hsum
  have hcount : rows.card ≤ ∑ r ∈ reps, blocks r := by
    apply (Finset.card_biUnion_le).trans
    apply Finset.sum_le_sum
    intro r _
    exact (Finset.card_image_le.trans_eq (Finset.card_range _))
  refine ⟨rows, ?_, ?_, ?_⟩
  · have := Finset.card_image_le (f := canonicalCycle f) (s := H)
    simp only [blocks, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hcount
    change reps.card ≤ H.card at this
    lia
  · intro row hy
    obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    have hj' := Finset.mem_range.mp hj
    have hlength := transientDepth_add_cycleLength_le_card f r
    have hpos := cycleLength_pos f r
    have hdiv := Nat.div_le_self (cycleLength f r - 1) B
    dsimp only [blocks, Prod.snd] at hj' ⊢
    lia
  · intro h hh p hp
    apply Finset.mem_biUnion.mpr
    refine ⟨canonicalCycle f h, Finset.mem_image_of_mem _ hh, ?_⟩
    refine Finset.mem_image.mpr ⟨p / B, ?_, rfl⟩
    obtain ⟨j, hj⟩ := canonicalCycle_reachable f h
    have he : cycleLength f (canonicalCycle f h) = cycleLength f h := by
      rw [← hj, cycleLength_iterate]
    apply Finset.mem_range.mpr
    change p / B < (cycleLength f (canonicalCycle f h) - 1) / B + 1
    rw [he]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by lia))

end Cslib.FunctionalGraph
