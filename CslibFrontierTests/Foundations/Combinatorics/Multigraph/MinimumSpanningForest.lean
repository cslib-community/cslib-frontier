/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.Multigraph.MinimumSpanningForest
import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.KeyOracle
import Mathlib.Tactic.FinCases

/-!
# Tests: minimum spanning forests of multigraphs

A worked instance on three vertices with a self-loop and a pair of parallel edges, computed from
the cut and cycle properties; the empty edge set; and the comparison oracle of a weight function.
-/

namespace CslibFrontierTests.Foundations.Multigraph.MinimumSpanningForest

open Cslib Multigraph Finset

/-- Edge `0` is a self-loop at `0`; edges `1` and `2` are parallel edges joining `0` and `1`;
edge `3` joins `1` and `2`, and edge `4` joins `0` and `2`. The weight of edge `i` is `i`, so the
self-loop is the lightest edge. -/
private def multi : Fin 5 → Sym2 (Fin 3)
  | 0 => s(0, 0)
  | 1 => s(0, 1)
  | 2 => s(0, 1)
  | 3 => s(1, 2)
  | 4 => s(0, 2)

private def weight : Fin 5 → ℕ := Fin.val

private theorem weight_injective : Function.Injective weight := Fin.val_injective

/-- The lightest edge leaving `{0}` is edge `1`: the self-loop at `0` does not leave it. -/
private theorem one_mem : (1 : Fin 5) ∈ msf multi weight univ := by
  refine mem_msf_of_mem_edgeCut (P := ((({0} : Finset (Fin 3))) : Set (Fin 3))) weight
    (mem_univ _) ?_ ?_ <;> rw [← coe_edgeCut_eq_toGraph_edgeCut]
  · decide
  · intro f _ hf
    revert f
    decide

/-- The lightest edge leaving `{2}` is edge `3`. -/
private theorem three_mem : (3 : Fin 5) ∈ msf multi weight univ := by
  refine mem_msf_of_mem_edgeCut (P := ((({2} : Finset (Fin 3))) : Set (Fin 3))) weight
    (mem_univ _) ?_ ?_ <;> rw [← coe_edgeCut_eq_toGraph_edgeCut]
  · decide
  · intro f _ hf
    revert f
    decide

/-- The minimum spanning forest drops the self-loop, the heavier parallel edge, and the heaviest
edge of the triangle. -/
example : msf multi weight univ = {1, 3} := by
  have h01 : Joins multi {f | f ∈ (univ : Finset (Fin 5)) ∧ weight f < weight 2} 0 1 := by
    refine Joins.of_mem (e := 1) ?_ rfl
    simp [weight]
  have h02 : Joins multi {f | f ∈ (univ : Finset (Fin 5)) ∧ weight f < weight 4} 0 2 := by
    refine (Joins.of_mem (ends := multi) (e := 1) ?_ rfl).trans
      (Joins.of_mem (e := 3) ?_ rfl) <;> simp [weight]
  ext e
  fin_cases e
  · simpa using notMem_msf_of_isDiag (S := univ) weight (e := (0 : Fin 5)) (by decide)
  · simpa using one_mem
  · simpa using notMem_msf_of_joins (ends := multi) (S := univ) (e := 2) weight
      (by rintro f ⟨hf, -⟩; exact hf) (by rintro f ⟨-, hf⟩; exact hf) rfl h01
  · simpa using three_mem
  · simpa using notMem_msf_of_joins (ends := multi) (S := univ) (e := 4) weight
      (by rintro f ⟨hf, -⟩; exact hf) (by rintro f ⟨-, hf⟩; exact hf) rfl h02

/-- `msf` of the instance is a spanning forest, with at most `3 - 1` edges. -/
example : IsSpanningForest multi univ (msf multi weight univ) :=
  isSpanningForest_msf weight weight_injective

example : #(msf multi weight univ) ≤ 2 :=
  (card_msf_le (X := univ) weight weight_injective fun _ _ _ _ => mem_univ _).trans (by simp)

/-- The parallel edges `1` and `2` join `0` and `1`, and so does either one alone; the self-loop
joins nothing new. -/
example : Joins multi {2} 0 1 := Joins.of_mem rfl rfl

example : ¬Joins multi {0} 0 1 := by
  rw [joins_iff_reachable]
  rintro ⟨p⟩
  cases p with
  | cons hadj _ =>
    obtain ⟨hne, ⟨e, he⟩, hends⟩ := toSimpleGraph_adj.1 hadj
    obtain rfl := Set.mem_singleton_iff.1 he
    exact hne (Sym2.congr_right.1 (show s(0, 0) = s((0 : Fin 3), _) from hends))

/-- The empty set of edges has an empty minimum spanning forest. -/
example : msf multi weight ∅ = ∅ :=
  subset_empty.1 (msf_subset weight)

/-- The comparison oracle of the weights answers `1 ≤ 3` with `true`. -/
example : Query.LEQuery.keyOracle weight (.le 1 3) = true := by
  simp [weight]

end CslibFrontierTests.Foundations.Multigraph.MinimumSpanningForest
