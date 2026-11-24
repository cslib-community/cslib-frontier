/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Ties
import Mathlib.Tactic.FinCases

/-!
# Tests: minimum spanning forests with a linear number of comparisons

Algorithm 2 (`Cslib.Query.linearMsf`) on a multigraph with a self-loop, a pair of parallel edges, a
triangle and a second component, with concrete distinct weights; and Theorem 4.1
(`Cslib.Query.exists_msf_program_countQueries_le`) instantiated on it; and the tie-breaking
variant `Cslib.Query.linearMsfTies` on the same multigraph with all weights equal.
-/

namespace CslibFrontierTests.Algorithms.Query.MinimumSpanningForest.Linear

open Cslib Query Multigraph Finset

/-- Edge `0` is a self-loop at `0`; edges `1` and `2` are parallel edges joining `0` and `1`;
edge `3` joins `1` and `2`, and edge `4` joins `0` and `2`; edge `5` joins `3` and `4`, a second
component. The weight of edge `i` is `i`, so the self-loop is the lightest edge. -/
private def multi : Fin 6 → Sym2 (Fin 5)
  | 0 => s(0, 0)
  | 1 => s(0, 1)
  | 2 => s(0, 1)
  | 3 => s(1, 2)
  | 4 => s(0, 2)
  | 5 => s(3, 4)

private def weight : Fin 6 → ℕ := Fin.val

private theorem weight_injective : Function.Injective weight := Fin.val_injective

/-- The lightest edge leaving the vertex set `P` is in the minimum spanning forest. -/
private theorem mem_msf_of_cut (P : Finset (Fin 5)) (e : Fin 6)
    (hcut : e ∈ edgeCut multi P) (hmin : ∀ f ∈ edgeCut multi P, weight e ≤ weight f) :
    e ∈ msf multi weight univ := by
  refine mem_msf_of_mem_edgeCut (P := (P : Set (Fin 5))) weight (mem_univ _) ?_ ?_ <;>
    rw [← coe_edgeCut_eq_toGraph_edgeCut]
  · exact hcut
  · exact fun f _ hf => hmin f hf

/-- The minimum spanning forest drops the self-loop, the heavier parallel edge and the heaviest
edge of the triangle, and keeps the edge of the second component. -/
private theorem msf_multi : msf multi weight univ = {1, 3, 5} := by
  have h01 : Joins multi {f | f ∈ (univ : Finset (Fin 6)) ∧ weight f < weight 2} 0 1 := by
    refine Joins.of_mem (e := 1) ?_ rfl
    simp [weight]
  have h02 : Joins multi {f | f ∈ (univ : Finset (Fin 6)) ∧ weight f < weight 4} 0 2 := by
    refine (Joins.of_mem (ends := multi) (e := 1) ?_ rfl).trans
      (Joins.of_mem (e := 3) ?_ rfl) <;> simp [weight]
  ext e
  fin_cases e
  · simpa using notMem_msf_of_isDiag (S := univ) weight (e := (0 : Fin 6)) (by decide)
  · simpa using mem_msf_of_cut {0} 1 (by decide) (by decide)
  · simpa using notMem_msf_of_joins (ends := multi) (S := univ) (e := 2) weight
      (by rintro f ⟨hf, -⟩; exact hf) (by rintro f ⟨-, hf⟩; exact hf) rfl h01
  · simpa using mem_msf_of_cut {2} 3 (by decide) (by decide)
  · simpa using notMem_msf_of_joins (ends := multi) (S := univ) (e := 4) weight
      (by rintro f ⟨hf, -⟩; exact hf) (by rintro f ⟨-, hf⟩; exact hf) rfl h02
  · simpa using mem_msf_of_cut {3} 5 (by decide) (by decide)

/-- Algorithm 2, run against the comparison oracle of the weights, returns the minimum spanning
forest `{1, 3, 5}`. -/
example : (linearMsf linearMsfSteps multi univ).eval (LEQuery.keyOracle weight) = {1, 3, 5} := by
  rw [eval_linearMsf _ weight_injective, msf_multi]

/-- Correctness does not depend on the number of Borůvka steps: with none, the certificate
procedure does all the work. -/
example : (linearMsf 0 multi univ).eval (LEQuery.keyOracle weight) = {1, 3, 5} := by
  rw [eval_linearMsf _ weight_injective, msf_multi]

/-- Borůvka's algorithm run to completion, the fallback exact call, returns the same forest. -/
example : (boruvkaMsf multi univ).eval (LEQuery.keyOracle weight) = {1, 3, 5} := by
  rw [eval_boruvkaMsf _ _ weight_injective, msf_multi]

/-- **Theorem 4.1 on the instance**: some comparison program computes the minimum spanning forest
of the multigraph for every assignment of distinct weights, with at most `6 C` comparisons; for
the weights above it returns `{1, 3, 5}`. -/
example : ∃ C : ℕ, ∃ p : FreeM (LEQuery (Fin 6)) (Finset (Fin 6)),
    p.eval (LEQuery.keyOracle weight) = {1, 3, 5} ∧
      p.countQueries (LEQuery.keyOracle weight) ≤ C * 6 := by
  obtain ⟨C, hC⟩ := exists_msf_program_countQueries_le
  obtain ⟨p, hp⟩ := hC multi univ
  obtain ⟨heval, hcount⟩ := hp weight weight_injective
  exact ⟨C, p, heval.trans msf_multi, by simpa using hcount⟩

/-- The output is a spanning forest of least total weight. -/
example : IsSpanningForest multi univ
    ((linearMsf linearMsfSteps multi univ).eval (LEQuery.keyOracle weight)) :=
  (linearMsf_isSpanningForest_and_sum_le _ weight_injective multi univ).1

/-- On the empty edge set, Algorithm 2 makes no comparison: the Borůvka steps have nothing to
scan, and no edge remains. -/
example : (linearMsf linearMsfSteps multi ∅).countQueries (LEQuery.keyOracle weight) = 0 := by
  obtain ⟨D, hD⟩ := countQueries_linearMsf_le
  have := hD multi ∅ weight weight_injective
  simp only [card_empty, CharP.cast_eq_zero, mul_zero] at this
  exact_mod_cast le_antisymm this (Nat.cast_nonneg _)

/-! ### Tied weights -/

/-- All weights equal: ties are broken by edge index. -/
private def flat : Fin 6 → ℕ := fun _ => 0

/-- The tie-broken weights `e ↦ (0, e)` order the edges by index. -/
private def flatKey : Fin 6 → Lex (ℕ × Fin 6) := fun e => toLex (flat e, e)

private theorem flatKey_injective : Function.Injective flatKey :=
  fun _ _ h => (Prod.ext_iff.1 (toLex.injective h)).2

/-- With all weights equal, the minimum spanning forest for the tie-broken weights keeps the
lowest-indexed edge of each cycle. -/
private theorem msf_flat : msf multi flatKey univ = {1, 3, 5} := by
  have cut : ∀ (P : Finset (Fin 5)) (e : Fin 6), e ∈ edgeCut multi P →
      (∀ f ∈ edgeCut multi P, flatKey e ≤ flatKey f) → e ∈ msf multi flatKey univ :=
    fun P e hcut hmin => by
      refine mem_msf_of_mem_edgeCut (P := (P : Set (Fin 5))) flatKey (mem_univ _) ?_ ?_ <;>
        rw [← coe_edgeCut_eq_toGraph_edgeCut]
      · exact hcut
      · exact fun f _ hf => hmin f hf
  have h01 : Joins multi {f | f ∈ (univ : Finset (Fin 6)) ∧ flatKey f < flatKey 2} 0 1 := by
    refine Joins.of_mem (e := 1) ?_ rfl
    exact ⟨mem_univ _, by decide⟩
  have h02 : Joins multi {f | f ∈ (univ : Finset (Fin 6)) ∧ flatKey f < flatKey 4} 0 2 := by
    refine (Joins.of_mem (ends := multi) (e := 1) ?_ rfl).trans (Joins.of_mem (e := 3) ?_ rfl)
    · exact ⟨mem_univ _, by decide⟩
    · exact ⟨mem_univ _, by decide⟩
  ext e
  fin_cases e
  · simpa using notMem_msf_of_isDiag (S := univ) flatKey (e := (0 : Fin 6)) (by decide)
  · simpa using cut {0} 1 (by decide) (by decide)
  · simpa using notMem_msf_of_joins (ends := multi) (S := univ) (e := 2) flatKey
      (by rintro f ⟨hf, -⟩; exact hf) (by rintro f ⟨-, hf⟩; exact hf) rfl h01
  · simpa using cut {2} 3 (by decide) (by decide)
  · simpa using notMem_msf_of_joins (ends := multi) (S := univ) (e := 4) flatKey
      (by rintro f ⟨hf, -⟩; exact hf) (by rintro f ⟨-, hf⟩; exact hf) rfl h02
  · simpa using cut {3} 5 (by decide) (by decide)

/-- With all weights equal, `linearMsfTies` keeps one of the two parallel edges and drops the
self-loop and an edge of the triangle: the minimum spanning forest for the tie-broken weights. -/
example : (linearMsfTies multi univ).eval (LEQuery.keyOracle flat) = {1, 3, 5} := by
  rw [eval_linearMsfTies]
  exact msf_flat

end CslibFrontierTests.Algorithms.Query.MinimumSpanningForest.Linear
