/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Knapsack.PolyTime
public import CslibFrontier.Computability.Complexity.Classes.ApproximationSchemes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.Sublist
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Knapsack in FPTAS

The optimization problem chooses a subsequence of the items within the capacity and
maximizes its total value. The existing knapsack approximation algorithm and its
unary-accuracy time bound provide the solver for the generic FPTAS predicate
[Williamson and Shmoys][WilliamsonShmoys2011], Theorem 3.5, §3.1, printed p. 68
of the authors' electronic web edition. We also allow zero weights, values and capacity.
The solver filters out items exceeding capacity. Selecting a subsequence preserves distinct
positions for items with identical weights and values.
-/

public section

namespace Cslib.Algorithms.Lean.Knapsack

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime
open scoped List

/-- The 0–1 knapsack maximization problem, with a list of selected items as a solution. -/
@[expose] def optimizationProblem : NPOptimizationProblem encInstance encItems where
  Feasible x s := s <+ x.1 ∧ (s.map Prod.fst).sum ≤ x.2
  exists_feasible x := ⟨[], List.nil_sublist _, Nat.zero_le x.2⟩
  feasible_mem_P := by
    let check : (List (ℕ × ℕ) × ℕ) × List (ℕ × ℕ) → Bool :=
      fun p => p.2.isSublist p.1.1 && decide ((p.2.map Prod.fst).sum ≤ p.1.2)
    refine mem_P.mpr ⟨check, ?_, fun p => ?_⟩
    · have hsub := (isSublist (encPair encNat encNat)).comp
        (show ComputableInPolyTime
          (fun p : (List (ℕ × ℕ) × ℕ) × List (ℕ × ℕ) => (p.2, p.1.1))
          (encPair encInstance encItems) (encPair encItems encItems) from by fun_prop)
      have hsum := binary_sum
      have hweight := hsum.comp ((map (fst encNat encNat)).comp (snd encInstance encItems))
      have hcapacity := (snd encItems encNat).comp (fst encInstance encItems)
      exact bool_and' hsub (binary_le' hweight hcapacity)
    · simp [check]
  solution_length_bound := ⟨Polynomial.X, fun x s hs => by
    rw [Polynomial.eval_X]
    exact (length_encList_sublist _ hs.1).trans (length_le_encPair_left _ _ x)⟩
  value p := (p.2.map Prod.snd).sum
  computableInPolyTime_value := by
    have hsum := binary_sum
    exact hsum.comp ((map (snd encNat encNat)).comp (snd encInstance encItems))
  goal := .maximize

/-- The certified knapsack solver is an FPTAS for the optimization problem. -/
theorem optimizationProblem_fptas : optimizationProblem.FPTAS := by
  refine ⟨_, computableInPolyTime_fptas, fun k _ x => ?_⟩
  exact ⟨⟨fptas_sublist k x, sum_map_fst_fptas_le k x⟩,
    fun other h => sub_one_mul_value_le_fptas k h.1 h.2⟩

end Cslib.Algorithms.Lean.Knapsack
