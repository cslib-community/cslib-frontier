/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.PartitionComparisons
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.HeapPrimBudget
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.PettieRamachandran

/-!
# Cached local comparisons over the complete recursion

A trace lists the quotient graph and remaining original labels at every round. Folding the
selected Borůvka labels over the trace reconstructs the forest. For the concrete soft heap
the trace halves edge counts and quarters active vertex counts. The sum of the weight
comparisons executed by the small cached programs over all these rounds is at most twice
the global worst-case comparison optimum.
-/

public section

namespace Cslib.Multigraph.PettieRamachandran

open Finset

variable {V E W : Type} [LinearOrder V] [LinearOrder E] [LinearOrder W]
variable {w : E → W}

/-- Actual edge contraction for threshold two of the four-ary soft heap, including on
disconnected inputs. The marked-boundary bound pays for all edges beyond the residual rank. -/
theorem heapRound_half (alg : Solvers V E W w) (hw : Function.Injective w)
    (ends : E → Sym2 V) (S : Finset E) :
    2 * (round (PrimPartition.HeapPrim.grower 2 w) alg ends S).remaining.card ≤ S.card := by
  let g : PrimPartition.Grower V E W w := PrimPartition.HeapPrim.grower 2 w
  have corrupt := round_mark_budget g (4 ^ 2)
    (fun ends S extra dead seed h =>
      PrimPartition.HeapPrim.marks_le_touched w 2 extra ends S dead seed h)
    ends S
  have bound : 4 * (roundMarks g ends S).card ≤ (nonloops ends S).card := by omega
  exact (round_half_of_mark_bound g alg hw ends S bound).trans
    (card_le_card (fun _ he => (mem_nonloops.1 he).1))

/-- Quotient inputs appearing in the recursive reduction, in evaluation order. -/
noncomputable def roundInputs (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E) :
    List ((E → Sym2 V) × Finset E) :=
  if _h : (nonloops ends S).Nonempty then
    let r := round grower alg ends S
    (ends, S) :: roundInputs grower alg hw r.ends r.remaining
  else []
termination_by (nonloops ends S).card
decreasing_by exact round_card_lt grower alg hw ends S (by assumption)

/-- The union of precisely the labels chosen along this trace is the recursive result. -/
theorem roundInputs_selected (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E) :
    ((roundInputs grower alg hw ends S).map (fun j => (round grower alg j.1 j.2).chosen)).foldr
      (· ∪ ·) ∅ = reduceMSF grower alg hw ends S := by
  rw [roundInputs, reduceMSF]
  split
  next h =>
    let r := round grower alg ends S
    exact congrArg (r.chosen ∪ ·) (roundInputs_selected grower alg hw r.ends r.remaining)
  next => rfl
termination_by (nonloops ends S).card
decreasing_by exact round_card_lt grower alg hw ends S (by assumption)

private theorem sum_roundLocal_le (alg : Solvers V E W w) (hw : Function.Injective w)
    (maxV maxE : ℕ) (ends : E → Sym2 V) (S : Finset E) :
    let g : PrimPartition.Grower V E W w := PrimPartition.HeapPrim.grower 2 w
    ((roundInputs g alg hw ends S).map (fun j => roundLocalComparisons g maxV maxE j.1 j.2)).sum ≤
      2 * OptimalTree.worstCase S.card (support ends S).card := by
  dsimp only
  rw [roundInputs]
  split
  next h =>
    let g : PrimPartition.Grower V E W w := PrimPartition.HeapPrim.grower 2 w
    let r := round g alg ends S
    have child := sum_roundLocal_le alg hw maxV maxE r.ends r.remaining
    have current := roundLocalComparisons_le g hw maxV maxE ends S
    have nextEdges : 2 * r.remaining.card ≤ S.card := heapRound_half alg hw ends S
    have nextVertices : 4 * (support r.ends r.remaining).card ≤ (support ends S).card :=
      round_support_le g alg ends S
    have half : 2 * OptimalTree.worstCase r.remaining.card (support r.ends r.remaining).card ≤
        OptimalTree.worstCase S.card (support ends S).card :=
      (OptimalTree.twice_worstCase_le _ _).trans (OptimalTree.worstCase_mono nextEdges (by omega))
    exact (Nat.add_le_add current (child.trans half)).trans_eq (two_mul _).symm
  next => exact Nat.zero_le _
termination_by (nonloops ends S).card
decreasing_by exact round_card_lt _ alg hw ends S (by assumption)

/-- All quotient inputs of the graph-level algorithm, with its original precomputed bank. -/
noncomputable def forestRounds (ends : E → Sym2 V) (w : E → W) (hw : Function.Injective w)
    (S : Finset E) : List ((E → Sym2 V) × Finset E) :=
  let r := (support ends S).card.log2.log2.log2 + 1
  roundInputs (PrimPartition.HeapPrim.grower 2 w)
    (bankSolvers w hw (MSFPrecompute.fillBank r (r ^ 2)) rfl) hw ends S

/-- Over all recursive rounds, all fixed-topology cached local programs together use at most
twice the optimal worst-case comparison budget for the input sizes. The sums count queries
at the actual weights, with the original bank capacity fixed throughout recursion. -/
theorem forestRounds_localComparisons_le (ends : E → Sym2 V) (w : E → W) (hw : Function.Injective w)
    (S : Finset E) :
    let r := (support ends S).card.log2.log2.log2 + 1
    ((forestRounds ends w hw S).map (fun j =>
      roundLocalComparisons (PrimPartition.HeapPrim.grower 2 w) r (r ^ 2) j.1 j.2)).sum ≤
      2 * OptimalTree.worstCase S.card (support ends S).card := by
  apply sum_roundLocal_le

end Cslib.Multigraph.PettieRamachandran
