/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.RecursiveComparisons
public import CslibFrontier.Algorithms.PointerMachine.BindMSF
import all CslibFrontier.Algorithms.Lean.MinimumSpanningForest.RecursiveComparisons
import all CslibFrontier.Algorithms.Lean.MinimumSpanningForest.PartitionComparisons

/-!
# Pointer instructions for the local MSF calls over all rounds

Each call on an aligned input binds the edge records, traverses the stored comparison tree,
and flags its output edges. We sum the instruction count of this subroutine over the actual
local graphs of the recursive algorithm. Each compact input edge and output label can be
charged to a round edge, and each invocation to the vertex that seeded its search. Building
the shared tables and arranging the input records into aligned lists are separate operations.
-/

public section

namespace Cslib.Multigraph.PettieRamachandran

open Finset
open Cslib.PointerMachine.ComparisonTree.Binding

variable {V E W : Type} [LinearOrder V] [LinearOrder E] [LinearOrder W]

private theorem partition_length (w : E → W) (g : PrimPartition.Grower V E W w)
    (k : ℕ) (ends : E → Sym2 V) (S : Finset E) (rep : V → V) (dead : Finset V) (xs : List V) :
    (PrimPartition.partition g k ends S rep dead xs).length ≤ xs.length := by
  induction xs generalizing ends S rep dead with
  | nil => exact Nat.le_refl _
  | cons v xs ih =>
    rw [PrimPartition.partition]
    split
    · exact (ih ..).trans (Nat.le_succ _)
    · exact Nat.succ_le_succ (ih ..)

omit [LinearOrder V] in
private theorem localJobs_length (w : E → W) (ends : E → Sym2 V) (S : Finset E)
    (ps : List (PartitionPart V E W)) :
    (PrimPartition.localJobs w ends S ps).length = ps.length := by
  induction ps generalizing ends S with
  | nil => rfl
  | cons p ps ih => exact congrArg Nat.succ (ih ..)

/-- Sum of the binder, traversal and output instructions for the local MSF programs of a
single round, given the reusable trees and aligned edge records. -/
noncomputable def roundLocalInstructions (w : E → W) (g : PrimPartition.Grower V E W w)
    (v m : ℕ) (ends : E → Sym2 V) (S : Finset E) : ℕ :=
  let jobs := PrimPartition.localJobs w ends (nonloops ends S) (roundParts g ends S)
  (jobs.map fun j =>
    let queries := (MSFPrecompute.cachedMSFOn (MSFPrecompute.fillBank v m) j.1 j.2).countQueries
      (Cslib.Query.LEQuery.keyOracle w)
    instructionCount j.2.card queries (msf j.1 w j.2).card).sum

omit [LinearOrder V] [LinearOrder E] in
private theorem sum_cost (w : E → W) (queries : ((E → Sym2 V) × Finset E) → ℕ)
    (jobs : List ((E → Sym2 V) × Finset E)) :
    (jobs.map (fun j => instructionCount j.2.card (queries j) (msf j.1 w j.2).card)).sum ≤
      13 * (jobs.map fun j => j.2.card).sum + 8 * (jobs.map queries).sum + 9 * jobs.length := by
  induction jobs with
  | nil => simp
  | cons j js ih =>
    have sub : (msf j.1 w j.2).card ≤ j.2.card := card_le_card (msf_subset w)
    simp only [List.map_cons, List.sum_cons, List.length_cons, instructionCount] at ih ⊢
    omega

private theorem roundLocalInstructions_le (w : E → W) (g : PrimPartition.Grower V E W w)
    (hw : Function.Injective w) (v m : ℕ) (ends : E → Sym2 V) (S : Finset E) :
    roundLocalInstructions w g v m ends S ≤
      13 * S.card + 8 * OptimalTree.worstCase S.card (support ends S).card +
      9 * (support ends S).card := by
  let A := nonloops ends S
  let ps := roundParts g ends S
  let jobs := PrimPartition.localJobs w ends A ps
  let queries := fun (j : (E → Sym2 V) × Finset E) =>
    (MSFPrecompute.cachedMSFOn (MSFPrecompute.fillBank v m) j.1 j.2).countQueries
      (Cslib.Query.LEQuery.keyOracle w)
  have valid : PrimPartition.Valid w ends A ps := PrimPartition.valid_partition ..
  have edges : (jobs.map fun j => j.2.card).sum ≤ S.card :=
    (PrimPartition.sum_localJobs_edges_le valid hw).trans
      (card_le_card (fun _ he => (mem_nonloops.1 he).1))
  have count : jobs.length ≤ (support ends S).card := by
    rw [localJobs_length]
    have h := partition_length w g (support ends A).card.log2.log2.log2 ends A id ∅
      (support ends A).toList
    simpa only [ps, roundParts, Finset.length_toList, A, support_nonloops] using h
  have queryBound : (jobs.map queries).sum ≤ OptimalTree.worstCase S.card (support ends S).card :=
    roundLocalComparisons_le g hw v m ends S
  exact (sum_cost w queries jobs).trans (by omega)

private theorem inputs_localInstructions_le (w : E → W) (alg : Solvers V E W w)
    (hw : Function.Injective w) (v m : ℕ) (ends : E → Sym2 V) (S : Finset E) :
    let g := PrimPartition.HeapPrim.grower 2 w
    ((roundInputs g alg hw ends S).map fun j => roundLocalInstructions w g v m j.1 j.2).sum ≤
      26 * S.card + 16 * OptimalTree.worstCase S.card (support ends S).card +
      18 * (support ends S).card := by
  dsimp only
  rw [roundInputs]
  split
  next h =>
    let g : PrimPartition.Grower V E W w := PrimPartition.HeapPrim.grower 2 w
    let r := round g alg ends S
    have here := roundLocalInstructions_le w g hw v m ends S
    have tail := inputs_localInstructions_le w alg hw v m r.ends r.remaining
    change ((roundInputs g alg hw r.ends r.remaining).map
      (fun j => roundLocalInstructions w g v m j.1 j.2)).sum ≤
      26 * r.remaining.card + 16 * OptimalTree.worstCase r.remaining.card
      (support r.ends r.remaining).card + 18 * (support r.ends r.remaining).card at tail
    have e : 2 * r.remaining.card ≤ S.card := heapRound_half alg hw ends S
    have n : 4 * (support r.ends r.remaining).card ≤ (support ends S).card :=
      round_support_le g alg ends S
    have q : 2 * OptimalTree.worstCase r.remaining.card (support r.ends r.remaining).card ≤
        OptimalTree.worstCase S.card (support ends S).card :=
      (OptimalTree.twice_worstCase_le _ _).trans (OptimalTree.worstCase_mono e (by omega))
    change roundLocalInstructions w g v m ends S + ((roundInputs g alg hw r.ends r.remaining).map
      (fun j => roundLocalInstructions w g v m j.1 j.2)).sum ≤ _
    omega
  next => exact Nat.zero_le _
termination_by (nonloops ends S).card
decreasing_by exact round_card_lt _ alg hw _ _ (by assumption)

/-- For all the aligned local MSF calls of the algorithm, binding, tree traversal and output
decoding together cost at most `26 m + 16 T*(m,n) + 18 n` pointer instructions. -/
theorem forestRounds_localInstructions_le (ends : E → Sym2 V) (w : E → W)
    (hw : Function.Injective w) (S : Finset E) :
    let r := (support ends S).card.log2.log2.log2 + 1
    let g := PrimPartition.HeapPrim.grower 2 w
    ((forestRounds ends w hw S).map fun j => roundLocalInstructions w g r (r ^ 2) j.1 j.2).sum ≤
      26 * S.card + 16 * OptimalTree.worstCase S.card (support ends S).card +
      18 * (support ends S).card := by
  apply inputs_localInstructions_le

end Cslib.Multigraph.PettieRamachandran
