/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.DenseCase.Progress
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.Conglomerates
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.HeapPrimMarks
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.RecursiveReduction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Four dense passes suffice on the quotient of a recursive round

This combines the size of the actual soft-heap conglomerates with the progress of the
bounded-frontier dense passes. The nominal density uses the count of active edges before
sparsification, as in [PettieRamachandran2002], §§2.3 and 5.
-/

public section

namespace Cslib.Multigraph.PettieRamachandran

open Finset PrimPartition

variable {E V W : Type} [DecidableEq V] [LinearOrder E] [LinearOrder W]

omit [LinearOrder E] [DecidableEq V] in
private theorem support_card_le (ends : E → Sym2 V) (S : Finset E) :
    (support ends S).card ≤ 2 * S.card := by
  classical
  have sub : support ends S ⊆ S.biUnion fun e => (ends e).toFinset := by
    intro v hv
    obtain ⟨e, he, _, inc⟩ := mem_support.mp hv
    exact mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr inc⟩
  calc
    _ ≤ _ := (card_le_card sub).trans card_biUnion_le
    _ ≤ ∑ _e ∈ S, 2 := by
      apply sum_le_sum
      intro e _
      rw [Sym2.card_toFinset]
      split <;> decide
    _ = 2 * S.card := by simp [Nat.mul_comm]

/-- Every quotient submitted to the dense subroutine by one soft-heap MSF round has
no active vertices after four of its Fredman–Tarjan passes. -/
theorem round_dense_four (ends : E → Sym2 V) (S : Finset E) (w : E → W) :
    let A := nonloops ends S
    let p : Grower V E W w := HeapPrim.grower 2 w
    let G := terminalGraph w ends A (roundParts p ends S)
    let final := DenseCase.afterPasses A.card w G.1 G.2 4
    support final.1 final.2 = ∅ := by
  let A := nonloops ends S
  let X := support ends A
  let p : Grower V E W w := HeapPrim.grower 2 w
  let parts := roundParts p ends S
  let G := terminalGraph w ends A parts
  have complete : p.Complete :=
    fun es edges extra dead seed _ => HeapPrim.grower_complete w 2 es edges extra dead seed
  have size := terminalSupport_mul_le p complete X.card.log2.log2.log2 ends A
  exact DenseCase.four_passes_suffice X.card A.card G.1 G.2 w
    (card_le_card (terminalGraph_subset w ends A parts)) (support_card_le ends A)
    (by rw [Nat.mul_comm]; exact size)

end Cslib.Multigraph.PettieRamachandran
