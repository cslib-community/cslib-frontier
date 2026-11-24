/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.HeapPrimInsertions
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.HeapPrimMarks

/-!
# Mark budget for the Pettie–Ramachandran partition

The concrete soft heap bounds a single search's marked boundary by its own insertion count.
Charging those insertions to previously live vertices makes each original endpoint pay at
most once over the whole partition. This gives the marked-edge estimate of
[Pettie and Ramachandran, §3.2, Lemma 3.3][PettieRamachandran2002].
-/

public section

namespace Cslib.Multigraph.PrimPartition.HeapPrim

variable {E V W : Type} [DecidableEq V] [LinearOrder E] [LinearOrder W]

/-- Charge a completed live-seed component to labels incident to its live vertices. -/
theorem marks_le_touched (w : E → W) (t extra : ℕ) (ends : E → Sym2 V) (S : Finset E)
    (dead : Finset V) (seed : V) (live : seed ∉ dead) :
    let q := (grower t w).run ends S extra dead seed
    4 ^ t * (q.part.marks ends w S).card ≤ (touched ends S q.vertices dead).card := by
  dsimp only
  rw [Nat.mul_comm]
  exact (marks_le_insertions ends w S t extra dead seed).trans
    (insertions_le_touched (ends := ends) (w := w) (S := S) t extra dead seed live)

/-- The complete live/dead partition with a ranked soft heap has at most
`2 * S.card / 4 ^ t` marked labels for any threshold `t`. -/
theorem partition_marks_le (w : E → W) (t extra : ℕ) (ends : E → Sym2 V)
    (S : Finset E) (vertices : List V) :
    4 ^ t * (collect w ends S (partition (grower t w) extra ends S id ∅ vertices)).marked.card ≤
      2 * S.card :=
  marks_le_twice_edges (grower t w) _ extra (marks_le_touched w t extra) ends S vertices

end Cslib.Multigraph.PrimPartition.HeapPrim
