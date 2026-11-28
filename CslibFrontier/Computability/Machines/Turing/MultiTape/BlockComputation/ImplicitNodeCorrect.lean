/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitNode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.EncodedTree

/-!
# Implicit node tags agree with the existing Boolean tree

Classification reports the kind of the existing `encodedTree` node reached by the typed path.
The proof reuses the descending-tree lookup theorem, including uniform-height source padding
and rejection of paths beyond the horizon.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ImplicitNode

open Cslib.TreeEval.Ary

/-- Native raw-path classification agrees with the existing encoded tree's node tag. -/
theorem classify_eq_nodeAt {k q s : ℕ} {Q : Type}
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (path : List (Fin (k * 3 + 1))) :
    classify k (σ, q, path.map Fin.val) =
      kind ((encodedTree (MultiTapePTM.ofDeterministic M) w b
        (scheduleOfNat k q σ) e).nodeAt path) := by
  have hall : (path.map Fin.val).all (fun j => decide (j < k * 3 + 1)) = true :=
    List.all_eq_true.mpr fun _ hj =>
      let ⟨p, _, hp⟩ := List.mem_map.mp hj
      hp ▸ decide_eq_true p.isLt
  rw [encodedTree, tree, Descending.nodeAt_tree]
  simp only [classify, ImplicitPath.valid, List.length_map, hall, Bool.and_true,
    decide_eq_true_eq, Descending.lookup]
  rcases lt_trichotomy path.length q with hlt | heq | hgt
  · simp [hlt, hlt.le, hlt.ne, kind]
  · simp [heq, kind]
  · simp [hgt.not_gt, hgt.not_ge, hgt.ne', kind]

end Turing.MultiTapePTM.BlockComputation.ImplicitNode
