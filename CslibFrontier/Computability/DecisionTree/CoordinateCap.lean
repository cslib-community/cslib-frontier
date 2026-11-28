/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.DecisionTree.Cost

/-!
# Per-coordinate query caps

For a tree on a product of query sets, `Capped t c` bounds the number of queries to each
coordinate on every structural root-to-leaf path. It uses `DecisionTree.weightedDepth` with
indicator costs. Repeated queries count again, and unreachable structural paths still count.
No second notion of tree depth is introduced.

## Main definitions

* `Cslib.DecisionTree.Capped`: a separate structural query cap for each coordinate.

## Main results

* `Cslib.DecisionTree.capped_node_iff`: a node spends one unit from its queried coordinate.
* `Cslib.DecisionTree.capped_of_depth_le`: a total structural depth bound implies separate caps.
-/

public section

namespace Cslib.DecisionTree

variable {J ι β : Type*} [DecidableEq J]

/-- Every structural path queries coordinate `j` at most `c j` times. -/
@[expose] def Capped (t : DecisionTree (J × ι) β) (c : J → ℕ) : Prop :=
  ∀ j, t.weightedDepth (fun p => if p.1 = j then 1 else 0) ≤ c j

@[simp] theorem capped_leaf (b : β) (c : J → ℕ) :
    (leaf b : DecisionTree (J × ι) β).Capped c :=
  fun _ => Nat.zero_le _

/-- A node spends one unit from its queried coordinate on both branches. -/
theorem capped_node_iff {j : J} {i : ι} {left right : DecisionTree (J × ι) β}
    {c : J → ℕ} :
    (node (j, i) left right).Capped c ↔
      0 < c j ∧ left.Capped (Function.update c j (c j - 1)) ∧
        right.Capped (Function.update c j (c j - 1)) := by
  constructor
  · intro ht
    refine ⟨by
        have := ht j
        simp only [weightedDepth_node, ↓reduceIte] at this; omega,
      fun k => ?_, fun k => ?_⟩ <;>
    · have hk := ht k
      rcases eq_or_ne k j with rfl | hkj
      · simp only [weightedDepth_node, ↓reduceIte, Function.update_self] at hk ⊢; omega
      · simp only [Function.update_of_ne hkj, weightedDepth_node, ite_eq_right hkj.symm,
          Nat.add_zero] at hk ⊢
        omega
  · rintro ⟨h0, hl, hr⟩ k
    have hlk := hl k
    have hrk := hr k
    rcases eq_or_ne k j with rfl | hkj
    · simp only [Function.update_self, weightedDepth_node, ↓reduceIte] at hlk hrk ⊢; omega
    · simp only [Function.update_of_ne hkj, weightedDepth_node, ite_eq_right hkj.symm,
        Nat.add_zero] at hlk hrk ⊢
      exact max_le hlk hrk

/-- Increasing any coordinate's cap preserves the cap condition. -/
theorem capped_mono {t : DecisionTree (J × ι) β} {c d : J → ℕ}
    (ht : t.Capped c) (hcd : ∀ j, c j ≤ d j) : t.Capped d :=
  fun j => (ht j).trans (hcd j)

/-- A bound on total structural depth gives the same bound for every coordinate. -/
theorem capped_of_depth_le {t : DecisionTree (J × ι) β} {n : ℕ} {c : J → ℕ}
    (ht : t.depth ≤ n) (hc : ∀ j, n ≤ c j) : t.Capped c := fun j =>
  calc
    t.weightedDepth (fun p => if p.1 = j then 1 else 0) ≤ t.depth * 1 :=
      t.weightedDepth_le_depth_mul fun _ => by split_ifs <;> omega
    _ = t.depth := Nat.mul_one _
    _ ≤ c j := ht.trans (hc j)

/-- Separate structural caps also bound the queries executed on each actual input. -/
theorem weightedCost_le_of_capped {t : DecisionTree (J × ι) β} {c : J → ℕ}
    (ht : t.Capped c) (j : J) (x : J × ι → Bool) :
    t.weightedCost (fun p => if p.1 = j then 1 else 0) x ≤ c j :=
  (t.weightedCost_le_weightedDepth _ x).trans (ht j)

end Cslib.DecisionTree
