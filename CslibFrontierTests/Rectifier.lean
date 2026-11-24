/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Circuit.Boolean.Rectifier
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Rectangular matrix orientation, repeated rows, empty inputs, and a nondivisible block
width for the depth-two rectifier construction. Two further checks concern the graph model
`RectifierCircuit`: the orientation of the bridge to `orDepthComplexity`, and a depth-two
`RectifierCircuit` with fewer edges than any Lupanov `(p, q)`-circuit for the same matrix. -/

set_option linter.privateModule false

open Finset Cslib.Circuits Cslib.Circuits.Boolean.Rectifier
open scoped Matrix

private def repeatedRows : Matrix (Fin 3) (Fin 2) Bool :=
  ![![true, false], ![true, false], ![false, true]]

example (x : Fin 3 → Bool) :
    (rowPatternCircuit repeatedRows).eval interpretation x = ![x 0 || x 1, x 2] := by
  rw [eval_rowPatternCircuit]
  funext j
  fin_cases j <;>
    simp [matrixAction, repeatedRows, Fin.exists_fin_succ]

example :
    (rowPatternCircuit (Matrix.of fun i : Fin 0 => i.elim0 : Matrix (Fin 0) (Fin 3) Bool)).eval
      interpretation Fin.elim0 = fun _ => false := by
  rw [eval_rowPatternCircuit]
  funext j
  simp [matrixAction]

-- Six blocks of width three include one padded column, whose four outgoing wires are omitted.
-- The resulting budget is below both the uniform block bound of 168 and the dense bound of 272.
example (A : Matrix (Fin 16) (Fin 17) Bool) :
    ∃ c : Circuit signature 16 17,
      IsTwoLayer c ∧ c.Computes interpretation (matrixAction A) ∧ c.program.cost id = 164 := by
  obtain ⟨c, hl, hc, hw⟩ := exists_depth_two_blocked_exact A (s := 3) (by decide)
  norm_num [Nat.ceilDiv_eq_add_pred_div] at hw
  exact ⟨c, hl, hc, hw⟩

-- Orientation of the bridge. `repeatedRows` has three input rows and two output columns; in the
-- graph model the same map is the matrix with two output rows and three input columns.
example : orDepthComplexity 2 !![true, true, false; false, false, true] ≤ 7 := by
  have hA : !![true, true, false; false, false, true] = repeatedRowsᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hA]
  refine ((isTwoLayer_rowPatternCircuit repeatedRows).orDepthComplexity_two_le
    (eval_rowPatternCircuit repeatedRows)).trans ?_
  rw [cost_rowPatternCircuit]
  exact_mod_cast (by decide : 3 + 2 * 2 ^ (2 - 1) ≤ 7)

/-- The four edges `a₀ → a₁` and `a₁ → b₀, b₁, b₂` on five poles. The edge between the two
input poles is permitted in a `RectifierCircuit` but not in a rectifier `(2, 3)`-circuit of
[Lupanov1956], section 2°. -/
private def chainedInputs : RectifierCircuit (Fin 3) (Fin 2) (Fin 2 ⊕ Fin 3) where
  edges := insert (Sum.inl 0, Sum.inl 1) (univ.image fun j : Fin 3 => (Sum.inl 1, Sum.inr j))
  inp := Function.Embedding.inl
  out := Function.Embedding.inr
  disjoint_poles := by
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
    nomatch h

-- `orDepthComplexity 2` can be smaller than Lupanov's `B₂`: the all-true matrix with two inputs
-- and three outputs has a depth-two `RectifierCircuit` with four edges, while every
-- `(2, 3)`-circuit implementing it has at least five rectifiers (not proved here).
example : orDepthComplexity 2 (fun (_ : Fin 3) (_ : Fin 2) => true) ≤ 4 := by
  have hedge (j : Fin 3) : ((Sum.inl 1 : Fin 2 ⊕ Fin 3), Sum.inr j) ∈ chainedInputs.edges :=
    mem_insert_of_mem (mem_image_of_mem _ (mem_univ j))
  have hC : chainedInputs.Computes fun _ _ => true := by
    intro j i
    refine iff_of_true rfl ?_
    fin_cases i
    · exact ⟨.cons (mem_insert_self _ _) (.cons (hedge j) (.nil _))⟩
    · exact ⟨.cons (hedge j) (.nil _)⟩
  have hd : chainedInputs.HasDepthLE 2 := by
    refine RectifierCircuit.hasDepthLE_of_layer (Sum.elim (fun i => i.val) fun _ => 2) ?_ ?_
    · intro u v h
      rcases mem_insert.mp h with h | h
      · cases h
        rfl
      · obtain ⟨j, -, h⟩ := mem_image.mp h
        cases h
        rfl
    · rintro (i | j)
      · exact Nat.le_of_lt_succ (i.isLt.trans (by decide))
      · exact le_rfl
  refine (hC.orDepthComplexity_le hd).trans ?_
  exact_mod_cast (card_insert_le _ _).trans
    (Nat.succ_le_succ (card_image_le.trans (Finset.card_fin 3).le))
