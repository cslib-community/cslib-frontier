/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Pieces.Program
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Tests of the heavy nodes and the pieces of a tree by stages, as a client that sees only the
public statements. The fixture is a tree on five nodes: the root `4` at the stage `2`, its
children `2` and `3`, and the children `0` and `1` of `2`. For the weights `g = 1` at `0` and
`u = 1` at `3`, with `M = Y = 1` and `k = 3`, the node `3` is heavy and `2` is light, so the
pieces are `{0, 1, 2}`, `{3}` and `{4}`. The program of the pieces is tested on this tree for all
inputs, under the hypotheses on the program that computes its parents and weights. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationPieces

open Finset Cslib Cslib.Circuits Cslib.Circuits.Arithmetic.Separation.Pieces

/-- The tree: `0, 1 ↦ 2 ↦ 4` and `3 ↦ 4`. -/
private def tree : StagedTree (Fin 5) where
  parent := ![2, 2, 4, 4, 4]
  stage := ![0, 0, 1, 1, 2]
  depth := 2
  root := 4
  stage_le := by decide
  stage_eq_depth_iff {p} := by revert p; decide
  stage_parent {p} := by revert p; decide

/-- The weight `g`: one given node, `0`. -/
private def g : Fin 5 → ℕ := ![1, 0, 0, 0, 0]

/-- The weight `u`: one unit, at `3`. -/
private def u : Fin 5 → ℕ := ![0, 0, 0, 1, 0]

/-- The node `3` is heavy and `2` is light. -/
example : tree.Heavy g u 1 1 3 3 ∧ ¬tree.Heavy g u 1 1 3 2 := by decide

/-- The pieces: `{0, 1, 2}` (below the light node `2`), `{3}` and `{4}`. -/
example : (List.finRange 5).map (tree.piece g u 1 1 3) = [0, 0, 0, 1, 2] := by decide

/-- Fewer than `1 + 2 + 2 · (2 · 3)` pieces: the root and the other nodes have at most two
children. -/
example (p : Fin 5) : tree.piece g u 1 1 3 p < 1 + 2 + 2 * (tree.depth * 3) :=
  StagedTree.piece_lt (by norm_num) (by decide) (by decide) (by decide) (by decide) p

/-- The pieces are numbered below the number of nodes. -/
example (p : Fin 5) : tree.piece g u 1 1 3 p < 5 := by
  simpa using StagedTree.piece_lt_card (T := tree) (g := g) (u := u) (M := 1) (Y := 1) (k := 3) p

/-- The weight `g` below the light node `2`. -/
example : 3 * tree.sumBelow g 2 ≤ 4 * 1 :=
  StagedTree.light_given_le (u := u) (Y := 1) (by norm_num) (by decide)

/-- The weight `u` below the light node `2`. -/
example : 3 * tree.sumBelow u 2 ≤ 2 * 1 :=
  StagedTree.light_units_le (g := g) (M := 1) (by norm_num) (by decide)

/-- `3 g` adds up to at most `4` on every piece. -/
example (n : ℕ) : ∑ p ∈ univ.filter (tree.piece g u 1 1 3 · = n), 3 * g p ≤ 4 * 1 :=
  StagedTree.sum_piece_le _ (by decide) (fun _ hx =>
    (mul_sum _ _ _).symm.trans_le (StagedTree.light_given_le (by norm_num) hx)) n

/-- The units at the children of the nodes below the root. -/
example : tree.sumBelow (fun q => ∑ c ∈ tree.children q, u c) 4 ≤ tree.sumBelow u 4 :=
  StagedTree.sumBelow_children_le u 4

/-- The edges out of a piece meet one node. -/
example (n : ℕ) : ∃ x, ∀ q, q ≠ tree.root →
    ¬(tree.piece g u 1 1 3 q = n ↔ tree.piece g u 1 1 3 (tree.parent q) = n) →
      q = x ∨ tree.parent q = x :=
  StagedTree.exists_piece_boundary n

/-- **The program of the pieces** of the fixture, the same tree for every input: if a program
computes the indicators of its parents and the weights `u`, eight more stages compute the pieces. -/
example {Inp : Type} {D Y m p c : ℕ} {inp : Fin m → Inp → Fin D} {H : Set (Inp → ℕ)}
    (hY : StepBase D Y) (h5 : 5 ≤ Y) (hS : SlpN inp (p + c * Y ^ 12) H)
    (hpar : ∀ q q', {_x : Inp | tree.parent q = q'}.indicator 1 ∈ H)
    (hu : ∀ q, (fun _ : Inp => u q) ∈ H) :
    ∃ H', SlpN inp (p + (c + 8) * Y ^ 12) H' ∧ ∀ q, (fun _ => tree.piece g u 1 1 3 q) ∈ H' := by
  obtain ⟨H', hS', -, hP⟩ := pieces_stage (T := fun _ => tree) (g := g) (u := fun _ => u)
    (M := 1) (Yh := 1) (k := 3) hY (by simpa using h5) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) hS hpar hu (fun q => (show g q ≤ 1 by revert q; decide).trans (by omega))
    (fun _ q => (show u q ≤ 1 by revert q; decide).trans (by omega))
  exact ⟨H', hS', hP⟩

/-- A larger alphabet: the program of one input below `10` over `Fin 10` runs over `Fin 81`. -/
example : SlpN (fun (_ : Fin 1) (x : Fin 10) => (Fin.castLE (by norm_num) x : Fin 81)) 1
    (Set.range fun (_ : Fin 1) (x : Fin 10) => (x : ℕ)) :=
  (SlpN.inputs fun _ x => x).castLE (by norm_num) fun _ _ => Fin.val_castLE _ _

end CslibFrontierTests.SeparationPieces
