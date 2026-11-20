/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.Reduction
public import CslibFrontier.Foundations.Relation.Layered
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith

/-!
# Layering the native configuration-graph reduction

Reuse the checked native NL-to-STCON construction, including its accepting sink and native
graph writer. Its graph is layered by the bounded-walk construction: each edge advances one
layer, and a waiting step leaves the original vertex unchanged. Reaching the fixed final-layer
target is equivalent to the original STCON answer, including paths that terminate early.

For a native logarithmic-space witness, both the width and the number of layers are polynomial
in input length. This is the layered-reachability prerequisite of #6747, not NL = UL.

## Main results

* `Cslib.Complexity.STCON.layered_reachable_iff`: exact reachability between fixed endpoints.
* `Cslib.Complexity.STCON.card_configurationLayered_le_pow`: a polynomial bound on graph size.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeNTM.ConfigurationGraph

/-- A copy of the original vertices in each layer from zero through `n-1`. -/
abbrev LayeredGraphVertex (I : STCONInstance) :=
  Relation.LayeredVertex.Bounded (Fin I.n) (I.n - 1)

/-- The simple layered graph, with waiting edges between successive copies of a vertex. -/
@[expose] def layeredRelation (I : STCONInstance) :
    LayeredGraphVertex I → LayeredGraphVertex I → Prop :=
  fun a b => Relation.LayeredVertex.Step I.Adj (I.n - 1) a.val b.val

/-- Fixed source, in the first layer. -/
@[expose] def layeredStart (I : STCONInstance) : LayeredGraphVertex I :=
  ⟨⟨0, I.s⟩, Nat.zero_le _⟩

/-- Fixed target, in the last layer. -/
@[expose] def layeredTarget (I : STCONInstance) : LayeredGraphVertex I :=
  ⟨⟨I.n - 1, I.t⟩, le_rfl⟩

/-- The layered graph is simple even if the original graph has self edges. -/
theorem layeredRelation_irrefl (I : STCONInstance) (v : LayeredGraphVertex I) :
    ¬ layeredRelation I v v := Relation.LayeredVertex.step_irrefl v.val

/-- Reachability between the fixed layered endpoints is exactly the original STCON answer.
Finite reachability supplies a path of at most `n-1` steps; waiting pads shorter paths. -/
theorem layered_reachable_iff (I : STCONInstance) :
    Relation.ReflTransGen (layeredRelation I) (layeredStart I) (layeredTarget I) ↔ I ∈ STCON := by
  change Relation.ReflTransGen
    (fun a b : LayeredGraphVertex I =>
      Relation.LayeredVertex.Step I.Adj (I.n - 1) a.val b.val) _ _ ↔ _
  rw [Relation.LayeredVertex.bounded_reachable_iff]
  change Relation.ReflTransGen (Relation.LayeredVertex.Step I.Adj (I.n - 1))
    ⟨0, I.s⟩ ⟨I.n - 1, I.t⟩ ↔ _
  rw [Relation.LayeredVertex.reachable_iff]
  exact (Relation.reflTransGen_iff_relatesWithinSteps (r := I.Adj)
    (by rw [Nat.card_fin]; have := I.s.isLt; omega)).symm

/-- A width-`n` graph has `n` layers in the construction. Its finite rectangular vertex set
therefore has `n²` vertices. -/
theorem card_layeredGraphVertex (I : STCONInstance) :
    Nat.card (LayeredGraphVertex I) = I.n ^ 2 := by
  rw [LayeredGraphVertex, Relation.LayeredVertex.card_bounded, Nat.card_fin]
  have hn : 1 ≤ I.n := by have := I.s.isLt; omega
  rw [Nat.sub_add_cancel hn, pow_two]

/-- The native configuration graph's layered version has polynomially many vertices, with
an exponent fixed by the machine and its native space constant. -/
theorem card_configurationLayered_le_pow {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    Nat.card (LayeredGraphVertex (configurationInstance ntm c w)) ≤
      (w.length + 2) ^ (2 * (radixExponent State c * Fintype.card (Register k) + 1)) := by
  rw [card_layeredGraphVertex]
  change (vertexBound (k := k) (radix (radixExponent State c) w.length) + 1) ^ 2 ≤ _
  rw [vertexBound_eq_pow]
  have hpos : 1 ≤ (w.length + 2) ^ (radixExponent State c * Fintype.card (Register k)) :=
    Nat.one_le_pow _ _ (by omega)
  have hwidth : (w.length + 2) ^ (radixExponent State c * Fintype.card (Register k)) + 1 ≤
      (w.length + 2) ^ (radixExponent State c * Fintype.card (Register k) + 1) := by
    rw [pow_succ]
    nlinarith
  calc
    _ ≤ ((w.length + 2) ^ (radixExponent State c * Fintype.card (Register k) + 1)) ^ 2 :=
      Nat.pow_le_pow_left hwidth 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

end Cslib.Complexity.STCON
