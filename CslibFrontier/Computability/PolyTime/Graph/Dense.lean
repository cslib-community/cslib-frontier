/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Combinatorics.SimpleGraph.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.PolyTime

/-!
# Dense graph inputs with native adjacency lookup

`DenseGraphInput` stores a unary vertex count followed by raw row-major adjacency bits.
The decoder reads the upper triangle, rejects loops, and treats missing bits as false.
Consequently every input has a total simple-graph interpretation, even when the word is short
or asymmetric. This representation is shared by planted-clique and community-recovery programs.
The edge-list representation `Complexity.Graph` has different input and malformed-data semantics.

`ofGraph` presents a mathematical graph by its full adjacency word, and `graph_ofGraph` proves
that decoding this presentation returns the graph. Presentation is not a sampling primitive or
an operation performed by an algorithm. The native adjacency certificate charges all lookups
and the runtime unary indices.
-/

public section

namespace Cslib

open Turing.MultiTapeTM

/-- A dense graph whose dimension is supplied at runtime. -/
structure DenseGraphInput where
  /-- Number of vertices, encoded in unary. -/
  vertexCount : ℕ
  /-- Row-major bits; only the upper triangle is read, with missing bits false. -/
  adjacencyBits : List Bool
  deriving DecidableEq, Repr, Inhabited

/-- Framed unary vertex count followed by raw row-major adjacency bits. -/
enc_structure encDenseGraphInput : DenseGraphInput where
  vertexCount : encUnary,
  adjacencyBits : encBits

attribute [fun_prop] encDenseGraphInput_vertexCount_polyTime
  encDenseGraphInput_adjacencyBits_polyTime encDenseGraphInput_mk_polyTime

namespace DenseGraphInput

/-- Symmetric, loopless lookup in the upper triangle of the raw adjacency word. -/
@[expose] def adjacent (x : DenseGraphInput) (i j : ℕ) : Bool :=
  i != j && x.adjacencyBits.getD (min i j * x.vertexCount + max i j) false

/-- The simple graph decoded from any input, including malformed adjacency words. -/
@[expose] def graph (x : DenseGraphInput) : SimpleGraph (Fin x.vertexCount) where
  Adj i j := x.adjacent i j = true
  symm := by
    constructor
    intro i j h
    simpa only [adjacent, min_comm j.val i.val, max_comm j.val i.val,
      bne_comm (a := j.val) (b := i.val)] using h
  loopless := by
    constructor
    intro i
    simp [adjacent]

instance (x : DenseGraphInput) : DecidableRel x.graph.Adj :=
  fun i j => inferInstanceAs (Decidable (x.adjacent i j = true))

/-- Symmetric adjacency lookup is polynomial-time in the dense input and unary indices. -/
@[fun_prop] theorem computableInPolyTime_adjacent {α : Type} {encIn : α ↪ List Bool}
    {input : α → DenseGraphInput} {i j : α → ℕ}
    (hx : ComputableInPolyTime input encIn encDenseGraphInput)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun a => (input a).adjacent (i a) (j a)) encIn encBool := by
  unfold adjacent
  have hmin := ComputableInPolyTime.unary_min' hi hj
  have hmax := ComputableInPolyTime.unary_max' hi hj
  fun_prop

open scoped Classical in
/-- Present a graph by all `n²` adjacency bits in row-major order. -/
@[expose] noncomputable def ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) : DenseGraphInput where
  vertexCount := n
  adjacencyBits := (List.finRange n).flatMap fun i => List.ofFn fun j => decide (G.Adj i j)

/-- Decoding the full adjacency word recovers the original graph. -/
@[simp] theorem graph_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) :
    (ofGraph G).graph = G := by
  classical
  ext i j
  change Fin n at i j
  change (i.val != j.val &&
    ((List.finRange n).flatMap fun i => List.ofFn fun j => decide (G.Adj i j)).getD
      (min i.val j.val * n + max i.val j.val) false) = true ↔ G.Adj i j
  rcases le_total i.val j.val with h | h
  · rw [min_eq_left h, max_eq_right h, List.getD_flatMap_ofFn]
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    exact ⟨And.right, fun hG => ⟨fun heq => hG.ne (Fin.ext heq), hG⟩⟩
  · rw [min_eq_right h, max_eq_left h, List.getD_flatMap_ofFn]
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    exact ⟨fun hG => hG.2.symm, fun hG => ⟨fun heq => hG.ne (Fin.ext heq), hG.symm⟩⟩

/-- A canonical dense input has `n²` adjacency bits and one framed unary dimension. -/
theorem length_encDenseGraphInput_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) :
    (encDenseGraphInput (ofGraph G)).length = n * n + 2 * n + 1 := by
  simp [encDenseGraphInput_apply, ofGraph, List.length_flatMap]
  omega

end DenseGraphInput

end Cslib
