/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Algorithm
public import CslibFrontier.Computability.PolyTime.Graph.Dense
public import CslibFrontier.Computability.PolyTime.Int.Table
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Tactic.PolyTime

/-!
# Uniform dense inputs for planted-clique recovery

`RecoveryInput` stores the number of vertices and target size in unary, followed by raw row-major
adjacency bits. The decoder reads only the upper triangle and treats missing bits as `false`.
Every record therefore defines an undirected loopless graph, without a well-formedness promise.

The unary dimensions make iteration over the vertices polynomial in the input length, including
on short or malformed adjacency words. Signed entries and their dense integer row table have
uniform certificates in the native `ComputableInPolyTime` model. `rowEntry_signedRows` identifies
this table with the signed adjacency matrix used in the recovery proof.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Turing.MultiTapeTM

/-- A dense graph and requested clique size, with runtime-varying dimensions. -/
structure RecoveryInput where
  /-- Number of vertices, encoded in unary. -/
  vertexCount : ℕ
  /-- Requested number of planted vertices, encoded in unary. -/
  cliqueSize : ℕ
  /-- Row-major adjacency word; the upper triangle is used and missing bits are false. -/
  adjacencyBits : List Bool
  deriving DecidableEq, Repr, Inhabited

/-- Framed unary vertex count, framed unary clique size, then raw adjacency bits. -/
enc_structure encRecoveryInput : RecoveryInput where
  vertexCount : encUnary,
  cliqueSize : encUnary,
  adjacencyBits : encBits

attribute [fun_prop] encRecoveryInput_vertexCount_polyTime encRecoveryInput_cliqueSize_polyTime
  encRecoveryInput_adjacencyBits_polyTime encRecoveryInput_mk_polyTime

namespace RecoveryInput

/-- The graph component of a planted-clique input. The original three-field encoding is kept. -/
@[expose] def toDenseGraphInput (x : RecoveryInput) : DenseGraphInput :=
  ⟨x.vertexCount, x.adjacencyBits⟩

/-- Symmetric adjacency lookup through the common dense graph decoder. -/
@[expose] def adjacent (x : RecoveryInput) (i j : ℕ) : Bool :=
  x.toDenseGraphInput.adjacent i j

/-- The simple graph described by the graph component of a planted-clique input. -/
@[expose] def graph (x : RecoveryInput) : SimpleGraph (Fin x.vertexCount) :=
  x.toDenseGraphInput.graph

instance (x : RecoveryInput) : DecidableRel x.graph.Adj :=
  inferInstanceAs (DecidableRel x.toDenseGraphInput.graph.Adj)

/-- Forgetting the target size keeps the common dense graph presentation in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_toDenseGraphInput :
    ComputableInPolyTime toDenseGraphInput encRecoveryInput encDenseGraphInput := by
  unfold toDenseGraphInput
  fun_prop

/-- The integer signed adjacency entry, with its diagonal set to zero. -/
@[expose] def signedEntry (x : RecoveryInput) (i j : ℕ) : ℤ :=
  if i = j then 0 else if x.adjacent i j then 1 else -1

/-- The signed adjacency matrix stored as a list of rows of binary integers. -/
@[expose] def signedRows (x : RecoveryInput) : List (List ℤ) :=
  tabulateTable x.vertexCount x.vertexCount x.signedEntry

/-- The stored signed matrix is square with the declared dimension. -/
theorem isTableShape_signedRows (x : RecoveryInput) :
    IsTableShape x.vertexCount x.vertexCount x.signedRows :=
  isTableShape_tabulateTable _ _ _

/-- Stored signed entries agree with the signed matrix of the decoded simple graph. -/
theorem rowEntry_signedRows (x : RecoveryInput) (i j : Fin x.vertexCount) :
    rowEntry x.signedRows i j = signedAdjacency x.graph i j := by
  rw [signedRows, rowEntry_tabulateTable_of_lt _ i.isLt j.isLt]
  by_cases hij : i = j
  · subst j
    simp [signedEntry, signedAdjacency]
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [signedEntry, signedAdjacency, hij, hval, ite_false]
    rfl

/-- The stored matrix is the rowwise finite enumeration of the mathematical signed matrix. -/
theorem signedRows_eq_ofFn (x : RecoveryInput) :
    x.signedRows = List.ofFn (fun i => List.ofFn (fun j => signedAdjacency x.graph i j)) := by
  have htab : x.signedRows =
      List.ofFn (fun i : Fin x.vertexCount => List.ofFn (fun j : Fin x.vertexCount =>
        x.signedEntry i j)) := by
    apply List.ext_getElem (by simp [signedRows])
    intro i hi hi'
    apply List.ext_getElem (by simp [signedRows, tabulateTable])
    intro j hj hj'
    simp [signedRows, tabulateTable]
  rw [htab]
  congr 1
  funext i
  congr 1
  funext j
  exact (rowEntry_tabulateTable_of_lt x.signedEntry i.isLt j.isLt).symm.trans
    (rowEntry_signedRows x i j)

/-- Symmetric adjacency lookup is uniformly polynomial-time in the dense input and unary indices. -/
@[fun_prop] theorem computableInPolyTime_adjacent {α : Type} {encIn : α ↪ List Bool}
    {input : α → RecoveryInput} {i j : α → ℕ}
    (hx : ComputableInPolyTime input encIn encRecoveryInput)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun a => (input a).adjacent (i a) (j a)) encIn encBool := by
  unfold adjacent
  exact DenseGraphInput.computableInPolyTime_adjacent
    (computableInPolyTime_toDenseGraphInput.comp hx) hi hj

/-- Computing a signed entry charges the adjacency lookup and both unary indices. -/
@[fun_prop] theorem computableInPolyTime_signedEntry {α : Type} {encIn : α ↪ List Bool}
    {input : α → RecoveryInput} {i j : α → ℕ}
    (hx : ComputableInPolyTime input encIn encRecoveryInput)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun a => (input a).signedEntry (i a) (j a)) encIn encIntBin := by
  unfold signedEntry
  fun_prop

/-- Uniform native polynomial-time construction of the entire signed matrix. -/
@[fun_prop] theorem computableInPolyTime_signedRows :
    ComputableInPolyTime signedRows encRecoveryInput encIntTable := by
  unfold signedRows
  apply computableInPolyTime_tabulateTable <;> fun_prop

end RecoveryInput

end Cslib.Algorithms.PlantedClique
