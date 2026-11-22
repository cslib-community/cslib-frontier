/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.BlockNetworks
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Tactic

/-!
# Local access to the block-counting networks

The network of the semantic reduction (`blockNetworkOf`) has
`2 q (3k + 1) m` edges and `q (3k + 2) + q (3k + 1) m` vertices, where
`b = blockLength t`, `q = numBlocks t` and `m = letterBits k s b`. Vertex `v`
has the ports `explicitPortsNum k q m σ v` and the table whose entry `j` is
`tableEntryNum`. With `NetPortTerm` and `NetTable`, every part of the network
is computed by a term from `x`, `t` and `σ`, without storing the network.
-/

public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open Cslib.Complexity.CountingSimulation _root_.Turing _root_.Turing.MultiTapePTM

variable {k s : ℕ} {State : Type} [DecidableEq State] (machine : MultiTapePTM k Bool State)
  (e : State ≃ Fin s)

theorem blockNetworkOf_eq (x : List Bool) (t σ : ℕ) :
    (blockNetworkOf machine e (x, t, σ)).2 =
      explicitNetworkNum e (blockLength t) machine x (numBlocks t) σ := by
  unfold blockNetworkOf
  exact explicitBlockNetwork_eq_explicitNetworkNum e (blockLength t) machine x σ

theorem numEdges_blockNetworkOf (x : List Bool) (t σ : ℕ) :
    (blockNetworkOf machine e (x, t, σ)).2.numEdges =
      2 * (numBlocks t * (3 * k + 1) * letterBits k s (blockLength t)) := by
  rw [blockNetworkOf_eq]; rfl

theorem length_vertices_blockNetworkOf (x : List Bool) (t σ : ℕ) :
    (blockNetworkOf machine e (x, t, σ)).2.vertices.length =
      numBlocks t * (3 * k + 2) + numBlocks t * (3 * k + 1) * letterBits k s (blockLength t) := by
  rw [blockNetworkOf_eq]; simp [explicitNetworkNum, explicitVerticesNum]

/-- **Vertex `v` of the network**: its ports and its table. -/
theorem vertex_blockNetworkOf (x : List Bool) (t σ v : ℕ)
    (hv : v < numBlocks t * (3 * k + 2) + numBlocks t * (3 * k + 1) * letterBits k s
        (blockLength t)) :
    (blockNetworkOf machine e (x, t, σ)).2.vertices[v]? = some
      (explicitPortsNum k (numBlocks t) (letterBits k s (blockLength t)) σ v,
        (List.range (2 ^ (explicitPortsNum k (numBlocks t) (letterBits k s (blockLength t)) σ
            v).length)).map
          (tableEntryNum e (blockLength t) machine x (numBlocks t) σ v
            (explicitPortsNum k (numBlocks t) (letterBits k s (blockLength t)) σ v))) := by
  rw [blockNetworkOf_eq]
  simp [explicitNetworkNum, explicitVerticesNum, explicitTableNum, hv]

end Cslib.Complexity.NtimeDspace.LocalSim
