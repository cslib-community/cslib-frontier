/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Arborescence.Branching
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Foundations.Data.List.ArgMin
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Polynomial-time Chu–Liu/Edmonds arborescence and branching solvers (`P`)

This file implements plain `ComputableInPolyTime` list-table versions of the Chu–Liu/Edmonds
minimum-cost rooted arborescence algorithm and Edmonds's Theorem 1 maximum-weight branching solver
[Edmonds1967Branchings], proving that the corresponding decision problems lie in `P` with binary
integer arc weights (`encIntBin`).

Contraction modifies arc costs solely via `otherCycleCost` additions (no integer subtraction), so
after `i` contraction rounds every intermediate table entry satisfies
`|cᵢ[u, w]| ≤ (n + 1) ^ i · M₀` and has binary bit length `O(L²)` in the input length `L`, keeping
the contraction stack and all reachable `ContractState`s bounded by a polynomial in `L`.

## Main definitions

* `Cslib.Algorithms.Lean.Arborescence.ArborescenceInstance`, `.ArborescenceDecInstance`,
  `.BranchingInstance`, `.BranchingDecInstance`: structured inputs and decision instances encoded
  with `enc_structure`.
* `Cslib.Algorithms.Lean.Arborescence.ContractLevel`, `.ContractState`: structured contraction
  frames and forward-pass state for `iterateWith` and `foldl'`.
* `Cslib.Algorithms.Lean.Arborescence.edmondsList`, `.edmondsOutList`, `.optimumBranchingList`:
  list-table solvers for minimum-cost spanning in-arborescences, out-arborescences, and
  maximum-weight branchings.
* `Cslib.Algorithms.Lean.Arborescence.minArborescenceDec`, `.minOutArborescenceDec`,
  `.maxBranchingDec`: decision languages for bounded-cost spanning in/out-arborescences and
  bounded-weight branchings.

## Main results

* `Cslib.Algorithms.Lean.Arborescence.computableInPolyTime_edmondsList`,
  `.computableInPolyTime_edmondsOutList`, `.computableInPolyTime_optimumBranchingList`:
  all three solvers are `ComputableInPolyTime` on binary integer weights.
* `Cslib.Algorithms.Lean.Arborescence.minArborescenceDec_mem_P`,
  `.minOutArborescenceDec_mem_P`, `.maxBranchingDec_mem_P`: all three decision problems belong to
  `Cslib.Complexity.P`.

## References

* [J. Edmonds, *Optimum branchings*][Edmonds1967Branchings], Sections 1–4 (Theorem 1)
-/

public section

namespace Cslib.Algorithms.Lean.Arborescence

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Problem instances and contraction state structures -/

/-- Row-major Boolean adjacency matrix encoding. -/
abbrev encAdjTable : List (List Bool) ↪ List Bool :=
  encList (encList encBool)

/-- Row-major binary integer weight or cost matrix encoding. -/
abbrev encIntTable : List (List ℤ) ↪ List Bool :=
  encList (encList encIntBin)

/-- Encoding of an optional list of unary vertex indices (`Option (List ℕ)`). -/
abbrev encParentOption : Option (List ℕ) ↪ List Bool :=
  encOption (encList encUnary)

/-- Instance of the minimum-cost spanning arborescence problem on vertices `0, …, n - 1` (`n =
adj.length`), given by a Boolean adjacency table, a binary integer cost table, and a binary root
vertex index. -/
structure ArborescenceInstance where
  /-- `n × n` Boolean adjacency matrix (`adj[u][v] = true` for arc `u → v`). -/
  adj : List (List Bool)
  /-- `n × n` binary integer arc-cost matrix. -/
  cost : List (List ℤ)
  /-- Designated root vertex index (`root < adj.length`). -/
  root : ℕ

/-- Encoding of `ArborescenceInstance` with Boolean adjacency table, `encIntBin` cost matrix, and
binary root index `encNat`. -/
enc_structure encArborescenceInstance : ArborescenceInstance where
  adj : encAdjTable, cost : encIntTable, root : encNat

/-- Decision instance for minimum-cost spanning arborescence (`arcCost ≤ threshold`). -/
structure ArborescenceDecInstance where
  /-- Underlying weighted digraph and root instance. -/
  inst : ArborescenceInstance
  /-- Binary integer cost upper bound. -/
  threshold : ℤ

/-- Encoding of `ArborescenceDecInstance` as instance plus binary `encIntBin` threshold. -/
enc_structure encArborescenceDecInstance : ArborescenceDecInstance where
  inst : encArborescenceInstance, threshold : encIntBin

/-- Instance of the maximum-weight branching problem on vertices `0, …, n - 1`. -/
structure BranchingInstance where
  /-- `n × n` Boolean adjacency matrix. -/
  adj : List (List Bool)
  /-- `n × n` binary integer arc-weight matrix. -/
  weight : List (List ℤ)

/-- Encoding of `BranchingInstance` with Boolean adjacency table and `encIntBin` weights. -/
enc_structure encBranchingInstance : BranchingInstance where
  adj : encAdjTable, weight : encIntTable

/-- Decision instance for maximum-weight branching (`threshold ≤ arcCost`). -/
structure BranchingDecInstance where
  /-- Underlying weighted digraph instance. -/
  inst : BranchingInstance
  /-- Binary integer weight lower bound. -/
  threshold : ℤ

/-- Encoding of `BranchingDecInstance` as instance plus binary `encIntBin` threshold. -/
enc_structure encBranchingDecInstance : BranchingDecInstance where
  inst : encBranchingInstance, threshold : encIntBin

/-- One contraction level recorded by the forward pass of `edmondsTableAuxList` for bottom-up
expansion of parent pointers. -/
structure ContractLevel where
  /-- Selected parent table `f[v]` before contraction (`v < n`). -/
  parent : List ℕ
  /-- Cycle indicator mask `inCycle[v]` for the contracted directed cycle `C`. -/
  inCycle : List Bool
  /-- Best incoming vertex index into `C` from each `u ∉ C`, if any. -/
  bestEntry : List (Option ℕ)
  /-- Best outgoing vertex `x ∈ C` to each `w ∉ C`, if any. -/
  bestExit : List (Option ℕ)
  /-- Representative vertex `x₀ ∈ C` of the contracted cycle. -/
  rep : ℕ

/-- Encoding of `ContractLevel` with unary vertex indices bounded by `n`. -/
enc_structure encContractLevel : ContractLevel where
  parent : (encList encUnary), inCycle : (encList encBool),
  bestEntry : (encList (encOption encUnary)), bestExit : (encList (encOption encUnary)),
  rep : encUnary

/-- Forward contraction state of the list-based Chu–Liu/Edmonds solver. -/
structure ContractState where
  /-- Current contracted adjacency matrix. -/
  adj : List (List Bool)
  /-- Current contracted integer cost matrix. -/
  cost : List (List ℤ)
  /-- Root vertex index (`encUnary` during table contraction). -/
  root : ℕ
  /-- Whether contraction has terminated (acyclic solution found or infeasible). -/
  done : Bool
  /-- Base acyclic parent map when terminated cleanly, or `none`. -/
  result : Option (List ℕ)
  /-- Contraction frames pushed innermost-first for backward `foldl` expansion. -/
  stack : List ContractLevel

/-- Encoding of `ContractState` for `iterateWith`. -/
enc_structure encContractState : ContractState where
  adj : encAdjTable, cost : encIntTable,
  root : encUnary, done : encBool, result : encParentOption,
  stack : (encList encContractLevel)

/-- Input bundle for parameterized `edmondsTableAuxList`. -/
structure TableAuxInput where
  /-- Iteration bound (fuel) in unary. -/
  fuel : ℕ
  /-- Root vertex index in unary. -/
  root : ℕ
  /-- Boolean adjacency table. -/
  adj : List (List Bool)
  /-- Integer arc-cost table. -/
  cost : List (List ℤ)

/-- Encoding of `TableAuxInput` with unary fuel and root and binary integer costs. -/
enc_structure encTableAuxInput : TableAuxInput where
  fuel : encUnary, root : encUnary, adj : encAdjTable,
  cost : encIntTable

/-- Intermediate workspace record for one contraction round (`contractFromParent`). -/
structure ContractWork where
  /-- Current contraction state before the step. -/
  state : ContractState
  /-- Selected parent table `f`. -/
  parent : List ℕ
  /-- Representative vertex `x₀` of the detected cycle. -/
  rep : ℕ
  /-- Cycle indicator mask `inCycle`. -/
  inCycle : List Bool
  /-- Other-cycle-cost sum vector `otherCycleCost`. -/
  other : List ℤ
  /-- Best entry vector `bestEntry`. -/
  bestEntry : List (Option ℕ)
  /-- Best exit vector `bestExit`. -/
  bestExit : List (Option ℕ)

/-- Encoding of `ContractWork` for assembling step certificates without nested pair projections. -/
enc_structure encContractWork : ContractWork where
  state : encContractState, parent : (encList encUnary), rep : encUnary,
  inCycle : (encList encBool), other : (encList encIntBin),
  bestEntry : (encList (encOption encUnary)), bestExit : (encList (encOption encUnary))

/-! ### Table semantics and decision problems -/

/-- Read entry `(u, w)` of a Boolean adjacency table, defaulting out-of-bounds to `false`. -/
@[expose] def adjAt (a : List (List Bool)) (u w : ℕ) : Bool :=
  (a.getD u []).getD w false

/-- Read `(u, w)` entry of an integer cost table, defaulting out-of-bounds entries to `0`. -/
@[expose] def costAt (c : List (List ℤ)) (u w : ℕ) : ℤ :=
  (c.getD u []).getD w 0

/-- Digraph on `Fin a.length` defined by `adjAt a`. -/
@[expose] def tableDigraph (a : List (List Bool)) : Digraph (Fin a.length) where
  Adj u w := adjAt a u.val w.val = true

instance instDecidableRelTableDigraphAdj (a : List (List Bool)) :
    DecidableRel (tableDigraph a).Adj :=
  fun u w => inferInstanceAs (Decidable (adjAt a u.val w.val = true))

/-- Integer arc-cost function on `Fin n` extracted from `costAt c`. -/
@[expose] def tableCost (c : List (List ℤ)) {n : ℕ} (u w : Fin n) : ℤ :=
  costAt c u.val w.val

/-- Decision language for minimum-cost spanning in-arborescence (`arcCost T ≤ threshold`). -/
@[expose] def minArborescenceDec : Set ArborescenceDecInstance :=
  {d | ∃ h : d.inst.root < d.inst.adj.length,
    ∃ T : Digraph (Fin d.inst.adj.length),
      T.IsInArborescence ⟨d.inst.root, h⟩ ∧ T ≤ tableDigraph d.inst.adj ∧
        let _ := Classical.decRel T.Adj
        arcCost T (tableCost d.inst.cost) ≤ d.threshold}

/-- Decision language for minimum-cost spanning out-arborescence (`arcCost T ≤ threshold`). -/
@[expose] def minOutArborescenceDec : Set ArborescenceDecInstance :=
  {d | ∃ h : d.inst.root < d.inst.adj.length,
    ∃ T : Digraph (Fin d.inst.adj.length),
      T.IsOutArborescence ⟨d.inst.root, h⟩ ∧ T ≤ tableDigraph d.inst.adj ∧
        let _ := Classical.decRel T.Adj
        arcCost T (tableCost d.inst.cost) ≤ d.threshold}

/-- Decision language for maximum-weight branching (`threshold ≤ arcCost B`). -/
@[expose] def maxBranchingDec : Set BranchingDecInstance :=
  {d | ∃ B : Digraph (Fin d.inst.adj.length),
    B.IsBranching ∧ B ≤ tableDigraph d.inst.adj ∧
      let _ := Classical.decRel B.Adj
      d.threshold ≤ arcCost B (tableCost d.inst.weight)}

/-! ### List-based Chu–Liu/Edmonds operations -/

/-- Single step in scanning `List.range n` for the first index satisfying `pred` with minimum
`key`. -/
@[expose] def argMinStep (pred : ℕ → Bool) (key : ℕ → ℤ) (acc : Option ℕ) (j : ℕ) :
    Option ℕ :=
  if pred j then
    acc.elim (some j) fun cur => if decide (key j < key cur) then some j else some cur
  else acc

/-- First index in `List.range n` satisfying `pred` with minimum `key`. -/
@[expose] def argMinRange (n : ℕ) (pred : ℕ → Bool) (key : ℕ → ℤ) : Option ℕ :=
  (List.range n).foldl (argMinStep pred key) none

/-- Select cheapest valid incoming parent for each `v ≠ r` (`some r` at `v = r`), returning `none`
when some `v ≠ r` has no valid candidate arc. -/
@[expose] def selectParentsList (a : List (List Bool)) (c : List (List ℤ)) (r : ℕ) :
    Option (List ℕ) :=
  let n := a.length
  let opts := (List.range n).map fun v =>
    if v == r then some r
    else argMinRange n (fun w => adjAt a v w && (w != v)) (fun w => costAt c v w)
  if opts.all Option.isSome then some (opts.map fun o => o.getD 0) else none

/-- Follow parent table `f` from `x`, defaulting out-of-bounds lookups to `0`. -/
@[expose] def followParent (f : List ℕ) (x : ℕ) : ℕ :=
  f.getD x 0

/-- Test whether `x` reaches itself within `n` steps of `followParent f` (in `1 .. n` steps). -/
@[expose] def hasCycleFromList (n : ℕ) (f : List ℕ) (x : ℕ) : Bool :=
  (List.range n).any fun k => (followParent f)^[k + 1] x == x

/-- Find the first vertex `x < n` with `x ≠ r` lying on a cycle of `followParent f`. -/
@[expose] def findCycleList (n r : ℕ) (f : List ℕ) : Option ℕ :=
  (List.range n).find? fun x => (x != r) && hasCycleFromList n f x

/-- Boolean mask of vertices `y < n` in the `n`-step orbit of `x0` under `followParent f`. -/
@[expose] def cycleMaskList (n : ℕ) (f : List ℕ) (x0 : ℕ) : List Bool :=
  (List.range n).map fun y =>
    (List.range n).any fun k => (followParent f)^[k] x0 == y

/-- Subtraction-free sum `∑ y ∈ C \ {x}, c[y, f[y]]` for `x ∈ C`, and `0` outside `C`. -/
@[expose] def otherCycleCostList (n : ℕ) (c : List (List ℤ)) (f : List ℕ)
    (inCycle : List Bool) : List ℤ :=
  (List.range n).map fun x =>
    if inCycle.getD x false then
      (((List.range n).filter fun y => inCycle.getD y false && (y != x)).map fun y =>
        costAt c y (f.getD y 0)).sum
    else 0

/-- Best cycle vertex `y ∈ C` maximizing cheapness of `u → y` for each `u < n`. -/
@[expose] def bestEntryList (n : ℕ) (a : List (List Bool)) (c : List (List ℤ))
    (inCycle : List Bool) : List (Option ℕ) :=
  (List.range n).map fun u =>
    argMinRange n (fun y => inCycle.getD y false && adjAt a u y) (fun y => costAt c u y)

/-- Best exit vertex `x ∈ C` minimizing `c[x, w] + otherCycleCost[x]` for each `w < n`. -/
@[expose] def bestExitList (n : ℕ) (a : List (List Bool)) (c : List (List ℤ))
    (inCycle : List Bool) (other : List ℤ) : List (Option ℕ) :=
  (List.range n).map fun w =>
    argMinRange n (fun x => inCycle.getD x false && adjAt a x w)
      (fun x => costAt c x w + other.getD x 0)

/-- Contracted `n × n` adjacency table. -/
@[expose] def contractAdjList (n : ℕ) (inCycle : List Bool) (a : List (List Bool))
    (bEntry bExit : List (Option ℕ)) (x0 r : ℕ) : List (List Bool) :=
  (List.range n).map fun u =>
    (List.range n).map fun w =>
      if inCycle.getD u false then
        if u == x0 then !(inCycle.getD w false) && (bExit.getD w none).isSome
        else w == r
      else
        if inCycle.getD w false then (w == x0) && (bEntry.getD u none).isSome
        else adjAt a u w

/-- Contracted `n × n` subtraction-free integer cost table. -/
@[expose] def contractCostList (n : ℕ) (inCycle : List Bool) (c : List (List ℤ))
    (other : List ℤ) (bEntry bExit : List (Option ℕ)) (x0 : ℕ) : List (List ℤ) :=
  (List.range n).map fun u =>
    (List.range n).map fun w =>
      if inCycle.getD u false then
        if u == x0 then
          (bExit.getD w none).elim (costAt c u w) fun x => costAt c x w + other.getD x 0
        else 0
      else
        if w == x0 then
          (bEntry.getD u none).elim (costAt c u w) fun y => costAt c u y
        else costAt c u w

/-- Expand a contracted parent list `q` using one saved `ContractLevel`. -/
@[expose] def expandLevelList (lvl : ContractLevel) (q : List ℕ) : List ℕ :=
  let n := lvl.inCycle.length
  let qx0 := q.getD lvl.rep 0
  let bx := lvl.bestExit.getD qx0 none
  (List.range n).map fun v =>
    if lvl.inCycle.getD v false then
      bx.elim (lvl.parent.getD v 0) fun x => if v == x then qx0 else lvl.parent.getD v 0
    else if q.getD v 0 == lvl.rep then (lvl.bestEntry.getD v none).getD v
    else q.getD v 0

/-- Perform one cycle-contraction step given selected parent table `f` and cycle witness `x0`. -/
@[expose] def contractFromParent (s : ContractState) (f : List ℕ) (x0 : ℕ) : ContractState :=
  let n := s.adj.length
  let inCycle := cycleMaskList n f x0
  let other := otherCycleCostList n s.cost f inCycle
  let bEntry := bestEntryList n s.adj s.cost inCycle
  let bExit := bestExitList n s.adj s.cost inCycle other
  let a' := contractAdjList n inCycle s.adj bEntry bExit x0 s.root
  let c' := contractCostList n inCycle s.cost other bEntry bExit x0
  let lvl : ContractLevel := ⟨f, inCycle, bEntry, bExit, x0⟩
  ⟨a', c', s.root, false, none, lvl :: s.stack⟩

/-- Perform one step of the iterative forward contraction pass. -/
@[expose] def contractStep (s : ContractState) : ContractState :=
  if s.done then s
  else
    (selectParentsList s.adj s.cost s.root).elim
      ⟨s.adj, s.cost, s.root, true, none, s.stack⟩
      fun f =>
        (findCycleList s.adj.length s.root f).elim
          ⟨s.adj, s.cost, s.root, true, some f, s.stack⟩
          fun x0 => contractFromParent s f x0

/-- Iterative list-table Chu–Liu/Edmonds solver running `fuel` forward steps followed by stack
expansion. -/
@[expose] def edmondsTableAuxList (fuel r : ℕ) (a : List (List Bool)) (c : List (List ℤ)) :
    Option (List ℕ) :=
  let init : ContractState := ⟨a, c, r, false, none, []⟩
  let final := contractStep^[fuel] init
  final.result.map fun base => final.stack.foldl (fun q lvl => expandLevelList lvl q) base

/-- Normalize `inst.root` to a unary-bounded index (`0` when out of bounds). -/
@[expose] def clampedRoot (inst : ArborescenceInstance) : ℕ :=
  if decide ((inst.root : ℤ) < (inst.adj.length : ℤ)) then inst.root else 0

/-- Solve minimum-cost spanning in-arborescence for `inst`, returning `none` if `root ≥ n` or no
spanning in-arborescence exists. -/
@[expose] def edmondsList (inst : ArborescenceInstance) : Option (List ℕ) :=
  if decide ((inst.root : ℤ) < (inst.adj.length : ℤ)) then
    edmondsTableAuxList inst.adj.length (clampedRoot inst) inst.adj inst.cost
  else none

/-- Transpose an `n × n` Boolean matrix (`n = a.length`). -/
@[expose] def transposeBoolTable (a : List (List Bool)) : List (List Bool) :=
  let n := a.length
  (List.range n).map fun u => (List.range n).map fun w => adjAt a w u

/-- Transpose an `n × n` integer matrix (`c[w, u]` for `u, w < n`). -/
@[expose] def transposeIntTable (n : ℕ) (c : List (List ℤ)) : List (List ℤ) :=
  (List.range n).map fun u => (List.range n).map fun w => costAt c w u

/-- Solve minimum-cost spanning out-arborescence by reversing all arcs and costs. -/
@[expose] def edmondsOutList (inst : ArborescenceInstance) : Option (List ℕ) :=
  if decide ((inst.root : ℤ) < (inst.adj.length : ℤ)) then
    edmondsTableAuxList inst.adj.length (clampedRoot inst)
      (transposeBoolTable inst.adj) (transposeIntTable inst.adj.length inst.cost)
  else none

/-- Decision procedure for `minArborescenceDec`. -/
@[expose] def minArborescenceDecide (d : ArborescenceDecInstance) : Bool :=
  (edmondsList d.inst).elim false fun p =>
    let r := clampedRoot d.inst
    let n := d.inst.adj.length
    let total := (((List.range n).filter fun v => v != r).map fun v =>
      costAt d.inst.cost v (p.getD v 0)).sum
    decide (total ≤ d.threshold)

/-- Decision procedure for `minOutArborescenceDec`. -/
@[expose] def minOutArborescenceDecide (d : ArborescenceDecInstance) : Bool :=
  (edmondsOutList d.inst).elim false fun p =>
    let r := clampedRoot d.inst
    let n := d.inst.adj.length
    let total := (((List.range n).filter fun v => v != r).map fun v =>
      costAt d.inst.cost (p.getD v 0) v).sum
    decide (total ≤ d.threshold)

/-- `(n + 1) × (n + 1)` super-root adjacency matrix with reversed real arcs (`v < n, u < n`:
`adj[u, v]`) and fallback arcs `v → n` (`v < n`). -/
@[expose] def superRootAdjList (a : List (List Bool)) : List (List Bool) :=
  let n := a.length
  (List.range (n + 1)).map fun u =>
    (List.range (n + 1)).map fun w =>
      if u == n then false
      else if w == n then true
      else adjAt a w u

/-- `(n + 1) × (n + 1)` super-root cost matrix with negated reversed weights `-wt[w, u]` and `0`
on fallback arcs incident to vertex `n`. -/
@[expose] def superRootWeightList (n : ℕ) (wt : List (List ℤ)) : List (List ℤ) :=
  (List.range (n + 1)).map fun u =>
    (List.range (n + 1)).map fun w =>
      if u == n then 0
      else if w == n then 0
      else -costAt wt w u

/-- Optimum branching parent map on `0, …, n - 1` computed via Edmonds's super-root reduction
(`p[v] = v` denotes a root of a component tree). -/
@[expose] def optimumBranchingList (B : BranchingInstance) : List ℕ :=
  let n := B.adj.length
  let adj' := superRootAdjList B.adj
  let wt' := superRootWeightList n B.weight
  (edmondsTableAuxList (n + 1) n adj' wt').elim [] fun p =>
    (List.range n).map fun v =>
      let pv := p.getD v 0
      if pv == n then v else pv

/-- Decision procedure for `maxBranchingDec`. -/
@[expose] def maxBranchingDecide (d : BranchingDecInstance) : Bool :=
  let n := d.inst.adj.length
  let p := optimumBranchingList d.inst
  let total := (((List.range n).filter fun v => p.getD v 0 != v).map fun v =>
    costAt d.inst.weight (p.getD v 0) v).sum
  decide (d.threshold ≤ total)

/-! ### Polynomial-time certificates for list operations -/

private theorem length_encOption_unary_le {o : Option ℕ} {n : ℕ}
    (ho : ∀ x, o = some x → x ≤ n) :
    (encOption encUnary o).length ≤ n + 1 := by
  cases o with
  | none => simp
  | some x =>
    have hx := ho x rfl
    simp [encOption_some, encUnary_apply]
    omega

private theorem foldl_argMinStep_lt (pred : ℕ → Bool) (key : ℕ → ℤ) (n : ℕ) :
    ∀ (l : List ℕ), (∀ j ∈ l, j < n) →
      ∀ (acc : Option ℕ), (∀ cur, acc = some cur → cur < n) →
        ∀ res, l.foldl (argMinStep pred key) acc = some res → res < n
  | [], _, acc, hacc, res, hres => hacc res hres
  | j :: l, hl, acc, hacc, res, hres => by
    refine foldl_argMinStep_lt pred key n l (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      (argMinStep pred key acc j) (fun cur hcur => ?_) res (by simpa using hres)
    have hj : j < n := hl j List.mem_cons_self
    unfold argMinStep at hcur
    split_ifs at hcur
    · cases acc with
      | none => exact (Option.some_injective _ hcur) ▸ hj
      | some c =>
        simp only [Option.elim_some] at hcur
        split_ifs at hcur <;>
          exact (Option.some_injective _ hcur) ▸ (by first | exact hj | exact hacc c rfl)
    · exact hacc cur hcur

private theorem computableInPolyTime_argMinRange {γ π : Type}
    {encIn : γ ↪ List Bool} {encPar : π ↪ List Bool}
    {par : γ → π} {bound : γ → ℕ} {pred : π → ℕ → Bool} {key : π → ℕ → ℤ}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hbound : ComputableInPolyTime bound encIn encUnary)
    (hpred : ComputableInPolyTime (fun p : π × ℕ => pred p.1 p.2)
      (encPair encPar encUnary) encBool)
    (hkey : ComputableInPolyTime (fun p : π × ℕ => key p.1 p.2)
      (encPair encPar encUnary) encIntBin) :
    ComputableInPolyTime (fun x => argMinRange (bound x) (pred (par x)) (key (par x)))
      encIn (encOption encUnary) := by
  let Q := encPair (encPair encPar (encOption encUnary)) encUnary
  have hstep : ComputableInPolyTime
      (fun q : (π × Option ℕ) × ℕ => argMinStep (pred q.1.1) (key q.1.1) q.1.2 q.2)
      Q (encOption encUnary) := by
    have hparq : ComputableInPolyTime (fun q : (π × Option ℕ) × ℕ => q.1.1) Q encPar := by polytime
    have hacc : ComputableInPolyTime (fun q : (π × Option ℕ) × ℕ => q.1.2) Q
        (encOption encUnary) := by polytime
    have hj : ComputableInPolyTime (fun q : (π × Option ℕ) × ℕ => q.2) Q encUnary := by polytime
    have hbody : ComputableInPolyTime
        (fun r : ((π × Option ℕ) × ℕ) × ℕ =>
          if decide (key r.1.1.1 r.1.2 < key r.1.1.1 r.2) then some r.1.2 else some r.2)
        (encPair Q encUnary) (encOption encUnary) :=
      ite (intBin_lt.comp
          ((hkey.comp ((hparq.comp (fst _ _)).prod (hj.comp (fst _ _)))).prod
           (hkey.comp ((hparq.comp (fst _ _)).prod (snd _ _)))))
        ((optionSome encUnary).comp (hj.comp (fst _ _))) ((optionSome encUnary).comp (snd _ _))
    exact ite (hpred.comp (hparq.prod hj))
      (optionElimWithInput hacc ((optionSome encUnary).comp hj) hbody) hacc
  have hB : PolyBounded (fun x => (encIn x).length) (fun x => bound x + 1) := by
    obtain ⟨c, d, hcd⟩ := hbound.polyBounded.exists_le
    refine PolyBounded.of_forall_le (c + 1) d fun x => ?_
    have h1 := hcd x
    have hpow : 1 ≤ ((encIn x).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
    nlinarith
  refine ComputableInPolyTime.foldlWith (encA := encUnary) (encB := encOption encUnary)
    (encL := encList encUnary) (encP := encPar)
    (par := par) (list := fun x => List.range (bound x)) (init := fun _ => none)
    (step := fun p acc j => argMinStep (pred p) (key p) acc j)
    hpar (by fun_prop) (const none) hstep hB fun x i _ =>
      length_encOption_unary_le fun res hres => Nat.le_of_lt <|
        foldl_argMinStep_lt (pred (par x)) (key (par x)) (bound x)
          ((List.range (bound x)).take i) (fun j hj => List.mem_range.mp (List.mem_of_mem_take hj))
          none (fun _ h => by simp at h) res hres

private theorem computableInPolyTime_adjAt' {γ : Type} {encIn : γ ↪ List Bool}
    {a : γ → List (List Bool)} {u w : γ → ℕ}
    (ha : ComputableInPolyTime a encIn (encList (encList encBool)))
    (hu : ComputableInPolyTime u encIn encUnary)
    (hw : ComputableInPolyTime w encIn encUnary) :
    ComputableInPolyTime (fun x => adjAt (a x) (u x) (w x)) encIn encBool := by
  unfold adjAt
  exact listGetDWithInput (listGetDWithInput ha hu []) hw false

private theorem computableInPolyTime_costAt' {γ : Type} {encIn : γ ↪ List Bool}
    {c : γ → List (List ℤ)} {u w : γ → ℕ}
    (hc : ComputableInPolyTime c encIn (encList (encList encIntBin)))
    (hu : ComputableInPolyTime u encIn encUnary)
    (hw : ComputableInPolyTime w encIn encUnary) :
    ComputableInPolyTime (fun x => costAt (c x) (u x) (w x)) encIn encIntBin := by
  unfold costAt
  exact listGetDWithInput (listGetDWithInput hc hu []) hw 0

attribute [local fun_prop] computableInPolyTime_adjAt' computableInPolyTime_costAt'

private theorem computableInPolyTime_selectParentsState :
    ComputableInPolyTime
      (fun s : ContractState => selectParentsList s.adj s.cost s.root)
      encContractState (encOption (encList encUnary)) := by
  have hopts : ComputableInPolyTime
      (fun s : ContractState => (List.range s.adj.length).map fun v =>
        if v == s.root then some s.root
        else argMinRange s.adj.length (fun w => adjAt s.adj v w && (w != v))
          (fun w => costAt s.cost v w))
      encContractState (encList (encOption encUnary)) :=
    mapWithInput (range.comp (show ComputableInPolyTime
      (fun s : ContractState => s.adj.length) encContractState encUnary by fun_prop)) <|
      ite (by fun_prop) (by fun_prop)
        (computableInPolyTime_argMinRange (encPar := encPair encContractState encUnary)
          (par := fun q => q) (bound := fun q => q.1.adj.length)
          (pred := fun par w => adjAt par.1.adj par.2 w && (w != par.2))
          (key := fun par w => costAt par.1.cost par.2 w)
          (id' (encIn := encPair encContractState encUnary))
          (by fun_prop) (by fun_prop) (by fun_prop))
  unfold selectParentsList
  exact ite (allWithInput hopts (optionIsSome (encB := encUnary) (snd _ _)))
    ((optionSome (encList encUnary)).comp
      (mapWithInput hopts (optionGetDWithInput (snd _ _) (const 0))))
    (const none)

private theorem followParent_iterate_le (f : List ℕ) (x : ℕ) :
    ∀ k, (followParent f)^[k] x ≤ max x (encList encUnary f).length
  | 0 => le_max_left _ _
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact (List.getD_le_of_forall_le (fun y hy => by
      have h : (encUnary y).length ≤ (encList encUnary f).length :=
        SizedListEncoding.length_elem_le f y hy
      simpa only [encUnary_apply, List.length_replicate] using h) _).trans (le_max_right _ _)

private theorem computableInPolyTime_followParent_iterate :
    ComputableInPolyTime
      (fun p : (List ℕ × ℕ) × ℕ => (followParent p.1.1)^[p.2] p.1.2)
      (encPair (encPair (encList encUnary) encUnary) encUnary) encUnary := by
  let E := encPair (encPair (encList encUnary) encUnary) encUnary
  have hstep : ComputableInPolyTime (fun q : List ℕ × ℕ => followParent q.1 q.2)
      (encPair (encList encUnary) encUnary) encUnary :=
    listGetDWithInput (fst _ _) (snd _ _) 0
  have hB : PolyBounded (fun p => (E p).length)
      (fun p => p.1.2 + (encList encUnary p.1.1).length) :=
    PolyBounded.of_forall_le 2 1 fun p => by
      have hx : p.1.2 ≤ (E p).length := by
        have h := (length_le_encPair_right (encList encUnary) encUnary p.1).trans
          (length_le_encPair_left (encPair (encList encUnary) encUnary) encUnary p)
        simpa only [E, encUnary_apply, List.length_replicate] using h
      have hf : (encList encUnary p.1.1).length ≤ (E p).length :=
        (length_le_encPair_left (encList encUnary) encUnary p.1).trans
          (length_le_encPair_left (encPair (encList encUnary) encUnary) encUnary p)
      have := pow_one ((E p).length + 1)
      omega
  refine ComputableInPolyTime.iterateWith (by fun_prop) (by fun_prop) (by fun_prop) hstep hB
    fun p i _ => by
      simpa only [encUnary_apply, List.length_replicate] using
        (followParent_iterate_le p.1.1 p.1.2 i).trans
          (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

private theorem computableInPolyTime_hasCycleFromList :
    ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × ℕ => hasCycleFromList p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList encUnary)) encUnary) encBool := by
  unfold hasCycleFromList
  refine anyWithInput (range.comp (by fun_prop)) <|
    unary_beq' (computableInPolyTime_followParent_iterate.comp (show ComputableInPolyTime
      (fun q : ((ℕ × List ℕ) × ℕ) × ℕ => ((q.1.1.2, q.1.2), q.2 + 1)) _ _ by fun_prop))
      (by fun_prop)

private theorem computableInPolyTime_findCycleList :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List ℕ => findCycleList p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) (encList encUnary)) (encOption encUnary) := by
  unfold findCycleList
  exact findWithInput (range.comp (by fun_prop)) <|
    bool_and' (by fun_prop) (computableInPolyTime_hasCycleFromList.comp (show ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × List ℕ) × ℕ => ((q.1.1.1, q.1.2), q.2)) _ _ by fun_prop))

private theorem workVertexCount_polyTime :
    ComputableInPolyTime (fun w : ContractWork => w.state.adj.length) encContractWork encUnary :=
  (length_list (encList encBool)).comp
    (encContractState_adj_polyTime <| encContractWork_state_polyTime id')

private theorem computableInPolyTime_cycleMaskWork :
    ComputableInPolyTime
      (fun w : ContractWork => cycleMaskList w.state.adj.length w.parent w.rep)
      encContractWork (encList encBool) := by
  unfold cycleMaskList
  exact mapWithInput (range.comp workVertexCount_polyTime) <|
    anyWithInput (range.comp (workVertexCount_polyTime.comp (fst _ _))) <|
      unary_beq' (computableInPolyTime_followParent_iterate.comp (show ComputableInPolyTime
        (fun r : (ContractWork × ℕ) × ℕ => ((r.1.1.parent, r.1.1.rep), r.2)) _ _ by fun_prop))
        (by fun_prop)

private theorem computableInPolyTime_otherCycleCostWork :
    ComputableInPolyTime
      (fun w : ContractWork =>
        otherCycleCostList w.state.adj.length w.state.cost w.parent w.inCycle)
      encContractWork (encList encIntBin) := by
  unfold otherCycleCostList
  refine mapWithInput (range.comp workVertexCount_polyTime) ?_
  have hcond : ComputableInPolyTime
      (fun q : ContractWork × ℕ => q.1.inCycle.getD q.2 false)
      (encPair encContractWork encUnary) encBool := by fun_prop
  have hsum : ComputableInPolyTime
      (fun q : ContractWork × ℕ =>
        (((List.range q.1.state.adj.length).filter fun y =>
          q.1.inCycle.getD y false && (y != q.2)).map fun y =>
          costAt q.1.state.cost y (q.1.parent.getD y 0)).sum)
      (encPair encContractWork encUnary) encIntBin :=
    intBin_sum.comp <| mapWithInput
      (filterWithInput (range.comp (workVertexCount_polyTime.comp (fst _ _))) (by fun_prop))
      (by fun_prop)
  exact ite hcond hsum (const 0)

private theorem computableInPolyTime_bestEntryWork :
    ComputableInPolyTime
      (fun w : ContractWork =>
        bestEntryList w.state.adj.length w.state.adj w.state.cost w.inCycle)
      encContractWork (encList (encOption encUnary)) := by
  unfold bestEntryList
  refine mapWithInput (range.comp workVertexCount_polyTime) ?_
  refine computableInPolyTime_argMinRange (encPar := encPair encContractWork encUnary)
    (par := fun q => q) (bound := fun q => q.1.state.adj.length)
    (pred := fun par y => par.1.inCycle.getD y false && adjAt par.1.state.adj par.2 y)
    (key := fun par y => costAt par.1.state.cost par.2 y)
    (id' (encIn := encPair encContractWork encUnary)) (workVertexCount_polyTime.comp (fst _ _))
    (by fun_prop) (by fun_prop)

private theorem computableInPolyTime_bestExitWork :
    ComputableInPolyTime
      (fun w : ContractWork =>
        bestExitList w.state.adj.length w.state.adj w.state.cost w.inCycle w.other)
      encContractWork (encList (encOption encUnary)) := by
  unfold bestExitList
  refine mapWithInput (range.comp workVertexCount_polyTime) ?_
  refine computableInPolyTime_argMinRange (encPar := encPair encContractWork encUnary)
    (par := fun q => q) (bound := fun q => q.1.state.adj.length)
    (pred := fun par x => par.1.inCycle.getD x false && adjAt par.1.state.adj x par.2)
    (key := fun par x => costAt par.1.state.cost x par.2 + par.1.other.getD x 0)
    (id' (encIn := encPair encContractWork encUnary)) (workVertexCount_polyTime.comp (fst _ _))
    (by fun_prop) (by fun_prop)

private theorem computableInPolyTime_contractAdjWork :
    ComputableInPolyTime
      (fun w : ContractWork =>
        contractAdjList w.state.adj.length w.inCycle w.state.adj w.bestEntry w.bestExit
          w.rep w.state.root)
      encContractWork (encList (encList encBool)) := by
  unfold contractAdjList
  refine mapWithInput (range.comp workVertexCount_polyTime) ?_
  refine mapWithInput (range.comp (workVertexCount_polyTime.comp (fst _ _))) ?_
  fun_prop

private theorem computableInPolyTime_contractCostWork :
    ComputableInPolyTime
      (fun w : ContractWork =>
        contractCostList w.state.adj.length w.inCycle w.state.cost w.other w.bestEntry
          w.bestExit w.rep)
      encContractWork (encList (encList encIntBin)) := by
  unfold contractCostList
  refine mapWithInput (range.comp workVertexCount_polyTime) ?_
  refine mapWithInput (range.comp (workVertexCount_polyTime.comp (fst _ _))) ?_
  fun_prop

private theorem computableInPolyTime_contractFromParent :
    ComputableInPolyTime
      (fun p : (ContractState × List ℕ) × ℕ => contractFromParent p.1.1 p.1.2 p.2)
      (encPair (encPair encContractState (encList encUnary)) encUnary) encContractState := by
  have hw0 : ComputableInPolyTime
      (fun p : (ContractState × List ℕ) × ℕ => ContractWork.mk p.1.1 p.1.2 p.2 [] [] [] [])
      (encPair (encPair encContractState (encList encUnary)) encUnary) encContractWork := by
    polytime
  have hw1 : ComputableInPolyTime (fun w : ContractWork =>
      ContractWork.mk w.state w.parent w.rep (cycleMaskList w.state.adj.length w.parent w.rep)
        [] [] []) encContractWork encContractWork := by
    have _ := computableInPolyTime_cycleMaskWork; polytime
  have hw2 : ComputableInPolyTime (fun w : ContractWork =>
      ContractWork.mk w.state w.parent w.rep w.inCycle
        (otherCycleCostList w.state.adj.length w.state.cost w.parent w.inCycle) [] [])
      encContractWork encContractWork := by
    have _ := computableInPolyTime_otherCycleCostWork; polytime
  have hw3 : ComputableInPolyTime (fun w : ContractWork =>
      ContractWork.mk w.state w.parent w.rep w.inCycle w.other
        (bestEntryList w.state.adj.length w.state.adj w.state.cost w.inCycle) [])
      encContractWork encContractWork := by
    have _ := computableInPolyTime_bestEntryWork; polytime
  have hw4 : ComputableInPolyTime (fun w : ContractWork =>
      ContractWork.mk w.state w.parent w.rep w.inCycle w.other w.bestEntry
        (bestExitList w.state.adj.length w.state.adj w.state.cost w.inCycle w.other))
      encContractWork encContractWork := by
    have _ := computableInPolyTime_bestExitWork; polytime
  have hfin : ComputableInPolyTime (fun w : ContractWork =>
      ContractState.mk
        (contractAdjList w.state.adj.length w.inCycle w.state.adj w.bestEntry w.bestExit
          w.rep w.state.root)
        (contractCostList w.state.adj.length w.inCycle w.state.cost w.other w.bestEntry
          w.bestExit w.rep)
        w.state.root false none
        (⟨w.parent, w.inCycle, w.bestEntry, w.bestExit, w.rep⟩ :: w.state.stack))
      encContractWork encContractState := by
    have _ := computableInPolyTime_contractAdjWork
    have _ := computableInPolyTime_contractCostWork
    polytime
  simpa only [Function.comp_def, contractFromParent] using
    hfin.comp (hw4.comp (hw3.comp (hw2.comp (hw1.comp hw0))))

private theorem computableInPolyTime_contractStep :
    ComputableInPolyTime contractStep encContractState encContractState := by
  unfold contractStep
  refine ite (by fun_prop) id' <|
    optionElimWithInput computableInPolyTime_selectParentsState (by fun_prop) <|
      optionElimWithInput
        (computableInPolyTime_findCycleList.comp (by fun_prop :
          ComputableInPolyTime (fun q : ContractState × List ℕ => ((q.1.adj.length, q.1.root), q.2))
            _ _))
        (by fun_prop) computableInPolyTime_contractFromParent

private theorem computableInPolyTime_expandLevelList :
    ComputableInPolyTime (fun p : List ℕ × ContractLevel => expandLevelList p.2 p.1)
      (encPair (encList encUnary) encContractLevel) (encList encUnary) := by
  unfold expandLevelList
  refine mapWithInput (range.comp (by fun_prop)) <|
    ite (by fun_prop)
      (optionElimWithInput (by fun_prop) (by fun_prop)
        (ite (by fun_prop) (by fun_prop) (by fun_prop)))
      (ite (by fun_prop) (optionGetDWithInput (by fun_prop) (by fun_prop)) (by fun_prop))

/-! ### Bit-length invariant and polynomial-time certificate for `edmondsTableAuxList` -/

private theorem foldl_le_of_step {α : Type*} (step : ℕ → α → ℕ) (hstep : ∀ m x, m ≤ step m x) :
    ∀ (l : List α) (u : ℕ), u ≤ l.foldl step u
  | [], _ => le_rfl
  | x :: l, u => (hstep u x).trans (foldl_le_of_step step hstep l _)

private theorem maxNatAbsRow_le (row : List ℤ) :
    ∀ acc z, z ∈ row → z.natAbs ≤ row.foldl (fun m (x : ℤ) => max m x.natAbs) acc := by
  induction row with
  | nil => simp
  | cons a t ih =>
    intro acc z hz
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hz with rfl | ht
    · exact (le_max_right _ _).trans (foldl_le_of_step _ (fun m _ => le_max_left m _) t _)
    · exact ih _ _ ht

private theorem maxNatAbsTable_le (c : List (List ℤ)) :
    ∀ acc row z, row ∈ c → z ∈ row →
      z.natAbs ≤ c.foldl (fun m r => r.foldl (fun k (x : ℤ) => max k x.natAbs) m) acc := by
  induction c with
  | nil => simp
  | cons r rs ih =>
    intro acc row z hrow hz
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hrow with rfl | hrs
    · exact (maxNatAbsRow_le row acc z hz).trans
        (foldl_le_of_step _ (fun m y => foldl_le_of_step _ (fun k _ => le_max_left k _) y m) rs _)
    · exact ih _ row z hrs hz

private theorem maxNatAbsRow_size_le (B : ℕ) :
    ∀ (r : List ℤ), (∀ z ∈ r, z.natAbs.size ≤ B) →
      ∀ (acc : ℕ), acc.size ≤ B →
        (r.foldl (fun k (x : ℤ) => max k x.natAbs) acc).size ≤ B
  | [], _, _, hacc => hacc
  | a :: t, hrow, _, hacc =>
    maxNatAbsRow_size_le B t (fun z hz => hrow z (List.mem_cons_of_mem _ hz)) _
      (max_rec' (fun k : ℕ => k.size ≤ B) hacc (hrow a List.mem_cons_self))

private theorem maxNatAbsTable_size_le (c : List (List ℤ)) (B : ℕ)
    (hB : ∀ row ∈ c, ∀ z ∈ row, z.natAbs.size ≤ B) (acc : ℕ) (hacc : acc.size ≤ B) :
    (c.foldl (fun m r => r.foldl (fun k (x : ℤ) => max k x.natAbs) m) acc).size ≤ B := by
  induction c generalizing acc with
  | nil => exact hacc
  | cons r rs ih =>
    exact ih (fun row hr => hB row (List.mem_cons_of_mem _ hr)) _
      (maxNatAbsRow_size_le B r (hB r List.mem_cons_self) acc hacc)

private theorem costAt_natAbs_le {c : List (List ℤ)} {M : ℕ}
    (hc : ∀ row ∈ c, ∀ z ∈ row, z.natAbs ≤ M) (u w : ℕ) : (costAt c u w).natAbs ≤ M := by
  rcases List.getD_mem_or c u [] with hrow | hrow
  · rcases List.getD_mem_or (c.getD u []) w 0 with hz | hz
    · exact hc _ hrow _ hz
    · simp only [costAt, hz, Int.natAbs_zero, Nat.zero_le]
  · simp only [costAt, hrow, List.getD_nil, Int.natAbs_zero, Nat.zero_le]

private theorem list_sum_natAbs_le {M : ℕ} :
    ∀ l : List ℤ, (∀ z ∈ l, z.natAbs ≤ M) → l.sum.natAbs ≤ l.length * M
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    have ha := h a List.mem_cons_self
    have hl := list_sum_natAbs_le l fun z hz => h z (List.mem_cons_of_mem _ hz)
    omega

private theorem otherCycleCostList_natAbs_le {n : ℕ} {c : List (List ℤ)} {f : List ℕ}
    {inCycle : List Bool} {M : ℕ} (hc : ∀ row ∈ c, ∀ z ∈ row, z.natAbs ≤ M) (x : ℕ) :
    ((otherCycleCostList n c f inCycle).getD x 0).natAbs ≤ n * M := by
  have hlen : (otherCycleCostList n c f inCycle).length = n := by
    simp [otherCycleCostList]
  by_cases hx : x < n
  · rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hx)]
    unfold otherCycleCostList
    rw [List.getElem_map, List.getElem_range]
    split_ifs
    · have hs := list_sum_natAbs_le
          (((List.range n).filter fun z => inCycle.getD z false && (z != x)).map fun z =>
            costAt c z (f.getD z 0)) (fun v hv => by
        obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv
        exact costAt_natAbs_le hc z _)
      rw [List.length_map] at hs
      have hfl : ((List.range n).filter fun z => inCycle.getD z false && (z != x)).length ≤ n :=
        (List.length_filter_le _ _).trans (by simp)
      exact hs.trans (Nat.mul_le_mul_right M hfl)
    · exact Nat.zero_le _
  · rw [List.getD_eq_default _ _ (by rw [hlen]; exact Nat.le_of_not_lt hx)]
    exact Nat.zero_le _

private theorem contractCostList_natAbs_le {n : ℕ} {inCycle : List Bool} {c : List (List ℤ)}
    {other : List ℤ} {bEntry bExit : List (Option ℕ)} {x0 M : ℕ}
    (hc : ∀ row ∈ c, ∀ z ∈ row, z.natAbs ≤ M) (ho : ∀ x, (other.getD x 0).natAbs ≤ n * M) :
    ∀ row ∈ contractCostList n inCycle c other bEntry bExit x0,
      ∀ z ∈ row, z.natAbs ≤ (n + 1) * M := by
  intro row hrow z hz
  unfold contractCostList at hrow
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hz
  split_ifs
  · cases bExit.getD w none with
    | none => exact (costAt_natAbs_le hc u w).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))
    | some x =>
      exact (Int.natAbs_add_le _ _).trans
        (by simpa [Nat.succ_mul, Nat.add_comm] using
          Nat.add_le_add (costAt_natAbs_le hc x w) (ho x))
  · exact Nat.zero_le _
  · cases bEntry.getD u none with
    | none => exact (costAt_natAbs_le hc u w).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))
    | some y => exact (costAt_natAbs_le hc u y).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))
  · exact (costAt_natAbs_le hc u w).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))

private theorem encListBool_table_le (a : List (List Bool)) (n : ℕ)
    (h1 : a.length ≤ n) (h2 : ∀ r ∈ a, r.length ≤ n) :
    (encList (encList encBool) a).length ≤ n * (6 * n + 1) := by
  have hle := length_encList_le (encList encBool) a (b := 3 * n) fun r hr => by
    have hr1 := length_encList_le encBool r (b := 1) fun b _ => by simp [encBool_apply]
    have hr2 := h2 r hr
    nlinarith
  nlinarith

private theorem encListUnary_le (l : List ℕ) (n B : ℕ)
    (h1 : l.length ≤ n) (h2 : ∀ x ∈ l, x ≤ B) :
    (encList encUnary l).length ≤ n * (2 * B + 1) := by
  refine (length_encList_le encUnary l (b := B) fun x hx => ?_).trans
    (Nat.mul_le_mul_right _ h1)
  simpa [encUnary_apply] using h2 x hx

private theorem encListOptUnary_le (l : List (Option ℕ)) (n B : ℕ)
    (h1 : l.length ≤ n) (h2 : ∀ o ∈ l, ∀ x, o = some x → x ≤ B) :
    (encList (encOption encUnary) l).length ≤ n * (2 * (B + 1) + 1) :=
  (length_encList_le (encOption encUnary) l (b := B + 1) fun o ho =>
    length_encOption_unary_le (h2 o ho)).trans (Nat.mul_le_mul_right _ h1)

private structure StateBoundInv (x : TableAuxInput) (M₀ i : ℕ) (s : ContractState) : Prop where
  adj_len : s.adj.length = x.adj.length
  root_eq : s.root = x.root
  adj_code : (encList (encList encBool) s.adj).length ≤
    (encList (encList encBool) x.adj).length + x.adj.length * (6 * x.adj.length + 1)
  cost_abs : ∀ row ∈ s.cost, ∀ z ∈ row, z.natAbs ≤ (x.adj.length + 1) ^ i * M₀
  cost_rows : s.cost = x.cost ∨
    (s.cost.length = x.adj.length ∧ ∀ row ∈ s.cost, row.length = x.adj.length)
  result_bound : ∀ f, s.result = some f →
    f.length ≤ x.adj.length ∧ ∀ v ∈ f, v ≤ max x.root x.adj.length
  stack_len : s.stack.length ≤ i
  stack_bound : ∀ lvl ∈ s.stack,
    lvl.parent.length ≤ x.adj.length ∧ (∀ v ∈ lvl.parent, v ≤ max x.root x.adj.length) ∧
    lvl.inCycle.length ≤ x.adj.length ∧
    lvl.bestEntry.length ≤ x.adj.length ∧
    (∀ o ∈ lvl.bestEntry, ∀ v, o = some v → v ≤ x.adj.length) ∧
    lvl.bestExit.length ≤ x.adj.length ∧ (∀ o ∈ lvl.bestExit, ∀ v, o = some v → v ≤ x.adj.length) ∧
    lvl.rep ≤ x.adj.length

private theorem selectParentsList_bound (a : List (List Bool)) (c : List (List ℤ)) (r : ℕ)
    (f : List ℕ) (hf : selectParentsList a c r = some f) :
    f.length = a.length ∧ ∀ v ∈ f, v ≤ max r a.length := by
  unfold selectParentsList at hf; dsimp only at hf
  split_ifs at hf
  obtain rfl := Option.some_injective _ hf
  refine ⟨by simp, fun v hv => ?_⟩
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv
  obtain ⟨idx, -, rfl⟩ := List.mem_map.mp ho
  split_ifs
  · simp
  · cases harg : argMinRange a.length _ _ with
    | none => simp
    | some w =>
      exact (Nat.le_of_lt (foldl_argMinStep_lt _ _ a.length (List.range a.length)
        (fun _ hj => List.mem_range.mp hj) none (fun _ h => by simp at h) w harg)).trans
        (le_max_right _ _)

private theorem findCycleList_lt (n r : ℕ) (f : List ℕ) (x0 : ℕ)
    (h : findCycleList n r f = some x0) : x0 < n := by
  have hmem := List.mem_of_find?_eq_some h
  exact List.mem_range.mp hmem

/-- Shared bound for `bestEntryList` and `bestExitList`: a row of `n` arg-min lookups over
`List.range n` has length `n` and entries at most `n`. -/
private theorem argMinRangeList_bound (n : ℕ) (pred : ℕ → ℕ → Bool) (key : ℕ → ℕ → ℤ) :
    ((List.range n).map fun u => argMinRange n (pred u) (key u)).length = n ∧
      ∀ o ∈ (List.range n).map (fun u => argMinRange n (pred u) (key u)), ∀ v, o = some v →
        v ≤ n := by
  refine ⟨by simp, fun o ho v hv => ?_⟩
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp ho
  exact Nat.le_of_lt (foldl_argMinStep_lt _ _ n (List.range n)
    (fun j hj => List.mem_range.mp hj) none (fun _ h => by simp at h) v hv)

private theorem stateBoundInv_step (x : TableAuxInput) (M₀ i : ℕ) {s : ContractState}
    (hs : StateBoundInv x M₀ i s) :
    StateBoundInv x M₀ (i + 1) (contractStep s) := by
  have hmono : ∀ row ∈ s.cost, ∀ z ∈ row, z.natAbs ≤ (x.adj.length + 1) ^ (i + 1) * M₀ :=
    fun row hr z hz => (hs.cost_abs row hr z hz).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ i)))
  have hlen_le := hs.stack_len.trans (Nat.le_succ i)
  unfold contractStep
  split_ifs
  · exact ⟨hs.adj_len, hs.root_eq, hs.adj_code, hmono, hs.cost_rows, hs.result_bound,
      hlen_le, hs.stack_bound⟩
  · cases hsel : selectParentsList s.adj s.cost s.root with
    | none =>
      simp only [Option.elim_none]
      exact ⟨hs.adj_len, hs.root_eq, hs.adj_code, hmono, hs.cost_rows,
        fun _ h => by simp at h, hlen_le, hs.stack_bound⟩
    | some f =>
      have hf := selectParentsList_bound s.adj s.cost s.root f hsel
      rw [hs.adj_len, hs.root_eq] at hf
      cases hcyc : findCycleList s.adj.length s.root f with
      | none =>
        simp only [Option.elim_some, hcyc, Option.elim_none]
        exact ⟨hs.adj_len, hs.root_eq, hs.adj_code, hmono, hs.cost_rows, fun g hg =>
          Option.some_injective _ hg ▸ ⟨hf.1.le, hf.2⟩, hlen_le, hs.stack_bound⟩
      | some x0 =>
        have hx0 : x0 ≤ x.adj.length := Nat.le_of_lt (hs.adj_len ▸ findCycleList_lt _ _ _ _ hcyc)
        have hn : s.adj.length = x.adj.length := hs.adj_len
        simp only [Option.elim_some, hcyc, contractFromParent]
        have hbe := argMinRangeList_bound s.adj.length
          (fun u y => (cycleMaskList s.adj.length f x0).getD y false && adjAt s.adj u y)
          (fun u y => costAt s.cost u y)
        have hbx := argMinRangeList_bound s.adj.length
          (fun w y => (cycleMaskList s.adj.length f x0).getD y false && adjAt s.adj y w)
          (fun w y => costAt s.cost y w +
            (otherCycleCostList s.adj.length s.cost f (cycleMaskList s.adj.length f x0)).getD y 0)
        refine ⟨by simp [contractAdjList, hn], hs.root_eq,
          (encListBool_table_le _ x.adj.length (by simp [contractAdjList, hn]) fun r hr => by
            obtain ⟨_, -, rfl⟩ := List.mem_map.mp hr; simp [hn]).trans (Nat.le_add_left _ _),
          fun row hrow z hz => by
            simpa [hn, pow_succ', Nat.mul_assoc] using contractCostList_natAbs_le
              hs.cost_abs (otherCycleCostList_natAbs_le hs.cost_abs) row hrow z hz,
          Or.inr ⟨by simp [contractCostList, hn], fun row hr => by
            obtain ⟨_, -, rfl⟩ := List.mem_map.mp hr; simp [hn]⟩,
          fun _ h => by simp at h, Nat.succ_le_succ hs.stack_len, fun lvl hlvl => ?_⟩
        rcases List.mem_cons.mp hlvl with rfl | hlvl'
        · exact ⟨hf.1.le, hf.2, by simp [cycleMaskList, hn],
            hn ▸ hbe.1.le, fun o ho v hv => hn ▸ hbe.2 o ho v hv,
            hn ▸ hbx.1.le, fun o ho v hv => hn ▸ hbx.2 o ho v hv, hx0⟩
        · exact hs.stack_bound lvl hlvl'

private theorem stateBoundInv_iterate (x : TableAuxInput) :
    let M₀ := x.cost.foldl (fun m r => r.foldl (fun k (z : ℤ) => max k z.natAbs) m) 0
    ∀ i, StateBoundInv x M₀ i (contractStep^[i] ⟨x.adj, x.cost, x.root, false, none, []⟩)
  | 0 => by
    refine ⟨rfl, rfl, Nat.le_add_right _ _, fun row hr z hz => ?_, Or.inl rfl,
      fun _ h => by simp at h, le_rfl, fun _ h => by simp at h⟩
    simpa only [pow_zero, one_mul] using maxNatAbsTable_le x.cost 0 row z hr hz
  | i + 1 => by
    rw [Function.iterate_succ_apply']
    exact stateBoundInv_step x _ i (stateBoundInv_iterate x i)

private def tableAuxStateBound (L : ℕ) : ℕ :=
  let sAdj := L + L * (6 * L + 1)
  let sCost := L + L * (2 * (L * (2 * (L * (L + 1) + 1 + L + 1) + 1)) + 1)
  let sRes := 1 + L * (2 * L + 1)
  let sLvl := 2 * (L * (2 * L + 1)) + 1 + (2 * (3 * L) + 1 +
    (2 * (L * (2 * (L + 1) + 1)) + 1 + (2 * (L * (2 * (L + 1) + 1)) + 1 + L)))
  let sStack := L * (2 * sLvl + 1)
  2 * sAdj + 1 + (2 * sCost + 1 + (2 * L + 1 + (2 * 1 + 1 + (2 * sRes + 1 + sStack))))

private theorem length_encContractState_le (x : TableAuxInput) {i : ℕ} (hi : i ≤ x.fuel) :
    (encContractState (contractStep^[i] ⟨x.adj, x.cost, x.root, false, none, []⟩)).length ≤
      tableAuxStateBound (encTableAuxInput x).length := by
  set L := (encTableAuxInput x).length
  set M₀ := x.cost.foldl (fun m r => r.foldl (fun k (z : ℤ) => max k z.natAbs) m) 0
  have hinv := stateBoundInv_iterate x i
  have hfuel : x.fuel ≤ L := by
    simpa only [encUnary_apply, List.length_replicate] using encTableAuxInput_fuel_length_le x
  have hroot : x.root ≤ L := by
    simpa only [encUnary_apply, List.length_replicate] using encTableAuxInput_root_length_le x
  have hadj_in : (encList (encList encBool) x.adj).length ≤ L := encTableAuxInput_adj_length_le x
  have hcost_in : (encList (encList encIntBin) x.cost).length ≤ L :=
    encTableAuxInput_cost_length_le x
  have hn : x.adj.length ≤ L :=
    (SizedListEncoding.length_le (encA := encList encBool)
      (encL := encList (encList encBool)) x.adj).trans hadj_in
  have hM0_size : M₀.size ≤ L :=
    maxNatAbsTable_size_le x.cost L (fun row hrow z hz => by
      have h1 : (encIntBin z).length ≤ (encList encIntBin row).length :=
        SizedListEncoding.length_elem_le row z hz
      have h2 : (encList encIntBin row).length ≤ (encList (encList encIntBin) x.cost).length :=
        SizedListEncoding.length_elem_le x.cost row hrow
      rw [length_encIntBin] at h1; omega) 0 (by simp)
  set s := contractStep^[i] ⟨x.adj, x.cost, x.root, false, none, []⟩
  have hadj_code : (encList (encList encBool) s.adj).length ≤ L + L * (6 * L + 1) :=
    hinv.adj_code.trans (Nat.add_le_add hadj_in (Nat.mul_le_mul hn (by omega)))
  have hcost_code : (encList (encList encIntBin) s.cost).length ≤
      L + L * (2 * (L * (2 * (L * (L + 1) + 1 + L + 1) + 1)) + 1) := by
    rcases hinv.cost_rows with heq_cost | ⟨hrows_len, hrows_each⟩
    · exact heq_cost ▸ hcost_in.trans (Nat.le_add_right _ _)
    · refine ((length_encList_le (encList encIntBin) s.cost
          (b := L * (2 * (L * (L + 1) + 1 + L + 1) + 1)) fun row hrow =>
        (length_encList_le encIntBin row (b := L * (L + 1) + 1 + L + 1) fun z hz => by
          rw [length_encIntBin]
          have hs1 : z.natAbs.size ≤ ((x.adj.length + 1) ^ i * M₀).size :=
            Nat.size_le_size (hinv.cost_abs row hrow z hz)
          have hs2 : ((x.adj.length + 1) ^ i * M₀).size ≤
              ((x.adj.length + 1) ^ i).size + M₀.size := Nat.size_mul_le _ _
          have hs3 : ((x.adj.length + 1) ^ i).size ≤ i * (x.adj.length + 1).size + 1 :=
            Nat.size_pow_le _ _
          have hs4 : (x.adj.length + 1).size ≤ L + 1 := (Nat.size_le_self _).trans (by omega)
          have hmul : i * (x.adj.length + 1).size ≤ L * (L + 1) :=
            Nat.mul_le_mul (hi.trans hfuel) hs4
          omega).trans (Nat.mul_le_mul_right _ (hrows_each row hrow ▸ hn))).trans
        (Nat.mul_le_mul_right _ (hrows_len ▸ hn))).trans (Nat.le_add_left _ _)
  have hroot_code : (encUnary s.root).length ≤ L := by
    simpa [encUnary_apply, hinv.root_eq] using hroot
  have hdone_code : (encBool s.done).length = 1 := by simp [encBool_apply]
  have hres_code : (encOption (encList encUnary) s.result).length ≤ 1 + L * (2 * L + 1) := by
    cases hr : s.result with
    | none => simp
    | some f =>
      simp only [encOption_some, List.length_cons]
      have hf := hinv.result_bound f hr
      have hlen := encListUnary_le f L L (hf.1.trans hn) fun v hv =>
        (hf.2 v hv).trans (max_le hroot hn)
      omega
  have hstack_code : (encList encContractLevel s.stack).length ≤
      L * (2 * (2 * (L * (2 * L + 1)) + 1 + (2 * (3 * L) + 1 +
        (2 * (L * (2 * (L + 1) + 1)) + 1 +
        (2 * (L * (2 * (L + 1) + 1)) + 1 + L)))) + 1) := by
    refine (length_encList_le encContractLevel s.stack fun lvl hlvl => ?_).trans
      (Nat.mul_le_mul_right _ (hinv.stack_len.trans (hi.trans hfuel)))
    obtain ⟨hp1, hp2, hic, hbe1, hbe2, hbx1, hbx2, hrep⟩ := hinv.stack_bound lvl hlvl
    rw [encContractLevel_apply, length_encPair, length_encPair, length_encPair, length_encPair]
    have c1 := encListUnary_le lvl.parent L L (hp1.trans hn) fun v hv =>
      (hp2 v hv).trans (max_le hroot hn)
    have c2 : (encList encBool lvl.inCycle).length ≤ 3 * L :=
      (length_encList_le encBool lvl.inCycle (b := 1) fun _ _ => by simp [encBool_apply]).trans
        (by have := hic.trans hn; omega)
    have c3 := encListOptUnary_le lvl.bestEntry L L (hbe1.trans hn) fun o ho v hv =>
      (hbe2 o ho v hv).trans hn
    have c4 := encListOptUnary_le lvl.bestExit L L (hbx1.trans hn) fun o ho v hv =>
      (hbx2 o ho v hv).trans hn
    have c5 : (encUnary lvl.rep).length ≤ L := by simpa [encUnary_apply] using hrep.trans hn
    dsimp only; omega
  rw [encContractState_apply, length_encPair, length_encPair, length_encPair, length_encPair,
    length_encPair]
  dsimp only [tableAuxStateBound, encAdjTable, encIntTable, encParentOption] at *
  omega

private theorem expandLevelList_bound {n B : ℕ} {lvl : ContractLevel} {q : List ℕ}
    (hp : ∀ v ∈ lvl.parent, v ≤ B) (hic : lvl.inCycle.length ≤ n)
    (hbe : ∀ o ∈ lvl.bestEntry, ∀ v, o = some v → v ≤ B) (hnB : n ≤ B)
    (hq : ∀ v ∈ q, v ≤ B) :
    (expandLevelList lvl q).length ≤ n ∧ ∀ v ∈ expandLevelList lvl q, v ≤ B := by
  refine ⟨by simp [expandLevelList, hic], fun v hv => ?_⟩
  unfold expandLevelList at hv
  obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hv
  split_ifs
  · cases lvl.bestExit.getD (q.getD lvl.rep 0) none with
    | none => exact List.getD_le_of_forall_le hp idx
    | some _ =>
      dsimp only [Option.elim_some]
      split_ifs <;>
        [exact List.getD_le_of_forall_le hq lvl.rep; exact List.getD_le_of_forall_le hp idx]
  · rcases List.getD_mem_or lvl.bestEntry idx none with hmem | hdef
    · cases h : lvl.bestEntry.getD idx none with
      | none => exact (Nat.le_of_lt (lt_of_lt_of_le (List.mem_range.mp hidx) hic)).trans hnB
      | some y => exact hbe _ hmem y h
    · rw [hdef]; exact (Nat.le_of_lt (lt_of_lt_of_le (List.mem_range.mp hidx) hic)).trans hnB
  · exact List.getD_le_of_forall_le hq idx

private theorem foldl_expandLevelList_bound {n B : ℕ} (stack : List ContractLevel)
    (hstack : ∀ lvl ∈ stack, (∀ v ∈ lvl.parent, v ≤ B) ∧ lvl.inCycle.length ≤ n ∧
      (∀ o ∈ lvl.bestEntry, ∀ v, o = some v → v ≤ B))
    (hnB : n ≤ B) :
    ∀ (l : List ContractLevel), (∀ lvl ∈ l, lvl ∈ stack) → ∀ (q : List ℕ), (∀ v ∈ q, v ≤ B) →
      l = [] ∨ ((l.foldl (fun acc lvl => expandLevelList lvl acc) q).length ≤ n ∧
        ∀ v ∈ l.foldl (fun acc lvl => expandLevelList lvl acc) q, v ≤ B)
  | [], _, _, _ => Or.inl rfl
  | lvl :: ls, hl, q, hq => by
    obtain ⟨hp, hic, hbe⟩ := hstack lvl (hl lvl List.mem_cons_self)
    have hstep := expandLevelList_bound hp hic hbe hnB hq
    rcases ls with _ | ⟨lvl2, ls2⟩
    · exact Or.inr hstep
    · rcases foldl_expandLevelList_bound stack hstack hnB (lvl2 :: ls2)
        (fun m hm => hl m (List.mem_cons_of_mem _ hm)) (expandLevelList lvl q) hstep.2 with
        h | h
      · simp at h
      · exact Or.inr h

theorem computableInPolyTime_edmondsTableAuxList :
    ComputableInPolyTime
      (fun x : TableAuxInput => edmondsTableAuxList x.fuel x.root x.adj x.cost)
      encTableAuxInput encParentOption := by
  have hpoly : PolyBounded (fun x => (encTableAuxInput x).length)
      (fun x => tableAuxStateBound (encTableAuxInput x).length) :=
    PolyBounded.of_forall_le 1000 4 fun x => by
      set L := (encTableAuxInput x).length
      dsimp only [tableAuxStateBound]
      rw [show 1000 * (L + 1) ^ 4 =
        1000 + 4000 * L + 6000 * L ^ 2 + 4000 * L ^ 3 + 1000 * L ^ 4 by ring]
      ring_nf; omega
  have hiter : ComputableInPolyTime
      (fun x : TableAuxInput => contractStep^[x.fuel] ⟨x.adj, x.cost, x.root, false, none, []⟩)
      encTableAuxInput encContractState :=
    ComputableInPolyTime.iterate (by polytime) (by polytime)
      computableInPolyTime_contractStep hpoly (fun x _ hi => length_encContractState_le x hi)
  refine optionMapWithInput (by polytime) ?_
  have hB : PolyBounded (fun p : TableAuxInput × List ℕ =>
      (encPair encTableAuxInput (encList encUnary) p).length)
      (fun p => max (encList encUnary p.2).length
        ((encTableAuxInput p.1).length *
          (2 * ((encList encUnary p.2).length + (encTableAuxInput p.1).length) + 1))) :=
    PolyBounded.of_forall_le 4 2 fun p => by
      rw [length_encPair]
      set L := (encTableAuxInput p.1).length; set M := (encList encUnary p.2).length
      rcases le_total M (L * (2 * (M + L) + 1)) with h | h <;>
        [rw [max_eq_right h]; rw [max_eq_left h]] <;> nlinarith
  have hlist_f : ComputableInPolyTime
      (fun p : TableAuxInput × List ℕ =>
        (contractStep^[p.1.fuel] ⟨p.1.adj, p.1.cost, p.1.root, false, none, []⟩).stack)
      (encPair encTableAuxInput (encList encUnary)) (encList encContractLevel) := by
    have := hiter.comp (fst encTableAuxInput (encList encUnary)); polytime
  refine ComputableInPolyTime.foldl' (encA := encContractLevel) (encB := encList encUnary)
    (encL := encList encContractLevel)
    hlist_f (snd _ _) computableInPolyTime_expandLevelList hB fun p k _ => ?_
  set x := p.1; set base := p.2
  have hinv := stateBoundInv_iterate x x.fuel
  have hL_adj : x.adj.length ≤ (encTableAuxInput x).length :=
    (SizedListEncoding.length_le (encA := encList encBool)
      (encL := encList (encList encBool)) x.adj).trans (encTableAuxInput_adj_length_le x)
  have hL_root : x.root ≤ (encTableAuxInput x).length := by
    simpa only [encUnary_apply, List.length_replicate] using encTableAuxInput_root_length_le x
  set B_val := (encList encUnary base).length + (encTableAuxInput x).length
  rcases foldl_expandLevelList_bound (n := x.adj.length) (B := B_val) _ (fun lvl hlvl => by
      obtain ⟨_, hp2, hic, _, hbe2, _⟩ := hinv.stack_bound lvl hlvl
      exact ⟨fun v hv => (hp2 v hv).trans (max_le (by omega) (by omega)), hic,
        fun o ho v hv => (hbe2 o ho v hv).trans (by omega)⟩)
      (by omega) _ (fun _ hl => List.mem_of_mem_take hl) base (fun v hv => by
        have h : (encUnary v).length ≤ (encList encUnary base).length :=
          SizedListEncoding.length_elem_le base v hv
        simp only [encUnary_apply, List.length_replicate] at h; omega)
    with hnil | ⟨hlen, helem⟩
  · rw [hnil, List.foldl_nil]; exact le_max_left _ _
  · exact (encListUnary_le _ (encTableAuxInput x).length B_val (hlen.trans hL_adj) helem).trans
      (le_max_right _ _)

/-! ### Polynomial-time certificates for solvers and deciders -/

private theorem computableInPolyTime_rootInBounds :
    ComputableInPolyTime
      (fun inst : ArborescenceInstance => decide ((inst.root : ℤ) < (inst.adj.length : ℤ)))
      encArborescenceInstance encBool :=
  intBin_lt' (intBin_natCast.comp (by fun_prop))
    (intBin_natCast.comp (ComputableInPolyTime.unary_to_binary.comp (by fun_prop)))

private theorem computableInPolyTime_clampedRoot :
    ComputableInPolyTime clampedRoot encArborescenceInstance encUnary :=
  binary_to_unary_bounded
    (by unfold clampedRoot; exact ite computableInPolyTime_rootInBounds (by fun_prop) (const 0))
    (show ComputableInPolyTime (fun inst : ArborescenceInstance => inst.adj.length)
      encArborescenceInstance encUnary by fun_prop) fun inst => by
      unfold clampedRoot; split_ifs with h
      · exact Nat.le_of_lt (Int.ofNat_lt.mp (of_decide_eq_true h))
      · exact Nat.zero_le _

theorem computableInPolyTime_edmondsList :
    ComputableInPolyTime edmondsList encArborescenceInstance encParentOption := by
  have hcr := computableInPolyTime_clampedRoot
  unfold edmondsList
  exact ite computableInPolyTime_rootInBounds
    (computableInPolyTime_edmondsTableAuxList.comp (show ComputableInPolyTime
      (fun inst : ArborescenceInstance =>
        TableAuxInput.mk inst.adj.length (clampedRoot inst) inst.adj inst.cost)
      encArborescenceInstance encTableAuxInput by fun_prop)) (const none)

private theorem computableInPolyTime_transposeBoolTable :
    ComputableInPolyTime transposeBoolTable
      (encList (encList encBool)) (encList (encList encBool)) := by
  unfold transposeBoolTable
  exact mapWithInput (range.comp (by fun_prop)) <|
    mapWithInput (range.comp (by fun_prop)) (by fun_prop)

private theorem computableInPolyTime_transposeIntTable :
    ComputableInPolyTime
      (fun p : ℕ × List (List ℤ) => transposeIntTable p.1 p.2)
      (encPair encUnary (encList (encList encIntBin))) (encList (encList encIntBin)) := by
  unfold transposeIntTable
  exact mapWithInput (range.comp (by fun_prop)) <|
    mapWithInput (range.comp (by fun_prop)) <|
      computableInPolyTime_costAt' (by fun_prop) (by fun_prop) (by fun_prop)

theorem computableInPolyTime_edmondsOutList :
    ComputableInPolyTime edmondsOutList encArborescenceInstance encParentOption := by
  have hcr := computableInPolyTime_clampedRoot
  have htb : ComputableInPolyTime (fun inst : ArborescenceInstance => transposeBoolTable inst.adj)
      encArborescenceInstance (encList (encList encBool)) :=
    computableInPolyTime_transposeBoolTable.comp (by fun_prop)
  have hlen : ComputableInPolyTime (fun inst : ArborescenceInstance => inst.adj.length)
      encArborescenceInstance encUnary := by fun_prop
  have hcost : ComputableInPolyTime (fun inst : ArborescenceInstance => inst.cost)
      encArborescenceInstance (encList (encList encIntBin)) := by fun_prop
  have hti : ComputableInPolyTime
      (fun inst : ArborescenceInstance => transposeIntTable inst.adj.length inst.cost)
      encArborescenceInstance (encList (encList encIntBin)) :=
    computableInPolyTime_transposeIntTable.comp (hlen.prod hcost)
  have hin : ComputableInPolyTime
      (fun inst : ArborescenceInstance =>
        TableAuxInput.mk inst.adj.length (clampedRoot inst)
          (transposeBoolTable inst.adj) (transposeIntTable inst.adj.length inst.cost))
      encArborescenceInstance encTableAuxInput := by fun_prop
  unfold edmondsOutList
  exact ite computableInPolyTime_rootInBounds
    (computableInPolyTime_edmondsTableAuxList.comp hin) (const none)

private theorem computableInPolyTime_nonRootFilter :
    ComputableInPolyTime
      (fun q : ArborescenceDecInstance × List ℕ =>
        (List.range q.1.inst.adj.length).filter fun v => v != clampedRoot q.1.inst)
      (encPair encArborescenceDecInstance (encList encUnary)) (encList encUnary) :=
  filterWithInput (range.comp (by fun_prop)) <|
    bool_not.comp (unary_beq' (by fun_prop)
      (computableInPolyTime_clampedRoot.comp (by fun_prop)))

theorem computableInPolyTime_minArborescenceDecide :
    ComputableInPolyTime minArborescenceDecide encArborescenceDecInstance encBool :=
  optionElimWithInput (computableInPolyTime_edmondsList.comp (by fun_prop)) (const false) <|
    intBin_le' (intBin_sum.comp (mapWithInput computableInPolyTime_nonRootFilter (by fun_prop)))
      (by fun_prop)

theorem computableInPolyTime_minOutArborescenceDecide :
    ComputableInPolyTime minOutArborescenceDecide encArborescenceDecInstance encBool :=
  optionElimWithInput (computableInPolyTime_edmondsOutList.comp (by fun_prop)) (const false) <|
    intBin_le' (intBin_sum.comp (mapWithInput computableInPolyTime_nonRootFilter (by fun_prop)))
      (by fun_prop)

private theorem computableInPolyTime_superRootAdjList :
    ComputableInPolyTime superRootAdjList
      (encList (encList encBool)) (encList (encList encBool)) := by
  unfold superRootAdjList
  exact mapWithInput (range.comp (by fun_prop)) <|
    mapWithInput (range.comp (by fun_prop)) (by fun_prop)

private theorem computableInPolyTime_superRootWeightList :
    ComputableInPolyTime
      (fun p : ℕ × List (List ℤ) => superRootWeightList p.1 p.2)
      (encPair encUnary (encList (encList encIntBin))) (encList (encList encIntBin)) := by
  unfold superRootWeightList
  exact mapWithInput (range.comp (by fun_prop)) <|
    mapWithInput (range.comp (by fun_prop)) (by fun_prop)

theorem computableInPolyTime_optimumBranchingList :
    ComputableInPolyTime optimumBranchingList encBranchingInstance (encList encUnary) := by
  have hsa : ComputableInPolyTime (fun B : BranchingInstance => superRootAdjList B.adj)
      encBranchingInstance (encList (encList encBool)) :=
    computableInPolyTime_superRootAdjList.comp (by fun_prop)
  have hsw : ComputableInPolyTime
      (fun B : BranchingInstance => superRootWeightList B.adj.length B.weight)
      encBranchingInstance (encList (encList encIntBin)) :=
    computableInPolyTime_superRootWeightList.comp ((by fun_prop :
      ComputableInPolyTime (fun B : BranchingInstance => B.adj.length) _ encUnary).prod
        (by fun_prop :
          ComputableInPolyTime (fun B : BranchingInstance => B.weight) _ _))
  unfold optimumBranchingList
  exact optionElimWithInput
    (computableInPolyTime_edmondsTableAuxList.comp (show ComputableInPolyTime
      (fun B : BranchingInstance => TableAuxInput.mk (B.adj.length + 1) B.adj.length
        (superRootAdjList B.adj) (superRootWeightList B.adj.length B.weight))
      encBranchingInstance encTableAuxInput by fun_prop))
    (const []) <| mapWithInput (range.comp (by fun_prop)) <|
      ite (by fun_prop) (by fun_prop) (by fun_prop)

theorem computableInPolyTime_maxBranchingDecide :
    ComputableInPolyTime maxBranchingDecide encBranchingDecInstance encBool := by
  have hp : ComputableInPolyTime
      (fun q : BranchingDecInstance × ℕ => (optimumBranchingList q.1.inst).getD q.2 0)
      (encPair encBranchingDecInstance encUnary) encUnary :=
    listGetDWithInput (computableInPolyTime_optimumBranchingList.comp (by fun_prop)) (snd _ _) 0
  exact intBin_le' (by fun_prop) <| intBin_sum.comp <|
    mapWithInput
      (filterWithInput (range.comp (by fun_prop)) (bool_not.comp (unary_beq' hp (snd _ _))))
      (computableInPolyTime_costAt' (by fun_prop) hp (snd _ _))

/-! ### Correctness equivalence and `P` membership -/

private def runListAux (r : ℕ) : ℕ → List (List Bool) → List (List ℤ) → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, a, c =>
    match selectParentsList a c r with
    | none => none
    | some f =>
      match findCycleList a.length r f with
      | none => some f
      | some x0 =>
        let n := a.length
        let inCycle := cycleMaskList n f x0
        let other := otherCycleCostList n c f inCycle
        let bEntry := bestEntryList n a c inCycle
        let bExit := bestExitList n a c inCycle other
        let a' := contractAdjList n inCycle a bEntry bExit x0 r
        let c' := contractCostList n inCycle c other bEntry bExit x0
        let lvl : ContractLevel := ⟨f, inCycle, bEntry, bExit, x0⟩
        (runListAux r fuel a' c').map (expandLevelList lvl)

private theorem contractStep_of_done {s : ContractState} (h : s.done = true) :
    ∀ k, contractStep^[k] s = s
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply, show contractStep s = s by simp [contractStep, h]]
    exact contractStep_of_done h k

private theorem evalContractState_iterate (r : ℕ) :
    ∀ (fuel : ℕ) (a : List (List Bool)) (c : List (List ℤ)) (st : List ContractLevel),
      let final := contractStep^[fuel] ⟨a, c, r, false, none, st⟩
      final.result.map (fun base => final.stack.foldl (fun q lvl => expandLevelList lvl q) base) =
        (runListAux r fuel a c).map fun base => st.foldl (fun q lvl => expandLevelList lvl q) base
  | 0, _, _, _ => rfl
  | fuel + 1, a, c, st => by
    dsimp only
    rw [Function.iterate_succ_apply]
    cases hsel : selectParentsList a c r with
    | none =>
      rw [show contractStep ⟨a, c, r, false, none, st⟩ = ⟨a, c, r, true, none, st⟩ by
        simp [contractStep, hsel], contractStep_of_done rfl fuel]
      simp [runListAux, hsel]
    | some f =>
      cases hcyc : findCycleList a.length r f with
      | none =>
        rw [show contractStep ⟨a, c, r, false, none, st⟩ = ⟨a, c, r, true, some f, st⟩ by
          simp [contractStep, hsel, hcyc], contractStep_of_done rfl fuel]
        simp [runListAux, hsel, hcyc]
      | some x0 =>
        rw [show contractStep ⟨a, c, r, false, none, st⟩ =
          contractFromParent ⟨a, c, r, false, none, st⟩ f x0 by simp [contractStep, hsel, hcyc]]
        dsimp only [contractFromParent]
        set inC := cycleMaskList a.length f x0
        set other := otherCycleCostList a.length c f inC
        set bE := bestEntryList a.length a c inC
        set bX := bestExitList a.length a c inC other
        have ih := evalContractState_iterate r fuel
          (contractAdjList a.length inC a bE bX x0 r)
          (contractCostList a.length inC c other bE bX x0)
          (⟨f, inC, bE, bX, x0⟩ :: st)
        simpa [runListAux, hsel, hcyc, Option.map_map, Function.comp_def, List.foldl_cons] using ih

private theorem edmondsTableAuxList_eq_runListAux (fuel r : ℕ) (a : List (List Bool))
    (c : List (List ℤ)) :
    edmondsTableAuxList fuel r a c = runListAux r fuel a c := by
  have h := evalContractState_iterate r fuel a c []
  simpa [edmondsTableAuxList] using h

@[instance_reducible] private def localFinEnum (n : ℕ) : FinEnum (Fin n) :=
  ⟨n, Equiv.refl (Fin n)⟩

private theorem localFinEnum_toList (n : ℕ) :
    @FinEnum.toList (Fin n) (localFinEnum n) = List.finRange n := by
  change List.map (⇑(Equiv.refl (Fin n)).symm) (List.finRange n) = List.finRange n
  simp

private theorem map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

private theorem foldl_argMinStep_fin {n : ℕ} (pred : Fin n → Bool) (key : Fin n → ℤ)
    (predN : ℕ → Bool) (keyN : ℕ → ℤ)
    (hpred : ∀ w : Fin n, pred w = predN w.val)
    (hkey : ∀ w : Fin n, pred w = true → key w = keyN w.val) :
    ∀ (l : List (Fin n)) (acc : Option (Fin n)), (∀ a, acc = some a → pred a = true) →
      ((l.filter pred).foldl (List.argAux fun a b => key a < key b) acc).map Fin.val =
        (l.map Fin.val).foldl (argMinStep predN keyN) (acc.map Fin.val)
  | [], _, _ => rfl
  | x :: xs, acc, hacc => by
    simp only [List.map_cons, List.foldl_cons, argMinStep]
    by_cases hx : pred x = true
    · have hxn : predN x.val = true := (hpred x).symm.trans hx
      rw [List.filter_cons_of_pos (by simp [hx])]
      simp only [List.foldl_cons, hxn, ↓reduceIte]
      have hstep : (List.argAux (fun a b => key a < key b) acc x).map Fin.val =
          (acc.map Fin.val).elim (some x.val)
            (fun cur => if decide (keyN x.val < keyN cur) then some x.val else some cur) := by
        cases acc with
        | none => rfl
        | some a =>
          have ha := hacc a rfl
          simp only [List.argAux, Option.map_some, Option.elim_some, hkey x hx, hkey a ha]
          by_cases hlt : keyN x.val < keyN a.val <;> simp [hlt]
      have hacc' : ∀ b, List.argAux (fun a b => key a < key b) acc x = some b → pred b = true := by
        intro b hb
        cases acc with
        | none =>
          simp only [List.argAux, Option.some.injEq] at hb
          exact hb ▸ hx
        | some a =>
          simp only [List.argAux] at hb
          split_ifs at hb <;> simp only [Option.some.injEq] at hb
          · exact hb ▸ hx
          · exact hb ▸ hacc a rfl
      rw [foldl_argMinStep_fin pred key predN keyN hpred hkey xs _ hacc', hstep]
    · have hxf : pred x = false := Bool.eq_false_iff.mpr hx
      have hxn : predN x.val = false := (hpred x).symm.trans hxf
      rw [List.filter_cons_of_neg (by simp [hxf])]
      simp only [hxn, Bool.false_eq_true, ↓reduceIte]
      exact foldl_argMinStep_fin pred key predN keyN hpred hkey xs acc hacc

private theorem argMinRange_fin {n : ℕ} (pred : Fin n → Bool) (key : Fin n → ℤ)
    (predN : ℕ → Bool) (keyN : ℕ → ℤ)
    (hpred : ∀ w : Fin n, pred w = predN w.val)
    (hkey : ∀ w : Fin n, pred w = true → key w = keyN w.val) :
    (((List.finRange n).filter pred).argmin key).map Fin.val = argMinRange n predN keyN := by
  have h := foldl_argMinStep_fin pred key predN keyN hpred hkey (List.finRange n) none
    fun _ h => by simp at h
  simpa [List.argmin, argMinRange, map_val_finRange] using h

/-- Boolean adjacency relation on `Fin n × Fin n` read from row-major table `a`. -/
private def tableAdj (n : ℕ) (a : List (List Bool)) (u w : Fin n) : Bool :=
  adjAt a u.val w.val

private theorem decide_congr_inst {p : Prop} (d₁ d₂ : Decidable p) :
    @decide p d₁ = @decide p d₂ := by
  cases Subsingleton.elim d₁ d₂
  rfl

private theorem fin_val_beq {n : ℕ} (a b : Fin n) : (a.val == b.val) = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by simp [Fin.ext_iff])

private theorem sum_range_filter_map {n : ℕ} (p : ℕ → Bool) (g : ℕ → ℤ) :
    (((List.range n).filter p).map g).sum =
      ∑ v ∈ Finset.univ.filter (fun v : Fin n => p v.val = true), g v.val := by
  rw [← map_val_finRange n, List.filter_map, List.map_map]
  have hnd : ((List.finRange n).filter (p ∘ Fin.val)).Nodup := (List.nodup_finRange n).filter _
  change (((List.finRange n).filter (p ∘ Fin.val)).map (fun v : Fin n => g v.val)).sum = _
  rw [← List.sum_toFinset (fun v : Fin n => g v.val) hnd]
  congr 1; ext v; simp

private theorem selectParentsList_eq {n : ℕ} [FinEnum (Fin n)]
    (htl : FinEnum.toList (Fin n) = List.finRange n)
    {a : List (List Bool)} (ha : a.length = n) (c : List (List ℤ)) (r : Fin n) :
    match selectParentsList a c r.val with
    | none => ¬ ∀ v : Fin n, v ≠ r → candidates (tableAdj n a) v ≠ []
    | some f =>
      (∀ v : Fin n, v ≠ r → candidates (tableAdj n a) v ≠ []) ∧
        f.length = n ∧ (∀ i < n, f.getD i 0 < n) ∧
        ∀ v : Fin n, f.getD v.val 0 = (cheapestParent (tableAdj n a) (tableCost c) r v).val := by
  have hcand_eq (v : Fin n) :
      ((List.finRange n).filter fun w : Fin n => adjAt a v.val w.val && (w != v)) =
        candidates (tableAdj n a) v := by
    unfold candidates; rw [htl]
    refine List.filter_congr fun w _ => ?_
    simp only [tableAdj, _root_.bne, BEq.beq]
    exact congrArg (adjAt a v.val w.val && ·) (congrArg not (decide_congr_inst _ _))
  have harg (v : Fin n) :
      ((candidates (tableAdj n a) v).argmin (tableCost c v)).map Fin.val =
        argMinRange n (fun w => adjAt a v.val w && (w != v.val)) (fun w => costAt c v.val w) := by
    rw [← hcand_eq v]
    exact argMinRange_fin _ _ _ _
      (fun w => congrArg (_ && ·) (Bool.eq_iff_iff.mpr (by simp [Fin.ext_iff]))) (fun _ _ => rfl)
  unfold selectParentsList; dsimp only; rw [ha]
  let fopt (v : ℕ) := if v == r.val then some r.val
    else argMinRange n (fun w => adjAt a v w && (w != v)) (fun w => costAt c v w)
  have hfopt (v : Fin n) : fopt v.val =
      if v = r then some r.val
      else ((candidates (tableAdj n a) v).argmin (tableCost c v)).map Fin.val := by
    simp only [fopt, fin_val_beq, ← harg v]; split_ifs <;> simp_all
  have hall_iff : ((List.range n).map fopt).all Option.isSome = true ↔
      ∀ v : Fin n, v ≠ r → candidates (tableAdj n a) v ≠ [] := by
    simp only [List.all_eq_true, List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    refine ⟨fun h v hvr hnil => ?_, fun h k hk => ?_⟩
    · have := h v.val v.isLt; rw [hfopt v, ite_eq_right (fun e => hvr e),
        hnil] at this; simp at this
    · rw [hfopt ⟨k, hk⟩]; by_cases hvr : (⟨k, hk⟩ : Fin n) = r
      · simp [hvr]
      · obtain ⟨m, hm⟩ := List.exists_argmin_eq_some (f := tableCost c ⟨k, hk⟩) (h ⟨k, hk⟩ hvr)
        simp [hvr, hm]
  split_ifs with hall
  · have hcond := hall_iff.mp hall
    have hval (v : Fin n) : (((List.range n).map fopt).map fun o => o.getD 0).getD v.val 0 =
        (cheapestParent (tableAdj n a) (tableCost c) r v).val := by
      rw [List.map_map, List.getD_map_range _ _ v.isLt]; dsimp only [Function.comp_apply]
      rw [hfopt v]; unfold cheapestParent; by_cases hvr : v = r
      · simp [hvr]
      · obtain ⟨m, hm⟩ := List.exists_argmin_eq_some (f := tableCost c v) (hcond v hvr)
        simp [hvr, hm]
    exact ⟨hcond, by simp, fun i hi => by rw [hval ⟨i, hi⟩]; exact Fin.isLt _, hval⟩
  · exact fun h => hall (hall_iff.mpr h)

private theorem followParent_iterate_eq {n : ℕ} (f : List ℕ) (fV : Fin n → Fin n)
    (hf : ∀ v : Fin n, f.getD v.val 0 = (fV v).val) (v : Fin n) :
    ∀ k, (followParent f)^[k] v.val = (fV^[k] v).val
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      followParent_iterate_eq f fV hf v k, followParent, hf]

private theorem findCycleList_eq {n : ℕ} [FinEnum (Fin n)]
    (htl : FinEnum.toList (Fin n) = List.finRange n)
    (hcard : FinEnum.card (Fin n) = n)
    (f : List ℕ) (fV : Fin n → Fin n) (hf : ∀ v : Fin n, f.getD v.val 0 = (fV v).val) (r : Fin n) :
    findCycleList n r.val f = (findCycle r fV).map Fin.val := by
  unfold findCycleList findCycle
  rw [htl, ← map_val_finRange n, List.find?_map]
  congr 1; refine congrArg (fun p => (List.finRange n).find? p) (funext fun x => ?_)
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, hasCycleFromList, Bool.and_eq_true, bne_iff_ne,
    List.any_eq_true, List.mem_range, beq_iff_eq, hcard, Fin.ext_iff, ne_eq]
  simp only [followParent_iterate_eq f fV hf x]

private theorem finset_erase_eq_of_dec {α : Type*} (d₁ d₂ : DecidableEq α) (s : Finset α)
    (a : α) : @Finset.erase α d₁ s a = @Finset.erase α d₂ s a := by
  cases Subsingleton.elim d₁ d₂; rfl

private theorem cycleMaskList_eq {n : ℕ} [FinEnum (Fin n)]
    (hcard : FinEnum.card (Fin n) = n)
    (f : List ℕ) (fV : Fin n → Fin n) (hf : ∀ v : Fin n, f.getD v.val 0 = (fV v).val)
    (x0 y : Fin n) :
    (cycleMaskList n f x0.val).getD y.val false = true ↔ y ∈ cycleOf fV x0 := by
  unfold cycleMaskList
  rw [List.getD_map_range _ _ y.isLt, List.any_eq_true, mem_cycleOf]
  simp only [List.mem_range, beq_iff_eq, hcard, Fin.ext_iff, followParent_iterate_eq f fV hf x0]

private theorem otherCycleCostList_eq {n : ℕ} (c : List (List ℤ)) (f : List ℕ) (fV : Fin n → Fin n)
    (inCycle : List Bool) (C : Finset (Fin n))
    (hf : ∀ v : Fin n, f.getD v.val 0 = (fV v).val)
    (hmask : ∀ y : Fin n, inCycle.getD y.val false = true ↔ y ∈ C)
    {x : Fin n} (hx : x ∈ C) :
    (otherCycleCostList n c f inCycle).getD x.val 0 = ∑ y ∈ C.erase x, tableCost c y (fV y) := by
  unfold otherCycleCostList
  rw [List.getD_map_range _ _ x.isLt, (hmask x).mpr hx]
  simp only [↓reduceIte, sum_range_filter_map]
  refine Finset.sum_congr (by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, bne_iff_ne,
      hmask, Finset.mem_erase, ne_eq, Fin.ext_iff, and_comm]) fun y _ => by
    simp only [tableCost, hf y]

private theorem contractAdjList_eq {n : ℕ} [FinEnum (Fin n)]
    (htl : FinEnum.toList (Fin n) = List.finRange n)
    {a : List (List Bool)} {inCycle : List Bool} {bEntry bExit : List (Option ℕ)}
    {C : Finset (Fin n)} {x0 r : Fin n}
    (hin : ∀ y : Fin n, inCycle.getD y.val false = decide (y ∈ C))
    (hbe_some : ∀ u : Fin n, (bEntry.getD u.val none).isSome =
      (List.finRange n).any fun y => decide (y ∈ C) && tableAdj n a u y)
    (hbx_some : ∀ w : Fin n, (bExit.getD w.val none).isSome =
      (List.finRange n).any fun x => decide (x ∈ C) && tableAdj n a x w) :
    tableAdj n (contractAdjList n inCycle a bEntry bExit x0.val r.val) =
      contractAdj (tableAdj n a) C x0 r := by
  funext u w
  change adjAt (contractAdjList n inCycle a bEntry bExit x0.val r.val) u.val w.val =
    contractAdj (tableAdj n a) C x0 r u w
  unfold adjAt contractAdjList contractAdj
  rw [List.getD_map_range _ _ u.isLt, List.getD_map_range _ _ w.isLt,
    htl, hin u, hin w, fin_val_beq, fin_val_beq, fin_val_beq, hbx_some w, hbe_some u]
  have dec_congr (f : Fin n → Bool) :
      (List.finRange n).any (fun y => decide (y ∈ C) && f y) =
        (List.finRange n).any
          (fun y => @decide (y ∈ C) (@Finset.decidableMem _ (fun a b => FinEnum.decEq a b) y C) &&
            f y) :=
    congrArg _ (funext fun y => congrArg (· && f y) (decide_congr_inst _ _))
  by_cases huC : u ∈ C <;> by_cases hwC : w ∈ C
  · simp only [huC, hwC, decide_true, ↓reduceIte]
    by_cases hux : u = x0 <;> simp [hux]
  · simp only [huC, hwC, decide_true, decide_false, Bool.not_false, Bool.true_and, ↓reduceIte]
    by_cases hux : u = x0
    · simp only [hux, decide_true, ↓reduceIte, not_false_eq_true, Bool.true_and]
      exact dec_congr _
    · simp [hux]
  · simp only [huC, hwC, decide_false, decide_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hwx : w = x0
    · simp only [hwx, decide_true, Bool.true_and]
      exact dec_congr _
    · simp [hwx]
  · simp [huC, hwC, tableAdj]

private theorem contractCostList_eq {n : ℕ} [FinEnum (Fin n)]
    {a : List (List Bool)} {c : List (List ℤ)} {inCycle : List Bool} {other : List ℤ}
    {bEntry bExit : List (Option ℕ)} {fV : Fin n → Fin n} {C : Finset (Fin n)} {x0 : Fin n}
    (hin : ∀ y : Fin n, inCycle.getD y.val false = decide (y ∈ C))
    (hother : ∀ {x : Fin n}, x ∈ C → other.getD x.val 0 = ∑ y ∈ C.erase x, tableCost c y (fV y))
    (hbe : ∀ u : Fin n, bEntry.getD u.val none =
      (bestEntry (tableAdj n a) (tableCost c) C u).map Fin.val)
    (hbx : ∀ w : Fin n, bExit.getD w.val none =
      (bestExit (tableAdj n a) (tableCost c) fV C w).map Fin.val) :
    tableCost (contractCostList n inCycle c other bEntry bExit x0.val) =
      contractCost (tableAdj n a) (tableCost c) fV C x0 := by
  funext u w
  change costAt (contractCostList n inCycle c other bEntry bExit x0.val) u.val w.val =
    contractCost (tableAdj n a) (tableCost c) fV C x0 u w
  unfold costAt contractCostList contractCost
  rw [List.getD_map_range _ _ u.isLt, List.getD_map_range _ _ w.isLt,
    hin u, fin_val_beq, fin_val_beq]
  by_cases huC : u ∈ C
  · simp only [huC, decide_true, ↓reduceIte]
    by_cases hux : u = x0
    · simp only [hux, decide_true, ↓reduceIte, hbx w]
      cases hbo : bestExit (tableAdj n a) (tableCost c) fV C w with
      | none => rfl
      | some x =>
        have hxC : x ∈ C := by
          have hm := (List.mem_filter.mp (List.argmin_mem hbo)).2
          simpa using (Bool.and_eq_true _ _ |>.mp hm).1
        simp only [Option.map_some, Option.elim_some, exitCost, tableCost, hother hxC,
          finset_erase_eq_of_dec (instDecidableEqFin n) (fun a b => FinEnum.decEq a b) C x]
    · simp [hux]
  · simp only [huC, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hwx : w = x0
    · simp only [hwx, decide_true, ↓reduceIte, hbe u]
      cases bestEntry (tableAdj n a) (tableCost c) C u <;> rfl
    · simp [hwx, tableCost]

private theorem expandLevelList_eq {n : ℕ} [FinEnum (Fin n)]
    {a : List (List Bool)} {c : List (List ℤ)} {f qL : List ℕ} {inCycle : List Bool}
    {bEntry bExit : List (Option ℕ)} {fV qV : Fin n → Fin n} {C : Finset (Fin n)} {x0 : Fin n}
    (hic_len : inCycle.length = n)
    (hin : ∀ y : Fin n, inCycle.getD y.val false = decide (y ∈ C))
    (hf : ∀ v : Fin n, f.getD v.val 0 = (fV v).val)
    (hq : ∀ v : Fin n, qL.getD v.val 0 = (qV v).val)
    (hbe : ∀ u : Fin n, bEntry.getD u.val none =
      (bestEntry (tableAdj n a) (tableCost c) C u).map Fin.val)
    (hbx : ∀ w : Fin n, bExit.getD w.val none =
      (bestExit (tableAdj n a) (tableCost c) fV C w).map Fin.val) :
    ∀ v : Fin n, (expandLevelList ⟨f, inCycle, bEntry, bExit, x0.val⟩ qL).getD v.val 0 =
      (expandParent (tableAdj n a) (tableCost c) fV C x0 qV v).val := by
  intro v
  unfold expandLevelList expandParent
  rw [List.getD_map_range _ _ (hic_len.symm ▸ v.isLt)]
  dsimp only
  rw [hin v, hq x0, hq v, hbx (qV x0), fin_val_beq (qV v) x0]
  by_cases hvC : v ∈ C
  · simp only [hvC, decide_true, ↓reduceIte]
    cases bestExit (tableAdj n a) (tableCost c) fV C (qV x0) with
    | none => exact hf v
    | some x =>
      simp only [Option.map_some, Option.elim_some, fin_val_beq v x]
      by_cases hvx : v = x
      · simp [hvx]
      · simp only [hvx, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hf v
  · simp only [hvC, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hqvx : qV v = x0
    · simp only [hqvx, decide_true, ↓reduceIte, hbe v]
      cases bestEntry (tableAdj n a) (tableCost c) C v <;> rfl
    · simp [hqvx]

private theorem runListAux_eq_edmondsAux {n : ℕ} [FinEnum (Fin n)]
    (htl : FinEnum.toList (Fin n) = List.finRange n)
    (hcard : FinEnum.card (Fin n) = n) (r : Fin n) :
    ∀ (fuel : ℕ) (a : List (List Bool)) (c : List (List ℤ)), a.length = n →
      match runListAux r.val fuel a c,
          edmondsAux r fuel (tableAdj n a) (tableCost c) with
      | none, none => True
      | some pL, some pV =>
        pL.length = n ∧ ∀ v : Fin n, pL.getD v.val 0 = (pV v).val
      | _, _ => False
  | 0, _, _, _ => trivial
  | fuel + 1, a, c, ha_len => by
    have hsel := selectParentsList_eq htl ha_len c r
    unfold runListAux edmondsAux
    cases hselL : selectParentsList a c r.val with
    | none => rw [hselL] at hsel; dsimp only at hsel; simp only [hsel, ↓reduceIte]
    | some f =>
      rw [hselL] at hsel; obtain ⟨hcond, hf_len, _, hf_eq⟩ := hsel
      set fV := cheapestParent (tableAdj n a) (tableCost c) r
      split_ifs; simp only [ha_len]
      have hcyc := findCycleList_eq htl hcard f fV hf_eq r
      cases hcycL : findCycleList n r.val f with
      | none =>
        rw [hcycL] at hcyc
        have hcycV : findCycle r fV = none := by cases h : findCycle r fV <;> simp_all
        rw [hcycV]; exact ⟨hf_len, hf_eq⟩
      | some x0N =>
        rw [hcycL] at hcyc
        obtain ⟨x0, hx0V, rfl⟩ : ∃ x0 : Fin n, findCycle r fV = some x0 ∧ x0.val = x0N := by
          cases h : findCycle r fV <;> simp_all
        rw [hx0V]; dsimp only
        set C := cycleOf fV x0
        set inCycle := cycleMaskList n f x0.val
        set other := otherCycleCostList n c f inCycle
        set bEntry := bestEntryList n a c inCycle
        set bExit := bestExitList n a c inCycle other
        set a' := contractAdjList n inCycle a bEntry bExit x0.val r.val
        set c' := contractCostList n inCycle c other bEntry bExit x0.val
        have hmask (y : Fin n) : inCycle.getD y.val false = true ↔ y ∈ C :=
          cycleMaskList_eq hcard f fV hf_eq x0 y
        have hin (y : Fin n) : inCycle.getD y.val false = decide (y ∈ C) :=
          Bool.eq_iff_iff.mpr (by simpa using hmask y)
        have hother {x : Fin n} (hx : x ∈ C) :
            other.getD x.val 0 = ∑ y ∈ C.erase x, tableCost c y (fV y) :=
          otherCycleCostList_eq c f fV inCycle C hf_eq hmask hx
        have hbe (u : Fin n) :
            bEntry.getD u.val none = (bestEntry (tableAdj n a) (tableCost c) C u).map Fin.val := by
          unfold bEntry bestEntryList bestEntry
          rw [List.getD_map_range _ _ u.isLt, htl]
          exact (argMinRange_fin _ _ _ _ (fun y => by
            rw [tableAdj, hin]; exact congrArg (· && _) (decide_congr_inst _ _))
            (fun _ _ => rfl)).symm
        have hbx (w : Fin n) :
            bExit.getD w.val none =
              (bestExit (tableAdj n a) (tableCost c) fV C w).map Fin.val := by
          unfold bExit bestExitList bestExit
          rw [List.getD_map_range _ _ w.isLt, htl]
          refine (argMinRange_fin _ _ _ _ (fun x => by
            rw [tableAdj, hin]; exact congrArg (· && _) (decide_congr_inst _ _))
            fun x hx => ?_).symm
          have hxC : x ∈ C := by
            have h := (Bool.and_eq_true _ _ |>.mp hx).1
            rw [decide_congr_inst _ inferInstance] at h; exact of_decide_eq_true h
          simp only [exitCost, tableCost, hother hxC,
            finset_erase_eq_of_dec _ (instDecidableEqFin n) C x]
        have isSome_argmin (adj : Fin n → Bool) (key : Fin n → ℤ) (o : Option ℕ)
            (ho : o = (((FinEnum.toList (Fin n)).filter fun y =>
                @decide (y ∈ C) (@Finset.decidableMem _ (fun a b => FinEnum.decEq a b) y C) &&
                  adj y).argmin key).map Fin.val) :
            o.isSome = (List.finRange n).any fun y => decide (y ∈ C) && adj y := by
          rw [ho, Option.isSome_map, htl, List.isSome_argmin_filter]
          exact congrArg _ (funext fun y => congrArg (· && adj y) (decide_congr_inst _ _))
        have hih := runListAux_eq_edmondsAux htl hcard r fuel a' c' (by simp [a', contractAdjList])
        rw [contractAdjList_eq htl hin
            (fun u => isSome_argmin (tableAdj n a u) _ _ (hbe u))
            (fun w => isSome_argmin (fun x => tableAdj n a x w) _ _ (hbx w)),
          contractCostList_eq hin hother hbe hbx] at hih
        cases hrL : runListAux r.val fuel a' c' <;>
          cases hrV : edmondsAux r fuel (contractAdj (tableAdj n a) C x0 r)
            (contractCost (tableAdj n a) (tableCost c) fV C x0) <;>
          simp only [hrL, hrV] at hih ⊢
        · simp only [Option.map_none]
        · exact ⟨by simp [expandLevelList, inCycle, cycleMaskList],
            expandLevelList_eq (by simp [inCycle, cycleMaskList]) hin hf_eq hih.2 hbe hbx⟩

private theorem arcCost_parentDigraph_eq_sum_range {n : ℕ} {c : Fin n → Fin n → ℤ}
    {cL : ℕ → ℕ → ℤ} (hc : ∀ u w : Fin n, c u w = cL u.val w.val)
    (r : Fin n) (p : Fin n → Fin n) (pL : List ℕ)
    (hp : ∀ v : Fin n, pL.getD v.val 0 = (p v).val) :
    arcCost (Digraph.parentDigraph r p) c =
      (((List.range n).filter fun v => v != r.val).map fun v => cL v (pL.getD v 0)).sum := by
  rw [arcCost_parentDigraph, sum_range_filter_map]
  refine Finset.sum_congr (by ext v; simp [Fin.ext_iff]) fun v _ => by rw [hc, hp v]

/-- Shared core of the bounded-cost decision procedures: a list run `o` that matches a solver
output `oV` satisfying the Chu–Liu/Edmonds specification on `G` decides whether `G` has a
spanning in-arborescence rooted at `r` of cost at most `θ`. -/
private theorem elim_decide_iff_of_spec {n : ℕ} {fi : Fintype (Fin n)}
    {de : DecidableEq (Fin n)} {G : Digraph (Fin n)}
    {c : Fin n → Fin n → ℤ} {r : Fin n} {cL : ℕ → ℕ → ℤ}
    (hc : ∀ u w : Fin n, c u w = cL u.val w.val) {o : Option (List ℕ)}
    {oV : Option (Fin n → Fin n)}
    (ho : match o, oV with
      | none, none => True
      | some pL, some pV => pL.length = n ∧ ∀ v : Fin n, pL.getD v.val 0 = (pV v).val
      | _, _ => False)
    (hspec : (∀ p, oV = some p → IsInArborescenceParent G.Adj r p ∧
        ∀ t, IsInArborescenceParent G.Adj r t →
          @parentCost _ _ fi de _ c r p ≤ @parentCost _ _ fi de _ c r t) ∧
      (oV = none → ∀ t, ¬ IsInArborescenceParent G.Adj r t)) (θ : ℤ) :
    o.elim false (fun pL => decide ((((List.range n).filter fun v => v != r.val).map fun v =>
        cL v (pL.getD v 0)).sum ≤ θ)) = true ↔
      ∃ T : Digraph (Fin n), T.IsInArborescence r ∧ T ≤ G ∧
        @arcCost (Fin n) ℤ (Fin.fintype n) _ T (Classical.decRel _) c ≤ θ := by
  have hcost (t : Fin n → Fin n) : @parentCost _ _ fi de _ c r t =
      @arcCost (Fin n) ℤ (Fin.fintype n) _ (Digraph.parentDigraph r t) (Classical.decRel _) c :=
    (@arcCost_parentDigraph _ _ fi de _ r t c).symm.trans (arcCost_congr _ _ _ _ rfl c)
  cases o <;> cases oV <;> simp only at ho
  · simp only [Option.elim_none, Bool.false_eq_true, false_iff, not_exists]
    rintro T ⟨hT, hTG, -⟩
    obtain ⟨t, htr, rfl⟩ := hT.exists_parentDigraph_eq
    exact hspec.2 rfl t ((isInArborescenceParent_iff htr).mpr ⟨hT, hTG⟩)
  · rename_i pL p
    obtain ⟨hp, hmin⟩ := hspec.1 p rfl
    rw [Option.elim_some, decide_eq_true_eq, ← arcCost_parentDigraph_eq_sum_range hc r p pL ho.2,
      arcCost_congr _ (Fin.fintype n) _ (Classical.decRel _) rfl c]
    obtain ⟨hT, hTG⟩ := (isInArborescenceParent_iff hp.root).mp hp
    refine ⟨fun hle => ⟨_, hT, hTG, hle⟩, fun ⟨T, hT', hTG', hle⟩ => ?_⟩
    obtain ⟨t, htr, rfl⟩ := hT'.exists_parentDigraph_eq
    have h := hmin t ((isInArborescenceParent_iff htr).mpr ⟨hT', hTG'⟩)
    rw [hcost, hcost] at h
    exact h.trans hle

/-- `adjAt a` as the Boolean form of a relation `R` that it decides. -/
private theorem tableAdj_eq_decide {n : ℕ} {a : List (List Bool)} {R : Fin n → Fin n → Prop}
    [DecidableRel R] (h : ∀ u w, R u w ↔ adjAt a u.val w.val = true) :
    tableAdj n a = fun u w => decide (R u w) := by
  funext u w
  simp [tableAdj, h]

theorem minArborescenceDecide_eq_true_iff (d : ArborescenceDecInstance) :
    minArborescenceDecide d = true ↔ d ∈ minArborescenceDec := by
  unfold minArborescenceDecide minArborescenceDec edmondsList clampedRoot
  by_cases hr : d.inst.root < d.inst.adj.length
  · let _ := localFinEnum d.inst.adj.length
    have h := runListAux_eq_edmondsAux (localFinEnum_toList _) rfl ⟨d.inst.root, hr⟩
      d.inst.adj.length d.inst.adj d.inst.cost rfl
    rw [tableAdj_eq_decide (R := (tableDigraph d.inst.adj).Adj) fun _ _ => Iff.rfl] at h
    simp only [show ((d.inst.root : ℤ) < d.inst.adj.length) by omega, decide_true, ↓reduceIte,
      edmondsTableAuxList_eq_runListAux, Set.mem_ofPred_eq, exists_prop_of_true hr]
    exact elim_decide_iff_of_spec (c := tableCost d.inst.cost) (cL := costAt d.inst.cost)
      (fun _ _ => rfl) h (edmonds_spec (r := (⟨d.inst.root, hr⟩ : Fin d.inst.adj.length))) _
  · simp [hr]

theorem minArborescenceDec_mem_P :
    minArborescenceDec ∈ Cslib.Complexity.P encArborescenceDecInstance :=
  ⟨minArborescenceDecide, computableInPolyTime_minArborescenceDecide,
    fun d => (minArborescenceDecide_eq_true_iff d).symm⟩

private theorem transposeBoolTable_adj {a : List (List Bool)} {n : ℕ} (ha : a.length = n)
    (u w : Fin n) : tableAdj n (transposeBoolTable a) u w = tableAdj n a w u := by
  have hu : u.val < a.length := ha.symm ▸ u.isLt
  have hw : w.val < a.length := ha.symm ▸ w.isLt
  unfold tableAdj adjAt transposeBoolTable
  rw [List.getD_map_range _ _ hu, List.getD_map_range _ _ hw]
  rfl

private theorem transposeIntTable_cost {n : ℕ} (c : List (List ℤ)) (u w : Fin n) :
    tableCost (transposeIntTable n c) u w = tableCost c w u := by
  unfold tableCost costAt transposeIntTable
  rw [List.getD_map_range _ _ u.isLt, List.getD_map_range _ _ w.isLt]
  rfl

private theorem arcCost_reverse {V β : Type*} [Fintype V] [AddCommMonoid β]
    (T : Digraph V) [DecidableRel T.Adj] [DecidableRel T.reverse.Adj] (c : V → V → β) :
    arcCost T.reverse (fun u w => c w u) = arcCost T c := by
  unfold arcCost
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => by
    simp [Digraph.reverse_adj]

theorem minOutArborescenceDecide_eq_true_iff (d : ArborescenceDecInstance) :
    minOutArborescenceDecide d = true ↔ d ∈ minOutArborescenceDec := by
  unfold minOutArborescenceDecide minOutArborescenceDec edmondsOutList clampedRoot
  by_cases hr : d.inst.root < d.inst.adj.length
  · let _ := localFinEnum d.inst.adj.length
    have h := runListAux_eq_edmondsAux (localFinEnum_toList _) rfl ⟨d.inst.root, hr⟩
      d.inst.adj.length (transposeBoolTable d.inst.adj)
      (transposeIntTable d.inst.adj.length d.inst.cost) (by simp [transposeBoolTable])
    rw [tableAdj_eq_decide (R := (tableDigraph d.inst.adj).reverse.Adj) fun u w => by
        change _ ↔ tableAdj _ _ u w = true; rw [transposeBoolTable_adj rfl]; rfl,
      show tableCost (transposeIntTable _ d.inst.cost) = fun u w => tableCost d.inst.cost w u
        from funext₂ (transposeIntTable_cost d.inst.cost)] at h
    simp only [show ((d.inst.root : ℤ) < d.inst.adj.length) by omega, decide_true, ↓reduceIte,
      edmondsTableAuxList_eq_runListAux, Set.mem_ofPred_eq, exists_prop_of_true hr]
    refine (elim_decide_iff_of_spec (G := (tableDigraph d.inst.adj).reverse)
      (c := fun u w => tableCost d.inst.cost w u) (cL := fun u w => costAt d.inst.cost w u)
      (r := ⟨d.inst.root, hr⟩) (fun _ _ => rfl) h
      (edmondsOut_spec (G := tableDigraph d.inst.adj) (c := tableCost d.inst.cost)) _).trans
      ⟨fun ⟨T, hT, hTG, hle⟩ => ⟨T.reverse, hT, fun _ _ h => hTG h, ?_⟩,
        fun ⟨T, hT, hTG, hle⟩ => ⟨T.reverse, hT, fun _ _ h => hTG h, ?_⟩⟩
    · exact (@arcCost_reverse _ _ _ _ T.reverse (Classical.decRel _) (Classical.decRel _)
        _).symm.trans_le hle
    · exact (@arcCost_reverse _ _ _ _ T (Classical.decRel _) (Classical.decRel _) _).trans_le hle
  · simp [hr]

theorem minOutArborescenceDec_mem_P :
    minOutArborescenceDec ∈ Cslib.Complexity.P encArborescenceDecInstance :=
  ⟨minOutArborescenceDecide, computableInPolyTime_minOutArborescenceDecide,
    fun d => (minOutArborescenceDecide_eq_true_iff d).symm⟩

private def mapDigraph {α β : Type*} (φ : α ≃ β) (G : Digraph α) : Digraph β where
  Adj x y := G.Adj (φ.symm x) (φ.symm y)

private instance instDecidableRelMapDigraph {α β : Type*} (φ : α ≃ β) (G : Digraph α)
    [DecidableRel G.Adj] : DecidableRel (mapDigraph φ G).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj (φ.symm x) (φ.symm y)))

private theorem mapDigraph_symm {α β : Type*} (φ : α ≃ β) (G : Digraph α) :
    mapDigraph φ.symm (mapDigraph φ G) = G := by
  ext x y; simp [mapDigraph]

private theorem isInArborescence_mapDigraph_fwd {α β : Type*} (φ : α ≃ β) {G : Digraph α} {r : α}
    (h : G.IsInArborescence r) : (mapDigraph φ G).IsInArborescence (φ r) := by
  have hwalk {a b : α} (hab : Relation.ReflTransGen G.Adj a b) :
      Relation.ReflTransGen (mapDigraph φ G).Adj (φ a) (φ b) :=
    hab.lift φ fun _ _ hxy => by simpa [Function.onFun, mapDigraph] using hxy
  refine ⟨fun y hy => h.not_adj_root (φ.symm y) (by simpa [mapDigraph] using hy),
    fun v hv => ?_, fun v => by simpa using hwalk (h.reachable (φ.symm v))⟩
  obtain ⟨w, hw, hu⟩ := h.existsUnique_adj (φ.symm v) fun e => hv (φ.symm_apply_eq.mp e)
  exact ⟨φ w, by simpa [mapDigraph] using hw, fun u hu' =>
    φ.symm_apply_eq.mp (hu (φ.symm u) (by simpa [mapDigraph] using hu'))⟩

private theorem isInArborescence_mapDigraph {α β : Type*} (φ : α ≃ β) {G : Digraph α} {r : α} :
    (mapDigraph φ G).IsInArborescence (φ r) ↔ G.IsInArborescence r :=
  ⟨fun h => by simpa [mapDigraph_symm] using isInArborescence_mapDigraph_fwd φ.symm h,
    isInArborescence_mapDigraph_fwd φ⟩

private theorem arcCost_mapDigraph {α β γ : Type*} [Fintype α] [Fintype β] [AddCommMonoid γ]
    (φ : α ≃ β) (G : Digraph α) [DecidableRel G.Adj] [DecidableRel (mapDigraph φ G).Adj]
    (c : β → β → γ) :
    arcCost (mapDigraph φ G) c = arcCost G (fun u w => c (φ u) (φ w)) := by
  unfold arcCost
  rw [Finset.sum_filter, Finset.sum_filter]
  refine (Fintype.sum_equiv (φ.prodCongr φ) _ _ fun e => ?_).symm
  simp [mapDigraph]

private theorem superRootAdjList_getD (a : List (List Bool)) {u w : ℕ}
    (hu : u < a.length + 1) (hw : w < a.length + 1) :
    adjAt (superRootAdjList a) u w =
      if u == a.length then false else if w == a.length then true else adjAt a w u := by
  unfold adjAt superRootAdjList
  rw [List.getD_map_range _ _ hu, List.getD_map_range _ _ hw]
  rfl

private theorem superRootWeightList_getD (n : ℕ) (wt : List (List ℤ)) {u w : ℕ}
    (hu : u < n + 1) (hw : w < n + 1) :
    costAt (superRootWeightList n wt) u w =
      if u == n then 0 else if w == n then 0 else -costAt wt w u := by
  unfold costAt superRootWeightList
  rw [List.getD_map_range _ _ hu, List.getD_map_range _ _ hw]
  rfl

theorem maxBranchingDecide_eq_true_iff (d : BranchingDecInstance) :
    maxBranchingDecide d = true ↔ d ∈ maxBranchingDec := by
  classical
  set n := d.inst.adj.length
  set adj' := superRootAdjList d.inst.adj
  set wt' := superRootWeightList n d.inst.weight
  set r : Fin (n + 1) := Fin.last n
  let G' : Digraph (Fin (n + 1)) := ⟨fun u w => tableAdj (n + 1) adj' u w = true⟩
  let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquivLast
  have he_none : e r = none := by simp [e, r]
  have hcase (u : Fin (n + 1)) : (∃ h : u.val < n, (u.val == n) = false ∧ e u = some ⟨u.val, h⟩) ∨
      ((u.val == n) = true ∧ e u = none) := by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ u.isLt) with hu | hu
    · exact .inl ⟨hu, beq_false_of_ne hu.ne, by
        simpa [e] using (finSuccEquivLast_castSucc ⟨u.val, hu⟩)⟩
    · exact .inr ⟨beq_iff_eq.mpr hu, by rw [← he_none]; congr 1; exact Fin.ext hu⟩
  have hsuper_adj (u w : Fin (n + 1)) :
      G'.Adj u w ↔ (tableDigraph d.inst.adj).superRootDigraph.Adj (e u) (e w) := by
    change adjAt adj' u.val w.val = true ↔ _
    rw [superRootAdjList_getD d.inst.adj u.isLt w.isLt]
    rcases hcase u with ⟨_, hu, heu⟩ | ⟨hu, heu⟩ <;>
      rcases hcase w with ⟨_, hw, hew⟩ | ⟨hw, hew⟩ <;>
      dsimp only [n] at hu hw <;>
      simp [hu, hw, heu, hew, Digraph.superRootDigraph, tableDigraph]
  have hsuper_cost (u w : Fin (n + 1)) :
      tableCost wt' u w = superRootCost (tableCost d.inst.weight) (e u) (e w) := by
    change costAt wt' u.val w.val = _
    rw [superRootWeightList_getD n d.inst.weight u.isLt w.isLt]
    rcases hcase u with ⟨_, hu, heu⟩ | ⟨hu, heu⟩ <;>
      rcases hcase w with ⟨_, hw, hew⟩ | ⟨hw, hew⟩ <;>
      simp [hu, hw, heu, hew, superRootCost, tableCost]
  have hfeas : IsInArborescenceParent G'.Adj r (fun _ => r) :=
    ⟨rfl, fun x hx => by
      rw [hsuper_adj x r, he_none]
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp fun h =>
        hx (e.injective (h.trans he_none.symm))
      rw [hv]; trivial, fun _ => ⟨1, rfl⟩⟩
  let _ := localFinEnum (n + 1)
  have hG'_adj : (fun u w : Fin (n + 1) => decide (G'.Adj u w)) = tableAdj (n + 1) adj' := by
    funext u w; simp [G', Bool.decide_eq_true]
  obtain ⟨pV, hpV⟩ : ∃ pV, @edmonds (Fin (n + 1)) ℤ (localFinEnum (n + 1)) _ _ G' _
      (tableCost wt') r = some pV :=
    Option.ne_none_iff_exists'.mp fun hnone => absurd hfeas (edmonds_spec.2 hnone _)
  have hrun_eq := @runListAux_eq_edmondsAux (n + 1) (localFinEnum (n + 1))
    (localFinEnum_toList (n + 1)) rfl r (n + 1) adj' wt' (by simp [adj', superRootAdjList, n])
  have hpV' : @edmondsAux (Fin (n + 1)) ℤ (localFinEnum (n + 1)) _ _ r (n + 1)
      (tableAdj (n + 1) adj') (tableCost wt') = some pV := by
    rwa [← hG'_adj]
  rw [hpV'] at hrun_eq
  obtain ⟨pL, hpL_eq, _, hpL_val⟩ :
      ∃ pL, edmondsTableAuxList (n + 1) n adj' wt' = some pL ∧
        pL.length = n + 1 ∧ ∀ v : Fin (n + 1), pL.getD v.val 0 = (pV v).val := by
    rw [edmondsTableAuxList_eq_runListAux]
    cases hL : runListAux r.val (n + 1) adj' wt' with
    | none => simp [hL] at hrun_eq
    | some pL => exact ⟨pL, by simpa only [r, Fin.val_last] using hL, by
        simp only [hL] at hrun_eq; exact hrun_eq⟩
  obtain ⟨hT, hTG, hoptT⟩ := edmonds_optimal hpV
  have hT_map_arb : (mapDigraph e (Digraph.parentDigraph r pV)).IsInArborescence none :=
    he_none ▸ (isInArborescence_mapDigraph e).mpr hT
  obtain ⟨hB_branch, hB_ext, hB_le⟩ := Digraph.restrictOption_spec hT_map_arb
  set Bstar := Digraph.restrictOption (mapDigraph e (Digraph.parentDigraph r pV))
  have hcost_neg (T : Digraph (Fin (n + 1))) (B : Digraph (Fin n))
      (hext : mapDigraph e T = B.superRootExtend) :
      @arcCost (Fin (n + 1)) ℤ FinEnum.instFintype _ T (Classical.decRel _) (tableCost wt') =
        -@arcCost (Fin n) ℤ (Fin.fintype n) _ B (Classical.decRel _) (tableCost d.inst.weight) := by
    calc _ = arcCost T (fun u w => superRootCost (tableCost d.inst.weight) (e u) (e w)) := by
            unfold arcCost; exact Finset.sum_congr (by ext p; simp) fun p _ => hsuper_cost p.1 p.2
      _ = arcCost (mapDigraph e T) (superRootCost (tableCost d.inst.weight)) :=
            (arcCost_mapDigraph e _ _).symm
      _ = @arcCost (Option (Fin n)) ℤ inferInstance _ B.superRootExtend (Classical.decRel _)
            (superRootCost (tableCost d.inst.weight)) :=
            arcCost_congr _ _ _ _ hext _
      _ = -@arcCost (Fin n) ℤ (Fin.fintype n) _ B (Classical.decRel _)
            (tableCost d.inst.weight) := by
            rw [arcCost_superRootExtend B (tableCost d.inst.weight),
              arcCost_congr _ (Fin.fintype n) _ (Classical.decRel _) rfl (tableCost d.inst.weight)]
  have hneg_star : @arcCost (Fin (n + 1)) ℤ FinEnum.instFintype _
      (Digraph.parentDigraph r pV) (Classical.decRel _) (tableCost wt') =
      -@arcCost (Fin n) ℤ (Fin.fintype n) _ Bstar (Classical.decRel _)
        (tableCost d.inst.weight) :=
    hcost_neg _ Bstar hB_ext.symm
  have hsum_eq : (((List.range n).filter fun v => (optimumBranchingList d.inst).getD v 0 != v).map
      fun v => costAt d.inst.weight ((optimumBranchingList d.inst).getD v 0) v).sum =
      @arcCost (Fin n) ℤ (Fin.fintype n) _ Bstar (Classical.decRel _)
        (tableCost d.inst.weight) := by
    have hopt_get (v : Fin n) : (optimumBranchingList d.inst).getD v.val 0 =
        if pL.getD v.val 0 == n then v.val else pL.getD v.val 0 := by
      unfold optimumBranchingList
      change ((edmondsTableAuxList (n + 1) n adj' wt').elim [] _).getD v.val 0 = _
      rw [hpL_eq, Option.elim_some, List.getD_map_range _ _ v.isLt]
    have hno_loop (v : Fin n) : pL.getD v.val 0 ≠ v.val := fun h => by
      have hself : pV v.castSucc = v.castSucc := Fin.ext ((hpL_val v.castSucc).symm.trans h)
      have hadj : Bstar.Adj v v := by
        simpa [Bstar, mapDigraph, e] using
          show (Digraph.parentDigraph r pV).Adj v.castSucc v.castSucc from
            ⟨Fin.ne_of_val_ne (by simpa [r] using v.isLt.ne), hself⟩
      exact hB_branch.acyclic (Relation.TransGen.single hadj)
    have hpar := arcCost_parentDigraph_eq_sum_range (c := tableCost wt') (cL := costAt wt')
      (fun _ _ => rfl) r pV pL hpL_val
    rw [arcCost_congr (T₁ := Digraph.parentDigraph r pV) FinEnum.instFintype _ _ _ rfl _]
      at hneg_star
    have hsum_parent :
        (((List.range (n + 1)).filter fun v => v != r.val).map fun v =>
            costAt wt' v (pL.getD v 0)).sum =
          -(((List.range n).filter fun v => (optimumBranchingList d.inst).getD v 0 != v).map
            fun v => costAt d.inst.weight ((optimumBranchingList d.inst).getD v 0) v).sum := by
      rw [sum_range_filter_map, sum_range_filter_map,
        show (Finset.univ.filter fun v : Fin (n + 1) => (v.val != r.val) = true) =
          Finset.univ.map Fin.castSuccEmb by
            ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, bne_iff_ne, r,
              Fin.val_last, Finset.mem_map, Fin.castSuccEmb_apply, Fin.ext_iff, Fin.val_castSucc]
            exact ⟨fun h => ⟨⟨v.val, lt_of_le_of_ne (Nat.le_of_lt_succ v.isLt) h⟩, rfl⟩,
              fun ⟨w, hw⟩ => hw ▸ w.isLt.ne⟩,
        Finset.sum_map, Finset.sum_filter, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hlt : pL.getD v.val 0 < n + 1 := by
        simpa only [Fin.val_castSucc] using hpL_val v.castSucc ▸ (pV v.castSucc).isLt
      change costAt wt' v.val (pL.getD v.val 0) = -if _ then _ else _
      rw [superRootWeightList_getD n d.inst.weight (by omega) hlt,
        show (v.val == n) = false from beq_false_of_ne v.isLt.ne, hopt_get v]
      by_cases hpn : pL.getD v.val 0 = n
      · simp only [hpn, beq_self_eq_true, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true,
          neg_zero]
      · simp only [show (pL.getD v.val 0 == n) = false from beq_false_of_ne hpn,
          Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq, hno_loop v, not_false_eq_true]
    omega
  unfold maxBranchingDecide maxBranchingDec; dsimp only
  change decide (d.threshold ≤ _) = true ↔ _
  rw [hsum_eq, decide_eq_true_eq]
  refine ⟨fun hth => ⟨Bstar, hB_branch, hB_le _ fun x y hxy => by
      have := hTG hxy; change G'.Adj (e.symm x) (e.symm y) at this
      rw [hsuper_adj] at this; simpa using this, by
      rwa [arcCost_congr _ (Fin.fintype n) _ _ rfl _]⟩,
    fun ⟨B₁, hB₁, hB₁G, hle₁⟩ => hle₁.trans ?_⟩
  let T₁ := mapDigraph e.symm B₁.superRootExtend
  have hcmp := hoptT T₁ (by
      simpa [T₁, e, r] using (isInArborescence_mapDigraph e.symm).mpr
        (Digraph.isBranching_iff_isInArborescence_superRootExtend.mp hB₁))
    fun x y hxy => (hsuper_adj x y).mpr (Digraph.superRootExtend_le_superRootDigraph hB₁G
      (by simpa [T₁, mapDigraph] using hxy))
  have hrhs := hcost_neg T₁ B₁ (mapDigraph_symm e.symm B₁.superRootExtend)
  rw [arcCost_congr (T₁ := Digraph.parentDigraph r pV) _ FinEnum.instFintype _
      (Classical.decRel _) rfl _,
    arcCost_congr (T₁ := T₁) _ FinEnum.instFintype _ (Classical.decRel _) rfl _,
    hneg_star, hrhs] at hcmp
  have hle_neg := neg_le_neg_iff.mp hcmp
  rwa [arcCost_congr (T₁ := B₁) _ (Fin.fintype n) _ (Classical.decRel _) rfl _]

theorem maxBranchingDec_mem_P :
    maxBranchingDec ∈ Cslib.Complexity.P encBranchingDecInstance :=
  ⟨maxBranchingDecide, computableInPolyTime_maxBranchingDecide,
    fun d => (maxBranchingDecide_eq_true_iff d).symm⟩

end Cslib.Algorithms.Lean.Arborescence
