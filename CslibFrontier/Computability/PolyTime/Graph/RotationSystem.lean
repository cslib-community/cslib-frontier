/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.GetD
import CslibFrontier.Tactic.EncLen

/-!
# Native polynomial-time rotation-certificate verification

Binary table lookup uses the existing saturating binary-index implementation. Orbit clocks
are unary and computed from the edge-list length. Every intermediate iterate is a table entry
or zero, whose encoded length is bounded by the encoded table; this remains true on malformed
input. No certificate validity premise appears in the native resource theorem.

## Main results

* `Cslib.Complexity.Graph.RotationCertificate.computableInPolyTime_verifyRotation`: native
  permutation and endpoint-fiber verification.
* `Cslib.Complexity.Graph.RotationCertificate.computableInPolyTime_verifyGenusZero`: native
  verification including each component's numerical Euler equation.
-/

public section

namespace Cslib.Complexity.Graph.RotationCertificate

open Turing.MultiTapeTM

attribute [fun_prop] encRotationCertificate_successor_polyTime encRotationCertificate_mk_polyTime

/-- Saturating binary-indexed lookup in a computed framed list with a fixed fallback, scoped to
`Cslib.Complexity.Graph.RotationCertificate` so modules using unary `List.getD` incur no extra
`fun_prop` search branch. -/
@[scoped fun_prop] theorem listGetD_binary_encList {α β : Type}
    {input : α ↪ List Bool} {enc : β ↪ List Bool} (fallback : β)
    {table : α → List β} {index : α → ℕ}
    (ht : ComputableInPolyTime table input (encList enc))
    (hi : ComputableInPolyTime index input encNat) :
    ComputableInPolyTime (fun x => (table x).getD (index x) fallback) input enc :=
  ComputableInPolyTime.listGetD_binary fallback ht hi

/-- Reading the supplied binary successor table is a projection of its structure encoding. -/
@[fun_prop] theorem computableInPolyTime_successor :
    ComputableInPolyTime RotationCertificate.successor encRotationCertificate (encList encNat) :=
  encRotationCertificate_successor_deg.computableInPolyTime

/-- Enumerating listed endpoint occurrences is native polynomial-time on every raw graph. -/
theorem incidenceVertices_polyTime :
    ComputableInPolyTime incidenceVertices encGraph (encList encNat) := by
  unfold incidenceVertices encGraph
  fun_prop

/-- Enumerating listed endpoint occurrences of a computed graph is native polynomial-time. -/
@[fun_prop] theorem incidenceVertices_polyTime' {α : Type} {enc : α ↪ List Bool}
    {G : α → Graph} (hG : ComputableInPolyTime G enc encGraph) :
    ComputableInPolyTime (fun x => (G x).incidenceVertices) enc (encList encNat) := by
  simpa only [Function.comp_def] using incidenceVertices_polyTime.comp hG

/-- The table and unary iteration count are paired and framed before the binary start index. -/
abbrev encRotationWalk := encPair (encPair (encList encNat) encUnary) encNat

/-- Iterating a binary-indexed successor table has a native polynomial-time implementation
for a unary number of steps, including invalid and oversized table indices. -/
theorem computableInPolyTime_walk :
    ComputableInPolyTime (fun x : (List ℕ × ℕ) × ℕ => walk x.1.1 x.1.2 x.2)
      encRotationWalk encNat := by
  have hpar : ComputableInPolyTime
      (fun x : (List ℕ × ℕ) × ℕ => x.1.1) encRotationWalk (encList encNat) := by
    unfold encRotationWalk
    fun_prop
  unfold walk
  refine ComputableInPolyTime.iterateWith_of_bounded_growth
    (count := fun x => x.1.2) (init := fun x => x.2)
    (step := fun table i => table.getD i 0) (encState := encNat) hpar
    (by unfold encRotationWalk; fun_prop) (by unfold encRotationWalk; fun_prop)
    (by fun_prop) hpar.polyBounded_length ?_
  intro x state
  have hb : (encNat (x.1.1.getD state 0)).length ≤ (encList encNat x.1.1).length := by
    by_cases hi : state < x.1.1.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat)
        x.1.1 _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [encNat_apply]
  exact hb.trans (Nat.le_add_left _ _)

/-- Iterating a computed binary-indexed successor table for a computed unary step count from a
computed binary start index is native polynomial-time. -/
@[fun_prop] theorem computableInPolyTime_walk_comp {α : Type} {enc : α ↪ List Bool}
    {table : α → List ℕ} {steps start : α → ℕ}
    (ht : ComputableInPolyTime table enc (encList encNat))
    (hs : ComputableInPolyTime steps enc encUnary)
    (hi : ComputableInPolyTime start enc encNat) :
    ComputableInPolyTime (fun x => walk (table x) (steps x) (start x)) enc encNat := by
  simpa only [Function.comp_def] using computableInPolyTime_walk.comp ((ht.prod hs).prod hi)

/-- Orbit input: unary dart count, binary successor list, then two binary dart indices.
Each left part is framed by its enclosing pair. -/
abbrev encRotationOrbit :=
  encPair (encPair encUnary (encList encNat)) (encPair encNat encNat)

/-- Bounded orbit membership is native polynomial-time on all tables. -/
theorem computableInPolyTime_orbitBool :
    ComputableInPolyTime (fun x : (ℕ × List ℕ) × (ℕ × ℕ) =>
      orbitBool x.1.1 x.1.2 x.2.1 x.2.2)
      encRotationOrbit encBool := by
  unfold orbitBool encRotationOrbit
  fun_prop

/-- Bounded orbit scanning composes native table, binary endpoint and unary clock computations.
The clock is explicit; the runtime certificate applies to every raw table and index, without
a graph, permutation or certificate-validity premise. -/
theorem orbitBool_polyTime {α : Type} {enc : α ↪ List Bool}
    {n i j : α → ℕ} {table : α → List ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (ht : ComputableInPolyTime table enc (encList encNat))
    (hi : ComputableInPolyTime i enc encNat) (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (fun x => orbitBool (n x) (table x) (i x) (j x)) enc encBool := by
  simpa only [Function.comp_def] using
    computableInPolyTime_orbitBool.comp ((hn.prod ht).prod (hi.prod hj))

attribute [local fun_prop] orbitBool_polyTime

/-- A unary-funded range can be enumerated with binary-encoded entries in polynomial time. -/
theorem range_binary :
    ComputableInPolyTime List.range encUnary (encList encNat) := by
  simpa [Function.comp_def] using
    (ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp
      ComputableInPolyTime.range

/-- Enumerating `List.range (n x)` with binary-encoded entries from a computed unary count,
scoped to `Cslib.Complexity.Graph.RotationCertificate` so unary `List.range` callers incur no
extra `fun_prop` search branch. -/
@[scoped fun_prop] theorem range_binary' {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun x => List.range (n x)) enc (encList encNat) := by
  simpa only [Function.comp_def] using range_binary.comp hn

/-- Testing whether a computed list enumerates every vertex of another computed list once is
native polynomial-time. -/
@[fun_prop] theorem _root_.Cslib.Complexity.Graph.computableInPolyTime_enumeratesBool_comp
    {α : Type} {enc : α ↪ List Bool} {V p : α → List ℕ}
    (hV : ComputableInPolyTime V enc (encList encNat))
    (hp : ComputableInPolyTime p enc (encList encNat)) :
    ComputableInPolyTime (fun x => enumeratesBool (V x) (p x)) enc encBool := by
  simpa only [Function.comp_def] using computableInPolyTime_enumeratesBool.comp (hV.prod hp)

/-- Every part of rotation validation runs natively in polynomial time in the graph and table
encodings, without an assumed checker, recognizer, or well-formedness hypothesis. -/
@[fun_prop] theorem computableInPolyTime_verifyRotation :
    ComputableInPolyTime (fun x : Graph × RotationCertificate => verifyRotation x.1 x.2)
      encGraphRotationCertificate encBool := by
  unfold verifyRotation encGraphRotationCertificate
  apply ComputableInPolyTime.bool_and' (by fun_prop)
  apply ComputableInPolyTime.allWithInput (encA := encNat) (by fun_prop)
  apply ComputableInPolyTime.allWithInput (encA := encNat) (by fun_prop)
  fun_prop

private theorem componentStep_polyTime :
    ComputableInPolyTime (fun p : Graph × List ℕ => componentStep p.1 p.2)
      (encPair encGraph (encList encNat)) (encList encNat) := by
  unfold componentStep encGraph
  fun_prop

/-- Breadth-first expansion is native polynomial-time; the accumulated list grows by at most
one copy of the declared vertex list per iteration, including on malformed graphs. -/
theorem computableInPolyTime_componentVertices :
    ComputableInPolyTime (fun p : Graph × ℕ => componentVertices p.1 p.2)
      (encPair encGraph encNat) (encList encNat) := by
  have hv : ComputableInPolyTime (fun p : Graph × ℕ => p.1.vertices)
      (encPair encGraph encNat) (encList encNat) := by fun_prop
  unfold componentVertices
  refine ComputableInPolyTime.iterateWith_of_bounded_growth
    (par := fun p : Graph × ℕ => p.1) (count := fun p => p.1.vertices.length)
    (init := fun p => [p.2]) (step := componentStep)
    (by fun_prop) (by fun_prop) (by fun_prop)
    componentStep_polyTime hv.polyBounded_length ?_
  intro p state
  simp only [componentStep, encList_append, List.length_append]
  apply Nat.add_le_add_left
  rw [length_encList, length_encList]
  exact (List.filter_sublist.map (fun n : ℕ => 2 * (encNat n).length + 1)).sum_le_sum (by simp)

private theorem componentBool_polyTime {α : Type} {enc : α ↪ List Bool}
    {G : α → Graph} {root v : α → ℕ} (hG : ComputableInPolyTime G enc encGraph)
    (hr : ComputableInPolyTime root enc encNat) (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => componentBool (G x) (root x) (v x)) enc encBool := by
  unfold componentBool
  apply ComputableInPolyTime.anyWithInput
    (computableInPolyTime_componentVertices.comp (hG.prod hr))
  fun_prop

attribute [local fun_prop] componentBool_polyTime

private theorem reverseIndex_polyTime : ComputableInPolyTime reverseIndex encNat encNat := by
  have hmod : ComputableInPolyTime (fun i : ℕ => i % 2) encNat encNat :=
    ComputableInPolyTime.binary_mod' ComputableInPolyTime.id' (ComputableInPolyTime.const 2)
  unfold reverseIndex
  fun_prop

attribute [local fun_prop] reverseIndex_polyTime

/-- Construct the inverse-successor face table by bounded scans of actual graph darts.
Runtime is native polynomial time on all raw graphs and certificates, including oversized
binary successors; no validity or endpoint-declaration premise is used. -/
theorem faceTable_polyTime :
    ComputableInPolyTime (fun p : Graph × RotationCertificate => faceTable p.1 p.2)
      encGraphRotationCertificate (encList encNat) := by
  unfold faceTable encGraphRotationCertificate
  apply ComputableInPolyTime.mapWithInput (encA := encNat) (by fun_prop)
  exact ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.idxOfWithInput (by fun_prop) (by fun_prop))

private theorem faceTable_polyTime_comp {α : Type} {enc : α ↪ List Bool}
    {G : α → Graph} {c : α → RotationCertificate}
    (hG : ComputableInPolyTime G enc encGraph)
    (hc : ComputableInPolyTime c enc encRotationCertificate) :
    ComputableInPolyTime (fun x => faceTable (G x) (c x)) enc (encList encNat) := by
  simpa only [Function.comp_def] using faceTable_polyTime.comp (hG.prod hc)

private theorem faceRepBool_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ => faceRepBool p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList encNat)) encNat) encBool := by
  unfold faceRepBool
  apply ComputableInPolyTime.allWithInput (encA := encNat) (by fun_prop)
  exact ComputableInPolyTime.bool_or'
    (ComputableInPolyTime.bool_not.comp (by fun_prop))
    (ComputableInPolyTime.binary_le' (by fun_prop) (by fun_prop))

private theorem faceRepBool_polyTime' {α : Type} {enc : α ↪ List Bool}
    {n i : α → ℕ} {table : α → List ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (ht : ComputableInPolyTime table enc (encList encNat))
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun x => faceRepBool (n x) (table x) (i x)) enc encBool := by
  simpa only [Function.comp_def] using faceRepBool_polyTime.comp ((hn.prod ht).prod hi)

attribute [local fun_prop] faceTable_polyTime_comp faceRepBool_polyTime'

private theorem faceCount_polyTime :
    ComputableInPolyTime (fun p : (Graph × RotationCertificate) × ℕ =>
      (List.range (2 * p.1.1.edges.length)).countP fun i =>
        componentBool p.1.1 p.2 (p.1.1.incidenceVertices.getD i 0) &&
          faceRepBool (2 * p.1.1.edges.length) (faceTable p.1.1 p.1.2) i)
      (encPair encGraphRotationCertificate encNat) encUnary := by
  unfold encGraphRotationCertificate
  apply ComputableInPolyTime.countPWithInput (encA := encNat) (by fun_prop)
  fun_prop

/-- Componentwise Euler verification is native polynomial-time in the actual encoded graph
and successor table. No connectivity, permutation, or index-bound premise is required. -/
@[fun_prop] theorem computableInPolyTime_verifyEuler :
    ComputableInPolyTime (fun p : Graph × RotationCertificate => verifyEuler p.1 p.2)
      encGraphRotationCertificate encBool := by
  have hf := faceCount_polyTime
  unfold verifyEuler encGraphRotationCertificate
  apply ComputableInPolyTime.allWithInput (encA := encNat) (by fun_prop)
  apply ComputableInPolyTime.ite (by fun_prop)
    (ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.unary_add' (by fun_prop) hf)
      (ComputableInPolyTime.unary_add' (by fun_prop) (ComputableInPolyTime.const 2)))
    (ComputableInPolyTime.const true)

/-- The full finite supplied-certificate verifier has a native polynomial-time certificate. -/
@[fun_prop] theorem computableInPolyTime_verifyGenusZero :
    ComputableInPolyTime (fun p : Graph × RotationCertificate => verifyGenusZero p.1 p.2)
      encGraphRotationCertificate encBool := by
  unfold verifyGenusZero
  exact computableInPolyTime_verifyRotation.bool_and' computableInPolyTime_verifyEuler

/-- Verifying a computed graph against a computed rotation certificate runs in native
polynomial time. -/
@[fun_prop] theorem computableInPolyTime_verifyGenusZero_comp {α : Type} {enc : α ↪ List Bool}
    {G : α → Graph} {c : α → RotationCertificate}
    (hG : ComputableInPolyTime G enc encGraph)
    (hc : ComputableInPolyTime c enc encRotationCertificate) :
    ComputableInPolyTime (fun x => verifyGenusZero (G x) (c x)) enc encBool := by
  simpa only [Function.comp_def] using computableInPolyTime_verifyGenusZero.comp (hG.prod hc)

end Cslib.Complexity.Graph.RotationCertificate
