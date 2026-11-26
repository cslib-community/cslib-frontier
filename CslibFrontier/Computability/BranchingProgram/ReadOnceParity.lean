/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.Nondeterministic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import CslibFrontier.Foundations.Data.List.Filter
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

/-!
# Syntactic read-once parity branching programs

A *read-once parity branching program* [Volk, Definition 1.1][Volk2026] is a directed acyclic
multigraph with a source and a target whose edges are labelled by literals or Boolean constants. It
accepts an input when an odd number of source-to-target paths are consistent with it, and it is
*syntactically read-once* when no variable is tested twice on any source-to-target path, whether
or not the path is consistent with some input. Its size is its number of edges.

In this library such a program is a nondeterministic branching program `NBP` with parity acceptance
(`NBP.AcceptsParity`). Rectifiers are the edges labelled `1`, and contacts testing `x i = true` and
`x i = false` are the positive and negative literals. An edge labelled `0` is never switched on, so
deleting it changes no path count and lowers the number of edges: lower bounds for programs without
such edges apply to programs with them. This file adds the read-once condition and the size
measure:

* `NBP.wireCount` counts every wire, rectifiers included. This is the size of
  [Volk, Definition 1.1][Volk2026], which counts edges rather than nodes because in-degrees are
  unbounded. `NBP.size` counts only contacts (`NBP.size_le_wireCount`).
* `NBP.tests P v` lists, for each path from the node `v` to the target, the tests of its contacts in
  order, and `NBP.routes P` does the same for the paths from the source. An input switches on a path
  exactly when it passes all of its tests (`NBP.paths_eq_countP`, `NBP.pathCount_eq_countP`).
* `NBP.IsReadOnce` requires that no coordinate is tested twice on any route.

**Vertices and edges.** Parallel wires with the same head and label cancel in pairs under parity
acceptance. `NBP.reduce` keeps one copy of each wire of odd multiplicity at every node. It accepts
the same inputs by parity (`NBP.acceptsParity_reduce_iff`), is read-once when the original is
(`NBP.IsReadOnce.reduce`), and has at most `n ^ 2 * (|ι| |α| + 1)` wires on `n` nodes
(`NBP.wireCount_reduce_le`). So for parity acceptance the number of wires and the number of nodes
are polynomially related.

## Main definitions

* `Cslib.BranchingPrograms.NBP.wireCount`: the number of wires of a program.
* `Cslib.BranchingPrograms.NBP.tests`, `Cslib.BranchingPrograms.NBP.routes`: the tests along the
  paths from a node, and from the source, to the target.
* `Cslib.BranchingPrograms.NBP.IsReadOnce`: the syntactic read-once condition.
* `Cslib.BranchingPrograms.NBP.reduce`: cancelling parallel wires in pairs.

## Main results

* `Cslib.BranchingPrograms.NBP.pathCount_eq_countP`: the paths switched on by an input are the
  routes whose tests it passes.
* `Cslib.BranchingPrograms.NBP.acceptsParity_reduce_iff`,
  `Cslib.BranchingPrograms.NBP.IsReadOnce.reduce`,
  `Cslib.BranchingPrograms.NBP.wireCount_reduce_le`:
  a program on `n` nodes has an equivalent one, read-once if the original is, with at most
  `n ^ 2 * (|ι| |α| + 1)` wires.

## References

* [B. L. Volk, *A Lower Bound for Read-Once Parity Branching Programs*][Volk2026]
-/

public section

namespace Cslib.BranchingPrograms

namespace NBP

variable {ι α : Type*}

/-! ### Size and routes -/

/-- The number of wires of a program, rectifiers and contacts: the size of a read-once parity
branching program in [Volk, Definition 1.1][Volk2026]. -/
@[expose]
def wireCount : {n : ℕ} → NBP ι α n → ℕ
  | _, target => 0
  | _, node P wires => P.wireCount + wires.length

/-- Contacts are wires. -/
theorem size_le_wireCount : ∀ {n : ℕ} (P : NBP ι α n), P.size ≤ P.wireCount
  | _, target => le_rfl
  | _, node P _ => Nat.add_le_add (size_le_wireCount P) List.countP_le_length

/-- For each path from the node `v` to the target, the tests of its contacts in order, listed with
multiplicity: one list for each path. -/
@[expose]
def tests : {n : ℕ} → NBP ι α n → Fin n → List (List (ι × α))
  | _, target, _ => [[]]
  | _, node P wires, v =>
    Fin.lastCases (wires.flatMap fun w => (P.tests w.head).map (w.label.toList ++ ·)) P.tests v

/-- An earlier node has the same paths in a longer program. -/
@[simp] theorem tests_node_castSucc {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n))
    (v : Fin n) : (P.node wires).tests v.castSucc = P.tests v := by
  simp [tests]

/-- The paths from the last node begin with one of its wires. -/
@[simp] theorem tests_node_last {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n)) :
    (P.node wires).tests (Fin.last n) =
      wires.flatMap fun w => (P.tests w.head).map (w.label.toList ++ ·) := by
  simp [tests]

/-- The *routes* of a program: for each path from the source to the target, the tests of its
contacts in order. -/
@[expose]
def routes : {n : ℕ} → NBP ι α n → List (List (ι × α))
  | _, target => [[]]
  | _, node P wires => wires.flatMap fun w => (P.tests w.head).map (w.label.toList ++ ·)

/-- The routes of a program are the paths from its last node, the source. -/
theorem routes_node {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n)) :
    (P.node wires).routes = (P.node wires).tests (Fin.last n) :=
  (tests_node_last P wires).symm

/-- A program is *syntactically read-once* when no coordinate is tested twice on any path from the
source to the target [Volk, Definition 1.1][Volk2026]. The condition concerns all paths, also those
that no input switches on. -/
@[expose]
def IsReadOnce {n : ℕ} (P : NBP ι α n) : Prop :=
  ∀ l ∈ P.routes, (l.map Prod.fst).Nodup

instance [DecidableEq ι] {n : ℕ} (P : NBP ι α n) : Decidable P.IsReadOnce :=
  inferInstanceAs (Decidable (∀ l ∈ P.routes, (l.map Prod.fst).Nodup))

/-! ### Path counts -/

section Count

variable [DecidableEq α]

/-- An input passes the test of a wire exactly when it switches the wire on. -/
private theorem all_label_toList {n : ℕ} (w : Wire ι α n) (x : ι → α) :
    (w.label.toList.all fun p => x p.1 = p.2) = w.on x := by
  obtain ⟨_, _ | _⟩ := w <;> simp [Wire.on]

/-- The input `x` switches on the paths from `v` whose tests it passes: their number is the path
count `P.paths x v`. -/
theorem paths_eq_countP (x : ι → α) :
    ∀ {n : ℕ} (P : NBP ι α n) (v : Fin n),
      P.paths x v = (P.tests v).countP fun l => l.all fun p => x p.1 = p.2
  | _, target, _ => rfl
  | _, node P wires, v => by
    induction v using Fin.lastCases with
    | last =>
      rw [paths_node_last, tests_node_last, List.countP_flatMap, List.sum_map_filter]
      congr 1
      refine List.map_congr_left fun w _ => ?_
      simp only [Function.comp_apply, List.countP_map]
      rw [paths_eq_countP x P w.head]
      cases h : w.on x <;> simp [Function.comp_def, all_label_toList, h]
    | cast v => rw [paths_node_castSucc, tests_node_castSucc, paths_eq_countP x P v]

/-- **Path counts by routes.** The number of paths from the source to the target that `x` switches
on is the number of routes whose tests it passes. -/
theorem pathCount_eq_countP {n : ℕ} (P : NBP ι α n) (x : ι → α) :
    P.pathCount x = P.routes.countP fun l => l.all fun p => x p.1 = p.2 := by
  cases P with
  | target => rfl
  | node P wires =>
    rw [routes_node, ← paths_eq_countP, paths_node_last]
    rfl

end Count

/-! ### Cancelling parallel wires -/

section Reduce

variable [DecidableEq ι] [DecidableEq α]

/-- The wires of odd multiplicity in a list, each once. -/
@[expose]
def oddWires {n : ℕ} (wires : List (Wire ι α n)) : List (Wire ι α n) :=
  wires.dedup.filter fun w => Odd (wires.count w)

/-- Cancel parallel wires in pairs: at every node keep one copy of each wire, with its head and
label, that occurs an odd number of times. -/
@[expose]
def reduce : {n : ℕ} → NBP ι α n → NBP ι α n
  | _, target => target
  | _, node P wires => node P.reduce (oddWires wires)

private theorem mem_of_mem_oddWires {n : ℕ} {wires : List (Wire ι α n)} {w : Wire ι α n}
    (h : w ∈ oddWires wires) : w ∈ wires :=
  List.mem_dedup.mp (List.mem_of_mem_filter h)

/-- Every path of the reduced program is a path of the original one. -/
theorem mem_tests_of_mem_tests_reduce :
    ∀ {n : ℕ} (P : NBP ι α n) (v : Fin n) {l : List (ι × α)},
      l ∈ P.reduce.tests v → l ∈ P.tests v
  | _, target, _, _, h => h
  | _, node P wires, v, l, h => by
    induction v using Fin.lastCases with
    | last =>
      simp only [reduce, tests_node_last, List.mem_flatMap, List.mem_map] at h ⊢
      obtain ⟨w, hw, l', hl', rfl⟩ := h
      exact ⟨w, mem_of_mem_oddWires hw, l', mem_tests_of_mem_tests_reduce P w.head hl', rfl⟩
    | cast v =>
      rw [tests_node_castSucc]
      exact mem_tests_of_mem_tests_reduce P v (by rwa [reduce, tests_node_castSucc] at h)

/-- Every route of the reduced program is a route of the original one. -/
theorem mem_routes_of_mem_routes_reduce {n : ℕ} (P : NBP ι α n) {l : List (ι × α)}
    (h : l ∈ P.reduce.routes) : l ∈ P.routes := by
  cases P with
  | target => exact h
  | node P wires =>
    simpa only [routes_node] using
      mem_tests_of_mem_tests_reduce (P.node wires) (Fin.last _) (by rwa [reduce, tests_node_last])

/-- Cancelling parallel wires keeps a program read-once. -/
theorem IsReadOnce.reduce {n : ℕ} {P : NBP ι α n} (h : P.IsReadOnce) : P.reduce.IsReadOnce :=
  fun l hl => h l (mem_routes_of_mem_routes_reduce P hl)

/-- In `ZMod 2`, a sum over a list of wires depends only on the parity of their multiplicities. -/
private theorem sum_map_oddWires {n : ℕ} (wires : List (Wire ι α n))
    (g : Wire ι α n → ZMod 2) :
    ((oddWires wires).map g).sum = (wires.map g).sum := by
  rw [oddWires, ← List.sum_toFinset g ((List.nodup_dedup wires).filter _),
    Finset.sum_list_map_count, List.toFinset_filter, List.toFinset_dedup, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [nsmul_eq_mul]
  rcases Nat.even_or_odd (wires.count w) with he | ho
  · simp [ZMod.natCast_eq_zero_iff_even.mpr he, Nat.not_odd_iff_even.mpr he]
  · simp [ZMod.natCast_eq_one_iff_odd.mpr ho, ho]

/-- Cancelling parallel wires keeps the parity of the number of paths switched on from each
node. -/
theorem paths_reduce (x : ι → α) :
    ∀ {n : ℕ} (P : NBP ι α n) (v : Fin n),
      (P.reduce.paths x v : ZMod 2) = (P.paths x v : ZMod 2)
  | _, target, _ => rfl
  | _, node P wires, v => by
    induction v using Fin.lastCases with
    | last =>
      simp only [reduce]
      rw [paths_node_last, paths_node_last, List.sum_map_filter, List.sum_map_filter,
        Nat.cast_list_sum, Nat.cast_list_sum, List.map_map, List.map_map, sum_map_oddWires]
      congr 2 with w
      by_cases hw : w.on x <;> simp [hw, paths_reduce x P w.head]
    | cast v => simpa only [reduce, paths_node_castSucc] using paths_reduce x P v

/-- Cancelling parallel wires keeps the parity of the number of paths switched on. -/
theorem pathCount_reduce {n : ℕ} (P : NBP ι α n) (x : ι → α) :
    (P.reduce.pathCount x : ZMod 2) = (P.pathCount x : ZMod 2) := by
  cases P with
  | target => rfl
  | node P wires =>
    simpa only [reduce, pathCount, paths_node_last] using paths_reduce x (P.node wires) (Fin.last _)

/-- **Cancelling parallel wires keeps the function computed by parity.** -/
theorem acceptsParity_reduce_iff {n : ℕ} (P : NBP ι α n) (x : ι → α) :
    P.reduce.AcceptsParity x ↔ P.AcceptsParity x := by
  rw [AcceptsParity, AcceptsParity, ← ZMod.natCast_eq_one_iff_odd,
    ← ZMod.natCast_eq_one_iff_odd, pathCount_reduce]

/-- **Edges against vertices.** After cancelling parallel wires, a program on `n` nodes has at most
`n ^ 2 * (|ι| |α| + 1)` wires: each node keeps at most one wire of each head and label. -/
theorem wireCount_reduce_le [Fintype ι] [Fintype α] :
    ∀ {n : ℕ} (P : NBP ι α n),
      P.reduce.wireCount ≤ n ^ 2 * (Fintype.card ι * Fintype.card α + 1)
  | _, target => Nat.zero_le _
  | n + 1, node P wires => by
    have hP := wireCount_reduce_le P
    have hw : (oddWires wires).length ≤ n * (Fintype.card ι * Fintype.card α + 1) :=
      Wire.card (ι := ι) (α := α) (n := n) ▸ ((List.nodup_dedup wires).filter _).length_le_card
    simp only [reduce, wireCount]
    nlinarith

end Reduce

end NBP

end Cslib.BranchingPrograms
