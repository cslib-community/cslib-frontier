/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPredecessorGraph
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.ParentEdgeWitness
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Child port selection in a seeded root graph

At a split coordinate, the row group and column group are the radix-64 symbols of the
corresponding endpoint labels. One raw root endpoint lookup and one seeded hash suffice to test
whether a numbered parent edge contributes to a child port prefix. The group and endpoint lists
here specify the native child's ordering and do not form part of the query input.
-/

public section

namespace Turing.MultiTapeTM.RootPortGraph

open MultiTapePTM Cslib Cslib.Circuits.Frontier
open RootPredecessorGraph (edgeCount vertexCount rowOf colOf inputOfIndices)

variable {k q copies a : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)
    (input : List Bool) (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool)

/-- The old vertices and subdivision vertices have separate lists of words from one seed.
The second list continues the tagged vertex numbering after the first. -/
noncomputable def words (r s a : ℕ) (seed : BalancedSchedules.SeededLabels.Seed (r + s) (6 * a)) :
    List (List ℕ) × List (List ℕ) :=
  let word (v : Fin (r + s)) := BalancedSchedules.scheduleToWord
    (PacketPacking.Seeded.label (r + s) a seed v)
  (List.ofFn fun v : Fin r => word (v.castAdd s), List.ofFn fun v : Fin s => word (v.natAdd r))

/-- The native child's group lookup is the selected symbol of the shared seed's vertex label. -/
theorem getD_groupsOf (r s a : ℕ) (seed : BalancedSchedules.SeededLabels.Seed (r + s) (6 * a))
    (i : Fin a) (v : Fin (r + s)) :
    (NativeChild.groupsOf r i.val (r + s) (words r s a seed)).getD v.val 0 =
      (PacketPacking.Seeded.label (r + s) a seed v i).val := by
  rw [List.getD_eq_getElem _ _ (by simp [NativeChild.groupsOf])]
  simp only [NativeChild.groupsOf, List.getElem_map, List.getElem_range, words]
  by_cases h : v.val < r
  · rw [ite_eq_left h, List.getD_ofFn _ ⟨v.val, h⟩, BalancedSchedules.scheduleToWord,
      List.getD_ofFn _ i]
    rfl
  · have hv : v.val - r < s := by omega
    rw [ite_eq_right h, List.getD_ofFn _ ⟨v.val - r, hv⟩, BalancedSchedules.scheduleToWord,
      List.getD_ofFn _ i]
    have he : (⟨v.val - r, hv⟩ : Fin s).natAdd r = v := by apply Fin.ext; dsimp; omega
    rw [he]

/-- The two endpoint keys used by the native child, in the actual numbered parent edge order. -/
@[expose] noncomputable def ends : List (ℕ × ℕ) := List.ofFn fun e : Fin (edgeCount k q copies) =>
  ((explicitVertexEquiv k q copies (.inl (rowOf machine input b σ code e))).val,
    (explicitVertexEquiv k q copies (.inr (colOf k q copies e))).val)

/-- The parent's endpoint table has exactly one pair per half-edge. -/
@[simp] theorem length_ends :
    (ends (q := q) machine input b σ code).length = edgeCount k q copies := by simp [ends]

variable (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))

/-- The group selected by one radix-64 split coordinate at each numbered vertex. -/
noncomputable def groups (i : Fin a) : List ℕ :=
  NativeChild.groupsOf (q * (3 * k + 2)) i.val (vertexCount k q copies)
    (words _ (q * (3 * k + 1) * copies) a seed)

private theorem symbol_eq (bound j : ℕ) (i : Fin a) (v : Fin (vertexCount k q copies)) :
    RootPortFinish.symbol (inputOfIndices k q copies σ a seed bound j).context i.val v.val =
      (PacketPacking.Seeded.label (vertexCount k q copies) a seed v i).val := by
  simp only [RootPortFinish.symbol, inputOfIndices, TrinomialArithmetic.runSelected_eq,
    PacketPacking.Seeded.label, PacketPacking.Seeded.wordEquiv, Equiv.trans_apply,
    finFunctionFinEquiv_symm_apply_val, BalancedSchedules.SeededLabels.label]
  rfl

/-- Select the endpoint named by the port side, using the child's ordinary row/column convention. -/
@[expose] def side (column : Bool) (e : ℕ × ℕ) : ℕ := if column then e.2 else e.1

/-- Every bounded prefix test uses exactly the endpoint group used by the native child.
Padded candidate indices reject even for group zero. -/
theorem query_eq_portPredecessor (i : Fin a) (column : Bool) (g : ℕ) {bound : ℕ}
    (hb : bound ≤ edgeCount k q copies) (j : ℕ) :
    RootPortQuery.query k (⟨column, i.val, g⟩, inputOfIndices k q copies σ a seed bound j) =
      NativeChild.portPredecessor (groups seed i) g (ends (q := q) machine input b σ code)
        (side column) bound j := by
  by_cases hj : j < edgeCount k q copies
  · let e : Fin (edgeCount k q copies) := ⟨j, hj⟩
    let row := explicitVertexEquiv k q copies (.inl (rowOf machine input b σ code e))
    let col := explicitVertexEquiv k q copies (.inr (colOf k q copies e))
    have he := RootPredecessorGraph.query_endpoint machine input b σ code e
    change RootPortFinish.run ⟨_, _, RootEndpointQuery.query k ⟨_, copies, e.val⟩⟩ = _
    rw [show RootEndpointQuery.query k ⟨(inputOfIndices k q copies σ a seed bound j).raw,
      copies, e.val⟩ = some (row.val, col.val) from he, RootPortFinish.run_some]
    rw [NativeChild.portPredecessor, show (ends (q := q) machine input b σ code).getD j (0, 0) =
        (row.val, col.val) from List.getD_ofFn _ e _]
    cases column <;>
      simp only [side, Bool.false_eq_true, ↓reduceIte, groups, getD_groupsOf] <;>
      rw [symbol_eq] <;> rfl
  · have he : RootEndpointQuery.query k
        (RootPredecessorQuery.request (inputOfIndices k q copies σ a seed bound j) j) = none := by
      apply RootEndpointQuery.query_eq_none_of_edgeCount_le
      simpa [RootEndpointQuery.edgeCount, RootEndpointQuery.intervals, inputOfIndices,
        RootPredecessorQuery.request, edgeCount] using Nat.le_of_not_gt hj
    change RootPortFinish.run ⟨_, _, RootEndpointQuery.query k
      (RootPredecessorQuery.request (inputOfIndices k q copies σ a seed bound j) j)⟩ = _
    rw [he, RootPortFinish.run_none]
    simp [NativeChild.portPredecessor, show ¬j < bound by omega]

/-- The sum of native root port tests is the child's port prefix rank, including the full
prefix that counts all row or column ports of a group. -/
theorem portRank_eq_sum_query (i : Fin a) (column : Bool) (g : ℕ) {bound : ℕ}
    (hb : bound ≤ edgeCount k q copies) :
    NativeChild.portRank (groups seed i) g (ends (q := q) machine input b σ code)
        (side column) bound =
      ∑ j : Fin (edgeCount k q copies),
        (RootPortQuery.query k (⟨column, i.val, g⟩,
          inputOfIndices k q copies σ a seed bound j.val)).toNat := by
  rw [NativeChild.portRank_eq_sum_predecessors _ _ _ _ (by simpa [ends] using hb)]
  simp only [query_eq_portPredecessor machine input b σ code seed i column g hb]
  let f (j : ℕ) := (NativeChild.portPredecessor (groups seed i) g
    (ends (q := q) machine input b σ code) (side column) bound j).toNat
  change (∑ j : Fin (ends (q := q) machine input b σ code).length, f j.val) =
    ∑ j : Fin (edgeCount k q copies), f j.val
  rw [Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f]
  simp [ends]

end Turing.MultiTapeTM.RootPortGraph
