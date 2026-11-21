/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.SeededChildEndpoints
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortGraph
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Recursive lookup of descendant endpoints from a represented block computation

A path of packing splits starts from the executable lookup of the marked schedule. The recursive
witness at the other end answers exactly the numbered endpoints of the resulting descendant,
and has no witness at an out-of-range index.
-/

public section

namespace Turing.MultiTapeTM.RootEndpointQuery

open MultiTapePTM Cslib.Circuits.Frontier NativeChild

/-- Root of the endpoint-witness recursion, reading the actual marked schedule. -/
@[expose] def endpointQuery (k copies : ℕ) (raw : List Bool) : EndpointQuery where
  size := edgeCount k ⟨raw, copies, 0⟩
  accepts e p := query k ⟨raw, copies, e⟩ = some p

/-- Every finite sequence of splits from the actual represented root gives precisely its
native descendant edge list. The proposed parent and its class-rank predecessors at each
level use the endpoint relation for the same preceding path. -/
theorem represents_descendant {k q copies : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)
    (input : List Bool) (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool)
    (levels : List EndpointQuery.Labels) :
    let raw := ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ))
    let root := endpointQuery k copies raw
    (levels.foldl (fun parent l => parent.child (l.split parent)) root).Represents
      (levels.foldl (fun parent l => l.edges parent) (RootPortGraph.ends (q := q)
        machine input b σ code)) := by
  apply EndpointQuery.Represents.descend
  constructor
  · simp [endpointQuery, edgeCount, intervals, RootPredecessorGraph.edgeCount]
  · intro e p
    by_cases he : e < RootPredecessorGraph.edgeCount k q copies
    · let i : Fin (RootPredecessorGraph.edgeCount k q copies) := ⟨e, he⟩
      change query k _ = some p ↔ _
      rw [RootPredecessorGraph.query_endpoint machine input b σ code i]
      rw [RootPortGraph.length_ends, and_iff_right he, RootPortGraph.ends]
      rw [show e = i.val from rfl, List.getD_ofFn _ i]
      simp
    · have hn := query_eq_none_of_edgeCount_le k
        ⟨ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ)), copies, e⟩
        (by simpa [edgeCount, intervals, RootPredecessorGraph.edgeCount] using Nat.le_of_not_gt he)
      simp [endpointQuery, hn, he]

end Turing.MultiTapeTM.RootEndpointQuery
