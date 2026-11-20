/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredQuery

/-!
# Native NL as uniformly queried layered reachability

This is the layered-reachability prerequisite of #6747, not the equality NL = UL. For every
native NL witness, the fixed compact-configuration construction gives a simple layered graph
with polynomially many vertices and two distinguished endpoints. Early acceptance is preserved
by an accepting sink and waiting steps. No bound on the original accepting computation time is
assumed: finite reachability supplies a short path.

The graph is implicit. `STCON.layeredEdgeQuery_inSpace` and
`STCON.layeredQueryIndex_inSpace` certify native linear workspace in the binary
dimensions/coordinates; `STCON.layeredQuery_length_le_log` bounds that argument
logarithmically when its numbers are polynomially bounded. The single input bit is read from
the original word, not copied into the callback state. `STCON.layeredQuery_agrees`
connects this callback to the mathematical graph.

The convention of one fixed-width copy of the vertices per layer and edges advancing exactly
one layer matches [Hoza2026NLUL], Section 1.2, page 2, footnote 2. Hoza uses the NL-completeness of
layered reachability as a prerequisite; the construction here instantiates that step for the
library's native machines and arbitrary injective input encodings.

## Main results

* `Cslib.Complexity.exists_layered_reachability_of_mem_NL`: the fixed native witness and its
  polynomial-size, exact layered configuration graphs, uniformly over all encoded inputs.
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeNTM _root_.Turing.MultiTapeNTM.ConfigurationGraph
  _root_.Turing.MultiTapeTM

/-- A step toward #6747, not NL = UL: every native NL language reduces to the fixed layered
configuration graph of its witnessing machine. The exponent and machine are chosen before
the input. The graph has polynomial size and its adjacency callback has the native certificates
in `STCON.LayeredQuery`, with read-only access to the original input. -/
theorem exists_layered_reachability_of_mem_NL {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ NL enc) :
    ∃ (k : ℕ) (State : Type) (inst : Fintype State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
      letI := inst
      ntm.DecidesInSpace enc A (fun a => c * (Nat.log2 (enc a).length + 1)) ∧
      ComputableInSpace (STCON.layeredEdgeQuery ntm) STCON.encLayeredQuery encBool
        (fun q => (STCON.encLayeredQuery q).length) ∧
      ComputableInSpace (STCON.layeredQueryIndex (k := k)) STCON.encLayeredQuery encNat
        (fun q => (STCON.encLayeredQuery q).length) ∧
      ∀ a, let I := STCON.configurationInstance ntm c (enc a)
        (a ∈ A ↔ Relation.ReflTransGen (STCON.layeredRelation I)
          (STCON.layeredStart I) (STCON.layeredTarget I)) ∧
        Nat.card (STCON.LayeredGraphVertex I) ≤
          ((enc a).length + 2) ^
            (2 * (radixExponent State c * Fintype.card (Register k) + 1)) ∧
        ∀ u v : STCON.LayeredGraphVertex I,
          (STCON.encLayeredQuery (STCON.layeredQuery ntm c (enc a) u v)).length ≤
            12 * (radixExponent State c * Fintype.card (Register k) + 1) *
              (Nat.log2 ((enc a).length + 1) + 1) + 8 := by
  obtain ⟨k, State, hfin, ntm, c, hdec⟩ := hA
  let : Finite State := hfin
  let : Fintype State := Fintype.ofFinite State
  refine ⟨k, State, inferInstance, ntm, c, hdec, STCON.layeredEdgeQuery_inSpace ntm,
    STCON.layeredQueryIndex_inSpace, ?_⟩
  intro a
  exact ⟨(hdec.1 a).2.trans
      ((STCON.configurationInstance_mem_iff ntm c (hdec.1 a).1).symm.trans
        (STCON.layered_reachable_iff _).symm),
    STCON.card_configurationLayered_le_pow ntm c (enc a),
    STCON.length_layeredQuery_le_log ntm c (enc a)⟩

end Cslib.Complexity
