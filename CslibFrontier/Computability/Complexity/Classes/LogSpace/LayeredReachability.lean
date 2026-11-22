/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredCallback

/-!
# Native NL as uniformly queried layered reachability

This is the layered-reachability prerequisite of #6747, not the equality NL = UL. For every
native NL witness, the fixed compact-configuration construction gives a simple layered graph
with polynomially many vertices and two distinguished endpoints. Early acceptance is preserved
by an accepting sink and waiting steps. No bound on the original accepting computation time is
assumed: finite reachability supplies a short path.

The graph is implicit. The fixed `STCON.layeredCallback` takes a compact pending request,
reads one bit from the original word and returns the adjacency answer. All five components have
native linear-workspace certificates, and every reachable call state has logarithmic encoded
length. The existing same-input call compiler consumes this interface; the streaming scans and
their caller-state bounds remain separate work in #6747.

The convention of one fixed-width copy of the vertices per layer and edges advancing exactly
one layer matches [Hoza2026NLUL], Section 1.2, page 2, footnote 2. Hoza uses the NL-completeness of
layered reachability as a prerequisite; the construction here instantiates that step for the
library's native machines and arbitrary injective input encodings.

## Applying the interface

Import `CslibFrontier.Computability.Complexity.Classes.LogSpace.LayeredReachability` and use
`Cslib.Complexity.exists_layered_reachability_of_mem_NL` for the layered configuration graph
of a native NL witness. This is a prerequisite for [#6747](https://github.com/cslib-community/cslib-frontier/issues/6747),
not NL = UL. The machine and polynomial exponent are fixed before the encoded input; arbitrary
injective input encodings are supported. The construction reuses the existing accepting sink.

For a graph `I` with `n` vertices, `STCON.LayeredGraphVertex I` has layers `0…n−1` and columns
`Fin n`. Access them as `v.val.layer` and `v.val.vertex`.
`Relation.LayeredVertex.boundedEquiv (Fin n) (n−1)` converts this carrier to the rectangular
product `Fin ((n−1)+1) × Fin n`; `n` is positive because `I.s : Fin n`.
`STCON.layeredRelation I` advances exactly one layer and either follows an original edge or
waits in the same column. It has no self edges. The fixed endpoints are `layeredStart I` at
layer zero and `layeredTarget I` at layer `n−1`. `layered_reachable_iff` preserves reachability,
including empty paths and early arrival, using a short finite path rather than a machine-time
hypothesis.

The `STCON.LayeredQuery`
separates `layeredQueryRequest` (binary dimensions and coordinates, with no input bit),
`layeredQueryIndex` (the original-input address), and `layeredEdgeQuery` (the Boolean answer
after supplying the optional read symbol). The fixed
`STCON.LayeredCallback`
`layeredCallback ntm` starts a call at `.inl request`, reads the original word and returns
`.inr answer` in one abstract step. `layeredCallback_agrees` identifies this answer with graph
adjacency. `layeredCallback_parts_inSpace` certifies native linear workspace for all five
components; `layeredCallback_states_le_log` bounds every call state logarithmically in the
original word length. The request is data, not part of the fixed machine code. The existing
`QueryMachine.withCalls` compiler supports the same-input call. These certificates do not
supply a complete streaming scan or its caller-state bounds; weight generation, scans and the
final class-equality composition remain open in #6747.

The [checked client](https://github.com/cslib-community/cslib-frontier/blob/97b9cf84a95029fd1647f8a0bf35500e938d16c9/CslibFrontierTests/LayeredNLReachability.lean) contains the imports,
empty-path, early-arrival and rejection cases, an actual native STCON witness, and a caller
resuming with the adjacency answer after call entry, read and return. Validate it with
`scripts/build.sh CslibFrontierTests.LayeredNLReachability --wfail --iofail`.


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
for all five components of `STCON.layeredCallback`, with read-only access to the original
input. Its one-step answer and every call-state size are included below. -/
theorem exists_layered_reachability_of_mem_NL {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ NL enc) :
    ∃ (k : ℕ) (State : Type) (inst : Fintype State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
      letI := inst
      ntm.DecidesInSpace enc A (fun a => c * (Nat.log2 (enc a).length + 1)) ∧
      (ComputableInSpace (STCON.layeredCallback ntm).query STCON.encLayeredCallback encNat
        (fun s => (STCON.encLayeredCallback s).length) ∧
      ComputableInSpace (STCON.layeredCallback ntm).next
        (QueryMachine.encStateRead STCON.encLayeredCallback) STCON.encLayeredCallback
        (fun p => (QueryMachine.encStateRead STCON.encLayeredCallback p).length) ∧
      ComputableInSpace (STCON.layeredCallback ntm).halted STCON.encLayeredCallback encBool
        (fun s => (STCON.encLayeredCallback s).length) ∧
      ComputableInSpace (STCON.layeredCallback ntm).emit
        (QueryMachine.encStateRead STCON.encLayeredCallback) encBits
        (fun p => (QueryMachine.encStateRead STCON.encLayeredCallback p).length) ∧
      ComputableInSpace (STCON.layeredCallback ntm).finish STCON.encLayeredCallback encBits
        (fun s => (STCON.encLayeredCallback s).length)) ∧
      ∀ a, let I := STCON.configurationInstance ntm c (enc a)
        (a ∈ A ↔ Relation.ReflTransGen (STCON.layeredRelation I)
          (STCON.layeredStart I) (STCON.layeredTarget I)) ∧
        Nat.card (STCON.LayeredGraphVertex I) ≤
          ((enc a).length + 2) ^
            (2 * (radixExponent State c * Fintype.card (Register k) + 1)) ∧
        ∀ u v : STCON.LayeredGraphVertex I,
          (∃ answer, (STCON.layeredCallback ntm).runFrom (enc a)
            (.inl (STCON.layeredQueryRequest ntm c (enc a) u v)) 1 = .inr answer ∧
            (answer = true ↔ STCON.layeredRelation I u v)) ∧
          ∀ t, (STCON.encLayeredCallback ((STCON.layeredCallback ntm).runFrom (enc a)
            (.inl (STCON.layeredQueryRequest ntm c (enc a) u v)) t)).length ≤
            12 * (radixExponent State c * Fintype.card (Register k) + 1) *
              (Nat.log2 ((enc a).length + 1) + 1) + 10 := by
  obtain ⟨k, State, hfin, ntm, c, hdec⟩ := hA
  let : Finite State := hfin
  let : Fintype State := Fintype.ofFinite State
  refine ⟨k, State, inferInstance, ntm, c, hdec, STCON.layeredCallback_parts_inSpace ntm, ?_⟩
  intro a
  exact ⟨(hdec.1 a).2.trans
      ((STCON.configurationInstance_mem_iff ntm c (hdec.1 a).1).symm.trans
        (STCON.layered_reachable_iff _).symm),
    STCON.card_configurationLayered_le_pow ntm c (enc a),
    fun u v => ⟨STCON.layeredCallback_agrees ntm c (enc a) u v,
      STCON.layeredCallback_states_le_log ntm c (enc a) u v⟩⟩

end Cslib.Complexity
