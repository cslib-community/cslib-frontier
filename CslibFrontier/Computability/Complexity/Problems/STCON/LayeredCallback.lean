/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallSpace

/-!
# A uniform one-read adjacency callee

The fixed query machine starts a call from `.inl q`, reads the original input at the certified
index, and returns `.inr answer` after exactly one step. The request is data, not part of the
machine code. The dummy initializer is already halted; callers use `QueryMachine.withCalls`
with the explicitly requested state. Calls return the answer state and emit no stream.

All five machine components have native compact-state workspace certificates. Every state
of a call is bounded by the pending query's encoded length plus two. Thus the logarithmic
query-size bound supplies the actual read-only call interface needed by #6747's scans.

## Main results

* `Cslib.Complexity.STCON.layeredCallback_runFrom`: one real input read returns the answer.
* `Cslib.Complexity.STCON.layeredCallback_agrees`: the returned bit decides graph adjacency.
* `Cslib.Complexity.STCON.layeredCallback_parts_inSpace`: native certificates for all components.
* `Cslib.Complexity.STCON.layeredCallback_states_le_log`: logarithmic states throughout a call.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
  _root_.Turing.MultiTapeNTM.ConfigurationGraph

/-- One sum tag followed by a pending binary query or the one-bit returned answer. -/
abbrev encLayeredCallback : LayeredQuery ⊕ Bool ↪ List Bool := encSum encLayeredQuery encBool

variable {k : ℕ} {State : Type} [Fintype State]

/-- A state-returning, one-read callee. Its component code depends only on the fixed source
machine, never on the query or original input. -/
@[expose] noncomputable def layeredCallback (ntm : MultiTapeNTM k Bool State) :
    QueryMachine (LayeredQuery ⊕ Bool) where
  init := .inr false
  query := Sum.elim (layeredQueryIndex (k := k)) (fun _ => 0)
  next p := p.1.elim
    (fun q => .inr (layeredEdgeQuery ntm {q with symbol := p.2})) Sum.inr
  emit _ := []
  halted := Sum.elim (fun _ => false) (fun _ => true)
  finish _ := []

/-- A call reads its bit from the actual original word, including the `none` response past
its end. After that step the answer state is fixed. -/
theorem layeredCallback_runFrom (ntm : MultiTapeNTM k Bool State) (w : List Bool)
    (q : LayeredQuery) (t : ℕ) :
    (layeredCallback ntm).runFrom w (.inl q) (t + 1) =
      .inr (layeredEdgeQuery ntm {q with symbol := w[layeredQueryIndex (k := k) q]?}) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [QueryMachine.runFrom_succ, ih]; rfl

/-- Starting from coordinates alone, the callee returns exactly the mathematical adjacency
answer. No pre-read input bit is supplied in the pending request. -/
theorem layeredCallback_agrees (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (a b : LayeredGraphVertex (configurationInstance ntm c w)) :
    ∃ answer, (layeredCallback ntm).runFrom w (.inl (layeredQueryRequest ntm c w a b)) 1 =
      .inr answer ∧ (answer = true ↔ layeredRelation (configurationInstance ntm c w) a b) := by
  exact ⟨_, layeredCallback_runFrom ntm w _ 0, layeredQuery_agrees ntm c w a b⟩

private theorem call_state_length_le (ntm : MultiTapeNTM k Bool State) (w : List Bool)
    (q : LayeredQuery) (t : ℕ) :
    (encLayeredCallback ((layeredCallback ntm).runFrom w (.inl q) t)).length ≤
      (encLayeredQuery q).length + 2 := by
  cases t with
  | zero => change (encLayeredQuery q).length + 1 ≤ _; omega
  | succ t => rw [layeredCallback_runFrom]; change 2 ≤ _; omega

/-- Every state, before and after the native read, has logarithmic encoded length for valid
graph coordinates. The constants depend only on the fixed native source and its space bound. -/
theorem layeredCallback_states_le_log (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (a b : LayeredGraphVertex (configurationInstance ntm c w)) (t : ℕ) :
    (encLayeredCallback ((layeredCallback ntm).runFrom w
      (.inl (layeredQueryRequest ntm c w a b)) t)).length ≤
      12 * (radixExponent State c * Fintype.card (Register k) + 1) *
        (Nat.log2 (w.length + 1) + 1) + 10 := by
  have h := length_layeredQuery_le_log ntm c w a b none
  change (encLayeredQuery (layeredQueryRequest ntm c w a b)).length ≤ _ at h
  exact (call_state_length_le ntm w _ t).trans (by omega)

/-- All components of the uniform callee use native workspace linear in the compact state.
These are the five hypotheses consumed by the existing query-machine and same-input-call
compilers; no source word is part of the encoded state. -/
theorem layeredCallback_parts_inSpace (ntm : MultiTapeNTM k Bool State) :
    ComputableInSpace (layeredCallback ntm).query encLayeredCallback encNat
      (fun s => (encLayeredCallback s).length) ∧
    ComputableInSpace (layeredCallback ntm).next (QueryMachine.encStateRead encLayeredCallback)
      encLayeredCallback (fun p => (QueryMachine.encStateRead encLayeredCallback p).length) ∧
    ComputableInSpace (layeredCallback ntm).halted encLayeredCallback encBool
      (fun s => (encLayeredCallback s).length) ∧
    ComputableInSpace (layeredCallback ntm).emit (QueryMachine.encStateRead encLayeredCallback)
      encBits (fun p => (QueryMachine.encStateRead encLayeredCallback p).length) ∧
    ComputableInSpace (layeredCallback ntm).finish encLayeredCallback encBits
      (fun s => (encLayeredCallback s).length) := by
  have hquery := sumElim (layeredQueryIndex_inSpace (k := k))
    (budget_const (encIn := encBool) 0 (.refl _))
  have hhalt := sumElim
    (budget_const (encIn := encLayeredQuery) (encB := encBool) false (.refl _))
    (budget_const (encIn := encBool) true (.refl _))
  have hq := fst encLayeredQuery (encOption encBool)
  have hs := snd encLayeredQuery (encOption encBool)
  have hupdate := encLayeredQuery_mk_budget
    (encLayeredQuery_radix_budget hq) (encLayeredQuery_inputLength_budget hq)
    (encLayeredQuery_fromLayer_budget hq) (encLayeredQuery_fromLabel_budget hq)
    (encLayeredQuery_toLayer_budget hq) (encLayeredQuery_toLabel_budget hq) hs
  have hinr := of_inO (ComputableInO.inr encLayeredQuery encBool)
  have hleft := budget_comp_linear hinr
    (budget_comp_linear (layeredEdgeQuery_inSpace ntm) hupdate)
  have hright := budget_comp_linear hinr (fst encBool (encOption encBool))
  have hnext := sumElimFst hleft hright
  exact ⟨hquery, hnext, hhalt, budget_const [] (.refl _), budget_const [] (.refl _)⟩

end Cslib.Complexity.STCON
