/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Digraph.Layered.Subdivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallBounds

/-!
# Native subdivision adjacency from a weight function and a read-only edge callee

The request carries binary vertex labels and chain offsets, together with caller context
such as dimensions and a seed. A fixed caller invokes the original graph's same-input edge
callee, then combines its returned bit with the source vertex's weight. The original input
is never stored in a caller state. Native certificates are relative to the supplied weight
routine and original-edge callee; constructing Hoza's weight routine remains in #6747.
-/

public section

namespace Cslib.LayeredDigraph.Subdivision

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- Coordinates of a subdivision edge, together with its dimensions/seed context. -/
structure Query (Context : Type) where
  /-- Compact parameters retained by the calling scan. -/
  context : Context
  /-- Original source vertex label in binary. -/
  fromLabel : ℕ
  /-- Original target vertex label in binary. -/
  toLabel : ℕ
  /-- Source chain offset in binary. -/
  fromOffset : ℕ
  /-- Target chain offset in binary. -/
  toOffset : ℕ

variable {Context : Type}

/-- Context and the first three binary coordinates are framed; target offset is last. -/
enc_structure encQuery (encContext : Context ↪ List Bool) : Query Context where
  context : encContext, fromLabel : encNat, toLabel : encNat,
  fromOffset : encNat, toOffset : encNat

/-- Decide a subdivision edge using the source weight and the original-edge answer. -/
@[expose] def edgeQuery (q : Query Context) (sourceWeight : ℕ) (baseEdge : Bool) : Bool :=
  ((q.fromLabel == q.toLabel) && (q.toOffset == q.fromOffset + 1) &&
    decide (q.toOffset ≤ sourceWeight)) ||
  ((q.fromOffset == sourceWeight) && (q.toOffset == 0) && baseEdge)

/-- The Boolean kernel agrees with the mathematical subdivision, including unused offsets. -/
theorem edgeQuery_agrees {n : ℕ} (G : LayeredDigraph (Fin n)) (weight : Fin n → ℕ)
    (bound : ℕ) (ctx : Context) (a b : Vertex (Fin n) bound) (baseEdge : Bool)
    (hbase : baseEdge = true ↔ G.Adj a.vertex b.vertex) :
    edgeQuery ⟨ctx, a.vertex.val, b.vertex.val, a.offset.val, b.offset.val⟩
      (weight a.vertex) baseEdge = true ↔ (graph G weight bound).Adj a b := by
  simp only [edgeQuery, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  rw [hbase]
  simp only [Fin.ext_iff, and_assoc]

variable {Context τ : Type} (encContext : Context ↪ List Bool) (encT : τ ↪ List Bool)

/-- Pending compact query or returned Boolean, preceded by one sum tag. -/
abbrev encCaller : Query Context ⊕ Bool ↪ List Bool := encSum (encQuery encContext) encBool

/-- A caller that returns its state, emits no stream, and waits for its sole edge call. -/
@[expose] def caller : QueryMachine (Query Context ⊕ Bool) where
  init := .inr false
  query _ := 0
  next p := p.1
  emit _ := []
  halted := Sum.elim (fun _ => false) (fun _ => true)
  finish _ := []

/-- Pending queries always request the original edge callee; answer states never call. -/
@[expose] def request (baseRequest : Query Context → τ) : Query Context ⊕ Bool → Option τ :=
  Sum.elim (fun q => some (baseRequest q)) (fun _ => none)

/-- Return to the caller with the subdivision answer, using the supplied weight routine. -/
@[expose] def resume (weight : Query Context → ℕ) (answer : τ → Bool)
    (s : Query Context ⊕ Bool) (t : τ) : Query Context ⊕ Bool :=
  s.elim (fun q => .inr (edgeQuery q (weight q) (answer t))) Sum.inr

/-- The native adjacency callback, with actual original-input reads delegated to `N`. -/
@[expose] def callback (N : QueryMachine τ) (baseRequest : Query Context → τ)
    (weight : Query Context → ℕ) (answer : τ → Bool) :=
  (caller (Context := Context)).withCalls N (request baseRequest) (resume weight answer)

/-- Caller and suspended-callee states, with the caller framed while a call is active. -/
abbrev encCallback := QueryMachine.encWithCalls (encCaller encContext) encT

/-- Running the supplied read-only callee returns the subdivision answer after its own
first-halting time plus call entry and return. No answer bit is assumed in the initial query. -/
theorem callback_runFrom (N : QueryMachine τ) (baseRequest : Query Context → τ)
    (weight : Query Context → ℕ) (answer : τ → Bool) (w : List Bool) (q : Query Context)
    (T : ℕ)
    (hpre : ∀ i < T, N.halted (N.runFrom w (baseRequest q) i) = false)
    (hhalt : N.halted (N.runFrom w (baseRequest q) T) = true) :
    (callback N baseRequest weight answer).runFrom w (.inl (.inl q)) (T + 2) =
      .inl (.inr (edgeQuery q (weight q) (answer (N.runFrom w (baseRequest q) T)))) :=
  QueryMachine.withCalls_runFrom_call caller N (request baseRequest) (resume weight answer)
    w (.inl q) (baseRequest q) T rfl rfl hpre hhalt

private theorem edgeQuery_budget {α : Type} {encA : α ↪ List Bool} {S : α → ℕ}
    {q : α → Query Context} {weight : α → ℕ} {edge : α → Bool}
    (hq : ComputableInSpace q encA (encQuery encContext) S)
    (hw : ComputableInSpace weight encA encNat S)
    (he : ComputableInSpace edge encA encBool S) :
    ComputableInSpace (fun a => edgeQuery (q a) (weight a) (edge a)) encA encBool S := by
  have hu := encQuery_fromLabel_budget encContext hq
  have hv := encQuery_toLabel_budget encContext hq
  have hi := encQuery_fromOffset_budget encContext hq
  have hj := encQuery_toOffset_budget encContext hq
  exact budget_boolOr
    (budget_boolAnd (budget_boolAnd (budget_natEq hu hv) (budget_natEq hj (budget_natSucc hi)))
      (budget_natLe hj hw))
    (budget_boolAnd (budget_boolAnd (budget_natEq hi hw) (budget_natIsZero hj)) he)

/-- Preparing the original edge request uses only the compact query. -/
private theorem request_inSpace (baseRequest : Query Context → τ)
    (hr : ComputableInSpace baseRequest (encQuery encContext) encT
      (fun q => (encQuery encContext q).length)) :
    ComputableInSpace (request baseRequest) (encCaller encContext) (encOption encT)
      (fun s => (encCaller encContext s).length) := by
  have hsome := budget_optionSome hr
  exact sumElim hsome (budget_const (encIn := encBool) none (.refl _))

/-- The return transition has native linear workspace relative to the supplied weight
routine and decoder for the original-edge callee's final state. -/
private theorem resume_inSpace (weight : Query Context → ℕ) (answer : τ → Bool)
    (hw : ComputableInSpace weight (encQuery encContext) encNat
      (fun q => (encQuery encContext q).length))
    (ha : ComputableInSpace answer encT encBool (fun t => (encT t).length)) :
    ComputableInSpace (fun p : (Query Context ⊕ Bool) × τ => resume weight answer p.1 p.2)
      (encPair (encCaller encContext) encT) (encCaller encContext)
      (fun p => (encPair (encCaller encContext) encT p).length) := by
  have hq := fst (encQuery encContext) encT
  have ht := snd (encQuery encContext) encT
  have hleft := edgeQuery_budget encContext hq (budget_comp_linear hw hq)
    (budget_comp_linear ha ht)
  have hinr := of_inO (ComputableInO.inr (encQuery encContext) encBool)
  exact sumElimFst (budget_comp_linear hinr hleft)
    (budget_comp_linear hinr (fst encBool encT))

/-- All five components of the same-input subdivision callback use linear compact-state
workspace, relative to the native weight routine and original-edge callee. The callee's
emissions and finish routine are discarded by the state-returning call and need no bounds. -/
theorem callback_parts_inSpace (N : QueryMachine τ) (baseRequest : Query Context → τ)
    (weight : Query Context → ℕ) (answer : τ → Bool)
    (hr : ComputableInSpace baseRequest (encQuery encContext) encT
      (fun q => (encQuery encContext q).length))
    (hw : ComputableInSpace weight (encQuery encContext) encNat
      (fun q => (encQuery encContext q).length))
    (ha : ComputableInSpace answer encT encBool (fun t => (encT t).length))
    (hnq : ComputableInSpace N.query encT encNat (fun t => (encT t).length))
    (hnn : ComputableInSpace N.next (QueryMachine.encStateRead encT) encT
      (fun p => (QueryMachine.encStateRead encT p).length))
    (hnh : ComputableInSpace N.halted encT encBool (fun t => (encT t).length)) :
    ComputableInSpace (callback N baseRequest weight answer).query
      (encCallback encContext encT) encNat (fun s => (encCallback encContext encT s).length) ∧
    ComputableInSpace (callback N baseRequest weight answer).next
      (QueryMachine.encStateRead (encCallback encContext encT)) (encCallback encContext encT)
      (fun p => (QueryMachine.encStateRead (encCallback encContext encT) p).length) ∧
    ComputableInSpace (callback N baseRequest weight answer).halted
      (encCallback encContext encT) encBool (fun s => (encCallback encContext encT s).length) ∧
    ComputableInSpace (callback N baseRequest weight answer).emit
      (QueryMachine.encStateRead (encCallback encContext encT)) encBits
      (fun p => (QueryMachine.encStateRead (encCallback encContext encT) p).length) ∧
    ComputableInSpace (callback N baseRequest weight answer).finish
      (encCallback encContext encT) encBits (fun s => (encCallback encContext encT s).length) := by
  let M := caller (Context := Context)
  let encS := encCaller encContext
  have hreq := request_inSpace encContext encT baseRequest hr
  have hres := resume_inSpace encContext encT weight answer hw ha
  have hmq : ComputableInSpace M.query encS encNat (fun s => (encS s).length) :=
    budget_const 0 (.refl _)
  have hmn : ComputableInSpace M.next (QueryMachine.encStateRead encS) encS
      (fun p => (QueryMachine.encStateRead encS p).length) := fst encS (encOption encBool)
  have hmh : ComputableInSpace M.halted encS encBool (fun s => (encS s).length) :=
    sumElim (budget_const (encIn := encQuery encContext) false (.refl _))
      (budget_const (encIn := encBool) true (.refl _))
  have hme : ComputableInSpace M.emit (QueryMachine.encStateRead encS) encBits
      (fun p => (QueryMachine.encStateRead encS p).length) := budget_const [] (.refl _)
  have hmf : ComputableInSpace M.finish encS encBits (fun s => (encS s).length) :=
    budget_const [] (.refl _)
  exact ⟨QueryMachine.withCalls_query_inSpace M N _ _ encS encT hmq hnq hreq,
    QueryMachine.withCalls_next_inSpace M N _ _ encS encT hmn hnn hnh hreq hres,
    QueryMachine.withCalls_halted_inSpace M N _ _ encS encT hmh,
    QueryMachine.withCalls_emit_inSpace M N _ _ encS encT hme hreq,
    QueryMachine.withCalls_finish_inSpace M N _ _ encS encT hmf⟩

/-- If the request has at most `C` bits and the base edge callee has at most `D` bits
through its first halt, the whole call has at most `2*C+D+6` bits through its return.
Thus logarithmic bounds compose without storing the original input. -/
theorem callback_states_le (N : QueryMachine τ) (baseRequest : Query Context → τ)
    (weight : Query Context → ℕ) (answer : τ → Bool) (w : List Bool) (q : Query Context)
    (T C D : ℕ)
    (hpre : ∀ i < T, N.halted (N.runFrom w (baseRequest q) i) = false)
    (hhalt : N.halted (N.runFrom w (baseRequest q) T) = true)
    (hq : (encQuery encContext q).length ≤ C)
    (hcallee : ∀ i ≤ T, (encT (N.runFrom w (baseRequest q) i)).length ≤ D)
    (t : ℕ) (ht : t ≤ T + 2) :
    (encCallback encContext encT ((callback N baseRequest weight answer).runFrom w
      (.inl (.inl q)) t)).length ≤ 2 * C + D + 6 := by
  have hc : (encCaller encContext (.inl q)).length ≤ C + 2 := by
    change (encQuery encContext q).length + 1 ≤ C + 2
    omega
  have hr : (encCaller encContext (resume weight answer (.inl q)
      (N.runFrom w (baseRequest q) T))).length ≤ C + 2 := by
    change 2 ≤ C + 2
    omega
  have h := QueryMachine.withCalls_runFrom_call_encoding_le caller N (request baseRequest)
    (resume weight answer) w (encCaller encContext) encT rfl rfl hpre hhalt hc hr hcallee t ht
  change (encCallback encContext encT ((callback N baseRequest weight answer).runFrom w
    (.inl (.inl q)) t)).length ≤ 2 * (C + 2) + D + 2 at h
  omega

end Cslib.LayeredDigraph.Subdivision
