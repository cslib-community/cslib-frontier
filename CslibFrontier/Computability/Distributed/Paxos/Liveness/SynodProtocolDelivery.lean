/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SynodProtocol

/-!
# Internal packet fanout and fan-in delivery lemmas for `synodQuorumProtocol`

Internal multi-step delivery builders used only by `SynodProtocolCohort`; never re-exported
through `Liveness`.

## Main definitions

* `Cslib.Distributed.Paxos.AsyncQuorumProtocol.deliverStep`: single packet-delivery step.

## Main results

* `Cslib.Distributed.Paxos.deliver_fanout_acc`, `Cslib.Distributed.Paxos.deliver_fanin_leader`:
  cohort fanout and leader fan-in multi-step lemmas.
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib

namespace AsyncQuorumProtocol

variable {P S L M V : Type*} [DecidableEq P] [DecidableEq M]
  (π : AsyncQuorumProtocol P S L M V)

/-- Single packet-delivery transition step in `AsyncQuorumProtocol`. -/
@[expose] def deliverStep (s : NetState P S M V) (pkt : Packet P M) : NetState P S M V :=
  applyResult pkt.dest (π.onRecv pkt.src pkt.dest pkt.body (s.proc pkt.dest)) s

/-- Multi-step transition along a list of available packet deliveries. -/
private lemma mTr_map_deliver {α : Type*} (f : α → Packet P M) {u : NetState P S M V}
    {as : List α} (hmem : ∀ a ∈ as, f a ∈ u.msgs) :
    let u' := as.foldl (fun w a => π.deliverStep w (f a)) u
    π.lts.MTr u (as.map fun a => .deliver (f a)) u' ∧ u.msgs ⊆ u'.msgs := by
  induction as generalizing u with
  | nil => exact ⟨LTS.MTr.refl, Finset.Subset.rfl⟩
  | cons a rest ih =>
    have htr : π.lts.Tr u (.deliver (f a)) (π.deliverStep u (f a)) :=
      ⟨hmem a List.mem_cons_self, rfl⟩
    have hsub1 : u.msgs ⊆ (π.deliverStep u (f a)).msgs := Finset.subset_union_left
    obtain ⟨hmtr_r, hsub_r⟩ := ih (fun x hx => hsub1 (hmem x (List.mem_cons_of_mem a hx)))
    exact ⟨LTS.MTr.stepL htr hmtr_r, hsub1.trans hsub_r⟩


end AsyncQuorumProtocol

/-- One-to-many acceptor delivery fanout across a duplicate-free cohort list. -/
lemma deliver_fanout_acc {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P) (p₀ : P) (msg : Msg P P V)
    (acc₀ ast : AcceptorState P V) (reply : P → Msg P P V)
    (hrecv : ∀ (a : P) (st : NodeProcState (SynodNodeState P V) V),
      st.state.acc = acc₀ →
      ∃ out, (synodQuorumProtocol (V := V) qs).onRecv p₀ a msg st =
        { nextState := { st.state with acc := ast }, outgoing := out, decideVal := none } ∧
        (p₀, reply a) ∈ out)
    {as : List P} (hnodup : as.Nodup)
    {u : NetState P (SynodNodeState P V) (Msg P P V) V}
    (hall : ∀ x ∈ as, (⟨p₀, x, msg⟩ : Packet P (Msg P P V)) ∈ u.msgs ∧
      (u.proc x).state.acc = acc₀) :
    let π := synodQuorumProtocol (V := V) qs
    let u' := as.foldl (fun w a => π.deliverStep w ⟨p₀, a, msg⟩) u
    π.lts.MTr u (as.map fun a => .deliver ⟨p₀, a, msg⟩) u' ∧
      (∀ q, (u'.proc q).state.prop = (u.proc q).state.prop ∧
        (u'.proc q).state.learn = (u.proc q).state.learn) ∧
      (∀ x ∉ as, (u'.proc x).state.acc = (u.proc x).state.acc) ∧
      (∀ a ∈ as, (u'.proc a).state.acc = ast ∧
        (⟨a, p₀, reply a⟩ : Packet P (Msg P P V)) ∈ u'.msgs) := by
  let π := synodQuorumProtocol (V := V) qs
  refine ⟨(π.mTr_map_deliver (fun a => ⟨p₀, a, msg⟩) (fun x hx => (hall x hx).1)).1, ?_⟩
  induction hnodup generalizing u with
  | nil => exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | @cons a rest ha_not _ ih =>
    have ha_not' : a ∉ rest := fun h => ha_not a h rfl
    obtain ⟨out, hon, hrep_mem⟩ := hrecv a (u.proc a) (hall a List.mem_cons_self).2
    let w1 := π.deliverStep u ⟨p₀, a, msg⟩
    have hw1_pl : ∀ q, (w1.proc q).state.prop = (u.proc q).state.prop ∧
        (w1.proc q).state.learn = (u.proc q).state.learn := by
      intro q
      dsimp only [w1, AsyncQuorumProtocol.deliverStep, AsyncQuorumProtocol.applyResult]
      rw [hon]
      by_cases hqa : q = a <;> simp only [hqa, ↓reduceIte, and_self]
    have hw1_other : ∀ x, x ≠ a → (w1.proc x).state.acc = (u.proc x).state.acc := by
      intro x hxa
      dsimp only [w1, AsyncQuorumProtocol.deliverStep, AsyncQuorumProtocol.applyResult]
      simp only [hxa, ↓reduceIte]
    have hw1_a : (w1.proc a).state.acc = ast ∧
        (⟨a, p₀, reply a⟩ : Packet P (Msg P P V)) ∈ w1.msgs := by
      dsimp only [w1, AsyncQuorumProtocol.deliverStep, AsyncQuorumProtocol.applyResult]
      rw [hon, ite_eq_left rfl]
      exact ⟨rfl, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p₀, reply a), hrep_mem, rfl⟩)⟩
    have hall_r : ∀ x ∈ rest, (⟨p₀, x, msg⟩ : Packet P (Msg P P V)) ∈ w1.msgs ∧
        (w1.proc x).state.acc = acc₀ := fun x hx =>
      ⟨Finset.subset_union_left (hall x (List.mem_cons_of_mem a hx)).1,
        (hw1_other x fun h => ha_not' (h ▸ hx)).trans (hall x (List.mem_cons_of_mem a hx)).2⟩
    have ⟨_, hsub_r⟩ := π.mTr_map_deliver (u := w1) (fun x => ⟨p₀, x, msg⟩)
      (fun x hx => (hall_r x hx).1)
    obtain ⟨hpl_r, hnot_r, hin_r⟩ := ih hall_r
    refine ⟨fun q => ⟨(hpl_r q).1.trans (hw1_pl q).1, (hpl_r q).2.trans (hw1_pl q).2⟩,
      fun x hx => (hnot_r x fun h => hx (List.mem_cons_of_mem a h)).trans
        (hw1_other x fun h => hx (h ▸ List.mem_cons_self)),
      fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx_r
    · exact ⟨(hnot_r x ha_not').trans hw1_a.1, hsub_r hw1_a.2⟩
    · exact hin_r x hx_r

/-- Many-to-one delivery fan-in preserving an inductive cohort predicate. -/
lemma deliver_fanin_leader {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P) (p₀ : P) (msg : P → Msg P P V)
    (Inv : Finset P → NetState P (SynodNodeState P V) (Msg P P V) V → Prop)
    (hstep : ∀ (w : NetState P (SynodNodeState P V) (Msg P P V) V) (S : Finset P) (a : P),
      Inv S w → Inv (insert a S) ((synodQuorumProtocol (V := V) qs).deliverStep w ⟨a, p₀, msg a⟩))
    {as : List P} {u : NetState P (SynodNodeState P V) (Msg P P V) V} {S₀ : Finset P}
    (hmem : ∀ a ∈ as, (⟨a, p₀, msg a⟩ : Packet P (Msg P P V)) ∈ u.msgs)
    (hinv₀ : Inv S₀ u) :
    let π := synodQuorumProtocol (V := V) qs
    let u' := as.foldl (fun w a => π.deliverStep w ⟨a, p₀, msg a⟩) u
    π.lts.MTr u (as.map fun a => .deliver ⟨a, p₀, msg a⟩) u' ∧
      ∃ S', S₀ ⊆ S' ∧ (∀ a ∈ as, a ∈ S') ∧ Inv S' u' := by
  let π := synodQuorumProtocol (V := V) qs
  refine ⟨(π.mTr_map_deliver (fun a => ⟨a, p₀, msg a⟩) hmem).1, ?_⟩
  induction as generalizing u S₀ with
  | nil => exact ⟨S₀, Finset.Subset.rfl, fun _ h => absurd h List.not_mem_nil, hinv₀⟩
  | cons a rest ih =>
    obtain ⟨S', hsub, hin, hinv'⟩ :=
      ih (fun x hx => Finset.subset_union_left (hmem x (List.mem_cons_of_mem a hx)))
        (hstep u S₀ a hinv₀)
    refine ⟨S', (Finset.subset_insert a S₀).trans hsub, fun x hx => ?_, hinv'⟩
    rcases List.mem_cons.mp hx with rfl | hx_r
    · exact hsub (Finset.mem_insert_self x S₀)
    · exact hin x hx_r


end Cslib.Distributed.Paxos
