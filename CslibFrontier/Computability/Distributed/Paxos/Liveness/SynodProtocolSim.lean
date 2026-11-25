/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SynodProtocol

/-!
# Internal simulation from `synodQuorumProtocol` to `synodLts`

Internal refinement invariant used only by `SynodProtocolCohort`; never re-exported through
`Liveness`.

## Main definitions

* `Cslib.Distributed.Paxos.netToSynod`: projection from `NetState` to `SynodState`.

## Main results

* `Cslib.Distributed.Paxos.netToSynod_reach`: reachability simulation into `synodLts`.
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib

/-- Projection from co-located `NetState` to `SynodState`. -/
@[expose] def netToSynod {P V : Type*} [DecidableEq P] [DecidableEq V]
    (s : NetState P (SynodNodeState P V) (Msg P P V) V) : SynodState P P P V where
  msgs := s.msgs.image Packet.body
  proposers p := (s.proc p).state.prop
  acceptors a := (s.proc a).state.acc
  learners l := (s.proc l).state.learn

/-- Body-projection identity for uniform all-node broadcast packets. -/
private lemma union_image_broadcastPairs {P M : Type*} [Fintype P] [DecidableEq P] [DecidableEq M]
    (pkts : Finset (Packet P M)) (p : P) (m : M) :
    (pkts ∪ (Finset.univ.image fun q : P => (q, m)).image fun db => ⟨p, db.1, db.2⟩).image
        Packet.body =
      insert m (pkts.image Packet.body) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_union, Finset.mem_insert, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨pkt, hold | ⟨db, ⟨q, rfl⟩, rfl⟩, rfl⟩
    exacts [Or.inr ⟨pkt, hold, rfl⟩, Or.inl rfl]
  · rintro (rfl | ⟨pkt, hold, rfl⟩)
    exacts [⟨⟨p, p, x⟩, Or.inr ⟨(p, x), ⟨p, rfl⟩, rfl⟩, rfl⟩, ⟨pkt, Or.inl hold, rfl⟩]

/-- Body-projection identity for singleton-destination outgoing packets. -/
private lemma union_image_singleton_pair {P M : Type*} [DecidableEq P] [DecidableEq M]
    (pkts : Finset (Packet P M)) (p q : P) (m : M) :
    (pkts ∪ ({(q, m)} : Finset (P × M)).image fun db => ⟨p, db.1, db.2⟩).image Packet.body =
      insert m (pkts.image Packet.body) := by
  ext x
  simp only [Finset.image_singleton, Finset.mem_image, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · rintro ⟨pkt, hold | rfl, rfl⟩
    exacts [Or.inr ⟨pkt, hold, rfl⟩, Or.inl rfl]
  · rintro (rfl | ⟨pkt, hold, rfl⟩)
    exacts [⟨⟨p, q, x⟩, Or.inr rfl, rfl⟩, ⟨pkt, Or.inl hold, rfl⟩]

/-- Decision output preservation across non-learning steps. -/
private lemma out_eq_after_nonlearn {V : Type*} (out learned : Option V)
    (h : out = learned) :
    (if out.isNone then none else out) = learned := by
  subst h; cases out <;> rfl

/-- Preserves `out = state.learn.learned` across non-learning `applyResult` updates. -/
private lemma out_preserved_of_nonlearn {P V : Type*} [DecidableEq P] [DecidableEq V]
    {s : NetState P (SynodNodeState P V) (Msg P P V) V}
    (hout : ∀ q, (s.proc q).out = (s.proc q).state.learn.learned)
    {dest : P} {nst : SynodNodeState P V} {out : Finset (P × Msg P P V)}
    (hl_eq : nst.learn.learned = (s.proc dest).state.learn.learned) :
    ∀ q, ((AsyncQuorumProtocol.applyResult dest
      { nextState := nst, outgoing := out, decideVal := none } s).proc q).out =
      ((AsyncQuorumProtocol.applyResult dest
        { nextState := nst, outgoing := out, decideVal := none }
          s).proc q).state.learn.learned := by
  intro q
  by_cases hqd : q = dest
  · subst hqd
    simp only [AsyncQuorumProtocol.applyResult, ↓reduceIte, hl_eq]
    exact out_eq_after_nonlearn _ _ (hout q)
  · simp only [AsyncQuorumProtocol.applyResult, hqd, ↓reduceIte]; exact hout q

/-- Commutation of `netToSynod` with `AsyncQuorumProtocol.applyResult`. -/
private lemma netToSynod_applyResult {P V : Type*} [DecidableEq P] [DecidableEq V]
    (s : NetState P (SynodNodeState P V) (Msg P P V) V)
    (dest : P) (res : StepResult P (SynodNodeState P V) (Msg P P V) V)
    (msgs' : Finset (Msg P P V))
    (hmsgs : (s.msgs ∪ res.outgoing.image fun db => ⟨dest, db.1, db.2⟩).image Packet.body =
      msgs') :
    netToSynod (AsyncQuorumProtocol.applyResult dest res s) =
      { msgs := msgs'
        proposers := fun x =>
          if x = dest then res.nextState.prop else (netToSynod s).proposers x
        acceptors := fun x =>
          if x = dest then res.nextState.acc else (netToSynod s).acceptors x
        learners := fun x =>
          if x = dest then res.nextState.learn else (netToSynod s).learners x } := by
  refine SynodState.ext hmsgs (funext fun x => ?_) (funext fun x => ?_) (funext fun x => ?_) <;>
    (dsimp only [netToSynod, AsyncQuorumProtocol.applyResult];
      by_cases hxd : x = dest <;> simp only [hxd, ↓reduceIte])

/-- Pointwise `if`-update simplification when the updated value equals the prior value. -/
private lemma ite_self_field {P α : Type*} [DecidableEq P] (f : P → α) (dest : P) {val : α}
    (hval : val = f dest) :
    (fun x => if x = dest then val else f x) = f := by
  funext x; by_cases h : x = dest <;> simp only [h, ↓reduceIte, hval]

/-- Projection and output invariance under no-op `applyResult`. -/
private lemma applyResult_noop_sim {P V : Type*} [DecidableEq P] [DecidableEq V]
    {s : NetState P (SynodNodeState P V) (Msg P P V) V}
    (hout : ∀ q, (s.proc q).out = (s.proc q).state.learn.learned) (dest : P) :
    let u := AsyncQuorumProtocol.applyResult dest
      { nextState := (s.proc dest).state, outgoing := ∅, decideVal := none } s
    (∀ q, (u.proc q).out = (u.proc q).state.learn.learned) ∧
      netToSynod u = netToSynod s := by
  refine ⟨out_preserved_of_nonlearn hout rfl, ?_⟩
  exact (netToSynod_applyResult s dest ⟨_, ∅, none⟩ (netToSynod s).msgs
    (by simp only [netToSynod, Finset.image_empty, Finset.union_empty])).trans
    (SynodState.ext rfl (ite_self_field _ dest rfl) (ite_self_field _ dest rfl)
      (ite_self_field _ dest rfl))

/-- Projection equation for an acceptor-only state update. -/
private lemma netToSynod_acc_update {P V : Type*} [DecidableEq P] [DecidableEq V]
    (s : NetState P (SynodNodeState P V) (Msg P P V) V)
    (dest : P) (ast : AcceptorState P V) (out : Finset (P × Msg P P V))
    (msgs' : Finset (Msg P P V))
    (hmsgs : (s.msgs ∪ out.image fun db => ⟨dest, db.1, db.2⟩).image Packet.body = msgs') :
    netToSynod (AsyncQuorumProtocol.applyResult dest
      { nextState := { (s.proc dest).state with acc := ast },
        outgoing := out, decideVal := none } s) =
      { (netToSynod s) with
        msgs := msgs'
        acceptors := fun x => if x = dest then ast else ((netToSynod s).acceptors x) } :=
  (netToSynod_applyResult s dest ⟨_, out, none⟩ msgs' hmsgs).trans
    (SynodState.ext rfl (ite_self_field _ dest rfl) rfl (ite_self_field _ dest rfl))

/-- Projection equation for a proposer-only state update. -/
private lemma netToSynod_prop_update {P V : Type*} [DecidableEq P] [DecidableEq V]
    (s : NetState P (SynodNodeState P V) (Msg P P V) V)
    (dest : P) (pst : ProposerState P P V) (out : Finset (P × Msg P P V))
    (msgs' : Finset (Msg P P V))
    (hmsgs : (s.msgs ∪ out.image fun db => ⟨dest, db.1, db.2⟩).image Packet.body = msgs') :
    netToSynod (AsyncQuorumProtocol.applyResult dest
      { nextState := { (s.proc dest).state with prop := pst },
        outgoing := out, decideVal := none } s) =
      { (netToSynod s) with
        msgs := msgs'
        proposers := fun x => if x = dest then pst else ((netToSynod s).proposers x) } :=
  (netToSynod_applyResult s dest ⟨_, out, none⟩ msgs' hmsgs).trans
    (SynodState.ext rfl rfl (ite_self_field _ dest rfl) (ite_self_field _ dest rfl))

/-- Step simulation for incoming acceptor packets (`Phase1a` and `Phase2a`). -/
private lemma netToSynod_acc_recv_sim {P V : Type*} [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P)
    (s : NetState P (SynodNodeState P V) (Msg P P V) V)
    (hout : ∀ q, (s.proc q).out = (s.proc q).state.learn.learned)
    (dest : P) (guard : Bool) (ast : AcceptorState P V) (out : Finset (P × Msg P P V))
    (emit : Msg P P V) (sact : SynodAction P P P V)
    (hen_live : (s.proc dest).state.acc.crashed = false → synodEnabled (netToSynod s) sact)
    (hstep_eq : synodStep qs (netToSynod s) sact =
      if guard then
        { (netToSynod s) with
          msgs := insert emit (netToSynod s).msgs
          acceptors := fun x => if x = dest then ast else (netToSynod s).acceptors x }
      else netToSynod s)
    (hmsgs : (s.msgs ∪ out.image fun db => ⟨dest, db.1, db.2⟩).image Packet.body =
      insert emit (netToSynod s).msgs) :
    let u := AsyncQuorumProtocol.applyResult dest
      (if (s.proc dest).state.acc.crashed = false ∧ guard = true then
        { nextState := { (s.proc dest).state with acc := ast }, outgoing := out, decideVal := none }
      else { nextState := (s.proc dest).state, outgoing := ∅, decideVal := none }) s
    (∀ q, (u.proc q).out = (u.proc q).state.learn.learned) ∧
      (netToSynod u = netToSynod s ∨
        ∃ sact', (synodLts qs).Tr (netToSynod s) sact' (netToSynod u)) := by
  by_cases hguard : (s.proc dest).state.acc.crashed = false ∧ guard = true
  · dsimp only []; rw [ite_eq_left hguard]
    refine ⟨out_preserved_of_nonlearn hout rfl, Or.inr ⟨sact, ⟨hen_live hguard.1, ?_⟩⟩⟩
    rw [hstep_eq, ite_eq_left hguard.2]
    exact netToSynod_acc_update s dest ast out _ hmsgs
  · dsimp only []; rw [ite_eq_right hguard]
    obtain ⟨ho, heq⟩ := applyResult_noop_sim hout dest
    by_cases hlive : (s.proc dest).state.acc.crashed = false
    · refine ⟨ho, Or.inr ⟨sact, ⟨hen_live hlive, ?_⟩⟩⟩
      rw [hstep_eq, ite_eq_right (fun hg => hguard ⟨hlive, hg⟩)]; exact heq
    · exact ⟨ho, Or.inl heq⟩

/-- Step simulation for incoming proposer/learner packets (`Phase1b` and `Phase2b`). -/
private lemma netToSynod_prop_recv_sim {P V : Type*} [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P)
    (s : NetState P (SynodNodeState P V) (Msg P P V) V)
    (hout : ∀ q, (s.proc q).out = (s.proc q).state.learn.learned)
    (src dest a : P) (crashed : Bool)
    (res : StepResult P (SynodNodeState P V) (Msg P P V) V)
    (sact : SynodAction P P P V)
    (hen_live : crashed = false → synodEnabled (netToSynod s) sact)
    (hres :
      (∀ q, ((AsyncQuorumProtocol.applyResult dest res s).proc q).out =
        ((AsyncQuorumProtocol.applyResult dest res s).proc q).state.learn.learned) ∧
      netToSynod (AsyncQuorumProtocol.applyResult dest res s) =
        synodStep qs (netToSynod s) sact) :
    let u := AsyncQuorumProtocol.applyResult dest
      (if crashed = false ∧ src = a then res
       else { nextState := (s.proc dest).state, outgoing := ∅, decideVal := none }) s
    (∀ q, (u.proc q).out = (u.proc q).state.learn.learned) ∧
      (netToSynod u = netToSynod s ∨
        ∃ sact', (synodLts qs).Tr (netToSynod s) sact' (netToSynod u)) := by
  by_cases hguard : crashed = false ∧ src = a
  · dsimp only []; rw [ite_eq_left hguard]
    exact ⟨hres.1, Or.inr ⟨sact, ⟨hen_live hguard.1, hres.2⟩⟩⟩
  · dsimp only []; rw [ite_eq_right hguard]
    obtain ⟨ho, heq⟩ := applyResult_noop_sim hout dest
    exact ⟨ho, Or.inl heq⟩

/-- Single-step simulation from `synodQuorumProtocol` to `synodLts`. -/
private lemma netToSynod_step {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P)
    {s s' : NetState P (SynodNodeState P V) (Msg P P V) V}
    {act : NetAction P ℕ (Msg P P V)}
    (htr : (synodQuorumProtocol qs).lts.Tr s act s')
    (hout : ∀ q, (s.proc q).out = (s.proc q).state.learn.learned) :
    (∀ q, (s'.proc q).out = (s'.proc q).state.learn.learned) ∧
      (netToSynod s' = netToSynod s ∨
        ∃ sact, (synodLts qs).Tr (netToSynod s) sact (netToSynod s')) := by
  cases act with
  | localStep p r =>
    obtain ⟨hen, rfl⟩ := htr
    exact ⟨out_preserved_of_nonlearn hout rfl,
      Or.inr ⟨.prepare p r, ⟨hen,
        netToSynod_prop_update s p _ _ _ (union_image_broadcastPairs s.msgs p _)⟩⟩⟩
  | deliver pkt =>
    obtain ⟨hpkt_mem, rfl⟩ := htr
    have hbody_mem : pkt.body ∈ (netToSynod s).msgs :=
      Finset.mem_image.mpr ⟨pkt, hpkt_mem, rfl⟩
    rcases pkt with ⟨src, dest, body⟩
    dsimp only [synodQuorumProtocol]
    cases body with
    | phase1a b =>
      exact netToSynod_acc_recv_sim qs s hout dest
        (aboveMaxBal (s.proc dest).state.acc.maxBal b)
        { (s.proc dest).state.acc with maxBal := some b }
        {(b.proposer, Msg.phase1b dest b (s.proc dest).state.acc.maxVoted)}
        (Msg.phase1b dest b (s.proc dest).state.acc.maxVoted)
        (.recvPhase1a dest b)
        (fun hlive => ⟨hlive, hbody_mem⟩) rfl
        (union_image_singleton_pair s.msgs dest b.proposer _)
    | phase1b a b mv =>
      refine netToSynod_prop_recv_sim qs s hout src dest a
        (s.proc dest).state.prop.crashed _ (.recvPhase1b dest a b mv)
        (fun hlive => ⟨hlive, hbody_mem⟩) ?_
      have hprop_ns : (netToSynod s).proposers dest = (s.proc dest).state.prop := rfl
      dsimp only [synodStep, synodStepCore]
      rw [hprop_ns]
      cases hround : (s.proc dest).state.prop.round with
      | none => exact applyResult_noop_sim hout dest
      | some r =>
        dsimp only []
        by_cases hnew : b = ⟨r, dest⟩ ∧ a ∉ (s.proc dest).state.prop.promised
        · rw [ite_eq_left hnew, ite_eq_left hnew]
          by_cases hq_cond : (!(s.proc dest).state.prop.proposed &&
              decide (∃ Q ∈ qs.prepareQuorums,
                Q ⊆ insert a (s.proc dest).state.prop.promised)) = true
          · rw [ite_eq_left hq_cond, ite_eq_left hq_cond]
            exact ⟨out_preserved_of_nonlearn hout rfl,
              netToSynod_prop_update s dest _
                (Finset.univ.image fun q => (q, Msg.phase2a ⟨r, dest⟩ _)) _
                (union_image_broadcastPairs s.msgs dest _)⟩
          · rw [ite_eq_right hq_cond, ite_eq_right hq_cond]
            exact ⟨out_preserved_of_nonlearn hout rfl,
              netToSynod_prop_update s dest _ ∅ _
                (by simp only [Finset.image_empty, Finset.union_empty]; rfl)⟩
        · rw [ite_eq_right hnew, ite_eq_right hnew]
          exact applyResult_noop_sim hout dest
    | phase2a b v =>
      exact netToSynod_acc_recv_sim qs s hout dest
        (allowsVote (s.proc dest).state.acc.maxBal b)
        { (s.proc dest).state.acc with maxBal := some b, maxVoted := some ⟨b, v⟩ }
        (Finset.univ.image fun q => (q, Msg.phase2b dest b v))
        (Msg.phase2b dest b v)
        (.recvPhase2a dest b v)
        (fun hlive => ⟨hlive, hbody_mem⟩) rfl
        (union_image_broadcastPairs s.msgs dest _)
    | phase2b a b v =>
      refine netToSynod_prop_recv_sim qs s hout src dest a
        (s.proc dest).state.learn.crashed _ (.recvPhase2b dest a b v)
        (fun hlive => ⟨hlive, hbody_mem⟩) ⟨fun q => ?_, ?_⟩
      · dsimp only [AsyncQuorumProtocol.applyResult]
        rcases eq_or_ne q dest with rfl | hqd
        · simp only [↓reduceIte]; rw [hout q]; cases (s.proc q).state.learn.learned <;> rfl
        · simp only [hqd, ↓reduceIte]; exact hout q
      · rw [netToSynod_applyResult s dest ⟨_, ∅, _⟩ (netToSynod s).msgs
          (by simp only [Finset.image_empty, Finset.union_empty]; rfl)]
        refine SynodState.ext rfl (ite_self_field _ dest rfl) (ite_self_field _ dest rfl)
          (funext fun x => ?_)
        dsimp only [synodStep, synodStepCore, netToSynod]
        by_cases hxd : x = dest <;> simp only [hxd, ↓reduceIte]
        congr
  | stutter => obtain rfl := htr; exact ⟨hout, Or.inl rfl⟩

/-- Reachability and output simulation from `synodQuorumProtocol` to `synodLts`. -/
lemma netToSynod_reach {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P) {inp : P → V}
    {s : NetState P (SynodNodeState P V) (Msg P P V) V}
    (hreach : (synodQuorumProtocol qs).Reachable inp s) :
    Reachable qs inp (netToSynod s) ∧
      ∀ q, (s.proc q).out = ((netToSynod s).learners q).learned := by
  obtain ⟨xl, hmtr⟩ := hreach
  have hgen : ∀ {u u' : NetState P (SynodNodeState P V) (Msg P P V) V} {yl},
      (synodQuorumProtocol qs).lts.MTr u yl u' →
      Reachable qs inp (netToSynod u) →
      (∀ q, (u.proc q).out = (u.proc q).state.learn.learned) →
      Reachable qs inp (netToSynod u') ∧
        ∀ q, (u'.proc q).out = (u'.proc q).state.learn.learned := by
    intro u u' yl hm
    induction hm with
    | refl => exact fun hr ho => ⟨hr, ho⟩
    | stepL hstep _ ih =>
      intro hr ho
      obtain ⟨ho', hsim⟩ := netToSynod_step qs hstep ho
      rcases hsim with heq | ⟨sact, hstr⟩
      exacts [ih (heq ▸ hr) ho', ih (hr.trans ⟨[sact], LTS.MTr.single _ hstr⟩) ho']
  have hinit_eq : netToSynod ((synodQuorumProtocol qs).start inp) = initState inp := by
    refine SynodState.ext ?_ rfl rfl rfl
    simp only [netToSynod, AsyncQuorumProtocol.start, Finset.image_empty, initState]
  have hr₀ : Reachable qs inp (netToSynod ((synodQuorumProtocol qs).start inp)) := by
    rw [hinit_eq]; exact ⟨[], LTS.MTr.refl⟩
  exact hgen hmtr hr₀ (fun _ => rfl)


end Cslib.Distributed.Paxos
