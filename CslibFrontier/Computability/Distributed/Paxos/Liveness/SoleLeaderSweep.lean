/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Basic
import CslibFrontier.Computability.Distributed.Paxos.Liveness.StepFacts
import Mathlib.Data.Finset.Sort

/-!
# Internal fair message-delivery sweep helpers for sole-leader witness

Internal delivery-sweep construction used only by `SoleLeaderWitness`; never re-exported through
`Liveness`.

## Main definitions

* `Cslib.Distributed.Paxos.soleLeaderMsgActs`, `Cslib.Distributed.Paxos.soleLeaderSweep`,
  `Cslib.Distributed.Paxos.IsSweepAct`, `Cslib.Distributed.Paxos.soleLeaderStateSeq`: fair ballot
  delivery sweep builders.

## Main results

* `Cslib.Distributed.Paxos.soleLeaderSweep_pos`,
  `Cslib.Distributed.Paxos.isSweepAct_of_mem_soleLeaderSweep`,
  `Cslib.Distributed.Paxos.synodStep_preserve_of_delivery`,
  `Cslib.Distributed.Paxos.soleLeaderSweep_mTr`: sweep invariants and multi-step soundness.
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib

section SoleLeader

variable {Proposer Acceptor Learner V : Type*}
  [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
  (qs : QuorumSystem Acceptor)

/-- Internal delivery actions targeting ballot-`b` packets across `p`, `Q`, and `l`. -/
@[expose] noncomputable def soleLeaderMsgActs (b : Ballot Proposer) (p : Proposer)
    (Q : Finset Acceptor) (l : Learner) :
    Msg Proposer Acceptor V → List (SynodAction Proposer Acceptor Learner V)
  | .phase1a b' => if b' = b then Q.toList.map fun a => .recvPhase1a a b else []
  | .phase1b a b' mv => if b' = b ∧ a ∈ Q then [.recvPhase1b p a b mv] else []
  | .phase2a b' v => if b' = b then Q.toList.map fun a => .recvPhase2a a b v else []
  | .phase2b a b' v => if b' = b ∧ a ∈ Q then [.recvPhase2b l a b v] else []

/-- Finite delivery sweep over all messages in `u.msgs`, terminated by `.stutter`. -/
@[expose] noncomputable def soleLeaderSweep (b : Ballot Proposer) (p : Proposer)
    (Q : Finset Acceptor) (l : Learner)
    (u : SynodState Proposer Acceptor Learner V) :
    List (SynodAction Proposer Acceptor Learner V) :=
  u.msgs.toList.flatMap (soleLeaderMsgActs (Learner := Learner) b p Q l) ++ [.stutter]

omit [DecidableEq Learner] [DecidableEq V] in
/-- Every `soleLeaderSweep` action list is non-empty. -/
lemma soleLeaderSweep_pos (b : Ballot Proposer) (p : Proposer)
    (Q : Finset Acceptor) (l : Learner)
    (u : SynodState Proposer Acceptor Learner V) :
    0 < (soleLeaderSweep b p Q l u).length := by
  simp only [soleLeaderSweep, List.length_append, List.length_singleton]
  omega

omit [DecidableEq Learner] [DecidableEq V] in
/-- Membership characterization for `soleLeaderSweep`. -/
private lemma mem_soleLeaderSweep_cases {b : Ballot Proposer} {p : Proposer}
    {Q : Finset Acceptor} {l : Learner}
    {u : SynodState Proposer Acceptor Learner V}
    {act : SynodAction Proposer Acceptor Learner V}
    (hmem : act ∈ soleLeaderSweep b p Q l u) :
    act = .stutter ∨
      (∃ a ∈ Q, Msg.phase1a b ∈ u.msgs ∧ act = .recvPhase1a a b) ∨
      (∃ a ∈ Q, ∃ mv, Msg.phase1b a b mv ∈ u.msgs ∧ act = .recvPhase1b p a b mv) ∨
      (∃ a ∈ Q, ∃ v, Msg.phase2a b v ∈ u.msgs ∧ act = .recvPhase2a a b v) ∨
      (∃ a ∈ Q, ∃ v, Msg.phase2b a b v ∈ u.msgs ∧ act = .recvPhase2b l a b v) := by
  simp only [soleLeaderSweep, soleLeaderMsgActs, List.mem_append, List.mem_singleton,
    List.mem_flatMap, Finset.mem_toList] at hmem
  rcases hmem with ⟨m, hm_msgs, hm_act⟩ | rfl
  · cases m with
    | phase1a b' =>
      dsimp only at hm_act
      split_ifs at hm_act with hb
      · subst hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm_act
        exact Or.inr (Or.inl ⟨a, Finset.mem_toList.mp ha, hm_msgs, rfl⟩)
      · cases hm_act
    | phase1b a b' mv =>
      dsimp only at hm_act
      split_ifs at hm_act with hba
      · obtain ⟨rfl, haQ⟩ := hba
        rw [List.mem_singleton] at hm_act
        exact Or.inr (Or.inr (Or.inl ⟨a, haQ, mv, hm_msgs, hm_act⟩))
      · cases hm_act
    | phase2a b' v =>
      dsimp only at hm_act
      split_ifs at hm_act with hb
      · subst hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm_act
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, Finset.mem_toList.mp ha, v, hm_msgs, rfl⟩)))
      · cases hm_act
    | phase2b a b' v =>
      dsimp only at hm_act
      split_ifs at hm_act with hba
      · obtain ⟨rfl, haQ⟩ := hba
        rw [List.mem_singleton] at hm_act
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, haQ, v, hm_msgs, hm_act⟩)))
      · cases hm_act
  · exact Or.inl rfl

/-- Delivery-only actions that neither prepare new rounds, drop packets, nor crash nodes. -/
@[expose] def IsSweepAct (act : SynodAction Proposer Acceptor Learner V) : Prop :=
  (∀ q r', act ≠ .prepare q r') ∧ (∀ m, act ≠ .drop m) ∧
    (∀ q, act ≠ .crashProposer q) ∧ (∀ a, act ≠ .crashAcceptor a) ∧
    (∀ l₀, act ≠ .crashLearner l₀)

omit [DecidableEq Learner] [DecidableEq V] in
/-- Every action in `soleLeaderSweep` satisfies `IsSweepAct`. -/
lemma isSweepAct_of_mem_soleLeaderSweep {b : Ballot Proposer} {p : Proposer}
    {Q : Finset Acceptor} {l : Learner} {u : SynodState Proposer Acceptor Learner V}
    {act : SynodAction Proposer Acceptor Learner V}
    (hmem : act ∈ soleLeaderSweep b p Q l u) : IsSweepAct act := by
  rcases mem_soleLeaderSweep_cases hmem with rfl | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    exact ⟨nofun, nofun, nofun, nofun, nofun⟩

/-- Any non-drop, non-crash action preserves `msgs` monotonicity and node liveness. -/
lemma synodStep_preserve_of_delivery {w : SynodState Proposer Acceptor Learner V}
    {act : SynodAction Proposer Acceptor Learner V}
    (hnodrop : ∀ m, act ≠ .drop m)
    (hnocp : ∀ q, act ≠ .crashProposer q)
    (hnoca : ∀ a, act ≠ .crashAcceptor a)
    (hnocl : ∀ l₀, act ≠ .crashLearner l₀) :
    let w' := synodStep qs w act
    w.msgs ⊆ w'.msgs ∧
      (∀ q, (w'.proposers q).crashed = (w.proposers q).crashed) ∧
      (∀ a, (w'.acceptors a).crashed = (w.acceptors a).crashed) ∧
      (∀ l₀, (w'.learners l₀).crashed = (w.learners l₀).crashed) := by
  refine ⟨fun m hm => mem_msgs_synodStep_of_mem hm (hnodrop m), fun q => ?_, fun a => ?_,
    fun l₀ => ?_⟩
  · rcases proposers_synodStep_cases qs w act q with heq | ⟨_, _, heq⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, heq, _⟩ | ⟨_, _, _, _, _, _, _, _, _, heq⟩ | ⟨hact, _⟩
    · rw [heq]
    · rw [heq]
    · rw [heq]
    · rw [heq]
    · exact absurd hact (hnocp q)
  · rcases acceptors_synodStep_cases qs w act a with heq | ⟨_, _, _, heq, _⟩ |
        ⟨_, _, _, _, heq⟩ | ⟨hact, _⟩
    · rw [heq]
    · rw [heq]
    · rw [heq]
    · exact absurd hact (hnoca a)
  · rcases learners_synodStep_cases qs w act l₀ with heq | ⟨_, _, _, _, heq⟩ | ⟨hact, _⟩
    · rw [heq]
    · rw [heq]
    · exact absurd hact (hnocl l₀)

/-- Valid multi-step transition and liveness preservation across one `soleLeaderSweep`. -/
lemma soleLeaderSweep_mTr {b : Ballot Proposer} {p : Proposer}
    {Q : Finset Acceptor} {l : Learner}
    {u : SynodState Proposer Acceptor Learner V}
    (hp_live : (u.proposers p).crashed = false)
    (hQ_live : ∀ a ∈ Q, (u.acceptors a).crashed = false)
    (hl_live : (u.learners l).crashed = false) :
    let u' := (soleLeaderSweep b p Q l u).foldl (synodStep qs) u
    (synodLts qs).MTr u (soleLeaderSweep b p Q l u) u' ∧
      (u'.proposers p).crashed = false ∧
      (∀ a ∈ Q, (u'.acceptors a).crashed = false) ∧
      (u'.learners l).crashed = false := by
  have hloop : ∀ (acts : List (SynodAction Proposer Acceptor Learner V)),
      (∀ act ∈ acts, act ∈ soleLeaderSweep b p Q l u) →
      ∀ (w : SynodState Proposer Acceptor Learner V),
      u.msgs ⊆ w.msgs →
      (w.proposers p).crashed = false →
      (∀ a ∈ Q, (w.acceptors a).crashed = false) →
      (w.learners l).crashed = false →
      let w' := acts.foldl (synodStep qs) w
      (synodLts qs).MTr w acts w' ∧
        (w'.proposers p).crashed = false ∧
        (∀ a ∈ Q, (w'.acceptors a).crashed = false) ∧
        (w'.learners l).crashed = false := by
    intro acts hacts
    induction acts with
    | nil => exact fun _ _ hpw hQw hlw => ⟨LTS.MTr.refl, hpw, hQw, hlw⟩
    | cons act rest ih =>
      intro w hsub hpw hQw hlw
      have hmem := hacts act List.mem_cons_self
      have hen : synodEnabled w act := by
        rcases mem_soleLeaderSweep_cases hmem with rfl | ⟨a, haQ, hm, rfl⟩ |
            ⟨a, haQ, _, hm, rfl⟩ | ⟨a, haQ, _, hm, rfl⟩ | ⟨a, haQ, _, hm, rfl⟩
        · trivial
        · exact ⟨hQw a haQ, hsub hm⟩
        · exact ⟨hpw, hsub hm⟩
        · exact ⟨hQw a haQ, hsub hm⟩
        · exact ⟨hlw, hsub hm⟩
      have hsw := isSweepAct_of_mem_soleLeaderSweep hmem
      have hpres := synodStep_preserve_of_delivery (qs := qs) (w := w) (act := act)
        hsw.2.1 hsw.2.2.1 hsw.2.2.2.1 hsw.2.2.2.2
      obtain ⟨hmtr_r, hpw', hQw', hlw'⟩ := ih
        (fun x hx => hacts x (List.mem_cons_of_mem act hx))
        (synodStep qs w act) (hsub.trans hpres.1)
        ((hpres.2.1 p).trans hpw)
        (fun a haQ => (hpres.2.2.1 a).trans (hQw a haQ))
        ((hpres.2.2.2 l).trans hlw)
      exact ⟨LTS.MTr.stepL ⟨hen, rfl⟩ hmtr_r, hpw', hQw', hlw'⟩
  exact hloop (soleLeaderSweep b p Q l u) (fun _ h => h) u Finset.Subset.rfl
    hp_live hQ_live hl_live

/-- Infinite sequence of post-sweep configurations for constructive sole-leader execution. -/
@[expose] noncomputable def soleLeaderStateSeq (qs : QuorumSystem Acceptor) (b : Ballot Proposer)
    (p : Proposer) (Q : Finset Acceptor) (l : Learner)
    (s₁ : SynodState Proposer Acceptor Learner V) :
    ℕ → SynodState Proposer Acceptor Learner V
  | 0 => s₁
  | c + 1 => (soleLeaderSweep b p Q l (soleLeaderStateSeq qs b p Q l s₁ c)).foldl
      (synodStep qs) (soleLeaderStateSeq qs b p Q l s₁ c)


end SoleLeader

end Cslib.Distributed.Paxos
