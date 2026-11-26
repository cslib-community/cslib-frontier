/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SoleLeaderDefs
import CslibFrontier.Computability.Distributed.Paxos.Liveness.StepFacts
import CslibFrontier.Computability.Distributed.Paxos.Liveness.SoleLeader
import CslibFrontier.Computability.Distributed.Paxos.Liveness.SoleLeaderSweep
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort

/-!
# Constructive sole-leader execution witness

Proves `exists_sole_leader_execution_crashStop`, constructing an explicit fair 4-phase execution
satisfying `LiveAndLossless` from any reachable crash-stop state.

## Main results

* `Cslib.Distributed.Paxos.exists_sole_leader_execution_crashStop`: constructive 4-phase execution
  witness from any reachable crash-stop state (with `[Finite Acceptor]`).
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib Cslib.ωSequence

section SoleLeader

variable {Proposer Acceptor Learner V : Type*}
  [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
  (qs : QuorumSystem Acceptor)

/-- Crash-stop constructive non-vacuity witness for `paxos_liveness_of_sole_leader_crashStop` (a
step towards [Lamport2001] §2.4 and [Lamport1998] §2.1 Theorem 2, not the crash-recovery cited
protocol): from any reachable crash-stop state `s₀` over `[Finite Acceptor]`, given live proposer
`p`, a live cohort `Q` satisfying `qs.Supports Q`, and live learner `l`, there exist a fresh round
`r` and a valid infinite execution starting from `s₀` (preparing `⟨r, p⟩` at step `0` and sweeping
ballot-`b` deliveries across `p`, `Q`, and `l`) satisfying `LiveAndLossless` in which `l` learns a
value `v` at ballot `⟨r, p⟩`. -/
theorem exists_sole_leader_execution_crashStop [Finite Acceptor] {inputs : Proposer → V}
    {s₀ : SynodState Proposer Acceptor Learner V}
    (hr₀ : Reachable qs inputs s₀)
    {p : Proposer} {Q : Finset Acceptor} {l : Learner}
    (hQ : qs.Supports Q)
    (hp_live : (s₀.proposers p).crashed = false)
    (hQ_live : ∀ a ∈ Q, (s₀.acceptors a).crashed = false)
    (hl_live : (s₀.learners l).crashed = false) :
    ∃ (r : ℕ) (ss : ωSequence (SynodState Proposer Acceptor Learner V))
      (xs : ωSequence (SynodAction Proposer Acceptor Learner V)) (k : ℕ) (v : V),
      ss 0 = s₀ ∧
      (synodLts qs).OmegaExecution ss xs ∧
      xs 0 = .prepare p r ∧
      BallotsBelow (ss 0) ⟨r, p⟩ ∧
      (∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ (⟨r, p⟩ : Ballot Proposer)) ∧
      LiveAndLossless ⟨r, p⟩ p Q l ss xs ∧
      (ss k).LearnedAt qs l ⟨r, p⟩ v ∧
      ((ss k).learners l).learned = some v := by
  let _ := Fintype.ofFinite Acceptor
  let msgBound := s₀.msgs.sup fun m => m.ballot.round + 1
  let accBound := (Finset.univ : Finset Acceptor).sup fun a =>
    match (s₀.acceptors a).maxBal with
    | none => 0
    | some mb => mb.round + 1
  let propBound := match (s₀.proposers p).round with
    | none => 0
    | some r₀ => r₀ + 1
  let r := max propBound (max msgBound accBound)
  let b : Ballot Proposer := ⟨r, p⟩
  have hbelow : BallotsBelow s₀ b := by
    refine ⟨fun m hm => (Ballot.lt_iff _ _).mpr (Or.inl ?_),
      fun a mb hmb => (Ballot.lt_iff _ _).mpr (Or.inl ?_)⟩
    · exact Nat.lt_of_succ_le ((Finset.le_sup (f := fun m : Msg Proposer Acceptor V =>
        m.ballot.round + 1) hm).trans (le_max_of_le_right (le_max_left _ _)))
    · have hsup := Finset.le_sup (s := Finset.univ) (f := fun a' : Acceptor =>
        match (s₀.acceptors a').maxBal with | none => 0 | some mb' => mb'.round + 1)
        (Finset.mem_univ a)
      simp only [hmb] at hsup
      exact Nat.lt_of_succ_le (hsup.trans (le_max_of_le_right (le_max_right _ _)))
  have hp_round_ok : match (s₀.proposers p).round with | none => True | some r₀ => r₀ < r := by
    cases hpr : (s₀.proposers p).round with
    | none => trivial
    | some r₀ =>
      simpa only [r, propBound, hpr, Nat.succ_le_iff] using
        le_max_left propBound (max msgBound accBound)
  let s₁ := synodStep qs s₀ (.prepare p r)
  have htr_prep : (synodLts qs).Tr s₀ (.prepare p r) s₁ := ⟨⟨hp_live, hp_round_ok⟩, rfl⟩
  let ts : ωSequence (SynodState Proposer Acceptor Learner V) :=
    ωSequence.mk (soleLeaderStateSeq qs b p Q l s₁)
  let xls : ωSequence (List (SynodAction Proposer Acceptor Learner V)) :=
    ωSequence.mk fun c => soleLeaderSweep b p Q l (ts c)
  have hts_live : ∀ c, ((ts c).proposers p).crashed = false ∧
      (∀ a ∈ Q, ((ts c).acceptors a).crashed = false) ∧
      ((ts c).learners l).crashed = false := by
    intro c
    induction c with
    | zero =>
      refine ⟨?_, hQ_live, hl_live⟩
      simp [ts, get_fun, soleLeaderStateSeq, s₁, synodStep, synodStepCore, hp_live]
    | succ c ih => exact (soleLeaderSweep_mTr qs ih.1 ih.2.1 ih.2.2 (b := b)).2
  have hts_mtr : ∀ c, (synodLts qs).MTr (ts c) (xls c) (ts (c + 1)) :=
    fun c => (soleLeaderSweep_mTr qs (hts_live c).1 (hts_live c).2.1 (hts_live c).2.2).1
  have hpos : ∀ c, 0 < (xls c).length := fun c => soleLeaderSweep_pos b p Q l (ts c)
  have : Inhabited (SynodAction Proposer Acceptor Learner V) := ⟨.stutter⟩
  obtain ⟨ss_tail, hexec_tail, hcum⟩ := LTS.OmegaExecution.flatten_mTr hts_mtr hpos
  let ss := s₀ ::ω ss_tail
  let xs := (SynodAction.prepare p r) ::ω xls.flatten
  have hexec : (synodLts qs).OmegaExecution ss xs :=
    LTS.OmegaExecution.cons htr_prep hexec_tail
      (by simpa only [cumLen_zero, ts, get_fun, soleLeaderStateSeq] using hcum 0)
  have htail_ok : ∀ m, IsSweepAct (xs (m + 1)) :=
    (forall_flatten_iff hpos IsSweepAct).mpr fun _ =>
      List.forall_iff_forall_mem.mpr fun _ => isSweepAct_of_mem_soleLeaderSweep
  have hxs_nodel : ∀ n, (∀ m, xs n ≠ .drop m) ∧ (∀ q, xs n ≠ .crashProposer q) ∧
      (∀ a, xs n ≠ .crashAcceptor a) ∧ (∀ l₀, xs n ≠ .crashLearner l₀) := fun
    | 0 => ⟨nofun, nofun, nofun, nofun⟩
    | m + 1 => (htail_ok m).2
  have hno_higher : ∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ b := by
    rintro (_ | m) q r' hj
    · injection hj with hq hr; subst hq hr; exact le_refl b
    · exact absurd hj ((htail_ok m).1 q r')
  have hss_inv : ∀ n, ((ss n).proposers p).crashed = false ∧
      (∀ a ∈ Q, ((ss n).acceptors a).crashed = false) ∧
      ((ss n).learners l).crashed = false := by
    intro n
    induction n with
    | zero => exact ⟨hp_live, hQ_live, hl_live⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := hxs_nodel n
      obtain ⟨_, hp, ha, hl⟩ := synodStep_preserve_of_delivery (qs := qs) (w := ss n) h1 h2 h3 h4
      rw [(hexec n).2]
      exact ⟨(hp p).trans ih.1, fun a haQ => (ha a).trans (ih.2.1 a haQ), (hl l).trans ih.2.2⟩
  have hmsgs_mono : ∀ {n j}, n ≤ j → (ss n).msgs ⊆ (ss j).msgs := by
    intro n j hle
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    induction d with
    | zero => exact Finset.Subset.rfl
    | succ d ih =>
      rw [← Nat.add_assoc, (hexec (n + d)).2]
      exact fun m hm => mem_msgs_synodStep_of_mem (ih (Nat.le_add_right n d) hm)
        ((hxs_nodel (n + d)).1 m)
  have hex_fair : ∀ n (m : Msg Proposer Acceptor V)
      (act : SynodAction Proposer Acceptor Learner V),
      m ∈ (ss n).msgs → act ∈ soleLeaderMsgActs b p Q l m →
      ∃ j, n ≤ j ∧ xs j = act := by
    intro n m act hm hact_m
    have hts_m : m ∈ (ts n).msgs :=
      (hcum n ▸ hmsgs_mono (Nat.le_succ_of_le ((cumLen_strictMono hpos).id_le n))) hm
    have hmem : act ∈ soleLeaderSweep b p Q l (ts n) :=
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨m, Finset.mem_toList.mpr hts_m, hact_m⟩)
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
    have hn_le : n ≤ xls.cumLen n := (cumLen_strictMono hpos).id_le n
    exact ⟨(xls.cumLen n + i) + 1, by omega, (xls.flatten_get_add hi hpos).trans hget⟩
  have hlive : LiveAndLossless b p Q l ss xs :=
    { proposer_live := fun n => (hss_inv n).1
      quorum_live := fun a haQ n => (hss_inv n).2.1 a haQ
      learner_live := fun n => (hss_inv n).2.2
      no_drop_ballot := fun n m hm => absurd hm ((hxs_nodel n).1 m)
      fair_phase1a := fun n hm a haQ =>
        hex_fair n (.phase1a b) (.recvPhase1a a b) hm (by simp [soleLeaderMsgActs, haQ])
      fair_phase1b := fun n a mv haQ hm =>
        hex_fair n (.phase1b a b mv) (.recvPhase1b p a b mv) hm (by simp [soleLeaderMsgActs, haQ])
      fair_phase2a := fun n v hm a haQ =>
        hex_fair n (.phase2a b v) (.recvPhase2a a b v) hm (by simp [soleLeaderMsgActs, haQ])
      fair_phase2b := fun n a v haQ hm =>
        hex_fair n (.phase2b a b v) (.recvPhase2b l a b v) hm (by simp [soleLeaderMsgActs, haQ]) }
  obtain ⟨k, v, hlearnedAt, hlearned⟩ :=
    paxos_liveness_of_sole_leader_crashStop qs hr₀ hexec hQ rfl hbelow hno_higher hlive
  exact ⟨r, ss, xs, k, v, rfl, hexec, rfl, hbelow, hno_higher, hlive, hlearnedAt, hlearned⟩

end SoleLeader

end Cslib.Distributed.Paxos
