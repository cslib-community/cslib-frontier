/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SoleLeaderDefs
import CslibFrontier.Computability.Distributed.Paxos.Liveness.StepFacts
import CslibFrontier.Computability.Distributed.Paxos.Liveness.SoleLeaderInvariants
import Mathlib.Data.Nat.Order.Lemmas

/-!
# Conditional sole-leader 4-phase progress steps

Proves `paxos_liveness_from_phase2a_crashStop` (Phase 2 progress using only an accept quorum) and
`paxos_liveness_of_sole_leader_crashStop` (conditional 4-phase crash-stop progress under a fresh
sole-leader ballot).

## Main results

* `Cslib.Distributed.Paxos.paxos_liveness_from_phase2a_crashStop`: phase-2 progress using only
  an accept quorum after the proposal is sent, without requiring a live prepare quorum.
* `Cslib.Distributed.Paxos.paxos_liveness_of_sole_leader_crashStop`: conditional crash-stop 4-phase
  learner termination step under a live sole leader at a fresh highest ballot.
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib Cslib.ωSequence

section SoleLeader

variable {Proposer Acceptor Learner V : Type*}
  [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
  (qs : QuorumSystem Acceptor)

/-- Crash-stop phase-2 progress after a proposal has been sent: an accept quorum suffices,
even if no prepare quorum remains live. With no higher promise on that quorum and fair delivery
of the proposal and its votes, a reachable execution eventually records the proposal at the
learner. No proposer liveness or delivery of phase-1 messages is required. This is a phase-2
step after [HowardMalkhiSpiegelman2017], §§3–4.1, in the crash-stop model; persistent-storage
recovery and Multi-Paxos remain outside this kernel (issue #7207). -/
theorem paxos_liveness_from_phase2a_crashStop {inputs : Proposer → V}
    {ss : ωSequence (SynodState Proposer Acceptor Learner V)}
    {xs : ωSequence (SynodAction Proposer Acceptor Learner V)}
    (hr₀ : Reachable qs inputs (ss 0))
    (hexec : (synodLts qs).OmegaExecution ss xs)
    {b : Ballot Proposer} {Q : Finset Acceptor} {l : Learner}
    (hQ : Q ∈ qs.acceptQuorums)
    (hbound : ∀ n a, a ∈ Q → ∀ mb,
      ((ss n).acceptors a).maxBal = some mb → mb ≤ b)
    (hphase2a : ∀ n v, Msg.phase2a b v ∈ (ss n).msgs →
      ∀ a ∈ Q, ∃ j, n ≤ j ∧ xs j = .recvPhase2a a b v)
    (hphase2b : ∀ n a v, a ∈ Q → Msg.phase2b a b v ∈ (ss n).msgs →
      ∃ j, n ≤ j ∧ xs j = .recvPhase2b l a b v)
    {n₂ : ℕ} {v : V} (h2a_mem : Msg.phase2a b v ∈ (ss n₂).msgs) :
    ∃ k, (ss k).LearnedAt qs l b v ∧ ((ss k).learners l).learned = some v := by
  have hQ_recv : ∀ a ∈ Q, ∃ n, ⟨a, b, v⟩ ∈ ((ss n).learners l).received := by
    intro a haQ
    obtain ⟨j₃, _, hj₃_act⟩ := hphase2a n₂ v h2a_mem a haQ
    have hallows_j₃ : allowsVote ((ss j₃).acceptors a).maxBal b = true := by
      cases hmb : ((ss j₃).acceptors a).maxBal with
      | none => rfl
      | some mb => simp only [allowsVote, decide_eq_true_eq, hbound j₃ a haQ mb hmb]
    have h2b_mem : Msg.phase2b a b v ∈ (ss (j₃ + 1)).msgs := by
      simp only [(hexec j₃).2, hj₃_act, synodStep, synodStepCore, hallows_j₃, ↓reduceIte,
        Finset.mem_insert_self]
    obtain ⟨j₄, _, hj₄_act⟩ := hphase2b (j₃ + 1) a v haQ h2b_mem
    exact ⟨j₄ + 1, by simp [(hexec j₄).2, hj₄_act, synodStep, synodStepCore]⟩
  let recvStep : Acceptor → ℕ := fun a =>
    if h : a ∈ Q then Classical.choose (hQ_recv a h) else 0
  let k_final := Q.sup recvStep
  have hlearnedAt : (ss k_final).LearnedAt qs l b v := by
    refine ⟨Q, hQ, fun a haQ => ?_⟩
    have hle : Classical.choose (hQ_recv a haQ) ≤ k_final := by
      simpa only [recvStep, dite_eq_left haQ] using Finset.le_sup (f := recvStep) haQ
    exact learner_received_mono qs hexec hle (Classical.choose_spec (hQ_recv a haQ))
  have hr_final : Reachable qs inputs (ss k_final) :=
    hr₀.trans ⟨xs.extract 0 k_final, hexec.extract_mTr (Nat.zero_le k_final)⟩
  exact ⟨k_final, hlearnedAt, hr_final.learned_eq_some_iff.mpr ⟨b, hlearnedAt⟩⟩

/-- Conditional crash-stop 4-phase progress step towards [Lamport2001] §2.4 and [Lamport1998] §2.1
Theorem 2 / §2.4, and **not** the crash-recovery or timeout-based leader-election liveness result:
assuming an already-selected sole leader `p` (without modeling leader election, NACK `nextBal[q]`
ballot-bumping, persistent-storage crash recovery, or real-time timeout bounds), from any reachable
crash-stop Synod state `ss 0`, if live proposer `p` issues `prepare p r` at step `0` with ballot
`b = ⟨r, p⟩` strictly exceeding all ballots previously present or promised
(`BallotsBelow (ss 0) b`), no ballot strictly greater than `b` is subsequently prepared, and
ballot-`b` packets among `p`, a live cohort `Q` containing a quorum of each phase
(`qs.Supports Q`), and live learner `l` are delivered
without loss (`LiveAndLossless b p Q l ss xs`), then `l` eventually learns a decree value `v` at
ballot `b` (and `((ss k).learners l).learned = some v`). -/
theorem paxos_liveness_of_sole_leader_crashStop {inputs : Proposer → V}
    {ss : ωSequence (SynodState Proposer Acceptor Learner V)}
    {xs : ωSequence (SynodAction Proposer Acceptor Learner V)}
    (hr₀ : Reachable qs inputs (ss 0))
    (hexec : (synodLts qs).OmegaExecution ss xs)
    {p : Proposer} {r : ℕ} {Q : Finset Acceptor} {l : Learner}
    (hQ : qs.Supports Q)
    (hprep₀ : xs 0 = .prepare p r)
    (hbelow : BallotsBelow (ss 0) ⟨r, p⟩)
    (hno_higher : ∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ (⟨r, p⟩ : Ballot Proposer))
    (hlive : LiveAndLossless ⟨r, p⟩ p Q l ss xs) :
    ∃ k v, (ss k).LearnedAt qs l ⟨r, p⟩ v ∧ ((ss k).learners l).learned = some v := by
  obtain ⟨⟨Q₁, hQ₁, hQ₁_sub⟩, ⟨Q₂, hQ₂, hQ₂_sub⟩⟩ := hQ
  set b : Ballot Proposer := ⟨r, p⟩
  have hceil := ballot_ceiling_inv qs hexec hbelow hno_higher
  have hround_inv := sole_leader_round_inv qs hexec hprep₀ hno_higher
  have hs1_1a : Msg.phase1a b ∈ (ss 1).msgs := by
    rw [(hexec 0).2, hprep₀]; exact Finset.mem_insert_self _ _
  have ⟨hs1_prop_false, hs1_prom_empty⟩ :
      ((ss 1).proposers p).proposed = false ∧ ((ss 1).proposers p).promised = ∅ := by
    simp only [(hexec 0).2, hprep₀, synodStep, synodStepCore, ↓reduceIte, and_self]
  -- Phase 1a → 1b → 2a: prove `∃ n₂ ≥ 1, ∃ v, Msg.phase2a b v ∈ (ss n₂).msgs`.
  have hexists_2a : ∃ n₂ v, 1 ≤ n₂ ∧ Msg.phase2a b v ∈ (ss n₂).msgs := by
    by_cases hprop_ever : ∃ n, 1 ≤ n ∧ ((ss n).proposers p).proposed = true
    · obtain ⟨n_wit, hn_wit, htrue_wit⟩ := hprop_ever
      obtain ⟨d_wit, rfl⟩ := Nat.exists_eq_add_of_le hn_wit
      obtain ⟨d, hd_not, hd_true⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
        (p := fun d => ((ss (1 + d)).proposers p).proposed = true)
        (by simp only [Nat.add_zero, hs1_prop_false, Bool.false_eq_true, not_false_eq_true])
        ⟨d_wit, htrue_wit⟩
      set m := 1 + d
      have hm1 : 1 ≤ m := Nat.le_add_right 1 d
      have hm_false : ((ss m).proposers p).proposed = false := Bool.eq_false_iff.mpr hd_not
      have hm_true : ((ss (m + 1)).proposers p).proposed = true := by
        simpa only [m, Nat.add_assoc] using hd_true
      have ⟨hm_round, hm_noprep⟩ := hround_inv m hm1
      rw [(hexec m).2] at hm_true
      rcases proposers_synodStep_cases qs (ss m) (xs m) p with heq | ⟨r', hact, _⟩ |
          ⟨_, _, _, r_m, val, _, hr_m, _, _, _, _, h2a_mem⟩ |
          ⟨_, _, _, _, _, _, _, _, _, heq⟩ | ⟨_, heq⟩
      · exact absurd (heq.symm ▸ hm_true) (by rw [hm_false]; exact Bool.false_ne_true)
      · exact absurd hact (hm_noprep r')
      · obtain rfl : r_m = r := Option.some.inj (hr_m.symm.trans hm_round)
        exact ⟨m + 1, val, by omega, (hexec m).2 ▸ h2a_mem⟩
      · simp [heq, hm_false] at hm_true
      · simp [heq, hm_false] at hm_true
    · -- Contradiction if `proposed` stays `false` for all `n ≥ 1`:
      have hprop_false : ∀ n, 1 ≤ n → ((ss n).proposers p).proposed = false := fun n hn =>
        Bool.eq_false_iff.mpr fun h => hprop_ever ⟨n, hn, h⟩
      have hno_2a : ∀ n v, Msg.phase2a b v ∉ (ss n).msgs := by
        intro n
        induction n with
        | zero => exact fun v hm => lt_irrefl b (hbelow.1 (.phase2a b v) hm)
        | succ n ih =>
          intro v hm
          rw [(hexec n).2] at hm
          rcases mem_msgs_synodStep_cases hm with hold | ⟨_, _, _, ⟨⟩⟩ | ⟨_, _, _, _, ⟨⟩⟩ |
              ⟨q, _, _, _, r_q, _, hact, _, _, hprop_t, h⟩ | ⟨_, _, _, _, _, ⟨⟩⟩
          · exact ih v hold
          · injection h with hb_eq _
            obtain rfl : q = p := (congrArg Ballot.proposer hb_eq).symm
            rcases eq_or_ne n 0 with rfl | hn0
            · rw [hprep₀] at hact; cases hact
            · have hp1 := hprop_false (n + 1) (by omega)
              rw [(hexec n).2, hprop_t] at hp1; cases hp1
      have hacc_1b : ∀ n a, ((ss n).acceptors a).maxBal = some b →
          ∃ j mv, Msg.phase1b a b mv ∈ (ss j).msgs := by
        intro n
        induction n with
        | zero => exact fun a hmb => False.elim (lt_irrefl b (hbelow.2 a b hmb))
        | succ n ih =>
          intro a hmb
          obtain ⟨hen, hstep⟩ := hexec n
          rw [hstep] at hmb
          rcases acceptors_synodStep_cases qs (ss n) (xs n) a with heq |
              ⟨b', _, _, heq, h1b⟩ | ⟨b', v, hact, _, heq⟩ | ⟨_, heq⟩
          · exact ih a (heq ▸ hmb)
          · exact ⟨n + 1, _, Option.some.inj (heq ▸ hmb) ▸ hstep ▸ h1b⟩
          · exact (hno_2a n v (Option.some.inj (heq ▸ hmb) ▸ (hact ▸ hen).2)).elim
          · exact ih a (by simpa [heq] using hmb)
      have hQ_prom : ∀ a ∈ Q, ∃ n, 1 ≤ n ∧ a ∈ ((ss n).proposers p).promised := by
        intro a haQ
        obtain ⟨j₁, _, hj₁_act⟩ := hlive.fair_phase1a 1 hs1_1a a haQ
        have hex_1b : ∃ j_m mv, Msg.phase1b a b mv ∈ (ss j_m).msgs := by
          cases hab : aboveMaxBal ((ss j₁).acceptors a).maxBal b with
          | true =>
            exact ⟨j₁ + 1, ((ss j₁).acceptors a).maxVoted, by
              simp [(hexec j₁).2, hj₁_act, synodStep, synodStepCore, hab]⟩
          | false =>
            cases hmb_cur : ((ss j₁).acceptors a).maxBal with
            | none => rw [hmb_cur] at hab; cases hab
            | some mb =>
              rw [hmb_cur] at hab
              simp only [aboveMaxBal, decide_eq_false_iff_not, not_lt] at hab
              exact hacc_1b j₁ a (le_antisymm ((hceil j₁).2 a mb hmb_cur) hab ▸ hmb_cur)
        obtain ⟨j_m, mv, h1b_mem⟩ := hex_1b
        have h1b_at_max : Msg.phase1b a b mv ∈ (ss (max 1 j_m)).msgs :=
          ballot_msg_persist qs hexec hlive.no_drop_ballot (le_max_right 1 j_m) h1b_mem rfl
        obtain ⟨j₂, hj₂_ge, hj₂_act⟩ := hlive.fair_phase1b (max 1 j_m) a mv haQ h1b_at_max
        have hj₂_1 : 1 ≤ j₂ := (le_max_left 1 j_m).trans hj₂_ge
        refine ⟨j₂ + 1, by omega, ?_⟩
        by_cases ha_already : a ∈ ((ss j₂).proposers p).promised
        · exact promised_mono qs hexec hprep₀ hno_higher hj₂_1 (Nat.le_succ j₂) ha_already
        · simp only [(hexec j₂).2, hj₂_act, synodStep, synodStepCore, (hround_inv j₂ hj₂_1).1]
          rw [ite_eq_left ⟨rfl, ha_already⟩]
          split_ifs <;> simp only [↓reduceIte] <;> exact Finset.mem_insert_self _ _
      choose! stepOf hstep₁ hstep using hQ_prom
      let N_all := max 1 (Q.sup stepOf)
      have hQ_sub_Nall : Q ⊆ ((ss N_all).proposers p).promised := fun a haQ =>
        promised_mono qs hexec hprep₀ hno_higher (hstep₁ a haQ)
          ((Finset.le_sup haQ).trans (le_max_right 1 _)) (hstep a haQ)
      have hnot_1 : ¬ (Q ⊆ ((ss 1).proposers p).promised) := by
        rw [hs1_prom_empty]
        obtain ⟨a₀, ha₀⟩ := qs.prepareQuorum_nonempty hQ₁
        exact fun hsub => Finset.notMem_empty a₀ (hsub (hQ₁_sub ha₀))
      obtain ⟨d_all, hd_eq⟩ := Nat.exists_eq_add_of_le (le_max_left 1 (Q.sup stepOf))
      obtain ⟨d, hm_not_sub, hd_sub⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
        (p := fun d => Q ⊆ ((ss (1 + d)).proposers p).promised)
        (by simpa only [Nat.add_zero] using hnot_1)
        ⟨d_all, hd_eq ▸ hQ_sub_Nall⟩
      set m := 1 + d
      have hm1 : 1 ≤ m := Nat.le_add_right 1 d
      have hm_sub : Q ⊆ ((ss (m + 1)).proposers p).promised := by
        simpa only [m, Nat.add_assoc] using hd_sub
      have ⟨_, hm_noprep⟩ := hround_inv m hm1
      have hm_pfalse := hprop_false m hm1
      have hm_next_pfalse := hprop_false (m + 1) (by omega)
      rw [(hexec m).2] at hm_sub hm_next_pfalse
      rcases proposers_synodStep_cases qs (ss m) (xs m) p with heq | ⟨r', hact, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, heq, _⟩ |
          ⟨a, _, _, _, _, _, _, _, hq_not, heq⟩ | ⟨_, heq⟩
      · exact (hm_not_sub (heq ▸ hm_sub)).elim
      · exact (hm_noprep r' hact).elim
      · simp [heq] at hm_next_pfalse
      · rw [heq] at hm_sub
        exact (hq_not (by simpa [hm_pfalse] using ⟨Q₁, hQ₁, hQ₁_sub.trans hm_sub⟩)).elim
      · exact (hm_not_sub (by simpa [heq] using hm_sub)).elim
  -- The accept phase needs only the accept quorum inside the live cohort.
  obtain ⟨n₂, v, _, h2a_mem⟩ := hexists_2a
  obtain ⟨k, hlearned, hreg⟩ := paxos_liveness_from_phase2a_crashStop qs hr₀ hexec hQ₂
    (fun n a _ mb => (hceil n).2 a mb)
    (fun n w hm a ha => hlive.fair_phase2a n w hm a (hQ₂_sub ha))
    (fun n a w ha hm => hlive.fair_phase2b n a w (hQ₂_sub ha) hm) h2a_mem
  exact ⟨k, v, hlearned, hreg⟩

end SoleLeader

end Cslib.Distributed.Paxos
