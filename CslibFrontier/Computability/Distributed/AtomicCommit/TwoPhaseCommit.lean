/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Multiset.Basic

/-!
# Distributed Atomic Commitment and Fail-Stop Two-Phase Commit Step

This module specifies the distributed **Atomic Commitment** problem (`AC1` Uniform Agreement across
all deciding processes including crashed ones, `AC2` Abort Validity on any `no` vote, and `AC3`
failure-free Commit Nontriviality) and proves an intermediate **fail-stop register-state Two-Phase
Commit (`2PC`) step** toward [Gray1978], §5.8.3.3.2 (pp. 466–469), [Skeen1981], §§1–3
(pp. 134–137), and [SkeenStonebraker1983], §§II–IV (pp. 220–223), not the cited crash-recovery
log-replay endpoint (#7289).

In this fail-stop `2PC` step, a designated coordinator `coord : P` sends vote requests to all cohort
sites `r ≠ coord` in Phase 1. Each cohort casts its initial `Vote` (`yes` moving to `.uncertain`, or
`no` unilaterally deciding `.aborted`) and replies to `coord`. In Phase 2, `coord` decides
`.committed` and broadcasts `.commit` only if `votes coord = .yes` and every cohort replied `.yes`;
if `votes coord = .no`, any cohort replied `.no`, or a site crashed (timeout), `coord` decides
`.aborted` and broadcasts `.abort`. Stable undo/redo log forces ([Gray1978], §5.8.3.3.2, p. 468)
are abstracted as persistent per-site `TwoPCLocalState` registers retained across permanent
fail-stop crashes rather than crash-recovery log-replay restarts (#7289).

Within this fail-stop model we prove two complementary step families:

1. **Fail-stop safety and fault-free completion:** Across arbitrary fail-stop crashes and message
   omissions, decisions are write-once (`twoPC_decision_stable_failStop`) and every reachable
   configuration satisfies `UniformAgreement` (`twoPC_agreement_failStop`, `AC1`) and
   `AbortValidity` (`twoPC_abort_of_vote_no_failStop`, `AC2`). When no faults occur and all
   processes vote `yes`, `2PC` reaches unanimous `.commit` (`twoPC_failureFree_commit_failStop`,
   `AC3`); when any process votes `no`, a fault-free run reaches unanimous `.abort`
   (`twoPC_failureFree_abort_failStop`).
2. **Survivor uncertainty on coordinator crash (`2 ≤ Fintype.card P`):** Whenever at least two
   processes participate, there exist two reachable crash/omission configurations `sAbort` and
   `sCommit` with the same surviving operational cohort `{q}` (`q ≠ coord`, `votes q = .yes`,
   local state `.uncertain`, empty survivor inbox) such that `coord` voted `.no` and already
   decided `.abort` in `sAbort` whereas `coord` already decided `.commit` in `sCommit`
   (`twoPC_uncertain_bivalent_failStop`; on three or more sites, cohort-vote ambiguity with
   `votes coord = .yes` also arises). Consequently, no termination rule depending only on the
   surviving processes' states, votes, and inbox can safely decide for `q` without violating
   `UniformAgreement` (`twoPC_no_safe_survivor_termination_failStop`).

## Main definitions

* `Cslib.Distributed.AtomicCommit.Vote`: initial transaction vote (`yes` or `no`).
* `Cslib.Distributed.AtomicCommit.Decision`: irreversible outcome (`commit` or `abort`).
* `Cslib.Distributed.AtomicCommit.UniformAgreement`: `AC1` agreement across all deciding sites
  (operational or crashed).
* `Cslib.Distributed.AtomicCommit.AbortValidity`: `AC2` unilateral-abort validity
  (`(∃ p, votes p = .no) → ∀ q, dec q ≠ some .commit`).
* `Cslib.Distributed.AtomicCommit.AllDecided`,
  `Cslib.Distributed.AtomicCommit.OperationalDecided`: unanimous decision predicates.
* `Cslib.Distributed.AtomicCommit.TwoPCLocalState`,
  `Cslib.Distributed.AtomicCommit.TwoPCMsg`,
  `Cslib.Distributed.AtomicCommit.TwoPCState`,
  `Cslib.Distributed.AtomicCommit.TwoPCAction`: local states, network messages, global
  configurations, and transition labels of the fail-stop `2PC` step.
* `Cslib.Distributed.AtomicCommit.twoPCStep?`,
  `Cslib.Distributed.AtomicCommit.twoPCLts`,
  `Cslib.Distributed.AtomicCommit.TwoPCReachable`: operational `Cslib.LTS` semantics of the
  fail-stop `2PC` step with crashes and message omissions.
* `Cslib.Distributed.AtomicCommit.TwoPCSurvivorView`: projection of a `2PC` global state visible to
  the surviving operational sites.

## Main results

* `Cslib.Distributed.AtomicCommit.twoPC_decision_stable_failStop`: local `2PC` decisions are
  irreversible along reachable executions in the fail-stop register-state step.
* `Cslib.Distributed.AtomicCommit.twoPC_agreement_failStop`: fail-stop `2PC` step toward
  `UniformAgreement` (`AC1`) across arbitrary fail-stop crashes and message omissions.
* `Cslib.Distributed.AtomicCommit.twoPC_abort_of_vote_no_failStop`: fail-stop `2PC` step toward
  `AbortValidity` (`AC2`) in every reachable state.
* `Cslib.Distributed.AtomicCommit.twoPC_failureFree_commit_failStop`: fault-free all-`yes`
  execution of the fail-stop `2PC` model reaches `AllDecided _ .commit` (`AC3`).
* `Cslib.Distributed.AtomicCommit.twoPC_failureFree_abort_failStop`: fault-free execution of the
  fail-stop `2PC` model with at least one `no` vote reaches `AllDecided _ .abort`.
* `Cslib.Distributed.AtomicCommit.twoPC_uncertain_bivalent_failStop`: for `2 ≤ Fintype.card P`,
  exhibits reachable `sAbort` and `sCommit` with identical `TwoPCSurvivorView` on a surviving
  `.uncertain` cohort `q` (`votes q = .yes`) where `coord` has already decided `.abort` vs
  `.commit`.
* `Cslib.Distributed.AtomicCommit.twoPC_no_safe_survivor_termination_failStop`: for
  `2 ≤ Fintype.card P`, no survivor-only termination rule for the fail-stop `2PC` model preserves
  `UniformAgreement`.

## References

* [J. Gray, *Notes on Data Base Operating Systems*][Gray1978]
* [D. Skeen, *Nonblocking Commit Protocols*][Skeen1981]
* [D. Skeen, M. Stonebraker, *A Formal Model of Crash Recovery in a Distributed
  System*][SkeenStonebraker1983]
-/

public section

namespace Cslib.Distributed.AtomicCommit

open Cslib

/-! ### Atomic commitment specification -/

/-- Initial vote of a site on whether it is prepared to commit or unilaterally aborts. -/
inductive Vote where
  | yes
  | no
  deriving @[expose] DecidableEq, Repr

/-- Irreversible transaction outcome decided by a site. -/
inductive Decision where
  | commit
  | abort
  deriving @[expose] DecidableEq, Repr

/-- **Uniform Agreement (`AC1`):** any two sites (operational or crashed) that have reached
decisions agree on the same `Decision`. -/
@[expose] def UniformAgreement {P : Type*} (dec : P → Option Decision) : Prop :=
  ∀ p q d₁ d₂, dec p = some d₁ → dec q = some d₂ → d₁ = d₂

/-- **Abort Validity (`AC2`):** if any site initially voted `.no`, no site ever decides
`.commit`. -/
@[expose] def AbortValidity {P : Type*} (votes : P → Vote) (dec : P → Option Decision) : Prop :=
  (∃ p, votes p = .no) → ∀ q, dec q ≠ some .commit

/-- Every site in `P` has reached decision `d`. -/
@[expose] def AllDecided {P : Type*} (dec : P → Option Decision) (d : Decision) : Prop :=
  ∀ p, dec p = some d

/-- Every operational site in `alive` has reached decision `d`. -/
@[expose] def OperationalDecided {P : Type*} (alive : Finset P) (dec : P → Option Decision)
    (d : Decision) : Prop :=
  ∀ p ∈ alive, dec p = some d

/-- Finite-process decidability of `UniformAgreement`. -/
instance instDecidableUniformAgreement {P : Type*} [Fintype P]
    (dec : P → Option Decision) : Decidable (UniformAgreement dec) :=
  decidable_of_iff
    (∀ p q, (dec p).isSome = true → (dec q).isSome = true → dec p = dec q)
    ⟨fun h p q _ _ hp hq => by
       have heq := h p q (by simp [hp]) (by simp [hq])
       exact Option.some.inj (hp.symm.trans (heq.trans hq)),
     fun h p q hp hq => by
       obtain ⟨d₁, hd₁⟩ := Option.isSome_iff_exists.mp hp
       obtain ⟨d₂, hd₂⟩ := Option.isSome_iff_exists.mp hq
       rw [hd₁, hd₂, h p q d₁ d₂ hd₁ hd₂]⟩

/-- Finite-process decidability of `AbortValidity`. -/
instance instDecidableAbortValidity {P : Type*} [Fintype P] (votes : P → Vote)
    (dec : P → Option Decision) : Decidable (AbortValidity votes dec) :=
  inferInstanceAs (Decidable ((∃ p, votes p = .no) → ∀ q, dec q ≠ some .commit))

/-- Finite-process decidability of `AllDecided`. -/
instance instDecidableAllDecided {P : Type*} [Fintype P] (dec : P → Option Decision)
    (d : Decision) : Decidable (AllDecided dec d) :=
  inferInstanceAs (Decidable (∀ p, dec p = some d))

/-- Decidability of `OperationalDecided` over `alive : Finset P`. -/
instance instDecidableOperationalDecided {P : Type*} (alive : Finset P)
    (dec : P → Option Decision) (d : Decision) : Decidable (OperationalDecided alive dec d) :=
  inferInstanceAs (Decidable (∀ p ∈ alive, dec p = some d))

/-- Under `AbortValidity`, if at least one site voted `.no`, any decided outcome is `.abort`. -/
theorem AbortValidity.eq_abort_of_eq_some {P : Type*} {votes : P → Vote}
    {dec : P → Option Decision} (hval : AbortValidity votes dec) (hno : ∃ p, votes p = .no)
    {q : P} {d : Decision} (hq : dec q = some d) : d = .abort := by
  cases d; exacts [(hval hno q hq).elim, rfl]

/-! ### Fail-stop register-state Two-Phase Commit (`2PC`) step -/

/-- Local automaton states of centralized Two-Phase Commit ([Skeen1981], Figure 2, p. 135;
[Gray1978], §5.8.3.3.2, p. 468). -/
inductive TwoPCLocalState where
  /-- Initial state (`q_i`) prior to Phase 1 voting or request broadcast. -/
  | init
  /-- Coordinator Phase 1 state (`w_1`) awaiting cohort vote replies. -/
  | waitVotes
  /-- Cohort Phase 1 state (`w_i`) after voting `.yes` and forcing undo/redo logs, awaiting the
  coordinator's Phase 2 verdict. -/
  | uncertain
  /-- Final committed state (`c_i`). -/
  | committed
  /-- Final aborted state (`a_i`). -/
  | aborted
  deriving @[expose] DecidableEq, Repr

/-- Decision recorded in a `TwoPCLocalState` (`none` until `.committed` or `.aborted`). -/
@[expose] def TwoPCLocalState.decision : TwoPCLocalState → Option Decision
  | .committed => some .commit
  | .aborted => some .abort
  | .init | .waitVotes | .uncertain => none

/-- Final `TwoPCLocalState` corresponding to a `Decision`. -/
@[expose] def Decision.toTwoPCLocal : Decision → TwoPCLocalState
  | .commit => .committed
  | .abort => .aborted

@[simp] theorem TwoPCLocalState.decision_committed :
    TwoPCLocalState.committed.decision = some .commit := rfl

@[simp] theorem TwoPCLocalState.decision_aborted :
    TwoPCLocalState.aborted.decision = some .abort := rfl

@[simp] theorem TwoPCLocalState.decision_init : TwoPCLocalState.init.decision = none := rfl

@[simp] theorem TwoPCLocalState.decision_waitVotes :
    TwoPCLocalState.waitVotes.decision = none := rfl

@[simp] theorem TwoPCLocalState.decision_uncertain :
    TwoPCLocalState.uncertain.decision = none := rfl

@[simp] theorem Decision.decision_toTwoPCLocal (d : Decision) :
    d.toTwoPCLocal.decision = some d := by
  cases d <;> rfl

/-- A `TwoPCLocalState` decides `.commit` iff it is `.committed`. -/
theorem TwoPCLocalState.decision_eq_some_commit_iff {st : TwoPCLocalState} :
    st.decision = some .commit ↔ st = .committed := by
  cases st <;> simp [TwoPCLocalState.decision]

/-- A `TwoPCLocalState` decides `.abort` iff it is `.aborted`. -/
theorem TwoPCLocalState.decision_eq_some_abort_iff {st : TwoPCLocalState} :
    st.decision = some .abort ↔ st = .aborted := by
  cases st <;> simp [TwoPCLocalState.decision]

/-- Point-to-point protocol messages of centralized `2PC`. -/
inductive TwoPCMsg (P : Type*) where
  /-- Phase 1 `REQUEST_COMMIT` sent by the coordinator to cohort `dest`. -/
  | voteRequest (dest : P)
  /-- Phase 1 vote reply sent by cohort `src` to the coordinator. -/
  | voteReply (src : P) (vote : Vote)
  /-- Phase 2 final verdict (`COMMIT` or `ABORT`) sent by the coordinator to cohort `dest`. -/
  | verdict (dest : P) (dec : Decision)
  deriving @[expose] DecidableEq, Repr

/-- Recipient process of a `TwoPCMsg` given the designated coordinator `coord`. -/
@[expose] def TwoPCMsg.recipient {P : Type*} (coord : P) : TwoPCMsg P → P
  | .voteRequest dest => dest
  | .voteReply _ _ => coord
  | .verdict dest _ => dest

/-- Global configuration of centralized `2PC` under fail-stop crashes and message omissions. -/
structure TwoPCState (P : Type*) where
  /-- Local automaton state of each process (retained permanently even if the process crashes). -/
  localState : P → TwoPCLocalState
  /-- Set of cohorts from which the coordinator has received `.yes` replies. -/
  yesVotes : Finset P
  /-- Whether the coordinator has received at least one `.no` reply. -/
  sawNo : Bool
  /-- Currently operational (non-crashed) processes. -/
  alive : Finset P
  /-- Multiset of in-flight messages on the asynchronous network. -/
  msgs : Multiset (TwoPCMsg P)

/-- Decision vector of a global `TwoPCState` across all sites (operational or crashed). -/
@[expose] def TwoPCState.decision {P : Type*} (s : TwoPCState P) (p : P) : Option Decision :=
  (s.localState p).decision

/-- Initial global configuration of `2PC`: all processes operational in `.init` with empty
network. -/
@[expose] def twoPCStart (P : Type*) [Fintype P] : TwoPCState P where
  localState := fun _ => .init
  yesVotes := ∅
  sawNo := false
  alive := Finset.univ
  msgs := 0

/-- Transition labels of the `2PC` operational `LTS`. -/
inductive TwoPCAction (P : Type*) where
  /-- Coordinator initiates Phase 1 by broadcasting `voteRequest` to all cohorts `r ≠ coord`. -/
  | sendRequests
  /-- Cohort `p ≠ coord` processes `voteRequest p` and casts `votes p`. -/
  | recvRequest (p : P)
  /-- Coordinator processes `voteReply p v` in `.waitVotes`. -/
  | recvVote (p : P) (v : Vote)
  /-- Coordinator commits after collecting `.yes` from every cohort and checking its own `.yes`. -/
  | coordCommit
  /-- Coordinator aborts upon `votes coord = .no`, a `.no` reply, or a site crash timeout. -/
  | coordAbort
  /-- Cohort `p ≠ coord` processes `verdict p d` from the coordinator. -/
  | recvVerdict (p : P) (d : Decision)
  /-- Fail-stop crash of operational site `p`. -/
  | crash (p : P)
  /-- Network omission (loss) of an in-flight message `m`. -/
  | dropMsg (m : TwoPCMsg P)
  deriving @[expose] DecidableEq, Repr

/-- Whether a `TwoPCAction` is a normal message-passing step without crashes or message drops. -/
@[expose] def TwoPCAction.isFaultFree {P : Type*} : TwoPCAction P → Bool
  | .crash _ | .dropMsg _ => false
  | _ => true

/-- Partial transition function of centralized `2PC` for designated coordinator `coord` and initial
vote profile `votes`. -/
@[expose] def twoPCStep? {P : Type*} [DecidableEq P] [Fintype P] (coord : P) (votes : P → Vote)
    (s : TwoPCState P) (act : TwoPCAction P) : Option (TwoPCState P) :=
  let cohorts := (Finset.univ.erase coord).val
  match act with
  | .sendRequests =>
    if coord ∈ s.alive ∧ s.localState coord = .init then
      some { s with
        localState := Function.update s.localState coord .waitVotes
        msgs := s.msgs + cohorts.map .voteRequest }
    else none
  | .recvRequest p =>
    if p ≠ coord ∧ p ∈ s.alive ∧ s.localState p = .init ∧ TwoPCMsg.voteRequest p ∈ s.msgs then
      let nextSt : TwoPCLocalState := if votes p = .yes then .uncertain else .aborted
      some { s with
        localState := Function.update s.localState p nextSt
        msgs := s.msgs.erase (.voteRequest p) + {TwoPCMsg.voteReply p (votes p)} }
    else none
  | .recvVote p v =>
    if coord ∈ s.alive ∧ s.localState coord = .waitVotes ∧ TwoPCMsg.voteReply p v ∈ s.msgs then
      some { s with
        yesVotes := if v = .yes then insert p s.yesVotes else s.yesVotes
        sawNo := if v = .no then true else s.sawNo
        msgs := s.msgs.erase (.voteReply p v) }
    else none
  | .coordCommit =>
    if coord ∈ s.alive ∧ s.localState coord = .waitVotes ∧ votes coord = .yes ∧
        s.sawNo = false ∧ Finset.univ.erase coord ⊆ s.yesVotes then
      some { s with
        localState := Function.update s.localState coord .committed
        msgs := s.msgs + cohorts.map (fun r => TwoPCMsg.verdict r .commit) }
    else none
  | .coordAbort =>
    if coord ∈ s.alive ∧ s.localState coord = .waitVotes ∧
        (votes coord = .no ∨ s.sawNo = true ∨ s.alive ≠ Finset.univ) then
      some { s with
        localState := Function.update s.localState coord .aborted
        msgs := s.msgs + cohorts.map (fun r => TwoPCMsg.verdict r .abort) }
    else none
  | .recvVerdict p d =>
    if p ≠ coord ∧ p ∈ s.alive ∧ TwoPCMsg.verdict p d ∈ s.msgs ∧
        (s.localState p = .uncertain ∨ (d = .abort ∧ s.localState p = .init)) then
      some { s with
        localState := Function.update s.localState p d.toTwoPCLocal
        msgs := s.msgs.erase (.verdict p d) }
    else none
  | .crash p =>
    if p ∈ s.alive then
      some { s with alive := s.alive.erase p }
    else none
  | .dropMsg m =>
    if m ∈ s.msgs then
      some { s with msgs := s.msgs.erase m }
    else none

/-- Operational `Cslib.LTS` of the fail-stop register-state `2PC` step with crashes and message
omissions (after [Gray1978], §5.8.3.3.2, pp. 466–469). -/
@[expose] def twoPCLts {P : Type*} [DecidableEq P] [Fintype P] (coord : P) (votes : P → Vote) :
    LTS (TwoPCState P) (TwoPCAction P) where
  Tr s a s' := twoPCStep? coord votes s a = some s'

/-- Reachability of a `2PC` configuration from `twoPCStart P` in the fail-stop register-state
step. -/
@[expose] def TwoPCReachable {P : Type*} [DecidableEq P] [Fintype P] (coord : P) (votes : P → Vote)
    (s : TwoPCState P) : Prop :=
  (twoPCLts coord votes).CanReach (twoPCStart P) s

/-! ### Fail-stop safety (`AC1` and `AC2`) and decision stability of `2PC` -/

section Safety

variable {P : Type*} [DecidableEq P] [Fintype P] {coord : P} {votes : P → Vote}

private theorem twoPC_canReach_trans {s₁ s₂ s₃ : TwoPCState P}
    (h₁ : (twoPCLts coord votes).CanReach s₁ s₂) (h₂ : (twoPCLts coord votes).CanReach s₂ s₃) :
    (twoPCLts coord votes).CanReach s₁ s₃ := by
  rcases h₁ with ⟨tr₁, hm₁⟩
  rcases h₂ with ⟨tr₂, hm₂⟩
  exact ⟨tr₁ ++ tr₂, hm₁.comp _ hm₂⟩

omit [Fintype P] in
private theorem decision_update_of_none {st : P → TwoPCLocalState} {q p : P}
    {newSt : TwoPCLocalState} {d : Decision}
    (hq : (st q).decision = none) (hd : (st p).decision = some d) :
    (Function.update st q newSt p).decision = some d := by
  by_cases hp : p = q
  · subst hp; rw [hq] at hd; cases hd
  · rwa [Function.update_of_ne hp]

private theorem step_decision_stable {s s' : TwoPCState P} {act : TwoPCAction P}
    (hstep : twoPCStep? coord votes s act = some s') {p : P} {d : Decision}
    (hd : s.decision p = some d) : s'.decision p = some d := by
  cases act <;> dsimp only [twoPCStep?] at hstep <;> split at hstep <;> cases hstep <;>
    dsimp only [TwoPCState.decision] at hd ⊢
  · rename_i hg; exact decision_update_of_none (by rw [hg.2]; rfl) hd
  · rename_i q hg; exact decision_update_of_none (by rw [hg.2.2.1]; rfl) hd
  · exact hd
  · rename_i hg; exact decision_update_of_none (by rw [hg.2.1]; rfl) hd
  · rename_i hg; exact decision_update_of_none (by rw [hg.2.1]; rfl) hd
  · rename_i q d' hg
    exact decision_update_of_none
      (hg.2.2.2.elim (fun h => by rw [h]; rfl) (fun ⟨_, h⟩ => by rw [h]; rfl)) hd
  · exact hd
  · exact hd

/-- Fail-stop register-state step toward [Gray1978], §5.8.3.3.2 (p. 468), not the cited
crash-recovery log-replay result (#7289): once a site decides `.commit` or `.abort` in `twoPCLts`,
its decision is preserved along all subsequent transitions (including fail-stop crashes and message
drops). -/
theorem twoPC_decision_stable_failStop {s s' : TwoPCState P}
    (hreach : (twoPCLts coord votes).CanReach s s') {p : P} {d : Decision}
    (hd : s.decision p = some d) : s'.decision p = some d := by
  rcases hreach with ⟨tr, hmtr⟩
  exact (twoPCLts coord votes).mtrInv_of_trInv
    (fun _ _ _ hstep hd' => step_decision_stable hstep hd') _ _ _ hmtr hd

/-- Inductive safety invariant for centralized `2PC`. -/
private structure TwoPCInvariant (coord : P) (votes : P → Vote) (s : TwoPCState P) : Prop where
  yesVotes_yes : ∀ p ∈ s.yesVotes, votes p = .yes
  voteReply_yes : ∀ p, TwoPCMsg.voteReply p .yes ∈ s.msgs → votes p = .yes
  committed_imp_coord : ∀ p, s.localState p = .committed → s.localState coord = .committed
  verdict_commit_imp_coord :
    ∀ p, TwoPCMsg.verdict p .commit ∈ s.msgs → s.localState coord = .committed
  coord_committed_all_yes : s.localState coord = .committed → ∀ q, votes q = .yes
  verdict_abort_imp_coord :
    ∀ p, TwoPCMsg.verdict p .abort ∈ s.msgs → s.localState coord = .aborted
  aborted_imp_no_or_coord :
    ∀ p, s.localState p = .aborted → votes p = .no ∨ s.localState coord = .aborted

omit [DecidableEq P] in
private theorem twoPCInvariant_start : TwoPCInvariant coord votes (twoPCStart P) where
  yesVotes_yes _ hp := absurd hp (Finset.notMem_empty _)
  voteReply_yes _ hm := absurd hm (Multiset.notMem_zero _)
  committed_imp_coord _ h := by simp [twoPCStart] at h
  verdict_commit_imp_coord _ hm := absurd hm (Multiset.notMem_zero _)
  coord_committed_all_yes h := by simp [twoPCStart] at h
  verdict_abort_imp_coord _ hm := absurd hm (Multiset.notMem_zero _)
  aborted_imp_no_or_coord _ h := by simp [twoPCStart] at h

private theorem mem_of_mem_add_map_ne {α β : Type*} {ms : Multiset β} {xs : Multiset α}
    {f : α → β} {m : β} (hne : ∀ x, f x ≠ m) (hm : m ∈ ms + xs.map f) : m ∈ ms := by
  simp only [Multiset.mem_add, Multiset.mem_map] at hm
  rcases hm with hm | ⟨x, _, hx⟩
  · exact hm
  · exact False.elim (hne x hx)

omit [Fintype P] in
private theorem not_committed_update_coord {st : P → TwoPCLocalState} {newSt : TwoPCLocalState}
    (hnew : newSt ≠ .committed) (hnc : st coord ≠ .committed)
    (himp : ∀ p, st p = .committed → st coord = .committed) {p : P}
    (hp : Function.update st coord newSt p = .committed) : False := by
  by_cases hpc : p = coord
  · subst hpc; rw [Function.update_self] at hp; exact hnew hp
  · rw [Function.update_of_ne hpc _ _] at hp; exact hnc (himp p hp)

omit [Fintype P] in
private theorem aborted_imp_no_update_coord {st : P → TwoPCLocalState} {newSt : TwoPCLocalState}
    (hnew : newSt ≠ .aborted) (hna : st coord ≠ .aborted)
    (hab : ∀ p, st p = .aborted → votes p = .no ∨ st coord = .aborted) {p : P}
    (hp : Function.update st coord newSt p = .aborted) :
    votes p = .no ∨ Function.update st coord newSt coord = .aborted := by
  by_cases hpc : p = coord
  · subst hpc; rw [Function.update_self] at hp; exact False.elim (hnew hp)
  · rw [Function.update_of_ne hpc _ _] at hp
    exact Or.inl ((hab p hp).resolve_right hna)

omit [Fintype P] in
private theorem twoPCInvariant_coord_noncommit {s : TwoPCState P} {newSt : TwoPCLocalState}
    {xs : Multiset P} {f : P → TwoPCMsg P} (hinv : TwoPCInvariant coord votes s)
    (hnew : newSt ≠ .committed) (hnc : s.localState coord ≠ .committed)
    (hnot_rep : ∀ p r, f r ≠ .voteReply p .yes)
    (hnot_vcom : ∀ p r, f r ≠ .verdict p .commit)
    (hva : ∀ p, TwoPCMsg.verdict p .abort ∈ s.msgs + xs.map f → newSt = .aborted)
    (hab : ∀ p, Function.update s.localState coord newSt p = .aborted →
      votes p = .no ∨ newSt = .aborted) :
    TwoPCInvariant coord votes
      { s with
        localState := Function.update s.localState coord newSt
        msgs := s.msgs + xs.map f } :=
  { yesVotes_yes := hinv.yesVotes_yes
    voteReply_yes := fun p hm => hinv.voteReply_yes p (mem_of_mem_add_map_ne (hnot_rep p) hm)
    committed_imp_coord := fun _ hp =>
      False.elim (not_committed_update_coord hnew hnc hinv.committed_imp_coord hp)
    verdict_commit_imp_coord := fun p hm =>
      absurd (hinv.verdict_commit_imp_coord p (mem_of_mem_add_map_ne (hnot_vcom p) hm)) hnc
    coord_committed_all_yes := fun hc =>
      False.elim (hnew (by simpa [Function.update] using hc))
    verdict_abort_imp_coord := fun p hm => by simp [hva p hm]
    aborted_imp_no_or_coord := fun p hp => by simpa using hab p hp }

omit [Fintype P] in
private theorem twoPCInvariant_cohort_step {s : TwoPCState P} {q : P}
    {newSt : TwoPCLocalState} {msgs' : Multiset (TwoPCMsg P)}
    (hinv : TwoPCInvariant coord votes s) (hqc : q ≠ coord)
    (hrep : ∀ p, TwoPCMsg.voteReply p .yes ∈ msgs' →
      TwoPCMsg.voteReply p .yes ∈ s.msgs ∨ votes p = .yes)
    (hsub_v : ∀ p d, TwoPCMsg.verdict p d ∈ msgs' → TwoPCMsg.verdict p d ∈ s.msgs)
    (hcom_q : newSt = .committed → s.localState coord = .committed)
    (hab_q : newSt = .aborted → votes q = .no ∨ s.localState coord = .aborted) :
    TwoPCInvariant coord votes
      { s with localState := Function.update s.localState q newSt, msgs := msgs' } := by
  have hcoord : Function.update s.localState q newSt coord = s.localState coord :=
    Function.update_of_ne hqc.symm _ _
  refine ⟨hinv.yesVotes_yes,
    fun p hm => (hrep p hm).elim (hinv.voteReply_yes p) id, ?_,
    fun p hm => hcoord.trans (hinv.verdict_commit_imp_coord p (hsub_v p .commit hm)),
    fun hc => hinv.coord_committed_all_yes (hcoord ▸ hc),
    fun p hm => hcoord.trans (hinv.verdict_abort_imp_coord p (hsub_v p .abort hm)), ?_⟩
  · intro p hp; dsimp only at hp ⊢
    rw [hcoord, Function.update_apply] at *; split_ifs at hp with hpq
    exacts [hcom_q hp, hinv.committed_imp_coord p hp]
  · intro p hp; dsimp only at hp ⊢
    rw [hcoord, Function.update_apply] at *; split_ifs at hp with hpq
    exacts [hpq ▸ hab_q hp, hinv.aborted_imp_no_or_coord p hp]

private theorem twoPCInvariant_step {s s' : TwoPCState P} {act : TwoPCAction P}
    (hinv : TwoPCInvariant coord votes s) (hstep : twoPCStep? coord votes s act = some s') :
    TwoPCInvariant coord votes s' := by
  cases act <;> dsimp only [twoPCStep?] at hstep <;> split at hstep <;> cases hstep
  case sendRequests.isTrue hg =>
    have hnc : s.localState coord ≠ .committed := by rw [hg.2]; decide
    have hna : s.localState coord ≠ .aborted := by rw [hg.2]; decide
    refine twoPCInvariant_coord_noncommit hinv (by decide) hnc
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun p hm => ?_) (fun p hp => ?_)
    · exact False.elim (hna (hinv.verdict_abort_imp_coord p
        (mem_of_mem_add_map_ne (fun _ h => by cases h) hm)))
    · simpa using aborted_imp_no_update_coord (by decide) hna hinv.aborted_imp_no_or_coord hp
  case recvRequest.isTrue q hg =>
    refine twoPCInvariant_cohort_step hinv hg.1
      (fun p hm => ?_) (fun p d hm => ?_)
      (fun hp => by split at hp <;> cases hp)
      (fun hp => by cases hv : votes q <;> [simp only [hv, ↓reduceIte, reduceCtorEq] at hp;
        exact Or.inl rfl])
    · rcases Multiset.mem_add.mp hm with hm | heq
      · exact Or.inl (Multiset.mem_of_mem_erase hm)
      · obtain ⟨rfl, hv⟩ := TwoPCMsg.voteReply.inj (Multiset.mem_singleton.mp heq)
        exact Or.inr hv.symm
    · rcases Multiset.mem_add.mp hm with hm | heq
      · exact Multiset.mem_of_mem_erase hm
      · cases Multiset.mem_singleton.mp heq
  case recvVote.isTrue q v hg =>
    have he := @Multiset.mem_of_mem_erase
    refine { hinv with
      yesVotes_yes := fun p hp => ?_
      voteReply_yes := fun p hm => hinv.voteReply_yes p (he hm)
      verdict_commit_imp_coord := fun p hm => hinv.verdict_commit_imp_coord p (he hm)
      verdict_abort_imp_coord := fun p hm => hinv.verdict_abort_imp_coord p (he hm) }
    dsimp only at hp
    cases v
    · rcases Finset.mem_insert.mp hp with rfl | hp
      exacts [hinv.voteReply_yes p hg.2.2, hinv.yesVotes_yes p hp]
    · exact hinv.yesVotes_yes p hp
  case coordCommit.isTrue hg =>
    have hna : s.localState coord ≠ .aborted := by rw [hg.2.1]; decide
    have hall_yes : ∀ r, votes r = .yes := fun r =>
      if hrc : r = coord then hrc ▸ hg.2.2.1
      else hinv.yesVotes_yes r (hg.2.2.2.2 (Finset.mem_erase.mpr ⟨hrc, Finset.mem_univ r⟩))
    exact ⟨hinv.yesVotes_yes,
      fun p hm => hinv.voteReply_yes p (mem_of_mem_add_map_ne (fun _ h => by cases h) hm),
      fun _ _ => Function.update_self _ _ _,
      fun _ _ => Function.update_self _ _ _,
      fun _ => hall_yes,
      fun p hm => absurd (hinv.verdict_abort_imp_coord p
        (mem_of_mem_add_map_ne (fun _ h => by cases h) hm)) hna,
      fun _ hp => aborted_imp_no_update_coord (by decide) hna hinv.aborted_imp_no_or_coord hp⟩
  case coordAbort.isTrue hg =>
    have hnc : s.localState coord ≠ .committed := by rw [hg.2.1]; decide
    exact twoPCInvariant_coord_noncommit hinv (by decide) hnc
      (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ => rfl) (fun _ _ => Or.inr rfl)
  case recvVerdict.isTrue q d hg =>
    exact twoPCInvariant_cohort_step hinv hg.1
      (fun _ hm => Or.inl (Multiset.mem_of_mem_erase hm))
      (fun _ _ hm => Multiset.mem_of_mem_erase hm)
      (fun hp => by cases d <;> [exact hinv.verdict_commit_imp_coord q hg.2.2.1; cases hp])
      (fun hp => by cases d <;> [cases hp; exact Or.inr (hinv.verdict_abort_imp_coord q hg.2.2.1)])
  case crash.isTrue => exact { hinv with }
  case dropMsg.isTrue =>
    have he := @Multiset.mem_of_mem_erase
    exact { hinv with
      voteReply_yes := fun p hm => hinv.voteReply_yes p (he hm)
      verdict_commit_imp_coord := fun p hm => hinv.verdict_commit_imp_coord p (he hm)
      verdict_abort_imp_coord := fun p hm => hinv.verdict_abort_imp_coord p (he hm) }

private theorem twoPCInvariant_of_reachable {s : TwoPCState P}
    (hreach : TwoPCReachable coord votes s) : TwoPCInvariant coord votes s := by
  rcases hreach with ⟨tr, hmtr⟩
  exact (twoPCLts coord votes).mtrInv_of_trInv
    (fun _ _ _ hstep hinv => twoPCInvariant_step hinv hstep) _ _ _ hmtr twoPCInvariant_start

omit [DecidableEq P] [Fintype P] in
private theorem TwoPCInvariant.not_commit_and_abort {s : TwoPCState P}
    (hinv : TwoPCInvariant coord votes s) {p q : P}
    (hp : s.decision p = some .commit) (hq : s.decision q = some .abort) : False := by
  have hc : s.localState coord = .committed :=
    hinv.committed_imp_coord p (TwoPCLocalState.decision_eq_some_commit_iff.mp hp)
  have hqa : s.localState q = .aborted := TwoPCLocalState.decision_eq_some_abort_iff.mp hq
  rcases hinv.aborted_imp_no_or_coord q hqa with hno | hca
  · exact absurd (hinv.coord_committed_all_yes hc q) (by rw [hno]; decide)
  · rw [hc] at hca; cases hca

/-- Fail-stop register-state step toward [Gray1978], §5.8.3.3.2 (p. 469) and [Skeen1981], §2
(p. 136), not the cited crash-recovery log-replay result (#7289): in every reachable configuration
of `twoPCLts` (across arbitrary fail-stop site crashes and message omissions), all decided
sites—operational or crashed—satisfy `UniformAgreement` (`AC1`). -/
theorem twoPC_agreement_failStop {s : TwoPCState P} (hreach : TwoPCReachable coord votes s) :
    UniformAgreement s.decision := by
  have hinv := twoPCInvariant_of_reachable hreach
  intro p q d₁ d₂ hp hq
  cases d₁ <;> cases d₂
  exacts [rfl, (hinv.not_commit_and_abort hp hq).elim, (hinv.not_commit_and_abort hq hp).elim, rfl]

/-- Fail-stop register-state step toward [Gray1978], §5.8.3.3.2 (p. 468) and [Skeen1981], §2
(p. 136), not the cited crash-recovery log-replay result (#7289): if any site voted `.no`, no site
decides `.commit` in any reachable configuration of `twoPCLts` (`AC2`). -/
theorem twoPC_abort_of_vote_no_failStop {s : TwoPCState P}
    (hreach : TwoPCReachable coord votes s) :
    AbortValidity votes s.decision := by
  have hinv := twoPCInvariant_of_reachable hreach
  intro ⟨p, hp⟩ q hq
  have hc : s.localState coord = .committed :=
    hinv.committed_imp_coord q (TwoPCLocalState.decision_eq_some_commit_iff.mp hq)
  simpa [hp] using hinv.coord_committed_all_yes hc p

/-! ### Failure-free execution (`AC3` and abort completion) -/

private def FaultFreeMTr (coord : P) (votes : P → Vote) (s₁ s₂ : TwoPCState P) : Prop :=
  ∃ tr, (∀ a ∈ tr, a.isFaultFree = true) ∧ (twoPCLts coord votes).MTr s₁ tr s₂

private theorem FaultFreeMTr.refl (s : TwoPCState P) : FaultFreeMTr coord votes s s :=
  ⟨[], fun _ h => absurd h List.not_mem_nil, .refl⟩

private theorem FaultFreeMTr.step {s₁ s₂ s₃ : TwoPCState P} {a : TwoPCAction P}
    (ha : a.isFaultFree = true) (htr : twoPCStep? coord votes s₁ a = some s₂)
    (hrest : FaultFreeMTr coord votes s₂ s₃) : FaultFreeMTr coord votes s₁ s₃ := by
  rcases hrest with ⟨tr, hff, hmtr⟩
  exact ⟨a :: tr, List.forall_mem_cons.mpr ⟨ha, hff⟩, .stepL htr hmtr⟩

private theorem FaultFreeMTr.trans {s₁ s₂ s₃ : TwoPCState P}
    (h₁ : FaultFreeMTr coord votes s₁ s₂) (h₂ : FaultFreeMTr coord votes s₂ s₃) :
    FaultFreeMTr coord votes s₁ s₃ := by
  rcases h₁ with ⟨tr₁, hff₁, hm₁⟩
  rcases h₂ with ⟨tr₂, hff₂, hm₂⟩
  exact ⟨tr₁ ++ tr₂, List.forall_mem_append.mpr ⟨hff₁, hff₂⟩, hm₁.comp _ hm₂⟩

omit [Fintype P] in
private theorem ite_mem_update_eq_insert {α : Type*} (R : Finset P) (q : P) (v : α)
    (st : P → α) :
    (fun p => if p ∈ R then v else Function.update st q v p) =
      (fun p => if p ∈ insert q R then v else st p) := by
  funext p; by_cases hpq : p = q <;> simp [hpq]

/-- Process Phase 1 requests and vote replies for every cohort in `R` when all cohorts vote
`.yes`. -/
private theorem faultFree_collect_all_yes (hyes : ∀ p, votes p = .yes) :
    ∀ R : Finset P, coord ∉ R →
      ∀ (st : P → TwoPCLocalState) (yv : Finset P) (rest : Multiset (TwoPCMsg P)),
        st coord = .waitVotes → (∀ r ∈ R, st r = .init) →
        ∃ s' : TwoPCState P,
          FaultFreeMTr coord votes
            { localState := st, yesVotes := yv, sawNo := false, alive := Finset.univ,
              msgs := rest + R.val.map .voteRequest } s' ∧
          s'.localState = (fun p => if p ∈ R then .uncertain else st p) ∧
          s'.yesVotes = yv ∪ R ∧ s'.sawNo = false ∧
          s'.alive = Finset.univ ∧ s'.msgs = rest := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _ st yv rest _ _
    refine ⟨_, FaultFreeMTr.refl _, ?_, ?_, rfl, rfl, ?_⟩ <;> simp
  | @insert q R hqR ih =>
    intro hcoord st yv rest hst_c hst_R
    have hqc : q ≠ coord := fun h => hcoord (h ▸ Finset.mem_insert_self q R)
    have hcoordR : coord ∉ R := fun h => hcoord (Finset.mem_insert_of_mem h)
    have hst_q : st q = .init := hst_R q (Finset.mem_insert_self q R)
    let s₀ : TwoPCState P :=
      { localState := st, yesVotes := yv, sawNo := false, alive := Finset.univ,
        msgs := rest + (insert q R).val.map .voteRequest }
    let s₁ : TwoPCState P :=
      { localState := Function.update st q .uncertain, yesVotes := yv, sawNo := false,
        alive := Finset.univ, msgs := rest + R.val.map .voteRequest + {TwoPCMsg.voteReply q .yes} }
    have hstep₁ : twoPCStep? coord votes s₀ (.recvRequest q) = some s₁ := by
      simp [twoPCStep?, s₀, s₁, hqc, hst_q, hyes q, Finset.insert_val_of_notMem hqR]
    let s₂ : TwoPCState P :=
      { localState := Function.update st q .uncertain, yesVotes := insert q yv, sawNo := false,
        alive := Finset.univ, msgs := rest + R.val.map .voteRequest }
    have hstep₂ : twoPCStep? coord votes s₁ (.recvVote q .yes) = some s₂ := by
      simp [twoPCStep?, s₁, s₂, hqc.symm, hst_c,
        Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self _)]
    have hst₂_R : ∀ r ∈ R, Function.update st q .uncertain r = .init := fun r hr => by
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hr hqR)]
      exact hst_R r (Finset.mem_insert_of_mem hr)
    obtain ⟨s', hff, hloc, hyv, hsaw, halive, hmsgs⟩ :=
      ih hcoordR (Function.update st q .uncertain) (insert q yv) rest
        (by rwa [Function.update_of_ne hqc.symm]) hst₂_R
    refine ⟨s', FaultFreeMTr.step rfl hstep₁ (FaultFreeMTr.step rfl hstep₂ hff),
      hloc.trans (ite_mem_update_eq_insert R q .uncertain st), ?_, hsaw, halive, hmsgs⟩
    rw [hyv]; ext p; simp only [Finset.mem_union, Finset.mem_insert]; tauto

/-- Deliver Phase 2 verdicts `d` to every cohort in `R`. -/
private theorem faultFree_deliver_verdicts (d : Decision) :
    ∀ R : Finset P, coord ∉ R →
      ∀ (st : P → TwoPCLocalState) (yv : Finset P) (sn : Bool) (rest : Multiset (TwoPCMsg P)),
        (∀ r ∈ R, st r = .uncertain ∨ (d = .abort ∧ st r = .init)) →
        ∃ s' : TwoPCState P,
          FaultFreeMTr coord votes
            { localState := st, yesVotes := yv, sawNo := sn, alive := Finset.univ,
              msgs := rest + R.val.map (fun r => TwoPCMsg.verdict r d) } s' ∧
          s'.localState = (fun p => if p ∈ R then d.toTwoPCLocal else st p) ∧
          s'.alive = Finset.univ ∧ s'.msgs = rest := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _ st yv sn rest _
    refine ⟨_, FaultFreeMTr.refl _, ?_, rfl, ?_⟩ <;> simp
  | @insert q R hqR ih =>
    intro hcoord st yv sn rest hst_R
    have hqc : q ≠ coord := fun h => hcoord (h ▸ Finset.mem_insert_self q R)
    have hcoordR : coord ∉ R := fun h => hcoord (Finset.mem_insert_of_mem h)
    have hst_q := hst_R q (Finset.mem_insert_self q R)
    let s₀ : TwoPCState P :=
      { localState := st, yesVotes := yv, sawNo := sn, alive := Finset.univ,
        msgs := rest + (insert q R).val.map (fun r => TwoPCMsg.verdict r d) }
    let s₁ : TwoPCState P :=
      { localState := Function.update st q d.toTwoPCLocal, yesVotes := yv, sawNo := sn,
        alive := Finset.univ, msgs := rest + R.val.map (fun r => TwoPCMsg.verdict r d) }
    have hstep₁ : twoPCStep? coord votes s₀ (.recvVerdict q d) = some s₁ := by
      simp [twoPCStep?, s₀, s₁, hqc, hst_q, Finset.insert_val_of_notMem hqR]
    have hst₁_R : ∀ r ∈ R,
        Function.update st q d.toTwoPCLocal r = .uncertain ∨
          (d = .abort ∧ Function.update st q d.toTwoPCLocal r = .init) := fun r hr => by
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hr hqR)]
      exact hst_R r (Finset.mem_insert_of_mem hr)
    obtain ⟨s', hff, hloc, halive, hmsgs⟩ :=
      ih hcoordR (Function.update st q d.toTwoPCLocal) yv sn rest hst₁_R
    exact ⟨s', FaultFreeMTr.step rfl hstep₁ hff,
      hloc.trans (ite_mem_update_eq_insert R q d.toTwoPCLocal st), halive, hmsgs⟩

private abbrev twoPCAfterRequests (coord : P) : TwoPCState P where
  localState := Function.update (fun _ => .init) coord .waitVotes
  yesVotes := ∅
  sawNo := false
  alive := Finset.univ
  msgs := 0 + (Finset.univ.erase coord).val.map .voteRequest

private theorem twoPCStep?_sendRequests_start (coord : P) (votes : P → Vote) :
    twoPCStep? coord votes (twoPCStart P) .sendRequests = some (twoPCAfterRequests coord) := by
  simp [twoPCStep?, twoPCStart, twoPCAfterRequests]

/-- Shared all-`.yes` execution prefix from `twoPCStart P` through Phase 1 vote collection and
`coordCommit`, used by both `twoPC_failureFree_commit_failStop` and
`twoPC_uncertain_bivalent_failStop`. -/
private theorem faultFree_to_coordCommit (coord : P) (hyes : ∀ p, votes p = .yes) :
    ∃ s₃ : TwoPCState P,
      FaultFreeMTr coord votes (twoPCStart P) s₃ ∧
      (∀ p, s₃.localState p = if p = coord then .committed else .uncertain) ∧
      s₃.alive = Finset.univ ∧
      s₃.msgs = 0 + (Finset.univ.erase coord).val.map (fun r => TwoPCMsg.verdict r .commit) := by
  let C := Finset.univ.erase coord
  have hstep_req := twoPCStep?_sendRequests_start coord votes
  have hinit_C : ∀ r ∈ C, Function.update (fun _ : P => TwoPCLocalState.init) coord .waitVotes r =
      .init := fun r hr => Function.update_of_ne (Finset.ne_of_mem_erase hr) _ _
  obtain ⟨s₂, hff₂, hloc₂, hyv₂, hsaw₂, halive₂, hmsgs₂⟩ :=
    faultFree_collect_all_yes (coord := coord) hyes C (Finset.notMem_erase coord _)
      (Function.update (fun _ => .init) coord .waitVotes) ∅ 0 (Function.update_self _ _ _) hinit_C
  have hloc₂_c : s₂.localState coord = .waitVotes := by simp [hloc₂, C]
  have hsub₂ : C ⊆ s₂.yesVotes := by rw [hyv₂]; simp
  let s₃ : TwoPCState P :=
    { localState := Function.update s₂.localState coord .committed, yesVotes := s₂.yesVotes,
      sawNo := s₂.sawNo, alive := Finset.univ,
      msgs := 0 + C.val.map (fun r => TwoPCMsg.verdict r .commit) }
  have hstep_com : twoPCStep? coord votes s₂ .coordCommit = some s₃ := by
    simp [twoPCStep?, s₃, C, halive₂, hloc₂_c, hyes coord, hsaw₂, hsub₂, hmsgs₂]
  refine ⟨s₃, .step rfl hstep_req (hff₂.trans (.step rfl hstep_com (.refl s₃))), fun p => ?_,
    rfl, rfl⟩
  by_cases hpc : p = coord <;> simp [s₃, hpc, hloc₂, C]

/-- Fail-stop register-state step toward [Gray1978], §5.8.3.3.2 (pp. 467–468), not the cited
crash-recovery log-replay result (#7289): when all sites vote `.yes`, `twoPCLts` admits a
crash-free, omission-free execution from `twoPCStart P` reaching `AllDecided s.decision .commit`
with all sites operational and an empty network (`AC3`). -/
theorem twoPC_failureFree_commit_failStop (coord : P) (hyes : ∀ p, votes p = .yes) :
    ∃ tr s, (∀ a ∈ tr, a.isFaultFree = true) ∧
      (twoPCLts coord votes).MTr (twoPCStart P) tr s ∧
      AllDecided s.decision .commit ∧ s.alive = Finset.univ ∧ s.msgs = 0 := by
  let C := Finset.univ.erase coord
  obtain ⟨⟨st, yv, sn, _, _⟩, hff₃, hloc₃, rfl, rfl⟩ := faultFree_to_coordCommit coord hyes
  dsimp only at hloc₃
  have hunc_C : ∀ r ∈ C, st r = .uncertain ∨ (Decision.commit = .abort ∧ st r = .init) :=
    fun r hr => Or.inl (by simp [hloc₃ r, Finset.ne_of_mem_erase hr])
  obtain ⟨s₄, hff₄, hloc₄, halive₄, hmsgs₄⟩ :=
    faultFree_deliver_verdicts (coord := coord) (votes := votes) .commit C
      (Finset.notMem_erase coord _) st yv sn 0 hunc_C
  obtain ⟨tr, hff, hmtr⟩ := hff₃.trans hff₄
  refine ⟨tr, s₄, hff, hmtr, fun p => ?_, halive₄, hmsgs₄⟩
  by_cases hpc : p = coord <;> simp [TwoPCState.decision, hloc₄, hloc₃, C, hpc]

/-- Fail-stop register-state step toward [Gray1978], §5.8.3.3.2 (pp. 467–468), not the cited
crash-recovery log-replay result (#7289): when at least one site votes `.no`, `twoPCLts` admits a
crash-free, omission-free execution from `twoPCStart P` reaching `AllDecided s.decision .abort`. -/
theorem twoPC_failureFree_abort_failStop (coord : P) (hno : ∃ p, votes p = .no) :
    ∃ tr s, (∀ a ∈ tr, a.isFaultFree = true) ∧
      (twoPCLts coord votes).MTr (twoPCStart P) tr s ∧
      AllDecided s.decision .abort ∧ s.alive = Finset.univ := by
  let C := Finset.univ.erase coord
  let s₁ := twoPCAfterRequests coord
  have hstep_req : twoPCStep? coord votes (twoPCStart P) .sendRequests = some s₁ :=
    twoPCStep?_sendRequests_start coord votes
  by_cases hcno : votes coord = .no
  · let s₂ : TwoPCState P :=
      { localState := Function.update s₁.localState coord .aborted, yesVotes := s₁.yesVotes,
        sawNo := s₁.sawNo, alive := Finset.univ,
        msgs := s₁.msgs + C.val.map (fun r => TwoPCMsg.verdict r .abort) }
    have hstep_ab : twoPCStep? coord votes s₁ .coordAbort = some s₂ := by
      simp [twoPCStep?, s₁, s₂, hcno, C]
    have hinit_C : ∀ r ∈ C, s₂.localState r = .uncertain ∨
        (Decision.abort = .abort ∧ s₂.localState r = .init) := fun r hr =>
      Or.inr ⟨rfl, by simp [s₂, s₁, Function.update, Finset.ne_of_mem_erase hr]⟩
    obtain ⟨s₃, hff₃, hloc₃, halive₃, _⟩ :=
      faultFree_deliver_verdicts (coord := coord) (votes := votes) .abort C
        (Finset.notMem_erase coord _) s₂.localState s₂.yesVotes s₂.sawNo s₁.msgs hinit_C
    obtain ⟨tr, hff, hmtr⟩ :=
      FaultFreeMTr.step rfl hstep_req (FaultFreeMTr.step rfl hstep_ab hff₃)
    refine ⟨tr, s₃, hff, hmtr, fun p => ?_, halive₃⟩
    by_cases hpc : p = coord <;> simp [TwoPCState.decision, hloc₃, s₂, C, hpc]
  · rcases hno with ⟨p₀, hp₀⟩
    have hp₀c : p₀ ≠ coord := fun h => hcno (h ▸ hp₀)
    have hp₀C : p₀ ∈ C := Finset.mem_erase.mpr ⟨hp₀c, Finset.mem_univ p₀⟩
    let s₂ : TwoPCState P :=
      { localState := Function.update s₁.localState p₀ .aborted, yesVotes := ∅, sawNo := false,
        alive := Finset.univ,
        msgs := s₁.msgs.erase (.voteRequest p₀) + {TwoPCMsg.voteReply p₀ .no} }
    have hstep_p₀ : twoPCStep? coord votes s₁ (.recvRequest p₀) = some s₂ := by
      simp [twoPCStep?, s₁, s₂, hp₀c, hp₀, Multiset.mem_erase_of_ne hp₀c]
    let s₃ : TwoPCState P :=
      { localState := s₂.localState, yesVotes := ∅, sawNo := true, alive := Finset.univ,
        msgs := s₂.msgs.erase (.voteReply p₀ .no) }
    have hstep_v : twoPCStep? coord votes s₂ (.recvVote p₀ .no) = some s₃ := by
      simp [twoPCStep?, s₁, s₂, s₃, hp₀c.symm]
    let C' := C.erase p₀
    let s₄ : TwoPCState P :=
      { localState := Function.update s₃.localState coord .aborted, yesVotes := ∅, sawNo := true,
        alive := Finset.univ, msgs := s₃.msgs + C.val.map (fun r => TwoPCMsg.verdict r .abort) }
    have hstep_ab : twoPCStep? coord votes s₃ .coordAbort = some s₄ := by
      simp [twoPCStep?, s₁, s₂, s₃, s₄, hp₀c.symm, C]
    have hinit_C' : ∀ r ∈ C', s₄.localState r = .uncertain ∨
        (Decision.abort = .abort ∧ s₄.localState r = .init) := fun r hr =>
      Or.inr ⟨rfl, by simp [s₄, s₃, s₂, s₁, Function.update, Finset.ne_of_mem_erase hr,
        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)]⟩
    have hcoordC' : coord ∉ C' := fun h =>
      Finset.notMem_erase coord _ (Finset.mem_of_mem_erase h)
    obtain ⟨s₅, hff₅, hloc₅, halive₅, _⟩ :=
      faultFree_deliver_verdicts (coord := coord) (votes := votes) .abort C' hcoordC'
        s₄.localState s₄.yesVotes s₄.sawNo (s₃.msgs + {.verdict p₀ .abort}) hinit_C'
    have hC : C.val = p₀ ::ₘ C'.val := by
      rw [← Finset.insert_erase hp₀C, Finset.insert_val_of_notMem (Finset.notMem_erase p₀ C)]
    rw [Multiset.add_assoc, Multiset.singleton_add,
      ← Multiset.map_cons (fun r => TwoPCMsg.verdict r .abort), ← hC] at hff₅
    obtain ⟨tr, hff, hmtr⟩ := FaultFreeMTr.step rfl hstep_req (FaultFreeMTr.step rfl hstep_p₀
      (FaultFreeMTr.step rfl hstep_v (FaultFreeMTr.step rfl hstep_ab hff₅)))
    refine ⟨tr, s₅, hff, hmtr, fun p => ?_, halive₅⟩
    rcases eq_or_ne p coord with rfl | hpc
    · simp [TwoPCState.decision, hloc₅, C', C, s₄]
    rcases eq_or_ne p p₀ with rfl | hpp₀
    · simp [TwoPCState.decision, hloc₅, C', s₄, s₃, s₂, hp₀c]
    · simp [TwoPCState.decision, hloc₅, C', C, hpc, hpp₀]

/-! ### Coordinator-crash uncertainty and inherent blocking of `2PC` -/

/-- Projection of a `2PC` global configuration visible to the surviving operational processes:
the operational survivor set `alive`, each survivor's local state (masked to `.init` outside
`alive`), each survivor's initial vote (masked to `.yes` outside `alive`), and all in-flight
messages addressed to survivors. -/
structure TwoPCSurvivorView (P : Type*) where
  /-- Currently operational sites. -/
  alive : Finset P
  /-- Local states of operational sites (`.init` outside `alive`). -/
  survivorState : P → TwoPCLocalState
  /-- Initial votes of operational sites (`.yes` outside `alive`). -/
  survivorVote : P → Vote
  /-- In-flight messages addressed to operational sites. -/
  inbox : Multiset (TwoPCMsg P)

/-- Extract the survivor-visible projection of a `2PC` configuration `s`. -/
@[expose] def TwoPCState.survivorView {P : Type*} [DecidableEq P] (coord : P) (votes : P → Vote)
    (s : TwoPCState P) : TwoPCSurvivorView P where
  alive := s.alive
  survivorState := fun p => if p ∈ s.alive then s.localState p else .init
  survivorVote := fun p => if p ∈ s.alive then votes p else .yes
  inbox := s.msgs.filter (fun m => m.recipient coord ∈ s.alive)

private theorem canReach_drop_all_msgs (s : TwoPCState P) :
    (twoPCLts coord votes).CanReach s { s with msgs := 0 } := by
  obtain ⟨st, yv, sn, al, ms⟩ := s
  induction ms using Multiset.induction_on with
  | empty => exact LTS.CanReach.refl _ _
  | @cons m ms ih =>
    have hstep : twoPCStep? coord votes ⟨st, yv, sn, al, m ::ₘ ms⟩ (.dropMsg m) =
        some ⟨st, yv, sn, al, ms⟩ := by
      simp [twoPCStep?]
    exact twoPC_canReach_trans ⟨[TwoPCAction.dropMsg m], LTS.MTr.single _ hstep⟩ ih

private theorem canReach_crash_set :
    ∀ (dead : Finset P) (s : TwoPCState P), dead ⊆ s.alive →
      (twoPCLts coord votes).CanReach s { s with alive := s.alive \ dead } := by
  intro dead s hsub
  induction dead using Finset.induction_on generalizing s with
  | empty => simpa using LTS.CanReach.refl (twoPCLts coord votes) s
  | @insert p dead hp ih =>
    have hstep : twoPCStep? coord votes s (.crash p) =
        some { s with alive := s.alive.erase p } := by
      simp [twoPCStep?, hsub (Finset.mem_insert_self p dead)]
    have hreach := twoPC_canReach_trans ⟨[TwoPCAction.crash p], LTS.MTr.single _ hstep⟩
      (ih { s with alive := s.alive.erase p } fun r hr => Finset.mem_erase.mpr
        ⟨ne_of_mem_of_not_mem hr hp, hsub (Finset.mem_insert_of_mem hr)⟩)
    convert hreach using 2
    ext r
    simp [and_assoc, and_comm, and_left_comm]

/-- Fail-stop register-state step toward [Skeen1981], §1 (p. 134) and [SkeenStonebraker1983],
§IV-C, Lemma 1 (p. 223), not the cited crash-recovery result (#7289): for `2 ≤ Fintype.card P` and
any coordinator `coord : P`, there exist a surviving cohort `q ≠ coord`, vote profile `votesAbort`
(`votesAbort coord = .no`, `votesAbort q = .yes`), and `twoPCLts`-reachable configurations `sAbort`
and `sCommit` such that:
1. in both configurations `q` is the sole operational survivor (`alive = {q}`), is `.uncertain`,
   and has an empty network (`msgs = 0`),
2. `sAbort` and `sCommit` induce the exact same `TwoPCSurvivorView`,
3. `coord` has already decided `.abort` in `sAbort` whereas `coord` has already decided `.commit`
   in `sCommit`. -/
theorem twoPC_uncertain_bivalent_failStop (hcard : 2 ≤ Fintype.card P) (coord : P) :
    ∃ (q : P) (votesAbort : P → Vote) (sAbort sCommit : TwoPCState P),
      q ≠ coord ∧
      votesAbort coord = .no ∧
      votesAbort q = .yes ∧
      TwoPCReachable coord votesAbort sAbort ∧
      TwoPCReachable coord (fun _ => .yes) sCommit ∧
      sAbort.alive = {q} ∧
      sAbort.localState q = .uncertain ∧
      sAbort.msgs = 0 ∧
      sAbort.decision coord = some .abort ∧
      sCommit.decision coord = some .commit ∧
      sAbort.survivorView coord votesAbort =
        sCommit.survivorView coord (fun _ => .yes) := by
  obtain ⟨q, hqC⟩ : (Finset.univ.erase coord).Nonempty := by
    rw [Finset.erase_nonempty (Finset.mem_univ coord), Finset.univ_nontrivial_iff]
    exact Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hqc : q ≠ coord := Finset.ne_of_mem_erase hqC
  let votesAbort : P → Vote := fun p => if p = coord then .no else .yes
  let votesCommit : P → Vote := fun _ => .yes
  let C := Finset.univ.erase coord
  -- 1. Construct `sAbort`: `sendRequests`, `recvRequest q`, `coordAbort`, drop all msgs, crash
  --    `univ.erase q`.
  let sa₁ := twoPCAfterRequests coord
  have hsa_step₁ : twoPCStep? coord votesAbort (twoPCStart P) .sendRequests = some sa₁ :=
    twoPCStep?_sendRequests_start coord votesAbort
  let sa₂ : TwoPCState P :=
    { localState := Function.update sa₁.localState q .uncertain, yesVotes := ∅, sawNo := false,
      alive := Finset.univ, msgs := sa₁.msgs.erase (.voteRequest q) + {TwoPCMsg.voteReply q .yes} }
  have hsa_step₂ : twoPCStep? coord votesAbort sa₁ (.recvRequest q) = some sa₂ := by
    simp [twoPCStep?, sa₁, sa₂, hqc, votesAbort, Multiset.mem_erase_of_ne hqc]
  let sa₃ : TwoPCState P :=
    { localState := Function.update sa₂.localState coord .aborted, yesVotes := ∅, sawNo := false,
      alive := Finset.univ, msgs := sa₂.msgs + C.val.map (fun r => TwoPCMsg.verdict r .abort) }
  have hsa_step₃ : twoPCStep? coord votesAbort sa₂ .coordAbort = some sa₃ := by
    simp [twoPCStep?, sa₁, sa₂, sa₃, hqc.symm, votesAbort, C]
  let sa₄ : TwoPCState P := { sa₃ with msgs := 0 }
  let sAbort : TwoPCState P := { sa₄ with alive := Finset.univ \ (Finset.univ.erase q) }
  have hreach_abort : TwoPCReachable coord votesAbort sAbort :=
    twoPC_canReach_trans ⟨[.sendRequests], LTS.MTr.single _ hsa_step₁⟩
      (twoPC_canReach_trans ⟨[.recvRequest q], LTS.MTr.single _ hsa_step₂⟩
        (twoPC_canReach_trans ⟨[.coordAbort], LTS.MTr.single _ hsa_step₃⟩
          (twoPC_canReach_trans (canReach_drop_all_msgs sa₃)
            (canReach_crash_set (Finset.univ.erase q) sa₄ (Finset.subset_univ _)))))
  -- 2. Construct `sCommit` under `votesCommit`: reuse `faultFree_to_coordCommit`, then drop all
  --    msgs and crash `univ.erase q`.
  obtain ⟨sc₃, ⟨tr_c, _, hmtr_c⟩, hloc_sc₃, halive_sc₃, _⟩ :=
    faultFree_to_coordCommit (votes := votesCommit) coord (fun _ => rfl)
  let sc₄ : TwoPCState P := { sc₃ with msgs := 0 }
  let sCommit : TwoPCState P := { sc₄ with alive := sc₄.alive \ (Finset.univ.erase q) }
  have hreach_commit : TwoPCReachable coord votesCommit sCommit :=
    twoPC_canReach_trans ⟨tr_c, hmtr_c⟩
      (twoPC_canReach_trans (canReach_drop_all_msgs sc₃)
        (canReach_crash_set (Finset.univ.erase q) sc₄ (by simp [sc₄, halive_sc₃])))
  have halive_q : Finset.univ \ (Finset.univ.erase q) = ({q} : Finset P) := by
    ext r; simp
  have halive_sc : sCommit.alive = {q} := by simp [sCommit, sc₄, halive_sc₃, halive_q]
  have hsa_q : sAbort.localState q = .uncertain := by
    simp [sAbort, sa₄, sa₃, sa₂, Function.update, hqc]
  have hsc_q : sCommit.localState q = .uncertain := by
    simp [sCommit, sc₄, hloc_sc₃, hqc]
  refine ⟨q, votesAbort, sAbort, sCommit, hqc, by simp [votesAbort], by simp [votesAbort, hqc],
    hreach_abort, hreach_commit, halive_q, hsa_q, rfl, ?_, ?_, ?_⟩
  · simp [TwoPCState.decision, sAbort, sa₄, sa₃]
  · simp [TwoPCState.decision, sCommit, sc₄, hloc_sc₃]
  · have halive_sa : sAbort.alive = {q} := halive_q
    have h0 : sAbort.msgs = 0 ∧ sCommit.msgs = 0 := ⟨rfl, rfl⟩
    simp only [TwoPCState.survivorView, halive_sa, halive_sc, h0.1, h0.2, Multiset.filter_zero,
      TwoPCSurvivorView.mk.injEq, true_and, and_true]
    constructor <;> funext r <;> by_cases hrq : r = q <;> simp [hrq, hsa_q, hsc_q, votesAbort, hqc]

/-- Fail-stop register-state step toward [Gray1978], §5.8.3.3.2 (p. 469), [Skeen1981], §1
(p. 134), and [SkeenStonebraker1983], §IV-C, Lemma 1 (p. 223), not the cited crash-recovery result
(#7289): for `2 ≤ Fintype.card P`, no termination rule `term` depending only on the surviving
processes' `TwoPCSurvivorView` can assign decisions to undecided survivors in a way that preserves
`UniformAgreement` across all reachable configurations of `twoPCLts`. -/
theorem twoPC_no_safe_survivor_termination_failStop (hcard : 2 ≤ Fintype.card P) (coord : P)
    (term : TwoPCSurvivorView P → Decision) :
    ∃ (votes : P → Vote) (s : TwoPCState P),
      TwoPCReachable coord votes s ∧ s.alive.Nonempty ∧
      ¬ UniformAgreement (fun p =>
        match s.decision p with
        | some d => some d
        | none => if p ∈ s.alive then some (term (s.survivorView coord votes)) else none) := by
  obtain ⟨q, votesAbort, sAbort, sCommit, _, _, _, hrA, hrC, haliveA, hlocA, _, hdecA, hdecC,
    hview⟩ := twoPC_uncertain_bivalent_failStop hcard coord
  have haliveC : sCommit.alive = {q} := by
    simpa [TwoPCState.survivorView, haliveA] using (congrArg TwoPCSurvivorView.alive hview).symm
  cases hd : term (sAbort.survivorView coord votesAbort) with
  | commit =>
    refine ⟨votesAbort, sAbort, hrA, ⟨q, by simp [haliveA]⟩, fun hagr => ?_⟩
    cases hagr q coord .commit .abort (by simp [TwoPCState.decision, hlocA, haliveA, hd])
      (by simp [hdecA])
  | abort =>
    have hlocC : sCommit.localState q = .uncertain := by
      simpa [TwoPCState.survivorView, haliveA, haliveC, hlocA] using
        (congrFun (congrArg TwoPCSurvivorView.survivorState hview) q).symm
    have hdC : term (sCommit.survivorView coord (fun _ => .yes)) = .abort :=
      (congrArg term hview).symm.trans hd
    refine ⟨fun _ => .yes, sCommit, hrC, ⟨q, by simp [haliveC]⟩, fun hagr => ?_⟩
    cases hagr q coord .abort .commit (by simp [TwoPCState.decision, hlocC, haliveC, hdC])
      (by simp [hdecC])

end Safety

end Cslib.Distributed.AtomicCommit
