/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Finite-batch log-append universal construction over single-use consensus cells

This module formalizes the finite-invocation-batch (`P`), unhelped log-append step over idealized
single-use `ConsensusCell` slots (after [Herlihy1991], §4.1, pp. 143–146, Figure 14 p. 145 &
Theorem 14 p. 146) toward `#7199`. As Herlihy observes ([Herlihy1991], §4.1, p. 144), omitting the
`announce[1..n]` helping array makes log-append nonblocking rather than wait-free across unbounded
invocation streams: here `P` indexes a **finite batch** of invocations (`Fintype P`), slots are
modeled as idealized predetermined-winner `ConsensusCell`s under `ValidSlotSchedule` rather than
`Protocol` executions, and [Herlihy1991]'s `announce`/helping array and §4.2 cell reclamation remain
open in `#7199`.

Within this finite-batch log-append model:

* Each `ConsensusCell α` models a single-use consensus slot whose `propose` operation returns the
  unique agreed winner for that slot (`propose_eq`).
* `applyLog` replays the deterministic sequential state machine `M` (`SeqSpec State Op Resp`) from
  `M.init` along a list of agreed `(caller, operation)` commands, and `slotLog` reads the agreed
  prefix of length `k` from `slot` (`slotLog_eq` shows all callers reconstruct the identical log
  prefix without shared locks).
* `universalInvoke` executes a tagged operation `(p, op)` starting from the settled log length
  `startSlot` observed when the invocation begins, proposing `(p, op)` to consecutive consensus
  slots until `p` wins a slot `k` and then returning the exact sequential response of `M.step`
  applied to `applyLog M (slotLog slot (p, op) k)`.
* Under `ValidSlotSchedule` (consensus validity, start-time causality, and at-most-once winning
  across the finite invocation batch `P`), pigeonhole on `Fintype.card P` proves completion within
  at most `Fintype.card P` slot attempts (`universalInvoke_terminates`), unique per-invocation
  linearization slots (`universalInvoke_slotIdx_injective`), and Herlihy–Wing linearizability
  preserving sequential state-machine responses and real-time precedence (`universalInvoke_spec`,
  `universalInvoke_linearizable_of_validSlotSchedule`).

## Main definitions

* `Cslib.Distributed.SharedMemory.SeqSpec`: deterministic sequential state-machine specification.
* `Cslib.Distributed.SharedMemory.ConsensusCell`: idealized single-use consensus slot (`propose`
  and `propose_eq`), with computable constructor `ConsensusCell.ofWinner`.
* `Cslib.Distributed.SharedMemory.applyLog`, `Cslib.Distributed.SharedMemory.slotLog`: sequential
  log replay and prefix reconstruction from consensus slots.
* `Cslib.Distributed.SharedMemory.UniversalResult`: completed invocation output (`slotIdx`, `resp`).
* `Cslib.Distributed.SharedMemory.universalInvokeAux`,
  `Cslib.Distributed.SharedMemory.universalInvoke`: finite-batch log-append universal invocation.
* `Cslib.Distributed.SharedMemory.SlotActive`,
  `Cslib.Distributed.SharedMemory.ValidSlotSchedule`: validity and causality conditions on a
  concurrent consensus-slot execution over `P`.

## Main results

* `Cslib.Distributed.SharedMemory.universalInvoke_terminates`: every invocation `p : P` under a
  `ValidSlotSchedule` completes within `Fintype.card P` consensus slots from `startSlot p`.
* `Cslib.Distributed.SharedMemory.universalInvoke_spec`: linearizable state-machine safety —
  every completed invocation owns its consensus slot `k = res.slotIdx`, returns the exact
  sequential response `(M.step (applyLog M (slotLog slot probe k)) (ops p)).2`, and advances the
  replayed sequential state to `applyLog M (slotLog slot probe (k + 1))`.
* `Cslib.Distributed.SharedMemory.universalInvoke_slotIdx_injective`: distinct invocations win
  distinct consensus log indices (giving a strict total linearization order on `P`).
* `Cslib.Distributed.SharedMemory.universalInvoke_linearizable_of_validSlotSchedule`: finite-batch
  linearizability under `ValidSlotSchedule` — every invocation completes within `Fintype.card P`
  slots with a unique log slot, exact sequential state-machine response, and real-time precedence
  (`(res p).slotIdx < startSlot q → (res p).slotIdx < (res q).slotIdx`).
* `Cslib.Distributed.SharedMemory.universalInvoke_slotIdx_bijective_of_validSlotSchedule`: when all
  invocations start at `0` under `ValidSlotSchedule`, the winning slots form a bijection
  `P ≃ Fin (Fintype.card P)` permuting all `Fintype.card P` operations into a single sequential
  execution of `M`.

## References

* [M. Herlihy, *Wait-Free Synchronization*][Herlihy1991]
-/

public section

namespace Cslib.Distributed.SharedMemory

/-- Deterministic sequential object specification with state type `State`, initial state `init`,
operation type `Op`, response type `Resp`, and transition `step` returning
`(nextState, response)`. -/
structure SeqSpec (State Op Resp : Type*) where
  /-- Initial state of the sequential state machine. -/
  init : State
  /-- Sequential transition taking `(state, op)` to `(nextState, response)`. -/
  step : State → Op → State × Resp

/-- Idealized single-use consensus cell over `α`: every caller invoking `propose` receives the
same agreed winning value (`propose_eq`). -/
structure ConsensusCell (α : Type*) where
  /-- Propose a candidate value to this consensus slot and receive the slot's winning value. -/
  propose : α → α
  /-- Agreement: all proposals to the same slot return the identical winning value. -/
  propose_eq : ∀ x y, propose x = propose y

namespace ConsensusCell

/-- Construct a `ConsensusCell` with predetermined winning value `w` (useful for executable test
schedules). -/
@[expose]
def ofWinner {α : Type*} (w : α) : ConsensusCell α where
  propose _ := w
  propose_eq _ _ := rfl

end ConsensusCell

/-- Replay sequential specification `M` from `M.init` along a list of `(caller, operation)` log
entries, returning the resulting sequential state. -/
@[expose]
def applyLog {P State Op Resp : Type*} (M : SeqSpec State Op Resp) (log : List (P × Op)) : State :=
  log.foldl (fun s entry => (M.step s entry.2).1) M.init

@[simp]
theorem applyLog_nil {P State Op Resp : Type*} (M : SeqSpec State Op Resp) :
    applyLog (P := P) M [] = M.init :=
  rfl

@[simp]
theorem applyLog_append_singleton {P State Op Resp : Type*} (M : SeqSpec State Op Resp)
    (log : List (P × Op)) (entry : P × Op) :
    applyLog M (log ++ [entry]) = (M.step (applyLog M log) entry.2).1 := by
  simp only [applyLog, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Reconstruct the agreed log prefix of length `n` from consensus slots `0, ..., n - 1` using any
probe proposal `probe`. -/
@[expose]
def slotLog {P Op : Type*} (slot : ℕ → ConsensusCell (P × Op)) (probe : P × Op) (n : ℕ) :
    List (P × Op) :=
  (List.range n).map fun i => (slot i).propose probe

@[simp]
theorem length_slotLog {P Op : Type*} (slot : ℕ → ConsensusCell (P × Op)) (probe : P × Op)
    (n : ℕ) : (slotLog slot probe n).length = n := by
  simp only [slotLog, List.length_map, List.length_range]

/-- **Log agreement:** every caller reconstructs the exact same prefix log from `slot`, regardless
of the proposal argument it supplies. -/
theorem slotLog_eq {P Op : Type*} (slot : ℕ → ConsensusCell (P × Op)) (x y : P × Op) (n : ℕ) :
    slotLog slot x n = slotLog slot y n :=
  List.map_congr_left fun i _ => (slot i).propose_eq x y

private theorem slotLog_succ {P Op : Type*} (slot : ℕ → ConsensusCell (P × Op)) (probe : P × Op)
    (k : ℕ) :
    slotLog slot probe (k + 1) = slotLog slot probe k ++ [(slot k).propose probe] := by
  simp only [slotLog, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- Advancing the agreed consensus log from `k` to `k + 1` steps the sequential state machine `M`
by the winning command of slot `k`. -/
theorem applyLog_slotLog_succ {P State Op Resp : Type*} (M : SeqSpec State Op Resp)
    (slot : ℕ → ConsensusCell (P × Op)) (probe : P × Op) (k : ℕ) :
    applyLog M (slotLog slot probe (k + 1)) =
      (M.step (applyLog M (slotLog slot probe k)) ((slot k).propose probe).2).1 := by
  rw [slotLog_succ, applyLog_append_singleton]

/-- Output of a completed universal-construction invocation: its winning consensus slot `slotIdx`
(the linearization index in the global log) and its sequential response `resp`. -/
structure UniversalResult (Resp : Type*) where
  /-- Consensus log index won by this invocation. -/
  slotIdx : ℕ
  /-- Sequential state-machine response produced at `slotIdx`. -/
  resp : Resp
  deriving @[expose] DecidableEq

/-- Bounded-fuel loop of Herlihy's log-append universal construction: starting at consensus slot
`k`, caller `p` proposes `(p, op)` to consecutive slots until `p` wins a slot, then replays the
agreed log prefix `0 ..< k` on `M` and returns `M.step`'s response. -/
@[expose]
def universalInvokeAux {P State Op Resp : Type*} [DecidableEq P]
    (M : SeqSpec State Op Resp) (slot : ℕ → ConsensusCell (P × Op))
    (p : P) (op : Op) (k : ℕ) : ℕ → Option (UniversalResult Resp)
  | 0 => none
  | fuel + 1 =>
    if ((slot k).propose (p, op)).1 = p then
      let stateBefore := applyLog M (slotLog slot (p, op) k)
      some { slotIdx := k, resp := (M.step stateBefore op).2 }
    else
      universalInvokeAux M slot p op (k + 1) fuel

/-- Execute invocation `(p, op)` via Herlihy's universal construction starting from settled prefix
index `startSlot`, using `Fintype.card P` consensus attempts (the exact worst-case wait-free bound
when `P` bounds concurrent invocations). -/
@[expose]
def universalInvoke {P State Op Resp : Type*} [Fintype P] [DecidableEq P]
    (M : SeqSpec State Op Resp) (slot : ℕ → ConsensusCell (P × Op))
    (p : P) (op : Op) (startSlot : ℕ := 0) : Option (UniversalResult Resp) :=
  universalInvokeAux M slot p op startSlot (Fintype.card P)

/-- Consensus slot `k` is *active* under invocation operations `ops` and start prefix lengths
`startSlot` if either `k` lies in the pre-settled prefix observed before some invocation started
(`k < startSlot r`) or some already-started invocation `r` (`startSlot r ≤ k`) has not yet won any
earlier slot `j < k`. -/
@[expose]
def SlotActive {P Op : Type*} (slot : ℕ → ConsensusCell (P × Op))
    (ops : P → Op) (startSlot : P → ℕ) (k : ℕ) : Prop :=
  (∃ r, k < startSlot r) ∨
    ∃ r, startSlot r ≤ k ∧ ∀ j < k, ((slot j).propose (r, ops r)).1 ≠ r

/-- Validity and real-time causality of a sequence of consensus slots `slot` for a family of
invocations indexed by `P` with operations `ops` and start prefix lengths `startSlot`:
at every active slot `k`, the agreed winner `(q, cmd) = (slot k).propose probe` carries `q`'s own
operation `ops q`, `q` had already started by slot `k` (`startSlot q ≤ k`), and `q` had not already
won an earlier slot `j < k`. -/
structure ValidSlotSchedule {P Op : Type*} (slot : ℕ → ConsensusCell (P × Op))
    (ops : P → Op) (startSlot : P → ℕ) : Prop where
  /-- Every active slot's winning entry carries its winning caller's operation `ops`. -/
  winner_op : ∀ k, SlotActive slot ops startSlot k →
    ∀ probe, ((slot k).propose probe).2 = ops ((slot k).propose probe).1
  /-- Only an invocation that has begun (`startSlot q ≤ k`) can win active slot `k`. -/
  start_le : ∀ k, SlotActive slot ops startSlot k →
    ∀ probe, startSlot ((slot k).propose probe).1 ≤ k
  /-- An invocation stops proposing once it wins a slot, so no caller wins two slots `j < k`. -/
  fresh_winner : ∀ k, SlotActive slot ops startSlot k →
    ∀ j < k, ∀ probe, ((slot j).propose probe).1 ≠ ((slot k).propose probe).1

section SafetyAndLinearizability

variable {P State Op Resp : Type*} [DecidableEq P]
  {M : SeqSpec State Op Resp} {slot : ℕ → ConsensusCell (P × Op)}
  {ops : P → Op} {startSlot : P → ℕ}

private theorem universalInvokeAux_sound {p : P} {op : Op} {k fuel : ℕ}
    {res : UniversalResult Resp}
    (h : universalInvokeAux M slot p op k fuel = some res) :
    k ≤ res.slotIdx ∧
      res.slotIdx < k + fuel ∧
      ((slot res.slotIdx).propose (p, op)).1 = p ∧
      (∀ j, k ≤ j → j < res.slotIdx → ((slot j).propose (p, op)).1 ≠ p) ∧
      res.resp = (M.step (applyLog M (slotLog slot (p, op) res.slotIdx)) op).2 := by
  induction fuel generalizing k with
  | zero => simp only [universalInvokeAux, reduceCtorEq] at h
  | succ fuel ih =>
    simp only [universalInvokeAux] at h
    split at h
    · rename_i hwin
      simp only [Option.some.injEq] at h
      rw [← h]
      dsimp only
      exact ⟨le_rfl, by omega, hwin, fun j hkj hjk => by omega, rfl⟩
    · rename_i hnotwin
      obtain ⟨hle, hlt, hwin, hprev, hresp⟩ := ih h
      refine ⟨by omega, by omega, hwin, fun j hkj hjk => ?_, hresp⟩
      by_cases hj : j = k
      · subst hj
        exact hnotwin
      · exact hprev j (by omega) hjk

private theorem universalInvokeAux_eq_some_of_exists_win {p : P} {op : Op} {k fuel : ℕ}
    (hex : ∃ m, k ≤ m ∧ m < k + fuel ∧ ((slot m).propose (p, op)).1 = p) :
    ∃ res, universalInvokeAux M slot p op k fuel = some res := by
  induction fuel generalizing k with
  | zero =>
    obtain ⟨m, hkm, hmk, _⟩ := hex
    omega
  | succ fuel ih =>
    simp only [universalInvokeAux]
    split
    · exact ⟨_, rfl⟩
    · rename_i hnotwin
      apply ih
      obtain ⟨m, hkm, hmk, hm_win⟩ := hex
      have hne : m ≠ k := by
        rintro rfl
        exact hnotwin hm_win
      exact ⟨m, by omega, by omega, hm_win⟩

omit [DecidableEq P] in
/-- No invocation `p` can win a slot `j < startSlot p` before `p` has begun. -/
private theorem ValidSlotSchedule.ne_winner_before_start
    (hsched : ValidSlotSchedule slot ops startSlot) (p : P) {j : ℕ} (hj : j < startSlot p)
    (probe : P × Op) : ((slot j).propose probe).1 ≠ p := by
  intro heq
  have hact : SlotActive slot ops startSlot j := Or.inl ⟨p, hj⟩
  have hle := hsched.start_le j hact probe
  rw [heq] at hle
  omega

/-- **Wait-free bounded termination of `universalInvoke`:** under `ValidSlotSchedule`, every
invocation `p : P` wins a consensus slot and returns `some res` within at most `Fintype.card P`
attempts from `startSlot p`. -/
theorem universalInvoke_terminates [Fintype P]
    (hsched : ValidSlotSchedule slot ops startSlot) (p : P) :
    ∃ res, universalInvoke M slot p (ops p) (startSlot p) = some res := by
  apply universalInvokeAux_eq_some_of_exists_win
  by_contra hnowin
  push Not at hnowin
  let s := startSlot p
  let n := Fintype.card P
  have hact_range (i : Fin n) : SlotActive slot ops startSlot (s + i.val) := by
    refine Or.inr ⟨p, by omega, fun j hj => ?_⟩
    by_cases hjs : j < s
    · exact hsched.ne_winner_before_start p hjs (p, ops p)
    · exact hnowin j (by omega) (by omega)
  let winOf : Fin n → P := fun i => ((slot (s + i.val)).propose (p, ops p)).1
  have hwin_inj : Function.Injective winOf := fun i₁ i₂ heq => by
    by_contra hne
    rcases Nat.lt_trichotomy i₁.val i₂.val with hlt | hveq | hgt
    · exact hsched.fresh_winner _ (hact_range i₂) _ (by omega) (p, ops p) heq
    · exact hne (Fin.ext hveq)
    · exact hsched.fresh_winner _ (hact_range i₁) _ (by omega) (p, ops p) heq.symm
  have hnotMem : p ∉ Set.range winOf := fun ⟨i, hi⟩ =>
    hnowin (s + i.val) (by omega) (by omega) hi
  exact absurd (Fintype.card_lt_of_injective_of_notMem winOf hwin_inj hnotMem) (by simp [n])

/-- **State-machine safety of `universalInvoke`:** when `universalInvoke` returns `some res` for
invocation `p` under `ValidSlotSchedule`:
1. `startSlot p ≤ res.slotIdx < startSlot p + Fintype.card P`,
2. slot `res.slotIdx` is active and its agreed entry is `(p, ops p)` for every probe,
3. `res.resp` equals the exact sequential transition response of `M.step` after replaying the
   agreed log prefix of length `res.slotIdx`, and
4. the replayed sequential state after `res.slotIdx + 1` slots equals the post-step state
   `(M.step (applyLog M (slotLog slot probe res.slotIdx)) (ops p)).1`. -/
theorem universalInvoke_spec [Fintype P]
    (hsched : ValidSlotSchedule slot ops startSlot) {p : P} {res : UniversalResult Resp}
    (hres : universalInvoke M slot p (ops p) (startSlot p) = some res) (probe : P × Op) :
    startSlot p ≤ res.slotIdx ∧
      res.slotIdx < startSlot p + Fintype.card P ∧
      (slot res.slotIdx).propose probe = (p, ops p) ∧
      res.resp = (M.step (applyLog M (slotLog slot probe res.slotIdx)) (ops p)).2 ∧
      applyLog M (slotLog slot probe (res.slotIdx + 1)) =
        (M.step (applyLog M (slotLog slot probe res.slotIdx)) (ops p)).1 := by
  obtain ⟨hle, hlt, hwin, hprev, hresp⟩ := universalInvokeAux_sound hres
  have hact : SlotActive slot ops startSlot res.slotIdx := by
    refine Or.inr ⟨p, hle, fun j hj => ?_⟩
    by_cases hjs : j < startSlot p
    · exact hsched.ne_winner_before_start p hjs (p, ops p)
    · exact hprev j (by omega) hj
  have hpair_eq : (slot res.slotIdx).propose probe = (p, ops p) := by
    rw [(slot res.slotIdx).propose_eq probe (p, ops p)]
    exact Prod.ext hwin ((hsched.winner_op res.slotIdx hact (p, ops p)).trans (congrArg ops hwin))
  refine ⟨hle, hlt, hpair_eq, ?_, ?_⟩
  · rw [hresp, slotLog_eq slot (p, ops p) probe]
  · rw [applyLog_slotLog_succ, hpair_eq]

/-- **Injectivity of linearization slots:** distinct invocations `p ≠ q` never win the same
consensus log index `slotIdx`. -/
theorem universalInvoke_slotIdx_injective [Fintype P]
    (hsched : ValidSlotSchedule slot ops startSlot) {p q : P}
    {res_p res_q : UniversalResult Resp}
    (hp : universalInvoke M slot p (ops p) (startSlot p) = some res_p)
    (hq : universalInvoke M slot q (ops q) (startSlot q) = some res_q)
    (hidx : res_p.slotIdx = res_q.slotIdx) : p = q := by
  have hp_win := (universalInvoke_spec hsched hp (p, ops p)).2.2.1
  have hq_win := (universalInvoke_spec hsched hq (p, ops p)).2.2.1
  rw [hidx, hq_win] at hp_win
  exact (Prod.mk.inj hp_win).1.symm

/-- Finite-batch linearizability of `universalInvoke` under `ValidSlotSchedule` (unhelped idealized
`ConsensusCell` log-append step after [Herlihy1991], §4.1, pp. 143–146, Figure 14 p. 145 &
Theorem 14 p. 146, without `announce`/helping or §4.2 cell reclamation): for any finite invocation
batch `P`, there is a total assignment `res : P → UniversalResult Resp` of completed invocation
outcomes such that:
1. every invocation `p : P` terminates in `[startSlot p, startSlot p + Fintype.card P)`,
2. winning log indices `(res p).slotIdx` are injective across `P`,
3. real-time precedence is preserved (`(res p).slotIdx < startSlot q → (res p).slotIdx <
   (res q).slotIdx`), and
4. at `(res p).slotIdx`, the agreed log records `(p, ops p)` and `(res p).resp` equals the exact
   sequential transition response of `M` on the replayed prefix. -/
theorem universalInvoke_linearizable_of_validSlotSchedule [Fintype P]
    (M : SeqSpec State Op Resp) (hsched : ValidSlotSchedule slot ops startSlot) :
    ∃ res : P → UniversalResult Resp,
      (∀ p, universalInvoke M slot p (ops p) (startSlot p) = some (res p)) ∧
      Function.Injective (fun p => (res p).slotIdx) ∧
      (∀ p q, (res p).slotIdx < startSlot q → (res p).slotIdx < (res q).slotIdx) ∧
      (∀ p probe,
        startSlot p ≤ (res p).slotIdx ∧
        (res p).slotIdx < startSlot p + Fintype.card P ∧
        (slot (res p).slotIdx).propose probe = (p, ops p) ∧
        (res p).resp = (M.step (applyLog M (slotLog slot probe (res p).slotIdx)) (ops p)).2 ∧
        applyLog M (slotLog slot probe ((res p).slotIdx + 1)) =
          (M.step (applyLog M (slotLog slot probe (res p).slotIdx)) (ops p)).1) := by
  have hterm := fun p => universalInvoke_terminates (M := M) hsched p
  let res : P → UniversalResult Resp := fun p => Classical.choose (hterm p)
  have hres : ∀ p, universalInvoke M slot p (ops p) (startSlot p) = some (res p) :=
    fun p => Classical.choose_spec (hterm p)
  refine ⟨res, hres, fun p q => universalInvoke_slotIdx_injective hsched (hres p) (hres q),
    fun p q hprec => hprec.trans_le (universalInvoke_spec hsched (hres q) (q, ops q)).1,
    fun p => universalInvoke_spec hsched (hres p)⟩

/-- Under `ValidSlotSchedule` with `startSlot = 0`, the winning consensus indices of a finite
invocation batch `P` form a bijection `P ≃ Fin (Fintype.card P)` ordering all `Fintype.card P`
concurrent invocations without gaps. -/
theorem universalInvoke_slotIdx_bijective_of_validSlotSchedule [Fintype P]
    (hsched : ValidSlotSchedule slot ops (fun _ => 0))
    {res : P → UniversalResult Resp}
    (hres : ∀ p, universalInvoke M slot p (ops p) 0 = some (res p)) :
    ∃ order : P ≃ Fin (Fintype.card P),
      ∀ p, (order p).val = (res p).slotIdx := by
  let f : P → Fin (Fintype.card P) := fun p => ⟨(res p).slotIdx, by
    simpa using (universalInvoke_spec hsched (hres p) (p, ops p)).2.1⟩
  have hinj : Function.Injective f := fun p q heq =>
    universalInvoke_slotIdx_injective hsched (hres p) (hres q) (congrArg Fin.val heq)
  have hsurj : Function.Surjective f := by
    by_contra hns
    exact (Fintype.card_lt_of_injective_not_surjective f hinj hns).ne (Fintype.card_fin _).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

end SafetyAndLinearizability

end Cslib.Distributed.SharedMemory
