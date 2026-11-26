/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.Basic
public import CslibFrontier.Computability.Distributed.RingElection.ChangRoberts
public import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# All-Active Basic Two-Hop Unidirectional FIFO Ring Election Steps

Intermediate steps for all-initially-active basic two-hop unidirectional asynchronous FIFO ring
election on `Fin n` (`n ≥ 1`) with injective identifiers `uid : Fin n → U` from a linear order `U`
(steps towards [Peterson][Peterson1982], not the spontaneous-wakeup or `1.44 n log₂ n`
Fibonacci-threshold endpoints of `[Peterson1982]`).

All `n` processors start active (`twoHopAllActiveInit`), hold a current temporary identifier `tid`,
and execute two-hop comparison phases while eliminated processors act as passive FIFO relays
(`.relay`):

1. **First hop (`hop1`):** at the start of a phase, each active processor `p` emits `.hop1 tid_p`,
   which passive relays forward clockwise to the next active processor `q`. If `tid_p = tid_q`,
   `tid_q` wrapped around the entire ring as the sole remaining active processor, so `q` becomes
   `.leader tid_q` without emitting further messages. Otherwise `q` records `ntid := tid_p`
   (`.active2 tid_q tid_p`) and emits `.hop2 tid_p`.
2. **Second hop (`hop2`):** `.hop2 tid_p` is forwarded clockwise to the next active processor `r`,
   which has already received `ntid_r = tid_q` in `.hop1` from `q` and therefore knows all three
   consecutive active temporary identifiers `(tid_p, tid_q, tid_r)`. If `q` is a strict local peak
   (`tid_p < tid_q ∧ tid_r < tid_q`), `r` remains active in the next phase adopting `tid' := tid_q`
   and immediately emits `.hop1 tid_q`; otherwise `r` becomes a passive `.relay`.

The proof combines two clean structural ingredients:

* **Phase combinatorics (`twoHopSurvivors_card_halving`, `twoHopAllActive_phases_le_log`):**
  distinctness of active temporary identifiers and the global maximum `max_j (uid j)` are preserved
  across every phase (`2 ≤ active`), while adjacent active nodes cannot both be strict peaks, giving
  `2 * active_{k + 1} ≤ active_k` and `twoHopAllActivePhases uid ≤ Nat.log 2 n` elimination phases.
  Telescoping the per-phase emissions (`n` initial + `(2n - active_k + active_{k + 1})` per
  elimination phase + `(n - 1)` in the final `active = 1` pass) yields `2 * n * K + n` messages on
  the canonical wave execution.
* **Strong weighted FIFO confluence (`twoHopStep_comm`):** enabled single-message deliveries at
  distinct nodes `i ≠ j` commute in one step (`twoHopStep j (twoHopStep i cfg) =
  twoHopStep i (twoHopStep j cfg)`) with identical additive message emissions, because popping
  the head of a nonempty FIFO list commutes with appending to its tail. A general strip lemma
  transfers termination, the unique quiescent state, and the message bound
  `2 * n * Nat.log 2 n + n` to every asynchronous FIFO execution from `twoHopAllActiveInit uid`.

## Main definitions

* `Cslib.Distributed.RingElection.TwoHopMsg`, `TwoHopNode`, `TwoHopLocalOut`, `twoHopRecv`:
  untagged two-hop message payloads, processor states, and local transition handler.
* `Cslib.Distributed.RingElection.TwoHopConfig`, `twoHopAllActiveInit`, `twoHopStep`, `twoHopExec`,
  `twoHopLTS`, `twoHopAllActiveExecMsgs`: global FIFO configurations, all-active initial state,
  asynchronous transitions, LTS, and cumulative edge-message counter.
* `Cslib.Distributed.RingElection.backLen`, `prevActive`, `nextActive`, `twoHopSurvivors`,
  `TwoHopPhaseState`, `twoHopAllActivePhase`, `twoHopAllActivePhases`: active-subring combinatorics
  and all-active phase evolution.

## Main results

* `Cslib.Distributed.RingElection.twoHopSurvivors_card_halving`,
  `Cslib.Distributed.RingElection.twoHopAllActive_phase_halving`: per-phase halving steps
  `2 * active_{k + 1} ≤ active_k` whenever `2 ≤ active_k`.
* `Cslib.Distributed.RingElection.twoHopAllActive_phases_le_log`: phase-bound step
  `twoHopAllActivePhases uid ≤ Nat.log 2 n` and convergence to a single active processor.
* `Cslib.Distributed.RingElection.twoHopStep_comm`: one-step FIFO confluence step on `Fin n`.
* `Cslib.Distributed.RingElection.twoHopAllActive_elects_leader`: bounded-termination and
  unique-leader step from `twoHopAllActiveInit uid` across all asynchronous FIFO schedules.
* `Cslib.Distributed.RingElection.twoHopAllActive_execMsgs_eq`,
  `Cslib.Distributed.RingElection.twoHopAllActive_messages_le`: complete-run
  `2 * n * twoHopAllActivePhases uid + n` message-count step and `≤ 2 * n * Nat.log 2 n + n`
  bound step from `twoHopAllActiveInit uid`.

## References

* [G. L. Peterson, *An $O(n \log n)$ Unidirectional Algorithm for the Circular Extrema
  Problem*][Peterson1982]
-/

public section

namespace Cslib.Distributed.RingElection

open Cslib

/-! ### Local processor machine and asynchronous FIFO ring LTS -/

/-- Message payload in the basic two-hop unidirectional ring election protocol. -/
inductive TwoHopMsg (U : Type*) where
  /-- First-hop message carrying an active node's current temporary identifier `tid`. -/
  | hop1 (tid : U)
  /-- Second-hop message carrying the predecessor active node's temporary identifier `ntid`. -/
  | hop2 (ntid : U)
  deriving @[expose] DecidableEq

/-- Local state of a processor in the basic two-hop unidirectional ring election protocol. -/
inductive TwoHopNode (U : Type*) where
  /-- Active node at start of phase holding `tid`, awaiting `hop1` from its predecessor. -/
  | active1 (tid : U)
  /-- Active node holding `tid` and predecessor's `ntid`, awaiting `hop2` (`nnid`). -/
  | active2 (tid ntid : U)
  /-- Passive relay node forwarding every incoming message unchanged. -/
  | relay
  /-- Elected leader node holding the global maximum identifier `maxUid`. -/
  | leader (maxUid : U)
  deriving @[expose] DecidableEq

/-- Whether a `TwoHopNode` is in the elected `.leader` state. -/
@[expose] def TwoHopNode.isLeader {U : Type*} : TwoHopNode U → Bool
  | .leader _ => true
  | _ => false

/-- Output of a single message reception in the basic two-hop protocol: updated processor state and
outgoing FIFO messages appended to `i → i + 1`. -/
structure TwoHopLocalOut (U : Type*) where
  /-- Updated local state of the receiving processor. -/
  nextNode : TwoHopNode U
  /-- Outgoing messages appended to the processor's clockwise channel. -/
  sent : List (TwoHopMsg U)
  deriving @[expose] DecidableEq

/-- Deterministic local transition handler for the basic two-hop protocol upon receiving `msg`. -/
@[expose] def twoHopRecv {U : Type*} [LinearOrder U] (st : TwoHopNode U)
    (msg : TwoHopMsg U) : TwoHopLocalOut U :=
  match st, msg with
  | .active1 tid, .hop1 ntid =>
    if ntid = tid then ⟨.leader tid, []⟩
    else ⟨.active2 tid ntid, [.hop2 ntid]⟩
  | .active2 tid ntid, .hop2 nnid =>
    if nnid < ntid ∧ tid < ntid then ⟨.active1 ntid, [.hop1 ntid]⟩
    else ⟨.relay, []⟩
  | .relay, m => ⟨.relay, [m]⟩
  | st, _ => ⟨st, []⟩

/-- Global configuration of the basic two-hop protocol on an asynchronous FIFO unidirectional
`n`-ring. -/
@[ext]
structure TwoHopConfig (n : ℕ) (U : Type*) where
  /-- Local state of each node `i : Fin n`. -/
  node : Fin n → TwoHopNode U
  /-- Clockwise FIFO channel on directed edge `i → i + 1` (head is oldest, tail is newest). -/
  chan : Fin n → List (TwoHopMsg U)

/-- Whether node `i` has declared leadership in configuration `cfg`. -/
@[expose] def TwoHopConfig.isLeader {n : ℕ} {U : Type*} (cfg : TwoHopConfig n U)
    (i : Fin n) : Bool :=
  (cfg.node i).isLeader

/-- All-initially-active start configuration for the basic two-hop protocol (a step model towards
[Peterson][Peterson1982]): every node `i` starts active with `tid = uid i` and injects
`[.hop1 (uid i)]` onto `i → i + 1`. -/
@[expose] def twoHopAllActiveInit {n : ℕ} {U : Type*} (uid : Fin n → U) : TwoHopConfig n U where
  node i := .active1 (uid i)
  chan i := [.hop1 (uid i)]

/-- Deliver the oldest message on `target - 1 → target` to `target` (no-op if empty). -/
@[expose] def twoHopStep {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (target : Fin n) (cfg : TwoHopConfig n U) : TwoHopConfig n U :=
  match cfg.chan (target - 1) with
  | [] => cfg
  | msg :: rest =>
    let out := twoHopRecv (cfg.node target) msg
    let chan₁ := Function.update cfg.chan (target - 1) rest
    TwoHopConfig.mk
      (Function.update cfg.node target out.nextNode)
      (Function.update chan₁ target (chan₁ target ++ out.sent))

/-- Number of messages emitted onto `target → target + 1` by a single `twoHopStep`. -/
@[expose] def twoHopStepMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (target : Fin n) (cfg : TwoHopConfig n U) : ℕ :=
  match cfg.chan (target - 1) with
  | [] => 0
  | msg :: _ => (twoHopRecv (cfg.node target) msg).sent.length

/-- Execute a finite delivery schedule `sched : List (Fin n)` starting from `cfg`. -/
@[expose] def twoHopExec {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (cfg : TwoHopConfig n U) (sched : List (Fin n)) : TwoHopConfig n U :=
  sched.foldl (fun c i => twoHopStep i c) cfg

/-- Cumulative messages emitted onto ring edges during `sched` starting from `cfg`. -/
@[expose] def twoHopEmittedMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (cfg : TwoHopConfig n U) : List (Fin n) → ℕ
  | [] => 0
  | target :: rest =>
    twoHopStepMsgs target cfg + twoHopEmittedMsgs (twoHopStep target cfg) rest

/-- Total messages transmitted across edges in schedule `sched` from `twoHopAllActiveInit uid`: the
`n` initial `.hop1` injections plus all subsequent emissions. -/
@[expose] def twoHopAllActiveExecMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) (sched : List (Fin n)) : ℕ :=
  n + twoHopEmittedMsgs (twoHopAllActiveInit uid) sched

/-- Labelled transition system of enabled FIFO deliveries in the basic two-hop protocol on
`Fin n`. -/
@[expose] def twoHopLTS (n : ℕ) [NeZero n] (U : Type*) [LinearOrder U] :
    LTS (TwoHopConfig n U) (Fin n) where
  Tr cfg target cfg' := cfg.chan (target - 1) ≠ [] ∧ cfg' = twoHopStep target cfg

private theorem twoHopEmittedMsgs_append {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (cfg : TwoHopConfig n U) (s₁ s₂ : List (Fin n)) :
    twoHopEmittedMsgs cfg (s₁ ++ s₂) =
      twoHopEmittedMsgs cfg s₁ + twoHopEmittedMsgs (twoHopExec cfg s₁) s₂ := by
  induction s₁ generalizing cfg with
  | nil => simp only [List.nil_append, twoHopEmittedMsgs, twoHopExec, List.foldl_nil, zero_add]
  | cons a rest ih =>
    simp only [List.cons_append, twoHopEmittedMsgs, twoHopExec, List.foldl_cons, ih, add_assoc]

private theorem twoHopExec_of_mtr {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {c₀ c₁ : TwoHopConfig n U} {tr : List (Fin n)}
    (hmtr : (twoHopLTS n U).MTr c₀ tr c₁) :
    twoHopExec c₀ tr = c₁ := by
  induction hmtr with
  | refl => rfl
  | stepL htr _ ih =>
    rw [twoHopExec, List.foldl_cons, ← htr.2]
    exact ih

/-! ### Strong one-step FIFO confluence and strip lemma -/

private theorem twoHopStep_node_of_cons {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {target : Fin n} {cfg : TwoHopConfig n U} {msg : TwoHopMsg U} {rest : List (TwoHopMsg U)}
    (hq : cfg.chan (target - 1) = msg :: rest) :
    (twoHopStep target cfg).node =
      Function.update cfg.node target (twoHopRecv (cfg.node target) msg).nextNode := by
  simp only [twoHopStep, hq]

private theorem twoHopStep_chan_apply {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {target : Fin n} {cfg : TwoHopConfig n U} {msg : TwoHopMsg U} {rest : List (TwoHopMsg U)}
    (hq : cfg.chan (target - 1) = msg :: rest) (e : Fin n) :
    (twoHopStep target cfg).chan e =
      (if e = target - 1 then rest else cfg.chan e) ++
        (if e = target then (twoHopRecv (cfg.node target) msg).sent else []) := by
  rcases eq_or_ne e target with rfl | het
  · simp only [twoHopStep, hq, Function.update_apply, ↓reduceIte]
  · simp only [twoHopStep, hq, Function.update_apply, het, ↓reduceIte, List.append_nil]

private theorem twoHopStep_two_of_ne {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {cfg : TwoHopConfig n U} {i j : Fin n} (hne : i ≠ j)
    (hi : cfg.chan (i - 1) ≠ []) (hj : cfg.chan (j - 1) ≠ []) :
    (twoHopStep i cfg).chan (j - 1) =
      (cfg.chan (j - 1)).head hj ::
        (if j - 1 = i then
          (cfg.chan (j - 1)).tail ++ (twoHopRecv (cfg.node i) ((cfg.chan (i - 1)).head hi)).sent
        else (cfg.chan (j - 1)).tail) ∧
    (twoHopStep i cfg).node j = cfg.node j ∧
    ∀ e : Fin n, (twoHopStep j (twoHopStep i cfg)).chan e =
      (if e = i - 1 then (cfg.chan (i - 1)).tail
      else if e = j - 1 then (cfg.chan (j - 1)).tail
      else cfg.chan e) ++
      (if e = i then (twoHopRecv (cfg.node i) ((cfg.chan (i - 1)).head hi)).sent else []) ++
      (if e = j then (twoHopRecv (cfg.node j) ((cfg.chan (j - 1)).head hj)).sent else []) := by
  have hpred_ne : j - 1 ≠ i - 1 := fun h => hne.symm (sub_left_injective h)
  have hqi : cfg.chan (i - 1) = (cfg.chan (i - 1)).head hi :: (cfg.chan (i - 1)).tail :=
    (List.cons_head_tail hi).symm
  have hqj : cfg.chan (j - 1) = (cfg.chan (j - 1)).head hj :: (cfg.chan (j - 1)).tail :=
    (List.cons_head_tail hj).symm
  have hstep_i_at_jpred :
      (twoHopStep i cfg).chan (j - 1) =
        (cfg.chan (j - 1)).head hj ::
          (if j - 1 = i then
            (cfg.chan (j - 1)).tail ++ (twoHopRecv (cfg.node i) ((cfg.chan (i - 1)).head hi)).sent
          else (cfg.chan (j - 1)).tail) := by
    rw [twoHopStep_chan_apply hqi, ite_eq_right hpred_ne]
    conv_lhs => rw [hqj]
    by_cases hji : j - 1 = i <;> simp only [hji, ↓reduceIte, List.cons_append, List.append_nil]
  have hnode_i_at_j : (twoHopStep i cfg).node j = cfg.node j := by
    rw [twoHopStep_node_of_cons hqi]
    exact Function.update_of_ne (Ne.symm hne) _ _
  refine ⟨hstep_i_at_jpred, hnode_i_at_j, fun e => ?_⟩
  rw [twoHopStep_chan_apply hstep_i_at_jpred e, hnode_i_at_j]
  by_cases hej : e = j - 1
  · subst hej
    simp only [↓reduceIte, hpred_ne]
    by_cases hji : j - 1 = i <;> simp only [hji, ↓reduceIte, List.append_nil]
  · rw [ite_eq_right hej, twoHopStep_chan_apply hqi e]
    by_cases hei : e = i - 1 <;> simp only [hei, hej, ↓reduceIte]

/-- A one-step FIFO confluence step for the basic two-hop unidirectional ring protocol (a step
towards [Peterson][Peterson1982], not the cited endpoint): whenever two distinct processors `i ≠ j`
both have nonempty incoming channels in `cfg`, each remains enabled after the other steps, the two
delivery orders reach the same global configuration, and their emitted message counts commute. -/
theorem twoHopStep_comm {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {cfg : TwoHopConfig n U} {i j : Fin n} (hne : i ≠ j)
    (hi : cfg.chan (i - 1) ≠ []) (hj : cfg.chan (j - 1) ≠ []) :
    (twoHopStep i cfg).chan (j - 1) ≠ [] ∧
    (twoHopStep j cfg).chan (i - 1) ≠ [] ∧
    twoHopStep j (twoHopStep i cfg) = twoHopStep i (twoHopStep j cfg) ∧
    twoHopStepMsgs i cfg + twoHopStepMsgs j (twoHopStep i cfg) =
      twoHopStepMsgs j cfg + twoHopStepMsgs i (twoHopStep j cfg) := by
  obtain ⟨hstep_i_at_jpred, hnode_i_at_j, hlhs⟩ := twoHopStep_two_of_ne hne hi hj
  obtain ⟨hstep_j_at_ipred, hnode_j_at_i, hrhs⟩ := twoHopStep_two_of_ne hne.symm hj hi
  have hqi : cfg.chan (i - 1) = (cfg.chan (i - 1)).head hi :: (cfg.chan (i - 1)).tail :=
    (List.cons_head_tail hi).symm
  have hqj : cfg.chan (j - 1) = (cfg.chan (j - 1)).head hj :: (cfg.chan (j - 1)).tail :=
    (List.cons_head_tail hj).symm
  refine ⟨by rw [hstep_i_at_jpred]; exact List.cons_ne_nil _ _,
    by rw [hstep_j_at_ipred]; exact List.cons_ne_nil _ _, ?_, ?_⟩
  · refine TwoHopConfig.ext (funext fun x => ?_) (funext fun e => ?_)
    · rw [twoHopStep_node_of_cons hstep_i_at_jpred, hnode_i_at_j,
        twoHopStep_node_of_cons hstep_j_at_ipred, hnode_j_at_i,
        twoHopStep_node_of_cons hqi, twoHopStep_node_of_cons hqj]
      by_cases hxj : x = j
      · subst hxj
        simp [hne.symm]
      · by_cases hxi : x = i <;> simp [hxj, hxi, hne]
    · rw [hlhs e, hrhs e]
      have hpred_ne : i - 1 ≠ j - 1 := fun h => hne (sub_left_injective h)
      have hbase_eq :
          (if e = i - 1 then (cfg.chan (i - 1)).tail
            else if e = j - 1 then (cfg.chan (j - 1)).tail else cfg.chan e) =
          (if e = j - 1 then (cfg.chan (j - 1)).tail
            else if e = i - 1 then (cfg.chan (i - 1)).tail else cfg.chan e) := by
        by_cases he : e = i - 1 <;> simp only [he, hpred_ne, ↓reduceIte]
      rw [hbase_eq]
      by_cases hei : e = i <;> simp only [hei, hne, ↓reduceIte, List.append_nil]
  · have hmsgs_cons {c : TwoHopConfig n U} {t : Fin n} {m : TwoHopMsg U} {r : List (TwoHopMsg U)}
        (hq : c.chan (t - 1) = m :: r) :
        twoHopStepMsgs t c = (twoHopRecv (c.node t) m).sent.length := by
      simp only [twoHopStepMsgs, hq]
    rw [hmsgs_cons hqi, hmsgs_cons hstep_i_at_jpred, hnode_i_at_j,
      hmsgs_cons hqj, hmsgs_cons hstep_j_at_ipred, hnode_j_at_i, Nat.add_comm]

/-- **Strip lemma (`strip_one_step`).**
Given a terminating trace `MTr cfg tr cfg_term` (`IsTerminal cfg_term`) and any single enabled step
`Tr cfg b cfg'`, pushing `b` across `tr` yields a strictly shorter trace `tr'` from `cfg'` to the
*same* terminal configuration `cfg_term` with the *same* total emitted messages! -/
private theorem strip_one_step {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {cfg cfg' cfg_term : TwoHopConfig n U} {tr : List (Fin n)} {b : Fin n}
    (hmtr : (twoHopLTS n U).MTr cfg tr cfg_term)
    (hterm : (twoHopLTS n U).IsTerminal cfg_term)
    (hstep : (twoHopLTS n U).Tr cfg b cfg') :
    ∃ tr' : List (Fin n),
      (twoHopLTS n U).MTr cfg' tr' cfg_term ∧
      tr'.length + 1 = tr.length ∧
      twoHopStepMsgs b cfg + twoHopEmittedMsgs cfg' tr' = twoHopEmittedMsgs cfg tr := by
  induction tr generalizing cfg cfg' b with
  | nil =>
    cases hmtr
    exact absurd hstep (hterm b cfg')
  | cons a rest ih =>
    rcases LTS.MTr.cons_iff.mp hmtr with ⟨cfg₁, htr_a, hrest⟩
    by_cases hba : b = a
    · subst hba
      obtain ⟨_, rfl⟩ := hstep
      obtain ⟨_, rfl⟩ := htr_a
      exact ⟨rest, hrest, rfl, rfl⟩
    · obtain ⟨ha_en, rfl⟩ := htr_a
      obtain ⟨hb_en, rfl⟩ := hstep
      obtain ⟨hb_after_a, ha_after_b, hcomm, hw_comm⟩ :=
        twoHopStep_comm (Ne.symm hba) ha_en hb_en
      obtain ⟨rest', hmtr_rest', hlen_rest', hw_rest'⟩ := ih hrest ⟨hb_after_a, rfl⟩
      refine ⟨a :: rest', LTS.MTr.stepL ⟨ha_after_b, hcomm⟩ hmtr_rest', by simp [hlen_rest'], ?_⟩
      simp only [twoHopEmittedMsgs, ← hcomm]
      linarith

/-- **Global confluence from a canonical terminating run (`confluence_of_canonical_terminal`).**
If `syncSched` reaches a terminal configuration `cfg_term` from `cfg₀`, then *every* finite trace
`sched` from `cfg₀` can be completed to `cfg_term` with exact conservation of step length and
emitted messages! -/
private theorem confluence_of_canonical_terminal {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {cfg₀ cfg_term cfg : TwoHopConfig n U} {syncSched sched : List (Fin n)}
    (hsync : (twoHopLTS n U).MTr cfg₀ syncSched cfg_term)
    (hterm : (twoHopLTS n U).IsTerminal cfg_term)
    (hmtr : (twoHopLTS n U).MTr cfg₀ sched cfg) :
    ∃ rem : List (Fin n),
      (twoHopLTS n U).MTr cfg rem cfg_term ∧
      sched.length + rem.length = syncSched.length ∧
      twoHopEmittedMsgs cfg₀ sched + twoHopEmittedMsgs cfg rem =
        twoHopEmittedMsgs cfg₀ syncSched := by
  induction hmtr generalizing syncSched with
  | refl =>
    exact ⟨syncSched, hsync, by simp, by simp [twoHopEmittedMsgs]⟩
  | @stepL s1 b s2 tail s3 htr _ ih =>
    obtain ⟨sync', hsync', hlen', hw'⟩ := strip_one_step hsync hterm htr
    obtain ⟨rem, hrem, hlen_rem, hw_rem⟩ := ih hsync'
    obtain ⟨_, rfl⟩ := htr
    refine ⟨rem, hrem, by simp only [List.length_cons]; omega, ?_⟩
    simp only [twoHopEmittedMsgs]
    linarith

/-! ### Active sub-ring geometry and per-phase halving -/

/-- Counter-clockwise hop distance `d ∈ {1, …, n}` from `q` to the previous element of `A`,
computed via `arcLen` on the negated set `A.image (fun x => -x)`. -/
@[expose] def backLen {n : ℕ} [NeZero n] (A : Finset (Fin n)) (q : Fin n) : ℕ :=
  arcLen (A.image fun x => -x) (-q)

/-- Immediate counter-clockwise active predecessor of `q` in `A`. -/
@[expose] def prevActive {n : ℕ} [NeZero n] (A : Finset (Fin n)) (q : Fin n) : Fin n :=
  q - Fin.ofNat n (backLen A q)

/-- Immediate clockwise active successor of `p` in `A`. -/
@[expose] def nextActive {n : ℕ} [NeZero n] (A : Finset (Fin n)) (p : Fin n) : Fin n :=
  p + Fin.ofNat n (arcLen A p)

private theorem mem_neg_image_iff {n : ℕ} (A : Finset (Fin n)) (x : Fin n) :
    -x ∈ A.image (fun y : Fin n => -y) ↔ x ∈ A := by
  simp only [Finset.mem_image]
  exact ⟨fun ⟨y, hy, hneg⟩ => neg_injective hneg ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

private theorem backLen_bounds_and_mem {n : ℕ} [NeZero n] {A : Finset (Fin n)} {q : Fin n}
    (hq : q ∈ A) :
    1 ≤ backLen A q ∧ backLen A q ≤ n ∧ prevActive A q ∈ A ∧
      ∀ k, 1 ≤ k → k < backLen A q → q - Fin.ofNat n k ∉ A := by
  have hnq : -q ∈ A.image (fun y : Fin n => -y) := (mem_neg_image_iff A q).mpr hq
  obtain ⟨h1, hn, hmem, hmin⟩ := arcLen_bounds_and_mem hnq
  have hneg_sub : ∀ d, -q + Fin.ofNat n d = -(q - Fin.ofNat n d) := fun d => by
    rw [neg_sub, sub_eq_add_neg, add_comm]
  rw [hneg_sub, mem_neg_image_iff] at hmem
  exact ⟨h1, hn, hmem, fun k hk1 hk2 => by
    simpa only [hneg_sub, mem_neg_image_iff] using hmin k hk1 hk2⟩

private theorem nextActive_mem {n : ℕ} [NeZero n] {A : Finset (Fin n)} {p : Fin n} (hp : p ∈ A) :
    nextActive A p ∈ A :=
  (arcLen_bounds_and_mem hp).2.2.1

private theorem prevActive_mem {n : ℕ} [NeZero n] {A : Finset (Fin n)} {q : Fin n} (hq : q ∈ A) :
    prevActive A q ∈ A :=
  (backLen_bounds_and_mem hq).2.2.1

private theorem ofNat_sub_add_of_le {n d k : ℕ} [NeZero n] (hk : k ≤ d) :
    Fin.ofNat n d = Fin.ofNat n (d - k) + Fin.ofNat n k := by
  ext
  change d % n = ((d - k) % n + k % n) % n
  rw [← Nat.add_mod, Nat.sub_add_cancel hk]

private theorem ofNat_succ_eq {n : ℕ} [NeZero n] (k : ℕ) :
    Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 :=
  Fin.ext (Nat.add_mod k 1 n)

private theorem backLen_nextActive_eq {n : ℕ} [NeZero n] {A : Finset (Fin n)} {p : Fin n}
    (hp : p ∈ A) :
    backLen A (nextActive A p) = arcLen A p := by
  obtain ⟨hd1, _, hqA, hmin⟩ := arcLen_bounds_and_mem hp
  let q := nextActive A p
  have hnq : -q ∈ A.image (fun y : Fin n => -y) := (mem_neg_image_iff A q).mpr hqA
  refine arcLen_eq_of_isFirst hnq hd1 ?_ fun k hk1 hk2 => ?_
  · have heq : -q + Fin.ofNat n (arcLen A p) = -p := by
      dsimp only [q, nextActive]
      abel
    rw [heq, mem_neg_image_iff]
    exact hp
  · have heq : -q + Fin.ofNat n k = -(p + Fin.ofNat n (arcLen A p - k)) := by
      dsimp only [q, nextActive]
      rw [ofNat_sub_add_of_le (le_of_lt hk2)]
      abel
    rw [heq, mem_neg_image_iff]
    exact hmin (arcLen A p - k) (by omega) (by omega)

private theorem prevActive_nextActive {n : ℕ} [NeZero n] {A : Finset (Fin n)} {p : Fin n}
    (hp : p ∈ A) :
    prevActive A (nextActive A p) = p := by
  rw [prevActive, backLen_nextActive_eq hp, nextActive, add_sub_cancel_right]

private theorem arcLen_prevActive_eq {n : ℕ} [NeZero n] {A : Finset (Fin n)} {q : Fin n}
    (hq : q ∈ A) :
    arcLen A (prevActive A q) = backLen A q := by
  obtain ⟨hd1, _, hpA, hmin⟩ := backLen_bounds_and_mem hq
  refine arcLen_eq_of_isFirst hpA hd1 ?_ fun k hk1 hk2 => ?_
  · rw [prevActive, sub_add_cancel]
    exact hq
  · have heq : prevActive A q + Fin.ofNat n k = q - Fin.ofNat n (backLen A q - k) := by
      rw [prevActive, ofNat_sub_add_of_le (le_of_lt hk2), sub_add_eq_sub_sub, sub_add_cancel]
    rw [heq]
    exact hmin (backLen A q - k) (by omega) (by omega)

private theorem nextActive_prevActive {n : ℕ} [NeZero n] {A : Finset (Fin n)} {q : Fin n}
    (hq : q ∈ A) :
    nextActive A (prevActive A q) = q := by
  rw [nextActive, arcLen_prevActive_eq hq, prevActive, sub_add_cancel]

private theorem prevActive_ne_self_of_two_le_card {n : ℕ} [NeZero n] {A : Finset (Fin n)}
    (hcard : 2 ≤ A.card) {q : Fin n} (hq : q ∈ A) :
    prevActive A q ≠ q := by
  intro heq
  have hnext : nextActive A q = q :=
    (congrArg (nextActive A) heq.symm).trans (nextActive_prevActive hq)
  obtain ⟨_, hdn, _, hmin⟩ := arcLen_bounds_and_mem hq
  have hd_eq_n : arcLen A q = n := by
    have hmod : arcLen A q % n = 0 :=
      congrArg Fin.val (add_left_cancel (hnext.trans (add_zero q).symm))
    refine le_antisymm hdn (by_contra fun hlt => ?_)
    rw [Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  obtain ⟨x, hxA, hxq⟩ := Finset.exists_mem_ne (by omega : 1 < A.card) q
  let k := (x - q).val
  have hval : Fin.ofNat n k = x - q := Fin.ext (Nat.mod_eq_of_lt (x - q).isLt)
  have hkx : q + Fin.ofNat n k = x := hval ▸ add_sub_cancel q x
  have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h0 => hxq (by simpa [h0] using hkx.symm)
  exact hmin k hk_pos (hd_eq_n.symm ▸ (x - q).isLt) (hkx ▸ hxA)

/-- Surviving active nodes after a two-hop comparison phase on active set `A` with temporary
identifier assignment `tidMap`: nodes `r ∈ A` whose predecessor `q = prevActive A r` is a strict
local peak (`tidMap (prevActive A q) < tidMap q ∧ tidMap r < tidMap q`). -/
@[expose] def twoHopSurvivors {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (A : Finset (Fin n)) (tidMap : Fin n → U) : Finset (Fin n) :=
  A.filter fun r =>
    tidMap (prevActive A (prevActive A r)) < tidMap (prevActive A r) ∧
      tidMap r < tidMap (prevActive A r)

/-- A combinatorial active-subring halving step for two-hop peak comparison (a step towards
[Peterson][Peterson1982], not the cited endpoint): adjacent active nodes cannot both be strict
peaks, so `r` and `prevActive A r` for `r ∈ twoHopSurvivors A tidMap` form disjoint subsets of `A`,
giving `2 * (twoHopSurvivors A tidMap).card ≤ A.card`. -/
theorem twoHopSurvivors_card_halving {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (A : Finset (Fin n)) (tidMap : Fin n → U) :
    2 * (twoHopSurvivors A tidMap).card ≤ A.card := by
  let S := twoHopSurvivors A tidMap
  let P := S.image (prevActive A)
  have hSP_sub : S ∪ P ⊆ A := Finset.union_subset (Finset.filter_subset _ _)
    (Finset.image_subset_iff.mpr fun r hr => prevActive_mem (Finset.mem_filter.mp hr).1)
  have hSP_disj : Disjoint S P := by
    refine Finset.disjoint_left.mpr fun r₁ hr₁ hr₂ => ?_
    rcases Finset.mem_image.mp hr₂ with ⟨r₂, hr₂S, hprev_eq⟩
    have h1 := (Finset.mem_filter.mp hr₁).2
    have h2 := (Finset.mem_filter.mp hr₂S).2
    -- `hprev_eq : prevActive A r₂ = r₁`, so `h2.1` says `tidMap (prevActive A r₁) < tidMap r₁`,
    -- contradicting `h1.2 : tidMap r₁ < tidMap (prevActive A r₁)`!
    rw [hprev_eq] at h2
    exact lt_asymm h1.2 h2.1
  have hP_card : P.card = S.card := Finset.card_image_of_injOn fun r₁ hr₁ r₂ hr₂ heq => by
    simpa [nextActive_prevActive (Finset.mem_filter.mp hr₁).1,
      nextActive_prevActive (Finset.mem_filter.mp hr₂).1] using congrArg (nextActive A) heq
  have hle := Finset.card_le_card hSP_sub
  rw [Finset.card_union_of_disjoint hSP_disj, hP_card] at hle
  dsimp only [S] at hle
  omega

/-- Global maximum preservation and nonemptiness of `twoHopSurvivors A tidMap`: when `2 ≤ A.card`
and `tidMap` is injective on `A`, the node `r* = nextActive A q*` immediately clockwise of the
unique `tidMap`-maximizer `q* ∈ A` survives with new temporary identifier `tidMap q*`, and the
updated temporary identifiers remain injective on `twoHopSurvivors A tidMap`. -/
private theorem twoHopSurvivors_nonempty_and_max {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {A : Finset (Fin n)} (hcard : 2 ≤ A.card) {tidMap : Fin n → U}
    (hinj : Set.InjOn tidMap A) :
    let S := twoHopSurvivors A tidMap
    let tidMap' := fun r => tidMap (prevActive A r)
    S.Nonempty ∧
      Set.InjOn tidMap' S ∧
      ∀ M : U, (∃ q ∈ A, tidMap q = M ∧ ∀ x ∈ A, tidMap x ≤ M) →
        ∃ r ∈ S, tidMap' r = M ∧ ∀ x ∈ S, tidMap' x ≤ M := by
  intro S tidMap'
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hne_img : (A.image tidMap).Nonempty := hne.image tidMap
  rcases Finset.mem_image.mp (Finset.max'_mem (A.image tidMap) hne_img) with ⟨qStar, hqA, hqMax⟩
  have hmax_all : ∀ x ∈ A, tidMap x ≤ tidMap qStar := fun x hx => by
    rw [hqMax]
    exact Finset.le_max' _ (tidMap x) (Finset.mem_image_of_mem tidMap hx)
  -- Show `rStar := nextActive A qStar ∈ S`!
  let rStar := nextActive A qStar
  have hrA : rStar ∈ A := nextActive_mem hqA
  have hprev_r : prevActive A rStar = qStar := prevActive_nextActive hqA
  have hp_ne_q : prevActive A qStar ≠ qStar := prevActive_ne_self_of_two_le_card hcard hqA
  have hr_ne_q : rStar ≠ qStar := fun h => by
    have hp := congrArg (prevActive A) h
    rw [hprev_r] at hp
    exact hp_ne_q hp.symm
  have hp_lt : tidMap (prevActive A qStar) < tidMap qStar :=
    lt_of_le_of_ne (hmax_all _ (prevActive_mem hqA)) fun heq =>
      hp_ne_q (hinj (prevActive_mem hqA) hqA heq)
  have hr_lt : tidMap rStar < tidMap qStar :=
    lt_of_le_of_ne (hmax_all _ hrA) fun heq => hr_ne_q (hinj hrA hqA heq)
  have hrS : rStar ∈ S := Finset.mem_filter.mpr ⟨hrA, by rw [hprev_r]; exact ⟨hp_lt, hr_lt⟩⟩
  refine ⟨⟨rStar, hrS⟩, ?_, ?_⟩
  · intro r₁ hr₁ r₂ hr₂ heq
    have h1A : r₁ ∈ A := (Finset.mem_filter.mp hr₁).1
    have h2A : r₂ ∈ A := (Finset.mem_filter.mp hr₂).1
    have hp_eq := hinj (prevActive_mem h1A) (prevActive_mem h2A) heq
    have hn_eq := congrArg (nextActive A) hp_eq
    rwa [nextActive_prevActive h1A, nextActive_prevActive h2A] at hn_eq
  · rintro M ⟨q, hq_in, rfl, hq_le⟩
    have hq_eq : q = qStar :=
      hinj hq_in hqA (le_antisymm (hmax_all q hq_in) (hq_le qStar hqA))
    subst hq_eq
    refine ⟨rStar, hrS, by dsimp only [tidMap']; rw [hprev_r], fun x hxS => ?_⟩
    exact hmax_all (prevActive A x) (prevActive_mem (Finset.mem_filter.mp hxS).1)

/-- Combinatorial state of active nodes and their temporary identifiers at phase `k`. -/
structure TwoHopPhaseState (n : ℕ) (U : Type*) where
  /-- Active node set `A_k` at phase `k`. -/
  active : Finset (Fin n)
  /-- Temporary identifier assignment on `Fin n` (meaningful on `active`). -/
  tidMap : Fin n → U

/-- Phase-by-phase combinatorial evolution of the all-initially-active basic two-hop protocol
(stabilizing once `active.card ≤ 1`). -/
@[expose] def twoHopAllActivePhase {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) : ℕ → TwoHopPhaseState n U
  | 0 => ⟨Finset.univ, uid⟩
  | k + 1 =>
    let st := twoHopAllActivePhase uid k
    if 2 ≤ st.active.card then
      ⟨twoHopSurvivors st.active st.tidMap, fun r => st.tidMap (prevActive st.active r)⟩
    else st

/-- Total number of elimination phases (`2 ≤ active.card`) executed by the all-initially-active
basic two-hop protocol on `uid` before `active.card = 1`. -/
@[expose] def twoHopAllActivePhases {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) : ℕ :=
  (List.range n).countP fun k => decide (2 ≤ (twoHopAllActivePhase uid k).active.card)

/-- A per-phase active-count halving step for all-initially-active basic two-hop ring election (a
step towards [Peterson][Peterson1982], not the cited endpoint): whenever
`2 ≤ (twoHopAllActivePhase uid k).active.card`, the next phase has at most half as many active
nodes. -/
theorem twoHopAllActive_phase_halving {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) (k : ℕ) (h2 : 2 ≤ (twoHopAllActivePhase uid k).active.card) :
    2 * (twoHopAllActivePhase uid (k + 1)).active.card ≤
      (twoHopAllActivePhase uid k).active.card := by
  simp only [twoHopAllActivePhase, h2, ↓reduceIte]
  exact twoHopSurvivors_card_halving (twoHopAllActivePhase uid k).active
    (twoHopAllActivePhase uid k).tidMap

private theorem twoHopAllActivePhase_inv {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    let hne_univ : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, Finset.mem_univ _⟩
    let maxUid := (Finset.univ.image uid).max' (hne_univ.image uid)
    ∀ k : ℕ,
      let st := twoHopAllActivePhase uid k
      st.active.Nonempty ∧
      Set.InjOn st.tidMap st.active ∧
      (∃ q ∈ st.active, st.tidMap q = maxUid ∧ ∀ x ∈ st.active, st.tidMap x ≤ maxUid) := by
  intro hne_univ maxUid k
  induction k with
  | zero =>
    dsimp only [twoHopAllActivePhase]
    rcases Finset.mem_image.mp (Finset.max'_mem (Finset.univ.image uid) (hne_univ.image uid)) with
      ⟨iStar, _, hiStar⟩
    exact ⟨hne_univ, huid.injOn, ⟨iStar, Finset.mem_univ iStar, hiStar, fun x _ =>
      Finset.le_max' _ (uid x) (Finset.mem_image_of_mem uid (Finset.mem_univ x))⟩⟩
  | succ k ih =>
    obtain ⟨hne_k, hinj_k, hmax_k⟩ := ih
    dsimp only [twoHopAllActivePhase]
    by_cases h2 : 2 ≤ (twoHopAllActivePhase uid k).active.card
    · simp only [h2, ↓reduceIte]
      obtain ⟨hne', hinj', hmax'⟩ := twoHopSurvivors_nonempty_and_max h2 hinj_k
      exact ⟨hne', hinj', hmax' maxUid hmax_k⟩
    · simp only [h2, ↓reduceIte]
      exact ⟨hne_k, hinj_k, hmax_k⟩

/-- Exponential halving invariant: if phases `0, …, k - 1` all have `2 ≤ active.card`, then
`2 ^ k * (twoHopAllActivePhase uid k).active.card ≤ n`. -/
private theorem pow_two_mul_phase_card_le {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) :
    ∀ k : ℕ, (∀ j < k, 2 ≤ (twoHopAllActivePhase uid j).active.card) →
      2 ^ k * (twoHopAllActivePhase uid k).active.card ≤ n := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [pow_zero, one_mul, twoHopAllActivePhase, Finset.card_univ, Fintype.card_fin, le_rfl]
  | succ k ih =>
    intro hall
    have hk2 : 2 ≤ (twoHopAllActivePhase uid k).active.card := hall k (Nat.lt_succ_self k)
    have hhalve := twoHopAllActive_phase_halving uid k hk2
    have hprev := ih fun j hj => hall j (Nat.lt_succ_of_lt hj)
    calc 2 ^ (k + 1) * (twoHopAllActivePhase uid (k + 1)).active.card
        = 2 ^ k * (2 * (twoHopAllActivePhase uid (k + 1)).active.card) := by ring
      _ ≤ 2 ^ k * (twoHopAllActivePhase uid k).active.card := Nat.mul_le_mul_left (2 ^ k) hhalve
      _ ≤ n := hprev

private theorem phase_stable_of_lt_two {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) {k₀ : ℕ} (h1 : ¬ 2 ≤ (twoHopAllActivePhase uid k₀).active.card) :
    ∀ m, k₀ ≤ m → twoHopAllActivePhase uid m = twoHopAllActivePhase uid k₀ := by
  suffices ∀ d, twoHopAllActivePhase uid (k₀ + d) = twoHopAllActivePhase uid k₀ by
    intro m hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact this d
  intro d
  induction d with
  | zero => simp only [add_zero]
  | succ d ih =>
    rw [← add_assoc, twoHopAllActivePhase, ih]
    simp only [h1, ↓reduceIte]

private theorem twoHopAllActivePhases_prefix_spec {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) (m : ℕ) :
    let cnt := (List.range m).countP fun k => decide (2 ≤ (twoHopAllActivePhase uid k).active.card)
    cnt ≤ m ∧
      (∀ j < cnt, 2 ≤ (twoHopAllActivePhase uid j).active.card) ∧
      (cnt < m → ¬ 2 ≤ (twoHopAllActivePhase uid cnt).active.card) := by
  induction m with
  | zero =>
    dsimp only
    simp only [List.range_zero, List.countP_nil]
    exact ⟨le_rfl, fun _ hj => by omega, fun h => by omega⟩
  | succ m ih =>
    dsimp only at ih ⊢
    obtain ⟨hKm, hall, hstop⟩ := ih
    rw [List.range_succ, List.countP_append, List.countP_singleton]
    simp only [decide_eq_true_eq]
    by_cases hm2 : 2 ≤ (twoHopAllActivePhase uid m).active.card
    · have hK_eq_m :
          ((List.range m).countP fun k =>
            decide (2 ≤ (twoHopAllActivePhase uid k).active.card)) = m := by
        by_contra hne
        have hnot := hstop (lt_of_le_of_ne hKm hne)
        have hst := phase_stable_of_lt_two uid hnot m (by omega)
        rw [← hst] at hnot
        exact hnot hm2
      simp only [hm2, ↓reduceIte]
      rw [hK_eq_m]
      refine ⟨le_rfl, fun j hj => ?_, fun h => by omega⟩
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hlt
      · exact hm2
      · exact hall j (hK_eq_m.symm ▸ hlt)
    · simp only [hm2, ↓reduceIte, add_zero]
      refine ⟨by omega, hall, fun _ => ?_⟩
      rcases eq_or_lt_of_le hKm with heq | hlt
      · rwa [heq]
      · exact hstop hlt

/-- A logarithmic phase-bound step for all-initially-active basic two-hop ring election (a step
towards [Peterson][Peterson1982], not the cited endpoint): for any injective `uid : Fin n → U`, the
number of elimination phases satisfies `twoHopAllActivePhases uid ≤ Nat.log 2 n`, and at phase
`K = twoHopAllActivePhases uid` (as well as at `Nat.log 2 n`), exactly `1` active processor
remains. -/
theorem twoHopAllActive_phases_le_log {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    twoHopAllActivePhases uid ≤ Nat.log 2 n ∧
      (twoHopAllActivePhase uid (twoHopAllActivePhases uid)).active.card = 1 ∧
      (twoHopAllActivePhase uid (Nat.log 2 n)).active.card = 1 := by
  have hstop_log : ¬ 2 ≤ (twoHopAllActivePhase uid (Nat.log 2 n)).active.card := by
    intro h2_log
    have hall : ∀ j < Nat.log 2 n + 1, 2 ≤ (twoHopAllActivePhase uid j).active.card :=
      fun j hj => by_contra fun hnot2 =>
        hnot2 (phase_stable_of_lt_two uid hnot2 (Nat.log 2 n) (by omega) ▸ h2_log)
    have hpow := pow_two_mul_phase_card_le uid (Nat.log 2 n + 1) hall
    have hcard_pos : 1 ≤ (twoHopAllActivePhase uid (Nat.log 2 n + 1)).active.card :=
      Finset.card_pos.mpr (twoHopAllActivePhase_inv huid (Nat.log 2 n + 1)).1
    have h2pow : 2 ^ (Nat.log 2 n + 1) ≤ n := by
      calc 2 ^ (Nat.log 2 n + 1)
          ≤ 2 ^ (Nat.log 2 n + 1) * (twoHopAllActivePhase uid (Nat.log 2 n + 1)).active.card :=
            Nat.le_mul_of_pos_right _ hcard_pos
        _ ≤ n := hpow
    have hle := Nat.le_log_of_pow_le (by omega) h2pow
    omega
  have hlog_lt_n : Nat.log 2 n < n :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_log_le_self 2 (NeZero.ne n))
  obtain ⟨_, hallK, hstopK⟩ := twoHopAllActivePhases_prefix_spec uid n
  have hK_le_log : twoHopAllActivePhases uid ≤ Nat.log 2 n :=
    not_lt.mp fun hgt => hstop_log (hallK (Nat.log 2 n) hgt)
  have hnot2_K : ¬ 2 ≤ (twoHopAllActivePhase uid (twoHopAllActivePhases uid)).active.card :=
    hstopK (lt_of_le_of_lt hK_le_log hlog_lt_n)
  have hcard_K : (twoHopAllActivePhase uid (twoHopAllActivePhases uid)).active.card = 1 := by
    have hpos : 1 ≤ (twoHopAllActivePhase uid (twoHopAllActivePhases uid)).active.card :=
      Finset.card_pos.mpr (twoHopAllActivePhase_inv huid (twoHopAllActivePhases uid)).1
    omega
  exact ⟨hK_le_log, hcard_K,
    (congrArg TwoHopPhaseState.active (phase_stable_of_lt_two uid hnot2_K _ hK_le_log) ▸ hcard_K)⟩

/-! ### Canonical wave execution across passive relays and active nodes -/

/-- Points `p + Fin.ofNat n k` on half-open clockwise arcs `0 ≤ k < arcLen A p` (`p ∈ A`) are
pairwise distinct across `A`. -/
private theorem arc_point_inj {n : ℕ} [NeZero n] {A : Finset (Fin n)}
    {p₁ p₂ : Fin n} (hp₁ : p₁ ∈ A) (hp₂ : p₂ ∈ A)
    {k₁ k₂ : ℕ} (hk₁ : k₁ < arcLen A p₁) (hk₂ : k₂ < arcLen A p₂)
    (heq : p₁ + Fin.ofNat n k₁ = p₂ + Fin.ofNat n k₂) :
    p₁ = p₂ ∧ k₁ = k₂ := by
  -- A point strictly before the end of `p₂`'s arc is not hit by an earlier offset from `p₁ ∈ A`.
  have key : ∀ {p₁ p₂ : Fin n} {k₁ k₂ : ℕ}, p₁ ∈ A → p₂ ∈ A → k₂ < arcLen A p₂ → k₁ < k₂ →
      p₁ + Fin.ofNat n k₁ ≠ p₂ + Fin.ofNat n k₂ := by
    intro p₁ p₂ k₁ k₂ hp₁ hp₂ hk₂ hlt heq
    rw [ofNat_sub_add_of_le hlt.le, ← add_assoc] at heq
    exact (arcLen_bounds_and_mem hp₂).2.2.2 (k₂ - k₁) (by omega) (by omega)
      (add_right_cancel heq ▸ hp₁)
  rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
  · exact (key hp₁ hp₂ hk₂ hlt heq).elim
  · exact ⟨add_right_cancel heq, rfl⟩
  · exact (key hp₂ hp₁ hk₁ hgt heq.symm).elim

/-- Delivering the lone message `m` on `t - 1 → t` to a relay `t` with an empty outgoing channel
moves `m` one edge forward and leaves every node unchanged. -/
private theorem twoHopStep_relay {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {t : Fin n} {cfg : TwoHopConfig n U} {m : TwoHopMsg U}
    (hc : cfg.chan (t - 1) = [m]) (hn : cfg.node t = .relay) (he : cfg.chan t = []) :
    (twoHopStep t cfg).node = cfg.node ∧ ∀ e, (twoHopStep t cfg).chan e =
      if e = t then [m] else if e = t - 1 then [] else cfg.chan e := by
  refine ⟨by rw [twoHopStep_node_of_cons hc, hn]; exact Function.update_eq_self_iff.mpr hn.symm,
    fun e => ?_⟩
  have ht : t - 1 ≠ t := fun h => by rw [h, he] at hc; cases hc
  rw [twoHopStep_chan_apply hc, hn]
  by_cases h1 : e = t
  · subst h1; simp [ht.symm, he, twoHopRecv]
  · simp only [h1, ↓reduceIte, List.append_nil]

/-- **Single-wave execution lemma (`mtr_wave`).**
Starting from any configuration `cfg₀` where passive nodes `i ∉ A` are `.relay` and channels hold
`[payload i]` on `i ∈ A` and `[]` on `i ∉ A`, relaying every message across `Aᶜ` and delivering to
every `q ∈ A` is a valid `LTS.MTr` trace emitting `(n - A.card) + ∑ q ∈ A, out_q.sent.length`
messages and leaving each `q ∈ A` in `out_q.nextNode` with channel `out_q.sent`! -/
private theorem mtr_wave {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {A : Finset (Fin n)} (hA : A.Nonempty) (payload : Fin n → TwoHopMsg U)
    {cfg₀ : TwoHopConfig n U}
    (hnode₀ : ∀ i, i ∉ A → cfg₀.node i = .relay)
    (hchan₀ : ∀ i, cfg₀.chan i = if i ∈ A then [payload i] else []) :
    ∃ (sched : List (Fin n)) (cfg₂ : TwoHopConfig n U),
      (twoHopLTS n U).MTr cfg₀ sched cfg₂ ∧
      twoHopEmittedMsgs cfg₀ sched =
        (n - A.card) +
          ∑ q ∈ A, (twoHopRecv (cfg₀.node q) (payload (prevActive A q))).sent.length ∧
      (∀ i, cfg₂.node i =
        if i ∈ A then (twoHopRecv (cfg₀.node i) (payload (prevActive A i))).nextNode
        else .relay) ∧
      (∀ i, cfg₂.chan i =
        if i ∈ A then (twoHopRecv (cfg₀.node i) (payload (prevActive A i))).sent
        else []) := by
  -- Stage 1a: advance each `p ∈ A` from `prog p = 0` to `prog p = arcLen A p - 1` across relays.
  have hstage1a : ∀ rem : ℕ, ∀ (prog : Fin n → ℕ) (cfg : TwoHopConfig n U),
      (∑ p ∈ A, (arcLen A p - 1 - prog p) = rem) →
      (∀ p ∈ A, prog p ≤ arcLen A p - 1) →
      cfg.node = cfg₀.node →
      (∀ p ∈ A, cfg.chan (p + Fin.ofNat n (prog p)) = [payload p]) →
      (∀ e : Fin n, (∀ p ∈ A, e ≠ p + Fin.ofNat n (prog p)) → cfg.chan e = []) →
      ∃ (s₁ : List (Fin n)) (cfg₁ : TwoHopConfig n U),
        (twoHopLTS n U).MTr cfg s₁ cfg₁ ∧
        twoHopEmittedMsgs cfg s₁ = rem ∧
        cfg₁.node = cfg₀.node ∧
        (∀ e : Fin n, cfg₁.chan e =
          if e + 1 ∈ A then [payload (prevActive A (e + 1))] else []) := by
    intro rem
    induction rem with
    | zero =>
      intro prog cfg hrem hprog_le hnode hchan_at hchan_else
      -- Every message sits on the last edge of its arc.
      have hlast : ∀ p ∈ A, p + Fin.ofNat n (prog p) + 1 = p + Fin.ofNat n (arcLen A p) :=
        fun p hp => by
          have := Finset.sum_eq_zero_iff.mp hrem p hp
          have := hprog_le p hp
          have := (arcLen_bounds_and_mem hp).1
          rw [add_assoc, ← ofNat_succ_eq, show prog p + 1 = arcLen A p by omega]
      refine ⟨[], cfg, LTS.MTr.refl, rfl, hnode, fun e => ?_⟩
      split_ifs with heA
      · have hpA := prevActive_mem heA
        rw [← hchan_at _ hpA]
        exact congrArg _ (add_right_cancel ((hlast _ hpA).trans (nextActive_prevActive heA))).symm
      · refine hchan_else e fun p hp hcontra => heA ?_
        rw [hcontra, hlast p hp]
        exact nextActive_mem hp
    | succ r ih =>
      intro prog cfg hrem hprog_le hnode hchan_at hchan_else
      have hlt : ∀ x ∈ A, prog x < arcLen A x := fun x hx => by
        have := hprog_le x hx; have := (arcLen_bounds_and_mem hx).1; omega
      obtain ⟨p, hpA, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hrem.trans_ne r.succ_ne_zero)
      replace hp : prog p + 1 < arcLen A p := by omega
      obtain ⟨t, ht⟩ : ∃ t, t = p + Fin.ofNat n (prog p + 1) := ⟨_, rfl⟩
      have ht_pred : t - 1 = p + Fin.ofNat n (prog p) := by
        rw [ht, ofNat_succ_eq, ← add_assoc, add_sub_cancel_right]
      have ht_notA : t ∉ A := ht ▸ (arcLen_bounds_and_mem hpA).2.2.2 _ (by omega) hp
      have hchan_pred : cfg.chan (t - 1) = [payload p] := by rw [ht_pred, hchan_at p hpA]
      have hnode_t : cfg.node t = .relay := (congrFun hnode t).trans (hnode₀ t ht_notA)
      obtain ⟨hnode', hchan'⟩ := twoHopStep_relay hchan_pred hnode_t <|
        hchan_else t fun x hx h => by
          obtain ⟨rfl, h⟩ := arc_point_inj hpA hx hp (hlt x hx) (ht.symm.trans h)
          omega
      let prog' := Function.update prog p (prog p + 1)
      have hrem' : ∑ x ∈ A, (arcLen A x - 1 - prog' x) = r := by
        have h : ∑ x ∈ A.erase p, (arcLen A x - 1 - prog' x) =
            ∑ x ∈ A.erase p, (arcLen A x - 1 - prog x) := Finset.sum_congr rfl fun x hx => by
          simp only [prog', Function.update_of_ne (Finset.ne_of_mem_erase hx)]
        rw [← Finset.add_sum_erase _ _ hpA, h]
        rw [← Finset.add_sum_erase _ _ hpA] at hrem
        simp only [prog', Function.update_self]
        omega
      have hprog'_le : ∀ x ∈ A, prog' x ≤ arcLen A x - 1 := fun x hx => by
        by_cases hxp : x = p <;> simp [prog', hxp, hprog_le x hx]; omega
      have hat : ∀ x ∈ A, (twoHopStep t cfg).chan (x + Fin.ofNat n (prog' x)) = [payload x] := by
        intro x hx
        rw [hchan']
        by_cases hxp : x = p
        · subst hxp; simp only [prog', Function.update_self, ← ht, ↓reduceIte]
        · have h1 : x + Fin.ofNat n (prog x) ≠ t := fun h =>
            hxp (arc_point_inj hx hpA (hlt x hx) hp (h.trans ht)).1
          have h2 : x + Fin.ofNat n (prog x) ≠ t - 1 := fun h =>
            hxp (arc_point_inj hx hpA (hlt x hx) (hlt p hpA) (h.trans ht_pred)).1
          simp only [prog', Function.update_of_ne hxp, h1, h2, ↓reduceIte, hchan_at x hx]
      have helse : ∀ e : Fin n, (∀ x ∈ A, e ≠ x + Fin.ofNat n (prog' x)) →
          (twoHopStep t cfg).chan e = [] := by
        intro e he
        have h1 : e ≠ t := by rw [ht]; simpa only [prog', Function.update_self] using he p hpA
        rw [hchan', ite_eq_right h1]
        split_ifs with h2
        · rfl
        refine hchan_else e fun x hx hx_eq => ?_
        by_cases hxp : x = p
        · exact h2 (hx_eq.trans (hxp ▸ ht_pred.symm))
        · exact he x hx (by simpa only [prog', Function.update_of_ne hxp] using hx_eq)
      obtain ⟨s, cfg₁, hmtr, hmsgs, hnode₁, hchan₁⟩ :=
        ih prog' _ hrem' hprog'_le (hnode'.trans hnode) hat helse
      refine ⟨t :: s, cfg₁, LTS.MTr.stepL ⟨by simp [hchan_pred], rfl⟩ hmtr, ?_, hnode₁, hchan₁⟩
      simp only [twoHopEmittedMsgs, twoHopStepMsgs, hchan_pred, hnode_t, twoHopRecv,
        List.length_singleton, hmsgs]
      omega
  -- Instantiate Stage 1a with `prog = fun _ => 0`:
  have hrem0 : ∑ p ∈ A, (arcLen A p - 1 - 0) = n - A.card := by
    have hsum1 : ∑ p ∈ A, (arcLen A p - 1 + 1) = ∑ p ∈ A, arcLen A p :=
      Finset.sum_congr rfl fun p hp => by have := (arcLen_bounds_and_mem hp).1; omega
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, sum_arcLen_eq hA] at hsum1
    simp only [Nat.sub_zero]
    omega
  obtain ⟨s₁, cfg₁, hmtr₁, hmsgs₁, hnode₁, hchan₁⟩ :=
    hstage1a (n - A.card) (fun _ => 0) cfg₀ hrem0 (fun _ _ => Nat.zero_le _) rfl
      (fun p hp => by simp [hchan₀, hp])
      (fun e he => by simpa [hchan₀] using fun h => he e h (add_zero e).symm)
  -- Stage 1b: deliver to each active node `q ∈ A` one by one (`rem = (A \ Done).card`):
  let outAt (q : Fin n) := twoHopRecv (cfg₀.node q) (payload (prevActive A q))
  have hstage1b : ∀ rem : ℕ, ∀ (Done : Finset (Fin n)) (cfg : TwoHopConfig n U),
      Done ⊆ A →
      (A \ Done).card = rem →
      (∀ i, cfg.node i = if i ∈ Done then (outAt i).nextNode else cfg₀.node i) →
      (∀ e, cfg.chan e =
        (if e + 1 ∈ A \ Done then [payload (prevActive A (e + 1))] else []) ++
          (if e ∈ Done then (outAt e).sent else [])) →
      ∃ (s₂ : List (Fin n)) (cfg₂ : TwoHopConfig n U),
        (twoHopLTS n U).MTr cfg s₂ cfg₂ ∧
        twoHopEmittedMsgs cfg s₂ = ∑ q ∈ A \ Done, (outAt q).sent.length ∧
        (∀ i, cfg₂.node i = if i ∈ A then (outAt i).nextNode else .relay) ∧
        (∀ e, cfg₂.chan e = if e ∈ A then (outAt e).sent else []) := by
    intro rem
    induction rem with
    | zero =>
      intro Done cfg hsub hcard0 hnode_d hchan_d
      obtain rfl : Done = A := hsub.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard0))
      refine ⟨[], cfg, LTS.MTr.refl, by simp [twoHopEmittedMsgs], fun i => ?_,
        fun e => by simp [hchan_d e]⟩
      by_cases hi : i ∈ Done <;> simp [hnode_d i, hi, hnode₀ i]
    | succ r ih =>
      intro Done cfg hsub hcard_r hnode_d hchan_d
      obtain ⟨q, hq_sdiff⟩ := Finset.card_pos.mp (by omega : 0 < (A \ Done).card)
      obtain ⟨hqA, hq_notDone⟩ := Finset.mem_sdiff.mp hq_sdiff
      have hq_pred_chan : cfg.chan (q - 1) =
          payload (prevActive A q) :: (if q - 1 ∈ Done then (outAt (q - 1)).sent else []) := by
        rw [hchan_d (q - 1), sub_add_cancel]
        simp only [hq_sdiff, ↓reduceIte, List.singleton_append]
      have hq_node : cfg.node q = cfg₀.node q := by simp only [hnode_d q, hq_notDone, ↓reduceIte]
      obtain ⟨s, cfg₂, hmtr, hmsgs, hnode₂, hchan₂⟩ :=
        ih (insert q Done) (twoHopStep q cfg) (Finset.insert_subset hqA hsub)
          (by rw [Finset.sdiff_insert, Finset.card_erase_of_mem hq_sdiff]; omega)
          (fun i => by
            rw [twoHopStep_node_of_cons hq_pred_chan, Function.update_apply, hnode_d i]
            by_cases hi : i = q <;> simp [hi, hq_node, outAt])
          (fun e => by
            have hs : (if e ∈ Done then (outAt e).sent else []) ++
                (if e = q then (outAt q).sent else []) =
                if e ∈ insert q Done then (outAt e).sent else [] := by
              by_cases h : e = q <;> simp [h, hq_notDone]
            rw [twoHopStep_chan_apply hq_pred_chan e, hq_node, hchan_d e, ← hs]
            by_cases h1 : e = q - 1
            · subst h1; simp [outAt]
            · have : e + 1 ≠ q := fun h => h1 (eq_sub_of_add_eq h)
              simp [h1, this, outAt])
      refine ⟨q :: s, cfg₂, LTS.MTr.stepL ⟨by simp [hq_pred_chan], rfl⟩ hmtr, ?_, hnode₂, hchan₂⟩
      rw [twoHopEmittedMsgs, hmsgs, Finset.sdiff_insert, ← Finset.add_sum_erase _ _ hq_sdiff]
      simp only [twoHopStepMsgs, hq_pred_chan, hq_node, outAt]
  -- Combine Stage 1a and Stage 1b:
  obtain ⟨s₂, cfg₂, hmtr₂, hmsgs₂, hnode₂, hchan₂⟩ :=
    hstage1b A.card ∅ cfg₁ (Finset.empty_subset A) (by simp)
      (fun i => by simp only [Finset.notMem_empty, ↓reduceIte, hnode₁])
      (fun e => by simp only [Finset.sdiff_empty, Finset.notMem_empty, ↓reduceIte,
        List.append_nil, hchan₁])
  simp only [Finset.sdiff_empty] at hmsgs₂
  refine ⟨s₁ ++ s₂, cfg₂, hmtr₁.comp (twoHopLTS n U) hmtr₂, ?_, hnode₂, hchan₂⟩
  rw [twoHopEmittedMsgs_append, twoHopExec_of_mtr hmtr₁, hmsgs₁, hmsgs₂]

/-! ### Canonical full-protocol run and main theorems -/

private def IsPhaseStartCfg {n : ℕ} {U : Type*} (st : TwoHopPhaseState n U)
    (cfg : TwoHopConfig n U) : Prop :=
  (∀ i, cfg.node i = if i ∈ st.active then .active1 (st.tidMap i) else .relay) ∧
  (∀ i, cfg.chan i = if i ∈ st.active then [.hop1 (st.tidMap i)] else [])

/-- One elimination phase (`2 ≤ st.active.card`) takes `IsPhaseStartCfg st` to
`IsPhaseStartCfg st'` while emitting `2 * n - st.active.card + st'.active.card` messages! -/
private theorem mtr_elimination_phase {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {st : TwoHopPhaseState n U} {cfg₀ : TwoHopConfig n U}
    (hstart : IsPhaseStartCfg st cfg₀) (h2 : 2 ≤ st.active.card)
    (hinj : Set.InjOn st.tidMap st.active) :
    let st' : TwoHopPhaseState n U :=
      ⟨twoHopSurvivors st.active st.tidMap, fun r => st.tidMap (prevActive st.active r)⟩
    ∃ (sched : List (Fin n)) (cfg₂ : TwoHopConfig n U),
      (twoHopLTS n U).MTr cfg₀ sched cfg₂ ∧
      twoHopEmittedMsgs cfg₀ sched = 2 * n - st.active.card + st'.active.card ∧
      IsPhaseStartCfg st' cfg₂ := by
  intro st'
  have hA_ne : st.active.Nonempty := Finset.card_pos.mp (by omega)
  have hA_le_n : st.active.card ≤ n := st.active.card_le_univ.trans_eq (Fintype.card_fin n)
  -- Pass 1 (`hop1` wave):
  obtain ⟨w₁, cfg₁, hmtr₁, hmsgs₁, hnode₁, hchan₁⟩ :=
    mtr_wave hA_ne (fun i => TwoHopMsg.hop1 (st.tidMap i))
      (fun i hi => by rw [hstart.1 i]; simp only [hi, ↓reduceIte])
      hstart.2
  have hpass1_out : ∀ q ∈ st.active,
      twoHopRecv (cfg₀.node q) (.hop1 (st.tidMap (prevActive st.active q))) =
        ⟨.active2 (st.tidMap q) (st.tidMap (prevActive st.active q)),
          [.hop2 (st.tidMap (prevActive st.active q))]⟩ := by
    intro q hq
    have hp_ne : prevActive st.active q ≠ q := prevActive_ne_self_of_two_le_card h2 hq
    have htid_ne : st.tidMap (prevActive st.active q) ≠ st.tidMap q := fun h =>
      hp_ne (hinj (prevActive_mem hq) hq h)
    rw [hstart.1 q]
    simp only [hq, ↓reduceIte, twoHopRecv, htid_ne]
  have hmsgs₁_eq : twoHopEmittedMsgs cfg₀ w₁ = n := by
    rw [hmsgs₁, Finset.sum_congr rfl fun q hq =>
      congrArg (fun o : TwoHopLocalOut U => o.sent.length) (hpass1_out q hq)]
    simp only [List.length_singleton, Finset.sum_const, smul_eq_mul, mul_one]
    omega
  -- Pass 2 (`hop2` wave):
  obtain ⟨w₂, cfg₂, hmtr₂, hmsgs₂, hnode₂, hchan₂⟩ :=
    mtr_wave hA_ne (fun q => TwoHopMsg.hop2 (st.tidMap (prevActive st.active q)))
      (fun i hi => by rw [hnode₁ i]; simp only [hi, ↓reduceIte])
      (fun i => by by_cases hi : i ∈ st.active <;> simp [hchan₁ i, hi, hpass1_out])
  have hpass2_out : ∀ r ∈ st.active,
      twoHopRecv (cfg₁.node r)
        (.hop2 (st.tidMap (prevActive st.active (prevActive st.active r)))) =
      if r ∈ st'.active then ⟨.active1 (st'.tidMap r), [.hop1 (st'.tidMap r)]⟩
      else ⟨.relay, []⟩ := by
    intro r hr
    rw [hnode₁ r, ite_eq_left hr, hpass1_out r hr]
    simp only [twoHopRecv, st', twoHopSurvivors, Finset.mem_filter, hr, true_and]
  have hmsgs₂_eq : twoHopEmittedMsgs cfg₁ w₂ = (n - st.active.card) + st'.active.card := by
    rw [hmsgs₂, Finset.sum_congr rfl fun r hr =>
      (congrArg (fun o : TwoHopLocalOut U => o.sent.length) (hpass2_out r hr)).trans
        (apply_ite (fun o : TwoHopLocalOut U => o.sent.length) _ _ _)]
    simp only [List.length_singleton, List.length_nil]
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, Finset.filter_mem_eq_inter]
    congr 2
    exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  refine ⟨w₁ ++ w₂, cfg₂, hmtr₁.comp (twoHopLTS n U) hmtr₂, ?_, fun i => ?_, fun i => ?_⟩
  · rw [twoHopEmittedMsgs_append, twoHopExec_of_mtr hmtr₁, hmsgs₁_eq, hmsgs₂_eq]
    omega
  all_goals
    by_cases hiA : i ∈ st.active
    · simp only [hnode₂, hchan₂, hiA, ↓reduceIte, hpass2_out i hiA]
      split_ifs <;> rfl
    · have hiS : i ∉ st'.active := fun h => hiA (Finset.filter_subset _ _ h)
      simp only [hnode₂, hchan₂, hiA, hiS, ↓reduceIte]

/-- Existence of the canonical terminating wave execution reaching a unique `.leader maxUid` in
`2 * n * twoHopAllActivePhases uid + n` total messages! -/
private theorem exists_canonical_terminal {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    ∃ (syncSched : List (Fin n)) (cfg_term : TwoHopConfig n U) (iStar : Fin n) (maxUid : U),
      (twoHopLTS n U).MTr (twoHopAllActiveInit uid) syncSched cfg_term ∧
      (twoHopLTS n U).IsTerminal cfg_term ∧
      twoHopAllActiveExecMsgs uid syncSched = 2 * n * twoHopAllActivePhases uid + n ∧
      (∀ j, uid j ≤ maxUid) ∧
      (∃ j₀, uid j₀ = maxUid) ∧
      cfg_term.node iStar = .leader maxUid ∧
      ∀ j, j ≠ iStar → cfg_term.node j = .relay := by
  let K := twoHopAllActivePhases uid
  obtain ⟨hK_le_log, hcard_K, _⟩ := twoHopAllActive_phases_le_log huid
  -- Induct `k = 0, …, K` to reach `IsPhaseStartCfg (twoHopAllActivePhase uid K)`!
  have hphases : ∀ k ≤ K,
      ∃ (sched_k : List (Fin n)) (cfg_k : TwoHopConfig n U),
        (twoHopLTS n U).MTr (twoHopAllActiveInit uid) sched_k cfg_k ∧
        IsPhaseStartCfg (twoHopAllActivePhase uid k) cfg_k ∧
        n + twoHopEmittedMsgs (twoHopAllActiveInit uid) sched_k =
          2 * n * k + (twoHopAllActivePhase uid k).active.card := by
    intro k hkK
    induction k with
    | zero =>
      refine ⟨[], twoHopAllActiveInit uid, LTS.MTr.refl, ?_, ?_⟩
      · exact ⟨fun i => by simp [twoHopAllActivePhase, twoHopAllActiveInit],
          fun i => by simp [twoHopAllActivePhase, twoHopAllActiveInit]⟩
      · simp only [twoHopEmittedMsgs, add_zero, mul_zero, zero_add, twoHopAllActivePhase,
          Finset.card_univ, Fintype.card_fin]
    | succ k ih =>
      obtain ⟨sk, cfg_k, hmtr_k, hstart_k, hmsgs_k⟩ := ih (by omega)
      -- Since `k < K = twoHopAllActivePhases uid`, `2 ≤ (twoHopAllActivePhase uid k).active.card`!
      have hk2 : 2 ≤ (twoHopAllActivePhase uid k).active.card :=
        (twoHopAllActivePhases_prefix_spec uid n).2.1 k (Nat.lt_of_succ_le hkK)
      have hinj_k :
          Set.InjOn (twoHopAllActivePhase uid k).tidMap (twoHopAllActivePhase uid k).active :=
        (twoHopAllActivePhase_inv huid k).2.1
      obtain ⟨w, cfg_next, hmtr_w, hmsgs_w, hstart_next⟩ :=
        mtr_elimination_phase hstart_k hk2 hinj_k
      have hphase_succ : twoHopAllActivePhase uid (k + 1) =
          ⟨twoHopSurvivors (twoHopAllActivePhase uid k).active (twoHopAllActivePhase uid k).tidMap,
            fun r => (twoHopAllActivePhase uid k).tidMap
              (prevActive (twoHopAllActivePhase uid k).active r)⟩ := by
        simp only [twoHopAllActivePhase, hk2, ↓reduceIte]
      have hcard_le_n : (twoHopAllActivePhase uid k).active.card ≤ n :=
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
      refine ⟨sk ++ w, cfg_next, hmtr_k.comp (twoHopLTS n U) hmtr_w, hphase_succ ▸ hstart_next,
        ?_⟩
      rw [twoHopEmittedMsgs_append, twoHopExec_of_mtr hmtr_k, hphase_succ, mul_add_one]
      dsimp only at hmsgs_w ⊢
      omega
  obtain ⟨sK, cfgK, hmtrK, hstartK, hmsgsK⟩ := hphases K le_rfl
  -- Now `(twoHopAllActivePhase uid K).active` is a singleton `{iStar}` holding `maxUid`!
  obtain ⟨iStar, hiStar_eq⟩ := Finset.card_eq_one.mp hcard_K
  let stK := twoHopAllActivePhase uid K
  have hiStar_mem : iStar ∈ stK.active := hiStar_eq ▸ Finset.mem_singleton_self iStar
  obtain ⟨_, _, ⟨qMax, hqMax_mem, hqMax_eq, _⟩⟩ := twoHopAllActivePhase_inv huid K
  obtain rfl : qMax = iStar := Finset.mem_singleton.mp (hiStar_eq ▸ hqMax_mem)
  let maxUid := stK.tidMap qMax
  -- Run the final `active = 1` wave (`mtr_wave`) from `cfgK`:
  obtain ⟨w_end, cfg_term, hmtr_end, hmsgs_end, hnode_end, hchan_end⟩ :=
    mtr_wave ⟨qMax, hiStar_mem⟩ (fun i => TwoHopMsg.hop1 (stK.tidMap i))
      (fun i hi => by simp [hstartK.1 i, show i ∉ (twoHopAllActivePhase uid K).active from hi])
      hstartK.2
  have hprev_self : prevActive stK.active qMax = qMax :=
    Finset.mem_singleton.mp (hiStar_eq ▸ prevActive_mem hiStar_mem)
  have hout_iStar :
      twoHopRecv (cfgK.node qMax) (.hop1 (stK.tidMap (prevActive stK.active qMax))) =
        ⟨.leader maxUid, []⟩ := by
    rw [hprev_self, hstartK.1 qMax]
    dsimp only [stK, maxUid] at hiStar_mem ⊢
    simp only [hiStar_mem, ↓reduceIte, twoHopRecv]
  have hchan_empty : ∀ e, cfg_term.chan e = [] := fun e => by
    rw [hchan_end e]
    split_ifs with he
    · rw [show e = qMax from Finset.mem_singleton.mp (hiStar_eq ▸ he), hout_iStar]
    · rfl
  have hterm : (twoHopLTS n U).IsTerminal cfg_term := by
    intro target _ ⟨hne, _⟩
    exact hne (hchan_empty (target - 1))
  have hmsgs_end_eq : twoHopEmittedMsgs cfgK w_end = n - 1 := by
    rw [hmsgs_end, show stK.active = {qMax} from hiStar_eq]
    simp only [Finset.card_singleton, Finset.sum_singleton]
    rw [← hiStar_eq, hout_iStar]
    rfl
  have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- Identify `maxUid` with `(Finset.univ.image uid).max'` for `∀ j, uid j ≤ maxUid`:
  have hne_univ : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, Finset.mem_univ _⟩
  rcases Finset.mem_image.mp (Finset.max'_mem (Finset.univ.image uid) (hne_univ.image uid)) with
    ⟨j₀, _, hj₀_eq⟩
  refine ⟨sK ++ w_end, cfg_term, qMax, maxUid, hmtrK.comp (twoHopLTS n U) hmtr_end, hterm,
    ?_, fun j => ?_, ⟨j₀, hj₀_eq.trans hqMax_eq.symm⟩, ?_, ?_⟩
  · rw [twoHopAllActiveExecMsgs, twoHopEmittedMsgs_append, twoHopExec_of_mtr hmtrK, hmsgs_end_eq]
    change n + (twoHopEmittedMsgs (twoHopAllActiveInit uid) sK + (n - 1)) = 2 * n * K + n
    rw [← add_assoc, hmsgsK, hcard_K]
    omega
  · dsimp only [maxUid, stK]
    exact hqMax_eq ▸ Finset.le_max' _ (uid j) (Finset.mem_image_of_mem uid (Finset.mem_univ j))
  · simp only [hnode_end qMax, hiStar_mem, ↓reduceIte, hout_iStar]
  · intro j hj
    have hj_not : j ∉ stK.active := fun h => hj (Finset.mem_singleton.mp (hiStar_eq ▸ h))
    simp only [hnode_end j, hj_not, ↓reduceIte]

private theorem mtr_eq_nil_of_isTerminal {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {cfg cfg_term : TwoHopConfig n U} {rem : List (Fin n)}
    (hrem : (twoHopLTS n U).MTr cfg rem cfg_term) (hterm : (twoHopLTS n U).IsTerminal cfg) :
    rem = [] ∧ cfg = cfg_term := by
  cases rem with
  | nil => exact ⟨rfl, LTS.MTr.nil_eq (twoHopLTS n U) hrem⟩
  | cons a _ =>
    rcases LTS.MTr.cons_iff.mp hrem with ⟨c', htr, _⟩
    exact absurd htr (hterm a c')

/-- A bounded-termination and unique-leader election step for all-initially-active basic two-hop
unidirectional FIFO ring election (a step towards [Peterson][Peterson1982], not the
spontaneous-wakeup or Fibonacci-threshold endpoint): for any injective `uid : Fin n → U` on `Fin n`:
1. Every configuration reachable from `twoHopAllActiveInit uid` extends to a quiescent
   (`LTS.IsTerminal`) configuration;
2. Every quiescent configuration reachable from `twoHopAllActiveInit uid` coincides with the unique
   terminal configuration where a single node `i*` holds `.leader maxUid` (`maxUid = max_j (uid j)`)
   and all `j ≠ i*` are passive `.relay`s (`∃! i*, cfg.isLeader i* = true`). -/
theorem twoHopAllActive_elects_leader {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    (∀ sched cfg, (twoHopLTS n U).MTr (twoHopAllActiveInit uid) sched cfg →
      ∃ rem cfg_term, (twoHopLTS n U).MTr cfg rem cfg_term ∧
        (twoHopLTS n U).IsTerminal cfg_term) ∧
    ∀ sched cfg, (twoHopLTS n U).MTr (twoHopAllActiveInit uid) sched cfg →
      (twoHopLTS n U).IsTerminal cfg →
      ∃! iStar : Fin n,
        cfg.isLeader iStar = true ∧
        (∃ maxUid, cfg.node iStar = .leader maxUid ∧
          (∀ j, uid j ≤ maxUid) ∧ ∃ j₀, uid j₀ = maxUid) ∧
        ∀ j, j ≠ iStar → cfg.node j = .relay := by
  obtain ⟨syncSched, cfg_term, iStar, maxUid, hsync, hterm, _, hmax_le, hmax_ex, hleader, hrelay⟩ :=
    exists_canonical_terminal huid
  refine ⟨fun sched cfg hmtr => ?_, fun sched cfg hmtr hcfg_term => ?_⟩
  · obtain ⟨rem, hrem, _, _⟩ := confluence_of_canonical_terminal hsync hterm hmtr
    exact ⟨rem, cfg_term, hrem, hterm⟩
  · obtain ⟨rem, hrem, _, _⟩ := confluence_of_canonical_terminal hsync hterm hmtr
    obtain ⟨_, rfl⟩ := mtr_eq_nil_of_isTerminal hrem hcfg_term
    refine ⟨iStar, ⟨by simp [TwoHopConfig.isLeader, hleader, TwoHopNode.isLeader],
      ⟨maxUid, hleader, hmax_le, hmax_ex⟩, hrelay⟩, fun k hk => ?_⟩
    by_contra hne
    simp [TwoHopConfig.isLeader, hrelay k hne, TwoHopNode.isLeader] at hk

/-- A complete-run message-accounting step for all-initially-active basic two-hop unidirectional
FIFO ring election (a step towards [Peterson][Peterson1982], not the cited endpoint): every complete
execution `(twoHopLTS n U).MTr (twoHopAllActiveInit uid) sched cfg` (`IsTerminal cfg`) transmits
`2 * n * twoHopAllActivePhases uid + n` messages regardless of the asynchronous FIFO delivery
order. -/
theorem twoHopAllActive_execMsgs_eq {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid)
    {sched : List (Fin n)} {cfg : TwoHopConfig n U}
    (hmtr : (twoHopLTS n U).MTr (twoHopAllActiveInit uid) sched cfg)
    (hterm : (twoHopLTS n U).IsTerminal cfg) :
    twoHopAllActiveExecMsgs uid sched = 2 * n * twoHopAllActivePhases uid + n := by
  obtain ⟨syncSched, cfg_term, _, _, hsync, hsync_term, hsync_msgs, _, _, _, _⟩ :=
    exists_canonical_terminal huid
  obtain ⟨rem, hrem, _, hw⟩ := confluence_of_canonical_terminal hsync hsync_term hmtr
  obtain ⟨rfl, _⟩ := mtr_eq_nil_of_isTerminal hrem hterm
  simp only [twoHopEmittedMsgs, add_zero] at hw
  rw [twoHopAllActiveExecMsgs, hw, ← twoHopAllActiveExecMsgs, hsync_msgs]

/-- An asynchronous message-bound step for all-initially-active basic two-hop unidirectional FIFO
ring election (a step towards [Peterson][Peterson1982], not the spontaneous-wakeup or
`1.44 n log₂ n` Fibonacci-threshold endpoint): in every execution
`(twoHopLTS n U).MTr (twoHopAllActiveInit uid) sched cfg` (partial or complete), total messages
transmitted across all edges satisfy `twoHopAllActiveExecMsgs uid sched ≤ 2 * n * Nat.log 2 n + n`.
-/
theorem twoHopAllActive_messages_le {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid)
    {sched : List (Fin n)} {cfg : TwoHopConfig n U}
    (hmtr : (twoHopLTS n U).MTr (twoHopAllActiveInit uid) sched cfg) :
    twoHopAllActiveExecMsgs uid sched ≤ 2 * n * Nat.log 2 n + n := by
  obtain ⟨syncSched, cfg_term, _, _, hsync, hsync_term, hsync_msgs, _, _, _, _⟩ :=
    exists_canonical_terminal huid
  obtain ⟨rem, _, _, hw⟩ := confluence_of_canonical_terminal hsync hsync_term hmtr
  have hle_sync : twoHopAllActiveExecMsgs uid sched ≤ twoHopAllActiveExecMsgs uid syncSched := by
    simp only [twoHopAllActiveExecMsgs]
    omega
  have hK_le : twoHopAllActivePhases uid ≤ Nat.log 2 n := (twoHopAllActive_phases_le_log huid).1
  calc twoHopAllActiveExecMsgs uid sched
      ≤ twoHopAllActiveExecMsgs uid syncSched := hle_sync
    _ = 2 * n * twoHopAllActivePhases uid + n := hsync_msgs
    _ ≤ 2 * n * Nat.log 2 n + n :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (2 * n) hK_le) n

end Cslib.Distributed.RingElection
