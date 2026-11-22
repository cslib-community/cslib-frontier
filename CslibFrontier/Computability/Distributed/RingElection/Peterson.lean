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
# Peterson's `O(n log n)` Asynchronous Unidirectional Ring Leader Election

Deterministic `O(n log n)` leader election on an asynchronous FIFO unidirectional ring `Fin n`
(`n ≥ 1`) with injective identifiers `uid : Fin n → U` from a linear order `U`, following
[Peterson][Peterson1982].

Active processors hold a current temporary identifier `tid` and execute two-hop comparison phases
while eliminated processors act as passive FIFO relays (`.relay`):

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

* **Phase combinatorics (`petersonSurvivors_card_halving`, `peterson_phases_le_log`):** distinctness
  of active temporary identifiers and the global maximum `max_j (uid j)` are preserved across every
  phase (`2 ≤ active`), while adjacent active nodes cannot both be strict peaks, giving
  `2 * active_{k + 1} ≤ active_k` and hence `petersonPhases uid ≤ Nat.log 2 n` elimination phases.
  Telescoping the per-phase emissions (`n` initial + `(2n - active_k + active_{k + 1})` per
  elimination phase + `(n - 1)` in the final `active = 1` pass) yields `2 * n * K + n` messages on
  the canonical wave execution.
* **Strong weighted FIFO confluence (`petersonStep_comm`):** enabled single-message deliveries at
  distinct nodes `i ≠ j` commute in one step (`petersonStep j (petersonStep i cfg) =
  petersonStep i (petersonStep j cfg)`) with identical additive message emissions, because popping
  the head of a nonempty FIFO list commutes with appending to its tail. A general strip lemma
  transfers termination, the unique quiescent state, and the exact message bound
  `2 * n * Nat.log 2 n + n` to *every* asynchronous FIFO execution!

## Main definitions

* `Cslib.Distributed.RingElection.PetersonMsg`, `PetersonNode`, `PetersonLocalOut`, `petersonRecv`:
  untagged two-hop message payloads, processor states, and local transition handler.
* `Cslib.Distributed.RingElection.PetersonConfig`, `petersonInit`, `petersonStep`, `petersonExec`,
  `petersonLTS`, `petersonExecMsgs`: global FIFO configurations, asynchronous transitions, LTS, and
  cumulative edge-message counter.
* `Cslib.Distributed.RingElection.backLen`, `prevActive`, `nextActive`, `petersonSurvivors`,
  `PetersonPhaseState`, `petersonPhase`, `petersonPhases`: active-subring combinatorics and phase
  evolution.

## Main results

* `Cslib.Distributed.RingElection.petersonSurvivors_card_halving`,
  `Cslib.Distributed.RingElection.peterson_phase_halving`: strict per-phase halving
  `2 * active_{k + 1} ≤ active_k` whenever `2 ≤ active_k`.
* `Cslib.Distributed.RingElection.peterson_phases_le_log`: `petersonPhases uid ≤ Nat.log 2 n` and
  convergence to a single active processor holding the global maximum identifier.
* `Cslib.Distributed.RingElection.petersonStep_comm`: strong one-step FIFO confluence on `Fin n`.
* `Cslib.Distributed.RingElection.peterson_elects_leader`: bounded termination, confluence to a
  unique quiescent state, and unique leader election holding `max_j (uid j)` across all
  asynchronous FIFO schedules.
* `Cslib.Distributed.RingElection.peterson_execMsgs_eq`,
  `Cslib.Distributed.RingElection.peterson_messages_le`: exact `2 * n * petersonPhases uid + n`
  complete-run message formula and `≤ 2 * n * Nat.log 2 n + n` bound for every asynchronous FIFO
  execution.

## References

* [G. L. Peterson, *An $O(n \log n)$ Unidirectional Algorithm for the Circular Extrema
  Problem*][Peterson1982]
-/

public section

namespace Cslib.Distributed.RingElection

open Cslib

/-! ### Local processor machine and asynchronous FIFO ring LTS -/

/-- Message payload in Peterson's unidirectional ring election algorithm. -/
inductive PetersonMsg (U : Type*) where
  /-- First-hop message carrying an active node's current temporary identifier `tid`. -/
  | hop1 (tid : U)
  /-- Second-hop message carrying the predecessor active node's temporary identifier `ntid`. -/
  | hop2 (ntid : U)
  deriving @[expose] DecidableEq

/-- Local state of a processor in Peterson's unidirectional ring election algorithm. -/
inductive PetersonNode (U : Type*) where
  /-- Active node at start of phase holding `tid`, awaiting `hop1` from its predecessor. -/
  | active1 (tid : U)
  /-- Active node holding `tid` and predecessor's `ntid`, awaiting `hop2` (`nnid`). -/
  | active2 (tid ntid : U)
  /-- Passive relay node forwarding every incoming message unchanged. -/
  | relay
  /-- Elected leader node holding the global maximum identifier `maxUid`. -/
  | leader (maxUid : U)
  deriving @[expose] DecidableEq

/-- Whether a `PetersonNode` is in the elected `.leader` state. -/
@[expose] def PetersonNode.isLeader {U : Type*} : PetersonNode U → Bool
  | .leader _ => true
  | _ => false

/-- Output of a single message reception in Peterson's algorithm: updated processor state and
outgoing FIFO messages appended to `i → i + 1`. -/
structure PetersonLocalOut (U : Type*) where
  /-- Updated local state of the receiving processor. -/
  nextNode : PetersonNode U
  /-- Outgoing messages appended to the processor's clockwise channel. -/
  sent : List (PetersonMsg U)
  deriving @[expose] DecidableEq

/-- Deterministic local transition handler for Peterson's algorithm upon receiving `msg`. -/
@[expose] def petersonRecv {U : Type*} [LinearOrder U] (st : PetersonNode U)
    (msg : PetersonMsg U) : PetersonLocalOut U :=
  match st, msg with
  | .active1 tid, .hop1 ntid =>
    if ntid = tid then ⟨.leader tid, []⟩
    else ⟨.active2 tid ntid, [.hop2 ntid]⟩
  | .active2 tid ntid, .hop2 nnid =>
    if nnid < ntid ∧ tid < ntid then ⟨.active1 ntid, [.hop1 ntid]⟩
    else ⟨.relay, []⟩
  | .relay, m => ⟨.relay, [m]⟩
  | st, _ => ⟨st, []⟩

/-- Global configuration of Peterson's algorithm on an asynchronous FIFO unidirectional `n`-ring. -/
@[ext]
structure PetersonConfig (n : ℕ) (U : Type*) where
  /-- Local state of each node `i : Fin n`. -/
  node : Fin n → PetersonNode U
  /-- Clockwise FIFO channel on directed edge `i → i + 1` (head is oldest, tail is newest). -/
  chan : Fin n → List (PetersonMsg U)

/-- Whether node `i` has declared leadership in configuration `cfg`. -/
@[expose] def PetersonConfig.isLeader {n : ℕ} {U : Type*} (cfg : PetersonConfig n U)
    (i : Fin n) : Bool :=
  (cfg.node i).isLeader

/-- Initial configuration of Peterson's algorithm: every node `i` starts active with `tid = uid i`
and injects `[.hop1 (uid i)]` onto `i → i + 1`. -/
@[expose] def petersonInit {n : ℕ} {U : Type*} (uid : Fin n → U) : PetersonConfig n U where
  node i := .active1 (uid i)
  chan i := [.hop1 (uid i)]

/-- Deliver the oldest message on `target - 1 → target` to `target` (no-op if empty). -/
@[expose] def petersonStep {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (target : Fin n) (cfg : PetersonConfig n U) : PetersonConfig n U :=
  match cfg.chan (target - 1) with
  | [] => cfg
  | msg :: rest =>
    let out := petersonRecv (cfg.node target) msg
    let chan₁ := Function.update cfg.chan (target - 1) rest
    PetersonConfig.mk
      (Function.update cfg.node target out.nextNode)
      (Function.update chan₁ target (chan₁ target ++ out.sent))

/-- Number of messages emitted onto `target → target + 1` by a single `petersonStep`. -/
@[expose] def petersonStepMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (target : Fin n) (cfg : PetersonConfig n U) : ℕ :=
  match cfg.chan (target - 1) with
  | [] => 0
  | msg :: _ => (petersonRecv (cfg.node target) msg).sent.length

/-- Execute a finite delivery schedule `sched : List (Fin n)` starting from `cfg`. -/
@[expose] def petersonExec {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (cfg : PetersonConfig n U) (sched : List (Fin n)) : PetersonConfig n U :=
  sched.foldl (fun c i => petersonStep i c) cfg

/-- Cumulative messages emitted onto ring edges during `sched` starting from `cfg`. -/
@[expose] def petersonEmittedMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (cfg : PetersonConfig n U) : List (Fin n) → ℕ
  | [] => 0
  | target :: rest =>
    petersonStepMsgs target cfg + petersonEmittedMsgs (petersonStep target cfg) rest

/-- Total messages transmitted across edges in schedule `sched` from `petersonInit uid`: the `n`
initial `.hop1` injections plus all subsequent emissions. -/
@[expose] def petersonExecMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) (sched : List (Fin n)) : ℕ :=
  n + petersonEmittedMsgs (petersonInit uid) sched

/-- Labelled transition system of enabled FIFO deliveries in Peterson's algorithm on `Fin n`. -/
@[expose] def petersonLTS (n : ℕ) [NeZero n] (U : Type*) [LinearOrder U] :
    LTS (PetersonConfig n U) (Fin n) where
  Tr cfg target cfg' := cfg.chan (target - 1) ≠ [] ∧ cfg' = petersonStep target cfg

theorem petersonEmittedMsgs_append {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (cfg : PetersonConfig n U) (s₁ s₂ : List (Fin n)) :
    petersonEmittedMsgs cfg (s₁ ++ s₂) =
      petersonEmittedMsgs cfg s₁ + petersonEmittedMsgs (petersonExec cfg s₁) s₂ := by
  induction s₁ generalizing cfg with
  | nil => simp only [List.nil_append, petersonEmittedMsgs, petersonExec, List.foldl_nil, zero_add]
  | cons a rest ih =>
    simp only [List.cons_append, petersonEmittedMsgs, petersonExec, List.foldl_cons, ih, add_assoc]

theorem petersonExec_of_mtr {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {c₀ c₁ : PetersonConfig n U} {tr : List (Fin n)}
    (hmtr : (petersonLTS n U).MTr c₀ tr c₁) :
    petersonExec c₀ tr = c₁ := by
  induction hmtr with
  | refl => rfl
  | stepL htr _ ih =>
    rw [petersonExec, List.foldl_cons, ← htr.2]
    exact ih

/-! ### Strong one-step FIFO confluence and strip lemma -/

private theorem petersonStep_node_of_cons {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {target : Fin n} {cfg : PetersonConfig n U} {msg : PetersonMsg U} {rest : List (PetersonMsg U)}
    (hq : cfg.chan (target - 1) = msg :: rest) :
    (petersonStep target cfg).node =
      Function.update cfg.node target (petersonRecv (cfg.node target) msg).nextNode := by
  simp only [petersonStep, hq]

private theorem petersonStep_chan_of_cons {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {target : Fin n} {cfg : PetersonConfig n U} {msg : PetersonMsg U} {rest : List (PetersonMsg U)}
    (hq : cfg.chan (target - 1) = msg :: rest) :
    (petersonStep target cfg).chan =
      Function.update (Function.update cfg.chan (target - 1) rest) target
        (Function.update cfg.chan (target - 1) rest target ++
          (petersonRecv (cfg.node target) msg).sent) := by
  simp only [petersonStep, hq]

private theorem petersonStep_two_of_ne {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {cfg : PetersonConfig n U} {i j : Fin n} (hne : i ≠ j)
    (hi : cfg.chan (i - 1) ≠ []) (hj : cfg.chan (j - 1) ≠ []) :
    (petersonStep i cfg).chan (j - 1) =
      (cfg.chan (j - 1)).head hj ::
        (if j - 1 = i then
          (cfg.chan (j - 1)).tail ++ (petersonRecv (cfg.node i) ((cfg.chan (i - 1)).head hi)).sent
        else (cfg.chan (j - 1)).tail) ∧
    (petersonStep i cfg).node j = cfg.node j ∧
    ∀ e : Fin n, (petersonStep j (petersonStep i cfg)).chan e =
      (if e = i - 1 then (cfg.chan (i - 1)).tail
      else if e = j - 1 then (cfg.chan (j - 1)).tail
      else cfg.chan e) ++
      (if e = i then (petersonRecv (cfg.node i) ((cfg.chan (i - 1)).head hi)).sent else []) ++
      (if e = j then (petersonRecv (cfg.node j) ((cfg.chan (j - 1)).head hj)).sent else []) := by
  have hpred_ne : i - 1 ≠ j - 1 := fun h => hne (sub_left_injective h)
  have hself_ne_pred : ∀ x : Fin n, x ≠ x - 1 := by
    intro x hx
    have h10 : (1 : Fin n) = 0 := sub_eq_self.mp hx.symm
    have hn1 : n ≤ 1 := by
      by_contra hgt
      have h1val : (1 : Fin n).val = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega)
      have hv := congrArg Fin.val h10
      rw [h1val, Fin.val_zero] at hv
      omega
    have := i.isLt
    have := j.isLt
    exact hne (Fin.ext (by omega))
  let mi := (cfg.chan (i - 1)).head hi
  let ti := (cfg.chan (i - 1)).tail
  have hqi : cfg.chan (i - 1) = mi :: ti := (List.cons_head_tail hi).symm
  let mj := (cfg.chan (j - 1)).head hj
  let tj := (cfg.chan (j - 1)).tail
  have hqj : cfg.chan (j - 1) = mj :: tj := (List.cons_head_tail hj).symm
  let outi := petersonRecv (cfg.node i) mi
  let outj := petersonRecv (cfg.node j) mj
  have houti : petersonRecv (cfg.node i) mi = outi := rfl
  have houtj : petersonRecv (cfg.node j) mj = outj := rfl
  have hstep_i_at_jpred :
      (petersonStep i cfg).chan (j - 1) =
        mj :: (if j - 1 = i then tj ++ outi.sent else tj) := by
    rw [petersonStep_chan_of_cons hqi, houti]
    by_cases hji : j - 1 = i
    · rw [hji, Function.update_self, Function.update_of_ne (hself_ne_pred i), ← hji, hqj]
      simp only [↓reduceIte, List.cons_append]
    · rw [Function.update_of_ne hji, Function.update_of_ne (Ne.symm hpred_ne), hqj]
      simp only [hji, ↓reduceIte]
  have hnode_i_at_j : (petersonStep i cfg).node j = cfg.node j := by
    rw [petersonStep_node_of_cons hqi]
    exact Function.update_of_ne (Ne.symm hne) _ _
  refine ⟨hstep_i_at_jpred, hnode_i_at_j, fun e => ?_⟩
  change (petersonStep j (petersonStep i cfg)).chan e =
    (if e = i - 1 then ti else if e = j - 1 then tj else cfg.chan e) ++
      (if e = i then outi.sent else []) ++ (if e = j then outj.sent else [])
  rw [petersonStep_chan_of_cons hstep_i_at_jpred, hnode_i_at_j, houtj,
    petersonStep_chan_of_cons hqi, houti]
  by_cases hej : e = j
  · rw [hej, Function.update_self, Function.update_of_ne (hself_ne_pred j),
      Function.update_of_ne (Ne.symm hne)]
    by_cases hj_ipred : j = i - 1
    · rw [hj_ipred, Function.update_self]
      have hipred_ne_i : i - 1 ≠ i := Ne.symm (hself_ne_pred i)
      simp only [↓reduceIte, hipred_ne_i, List.append_nil]
    · rw [Function.update_of_ne hj_ipred]
      simp only [hj_ipred, hself_ne_pred j, Ne.symm hne, ↓reduceIte, List.append_nil]
  · rw [Function.update_of_ne hej]
    by_cases he_jpred : e = j - 1
    · rw [he_jpred, Function.update_self]
      have hne_ipred : j - 1 ≠ i - 1 := Ne.symm hpred_ne
      have hne_j : j - 1 ≠ j := Ne.symm (hself_ne_pred j)
      simp only [hne_ipred, hne_j, ↓reduceIte, List.append_nil]
      by_cases hji : j - 1 = i
      · simp only [hji, ↓reduceIte]
      · simp only [hji, ↓reduceIte, List.append_nil]
    · rw [Function.update_of_ne he_jpred]
      by_cases hei : e = i
      · rw [hei, Function.update_self, Function.update_of_ne (hself_ne_pred i)]
        have hi_ne_jpred : i ≠ j - 1 := fun h => he_jpred (hei.trans h)
        simp only [hself_ne_pred i, hi_ne_jpred, hne, ↓reduceIte, List.append_nil]
      · rw [Function.update_of_ne hei]
        by_cases he_ipred : e = i - 1
        · rw [he_ipred, Function.update_self]
          have hipred_ne_i : i - 1 ≠ i := he_ipred ▸ hei
          have hipred_ne_j : i - 1 ≠ j := he_ipred ▸ hej
          simp only [↓reduceIte, hipred_ne_i, hipred_ne_j, List.append_nil]
        · rw [Function.update_of_ne he_ipred]
          simp only [he_ipred, he_jpred, hei, hej, ↓reduceIte, List.append_nil]

/-- **Strong one-step FIFO confluence (`petersonStep_comm`).**
Whenever two distinct processors `i ≠ j` both have nonempty incoming channels in `cfg`, each
remains enabled after the other steps, the two delivery orders reach the exact same global
configuration, and their emitted message counts commute! -/
theorem petersonStep_comm {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {cfg : PetersonConfig n U} {i j : Fin n} (hne : i ≠ j)
    (hi : cfg.chan (i - 1) ≠ []) (hj : cfg.chan (j - 1) ≠ []) :
    (petersonStep i cfg).chan (j - 1) ≠ [] ∧
    (petersonStep j cfg).chan (i - 1) ≠ [] ∧
    petersonStep j (petersonStep i cfg) = petersonStep i (petersonStep j cfg) ∧
    petersonStepMsgs i cfg + petersonStepMsgs j (petersonStep i cfg) =
      petersonStepMsgs j cfg + petersonStepMsgs i (petersonStep j cfg) := by
  obtain ⟨hstep_i_at_jpred, hnode_i_at_j, hlhs⟩ := petersonStep_two_of_ne hne hi hj
  obtain ⟨hstep_j_at_ipred, hnode_j_at_i, hrhs⟩ := petersonStep_two_of_ne hne.symm hj hi
  have hqi : cfg.chan (i - 1) = (cfg.chan (i - 1)).head hi :: (cfg.chan (i - 1)).tail :=
    (List.cons_head_tail hi).symm
  have hqj : cfg.chan (j - 1) = (cfg.chan (j - 1)).head hj :: (cfg.chan (j - 1)).tail :=
    (List.cons_head_tail hj).symm
  refine ⟨by rw [hstep_i_at_jpred]; exact List.cons_ne_nil _ _,
    by rw [hstep_j_at_ipred]; exact List.cons_ne_nil _ _, ?_, ?_⟩
  · refine PetersonConfig.ext (funext fun x => ?_) (funext fun e => ?_)
    · rw [petersonStep_node_of_cons hstep_i_at_jpred, hnode_i_at_j,
        petersonStep_node_of_cons hstep_j_at_ipred, hnode_j_at_i,
        petersonStep_node_of_cons hqi, petersonStep_node_of_cons hqj]
      by_cases hxj : x = j
      · rw [hxj, Function.update_self, Function.update_of_ne (Ne.symm hne), Function.update_self]
      · by_cases hxi : x = i
        · rw [hxi, Function.update_of_ne hne, Function.update_self, Function.update_self]
        · simp only [Function.update_of_ne hxj, Function.update_of_ne hxi]
    · rw [hlhs e, hrhs e]
      have hpred_ne : i - 1 ≠ j - 1 := fun h => hne (sub_left_injective h)
      have hbase_eq :
          (if e = i - 1 then (cfg.chan (i - 1)).tail
            else if e = j - 1 then (cfg.chan (j - 1)).tail else cfg.chan e) =
          (if e = j - 1 then (cfg.chan (j - 1)).tail
            else if e = i - 1 then (cfg.chan (i - 1)).tail else cfg.chan e) := by
        by_cases he : e = i - 1
        · simp only [he, hpred_ne, ↓reduceIte]
        · simp only [he, ↓reduceIte]
      rw [hbase_eq]
      by_cases hei : e = i
      · simp only [hei, hne, ↓reduceIte, List.append_nil]
      · simp only [hei, ↓reduceIte, List.append_nil]
  · have hmsgs_cons : ∀ {c : PetersonConfig n U} {t : Fin n} {m : PetersonMsg U}
        {r : List (PetersonMsg U)}, c.chan (t - 1) = m :: r →
        petersonStepMsgs t c = (petersonRecv (c.node t) m).sent.length := by
      intro c t m r hq
      simp only [petersonStepMsgs, hq]
    rw [hmsgs_cons hqi, hmsgs_cons hstep_i_at_jpred, hnode_i_at_j,
      hmsgs_cons hqj, hmsgs_cons hstep_j_at_ipred, hnode_j_at_i, Nat.add_comm]

/-- **Strip lemma (`strip_one_step`).**
Given a terminating trace `MTr cfg tr cfg_term` (`IsTerminal cfg_term`) and any single enabled step
`Tr cfg b cfg'`, pushing `b` across `tr` yields a strictly shorter trace `tr'` from `cfg'` to the
*same* terminal configuration `cfg_term` with the *same* total emitted messages! -/
private theorem strip_one_step {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {cfg cfg' cfg_term : PetersonConfig n U} {tr : List (Fin n)} {b : Fin n}
    (hmtr : (petersonLTS n U).MTr cfg tr cfg_term)
    (hterm : (petersonLTS n U).IsTerminal cfg_term)
    (hstep : (petersonLTS n U).Tr cfg b cfg') :
    ∃ tr' : List (Fin n),
      (petersonLTS n U).MTr cfg' tr' cfg_term ∧
      tr'.length + 1 = tr.length ∧
      petersonStepMsgs b cfg + petersonEmittedMsgs cfg' tr' = petersonEmittedMsgs cfg tr := by
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
        petersonStep_comm (Ne.symm hba) ha_en hb_en
      let cfg₂ := petersonStep b (petersonStep a cfg)
      have htr_b' : (petersonLTS n U).Tr (petersonStep a cfg) b cfg₂ := ⟨hb_after_a, rfl⟩
      have htr_a' : (petersonLTS n U).Tr (petersonStep b cfg) a cfg₂ := ⟨ha_after_b, hcomm⟩
      obtain ⟨rest', hmtr_rest', hlen_rest', hw_rest'⟩ := ih hrest htr_b'
      refine ⟨a :: rest', LTS.MTr.stepL htr_a' hmtr_rest', by simp [hlen_rest'], ?_⟩
      simp only [petersonEmittedMsgs]
      rw [← hcomm]
      dsimp only [cfg₂] at hw_rest'
      linarith

/-- **Global confluence from a canonical terminating run (`confluence_of_canonical_terminal`).**
If `syncSched` reaches a terminal configuration `cfg_term` from `cfg₀`, then *every* finite trace
`sched` from `cfg₀` can be completed to `cfg_term` with exact conservation of step length and
emitted messages! -/
private theorem confluence_of_canonical_terminal {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {cfg₀ cfg_term cfg : PetersonConfig n U} {syncSched sched : List (Fin n)}
    (hsync : (petersonLTS n U).MTr cfg₀ syncSched cfg_term)
    (hterm : (petersonLTS n U).IsTerminal cfg_term)
    (hmtr : (petersonLTS n U).MTr cfg₀ sched cfg) :
    ∃ rem : List (Fin n),
      (petersonLTS n U).MTr cfg rem cfg_term ∧
      sched.length + rem.length = syncSched.length ∧
      petersonEmittedMsgs cfg₀ sched + petersonEmittedMsgs cfg rem =
        petersonEmittedMsgs cfg₀ syncSched := by
  induction hmtr generalizing syncSched with
  | refl =>
    exact ⟨syncSched, hsync, by simp, by simp [petersonEmittedMsgs]⟩
  | @stepL s1 b s2 tail s3 htr _ ih =>
    obtain ⟨sync', hsync', hlen', hw'⟩ := strip_one_step hsync hterm htr
    obtain ⟨rem, hrem, hlen_rem, hw_rem⟩ := ih hsync'
    have hs2 : s2 = petersonStep b s1 := htr.2
    subst hs2
    refine ⟨rem, hrem, by simp only [List.length_cons]; omega, ?_⟩
    simp only [petersonEmittedMsgs]
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

theorem backLen_bounds_and_mem {n : ℕ} [NeZero n] {A : Finset (Fin n)} {q : Fin n} (hq : q ∈ A) :
    1 ≤ backLen A q ∧ backLen A q ≤ n ∧ prevActive A q ∈ A ∧
      ∀ k, 1 ≤ k → k < backLen A q → q - Fin.ofNat n k ∉ A := by
  have hnq : -q ∈ A.image (fun y : Fin n => -y) := (mem_neg_image_iff A q).mpr hq
  obtain ⟨h1, hn, hmem, hmin⟩ := arcLen_bounds_and_mem hnq
  have hneg_sub : ∀ d, -q + Fin.ofNat n d = -(q - Fin.ofNat n d) := fun d => by
    rw [neg_sub, sub_eq_add_neg, add_comm]
  rw [hneg_sub, mem_neg_image_iff] at hmem
  refine ⟨h1, hn, hmem, fun k hk1 hk2 => ?_⟩
  have hk := hmin k hk1 hk2
  rwa [hneg_sub, mem_neg_image_iff] at hk

theorem nextActive_mem {n : ℕ} [NeZero n] {A : Finset (Fin n)} {p : Fin n} (hp : p ∈ A) :
    nextActive A p ∈ A :=
  (arcLen_bounds_and_mem hp).2.2.1

theorem prevActive_mem {n : ℕ} [NeZero n] {A : Finset (Fin n)} {q : Fin n} (hq : q ∈ A) :
    prevActive A q ∈ A :=
  (backLen_bounds_and_mem hq).2.2.1

private theorem ofNat_sub_add_of_le {n d k : ℕ} [NeZero n] (hk : k ≤ d) :
    Fin.ofNat n d = Fin.ofNat n (d - k) + Fin.ofNat n k := by
  ext
  change d % n = ((d - k) % n + k % n) % n
  rw [← Nat.add_mod, Nat.sub_add_cancel hk]

theorem backLen_nextActive_eq {n : ℕ} [NeZero n] {A : Finset (Fin n)} {p : Fin n} (hp : p ∈ A) :
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

@[simp] theorem prevActive_nextActive {n : ℕ} [NeZero n] {A : Finset (Fin n)} {p : Fin n}
    (hp : p ∈ A) :
    prevActive A (nextActive A p) = p := by
  rw [prevActive, backLen_nextActive_eq hp, nextActive, add_sub_cancel_right]

theorem arcLen_prevActive_eq {n : ℕ} [NeZero n] {A : Finset (Fin n)} {q : Fin n} (hq : q ∈ A) :
    arcLen A (prevActive A q) = backLen A q := by
  obtain ⟨hd1, _, hpA, hmin⟩ := backLen_bounds_and_mem hq
  refine arcLen_eq_of_isFirst hpA hd1 ?_ fun k hk1 hk2 => ?_
  · rw [prevActive, sub_add_cancel]
    exact hq
  · have heq : prevActive A q + Fin.ofNat n k = q - Fin.ofNat n (backLen A q - k) := by
      rw [prevActive, ofNat_sub_add_of_le (le_of_lt hk2), sub_add_eq_sub_sub, sub_add_cancel]
    rw [heq]
    exact hmin (backLen A q - k) (by omega) (by omega)

@[simp] theorem nextActive_prevActive {n : ℕ} [NeZero n] {A : Finset (Fin n)} {q : Fin n}
    (hq : q ∈ A) :
    nextActive A (prevActive A q) = q := by
  rw [nextActive, arcLen_prevActive_eq hq, prevActive, sub_add_cancel]

theorem prevActive_ne_self_of_two_le_card {n : ℕ} [NeZero n] {A : Finset (Fin n)}
    (hcard : 2 ≤ A.card) {q : Fin n} (hq : q ∈ A) :
    prevActive A q ≠ q := by
  intro heq
  have hnext : nextActive A q = q := by
    have := nextActive_prevActive hq
    rwa [heq] at this
  obtain ⟨hd1, hdn, _, hmin⟩ := arcLen_bounds_and_mem hq
  have hd_eq_n : arcLen A q = n := by
    have h0 : Fin.ofNat n (arcLen A q) = 0 := add_left_cancel (hnext.trans (add_zero q).symm)
    have hmod : arcLen A q % n = 0 := congrArg Fin.val h0
    rcases lt_or_eq_of_le hdn with hlt | h_eq
    · have := Nat.mod_eq_of_lt hlt
      omega
    · exact h_eq
  have herase_pos : 0 < (A.erase q).card := by
    have := Finset.card_erase_add_one hq
    omega
  obtain ⟨x, hx_erase⟩ := Finset.card_pos.mp herase_pos
  have hxq : x ≠ q := Finset.ne_of_mem_erase hx_erase
  have hxA : x ∈ A := Finset.mem_of_mem_erase hx_erase
  let k := (x - q).val
  have hkx : q + Fin.ofNat n k = x := by
    have hval : Fin.ofNat n k = x - q := Fin.ext (Nat.mod_eq_of_lt (x - q).isLt)
    rw [hval, add_sub_cancel]
  have hk_pos : 1 ≤ k := by
    by_contra hk0
    have h0 : k = 0 := by omega
    apply hxq
    rw [← hkx, h0]
    change q + 0 = q
    exact add_zero q
  exact hmin k hk_pos (hd_eq_n.symm ▸ (x - q).isLt) (hkx ▸ hxA)

/-- Surviving active nodes after a two-hop comparison phase on active set `A` with temporary
identifier assignment `tidMap`: nodes `r ∈ A` whose predecessor `q = prevActive A r` is a strict
local peak (`tidMap (prevActive A q) < tidMap q ∧ tidMap r < tidMap q`). -/
@[expose] def petersonSurvivors {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (A : Finset (Fin n)) (tidMap : Fin n → U) : Finset (Fin n) :=
  A.filter fun r =>
    tidMap (prevActive A (prevActive A r)) < tidMap (prevActive A r) ∧
      tidMap r < tidMap (prevActive A r)

/-- **Strict per-phase active-node halving (`petersonSurvivors_card_halving`).**
Adjacent active nodes cannot both be strict peaks, so `r` and `prevActive A r` for
`r ∈ petersonSurvivors A tidMap` form disjoint subsets of `A`, giving
`2 * (petersonSurvivors A tidMap).card ≤ A.card`. -/
theorem petersonSurvivors_card_halving {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (A : Finset (Fin n)) (tidMap : Fin n → U) :
    2 * (petersonSurvivors A tidMap).card ≤ A.card := by
  let S := petersonSurvivors A tidMap
  let P := S.image (prevActive A)
  have hSP_sub : S ∪ P ⊆ A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxP
    · exact (Finset.mem_filter.mp hxS).1
    · rcases Finset.mem_image.mp hxP with ⟨r, hrS, rfl⟩
      exact prevActive_mem (Finset.mem_filter.mp hrS).1
  have hSP_disj : Disjoint S P := by
    refine Finset.disjoint_left.mpr fun r₁ hr₁ hr₂ => ?_
    rcases Finset.mem_image.mp hr₂ with ⟨r₂, hr₂S, hprev_eq⟩
    have h1 := (Finset.mem_filter.mp hr₁).2
    have h2 := (Finset.mem_filter.mp hr₂S).2
    -- `hprev_eq : prevActive A r₂ = r₁`, so `h2.1` says `tidMap (prevActive A r₁) < tidMap r₁`,
    -- contradicting `h1.2 : tidMap r₁ < tidMap (prevActive A r₁)`!
    rw [hprev_eq] at h2
    exact lt_asymm h1.2 h2.1
  have hP_card : P.card = S.card := by
    refine Finset.card_image_of_injOn fun r₁ hr₁ r₂ hr₂ heq => ?_
    have hA₁ : r₁ ∈ A := (Finset.mem_filter.mp hr₁).1
    have hA₂ : r₂ ∈ A := (Finset.mem_filter.mp hr₂).1
    have h := congrArg (nextActive A) heq
    rwa [nextActive_prevActive hA₁, nextActive_prevActive hA₂] at h
  have hle := Finset.card_le_card hSP_sub
  rw [Finset.card_union_of_disjoint hSP_disj, hP_card] at hle
  dsimp only [S] at hle
  omega

/-- Global maximum preservation and nonemptiness of `petersonSurvivors A tidMap`: when `2 ≤ A.card`
and `tidMap` is injective on `A`, the node `r* = nextActive A q*` immediately clockwise of the
unique `tidMap`-maximizer `q* ∈ A` survives with new temporary identifier `tidMap q*`, and the
updated temporary identifiers remain injective on `petersonSurvivors A tidMap`. -/
private theorem petersonSurvivors_nonempty_and_max {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {A : Finset (Fin n)} (hcard : 2 ≤ A.card) {tidMap : Fin n → U}
    (hinj : Set.InjOn tidMap A) :
    let S := petersonSurvivors A tidMap
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
  have hrS : rStar ∈ S := by
    refine Finset.mem_filter.mpr ⟨hrA, ?_, ?_⟩
    · rwa [hprev_r]
    · rwa [hprev_r]
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
structure PetersonPhaseState (n : ℕ) (U : Type*) where
  /-- Active node set `A_k` at phase `k`. -/
  active : Finset (Fin n)
  /-- Temporary identifier assignment on `Fin n` (meaningful on `active`). -/
  tidMap : Fin n → U

/-- Phase-by-phase combinatorial evolution of Peterson's algorithm (stabilizing once
`active.card ≤ 1`). -/
@[expose] def petersonPhase {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) : ℕ → PetersonPhaseState n U
  | 0 => ⟨Finset.univ, uid⟩
  | k + 1 =>
    let st := petersonPhase uid k
    if 2 ≤ st.active.card then
      ⟨petersonSurvivors st.active st.tidMap, fun r => st.tidMap (prevActive st.active r)⟩
    else st

/-- Count how many elimination phases (`2 ≤ active.card`) occur within the first `fuel` steps. -/
@[expose] def petersonPhasesAux {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    petersonPhasesAux uid k + if 2 ≤ (petersonPhase uid k).active.card then 1 else 0

/-- Total number of elimination phases (`2 ≤ active.card`) executed by Peterson's algorithm on
`uid` before `active.card = 1`. -/
@[expose] def petersonPhases {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) : ℕ :=
  petersonPhasesAux uid n

/-- **Per-phase halving (`peterson_phase_halving`).** -/
theorem peterson_phase_halving {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) (k : ℕ) (h2 : 2 ≤ (petersonPhase uid k).active.card) :
    2 * (petersonPhase uid (k + 1)).active.card ≤ (petersonPhase uid k).active.card := by
  simp only [petersonPhase, h2, ↓reduceIte]
  exact petersonSurvivors_card_halving (petersonPhase uid k).active (petersonPhase uid k).tidMap

private theorem petersonPhase_inv {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    let hne_univ : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, Finset.mem_univ _⟩
    let maxUid := (Finset.univ.image uid).max' (hne_univ.image uid)
    ∀ k : ℕ,
      let st := petersonPhase uid k
      st.active.Nonempty ∧
      Set.InjOn st.tidMap st.active ∧
      (∃ q ∈ st.active, st.tidMap q = maxUid ∧ ∀ x ∈ st.active, st.tidMap x ≤ maxUid) := by
  intro hne_univ maxUid k
  induction k with
  | zero =>
    dsimp only [petersonPhase]
    rcases Finset.mem_image.mp (Finset.max'_mem (Finset.univ.image uid) (hne_univ.image uid)) with
      ⟨iStar, _, hiStar⟩
    exact ⟨hne_univ, huid.injOn, ⟨iStar, Finset.mem_univ iStar, hiStar, fun x _ =>
      Finset.le_max' _ (uid x) (Finset.mem_image_of_mem uid (Finset.mem_univ x))⟩⟩
  | succ k ih =>
    obtain ⟨hne_k, hinj_k, hmax_k⟩ := ih
    dsimp only [petersonPhase]
    by_cases h2 : 2 ≤ (petersonPhase uid k).active.card
    · simp only [h2, ↓reduceIte]
      obtain ⟨hne', hinj', hmax'⟩ := petersonSurvivors_nonempty_and_max h2 hinj_k
      exact ⟨hne', hinj', hmax' maxUid hmax_k⟩
    · simp only [h2, ↓reduceIte]
      exact ⟨hne_k, hinj_k, hmax_k⟩

/-- Exponential halving invariant: if phases `0, …, k - 1` all have `2 ≤ active.card`, then
`2 ^ k * (petersonPhase uid k).active.card ≤ n`. -/
private theorem pow_two_mul_phase_card_le {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) :
    ∀ k : ℕ, (∀ j < k, 2 ≤ (petersonPhase uid j).active.card) →
      2 ^ k * (petersonPhase uid k).active.card ≤ n := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [pow_zero, one_mul, petersonPhase, Finset.card_univ, Fintype.card_fin, le_rfl]
  | succ k ih =>
    intro hall
    have hk2 : 2 ≤ (petersonPhase uid k).active.card := hall k (Nat.lt_succ_self k)
    have hhalve := peterson_phase_halving uid k hk2
    have hprev := ih fun j hj => hall j (Nat.lt_succ_of_lt hj)
    calc 2 ^ (k + 1) * (petersonPhase uid (k + 1)).active.card
        = 2 ^ k * (2 * (petersonPhase uid (k + 1)).active.card) := by ring
      _ ≤ 2 ^ k * (petersonPhase uid k).active.card := Nat.mul_le_mul_left (2 ^ k) hhalve
      _ ≤ n := hprev

private theorem phase_stable_of_lt_two {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) {k₀ : ℕ} (h1 : ¬ 2 ≤ (petersonPhase uid k₀).active.card) :
    ∀ m, k₀ ≤ m → petersonPhase uid m = petersonPhase uid k₀ := by
  suffices ∀ d, petersonPhase uid (k₀ + d) = petersonPhase uid k₀ by
    intro m hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact this d
  intro d
  induction d with
  | zero => simp only [add_zero]
  | succ d ih =>
    rw [← add_assoc, petersonPhase, ih]
    simp only [h1, ↓reduceIte]

/-- **Logarithmic phase bound (`peterson_phases_le_log`).**
For any injective `uid : Fin n → U`, the number of elimination phases satisfies
`petersonPhases uid ≤ Nat.log 2 n`, and at phase `K = petersonPhases uid` (as well as at
`Nat.log 2 n`), exactly `1` active processor remains! -/
theorem peterson_phases_le_log {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    petersonPhases uid ≤ Nat.log 2 n ∧
      (petersonPhase uid (petersonPhases uid)).active.card = 1 ∧
      (petersonPhase uid (Nat.log 2 n)).active.card = 1 := by
  -- First show `¬ 2 ≤ (petersonPhase uid (Nat.log 2 n)).active.card`!
  have hstop_log : ¬ 2 ≤ (petersonPhase uid (Nat.log 2 n)).active.card := by
    intro h2_log
    have hall : ∀ j < Nat.log 2 n + 1, 2 ≤ (petersonPhase uid j).active.card := by
      intro j hj
      by_contra hnot2
      have heq := phase_stable_of_lt_two uid hnot2 (Nat.log 2 n) (by omega)
      rw [← heq] at hnot2
      exact hnot2 h2_log
    have hpow := pow_two_mul_phase_card_le uid (Nat.log 2 n + 1) hall
    have hne := (petersonPhase_inv huid (Nat.log 2 n + 1)).1
    have hcard_pos : 1 ≤ (petersonPhase uid (Nat.log 2 n + 1)).active.card :=
      Finset.card_pos.mpr hne
    have h2pow : 2 ^ (Nat.log 2 n + 1) ≤ n := by
      calc 2 ^ (Nat.log 2 n + 1)
          ≤ 2 ^ (Nat.log 2 n + 1) * (petersonPhase uid (Nat.log 2 n + 1)).active.card :=
            Nat.le_mul_of_pos_right _ hcard_pos
        _ ≤ n := hpow
    have hle := Nat.le_log_of_pow_le (by omega) h2pow
    omega
  have hlog_lt_n : Nat.log 2 n < n := by
    have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hpow := Nat.pow_log_le_self 2 (NeZero.ne n)
    have hlt_pow : Nat.log 2 n < 2 ^ Nat.log 2 n := Nat.lt_two_pow_self
    omega
  -- Characterize `petersonPhasesAux uid m` as a prefix of `2 ≤ active.card` steps:
  have haux_spec : ∀ m : ℕ,
      petersonPhasesAux uid m ≤ m ∧
      (∀ j < petersonPhasesAux uid m, 2 ≤ (petersonPhase uid j).active.card) ∧
      (petersonPhasesAux uid m < m →
        ¬ 2 ≤ (petersonPhase uid (petersonPhasesAux uid m)).active.card) := by
    intro m
    induction m with
    | zero =>
      simp only [petersonPhasesAux]
      exact ⟨le_rfl, fun _ hj => by omega, fun h => by omega⟩
    | succ m ih =>
      obtain ⟨hKm, hall, hstop⟩ := ih
      simp only [petersonPhasesAux]
      by_cases hm2 : 2 ≤ (petersonPhase uid m).active.card
      · have hK_eq_m : petersonPhasesAux uid m = m := by
          by_contra hne
          have hnot := hstop (lt_of_le_of_ne hKm hne)
          have hst := phase_stable_of_lt_two uid hnot m (by omega)
          rw [← hst] at hnot
          exact hnot hm2
        simp only [hm2, ↓reduceIte, hK_eq_m]
        refine ⟨le_rfl, fun j hj => ?_, fun h => by omega⟩
        rcases eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hlt
        · exact hm2
        · exact hall j (hK_eq_m.symm ▸ hlt)
      · simp only [hm2, ↓reduceIte, add_zero]
        refine ⟨by omega, hall, fun _ => ?_⟩
        rcases eq_or_lt_of_le hKm with heq | hlt
        · rwa [heq]
        · exact hstop hlt
  obtain ⟨hKn, hallK, hstopK⟩ := haux_spec n
  dsimp only [petersonPhases]
  have hK_le_log : petersonPhasesAux uid n ≤ Nat.log 2 n := by
    by_contra hgt
    exact hstop_log (hallK (Nat.log 2 n) (by omega))
  have hnot2_K : ¬ 2 ≤ (petersonPhase uid (petersonPhasesAux uid n)).active.card :=
    hstopK (lt_of_le_of_lt hK_le_log hlog_lt_n)
  have hcard_K : (petersonPhase uid (petersonPhasesAux uid n)).active.card = 1 := by
    have hpos : 1 ≤ (petersonPhase uid (petersonPhasesAux uid n)).active.card :=
      Finset.card_pos.mpr (petersonPhase_inv huid (petersonPhasesAux uid n)).1
    omega
  have hcard_log : (petersonPhase uid (Nat.log 2 n)).active.card = 1 := by
    rw [phase_stable_of_lt_two uid hnot2_K (Nat.log 2 n) hK_le_log]
    exact hcard_K
  exact ⟨hK_le_log, hcard_K, hcard_log⟩

/-! ### Canonical wave execution across passive relays and active nodes -/

/-- Points `p + Fin.ofNat n k` on half-open clockwise arcs `0 ≤ k < arcLen A p` (`p ∈ A`) are
pairwise distinct across `A`. -/
private theorem arc_point_inj {n : ℕ} [NeZero n] {A : Finset (Fin n)}
    {p₁ p₂ : Fin n} (hp₁ : p₁ ∈ A) (hp₂ : p₂ ∈ A)
    {k₁ k₂ : ℕ} (hk₁ : k₁ < arcLen A p₁) (hk₂ : k₂ < arcLen A p₂)
    (heq : p₁ + Fin.ofNat n k₁ = p₂ + Fin.ofNat n k₂) :
    p₁ = p₂ ∧ k₁ = k₂ := by
  have hofNat_add : ∀ a b : ℕ, Fin.ofNat n (a + b) = Fin.ofNat n a + Fin.ofNat n b := fun a b =>
    Fin.ext (Nat.add_mod a b n)
  rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
  · exfalso
    have hcast : Fin.ofNat n k₂ = Fin.ofNat n k₁ + Fin.ofNat n (k₂ - k₁) := by
      rw [← hofNat_add, show k₁ + (k₂ - k₁) = k₂ by omega]
    have hp₁_eq : p₁ = p₂ + Fin.ofNat n (k₂ - k₁) := by
      have h : Fin.ofNat n k₁ + p₁ = Fin.ofNat n k₁ + (p₂ + Fin.ofNat n (k₂ - k₁)) := by
        calc Fin.ofNat n k₁ + p₁ = p₁ + Fin.ofNat n k₁ := add_comm _ _
          _ = p₂ + Fin.ofNat n k₂ := heq
          _ = p₂ + (Fin.ofNat n k₁ + Fin.ofNat n (k₂ - k₁)) := by rw [hcast]
          _ = Fin.ofNat n k₁ + (p₂ + Fin.ofNat n (k₂ - k₁)) := by abel
      exact add_left_cancel h
    exact (arcLen_bounds_and_mem hp₂).2.2.2 (k₂ - k₁) (by omega) (by omega) (hp₁_eq ▸ hp₁)
  · exact ⟨add_right_cancel heq, rfl⟩
  · exfalso
    have hcast : Fin.ofNat n k₁ = Fin.ofNat n k₂ + Fin.ofNat n (k₁ - k₂) := by
      rw [← hofNat_add, show k₂ + (k₁ - k₂) = k₁ by omega]
    have hp₂_eq : p₂ = p₁ + Fin.ofNat n (k₁ - k₂) := by
      have h : Fin.ofNat n k₂ + (p₁ + Fin.ofNat n (k₁ - k₂)) = Fin.ofNat n k₂ + p₂ := by
        calc Fin.ofNat n k₂ + (p₁ + Fin.ofNat n (k₁ - k₂))
            = p₁ + (Fin.ofNat n k₂ + Fin.ofNat n (k₁ - k₂)) := by abel
          _ = p₁ + Fin.ofNat n k₁ := by rw [← hcast]
          _ = p₂ + Fin.ofNat n k₂ := heq
          _ = Fin.ofNat n k₂ + p₂ := add_comm _ _
      exact (add_left_cancel h).symm
    exact (arcLen_bounds_and_mem hp₁).2.2.2 (k₁ - k₂) (by omega) (by omega) (hp₂_eq ▸ hp₂)

/-- **Single-wave execution lemma (`mtr_wave`).**
Starting from any configuration `cfg₀` where passive nodes `i ∉ A` are `.relay` and channels hold
`[payload i]` on `i ∈ A` and `[]` on `i ∉ A`, relaying every message across `Aᶜ` and delivering to
every `q ∈ A` is a valid `LTS.MTr` trace emitting `(n - A.card) + ∑ q ∈ A, out_q.sent.length`
messages and leaving each `q ∈ A` in `out_q.nextNode` with channel `out_q.sent`! -/
private theorem mtr_wave {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {A : Finset (Fin n)} (hA : A.Nonempty) (payload : Fin n → PetersonMsg U)
    {cfg₀ : PetersonConfig n U}
    (hnode₀ : ∀ i, i ∉ A → cfg₀.node i = .relay)
    (hchan₀ : ∀ i, cfg₀.chan i = if i ∈ A then [payload i] else []) :
    ∃ (sched : List (Fin n)) (cfg₂ : PetersonConfig n U),
      (petersonLTS n U).MTr cfg₀ sched cfg₂ ∧
      petersonEmittedMsgs cfg₀ sched =
        (n - A.card) +
          ∑ q ∈ A, (petersonRecv (cfg₀.node q) (payload (prevActive A q))).sent.length ∧
      (∀ i, cfg₂.node i =
        if i ∈ A then (petersonRecv (cfg₀.node i) (payload (prevActive A i))).nextNode
        else .relay) ∧
      (∀ i, cfg₂.chan i =
        if i ∈ A then (petersonRecv (cfg₀.node i) (payload (prevActive A i))).sent
        else []) := by
  have hofNat_add : ∀ a b : ℕ, Fin.ofNat n (a + b) = Fin.ofNat n a + Fin.ofNat n b := fun a b =>
    Fin.ext (Nat.add_mod a b n)
  -- Stage 1a: advance each `p ∈ A` from `prog p = 0` to `prog p = arcLen A p - 1` across relays.
  have hstage1a : ∀ rem : ℕ, ∀ (prog : Fin n → ℕ) (cfg : PetersonConfig n U),
      (∑ p ∈ A, (arcLen A p - 1 - prog p) = rem) →
      (∀ p ∈ A, prog p ≤ arcLen A p - 1) →
      cfg.node = cfg₀.node →
      (∀ p ∈ A, cfg.chan (p + Fin.ofNat n (prog p)) = [payload p]) →
      (∀ e : Fin n, (∀ p ∈ A, e ≠ p + Fin.ofNat n (prog p)) → cfg.chan e = []) →
      ∃ (s₁ : List (Fin n)) (cfg₁ : PetersonConfig n U),
        (petersonLTS n U).MTr cfg s₁ cfg₁ ∧
        petersonEmittedMsgs cfg s₁ = rem ∧
        cfg₁.node = cfg₀.node ∧
        (∀ e : Fin n, cfg₁.chan e =
          if e + 1 ∈ A then [payload (prevActive A (e + 1))] else []) := by
    intro rem
    induction rem with
    | zero =>
      intro prog cfg hrem hprog_le hnode hchan_at hchan_else
      have hprog_done : ∀ p ∈ A, prog p = arcLen A p - 1 := by
        rw [Finset.sum_eq_zero_iff] at hrem
        intro p hp
        have h0 := hrem p hp
        have hle := hprog_le p hp
        omega
      refine ⟨[], cfg, LTS.MTr.refl, rfl, hnode, fun e => ?_⟩
      by_cases heA : e + 1 ∈ A
      · simp only [heA, ↓reduceIte]
        let p := prevActive A (e + 1)
        have hpA : p ∈ A := prevActive_mem heA
        have hd1 : 1 ≤ arcLen A p := (arcLen_bounds_and_mem hpA).1
        have he_eq : e = p + Fin.ofNat n (prog p) := by
          have hnext : p + Fin.ofNat n (arcLen A p) = e + 1 := nextActive_prevActive heA
          have hsplit : Fin.ofNat n (arcLen A p) = Fin.ofNat n (prog p) + 1 := by
            rw [hprog_done p hpA]
            change Fin.ofNat n (arcLen A p) = Fin.ofNat n (arcLen A p - 1) + Fin.ofNat n 1
            rw [← hofNat_add, show arcLen A p - 1 + 1 = arcLen A p by omega]
          rw [hsplit, ← add_assoc] at hnext
          exact (add_right_cancel hnext).symm
        conv_lhs => rw [he_eq, hchan_at p hpA]
      · simp only [heA, ↓reduceIte]
        refine hchan_else e fun p hp hcontra => heA ?_
        have hd1 : 1 ≤ arcLen A p := (arcLen_bounds_and_mem hp).1
        have he1 : e + 1 = nextActive A p := by
          rw [hcontra, hprog_done p hp, add_assoc]
          change p + (Fin.ofNat n (arcLen A p - 1) + Fin.ofNat n 1) = p + Fin.ofNat n (arcLen A p)
          rw [← hofNat_add, show arcLen A p - 1 + 1 = arcLen A p by omega]
        rw [he1]
        exact nextActive_mem hp
    | succ r ih =>
      intro prog cfg hrem hprog_le hnode hchan_at hchan_else
      have hex_p : ∃ p ∈ A, prog p < arcLen A p - 1 := by
        by_contra hall
        simp only [not_exists, not_and, not_lt] at hall
        have h0 : ∑ p ∈ A, (arcLen A p - 1 - prog p) = 0 :=
          Finset.sum_eq_zero fun p hp => by have := hall p hp; omega
        omega
      obtain ⟨p, hpA, hp_lt⟩ := hex_p
      let k := prog p
      let target := p + Fin.ofNat n (k + 1)
      have htarget_pred : target - 1 = p + Fin.ofNat n k := by
        dsimp only [target]
        rw [hofNat_add, ← add_assoc]
        exact add_sub_cancel_right _ 1
      have htarget_notA : target ∉ A :=
        (arcLen_bounds_and_mem hpA).2.2.2 (k + 1) (by omega) (by omega)
      have htarget_node : cfg.node target = .relay := by
        rw [hnode]
        exact hnode₀ target htarget_notA
      have htarget_empty : cfg.chan target = [] := by
        refine hchan_else target fun p' hp' heq => ?_
        have hp'_lt : prog p' < arcLen A p' := by
          have := hprog_le p' hp'
          have := (arcLen_bounds_and_mem hp').1
          omega
        obtain ⟨rfl, hk_eq⟩ := arc_point_inj hpA hp' (by omega) hp'_lt heq
        change k + 1 = k at hk_eq
        omega
      have ht_ne_pred : target ≠ target - 1 := fun h => by
        have h1 := hchan_at p hpA
        rw [← htarget_pred, ← h, htarget_empty] at h1
        cases h1
      have hchan_pred : cfg.chan (target - 1) = [payload p] := by
        rw [htarget_pred, hchan_at p hpA]
      have htr : (petersonLTS n U).Tr cfg target (petersonStep target cfg) :=
        ⟨by rw [hchan_pred]; exact List.cons_ne_nil _ _, rfl⟩
      have hmsgs1 : petersonStepMsgs target cfg = 1 := by
        simp only [petersonStepMsgs, hchan_pred, htarget_node, petersonRecv, List.length_singleton]
      let cfg' := petersonStep target cfg
      let prog' := Function.update prog p (k + 1)
      have hnode' : cfg'.node = cfg₀.node := by
        ext i
        simp only [cfg', petersonStep, hchan_pred, htarget_node, petersonRecv]
        by_cases hi : i = target
        · rw [hi, Function.update_self, hnode₀ target htarget_notA]
        · rw [Function.update_of_ne hi, hnode]
      have hrem' : ∑ x ∈ A, (arcLen A x - 1 - prog' x) = r := by
        have h1 := Finset.add_sum_erase A (fun x => arcLen A x - 1 - prog' x) hpA
        have h2 := Finset.add_sum_erase A (fun x => arcLen A x - 1 - prog x) hpA
        have herase : ∑ x ∈ A.erase p, (arcLen A x - 1 - prog' x) =
            ∑ x ∈ A.erase p, (arcLen A x - 1 - prog x) :=
          Finset.sum_congr rfl fun x hx => by
            simp only [prog', Function.update_of_ne (Finset.ne_of_mem_erase hx)]
        have hp_new : arcLen A p - 1 - prog' p + 1 = arcLen A p - 1 - prog p := by
          simp only [prog', Function.update_self, k]
          omega
        rw [herase] at h1
        linarith
      have hprog'_le : ∀ x ∈ A, prog' x ≤ arcLen A x - 1 := by
        intro x hx
        by_cases hxp : x = p
        · rw [hxp]; simp only [prog', Function.update_self]; omega
        · simp only [prog', Function.update_of_ne hxp]; exact hprog_le x hx
      have hchan'_at : ∀ x ∈ A, cfg'.chan (x + Fin.ofNat n (prog' x)) = [payload x] := by
        intro x hx
        simp only [cfg', petersonStep, hchan_pred, htarget_node, petersonRecv]
        by_cases hxp : x = p
        · rw [hxp]
          simp only [prog', Function.update_self]
          change Function.update (Function.update cfg.chan (target - 1) []) target
            (Function.update cfg.chan (target - 1) [] target ++ [payload p]) target = [payload p]
          rw [Function.update_self, Function.update_of_ne ht_ne_pred, htarget_empty,
            List.nil_append]
        · simp only [prog', Function.update_of_ne hxp]
          have hne_t : x + Fin.ofNat n (prog x) ≠ target := fun h => by
            have hx_lt : prog x < arcLen A x := by
              have := hprog_le x hx; have := (arcLen_bounds_and_mem hx).1; omega
            exact hxp (arc_point_inj hx hpA hx_lt (by omega) h).1
          have hne_tp : x + Fin.ofNat n (prog x) ≠ target - 1 := fun h => by
            rw [htarget_pred] at h
            have hx_lt : prog x < arcLen A x := by
              have := hprog_le x hx; have := (arcLen_bounds_and_mem hx).1; omega
            exact hxp (arc_point_inj hx hpA hx_lt (by omega) h).1
          rw [Function.update_of_ne hne_t, Function.update_of_ne hne_tp, hchan_at x hx]
      have hchan'_else : ∀ e : Fin n,
          (∀ x ∈ A, e ≠ x + Fin.ofNat n (prog' x)) → cfg'.chan e = [] := by
        intro e he_all
        simp only [cfg', petersonStep, hchan_pred, htarget_node, petersonRecv]
        have he_ne_t : e ≠ target := by
          have := he_all p hpA
          simpa only [prog', Function.update_self] using this
        rw [Function.update_of_ne he_ne_t]
        by_cases he_tp : e = target - 1
        · rw [he_tp, Function.update_self]
        · rw [Function.update_of_ne he_tp]
          refine hchan_else e fun x hx hx_eq => ?_
          by_cases hxp : x = p
          · rw [hxp, ← htarget_pred] at hx_eq
            exact he_tp hx_eq
          · have hne := he_all x hx
            simp only [prog', Function.update_of_ne hxp] at hne
            exact hne hx_eq
      obtain ⟨s_rest, cfg₁, hmtr_rest, hmsgs_rest, hnode₁, hchan₁⟩ :=
        ih prog' cfg' hrem' hprog'_le hnode' hchan'_at hchan'_else
      refine ⟨target :: s_rest, cfg₁, LTS.MTr.stepL htr hmtr_rest, ?_, hnode₁, hchan₁⟩
      simp only [petersonEmittedMsgs, hmsgs1]
      dsimp only [cfg'] at hmsgs_rest
      omega
  -- Instantiate Stage 1a with `prog = fun _ => 0`:
  have hrem0 : ∑ p ∈ A, (arcLen A p - 1 - 0) = n - A.card := by
    have hsum1 : ∑ p ∈ A, (arcLen A p - 1 + 1) = ∑ p ∈ A, arcLen A p :=
      Finset.sum_congr rfl fun p hp => by have := (arcLen_bounds_and_mem hp).1; omega
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, sum_arcLen_eq hA] at hsum1
    have hA_le : A.card ≤ n := by
      have := Finset.card_le_univ A
      rwa [Fintype.card_fin] at this
    simp only [Nat.sub_zero]
    omega
  obtain ⟨s₁, cfg₁, hmtr₁, hmsgs₁, hnode₁, hchan₁⟩ :=
    hstage1a (n - A.card) (fun _ => 0) cfg₀ hrem0 (fun _ _ => Nat.zero_le _) rfl
      (fun p hp => by
        change cfg₀.chan (p + 0) = [payload p]
        rw [add_zero, hchan₀ p]
        simp only [hp, ↓reduceIte])
      (fun e he => by
        have he_notA : e ∉ A := fun h => he e h (by change e = e + 0; exact (add_zero e).symm)
        rw [hchan₀ e]
        simp only [he_notA, ↓reduceIte])
  -- Stage 1b: deliver to each active node `q ∈ A` one by one (`rem = (A \ Done).card`):
  let outAt (q : Fin n) := petersonRecv (cfg₀.node q) (payload (prevActive A q))
  have hstage1b : ∀ rem : ℕ, ∀ (Done : Finset (Fin n)) (cfg : PetersonConfig n U),
      Done ⊆ A →
      (A \ Done).card = rem →
      (∀ i, cfg.node i = if i ∈ Done then (outAt i).nextNode else cfg₀.node i) →
      (∀ e, cfg.chan e =
        (if e + 1 ∈ A \ Done then [payload (prevActive A (e + 1))] else []) ++
          (if e ∈ Done then (outAt e).sent else [])) →
      ∃ (s₂ : List (Fin n)) (cfg₂ : PetersonConfig n U),
        (petersonLTS n U).MTr cfg s₂ cfg₂ ∧
        petersonEmittedMsgs cfg s₂ = ∑ q ∈ A \ Done, (outAt q).sent.length ∧
        (∀ i, cfg₂.node i = if i ∈ A then (outAt i).nextNode else .relay) ∧
        (∀ e, cfg₂.chan e = if e ∈ A then (outAt e).sent else []) := by
    intro rem
    induction rem with
    | zero =>
      intro Done cfg hsub hcard0 hnode_d hchan_d
      have hDone_eq : Done = A := by
        have hemp : A \ Done = ∅ := Finset.card_eq_zero.mp hcard0
        exact Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.mp hemp)
      rw [hDone_eq] at hnode_d hchan_d ⊢
      refine ⟨[], cfg, LTS.MTr.refl, ?_, ?_, ?_⟩
      · simp only [Finset.sdiff_self, Finset.sum_empty, petersonEmittedMsgs]
      · intro i
        rw [hnode_d i]
        by_cases hi : i ∈ A
        · simp only [hi, ↓reduceIte]
        · simp only [hi, ↓reduceIte, hnode₀ i hi]
      · intro e
        rw [hchan_d e]
        simp only [Finset.sdiff_self, Finset.notMem_empty, ↓reduceIte, List.nil_append]
    | succ r ih =>
      intro Done cfg hsub hcard_r hnode_d hchan_d
      obtain ⟨q, hq_sdiff⟩ := Finset.card_pos.mp (by omega : 0 < (A \ Done).card)
      obtain ⟨hqA, hq_notDone⟩ := Finset.mem_sdiff.mp hq_sdiff
      have hq_pred_chan : cfg.chan (q - 1) =
          payload (prevActive A q) :: (if q - 1 ∈ Done then (outAt (q - 1)).sent else []) := by
        rw [hchan_d (q - 1), sub_add_cancel]
        simp only [hq_sdiff, ↓reduceIte, List.singleton_append]
      have hq_node : cfg.node q = cfg₀.node q := by
        rw [hnode_d q]
        simp only [hq_notDone, ↓reduceIte]
      have htr : (petersonLTS n U).Tr cfg q (petersonStep q cfg) :=
        ⟨by rw [hq_pred_chan]; exact List.cons_ne_nil _ _, rfl⟩
      have hmsgs_q : petersonStepMsgs q cfg = (outAt q).sent.length := by
        simp only [petersonStepMsgs, hq_pred_chan, hq_node, outAt]
      let Done' := insert q Done
      let cfg' := petersonStep q cfg
      have hsub' : Done' ⊆ A := Finset.insert_subset_iff.mpr ⟨hqA, hsub⟩
      have hsdiff_erase : A \ Done' = (A \ Done).erase q := by
        ext x
        simp only [Done', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, ne_eq]
        tauto
      have hcard' : (A \ Done').card = r := by
        rw [hsdiff_erase]
        have := Finset.card_erase_add_one hq_sdiff
        omega
      have hnode' : ∀ i, cfg'.node i = if i ∈ Done' then (outAt i).nextNode else cfg₀.node i := by
        intro i
        simp only [cfg', petersonStep, hq_pred_chan, hq_node]
        by_cases hi : i = q
        · rw [hi, Function.update_self]
          simp only [Done', Finset.mem_insert_self, ↓reduceIte, outAt]
        · rw [Function.update_of_ne hi, hnode_d i]
          simp only [Done', Finset.mem_insert, hi, false_or]
      have hchan' : ∀ e, cfg'.chan e =
          (if e + 1 ∈ A \ Done' then [payload (prevActive A (e + 1))] else []) ++
            (if e ∈ Done' then (outAt e).sent else []) := by
        intro e
        simp only [cfg', petersonStep, hq_pred_chan, hq_node]
        by_cases heq_q : e = q
        · rw [heq_q, Function.update_self]
          by_cases hq_self : q = q - 1
          · -- `n = 1` case: `q - 1 = q`, `q + 1 = q ∉ A \ Done'`!
            have hq1 : q + 1 = q := by
              have h := congrArg (· + 1) hq_self
              simpa only [sub_add_cancel] using h
            have hnot_sdiff' : q + 1 ∉ A \ Done' := by
              rw [hq1]
              simp only [Done', Finset.mem_sdiff, Finset.mem_insert_self, not_true_eq_false,
                and_false, not_false_eq_true]
            have hqp : q - 1 = q := hq_self.symm
            rw [hqp, Function.update_self]
            simp only [hq_notDone, ↓reduceIte, List.nil_append, hnot_sdiff', Done',
              Finset.mem_insert_self, outAt]
          · rw [Function.update_of_ne hq_self, hchan_d q]
            have hq1_ne : q + 1 ≠ q := fun h => hq_self (eq_sub_of_add_eq h)
            have hsdiff_iff : (q + 1 ∈ A \ Done') ↔ (q + 1 ∈ A \ Done) := by
              rw [hsdiff_erase, Finset.mem_erase]
              exact ⟨fun h => h.2, fun h => ⟨hq1_ne, h⟩⟩
            simp only [hq_notDone, ↓reduceIte, List.append_nil, hsdiff_iff, Done',
              Finset.mem_insert_self, outAt]
        · rw [Function.update_of_ne heq_q]
          by_cases he_pred : e = q - 1
          · rw [he_pred, Function.update_self]
            have he1_not : (q - 1) + 1 ∉ A \ Done' := by
              rw [sub_add_cancel]
              simp only [Done', Finset.mem_sdiff, Finset.mem_insert_self, not_true_eq_false,
                and_false, not_false_eq_true]
            have hmem_iff : (q - 1 ∈ Done') ↔ (q - 1 ∈ Done) := by
              simp only [Done', Finset.mem_insert, show q - 1 ≠ q from he_pred ▸ heq_q, false_or]
            simp only [he1_not, ↓reduceIte, List.nil_append, hmem_iff]
          · rw [Function.update_of_ne he_pred, hchan_d e]
            have he1_ne_q : e + 1 ≠ q := fun h => he_pred (eq_sub_of_add_eq h)
            have hsdiff_iff : (e + 1 ∈ A \ Done') ↔ (e + 1 ∈ A \ Done) := by
              rw [hsdiff_erase, Finset.mem_erase]
              exact ⟨fun h => h.2, fun h => ⟨he1_ne_q, h⟩⟩
            have hmem_iff : (e ∈ Done') ↔ (e ∈ Done) := by
              simp only [Done', Finset.mem_insert, heq_q, false_or]
            simp only [hsdiff_iff, hmem_iff]
      obtain ⟨s_rest, cfg₂, hmtr_rest, hmsgs_rest, hnode₂, hchan₂⟩ :=
        ih Done' cfg' hsub' hcard' hnode' hchan'
      refine ⟨q :: s_rest, cfg₂, LTS.MTr.stepL htr hmtr_rest, ?_, hnode₂, hchan₂⟩
      have hsum_split := Finset.add_sum_erase (A \ Done) (fun x => (outAt x).sent.length) hq_sdiff
      rw [← hsdiff_erase] at hsum_split
      simp only [petersonEmittedMsgs, hmsgs_q]
      dsimp only [cfg'] at hmsgs_rest
      linarith
  -- Combine Stage 1a and Stage 1b:
  obtain ⟨s₂, cfg₂, hmtr₂, hmsgs₂, hnode₂, hchan₂⟩ :=
    hstage1b A.card ∅ cfg₁ (Finset.empty_subset A) (by simp)
      (fun i => by simp only [Finset.notMem_empty, ↓reduceIte, hnode₁])
      (fun e => by simp only [Finset.sdiff_empty, Finset.notMem_empty, ↓reduceIte,
        List.append_nil, hchan₁])
  simp only [Finset.sdiff_empty] at hmsgs₂
  refine ⟨s₁ ++ s₂, cfg₂, hmtr₁.comp (petersonLTS n U) hmtr₂, ?_, hnode₂, hchan₂⟩
  rw [petersonEmittedMsgs_append, petersonExec_of_mtr hmtr₁, hmsgs₁, hmsgs₂]

/-! ### Canonical full-protocol run and main theorems -/

private def IsPhaseStartCfg {n : ℕ} {U : Type*} (st : PetersonPhaseState n U)
    (cfg : PetersonConfig n U) : Prop :=
  (∀ i, cfg.node i = if i ∈ st.active then .active1 (st.tidMap i) else .relay) ∧
  (∀ i, cfg.chan i = if i ∈ st.active then [.hop1 (st.tidMap i)] else [])

/-- One elimination phase (`2 ≤ st.active.card`) takes `IsPhaseStartCfg st` to
`IsPhaseStartCfg st'` while emitting `2 * n - st.active.card + st'.active.card` messages! -/
private theorem mtr_elimination_phase {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {st : PetersonPhaseState n U} {cfg₀ : PetersonConfig n U}
    (hstart : IsPhaseStartCfg st cfg₀) (h2 : 2 ≤ st.active.card)
    (hinj : Set.InjOn st.tidMap st.active) :
    let st' : PetersonPhaseState n U :=
      ⟨petersonSurvivors st.active st.tidMap, fun r => st.tidMap (prevActive st.active r)⟩
    ∃ (sched : List (Fin n)) (cfg₂ : PetersonConfig n U),
      (petersonLTS n U).MTr cfg₀ sched cfg₂ ∧
      petersonEmittedMsgs cfg₀ sched = 2 * n - st.active.card + st'.active.card ∧
      IsPhaseStartCfg st' cfg₂ := by
  intro st'
  have hA_ne : st.active.Nonempty := Finset.card_pos.mp (by omega)
  have hA_le_n : st.active.card ≤ n := by
    have := Finset.card_le_univ st.active
    rwa [Fintype.card_fin] at this
  -- Pass 1 (`hop1` wave):
  obtain ⟨w₁, cfg₁, hmtr₁, hmsgs₁, hnode₁, hchan₁⟩ :=
    mtr_wave hA_ne (fun i => PetersonMsg.hop1 (st.tidMap i))
      (fun i hi => by rw [hstart.1 i]; simp only [hi, ↓reduceIte])
      hstart.2
  have hpass1_out : ∀ q ∈ st.active,
      petersonRecv (cfg₀.node q) (.hop1 (st.tidMap (prevActive st.active q))) =
        ⟨.active2 (st.tidMap q) (st.tidMap (prevActive st.active q)),
          [.hop2 (st.tidMap (prevActive st.active q))]⟩ := by
    intro q hq
    have hp_ne : prevActive st.active q ≠ q := prevActive_ne_self_of_two_le_card h2 hq
    have htid_ne : st.tidMap (prevActive st.active q) ≠ st.tidMap q := fun h =>
      hp_ne (hinj (prevActive_mem hq) hq h)
    rw [hstart.1 q]
    simp only [hq, ↓reduceIte, petersonRecv, htid_ne]
  have hmsgs₁_eq : petersonEmittedMsgs cfg₀ w₁ = n := by
    have hsum : (∑ q ∈ st.active,
        (petersonRecv (cfg₀.node q) (.hop1 (st.tidMap (prevActive st.active q)))).sent.length) =
        st.active.card := by
      calc _ = ∑ _q ∈ st.active, 1 :=
            Finset.sum_congr rfl fun q hq => by rw [hpass1_out q hq]; rfl
        _ = st.active.card := by simp only [Finset.sum_const, smul_eq_mul, mul_one]
    rw [hmsgs₁, hsum]
    omega
  -- Pass 2 (`hop2` wave):
  obtain ⟨w₂, cfg₂, hmtr₂, hmsgs₂, hnode₂, hchan₂⟩ :=
    mtr_wave hA_ne (fun q => PetersonMsg.hop2 (st.tidMap (prevActive st.active q)))
      (fun i hi => by rw [hnode₁ i]; simp only [hi, ↓reduceIte])
      (fun i => by
        rw [hchan₁ i]
        by_cases hi : i ∈ st.active
        · simp only [hi, ↓reduceIte, hpass1_out i hi]
        · simp only [hi, ↓reduceIte])
  have hpass2_out : ∀ r ∈ st.active,
      petersonRecv (cfg₁.node r)
        (.hop2 (st.tidMap (prevActive st.active (prevActive st.active r)))) =
      if r ∈ st'.active then ⟨.active1 (st'.tidMap r), [.hop1 (st'.tidMap r)]⟩
      else ⟨.relay, []⟩ := by
    intro r hr
    rw [hnode₁ r]
    simp only [hr, ↓reduceIte]
    rw [hpass1_out r hr]
    simp only [petersonRecv]
    by_cases hrS : r ∈ st'.active
    · have hpeak := (Finset.mem_filter.mp hrS).2
      simp only [hrS, hpeak, and_self, ↓reduceIte, st']
    · have hnot_peak :
          ¬ (st.tidMap (prevActive st.active (prevActive st.active r)) <
              st.tidMap (prevActive st.active r) ∧
            st.tidMap r < st.tidMap (prevActive st.active r)) :=
        fun hp => hrS (Finset.mem_filter.mpr ⟨hr, hp⟩)
      simp only [hrS, hnot_peak, ↓reduceIte]
  have hmsgs₂_eq : petersonEmittedMsgs cfg₁ w₂ = (n - st.active.card) + st'.active.card := by
    have hsum : (∑ r ∈ st.active,
        (petersonRecv (cfg₁.node r)
          (.hop2 (st.tidMap (prevActive st.active (prevActive st.active r))))).sent.length) =
        st'.active.card := by
      have hsub_S : st'.active ⊆ st.active := Finset.filter_subset _ _
      calc _ = ∑ r ∈ st.active, if r ∈ st'.active then 1 else 0 := by
            refine Finset.sum_congr rfl fun r hr => ?_
            rw [hpass2_out r hr]
            split_ifs <;> rfl
        _ = (st.active.filter (· ∈ st'.active)).card := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = st'.active.card := by
            congr 1
            ext x
            exact ⟨fun hx => (Finset.mem_filter.mp hx).2,
              fun hx => Finset.mem_filter.mpr ⟨hsub_S hx, hx⟩⟩
    rw [hmsgs₂, hsum]
  refine ⟨w₁ ++ w₂, cfg₂, hmtr₁.comp (petersonLTS n U) hmtr₂, ?_, ?_, ?_⟩
  · rw [petersonEmittedMsgs_append, petersonExec_of_mtr hmtr₁, hmsgs₁_eq, hmsgs₂_eq]
    omega
  · intro i
    rw [hnode₂ i]
    by_cases hiA : i ∈ st.active
    · simp only [hiA, ↓reduceIte, hpass2_out i hiA]
      split_ifs <;> rfl
    · have hiS : i ∉ st'.active := fun h => hiA (Finset.filter_subset _ _ h)
      simp only [hiA, hiS, ↓reduceIte]
  · intro i
    rw [hchan₂ i]
    by_cases hiA : i ∈ st.active
    · simp only [hiA, ↓reduceIte, hpass2_out i hiA]
      split_ifs <;> rfl
    · have hiS : i ∉ st'.active := fun h => hiA (Finset.filter_subset _ _ h)
      simp only [hiA, hiS, ↓reduceIte]

/-- Existence of the canonical terminating wave execution reaching a unique `.leader maxUid` in
`2 * n * petersonPhases uid + n` total messages! -/
private theorem exists_canonical_terminal {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    ∃ (syncSched : List (Fin n)) (cfg_term : PetersonConfig n U) (iStar : Fin n) (maxUid : U),
      (petersonLTS n U).MTr (petersonInit uid) syncSched cfg_term ∧
      (petersonLTS n U).IsTerminal cfg_term ∧
      petersonExecMsgs uid syncSched = 2 * n * petersonPhases uid + n ∧
      (∀ j, uid j ≤ maxUid) ∧
      (∃ j₀, uid j₀ = maxUid) ∧
      cfg_term.node iStar = .leader maxUid ∧
      ∀ j, j ≠ iStar → cfg_term.node j = .relay := by
  let K := petersonPhases uid
  obtain ⟨hK_le_log, hcard_K, _⟩ := peterson_phases_le_log huid
  -- Induct `k = 0, …, K` to reach `IsPhaseStartCfg (petersonPhase uid K)`!
  have hphases : ∀ k ≤ K,
      ∃ (sched_k : List (Fin n)) (cfg_k : PetersonConfig n U),
        (petersonLTS n U).MTr (petersonInit uid) sched_k cfg_k ∧
        IsPhaseStartCfg (petersonPhase uid k) cfg_k ∧
        n + petersonEmittedMsgs (petersonInit uid) sched_k =
          2 * n * k + (petersonPhase uid k).active.card := by
    intro k hkK
    induction k with
    | zero =>
      refine ⟨[], petersonInit uid, LTS.MTr.refl, ?_, ?_⟩
      · exact ⟨fun i => by simp [petersonPhase, petersonInit],
          fun i => by simp [petersonPhase, petersonInit]⟩
      · simp only [petersonEmittedMsgs, add_zero, mul_zero, zero_add, petersonPhase,
          Finset.card_univ, Fintype.card_fin]
    | succ k ih =>
      obtain ⟨sk, cfg_k, hmtr_k, hstart_k, hmsgs_k⟩ := ih (by omega)
      -- Since `k < K = petersonPhases uid`, `2 ≤ (petersonPhase uid k).active.card`!
      have hk2 : 2 ≤ (petersonPhase uid k).active.card := by
        by_contra hnot2
        have hst := phase_stable_of_lt_two uid hnot2 K (by omega)
        -- Look at `petersonPhasesAux uid n` when `¬ 2 ≤ card` at `k < K`:
        have haux_le : ∀ m, k ≤ m → petersonPhasesAux uid m = petersonPhasesAux uid k := by
          suffices ∀ d, petersonPhasesAux uid (k + d) = petersonPhasesAux uid k by
            intro m hm
            obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
            exact this d
          intro d
          induction d with
          | zero => simp only [add_zero]
          | succ d ih_d =>
            have hnot_kd : ¬ 2 ≤ (petersonPhase uid (k + d)).active.card := by
              rw [phase_stable_of_lt_two uid hnot2 (k + d) (by omega)]
              exact hnot2
            rw [← add_assoc, petersonPhasesAux, ih_d]
            simp only [hnot_kd, ↓reduceIte, add_zero]
        have hK_le_k : K ≤ k := by
          have hn_ge_k : k ≤ n := by
            have := Nat.pow_log_le_self 2 (NeZero.ne n)
            have := Nat.lt_two_pow_self (n := Nat.log 2 n)
            omega
          have h1 : K = petersonPhasesAux uid k := haux_le n hn_ge_k
          have h2_le : ∀ m, petersonPhasesAux uid m ≤ m := by
            intro m; induction m with
            | zero => exact le_rfl
            | succ m ihm => simp only [petersonPhasesAux]; split_ifs <;> omega
          exact h1 ▸ h2_le k
        omega
      have hinj_k : Set.InjOn (petersonPhase uid k).tidMap (petersonPhase uid k).active :=
        (petersonPhase_inv huid k).2.1
      obtain ⟨w, cfg_next, hmtr_w, hmsgs_w, hstart_next⟩ :=
        mtr_elimination_phase hstart_k hk2 hinj_k
      have hphase_succ : petersonPhase uid (k + 1) =
          ⟨petersonSurvivors (petersonPhase uid k).active (petersonPhase uid k).tidMap,
            fun r => (petersonPhase uid k).tidMap
              (prevActive (petersonPhase uid k).active r)⟩ := by
        simp only [petersonPhase, hk2, ↓reduceIte]
      have hcard_le_n : (petersonPhase uid k).active.card ≤ n := by
        have := Finset.card_le_univ (petersonPhase uid k).active
        rwa [Fintype.card_fin] at this
      refine ⟨sk ++ w, cfg_next, hmtr_k.comp (petersonLTS n U) hmtr_w, hphase_succ ▸ hstart_next,
        ?_⟩
      rw [petersonEmittedMsgs_append, petersonExec_of_mtr hmtr_k, hphase_succ]
      dsimp only at hmsgs_w ⊢
      have : 2 * n * (k + 1) = 2 * n * k + 2 * n := by ring
      omega
  obtain ⟨sK, cfgK, hmtrK, hstartK, hmsgsK⟩ := hphases K le_rfl
  -- Now `(petersonPhase uid K).active` is a singleton `{iStar}` holding `maxUid`!
  obtain ⟨iStar, hiStar_eq⟩ := Finset.card_eq_one.mp hcard_K
  let stK := petersonPhase uid K
  have hiStar_mem : iStar ∈ stK.active := hiStar_eq ▸ Finset.mem_singleton_self iStar
  obtain ⟨_, _, ⟨qMax, hqMax_mem, hqMax_eq, _⟩⟩ := petersonPhase_inv huid K
  have hqMax_iStar : qMax = iStar :=
    Finset.mem_singleton.mp (hiStar_eq ▸ hqMax_mem)
  rw [hqMax_iStar] at hqMax_eq
  let maxUid := stK.tidMap iStar
  -- Run the final `active = 1` wave (`mtr_wave`) from `cfgK`:
  obtain ⟨w_end, cfg_term, hmtr_end, hmsgs_end, hnode_end, hchan_end⟩ :=
    mtr_wave ⟨iStar, hiStar_mem⟩ (fun i => PetersonMsg.hop1 (stK.tidMap i))
      (fun i hi => by
        rw [hstartK.1 i]
        change (if i ∈ stK.active then _ else _) = _
        simp only [hi, ↓reduceIte])
      hstartK.2
  have hprev_self : prevActive stK.active iStar = iStar := by
    have hp := prevActive_mem hiStar_mem
    exact Finset.mem_singleton.mp (hiStar_eq ▸ hp)
  have hout_iStar :
      petersonRecv (cfgK.node iStar) (.hop1 (stK.tidMap (prevActive stK.active iStar)))
        = ⟨.leader maxUid, []⟩ := by
    rw [hprev_self, hstartK.1 iStar]
    change petersonRecv (if iStar ∈ stK.active then .active1 (stK.tidMap iStar) else .relay)
      (.hop1 (stK.tidMap iStar)) = ⟨.leader maxUid, []⟩
    simp only [hiStar_mem, ↓reduceIte, petersonRecv, maxUid]
  have hchan_empty : ∀ e, cfg_term.chan e = [] := by
    intro e
    rw [hchan_end e]
    by_cases he : e ∈ stK.active
    · have hei : e = iStar := Finset.mem_singleton.mp (hiStar_eq ▸ he)
      subst hei
      simp only [he, ↓reduceIte, hout_iStar]
    · simp only [he, ↓reduceIte]
  have hterm : (petersonLTS n U).IsTerminal cfg_term := by
    intro target _ ⟨hne, _⟩
    exact hne (hchan_empty (target - 1))
  have hmsgs_end_eq : petersonEmittedMsgs cfgK w_end = n - 1 := by
    rw [hmsgs_end, show stK.active = {iStar} from hiStar_eq]
    simp only [Finset.card_singleton, Finset.sum_singleton]
    rw [← hiStar_eq, hout_iStar]
    simp only [List.length_nil, add_zero]
  have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- Identify `maxUid` with `(Finset.univ.image uid).max'` for `∀ j, uid j ≤ maxUid`:
  have hne_univ : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, Finset.mem_univ _⟩
  rcases Finset.mem_image.mp (Finset.max'_mem (Finset.univ.image uid) (hne_univ.image uid)) with
    ⟨j₀, _, hj₀_eq⟩
  refine ⟨sK ++ w_end, cfg_term, iStar, maxUid, hmtrK.comp (petersonLTS n U) hmtr_end, hterm,
    ?_, ?_, ⟨j₀, hj₀_eq.trans hqMax_eq.symm⟩, ?_, ?_⟩
  · rw [petersonExecMsgs, petersonEmittedMsgs_append, petersonExec_of_mtr hmtrK, hmsgs_end_eq]
    change n + (petersonEmittedMsgs (petersonInit uid) sK + (n - 1)) = 2 * n * K + n
    rw [← add_assoc, hmsgsK, hcard_K]
    omega
  · intro j
    dsimp only [maxUid, stK]
    rw [hqMax_eq]
    exact Finset.le_max' _ (uid j) (Finset.mem_image_of_mem uid (Finset.mem_univ j))
  · rw [hnode_end iStar]
    simp only [hiStar_mem, ↓reduceIte, hout_iStar]
  · intro j hj
    have hj_not : j ∉ stK.active := fun h => hj (Finset.mem_singleton.mp (hiStar_eq ▸ h))
    rw [hnode_end j]
    simp only [hj_not, ↓reduceIte]

/-- **Unique leader election (`peterson_elects_leader`).**
For any injective `uid : Fin n → U` on an asynchronous FIFO unidirectional ring `Fin n`:
1. Every reachable configuration extends to a quiescent (`LTS.IsTerminal`) configuration;
2. Every reachable quiescent configuration coincides with the unique terminal configuration where a
   single node `i*` holds `.leader maxUid` (`maxUid = max_j (uid j)`) and all `j ≠ i*` are passive
   `.relay`s (`∃! i*, cfg.isLeader i* = true`). -/
theorem peterson_elects_leader {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    (∀ sched cfg, (petersonLTS n U).MTr (petersonInit uid) sched cfg →
      ∃ rem cfg_term, (petersonLTS n U).MTr cfg rem cfg_term ∧
        (petersonLTS n U).IsTerminal cfg_term) ∧
    ∀ sched cfg, (petersonLTS n U).MTr (petersonInit uid) sched cfg →
      (petersonLTS n U).IsTerminal cfg →
      ∃! iStar : Fin n,
        cfg.isLeader iStar = true ∧
        (∃ maxUid, cfg.node iStar = .leader maxUid ∧
          (∀ j, uid j ≤ maxUid) ∧ ∃ j₀, uid j₀ = maxUid) ∧
        ∀ j, j ≠ iStar → cfg.node j = .relay := by
  obtain ⟨syncSched, cfg_term, iStar, maxUid, hsync, hterm, _, hmax_le, hmax_ex, hleader, hrelay⟩ :=
    exists_canonical_terminal huid
  refine ⟨?_, ?_⟩
  · intro sched cfg hmtr
    obtain ⟨rem, hrem, _, _⟩ := confluence_of_canonical_terminal hsync hterm hmtr
    exact ⟨rem, cfg_term, hrem, hterm⟩
  · intro sched cfg hmtr hcfg_term
    obtain ⟨rem, hrem, _, _⟩ := confluence_of_canonical_terminal hsync hterm hmtr
    have hcfg_eq : cfg = cfg_term := by
      cases rem with
      | nil => exact (LTS.MTr.nil_eq (petersonLTS n U) hrem)
      | cons a tail =>
        rcases LTS.MTr.cons_iff.mp hrem with ⟨c', htr, _⟩
        exact absurd htr (hcfg_term a c')
    subst hcfg_eq
    refine ⟨iStar, ?_, fun k hk => ?_⟩
    · refine ⟨?_, ⟨maxUid, hleader, hmax_le, hmax_ex⟩, hrelay⟩
      simp only [PetersonConfig.isLeader, hleader, PetersonNode.isLeader]
    · by_contra hne
      have hk_rel := hrelay k hne
      have hk_lead := hk.1
      simp only [PetersonConfig.isLeader, hk_rel, PetersonNode.isLeader, Bool.false_eq_true]
        at hk_lead

/-- **Schedule-independent exact complete-run message count (`peterson_execMsgs_eq`).**
Every complete execution `(petersonLTS n U).MTr (petersonInit uid) sched cfg` (`IsTerminal cfg`)
transmits `2 * n * petersonPhases uid + n` messages in total, regardless of the asynchronous FIFO
delivery order! -/
theorem peterson_execMsgs_eq {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid)
    {sched : List (Fin n)} {cfg : PetersonConfig n U}
    (hmtr : (petersonLTS n U).MTr (petersonInit uid) sched cfg)
    (hterm : (petersonLTS n U).IsTerminal cfg) :
    petersonExecMsgs uid sched = 2 * n * petersonPhases uid + n := by
  obtain ⟨syncSched, cfg_term, _, _, hsync, hsync_term, hsync_msgs, _, _, _, _⟩ :=
    exists_canonical_terminal huid
  obtain ⟨rem, hrem, _, hw⟩ := confluence_of_canonical_terminal hsync hsync_term hmtr
  have hrem_nil : rem = [] := by
    cases rem with
    | nil => rfl
    | cons a tail =>
      rcases LTS.MTr.cons_iff.mp hrem with ⟨c', htr, _⟩
      exact absurd htr (hterm a c')
  subst hrem_nil
  simp only [petersonEmittedMsgs, add_zero] at hw
  rw [petersonExecMsgs, hw, ← petersonExecMsgs, hsync_msgs]

/-- **`O(n log n)` Asynchronous Message Bound (`peterson_messages_le`).**
In *every* asynchronous FIFO execution `(petersonLTS n U).MTr (petersonInit uid) sched cfg`
(partial or complete), total messages transmitted across all edges satisfy
`petersonExecMsgs uid sched ≤ 2 * n * Nat.log 2 n + n`. -/
theorem peterson_messages_le {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid)
    {sched : List (Fin n)} {cfg : PetersonConfig n U}
    (hmtr : (petersonLTS n U).MTr (petersonInit uid) sched cfg) :
    petersonExecMsgs uid sched ≤ 2 * n * Nat.log 2 n + n := by
  obtain ⟨syncSched, cfg_term, _, _, hsync, hsync_term, hsync_msgs, _, _, _, _⟩ :=
    exists_canonical_terminal huid
  obtain ⟨rem, _, _, hw⟩ := confluence_of_canonical_terminal hsync hsync_term hmtr
  have hle_sync : petersonExecMsgs uid sched ≤ petersonExecMsgs uid syncSched := by
    simp only [petersonExecMsgs]
    omega
  have hK_le : petersonPhases uid ≤ Nat.log 2 n := (peterson_phases_le_log huid).1
  calc petersonExecMsgs uid sched
      ≤ petersonExecMsgs uid syncSched := hle_sync
    _ = 2 * n * petersonPhases uid + n := hsync_msgs
    _ ≤ 2 * n * Nat.log 2 n + n :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (2 * n) hK_le) n

end Cslib.Distributed.RingElection
