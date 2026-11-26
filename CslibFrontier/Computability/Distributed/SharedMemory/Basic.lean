/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Wait-free shared-memory consensus and the critical-configuration engine

This module models deterministic asynchronous shared-memory protocols interacting with an indexed
family of typed deterministic sequential shared objects (`ObjSpec`), following [Herlihy1991]
(§§2.2–3.1, pp. 128–133; see also prior register-impossibility work [LouiAbuAmara1987] cited in
[Herlihy1991], §3.1, p. 132). It serves as the shared-memory counterpart to `Cslib.FLP`
(asynchronous crash-fault message passing) and reuses `Cslib.LTS` for multistep reachability.

In each global configuration (`Config`), every shared object `i : I` holds a sequential state in
`ObjState i`, and every process `p : P` holds an internal local state in `S` together with a
write-once decision slot `decided : Option V` (`ProcState`). In an atomic step (`Protocol.step`),
an undecided (`Config.Active`) process `p` invokes a single shared object `i = π.target p s` with
operation `π.op p s`, updates object `i` to the resulting sequential state, updates `p`'s local
state from the returned response, and optionally writes its decision to `decided`. Once `p` has
decided, its decision is immutable and `p` takes no further active transitions in `Protocol.lts`.

`Protocol.SolvesWaitFreeConsensus` specifies wait-free consensus ([Herlihy1991], §3, p. 130):
* **Wait-free termination (`Protocol.WaitFree`):** from every initial configuration
  `π.initConfig inp`, the active-step relation `Protocol.StepRel` is accessible
  (`∀ inp, Acc π.StepRel (π.initConfig inp)`), i.e., no infinite sequence of active steps exists
  from any reachable configuration (`Protocol.Reachable.acc`). Unlike global `WellFounded`,
  unreachable local states in `S` impose no restriction on impossibility theorems, while
  bounded-step protocols discharge `WaitFree` in one line via `Protocol.WaitFree.of_wellFounded`.
* **Agreement (`Config.Agreed`):** no reachable configuration decides two distinct values.
* **Validity:** every value decided in a reachable configuration equals some process's initial
  input.

For binary consensus (`V = Bool`), we develop the constructive bivalence and critical-configuration
engine ([Herlihy1991], §3.1, pp. 131–133):
* `Protocol.soloRun` computably drives any single process `p` to a decision from any accessible
  configuration via `WellFounded.fixF`, and `Protocol.soloRun_mem_proc_eq` shows that `p`'s solo
  execution depends only on `c.mem` and `c.proc p`.
* `Protocol.exists_bivalent_init` proves that when `2 ≤ Fintype.card P`, every wait-free binary
  consensus protocol admits a bivalent initial configuration by flipping inputs one process at a
  time from unanimous `false` to unanimous `true` (extending [Herlihy1991], §3.1, p. 131 from
  `|P| = 2` to arbitrary `2 ≤ Fintype.card P`).
* `Protocol.exists_critical_config` uses structural recursion on `Acc π.StepRel` directly (without
  König's lemma) to reach a critical bivalent configuration `c*` where every process is active and
  two distinct processes `p ≠ q` step to `false`-univalent and `true`-univalent configurations
  respectively.

## Main definitions

* `Cslib.Distributed.SharedMemory.ObjSpec`: deterministic sequential shared-object specification.
* `Cslib.Distributed.SharedMemory.ProcState`: per-process internal state and write-once decision.
* `Cslib.Distributed.SharedMemory.Config`: global shared-memory configuration.
* `Cslib.Distributed.SharedMemory.Protocol`: asynchronous deterministic shared-memory protocol.
* `Cslib.Distributed.SharedMemory.Protocol.lts`: active-step `Cslib.LTS` of a protocol.
* `Cslib.Distributed.SharedMemory.Protocol.StepRel`,
  `Cslib.Distributed.SharedMemory.Protocol.WaitFree`: active-step relation and reachable wait-free
  termination from every `initConfig`.
* `Cslib.Distributed.SharedMemory.Protocol.SolvesWaitFreeConsensus`: wait-free consensus
  specification (termination, agreement, validity).
* `Cslib.Distributed.SharedMemory.Protocol.soloRun`: solo execution of a single process to
  completion.
* `Cslib.Distributed.SharedMemory.Protocol.CanDecide`,
  `Cslib.Distributed.SharedMemory.Protocol.IsUnivalent`,
  `Cslib.Distributed.SharedMemory.Protocol.IsBivalent`,
  `Cslib.Distributed.SharedMemory.Protocol.IsCritical`: bivalence and criticality predicates.

## Main results

* `Cslib.Distributed.SharedMemory.Protocol.soloRun_mem_proc_eq`: solo-run indistinguishability when
  shared memory and the running process's state agree.
* `Cslib.Distributed.SharedMemory.Protocol.not_univalent_of_indistinguishable`: configurations
  reachable from `false`-univalent and `true`-univalent states cannot agree on shared memory and
  any single witness process `w`.
* `Cslib.Distributed.SharedMemory.Protocol.exists_bivalent_init`: every wait-free binary consensus
  protocol on `2 ≤ Fintype.card P` processes has a bivalent initial configuration.
* `Cslib.Distributed.SharedMemory.Protocol.exists_critical_config`: every reachable bivalent
  configuration of a wait-free binary consensus protocol reaches a critical configuration with
  all processes active and distinct `false`-univalent and `true`-univalent successor steps.

## References

* [M. Herlihy, *Wait-Free Synchronization*][Herlihy1991]
* [M. C. Loui, H. H. Abu-Amara, *Memory Requirements for Agreement Among Unreliable Asynchronous
  Processes*][LouiAbuAmara1987]
-/

public section

namespace Cslib.Distributed.SharedMemory

open Cslib

/-- Specification of a single deterministic sequential shared object with operation type `Op`,
response type `Resp`, initial state `init`, and atomic transition `step` returning
`(nextState, response)`. -/
structure ObjSpec (Op Resp ObjState : Type*) where
  /-- Initial state of the shared object. -/
  init : ObjState
  /-- Atomic transition taking an operation and current state to `(nextState, response)`. -/
  step : Op → ObjState → ObjState × Resp

/-- Local state of a single process: internal protocol state `state` paired with a write-once
decision register `decided`. -/
@[ext]
structure ProcState (S V : Type*) where
  /-- Internal local state of the process. -/
  state : S
  /-- Write-once consensus decision (`none` while undecided). -/
  decided : Option V
  deriving @[expose] DecidableEq

/-- Global configuration of a shared-memory system over process type `P` and object family `I`:
the state `mem i` of every shared object `i` together with the local state `proc p` of every
process `p`. -/
@[ext]
structure Config (P : Type*) {I : Type*} (ObjState : I → Type*) (S V : Type*) where
  /-- Current sequential state of each shared object. -/
  mem : ∀ i, ObjState i
  /-- Current local state and optional decision of each process. -/
  proc : P → ProcState S V

namespace Config

variable {P I S V : Type*} {ObjState : I → Type*}

/-- Process `p` is active in configuration `c` when it has not yet decided a value. -/
@[expose]
def Active (c : Config P ObjState S V) (p : P) : Prop :=
  (c.proc p).decided = none

instance instDecidableActive (c : Config P ObjState S V) (p : P) : Decidable (c.Active p) :=
  match h : (c.proc p).decided with
  | none => isTrue h
  | some _ => isFalse fun h' => nomatch h.symm.trans h'

/-- Configuration `c` has decided `v` if at least one process has `decided = some v`. -/
@[expose]
def Decided (c : Config P ObjState S V) (v : V) : Prop :=
  ∃ p, (c.proc p).decided = some v

/-- All decided values in configuration `c` agree with one another. -/
@[expose]
def Agreed (c : Config P ObjState S V) : Prop :=
  ∀ v₁ v₂, c.Decided v₁ → c.Decided v₂ → v₁ = v₂

end Config

/-- Deterministic asynchronous shared-memory protocol for processes `P` with input/decision values
`V`, local state `S`, and shared objects `objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i)`.
Each step of an active process `p` in local state `s` invokes object `target p s` with operation
`op p s`, then updates `p`'s local state via `next` and optional decision via `decideVal` from
the returned response. -/
structure Protocol (P : Type*) {I : Type*} {Op Resp ObjState : I → Type*}
    (objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i)) (S V : Type*) where
  /-- Initial local state of process `p` given its input value. -/
  init : P → V → S
  /-- Shared object targeted by process `p` in local state `s`. -/
  target : P → S → I
  /-- Operation invoked on `target p s` by process `p` in local state `s`. -/
  op : ∀ (p : P) (s : S), Op (target p s)
  /-- Next internal local state of `p` after receiving the object's response. -/
  next : ∀ (p : P) (s : S), Resp (target p s) → S
  /-- Optional decision written by `p` after receiving the object's response. -/
  decideVal : ∀ (p : P) (s : S), Resp (target p s) → Option V

namespace Protocol

section Execution

variable {P I S V : Type*} {Op Resp ObjState : I → Type*}
  {objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i)}

/-- Initial global configuration for input assignment `inp : P → V`: every shared object starts at
`(objs i).init` and every process `p` starts undecided at `π.init p (inp p)`. -/
@[expose]
def initConfig (π : Protocol P objs S V) (inp : P → V) : Config P ObjState S V where
  mem i := (objs i).init
  proc p := { state := π.init p (inp p), decided := none }

variable [DecidableEq P] [DecidableEq I]

/-- Single atomic step of process `p` from configuration `c`. If `p` has already decided, `step`
is a no-op; otherwise `p` invokes `π.target p s` and updates that object and `p`'s local state. -/
@[expose]
def step (π : Protocol P objs S V) (p : P) (c : Config P ObjState S V) : Config P ObjState S V :=
  match (c.proc p).decided with
  | some _ => c
  | none =>
    let s := (c.proc p).state
    let i := π.target p s
    let res := (objs i).step (π.op p s) (c.mem i)
    { mem := Function.update c.mem i res.1
      proc := Function.update c.proc p
        { state := π.next p s res.2
          decided := π.decideVal p s res.2 } }

/-- Execute a finite schedule `sched : List P` of process steps from configuration `c`. -/
@[expose]
def run (π : Protocol P objs S V) (sched : List P) (c : Config P ObjState S V) :
    Config P ObjState S V :=
  sched.foldl (fun acc p => π.step p acc) c

@[simp]
theorem run_nil (π : Protocol P objs S V) (c : Config P ObjState S V) :
    π.run [] c = c :=
  rfl

@[simp]
theorem run_cons (π : Protocol P objs S V) (p : P) (sched : List P) (c : Config P ObjState S V) :
    π.run (p :: sched) c = π.run sched (π.step p c) :=
  rfl

/-- Active-step labelled transition system of `π`: transitions are labelled by `p : P` and fire
precisely when `p` is still undecided (`c.Active p`). -/
@[expose]
def lts (π : Protocol P objs S V) : LTS (Config P ObjState S V) P where
  Tr c p c' := c.Active p ∧ π.step p c = c'

instance instDeterministicLTS (π : Protocol P objs S V) : π.lts.Deterministic where
  deterministic _ _ _ _ h₁ h₂ := h₁.2.symm.trans h₂.2

/-- Configuration `c` is reachable under input assignment `inp` via active protocol steps. -/
@[expose]
def Reachable (π : Protocol P objs S V) (inp : P → V) (c : Config P ObjState S V) : Prop :=
  π.lts.CanReach (π.initConfig inp) c

/-- Active-step relation `c' ≺ c` of `π`: `c'` is reached from `c` by one atomic step of an active
(undecided) process `p`. -/
abbrev StepRel (π : Protocol P objs S V) (c' c : Config P ObjState S V) : Prop :=
  ∃ p, c.Active p ∧ π.step p c = c'

/-- Wait-free termination ([Herlihy1991], §2.3 & §3, pp. 129–130): from every initial configuration
`π.initConfig inp`, the active-step relation `π.StepRel` is accessible, so no infinite sequence of
active steps exists from any reachable configuration. -/
abbrev WaitFree (π : Protocol P objs S V) : Prop :=
  ∀ inp : P → V, Acc π.StepRel (π.initConfig inp)

/-- Any protocol whose active-step relation is globally well-founded is wait-free. -/
theorem WaitFree.of_wellFounded {π : Protocol P objs S V} (hwf : WellFounded π.StepRel) :
    π.WaitFree :=
  fun inp => hwf.apply (π.initConfig inp)

/-- `π.SolvesWaitFreeConsensus` states that `π` solves wait-free consensus over `P` and `V`
([Herlihy1991], §3, p. 130): active steps from every `initConfig` are accessible (`WaitFree`),
reachable configurations satisfy agreement, and every decided value in a reachable configuration
equals some process's initial input. -/
structure SolvesWaitFreeConsensus (π : Protocol P objs S V) : Prop where
  /-- No infinite sequence of active steps exists. -/
  waitFree : π.WaitFree
  /-- Reachable configurations never decide two distinct values. -/
  agreement : ∀ inp c, π.Reachable inp c → c.Agreed
  /-- Every decided value in a reachable configuration is some process's initial input. -/
  validity : ∀ inp c v, π.Reachable inp c → c.Decided v → ∃ q, inp q = v

theorem step_of_not_active (π : Protocol P objs S V) {p : P} {c : Config P ObjState S V}
    (h : ¬ c.Active p) : π.step p c = c := by
  simp only [Config.Active] at h
  cases hdec : (c.proc p).decided with
  | none => exact absurd hdec h
  | some v => simp only [step, hdec]

theorem step_of_active (π : Protocol P objs S V) {p : P} {c : Config P ObjState S V}
    (h : c.Active p) :
    π.step p c =
      { mem := Function.update c.mem (π.target p (c.proc p).state)
          ((objs (π.target p (c.proc p).state)).step
            (π.op p (c.proc p).state) (c.mem (π.target p (c.proc p).state))).1
        proc := Function.update c.proc p
          { state := π.next p (c.proc p).state
              ((objs (π.target p (c.proc p).state)).step
                (π.op p (c.proc p).state) (c.mem (π.target p (c.proc p).state))).2
            decided := π.decideVal p (c.proc p).state
              ((objs (π.target p (c.proc p).state)).step
                (π.op p (c.proc p).state) (c.mem (π.target p (c.proc p).state))).2 } } := by
  simp only [Config.Active] at h
  simp only [step, h]

@[simp]
theorem step_proc_of_ne (π : Protocol P objs S V) {p q : P} (c : Config P ObjState S V)
    (hne : q ≠ p) : (π.step p c).proc q = c.proc q := by
  by_cases h : c.Active p
  · rw [π.step_of_active h]
    exact Function.update_of_ne hne _ _
  · rw [π.step_of_not_active h]

theorem active_step_of_ne (π : Protocol P objs S V) {p q : P} {c : Config P ObjState S V}
    (hne : q ≠ p) : (π.step p c).Active q ↔ c.Active q := by
  simp only [Config.Active, π.step_proc_of_ne c hne]

theorem step_mem_of_ne_target (π : Protocol P objs S V) {p : P} {c : Config P ObjState S V}
    (h : c.Active p) {j : I} (hne : j ≠ π.target p (c.proc p).state) :
    (π.step p c).mem j = c.mem j := by
  rw [π.step_of_active h]
  exact Function.update_of_ne hne _ _

/-- Steps by distinct active processes targeting distinct shared objects commute exactly. -/
theorem step_comm_of_ne_target (π : Protocol P objs S V) {p q : P} {c : Config P ObjState S V}
    (hp : c.Active p) (hq : c.Active q) (hpq : p ≠ q)
    (htarget : π.target p (c.proc p).state ≠ π.target q (c.proc q).state) :
    π.step q (π.step p c) = π.step p (π.step q c) := by
  rw [π.step_of_active ((π.active_step_of_ne hpq.symm).mpr hq),
    π.step_of_active ((π.active_step_of_ne hpq).mpr hp),
    π.step_proc_of_ne c hpq.symm, π.step_proc_of_ne c hpq,
    π.step_mem_of_ne_target hp htarget.symm, π.step_mem_of_ne_target hq htarget,
    π.step_of_active hp, π.step_of_active hq]
  exact Config.ext (Function.update_comm htarget _ _ c.mem) (Function.update_comm hpq _ _ c.proc)

/-- Decisions are write-once across single steps: once `p` decides `v`, every step preserves it. -/
theorem procDecided_step (π : Protocol P objs S V) {p : P} (q : P) {c : Config P ObjState S V}
    {v : V} (hd : (c.proc p).decided = some v) :
    ((π.step q c).proc p).decided = some v := by
  by_cases hqp : p = q
  · subst hqp
    have hna : ¬ c.Active p := by simp only [Config.Active, hd, reduceCtorEq, not_false_eq_true]
    rw [π.step_of_not_active hna, hd]
  · rw [π.step_proc_of_ne c hqp, hd]

/-- Decisions are write-once across arbitrary reachable paths. -/
theorem procDecided_stable (π : Protocol P objs S V) {p : P} {c c' : Config P ObjState S V}
    {v : V} (hd : (c.proc p).decided = some v) (hreach : π.lts.CanReach c c') :
    (c'.proc p).decided = some v := by
  obtain ⟨ps, hmtr⟩ := hreach
  induction hmtr with
  | refl => exact hd
  | stepL htr _ ih =>
    rw [← htr.2] at ih
    exact ih (π.procDecided_step _ hd)

theorem reachable_initConfig (π : Protocol P objs S V) (inp : P → V) :
    π.Reachable inp (π.initConfig inp) :=
  LTS.CanReach.refl _ _

theorem Reachable.trans {π : Protocol P objs S V} {inp : P → V} {c c' : Config P ObjState S V}
    (hr : π.Reachable inp c) (hc : π.lts.CanReach c c') : π.Reachable inp c' := by
  obtain ⟨ps₁, h₁⟩ := hr
  obtain ⟨ps₂, h₂⟩ := hc
  exact ⟨ps₁ ++ ps₂, h₁.comp _ h₂⟩

/-- Accessibility under `StepRel` propagates forward along any active multi-step path. -/
theorem acc_of_canReach (π : Protocol P objs S V) {c c' : Config P ObjState S V}
    (ha : Acc π.StepRel c) (hreach : π.lts.CanReach c c') : Acc π.StepRel c' := by
  obtain ⟨ps, hmtr⟩ := hreach
  induction hmtr with
  | refl => exact ha
  | stepL htr _ ih => exact ih (ha.inv ⟨_, htr.1, htr.2⟩)

/-- Every configuration reachable from `π.initConfig inp` in a wait-free protocol is accessible
under `StepRel`. -/
theorem Reachable.acc {π : Protocol P objs S V} {inp : P → V} {c : Config P ObjState S V}
    (hr : π.Reachable inp c) (hwf : π.WaitFree) : Acc π.StepRel c :=
  π.acc_of_canReach (hwf inp) hr

/-- Invariant principle for configurations reachable under `inp`, derived from
`Cslib.LTS.mtrInv_of_trInv`. -/
theorem Reachable.induction {π : Protocol P objs S V} {inp : P → V}
    {motive : Config P ObjState S V → Prop}
    (hinit : motive (π.initConfig inp))
    (hstep : ∀ {c : Config P ObjState S V} {p : P}, motive c → c.Active p → motive (π.step p c))
    {c : Config P ObjState S V} (hr : π.Reachable inp c) : motive c := by
  obtain ⟨ps, hmtr⟩ := hr
  exact (LTS.mtrInv_of_trInv fun _ p _ htr hm => htr.2 ▸ hstep hm htr.1)
    (π.initConfig inp) ps c hmtr hinit

theorem canReach_step (π : Protocol P objs S V) (p : P) (c : Config P ObjState S V) :
    π.lts.CanReach c (π.step p c) := by
  by_cases h : c.Active p
  · exact ⟨[p], LTS.MTr.single _ ⟨h, rfl⟩⟩
  · rw [π.step_of_not_active h]
    exact LTS.CanReach.refl _ _

theorem canReach_run (π : Protocol P objs S V) (sched : List P) (c : Config P ObjState S V) :
    π.lts.CanReach c (π.run sched c) := by
  induction sched generalizing c with
  | nil => exact LTS.CanReach.refl _ _
  | cons p sched ih =>
    obtain ⟨ps₁, h₁⟩ := π.canReach_step p c
    obtain ⟨ps₂, h₂⟩ := ih (π.step p c)
    exact ⟨ps₁ ++ ps₂, h₁.comp _ h₂⟩

theorem reachable_run (π : Protocol P objs S V) (inp : P → V) (sched : List P) :
    π.Reachable inp (π.run sched (π.initConfig inp)) :=
  (π.reachable_initConfig inp).trans (π.canReach_run sched _)

/-! ### Solo executions -/

/-- Run process `p` alone from an accessible configuration `c` until `p` is no longer active
(has decided). -/
def soloRun (π : Protocol P objs S V) (p : P) (c : Config P ObjState S V)
    (ha : Acc π.StepRel c) : Config P ObjState S V :=
  WellFounded.fixF
    (fun c rec =>
      if h : c.Active p then
        rec (π.step p c) ⟨p, h, rfl⟩
      else
        c)
    c ha

theorem soloRun_of_not_active (π : Protocol P objs S V) (p : P)
    {c : Config P ObjState S V} (ha : Acc π.StepRel c) (h : ¬ c.Active p) :
    π.soloRun p c ha = c := by
  rw [soloRun, WellFounded.fixF_eq]
  simp only [h, ↓reduceDIte]

theorem soloRun_of_active (π : Protocol P objs S V) (p : P)
    {c : Config P ObjState S V} (ha : Acc π.StepRel c) (h : c.Active p) :
    π.soloRun p c ha = π.soloRun p (π.step p c) (ha.inv ⟨p, h, rfl⟩) := by
  nth_rw 1 [soloRun]
  rw [WellFounded.fixF_eq]
  simp only [h, ↓reduceDIte]
  rfl

theorem soloRun_not_active (π : Protocol P objs S V) (p : P)
    {c : Config P ObjState S V} (ha : Acc π.StepRel c) :
    ¬ (π.soloRun p c ha).Active p := by
  induction ha with
  | intro c ha ih =>
    by_cases h : c.Active p
    · rw [π.soloRun_of_active p (Acc.intro c ha) h]
      exact ih (π.step p c) ⟨p, h, rfl⟩
    · rw [π.soloRun_of_not_active p (Acc.intro c ha) h]
      exact h

theorem exists_decided_soloRun (π : Protocol P objs S V) (p : P)
    {c : Config P ObjState S V} (ha : Acc π.StepRel c) :
    ∃ v, ((π.soloRun p c ha).proc p).decided = some v := by
  have hna := π.soloRun_not_active p ha
  simp only [Config.Active] at hna
  cases hdec : ((π.soloRun p c ha).proc p).decided with
  | none => exact absurd hdec hna
  | some v => exact ⟨v, rfl⟩

theorem canReach_soloRun (π : Protocol P objs S V) (p : P)
    {c : Config P ObjState S V} (ha : Acc π.StepRel c) :
    π.lts.CanReach c (π.soloRun p c ha) := by
  induction ha with
  | intro c ha ih =>
    by_cases h : c.Active p
    · rw [π.soloRun_of_active p (Acc.intro c ha) h]
      obtain ⟨ps, hmtr⟩ := ih (π.step p c) ⟨p, h, rfl⟩
      exact ⟨p :: ps, .stepL ⟨h, rfl⟩ hmtr⟩
    · rw [π.soloRun_of_not_active p (Acc.intro c ha) h]
      exact LTS.CanReach.refl _ _

/-- **Solo-run indistinguishability:** a solo execution of process `p` depends only on the shared
memory `c.mem` and `p`'s own local state `c.proc p`; the local states of other processes `q ≠ p`
are neither read nor modified during `p`'s solo run. -/
theorem soloRun_mem_proc_eq (π : Protocol P objs S V) (p : P)
    {c₁ : Config P ObjState S V} (ha₁ : Acc π.StepRel c₁) :
    ∀ {c₂ : Config P ObjState S V} (ha₂ : Acc π.StepRel c₂),
      c₁.mem = c₂.mem → c₁.proc p = c₂.proc p →
      (π.soloRun p c₁ ha₁).mem = (π.soloRun p c₂ ha₂).mem ∧
        (π.soloRun p c₁ ha₁).proc p = (π.soloRun p c₂ ha₂).proc p := by
  induction ha₁ with
  | intro c₁ ha₁ ih =>
    intro c₂ ha₂ hmem hproc
    by_cases h₁ : c₁.Active p
    · have h₂ : c₂.Active p := by simpa only [Config.Active, ← hproc] using h₁
      rw [π.soloRun_of_active p (Acc.intro c₁ ha₁) h₁, π.soloRun_of_active p ha₂ h₂]
      apply ih (π.step p c₁) ⟨p, h₁, rfl⟩ (ha₂.inv ⟨p, h₂, rfl⟩)
      · rw [π.step_of_active h₁, π.step_of_active h₂]
        dsimp only
        rw [hproc, hmem]
      · rw [π.step_of_active h₁, π.step_of_active h₂]
        dsimp only
        rw [hproc, hmem, Function.update_self, Function.update_self]
    · have h₂ : ¬ c₂.Active p := by simpa only [Config.Active, ← hproc] using h₁
      rw [π.soloRun_of_not_active p (Acc.intro c₁ ha₁) h₁, π.soloRun_of_not_active p ha₂ h₂]
      exact ⟨hmem, hproc⟩

/-- Decision value `v` is reachable from configuration `c`. -/
def CanDecide (π : Protocol P objs S V) (c : Config P ObjState S V) (v : V) : Prop :=
  ∃ c', π.lts.CanReach c c' ∧ c'.Decided v

theorem CanDecide.of_canReach {π : Protocol P objs S V} {c₁ c₂ : Config P ObjState S V} {v : V}
    (hreach : π.lts.CanReach c₁ c₂) (hdec : π.CanDecide c₂ v) : π.CanDecide c₁ v := by
  obtain ⟨c₃, h₂₃, hd⟩ := hdec
  obtain ⟨ps₁, h₁⟩ := hreach
  obtain ⟨ps₂, h₂⟩ := h₂₃
  exact ⟨c₃, ⟨ps₁ ++ ps₂, h₁.comp _ h₂⟩, hd⟩

/-- From every accessible configuration `c` and any process `p`, `p`'s solo execution reaches a
decision. -/
theorem exists_canDecide (π : Protocol P objs S V) (p : P)
    {c : Config P ObjState S V} (ha : Acc π.StepRel c) : ∃ v, π.CanDecide c v := by
  obtain ⟨v, hv⟩ := π.exists_decided_soloRun p ha
  exact ⟨v, π.soloRun p c ha, π.canReach_soloRun p ha, p, hv⟩

end Execution

/-! ### Binary bivalence and critical configurations -/

section Bivalence

variable {P I S : Type*} {Op Resp ObjState : I → Type*}
  {objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i)}
  [DecidableEq P] [DecidableEq I]

/-- Configuration `c` is `b`-univalent (`b`-valent) if `b` is reachable from `c` and `!b` is not
([Herlihy1991], §3.1, p. 131). -/
def IsUnivalent (π : Protocol P objs S Bool) (c : Config P ObjState S Bool) (b : Bool) : Prop :=
  π.CanDecide c b ∧ ¬ π.CanDecide c (!b)

/-- Configuration `c` is bivalent if both `false` and `true` are reachable decisions from `c`
([Herlihy1991], §3.1, p. 131). -/
def IsBivalent (π : Protocol P objs S Bool) (c : Config P ObjState S Bool) : Prop :=
  π.CanDecide c false ∧ π.CanDecide c true

/-- Configuration `c` is *critical* if `c` is bivalent yet every active step from `c` is a decision
step leaving the set of bivalent configurations ([Herlihy1991], §3.1, pp. 131–132). -/
def IsCritical (π : Protocol P objs S Bool) (c : Config P ObjState S Bool) : Prop :=
  π.IsBivalent c ∧ ∀ p, c.Active p → ¬ π.IsBivalent (π.step p c)

/-- A decision reachable from a configuration that cannot reach `!b` is `b`. -/
private theorem eq_of_canDecide_of_not {π : Protocol P objs S Bool}
    {c : Config P ObjState S Bool} {b b' : Bool} (hb' : π.CanDecide c b')
    (hnb : ¬ π.CanDecide c (!b)) : b' = b := by
  cases b <;> cases b' <;> first | rfl | exact absurd hb' hnb

/-- A bivalent configuration can reach either decision. -/
private theorem IsBivalent.canDecide {π : Protocol P objs S Bool} {c : Config P ObjState S Bool}
    (h : π.IsBivalent c) : ∀ b, π.CanDecide c b
  | false => h.1
  | true => h.2

theorem IsUnivalent.of_canReach {π : Protocol P objs S Bool} (p : P)
    {c c' : Config P ObjState S Bool} {b : Bool} (ha : Acc π.StepRel c)
    (hu : π.IsUnivalent c b) (hreach : π.lts.CanReach c c') : π.IsUnivalent c' b := by
  refine ⟨?_, fun hnb => hu.2 (hnb.of_canReach hreach)⟩
  obtain ⟨b', hb'⟩ := π.exists_canDecide p (π.acc_of_canReach ha hreach)
  exact eq_of_canDecide_of_not (hb'.of_canReach hreach) hu.2 ▸ hb'

/-- In any accessible configuration `c'` reachable from a `b`-univalent configuration `c`, running
any process `w` solo decides `b`. -/
theorem IsUnivalent.soloRun_decided {π : Protocol P objs S Bool} (w : P)
    {c c' : Config P ObjState S Bool} {b : Bool}
    (hu : π.IsUnivalent c b) (hreach : π.lts.CanReach c c') (ha' : Acc π.StepRel c') :
    ((π.soloRun w c' ha').proc w).decided = some b := by
  obtain ⟨d, hd⟩ := π.exists_decided_soloRun w ha'
  have hcan : π.CanDecide c d :=
    CanDecide.of_canReach hreach ⟨π.soloRun w c' ha', π.canReach_soloRun w ha', w, hd⟩
  exact eq_of_canDecide_of_not hcan hu.2 ▸ hd

/-- **Solo-indistinguishability contradiction ([Herlihy1991], §3.1, pp. 131–133):** if `c₀` is
reachable from an accessible `false`-univalent configuration `u₀`, `c₁` is reachable from an
accessible `true`-univalent configuration `u₁`, and `c₀` and `c₁` have identical shared memory and
identical local state at some witness process `w`, then `w`'s solo execution yields a
contradiction. -/
theorem not_univalent_of_indistinguishable {π : Protocol P objs S Bool} (w : P)
    {u₀ u₁ c₀ c₁ : Config P ObjState S Bool}
    (ha₀ : Acc π.StepRel u₀) (ha₁ : Acc π.StepRel u₁)
    (hu₀ : π.IsUnivalent u₀ false) (hu₁ : π.IsUnivalent u₁ true)
    (hr₀ : π.lts.CanReach u₀ c₀) (hr₁ : π.lts.CanReach u₁ c₁)
    (hmem : c₀.mem = c₁.mem) (hproc : c₀.proc w = c₁.proc w) : False := by
  have ha₀' := π.acc_of_canReach ha₀ hr₀
  have ha₁' := π.acc_of_canReach ha₁ hr₁
  have hd₀ := hu₀.soloRun_decided w hr₀ ha₀'
  have hd₁ := hu₁.soloRun_decided w hr₁ ha₁'
  have heq := (π.soloRun_mem_proc_eq w ha₀' ha₁' hmem hproc).2
  rw [heq] at hd₀
  exact Option.some.inj (hd₀.symm.trans hd₁) |> Bool.noConfusion

/-- Under consensus agreement, every process in a reachable bivalent configuration is still active
(undecided): a decided process's write-once decision would persist into a reachable configuration
deciding the opposite bit. -/
theorem IsBivalent.active_all {π : Protocol P objs S Bool}
    (hcons : π.SolvesWaitFreeConsensus) {inp : P → Bool} {c : Config P ObjState S Bool}
    (hr : π.Reachable inp c) (hbiv : π.IsBivalent c) (p : P) : c.Active p := by
  simp only [Config.Active]
  cases hdec : (c.proc p).decided with
  | none => rfl
  | some b =>
    obtain ⟨c', hreach, hd_not⟩ := hbiv.canDecide (!b)
    have heq := hcons.agreement inp c' (hr.trans hreach) b (!b)
      ⟨p, π.procDecided_stable hdec hreach⟩ hd_not
    exact absurd heq.symm (Bool.not_ne_self b)

/-- For an adjacent input flip `inpK` along an enumeration `e : P ≃ Fin n`, unanimous `false` at
`0` is `false`-valent and unanimous `true` at `n` cannot decide `false`. -/
private theorem univalent_initConfig_const {π : Protocol P objs S Bool}
    (hcons : π.SolvesWaitFreeConsensus) (p₀ : P) (b : Bool) :
    π.IsUnivalent (π.initConfig fun _ => b) b := by
  have hno_opp : ¬ π.CanDecide (π.initConfig fun _ => b) (!b) := by
    rintro ⟨c, hreach, hd⟩
    obtain ⟨q, hq⟩ := hcons.validity (fun _ => b) c (!b) hreach hd
    exact Bool.not_ne_self b hq.symm
  obtain ⟨d, hd⟩ := π.exists_canDecide p₀ (hcons.waitFree fun _ => b)
  exact ⟨eq_of_canDecide_of_not hd hno_opp ▸ hd, hno_opp⟩

/-- **Initial bivalence (extending [Herlihy1991], §3.1, p. 131 from `|P| = 2` to
`2 ≤ Fintype.card P` via single-input flips):** every wait-free binary consensus protocol over
`2 ≤ Fintype.card P` processes has at least one bivalent initial configuration. -/
theorem exists_bivalent_init [Fintype P] (π : Protocol P objs S Bool)
    (hcons : π.SolvesWaitFreeConsensus) (hcard : 2 ≤ Fintype.card P) :
    ∃ inp : P → Bool, π.IsBivalent (π.initConfig inp) := by
  by_contra hnone
  push Not at hnone
  let n := Fintype.card P
  let e : P ≃ Fin n := Fintype.equivFin P
  have hn_pos : 0 < n := by omega
  let p₀ : P := e.symm ⟨0, hn_pos⟩
  let inpK : ℕ → P → Bool := fun k p => decide ((e p).val < k)
  have hu0 : π.IsUnivalent (π.initConfig (inpK 0)) false := by
    convert univalent_initConfig_const hcons p₀ false with p
    simp only [inpK, Nat.not_lt_zero, decide_false]
  have huN : π.IsUnivalent (π.initConfig (inpK n)) true := by
    convert univalent_initConfig_const hcons p₀ true with p
    simp only [inpK, (e p).isLt, decide_true]
  have huniv : ∀ k, π.IsUnivalent (π.initConfig (inpK k)) false ∨
      π.IsUnivalent (π.initConfig (inpK k)) true := by
    intro k
    obtain ⟨b, hb⟩ := π.exists_canDecide p₀ (hcons.waitFree (inpK k))
    cases b
    exacts [Or.inl ⟨hb, fun ht => hnone _ ⟨hb, ht⟩⟩, Or.inr ⟨hb, fun hf => hnone _ ⟨hf, hb⟩⟩]
  have hex_switch : ∃ k < n, π.IsUnivalent (π.initConfig (inpK k)) false ∧
      π.IsUnivalent (π.initConfig (inpK (k + 1))) true := by
    by_contra hno_sw
    push Not at hno_sw
    have hall : ∀ k ≤ n, π.IsUnivalent (π.initConfig (inpK k)) false := by
      intro k hk
      induction k with
      | zero => exact hu0
      | succ k ih => exact (huniv (k + 1)).resolve_right (hno_sw k hk (ih (by omega)))
    exact (hall n le_rfl).2 huN.1
  obtain ⟨k, hk, huf, hut⟩ := hex_switch
  let q : P := e.symm ⟨k, hk⟩
  obtain ⟨p, hpq⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card P) q
  have hval_ne : (e p).val ≠ k := fun heq => hpq (e.injective (Fin.ext (by simp [q, heq])))
  have hinp_eq : inpK k p = inpK (k + 1) p := by
    simp only [inpK, decide_eq_decide]
    omega
  exact not_univalent_of_indistinguishable p
    (hcons.waitFree (inpK k)) (hcons.waitFree (inpK (k + 1))) huf hut
    (LTS.CanReach.refl _ _) (LTS.CanReach.refl _ _) rfl
    (by simp only [initConfig, hinp_eq])

/-- **Constructive critical configuration ([Herlihy1991], §3.1, pp. 131–132):** from any reachable
bivalent configuration `c` of a wait-free binary consensus protocol, structural induction on
`Reachable.acc` reaches a critical configuration `c*` in which every process is active and two
distinct processes `p ≠ q` step to `false`-univalent and `true`-univalent configurations
respectively. -/
theorem exists_critical_config (π : Protocol P objs S Bool)
    (hcons : π.SolvesWaitFreeConsensus) {inp : P → Bool} {c : Config P ObjState S Bool}
    (hr : π.Reachable inp c) (hbiv : π.IsBivalent c) :
    ∃ cstar p q,
      π.lts.CanReach c cstar ∧
      π.IsCritical cstar ∧
      (∀ r, cstar.Active r) ∧
      p ≠ q ∧
      π.IsUnivalent (π.step p cstar) false ∧
      π.IsUnivalent (π.step q cstar) true := by
  have hex_crit : ∀ {c₀}, Acc π.StepRel c₀ → π.IsBivalent c₀ →
      ∃ cstar, π.lts.CanReach c₀ cstar ∧ π.IsCritical cstar := by
    intro c₀ ha
    induction ha with
    | intro c₀ _ ih =>
      intro hbiv₀
      by_cases hex : ∃ p, c₀.Active p ∧ π.IsBivalent (π.step p c₀)
      · obtain ⟨p, hact, hbiv'⟩ := hex
        obtain ⟨cstar, ⟨ps, hmtr⟩, hcrit⟩ := ih (π.step p c₀) ⟨p, hact, rfl⟩ hbiv'
        exact ⟨cstar, ⟨p :: ps, .stepL ⟨hact, rfl⟩ hmtr⟩, hcrit⟩
      · push Not at hex
        exact ⟨c₀, LTS.CanReach.refl _ _, hbiv₀, hex⟩
  obtain ⟨cstar, hreach, hcrit⟩ := hex_crit (hr.acc hcons.waitFree) hbiv
  have hr_star : π.Reachable inp cstar := hr.trans hreach
  have hall_act : ∀ r, cstar.Active r := hcrit.1.active_all hcons hr_star
  have hex_step : ∀ b : Bool, ∃ p, π.IsUnivalent (π.step p cstar) b := by
    intro b
    obtain ⟨cf, ⟨ps, hmtr⟩, hdf⟩ := hcrit.1.canDecide b
    cases hmtr with
    | refl =>
      obtain ⟨r, hr_dec⟩ := hdf
      have hact_r := hall_act r
      simp only [Config.Active, hr_dec, reduceCtorEq] at hact_r
    | @stepL _ p u ps' _ htr hrest =>
      rw [← htr.2] at hrest
      have hcan_p : π.CanDecide (π.step p cstar) b := ⟨cf, ⟨ps', hrest⟩, hdf⟩
      refine ⟨p, hcan_p, fun hcan_opp => hcrit.2 p htr.1 ?_⟩
      cases b
      exacts [⟨hcan_p, hcan_opp⟩, ⟨hcan_opp, hcan_p⟩]
  obtain ⟨p, hp⟩ := hex_step false
  obtain ⟨q, hq⟩ := hex_step true
  exact ⟨cstar, p, q, hreach, hcrit, hall_act, fun h => hq.2 (h ▸ hp.1), hp, hq⟩

end Bivalence

end Protocol

end Cslib.Distributed.SharedMemory
