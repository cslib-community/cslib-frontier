/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Lamport's Bakery Algorithm over Safe Overlapping Reads

This module formalizes Lamport's `P`-process Bakery mutual-exclusion algorithm ([Lamport1974],
pp. 453–455) as a fine-grained labelled transition system (`Cslib.LTS`) over single-writer
**safe registers** `choosing : P → Bool` and `number : P → ℕ` without atomic read-modify-write
primitives or atomic multi-reader register hardware.

Every register write is split into an initiation step (entering a mid-write phase) and a completion
step, and processes may also fail into a transient `.failed` phase ([Lamport1974], p. 454) before
recovering to `.remainder` with `choosing[p] = false` and `number[p] = 0`:

* While `p` is mid-write on `choosing[p]` (`.writeChoosingTrue`, `.writeChoosingFalse`) or in
  `.failed`, a concurrent read of `choosing[p]` may nondeterministically return **any** `Bool`
  value (`BakeryState.SafeReadChoosing`).
* While `p` is mid-write on `number[p]` (`.writeNumber`, `.writeNumberZero`) or in `.failed`, a
  concurrent read of `number[p]` may nondeterministically return **any** `ℕ` value
  (`BakeryState.SafeReadNumber`).
* During the doorway maximum calculation (`L1`), a process scans `number[j]` across `j : P` in any
  order (`BakeryPhase.readMax`).

## Main definitions

* `Cslib.Distributed.MutualExclusion.BakeryPhase`: per-process control state covering remainder,
  split-phase doorway writes and arbitrary-order ticket reads, `L2`/`L3` waiting polls, critical
  section, split-phase exit reset, and transient failure.
* `Cslib.Distributed.MutualExclusion.BakeryState`: global configuration `(phase, choosing, number)`
  with state predicates `isWritingChoosing`, `isWritingNumber`, `SafeReadChoosing`,
  `SafeReadNumber`, `inDoorway`, `inWaiting`, `inCS`, `inBakery`, `isTrying`,
  `beforeDoorwayScan`, `ticket`, `Reachable`, and `WeakFair`.
* `Cslib.Distributed.MutualExclusion.BakeryAction`: transition labels carrying the acting process
  and any nondeterministic safe-read value, plus `actor` and `NoFailAfter`.
* `Cslib.Distributed.MutualExclusion.bakeryStep?`,
  `Cslib.Distributed.MutualExclusion.bakeryStepTrace?`: computable single-step and multi-step
  transition evaluators.
* `Cslib.Distributed.MutualExclusion.bakeryLTS`: the `Cslib.LTS` of Lamport's Bakery algorithm.

## Main results

* `Cslib.Distributed.MutualExclusion.bakery_doorway_lt`: Lexicographic Doorway Ordering (variant of
  [Lamport1974], Assertion 1, p. 454) — if `p` is in the bakery before `q` begins its doorway ticket
  scan (`s₁.beforeDoorwayScan q`, whereas Assertion 1 starts before doorway entry and concludes the
  numeric inequality `number[p] < number[q]`) and `p` remains in the bakery until `q` enters the
  bakery, then `s₂.ticket p < s₂.ticket q`.
* `Cslib.Distributed.MutualExclusion.bakery_cs_lt`: Critical-Section Ticket Ordering ([Lamport1974],
  Assertion 2, pp. 454–455) — if `p` is in `CriticalSection` and `q ≠ p` is in the bakery in any
  reachable state, then `s.ticket p < s.ticket q`.
* `Cslib.Distributed.MutualExclusion.bakery_mutualExclusion`: Mutual Exclusion ([Lamport1974],
  p. 455) — in every reachable state (under arbitrary overlapping safe reads and mid-entry
  failures/halts), `s.inCS p → s.inCS q → p = q`.
* `Cslib.Distributed.MutualExclusion.bakery_fcfs`: First-Come-First-Served ([Lamport1974],
  p. 455) — if `p` completes its doorway before `q` begins its doorway scan, `q` cannot enter
  `CriticalSection` while `p` remains in its waiting section.
* `Cslib.Distributed.MutualExclusion.bakery_starvationFree`: Per-Process Starvation Freedom
  (per-process weak-fairness corollary following [Lamport1974], Assertion 3, p. 455) — whereas
  Assertion 3 states some-process progress under bounded failures, this theorem derives per-process
  `CriticalSection` entry under explicit weak per-process step fairness (`BakeryState.WeakFair`),
  bounded total failures (`BakeryAction.NoFailAfter`), and the target's no-failure premise.

## References

* [L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*][Lamport1974]
-/

public section

namespace Cslib.Distributed.MutualExclusion

open Cslib Cslib.ωSequence

/-- Control phase of a single process in Lamport's Bakery algorithm ([Lamport1974], p. 454). -/
inductive BakeryPhase (P : Type*) where
  /-- Noncritical remainder section (`choosing[p] = false`, `number[p] = 0`). -/
  | remainder
  /-- Doorway (`L1`): mid-write setting `choosing[p] := true`. -/
  | writeChoosingTrue
  /-- Doorway (`L1`): reading `number[j]` in arbitrary order (`scanned` read so far, max `acc`). -/
  | readMax (scanned : Finset P) (acc : ℕ)
  /-- Doorway (`L1`): mid-write setting `number[p] := nextTicket`. -/
  | writeNumber (nextTicket : ℕ)
  /-- Doorway (`L1`): mid-write resetting `choosing[p] := false` after `number[p]` is written. -/
  | writeChoosingFalse
  /-- Waiting loop (`L2`): polling `choosing[target]` until a safe read returns `false`. -/
  | waitL2 (checked : Finset P) (target : P)
  /-- Waiting loop (`L3`): polling `number[target]` until `0` or `(number[p], p)` has priority. -/
  | waitL3 (checked : Finset P) (target : P)
  /-- Critical section (`CS`). -/
  | cs
  /-- Exit section: mid-write resetting `number[p] := 0`. -/
  | writeNumberZero
  /-- Transient failure state ([Lamport1974], p. 454): concurrent reads of `p`'s registers may
  return arbitrary values until recovery resets `choosing[p] = false` and `number[p] = 0`. -/
  | failed
  deriving @[expose] DecidableEq

namespace BakeryPhase

variable {P : Type*}

/-- Boolean test for doorway phases (`L1`). -/
@[expose]
def isDoorway : BakeryPhase P → Bool
  | .writeChoosingTrue | .readMax _ _ | .writeNumber _ | .writeChoosingFalse => true
  | _ => false

/-- Boolean test for waiting-loop phases (`L2`/`L3`). -/
@[expose]
def isWaiting : BakeryPhase P → Bool
  | .waitL2 _ _ | .waitL3 _ _ => true
  | _ => false

/-- Boolean test for phases prior to starting the doorway ticket scan. -/
@[expose]
def isBeforeDoorwayScan : BakeryPhase P → Bool
  | .remainder | .writeChoosingTrue | .writeNumberZero | .failed => true
  | _ => false

end BakeryPhase

/-- Global configuration of Lamport's `P`-process Bakery algorithm ([Lamport1974], p. 454). -/
@[ext]
structure BakeryState (P : Type*) where
  /-- Per-process control phase. -/
  phase : P → BakeryPhase P
  /-- Last completed value of each process's doorway flag `choosing[p]`. -/
  choosing : P → Bool
  /-- Last completed value of each process's ticket register `number[p]`. -/
  number : P → ℕ

instance {P : Type*} [Fintype P] [DecidableEq P] : DecidableEq (BakeryState P) :=
  fun a b =>
    decidable_of_iff
      ((∀ p, a.phase p = b.phase p) ∧
        (∀ p, a.choosing p = b.choosing p) ∧
        (∀ p, a.number p = b.number p))
      ⟨fun ⟨hp, hc, hn⟩ => BakeryState.ext (funext hp) (funext hc) (funext hn),
        fun h => h ▸ ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩

namespace BakeryState

variable {P : Type*}

/-- Initial quiescent configuration with all processes in `.remainder` and all registers `0`. -/
@[expose]
def init (P : Type*) : BakeryState P where
  phase _ := .remainder
  choosing _ := false
  number _ := 0

/-- Whether `p` is mid-write (or transiently failing) on `choosing[p]`. -/
@[expose]
def isWritingChoosing (s : BakeryState P) (p : P) : Bool :=
  match s.phase p with
  | .writeChoosingTrue | .writeChoosingFalse | .failed => true
  | _ => false

/-- Whether `p` is mid-write (or transiently failing) on `number[p]`. -/
@[expose]
def isWritingNumber (s : BakeryState P) (p : P) : Bool :=
  match s.phase p with
  | .writeNumber _ | .writeNumberZero | .failed => true
  | _ => false

/-- Safe-register read relation for `choosing[j]` ([Lamport1974], p. 454): returns `s.choosing j`
when no write overlaps, and allows any `Bool` value during an overlapping write or failure. -/
@[expose]
def SafeReadChoosing (s : BakeryState P) (j : P) (val : Bool) : Prop :=
  s.isWritingChoosing j = true ∨ val = s.choosing j

/-- Safe-register read relation for `number[j]` ([Lamport1974], p. 454): returns `s.number j`
when no write overlaps, and allows any `ℕ` value during an overlapping write or failure. -/
@[expose]
def SafeReadNumber (s : BakeryState P) (j : P) (val : ℕ) : Prop :=
  s.isWritingNumber j = true ∨ val = s.number j

instance (s : BakeryState P) (j : P) (val : Bool) : Decidable (s.SafeReadChoosing j val) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (s : BakeryState P) (j : P) (val : ℕ) : Decidable (s.SafeReadNumber j val) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Process `p` is in the doorway (`L1`, prior to completing `choosing[p] := false`). -/
@[expose]
def inDoorway (s : BakeryState P) (p : P) : Prop :=
  (s.phase p).isDoorway = true

/-- Process `p` is in the `L2`/`L3` waiting loop. -/
@[expose]
def inWaiting (s : BakeryState P) (p : P) : Prop :=
  (s.phase p).isWaiting = true

/-- Process `p` is in its critical section (`CS`). -/
@[expose]
def inCS (s : BakeryState P) (p : P) : Prop :=
  s.phase p = .cs

/-- Process `p` is *in the bakery* ([Lamport1974], p. 454): from completing `choosing[p] := false`
until leaving its critical section or failing. -/
@[expose]
def inBakery (s : BakeryState P) (p : P) : Prop :=
  s.inWaiting p ∨ s.inCS p

/-- Process `p` is trying to enter its critical section (in the doorway or waiting loop). -/
@[expose]
def isTrying (s : BakeryState P) (p : P) : Prop :=
  s.inDoorway p ∨ s.inWaiting p

/-- Process `q` has not yet started scanning tickets in its current doorway (`remainder`,
`writeChoosingTrue`, `writeNumberZero`, or `failed`). -/
@[expose]
def beforeDoorwayScan (s : BakeryState P) (q : P) : Prop :=
  (s.phase q).isBeforeDoorwayScan = true

instance (s : BakeryState P) (p : P) : Decidable (s.inDoorway p) :=
  inferInstanceAs (Decidable (_ = true))

instance (s : BakeryState P) (p : P) : Decidable (s.inWaiting p) :=
  inferInstanceAs (Decidable (_ = true))

instance [DecidableEq P] (s : BakeryState P) (p : P) : Decidable (s.inCS p) :=
  inferInstanceAs (Decidable (s.phase p = .cs))

instance [DecidableEq P] (s : BakeryState P) (p : P) : Decidable (s.inBakery p) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (s : BakeryState P) (p : P) : Decidable (s.isTrying p) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (s : BakeryState P) (q : P) : Decidable (s.beforeDoorwayScan q) :=
  inferInstanceAs (Decidable (_ = true))

/-- Lexicographic pair `(s.number p, p)` ordered as in [Lamport1974], p. 454. -/
@[expose]
def ticket (s : BakeryState P) (p : P) : ℕ ×ₗ P :=
  toLex (s.number p, p)

@[simp]
theorem ticket_lt_iff [LT P] (s₁ s₂ : BakeryState P) (p q : P) :
    s₁.ticket p < s₂.ticket q ↔
      s₁.number p < s₂.number q ∨ s₁.number p = s₂.number q ∧ p < q :=
  Prod.Lex.lt_iff

@[simp]
theorem beforeDoorwayScan_of_remainder {s : BakeryState P} {q : P} (h : s.phase q = .remainder) :
    s.beforeDoorwayScan q := by
  simp [beforeDoorwayScan, BakeryPhase.isBeforeDoorwayScan, h]

theorem inBakery_of_inWaiting {s : BakeryState P} {p : P} (h : s.inWaiting p) : s.inBakery p :=
  Or.inl h

theorem inBakery_of_inCS {s : BakeryState P} {p : P} (h : s.inCS p) : s.inBakery p :=
  Or.inr h

end BakeryState

/-- Transition labels of Lamport's Bakery LTS, carrying the acting process and any safe-read
value observed during an overlapping read. -/
inductive BakeryAction (P : Type*) where
  /-- Process `p` leaves `.remainder` and begins writing `choosing[p] := true`. -/
  | enterDoorway (p : P)
  /-- Process `p` completes writing `choosing[p] := true` and begins scanning `number`. -/
  | finishChoosingTrue (p : P)
  /-- Process `p` reads `number[j]` (observing safe-read value `val`) during the doorway `max`. -/
  | readTicket (p j : P) (val : ℕ)
  /-- Process `p` finishes scanning all `j : P` and begins writing `number[p] := acc + 1`. -/
  | beginWriteNumber (p : P)
  /-- Process `p` completes writing `number[p]` and begins writing `choosing[p] := false`. -/
  | finishWriteNumber (p : P)
  /-- Process `p` completes writing `choosing[p] := false` and enters the waiting loop (`L2`). -/
  | finishChoosingFalse (p : P)
  /-- Process `p` polls `choosing[target]` at `L2`, observing safe-read value `val`. -/
  | pollChoosing (p : P) (val : Bool)
  /-- Process `p` polls `number[target]` at `L3`, observing safe-read value `val`. -/
  | pollNumber (p : P) (val : ℕ)
  /-- Process `p` leaves `CriticalSection` and begins resetting `number[p] := 0`. -/
  | exitCS (p : P)
  /-- Process `p` completes resetting `number[p] := 0` and returns to `.remainder`. -/
  | finishResetNumber (p : P)
  /-- Process `p` fails into transient `.failed` state ([Lamport1974], p. 454). -/
  | fail (p : P)
  /-- Process `p` recovers from `.failed` to `.remainder` with zeroed registers. -/
  | recover (p : P)
  /-- Stuttering step leaving the global state unchanged. -/
  | stutter
  deriving @[expose] DecidableEq

namespace BakeryAction

variable {P : Type*}

/-- Acting process of a `BakeryAction` (`none` for `.stutter`). -/
@[expose]
def actor : BakeryAction P → Option P
  | .enterDoorway p | .finishChoosingTrue p | .readTicket p _ _ | .beginWriteNumber p
  | .finishWriteNumber p | .finishChoosingFalse p | .pollChoosing p _ | .pollNumber p _
  | .exitCS p | .finishResetNumber p | .fail p | .recover p => some p
  | .stutter => none

/-- Bounded-failure condition ([Lamport1974], Assertion 3, p. 455): no `.fail` action occurs at or
after step index `N`. -/
@[expose]
def NoFailAfter (μs : ωSequence (BakeryAction P)) (N : ℕ) : Prop :=
  ∀ k ≥ N, ∀ q, μs k ≠ .fail q

end BakeryAction

/-- Computable single-step transition function of Lamport's Bakery algorithm over safe registers. -/
@[expose]
def bakeryStep? {P : Type*} [Fintype P] [LinearOrder P]
    (s : BakeryState P) (μ : BakeryAction P) : Option (BakeryState P) :=
  match μ with
  | .enterDoorway p =>
    if s.phase p = .remainder then
      some { s with phase := Function.update s.phase p .writeChoosingTrue }
    else none
  | .finishChoosingTrue p =>
    if s.phase p = .writeChoosingTrue then
      some { s with
        phase := Function.update s.phase p (.readMax ∅ 0)
        choosing := Function.update s.choosing p true }
    else none
  | .readTicket p j val =>
    match s.phase p with
    | .readMax scanned acc =>
      if j ∉ scanned ∧ s.SafeReadNumber j val then
        let phase' := Function.update s.phase p (.readMax (insert j scanned) (max acc val))
        some { s with phase := phase' }
      else none
    | _ => none
  | .beginWriteNumber p =>
    match s.phase p with
    | .readMax scanned acc =>
      if scanned = Finset.univ then
        some { s with phase := Function.update s.phase p (.writeNumber (acc + 1)) }
      else none
    | _ => none
  | .finishWriteNumber p =>
    match s.phase p with
    | .writeNumber nextTicket =>
      some { s with
        phase := Function.update s.phase p .writeChoosingFalse
        number := Function.update s.number p nextTicket }
    | _ => none
  | .finishChoosingFalse p =>
    if s.phase p = .writeChoosingFalse then
      let firstTarget := (Finset.univ : Finset P).min' ⟨p, Finset.mem_univ p⟩
      some { s with
        phase := Function.update s.phase p (.waitL2 ∅ firstTarget)
        choosing := Function.update s.choosing p false }
    else none
  | .pollChoosing p val =>
    match s.phase p with
    | .waitL2 checked target =>
      if s.SafeReadChoosing target val then
        if val then some s
        else some { s with phase := Function.update s.phase p (.waitL3 checked target) }
      else none
    | _ => none
  | .pollNumber p val =>
    match s.phase p with
    | .waitL3 checked target =>
      if s.SafeReadNumber target val then
        if val ≠ 0 ∧ toLex (val, target) < s.ticket p then
          some s
        else
          let checked' := insert target checked
          if hrem : (Finset.univ \ checked').Nonempty then
            let nextTarget := (Finset.univ \ checked').min' hrem
            some { s with phase := Function.update s.phase p (.waitL2 checked' nextTarget) }
          else
            some { s with phase := Function.update s.phase p .cs }
      else none
    | _ => none
  | .exitCS p =>
    if s.phase p = .cs then
      some { s with phase := Function.update s.phase p .writeNumberZero }
    else none
  | .finishResetNumber p =>
    if s.phase p = .writeNumberZero then
      some { s with
        phase := Function.update s.phase p .remainder
        number := Function.update s.number p 0 }
    else none
  | .fail p =>
    some { s with phase := Function.update s.phase p .failed }
  | .recover p =>
    if s.phase p = .failed then
      some { s with
        phase := Function.update s.phase p .remainder
        choosing := Function.update s.choosing p false
        number := Function.update s.number p 0 }
    else none
  | .stutter => some s

/-- Computable multi-step trace evaluator for `bakeryStep?`. -/
@[expose]
def bakeryStepTrace? {P : Type*} [Fintype P] [LinearOrder P]
    (s : BakeryState P) : List (BakeryAction P) → Option (BakeryState P)
  | [] => some s
  | μ :: μs => (bakeryStep? s μ).bind (fun s' => bakeryStepTrace? s' μs)

/-- Labelled transition system of Lamport's `P`-process Bakery algorithm ([Lamport1974]). -/
@[expose]
def bakeryLTS (P : Type*) [Fintype P] [LinearOrder P] : LTS (BakeryState P) (BakeryAction P) where
  Tr s μ s' := bakeryStep? s μ = some s'

theorem bakeryStepTrace?_eq_some_iff {P : Type*} [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μs : List (BakeryAction P)} :
    bakeryStepTrace? s μs = some s' ↔ (bakeryLTS P).MTr s μs s' := by
  induction μs generalizing s with
  | nil => simp [bakeryStepTrace?]
  | cons μ μs ih =>
    simp only [bakeryStepTrace?, Option.bind_eq_some_iff, LTS.MTr.cons_iff]
    exact exists_congr fun s₁ => and_congr_right fun _ => ih

namespace BakeryState

variable {P : Type*}

/-- A `BakeryState` is reachable if it is reachable from `BakeryState.init P` in `bakeryLTS P`. -/
@[expose]
def Reachable [Fintype P] [LinearOrder P] (s : BakeryState P) : Prop :=
  (bakeryLTS P).CanReach (BakeryState.init P) s

theorem Reachable.init [Fintype P] [LinearOrder P] : (BakeryState.init P).Reachable :=
  LTS.CanReach.refl (bakeryLTS P) (BakeryState.init P)

theorem Reachable.step [Fintype P] [LinearOrder P] {s s' : BakeryState P} {μ : BakeryAction P}
    (hr : s.Reachable) (htr : (bakeryLTS P).Tr s μ s') : s'.Reachable :=
  hr.elim fun μs hmtr => ⟨μs ++ [μ], hmtr.stepR (bakeryLTS P) htr⟩

theorem Reachable.mTr [Fintype P] [LinearOrder P] {s s' : BakeryState P}
    {μs : List (BakeryAction P)} (hr : s.Reachable) (hmtr : (bakeryLTS P).MTr s μs s') :
    s'.Reachable :=
  hr.elim fun μs₀ hmtr₀ => ⟨μs₀ ++ μs, hmtr₀.comp (bakeryLTS P) hmtr⟩

/-- Weak per-process step fairness: every process that remains continuously outside `.remainder`
eventually executes a step (completing writes/recoveries, exiting `CS`, or polling in waiting). -/
@[expose]
def WeakFair (ss : ωSequence (BakeryState P)) (μs : ωSequence (BakeryAction P)) : Prop :=
  ∀ q i, (∀ k ≥ i, (ss k).phase q ≠ .remainder) → ∃ k ≥ i, (μs k).actor = some q

end BakeryState

/-! ### Internal transition structure and inductive invariants -/

variable {P : Type*}

/-- Canonical case decomposition of `bakeryStep? s μ = some s'`, indexed by `μ.actor`. -/
private inductive BakeryStepShape [Fintype P] [LinearOrder P] (s : BakeryState P) :
    Option P → BakeryAction P → BakeryState P → Prop where
  | enter (p : P) :
      s.phase p = .remainder →
      BakeryStepShape s (some p) (.enterDoorway p)
        { s with phase := Function.update s.phase p .writeChoosingTrue }
  | finishChTrue (p : P) :
      s.phase p = .writeChoosingTrue →
      BakeryStepShape s (some p) (.finishChoosingTrue p)
        { s with
          phase := Function.update s.phase p (.readMax ∅ 0)
          choosing := Function.update s.choosing p true }
  | readTk (p j : P) (val : ℕ) (sc : Finset P) (ac : ℕ) :
      s.phase p = .readMax sc ac → j ∉ sc → s.SafeReadNumber j val →
      BakeryStepShape s (some p) (.readTicket p j val)
        { s with phase := Function.update s.phase p (.readMax (insert j sc) (max ac val)) }
  | beginNum (p : P) (sc : Finset P) (ac : ℕ) :
      s.phase p = .readMax sc ac → sc = Finset.univ →
      BakeryStepShape s (some p) (.beginWriteNumber p)
        { s with phase := Function.update s.phase p (.writeNumber (ac + 1)) }
  | finishNum (p : P) (nt : ℕ) :
      s.phase p = .writeNumber nt →
      BakeryStepShape s (some p) (.finishWriteNumber p)
        { s with
          phase := Function.update s.phase p .writeChoosingFalse
          number := Function.update s.number p nt }
  | finishChFalse (p tg : P) :
      s.phase p = .writeChoosingFalse →
      BakeryStepShape s (some p) (.finishChoosingFalse p)
        { s with
          phase := Function.update s.phase p (.waitL2 ∅ tg)
          choosing := Function.update s.choosing p false }
  | pollChSpin (p : P) (ch : Finset P) (tg : P) :
      s.phase p = .waitL2 ch tg → s.SafeReadChoosing tg true →
      BakeryStepShape s (some p) (.pollChoosing p true) s
  | pollChPass (p : P) (ch : Finset P) (tg : P) :
      s.phase p = .waitL2 ch tg → s.SafeReadChoosing tg false →
      BakeryStepShape s (some p) (.pollChoosing p false)
        { s with phase := Function.update s.phase p (.waitL3 ch tg) }
  | pollNumSpin (p : P) (val : ℕ) (ch : Finset P) (tg : P) :
      s.phase p = .waitL3 ch tg → s.SafeReadNumber tg val →
      val ≠ 0 ∧ toLex (val, tg) < s.ticket p →
      BakeryStepShape s (some p) (.pollNumber p val) s
  | pollNumNext (p : P) (val : ℕ) (ch : Finset P) (tg tg' : P) :
      s.phase p = .waitL3 ch tg → s.SafeReadNumber tg val →
      ¬ (val ≠ 0 ∧ toLex (val, tg) < s.ticket p) → tg' ∉ insert tg ch →
      BakeryStepShape s (some p) (.pollNumber p val)
        { s with phase := Function.update s.phase p (.waitL2 (insert tg ch) tg') }
  | pollNumCS (p : P) (val : ℕ) (ch : Finset P) (tg : P) :
      s.phase p = .waitL3 ch tg → s.SafeReadNumber tg val →
      ¬ (val ≠ 0 ∧ toLex (val, tg) < s.ticket p) → (∀ x, x ∈ insert tg ch) →
      BakeryStepShape s (some p) (.pollNumber p val)
        { s with phase := Function.update s.phase p .cs }
  | exit (p : P) :
      s.phase p = .cs →
      BakeryStepShape s (some p) (.exitCS p)
        { s with phase := Function.update s.phase p .writeNumberZero }
  | finishReset (p : P) :
      s.phase p = .writeNumberZero →
      BakeryStepShape s (some p) (.finishResetNumber p)
        { s with
          phase := Function.update s.phase p .remainder
          number := Function.update s.number p 0 }
  | fail (p : P) :
      BakeryStepShape s (some p) (.fail p) { s with phase := Function.update s.phase p .failed }
  | recover (p : P) :
      s.phase p = .failed →
      BakeryStepShape s (some p) (.recover p)
        { s with
          phase := Function.update s.phase p .remainder
          choosing := Function.update s.choosing p false
          number := Function.update s.number p 0 }
  | stutter :
      BakeryStepShape s none .stutter s

private theorem bakeryStepShape_of_step [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P}
    (htr : bakeryStep? s μ = some s') : BakeryStepShape s μ.actor μ s' := by
  cases μ with
  | enterDoorway p | finishChoosingTrue p | finishChoosingFalse p | exitCS p
  | finishResetNumber p | recover p =>
    simp only [bakeryStep?] at htr
    split at htr <;> simp only [Option.some.injEq, reduceCtorEq] at htr
    subst htr; constructor; assumption
  | readTicket p j val =>
    simp only [bakeryStep?] at htr
    cases hph : s.phase p <;> simp only [hph, reduceCtorEq] at htr
    split at htr <;> simp only [Option.some.injEq, reduceCtorEq] at htr
    rename_i hcond; subst htr; exact .readTk p j val _ _ hph hcond.1 hcond.2
  | beginWriteNumber p =>
    simp only [bakeryStep?] at htr
    cases hph : s.phase p <;> simp only [hph, reduceCtorEq] at htr
    split at htr <;> simp only [Option.some.injEq, reduceCtorEq] at htr
    rename_i huniv; subst htr; exact .beginNum p _ _ hph huniv
  | finishWriteNumber p =>
    simp only [bakeryStep?] at htr
    cases hph : s.phase p <;> simp only [hph, Option.some.injEq, reduceCtorEq] at htr
    subst htr; exact .finishNum p _ hph
  | pollChoosing p val =>
    simp only [bakeryStep?] at htr
    cases hph : s.phase p <;> simp only [hph, reduceCtorEq] at htr
    split at htr; swap; · simp at htr
    rename_i hsafe
    cases val <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at htr <;> subst htr
    · exact .pollChPass p _ _ hph hsafe
    · exact .pollChSpin p _ _ hph hsafe
  | pollNumber p val =>
    simp only [bakeryStep?] at htr
    cases hph : s.phase p <;> simp only [hph, reduceCtorEq] at htr
    split at htr; swap; · simp at htr
    rename_i hsafe
    split at htr
    · rename_i hspin; simp only [Option.some.injEq] at htr; subst htr
      exact .pollNumSpin p val _ _ hph hsafe hspin
    · rename_i hnspin
      split at htr <;> simp only [Option.some.injEq] at htr
      · rename_i hrem; subst htr
        exact .pollNumNext p val _ _ _ hph hsafe hnspin
          (Finset.mem_sdiff.mp (Finset.min'_mem _ hrem)).2
      · rename_i hnrem; subst htr
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hnrem
        exact .pollNumCS p val _ _ hph hsafe hnspin fun x => hnrem (Finset.mem_univ x)
  | fail p =>
    simp only [bakeryStep?, Option.some.injEq] at htr
    subst htr; exact .fail p
  | stutter =>
    simp only [bakeryStep?, Option.some.injEq] at htr
    subst htr; exact .stutter

private theorem bakeryActorStep_of_step [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {q : P}
    (htr : bakeryStep? s μ = some s') (hact : μ.actor = some q) :
    BakeryStepShape s (some q) μ s' :=
  hact ▸ bakeryStepShape_of_step htr

private theorem step_actor_frame [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} (htr : bakeryStep? s μ = some s')
    {q : P} (hq : μ.actor ≠ some q) :
    s'.phase q = s.phase q ∧ s'.choosing q = s.choosing q ∧ s'.number q = s.number q := by
  have hsh := bakeryStepShape_of_step htr
  generalize hoa : μ.actor = oa at hsh hq
  cases hsh <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | (simp only [ne_eq, Option.some.injEq] at hq
       simp [Function.update_of_ne (Ne.symm hq)])

private def passedL2 (s : BakeryState P) (i k : P) : Prop :=
  match s.phase i with
  | .waitL2 checked _ => k ∈ checked
  | .waitL3 checked target => k ∈ checked ∨ target = k
  | .cs => True
  | _ => False

private def passedL3 (s : BakeryState P) (i k : P) : Prop :=
  match s.phase i with
  | .waitL2 checked _ => k ∈ checked
  | .waitL3 checked _ => k ∈ checked
  | .cs => True
  | _ => False

private theorem passedL2_of_passedL3 {s : BakeryState P} {i k : P} (h : passedL3 s i k) :
    passedL2 s i k := by
  unfold passedL3 passedL2 at *
  cases hph : s.phase i <;> simp_all

private theorem inBakery_of_passedL2 {s : BakeryState P} {i k : P} (h : passedL2 s i k) :
    s.inBakery i := by
  unfold passedL2 BakeryState.inBakery BakeryState.inWaiting BakeryState.inCS
    BakeryPhase.isWaiting at *
  cases hph : s.phase i <;> simp_all

private structure LocalInv (s : BakeryState P) (i : P) : Prop where
  rem : s.phase i = .remainder → s.choosing i = false ∧ s.number i = 0
  readMax : ∀ scanned acc, s.phase i = .readMax scanned acc → s.choosing i = true
  writeNumber : ∀ nextTicket,
    s.phase i = .writeNumber nextTicket → s.choosing i = true ∧ 0 < nextTicket
  writeChoosingFalse : s.phase i = .writeChoosingFalse → 0 < s.number i
  waitL2 : ∀ checked target, s.phase i = .waitL2 checked target →
    s.choosing i = false ∧ 0 < s.number i ∧ target ∉ checked
  waitL3 : ∀ checked target, s.phase i = .waitL3 checked target →
    s.choosing i = false ∧ 0 < s.number i ∧ target ∉ checked
  cs : s.phase i = .cs → s.choosing i = false ∧ 0 < s.number i
  writeNumberZero : s.phase i = .writeNumberZero → s.choosing i = false

private theorem localInv_number_pos_of_inBakery {s : BakeryState P} {i : P}
    (hl : LocalInv s i) (hb : s.inBakery i) : 0 < s.number i := by
  unfold BakeryState.inBakery BakeryState.inWaiting BakeryState.inCS BakeryPhase.isWaiting at hb
  cases hph : s.phase i with
  | waitL2 checked target => exact (hl.waitL2 checked target hph).2.1
  | waitL3 checked target => exact (hl.waitL3 checked target hph).2.1
  | cs => exact (hl.cs hph).2
  | _ => simp [hph] at hb

private theorem localInv_choosing_false_of_inWaiting {s : BakeryState P} {i : P}
    (hl : LocalInv s i) (hw : s.inWaiting i) : s.choosing i = false := by
  unfold BakeryState.inWaiting BakeryPhase.isWaiting at hw
  cases hph : s.phase i with
  | waitL2 checked target => exact (hl.waitL2 checked target hph).1
  | waitL3 checked target => exact (hl.waitL3 checked target hph).1
  | _ => simp [hph] at hw

private theorem isWritingNumber_false_of_inBakery {s : BakeryState P} {i : P}
    (hb : s.inBakery i) : s.isWritingNumber i = false := by
  unfold BakeryState.inBakery BakeryState.inWaiting BakeryState.inCS
    BakeryPhase.isWaiting BakeryState.isWritingNumber at *
  cases hph : s.phase i <;> simp_all

private theorem isWritingChoosing_false_of_inWaiting {s : BakeryState P} {i : P}
    (hw : s.inWaiting i) : s.isWritingChoosing i = false := by
  unfold BakeryState.inWaiting BakeryPhase.isWaiting BakeryState.isWritingChoosing at *
  cases hph : s.phase i <;> simp_all

private structure BakeryInv [Fintype P] [LinearOrder P] (s : BakeryState P) : Prop where
  local_inv : ∀ i, LocalInv s i
  l2_scan : ∀ i k, i ≠ k → passedL2 s i k →
    (∀ scanned acc, s.phase k = .readMax scanned acc → i ∈ scanned → s.number i ≤ acc) ∧
    (∀ nextTicket, s.phase k = .writeNumber nextTicket → s.number i < nextTicket)
  l3_ticket : ∀ i k, i ≠ k → passedL3 s i k →
    (s.phase k = .writeChoosingFalse ∨ s.inBakery k) → s.ticket i < s.ticket k

private theorem bakeryInv_init [Fintype P] [LinearOrder P] :
    BakeryInv (BakeryState.init P) where
  local_inv _ := by constructor <;> simp [BakeryState.init]
  l2_scan _ _ _ h := by simp [passedL2, BakeryState.init] at h
  l3_ticket _ _ _ h := by simp [passedL3, BakeryState.init] at h

private theorem localInv_of_eq {s s' : BakeryState P} {i : P} (hl : LocalInv s i)
    (hph : s'.phase i = s.phase i) (hch : s'.choosing i = s.choosing i)
    (hnum : s'.number i = s.number i) : LocalInv s' i where
  rem h := by rw [hch, hnum]; exact hl.rem (hph ▸ h)
  readMax sc ac h := by rw [hch]; exact hl.readMax sc ac (hph ▸ h)
  writeNumber nt h := by rw [hch]; exact hl.writeNumber nt (hph ▸ h)
  writeChoosingFalse h := by rw [hnum]; exact hl.writeChoosingFalse (hph ▸ h)
  waitL2 ch tg h := by rw [hch, hnum]; exact hl.waitL2 ch tg (hph ▸ h)
  waitL3 ch tg h := by rw [hch, hnum]; exact hl.waitL3 ch tg (hph ▸ h)
  cs h := by rw [hch, hnum]; exact hl.cs (hph ▸ h)
  writeNumberZero h := by rw [hch]; exact hl.writeNumberZero (hph ▸ h)

private def localPhaseInv (s : BakeryState P) (i : P) : Prop :=
  match s.phase i with
  | .remainder => s.choosing i = false ∧ s.number i = 0
  | .readMax _ _ => s.choosing i = true
  | .writeNumber nextTicket => s.choosing i = true ∧ 0 < nextTicket
  | .writeChoosingFalse => 0 < s.number i
  | .waitL2 checked target | .waitL3 checked target =>
      s.choosing i = false ∧ 0 < s.number i ∧ target ∉ checked
  | .cs => s.choosing i = false ∧ 0 < s.number i
  | .writeNumberZero => s.choosing i = false
  | .writeChoosingTrue | .failed => True

private theorem localInv_of_phaseInv {s : BakeryState P} {i : P}
    (h : localPhaseInv s i) : LocalInv s i := by
  unfold localPhaseInv at h
  constructor <;> intros <;> rename_i hph <;> rwa [hph] at h

private theorem localInv_preserved [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} (hinv : ∀ i, LocalInv s i)
    (htr : bakeryStep? s μ = some s') (i : P) : LocalInv s' i := by
  by_cases hact : μ.actor = some i
  · apply localInv_of_phaseInv
    cases bakeryActorStep_of_step htr hact with
    | enter | finishChTrue | fail | recover => simp [localPhaseInv]
    | readTk _ _ _ sc ac hph | beginNum _ sc ac hph =>
      simp [localPhaseInv, (hinv i).readMax sc ac hph]
    | finishNum _ nt hph => simp [localPhaseInv, ((hinv i).writeNumber nt hph).2]
    | finishChFalse _ _ hph => simp [localPhaseInv, (hinv i).writeChoosingFalse hph]
    | pollChSpin _ ch tg hph => simp [localPhaseInv, hph, (hinv i).waitL2 ch tg hph]
    | pollChPass _ ch tg hph => simp [localPhaseInv, (hinv i).waitL2 ch tg hph]
    | pollNumSpin _ _ ch tg hph => simp [localPhaseInv, hph, (hinv i).waitL3 ch tg hph]
    | pollNumNext _ _ ch tg tg' hph _ _ hnot =>
      obtain ⟨hch, hpos, _⟩ := (hinv i).waitL3 ch tg hph
      unfold localPhaseInv; dsimp only; rw [Function.update_self]
      exact ⟨hch, hpos, hnot⟩
    | pollNumCS _ _ ch tg hph =>
      obtain ⟨hch, hpos, _⟩ := (hinv i).waitL3 ch tg hph
      simp [localPhaseInv, hch, hpos]
    | exit _ hph => simp [localPhaseInv, ((hinv i).cs hph).1]
    | finishReset _ hph => simp [localPhaseInv, (hinv i).writeNumberZero hph]
  · obtain ⟨hph, hch, hnum⟩ := step_actor_frame htr hact
    exact localInv_of_eq (hinv i) hph hch hnum

private theorem passedL2_congr {s s' : BakeryState P} {i k : P} (hph : s'.phase i = s.phase i) :
    passedL2 s' i k ↔ passedL2 s i k := by
  simp [passedL2, hph]

private theorem passedL3_congr {s s' : BakeryState P} {i k : P} (hph : s'.phase i = s.phase i) :
    passedL3 s' i k ↔ passedL3 s i k := by
  simp [passedL3, hph]

private theorem inBakery_congr {s s' : BakeryState P} {k : P} (hph : s'.phase k = s.phase k) :
    s'.inBakery k ↔ s.inBakery k := by
  simp [BakeryState.inBakery, BakeryState.inWaiting, BakeryState.inCS, hph]

private theorem bakeryInv_step [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P}
    (hinv : BakeryInv s) (htr : bakeryStep? s μ = some s') : BakeryInv s' := by
  have hloc' : ∀ i, LocalInv s' i := localInv_preserved hinv.local_inv htr
  refine ⟨hloc', ?_, ?_⟩
  · -- l2_scan
    intro i k hik hp2'
    by_cases hact_i : μ.actor = some i
    · obtain ⟨hph_k, _, _⟩ := step_actor_frame (q := k) htr (by rw [hact_i]; simp [hik])
      cases bakeryActorStep_of_step htr hact_i with
      | pollChSpin | pollNumSpin => exact hinv.l2_scan i k hik hp2'
      | pollChPass _ checked target hph hsafe =>
        simp only [passedL2, Function.update_self] at hp2'
        dsimp only at hph_k ⊢
        rw [hph_k]
        rcases hp2' with hmem | rfl
        · exact hinv.l2_scan i k hik (by simp [passedL2, hph, hmem])
        · refine ⟨fun sc ac hrm _ => ?_, fun nt hwn => ?_⟩
          · simp [BakeryState.SafeReadChoosing, BakeryState.isWritingChoosing, hrm,
              (hinv.local_inv target).readMax sc ac hrm] at hsafe
          · simp [BakeryState.SafeReadChoosing, BakeryState.isWritingChoosing, hwn,
              ((hinv.local_inv target).writeNumber nt hwn).1] at hsafe
      | pollNumNext _ _ checked target _ hph =>
        simp only [passedL2, Function.update_self, Finset.mem_insert] at hp2'
        dsimp only at hph_k ⊢
        rw [hph_k]
        exact hinv.l2_scan i k hik (by simpa [passedL2, hph, eq_comm, or_comm] using hp2')
      | pollNumCS _ _ checked target hph _ _ hall =>
        dsimp only at hph_k ⊢
        rw [hph_k]
        exact hinv.l2_scan i k hik
          (by simpa [passedL2, hph, eq_comm, or_comm] using Finset.mem_insert.mp (hall k))
      | _ => simp [passedL2] at hp2'
    · obtain ⟨hph_i, _, hnum_i⟩ := step_actor_frame htr hact_i
      have hp2 : passedL2 s i k := (passedL2_congr hph_i).mp hp2'
      by_cases hact_k : μ.actor = some k
      · cases bakeryActorStep_of_step htr hact_k with
        | readTk _ j val scanned acc hph_k _ hsafe =>
          refine ⟨fun sc ac h hmem => ?_, by simp⟩
          obtain ⟨rfl, rfl⟩ : insert j scanned = sc ∧ max acc val = ac := by simpa using h
          rcases Finset.mem_insert.mp hmem with rfl | hin
          · have hnwr := isWritingNumber_false_of_inBakery (inBakery_of_passedL2 hp2)
            simp only [BakeryState.SafeReadNumber, hnwr, Bool.false_eq_true, false_or] at hsafe
            subst hsafe; exact le_max_right _ _
          · exact le_trans ((hinv.l2_scan i k hik hp2).1 scanned acc hph_k hin) (le_max_left _ _)
        | beginNum _ scanned acc hph_k huniv =>
          refine ⟨by simp, fun nt h => ?_⟩
          obtain rfl : acc + 1 = nt := by simpa using h
          exact Nat.lt_succ_of_le
            ((hinv.l2_scan i k hik hp2).1 scanned acc hph_k (huniv ▸ Finset.mem_univ i))
        | pollChSpin _ _ _ hph_k | pollNumSpin _ _ _ _ hph_k => simp [hph_k]
        | _ => simp
      · obtain ⟨hph_k, _, _⟩ := step_actor_frame htr hact_k
        rw [hnum_i, hph_k]
        exact hinv.l2_scan i k hik hp2
  · -- l3_ticket
    intro i k hik hp3' hk_in'
    by_cases hact_i : μ.actor = some i
    · obtain ⟨hph_k, _, hnum_k⟩ :=
        step_actor_frame (q := k) htr (by rw [hact_i]; simp [hik])
      have hk_in : s.phase k = .writeChoosingFalse ∨ s.inBakery k := by
        rwa [hph_k, inBakery_congr hph_k] at hk_in'
      have hpass_lt : ∀ val checked target,
          s.phase i = .waitL3 checked target → s.SafeReadNumber target val →
          ¬ (val ≠ 0 ∧ toLex (val, target) < s.ticket i) →
          k ∈ insert target checked → s.ticket i < s.ticket k := by
        intro val checked target hph hsafe hpass hm
        rcases Finset.mem_insert.mp hm with rfl | hmem
        · have hnwr_k : s.isWritingNumber k = false :=
            hk_in.elim (fun h => by simp [BakeryState.isWritingNumber, h])
              isWritingNumber_false_of_inBakery
          have hpos_k : 0 < s.number k :=
            hk_in.elim (hinv.local_inv k).writeChoosingFalse
              (localInv_number_pos_of_inBakery (hinv.local_inv k))
          simp only [BakeryState.SafeReadNumber, hnwr_k, Bool.false_eq_true, false_or] at hsafe
          subst hsafe
          refine lt_of_le_of_ne (not_lt.mp fun hlt => hpass ⟨hpos_k.ne', hlt⟩) fun heq => ?_
          exact hik (Prod.ext_iff.mp (ofLex_inj.mpr heq)).2
        · exact hinv.l3_ticket i k hik (by simp [passedL3, hph, hmem]) hk_in
      cases bakeryActorStep_of_step htr hact_i with
      | pollChSpin | pollNumSpin => exact hinv.l3_ticket i k hik hp3' hk_in
      | pollChPass _ checked target hph =>
        simp only [passedL3, Function.update_self] at hp3'
        exact hinv.l3_ticket i k hik (by simp [passedL3, hph, hp3']) hk_in
      | pollNumNext _ val checked target _ hph hsafe hpass _ =>
        simp only [passedL3, Function.update_self] at hp3'
        exact hpass_lt val checked target hph hsafe hpass hp3'
      | pollNumCS _ val checked target hph hsafe hpass hall =>
        exact hpass_lt val checked target hph hsafe hpass (hall k)
      | _ => simp [passedL3] at hp3'
    · obtain ⟨hph_i, _, hnum_i⟩ := step_actor_frame htr hact_i
      have hp3 : passedL3 s i k := (passedL3_congr hph_i).mp hp3'
      by_cases hact_k : μ.actor = some k
      · cases bakeryActorStep_of_step htr hact_k with
        | finishNum _ nt h1 =>
          have hlt_num := (hinv.l2_scan i k hik (passedL2_of_passedL3 hp3)).2 nt h1
          simp only [BakeryState.ticket_lt_iff, Function.update_self, Function.update_of_ne hik]
          exact Or.inl hlt_num
        | finishChFalse _ _ h1 =>
          simpa [BakeryState.ticket, hnum_i] using hinv.l3_ticket i k hik hp3 (Or.inl h1)
        | pollChSpin | pollNumSpin => exact hinv.l3_ticket i k hik hp3 hk_in'
        | pollChPass _ _ _ h1 | pollNumNext _ _ _ _ _ h1 | pollNumCS _ _ _ _ h1 =>
          have hk_bak : s.inBakery k := by
            simp [BakeryState.inBakery, BakeryState.inWaiting, BakeryPhase.isWaiting, h1]
          simpa [BakeryState.ticket, hnum_i] using hinv.l3_ticket i k hik hp3 (Or.inr hk_bak)
        | _ =>
          simp [BakeryState.inBakery, BakeryState.inWaiting, BakeryState.inCS,
            BakeryPhase.isWaiting] at hk_in'
      · obtain ⟨hph_k, _, hnum_k⟩ := step_actor_frame htr hact_k
        have hk_in : s.phase k = .writeChoosingFalse ∨ s.inBakery k := by
          rwa [hph_k, inBakery_congr hph_k] at hk_in'
        simpa [BakeryState.ticket, hnum_i, hnum_k] using hinv.l3_ticket i k hik hp3 hk_in

private theorem BakeryState.Reachable.bakeryInv [Fintype P] [LinearOrder P] {s : BakeryState P}
    (hr : s.Reachable) : BakeryInv s := by
  obtain ⟨μs, hmtr⟩ := hr
  exact LTS.mtrInv_of_trInv (lts := bakeryLTS P) (fun _ _ _ htr hi => bakeryInv_step hi htr)
    _ _ _ hmtr bakeryInv_init

/-! ### Main safety and ordering theorems -/

/-- **Critical-Section Ticket Ordering** ([Lamport1974], Assertion 2, pp. 454–455): in any
reachable state `s`, if `p` is in its critical section, `q` is in the bakery, and `p ≠ q`, then
`p`'s ticket strictly precedes `q`'s ticket lexicographically. -/
theorem bakery_cs_lt [Fintype P] [LinearOrder P] {s : BakeryState P}
    (hr : s.Reachable) {p q : P} (hcs : s.inCS p) (hbak : s.inBakery q) (hne : p ≠ q) :
    s.ticket p < s.ticket q :=
  hr.bakeryInv.l3_ticket p q hne (by simp [passedL3, show s.phase p = .cs from hcs]) (Or.inr hbak)

/-- **Mutual Exclusion** ([Lamport1974], p. 455): in every reachable state of Lamport's Bakery
algorithm — even under arbitrary nondeterministic safe-register overlapping reads and mid-entry
failures or halts — at most one process is in `CriticalSection`. -/
theorem bakery_mutualExclusion [Fintype P] [LinearOrder P] {s : BakeryState P}
    (hr : s.Reachable) {p q : P} (hp : s.inCS p) (hq : s.inCS q) : p = q := by
  by_contra hne
  exact lt_asymm (bakery_cs_lt hr hp (.inr hq) hne) (bakery_cs_lt hr hq (.inr hp) (Ne.symm hne))

/-! ### Doorway ordering and First-Come-First-Served -/

private def doorwayAfter (n_p : ℕ) (p q : P) (s : BakeryState P) : Prop :=
  (∀ scanned acc, s.phase q = .readMax scanned acc → p ∈ scanned → n_p ≤ acc) ∧
  (∀ nextTicket, s.phase q = .writeNumber nextTicket → n_p < nextTicket) ∧
  ((s.phase q = .writeChoosingFalse ∨ s.inBakery q) → n_p < s.number q)

private theorem doorwayAfter_of_beforeDoorwayScan {n_p : ℕ} {p q : P} {s : BakeryState P}
    (hbef : s.beforeDoorwayScan q) : doorwayAfter n_p p q s := by
  unfold BakeryState.beforeDoorwayScan BakeryPhase.isBeforeDoorwayScan at hbef
  unfold doorwayAfter BakeryState.inBakery BakeryState.inWaiting BakeryState.inCS
    BakeryPhase.isWaiting
  cases hph : s.phase q <;> simp_all

private theorem inBakery_number_preserved [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {p : P}
    (htr : bakeryStep? s μ = some s') (_hb₁ : s.inBakery p) (_hb₂ : s'.inBakery p) :
    s'.number p = s.number p := by
  by_cases hact : μ.actor = some p
  · cases bakeryActorStep_of_step htr hact <;>
      simp_all [BakeryState.inBakery, BakeryState.inWaiting, BakeryState.inCS,
        BakeryPhase.isWaiting]
  · exact (step_actor_frame htr hact).2.2

private theorem doorwayAfter_step [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {p q : P}
    (htr : bakeryStep? s μ = some s')
    (hb₁ : s.inBakery p) (hb₂ : s'.inBakery p)
    (hda : doorwayAfter (s.number p) p q s) :
    doorwayAfter (s'.number p) p q s' := by
  have hnum_p : s'.number p = s.number p := inBakery_number_preserved htr hb₁ hb₂
  rw [hnum_p]
  by_cases hact : μ.actor = some q
  · cases bakeryActorStep_of_step htr hact with
    | readTk _ j val scanned acc hph _ hsafe =>
      refine ⟨fun sc ac h hmem => ?_, by simp,
        by simp [BakeryState.inBakery, BakeryState.inWaiting, BakeryState.inCS,
          BakeryPhase.isWaiting]⟩
      obtain ⟨rfl, rfl⟩ : insert j scanned = sc ∧ max acc val = ac := by simpa using h
      rcases Finset.mem_insert.mp hmem with rfl | hin
      · have hnwr := isWritingNumber_false_of_inBakery hb₁
        simp only [BakeryState.SafeReadNumber, hnwr, Bool.false_eq_true, false_or] at hsafe
        subst hsafe; exact le_max_right _ _
      · exact le_trans (hda.1 scanned acc hph hin) (le_max_left _ _)
    | beginNum _ scanned acc hph huniv =>
      refine ⟨by simp, fun nt h => ?_,
        by simp [BakeryState.inBakery, BakeryState.inWaiting, BakeryState.inCS,
          BakeryPhase.isWaiting]⟩
      obtain rfl : acc + 1 = nt := by simpa using h
      exact Nat.lt_succ_of_le (hda.1 scanned acc hph (huniv ▸ Finset.mem_univ p))
    | finishNum _ nextTicket hph =>
      exact ⟨by simp, by simp, fun _ => by
        simp only [Function.update_self]; exact hda.2.1 nextTicket hph⟩
    | finishChFalse _ _ hph =>
      exact ⟨by simp, by simp, fun _ => hda.2.2 (Or.inl hph)⟩
    | pollChSpin | pollNumSpin => exact hda
    | pollChPass _ _ _ hph | pollNumNext _ _ _ _ _ hph | pollNumCS _ _ _ _ hph =>
      have hq_bak : s.inBakery q := by
        simp [BakeryState.inBakery, BakeryState.inWaiting, BakeryPhase.isWaiting, hph]
      exact ⟨by simp, by simp, fun _ => hda.2.2 (Or.inr hq_bak)⟩
    | _ =>
      simp [doorwayAfter, BakeryState.inBakery, BakeryState.inWaiting, BakeryState.inCS,
        BakeryPhase.isWaiting]
  · obtain ⟨hph_q, _, hnum_q⟩ := step_actor_frame htr hact
    simpa only [doorwayAfter, hph_q, inBakery_congr hph_q, hnum_q] using hda

private theorem doorwayAfter_execution [Fintype P] [LinearOrder P]
    {s₁ s₂ : BakeryState P} {μs : List (BakeryAction P)} {sl : List (BakeryState P)}
    (hex : (bakeryLTS P).Execution s₁ μs s₂ sl)
    {p q : P} (hstay : ∀ s ∈ sl, s.inBakery p)
    (hda : doorwayAfter (s₁.number p) p q s₁) :
    doorwayAfter (s₂.number p) p q s₂ ∧ s₂.number p = s₁.number p := by
  induction hex with
  | refl => exact ⟨hda, rfl⟩
  | @stepL r s t μ μs ss htr hex' ih =>
    have hr_bak : r.inBakery p := hstay r List.mem_cons_self
    have hs_bak : s.inBakery p :=
      hstay s (List.mem_cons_of_mem r (hex'.head ▸ List.head_mem hex'.ss_ne_nil))
    obtain ⟨hda_t, hnum_st⟩ := ih (fun x hx => hstay x (List.mem_cons_of_mem r hx))
      (doorwayAfter_step htr hr_bak hs_bak hda)
    exact ⟨hda_t, hnum_st.trans (inBakery_number_preserved htr hr_bak hs_bak)⟩

/-- **Doorway Ordering Lemma** (lexicographic variant of [Lamport1974], Assertion 1, p. 454): if `p`
has entered the bakery (`s₁.inBakery p`) before `q` begins its doorway ticket scan
(`s₁.beforeDoorwayScan q`, in particular when `s₁.phase q = .remainder`), and `p` remains in the
bakery throughout an execution to `s₂` where `q` is also in the bakery (`s₂.inBakery q`), then
`s₂.ticket p < s₂.ticket q`.

Whereas Assertion 1 in [Lamport1974] (p. 454) starts before `q` enters the doorway and states the
numeric ticket inequality `number[p] < number[q]`, this lemma starts before `q`'s ticket scan and
states the induced lexicographic inequality `s₂.ticket p < s₂.ticket q`. -/
theorem bakery_doorway_lt [Fintype P] [LinearOrder P]
    {s₁ s₂ : BakeryState P} {μs : List (BakeryAction P)} {sl : List (BakeryState P)}
    (hex : (bakeryLTS P).Execution s₁ μs s₂ sl)
    {p q : P} (hstay : ∀ s ∈ sl, s.inBakery p)
    (hbef : s₁.beforeDoorwayScan q) (hq_bak : s₂.inBakery q) :
    s₂.ticket p < s₂.ticket q := by
  obtain ⟨hda, _⟩ := doorwayAfter_execution hex hstay (doorwayAfter_of_beforeDoorwayScan hbef)
  exact (BakeryState.ticket_lt_iff s₂ s₂ p q).mpr (Or.inl (hda.2.2 (Or.inr hq_bak)))

/-- **First-Come-First-Served** ([Lamport1974], p. 455): if `p` has completed its doorway and
remains in its waiting section throughout a reachable execution starting before `q` begins its
doorway scan (`s₁.beforeDoorwayScan q`), then `q` cannot enter `CriticalSection`. -/
theorem bakery_fcfs [Fintype P] [LinearOrder P]
    {s₁ s₂ : BakeryState P} {μs : List (BakeryAction P)} {sl : List (BakeryState P)}
    (hr₁ : s₁.Reachable) (hex : (bakeryLTS P).Execution s₁ μs s₂ sl)
    {p q : P} (hwait : ∀ s ∈ sl, s.inWaiting p)
    (hbef : s₁.beforeDoorwayScan q) :
    ¬ s₂.inCS q := by
  intro hcs_q
  have hstay : ∀ s ∈ sl, s.inBakery p := fun s hs => BakeryState.inBakery_of_inWaiting (hwait s hs)
  have hlt₁ := bakery_doorway_lt hex hstay hbef (BakeryState.inBakery_of_inCS hcs_q)
  have hp_bak := hstay s₂ (hex.getLast ▸ List.getLast_mem hex.ss_ne_nil)
  exact lt_asymm hlt₁ (bakery_cs_lt (hr₁.mTr hex.to_mTr) hcs_q hp_bak
    (fun heq => lt_irrefl _ (heq ▸ hlt₁)))

/-! ### Starvation-free liveness -/

private def nonBakeryMeasure [Fintype P] [DecidableEq P] : BakeryPhase P → ℕ
  | .failed => 1
  | .writeNumberZero => 1
  | .writeChoosingTrue => Fintype.card P + 4
  | .readMax scanned _ => (Finset.univ \ scanned).card + 3
  | .writeNumber _ => 2
  | .writeChoosingFalse => 1
  | .remainder | .waitL2 _ _ | .waitL3 _ _ | .cs => 0

private theorem phase_ne_remainder_of_nonBakeryMeasure_pos [Fintype P] [DecidableEq P]
    {ph : BakeryPhase P} (h : 0 < nonBakeryMeasure ph) : ph ≠ .remainder := by
  rintro rfl; simp [nonBakeryMeasure] at h

private theorem nonBakeryMeasure_eq_zero_iff [Fintype P] [DecidableEq P]
    {s : BakeryState P} {q : P} :
    nonBakeryMeasure (s.phase q) = 0 ↔ s.phase q = .remainder ∨ s.inBakery q := by
  unfold nonBakeryMeasure BakeryState.inBakery BakeryState.inWaiting BakeryState.inCS
    BakeryPhase.isWaiting
  cases hph : s.phase q <;> simp

private theorem sdiff_insert_card_lt [Fintype P] [DecidableEq P] {A : Finset P} {x : P}
    (hx : x ∉ A) : (Finset.univ \ insert x A).card < (Finset.univ \ A).card := by
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset (fun y hy => ?_) |>.mpr
    ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩, by simp⟩)
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1,
    fun hm => (Finset.mem_sdiff.mp hy).2 (Finset.mem_insert_of_mem hm)⟩

private theorem nonBakeryMeasure_step_lt [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {q : P}
    (htr : bakeryStep? s μ = some s') (hact : μ.actor = some q) (hnf : μ ≠ .fail q)
    (hpos : 0 < nonBakeryMeasure (s.phase q)) :
    nonBakeryMeasure (s'.phase q) < nonBakeryMeasure (s.phase q) := by
  cases bakeryActorStep_of_step htr hact with
  | readTk _ _ _ scanned acc hph hj_not =>
    simp only [Function.update_self, hph, nonBakeryMeasure]
    have := sdiff_insert_card_lt hj_not; omega
  | fail => exact absurd rfl hnf
  | _ => simp_all [nonBakeryMeasure]

/-- Under weak fairness, a measure on `q`'s phase that drops at each of `q`'s steps while positive
(and is unchanged by other processes' steps) eventually reaches zero, provided `q` is not in its
remainder section while the measure is positive. -/
private theorem exists_measure_zero [Fintype P] [LinearOrder P]
    {ss : ωSequence (BakeryState P)} {μs : ωSequence (BakeryAction P)}
    (hexec : (bakeryLTS P).OmegaExecution ss μs) (hfair : BakeryState.WeakFair ss μs)
    {q : P} (f : BakeryPhase P → ℕ) {i : ℕ}
    (hdec : ∀ k ≥ i, (μs k).actor = some q → 0 < f ((ss k).phase q) →
      f ((ss (k + 1)).phase q) < f ((ss k).phase q))
    (hrem : ∀ k ≥ i, 0 < f ((ss k).phase q) → (ss k).phase q ≠ .remainder) :
    ∃ k ≥ i, f ((ss k).phase q) = 0 := by
  suffices ∀ m j, i ≤ j → f ((ss j).phase q) ≤ m → ∃ k ≥ j, f ((ss k).phase q) = 0 from
    this _ i le_rfl le_rfl
  intro m
  induction m with
  | zero => exact fun j _ hm => ⟨j, le_rfl, Nat.eq_zero_of_le_zero hm⟩
  | succ m ih =>
    intro j hij hm
    by_cases hall : ∀ k ≥ j, 0 < f ((ss k).phase q)
    · have hstay : ∀ k ≥ j, f ((ss k).phase q) ≤ m + 1 := by
        intro k hjk
        induction k, hjk using Nat.le_induction with
        | base => exact hm
        | succ k hjk ihk =>
          by_cases hact : (μs k).actor = some q
          · have := hdec k (by omega) hact (hall k hjk); omega
          · rwa [(step_actor_frame (hexec k) hact).1]
      obtain ⟨k₀, hk₀_ge, hact₀⟩ := hfair q j fun k hk => hrem k (by omega) (hall k hk)
      have hlt := (hdec k₀ (by omega) hact₀ (hall k₀ hk₀_ge)).trans_le (hstay k₀ hk₀_ge)
      exact (ih (k₀ + 1) (by omega) (Nat.le_of_lt_succ hlt)).imp fun _ ⟨hk, h0⟩ => ⟨by omega, h0⟩
    · push Not at hall
      exact hall.imp fun _ ⟨hk, h0⟩ => ⟨hk, Nat.eq_zero_of_le_zero h0⟩

private theorem exists_nonBakeryMeasure_zero [Fintype P] [LinearOrder P]
    {ss : ωSequence (BakeryState P)} {μs : ωSequence (BakeryAction P)}
    (hexec : (bakeryLTS P).OmegaExecution ss μs)
    (hfair : BakeryState.WeakFair ss μs)
    {q : P} {i : ℕ} (hnf : ∀ k ≥ i, μs k ≠ .fail q) :
    ∃ k ≥ i, nonBakeryMeasure ((ss k).phase q) = 0 :=
  exists_measure_zero hexec hfair nonBakeryMeasure
    (fun k hk hact hpos => nonBakeryMeasure_step_lt (hexec k) hact (hnf k hk) hpos)
    fun _ _ => phase_ne_remainder_of_nonBakeryMeasure_pos

private theorem isTrying_step_of_not_cs [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {p : P}
    (htr : bakeryStep? s μ = some s') (hnf : μ ≠ .fail p)
    (htry : s.isTrying p) (hncs : ¬ s'.inCS p) :
    s'.isTrying p := by
  by_cases hact : μ.actor = some p
  · cases bakeryActorStep_of_step htr hact <;>
      simp_all [BakeryState.isTrying, BakeryState.inDoorway, BakeryState.inWaiting,
        BakeryState.inCS, BakeryPhase.isDoorway, BakeryPhase.isWaiting]
  · unfold BakeryState.isTrying BakeryState.inDoorway BakeryState.inWaiting at htry ⊢
    rwa [(step_actor_frame htr hact).1]

private theorem inWaiting_step_of_not_cs [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {p : P}
    (htr : bakeryStep? s μ = some s') (hnf : μ ≠ .fail p)
    (hw : s.inWaiting p) (hncs : ¬ s'.inCS p) :
    s'.inWaiting p ∧ s'.number p = s.number p := by
  by_cases hact : μ.actor = some p
  · cases bakeryActorStep_of_step htr hact <;>
      simp_all [BakeryState.inWaiting, BakeryState.inCS, BakeryPhase.isWaiting]
  · obtain ⟨hph, _, hnum⟩ := step_actor_frame htr hact
    unfold BakeryState.inWaiting at hw ⊢
    rw [hph]; exact ⟨hw, hnum⟩

private theorem beforeDoorwayScan_of_exit_bakery [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {q : P}
    (htr : bakeryStep? s μ = some s') (hnf : μ ≠ .fail q)
    (hbak : s.inBakery q) (hnbak : ¬ s'.inBakery q) :
    s'.beforeDoorwayScan q := by
  by_cases hact : μ.actor = some q
  · cases bakeryActorStep_of_step htr hact <;>
      simp_all [BakeryState.inBakery, BakeryState.inWaiting, BakeryState.inCS,
        BakeryState.beforeDoorwayScan, BakeryPhase.isWaiting, BakeryPhase.isBeforeDoorwayScan]
  · exact absurd ((inBakery_congr (step_actor_frame htr hact).1).mpr hbak) hnbak

private theorem step_cs_stays_of_inBakery [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {q : P}
    (htr : bakeryStep? s μ = some s') (hnf : μ ≠ .fail q)
    (hcs : s.phase q = .cs) (hbak' : s'.inBakery q) : s'.phase q = .cs := by
  by_cases hact : μ.actor = some q
  · cases bakeryActorStep_of_step htr hact <;>
      simp_all [BakeryState.inBakery, BakeryState.inWaiting, BakeryState.inCS,
        BakeryPhase.isWaiting]
  · exact (step_actor_frame htr hact).1.trans hcs

private theorem not_step_actor_from_staying_cs [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {q : P}
    (htr : bakeryStep? s μ = some s') (hact : μ.actor = some q) (hnf : μ ≠ .fail q)
    (hcs : s.phase q = .cs) (hcs' : s'.phase q = .cs) : False := by
  cases bakeryActorStep_of_step htr hact <;> simp_all

private theorem step_clean_reset_fail [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {r : P}
    (htr : bakeryStep? s μ = some s') (hnf_act : μ ≠ .fail r)
    (hncs : ¬ s.inCS r)
    (hcl : s.phase r ≠ .failed ∧ s.phase r ≠ .writeNumberZero) :
    s'.phase r ≠ .failed ∧ s'.phase r ≠ .writeNumberZero := by
  by_cases hact : μ.actor = some r
  · cases bakeryActorStep_of_step htr hact <;> simp_all [BakeryState.inCS]
  · rw [(step_actor_frame htr hact).1]; exact hcl

private theorem step_not_rem_of_clean [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {r : P}
    (htr : bakeryStep? s μ = some s') (hnf_act : μ ≠ .fail r)
    (hcl : s.phase r ≠ .failed ∧ s.phase r ≠ .writeNumberZero)
    (hnrem : s.phase r ≠ .remainder) :
    s'.phase r ≠ .remainder := by
  by_cases hact : μ.actor = some r
  · cases bakeryActorStep_of_step htr hact <;> simp_all
  · rw [(step_actor_frame htr hact).1]; exact hnrem

private theorem phase_rem_or_waiting_of_clean {s : BakeryState P} {r : P}
    (hndw : ¬ s.inDoorway r) (hncs : ¬ s.inCS r)
    (hcl : s.phase r ≠ .failed ∧ s.phase r ≠ .writeNumberZero) :
    s.phase r = .remainder ∨ s.inWaiting r := by
  unfold BakeryState.inDoorway BakeryPhase.isDoorway at hndw
  unfold BakeryState.inCS at hncs
  unfold BakeryState.inWaiting BakeryPhase.isWaiting
  cases hph : s.phase r <;> simp_all

private theorem exists_forall_eq_of_antitone_finset
    {f : ℕ → Finset P} {t₁ : ℕ} (hanti : ∀ k ≥ t₁, f (k + 1) ⊆ f k) :
    ∃ t ≥ t₁, ∀ k ≥ t, f k = f t := by
  suffices ∀ c t₁, (∀ k ≥ t₁, f (k + 1) ⊆ f k) → (f t₁).card = c →
      ∃ t ≥ t₁, ∀ k ≥ t, f k = f t from this _ t₁ hanti rfl
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro t₁ hanti hc
    by_cases hall : ∀ k ≥ t₁, f k = f t₁
    · exact ⟨t₁, le_rfl, hall⟩
    push Not at hall
    obtain ⟨k₀, hk₀, hne⟩ := hall
    have hsub : f k₀ ⊆ f t₁ := by
      clear hne
      induction k₀, hk₀ using Nat.le_induction with
      | base => exact Finset.Subset.refl _
      | succ k hk ihk => exact (hanti k hk).trans ihk
    obtain ⟨t, ht, hstab⟩ := ih _ (hc ▸ Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)) k₀ (fun k hk => hanti k (by omega)) rfl
    exact ⟨t, by omega, hstab⟩

private def waitMeasure [Fintype P] [DecidableEq P] : BakeryPhase P → ℕ
  | .waitL2 checked _ => 2 * (Finset.univ \ checked).card
  | .waitL3 checked _ => 2 * (Finset.univ \ checked).card - 1
  | _ => 0

private theorem waitMeasure_pos_of_inWaiting [Fintype P] [LinearOrder P]
    {s : BakeryState P} {q : P} (hl : LocalInv s q) (hw : s.inWaiting q) :
    0 < waitMeasure (s.phase q) := by
  unfold BakeryState.inWaiting BakeryPhase.isWaiting at hw
  cases hph : s.phase q with
  | waitL2 checked target =>
    have := sdiff_insert_card_lt (hl.waitL2 checked target hph).2.2
    simp only [waitMeasure]; omega
  | waitL3 checked target =>
    have := sdiff_insert_card_lt (hl.waitL3 checked target hph).2.2
    simp only [waitMeasure]; omega
  | _ => simp [hph] at hw

private theorem waitMeasure_step_lt_of_quiescent [Fintype P] [LinearOrder P]
    {s s' : BakeryState P} {μ : BakeryAction P} {q : P}
    (hl : ∀ r, LocalInv s r)
    (htr : bakeryStep? s μ = some s') (hact : μ.actor = some q) (hnf : μ ≠ .fail q)
    (hw : s.inWaiting q)
    (hquiesce : ∀ r, s.phase r = .remainder ∨ s.inWaiting r)
    (hmin : ∀ r, s.inWaiting r → r ≠ q → s.ticket q < s.ticket r) :
    waitMeasure (s'.phase q) < waitMeasure (s.phase q) := by
  have hnspin_of_wait : ∀ (val : ℕ) (target : P),
      s.SafeReadNumber target val → ¬ (val ≠ 0 ∧ toLex (val, target) < s.ticket q) := by
    intro val target hsafe ⟨hn0, hlt_tk⟩
    have hnwr_t : s.isWritingNumber target = false :=
      (hquiesce target).elim (fun h => by simp [BakeryState.isWritingNumber, h])
        (fun h => isWritingNumber_false_of_inBakery (BakeryState.inBakery_of_inWaiting h))
    simp only [BakeryState.SafeReadNumber, hnwr_t, Bool.false_eq_true, false_or] at hsafe
    subst hsafe
    rcases hquiesce target with ht_rem | ht_w
    · exact hn0 ((hl target).rem ht_rem).2
    · by_cases hteq : target = q
      · subst hteq; exact lt_irrefl _ hlt_tk
      · exact lt_asymm hlt_tk (hmin target ht_w hteq)
  cases bakeryActorStep_of_step htr hact with
  | pollChSpin _ _ target hph hsafe =>
    rcases hquiesce target with h | h
    · simp [BakeryState.SafeReadChoosing, BakeryState.isWritingChoosing, h,
        ((hl target).rem h).1] at hsafe
    · simp [BakeryState.SafeReadChoosing, isWritingChoosing_false_of_inWaiting h,
        localInv_choosing_false_of_inWaiting (hl target) h] at hsafe
  | pollChPass _ checked target hph =>
    have := sdiff_insert_card_lt ((hl q).waitL2 checked target hph).2.2
    simp only [Function.update_self, hph, waitMeasure]; omega
  | pollNumSpin _ val _ target _ hsafe hspin =>
    exact absurd hspin (hnspin_of_wait val target hsafe)
  | pollNumNext _ _ checked target _ hph | pollNumCS _ _ checked target hph =>
    have := sdiff_insert_card_lt ((hl q).waitL3 checked target hph).2.2
    simp only [Function.update_self, hph, waitMeasure]; omega
  | fail => exact absurd rfl hnf
  | _ => simp_all [BakeryState.inWaiting, BakeryPhase.isWaiting]

/-- **Per-Process Starvation Freedom** (weak-fairness corollary following [Lamport1974],
Assertion 3, p. 455): in any infinite execution from a reachable state under weak per-process step
fairness (`BakeryState.WeakFair`, under which processes in `CriticalSection` eventually exit and
in-progress writes/recoveries complete) and bounded total failures (`BakeryAction.NoFailAfter`),
every trying process `p` that never fails (`∀ k, μs k ≠ .fail p`) eventually enters
`CriticalSection`.

Whereas Assertion 3 in [Lamport1974] (p. 455) states bounded-failure progress for *some* process in
the bakery, this theorem formalizes the ensuing per-process lockout-freedom consequence under
explicit weak step fairness and `p`'s no-failure premise. -/
theorem bakery_starvationFree [Fintype P] [LinearOrder P]
    {ss : ωSequence (BakeryState P)} {μs : ωSequence (BakeryAction P)}
    (hreach : (ss 0).Reachable)
    (hexec : (bakeryLTS P).OmegaExecution ss μs)
    (hfair : BakeryState.WeakFair ss μs)
    {N : ℕ} (hbound : BakeryAction.NoFailAfter μs N)
    {p : P} (hp_nofail : ∀ k, μs k ≠ .fail p)
    (htry : (ss 0).isTrying p) :
    ∃ k, (ss k).inCS p := by
  by_contra! hno_cs
  have hreach_all : ∀ k, (ss k).Reachable := fun k =>
    hreach.mTr (hexec.extract_mTr (Nat.zero_le k))
  -- Step 1: `p` stays trying forever, so `p` finishes its doorway and enters `inWaiting` at
  -- `t₀ ≥ N`.
  have htry_all : ∀ k, (ss k).isTrying p := fun k => Nat.rec htry
    (fun k ih => isTrying_step_of_not_cs (hexec k) (hp_nofail k) ih (hno_cs (k + 1))) k
  obtain ⟨t₀, ht₀_ge, ht₀_zero⟩ := exists_nonBakeryMeasure_zero hexec hfair
    (q := p) (i := N) (fun k _ => hp_nofail k)
  have hw_t₀ : (ss t₀).inWaiting p := by
    rcases nonBakeryMeasure_eq_zero_iff.mp ht₀_zero with hrem | hbak
    · have ht := htry_all t₀
      simp [BakeryState.isTrying, BakeryState.inDoorway, BakeryState.inWaiting,
        BakeryPhase.isDoorway, BakeryPhase.isWaiting, hrem] at ht
    · exact hbak.resolve_right (hno_cs t₀)
  have hw_p : ∀ k ≥ t₀, (ss k).inWaiting p ∧ (ss k).number p = (ss t₀).number p :=
    fun k hk => Nat.le_induction ⟨hw_t₀, rfl⟩ (fun k _ ih =>
      have h := inWaiting_step_of_not_cs (hexec k) (hp_nofail k) ih.1 (hno_cs (k + 1))
      ⟨h.1, h.2.trans ih.2⟩) k hk
  -- Step 2: Wait for every process currently mid-doorway at `t₀` to finish its doorway/recovery.
  have hex_drain (q : P) : ∃ u ≥ t₀, (ss u).beforeDoorwayScan q ∨ (ss u).inBakery q :=
    (exists_nonBakeryMeasure_zero hexec hfair (q := q) (i := t₀)
      fun k hk => hbound k (by omega) q).imp fun _ ⟨hu, h0⟩ =>
        ⟨hu, (nonBakeryMeasure_eq_zero_iff.mp h0).imp_left
          BakeryState.beforeDoorwayScan_of_remainder⟩
  choose u_of hu_ge hu_prop using hex_drain
  let t₁ := Finset.univ.sup u_of ⊔ t₀
  have hda_from : ∀ q k, u_of q ≤ k →
      ((∀ j, u_of q ≤ j → j ≤ k → (ss j).inBakery q) ∨
        doorwayAfter ((ss t₀).number p) p q (ss k)) := by
    intro q k hk
    induction k, hk using Nat.le_induction with
    | base =>
      rcases hu_prop q with hbef | hbak
      · exact Or.inr (doorwayAfter_of_beforeDoorwayScan hbef)
      · exact Or.inl fun j hj₁ hj₂ => le_antisymm hj₂ hj₁ ▸ hbak
    | succ k hk ih =>
      have hu_ge_q := hu_ge q
      rcases ih with hall_bak | hda_k
      · by_cases hbak_next : (ss (k + 1)).inBakery q
        · exact Or.inl fun j hj₁ hj₂ =>
            (Nat.le_succ_iff.mp hj₂).elim (hall_bak j hj₁) fun h => h ▸ hbak_next
        · exact Or.inr (doorwayAfter_of_beforeDoorwayScan (beforeDoorwayScan_of_exit_bakery
            (hexec k) (hbound k (by omega) q) (hall_bak k hk le_rfl) hbak_next))
      · rw [← (hw_p k (by omega)).2] at hda_k
        rw [← (hw_p (k + 1) (by omega)).2]
        exact Or.inr (doorwayAfter_step (hexec k)
          (BakeryState.inBakery_of_inWaiting (hw_p k (by omega)).1)
          (BakeryState.inBakery_of_inWaiting (hw_p (k + 1) (by omega)).1) hda_k)
  -- Step 3: Antitone stabilization of `B k = {q | inBakery q ∧ ticket q ≤ T_p}` for `k ≥ t₁`.
  let T_p := (ss t₀).ticket p
  let B : ℕ → Finset P := fun k =>
    Finset.univ.filter (fun q => (ss k).inBakery q ∧ (ss k).ticket q ≤ T_p)
  have hB_anti : ∀ k ≥ t₁, B (k + 1) ⊆ B k := by
    intro k hk q hq_mem
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hq_mem ⊢
    rcases hq_mem with ⟨hq_bak1, hq_le1⟩
    have hu_le_k : u_of q ≤ k := ((Finset.le_sup (Finset.mem_univ q)).trans le_sup_left).trans hk
    rcases hda_from q (k + 1) (by omega) with hall_bak | hda1
    · have hq_bak0 : (ss k).inBakery q := hall_bak k hu_le_k (Nat.le_succ k)
      have hnum_eq := inBakery_number_preserved (hexec k) hq_bak0 hq_bak1
      exact ⟨hq_bak0, by simpa [BakeryState.ticket, hnum_eq] using hq_le1⟩
    · exact absurd hq_le1 (not_le_of_gt ((BakeryState.ticket_lt_iff _ _ p q).mpr
        (Or.inl (hda1.2.2 (Or.inr hq_bak1)))))
  obtain ⟨t_s, ht_s_ge, hB_stab⟩ := exists_forall_eq_of_antitone_finset hB_anti
  have ht₁_ge : t₀ ≤ t₁ := le_sup_right
  have hp_mem_Bs : p ∈ B t_s := by
    obtain ⟨hw_s, hnum_s⟩ := hw_p t_s (by omega)
    simp [B, T_p, BakeryState.ticket, hnum_s, BakeryState.inBakery_of_inWaiting hw_s]
  -- Pick `q_star ∈ B t_s` with the minimum ticket.
  let tickets_Bs := (B t_s).image (fun q => (ss t_s).ticket q)
  have htickets_ne : tickets_Bs.Nonempty := ⟨_, Finset.mem_image_of_mem _ hp_mem_Bs⟩
  obtain ⟨q_star, hq_star_mem, hq_star_min_eq⟩ :=
    Finset.mem_image.mp (Finset.min'_mem tickets_Bs htickets_ne)
  have hB_bak : ∀ r ∈ B t_s, ∀ k ≥ t_s,
      (ss k).inBakery r ∧ (ss k).number r = (ss t_s).number r := fun r hr_mem k hk =>
    Nat.le_induction ⟨(Finset.mem_filter.mp hr_mem).2.1, rfl⟩ (fun m hm ihm =>
      have hm1_mem : r ∈ B (m + 1) := hB_stab (m + 1) (Nat.le_succ_of_le hm) ▸ hr_mem
      have hbak1 := (Finset.mem_filter.mp hm1_mem).2.1
      ⟨hbak1, (inBakery_number_preserved (hexec m) ihm.1 hbak1).trans ihm.2⟩) k hk
  have hq_star_bak : ∀ k ≥ t_s, (ss k).inBakery q_star :=
    fun k hk => (hB_bak q_star hq_star_mem k hk).1
  have hq_star_wait : ∀ k ≥ t_s, (ss k).inWaiting q_star := fun k hk =>
    (hq_star_bak k hk).resolve_right fun hcs => by
      have hstay_cs : ∀ j ≥ k, (ss j).phase q_star = .cs := fun j hj =>
        Nat.le_induction hcs (fun j hj ih => step_cs_stays_of_inBakery (hexec j)
          (hbound j (by omega) q_star) ih (hq_star_bak (j + 1) (by omega))) j hj
      obtain ⟨m, hm_ge, hact_m⟩ := hfair q_star k (fun j hj => by simp [hstay_cs j hj])
      exact not_step_actor_from_staying_cs (hexec m) hact_m
        (hbound m (by omega) q_star) (hstay_cs m hm_ge) (hstay_cs (m + 1) (by omega))
  have hq_star_global_min : ∀ k ≥ t_s, ∀ r, (ss k).inBakery r → r ≠ q_star →
      (ss k).ticket q_star < (ss k).ticket r := by
    intro k hk r hr_bak hr_ne
    have htk : ∀ r ∈ B t_s, (ss k).ticket r = (ss t_s).ticket r := fun r hr => by
      simp [BakeryState.ticket, (hB_bak r hr k hk).2]
    rw [htk _ hq_star_mem]
    by_cases hr_le : (ss k).ticket r ≤ T_p
    · have hr_mem_Bk : r ∈ B k := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr_bak, hr_le⟩
      have hr_mem_Bs : r ∈ B t_s := hB_stab k hk ▸ hr_mem_Bk
      rw [htk _ hr_mem_Bs]
      refine lt_of_le_of_ne ?_ fun heq => hr_ne (Prod.ext_iff.mp (ofLex_inj.mpr heq)).2.symm
      rw [hq_star_min_eq]
      exact Finset.min'_le tickets_Bs _ (Finset.mem_image_of_mem _ hr_mem_Bs)
    · exact lt_of_le_of_lt (Finset.mem_filter.mp hq_star_mem).2.2 (not_le.mp hr_le)
  have hno_cs_after : ∀ k ≥ t_s, ∀ r, ¬ (ss k).inCS r := by
    intro k hk r hr_cs
    rcases eq_or_ne r q_star with rfl | hr_eq
    · have hw := hq_star_wait k hk
      simp [BakeryState.inWaiting, BakeryPhase.isWaiting, show (ss k).phase r = .cs from hr_cs]
        at hw
    · exact lt_asymm (bakery_cs_lt (hreach_all k) hr_cs (hq_star_bak k hk) hr_eq)
        (hq_star_global_min k hk r (.inr hr_cs) hr_eq)
  -- Step 4a: Drain all processes initially in `.failed` or `.writeNumberZero` at `t_s`.
  have hex_clean_rf (r : P) :
      ∃ u ≥ t_s, (ss u).phase r ≠ .failed ∧ (ss u).phase r ≠ .writeNumberZero := by
    obtain ⟨u, hu_ge, hu_zero⟩ := exists_nonBakeryMeasure_zero hexec hfair (q := r) (i := t_s)
      (fun k hk => hbound k (by omega) r)
    refine ⟨u, hu_ge, ?_⟩
    cases hph : (ss u).phase r <;> simp_all [nonBakeryMeasure]
  choose v_of hv_ge hv_clean using hex_clean_rf
  have hv_clean_from : ∀ r j, v_of r ≤ j →
      (ss j).phase r ≠ .failed ∧ (ss j).phase r ≠ .writeNumberZero := fun r j hj =>
    have hv_ge_r := hv_ge r
    Nat.le_induction (hv_clean r) (fun m hm ihm => step_clean_reset_fail (hexec m)
      (hbound m (by omega) r) (hno_cs_after m (by omega) r) ihm) j hj
  let t_A := Finset.univ.sup v_of ⊔ t_s
  have ht_A_ge : t_s ≤ t_A := le_sup_right
  have hclean_after_tA : ∀ k ≥ t_A, ∀ r,
      (ss k).phase r ≠ .failed ∧ (ss k).phase r ≠ .writeNumberZero :=
    fun k hk r =>
      hv_clean_from r k (((Finset.le_sup (Finset.mem_univ r)).trans le_sup_left).trans hk)
  -- Step 4b: From `t_A` onward, any doorway completion enters `inWaiting` permanently.
  have hstay_waiting_after_tA : ∀ r k, t_A ≤ k → (ss k).inWaiting r →
      ∀ j ≥ k, (ss j).inWaiting r := fun r k hk hw_r j hj =>
    Nat.le_induction hw_r (fun m hm ihm => (inWaiting_step_of_not_cs (hexec m)
      (hbound m (by omega) r) ihm (hno_cs_after (m + 1) (by omega) r)).1) j hj
  have hex_quiesce_r : ∀ r, ∃ w ≥ t_A, ∀ k ≥ w,
      (ss k).phase r = .remainder ∨ (ss k).inWaiting r := by
    intro r
    by_cases h_ever_dw : ∃ m ≥ t_A, (ss m).inDoorway r
    · obtain ⟨m, hm_ge, hdw_m⟩ := h_ever_dw
      have hnot_rem_from_m : ∀ j ≥ m, (ss j).phase r ≠ .remainder := fun j hj =>
        Nat.le_induction
          (fun hrem => by simp [BakeryState.inDoorway, BakeryPhase.isDoorway, hrem] at hdw_m)
          (fun l hml ihl => step_not_rem_of_clean (hexec l) (hbound l (by omega) r)
            (hclean_after_tA l (by omega) r) ihl) j hj
      obtain ⟨w, hw_ge, hw_zero⟩ := exists_nonBakeryMeasure_zero hexec hfair (q := r) (i := m)
        (fun k hk => hbound k (by omega) r)
      have hw_wait : (ss w).inWaiting r := by
        rcases nonBakeryMeasure_eq_zero_iff.mp hw_zero with hrem_w | hbak_w
        · exact absurd hrem_w (hnot_rem_from_m w hw_ge)
        · exact hbak_w.resolve_right (hno_cs_after w (by omega) r)
      exact ⟨w, by omega, fun k hk => Or.inr (hstay_waiting_after_tA r w (by omega) hw_wait k hk)⟩
    · push Not at h_ever_dw
      exact ⟨t_A, le_rfl, fun k hk => phase_rem_or_waiting_of_clean
        (h_ever_dw k hk) (hno_cs_after k (by omega) r) (hclean_after_tA k hk r)⟩
  choose w_of hw_ge hw_quiesce using hex_quiesce_r
  let t₂ := Finset.univ.sup w_of ⊔ t_A
  have ht₂_ge : t_A ≤ t₂ := le_sup_right
  have hquiesce_all : ∀ k ≥ t₂, ∀ r, (ss k).phase r = .remainder ∨ (ss k).inWaiting r :=
    fun k hk r =>
      hw_quiesce r k (((Finset.le_sup (Finset.mem_univ r)).trans le_sup_left).trans hk)
  -- Step 5: From `t₂` onward, every step of `q_star` strictly decreases `waitMeasure`.
  obtain ⟨k, hk, hk_zero⟩ := exists_measure_zero hexec hfair (q := q_star) (i := t₂) waitMeasure
    (fun j hj hact _ => waitMeasure_step_lt_of_quiescent (hreach_all j).bakeryInv.local_inv
      (hexec j) hact (hbound j (by omega) q_star) (hq_star_wait j (by omega)) (hquiesce_all j hj)
      fun r hr_w hr_ne => hq_star_global_min j (by omega) r
        (BakeryState.inBakery_of_inWaiting hr_w) hr_ne)
    fun _ _ hpos hrem => by simp [hrem, waitMeasure] at hpos
  have := waitMeasure_pos_of_inWaiting ((hreach_all k).bakeryInv.local_inv q_star)
    (hq_star_wait k (by omega))
  omega

end Cslib.Distributed.MutualExclusion
