/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Peterson's Bounded-State Filter Lock and Single-Register Impossibility

This module pairs two foundational results on shared-memory mutual exclusion over atomic read/write
registers, complementing the unbounded-ticket safe-register Bakery algorithm in `Bakery.lean`:

1. **Peterson's `(n - 1)`-Level `n`-Process Filter Lock (`filterLock`, [Peterson1981], Fig. 3,
   p. 116):**
   Using bounded `0`-indexed `Fin n`-valued atomic read/write arrays `level : Fin n → Fin n` and
   `victim : Fin (n - 1) → Fin n` (evaluating each waiting room's test via single-register
   reads `checkVictim` and `checkLevel` without multi-word snapshots or read-modify-write
   primitives), each waiting room `r : Fin (n - 1)` acts as a filter admitting at most `n - (r + 1)`
   processes (`card_at_level_le`, proof infrastructure for Fig. 3). At the final level `ℓ = n - 1`,
   capacity `n - (n - 1) = 1` yields mutual exclusion (`filterLock_mutualExclusion`). Inspecting the
   highest occupied waiting room (`filterLock_step_progress`) yields an enabled finite trying-only
   execution reaching `CriticalSection` (`filterLock_exists_cs_execution`, a finite progress
   witness; fair-execution progress across infinite runs with a sequenced room scan remains open in
   #7296).

2. **Single-Register Covering-Write Impossibility Step
   (`not_deadlockFreeMutex_of_single_register`, 1-register base step toward [BurnsLynch1993],
   Theorem 5.1, p. 177):**
   Formalizes deterministic asynchronous multi-writer atomic read/write register protocols
   (`MutexProtocol P Reg Val State`, with `.remainder`, `.trying`, `.cs`, and `.exit` regions in
   `MutexSection`). Here `MutexProtocol.DeadlockFree` asks for some process to reach `.cs` from an
   initially trying state under `MutexProtocol.WeakFair` (scheduling `.trying` and `.exit`) and
   `MutexProtocol.CSEventuallyExits`, whereas [BurnsLynch1993] (§§2–3, pp. 173–175) asks for a
   region change in each nonnull fair history. Proves the `Fintype.card Reg ≤ 1`
   (`2 ≤ Fintype.card P`) step via one blind write overwriting another process's writes
   (specializing Lemma 5.2's indistinguishability replay and Lemma 5.4's covering-write argument,
   pp. 177, 180); the full `Fintype.card P ≤ Fintype.card Reg` bound stays open under #7296.

## Main definitions

* `Cslib.Distributed.MutualExclusion.FilterPhase`: per-process control state of Peterson's
  `n`-thread filter lock.
* `Cslib.Distributed.MutualExclusion.FilterState`: global state `(phase, level, victim)` over
  `Fin n`-valued registers, with `init`, `inCS`, `isTrying`, `atLevel`, `potential`, and
  `Reachable`.
* `Cslib.Distributed.MutualExclusion.FilterAction`: single-register atomic read/write actions of
  the filter lock.
* `Cslib.Distributed.MutualExclusion.filterStep?`,
  `Cslib.Distributed.MutualExclusion.filterStepTrace?`: computable single-step and trace
  evaluators.
* `Cslib.Distributed.MutualExclusion.filterLock`: the `Cslib.LTS` of Peterson's `n`-process filter
  lock.
* `Cslib.Distributed.MutualExclusion.MutexSection`,
  `Cslib.Distributed.MutualExclusion.RegStep`,
  `Cslib.Distributed.MutualExclusion.MutexProtocol`,
  `Cslib.Distributed.MutualExclusion.MutexConfig`,
  `Cslib.Distributed.MutualExclusion.MutexAction`: general deterministic asynchronous atomic
  read/write register mutual-exclusion protocols and their `Cslib.LTS` semantics
  (`MutuallyExclusive`, `WeakFair`, `CSEventuallyExits`, `DeadlockFree`, `DeadlockFreeMutex`).

## Main results

* `Cslib.Distributed.MutualExclusion.filterLock_mutualExclusion`: Mutual Exclusion for Peterson's
  Fig. 3 `n`-process filter lock ([Peterson1981], p. 116) — in every reachable state of
  `filterLock n`, at most one process is in `CriticalSection` (proved via the level-capacity
  infrastructure `atLevel_level_ge` and `card_at_level_le`).
* `Cslib.Distributed.MutualExclusion.filterLock_exists_cs_execution`: Finite Progress Witness for
  `filterLock` — from any reachable state with a nonempty set of trying processes, there exists an
  enabled finite trying-only execution reaching `CriticalSection` (built on single-step potential
  infrastructure `filterLock_step_progress`, without claiming fair-execution liveness; see #7296).
* `Cslib.Distributed.MutualExclusion.not_deadlockFreeMutex_of_single_register`: Single-Register
  Impossibility Step toward [BurnsLynch1993], Theorem 5.1 (#7296) — for `2 ≤ Fintype.card P` and
  `Fintype.card Reg ≤ 1`, no `MutexProtocol P Reg Val State` achieves `DeadlockFreeMutex`.

## References

* [J. E. Burns, N. A. Lynch, *Bounds on Shared Memory for Mutual Exclusion*][BurnsLynch1993]
* [G. L. Peterson, *Myths About the Mutual Exclusion Problem*][Peterson1981]
-/

public section

namespace Cslib.Distributed.MutualExclusion

open Cslib Cslib.ωSequence

/-! ## Part 1: Peterson's bounded-state `n`-process Filter Lock -/

/-- Per-process control phase of Peterson's `n`-process filter lock [Peterson1981]. -/
inductive FilterPhase (n : ℕ) where
  /-- Noncritical remainder section (`level[p] = 0`). -/
  | remainder
  /-- Ready at level `ℓ` (after `requestCS` at `ℓ = 0`, or after passing room `ℓ - 1`): poised to
  write `level[p] := ℓ + 1` (if `ℓ + 1 < n`) or enter `.cs` (when `n = 1`). -/
  | ready (ℓ : Fin n)
  /-- Poised to write `victim[r] := p` after setting `level[p] := r + 1`. -/
  | writeVictim (r : Fin (n - 1))
  /-- Waiting in room `r` (`level[p] = r + 1`), having confirmed `level[q] < r + 1` for each
  `q ∈ cleared`. -/
  | waitRoom (r : Fin (n - 1)) (cleared : Finset (Fin n))
  /-- Critical section (`CS`). -/
  | cs
  deriving @[expose] DecidableEq

namespace FilterPhase

variable {n : ℕ}

/-- Boolean test for trying phases (outside `.remainder` and `.cs`). -/
@[expose]
def isTrying : FilterPhase n → Bool
  | .remainder | .cs => false
  | .ready _ | .writeVictim _ | .waitRoom _ _ => true

/-- Process has set `victim[r]` (or passed room `r`) and has not exited `.cs`. -/
private def atOrAboveRoom (r : Fin (n - 1)) : FilterPhase n → Bool
  | .remainder => false
  | .ready ℓ => decide (r.val + 1 ≤ ℓ.val)
  | .writeVictim r' => decide (r.val < r'.val)
  | .waitRoom r' _ => decide (r.val ≤ r'.val)
  | .cs => true

/-- Process has strictly passed waiting room `r` and has not exited `.cs`. -/
@[expose]
def aboveRoom (r : Fin (n - 1)) : FilterPhase n → Bool
  | .remainder => false
  | .ready ℓ => decide (r.val + 1 ≤ ℓ.val)
  | .writeVictim r' => decide (r.val < r'.val)
  | .waitRoom r' _ => decide (r.val < r'.val)
  | .cs => true

/-- Bounded local progress rank of a `FilterPhase n`. -/
@[expose]
def potential : FilterPhase n → ℕ
  | .remainder => 0
  | .ready ℓ => ℓ.val * (n + 2) + 1
  | .writeVictim r => r.val * (n + 2) + 2
  | .waitRoom r cleared => r.val * (n + 2) + 3 + cleared.card
  | .cs => n * (n + 2)

/-- Waiting room currently occupied by a `.waitRoom` phase, if any. -/
private def waitRoomOf : FilterPhase n → Option (Fin (n - 1))
  | .waitRoom r _ => some r
  | _ => none

end FilterPhase

/-- Global configuration of Peterson's `n`-process filter lock over bounded `Fin n` registers. -/
@[ext]
structure FilterState (n : ℕ) where
  /-- Per-process control phase. -/
  phase : Fin n → FilterPhase n
  /-- Bounded atomic register array `level : Fin n → Fin n`. -/
  level : Fin n → Fin n
  /-- Bounded atomic register array `victim : Fin (n - 1) → Fin n`. -/
  victim : Fin (n - 1) → Fin n

instance {n : ℕ} : DecidableEq (FilterState n) :=
  fun a b =>
    decidable_of_iff
      ((∀ p, a.phase p = b.phase p) ∧
        (∀ p, a.level p = b.level p) ∧
        (∀ r, a.victim r = b.victim r))
      ⟨fun ⟨hp, hl, hv⟩ => FilterState.ext (funext hp) (funext hl) (funext hv),
        fun h => h ▸ ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩

namespace FilterState

variable {n : ℕ}

/-- Initial quiescent configuration with all processes in `.remainder` and all registers `0`. -/
@[expose]
def init (n : ℕ) : FilterState n where
  phase _ := .remainder
  level p := ⟨0, p.pos⟩
  victim r := ⟨0, by have := r.isLt; omega⟩

/-- Process `p` is in its critical section (`CS`). -/
@[expose]
def inCS (s : FilterState n) (p : Fin n) : Prop :=
  s.phase p = .cs

/-- Process `p` is in its trying section. -/
@[expose]
def isTrying (s : FilterState n) (p : Fin n) : Prop :=
  (s.phase p).isTrying = true

instance (s : FilterState n) (p : Fin n) : Decidable (s.inCS p) :=
  inferInstanceAs (Decidable (s.phase p = .cs))

instance (s : FilterState n) (p : Fin n) : Decidable (s.isTrying p) :=
  inferInstanceAs (Decidable (_ = true))

/-- Processes that have reached filtered level `ℓ` (`0 ≤ ℓ < n`) and passed all wait rooms `< ℓ`. -/
@[expose]
def atLevel (s : FilterState n) : ℕ → Finset (Fin n)
  | 0 => Finset.univ
  | k + 1 =>
    if hk : k < n - 1 then
      Finset.univ.filter (fun p => (s.phase p).aboveRoom ⟨k, hk⟩ = true)
    else
      ∅

/-- Global progress potential summing `FilterPhase.potential` across all `n` processes. -/
@[expose]
def potential (s : FilterState n) : ℕ :=
  Finset.univ.sum fun p => (s.phase p).potential

end FilterState

/-- Single-register atomic actions of Peterson's `n`-process filter lock. -/
inductive FilterAction (n : ℕ) where
  /-- Process `p` leaves `.remainder` to acquire the lock. -/
  | requestCS (p : Fin n)
  /-- Single-process fast path (`n = 1`): enter `.cs` from `.ready 0` when there are `0` rooms. -/
  | enterCSOne (p : Fin n)
  /-- Process `p` atomically writes `level[p] := ℓ + 1` to enter waiting room `ℓ`. -/
  | setLevel (p : Fin n)
  /-- Process `p` atomically writes `victim[r] := p` in waiting room `r`. -/
  | setVictim (p : Fin n)
  /-- Process `p` atomically reads `victim[r]` in room `r` (advancing if `victim[r] ≠ p`). -/
  | checkVictim (p : Fin n)
  /-- Process `p` atomically reads `level[q]` (`q ≠ p`) in room `r`. -/
  | checkLevel (p q : Fin n)
  /-- Process `p` exits `.cs`, atomically resetting `level[p] := 0`. -/
  | exitCS (p : Fin n)
  deriving @[expose] DecidableEq

namespace FilterAction

variable {n : ℕ}

/-- Acting process of a `FilterAction`. -/
@[expose]
def actor : FilterAction n → Fin n
  | .requestCS p | .enterCSOne p | .setLevel p | .setVictim p
  | .checkVictim p | .checkLevel p _ | .exitCS p => p

end FilterAction

/-- Phase entered upon passing waiting room `r`: `.ready (r + 1)` if higher rooms remain, or `.cs`
directly when `r` is the final room `n - 2`. -/
@[expose]
def nextAfterRoom {n : ℕ} (r : Fin (n - 1)) : FilterPhase n :=
  if h : r.val + 2 < n then
    .ready ⟨r.val + 1, by omega⟩
  else
    .cs

/-- Computable single-step transition evaluator for Peterson's filter lock. -/
@[expose]
def filterStep? {n : ℕ} (s : FilterState n) (μ : FilterAction n) : Option (FilterState n) :=
  match μ with
  | .requestCS p =>
    if s.phase p = .remainder then
      some { s with phase := Function.update s.phase p (.ready ⟨0, p.pos⟩) }
    else none
  | .enterCSOne p =>
    match s.phase p with
    | .ready ℓ =>
      if ¬ (ℓ.val + 1 < n) then
        some { s with phase := Function.update s.phase p .cs }
      else none
    | _ => none
  | .setLevel p =>
    match s.phase p with
    | .ready ℓ =>
      if h : ℓ.val + 1 < n then
        some { s with
          phase := Function.update s.phase p (.writeVictim ⟨ℓ.val, by omega⟩)
          level := Function.update s.level p ⟨ℓ.val + 1, h⟩ }
      else none
    | _ => none
  | .setVictim p =>
    match s.phase p with
    | .writeVictim r =>
      some { s with
        phase := Function.update s.phase p (.waitRoom r ∅)
        victim := Function.update s.victim r p }
    | _ => none
  | .checkVictim p =>
    match s.phase p with
    | .waitRoom r _ =>
      if s.victim r ≠ p then
        some { s with phase := Function.update s.phase p (nextAfterRoom r) }
      else
        some s
    | _ => none
  | .checkLevel p q =>
    match s.phase p with
    | .waitRoom r cleared =>
      if q ≠ p then
        if (s.level q).val < r.val + 1 then
          let cleared' := insert q cleared
          if cleared' = Finset.univ.erase p then
            some { s with phase := Function.update s.phase p (nextAfterRoom r) }
          else
            some { s with phase := Function.update s.phase p (.waitRoom r cleared') }
        else
          some s
      else none
    | _ => none
  | .exitCS p =>
    if s.phase p = .cs then
      some { s with
        phase := Function.update s.phase p .remainder
        level := Function.update s.level p ⟨0, p.pos⟩ }
    else none

/-- Computable multi-step trace evaluator for `filterStep?`. -/
@[expose]
def filterStepTrace? {n : ℕ} (s : FilterState n) : List (FilterAction n) → Option (FilterState n)
  | [] => some s
  | μ :: μs => (filterStep? s μ).bind (fun s' => filterStepTrace? s' μs)

/-- Labelled transition system of Peterson's `n`-process filter lock [Peterson1981]. -/
@[expose]
def filterLock (n : ℕ) : LTS (FilterState n) (FilterAction n) where
  Tr s μ s' := filterStep? s μ = some s'

theorem filterStepTrace?_eq_some_iff {n : ℕ} {s s' : FilterState n} {μs : List (FilterAction n)} :
    filterStepTrace? s μs = some s' ↔ (filterLock n).MTr s μs s' := by
  induction μs generalizing s with
  | nil => simp [filterStepTrace?]
  | cons μ μs ih =>
    simp only [filterStepTrace?, Option.bind_eq_some_iff, LTS.MTr.cons_iff]
    exact exists_congr fun s₁ => and_congr_right fun _ => ih

namespace FilterState

variable {n : ℕ}

/-- A `FilterState` is reachable if it is reachable from `FilterState.init n` in `filterLock n`. -/
@[expose]
def Reachable (s : FilterState n) : Prop :=
  (filterLock n).CanReach (FilterState.init n) s

theorem Reachable.init : (FilterState.init n).Reachable :=
  LTS.CanReach.refl (filterLock n) (FilterState.init n)

theorem Reachable.step {s s' : FilterState n} {μ : FilterAction n}
    (hr : s.Reachable) (htr : (filterLock n).Tr s μ s') : s'.Reachable := by
  obtain ⟨μs, hmtr⟩ := hr
  exact ⟨μs ++ [μ], hmtr.stepR (filterLock n) htr⟩

theorem Reachable.mTr {s s' : FilterState n} {μs : List (FilterAction n)}
    (hr : s.Reachable) (hmtr : (filterLock n).MTr s μs s') : s'.Reachable := by
  obtain ⟨μs₀, hmtr₀⟩ := hr
  exact ⟨μs₀ ++ μs, hmtr₀.comp (filterLock n) hmtr⟩

end FilterState

/-! ### Filter lock inductive invariants, capacity bound, mutual exclusion, and deadlock freedom -/

private def atRoomSet {n : ℕ} (s : FilterState n) (r : Fin (n - 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun p => (s.phase p).atOrAboveRoom r = true)

private def aboveRoomSet {n : ℕ} (s : FilterState n) (r : Fin (n - 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun p => (s.phase p).aboveRoom r = true)

private theorem aboveRoom_imp_atOrAboveRoom {n : ℕ} {ph : FilterPhase n} {r : Fin (n - 1)}
    (h : ph.aboveRoom r = true) : ph.atOrAboveRoom r = true := by
  unfold FilterPhase.aboveRoom FilterPhase.atOrAboveRoom at *
  (cases ph <;> simp_all); omega

private theorem aboveRoomSet_subset_atRoomSet {n : ℕ} (s : FilterState n) (r : Fin (n - 1)) :
    aboveRoomSet s r ⊆ atRoomSet s r := by
  intro p hp
  simp only [aboveRoomSet, atRoomSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact aboveRoom_imp_atOrAboveRoom hp

private theorem nextAfterRoom_atOrAbove {n : ℕ} (r r' : Fin (n - 1)) :
    (nextAfterRoom r).atOrAboveRoom r' = decide (r'.val ≤ r.val) := by
  unfold nextAfterRoom
  split
  · simp [FilterPhase.atOrAboveRoom]
  · simp only [FilterPhase.atOrAboveRoom, Bool.true_eq, decide_eq_true_eq]
    have := r.isLt; have := r'.isLt; omega

private theorem nextAfterRoom_above {n : ℕ} (r r' : Fin (n - 1)) :
    (nextAfterRoom r).aboveRoom r' = decide (r'.val ≤ r.val) := by
  unfold nextAfterRoom
  split
  · simp [FilterPhase.aboveRoom]
  · simp only [FilterPhase.aboveRoom, Bool.true_eq, decide_eq_true_eq]
    have := r.isLt; have := r'.isLt; omega

private def filterLocalInv {n : ℕ} (s : FilterState n) (p : Fin n) : Prop :=
  match s.phase p with
  | .remainder => (s.level p).val = 0
  | .ready ℓ => (s.level p).val = ℓ.val ∧ (1 < n → ℓ.val + 1 < n)
  | .writeVictim r => (s.level p).val = r.val + 1
  | .waitRoom r cleared => (s.level p).val = r.val + 1 ∧ p ∉ cleared
  | .cs => n ≤ 1 ∨ (s.level p).val = n - 1

private theorem filterLocalInv_level_ge_of_atOrAbove {n : ℕ} {s : FilterState n} {p : Fin n}
    {r : Fin (n - 1)} (hl : filterLocalInv s p) (hat : (s.phase p).atOrAboveRoom r = true) :
    r.val + 1 ≤ (s.level p).val := by
  have hn : 1 < n := by have := r.isLt; omega
  unfold filterLocalInv at hl
  unfold FilterPhase.atOrAboveRoom at hat
  cases hph : s.phase p <;> simp only [hph] at hl hat
  · simp at hat
  · simp only [decide_eq_true_eq] at hat; omega
  · simp only [decide_eq_true_eq] at hat; omega
  · simp only [decide_eq_true_eq] at hat; omega
  · rcases hl with hle1 | heq <;> omega

private theorem filterLocalInv_level_ge_of_above {n : ℕ} {s : FilterState n} {p : Fin n}
    {r : Fin (n - 1)} (hl : filterLocalInv s p) (hab : (s.phase p).aboveRoom r = true) :
    r.val + 1 ≤ (s.level p).val :=
  filterLocalInv_level_ge_of_atOrAbove hl (aboveRoom_imp_atOrAboveRoom hab)

private structure FilterInv {n : ℕ} (s : FilterState n) : Prop where
  local_inv : ∀ p, filterLocalInv s p
  cleared_disjoint : ∀ r cleared, s.phase (s.victim r) = .waitRoom r cleared →
    ∀ q ∈ cleared, q ∉ atRoomSet s r
  victim_unique_above : ∀ r, s.victim r ∈ aboveRoomSet s r →
    ∀ q, q ≠ s.victim r → q ∉ atRoomSet s r
  victim_mem : ∀ r, (atRoomSet s r).Nonempty → s.victim r ∈ atRoomSet s r

private theorem filterInv_init (n : ℕ) : FilterInv (FilterState.init n) where
  local_inv _ := by simp [filterLocalInv, FilterState.init]
  cleared_disjoint r _ h := by simp [FilterState.init] at h
  victim_unique_above r h := by simp [aboveRoomSet, FilterState.init, FilterPhase.aboveRoom] at h
  victim_mem := by
    rintro r ⟨p, hp⟩
    simp [atRoomSet, FilterState.init, FilterPhase.atOrAboveRoom] at hp

private inductive FilterStepShape {n : ℕ} (s : FilterState n) :
    FilterAction n → FilterState n → Prop where
  | reqCS (p : Fin n) :
      s.phase p = .remainder →
      FilterStepShape s (.requestCS p)
        { s with phase := Function.update s.phase p (.ready ⟨0, p.pos⟩) }
  | csOne (p : Fin n) (ℓ : Fin n) :
      s.phase p = .ready ℓ → ¬ (ℓ.val + 1 < n) →
      FilterStepShape s (.enterCSOne p) { s with phase := Function.update s.phase p .cs }
  | setLv (p : Fin n) (ℓ : Fin n) (h : ℓ.val + 1 < n) :
      s.phase p = .ready ℓ →
      FilterStepShape s (.setLevel p)
        { s with
          phase := Function.update s.phase p (.writeVictim ⟨ℓ.val, by omega⟩)
          level := Function.update s.level p ⟨ℓ.val + 1, h⟩ }
  | setVic (p : Fin n) (r : Fin (n - 1)) :
      s.phase p = .writeVictim r →
      FilterStepShape s (.setVictim p)
        { s with
          phase := Function.update s.phase p (.waitRoom r ∅)
          victim := Function.update s.victim r p }
  | passVic (p : Fin n) (r : Fin (n - 1)) (cl : Finset (Fin n)) :
      s.phase p = .waitRoom r cl → s.victim r ≠ p →
      FilterStepShape s (.checkVictim p)
        { s with phase := Function.update s.phase p (nextAfterRoom r) }
  | spinVic (p : Fin n) (r : Fin (n - 1)) (cl : Finset (Fin n)) :
      s.phase p = .waitRoom r cl → FilterStepShape s (.checkVictim p) s
  | passLv (p target : Fin n) (r : Fin (n - 1)) (cl : Finset (Fin n)) :
      s.phase p = .waitRoom r cl → target ≠ p → (s.level target).val < r.val + 1 →
      insert target cl = Finset.univ.erase p →
      FilterStepShape s (.checkLevel p target)
        { s with phase := Function.update s.phase p (nextAfterRoom r) }
  | recLv (p target : Fin n) (r : Fin (n - 1)) (cl : Finset (Fin n)) :
      s.phase p = .waitRoom r cl → target ≠ p → (s.level target).val < r.val + 1 →
      insert target cl ≠ Finset.univ.erase p →
      FilterStepShape s (.checkLevel p target)
        { s with phase := Function.update s.phase p (.waitRoom r (insert target cl)) }
  | spinLv (p target : Fin n) (r : Fin (n - 1)) (cl : Finset (Fin n)) :
      s.phase p = .waitRoom r cl → FilterStepShape s (.checkLevel p target) s
  | exit (p : Fin n) :
      s.phase p = .cs →
      FilterStepShape s (.exitCS p)
        { s with
          phase := Function.update s.phase p .remainder
          level := Function.update s.level p ⟨0, p.pos⟩ }

private theorem filterStepShape_of_step {n : ℕ} {s s' : FilterState n} {μ : FilterAction n}
    (htr : filterStep? s μ = some s') : FilterStepShape s μ s' := by
  cases μ <;> dsimp only [filterStep?] at htr
  · rename_i p
    split at htr; swap; · cases htr
    rename_i hph; injection htr with htr; exact htr ▸ .reqCS p hph
  · rename_i p
    cases hph : s.phase p <;> simp only [hph, reduceCtorEq] at htr
    rename_i ℓ
    by_cases hlt : ℓ.val + 1 < n
    · simp [hlt] at htr
    · simp only [hlt, not_false_eq_true, ↓reduceIte, Option.some.injEq] at htr
      exact htr ▸ .csOne p ℓ hph hlt
  · rename_i p
    cases hph : s.phase p <;> simp only [hph, reduceCtorEq] at htr
    split at htr; swap; · cases htr
    rename_i hlt; injection htr with htr; exact htr ▸ .setLv p _ hlt hph
  · rename_i p
    cases hph : s.phase p <;> simp only [hph, Option.some.injEq, reduceCtorEq] at htr
    exact htr ▸ .setVic p _ hph
  · rename_i p
    cases hph : s.phase p <;> simp only [hph, reduceCtorEq] at htr
    split at htr <;> injection htr with htr <;> subst htr
    · rename_i hvne; exact .passVic p _ _ hph hvne
    · exact .spinVic p _ _ hph
  · rename_i p target
    cases hph : s.phase p <;> simp only [hph, reduceCtorEq] at htr
    split at htr; swap; · cases htr
    rename_i htp
    split at htr
    · rename_i hlv
      split at htr <;> injection htr with htr <;> subst htr
      · rename_i hall; exact .passLv p target _ _ hph htp hlv hall
      · rename_i hne; exact .recLv p target _ _ hph htp hlv hne
    · injection htr with htr; exact htr ▸ .spinLv p target _ _ hph
  · rename_i p
    split at htr; swap; · cases htr
    rename_i hph; injection htr with htr; exact htr ▸ .exit p hph

private theorem filterStep_frame {n : ℕ} {s s' : FilterState n} {μ : FilterAction n}
    (htr : filterStep? s μ = some s') {q : Fin n} (hq : μ.actor ≠ q) :
    s'.phase q = s.phase q ∧ s'.level q = s.level q := by
  cases filterStepShape_of_step htr <;>
    first
    | exact ⟨rfl, rfl⟩
    | (simp only [FilterAction.actor, ne_eq] at hq
       simp [Function.update_of_ne (Ne.symm hq)])

private theorem filterLocalInv_nextAfterRoom {n : ℕ} {s : FilterState n} {p : Fin n}
    {r : Fin (n - 1)} (hlv : (s.level p).val = r.val + 1) :
    filterLocalInv { s with phase := Function.update s.phase p (nextAfterRoom r) } p := by
  unfold filterLocalInv; dsimp only; rw [Function.update_self]
  by_cases h2 : r.val + 2 < n
  · simp only [nextAfterRoom, h2, ↓reduceDIte]
    exact ⟨hlv, fun _ => trivial⟩
  · simp only [nextAfterRoom, h2, ↓reduceDIte]
    exact Or.inr (by have := r.isLt; omega)

private theorem filter_update_eq {n : ℕ} (P : FilterPhase n → Bool) (f : Fin n → FilterPhase n)
    (p : Fin n) (ph' : FilterPhase n) (h : P ph' = P (f p)) :
    (Finset.univ.filter fun q => P (Function.update f p ph' q)) =
      Finset.univ.filter fun q => P (f q) := by
  ext q; by_cases hqp : q = p <;> simp [hqp, h]

private theorem filter_update_false {n : ℕ} (P : FilterPhase n → Bool) (f : Fin n → FilterPhase n)
    (p : Fin n) (ph' : FilterPhase n) (h : P ph' = false) :
    (Finset.univ.filter fun q => P (Function.update f p ph' q)) =
      (Finset.univ.filter fun q => P (f q)).erase p := by
  ext q; by_cases hqp : q = p <;> simp [hqp, h]

private theorem filterInv_of_unchanged_rooms {n : ℕ} {s : FilterState n} {p : Fin n}
    {ph' : FilterPhase n} {lv' : Fin n → Fin n}
    (hinv : FilterInv s)
    (hloc' : ∀ q, filterLocalInv { s with phase := Function.update s.phase p ph', level := lv' } q)
    (hnw : ∀ r cl, ph' ≠ .waitRoom r cl)
    (hat : ∀ r, ph'.atOrAboveRoom r = (s.phase p).atOrAboveRoom r)
    (hab : ∀ r, ph'.aboveRoom r = (s.phase p).aboveRoom r) :
    FilterInv { s with phase := Function.update s.phase p ph', level := lv' } := by
  let s₁ : FilterState n := { s with phase := Function.update s.phase p ph', level := lv' }
  have hat_eq : ∀ r, atRoomSet s₁ r = atRoomSet s r := fun r =>
    filter_update_eq (·.atOrAboveRoom r) s.phase p ph' (hat r)
  have hab_eq : ∀ r, aboveRoomSet s₁ r = aboveRoomSet s r := fun r =>
    filter_update_eq (·.aboveRoom r) s.phase p ph' (hab r)
  refine ⟨hloc', ?_, ?_, ?_⟩
  · intro r cleared hw
    rw [hat_eq r]
    dsimp only [s₁] at hw
    have hvp : s.victim r ≠ p := by
      rintro rfl; rw [Function.update_self] at hw; exact hnw r cleared hw
    rw [Function.update_of_ne hvp] at hw
    exact hinv.cleared_disjoint r cleared hw
  · intro r hv; rw [hab_eq r] at hv
    intro q hne; rw [hat_eq r]
    exact hinv.victim_unique_above r hv q hne
  · intro r hne; rw [hat_eq r] at hne ⊢
    exact hinv.victim_mem r hne

private theorem filterInv_of_passRoom {n : ℕ} {s : FilterState n} {p : Fin n}
    {r₀ : Fin (n - 1)} {cleared₀ : Finset (Fin n)}
    (hinv : FilterInv s) (hph : s.phase p = .waitRoom r₀ cleared₀)
    (hloc' : ∀ q, filterLocalInv { s with phase := Function.update s.phase p (nextAfterRoom r₀) } q)
    (hvic_case : s.victim r₀ = p → ∀ q, q ≠ p → q ∉ atRoomSet s r₀) :
    FilterInv { s with phase := Function.update s.phase p (nextAfterRoom r₀) } := by
  let s₁ : FilterState n := { s with phase := Function.update s.phase p (nextAfterRoom r₀) }
  have hat_all : ∀ r, atRoomSet s₁ r = atRoomSet s r := fun r =>
    filter_update_eq (·.atOrAboveRoom r) s.phase p _ (by rw [hph, nextAfterRoom_atOrAbove]; rfl)
  have hab_ne : ∀ r ≠ r₀, aboveRoomSet s₁ r = aboveRoomSet s r := fun r hr =>
    filter_update_eq (·.aboveRoom r) s.phase p _ (by
      have := Fin.val_ne_of_ne hr
      rw [hph, nextAfterRoom_above]; simp only [FilterPhase.aboveRoom, decide_eq_decide]; omega)
  refine ⟨hloc', ?_, ?_, ?_⟩
  · intro r cleared hw
    rw [hat_all r]
    dsimp only [s₁] at hw
    have hvp : s.victim r ≠ p := by
      rintro rfl; rw [Function.update_self] at hw
      unfold nextAfterRoom at hw; split at hw <;> cases hw
    rw [Function.update_of_ne hvp] at hw
    exact hinv.cleared_disjoint r cleared hw
  · intro r hv
    by_cases hrr : r = r₀
    · subst hrr
      by_cases hvp : s.victim r = p
      · intro q hne
        rw [hat_all r]
        rw [hvp] at hne
        exact hvic_case hvp q hne
      · have hv_old : s.victim r ∈ aboveRoomSet s r := by
          simp only [aboveRoomSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          rwa [Function.update_of_ne hvp] at hv
        intro q hne; rw [hat_all r]
        exact hinv.victim_unique_above r hv_old q hne
    · rw [hab_ne r hrr] at hv
      intro q hne; rw [hat_all r]
      exact hinv.victim_unique_above r hv q hne
  · intro r hne; rw [hat_all r] at hne ⊢
    exact hinv.victim_mem r hne

private theorem filterInv_step {n : ℕ} {s s' : FilterState n} {μ : FilterAction n}
    (hinv : FilterInv s) (htr : filterStep? s μ = some s') : FilterInv s' := by
  have hloc' : ∀ q, filterLocalInv s' q := by
    intro q
    by_cases hact : μ.actor = q
    · cases filterStepShape_of_step htr with
      | reqCS p hph =>
        simp only [FilterAction.actor] at hact; subst hact
        have hl := hinv.local_inv p; unfold filterLocalInv at hl; rw [hph] at hl
        unfold filterLocalInv; dsimp only; rw [Function.update_self]
        exact ⟨hl, fun _ => by omega⟩
      | csOne p ℓ hph hnot =>
        simp only [FilterAction.actor] at hact; subst hact
        have hl := hinv.local_inv p; unfold filterLocalInv at hl; rw [hph] at hl
        unfold filterLocalInv; dsimp only; rw [Function.update_self]
        by_cases hn1 : n ≤ 1
        · exact Or.inl hn1
        · exact absurd (hl.2 (by omega)) hnot
      | setLv p ℓ _ _ =>
        simp only [FilterAction.actor] at hact; subst hact
        unfold filterLocalInv; dsimp only; rw [Function.update_self, Function.update_self]
      | setVic p r hph =>
        simp only [FilterAction.actor] at hact; subst hact
        have hl := hinv.local_inv p; unfold filterLocalInv at hl; rw [hph] at hl
        unfold filterLocalInv; dsimp only; rw [Function.update_self]
        exact ⟨hl, Finset.notMem_empty p⟩
      | passVic p r _ hph _ =>
        simp only [FilterAction.actor] at hact; subst hact
        have hl := hinv.local_inv p; unfold filterLocalInv at hl; rw [hph] at hl
        exact filterLocalInv_nextAfterRoom hl.1
      | spinVic _ _ _ _ => exact hinv.local_inv q
      | passLv p _ r _ hph _ _ _ =>
        simp only [FilterAction.actor] at hact; subst hact
        have hl := hinv.local_inv p; unfold filterLocalInv at hl; rw [hph] at hl
        exact filterLocalInv_nextAfterRoom hl.1
      | recLv p target r cleared hph hqp _ _ =>
        simp only [FilterAction.actor] at hact; subst hact
        have hl := hinv.local_inv p; unfold filterLocalInv at hl; rw [hph] at hl
        unfold filterLocalInv; dsimp only; rw [Function.update_self]
        exact ⟨hl.1, by rw [Finset.mem_insert, not_or]; exact ⟨Ne.symm hqp, hl.2⟩⟩
      | spinLv _ _ _ _ _ => exact hinv.local_inv q
      | exit p _ =>
        simp only [FilterAction.actor] at hact; subst hact
        unfold filterLocalInv; dsimp only; rw [Function.update_self, Function.update_self]
    · obtain ⟨hph, hlv⟩ := filterStep_frame htr hact
      have hl := hinv.local_inv q
      unfold filterLocalInv at hl ⊢
      rwa [hph, hlv]
  cases filterStepShape_of_step htr with
  | reqCS p hph =>
    exact filterInv_of_unchanged_rooms hinv hloc' (fun _ _ h => by cases h)
      (fun r => by simp [hph, FilterPhase.atOrAboveRoom])
      (fun r => by simp [hph, FilterPhase.aboveRoom])
  | csOne p ℓ hph hnot =>
    have hl := hinv.local_inv p; unfold filterLocalInv at hl; rw [hph] at hl
    have hn1 : n ≤ 1 := by by_contra hgt; exact hnot (hl.2 (by omega))
    exact ⟨hloc', fun r => (by have := r.isLt; omega),
      fun r => (by have := r.isLt; omega), fun r => (by have := r.isLt; omega)⟩
  | setLv p ℓ hlt hph =>
    exact filterInv_of_unchanged_rooms hinv hloc' (fun _ _ h => by cases h)
      (fun r => by rw [hph]; simp only [FilterPhase.atOrAboveRoom, decide_eq_decide]; omega)
      (fun r => by rw [hph]; simp only [FilterPhase.aboveRoom, decide_eq_decide]; omega)
  | setVic p r₀ hph =>
    let s₁ : FilterState n := { s with
      phase := Function.update s.phase p (.waitRoom r₀ ∅)
      victim := Function.update s.victim r₀ p }
    change FilterInv s₁
    have hat_ne : ∀ r ≠ r₀, atRoomSet s₁ r = atRoomSet s r := fun r hr =>
      filter_update_eq (·.atOrAboveRoom r) s.phase p _ (by
        have := Fin.val_ne_of_ne hr
        simp only [hph, FilterPhase.atOrAboveRoom, decide_eq_decide]; omega)
    have hat_eq_r₀ : atRoomSet s₁ r₀ = insert p (atRoomSet s r₀) := by
      ext q; by_cases hqp : q = p <;> simp [atRoomSet, s₁, hqp, FilterPhase.atOrAboveRoom]
    have hab_all : ∀ r, aboveRoomSet s₁ r = aboveRoomSet s r := fun r =>
      filter_update_eq (·.aboveRoom r) s.phase p _ (by simp [hph, FilterPhase.aboveRoom])
    refine ⟨hloc', ?_, ?_, ?_⟩
    · intro r cleared hw
      by_cases hrr : r = r₀
      · subst hrr
        dsimp only [s₁] at hw
        rw [Function.update_self, Function.update_self] at hw
        injection hw with _ hcl_eq; subst hcl_eq
        intro q hq; exact absurd hq (Finset.notMem_empty q)
      · rw [hat_ne r hrr]
        dsimp only [s₁] at hw; rw [Function.update_of_ne hrr] at hw
        have hvp : s.victim r ≠ p := by
          rintro rfl; rw [Function.update_self] at hw
          injection hw with hr_eq _; exact hrr hr_eq.symm
        rw [Function.update_of_ne hvp] at hw
        exact hinv.cleared_disjoint r cleared hw
    · intro r hv
      rw [hab_all r] at hv
      by_cases hrr : r = r₀
      · subst hrr
        have hv_mem : s₁.victim r ∈ aboveRoomSet s r := hv
        dsimp only [s₁] at hv_mem; rw [Function.update_self] at hv_mem
        simp [aboveRoomSet, hph, FilterPhase.aboveRoom] at hv_mem
      · dsimp only [s₁] at hv ⊢
        rw [Function.update_of_ne hrr] at hv ⊢
        rw [hat_ne r hrr]
        exact hinv.victim_unique_above r hv
    · intro r hne
      by_cases hrr : r = r₀
      · subst hrr; rw [hat_eq_r₀]; dsimp only [s₁]; rw [Function.update_self]
        exact Finset.mem_insert_self p _
      · dsimp only [s₁]; rw [Function.update_of_ne hrr]
        rw [hat_ne r hrr] at hne ⊢
        exact hinv.victim_mem r hne
  | passVic p r₀ cleared₀ hph hvne =>
    exact filterInv_of_passRoom hinv hph hloc' fun hvp => absurd hvp hvne
  | spinVic | spinLv => exact hinv
  | passLv p target r₀ cleared₀ hph _ hlv_lt hall_cl =>
    refine filterInv_of_passRoom hinv hph hloc' fun hvp q hqp => ?_
    have hq_mem : q ∈ insert target cleared₀ := by
      rw [hall_cl]; exact Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ q⟩
    rcases Finset.mem_insert.mp hq_mem with rfl | hq_cl
    · intro hmem
      simp only [atRoomSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hge := filterLocalInv_level_ge_of_atOrAbove (hinv.local_inv q) hmem
      omega
    · exact hinv.cleared_disjoint r₀ cleared₀ (hvp.symm ▸ hph) q hq_cl
  | recLv p target r₀ cleared₀ hph _ hlv_lt _ =>
    have htarget_not_at : target ∉ atRoomSet s r₀ := by
      intro hmem
      simp only [atRoomSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hge := filterLocalInv_level_ge_of_atOrAbove (hinv.local_inv target) hmem
      omega
    let s₁ : FilterState n :=
      { s with phase := Function.update s.phase p (.waitRoom r₀ (insert target cleared₀)) }
    change FilterInv s₁
    have hat_all : ∀ r, atRoomSet s₁ r = atRoomSet s r := fun r =>
      filter_update_eq (·.atOrAboveRoom r) s.phase p _ (by rw [hph]; rfl)
    have hab_all : ∀ r, aboveRoomSet s₁ r = aboveRoomSet s r := fun r =>
      filter_update_eq (·.aboveRoom r) s.phase p _ (by rw [hph]; rfl)
    refine ⟨hloc', ?_, ?_, ?_⟩
    · intro r cleared hw
      rw [hat_all r]
      dsimp only [s₁] at hw
      by_cases hvp : s.victim r = p
      · rw [hvp, Function.update_self] at hw
        injection hw with hr_eq hcl_eq
        rw [← hr_eq, ← hcl_eq]
        intro q hq_mem
        rcases Finset.mem_insert.mp hq_mem with hqt | hq_cl
        · rw [hqt]; exact htarget_not_at
        · have hw0 : s.phase (s.victim r₀) = .waitRoom r₀ cleared₀ := by
            rw [congrArg s.victim hr_eq, hvp, hph]
          exact hinv.cleared_disjoint r₀ cleared₀ hw0 q hq_cl
      · rw [Function.update_of_ne hvp] at hw
        exact hinv.cleared_disjoint r cleared hw
    · intro r hv; rw [hab_all r] at hv
      intro q hne; rw [hat_all r]
      exact hinv.victim_unique_above r hv q hne
    · intro r hne; rw [hat_all r] at hne ⊢
      exact hinv.victim_mem r hne
  | exit p hph =>
    let s₁ : FilterState n := { s with
      phase := Function.update s.phase p .remainder
      level := Function.update s.level p ⟨0, p.pos⟩ }
    change FilterInv s₁
    have hat_erase : ∀ r, atRoomSet s₁ r = (atRoomSet s r).erase p := fun r =>
      filter_update_false (·.atOrAboveRoom r) s.phase p _ rfl
    have hab_erase : ∀ r, aboveRoomSet s₁ r = (aboveRoomSet s r).erase p := fun r =>
      filter_update_false (·.aboveRoom r) s.phase p _ rfl
    refine ⟨hloc', ?_, ?_, ?_⟩
    · intro r cleared hw
      rw [hat_erase r]
      dsimp only [s₁] at hw
      have hvp : s.victim r ≠ p := by rintro rfl; rw [Function.update_self] at hw; cases hw
      rw [Function.update_of_ne hvp] at hw
      intro q hq hmem
      exact hinv.cleared_disjoint r cleared hw q hq (Finset.mem_of_mem_erase hmem)
    · intro r hv
      rw [hab_erase r] at hv
      intro q hne
      rw [hat_erase r]
      intro hmem
      exact hinv.victim_unique_above r (Finset.mem_of_mem_erase hv) q hne
        (Finset.mem_of_mem_erase hmem)
    · intro r ⟨q, hq⟩
      rw [hat_erase r] at hq ⊢
      obtain ⟨hqp, hq_at⟩ := Finset.mem_erase.mp hq
      have hvp : s.victim r ≠ p := by
        intro heq
        have hp_above : s.victim r ∈ aboveRoomSet s r := by
          simp [aboveRoomSet, heq, hph, FilterPhase.aboveRoom]
        exact hinv.victim_unique_above r hp_above q (heq ▸ hqp) hq_at
      exact Finset.mem_erase.mpr ⟨hvp, hinv.victim_mem r ⟨q, hq_at⟩⟩

private theorem FilterState.Reachable.filterInv {n : ℕ} {s : FilterState n}
    (hr : s.Reachable) : FilterInv s := by
  obtain ⟨μs, hmtr⟩ := hr
  exact LTS.mtrInv_of_trInv (lts := filterLock n) (fun _ _ _ htr hi => filterInv_step hi htr)
    _ _ _ hmtr (filterInv_init n)

/-- Every process in `s.atLevel ℓ` has `(s.level p).val ≥ ℓ`. -/
theorem atLevel_level_ge {n : ℕ} {s : FilterState n} (hr : s.Reachable)
    {ℓ : ℕ} {p : Fin n} (hp : p ∈ s.atLevel ℓ) : ℓ ≤ (s.level p).val := by
  cases ℓ with
  | zero => exact Nat.zero_le _
  | succ k =>
    simp only [FilterState.atLevel] at hp
    split at hp
    · rename_i hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact filterLocalInv_level_ge_of_above (hr.filterInv.local_inv p) hp
    · exact absurd hp (Finset.notMem_empty p)

private theorem atRoomSet_subset_prev {n : ℕ} (s : FilterState n) (r : Fin (n - 1)) :
    atRoomSet s r ⊆ s.atLevel r.val := by
  intro p hp
  rcases hr0 : r.val with _ | k
  · simp [FilterState.atLevel]
  · have hk : k < n - 1 := by have := r.isLt; omega
    simp only [FilterState.atLevel, hk, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [atRoomSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    unfold FilterPhase.atOrAboveRoom at hp
    unfold FilterPhase.aboveRoom
    (cases hph : s.phase p <;> simp_all) <;> omega

/-- Inductive level-capacity invariant (proof infrastructure for Peterson's Fig. 3 protocol,
[Peterson1981], p. 116): in every reachable state of `filterLock n`, for every level `ℓ < n`, at
most `n - ℓ` processes belong to `s.atLevel ℓ` (having reached `level ≥ ℓ` and passed all waiting
rooms `< ℓ`). -/
theorem card_at_level_le {n : ℕ} {s : FilterState n} (hr : s.Reachable)
    (ℓ : ℕ) (hℓ : ℓ < n) : (s.atLevel ℓ).card ≤ n - ℓ := by
  have hinv := hr.filterInv
  induction ℓ with
  | zero => simp [FilterState.atLevel]
  | succ k ih =>
    have hk : k < n - 1 := by omega
    let r : Fin (n - 1) := ⟨k, hk⟩
    have hprev : (s.atLevel r.val).card ≤ n - k := ih (by omega)
    have heq_set : s.atLevel (k + 1) = aboveRoomSet s r := by
      simp [FilterState.atLevel, hk, aboveRoomSet, r]
    rw [heq_set]
    by_cases hne : (aboveRoomSet s r).Nonempty
    · have hat_ne : (atRoomSet s r).Nonempty := hne.mono (aboveRoomSet_subset_atRoomSet s r)
      have hv_at : s.victim r ∈ atRoomSet s r := hinv.victim_mem r hat_ne
      have hv_pool : s.victim r ∈ s.atLevel r.val := atRoomSet_subset_prev s r hv_at
      by_cases hv_ab : s.victim r ∈ aboveRoomSet s r
      · have hsub_single : aboveRoomSet s r ⊆ {s.victim r} := by
          intro q hq
          rw [Finset.mem_singleton]
          by_contra hne_q
          exact hinv.victim_unique_above r hv_ab q hne_q
            (aboveRoomSet_subset_atRoomSet s r hq)
        have hcard1 : (aboveRoomSet s r).card ≤ 1 :=
          le_trans (Finset.card_le_card hsub_single) (by simp)
        omega
      · have hsub_erase : aboveRoomSet s r ⊆ (s.atLevel r.val).erase (s.victim r) := by
          intro q hq
          refine Finset.mem_erase.mpr ⟨fun heq => hv_ab (heq ▸ hq), ?_⟩
          exact atRoomSet_subset_prev s r (aboveRoomSet_subset_atRoomSet s r hq)
        have hcard_er : (aboveRoomSet s r).card ≤ ((s.atLevel r.val).erase (s.victim r)).card :=
          Finset.card_le_card hsub_erase
        have her_eq : ((s.atLevel r.val).erase (s.victim r)).card = (s.atLevel r.val).card - 1 :=
          Finset.card_erase_of_mem hv_pool
        omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp

/-- **Mutual Exclusion for Peterson's Filter Lock** ([Peterson1981], Fig. 3, p. 116): in every
reachable state of `filterLock n`, at most one process is in `CriticalSection`. -/
theorem filterLock_mutualExclusion {n : ℕ} {s : FilterState n} (hr : s.Reachable)
    {p q : Fin n} (hp : s.inCS p) (hq : s.inCS q) : p = q := by
  by_cases hn2 : n ≤ 1
  · exact Fin.ext (by have := p.isLt; have := q.isLt; omega)
  · have hcap := card_at_level_le hr (n - 1) (by omega)
    have hmem : ∀ x : Fin n, s.inCS x → x ∈ s.atLevel (n - 1) := by
      intro x hx
      obtain ⟨k, heqk⟩ : ∃ k, n - 1 = k + 1 := ⟨n - 2, by omega⟩
      have hk : k < n - 1 := by omega
      unfold FilterState.inCS at hx
      rw [heqk]
      simp [FilterState.atLevel, hk, hx, FilterPhase.aboveRoom]
    have hsub : ({p, q} : Finset (Fin n)) ⊆ s.atLevel (n - 1) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hxp | hx'
      · rw [hxp]; exact hmem p hp
      · rw [Finset.mem_singleton.mp hx']; exact hmem q hq
    have hle1 : ({p, q} : Finset (Fin n)).card ≤ 1 := by
      have := Finset.card_le_card hsub
      omega
    by_contra hne
    rw [Finset.card_pair hne] at hle1
    omega

/-! ### Deadlock freedom of Peterson's filter lock -/

private theorem potential_le {n : ℕ} (s : FilterState n) :
    s.potential ≤ n * (n * (n + 2)) := by
  unfold FilterState.potential
  have hterm : ∀ p : Fin n, (s.phase p).potential ≤ n * (n + 2) := by
    intro p
    cases s.phase p with
    | remainder => exact Nat.zero_le _
    | ready ℓ =>
      simp only [FilterPhase.potential]
      have := ℓ.isLt
      have : (ℓ.val + 1) * (n + 2) ≤ n * (n + 2) := Nat.mul_le_mul_right (n + 2) this
      linarith
    | writeVictim r =>
      simp only [FilterPhase.potential]
      have hr : r.val + 1 ≤ n := by have := r.isLt; omega
      have : (r.val + 1) * (n + 2) ≤ n * (n + 2) := Nat.mul_le_mul_right (n + 2) hr
      linarith
    | waitRoom r cleared =>
      simp only [FilterPhase.potential]
      have hr : r.val + 2 ≤ n := by have := r.isLt; omega
      have hcl : cleared.card ≤ n := le_trans (Finset.card_le_univ _) (by simp)
      have : (r.val + 2) * (n + 2) ≤ n * (n + 2) := Nat.mul_le_mul_right (n + 2) hr
      linarith
    | cs => exact le_rfl
  calc Finset.univ.sum (fun p => (s.phase p).potential)
      ≤ Finset.univ.sum (fun _ : Fin n => n * (n + 2)) := Finset.sum_le_sum fun p _ => hterm p
    _ = n * (n * (n + 2)) := by simp

private theorem potential_update_gt {n : ℕ} {s s' : FilterState n} {p : Fin n}
    {ph' : FilterPhase n} (hupd : s'.phase = Function.update s.phase p ph')
    (hlt : (s.phase p).potential < ph'.potential) :
    s.potential < s'.potential := by
  unfold FilterState.potential
  have hrest : (Finset.univ.erase p).sum (fun q => (Function.update s.phase p ph' q).potential) =
      (Finset.univ.erase p).sum (fun q => (s.phase q).potential) :=
    Finset.sum_congr rfl fun q hq => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
  rw [hupd, ← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ p), hrest, Function.update_self]
  omega

private theorem nextAfterRoom_potential_gt {n : ℕ} (r : Fin (n - 1)) (c : ℕ) (hc : c < n) :
    r.val * (n + 2) + 3 + c < (nextAfterRoom r).potential := by
  unfold nextAfterRoom
  split
  · simp only [FilterPhase.potential]; ring_nf; omega
  · simp only [FilterPhase.potential]
    have hr : r.val + 2 ≤ n := by have := r.isLt; omega
    have : (r.val + 2) * (n + 2) ≤ n * (n + 2) := Nat.mul_le_mul_right (n + 2) hr
    linarith

/-- Single-step potential-progress lemma (proof infrastructure for
`filterLock_exists_cs_execution`): in any reachable state where the set of trying processes is
nonempty and no process is in `CriticalSection`, some trying process has an enabled step (advancing
from `.ready`/`.writeVictim`, passing the highest occupied waiting room `r_max` when not
`victim[r_max]`, or recording a lower-level witness at `r_max` when it is the unique occupant) that
strictly increases `FilterState.potential` without waking any remainder process. -/
theorem filterLock_step_progress {n : ℕ} {s : FilterState n} (hr : s.Reachable)
    (htry : ∃ p, s.isTrying p) (hno_cs : ∀ p, ¬ s.inCS p) :
    ∃ μ s', s.isTrying μ.actor ∧ (filterLock n).Tr s μ s' ∧
      s.potential < s'.potential := by
  have hinv := hr.filterInv
  by_cases h_imm : ∃ p, (∃ ℓ, s.phase p = .ready ℓ) ∨ (∃ r, s.phase p = .writeVictim r)
  · rcases h_imm with ⟨p, ⟨ℓ, hph⟩ | ⟨r, hph⟩⟩
    · by_cases hlt : ℓ.val + 1 < n
      · refine ⟨.setLevel p,
          { s with
            phase := Function.update s.phase p (.writeVictim ⟨ℓ.val, by omega⟩)
            level := Function.update s.level p ⟨ℓ.val + 1, hlt⟩ }, ?_, ?_, ?_⟩
        · simp [FilterAction.actor, FilterState.isTrying, hph, FilterPhase.isTrying]
        · simp [filterLock, filterStep?, hph, hlt]
        · exact potential_update_gt rfl (by simp [hph, FilterPhase.potential])
      · refine ⟨.enterCSOne p,
          { s with phase := Function.update s.phase p .cs }, ?_, ?_, ?_⟩
        · simp [FilterAction.actor, FilterState.isTrying, hph, FilterPhase.isTrying]
        · simp [filterLock, filterStep?, hph, hlt]
        · apply potential_update_gt rfl
          simp only [hph, FilterPhase.potential]
          have := ℓ.isLt
          have hmul : (ℓ.val + 1) * (n + 2) ≤ n * (n + 2) := Nat.mul_le_mul_right (n + 2) this
          linarith
    · refine ⟨.setVictim p,
        { s with
          phase := Function.update s.phase p (.waitRoom r ∅)
          victim := Function.update s.victim r p }, ?_, ?_, ?_⟩
      · simp [FilterAction.actor, FilterState.isTrying, hph, FilterPhase.isTrying]
      · simp [filterLock, filterStep?, hph]
      · exact potential_update_gt rfl (by simp [hph, FilterPhase.potential])
  · push Not at h_imm
    have hwait_of_trying : ∀ q, s.isTrying q → ∃ r cl, s.phase q = .waitRoom r cl := by
      intro q hq
      unfold FilterState.isTrying FilterPhase.isTrying at hq
      cases hph : s.phase q with
      | remainder | cs => simp [hph] at hq
      | ready ℓ => exact absurd hph ((h_imm q).1 ℓ)
      | writeVictim r => exact absurd hph ((h_imm q).2 r)
      | waitRoom r cl => exact ⟨r, cl, rfl⟩
    obtain ⟨p₀, hp₀_try⟩ := htry
    obtain ⟨r₀, _, hp₀_ph⟩ := hwait_of_trying p₀ hp₀_try
    let occRooms : Finset (Fin (n - 1)) :=
      Finset.univ.filter fun r => ∃ q, (s.phase q).waitRoomOf = some r
    have hocc_ne : occRooms.Nonempty := by
      refine ⟨r₀, Finset.mem_filter.mpr ⟨Finset.mem_univ r₀, p₀, ?_⟩⟩
      simp [hp₀_ph, FilterPhase.waitRoomOf]
    let r_max := occRooms.max' hocc_ne
    obtain ⟨p₁, hp₁_wr⟩ := (Finset.mem_filter.mp (Finset.max'_mem occRooms hocc_ne)).2
    obtain ⟨cl₁, hp₁_ph⟩ : ∃ cl₁, s.phase p₁ = .waitRoom r_max cl₁ := by
      cases hph : s.phase p₁ with
      | waitRoom r' cl' =>
        simp only [hph, FilterPhase.waitRoomOf, Option.some.injEq] at hp₁_wr
        subst hp₁_wr
        exact ⟨cl', rfl⟩
      | remainder | ready _ | writeVictim _ | cs =>
        simp [hph, FilterPhase.waitRoomOf] at hp₁_wr
    have hcl_lt_of_wait : ∀ p cl, s.phase p = .waitRoom r_max cl → cl.card < n := by
      intro p cl hp_ph
      have hp_not_cl : p ∉ cl := by
        have hl := hinv.local_inv p
        unfold filterLocalInv at hl; rw [hp_ph] at hl; exact hl.2
      have hsub : cl ⊆ Finset.univ.erase p :=
        fun x hx => Finset.mem_erase.mpr ⟨fun heq => hp_not_cl (heq ▸ hx), Finset.mem_univ x⟩
      have hle := Finset.card_le_card hsub
      have her : (Finset.univ.erase p).card = n - 1 := by simp
      have := p.pos; omega
    by_cases hex_nonvic : ∃ p cl, s.phase p = .waitRoom r_max cl ∧ s.victim r_max ≠ p
    · obtain ⟨p, cl, hp_ph, hvne⟩ := hex_nonvic
      refine ⟨.checkVictim p,
        { s with phase := Function.update s.phase p (nextAfterRoom r_max) }, ?_, ?_, ?_⟩
      · simp [FilterAction.actor, FilterState.isTrying, hp_ph, FilterPhase.isTrying]
      · simp [filterLock, filterStep?, hp_ph, hvne]
      · apply potential_update_gt rfl
        simp only [hp_ph, FilterPhase.potential]
        exact nextAfterRoom_potential_gt r_max cl.card (hcl_lt_of_wait p cl hp_ph)
    · push Not at hex_nonvic
      -- Every `q ≠ p₁` has `(s.level q).val < r_max.val + 1`.
      have hlv_lt_all : ∀ q, q ≠ p₁ → (s.level q).val < r_max.val + 1 := by
        intro q hqp₁
        have hl_q := hinv.local_inv q
        cases hph_q : s.phase q with
        | remainder =>
          unfold filterLocalInv at hl_q; rw [hph_q] at hl_q; omega
        | ready ℓ => exact absurd hph_q ((h_imm q).1 ℓ)
        | writeVictim r => exact absurd hph_q ((h_imm q).2 r)
        | cs => exact absurd hph_q (hno_cs q)
        | waitRoom r_q cl_q =>
          unfold filterLocalInv at hl_q; rw [hph_q] at hl_q
          have hr_le : r_q ≤ r_max := by
            refine Finset.le_max' occRooms r_q (Finset.mem_filter.mpr ⟨Finset.mem_univ r_q, q, ?_⟩)
            simp [hph_q, FilterPhase.waitRoomOf]
          have hr_ne : r_q ≠ r_max := fun heq => by
            have hvic := hex_nonvic q cl_q (heq ▸ hph_q)
            have hvic₁ := hex_nonvic p₁ cl₁ hp₁_ph
            exact hqp₁ (hvic.symm.trans hvic₁)
          have hr_lt : r_q.val < r_max.val := Fin.lt_def.mp (lt_of_le_of_ne hr_le hr_ne)
          omega
      have hn2 : 2 ≤ n := by have := r_max.isLt; omega
      by_cases hex_unclear : ∃ q, q ≠ p₁ ∧ q ∉ cl₁
      · obtain ⟨q, hqp₁, hq_nmem⟩ := hex_unclear
        have hlv_q := hlv_lt_all q hqp₁
        by_cases hall_cl : insert q cl₁ = Finset.univ.erase p₁
        · refine ⟨.checkLevel p₁ q,
            { s with phase := Function.update s.phase p₁ (nextAfterRoom r_max) }, ?_, ?_, ?_⟩
          · simp [FilterAction.actor, FilterState.isTrying, hp₁_ph, FilterPhase.isTrying]
          · simp only [filterLock, filterStep?, hp₁_ph, hqp₁, hlv_q, hall_cl, ne_eq,
              not_false_eq_true, ↓reduceIte]
          · apply potential_update_gt rfl
            simp only [hp₁_ph, FilterPhase.potential]
            exact nextAfterRoom_potential_gt r_max cl₁.card (hcl_lt_of_wait p₁ cl₁ hp₁_ph)
        · refine ⟨.checkLevel p₁ q,
            { s with phase := Function.update s.phase p₁ (.waitRoom r_max (insert q cl₁)) },
            ?_, ?_, ?_⟩
          · simp [FilterAction.actor, FilterState.isTrying, hp₁_ph, FilterPhase.isTrying]
          · simp only [filterLock, filterStep?, hp₁_ph, hqp₁, hlv_q, hall_cl, ne_eq,
              not_false_eq_true, ↓reduceIte]
          · apply potential_update_gt rfl
            simp only [hp₁_ph, FilterPhase.potential, Finset.card_insert_of_notMem hq_nmem]
            omega
      · push Not at hex_unclear
        let q₀ : Fin n := ⟨(p₁.val + 1) % n, Nat.mod_lt _ (by omega)⟩
        have hq₀_ne : q₀ ≠ p₁ := by
          intro heq
          have hv : (p₁.val + 1) % n = p₁.val := congrArg Fin.val heq
          by_cases hlast : p₁.val + 1 = n
          · rw [hlast, Nat.mod_self] at hv; omega
          · rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
        have hp₁_not_cl : p₁ ∉ cl₁ := by
          have hl := hinv.local_inv p₁
          unfold filterLocalInv at hl; rw [hp₁_ph] at hl; exact hl.2
        have hall_cl : insert q₀ cl₁ = Finset.univ.erase p₁ := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_univ, and_true]
          constructor
          · rintro (rfl | hx); · exact hq₀_ne
            · exact fun heq => hp₁_not_cl (heq ▸ hx)
          · intro hne; exact Or.inr (hex_unclear x hne)
        have hlv_q₀ := hlv_lt_all q₀ hq₀_ne
        refine ⟨.checkLevel p₁ q₀,
          { s with phase := Function.update s.phase p₁ (nextAfterRoom r_max) }, ?_, ?_, ?_⟩
        · simp [FilterAction.actor, FilterState.isTrying, hp₁_ph, FilterPhase.isTrying]
        · simp only [filterLock, filterStep?, hp₁_ph, hq₀_ne, hlv_q₀, hall_cl, ne_eq,
            not_false_eq_true, ↓reduceIte]
        · apply potential_update_gt rfl
          simp only [hp₁_ph, FilterPhase.potential]
          exact nextAfterRoom_potential_gt r_max cl₁.card (hcl_lt_of_wait p₁ cl₁ hp₁_ph)

private theorem trying_step_leads_to_trying_or_cs {n : ℕ} {s s' : FilterState n}
    {μ : FilterAction n} (htry_act : s.isTrying μ.actor) (htr : (filterLock n).Tr s μ s') :
    s'.isTrying μ.actor ∨ s'.inCS μ.actor := by
  have hnext : ∀ (p : Fin n) (r : Fin (n - 1)),
      FilterState.isTrying { s with phase := Function.update s.phase p (nextAfterRoom r) } p ∨
        FilterState.inCS { s with phase := Function.update s.phase p (nextAfterRoom r) } p := by
    intro p r
    unfold nextAfterRoom
    split
    · exact Or.inl (by simp [FilterState.isTrying, FilterPhase.isTrying])
    · exact Or.inr (by simp [FilterState.inCS])
  cases filterStepShape_of_step htr with
  | reqCS p hph =>
    simp [FilterAction.actor, FilterState.isTrying, hph, FilterPhase.isTrying] at htry_act
  | csOne p => exact Or.inr (by simp [FilterAction.actor, FilterState.inCS])
  | setLv p =>
    exact Or.inl (by simp [FilterAction.actor, FilterState.isTrying, FilterPhase.isTrying])
  | setVic p =>
    exact Or.inl (by simp [FilterAction.actor, FilterState.isTrying, FilterPhase.isTrying])
  | passVic p r => exact hnext p r
  | spinVic => exact Or.inl htry_act
  | passLv p _ r => exact hnext p r
  | recLv p =>
    exact Or.inl (by simp [FilterAction.actor, FilterState.isTrying, FilterPhase.isTrying])
  | spinLv => exact Or.inl htry_act
  | exit p hph =>
    simp [FilterAction.actor, FilterState.isTrying, hph, FilterPhase.isTrying] at htry_act

/-- **Finite Progress Witness for `filterLock`**: from any reachable state where at least one
process is trying (`∃ p, s.isTrying p`), there exists **an** enabled finite execution stepping only
trying processes (never waking `.remainder` processes or exiting `.cs`) that reaches a state with a
process in `CriticalSection`.

This provides an existential finite execution witness (which may schedule several trying
processes, can be empty if some process is already in `.cs`, and only promises that some process is
in `.cs` at the end), rather than progress across all fair infinite executions (`OmegaExecution`),
which requires sequencing the waiting-room scan (#7296). -/
theorem filterLock_exists_cs_execution {n : ℕ} {s : FilterState n} (hr : s.Reachable)
    (htry : ∃ p, s.isTrying p) :
    ∃ μs s', (filterLock n).MTr s μs s' ∧
      (∀ μ ∈ μs, ∀ p, μ ≠ .requestCS p ∧ μ ≠ .exitCS p) ∧
      (∃ p, s'.inCS p) := by
  suffices ∀ B (s : FilterState n), s.Reachable → (∃ p, s.isTrying p) →
      n * (n * (n + 2)) - s.potential ≤ B →
      ∃ μs s', (filterLock n).MTr s μs s' ∧
        (∀ μ ∈ μs, ∀ p, μ ≠ .requestCS p ∧ μ ≠ .exitCS p) ∧
        (∃ p, s'.inCS p) from
    this (n * (n * (n + 2)) - s.potential) s hr htry le_rfl
  intro B
  induction B with
  | zero =>
    intro s hr htry hB0
    by_cases hex_cs : ∃ p, s.inCS p
    · exact ⟨[], s, .refl, fun _ h => (List.not_mem_nil h).elim, hex_cs⟩
    · push Not at hex_cs
      obtain ⟨μ, s', _, htr, hpot_lt⟩ := filterLock_step_progress hr htry hex_cs
      have hbound := potential_le s'
      omega
  | succ B ih =>
    intro s hr htry hB
    by_cases hex_cs : ∃ p, s.inCS p
    · exact ⟨[], s, .refl, fun _ h => (List.not_mem_nil h).elim, hex_cs⟩
    · push Not at hex_cs
      obtain ⟨μ, s', htry_act, htr, hpot_lt⟩ := filterLock_step_progress hr htry hex_cs
      have hμ_clean : ∀ p, μ ≠ .requestCS p ∧ μ ≠ .exitCS p := by
        intro p; constructor <;> rintro rfl
        · simp only [filterLock, filterStep?] at htr
          split at htr <;> simp only [Option.some.injEq, reduceCtorEq] at htr
          rename_i hph
          simp [FilterAction.actor, FilterState.isTrying, hph, FilterPhase.isTrying] at htry_act
        · simp only [filterLock, filterStep?] at htr
          split at htr <;> simp only [Option.some.injEq, reduceCtorEq] at htr
          rename_i hph
          simp [FilterAction.actor, FilterState.isTrying, hph, FilterPhase.isTrying] at htry_act
      have hr' : s'.Reachable := hr.step htr
      rcases trying_step_leads_to_trying_or_cs htry_act htr with htry' | hcs'
      · have hbound' := potential_le s'
        obtain ⟨μs, s'', hmtr, hclean, hcs''⟩ :=
          ih s' hr' ⟨μ.actor, htry'⟩ (by omega)
        refine ⟨μ :: μs, s'', .stepL htr hmtr, ?_, hcs''⟩
        intro ν hν p
        rcases List.mem_cons.mp hν with rfl | hmem
        · exact hμ_clean p
        · exact hclean ν hmem p
      · refine ⟨[μ], s', LTS.MTr.single (filterLock n) htr, ?_, ⟨μ.actor, hcs'⟩⟩
        intro ν hν p
        rw [List.mem_singleton.mp hν]
        exact hμ_clean p

/-! ## Part 2: General Multi-Writer Register Mutex Protocols & Single-Register Impossibility -/

/-- Standard four-phase section partition of a shared-memory mutual-exclusion process. -/
inductive MutexSection where
  /-- Noncritical remainder section. -/
  | remainder
  /-- Entry / doorway / waiting section trying to enter `cs`. -/
  | trying
  /-- Critical section (`CS`). -/
  | cs
  /-- Exit protocol resetting shared variables before returning to `remainder`. -/
  | exit
  deriving @[expose] DecidableEq

/-- Elementary atomic step of a process over multi-writer atomic read/write registers `Reg` with
value domain `Val` (no read-modify-write primitives). -/
inductive RegStep (Reg Val State : Type*) where
  /-- Internal local transition neither reading nor writing shared memory. -/
  | localStep (next : State)
  /-- Atomic read of shared register `r`, branching to `cont v` on observed value `v`. -/
  | read (r : Reg) (cont : Val → State)
  /-- Atomic blind write `r := val`, transitioning to local state `next`. -/
  | write (r : Reg) (val : Val) (next : State)

namespace RegStep

/-- Whether `st'` is a possible successor local state of a `RegStep`. -/
@[expose]
def NextState {Reg Val State : Type*} : RegStep Reg Val State → State → Prop
  | .localStep next, st' => st' = next
  | .read _ cont, st' => ∃ v, cont v = st'
  | .write _ _ next, st' => st' = next

/-- Whether a `RegStep` is a shared-register write. -/
@[expose]
def isWrite {Reg Val State : Type*} : RegStep Reg Val State → Bool
  | .write _ _ _ => true
  | .localStep _ | .read _ _ => false

end RegStep

/-- General deterministic asynchronous mutual-exclusion protocol over processes `P`, atomic
multi-writer read/write registers `Reg` with values in `Val`, and local process states `State`. -/
structure MutexProtocol (P Reg Val State : Type*) where
  /-- Initial contents of shared registers. -/
  initMem : Reg → Val
  /-- Initial local state of each process. -/
  initLocal : P → State
  /-- Section classification (`remainder`, `trying`, `cs`, `exit`) of a process's local state. -/
  sectionOf : P → State → MutexSection
  /-- Invocation transition when `p` leaves `.remainder` to acquire the lock. -/
  enterTrying : P → State → State
  /-- Deterministic protocol step of `p` while in `.trying` or `.exit`. -/
  step : P → State → RegStep Reg Val State
  /-- Environment transition when `p` leaves `.cs` into `.exit` or `.remainder`. -/
  exitCS : P → State → State
  /-- Every process starts in `.remainder`. -/
  init_remainder : ∀ p, sectionOf p (initLocal p) = .remainder
  /-- Leaving `.remainder` places `p` into `.trying` or `.cs`. -/
  enterTrying_section : ∀ p st, sectionOf p st = .remainder →
    sectionOf p (enterTrying p st) = .trying ∨ sectionOf p (enterTrying p st) = .cs
  /-- A trying step keeps `p` in `.trying` or enters `.cs` (never silently aborting to
  `.remainder` or `.exit` without first entering `.cs`). -/
  trying_step_section : ∀ p st, sectionOf p st = .trying →
    ∀ st', (step p st).NextState st' →
      sectionOf p st' = .trying ∨ sectionOf p st' = .cs

/-- Global configuration of a `MutexProtocol`: shared register memory and local process states. -/
@[ext]
structure MutexConfig (P Reg Val State : Type*) where
  /-- Shared register contents. -/
  mem : Reg → Val
  /-- Local state of each process. -/
  localState : P → State

instance {P Reg Val State : Type*}
    [Fintype P] [Fintype Reg] [DecidableEq Val] [DecidableEq State] :
    DecidableEq (MutexConfig P Reg Val State) :=
  fun a b =>
    decidable_of_iff
      ((∀ r, a.mem r = b.mem r) ∧ (∀ p, a.localState p = b.localState p))
      ⟨fun ⟨hm, hl⟩ => MutexConfig.ext (funext hm) (funext hl),
        fun h => h ▸ ⟨fun _ => rfl, fun _ => rfl⟩⟩

/-- Transition labels of a `MutexProtocol` LTS. -/
inductive MutexAction (P : Type*) where
  /-- Process `p` leaves `.remainder` via `enterTrying`. -/
  | enter (p : P)
  /-- Active process `p` (in `.trying` or `.exit`) executes one atomic `RegStep`. -/
  | step (p : P)
  /-- Process `p` leaves `.cs` via `exitCS`. -/
  | exit (p : P)
  /-- Stuttering step preserving the configuration. -/
  | stutter
  deriving @[expose] DecidableEq

namespace MutexConfig

variable {P Reg Val State : Type*}

/-- Process `p` is in its critical section under `π`. -/
@[expose]
def inCS (c : MutexConfig P Reg Val State) (π : MutexProtocol P Reg Val State) (p : P) : Prop :=
  π.sectionOf p (c.localState p) = .cs

/-- Process `p` is in its trying section under `π`. -/
@[expose]
def isTrying (c : MutexConfig P Reg Val State) (π : MutexProtocol P Reg Val State) (p : P) : Prop :=
  π.sectionOf p (c.localState p) = .trying

/-- Process `p` has an active protocol step enabled (`.trying` or `.exit`). -/
@[expose]
def isActive (c : MutexConfig P Reg Val State) (π : MutexProtocol P Reg Val State) (p : P) : Prop :=
  π.sectionOf p (c.localState p) = .trying ∨ π.sectionOf p (c.localState p) = .exit

instance (c : MutexConfig P Reg Val State) (π : MutexProtocol P Reg Val State) (p : P) :
    Decidable (c.inCS π p) :=
  inferInstanceAs (Decidable (π.sectionOf p (c.localState p) = MutexSection.cs))

instance (c : MutexConfig P Reg Val State) (π : MutexProtocol P Reg Val State) (p : P) :
    Decidable (c.isTrying π p) :=
  inferInstanceAs (Decidable (π.sectionOf p (c.localState p) = MutexSection.trying))

instance (c : MutexConfig P Reg Val State) (π : MutexProtocol P Reg Val State) (p : P) :
    Decidable (c.isActive π p) :=
  inferInstanceAs
    (Decidable
      (π.sectionOf p (c.localState p) = MutexSection.trying ∨
        π.sectionOf p (c.localState p) = MutexSection.exit))

end MutexConfig

namespace MutexProtocol

variable {P Reg Val State : Type*}

/-- Initial configuration `(initMem, initLocal)` of `π`. -/
@[expose]
def initConfig (π : MutexProtocol P Reg Val State) : MutexConfig P Reg Val State where
  mem := π.initMem
  localState := π.initLocal

/-- Execute `p`'s atomic `RegStep` on configuration `c`. -/
@[expose]
def execRegStep [DecidableEq P] [DecidableEq Reg]
    (π : MutexProtocol P Reg Val State) (c : MutexConfig P Reg Val State) (p : P) :
    MutexConfig P Reg Val State :=
  match π.step p (c.localState p) with
  | .localStep next =>
    { c with localState := Function.update c.localState p next }
  | .read r cont =>
    { c with localState := Function.update c.localState p (cont (c.mem r)) }
  | .write r val next =>
    { mem := Function.update c.mem r val
      localState := Function.update c.localState p next }

/-- Computable single-step transition evaluator for `π`. -/
@[expose]
def step? [DecidableEq P] [DecidableEq Reg]
    (π : MutexProtocol P Reg Val State) (c : MutexConfig P Reg Val State) (μ : MutexAction P) :
    Option (MutexConfig P Reg Val State) :=
  match μ with
  | .enter p =>
    if π.sectionOf p (c.localState p) = .remainder then
      some
        { c with localState := Function.update c.localState p (π.enterTrying p (c.localState p)) }
    else none
  | .step p =>
    if c.isActive π p then
      some (π.execRegStep c p)
    else none
  | .exit p =>
    if c.inCS π p then
      some { c with localState := Function.update c.localState p (π.exitCS p (c.localState p)) }
    else none
  | .stutter => some c

/-- Computable multi-step trace evaluator for `π.step?`. -/
@[expose]
def stepTrace? [DecidableEq P] [DecidableEq Reg]
    (π : MutexProtocol P Reg Val State) (c : MutexConfig P Reg Val State) :
    List (MutexAction P) → Option (MutexConfig P Reg Val State)
  | [] => some c
  | μ :: μs => (π.step? c μ).bind (fun c' => π.stepTrace? c' μs)

/-- Labelled transition system of `π`. -/
@[expose]
def lts [DecidableEq P] [DecidableEq Reg] (π : MutexProtocol P Reg Val State) :
    LTS (MutexConfig P Reg Val State) (MutexAction P) where
  Tr c μ c' := π.step? c μ = some c'

theorem stepTrace?_eq_some_iff [DecidableEq P] [DecidableEq Reg]
    (π : MutexProtocol P Reg Val State) {c c' : MutexConfig P Reg Val State}
    {μs : List (MutexAction P)} :
    π.stepTrace? c μs = some c' ↔ π.lts.MTr c μs c' := by
  induction μs generalizing c with
  | nil => simp [stepTrace?]
  | cons μ μs ih =>
    simp only [stepTrace?, Option.bind_eq_some_iff, LTS.MTr.cons_iff]
    exact exists_congr fun c₁ => and_congr_right fun _ => ih

/-- Reachability from `π.initConfig` in `π.lts`. -/
@[expose]
def Reachable [DecidableEq P] [DecidableEq Reg]
    (π : MutexProtocol P Reg Val State) (c : MutexConfig P Reg Val State) : Prop :=
  π.lts.CanReach π.initConfig c

theorem Reachable.init [DecidableEq P] [DecidableEq Reg] (π : MutexProtocol P Reg Val State) :
    π.Reachable π.initConfig :=
  LTS.CanReach.refl π.lts π.initConfig

theorem Reachable.step_tr [DecidableEq P] [DecidableEq Reg] {π : MutexProtocol P Reg Val State}
    {c c' : MutexConfig P Reg Val State} {μ : MutexAction P}
    (hr : π.Reachable c) (htr : π.lts.Tr c μ c') : π.Reachable c' := by
  obtain ⟨μs, hmtr⟩ := hr
  exact ⟨μs ++ [μ], hmtr.stepR π.lts htr⟩

theorem Reachable.mTr [DecidableEq P] [DecidableEq Reg] {π : MutexProtocol P Reg Val State}
    {c c' : MutexConfig P Reg Val State} {μs : List (MutexAction P)}
    (hr : π.Reachable c) (hmtr : π.lts.MTr c μs c') : π.Reachable c' := by
  obtain ⟨μs₀, hmtr₀⟩ := hr
  exact ⟨μs₀ ++ μs, hmtr₀.comp π.lts hmtr⟩

/-- **Mutual Exclusion**: in every reachable configuration, at most one process is in `.cs`. -/
@[expose]
def MutuallyExclusive [DecidableEq P] [DecidableEq Reg]
    (π : MutexProtocol P Reg Val State) : Prop :=
  ∀ c, π.Reachable c → ∀ p q, c.inCS π p → c.inCS π q → p = q

/-- Weak step fairness for active processes (`.trying` or `.exit`); processes in `.remainder` may
remain quiescent indefinitely. -/
@[expose]
def WeakFair (π : MutexProtocol P Reg Val State)
    (ss : ωSequence (MutexConfig P Reg Val State)) (μs : ωSequence (MutexAction P)) : Prop :=
  ∀ p i, (∀ k ≥ i, (ss k).isActive π p) → ∃ k ≥ i, μs k = .step p

/-- Every process entering `.cs` eventually exits `.cs`. -/
@[expose]
def CSEventuallyExits (π : MutexProtocol P Reg Val State)
    (ss : ωSequence (MutexConfig P Reg Val State)) (μs : ωSequence (MutexAction P)) : Prop :=
  ∀ p i, (ss i).inCS π p → ∃ k ≥ i, μs k = .exit p

/-- **Deadlock Freedom** (critical-section entry from an initially trying state): in every infinite
execution from a reachable configuration with at least one trying process, assuming `WeakFair`
(scheduling active processes in `.trying` or `.exit`) and `CSEventuallyExits`, some process
eventually reaches `.cs` (`∃ k q, (ss k).inCS π q`).

Whereas [BurnsLynch1993] (§3, pp. 174–175) defines global progress as some process changing regions
in each nonnull fair history (stepping every process outside `.remainder`), this predicate asks for
some process to reach `.cs` from an initially trying state under `WeakFair` and
`CSEventuallyExits`. -/
@[expose]
def DeadlockFree [DecidableEq P] [DecidableEq Reg] (π : MutexProtocol P Reg Val State) : Prop :=
  ∀ ss μs, π.Reachable (ss 0) → π.lts.OmegaExecution ss μs →
    π.WeakFair ss μs → π.CSEventuallyExits ss μs →
    (∃ p, (ss 0).isTrying π p) → ∃ k q, (ss k).inCS π q

/-- Combined specification: `π` achieves both `MutuallyExclusive` and `DeadlockFree`. -/
@[expose]
def DeadlockFreeMutex [DecidableEq P] [DecidableEq Reg]
    (π : MutexProtocol P Reg Val State) : Prop :=
  π.MutuallyExclusive ∧ π.DeadlockFree

end MutexProtocol

/-! ### Covering-write proof of the single-register impossibility step -/

section SingleRegisterImpossibility

variable {P Reg Val State : Type*} [DecidableEq P] [DecidableEq Reg]

/-- Iterate `k` solo `execRegStep` transitions of process `p` from `c`. -/
private def soloIter (π : MutexProtocol P Reg Val State) (p : P) :
    ℕ → MutexConfig P Reg Val State → MutexConfig P Reg Val State
  | 0, c => c
  | k + 1, c => soloIter π p k (π.execRegStep c p)

private theorem soloIter_succ_right (π : MutexProtocol P Reg Val State) (p : P) :
    ∀ k (c : MutexConfig P Reg Val State),
      soloIter π p (k + 1) c = π.execRegStep (soloIter π p k c) p
  | 0, _ => rfl
  | k + 1, c => soloIter_succ_right π p k (π.execRegStep c p)

private theorem soloIter_add (π : MutexProtocol P Reg Val State) (p : P) :
    ∀ m n (c : MutexConfig P Reg Val State),
      soloIter π p (m + n) c = soloIter π p n (soloIter π p m c)
  | 0, _, _ => by simp [soloIter]
  | m + 1, n, c => by
    rw [Nat.succ_add]
    exact soloIter_add π p m n (π.execRegStep c p)

private theorem execRegStep_nextState (π : MutexProtocol P Reg Val State)
    (c : MutexConfig P Reg Val State) (p : P) :
    (π.step p (c.localState p)).NextState ((π.execRegStep c p).localState p) := by
  unfold MutexProtocol.execRegStep
  cases hst : π.step p (c.localState p) with
  | localStep next => simp [RegStep.NextState]
  | read r cont => exact ⟨c.mem r, by simp⟩
  | write r val next => simp [RegStep.NextState]

private theorem execRegStep_other {π : MutexProtocol P Reg Val State}
    {c : MutexConfig P Reg Val State} {p q : P} (hq : q ≠ p) :
    (π.execRegStep c p).localState q = c.localState q := by
  unfold MutexProtocol.execRegStep
  cases π.step p (c.localState p) <;> simp [Function.update_of_ne hq]

private theorem execRegStep_mem_of_not_write {π : MutexProtocol P Reg Val State}
    {c : MutexConfig P Reg Val State} {p : P}
    (hnw : (π.step p (c.localState p)).isWrite = false) :
    (π.execRegStep c p).mem = c.mem := by
  unfold MutexProtocol.execRegStep
  cases h : π.step p (c.localState p) <;> simp_all [RegStep.isWrite]

private theorem soloIter_mem_of_no_write (π : MutexProtocol P Reg Val State) (p : P) :
    ∀ m (c : MutexConfig P Reg Val State),
      (∀ i < m, (π.step p ((soloIter π p i c).localState p)).isWrite = false) →
      (soloIter π p m c).mem = c.mem
  | 0, _, _ => rfl
  | m + 1, c, hnw => by
    rw [soloIter_succ_right, execRegStep_mem_of_not_write (hnw m (Nat.lt_succ_self m))]
    exact soloIter_mem_of_no_write π p m c (fun i hi => hnw i (Nat.lt_succ_of_lt hi))

private theorem execRegStep_congr {π : MutexProtocol P Reg Val State}
    {a b : MutexConfig P Reg Val State} {p : P}
    (hmem : a.mem = b.mem) (hloc : a.localState p = b.localState p) :
    (π.execRegStep a p).mem = (π.execRegStep b p).mem ∧
      (π.execRegStep a p).localState p = (π.execRegStep b p).localState p := by
  unfold MutexProtocol.execRegStep
  rw [hloc, hmem]
  cases π.step p (b.localState p) <;> simp

/-- Replaying `k` solo steps of `p` from a configuration `b` that agrees with `a` on `mem` and
`localState p`, when `a`'s `k` solo steps stay in `.trying`, produces a valid `MTr` from `b`
matching `soloIter π p k a` on `mem` and `localState p` while leaving every `q ≠ p` unchanged. -/
private theorem soloIter_replay (π : MutexProtocol P Reg Val State) (p : P) :
    ∀ k (a b : MutexConfig P Reg Val State),
      a.mem = b.mem → a.localState p = b.localState p →
      (∀ j < k, (soloIter π p j a).isTrying π p) →
      (soloIter π p k a).mem = (soloIter π p k b).mem ∧
        (soloIter π p k a).localState p = (soloIter π p k b).localState p ∧
        (∀ q ≠ p, (soloIter π p k b).localState q = b.localState q) ∧
        π.lts.MTr b (List.replicate k (.step p)) (soloIter π p k b)
  | 0, _, b, hmem, hloc, _ => ⟨hmem, hloc, fun _ _ => rfl, .refl⟩
  | k + 1, a, b, hmem, hloc, htry => by
    have htry0_a : a.isTrying π p := htry 0 (Nat.zero_lt_succ k)
    have htry0_b : b.isTrying π p := by
      unfold MutexConfig.isTrying at htry0_a ⊢; rwa [← hloc]
    have hact_b : b.isActive π p := Or.inl htry0_b
    have htr_b : π.lts.Tr b (.step p) (π.execRegStep b p) := by
      simp [MutexProtocol.lts, MutexProtocol.step?, hact_b]
    obtain ⟨hmem1, hloc1⟩ := execRegStep_congr hmem hloc
    obtain ⟨hmem_k, hloc_k, hoth_k, hmtr_k⟩ :=
      soloIter_replay π p k (π.execRegStep a p) (π.execRegStep b p) hmem1 hloc1
        (fun j hj => htry (j + 1) (Nat.succ_lt_succ hj))
    refine ⟨hmem_k, hloc_k, fun q hqp => ?_, .stepL htr_b hmtr_k⟩
    exact (hoth_k q hqp).trans (execRegStep_other hqp)

/-- Under weak-fairness `DeadlockFree`, any process `p` invoking `enterTrying` solo from
`π.initConfig` (while all `q ≠ p` remain quiescently in `.remainder`) enters `.cs` after some
minimal number `k` of solo `execRegStep` transitions, staying in `.trying` for all `j < k`. -/
private theorem solo_enters_cs_from_init {π : MutexProtocol P Reg Val State}
    (hdf : π.DeadlockFree) (p : P) :
    let c_enter :=
      { π.initConfig with
        localState := Function.update π.initConfig.localState p (π.enterTrying p (π.initLocal p)) }
    π.Reachable c_enter ∧
      ∃ k, (soloIter π p k c_enter).inCS π p ∧
        (∀ j < k, (soloIter π p j c_enter).isTrying π p) ∧
        (∀ q ≠ p, (soloIter π p k c_enter).localState q = π.initLocal q) := by
  intro c_enter
  have hrem_p : π.sectionOf p (π.initConfig.localState p) = .remainder := π.init_remainder p
  have htr_enter : π.lts.Tr π.initConfig (.enter p) c_enter := by
    simp only [MutexProtocol.lts, MutexProtocol.step?, hrem_p, ↓reduceIte, Option.some.injEq]
    rfl
  have hr_enter : π.Reachable c_enter := (MutexProtocol.Reachable.init π).step_tr htr_enter
  refine ⟨hr_enter, ?_⟩
  rcases π.enterTrying_section p (π.initLocal p) (π.init_remainder p) with htry0 | hcs0
  · have htry_enter : c_enter.isTrying π p := by
      dsimp only [MutexConfig.isTrying, c_enter, MutexProtocol.initConfig]
      rw [Function.update_self]
      exact htry0
    have hex_cs : ∃ m, (soloIter π p m c_enter).inCS π p := by
      by_contra! hnever_cs
      have hall_try : ∀ m, (soloIter π p m c_enter).isTrying π p ∧
          ∀ q ≠ p, (soloIter π p m c_enter).localState q = π.initLocal q := by
        intro m
        induction m with
        | zero =>
          refine ⟨htry_enter, fun q hqp => ?_⟩
          simp [soloIter, c_enter, MutexProtocol.initConfig, Function.update_of_ne hqp]
        | succ m ih =>
          obtain ⟨htry_m, hoth_m⟩ := ih
          have hsec_next := π.trying_step_section p _ htry_m _
            (execRegStep_nextState π (soloIter π p m c_enter) p)
          refine ⟨?_, fun q hqp => ?_⟩
          · rcases hsec_next with htry_next | hcs_next
            · rw [soloIter_succ_right]; exact htry_next
            · have hcs_succ : (soloIter π p (m + 1) c_enter).inCS π p := by
                rw [soloIter_succ_right]; exact hcs_next
              exact absurd hcs_succ (hnever_cs (m + 1))
          · rw [soloIter_succ_right]
            exact (execRegStep_other hqp).trans (hoth_m q hqp)
      let ss : ωSequence (MutexConfig P Reg Val State) := ⟨fun m => soloIter π p m c_enter⟩
      let μs : ωSequence (MutexAction P) := ⟨fun _ => .step p⟩
      have hss : ∀ m, ss m = soloIter π p m c_enter := fun _ => rfl
      have hμs : ∀ m, μs m = .step p := fun _ => rfl
      have hexec : π.lts.OmegaExecution ss μs := by
        intro m
        rw [hss, hss, hμs, soloIter_succ_right]
        have hact : (soloIter π p m c_enter).isActive π p := Or.inl (hall_try m).1
        simp [MutexProtocol.lts, MutexProtocol.step?, hact]
      have hfair : π.WeakFair ss μs := by
        intro q i hact_all
        by_cases hqp : q = p
        · subst hqp; exact ⟨i, le_rfl, rfl⟩
        · exfalso
          have hact_i := hact_all i le_rfl
          rw [hss] at hact_i
          have hrem_q : π.sectionOf q ((soloIter π p i c_enter).localState q) = .remainder := by
            rw [(hall_try i).2 q hqp]; exact π.init_remainder q
          unfold MutexConfig.isActive at hact_i
          rw [hrem_q] at hact_i
          rcases hact_i with h1 | h1 <;> cases h1
      have hcs_exit : π.CSEventuallyExits ss μs := by
        intro q i hcs_i
        exfalso
        rw [hss] at hcs_i
        by_cases hqp : q = p
        · subst hqp; exact hnever_cs i hcs_i
        · have hrem_q : π.sectionOf q ((soloIter π p i c_enter).localState q) = .remainder := by
            rw [(hall_try i).2 q hqp]; exact π.init_remainder q
          unfold MutexConfig.inCS at hcs_i
          rw [hrem_q] at hcs_i; cases hcs_i
      obtain ⟨k, q, hcs_kq⟩ := hdf ss μs hr_enter hexec hfair hcs_exit ⟨p, htry_enter⟩
      rw [hss] at hcs_kq
      by_cases hqp : q = p
      · subst hqp; exact hnever_cs k hcs_kq
      · have hrem_q : π.sectionOf q ((soloIter π p k c_enter).localState q) = .remainder := by
          rw [(hall_try k).2 q hqp]; exact π.init_remainder q
        unfold MutexConfig.inCS at hcs_kq
        rw [hrem_q] at hcs_kq; cases hcs_kq
    let k := Nat.find hex_cs
    have hk_cs : (soloIter π p k c_enter).inCS π p := Nat.find_spec hex_cs
    have hprefix : ∀ j ≤ k,
        (j < k → (soloIter π p j c_enter).isTrying π p) ∧
          (∀ q ≠ p, (soloIter π p j c_enter).localState q = π.initLocal q) := by
      intro j hj
      induction j with
      | zero =>
        refine ⟨fun _ => htry_enter, fun q hqp => ?_⟩
        simp [soloIter, c_enter, MutexProtocol.initConfig, Function.update_of_ne hqp]
      | succ j ih =>
        obtain ⟨htry_j_imp, hoth_j⟩ := ih (Nat.le_of_succ_le hj)
        have htry_j : (soloIter π p j c_enter).isTrying π p :=
          htry_j_imp (Nat.lt_of_succ_le hj)
        have hsec_next := π.trying_step_section p _ htry_j _
          (execRegStep_nextState π (soloIter π p j c_enter) p)
        refine ⟨fun hj1_lt => ?_, fun q hqp => ?_⟩
        · have hnot_cs : ¬ (soloIter π p (j + 1) c_enter).inCS π p := Nat.find_min hex_cs hj1_lt
          rcases hsec_next with htry_next | hcs_next
          · rw [soloIter_succ_right]; exact htry_next
          · exfalso
            apply hnot_cs
            rw [soloIter_succ_right]; exact hcs_next
        · rw [soloIter_succ_right]
          exact (execRegStep_other hqp).trans (hoth_j q hqp)
    exact ⟨k, hk_cs, fun j hj => (hprefix j (le_of_lt hj)).1 hj, (hprefix k le_rfl).2⟩
  · refine ⟨0, ?_, fun _ h => absurd h (Nat.not_lt_zero _), fun q hqp => ?_⟩
    · dsimp only [soloIter, MutexConfig.inCS, c_enter, MutexProtocol.initConfig]
      rw [Function.update_self]; exact hcs0
    · dsimp only [soloIter, c_enter, MutexProtocol.initConfig]
      exact Function.update_of_ne hqp _ _

/-- From any reachable configuration `c` whose shared memory still equals `π.initMem` and where
`p₁ ≠ p₀` is still at `π.initLocal p₁`, `p₁` can enter trying and replay its solo run into `.cs`
without modifying `c.localState p₀`. -/
private theorem run_second_solo_into_cs {π : MutexProtocol P Reg Val State}
    (hdf : π.DeadlockFree) {c : MutexConfig P Reg Val State} (hr : π.Reachable c)
    {p₀ p₁ : P} (hp_ne : p₀ ≠ p₁)
    (hmem : c.mem = π.initMem) (hloc₁ : c.localState p₁ = π.initLocal p₁) :
    ∃ c', π.Reachable c' ∧ c'.inCS π p₁ ∧ c'.localState p₀ = c.localState p₀ := by
  let c_enter₁ : MutexConfig P Reg Val State :=
    { π.initConfig with
      localState := Function.update π.initConfig.localState p₁ (π.enterTrying p₁ (π.initLocal p₁)) }
  obtain ⟨_, k₁, hcs₁, htry₁, _⟩ := solo_enters_cs_from_init hdf p₁
  have hrem₁ : π.sectionOf p₁ (c.localState p₁) = .remainder := by
    rw [hloc₁]; exact π.init_remainder p₁
  let b₁ : MutexConfig P Reg Val State :=
    { c with localState := Function.update c.localState p₁ (π.enterTrying p₁ (c.localState p₁)) }
  have htr_b₁ : π.lts.Tr c (.enter p₁) b₁ := by
    simp only [MutexProtocol.lts, MutexProtocol.step?, hrem₁, ↓reduceIte, Option.some.injEq]
    rfl
  have hr_b₁ : π.Reachable b₁ := hr.step_tr htr_b₁
  have hb₁_loc₁ : c_enter₁.localState p₁ = b₁.localState p₁ := by
    dsimp only [c_enter₁, b₁, MutexProtocol.initConfig]
    rw [Function.update_self, Function.update_self, hloc₁]
  obtain ⟨_, hloc_c', hoth_c', hmtr_c'⟩ :=
    soloIter_replay π p₁ k₁ c_enter₁ b₁ hmem.symm hb₁_loc₁ htry₁
  refine ⟨soloIter π p₁ k₁ b₁, hr_b₁.mTr hmtr_c', ?_, ?_⟩
  · unfold MutexConfig.inCS at hcs₁ ⊢; rwa [← hloc_c']
  · calc (soloIter π p₁ k₁ b₁).localState p₀ = b₁.localState p₀ := hoth_c' p₀ hp_ne
      _ = c.localState p₀ := by dsimp only [b₁]; exact Function.update_of_ne hp_ne _ _

/-- Intermediate 1-register covering-write base step toward the `Fintype.card P ≤ Fintype.card Reg`
space lower bound of [BurnsLynch1993] (Theorem 5.1, p. 177; tracked in #7296): for
`2 ≤ Fintype.card P` processes and `Fintype.card Reg ≤ 1` atomic multi-writer read/write registers,
no deterministic asynchronous `MutexProtocol` satisfies `DeadlockFreeMutex` (`MutuallyExclusive` and
`DeadlockFree`).

Here `MutexProtocol` includes `.remainder`, `.trying`, `.cs`, and `.exit` (`MutexSection`), and
`MutexProtocol.DeadlockFree` asks for some process to reach `.cs` from an initially trying state
under `MutexProtocol.WeakFair` (scheduling `.trying` and `.exit`) and
`MutexProtocol.CSEventuallyExits`, whereas [BurnsLynch1993] (§§2–3, pp. 173–175) asks for a region
change in each nonnull fair history. The proof uses one poised blind write to erase the second
process's writes, specializing the indistinguishability and covering-write arguments of
[BurnsLynch1993], Lemmas 5.2 and 5.4 (pp. 177, 180). -/
theorem not_deadlockFreeMutex_of_single_register
    {P Reg Val State : Type*} [Fintype P] [Fintype Reg] [DecidableEq P] [DecidableEq Reg]
    (hP : 2 ≤ Fintype.card P) (hReg : Fintype.card Reg ≤ 1)
    (π : MutexProtocol P Reg Val State) :
    ¬ π.DeadlockFreeMutex := by
  rintro ⟨hme, hdf⟩
  have hP_lt : 1 < Fintype.card P := by omega
  obtain ⟨p₀, p₁, hp_ne⟩ := Fintype.exists_pair_of_one_lt_card hP_lt
  have : Subsingleton Reg := Fintype.card_le_one_iff_subsingleton.mp hReg
  let c_enter₀ : MutexConfig P Reg Val State :=
    { π.initConfig with
      localState := Function.update π.initConfig.localState p₀ (π.enterTrying p₀ (π.initLocal p₀)) }
  obtain ⟨hr_enter₀, k₀, hcs₀, htry₀, hoth₀⟩ := solo_enters_cs_from_init hdf p₀
  -- First show `p₀`'s solo entry must perform at least one shared-register write before `.cs`.
  have hex_write :
      ∃ j, j < k₀ ∧ (π.step p₀ ((soloIter π p₀ j c_enter₀).localState p₀)).isWrite = true := by
    by_contra hno_w
    have hnw_all : ∀ j < k₀,
        (π.step p₀ ((soloIter π p₀ j c_enter₀).localState p₀)).isWrite = false := by
      intro j hj
      exact Bool.eq_false_iff.mpr fun hw => hno_w ⟨j, hj, hw⟩
    let d₀ := soloIter π p₀ k₀ c_enter₀
    obtain ⟨_, _, _, hmtr_d₀⟩ := soloIter_replay π p₀ k₀ c_enter₀ c_enter₀ rfl rfl htry₀
    obtain ⟨d₂, hr_d₂, hcs_d₂_1, hp₀_eq⟩ := run_second_solo_into_cs hdf
      (hr_enter₀.mTr hmtr_d₀) hp_ne
      (soloIter_mem_of_no_write π p₀ k₀ c_enter₀ hnw_all)
      (hoth₀ p₁ hp_ne.symm)
    have hcs_d₂_0 : d₂.inCS π p₀ := by
      unfold MutexConfig.inCS at hcs₀ ⊢; rwa [hp₀_eq]
    exact hp_ne (hme d₂ hr_d₂ p₀ p₁ hcs_d₂_0 hcs_d₂_1)
  -- Pick the first write index `j < k₀` along `p₀`'s solo entry.
  let j := Nat.find hex_write
  obtain ⟨hj_lt, hj_write⟩ := Nat.find_spec hex_write
  have hnw_pre : ∀ i < j,
      (π.step p₀ ((soloIter π p₀ i c_enter₀).localState p₀)).isWrite = false := by
    intro i hi
    exact Bool.eq_false_iff.mpr fun hw =>
      Nat.find_min hex_write hi ⟨lt_trans hi hj_lt, hw⟩
  let c₀ := soloIter π p₀ j c_enter₀
  change (π.step p₀ (c₀.localState p₀)).isWrite = true at hj_write
  obtain ⟨_, _, hoth_c₀, hmtr_c₀⟩ :=
    soloIter_replay π p₀ j c_enter₀ c_enter₀ rfl rfl (fun i hi => htry₀ i (lt_trans hi hj_lt))
  have hc₀_p₁ : c₀.localState p₁ = π.initLocal p₁ := by
    calc c₀.localState p₁ = c_enter₀.localState p₁ := hoth_c₀ p₁ hp_ne.symm
      _ = π.initLocal p₁ := by
        dsimp only [c_enter₀, MutexProtocol.initConfig]
        exact Function.update_of_ne hp_ne.symm _ _
  -- While `p₀` pauses poised at `c₀`, run `p₁` solo into `.cs`.
  obtain ⟨c₁, hr_c₁, hc₁_cs₁, hc₁_p₀⟩ := run_second_solo_into_cs hdf
    (hr_enter₀.mTr hmtr_c₀) hp_ne
    (soloIter_mem_of_no_write π p₀ j c_enter₀ hnw_pre) hc₀_p₁
  -- Fire `p₀`'s poised write from `c₁`, covering `p₁`'s traces in the single register!
  have hc₁_try₀ : c₁.isTrying π p₀ := by
    have htry_c₀ := htry₀ j hj_lt
    unfold MutexConfig.isTrying at htry_c₀ ⊢
    rwa [hc₁_p₀]
  let c₂ := π.execRegStep c₁ p₀
  have htr_c₂ : π.lts.Tr c₁ (.step p₀) c₂ := by
    have hact : c₁.isActive π p₀ := Or.inl hc₁_try₀
    simp only [MutexProtocol.lts, MutexProtocol.step?, hact, ↓reduceIte]
    rfl
  have hr_c₂ : π.Reachable c₂ := hr_c₁.step_tr htr_c₂
  have hc₂_cs₁ : c₂.inCS π p₁ := by
    unfold MutexConfig.inCS at hc₁_cs₁ ⊢
    rwa [show c₂.localState p₁ = c₁.localState p₁ from execRegStep_other hp_ne.symm]
  let a₂ := soloIter π p₀ (j + 1) c_enter₀
  have ha₂_eq : a₂ = π.execRegStep c₀ p₀ := soloIter_succ_right π p₀ j c_enter₀
  have hcover : a₂.mem = c₂.mem ∧ a₂.localState p₀ = c₂.localState p₀ := by
    rw [ha₂_eq]
    dsimp only [c₂, MutexProtocol.execRegStep]
    rw [hc₁_p₀]
    cases hstep₀ : π.step p₀ (c₀.localState p₀) with
    | localStep _ => rw [hstep₀] at hj_write; cases hj_write
    | read _ _ => rw [hstep₀] at hj_write; cases hj_write
    | write r val next₀ =>
      refine ⟨funext fun r' => ?_, by simp⟩
      rcases Subsingleton.elim r' r with rfl
      simp
  -- Replay `p₀`'s remaining `k₀ - (j + 1)` solo steps into `.cs` while `p₁` stays in `.cs`!
  let rem := k₀ - (j + 1)
  have hrem_add : (j + 1) + rem = k₀ := Nat.add_sub_of_le (Nat.succ_le_of_lt hj_lt)
  have htry_rem : ∀ i < rem, (soloIter π p₀ i a₂).isTrying π p₀ := by
    intro i hi
    have hadd_eq : soloIter π p₀ i a₂ = soloIter π p₀ ((j + 1) + i) c_enter₀ :=
      (soloIter_add π p₀ (j + 1) i c_enter₀).symm
    rw [hadd_eq]
    exact htry₀ ((j + 1) + i) (by omega)
  obtain ⟨_, hloc_c₃_0, hoth_c₃, hmtr_c₃⟩ :=
    soloIter_replay π p₀ rem a₂ c₂ hcover.1 hcover.2 htry_rem
  let c₃ := soloIter π p₀ rem c₂
  have hr_c₃ : π.Reachable c₃ := hr_c₂.mTr hmtr_c₃
  have hc₃_cs₀ : c₃.inCS π p₀ := by
    have ha₃_eq : soloIter π p₀ rem a₂ = soloIter π p₀ k₀ c_enter₀ := by
      rw [← soloIter_add π p₀ (j + 1) rem c_enter₀, hrem_add]
    unfold MutexConfig.inCS at hcs₀ ⊢
    rw [← hloc_c₃_0, ha₃_eq]
    exact hcs₀
  have hc₃_cs₁ : c₃.inCS π p₁ := by
    unfold MutexConfig.inCS at hc₂_cs₁ ⊢
    rwa [hoth_c₃ p₁ hp_ne.symm]
  exact hp_ne (hme c₃ hr_c₃ p₀ p₁ hc₃_cs₀ hc₃_cs₁)

end SingleRegisterImpossibility

end Cslib.Distributed.MutualExclusion
