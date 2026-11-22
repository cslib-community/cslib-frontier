/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.Basic
import Mathlib.Data.Fintype.Pigeonhole

/-!
# The Non-Blocking Progress Hierarchy: Wait-Freedom, Lock-Freedom, and Obstruction-Freedom

This module formalizes the three classical non-blocking progress conditions for asynchronous
shared-memory concurrent object implementations over processes `P` ([Herlihy1991], §§2.2–2.3,
pp. 128–129; [HerlihyLuchangcoMoir2003], §1, pp. 1–2; [MoirShavit2007], §1.1.3, pp. 1-5–1-6):

* **Wait-freedom** (`ProgressSystem.IsWaitFree`): in every infinite execution starting from a
  reachable state, any process `p` with a pending operation that takes infinitely many
  implementation steps eventually completes an operation.
* **Lock-freedom** (`ProgressSystem.IsLockFree`): in every infinite execution starting from a
  reachable state in which infinitely many implementation steps are taken, infinitely many
  operations complete.
* **Obstruction-freedom** (`ProgressSystem.IsObstructionFree`): from every reachable state, any
  process `p` with a pending operation completes within finitely many steps when scheduled in
  isolation (`soloIter`).

Unlike `Cslib.Distributed.SharedMemory.Protocol` (which models one-shot consensus where each
process decides once and halts), `ProgressSystem` separates relational new-operation invocations by
idle processes (`Invoke`) from a **deterministic, always-enabled** per-process implementation step
(`step : State → P → State × Bool`), capturing long-lived concurrent objects where fast processes
may repeatedly invoke and complete new operations while a slow process retries. Because active
implementation steps cannot be passively disabled, passive conditional or lock waiting is modeled as
spin-waiting (`.exec p false`): consequently, [Herlihy1991] §2.3 (p. 129)'s non-blocking Condition
(2) follows from Condition (1) via `IsWaitFree.isObstructionFree`, and `IsObstructionFree` inspects
the unique solo trajectory `soloIter` rather than quantifying over nondeterministic solo runs.

## Main definitions

* `Cslib.Distributed.ConcurrentObjects.StepLabel`: transition label (`invoke` or `exec`).
* `Cslib.Distributed.ConcurrentObjects.ProgressSystem`: asynchronous concurrent-object transition
  system with relational invocations and deterministic per-process implementation steps over
  `Cslib.LTS`.
* `Cslib.Distributed.ConcurrentObjects.ProgressSystem.IsWaitFree`,
  `Cslib.Distributed.ConcurrentObjects.ProgressSystem.IsLockFree`,
  `Cslib.Distributed.ConcurrentObjects.ProgressSystem.IsObstructionFree`: the three non-blocking
  progress properties.
* `Cslib.Distributed.ConcurrentObjects.atomicIncSystem`: single-step atomic increment witness.
* `Cslib.Distributed.ConcurrentObjects.casCounterSystem`: original two-step `CAS`
  fetch-and-increment counter model illustrating `CAS`-loop starvation ([MoirShavit2007], §1.1.3,
  p. 1-6).
* `Cslib.Distributed.ConcurrentObjects.racingClaimSystem`: original minimal two-step shared-register
  claim-and-verify model isolating two-thread contention livelock ([HerlihyLuchangcoMoir2003], §1,
  pp. 1–2).

## Main results

* `Cslib.Distributed.ConcurrentObjects.ProgressSystem.IsWaitFree.isLockFree`: in a deterministic
  `ProgressSystem` over `[Finite P]`, wait-freedom implies lock-freedom (after [MoirShavit2007],
  §1.1.3, p. 1-5).
* `Cslib.Distributed.ConcurrentObjects.ProgressSystem.IsLockFree.isObstructionFree`,
  `Cslib.Distributed.ConcurrentObjects.ProgressSystem.IsWaitFree.isObstructionFree`: in a
  deterministic `ProgressSystem`, lock-freedom and wait-freedom imply obstruction-freedom (for
  arbitrary `P`, without finiteness).
* `Cslib.Distributed.ConcurrentObjects.ProgressSystem.isLockFree_of_bounded_shared_changes`:
  original reusable lock-freedom criterion for optimistic `CAS` implementations (shared by
  `casCounterSystem` and `TreiberStack`).
* `Cslib.Distributed.ConcurrentObjects.casCounterSystem_isLockFree`,
  `Cslib.Distributed.ConcurrentObjects.casCounterSystem_not_isWaitFree`,
  `Cslib.Distributed.ConcurrentObjects.exists_lockFree_not_waitFree`: concrete strict separation of
  lock-freedom from wait-freedom.
* `Cslib.Distributed.ConcurrentObjects.racingClaimSystem_isObstructionFree`,
  `Cslib.Distributed.ConcurrentObjects.racingClaimSystem_not_isLockFree`,
  `Cslib.Distributed.ConcurrentObjects.exists_obstructionFree_not_lockFree`: concrete strict
  separation of obstruction-freedom from lock-freedom.

## References

* [M. Herlihy, *Wait-Free Synchronization*][Herlihy1991]
* [M. Herlihy, V. Luchangco, M. Moir, *Obstruction-Free Synchronization: Double-Ended Queues as an
  Example*][HerlihyLuchangcoMoir2003]
* [M. Moir, N. Shavit, *Concurrent Data Structures*][MoirShavit2007]
-/

public section

namespace Cslib.Distributed.ConcurrentObjects

open Cslib

/-- Label of an asynchronous step in a `ProgressSystem`: either an idle process `proc` invoking a
new operation, or an active process `proc` executing one implementation step (which finishes its
pending operation iff `completed = true`). -/
inductive StepLabel (P : Type*) where
  /-- Idle process `proc` begins a new pending operation. -/
  | invoke (proc : P)
  /-- Active process `proc` executes one implementation step; `completed = true` iff its pending
  operation finishes on this step. -/
  | exec (proc : P) (completed : Bool)
  deriving @[expose] DecidableEq

namespace StepLabel

variable {P : Type*}

/-- Process taking the step. -/
@[expose]
def proc : StepLabel P → P
  | .invoke p => p
  | .exec p _ => p

/-- Whether the step is an implementation step (rather than a new invocation). -/
@[expose]
def isExec : StepLabel P → Bool
  | .invoke _ => false
  | .exec _ _ => true

/-- Whether the step completes a pending operation. -/
@[expose]
def isCompleted : StepLabel P → Bool
  | .invoke _ => false
  | .exec _ done => done

@[simp]
theorem proc_invoke (p : P) : (invoke p).proc = p :=
  rfl

@[simp]
theorem proc_exec (p : P) (done : Bool) : (exec p done).proc = p :=
  rfl

@[simp]
theorem isExec_invoke (p : P) : (invoke p).isExec = false :=
  rfl

@[simp]
theorem isExec_exec (p : P) (done : Bool) : (exec p done).isExec = true :=
  rfl

@[simp]
theorem isCompleted_invoke (p : P) : (invoke p).isCompleted = false :=
  rfl

@[simp]
theorem isCompleted_exec (p : P) (done : Bool) : (exec p done).isCompleted = done :=
  rfl

theorem isExec_of_isCompleted {lbl : StepLabel P} (h : lbl.isCompleted = true) :
    lbl.isExec = true := by
  cases lbl with
  | invoke _ => exact Bool.noConfusion h
  | exec _ _ => rfl

end StepLabel

universe u

/-- Operational transition system of a concurrent shared-memory object implementation over
processes `P` with per-process pending operations ([Herlihy1991], §§2.2–2.3, pp. 128–129;
[HerlihyLuchangcoMoir2003], §1, pp. 1–2; [MoirShavit2007], §1.1.3, pp. 1-5–1-6). Invocations
`Invoke` are relational, whereas `step : State → P → State × Bool` is deterministic and always
enabled whenever `Active s p` holds (modeling passive lock or conditional waiting via non-completing
spin steps `.exec p false`, so each active process has a unique `soloIter` trajectory). -/
structure ProgressSystem (P : Type u) where
  /-- Global configuration (shared memory together with per-process local execution phases). -/
  State : Type u
  /-- Initial global configuration. -/
  init : State
  /-- `Active s p` holds when process `p` has an uncompleted pending operation in state `s`. -/
  Active : State → P → Prop
  /-- `Invoke s p s'` transitions idle process `p` into a new pending operation in state `s'`. -/
  Invoke : State → P → State → Prop
  /-- `step s p = (s', done)` executes one implementation step of active process `p`, returning
  the successor state `s'` and whether `p`'s pending operation completed (`done = true`). -/
  step : State → P → State × Bool
  /-- Only an idle process may invoke a new operation. -/
  invoke_only_idle : ∀ {s p s'}, Invoke s p s' → ¬ Active s p
  /-- Invoking an operation makes `p` active. -/
  active_after_invoke : ∀ {s p s'}, Invoke s p s' → Active s' p
  /-- An invocation by `p` does not change whether any other process `q ≠ p` is active. -/
  invoke_frame_active : ∀ {s p q s'}, Invoke s p s' → q ≠ p → (Active s' q ↔ Active s q)
  /-- A non-completing step (`done = false`) keeps `p` active. -/
  active_after_step_false : ∀ {s p}, Active s p → (step s p).2 = false → Active (step s p).1 p
  /-- A completing step (`done = true`) returns `p` to idle. -/
  idle_after_step_true : ∀ {s p}, Active s p → (step s p).2 = true → ¬ Active (step s p).1 p
  /-- An implementation step by `p` does not change whether any other process `q ≠ p` is active. -/
  step_frame_active : ∀ {s p q}, Active s p → q ≠ p → (Active (step s p).1 q ↔ Active s q)

namespace ProgressSystem

variable {P : Type*}

/-- Labelled transition system of a `ProgressSystem`. -/
@[expose]
def lts (sys : ProgressSystem P) : LTS sys.State (StepLabel P) where
  Tr s lbl s' :=
    match lbl with
    | .invoke p => sys.Invoke s p s'
    | .exec p done => sys.Active s p ∧ sys.step s p = (s', done)

/-- State `s` is reachable from `sys.init` via a finite sequence of invocations and implementation
steps. -/
@[expose]
def Reachable (sys : ProgressSystem P) (s : sys.State) : Prop :=
  sys.lts.CanReach sys.init s

theorem Reachable.init (sys : ProgressSystem P) : sys.Reachable sys.init :=
  LTS.CanReach.refl sys.lts sys.init

theorem Reachable.step {sys : ProgressSystem P} {s s' : sys.State} {lbl : StepLabel P}
    (hs : sys.Reachable s) (htr : sys.lts.Tr s lbl s') : sys.Reachable s' := by
  obtain ⟨μs, hmtr⟩ := hs
  exact ⟨μs ++ [lbl], (LTS.MTr.append_iff sys.lts).mpr ⟨s, hmtr, LTS.MTr.single sys.lts htr⟩⟩

theorem Reachable.induction {sys : ProgressSystem P} {motive : sys.State → Prop}
    (hinit : motive sys.init)
    (hstep : ∀ {s lbl s'}, sys.Reachable s → sys.lts.Tr s lbl s' → motive s → motive s')
    {s : sys.State} (hs : sys.Reachable s) : motive s := by
  obtain ⟨μs, hmtr⟩ := hs
  have hinv : sys.lts.TrInv (fun u => sys.Reachable u ∧ motive u) :=
    fun _ _ _ htr ⟨hr, hm⟩ => ⟨hr.step htr, hstep hr htr hm⟩
  exact (LTS.mtrInv_of_trInv hinv sys.init μs s hmtr ⟨Reachable.init sys, hinit⟩).2

/-- An infinite execution of `sys` starting from a reachable state `states 0`. -/
structure InfiniteExec (sys : ProgressSystem P) where
  /-- Sequence of global states visited along the execution. -/
  states : ℕ → sys.State
  /-- Sequence of transition labels taken along the execution. -/
  labels : ℕ → StepLabel P
  /-- The starting state `states 0` is reachable from `sys.init`. -/
  reachable_zero : sys.Reachable (states 0)
  /-- Every index `n` is a valid transition `Tr (states n) (labels n) (states (n + 1))`. -/
  valid : ∀ n, sys.lts.Tr (states n) (labels n) (states (n + 1))

theorem InfiniteExec.reachable {sys : ProgressSystem P} (exec : sys.InfiniteExec) :
    ∀ n, sys.Reachable (exec.states n)
  | 0 => exec.reachable_zero
  | n + 1 => (exec.reachable n).step (exec.valid n)

/-- State reached after `k` solo implementation steps of process `p` starting from `s`. -/
@[expose]
def soloIter (sys : ProgressSystem P) (s : sys.State) (p : P) : ℕ → sys.State
  | 0 => s
  | k + 1 => (sys.step (sys.soloIter s p k) p).1

@[simp]
theorem soloIter_zero (sys : ProgressSystem P) (s : sys.State) (p : P) :
    sys.soloIter s p 0 = s :=
  rfl

@[simp]
theorem soloIter_succ (sys : ProgressSystem P) (s : sys.State) (p : P) (k : ℕ) :
    sys.soloIter s p (k + 1) = (sys.step (sys.soloIter s p k) p).1 :=
  rfl

/-- **Wait-freedom** ([Herlihy1991], §2.3, p. 129; [MoirShavit2007], §1.1.3, p. 1-5): in every
infinite execution from a reachable state, if process `p` has a pending operation at index `t₀` and
takes infinitely many implementation steps at or after `t₀`, then `p` completes its pending
operation at some index `n ≥ t₀`. -/
@[expose]
def IsWaitFree (sys : ProgressSystem P) : Prop :=
  ∀ (exec : sys.InfiniteExec) (p : P) (t₀ : ℕ),
    sys.Active (exec.states t₀) p →
    (∀ M ≥ t₀, ∃ n ≥ M, (exec.labels n).isExec = true ∧ (exec.labels n).proc = p) →
    ∃ n ≥ t₀, exec.labels n = .exec p true

/-- **Lock-freedom** ([HerlihyLuchangcoMoir2003], §1, p. 1; [MoirShavit2007], §1.1.3, p. 1-5): in
every infinite execution from a reachable state in which infinitely many implementation steps are
taken, infinitely many operations complete. -/
@[expose]
def IsLockFree (sys : ProgressSystem P) : Prop :=
  ∀ exec : sys.InfiniteExec,
    (∀ M, ∃ n ≥ M, (exec.labels n).isExec = true) →
    ∀ M, ∃ n ≥ M, (exec.labels n).isCompleted = true

/-- **Obstruction-freedom** ([HerlihyLuchangcoMoir2003], §1, p. 1; [MoirShavit2007], §1.1.3,
p. 1-5): from every reachable state `s`, any active process `p` completes its pending operation
within finitely many steps when scheduled in isolation. -/
@[expose]
def IsObstructionFree (sys : ProgressSystem P) : Prop :=
  ∀ ⦃s : sys.State⦄, sys.Reachable s → ∀ p : P, sys.Active s p →
    ∃ k : ℕ, (sys.step (sys.soloIter s p k) p).2 = true

/-! ### Preservation of active status without completions and finite-process properties -/

/-- If no operation completes in `[n₁, n₂)`, any process active at `n₁` remains active at `n₂`. -/
theorem InfiniteExec.active_of_no_completion {sys : ProgressSystem P} (exec : sys.InfiniteExec)
    {p : P} {n₁ n₂ : ℕ} (hle : n₁ ≤ n₂) (hact : sys.Active (exec.states n₁) p)
    (hno : ∀ m, n₁ ≤ m → m < n₂ → (exec.labels m).isCompleted = false) :
    sys.Active (exec.states n₂) p := by
  induction n₂ with
  | zero =>
    have : n₁ = 0 := by omega
    subst this
    exact hact
  | succ m ih =>
    by_cases hlt : n₁ ≤ m
    · have hm_act := ih hlt (fun j hj₁ hj₂ => hno j hj₁ (by omega))
      have htr := exec.valid m
      have hnc := hno m hlt (Nat.lt_succ_self m)
      cases hlbl : exec.labels m with
      | invoke q =>
        rw [hlbl] at htr
        have hqp : p ≠ q := fun h => by
          subst h
          exact sys.invoke_only_idle htr hm_act
        exact (sys.invoke_frame_active htr hqp).mpr hm_act
      | exec q done =>
        rw [hlbl] at htr hnc
        simp only [StepLabel.isCompleted_exec] at hnc
        subst hnc
        obtain ⟨hq_act, hstep⟩ := htr
        by_cases hqp : p = q
        · subst hqp
          have h1 : (sys.step (exec.states m) p).1 = exec.states (m + 1) :=
            congrArg Prod.fst hstep
          have h2 : (sys.step (exec.states m) p).2 = false :=
            congrArg Prod.snd hstep
          rw [← h1]
          exact sys.active_after_step_false hm_act h2
        · have h1 : (sys.step (exec.states m) q).1 = exec.states (m + 1) :=
            congrArg Prod.fst hstep
          rw [← h1]
          exact (sys.step_frame_active hq_act hqp).mpr hm_act
    · have : n₁ = m + 1 := by omega
      subst this
      exact hact

/-- Without completions in `[N, ∞)`, no process can invoke more than once at or after `N`. -/
theorem InfiniteExec.invoke_injective_of_no_completion {sys : ProgressSystem P}
    (exec : sys.InfiniteExec) {N n₁ n₂ : ℕ} {p₁ p₂ : P}
    (hno : ∀ m ≥ N, (exec.labels m).isCompleted = false)
    (hN : N ≤ n₁) (hlt : n₁ < n₂)
    (hl₁ : exec.labels n₁ = .invoke p₁) (hl₂ : exec.labels n₂ = .invoke p₂) :
    p₁ ≠ p₂ := by
  intro hp
  subst hp
  have htr₁ := exec.valid n₁
  rw [hl₁] at htr₁
  have hact₁ : sys.Active (exec.states (n₁ + 1)) p₁ := sys.active_after_invoke htr₁
  have hact₂ : sys.Active (exec.states n₂) p₁ :=
    exec.active_of_no_completion (by omega) hact₁ (fun m hm _ => hno m (by omega))
  have htr₂ := exec.valid n₂
  rw [hl₂] at htr₂
  exact sys.invoke_only_idle htr₂ hact₂

private noncomputable def chooseGeSeq {P : ℕ → Prop} (hex : ∀ M, ∃ n ≥ M, P n) : ℕ → ℕ
  | 0 => Classical.choose (hex 0)
  | k + 1 => Classical.choose (hex (chooseGeSeq hex k + 1))

private theorem chooseGeSeq_spec {P : ℕ → Prop} (hex : ∀ M, ∃ n ≥ M, P n) :
    (∀ k, P (chooseGeSeq hex k)) ∧ ∀ k₁ k₂, k₁ < k₂ → chooseGeSeq hex k₁ < chooseGeSeq hex k₂ := by
  have hP : ∀ k, P (chooseGeSeq hex k) := by
    intro k
    cases k with
    | zero => exact (Classical.choose_spec (hex 0)).2
    | succ k' => exact (Classical.choose_spec (hex (chooseGeSeq hex k' + 1))).2
  have hstep : ∀ k, chooseGeSeq hex k < chooseGeSeq hex (k + 1) := by
    intro k
    have hge := (Classical.choose_spec (hex (chooseGeSeq hex k + 1))).1
    simp only [chooseGeSeq]
    omega
  refine ⟨hP, fun k₁ k₂ hlt => ?_⟩
  induction k₂ with
  | zero => omega
  | succ m ih =>
    by_cases hkm : k₁ < m
    · exact Nat.lt_trans (ih hkm) (hstep m)
    · have : k₁ = m := by omega
      subst this
      exact hstep k₁

/-- Over finitely many processes `[Finite P]`, if no operation completes at or after `N`, then
eventually every transition is an implementation step (`.exec`). -/
theorem InfiniteExec.eventually_isExec_of_no_completion [Finite P] {sys : ProgressSystem P}
    (exec : sys.InfiniteExec) {N : ℕ} (hno : ∀ m ≥ N, (exec.labels m).isCompleted = false) :
    ∃ N₁ ≥ N, ∀ n ≥ N₁, (exec.labels n).isExec = true := by
  by_contra hnot
  have hex : ∀ M, ∃ n ≥ M, N ≤ n ∧ (exec.labels n).isExec = false := by
    intro M
    by_contra hnone
    apply hnot
    refine ⟨max N M, Nat.le_max_left N M, fun n hn => ?_⟩
    cases hb : (exec.labels n).isExec
    · exfalso
      exact hnone ⟨n, by omega, by omega, hb⟩
    · rfl
  let idx := chooseGeSeq hex
  obtain ⟨hspec, hmono⟩ := chooseGeSeq_spec hex
  have hinv : ∀ k, exec.labels (idx k) = .invoke (exec.labels (idx k)).proc := by
    intro k
    have hf := (hspec k).2
    cases hlbl : exec.labels (idx k) with
    | invoke _ => rfl
    | exec _ _ =>
      rw [hlbl, StepLabel.isExec_exec] at hf
      exact Bool.noConfusion hf
  obtain ⟨k₁, k₂, hkne, hpeq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k => (exec.labels (idx k)).proc)
  rcases Nat.lt_or_gt_of_ne hkne with h₁₂ | h₂₁
  · exact exec.invoke_injective_of_no_completion hno (hspec k₁).1 (hmono k₁ k₂ h₁₂)
      (hinv k₁) (hinv k₂) hpeq
  · exact exec.invoke_injective_of_no_completion hno (hspec k₂).1 (hmono k₂ k₁ h₂₁)
      (hinv k₂) (hinv k₁) hpeq.symm

/-- Over finitely many processes `[Finite P]`, every infinite execution takes infinitely many
implementation steps (`.exec`). -/
theorem InfiniteExec.infinitely_many_isExec [Finite P] {sys : ProgressSystem P}
    (exec : sys.InfiniteExec) (M : ℕ) :
    ∃ n ≥ M, (exec.labels n).isExec = true := by
  by_cases hcomp : ∃ n ≥ M, (exec.labels n).isCompleted = true
  · obtain ⟨n, hn, hc⟩ := hcomp
    exact ⟨n, hn, StepLabel.isExec_of_isCompleted hc⟩
  · have hno : ∀ n ≥ M, (exec.labels n).isCompleted = false := by
      intro n hn
      cases hb : (exec.labels n).isCompleted
      · rfl
      · exfalso; exact hcomp ⟨n, hn, hb⟩
    obtain ⟨N₁, hN₁, hall⟩ := exec.eventually_isExec_of_no_completion hno
    exact ⟨N₁, hN₁, hall N₁ (Nat.le_refl N₁)⟩

/-! ### The Non-Blocking Progress Hierarchy (`IsWaitFree → IsLockFree → IsObstructionFree`) -/

/-- In a deterministic `ProgressSystem` over finitely many processes (`[Finite P]`), wait-freedom
implies lock-freedom (after [MoirShavit2007], §1.1.3, p. 1-5): in any infinite execution taking
infinitely many implementation steps, some process steps infinitely often by infinite pigeonhole
(`Finite.exists_infinite_fiber`) and therefore completes infinitely often. -/
theorem IsWaitFree.isLockFree [Finite P] {sys : ProgressSystem P} (hwf : sys.IsWaitFree) :
    sys.IsLockFree := by
  intro exec hexec M
  by_contra hnone
  have hno : ∀ n ≥ M, (exec.labels n).isCompleted = false := by
    intro n hn
    cases hb : (exec.labels n).isCompleted
    · rfl
    · exfalso; exact hnone ⟨n, hn, hb⟩
  have hex : ∀ K, ∃ n ≥ K, M ≤ n ∧ (exec.labels n).isExec = true := by
    intro K
    obtain ⟨n, hn, he⟩ := hexec (max M K)
    exact ⟨n, by omega, by omega, he⟩
  let idx := chooseGeSeq hex
  obtain ⟨hspec, hmono⟩ := chooseGeSeq_spec hex
  have idx_ge : ∀ k, k ≤ idx k := by
    intro k
    induction k with
    | zero => omega
    | succ k' ih =>
      have hlt : idx k' < idx (k' + 1) := hmono k' (k' + 1) (Nat.lt_succ_self k')
      omega
  let procOf : ℕ → P := fun k => (exec.labels (idx k)).proc
  obtain ⟨p, hinf_fiber⟩ := Finite.exists_infinite_fiber procOf
  have hp_unbdd : ∀ K, ∃ k ≥ K, procOf k = p := by
    intro K
    by_contra hbdd
    have hlt_K : ∀ x : procOf ⁻¹' {p}, x.1 < K := by
      intro x
      by_contra hge
      exact hbdd ⟨x.1, by omega, x.2⟩
    let toFin : procOf ⁻¹' {p} → Fin K := fun x => ⟨x.1, hlt_K x⟩
    obtain ⟨x₁, x₂, hxne, hfeq⟩ := Finite.exists_ne_map_eq_of_infinite toFin
    exact hxne (Subtype.ext (Fin.mk.inj hfeq))
  obtain ⟨k₀, _, hk₀_p⟩ := hp_unbdd 0
  let t₀ := idx k₀
  have ht₀_M : M ≤ t₀ := (hspec k₀).1
  have ht₀_act : sys.Active (exec.states t₀) p := by
    have htr := exec.valid t₀
    have he := (hspec k₀).2
    cases hlbl : exec.labels t₀ with
    | invoke _ =>
      rw [hlbl, StepLabel.isExec_invoke] at he
      exact Bool.noConfusion he
    | exec q done =>
      rw [hlbl] at htr
      have hqp : q = p := by
        simpa only [procOf, t₀, hlbl, StepLabel.proc_exec] using hk₀_p
      subst hqp
      exact htr.1
  have hp_inf : ∀ K ≥ t₀, ∃ n ≥ K, (exec.labels n).isExec = true ∧ (exec.labels n).proc = p := by
    intro K _
    obtain ⟨k, hk, hkp⟩ := hp_unbdd K
    refine ⟨idx k, Nat.le_trans hk (idx_ge k), (hspec k).2, hkp⟩
  obtain ⟨n, hn, hdone⟩ := hwf exec p t₀ ht₀_act hp_inf
  have hc : (exec.labels n).isCompleted = true := by
    rw [hdone]; rfl
  have hnc := hno n (by omega)
  rw [hc] at hnc
  exact Bool.noConfusion hnc

private def nonCompletingSoloExec {sys : ProgressSystem P} {s : sys.State} {p : P}
    (hs : sys.Reachable s) (hact : sys.Active s p)
    (hnever : ¬ ∃ k : ℕ, (sys.step (sys.soloIter s p k) p).2 = true) : sys.InfiniteExec :=
  have hfalse : ∀ k, (sys.step (sys.soloIter s p k) p).2 = false := fun k => by
    cases hb : (sys.step (sys.soloIter s p k) p).2
    · rfl
    · exact False.elim (hnever ⟨k, hb⟩)
  have hact_all : ∀ k, sys.Active (sys.soloIter s p k) p := fun k => by
    induction k with
    | zero => exact hact
    | succ k' ih => exact sys.active_after_step_false ih (hfalse k')
  { states := sys.soloIter s p
    labels := fun _ => .exec p false
    reachable_zero := hs
    valid := fun k => ⟨hact_all k, Prod.ext rfl (hfalse k)⟩ }

/-- In a deterministic `ProgressSystem`, lock-freedom implies obstruction-freedom (after
[HerlihyLuchangcoMoir2003], §1, p. 1; [MoirShavit2007], §1.1.3, p. 1-5): if an active process `p`
failed to complete in every finite prefix of its solo trajectory `soloIter` from a reachable state
`s`, scheduling `p` forever in isolation would yield a valid infinite execution with zero
completions. -/
theorem IsLockFree.isObstructionFree {sys : ProgressSystem P} (hlf : sys.IsLockFree) :
    sys.IsObstructionFree := by
  intro s hs p hact
  by_contra hnever
  obtain ⟨n, _, hc⟩ :=
    hlf (nonCompletingSoloExec hs hact hnever) (fun M => ⟨M, Nat.le_refl M, rfl⟩) 0
  exact Bool.noConfusion hc

/-- In a deterministic `ProgressSystem` over arbitrary `P` (including infinite process sets,
without `[Finite P]`), wait-freedom implies obstruction-freedom (after [Herlihy1991], §2.3, p. 129;
[MoirShavit2007], §1.1.3, p. 1-5): scheduling an active process `p` along its always-enabled solo
trajectory `soloIter` gives `p` infinitely many implementation steps, so `IsWaitFree` forces `p` to
complete at some step `n`. -/
theorem IsWaitFree.isObstructionFree {sys : ProgressSystem P} (hwf : sys.IsWaitFree) :
    sys.IsObstructionFree := by
  intro s hs p hact
  by_contra hnever
  obtain ⟨n, _, hc⟩ :=
    hwf (nonCompletingSoloExec hs hact hnever) p 0 hact
      (fun M _ => ⟨M, Nat.le_refl M, rfl, rfl⟩)
  dsimp only [nonCompletingSoloExec] at hc
  nomatch hc

/-! ### Reusable bounded-shared-change engine for lock-free `CAS` implementations -/

/-- **Bounded-shared-change lock-freedom criterion**: in an optimistic `CAS`-based implementation
over `[Finite P]`, suppose:
1. Every non-completing step of `p` that modifies the shared projection `shared` places `p` into a
   `Committed` state (`committed_of_shared_ne`), `Committed` is preserved by other processes'
   non-completing steps (`committed_frame`), and any step by an already-`Committed` process
   immediately completes (`complete_of_committed`); hence `shared` can change at most `|P|` times
   without an operation completing.
2. Whenever `shared` is unchanged across a non-completing step of `p`, a natural-number measure
   `rank s p` strictly decreases for `p` (`rank_lt_of_shared_eq`) and does not increase for any
   `q ≠ p` (`rank_le_of_shared_eq_ne`).

Then `sys` is lock-free (`sys.IsLockFree`). Both `casCounterSystem` and `treiberFreshNodeSystem`
instantiate this criterion directly. -/
theorem isLockFree_of_bounded_shared_changes [Finite P] {sys : ProgressSystem P} {α : Type*}
    (shared : sys.State → α)
    (Committed : sys.State → P → Prop)
    (rank : sys.State → P → ℕ)
    (committed_of_shared_ne : ∀ {s p}, sys.Active s p → (sys.step s p).2 = false →
      shared (sys.step s p).1 ≠ shared s → Committed (sys.step s p).1 p)
    (committed_frame : ∀ {s p q}, sys.Active s p → (sys.step s p).2 = false → q ≠ p →
      Committed s q → Committed (sys.step s p).1 q)
    (complete_of_committed : ∀ {s p}, sys.Active s p → Committed s p → (sys.step s p).2 = true)
    (rank_lt_of_shared_eq : ∀ {s p}, sys.Active s p → (sys.step s p).2 = false →
      shared (sys.step s p).1 = shared s → rank (sys.step s p).1 p < rank s p)
    (rank_le_of_shared_eq_ne : ∀ {s p q}, sys.Active s p → (sys.step s p).2 = false →
      shared (sys.step s p).1 = shared s → q ≠ p → rank (sys.step s p).1 q ≤ rank s q) :
    sys.IsLockFree := by
  intro exec _ M
  by_contra hnone
  have hno : ∀ n ≥ M, (exec.labels n).isCompleted = false := by
    intro n hn
    cases hb : (exec.labels n).isCompleted
    · rfl
    · exfalso; exact hnone ⟨n, hn, hb⟩
  -- Step 1: Beyond `N₁ ≥ M`, all transitions are non-completing `.exec p false` steps.
  obtain ⟨N₁, hN₁_M, honly_exec⟩ := exec.eventually_isExec_of_no_completion hno
  have hstep_at : ∀ n ≥ N₁, ∃ p, exec.labels n = .exec p false ∧
      sys.Active (exec.states n) p ∧
      sys.step (exec.states n) p = (exec.states (n + 1), false) := by
    intro n hn
    have he := honly_exec n hn
    have hc := hno n (by omega)
    have htr := exec.valid n
    cases hlbl : exec.labels n with
    | invoke _ =>
      rw [hlbl, StepLabel.isExec_invoke] at he
      exact Bool.noConfusion he
    | exec p done =>
      rw [hlbl] at hc htr
      simp only [StepLabel.isCompleted_exec] at hc
      subst hc
      exact ⟨p, rfl, htr.1, htr.2⟩
  -- Step 2: `Committed` persists across all steps `≥ N₁` (because a `Committed` thread cannot step
  -- without producing `done = true`!).
  have hcomm_persist : ∀ {n₁ n₂ p}, N₁ ≤ n₁ → n₁ ≤ n₂ →
      Committed (exec.states n₁) p → Committed (exec.states n₂) p := by
    intro n₁ n₂ p hN₁ hle hcomm
    induction n₂ with
    | zero =>
      have : n₁ = 0 := by omega
      subst this; exact hcomm
    | succ m ih =>
      by_cases hlt : n₁ ≤ m
      · have hm_c := ih hlt
        obtain ⟨q, _, hq_act, hq_step⟩ := hstep_at m (by omega)
        have hq1 : (sys.step (exec.states m) q).1 = exec.states (m + 1) := congrArg Prod.fst hq_step
        have hq2 : (sys.step (exec.states m) q).2 = false := congrArg Prod.snd hq_step
        have hpq : p ≠ q := fun h => by
          subst h
          have htrue := complete_of_committed hq_act hm_c
          rw [htrue] at hq2
          exact Bool.noConfusion hq2
        rw [← hq1]
        exact committed_frame hq_act hq2 hpq hm_c
      · have : n₁ = m + 1 := by omega
        subst this; exact hcomm
  -- Step 3: Consequently, `shared` changes at most once per process after `N₁`, hence freezes
  -- permanently from some `N₂ ≥ N₁` onwards!
  have hshared_freeze : ∃ N₂ ≥ N₁, ∀ n ≥ N₂,
      shared (exec.states (n + 1)) = shared (exec.states n) := by
    by_contra hnot_fr
    have hex_chg : ∀ K, ∃ n ≥ K, N₁ ≤ n ∧
        shared (exec.states (n + 1)) ≠ shared (exec.states n) := by
      intro K
      by_contra hno_chg
      apply hnot_fr
      refine ⟨max N₁ K, Nat.le_max_left N₁ K, fun n hn => ?_⟩
      by_contra hne
      exact hno_chg ⟨n, by omega, by omega, hne⟩
    let idx := chooseGeSeq hex_chg
    obtain ⟨hspec, hmono⟩ := chooseGeSeq_spec hex_chg
    obtain ⟨k₁, k₂, hkne, hpeq⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun k => (exec.labels (idx k)).proc)
    have hconflict : ∀ u v, u < v →
        (exec.labels (idx u)).proc ≠ (exec.labels (idx v)).proc := by
      intro u v huv hpuv
      have hu_N₁ : N₁ ≤ idx u := (hspec u).1
      have huv_idx : idx u < idx v := hmono u v huv
      obtain ⟨pu, hlu, hact_u, hstep_u⟩ := hstep_at (idx u) hu_N₁
      obtain ⟨pv, hlv, hact_v, hstep_v⟩ := hstep_at (idx v) (by omega)
      have hpu_eq : pu = pv := by
        simpa only [hlu, hlv, StepLabel.proc_exec] using hpuv
      subst hpu_eq
      have hu1 : (sys.step (exec.states (idx u)) pu).1 = exec.states (idx u + 1) :=
        congrArg Prod.fst hstep_u
      have hu2 : (sys.step (exec.states (idx u)) pu).2 = false :=
        congrArg Prod.snd hstep_u
      have hchg_u : shared (sys.step (exec.states (idx u)) pu).1 ≠
          shared (exec.states (idx u)) := by
        rw [hu1]; exact (hspec u).2
      have hcomm_u : Committed (exec.states (idx u + 1)) pu := by
        rw [← hu1]; exact committed_of_shared_ne hact_u hu2 hchg_u
      have hcomm_v : Committed (exec.states (idx v)) pu :=
        hcomm_persist (by omega) (by omega) hcomm_u
      have htrue := complete_of_committed hact_v hcomm_v
      have hv2 : (sys.step (exec.states (idx v)) pu).2 = false := congrArg Prod.snd hstep_v
      rw [htrue] at hv2
      exact Bool.noConfusion hv2
    rcases Nat.lt_or_gt_of_ne hkne with h₁₂ | h₂₁
    · exact hconflict k₁ k₂ h₁₂ hpeq
    · exact hconflict k₂ k₁ h₂₁ hpeq.symm
  obtain ⟨N₂, hN₂_N₁, hfrozen⟩ := hshared_freeze
  -- Step 4: After `N₂`, sum/pigeonhole: some process `p` steps infinitely often, strictly
  -- decreasing `rank (exec.states n) p` on its own steps while other steps never increase it!
  obtain ⟨p, hinf_p⟩ :=
    Finite.exists_infinite_fiber (fun k : ℕ => (exec.labels (N₂ + k)).proc)
  have hp_unbdd : ∀ K, ∃ k ≥ K, (exec.labels (N₂ + k)).proc = p := by
    intro K
    by_contra hbdd
    let toFin : ((fun k : ℕ => (exec.labels (N₂ + k)).proc) ⁻¹' {p}) → Fin K :=
      fun x => ⟨x.1, by by_contra hge; exact hbdd ⟨x.1, by omega, x.2⟩⟩
    obtain ⟨x₁, x₂, hxne, hfeq⟩ := Finite.exists_ne_map_eq_of_infinite toFin
    exact hxne (Subtype.ext (Fin.mk.inj hfeq))
  have hrank_mono : ∀ {a b}, N₂ ≤ a → a ≤ b →
      rank (exec.states b) p ≤ rank (exec.states a) p := by
    intro a b ha hab
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst this; exact Nat.le_refl _
    | succ m ih =>
      by_cases hlt : a ≤ m
      · have hm_le := ih hlt
        obtain ⟨q, _, hq_act, hq_step⟩ := hstep_at m (by omega)
        have hq1 : (sys.step (exec.states m) q).1 = exec.states (m + 1) := congrArg Prod.fst hq_step
        have hq2 : (sys.step (exec.states m) q).2 = false := congrArg Prod.snd hq_step
        have hsh : shared (sys.step (exec.states m) q).1 = shared (exec.states m) := by
          rw [hq1]; exact hfrozen m (by omega)
        by_cases hpq : p = q
        · subst hpq
          have hdec := rank_lt_of_shared_eq hq_act hq2 hsh
          rw [hq1] at hdec
          omega
        · have hle_q := rank_le_of_shared_eq_ne hq_act hq2 hsh hpq
          rw [hq1] at hle_q
          omega
      · have : a = m + 1 := by omega
        subst this; exact Nat.le_refl _
  -- Construct `R + 1` steps of `p` after `N₂`, where `R = rank (exec.states N₂) p`, to force
  -- `rank < 0`, contradiction!
  have hdrop : ∀ r : ℕ, ∃ k, rank (exec.states (N₂ + k)) p + r ≤ rank (exec.states N₂) p := by
    intro r
    induction r with
    | zero => exact ⟨0, by simp only [Nat.add_zero, Nat.le_refl]⟩
    | succ r' ih =>
      obtain ⟨k₀, hk₀⟩ := ih
      obtain ⟨k₁, hk₁_ge, hk₁_p⟩ := hp_unbdd k₀
      have hle_01 := hrank_mono (a := N₂ + k₀) (b := N₂ + k₁) (by omega)
        (Nat.add_le_add_left hk₁_ge N₂)
      obtain ⟨q, hlq, hq_act, hq_step⟩ := hstep_at (N₂ + k₁) (by omega)
      have hqp : q = p := by
        simpa only [hlq, StepLabel.proc_exec] using hk₁_p
      subst hqp
      have hq1 : (sys.step (exec.states (N₂ + k₁)) q).1 = exec.states (N₂ + (k₁ + 1)) := by
        have := congrArg Prod.fst hq_step
        simpa only [Nat.add_assoc] using this
      have hq2 : (sys.step (exec.states (N₂ + k₁)) q).2 = false := congrArg Prod.snd hq_step
      have hsh : shared (sys.step (exec.states (N₂ + k₁)) q).1 =
          shared (exec.states (N₂ + k₁)) := by
        rw [hq1]
        simpa only [Nat.add_assoc] using hfrozen (N₂ + k₁) (by omega)
      have hdec := rank_lt_of_shared_eq hq_act hq2 hsh
      rw [hq1] at hdec
      exact ⟨k₁ + 1, by omega⟩
  obtain ⟨k_bad, hk_bad⟩ := hdrop (rank (exec.states N₂) p + 1)
  omega

end ProgressSystem

/-! ### Concrete separating shared-memory implementations -/

/-- State of a single-step atomic increment counter over processes `P`: `counter` holds the shared
natural number and `pending p = true` iff `p` has an uncompleted increment invocation. -/
@[ext]
structure AtomicIncState (P : Type*) where
  /-- Current shared counter value. -/
  counter : ℕ
  /-- Per-process pending-operation flag. -/
  pending : P → Bool

/-- Wait-free single-step atomic increment system over processes `P`. -/
@[expose]
def atomicIncSystem (P : Type*) [DecidableEq P] : ProgressSystem P where
  State := AtomicIncState P
  init := { counter := 0, pending := fun _ => false }
  Active s p := s.pending p = true
  Invoke s p s' :=
    s.pending p = false ∧ s' = { s with pending := Function.update s.pending p true }
  step s p :=
    if s.pending p then
      ({ counter := s.counter + 1, pending := Function.update s.pending p false }, true)
    else
      (s, false)
  invoke_only_idle := by
    rintro s p _ ⟨hp, _⟩ hact
    rw [hp] at hact
    exact Bool.noConfusion hact
  active_after_invoke := by
    rintro s p _ ⟨_, rfl⟩
    simp only [Function.update_self]
  invoke_frame_active := by
    rintro s p q _ ⟨_, rfl⟩ hqp
    simp only [Function.update_of_ne hqp]
  active_after_step_false := by
    intro s p hact hfalse
    simp only [hact, ↓reduceIte] at hfalse
    exact Bool.noConfusion hfalse
  idle_after_step_true := by
    intro s p hact _
    simp only [hact, ↓reduceIte, Function.update_self, Bool.false_eq_true, not_false_eq_true]
  step_frame_active := by
    intro s p q hact hqp
    simp only [hact, ↓reduceIte, Function.update_of_ne hqp]

/-- Single-step atomic increment is wait-free. -/
theorem atomicIncSystem_isWaitFree (P : Type*) [DecidableEq P] :
    (atomicIncSystem P).IsWaitFree := by
  intro exec p t₀ _ hinf
  obtain ⟨n, hn, he, hp⟩ := hinf t₀ (Nat.le_refl t₀)
  have htr := exec.valid n
  cases hlbl : exec.labels n with
  | invoke _ =>
    rw [hlbl, StepLabel.isExec_invoke] at he
    exact Bool.noConfusion he
  | exec q done =>
    rw [hlbl, StepLabel.proc_exec] at hp
    subst hp
    rw [hlbl] at htr
    obtain ⟨hact_n, hstep_n⟩ := htr
    have hdone : done = true := by
      have h2 := congrArg Prod.snd hstep_n
      dsimp only [atomicIncSystem] at hact_n h2
      simp only [hact_n, ↓reduceIte] at h2
      exact h2.symm
    subst hdone
    exact ⟨n, hn, hlbl⟩

/-! #### Separating Lock-Freedom from Wait-Freedom: Two-Step `CAS` Counter -/

/-- Local execution phase of a process in the two-step `CAS` fetch-and-increment counter
([MoirShavit2007], §1.1.3, p. 1-6). -/
inductive CASCounterPhase where
  /-- No pending operation. -/
  | idle
  /-- Ready to read the current value of the shared counter. -/
  | readCounter
  /-- Read `expected` from the shared counter; ready to execute `CAS(&counter, expected,
  expected + 1)`, retrying from `readCounter` on failure. -/
  | tryCAS (expected : ℕ)
  deriving @[expose] DecidableEq

/-- Global configuration of the two-step `CAS` fetch-and-increment counter over processes `P`. -/
@[ext]
structure CASCounterState (P : Type*) where
  /-- Shared `CAS` register holding the current counter value. -/
  counter : ℕ
  /-- Per-process local control phase. -/
  threads : P → CASCounterPhase

namespace CASCounterPhase

/-- Bounded solo-progress rank when `counter` is unchanged across non-completing steps. -/
private def rank (counter : ℕ) : CASCounterPhase → ℕ
  | .idle => 0
  | .tryCAS expected => if expected = counter then 1 else 3
  | .readCounter => 2

end CASCounterPhase

/-- Original two-step optimistic `CAS` fetch-and-increment counter model (illustrating the `CAS`
retry-loop starvation mechanism discussed in [MoirShavit2007], §1.1.3, p. 1-6):
each operation reads `c := counter` in one step and attempts `CAS(&counter, c, c + 1)` in the next,
retrying from `readCounter` whenever a concurrent `CAS` has modified `counter`. -/
@[expose]
def casCounterSystem (P : Type*) [DecidableEq P] : ProgressSystem P where
  State := CASCounterState P
  init := { counter := 0, threads := fun _ => .idle }
  Active s p := s.threads p ≠ .idle
  Invoke s p s' :=
    s.threads p = .idle ∧ s' = { s with threads := Function.update s.threads p .readCounter }
  step s p :=
    match s.threads p with
    | .idle => (s, false)
    | .readCounter =>
      ({ s with threads := Function.update s.threads p (.tryCAS s.counter) }, false)
    | .tryCAS expected =>
      if s.counter = expected then
        ({ counter := expected + 1, threads := Function.update s.threads p .idle }, true)
      else
        ({ s with threads := Function.update s.threads p .readCounter }, false)
  invoke_only_idle := by
    rintro s p _ ⟨hp, _⟩ hact
    exact hact hp
  active_after_invoke := by
    rintro s p _ ⟨_, rfl⟩
    simp only [ne_eq, Function.update_self, reduceCtorEq, not_false_eq_true]
  invoke_frame_active := by
    rintro s p q _ ⟨_, rfl⟩ hqp
    simp only [ne_eq, Function.update_of_ne hqp]
  active_after_step_false := by
    intro s p hact hfalse
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | readCounter =>
      simp only [ne_eq, Function.update_self, reduceCtorEq, not_false_eq_true]
    | tryCAS exp =>
      simp only [htp] at hfalse ⊢
      by_cases hc : s.counter = exp
      · simp only [hc, ↓reduceIte] at hfalse
        exact Bool.noConfusion hfalse
      · simp only [hc, ↓reduceIte, ne_eq, Function.update_self, reduceCtorEq, not_false_eq_true]
  idle_after_step_true := by
    intro s p hact htrue
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | readCounter =>
      simp only [htp] at htrue
      exact Bool.noConfusion htrue
    | tryCAS exp =>
      simp only [htp] at htrue ⊢
      by_cases hc : s.counter = exp
      · simp only [hc, ↓reduceIte, ne_eq, Function.update_self, not_true_eq_false,
          not_false_eq_true]
      · simp only [hc, ↓reduceIte] at htrue
        exact Bool.noConfusion htrue
  step_frame_active := by
    intro s p q hact hqp
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | readCounter => simp only [Function.update_of_ne hqp]
    | tryCAS exp =>
      by_cases hc : s.counter = exp <;>
        simp only [hc, ↓reduceIte, ne_eq, Function.update_of_ne hqp]

/-- Original lock-freedom proof for `casCounterSystem` over finitely many processes (`[Finite P]`,
illustrating [MoirShavit2007], §1.1.3, p. 1-6). -/
theorem casCounterSystem_isLockFree (P : Type*) [DecidableEq P] [Finite P] :
    (casCounterSystem P).IsLockFree := by
  refine ProgressSystem.isLockFree_of_bounded_shared_changes
    (sys := casCounterSystem P)
    (shared := CASCounterState.counter)
    (Committed := fun _ _ => False)
    (rank := fun s p => CASCounterPhase.rank s.counter (s.threads p))
    ?_ ?_ ?_ ?_ ?_
  · intro s p hact hfalse hsh_ne
    exfalso
    cases htp : s.threads p with
    | idle => exact hact htp
    | readCounter =>
      simp only [casCounterSystem, htp] at hsh_ne
      exact hsh_ne rfl
    | tryCAS exp =>
      simp only [casCounterSystem, htp] at hfalse hsh_ne
      by_cases hc : s.counter = exp
      · simp only [hc, ↓reduceIte] at hfalse
        exact Bool.noConfusion hfalse
      · simp only [hc, ↓reduceIte] at hsh_ne
        exact hsh_ne rfl
  · intro _ _ _ _ _ _ hcomm
    exact hcomm
  · intro _ _ _ hcomm
    exact False.elim hcomm
  · intro s p hact hfalse _
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | readCounter =>
      simp only [casCounterSystem, htp, Function.update_self, CASCounterPhase.rank, ↓reduceIte]
      omega
    | tryCAS exp =>
      simp only [casCounterSystem, htp] at hfalse ⊢
      by_cases hc : s.counter = exp
      · simp only [hc, ↓reduceIte] at hfalse
        exact Bool.noConfusion hfalse
      · have hne : exp ≠ s.counter := Ne.symm hc
        simp only [hc, ↓reduceIte, Function.update_self, CASCounterPhase.rank, hne]
        omega
  · intro s p q hact hfalse _ hqp
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | readCounter =>
      simp only [casCounterSystem, htp, Function.update_of_ne hqp, Nat.le_refl]
    | tryCAS exp =>
      simp only [casCounterSystem, htp] at hfalse ⊢
      by_cases hc : s.counter = exp
      · simp only [hc, ↓reduceIte] at hfalse
        exact Bool.noConfusion hfalse
      · simp only [hc, ↓reduceIte, Function.update_of_ne hqp, Nat.le_refl]

/-- Original `CAS`-starvation witness over `[Nontrivial P]` (illustrating [MoirShavit2007], §1.1.3,
p. 1-6): `casCounterSystem P` is **not wait-free** because a fast process repeatedly invoking,
reading, and succeeding at `CAS` starves a slow process whose `CAS` continually sees a stale
counter value and retries forever. -/
theorem casCounterSystem_not_isWaitFree (P : Type*) [DecidableEq P] [Nontrivial P] :
    ¬ (casCounterSystem P).IsWaitFree := by
  obtain ⟨slow, fast, hne⟩ := exists_pair_ne P
  intro hwf
  -- Periodic 5-step starvation schedule:
  -- `r = 0`: `slow` steps (`readCounter → tryCAS k`)
  -- `r = 1`: `fast` invokes (`idle → readCounter`)
  -- `r = 2`: `fast` steps (`readCounter → tryCAS k`)
  -- `r = 3`: `fast` steps and completes (`tryCAS k → idle`, `counter := k + 1`)
  -- `r = 4`: `slow` steps and fails `CAS` (`tryCAS k → readCounter`)
  let mkThreads (sPhase fPhase : CASCounterPhase) : P → CASCounterPhase :=
    Function.update (Function.update (fun _ : P => CASCounterPhase.idle) slow sPhase) fast fPhase
  let stateAt (n : ℕ) : CASCounterState P :=
    let k := n / 5
    match n % 5 with
    | 0 => { counter := k, threads := mkThreads .readCounter .idle }
    | 1 => { counter := k, threads := mkThreads (.tryCAS k) .idle }
    | 2 => { counter := k, threads := mkThreads (.tryCAS k) .readCounter }
    | 3 => { counter := k, threads := mkThreads (.tryCAS k) (.tryCAS k) }
    | _ => { counter := k + 1, threads := mkThreads (.tryCAS k) .idle }
  let labelAt (n : ℕ) : StepLabel P :=
    match n % 5 with
    | 0 => .exec slow false
    | 1 => .invoke fast
    | 2 => .exec fast false
    | 3 => .exec fast true
    | _ => .exec slow false
  have hmk_slow : ∀ sp fp, mkThreads sp fp slow = sp := by
    intro sp fp
    simp only [mkThreads, Function.update_of_ne hne, Function.update_self]
  have hmk_fast : ∀ sp fp, mkThreads sp fp fast = fp := by
    intro sp fp
    simp only [mkThreads, Function.update_self]
  have hupd_slow : ∀ sp fp sp',
      Function.update (mkThreads sp fp) slow sp' = mkThreads sp' fp := by
    intro sp fp sp'
    funext q
    by_cases hqf : q = fast
    · subst hqf
      simp only [mkThreads, Function.update_of_ne hne.symm, Function.update_self]
    · by_cases hqs : q = slow
      · subst hqs
        simp only [mkThreads, Function.update_self, Function.update_of_ne hne]
      · simp only [mkThreads, Function.update_of_ne hqf, Function.update_of_ne hqs]
  have hupd_fast : ∀ sp fp fp',
      Function.update (mkThreads sp fp) fast fp' = mkThreads sp fp' := by
    intro sp fp fp'
    simp only [mkThreads, Function.update_idem]
  have hreach₀ : (casCounterSystem P).Reachable (stateAt 0) := by
    have htr₀ :
        (casCounterSystem P).lts.Tr (casCounterSystem P).init (.invoke slow) (stateAt 0) := by
      refine ⟨rfl, ?_⟩
      ext q
      · rfl
      · by_cases hqf : q = fast
        · subst hqf
          simp only [stateAt, Nat.zero_mod, mkThreads, casCounterSystem, Function.update_self,
            Function.update_of_ne hne.symm]
        · simp only [stateAt, Nat.zero_mod, mkThreads, casCounterSystem, Function.update_of_ne hqf]
    exact (ProgressSystem.Reachable.init _).step htr₀
  have hvalid : ∀ n, (casCounterSystem P).lts.Tr (stateAt n) (labelAt n) (stateAt (n + 1)) := by
    intro n
    have hmod_cases : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases hmod_cases with hm | hm | hm | hm | hm
    · have hdiv : (n + 1) / 5 = n / 5 := by omega
      have hm' : (n + 1) % 5 = 1 := by omega
      simp only [stateAt, labelAt, hm, hm', hdiv, ProgressSystem.lts, casCounterSystem, hmk_slow,
        ne_eq, reduceCtorEq, not_false_eq_true, hupd_slow, and_self]
    · have hdiv : (n + 1) / 5 = n / 5 := by omega
      have hm' : (n + 1) % 5 = 2 := by omega
      simp only [stateAt, labelAt, hm, hm', hdiv, ProgressSystem.lts, casCounterSystem, hmk_fast,
        hupd_fast, and_self]
    · have hdiv : (n + 1) / 5 = n / 5 := by omega
      have hm' : (n + 1) % 5 = 3 := by omega
      simp only [stateAt, labelAt, hm, hm', hdiv, ProgressSystem.lts, casCounterSystem, hmk_fast,
        ne_eq, reduceCtorEq, not_false_eq_true, hupd_fast, and_self]
    · have hdiv : (n + 1) / 5 = n / 5 := by omega
      have hm' : (n + 1) % 5 = 4 := by omega
      simp only [stateAt, labelAt, hm, hm', hdiv, ProgressSystem.lts, casCounterSystem, hmk_fast,
        ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, hupd_fast, and_self]
    · have hdiv : (n + 1) / 5 = n / 5 + 1 := by omega
      have hm' : (n + 1) % 5 = 0 := by omega
      have hne_k : n / 5 + 1 ≠ n / 5 := by omega
      simp only [stateAt, labelAt, hm, hm', hdiv, ProgressSystem.lts, casCounterSystem, hmk_slow,
        ne_eq, reduceCtorEq, not_false_eq_true, hne_k, ↓reduceIte, hupd_slow, and_self]
  let exec : (casCounterSystem P).InfiniteExec :=
    { states := stateAt
      labels := labelAt
      reachable_zero := hreach₀
      valid := hvalid }
  have hact₀ : (casCounterSystem P).Active (exec.states 0) slow := by
    simp only [exec, stateAt, Nat.zero_mod, casCounterSystem, hmk_slow, ne_eq, reduceCtorEq,
      not_false_eq_true]
  have hinf_slow : ∀ M ≥ 0, ∃ n ≥ M,
      (exec.labels n).isExec = true ∧ (exec.labels n).proc = slow := by
    intro M _
    refine ⟨5 * M, by omega, ?_⟩
    have hm : (5 * M) % 5 = 0 := by omega
    simp only [exec, labelAt, hm, StepLabel.isExec_exec, StepLabel.proc_exec, and_self]
  obtain ⟨n, _, hdone⟩ := hwf exec slow 0 hact₀ hinf_slow
  have hmod_cases : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hmod_cases with hm | hm | hm | hm | hm
  · simp only [exec, labelAt, hm, StepLabel.exec.injEq, Bool.false_eq_true, and_false] at hdone
  · simp only [exec, labelAt, hm, reduceCtorEq] at hdone
  · simp only [exec, labelAt, hm, StepLabel.exec.injEq, Bool.false_eq_true, and_false] at hdone
  · simp only [exec, labelAt, hm, StepLabel.exec.injEq, and_true] at hdone
    exact hne hdone.symm
  · simp only [exec, labelAt, hm, StepLabel.exec.injEq, Bool.false_eq_true, and_false] at hdone

/-- Original concrete `ProgressSystem` separation of lock-freedom from wait-freedom (illustrating
[MoirShavit2007], §1.1.3, p. 1-6): there exists a finite-process concurrent-object transition
system that is lock-free yet not wait-free. -/
theorem exists_lockFree_not_waitFree :
    ∃ sys : ProgressSystem Bool, sys.IsLockFree ∧ ¬ sys.IsWaitFree :=
  ⟨casCounterSystem Bool, casCounterSystem_isLockFree Bool, casCounterSystem_not_isWaitFree Bool⟩

/-! #### Separating Obstruction-Freedom from Lock-Freedom: Racing Claim-and-Verify Protocol -/

/-- Local execution phase of a process in the original minimal shared-register claim-and-verify
witness isolating two-thread contention livelock ([HerlihyLuchangcoMoir2003], §1, pp. 1–2). -/
inductive ClaimPhase where
  /-- No pending operation. -/
  | idle
  /-- Ready to write own process ID into the shared `owner` register. -/
  | writeClaim
  /-- Wrote own ID into `owner`; ready to verify `owner = some p` and complete if uncontested, or
  retry from `writeClaim` if overwritten by a concurrent process. -/
  | verifyClaim
  deriving @[expose] DecidableEq

/-- Global configuration of the racing shared-register claim-and-verify protocol over `P`. -/
@[ext]
structure RacingClaimState (P : Type*) where
  /-- Shared atomic register recording the last process to execute `writeClaim`. -/
  owner : Option P
  /-- Per-process local control phase. -/
  threads : P → ClaimPhase

/-- Original minimal shared-register claim-and-verify system (isolating the two-thread livelock
mechanism discussed in [HerlihyLuchangcoMoir2003], §1, pp. 1–2): an active process writes its ID to
`owner` (`writeClaim`) and completes on the next step (`verifyClaim`) iff no other process overwrote
`owner` in between; otherwise it retries from `writeClaim`. -/
@[expose]
def racingClaimSystem (P : Type*) [DecidableEq P] : ProgressSystem P where
  State := RacingClaimState P
  init := { owner := none, threads := fun _ => .idle }
  Active s p := s.threads p ≠ .idle
  Invoke s p s' :=
    s.threads p = .idle ∧ s' = { s with threads := Function.update s.threads p .writeClaim }
  step s p :=
    match s.threads p with
    | .idle => (s, false)
    | .writeClaim =>
      ({ owner := some p, threads := Function.update s.threads p .verifyClaim }, false)
    | .verifyClaim =>
      if s.owner = some p then
        ({ s with threads := Function.update s.threads p .idle }, true)
      else
        ({ s with threads := Function.update s.threads p .writeClaim }, false)
  invoke_only_idle := by
    rintro s p _ ⟨hp, _⟩ hact
    exact hact hp
  active_after_invoke := by
    rintro s p _ ⟨_, rfl⟩
    simp only [ne_eq, Function.update_self, reduceCtorEq, not_false_eq_true]
  invoke_frame_active := by
    rintro s p q _ ⟨_, rfl⟩ hqp
    simp only [ne_eq, Function.update_of_ne hqp]
  active_after_step_false := by
    intro s p hact hfalse
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | writeClaim =>
      simp only [ne_eq, Function.update_self, reduceCtorEq, not_false_eq_true]
    | verifyClaim =>
      simp only [htp] at hfalse ⊢
      by_cases ho : s.owner = some p
      · simp only [ho, ↓reduceIte] at hfalse
        exact Bool.noConfusion hfalse
      · simp only [ho, ↓reduceIte, ne_eq, Function.update_self, reduceCtorEq, not_false_eq_true]
  idle_after_step_true := by
    intro s p hact htrue
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | writeClaim =>
      simp only [htp] at htrue
      exact Bool.noConfusion htrue
    | verifyClaim =>
      simp only [htp] at htrue ⊢
      by_cases ho : s.owner = some p
      · simp only [ho, ↓reduceIte, ne_eq, Function.update_self, not_true_eq_false,
          not_false_eq_true]
      · simp only [ho, ↓reduceIte] at htrue
        exact Bool.noConfusion htrue
  step_frame_active := by
    intro s p q hact hqp
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | writeClaim => simp only [Function.update_of_ne hqp]
    | verifyClaim =>
      by_cases ho : s.owner = some p <;>
        simp only [ho, ↓reduceIte, ne_eq, Function.update_of_ne hqp]

/-- Original obstruction-freedom proof for `racingClaimSystem` (illustrating
[HerlihyLuchangcoMoir2003], §1, p. 1): from any state, any active process `p` completes within at
most 3 solo steps (`k ∈ {0, 1, 2}`). -/
theorem racingClaimSystem_isObstructionFree (P : Type*) [DecidableEq P] :
    (racingClaimSystem P).IsObstructionFree := by
  intro s _ p hact
  cases htp : s.threads p with
  | idle => exact absurd htp hact
  | writeClaim =>
    refine ⟨1, ?_⟩
    dsimp only [ProgressSystem.soloIter, racingClaimSystem]
    simp only [htp, Function.update_self, ↓reduceIte]
  | verifyClaim =>
    by_cases ho : s.owner = some p
    · refine ⟨0, ?_⟩
      dsimp only [ProgressSystem.soloIter, racingClaimSystem]
      simp only [htp, ho, ↓reduceIte]
    · refine ⟨2, ?_⟩
      dsimp only [ProgressSystem.soloIter, racingClaimSystem]
      simp only [htp, ho, ↓reduceIte, Function.update_self]

/-- Original two-thread livelock witness over `[Nontrivial P]` (illustrating
[HerlihyLuchangcoMoir2003], §1, pp. 1–2): `racingClaimSystem P` is **not lock-free** because two
active processes alternating `writeClaim` and `verifyClaim` out of phase overwrite each other's
claim on every cycle so neither operation ever completes. -/
theorem racingClaimSystem_not_isLockFree (P : Type*) [DecidableEq P] [Nontrivial P] :
    ¬ (racingClaimSystem P).IsLockFree := by
  obtain ⟨p₀, p₁, hne⟩ := exists_pair_ne P
  intro hlf
  -- Reach `{ owner := some p₀, p₀ := .verifyClaim, p₁ := .writeClaim }` in 3 steps from `init`,
  -- then repeat the 4-step livelock cycle forever:
  -- `r = 0`: `p₁` writes `some p₁` (`writeClaim → verifyClaim`)
  -- `r = 1`: `p₀` sees `some p₁ ≠ some p₀` (`verifyClaim → writeClaim`)
  -- `r = 2`: `p₀` writes `some p₀` (`writeClaim → verifyClaim`)
  -- `r = 3`: `p₁` sees `some p₀ ≠ some p₁` (`verifyClaim → writeClaim`)
  let mkThreads (ph₀ ph₁ : ClaimPhase) : P → ClaimPhase :=
    Function.update (Function.update (fun _ : P => ClaimPhase.idle) p₀ ph₀) p₁ ph₁
  have hmk₀ : ∀ ph₀ ph₁, mkThreads ph₀ ph₁ p₀ = ph₀ := by
    intro ph₀ ph₁
    simp only [mkThreads, Function.update_of_ne hne, Function.update_self]
  have hmk₁ : ∀ ph₀ ph₁, mkThreads ph₀ ph₁ p₁ = ph₁ := by
    intro ph₀ ph₁
    simp only [mkThreads, Function.update_self]
  have hupd₀ : ∀ ph₀ ph₁ ph₀',
      Function.update (mkThreads ph₀ ph₁) p₀ ph₀' = mkThreads ph₀' ph₁ := by
    intro ph₀ ph₁ ph₀'
    funext q
    by_cases hq₁ : q = p₁
    · subst hq₁
      simp only [mkThreads, Function.update_of_ne hne.symm, Function.update_self]
    · by_cases hq₀ : q = p₀
      · subst hq₀
        simp only [mkThreads, Function.update_self, Function.update_of_ne hne]
      · simp only [mkThreads, Function.update_of_ne hq₁, Function.update_of_ne hq₀]
  have hupd₁ : ∀ ph₀ ph₁ ph₁',
      Function.update (mkThreads ph₀ ph₁) p₁ ph₁' = mkThreads ph₀ ph₁' := by
    intro ph₀ ph₁ ph₁'
    simp only [mkThreads, Function.update_idem]
  let stateAt (n : ℕ) : RacingClaimState P :=
    match n % 4 with
    | 0 => { owner := some p₀, threads := mkThreads .verifyClaim .writeClaim }
    | 1 => { owner := some p₁, threads := mkThreads .verifyClaim .verifyClaim }
    | 2 => { owner := some p₁, threads := mkThreads .writeClaim .verifyClaim }
    | _ => { owner := some p₀, threads := mkThreads .verifyClaim .verifyClaim }
  let labelAt (n : ℕ) : StepLabel P :=
    match n % 4 with
    | 0 => .exec p₁ false
    | 1 => .exec p₀ false
    | 2 => .exec p₀ false
    | _ => .exec p₁ false
  -- Show `stateAt 0` is reachable in 3 steps from `init`:
  let s₁ : RacingClaimState P :=
    { owner := none, threads := Function.update (fun _ : P => ClaimPhase.idle) p₀ .writeClaim }
  let s₂ : RacingClaimState P :=
    { owner := none, threads := mkThreads .writeClaim .writeClaim }
  have hr₁ : (racingClaimSystem P).Reachable s₁ :=
    (ProgressSystem.Reachable.init _).step (lbl := .invoke p₀) ⟨rfl, rfl⟩
  have hr₂ : (racingClaimSystem P).Reachable s₂ := by
    have htr : (racingClaimSystem P).lts.Tr s₁ (.invoke p₁) s₂ :=
      ⟨by simp only [s₁, Function.update_of_ne hne.symm], rfl⟩
    exact hr₁.step htr
  have hr₃ : (racingClaimSystem P).Reachable (stateAt 0) := by
    have htr : (racingClaimSystem P).lts.Tr s₂ (.exec p₀ false) (stateAt 0) := by
      simp only [ProgressSystem.lts, racingClaimSystem, s₂, stateAt, Nat.zero_mod, hmk₀, ne_eq,
        reduceCtorEq, not_false_eq_true, hupd₀, and_self]
    exact hr₂.step htr
  have hvalid : ∀ n, (racingClaimSystem P).lts.Tr (stateAt n) (labelAt n) (stateAt (n + 1)) := by
    intro n
    have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hmod with hm | hm | hm | hm
    · have hm' : (n + 1) % 4 = 1 := by omega
      simp only [stateAt, labelAt, hm, hm', ProgressSystem.lts, racingClaimSystem, hmk₁, ne_eq,
        reduceCtorEq, not_false_eq_true, hupd₁, and_self]
    · have hm' : (n + 1) % 4 = 2 := by omega
      have hne_opt : (some p₁ : Option P) ≠ some p₀ := fun h => hne (Option.some.inj h).symm
      simp only [stateAt, labelAt, hm, hm', ProgressSystem.lts, racingClaimSystem, hmk₀, ne_eq,
        reduceCtorEq, not_false_eq_true, hne_opt, ↓reduceIte, hupd₀, and_self]
    · have hm' : (n + 1) % 4 = 3 := by omega
      simp only [stateAt, labelAt, hm, hm', ProgressSystem.lts, racingClaimSystem, hmk₀, ne_eq,
        reduceCtorEq, not_false_eq_true, hupd₀, and_self]
    · have hm' : (n + 1) % 4 = 0 := by omega
      have hne_opt : (some p₀ : Option P) ≠ some p₁ := fun h => hne (Option.some.inj h)
      simp only [stateAt, labelAt, hm, hm', ProgressSystem.lts, racingClaimSystem, hmk₁, ne_eq,
        reduceCtorEq, not_false_eq_true, hne_opt, ↓reduceIte, hupd₁, and_self]
  let exec : (racingClaimSystem P).InfiniteExec :=
    { states := stateAt
      labels := labelAt
      reachable_zero := hr₃
      valid := hvalid }
  have hexec_all : ∀ M, ∃ n ≥ M, (exec.labels n).isExec = true := by
    intro M
    refine ⟨M, Nat.le_refl M, ?_⟩
    have hmod : M % 4 = 0 ∨ M % 4 = 1 ∨ M % 4 = 2 ∨ M % 4 = 3 := by omega
    rcases hmod with hm | hm | hm | hm <;> simp only [exec, labelAt, hm, StepLabel.isExec_exec]
  obtain ⟨n, _, hc⟩ := hlf exec hexec_all 0
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with hm | hm | hm | hm <;>
    simp only [exec, labelAt, hm, StepLabel.isCompleted_exec, Bool.false_eq_true] at hc

/-- Original concrete `ProgressSystem` separation of obstruction-freedom from lock-freedom
(illustrating [HerlihyLuchangcoMoir2003], §1, pp. 1–2): there exists a finite-process
concurrent-object transition system that is obstruction-free yet not lock-free. -/
theorem exists_obstructionFree_not_lockFree :
    ∃ sys : ProgressSystem Bool, sys.IsObstructionFree ∧ ¬ sys.IsLockFree :=
  ⟨racingClaimSystem Bool,
    racingClaimSystem_isObstructionFree Bool,
    racingClaimSystem_not_isLockFree Bool⟩

end Cslib.Distributed.ConcurrentObjects
