/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.ObliviousTransfer

/-!
# Ideal UC Secure Function Evaluation with Abort

This module defines the `n`-party ideal functionality `fsfe` for secure function evaluation (SFE)
with abort of a deterministic function `f : (Fin n → In) → (Fin n → Out)` in the Universally
Composable (UC) framework with static corruptions
(`CslibFrontier/Crypto/Protocols/UC/Execution.lean`), adapting the ideal SFE functionality of
[Canetti2020] (and motivated by [BonehShoup2023], Chapter 23; chapter/section locators not
verified from the rendered PDF) to this library's call-bounded, pull-only port
model (`UC.IdealFunctionality`).

## Model and scope

* **Parties and inputs:** Each party `i : Fin n` submits its input `x i : In` once via
  `SFEInput.input (x i)` (write-once immutable) and polls for its output via `SFEInput.query`.
* **Delayed output and selective abort:** Outputs wait until all `n` parties have submitted inputs
  (`SFEState.allSubmitted = true`) and the adversary issues `SFEBackdoor.deliver i` (provided no
  abort has occurred yet), after which party `i` observes `some (.output (f x i))`. Issuing
  `SFEBackdoor.abort` sets `aborted := true`: any party whose output was already delivered retains
  `some (.output (f x i))`, while undelivered parties observe `some .aborted` and subsequent
  `deliver` calls have no effect.
* **Minimal status leakage:** Polling `SFEBackdoor.query` returns `SFEBackdoorReply.status st` where
  `st : SFEStatus n` exposes only arrival, delivery, and abort Boolean flags, never honest inputs
  or other parties' outputs.
* **Call-bounded pull model:** As throughout `CslibFrontier/Crypto/Protocols/UC/Execution.lean`,
  activations are pull-based and `PolyBounded` / `IsBounded` count oracle calls and private coins
  only, not PPT interactive Turing machine running time.

## Main definitions

* `Cslib.Crypto.Protocols.UC.SFEInput`, `Cslib.Crypto.Protocols.UC.SFEOutput`,
  `Cslib.Crypto.Protocols.UC.SFEStatus`, `Cslib.Crypto.Protocols.UC.SFEBackdoor`,
  `Cslib.Crypto.Protocols.UC.SFEBackdoorReply`, `Cslib.Crypto.Protocols.UC.SFEState`: named
  request, reply, status, backdoor, and state records for `n`-party SFE with abort.
* `Cslib.Crypto.Protocols.UC.fsfe`: the `n`-party ideal SFE functionality
  $\mathcal{F}_{\mathrm{SFE}}$ for a deterministic function `f : (Fin n → In) → (Fin n → Out)`.
* `Cslib.Crypto.Protocols.UC.SFECorruptEquiv`, `Cslib.Crypto.Protocols.UC.SFEPreOutputEquiv`:
  corrupted-party and backdoor equivalence relations for honest-input privacy.
* `Cslib.Crypto.Protocols.UC.otEvalFn`, `Cslib.Crypto.Protocols.UC.otSFE`,
  `Cslib.Crypto.Protocols.UC.otInSFEHybrid`: concrete 2-party `fsfe` instantiation of 1-out-of-2 OT
  and its role-typed hybrid wrapper.

## Main results

* `Cslib.Crypto.Protocols.UC.fsfe_isBounded`, `Cslib.Crypto.Protocols.UC.fsfe_polyBounded`,
  `Cslib.Crypto.Protocols.UC.fsfe_multiSession_polyBounded`: zero-call budget bounds for `fsfe` and
  its multi-session extension `(fsfe f).multiSession SSID`.
* `Cslib.Crypto.Protocols.UC.SFEState.monotone_of_mem_support_runFrom`: write-once input lock and
  delivery/abort monotonicity across arbitrary multi-step interactions.
* `Cslib.Crypto.Protocols.UC.eval_exec_honestSFEEnv`,
  `Cslib.Crypto.Protocols.UC.eval_exec_abortSFEEnv`: honest evaluation agreement (`f x i`) and
  abort behavior.
* `Cslib.Crypto.Protocols.UC.eval_runFrom_fsfe_corrupt_preAllSubmitted_eq`,
  `Cslib.Crypto.Protocols.UC.eval_runFrom_fsfe_corrupt_preDeliver_eq`,
  `Cslib.Crypto.Protocols.UC.eval_runFrom_fsfe_corrupt_eq`,
  `Cslib.Crypto.Protocols.UC.eval_runFrom_fsfe_corrupt_inputs_eq`: **honest-input privacy** before
  all inputs arrive, before corrupted-party delivery, and post-output when `f x i = f x' i` for
  all `i ∈ C`.
* `Cslib.Crypto.Protocols.UC.eval_exec_otInSFE_honestOT`,
  `Cslib.Crypto.Protocols.UC.eval_exec_otInSFE_abortOT`,
  `Cslib.Crypto.Protocols.UC.otSFE_sender_abort_differs_from_fot`,
  `Cslib.Crypto.Protocols.UC.otSFE_selective_deliver_zero`: `fot` vs. 2-party `fsfe`
  correspondence and semantic comparison.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 23
  (motivation only; chapter/section locators not verified from the rendered PDF): ideal secure
  function evaluation with abort.
* [R. Canetti, *Universally Composable Security*][Canetti2020], Section 4: UC execution and
  realization.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open Polynomial
open scoped NNReal ENNReal

/-! ### Request, reply, status, backdoor, and state types -/

/-- Party-port inputs for `fsfe`: each party `i` submits its input once via `input val` and polls
for its output via `query`. -/
inductive SFEInput (In : Type) : Type
  | input (val : In)
  | query
  deriving DecidableEq, Repr

/-- Party-port outputs for `fsfe`: either the party's computed output `output val` or `aborted`. -/
inductive SFEOutput (Out : Type) : Type
  | output (val : Out)
  | aborted
  deriving DecidableEq, Repr

/-- Non-leaking status flags exposed on the backdoor of `fsfe`: per-party input arrival flags,
per-party output delivery flags, and the global abort flag. -/
structure SFEStatus (n : ℕ) : Type where
  /-- Whether party `i` has submitted its input. -/
  submitted : Fin n → Bool
  /-- Whether party `i`'s output has been released. -/
  delivered : Fin n → Bool
  /-- Whether the computation has been aborted. -/
  aborted : Bool

/-- Backdoor queries of `fsfe`: `query` reads `SFEStatus n`, `deliver party` releases output to
`party` once all inputs are present and no abort occurred, and `abort` sets the abort flag. -/
inductive SFEBackdoor (n : ℕ) : Type
  | query
  | deliver (party : Fin n)
  | abort
  deriving DecidableEq, Repr

/-- Backdoor replies of `fsfe`: either status flags or an acknowledgement. -/
inductive SFEBackdoorReply (n : ℕ) : Type
  | status (st : SFEStatus n)
  | ack

/-- Internal state of `fsfe`. -/
structure SFEState (n : ℕ) (In : Type) : Type where
  /-- Per-party submitted inputs, write-once. -/
  inputs : Fin n → Option In := fun _ => none
  /-- Per-party output delivery flags. -/
  delivered : Fin n → Bool := fun _ => false
  /-- Whether the adversary has aborted the evaluation. -/
  aborted : Bool := false

/-- Whether every party `i : Fin n` has submitted an input. -/
@[expose] def SFEState.allSubmitted {n : ℕ} {In : Type} (s : SFEState n In) : Bool :=
  decide (∀ i : Fin n, (s.inputs i).isSome)

/-- Extract the public `SFEStatus n` flags from `SFEState n In`. -/
@[expose] def SFEState.status {n : ℕ} {In : Type} (s : SFEState n In) : SFEStatus n where
  submitted i := (s.inputs i).isSome
  delivered := s.delivered
  aborted := s.aborted

/-- Evaluate `f` when all `n` parties have submitted inputs, returning `none` otherwise. -/
@[expose] def SFEState.eval? {n : ℕ} {In Out : Type}
    (f : (Fin n → In) → (Fin n → Out)) (s : SFEState n In) : Option (Fin n → Out) :=
  if h : ∀ i : Fin n, (s.inputs i).isSome then
    some (f fun i => (s.inputs i).get (h i))
  else
    none

/-- Party `i`'s observable output in state `s` on `SFEInput.query`. Delivered outputs persist even
if a selective `abort` occurs later; undelivered parties observe `some .aborted` after an abort. -/
@[expose] def SFEState.partyOutput {n : ℕ} {In Out : Type}
    (f : (Fin n → In) → (Fin n → Out)) (s : SFEState n In) (i : Fin n) :
    Option (SFEOutput Out) :=
  if s.delivered i then
    (s.eval? f).map fun y => .output (y i)
  else if s.aborted then
    some .aborted
  else
    none

/-- Monotonicity relation between states `s` and `s'` across activations of `fsfe`: every
submitted input is write-once immutable, and `delivered` and `aborted` are sticky. -/
structure SFEState.Monotone {n : ℕ} {In : Type} (s s' : SFEState n In) : Prop where
  /-- Once set, party `i`'s input cannot change. -/
  inputs_lock : ∀ i v, s.inputs i = some v → s'.inputs i = some v
  /-- Once delivered, party `i`'s output remains delivered. -/
  delivered_mono : ∀ i, s.delivered i = true → s'.delivered i = true
  /-- Once aborted, the session remains aborted. -/
  aborted_mono : s.aborted = true → s'.aborted = true

/-! ### Ideal `n`-party secure function evaluation with abort `fsfe` -/

/-- The ideal `n`-party secure function evaluation functionality with abort
$\mathcal{F}_{\mathrm{SFE}}$ ([Canetti2020]; motivated by [BonehShoup2023], Ch. 23, locators not
verified from PDF) for a deterministic
function `f : (Fin n → In) → (Fin n → Out)`:
- Each party `i : Fin n` submits `input val` once (subsequent inputs are ignored) and polls `query`
  to read its output once released (`some (.output (f x i))`), or `some .aborted` if aborted before
  its output was delivered.
- Backdoor `query` returns `SFEStatus n` (only arrival, delivery, and abort flags); `deliver i`
  releases party `i`'s output when all parties have submitted and no abort occurred; `abort` sets
  `aborted := true`. -/
@[expose] def fsfe {n : ℕ} {In Out : Type} (f : (Fin n → In) → (Fin n → Out)) :
    IdealFunctionality n (SFEInput In) (SFEOutput Out) (SFEBackdoor n) (SFEBackdoorReply n) where
  State := SFEState n In
  init _ _ := pure {}
  onInput i x s :=
    match x with
    | .input val =>
      if (s.inputs i).isNone then
        pure (none, { s with inputs := Function.update s.inputs i (some val) })
      else
        pure (none, s)
    | .query => pure (s.partyOutput f i, s)
  onBackdoor q s :=
    match q with
    | .query => pure (.status s.status, s)
    | .deliver i =>
      if s.allSubmitted && !s.aborted then
        pure (.ack, { s with delivered := Function.update s.delivered i true })
      else
        pure (.ack, s)
    | .abort => pure (.ack, { s with aborted := true })

/-! ### Call-budget bounds and multi-session compatibility -/

/-- `fsfe f` is deterministic and makes zero oracle calls per activation. -/
theorem fsfe_isBounded {n : ℕ} {In Out : Type} (f : (Fin n → In) → (Fin n → Out))
    (κ : ℕ) (C : Finset (Fin n)) : ((fsfe f).toProtocol κ C).IsBounded 0 := by
  refine ⟨OracleComp.IsCostBounded.pure _ 0, fun q s => ?_⟩
  rcases q with ⟨i, x⟩ | bq
  · cases x
    · by_cases hi : (s.inputs i).isNone <;>
        simp only [IdealFunctionality.toProtocol, fsfe, StateT.run, hi, ↓reduceIte,
          ProbOracleComp.sample_pure] <;>
        exact OracleComp.IsCostBounded.pure _ 0
    · simp only [IdealFunctionality.toProtocol, fsfe, StateT.run, ProbOracleComp.sample_pure]
      exact OracleComp.IsCostBounded.pure _ 0
  · cases bq
    · simp only [IdealFunctionality.toProtocol, fsfe, StateT.run, ProbOracleComp.sample_pure]
      exact OracleComp.IsCostBounded.pure _ 0
    · by_cases hd : (s.allSubmitted && !s.aborted) <;>
        simp only [IdealFunctionality.toProtocol, fsfe, StateT.run, hd, ↓reduceIte,
          ProbOracleComp.sample_pure] <;>
        exact OracleComp.IsCostBounded.pure _ 0
    · simp only [IdealFunctionality.toProtocol, fsfe, StateT.run, ProbOracleComp.sample_pure]
      exact OracleComp.IsCostBounded.pure _ 0

/-- `fsfe f` has polynomial call budget `0`. -/
theorem fsfe_polyBounded {n : ℕ} {In Out : Type} (f : (Fin n → In) → (Fin n → Out)) :
    (fsfe f).toProtocol.PolyBounded 0 := fun κ C => by
  rw [Polynomial.eval_zero]
  exact fsfe_isBounded f κ C

/-- Routing static corruptions around `fsfe f` still makes zero oracle calls per activation. -/
theorem corruptRouter_fsfe_isBounded {n : ℕ} {In Out : Type} (f : (Fin n → In) → (Fin n → Out))
    (κ : ℕ) (C : Finset (Fin n)) :
    (corruptRouter C ((fsfe f).toProtocol κ C)).IsBounded 0 :=
  corruptRouter_isBounded C ((fsfe f).toProtocol κ C) (fsfe_isBounded f κ C)

/-- The lazy multi-session extension `(fsfe f).multiSession SSID` has polynomial call budget `0`. -/
theorem fsfe_multiSession_polyBounded {n : ℕ} {In Out : Type}
    (f : (Fin n → In) → (Fin n → Out)) (SSID : Type) [DecidableEq SSID] :
    ((fsfe f).multiSession SSID).toProtocol.PolyBounded 0 :=
  multiSession_polyBounded_of_zero (fsfe f)
    (fun _ _ => OracleComp.IsCostBounded.pure _ 0)
    (fun i x s => by
      cases x <;> dsimp only [fsfe, StateT.run]
      · split_ifs <;> exact OracleComp.IsCostBounded.pure _ 0
      · exact OracleComp.IsCostBounded.pure _ 0)
    (fun q s => by
      cases q <;> dsimp only [fsfe, StateT.run]
      · exact OracleComp.IsCostBounded.pure _ 0
      · split_ifs <;> exact OracleComp.IsCostBounded.pure _ 0
      · exact OracleComp.IsCostBounded.pure _ 0)
    SSID

/-! ### State invariants and write-once input lock -/

theorem SFEState.Monotone.refl {n : ℕ} {In : Type} (s : SFEState n In) : SFEState.Monotone s s :=
  ⟨fun _ _ h => h, fun _ h => h, fun h => h⟩

theorem SFEState.Monotone.trans {n : ℕ} {In : Type} {a b c : SFEState n In}
    (hab : SFEState.Monotone a b) (hbc : SFEState.Monotone b c) : SFEState.Monotone a c where
  inputs_lock i v h := hbc.inputs_lock i v (hab.inputs_lock i v h)
  delivered_mono i h := hbc.delivered_mono i (hab.delivered_mono i h)
  aborted_mono h := hbc.aborted_mono (hab.aborted_mono h)

private theorem fsfe_single_step_monotone {n : ℕ} {In Out : Type}
    (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ) (C : Finset (Fin n))
    (q₀ : (Fin n × SFEInput In) ⊕ SFEBackdoor n) (s : SFEState n In)
    (r : protocolSpec n (SFEInput In) (SFEOutput Out) (SFEBackdoor n)
      (SFEBackdoorReply n) q₀ × SFEState n In)
    (hr : r ∈ (Machine.closeEval (((fsfe f).toProtocol κ C).handle q₀ |>.run s)).support) :
    SFEState.Monotone s r.2 := by
  rcases q₀ with ⟨i, x⟩ | bq
  · cases x with
    | input val =>
      dsimp only [IdealFunctionality.toProtocol, fsfe, StateT.run] at hr
      split_ifs at hr with hi
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure, PMF.mem_support_pure_iff] at hr
        subst hr
        refine ⟨fun j v hj => ?_, fun _ h => h, fun h => h⟩
        by_cases hji : j = i
        · subst hji
          rw [hj] at hi
          cases hi
        · dsimp only
          rw [Function.update_of_ne hji]
          exact hj
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure, PMF.mem_support_pure_iff] at hr
        subst hr; exact SFEState.Monotone.refl s
    | query =>
      dsimp only [IdealFunctionality.toProtocol, fsfe, StateT.run] at hr
      erw [ProbOracleComp.sample_pure, Machine.closeEval_pure, PMF.mem_support_pure_iff] at hr
      subst hr; exact SFEState.Monotone.refl s
  · cases bq with
    | query =>
      dsimp only [IdealFunctionality.toProtocol, fsfe, StateT.run] at hr
      erw [ProbOracleComp.sample_pure, Machine.closeEval_pure, PMF.mem_support_pure_iff] at hr
      subst hr; exact SFEState.Monotone.refl s
    | deliver i =>
      dsimp only [IdealFunctionality.toProtocol, fsfe, StateT.run] at hr
      split_ifs at hr with hd
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure, PMF.mem_support_pure_iff] at hr
        subst hr
        refine ⟨fun _ _ h => h, fun j hj => ?_, fun h => h⟩
        by_cases hji : j = i
        · subst hji; simp [Function.update_self]
        · dsimp only; rw [Function.update_of_ne hji]; exact hj
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure, PMF.mem_support_pure_iff] at hr
        subst hr; exact SFEState.Monotone.refl s
    | abort =>
      dsimp only [IdealFunctionality.toProtocol, fsfe, StateT.run] at hr
      erw [ProbOracleComp.sample_pure, Machine.closeEval_pure, PMF.mem_support_pure_iff] at hr
      subst hr
      exact ⟨fun _ _ h => h, fun _ h => h, fun _ => rfl⟩

/-- **Write-once input lock and delivery/abort monotonicity:** across any program run against
`corruptRouter C ((fsfe f).toProtocol κ C)`, every reachable final state satisfies
`SFEState.Monotone` relative to the starting state `s`. -/
theorem SFEState.monotone_of_mem_support_runFrom {n : ℕ} {In Out α : Type}
    (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ) (C : Finset (Fin n))
    (prog : ProbOracleComp
      (protocolSpec n (SFEInput In) (SFEOutput Out) (RoutedNetQ n (SFEInput In) (SFEBackdoor n))
        (RoutedNetR (SFEOutput Out) (SFEBackdoorReply n))) α)
    (s : SFEState n In) {x : α × SFEState n In}
    (hx : x ∈ (Machine.closeEval
      ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom prog s)).support) :
    SFEState.Monotone s x.2 :=
  corruptRouter_invariant_of_mem_support_runFrom C ((fsfe f).toProtocol κ C)
    SFEState.Monotone SFEState.Monotone.refl (fun hab hbc => hab.trans hbc)
    (fsfe_single_step_monotone f κ C) prog s hx

/-! ### Honest evaluation agreement and abort correctness -/

/-- Helper environment prefix submitting the first `k ≤ n` inputs of `x` to `fsfe`. -/
@[expose] def submitSFEPrefix {n : ℕ} {In Out AdvQ AdvR : Type} (x : Fin n → In) :
    (k : ℕ) → k ≤ n →
    ProbOracleComp (execSpec n (SFEInput In) (SFEOutput Out) AdvQ AdvR) Unit
  | 0, _ => pure ()
  | k + 1, hk => do
    submitSFEPrefix x k (Nat.le_of_succ_le hk)
    let _ ← ProbOracleComp.query
      (spec := execSpec n (SFEInput In) (SFEOutput Out) AdvQ AdvR)
      (Sum.inl (⟨k, hk⟩, .input (x ⟨k, hk⟩)))
    return ()

/-- Honest-execution environment (`C = ∅`) for `fsfe f`: all `n` parties submit `x`, the backdoor
releases output to party `target`, and `target` polls `some (.output (f x target))`. -/
@[expose] def honestSFEEnv {n : ℕ} {In Out : Type} [DecidableEq Out]
    (f : (Fin n → In) → (Fin n → Out)) (x : Fin n → In) (target : Fin n) :
    Environment n (SFEInput In) (SFEOutput Out)
      (RoutedNetQ n (SFEInput In) (SFEBackdoor n))
      (RoutedNetR (SFEOutput Out) (SFEBackdoorReply n)) := fun _ _ => do
  submitSFEPrefix x n (le_refl n)
  let _ ← ProbOracleComp.query
    (spec := execSpec n (SFEInput In) (SFEOutput Out) _ _) (Sum.inr (.inr (.deliver target)))
  let out ← ProbOracleComp.query
    (spec := execSpec n (SFEInput In) (SFEOutput Out) _ _) (Sum.inl (target, .query))
  return decide (out = some (.output (f x target)))

/-- Abort-test environment (`C = ∅`) for `fsfe f`: all `n` parties submit `x`, the backdoor issues
`abort`, and `target` polls `some .aborted`. -/
@[expose] def abortSFEEnv {n : ℕ} {In Out : Type} (x : Fin n → In) (target : Fin n) :
    Environment n (SFEInput In) (SFEOutput Out)
      (RoutedNetQ n (SFEInput In) (SFEBackdoor n))
      (RoutedNetR (SFEOutput Out) (SFEBackdoorReply n)) := fun _ _ => do
  submitSFEPrefix x n (le_refl n)
  let _ ← ProbOracleComp.query
    (spec := execSpec n (SFEInput In) (SFEOutput Out) _ _) (Sum.inr (.inr .abort))
  let out ← ProbOracleComp.query
    (spec := execSpec n (SFEInput In) (SFEOutput Out) _ _) (Sum.inl (target, .query))
  return match out with | some .aborted => true | _ => false

private theorem runFrom_submitSFEPrefix {n : ℕ} {In Out : Type}
    (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ) (x : Fin n → In) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (corruptRouter ∅ ((fsfe f).toProtocol κ ∅)).runFrom (submitSFEPrefix x k hk) {} =
        pure ((), { inputs := fun i => if i.val < k then some (x i) else none,
                    delivered := fun _ => false, aborted := false })
  | 0, _ => by
    dsimp only [submitSFEPrefix]
    erw [Machine.runFrom_pure]
    simp only [Nat.not_lt_zero, ↓reduceIte]
  | k + 1, hk => by
    dsimp only [submitSFEPrefix]
    erw [Machine.runFrom_bind, runFrom_submitSFEPrefix f κ x k (Nat.le_of_succ_le hk), pure_bind,
      Machine.runFrom_bind, Machine.runFrom_query]
    have hnone :
        ((if (⟨k, hk⟩ : Fin n).val < k then some (x ⟨k, hk⟩) else none) : Option In).isNone =
          true := by
      simp
    simp only [corruptRouter, IdealFunctionality.toProtocol, fsfe, Finset.notMem_empty, ↓reduceIte,
      StateT.run, hnone, ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_pure]
    refine congrArg (fun fn => pure ((), ({ inputs := fn } : SFEState n In)))
      (funext fun j => ?_)
    by_cases hjk : j = ⟨k, hk⟩
    · subst hjk
      simp [Function.update_self]
    · have hval : j.val ≠ k := fun h => hjk (Fin.ext h)
      rw [Function.update_of_ne hjk]
      by_cases hlt : j.val < k
      · simp only [hlt, Nat.lt_succ_iff_lt_or_eq, true_or, ↓reduceIte]
      · simp only [hlt, Nat.lt_succ_iff_lt_or_eq, hval, or_self, ↓reduceIte]

/-- **Honest evaluation agreement of `fsfe`:** when all parties submit `x` and the backdoor
delivers to `target` without aborting, `target` observes `some (.output (f x target))` with
probability `1`. -/
theorem eval_exec_honestSFEEnv {n : ℕ} {In Out : Type} [DecidableEq Out]
    (f : (Fin n → In) → (Fin n → Out)) (x : Fin n → In) (target : Fin n)
    (κ : ℕ) (z : List Bool) :
    (exec (fsfe f).toProtocol (dummyAdversary n _ _) ∅ (honestSFEEnv f x target) κ z).eval =
      PMF.pure true := by
  rw [exec_dummyAdversary]
  simp only [Machine.run, Machine.link, honestSFEEnv, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.runFrom_pure, Machine.closeProgram_bind, Machine.closeProgram_map,
    Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  have hinit : (corruptRouter (∅ : Finset (Fin n)) ((fsfe f).toProtocol κ ∅)).init =
      (pure ({} : SFEState n In) :
        ProbComp (corruptRouter (∅ : Finset (Fin n)) ((fsfe f).toProtocol κ ∅)).State) := rfl
  have hinp : (fun i : Fin n => if i.val < n then some (x i) else none) =
      fun i => some (x i) := funext fun i => by simp [i.isLt]
  let sAll : SFEState n In := { inputs := fun i => some (x i) }
  have hall : sAll.allSubmitted = true := by simp [sAll, SFEState.allSubmitted]
  have heval : sAll.eval? f = some (f x) := by simp [sAll, SFEState.eval?]
  erw [hinit, ProbOracleComp.sample_pure, Machine.closeProgram_pure, ProbComp.eval_pure,
    PMF.pure_bind, runFrom_submitSFEPrefix f κ x n (le_refl n), Machine.closeProgram_pure,
    ProbComp.eval_pure, PMF.pure_bind, hinp]
  simp only [corruptRouter, IdealFunctionality.toProtocol, fsfe, Finset.notMem_empty, ↓reduceIte,
    StateT.run, Functor.map, StateT.map]
  erw [show sAll.allSubmitted = true from hall]
  simp only [Bool.not_false, Bool.and_self, ↓reduceIte, ProbOracleComp.sample_pure, pure_bind,
    Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind, SFEState.partyOutput,
    Function.update_self]
  erw [heval]
  simp only [Option.map_some, decide_true, PMF.pure_map]

/-- **Abort correctness of `fsfe`:** when all parties submit `x` and the backdoor aborts before
delivering to `target`, `target` observes `some .aborted` with probability `1`. -/
theorem eval_exec_abortSFEEnv {n : ℕ} {In Out : Type}
    (f : (Fin n → In) → (Fin n → Out)) (x : Fin n → In) (target : Fin n)
    (κ : ℕ) (z : List Bool) :
    (exec (fsfe f).toProtocol (dummyAdversary n _ _) ∅ (abortSFEEnv x target) κ z).eval =
      PMF.pure true := by
  rw [exec_dummyAdversary]
  simp only [Machine.run, Machine.link, abortSFEEnv, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.runFrom_pure, Machine.closeProgram_bind, Machine.closeProgram_map,
    Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  have hinit : (corruptRouter (∅ : Finset (Fin n)) ((fsfe f).toProtocol κ ∅)).init =
      (pure ({} : SFEState n In) :
        ProbComp (corruptRouter (∅ : Finset (Fin n)) ((fsfe f).toProtocol κ ∅)).State) := rfl
  erw [hinit, ProbOracleComp.sample_pure, Machine.closeProgram_pure, ProbComp.eval_pure,
    PMF.pure_bind, runFrom_submitSFEPrefix f κ x n (le_refl n), Machine.closeProgram_pure,
    ProbComp.eval_pure, PMF.pure_bind]
  simp only [corruptRouter, IdealFunctionality.toProtocol, fsfe, Finset.notMem_empty, ↓reduceIte,
    StateT.run, Functor.map, StateT.map, ProbOracleComp.sample_pure, pure_bind,
    Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind, SFEState.partyOutput,
    Bool.false_eq_true, ↓reduceIte, PMF.pure_map]

/-! ### Honest-input privacy -/

/-- State equivalence for post-output honest-input privacy of `fsfe f` under static corruption set
`C`: corrupted inputs match, all arrival/delivery/abort flags match, and for every pair of full
input vectors extending `s₁` and `s₂` and agreeing on `C`, `f` yields the same outputs on `C`. -/
structure SFECorruptEquiv {n : ℕ} {In Out : Type} (C : Finset (Fin n))
    (f : (Fin n → In) → (Fin n → Out)) (s₁ s₂ : SFEState n In) : Prop where
  /-- Corrupted parties' submitted inputs agree. -/
  inputs_corrupt : ∀ i ∈ C, s₁.inputs i = s₂.inputs i
  /-- All parties have the same input-arrival status. -/
  submitted_eq : ∀ i, (s₁.inputs i).isSome = (s₂.inputs i).isSome
  /-- Output delivery flags agree. -/
  delivered_eq : s₁.delivered = s₂.delivered
  /-- Abort flags agree. -/
  aborted_eq : s₁.aborted = s₂.aborted
  /-- All completions extending `s₁` and `s₂` and agreeing on `C` produce identical `f`-outputs
  on `C`. -/
  outputs_corrupt : ∀ (x₁ x₂ : Fin n → In),
    (∀ j v, s₁.inputs j = some v → x₁ j = v) →
    (∀ j v, s₂.inputs j = some v → x₂ j = v) →
    (∀ j ∈ C, x₁ j = x₂ j) →
    ∀ i ∈ C, f x₁ i = f x₂ i

/-- State equivalence for pre-output honest-input privacy of `fsfe f` under static corruption set
`C`: corrupted inputs, arrival flags, honest-party delivery flags, and abort flags match, while
no corrupted party has received its output yet. -/
structure SFEPreOutputEquiv {n : ℕ} {In : Type} (C : Finset (Fin n))
    (s₁ s₂ : SFEState n In) : Prop where
  /-- Corrupted parties' submitted inputs agree. -/
  inputs_corrupt : ∀ i ∈ C, s₁.inputs i = s₂.inputs i
  /-- All parties have the same input-arrival status. -/
  submitted_eq : ∀ i, (s₁.inputs i).isSome = (s₂.inputs i).isSome
  /-- No corrupted party has had its output delivered in `s₁`. -/
  corrupt_undelivered₁ : ∀ i ∈ C, s₁.delivered i = false
  /-- No corrupted party has had its output delivered in `s₂`. -/
  corrupt_undelivered₂ : ∀ i ∈ C, s₂.delivered i = false
  /-- Delivery flags on honest parties match. -/
  honest_delivered_eq : ∀ i ∉ C, s₁.delivered i = s₂.delivered i
  /-- Abort flags agree. -/
  aborted_eq : s₁.aborted = s₂.aborted

private theorem sfeState_allSubmitted_eq_of_submitted_eq {n : ℕ} {In : Type}
    {s₁ s₂ : SFEState n In} (hsub : ∀ i, (s₁.inputs i).isSome = (s₂.inputs i).isSome) :
    s₁.allSubmitted = s₂.allSubmitted := by
  simp [SFEState.allSubmitted, hsub]

private theorem sfeState_status_eq_of_flags {n : ℕ} {In : Type} {s₁ s₂ : SFEState n In}
    (hsub : ∀ i, (s₁.inputs i).isSome = (s₂.inputs i).isSome)
    (hdel : s₁.delivered = s₂.delivered) (hab : s₁.aborted = s₂.aborted) :
    s₁.status = s₂.status := by
  simp only [SFEState.status, hdel, hab]
  congr 1
  funext i
  exact hsub i

private theorem sfeState_partyOutput_eq_of_equiv {n : ℕ} {In Out : Type}
    {C : Finset (Fin n)} {f : (Fin n → In) → (Fin n → Out)}
    {s₁ s₂ : SFEState n In} (h : SFECorruptEquiv C f s₁ s₂) {i : Fin n} (hi : i ∈ C) :
    s₁.partyOutput f i = s₂.partyOutput f i := by
  simp only [SFEState.partyOutput, h.delivered_eq, h.aborted_eq]
  split_ifs with hdel hab
  · by_cases hs₁ : ∀ j : Fin n, (s₁.inputs j).isSome = true
    · have hs₂ : ∀ j : Fin n, (s₂.inputs j).isSome = true := fun j =>
        (h.submitted_eq j) ▸ hs₁ j
      have hx₁ : ∀ j v (hj' : (s₁.inputs j).isSome = true),
          s₁.inputs j = some v → (s₁.inputs j).get hj' = v := fun j v hj' hj => by
        simp [hj]
      have hx₂ : ∀ j v (hj' : (s₂.inputs j).isSome = true),
          s₂.inputs j = some v → (s₂.inputs j).get hj' = v := fun j v hj' hj => by
        simp [hj]
      have hxC : ∀ j ∈ C, ∀ (hj₁ : (s₁.inputs j).isSome = true)
          (hj₂ : (s₂.inputs j).isSome = true),
          (s₁.inputs j).get hj₁ = (s₂.inputs j).get hj₂ := fun j hj hj₁ hj₂ => by
        have hin := h.inputs_corrupt j hj
        congr 1
      simp only [SFEState.eval?, eq_true hs₁, eq_true hs₂, ↓reduceDIte, Option.map_some]
      congr 2
      exact h.outputs_corrupt _ _ (fun j v => hx₁ j v _) (fun j v => hx₂ j v _)
        (fun j hj => hxC j hj _ _) i hi
    · have hns₂ : ¬ ∀ j : Fin n, (s₂.inputs j).isSome = true := fun h2 =>
        hs₁ fun j => (h.submitted_eq j).symm ▸ h2 j
      simp only [SFEState.eval?, eq_false hs₁, eq_false hns₂, ↓reduceDIte, Option.map_none]
  · rfl
  · rfl

private theorem eval_runFrom_fsfe_corrupt_invariant {n : ℕ} {In Out α : Type}
    (C : Finset (Fin n)) (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ)
    (Inv : RoutedNetQ n (SFEInput In) (SFEBackdoor n) → Prop)
    (R : SFEState n In → SFEState n In → Prop)
    (hstep : ∀ q s₁ s₂, Inv q → R s₁ s₂ →
      ∃ r s₁' s₂',
        ((corruptRouter C ((fsfe f).toProtocol κ C)).handle (.inr q)).run s₁ =
          pure (r, s₁') ∧
        ((corruptRouter C ((fsfe f).toProtocol κ C)).handle (.inr q)).run s₂ =
          pure (r, s₂') ∧
        R s₁' s₂')
    (program : ProbOracleComp
      (netSpec (RoutedNetQ n (SFEInput In) (SFEBackdoor n))
        (RoutedNetR (SFEOutput Out) (SFEBackdoorReply n))) α)
    (hprog : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) program)
    {s₁ s₂ : SFEState n In} (hR : R s₁ s₂) :
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom (liftNet program) s₁)).eval =
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom (liftNet program) s₂)).eval := by
  let M := corruptRouter C ((fsfe f).toProtocol κ C)
  have hfst : ∀ {s₁ s₂ : SFEState n In}, R s₁ s₂ →
      Prod.fst <$> M.runFrom (liftNet program) s₁ =
      Prod.fst <$> M.runFrom (liftNet program) s₂ := by
    induction program using OracleComp.induction with
    | pure a =>
      intro s₁ s₂ _; rfl
    | query_bind q cont ih =>
      intro s₁ s₂ hR'
      have hq := OracleComp.QueriesSatisfy.liftBind_iff.mp hprog
      rw [PFunctor.FreeM.bind_eq_bind]
      dsimp only [liftNet]
      rcases q with k | nq
      · rw [Machine.liftRightProgram_bind]
        have hs : Machine.liftRightProgram (partySpec n (SFEInput In) (SFEOutput Out))
            (OracleComp.query (spec := probOracleSpec
              (netSpec (RoutedNetQ n (SFEInput In) (SFEBackdoor n))
                (RoutedNetR (SFEOutput Out) (SFEBackdoorReply n)))) (Sum.inl k)) =
            ProbOracleComp.sample (ProbComp.unifFin k) := by
          rw [← Machine.liftRightProgram_sample (partySpec n (SFEInput In) (SFEOutput Out))]
          rfl
        erw [Machine.runFrom_bind, hs, Machine.runFrom_sample, bind_map_left, map_bind]
        exact bind_congr fun c => ih c (hq.2 c) hR'
      · obtain ⟨r, s₁', s₂', hr₁, hr₂, hR''⟩ := hstep nq s₁ s₂ hq.1 hR'
        have hrun_nq : ∀ (s : SFEState n In),
            M.runFrom (Machine.liftRightProgram (partySpec n (SFEInput In) (SFEOutput Out))
              (OracleComp.query (spec := probOracleSpec
                (netSpec (RoutedNetQ n (SFEInput In) (SFEBackdoor n))
                  (RoutedNetR (SFEOutput Out) (SFEBackdoorReply n)))) (Sum.inr nq) >>= cont))
              s =
            ((corruptRouter C ((fsfe f).toProtocol κ C)).handle (.inr nq)).run s >>= fun x =>
              M.runFrom (liftNet (cont x.1)) x.2 := fun s => by
          rw [Machine.liftRightProgram_bind]
          erw [Machine.runFrom_bind, Machine.liftRightProgram_query, Machine.runFrom_query]
        erw [hrun_nq s₁, hrun_nq s₂, hr₁, hr₂, pure_bind, pure_bind]
        exact ih r (hq.2 r) hR''
  have hclose := congrArg (fun p => (Machine.closeProgram p).eval) (hfst hR)
  simpa only [Machine.closeProgram_map] using hclose

private theorem sfeCorrupt_input_branch {n : ℕ} {In Out : Type} {C : Finset (Fin n)}
    (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ) {i : Fin n} (hi : i ∈ C) (val : In)
    {s₁ s₂ : SFEState n In} (h_corrupt : ∀ j ∈ C, s₁.inputs j = s₂.inputs j)
    (h_sub : ∀ j, (s₁.inputs j).isSome = (s₂.inputs j).isSome)
    (P : SFEState n In → SFEState n In → Prop) (h_refl : P s₁ s₂)
    (h_upd : (s₁.inputs i).isNone → (s₂.inputs i).isNone →
      let s₁' : SFEState n In := { s₁ with inputs := Function.update s₁.inputs i (some val) }
      let s₂' : SFEState n In := { s₂ with inputs := Function.update s₂.inputs i (some val) }
      (∀ j ∈ C, s₁'.inputs j = s₂'.inputs j) →
      (∀ j, (s₁'.inputs j).isSome = (s₂'.inputs j).isSome) →
      P s₁' s₂') :
    ∃ r : RoutedNetR (SFEOutput Out) (SFEBackdoorReply n),
      ∃ s₁' s₂' : SFEState n In,
        ((corruptRouter C ((fsfe f).toProtocol κ C)).handle
          (.inr (.inl (i, .input val)))).run s₁ = pure (r, s₁') ∧
        ((corruptRouter C ((fsfe f).toProtocol κ C)).handle
          (.inr (.inl (i, .input val)))).run s₂ = pure (r, s₂') ∧
        P s₁' s₂' := by
  have hnone : (s₁.inputs i).isNone = (s₂.inputs i).isNone := by rw [h_corrupt i hi]
  by_cases hn : (s₁.inputs i).isNone
  · have hn₂ : (s₂.inputs i).isNone := hnone ▸ hn
    refine ⟨.inl none, { s₁ with inputs := Function.update s₁.inputs i (some val) },
      { s₂ with inputs := Function.update s₂.inputs i (some val) }, ?_, ?_, h_upd hn hn₂ ?_ ?_⟩
    · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
      simp only [hi, ↓reduceIte, StateT.run, Functor.map, StateT.map, hn,
        ProbOracleComp.sample_pure, pure_bind]
    · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
      simp only [hi, ↓reduceIte, StateT.run, Functor.map, StateT.map, hn₂,
        ProbOracleComp.sample_pure, pure_bind]
    · intro j hj
      by_cases hji : j = i
      · subst hji; simp [Function.update_self]
      · dsimp only
        rw [Function.update_of_ne hji, Function.update_of_ne hji]
        exact h_corrupt j hj
    · intro j
      by_cases hji : j = i
      · subst hji; simp [Function.update_self]
      · dsimp only
        rw [Function.update_of_ne hji, Function.update_of_ne hji]
        exact h_sub j
  · have hn₂ : (s₂.inputs i).isNone = false := by
      rw [← hnone]; exact Bool.eq_false_iff.mpr hn
    refine ⟨.inl none, s₁, s₂, ?_, ?_, h_refl⟩
    · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
      simp only [hi, ↓reduceIte, StateT.run, Functor.map, StateT.map, hn, Bool.false_eq_true,
        ProbOracleComp.sample_pure, pure_bind]
    · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
      simp only [hi, ↓reduceIte, StateT.run, Functor.map, StateT.map, hn₂, Bool.false_eq_true,
        ProbOracleComp.sample_pure, pure_bind]

private theorem sfeCorruptEquiv_step {n : ℕ} {In Out : Type}
    {C : Finset (Fin n)} (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ)
    (q : RoutedNetQ n (SFEInput In) (SFEBackdoor n))
    {s₁ s₂ : SFEState n In} (h : SFECorruptEquiv C f s₁ s₂) :
    ∃ r : RoutedNetR (SFEOutput Out) (SFEBackdoorReply n),
      ∃ s₁' s₂' : SFEState n In,
        ((corruptRouter C ((fsfe f).toProtocol κ C)).handle (.inr q)).run s₁ = pure (r, s₁') ∧
        ((corruptRouter C ((fsfe f).toProtocol κ C)).handle (.inr q)).run s₂ = pure (r, s₂') ∧
        SFECorruptEquiv C f s₁' s₂' := by
  rcases q with ⟨i, inp⟩ | bq
  · by_cases hi : i ∈ C
    · cases inp with
      | input val =>
        refine sfeCorrupt_input_branch f κ hi val h.inputs_corrupt h.submitted_eq
          (SFECorruptEquiv C f) h fun hn₁ hn₂ h_corrupt h_sub => ?_
        refine ⟨h_corrupt, h_sub, h.delivered_eq, h.aborted_eq, fun x₁ x₂ hx₁ hx₂ hxC => ?_⟩
        refine h.outputs_corrupt x₁ x₂ ?_ ?_ hxC
        · intro j v hj
          by_cases hji : j = i
          · subst hji; rw [Option.isNone_iff_eq_none] at hn₁; rw [hn₁] at hj; cases hj
          · exact hx₁ j v (by simpa [Function.update_of_ne hji] using hj)
        · intro j v hj
          by_cases hji : j = i
          · subst hji; rw [Option.isNone_iff_eq_none] at hn₂; rw [hn₂] at hj; cases hj
          · exact hx₂ j v (by simpa [Function.update_of_ne hji] using hj)
      | query =>
        refine ⟨.inl (s₁.partyOutput f i), s₁, s₂, ?_, ?_, h⟩
        · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
          simp only [hi, ↓reduceIte, StateT.run, Functor.map, StateT.map,
            ProbOracleComp.sample_pure, pure_bind]
        · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
          simp only [hi, ↓reduceIte, StateT.run, Functor.map, StateT.map,
            ProbOracleComp.sample_pure, pure_bind, sfeState_partyOutput_eq_of_equiv h hi]
    · refine ⟨.inl none, s₁, s₂, ?_, ?_, h⟩
      · dsimp only [corruptRouter]; simp only [hi, ↓reduceIte, StateT.run]; rfl
      · dsimp only [corruptRouter]; simp only [hi, ↓reduceIte, StateT.run]; rfl
  · cases bq with
    | query =>
      refine ⟨.inr (.status s₁.status), s₁, s₂, ?_, ?_, h⟩
      · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
        simp only [StateT.run, Functor.map, StateT.map, ProbOracleComp.sample_pure, pure_bind]
      · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
        simp only [StateT.run, Functor.map, StateT.map, ProbOracleComp.sample_pure, pure_bind,
          sfeState_status_eq_of_flags h.submitted_eq h.delivered_eq h.aborted_eq]
    | deliver j =>
      have hall := sfeState_allSubmitted_eq_of_submitted_eq h.submitted_eq
      by_cases hd : (s₁.allSubmitted && !s₁.aborted)
      · have hd₂ : (s₂.allSubmitted && !s₂.aborted) = true := by
          rw [← hall, ← h.aborted_eq]; exact hd
        refine ⟨.inr .ack, { s₁ with delivered := Function.update s₁.delivered j true },
          { s₂ with delivered := Function.update s₂.delivered j true }, ?_, ?_, ?_⟩
        · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
          simp only [StateT.run, Functor.map, StateT.map, hd, ↓reduceIte,
            ProbOracleComp.sample_pure, pure_bind]
        · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
          simp only [StateT.run, Functor.map, StateT.map, hd₂, ↓reduceIte,
            ProbOracleComp.sample_pure, pure_bind]
        · exact ⟨h.inputs_corrupt, h.submitted_eq,
            congrArg (Function.update · j true) h.delivered_eq, h.aborted_eq, h.outputs_corrupt⟩
      · have hd₂ : (s₂.allSubmitted && !s₂.aborted) = false := by
          rw [← hall, ← h.aborted_eq]; exact Bool.eq_false_iff.mpr hd
        refine ⟨.inr .ack, s₁, s₂, ?_, ?_, h⟩
        · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
          simp only [StateT.run, Functor.map, StateT.map, hd, Bool.false_eq_true, ↓reduceIte,
            ProbOracleComp.sample_pure, pure_bind]
        · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
          simp only [StateT.run, Functor.map, StateT.map, hd₂, Bool.false_eq_true, ↓reduceIte,
            ProbOracleComp.sample_pure, pure_bind]
    | abort =>
      refine ⟨.inr .ack, { s₁ with aborted := true }, { s₂ with aborted := true }, ?_, ?_,
        ⟨h.inputs_corrupt, h.submitted_eq, h.delivered_eq, rfl, h.outputs_corrupt⟩⟩
      · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
        simp only [StateT.run, Functor.map, StateT.map, ProbOracleComp.sample_pure, pure_bind]
      · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
        simp only [StateT.run, Functor.map, StateT.map, ProbOracleComp.sample_pure, pure_bind]

/-- **Honest-input privacy (post-output):** for static corruption set `C`, any two states
`s₁, s₂` satisfying `SFECorruptEquiv C f s₁ s₂` produce identical distributions across every
network-port program `liftNet program` (including all corrupted-party inputs/queries and all
backdoor queries/deliveries/aborts). -/
theorem eval_runFrom_fsfe_corrupt_eq {n : ℕ} {In Out α : Type}
    (C : Finset (Fin n)) (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ)
    {s₁ s₂ : SFEState n In} (h : SFECorruptEquiv C f s₁ s₂)
    (program : ProbOracleComp
      (netSpec (RoutedNetQ n (SFEInput In) (SFEBackdoor n))
        (RoutedNetR (SFEOutput Out) (SFEBackdoorReply n))) α) :
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom (liftNet program) s₁)).eval =
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom (liftNet program) s₂)).eval :=
  eval_runFrom_fsfe_corrupt_invariant C f κ (fun _ => True) (SFECorruptEquiv C f)
    (fun q _ _ _ hR => sfeCorruptEquiv_step f κ q hR) program
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) program) h

/-- **Honest-input privacy (input-vector form):** two full input vectors `x₁, x₂ : Fin n → In`
agreeing on `C` and producing identical `f`-outputs on `C` induce identical `C`-and-backdoor
behavior across every network-port program `liftNet program`. -/
theorem eval_runFrom_fsfe_corrupt_inputs_eq {n : ℕ} {In Out α : Type}
    (C : Finset (Fin n)) (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ)
    {x₁ x₂ : Fin n → In} (hxC : ∀ i ∈ C, x₁ i = x₂ i) (hfC : ∀ i ∈ C, f x₁ i = f x₂ i)
    (delivered : Fin n → Bool) (aborted : Bool)
    (program : ProbOracleComp
      (netSpec (RoutedNetQ n (SFEInput In) (SFEBackdoor n))
        (RoutedNetR (SFEOutput Out) (SFEBackdoorReply n))) α) :
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom (liftNet program)
        { inputs := fun i => some (x₁ i), delivered := delivered, aborted := aborted })).eval =
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom (liftNet program)
          { inputs := fun i => some (x₂ i),
            delivered := delivered, aborted := aborted })).eval := by
  refine eval_runFrom_fsfe_corrupt_eq C f κ ?_ program
  refine ⟨fun i hi => by simp [hxC i hi], fun _ => rfl, rfl, rfl, fun y₁ y₂ hy₁ hy₂ _ i hi => ?_⟩
  have heq₁ : y₁ = x₁ := funext fun j => hy₁ j (x₁ j) rfl
  have heq₂ : y₂ = x₂ := funext fun j => hy₂ j (x₂ j) rfl
  subst heq₁ heq₂
  exact hfC i hi

private theorem sfePreOutputEquiv_step {n : ℕ} {In Out : Type}
    {C : Finset (Fin n)} (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ)
    (q : RoutedNetQ n (SFEInput In) (SFEBackdoor n))
    {s₁ s₂ : SFEState n In} (h : SFEPreOutputEquiv C s₁ s₂)
    (hq : match q with
      | .inr (.deliver i) => i ∈ C → s₁.allSubmitted = false
      | _ => True) :
    ∃ r : RoutedNetR (SFEOutput Out) (SFEBackdoorReply n),
      ∃ s₁' s₂' : SFEState n In,
        ((corruptRouter C ((fsfe f).toProtocol κ C)).handle (.inr q)).run s₁ = pure (r, s₁') ∧
        ((corruptRouter C ((fsfe f).toProtocol κ C)).handle (.inr q)).run s₂ = pure (r, s₂') ∧
        SFEPreOutputEquiv C s₁' s₂' ∧
        (∀ j ∉ C, s₁'.inputs j = s₁.inputs j) := by
  rcases q with ⟨i, inp⟩ | bq
  · by_cases hi : i ∈ C
    · cases inp with
      | input val =>
        refine sfeCorrupt_input_branch f κ hi val h.inputs_corrupt h.submitted_eq
          (fun s₁' s₂' => SFEPreOutputEquiv C s₁' s₂' ∧ ∀ j ∉ C, s₁'.inputs j = s₁.inputs j)
          ⟨h, fun _ _ => rfl⟩ fun _ _ h_corrupt h_sub => ?_
        refine ⟨⟨h_corrupt, h_sub, h.corrupt_undelivered₁, h.corrupt_undelivered₂,
          h.honest_delivered_eq, h.aborted_eq⟩, fun j hj => ?_⟩
        have hji : j ≠ i := fun hjeq => hj (hjeq.symm ▸ hi)
        dsimp only
        rw [Function.update_of_ne hji]
      | query =>
        have hd₁ := h.corrupt_undelivered₁ i hi
        have hd₂ := h.corrupt_undelivered₂ i hi
        have hout : s₁.partyOutput f i = s₂.partyOutput f i := by
          simp [SFEState.partyOutput, hd₁, hd₂, h.aborted_eq]
        refine ⟨.inl (s₁.partyOutput f i), s₁, s₂, ?_, ?_, h, fun _ _ => rfl⟩
        · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
          simp only [hi, ↓reduceIte, StateT.run, Functor.map, StateT.map,
            ProbOracleComp.sample_pure, pure_bind]
        · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
          simp only [hi, ↓reduceIte, StateT.run, Functor.map, StateT.map,
            ProbOracleComp.sample_pure, pure_bind, hout]
    · refine ⟨.inl none, s₁, s₂, ?_, ?_, h, fun _ _ => rfl⟩
      · dsimp only [corruptRouter]; simp only [hi, ↓reduceIte, StateT.run]; rfl
      · dsimp only [corruptRouter]; simp only [hi, ↓reduceIte, StateT.run]; rfl
  · cases bq with
    | query =>
      have hdel : s₁.delivered = s₂.delivered := funext fun j => by
        by_cases hj : j ∈ C
        · rw [h.corrupt_undelivered₁ j hj, h.corrupt_undelivered₂ j hj]
        · exact h.honest_delivered_eq j hj
      refine ⟨.inr (.status s₁.status), s₁, s₂, ?_, ?_, h, fun _ _ => rfl⟩
      · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
        simp only [StateT.run, Functor.map, StateT.map, ProbOracleComp.sample_pure, pure_bind]
      · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
        simp only [StateT.run, Functor.map, StateT.map, ProbOracleComp.sample_pure, pure_bind,
          sfeState_status_eq_of_flags h.submitted_eq hdel h.aborted_eq]
    | deliver j =>
      have hall := sfeState_allSubmitted_eq_of_submitted_eq h.submitted_eq
      by_cases hj : j ∈ C
      · have hnot := hq hj
        have hnot₂ : s₂.allSubmitted = false := hall ▸ hnot
        refine ⟨.inr .ack, s₁, s₂, ?_, ?_, h, fun _ _ => rfl⟩
        · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
          simp only [StateT.run, Functor.map, StateT.map, hnot, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, ProbOracleComp.sample_pure, pure_bind]
        · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
          simp only [StateT.run, Functor.map, StateT.map, hnot₂, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, ProbOracleComp.sample_pure, pure_bind]
      · by_cases hd : (s₁.allSubmitted && !s₁.aborted)
        · have hd₂ : (s₂.allSubmitted && !s₂.aborted) = true := by
            rw [← hall, ← h.aborted_eq]; exact hd
          refine ⟨.inr .ack, { s₁ with delivered := Function.update s₁.delivered j true },
            { s₂ with delivered := Function.update s₂.delivered j true }, ?_, ?_, ?_,
            fun _ _ => rfl⟩
          · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
            simp only [StateT.run, Functor.map, StateT.map, hd, ↓reduceIte,
              ProbOracleComp.sample_pure, pure_bind]
          · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
            simp only [StateT.run, Functor.map, StateT.map, hd₂, ↓reduceIte,
              ProbOracleComp.sample_pure, pure_bind]
          · refine ⟨h.inputs_corrupt, h.submitted_eq, ?_, ?_, fun k hk => ?_, h.aborted_eq⟩
            · intro k hk
              dsimp only
              rw [Function.update_of_ne (fun hkj => by subst hkj; exact hj hk)]
              exact h.corrupt_undelivered₁ k hk
            · intro k hk
              dsimp only
              rw [Function.update_of_ne (fun hkj => by subst hkj; exact hj hk)]
              exact h.corrupt_undelivered₂ k hk
            · by_cases hkj : k = j
              · subst hkj; simp [Function.update_self]
              · dsimp only
                rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
                exact h.honest_delivered_eq k hk
        · have hd₂ : (s₂.allSubmitted && !s₂.aborted) = false := by
            rw [← hall, ← h.aborted_eq]; exact Bool.eq_false_iff.mpr hd
          refine ⟨.inr .ack, s₁, s₂, ?_, ?_, h, fun _ _ => rfl⟩
          · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
            simp only [StateT.run, Functor.map, StateT.map, hd, Bool.false_eq_true, ↓reduceIte,
              ProbOracleComp.sample_pure, pure_bind]
          · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
            simp only [StateT.run, Functor.map, StateT.map, hd₂, Bool.false_eq_true, ↓reduceIte,
              ProbOracleComp.sample_pure, pure_bind]
    | abort =>
      refine ⟨.inr .ack, { s₁ with aborted := true }, { s₂ with aborted := true }, ?_, ?_,
        ⟨h.inputs_corrupt, h.submitted_eq, h.corrupt_undelivered₁, h.corrupt_undelivered₂,
          h.honest_delivered_eq, rfl⟩, fun _ _ => rfl⟩
      · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
        simp only [StateT.run, Functor.map, StateT.map, ProbOracleComp.sample_pure, pure_bind]
      · dsimp only [corruptRouter, IdealFunctionality.toProtocol, fsfe]
        simp only [StateT.run, Functor.map, StateT.map, ProbOracleComp.sample_pure, pure_bind]

/-- **Honest-input privacy (pre-all-submitted):** if at least one honest party `j ∉ C` has not
yet submitted an input (`s₁.inputs j = none`), and `s₁, s₂` match on `C`, arrival flags, and
undelivered/abort flags, then ANY network-port program `liftNet program` produces identical output
distributions on `s₁` and `s₂` regardless of honest inputs or `f`-outputs. -/
theorem eval_runFrom_fsfe_corrupt_preAllSubmitted_eq {n : ℕ} {In Out α : Type}
    (C : Finset (Fin n)) (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ)
    {s₁ s₂ : SFEState n In} (h : SFEPreOutputEquiv C s₁ s₂)
    (hhonest : ∃ j ∉ C, s₁.inputs j = none)
    (program : ProbOracleComp
      (netSpec (RoutedNetQ n (SFEInput In) (SFEBackdoor n))
        (RoutedNetR (SFEOutput Out) (SFEBackdoorReply n))) α) :
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom (liftNet program) s₁)).eval =
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom (liftNet program) s₂)).eval := by
  refine eval_runFrom_fsfe_corrupt_invariant C f κ (fun _ => True)
    (fun a b => SFEPreOutputEquiv C a b ∧ ∃ j ∉ C, a.inputs j = none)
    (fun q s₁' s₂' _ ⟨hR', j, hjC, hjnone⟩ => ?_) program
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) program)
    ⟨h, hhonest⟩
  have hnotAll : s₁'.allSubmitted = false := by
    simp only [SFEState.allSubmitted, decide_eq_false_iff_not, not_forall]
    exact ⟨j, by simp [hjnone]⟩
  have hq : match q with
      | .inr (.deliver i) => i ∈ C → s₁'.allSubmitted = false
      | _ => True := by
    cases q with
    | inl _ => trivial
    | inr bq => cases bq <;> first | trivial | exact fun _ => hnotAll
  obtain ⟨r, s₁'', s₂'', hr₁, hr₂, hR'', hkeep⟩ := sfePreOutputEquiv_step f κ q hR' hq
  exact ⟨r, s₁'', s₂'', hr₁, hr₂, hR'', j, hjC, (hkeep j hjC).trans hjnone⟩

/-- **Honest-input privacy (pre-output, even after all inputs arrive):** for any two states
`s₁, s₂` satisfying `SFEPreOutputEquiv C s₁ s₂` (including two full input vectors `x₁, x₂` agreeing
on `C` without requiring `f x₁ i = f x₂ i`), any network-port program `program` that does not
invoke `.deliver i` for `i ∈ C` produces identical output distributions on `s₁` and `s₂`. -/
theorem eval_runFrom_fsfe_corrupt_preDeliver_eq {n : ℕ} {In Out α : Type}
    (C : Finset (Fin n)) (f : (Fin n → In) → (Fin n → Out)) (κ : ℕ)
    {s₁ s₂ : SFEState n In} (h : SFEPreOutputEquiv C s₁ s₂)
    (program : ProbOracleComp
      (netSpec (RoutedNetQ n (SFEInput In) (SFEBackdoor n))
        (RoutedNetR (SFEOutput Out) (SFEBackdoorReply n))) α)
    (hnodel : OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => match q with
        | .inr (.deliver i) => i ∉ C
        | _ => True) program) :
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom (liftNet program) s₁)).eval =
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter C ((fsfe f).toProtocol κ C)).runFrom (liftNet program) s₂)).eval := by
  refine eval_runFrom_fsfe_corrupt_invariant C f κ
    (fun q => match q with | .inr (.deliver i) => i ∉ C | _ => True)
    (SFEPreOutputEquiv C) (fun q s₁' s₂' hq hR => ?_) program hnodel h
  obtain ⟨r, s₁', s₂', hr₁, hr₂, hR', _⟩ := sfePreOutputEquiv_step f κ q hR (by
    rcases q with ⟨_, _⟩ | bq
    · trivial
    · cases bq with
      | deliver i => intro hiC; exact absurd hiC hq
      | _ => trivial)
  exact ⟨r, s₁', s₂', hr₁, hr₂, hR'⟩

/-! ### Relationship between `fot` and 2-party `fsfe` -/

/-- The 2-party deterministic function for 1-out-of-2 oblivious transfer: sender `0` supplies
`OTMessages M` (receiving `Unit`), receiver `1` supplies `Bool` (receiving `msgs.select b`).
Malformed role inputs default to `.inl ()`. -/
@[expose] def otEvalFn (M : Type) (x : Fin 2 → OTMessages M ⊕ Bool) : Fin 2 → Unit ⊕ M :=
  fun i =>
    if i = 0 then .inl ()
    else
      match x 0, x 1 with
      | .inl msgs, .inr b => .inr (msgs.select b)
      | _, _ => .inl ()

/-- Concrete 2-party `fsfe` instantiation of 1-out-of-2 oblivious transfer. -/
@[expose] def otSFE (M : Type) :
    IdealFunctionality 2 (SFEInput (OTMessages M ⊕ Bool)) (SFEOutput (Unit ⊕ M))
      (SFEBackdoor 2) (SFEBackdoorReply 2) :=
  fsfe (otEvalFn M)

/-- Role-enforcing 2-party hybrid protocol adapting `otSFE M` to the `OTInput M` / `OTOutput M`
interface of `fot M`:
- Party `0` forwards `.send msgs` as `(0, .input (.inl msgs))` and returns `none`.
- Party `1` forwards `.choose b` as `(1, .input (.inr b))` (returning `none`) and `.query` as
  `(1, .query)` (mapping `.output (.inr m)` to `.delivered m` and `.aborted` to `.aborted`). -/
@[expose] def otInSFEHybrid (M : Type) :
    HybridProtocol 2 (OTInput M) (OTOutput M) Unit Unit
      (SFEInput (OTMessages M ⊕ Bool)) (SFEOutput (Unit ⊕ M)) := fun _ _ => {
  State := Unit
  init := pure ()
  handle q _ :=
    match q with
    | .inl (0, .send msgs) => do
      let _ ← ProbOracleComp.query
        (spec := partySpec 2 (SFEInput (OTMessages M ⊕ Bool)) (SFEOutput (Unit ⊕ M)))
        (0, .input (.inl msgs))
      return (none, ())
    | .inl (1, .choose b) => do
      let _ ← ProbOracleComp.query
        (spec := partySpec 2 (SFEInput (OTMessages M ⊕ Bool)) (SFEOutput (Unit ⊕ M)))
        (1, .input (.inr b))
      return (none, ())
    | .inl (1, .query) => do
      let out ← ProbOracleComp.query
        (spec := partySpec 2 (SFEInput (OTMessages M ⊕ Bool)) (SFEOutput (Unit ⊕ M)))
        (1, .query)
      let mapped : Option (OTOutput M) := match out with
        | some (.output (.inr m)) => some (.delivered m)
        | some .aborted => some .aborted
        | _ => none
      return (mapped, ())
    | .inl _ => pure (none, ())
    | .inr () => pure ((), ()) }

/-- `otInSFEHybrid M` makes at most `1` subroutine call per activation. -/
theorem otInSFEHybrid_polyBounded (M : Type) : (otInSFEHybrid M).PolyBounded 1 := fun _ _ => by
  rw [Polynomial.eval_one]
  refine ⟨OracleComp.IsCostBounded.pure _ 1, fun q _ => ?_⟩
  rcases q with ⟨i, x⟩ | ⟨⟩
  · fin_cases i <;> cases x <;>
      first
      | exact OracleComp.IsCostBounded.pure _ 1
      | exact ((OracleComp.IsCostBounded.query _).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0).mono (by simp)
  · exact OracleComp.IsCostBounded.pure _ 1

/-- Honest delivery environment (`C = ∅`) for `compose (otInSFEHybrid M) (otSFE M).toProtocol`. -/
@[expose] def honestOTInSFEEnv {M : Type} [DecidableEq M] (msgs : OTMessages M) (b : Bool) :
    Environment 2 (OTInput M) (OTOutput M)
      (RoutedNetQ 2 (OTInput M) (Unit ⊕ RoutedNetQ 2 (SFEInput (OTMessages M ⊕ Bool))
        (SFEBackdoor 2)))
      (RoutedNetR (OTOutput M) (Unit ⊕ RoutedNetR (SFEOutput (Unit ⊕ M)) (SFEBackdoorReply 2))) :=
  fun _ _ => do
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (0, .send msgs))
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (1, .choose b))
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inr (.inr (.inr (.inr (.deliver 1)))))
  let out ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (1, .query))
  return decide (out = some (.delivered (msgs.select b)))

/-- Abort environment (`C = ∅`) for `compose (otInSFEHybrid M) (otSFE M).toProtocol`. -/
@[expose] def abortOTInSFEEnv {M : Type} (msgs : OTMessages M) (b : Bool) :
    Environment 2 (OTInput M) (OTOutput M)
      (RoutedNetQ 2 (OTInput M) (Unit ⊕ RoutedNetQ 2 (SFEInput (OTMessages M ⊕ Bool))
        (SFEBackdoor 2)))
      (RoutedNetR (OTOutput M) (Unit ⊕ RoutedNetR (SFEOutput (Unit ⊕ M)) (SFEBackdoorReply 2))) :=
  fun _ _ => do
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (0, .send msgs))
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (1, .choose b))
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inr (.inr (.inr (.inr .abort))))
  let out ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (1, .query))
  return match out with | some .aborted => true | _ => false

/-- **Positive `fot` vs. 2-party `fsfe` correspondence (honest delivery):** running `otInSFEHybrid`
over `otSFE M` delivers `some (.delivered (msgs.select b))` to receiver `1` with probability `1`,
matching `eval_exec_honestOTEnv`. -/
theorem eval_exec_otInSFE_honestOT {M : Type} [DecidableEq M] (msgs : OTMessages M) (b : Bool)
    (κ : ℕ) (z : List Bool) :
    (exec (compose (otInSFEHybrid M) (otSFE M).toProtocol) (dummyAdversary 2 _ _) ∅
      (honestOTInSFEEnv msgs b) κ z).eval = PMF.pure true := by
  rw [exec_compose_dummy, exec_dummyAdversary]
  simp only [Machine.run, Machine.link, absorbHybrid, honestOTInSFEEnv, routeCorrupt,
    hybridWrap, otInSFEHybrid, Finset.notMem_empty, ↓reduceIte, StateT.run,
    Machine.runFrom_bind, Machine.runFrom_map, Machine.runFrom_query, Machine.runFrom_pure,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  have hinit : (corruptRouter (∅ : Finset (Fin 2)) ((otSFE M).toProtocol κ ∅)).init =
      (pure ({} : SFEState 2 (OTMessages M ⊕ Bool)) :
        ProbComp (corruptRouter (∅ : Finset (Fin 2)) ((otSFE M).toProtocol κ ∅)).State) := rfl
  erw [hinit, ProbOracleComp.sample_pure, Machine.closeProgram_pure, ProbComp.eval_pure,
    PMF.pure_bind]
  have hstep3 : ∀ {ι : Type} {spec : OracleSpec ι} {α β : Type} (f : α → β)
      (m : ProbOracleComp spec α) (s : Unit),
      (f <$> StateT.lift m) s = (fun a => (f a, s)) <$> m := by
    intro ι spec α β f m s
    change (f <$> StateT.lift m).run s = _
    rw [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map]
  have hstateMap : ∀ {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
      (f : α → β) (x : StateT σ m α) (s : σ),
      (f <$> x) s = Prod.map f id <$> x s := by
    intro σ m _ _ α β f x s
    change (f <$> x).run s = _
    exact StateT.run_map f x s
  simp only [corruptRouter, otSFE, IdealFunctionality.toProtocol, fsfe, Finset.notMem_empty,
    ↓reduceIte, StateT.run, hstep3, hstateMap, liftParty, OracleComp.interpret_bind,
    ProbOracleComp.interpret_query, OracleComp.interpret_pure, Option.isNone_none,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
    SFEState.allSubmitted, Fin.forall_fin_two, Function.update_self, Option.isSome_some,
    and_self, decide_true, Bool.not_false, Bool.and_self,
    ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_bind, Machine.runFrom_map,
    Machine.runFrom_query, Machine.runFrom_pure, Machine.closeProgram_bind,
    Machine.closeProgram_map, Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, PMF.pure_map, PMF.pure_bind, Prod.map, id_eq, SFEState.partyOutput,
    SFEState.eval?, ↓reduceDIte, otEvalFn, (by decide : ((1 : Fin 2) = 0) = false),
    Bool.false_eq_true, Option.get_some, Option.map_some, decide_true]

/-- **Positive `fot` vs. 2-party `fsfe` correspondence (abort):** running `otInSFEHybrid M` over
`otSFE M` returns `some .aborted` to receiver `1` on `.abort` with probability `1`, matching
`eval_exec_abortOTEnv`. -/
theorem eval_exec_otInSFE_abortOT {M : Type} (msgs : OTMessages M) (b : Bool)
    (κ : ℕ) (z : List Bool) :
    (exec (compose (otInSFEHybrid M) (otSFE M).toProtocol) (dummyAdversary 2 _ _) ∅
      (abortOTInSFEEnv msgs b) κ z).eval = PMF.pure true := by
  rw [exec_compose_dummy, exec_dummyAdversary]
  simp only [Machine.run, Machine.link, absorbHybrid, abortOTInSFEEnv, routeCorrupt,
    hybridWrap, otInSFEHybrid, Finset.notMem_empty, ↓reduceIte, StateT.run,
    Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
    Machine.closeProgram_bind, ProbComp.eval_bind]
  have hinit : (corruptRouter (∅ : Finset (Fin 2)) ((otSFE M).toProtocol κ ∅)).init =
      (pure ({} : SFEState 2 (OTMessages M ⊕ Bool)) :
        ProbComp (corruptRouter (∅ : Finset (Fin 2)) ((otSFE M).toProtocol κ ∅)).State) := rfl
  erw [hinit, ProbOracleComp.sample_pure, Machine.closeProgram_pure, ProbComp.eval_pure,
    PMF.pure_bind]
  simp only [corruptRouter, otSFE, IdealFunctionality.toProtocol, fsfe, StateT.run,
    ProbOracleComp.sample_pure, SFEState.partyOutput]
  rfl

/-- **Semantic difference 1 (sender abort visibility):** after an `.abort` on the backdoor, sender
`0` polling `.query` receives `some .aborted` in `otSFE M` (since every party of `fsfe` receives an
output or abort), whereas sender `0` always receives `none` in `fot M`. -/
theorem otSFE_sender_abort_differs_from_fot (M : Type) (κ : ℕ) (C : Finset (Fin 2)) :
    (((otSFE M).toProtocol κ C).run do
      let _ ← ProbOracleComp.query (Sum.inr SFEBackdoor.abort)
      ProbOracleComp.query (Sum.inl ((0 : Fin 2), .query))).eval =
      PMF.pure (some (SFEOutput.aborted : SFEOutput (Unit ⊕ M))) ∧
    (((fot M).toProtocol κ C).run do
      let _ ← ProbOracleComp.query (Sum.inr OTBackdoor.abort)
      ProbOracleComp.query (Sum.inl ((0 : Fin 2), .query))).eval =
      PMF.pure (none : Option (OTOutput M)) := by
  constructor <;>
    simp [Machine.run, Machine.link, otSFE, fot, IdealFunctionality.toProtocol, fsfe,
      SFEState.partyOutput, StateT.run, ProbOracleComp.sample_pure]

/-- **Semantic difference 2 (selective per-party delivery in `otSFE`):** after both parties submit
`(msgs, b)`, issuing `.deliver 0` releases `some (.output (.inl ()))` to sender `0` while receiver
`1` still observes `none`, and a subsequent `.abort` leaves sender `0` with its delivered output and
receiver `1` with `some .aborted`. (`fot` has only a single `.deliver` for receiver `1`.) -/
theorem otSFE_selective_deliver_zero {M : Type} (msgs : OTMessages M) (b : Bool)
    (κ : ℕ) :
    (((otSFE M).toProtocol κ ∅).run do
      let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), .input (.inl msgs)))
      let _ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), .input (.inr b)))
      let _ ← ProbOracleComp.query (Sum.inr (SFEBackdoor.deliver 0))
      let r₁Before ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), .query))
      let _ ← ProbOracleComp.query (Sum.inr SFEBackdoor.abort)
      let r₀After ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), .query))
      let r₁After ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), .query))
      return (r₁Before, r₀After, r₁After)).eval =
      PMF.pure (none, some (.output (.inl ())), some .aborted) := by
  let sAll : SFEState 2 (OTMessages M ⊕ Bool) :=
    { inputs := Function.update (Function.update (fun _ : Fin 2 => none) 0
        (some (Sum.inl msgs))) 1 (some (Sum.inr b)) }
  have hall : sAll.allSubmitted = true := by
    simp [sAll, SFEState.allSubmitted, Fin.forall_fin_two, Function.update_self,
      Function.update_of_ne]
  let sDel0 : SFEState 2 (OTMessages M ⊕ Bool) :=
    { sAll with delivered := Function.update (fun _ : Fin 2 => false) 0 true }
  let sDel0Ab : SFEState 2 (OTMessages M ⊕ Bool) := { sDel0 with aborted := true }
  simp only [Machine.run, Machine.link, otSFE, IdealFunctionality.toProtocol, fsfe,
    StateT.run, apply_ite ProbOracleComp.sample, ProbOracleComp.sample_pure, Option.isNone_none,
    ↓reduceIte, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), pure_bind,
    Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  erw [hall]
  simp only [Bool.not_false, Bool.and_self, ↓reduceIte, Machine.closeProgram_pure,
    ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map]
  simp only [SFEState.partyOutput, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), SFEState.eval?, Fin.forall_fin_two,
    Option.isSome_some, and_self, ↓reduceDIte, otEvalFn, ↓reduceIte, Option.map_some]
  rfl

end Cslib.Crypto.Protocols.UC
