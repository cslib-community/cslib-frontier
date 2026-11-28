/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.JointState
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind

/-!
# Ideal UC 1-out-of-2 Oblivious Transfer

This module defines the two-party ideal 1-out-of-2 oblivious transfer functionality `fot` in the
Universally Composable (UC) framework with static corruptions
(`CslibFrontier/Crypto/Protocols/UC/Execution.lean`), adapting the ideal oblivious-transfer
functionality of [Canetti2020] (and motivated by [BonehShoup2023], Section 23.5; section/page
locators not verified from the rendered PDF) to this library's call-bounded,
pull-only port model (`UC.IdealFunctionality`).

## Model and scope

* **Parties and inputs:** Sender `0 : Fin 2` submits a pair `msgs : OTMessages M` (`m₀`, `m₁`) via
  `OTInput.send msgs`, and receiver `1 : Fin 2` submits a choice bit `b : Bool` via
  `OTInput.choose b` and polls for output via `OTInput.query`. Both inputs are write-once immutable.
* **Delayed output and abort:** Receiver `1` sees `none` on `OTInput.query` until the adversary
  either releases the output via `OTBackdoor.deliver` (after both inputs are recorded and no abort
  has occurred), yielding `some (.delivered (msgs.select b))`, or aborts via `OTBackdoor.abort`
  (before delivery), yielding `some .aborted`.
* **Minimal status leakage:** Polling `OTBackdoor.query` returns `OTBackdoorReply.status st` where
  `st : OTStatus` exposes only four Boolean readiness/completion flags (`senderReady`,
  `receiverReady`, `delivered`, `aborted`) and never leaks `m₀`, `m₁`, or `b`.
* **Call-bounded pull model:** As throughout `CslibFrontier/Crypto/Protocols/UC/Execution.lean`,
  activations are pull-based and `PolyBounded` / `IsBounded` count oracle calls and private coins
  only, not PPT interactive Turing machine running time.

## Main definitions

* `Cslib.Crypto.Protocols.UC.OTMessages`, `Cslib.Crypto.Protocols.UC.OTInput`,
  `Cslib.Crypto.Protocols.UC.OTOutput`, `Cslib.Crypto.Protocols.UC.OTStatus`,
  `Cslib.Crypto.Protocols.UC.OTBackdoor`, `Cslib.Crypto.Protocols.UC.OTBackdoorReply`,
  `Cslib.Crypto.Protocols.UC.OTState`: named request, reply, status, backdoor, and state records for
  1-out-of-2 oblivious transfer.
* `Cslib.Crypto.Protocols.UC.fot`: the two-party ideal 1-out-of-2 oblivious transfer functionality
  $\mathcal{F}_{\mathrm{OT}}$.
* `Cslib.Crypto.Protocols.UC.fotSelectedView`, `Cslib.Crypto.Protocols.UC.fotSenderView`:
  state-abstraction machines capturing sender privacy (`C = {1}`) and receiver privacy (`C = {0}`).
* `Cslib.Crypto.Protocols.UC.PlainSenderOT`, `Cslib.Crypto.Protocols.UC.corruptOTReceiverEnv`:
  one-message sender-to-receiver plain-model OT schemes and their corrupted-receiver extraction
  environment.

## Main results

* `Cslib.Crypto.Protocols.UC.fot_isBounded`, `Cslib.Crypto.Protocols.UC.fot_polyBounded`,
  `Cslib.Crypto.Protocols.UC.fot_multiSession_polyBounded`: zero-call budget bounds for `fot` and
  its multi-session extension `(fot M).multiSession SSID`.
* `Cslib.Crypto.Protocols.UC.OTState.monotone_of_mem_support_runFrom`: write-once input lock and
  delivery/abort monotonicity across arbitrary multi-step interactions.
* `Cslib.Crypto.Protocols.UC.eval_exec_honestOTEnv`,
  `Cslib.Crypto.Protocols.UC.eval_exec_abortOTEnv`: honest delivery of `msgs.select b` and abort
  semantics.
* `Cslib.Crypto.Protocols.UC.runFrom_fot_corruptReceiver`,
  `Cslib.Crypto.Protocols.UC.eval_runFrom_fot_corruptReceiver_eq_of_select_eq`: **sender privacy**
  for `C = {1}` and fixed `b` (unselected-message independence across all party and backdoor ports).
* `Cslib.Crypto.Protocols.UC.runFrom_fot_corruptSender`,
  `Cslib.Crypto.Protocols.UC.eval_runFrom_fot_corruptSender_flip`: **receiver privacy** for
  `C = {0}` (choice-bit invariance across all party-`0` and backdoor queries).
* `Cslib.Crypto.Protocols.UC.not_realizes_fot_of_plainSenderOT`: no one-message sender-to-receiver
  plain-model OT scheme with nontrivial completeness UC-realizes `fot Bool`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 23.5
  (motivation only; section/page locators not verified from the rendered PDF): ideal 1-out-of-2
  oblivious transfer.
* [R. Canetti, *Universally Composable Security*][Canetti2020], Section 4: UC execution and
  realization.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open Polynomial
open scoped NNReal ENNReal

/-! ### Request, reply, status, backdoor, and state types -/

/-- The sender's pair of messages `(m₀, m₁)` submitted to 1-out-of-2 oblivious transfer. -/
structure OTMessages (M : Type) : Type where
  /-- Message delivered when receiver chooses `false`. -/
  m₀ : M
  /-- Message delivered when receiver chooses `true`. -/
  m₁ : M
  deriving DecidableEq, Repr

/-- Select `m₀` on `false` and `m₁` on `true`. -/
@[expose] def OTMessages.select {M : Type} (msgs : OTMessages M) (b : Bool) : M :=
  if b then msgs.m₁ else msgs.m₀

/-- Party-port inputs for `fot`: sender `0` submits `send msgs`, while receiver `1` submits
`choose b` and polls `query`. -/
inductive OTInput (M : Type) : Type
  | send (msgs : OTMessages M)
  | choose (b : Bool)
  | query
  deriving DecidableEq, Repr

/-- Party-port outputs for `fot`: receiver `1` receives either `delivered msg` or `aborted`. -/
inductive OTOutput (M : Type) : Type
  | delivered (msg : M)
  | aborted
  deriving DecidableEq, Repr

/-- Non-leaking status flags exposed on the backdoor of `fot`: readiness of each party, delivery
status, and abort status, without revealing `m₀`, `m₁`, or `b`. -/
structure OTStatus : Type where
  /-- Whether sender `0` has submitted its message pair. -/
  senderReady : Bool
  /-- Whether receiver `1` has submitted its choice bit. -/
  receiverReady : Bool
  /-- Whether output has been released to receiver `1`. -/
  delivered : Bool
  /-- Whether the transfer has been aborted. -/
  aborted : Bool
  deriving DecidableEq, Repr

/-- Backdoor queries of `fot`: `query` reads `OTStatus`, `deliver` releases the selected message
to receiver `1` once both inputs are present and no abort occurred, and `abort` aborts before
delivery. -/
inductive OTBackdoor : Type
  | query
  | deliver
  | abort
  deriving DecidableEq, Repr

/-- Backdoor replies of `fot`: either status flags or an acknowledgement. -/
inductive OTBackdoorReply : Type
  | status (st : OTStatus)
  | ack
  deriving DecidableEq, Repr

/-- Internal state of `fot`. -/
structure OTState (M : Type) : Type where
  /-- Sender `0`'s submitted message pair, write-once. -/
  senderMsgs : Option (OTMessages M) := none
  /-- Receiver `1`'s submitted choice bit, write-once. -/
  receiverChoice : Option Bool := none
  /-- Whether the adversary has released the chosen message to receiver `1`. -/
  delivered : Bool := false
  /-- Whether the adversary has aborted the transfer. -/
  aborted : Bool := false
  deriving DecidableEq, Repr

/-- Extract the public `OTStatus` flags from `OTState`. -/
@[expose] def OTState.status {M : Type} (s : OTState M) : OTStatus where
  senderReady := s.senderMsgs.isSome
  receiverReady := s.receiverChoice.isSome
  delivered := s.delivered
  aborted := s.aborted

/-- Receiver `1`'s observable output in state `s` on `OTInput.query`. -/
@[expose] def OTState.receiverOutput {M : Type} (s : OTState M) : Option (OTOutput M) :=
  if s.aborted then
    some .aborted
  else if s.delivered then
    match s.senderMsgs, s.receiverChoice with
    | some msgs, some b => some (.delivered (msgs.select b))
    | _, _ => none
  else
    none

/-- Monotonicity relation between states `s` and `s'` across activations of `fot`: inputs are
write-once immutable, and `delivered` and `aborted` are sticky. -/
structure OTState.Monotone {M : Type} (s s' : OTState M) : Prop where
  /-- Once set, sender messages cannot change. -/
  senderMsgs_lock : ∀ msgs, s.senderMsgs = some msgs → s'.senderMsgs = some msgs
  /-- Once set, receiver choice bit cannot change. -/
  receiverChoice_lock : ∀ b, s.receiverChoice = some b → s'.receiverChoice = some b
  /-- Once delivered, the transfer stays delivered. -/
  delivered_mono : s.delivered = true → s'.delivered = true
  /-- Once aborted, the transfer stays aborted. -/
  aborted_mono : s.aborted = true → s'.aborted = true

/-! ### Ideal 1-out-of-2 oblivious transfer functionality `fot` -/

/-- The ideal two-party 1-out-of-2 oblivious transfer functionality $\mathcal{F}_{\mathrm{OT}}$
(motivated by [BonehShoup2023], §23.5; locators not verified from PDF) for sender `0 : Fin 2` and
receiver `1 : Fin 2`, generic over message
type `M`:
- Sender `0` submits `send msgs` once (subsequent sends and queries return `none` without changing
  `senderMsgs`).
- Receiver `1` submits `choose b` once (subsequent choices are ignored) and polls `query` to read
  `none` before release/abort, `some (.delivered (msgs.select b))` after `deliver`, or
  `some .aborted` after `abort`.
- Backdoor `query` returns `OTStatus` (without `m₀`, `m₁`, or `b`); `deliver` releases the output
  if both parties have submitted and no abort occurred; `abort` sets `aborted := true` if not yet
  delivered. -/
@[expose] def fot (M : Type) :
    IdealFunctionality 2 (OTInput M) (OTOutput M) OTBackdoor OTBackdoorReply where
  State := OTState M
  init _ _ := pure {}
  onInput i x s :=
    if i = 0 then
      match x with
      | .send msgs =>
        if s.senderMsgs.isNone then
          pure (none, { s with senderMsgs := some msgs })
        else
          pure (none, s)
      | _ => pure (none, s)
    else
      match x with
      | .choose b =>
        if s.receiverChoice.isNone then
          pure (none, { s with receiverChoice := some b })
        else
          pure (none, s)
      | .query => pure (s.receiverOutput, s)
      | _ => pure (none, s)
  onBackdoor q s :=
    match q with
    | .query => pure (.status s.status, s)
    | .deliver =>
      if s.senderMsgs.isSome && s.receiverChoice.isSome && !s.aborted then
        pure (.ack, { s with delivered := true })
      else
        pure (.ack, s)
    | .abort =>
      if !s.delivered then
        pure (.ack, { s with aborted := true })
      else
        pure (.ack, s)

/-! ### Call-budget bounds and multi-session compatibility -/

/-- `fot` is deterministic and makes zero oracle calls per activation. -/
theorem fot_isBounded (M : Type) (κ : ℕ) (C : Finset (Fin 2)) :
    ((fot M).toProtocol κ C).IsBounded 0 := by
  refine ⟨OracleComp.IsCostBounded.pure _ 0, fun q s => ?_⟩
  rcases q with ⟨i, x⟩ | q
  · fin_cases i <;> cases x
    · by_cases hs : s.senderMsgs.isNone <;>
        simp only [IdealFunctionality.toProtocol, fot, StateT.run, hs, ↓reduceIte] <;>
        exact OracleComp.IsCostBounded.pure _ 0
    · simp only [IdealFunctionality.toProtocol, fot, StateT.run]
      exact OracleComp.IsCostBounded.pure _ 0
    · simp only [IdealFunctionality.toProtocol, fot, StateT.run]
      exact OracleComp.IsCostBounded.pure _ 0
    · simp only [IdealFunctionality.toProtocol, fot, StateT.run]
      exact OracleComp.IsCostBounded.pure _ 0
    · by_cases hr : s.receiverChoice.isNone <;>
        simp only [IdealFunctionality.toProtocol, fot, StateT.run, hr, ↓reduceIte] <;>
        exact OracleComp.IsCostBounded.pure _ 0
    · simp only [IdealFunctionality.toProtocol, fot, StateT.run]
      exact OracleComp.IsCostBounded.pure _ 0
  · cases q
    · simp only [IdealFunctionality.toProtocol, fot, StateT.run]
      exact OracleComp.IsCostBounded.pure _ 0
    · by_cases hd : (s.senderMsgs.isSome && s.receiverChoice.isSome && !s.aborted) <;>
        simp only [IdealFunctionality.toProtocol, fot, StateT.run, hd, ↓reduceIte] <;>
        exact OracleComp.IsCostBounded.pure _ 0
    · by_cases ha : !s.delivered <;>
        simp only [IdealFunctionality.toProtocol, fot, StateT.run, ha, ↓reduceIte] <;>
        exact OracleComp.IsCostBounded.pure _ 0

/-- `fot` has polynomial call budget `0`. -/
theorem fot_polyBounded (M : Type) : (fot M).toProtocol.PolyBounded 0 := fun κ C => by
  rw [Polynomial.eval_zero]
  exact fot_isBounded M κ C

/-- Routing static corruptions around any `b`-bounded protocol still makes at most `b` oracle
calls per activation. -/
theorem corruptRouter_isBounded {n : ℕ} {In Out NetQ NetR : Type}
    (C : Finset (Fin n)) (P : Machine OracleSpec.empty (protocolSpec n In Out NetQ NetR))
    {b : ℕ} (hP : P.IsBounded b) : (corruptRouter C P).IsBounded b := by
  refine ⟨hP.1, fun q s => ?_⟩
  rcases q with ⟨i, x⟩ | ⟨⟨i, x⟩ | bq⟩
  · by_cases hi : i ∈ C
    · simp only [corruptRouter, hi, ↓reduceIte]
      exact OracleComp.IsCostBounded.pure _ b
    · simp only [corruptRouter, hi, ↓reduceIte]
      exact hP.2 (.inl (i, x)) s
  · by_cases hi : i ∈ C
    · simp only [corruptRouter, hi, ↓reduceIte, StateT.run, Functor.map, StateT.map,
        bind_pure_comp]
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (hP.2 (.inl (i, x)) s)
    · simp only [corruptRouter, hi, ↓reduceIte]
      exact OracleComp.IsCostBounded.pure _ b
  · simp only [corruptRouter, StateT.run, Functor.map, StateT.map, bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (hP.2 (.inr bq) s)

/-- Routing static corruptions around `fot` still makes zero oracle calls per activation. -/
theorem corruptRouter_fot_isBounded (M : Type) (κ : ℕ) (C : Finset (Fin 2)) :
    (corruptRouter C ((fot M).toProtocol κ C)).IsBounded 0 :=
  corruptRouter_isBounded C ((fot M).toProtocol κ C) (fot_isBounded M κ C)

/-- Any `0`-bounded ideal functionality's lazy multi-session extension has polynomial call budget
`0`. -/
theorem multiSession_polyBounded_of_zero {n : ℕ}
    {In Out BackQ BackR : Type} (F : IdealFunctionality n In Out BackQ BackR)
    (hInit : ∀ κ C, (F.init κ C).IsQueryBounded 0)
    (hIn : ∀ i x s, ((F.onInput i x).run s).IsQueryBounded 0)
    (hBack : ∀ q s, ((F.onBackdoor q).run s).IsQueryBounded 0)
    (SSID : Type) [DecidableEq SSID] :
    (F.multiSession SSID).toProtocol.PolyBounded 0 := fun κ C => by
  rw [Polynomial.eval_zero]
  dsimp only [StateT.run] at hIn hBack
  refine ⟨OracleComp.IsCostBounded.pure _ 0, fun q s => ?_⟩
  rcases q with ⟨i, req⟩ | req
  · dsimp only [IdealFunctionality.toProtocol, IdealFunctionality.multiSession, StateT.run]
    refine Machine.isQueryBounded_sample ?_
    cases s.sessions req.ssid with
    | some st =>
      simpa only [pure_bind, Nat.add_zero] using
        (hIn i req.input st).bind fun _ => OracleComp.IsCostBounded.pure _ 0
    | none =>
      simpa only [Nat.add_zero] using
        (hInit s.secParam s.corrupted).bind fun fState =>
          (hIn i req.input fState).bind fun _ => OracleComp.IsCostBounded.pure _ 0
  · dsimp only [IdealFunctionality.toProtocol, IdealFunctionality.multiSession, StateT.run]
    refine Machine.isQueryBounded_sample ?_
    cases s.sessions req.ssid with
    | some st =>
      simpa only [pure_bind, Nat.add_zero] using
        (hBack req.query st).bind fun _ => OracleComp.IsCostBounded.pure _ 0
    | none =>
      simpa only [Nat.add_zero] using
        (hInit s.secParam s.corrupted).bind fun fState =>
          (hBack req.query fState).bind fun _ => OracleComp.IsCostBounded.pure _ 0

/-- The lazy multi-session extension `(fot M).multiSession SSID` has polynomial call budget `0`. -/
theorem fot_multiSession_polyBounded (M SSID : Type) [DecidableEq SSID] :
    ((fot M).multiSession SSID).toProtocol.PolyBounded 0 :=
  multiSession_polyBounded_of_zero (fot M)
    (fun _ _ => OracleComp.IsCostBounded.pure _ 0)
    (fun i x s => by
      fin_cases i <;> cases x <;> dsimp only [fot, StateT.run, Fin.isValue]
      · split_ifs <;> exact OracleComp.IsCostBounded.pure _ 0
      · exact OracleComp.IsCostBounded.pure _ 0
      · exact OracleComp.IsCostBounded.pure _ 0
      · exact OracleComp.IsCostBounded.pure _ 0
      · split_ifs <;> exact OracleComp.IsCostBounded.pure _ 0
      · exact OracleComp.IsCostBounded.pure _ 0)
    (fun q s => by
      cases q <;> dsimp only [fot, StateT.run]
      · exact OracleComp.IsCostBounded.pure _ 0
      · split_ifs <;> exact OracleComp.IsCostBounded.pure _ 0
      · split_ifs <;> exact OracleComp.IsCostBounded.pure _ 0)
    SSID

/-! ### State invariants and write-once immutability -/

theorem OTState.Monotone.refl {M : Type} (s : OTState M) : OTState.Monotone s s :=
  ⟨fun _ h => h, fun _ h => h, fun h => h, fun h => h⟩

theorem OTState.Monotone.trans {M : Type} {a b c : OTState M}
    (hab : OTState.Monotone a b) (hbc : OTState.Monotone b c) : OTState.Monotone a c where
  senderMsgs_lock msgs h := hbc.senderMsgs_lock msgs (hab.senderMsgs_lock msgs h)
  receiverChoice_lock b' h := hbc.receiverChoice_lock b' (hab.receiverChoice_lock b' h)
  delivered_mono h := hbc.delivered_mono (hab.delivered_mono h)
  aborted_mono h := hbc.aborted_mono (hab.aborted_mono h)

/-- Lifts a reflexive, transitive per-activation relation `R` from single steps of `P` through
`corruptRouter C P` and any multi-step execution `runFrom prog s`. -/
theorem corruptRouter_invariant_of_mem_support_runFrom {n : ℕ} {In Out NetQ NetR α : Type}
    (C : Finset (Fin n)) (P : Machine OracleSpec.empty (protocolSpec n In Out NetQ NetR))
    (R : P.State → P.State → Prop) (hrefl : ∀ s, R s s)
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (hsingle : ∀ q₀ s r,
      r ∈ (Machine.closeEval ((P.handle q₀).run s)).support → R s r.2)
    (prog : ProbOracleComp
      (protocolSpec n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) α)
    (s : P.State) {x : α × P.State}
    (hx : x ∈ (Machine.closeEval ((corruptRouter C P).runFrom prog s)).support) :
    R s x.2 := by
  refine Machine.mem_support_closeEval_runFrom_invariant
    (corruptRouter C P) (fun _ => True) R hrefl htrans prog
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _) s hx ?_
  intro q s' y _ hy
  rcases q with ⟨i, inp⟩ | ⟨⟨i, inp⟩ | bq⟩
  · by_cases hi : i ∈ C
    · dsimp only [corruptRouter, StateT.run] at hy
      split_ifs at hy
      erw [Machine.closeEval_pure, PMF.mem_support_pure_iff] at hy
      subst hy; exact hrefl s'
    · dsimp only [corruptRouter] at hy
      split_ifs at hy
      exact hsingle (.inl (i, inp)) s' y hy
  · by_cases hi : i ∈ C
    · simp only [corruptRouter, hi, ↓reduceIte, StateT.run, Functor.map, StateT.map,
        bind_pure_comp] at hy
      erw [Machine.closeEval_map, PMF.mem_support_map_iff] at hy
      rcases hy with ⟨r, hr, rfl⟩
      exact hsingle (.inl (i, inp)) s' r hr
    · dsimp only [corruptRouter, StateT.run] at hy
      split_ifs at hy
      erw [Machine.closeEval_pure, PMF.mem_support_pure_iff] at hy
      subst hy; exact hrefl s'
  · simp only [corruptRouter, StateT.run, Functor.map, StateT.map, bind_pure_comp] at hy
    erw [Machine.closeEval_map, PMF.mem_support_map_iff] at hy
    rcases hy with ⟨r, hr, rfl⟩
    exact hsingle (.inr bq) s' r hr

private theorem fot_single_step_monotone {M : Type} (κ : ℕ) (C : Finset (Fin 2))
    (q₀ : (Fin 2 × OTInput M) ⊕ OTBackdoor) (s : OTState M)
    (r : protocolSpec 2 (OTInput M) (OTOutput M) OTBackdoor OTBackdoorReply q₀ × OTState M)
    (hr : r ∈ (Machine.closeEval (((fot M).toProtocol κ C).handle q₀ |>.run s)).support) :
    OTState.Monotone s r.2 := by
  rcases q₀ with ⟨i, x⟩ | bq
  · rcases i with ⟨_ | _ | i, hi⟩
    · have h0 : (⟨0, hi⟩ : Fin 2) = 0 := rfl
      dsimp only [IdealFunctionality.toProtocol, fot, StateT.run] at hr
      rw [ite_eq_left_of_eq_true _ _ (eq_true h0)] at hr
      cases x
      · split_ifs at hr with hs
        · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
            PMF.mem_support_pure_iff] at hr
          subst hr
          refine ⟨fun m hm => ?_, fun _ h => h, fun h => h, fun h => h⟩
          rw [hm] at hs; simp at hs
        · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
            PMF.mem_support_pure_iff] at hr
          subst hr; exact OTState.Monotone.refl s
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr; exact OTState.Monotone.refl s
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr; exact OTState.Monotone.refl s
    · have h1 : (⟨1, hi⟩ : Fin 2) ≠ 0 := by simp
      dsimp only [IdealFunctionality.toProtocol, fot, StateT.run] at hr
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hr
      cases x
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr; exact OTState.Monotone.refl s
      · split_ifs at hr with hb
        · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
            PMF.mem_support_pure_iff] at hr
          subst hr
          refine ⟨fun _ h => h, fun b' hb' => ?_, fun h => h, fun h => h⟩
          rw [hb'] at hb; simp at hb
        · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
            PMF.mem_support_pure_iff] at hr
          subst hr; exact OTState.Monotone.refl s
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr; exact OTState.Monotone.refl s
    · omega
  · cases bq <;> dsimp only [IdealFunctionality.toProtocol, fot, StateT.run] at hr
    · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure, PMF.mem_support_pure_iff] at hr
      subst hr; exact OTState.Monotone.refl s
    · split_ifs at hr
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr; exact ⟨fun _ h => h, fun _ h => h, fun _ => rfl, fun h => h⟩
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr; exact OTState.Monotone.refl s
    · split_ifs at hr
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr; exact ⟨fun _ h => h, fun _ h => h, fun h => h, fun _ => rfl⟩
      · erw [ProbOracleComp.sample_pure, Machine.closeEval_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr; exact OTState.Monotone.refl s

/-- **Write-once input lock and delivery/abort monotonicity:** across any program run against
`corruptRouter C ((fot M).toProtocol κ C)`, every reachable final state satisfies `OTState.Monotone`
relative to the starting state `s`. -/
theorem OTState.monotone_of_mem_support_runFrom {M α : Type} (κ : ℕ) (C : Finset (Fin 2))
    (prog : ProbOracleComp
      (protocolSpec 2 (OTInput M) (OTOutput M) (RoutedNetQ 2 (OTInput M) OTBackdoor)
        (RoutedNetR (OTOutput M) OTBackdoorReply)) α)
    (s : OTState M) {x : α × OTState M}
    (hx : x ∈ (Machine.closeEval
      ((corruptRouter C ((fot M).toProtocol κ C)).runFrom prog s)).support) :
    OTState.Monotone s x.2 :=
  corruptRouter_invariant_of_mem_support_runFrom C ((fot M).toProtocol κ C)
    OTState.Monotone OTState.Monotone.refl (fun hab hbc => hab.trans hbc)
    (fot_single_step_monotone κ C) prog s hx

/-! ### Honest delivery and abort correctness -/

/-- Honest-execution environment (`C = ∅`) for `fot M`: sender `0` submits `msgs`, receiver `1`
submits `b`, the backdoor delivers, and receiver `1` polls for `some (.delivered (msgs.select b))`.
-/
@[expose] def honestOTEnv {M : Type} [DecidableEq M] (msgs : OTMessages M) (b : Bool) :
    Environment 2 (OTInput M) (OTOutput M)
      (RoutedNetQ 2 (OTInput M) OTBackdoor)
      (RoutedNetR (OTOutput M) OTBackdoorReply) := fun _ _ => do
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (0, .send msgs))
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (1, .choose b))
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inr (.inr .deliver))
  let out ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (1, .query))
  return decide (out = some (.delivered (msgs.select b)))

/-- Abort-test environment (`C = ∅`) for `fot M`: sender `0` submits `msgs`, receiver `1` submits
`b`, the backdoor aborts, and receiver `1` polls for `some .aborted`. -/
@[expose] def abortOTEnv {M : Type} (msgs : OTMessages M) (b : Bool) :
    Environment 2 (OTInput M) (OTOutput M)
      (RoutedNetQ 2 (OTInput M) OTBackdoor)
      (RoutedNetR (OTOutput M) OTBackdoorReply) := fun _ _ => do
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (0, .send msgs))
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (1, .choose b))
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inr (.inr .abort))
  let out ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput M) (OTOutput M) _ _) (Sum.inl (1, .query))
  return match out with | some .aborted => true | _ => false

/-- **Correctness / honest delivery of `fot`:** with no corruptions and the dummy adversary,
`honestOTEnv msgs b` observes `some (.delivered (msgs.select b))` with probability `1`. -/
theorem eval_exec_honestOTEnv {M : Type} [DecidableEq M] (msgs : OTMessages M) (b : Bool)
    (κ : ℕ) (z : List Bool) :
    (exec (fot M).toProtocol (dummyAdversary 2 _ _) ∅ (honestOTEnv msgs b) κ z).eval =
      PMF.pure true := by
  rw [exec_dummyAdversary]
  simp only [Machine.run, Machine.link, honestOTEnv, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.runFrom_pure, Machine.closeProgram_bind, Machine.closeProgram_map,
    Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  have hinit : (corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).init =
      (pure ({} : OTState M) :
        ProbComp (corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).State) := rfl
  have h0 : ((corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).handle
      (Sum.inl (0, .send msgs))).run {} =
      pure (none, { senderMsgs := some msgs }) := rfl
  have h1 : ((corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).handle
      (Sum.inl (1, .choose b))).run { senderMsgs := some msgs } =
      pure (none, { senderMsgs := some msgs, receiverChoice := some b }) := rfl
  have hd : ((corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).handle
      (Sum.inr (.inr .deliver))).run { senderMsgs := some msgs, receiverChoice := some b } =
      pure (.inr .ack, { senderMsgs := some msgs, receiverChoice := some b, delivered := true }) :=
    rfl
  have hq : ((corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).handle
      (Sum.inl (1, .query))).run
        { senderMsgs := some msgs, receiverChoice := some b, delivered := true } =
      pure (some (.delivered (msgs.select b)),
        { senderMsgs := some msgs, receiverChoice := some b, delivered := true }) := rfl
  erw [hinit, ProbOracleComp.sample_pure, Machine.closeProgram_pure, ProbComp.eval_pure,
    PMF.pure_bind, h0, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind,
    h1, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind,
    hd, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind,
    hq, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind]
  simp only [PMF.pure_map]
  rfl

/-- **Abort correctness of `fot`:** when the backdoor issues `.abort` before delivery, receiver `1`
observes `some .aborted` with probability `1`. -/
theorem eval_exec_abortOTEnv {M : Type} (msgs : OTMessages M) (b : Bool)
    (κ : ℕ) (z : List Bool) :
    (exec (fot M).toProtocol (dummyAdversary 2 _ _) ∅ (abortOTEnv msgs b) κ z).eval =
      PMF.pure true := by
  rw [exec_dummyAdversary]
  simp only [Machine.run, Machine.link, abortOTEnv, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.runFrom_pure, Machine.closeProgram_bind, Machine.closeProgram_map,
    Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  have hinit : (corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).init =
      (pure ({} : OTState M) :
        ProbComp (corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).State) := rfl
  have h0 : ((corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).handle
      (Sum.inl (0, .send msgs))).run {} =
      pure (none, { senderMsgs := some msgs }) := rfl
  have h1 : ((corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).handle
      (Sum.inl (1, .choose b))).run { senderMsgs := some msgs } =
      pure (none, { senderMsgs := some msgs, receiverChoice := some b }) := rfl
  have ha : ((corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).handle
      (Sum.inr (.inr .abort))).run { senderMsgs := some msgs, receiverChoice := some b } =
      pure (.inr .ack, { senderMsgs := some msgs, receiverChoice := some b, aborted := true }) :=
    rfl
  have hq : ((corruptRouter (∅ : Finset (Fin 2)) ((fot M).toProtocol κ ∅)).handle
      (Sum.inl (1, .query))).run
        { senderMsgs := some msgs, receiverChoice := some b, aborted := true } =
      pure (some .aborted,
        { senderMsgs := some msgs, receiverChoice := some b, aborted := true }) := rfl
  erw [hinit, ProbOracleComp.sample_pure, Machine.closeProgram_pure, ProbComp.eval_pure,
    PMF.pure_bind, h0, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind,
    h1, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind,
    ha, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind,
    hq, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind]
  simp only [PMF.pure_map]

/-! ### Sender privacy (`C = {1}`, unselected-message independence) -/

/-- State of the unselected-message-independent machine `fotSelectedView`. -/
structure OTSelectedViewState : Type where
  /-- Whether output has been delivered to receiver `1`. -/
  delivered : Bool
  /-- Whether the transfer has been aborted. -/
  aborted : Bool
  deriving DecidableEq, Repr

/-- Deterministic single-step transition of `corruptRouter {1} ((fot M).toProtocol κ {1})` once
`senderMsgs = some msgs` and `receiverChoice = some b`: depends only on `mSelected := msgs.select b`
and never on `msgs.select (!b)`. -/
@[expose] def fotSelectedStep {M : Type} (mSelected : M)
    (q : (Fin 2 × OTInput M) ⊕ RoutedNetQ 2 (OTInput M) OTBackdoor)
    (st : OTSelectedViewState) :
    protocolSpec 2 (OTInput M) (OTOutput M) (RoutedNetQ 2 (OTInput M) OTBackdoor)
      (RoutedNetR (OTOutput M) OTBackdoorReply) q × OTSelectedViewState :=
  match q with
  | .inl _ => (none, st)
  | .inr (.inl (i, x)) =>
    if i = 1 then
      match x with
      | .query =>
        let out :=
          if st.aborted then some .aborted
          else if st.delivered then some (.delivered mSelected)
          else none
        (.inl out, st)
      | _ => (.inl none, st)
    else
      (.inl none, st)
  | .inr (.inr .query) =>
    (.inr (.status ⟨true, true, st.delivered, st.aborted⟩), st)
  | .inr (.inr .deliver) =>
    if !st.aborted then (.inr .ack, { st with delivered := true })
    else (.inr .ack, st)
  | .inr (.inr .abort) =>
    if !st.delivered then (.inr .ack, { st with aborted := true })
    else (.inr .ack, st)

/-- Machine capturing the entire port and backdoor behavior of
`corruptRouter {1} ((fot M).toProtocol κ {1})` once both `senderMsgs` and `receiverChoice = some b`
are fixed, depending only on the selected message `mSelected`. -/
@[expose] def fotSelectedView {M : Type} (mSelected : M) :
    Machine OracleSpec.empty
      (protocolSpec 2 (OTInput M) (OTOutput M) (RoutedNetQ 2 (OTInput M) OTBackdoor)
        (RoutedNetR (OTOutput M) OTBackdoorReply)) where
  State := OTSelectedViewState
  init := pure ⟨false, false⟩
  handle q st := pure (fotSelectedStep mSelected q st)

private theorem handle_corruptRouter_fot_corruptReceiver {M : Type} (κ : ℕ)
    (msgs : OTMessages M) (b : Bool)
    (q : (Fin 2 × OTInput M) ⊕ RoutedNetQ 2 (OTInput M) OTBackdoor)
    (st : OTSelectedViewState) :
    ((corruptRouter ({1} : Finset (Fin 2)) ((fot M).toProtocol κ {1})).handle q).run
        { senderMsgs := some msgs, receiverChoice := some b,
          delivered := st.delivered, aborted := st.aborted } =
      Prod.map _root_.id (fun st' : OTSelectedViewState =>
        ({ senderMsgs := some msgs, receiverChoice := some b,
           delivered := st'.delivered, aborted := st'.aborted } : OTState M)) <$>
        ((fotSelectedView (msgs.select b)).handle q).run st := by
  rcases q with ⟨i, x⟩ | ⟨⟨i, x⟩ | bq⟩
  · fin_cases i <;> cases x <;> rcases st with ⟨_ | _, _ | _⟩ <;> rfl
  · fin_cases i <;> cases x <;> rcases st with ⟨_ | _, _ | _⟩ <;> rfl
  · cases bq <;> rcases st with ⟨_ | _, _ | _⟩ <;> rfl

/-- **Sender privacy (factoring through `fotSelectedView`):** when receiver `1` is corrupted
(`C = {1}`) and choice bit `b` is fixed (`receiverChoice = some b`), running any program over ALL
party and backdoor ports against `corruptRouter {1} ((fot M).toProtocol κ {1})` from
`senderMsgs = some msgs` factors through `fotSelectedView (msgs.select b)`, which has no access to
`msgs.select (!b)`. -/
theorem runFrom_fot_corruptReceiver {M α : Type} (κ : ℕ) (msgs : OTMessages M) (b : Bool)
    (program : ProbOracleComp
      (protocolSpec 2 (OTInput M) (OTOutput M) (RoutedNetQ 2 (OTInput M) OTBackdoor)
        (RoutedNetR (OTOutput M) OTBackdoorReply)) α)
    (st : OTSelectedViewState) :
    (corruptRouter ({1} : Finset (Fin 2)) ((fot M).toProtocol κ {1})).runFrom program
        { senderMsgs := some msgs, receiverChoice := some b,
          delivered := st.delivered, aborted := st.aborted } =
      Prod.map _root_.id (fun st' : OTSelectedViewState =>
        ({ senderMsgs := some msgs, receiverChoice := some b,
           delivered := st'.delivered, aborted := st'.aborted } : OTState M)) <$>
        (fotSelectedView (msgs.select b)).runFrom program st := by
  exact Machine.runFrom_map_state
    (corruptRouter ({1} : Finset (Fin 2)) ((fot M).toProtocol κ {1}))
    (fotSelectedView (msgs.select b))
    (fun st' => { senderMsgs := some msgs, receiverChoice := some b,
                  delivered := st'.delivered, aborted := st'.aborted })
    (handle_corruptRouter_fot_corruptReceiver κ msgs b) program st

/-- **Sender privacy (unselected-message independence):** for `C = {1}` and fixed `b`, any two
sender message pairs `msgs, msgs'` agreeing on the selected branch
(`msgs.select b = msgs'.select b`) produce identical output distributions across every port/backdoor
program `program`. -/
theorem eval_runFrom_fot_corruptReceiver_eq_of_select_eq {M α : Type} (κ : ℕ)
    {msgs msgs' : OTMessages M} {b : Bool} (hsel : msgs.select b = msgs'.select b)
    (program : ProbOracleComp
      (protocolSpec 2 (OTInput M) (OTOutput M) (RoutedNetQ 2 (OTInput M) OTBackdoor)
        (RoutedNetR (OTOutput M) OTBackdoorReply)) α)
    (delivered aborted : Bool) :
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({1} : Finset (Fin 2)) ((fot M).toProtocol κ {1})).runFrom program
        { senderMsgs := some msgs, receiverChoice := some b,
          delivered := delivered, aborted := aborted })).eval =
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({1} : Finset (Fin 2)) ((fot M).toProtocol κ {1})).runFrom program
          { senderMsgs := some msgs', receiverChoice := some b,
            delivered := delivered, aborted := aborted })).eval := by
  rw [runFrom_fot_corruptReceiver κ msgs b program ⟨delivered, aborted⟩,
    runFrom_fot_corruptReceiver κ msgs' b program ⟨delivered, aborted⟩, hsel]
  repeat erw [Machine.closeProgram_map]
  repeat erw [Functor.map_map]
  rfl

/-! ### Receiver privacy (`C = {0}`, choice-bit hiding) -/

/-- State of the choice-bit-independent machine `fotSenderView` seen on the network port when
sender `0` is corrupted (`C = {0}`) and receiver `1` has submitted its choice bit. -/
structure OTSenderViewState (M : Type) : Type where
  /-- Sender `0`'s submitted message pair, if any. -/
  senderMsgs : Option (OTMessages M)
  /-- Whether output has been delivered to receiver `1`. -/
  delivered : Bool
  /-- Whether the transfer has been aborted. -/
  aborted : Bool
  deriving DecidableEq, Repr

/-- Deterministic network-port step of `corruptRouter {0} ((fot M).toProtocol κ {0})` once
receiver `1` has submitted a choice bit (`receiverReady = true`), independent of the bit `b`. -/
@[expose] def fotSenderStep {M : Type}
    (q : RoutedNetQ 2 (OTInput M) OTBackdoor) (st : OTSenderViewState M) :
    RoutedNetR (OTOutput M) OTBackdoorReply × OTSenderViewState M :=
  match q with
  | .inl (i, x) =>
    if i = 0 then
      match x with
      | .send msgs =>
        if st.senderMsgs.isNone then (.inl none, { st with senderMsgs := some msgs })
        else (.inl none, st)
      | _ => (.inl none, st)
    else
      (.inl none, st)
  | .inr .query =>
    (.inr (.status ⟨st.senderMsgs.isSome, true, st.delivered, st.aborted⟩), st)
  | .inr .deliver =>
    if st.senderMsgs.isSome && !st.aborted then
      (.inr .ack, { st with delivered := true })
    else
      (.inr .ack, st)
  | .inr .abort =>
    if !st.delivered then (.inr .ack, { st with aborted := true })
    else (.inr .ack, st)

/-- Choice-bit-independent machine capturing the party-`0` and backdoor behavior of
`corruptRouter {0} ((fot M).toProtocol κ {0})` once `receiverChoice = some b` is set. -/
@[expose] def fotSenderView (M : Type) :
    Machine OracleSpec.empty
      (netSpec (RoutedNetQ 2 (OTInput M) OTBackdoor) (RoutedNetR (OTOutput M) OTBackdoorReply))
    where
  State := OTSenderViewState M
  init := pure ⟨none, false, false⟩
  handle q st := pure (fotSenderStep q st)

private theorem handle_corruptRouter_fot_corruptSender {M : Type} (κ : ℕ) (b : Bool)
    (q : RoutedNetQ 2 (OTInput M) OTBackdoor) (st : OTSenderViewState M) :
    ((corruptRouter ({0} : Finset (Fin 2)) ((fot M).toProtocol κ {0})).handle (.inr q)).run
        { senderMsgs := st.senderMsgs, receiverChoice := some b,
          delivered := st.delivered, aborted := st.aborted } =
      Prod.map _root_.id (fun st' : OTSenderViewState M =>
        ({ senderMsgs := st'.senderMsgs, receiverChoice := some b,
           delivered := st'.delivered, aborted := st'.aborted } : OTState M)) <$>
        ((fotSenderView M).handle q).run st := by
  rcases q with ⟨i, x⟩ | bq
  · fin_cases i <;> cases x <;> rcases st with ⟨_ | msgs, _ | _, _ | _⟩ <;> rfl
  · cases bq <;> rcases st with ⟨_ | msgs, _ | _, _ | _⟩ <;> rfl

/-- **Receiver privacy (factoring through `fotSenderView`):** when sender `0` is corrupted
(`C = {0}`) and receiver `1` has submitted `b`, every network-port program `liftNet program`
(covering party-`0` queries and backdoor queries) factors through `fotSenderView M`, which is
independent of `b`. -/
theorem runFrom_fot_corruptSender {M α : Type} (κ : ℕ) (b : Bool)
    (program : ProbOracleComp
      (netSpec (RoutedNetQ 2 (OTInput M) OTBackdoor) (RoutedNetR (OTOutput M) OTBackdoorReply)) α)
    (st : OTSenderViewState M) :
    (corruptRouter ({0} : Finset (Fin 2)) ((fot M).toProtocol κ {0})).runFrom (liftNet program)
        { senderMsgs := st.senderMsgs, receiverChoice := some b,
          delivered := st.delivered, aborted := st.aborted } =
      Prod.map _root_.id (fun st' : OTSenderViewState M =>
        ({ senderMsgs := st'.senderMsgs, receiverChoice := some b,
           delivered := st'.delivered, aborted := st'.aborted } : OTState M)) <$>
        (fotSenderView M).runFrom program st := by
  let R := netSpec (RoutedNetQ 2 (OTInput M) OTBackdoor) (RoutedNetR (OTOutput M) OTBackdoorReply)
  induction program using OracleComp.induction generalizing st with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind]
    dsimp only [liftNet]
    rw [Machine.liftRightProgram_bind]
    rcases q with k | q
    · have h₁ : Machine.liftRightProgram (partySpec 2 (OTInput M) (OTOutput M))
          (OracleComp.query (spec := probOracleSpec R) (Sum.inl k)) =
          ProbOracleComp.sample (ProbComp.unifFin k) := by
        rw [← Machine.liftRightProgram_sample (partySpec 2 (OTInput M) (OTOutput M)) (R := R)]
        rfl
      have h₂ := (fotSenderView M).runFrom_sample (ProbComp.unifFin k) st
      erw [h₁, Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left,
        Machine.runFrom_bind, h₂, bind_map_left, map_bind]
      exact bind_congr fun a => ih a st
    · have h₁ : (corruptRouter ({0} : Finset (Fin 2)) ((fot M).toProtocol κ {0})).runFrom
          (Machine.liftRightProgram (partySpec 2 (OTInput M) (OTOutput M))
            (OracleComp.query (spec := probOracleSpec R) (Sum.inr q)))
          { senderMsgs := st.senderMsgs, receiverChoice := some b,
            delivered := st.delivered, aborted := st.aborted } =
          pure ((fotSenderStep q st).1,
            { senderMsgs := (fotSenderStep q st).2.senderMsgs, receiverChoice := some b,
              delivered := (fotSenderStep q st).2.delivered,
              aborted := (fotSenderStep q st).2.aborted }) := by
        erw [Machine.liftRightProgram_query, Machine.runFrom_query]
        exact handle_corruptRouter_fot_corruptSender κ b q st
      have h₂ : (fotSenderView M).runFrom
          (OracleComp.query (spec := probOracleSpec R) (Sum.inr q)) st =
          pure (fotSenderStep q st) := rfl
      erw [Machine.runFrom_bind, h₁, pure_bind, Machine.runFrom_bind, h₂, pure_bind]
      exact ih (fotSenderStep q st).1 (fotSenderStep q st).2

/-- **Receiver privacy (choice-bit hiding):** for `C = {0}`, flipping receiver `1`'s choice bit `b`
to `!b` leaves the entire party-`0` and backdoor behavior (`liftNet program`) identically
distributed. -/
theorem eval_runFrom_fot_corruptSender_flip {M α : Type} (κ : ℕ) (b : Bool)
    (program : ProbOracleComp
      (netSpec (RoutedNetQ 2 (OTInput M) OTBackdoor) (RoutedNetR (OTOutput M) OTBackdoorReply)) α)
    (st : OTSenderViewState M) :
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({0} : Finset (Fin 2)) ((fot M).toProtocol κ {0})).runFrom (liftNet program)
        { senderMsgs := st.senderMsgs, receiverChoice := some b,
          delivered := st.delivered, aborted := st.aborted })).eval =
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({0} : Finset (Fin 2)) ((fot M).toProtocol κ {0})).runFrom
          (liftNet program)
          { senderMsgs := st.senderMsgs, receiverChoice := some (!b),
            delivered := st.delivered, aborted := st.aborted })).eval := by
  rw [runFrom_fot_corruptSender κ b program st, runFrom_fot_corruptSender κ (!b) program st]
  repeat erw [Machine.closeProgram_map]
  repeat erw [Functor.map_map]
  rfl

/-! ### Impossibility of one-message sender-to-receiver plain-model OT -/

/-- Network queries for a one-message (sender-to-receiver) plain-model OT protocol: the adversary
can read the sender's message (`readMsg`) and deliver a message to the receiver (`deliverMsg`). -/
inductive PlainOTNetQ (Msg : Type) : Type
  | readMsg
  | deliverMsg (msg : Msg)
  deriving DecidableEq, Repr

/-- Network replies for a one-message plain-model OT protocol. -/
inductive PlainOTNetR (Msg : Type) : Type
  | msg (c : Option Msg)
  | ack
  deriving DecidableEq, Repr

/-- A one-message (sender-to-receiver) plain-model 1-out-of-2 OT scheme over `Bool`: sender `0` runs
`send κ m₀ m₁` to produce a single message `c : Msg`, and receiver `1` runs `recv κ c b` locally to
recover `m_b`. -/
structure PlainSenderOT (Msg : Type) : Type where
  /-- Sender algorithm producing a single message from `(m₀, m₁)`. -/
  send : ℕ → Bool → Bool → ProbComp Msg
  /-- Receiver recovery algorithm computing `m_b` from the sender's message and choice bit `b`. -/
  recv : ℕ → Msg → Bool → ProbComp Bool

namespace PlainSenderOT

variable {Msg : Type}

/-- State of a compiled `PlainSenderOT` protocol. -/
structure State (Msg : Type) : Type where
  /-- Message posted by sender `0`, if any. -/
  senderMsg : Option Msg := none
  /-- Choice bit submitted by receiver `1`, if any. -/
  receiverChoice : Option Bool := none
  /-- Output recovered by receiver `1`, if delivered. -/
  receiverOut : Option Bool := none
  deriving DecidableEq, Repr

/-- Honest completeness probability of `scheme` for choice bit `b` over uniform `(m₀, m₁)` at
security parameter `κ`. -/
@[expose] noncomputable def acceptGame (scheme : PlainSenderOT Msg) (κ : ℕ) (b : Bool) : Game :=
  ProbComp.eval do
    let r₀ ← ProbComp.unifFin 1
    let r₁ ← ProbComp.unifFin 1
    let m₀ := decide (r₀.val = 1)
    let m₁ := decide (r₁.val = 1)
    let c ← scheme.send κ m₀ m₁
    let res ← scheme.recv κ c b
    return decide (res = if b then m₁ else m₀)

/-- Probability that an honest receiver recovers `m_b` on uniform `(m₀, m₁)`. -/
@[expose] noncomputable def acceptProb (scheme : PlainSenderOT Msg) (κ : ℕ) (b : Bool) : ℝ≥0 :=
  Game.succProbability (scheme.acceptGame κ b)

/-- Polynomial call budgets `pS` and `pR` for `scheme.send` and `scheme.recv`. -/
structure IsPolyBounded (scheme : PlainSenderOT Msg) (pS pR : Polynomial ℕ) : Prop where
  /-- Every sender call at security parameter `κ` makes at most `pS.eval κ` calls. -/
  send : ∀ κ m₀ m₁, (scheme.send κ m₀ m₁).IsQueryBounded (pS.eval κ)
  /-- Every receiver recovery at security parameter `κ` makes at most `pR.eval κ` calls. -/
  recv : ∀ κ c b, (scheme.recv κ c b).IsQueryBounded (pR.eval κ)

/-- Compile a `PlainSenderOT` scheme into a two-party UC `Protocol` in the plain model (matching
`OTInput Bool` / `OTOutput Bool`): sender `0` computes `c ← scheme.send κ m₀ m₁` once; receiver `1`
records `b` once; `deliverMsg c` forwards `c` to receiver `1` (matching `senderMsg` when `0 ∉ C`, or
any `c` when `0 ∈ C`) and runs `scheme.recv κ c b`. -/
@[expose] def toProtocol [DecidableEq Msg] (scheme : PlainSenderOT Msg) :
    Protocol 2 (OTInput Bool) (OTOutput Bool) (PlainOTNetQ Msg) (PlainOTNetR Msg) := fun κ C => {
  State := PlainSenderOT.State Msg
  init := pure {}
  handle q s :=
    match q with
    | .inl (i, x) =>
      if i = 0 then
        if (0 : Fin 2) ∈ C then pure (none, s)
        else match x, s.senderMsg with
          | .send msgs, none =>
            ProbOracleComp.sample (scheme.send κ msgs.m₀ msgs.m₁) >>= fun c =>
              pure (none, { s with senderMsg := some c })
          | _, _ => pure (none, s)
      else
        if (1 : Fin 2) ∈ C then pure (none, s)
        else match x with
          | .choose b =>
            if s.receiverChoice.isNone then pure (none, { s with receiverChoice := some b })
            else pure (none, s)
          | .query => pure (s.receiverOut.map .delivered, s)
          | _ => pure (none, s)
    | .inr .readMsg => pure (.msg s.senderMsg, s)
    | .inr (.deliverMsg c) =>
      match s.receiverChoice, s.receiverOut with
      | some b, none =>
        if (0 : Fin 2) ∈ C || s.senderMsg = some c then
          ProbOracleComp.sample (scheme.recv κ c b) >>= fun res =>
            pure (.ack, { s with receiverOut := some res })
        else
          pure (.ack, s)
      | _, _ => pure (.ack, s) }

end PlainSenderOT

/-- Corrupted-receiver extraction environment (`C = {1}`) for a one-message plain-model OT scheme:
samples uniform `(m₀, m₁)`, sends `⟨m₀, m₁⟩` to honest sender `0`, reads the network message `c`,
runs `scheme.recv` locally on both `false` and `true`, and checks whether both bits were recovered.
-/
@[expose] def corruptOTReceiverEnv {Msg : Type} (scheme : PlainSenderOT Msg) :
    Environment 2 (OTInput Bool) (OTOutput Bool)
      (RoutedNetQ 2 (OTInput Bool) (PlainOTNetQ Msg))
      (RoutedNetR (OTOutput Bool) (PlainOTNetR Msg)) := fun κ _ => do
  let r₀ ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let r₁ ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let m₀ := decide (r₀.val = 1)
  let m₁ := decide (r₁.val = 1)
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput Bool) (OTOutput Bool) _ _) (Sum.inl (0, .send ⟨m₀, m₁⟩))
  let netR ← ProbOracleComp.query
    (spec := execSpec 2 (OTInput Bool) (OTOutput Bool) _ _) (Sum.inr (.inr .readMsg))
  match netR with
  | .inr (.msg (some c)) =>
    let g₀ ← ProbOracleComp.sample (scheme.recv κ c false)
    let g₁ ← ProbOracleComp.sample (scheme.recv κ c true)
    return decide (g₀ = m₀ ∧ g₁ = m₁)
  | _ => return false

/-- If `scheme.recv` has polynomial call budget `pR`, then `corruptOTReceiverEnv scheme` has
polynomial call budget `2 * pR + 4`. -/
theorem corruptOTReceiverEnv_polyBounded {Msg : Type} {scheme : PlainSenderOT Msg}
    {pR : Polynomial ℕ} (hR : ∀ κ c b, (scheme.recv κ c b).IsQueryBounded (pR.eval κ)) :
    (corruptOTReceiverEnv scheme).PolyBounded (2 * pR + 4) := fun κ _ => by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, corruptOTReceiverEnv]
  rw [show 2 * pR.eval κ + 4 = 1 + (1 + (1 + (1 + (pR.eval κ + pR.eval κ)))) by omega]
  refine (OracleComp.IsCostBounded.query _).bind fun _ =>
    (OracleComp.IsCostBounded.query _).bind fun _ =>
    (OracleComp.IsCostBounded.query _).bind fun _ =>
    (OracleComp.IsCostBounded.query _).bind fun netR => ?_
  rcases netR with _ | ⟨(_ | c) | _⟩ <;> try exact OracleComp.IsCostBounded.pure _ _
  refine (Machine.isQueryBounded_sample (hR κ c false)).bind fun _ => ?_
  simp only [bind_pure_comp]
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
    (Machine.isQueryBounded_sample (hR κ c true))

private theorem succProbability_bind_le {α : Type} (μ : PMF α) (f : α → Game) (c : ℝ≥0)
    (hf : ∀ a, Game.succProbability (f a) ≤ c) :
    Game.succProbability (μ.bind f) ≤ c := by
  rw [← NNReal.coe_le_coe, Game.coe_succProbability, Probability.PMF.bind_apply_toReal_tsum]
  have hsum : Summable (fun a => (μ a).toReal * (f a true).toReal) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (by simpa [Game.coe_succProbability] using
          NNReal.coe_le_coe.mpr (Game.succProbability_le_one (f a))))
      (Probability.PMF.summable_toReal μ)
  have hc_sum : Summable (fun a => (μ a).toReal * (c : ℝ)) :=
    (Probability.PMF.summable_toReal μ).mul_right (c : ℝ)
  calc ∑' a, (μ a).toReal * (f a true).toReal
      ≤ ∑' a, (μ a).toReal * (c : ℝ) :=
        Summable.tsum_le_tsum (fun a => mul_le_mul_of_nonneg_left
          (by simpa [Game.coe_succProbability] using NNReal.coe_le_coe.mpr (hf a))
          ENNReal.toReal_nonneg) hsum hc_sum
    _ = (∑' a, (μ a).toReal) * (c : ℝ) := tsum_mul_right
    _ = (c : ℝ) := by rw [Probability.PMF.tsum_toReal, one_mul]

/-- In the real execution with `C = {1}` and `dummyAdversary`, `corruptOTReceiverEnv scheme`
recovers both `m₀` and `m₁` with probability at least `acceptProb false + acceptProb true - 1`. -/
theorem acceptProb_add_sub_one_le_exec_real_corruptOTReceiverEnv {Msg : Type} [DecidableEq Msg]
    (scheme : PlainSenderOT Msg) (κ : ℕ) (z : List Bool) :
    (scheme.acceptProb κ false : ℝ) + scheme.acceptProb κ true - 1 ≤
      Game.succProbability (exec scheme.toProtocol (dummyAdversary 2 _ _) {1}
        (corruptOTReceiverEnv scheme) κ z).eval := by
  have hreal :
      (exec scheme.toProtocol (dummyAdversary 2 _ _) {1}
        (corruptOTReceiverEnv scheme) κ z).eval =
      (do
        let r₀ ← ProbComp.unifFin 1
        let r₁ ← ProbComp.unifFin 1
        let m₀ := decide (r₀.val = 1)
        let m₁ := decide (r₁.val = 1)
        let c ← scheme.send κ m₀ m₁
        let g₀ ← scheme.recv κ c false
        let g₁ ← scheme.recv κ c true
        return decide (g₀ = m₀ ∧ g₁ = m₁)).eval := by
    rw [exec_dummyAdversary]
    simp only [Machine.run, Machine.link, corruptOTReceiverEnv, Machine.runFrom_bind,
      Machine.runFrom_sample, Machine.runFrom_query, Machine.closeProgram_bind,
      Machine.closeProgram_sample, Machine.closeProgram_map, bind_map_left, map_bind,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
    have hinit : (corruptRouter ({1} : Finset (Fin 2)) (scheme.toProtocol κ {1})).init =
        (pure ({} : PlainSenderOT.State Msg) :
          ProbComp (corruptRouter ({1} : Finset (Fin 2)) (scheme.toProtocol κ {1})).State) := rfl
    erw [hinit, ProbComp.eval_pure, PMF.pure_bind]
    congr 1; funext r₀; congr 1; funext r₁
    have hsend : ((corruptRouter ({1} : Finset (Fin 2)) (scheme.toProtocol κ {1})).handle
        (Sum.inl (0, .send ⟨decide (r₀.val = 1), decide (r₁.val = 1)⟩))).run {} =
        (fun c => (none, ({ senderMsg := some c } : PlainSenderOT.State Msg))) <$>
          ProbOracleComp.sample (scheme.send κ (decide (r₀.val = 1)) (decide (r₁.val = 1))) := by
      simp [corruptRouter, PlainSenderOT.toProtocol, StateT.run, bind_pure_comp]
    erw [hsend, Machine.closeProgram_map, Machine.closeProgram_sample, ProbComp.eval_map]
    dsimp only [PMF.map]
    rw [PMF.bind_bind]
    congr 1; funext c
    simp only [Function.comp_def]
    erw [PMF.pure_bind]
    have hread : ((corruptRouter ({1} : Finset (Fin 2)) (scheme.toProtocol κ {1})).handle
        (Sum.inr (.inr .readMsg))).run ({ senderMsg := some c } : PlainSenderOT.State Msg) =
        pure (.inr (.msg (some c)), ({ senderMsg := some c } : PlainSenderOT.State Msg)) := rfl
    erw [hread, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind]
    dsimp only
    erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left, Machine.closeProgram_bind,
      Machine.closeProgram_sample, ProbComp.eval_bind, PMF.bind_bind]
    congr 1; funext g₀
    erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left, Machine.closeProgram_bind,
      Machine.closeProgram_sample, ProbComp.eval_bind, PMF.bind_bind]
    congr 1; funext g₁
    erw [Machine.runFrom_pure, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind]
  rw [hreal]
  let P : PMF (Bool × Bool × Bool × Bool) :=
    (do
      let r₀ ← ProbComp.unifFin 1
      let r₁ ← ProbComp.unifFin 1
      let m₀ := decide (r₀.val = 1)
      let m₁ := decide (r₁.val = 1)
      let c ← scheme.send κ m₀ m₁
      let g₀ ← scheme.recv κ c false
      let g₁ ← scheme.recv κ c true
      return (m₀, m₁, g₀, g₁)).eval
  have h0 : scheme.acceptGame κ false = P.map (fun x => decide (x.2.2.1 = x.1)) := by
    simp only [PlainSenderOT.acceptGame, P, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, Bool.false_eq_true, ↓reduceIte]
    congr 1; funext r₀; congr 1; funext r₁; congr 1; funext c
    congr 1; funext g₀
    exact (PMF.bind_const (scheme.recv κ c true).eval _).symm
  have h1 : scheme.acceptGame κ true = P.map (fun x => decide (x.2.2.2 = x.2.1)) := by
    simp only [PlainSenderOT.acceptGame, P, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, ↓reduceIte]
    congr 1; funext r₀; congr 1; funext r₁; congr 1; funext c
    rw [PMF.bind_comm (scheme.recv κ c false).eval]
    congr 1; funext g₁
    exact (PMF.bind_const (scheme.recv κ c false).eval _).symm
  have hboth :
      (do
        let r₀ ← ProbComp.unifFin 1
        let r₁ ← ProbComp.unifFin 1
        let m₀ := decide (r₀.val = 1)
        let m₁ := decide (r₁.val = 1)
        let c ← scheme.send κ m₀ m₁
        let g₀ ← scheme.recv κ c false
        let g₁ ← scheme.recv κ c true
        return decide (g₀ = m₀ ∧ g₁ = m₁)).eval =
      P.map (fun x => decide (x.2.2.1 = x.1 ∧ x.2.2.2 = x.2.1)) := by
    simp only [P, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
  rw [hboth, PlainSenderOT.acceptProb, PlainSenderOT.acceptProb, h0, h1]
  have hsum_le : ∀ (f g : Bool × Bool × Bool × Bool → Bool),
      (Game.succProbability (P.map f) : ℝ) + Game.succProbability (P.map g) - 1 ≤
        Game.succProbability (P.map (fun x => f x && g x)) := by
    intro f g
    have hsucc_eq : ∀ (h : Bool × Bool × Bool × Bool → Bool),
        (Game.succProbability (P.map h) : ℝ) =
          ∑ x : Bool × Bool × Bool × Bool, if h x = true then (P x).toReal else 0 := by
      intro h
      rw [Game.coe_succProbability, PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl fun x _ => ?_
        cases hhx : h x
        · simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte, ENNReal.toReal_zero]
        · simp only [↓reduceIte]
      · intro x _
        split_ifs
        · exact P.apply_ne_top x
        · exact ENNReal.zero_ne_top
    have hone : (∑ x : Bool × Bool × Bool × Bool, (P x).toReal) = 1 := by
      have htsum : (∑ x : Bool × Bool × Bool × Bool, P x) = 1 := by
        simpa only [tsum_fintype] using P.tsum_coe
      have hsum := ENNReal.toReal_sum (s := Finset.univ) (f := P) (fun x _ => P.apply_ne_top x)
      rw [htsum, ENNReal.toReal_one] at hsum
      exact hsum.symm
    rw [hsucc_eq f, hsucc_eq g, hsucc_eq (fun x => f x && g x), ← hone]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    cases f x <;> cases g x <;> simp [ENNReal.toReal_nonneg]
  simpa only [Bool.decide_and] using
    hsum_le (fun x => decide (x.2.2.1 = x.1)) (fun x => decide (x.2.2.2 = x.2.1))

private noncomputable def coinBoolPMF : PMF Bool :=
  (ProbComp.unifFin 1).eval.map (fun r => decide (r.val = 1))

private theorem coinBoolPMF_apply (b : Bool) : coinBoolPMF b = (1 / 2 : ℝ≥0∞) := by
  simp only [coinBoolPMF, ProbComp.eval_unifFin, PMF.map_apply,
    Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [tsum_fintype, Fin.sum_univ_two]
  cases b <;> norm_num

private def otGuessMatch (m₀ m₁ : Bool) : Option (Bool × Bool) → Bool
  | some (g₀, g₁) => decide (g₀ = m₀ ∧ g₁ = m₁)
  | none => false

private theorem succProb_coin_guess_le_half {α : Type} (view : Bool → PMF α)
    (evalRes : α → ProbComp (Option (Bool × Bool)))
    (matchFn : Bool → Bool → Option (Bool × Bool) → Bool)
    (hbound : ∀ s res,
      (∑' u : Bool, coinBoolPMF u * if true = matchFn s u res then 1 else 0) ≤ (1 / 2 : ℝ≥0∞)) :
    Game.succProbability (do
      let s ← coinBoolPMF
      let a ← view s
      let res ← (evalRes a).eval
      let u ← coinBoolPMF
      return matchFn s u res) ≤ (1 / 2 : ℝ≥0) := by
  simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  refine succProbability_bind_le _ _ _ fun s => ?_
  refine succProbability_bind_le _ _ _ fun a => ?_
  refine succProbability_bind_le _ _ _ fun res => ?_
  simp only [Game.succProbability, PMF.bind_apply, PMF.pure_apply]
  convert ENNReal.toNNReal_mono (b := (1 / 2 : ℝ≥0∞)) (by norm_num) (hbound s res)
  rw [← ENNReal.coe_inj, ENNReal.coe_toNNReal (by norm_num)]
  norm_num

private theorem succProb_post_selected {α : Type} (κ : ℕ) (b : Bool) (ab : Bool)
    (prog : ProbOracleComp
      (protocolSpec 2 (OTInput Bool) (OTOutput Bool) (RoutedNetQ 2 (OTInput Bool) OTBackdoor)
        (RoutedNetR (OTOutput Bool) OTBackdoorReply)) α)
    (evalRes : α → ProbComp (Option (Bool × Bool))) :
    Game.succProbability (do
      let r₀ ← (ProbComp.unifFin 1).eval
      let r₁ ← (ProbComp.unifFin 1).eval
      let m₀ := decide (r₀.val = 1)
      let m₁ := decide (r₁.val = 1)
      let a ← (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom prog
          { senderMsgs := some ⟨m₀, m₁⟩, receiverChoice := some b,
            delivered := false, aborted := ab })).eval
      let res ← (evalRes a).eval
      return otGuessMatch m₀ m₁ res) ≤ (1 / 2 : ℝ≥0) := by
  let view : Bool → PMF α := fun s =>
    (Prod.fst <$> Machine.closeProgram
      ((fotSelectedView s).runFrom prog ⟨false, ab⟩)).eval
  have hfactor : ∀ m₀ m₁ : Bool,
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom prog
          { senderMsgs := some ⟨m₀, m₁⟩, receiverChoice := some b,
            delivered := false, aborted := ab })).eval =
      view (if b then m₁ else m₀) := fun m₀ m₁ => by
    rw [runFrom_fot_corruptReceiver κ ⟨m₀, m₁⟩ b prog ⟨false, ab⟩]
    repeat erw [Machine.closeProgram_map]
    repeat erw [Functor.map_map]
    cases b <;> rfl
  simp_rw [hfactor]
  cases b
  · have hcomm :
        ((ProbComp.unifFin 1).eval.bind fun r₀ =>
          (ProbComp.unifFin 1).eval.bind fun r₁ =>
          (view (decide (r₀.val = 1))).bind fun a =>
          (evalRes a).eval.bind fun res =>
          PMF.pure (otGuessMatch (decide (r₀.val = 1)) (decide (r₁.val = 1)) res)) =
        (coinBoolPMF.bind fun s =>
          (view s).bind fun a =>
          (evalRes a).eval.bind fun res =>
          coinBoolPMF.bind fun u =>
          PMF.pure (otGuessMatch s u res)) := by
      dsimp only [coinBoolPMF, PMF.map]
      rw [PMF.bind_bind]
      congr 1; funext r₀
      simp only [Function.comp_def, PMF.pure_bind]
      rw [PMF.bind_comm (ProbComp.unifFin 1).eval]
      congr 1; funext a
      rw [PMF.bind_comm (ProbComp.unifFin 1).eval]
      congr 1; funext res
      rw [PMF.bind_bind]
      simp only [PMF.pure_bind]
    simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      Bool.false_eq_true, ↓reduceIte] at hcomm ⊢
    rw [hcomm]
    refine succProb_coin_guess_le_half view evalRes otGuessMatch fun s res => ?_
    rw [tsum_bool]
    rcases res with _ | ⟨g₀, g₁⟩
    · simp [otGuessMatch]
    · cases h1 : decide (g₀ = s) <;> cases g₁ <;> simp [otGuessMatch, coinBoolPMF_apply, h1]
  · have hcomm :
        ((ProbComp.unifFin 1).eval.bind fun r₀ =>
          (ProbComp.unifFin 1).eval.bind fun r₁ =>
          (view (decide (r₁.val = 1))).bind fun a =>
          (evalRes a).eval.bind fun res =>
          PMF.pure (otGuessMatch (decide (r₀.val = 1)) (decide (r₁.val = 1)) res)) =
        (coinBoolPMF.bind fun s =>
          (view s).bind fun a =>
          (evalRes a).eval.bind fun res =>
          coinBoolPMF.bind fun u =>
          PMF.pure (otGuessMatch u s res)) := by
      rw [PMF.bind_comm (ProbComp.unifFin 1).eval]
      dsimp only [coinBoolPMF, PMF.map]
      rw [PMF.bind_bind]
      congr 1; funext r₁
      simp only [Function.comp_def, PMF.pure_bind]
      rw [PMF.bind_comm (ProbComp.unifFin 1).eval]
      congr 1; funext a
      rw [PMF.bind_comm (ProbComp.unifFin 1).eval]
      congr 1; funext res
      rw [PMF.bind_bind]
      simp only [PMF.pure_bind]
    simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      ↓reduceIte] at hcomm ⊢
    rw [hcomm]
    refine succProb_coin_guess_le_half view evalRes (fun s u => otGuessMatch u s) fun s res => ?_
    rw [tsum_bool]
    rcases res with _ | ⟨g₀, g₁⟩
    · simp [otGuessMatch]
    · cases g₀ <;> cases h2 : decide (g₁ = s) <;> simp [otGuessMatch, coinBoolPMF_apply, h2]

private theorem succProb_preChoice {α : Type} (κ : ℕ) (ab : Bool)
    (prog : ProbOracleComp
      (netSpec (RoutedNetQ 2 (OTInput Bool) OTBackdoor)
        (RoutedNetR (OTOutput Bool) OTBackdoorReply)) α)
    (evalRes : α → ProbComp (Option (Bool × Bool))) :
    Game.succProbability (do
      let r₀ ← (ProbComp.unifFin 1).eval
      let r₁ ← (ProbComp.unifFin 1).eval
      let m₀ := decide (r₀.val = 1)
      let m₁ := decide (r₁.val = 1)
      let a ← (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
          (liftNet prog)
          { senderMsgs := some ⟨m₀, m₁⟩, receiverChoice := none,
            delivered := false, aborted := ab })).eval
      let res ← (evalRes a).eval
      return otGuessMatch m₀ m₁ res) ≤ (1 / 2 : ℝ≥0) := by
  let R := netSpec (RoutedNetQ 2 (OTInput Bool) OTBackdoor)
    (RoutedNetR (OTOutput Bool) OTBackdoorReply)
  induction prog using OracleComp.induction generalizing ab with
  | pure a =>
    have hpure : ∀ m₀ m₁ : Bool,
        (Prod.fst <$> Machine.closeProgram
          ((corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
            (liftNet (pure a))
            ({ senderMsgs := some ⟨m₀, m₁⟩, receiverChoice := none,
               delivered := false, aborted := ab } : OTState Bool))).eval =
          PMF.pure a := fun m₀ m₁ => by
      dsimp only [liftNet]
      erw [Machine.liftRightProgram_pure, Machine.runFrom_pure,
        Machine.closeProgram_pure, ProbComp.eval_map, PMF.pure_map]
    simp_rw [hpure]
    simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      PMF.pure_bind]
    have hcomm :
        ((ProbComp.unifFin 1).eval.bind fun r₀ =>
          (ProbComp.unifFin 1).eval.bind fun r₁ =>
          (evalRes a).eval.bind fun res =>
          PMF.pure (otGuessMatch (decide (r₀.val = 1)) (decide (r₁.val = 1)) res)) =
        ((evalRes a).eval.bind fun res =>
          coinBoolPMF.bind fun m₀ =>
          coinBoolPMF.bind fun m₁ =>
          PMF.pure (otGuessMatch m₀ m₁ res)) := by
      have hinner : ∀ r₀ : Fin 2,
          ((ProbComp.unifFin 1).eval.bind fun r₁ =>
            (evalRes a).eval.bind fun res =>
            PMF.pure (otGuessMatch (decide (r₀.val = 1)) (decide (r₁.val = 1)) res)) =
          ((evalRes a).eval.bind fun res =>
            (ProbComp.unifFin 1).eval.bind fun r₁ =>
            PMF.pure (otGuessMatch (decide (r₀.val = 1)) (decide (r₁.val = 1)) res)) :=
        fun r₀ => PMF.bind_comm (ProbComp.unifFin 1).eval (evalRes a).eval _
      simp_rw [hinner]
      rw [PMF.bind_comm (ProbComp.unifFin 1).eval (evalRes a).eval]
      dsimp only [coinBoolPMF, PMF.map]
      simp only [PMF.bind_bind, Function.comp_def, PMF.pure_bind]
    rw [hcomm]
    refine succProbability_bind_le _ _ _ fun res => ?_
    refine succProbability_bind_le _ _ _ fun m₀ => ?_
    simp only [Game.succProbability, PMF.bind_apply, PMF.pure_apply]
    have hsum : (∑' m₁ : Bool, coinBoolPMF m₁ *
        if true = otGuessMatch m₀ m₁ res then 1 else 0) ≤ (1 / 2 : ℝ≥0∞) := by
      rw [tsum_bool]
      rcases res with _ | ⟨g₀, g₁⟩
      · simp [otGuessMatch]
      · cases h1 : decide (g₀ = m₀) <;> cases g₁ <;>
          simp [otGuessMatch, coinBoolPMF_apply, h1]
    convert ENNReal.toNNReal_mono (b := (1 / 2 : ℝ≥0∞)) (by norm_num) hsum
    rw [← ENNReal.coe_inj, ENNReal.coe_toNNReal (by norm_num)]
    norm_num
  | query_bind q cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind]
    have hsplit : ∀ m₀ m₁ : Bool,
        (corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
          (liftNet (OracleComp.query q >>= cont))
          { senderMsgs := some ⟨m₀, m₁⟩, receiverChoice := none,
            delivered := false, aborted := ab } =
        (corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
          (liftNet (OracleComp.query q))
          { senderMsgs := some ⟨m₀, m₁⟩, receiverChoice := none,
            delivered := false, aborted := ab } >>= fun x =>
          (corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
            (liftNet (cont x.1)) x.2 := fun m₀ m₁ => by
      dsimp only [liftNet]
      erw [Machine.liftRightProgram_bind, Machine.runFrom_bind]
    simp_rw [hsplit]
    rcases q with k | q
    · have hcoin : ∀ m₀ m₁ : Bool,
          (Prod.fst <$> Machine.closeProgram
            ((corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
              (liftNet (OracleComp.query (spec := probOracleSpec R) (Sum.inl k)))
              { senderMsgs := some ⟨m₀, m₁⟩, receiverChoice := none,
                delivered := false, aborted := ab } >>= fun x =>
              (corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
                (liftNet (cont x.1)) x.2)).eval =
          ((ProbComp.unifFin k).eval.bind fun c =>
            (Prod.fst <$> Machine.closeProgram
              ((corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
                (liftNet (cont c))
                { senderMsgs := some ⟨m₀, m₁⟩, receiverChoice := none,
                  delivered := false, aborted := ab })).eval) := fun m₀ m₁ => by
        have hs : liftNet (n := 2) (In := OTInput Bool) (Out := OTOutput Bool)
            (OracleComp.query (spec := probOracleSpec R) (Sum.inl k)) =
            ProbOracleComp.sample (ProbComp.unifFin k) := by
          dsimp only [liftNet]
          rw [← Machine.liftRightProgram_sample (partySpec 2 (OTInput Bool) (OTOutput Bool))
            (R := R)]
          rfl
        rw [hs]
        erw [Machine.runFrom_sample, bind_map_left, Machine.closeProgram_bind,
          Machine.closeProgram_sample, ProbComp.eval_map, ProbComp.eval_bind, PMF.map_bind]
        congr 1; funext c
        exact (ProbComp.eval_map Prod.fst _).symm
      simp_rw [hcoin]
      have hcomm :
          ((ProbComp.unifFin 1).eval.bind fun r₀ =>
            (ProbComp.unifFin 1).eval.bind fun r₁ =>
            (ProbComp.unifFin k).eval.bind fun c =>
            (Prod.fst <$> Machine.closeProgram
              ((corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
                (liftNet (cont c))
                { senderMsgs := some ⟨decide (r₀.val = 1), decide (r₁.val = 1)⟩,
                  receiverChoice := none, delivered := false, aborted := ab })).eval.bind fun a =>
            (evalRes a).eval.bind fun res =>
            PMF.pure (otGuessMatch (decide (r₀.val = 1)) (decide (r₁.val = 1)) res)) =
          ((ProbComp.unifFin k).eval.bind fun c =>
            (ProbComp.unifFin 1).eval.bind fun r₀ =>
            (ProbComp.unifFin 1).eval.bind fun r₁ =>
            (Prod.fst <$> Machine.closeProgram
              ((corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
                (liftNet (cont c))
                { senderMsgs := some ⟨decide (r₀.val = 1), decide (r₁.val = 1)⟩,
                  receiverChoice := none, delivered := false, aborted := ab })).eval.bind fun a =>
            (evalRes a).eval.bind fun res =>
            PMF.pure (otGuessMatch (decide (r₀.val = 1)) (decide (r₁.val = 1)) res)) := by
        have hinner : ∀ r₀ : Fin 2,
            ((ProbComp.unifFin 1).eval.bind fun r₁ =>
              (ProbComp.unifFin k).eval.bind fun c =>
              (Prod.fst <$> Machine.closeProgram
                ((corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
                  (liftNet (cont c))
                  { senderMsgs := some ⟨decide (r₀.val = 1), decide (r₁.val = 1)⟩,
                    receiverChoice := none, delivered := false, aborted := ab })).eval.bind fun a =>
              (evalRes a).eval.bind fun res =>
              PMF.pure (otGuessMatch (decide (r₀.val = 1)) (decide (r₁.val = 1)) res)) =
            ((ProbComp.unifFin k).eval.bind fun c =>
              (ProbComp.unifFin 1).eval.bind fun r₁ =>
              (Prod.fst <$> Machine.closeProgram
                ((corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
                  (liftNet (cont c))
                  { senderMsgs := some ⟨decide (r₀.val = 1), decide (r₁.val = 1)⟩,
                    receiverChoice := none, delivered := false, aborted := ab })).eval.bind fun a =>
              (evalRes a).eval.bind fun res =>
              PMF.pure (otGuessMatch (decide (r₀.val = 1)) (decide (r₁.val = 1)) res)) :=
          fun r₀ => PMF.bind_comm (ProbComp.unifFin 1).eval (ProbComp.unifFin k).eval _
        simp_rw [hinner]
        exact PMF.bind_comm (ProbComp.unifFin 1).eval (ProbComp.unifFin k).eval _
      simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        PMF.bind_bind] at hcomm ⊢
      rw [hcomm]
      exact succProbability_bind_le _ _ _ fun c => ih c ab
    · rcases q with ⟨i, x⟩ | bq
      · fin_cases i
        · refine le_trans (le_of_eq (congrArg Game.succProbability ?_)) (ih (.inl none) ab)
          simp only [Probability.PMF.monad_bind_eq_bind]
          congr 1
        · cases x with
          | send _ =>
            refine le_trans (le_of_eq (congrArg Game.succProbability ?_)) (ih (.inl none) ab)
            simp only [Probability.PMF.monad_bind_eq_bind]
            congr 1
          | query =>
            let rep : RoutedNetR (OTOutput Bool) OTBackdoorReply :=
              .inl (if ab then some .aborted else none)
            refine le_trans (le_of_eq (congrArg Game.succProbability ?_)) (ih rep ab)
            simp only [Probability.PMF.monad_bind_eq_bind]
            congr 1
          | choose b =>
            refine le_trans (le_of_eq (congrArg Game.succProbability ?_))
              (succProb_post_selected κ b ab (liftNet (cont (.inl none))) evalRes)
            simp only [Probability.PMF.monad_bind_eq_bind]
            congr 1
      · cases bq
        · let rep : RoutedNetR (OTOutput Bool) OTBackdoorReply :=
            .inr (.status ⟨true, false, false, ab⟩)
          refine le_trans (le_of_eq (congrArg Game.succProbability ?_)) (ih rep ab)
          simp only [Probability.PMF.monad_bind_eq_bind]
          congr 1
        · refine le_trans (le_of_eq (congrArg Game.succProbability ?_)) (ih (.inr .ack) ab)
          simp only [Probability.PMF.monad_bind_eq_bind]
          congr 1
        · refine le_trans (le_of_eq (congrArg Game.succProbability ?_)) (ih (.inr .ack) true)
          simp only [Probability.PMF.monad_bind_eq_bind]
          congr 1

/-- **Ideal-world corrupted-receiver extraction bound:** against `fot Bool`, every simulator `S₁`
for `C = {1}` succeeds on `corruptOTReceiverEnv scheme` with probability at most `1 / 2`. -/
theorem succProbability_exec_fot_corruptOTReceiverEnv_le_half {Msg : Type}
    (scheme : PlainSenderOT Msg)
    (S₁ : ExecAdversary 2 (OTInput Bool) (OTOutput Bool) OTBackdoor OTBackdoorReply
      (RoutedNetQ 2 (OTInput Bool) (PlainOTNetQ Msg))
      (RoutedNetR (OTOutput Bool) (PlainOTNetR Msg)))
    (κ : ℕ) (z : List Bool) :
    Game.succProbability (exec (fot Bool).toProtocol S₁ {1}
      (corruptOTReceiverEnv scheme) κ z).eval ≤ (1 / 2 : ℝ≥0) := by
  let mkPair (sA : (S₁ κ {1}).State) :
      (execMachine (fot Bool).toProtocol S₁ κ {1}).State :=
    (sA, ({} : OTState Bool))
  have hcomp_init : (execMachine (fot Bool).toProtocol S₁ κ {1}).init.eval =
      ((S₁ κ {1}).init).eval.bind fun sA => PMF.pure (mkPair sA) := by
    dsimp only [execMachine, Machine.comp, liftAdversary, Machine.liftRight]
    have h0 : (corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).init =
        pure ({} : OTState Bool) := rfl
    erw [h0, pure_bind, ProbComp.eval_bind]
    congr 1
  dsimp only [exec, Machine.run, Machine.link]
  simp only [Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_bind]
  rw [hcomp_init, PMF.bind_bind]
  simp only [PMF.pure_bind]
  refine succProbability_bind_le _ _ _ fun st₀ => ?_
  let evalRes :
      (RoutedNetR (OTOutput Bool) (PlainOTNetR Msg) × (S₁ κ {1}).State) →
        ProbComp (Option (Bool × Bool))
    | (.inr (.msg (some c)), _) => do
      let g₀ ← scheme.recv κ c false
      let g₁ ← scheme.recv κ c true
      return some (g₀, g₁)
    | _ => pure none
  have hbound := succProb_preChoice κ false (((S₁ κ {1}).handle (.inr .readMsg)).run st₀) evalRes
  refine le_trans (le_of_eq ?_) hbound
  simp only [corruptOTReceiverEnv, Machine.runFrom_bind, Machine.runFrom_sample,
    Machine.runFrom_query, Machine.closeProgram_bind, Machine.closeProgram_sample,
    Machine.closeProgram_map, bind_map_left, map_bind, ProbComp.eval_bind, ProbComp.eval_map,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  refine congrArg Game.succProbability
    (congrArg (PMF.bind (ProbComp.unifFin 1).eval)
      (funext fun r₀ => congrArg (PMF.bind (ProbComp.unifFin 1).eval) (funext fun r₁ => ?_)))
  have hsend : ((execMachine (fot Bool).toProtocol S₁ κ {1}).handle
      (Sum.inl (0, .send ⟨decide (r₀.val = 1), decide (r₁.val = 1)⟩))).run
      (mkPair st₀) =
      pure (none, (st₀, { senderMsgs := some ⟨decide (r₀.val = 1), decide (r₁.val = 1)⟩,
                          receiverChoice := none, delivered := false, aborted := false })) := rfl
  erw [hsend, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind]
  have hread : ((execMachine (fot Bool).toProtocol S₁ κ {1}).handle
      (Sum.inr (.inr .readMsg))).run
      (st₀, { senderMsgs := some ⟨decide (r₀.val = 1), decide (r₁.val = 1)⟩,
              receiverChoice := none, delivered := false, aborted := false }) =
      Equiv.prodAssoc _ _ _ <$>
        (corruptRouter ({1} : Finset (Fin 2)) ((fot Bool).toProtocol κ {1})).runFrom
          (liftNet (((S₁ κ {1}).handle (.inr .readMsg)).run st₀))
          { senderMsgs := some ⟨decide (r₀.val = 1), decide (r₁.val = 1)⟩,
            receiverChoice := none, delivered := false, aborted := false } := rfl
  erw [hread, Machine.closeProgram_map, ProbComp.eval_map]
  dsimp only [PMF.map]
  simp only [PMF.bind_bind]
  congr 1; funext x
  rcases x with ⟨⟨netR, stA'⟩, sP'⟩
  erw [Function.comp_apply, Equiv.prodAssoc_apply, PMF.pure_bind, PMF.pure_bind]
  dsimp only
  rcases netR with _ | ⟨(_ | c) | _⟩
  · erw [Machine.runFrom_pure, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind]
    simp only [evalRes, ProbComp.eval_pure, PMF.pure_bind]
    rfl
  · erw [Machine.runFrom_pure, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind]
    simp only [evalRes, ProbComp.eval_pure, PMF.pure_bind]
    rfl
  · simp only [evalRes, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left,
      Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_bind, PMF.bind_bind]
    congr 1; funext g₀
    erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left,
      Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_bind, PMF.bind_bind]
    congr 1; funext g₁
    erw [Machine.runFrom_pure, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind]
    simp only [Function.comp_apply, otGuessMatch]
  · erw [Machine.runFrom_pure, Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_bind]
    simp only [evalRes, ProbComp.eval_pure, PMF.pure_bind]
    rfl

/-- **Concrete Impossibility of One-Message Plain-Model OT:** if `scheme.recv` has polynomial call
budget `pR` and at security parameter `κ` the error bound `ε` satisfies
`ε 1 (2 * pR + 4) κ + 3 / 2 < scheme.acceptProb κ false + scheme.acceptProb κ true`, then
`scheme.toProtocol` does not UC-realize `fot Bool` within `(g, ε)`. -/
theorem not_realizesWithin_fot_of_plainSenderOT {Msg : Type} [DecidableEq Msg]
    {scheme : PlainSenderOT Msg}
    {pR : Polynomial ℕ} (hR : ∀ κ c b, (scheme.recv κ c b).IsQueryBounded (pR.eval κ))
    (g : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) (κ : ℕ)
    (hgap : (ε 1 (2 * pR + 4) κ : ℝ) + 3 / 2 <
      scheme.acceptProb κ false + scheme.acceptProb κ true) :
    ¬ RealizesWithin scheme.toProtocol (fot Bool) g ε := by
  intro hreal
  obtain ⟨S, _, _, _, hadv⟩ := hreal _ _ (dummyAdversary 2 _ _) 1 (dummyAdversary_polyBounded 2 _ _)
  have h1 := hadv {1} (corruptOTReceiverEnv scheme) (2 * pR + 4)
    (corruptOTReceiverEnv_polyBounded hR) κ []
  have hreal_lb := acceptProb_add_sub_one_le_exec_real_corruptOTReceiverEnv scheme κ []
  have hideal_ub := succProbability_exec_fot_corruptOTReceiverEnv_le_half scheme S κ []
  rw [← NNReal.coe_le_coe] at h1 hideal_ub
  simp only [advantage, Game.coe_advantage, Game.coe_succProbability] at h1 hreal_lb
  have h1' := (abs_le.mp h1).2
  push_cast at h1' hideal_ub
  linarith

/-- **Impossibility of One-Message Plain-Model OT (`UC.Realizes`):** no one-message
sender-to-receiver plain-model OT scheme with polynomial-call-bounded recovery whose honest
acceptance probabilities eventually sum to at least `3 / 2 + c` (for `c > 0`) UC-realizes
`fot Bool`. -/
theorem not_realizes_fot_of_plainSenderOT {Msg : Type} [DecidableEq Msg]
    {scheme : PlainSenderOT Msg}
    {pR : Polynomial ℕ} (hR : ∀ κ c b, (scheme.recv κ c b).IsQueryBounded (pR.eval κ))
    {c : ℝ≥0} (hc : 0 < c)
    (hcomplete : ∀ᶠ κ in Filter.atTop,
      (3 / 2 : ℝ) + c ≤ scheme.acceptProb κ false + scheme.acceptProb κ true) :
    ¬ Realizes scheme.toProtocol (fot Bool) := by
  intro hreal
  obtain ⟨S, _, _, hν⟩ := hreal _ _ (dummyAdversary 2 _ _) 1 (dummyAdversary_polyBounded 2 _ _)
  obtain ⟨ν, hν_neg, hadv⟩ := hν (2 * pR + 4)
  have hbound : ∀ᶠ κ in Filter.atTop, c ≤ ν κ := by
    filter_upwards [hcomplete] with κ hcomp
    have h1 := hadv {1} (corruptOTReceiverEnv scheme) (corruptOTReceiverEnv_polyBounded hR) κ []
    have hreal_lb := acceptProb_add_sub_one_le_exec_real_corruptOTReceiverEnv scheme κ []
    have hideal_ub := succProbability_exec_fot_corruptOTReceiverEnv_le_half scheme S κ []
    rw [← NNReal.coe_le_coe] at h1 hideal_ub ⊢
    simp only [advantage, Game.coe_advantage, Game.coe_succProbability] at h1 hreal_lb
    have h1' := (abs_le.mp h1).2
    push_cast at h1' hideal_ub
    linarith
  exact not_negligible_const (ne_of_gt hc) (negligible_of_eventually_le hν_neg hbound)

end Cslib.Crypto.Protocols.UC
