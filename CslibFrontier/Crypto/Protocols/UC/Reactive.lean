/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Execution

/-!
# Reactive Nodes and Scheduler State for Push-Style UC Execution

This file defines the vocabulary and pure single-token scheduler transition for a push-style
execution of interactive machines, modeled after the single-token activation model of
[Canetti2020], §3.1.2 (JACM pp. 28:23–28:24) and §3.3.2, "Deleting ITIs" (JACM p. 28:33).

In this library's single-token push reading:
- A system has a fixed finite set of `m` nodes addressed by index `Fin m` rather than dynamically
  invoked ITI identities (`PushSystem`).
- Every external write (`Outcome.write`) is forced and reveals its sender index (`Envelope.sender`):
  the reveal-sender-id flag `r` of [Canetti2020] §3.1.2 is fixed to `1`.
- A `ControlFunction` reads the log of previously delivered envelopes rather than the full
  execution prefix and decides only whether a proposed write is allowed.
- Returning control to the initial node on `Outcome.yield` or on a non-initial node's
  `Outcome.halt` is a library convention (whereas returning to the initial node on a disallowed
  write follows [Canetti2020] §3.1.2, and ignoring activations of halted non-initial nodes follows
  [Canetti2020] §3.3.2, "Deleting ITIs").

The operational runner built on this vocabulary lives in
`CslibFrontier.Crypto.Protocols.UC.PushExecution`. Relating this push execution to the pull-style
execution of `CslibFrontier.Crypto.Protocols.UC.Execution`, as well as bounding running time rather
than step/call counts (computational polynomial-time UC execution), remain open under `#6043`.

## Main definitions

* `TapeName`: external write target tapes (`input`, `subroutineOutput`, `backdoor`).
* `Envelope`: a message in flight with sender, recipient, target tape, and payload.
* `Delivery`: what activates a node (`start`, `deliver`, `resume`).
* `Outcome`: how an activation ends (`write`, `yield`, `halt`).
* `ReactiveNode`: a closed `Machine` mapping `Delivery` to `Outcome`.
* `ControlFunction`: a predicate on the delivered log and a proposed envelope.
* `PushSystem`: a fixed `m`-node family, distinguished initial node, and control function.
* `TokenState`, `TokenState.initialFor`, `TokenState.next`: scheduler state and pure rule table
  (together with its `@[simp]` row equations `TokenState.next_write_of_control_eq_true`,
  `TokenState.next_write_of_control_eq_false`, `TokenState.next_yield`,
  `TokenState.next_halt_of_target_eq`, and `TokenState.next_halt_of_target_ne`).

## Main results

* `TokenState.halted_subset_next`, `TokenState.log_prefix_next`: monotonicity of halted nodes
  and append-only growth of the delivered log under `TokenState.next`.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], §3.1.2 (JACM pp. 28:23–28:24)
  and §3.3.2, "Deleting ITIs" (JACM p. 28:33).
-/

public section

namespace Cslib.Crypto.Protocols.UC.Push

/-- Library construction (no cited definition): the tape an external write targets (§3.1.2 of
[Canetti2020], JACM p. 28:23: "`t` is a tape name out of `{input, subroutine-output, backdoor}`").
-/
inductive TapeName where
  | input
  | subroutineOutput
  | backdoor
  deriving DecidableEq

instance : Fintype TapeName where
  elems := {.input, .subroutineOutput, .backdoor}
  complete t := by cases t <;> simp

/-- Library construction (no cited definition): a message in flight between the nodes `Fin m` of a
push system. The runner fills in `sender`, so the recipient always learns it (the reveal-sender-id
flag `r` of §3.1.2 of [Canetti2020], JACM p. 28:23, is fixed to `1`). -/
structure Envelope (m : ℕ) (Msg : Type) where
  /-- The node that emitted the write. -/
  sender : Fin m
  /-- The node targeted by the write. -/
  recipient : Fin m
  /-- The tape targeted by the write. -/
  tape : TapeName
  /-- The message payload. -/
  payload : Msg
  deriving DecidableEq

/-- Library construction (no cited definition): what activates a node: the initial node's auxiliary
input, a delivered envelope, or a return of control to the initial node. -/
inductive Delivery (m : ℕ) (Msg : Type) where
  /-- The initial activation of the initial node with auxiliary input `input`. -/
  | start (input : List Bool)
  /-- Delivery of an allowed external write `envelope` to its recipient. -/
  | deliver (envelope : Envelope m Msg)
  /-- Return of control to the initial node without a new message (after a disallowed write, a
  halted target, or a library-convention return from `yield` or a non-initial `halt`). -/
  | resume
  deriving DecidableEq

/-- Library construction (no cited definition): how an activation ends in this library's
single-token push reading: one external write (ending the activation and, if allowed, activating its
recipient; §3.1.2 of [Canetti2020], JACM p. 28:24), ending without a write (`yield`), or halting
with an output bit (`halt`). -/
inductive Outcome (m : ℕ) (Msg : Type) where
  /-- Perform one external write to `recipient`'s `tape` with `payload`. -/
  | write (recipient : Fin m) (tape : TapeName) (payload : Msg)
  /-- End the activation without an external write; control returns to the initial node by
  library convention. -/
  | yield
  /-- Halt the active node with output bit `output`; if this is the initial node the execution
  ends with `output` (§3.1.2 of [Canetti2020], JACM p. 28:23), otherwise the node is recorded as
  halted and control returns to the initial node by library convention. -/
  | halt (output : Bool)
  deriving DecidableEq

/-- Library construction (no cited definition): a reactive node in a fixed `m`-node push system: a
closed interactive machine (no oracle calls) whose activations take a `Delivery` and return an
`Outcome`. -/
abbrev ReactiveNode (m : ℕ) (Msg : Type) : Type 1 :=
  Machine OracleSpec.empty (netSpec (Delivery m Msg) (Outcome m Msg))

/-- Library construction (no cited definition): a control function over the log of previously
delivered envelopes, returning `true` to allow a proposed write or `false` to disallow it
(narrower than §3.1.2 of [Canetti2020], JACM p. 28:23, where the control function reads the entire
execution prefix and may be extended to redirect writes). -/
abbrev ControlFunction (m : ℕ) (Msg : Type) : Type :=
  List (Envelope m Msg) → Envelope m Msg → Bool

/-- Library construction (no cited definition): a push system comprising a fixed family of `m`
reactive nodes indexed by security parameter and node index, a distinguished initial node, and a
control function (a library reading of the pair `(I, C)` of §3.1.2 of [Canetti2020], JACM
p. 28:23, with the node set fixed in advance rather than dynamically invoked). -/
structure PushSystem (m : ℕ) (Msg : Type) : Type 1 where
  /-- The reactive node at index `i` for security parameter `κ`. -/
  node : ℕ → Fin m → ReactiveNode m Msg
  /-- The distinguished initial node. -/
  initial : Fin m
  /-- The control function deciding whether each external write is allowed. -/
  control : ControlFunction m Msg

/-- Library construction (no cited definition): the scheduler's bookkeeping for a single-token push
run: who is activated next and with what delivery, the log of delivered envelopes, the set of
halted non-initial nodes, and the initial node's output bit once it has halted. -/
structure TokenState (m : ℕ) (Msg : Type) where
  /-- The node holding the activation token next. -/
  target : Fin m
  /-- The delivery passed to `target` on its next activation. -/
  delivery : Delivery m Msg
  /-- The log of previously delivered envelopes, in delivery order. -/
  log : List (Envelope m Msg)
  /-- Non-initial nodes that have halted. -/
  halted : Finset (Fin m)
  /-- The execution's final output bit once the initial node has halted, or `none` while
  running. -/
  output : Option Bool

/-- Library construction (no cited definition): the initial scheduler state for initial node `i`
and auxiliary input `z`: `i` is activated with `.start z`, the delivered log and halted set are
empty, and no output has been produced. -/
@[expose] def TokenState.initialFor {m : ℕ} {Msg : Type} (i : Fin m) (z : List Bool) :
    TokenState m Msg where
  target := i
  delivery := .start z
  log := []
  halted := ∅
  output := none

/-- Library construction (no cited definition): pure scheduler transition applying the active node
`ts.target`'s `Outcome` in push system `S` (in this library's push reading of [Canetti2020], §3.1.2
(JACM pp. 28:23–28:24) and §3.3.2, "Deleting ITIs" (JACM p. 28:33); narrower in fixed index
addressing, eager initialization, forced sender-revealing writes, and a log-based control function):
- `write r t p` allowed by `S.control`: the envelope `e` is appended to `ts.log` and `r` is
  activated next with `.deliver e` (step 1a, §3.1.2 of [Canetti2020], JACM p. 28:24).
- `write r t p` disallowed by `S.control`: the write is not carried out and the initial node is
  activated next with `.resume` (§3.1.2 of [Canetti2020], JACM p. 28:23).
- `yield`: the initial node is activated next with `.resume` (library convention).
- `halt b` by the initial node: execution ends with `output := some b` (§3.1.2 of [Canetti2020],
  JACM p. 28:23).
- `halt b` by a non-initial node: `ts.target` is recorded in `ts.halted` (so later activations
  perform no operation per §3.3.2, "Deleting ITIs", of [Canetti2020], JACM p. 28:33) and the initial
  node is activated next with `.resume` (library convention). -/
@[expose] def TokenState.next {m : ℕ} {Msg : Type} (S : PushSystem m Msg)
    (ts : TokenState m Msg) : Outcome m Msg → TokenState m Msg
  | .write r t p =>
    let e : Envelope m Msg := ⟨ts.target, r, t, p⟩
    if S.control ts.log e then
      { ts with target := r, delivery := .deliver e, log := ts.log ++ [e] }
    else
      { ts with target := S.initial, delivery := .resume }
  | .yield =>
    { ts with target := S.initial, delivery := .resume }
  | .halt b =>
    if ts.target = S.initial then
      { ts with output := some b }
    else
      { ts with target := S.initial, delivery := .resume, halted := insert ts.target ts.halted }

variable {m : ℕ} {Msg : Type}

/-- Library infrastructure (no cited result): rule-table equation for an allowed write. -/
@[simp] theorem TokenState.next_write_of_control_eq_true (S : PushSystem m Msg)
    (ts : TokenState m Msg) (r : Fin m) (t : TapeName) (p : Msg)
    (h : S.control ts.log ⟨ts.target, r, t, p⟩ = true) :
    ts.next S (.write r t p) =
      { ts with
        target := r
        delivery := .deliver ⟨ts.target, r, t, p⟩
        log := ts.log ++ [⟨ts.target, r, t, p⟩] } := by
  simp [TokenState.next, h]

/-- Library infrastructure (no cited result): rule-table equation for a disallowed write. -/
@[simp] theorem TokenState.next_write_of_control_eq_false (S : PushSystem m Msg)
    (ts : TokenState m Msg) (r : Fin m) (t : TapeName) (p : Msg)
    (h : S.control ts.log ⟨ts.target, r, t, p⟩ = false) :
    ts.next S (.write r t p) = { ts with target := S.initial, delivery := .resume } := by
  simp [TokenState.next, h]

/-- Library infrastructure (no cited result): rule-table equation for `Outcome.yield`. -/
@[simp] theorem TokenState.next_yield (S : PushSystem m Msg) (ts : TokenState m Msg) :
    ts.next S .yield = { ts with target := S.initial, delivery := .resume } := rfl

/-- Library infrastructure (no cited result): rule-table equation for the initial node halting. -/
@[simp] theorem TokenState.next_halt_of_target_eq (S : PushSystem m Msg)
    (ts : TokenState m Msg) (b : Bool) (h : ts.target = S.initial) :
    ts.next S (.halt b) = { ts with output := some b } := by
  simp [TokenState.next, h]

/-- Library infrastructure (no cited result): rule-table equation for a non-initial node
halting. -/
@[simp] theorem TokenState.next_halt_of_target_ne (S : PushSystem m Msg)
    (ts : TokenState m Msg) (b : Bool) (h : ts.target ≠ S.initial) :
    ts.next S (.halt b) =
      { ts with
        target := S.initial
        delivery := .resume
        halted := insert ts.target ts.halted } := by
  simp [TokenState.next, h]

/-- Library infrastructure (no cited result): `TokenState.next` never removes a node from
`halted`. -/
theorem TokenState.halted_subset_next (S : PushSystem m Msg) (ts : TokenState m Msg)
    (a : Outcome m Msg) : ts.halted ⊆ (ts.next S a).halted := by
  cases a with
  | write r t p =>
    simp only [TokenState.next]
    split_ifs <;> exact Finset.Subset.refl _
  | yield => exact Finset.Subset.refl _
  | halt b =>
    simp only [TokenState.next]
    split_ifs
    · exact Finset.Subset.refl _
    · exact Finset.subset_insert _ _

/-- Library infrastructure (no cited result): `TokenState.next` only appends to `log`. -/
theorem TokenState.log_prefix_next (S : PushSystem m Msg) (ts : TokenState m Msg)
    (a : Outcome m Msg) : ts.log <+: (ts.next S a).log := by
  cases a with
  | write r t p =>
    simp only [TokenState.next]
    split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_rfl
  | yield => exact List.prefix_rfl
  | halt b =>
    simp only [TokenState.next]
    split_ifs <;> exact List.prefix_rfl

end Cslib.Crypto.Protocols.UC.Push
