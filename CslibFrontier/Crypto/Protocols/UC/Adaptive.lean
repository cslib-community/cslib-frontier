/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Emulation
public import CslibFrontier.Crypto.Protocols.UC.Linking

/-!
# Adaptive corruptions in the UC execution

This module extends the UC execution of `CslibFrontier.Crypto.Protocols.UC.Execution` with
adaptive party corruptions (`CorruptionMode.adaptive`) and the distinction between erasing and
non-erasing parties (`PartyMemory.erasing` versus `PartyMemory.nonErasing`), following Section 7.1
(p. 28:69) and Section 7.1.1 (p. 28:71) of [Canetti2020] (J. ACM pagination; ePrint p. 74).

## Modelling decisions

* **Structures, not tuples.** Domain records (`AdaptiveProtocol`, `CorruptionReport`,
  `AdaptiveRouterState`, `AdaptiveAdversary`) are structures with named fields; network queries and
  replies use the dedicated inductive types `AdaptiveNetQ` and `AdaptiveNetR`, and environment
  party-side queries use `AdaptivePartyQ`.
* **When corruption happens (`CorruptionMode`).** Under `.static`, initial corruptions `C₀` occur
  at invocation via `AdaptiveProtocol.onCorrupt`, and any later `.corrupt i` query for
  `i ∉ corrupted` is ignored with no state change ("a corruption message is considered only if it
  is delivered in the very next activation. Later corruption messages are ignored",
  [Canetti2020], Section 7.1.1, p. 28:71). Under `.adaptive`, any party may be corrupted mid-run.
* **What corruption exposes (`PartyMemory`).** `PartyMemory` is a property of the protocol, not of
  the adversary, matching [Canetti2020], Section 7.1.1, p. 28:71, where no trusted erasures are
  modeled by restricting to write-once protocols ("protocols where each data cell can be written to
  at most once"). Here erasure is modeled by *exposure* rather than write-once memory cells:
  `adaptiveRouter` records a per-activation snapshot `P.view κ j s'` in `trace j` after `init` and
  after every activation of `P.machine κ`. Upon corruption of party `i`, `CorruptionReport` returns
  `current := P.view κ i inner` and `history := some (trace i)` when `P.memory = .nonErasing`, or
  `history := none` when `P.memory = .erasing`. A write-once party can always reconstruct every
  past snapshot, and `trace i` exposes exactly that oldest-first sequence of snapshots.
* **Randomness and snapshot granularity.** A party's randomness is exposed exactly to the extent
  that the protocol retains it in the state read by `view`; a protocol wanting random-tape semantics
  samples its tape in `init` and keeps it in state. Coins sampled and discarded within a single
  activation are never exposed, even for `.nonErasing`, because snapshots are taken between
  activations (matching the activation-level phrasing "In an activation due to an incoming input or
  subroutine-output, the shell sends the entire local state to the adversary", [Canetti2020],
  Section 7.1.1, p. 28:71).
* **Environment corruption-status query (`AdaptivePartyQ.status`).** The environment has a
  read-only `.status` query returning the current set `corrupted : Finset (Fin n)`, corresponding to
  the corruption-aggregation machine's "Report corruption status" interface ([Canetti2020],
  Section 7.1, p. 28:69). Without it, a simulator could corrupt different parties unobserved.
* **Ideal functionalities (`IdealFunctionality.toAdaptive`).** An ideal functionality is embedded
  with `memory := .erasing` and a caller-supplied leakage map `reveal`. In [Canetti2020],
  Section 7.1, p. 28:69, an ideal functionality's internal state belongs to no party: on corruption,
  it reveals only what its code specifies ("standard `f`-revealing corruption"), and a dummy
  party's own memory is only its I/O. Marking ideal protocols `.erasing` is a modelling choice
  justified by this.
* **Adversary class and epsilon convention.** As in `CslibFrontier.Crypto.Protocols.UC.Execution`
  and `CslibFrontier.Crypto.Protocols.UC.Emulation`, all participants are statistical and
  interaction-bounded (`Machine.IsBounded` counts oracle calls and private samples per activation,
  not running time). `AdaptiveAdversary.PolyBounded` bounds the per-activation calls of
  `A.machine κ` by a polynomial in `κ`, while `A.initial : ℕ → Finset (Fin n)` is unconstrained.
  `AdaptiveEmulatesWithin` and `AdaptiveEmulates` are therefore adaptations of Section 7.1.1 to the
  call-bounded statistical model, not theorems of [Canetti2020] (which uses PPT machines and states
  no theorem in Section 7.1.1).

## Scope

Universal composition under adaptive corruption (the adaptive analogue of `UC.Emulates.compose`),
multiple sessions, mobile/proactive corruption, passive corruption as a separate mode, subroutine
corruption paths, PPT adversaries, and computational commitments ([CanettiFischlin2001],
Theorems 8 and 11) are out of scope here. Existing static definitions in
`CslibFrontier.Crypto.Protocols.UC.Execution`, `Emulation`, `DummyAdversary`, and `Composition` are
unchanged.

## Main definitions

* `Cslib.Crypto.Protocols.UC.CorruptionMode`, `Cslib.Crypto.Protocols.UC.PartyMemory`:
  when corruption happens (`.static` vs `.adaptive`) and what is exposed (`.erasing` vs
  `.nonErasing`).
* `Cslib.Crypto.Protocols.UC.AdaptiveProtocol`, `Cslib.Crypto.Protocols.UC.CorruptionReport`,
  `Cslib.Crypto.Protocols.UC.AdaptiveRouterState`: adaptive protocols, corruption reports, and
  router state.
* `Cslib.Crypto.Protocols.UC.AdaptivePartyQ`, `Cslib.Crypto.Protocols.UC.adaptivePartySpec`,
  `Cslib.Crypto.Protocols.UC.AdaptiveNetQ`, `Cslib.Crypto.Protocols.UC.AdaptiveNetR`,
  `Cslib.Crypto.Protocols.UC.adaptiveProtocolSpec`, `Cslib.Crypto.Protocols.UC.adaptiveExecSpec`:
  ports of the adaptive UC execution.
* `Cslib.Crypto.Protocols.UC.adaptiveRouter`, `Cslib.Crypto.Protocols.UC.AdaptiveAdversary`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEnvironment`,
  `Cslib.Crypto.Protocols.UC.Environment.toAdaptive`,
  `Cslib.Crypto.Protocols.UC.IdealFunctionality.toAdaptive`: participants and adaptive routing.
* `Cslib.Crypto.Protocols.UC.liftAdaptiveNet`, `Cslib.Crypto.Protocols.UC.liftAdaptiveAdversary`,
  `Cslib.Crypto.Protocols.UC.adaptiveExecMachine`, `Cslib.Crypto.Protocols.UC.adaptiveExec`,
  `Cslib.Crypto.Protocols.UC.adaptiveAdvantage`: the adaptive execution experiment and advantage.
* `Cslib.Crypto.Protocols.UC.AdaptiveProtocol.PolyBounded`,
  `Cslib.Crypto.Protocols.UC.AdaptiveAdversary.PolyBounded`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEnvironment.PolyBounded`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesWithin`, `Cslib.Crypto.Protocols.UC.AdaptiveEmulates`:
  call budgets and adaptive UC emulation.
* `Cslib.Crypto.Protocols.UC.AdaptiveProtocol.toStatic`,
  `Cslib.Crypto.Protocols.UC.AdaptiveAdversary.ofStatic`: embedding an adaptive protocol and a
  static adversary into the static/adaptive interfaces.

## Main results

* `Cslib.Crypto.Protocols.UC.adaptiveAdvantage_self`,
  `Cslib.Crypto.Protocols.UC.adaptiveAdvantage_comm`,
  `Cslib.Crypto.Protocols.UC.adaptiveAdvantage_triangle`: the adaptive advantage is a pseudometric.
* `Cslib.Crypto.Protocols.UC.Environment.PolyBounded.toAdaptive`: embedding a static environment
  preserves its call budget.
* `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesWithin.mono`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesWithin.refl`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesWithin.trans`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesWithin.emulates`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulates.refl`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulates.trans`: reflexivity, transitivity, and error
  monotonicity of adaptive UC emulation.
* `Cslib.Crypto.Protocols.UC.adaptiveExec_static_eq_adaptive_of_noCorrupt`,
  `Cslib.Crypto.Protocols.UC.adaptiveExec_static_ofStatic`,
  `Cslib.Crypto.Protocols.UC.adaptiveExec_adaptive_ofStatic`: static execution as a special case
  of adaptive execution.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], J. ACM 67(5), Art. 28, 2020:
  Section 7.1 (p. 28:69; ePrint p. 74) for corruption messages and the corruption-status query, and
  Section 7.1.1 (p. 28:71) for Byzantine state exposure, non-erasing ("write once") protocols, and
  static corruption as a restricted case.
* [R. Canetti, M. Fischlin, *Universally Composable Commitments*][CanettiFischlin2001], CRYPTO 2001
  (ePrint 2001/055): p. 5, p. 13, Theorem 8 (p. 20), and Theorem 11 (p. 26), motivating the
  erasing vs non-erasing distinction (not formalized here).
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open Polynomial (eval)
open scoped NNReal

/-! ### Modes, protocols, reports, and ports -/

/-- When corruption may occur during an execution: either only at invocation (`static`) or at any
time (`adaptive`) ([Canetti2020], Section 7.1.1, p. 28:71). -/
inductive CorruptionMode : Type
  | static
  | adaptive
  deriving DecidableEq, Repr

/-- Whether a protocol's parties erase past local state (`erasing`) or retain and expose their full
per-activation view history on corruption (`nonErasing`, capturing the write-once restriction of
[Canetti2020], Section 7.1.1, p. 28:71). -/
inductive PartyMemory : Type
  | erasing
  | nonErasing
  deriving DecidableEq, Repr

/-- An `n`-party protocol equipped for adaptive corruption: a closed machine per security
parameter `κ`, a per-party local view projection `view` (including any retained coins), a state
transition `onCorrupt` applied when party `i` is corrupted, and a memory model `memory`. -/
structure AdaptiveProtocol (n : ℕ) (In Out NetQ NetR View : Type) : Type 1 where
  /-- The protocol machine at security parameter `κ`. -/
  machine : ℕ → Machine OracleSpec.empty (protocolSpec n In Out NetQ NetR)
  /-- The local state view of party `i` extracted from the protocol state. -/
  view : (κ : ℕ) → Fin n → (machine κ).State → View
  /-- The protocol's own reaction when party `i` is corrupted (replacing `π κ C`'s dependence on
  `C` in static `Protocol`). -/
  onCorrupt : (κ : ℕ) → Fin n → (machine κ).State → (machine κ).State
  /-- Whether past views are erased or retained and exposed on corruption. -/
  memory : PartyMemory

/-- The corruption report returned to the adversary when corrupting party `i`: its `current` view
and, for `.nonErasing` protocols, the oldest-first `history` of snapshots since initialization. -/
structure CorruptionReport (View : Type) : Type where
  /-- Party `i`'s current view at corruption. -/
  current : View
  /-- Oldest-first sequence of snapshots since initialization (`some` iff `.nonErasing`). -/
  history : Option (List View)
  deriving DecidableEq, Repr

/-- The state maintained by `adaptiveRouter`: the inner protocol state, the currently `corrupted`
parties, and the per-party `trace` of oldest-first view snapshots. -/
structure AdaptiveRouterState (S View : Type) (n : ℕ) : Type where
  /-- The inner protocol machine's state. -/
  inner : S
  /-- The set of currently corrupted parties. -/
  corrupted : Finset (Fin n)
  /-- Per-party oldest-first snapshot history recorded at `init` and after each inner activation. -/
  trace : Fin n → List View

/-- Environment-side queries to the party and corruption-status interface: `.party i x` activates
party `i` with input `x`, and `.status` queries the current set of corrupted parties
([Canetti2020], Section 7.1, p. 28:69). -/
inductive AdaptivePartyQ (n : ℕ) (In : Type) : Type
  | party (i : Fin n) (x : In)
  | status
  deriving DecidableEq, Repr

/-- Reply types for `AdaptivePartyQ`: party activations return `Option Out`, and `.status` returns
`Finset (Fin n)`. -/
@[expose] def adaptivePartySpec (n : ℕ) (In Out : Type) : AdaptivePartyQ n In → Type
  | .party _ _ => Option Out
  | .status => Finset (Fin n)

/-- Adversary-side queries behind `adaptiveRouter`: drive a corrupted party (`party`), corrupt a
party (`corrupt`), or send a protocol network query (`net`). -/
inductive AdaptiveNetQ (n : ℕ) (In NetQ : Type) : Type
  | party (i : Fin n) (x : In)
  | corrupt (i : Fin n)
  | net (q : NetQ)
  deriving DecidableEq, Repr

/-- Adversary-side replies behind `adaptiveRouter`, matching `AdaptiveNetQ`. -/
inductive AdaptiveNetR (Out NetR View : Type) : Type
  | party (out : Option Out)
  | corrupt (report : Option (CorruptionReport View))
  | net (r : NetR)
  deriving DecidableEq, Repr

/-- The ports exported by `adaptiveRouter`: the environment's party/status port and the
adversary's routed network port. -/
abbrev adaptiveProtocolSpec (n : ℕ) (In Out NetQ NetR View : Type) :
    AdaptivePartyQ n In ⊕ AdaptiveNetQ n In NetQ → Type :=
  adaptivePartySpec n In Out ⊕ₒ netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)

/-- The ports seen by an adaptive environment: the party/status port and the adversary port. -/
abbrev adaptiveExecSpec (n : ℕ) (In Out AdvQ AdvR : Type) :
    AdaptivePartyQ n In ⊕ AdvQ → Type :=
  adaptivePartySpec n In Out ⊕ₒ netSpec AdvQ AdvR

/-! ### Adaptive router and participants -/

section Router

variable {n : ℕ} {In Out NetQ NetR View AdvQ AdvR : Type}

/-- Apply `P.onCorrupt κ i` in canonical order for every `i ∈ C₀` at initialization. -/
@[expose] def AdaptiveProtocol.applyInitialCorruptions
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (s : (P.machine κ).State) : (P.machine κ).State :=
  (List.finRange n).foldl (fun acc i => if i ∈ C₀ then P.onCorrupt κ i acc else acc) s

/-- Build the corruption report for party `i` from a router state. -/
@[expose] def AdaptiveProtocol.corruptionReport
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (i : Fin n)
    (s : AdaptiveRouterState (P.machine κ).State View n) : CorruptionReport View :=
  { current := P.view κ i s.inner
    history := if P.memory = .nonErasing then some (s.trace i) else none }

/-- Update the router state after an inner protocol activation by appending each party's view. -/
@[expose] def AdaptiveProtocol.recordSnapshot
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (s' : (P.machine κ).State)
    (corrupted : Finset (Fin n)) (trace : Fin n → List View) :
    AdaptiveRouterState (P.machine κ).State View n :=
  { inner := s'
    corrupted := corrupted
    trace := fun j => trace j ++ [P.view κ j s'] }

/-- The adaptive corruption router wrapping `P.machine κ` with initial corruptions `C₀`.
Initial corruptions apply `P.onCorrupt` at `init`. Environment party calls are dropped for
corrupted parties; adversary party calls are allowed only for corrupted parties; `.status` returns
`s.corrupted`; `.corrupt i` is ignored for `i ∉ s.corrupted` in `.static` mode and corrupts `i`
in `.adaptive` mode, returning a `CorruptionReport` respecting `P.memory`. -/
@[expose] def adaptiveRouter (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n)) :
    Machine OracleSpec.empty (adaptiveProtocolSpec n In Out NetQ NetR View) where
  State := AdaptiveRouterState (P.machine κ).State View n
  init := do
    let s₀ ← (P.machine κ).init
    let s₁ := P.applyInitialCorruptions κ C₀ s₀
    return { inner := s₁, corrupted := C₀, trace := fun i => [P.view κ i s₁] }
  handle
    | .inl (.party i x) => fun s =>
        if i ∈ s.corrupted then
          pure (none, s)
        else do
          let (out, s') ← ((P.machine κ).handle (.inl (i, x))).run s.inner
          pure (out, P.recordSnapshot κ s' s.corrupted s.trace)
    | .inl .status => fun s => pure (s.corrupted, s)
    | .inr (.party i x) => fun s =>
        if i ∈ s.corrupted then do
          let (out, s') ← ((P.machine κ).handle (.inl (i, x))).run s.inner
          pure (.party out, P.recordSnapshot κ s' s.corrupted s.trace)
        else
          pure (.party none, s)
    | .inr (.corrupt i) => fun s =>
        match mode with
        | .static =>
            if i ∈ s.corrupted then
              pure (.corrupt (some (P.corruptionReport κ i s)), s)
            else
              pure (.corrupt none, s)
        | .adaptive =>
            let s' : AdaptiveRouterState (P.machine κ).State View n :=
              if i ∈ s.corrupted then s
              else
                { inner := P.onCorrupt κ i s.inner
                  corrupted := insert i s.corrupted
                  trace := s.trace }
            pure (.corrupt (some (P.corruptionReport κ i s')), s')
    | .inr (.net q) => fun s => do
        let (r, s') ← ((P.machine κ).handle (.inr q)).run s.inner
        pure (.net r, P.recordSnapshot κ s' s.corrupted s.trace)

/-- An adversary (or simulator) in the adaptive execution: an initial corruption set `initial κ` at
invocation and an interactive machine talking to the routed network port
`AdaptiveNetQ`/`AdaptiveNetR`. Its internal state is generic. -/
structure AdaptiveAdversary (n : ℕ) (In Out NetQ NetR View AdvQ AdvR : Type) : Type 1 where
  /-- Parties corrupted immediately at invocation for security parameter `κ`. -/
  initial : ℕ → Finset (Fin n)
  /-- The adversary machine talking to `AdaptiveNetQ`/`AdaptiveNetR`. -/
  machine : ℕ →
    Machine (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) (netSpec AdvQ AdvR)

/-- An environment in the adaptive execution: a program with private coins interacting with the
party/status port and the adversary, outputting a bit. -/
abbrev AdaptiveEnvironment (n : ℕ) (In Out AdvQ AdvR : Type) : Type :=
  ℕ → List Bool → ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) Bool

/-- Embed a static `execSpec` program into `adaptiveExecSpec` by sending party calls to
`AdaptivePartyQ.party` and never querying `.status`. -/
@[expose] def liftPartyQuery {α : Type} (program : ProbOracleComp (execSpec n In Out AdvQ AdvR) α) :
    ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec (adaptiveExecSpec n In Out AdvQ AdvR))
        (Sum.inl k))
      fun q => match q with
        | .inl (i, x) => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR)
            (.inl (.party i x))
        | .inr a => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR) (.inr a))
    program

/-- Embed a static environment into `AdaptiveEnvironment` as one that never queries `.status`. -/
@[expose] def Environment.toAdaptive (Z : Environment n In Out AdvQ AdvR) :
    AdaptiveEnvironment n In Out AdvQ AdvR :=
  fun κ z => liftPartyQuery (Z κ z)

/-- Embed an `IdealFunctionality` as an `AdaptiveProtocol` with `memory := .erasing` and
`f`-revealing leakage `reveal` ([Canetti2020], Section 7.1, p. 28:69). Marking ideal protocols
`.erasing` models that `F`'s internal state belongs to no party and only `reveal` is exposed on
corruption. -/
@[expose] def IdealFunctionality.toAdaptive {BackQ BackR : Type}
    (F : IdealFunctionality n In Out BackQ BackR)
    (reveal : (κ : ℕ) → F.State → Fin n → View) :
    AdaptiveProtocol n In Out BackQ BackR View where
  machine κ := {
    State := F.State
    init := F.init κ ∅
    handle
      | .inl (i, x) => fun s => ProbOracleComp.sample ((F.onInput i x).run s)
      | .inr q => fun s => ProbOracleComp.sample ((F.onBackdoor q).run s) }
  view κ i s := reveal κ s i
  onCorrupt _ _ s := s
  memory := .erasing

end Router

/-! ### Execution and advantage -/

section Execution

variable {n : ℕ} {In Out Q R NetQ NetR View AdvQ AdvR : Type}
  {NetQ₁ NetR₁ View₁ NetQ₂ NetR₂ View₂ NetQ₃ NetR₃ View₃ : Type}

/-- Mirror of `UC.liftNet` for the adaptive left port `adaptivePartySpec n In Out` (which extends
`partySpec n In Out` with `.status`, so `UC.liftNet` does not apply directly). -/
@[expose] def liftAdaptiveNet {α : Type}
    (program : ProbOracleComp (netSpec Q R) α) :
    ProbOracleComp (adaptivePartySpec n In Out ⊕ₒ netSpec Q R) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (adaptivePartySpec n In Out ⊕ₒ netSpec Q R)) (Sum.inl k))
      fun q => ProbOracleComp.query (spec := adaptivePartySpec n In Out ⊕ₒ netSpec Q R) (.inr q))
    program

/-- Mirror of `UC.liftAdversary` for `adaptivePartySpec n In Out`. -/
@[expose] def liftAdaptiveAdversary (A : Machine (netSpec Q R) (netSpec AdvQ AdvR)) :
    Machine (adaptivePartySpec n In Out ⊕ₒ netSpec Q R) (adaptiveExecSpec n In Out AdvQ AdvR) where
  State := A.State
  init := A.init
  handle
    | .inl p => StateT.lift (ProbOracleComp.query
        (spec := adaptivePartySpec n In Out ⊕ₒ netSpec Q R) (.inl p))
    | .inr q => fun s => liftAdaptiveNet ((A.handle q).run s)

/-- The closed machine of an adaptive execution: `A` placed in front of `adaptiveRouter`. -/
@[expose] def adaptiveExecMachine (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ) :
    Machine OracleSpec.empty (adaptiveExecSpec n In Out AdvQ AdvR) :=
  (liftAdaptiveAdversary (A.machine κ)).comp (adaptiveRouter mode P κ (A.initial κ))

/-- The adaptive UC execution experiment: the environment's output bit when interacting with
`P` and `A` under `mode`, at security parameter `κ` and auxiliary input `z`. -/
@[expose] def adaptiveExec (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) : ProbComp Bool :=
  (adaptiveExecMachine mode P A κ).run (Z κ z)

/-- The advantage of `Z` in distinguishing `(P, A)` from `(Q, S)` under `mode`. Both worlds run
under the same `mode`, while each uses its own protocol's `memory`. -/
@[expose] noncomputable def adaptiveAdvantage (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR)
    (S : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂ AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) : NNReal :=
  Game.advantage (adaptiveExec mode P A Z κ z).eval (adaptiveExec mode Q S Z κ z).eval

/-- An adaptive execution cannot be distinguished from itself. -/
@[simp] theorem adaptiveAdvantage_self (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveAdvantage mode P P A A Z κ z = 0 :=
  Game.advantage_self _

/-- The adaptive distinguishing advantage is symmetric. -/
theorem adaptiveAdvantage_comm (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR)
    (S : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂ AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveAdvantage mode P Q A S Z κ z = adaptiveAdvantage mode Q P S A Z κ z :=
  Game.advantage_comm _ _

/-- The triangle inequality for adaptive advantage through an intermediate protocol and
adversary. -/
theorem adaptiveAdvantage_triangle (mode : CorruptionMode)
    (P₁ : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (P₂ : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (P₃ : AdaptiveProtocol n In Out NetQ₃ NetR₃ View₃)
    (A₁ : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR)
    (A₂ : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂ AdvQ AdvR)
    (A₃ : AdaptiveAdversary n In Out NetQ₃ NetR₃ View₃ AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveAdvantage mode P₁ P₃ A₁ A₃ Z κ z ≤
      adaptiveAdvantage mode P₁ P₂ A₁ A₂ Z κ z + adaptiveAdvantage mode P₂ P₃ A₂ A₃ Z κ z :=
  Game.advantage_triangle _ _ _

end Execution

/-! ### Budgets and adaptive emulation -/

section Budgets

variable {n : ℕ} {In Out NetQ NetR View AdvQ AdvR : Type}
  {NetQ₁ NetR₁ View₁ NetQ₂ NetR₂ View₂ NetQ₃ NetR₃ View₃ : Type}

/-- Every activation of `P.machine κ` makes at most `p.eval κ` calls. -/
@[expose] def AdaptiveProtocol.PolyBounded
    (P : AdaptiveProtocol n In Out NetQ NetR View) (p : Polynomial ℕ) : Prop :=
  ∀ κ, (P.machine κ).IsBounded (p.eval κ)

/-- Every activation of `A.machine κ` makes at most `p.eval κ` calls (`A.initial` is
unconstrained). -/
@[expose] def AdaptiveAdversary.PolyBounded
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (p : Polynomial ℕ) : Prop :=
  ∀ κ, (A.machine κ).IsBounded (p.eval κ)

/-- At security parameter `κ`, `Z` makes at most `p.eval κ` calls in total, regardless of the
auxiliary input `z`. -/
@[expose] def AdaptiveEnvironment.PolyBounded
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (p : Polynomial ℕ) : Prop :=
  ∀ κ z, (Z κ z).IsQueryBounded (p.eval κ)

theorem AdaptiveProtocol.PolyBounded.mono {P : AdaptiveProtocol n In Out NetQ NetR View}
    {p q : Polynomial ℕ} (h : P.PolyBounded p) (hpq : ∀ κ, p.eval κ ≤ q.eval κ) :
    P.PolyBounded q :=
  fun κ => (h κ).mono (hpq κ)

theorem AdaptiveAdversary.PolyBounded.mono
    {A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR} {p q : Polynomial ℕ}
    (h : A.PolyBounded p) (hpq : ∀ κ, p.eval κ ≤ q.eval κ) : A.PolyBounded q :=
  fun κ => (h κ).mono (hpq κ)

theorem AdaptiveEnvironment.PolyBounded.mono {Z : AdaptiveEnvironment n In Out AdvQ AdvR}
    {p q : Polynomial ℕ} (h : Z.PolyBounded p) (hpq : ∀ κ, p.eval κ ≤ q.eval κ) :
    Z.PolyBounded q :=
  fun κ z => (h κ z).mono (hpq κ)

/-- Lifting static queries into `adaptiveExecSpec` preserves query budgets. -/
theorem isQueryBounded_liftPartyQuery {α : Type}
    {program : ProbOracleComp (execSpec n In Out AdvQ AdvR) α} {m : ℕ}
    (h : program.IsQueryBounded m) :
    (liftPartyQuery program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  rcases q with k | (⟨i, x⟩ | a)
  · exact OracleComp.IsCostBounded.query _
  · exact OracleComp.IsCostBounded.query _
  · exact OracleComp.IsCostBounded.query _

/-- Embedding a static environment into `AdaptiveEnvironment` preserves its call budget. -/
theorem Environment.PolyBounded.toAdaptive {Z : Environment n In Out AdvQ AdvR}
    {p : Polynomial ℕ} (h : Z.PolyBounded p) : Z.toAdaptive.PolyBounded p :=
  fun κ z => isQueryBounded_liftPartyQuery (h κ z)

/-- Concrete adaptive UC emulation under `mode` (statistical, call-bounded adaptation of
[Canetti2020], Section 7.1.1, p. 28:71, not a theorem of the paper). Every adversary `A` with
per-activation call budget `pA` has a simulator `S` with per-activation call budget `pS` bounded by
`g` at `κ + pA.eval κ`, such that every environment `Z` with call budget `pZ` distinguishes
`(P, A)` from `(Q, S)` with advantage at most `ε pA pZ κ`. -/
@[expose] def AdaptiveEmulatesWithin (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (g : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) : Prop :=
  ∀ (AdvQ AdvR : Type) (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR)
    (pA : Polynomial ℕ), A.PolyBounded pA →
    ∃ (S : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂ AdvQ AdvR) (pS : Polynomial ℕ),
      S.PolyBounded pS ∧ SimPolyBound g pA pS ∧
        ∀ (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (pZ : Polynomial ℕ),
          Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
            adaptiveAdvantage mode P Q A S Z κ z ≤ ε pA pZ κ

/-- Asymptotic adaptive UC emulation under `mode` with negligible error (statistical, call-bounded
adaptation of [Canetti2020], Section 7.1.1, p. 28:71, not a theorem of the paper). -/
@[expose] def AdaptiveEmulates (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂) : Prop :=
  ∀ (AdvQ AdvR : Type) (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR)
    (pA : Polynomial ℕ), A.PolyBounded pA →
    ∃ (S : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂ AdvQ AdvR) (pS : Polynomial ℕ),
      S.PolyBounded pS ∧
        ∀ pZ : Polynomial ℕ, ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
          ∀ (Z : AdaptiveEnvironment n In Out AdvQ AdvR),
            Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
              adaptiveAdvantage mode P Q A S Z κ z ≤ ν κ

namespace AdaptiveEmulatesWithin

/-- A larger error bound is still an error bound. -/
theorem mono {mode : CorruptionMode} {P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    {g : Polynomial ℕ} {ε ε' : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : AdaptiveEmulatesWithin mode P Q g ε) (hε : ∀ pA pZ κ, ε pA pZ κ ≤ ε' pA pZ κ) :
    AdaptiveEmulatesWithin mode P Q g ε' := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hSg, hadv⟩ := h AdvQ AdvR A pA hA
  exact ⟨S, pS, hS, hSg, fun Z pZ hZ κ z => (hadv Z pZ hZ κ z).trans (hε pA pZ κ)⟩

/-- Every adaptive protocol emulates itself with zero error. -/
theorem refl (mode : CorruptionMode) (P : AdaptiveProtocol n In Out NetQ NetR View) :
    AdaptiveEmulatesWithin mode P P Polynomial.X (fun _ _ _ => 0) :=
  fun _ _ A pA hA => ⟨A, pA, hA, SimPolyBound.refl pA, fun Z _ _ κ z => by simp⟩

/-- Transitivity of concrete adaptive UC emulation. -/
theorem trans {mode : CorruptionMode} {P₁ : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {P₂ : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    {P₃ : AdaptiveProtocol n In Out NetQ₃ NetR₃ View₃}
    {g₁₂ g₂₃ : Polynomial ℕ} {ε₁₂ ε₂₃ : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h₁₂ : AdaptiveEmulatesWithin mode P₁ P₂ g₁₂ ε₁₂)
    (h₂₃ : AdaptiveEmulatesWithin mode P₂ P₃ g₂₃ ε₂₃)
    (hmono : ∀ p p' pZ κ, (∀ κ', p.eval κ' ≤ p'.eval κ') → ε₂₃ p pZ κ ≤ ε₂₃ p' pZ κ) :
    AdaptiveEmulatesWithin mode P₁ P₃ (g₂₃.comp (Polynomial.X + g₁₂))
      (fun pA pZ κ => ε₁₂ pA pZ κ + ε₂₃ (g₁₂.comp (Polynomial.X + pA)) pZ κ) := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S₂, pS₂, hS₂, hS₂g, hadv₁₂⟩ := h₁₂ AdvQ AdvR A pA hA
  obtain ⟨S₃, pS₃, hS₃, hS₃g, hadv₂₃⟩ := h₂₃ AdvQ AdvR S₂ pS₂ hS₂
  refine ⟨S₃, pS₃, hS₃, hS₂g.trans hS₃g, fun Z pZ hZ κ z => ?_⟩
  calc adaptiveAdvantage mode P₁ P₃ A S₃ Z κ z
      ≤ adaptiveAdvantage mode P₁ P₂ A S₂ Z κ z + adaptiveAdvantage mode P₂ P₃ S₂ S₃ Z κ z :=
        adaptiveAdvantage_triangle mode P₁ P₂ P₃ A S₂ S₃ Z κ z
    _ ≤ ε₁₂ pA pZ κ + ε₂₃ (g₁₂.comp (Polynomial.X + pA)) pZ κ :=
        add_le_add (hadv₁₂ Z pZ hZ κ z)
          ((hadv₂₃ Z pZ hZ κ z).trans (hmono _ _ pZ κ hS₂g.le_eval_comp))

/-- Concrete adaptive emulation whose errors are negligible for all budgets is asymptotic adaptive
emulation. -/
theorem emulates {mode : CorruptionMode} {P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂} {g : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : AdaptiveEmulatesWithin mode P Q g ε) (hε : ∀ pA pZ, Negligible (ε pA pZ)) :
    AdaptiveEmulates mode P Q := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, _, hadv⟩ := h AdvQ AdvR A pA hA
  exact ⟨S, pS, hS, fun pZ => ⟨ε pA pZ, hε pA pZ, fun Z hZ κ z => hadv Z pZ hZ κ z⟩⟩

end AdaptiveEmulatesWithin

namespace AdaptiveEmulates

/-- Every adaptive protocol emulates itself. -/
theorem refl (mode : CorruptionMode) (P : AdaptiveProtocol n In Out NetQ NetR View) :
    AdaptiveEmulates mode P P :=
  (AdaptiveEmulatesWithin.refl mode P).emulates fun _ _ => negligible_zero

/-- Asymptotic adaptive UC emulation is transitive. -/
theorem trans {mode : CorruptionMode} {P₁ : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {P₂ : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    {P₃ : AdaptiveProtocol n In Out NetQ₃ NetR₃ View₃}
    (h₁₂ : AdaptiveEmulates mode P₁ P₂) (h₂₃ : AdaptiveEmulates mode P₂ P₃) :
    AdaptiveEmulates mode P₁ P₃ := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S₂, pS₂, hS₂, hadv₁₂⟩ := h₁₂ AdvQ AdvR A pA hA
  obtain ⟨S₃, pS₃, hS₃, hadv₂₃⟩ := h₂₃ AdvQ AdvR S₂ pS₂ hS₂
  refine ⟨S₃, pS₃, hS₃, fun pZ => ?_⟩
  obtain ⟨ν₁₂, hν₁₂, h₁⟩ := hadv₁₂ pZ
  obtain ⟨ν₂₃, hν₂₃, h₂⟩ := hadv₂₃ pZ
  refine ⟨ν₁₂ + ν₂₃, hν₁₂.add hν₂₃, fun Z hZ κ z => ?_⟩
  exact (adaptiveAdvantage_triangle mode P₁ P₂ P₃ A S₂ S₃ Z κ z).trans
    (add_le_add (h₁ Z hZ κ z) (h₂ Z hZ κ z))

end AdaptiveEmulates

end Budgets

/-! ### Static corruption as a special case -/

section StaticSpecialCase

variable {n : ℕ} {In Out NetQ NetR View AdvQ AdvR : Type}

/-- Convert an adaptive protocol to a static `Protocol` by applying `P.onCorrupt` for `C` during
initialization. -/
@[expose] def AdaptiveProtocol.toStatic (P : AdaptiveProtocol n In Out NetQ NetR View) :
    Protocol n In Out NetQ NetR :=
  fun κ C => {
    State := (P.machine κ).State
    init := P.applyInitialCorruptions κ C <$> (P.machine κ).init
    handle := (P.machine κ).handle }

/-- Converting an adaptive protocol to a static one preserves its call budget. -/
theorem AdaptiveProtocol.PolyBounded.toStatic {P : AdaptiveProtocol n In Out NetQ NetR View}
    {p : Polynomial ℕ} (h : P.PolyBounded p) : P.toStatic.PolyBounded p := fun κ _C =>
  ⟨(OracleComp.isCostBounded_map_iff _ _ _).mpr (h κ).1, (h κ).2⟩

/-- Project an `AdaptiveNetR` reply back to `RoutedNetR` (ignoring `.corrupt`, which static
adversaries never send). -/
@[expose] def AdaptiveNetR.toRoutedNetR : AdaptiveNetR Out NetR View → RoutedNetR Out NetR
  | .party out => .inl out
  | .net r => .inr r
  | .corrupt _ => .inl none

/-- Translate a static adversary's network program into `AdaptiveNetQ`/`AdaptiveNetR`, sending
only `.party` and `.net` queries and never `.corrupt`. -/
@[expose] def liftStaticNetProgram {α : Type}
    (program : ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) α) :
    ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)))
        (Sum.inl k))
      fun q => match q with
        | .inl (i, x) => AdaptiveNetR.toRoutedNetR <$>
            ProbOracleComp.query
              (spec := netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))
              (.party i x)
        | .inr nq => AdaptiveNetR.toRoutedNetR <$>
            ProbOracleComp.query
              (spec := netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))
              (.net nq))
    program

/-- Lift a static `ExecAdversary` to an `AdaptiveAdversary` with initial corruption set `C` that
never sends `.corrupt`. -/
@[expose] def AdaptiveAdversary.ofStatic
    (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR) (C : ℕ → Finset (Fin n)) :
    AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR where
  initial := C
  machine κ := {
    State := (A κ (C κ)).State
    init := (A κ (C κ)).init
    handle q s := liftStaticNetProgram (((A κ (C κ)).handle q).run s) }

private theorem isQueryBounded_liftStaticNetProgram {α : Type}
    {program : ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) α}
    {m : ℕ} (h : program.IsQueryBounded m) :
    (liftStaticNetProgram (View := View) program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  rcases q with k | (⟨i, x⟩ | nq)
  · exact OracleComp.IsCostBounded.query _
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- Lifting a static adversary preserves its call budget. -/
theorem Adversary.PolyBounded.ofStatic
    {A : ExecAdversary n In Out NetQ NetR AdvQ AdvR} {p : Polynomial ℕ}
    (h : A.PolyBounded p) (C : ℕ → Finset (Fin n)) :
    (AdaptiveAdversary.ofStatic A C :
      AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR).PolyBounded p :=
  fun κ => ⟨(h κ (C κ)).1, fun q s => isQueryBounded_liftStaticNetProgram ((h κ (C κ)).2 q s)⟩

/-- Every external query of `program` of the form `.corrupt i` has `i ∈ C₀`. -/
@[expose] def NoNewCorruptProgram (C₀ : Finset (Fin n)) {α : Type}
    (program : ProbOracleComp
      (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α) : Prop :=
  OracleComp.QueriesSatisfy
    (fun q => match q with
      | .inl _ => True
      | .inr (.corrupt i) => i ∈ C₀
      | .inr _ => True)
    program

/-- An adaptive adversary sends `.corrupt i` only for parties already in `A.initial κ`. -/
@[expose] def AdaptiveAdversary.NoNewCorrupt
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) : Prop :=
  ∀ κ q s, NoNewCorruptProgram (A.initial κ) (((A.machine κ).handle q).run s)

private theorem noNewCorrupt_liftStaticNetProgram (C₀ : Finset (Fin n)) {α : Type}
    (program : ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) α) :
    NoNewCorruptProgram (View := View) C₀ (liftStaticNetProgram program) := by
  induction program using OracleComp.induction with
  | pure a => exact OracleComp.QueriesSatisfy.pure a
  | query_bind q cont ih =>
    rcases q with k | (⟨i, x⟩ | nq)
    · rw [liftStaticNetProgram, OracleComp.interpret_bind]
      exact OracleComp.QueriesSatisfy.bind (OracleComp.QueriesSatisfy.query trivial) ih
    · rw [liftStaticNetProgram, OracleComp.interpret_bind]
      refine OracleComp.QueriesSatisfy.bind ?_ ih
      rw [OracleComp.interpret_query]
      simp only [sumHandler, OracleComp.queriesSatisfy_map_iff]
      exact OracleComp.QueriesSatisfy.query (spec := probOracleSpec _) trivial
    · rw [liftStaticNetProgram, OracleComp.interpret_bind]
      refine OracleComp.QueriesSatisfy.bind ?_ ih
      rw [OracleComp.interpret_query]
      simp only [sumHandler, OracleComp.queriesSatisfy_map_iff]
      exact OracleComp.QueriesSatisfy.query (spec := probOracleSpec _) trivial

/-- A static adversary lifted via `AdaptiveAdversary.ofStatic` never queries `.corrupt`. -/
theorem AdaptiveAdversary.noNewCorrupt_ofStatic
    (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR) (C : ℕ → Finset (Fin n)) :
    (AdaptiveAdversary.ofStatic A C :
      AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR).NoNewCorrupt :=
  fun κ q s => noNewCorrupt_liftStaticNetProgram (C κ) (((A κ (C κ)).handle q).run s)

private theorem liftAdaptiveNet_bind {Q R α β : Type}
    (program : ProbOracleComp (netSpec Q R) α)
    (next : α → ProbOracleComp (netSpec Q R) β) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out) (program >>= next) =
      liftAdaptiveNet program >>= fun a => liftAdaptiveNet (next a) :=
  OracleComp.interpret_bind _ _ _

private theorem liftAdaptiveNet_map {Q R α β : Type} (f : α → β)
    (program : ProbOracleComp (netSpec Q R) α) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out) (f <$> program) =
      f <$> liftAdaptiveNet program :=
  OracleComp.interpret_map _ _ _

private theorem liftAdaptiveNet_query {Q R : Type} (q : Q) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out)
        (OracleComp.query (spec := probOracleSpec (netSpec Q R)) (Sum.inr q)) =
      ProbOracleComp.query (spec := adaptivePartySpec n In Out ⊕ₒ netSpec Q R) (.inr q) :=
  OracleComp.interpret_query _ _

private theorem liftAdaptiveNet_sample {Q R α : Type} (program : ProbComp α) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out)
        (ProbOracleComp.sample (spec := netSpec Q R) program) =
      ProbOracleComp.sample program := by
  simp only [liftAdaptiveNet, ProbOracleComp.interpret_sample]
  rfl

private theorem liftAdaptiveNet_unifFin {Q R : Type} (k : ℕ) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out) (Q := Q) (R := R)
        (OracleComp.query (spec := probOracleSpec (netSpec Q R)) (Sum.inl k)) =
      ProbOracleComp.sample (ProbComp.unifFin k) := by
  simp only [liftAdaptiveNet, ProbOracleComp.sample, ProbComp.unifFin, OracleComp.interpret_query,
    sumHandler]

private theorem runFrom_query_sample {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    (M : Machine I E) (k : ℕ) (s : M.State) :
    M.runFrom (OracleComp.query (spec := probOracleSpec E) (Sum.inl k)) s =
      (fun a => (a, s)) <$> OracleComp.query (spec := probOracleSpec I) (Sum.inl k) := by
  rw [Machine.runFrom_call]
  change (StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k))).run s = _
  rw [StateT.run_lift, bind_pure_comp]
  rfl

private theorem runFrom_adaptiveRouter_bind (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    {α β : Type} (program : ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR View) α)
    (next : α → ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR View) β)
    (rs : AdaptiveRouterState (P.machine κ).State View n) :
    (adaptiveRouter mode P κ C₀).runFrom (program >>= next) rs =
      (adaptiveRouter mode P κ C₀).runFrom program rs >>=
        fun (x : α × AdaptiveRouterState (P.machine κ).State View n) =>
          (adaptiveRouter mode P κ C₀).runFrom (next x.1) x.2 :=
  Machine.runFrom_bind _ _ _ _

private theorem runFrom_adaptiveRouter_map (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    {α β : Type} (f : α → β)
    (program : ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR View) α)
    (rs : AdaptiveRouterState (P.machine κ).State View n) :
    (adaptiveRouter mode P κ C₀).runFrom (f <$> program) rs =
      Prod.map f _root_.id <$> (adaptiveRouter mode P κ C₀).runFrom program rs :=
  Machine.runFrom_map _ _ _ _

private theorem runFrom_adaptiveRouter_query (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (q : AdaptivePartyQ n In ⊕ AdaptiveNetQ n In NetQ)
    (rs : AdaptiveRouterState (P.machine κ).State View n) :
    (adaptiveRouter mode P κ C₀).runFrom (ProbOracleComp.query q) rs =
      ((adaptiveRouter mode P κ C₀).handle q).run rs :=
  Machine.runFrom_query _ _ _

private theorem runFrom_adaptiveRouter_sample (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (k : ℕ) (rs : AdaptiveRouterState (P.machine κ).State View n) :
    (adaptiveRouter mode P κ C₀).runFrom
        (OracleComp.query (spec := probOracleSpec _) (Sum.inl k)) rs =
      (fun a => (a, rs)) <$>
        OracleComp.query (spec := probOracleSpec OracleSpec.empty) (Sum.inl k) :=
  runFrom_query_sample (adaptiveRouter mode P κ C₀) k rs

private theorem runFrom_adaptiveExecMachine_bind (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    {α β : Type} (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (next : α → ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) β)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n) :
    (adaptiveExecMachine mode P A κ).runFrom (program >>= next) (sA, rs) =
      (adaptiveExecMachine mode P A κ).runFrom program (sA, rs) >>=
        fun (x : α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n)) =>
          (adaptiveExecMachine mode P A κ).runFrom (next x.1) x.2 :=
  Machine.runFrom_bind _ _ _ _

private theorem runFrom_adaptiveExecMachine_query (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (q : AdaptivePartyQ n In ⊕ AdvQ)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n) :
    (adaptiveExecMachine mode P A κ).runFrom (ProbOracleComp.query q) (sA, rs) =
      ((adaptiveExecMachine mode P A κ).handle q).run (sA, rs) :=
  Machine.runFrom_query _ _ _

private theorem runFrom_adaptiveExecMachine_sample (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (k : ℕ) (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n) :
    (adaptiveExecMachine mode P A κ).runFrom
        (OracleComp.query (spec := probOracleSpec _) (Sum.inl k)) (sA, rs) =
      (fun a => (a, (sA, rs))) <$>
        OracleComp.query (spec := probOracleSpec OracleSpec.empty) (Sum.inl k) :=
  runFrom_query_sample (adaptiveExecMachine mode P A κ) k (sA, rs)

private theorem adaptiveExecMachine_handle_inl_party (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (i : Fin n) (x : In) (sA : (A.machine κ).State)
    (rs : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveExecMachine mode P A κ).handle (.inl (.party i x))).run (sA, rs) =
      (fun (p : Option Out × AdaptiveRouterState (P.machine κ).State View n) =>
        (p.1, (sA, p.2))) <$>
        ((adaptiveRouter mode P κ (A.initial κ)).handle (.inl (.party i x))).run rs := by
  change Equiv.prodAssoc _ _ _ <$> (adaptiveRouter mode P κ (A.initial κ)).runFrom
      ((fun a => (a, sA)) <$> ProbOracleComp.query (Sum.inl (.party i x))) rs = _
  rw [runFrom_adaptiveRouter_map, runFrom_adaptiveRouter_query]
  simp only [Functor.map_map]
  rfl

private theorem adaptiveExecMachine_handle_inl_status (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveExecMachine mode P A κ).handle (.inl .status)).run (sA, rs) =
      (fun (p : Finset (Fin n) × AdaptiveRouterState (P.machine κ).State View n) =>
        (p.1, (sA, p.2))) <$>
        ((adaptiveRouter mode P κ (A.initial κ)).handle (.inl .status)).run rs := by
  change Equiv.prodAssoc _ _ _ <$> (adaptiveRouter mode P κ (A.initial κ)).runFrom
      ((fun a => (a, sA)) <$> ProbOracleComp.query (Sum.inl .status)) rs = _
  rw [runFrom_adaptiveRouter_map, runFrom_adaptiveRouter_query]
  simp only [Functor.map_map]
  rfl

private theorem adaptiveExecMachine_handle_inr (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (a : AdvQ) (sA : (A.machine κ).State)
    (rs : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveExecMachine mode P A κ).handle (.inr a)).run (sA, rs) =
      (fun (p : (AdvR × (A.machine κ).State) ×
          AdaptiveRouterState (P.machine κ).State View n) =>
        (p.1.1, (p.1.2, p.2))) <$>
        (adaptiveRouter mode P κ (A.initial κ)).runFrom
          (liftAdaptiveNet (((A.machine κ).handle a).run sA)) rs :=
  rfl

private theorem adaptiveRouter_init (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n)) :
    (adaptiveRouter mode P κ C₀).init =
      (P.machine κ).init >>= fun s₀ =>
        let s₁ := P.applyInitialCorruptions κ C₀ s₀
        pure { inner := s₁, corrupted := C₀, trace := fun i => [P.view κ i s₁] } := rfl

private theorem sample_adaptiveRouter_init (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    {ι : Type} {spec : ι → Type} :
    ProbOracleComp.sample (spec := spec) (adaptiveRouter mode P κ C₀).init =
      ProbOracleComp.sample (spec := spec) (P.machine κ).init >>= fun s₀ =>
        let s₁ := P.applyInitialCorruptions κ C₀ s₀
        pure ({ inner := s₁, corrupted := C₀, trace := fun i => [P.view κ i s₁] } :
          AdaptiveRouterState (P.machine κ).State View n) := by
  rw [adaptiveRouter_init, ProbOracleComp.sample_bind]
  exact bind_congr fun _s₀ => ProbOracleComp.sample_pure _

private theorem sample_adaptiveExecMachine_init (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ) {α : Type}
    (f : (A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n →
      ProbOracleComp OracleSpec.empty α) :
    (ProbOracleComp.sample (adaptiveExecMachine mode P A κ).init >>= f) =
      ProbOracleComp.sample (P.machine κ).init >>= fun s₀ =>
        ProbOracleComp.sample (A.machine κ).init >>= fun sA =>
          let s₁ := P.applyInitialCorruptions κ (A.initial κ) s₀
          f (sA, { inner := s₁, corrupted := A.initial κ, trace := fun i => [P.view κ i s₁] }) := by
  erw [Machine.sample_comp_init, sample_adaptiveRouter_init, bind_assoc, bind_assoc]
  refine bind_congr fun s₀ => ?_
  erw [pure_bind, bind_assoc]
  refine bind_congr fun sA => ?_
  exact pure_bind _ _

private theorem sample_execMachine_init (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR) (C : ℕ → Finset (Fin n)) (κ : ℕ)
    {α : Type} (f : (A κ (C κ)).State × (P.machine κ).State → ProbOracleComp OracleSpec.empty α) :
    (ProbOracleComp.sample (execMachine P.toStatic A κ (C κ)).init >>= f) =
      ProbOracleComp.sample (P.machine κ).init >>= fun s₀ =>
        ProbOracleComp.sample (A κ (C κ)).init >>= fun sA =>
          f (sA, P.applyInitialCorruptions κ (C κ) s₀) := by
  erw [Machine.sample_comp_init]
  change (ProbOracleComp.sample (P.applyInitialCorruptions κ (C κ) <$> (P.machine κ).init) >>=
    fun sP => (ProbOracleComp.sample (A κ (C κ)).init >>= fun sA => pure (sA, sP))) >>= f = _
  rw [ProbOracleComp.sample_map, bind_assoc, bind_map_left]
  refine bind_congr fun s₀ => ?_
  erw [bind_assoc]
  refine bind_congr fun sA => ?_
  exact pure_bind _ _

private theorem adaptiveRouter_handle_inl_party (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (i : Fin n) (x : In) (s : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveRouter mode P κ C₀).handle (.inl (.party i x))).run s =
      if i ∈ s.corrupted then pure (none, s)
      else ((P.machine κ).handle (.inl (i, x))).run s.inner >>= fun p =>
        pure (p.1, P.recordSnapshot κ p.2 s.corrupted s.trace) := rfl

private theorem adaptiveRouter_handle_inl_status (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (s : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveRouter mode P κ C₀).handle (.inl .status)).run s = pure (s.corrupted, s) := rfl

private theorem adaptiveRouter_handle_inr_party (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (i : Fin n) (x : In) (s : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveRouter mode P κ C₀).handle (.inr (.party i x))).run s =
      if i ∈ s.corrupted then
        ((P.machine κ).handle (.inl (i, x))).run s.inner >>= fun p =>
          pure (.party p.1, P.recordSnapshot κ p.2 s.corrupted s.trace)
      else pure (.party none, s) := rfl

private theorem adaptiveRouter_handle_inr_corrupt_static
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (i : Fin n) (s : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveRouter .static P κ C₀).handle (.inr (.corrupt i))).run s =
      if i ∈ s.corrupted then pure (.corrupt (some (P.corruptionReport κ i s)), s)
      else pure (.corrupt none, s) := rfl

private theorem adaptiveRouter_handle_inr_corrupt_adaptive
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (i : Fin n) (s : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveRouter .adaptive P κ C₀).handle (.inr (.corrupt i))).run s =
      let s' : AdaptiveRouterState (P.machine κ).State View n :=
        if i ∈ s.corrupted then s
        else
          { inner := P.onCorrupt κ i s.inner
            corrupted := insert i s.corrupted
            trace := s.trace }
      pure (.corrupt (some (P.corruptionReport κ i s')), s') := rfl

private theorem adaptiveRouter_handle_inr_net (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (q : NetQ) (s : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveRouter mode P κ C₀).handle (.inr (.net q))).run s =
      ((P.machine κ).handle (.inr q)).run s.inner >>= fun p =>
        pure (.net p.1, P.recordSnapshot κ p.2 s.corrupted s.trace) := rfl

private theorem runFrom_adaptiveRouter_liftAdaptiveNet_static_eq_adaptive {α β : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (hno : NoNewCorruptProgram C₀ netProg)
    (rs : AdaptiveRouterState (P.machine κ).State View n) (hrs : rs.corrupted = C₀)
    (f g : α × AdaptiveRouterState (P.machine κ).State View n → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a rs', rs'.corrupted = C₀ → f (a, rs') = g (a, rs')) :
    ((adaptiveRouter .static P κ C₀).runFrom (liftAdaptiveNet netProg) rs >>= f) =
      ((adaptiveRouter .adaptive P κ C₀).runFrom (liftAdaptiveNet netProg) rs >>= g) := by
  induction netProg using OracleComp.induction generalizing rs with
  | pure a =>
    exact hfg a rs hrs
  | query_bind q cont ih =>
    rcases q with k | q
    · rw [liftAdaptiveNet_bind, liftAdaptiveNet_unifFin]
      change ((adaptiveRouter .static P κ C₀).runFrom
        (OracleComp.query (spec := probOracleSpec _) (Sum.inl k) >>=
          fun a => liftAdaptiveNet (cont a)) rs >>= f) =
        ((adaptiveRouter .adaptive P κ C₀).runFrom
        (OracleComp.query (spec := probOracleSpec _) (Sum.inl k) >>=
          fun a => liftAdaptiveNet (cont a)) rs >>= g)
      rw [runFrom_adaptiveRouter_bind, runFrom_adaptiveRouter_bind,
        runFrom_adaptiveRouter_sample, runFrom_adaptiveRouter_sample]
      erw [bind_map_left, bind_map_left, bind_assoc, bind_assoc]
      exact bind_congr fun a =>
        ih a ((OracleComp.QueriesSatisfy.liftBind_iff.mp hno).2 a) rs hrs
    · have hno' := OracleComp.QueriesSatisfy.liftBind_iff.mp hno
      have hcont : ∀ a, NoNewCorruptProgram C₀ (cont a) := hno'.2
      rw [liftAdaptiveNet_bind, liftAdaptiveNet_query]
      rw [runFrom_adaptiveRouter_bind, runFrom_adaptiveRouter_bind,
        runFrom_adaptiveRouter_query, runFrom_adaptiveRouter_query]
      erw [bind_assoc, bind_assoc]
      cases q with
      | party i x =>
        rw [adaptiveRouter_handle_inr_party, adaptiveRouter_handle_inr_party]
        by_cases hi : i ∈ C₀
        · have hi' : i ∈ rs.corrupted := hrs ▸ hi
          simp only [hi', ↓reduceIte]
          erw [bind_assoc, bind_assoc]
          refine bind_congr fun ⟨out, s'⟩ => ?_
          erw [pure_bind, pure_bind]
          exact ih (.party out) (hcont (.party out)) (P.recordSnapshot κ s' rs.corrupted rs.trace)
            (by simpa [AdaptiveProtocol.recordSnapshot] using hrs)
        · have hi' : i ∉ rs.corrupted := hrs ▸ hi
          simp only [hi', ↓reduceIte]
          erw [pure_bind, pure_bind]
          exact ih (.party none) (hcont (.party none)) rs hrs
      | corrupt i =>
        have hi : i ∈ C₀ := by simpa only [] using hno'.1
        have hi' : i ∈ rs.corrupted := hrs ▸ hi
        rw [adaptiveRouter_handle_inr_corrupt_static, adaptiveRouter_handle_inr_corrupt_adaptive]
        simp only [hi', ↓reduceIte]
        erw [pure_bind, pure_bind]
        exact ih (.corrupt (some (P.corruptionReport κ i rs))) (hcont _) rs hrs
      | net nq =>
        rw [adaptiveRouter_handle_inr_net, adaptiveRouter_handle_inr_net]
        erw [bind_assoc, bind_assoc]
        refine bind_congr fun ⟨r, s'⟩ => ?_
        erw [pure_bind, pure_bind]
        exact ih (.net r) (hcont (.net r)) (P.recordSnapshot κ s' rs.corrupted rs.trace)
          (by simpa [AdaptiveProtocol.recordSnapshot] using hrs)

private theorem runFrom_adaptiveExecMachine_static_eq_adaptive {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (hno : A.NoNewCorrupt) (κ : ℕ)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n)
    (hrs : rs.corrupted = A.initial κ) :
    (adaptiveExecMachine .static P A κ).runFrom program (sA, rs) =
      (adaptiveExecMachine .adaptive P A κ).runFrom program (sA, rs) := by
  induction program using OracleComp.induction generalizing sA rs with
  | pure a => rfl
  | query_bind q cont ih =>
    rcases q with k | q
    · rw [runFrom_adaptiveExecMachine_bind, runFrom_adaptiveExecMachine_bind,
        runFrom_adaptiveExecMachine_sample, runFrom_adaptiveExecMachine_sample]
      erw [bind_map_left, bind_map_left]
      exact bind_congr fun a => ih a sA rs hrs
    · rw [runFrom_adaptiveExecMachine_bind, runFrom_adaptiveExecMachine_bind]
      change ((adaptiveExecMachine .static P A κ).runFrom (ProbOracleComp.query q) (sA, rs) >>=
        fun x => (adaptiveExecMachine .static P A κ).runFrom (cont x.1) x.2) =
        ((adaptiveExecMachine .adaptive P A κ).runFrom (ProbOracleComp.query q) (sA, rs) >>=
        fun x => (adaptiveExecMachine .adaptive P A κ).runFrom (cont x.1) x.2)
      rw [runFrom_adaptiveExecMachine_query, runFrom_adaptiveExecMachine_query]
      rcases q with (⟨i, x⟩ | _) | a
      · rw [adaptiveExecMachine_handle_inl_party, adaptiveExecMachine_handle_inl_party]
        rw [adaptiveRouter_handle_inl_party, adaptiveRouter_handle_inl_party]
        by_cases hi : i ∈ A.initial κ
        · have hi' : i ∈ rs.corrupted := hrs ▸ hi
          simp only [hi', ↓reduceIte, map_pure]
          erw [pure_bind, pure_bind]
          exact ih none sA rs hrs
        · have hi' : i ∉ rs.corrupted := hrs ▸ hi
          simp only [hi', ↓reduceIte]
          erw [bind_map_left, bind_map_left, bind_assoc, bind_assoc]
          refine bind_congr fun ⟨out, s'⟩ => ?_
          erw [pure_bind, pure_bind]
          exact ih out sA (P.recordSnapshot κ s' rs.corrupted rs.trace)
            (by simpa [AdaptiveProtocol.recordSnapshot] using hrs)
      · rw [adaptiveExecMachine_handle_inl_status, adaptiveExecMachine_handle_inl_status]
        rw [adaptiveRouter_handle_inl_status, adaptiveRouter_handle_inl_status]
        simp only [map_pure]
        erw [pure_bind, pure_bind]
        exact ih rs.corrupted sA rs hrs
      · rw [adaptiveExecMachine_handle_inr, adaptiveExecMachine_handle_inr]
        erw [bind_map_left, bind_map_left]
        exact runFrom_adaptiveRouter_liftAdaptiveNet_static_eq_adaptive P κ (A.initial κ)
          (((A.machine κ).handle a).run sA) (hno κ a sA) rs hrs _ _ fun res rs' hrs' =>
          ih res.1 res.2 rs' hrs'

/-- If `A` satisfies `NoNewCorrupt` (it sends `.corrupt i` only for parties already in
`A.initial κ`), then `.static` and `.adaptive` modes produce the exact same execution. -/
theorem adaptiveExec_static_eq_adaptive_of_noCorrupt
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (hno : A.NoNewCorrupt) (Z : AdaptiveEnvironment n In Out AdvQ AdvR)
    (κ : ℕ) (z : List Bool) :
    adaptiveExec .static P A Z κ z = adaptiveExec .adaptive P A Z κ z := by
  simp only [adaptiveExec, Machine.run, Machine.link]
  refine congrArg Machine.closeProgram ?_
  erw [sample_adaptiveExecMachine_init, sample_adaptiveExecMachine_init]
  refine bind_congr fun s₀ => bind_congr fun sA => ?_
  exact congrArg (Prod.fst <$> ·)
    (runFrom_adaptiveExecMachine_static_eq_adaptive P A hno κ (Z κ z) sA _ rfl)

private theorem liftStaticNetProgram_bind {α β : Type}
    (p : ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) α)
    (next : α → ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) β) :
    liftStaticNetProgram (n := n) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
        (View := View) (p >>= next) =
      liftStaticNetProgram p >>= fun a => liftStaticNetProgram (next a) :=
  OracleComp.interpret_bind _ _ _

private theorem liftStaticNetProgram_unifFin (k : ℕ) :
    liftStaticNetProgram (n := n) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
        (View := View)
        (OracleComp.query (spec := probOracleSpec
          (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))) (Sum.inl k)) =
      OracleComp.query (spec := probOracleSpec
        (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))) (Sum.inl k) := by
  rw [liftStaticNetProgram, OracleComp.interpret_query]

private theorem liftStaticNetProgram_party (i : Fin n) (x : In) :
    liftStaticNetProgram (n := n) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
        (View := View)
        (OracleComp.query (spec := probOracleSpec
          (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))) (Sum.inr (.inl (i, x)))) =
      AdaptiveNetR.toRoutedNetR <$>
        ProbOracleComp.query (spec := netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))
          (.party i x) := by
  rw [liftStaticNetProgram, OracleComp.interpret_query]

private theorem liftStaticNetProgram_net (nq : NetQ) :
    liftStaticNetProgram (n := n) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
        (View := View)
        (OracleComp.query (spec := probOracleSpec
          (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))) (Sum.inr (.inr nq))) =
      AdaptiveNetR.toRoutedNetR <$>
        ProbOracleComp.query (spec := netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))
          (.net nq) := by
  rw [liftStaticNetProgram, OracleComp.interpret_query]

private theorem liftNet_bind' {NetQ NetR α β : Type} (p : ProbOracleComp (netSpec NetQ NetR) α)
    (next : α → ProbOracleComp (netSpec NetQ NetR) β) :
    liftNet (n := n) (In := In) (Out := Out) (p >>= next) =
      liftNet p >>= fun a => liftNet (next a) :=
  OracleComp.interpret_bind _ _ _

private theorem liftNet_unifFin' {NetQ NetR : Type} (k : ℕ) :
    liftNet (n := n) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
        (OracleComp.query (spec := probOracleSpec (netSpec NetQ NetR)) (Sum.inl k)) =
      OracleComp.query (spec := probOracleSpec (protocolSpec n In Out NetQ NetR)) (Sum.inl k) := by
  rw [liftNet, OracleComp.interpret_query]

private theorem liftNet_query' {NetQ NetR : Type} (q : NetQ) :
    liftNet (n := n) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
        (OracleComp.query (spec := probOracleSpec (netSpec NetQ NetR)) (Sum.inr q)) =
      ProbOracleComp.query (spec := protocolSpec n In Out NetQ NetR) (.inr q) := by
  rw [liftNet, OracleComp.interpret_query]

private theorem runFrom_adaptiveRouter_liftStaticNetProgram {α β : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) α)
    (rs : AdaptiveRouterState (P.machine κ).State View n) (hrs : rs.corrupted = C₀)
    (f : α × AdaptiveRouterState (P.machine κ).State View n → ProbOracleComp OracleSpec.empty β)
    (g : α × (P.machine κ).State → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a rs', rs'.corrupted = C₀ → f (a, rs') = g (a, rs'.inner)) :
    ((adaptiveRouter .static P κ C₀).runFrom
        (liftAdaptiveNet (liftStaticNetProgram (View := View) netProg)) rs >>= f) =
      ((corruptRouter C₀ (P.toStatic κ C₀)).runFrom (liftNet netProg) rs.inner >>= g) := by
  induction netProg using OracleComp.induction generalizing rs with
  | pure a =>
    exact hfg a rs hrs
  | query_bind q cont ih =>
    rcases q with k | (⟨i, x⟩ | nq)
    · rw [liftStaticNetProgram_bind, liftStaticNetProgram_unifFin, liftAdaptiveNet_bind,
        liftAdaptiveNet_unifFin, liftNet_bind', liftNet_unifFin']
      change ((adaptiveRouter .static P κ C₀).runFrom
        (OracleComp.query (spec := probOracleSpec _) (Sum.inl k) >>=
          fun a => liftAdaptiveNet (liftStaticNetProgram (cont a))) rs >>= f) =
        ((corruptRouter C₀ (P.toStatic κ C₀)).runFrom
        (OracleComp.query (spec := probOracleSpec _) (Sum.inl k) >>=
          fun a => liftNet (cont a)) rs.inner >>= g)
      rw [runFrom_adaptiveRouter_bind, runFrom_adaptiveRouter_sample]
      erw [Machine.runFrom_bind, runFrom_query_sample, bind_map_left, bind_map_left,
        bind_assoc, bind_assoc]
      exact bind_congr fun a => ih a rs hrs
    · rw [liftStaticNetProgram_bind, liftStaticNetProgram_party, liftAdaptiveNet_bind,
        liftAdaptiveNet_map]
      erw [liftAdaptiveNet_query]
      rw [liftNet_bind', liftNet_query']
      rw [runFrom_adaptiveRouter_bind, runFrom_adaptiveRouter_map, runFrom_adaptiveRouter_query]
      erw [Machine.runFrom_bind, Machine.runFrom_query, bind_map_left]
      rw [adaptiveRouter_handle_inr_party]
      erw [bind_assoc, bind_assoc]
      change (if i ∈ rs.corrupted then _ else _) >>= _ =
        ((corruptRouter C₀ (P.toStatic κ C₀)).handle (.inr (.inl (i, x)))).run rs.inner >>= _
      simp only [corruptRouter, AdaptiveProtocol.toStatic]
      by_cases hi : i ∈ C₀
      · have hi' : i ∈ rs.corrupted := hrs ▸ hi
        simp only [hi, hi', ↓reduceIte, StateT.run_map, bind_map_left]
        erw [bind_assoc]
        refine bind_congr fun ⟨out, s'⟩ => ?_
        erw [pure_bind]
        exact ih (.inl out) (P.recordSnapshot κ s' rs.corrupted rs.trace)
          (by simpa [AdaptiveProtocol.recordSnapshot] using hrs)
      · have hi' : i ∉ rs.corrupted := hrs ▸ hi
        simp only [hi, hi', ↓reduceIte, StateT.run_pure, pure_bind]
        exact ih (.inl none) rs hrs
    · rw [liftStaticNetProgram_bind, liftStaticNetProgram_net, liftAdaptiveNet_bind,
        liftAdaptiveNet_map]
      erw [liftAdaptiveNet_query]
      rw [liftNet_bind', liftNet_query']
      rw [runFrom_adaptiveRouter_bind, runFrom_adaptiveRouter_map, runFrom_adaptiveRouter_query]
      erw [Machine.runFrom_bind, Machine.runFrom_query, bind_map_left]
      rw [adaptiveRouter_handle_inr_net]
      erw [bind_assoc]
      simp only [corruptRouter, AdaptiveProtocol.toStatic, StateT.run_map, bind_map_left]
      erw [bind_assoc, bind_assoc]
      apply bind_congr
      rintro ⟨r, s'⟩
      erw [pure_bind]
      exact ih (.inr r) (P.recordSnapshot κ s' rs.corrupted rs.trace)
        (by simpa [AdaptiveProtocol.recordSnapshot] using hrs)

private theorem runFrom_adaptiveExecMachine_ofStatic {α β : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR)
    (C : ℕ → Finset (Fin n)) (κ : ℕ)
    (program : ProbOracleComp (execSpec n In Out AdvQ AdvR) α)
    (sA : (A κ (C κ)).State) (rs : AdaptiveRouterState (P.machine κ).State View n)
    (hrs : rs.corrupted = C κ)
    (f : α × ((A κ (C κ)).State × AdaptiveRouterState (P.machine κ).State View n) →
      ProbOracleComp OracleSpec.empty β)
    (g : α × ((A κ (C κ)).State × (P.machine κ).State) → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a sA' rs', rs'.corrupted = C κ → f (a, sA', rs') = g (a, sA', rs'.inner)) :
    ((adaptiveExecMachine .static P (AdaptiveAdversary.ofStatic A C) κ).runFrom
        (liftPartyQuery program) (sA, rs) >>= f) =
      ((execMachine P.toStatic A κ (C κ)).runFrom program (sA, rs.inner) >>= g) := by
  induction program using OracleComp.induction generalizing sA rs with
  | pure a => exact hfg a sA rs hrs
  | query_bind q cont ih =>
    rcases q with k | (⟨i, x⟩ | a)
    · rw [liftPartyQuery, OracleComp.interpret_bind]
      have hsamp : OracleComp.interpret
          (sumHandler
            (fun k => OracleComp.query
              (spec := probOracleSpec (adaptiveExecSpec n In Out AdvQ AdvR)) (Sum.inl k))
            (fun q => match q with
              | .inl (i, x) => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR)
                  (.inl (.party i x))
              | .inr a => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR)
                  (.inr a)))
          (OracleComp.query (spec := probOracleSpec (execSpec n In Out AdvQ AdvR)) (Sum.inl k)) =
          OracleComp.query (spec := probOracleSpec (adaptiveExecSpec n In Out AdvQ AdvR))
            (Sum.inl k) := by
        rw [OracleComp.interpret_query]
      erw [runFrom_adaptiveExecMachine_bind, hsamp, runFrom_adaptiveExecMachine_sample]
      erw [Machine.runFrom_bind, runFrom_query_sample, bind_assoc, bind_assoc,
        bind_map_left, bind_map_left]
      exact bind_congr fun a => ih a sA rs hrs
    · rw [liftPartyQuery, OracleComp.interpret_bind]
      have hq : OracleComp.interpret
          (sumHandler
            (fun k => OracleComp.query
              (spec := probOracleSpec (adaptiveExecSpec n In Out AdvQ AdvR)) (Sum.inl k))
            (fun q => match q with
              | .inl (i, x) => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR)
                  (.inl (.party i x))
              | .inr a => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR)
                  (.inr a)))
          (OracleComp.query (spec := probOracleSpec (execSpec n In Out AdvQ AdvR))
            (Sum.inr (.inl (i, x)))) =
          ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR)
            (.inl (.party i x)) := by
        rw [OracleComp.interpret_query]
      erw [runFrom_adaptiveExecMachine_bind, hq, runFrom_adaptiveExecMachine_query]
      erw [adaptiveExecMachine_handle_inl_party, adaptiveRouter_handle_inl_party]
      erw [bind_assoc, bind_map_left, Machine.runFrom_bind,
        show OracleComp.query (spec := probOracleSpec (execSpec n In Out AdvQ AdvR))
            (Sum.inr (.inl (i, x))) =
          ProbOracleComp.query (spec := execSpec n In Out AdvQ AdvR) (.inl (i, x)) from rfl,
        Machine.runFrom_query, bind_assoc]
      change (if i ∈ rs.corrupted then _ else _) >>= _ =
        ((execMachine P.toStatic A κ (C κ)).handle (.inl (i, x))).run (sA, rs.inner) >>= _
      simp only [execMachine, Machine.comp, liftAdversary, corruptRouter, AdaptiveProtocol.toStatic,
        StateT.lift, StateT.run, bind_pure_comp, Machine.runFrom_map, Machine.runFrom_query,
        Functor.map_map, bind_map_left]
      by_cases hi : i ∈ C κ
      · have hi' : i ∈ rs.corrupted := hrs ▸ hi
        simp only [hi, hi', ↓reduceIte, pure_bind]
        exact ih none sA rs hrs
      · have hi' : i ∉ rs.corrupted := hrs ▸ hi
        simp only [hi, hi', ↓reduceIte]
        erw [bind_map_left]
        exact bind_congr fun ⟨out, s'⟩ =>
          ih out sA (P.recordSnapshot κ s' rs.corrupted rs.trace)
            (by simpa [AdaptiveProtocol.recordSnapshot] using hrs)
    · rw [liftPartyQuery, OracleComp.interpret_bind]
      have hq : OracleComp.interpret
          (sumHandler
            (fun k => OracleComp.query
              (spec := probOracleSpec (adaptiveExecSpec n In Out AdvQ AdvR)) (Sum.inl k))
            (fun q => match q with
              | .inl (i, x) => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR)
                  (.inl (.party i x))
              | .inr a => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR)
                  (.inr a)))
          (OracleComp.query (spec := probOracleSpec (execSpec n In Out AdvQ AdvR))
            (Sum.inr (.inr a))) =
          ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR) (.inr a) := by
        rw [OracleComp.interpret_query]
      erw [runFrom_adaptiveExecMachine_bind, hq, runFrom_adaptiveExecMachine_query]
      erw [adaptiveExecMachine_handle_inr]
      erw [bind_assoc, bind_map_left, Machine.runFrom_bind,
        show OracleComp.query (spec := probOracleSpec (execSpec n In Out AdvQ AdvR))
            (Sum.inr (.inr a)) =
          ProbOracleComp.query (spec := execSpec n In Out AdvQ AdvR) (.inr a) from rfl,
        Machine.runFrom_query, bind_assoc]
      change (adaptiveRouter .static P κ (C κ)).runFrom
          (liftAdaptiveNet (((AdaptiveAdversary.ofStatic A C).machine κ).handle a |>.run sA)) rs >>=
            _ =
        ((execMachine P.toStatic A κ (C κ)).handle (.inr a)).run (sA, rs.inner) >>= _
      simp only [AdaptiveAdversary.ofStatic, execMachine, Machine.comp, liftAdversary,
        StateT.run, Equiv.prodAssoc, bind_map_left]
      exact runFrom_adaptiveRouter_liftStaticNetProgram P κ (C κ)
        (((A κ (C κ)).handle a).run sA) rs hrs _ _ fun res rs' hrs' =>
        ih res.1 res.2 rs' hrs'

/-- Running a static adversary lifted via `AdaptiveAdversary.ofStatic` against `P` in `.static`
mode with embedded environment `Z.toAdaptive` equals the static UC execution `exec P.toStatic`. -/
theorem adaptiveExec_static_ofStatic (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR) (C : ℕ → Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec .static P (AdaptiveAdversary.ofStatic A C) Z.toAdaptive κ z =
      exec P.toStatic A (C κ) Z κ z := by
  simp only [adaptiveExec, exec, Machine.run, Machine.link, Environment.toAdaptive]
  refine congrArg Machine.closeProgram ?_
  erw [sample_adaptiveExecMachine_init, sample_execMachine_init]
  refine bind_congr fun s₀ => bind_congr fun sA => ?_
  erw [← bind_pure_comp, ← bind_pure_comp]
  exact runFrom_adaptiveExecMachine_ofStatic P A C κ (Z κ z) sA _ rfl
    (fun x => pure x.1) (fun x => pure x.1) fun a _ _ _ => rfl

/-- Running a static adversary lifted via `AdaptiveAdversary.ofStatic` against `P` in `.adaptive`
mode with embedded environment `Z.toAdaptive` also equals the static UC execution
`exec P.toStatic`, because `ofStatic` never sends `.corrupt`. -/
theorem adaptiveExec_adaptive_ofStatic (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR) (C : ℕ → Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec .adaptive P (AdaptiveAdversary.ofStatic A C) Z.toAdaptive κ z =
      exec P.toStatic A (C κ) Z κ z :=
  (adaptiveExec_static_eq_adaptive_of_noCorrupt P (AdaptiveAdversary.ofStatic A C)
    (AdaptiveAdversary.noNewCorrupt_ofStatic A C) Z.toAdaptive κ z).symm.trans
    (adaptiveExec_static_ofStatic P A C Z κ z)

end StaticSpecialCase

end Cslib.Crypto.Protocols.UC
