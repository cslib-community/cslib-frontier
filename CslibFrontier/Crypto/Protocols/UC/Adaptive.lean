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

end Execution

/-! ### Budgets and adaptive emulation -/

section Budgets

variable {n : ℕ} {In Out NetQ NetR View AdvQ AdvR : Type}
  {NetQ₁ NetR₁ View₁ NetQ₂ NetR₂ View₂ : Type}

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

end Budgets

end Cslib.Crypto.Protocols.UC
