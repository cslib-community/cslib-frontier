/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.DummyAdversary
public import CslibFrontier.Crypto.Protocols.UC.Emulation
public import CslibFrontier.Crypto.Protocols.UC.Linking

/-!
# Adaptive corruptions in the UC execution

This module extends the UC execution of `CslibFrontier.Crypto.Protocols.UC.Execution` with
`CorruptionMode` (`.static` vs `.adaptive`) and protocol memory exposure (`PartyMemory`:
`.erasing` vs `.nonErasing`), adapting Section 7.1 (pp. 28:69–70) and Section 7.1.1 (p. 28:71)
of [Canetti2020] (J. ACM pagination; ePrint p. 74).

* **Erasure and snapshot granularity:** Erasure is modeled by state exposure on corruption via
  per-activation view snapshots (`AdaptiveProtocol.recordSnapshot`), not write-once cells; coins
  sampled and discarded within a single activation are never exposed.
* **Status query and adversary class:** `AdaptivePartyQ.status` models the corruption aggregation
  ITI's identity-revealing (`f = id`) "Report corruption status" query ([Canetti2020], p. 28:70).
  `AdaptiveEmulatesWithin` and `AdaptiveEmulates` are statistical call-bounded adaptations
  (`Machine.IsBounded`), not PPT notions or theorems stated in Section 7.1.1.

## Scope

Universal composition under adaptive corruption (the adaptive analogue of `UC.Emulates.compose`),
multiple sessions, mobile/proactive corruption, passive corruption as a separate mode, subroutine
corruption paths, PPT adversaries, and computational commitments ([CanettiFischlin2001],
Theorems 8 and 11) are out of scope. Existing static definitions in `Execution`, `Emulation`,
`DummyAdversary`, and `Composition` are unchanged.

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
  `Cslib.Crypto.Protocols.UC.AdaptiveAdversary.ofStatic`,
  `Cslib.Crypto.Protocols.UC.AdaptiveAdversary.clampStatic`: embedding and clamping
  static/adaptive interfaces.

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
* `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesWithin.static_of_adaptive`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulates.static_of_adaptive`: adaptive emulation implies
  static emulation (with a `+ 1` environment call-budget shift for checking corruption status).

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

@[simp] theorem liftAdaptiveNet_pure {α : Type} (a : α) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out)
        (pure a : ProbOracleComp (netSpec Q R) α) = pure a := rfl

@[simp] theorem liftAdaptiveNet_bind {α β : Type} (program : ProbOracleComp (netSpec Q R) α)
    (next : α → ProbOracleComp (netSpec Q R) β) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out) (program >>= next) =
      liftAdaptiveNet program >>= fun a => liftAdaptiveNet (next a) :=
  OracleComp.interpret_bind _ _ _

@[simp] theorem liftAdaptiveNet_map {α β : Type} (f : α → β)
    (program : ProbOracleComp (netSpec Q R) α) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out) (f <$> program) =
      f <$> liftAdaptiveNet program :=
  OracleComp.interpret_map _ _ _

/-- A network query becomes a query on the protocol's adaptive network port. -/
@[simp] theorem liftAdaptiveNet_query (q : Q) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out)
        (ProbOracleComp.query (spec := netSpec Q R) q) =
      ProbOracleComp.query (spec := adaptivePartySpec n In Out ⊕ₒ netSpec Q R) (.inr q) :=
  OracleComp.interpret_query _ _

/-- Private samples are unchanged. -/
@[simp] theorem liftAdaptiveNet_sample {α : Type} (program : ProbComp α) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out)
        (ProbOracleComp.sample (spec := netSpec Q R) program) =
      ProbOracleComp.sample program := by
  simp only [liftAdaptiveNet, ProbOracleComp.interpret_sample]
  rfl

/-- Private uniform index queries are unchanged. -/
@[simp] theorem liftAdaptiveNet_unifFin (k : ℕ) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out) (Q := Q) (R := R)
        (OracleComp.query (spec := probOracleSpec (netSpec Q R)) (Sum.inl k)) =
      ProbOracleComp.sample (ProbComp.unifFin k) := by
  simp only [liftAdaptiveNet, ProbOracleComp.sample, ProbComp.unifFin, OracleComp.interpret_query,
    sumHandler]

/-- Lifting to the adaptive network port preserves call count. -/
theorem isQueryBounded_liftAdaptiveNet {α : Type}
    {program : ProbOracleComp (netSpec Q R) α} {m : ℕ} (h : program.IsQueryBounded m) :
    (liftAdaptiveNet (n := n) (In := In) (Out := Out) program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl _ => exact OracleComp.IsCostBounded.query _
  | inr _ => exact OracleComp.IsCostBounded.query _

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
  erw [Machine.sample_comp_init]
  change (ProbOracleComp.sample ((P.machine κ).init >>= fun s₀ =>
      let s₁ := P.applyInitialCorruptions κ (A.initial κ) s₀
      pure ({ inner := s₁, corrupted := A.initial κ, trace := fun i => [P.view κ i s₁] } :
        AdaptiveRouterState (P.machine κ).State View n)) >>= fun sP =>
    ProbOracleComp.sample (A.machine κ).init >>= fun sA => pure (sA, sP)) >>= f = _
  rw [ProbOracleComp.sample_bind, bind_assoc, bind_assoc]
  refine bind_congr fun s₀ => ?_
  erw [ProbOracleComp.sample_pure, pure_bind, bind_assoc]
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

private theorem adaptiveExecMachine_handle_inl_party (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (i : Fin n) (x : In)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveExecMachine mode P A κ).handle (.inl (.party i x))).run (sA, rs) =
      if i ∈ rs.corrupted then pure (none, (sA, rs))
      else ((P.machine κ).handle (.inl (i, x))).run rs.inner >>= fun p =>
        pure (p.1, (sA, P.recordSnapshot κ p.2 rs.corrupted rs.trace)) := by
  change Equiv.prodAssoc _ _ _ <$> (adaptiveRouter mode P κ (A.initial κ)).runFrom
      ((fun v => (v, sA)) <$> ProbOracleComp.query (Sum.inl (.party i x))) rs = _
  erw [Machine.runFrom_map, Machine.runFrom_query, adaptiveRouter_handle_inl_party]
  by_cases hi : i ∈ rs.corrupted
  · simp [hi]; rfl
  · simp only [hi, ↓reduceIte]
    erw [Functor.map_map, map_bind]
    exact bind_congr fun _ => rfl

private theorem adaptiveExecMachine_handle_inl_status (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveExecMachine mode P A κ).handle (.inl .status)).run (sA, rs) =
      pure (rs.corrupted, (sA, rs)) := by
  change Equiv.prodAssoc _ _ _ <$> (adaptiveRouter mode P κ (A.initial κ)).runFrom
      ((fun v => (v, sA)) <$> ProbOracleComp.query (Sum.inl .status)) rs = _
  erw [Machine.runFrom_map, Machine.runFrom_query, adaptiveRouter_handle_inl_status]
  rfl

private theorem interpret_sumHandler_id {ι α : Type} {E : ι → Type} (p : ProbOracleComp E α) :
    OracleComp.interpret (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E) (.inl k))
        (fun q => ProbOracleComp.query (spec := E) q)) p = p := by
  induction p using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    rcases q with k | q <;>
      simp only [OracleComp.interpret_bind, OracleComp.interpret_query, sumHandler] <;>
      exact congrArg (_ >>= ·) (funext ih)

private theorem interpret_sumHandler_comp {ι₀ ι₁ ι₂ α : Type}
    {E₀ : ι₀ → Type} {E₁ : ι₁ → Type} {E₂ : ι₂ → Type}
    (h₀ : (q : ι₀) → ProbOracleComp E₁ (E₀ q))
    (h₁ : (q : ι₁) → ProbOracleComp E₂ (E₁ q))
    (p : ProbOracleComp E₀ α) :
    OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₂) (.inl k)) h₁)
        (OracleComp.interpret
          (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₁) (.inl k)) h₀) p) =
      OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₂) (.inl k))
          fun q => OracleComp.interpret
            (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₂) (.inl k)) h₁)
            (h₀ q)) p := by
  induction p using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    rcases q with k | q <;>
      simp only [OracleComp.interpret_bind, OracleComp.interpret_query, sumHandler] <;>
      exact congrArg (_ >>= ·) (funext ih)

/-- Generic state-intertwining lemma for `Machine.runFrom` over two interpreted programs sharing
an invariant `R` between machine states and `Inv` on allowed queries. -/
private theorem queriesSatisfy_sumTrue {ι : Type} {E : ι → Type} {α : Type}
    (p : ProbOracleComp E α) :
    OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) (fun _ => True)) p := by
  induction p using OracleComp.induction with
  | pure _ => exact .pure _
  | query_bind q _ ih => rcases q with k | q <;> exact .bind (.query trivial) ih

private theorem runFrom_interpret_intertwine {ι₁ ι₂ ι α β : Type}
    {E₁ : ι₁ → Type} {E₂ : ι₂ → Type} {O : ι → Type}
    (M₁ : Machine OracleSpec.empty E₁) (M₂ : Machine OracleSpec.empty E₂)
    (h₁ : (q : ι) → ProbOracleComp E₁ (O q))
    (h₂ : (q : ι) → ProbOracleComp E₂ (O q))
    (Inv : ι → Prop) (R : M₁.State → M₂.State → Prop)
    (prog : ProbOracleComp O α)
    (hinv : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) prog)
    (s₁ : M₁.State) (s₂ : M₂.State) (hR : R s₁ s₂)
    (f : α × M₁.State → ProbOracleComp OracleSpec.empty β)
    (g : α × M₂.State → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a s₁' s₂', R s₁' s₂' → f (a, s₁') = g (a, s₂'))
    (hstep : ∀ (q : ι) (s₁' : M₁.State) (s₂' : M₂.State)
      (k₁ : O q × M₁.State → ProbOracleComp OracleSpec.empty β)
      (k₂ : O q × M₂.State → ProbOracleComp OracleSpec.empty β),
      Inv q → R s₁' s₂' →
      (∀ r s₁'' s₂'', R s₁'' s₂'' → k₁ (r, s₁'') = k₂ (r, s₂'')) →
      (M₁.runFrom (h₁ q) s₁' >>= k₁) = (M₂.runFrom (h₂ q) s₂' >>= k₂)) :
    (M₁.runFrom (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₁) (.inl k)) h₁) prog)
        s₁ >>= f) =
      (M₂.runFrom (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₂) (.inl k)) h₂) prog)
        s₂ >>= g) := by
  induction prog using OracleComp.induction generalizing s₁ s₂ with
  | pure a => exact hfg a s₁ s₂ hR
  | query_bind q cont ih =>
    rcases q with k | q
    · rw [OracleComp.interpret_bind, OracleComp.interpret_bind,
        OracleComp.interpret_query, OracleComp.interpret_query]
      dsimp only [sumHandler]
      erw [Machine.runFrom_bind, Machine.runFrom_bind,
        Machine.runFrom_call, Machine.runFrom_call,
        StateT.run_lift, StateT.run_lift, bind_pure_comp, bind_pure_comp,
        bind_map_left, bind_map_left, bind_assoc, bind_assoc]
      exact bind_congr fun a =>
        ih a ((OracleComp.QueriesSatisfy.liftBind_iff.mp hinv).2 a) s₁ s₂ hR
    · have hq := OracleComp.QueriesSatisfy.liftBind_iff.mp hinv
      rw [OracleComp.interpret_bind, OracleComp.interpret_bind,
        OracleComp.interpret_query, OracleComp.interpret_query]
      dsimp only [sumHandler]
      erw [Machine.runFrom_bind, Machine.runFrom_bind, bind_assoc, bind_assoc]
      exact hstep q s₁ s₂ _ _ hq.1 hR fun r s₁'' s₂'' hR' =>
        ih r (hq.2 r) s₁'' s₂'' hR'

private theorem runFrom_intertwine {ιE α β : Type} {E : ιE → Type}
    (M₁ M₂ : Machine OracleSpec.empty E) (Inv : ιE → Prop) (R : M₁.State → M₂.State → Prop)
    (prog : ProbOracleComp E α)
    (hinv : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) prog)
    (s₁ : M₁.State) (s₂ : M₂.State) (hR : R s₁ s₂)
    (f : α × M₁.State → ProbOracleComp OracleSpec.empty β)
    (g : α × M₂.State → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a s₁' s₂', R s₁' s₂' → f (a, s₁') = g (a, s₂'))
    (hstep : ∀ (q : ιE) (s₁' : M₁.State) (s₂' : M₂.State)
      (k₁ : E q × M₁.State → ProbOracleComp OracleSpec.empty β)
      (k₂ : E q × M₂.State → ProbOracleComp OracleSpec.empty β),
      Inv q → R s₁' s₂' →
      (∀ r s₁'' s₂'', R s₁'' s₂'' → k₁ (r, s₁'') = k₂ (r, s₂'')) →
      ((M₁.handle q).run s₁' >>= k₁) = ((M₂.handle q).run s₂' >>= k₂)) :
    (M₁.runFrom prog s₁ >>= f) = (M₂.runFrom prog s₂ >>= g) := by
  have h := runFrom_interpret_intertwine M₁ M₂
    (fun q => ProbOracleComp.query (spec := E) q) (fun q => ProbOracleComp.query (spec := E) q)
    Inv R prog hinv s₁ s₂ hR f g hfg fun q s₁' s₂' k₁ k₂ hq hR' hcont => by
      erw [Machine.runFrom_query, Machine.runFrom_query]
      exact hstep q s₁' s₂' k₁ k₂ hq hR' hcont
  simpa only [interpret_sumHandler_id] using h

private theorem runFrom_adaptiveRouter_liftAdaptiveNet_static_eq_adaptive {α β : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (hno : NoNewCorruptProgram C₀ netProg)
    (rs : AdaptiveRouterState (P.machine κ).State View n) (hrs : rs.corrupted = C₀)
    (f g : α × AdaptiveRouterState (P.machine κ).State View n → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a rs', rs'.corrupted = C₀ → f (a, rs') = g (a, rs')) :
    ((adaptiveRouter .static P κ C₀).runFrom (liftAdaptiveNet netProg) rs >>= f) =
      ((adaptiveRouter .adaptive P κ C₀).runFrom (liftAdaptiveNet netProg) rs >>= g) := by
  let Inv : AdaptiveNetQ n In NetQ → Prop := fun q => match q with
    | .corrupt i => i ∈ C₀
    | _ => True
  have hno' : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) netProg := by
    induction netProg using OracleComp.induction with
    | pure _ => exact .pure _
    | query_bind q _ ih =>
      have hq := OracleComp.QueriesSatisfy.liftBind_iff.mp hno
      rcases q with k | (⟨i, x⟩ | i | nq)
      · exact .bind (.query trivial) fun a => ih a (hq.2 a)
      · exact .bind (.query trivial) fun a => ih a (hq.2 a)
      · exact .bind (.query hq.1) fun a => ih a (hq.2 a)
      · exact .bind (.query trivial) fun a => ih a (hq.2 a)
  refine runFrom_interpret_intertwine
    (adaptiveRouter .static P κ C₀) (adaptiveRouter .adaptive P κ C₀)
    (fun q => ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View) (.inr q))
    (fun q => ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View) (.inr q))
    Inv
    (fun rs₁ rs₂ => rs₁ = rs₂ ∧ rs₁.corrupted = C₀)
    netProg hno' rs rs ⟨rfl, hrs⟩ f g
    (fun a rs₁ rs₂ hR => hR.1 ▸ hfg a rs₁ hR.2)
    fun q rs₁ rs₂ k₁ k₂ hq hR hcont => ?_
  rcases hR with ⟨hEq, hrs₁⟩
  cases hEq
  erw [Machine.runFrom_query, Machine.runFrom_query]
  cases q with
  | party i x =>
    erw [adaptiveRouter_handle_inr_party]
    by_cases hi : i ∈ rs₁.corrupted
    · simp only [hi, ↓reduceIte]
      erw [bind_assoc, bind_assoc]
      refine bind_congr fun ⟨out, s'⟩ => ?_
      erw [pure_bind]
      exact hcont (.party out) _ _ ⟨rfl, hrs₁⟩
    · simp only [hi, ↓reduceIte]
      erw [pure_bind]
      exact hcont (.party none) _ _ ⟨rfl, hrs₁⟩
  | corrupt i =>
    have hi : i ∈ rs₁.corrupted := hrs₁ ▸ hq
    erw [adaptiveRouter_handle_inr_corrupt_static, adaptiveRouter_handle_inr_corrupt_adaptive]
    simp only [hi, ↓reduceIte]
    exact hcont (.corrupt (some (P.corruptionReport κ i rs₁))) _ _ ⟨rfl, hrs₁⟩
  | net nq =>
    erw [adaptiveRouter_handle_inr_net]
    erw [bind_assoc, bind_assoc]
    refine bind_congr fun ⟨r, s'⟩ => ?_
    erw [pure_bind]
    exact hcont (.net r) _ _ ⟨rfl, hrs₁⟩

private theorem runFrom_adaptiveExecMachine_static_eq_adaptive {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (hno : A.NoNewCorrupt) (κ : ℕ)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n)
    (hrs : rs.corrupted = A.initial κ) :
    (adaptiveExecMachine .static P A κ).runFrom program (sA, rs) =
      (adaptiveExecMachine .adaptive P A κ).runFrom program (sA, rs) := by
  suffices h :
      ((adaptiveExecMachine .static P A κ).runFrom program (sA, rs) >>= pure) =
        ((adaptiveExecMachine .adaptive P A κ).runFrom program (sA, rs) >>= pure) by
    simpa only [bind_pure] using h
  refine runFrom_intertwine
    (adaptiveExecMachine .static P A κ) (adaptiveExecMachine .adaptive P A κ)
    (fun _ => True) (fun x₁ x₂ => x₁ = x₂ ∧ x₁.2.corrupted = A.initial κ)
    program (queriesSatisfy_sumTrue _) (sA, rs) (sA, rs) ⟨rfl, hrs⟩ pure pure
    (fun _ _ _ hR => hR.1 ▸ rfl)
    fun q ⟨sA₁, rs₁⟩ ⟨sA₂, rs₂⟩ k₁ k₂ _ hR hcont => ?_
  rcases hR with ⟨hEq, hrs₁⟩
  cases hEq
  rcases q with (⟨i, x⟩ | _) | a
  · erw [adaptiveExecMachine_handle_inl_party]
    by_cases hi : i ∈ rs₁.corrupted
    · simp only [hi, ↓reduceIte]
      erw [pure_bind]
      exact hcont none _ _ ⟨rfl, hrs₁⟩
    · simp only [hi, ↓reduceIte]
      erw [bind_assoc, bind_assoc]
      refine bind_congr fun ⟨out, s'⟩ => ?_
      erw [pure_bind]
      exact hcont out _ _ ⟨rfl, hrs₁⟩
  · erw [adaptiveExecMachine_handle_inl_status]
    erw [pure_bind]
    exact hcont rs₁.corrupted _ _ ⟨rfl, hrs₁⟩
  · change (fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
        (adaptiveRouter .static P κ (A.initial κ)).runFrom
          (liftAdaptiveNet (((A.machine κ).handle a).run sA₁)) rs₁ >>= k₁ =
      (fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
        (adaptiveRouter .adaptive P κ (A.initial κ)).runFrom
          (liftAdaptiveNet (((A.machine κ).handle a).run sA₁)) rs₁ >>= k₂
    erw [bind_map_left, bind_map_left]
    exact runFrom_adaptiveRouter_liftAdaptiveNet_static_eq_adaptive P κ (A.initial κ)
      (((A.machine κ).handle a).run sA₁) (hno κ a sA₁) rs₁ hrs₁ _ _ fun res rs' hrs' =>
      hcont res.1 (res.2, rs') (res.2, rs') ⟨rfl, hrs'⟩

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
  rw [liftAdaptiveNet, liftStaticNetProgram, liftNet, interpret_sumHandler_comp]
  have hcomp :
      (fun (q : RoutedNetQ n In NetQ) => OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query (spec := probOracleSpec
            (adaptivePartySpec n In Out ⊕ₒ
              netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)))
            (.inl k))
          (fun q => ProbOracleComp.query
            (spec := adaptivePartySpec n In Out ⊕ₒ
              netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))
            (.inr q)))
        (match q with
          | .inl (i, x) => AdaptiveNetR.toRoutedNetR <$> ProbOracleComp.query (.party i x)
          | .inr nq => AdaptiveNetR.toRoutedNetR <$> ProbOracleComp.query (.net nq))) =
        (fun (q : RoutedNetQ n In NetQ) => match q with
          | .inl (i, x) => AdaptiveNetR.toRoutedNetR <$>
              ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View)
                (.inr (.party i x))
          | .inr nq => AdaptiveNetR.toRoutedNetR <$>
              ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View)
                (.inr (.net nq))) := by
    funext q; rcases q with ⟨i, x⟩ | nq <;>
      exact (OracleComp.interpret_map _ _ _).trans (congrArg _ (OracleComp.interpret_query _ _))
  rw [hcomp]
  refine runFrom_interpret_intertwine
    (adaptiveRouter .static P κ C₀) (corruptRouter C₀ (P.toStatic κ C₀))
    (fun (q : RoutedNetQ n In NetQ) => match q with
      | .inl (i, x) => AdaptiveNetR.toRoutedNetR <$>
          ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View)
            (.inr (.party i x))
      | .inr nq => AdaptiveNetR.toRoutedNetR <$>
          ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View)
            (.inr (.net nq)))
    (fun (q : RoutedNetQ n In NetQ) => ProbOracleComp.query
      (spec := protocolSpec n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) (.inr q))
    (fun _ => True) (fun rs' sP => rs'.corrupted = C₀ ∧ rs'.inner = sP)
    netProg (queriesSatisfy_sumTrue _) rs rs.inner ⟨hrs, rfl⟩ f g
    (fun a rs' sP hR => hR.2 ▸ hfg a rs' hR.1)
    fun q rs' sP k₁ k₂ _ ⟨hrs', hsP⟩ hcont => by
      rcases hsP with rfl
      erw [Machine.runFrom_query]
      rcases q with ⟨i, x⟩ | nq
      · erw [Machine.runFrom_map, Machine.runFrom_query, bind_map_left,
          adaptiveRouter_handle_inr_party]
        simp only [corruptRouter, AdaptiveProtocol.toStatic]
        by_cases hi : i ∈ C₀
        · have hi' : i ∈ rs'.corrupted := hrs' ▸ hi
          simp only [hi, hi', ↓reduceIte, StateT.run_map]
          erw [bind_assoc, bind_map_left]
          refine bind_congr fun p => ?_
          erw [pure_bind]
          exact hcont (.inl p.1) _ _ ⟨hrs', rfl⟩
        · have hi' : i ∉ rs'.corrupted := hrs' ▸ hi
          simp only [hi, hi', ↓reduceIte, StateT.run_pure]
          erw [pure_bind, pure_bind]
          exact hcont (.inl none) _ _ ⟨hrs', rfl⟩
      · erw [Machine.runFrom_map, Machine.runFrom_query, bind_map_left,
          adaptiveRouter_handle_inr_net]
        simp only [corruptRouter, AdaptiveProtocol.toStatic, StateT.run_map]
        erw [bind_assoc, bind_map_left]
        refine bind_congr fun p => ?_
        erw [pure_bind]
        exact hcont (.inr p.1) _ _ ⟨hrs', rfl⟩

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
  rw [liftPartyQuery]
  conv_rhs => rw [← interpret_sumHandler_id program]
  refine runFrom_interpret_intertwine
    (adaptiveExecMachine .static P (AdaptiveAdversary.ofStatic A C) κ)
    (execMachine P.toStatic A κ (C κ))
    (fun q => match q with
      | .inl (i, x) => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR)
          (.inl (.party i x))
      | .inr a => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR) (.inr a))
    (fun q => ProbOracleComp.query (spec := execSpec n In Out AdvQ AdvR) q)
    (fun _ => True)
    (fun x₁ x₂ => x₁.1 = x₂.1 ∧ x₁.2.corrupted = C κ ∧ x₁.2.inner = x₂.2)
    program (queriesSatisfy_sumTrue _) (sA, rs) (sA, rs.inner) ⟨rfl, hrs, rfl⟩ f g
    (fun a ⟨sA₁, rs₁⟩ ⟨sA₂, sP⟩ ⟨hsA, hrs₁, hsP⟩ => by
      subst hsA; subst hsP; exact hfg a sA₁ rs₁ hrs₁)
    fun q ⟨sA₁, rs₁⟩ ⟨sA₂, sP⟩ k₁ k₂ _ ⟨hsA, hrs₁, hsP⟩ hcont => by
      subst hsA; subst hsP
      rcases q with ⟨i, x⟩ | a
      · erw [Machine.runFrom_query, Machine.runFrom_query, adaptiveExecMachine_handle_inl_party]
        dsimp only [execMachine, Machine.comp, liftAdversary, StateT.lift, StateT.run]
        erw [Machine.runFrom_bind, Machine.runFrom_query, bind_map_left, bind_assoc]
        simp only [corruptRouter, AdaptiveProtocol.toStatic]
        by_cases hi : i ∈ C κ
        · have hi' : i ∈ rs₁.corrupted := hrs₁ ▸ hi
          simp only [hi, hi', ↓reduceIte, StateT.run_pure]
          erw [pure_bind, pure_bind, Machine.runFrom_pure, pure_bind]
          exact hcont none _ _ ⟨rfl, hrs₁, rfl⟩
        · have hi' : i ∉ rs₁.corrupted := hrs₁ ▸ hi
          simp only [hi, hi', ↓reduceIte]
          erw [bind_assoc]
          refine bind_congr fun p => ?_
          erw [Machine.runFrom_pure, pure_bind, pure_bind]
          exact hcont p.1 _ _ ⟨rfl, hrs₁, rfl⟩
      · erw [Machine.runFrom_query, Machine.runFrom_query]
        change (fun (p : (AdvR × (A κ (C κ)).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
            (adaptiveRouter .static P κ (C κ)).runFrom
              (liftAdaptiveNet (liftStaticNetProgram (((A κ (C κ)).handle a).run sA₁))) rs₁ >>= k₁ =
          (fun (p : (AdvR × (A κ (C κ)).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
            (corruptRouter (C κ) (P.toStatic κ (C κ))).runFrom
              (liftNet (((A κ (C κ)).handle a).run sA₁)) rs₁.inner >>= k₂
        erw [bind_map_left, bind_map_left]
        exact runFrom_adaptiveRouter_liftStaticNetProgram P κ (C κ) (((A κ (C κ)).handle a).run sA₁)
          rs₁ hrs₁ _ _ fun res rs' hrs' =>
            hcont res.1 (res.2, rs') (res.2, rs'.inner) ⟨rfl, hrs', rfl⟩

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

/-! ### Adaptive emulation implies static emulation -/

section AdaptiveToStatic

open scoped ENNReal NNReal

variable {n : ℕ} {In Out NetQ NetR View AdvQ AdvR : Type}
variable {NetQ₁ NetR₁ View₁ NetQ₂ NetR₂ View₂ : Type}

/-- Rewrite an adaptive network program to drop `.corrupt i` queries for `i ∉ C₀` (returning
`pure (.corrupt none)`), matching `.static` router behavior. -/
@[expose] def clampNetProgram (C₀ : Finset (Fin n)) {α : Type}
    (program : ProbOracleComp
      (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α) :
    ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec
        (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))) (Sum.inl k))
      fun q => match q with
        | .party i x => ProbOracleComp.query (.party i x)
        | .corrupt i =>
            if i ∈ C₀ then ProbOracleComp.query (.corrupt i) else pure (.corrupt none)
        | .net nq => ProbOracleComp.query (.net nq))
    program

private theorem isQueryBounded_clampNetProgram (C₀ : Finset (Fin n)) {α : Type}
    {program : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α}
    {m : ℕ} (h : program.IsQueryBounded m) :
    (clampNetProgram (n := n) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      (View := View) C₀ program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  rcases q with k | (⟨i, x⟩ | i | nq)
  · exact OracleComp.IsCostBounded.query _
  · exact OracleComp.IsCostBounded.query _
  · dsimp only [sumHandler, Sum.elim_inr]
    split_ifs
    · exact OracleComp.IsCostBounded.query _
    · exact OracleComp.IsCostBounded.pure _ 1
  · exact OracleComp.IsCostBounded.query _

private theorem noNewCorrupt_clampNetProgram (C₀ : Finset (Fin n)) {α : Type}
    (program : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α) :
    NoNewCorruptProgram C₀ (clampNetProgram C₀ program) := by
  induction program using OracleComp.induction with
  | pure _ => exact .pure _
  | query_bind q _ ih =>
    rcases q with k | (⟨i, x⟩ | i | nq)
    · exact .bind (.query trivial) ih
    · exact .bind (.query trivial) ih
    · rw [clampNetProgram, OracleComp.interpret_bind, OracleComp.interpret_query]
      dsimp only [sumHandler]
      by_cases hi : i ∈ C₀
      · simp only [hi, ↓reduceIte]; exact .bind (.query hi) ih
      · simp only [hi, ↓reduceIte, pure_bind]; exact ih (.corrupt none)
    · exact .bind (.query trivial) ih

/-- Clamp an adaptive adversary so it drops any `.corrupt i` query for `i ∉ A.initial κ`. -/
@[expose] def AdaptiveAdversary.clampStatic
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) :
    AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR where
  initial := A.initial
  machine κ := {
    State := (A.machine κ).State
    init := (A.machine κ).init
    handle q s := clampNetProgram (A.initial κ) (((A.machine κ).handle q).run s) }

/-- A clamped adaptive adversary never queries `.corrupt i` for `i ∉ A.initial κ`. -/
theorem AdaptiveAdversary.noNewCorrupt_clampStatic
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) :
    A.clampStatic.NoNewCorrupt :=
  fun κ q s => noNewCorrupt_clampNetProgram (A.initial κ) (((A.machine κ).handle q).run s)

/-- Clamping an adaptive adversary preserves its call budget. -/
theorem AdaptiveAdversary.PolyBounded.clampStatic
    {A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR} {pA : Polynomial ℕ}
    (hA : A.PolyBounded pA) : A.clampStatic.PolyBounded pA := fun κ =>
  ⟨(hA κ).1, fun q s => isQueryBounded_clampNetProgram (A.initial κ) ((hA κ).2 q s)⟩

private theorem runFrom_adaptiveRouter_clampNetProgram_static {α β : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (rs : AdaptiveRouterState (P.machine κ).State View n) (hrs : rs.corrupted = C₀)
    (f g : α × AdaptiveRouterState (P.machine κ).State View n → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a rs', rs'.corrupted = C₀ → f (a, rs') = g (a, rs')) :
    ((adaptiveRouter .static P κ C₀).runFrom (liftAdaptiveNet (clampNetProgram C₀ netProg)) rs >>=
        f) =
      ((adaptiveRouter .static P κ C₀).runFrom (liftAdaptiveNet netProg) rs >>= g) := by
  rw [liftAdaptiveNet, clampNetProgram, interpret_sumHandler_comp]
  refine runFrom_interpret_intertwine
    (adaptiveRouter .static P κ C₀) (adaptiveRouter .static P κ C₀)
    _ (fun q =>
      ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View) (.inr q))
    (fun _ => True) (fun rs₁ rs₂ => rs₁ = rs₂ ∧ rs₁.corrupted = C₀)
    netProg (queriesSatisfy_sumTrue _) rs rs ⟨rfl, hrs⟩ f g
    (fun a rs₁ rs₂ hR => hR.1 ▸ hfg a rs₁ hR.2)
    fun q rs₁ rs₂ k₁ k₂ _ hR hcont => ?_
  rcases hR with ⟨rfl, hrs₁⟩
  cases q with
  | party i x =>
    erw [OracleComp.interpret_query, Machine.runFrom_query, adaptiveRouter_handle_inr_party]
    by_cases hi : i ∈ rs₁.corrupted
    · simp only [hi, ↓reduceIte]
      erw [bind_assoc, bind_assoc]
      refine bind_congr fun ⟨out, s'⟩ => ?_
      erw [pure_bind]
      exact hcont (.party out) _ _ ⟨rfl, hrs₁⟩
    · simp only [hi, ↓reduceIte]
      erw [pure_bind]
      exact hcont (.party none) _ _ ⟨rfl, hrs₁⟩
  | net nq =>
    erw [OracleComp.interpret_query, Machine.runFrom_query, adaptiveRouter_handle_inr_net]
    erw [bind_assoc, bind_assoc]
    refine bind_congr fun ⟨r, s'⟩ => ?_
    erw [pure_bind]
    exact hcont (.net r) _ _ ⟨rfl, hrs₁⟩
  | corrupt i =>
    by_cases hi : i ∈ C₀
    · have hi' : i ∈ rs₁.corrupted := hrs₁ ▸ hi
      simp only [hi, ↓reduceIte]
      erw [OracleComp.interpret_query, Machine.runFrom_query,
        adaptiveRouter_handle_inr_corrupt_static]
      simp only [hi', ↓reduceIte]
      erw [pure_bind]
      exact hcont (.corrupt (some (P.corruptionReport κ i rs₁))) _ _ ⟨rfl, hrs₁⟩
    · have hi' : i ∉ rs₁.corrupted := hrs₁ ▸ hi
      simp only [hi, ↓reduceIte, OracleComp.interpret_pure]
      erw [Machine.runFrom_pure, Machine.runFrom_query, adaptiveRouter_handle_inr_corrupt_static]
      simp only [hi', ↓reduceIte, pure_bind]
      exact hcont (.corrupt none) _ _ ⟨rfl, hrs₁⟩

private theorem runFrom_adaptiveExecMachine_clampStatic {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n)
    (hrs : rs.corrupted = A.initial κ) :
    (adaptiveExecMachine .static P A.clampStatic κ).runFrom program (sA, rs) =
      (adaptiveExecMachine .static P A κ).runFrom program (sA, rs) := by
  suffices h :
      ((adaptiveExecMachine .static P A.clampStatic κ).runFrom program (sA, rs) >>= pure) =
        ((adaptiveExecMachine .static P A κ).runFrom program (sA, rs) >>= pure) by
    simpa only [bind_pure] using h
  refine runFrom_intertwine
    (adaptiveExecMachine .static P A.clampStatic κ) (adaptiveExecMachine .static P A κ)
    (fun _ => True) (fun x₁ x₂ => x₁ = x₂ ∧ x₁.2.corrupted = A.initial κ)
    program (queriesSatisfy_sumTrue _) (sA, rs) (sA, rs) ⟨rfl, hrs⟩ pure pure
    (fun _ _ _ hR => hR.1 ▸ rfl)
    fun q ⟨sA₁, rs₁⟩ ⟨sA₂, rs₂⟩ k₁ k₂ _ hR hcont => ?_
  rcases hR with ⟨hEq, hrs₁⟩
  cases hEq
  rcases q with (⟨i, x⟩ | _) | a
  · erw [adaptiveExecMachine_handle_inl_party]
    by_cases hi : i ∈ rs₁.corrupted
    · simp only [hi, ↓reduceIte]
      erw [pure_bind]
      exact hcont none _ _ ⟨rfl, hrs₁⟩
    · simp only [hi, ↓reduceIte]
      erw [bind_assoc, bind_assoc]
      refine bind_congr fun ⟨out, s'⟩ => ?_
      erw [pure_bind]
      exact hcont out _ _ ⟨rfl, hrs₁⟩
  · erw [adaptiveExecMachine_handle_inl_status]
    erw [pure_bind]
    exact hcont rs₁.corrupted _ _ ⟨rfl, hrs₁⟩
  · change (fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
        (adaptiveRouter .static P κ (A.initial κ)).runFrom
          (liftAdaptiveNet (clampNetProgram (A.initial κ) (((A.machine κ).handle a).run sA₁)))
          rs₁ >>= k₁ =
      (fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
        (adaptiveRouter .static P κ (A.initial κ)).runFrom
          (liftAdaptiveNet (((A.machine κ).handle a).run sA₁)) rs₁ >>= k₂
    erw [bind_map_left, bind_map_left]
    exact runFrom_adaptiveRouter_clampNetProgram_static P κ (A.initial κ)
      (((A.machine κ).handle a).run sA₁) rs₁ hrs₁ _ _ fun res rs' hrs' =>
      hcont res.1 (res.2, rs') (res.2, rs') ⟨rfl, hrs'⟩

/-- Clamping `A` does not change `.static` execution. -/
theorem adaptiveExec_static_clampStatic
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec .static P A.clampStatic Z κ z = adaptiveExec .static P A Z κ z := by
  simp only [adaptiveExec, Machine.run, Machine.link]
  refine congrArg Machine.closeProgram ?_
  erw [sample_adaptiveExecMachine_init, sample_adaptiveExecMachine_init]
  refine bind_congr fun s₀ => bind_congr fun sA => ?_
  exact congrArg (Prod.fst <$> ·)
    (runFrom_adaptiveExecMachine_clampStatic P A κ (Z κ z) sA _ rfl)

/-- In `.static` mode, any adversary `A` executes identically to `A.clampStatic` in `.adaptive`
mode. -/
theorem adaptiveExec_static_eq_adaptive_clampStatic
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec .static P A Z κ z = adaptiveExec .adaptive P A.clampStatic Z κ z :=
  (adaptiveExec_static_clampStatic P A Z κ z).symm.trans
    (adaptiveExec_static_eq_adaptive_of_noCorrupt P A.clampStatic A.noNewCorrupt_clampStatic
      Z κ z)

/-! #### Closing and evaluating joint router states for `static_of_adaptive` -/

/-- Close an empty-spec probabilistic computation and return its `PMF`. -/
@[expose] noncomputable def closeEval {α : Type}
    (program : ProbOracleComp OracleSpec.empty α) : PMF α :=
  ProbComp.eval (Machine.closeProgram program)

@[simp] theorem closeEval_pure {α : Type} (a : α) :
    closeEval (pure a) = PMF.pure a := rfl

@[simp] theorem closeEval_bind {α β : Type} (p : ProbOracleComp OracleSpec.empty α)
    (next : α → ProbOracleComp OracleSpec.empty β) :
    closeEval (p >>= next) = (closeEval p).bind fun a => closeEval (next a) := by
  simp only [closeEval, Machine.closeProgram_bind, ProbComp.eval_bind]

@[simp] theorem closeEval_map {α β : Type} (f : α → β)
    (p : ProbOracleComp OracleSpec.empty α) :
    closeEval (f <$> p) = (closeEval p).map f := by
  simp only [closeEval, Machine.closeProgram_map, ProbComp.eval_map]

@[simp] theorem closeEval_sample {α : Type} (p : ProbComp α) :
    closeEval (ProbOracleComp.sample p) = p.eval := by
  simp only [closeEval, Machine.closeProgram_sample]

private noncomputable def execState (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    {α : Type} (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (κ : ℕ) :
    PMF (α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n)) :=
  closeEval (ProbOracleComp.sample (adaptiveExecMachine mode P A κ).init >>=
    fun s => (adaptiveExecMachine mode P A κ).runFrom program s)

private def queryStatus :
    ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) (Finset (Fin n)) :=
  ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR) (.inl .status)

private theorem eval_adaptiveExec_eq_execState_map (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    (adaptiveExec mode P A Z κ z).eval = (execState mode P A (Z κ z) κ).map Prod.fst := by
  change closeEval (ProbOracleComp.sample (adaptiveExecMachine mode P A κ).init >>=
      fun s => Prod.fst <$> (adaptiveExecMachine mode P A κ).runFrom (Z κ z) s) =
    (closeEval (ProbOracleComp.sample (adaptiveExecMachine mode P A κ).init >>=
      fun s => (adaptiveExecMachine mode P A κ).runFrom (Z κ z) s)).map Prod.fst
  rw [closeEval_bind, closeEval_bind, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun s => ?_)
  exact closeEval_map Prod.fst _

private theorem eval_adaptiveExec_status_post (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (f : Bool → Finset (Fin n) → Bool)
    (κ : ℕ) (z : List Bool) :
    (adaptiveExec mode P A (fun κ z => do
        let b ← Z κ z
        let C ← queryStatus
        pure (f b C)) κ z).eval =
      (execState mode P A (Z κ z) κ).map fun x => f x.1 x.2.2.corrupted := by
  change closeEval (ProbOracleComp.sample (adaptiveExecMachine mode P A κ).init >>=
      fun s => Prod.fst <$> (adaptiveExecMachine mode P A κ).runFrom
        (Z κ z >>= fun b => queryStatus >>= fun C => pure (f b C)) s) =
    (closeEval (ProbOracleComp.sample (adaptiveExecMachine mode P A κ).init >>=
      fun s => (adaptiveExecMachine mode P A κ).runFrom (Z κ z) s)).map
        fun x => f x.1 x.2.2.corrupted
  have hrun (s : (adaptiveExecMachine mode P A κ).State) :
      Prod.fst <$> (adaptiveExecMachine mode P A κ).runFrom
          (Z κ z >>= fun b => queryStatus >>= fun C => pure (f b C)) s =
        (fun x => f x.1 x.2.2.corrupted) <$>
          (adaptiveExecMachine mode P A κ).runFrom (Z κ z) s := by
    rcases s with ⟨sA, rs⟩
    erw [Machine.runFrom_bind, map_eq_pure_bind, map_eq_pure_bind, bind_assoc]
    refine bind_congr fun ⟨b, sA', rs'⟩ => ?_
    erw [Machine.runFrom_bind, queryStatus, Machine.runFrom_query,
      adaptiveExecMachine_handle_inl_status]
    simp only [Machine.runFrom_pure]
    rfl
  simp_rw [hrun]
  rw [closeEval_bind, closeEval_bind, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun s => ?_)
  erw [closeEval_map]

private theorem mem_support_closeEval_runFrom_invariant {ιE α : Type} {E : ιE → Type}
    (M : Machine OracleSpec.empty E) (Inv : ιE → Prop) (R : M.State → M.State → Prop)
    (hR_refl : ∀ s, R s s) (hR_trans : ∀ {a b c}, R a b → R b c → R a c)
    (prog : ProbOracleComp E α)
    (hinv : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) prog)
    (s : M.State) {x : α × M.State}
    (hx : x ∈ (closeEval (M.runFrom prog s)).support)
    (hstep : ∀ (q : ιE) (s' : M.State) {y : E q × M.State},
      Inv q → y ∈ (closeEval ((M.handle q).run s')).support → R s' y.2) :
    R s x.2 := by
  induction prog using OracleComp.induction generalizing s with
  | pure a =>
    erw [Machine.runFrom_pure, closeEval_pure, PMF.mem_support_pure_iff] at hx
    rcases hx with rfl
    exact hR_refl s
  | query_bind q cont ih =>
    rcases q with k | q
    · erw [Machine.runFrom_bind, Machine.runFrom_call, StateT.run_lift, bind_pure_comp,
        closeEval_bind, PMF.mem_support_bind_iff] at hx
      rcases hx with ⟨y, hy, hx'⟩
      erw [closeEval_map, PMF.mem_support_map_iff] at hy
      rcases hy with ⟨a, _, rfl⟩
      exact ih a ((OracleComp.QueriesSatisfy.liftBind_iff.mp hinv).2 a) s hx'
    · have hq := OracleComp.QueriesSatisfy.liftBind_iff.mp hinv
      erw [Machine.runFrom_bind, Machine.runFrom_query, closeEval_bind,
        PMF.mem_support_bind_iff] at hx
      rcases hx with ⟨y, hy, hx'⟩
      exact hR_trans (hstep q s hq.1 hy) (ih y.1 (hq.2 y.1) y.2 hx')

private theorem queriesSatisfy_liftAdaptiveNet {C₀ : Finset (Fin n)} {α : Type}
    {netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α}
    (hno : NoNewCorruptProgram C₀ netProg) :
    OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => match q with | .inr (.corrupt i) => i ∈ C₀ | _ => True)
      (liftAdaptiveNet (n := n) (In := In) (Out := Out) netProg) := by
  induction netProg using OracleComp.induction with
  | pure _ => exact .pure _
  | query_bind q _ ih =>
    have hq := OracleComp.QueriesSatisfy.liftBind_iff.mp hno
    rcases q with k | (⟨i, x⟩ | i | nq)
    · rw [liftAdaptiveNet_bind, liftAdaptiveNet_unifFin]
      exact .bind (.query trivial) fun a => ih a (hq.2 a)
    · rw [liftAdaptiveNet_bind]; erw [liftAdaptiveNet_query]
      exact .bind (.query trivial) fun a => ih a (hq.2 a)
    · rw [liftAdaptiveNet_bind]; erw [liftAdaptiveNet_query]
      exact .bind (.query hq.1) fun a => ih a (hq.2 a)
    · rw [liftAdaptiveNet_bind]; erw [liftAdaptiveNet_query]
      exact .bind (.query trivial) fun a => ih a (hq.2 a)

private theorem corrupted_subset_of_mem_support_router {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (rs : AdaptiveRouterState (P.machine κ).State View n)
    {x : α × AdaptiveRouterState (P.machine κ).State View n}
    (hx : x ∈ (closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
      (liftAdaptiveNet netProg) rs)).support) :
    rs.corrupted ⊆ x.2.corrupted := by
  refine mem_support_closeEval_runFrom_invariant (adaptiveRouter .adaptive P κ C₀)
    (fun _ => True) (fun s₁ s₂ => s₁.corrupted ⊆ s₂.corrupted)
    (fun _ => Finset.Subset.rfl) Finset.Subset.trans (liftAdaptiveNet netProg)
    (queriesSatisfy_sumTrue _) rs hx fun q s' y _ hy => ?_
  rcases q with (⟨i, u⟩ | _) | (⟨i, u⟩ | i | nq)
  · erw [adaptiveRouter_handle_inl_party] at hy
    by_cases hi : i ∈ s'.corrupted <;> simp only [hi, ↓reduceIte] at hy
    · erw [closeEval_pure, PMF.mem_support_pure_iff] at hy
      rcases hy with rfl; exact Finset.Subset.rfl
    · erw [closeEval_bind, PMF.mem_support_bind_iff] at hy
      rcases hy with ⟨⟨_, s''⟩, _, hy'⟩
      erw [closeEval_pure, PMF.mem_support_pure_iff] at hy'
      rcases hy' with rfl; exact Finset.Subset.rfl
  · erw [adaptiveRouter_handle_inl_status] at hy
    erw [closeEval_pure, PMF.mem_support_pure_iff] at hy
    rcases hy with rfl; exact Finset.Subset.rfl
  · erw [adaptiveRouter_handle_inr_party] at hy
    by_cases hi : i ∈ s'.corrupted <;> simp only [hi, ↓reduceIte] at hy
    · erw [closeEval_bind, PMF.mem_support_bind_iff] at hy
      rcases hy with ⟨⟨_, s''⟩, _, hy'⟩
      erw [closeEval_pure, PMF.mem_support_pure_iff] at hy'
      rcases hy' with rfl; exact Finset.Subset.rfl
    · erw [closeEval_pure, PMF.mem_support_pure_iff] at hy
      rcases hy with rfl; exact Finset.Subset.rfl
  · erw [adaptiveRouter_handle_inr_corrupt_adaptive] at hy
    erw [closeEval_pure, PMF.mem_support_pure_iff] at hy; rcases hy with rfl
    by_cases hi : i ∈ s'.corrupted <;> simp [hi, Finset.subset_insert]
  · erw [adaptiveRouter_handle_inr_net] at hy
    erw [closeEval_bind, PMF.mem_support_bind_iff] at hy
    rcases hy with ⟨⟨_, s''⟩, _, hy'⟩
    erw [closeEval_pure, PMF.mem_support_pure_iff] at hy'
    rcases hy' with rfl; exact Finset.Subset.rfl

private theorem corrupted_subset_of_mem_support_execMachine {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n)
    {x : α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n)}
    (hx : x ∈
      (closeEval ((adaptiveExecMachine .adaptive P A κ).runFrom program (sA, rs))).support) :
    rs.corrupted ⊆ x.2.2.corrupted := by
  refine mem_support_closeEval_runFrom_invariant (adaptiveExecMachine .adaptive P A κ)
    (fun _ => True) (fun s₁ s₂ => s₁.2.corrupted ⊆ s₂.2.corrupted)
    (fun _ => Finset.Subset.rfl) Finset.Subset.trans program
    (queriesSatisfy_sumTrue _) (sA, rs) hx fun q ⟨sA', rs'⟩ y _ hy => ?_
  rcases q with (⟨i, u⟩ | _) | a
  · erw [adaptiveExecMachine_handle_inl_party] at hy
    by_cases hi : i ∈ rs'.corrupted <;> simp only [hi, ↓reduceIte] at hy
    · erw [closeEval_pure, PMF.mem_support_pure_iff] at hy
      rcases hy with rfl; exact Finset.Subset.rfl
    · erw [closeEval_bind, PMF.mem_support_bind_iff] at hy
      rcases hy with ⟨⟨_, _⟩, _, hy'⟩
      erw [closeEval_pure, PMF.mem_support_pure_iff] at hy'
      rcases hy' with rfl; exact Finset.Subset.rfl
  · erw [adaptiveExecMachine_handle_inl_status] at hy
    erw [closeEval_pure, PMF.mem_support_pure_iff] at hy
    rcases hy with rfl; exact Finset.Subset.rfl
  · change y ∈ (closeEval ((fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
        (adaptiveRouter .adaptive P κ (A.initial κ)).runFrom
          (liftAdaptiveNet (((A.machine κ).handle a).run sA')) rs')).support at hy
    erw [closeEval_map, PMF.mem_support_map_iff] at hy
    rcases hy with ⟨⟨⟨r, sA''⟩, rs''⟩, hz, rfl⟩
    exact corrupted_subset_of_mem_support_router P κ (A.initial κ) _ rs'
      (x := ((r, sA''), rs'')) hz

private theorem corrupted_eq_of_mem_support_noNewCorrupt_router {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (hno : NoNewCorruptProgram C₀ netProg)
    (rs : AdaptiveRouterState (P.machine κ).State View n) (hrs : rs.corrupted = C₀)
    {x : α × AdaptiveRouterState (P.machine κ).State View n}
    (hx : x ∈ (closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
      (liftAdaptiveNet netProg) rs)).support) :
    x.2.corrupted = C₀ := by
  refine mem_support_closeEval_runFrom_invariant (adaptiveRouter .adaptive P κ C₀)
    (fun q => match q with | .inr (.corrupt i) => i ∈ C₀ | _ => True)
    (fun s₁ s₂ => s₁.corrupted = C₀ → s₂.corrupted = C₀)
    (fun _ h => h) (fun h₁ h₂ hc => h₂ (h₁ hc))
    (liftAdaptiveNet netProg) (queriesSatisfy_liftAdaptiveNet hno) rs hx
    (fun q s' y hq hy hs' => ?_) hrs
  rcases q with (⟨i, u⟩ | _) | (⟨i, u⟩ | i | nq)
  · erw [adaptiveRouter_handle_inl_party] at hy
    by_cases hi : i ∈ s'.corrupted <;> simp only [hi, ↓reduceIte] at hy
    · erw [closeEval_pure, PMF.mem_support_pure_iff] at hy; rcases hy with rfl; exact hs'
    · erw [closeEval_bind, PMF.mem_support_bind_iff] at hy
      rcases hy with ⟨⟨_, _⟩, _, hy'⟩
      erw [closeEval_pure, PMF.mem_support_pure_iff] at hy'; rcases hy' with rfl; exact hs'
  · erw [adaptiveRouter_handle_inl_status] at hy
    erw [closeEval_pure, PMF.mem_support_pure_iff] at hy; rcases hy with rfl; exact hs'
  · erw [adaptiveRouter_handle_inr_party] at hy
    by_cases hi : i ∈ s'.corrupted <;> simp only [hi, ↓reduceIte] at hy
    · erw [closeEval_bind, PMF.mem_support_bind_iff] at hy
      rcases hy with ⟨⟨_, _⟩, _, hy'⟩
      erw [closeEval_pure, PMF.mem_support_pure_iff] at hy'; rcases hy' with rfl; exact hs'
    · erw [closeEval_pure, PMF.mem_support_pure_iff] at hy; rcases hy with rfl; exact hs'
  · have hi : i ∈ s'.corrupted := hs' ▸ hq
    erw [adaptiveRouter_handle_inr_corrupt_adaptive] at hy
    erw [closeEval_pure, PMF.mem_support_pure_iff] at hy; rcases hy with rfl
    simp only [hi, ↓reduceIte]; exact hs'
  · erw [adaptiveRouter_handle_inr_net] at hy
    erw [closeEval_bind, PMF.mem_support_bind_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, hy'⟩
    erw [closeEval_pure, PMF.mem_support_pure_iff] at hy'; rcases hy' with rfl; exact hs'

private theorem corrupted_eq_of_mem_support_execMachine_noNewCorrupt
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (hno : A.NoNewCorrupt) {α : Type}
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α) (κ : ℕ)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n)
    (hrs : rs.corrupted = A.initial κ)
    {y : α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n)}
    (hy : y ∈
      (closeEval ((adaptiveExecMachine .adaptive P A κ).runFrom program (sA, rs))).support) :
    y.2.2.corrupted = A.initial κ := by
  refine mem_support_closeEval_runFrom_invariant (adaptiveExecMachine .adaptive P A κ)
    (fun _ => True) (fun s₁ s₂ => s₁.2.corrupted = A.initial κ → s₂.2.corrupted = A.initial κ)
    (fun _ h => h) (fun h₁ h₂ hc => h₂ (h₁ hc))
    program (queriesSatisfy_sumTrue _) (sA, rs) hy
    (fun q ⟨sA', rs'⟩ z _ hz hrs' => ?_) hrs
  rcases q with (⟨i, u⟩ | _) | a
  · erw [adaptiveExecMachine_handle_inl_party] at hz
    by_cases hi : i ∈ rs'.corrupted <;> simp only [hi, ↓reduceIte] at hz
    · erw [closeEval_pure, PMF.mem_support_pure_iff] at hz; rcases hz with rfl; exact hrs'
    · erw [closeEval_bind, PMF.mem_support_bind_iff] at hz
      rcases hz with ⟨⟨_, _⟩, _, hz'⟩
      erw [closeEval_pure, PMF.mem_support_pure_iff] at hz'; rcases hz' with rfl; exact hrs'
  · erw [adaptiveExecMachine_handle_inl_status] at hz
    erw [closeEval_pure, PMF.mem_support_pure_iff] at hz; rcases hz with rfl; exact hrs'
  · change z ∈ (closeEval ((fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
        (adaptiveRouter .adaptive P κ (A.initial κ)).runFrom
          (liftAdaptiveNet (((A.machine κ).handle a).run sA')) rs')).support at hz
    erw [closeEval_map, PMF.mem_support_map_iff] at hz
    rcases hz with ⟨w, hw, rfl⟩
    exact corrupted_eq_of_mem_support_noNewCorrupt_router P κ (A.initial κ) _ (hno κ a sA') rs'
      hrs' hw

private theorem corrupted_eq_of_mem_support_execState_noNewCorrupt
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (hno : A.NoNewCorrupt) {α : Type}
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α) (κ : ℕ)
    {x : α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n)}
    (hx : x ∈ (execState .adaptive P A program κ).support) :
    x.2.2.corrupted = A.initial κ := by
  simp only [execState] at hx
  erw [sample_adaptiveExecMachine_init, closeEval_bind, PMF.mem_support_bind_iff] at hx
  rcases hx with ⟨s₀, _, hx⟩
  erw [closeEval_bind, PMF.mem_support_bind_iff] at hx
  rcases hx with ⟨sA, _, hx⟩
  exact corrupted_eq_of_mem_support_execMachine_noNewCorrupt P A hno program κ sA _ rfl hx

private theorem closeEval_router_adaptive_le_clamp {α β : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (rs : AdaptiveRouterState (P.machine κ).State View n) (hrs : rs.corrupted = C₀)
    (f g : α × AdaptiveRouterState (P.machine κ).State View n → ProbOracleComp OracleSpec.empty β)
    (y : β)
    (hfg : ∀ (a : α) (rs₁ : AdaptiveRouterState (P.machine κ).State View n),
      rs₁.corrupted = C₀ → closeEval (f (a, rs₁)) y ≤ closeEval (g (a, rs₁)) y)
    (hzero : ∀ (a : α) (rs₁ : AdaptiveRouterState (P.machine κ).State View n),
      ¬ (rs₁.corrupted ⊆ C₀) → closeEval (f (a, rs₁)) y = 0) :
    closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
        (liftAdaptiveNet netProg) rs >>= f) y ≤
      closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
        (liftAdaptiveNet (clampNetProgram C₀ netProg)) rs >>= g) y := by
  induction netProg using OracleComp.induction generalizing rs with
  | pure a =>
    change closeEval (f (a, rs)) y ≤ closeEval (g (a, rs)) y
    exact hfg a rs hrs
  | query_bind q cont ih =>
    rcases q with k | q
    · have hcall :
          liftAdaptiveNet (n := n) (In := In) (Out := Out)
              (Q := AdaptiveNetQ n In NetQ) (R := AdaptiveNetR Out NetR View)
              (OracleComp.query (spec := probOracleSpec
                (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))) (Sum.inl k)) =
            OracleComp.query (Sum.inl k) := rfl
      rw [clampNetProgram, OracleComp.interpret_bind, OracleComp.interpret_query]
      dsimp only [sumHandler]
      erw [liftAdaptiveNet_bind, liftAdaptiveNet_bind, hcall,
        Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_call, StateT.run_lift]
      erw [bind_assoc]; conv_rhs => erw [bind_assoc]
      erw [bind_assoc]; conv_rhs => erw [bind_assoc]
      erw [closeEval_bind]; conv_rhs => erw [closeEval_bind]
      erw [PMF.bind_apply, PMF.bind_apply]
      refine tsum_le_tsum fun a => ?_
      erw [pure_bind, pure_bind]
      exact mul_le_mul_of_nonneg_left (ih a rs hrs) zero_le
    · cases q with
      | party i u =>
        rw [clampNetProgram, OracleComp.interpret_bind, OracleComp.interpret_query,
          liftAdaptiveNet_bind, liftAdaptiveNet_bind, liftAdaptiveNet_query]
        erw [liftAdaptiveNet_query, Machine.runFrom_bind, Machine.runFrom_bind,
          Machine.runFrom_query]
        erw [bind_assoc, bind_assoc]
        erw [adaptiveRouter_handle_inr_party]
        by_cases hi : i ∈ C₀
        · have hi' : i ∈ rs.corrupted := hrs ▸ hi
          simp only [hi', ↓reduceIte]
          erw [bind_assoc, bind_assoc]
          rw [closeEval_bind, closeEval_bind, PMF.bind_apply, PMF.bind_apply]
          refine tsum_le_tsum fun ⟨out, s'⟩ => ?_
          erw [pure_bind, pure_bind]
          exact mul_le_mul_of_nonneg_left
            (ih (.party out) (P.recordSnapshot κ s' rs.corrupted rs.trace) hrs) zero_le
        · have hi' : i ∉ rs.corrupted := hrs ▸ hi
          simp only [hi', ↓reduceIte]
          erw [pure_bind, pure_bind]
          exact ih (.party none) rs hrs
      | net nq =>
        rw [clampNetProgram, OracleComp.interpret_bind, OracleComp.interpret_query,
          liftAdaptiveNet_bind, liftAdaptiveNet_bind, liftAdaptiveNet_query]
        erw [liftAdaptiveNet_query, Machine.runFrom_bind, Machine.runFrom_bind,
          Machine.runFrom_query]
        erw [bind_assoc, bind_assoc]
        erw [adaptiveRouter_handle_inr_net]
        erw [bind_assoc, bind_assoc]
        rw [closeEval_bind, closeEval_bind, PMF.bind_apply, PMF.bind_apply]
        refine tsum_le_tsum fun ⟨r, s'⟩ => ?_
        erw [pure_bind, pure_bind]
        exact mul_le_mul_of_nonneg_left
          (ih (.net r) (P.recordSnapshot κ s' rs.corrupted rs.trace) hrs) zero_le
      | corrupt i =>
        rw [clampNetProgram, OracleComp.interpret_bind, OracleComp.interpret_query]
        by_cases hi : i ∈ C₀
        · simp only [sumHandler, hi, ↓reduceIte, liftAdaptiveNet_bind]
          rw [liftAdaptiveNet_query]
          erw [liftAdaptiveNet_query, Machine.runFrom_bind, Machine.runFrom_bind,
            Machine.runFrom_query]
          erw [bind_assoc, bind_assoc]
          erw [adaptiveRouter_handle_inr_corrupt_adaptive]
          have hi' : i ∈ rs.corrupted := hrs ▸ hi
          simp only [hi', ↓reduceIte]
          erw [pure_bind, pure_bind]
          exact ih (.corrupt (some (P.corruptionReport κ i rs))) rs hrs
        · simp only [sumHandler, hi, ↓reduceIte, pure_bind, liftAdaptiveNet_bind]
          erw [liftAdaptiveNet_query, Machine.runFrom_bind, Machine.runFrom_query]
          erw [bind_assoc]
          erw [adaptiveRouter_handle_inr_corrupt_adaptive]
          have hi' : i ∉ rs.corrupted := hrs ▸ hi
          simp only [hi', ↓reduceIte]
          erw [pure_bind]
          let rs₁ : AdaptiveRouterState (P.machine κ).State View n :=
            { inner := P.onCorrupt κ i rs.inner
              corrupted := insert i rs.corrupted
              trace := rs.trace }
          have hsub_zero : closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
              (liftAdaptiveNet (cont (.corrupt (some (P.corruptionReport κ i rs₁))))) rs₁ >>= f)
              y = 0 := by
            erw [closeEval_bind, PMF.bind_apply, tsum_eq_zero_iff]
            intro z
            by_cases hz : closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
                (liftAdaptiveNet (cont (.corrupt (some (P.corruptionReport κ i rs₁))))) rs₁) z = 0
            · exact mul_eq_zero_of_left hz _
            · have hzsup : z ∈ (closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
                  (liftAdaptiveNet (cont (.corrupt (some (P.corruptionReport κ i rs₁)))))
                  rs₁)).support := by
                erw [PMF.mem_support_iff]; exact hz
              have hinc := corrupted_subset_of_mem_support_router P κ C₀ _ rs₁ hzsup
              have hnot : ¬ (z.2.corrupted ⊆ C₀) := fun hsub =>
                hi (hsub (hinc (Finset.mem_insert_self i rs.corrupted)))
              exact mul_eq_zero_of_right _ (hzero z.1 z.2 hnot)
          rw [hsub_zero]
          exact zero_le

private theorem closeEval_execMachine_adaptive_le_clampStatic {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n)
    (hrs : rs.corrupted = A.initial κ)
    (y : α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n))
    (hy : y.2.2.corrupted = A.initial κ) :
    closeEval ((adaptiveExecMachine .adaptive P A κ).runFrom program (sA, rs)) y ≤
      closeEval ((adaptiveExecMachine .adaptive P A.clampStatic κ).runFrom program (sA, rs)) y := by
  induction program using OracleComp.induction generalizing sA rs with
  | pure a =>
    change closeEval (pure (a, (sA, rs))) y ≤ closeEval (pure (a, (sA, rs))) y
    exact le_rfl
  | query_bind q cont ih =>
    rcases q with k | q
    · erw [Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_call,
        StateT.run_lift, bind_pure_comp, bind_map_left, bind_map_left]
      erw [closeEval_bind]; conv_rhs => erw [closeEval_bind]
      erw [PMF.bind_apply, PMF.bind_apply]
      exact tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (ih a sA rs hrs) zero_le
    · erw [Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_query,
        Machine.runFrom_query]
      rcases q with (⟨i, u⟩ | _) | a
      · erw [adaptiveExecMachine_handle_inl_party]
        by_cases hi : i ∈ A.initial κ
        · have hi' : i ∈ rs.corrupted := hrs ▸ hi
          simp only [hi', ↓reduceIte]
          erw [pure_bind, pure_bind]
          exact ih none sA rs hrs
        · have hi' : i ∉ rs.corrupted := hrs ▸ hi
          simp only [hi', ↓reduceIte]
          erw [bind_assoc]; conv_rhs => erw [bind_assoc]
          erw [closeEval_bind]; conv_rhs => erw [closeEval_bind]
          erw [PMF.bind_apply, PMF.bind_apply]
          refine tsum_le_tsum fun ⟨out, s'⟩ => ?_
          erw [pure_bind, pure_bind]
          exact mul_le_mul_of_nonneg_left
            (ih out sA (P.recordSnapshot κ s' rs.corrupted rs.trace) hrs) zero_le
      · erw [adaptiveExecMachine_handle_inl_status]
        erw [pure_bind, pure_bind]
        exact ih rs.corrupted sA rs hrs
      · change closeEval (((fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
            (adaptiveRouter .adaptive P κ (A.initial κ)).runFrom
              (liftAdaptiveNet (((A.machine κ).handle a).run sA)) rs) >>= _) y ≤
          closeEval (((fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
            (adaptiveRouter .adaptive P κ (A.initial κ)).runFrom
              (liftAdaptiveNet (clampNetProgram (A.initial κ) (((A.machine κ).handle a).run sA)))
              rs) >>= _) y
        erw [bind_map_left, bind_map_left]
        refine closeEval_router_adaptive_le_clamp P κ (A.initial κ)
          (((A.machine κ).handle a).run sA) rs hrs
          (fun res => (adaptiveExecMachine .adaptive P A κ).runFrom
            (cont res.1.1) (res.1.2, res.2))
          (fun res => (adaptiveExecMachine .adaptive P A.clampStatic κ).runFrom
            (cont res.1.1) (res.1.2, res.2))
          y
          (fun res rs₁ hrs₁ => ih res.1 res.2 rs₁ hrs₁)
          fun res rs₁ hnot => ?_
        by_contra hne
        have hsup : y ∈ (closeEval ((adaptiveExecMachine .adaptive P A κ).runFrom
            (cont res.1) (res.2, rs₁))).support := by
          erw [PMF.mem_support_iff]; exact hne
        have hsub := corrupted_subset_of_mem_support_execMachine P A κ (cont res.1) res.2 rs₁ hsup
        rw [hy] at hsub
        exact hnot hsub

private theorem execState_adaptive_le_clampStatic {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α) (κ : ℕ)
    (y : α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n))
    (hy : y.2.2.corrupted = A.initial κ) :
    execState .adaptive P A program κ y ≤ execState .adaptive P A.clampStatic program κ y := by
  simp only [execState]
  erw [sample_adaptiveExecMachine_init, sample_adaptiveExecMachine_init]
  erw [closeEval_bind, PMF.bind_apply]
  conv_rhs => erw [closeEval_bind, PMF.bind_apply]
  refine tsum_le_tsum fun s₀ => mul_le_mul_of_nonneg_left ?_ zero_le
  erw [closeEval_bind, PMF.bind_apply]
  conv_rhs => erw [closeEval_bind, PMF.bind_apply]
  exact tsum_le_tsum fun sA => mul_le_mul_of_nonneg_left
    (closeEval_execMachine_adaptive_le_clampStatic P A κ program sA _ rfl y hy) zero_le

private theorem apply_true_status_post_le
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (S : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂ AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool)
    (target : Bool) :
    let C₀ := S.initial κ
    let Z_post : AdaptiveEnvironment n In Out AdvQ AdvR := fun κ' z' => do
      let b ← Z κ' z'
      let C ← queryStatus
      pure ((b == target) && decide (C = C₀))
    (adaptiveExec .adaptive Q S Z_post κ z).eval true ≤
      (adaptiveExec .adaptive Q S.clampStatic Z κ z).eval target := by
  intro C₀ Z_post
  have h1 : (adaptiveExec .adaptive Q S Z_post κ z).eval true =
      ∑' x, if ((x.1 == target) && decide (x.2.2.corrupted = C₀)) = true then
        execState .adaptive Q S (Z κ z) κ x else 0 := by
    rw [eval_adaptiveExec_status_post, PMF.map_apply]
    refine tsum_congr fun x => ?_
    by_cases h1 : x.1 = target <;> by_cases h2 : x.2.2.corrupted = C₀ <;>
      simp [h1, h2, eq_comm (a := true)]
  have h2 : (adaptiveExec .adaptive Q S.clampStatic Z κ z).eval target =
      ∑' x, if x.1 = target then execState .adaptive Q S.clampStatic (Z κ z) κ x else 0 := by
    rw [eval_adaptiveExec_eq_execState_map, PMF.map_apply]
    refine tsum_congr fun x => ?_
    by_cases h1 : x.1 = target <;> simp [h1, eq_comm (a := target)]
  rw [h1, h2]
  refine tsum_le_tsum fun x => ?_
  by_cases hx : ((x.1 == target) && decide (x.2.2.corrupted = C₀)) = true
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
    simp only [hx.1, hx.2, decide_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    exact execState_adaptive_le_clampStatic Q S (Z κ z) κ x hx.2
  · simp only [Bool.eq_false_iff.mpr hx, Bool.false_eq_true, ↓reduceIte, zero_le]

private theorem apply_true_status_post_eq_noNewCorrupt
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR)
    (hno : A.NoNewCorrupt)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool)
    (target : Bool) :
    let C₀ := A.initial κ
    let Z_post : AdaptiveEnvironment n In Out AdvQ AdvR := fun κ' z' => do
      let b ← Z κ' z'
      let C ← queryStatus
      pure ((b == target) && decide (C = C₀))
    (adaptiveExec .adaptive P A Z_post κ z).eval true =
      (adaptiveExec .adaptive P A Z κ z).eval target := by
  intro C₀ Z_post
  rw [eval_adaptiveExec_status_post, eval_adaptiveExec_eq_execState_map,
    PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases hsup : execState .adaptive P A (Z κ z) κ x = 0
  · simp [hsup]
  · have hC : x.2.2.corrupted = C₀ :=
      corrupted_eq_of_mem_support_execState_noNewCorrupt P A hno (Z κ z) κ
        (by rw [PMF.mem_support_iff]; exact hsup)
    by_cases hb : x.1 = target
    · simp [hC, hb]
    · simp [hC, hb, Ne.symm hb]

private theorem eval_Z_status_eq_pure
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (C₀ : Finset (Fin n)) (κ : ℕ) (z : List Bool) :
    let Z_status : AdaptiveEnvironment n In Out AdvQ AdvR := fun _ _ => do
      let C ← queryStatus
      pure (decide (C = C₀))
    (adaptiveExec .adaptive P A Z_status κ z).eval = PMF.pure (decide (A.initial κ = C₀)) := by
  intro Z_status
  change closeEval (ProbOracleComp.sample (adaptiveExecMachine .adaptive P A κ).init >>=
    fun s => Prod.fst <$> (adaptiveExecMachine .adaptive P A κ).runFrom (Z_status κ z) s) =
    PMF.pure (decide (A.initial κ = C₀))
  erw [sample_adaptiveExecMachine_init]
  have hstep (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n) :
      Prod.fst <$> (adaptiveExecMachine .adaptive P A κ).runFrom (Z_status κ z) (sA, rs) =
        pure (decide (rs.corrupted = C₀)) := by
    erw [Machine.runFrom_bind, queryStatus, Machine.runFrom_query,
      adaptiveExecMachine_handle_inl_status]
    simp only [Machine.runFrom_pure]
    rfl
  rw [closeEval_bind]
  refine (congrArg (PMF.bind _) (funext fun s₀ => ?_)).trans (PMF.bind_const _ _)
  rw [closeEval_bind]
  have hconst : (fun sA : (A.machine κ).State =>
      closeEval (Prod.fst <$> (adaptiveExecMachine .adaptive P A κ).runFrom (Z_status κ z)
        (sA, {
          inner := P.applyInitialCorruptions κ (A.initial κ) s₀
          corrupted := A.initial κ
          trace := fun i => [P.view κ i (P.applyInitialCorruptions κ (A.initial κ) s₀)] }))) =
      fun _ => PMF.pure (decide (A.initial κ = C₀)) := by
    funext sA
    rw [hstep, closeEval_pure]
  erw [hconst, PMF.bind_const]

private theorem static_advantage_le_of_adaptive_clampStatic
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR)
    (S : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂ AdvQ AdvR)
    {pZ : Polynomial ℕ} {ν : ℕ → ℝ≥0}
    (hadv : ∀ (Z' : AdaptiveEnvironment n In Out AdvQ AdvR), Z'.PolyBounded (pZ + 1) →
      ∀ κ z, adaptiveAdvantage .adaptive P Q A.clampStatic S Z' κ z ≤ ν κ)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (hZ : Z.PolyBounded pZ)
    (κ : ℕ) (z : List Bool) :
    adaptiveAdvantage .static P Q A S.clampStatic Z κ z ≤ ν κ := by
  have heqP : adaptiveExec .static P A Z κ z = adaptiveExec .adaptive P A.clampStatic Z κ z :=
    adaptiveExec_static_eq_adaptive_clampStatic P A Z κ z
  have heqQ : adaptiveExec .static Q S.clampStatic Z κ z =
      adaptiveExec .adaptive Q S.clampStatic Z κ z :=
    adaptiveExec_static_eq_adaptive_of_noCorrupt Q S.clampStatic S.noNewCorrupt_clampStatic Z κ z
  rw [adaptiveAdvantage, heqP, heqQ]
  by_cases hinit : S.initial κ = A.initial κ
  · let Z_post (target : Bool) : AdaptiveEnvironment n In Out AdvQ AdvR := fun κ' z' => do
      let b ← Z κ' z'
      let C ← queryStatus
      pure ((b == target) && decide (C = A.initial κ))
    have hZ_post (target : Bool) : (Z_post target).PolyBounded (pZ + 1) := fun κ' z' => by
      refine (OracleComp.IsCostBounded.bind (hZ κ' z') fun _ =>
        OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query (cost := fun _ => 1) _)
          fun _ => OracleComp.IsCostBounded.pure _ 0).mono ?_
      simp only [Polynomial.eval_add, Polynomial.eval_one]
      omega
    have hadvT := hadv (Z_post true) (hZ_post true) κ z
    have hadvF := hadv (Z_post false) (hZ_post false) κ z
    have hPA_T : (adaptiveExec .adaptive P A.clampStatic (Z_post true) κ z).eval true =
        (adaptiveExec .adaptive P A.clampStatic Z κ z).eval true :=
      apply_true_status_post_eq_noNewCorrupt P A.clampStatic A.noNewCorrupt_clampStatic Z κ z true
    have hPA_F : (adaptiveExec .adaptive P A.clampStatic (Z_post false) κ z).eval true =
        (adaptiveExec .adaptive P A.clampStatic Z κ z).eval false :=
      apply_true_status_post_eq_noNewCorrupt P A.clampStatic A.noNewCorrupt_clampStatic Z κ z false
    have hQS_T : (adaptiveExec .adaptive Q S (Z_post true) κ z).eval true ≤
        (adaptiveExec .adaptive Q S.clampStatic Z κ z).eval true := by
      dsimp only [Z_post]
      rw [← hinit]
      exact apply_true_status_post_le Q S Z κ z true
    have hQS_F : (adaptiveExec .adaptive Q S (Z_post false) κ z).eval true ≤
        (adaptiveExec .adaptive Q S.clampStatic Z κ z).eval false := by
      dsimp only [Z_post]
      rw [← hinit]
      exact apply_true_status_post_le Q S Z κ z false
    have hqT_real : ((adaptiveExec .adaptive Q S (Z_post true) κ z).eval true).toReal ≤
        ((adaptiveExec .adaptive Q S.clampStatic Z κ z).eval true).toReal :=
      ENNReal.toReal_mono (PMF.apply_ne_top _ _) hQS_T
    have hqF_real : ((adaptiveExec .adaptive Q S (Z_post false) κ z).eval true).toReal ≤
        ((adaptiveExec .adaptive Q S.clampStatic Z κ z).eval false).toReal :=
      ENNReal.toReal_mono (PMF.apply_ne_top _ _) hQS_F
    have hsumP :
        ((adaptiveExec .adaptive P A.clampStatic Z κ z).eval true).toReal +
          ((adaptiveExec .adaptive P A.clampStatic Z κ z).eval false).toReal = 1 := by
      have h := Game.succProbability_add_failProbability
        (adaptiveExec .adaptive P A.clampStatic Z κ z).eval
      simpa [Game.succProbability, Game.failProbability] using congrArg NNReal.toReal h
    have hsumQ :
        ((adaptiveExec .adaptive Q S.clampStatic Z κ z).eval true).toReal +
          ((adaptiveExec .adaptive Q S.clampStatic Z κ z).eval false).toReal = 1 := by
      have h := Game.succProbability_add_failProbability
        (adaptiveExec .adaptive Q S.clampStatic Z κ z).eval
      simpa [Game.succProbability, Game.failProbability] using congrArg NNReal.toReal h
    have hadvT_real :
        |((adaptiveExec .adaptive P A.clampStatic Z κ z).eval true).toReal -
          ((adaptiveExec .adaptive Q S (Z_post true) κ z).eval true).toReal| ≤ (ν κ : ℝ) := by
      have h := NNReal.coe_le_coe.mpr hadvT
      rw [adaptiveAdvantage, Game.coe_advantage, Game.coe_succProbability,
        Game.coe_succProbability, hPA_T] at h
      exact h
    have hadvF_real :
        |((adaptiveExec .adaptive P A.clampStatic Z κ z).eval false).toReal -
          ((adaptiveExec .adaptive Q S (Z_post false) κ z).eval true).toReal| ≤ (ν κ : ℝ) := by
      have h := NNReal.coe_le_coe.mpr hadvF
      rw [adaptiveAdvantage, Game.coe_advantage, Game.coe_succProbability,
        Game.coe_succProbability, hPA_F] at h
      exact h
    have hmain_real :
        |((adaptiveExec .adaptive P A.clampStatic Z κ z).eval true).toReal -
          ((adaptiveExec .adaptive Q S.clampStatic Z κ z).eval true).toReal| ≤ (ν κ : ℝ) := by
      rw [abs_sub_le_iff] at hadvT_real hadvF_real ⊢
      constructor <;> linarith
    rw [← NNReal.coe_le_coe, Game.coe_advantage, Game.coe_succProbability,
      Game.coe_succProbability]
    exact hmain_real
  · let Z_status : AdaptiveEnvironment n In Out AdvQ AdvR := fun _ _ => do
      let C ← queryStatus
      pure (decide (C = A.initial κ))
    have hZ_status : Z_status.PolyBounded (pZ + 1) := fun κ' z' => by
      refine (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query (cost := fun _ => 1) _)
        fun _ => OracleComp.IsCostBounded.pure _ 0).mono ?_
      simp only [Polynomial.eval_add, Polynomial.eval_one]
      omega
    have hadv_st := hadv Z_status hZ_status κ z
    have hP_st : (adaptiveExec .adaptive P A.clampStatic Z_status κ z).eval = PMF.pure true := by
      simpa only [AdaptiveAdversary.clampStatic, decide_true] using
        eval_Z_status_eq_pure P A.clampStatic (A.initial κ) κ z
    have hQ_st : (adaptiveExec .adaptive Q S Z_status κ z).eval = PMF.pure false := by
      simpa only [hinit, decide_false] using
        eval_Z_status_eq_pure Q S (A.initial κ) κ z
    have h1 : (1 : ℝ≥0) ≤ ν κ := by
      simpa [adaptiveAdvantage, hP_st, hQ_st, Game.succProbability] using hadv_st
    exact (Game.advantage_le_one _ _).trans h1

/-- Adaptive emulation implies static emulation. Checking whether the simulator corrupted any
party outside `A.initial κ` via `.status` costs one environment query, shifting the error's
environment-budget argument from `pZ` to `pZ + 1`. -/
theorem AdaptiveEmulatesWithin.static_of_adaptive
    {P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    {g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : AdaptiveEmulatesWithin .adaptive P Q g ε) :
    AdaptiveEmulatesWithin .static P Q g (fun pA pZ => ε pA (pZ + 1)) := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hpS, hadv⟩ := h AdvQ AdvR A.clampStatic pA hA.clampStatic
  refine ⟨S.clampStatic, pS, hS.clampStatic, hpS, fun Z pZ hZ κ z =>
    static_advantage_le_of_adaptive_clampStatic P Q A S (hadv · (pZ + 1) ·) Z hZ κ z⟩

/-- Asymptotic adaptive emulation implies asymptotic static emulation. -/
theorem AdaptiveEmulates.static_of_adaptive
    {P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    (h : AdaptiveEmulates .adaptive P Q) : AdaptiveEmulates .static P Q := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hper_Z⟩ := h AdvQ AdvR A.clampStatic pA hA.clampStatic
  refine ⟨S.clampStatic, pS, hS.clampStatic, fun pZ => ?_⟩
  obtain ⟨ν, hν, hadv⟩ := hper_Z (pZ + 1)
  exact ⟨ν, hν, fun Z hZ κ z =>
    static_advantage_le_of_adaptive_clampStatic P Q A S hadv Z hZ κ z⟩

end AdaptiveToStatic

end Cslib.Crypto.Protocols.UC
