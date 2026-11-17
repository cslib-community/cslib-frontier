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
# Adaptive corruptions (snapshot model) in the UC execution

Extends `CslibFrontier.Crypto.Protocols.UC.Execution` with `CorruptionMode` (`.static` vs
`.adaptive`) and a snapshot-based corruption exposure interface (`PartyMemory`: `.erasing` vs
`.nonErasing`), inspired by Section 7.1 (pp. 28:69–70), Section 7.1.1 (p. 28:71), and
Section 7.2 (pp. 28:73–74) of [Canetti2020] (J. ACM pagination; ePrint 2000/067 of Feb 11, 2020,
p. 74).

* **Snapshot corruption model (not Canetti §7.1.1 write-once storage):** `AdaptiveProtocol.view`
  is an arbitrary caller-supplied projection (for instance, `View := Unit` can hide coins still
  stored in the inner machine), and `AdaptiveProtocol.recordSnapshot` appends `P.view κ j s'`
  for every party `j` after each inner activation (`.party` or `.net`). Thus `.nonErasing`
  histories omit intra-activation discarded coins while exposing global inner-activation counts.
  `PartyMemory` controls only whether `CorruptionReport.history` returns `none` or that snapshot
  list; establishing [Canetti2020] §7.1.1's write-once / non-erasing storage restriction, mandatory
  coin exposure, and per-party activation granularity remains open.
* **Status query and adversary class:** `AdaptivePartyQ.status` models the identity-revealing
  (`f = id`) "Report corruption status" query on the corruption aggregation ITI (p. 28:70).
  `AdaptiveEmulatesWithin` / `AdaptiveEmulates` are call-bounded statistical notions.

## Scope

[Canetti2020] §7.1.1 write-once / non-erasing storage restrictions and mandatory coin-exposure /
per-party activation-granularity guarantees, universal composition under adaptive corruption,
multiple sessions, proactive/passive modes, subroutine corruption paths, PPT bounds, and
[CanettiFischlin2001] Theorems 8 and 11 remain open and out of scope. Existing static definitions
in `Execution`, `Emulation`, `DummyAdversary`, and `Composition` are unchanged.

## Main definitions

* `Cslib.Crypto.Protocols.UC.CorruptionMode`, `PartyMemory`, `AdaptiveProtocol`,
  `CorruptionReport`, `AdaptiveRouterState`: corruption modes, memory, protocols, and router state.
* `Cslib.Crypto.Protocols.UC.AdaptivePartyQ`, `adaptivePartySpec`, `AdaptiveNetQ`,
  `AdaptiveNetR`, `adaptiveProtocolSpec`, `adaptiveExecSpec`: adaptive execution ports.
* `Cslib.Crypto.Protocols.UC.adaptiveRouter`, `AdaptiveAdversary`, `AdaptiveEnvironment`,
  `Environment.toAdaptive`, `IdealFunctionality.toAdaptive`: participants and adaptive routing.
* `Cslib.Crypto.Protocols.UC.liftAdaptiveNet`, `liftAdaptiveAdversary`, `adaptiveExecMachine`,
  `adaptiveExec`, `adaptiveAdvantage`, `AdaptiveEmulatesWithin`, `AdaptiveEmulates`: experiment
  and call-bounded emulation.
* `Cslib.Crypto.Protocols.UC.AdaptiveProtocol.toStatic`, `AdaptiveAdversary.ofStatic`: static
  special case embeddings.

## Main results

* `Cslib.Crypto.Protocols.UC.adaptiveAdvantage_self`, `adaptiveAdvantage_comm`,
  `adaptiveAdvantage_triangle`: pseudometric laws for `adaptiveAdvantage`.
* `Cslib.Crypto.Protocols.UC.Environment.PolyBounded.toAdaptive`,
  `AdaptiveEmulatesWithin.{mono, refl, trans, emulates}`, `AdaptiveEmulates.{refl, trans}`.
* `Cslib.Crypto.Protocols.UC.IdealFunctionality.toStatic_toAdaptive`: functionality round-trip.
* `Cslib.Crypto.Protocols.UC.adaptiveExec_static_eq_adaptive_of_noCorrupt`,
  `adaptiveExec_static_ofStatic`, `adaptiveExec_adaptive_ofStatic`: static special case.

## References

* [Canetti2020] J. ACM 67(5), Art. 28, 2020 (ePrint 2000/067 of Feb 11, 2020): Section 7.1
  (pp. 28:69–70; ePrint p. 74), Section 7.1.1 (p. 28:71), and Section 7.2 (pp. 28:73–74).
* [CanettiFischlin2001] CRYPTO 2001 (ePrint 2001/055): p. 5, p. 13, Theorems 8 and 11
  (unformalized).
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

/-- Router trace-exposure flag in the snapshot corruption model: `.erasing` exposes only the
post-corruption view snapshot (`CorruptionReport.history = none`), while `.nonErasing` exposes the
recorded list of per-activation `P.view` snapshots (`some (s.trace i)`). This flag governs only
`CorruptionReport.history` in `adaptiveRouter`; it does not enforce [Canetti2020] §7.1.1's
write-once storage restriction, coin exposure, or per-party activation granularity (which stay
open). -/
inductive PartyMemory : Type
  | erasing
  | nonErasing
  deriving DecidableEq, Repr

/-- An `n`-party protocol equipped for the snapshot adaptive-corruption model: a closed machine per
security parameter `κ`, an arbitrary caller-supplied per-party view projection `view` (which need
not expose all stored coins or private state, e.g. `View := Unit`), a state transition `onCorrupt`
applied when party `i` is corrupted, and a trace-exposure flag `memory`. -/
structure AdaptiveProtocol (n : ℕ) (In Out NetQ NetR View : Type) : Type 1 where
  /-- The protocol machine at security parameter `κ`. -/
  machine : ℕ → Machine OracleSpec.empty (protocolSpec n In Out NetQ NetR)
  /-- Arbitrary caller-supplied projection from inner protocol state to party `i`'s reported view
  (may hide stored coins or state, e.g. with `View := Unit`). -/
  view : (κ : ℕ) → Fin n → (machine κ).State → View
  /-- The protocol's own reaction when party `i` is corrupted (replacing `π κ C`'s dependence on
  `C` in static `Protocol`). -/
  onCorrupt : (κ : ℕ) → Fin n → (machine κ).State → (machine κ).State
  /-- Router trace-exposure flag selecting whether past view snapshots are omitted or included in
  `CorruptionReport.history`. -/
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
([Canetti2020], Section 7.1, p. 28:70, the identity-revealing `f = id` case of standard
`f`-revealing corruption on the corruption aggregation ITI). -/
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

/-- Update the router state after an inner protocol activation by appending every party's `P.view`
snapshot (so `.nonErasing` histories reflect global inner-activation counts). -/
@[expose] def AdaptiveProtocol.recordSnapshot
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (s' : (P.machine κ).State)
    (corrupted : Finset (Fin n)) (trace : Fin n → List View) :
    AdaptiveRouterState (P.machine κ).State View n :=
  { inner := s'
    corrupted := corrupted
    trace := fun j => trace j ++ [P.view κ j s'] }

/-- The snapshot-model adaptive corruption router wrapping `P.machine κ` with initial corruptions
`C₀`. Initial corruptions apply `P.onCorrupt` at `init`. Environment party calls addressed to
corrupted parties are dropped (`none`, matching static `corruptRouter`); adversary party calls are
allowed only for corrupted parties; `.status` returns `s.corrupted`; `.corrupt i` is ignored for
`i ∉ s.corrupted` in `.static` mode and in `.adaptive` mode applies `P.onCorrupt`, inserts `i`,
and computes `P.corruptionReport` *after* `P.onCorrupt` without recording an extra snapshot of the
`onCorrupt` transition itself. -/
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

/-- Embed an `IdealFunctionality` as an `AdaptiveProtocol` with `memory := .erasing`,
view-leakage map `reveal`, and optional corruption-notification state hook `onCorrupt`
([Canetti2020], Section 7.2, pp. 28:73–74, standard PID-wise corruption). Marking ideal
functionalities `.erasing` models that `F`'s internal state belongs to no party and only
`reveal` is exposed on corruption; rule (1)'s disclosure of party `p`'s past inputs and
subroutine outputs holds when `F`'s state records them and `reveal` exposes them. When `onCorrupt`
is supplied, `F` learns of both initial corruptions (via `applyInitialCorruptions`) and mid-run
corruptions (via `adaptiveRouter`), so `(F.toAdaptive reveal onCorrupt).toStatic = F.toProtocol`
whenever `F.init κ C` factors as `applyInitialCorruptions κ C <$> F.init κ ∅` (e.g., `C`-independent
or deterministically tracked initial corruptions; arbitrary `C`-dependent probabilistic sampling
inside `F.init κ C` cannot be reconstructed after `init` and remains outside `AdaptiveProtocol`). -/
@[expose] def IdealFunctionality.toAdaptive {BackQ BackR : Type}
    (F : IdealFunctionality n In Out BackQ BackR)
    (reveal : (κ : ℕ) → F.State → Fin n → View)
    (onCorrupt : (κ : ℕ) → Fin n → F.State → F.State := fun _ _ s => s) :
    AdaptiveProtocol n In Out BackQ BackR View where
  machine κ := {
    State := F.State
    init := F.init κ ∅
    handle
      | .inl (i, x) => fun s => ProbOracleComp.sample ((F.onInput i x).run s)
      | .inr q => fun s => ProbOracleComp.sample ((F.onBackdoor q).run s) }
  view κ i s := reveal κ s i
  onCorrupt := onCorrupt
  memory := .erasing

end Router

/-! ### Execution and advantage -/

section Execution

variable {n : ℕ} {In Out Q R NetQ NetR View AdvQ AdvR : Type}
  {NetQ₁ NetR₁ View₁ NetQ₂ NetR₂ View₂ NetQ₃ NetR₃ View₃ : Type}

/-- Mirror of `UC.liftNet` for the adaptive left port `adaptivePartySpec n In Out` (which extends
`partySpec n In Out` with `.status`, so `UC.liftNet` does not apply directly). -/
abbrev liftAdaptiveNet {α : Type} (program : ProbOracleComp (netSpec Q R) α) :
    ProbOracleComp (adaptivePartySpec n In Out ⊕ₒ netSpec Q R) α :=
  Machine.liftRightProgram (adaptivePartySpec n In Out) program

/-- Mirror of `UC.liftAdversary` for `adaptivePartySpec n In Out`. -/
abbrev liftAdaptiveAdversary (A : Machine (netSpec Q R) (netSpec AdvQ AdvR)) :
    Machine (adaptivePartySpec n In Out ⊕ₒ netSpec Q R) (adaptiveExecSpec n In Out AdvQ AdvR) :=
  Machine.liftRight (adaptivePartySpec n In Out) A

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
    P.PolyBounded q := fun κ => (h κ).mono (hpq κ)

theorem AdaptiveAdversary.PolyBounded.mono
    {A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR} {p q : Polynomial ℕ}
    (h : A.PolyBounded p) (hpq : ∀ κ, p.eval κ ≤ q.eval κ) : A.PolyBounded q :=
  fun κ => (h κ).mono (hpq κ)

theorem AdaptiveEnvironment.PolyBounded.mono {Z : AdaptiveEnvironment n In Out AdvQ AdvR}
    {p q : Polynomial ℕ} (h : Z.PolyBounded p) (hpq : ∀ κ, p.eval κ ≤ q.eval κ) :
    Z.PolyBounded q := fun κ z => (h κ z).mono (hpq κ)

/-- Lifting static queries into `adaptiveExecSpec` preserves query budgets. -/
theorem isQueryBounded_liftPartyQuery {α : Type}
    {program : ProbOracleComp (execSpec n In Out AdvQ AdvR) α} {m : ℕ}
    (h : program.IsQueryBounded m) : (liftPartyQuery program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  rcases q with k | (⟨i, x⟩ | a) <;> exact OracleComp.IsCostBounded.query _

/-- Embedding a static environment into `AdaptiveEnvironment` preserves its call budget. -/
theorem Environment.PolyBounded.toAdaptive {Z : Environment n In Out AdvQ AdvR}
    {p : Polynomial ℕ} (h : Z.PolyBounded p) : Z.toAdaptive.PolyBounded p :=
  fun κ z => isQueryBounded_liftPartyQuery (h κ z)

/-- Concrete adaptive UC emulation under `mode` in the snapshot corruption model (statistical,
call-bounded notion inspired by [Canetti2020], Section 7.1.1, p. 28:71, not a theorem of the
paper; §7.1.1's write-once storage restriction, coin exposure, and per-party activation
granularity remain open). Every adversary `A` with per-activation call budget `pA` has a simulator
`S` with per-activation call budget `pS` bounded by `g` at `κ + pA.eval κ`, such that every
environment `Z` with call budget `pZ` distinguishes `(P, A)` from `(Q, S)` with advantage at most
`ε pA pZ κ`. -/
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

/-- Asymptotic adaptive UC emulation under `mode` with negligible error in the snapshot corruption
model (statistical, call-bounded notion inspired by [Canetti2020], Section 7.1.1, p. 28:71, not
a theorem of the paper; §7.1.1's write-once storage, coin exposure, and activation granularity
remain open). -/
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
    AdaptiveEmulatesWithin mode P Q g ε' := fun AdvQ AdvR A pA hA =>
  let ⟨S, pS, hS, hSg, hadv⟩ := h AdvQ AdvR A pA hA
  ⟨S, pS, hS, hSg, fun Z pZ hZ κ z => (hadv Z pZ hZ κ z).trans (hε pA pZ κ)⟩

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
  exact (adaptiveAdvantage_triangle mode P₁ P₂ P₃ A S₂ S₃ Z κ z).trans
    (add_le_add (hadv₁₂ Z pZ hZ κ z)
      ((hadv₂₃ Z pZ hZ κ z).trans (hmono _ _ pZ κ hS₂g.le_eval_comp)))

/-- Concrete adaptive emulation whose errors are negligible for all budgets is asymptotic adaptive
emulation. -/
theorem emulates {mode : CorruptionMode} {P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂} {g : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : AdaptiveEmulatesWithin mode P Q g ε) (hε : ∀ pA pZ, Negligible (ε pA pZ)) :
    AdaptiveEmulates mode P Q := fun AdvQ AdvR A pA hA =>
  let ⟨S, pS, hS, _, hadv⟩ := h AdvQ AdvR A pA hA
  ⟨S, pS, hS, fun pZ => ⟨ε pA pZ, hε pA pZ, fun Z hZ κ z => hadv Z pZ hZ κ z⟩⟩

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
  obtain ⟨ν₁₂, hν₁₂, h₁⟩ := hadv₁₂ pZ; obtain ⟨ν₂₃, hν₂₃, h₂⟩ := hadv₂₃ pZ
  exact ⟨ν₁₂ + ν₂₃, hν₁₂.add hν₂₃, fun Z hZ κ z =>
    (adaptiveAdvantage_triangle mode P₁ P₂ P₃ A S₂ S₃ Z κ z).trans
      (add_le_add (h₁ Z hZ κ z) (h₂ Z hZ κ z))⟩

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

/-- When `F.init κ C` factors as `applyInitialCorruptions κ C <$> F.init κ ∅`, converting
`F.toAdaptive reveal onCorrupt` back to a static `Protocol` recovers `F.toProtocol` identically. -/
theorem IdealFunctionality.toStatic_toAdaptive {BackQ BackR : Type}
    (F : IdealFunctionality n In Out BackQ BackR)
    (reveal : (κ : ℕ) → F.State → Fin n → View)
    (onCorrupt : (κ : ℕ) → Fin n → F.State → F.State)
    (hinit : ∀ κ C,
      (F.toAdaptive reveal onCorrupt).applyInitialCorruptions κ C <$> F.init κ ∅ = F.init κ C) :
    (F.toAdaptive reveal onCorrupt).toStatic = F.toProtocol := by
  funext κ C
  simp only [AdaptiveProtocol.toStatic, IdealFunctionality.toAdaptive,
    IdealFunctionality.toProtocol]
  congr 1
  exact hinit κ C

/-- Specialization of `IdealFunctionality.toStatic_toAdaptive` for `IdealFunctionality`
instances whose initial state ignores `C` and with default trivial `onCorrupt`. -/
theorem IdealFunctionality.toStatic_toAdaptive_of_initIndep {BackQ BackR : Type}
    (F : IdealFunctionality n In Out BackQ BackR)
    (reveal : (κ : ℕ) → F.State → Fin n → View)
    (hinit : ∀ κ C, F.init κ C = F.init κ ∅) :
    (F.toAdaptive reveal).toStatic = F.toProtocol := by
  refine F.toStatic_toAdaptive reveal (fun _ _ s => s) fun κ C => ?_
  have hid : (F.toAdaptive reveal).applyInitialCorruptions κ C = id := by
    funext s
    simp only [AdaptiveProtocol.applyInitialCorruptions, IdealFunctionality.toAdaptive, ite_self]
    clear hinit
    induction List.finRange n generalizing s with
    | nil => rfl
    | cons _ _ ih => exact ih s
  rw [hid]; exact (id_map _).trans (hinit κ C).symm

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
    (sumHandler (fun k => OracleComp.query (Sum.inl k)) fun q => match q with
      | .inl (i, x) => AdaptiveNetR.toRoutedNetR <$> ProbOracleComp.query (.party i x)
      | .inr nq => AdaptiveNetR.toRoutedNetR <$> ProbOracleComp.query (.net nq))
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
  | pure a => exact .pure a
  | query_bind q _ ih =>
    simp only [PFunctor.FreeM.bind_eq_bind]
    rcases q with k | (⟨i, x⟩ | nq) <;>
      rw [liftStaticNetProgram, OracleComp.interpret_bind, OracleComp.interpret_query] <;>
      refine .bind ?_ ih
    · exact .query trivial
    · simp only [sumHandler, OracleComp.queriesSatisfy_map_iff]; exact .query trivial
    · simp only [sumHandler, OracleComp.queriesSatisfy_map_iff]; exact .query trivial

/-- A static adversary lifted via `AdaptiveAdversary.ofStatic` never queries `.corrupt`. -/
theorem AdaptiveAdversary.noNewCorrupt_ofStatic
    (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR) (C : ℕ → Finset (Fin n)) :
    (AdaptiveAdversary.ofStatic A C :
      AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR).NoNewCorrupt :=
  fun κ q s => noNewCorrupt_liftStaticNetProgram (C κ) (((A κ (C κ)).handle q).run s)

/-- Sample the initial state of `adaptiveExecMachine` as independent samples of protocol and
adversary initial states. -/
theorem sample_adaptiveExecMachine_init (mode : CorruptionMode)
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
  exact bind_congr fun _ => by
    erw [ProbOracleComp.sample_pure, pure_bind, bind_assoc]
    exact bind_congr fun _ => pure_bind _ _

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
  exact bind_congr fun _ => by erw [bind_assoc]; exact bind_congr fun _ => pure_bind _ _

/-- Left-port party query step of `adaptiveExecMachine`. -/
theorem adaptiveExecMachine_handle_inl_party (mode : CorruptionMode)
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
  erw [Machine.runFrom_map, Machine.runFrom_query]; dsimp only [adaptiveRouter, StateT.run]
  by_cases hi : i ∈ rs.corrupted
  · simp [hi]; rfl
  · simp only [hi, ↓reduceIte]; erw [Functor.map_map, map_bind]; exact bind_congr fun _ => rfl

/-- Left-port `.status` query step of `adaptiveExecMachine`. -/
theorem adaptiveExecMachine_handle_inl_status (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n) :
    ((adaptiveExecMachine mode P A κ).handle (.inl .status)).run (sA, rs) =
      pure (rs.corrupted, (sA, rs)) := by
  change Equiv.prodAssoc _ _ _ <$> (adaptiveRouter mode P κ (A.initial κ)).runFrom
      ((fun v => (v, sA)) <$> ProbOracleComp.query (Sum.inl .status)) rs = _
  erw [Machine.runFrom_map, Machine.runFrom_query]; rfl

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
    | .corrupt i => i ∈ C₀ | _ => True
  have hno' : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) netProg :=
    hno.mono fun q hq => by
      rcases q with k | (⟨i, x⟩ | i | nq)
      · trivial
      · trivial
      · exact hq
      · trivial
  refine Machine.runFrom_interpret_intertwine
    (adaptiveRouter .static P κ C₀) (adaptiveRouter .adaptive P κ C₀)
    (fun q => ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View) (.inr q))
    (fun q => ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View) (.inr q))
    Inv (fun rs₁ rs₂ => rs₁ = rs₂ ∧ rs₁.corrupted = C₀)
    netProg hno' rs rs ⟨rfl, hrs⟩ f g (fun a rs₁ _ hR => hR.1 ▸ hfg a rs₁ hR.2)
    fun q rs₁ _ k₁ k₂ hq ⟨hEq, hrs₁⟩ hcont => ?_
  cases hEq; erw [Machine.runFrom_query, Machine.runFrom_query]
  dsimp only [adaptiveRouter, StateT.run]
  cases q with
  | party i x =>
    by_cases hi : i ∈ rs₁.corrupted
    · simp only [hi, ↓reduceIte]; erw [bind_assoc, bind_assoc]
      exact bind_congr fun ⟨out, _⟩ => by erw [pure_bind]; exact hcont (.party out) _ _ ⟨rfl, hrs₁⟩
    · simp only [hi, ↓reduceIte]; erw [pure_bind]; exact hcont (.party none) _ _ ⟨rfl, hrs₁⟩
  | corrupt i =>
    have hi : i ∈ rs₁.corrupted := hrs₁ ▸ hq
    simp only [hi, ↓reduceIte]
    exact hcont (.corrupt (some (P.corruptionReport κ i rs₁))) _ _ ⟨rfl, hrs₁⟩
  | net nq =>
    erw [bind_assoc, bind_assoc]
    exact bind_congr fun ⟨r, _⟩ => by erw [pure_bind]; exact hcont (.net r) _ _ ⟨rfl, hrs₁⟩

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
  refine Machine.runFrom_intertwine
    (adaptiveExecMachine .static P A κ) (adaptiveExecMachine .adaptive P A κ)
    (fun _ => True) (fun x₁ x₂ => x₁ = x₂ ∧ x₁.2.corrupted = A.initial κ)
    program (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    (sA, rs) (sA, rs) ⟨rfl, hrs⟩ pure pure
    (fun _ _ _ hR => hR.1 ▸ rfl)
    fun q ⟨sA₁, rs₁⟩ _ k₁ k₂ _ ⟨hEq, hrs₁⟩ hcont => ?_
  cases hEq; rcases q with (⟨i, x⟩ | _) | a
  · erw [adaptiveExecMachine_handle_inl_party]
    by_cases hi : i ∈ rs₁.corrupted
    · simp only [hi, ↓reduceIte]; erw [pure_bind]; exact hcont none _ _ ⟨rfl, hrs₁⟩
    · simp only [hi, ↓reduceIte]; erw [bind_assoc, bind_assoc]
      exact bind_congr fun ⟨out, _⟩ => by erw [pure_bind]; exact hcont out _ _ ⟨rfl, hrs₁⟩
  · erw [adaptiveExecMachine_handle_inl_status, pure_bind]
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
  dsimp only [liftAdaptiveNet, liftNet]
  rw [Machine.liftRightProgram, liftStaticNetProgram,
    OracleComp.interpret_interpret, OracleComp.interpret_sumHandler]
  let qLift : (q : RoutedNetQ n In NetQ) →
      ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR View)
        (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR) q) := fun q => match q with
    | .inl (i, x) => AdaptiveNetR.toRoutedNetR <$>
        ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View)
          (.inr (.party i x))
    | .inr nq => AdaptiveNetR.toRoutedNetR <$>
        ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View)
          (.inr (.net nq))
  have hleft :
      (fun k => OracleComp.interpret
        (sumHandler (fun k => OracleComp.query
          (spec := probOracleSpec (adaptiveProtocolSpec n In Out NetQ NetR View)) (.inl k))
          fun q => ProbOracleComp.query (.inr q))
        (OracleComp.query
          (spec := probOracleSpec (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)))
          (.inl k))) =
      fun k => OracleComp.query
        (spec := probOracleSpec (adaptiveProtocolSpec n In Out NetQ NetR View)) (.inl k) := by
    funext k; rfl
  have hcomp :
      (fun q : RoutedNetQ n In NetQ => OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (.inl k)) fun q => ProbOracleComp.query (.inr q))
        (match q with
          | .inl (i, x) => AdaptiveNetR.toRoutedNetR <$> ProbOracleComp.query (.party i x)
          | .inr nq => AdaptiveNetR.toRoutedNetR <$> ProbOracleComp.query (.net nq))) = qLift :=
    funext fun q => by rcases q with ⟨i, x⟩ | nq <;>
      exact (OracleComp.interpret_map _ _ _).trans (congrArg _ (OracleComp.interpret_query _ _))
  rw [hleft, hcomp]
  refine Machine.runFrom_interpret_intertwine (adaptiveRouter .static P κ C₀)
    (corruptRouter C₀ (P.toStatic κ C₀)) qLift
    (fun (q : RoutedNetQ n In NetQ) => ProbOracleComp.query
      (spec := protocolSpec n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) (.inr q))
    (fun _ => True) (fun rs' sP => rs'.corrupted = C₀ ∧ rs'.inner = sP)
    netProg (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    rs rs.inner ⟨hrs, rfl⟩ f g
    (fun a rs' sP hR => hR.2 ▸ hfg a rs' hR.1)
    fun q rs' sP k₁ k₂ _ ⟨hrs', hsP⟩ hcont => by
      rcases hsP with rfl; erw [Machine.runFrom_query]
      rcases q with ⟨i, x⟩ | nq
      · erw [Machine.runFrom_map, Machine.runFrom_query, bind_map_left]
        dsimp only [adaptiveRouter, corruptRouter, AdaptiveProtocol.toStatic]
        conv_lhs => dsimp only [StateT.run]
        by_cases hi : i ∈ C₀
        · have hi' : i ∈ rs'.corrupted := hrs' ▸ hi
          simp only [hi, hi', ↓reduceIte]
          erw [StateT.run_map, bind_assoc, bind_map_left]
          exact bind_congr fun p => by erw [pure_bind]; exact hcont (.inl p.1) _ _ ⟨hrs', rfl⟩
        · have hi' : i ∉ rs'.corrupted := hrs' ▸ hi
          simp only [hi, hi', ↓reduceIte]
          erw [StateT.run_pure, pure_bind, pure_bind]; exact hcont (.inl none) _ _ ⟨hrs', rfl⟩
      · erw [Machine.runFrom_map, Machine.runFrom_query, bind_map_left]
        dsimp only [adaptiveRouter, corruptRouter, AdaptiveProtocol.toStatic]
        conv_lhs => dsimp only [StateT.run]
        erw [StateT.run_map, bind_assoc, bind_map_left]
        exact bind_congr fun p => by erw [pure_bind]; exact hcont (.inr p.1) _ _ ⟨hrs', rfl⟩

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
  have hid :
      (sumHandler
        (fun k => OracleComp.query (spec := probOracleSpec (execSpec n In Out AdvQ AdvR)) (.inl k))
        (fun q => ProbOracleComp.query (spec := execSpec n In Out AdvQ AdvR) q)) =
      OracleComp.query :=
    funext fun q => by cases q <;> rfl
  conv_rhs => rw [← OracleComp.interpret_query_eq_self program, ← hid]
  refine Machine.runFrom_interpret_intertwine
    (adaptiveExecMachine .static P (AdaptiveAdversary.ofStatic A C) κ)
    (execMachine P.toStatic A κ (C κ))
    (fun q => match q with
      | .inl (i, x) => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR)
          (.inl (.party i x))
      | .inr a => ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR) (.inr a))
    (fun q => ProbOracleComp.query (spec := execSpec n In Out AdvQ AdvR) q)
    (fun _ => True) (fun x₁ x₂ => x₁.1 = x₂.1 ∧ x₁.2.corrupted = C κ ∧ x₁.2.inner = x₂.2)
    program (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    (sA, rs) (sA, rs.inner) ⟨rfl, hrs, rfl⟩ f g
    (fun a ⟨sA₁, _⟩ ⟨_, _⟩ ⟨hsA, hrs₁, hsP⟩ => by
      subst hsA; subst hsP; exact hfg a sA₁ _ hrs₁)
    fun q ⟨sA₁, rs₁⟩ ⟨_, _⟩ k₁ k₂ _ ⟨hsA, hrs₁, hsP⟩ hcont => by
      subst hsA; subst hsP; rcases q with ⟨i, x⟩ | a
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
          simp only [hi, hi', ↓reduceIte]; erw [bind_assoc]
          exact bind_congr fun p => by
            erw [Machine.runFrom_pure, pure_bind, pure_bind]; exact hcont p.1 _ _ ⟨rfl, hrs₁, rfl⟩
      · erw [Machine.runFrom_query, Machine.runFrom_query]
        change (fun (p : (AdvR × (A κ (C κ)).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
            (adaptiveRouter .static P κ (C κ)).runFrom
              (liftAdaptiveNet (liftStaticNetProgram (((A κ (C κ)).handle a).run sA₁))) rs₁ >>= k₁ =
          (fun (p : (AdvR × (A κ (C κ)).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
            (corruptRouter (C κ) (P.toStatic κ (C κ))).runFrom
              (liftNet (((A κ (C κ)).handle a).run sA₁)) rs₁.inner >>= k₂
        erw [bind_map_left, bind_map_left]
        exact runFrom_adaptiveRouter_liftStaticNetProgram P κ (C κ)
          (((A κ (C κ)).handle a).run sA₁) rs₁ hrs₁ _ _ fun res rs' hrs' =>
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

end Cslib.Crypto.Protocols.UC
