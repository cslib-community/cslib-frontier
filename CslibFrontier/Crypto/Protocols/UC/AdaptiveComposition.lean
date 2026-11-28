/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.AdaptiveDummyAdversary
public import CslibFrontier.Crypto.Protocols.UC.Composition

/-!
# Single-session adaptive UC composition (snapshot corruption model)

This module proves single-subroutine composition for this library's **snapshot, call-bounded
adaptive-corruption port model** (`CslibFrontier.Crypto.Protocols.UC.Adaptive` and
`CslibFrontier.Crypto.Protocols.UC.AdaptiveDummyAdversary`), mirroring static single-session
composition in `CslibFrontier.Crypto.Protocols.UC.Composition` (#6043). These results are **not**
[Canetti2020] Theorem 3 (Section 2.3), Theorem 22 (Section 6.1), or Section 7.1.1's write-once /
non-erasing storage and coin-exposure model: participants are bounded only by oracle call counts
per activation (unbounded local computation, not PPT ITMs), sessions are fixed to a single
`n`-party subroutine instance, and `.nonErasing` histories record caller-supplied `view` snapshots
rather than enforcing write-once storage or per-party activation granularity.

An `AdaptiveHybridProtocol ρ` is an `n`-party adaptive calling protocol whose machines invoke a
subroutine's `partySpec n SubIn SubOut` port. `composeAdaptive ρ σ` composes `ρ` over an inner
`AdaptiveProtocol σ`, exposing `ρ`'s network port beside `σ`'s routed network port
(`NetQ ⊕ RoutedNetQ n SubIn NQ`). A single `.corrupt i` query corrupts party `i` consistently
across both `ρ` and `σ`, returning `AdaptiveHybridView Viewρ Viewσ` pairing `ρ`'s and `σ`'s
`CorruptionReport`s without leaking uncorrupted party state or erased histories.

Because `adaptiveRouter` in `UC.Adaptive` runs `P.applyInitialCorruptions` before recording the
initial snapshot `trace[0]`, composition preserves initial snapshots under
`ViewStableOnCorrupt` (vacuously true for `.erasing` protocols, and true whenever `onCorrupt` does
not alter `view` for `.nonErasing` protocols).

## Main definitions

* `Cslib.Crypto.Protocols.UC.AdaptiveHybridProtocol`,
  `Cslib.Crypto.Protocols.UC.AdaptiveHybridProtocol.PolyBounded`,
  `Cslib.Crypto.Protocols.UC.AdaptiveHybridProtocol.ViewStableOnCorrupt`,
  `Cslib.Crypto.Protocols.UC.AdaptiveProtocol.ViewStableOnCorrupt`: adaptive hybrid protocols and
  snapshot-stability predicates.
* `Cslib.Crypto.Protocols.UC.AdaptiveHybridView`,
  `Cslib.Crypto.Protocols.UC.AdaptiveComposeState`: combined corruption report and internal
  composed router state.
* `Cslib.Crypto.Protocols.UC.composeAdaptive`: single-session adaptive subroutine replacement.
* `Cslib.Crypto.Protocols.UC.absorbAdaptiveHybrid`: environment running `ρ` internally against the
  subroutine.
* `Cslib.Crypto.Protocols.UC.adaptiveHybridSim`: composed adaptive simulator wrapping a subroutine
  dummy simulator `S_D`.
* `Cslib.Crypto.Protocols.UC.AdaptiveAdversary.CorruptSync`: synchronization predicate under which
  `eval_adaptiveExec_compose_sim` holds as an exact distributional equality.

## Main results

* `Cslib.Crypto.Protocols.UC.composeAdaptive_polyBounded`,
  `Cslib.Crypto.Protocols.UC.absorbAdaptiveHybrid_polyBounded`,
  `Cslib.Crypto.Protocols.UC.adaptiveHybridSim_polyBounded`: call-budget preservation.
* `Cslib.Crypto.Protocols.UC.adaptiveExec_compose_dummy`,
  `Cslib.Crypto.Protocols.UC.eval_adaptiveExec_compose_sim`,
  `Cslib.Crypto.Protocols.UC.adaptiveAdvantage_compose`: execution regrouping identities.
* `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesDummyWithin.compose`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesWithin.compose`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulates.compose`: quantitative and asymptotic adaptive
  composition in the snapshot, call-bounded port model (#6043).

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], J. ACM 67(5), Article 28, 2020
  (ePrint 2000/067 of Feb 11, 2020): Section 2.3 (Theorem 3) and Section 7.1.1 (p. 28:71), which
  inspire the snapshot adaptive-corruption model adapted here.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open Machine (closeEval closeEval_pure closeEval_bind closeEval_map closeEval_sample
  mem_support_closeEval_pure mem_support_closeEval_bind mem_support_closeEval_map
  closeEval_bind_le mem_support_closeEval_runFrom_invariant)
open scoped ENNReal NNReal

variable {n : ℕ} {In Out NetQ NetR SubIn SubOut Viewρ : Type}
  {NQ NR NQ₁ NR₁ View₁ NQ₂ NR₂ View₂ AdvQ AdvR α β : Type}

/-! ### Adaptive hybrid protocols, views, and composed state -/

/-- An `n`-party calling protocol in the snapshot adaptive-corruption model, invoking a subroutine's
`partySpec n SubIn SubOut` port. -/
structure AdaptiveHybridProtocol
    (n : ℕ) (In Out NetQ NetR SubIn SubOut View : Type) : Type 1 where
  /-- The hybrid protocol machine at security parameter `κ`. -/
  machine : ℕ → Machine (partySpec n SubIn SubOut) (protocolSpec n In Out NetQ NetR)
  /-- Arbitrary caller-supplied projection from inner hybrid state to party `i`'s reported view. -/
  view : (κ : ℕ) → Fin n → (machine κ).State → View
  /-- The hybrid protocol's reaction when party `i` is corrupted. -/
  onCorrupt : (κ : ℕ) → Fin n → (machine κ).State → (machine κ).State
  /-- Router trace-exposure flag selecting whether past view snapshots are omitted or included in
  `AdaptiveHybridView.outer`. -/
  memory : PartyMemory

/-- Combined corruption report returned when corrupting party `i` in `composeAdaptive ρ σ`: pairs
the outer protocol's `CorruptionReport` with the inner subroutine's `CorruptionReport`, each
respecting its own `PartyMemory`. -/
structure AdaptiveHybridView (Viewρ Viewσ : Type) : Type where
  /-- The outer hybrid protocol's corruption report at party `i`. -/
  outer : CorruptionReport Viewρ
  /-- The inner subroutine protocol's corruption report at party `i`. -/
  sub : CorruptionReport Viewσ
  deriving DecidableEq, Repr

/-- Internal state of `composeAdaptive ρ σ` at security parameter `κ`: separate
`AdaptiveRouterState`s for the outer protocol `ρ` and inner subroutine `σ` so that each tracks
exactly its own activations and snapshots. -/
structure AdaptiveComposeState (Sρ Viewρ Sσ Viewσ : Type) (n : ℕ) : Type where
  /-- Router state of the outer hybrid protocol `ρ`. -/
  outer : AdaptiveRouterState Sρ Viewρ n
  /-- Router state of the inner subroutine protocol `σ`. -/
  sub : AdaptiveRouterState Sσ Viewσ n

/-- Apply `ρ.onCorrupt κ i` in canonical order for every `i ∈ C₀` at initialization. -/
@[expose] def AdaptiveHybridProtocol.applyInitialCorruptions
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (C₀ : Finset (Fin n)) (s : (ρ.machine κ).State) : (ρ.machine κ).State :=
  (List.finRange n).foldl (fun acc i => if i ∈ C₀ then ρ.onCorrupt κ i acc else acc) s

/-- Build the corruption report for party `i` from `ρ`'s router state. -/
@[expose] def AdaptiveHybridProtocol.corruptionReport
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (i : Fin n) (s : AdaptiveRouterState (ρ.machine κ).State Viewρ n) :
    CorruptionReport Viewρ :=
  { current := ρ.view κ i s.inner
    history := if ρ.memory = .nonErasing then some (s.trace i) else none }

/-- Append every party's `ρ.view` snapshot after an outer protocol activation. -/
@[expose] def AdaptiveHybridProtocol.recordSnapshot
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (s' : (ρ.machine κ).State) (corrupted : Finset (Fin n))
    (trace : Fin n → List Viewρ) :
    AdaptiveRouterState (ρ.machine κ).State Viewρ n :=
  { inner := s'
    corrupted := corrupted
    trace := fun j => trace j ++ [ρ.view κ j s'] }

/-- Every activation and initialization of `ρ.machine κ` makes at most `p.eval κ` calls. -/
@[expose] def AdaptiveHybridProtocol.PolyBounded
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ) (p : Polynomial ℕ) :
    Prop :=
  ∀ κ, (ρ.machine κ).IsBounded (p.eval κ)

/-- Snapshot stability under `onCorrupt` for `.nonErasing` `AdaptiveProtocol`s: `onCorrupt` does
not modify `view`, so initial snapshots recorded before vs. after `applyInitialCorruptions` agree.
Vacuously true when `P.memory = .erasing`. -/
@[expose] def AdaptiveProtocol.ViewStableOnCorrupt
    (P : AdaptiveProtocol n In Out NetQ NetR View₁) : Prop :=
  P.memory = .nonErasing → ∀ κ i j s, P.view κ i (P.onCorrupt κ j s) = P.view κ i s

/-- Snapshot stability under `onCorrupt` for `.nonErasing` `AdaptiveHybridProtocol`s. Vacuously
true when `ρ.memory = .erasing`. -/
@[expose] def AdaptiveHybridProtocol.ViewStableOnCorrupt
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ) : Prop :=
  ρ.memory = .nonErasing → ∀ κ i j s, ρ.view κ i (ρ.onCorrupt κ j s) = ρ.view κ i s

theorem AdaptiveProtocol.ViewStableOnCorrupt.of_erasing
    {P : AdaptiveProtocol n In Out NetQ NetR View₁} (h : P.memory = .erasing) :
    P.ViewStableOnCorrupt :=
  fun hne => absurd (h.symm.trans hne) (by decide)

theorem AdaptiveHybridProtocol.ViewStableOnCorrupt.of_erasing
    {ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ}
    (h : ρ.memory = .erasing) : ρ.ViewStableOnCorrupt :=
  fun hne => absurd (h.symm.trans hne) (by decide)

/-! ### Subroutine replacement (`composeAdaptive`) -/

/-- Closed machine answering subroutine party calls for `σ` inside `composeAdaptive ρ σ`,
guarding against corrupted parties and recording `σ` snapshots per activation. -/
@[expose] def subPartyMachine
    (σ : AdaptiveProtocol n SubIn SubOut NQ NR View₁) (κ : ℕ) :
    Machine OracleSpec.empty (partySpec n SubIn SubOut) where
  State := AdaptiveRouterState (σ.machine κ).State View₁ n
  init := do
    let s₀ ← (σ.machine κ).init
    return { inner := s₀, corrupted := ∅, trace := fun i => [σ.view κ i s₀] }
  handle
    | (j, subX) => fun sSub =>
        if j ∈ sSub.corrupted then
          pure (none, sSub)
        else do
          let (out, s') ← ((σ.machine κ).handle (.inl (j, subX))).run sSub.inner
          pure (out, σ.recordSnapshot κ s' sSub.corrupted sSub.trace)

private theorem isBounded_subPartyMachine
    {σ : AdaptiveProtocol n SubIn SubOut NQ NR View₁} {κ t : ℕ}
    (hσ : (σ.machine κ).IsBounded t) : (subPartyMachine σ κ).IsBounded t := by
  refine ⟨(hσ.1.bind fun _ => OracleComp.IsCostBounded.pure _ 0), fun q sSub => ?_⟩
  rcases q with ⟨j, subX⟩
  dsimp only [subPartyMachine, StateT.run]
  split_ifs
  · exact OracleComp.IsCostBounded.pure _ _
  · exact (hσ.2 (.inl (j, subX)) sSub.inner).bind fun _ => OracleComp.IsCostBounded.pure _ 0

/-- Single-session subroutine replacement `ρ^σ` in the snapshot adaptive-corruption model. A single
`.corrupt i` query corrupts party `i` across both `ρ` and `σ` via `onCorrupt`, returning
`AdaptiveHybridView` (`outer` and `sub` `CorruptionReport`s). Outer `memory` is `.erasing` so that
outer `adaptiveRouter` snapshots neither leak erased inner histories nor count simulator-internal
subroutine queries. -/
@[expose] def composeAdaptive
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (σ : AdaptiveProtocol n SubIn SubOut NQ NR View₁) :
    AdaptiveProtocol n In Out (NetQ ⊕ RoutedNetQ n SubIn NQ) (NetR ⊕ RoutedNetR SubOut NR)
      (AdaptiveHybridView Viewρ View₁) where
  machine κ := {
    State := AdaptiveComposeState (ρ.machine κ).State Viewρ (σ.machine κ).State View₁ n
    init := do
      let sσ ← (σ.machine κ).init
      let sρ ← (ρ.machine κ).init
      return {
        outer := { inner := sρ, corrupted := ∅, trace := fun i => [ρ.view κ i sρ] }
        sub := { inner := sσ, corrupted := ∅, trace := fun i => [σ.view κ i sσ] } }
    handle
      | .inl (i, x) => fun s => do
          let ((out, sρ'), sSub') ←
            (subPartyMachine σ κ).runFrom (((ρ.machine κ).handle (.inl (i, x))).run s.outer.inner)
              s.sub
          pure (out,
            { outer := ρ.recordSnapshot κ sρ' s.outer.corrupted s.outer.trace, sub := sSub' })
      | .inr (.inl q) => fun s => do
          let ((r, sρ'), sSub') ←
            (subPartyMachine σ κ).runFrom (((ρ.machine κ).handle (.inr q)).run s.outer.inner)
              s.sub
          pure (.inl r,
            { outer := ρ.recordSnapshot κ sρ' s.outer.corrupted s.outer.trace, sub := sSub' })
      | .inr (.inr (.inl (j, subX))) => fun s =>
          if j ∈ s.sub.corrupted then do
            let (out, s') ← ((σ.machine κ).handle (.inl (j, subX))).run s.sub.inner
            pure (.inr (.inl out),
              { outer := s.outer, sub := σ.recordSnapshot κ s' s.sub.corrupted s.sub.trace })
          else
            pure (.inr (.inl none), s)
      | .inr (.inr (.inr nq)) => fun s => do
          let (r, s') ← ((σ.machine κ).handle (.inr nq)).run s.sub.inner
          pure (.inr (.inr r),
            { outer := s.outer, sub := σ.recordSnapshot κ s' s.sub.corrupted s.sub.trace }) }
  view κ i s :=
    { outer := ρ.corruptionReport κ i s.outer
      sub := σ.corruptionReport κ i s.sub }
  onCorrupt κ i s :=
    { outer :=
        if i ∈ s.outer.corrupted then s.outer
        else
          { inner := ρ.onCorrupt κ i s.outer.inner
            corrupted := insert i s.outer.corrupted
            trace := s.outer.trace }
      sub :=
        if i ∈ s.sub.corrupted then s.sub
        else
          { inner := σ.onCorrupt κ i s.sub.inner
            corrupted := insert i s.sub.corrupted
            trace := s.sub.trace } }
  memory := .erasing

/-! ### Absorbed environment and composed simulator -/

/-- Lift a subroutine `partySpec n SubIn SubOut` program into `adaptiveExecSpec n SubIn SubOut`,
translating each `(j, subX)` query to `.inl (.party j subX)`. -/
@[expose] def liftSubParty {SubIn SubOut AdvQ AdvR : Type}
    (program : ProbOracleComp (partySpec n SubIn SubOut) α) :
    ProbOracleComp (adaptiveExecSpec n SubIn SubOut AdvQ AdvR) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (adaptiveExecSpec n SubIn SubOut AdvQ AdvR)) (Sum.inl k))
      fun p => ProbOracleComp.query (spec := adaptiveExecSpec n SubIn SubOut AdvQ AdvR)
        (.inl (.party p.1 p.2)))
    program

/-- Project a subroutine `AdaptiveNetR` reply to `RoutedNetR`. -/
@[expose] def subNetReplyToRouted :
    AdaptiveNetR Out NetR View₁ → RoutedNetR Out NetR
  | .party out => .inl out
  | .net r => .inr r
  | .corrupt _ => .inl none

/-- The interactive machine of `absorbAdaptiveHybrid`, running `ρ` internally against the
subroutine's `adaptiveExecSpec` port. -/
@[expose] def absorbAdaptiveMachine (mode : CorruptionMode) (C₀ : Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ) (κ : ℕ) :
    Machine
      (adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ) (AdaptiveNetR SubOut NR View₁))
      (adaptiveExecSpec n In Out (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
        (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₁))) where
  State := AdaptiveRouterState (ρ.machine κ).State Viewρ n
  init := do
    let s₀ ← (ρ.machine κ).init
    let s₁ := ρ.applyInitialCorruptions κ C₀ s₀
    return { inner := s₁, corrupted := C₀, trace := fun i => [ρ.view κ i s₁] }
  handle
    | .inl (.party i x) => fun s =>
        if i ∈ s.corrupted then
          pure (none, s)
        else do
          let (out, s') ← liftSubParty (((ρ.machine κ).handle (.inl (i, x))).run s.inner)
          pure (out, ρ.recordSnapshot κ s' s.corrupted s.trace)
    | .inl .status => fun s => pure (s.corrupted, s)
    | .inr (.party i x) => fun s =>
        if i ∈ s.corrupted then do
          let (out, s') ← liftSubParty (((ρ.machine κ).handle (.inl (i, x))).run s.inner)
          pure (.party out, ρ.recordSnapshot κ s' s.corrupted s.trace)
        else
          pure (.party none, s)
    | .inr (.net (.inl q)) => fun s => do
        let (r, s') ← liftSubParty (((ρ.machine κ).handle (.inr q)).run s.inner)
        pure (.net (.inl r), ρ.recordSnapshot κ s' s.corrupted s.trace)
    | .inr (.net (.inr (.inl (j, subX)))) => StateT.lift
        ((fun r => .net (.inr (subNetReplyToRouted r))) <$>
          ProbOracleComp.query
            (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
              (AdaptiveNetR SubOut NR View₁))
            (.inr (.party j subX)))
    | .inr (.net (.inr (.inr nq))) => StateT.lift
        ((fun r => .net (.inr (subNetReplyToRouted r))) <$>
          ProbOracleComp.query
            (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
              (AdaptiveNetR SubOut NR View₁))
            (.inr (.net nq)))
    | .inr (.corrupt i) => fun s =>
        match mode with
        | .static =>
            if i ∈ s.corrupted then do
              let rep ← ProbOracleComp.query
                (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
                  (AdaptiveNetR SubOut NR View₁))
                (.inr (.corrupt i))
              let outRep := match rep with
                | .corrupt (some repSub) =>
                    some { current := { outer := ρ.corruptionReport κ i s, sub := repSub }
                           history := none }
                | _ => none
              pure (.corrupt outRep, s)
            else
              pure (.corrupt none, s)
        | .adaptive => do
            let s' : AdaptiveRouterState (ρ.machine κ).State Viewρ n :=
              if i ∈ s.corrupted then s
              else
                { inner := ρ.onCorrupt κ i s.inner
                  corrupted := insert i s.corrupted
                  trace := s.trace }
            let rep ← ProbOracleComp.query
              (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
                (AdaptiveNetR SubOut NR View₁))
              (.inr (.corrupt i))
            let outRep := match rep with
              | .corrupt (some repSub) =>
                  some { current := { outer := ρ.corruptionReport κ i s', sub := repSub }
                         history := none }
              | _ => none
            pure (.corrupt outRep, s')

/-- The subroutine environment embedding `ρ` and `Z`: runs `ρ` internally against the subroutine
and forwards `Z`'s subroutine-network and `.corrupt` queries. -/
@[expose] def absorbAdaptiveHybrid (mode : CorruptionMode) (C₀ : ℕ → Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₁))) :
    AdaptiveEnvironment n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
      (AdaptiveNetR SubOut NR View₁) :=
  fun κ z => (absorbAdaptiveMachine mode (C₀ κ) ρ κ).link (Z κ z)

private def toOuterPartyReply {View : Type} :
    AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) View →
      AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₁) View₁
  | .party out => .party out
  | _ => .party none

private def toOuterNetReply {View : Type} :
    AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) View →
      AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₁) View₁
  | .net (.inl r) => .net (.inl r)
  | _ => .party none

private def toSubPartyReply {Viewρ : Type} :
    AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₂) →
      AdaptiveNetR SubOut NR View₂
  | .net (.inr (.inl out)) => .party out
  | _ => .party none

private def toSubNetReply {Viewρ : Type} :
    AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₂) →
      AdaptiveNetR SubOut NR View₂
  | .net (.inr (.inr r)) => .net r
  | _ => .party none

private def toSubCorruptReply {Viewρ : Type} :
    AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₂) →
      AdaptiveNetR SubOut NR View₂
  | .corrupt (some rep) => .corrupt (some rep.current.sub)
  | _ => .corrupt none

private def liftSimSubNet (mode : CorruptionMode) (expectedC : Finset (Fin n))
    (program :
      ProbOracleComp (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂)) α) :
    ProbOracleComp
      (netSpec (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂))) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec
        (netSpec (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
          (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂))))
        (Sum.inl k))
      fun q => match q with
        | .party j subX => toSubPartyReply <$> ProbOracleComp.query
            (spec := netSpec (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
              (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
            (.net (.inr (.inl (j, subX))))
        | .net nq => toSubNetReply <$> ProbOracleComp.query
            (spec := netSpec (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
              (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
            (.net (.inr (.inr nq)))
        | .corrupt j =>
            match mode with
            | .static =>
                if j ∈ expectedC then
                  toSubCorruptReply <$> ProbOracleComp.query
                    (spec := netSpec (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
                      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)
                        (AdaptiveHybridView Viewρ View₂)))
                    (.corrupt j)
                else pure (.corrupt none)
            | .adaptive =>
                if j ∈ expectedC then
                  toSubCorruptReply <$> ProbOracleComp.query
                    (spec := netSpec (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
                      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)
                        (AdaptiveHybridView Viewρ View₂)))
                    (.corrupt j)
                else pure (.corrupt none))
    program

/-- Machine of `adaptiveHybridSim`: forwards `ρ` queries, delegates subroutine `.party`/`.net`
queries to `S_D` while clamping unexpected `.corrupt` queries, and on `.corrupt i` runs `S_D`
(allowing `.corrupt i` inside `S_D`) and queries `.corrupt i` on `composeAdaptive` to assemble
`AdaptiveHybridView`. -/
def adaptiveHybridSimMachine (mode : CorruptionMode) (C₀ : Finset (Fin n))
    (S_D : Machine (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂))
      (netSpec (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁))) :
    Machine
      (netSpec (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
      (netSpec (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
        (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₁) (AdaptiveHybridView Viewρ View₁))) where
  State := S_D.State × Finset (Fin n)
  init := do
    let sS ← S_D.init
    return (sS, C₀)
  handle
    | .party i x => StateT.lift
        (toOuterPartyReply <$> ProbOracleComp.query (spec := netSpec
          (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
          (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
          (.party i x))
    | .net (.inl q) => StateT.lift
        (toOuterNetReply <$> ProbOracleComp.query (spec := netSpec
          (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
          (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
          (.net (.inl q)))
    | .net (.inr (.inl (j, subX))) => fun s => do
        let (r, sS') ← liftSimSubNet mode s.2 ((S_D.handle (.party j subX)).run s.1)
        pure (.net (.inr (subNetReplyToRouted r)), (sS', s.2))
    | .net (.inr (.inr nq)) => fun s => do
        let (r, sS') ← liftSimSubNet mode s.2 ((S_D.handle (.net nq)).run s.1)
        pure (.net (.inr (subNetReplyToRouted r)), (sS', s.2))
    | .corrupt i => fun s =>
        match mode with
        | .static =>
            if i ∈ s.2 then do
              let (r, sS') ← liftSimSubNet .static s.2 ((S_D.handle (.corrupt i)).run s.1)
              let outerRep ← ProbOracleComp.query (spec := netSpec
                (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
                (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
                (AdaptiveNetQ.corrupt i)
              let outRep := match r, outerRep with
                | .corrupt (some repSub), .corrupt (some repOuter) =>
                    some { current := { outer := repOuter.current.outer, sub := repSub }
                           history := none }
                | _, _ => none
              pure (.corrupt outRep, (sS', s.2))
            else
              pure (.corrupt none, s)
        | .adaptive => do
            let C' := insert i s.2
            let (r, sS') ← liftSimSubNet .adaptive C' ((S_D.handle (.corrupt i)).run s.1)
            let outerRep ← ProbOracleComp.query (spec := netSpec
              (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
              (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
              (AdaptiveNetQ.corrupt i)
            let outRep := match r, outerRep with
              | .corrupt (some repSub), .corrupt (some repOuter) =>
                  some { current := { outer := repOuter.current.outer, sub := repSub }
                         history := none }
              | _, _ => none
            pure (.corrupt outRep, (sS', C'))

private theorem adaptiveHybridSimMachine_handle_party (mode : CorruptionMode) (C₀ : Finset (Fin n))
    (S_D : Machine (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂))
      (netSpec (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁)))
    (i : Fin n) (x : In) (s : S_D.State × Finset (Fin n)) :
    ((adaptiveHybridSimMachine (Viewρ := Viewρ) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      mode C₀ S_D).handle (.party i x)).run s =
      (fun r => (toOuterPartyReply r, s)) <$>
        ProbOracleComp.query (spec := netSpec
          (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
          (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
          (.party i x) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem adaptiveHybridSimMachine_handle_net_inl (mode : CorruptionMode)
    (C₀ : Finset (Fin n))
    (S_D : Machine (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂))
      (netSpec (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁)))
    (q : NetQ) (s : S_D.State × Finset (Fin n)) :
    ((adaptiveHybridSimMachine (Viewρ := Viewρ) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      mode C₀ S_D).handle (.net (.inl q))).run s =
      (fun r => (toOuterNetReply r, s)) <$>
        ProbOracleComp.query (spec := netSpec
          (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
          (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
          (.net (.inl q)) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem adaptiveHybridSimMachine_handle_net_inr_inl (mode : CorruptionMode)
    (C₀ : Finset (Fin n))
    (S_D : Machine (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂))
      (netSpec (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁)))
    (j : Fin n) (subX : SubIn) (s : S_D.State × Finset (Fin n)) :
    ((adaptiveHybridSimMachine (Viewρ := Viewρ) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      mode C₀ S_D).handle (.net (.inr (.inl (j, subX))))).run s =
      (liftSimSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) (Viewρ := Viewρ)
        mode s.2 ((S_D.handle (.party j subX)).run s.1) >>= fun (r, sS') =>
        pure (.net (.inr (subNetReplyToRouted r)), (sS', s.2))) := rfl

private theorem adaptiveHybridSimMachine_handle_net_inr_inr (mode : CorruptionMode)
    (C₀ : Finset (Fin n))
    (S_D : Machine (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂))
      (netSpec (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁)))
    (nq : NQ₁) (s : S_D.State × Finset (Fin n)) :
    ((adaptiveHybridSimMachine (Viewρ := Viewρ) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      mode C₀ S_D).handle (.net (.inr (.inr nq)))).run s =
      (liftSimSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) (Viewρ := Viewρ)
        mode s.2 ((S_D.handle (.net nq)).run s.1) >>= fun (r, sS') =>
        pure (.net (.inr (subNetReplyToRouted r)), (sS', s.2))) := rfl

private theorem adaptiveHybridSimMachine_handle_corrupt_static (C₀ : Finset (Fin n))
    (S_D : Machine (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂))
      (netSpec (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁)))
    (i : Fin n) (s : S_D.State × Finset (Fin n)) :
    ((adaptiveHybridSimMachine (Viewρ := Viewρ) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      .static C₀ S_D).handle (.corrupt i)).run s =
      if i ∈ s.2 then
        (do
          let (r, sS') ← liftSimSubNet .static s.2 ((S_D.handle (.corrupt i)).run s.1)
          let outerRep ← ProbOracleComp.query (spec := netSpec
            (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
            (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
            (AdaptiveNetQ.corrupt i)
          let outRep := match r, outerRep with
            | .corrupt (some repSub), .corrupt (some repOuter) =>
                some { current := { outer := repOuter.current.outer, sub := repSub }
                       history := none }
            | _, _ => none
          pure (.corrupt outRep, (sS', s.2)))
      else
        pure (.corrupt none, s) := rfl

private theorem adaptiveHybridSimMachine_handle_corrupt_adaptive (C₀ : Finset (Fin n))
    (S_D : Machine (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂))
      (netSpec (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁)))
    (i : Fin n) (s : S_D.State × Finset (Fin n)) :
    ((adaptiveHybridSimMachine (Viewρ := Viewρ) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      .adaptive C₀ S_D).handle (.corrupt i)).run s =
      (do
        let C' := insert i s.2
        let (r, sS') ← liftSimSubNet .adaptive C' ((S_D.handle (.corrupt i)).run s.1)
        let outerRep ← ProbOracleComp.query (spec := netSpec
          (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
          (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂)))
          (AdaptiveNetQ.corrupt i)
        let outRep := match r, outerRep with
          | .corrupt (some repSub), .corrupt (some repOuter) =>
              some { current := { outer := repOuter.current.outer, sub := repSub }
                     history := none }
          | _, _ => none
        pure (.corrupt outRep, (sS', C'))) := rfl

/-- The composed simulator for `composeAdaptive ρ π` against `composeAdaptive ρ φ`, built from an
adaptive dummy-adversary simulator `S_D` for `π` against `φ` and initial corruption schedule
`C₀`. -/
@[expose] def adaptiveHybridSim (mode : CorruptionMode) (C₀ : ℕ → Finset (Fin n))
    (S_D : AdaptiveAdversary n SubIn SubOut NQ₂ NR₂ View₂
      (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁)) :
    AdaptiveAdversary n In Out (NetQ ⊕ RoutedNetQ n SubIn NQ₂) (NetR ⊕ RoutedNetR SubOut NR₂)
      (AdaptiveHybridView Viewρ View₂)
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₁) (AdaptiveHybridView Viewρ View₁)) where
  initial := C₀
  machine κ := adaptiveHybridSimMachine mode (C₀ κ) (S_D.machine κ)

/-! ### Budgets -/

/-- The budget `pρ + 1 + pZ * (pρ + 3)` of the status-checked absorbed environment. -/
@[expose] noncomputable def absorbAdaptiveCheckPoly (pZ pρ : Polynomial ℕ) : Polynomial ℕ :=
  pρ + 1 + pZ * (pρ + 3)

@[simp] theorem eval_absorbAdaptiveCheckPoly (pZ pρ : Polynomial ℕ) (κ : ℕ) :
    (absorbAdaptiveCheckPoly pZ pρ).eval κ = pρ.eval κ + 1 + pZ.eval κ * (pρ.eval κ + 3) := by
  simp only [absorbAdaptiveCheckPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_ofNat]

private theorem isQueryBounded_liftSubParty {SubIn SubOut AdvQ AdvR : Type}
    {program : ProbOracleComp (partySpec n SubIn SubOut) α} {m : ℕ}
    (h : program.IsQueryBounded m) :
    (liftSubParty (AdvQ := AdvQ) (AdvR := AdvR) program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query _
  | inr p => exact OracleComp.IsCostBounded.query _

private theorem isQueryBounded_liftSimSubNet (mode : CorruptionMode) (expectedC : Finset (Fin n))
    {program :
      ProbOracleComp (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂)) α}
    {m : ℕ} (h : program.IsQueryBounded m) :
    (liftSimSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) (Viewρ := Viewρ)
      mode expectedC program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  rcases q with k | (⟨j, subX⟩ | j | nq)
  · exact OracleComp.IsCostBounded.query _
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
  · dsimp only [sumHandler]
    cases mode <;> split_ifs
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    · exact OracleComp.IsCostBounded.pure _ _
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    · exact OracleComp.IsCostBounded.pure _ _
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- Adaptive subroutine replacement preserves polynomial call budgets. -/
theorem composeAdaptive_polyBounded
    {ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ}
    {σ : AdaptiveProtocol n SubIn SubOut NQ NR View₁} {pρ pσ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hσ : σ.PolyBounded pσ) :
    (composeAdaptive ρ σ).PolyBounded ((pρ + 1) * (pσ + 1) + pσ) := fun κ => by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  refine ⟨?_, fun q s => ?_⟩
  · refine ((hσ κ).1.bind fun _ => (hρ κ).1.bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono ?_
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
    omega
  · rcases q with ⟨i, x⟩ | (q | (⟨j, subX⟩ | nq))
    · refine ((Machine.isQueryBounded_runFrom (isBounded_subPartyMachine (hσ κ))
          ((hρ κ).2 (.inl (i, x)) s.outer.inner) s.sub).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0).mono ?_
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      omega
    · refine ((Machine.isQueryBounded_runFrom (isBounded_subPartyMachine (hσ κ))
          ((hρ κ).2 (.inr q) s.outer.inner) s.sub).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0).mono ?_
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      omega
    · dsimp only [composeAdaptive, StateT.run]
      split_ifs
      · refine (((hσ κ).2 (.inl (j, subX)) s.sub.inner).bind fun _ =>
            OracleComp.IsCostBounded.pure _ 0).mono ?_
        omega
      · exact OracleComp.IsCostBounded.pure _ _
    · refine (((hσ κ).2 (.inr nq) s.sub.inner).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0).mono ?_
      omega

/-- Absorbing an adaptive hybrid protocol with budget `pρ` into an environment with budget `pZ`
gives an environment with budget `absorbPoly pZ pρ`. -/
theorem absorbAdaptiveHybrid_polyBounded (mode : CorruptionMode) (C₀ : ℕ → Finset (Fin n))
    {ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ}
    {Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₁))}
    {pρ pZ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (hZ : Z.PolyBounded pZ) :
    (absorbAdaptiveHybrid mode C₀ ρ Z).PolyBounded (absorbPoly pZ pρ) := fun κ z => by
  have hM : (absorbAdaptiveMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode (C₀ κ) ρ κ).IsBounded
      (pρ.eval κ + 1) := by
    refine ⟨((hρ κ).1.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_succ _),
      fun q s => ?_⟩
    rcases q with (⟨i, x⟩ | _) | (⟨i, x⟩ | i | (q | (⟨j, subX⟩ | nq)))
    · dsimp only [absorbAdaptiveMachine, StateT.run]
      split_ifs
      · exact OracleComp.IsCostBounded.pure _ _
      · exact ((isQueryBounded_liftSubParty ((hρ κ).2 (.inl (i, x)) s.inner)).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_succ _)
    · exact OracleComp.IsCostBounded.pure _ _
    · dsimp only [absorbAdaptiveMachine, StateT.run]
      split_ifs
      · exact ((isQueryBounded_liftSubParty ((hρ κ).2 (.inl (i, x)) s.inner)).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_succ _)
      · exact OracleComp.IsCostBounded.pure _ _
    · dsimp only [absorbAdaptiveMachine, StateT.run]
      cases mode
      · split_ifs
        · exact ((OracleComp.IsCostBounded.query _).bind fun _ =>
            OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_add_left 1 _)
        · exact OracleComp.IsCostBounded.pure _ _
      · exact ((OracleComp.IsCostBounded.query _).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_add_left 1 _)
    · exact ((isQueryBounded_liftSubParty ((hρ κ).2 (.inr q) s.inner)).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_succ _)
    · exact ((OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)).mono
        (Nat.le_add_left 1 _)
    · exact ((OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)).mono
        (Nat.le_add_left 1 _)
  refine (Machine.isQueryBounded_link hM (hZ κ z)).mono (le_of_eq ?_)
  rw [eval_absorbPoly]

/-- The composed simulator of a subroutine simulator with budget `pS` has budget `pS + 1`. -/
theorem adaptiveHybridSim_polyBounded (mode : CorruptionMode) (C₀ : ℕ → Finset (Fin n))
    {S_D : AdaptiveAdversary n SubIn SubOut NQ₂ NR₂ View₂
      (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁)} {pS : Polynomial ℕ}
    (hS : S_D.PolyBounded pS) :
    (adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      (Viewρ := Viewρ) mode C₀ S_D).PolyBounded (pS + 1) := fun κ => by
  rw [Polynomial.eval_add, Polynomial.eval_one]
  refine ⟨((hS κ).1.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_succ _),
    fun q s => ?_⟩
  rcases s with ⟨sS, expectedC⟩
  rcases q with ⟨i, x⟩ | i | (q | (⟨j, subX⟩ | nq))
  · exact ((OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)).mono
      (Nat.le_add_left 1 _)
  · dsimp only [adaptiveHybridSim, adaptiveHybridSimMachine, StateT.run]
    cases mode
    · by_cases hi : i ∈ expectedC
      · simp only [hi, ↓reduceIte]
        exact ((isQueryBounded_liftSimSubNet .static expectedC ((hS κ).2 (.corrupt i) sS)).bind
          fun _ => (OracleComp.IsCostBounded.query _).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0).mono (le_rfl)
      · simp only [hi, ↓reduceIte]
        exact OracleComp.IsCostBounded.pure _ _
    · exact ((isQueryBounded_liftSimSubNet .adaptive (insert i expectedC)
          ((hS κ).2 (.corrupt i) sS)).bind fun _ =>
        (OracleComp.IsCostBounded.query _).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (le_rfl)
  · exact ((OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)).mono
      (Nat.le_add_left 1 _)
  · exact ((isQueryBounded_liftSimSubNet mode expectedC ((hS κ).2 (.party j subX) sS)).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_succ _)
  · exact ((isQueryBounded_liftSimSubNet mode expectedC ((hS κ).2 (.net nq) sS)).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_succ _)

/-! ### Execution regrouping: dummy adversary -/

private theorem applyInitialCorruptions_composeAdaptive
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (σ : AdaptiveProtocol n SubIn SubOut NQ NR View₁)
    (κ : ℕ) (C₀ : Finset (Fin n))
    (sρ₀ : (ρ.machine κ).State) (sσ₀ : (σ.machine κ).State)
    (trρ : Fin n → List Viewρ) (trσ : Fin n → List View₁) :
    (composeAdaptive ρ σ).applyInitialCorruptions κ C₀
        { outer := { inner := sρ₀, corrupted := ∅, trace := trρ }
          sub := { inner := sσ₀, corrupted := ∅, trace := trσ } } =
      { outer := { inner := ρ.applyInitialCorruptions κ C₀ sρ₀, corrupted := C₀, trace := trρ }
        sub :=
          { inner := σ.applyInitialCorruptions κ C₀ sσ₀
            corrupted := C₀
            trace := trσ } } := by
  have hgen : ∀ (l : List (Fin n)) (_hl : l.Nodup)
      (s : ((composeAdaptive ρ σ).machine κ).State),
      (∀ x ∈ l, x ∉ s.outer.corrupted) → (∀ x ∈ l, x ∉ s.sub.corrupted) →
      l.foldl (fun acc i => if i ∈ C₀ then (composeAdaptive ρ σ).onCorrupt κ i acc else acc) s =
        { outer :=
            { inner := l.foldl (fun acc i => if i ∈ C₀ then ρ.onCorrupt κ i acc else acc)
                s.outer.inner
              corrupted := s.outer.corrupted ∪ C₀.filter (· ∈ l)
              trace := s.outer.trace }
          sub :=
            { inner := l.foldl (fun acc i => if i ∈ C₀ then σ.onCorrupt κ i acc else acc)
                s.sub.inner
              corrupted := s.sub.corrupted ∪ C₀.filter (· ∈ l)
              trace := s.sub.trace } } := by
    intro l hl
    induction l with
    | nil =>
      intro s _ _
      have hfil : C₀.filter (· ∈ ([] : List (Fin n))) = ∅ := by
        ext x; simp
      rcases s with ⟨⟨iO, cO, tO⟩, ⟨iS, cS, tS⟩⟩
      simp only [List.foldl_nil, hfil, Finset.union_empty]
      rfl
    | cons a t ih =>
      intro s hnoOuter hnoSub
      rcases List.nodup_cons.mp hl with ⟨hat, ht⟩
      rw [List.foldl_cons]
      have hfil : C₀.filter (· ∈ a :: t) =
          (if a ∈ C₀ then insert a (C₀.filter (· ∈ t)) else C₀.filter (· ∈ t)) := by
        ext x
        simp only [Finset.mem_filter, List.mem_cons]
        split_ifs with ha
        · simp only [Finset.mem_insert, Finset.mem_filter]
          constructor
          · rintro ⟨hx, rfl | hxt⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hx, hxt⟩
          · rintro (rfl | ⟨hx, hxt⟩)
            · exact ⟨ha, Or.inl rfl⟩
            · exact ⟨hx, Or.inr hxt⟩
        · simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hx, rfl | hxt⟩
            · exact absurd hx ha
            · exact ⟨hx, hxt⟩
          · rintro ⟨hx, hxt⟩
            exact ⟨hx, Or.inr hxt⟩
      by_cases ha : a ∈ C₀
      · simp only [ha, ↓reduceIte]
        have haO : a ∉ s.outer.corrupted := hnoOuter a List.mem_cons_self
        have haS : a ∉ s.sub.corrupted := hnoSub a List.mem_cons_self
        have hstep : (composeAdaptive ρ σ).onCorrupt κ a s =
            { outer := { inner := ρ.onCorrupt κ a s.outer.inner
                         corrupted := insert a s.outer.corrupted
                         trace := s.outer.trace }
              sub := { inner := σ.onCorrupt κ a s.sub.inner
                       corrupted := insert a s.sub.corrupted
                       trace := s.sub.trace } } := by
          simp [composeAdaptive, haO, haS]
        rw [hstep]
        refine (ih ht _ ?_ ?_).trans ?_
        · intro x hx
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun h => hat (h ▸ hx), hnoOuter x (List.mem_cons_of_mem a hx)⟩
        · intro x hx
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun h => hat (h ▸ hx), hnoSub x (List.mem_cons_of_mem a hx)⟩
        · simp only [hfil, ha, ↓reduceIte, Finset.insert_union, Finset.union_insert]
          rw [List.foldl_cons, List.foldl_cons]
          simp only [ha, ↓reduceIte]
          rfl
      · simp only [ha, ↓reduceIte]
        refine (ih ht s (fun x hx => hnoOuter x (List.mem_cons_of_mem a hx))
          (fun x hx => hnoSub x (List.mem_cons_of_mem a hx))).trans ?_
        simp only [hfil, ha, ↓reduceIte]
        rw [List.foldl_cons, List.foldl_cons]
        simp only [ha, ↓reduceIte]
        rfl
  have hres := hgen (List.finRange n) (List.nodup_finRange n)
    { outer := { inner := sρ₀, corrupted := ∅, trace := trρ }
      sub := { inner := sσ₀, corrupted := ∅, trace := trσ } }
    (fun _ _ => Finset.notMem_empty _) (fun _ _ => Finset.notMem_empty _)
  have hC : C₀.filter (· ∈ List.finRange n) = C₀ := by
    ext x; simp [List.mem_finRange]
  simpa [AdaptiveProtocol.applyInitialCorruptions, AdaptiveHybridProtocol.applyInitialCorruptions,
    hC] using hres

private def RouterStateRel {S View : Type} {n : ℕ} (mem : PartyMemory)
    (r₁ r₂ : AdaptiveRouterState S View n) : Prop :=
  r₁.inner = r₂.inner ∧ r₁.corrupted = r₂.corrupted ∧ (mem = .nonErasing → r₁.trace = r₂.trace)

private theorem routerStateRel_recordSnapshot_adaptive
    (σ : AdaptiveProtocol n SubIn SubOut NQ NR View₁) (κ : ℕ)
    {r₁ r₂ : AdaptiveRouterState (σ.machine κ).State View₁ n} (h : RouterStateRel σ.memory r₁ r₂)
    (s' : (σ.machine κ).State) :
    RouterStateRel σ.memory (σ.recordSnapshot κ s' r₁.corrupted r₁.trace)
      (σ.recordSnapshot κ s' r₂.corrupted r₂.trace) :=
  ⟨rfl, h.2.1, fun hne => by simp only [AdaptiveProtocol.recordSnapshot, h.2.2 hne]⟩

private theorem routerStateRel_recordSnapshot_hybrid
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ) (κ : ℕ)
    {r₁ r₂ : AdaptiveRouterState (ρ.machine κ).State Viewρ n} (h : RouterStateRel ρ.memory r₁ r₂)
    (s' : (ρ.machine κ).State) :
    RouterStateRel ρ.memory (ρ.recordSnapshot κ s' r₁.corrupted r₁.trace)
      (ρ.recordSnapshot κ s' r₂.corrupted r₂.trace) :=
  ⟨rfl, h.2.1, fun hne => by simp only [AdaptiveHybridProtocol.recordSnapshot, h.2.2 hne]⟩

private theorem routerStateRel_corruptionReport_adaptive
    (σ : AdaptiveProtocol n SubIn SubOut NQ NR View₁) (κ : ℕ) (i : Fin n)
    {r₁ r₂ : AdaptiveRouterState (σ.machine κ).State View₁ n}
    (h : RouterStateRel σ.memory r₁ r₂) :
    σ.corruptionReport κ i r₁ = σ.corruptionReport κ i r₂ := by
  dsimp only [AdaptiveProtocol.corruptionReport]
  rw [h.1]
  congr 1
  split_ifs with hne
  · rw [h.2.2 hne]
  · rfl

private theorem routerStateRel_corruptionReport_hybrid
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ) (κ : ℕ) (i : Fin n)
    {r₁ r₂ : AdaptiveRouterState (ρ.machine κ).State Viewρ n}
    (h : RouterStateRel ρ.memory r₁ r₂) :
    ρ.corruptionReport κ i r₁ = ρ.corruptionReport κ i r₂ := by
  dsimp only [AdaptiveHybridProtocol.corruptionReport]
  rw [h.1]
  congr 1
  split_ifs with hne
  · rw [h.2.2 hne]
  · rfl

private theorem view_applyInitialCorruptions_adaptive
    {P : AdaptiveProtocol n In Out NetQ NetR View₁} (hstab : P.ViewStableOnCorrupt)
    (hne : P.memory = .nonErasing) (κ : ℕ) (C₀ : Finset (Fin n)) (i : Fin n)
    (s : (P.machine κ).State) :
    P.view κ i (P.applyInitialCorruptions κ C₀ s) = P.view κ i s := by
  dsimp only [AdaptiveProtocol.applyInitialCorruptions]
  generalize List.finRange n = l
  induction l generalizing s with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldl_cons]
    by_cases ha : a ∈ C₀
    · simp only [ha, ↓reduceIte]
      exact (ih _).trans (hstab hne κ i a s)
    · simp only [ha, ↓reduceIte]
      exact ih s

private theorem view_applyInitialCorruptions_hybrid
    {ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ}
    (hstab : ρ.ViewStableOnCorrupt) (hne : ρ.memory = .nonErasing) (κ : ℕ)
    (C₀ : Finset (Fin n)) (i : Fin n) (s : (ρ.machine κ).State) :
    ρ.view κ i (ρ.applyInitialCorruptions κ C₀ s) = ρ.view κ i s := by
  dsimp only [AdaptiveHybridProtocol.applyInitialCorruptions]
  generalize List.finRange n = l
  induction l generalizing s with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldl_cons]
    by_cases ha : a ∈ C₀
    · simp only [ha, ↓reduceIte]
      exact (ih _).trans (hstab hne κ i a s)
    · simp only [ha, ↓reduceIte]
      exact ih s

private theorem runFrom_subParty_eq_liftSubParty {γ : Type}
    (σ : AdaptiveProtocol n SubIn SubOut NQ NR View₁) (mode : CorruptionMode)
    (κ : ℕ) (C₀ : Finset (Fin n)) (prog : ProbOracleComp (partySpec n SubIn SubOut) γ)
    (sSub₁ sSub₂ : AdaptiveRouterState (σ.machine κ).State View₁ n)
    (hSub : RouterStateRel σ.memory sSub₁ sSub₂)
    (f : γ × AdaptiveRouterState (σ.machine κ).State View₁ n → ProbOracleComp OracleSpec.empty β)
    (g : γ × AdaptiveRouterState (σ.machine κ).State View₁ n → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a r₁ r₂, RouterStateRel σ.memory r₁ r₂ →
      r₁.corrupted = sSub₁.corrupted → r₂.corrupted = sSub₂.corrupted →
      f (a, r₁) = g (a, r₂)) :
    ((subPartyMachine σ κ).runFrom prog sSub₁ >>= f) =
      ((adaptiveRouter mode σ κ C₀).runFrom (liftSubParty prog) sSub₂ >>= g) := by
  have hid : (OracleComp.query :
      (q : ℕ ⊕ (Fin n × SubIn)) →
        ProbOracleComp (partySpec n SubIn SubOut) (probOracleSpec (partySpec n SubIn SubOut) q)) =
      sumHandler
        (fun k => OracleComp.query (spec := probOracleSpec (partySpec n SubIn SubOut)) (.inl k))
        (fun p => ProbOracleComp.query (spec := partySpec n SubIn SubOut) p) := by
    funext q; cases q <;> rfl
  conv_lhs => rw [← OracleComp.interpret_query_eq_self prog, hid]
  rw [liftSubParty]
  refine Machine.runFrom_interpret_intertwine (subPartyMachine σ κ) (adaptiveRouter mode σ κ C₀)
    (fun p => ProbOracleComp.query (spec := partySpec n SubIn SubOut) p)
    (fun p => ProbOracleComp.query (spec := adaptiveProtocolSpec n SubIn SubOut NQ NR View₁)
      (.inl (.party p.1 p.2)))
    (fun _ => True)
    (fun r₁ r₂ =>
      RouterStateRel σ.memory r₁ r₂ ∧ r₁.corrupted = sSub₁.corrupted ∧
        r₂.corrupted = sSub₂.corrupted)
    prog (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    sSub₁ sSub₂ ⟨hSub, rfl, rfl⟩ f g (fun a r₁ r₂ ⟨hr, hc₁, hc₂⟩ => hfg a r₁ r₂ hr hc₁ hc₂)
    fun ⟨j, subX⟩ r₁ r₂ k₁ k₂ _ ⟨hr, hc₁, hc₂⟩ hcont => ?_
  erw [Machine.runFrom_query, Machine.runFrom_query]
  dsimp only [subPartyMachine, adaptiveRouter, StateT.run]
  by_cases hj : j ∈ r₁.corrupted
  · have hj' : j ∈ r₂.corrupted := hr.2.1 ▸ hj
    simp only [hj, hj', ↓reduceIte]
    erw [pure_bind, pure_bind]
    exact hcont none r₁ r₂ ⟨hr, hc₁, hc₂⟩
  · have hj' : j ∉ r₂.corrupted := hr.2.1 ▸ hj
    simp only [hj, hj', ↓reduceIte]
    erw [hr.1, bind_assoc, bind_assoc]
    refine bind_congr fun ⟨out, s'⟩ => ?_
    erw [pure_bind, pure_bind]
    exact hcont out _ _ ⟨routerStateRel_recordSnapshot_adaptive σ κ hr s', hc₁, hc₂⟩

/-- Running `composeAdaptive ρ π` with `adaptiveDummyAdversary C₀` equals running `π` with
`adaptiveDummyAdversary C₀` and `absorbAdaptiveHybrid mode C₀ ρ Z` (for `ViewStableOnCorrupt`
protocols; vacuously satisfied for `.erasing` protocols). -/
theorem adaptiveExec_compose_dummy (mode : CorruptionMode) (C₀ : ℕ → Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (π : AdaptiveProtocol n SubIn SubOut NQ NR View₁)
    (hρ_view : ρ.ViewStableOnCorrupt) (hπ_view : π.ViewStableOnCorrupt)
    (Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₁)))
    (κ : ℕ) (z : List Bool) :
    adaptiveExec mode (composeAdaptive ρ π) (adaptiveDummyAdversary C₀ _ _) Z κ z =
      adaptiveExec mode π (adaptiveDummyAdversary C₀ _ _)
        (absorbAdaptiveHybrid mode C₀ ρ Z) κ z := by
  rw [adaptiveExec_dummyAdversary, adaptiveExec_dummyAdversary]
  dsimp only [absorbAdaptiveHybrid]
  rw [← Machine.run_comp]
  simp only [Machine.run, Machine.link]
  refine congrArg Machine.closeProgram ?_
  have hinit1 :
      (adaptiveRouter mode (composeAdaptive ρ π) κ (C₀ κ)).init = do
        let sπ ← (π.machine κ).init
        let sρ ← (ρ.machine κ).init
        let sρ₁ := ρ.applyInitialCorruptions κ (C₀ κ) sρ
        let sπ₁ := π.applyInitialCorruptions κ (C₀ κ) sπ
        let inner : ((composeAdaptive ρ π).machine κ).State :=
          { outer := { inner := sρ₁, corrupted := C₀ κ, trace := fun i => [ρ.view κ i sρ] }
            sub := { inner := sπ₁, corrupted := C₀ κ, trace := fun i => [π.view κ i sπ] } }
        return { inner := inner
                 corrupted := C₀ κ
                 trace := fun i => [(composeAdaptive ρ π).view κ i inner] } := by
    dsimp only [adaptiveRouter, composeAdaptive]
    rw [bind_assoc]
    refine bind_congr fun sπ => ?_
    rw [bind_assoc]
    refine bind_congr fun sρ => ?_
    rw [pure_bind]
    exact congrArg pure (by
      have happly := applyInitialCorruptions_composeAdaptive ρ π κ (C₀ κ) sρ sπ
        (fun i => [ρ.view κ i sρ]) (fun i => [π.view κ i sπ])
      dsimp only [composeAdaptive] at happly
      rw [happly])
  have hinit2 :
      ((absorbAdaptiveMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode (C₀ κ) ρ κ).comp
          (adaptiveRouter mode π κ (C₀ κ))).init = do
        let sπ ← (π.machine κ).init
        let sρ ← (ρ.machine κ).init
        return ({ inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ
                  corrupted := C₀ κ
                  trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ)] },
                { inner := π.applyInitialCorruptions κ (C₀ κ) sπ
                  corrupted := C₀ κ
                  trace := fun i => [π.view κ i (π.applyInitialCorruptions κ (C₀ κ) sπ)] }) := by
    dsimp only [Machine.comp, absorbAdaptiveMachine, adaptiveRouter]
    rw [bind_assoc]
    refine bind_congr fun sπ => ?_
    rw [pure_bind, bind_assoc]
    refine bind_congr fun sρ => ?_
    rw [pure_bind]
  rw [hinit1, hinit2]
  erw [ProbOracleComp.sample_bind, ProbOracleComp.sample_bind, bind_assoc, bind_assoc]
  refine bind_congr (m := ProbOracleComp _) fun sπ => ?_
  erw [ProbOracleComp.sample_bind, ProbOracleComp.sample_bind, bind_assoc, bind_assoc]
  refine bind_congr (m := ProbOracleComp _) fun sρ => ?_
  erw [ProbOracleComp.sample_pure, ProbOracleComp.sample_pure, pure_bind, pure_bind]
  rw [← bind_pure_comp, ← bind_pure_comp]
  let R :
      (adaptiveRouter mode (composeAdaptive ρ π) κ (C₀ κ)).State →
      ((absorbAdaptiveMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode (C₀ κ) ρ κ).comp
        (adaptiveRouter mode π κ (C₀ κ))).State → Prop :=
    fun s₁ s₂ =>
      RouterStateRel ρ.memory s₁.inner.outer s₂.1 ∧
      RouterStateRel π.memory s₁.inner.sub s₂.2 ∧
      s₁.corrupted = s₁.inner.outer.corrupted ∧
      s₁.inner.sub.corrupted = s₁.inner.outer.corrupted
  let innerInit : (sρ : (ρ.machine κ).State) → (sπ : (π.machine κ).State) →
      ((composeAdaptive ρ π).machine κ).State := fun sρ sπ =>
    { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ
                 corrupted := C₀ κ
                 trace := fun i => [ρ.view κ i sρ] }
      sub := { inner := π.applyInitialCorruptions κ (C₀ κ) sπ
               corrupted := C₀ κ
               trace := fun i => [π.view κ i sπ] } }
  have hR_init : R
      { inner := innerInit sρ sπ
        corrupted := C₀ κ
        trace := fun i => [(composeAdaptive ρ π).view κ i (innerInit sρ sπ)] }
      ({ inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ
         corrupted := C₀ κ
         trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ)] },
       { inner := π.applyInitialCorruptions κ (C₀ κ) sπ
         corrupted := C₀ κ
         trace := fun i => [π.view κ i (π.applyInitialCorruptions κ (C₀ κ) sπ)] }) :=
    ⟨⟨rfl, rfl, fun hne => funext fun i => by
        simp [innerInit, view_applyInitialCorruptions_hybrid hρ_view hne]⟩,
     ⟨rfl, rfl, fun hne => funext fun i => by
        simp [innerInit, view_applyInitialCorruptions_adaptive hπ_view hne]⟩,
     rfl, rfl⟩
  refine Machine.runFrom_intertwine
    (adaptiveRouter mode (composeAdaptive ρ π) κ (C₀ κ))
    ((absorbAdaptiveMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode (C₀ κ) ρ κ).comp
      (adaptiveRouter mode π κ (C₀ κ)))
    (fun _ => True) R (Z κ z)
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    _ _ hR_init (fun x => pure x.1) (fun x => pure x.1) (fun _ _ _ _ => rfl)
    fun q s₁ ⟨rρ, rπ⟩ k₁ k₂ _ hR hcont => ?_
  rcases hR with ⟨hO, hS, hcO, hcS⟩
  dsimp only at hO hS
  have hcorO : s₁.corrupted = rρ.corrupted := hcO.trans hO.2.1
  have hcorS : s₁.inner.sub.corrupted = rπ.corrupted := hS.2.1
  have hcorEq : rρ.corrupted = rπ.corrupted :=
    hO.2.1.symm.trans (hcS.symm.trans hS.2.1)
  rcases q with (⟨i, x⟩ | _) | (⟨i, x⟩ | i | (q | (⟨j, subX⟩ | nq)))
  · dsimp only [adaptiveRouter, Machine.comp, absorbAdaptiveMachine, StateT.run]
    by_cases hi : i ∈ s₁.corrupted
    · have hi' : i ∈ rρ.corrupted := hcorO ▸ hi
      simp only [hi, hi', ↓reduceIte]
      erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind, pure_bind]
      exact hcont none s₁ (rρ, rπ) ⟨hO, hS, hcO, hcS⟩
    · have hi' : i ∉ rρ.corrupted := hcorO ▸ hi
      simp only [hi, hi', ↓reduceIte]
      dsimp only [composeAdaptive, StateT.run]
      erw [hO.1, bind_map_left, Machine.runFrom_bind, bind_assoc, bind_assoc, bind_assoc]
      refine runFrom_subParty_eq_liftSubParty π mode κ (C₀ κ)
        (((ρ.machine κ).handle (.inl (i, x))).run rρ.inner) s₁.inner.sub rπ hS _ _ ?_
      intro ⟨out, sρ'⟩ sSub' rπ' hSub' hC₁ _
      dsimp only
      erw [Machine.runFrom_pure, pure_bind, pure_bind, pure_bind, Equiv.prodAssoc_apply]
      exact hcont out _ _
        ⟨routerStateRel_recordSnapshot_hybrid ρ κ hO sρ', hSub',
         hcO, hC₁.trans hcS⟩
  · dsimp only [adaptiveRouter, Machine.comp, absorbAdaptiveMachine, StateT.run]
    erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind, pure_bind]
    rw [← hcorO]
    exact hcont s₁.corrupted s₁ (rρ, rπ) ⟨hO, hS, hcO, hcS⟩
  · dsimp only [adaptiveRouter, Machine.comp, absorbAdaptiveMachine, StateT.run]
    by_cases hi : i ∈ s₁.corrupted
    · have hi' : i ∈ rρ.corrupted := hcorO ▸ hi
      simp only [hi, hi', ↓reduceIte]
      dsimp only [composeAdaptive, StateT.run]
      erw [hO.1, bind_map_left, Machine.runFrom_bind, bind_assoc, bind_assoc, bind_assoc]
      refine runFrom_subParty_eq_liftSubParty π mode κ (C₀ κ)
        (((ρ.machine κ).handle (.inl (i, x))).run rρ.inner) s₁.inner.sub rπ hS _ _ ?_
      intro ⟨out, sρ'⟩ sSub' rπ' hSub' hC₁ _
      dsimp only
      erw [Machine.runFrom_pure, pure_bind, pure_bind, pure_bind, Equiv.prodAssoc_apply]
      exact hcont (.party out) _ _
        ⟨routerStateRel_recordSnapshot_hybrid ρ κ hO sρ', hSub',
         hcO, hC₁.trans hcS⟩
    · have hi' : i ∉ rρ.corrupted := hcorO ▸ hi
      simp only [hi, hi', ↓reduceIte]
      erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind, pure_bind]
      exact hcont (.party none) s₁ (rρ, rπ) ⟨hO, hS, hcO, hcS⟩
  · dsimp only [adaptiveRouter, Machine.comp, absorbAdaptiveMachine, StateT.run]
    cases mode
    · by_cases hi : i ∈ s₁.corrupted
      · have hi' : i ∈ rρ.corrupted := hcorO ▸ hi
        have hiS : i ∈ rπ.corrupted := hcorEq ▸ hi'
        simp only [hi, hi', ↓reduceIte]
        erw [Machine.runFrom_bind, Machine.runFrom_query]
        dsimp only [adaptiveRouter, StateT.run]
        simp only [hiS, ↓reduceIte, pure_bind, Machine.runFrom_pure, map_pure,
          Equiv.prodAssoc_apply]
        have hrep : (composeAdaptive ρ π).corruptionReport κ i s₁ =
            { current := { outer := ρ.corruptionReport κ i rρ, sub := π.corruptionReport κ i rπ }
              history := none } := by
          dsimp only [AdaptiveProtocol.corruptionReport, composeAdaptive]
          simp only [reduceCtorEq, ↓reduceIte]
          congr 2
          · exact routerStateRel_corruptionReport_hybrid ρ κ i hO
          · rw [hS.1]
            congr 1
            split_ifs with hne
            · exact congrArg (fun t => some (t i)) (hS.2.2 hne)
            · rfl
        erw [hrep]
        exact hcont _ s₁ (rρ, rπ) ⟨hO, hS, hcO, hcS⟩
      · have hi' : i ∉ rρ.corrupted := hcorO ▸ hi
        simp only [hi, hi', ↓reduceIte]
        erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind, pure_bind]
        exact hcont (.corrupt none) s₁ (rρ, rπ) ⟨hO, hS, hcO, hcS⟩
    · erw [Machine.runFrom_bind, Machine.runFrom_query]
      dsimp only [adaptiveRouter, StateT.run]
      by_cases hi : i ∈ s₁.corrupted
      · have hi' : i ∈ rρ.corrupted := hcorO ▸ hi
        have hiS : i ∈ rπ.corrupted := hcorEq ▸ hi'
        simp only [hi, hi', hiS, ↓reduceIte, pure_bind, Machine.runFrom_pure, map_pure,
          Equiv.prodAssoc_apply]
        have hrep : (composeAdaptive ρ π).corruptionReport κ i s₁ =
            { current := { outer := ρ.corruptionReport κ i rρ, sub := π.corruptionReport κ i rπ }
              history := none } := by
          dsimp only [AdaptiveProtocol.corruptionReport, composeAdaptive]
          simp only [reduceCtorEq, ↓reduceIte]
          congr 2
          · exact routerStateRel_corruptionReport_hybrid ρ κ i hO
          · rw [hS.1]
            congr 1
            split_ifs with hne
            · exact congrArg (fun t => some (t i)) (hS.2.2 hne)
            · rfl
        erw [hrep]
        exact hcont _ s₁ (rρ, rπ) ⟨hO, hS, hcO, hcS⟩
      · have hi' : i ∉ rρ.corrupted := hcorO ▸ hi
        have hiS : i ∉ rπ.corrupted := hcorEq ▸ hi'
        have hiO : i ∉ s₁.inner.outer.corrupted := hcO ▸ hi
        have hiSub : i ∉ s₁.inner.sub.corrupted := hcS ▸ hiO
        simp only [hi, hi', hiS, ↓reduceIte, pure_bind, Machine.runFrom_pure, map_pure,
          Equiv.prodAssoc_apply]
        dsimp only [composeAdaptive]
        simp only [hiO, hiSub, ↓reduceIte]
        have hO' : RouterStateRel ρ.memory
            { inner := ρ.onCorrupt κ i s₁.inner.outer.inner
              corrupted := insert i s₁.inner.outer.corrupted
              trace := s₁.inner.outer.trace }
            { inner := ρ.onCorrupt κ i rρ.inner
              corrupted := insert i rρ.corrupted
              trace := rρ.trace } :=
          ⟨by rw [hO.1], by rw [hO.2.1], fun hne => hO.2.2 hne⟩
        have hS' : RouterStateRel π.memory
            { inner := π.onCorrupt κ i s₁.inner.sub.inner
              corrupted := insert i s₁.inner.sub.corrupted
              trace := s₁.inner.sub.trace }
            { inner := π.onCorrupt κ i rπ.inner
              corrupted := insert i rπ.corrupted
              trace := rπ.trace } :=
          ⟨by rw [hS.1], by rw [hS.2.1], fun hne => hS.2.2 hne⟩
        have hrep : (composeAdaptive ρ π).corruptionReport κ i
            { inner :=
                { outer := { inner := ρ.onCorrupt κ i s₁.inner.outer.inner
                             corrupted := insert i s₁.inner.outer.corrupted
                             trace := s₁.inner.outer.trace }
                  sub := { inner := π.onCorrupt κ i s₁.inner.sub.inner
                           corrupted := insert i s₁.inner.sub.corrupted
                           trace := s₁.inner.sub.trace } }
              corrupted := insert i s₁.corrupted
              trace := s₁.trace } =
            { current :=
                { outer := ρ.corruptionReport κ i
                    { inner := ρ.onCorrupt κ i rρ.inner
                      corrupted := insert i rρ.corrupted
                      trace := rρ.trace }
                  sub := π.corruptionReport κ i
                    { inner := π.onCorrupt κ i rπ.inner
                      corrupted := insert i rπ.corrupted
                      trace := rπ.trace } }
              history := none } := by
          dsimp only [AdaptiveProtocol.corruptionReport, composeAdaptive]
          simp only [reduceCtorEq, ↓reduceIte]
          congr 2
          · exact routerStateRel_corruptionReport_hybrid ρ κ i hO'
          · rw [hS.1]
            congr 1
            split_ifs with hne
            · exact congrArg (fun t => some (t i)) (hS'.2.2 hne)
            · rfl
        erw [hrep]
        exact hcont _ _ _ ⟨hO', hS', by rw [hcO], by rw [hcS]⟩
  · dsimp only [adaptiveRouter, Machine.comp, absorbAdaptiveMachine, composeAdaptive, StateT.run]
    erw [hO.1, bind_map_left, Machine.runFrom_bind, bind_assoc, bind_assoc, bind_assoc]
    refine runFrom_subParty_eq_liftSubParty π mode κ (C₀ κ)
      (((ρ.machine κ).handle (.inr q)).run rρ.inner) s₁.inner.sub rπ hS _ _ ?_
    intro ⟨r, sρ'⟩ sSub' rπ' hSub' hC₁ _
    dsimp only
    erw [Machine.runFrom_pure, pure_bind, pure_bind, pure_bind, Equiv.prodAssoc_apply]
    exact hcont (.net (.inl r)) _ _
      ⟨routerStateRel_recordSnapshot_hybrid ρ κ hO sρ', hSub',
       hcO, hC₁.trans hcS⟩
  · dsimp only [adaptiveRouter, Machine.comp, absorbAdaptiveMachine, composeAdaptive, StateT.run]
    erw [bind_map_left, Machine.runFrom_bind, Machine.runFrom_map, Machine.runFrom_query]
    dsimp only [adaptiveRouter, StateT.run]
    by_cases hj : j ∈ s₁.inner.sub.corrupted
    · have hj' : j ∈ rπ.corrupted := hcorS ▸ hj
      simp only [hj, hj', ↓reduceIte]
      erw [hS.1, bind_map_left, bind_assoc, bind_assoc, bind_assoc, bind_assoc]
      refine bind_congr fun ⟨out, s'⟩ => ?_
      repeat erw [pure_bind]
      dsimp only [Prod.map, id]
      erw [Equiv.prodAssoc_apply]
      have hsub : subNetReplyToRouted (Out := SubOut) (NetR := NR) (View₁ := View₁)
          (.party out) = .inl out := rfl
      erw [hsub]
      exact hcont (.net (.inr (.inl out))) _ _
        ⟨hO, routerStateRel_recordSnapshot_adaptive π κ hS s', hcO, hcS⟩
    · have hj' : j ∉ rπ.corrupted := hcorS ▸ hj
      simp only [hj, hj', ↓reduceIte]
      erw [bind_map_left, pure_bind, pure_bind]
      dsimp only [Prod.map, id]
      erw [Equiv.prodAssoc_apply]
      have hsub : subNetReplyToRouted (Out := SubOut) (NetR := NR) (View₁ := View₁)
          (.party none) = .inl none := rfl
      erw [hsub]
      exact hcont (.net (.inr (.inl none))) _ (rρ, rπ) ⟨hO, hS, hcO, hcS⟩
  · dsimp only [adaptiveRouter, Machine.comp, absorbAdaptiveMachine, composeAdaptive, StateT.run]
    erw [bind_map_left, Machine.runFrom_bind, Machine.runFrom_map, Machine.runFrom_query]
    dsimp only [adaptiveRouter, StateT.run]
    erw [hS.1, bind_map_left, bind_assoc, bind_assoc, bind_assoc, bind_assoc]
    refine bind_congr fun ⟨r, s'⟩ => ?_
    repeat erw [pure_bind]
    dsimp only [Prod.map, id]
    erw [Equiv.prodAssoc_apply]
    have hsub : subNetReplyToRouted (Out := SubOut) (NetR := NR) (View₁ := View₁)
        (.net r) = .inr r := rfl
    erw [hsub]
    exact hcont (.net (.inr (.inr r))) _ _
      ⟨hO, routerStateRel_recordSnapshot_adaptive π κ hS s', hcO, hcS⟩

/-! ### Execution regrouping: composed simulator and synchronization check -/

/-- Synchronization condition for `eval_adaptiveExec_compose_sim`: `S_D` starts with `initial = C₀`
and every activation preserves `adaptiveRouter mode φ`'s `corrupted` set (`C` on `.party`/`.net`,
and `if mode = .adaptive then insert i C else C` on `.corrupt i`) whenever `C₀ κ ⊆ C`. -/
@[expose] def AdaptiveAdversary.CorruptSync (mode : CorruptionMode) (C₀ : ℕ → Finset (Fin n))
    (φ : AdaptiveProtocol n SubIn SubOut NQ₂ NR₂ View₂)
    (S_D : AdaptiveAdversary n SubIn SubOut NQ₂ NR₂ View₂
      (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁)) : Prop :=
  S_D.initial = C₀ ∧
    ∀ (κ : ℕ) (q : AdaptiveNetQ n SubIn NQ₁) (sS : (S_D.machine κ).State)
      (rs : AdaptiveRouterState (φ.machine κ).State View₂ n),
      C₀ κ ⊆ rs.corrupted →
      ∀ x ∈ (closeEval ((adaptiveRouter mode φ κ (C₀ κ)).runFrom
        (liftAdaptiveNet (((S_D.machine κ).handle q).run sS)) rs)).support,
        x.2.corrupted =
          match q with
          | .corrupt i => if mode = .adaptive then insert i rs.corrupted else rs.corrupted
          | _ => rs.corrupted

private structure AbsorbCheckState (Sρ Viewρ : Type) (n : ℕ) : Type where
  outer : AdaptiveRouterState Sρ Viewρ n
  desynced : Bool

open Classical in
private noncomputable def absorbAdaptiveCheckMachine (mode : CorruptionMode) (C₀ : Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ) (κ : ℕ) :
    Machine
      (adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ) (AdaptiveNetR SubOut NR View₁))
      (adaptiveExecSpec n In Out (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
        (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₁))) where
  State := AbsorbCheckState (ρ.machine κ).State Viewρ n
  init := do
    let s₀ ← (ρ.machine κ).init
    let s₁ := ρ.applyInitialCorruptions κ C₀ s₀
    return { outer := { inner := s₁, corrupted := C₀, trace := fun i => [ρ.view κ i s₁] }
             desynced := false }
  handle
    | .inl (.party i x) => fun s =>
        if i ∈ s.outer.corrupted then
          pure (none, s)
        else do
          let (out, s') ← liftSubParty (((ρ.machine κ).handle (.inl (i, x))).run s.outer.inner)
          pure (out,
            { outer := ρ.recordSnapshot κ s' s.outer.corrupted s.outer.trace
              desynced := s.desynced })
    | .inl .status => fun s => pure (s.outer.corrupted, s)
    | .inr (.party i x) => fun s =>
        if i ∈ s.outer.corrupted then do
          let (out, s') ← liftSubParty (((ρ.machine κ).handle (.inl (i, x))).run s.outer.inner)
          pure (.party out,
            { outer := ρ.recordSnapshot κ s' s.outer.corrupted s.outer.trace
              desynced := s.desynced })
        else
          pure (.party none, s)
    | .inr (.net (.inl q)) => fun s => do
        let (r, s') ← liftSubParty (((ρ.machine κ).handle (.inr q)).run s.outer.inner)
        pure (.net (.inl r),
          { outer := ρ.recordSnapshot κ s' s.outer.corrupted s.outer.trace
            desynced := s.desynced })
    | .inr (.net (.inr (.inl (j, subX)))) => fun s => do
        let r ← ProbOracleComp.query
          (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
            (AdaptiveNetR SubOut NR View₁))
          (.inr (.party j subX))
        let st ← ProbOracleComp.query
          (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
            (AdaptiveNetR SubOut NR View₁))
          (.inl .status)
        pure (.net (.inr (subNetReplyToRouted r)),
          { outer := s.outer, desynced := s.desynced || decide (st ≠ s.outer.corrupted) })
    | .inr (.net (.inr (.inr nq))) => fun s => do
        let r ← ProbOracleComp.query
          (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
            (AdaptiveNetR SubOut NR View₁))
          (.inr (.net nq))
        let st ← ProbOracleComp.query
          (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
            (AdaptiveNetR SubOut NR View₁))
          (.inl .status)
        pure (.net (.inr (subNetReplyToRouted r)),
          { outer := s.outer, desynced := s.desynced || decide (st ≠ s.outer.corrupted) })
    | .inr (.corrupt i) => fun s =>
        match mode with
        | .static =>
            if i ∈ s.outer.corrupted then do
              let rep ← ProbOracleComp.query
                (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
                  (AdaptiveNetR SubOut NR View₁))
                (.inr (.corrupt i))
              let st ← ProbOracleComp.query
                (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
                  (AdaptiveNetR SubOut NR View₁))
                (.inl .status)
              let outRep := match rep with
                | .corrupt (some repSub) =>
                    some { current := { outer := ρ.corruptionReport κ i s.outer, sub := repSub }
                           history := none }
                | _ => none
              pure (.corrupt outRep,
                { outer := s.outer, desynced := s.desynced || decide (st ≠ s.outer.corrupted) })
            else
              pure (.corrupt none, s)
        | .adaptive => do
            let s' : AdaptiveRouterState (ρ.machine κ).State Viewρ n :=
              if i ∈ s.outer.corrupted then s.outer
              else
                { inner := ρ.onCorrupt κ i s.outer.inner
                  corrupted := insert i s.outer.corrupted
                  trace := s.outer.trace }
            let rep ← ProbOracleComp.query
              (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
                (AdaptiveNetR SubOut NR View₁))
              (.inr (.corrupt i))
            let st ← ProbOracleComp.query
              (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
                (AdaptiveNetR SubOut NR View₁))
              (.inl .status)
            let outRep := match rep with
              | .corrupt (some repSub) =>
                  some { current := { outer := ρ.corruptionReport κ i s', sub := repSub }
                         history := none }
              | _ => none
            pure (.corrupt outRep,
              { outer := s', desynced := s.desynced || decide (st ≠ s'.corrupted) })

private theorem absorbAdaptiveCheckMachine_handle_inl_party (mode : CorruptionMode)
    (C₀ : Finset (Fin n)) (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (i : Fin n) (x : In) (s : AbsorbCheckState (ρ.machine κ).State Viewρ n) :
    ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode C₀ ρ κ).handle
      (.inl (.party i x))).run s =
      if i ∈ s.outer.corrupted then
        pure (none, s)
      else (do
        let (out, s') ← liftSubParty (((ρ.machine κ).handle (.inl (i, x))).run s.outer.inner)
        pure (out,
          { outer := ρ.recordSnapshot κ s' s.outer.corrupted s.outer.trace
            desynced := s.desynced })) := rfl

private theorem absorbAdaptiveCheckMachine_handle_inl_status (mode : CorruptionMode)
    (C₀ : Finset (Fin n)) (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (s : AbsorbCheckState (ρ.machine κ).State Viewρ n) :
    ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode C₀ ρ κ).handle
      (.inl .status)).run s = pure (s.outer.corrupted, s) := rfl

private theorem absorbAdaptiveCheckMachine_handle_inr_party (mode : CorruptionMode)
    (C₀ : Finset (Fin n)) (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (i : Fin n) (x : In) (s : AbsorbCheckState (ρ.machine κ).State Viewρ n) :
    ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode C₀ ρ κ).handle
      (.inr (.party i x))).run s =
      if i ∈ s.outer.corrupted then (do
        let (out, s') ← liftSubParty (((ρ.machine κ).handle (.inl (i, x))).run s.outer.inner)
        pure (.party out,
          { outer := ρ.recordSnapshot κ s' s.outer.corrupted s.outer.trace
            desynced := s.desynced }))
      else
        pure (.party none, s) := rfl

private theorem absorbAdaptiveCheckMachine_handle_inr_net_inl (mode : CorruptionMode)
    (C₀ : Finset (Fin n)) (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (q : NetQ) (s : AbsorbCheckState (ρ.machine κ).State Viewρ n) :
    ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode C₀ ρ κ).handle
      (.inr (.net (.inl q)))).run s = (do
      let (r, s') ← liftSubParty (((ρ.machine κ).handle (.inr q)).run s.outer.inner)
      pure (.net (.inl r),
        { outer := ρ.recordSnapshot κ s' s.outer.corrupted s.outer.trace
          desynced := s.desynced })) := rfl

open Classical in
private theorem absorbAdaptiveCheckMachine_handle_inr_net_inr_inl (mode : CorruptionMode)
    (C₀ : Finset (Fin n)) (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (j : Fin n) (subX : SubIn) (s : AbsorbCheckState (ρ.machine κ).State Viewρ n) :
    ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode C₀ ρ κ).handle
      (.inr (.net (.inr (.inl (j, subX)))))).run s = (do
      let r ← ProbOracleComp.query
        (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
          (AdaptiveNetR SubOut NR View₁))
        (.inr (.party j subX))
      let st ← ProbOracleComp.query
        (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
          (AdaptiveNetR SubOut NR View₁))
        (.inl .status)
      pure (.net (.inr (subNetReplyToRouted r)),
        { outer := s.outer, desynced := s.desynced || decide (st ≠ s.outer.corrupted) })) := rfl

open Classical in
private theorem absorbAdaptiveCheckMachine_handle_inr_net_inr_inr (mode : CorruptionMode)
    (C₀ : Finset (Fin n)) (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (nq : NQ) (s : AbsorbCheckState (ρ.machine κ).State Viewρ n) :
    ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode C₀ ρ κ).handle
      (.inr (.net (.inr (.inr nq))))).run s = (do
      let r ← ProbOracleComp.query
        (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
          (AdaptiveNetR SubOut NR View₁))
        (.inr (.net nq))
      let st ← ProbOracleComp.query
        (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
          (AdaptiveNetR SubOut NR View₁))
        (.inl .status)
      pure (.net (.inr (subNetReplyToRouted r)),
        { outer := s.outer, desynced := s.desynced || decide (st ≠ s.outer.corrupted) })) := rfl

open Classical in
private theorem absorbAdaptiveCheckMachine_handle_inr_corrupt_static
    (C₀ : Finset (Fin n)) (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (i : Fin n) (s : AbsorbCheckState (ρ.machine κ).State Viewρ n) :
    ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁)
        .static C₀ ρ κ).handle (.inr (.corrupt i))).run s =
      if i ∈ s.outer.corrupted then (do
        let rep ← ProbOracleComp.query
          (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
            (AdaptiveNetR SubOut NR View₁))
          (.inr (.corrupt i))
        let st ← ProbOracleComp.query
          (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
            (AdaptiveNetR SubOut NR View₁))
          (.inl .status)
        let outRep := match rep with
          | .corrupt (some repSub) =>
              some { current := { outer := ρ.corruptionReport κ i s.outer, sub := repSub }
                     history := none }
          | _ => none
        pure (.corrupt outRep,
          { outer := s.outer, desynced := s.desynced || decide (st ≠ s.outer.corrupted) }))
      else
        pure (.corrupt none, s) := rfl

open Classical in
private theorem absorbAdaptiveCheckMachine_handle_inr_corrupt_adaptive
    (C₀ : Finset (Fin n)) (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (κ : ℕ) (i : Fin n) (s : AbsorbCheckState (ρ.machine κ).State Viewρ n) :
    ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁)
        .adaptive C₀ ρ κ).handle (.inr (.corrupt i))).run s = (do
      let s' : AdaptiveRouterState (ρ.machine κ).State Viewρ n :=
        if i ∈ s.outer.corrupted then s.outer
        else
          { inner := ρ.onCorrupt κ i s.outer.inner
            corrupted := insert i s.outer.corrupted
            trace := s.outer.trace }
      let rep ← ProbOracleComp.query
        (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
          (AdaptiveNetR SubOut NR View₁))
        (.inr (.corrupt i))
      let st ← ProbOracleComp.query
        (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
          (AdaptiveNetR SubOut NR View₁))
        (.inl .status)
      let outRep := match rep with
        | .corrupt (some repSub) =>
            some { current := { outer := ρ.corruptionReport κ i s', sub := repSub }
                   history := none }
        | _ => none
      pure (.corrupt outRep,
        { outer := s', desynced := s.desynced || decide (st ≠ s'.corrupted) })) := rfl

open Classical in
private noncomputable def absorbAdaptiveHybridCheck (mode : CorruptionMode)
    (C₀ : ℕ → Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₁)))
    (target : Bool) :
    AdaptiveEnvironment n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
      (AdaptiveNetR SubOut NR View₁) :=
  fun κ z => do
    let st₀ ← ProbOracleComp.query
      (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
        (AdaptiveNetR SubOut NR View₁))
      (.inl .status)
    if st₀ ≠ C₀ κ then
      pure false
    else do
      let sInit ← ProbOracleComp.sample (absorbAdaptiveCheckMachine mode (C₀ κ) ρ κ).init
      let res ← (absorbAdaptiveCheckMachine mode (C₀ κ) ρ κ).runFrom (Z κ z) sInit
      pure (!res.2.desynced && (res.1 == target))

private theorem isBounded_absorbAdaptiveCheckMachine (mode : CorruptionMode) (C₀ : Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ) {κ t : ℕ}
    (hρ : (ρ.machine κ).IsBounded t) :
    (absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode C₀ ρ κ).IsBounded
      (t + 2) := by
  refine ⟨(hρ.1.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega), fun q s => ?_⟩
  rcases q with (⟨i, x⟩ | _) | (⟨i, x⟩ | i | (q | (⟨j, subX⟩ | nq)))
  · dsimp only [absorbAdaptiveCheckMachine, StateT.run]
    split_ifs
    · exact OracleComp.IsCostBounded.pure _ _
    · exact ((isQueryBounded_liftSubParty (hρ.2 (.inl (i, x)) s.outer.inner)).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  · exact OracleComp.IsCostBounded.pure _ _
  · dsimp only [absorbAdaptiveCheckMachine, StateT.run]
    split_ifs
    · exact ((isQueryBounded_liftSubParty (hρ.2 (.inl (i, x)) s.outer.inner)).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (by omega)
    · exact OracleComp.IsCostBounded.pure _ _
  · dsimp only [absorbAdaptiveCheckMachine, StateT.run]
    cases mode
    · split_ifs
      · exact ((OracleComp.IsCostBounded.query _).bind fun _ =>
          (OracleComp.IsCostBounded.query _).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0).mono (by omega)
      · exact OracleComp.IsCostBounded.pure _ _
    · exact ((OracleComp.IsCostBounded.query _).bind fun _ =>
        (OracleComp.IsCostBounded.query _).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  · exact ((isQueryBounded_liftSubParty (hρ.2 (.inr q) s.outer.inner)).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  · exact ((OracleComp.IsCostBounded.query _).bind fun _ =>
      (OracleComp.IsCostBounded.query _).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  · exact ((OracleComp.IsCostBounded.query _).bind fun _ =>
      (OracleComp.IsCostBounded.query _).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0).mono (by omega)

open Classical in
private theorem absorbAdaptiveHybridCheck_polyBounded (mode : CorruptionMode)
    (C₀ : ℕ → Finset (Fin n))
    {ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ}
    {Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₁))}
    {pρ pZ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (hZ : Z.PolyBounded pZ) (target : Bool) :
    (absorbAdaptiveHybridCheck mode C₀ ρ Z target).PolyBounded
      (absorbAdaptiveCheckPoly pZ pρ) := fun κ z => by
  have hM := isBounded_absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁)
    mode (C₀ κ) ρ (hρ κ)
  have hInit : (absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode (C₀ κ)
      ρ κ).init.IsQueryBounded (pρ.eval κ) :=
    (hρ κ).1.bind fun _ => OracleComp.IsCostBounded.pure _ 0
  dsimp only [absorbAdaptiveHybridCheck, ProbOracleComp.query]
  rw [eval_absorbAdaptiveCheckPoly]
  have hrest : ∀ st₀ : probOracleSpec
      (adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ)
        (AdaptiveNetR SubOut NR View₁)) (.inr (.inl .status)),
      (if st₀ ≠ C₀ κ then pure false
       else do
         let sInit ← ProbOracleComp.sample (absorbAdaptiveCheckMachine mode (C₀ κ) ρ κ).init
         let res ← (absorbAdaptiveCheckMachine mode (C₀ κ) ρ κ).runFrom (Z κ z) sInit
         pure (!res.2.desynced && (res.1 == target))).IsQueryBounded
        (pρ.eval κ + pZ.eval κ * (pρ.eval κ + 2 + 1)) := by
    intro st₀
    split_ifs
    · exact (OracleComp.IsCostBounded.pure false 0).mono (by omega)
    · have hbody :
          (do
            let sInit ← ProbOracleComp.sample (absorbAdaptiveCheckMachine mode (C₀ κ) ρ κ).init
            let res ←
              (absorbAdaptiveCheckMachine mode (C₀ κ) ρ κ).runFrom (Z κ z) sInit
            pure (!res.2.desynced && (res.1 == target))).IsQueryBounded
            (pρ.eval κ + (pZ.eval κ * (pρ.eval κ + 2 + 1) + 0)) :=
        (Machine.isQueryBounded_sample hInit).bind fun sInit =>
          (Machine.isQueryBounded_runFrom hM (hZ κ z) sInit).bind fun res =>
            OracleComp.IsCostBounded.pure (!res.2.desynced && (res.1 == target)) 0
      refine hbody.mono ?_
      omega
  dsimp only [OracleComp.IsQueryBounded] at hrest ⊢
  refine ((OracleComp.IsCostBounded.query _).bind hrest).mono ?_
  simp only [add_assoc, Nat.reduceAdd]
  omega

open Classical in
private theorem query_status_polyBounded (pZ pρ : Polynomial ℕ) {AdvQ AdvR : Type}
    (C₀ : ℕ → Finset (Fin n)) :
    AdaptiveEnvironment.PolyBounded
      (fun (κ : ℕ) (_ : List Bool) =>
        ProbOracleComp.query
          (spec := adaptiveExecSpec n SubIn SubOut AdvQ AdvR) (.inl .status) >>= fun C =>
          pure (decide (C = C₀ κ)))
      (absorbAdaptiveCheckPoly pZ pρ) := by
  intro κ _
  rw [eval_absorbAdaptiveCheckPoly]
  exact ((OracleComp.IsCostBounded.query _).bind fun _ =>
    OracleComp.IsCostBounded.pure _ 0).mono (by omega)

private theorem runFrom_liftAdaptiveAdversary_liftSubParty
    {SubIn SubOut AdvQ₁ AdvR₁ Q₂ R₂ γ : Type}
    (M : Machine (netSpec Q₂ R₂) (netSpec AdvQ₁ AdvR₁))
    (prog : ProbOracleComp (partySpec n SubIn SubOut) γ) (s : M.State) :
    (liftAdaptiveAdversary (n := n) (In := SubIn) (Out := SubOut) M).runFrom
        (liftSubParty prog) s =
      (fun a => (a, s)) <$> liftSubParty prog := by
  refine Machine.runFrom_interpret_of_forward (liftAdaptiveAdversary M) _ _ (fun q s => ?_) prog s
  cases q with
  | inl k =>
    rw [Machine.runFrom_call]
    change (StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k))).run s = _
    rw [StateT.run_lift, bind_pure_comp]
    rfl
  | inr p =>
    change (liftAdaptiveAdversary M).runFrom
      (ProbOracleComp.query (Sum.inl (.party p.1 p.2))) s = _
    rw [Machine.runFrom_query]
    change (StateT.lift (ProbOracleComp.query _)).run s = _
    rw [StateT.run_lift, bind_pure_comp]
    rfl

private theorem liftAdaptiveAdversary_handle_inl {In Out Q R AdvQ AdvR : Type}
    (A : Machine (netSpec Q R) (netSpec AdvQ AdvR))
    (p : AdaptivePartyQ n In) (s : A.State) :
    ((liftAdaptiveAdversary (n := n) (In := In) (Out := Out) A).handle (.inl p)).run s =
      (fun a => (a, s)) <$>
        ProbOracleComp.query (spec := adaptivePartySpec n In Out ⊕ₒ netSpec Q R) (Sum.inl p) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp]

private theorem liftAdaptiveAdversary_handle_inr {In Out Q R AdvQ AdvR : Type}
    (A : Machine (netSpec Q R) (netSpec AdvQ AdvR))
    (q : AdvQ) (s : A.State) :
    ((liftAdaptiveAdversary (n := n) (In := In) (Out := Out) A).handle (.inr q)).run s =
      liftAdaptiveNet ((A.handle q).run s) := rfl

private theorem machine_comp_handle_run {ιI ιJ ιE : Type}
    {I : ιI → Type} {J : ιJ → Type} {E : ιE → Type}
    (A : Machine J E) (P : Machine I J) (q : ιE) (s : A.State × P.State) :
    ((A.comp P).handle q).run s =
      Equiv.prodAssoc (E q) A.State P.State <$> P.runFrom ((A.handle q).run s.1) s.2 := rfl

private theorem runFrom_adaptiveRouter_liftSubParty_bind_congr {γ : Type}
    (mode : CorruptionMode) (σ : AdaptiveProtocol n SubIn SubOut NQ NR View₁)
    (κ : ℕ) (C₀ : Finset (Fin n)) (prog : ProbOracleComp (partySpec n SubIn SubOut) γ)
    (rσ : AdaptiveRouterState (σ.machine κ).State View₁ n)
    (f g : γ × AdaptiveRouterState (σ.machine κ).State View₁ n → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a rσ', rσ'.corrupted = rσ.corrupted → f (a, rσ') = g (a, rσ')) :
    ((adaptiveRouter mode σ κ C₀).runFrom
        (liftSubParty (AdvQ := AdaptiveNetQ n SubIn NQ) (AdvR := AdaptiveNetR SubOut NR View₁)
          prog) rσ >>= f) =
      ((adaptiveRouter mode σ κ C₀).runFrom
        (liftSubParty (AdvQ := AdaptiveNetQ n SubIn NQ) (AdvR := AdaptiveNetR SubOut NR View₁)
          prog) rσ >>= g) := by
  refine Machine.runFrom_interpret_intertwine (adaptiveRouter mode σ κ C₀)
    (adaptiveRouter mode σ κ C₀)
    (fun p => ProbOracleComp.query (spec := adaptiveProtocolSpec n SubIn SubOut NQ NR View₁)
      (.inl (.party p.1 p.2)))
    (fun p => ProbOracleComp.query (spec := adaptiveProtocolSpec n SubIn SubOut NQ NR View₁)
      (.inl (.party p.1 p.2)))
    (fun _ => True) (fun r₁ r₂ => r₁ = r₂ ∧ r₁.corrupted = rσ.corrupted) prog
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    rσ rσ ⟨rfl, rfl⟩ f g (fun a r₁ _ hR => hR.1 ▸ hfg a r₁ hR.2)
    fun ⟨j, subX⟩ r₁ _ k₁ k₂ _ ⟨hEq, hC⟩ hcont => by
      subst hEq
      erw [Machine.runFrom_query]
      dsimp only [adaptiveRouter, StateT.run]
      by_cases hj : j ∈ r₁.corrupted
      · simp only [hj, ↓reduceIte]
        erw [pure_bind, pure_bind]
        exact hcont none r₁ r₁ ⟨rfl, hC⟩
      · simp only [hj, ↓reduceIte]
        erw [bind_assoc, bind_assoc]
        exact bind_congr fun ⟨out, s'⟩ => by
          erw [pure_bind, pure_bind]
          exact hcont out _ _ ⟨rfl, hC⟩

private theorem runFrom_subParty_bind_congr {γ : Type}
    (σ : AdaptiveProtocol n SubIn SubOut NQ NR View₁) (κ : ℕ)
    (prog : ProbOracleComp (partySpec n SubIn SubOut) γ)
    (sSub : AdaptiveRouterState (σ.machine κ).State View₁ n)
    (f g : γ × AdaptiveRouterState (σ.machine κ).State View₁ n → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a sSub', sSub'.corrupted = sSub.corrupted → f (a, sSub') = g (a, sSub')) :
    ((subPartyMachine σ κ).runFrom prog sSub >>= f) =
      ((subPartyMachine σ κ).runFrom prog sSub >>= g) := by
  refine Machine.runFrom_intertwine (subPartyMachine σ κ) (subPartyMachine σ κ)
    (fun _ => True) (fun r₁ r₂ => r₁ = r₂ ∧ r₁.corrupted = sSub.corrupted) prog
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    sSub sSub ⟨rfl, rfl⟩ f g (fun a r₁ _ hR => hR.1 ▸ hfg a r₁ hR.2)
    fun ⟨j, subX⟩ r₁ _ k₁ k₂ _ ⟨hEq, hC⟩ hcont => by
      subst hEq
      dsimp only [subPartyMachine, StateT.run]
      by_cases hj : j ∈ r₁.corrupted
      · simp only [hj, ↓reduceIte]
        exact hcont none r₁ r₁ ⟨rfl, hC⟩
      · simp only [hj, ↓reduceIte]
        erw [bind_assoc, bind_assoc]
        exact bind_congr fun ⟨out, s'⟩ =>
          hcont out _ _ ⟨rfl, by simpa [AdaptiveProtocol.recordSnapshot] using hC⟩

private theorem closeEval_runLiftSubParty_le {γ : Type}
    (mode : CorruptionMode) (φ : AdaptiveProtocol n SubIn SubOut NQ NR View₂) (κ : ℕ)
    (C₀ : Finset (Fin n)) (prog : ProbOracleComp (partySpec n SubIn SubOut) γ)
    (rφ rSub : AdaptiveRouterState (φ.machine κ).State View₂ n)
    (hR : RouterStateRel φ.memory rφ rSub)
    (f g : γ × AdaptiveRouterState (φ.machine κ).State View₂ n → ProbOracleComp OracleSpec.empty β)
    (y : β)
    (hfg : ∀ a rφ' rSub', RouterStateRel φ.memory rφ' rSub' →
      rφ'.corrupted = rφ.corrupted → rSub'.corrupted = rSub.corrupted →
      closeEval (f (a, rφ')) y ≤ closeEval (g (a, rSub')) y) :
    closeEval ((adaptiveRouter mode φ κ C₀).runFrom
        (liftSubParty (AdvQ := AdaptiveNetQ n SubIn NQ) (AdvR := AdaptiveNetR SubOut NR View₂)
          prog) rφ >>= f) y ≤
      closeEval ((subPartyMachine φ κ).runFrom prog rSub >>= g) y := by
  induction prog using OracleComp.induction generalizing rφ rSub with
  | pure a =>
    erw [liftSubParty, OracleComp.interpret_pure, Machine.runFrom_pure, Machine.runFrom_pure,
      pure_bind, pure_bind]
    exact hfg a rφ rSub hR rfl rfl
  | query_bind q _ ih =>
    simp only [PFunctor.FreeM.bind_eq_bind]
    rcases q with k | ⟨j, subX⟩
    · erw [liftSubParty, OracleComp.interpret_bind, OracleComp.interpret_query]
      dsimp only [sumHandler]
      have hq_inl : ∀ {ιE : Type} {E : ιE → Type} (M : Machine OracleSpec.empty E) (s : M.State),
          M.runFrom (OracleComp.query (spec := probOracleSpec E) (.inl k)) s =
            (fun a => (a, s)) <$> ProbOracleComp.sample (ProbComp.unifFin k) := by
        intro ιE E M s
        rw [Machine.runFrom, OracleComp.run_interpret_query, Machine.handler, sumHandler]
        exact (StateT.run_lift _ s).trans (bind_pure_comp _ _)
      conv_lhs => erw [Machine.runFrom_bind, hq_inl, bind_map_left, bind_assoc]
      conv_rhs => erw [Machine.runFrom_bind, hq_inl, bind_map_left, bind_assoc]
      refine closeEval_bind_le _ _ _ y fun k' => ?_
      exact ih k' rφ rSub hR hfg
    · erw [liftSubParty, OracleComp.interpret_bind, OracleComp.interpret_query]
      dsimp only [sumHandler]
      erw [Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_query]
      dsimp only [adaptiveRouter, subPartyMachine, StateT.run]
      by_cases hj : j ∈ rφ.corrupted
      · have hj' : j ∈ rSub.corrupted := hR.2.1 ▸ hj
        simp only [hj, hj', ↓reduceIte]
        erw [pure_bind, pure_bind]
        exact ih none rφ rSub hR hfg
      · have hj' : j ∉ rSub.corrupted := hR.2.1 ▸ hj
        simp only [hj, hj', ↓reduceIte]
        erw [hR.1]
        repeat erw [bind_assoc]
        refine closeEval_bind_le _ _ _ y fun ⟨out, s'⟩ => ?_
        erw [pure_bind, pure_bind]
        exact ih out _ _ (routerStateRel_recordSnapshot_adaptive φ κ hR s') hfg

open Classical in
private theorem eval_absorbAdaptiveHybridCheck_dummy (mode : CorruptionMode)
    (C₀ : ℕ → Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (π : AdaptiveProtocol n SubIn SubOut NQ NR View₁)
    (hρ_view : ρ.ViewStableOnCorrupt) (hπ_view : π.ViewStableOnCorrupt)
    (Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₁)))
    (target : Bool) (κ : ℕ) (z : List Bool) :
    (adaptiveExec mode π (adaptiveDummyAdversary C₀ _ _)
        (absorbAdaptiveHybridCheck mode C₀ ρ Z target) κ z).eval true =
      (adaptiveExec mode (composeAdaptive ρ π) (adaptiveDummyAdversary C₀ _ _) Z κ z).eval
        target := by
  rw [adaptiveExec_compose_dummy mode C₀ ρ π hρ_view hπ_view Z κ z]
  rw [adaptiveExec_dummyAdversary, adaptiveExec_dummyAdversary]
  dsimp only [absorbAdaptiveHybrid, Machine.run]
  have hprog :
      (adaptiveRouter mode π κ (C₀ κ)).link (absorbAdaptiveHybridCheck mode C₀ ρ Z target κ z) =
        (· == target) <$>
          (adaptiveRouter mode π κ (C₀ κ)).link
            ((absorbAdaptiveMachine mode (C₀ κ) ρ κ).link (Z κ z)) := by
    dsimp only [Machine.link, absorbAdaptiveHybridCheck]
    have hinitπ : (adaptiveRouter mode π κ (C₀ κ)).init = (do
        let s₀ ← (π.machine κ).init
        pure
          { inner := π.applyInitialCorruptions κ (C₀ κ) s₀
            corrupted := C₀ κ
            trace := fun i => [π.view κ i (π.applyInitialCorruptions κ (C₀ κ) s₀)] }) := rfl
    have hstatusπ : ∀ s, (adaptiveRouter mode π κ (C₀ κ)).handle (.inl .status) s =
        pure (s.corrupted, s) := fun _ => rfl
    rw [← bind_pure_comp (f := fun b => b == target), hinitπ]
    simp only [ProbOracleComp.sample_bind, bind_assoc]
    refine bind_congr fun sπ₀ => ?_
    erw [ProbOracleComp.sample_pure, pure_bind, pure_bind]
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [StateT.run]
    erw [hstatusπ]
    erw [pure_bind]
    erw [ite_eq_right_iff.mpr (fun h => absurd rfl h)]
    have hinitCheck :
        (absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁)
          mode (C₀ κ) ρ κ).init = (do
          let s₀ ← (ρ.machine κ).init
          pure
            { outer :=
                { inner := ρ.applyInitialCorruptions κ (C₀ κ) s₀
                  corrupted := C₀ κ
                  trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) s₀)] }
              desynced := false }) := rfl
    have hinitAbs :
        (absorbAdaptiveMachine (NQ := NQ) (NR := NR) (View₁ := View₁)
          mode (C₀ κ) ρ κ).init = (do
          let s₀ ← (ρ.machine κ).init
          pure
            { inner := ρ.applyInitialCorruptions κ (C₀ κ) s₀
              corrupted := C₀ κ
              trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) s₀)] }) := rfl
    erw [Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_sample,
      Machine.runFrom_sample, bind_map_left, bind_map_left, bind_map_left,
      map_bind, bind_assoc]
    rw [hinitCheck, hinitAbs]
    erw [ProbOracleComp.sample_bind, ProbOracleComp.sample_bind, bind_assoc, bind_assoc]
    refine bind_congr (m := ProbOracleComp _) fun sρ₀ => ?_
    erw [ProbOracleComp.sample_pure, ProbOracleComp.sample_pure, pure_bind, pure_bind]
    have hfst : ∀ {α β : Type} (x : α) (y : β), (x, y).1 = x := fun _ _ => rfl
    have hsnd : ∀ {α β : Type} (x : α) (y : β), (x, y).2 = y := fun _ _ => rfl
    repeat erw [hfst]
    repeat erw [hsnd]
    erw [Machine.runFrom_bind, map_bind]
    have hcomp1 :
        ((adaptiveRouter mode π κ (C₀ κ)).runFrom
            ((absorbAdaptiveCheckMachine mode (C₀ κ) ρ κ).runFrom (Z κ z)
              { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                           corrupted := C₀ κ
                           trace := fun i =>
                             [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] }
                desynced := false })
            { inner := π.applyInitialCorruptions κ (C₀ κ) sπ₀
              corrupted := C₀ κ
              trace := fun i => [π.view κ i (π.applyInitialCorruptions κ (C₀ κ) sπ₀)] } >>=
          fun x =>
            Prod.fst <$> (adaptiveRouter mode π κ (C₀ κ)).runFrom
              (pure (!x.1.2.desynced && (x.1.1 == target))) x.2) =
        ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode (C₀ κ) ρ κ).comp
            (adaptiveRouter mode π κ (C₀ κ))).runFrom (Z κ z)
          ({ outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                        corrupted := C₀ κ
                        trace := fun i =>
                          [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] }
             desynced := false },
           { inner := π.applyInitialCorruptions κ (C₀ κ) sπ₀
             corrupted := C₀ κ
             trace := fun i => [π.view κ i (π.applyInitialCorruptions κ (C₀ κ) sπ₀)] }) >>=
          fun x => pure (!x.2.1.desynced && (x.1 == target)) := by
      erw [Machine.runFrom_comp, bind_map_left]
      exact bind_congr fun ⟨⟨b, sC⟩, rπ⟩ => by erw [Machine.runFrom_pure, map_pure]; rfl
    have hcomp2 :
        ((adaptiveRouter mode π κ (C₀ κ)).runFrom
            (Prod.fst <$> (absorbAdaptiveMachine mode (C₀ κ) ρ κ).runFrom (Z κ z)
              { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                corrupted := C₀ κ
                trace := fun i =>
                  [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] })
            { inner := π.applyInitialCorruptions κ (C₀ κ) sπ₀
              corrupted := C₀ κ
              trace := fun i => [π.view κ i (π.applyInitialCorruptions κ (C₀ κ) sπ₀)] } >>=
          fun a => pure (a.1 == target)) =
        ((absorbAdaptiveMachine (NQ := NQ) (NR := NR) (View₁ := View₁) mode (C₀ κ) ρ κ).comp
            (adaptiveRouter mode π κ (C₀ κ))).runFrom (Z κ z)
          ({ inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
             corrupted := C₀ κ
             trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] },
           { inner := π.applyInitialCorruptions κ (C₀ κ) sπ₀
             corrupted := C₀ κ
             trace := fun i => [π.view κ i (π.applyInitialCorruptions κ (C₀ κ) sπ₀)] }) >>=
          fun x => pure (x.1 == target) := by
      erw [Machine.runFrom_comp, Machine.runFrom_map, bind_map_left, bind_map_left]
      rfl
    erw [hcomp1, hcomp2]
    let R :
        ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁)
            mode (C₀ κ) ρ κ).comp (adaptiveRouter mode π κ (C₀ κ))).State →
        ((absorbAdaptiveMachine (NQ := NQ) (NR := NR) (View₁ := View₁)
            mode (C₀ κ) ρ κ).comp (adaptiveRouter mode π κ (C₀ κ))).State → Prop :=
      fun s₁ s₂ =>
        s₁.1.desynced = false ∧ s₁.1.outer = s₂.1 ∧ s₁.2 = s₂.2 ∧
        s₁.2.corrupted = s₁.1.outer.corrupted
    refine Machine.runFrom_intertwine
      ((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁)
          mode (C₀ κ) ρ κ).comp (adaptiveRouter mode π κ (C₀ κ)))
      ((absorbAdaptiveMachine (NQ := NQ) (NR := NR) (View₁ := View₁)
          mode (C₀ κ) ρ κ).comp (adaptiveRouter mode π κ (C₀ κ)))
      (fun _ => True) R (Z κ z)
      (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
      _ _ ⟨rfl, rfl, rfl, rfl⟩
      (fun x => pure (!x.2.1.desynced && (x.1 == target)))
      (fun x => pure (x.1 == target))
      (fun a s₁ s₂ hR => by simp [hR.1])
      fun q ⟨s₁, rπ₁⟩ ⟨s₂, rπ₂⟩ k₁ k₂ _ ⟨hdes, ho, hr, hc⟩ hcont => ?_
    dsimp only at hdes ho hr hc
    subst ho; subst hr
    rcases q with (⟨i, x⟩ | _) | (⟨i, x⟩ | i | (q | (⟨j, subX⟩ | nq)))
    · dsimp only [Machine.comp, absorbAdaptiveCheckMachine, absorbAdaptiveMachine, StateT.run]
      by_cases hi : i ∈ s₁.outer.corrupted
      · simp only [hi, ↓reduceIte, Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply]
        exact hcont none _ _ ⟨hdes, rfl, rfl, hc⟩
      · simp only [hi, ↓reduceIte]
        erw [bind_map_left, bind_map_left, Machine.runFrom_bind, Machine.runFrom_bind,
          bind_assoc, bind_assoc]
        refine runFrom_adaptiveRouter_liftSubParty_bind_congr mode π κ (C₀ κ) _ rπ₁ _ _
          fun ⟨out, s'⟩ rπ' hC => by
            erw [Machine.runFrom_pure, pure_bind, pure_bind, Equiv.prodAssoc_apply]
            exact hcont out _ _ ⟨hdes, rfl, rfl, hC.trans hc⟩
    · dsimp only [Machine.comp, absorbAdaptiveCheckMachine, absorbAdaptiveMachine, StateT.run]
      erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
      exact hcont s₁.outer.corrupted _ _ ⟨hdes, rfl, rfl, hc⟩
    · dsimp only [Machine.comp, absorbAdaptiveCheckMachine, absorbAdaptiveMachine, StateT.run]
      by_cases hi : i ∈ s₁.outer.corrupted
      · simp only [hi, ↓reduceIte]
        erw [bind_map_left, bind_map_left, Machine.runFrom_bind, Machine.runFrom_bind,
          bind_assoc, bind_assoc]
        refine runFrom_adaptiveRouter_liftSubParty_bind_congr mode π κ (C₀ κ) _ rπ₁ _ _
          fun ⟨out, s'⟩ rπ' hC => by
            erw [Machine.runFrom_pure, pure_bind, pure_bind, Equiv.prodAssoc_apply]
            exact hcont (.party out) _ _ ⟨hdes, rfl, rfl, hC.trans hc⟩
      · simp only [hi, ↓reduceIte, Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply]
        exact hcont (.party none) _ _ ⟨hdes, rfl, rfl, hc⟩
    · dsimp only [Machine.comp, absorbAdaptiveCheckMachine, absorbAdaptiveMachine, StateT.run]
      cases mode
      · by_cases hi : i ∈ s₁.outer.corrupted
        · simp only [hi, ↓reduceIte]
          erw [bind_map_left, bind_map_left, Machine.runFrom_bind, Machine.runFrom_query,
            Machine.runFrom_bind, Machine.runFrom_query]
          dsimp only [adaptiveRouter, StateT.run]
          have hiπ : i ∈ rπ₁.corrupted := hc ▸ hi
          simp only [hiπ, ↓reduceIte]
          repeat erw [pure_bind]
          erw [Equiv.prodAssoc_apply]
          have hfst : ∀ {α β : Type} (x : α) (y : β), (x, y).1 = x := fun _ _ => rfl
          have hsnd : ∀ {α β : Type} (x : α) (y : β), (x, y).2 = y := fun _ _ => rfl
          repeat erw [hfst]
          repeat erw [hsnd]
          erw [hc]
          exact hcont _ _ _
            ⟨by erw [hdes, Bool.false_or]; exact decide_eq_false (not_not.mpr rfl), rfl, rfl, hc⟩
        · simp only [hi, ↓reduceIte, Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply]
          exact hcont (.corrupt none) _ _ ⟨hdes, rfl, rfl, hc⟩
      · erw [bind_map_left, bind_map_left, Machine.runFrom_bind, Machine.runFrom_query,
          Machine.runFrom_bind, Machine.runFrom_query]
        dsimp only [adaptiveRouter, StateT.run]
        by_cases hi : i ∈ s₁.outer.corrupted
        · have hiπ : i ∈ rπ₁.corrupted := hc ▸ hi
          simp only [hi, hiπ, ↓reduceIte]
          repeat erw [pure_bind]
          erw [Equiv.prodAssoc_apply]
          have hfst : ∀ {α β : Type} (x : α) (y : β), (x, y).1 = x := fun _ _ => rfl
          have hsnd : ∀ {α β : Type} (x : α) (y : β), (x, y).2 = y := fun _ _ => rfl
          repeat erw [hfst]
          repeat erw [hsnd]
          erw [hc]
          exact hcont _ _ _
            ⟨by erw [hdes, Bool.false_or]; exact decide_eq_false (not_not.mpr rfl), rfl, rfl, hc⟩
        · have hiπ : i ∉ rπ₁.corrupted := hc ▸ hi
          simp only [hi, hiπ, ↓reduceIte]
          repeat erw [pure_bind]
          erw [Equiv.prodAssoc_apply]
          have hfst : ∀ {α β : Type} (x : α) (y : β), (x, y).1 = x := fun _ _ => rfl
          have hsnd : ∀ {α β : Type} (x : α) (y : β), (x, y).2 = y := fun _ _ => rfl
          repeat erw [hfst]
          repeat erw [hsnd]
          erw [hc]
          exact hcont _ _ _
            ⟨by erw [hdes, Bool.false_or]; exact decide_eq_false (not_not.mpr rfl), rfl, rfl, rfl⟩
    · dsimp only [Machine.comp, absorbAdaptiveCheckMachine, absorbAdaptiveMachine, StateT.run]
      erw [bind_map_left, bind_map_left, Machine.runFrom_bind, Machine.runFrom_bind,
        bind_assoc, bind_assoc]
      refine runFrom_adaptiveRouter_liftSubParty_bind_congr mode π κ (C₀ κ) _ rπ₁ _ _
        fun ⟨r, s'⟩ rπ' hC => by
          erw [Machine.runFrom_pure, pure_bind, pure_bind, Equiv.prodAssoc_apply]
          exact hcont (.net (.inl r)) _ _ ⟨hdes, rfl, rfl, hC.trans hc⟩
    · dsimp only [Machine.comp, absorbAdaptiveCheckMachine, absorbAdaptiveMachine, StateT.run]
      erw [bind_map_left, bind_map_left, Machine.runFrom_bind, Machine.runFrom_query,
        Machine.runFrom_bind, Machine.runFrom_map, Machine.runFrom_query]
      dsimp only [adaptiveRouter, StateT.run]
      have hfst : ∀ {α β : Type} (x : α) (y : β), (x, y).1 = x := fun _ _ => rfl
      have hsnd : ∀ {α β : Type} (x : α) (y : β), (x, y).2 = y := fun _ _ => rfl
      have hpmap : ∀ {α β γ : Type} (f : α → γ) (x : α) (y : β),
          Prod.map f id (x, y) = (f x, y) := fun _ _ _ => rfl
      by_cases hj : j ∈ rπ₁.corrupted
      · simp only [hj, ↓reduceIte]
        erw [bind_map_left]
        repeat erw [bind_assoc]
        refine bind_congr fun ⟨out, s'⟩ => ?_
        repeat erw [pure_bind]
        erw [Equiv.prodAssoc_apply, hpmap]
        repeat erw [hfst]
        repeat erw [hsnd]
        erw [hc]
        exact hcont (.net (.inr (subNetReplyToRouted (.party out)))) _ _
          ⟨by erw [hdes, Bool.false_or]; exact decide_eq_false (not_not.mpr rfl), rfl, rfl, rfl⟩
      · simp only [hj, ↓reduceIte]
        erw [bind_map_left]
        repeat erw [pure_bind]
        erw [Equiv.prodAssoc_apply, hpmap]
        repeat erw [hfst]
        repeat erw [hsnd]
        erw [hc]
        exact hcont (.net (.inr (subNetReplyToRouted (.party none)))) _ _
          ⟨by erw [hdes, Bool.false_or]; exact decide_eq_false (not_not.mpr rfl), rfl, rfl, hc⟩
    · dsimp only [Machine.comp, absorbAdaptiveCheckMachine, absorbAdaptiveMachine, StateT.run]
      erw [bind_map_left, bind_map_left, Machine.runFrom_bind, Machine.runFrom_query,
        Machine.runFrom_bind, Machine.runFrom_map, Machine.runFrom_query]
      dsimp only [adaptiveRouter, StateT.run]
      have hfst : ∀ {α β : Type} (x : α) (y : β), (x, y).1 = x := fun _ _ => rfl
      have hsnd : ∀ {α β : Type} (x : α) (y : β), (x, y).2 = y := fun _ _ => rfl
      have hpmap : ∀ {α β γ : Type} (f : α → γ) (x : α) (y : β),
          Prod.map f id (x, y) = (f x, y) := fun _ _ _ => rfl
      erw [bind_map_left]
      repeat erw [bind_assoc]
      refine bind_congr fun ⟨r, s'⟩ => ?_
      repeat erw [pure_bind]
      erw [Equiv.prodAssoc_apply, hpmap]
      repeat erw [hfst]
      repeat erw [hsnd]
      erw [hc]
      exact hcont (.net (.inr (subNetReplyToRouted (.net r)))) _ _
        ⟨by erw [hdes, Bool.false_or]; exact decide_eq_false (not_not.mpr rfl), rfl, rfl, rfl⟩
  rw [hprog, Machine.closeProgram_map, ProbComp.eval_map, PMF.map_apply]
  rw [tsum_fintype, Fintype.sum_bool]
  cases target <;> simp

private def simSubHandler (_mode : CorruptionMode) (expectedC : Finset (Fin n)) :
    (q : AdaptiveNetQ n SubIn NQ₂) →
      ProbOracleComp
        (adaptiveProtocolSpec n In Out (NetQ ⊕ RoutedNetQ n SubIn NQ₂)
          (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂))
        (AdaptiveNetR SubOut NR₂ View₂)
  | .party j subX =>
      toSubPartyReply <$> ProbOracleComp.query (spec :=
        adaptiveProtocolSpec n In Out (NetQ ⊕ RoutedNetQ n SubIn NQ₂)
          (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂))
        (.inr (.net (.inr (.inl (j, subX)))))
  | .net nq =>
      toSubNetReply <$> ProbOracleComp.query (spec :=
        adaptiveProtocolSpec n In Out (NetQ ⊕ RoutedNetQ n SubIn NQ₂)
          (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂))
        (.inr (.net (.inr (.inr nq))))
  | .corrupt j =>
      if j ∈ expectedC then
        toSubCorruptReply <$> ProbOracleComp.query (spec :=
          adaptiveProtocolSpec n In Out (NetQ ⊕ RoutedNetQ n SubIn NQ₂)
            (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂))
          (.inr (.corrupt j))
      else pure (.corrupt none)

private theorem liftAdaptiveNet_liftSimSubNet (mode : CorruptionMode) (expectedC : Finset (Fin n))
    {γ : Type}
    (prog :
      ProbOracleComp (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂)) γ) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out)
        (liftSimSubNet (NetQ := NetQ) (NetR := NetR) (Viewρ := Viewρ) mode expectedC prog) =
      OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query (spec := probOracleSpec
            (adaptiveProtocolSpec n In Out (NetQ ⊕ RoutedNetQ n SubIn NQ₂)
              (NetR ⊕ RoutedNetR SubOut NR₂) (AdaptiveHybridView Viewρ View₂))) (.inl k))
          (simSubHandler (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
            (Viewρ := Viewρ) mode expectedC))
        prog := by
  dsimp only [liftAdaptiveNet, Machine.liftRightProgram, liftSimSubNet]
  erw [OracleComp.interpret_interpret]
  congr 1 with q
  rcases q with k | (⟨j, subX⟩ | j | nq)
  · rfl
  · simp only [sumHandler, OracleComp.interpret_map, ProbOracleComp.interpret_query, simSubHandler]
  · dsimp only [sumHandler, simSubHandler]
    cases mode <;> split_ifs
    · simp only [OracleComp.interpret_map, ProbOracleComp.interpret_query]
    · rfl
    · simp only [OracleComp.interpret_map, ProbOracleComp.interpret_query]
    · rfl
  · simp only [sumHandler, OracleComp.interpret_map, ProbOracleComp.interpret_query, simSubHandler]

private theorem closeEval_runSubNet_le {γ : Type} (mode : CorruptionMode)
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (φ : AdaptiveProtocol n SubIn SubOut NQ₂ NR₂ View₂) (κ : ℕ)
    (C₀ expectedC targetC : Finset (Fin n))
    (hsub : expectedC ⊆ targetC) (hstat : mode = .static → targetC = expectedC)
    (OuterRel : Finset (Fin n) → AdaptiveRouterState (ρ.machine κ).State Viewρ n → Prop)
    (hOuter_corrupt : ∀ C rO j, expectedC ⊆ C → C ⊆ targetC → j ∈ targetC → j ∉ C →
      OuterRel C rO →
      OuterRel (insert j C)
        { inner := ρ.onCorrupt κ j rO.inner
          corrupted := insert j rO.corrupted
          trace := rO.trace })
    (prog :
      ProbOracleComp (netSpec (AdaptiveNetQ n SubIn NQ₂) (AdaptiveNetR SubOut NR₂ View₂)) γ)
    (rφ : AdaptiveRouterState (φ.machine κ).State View₂ n)
    (rComp : AdaptiveRouterState
      (AdaptiveComposeState (ρ.machine κ).State Viewρ (φ.machine κ).State View₂ n)
      (AdaptiveHybridView Viewρ View₂) n)
    (hinit : RouterStateRel φ.memory rφ rComp.inner.sub ∧ rφ.corrupted = expectedC ∧
      rComp.corrupted = expectedC ∧ rComp.inner.outer.corrupted = expectedC ∧
      rComp.inner.sub.corrupted = expectedC ∧ OuterRel expectedC rComp.inner.outer)
    (f : γ × AdaptiveRouterState (φ.machine κ).State View₂ n → ProbOracleComp OracleSpec.empty β)
    (g : γ × AdaptiveRouterState
        (AdaptiveComposeState (ρ.machine κ).State Viewρ (φ.machine κ).State View₂ n)
        (AdaptiveHybridView Viewρ View₂) n → ProbOracleComp OracleSpec.empty β)
    (y : β)
    (hfg : ∀ a rφ' rComp',
      RouterStateRel φ.memory rφ' rComp'.inner.sub →
      rφ'.corrupted = targetC → rComp'.corrupted = targetC →
      rComp'.inner.outer.corrupted = targetC → rComp'.inner.sub.corrupted = targetC →
      OuterRel targetC rComp'.inner.outer →
      closeEval (f (a, rφ')) y ≤ closeEval (g (a, rComp')) y)
    (hf_bad : ∀ a rφ', rφ'.corrupted ≠ targetC → closeEval (f (a, rφ')) y = 0) :
    closeEval ((adaptiveRouter mode φ κ C₀).runFrom (liftAdaptiveNet prog) rφ >>= f) y ≤
      closeEval ((adaptiveRouter mode (composeAdaptive ρ φ) κ C₀).runFrom
        (liftAdaptiveNet (liftSimSubNet mode targetC prog)) rComp >>= g) y := by
  rw [liftAdaptiveNet_liftSimSubNet]
  let R : AdaptiveRouterState (φ.machine κ).State View₂ n →
      AdaptiveRouterState
        (AdaptiveComposeState (ρ.machine κ).State Viewρ (φ.machine κ).State View₂ n)
        (AdaptiveHybridView Viewρ View₂) n → Prop :=
    fun r₁ r₂ =>
      RouterStateRel φ.memory r₁ r₂.inner.sub ∧
      r₁.corrupted = r₂.corrupted ∧
      r₂.inner.outer.corrupted = r₂.corrupted ∧
      r₂.inner.sub.corrupted = r₂.corrupted ∧
      expectedC ⊆ r₁.corrupted ∧
      r₁.corrupted ⊆ targetC ∧
      OuterRel r₁.corrupted r₂.inner.outer
  let Trap : AdaptiveRouterState (φ.machine κ).State View₂ n → Prop :=
    fun r₁ => ¬ (r₁.corrupted ⊆ targetC)
  have hR_init : R rφ rComp :=
    ⟨hinit.1, hinit.2.1.trans hinit.2.2.1.symm,
     hinit.2.2.2.1.trans hinit.2.2.1.symm,
     hinit.2.2.2.2.1.trans hinit.2.2.1.symm,
     hinit.2.1 ▸ Finset.Subset.rfl, hinit.2.1 ▸ hsub, hinit.2.1 ▸ hinit.2.2.2.2.2⟩
  refine Machine.closeEval_runFrom_interpret_le_intertwine
    (adaptiveRouter mode φ κ C₀) (adaptiveRouter mode (composeAdaptive ρ φ) κ C₀)
    (fun q => ProbOracleComp.query (spec := adaptiveProtocolSpec n SubIn SubOut NQ₂ NR₂ View₂)
      (.inr q))
    (simSubHandler mode targetC)
    (fun _ => True) R Trap prog
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    rφ rComp hR_init f g y ?_ ?_ ?_ ?_
  · intro a r₁ r₂ hR
    by_cases heq : r₁.corrupted = targetC
    · exact hfg a r₁ r₂ hR.1 heq (hR.2.1 ▸ heq) (hR.2.2.1 ▸ hR.2.1 ▸ heq)
        (hR.2.2.2.1 ▸ hR.2.1 ▸ heq) (heq ▸ hR.2.2.2.2.2.2)
    · have h0 : closeEval (f (a, r₁)) y = 0 := hf_bad a r₁ heq
      erw [h0]; exact zero_le
  · intro a r₁ hT
    exact hf_bad a r₁ fun heq => hT (heq ▸ Finset.Subset.rfl)
  · intro q r₁ z _ hT hz
    rcases q with ⟨j, subX⟩ | j | nq
    · erw [Machine.runFrom_query] at hz
      dsimp only [adaptiveRouter, StateT.run] at hz
      by_cases hj : j ∈ r₁.corrupted
      · simp only [hj, ↓reduceIte] at hz
        rcases mem_support_closeEval_bind.mp hz with ⟨⟨_, _⟩, _, hz'⟩
        rcases mem_support_closeEval_pure.mp hz' with rfl; exact hT
      · simp only [hj, ↓reduceIte] at hz
        rcases mem_support_closeEval_pure.mp hz with rfl; exact hT
    · erw [Machine.runFrom_query] at hz
      dsimp only [adaptiveRouter, StateT.run] at hz
      cases mode
      · by_cases hj : j ∈ r₁.corrupted <;> simp only [hj, ↓reduceIte] at hz <;>
          rcases mem_support_closeEval_pure.mp hz with rfl <;> exact hT
      · by_cases hj : j ∈ r₁.corrupted
        · simp only [hj, ↓reduceIte] at hz
          rcases mem_support_closeEval_pure.mp hz with rfl; exact hT
        · simp only [hj, ↓reduceIte] at hz
          rcases mem_support_closeEval_pure.mp hz with rfl
          exact fun hsub' => hT ((Finset.subset_insert _ _).trans hsub')
    · erw [Machine.runFrom_query] at hz
      dsimp only [adaptiveRouter, StateT.run] at hz
      rcases mem_support_closeEval_bind.mp hz with ⟨⟨_, _⟩, _, hz'⟩
      rcases mem_support_closeEval_pure.mp hz' with rfl; exact hT
  · intro q r₁ r₂ k₁ k₂ _ ⟨hS, hc, hcO, hcS, hE, hTsub, hOrel⟩ hcont htrap
    rcases q with ⟨j, subX⟩ | j | nq
    · dsimp only [simSubHandler]
      erw [Machine.runFrom_query, Machine.runFrom_map, Machine.runFrom_query]
      dsimp only [adaptiveRouter, composeAdaptive, StateT.run]
      by_cases hj : j ∈ r₁.corrupted
      · have hjS : j ∈ r₂.inner.sub.corrupted := hcS ▸ hc ▸ hj
        simp only [hj, hjS, ↓reduceIte]
        erw [hS.1, bind_map_left, bind_assoc, bind_assoc, bind_assoc]
        refine closeEval_bind_le _ _ _ y fun ⟨out, s'⟩ => ?_
        erw [pure_bind, pure_bind, pure_bind]
        exact hcont (.party out) _ _
          ⟨routerStateRel_recordSnapshot_adaptive φ κ hS s', hc, hcO, hcS, hE, hTsub, hOrel⟩
      · have hjS : j ∉ r₂.inner.sub.corrupted := hcS ▸ hc ▸ hj
        simp only [hj, hjS, ↓reduceIte]
        erw [bind_map_left, pure_bind, pure_bind]
        dsimp only [Prod.map, toSubPartyReply, id, AdaptiveProtocol.recordSnapshot, composeAdaptive]
        exact hcont (.party none) r₁ _ ⟨hS, hc, hcO, hcS, hE, hTsub, hOrel⟩
    · dsimp only [simSubHandler]
      cases mode
      · have hC : targetC = expectedC := hstat rfl
        have hr₁ : r₁.corrupted = expectedC := Finset.Subset.antisymm (hC ▸ hTsub) hE
        by_cases hjT : j ∈ targetC
        · have hj₁ : j ∈ r₁.corrupted := hr₁ ▸ hC ▸ hjT
          have hj₂ : j ∈ r₂.corrupted := hc ▸ hj₁
          simp only [hjT, ↓reduceIte]
          erw [Machine.runFrom_query, Machine.runFrom_map, Machine.runFrom_query]
          dsimp only [adaptiveRouter, composeAdaptive, StateT.run]
          simp only [hj₁, hj₂, ↓reduceIte]
          erw [bind_map_left, pure_bind, pure_bind]
          rw [routerStateRel_corruptionReport_adaptive φ κ j hS]
          exact hcont _ r₁ r₂ ⟨hS, hc, hcO, hcS, hE, hTsub, hOrel⟩
        · have hj₁ : j ∉ r₁.corrupted := fun h => hjT (hTsub h)
          simp only [hjT, ↓reduceIte]
          erw [Machine.runFrom_query, Machine.runFrom_pure]
          dsimp only [adaptiveRouter, StateT.run]
          simp only [hj₁, ↓reduceIte]
          erw [pure_bind, pure_bind]
          exact hcont (.corrupt none) r₁ r₂ ⟨hS, hc, hcO, hcS, hE, hTsub, hOrel⟩
      · by_cases hjT : j ∈ targetC
        · simp only [hjT, ↓reduceIte]
          erw [Machine.runFrom_query, Machine.runFrom_map, Machine.runFrom_query]
          dsimp only [adaptiveRouter, composeAdaptive, StateT.run]
          erw [bind_map_left]
          by_cases hj₁ : j ∈ r₁.corrupted
          · have hj₂ : j ∈ r₂.corrupted := hc ▸ hj₁
            simp only [hj₁, hj₂, ↓reduceIte]
            erw [pure_bind, pure_bind]
            rw [routerStateRel_corruptionReport_adaptive φ κ j hS]
            exact hcont _ r₁ r₂ ⟨hS, hc, hcO, hcS, hE, hTsub, hOrel⟩
          · have hj₂ : j ∉ r₂.corrupted := hc ▸ hj₁
            have hjO : j ∉ r₂.inner.outer.corrupted := hcO ▸ hj₂
            have hjS : j ∉ r₂.inner.sub.corrupted := hcS ▸ hj₂
            simp only [hj₁, hj₂, hjO, hjS, ↓reduceIte]
            erw [pure_bind, pure_bind]
            have hS' : RouterStateRel φ.memory
                { inner := φ.onCorrupt κ j r₁.inner
                  corrupted := insert j r₁.corrupted
                  trace := r₁.trace }
                { inner := φ.onCorrupt κ j r₂.inner.sub.inner
                  corrupted := insert j r₂.inner.sub.corrupted
                  trace := r₂.inner.sub.trace } :=
              ⟨by rw [hS.1], by rw [hS.2.1], fun hne => hS.2.2 hne⟩
            rw [routerStateRel_corruptionReport_adaptive φ κ j hS']
            exact hcont _ _ _
              ⟨hS', by dsimp only [id]; erw [hc], by dsimp only [id]; erw [hcO],
               by dsimp only [id]; erw [hcS],
               hE.trans (Finset.subset_insert _ _), Finset.insert_subset hjT hTsub,
               hOuter_corrupt r₁.corrupted r₂.inner.outer j hE hTsub hjT hj₁ hOrel⟩
        · simp only [hjT, ↓reduceIte]
          erw [Machine.runFrom_query, Machine.runFrom_pure]
          dsimp only [adaptiveRouter, StateT.run]
          have hj₁ : j ∉ r₁.corrupted := fun h => hjT (hTsub h)
          simp only [hj₁, ↓reduceIte]
          erw [pure_bind, pure_bind]
          erw [htrap _ _ fun hsub' => hjT (hsub' (Finset.mem_insert_self j r₁.corrupted))]
          exact zero_le
    · dsimp only [simSubHandler]
      erw [Machine.runFrom_query, Machine.runFrom_map, Machine.runFrom_query]
      dsimp only [adaptiveRouter, composeAdaptive, StateT.run]
      erw [hS.1, bind_map_left, bind_assoc, bind_assoc, bind_assoc]
      refine closeEval_bind_le _ _ _ y fun ⟨r, s'⟩ => ?_
      erw [pure_bind, pure_bind, pure_bind]
      exact hcont (.net r) _ _
        ⟨routerStateRel_recordSnapshot_adaptive φ κ hS s', hc, hcO, hcS, hE, hTsub, hOrel⟩

open Classical in
private theorem absorbAdaptiveCheckMachine_desynced_preserved {NQ NR View₁ : Type}
    (B : Machine OracleSpec.empty
      (adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ) (AdaptiveNetR SubOut NR View₁)))
    (mode : CorruptionMode) (C₀ : Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ) (κ : ℕ)
    (q : AdaptivePartyQ n In ⊕ AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
    (s₁ : AbsorbCheckState (ρ.machine κ).State Viewρ n × B.State)
    (hT : s₁.1.desynced = true)
    {z' : (adaptiveExecSpec n In Out (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR) (AdaptiveHybridView Viewρ View₁)) q) ×
      (AbsorbCheckState (ρ.machine κ).State Viewρ n × B.State)}
    (hz : z' ∈ (closeEval ((((absorbAdaptiveCheckMachine (NQ := NQ) (NR := NR) (View₁ := View₁)
      mode C₀ ρ κ).comp B).handle q).run s₁)).support) :
    z'.2.1.desynced = true := by
  dsimp only [Machine.comp, StateT.run] at hz
  erw [mem_support_closeEval_map] at hz
  rcases hz with ⟨⟨⟨res, sA'⟩, sB'⟩, hrun, rfl⟩
  erw [Equiv.prodAssoc_apply]
  rcases q with (⟨i, x⟩ | _) | (⟨i, x⟩ | i | (q | (⟨j, subX⟩ | nq)))
  · dsimp only [absorbAdaptiveCheckMachine, StateT.run] at hrun
    by_cases hi : i ∈ s₁.1.outer.corrupted
    · simp only [hi, ↓reduceIte, Machine.runFrom_pure] at hrun
      rcases mem_support_closeEval_pure.mp hrun with hEq
      have : sA' = s₁.1 := congrArg (fun p => p.1.2) hEq
      exact this ▸ hT
    · simp only [hi, ↓reduceIte] at hrun
      erw [Machine.runFrom_bind] at hrun
      rcases mem_support_closeEval_bind.mp hrun with ⟨a, _, hrun'⟩
      erw [Machine.runFrom_pure] at hrun'
      rcases mem_support_closeEval_pure.mp hrun' with hEq
      have : sA'.desynced = s₁.1.desynced := congrArg (fun p => p.1.2.desynced) hEq
      exact this ▸ hT
  · dsimp only [absorbAdaptiveCheckMachine, StateT.run] at hrun
    erw [Machine.runFrom_pure] at hrun
    rcases mem_support_closeEval_pure.mp hrun with hEq
    have : sA' = s₁.1 := congrArg (fun p => p.1.2) hEq
    exact this ▸ hT
  · dsimp only [absorbAdaptiveCheckMachine, StateT.run] at hrun
    by_cases hi : i ∈ s₁.1.outer.corrupted
    · simp only [hi, ↓reduceIte] at hrun
      erw [Machine.runFrom_bind] at hrun
      rcases mem_support_closeEval_bind.mp hrun with ⟨a, _, hrun'⟩
      erw [Machine.runFrom_pure] at hrun'
      rcases mem_support_closeEval_pure.mp hrun' with hEq
      have : sA'.desynced = s₁.1.desynced := congrArg (fun p => p.1.2.desynced) hEq
      exact this ▸ hT
    · simp only [hi, ↓reduceIte, Machine.runFrom_pure] at hrun
      rcases mem_support_closeEval_pure.mp hrun with hEq
      have : sA' = s₁.1 := congrArg (fun p => p.1.2) hEq
      exact this ▸ hT
  · dsimp only [absorbAdaptiveCheckMachine, StateT.run] at hrun
    cases mode
    · by_cases hi : i ∈ s₁.1.outer.corrupted
      · simp only [hi, ↓reduceIte] at hrun
        erw [Machine.runFrom_bind] at hrun
        rcases mem_support_closeEval_bind.mp hrun with ⟨a₁, _, hrun₁⟩
        erw [Machine.runFrom_bind] at hrun₁
        rcases mem_support_closeEval_bind.mp hrun₁ with ⟨a₂, _, hrun₂⟩
        erw [Machine.runFrom_pure] at hrun₂
        rcases mem_support_closeEval_pure.mp hrun₂ with hEq
        have hdes : sA'.desynced = (s₁.1.desynced || decide (a₂.1 ≠ s₁.1.outer.corrupted)) :=
          congrArg (fun p => p.1.2.desynced) hEq
        rw [hT, Bool.true_or] at hdes; exact hdes
      · simp only [hi, ↓reduceIte, Machine.runFrom_pure] at hrun
        rcases mem_support_closeEval_pure.mp hrun with hEq
        have : sA' = s₁.1 := congrArg (fun p => p.1.2) hEq
        exact this ▸ hT
    · erw [Machine.runFrom_bind] at hrun
      rcases mem_support_closeEval_bind.mp hrun with ⟨a₁, _, hrun₁⟩
      erw [Machine.runFrom_bind] at hrun₁
      rcases mem_support_closeEval_bind.mp hrun₁ with ⟨a₂, _, hrun₂⟩
      erw [Machine.runFrom_pure] at hrun₂
      rcases mem_support_closeEval_pure.mp hrun₂ with hEq
      have hdes : sA'.desynced = (s₁.1.desynced || _) :=
        congrArg (fun p => p.1.2.desynced) hEq
      rw [hT, Bool.true_or] at hdes; exact hdes
  · dsimp only [absorbAdaptiveCheckMachine, StateT.run] at hrun
    erw [Machine.runFrom_bind] at hrun
    rcases mem_support_closeEval_bind.mp hrun with ⟨a, _, hrun'⟩
    erw [Machine.runFrom_pure] at hrun'
    rcases mem_support_closeEval_pure.mp hrun' with hEq
    have : sA'.desynced = s₁.1.desynced := congrArg (fun p => p.1.2.desynced) hEq
    exact this ▸ hT
  · dsimp only [absorbAdaptiveCheckMachine, StateT.run] at hrun
    erw [Machine.runFrom_bind] at hrun
    rcases mem_support_closeEval_bind.mp hrun with ⟨a₁, _, hrun₁⟩
    erw [Machine.runFrom_bind] at hrun₁
    rcases mem_support_closeEval_bind.mp hrun₁ with ⟨a₂, _, hrun₂⟩
    erw [Machine.runFrom_pure] at hrun₂
    rcases mem_support_closeEval_pure.mp hrun₂ with hEq
    have hdes : sA'.desynced = (s₁.1.desynced || decide (a₂.1 ≠ s₁.1.outer.corrupted)) :=
      congrArg (fun p => p.1.2.desynced) hEq
    rw [hT, Bool.true_or] at hdes; exact hdes
  · dsimp only [absorbAdaptiveCheckMachine, StateT.run] at hrun
    erw [Machine.runFrom_bind] at hrun
    rcases mem_support_closeEval_bind.mp hrun with ⟨a₁, _, hrun₁⟩
    erw [Machine.runFrom_bind] at hrun₁
    rcases mem_support_closeEval_bind.mp hrun₁ with ⟨a₂, _, hrun₂⟩
    erw [Machine.runFrom_pure] at hrun₂
    rcases mem_support_closeEval_pure.mp hrun₂ with hEq
    have hdes : sA'.desynced = (s₁.1.desynced || decide (a₂.1 ≠ s₁.1.outer.corrupted)) :=
      congrArg (fun p => p.1.2.desynced) hEq
    rw [hT, Bool.true_or] at hdes; exact hdes

open Classical in
private theorem closeEval_absorbAdaptiveHybridCheck_le (mode : CorruptionMode)
    (C₀ : ℕ → Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (φ : AdaptiveProtocol n SubIn SubOut NQ₂ NR₂ View₂)
    (hρ_view : ρ.ViewStableOnCorrupt) (hφ_view : φ.ViewStableOnCorrupt)
    (S_D : AdaptiveAdversary n SubIn SubOut NQ₂ NR₂ View₂
      (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁))
    (Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₁) (AdaptiveHybridView Viewρ View₁)))
    (target : Bool) (κ : ℕ) (z : List Bool) (hinit : S_D.initial κ = C₀ κ) :
    (adaptiveExec mode φ S_D (absorbAdaptiveHybridCheck mode C₀ ρ Z target) κ z).eval true ≤
      (adaptiveExec mode (composeAdaptive ρ φ) (adaptiveHybridSim mode C₀ S_D) Z κ z).eval
        target := by
  change closeEval ((adaptiveExecMachine mode φ S_D κ).link
      (absorbAdaptiveHybridCheck mode C₀ ρ Z target κ z)) true ≤
    closeEval ((adaptiveExecMachine mode (composeAdaptive ρ φ)
      (adaptiveHybridSim mode C₀ S_D) κ).link (Z κ z)) target
  dsimp only [Machine.run, Machine.link, adaptiveExecMachine]
  have hinitL :
      ((liftAdaptiveAdversary (S_D.machine κ)).comp
          (adaptiveRouter mode φ κ (S_D.initial κ))).init = do
        let sφ ← (φ.machine κ).init
        let sS ← (S_D.machine κ).init
        return (sS,
          { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ
            corrupted := C₀ κ
            trace := fun i => [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ)] }) := by
    dsimp only [Machine.comp, liftAdaptiveAdversary, Machine.liftRight, adaptiveRouter]
    rw [hinit, bind_assoc]
    refine bind_congr (m := ProbComp) fun sφ => ?_
    rfl
  have hinitR :
      ((liftAdaptiveAdversary ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ)
          (NetR := NetR) (Viewρ := Viewρ) mode C₀ S_D).machine κ)).comp
          (adaptiveRouter mode (composeAdaptive ρ φ) κ
            ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ)
              (NetR := NetR) (Viewρ := Viewρ) mode C₀ S_D).initial κ))).init = do
        let sφ ← (φ.machine κ).init
        let sρ ← (ρ.machine κ).init
        let sS ← (S_D.machine κ).init
        return ((sS, C₀ κ),
          { inner :=
              { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ
                           corrupted := C₀ κ
                           trace := fun i => [ρ.view κ i sρ] }
                sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ
                         corrupted := C₀ κ
                         trace := fun i => [φ.view κ i sφ] } }
            corrupted := C₀ κ
            trace := fun i =>
              [(composeAdaptive ρ φ).view κ i
                { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ
                             corrupted := C₀ κ
                             trace := fun i => [ρ.view κ i sρ] }
                  sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ
                           corrupted := C₀ κ
                           trace := fun i => [φ.view κ i sφ] } }] }) := by
    dsimp only [Machine.comp, liftAdaptiveAdversary, Machine.liftRight, adaptiveHybridSim,
      adaptiveHybridSimMachine, adaptiveRouter, composeAdaptive]
    simp only [bind_assoc, pure_bind]
    refine bind_congr (m := ProbComp) fun sφ =>
      bind_congr (m := ProbComp) fun sρ =>
        bind_congr (m := ProbComp) fun sS => congrArg pure (by
      have happly := applyInitialCorruptions_composeAdaptive ρ φ κ (C₀ κ) sρ sφ
        (fun i => [ρ.view κ i sρ]) (fun i => [φ.view κ i sφ])
      dsimp only [composeAdaptive] at happly
      rw [happly])
  have hinitL_eval :
      ((ProbComp.eval ((liftAdaptiveAdversary (S_D.machine κ)).comp
          (adaptiveRouter mode φ κ (S_D.initial κ))).init).bind fun s =>
        closeEval (Prod.fst <$> ((liftAdaptiveAdversary (S_D.machine κ)).comp
          (adaptiveRouter mode φ κ (S_D.initial κ))).runFrom
          (absorbAdaptiveHybridCheck mode C₀ ρ Z target κ z) s)) true =
      ((ProbComp.eval (φ.machine κ).init).bind fun sφ₀ =>
        (ProbComp.eval (S_D.machine κ).init).bind fun sS₀ =>
          closeEval (Prod.fst <$> (adaptiveExecMachine mode φ S_D κ).runFrom
            (absorbAdaptiveHybridCheck mode C₀ ρ Z target κ z)
            (sS₀, { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                    corrupted := C₀ κ
                    trace := fun i =>
                      [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ₀)] }))) true := by
    erw [hinitL, ProbComp.eval_bind, PMF.bind_bind]
    refine congrArg (fun f => PMF.bind (ProbComp.eval (φ.machine κ).init) f true)
      (funext fun sφ₀ => ?_)
    erw [ProbComp.eval_bind, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun sS₀ => ?_)
    erw [ProbComp.eval_pure, PMF.pure_bind]
    rfl
  have hinitR_eval :
      ((ProbComp.eval ((liftAdaptiveAdversary
          ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
            (Viewρ := Viewρ) mode C₀ S_D).machine κ)).comp
          (adaptiveRouter mode (composeAdaptive ρ φ) κ
            ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
              (Viewρ := Viewρ) mode C₀ S_D).initial κ))).init).bind fun s =>
        closeEval (Prod.fst <$> ((liftAdaptiveAdversary
          ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
            (Viewρ := Viewρ) mode C₀ S_D).machine κ)).comp
          (adaptiveRouter mode (composeAdaptive ρ φ) κ
            ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
              (Viewρ := Viewρ) mode C₀ S_D).initial κ))).runFrom (Z κ z) s)) target =
      ((ProbComp.eval (φ.machine κ).init).bind fun sφ₀ =>
        (ProbComp.eval (ρ.machine κ).init).bind fun sρ₀ =>
          (ProbComp.eval (S_D.machine κ).init).bind fun sS₀ =>
            closeEval (Prod.fst <$> ((liftAdaptiveAdversary
              ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
                (Viewρ := Viewρ) mode C₀ S_D).machine κ)).comp
              (adaptiveRouter mode (composeAdaptive ρ φ) κ
                ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
                  (Viewρ := Viewρ) mode C₀ S_D).initial κ))).runFrom (Z κ z)
              ((sS₀, C₀ κ),
                { inner :=
                    { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                                 corrupted := C₀ κ
                                 trace := fun i => [ρ.view κ i sρ₀] }
                      sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                               corrupted := C₀ κ
                               trace := fun i => [φ.view κ i sφ₀] } }
                  corrupted := C₀ κ
                  trace := fun i =>
                    [(composeAdaptive ρ φ).view κ i
                      { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                                   corrupted := C₀ κ
                                   trace := fun i => [ρ.view κ i sρ₀] }
                        sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                                 corrupted := C₀ κ
                                 trace := fun i => [φ.view κ i sφ₀] } }] }))) target := by
    erw [hinitR, ProbComp.eval_bind, PMF.bind_bind]
    refine congrArg (fun f => PMF.bind (ProbComp.eval (φ.machine κ).init) f target)
      (funext fun sφ₀ => ?_)
    erw [ProbComp.eval_bind, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun sρ₀ => ?_)
    erw [ProbComp.eval_bind, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun sS₀ => ?_)
    erw [ProbComp.eval_pure, PMF.pure_bind]
  rw [closeEval_bind, closeEval_bind, closeEval_sample, closeEval_sample]
  erw [hinitL_eval, hinitR_eval]
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun sφ₀ => mul_le_mul_of_nonneg_left ?_ zero_le
  have hswap :
      ((ProbComp.eval (S_D.machine κ).init).bind fun sS₀ =>
        closeEval (Prod.fst <$> (adaptiveExecMachine mode φ S_D κ).runFrom
          (absorbAdaptiveHybridCheck mode C₀ ρ Z target κ z)
          (sS₀, { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                  corrupted := C₀ κ
                  trace := fun i =>
                    [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ₀)] }))) true =
      ((ProbComp.eval (S_D.machine κ).init).bind fun sS₀ =>
        (ProbComp.eval (ρ.machine κ).init).bind fun sρ₀ =>
          closeEval (do
            let x ← (absorbAdaptiveCheckMachine (NQ := NQ₁) (NR := NR₁) (View₁ := View₁)
              mode (C₀ κ) ρ κ).comp
              ((liftAdaptiveAdversary (S_D.machine κ)).comp
                (adaptiveRouter mode φ κ (S_D.initial κ))) |>.runFrom (Z κ z)
              ({ outer :=
                  { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                    corrupted := C₀ κ
                    trace := fun i =>
                      [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] }
                 desynced := false },
               (sS₀, { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                       corrupted := C₀ κ
                       trace := fun i =>
                         [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ₀)] }))
            pure (!x.2.1.desynced && (x.1 == target)))) true := by
    refine congrArg (fun f => PMF.bind (ProbComp.eval (S_D.machine κ).init) f true)
      (funext fun sS₀ => ?_)
    dsimp only [absorbAdaptiveHybridCheck]
    erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
      pure_bind]
    erw [ite_eq_right_iff.mpr (fun h => absurd rfl h)]
    have hinitCheck :
        (absorbAdaptiveCheckMachine (NQ := NQ₁) (NR := NR₁) (View₁ := View₁)
          mode (C₀ κ) ρ κ).init = (do
          let s₀ ← (ρ.machine κ).init
          pure
            { outer :=
                { inner := ρ.applyInitialCorruptions κ (C₀ κ) s₀
                  corrupted := C₀ κ
                  trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) s₀)] }
              desynced := false }) := rfl
    rw [hinitCheck]
    erw [Machine.runFrom_bind, ProbOracleComp.sample_bind, Machine.runFrom_bind,
      Machine.runFrom_sample, bind_map_left, bind_assoc, map_bind, closeEval_bind,
      closeEval_sample]
    refine congrArg (PMF.bind _) (funext fun sρ₀ => ?_)
    erw [ProbOracleComp.sample_pure, Machine.runFrom_pure, pure_bind]
    have hfst : ∀ {α β : Type} (x : α) (y : β), (x, y).1 = x := fun _ _ => rfl
    have hsnd : ∀ {α β : Type} (x : α) (y : β), (x, y).2 = y := fun _ _ => rfl
    repeat erw [hfst]
    repeat erw [hsnd]
    erw [Machine.runFrom_bind, map_bind]
    conv_rhs => erw [Machine.runFrom_comp, bind_map_left]
    refine congrArg closeEval (bind_congr fun ⟨⟨b, sC⟩, sA⟩ => ?_)
    erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply]
  have hRHS :
      ((ProbComp.eval (ρ.machine κ).init).bind fun sρ₀ =>
        (ProbComp.eval (S_D.machine κ).init).bind fun sS₀ =>
          closeEval (Prod.fst <$> ((liftAdaptiveAdversary
            ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
              (Viewρ := Viewρ) mode C₀ S_D).machine κ)).comp
            (adaptiveRouter mode (composeAdaptive ρ φ) κ
              ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
                (Viewρ := Viewρ) mode C₀ S_D).initial κ))).runFrom (Z κ z)
            ((sS₀, C₀ κ),
              { inner :=
                  { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                               corrupted := C₀ κ
                               trace := fun i => [ρ.view κ i sρ₀] }
                    sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                             corrupted := C₀ κ
                             trace := fun i => [φ.view κ i sφ₀] } }
                corrupted := C₀ κ
                trace := fun i =>
                  [(composeAdaptive ρ φ).view κ i
                    { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                                 corrupted := C₀ κ
                                 trace := fun i => [ρ.view κ i sρ₀] }
                      sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                               corrupted := C₀ κ
                               trace := fun i => [φ.view κ i sφ₀] } }] }))) target =
        ((ProbComp.eval (S_D.machine κ).init).bind fun sS₀ =>
          (ProbComp.eval (ρ.machine κ).init).bind fun sρ₀ =>
            closeEval (((liftAdaptiveAdversary
              ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
                (Viewρ := Viewρ) mode C₀ S_D).machine κ)).comp
              (adaptiveRouter mode (composeAdaptive ρ φ) κ
                ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
                  (Viewρ := Viewρ) mode C₀ S_D).initial κ))).runFrom (Z κ z)
              ((sS₀, C₀ κ),
                { inner :=
                    { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                                 corrupted := C₀ κ
                                 trace := fun i => [ρ.view κ i sρ₀] }
                      sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                               corrupted := C₀ κ
                               trace := fun i => [φ.view κ i sφ₀] } }
                  corrupted := C₀ κ
                  trace := fun i =>
                    [(composeAdaptive ρ φ).view κ i
                      { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                                   corrupted := C₀ κ
                                   trace := fun i => [ρ.view κ i sρ₀] }
                        sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                                 corrupted := C₀ κ
                                 trace := fun i => [φ.view κ i sφ₀] } }] }) >>=
              fun x => pure (x.1 == target))) true := by
    have hcomm := PMF.bind_comm (ProbComp.eval (ρ.machine κ).init)
      (ProbComp.eval (S_D.machine κ).init)
      (fun sρ₀ sS₀ => closeEval (Prod.fst <$>
        ((liftAdaptiveAdversary
          ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
            (Viewρ := Viewρ) mode C₀ S_D).machine κ)).comp
          (adaptiveRouter mode (composeAdaptive ρ φ) κ
            ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
              (Viewρ := Viewρ) mode C₀ S_D).initial κ))).runFrom (Z κ z)
        ((sS₀, C₀ κ),
          { inner :=
              { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                           corrupted := C₀ κ
                           trace := fun i => [ρ.view κ i sρ₀] }
                sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                         corrupted := C₀ κ
                         trace := fun i => [φ.view κ i sφ₀] } }
            corrupted := C₀ κ
            trace := fun i =>
              [(composeAdaptive ρ φ).view κ i
                { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                             corrupted := C₀ κ
                             trace := fun i => [ρ.view κ i sρ₀] }
                  sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                           corrupted := C₀ κ
                           trace := fun i => [φ.view κ i sφ₀] } }] })))
    rw [hcomm, PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun sS₀ => congrArg _ ?_
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun sρ₀ => congrArg _ ?_
    erw [bind_pure_comp, closeEval_map, closeEval_map]
    rw [PMF.map_apply, PMF.map_apply]
    refine tsum_congr fun x => ?_
    by_cases hx : x.1 = target
    · simp [hx]
    · simp [hx, Ne.symm hx]
  rw [hswap, hRHS]
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun sS₀ => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun sρ₀ => mul_le_mul_of_nonneg_left ?_ zero_le
  let M₁ := (absorbAdaptiveCheckMachine (NQ := NQ₁) (NR := NR₁) (View₁ := View₁)
    mode (C₀ κ) ρ κ).comp
    ((liftAdaptiveAdversary (S_D.machine κ)).comp (adaptiveRouter mode φ κ (S_D.initial κ)))
  let M₂ := (liftAdaptiveAdversary ((adaptiveHybridSim (In := In) (Out := Out)
    (NetQ := NetQ) (NetR := NetR) (Viewρ := Viewρ) mode C₀ S_D).machine κ)).comp
    (adaptiveRouter mode (composeAdaptive ρ φ) κ
      ((adaptiveHybridSim (In := In) (Out := Out) (NetQ := NetQ)
        (NetR := NetR) (Viewρ := Viewρ) mode C₀ S_D).initial κ))
  let R : M₁.State → M₂.State → Prop := fun s₁ s₂ =>
    s₁.1.desynced = false ∧
    RouterStateRel ρ.memory s₁.1.outer s₂.2.inner.outer ∧
    RouterStateRel φ.memory s₁.2.2 s₂.2.inner.sub ∧
    s₁.2.1 = s₂.1.1 ∧
    s₂.1.2 = s₁.1.outer.corrupted ∧
    s₂.2.corrupted = s₁.1.outer.corrupted ∧
    s₂.2.inner.outer.corrupted = s₁.1.outer.corrupted ∧
    s₂.2.inner.sub.corrupted = s₁.1.outer.corrupted ∧
    s₁.2.2.corrupted = s₁.1.outer.corrupted
  let Trap : M₁.State → Prop := fun s₁ => s₁.1.desynced = true
  have hR_init : R
      ({ outer :=
          { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
            corrupted := C₀ κ
            trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] }
         desynced := false },
       (sS₀, { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
               corrupted := C₀ κ
               trace := fun i => [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ₀)] }))
      ((sS₀, C₀ κ),
        { inner :=
            { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                         corrupted := C₀ κ
                         trace := fun i => [ρ.view κ i sρ₀] }
              sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                       corrupted := C₀ κ
                       trace := fun i => [φ.view κ i sφ₀] } }
          corrupted := C₀ κ
          trace := fun i =>
            [(composeAdaptive ρ φ).view κ i
              { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                           corrupted := C₀ κ
                           trace := fun i => [ρ.view κ i sρ₀] }
                sub := { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                         corrupted := C₀ κ
                         trace := fun i => [φ.view κ i sφ₀] } }] }) :=
    ⟨rfl,
     ⟨rfl, rfl, fun hne => funext fun i => by
        simp [view_applyInitialCorruptions_hybrid hρ_view hne]⟩,
     ⟨rfl, rfl, fun hne => funext fun i => by
        simp [view_applyInitialCorruptions_adaptive hφ_view hne]⟩,
     rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine Machine.closeEval_runFrom_le_intertwine M₁ M₂ (fun _ => True) R Trap (Z κ z)
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    _ _ hR_init
    (fun x => pure (!x.2.1.desynced && (x.1 == target)))
    (fun x => pure (x.1 == target)) true
    (fun a s₁ s₂ hR => by simp only [hR.1, Bool.not_false, Bool.true_and, le_rfl])
    (fun a s₁ hT => by
      dsimp only [Trap] at hT
      simp only [closeEval_pure, PMF.pure_apply, hT, Bool.not_true, Bool.false_and,
        Bool.true_eq_false, ↓reduceIte])
    (fun q s₁ _ _ hT hz =>
      absorbAdaptiveCheckMachine_desynced_preserved
        ((liftAdaptiveAdversary (S_D.machine κ)).comp (adaptiveRouter mode φ κ (S_D.initial κ)))
        mode (C₀ κ) ρ κ q s₁ hT hz)
    ?_
  · intro q ⟨⟨rρ, des⟩, ⟨sS₁, rφ⟩⟩ ⟨⟨sS₂, expC⟩, rComp⟩ k₁ k₂ _
      ⟨hdes, hO, hS, hsS, hexp, hcComp, hcO, hcS, hcφ⟩ hcont htrap
    dsimp only at hO hS hdes hsS hexp hcComp hcO hcS hcφ
    subst hdes; subst hsS
    have hcorO : rComp.corrupted = rρ.corrupted := hcComp
    have hcorφ : rφ.corrupted = rρ.corrupted := hcφ
    have hOsym : RouterStateRel ρ.memory rComp.inner.outer rρ :=
      ⟨hO.1.symm, hO.2.1.symm, fun hne => (hO.2.2 hne).symm⟩
    dsimp only [M₁, M₂]
    erw [machine_comp_handle_run, machine_comp_handle_run]
    rcases q with (⟨i, x⟩ | _) | (⟨i, x⟩ | i | (q | (⟨j, subX⟩ | nq)))
    · erw [absorbAdaptiveCheckMachine_handle_inl_party]
      dsimp only [adaptiveHybridSim]
      by_cases hi : i ∈ rρ.corrupted
      · have hi' : i ∈ rComp.corrupted := hcorO ▸ hi
        simp only [hi, ↓reduceIte]
        erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
        erw [liftAdaptiveAdversary_handle_inl, Machine.runFrom_map, Machine.runFrom_query]
        conv_rhs =>
          dsimp only [adaptiveRouter, StateT.run]
          simp only [hi', ↓reduceIte]
        erw [map_pure, Prod.map_apply, id_eq, Equiv.prodAssoc_apply, pure_bind]
        exact hcont none _ _ ⟨rfl, hO, hS, rfl, hexp, hcComp, hcO, hcS, hcφ⟩
      · have hi' : i ∉ rComp.corrupted := hcorO ▸ hi
        simp only [hi, ↓reduceIte]
        erw [liftAdaptiveAdversary_handle_inl, Machine.runFrom_map, Machine.runFrom_query]
        conv_rhs =>
          dsimp only [adaptiveRouter, composeAdaptive, StateT.run]
          simp only [hi', ↓reduceIte, hO.1, hS.1]
          repeat erw [map_bind]
          repeat erw [bind_assoc]
          simp only [pure_bind, map_pure, Prod.map_apply, id_eq, Equiv.prodAssoc_apply]
        conv_lhs =>
          erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_comp, bind_map_left,
            runFrom_liftAdaptiveAdversary_liftSubParty, Machine.runFrom_map, bind_map_left]
          rw [hO.1]
        refine closeEval_runLiftSubParty_le mode φ κ (S_D.initial κ) _ rφ rComp.inner.sub hS
          _ _ true ?_
        intro ⟨out, sρ'⟩ rφ' rSub' hSub' hCφ hCSub
        erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
        dsimp only
        refine hcont out _ _ ?_
        exact ⟨rfl, routerStateRel_recordSnapshot_hybrid ρ κ hO sρ', hSub', rfl, hexp, hcComp,
          hcO, hCSub.trans hcS, hCφ.trans hcφ⟩
    · erw [absorbAdaptiveCheckMachine_handle_inl_status]
      dsimp only [adaptiveHybridSim]
      erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
      erw [liftAdaptiveAdversary_handle_inl, Machine.runFrom_map, Machine.runFrom_query]
      conv_rhs => dsimp only [adaptiveRouter, StateT.run]
      erw [map_pure, Prod.map_apply, id_eq, Equiv.prodAssoc_apply, pure_bind, hcorO]
      exact hcont rρ.corrupted _ _ ⟨rfl, hO, hS, rfl, hexp, hcComp, hcO, hcS, hcφ⟩
    · erw [absorbAdaptiveCheckMachine_handle_inr_party]
      dsimp only [adaptiveHybridSim]
      by_cases hi : i ∈ rρ.corrupted
      · have hi' : i ∈ rComp.corrupted := hcorO ▸ hi
        simp only [hi, ↓reduceIte]
        erw [liftAdaptiveAdversary_handle_inr, adaptiveHybridSimMachine_handle_party,
          liftAdaptiveNet, Machine.liftRightProgram_map, Machine.liftRightProgram_query,
          Machine.runFrom_map, Machine.runFrom_query]
        conv_rhs =>
          dsimp only [adaptiveRouter, composeAdaptive, StateT.run, toOuterPartyReply]
          simp only [hi', ↓reduceIte, hO.1, hS.1]
          repeat erw [map_bind]
          repeat erw [bind_assoc]
          simp only [pure_bind, map_pure, Prod.map_apply, id_eq, Equiv.prodAssoc_apply]
        conv_lhs =>
          erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_comp, bind_map_left,
            runFrom_liftAdaptiveAdversary_liftSubParty, Machine.runFrom_map, bind_map_left]
          rw [hO.1]
        refine closeEval_runLiftSubParty_le mode φ κ (S_D.initial κ) _ rφ rComp.inner.sub hS
          _ _ true ?_
        intro ⟨out, sρ'⟩ rφ' rSub' hSub' hCφ hCSub
        erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
        dsimp only
        refine hcont (.party out) _ _ ?_
        exact ⟨rfl, routerStateRel_recordSnapshot_hybrid ρ κ hO sρ', hSub', rfl, hexp, hcComp,
          hcO, hCSub.trans hcS, hCφ.trans hcφ⟩
      · have hi' : i ∉ rComp.corrupted := hcorO ▸ hi
        simp only [hi, ↓reduceIte]
        erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
        erw [liftAdaptiveAdversary_handle_inr, adaptiveHybridSimMachine_handle_party,
          liftAdaptiveNet, Machine.liftRightProgram_map, Machine.liftRightProgram_query,
          Machine.runFrom_map, Machine.runFrom_query]
        conv_rhs =>
          dsimp only [adaptiveRouter, StateT.run, toOuterPartyReply]
          simp only [hi', ↓reduceIte]
        erw [map_pure, Prod.map_apply, id_eq, Equiv.prodAssoc_apply, pure_bind]
        exact hcont (.party none) _ _ ⟨rfl, hO, hS, rfl, hexp, hcComp, hcO, hcS, hcφ⟩
    · dsimp only [adaptiveHybridSim]
      cases mode
      · erw [absorbAdaptiveCheckMachine_handle_inr_corrupt_static]
        by_cases hi : i ∈ rρ.corrupted
        · have hi' : i ∈ expC := hexp ▸ hi
          simp only [hi, ↓reduceIte]
          conv_lhs =>
            erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_query,
              machine_comp_handle_run, bind_map_left, liftAdaptiveAdversary_handle_inr]
            dsimp only
          conv_rhs =>
            erw [liftAdaptiveAdversary_handle_inr, adaptiveHybridSimMachine_handle_corrupt_static]
            simp only [hi', ↓reduceIte]
            erw [liftAdaptiveNet, Machine.liftRightProgram_bind, Machine.runFrom_bind,
              bind_map_left, bind_assoc]
            rw [← hinit, hexp]
          refine closeEval_runSubNet_le .static ρ φ κ (S_D.initial κ) rρ.corrupted rρ.corrupted
            Finset.Subset.rfl (fun _ => rfl)
            (fun _ rO => RouterStateRel ρ.memory rO rρ)
            (fun _ _ _ hExp _ hj hjC => absurd (hExp hj) hjC)
            (((S_D.machine κ).handle (.corrupt i)).run sS₁) rφ rComp
            ⟨hS, hcφ, hcComp, hcO, hcS, hOsym⟩ _ _ true ?_ ?_
          · intro ⟨rSub, sS'⟩ rφ' rComp' hS' hcφ' hcComp' hcO' hcS' hO'
            have hO_sym' : RouterStateRel ρ.memory rρ rComp'.inner.outer :=
              ⟨hO'.1.symm, hO'.2.1.symm, fun hne => (hO'.2.2 hne).symm⟩
            erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
              pure_bind]
            repeat erw [Equiv.prodAssoc_apply]
            dsimp only
            erw [Machine.liftRightProgram_bind, Machine.liftRightProgram_query,
              Machine.runFrom_bind, Machine.runFrom_query]
            dsimp only [adaptiveRouter, StateT.run]
            have hiComp' : i ∈ rComp'.corrupted := hcComp' ▸ hi
            simp only [hiComp', ↓reduceIte, pure_bind]
            have hrep : ((composeAdaptive ρ φ).corruptionReport κ i rComp').current.outer =
                ρ.corruptionReport κ i rρ := by
              simp only [AdaptiveProtocol.corruptionReport, composeAdaptive]
              exact routerStateRel_corruptionReport_hybrid ρ κ i hO'
            cases rSub with
            | party _ =>
              dsimp only
              refine hcont (.corrupt none) _ _ ?_
              exact ⟨by
                  rw [hcφ']; exact (Bool.false_or _).trans (decide_eq_false (not_not.mpr rfl)),
                hO_sym', hS', rfl, rfl, hcComp', hcO', hcS', hcφ'⟩
            | net _ =>
              dsimp only
              refine hcont (.corrupt none) _ _ ?_
              exact ⟨by
                  rw [hcφ']; exact (Bool.false_or _).trans (decide_eq_false (not_not.mpr rfl)),
                hO_sym', hS', rfl, rfl, hcComp', hcO', hcS', hcφ'⟩
            | corrupt rep =>
              cases rep with
              | none =>
                dsimp only
                refine hcont (.corrupt none) _ _ ?_
                exact ⟨by
                    rw [hcφ']; exact (Bool.false_or _).trans (decide_eq_false (not_not.mpr rfl)),
                  hO_sym', hS', rfl, rfl, hcComp', hcO', hcS', hcφ'⟩
              | some repSub =>
                dsimp only
                erw [hrep]
                refine hcont (.corrupt (some { current :=
                    { outer := ρ.corruptionReport κ i rρ, sub := repSub }, history := none }))
                  _ _ ?_
                exact ⟨by
                    rw [hcφ']; exact (Bool.false_or _).trans (decide_eq_false (not_not.mpr rfl)),
                  hO_sym', hS', rfl, rfl, hcComp', hcO', hcS', hcφ'⟩
          · intro ⟨rSub, sS'⟩ rφ' hne
            erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
              pure_bind]
            repeat erw [Equiv.prodAssoc_apply]
            dsimp only
            exact htrap _ _ ((Bool.false_or _).trans (decide_eq_true hne))
        · have hi' : i ∉ expC := hexp ▸ hi
          simp only [hi, ↓reduceIte]
          erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
          erw [liftAdaptiveAdversary_handle_inr, adaptiveHybridSimMachine_handle_corrupt_static]
          simp only [hi', ↓reduceIte]
          erw [liftAdaptiveNet, Machine.liftRightProgram_pure,
            Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
          exact hcont (.corrupt none) _ _ ⟨rfl, hO, hS, rfl, hexp, hcComp, hcO, hcS, hcφ⟩
      · erw [absorbAdaptiveCheckMachine_handle_inr_corrupt_adaptive]
        let rρ' : AdaptiveRouterState (ρ.machine κ).State Viewρ n :=
          if i ∈ rρ.corrupted then rρ
          else { inner := ρ.onCorrupt κ i rρ.inner
                 corrupted := insert i rρ.corrupted
                 trace := rρ.trace }
        let OuterRel : Finset (Fin n) → AdaptiveRouterState (ρ.machine κ).State Viewρ n → Prop :=
          fun C rO =>
            if i ∈ C then RouterStateRel ρ.memory rO rρ' else RouterStateRel ρ.memory rO rρ
        have hOuter_init : OuterRel rρ.corrupted rComp.inner.outer := by
          dsimp only [OuterRel, rρ']
          by_cases hi : i ∈ rρ.corrupted <;> simp only [hi, ↓reduceIte] <;> exact hOsym
        have hOuter_corrupt : ∀ C rO j, rρ.corrupted ⊆ C → C ⊆ insert i rρ.corrupted →
            j ∈ insert i rρ.corrupted → j ∉ C → OuterRel C rO →
            OuterRel (insert j C)
              { inner := ρ.onCorrupt κ j rO.inner
                corrupted := insert j rO.corrupted
                trace := rO.trace } := by
          intro C rO j hExp hC hjT hjC hOr
          rcases Finset.mem_insert.mp hjT with rfl | hjR
          · have hi' : j ∉ rρ.corrupted := fun h => hjC (hExp h)
            dsimp only [OuterRel, rρ'] at hOr ⊢
            simp only [hjC, hi', Finset.mem_insert_self, ↓reduceIte] at hOr ⊢
            exact ⟨by rw [hOr.1], by rw [hOr.2.1], fun hne => hOr.2.2 hne⟩
          · exact absurd (hExp hjR) hjC
        conv_lhs =>
          erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_query,
            machine_comp_handle_run, bind_map_left, liftAdaptiveAdversary_handle_inr]
          dsimp only
        conv_rhs =>
          erw [liftAdaptiveAdversary_handle_inr, adaptiveHybridSimMachine_handle_corrupt_adaptive,
            liftAdaptiveNet, Machine.liftRightProgram_bind, Machine.runFrom_bind]
          erw [bind_map_left, bind_assoc]
          dsimp only
          rw [← hinit, hexp]
        refine closeEval_runSubNet_le .adaptive ρ φ κ (S_D.initial κ) rρ.corrupted
          (insert i rρ.corrupted) (Finset.subset_insert _ _) (fun h => by cases h)
          OuterRel hOuter_corrupt
          (((S_D.machine κ).handle (.corrupt i)).run sS₁) rφ rComp
          ⟨hS, hcφ, hcComp, hcO, hcS, hOuter_init⟩ _ _ true ?_ ?_
        · intro ⟨rSub, sS'⟩ rφ' rComp' hS' hcφ' hcComp' hcO' hcS' hO'
          have hcor_rρ' : rρ'.corrupted = insert i rρ.corrupted := by
            dsimp only [rρ']
            by_cases hi : i ∈ rρ.corrupted
            · simp only [hi, ↓reduceIte, Finset.insert_eq_of_mem]
            · simp only [hi, ↓reduceIte]
          have hO_rel' : RouterStateRel ρ.memory rComp'.inner.outer rρ' := by
            dsimp only [OuterRel] at hO'
            simp only [Finset.mem_insert_self, ↓reduceIte] at hO'
            exact hO'
          have hO_sym' : RouterStateRel ρ.memory rρ' rComp'.inner.outer :=
            ⟨hO_rel'.1.symm, hO_rel'.2.1.symm, fun hne => (hO_rel'.2.2 hne).symm⟩
          erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
            pure_bind]
          repeat erw [Equiv.prodAssoc_apply]
          dsimp only
          erw [Machine.liftRightProgram_bind, Machine.liftRightProgram_query,
            Machine.runFrom_bind, Machine.runFrom_query]
          dsimp only [adaptiveRouter, StateT.run]
          simp only [hcComp', Finset.mem_insert_self, ↓reduceIte, pure_bind]
          have hrep : ((composeAdaptive ρ φ).corruptionReport κ i rComp').current.outer =
              ρ.corruptionReport κ i rρ' := by
            simp only [AdaptiveProtocol.corruptionReport, composeAdaptive]
            exact routerStateRel_corruptionReport_hybrid ρ κ i hO_rel'
          have hcorO' : rComp'.corrupted = rρ'.corrupted := hcComp'.trans hcor_rρ'.symm
          have hcorO_inner' : rComp'.inner.outer.corrupted = rρ'.corrupted :=
            hcO'.trans hcor_rρ'.symm
          have hcorS_inner' : rComp'.inner.sub.corrupted = rρ'.corrupted :=
            hcS'.trans hcor_rρ'.symm
          have hcorφ' : rφ'.corrupted = rρ'.corrupted := hcφ'.trans hcor_rρ'.symm
          cases rSub with
          | party _ =>
            dsimp only
            refine hcont (.corrupt none) _ _ ?_
            exact ⟨by by_cases hi : i ∈ rρ.corrupted <;> simp [hi, hcφ'] <;> rfl,
              hO_sym', hS', rfl, hcor_rρ'.symm, hcorO', hcorO_inner', hcorS_inner', hcorφ'⟩
          | net _ =>
            dsimp only
            refine hcont (.corrupt none) _ _ ?_
            exact ⟨by by_cases hi : i ∈ rρ.corrupted <;> simp [hi, hcφ'] <;> rfl,
              hO_sym', hS', rfl, hcor_rρ'.symm, hcorO', hcorO_inner', hcorS_inner', hcorφ'⟩
          | corrupt rep =>
            cases rep with
            | none =>
              dsimp only
              refine hcont (.corrupt none) _ _ ?_
              exact ⟨by by_cases hi : i ∈ rρ.corrupted <;> simp [hi, hcφ'] <;> rfl,
                hO_sym', hS', rfl, hcor_rρ'.symm, hcorO', hcorO_inner', hcorS_inner', hcorφ'⟩
            | some repSub =>
              dsimp only
              erw [hrep]
              refine hcont (.corrupt (some { current :=
                  { outer := ρ.corruptionReport κ i rρ', sub := repSub }, history := none }))
                _ _ ?_
              exact ⟨by by_cases hi : i ∈ rρ.corrupted <;> simp [hi, hcφ'] <;> rfl,
                hO_sym', hS', rfl, hcor_rρ'.symm, hcorO', hcorO_inner', hcorS_inner', hcorφ'⟩
        · intro ⟨rSub, sS'⟩ rφ' hne
          erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
            pure_bind]
          repeat erw [Equiv.prodAssoc_apply]
          dsimp only
          exact htrap _ _ (by
            dsimp only [Trap]
            by_cases hi : i ∈ rρ.corrupted
            · simp only [hi, ↓reduceIte, Bool.false_or]
              exact decide_eq_true fun heq => hne (heq.trans (Finset.insert_eq_of_mem hi).symm)
            · simp only [hi, ↓reduceIte, Bool.false_or]
              exact decide_eq_true hne)
    · erw [absorbAdaptiveCheckMachine_handle_inr_net_inl]
      dsimp only [adaptiveHybridSim]
      erw [liftAdaptiveAdversary_handle_inr, adaptiveHybridSimMachine_handle_net_inl,
        liftAdaptiveNet, Machine.liftRightProgram_map, Machine.liftRightProgram_query,
        Machine.runFrom_map, Machine.runFrom_query]
      conv_rhs =>
        dsimp only [adaptiveRouter, composeAdaptive, StateT.run, toOuterNetReply]
        repeat erw [map_bind]
        repeat erw [bind_assoc]
        simp only [pure_bind, map_pure, Prod.map_apply, id_eq, Equiv.prodAssoc_apply]
      conv_lhs =>
        erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_comp, bind_map_left,
          runFrom_liftAdaptiveAdversary_liftSubParty, Machine.runFrom_map, bind_map_left]
        rw [hO.1]
      refine closeEval_runLiftSubParty_le mode φ κ (S_D.initial κ) _ rφ rComp.inner.sub hS
        _ _ true ?_
      intro ⟨r, sρ'⟩ rφ' rSub' hSub' hCφ hCSub
      erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
      dsimp only
      refine hcont (.net (.inl r)) _ _ ?_
      exact ⟨rfl, routerStateRel_recordSnapshot_hybrid ρ κ hO sρ', hSub', rfl, hexp, hcComp, hcO,
        hCSub.trans hcS, hCφ.trans hcφ⟩
    · erw [absorbAdaptiveCheckMachine_handle_inr_net_inr_inl]
      dsimp only [adaptiveHybridSim]
      conv_lhs =>
        erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_query,
          machine_comp_handle_run, bind_map_left, liftAdaptiveAdversary_handle_inr]
        dsimp only
      conv_rhs =>
        erw [liftAdaptiveAdversary_handle_inr, adaptiveHybridSimMachine_handle_net_inr_inl,
          liftAdaptiveNet, Machine.liftRightProgram_bind, Machine.runFrom_bind, bind_map_left,
          bind_assoc]
        dsimp only
        rw [← hinit, hexp]
      refine closeEval_runSubNet_le mode ρ φ κ (S_D.initial κ) rρ.corrupted rρ.corrupted
        Finset.Subset.rfl (fun _ => rfl)
        (fun _ rO => RouterStateRel ρ.memory rO rρ)
        (fun _ _ _ hExp _ hjT hjC => absurd (hExp hjT) hjC)
        (((S_D.machine κ).handle (.party j subX)).run sS₁) rφ rComp
        ⟨hS, hcφ, hcComp, hcO, hcS, hOsym⟩ _ _ true ?_ ?_
      · intro ⟨rSub, sS'⟩ rφ' rComp' hS' hcφ' hcComp' hcO' hcS' hO'
        have hO_sym' : RouterStateRel ρ.memory rρ rComp'.inner.outer :=
          ⟨hO'.1.symm, hO'.2.1.symm, fun hne => (hO'.2.2 hne).symm⟩
        erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
          pure_bind, Machine.runFrom_pure]
        repeat erw [Equiv.prodAssoc_apply]
        dsimp only
        refine hcont (.net (.inr (subNetReplyToRouted rSub))) _ _ ?_
        exact ⟨by rw [hcφ']; exact (Bool.false_or _).trans (decide_eq_false (not_not.mpr rfl)),
          hO_sym', hS', rfl, rfl, hcComp', hcO', hcS', hcφ'⟩
      · intro ⟨rSub, sS'⟩ rφ' hne
        erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
          pure_bind]
        repeat erw [Equiv.prodAssoc_apply]
        dsimp only
        exact htrap _ _ ((Bool.false_or _).trans (decide_eq_true hne))
    · erw [absorbAdaptiveCheckMachine_handle_inr_net_inr_inr]
      dsimp only [adaptiveHybridSim]
      conv_lhs =>
        erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_query,
          machine_comp_handle_run, bind_map_left, liftAdaptiveAdversary_handle_inr]
        dsimp only
      conv_rhs =>
        erw [liftAdaptiveAdversary_handle_inr, adaptiveHybridSimMachine_handle_net_inr_inr,
          liftAdaptiveNet, Machine.liftRightProgram_bind, Machine.runFrom_bind, bind_map_left,
          bind_assoc]
        dsimp only
        rw [← hinit, hexp]
      refine closeEval_runSubNet_le mode ρ φ κ (S_D.initial κ) rρ.corrupted rρ.corrupted
        Finset.Subset.rfl (fun _ => rfl)
        (fun _ rO => RouterStateRel ρ.memory rO rρ)
        (fun _ _ _ hExp _ hjT hjC => absurd (hExp hjT) hjC)
        (((S_D.machine κ).handle (.net nq)).run sS₁) rφ rComp
        ⟨hS, hcφ, hcComp, hcO, hcS, hOsym⟩ _ _ true ?_ ?_
      · intro ⟨rSub, sS'⟩ rφ' rComp' hS' hcφ' hcComp' hcO' hcS' hO'
        have hO_sym' : RouterStateRel ρ.memory rρ rComp'.inner.outer :=
          ⟨hO'.1.symm, hO'.2.1.symm, fun hne => (hO'.2.2 hne).symm⟩
        erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
          pure_bind, Machine.runFrom_pure]
        repeat erw [Equiv.prodAssoc_apply]
        dsimp only
        refine hcont (.net (.inr (subNetReplyToRouted rSub))) _ _ ?_
        exact ⟨by rw [hcφ']; exact (Bool.false_or _).trans (decide_eq_false (not_not.mpr rfl)),
          hO_sym', hS', rfl, rfl, hcComp', hcO', hcS', hcφ'⟩
      · intro ⟨rSub, sS'⟩ rφ' hne
        erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
          pure_bind]
        repeat erw [Equiv.prodAssoc_apply]
        dsimp only
        exact htrap _ _ ((Bool.false_or _).trans (decide_eq_true hne))

/-! ### Adaptive composition theorems -/

open Classical in
private noncomputable def initCheckEnv (C₀ : ℕ → Finset (Fin n)) :
    AdaptiveEnvironment n SubIn SubOut (AdaptiveNetQ n SubIn NQ₁)
      (AdaptiveNetR SubOut NR₁ View₁) :=
  fun κ _ =>
    ProbOracleComp.query
      (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ₁)
        (AdaptiveNetR SubOut NR₁ View₁))
      (.inl .status) >>= fun C => pure (decide (C = C₀ κ))

open Classical in
private theorem eval_exec_initCheckEnv {View : Type} (mode : CorruptionMode)
    (σ : AdaptiveProtocol n SubIn SubOut NQ NR View)
    (A : AdaptiveAdversary n SubIn SubOut NQ NR View (AdaptiveNetQ n SubIn NQ₁)
      (AdaptiveNetR SubOut NR₁ View₁))
    (C₀ : ℕ → Finset (Fin n)) (κ : ℕ) (z : List Bool) :
    (adaptiveExec mode σ A (initCheckEnv C₀) κ z).eval =
      PMF.pure (decide (A.initial κ = C₀ κ)) := by
  rw [adaptiveExec, Machine.run]
  dsimp only [initCheckEnv, adaptiveExecMachine, Machine.link]
  have hinit : ((liftAdaptiveAdversary (A.machine κ)).comp
      (adaptiveRouter mode σ κ (A.initial κ))).init = (do
      let sσ ← (σ.machine κ).init
      let sA ← (liftAdaptiveAdversary (A.machine κ)).init
      pure (sA,
        { inner := σ.applyInitialCorruptions κ (A.initial κ) sσ
          corrupted := A.initial κ
          trace := fun i => [σ.view κ i (σ.applyInitialCorruptions κ (A.initial κ) sσ)] })) := by
    dsimp only [Machine.comp, liftAdaptiveAdversary, Machine.liftRight, adaptiveRouter]
    rw [bind_assoc]
    rfl
  rw [hinit, ProbOracleComp.sample_bind, bind_assoc, Machine.closeProgram_bind, ProbComp.eval_bind,
    Machine.closeProgram_sample]
  have hrun : ∀ (sA : (A.machine κ).State)
      (rσ : AdaptiveRouterState (σ.machine κ).State View n),
      rσ.corrupted = A.initial κ →
      Prod.fst <$> ((liftAdaptiveAdversary (A.machine κ)).comp
        (adaptiveRouter mode σ κ (A.initial κ))).runFrom
        (ProbOracleComp.query
          (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ₁)
            (AdaptiveNetR SubOut NR₁ View₁))
          (.inl .status) >>= fun C => pure (decide (C = C₀ κ))) (sA, rσ) =
        pure (decide (A.initial κ = C₀ κ)) := by
    intro sA rσ hcor
    erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
      pure_bind, Machine.runFrom_pure, map_pure, hcor]
    exact congrArg pure (decide_eq_decide.mpr Iff.rfl)
  have hinner : ∀ (sσ : (σ.machine κ).State),
      (Machine.closeProgram (ProbOracleComp.sample (do
          let sA ← (liftAdaptiveAdversary (A.machine κ)).init
          pure (sA,
            { inner := σ.applyInitialCorruptions κ (A.initial κ) sσ
              corrupted := A.initial κ
              trace := fun i =>
                [σ.view κ i (σ.applyInitialCorruptions κ (A.initial κ) sσ)] })) >>= fun s =>
        Prod.fst <$> ((liftAdaptiveAdversary (A.machine κ)).comp
          (adaptiveRouter mode σ κ (A.initial κ))).runFrom
          (ProbOracleComp.query
            (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ₁)
              (AdaptiveNetR SubOut NR₁ View₁))
            (.inl .status) >>= fun C => pure (decide (C = C₀ κ))) s)).eval =
        PMF.pure (decide (A.initial κ = C₀ κ)) := fun sσ => by
    rw [ProbOracleComp.sample_bind, bind_assoc, Machine.closeProgram_bind, ProbComp.eval_bind,
      Machine.closeProgram_sample]
    have hstep : ∀ sA : (liftAdaptiveAdversary (A.machine κ)).State,
        (Machine.closeProgram (ProbOracleComp.sample (pure (sA,
            { inner := σ.applyInitialCorruptions κ (A.initial κ) sσ
              corrupted := A.initial κ
              trace := fun i =>
                [σ.view κ i (σ.applyInitialCorruptions κ (A.initial κ) sσ)] })) >>= fun s =>
          Prod.fst <$> ((liftAdaptiveAdversary (A.machine κ)).comp
            (adaptiveRouter mode σ κ (A.initial κ))).runFrom
            (ProbOracleComp.query
              (spec := adaptiveExecSpec n SubIn SubOut (AdaptiveNetQ n SubIn NQ₁)
                (AdaptiveNetR SubOut NR₁ View₁))
              (.inl .status) >>= fun C => pure (decide (C = C₀ κ))) s)).eval =
          PMF.pure (decide (A.initial κ = C₀ κ)) := fun sA => by
      rw [ProbOracleComp.sample_pure, pure_bind, hrun sA _ rfl, Machine.closeProgram_pure,
        ProbComp.eval_pure]
    simp only [hstep, PMF.bind_const]
  exact (congrArg (PMF.bind (ProbComp.eval (σ.machine κ).init)) (funext hinner)).trans
    (PMF.bind_const _ _)

open Classical in
private theorem adaptiveAdvantage_compose_dummy_le (mode : CorruptionMode)
    (C₀ : ℕ → Finset (Fin n))
    {ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ}
    {π : AdaptiveProtocol n SubIn SubOut NQ₁ NR₁ View₁}
    {φ : AdaptiveProtocol n SubIn SubOut NQ₂ NR₂ View₂}
    (hρ_view : ρ.ViewStableOnCorrupt) (hπ_view : π.ViewStableOnCorrupt)
    (hφ_view : φ.ViewStableOnCorrupt)
    (S_D : AdaptiveAdversary n SubIn SubOut NQ₂ NR₂ View₂
      (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁))
    (Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₁) (AdaptiveHybridView Viewρ View₁)))
    {pρ pZ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (hZ : Z.PolyBounded pZ)
    (κ : ℕ) (z : List Bool) :
    ∃ Z' : AdaptiveEnvironment n SubIn SubOut (AdaptiveNetQ n SubIn NQ₁)
        (AdaptiveNetR SubOut NR₁ View₁),
      Z'.PolyBounded (absorbAdaptiveCheckPoly pZ pρ) ∧
      adaptiveAdvantage mode (composeAdaptive ρ π) (composeAdaptive ρ φ)
        (adaptiveDummyAdversary C₀ _ _) (adaptiveHybridSim mode C₀ S_D) Z κ z ≤
        adaptiveAdvantage mode π φ (adaptiveDummyAdversary C₀ _ _) S_D Z' κ z := by
  by_cases hinit : S_D.initial κ = C₀ κ
  · let ZT := absorbAdaptiveHybridCheck mode C₀ ρ Z true
    let ZF := absorbAdaptiveHybridCheck mode C₀ ρ Z false
    have hZT : ZT.PolyBounded (absorbAdaptiveCheckPoly pZ pρ) :=
      absorbAdaptiveHybridCheck_polyBounded mode C₀ hρ hZ true
    have hZF : ZF.PolyBounded (absorbAdaptiveCheckPoly pZ pρ) :=
      absorbAdaptiveHybridCheck_polyBounded mode C₀ hρ hZ false
    let g₁ := (adaptiveExec mode (composeAdaptive ρ π) (adaptiveDummyAdversary C₀ _ _) Z κ z).eval
    let g₂ := (adaptiveExec mode (composeAdaptive ρ φ) (adaptiveHybridSim mode C₀ S_D) Z κ z).eval
    let advT := adaptiveAdvantage mode π φ (adaptiveDummyAdversary C₀ _ _) S_D ZT κ z
    let advF := adaptiveAdvantage mode π φ (adaptiveDummyAdversary C₀ _ _) S_D ZF κ z
    have hT_real : (g₁ true).toReal - (g₂ true).toReal ≤ (advT : ℝ) := by
      have h1 : g₁ true =
          (adaptiveExec mode π (adaptiveDummyAdversary C₀ _ _) ZT κ z).eval true :=
        (eval_absorbAdaptiveHybridCheck_dummy mode C₀ ρ π hρ_view hπ_view Z true κ z).symm
      have h2 : (adaptiveExec mode φ S_D ZT κ z).eval true ≤ g₂ true :=
        closeEval_absorbAdaptiveHybridCheck_le mode C₀ ρ φ hρ_view hφ_view S_D Z true κ z hinit
      have h2r : ((adaptiveExec mode φ S_D ZT κ z).eval true).toReal ≤ (g₂ true).toReal :=
        ENNReal.toReal_mono (PMF.apply_ne_top _ _) h2
      have hadv : (advT : ℝ) =
          |(g₁ true).toReal - ((adaptiveExec mode φ S_D ZT κ z).eval true).toReal| := by
        dsimp only [advT]
        rw [adaptiveAdvantage, Game.coe_advantage, Game.coe_succProbability,
          Game.coe_succProbability, ← h1]
      have hsub := (abs_sub_le_iff.mp hadv.symm.le).1
      linarith
    have hF_real : (g₂ true).toReal - (g₁ true).toReal ≤ (advF : ℝ) := by
      have hsum_pmf : ∀ g : PMF Bool, (g true).toReal + (g false).toReal = 1 := by
        intro g
        have h := congrArg ((↑) : ℝ≥0 → ℝ) (Game.succProbability_add_failProbability g)
        rw [NNReal.coe_add, NNReal.coe_one, Game.coe_succProbability] at h
        simpa [Game.failProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] using h
      have hsum₁ := hsum_pmf g₁
      have hsum₂ := hsum_pmf g₂
      have h1 : g₁ false =
          (adaptiveExec mode π (adaptiveDummyAdversary C₀ _ _) ZF κ z).eval true :=
        (eval_absorbAdaptiveHybridCheck_dummy mode C₀ ρ π hρ_view hπ_view Z false κ z).symm
      have h2 : (adaptiveExec mode φ S_D ZF κ z).eval true ≤ g₂ false :=
        closeEval_absorbAdaptiveHybridCheck_le mode C₀ ρ φ hρ_view hφ_view S_D Z false κ z hinit
      have h2r : ((adaptiveExec mode φ S_D ZF κ z).eval true).toReal ≤ (g₂ false).toReal :=
        ENNReal.toReal_mono (PMF.apply_ne_top _ _) h2
      have hadv : (advF : ℝ) =
          |(g₁ false).toReal - ((adaptiveExec mode φ S_D ZF κ z).eval true).toReal| := by
        dsimp only [advF]
        rw [adaptiveAdvantage, Game.coe_advantage, Game.coe_succProbability,
          Game.coe_succProbability, ← h1]
      have hsub := (abs_sub_le_iff.mp hadv.symm.le).1
      linarith
    by_cases hTF : advT ≤ advF
    · refine ⟨ZF, hZF, ?_⟩
      rw [← NNReal.coe_le_coe]
      change (Game.advantage g₁ g₂ : ℝ) ≤ advF
      rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability]
      exact abs_sub_le_iff.mpr ⟨hT_real.trans (NNReal.coe_le_coe.mpr hTF), hF_real⟩
    · refine ⟨ZT, hZT, ?_⟩
      rw [← NNReal.coe_le_coe]
      change (Game.advantage g₁ g₂ : ℝ) ≤ advT
      rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability]
      exact abs_sub_le_iff.mpr
        ⟨hT_real, hF_real.trans (NNReal.coe_le_coe.mpr (le_of_not_ge hTF))⟩
  · refine ⟨initCheckEnv C₀, query_status_polyBounded pZ pρ C₀, ?_⟩
    have hadv1 : adaptiveAdvantage mode π φ (adaptiveDummyAdversary C₀ _ _) S_D
        (initCheckEnv C₀) κ z = 1 := by
      rw [adaptiveAdvantage, eval_exec_initCheckEnv, eval_exec_initCheckEnv]
      dsimp only [adaptiveDummyAdversary]
      simp only [decide_true, hinit, decide_false]
      rw [Game.advantage_pure_true_left]
      simp [Game.failProbability]
    rw [hadv1]
    exact Game.advantage_le_one _ _

/-! ### Exact composition regrouping under `CorruptSync` -/

private theorem closeEval_bind_le_of_mem_support {α β : Type}
    (p : ProbOracleComp OracleSpec.empty α)
    (f g : α → ProbOracleComp OracleSpec.empty β) (y : β)
    (h : ∀ a ∈ (closeEval p).support, closeEval (f a) y ≤ closeEval (g a) y) :
    closeEval (p >>= f) y ≤ closeEval (p >>= g) y := by
  rw [Machine.closeEval_bind, Machine.closeEval_bind, PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ (closeEval p).support
  · exact mul_le_mul_of_nonneg_left (h a ha) zero_le
  · have hzero : (closeEval p) a = 0 := by
      simpa only [PMF.mem_support_iff, ne_eq, not_not] using ha
    simp [hzero]

private theorem closeEval_adaptiveRouter_liftSubParty_le {γ : Type}
    (mode : CorruptionMode) (φ : AdaptiveProtocol n SubIn SubOut NQ NR View₂) (κ : ℕ)
    (C₀ : Finset (Fin n)) (prog : ProbOracleComp (partySpec n SubIn SubOut) γ)
    (rφ : AdaptiveRouterState (φ.machine κ).State View₂ n)
    (f g : γ × AdaptiveRouterState (φ.machine κ).State View₂ n → ProbOracleComp OracleSpec.empty β)
    (y : β)
    (hfg : ∀ a rφ', rφ'.corrupted = rφ.corrupted →
      closeEval (f (a, rφ')) y ≤ closeEval (g (a, rφ')) y) :
    closeEval ((adaptiveRouter mode φ κ C₀).runFrom
        (liftSubParty (AdvQ := AdaptiveNetQ n SubIn NQ) (AdvR := AdaptiveNetR SubOut NR View₂)
          prog) rφ >>= f) y ≤
      closeEval ((adaptiveRouter mode φ κ C₀).runFrom
        (liftSubParty (AdvQ := AdaptiveNetQ n SubIn NQ) (AdvR := AdaptiveNetR SubOut NR View₂)
          prog) rφ >>= g) y := by
  induction prog using OracleComp.induction generalizing rφ with
  | pure a =>
    erw [liftSubParty, OracleComp.interpret_pure, Machine.runFrom_pure, pure_bind, pure_bind]
    exact hfg a rφ rfl
  | query_bind q k ih =>
    simp only [PFunctor.FreeM.bind_eq_bind]
    rcases q with c | p
    · have hstep : ∀ (h : γ × AdaptiveRouterState (φ.machine κ).State View₂ n →
          ProbOracleComp OracleSpec.empty β),
          ((adaptiveRouter mode φ κ C₀).runFrom
            (liftSubParty (AdvQ := AdaptiveNetQ n SubIn NQ) (AdvR := AdaptiveNetR SubOut NR View₂)
              (OracleComp.query (.inl c) >>= k)) rφ >>= h) =
            ProbOracleComp.sample (OracleComp.query c) >>= fun b =>
              ((adaptiveRouter mode φ κ C₀).runFrom
                (liftSubParty (AdvQ := AdaptiveNetQ n SubIn NQ)
                  (AdvR := AdaptiveNetR SubOut NR View₂) (k b)) rφ >>= h) := by
        intro h
        erw [liftSubParty, OracleComp.interpret_bind, OracleComp.interpret_query,
          Machine.runFrom_bind, Machine.runFrom_sample _ (OracleComp.query c), bind_map_left,
          bind_assoc]
      rw [hstep f, hstep g]
      exact Machine.closeEval_bind_le _ _ _ y fun b => ih b rφ hfg
    · have hstep : ∀ (h : γ × AdaptiveRouterState (φ.machine κ).State View₂ n →
          ProbOracleComp OracleSpec.empty β),
          ((adaptiveRouter mode φ κ C₀).runFrom
            (liftSubParty (AdvQ := AdaptiveNetQ n SubIn NQ) (AdvR := AdaptiveNetR SubOut NR View₂)
              (OracleComp.query (.inr p) >>= k)) rφ >>= h) =
            ((adaptiveRouter mode φ κ C₀).handle (.inl (.party p.1 p.2))).run rφ >>= fun x =>
              ((adaptiveRouter mode φ κ C₀).runFrom
                (liftSubParty (AdvQ := AdaptiveNetQ n SubIn NQ)
                  (AdvR := AdaptiveNetR SubOut NR View₂) (k x.1)) x.2 >>= h) := by
        intro h
        erw [liftSubParty, OracleComp.interpret_bind, OracleComp.interpret_query,
          Machine.runFrom_bind, Machine.runFrom_query, bind_assoc]
        rfl
      rw [hstep f, hstep g]
      refine closeEval_bind_le_of_mem_support _ _ _ y fun ⟨r, rφ'⟩ hr => ?_
      have hcorr : rφ'.corrupted = rφ.corrupted := by
        dsimp only [adaptiveRouter, StateT.run] at hr
        split_ifs at hr
        · rw [(Prod.mk.inj (Machine.mem_support_closeEval_pure.mp hr)).2]
        · rcases Machine.mem_support_closeEval_bind.mp hr with ⟨⟨_, _⟩, _, hr'⟩
          rw [(Prod.mk.inj (Machine.mem_support_closeEval_pure.mp hr')).2]; rfl
      exact ih r rφ' (fun a rφ'' h'' => hfg a rφ'' (h''.trans hcorr))

open Classical in
private theorem closeEval_absorbAdaptiveHybrid_le_check (mode : CorruptionMode)
    (C₀ : ℕ → Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (φ : AdaptiveProtocol n SubIn SubOut NQ₂ NR₂ View₂)
    (S_D : AdaptiveAdversary n SubIn SubOut NQ₂ NR₂ View₂
      (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁))
    (hSync : S_D.CorruptSync mode C₀ φ)
    (Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₁) (AdaptiveHybridView Viewρ View₁)))
    (target : Bool) (κ : ℕ) (z : List Bool) :
    (adaptiveExec mode φ S_D (absorbAdaptiveHybrid mode C₀ ρ Z) κ z).eval target ≤
      (adaptiveExec mode φ S_D (absorbAdaptiveHybridCheck mode C₀ ρ Z target) κ z).eval true := by
  have hinit : S_D.initial κ = C₀ κ := congrFun hSync.1 κ
  change closeEval ((adaptiveExecMachine mode φ S_D κ).link
      (absorbAdaptiveHybrid mode C₀ ρ Z κ z)) target ≤
    closeEval ((adaptiveExecMachine mode φ S_D κ).link
      (absorbAdaptiveHybridCheck mode C₀ ρ Z target κ z)) true
  dsimp only [Machine.run, Machine.link, adaptiveExecMachine]
  have hinitS : ((liftAdaptiveAdversary (S_D.machine κ)).comp
      (adaptiveRouter mode φ κ (S_D.initial κ))).init = (do
      let sφ ← (φ.machine κ).init
      let sS ← (S_D.machine κ).init
      pure (sS,
        { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ
          corrupted := C₀ κ
          trace := fun i => [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ)] })) := by
    dsimp only [Machine.comp, liftAdaptiveAdversary, Machine.liftRight, adaptiveRouter]
    rw [hinit, bind_assoc]
    rfl
  have hinitS_eval (prog : ProbOracleComp _ Bool) (b : Bool) :
      ((ProbComp.eval ((liftAdaptiveAdversary (S_D.machine κ)).comp
          (adaptiveRouter mode φ κ (S_D.initial κ))).init).bind fun s =>
        closeEval (Prod.fst <$> ((liftAdaptiveAdversary (S_D.machine κ)).comp
          (adaptiveRouter mode φ κ (S_D.initial κ))).runFrom prog s)) b =
      ((ProbComp.eval (φ.machine κ).init).bind fun sφ₀ =>
        (ProbComp.eval (S_D.machine κ).init).bind fun sS₀ =>
          closeEval (Prod.fst <$> ((liftAdaptiveAdversary (S_D.machine κ)).comp
            (adaptiveRouter mode φ κ (S_D.initial κ))).runFrom prog
            (sS₀, { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                    corrupted := C₀ κ
                    trace := fun i =>
                      [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ₀)] }))) b := by
    erw [hinitS, ProbComp.eval_bind, PMF.bind_bind]
    refine congrArg (fun f => PMF.bind (ProbComp.eval (φ.machine κ).init) f b)
      (funext fun sφ₀ => ?_)
    erw [ProbComp.eval_bind, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun sS₀ => ?_)
    erw [ProbComp.eval_pure, PMF.pure_bind]
  rw [closeEval_bind, closeEval_bind, closeEval_sample, hinitS_eval, hinitS_eval]
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun sφ₀ => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun sS₀ => mul_le_mul_of_nonneg_left ?_ zero_le
  have hchk :
      ((liftAdaptiveAdversary (S_D.machine κ)).comp
          (adaptiveRouter mode φ κ (S_D.initial κ))).runFrom
        (absorbAdaptiveHybridCheck mode C₀ ρ Z target κ z)
        (sS₀, { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                corrupted := C₀ κ
                trace := fun i =>
                  [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ₀)] }) =
      ((liftAdaptiveAdversary (S_D.machine κ)).comp
          (adaptiveRouter mode φ κ (S_D.initial κ))).runFrom
        (do
          let sInit ← ProbOracleComp.sample
            (absorbAdaptiveCheckMachine mode (C₀ κ) ρ κ).init
          let res ← (absorbAdaptiveCheckMachine mode (C₀ κ) ρ κ).runFrom (Z κ z) sInit
          pure (!res.2.desynced && res.1 == target))
        (sS₀, { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                corrupted := C₀ κ
                trace := fun i =>
                  [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ₀)] }) := by
    dsimp only [absorbAdaptiveHybridCheck]
    erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
      pure_bind]
    erw [ite_eq_right_iff.mpr (fun h => absurd rfl h)]
    rfl
  let Inner :=
    (liftAdaptiveAdversary (S_D.machine κ)).comp (adaptiveRouter mode φ κ (S_D.initial κ))
  let M₁ := (absorbAdaptiveMachine (NQ := NQ₁) (NR := NR₁) (View₁ := View₁)
    mode (C₀ κ) ρ κ).comp Inner
  let M₂ := (absorbAdaptiveCheckMachine (NQ := NQ₁) (NR := NR₁) (View₁ := View₁)
    mode (C₀ κ) ρ κ).comp Inner
  let rφ₀ : AdaptiveRouterState (φ.machine κ).State View₂ n :=
    { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
      corrupted := C₀ κ
      trace := fun i => [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ₀)] }
  have hinitAbs : (absorbAdaptiveMachine (NQ := NQ₁) (NR := NR₁) (View₁ := View₁)
      mode (C₀ κ) ρ κ).init = (do
      let s₀ ← (ρ.machine κ).init
      pure { inner := ρ.applyInitialCorruptions κ (C₀ κ) s₀
             corrupted := C₀ κ
             trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) s₀)] }) := rfl
  have hinitChk : (absorbAdaptiveCheckMachine (NQ := NQ₁) (NR := NR₁) (View₁ := View₁)
      mode (C₀ κ) ρ κ).init = (do
      let s₀ ← (ρ.machine κ).init
      pure { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) s₀
                        corrupted := C₀ κ
                        trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) s₀)] }
             desynced := false }) := rfl
  have hbool : ∀ (p : ProbOracleComp OracleSpec.empty Bool),
      closeEval p target = closeEval (p >>= fun b => pure (b == target)) true := by
    intro p
    rw [closeEval_bind, PMF.bind_apply]
    have h1 : (fun a : Bool => (closeEval p) a * (closeEval (pure (a == target))) true) =
        fun a => if a = target then (closeEval p) target else 0 := by
      ext a; cases a <;> cases target <;> simp [closeEval_pure]
    rw [h1, tsum_ite_eq]
  have hL_eval :
      closeEval (Prod.fst <$> Inner.runFrom (absorbAdaptiveHybrid mode C₀ ρ Z κ z)
          (sS₀, rφ₀)) target =
        ((ProbComp.eval (ρ.machine κ).init).bind fun sρ₀ =>
          closeEval (M₁.runFrom (Z κ z)
            ({ inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
               corrupted := C₀ κ
               trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] },
             (sS₀, rφ₀)) >>= fun x => pure (x.1 == target))) true := by
    rw [hbool]
    dsimp only [absorbAdaptiveHybrid, Machine.link]
    rw [hinitAbs]
    erw [ProbOracleComp.sample_bind, Machine.runFrom_bind, Machine.runFrom_bind,
      Machine.runFrom_sample, bind_map_left, bind_map_left, bind_assoc, bind_assoc,
      closeEval_bind, closeEval_sample]
    refine congrArg (fun f => PMF.bind (ProbComp.eval (ρ.machine κ).init) f true)
      (funext fun sρ₀ => ?_)
    erw [ProbOracleComp.sample_pure, Machine.runFrom_pure, pure_bind]
    have hfst : ∀ {α β : Type} (x : α) (y : β), (x, y).1 = x := fun _ _ => rfl
    have hsnd : ∀ {α β : Type} (x : α) (y : β), (x, y).2 = y := fun _ _ => rfl
    repeat erw [hfst]
    repeat erw [hsnd]
    erw [Machine.runFrom_map, bind_map_left,
      Machine.runFrom_comp (absorbAdaptiveMachine (NQ := NQ₁) (NR := NR₁) (View₁ := View₁)
        mode (C₀ κ) ρ κ) Inner,
      bind_map_left]
    rfl
  have hR_eval :
      closeEval (Prod.fst <$> Inner.runFrom (absorbAdaptiveHybridCheck mode C₀ ρ Z target κ z)
          (sS₀, rφ₀)) true =
        ((ProbComp.eval (ρ.machine κ).init).bind fun sρ₀ =>
          closeEval (M₂.runFrom (Z κ z)
            ({ outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                          corrupted := C₀ κ
                          trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] }
               desynced := false },
             (sS₀, rφ₀)) >>= fun x => pure (!x.2.1.desynced && (x.1 == target)))) true := by
    rw [hchk, hinitChk]
    erw [ProbOracleComp.sample_bind, Machine.runFrom_bind, Machine.runFrom_bind,
      Machine.runFrom_sample, bind_map_left, bind_assoc, map_bind, closeEval_bind, closeEval_sample]
    refine congrArg (fun f => PMF.bind (ProbComp.eval (ρ.machine κ).init) f true)
      (funext fun sρ₀ => ?_)
    erw [ProbOracleComp.sample_pure, Machine.runFrom_pure, pure_bind]
    have hfst : ∀ {α β : Type} (x : α) (y : β), (x, y).1 = x := fun _ _ => rfl
    have hsnd : ∀ {α β : Type} (x : α) (y : β), (x, y).2 = y := fun _ _ => rfl
    repeat erw [hfst]
    repeat erw [hsnd]
    erw [Machine.runFrom_bind, map_bind]
    have hcomp2 :
        (Inner.runFrom ((absorbAdaptiveCheckMachine (NQ := NQ₁) (NR := NR₁) (View₁ := View₁)
            mode (C₀ κ) ρ κ).runFrom (Z κ z)
            { outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                         corrupted := C₀ κ
                         trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] }
              desynced := false }) (sS₀, rφ₀) >>= fun x =>
            Prod.fst <$> Inner.runFrom (pure (!x.1.2.desynced && (x.1.1 == target))) x.2) =
          (M₂.runFrom (Z κ z)
            ({ outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                          corrupted := C₀ κ
                          trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] }
               desynced := false },
             (sS₀, rφ₀)) >>= fun x => pure (!x.2.1.desynced && (x.1 == target))) := by
      erw [Machine.runFrom_comp (absorbAdaptiveCheckMachine (NQ := NQ₁) (NR := NR₁)
        (View₁ := View₁) mode (C₀ κ) ρ κ) Inner, bind_map_left]
      refine bind_congr fun x => ?_
      erw [Machine.runFrom_pure, map_pure]
      rfl
    rw [hcomp2]
  change closeEval (Prod.fst <$> Inner.runFrom (absorbAdaptiveHybrid mode C₀ ρ Z κ z)
      (sS₀, rφ₀)) target ≤
    closeEval (Prod.fst <$> Inner.runFrom (absorbAdaptiveHybridCheck mode C₀ ρ Z target κ z)
      (sS₀, rφ₀)) true
  rw [hL_eval, hR_eval, PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun sρ₀ => mul_le_mul_of_nonneg_left ?_ zero_le
  have hgoal : closeEval (M₁.runFrom (Z κ z)
        ({ inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
           corrupted := C₀ κ
           trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] },
         (sS₀, { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                 corrupted := C₀ κ
                 trace := fun i => [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ₀)] })) >>=
        fun x => pure (x.1 == target)) true ≤
      closeEval (M₂.runFrom (Z κ z)
        ({ outer := { inner := ρ.applyInitialCorruptions κ (C₀ κ) sρ₀
                      corrupted := C₀ κ
                      trace := fun i => [ρ.view κ i (ρ.applyInitialCorruptions κ (C₀ κ) sρ₀)] }
           desynced := false },
         (sS₀, { inner := φ.applyInitialCorruptions κ (C₀ κ) sφ₀
                 corrupted := C₀ κ
                 trace := fun i => [φ.view κ i (φ.applyInitialCorruptions κ (C₀ κ) sφ₀)] })) >>=
        fun x => pure (!x.2.1.desynced && (x.1 == target))) true := by
    let R : M₁.State → M₂.State → Prop := fun s₁ s₂ =>
      s₁.1 = s₂.1.outer ∧ s₂.1.desynced = false ∧ s₁.2 = s₂.2 ∧
      s₁.2.2.corrupted = s₁.1.corrupted ∧ C₀ κ ⊆ s₁.2.2.corrupted
    refine Machine.closeEval_runFrom_le_intertwine M₁ M₂ (fun _ => True) R (fun _ => False) (Z κ z)
      (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
      _ _ ⟨rfl, rfl, rfl, rfl, Finset.Subset.rfl⟩
      (fun x => pure (x.1 == target)) (fun x => pure (!x.2.1.desynced && (x.1 == target))) true
      (fun a s₁ s₂ hR => by simp [hR.2.1])
      (fun _ _ h => False.elim h) (fun _ _ _ _ h _ => False.elim h) ?_
    intro q ⟨rρ₁, ⟨sS₁, rφ₁⟩⟩ ⟨⟨rρ₂, des₂⟩, ⟨sS₂, rφ₂⟩⟩ k₁ k₂ _
      ⟨ho, hdes, hs, hc, hsub⟩ hcont _
    dsimp only at ho hdes hs hc hsub
    subst ho; subst hdes
    rcases Prod.mk.inj hs with ⟨hsS, hrφ⟩; subst hsS; subst hrφ
    dsimp only [M₁, M₂, Inner]
    erw [machine_comp_handle_run, machine_comp_handle_run]
    rcases q with (⟨i, x⟩ | _) | (⟨i, x⟩ | i | (q | (⟨j, subX⟩ | nq)))
    · erw [absorbAdaptiveCheckMachine_handle_inl_party]
      conv_lhs => dsimp only [absorbAdaptiveMachine, StateT.run]
      by_cases hi : i ∈ rρ₁.corrupted
      · simp only [hi, ↓reduceIte]
        erw [Machine.runFrom_pure, Machine.runFrom_pure, map_pure, map_pure,
          Equiv.prodAssoc_apply, Equiv.prodAssoc_apply, pure_bind, pure_bind]
        exact hcont none _ _ ⟨rfl, rfl, rfl, hc, hsub⟩
      · simp only [hi, ↓reduceIte]
        conv_lhs =>
          erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_comp, bind_map_left,
            runFrom_liftAdaptiveAdversary_liftSubParty, Machine.runFrom_map, bind_map_left]
        conv_rhs =>
          erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_comp, bind_map_left,
            runFrom_liftAdaptiveAdversary_liftSubParty, Machine.runFrom_map, bind_map_left]
        refine closeEval_adaptiveRouter_liftSubParty_le mode φ κ (S_D.initial κ) _ rφ₁ _ _ true ?_
        intro ⟨out, s'⟩ rφ' hC
        erw [Machine.runFrom_pure, Machine.runFrom_pure, map_pure, map_pure,
          Equiv.prodAssoc_apply, Equiv.prodAssoc_apply, pure_bind, pure_bind]
        exact hcont out _ _ ⟨rfl, rfl, rfl, hC.trans hc, hC ▸ hsub⟩
    · erw [absorbAdaptiveCheckMachine_handle_inl_status, Machine.runFrom_pure]
      conv_lhs => dsimp only [absorbAdaptiveMachine, StateT.run]
      erw [Machine.runFrom_pure,
        map_pure, map_pure, Equiv.prodAssoc_apply, Equiv.prodAssoc_apply, pure_bind, pure_bind]
      exact hcont rρ₁.corrupted _ _ ⟨rfl, rfl, rfl, hc, hsub⟩
    · erw [absorbAdaptiveCheckMachine_handle_inr_party]
      conv_lhs => dsimp only [absorbAdaptiveMachine, StateT.run]
      by_cases hi : i ∈ rρ₁.corrupted
      · simp only [hi, ↓reduceIte]
        conv_lhs =>
          erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_comp, bind_map_left,
            runFrom_liftAdaptiveAdversary_liftSubParty, Machine.runFrom_map, bind_map_left]
        conv_rhs =>
          erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_comp, bind_map_left,
            runFrom_liftAdaptiveAdversary_liftSubParty, Machine.runFrom_map, bind_map_left]
        refine closeEval_adaptiveRouter_liftSubParty_le mode φ κ (S_D.initial κ) _ rφ₁ _ _ true ?_
        intro ⟨out, s'⟩ rφ' hC
        erw [Machine.runFrom_pure, Machine.runFrom_pure, map_pure, map_pure,
          Equiv.prodAssoc_apply, Equiv.prodAssoc_apply, pure_bind, pure_bind]
        exact hcont (.party out) _ _ ⟨rfl, rfl, rfl, hC.trans hc, hC ▸ hsub⟩
      · simp only [hi, ↓reduceIte]
        erw [Machine.runFrom_pure, Machine.runFrom_pure, map_pure, map_pure,
          Equiv.prodAssoc_apply, Equiv.prodAssoc_apply, pure_bind, pure_bind]
        exact hcont (.party none) _ _ ⟨rfl, rfl, rfl, hc, hsub⟩
    · cases mode
      · erw [absorbAdaptiveCheckMachine_handle_inr_corrupt_static]
        conv_lhs => dsimp only [absorbAdaptiveMachine, StateT.run]
        by_cases hi : i ∈ rρ₁.corrupted
        · simp only [hi, ↓reduceIte]
          conv_lhs =>
            erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_query,
              machine_comp_handle_run, bind_map_left, liftAdaptiveAdversary_handle_inr]
            dsimp only
          conv_rhs =>
            erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_query,
              machine_comp_handle_run, bind_map_left, liftAdaptiveAdversary_handle_inr]
            dsimp only
          refine closeEval_bind_le_of_mem_support _ _ _ true fun ⟨⟨rSub, sS'⟩, rφ'⟩ hmem => ?_
          have hC : rφ'.corrupted = rφ₁.corrupted := by
            simpa [← hinit] using hSync.2 κ (.corrupt i) sS₁ rφ₁ hsub _ hmem
          conv_lhs =>
            erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
            dsimp only
          conv_rhs =>
            erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
              pure_bind, Equiv.prodAssoc_apply]
            dsimp only
          refine hcont _ _ _ ?_
          exact ⟨rfl,
            by rw [hC, hc]; exact (Bool.false_or _).trans (decide_eq_false (not_not.mpr rfl)),
            rfl, hC.trans hc, hC ▸ hsub⟩
        · simp only [hi, ↓reduceIte]
          erw [Machine.runFrom_pure, Machine.runFrom_pure, map_pure, map_pure,
            Equiv.prodAssoc_apply, Equiv.prodAssoc_apply, pure_bind, pure_bind]
          exact hcont (.corrupt none) _ _ ⟨rfl, rfl, rfl, hc, hsub⟩
      · erw [absorbAdaptiveCheckMachine_handle_inr_corrupt_adaptive]
        conv_lhs => dsimp only [absorbAdaptiveMachine, StateT.run]
        conv_lhs =>
          erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_query,
            machine_comp_handle_run, bind_map_left, liftAdaptiveAdversary_handle_inr]
          dsimp only
        conv_rhs =>
          erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_query,
            machine_comp_handle_run, bind_map_left, liftAdaptiveAdversary_handle_inr]
          dsimp only
        refine closeEval_bind_le_of_mem_support _ _ _ true fun ⟨⟨rSub, sS'⟩, rφ'⟩ hmem => ?_
        have hC : rφ'.corrupted = insert i rφ₁.corrupted := by
          simpa [← hinit] using hSync.2 κ (.corrupt i) sS₁ rφ₁ hsub _ hmem
        conv_lhs =>
          erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
          dsimp only
        conv_rhs =>
          erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
            pure_bind, Equiv.prodAssoc_apply]
          dsimp only
        have hs'_cor : (if i ∈ rρ₁.corrupted then rρ₁
            else { inner := ρ.onCorrupt κ i rρ₁.inner, corrupted := insert i rρ₁.corrupted,
                   trace := rρ₁.trace }).corrupted = insert i rρ₁.corrupted := by
          by_cases hi : i ∈ rρ₁.corrupted <;> simp [hi, Finset.insert_eq_of_mem]
        refine hcont _ _ _ ?_
        exact ⟨rfl,
          by
            erw [hC, hc, hs'_cor]
            exact (Bool.false_or _).trans (decide_eq_false (not_not.mpr rfl)),
          rfl, hC.trans (by erw [hc, hs'_cor]), hsub.trans (hC ▸ Finset.subset_insert _ _)⟩
    · erw [absorbAdaptiveCheckMachine_handle_inr_net_inl]
      conv_lhs => dsimp only [absorbAdaptiveMachine, StateT.run]
      conv_lhs =>
        erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_comp, bind_map_left,
          runFrom_liftAdaptiveAdversary_liftSubParty, Machine.runFrom_map, bind_map_left]
      conv_rhs =>
        erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_comp, bind_map_left,
          runFrom_liftAdaptiveAdversary_liftSubParty, Machine.runFrom_map, bind_map_left]
      refine closeEval_adaptiveRouter_liftSubParty_le mode φ κ (S_D.initial κ) _ rφ₁ _ _ true ?_
      intro ⟨r, s'⟩ rφ' hC
      erw [Machine.runFrom_pure, Machine.runFrom_pure, map_pure, map_pure,
        Equiv.prodAssoc_apply, Equiv.prodAssoc_apply, pure_bind, pure_bind]
      exact hcont (.net (.inl r)) _ _ ⟨rfl, rfl, rfl, hC.trans hc, hC ▸ hsub⟩
    · erw [absorbAdaptiveCheckMachine_handle_inr_net_inr_inl]
      conv_lhs =>
        dsimp only [absorbAdaptiveMachine, StateT.run, StateT.lift]
        erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_map,
          Machine.runFrom_query, machine_comp_handle_run, bind_map_left,
          liftAdaptiveAdversary_handle_inr, bind_map_left]
        dsimp only
      conv_rhs =>
        erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_query,
          machine_comp_handle_run, bind_map_left, liftAdaptiveAdversary_handle_inr]
        dsimp only
      refine closeEval_bind_le_of_mem_support _ _ _ true fun ⟨⟨rSub, sS'⟩, rφ'⟩ hmem => ?_
      have hC : rφ'.corrupted = rφ₁.corrupted := by
        simpa [← hinit] using hSync.2 κ (.party j subX) sS₁ rφ₁ hsub _ hmem
      conv_lhs =>
        erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
        dsimp only
      conv_rhs =>
        erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
          pure_bind, Equiv.prodAssoc_apply]
        dsimp only
      refine hcont (.net (.inr (subNetReplyToRouted rSub))) _ _ ?_
      exact ⟨rfl, by rw [hC, hc]; exact (Bool.false_or _).trans (decide_eq_false (not_not.mpr rfl)),
        rfl, hC.trans hc, hC ▸ hsub⟩
    · erw [absorbAdaptiveCheckMachine_handle_inr_net_inr_inr]
      conv_lhs =>
        dsimp only [absorbAdaptiveMachine, StateT.run, StateT.lift]
        erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_map,
          Machine.runFrom_query, machine_comp_handle_run, bind_map_left,
          liftAdaptiveAdversary_handle_inr, bind_map_left]
        dsimp only
      conv_rhs =>
        erw [Machine.runFrom_bind, map_bind, bind_assoc, Machine.runFrom_query,
          machine_comp_handle_run, bind_map_left, liftAdaptiveAdversary_handle_inr]
        dsimp only
      refine closeEval_bind_le_of_mem_support _ _ _ true fun ⟨⟨rSub, sS'⟩, rφ'⟩ hmem => ?_
      have hC : rφ'.corrupted = rφ₁.corrupted := by
        simpa [← hinit] using hSync.2 κ (.net nq) sS₁ rφ₁ hsub _ hmem
      conv_lhs =>
        erw [Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply, pure_bind]
        dsimp only
      conv_rhs =>
        erw [Machine.runFrom_bind, Machine.runFrom_query, adaptiveExecMachine_handle_inl_status,
          pure_bind, Equiv.prodAssoc_apply]
        dsimp only
      refine hcont (.net (.inr (subNetReplyToRouted rSub))) _ _ ?_
      exact ⟨rfl, by rw [hC, hc]; exact (Bool.false_or _).trans (decide_eq_false (not_not.mpr rfl)),
        rfl, hC.trans hc, hC ▸ hsub⟩
  exact hgoal

/-- Execution regrouping for the composed simulator under `CorruptSync` in the snapshot adaptive
model: running `composeAdaptive ρ φ` against `adaptiveHybridSim mode C₀ S_D` and `Z` induces the
same Boolean distribution as running `φ` against `S_D` and `absorbAdaptiveHybrid mode C₀ ρ Z`. -/
theorem eval_adaptiveExec_compose_sim (mode : CorruptionMode) (C₀ : ℕ → Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (φ : AdaptiveProtocol n SubIn SubOut NQ₂ NR₂ View₂)
    (hρ_view : ρ.ViewStableOnCorrupt) (hφ_view : φ.ViewStableOnCorrupt)
    (S_D : AdaptiveAdversary n SubIn SubOut NQ₂ NR₂ View₂
      (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁))
    (hSync : S_D.CorruptSync mode C₀ φ)
    (Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₁) (AdaptiveHybridView Viewρ View₁)))
    (κ : ℕ) (z : List Bool) :
    (adaptiveExec mode (composeAdaptive ρ φ) (adaptiveHybridSim mode C₀ S_D) Z κ z).eval =
      (adaptiveExec mode φ S_D (absorbAdaptiveHybrid mode C₀ ρ Z) κ z).eval := by
  have hle : ∀ b : Bool,
      (adaptiveExec mode φ S_D (absorbAdaptiveHybrid mode C₀ ρ Z) κ z).eval b ≤
        (adaptiveExec mode (composeAdaptive ρ φ) (adaptiveHybridSim mode C₀ S_D) Z κ z).eval b :=
    fun b => (closeEval_absorbAdaptiveHybrid_le_check mode C₀ ρ φ S_D hSync Z b κ z).trans
      (closeEval_absorbAdaptiveHybridCheck_le mode C₀ ρ φ hρ_view hφ_view S_D Z b κ z
        (congrFun hSync.1 κ))
  refine PMF.ext fun b => ?_
  have hp : ∀ (p q : PMF Bool), p true ≤ q true → p false ≤ q false → p b = q b := by
    intro p q ht hf
    have hsum_pmf : ∀ g : PMF Bool, (g true).toReal + (g false).toReal = 1 := by
      intro g
      have h := congrArg ((↑) : ℝ≥0 → ℝ) (Game.succProbability_add_failProbability g)
      rw [NNReal.coe_add, NNReal.coe_one, Game.coe_succProbability] at h
      simpa [Game.failProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] using h
    have hp1 := hsum_pmf p
    have hq1 := hsum_pmf q
    have ht_real : (p true).toReal ≤ (q true).toReal :=
      ENNReal.toReal_mono (PMF.apply_ne_top _ _) ht
    have hf_real : (p false).toReal ≤ (q false).toReal :=
      ENNReal.toReal_mono (PMF.apply_ne_top _ _) hf
    rw [← ENNReal.ofReal_toReal (p.apply_ne_top b), ← ENNReal.ofReal_toReal (q.apply_ne_top b)]
    congr 1
    cases b <;> linarith
  exact (hp _ _ (hle true) (hle false)).symm

/-- Advantage regrouping under `CorruptSync` in the snapshot adaptive model. -/
theorem adaptiveAdvantage_compose (mode : CorruptionMode) (C₀ : ℕ → Finset (Fin n))
    (ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ)
    (π : AdaptiveProtocol n SubIn SubOut NQ₁ NR₁ View₁)
    (φ : AdaptiveProtocol n SubIn SubOut NQ₂ NR₂ View₂)
    (hρ_view : ρ.ViewStableOnCorrupt) (hπ_view : π.ViewStableOnCorrupt)
    (hφ_view : φ.ViewStableOnCorrupt)
    (S_D : AdaptiveAdversary n SubIn SubOut NQ₂ NR₂ View₂
      (AdaptiveNetQ n SubIn NQ₁) (AdaptiveNetR SubOut NR₁ View₁))
    (hSync : S_D.CorruptSync mode C₀ φ)
    (Z : AdaptiveEnvironment n In Out
      (AdaptiveNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (AdaptiveNetR Out (NetR ⊕ RoutedNetR SubOut NR₁) (AdaptiveHybridView Viewρ View₁)))
    (κ : ℕ) (z : List Bool) :
    adaptiveAdvantage mode (composeAdaptive ρ π) (composeAdaptive ρ φ)
      (adaptiveDummyAdversary C₀ _ _) (adaptiveHybridSim mode C₀ S_D) Z κ z =
      adaptiveAdvantage mode π φ (adaptiveDummyAdversary C₀ _ _) S_D
        (absorbAdaptiveHybrid mode C₀ ρ Z) κ z := by
  rw [adaptiveAdvantage, adaptiveExec_compose_dummy mode C₀ ρ π hρ_view hπ_view Z κ z,
    eval_adaptiveExec_compose_sim mode C₀ ρ φ hρ_view hφ_view S_D hSync Z κ z,
    adaptiveAdvantage]

/-- Concrete composition for `AdaptiveEmulatesDummyWithin`, this library's snapshot, call-bounded,
fixed-`n`-party, adaptive-corruption dummy-adversary emulation notion (a step toward
[Canetti2020]-style adaptive composition, not [Canetti2020] Theorem 3 or §7.1.1's write-once
storage and coin-exposure model; #6043). Requires `ViewStableOnCorrupt` on all three protocols
(vacuous when `.memory = .erasing`) and evaluates `ε` at `absorbAdaptiveCheckPoly pZ pρ`, whose
extra status queries rule out simulator initial-corruption and runtime-corruption desynchronization
without assuming an explicit `CorruptSync` condition. -/
theorem AdaptiveEmulatesDummyWithin.compose {mode : CorruptionMode}
    {ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ}
    {π : AdaptiveProtocol n SubIn SubOut NQ₁ NR₁ View₁}
    {φ : AdaptiveProtocol n SubIn SubOut NQ₂ NR₂ View₂}
    {pρ pD : Polynomial ℕ} {ε : Polynomial ℕ → ℕ → ℝ≥0}
    (hρ_view : ρ.ViewStableOnCorrupt) (hπ_view : π.ViewStableOnCorrupt)
    (hφ_view : φ.ViewStableOnCorrupt)
    (hρ : ρ.PolyBounded pρ) (h : AdaptiveEmulatesDummyWithin mode π φ pD ε) :
    AdaptiveEmulatesDummyWithin mode (composeAdaptive ρ π) (composeAdaptive ρ φ)
      (pD + 1) (fun pZ => ε (absorbAdaptiveCheckPoly pZ pρ)) := by
  intro C₀
  obtain ⟨S_D, hS, hadv⟩ := h C₀
  refine ⟨adaptiveHybridSim mode C₀ S_D, adaptiveHybridSim_polyBounded mode C₀ hS,
    fun Z pZ hZ κ z => ?_⟩
  obtain ⟨Z', hZ', hle⟩ := adaptiveAdvantage_compose_dummy_le mode C₀ hρ_view hπ_view hφ_view S_D Z
    hρ hZ κ z
  exact hle.trans (hadv Z' (absorbAdaptiveCheckPoly pZ pρ) hZ' κ z)

/-- Concrete composition for `AdaptiveEmulatesWithin`, this library's snapshot, call-bounded,
fixed-`n`-party, adaptive-corruption port-model emulation notion (not [Canetti2020] Theorem 3 or
§7.1.1's write-once non-erasing storage and PPT ITMs; #6043). -/
theorem AdaptiveEmulatesWithin.compose {mode : CorruptionMode}
    {ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ}
    {π : AdaptiveProtocol n SubIn SubOut NQ₁ NR₁ View₁}
    {φ : AdaptiveProtocol n SubIn SubOut NQ₂ NR₂ View₂}
    {pρ g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (hρ_view : ρ.ViewStableOnCorrupt) (hπ_view : π.ViewStableOnCorrupt)
    (hφ_view : φ.ViewStableOnCorrupt)
    (hρ : ρ.PolyBounded pρ) (h : AdaptiveEmulatesWithin mode π φ g ε) :
    AdaptiveEmulatesWithin mode (composeAdaptive ρ π) (composeAdaptive ρ φ)
      (Polynomial.X * (g.comp (Polynomial.X + 1) + 1 + 1) + (g.comp (Polynomial.X + 1) + 1))
      (fun pA pZ => ε 1 (absorbAdaptiveCheckPoly (absorbPoly pZ pA) pρ)) :=
  (h.emulatesDummyWithin.compose hρ_view hπ_view hφ_view hρ).emulatesWithin

/-- Asymptotic composition for `AdaptiveEmulates`, this library's snapshot, call-bounded,
fixed-`n`-party, adaptive-corruption port-model emulation notion (not [Canetti2020] Theorem 3 or
§7.1.1's write-once non-erasing storage and PPT ITMs; #6043). -/
theorem AdaptiveEmulates.compose {mode : CorruptionMode}
    {ρ : AdaptiveHybridProtocol n In Out NetQ NetR SubIn SubOut Viewρ}
    {π : AdaptiveProtocol n SubIn SubOut NQ₁ NR₁ View₁}
    {φ : AdaptiveProtocol n SubIn SubOut NQ₂ NR₂ View₂}
    {pρ : Polynomial ℕ}
    (hρ_view : ρ.ViewStableOnCorrupt) (hπ_view : π.ViewStableOnCorrupt)
    (hφ_view : φ.ViewStableOnCorrupt)
    (hρ : ρ.PolyBounded pρ) (h : AdaptiveEmulates mode π φ) :
    AdaptiveEmulates mode (composeAdaptive ρ π) (composeAdaptive ρ φ) := by
  rw [adaptiveEmulates_iff_adaptiveEmulatesDummy] at h ⊢
  intro C₀
  obtain ⟨S_D, pD, hS, hadv⟩ := h C₀
  refine ⟨adaptiveHybridSim mode C₀ S_D, pD + 1, adaptiveHybridSim_polyBounded mode C₀ hS,
    fun pZ => ?_⟩
  obtain ⟨ν, hν, hbound⟩ := hadv (absorbAdaptiveCheckPoly pZ pρ)
  refine ⟨ν, hν, fun Z hZ κ z => ?_⟩
  obtain ⟨Z', hZ', hle⟩ := adaptiveAdvantage_compose_dummy_le mode C₀ hρ_view hπ_view hφ_view S_D Z
    hρ hZ κ z
  exact hle.trans (hbound Z' hZ' κ z)

end Cslib.Crypto.Protocols.UC
