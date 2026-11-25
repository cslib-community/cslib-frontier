/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.MultiSession
import CslibFrontier.Crypto.Protocols.SSP.ParFinLazy
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution

/-!
# Universal composition with joint state (step theorems and lazy multi-session functionality)

This module defines the named data structures (`SubSessionInput`, `SubSessionBackdoor`,
`MultiSessionState`), the lazy multi-session extension `IdealFunctionality.multiSession` (`F̂`),
the sub-session relabelling `MultiHybridProtocol.toJoint`, the explicit demultiplexing and
multiplexing adversaries `jointDemux` and `jointMux`, and the fixed-session step theorems
`EmulatesWithin.toJoint_multiSession` and `EmulatesWithin.multiSession_toJoint` for this
library's call-bounded, static-corruption port-model emulation notions (`UC.EmulatesWithin`,
`UC.Emulates`, `UC.Realizes`).

These form the relabelling and execution-equivalence steps toward Theorem 1 (Universal
Composition with Joint State) of [CanettiRabin2003] (CRYPTO 2003, LNCS 2729: §3,
"The Composition Operation"; §3, "The Multi-session Extension of an Ideal Functionality"; Theorem 1;
and the proof of Theorem 1, definition of `π̃`), adapted to a fixed finite session count `m`, static
corruptions, pull-only execution, and this library's call-bounded statistical model (see
`Cslib.Crypto.Protocols.UC.Emulates` for the call-budget model vs. PPT ITMs).

The generic lazy-vs-eager parallel-package initialization theorem (`SSP.parFinLazy`,
`SSP.run_parFinLazy_eq_parFin`) lives separately in `CslibFrontier.Crypto.Protocols.SSP.ParFinLazy`
(`SSP.Basic` supplies `UC.Machine` via `UC.Linking`), so SSP callers can import the bridge
without importing the UC ideal-functionality or execution modules.

## Modelling decisions and differences from [CanettiRabin2003]

1. **Named structures (zero projection chains).** `SubSessionInput`, `SubSessionBackdoor`, and
   `MultiSessionState` replace raw nested products and options.
2. **Lazy multi-session extension `F.multiSession` ([CanettiRabin2003], §3, "The Multi-session
   Extension of an Ideal Functionality").** For any `[DecidableEq SSID]`,
   `IdealFunctionality.multiSession SSID F` stores `(secParam, corrupted, sessions)` and creates a
   fresh copy of `F` with `F.init secParam corrupted` on the first party input or backdoor query
   for a given `ssid`, keeping distinct `ssid`s independent.
3. **Pull-model interface and scheduling differences.** In [CanettiRabin2003], §3, "The
   Multi-session Extension of an Ideal Functionality", whenever a copy of `F` sends `(ssid, v)` to
   some party `Pi`, `F̂` sends `(sid, ssid, v)` to `Pi` and sends `ssid` to the adversary. Here,
   `IdealFunctionality.multiSession` returns an untagged `Option SubOut` on the selected pull query
   `SubSessionInput SSID SubIn`, and provides an explicitly queried backdoor interface
   (`SubSessionBackdoor SSID BackQ`) returning `BackR` (exposing no raw copy state) rather than
   sending adversary notifications on honest-party activations or outputs. Because the interfaces,
   scheduling, and call-bounded vs. PPT ITM resource models differ, no implication between
   `Realizes` for this pull API and the source premise is claimed here.
4. **Sub-session relabelling `toJoint` and fixed `m`.** `MultiHybridProtocol.toJoint` relabels each
   `SubSessionCall` `⟨session, party, input⟩` as `(party, ⟨session, input⟩)` (adapting
   [CanettiRabin2003], §3, "The Composition Operation", and the proof of Theorem 1, definition of
   `π̃`, to a fixed finite `Fin m` family; dynamic `SID` creation and push-model tagged outputs /
   `ssid` notifications are out of scope).
5. **Explicit demux/mux adversaries under static corruption.** `jointDemux` and `jointMux`
   translate network queries between the single-protocol `F̂`-hybrid interface and the `m`-session
   `composeMulti` interface while preserving replies (`NetR ⊕ RoutedNetR SubOut BackR`). Static
   corruptions `C : Finset (Fin n)` are shared across `ρ`, all copies of `F`, and `ρ̂`, so
   corrupted-party internal state translation ([CanettiRabin2003], item 3 of the proof of Theorem 1)
   is unneeded.
6. **Lazy-vs-eager equivalence via `SSP.ParFinLazy`.** The proof of
   `exec_compose_toJoint_multiSession` uses `SSP.run_parFinLazy_eq_parFin` from
   `CslibFrontier.Crypto.Protocols.SSP.ParFinLazy` to bridge lazy first-touch initialization and
   eager `SSP.parFin` sampling.
7. **Scope and joint state vs. global setup.** Joint state here is internal to a single subroutine
   protocol `ρ̂`, not a GUC/EUC global setup shared outside `ρ̂`. Structural isolation and
   unrestricted compliance hold by types (`OracleSpec.empty` closed machines and `SubSessionCall`).

## Main definitions

* `Cslib.Crypto.Protocols.UC.SubSessionInput`, `Cslib.Crypto.Protocols.UC.SubSessionBackdoor`,
  `Cslib.Crypto.Protocols.UC.MultiSessionState`: named data structures for multi-session
  functionalities.
* `Cslib.Crypto.Protocols.UC.IdealFunctionality.multiSession`: lazy multi-session extension `F̂`.
* `Cslib.Crypto.Protocols.UC.MultiHybridProtocol.toJoint`: relabelling `π̃` targeting `F̂`.
* `Cslib.Crypto.Protocols.UC.demuxNetQuery`, `Cslib.Crypto.Protocols.UC.muxNetQuery`,
  `Cslib.Crypto.Protocols.UC.jointDemux`, `Cslib.Crypto.Protocols.UC.jointMux`: explicit
  demultiplexing and multiplexing adversaries.

## Main results

* `Cslib.Crypto.Protocols.UC.toJoint_polyBounded`,
  `Cslib.Crypto.Protocols.UC.jointDemux_polyBounded`,
  `Cslib.Crypto.Protocols.UC.jointMux_polyBounded`: call-budget preservation.
* `Cslib.Crypto.Protocols.UC.exec_compose_toJoint_multiSession`,
  `Cslib.Crypto.Protocols.UC.exec_composeMulti_toJoint`: exact execution identities between
  `compose ρ.toJoint (F.multiSession (Fin m)).toProtocol` and `composeMulti ρ F.toProtocol`.
* `Cslib.Crypto.Protocols.UC.EmulatesWithin.toJoint_multiSession`,
  `Cslib.Crypto.Protocols.UC.EmulatesWithin.multiSession_toJoint`: fixed-session concrete
  emulation steps in both directions with zero error and `Polynomial.X` overhead.

## References

* [R. Canetti and T. Rabin, *Universal Composition with Joint State*][CanettiRabin2003], CRYPTO
  2003, LNCS 2729 (§3, "The Composition Operation"; §3, "The Multi-session Extension of an Ideal
  Functionality"; Theorem 1 (Universal Composition with Joint State); and the proof of Theorem 1,
  definition of `π̃`).
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open scoped NNReal

/-! ### Named structures and lazy multi-session functionality -/

/-- A party input to a multi-session functionality or joint-state protocol: sub-session `ssid`
with value `input` ([CanettiRabin2003], §3, "The Multi-session Extension of an Ideal
Functionality", the `(ssid, v)` part of `(sid, ssid, v)`). -/
structure SubSessionInput (SSID SubIn : Type) : Type where
  /-- Sub-session identifier. -/
  ssid : SSID
  /-- Party input (or poll token) for sub-session `ssid`. -/
  input : SubIn
  deriving DecidableEq

/-- An adversary backdoor query to copy `ssid` of the multi-session functionality. -/
structure SubSessionBackdoor (SSID BackQ : Type) : Type where
  /-- Target sub-session identifier. -/
  ssid : SSID
  /-- Backdoor query for sub-session `ssid`. -/
  query : BackQ
  deriving DecidableEq

/-- State of `F.multiSession`: the security parameter and corrupted set recorded at invocation
(so that copies can be created later) and the lazily created copies. -/
structure MultiSessionState (n : ℕ) (SSID FState : Type) : Type where
  /-- Security parameter fixed at functionality invocation. -/
  secParam : ℕ
  /-- Static corruption set fixed at functionality invocation. -/
  corrupted : Finset (Fin n)
  /-- Lazily initialized per-session states (`none` until first message). -/
  sessions : SSID → Option FState

/-- Multi-session extension `F̂` of an ideal functionality `F` for any `[DecidableEq SSID]`:
creates a fresh copy of `F` with `F.init secParam corrupted` on the first party input or backdoor
query for `ssid`, and activates that copy ([CanettiRabin2003], §3, "The Multi-session Extension of
an Ideal Functionality"). Unlike the source's `F̂` (which sends `(sid, ssid, v)` to `Pi` and sends
`ssid` to the adversary when a copy sends `(ssid, v)`), this pull API returns an untagged
`Option SubOut` on the selected pull and
provides an explicitly queried backdoor interface (`SubSessionBackdoor SSID BackQ`) returning
`BackR`, exposing no raw copy state. -/
@[expose] def IdealFunctionality.multiSession {n : ℕ} {SubIn SubOut BackQ BackR : Type}
    (SSID : Type) [DecidableEq SSID]
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) :
    IdealFunctionality n (SubSessionInput SSID SubIn) SubOut
      (SubSessionBackdoor SSID BackQ) BackR where
  State := MultiSessionState n SSID F.State
  init κ C := pure { secParam := κ, corrupted := C, sessions := fun _ => none }
  onInput i req s := do
    let fState ← match s.sessions req.ssid with
      | some st => pure st
      | none => F.init s.secParam s.corrupted
    let (out, fState') ← (F.onInput i req.input).run fState
    return (out, { s with sessions := Function.update s.sessions req.ssid (some fState') })
  onBackdoor req s := do
    let fState ← match s.sessions req.ssid with
      | some st => pure st
      | none => F.init s.secParam s.corrupted
    let (resp, fState') ← (F.onBackdoor req.query).run fState
    return (resp, { s with sessions := Function.update s.sessions req.ssid (some fState') })

/-! ### Sub-session relabelling and explicit demux/mux adversaries -/

/-- Relabel a multi-session hybrid protocol `ρ` (`SubSessionCall` subroutine calls) to a
single-subroutine `HybridProtocol` targeting `F.multiSession (Fin m)` ([CanettiRabin2003], §3,
"The Composition Operation", and the proof of Theorem 1, definition of `π̃`). -/
@[expose] def MultiHybridProtocol.toJoint {m n : ℕ} {In Out NetQ NetR SubIn SubOut : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut) :
    HybridProtocol n In Out NetQ NetR (SubSessionInput (Fin m) SubIn) SubOut :=
  fun κ C =>
    { State := (ρ κ C).State
      init := (ρ κ C).init
      handle := fun q s =>
        OracleComp.interpret
          (sumHandler
            (fun k => OracleComp.query
              (spec := probOracleSpec (partySpec n (SubSessionInput (Fin m) SubIn) SubOut))
              (Sum.inl k))
            fun c => do
              ProbOracleComp.query
                (spec := partySpec n (SubSessionInput (Fin m) SubIn) SubOut)
                (c.party, ⟨c.session, c.input⟩))
          (((ρ κ C).handle q).run s) }

/-- Library infrastructure (no cited result): relabelling `ρ` via `toJoint` preserves its polynomial
call budget `pρ` unchanged. -/
theorem toJoint_polyBounded {m n : ℕ} {In Out NetQ NetR SubIn SubOut : Type}
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut} {pρ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) : (ρ.toJoint).PolyBounded pρ := fun κ C => by
  refine ⟨(hρ κ C).1, fun q s => ?_⟩
  refine OracleComp.IsCostBounded.interpret (fun r => ?_) ((hρ κ C).2 q s)
  cases r with
  | inl k => exact OracleComp.IsCostBounded.query (Sum.inl k)
  | inr c => exact OracleComp.IsCostBounded.query _

/-- Library construction (no cited definition): translate a network query of the `F̂`-hybrid
execution (`compose ρ.toJoint F̂`) to the corresponding network query of the `m`-session execution
(`composeMulti ρ F.toProtocol`), keeping replies identical. -/
@[expose] def demuxNetQuery {m n : ℕ} {In NetQ SubIn BackQ : Type} :
    RoutedNetQ n In (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn)
      (SubSessionBackdoor (Fin m) BackQ)) →
      RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
  | .inl p => .inl p
  | .inr (.inl q) => .inr (.outer q)
  | .inr (.inr (.inl (i, req))) => .inr (.sub req.ssid (.inl (i, req.input)))
  | .inr (.inr (.inr req)) => .inr (.sub req.ssid (.inr req.query))

/-- Library construction (no cited definition): inverse network query translation from the
`m`-session interface (`composeMulti ρ F.toProtocol`) to the `F̂`-hybrid interface
(`compose ρ.toJoint F̂`). -/
@[expose] def muxNetQuery {m n : ℕ} {In NetQ SubIn BackQ : Type} :
    RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ)) →
      RoutedNetQ n In (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn)
        (SubSessionBackdoor (Fin m) BackQ))
  | .inl p => .inl p
  | .inr (.outer q) => .inr (.inl q)
  | .inr (.sub j (.inl (i, x))) => .inr (.inr (.inl (i, ⟨j, x⟩)))
  | .inr (.sub j (.inr bq)) => .inr (.inr (.inr ⟨j, bq⟩))

private theorem demuxNetQuery_muxNetQuery {m n : ℕ} {In NetQ SubIn BackQ : Type}
    (q : RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))) :
    demuxNetQuery (muxNetQuery q) = q := by
  rcases q with p | q | ⟨j, ⟨i, x⟩ | bq⟩ <;> rfl

/-- Translate the network query interface of a machine via `f` without modifying replies or
state. -/
private def mapNetMachine {NQ₁ NQ₂ R AdvQ AdvR : Type} (f : NQ₁ → NQ₂)
    (A : Machine (netSpec NQ₁ R) (netSpec AdvQ AdvR)) :
    Machine (netSpec NQ₂ R) (netSpec AdvQ AdvR) where
  State := A.State
  init := A.init
  handle q s :=
    OracleComp.interpret
      (sumHandler
        (fun k => OracleComp.query (spec := probOracleSpec (netSpec NQ₂ R)) (Sum.inl k))
        fun nq => do ProbOracleComp.query (spec := netSpec NQ₂ R) (f nq))
      ((A.handle q).run s)

private theorem isBounded_mapNetMachine {NQ₁ NQ₂ R AdvQ AdvR : Type} (f : NQ₁ → NQ₂)
    {A : Machine (netSpec NQ₁ R) (netSpec AdvQ AdvR)} {t : ℕ} (h : A.IsBounded t) :
    (mapNetMachine f A).IsBounded t := by
  refine ⟨h.1, fun q s => ?_⟩
  refine OracleComp.IsCostBounded.interpret (fun r => ?_) (h.2 q s)
  cases r with
  | inl k => exact OracleComp.IsCostBounded.query (Sum.inl k)
  | inr nq => exact OracleComp.IsCostBounded.query (Sum.inr (f nq))

/-- Library construction (no cited result): explicit demultiplexing adversary for
`compose ρ.toJoint (F.multiSession (Fin m)).toProtocol` running against
`composeMulti ρ F.toProtocol` ([CanettiRabin2003], §3, "The Composition Operation", and the proof
of Theorem 1). -/
def jointDemux {m n : ℕ} {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    (A : ExecAdversary n In Out
      (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR) :
    ExecAdversary n In Out (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR :=
  fun κ C => mapNetMachine demuxNetQuery (A κ C)

/-- Library construction (no cited result): explicit multiplexing adversary in the reverse
direction, mapping `composeMulti ρ F.toProtocol` queries to
`compose ρ.toJoint (F.multiSession (Fin m)).toProtocol`. -/
def jointMux {m n : ℕ} {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    (A : ExecAdversary n In Out (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR) :
    ExecAdversary n In Out
      (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR :=
  fun κ C => mapNetMachine muxNetQuery (A κ C)

/-- Library infrastructure (no cited result): `jointDemux A` preserves `A`'s polynomial call budget
`pA`. -/
theorem jointDemux_polyBounded {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    {A : ExecAdversary n In Out
      (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR}
    {pA : Polynomial ℕ} (hA : A.PolyBounded pA) : (jointDemux A).PolyBounded pA :=
  fun κ C => isBounded_mapNetMachine demuxNetQuery (hA κ C)

/-- Library infrastructure (no cited result): `jointMux A` preserves `A`'s polynomial call budget
`pA`. -/
theorem jointMux_polyBounded {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    {A : ExecAdversary n In Out (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR}
    {pA : Polynomial ℕ} (hA : A.PolyBounded pA) : (jointMux A).PolyBounded pA :=
  fun κ C => isBounded_mapNetMachine muxNetQuery (hA κ C)

/-! ### Execution identities and concrete step theorems -/

section DemuxProof

private def mapRightHandler {ιL ιR₁ ιR₂ : Type} {L : ιL → Type}
    {R : ιR₂ → Type} (f : ιR₁ → ιR₂) :
    (q : ιL ⊕ ιR₁) → ProbOracleComp (L ⊕ₒ R) ((L ⊕ₒ (R ∘ f)) q)
  | .inl p => ProbOracleComp.query (spec := L ⊕ₒ R) (.inl p)
  | .inr r => ProbOracleComp.query (spec := L ⊕ₒ R) (.inr (f r))

private theorem link_liftAdversary_mapNetMachine {n : ℕ} {In Out NQ₁ NQ₂ R AdvQ AdvR α : Type}
    (f : NQ₁ → NQ₂) (A : Machine (netSpec NQ₁ R) (netSpec AdvQ AdvR))
    (prog : ProbOracleComp (execSpec n In Out AdvQ AdvR) α) :
    (liftAdversary (n := n) (In := In) (Out := Out) (mapNetMachine f A)).link prog =
      ProbOracleComp.simulate (mapRightHandler (L := partySpec n In Out) (R := netSpec NQ₂ R) f)
        ((liftAdversary (n := n) (In := In) (Out := Out) A).link prog) := by
  simp only [Machine.link, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_map,
    ProbOracleComp.simulate_sample]
  refine congrArg _ (funext fun s => ?_)
  induction prog using OracleComp.induction generalizing s with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [PFunctor.FreeM.bind_eq_bind]
    erw [Machine.runFrom_bind, Machine.runFrom_bind, ProbOracleComp.simulate_bind]
    cases q with
    | inl k =>
      rw [← ProbOracleComp.sample_unifFin]
      erw [Machine.runFrom_sample, Machine.runFrom_sample]
      rw [ProbOracleComp.simulate_map, ProbOracleComp.simulate_sample]
      simp only [bind_map_left, map_bind]
      exact bind_congr fun a => ih a s
    | inr e =>
      cases e with
      | inl p =>
        erw [Machine.runFrom_query, Machine.runFrom_query]
        dsimp only [liftAdversary, Machine.liftRight, mapNetMachine] at s ⊢
        rw [StateT.run_lift, StateT.run_lift, bind_pure_comp, bind_pure_comp,
          ProbOracleComp.simulate_map, ProbOracleComp.simulate_query]
        simp only [mapRightHandler, bind_map_left, map_bind]
        exact bind_congr fun a => ih a s
      | inr adv =>
        erw [Machine.runFrom_query, Machine.runFrom_query]
        dsimp only [liftAdversary, Machine.liftRight, mapNetMachine, StateT.run] at s ⊢
        have hint : Machine.liftRightProgram (partySpec n In Out)
            (OracleComp.interpret
              (sumHandler
                (fun k => OracleComp.query (spec := probOracleSpec (netSpec NQ₂ R)) (Sum.inl k))
                fun nq => ProbOracleComp.query (spec := netSpec NQ₂ R) (f nq))
              ((A.handle adv).run s)) =
            ProbOracleComp.simulate
              (mapRightHandler (L := partySpec n In Out) (R := netSpec NQ₂ R) f)
              (Machine.liftRightProgram (partySpec n In Out) ((A.handle adv).run s)) := by
          dsimp only [Machine.liftRightProgram, ProbOracleComp.simulate]
          rw [OracleComp.substitute_eq_interpret]
          erw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
          congr 1 with r : 1
          cases r with
          | inl k => erw [OracleComp.interpret_query]
          | inr nq => rfl
        erw [hint, map_bind, map_bind]
        exact bind_congr fun x => ih x.1 x.2

private def relabelSessionHandler {m n : ℕ} {SubIn SubOut BackQ BackR : Type} :
    (q : Fin m × ((Fin n × SubIn) ⊕ RoutedNetQ n SubIn BackQ)) →
      ProbOracleComp (protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
        (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
        (RoutedNetR SubOut BackR))
        ((SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn BackQ)
          (RoutedNetR SubOut BackR))) q)
  | (j, .inl (i, x)) => ProbOracleComp.query (Sum.inl (i, ⟨j, x⟩))
  | (j, .inr (.inl (i, x))) => ProbOracleComp.query (Sum.inr (Sum.inl (i, ⟨j, x⟩)))
  | (j, .inr (.inr bq)) => ProbOracleComp.query (Sum.inr (Sum.inr ⟨j, bq⟩))

private def relabelSessionProg {m n : ℕ} {SubIn SubOut BackQ BackR α : Type}
    (prog : ProbOracleComp
      (SSP.sessionSpec m
        (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn BackQ) (RoutedNetR SubOut BackR))) α) :
    ProbOracleComp
      (protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
        (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
        (RoutedNetR SubOut BackR)) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
          (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
          (RoutedNetR SubOut BackR)))
        (Sum.inl k))
      relabelSessionHandler)
    prog

private theorem interpret_liftParty_toJoint {m n : ℕ} {SubIn SubOut BackQ BackR α : Type}
    (prog : ProbOracleComp (multiPartySpec m n SubIn SubOut) α) :
    liftParty (NetQ := RoutedNetQ n (SubSessionInput (Fin m) SubIn)
        (SubSessionBackdoor (Fin m) BackQ))
      (NetR := RoutedNetR SubOut BackR)
      (OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query
            (spec := probOracleSpec (partySpec n (SubSessionInput (Fin m) SubIn) SubOut))
            (Sum.inl k))
          fun c => ProbOracleComp.query
            (spec := partySpec n (SubSessionInput (Fin m) SubIn) SubOut)
            (c.party, ⟨c.session, c.input⟩))
        prog) =
      relabelSessionProg
        (liftMultiParty (NQ := RoutedNetQ n SubIn BackQ) (NR := RoutedNetR SubOut BackR) prog) := by
  dsimp only [liftParty, liftMultiParty, relabelSessionProg]
  erw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
  congr 1 with r : 1
  cases r with
  | inl k => rfl
  | inr c =>
    dsimp only [sumHandler]
    erw [OracleComp.interpret_query]

private theorem link_toJoint_eq_relabelSessionProg {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR α : Type}
    (C : Finset (Fin n)) (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (κ : ℕ)
    (prog : ProbOracleComp
      (protocolSpec n In Out
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn)
          (SubSessionBackdoor (Fin m) BackQ)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut BackR))) α) :
    (routeCorrupt C
        (hybridWrap (NQ := RoutedNetQ n (SubSessionInput (Fin m) SubIn)
          (SubSessionBackdoor (Fin m) BackQ))
          (NR := RoutedNetR SubOut BackR) (ρ.toJoint κ C))).link prog =
      relabelSessionProg
        ((routeCorrupt C
          (multiHybridWrap (NQ := RoutedNetQ n SubIn BackQ) (NR := RoutedNetR SubOut BackR)
            (ρ κ C))).link
          (ProbOracleComp.simulate
            (mapRightHandler (L := partySpec n In Out)
              (R := netSpec (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ)))
                (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut BackR)))
              demuxNetQuery)
            prog)) := by
  simp only [Machine.link]
  rw [relabelSessionProg, OracleComp.interpret_bind, ProbOracleComp.interpret_sample,
    ← OracleComp.substitute_eq_interpret]
  refine congrArg (ProbOracleComp.sample (ρ κ C).init >>= ·) (funext fun sρ => ?_)
  rw [OracleComp.interpret_map]
  refine congrArg (Prod.fst <$> ·) ?_
  dsimp only [routeCorrupt, hybridWrap, multiHybridWrap, MultiHybridProtocol.toJoint] at sρ
  induction prog using OracleComp.induction generalizing sρ with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind, ProbOracleComp.simulate_bind]
    erw [Machine.runFrom_bind, Machine.runFrom_bind, OracleComp.interpret_bind]
    cases q with
    | inl k =>
      rw [← ProbOracleComp.sample_unifFin]
      erw [ProbOracleComp.simulate_sample, Machine.runFrom_sample, Machine.runFrom_sample,
        OracleComp.interpret_map, ProbOracleComp.interpret_sample]
      rw [(OracleComp.substitute_eq_interpret _ _).symm, bind_map_left]
      exact bind_congr fun a => ih a sρ
    | inr e =>
      cases e with
      | inl p =>
        erw [ProbOracleComp.simulate_query]; dsimp only [mapRightHandler]
        erw [Machine.runFrom_query, Machine.runFrom_query]
        by_cases hp : p.1 ∈ C
        · simp only [routeCorrupt, hp, ↓reduceIte, StateT.run]
          erw [OracleComp.interpret_pure, pure_bind]; exact ih none sρ
        · simp only [routeCorrupt, hp, ↓reduceIte, hybridWrap, multiHybridWrap,
            MultiHybridProtocol.toJoint, StateT.run]
          erw [interpret_liftParty_toJoint (((ρ κ C).handle (.inl p)).run sρ)]
          exact bind_congr fun x => ih x.1 x.2
      | inr nq =>
        erw [ProbOracleComp.simulate_query]; dsimp only [mapRightHandler]
        rcases nq with ⟨i, x⟩ | q | ⟨i, req⟩ | req
        · simp only [demuxNetQuery]; erw [Machine.runFrom_query, Machine.runFrom_query]
          by_cases hi : i ∈ C
          · simp only [routeCorrupt, hi, ↓reduceIte, hybridWrap, multiHybridWrap,
              MultiHybridProtocol.toJoint]
            repeat erw [StateT.run_map]
            simp only [StateT.run]
            erw [interpret_liftParty_toJoint (((ρ κ C).handle (.inl (i, x))).run sρ),
              OracleComp.interpret_map, bind_map_left, bind_map_left]
            exact bind_congr fun p => ih (Sum.inl p.1) p.2
          · simp only [routeCorrupt, hi, ↓reduceIte, StateT.run]
            erw [OracleComp.interpret_pure, pure_bind]; exact ih (.inl none) sρ
        · simp only [demuxNetQuery]; erw [Machine.runFrom_query, Machine.runFrom_query]
          simp only [routeCorrupt, hybridWrap, multiHybridWrap, MultiHybridProtocol.toJoint]
          simp only [StateT.run_map]; simp only [StateT.run]
          erw [liftParty_map, liftMultiParty_map,
            interpret_liftParty_toJoint (((ρ κ C).handle (.inr q)).run sρ),
            OracleComp.interpret_map, OracleComp.interpret_map]
          simp only [Functor.map_map, bind_map_left]
          exact bind_congr fun (x : NetR × _) => ih (Sum.inr (Sum.inl x.1)) x.2
        all_goals
          simp only [demuxNetQuery]; erw [Machine.runFrom_query, Machine.runFrom_query]
          simp only [routeCorrupt, hybridWrap, multiHybridWrap]
          repeat erw [StateT.run_map]
          repeat erw [StateT.run_lift]
          simp only [bind_pure_comp, Functor.map_map, bind_map_left]
          erw [OracleComp.interpret_map, OracleComp.interpret_query]
          dsimp only [sumHandler, relabelSessionHandler]; rw [bind_map_left]
          exact bind_congr fun r => ih (Sum.inr (Sum.inr r)) sρ

private def stripCorruptHandler {n : ℕ} {In Out NetQ NetR : Type} (C : Finset (Fin n))
    (q : (Fin n × In) ⊕ RoutedNetQ n In NetQ) :
    ProbOracleComp (protocolSpec n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))
      (protocolSpec n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR) q) :=
  let qy := ProbOracleComp.query
    (spec := protocolSpec n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))
  match q with
  | .inl (i, x) => if i ∈ C then pure none else qy (.inl (i, x))
  | .inr (.inl (i, x)) => if i ∈ C then qy (.inr (.inl (i, x))) else pure (.inl none)
  | .inr (.inr q) => qy (.inr (.inr q))

private theorem run_corruptRouter_stripCorruptHandler {n : ℕ}
    {In Out NetQ NetR α : Type} (C : Finset (Fin n))
    (P : Machine OracleSpec.empty (protocolSpec n In Out NetQ NetR))
    (prog : ProbOracleComp
      (protocolSpec n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) α) :
    (corruptRouter C P).run (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec
          (protocolSpec n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))) (.inl k))
          (stripCorruptHandler C)) prog) =
      (corruptRouter C P).run prog := by
  refine Machine.run_interpret_stripNoop (corruptRouter C P) (stripCorruptHandler C)
    (fun q s => ?_) prog
  rcases q with ⟨i, x⟩ | ⟨⟨i, x⟩ | q⟩ <;> dsimp only [stripCorruptHandler]
  · by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
    · simp only [corruptRouter, hi, ↓reduceIte]; rfl
    · exact Machine.runFrom_query _ _ _
  · by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
    · exact Machine.runFrom_query _ _ _
    · simp only [corruptRouter, hi, ↓reduceIte]; rfl
  · exact Machine.runFrom_query _ _ _

private theorem handle_corruptRouter_multiSession_inl {m n : ℕ}
    {SubIn SubOut BackQ BackR : Type}
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) (C : Finset (Fin n)) (κ : ℕ)
    (j : Fin m) (i : Fin n) (x : SubIn) (hi : i ∉ C) (s : Fin m → Option F.State) :
    ((corruptRouter C ((F.multiSession (Fin m)).toProtocol κ C)).handle (.inl (i, ⟨j, x⟩))).run
        (MultiSessionState.mk κ C s) =
      Prod.map _root_.id (MultiSessionState.mk κ C) <$>
        ((SSP.parFinLazy fun _ : Fin m => corruptRouter C (F.toProtocol κ C)).handle
          (j, .inl (i, x))).run s := by
  dsimp only [SSP.parFinLazy, corruptRouter] at s ⊢
  simp only [hi, ↓reduceIte]
  dsimp only [IdealFunctionality.multiSession, IdealFunctionality.toProtocol, StateT.run]
  cases s j <;> simp [ProbOracleComp.sample_bind]

private theorem handle_corruptRouter_multiSession_inr {m n : ℕ}
    {SubIn SubOut BackQ BackR : Type}
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) (C : Finset (Fin n)) (κ : ℕ)
    (j : Fin m) (nq : RoutedNetQ n SubIn BackQ)
    (hnq : match nq with | .inl (i, _) => i ∈ C | .inr _ => True)
    (s : Fin m → Option F.State) :
    ((corruptRouter C ((F.multiSession (Fin m)).toProtocol κ C)).handle
        (.inr (match nq with
        | .inl (i, x) => .inl (i, ⟨j, x⟩)
        | .inr bq => .inr ⟨j, bq⟩))).run (MultiSessionState.mk κ C s) =
      Prod.map _root_.id (MultiSessionState.mk κ C) <$>
        ((SSP.parFinLazy fun _ : Fin m => corruptRouter C (F.toProtocol κ C)).handle
          (j, .inr nq)).run s := by
  rcases nq with ⟨i, x⟩ | bq <;> dsimp only [SSP.parFinLazy] at s ⊢
  · simp only [corruptRouter, hnq, ↓reduceIte, StateT.run_map]; erw [StateT.run_map]
    dsimp only [IdealFunctionality.multiSession, IdealFunctionality.toProtocol, StateT.run]
    cases s j <;> simp [ProbOracleComp.sample_bind]
  · simp only [corruptRouter, StateT.run_map]; erw [StateT.run_map]
    dsimp only [IdealFunctionality.multiSession, IdealFunctionality.toProtocol, StateT.run]
    cases s j <;> simp [ProbOracleComp.sample_bind]

private theorem eval_run_multiSession_relabel {m n : ℕ}
    {SubIn SubOut BackQ BackR α : Type}
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) (C : Finset (Fin n)) (κ : ℕ)
    (prog : ProbOracleComp
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn BackQ)
        (RoutedNetR SubOut BackR))) α) :
    ((corruptRouter C ((F.multiSession (Fin m)).toProtocol κ C)).run
        (relabelSessionProg prog)).eval =
      ((SSP.parFin fun _ : Fin m => corruptRouter C (F.toProtocol κ C)).run prog).eval := by
  let S := protocolSpec n SubIn SubOut (RoutedNetQ n SubIn BackQ) (RoutedNetR SubOut BackR)
  let M : Fin m → Machine OracleSpec.empty S := fun _ => corruptRouter C (F.toProtocol κ C)
  let stripHandler (jq : Fin m × ((Fin n × SubIn) ⊕ RoutedNetQ n SubIn BackQ)) :
      ProbOracleComp (SSP.sessionSpec m S) (SSP.sessionSpec m S jq) := match jq with
    | (j, .inl (i, x)) => if i ∈ C then pure none else ProbOracleComp.query (j, Sum.inl (i, x))
    | (j, .inr (.inl (i, x))) =>
        if i ∈ C then ProbOracleComp.query (j, Sum.inr (Sum.inl (i, x))) else pure (.inl none)
    | (j, .inr (.inr bq)) => ProbOracleComp.query (j, Sum.inr (Sum.inr bq))
  let stripProg := OracleComp.interpret
    (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (.inl k)) stripHandler) prog
  let P₁ := SSP.parFinLazy M
  let P₂ := corruptRouter C ((F.multiSession (Fin m)).toProtocol κ C)
  let rep : P₁.State → P₂.State := MultiSessionState.mk κ C
  have hP₂ : P₂.run (relabelSessionProg prog) = P₂.run (relabelSessionProg stripProg) := by
    have hcomm : relabelSessionProg stripProg = OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (.inl k))
          (stripCorruptHandler C)) (relabelSessionProg prog) := by
      dsimp only [relabelSessionProg, stripProg]
      erw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
      congr 1 with q; rcases q with k | ⟨j, ⟨i, x⟩ | ⟨i, x⟩ | bq⟩
      · rfl
      · dsimp only [sumHandler, stripHandler, relabelSessionHandler]
        erw [OracleComp.interpret_query]; dsimp only [sumHandler, stripCorruptHandler]
        by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
        · rfl
        · erw [OracleComp.interpret_query]; rfl
      · dsimp only [sumHandler, stripHandler, relabelSessionHandler]
        erw [OracleComp.interpret_query]; dsimp only [sumHandler, stripCorruptHandler]
        by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
        · erw [OracleComp.interpret_query]; rfl
        · rfl
      · dsimp only [sumHandler, stripHandler, relabelSessionHandler]
        erw [OracleComp.interpret_query]
    rw [hcomm]; exact (run_corruptRouter_stripCorruptHandler C _ _).symm
  have hLazy : P₂.run (relabelSessionProg stripProg) = P₁.run stripProg := by
    simp only [Machine.run, Machine.link]
    refine congrArg Machine.closeProgram ?_
    change (ProbOracleComp.sample (pure (rep fun _ => none)) >>= fun s₂ =>
        Prod.fst <$> P₂.runFrom (relabelSessionProg stripProg) s₂) =
      (ProbOracleComp.sample (pure fun _ => none) >>= fun s₁ =>
        Prod.fst <$> P₁.runFrom stripProg s₁)
    rw [ProbOracleComp.sample_pure, ProbOracleComp.sample_pure, pure_bind, pure_bind,
      ← bind_pure_comp, ← bind_pure_comp]
    dsimp only [relabelSessionProg, stripProg]
    rw [OracleComp.interpret_interpret, OracleComp.interpret_sumHandler]
    refine Machine.runFrom_interpret_intertwine P₂ P₁ _ stripHandler
      (fun _ => True) (fun s₂ s₁ => s₂ = rep s₁) prog
      (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
      (rep fun _ => none) (fun _ => none) rfl (fun x => pure x.1) (fun x => pure x.1)
      (fun _ _ _ _ => rfl) fun ⟨j, q⟩ _ s₁ k₂ k₁ _ hR hcont => ?_
    subst hR; rcases q with ⟨i, x⟩ | ⟨i, x⟩ | bq <;> dsimp only [stripHandler]
    · by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
      · erw [OracleComp.interpret_pure, Machine.runFrom_pure, Machine.runFrom_pure,
          pure_bind, pure_bind]
        exact hcont none _ _ rfl
      · erw [OracleComp.interpret_query, Machine.runFrom_query, Machine.runFrom_query,
          handle_corruptRouter_multiSession_inl F C κ j i x hi s₁, bind_map_left]
        exact bind_congr fun ⟨r, s'⟩ => hcont r _ _ rfl
    · by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
      · erw [OracleComp.interpret_query, Machine.runFrom_query, Machine.runFrom_query,
          handle_corruptRouter_multiSession_inr F C κ j (.inl (i, x)) hi s₁, bind_map_left]
        exact bind_congr fun ⟨r, s'⟩ => hcont r _ _ rfl
      · erw [OracleComp.interpret_pure, Machine.runFrom_pure, Machine.runFrom_pure,
          pure_bind, pure_bind]
        exact hcont (.inl none) _ _ rfl
    · erw [OracleComp.interpret_query, Machine.runFrom_query, Machine.runFrom_query,
        handle_corruptRouter_multiSession_inr F C κ j (.inr bq) trivial s₁, bind_map_left]
      exact bind_congr fun ⟨r, s'⟩ => hcont r _ _ rfl
  have hEager : (SSP.parFin M).run stripProg = (SSP.parFin M).run prog := by
    refine Machine.run_interpret_stripNoop (SSP.parFin M) stripHandler (fun ⟨j, q⟩ s => ?_) prog
    rcases q with ⟨i, x⟩ | ⟨i, x⟩ | bq <;> dsimp only [stripHandler]
    · by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
      · simp only [SSP.parFin, M, corruptRouter, hi, ↓reduceIte,
          StateT.run_pure, map_pure, Function.update_eq_self]; rfl
      · exact Machine.runFrom_query _ _ _
    · by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
      · exact Machine.runFrom_query _ _ _
      · simp only [SSP.parFin, M, corruptRouter, hi, ↓reduceIte,
          StateT.run_pure, map_pure, Function.update_eq_self]; rfl
    · exact Machine.runFrom_query _ _ _
  rw [hP₂, hLazy, SSP.run_parFinLazy_eq_parFin, hEager]

private theorem jointDemux_jointMux {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    (A : ExecAdversary n In Out (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR) :
    jointDemux (m := m) (n := n) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      (SubIn := SubIn) (SubOut := SubOut) (BackQ := BackQ) (BackR := BackR)
      (jointMux A) = A := by
  funext κ C; dsimp only [jointDemux, jointMux, mapNetMachine]
  cases hA : A κ C with
  | mk State init handle =>
    congr 1; funext q s
    change OracleComp.interpret _ (OracleComp.interpret _ ((handle q).run s)) = (handle q).run s
    erw [OracleComp.interpret_interpret]
    refine (congrFun (congrArg OracleComp.interpret ?_) ((handle q).run s)).trans
      (OracleComp.interpret_query_eq_self _)
    funext r; cases r with
    | inl k => rfl
    | inr nq =>
      dsimp only [sumHandler]; erw [OracleComp.interpret_query]
      change ProbOracleComp.query (demuxNetQuery (muxNetQuery nq)) = _
      rw [demuxNetQuery_muxNetQuery]; rfl

end DemuxProof

/-- A step of the proof of Theorem 1 of [CanettiRabin2003] (the step showing that "protocol `π̃`
in the `F̂`-hybrid model emulates protocol `π` in the `F`-hybrid model"), not that theorem;
fixed-session joint-state execution identity for this library's call-bounded UC execution model:
`compose ρ.toJoint (F.multiSession (Fin m)).toProtocol` with adversary `A` and
`composeMulti ρ F.toProtocol` with `jointDemux A` have identical output distributions. -/
theorem exec_compose_toJoint_multiSession {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (F : IdealFunctionality n SubIn SubOut BackQ BackR)
    (A : ExecAdversary n In Out
      (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR)
    (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    (exec (compose ρ.toJoint (F.multiSession (Fin m)).toProtocol) A C Z κ z).eval =
      (exec (composeMulti ρ F.toProtocol) (jointDemux A) C Z κ z).eval := by
  simp only [exec, execMachine, compose, composeMulti, composeFamily, corruptRouter_comp,
    Machine.run_comp]
  rw [link_toJoint_eq_relabelSessionProg, eval_run_multiSession_relabel,
    ← link_liftAdversary_mapNetMachine]
  rfl

/-- A step of the proof of Theorem 1 of [CanettiRabin2003] (the step showing that "protocol `π̃`
in the `F̂`-hybrid model emulates protocol `π` in the `F`-hybrid model"), not that theorem;
fixed-session reverse joint-state execution identity for this library's call-bounded UC execution
model: `composeMulti ρ F.toProtocol` with adversary `A` and
`compose ρ.toJoint (F.multiSession (Fin m)).toProtocol` with `jointMux A` have identical output
distributions. -/
theorem exec_composeMulti_toJoint {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (F : IdealFunctionality n SubIn SubOut BackQ BackR)
    (A : ExecAdversary n In Out (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR)
    (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    (exec (composeMulti ρ F.toProtocol) A C Z κ z).eval =
      (exec (compose ρ.toJoint (F.multiSession (Fin m)).toProtocol) (jointMux A) C Z κ z).eval := by
  rw [exec_compose_toJoint_multiSession, jointDemux_jointMux]

/-- A step of the proof of Theorem 1 of [CanettiRabin2003] (the step showing that "protocol `π̃`
in the `F̂`-hybrid model emulates protocol `π` in the `F`-hybrid model"), not that theorem;
fixed-session joint-state step for this library's call-bounded `EmulatesWithin` relation:
`compose ρ.toJoint (F.multiSession (Fin m)).toProtocol` emulates `composeMulti ρ F.toProtocol`
with overhead `Polynomial.X` and zero distinguishing error via the explicit demultiplexing
adversary `jointDemux`. Fixed number `m` of sessions chosen in advance; static corruption; pull
execution returning untagged `Option SubOut` with explicit `SubSessionBackdoor` queries. -/
theorem EmulatesWithin.toJoint_multiSession {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) :
    EmulatesWithin
      (UC.compose ρ.toJoint (F.multiSession (Fin m)).toProtocol)
      (UC.composeMulti ρ F.toProtocol)
      Polynomial.X
      (fun _ _ _ => 0) := by
  intro AdvQ AdvR A pA hA
  refine ⟨jointDemux A, pA, jointDemux_polyBounded hA, SimPolyBound.refl pA, fun C Z pZ _ κ z => ?_⟩
  simp only [advantage, Game.advantage, exec_compose_toJoint_multiSession, nndist_self, le_rfl]

/-- A step of the proof of Theorem 1 of [CanettiRabin2003] (the step showing that "protocol `π̃`
in the `F̂`-hybrid model emulates protocol `π` in the `F`-hybrid model"), not that theorem;
fixed-session reverse joint-state step for this library's call-bounded `EmulatesWithin` relation:
`composeMulti ρ F.toProtocol` emulates `compose ρ.toJoint (F.multiSession (Fin m)).toProtocol`
with overhead `Polynomial.X` and zero distinguishing error via `jointMux`. Fixed number `m` of
sessions chosen in advance; static corruption; pull execution returning untagged `Option SubOut`
with explicit `SubSessionBackdoor` queries. -/
theorem EmulatesWithin.multiSession_toJoint {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) :
    EmulatesWithin
      (UC.composeMulti ρ F.toProtocol)
      (UC.compose ρ.toJoint (F.multiSession (Fin m)).toProtocol)
      Polynomial.X
      (fun _ _ _ => 0) := by
  intro AdvQ AdvR A pA hA
  refine ⟨jointMux A, pA, jointMux_polyBounded hA, SimPolyBound.refl pA, fun C Z pZ _ κ z => ?_⟩
  simp only [advantage, Game.advantage, exec_composeMulti_toJoint, nndist_self, le_rfl]

end Cslib.Crypto.Protocols.UC
