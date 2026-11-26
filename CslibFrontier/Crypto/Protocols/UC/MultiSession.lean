/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Composition
public import CslibFrontier.Crypto.Protocols.SSP.Hybrid
import CslibFrontier.Languages.Probabilistic.Oracle.Vector

/-!
# Multi-session universal composition for a fixed session family

This module proves fixed-arity multi-session composition steps for this library's own call-bounded,
static-corruption port-model emulation notions (`UC.EmulatesDummyWithin`, `UC.EmulatesWithin`,
`UC.Emulates`, `UC.Realizes`), via explicit parallel simulation and the multi-session
state-separating hybrid bound `SSP.advantage_parFin_le_sum` [BrzuskaDFKK2018].

## Scope and relation to [Canetti2020]

These results adapt Theorem 22, Corollaries 23–24, and the heterogeneous-family extension of
Section 6.3 of [Canetti2020] to a **fixed number `m` of sessions chosen in advance; not dynamic
session creation; this is not the full Theorem 22**. Specifically:

1. **Fixed `Fin m` session family vs. dynamic `SID` spawning.** In Theorem 22 of [Canetti2020]
   (JACM p. 28:58; ePrint 2000/067, rev. February 11, 2020, p. 61), a calling protocol dynamically
   spawns `poly(κ)` subroutine sessions indexed by bitstring session identifiers across a recursive
   ITI call tree. Here `m : ℕ` is a fixed finite arity (`Fin m`) of depth-1 subroutine sessions,
   universally quantified over `{m : ℕ}` in every theorem (so concrete `EmulatesWithin` bounds
   instantiate `m := q.eval κ` at any fixed security parameter `κ`). Lazy first-touch spawning
   and dynamic session identifiers are not formalised here and are left to a follow-up.
2. **Heterogeneous §6.3 families with one fixed interface per side.** In Section 6.3 of
   [Canetti2020] (JACM p. 28:67; ePrint p. 70), distinct session identifiers may invoke distinct
   protocols. In `EmulatesDummyWithin.composeFamily` and `Emulates.composeFamily`, the protocol
   implementations and their private state types (`(π j κ C).State`, `(φ j κ C).State`) may vary
   with the session `j : Fin m`, while the party count `n`, party input/output types `SubIn` and
   `SubOut`, and each side's network message types (`NQ₁`, `NR₁` and `NQ₂`, `NR₂`) are shared
   across all `m` sessions.
3. **Library call-bounded statistical notions vs. PPT ITMs and §4.4.** Per-activation counting of
   oracle calls and private samples (`MultiHybridProtocol.PolyBounded`, `Protocol.PolyBounded`,
   `Adversary.PolyBounded`, `Environment.PolyBounded`) is this library's own convention (see the
   `Cslib.Crypto.Protocols.UC.Emulates` docstring); pure computation, state size, and message
   length are unbounded. By contrast, Section 4.4 of [Canetti2020] (JACM p. 28:48; ePrint p. 50)
   defines statistical emulation with computationally unbounded participants and quantitative
   running-time simulation overhead, and Theorem 22 is proved for PPT ITMs; no implication to or
   from Canetti's PPT or Section 4.4 notions is established here.
4. **Static same-party corruptions `C : Finset (Fin n)` vs. adaptive per-identity corruptions.**
   The calling protocol `ρ κ C` and all `m` subroutine sessions `corruptRouter C (σ j κ C)` share
   the same static corruption set `C`, fixed prior to execution.
5. **Structural type-level isolation and compliance vs. runtime predicates.** Subroutine-respecting
   isolation (each session `j : Fin m` is a closed `Machine OracleSpec.empty` package inside
   `SSP.parFin`), subroutine-exposing network addressing (`MultiNetQ.sub j q`), and `(π, φ, ξ)`-
   compliance (unrestricted `SubSessionCall m n SubIn`, corresponding to `ξ = univ`) are enforced
   statically by types rather than runtime directory queries.

Unlike the single-session theorem (`m = 1` in `UC.Emulates.compose`), where only `hρ` needs a
polynomial call budget, for `m ≥ 2` the single-hop hybrid distinguisher `sessionHopEnv` internally
simulates both real sessions `π j` (`j > j₀`) and ideal simulated sessions `(φ j, S j)` (`j < j₀`),
so polynomial call budgets on both `π` and `φ` (`hπ`, `hφ`) are essential—matching Canetti's
hypothesis that `ρ`, `π`, and `φ` are all bounded protocols.

## Main definitions

* `Cslib.Crypto.Protocols.UC.SubSessionCall`: named record selecting a target subroutine session `j`
  and target party port `party`.
* `Cslib.Crypto.Protocols.UC.multiPartySpec`, `Cslib.Crypto.Protocols.UC.MultiHybridProtocol`,
  `Cslib.Crypto.Protocols.UC.MultiHybridProtocol.PolyBounded`: multi-session hybrid protocols.
* `Cslib.Crypto.Protocols.UC.MultiNetQ`: composed network request port tagging outer vs.
  per-session subroutine traffic (paired with the sum reply type `NetR ⊕ RoutedNetR SubOut NR`).
* `Cslib.Crypto.Protocols.UC.sessionRouter`: `m` isolated static-corruption sessions via
  `SSP.parFin`.
* `Cslib.Crypto.Protocols.UC.multiHybridWrap`, `Cslib.Crypto.Protocols.UC.composeFamily`,
  `Cslib.Crypto.Protocols.UC.composeMulti`: multi-session subroutine replacement.
* `Cslib.Crypto.Protocols.UC.multiHybridSim`:
  parallel composition of per-session dummy-adversary simulators.
* `Cslib.Crypto.Protocols.UC.absorbMultiHybrid`, `Cslib.Crypto.Protocols.UC.sessionHopEnv`:
  absorbed multi-session environment and single-hop hybrid distinguisher.
* `Cslib.Crypto.Protocols.UC.sessionUnitPoly`, `Cslib.Crypto.Protocols.UC.sessionHopPoly`:
  explicit polynomial budget bounds for single-hop environments.

## Main results

* `Cslib.Crypto.Protocols.UC.exec_composeFamily_dummy`: running `composeFamily ρ π` with the
  dummy adversary equals running `sessionRouter` against `absorbMultiHybrid`.
* `Cslib.Crypto.Protocols.UC.eval_exec_composeFamily_multiHybridSim`: running `composeFamily ρ φ`
  with `multiHybridSim S` has the same output distribution as running `m` parallel ideal-world
  executions against `absorbMultiHybrid`.
* `Cslib.Crypto.Protocols.UC.advantage_composeFamily_le_sum`: telescoping hybrid bound reducing
  the `m`-session distinguishing advantage to the sum of `m` single-session advantages against
  `sessionHopEnv`.
* `Cslib.Crypto.Protocols.UC.EmulatesDummyWithin.composeFamily`,
  `Cslib.Crypto.Protocols.UC.EmulatesDummyWithin.composeMulti`: fixed-session composition steps for
  dummy-adversary emulation.
* `Cslib.Crypto.Protocols.UC.EmulatesWithin.composeMulti`: fixed-session quantitative composition
  step with explicit simulator call overhead and distinguishing bound.
* `Cslib.Crypto.Protocols.UC.Emulates.composeFamily`,
  `Cslib.Crypto.Protocols.UC.Emulates.composeMulti`: fixed-session heterogeneous and homogeneous
  composition steps for `UC.Emulates`.
* `Cslib.Crypto.Protocols.UC.Realizes.composeMulti`,
  `Cslib.Crypto.Protocols.UC.Realizes.composeMulti_trans`: fixed-session composition steps for
  `UC.Realizes`.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], J. ACM 67(5), Article 28, 2020:
  Section 6.1 (Theorem 22 p. 28:58; Corollaries 23–24 p. 28:59), Section 6.2 (hybrid proof,
  pp. 28:59–28:67), and Section 6.3 (heterogeneous families, p. 28:67); IACR ePrint 2000/067
  (rev. February 11, 2020), pp. 61–62, 65, 70.
* [C. Brzuska, A. Delignat-Lavaud, C. Fournet, K. Kohbrok, M. Kohlweiss, *State Separation for
  Code-Based Game-Playing Proofs*][BrzuskaDFKK2018]: `SSP.parFin` and `SSP.advantage_parFin_le_sum`.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open scoped NNReal

/-! ### Ports, hybrid protocols, and session routing -/

/-- A subroutine party-port call from a multi-session hybrid protocol: delivers `input` to target
party port `party` of subroutine session `session` (or polls it). The outer protocol can select
any target `party : Fin n`, including on a network activation. -/
structure SubSessionCall (m n : ℕ) (SubIn : Type) : Type where
  /-- Target subroutine session index (`0 ≤ session < m`). -/
  session : Fin m
  /-- Target party port index (`0 ≤ party < n`) in that subroutine session. -/
  party : Fin n
  /-- Input (or poll token) delivered to `(session, party)`. -/
  input : SubIn
  deriving DecidableEq

/-- The party-port interface of `m` subroutine sessions of `n` parties: each `SubSessionCall`
receives an optional output of the subroutine. -/
@[expose] def multiPartySpec (m n : ℕ) (SubIn SubOut : Type) :
    SubSessionCall m n SubIn → Type :=
  fun _ => Option SubOut

/-- An `n`-party protocol in the multi-session hybrid model of `m` subroutine sessions with party
inputs `SubIn` and outputs `SubOut`. -/
abbrev MultiHybridProtocol (m n : ℕ) (In Out NetQ NetR SubIn SubOut : Type) : Type 1 :=
  ℕ → Finset (Fin n) → Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR)

/-- Every activation of the multi-session hybrid protocol at security parameter `κ` makes at most
`p.eval κ` calls, counting private samples and subroutine calls. -/
@[expose] def MultiHybridProtocol.PolyBounded {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut) (p : Polynomial ℕ) : Prop :=
  ∀ κ C, (ρ κ C).IsBounded (p.eval κ)

/-- Network-side query to a multi-session composed protocol: either a query to the calling
protocol `ρ`'s own network port, or a query to subroutine session `session`'s routed network
port (including corrupted-party subroutine inputs `.inl (i, x)` and subroutine network queries
`.inr q`). -/
inductive MultiNetQ (m : ℕ) (NetQ SubRoutedQ : Type) : Type
  /-- A query directed to the outer calling protocol `ρ`'s own network port. -/
  | outer (query : NetQ)
  /-- A query directed to subroutine session `session`'s routed network port. -/
  | sub (session : Fin m) (query : SubRoutedQ)
  deriving DecidableEq

/-- Parallel router for `m` independent subroutine sessions sharing the static corruption set `C`.
Each session `j : Fin m` owns its private state inside `SSP.parFin` and cannot inspect or mutate
any other session's state. -/
@[expose] def sessionRouter {m n : ℕ} {SubIn SubOut NQ NR : Type} (C : Finset (Fin n))
    (σ : Fin m → Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ NR)) :
    Machine OracleSpec.empty
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ)
        (RoutedNetR SubOut NR))) :=
  SSP.parFin fun j => corruptRouter C (σ j)

/-- A program calling only the multi-session subroutine party port, lifted to call the `m`-session
interface `SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR)`. -/
@[expose] def liftMultiParty {m n : ℕ} {SubIn SubOut NQ NR α : Type}
    (program : ProbOracleComp (multiPartySpec m n SubIn SubOut) α) :
    ProbOracleComp (SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR)) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR)))
        (Sum.inl k))
      fun c => ProbOracleComp.query
        (spec := SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR))
        (c.session, Sum.inl (c.party, c.input)))
    program

/-- Wrap a multi-session hybrid protocol machine so its subroutine party calls target
`SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR)` and each subroutine session's network port
is exposed under `MultiNetQ.sub j` / `Sum.inr`. -/
@[expose] def multiHybridWrap {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (M : Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR)) :
    Machine (SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR))
      (protocolSpec n In Out (MultiNetQ m NetQ NQ) (NetR ⊕ NR)) where
  State := M.State
  init := M.init
  handle
    | .inl p => fun s => liftMultiParty ((M.handle (.inl p)).run s)
    | .inr (.outer q) => fun s => liftMultiParty ((Sum.inl <$> M.handle (.inr q)).run s)
    | .inr (.sub j q) => StateT.lift (Sum.inr <$>
        ProbOracleComp.query (spec := SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR))
          (j, Sum.inr q))

/-- Heterogeneous multi-session subroutine replacement: the hybrid protocol `ρ` with its `m`
subroutine sessions answered by the independent protocol family `σ : Fin m → Protocol …` behind
`sessionRouter C`, sharing the same parties and static corruption set `C`. -/
@[expose] def composeFamily {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (σ : Fin m → Protocol n SubIn SubOut NQ NR) :
    Protocol n In Out
      (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ))
      (NetR ⊕ RoutedNetR SubOut NR) :=
  fun κ C => (multiHybridWrap (ρ κ C)).comp (sessionRouter C fun j => σ j κ C)

/-- Homogeneous multi-session subroutine replacement: `ρ` calling `m` independent instances of the
same protocol `σ`. -/
abbrev composeMulti {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (σ : Protocol n SubIn SubOut NQ NR) :
    Protocol n In Out
      (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ))
      (NetR ⊕ RoutedNetR SubOut NR) :=
  composeFamily ρ (fun _ => σ)

/-! ### Multi-session simulator, absorbed hybrid, and single-hop reduction environment -/

private def liftMultiSubNet {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR α : Type}
    (j : Fin m)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α) :
    ProbOracleComp
      (netSpec (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (netSpec
          (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ)))
          (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))))
        (Sum.inl k))
      fun q => subReply <$> ProbOracleComp.query
        (spec := netSpec
          (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ)))
          (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)))
        (.inr (.sub j q)))
    program

/-- Machine combining `m` independent subroutine simulators `S j` side by side on the composed
network interface, forwarding corrupted outer-party inputs and outer network queries unchanged and
routing session `j` network queries to `S j` on state coordinate `j`. -/
def multiHybridSimMachine {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) :
    Machine
      (netSpec (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)))
      (netSpec (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₁)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))) where
  State := (j : Fin m) → (S j).State
  init := OracleComp.pi fun j => (S j).init
  handle
    | .inl p => StateT.lift (outerReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂))) (.inl p))
    | .inr (.outer q) => StateT.lift (outerReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂))) (.inr (.outer q)))
    | .inr (.sub j q) => fun s =>
        liftMultiSubNet j ((fun x => (Sum.inr (Sum.inr x.1), Function.update s j x.2)) <$>
          ((S j).handle q).run (s j))

/-- The composed simulator for `composeFamily ρ π` against `composeFamily ρ φ`, running an
independent simulator `S j` for each subroutine session `j : Fin m`. -/
@[expose] def multiHybridSim {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) →
      Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
        (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) :
    Adversary n
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)) :=
  fun κ C => multiHybridSimMachine fun j => S j κ C

/-- Absorbing `ρ κ C` into an environment `Z` produces a distinguisher against the `m`-session
subroutine interface `SSP.sessionSpec m (protocolSpec n SubIn SubOut …)`. -/
@[expose] def absorbMultiHybrid {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (C : Finset (Fin n))
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (Z : Environment n In Out
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)))
    (κ : ℕ) (z : List Bool) :
    ProbOracleComp
      (SSP.sessionSpec m
        (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)))
      Bool :=
  (routeCorrupt C (multiHybridWrap (ρ κ C))).link (Z κ z)

/-- Single-hop reduction environment for session `j₀`: runs ideal simulated sessions `(φ j, S j)`
for `j < j₀`, forwards session `j₀` externally, and runs real sessions `π j` for `j > j₀`. -/
@[expose] def sessionHopEnv {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (C : Finset (Fin n))
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (π : Fin m → Protocol n SubIn SubOut NQ₁ NR₁)
    (φ : Fin m → Protocol n SubIn SubOut NQ₂ NR₂)
    (S : (j : Fin m) →
      Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
        (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
    (Z : Environment n In Out
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)))
    (j₀ : Fin m) :
    Environment n SubIn SubOut (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁) :=
  fun κ z =>
    SSP.hybridDistinguisher
      (fun j => corruptRouter C (π j κ C))
      (fun j => execMachine (φ j) (S j) κ C)
      (absorbMultiHybrid C ρ Z κ z)
      j₀

/-- Polynomial dominating both a real session `corruptRouter C (π j κ C)` (`pπ`) and an ideal
simulated session `execMachine (φ j) (S j) κ C` (`(pD + 1) * (pφ + 1) + pφ`). -/
@[expose] noncomputable def sessionUnitPoly (pπ pφ pD : Polynomial ℕ) : Polynomial ℕ :=
  pπ + ((pD + 1) * (pφ + 1) + pφ)

/-- Polynomial call-budget bound for the single-hop hybrid distinguisher `sessionHopEnv`. -/
@[expose] noncomputable def sessionHopPoly (m : ℕ) (pZ pρ pπ pφ pD : Polynomial ℕ) :
    Polynomial ℕ :=
  absorbPoly (absorbPoly pZ pρ) (Polynomial.C m * sessionUnitPoly pπ pφ pD)

/-! ### Execution identities -/

/-- Running `composeFamily ρ π` with the dummy adversary is running `sessionRouter` against
`absorbMultiHybrid`. This is an equation of programs. -/
theorem exec_composeFamily_dummy {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (π : Fin m → Protocol n SubIn SubOut NQ NR) (C : Finset (Fin n))
    (Z : Environment n In Out
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)))
    (κ : ℕ) (z : List Bool) :
    exec (composeFamily ρ π) (dummyAdversary n _ _) C Z κ z =
      (sessionRouter C fun j => π j κ C).run (absorbMultiHybrid C ρ Z κ z) := by
  simp only [exec, execMachine, dummyAdversary, Machine.liftRight_id, Machine.run_comp,
    Machine.link_id, composeFamily, corruptRouter_comp, absorbMultiHybrid]

section Swap

private def liftSessionNet {m n : ℕ} {SubIn SubOut NQ NR α : Type} (j : Fin m)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α) :
    ProbOracleComp
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ)
        (RoutedNetR SubOut NR))) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (SSP.sessionSpec m (protocolSpec n SubIn SubOut
          (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR))))
        (Sum.inl k))
      fun q => ProbOracleComp.query
        (spec := SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ)
          (RoutedNetR SubOut NR)))
        (j, Sum.inr q))
    program

private def parLiftAdversary {m n : ℕ} {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) :
    Machine
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₂)
        (RoutedNetR SubOut NR₂)))
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁)
        (RoutedNetR SubOut NR₁))) where
  State := (j : Fin m) → (S j).State
  init := OracleComp.pi fun j => (S j).init
  handle
    | (j, .inl p) => StateT.lift (ProbOracleComp.query
        (spec := SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₂)
          (RoutedNetR SubOut NR₂)))
        (j, Sum.inl p))
    | (j, .inr q) => fun s =>
        liftSessionNet j ((fun x => (x.1, Function.update s j x.2)) <$> ((S j).handle q).run (s j))

private theorem runFrom_parLiftAdversary_liftMultiParty {m n : ℕ}
    {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ α : Type}
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (program : ProbOracleComp (multiPartySpec m n SubIn SubOut) α)
    (s : (parLiftAdversary S).State) :
    (parLiftAdversary S).runFrom (liftMultiParty program) s =
      (fun a => (a, s)) <$> liftMultiParty program := by
  refine Machine.runFrom_interpret_of_forward (parLiftAdversary S) _ _ (fun q s => ?_) program s
  cases q with
  | inl k => exact runFrom_query_sample _ k s
  | inr c => simp only [sumHandler, parLiftAdversary]; rfl

/-- Mapping over a multi-session party-interface program commutes with `liftMultiParty`. -/
theorem liftMultiParty_map {m n : ℕ} {SubIn SubOut NQ NR α β : Type} (f : α → β)
    (program : ProbOracleComp (multiPartySpec m n SubIn SubOut) α) :
    liftMultiParty (NQ := NQ) (NR := NR) (f <$> program) = f <$> liftMultiParty program :=
  OracleComp.interpret_map _ _ _

private theorem liftMultiSubNet_map {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR α β : Type}
    (j : Fin m) (f : α → β)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α) :
    liftMultiSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) j (f <$> program) =
      f <$> liftMultiSubNet j program :=
  OracleComp.interpret_map _ _ _

private theorem liftSessionNet_map {m n : ℕ} {SubIn SubOut NQ NR α β : Type}
    (j : Fin m) (f : α → β)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α) :
    liftSessionNet j (f <$> program) = f <$> liftSessionNet j program :=
  OracleComp.interpret_map _ _ _

private theorem multiHybridWrap_handle_inl {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (M : Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR))
    (p : Fin n × In) (s : M.State) :
    ((multiHybridWrap (NQ := NQ) (NR := NR) M).handle (.inl p)).run s =
      liftMultiParty ((M.handle (.inl p)).run s) := rfl

private theorem multiHybridWrap_handle_inr_outer {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (M : Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR))
    (q : NetQ) (s : M.State) :
    ((multiHybridWrap (NQ := NQ) (NR := NR) M).handle (.inr (.outer q))).run s =
      (fun p => (Sum.inl p.1, p.2)) <$> liftMultiParty ((M.handle (.inr q)).run s) := by
  change liftMultiParty ((Sum.inl <$> M.handle (.inr q)).run s) = _
  rw [StateT.run_map, liftMultiParty_map]

private theorem multiHybridWrap_handle_inr_sub {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (M : Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR))
    (j : Fin m) (q : NQ) (s : M.State) :
    ((multiHybridWrap (NR := NR) M).handle (.inr (.sub j q))).run s =
      (fun a => (Sum.inr a, s)) <$>
        ProbOracleComp.query (spec := SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR))
          (j, Sum.inr q) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem multiHybridSimMachine_handle_inl {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (p : Fin n × In) (s : (multiHybridSimMachine S).State) :
    ((multiHybridSimMachine (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) S).handle
        (.inl p)).run s =
      (fun a => (outerReply a, s)) <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂))) (.inl p) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem multiHybridSimMachine_handle_inr_outer {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (q : NetQ) (s : (multiHybridSimMachine S).State) :
    ((multiHybridSimMachine (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) S).handle
        (.inr (.outer q))).run s =
      (fun a => (outerReply a, s)) <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂))) (.inr (.outer q)) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem multiHybridSimMachine_handle_inr_sub {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (j : Fin m) (q : RoutedNetQ n SubIn NQ₁) (s : (multiHybridSimMachine S).State) :
    ((multiHybridSimMachine (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) S).handle
        (.inr (.sub j q))).run s =
      (fun x => (Sum.inr (Sum.inr x.1), Function.update s j x.2)) <$>
        liftMultiSubNet j (((S j).handle q).run (s j)) := by
  change liftMultiSubNet j (_ <$> ((S j).handle q).run (s j)) = _
  rw [liftMultiSubNet_map]

private theorem runFrom_routeCorrupt_liftNet_liftMultiSubNet {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR α : Type}
    (C : Finset (Fin n))
    (M : Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR))
    (j : Fin m)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α)
    (s : M.State) :
    (routeCorrupt C
        (multiHybridWrap (NQ := RoutedNetQ n SubIn NQ) (NR := RoutedNetR SubOut NR) M)).runFrom
        (liftNet (liftMultiSubNet j program)) s =
      (fun a => (a, s)) <$> liftSessionNet j program := by
  dsimp only [liftNet]
  rw [Machine.liftRightProgram, liftMultiSubNet, OracleComp.interpret_interpret, liftSessionNet]
  refine Machine.runFrom_interpret_of_forward (routeCorrupt C (multiHybridWrap M)) _ _
    (fun q s => ?_) program s
  cases q with
  | inl k => simpa only [OracleComp.interpret_query] using runFrom_query_sample _ k s
  | inr q =>
    simp only [OracleComp.interpret_map, ProbOracleComp.interpret_query, Machine.runFrom_map,
      Machine.runFrom_query]
    change Prod.map subReply _root_.id <$> ((Sum.inr <$> StateT.lift (Sum.inr <$>
      ProbOracleComp.query (spec := SSP.sessionSpec m (protocolSpec n SubIn SubOut
        (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR))) (j, Sum.inr q))).run s) = _
    rw [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map, Functor.map_map,
      Functor.map_map]
    rfl

private theorem parLiftAdversary_handle_inr {m n : ℕ} {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (j : Fin m) (q : RoutedNetQ n SubIn NQ₁) (s : (parLiftAdversary S).State) :
    ((parLiftAdversary S).handle (j, Sum.inr q)).run s =
      liftSessionNet j ((fun x => (x.1, Function.update s j x.2)) <$>
        ((S j).handle q).run (s j)) := rfl

private theorem handle_swap {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (C : Finset (Fin n))
    (M : Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR))
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (q : (Fin n × In) ⊕ RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₁)))
    (sρ : M.State) (sS : (j : Fin m) → (S j).State) :
    Equiv.prodAssoc _ _ _ <$> (routeCorrupt C (multiHybridWrap
        (NQ := RoutedNetQ n SubIn NQ₂) (NR := RoutedNetR SubOut NR₂) M)).runFrom
        (((liftAdversary (n := n) (In := In) (Out := Out)
          (multiHybridSimMachine S)).handle q).run sS) sρ =
      Prod.map _root_.id Prod.swap <$> (Equiv.prodAssoc _ _ _ <$>
        (parLiftAdversary S).runFrom
          (((routeCorrupt C (multiHybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
            (NR := RoutedNetR SubOut NR₁) M)).handle q).run sρ) sS) := by
  rcases q with ⟨i, x⟩ | ⟨i, x⟩ | q | ⟨j, q⟩
  · erw [liftAdversary_handle_inl, Machine.runFrom_map, Machine.runFrom_query,
      routeCorrupt_handle_inl, routeCorrupt_handle_inl]
    by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
    · rfl
    · erw [multiHybridWrap_handle_inl, multiHybridWrap_handle_inl,
        runFrom_parLiftAdversary_liftMultiParty]
      repeat erw [Functor.map_map]
      rfl
  · erw [liftAdversary_handle_inr, multiHybridSimMachine_handle_inl, Machine.liftRightProgram_map,
      Machine.liftRightProgram_query, Machine.runFrom_map, Machine.runFrom_query,
      routeCorrupt_handle_inr_inl, routeCorrupt_handle_inr_inl]
    by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
    · erw [multiHybridWrap_handle_inl, multiHybridWrap_handle_inl, Machine.runFrom_map,
        runFrom_parLiftAdversary_liftMultiParty]
      repeat erw [Functor.map_map]
      rfl
    · rfl
  · erw [liftAdversary_handle_inr, multiHybridSimMachine_handle_inr_outer,
      Machine.liftRightProgram_map, Machine.liftRightProgram_query, Machine.runFrom_map,
      Machine.runFrom_query, routeCorrupt_handle_inr_inr, routeCorrupt_handle_inr_inr,
      multiHybridWrap_handle_inr_outer, multiHybridWrap_handle_inr_outer]
    repeat erw [Functor.map_map]
    erw [Machine.runFrom_map, runFrom_parLiftAdversary_liftMultiParty]
    repeat erw [Functor.map_map]
    rfl
  · erw [liftAdversary_handle_inr, multiHybridSimMachine_handle_inr_sub,
      Machine.liftRightProgram_map, Machine.runFrom_map,
      runFrom_routeCorrupt_liftNet_liftMultiSubNet, routeCorrupt_handle_inr_inr,
      multiHybridWrap_handle_inr_sub]
    repeat erw [Functor.map_map]
    erw [Machine.runFrom_map, Machine.runFrom_query, parLiftAdversary_handle_inr,
      liftSessionNet_map]
    repeat erw [Functor.map_map]
    rfl

private theorem runFrom_sessionRouter_liftSessionNet {m n : ℕ} {SubIn SubOut NQ NR α : Type}
    (C : Finset (Fin n))
    (φ : Fin m → Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ NR))
    (j : Fin m)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α)
    (s : (sessionRouter C φ).State) :
    (sessionRouter C φ).runFrom (liftSessionNet j program) s =
      (fun x => (x.1, Function.update s j x.2)) <$>
        (corruptRouter C (φ j)).runFrom (liftNet program) (s j) := by
  induction program using OracleComp.induction generalizing s with
  | pure a =>
    simp only [liftSessionNet, Machine.liftRightProgram_pure, OracleComp.interpret_pure,
      Machine.runFrom_pure, map_pure]
    erw [Function.update_eq_self]
    rfl
  | query_bind q cont ih =>
    cases q with
    | inl k =>
      have h₁ : liftSessionNet (NQ := NQ) (NR := NR) j
          (OracleComp.query (spec := probOracleSpec (netSpec (RoutedNetQ n SubIn NQ)
            (RoutedNetR SubOut NR))) (Sum.inl k)) =
          ProbOracleComp.sample (ProbComp.unifFin k) := by
        simp only [liftSessionNet, OracleComp.interpret_query, sumHandler, ProbOracleComp.sample,
          ProbComp.unifFin, OracleComp.substitute_query]
      have h₂ : liftNet (n := n) (In := SubIn) (Out := SubOut)
          (OracleComp.query (spec := probOracleSpec (netSpec (RoutedNetQ n SubIn NQ)
            (RoutedNetR SubOut NR))) (Sum.inl k)) =
          ProbOracleComp.sample (ProbComp.unifFin k) := by
        rw [liftNet, ← Machine.liftRightProgram_sample (partySpec n SubIn SubOut)]; rfl
      simp only [liftSessionNet, liftNet]
      change (sessionRouter C φ).runFrom
          (liftSessionNet j (OracleComp.query (.inl k)) >>= fun a =>
            liftSessionNet j (cont a)) s =
        (fun x => (x.1, Function.update s j x.2)) <$> (corruptRouter C (φ j)).runFrom
          (liftNet (OracleComp.query (.inl k)) >>= fun a => liftNet (cont a)) (s j)
      rw [h₁, h₂, Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_sample,
        Machine.runFrom_sample, bind_map_left, bind_map_left, map_bind]
      exact bind_congr fun a => ih a s
    | inr e =>
      simp only [liftSessionNet, liftNet]
      change (sessionRouter C φ).runFrom
          (ProbOracleComp.query (j, Sum.inr e) >>= fun a => liftSessionNet j (cont a)) s =
        (fun x => (x.1, Function.update s j x.2)) <$> (corruptRouter C (φ j)).runFrom
          (ProbOracleComp.query (Sum.inr e) >>= fun a => liftNet (cont a)) (s j)
      rw [Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_query]
      erw [SSP.parFin_handle, bind_map_left, map_bind]
      refine bind_congr fun x => ?_
      rw [ih x.1 (Function.update s j x.2)]
      erw [Function.update_self]
      exact congrArg (· <$> _) (funext fun y => by erw [Function.update_idem])

private theorem eval_run_parLiftAdversary_comp_sessionRouter {m n : ℕ}
    {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ α : Type}
    (C : Finset (Fin n))
    (φ : Fin m → Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ₂ NR₂))
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (program : ProbOracleComp
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁)
        (RoutedNetR SubOut NR₁))) α) :
    (((parLiftAdversary S).comp (sessionRouter C φ)).run program).eval =
      ((SSP.parFin fun j => (liftAdversary (n := n) (In := SubIn) (Out := SubOut) (S j)).comp
        (corruptRouter C (φ j))).run program).eval := by
  refine SSP.eval_run_eq_of_represent
    ((parLiftAdversary S).comp (sessionRouter C φ))
    (SSP.parFin fun j => (liftAdversary (n := n) (In := SubIn) (Out := SubOut) (S j)).comp
      (corruptRouter C (φ j)))
    (fun s j => (s.1 j, s.2 j)) ?_ ?_ program
  · have hpair := congrArg (PMF.map fun f (j : Fin m) => (f j).swap)
      (ProbComp.eval_pi_pair (fun j => (φ j).init) (fun j => (S j).init))
    rw [← ProbComp.eval_pi_map] at hpair
    simp only [map_bind, map_pure, Prod.swap_prod_mk, PMF.map_bind, PMF.map_comp] at hpair
    dsimp only [Machine.comp, parLiftAdversary, sessionRouter, SSP.parFin]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
    exact hpair.symm
  · rintro ⟨j, q⟩ ⟨sS, sφ⟩
    conv_lhs =>
      enter [2, 1, 1]
      change Equiv.prodAssoc _ _ _ <$>
        (sessionRouter C φ).runFrom (((parLiftAdversary S).handle (j, q)).run sS) sφ
    rcases q with p | nq
    on_goal 1 =>
      erw [StateT.run_lift, bind_pure_comp, Machine.runFrom_map, Machine.runFrom_query,
        SSP.parFin_handle, SSP.parFin_handle]
      simp only [Machine.comp, liftAdversary, Machine.liftRight, StateT.run, StateT.lift,
        bind_pure_comp]
      erw [Machine.runFrom_map, Machine.runFrom_query]
    on_goal 2 =>
      erw [parLiftAdversary_handle_inr, liftSessionNet_map, Machine.runFrom_map,
        runFrom_sessionRouter_liftSessionNet, SSP.parFin_handle]
      simp only [Machine.comp, liftAdversary, Machine.liftRight, StateT.run]
    all_goals
      repeat erw [Machine.closeProgram_map]
      repeat erw [ProbComp.eval_map]
      repeat erw [PMF.map_comp]
      refine congrArg (PMF.map · _) (funext fun ⟨r, sφ'⟩ => ?_)
      dsimp only [sessionRouter, parLiftAdversary, SSP.parFin, Function.comp_apply,
        Prod.map_apply, id_eq] at r sφ' sS sφ ⊢
      erw [Equiv.prodAssoc_apply]
      refine Prod.ext rfl (funext fun i => ?_)
      obtain rfl | hi := eq_or_ne i j <;> simp [*]

end Swap

/-- Running `composeFamily ρ φ` with `multiHybridSim S` has the same output distribution as
running `m` parallel ideal-world executions `execMachine (φ j) (S j) κ C` against
`absorbMultiHybrid`. -/
theorem eval_exec_composeFamily_multiHybridSim {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (φ : Fin m → Protocol n SubIn SubOut NQ₂ NR₂)
    (S : (j : Fin m) →
      Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
        (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
    (C : Finset (Fin n))
    (Z : Environment n In Out
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)))
    (κ : ℕ) (z : List Bool) :
    (exec (composeFamily ρ φ) (multiHybridSim S) C Z κ z).eval =
      ((SSP.parFin fun j => execMachine (φ j) (S j) κ C).run
        (absorbMultiHybrid C ρ Z κ z)).eval := by
  simp only [exec, execMachine, composeFamily, corruptRouter_comp, multiHybridSim,
    absorbMultiHybrid, Machine.run_comp]
  rw [← Machine.link_comp]
  refine (eval_run_link_swap
    (liftAdversary (n := n) (In := In) (Out := Out) (multiHybridSimMachine fun j => S j κ C))
    (routeCorrupt C (multiHybridWrap (NQ := RoutedNetQ n SubIn NQ₂)
      (NR := RoutedNetR SubOut NR₂) (ρ κ C)))
    (routeCorrupt C (multiHybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
      (NR := RoutedNetR SubOut NR₁) (ρ κ C)))
    (parLiftAdversary fun j => S j κ C)
    _root_.id _root_.id (id_map _) (id_map _)
    (fun q s => handle_swap C (ρ κ C) (fun j => S j κ C) q s.1 s.2)
    (sessionRouter C fun j => φ j κ C) (Z κ z)).trans ?_
  rw [Machine.link_comp, ← Machine.run_comp]
  exact eval_run_parLiftAdversary_comp_sessionRouter C (fun j => φ j κ C) (fun j => S j κ C) _

/-! ### Hybrid telescoping advantage bound and polynomial call budgets -/

/-- Hybrid telescoping bound for `m` fixed sessions: the dummy-adversary distinguishing advantage
between `composeFamily ρ π` and `composeFamily ρ φ` (under `multiHybridSim S`) is at most the
sum over `j : Fin m` of the single-session dummy-adversary distinguishing advantages between `π j`
and `φ j` against `sessionHopEnv C ρ π φ S Z j`. -/
theorem advantage_composeFamily_le_sum {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (π : Fin m → Protocol n SubIn SubOut NQ₁ NR₁)
    (φ : Fin m → Protocol n SubIn SubOut NQ₂ NR₂)
    (S : (j : Fin m) →
      Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
        (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
    (C : Finset (Fin n))
    (Z : Environment n In Out
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)))
    (κ : ℕ) (z : List Bool) :
    advantage (composeFamily ρ π) (composeFamily ρ φ)
        (dummyAdversary n _ _) (multiHybridSim S) C Z κ z ≤
      ∑ j : Fin m,
        advantage (π j) (φ j) (dummyAdversary n _ _) (S j) C
          (sessionHopEnv C ρ π φ S Z j) κ z := by
  rw [advantage, exec_composeFamily_dummy, eval_exec_composeFamily_multiHybridSim]
  refine (SSP.advantage_parFin_le_sum
    (fun j => corruptRouter C (π j κ C))
    (fun j => execMachine (φ j) (S j) κ C)
    (absorbMultiHybrid C ρ Z κ z)).trans_eq ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [advantage, SSP.advantage, sessionHopEnv, exec, execMachine, dummyAdversary,
    Machine.liftRight_id, Machine.run_comp, Machine.link_id]

private theorem isQueryBounded_liftMultiParty {m n : ℕ} {SubIn SubOut NQ NR α : Type}
    {program : ProbOracleComp (multiPartySpec m n SubIn SubOut) α} {t : ℕ}
    (h : OracleComp.IsQueryBounded program t) :
    OracleComp.IsQueryBounded (liftMultiParty (NQ := NQ) (NR := NR) program) t := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query (Sum.inl k)
  | inr c => exact OracleComp.IsCostBounded.query (Sum.inr (c.session, Sum.inl (c.party, c.input)))

/-- Wrapping a `t`-bounded multi-session hybrid machine yields a `(t + 1)`-bounded machine
(accounting for `1`-query forwarding of `.inr (.sub j q)`). -/
theorem isBounded_multiHybridWrap {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    {M : Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR)}
    {t : ℕ} (h : M.IsBounded t) :
    (multiHybridWrap (NQ := NQ) (NR := NR) M).IsBounded (t + 1) := by
  refine ⟨h.1.mono (Nat.le_succ t), fun q s => ?_⟩
  rcases q with p | outer | ⟨j, q⟩
  · exact (isQueryBounded_liftMultiParty (h.2 (.inl p) s)).mono (Nat.le_succ t)
  · dsimp only [multiHybridWrap] at s ⊢
    change OracleComp.IsQueryBounded
      (liftMultiParty ((Sum.inl <$> M.handle (.inr outer)).run s)) (t + 1)
    rw [StateT.run_map, liftMultiParty_map, ← bind_pure_comp]
    refine ((isQueryBounded_liftMultiParty (h.2 (.inr outer) s)).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_succ t)
  · change OracleComp.IsQueryBounded ((StateT.lift (Sum.inr <$>
      ProbOracleComp.query (spec := SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR))
        (j, Sum.inr q))).run s) (t + 1)
    rw [StateT.run_lift, bind_pure_comp, Functor.map_map, ← bind_pure_comp]
    exact ((OracleComp.IsCostBounded.query (Sum.inr (j, Sum.inr q))).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_add_left 1 t)

/-- Absorbing a `pρ`-bounded multi-session hybrid protocol into a `pZ`-bounded environment gives
query bound `(absorbPoly pZ pρ).eval κ`. -/
theorem absorbMultiHybrid_polyBounded {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (C : Finset (Fin n))
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut}
    {Z : Environment n In Out
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))}
    {pρ pZ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (hZ : Z.PolyBounded pZ) :
    ∀ κ z, (absorbMultiHybrid C ρ Z κ z).IsQueryBounded ((absorbPoly pZ pρ).eval κ) := by
  intro κ z
  refine (Machine.isQueryBounded_link
    (isBounded_routeCorrupt C (isBounded_multiHybridWrap (hρ κ C))) (hZ κ z)).mono (le_of_eq ?_)
  simp [absorbPoly, Polynomial.eval_ofNat]

/-- Composing a `pρ`-bounded multi-session hybrid protocol with a family of `pσ`-bounded
protocols yields a `((pρ + 1) * (Polynomial.C m * pσ + 1) + Polynomial.C m * pσ)`-bounded
composed protocol. -/
theorem composeFamily_polyBounded {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut}
    {σ : Fin m → Protocol n SubIn SubOut NQ NR} {pρ pσ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hσ : ∀ j, (σ j).PolyBounded pσ) :
    (composeFamily ρ σ).PolyBounded
      ((pρ + 1) * (Polynomial.C m * pσ + 1) + Polynomial.C m * pσ) := fun κ C =>
  ((isBounded_multiHybridWrap (hρ κ C)).comp
    (SSP.isBounded_parFin fun j => isBounded_routeCorrupt C (hσ j κ C))).mono (le_of_eq (by simp))

/-- Parallel composition `multiHybridSim S` of `pS`-bounded simulators has polynomial call budget
`Polynomial.C m * pS + 1`. -/
theorem multiHybridSim_polyBounded {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    {S : (j : Fin m) →
      Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
        (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)}
    {pS : Polynomial ℕ} (hS : ∀ j, (S j).PolyBounded pS) :
    (multiHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) S).PolyBounded
      (Polynomial.C m * pS + 1) := by
  intro κ C
  refine ⟨?_, fun q s => ?_⟩
  · simpa [multiHybridSim, multiHybridSimMachine] using
      (OracleComp.isCostBounded_pi fun j => (hS j κ C).1).mono (Nat.le_succ (m * pS.eval κ))
  · rcases q with p | outer | ⟨j, q⟩
    -- outer and environment-facing queries are forwarded with one call
    iterate 2
      dsimp only [multiHybridSim, multiHybridSimMachine] at s ⊢
      rw [StateT.run_lift, bind_pure_comp, Functor.map_map, ← bind_pure_comp]
      exact ((OracleComp.IsCostBounded.query _).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (by simp)
    dsimp only [multiHybridSim, multiHybridSimMachine, StateT.run] at s ⊢
    rw [liftMultiSubNet_map, ← bind_pure_comp]
    have hsub : OracleComp.IsQueryBounded
        (liftMultiSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) j
          (((S j κ C).handle q).run (s j))) (pS.eval κ) := by
      refine OracleComp.IsCostBounded.interpret (fun r => ?_) ((hS j κ C).2 q (s j))
      cases r with
      | inl k => exact OracleComp.IsCostBounded.query (Sum.inl k)
      | inr q' =>
        dsimp only [sumHandler]
        rw [← bind_pure_comp]
        exact (OracleComp.IsCostBounded.query _).bind fun _ => OracleComp.IsCostBounded.pure _ 0
    refine (hsub.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono ?_
    simpa using (Nat.le_mul_of_pos_left (pS.eval κ) j.pos).trans (Nat.le_succ _)

/-- Pointwise monotonicity of `sessionHopPoly` in the simulator polynomial bound `pD`. -/
theorem eval_sessionHopPoly_mono {m : ℕ} {pZ pρ pπ pφ pD pD' : Polynomial ℕ}
    (hpD : ∀ κ, pD.eval κ ≤ pD'.eval κ) (κ : ℕ) :
    (sessionHopPoly m pZ pρ pπ pφ pD).eval κ ≤ (sessionHopPoly m pZ pρ pπ pφ pD').eval κ := by
  simp only [sessionHopPoly, sessionUnitPoly, absorbPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_ofNat]
  gcongr <;> exact hpD κ

/-- Each single-hop hybrid distinguisher `sessionHopEnv C ρ π φ S Z j₀` has polynomial call budget
`sessionHopPoly m pZ pρ pπ pφ pD`. -/
theorem sessionHopEnv_polyBounded {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (C : Finset (Fin n))
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut}
    {π : Fin m → Protocol n SubIn SubOut NQ₁ NR₁}
    {φ : Fin m → Protocol n SubIn SubOut NQ₂ NR₂}
    {S : (j : Fin m) →
      Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
        (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)}
    {Z : Environment n In Out
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))}
    {pρ pπ pφ pD pZ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hπ : ∀ j, (π j).PolyBounded pπ)
    (hφ : ∀ j, (φ j).PolyBounded pφ) (hS : ∀ j, (S j).PolyBounded pD)
    (hZ : Z.PolyBounded pZ) (j₀ : Fin m) :
    (sessionHopEnv C ρ π φ S Z j₀).PolyBounded (sessionHopPoly m pZ pρ pπ pφ pD) := by
  intro κ z
  have hreal : ∀ j : Fin m,
      (corruptRouter C (π j κ C)).IsBounded ((sessionUnitPoly pπ pφ pD).eval κ) := fun j =>
    (isBounded_routeCorrupt C (hπ j κ C)).mono (by simp [sessionUnitPoly])
  have hideal : ∀ j : Fin m,
      (execMachine (φ j) (S j) κ C).IsBounded ((sessionUnitPoly pπ pφ pD).eval κ) := fun j =>
    ((Machine.isBounded_liftRight (partySpec n SubIn SubOut) (hS j κ C)).comp
      (isBounded_routeCorrupt C (hφ j κ C))).mono (by simp [sessionUnitPoly])
  refine (SSP.isQueryBounded_hybridDistinguisher
    (fun j => corruptRouter C (π j κ C)) (fun j => execMachine (φ j) (S j) κ C)
    j₀ hreal hideal (absorbMultiHybrid_polyBounded C hρ hZ κ z)).mono (le_of_eq ?_)
  simp only [sessionHopPoly, sessionUnitPoly, absorbPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_ofNat]

/-! ### Multi-session UC composition theorems -/

private theorem emulatesDummyWithin_mono_bound {n : ℕ} {In Out NQ₁ NR₁ NQ₂ NR₂ : Type}
    {π : Protocol n In Out NQ₁ NR₁} {φ : Protocol n In Out NQ₂ NR₂}
    {pD pD' : Polynomial ℕ} {ε : Polynomial ℕ → ℕ → ℝ≥0}
    (h : EmulatesDummyWithin π φ pD ε) (hp : ∀ κ, pD.eval κ ≤ pD'.eval κ) :
    EmulatesDummyWithin π φ pD' ε := by
  rcases h with ⟨S_D, hSD, hadv⟩
  exact ⟨S_D, hSD.mono hp, hadv⟩

/-- Fixed-session composition step for `EmulatesDummyWithin`, this library's own call-bounded
dummy-adversary emulation relation, with an explicit parallel simulator `multiHybridSim` over a
fixed family of `m` sessions sharing party count, party input/output types, and one fixed network
interface per side (implementations and private state types may vary per session).
Adapts Theorem 22 and Section 6.3 of [Canetti2020] (JACM p. 28:58, p. 28:67; ePrint 2000/067,
pp. 61, 70) to static corruptions and a fixed `Fin m` session family; see the module docstring for
the relation to Canetti's PPT theorem. -/
theorem EmulatesDummyWithin.composeFamily {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut}
    {π : Fin m → Protocol n SubIn SubOut NQ₁ NR₁}
    {φ : Fin m → Protocol n SubIn SubOut NQ₂ NR₂}
    {pρ pπ pφ pD : Polynomial ℕ} {ε : Fin m → Polynomial ℕ → ℕ → ℝ≥0}
    (hρ : ρ.PolyBounded pρ) (hπ : ∀ j, (π j).PolyBounded pπ) (hφ : ∀ j, (φ j).PolyBounded pφ)
    (h : ∀ j, EmulatesDummyWithin (π j) (φ j) pD (ε j)) :
    EmulatesDummyWithin (composeFamily ρ π) (composeFamily ρ φ)
      (Polynomial.C m * pD + 1)
      (fun pZ κ => ∑ j : Fin m, ε j (sessionHopPoly m pZ pρ pπ pφ pD) κ) := by
  choose S_D hSD hadv using h
  refine ⟨multiHybridSim S_D, multiHybridSim_polyBounded hSD, fun C Z pZ hZ κ z => ?_⟩
  refine (advantage_composeFamily_le_sum ρ π φ S_D C Z κ z).trans (Finset.sum_le_sum fun j _ => ?_)
  exact hadv j C _ _ (sessionHopEnv_polyBounded C hρ hπ hφ hSD hZ j) κ z

/-- Fixed-session homogeneous composition step for `EmulatesDummyWithin`, this library's own
call-bounded dummy-adversary emulation relation, specializing `EmulatesDummyWithin.composeFamily`
to `m` instances of a single subroutine protocol `π` replaced by `φ`.
Adapts Theorem 22 of [Canetti2020] (JACM p. 28:58; ePrint 2000/067, p. 61) to static corruptions
and a fixed `Fin m` session count; see the module docstring for the relation to Canetti's PPT
theorem. -/
theorem EmulatesDummyWithin.composeMulti {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut}
    {π : Protocol n SubIn SubOut NQ₁ NR₁} {φ : Protocol n SubIn SubOut NQ₂ NR₂}
    {pρ pπ pφ pD : Polynomial ℕ} {ε : Polynomial ℕ → ℕ → ℝ≥0}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hφ : φ.PolyBounded pφ)
    (h : EmulatesDummyWithin π φ pD ε) :
    EmulatesDummyWithin (composeMulti ρ π) (composeMulti ρ φ)
      (Polynomial.C m * pD + 1)
      (fun pZ κ => m • ε (sessionHopPoly m pZ pρ pπ pφ pD) κ) := by
  simpa [composeMulti, Finset.sum_const, Finset.card_fin] using
    EmulatesDummyWithin.composeFamily hρ (fun _ => hπ) (fun _ => hφ) (fun _ => h)

/-- Fixed-session quantitative composition step for `EmulatesWithin`, this library's own
call-bounded emulation relation, yielding explicit simulator call overhead and distinguishing bound
`m • ε 1 (sessionHopPoly m (absorbPoly pZ pA) pρ pπ pφ (g.comp (X + 1)))`.
Adapts Theorem 22 of [Canetti2020] (JACM p. 28:58; ePrint 2000/067, p. 61) to static corruptions
and a fixed `Fin m` session count; see the module docstring for the relation to Canetti's PPT
theorem. -/
theorem EmulatesWithin.composeMulti {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut}
    {π : Protocol n SubIn SubOut NQ₁ NR₁} {φ : Protocol n SubIn SubOut NQ₂ NR₂}
    {pρ pπ pφ g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hφ : φ.PolyBounded pφ)
    (h : EmulatesWithin π φ g ε) :
    EmulatesWithin (composeMulti ρ π) (composeMulti ρ φ)
      (Polynomial.X * (Polynomial.C m * g.comp (Polynomial.X + 1) + 1 + 1) +
        (Polynomial.C m * g.comp (Polynomial.X + 1) + 1))
      (fun pA pZ κ =>
        m • ε 1 (sessionHopPoly m (absorbPoly pZ pA) pρ pπ pφ
          (g.comp (Polynomial.X + 1))) κ) := by
  rcases h.emulatesDummyWithin with ⟨pD, hpD, hD⟩
  have hD' : EmulatesDummyWithin π φ (g.comp (Polynomial.X + 1)) (fun pZ => ε 1 pZ) :=
    emulatesDummyWithin_mono_bound hD fun κ => by
      simpa [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
        using hpD κ
  exact (EmulatesDummyWithin.composeMulti hρ hπ hφ hD').emulatesWithin

/-- Fixed-session composition step for `Emulates`, this library's own call-bounded emulation
relation, with an explicit parallel simulator and one fixed interface per side: protocol
implementations and private state types may vary per session `j : Fin m`, while party count `n`,
party input/output types, and each side's network message types are shared across sessions.
Adapts Theorem 22 and Section 6.3 of [Canetti2020] (JACM p. 28:58, p. 28:67; ePrint 2000/067,
pp. 61, 70) to static corruptions and a fixed `Fin m` session family; see the module docstring for
the relation to Canetti's PPT theorem. -/
theorem Emulates.composeFamily {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut}
    {π : Fin m → Protocol n SubIn SubOut NQ₁ NR₁}
    {φ : Fin m → Protocol n SubIn SubOut NQ₂ NR₂}
    {pρ pπ pφ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hπ : ∀ j, (π j).PolyBounded pπ) (hφ : ∀ j, (φ j).PolyBounded pφ)
    (h : ∀ j, Emulates (π j) (φ j)) :
    Emulates (composeFamily ρ π) (composeFamily ρ φ) := by
  choose S_D pD hSD hadv using
    fun j => h j _ _ (dummyAdversary n _ _) 1 (dummyAdversary_polyBounded n _ _)
  let pD_max : Polynomial ℕ := ∑ j : Fin m, pD j
  have hdummy (j : Fin m) : ∃ ε : Polynomial ℕ → ℕ → ℝ≥0,
      (∀ pZ, Negligible (ε pZ)) ∧ EmulatesDummyWithin (π j) (φ j) pD_max ε := by
    choose ε hε hε_adv using hadv j
    refine ⟨ε, hε, S_D j, (hSD j).mono fun κ => ?_, fun C Z pZ hZ κ z => hε_adv pZ C Z hZ κ z⟩
    exact (Finset.single_le_sum (f := fun i => (pD i).eval κ) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans_eq (map_sum (Polynomial.evalRingHom κ) pD Finset.univ).symm
  choose ε hε hD using hdummy
  refine (EmulatesDummyWithin.composeFamily hρ hπ hφ hD).emulatesWithin.emulates fun pA pZ => ?_
  rw [← Finset.sum_fn]
  exact Negligible.sum Finset.univ fun j _ =>
    hε j (sessionHopPoly m (absorbPoly pZ pA) pρ pπ pφ pD_max)

/-- Fixed-session homogeneous composition step for `Emulates`, this library's own call-bounded
emulation relation, specializing `Emulates.composeFamily` to `m` instances of `π` replaced by `φ`.
Adapts Theorem 22 of [Canetti2020] (JACM p. 28:58; ePrint 2000/067, p. 61) to static corruptions
and a fixed `Fin m` session count; see the module docstring for the relation to Canetti's PPT
theorem. -/
theorem Emulates.composeMulti {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut}
    {π : Protocol n SubIn SubOut NQ₁ NR₁} {φ : Protocol n SubIn SubOut NQ₂ NR₂}
    {pρ pπ pφ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hφ : φ.PolyBounded pφ)
    (h : Emulates π φ) :
    Emulates (composeMulti ρ π) (composeMulti ρ φ) :=
  Emulates.composeFamily hρ (fun _ => hπ) (fun _ => hφ) (fun _ => h)

/-- Fixed-session composition step for `Realizes`, this library's own call-bounded emulation
relation against an ideal functionality, replacing `m` instances of `F` in `composeMulti ρ` with
a protocol `π` that realizes `F`.
Adapts Corollary 23 of [Canetti2020] (JACM p. 28:59; ePrint 2000/067, p. 62) to static corruptions
and a fixed `Fin m` session count; see the module docstring for the relation to Canetti's PPT
theorem. -/
theorem Realizes.composeMulti {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR BackQ BackR : Type}
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut}
    {π : Protocol n SubIn SubOut NQ NR}
    {F : IdealFunctionality n SubIn SubOut BackQ BackR}
    {pρ pπ pF : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hF : F.toProtocol.PolyBounded pF)
    (h : Realizes π F) :
    Emulates (composeMulti ρ π) (composeMulti ρ F.toProtocol) :=
  Emulates.composeMulti hρ hπ hF h

/-- Fixed-session transitive hybrid replacement step for `Realizes`, this library's own
call-bounded emulation relation against an ideal functionality: if `π` realizes `F` and
`composeMulti ρ F.toProtocol` realizes `G`, then `composeMulti ρ π` realizes `G`.
Adapts Corollary 24 of [Canetti2020] (JACM p. 28:59; ePrint 2000/067, p. 62) to static corruptions
and a fixed `Fin m` session count; see the module docstring for the relation to Canetti's PPT
theorem. -/
theorem Realizes.composeMulti_trans {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR BackQ BackR GQ GR : Type}
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut}
    {π : Protocol n SubIn SubOut NQ NR}
    {F : IdealFunctionality n SubIn SubOut BackQ BackR}
    {G : IdealFunctionality n In Out GQ GR}
    {pρ pπ pF : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hF : F.toProtocol.PolyBounded pF)
    (hπF : Realizes π F) (hρG : Realizes (UC.composeMulti ρ F.toProtocol) G) :
    Realizes (UC.composeMulti ρ π) G :=
  Emulates.trans (Realizes.composeMulti hρ hπ hF hπF) hρG

end Cslib.Crypto.Protocols.UC
