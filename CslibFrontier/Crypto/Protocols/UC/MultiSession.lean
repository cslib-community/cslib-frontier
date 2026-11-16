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

This module extends the single-session UC composition theorem of
`CslibFrontier/Crypto/Protocols/UC/Composition.lean` to a fixed finite family of `m` subroutine
sessions (`Fin m`), adapting Theorem 22, Corollaries 23–24, and the heterogeneous-family extension
of Section 6.3 of [Canetti2020] in the fixed-session, static-corruption, call-bounded model, via
the multi-session state-separating hybrid bound `SSP.advantage_parFin_le_sum` [BrzuskaDFKK2018].

## Scope and fidelity gaps relative to [Canetti2020]

This is a **fixed number `m` of sessions chosen in advance; not dynamic session creation; this is
not the full Theorem 22**. Specifically:

1. **Fixed `Fin m` session family vs. dynamic `SID` spawning.** In Theorem 22 of [Canetti2020]
   (JACM p. 28:58; ePrint 2000/067, rev. February 11, 2020, p. 61), a calling protocol dynamically
   spawns `poly(κ)` subroutine sessions indexed by bitstring session identifiers across a recursive
   ITI call tree. Here `m : ℕ` is a fixed finite arity (`Fin m`) of depth-1 subroutine sessions,
   universally quantified over `{m : ℕ}` in every theorem (so concrete `EmulatesWithin` bounds
   instantiate `m := q.eval κ` at any fixed security parameter `κ`). Because each session's
   initializer `(σ j κ C).init` is a proper distribution (`ProbComp`), eager initialization of all
   `m` independent states in `SSP.parFin` induces the same observable marginal distribution on all
   queried sessions as lazy first-touch `SID` spawning up to capacity `m`, and any deterministic
   first-touch `SID → Fin m` allocator inside `ρ` factors through `Fin m`.
2. **Call-bounded statistical participants vs. PPT ITMs.** `MultiHybridProtocol.PolyBounded`,
   `Protocol.PolyBounded`, `Adversary.PolyBounded`, and `Environment.PolyBounded` bound only the
   number of oracle and randomness calls per activation (or total for `Z`) by a `Polynomial ℕ`, as
   in Section 4.4 of [Canetti2020] (JACM p. 28:48; ePrint p. 50); pure computation, state size,
   and message length are unbounded.
3. **Static same-party corruptions `C : Finset (Fin n)` vs. adaptive per-identity corruptions.**
   The calling protocol `ρ κ C` and all `m` subroutine sessions `corruptRouter C (σ j κ C)` share
   the same static corruption set `C`, fixed prior to execution.
4. **Structural type-level isolation and compliance vs. runtime predicates.** Subroutine-respecting
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

* `Cslib.Crypto.Protocols.UC.SubSessionCall`: named record for a party-port call to session `j`.
* `Cslib.Crypto.Protocols.UC.multiPartySpec`, `Cslib.Crypto.Protocols.UC.MultiHybridProtocol`,
  `Cslib.Crypto.Protocols.UC.MultiHybridProtocol.PolyBounded`: multi-session hybrid protocols.
* `Cslib.Crypto.Protocols.UC.MultiNetQ`, `Cslib.Crypto.Protocols.UC.MultiNetR`: composed network
  ports tagging outer vs. per-session subroutine traffic.
* `Cslib.Crypto.Protocols.UC.sessionRouter`: `m` isolated static-corruption sessions via
  `SSP.parFin`.
* `Cslib.Crypto.Protocols.UC.multiHybridWrap`, `Cslib.Crypto.Protocols.UC.composeFamily`,
  `Cslib.Crypto.Protocols.UC.composeMulti`: multi-session subroutine replacement.
* `Cslib.Crypto.Protocols.UC.multiHybridSim`, `Cslib.Crypto.Protocols.UC.multiHybridSimConst`:
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

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], J. ACM 67(5), Article 28, 2020:
  Section 6.1 (Theorem 22 p. 28:58; Corollaries 23–24 p. 28:59), Section 6.2.1 (hybrid proof,
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

/-- A subroutine party-port call from a multi-session hybrid protocol: party `party` passes
`input` to subroutine session `session` (or polls it). -/
structure SubSessionCall (m n : ℕ) (SubIn : Type) : Type where
  /-- Target subroutine session index (`0 ≤ session < m`). -/
  session : Fin m
  /-- Calling party index (`0 ≤ party < n`). -/
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

/-- Network-side reply from a multi-session composed protocol. -/
inductive MultiNetR (NetR SubRoutedR : Type) : Type
  /-- A reply from the outer calling protocol `ρ`'s own network port. -/
  | outer (reply : NetR)
  /-- A reply from the addressed subroutine session's routed network port. -/
  | sub (reply : SubRoutedR)
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
is exposed under `MultiNetQ.sub j` / `MultiNetR.sub`. -/
@[expose] def multiHybridWrap {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (M : Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR)) :
    Machine (SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR))
      (protocolSpec n In Out (MultiNetQ m NetQ NQ) (MultiNetR NetR NR)) where
  State := M.State
  init := M.init
  handle
    | .inl p => fun s => liftMultiParty ((M.handle (.inl p)).run s)
    | .inr (.outer q) => fun s => liftMultiParty ((MultiNetR.outer <$> M.handle (.inr q)).run s)
    | .inr (.sub j q) => StateT.lift (MultiNetR.sub <$>
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
      (MultiNetR NetR (RoutedNetR SubOut NR)) :=
  fun κ C => (multiHybridWrap (ρ κ C)).comp (sessionRouter C fun j => σ j κ C)

/-- Homogeneous multi-session subroutine replacement: `ρ` calling `m` independent instances of the
same protocol `σ`. -/
abbrev composeMulti {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (σ : Protocol n SubIn SubOut NQ NR) :
    Protocol n In Out
      (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ))
      (MultiNetR NetR (RoutedNetR SubOut NR)) :=
  composeFamily ρ (fun _ => σ)

/-! ### Multi-session simulator, absorbed hybrid, and single-hop reduction environment -/

private def multiSubReply {Out NetR SubOut NR : Type} :
    RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR)) → RoutedNetR SubOut NR
  | .inr (.sub r) => r
  | _ => .inl none

private def multiOuterReply {Out NetR SubOut NR₁ NR₂ : Type} :
    RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₂)) →
      RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₁))
  | .inl o => .inl o
  | .inr (.outer r) => .inr (.outer r)
  | .inr (.sub _) => .inl none

private def liftMultiSubNet {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR α : Type}
    (j : Fin m)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α) :
    ProbOracleComp
      (netSpec (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ)))
        (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR)))) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (netSpec
          (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ)))
          (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR)))))
        (Sum.inl k))
      fun q => multiSubReply <$> ProbOracleComp.query
        (spec := netSpec
          (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ)))
          (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR))))
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
        (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₂))))
      (netSpec (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₁)))
        (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₁)))) where
  State := (j : Fin m) → (S j).State
  init := OracleComp.pi fun j => (S j).init
  handle
    | .inl p => StateT.lift (multiOuterReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₂)))) (.inl p))
    | .inr (.outer q) => StateT.lift (multiOuterReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₂)))) (.inr (.outer q)))
    | .inr (.sub j q) => fun s =>
        liftMultiSubNet j ((fun x => (Sum.inr (MultiNetR.sub x.1), Function.update s j x.2)) <$>
          ((S j).handle q).run (s j))

/-- The composed simulator for `composeFamily ρ π` against `composeFamily ρ φ`, running an
independent simulator `S j` for each subroutine session `j : Fin m`. -/
@[expose] def multiHybridSim {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) →
      Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
        (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) :
    Adversary n
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₁)))
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
      (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₂))) :=
  fun κ C => multiHybridSimMachine fun j => S j κ C

/-- Homogeneous specialization of `multiHybridSim` using one shared simulator `S` across all `m`
sessions. -/
abbrev multiHybridSimConst {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) :=
  multiHybridSim (m := m) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) (fun _ => S)

/-- Absorbing `ρ κ C` into an environment `Z` produces a distinguisher against the `m`-session
subroutine interface `SSP.sessionSpec m (protocolSpec n SubIn SubOut …)`. -/
@[expose] def absorbMultiHybrid {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (C : Finset (Fin n))
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (Z : Environment n In Out
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ)))
      (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR))))
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
      (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₁))))
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
      (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR))))
    (κ : ℕ) (z : List Bool) :
    exec (composeFamily ρ π) (dummyAdversary n _ _) C Z κ z =
      (sessionRouter C fun j => π j κ C).run (absorbMultiHybrid C ρ Z κ z) := by
  simp only [exec, execMachine, dummyAdversary, liftAdversary_id, Machine.run_comp,
    Machine.link_id, composeFamily, corruptRouter_comp, absorbMultiHybrid]

section Swap

private theorem runFrom_query_sample {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    (M : Machine I E) (k : ℕ) (s : M.State) :
    M.runFrom (OracleComp.query (spec := probOracleSpec E) (Sum.inl k)) s =
      (fun a => (a, s)) <$> OracleComp.query (spec := probOracleSpec I) (Sum.inl k) := by
  rw [Machine.runFrom_call]
  change (StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k))).run s = _
  rw [StateT.run_lift, bind_pure_comp]
  rfl

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
  | inr c =>
    change (parLiftAdversary S).runFrom
      (ProbOracleComp.query (c.session, Sum.inl (c.party, c.input))) s = _
    rw [Machine.runFrom_query]
    change (StateT.lift (ProbOracleComp.query _)).run s = _
    rw [StateT.run_lift, bind_pure_comp]
    rfl

private theorem liftMultiParty_map {m n : ℕ} {SubIn SubOut NQ NR α β : Type} (f : α → β)
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

private theorem routeCorrupt_handle_inl {n : ℕ} {In Out NetQ NetR : Type}
    {ιI : Type} {I : ιI → Type} (C : Finset (Fin n))
    (P : Machine I (protocolSpec n In Out NetQ NetR)) (i : Fin n) (x : In) (s : P.State) :
    ((routeCorrupt C P).handle (.inl (i, x))).run s =
      if i ∈ C then pure (none, s) else (P.handle (.inl (i, x))).run s := by
  change (if i ∈ C then pure none else P.handle (.inl (i, x)) :
    StateT P.State (ProbOracleComp I) (Option Out)).run s = _
  split_ifs <;> rfl

private theorem routeCorrupt_handle_inr_inl {n : ℕ} {In Out NetQ NetR : Type}
    {ιI : Type} {I : ιI → Type} (C : Finset (Fin n))
    (P : Machine I (protocolSpec n In Out NetQ NetR)) (i : Fin n) (x : In) (s : P.State) :
    ((routeCorrupt C P).handle (.inr (.inl (i, x)))).run s =
      if i ∈ C then (fun p => (Sum.inl p.1, p.2)) <$> (P.handle (.inl (i, x))).run s
      else pure (.inl none, s) := by
  change (if i ∈ C then Sum.inl <$> P.handle (.inl (i, x)) else pure (.inl none) :
    StateT P.State (ProbOracleComp I) (RoutedNetR Out NetR)).run s = _
  split_ifs
  · exact StateT.run_map _ _ _
  · rfl

private theorem routeCorrupt_handle_inr_inr {n : ℕ} {In Out NetQ NetR : Type}
    {ιI : Type} {I : ιI → Type} (C : Finset (Fin n))
    (P : Machine I (protocolSpec n In Out NetQ NetR)) (q : NetQ) (s : P.State) :
    ((routeCorrupt C P).handle (.inr (.inr q))).run s =
      (fun p => (Sum.inr p.1, p.2)) <$> (P.handle (.inr q)).run s :=
  StateT.run_map _ _ _

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
      (fun p => (MultiNetR.outer p.1, p.2)) <$> liftMultiParty ((M.handle (.inr q)).run s) := by
  change liftMultiParty ((MultiNetR.outer <$> M.handle (.inr q)).run s) = _
  rw [StateT.run_map, liftMultiParty_map]

private theorem multiHybridWrap_handle_inr_sub {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (M : Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR))
    (j : Fin m) (q : NQ) (s : M.State) :
    ((multiHybridWrap (NR := NR) M).handle (.inr (.sub j q))).run s =
      (fun a => (MultiNetR.sub a, s)) <$>
        ProbOracleComp.query (spec := SSP.sessionSpec m (protocolSpec n SubIn SubOut NQ NR))
          (j, Sum.inr q) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem liftAdversary_handle_inl {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    (A : Machine (netSpec NetQ NetR) (netSpec AdvQ AdvR)) (p : Fin n × In) (s : A.State) :
    ((liftAdversary (n := n) (In := In) (Out := Out) A).handle (.inl p)).run s =
      (fun a => (a, s)) <$>
        ProbOracleComp.query (spec := protocolSpec n In Out NetQ NetR) (Sum.inl p) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp]

private theorem liftAdversary_handle_inr {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    (A : Machine (netSpec NetQ NetR) (netSpec AdvQ AdvR)) (q : AdvQ) (s : A.State) :
    ((liftAdversary (n := n) (In := In) (Out := Out) A).handle (.inr q)).run s =
      liftNet ((A.handle q).run s) := rfl

private theorem multiHybridSimMachine_handle_inl {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (p : Fin n × In) (s : (multiHybridSimMachine S).State) :
    ((multiHybridSimMachine (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) S).handle
        (.inl p)).run s =
      (fun a => (multiOuterReply a, s)) <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₂)))) (.inl p) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem multiHybridSimMachine_handle_inr_outer {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (q : NetQ) (s : (multiHybridSimMachine S).State) :
    ((multiHybridSimMachine (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) S).handle
        (.inr (.outer q))).run s =
      (fun a => (multiOuterReply a, s)) <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₂)))) (.inr (.outer q)) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem multiHybridSimMachine_handle_inr_sub {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (j : Fin m) (q : RoutedNetQ n SubIn NQ₁) (s : (multiHybridSimMachine S).State) :
    ((multiHybridSimMachine (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) S).handle
        (.inr (.sub j q))).run s =
      (fun x => (Sum.inr (MultiNetR.sub x.1), Function.update s j x.2)) <$>
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
  rw [liftNet, liftMultiSubNet, OracleComp.interpret_interpret, liftSessionNet]
  refine Machine.runFrom_interpret_of_forward (routeCorrupt C (multiHybridWrap M)) _ _
    (fun q s => ?_) program s
  cases q with
  | inl k =>
    simp only [OracleComp.interpret_query]
    exact runFrom_query_sample _ k s
  | inr q =>
    simp only [OracleComp.interpret_map, ProbOracleComp.interpret_query, Machine.runFrom_map,
      Machine.runFrom_query]
    change Prod.map multiSubReply _root_.id <$> ((Sum.inr <$> StateT.lift (MultiNetR.sub <$>
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
    by_cases hi : i ∈ C
    · simp only [hi, ↓reduceIte]
      rfl
    · simp only [hi, ↓reduceIte]
      erw [multiHybridWrap_handle_inl, multiHybridWrap_handle_inl,
        runFrom_parLiftAdversary_liftMultiParty]
      repeat erw [Functor.map_map]
      rfl
  · erw [liftAdversary_handle_inr, multiHybridSimMachine_handle_inl, liftNet_map, liftNet_query,
      Machine.runFrom_map, Machine.runFrom_query, routeCorrupt_handle_inr_inl,
      routeCorrupt_handle_inr_inl]
    by_cases hi : i ∈ C
    · simp only [hi, ↓reduceIte]
      erw [multiHybridWrap_handle_inl, multiHybridWrap_handle_inl, Machine.runFrom_map,
        runFrom_parLiftAdversary_liftMultiParty]
      repeat erw [Functor.map_map]
      rfl
    · simp only [hi, ↓reduceIte]
      rfl
  · erw [liftAdversary_handle_inr, multiHybridSimMachine_handle_inr_outer, liftNet_map,
      liftNet_query, Machine.runFrom_map, Machine.runFrom_query, routeCorrupt_handle_inr_inr,
      routeCorrupt_handle_inr_inr, multiHybridWrap_handle_inr_outer,
      multiHybridWrap_handle_inr_outer]
    repeat erw [Functor.map_map]
    erw [Machine.runFrom_map, runFrom_parLiftAdversary_liftMultiParty]
    repeat erw [Functor.map_map]
    rfl
  · erw [liftAdversary_handle_inr, multiHybridSimMachine_handle_inr_sub, liftNet_map,
      Machine.runFrom_map, runFrom_routeCorrupt_liftNet_liftMultiSubNet,
      routeCorrupt_handle_inr_inr, multiHybridWrap_handle_inr_sub]
    repeat erw [Functor.map_map]
    erw [Machine.runFrom_map, Machine.runFrom_query, parLiftAdversary_handle_inr,
      liftSessionNet_map]
    repeat erw [Functor.map_map]
    rfl

private theorem eval_run_sample_bind_swap {ιJ : Type} {J : ιJ → Type} {σ τ α : Type}
    (R : Machine OracleSpec.empty J) (p : ProbComp σ) (q : ProbComp τ)
    (k : τ × σ → ProbOracleComp J α) :
    (R.run (ProbOracleComp.sample (do
        let a ← p
        let b ← q
        return (b, a)) >>= k)).eval =
      (R.run (ProbOracleComp.sample (do
        let b ← q
        let a ← p
        return (a, b)) >>= fun s => k s.swap)).eval := by
  simp only [Machine.run, Machine.link, Machine.runFrom_bind, Machine.runFrom_sample,
    bind_map_left, map_bind, Machine.closeProgram_bind, Machine.closeProgram_sample,
    ProbOracleComp.sample_bind, ProbOracleComp.sample_pure, bind_assoc, pure_bind,
    Prod.swap_prod_mk, ProbComp.eval_bind]
  congr 1 with sR : 1
  exact PMF.bind_comm _ _ _

private theorem eval_run_link_swap
    {m n : ℕ} {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ α : Type}
    (C : Finset (Fin n))
    (M : Machine (multiPartySpec m n SubIn SubOut) (protocolSpec n In Out NetQ NetR))
    (S : (j : Fin m) → Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (R : Machine OracleSpec.empty
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₂)
        (RoutedNetR SubOut NR₂))))
    (Z : ProbOracleComp (execSpec n In Out
      (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₁)))) α) :
    (R.run (((liftAdversary (n := n) (In := In) (Out := Out)
        (multiHybridSimMachine S)).comp (routeCorrupt C (multiHybridWrap
          (NQ := RoutedNetQ n SubIn NQ₂) (NR := RoutedNetR SubOut NR₂) M))).link Z)).eval =
      (R.run (((routeCorrupt C (multiHybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
          (NR := RoutedNetR SubOut NR₁) M)).comp (parLiftAdversary S)).link Z)).eval := by
  set A := (liftAdversary (n := n) (In := In) (Out := Out) (multiHybridSimMachine S)).comp
    (routeCorrupt C (multiHybridWrap (NQ := RoutedNetQ n SubIn NQ₂)
      (NR := RoutedNetR SubOut NR₂) M))
  set B := (routeCorrupt C (multiHybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
    (NR := RoutedNetR SubOut NR₁) M)).comp (parLiftAdversary S)
  have hrun (s : B.State) : Prod.fst <$> B.runFrom Z s = Prod.fst <$> A.runFrom Z s.swap := by
    rw [Machine.runFrom_map_state A B Prod.swap (fun q s => handle_swap C M S q s.1 s.2) Z s,
      Functor.map_map]
    rfl
  have hB : B.link Z =
      ProbOracleComp.sample B.init >>= fun s => Prod.fst <$> A.runFrom Z s.swap := by
    rw [Machine.link]
    exact bind_congr hrun
  rw [hB, Machine.link]
  exact eval_run_sample_bind_swap R M.init (OracleComp.pi fun j => (S j).init)
    (fun s => Prod.fst <$> A.runFrom Z s)

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
    simp only [liftSessionNet, liftNet, OracleComp.interpret_pure, Machine.runFrom_pure,
      map_pure]
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
          ProbComp.unifFin]
      have h₂ : liftNet (n := n) (In := SubIn) (Out := SubOut)
          (OracleComp.query (spec := probOracleSpec (netSpec (RoutedNetQ n SubIn NQ)
            (RoutedNetR SubOut NR))) (Sum.inl k)) =
          ProbOracleComp.sample (ProbComp.unifFin k) := by
        rw [← liftNet_sample (NetQ := RoutedNetQ n SubIn NQ) (NetR := RoutedNetR SubOut NR)]
        rfl
      simp only [liftSessionNet, liftNet, OracleComp.interpret_bind]
      change (sessionRouter C φ).runFrom
          (liftSessionNet j (OracleComp.query (.inl k)) >>= fun a =>
            liftSessionNet j (cont a)) s =
        (fun x => (x.1, Function.update s j x.2)) <$> (corruptRouter C (φ j)).runFrom
          (liftNet (OracleComp.query (.inl k)) >>= fun a => liftNet (cont a)) (s j)
      rw [h₁, h₂, Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_sample,
        Machine.runFrom_sample, bind_map_left, bind_map_left, map_bind]
      exact bind_congr fun a => ih a s
    | inr e =>
      simp only [liftSessionNet, liftNet, OracleComp.interpret_bind]
      change (sessionRouter C φ).runFrom
          (ProbOracleComp.query (j, Sum.inr e) >>= fun a => liftSessionNet j (cont a)) s =
        (fun x => (x.1, Function.update s j x.2)) <$> (corruptRouter C (φ j)).runFrom
          (ProbOracleComp.query (Sum.inr e) >>= fun a => liftNet (cont a)) (s j)
      rw [Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_query]
      erw [SSP.parFin_handle, bind_map_left, map_bind]
      refine bind_congr fun x => ?_
      rw [ih x.1 (Function.update s j x.2)]
      erw [Function.update_self]
      congr 1
      funext y
      erw [Function.update_idem]

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
    rcases q with p | nq
    · change (Machine.closeProgram (Equiv.prodAssoc _ _ _ <$>
          (sessionRouter C φ).runFrom
            ((StateT.lift (ProbOracleComp.query (j, Sum.inl p))).run sS) sφ)).eval.map
          (fun x => (x.1, fun i => (x.2.1 i, x.2.2 i))) =
        (Machine.closeProgram (((SSP.parFin fun i => (liftAdversary (S i)).comp
          (corruptRouter C (φ i))).handle (j, Sum.inl p)).run fun i => (sS i, sφ i))).eval
      rw [StateT.run_lift, bind_pure_comp]
      erw [Machine.runFrom_map, Machine.runFrom_query, SSP.parFin_handle]
      erw [SSP.parFin_handle]
      simp only [Machine.comp, liftAdversary, StateT.run, StateT.lift, bind_pure_comp]
      erw [Machine.runFrom_map, Machine.runFrom_query]
      repeat erw [Machine.closeProgram_map]
      repeat erw [ProbComp.eval_map]
      repeat erw [PMF.map_comp]
      refine congrArg (PMF.map · _) (funext fun x => ?_)
      dsimp only [sessionRouter, parLiftAdversary, SSP.parFin] at x sS sφ ⊢
      repeat erw [Function.comp_apply]
      repeat erw [Equiv.prodAssoc_apply]
      repeat erw [Prod.map_apply]
      dsimp only [id_eq]
      rcases x with ⟨r, sφ'⟩
      refine Prod.ext rfl (funext fun i => ?_)
      by_cases hi : i = j
      · subst hi
        dsimp only
        simp only [Function.update_self]
      · dsimp only
        simp only [Function.update_of_ne hi]
    · change (Machine.closeProgram (Equiv.prodAssoc _ _ _ <$>
          (sessionRouter C φ).runFrom
            (liftSessionNet j ((fun x => (x.1, Function.update sS j x.2)) <$>
              ((S j).handle nq).run (sS j))) sφ)).eval.map
          (fun x => (x.1, fun i => (x.2.1 i, x.2.2 i))) =
        (Machine.closeProgram (((SSP.parFin fun i => (liftAdversary (S i)).comp
          (corruptRouter C (φ i))).handle (j, Sum.inr nq)).run fun i => (sS i, sφ i))).eval
      rw [liftSessionNet_map]
      erw [Machine.runFrom_map, runFrom_sessionRouter_liftSessionNet]
      erw [SSP.parFin_handle]
      simp only [Machine.comp, liftAdversary, StateT.run]
      repeat erw [Machine.closeProgram_map]
      repeat erw [ProbComp.eval_map]
      repeat erw [PMF.map_comp]
      refine congrArg (PMF.map · _) (funext fun x => ?_)
      dsimp only [sessionRouter, parLiftAdversary, SSP.parFin] at x sS sφ ⊢
      repeat erw [Function.comp_apply]
      repeat erw [Equiv.prodAssoc_apply]
      repeat erw [Prod.map_apply]
      dsimp only [id_eq]
      rcases x with ⟨⟨r, sS'⟩, sφ'⟩
      refine Prod.ext rfl (funext fun i => ?_)
      by_cases hi : i = j
      · subst hi
        dsimp only
        simp only [Function.update_self]
      · dsimp only
        simp only [Function.update_of_ne hi]

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
      (RoutedNetR Out (MultiNetR NetR (RoutedNetR SubOut NR₁))))
    (κ : ℕ) (z : List Bool) :
    (exec (composeFamily ρ φ) (multiHybridSim S) C Z κ z).eval =
      ((SSP.parFin fun j => execMachine (φ j) (S j) κ C).run
        (absorbMultiHybrid C ρ Z κ z)).eval := by
  simp only [exec, execMachine, composeFamily, corruptRouter_comp, multiHybridSim,
    absorbMultiHybrid, Machine.run_comp]
  rw [← Machine.link_comp]
  refine (eval_run_link_swap C (ρ κ C) (fun j => S j κ C)
    (sessionRouter C fun j => φ j κ C) (Z κ z)).trans ?_
  rw [Machine.link_comp, ← Machine.run_comp]
  exact eval_run_parLiftAdversary_comp_sessionRouter C (fun j => φ j κ C) (fun j => S j κ C) _

end Cslib.Crypto.Protocols.UC
