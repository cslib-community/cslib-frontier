/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Protocols.UC.Commitment
import CslibFrontier.Crypto.Protocols.UC.HybridFunctionality
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm

/-!
# Tests for ideal functionalities with a private outgoing call port

This test suite exercises `UC.HybridFunctionality` on two concrete 2-party witnesses:

1. **Coin relay (resource swap is visible, growing state, static corruption `C = {1}`):**
   `coinRelay` answers party `0`'s inputs by calling a private coin resource
   `G := netSpec Unit Bool` once, recording the returned bit and incrementing a call counter in its
   state (`CoinRelayState`), and exposing the call counter on its backdoor; party `1`'s inputs
   return `none`. Closing `coinRelay` with `fairCoinResource` (which samples a fresh uniform bit in
   both `init` and `handle`) gives output probability `1 / 2`, while closing it with
   `oneCoinResource` (which always returns `true`) gives output probability `1`. Their
   `UC.advantage` is `1 / 2`, proved via `HybridFunctionality.advantage_close` and a direct
   `SSP.advantage` computation. Additional checks verify that querying party `0` twice advances the
   stored call counter to `2` (observable through the backdoor), that
   `HybridFunctionality.close_polyBounded` yields polynomial budgets for both `oneCoinResource`
   (`p = 1`, `q = 0`) and `fairCoinResource` (`p = 1`, `q = 1`), and that
   `HybridFunctionality.isQueryBounded_closeReduction` bounds the reduction program.
2. **Round trip on `UC.fcom`:** converting the 2-party commitment ideal functionality `UC.fcom` from
   `CslibFrontier.Crypto.Protocols.UC.Commitment` via `IdealFunctionality.toHybrid` and
   `HybridFunctionality.toMachine` recovers `fcom.toProtocol` definitionally, and a full 2-party
   commit-and-open execution yields identical output distributions under both.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCHybridFunctionality

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.UC Cslib.Probability
open scoped NNReal

/-! ### Witness 1: Coin relay and resource swap -/

/-- State of the 2-party coin-relay hybrid functionality: the most recent bit returned by the
private resource and the cumulative number of resource calls. -/
private structure CoinRelayState where
  /-- Most recent bit received from the private coin resource. -/
  lastBit : Option Bool
  /-- Total number of resource calls made so far. -/
  calls : ℕ

/-- A 2-party hybrid functionality with a private outgoing coin port `netSpec Unit Bool`: party `0`
queries the resource once, stores the bit and increments `calls`, and returns `some b`; party `1`
returns `none`; the backdoor returns the current call count. -/
private def coinRelay : HybridFunctionality 2 Unit Bool Unit ℕ (netSpec Unit Bool) where
  State := CoinRelayState
  init _ _ := pure { lastBit := none, calls := 0 }
  onInput i _ :=
    if i = 0 then do
      let b ← StateT.lift (ProbOracleComp.query (spec := netSpec Unit Bool) ())
      modify fun s => { lastBit := some b, calls := s.calls + 1 }
      return some b
    else
      return none
  onBackdoor _ := do
    let s ← get
    return s.calls

/-- Closed resource answering every query with a fresh uniform coin (and sampling an initial coin).
-/
private noncomputable def fairCoinResource :
    ℕ → Finset (Fin 2) → Machine OracleSpec.empty (netSpec Unit Bool) :=
  fun _ _ => {
    State := Bool
    init := $ᵗ Bool
    handle _ := StateT.lift (ProbOracleComp.sample ($ᵗ Bool)) }

/-- Closed resource that always answers `true`, making no random draws. -/
private def oneCoinResource :
    ℕ → Finset (Fin 2) → Machine OracleSpec.empty (netSpec Unit Bool) :=
  fun _ _ => {
    State := Unit
    init := pure ()
    handle _ := pure true }

/-- Corrupted party set `C = {1}`: party `0` is honest and party `1` is corrupted. -/
private abbrev corruptOne : Finset (Fin 2) := {1}

/-- Dummy adversary for `coinRelay`'s routed network port. -/
private abbrev relayDummyAdv :
    ExecAdversary 2 Unit Bool Unit ℕ (RoutedNetQ 2 Unit Unit) (RoutedNetR Bool ℕ) :=
  dummyAdversary 2 (RoutedNetQ 2 Unit Unit) (RoutedNetR Bool ℕ)

/-- Environment that sends one input to honest party `0` and outputs the returned bit. -/
private def queryPartyZero :
    Environment 2 Unit Bool (RoutedNetQ 2 Unit Unit) (RoutedNetR Bool ℕ) :=
  fun _ _ => do
    let r ← ProbOracleComp.query
      (spec := execSpec 2 Unit Bool (RoutedNetQ 2 Unit Unit) (RoutedNetR Bool ℕ))
      (Sum.inl (0, ()))
    return r.getD false

/-- Environment that queries honest party `0` twice and then queries the backdoor through the dummy
adversary to check that the call counter has grown to `2`. -/
private def queryTwiceAndCheckCount :
    Environment 2 Unit Bool (RoutedNetQ 2 Unit Unit) (RoutedNetR Bool ℕ) :=
  fun _ _ => do
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 Unit Bool (RoutedNetQ 2 Unit Unit) (RoutedNetR Bool ℕ))
      (Sum.inl (0, ()))
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 Unit Bool (RoutedNetQ 2 Unit Unit) (RoutedNetR Bool ℕ))
      (Sum.inl (0, ()))
    let c ← ProbOracleComp.query
      (spec := execSpec 2 Unit Bool (RoutedNetQ 2 Unit Unit) (RoutedNetR Bool ℕ))
      (Sum.inr (Sum.inr ()))
    return decide (c = Sum.inr 2)

/-- Environment that queries corrupted party `1` directly (blocked by `corruptRouter`) and checks
that it receives `none`. -/
private def queryCorruptedPartyOne :
    Environment 2 Unit Bool (RoutedNetQ 2 Unit Unit) (RoutedNetR Bool ℕ) :=
  fun _ _ => do
    let r ← ProbOracleComp.query
      (spec := execSpec 2 Unit Bool (RoutedNetQ 2 Unit Unit) (RoutedNetR Bool ℕ))
      (Sum.inl (1, ()))
    return r.isNone

/-- The resource-swap reduction program for `coinRelay`, `relayDummyAdv`, `C = {1}`, and
`queryPartyZero`. -/
private abbrev coinRelayReduction (κ : ℕ) (z : List Bool) :
    ProbOracleComp (netSpec Unit Bool) Bool :=
  (routeCorrupt corruptOne (coinRelay.toMachine κ corruptOne)).link
    (absorbAdversary corruptOne relayDummyAdv queryPartyZero κ z)

private theorem zero_notMem_corruptOne : (0 : Fin 2) ∉ corruptOne := by decide

private theorem one_mem_corruptOne : (1 : Fin 2) ∈ corruptOne := by decide

private theorem coinRelayReduction_eq_query (κ : ℕ) (z : List Bool) :
    coinRelayReduction κ z = ProbOracleComp.query (spec := netSpec Unit Bool) () := by
  simp only [coinRelayReduction, absorbAdversary, relayDummyAdv, dummyAdversary, liftAdversary,
    Machine.liftRight_id, Machine.link_id]
  simp only [Machine.link, queryPartyZero, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.runFrom_pure, routeCorrupt, zero_notMem_corruptOne, ↓reduceIte]
  simp only [coinRelay, HybridFunctionality.toMachine, ↓reduceIte, ProbOracleComp.sample_pure,
    StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_modify, pure_bind, bind_pure_comp,
    map_pure, Functor.map_map, Option.getD_some, id_map']

private theorem eval_run_fairCoinResource (κ : ℕ) (z : List Bool) :
    ((fairCoinResource κ corruptOne).run (coinRelayReduction κ z)).eval =
      PMF.uniformOfFintype Bool := by
  rw [coinRelayReduction_eq_query]
  simp only [Machine.run, Machine.link, fairCoinResource, Machine.runFrom_query, StateT.lift,
    StateT.run, Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_map,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform, bind_pure_comp, Functor.map_map,
    PMF.bind_const]
  exact PMF.map_id _

private theorem eval_run_oneCoinResource (κ : ℕ) (z : List Bool) :
    ((oneCoinResource κ corruptOne).run (coinRelayReduction κ z)).eval = PMF.pure true := by
  rw [coinRelayReduction_eq_query]
  simp only [Machine.run, Machine.link, oneCoinResource, Machine.runFrom_query, StateT.run_pure,
    Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_map,
    Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.pure_bind, PMF.pure_map]

/-- With `fairCoinResource`, the coin-relay execution outputs a uniform bit. -/
theorem eval_exec_coinRelay_fair (κ : ℕ) (z : List Bool) :
    (exec (coinRelay.close fairCoinResource) relayDummyAdv corruptOne queryPartyZero κ z).eval =
      PMF.uniformOfFintype Bool := by
  rw [HybridFunctionality.exec_close]
  exact eval_run_fairCoinResource κ z

/-- With `fairCoinResource`, the probability of outputting `true` is `1 / 2`. -/
theorem prob_exec_coinRelay_fair (κ : ℕ) (z : List Bool) :
    Pr[exec (coinRelay.close fairCoinResource) relayDummyAdv corruptOne queryPartyZero κ z] =
      1 / 2 := by
  rw [eval_exec_coinRelay_fair]
  simp [PMF.uniformOfFintype_apply]

/-- With `oneCoinResource`, the coin-relay execution outputs `true` with probability `1`. -/
theorem eval_exec_coinRelay_one (κ : ℕ) (z : List Bool) :
    (exec (coinRelay.close oneCoinResource) relayDummyAdv corruptOne queryPartyZero κ z).eval =
      PMF.pure true := by
  rw [HybridFunctionality.exec_close]
  exact eval_run_oneCoinResource κ z

/-- With `oneCoinResource`, the probability of outputting `true` is `1`. -/
theorem prob_exec_coinRelay_one (κ : ℕ) (z : List Bool) :
    Pr[exec (coinRelay.close oneCoinResource) relayDummyAdv corruptOne queryPartyZero κ z] = 1 := by
  rw [eval_exec_coinRelay_one]
  simp [PMF.pure_apply]

/-- Swapping `fairCoinResource` for `oneCoinResource` gives distinguishing advantage `1 / 2`,
proved via `HybridFunctionality.advantage_close` and a direct `SSP.advantage` computation. -/
theorem advantage_coinRelay_fair_one (κ : ℕ) (z : List Bool) :
    UC.advantage (coinRelay.close fairCoinResource) (coinRelay.close oneCoinResource)
      relayDummyAdv relayDummyAdv corruptOne queryPartyZero κ z = 1 / 2 := by
  rw [HybridFunctionality.advantage_close]
  simp only [SSP.advantage, Experiment.advantage, eval_run_fairCoinResource,
    eval_run_oneCoinResource, Game.advantage_pure_true]
  ext
  simp only [Game.coe_failProbability, PMF.uniformOfFintype_apply, Fintype.card_bool,
    Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

/-- Calling honest party `0` twice increments `coinRelay`'s internal call counter to `2`, which is
observable on the backdoor port. -/
theorem eval_exec_coinRelay_grows_state (κ : ℕ) (z : List Bool) :
    (exec (coinRelay.close fairCoinResource) relayDummyAdv corruptOne
      queryTwiceAndCheckCount κ z).eval = PMF.pure true := by
  rw [HybridFunctionality.exec_close]
  simp only [absorbAdversary, relayDummyAdv, dummyAdversary, liftAdversary, Machine.liftRight_id,
    Machine.link_id]
  simp only [Machine.link, queryTwiceAndCheckCount, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.runFrom_pure, routeCorrupt, zero_notMem_corruptOne, ↓reduceIte, StateT.run_map]
  simp only [coinRelay, HybridFunctionality.toMachine, ↓reduceIte, ProbOracleComp.sample_pure,
    StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_modify, StateT.run_get, pure_bind,
    bind_pure_comp, map_pure, map_bind, bind_map_left, Functor.map_map, decide_true]
  simp only [Machine.run, Machine.link, fairCoinResource, Machine.runFrom_bind,
    Machine.runFrom_map, Machine.runFrom_query, StateT.lift, StateT.run, bind_pure_comp,
    Functor.map_map, Machine.closeProgram_bind, Machine.closeProgram_sample,
    Machine.closeProgram_map, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform,
    PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.map_fst, PMF.bind_const]
  exact PMF.map_const _ _

/-- Querying corrupted party `1` directly through the party port is blocked by `corruptRouter`. -/
theorem eval_exec_coinRelay_corrupt_blocked (κ : ℕ) (z : List Bool) :
    (exec (coinRelay.close fairCoinResource) relayDummyAdv corruptOne
      queryCorruptedPartyOne κ z).eval = PMF.pure true := by
  rw [HybridFunctionality.exec_close]
  simp only [absorbAdversary, relayDummyAdv, dummyAdversary, liftAdversary, Machine.liftRight_id,
    Machine.link_id]
  simp only [Machine.link, queryCorruptedPartyOne, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.runFrom_pure, routeCorrupt, one_mem_corruptOne, ↓reduceIte, StateT.run_pure]
  simp only [coinRelay, HybridFunctionality.toMachine, ProbOracleComp.sample_pure, pure_bind,
    Option.isNone_none, map_pure]
  simp only [Machine.run, Machine.link, fairCoinResource, Machine.runFrom_pure, map_pure,
    Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_pure,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_const]

/-- `coinRelay` makes at most `1` resource call per activation. -/
theorem coinRelay_isBounded (κ : ℕ) (C : Finset (Fin 2)) :
    (coinRelay.toMachine κ C).IsBounded ((1 : Polynomial ℕ).eval κ) := by
  rw [Polynomial.eval_one]
  refine ⟨OracleComp.IsCostBounded.pure _ _, fun q s => ?_⟩
  rcases q with ⟨i, _⟩ | _
  · by_cases hi : i = 0
    · subst hi
      simp only [HybridFunctionality.toMachine, coinRelay, ↓reduceIte, bind_pure_comp]
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    · simp only [HybridFunctionality.toMachine, coinRelay, hi, ↓reduceIte]
      exact OracleComp.IsCostBounded.pure _ _
  · exact OracleComp.IsCostBounded.pure _ _

/-- `oneCoinResource` makes `0` calls per activation. -/
theorem oneCoinResource_isBounded (κ : ℕ) (C : Finset (Fin 2)) :
    (oneCoinResource κ C).IsBounded ((0 : Polynomial ℕ).eval κ) := by
  rw [Polynomial.eval_zero]
  exact ⟨OracleComp.IsCostBounded.pure _ _, fun _ _ => OracleComp.IsCostBounded.pure _ _⟩

/-- `fairCoinResource` makes `1` private coin draw at initialization and per activation. -/
theorem fairCoinResource_isBounded (κ : ℕ) (C : Finset (Fin 2)) :
    (fairCoinResource κ C).IsBounded ((1 : Polynomial ℕ).eval κ) := by
  rw [Polynomial.eval_one]
  have hunif : ($ᵗ Bool : ProbComp Bool).IsQueryBounded 1 := by
    rw [ProbComp.uniform, ProbComp.unifFin, PFunctor.FreeM.map_eq_map]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (OracleComp.IsCostBounded.query (spec := unifSpec) (Fintype.card Bool - 1))
  refine ⟨hunif, fun _ s => ?_⟩
  dsimp only [fairCoinResource] at s ⊢
  rw [StateT.run_lift, bind_pure_comp]
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (Machine.isQueryBounded_sample hunif)

/-- `queryPartyZero` makes `1` call in total. -/
theorem queryPartyZero_polyBounded : queryPartyZero.PolyBounded 1 := fun κ z => by
  rw [Polynomial.eval_one]
  simp only [queryPartyZero, bind_pure_comp]
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- Budget closure (`close_polyBounded`) with `p = 1` and `q = 0` on `oneCoinResource`, and with
`p = 1` and `q = 1` on `fairCoinResource`, plus the budget of the resource-swap reduction. -/
example (κ : ℕ) (z : List Bool) :
    (coinRelay.close oneCoinResource).PolyBounded (1 * (0 + 1) + 0) ∧
      (coinRelay.close fairCoinResource).PolyBounded (1 * (1 + 1) + 1) ∧
      OracleComp.IsQueryBounded (coinRelayReduction κ z)
        ((1 : Polynomial ℕ).eval κ + (absorbPoly 1 1).eval κ * ((1 : Polynomial ℕ).eval κ + 1)) :=
  ⟨HybridFunctionality.close_polyBounded coinRelay_isBounded oneCoinResource_isBounded,
    HybridFunctionality.close_polyBounded coinRelay_isBounded fairCoinResource_isBounded,
    by
      simpa only [coinRelayReduction, relayDummyAdv] using
        HybridFunctionality.isQueryBounded_closeReduction coinRelay_isBounded
          (dummyAdversary_polyBounded 2 _ _) queryPartyZero_polyBounded corruptOne κ z⟩

/-! ### Witness 2: Round trip on the 2-party commitment functionality `UC.fcom` -/

/-- Converting `UC.fcom` to a hybrid functionality and back to a machine recovers `fcom.toProtocol`
definitionally. -/
theorem fcom_toHybrid_toMachine (κ : ℕ) (C : Finset (Fin 2)) :
    fcom.toHybrid.toMachine κ C = fcom.toProtocol κ C := by
  simp

/-- Executing `fcom.toHybrid.toMachine` agrees with executing `fcom.toProtocol` for every
adversary, corruption set, and environment. -/
theorem exec_fcom_toHybrid_eq {AdvQ AdvR : Type}
    (A : ExecAdversary 2 CommitmentInput CommitmentOutput CommitmentBackdoor
      (Option CommitmentOutput) AdvQ AdvR)
    (C : Finset (Fin 2)) (Z : Environment 2 CommitmentInput CommitmentOutput AdvQ AdvR)
    (κ : ℕ) (z : List Bool) :
    (exec (fun κ C => fcom.toHybrid.toMachine κ C) A C Z κ z).eval =
      (exec fcom.toProtocol A C Z κ z).eval := by
  simp

/-- Dummy adversary for `fcom`'s routed network port. -/
abbrev fcomDummyAdv :
    ExecAdversary 2 CommitmentInput CommitmentOutput CommitmentBackdoor (Option CommitmentOutput)
      (RoutedNetQ 2 CommitmentInput CommitmentBackdoor)
      (RoutedNetR CommitmentOutput (Option CommitmentOutput)) :=
  dummyAdversary 2 _ _

/-- A 2-party environment for `fcom`: committer `0` commits to `b`, the dummy adversary delivers
the commitment receipt, committer `0` opens, the dummy adversary delivers the opening, and receiver
`1` polls and checks that it received `some (.opened b)`. -/
def commitAndOpenEnv (b : Bool) :
    Environment 2 CommitmentInput CommitmentOutput
      (RoutedNetQ 2 CommitmentInput CommitmentBackdoor)
      (RoutedNetR CommitmentOutput (Option CommitmentOutput)) :=
  fun _ _ => do
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput
        (RoutedNetQ 2 CommitmentInput CommitmentBackdoor)
        (RoutedNetR CommitmentOutput (Option CommitmentOutput)))
      (Sum.inl (0, .commit b))
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput
        (RoutedNetQ 2 CommitmentInput CommitmentBackdoor)
        (RoutedNetR CommitmentOutput (Option CommitmentOutput)))
      (Sum.inr (Sum.inr .deliverCommit))
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput
        (RoutedNetQ 2 CommitmentInput CommitmentBackdoor)
        (RoutedNetR CommitmentOutput (Option CommitmentOutput)))
      (Sum.inl (0, .openCom))
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput
        (RoutedNetQ 2 CommitmentInput CommitmentBackdoor)
        (RoutedNetR CommitmentOutput (Option CommitmentOutput)))
      (Sum.inr (Sum.inr .deliverOpen))
    let out ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput
        (RoutedNetQ 2 CommitmentInput CommitmentBackdoor)
        (RoutedNetR CommitmentOutput (Option CommitmentOutput)))
      (Sum.inl (1, .query))
    return decide (out = some (.opened b))

/-- Under both `fcom.toProtocol` and `fcom.toHybrid.toMachine`, the honest commit-and-open
environment sees the committed bit `b` with probability `1`. -/
theorem eval_exec_fcom_toHybrid_commitAndOpen (b : Bool) (κ : ℕ) (z : List Bool) :
    (exec (fun κ C => fcom.toHybrid.toMachine κ C) fcomDummyAdv ∅ (commitAndOpenEnv b) κ z).eval =
      PMF.pure true ∧
    (exec fcom.toProtocol fcomDummyAdv ∅ (commitAndOpenEnv b) κ z).eval = PMF.pure true := by
  have h : (exec fcom.toProtocol fcomDummyAdv ∅ (commitAndOpenEnv b) κ z).eval =
      PMF.pure true := by
    simp only [exec_dummyAdversary, Machine.run, Machine.link, commitAndOpenEnv,
      Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure, corruptRouter,
      Finset.notMem_empty, ↓reduceIte, StateT.run_map]
    simp only [fcom, IdealFunctionality.toProtocol, CommitmentState.committed, Fin.zero_ne_one.symm,
      ↓reduceIte, StateT.run, ProbOracleComp.sample_pure, pure_bind, bind_pure_comp, Bool.and_self,
      decide_true, map_pure, Machine.closeProgram_pure, ProbComp.eval_pure]
  exact ⟨by simpa only [IdealFunctionality.toHybrid_toMachine] using h, h⟩

end CslibFrontierTests.Crypto.UCHybridFunctionality
