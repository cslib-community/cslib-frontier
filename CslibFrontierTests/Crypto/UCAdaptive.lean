/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.UC.AdaptiveDummyAdversary
import CslibFrontier.Crypto.Negligible.Basic

/-!
# Tests for adaptive corruptions in the UC execution

This test suite exercises `CslibFrontier.Crypto.Protocols.UC.Adaptive` and
`CslibFrontier.Crypto.Protocols.UC.AdaptiveDummyAdversary` on a concrete two-party coin-flipping
protocol `P_coin` and ideal functionality `F_coin`:

* Router unit tests on explicit states checking `.static` ignoring `.corrupt 1` with `C₀ = {0}`,
  `.adaptive` corrupting party `1` mid-run, `.nonErasing` vs `.erasing` history traces after
  `go; erase`, and `.status` returning `{0}`.
* Satisfiability witnesses `corruptAdv` (with explicit `.corrupt` queries and `initial _ = {1}`)
  and `Z_star` with explicit `PolyBounded` proofs.
* Exact mode/memory separation (`Z_star`): `Pr[adaptiveExec .adaptive (P_coin .nonErasing) dummy
  Z_star = true] = 1` and `Pr[adaptiveExec .adaptive (P_coin .erasing) dummy Z_star = true] = 0`.
* Static embedding check on `n = 2` with `C = {1}`, applying `adaptiveExec_static_ofStatic` and
  checking the concrete output probability `1 / 2`.
* Information-theoretic erasing vs non-erasing separation witness: `P_coin .erasing` emulates
  `F_coin.toAdaptive coinReveal` with error `0`, whereas `P_coin .nonErasing` cannot be emulated
  by `F_coin.toAdaptive coinReveal` with any concrete error below `1 / 2`.
-/

namespace CslibFrontierTests.Crypto.UCAdaptive

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open OracleComp (sumHandler)
open scoped NNReal

/-! ### Concrete two-party coin protocol and functionality -/

/-- Party inputs for the two-party coin protocol. -/
inductive CoinIn : Type
  | go
  | erase
  | poll
  deriving DecidableEq

/-- State of the two-party coin protocol and functionality. -/
structure CoinState where
  party0 : Option Bool
  delivered1 : Option Bool
  deriving DecidableEq

/-- Concrete two-party coin-flipping protocol with configurable memory (`erasing` vs `nonErasing`).
Party `0` samples a uniform bit on `.go` and erases its local view on `.erase`; party `1` reads the
delivered bit on `.poll`. -/
def P_coin (mem : PartyMemory) : AdaptiveProtocol 2 CoinIn Bool Unit Unit (Option Bool) where
  machine _ := {
    State := CoinState
    init := pure { party0 := none, delivered1 := none }
    handle
      | .inl (i, .go) => fun s =>
          if i.val = 0 then
            if s.party0.isNone && s.delivered1.isNone then do
              let c ← ProbOracleComp.sample (ProbComp.unifFin 1)
              let b := decide (c = 0)
              pure (none, { party0 := some b, delivered1 := some b })
            else
              pure (none, s)
          else
            pure (none, s)
      | .inl (i, .erase) => fun s =>
          if i.val = 0 then
            pure (none, { s with party0 := none })
          else
            pure (none, s)
      | .inl (i, .poll) => fun s =>
          if i.val = 1 then
            pure (s.delivered1, s)
          else
            pure (none, s)
      | .inr () => fun s => pure ((), s) }
  view _ i s := if i.val = 0 then s.party0 else s.delivered1
  onCorrupt _ _ s := s
  memory := mem

/-- Ideal coin-flipping functionality matching `P_coin`. -/
@[reducible] def F_coin : IdealFunctionality 2 CoinIn Bool Unit Unit where
  State := CoinState
  init _ _ := pure { party0 := none, delivered1 := none }
  onInput
    | i, .go => fun s =>
        if i.val = 0 then
          if s.party0.isNone && s.delivered1.isNone then do
            let c ← ProbComp.unifFin 1
            let b := decide (c = 0)
            pure (none, { party0 := some b, delivered1 := some b })
          else
            pure (none, s)
        else
          pure (none, s)
    | i, .erase => fun s =>
        if i.val = 0 then
          pure (none, { s with party0 := none })
        else
          pure (none, s)
    | i, .poll => fun s =>
        if i.val = 1 then
          pure (s.delivered1, s)
        else
          pure (none, s)
  onBackdoor _ s := pure ((), s)

/-- Standard `f`-revealing leakage map for `F_coin`: party `0` exposes `party0` until `.erase`, and
party `1` exposes its delivered output `delivered1`. -/
def coinReveal (_ : ℕ) (s : F_coin.State) (i : Fin 2) : Option Bool :=
  if i.val = 0 then s.party0 else s.delivered1

/-! ### Router unit tests on explicit states -/

private def coinInitRS (C₀ : Finset (Fin 2)) :
    AdaptiveRouterState CoinState (Option Bool) 2 :=
  { inner := { party0 := none, delivered1 := none }
    corrupted := C₀
    trace := fun _ => [none] }

private theorem router_static_ignores_corrupt_one :
    ((adaptiveRouter .static (P_coin .erasing) 0 {0}).handle (.inr (.corrupt 1))).run
        (coinInitRS {0}) =
      pure (.corrupt none, coinInitRS {0}) := by
  rfl

private theorem router_static_reports_corrupt_zero :
    ((adaptiveRouter .static (P_coin .erasing) 0 {0}).handle (.inr (.corrupt 0))).run
        (coinInitRS {0}) =
      pure (.corrupt (some { current := none, history := none }), coinInitRS {0}) := by
  rfl

private theorem router_adaptive_corrupts_one_mid_run (b : Bool) :
    let sMid : AdaptiveRouterState CoinState (Option Bool) 2 :=
      { inner := { party0 := some b, delivered1 := some b }
        corrupted := ∅
        trace := fun i => match i with
          | ⟨0, _⟩ => [none, some b]
          | ⟨1, _⟩ => [none, some b] }
    ((adaptiveRouter .adaptive (P_coin .erasing) 0 ∅).handle (.inr (.corrupt 1))).run sMid =
      pure (.corrupt (some { current := some b, history := none }),
        { sMid with corrupted := {1} }) := by
  intro sMid
  simp [adaptiveRouter, P_coin, AdaptiveProtocol.corruptionReport, StateT.run, sMid]

private theorem router_nonErasing_vs_erasing_trace (b : Bool) :
    let sGo : AdaptiveRouterState CoinState (Option Bool) 2 :=
      (P_coin .nonErasing).recordSnapshot 0 { party0 := some b, delivered1 := some b }
        ∅ (fun _ => [none])
    let sEraseNon : AdaptiveRouterState CoinState (Option Bool) 2 :=
      (P_coin .nonErasing).recordSnapshot 0 { party0 := none, delivered1 := some b }
        ∅ sGo.trace
    let sEraseEr : AdaptiveRouterState CoinState (Option Bool) 2 :=
      (P_coin .erasing).recordSnapshot 0 { party0 := none, delivered1 := some b }
        ∅ sGo.trace
    (P_coin .nonErasing).corruptionReport 0 0 sEraseNon =
        { current := none, history := some [none, some b, none] } ∧
      (P_coin .erasing).corruptionReport 0 0 sEraseEr =
        { current := none, history := none } := by
  intro sGo sEraseNon sEraseEr
  simp [AdaptiveProtocol.corruptionReport, AdaptiveProtocol.recordSnapshot, P_coin, sEraseNon,
    sEraseEr, sGo]

private theorem router_status_returns_corrupted :
    ((adaptiveRouter .adaptive (P_coin .erasing) 0 ∅).handle (.inl .status)).run
        (coinInitRS {0}) =
      pure (({0} : Finset (Fin 2)), coinInitRS {0}) := by
  simp [adaptiveRouter, StateT.run]
  rfl

/-! ### Satisfiability witnesses and distinguishing environment `Z_star` -/

/-- A concrete adaptive adversary that initially corrupts party `1` and forwards `.corrupt` queries
to `adaptiveRouter`. -/
def corruptAdv :
    AdaptiveAdversary 2 CoinIn Bool Unit Unit (Option Bool)
      (Fin 2) (AdaptiveNetR Bool Unit (Option Bool)) where
  initial _ := {1}
  machine _ := {
    State := Unit
    init := pure ()
    handle i _ := do
      let r ← ProbOracleComp.query
        (spec := netSpec (AdaptiveNetQ 2 CoinIn Unit) (AdaptiveNetR Bool Unit (Option Bool)))
        (.corrupt i)
      pure (r, ()) }

theorem corruptAdv_polyBounded : corruptAdv.PolyBounded 1 := fun κ => by
  refine ⟨?_, fun i _ => ?_⟩
  · change (pure () : ProbComp Unit).IsQueryBounded (Polynomial.eval κ 1)
    simp only [Polynomial.eval_one]
    exact OracleComp.IsCostBounded.pure _ 1
  · simp only [Polynomial.eval_one, corruptAdv, StateT.run]
    exact OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
      OracleComp.IsCostBounded.pure _ 0

/-- Distinguishing environment `Z_star` for the adaptive dummy adversary: activates `(0, .go)`,
`(0, .erase)`, polls `(1, .poll)` for `b`, asks the dummy adversary to `.corrupt 0`, queries
`.status`, and outputs `true` iff `C = {0}` and `r.history = some [none, some b, none, none]`. -/
def Z_star :
    AdaptiveEnvironment 2 CoinIn Bool
      (AdaptiveNetQ 2 CoinIn Unit) (AdaptiveNetR Bool Unit (Option Bool)) := fun _ _ => do
  let _ ← ProbOracleComp.query
    (spec := adaptiveExecSpec 2 CoinIn Bool (AdaptiveNetQ 2 CoinIn Unit)
      (AdaptiveNetR Bool Unit (Option Bool)))
    (.inl (.party 0 .go))
  let _ ← ProbOracleComp.query
    (spec := adaptiveExecSpec 2 CoinIn Bool (AdaptiveNetQ 2 CoinIn Unit)
      (AdaptiveNetR Bool Unit (Option Bool)))
    (.inl (.party 0 .erase))
  let optB ← ProbOracleComp.query
    (spec := adaptiveExecSpec 2 CoinIn Bool (AdaptiveNetQ 2 CoinIn Unit)
      (AdaptiveNetR Bool Unit (Option Bool)))
    (.inl (.party 1 .poll))
  let rep ← ProbOracleComp.query
    (spec := adaptiveExecSpec 2 CoinIn Bool (AdaptiveNetQ 2 CoinIn Unit)
      (AdaptiveNetR Bool Unit (Option Bool)))
    (.inr (.corrupt 0))
  let C : Finset (Fin 2) ← ProbOracleComp.query
    (spec := adaptiveExecSpec 2 CoinIn Bool (AdaptiveNetQ 2 CoinIn Unit)
      (AdaptiveNetR Bool Unit (Option Bool)))
    (.inl .status)
  pure (match optB, rep with
    | some b, .corrupt (some r) => decide (C = {0} ∧ r.history = some [none, some b, none, none])
    | _, _ => false)

theorem Z_star_polyBounded : Z_star.PolyBounded 5 := fun κ z => by
  simp only [Polynomial.eval_ofNat]
  change (Z_star κ z).IsQueryBounded 5
  unfold Z_star
  refine (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
    OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
    OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
    OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
    OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
    OracleComp.IsCostBounded.pure _ 0).mono ?_
  omega

/-! ### Exact mode and memory probabilities for `Z_star` -/

private theorem P_coin_applyInitialCorruptions (m : PartyMemory) (κ : ℕ)
    (C₀ : Finset (Fin 2)) (s : CoinState) :
    (P_coin m).applyInitialCorruptions κ C₀ s = s := by
  simp only [AdaptiveProtocol.applyInitialCorruptions, P_coin, ite_self]
  rfl

private theorem Z_star_dummy_eval (m : PartyMemory) (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive (P_coin m)
        (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
        Z_star κ z).eval =
      PMF.pure (decide (m = .nonErasing)) := by
  have hfold : ∀ s : CoinState,
      List.foldl (fun acc (_ : Fin 2) => acc) s (List.finRange 2) = s := fun _ => rfl
  rw [adaptiveExec_dummyAdversary]
  dsimp only [Machine.run, Machine.link]
  let M := adaptiveRouter .adaptive (P_coin m) κ ∅
  have hinit : M.init = pure
      { inner := { party0 := none, delivered1 := none }
        corrupted := ∅
        trace := fun _ => [none] } := by
    dsimp only [M, adaptiveRouter, AdaptiveProtocol.applyInitialCorruptions, P_coin]
    simp only [ite_self, hfold, pure_bind]
  have hstatus (rs' : AdaptiveRouterState CoinState (Option Bool) 2) :
      (M.handle (.inl .status)).run rs' = pure (rs'.corrupted, rs') := rfl
  have hrun : ∀ rs : AdaptiveRouterState CoinState (Option Bool) 2,
      M.runFrom (Z_star κ z) rs =
        (M.handle (.inl (.party 0 .go))).run rs >>= fun x0 =>
        (M.handle (.inl (.party 0 .erase))).run x0.2 >>= fun x1 =>
        (M.handle (.inl (.party 1 .poll))).run x1.2 >>= fun x2 =>
        (M.handle (.inr (.corrupt 0))).run x2.2 >>= fun x3 =>
        pure (match x2.1, x3.1 with
          | some b, .corrupt (some r) =>
              decide (x3.2.corrupted = {0} ∧ r.history = some [none, some b, none, none])
          | _, _ => false, x3.2) := by
    intro rs
    dsimp only [Z_star]
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M)]
    refine bind_congr fun x0 => ?_
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M)]
    refine bind_congr fun x1 => ?_
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M)]
    refine bind_congr fun x2 => ?_
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M)]
    refine bind_congr fun x3 => ?_
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hstatus, pure_bind,
      Machine.runFrom_pure (M := M)]
    rfl
  change (Machine.closeProgram (ProbOracleComp.sample M.init >>= fun s =>
    Prod.fst <$> M.runFrom (Z_star κ z) s)).eval = PMF.pure (decide (m = .nonErasing))
  erw [hinit, ProbOracleComp.sample_pure, pure_bind, hrun]
  simp only [M, adaptiveRouter, P_coin, StateT.run, bind_pure_comp,
    map_bind, Functor.map_map, map_pure, AdaptiveProtocol.recordSnapshot,
    AdaptiveProtocol.corruptionReport, Fin.isValue, Fin.val_zero, Fin.val_one,
    Finset.notMem_empty, ↓reduceIte, Option.isNone_none, Bool.and_self,
    Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_map,
    Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.map, PMF.pure_bind, Function.comp_apply, PMF.bind_bind,
    List.cons_append, List.nil_append]
  have hconst : (fun c : Fin 2 =>
      PMF.pure (decide (insert (0 : Fin 2) ∅ = ({0} : Finset (Fin 2)) ∧
        (if m = .nonErasing then some [none, some (decide (c = 0)), none, none] else none) =
          some [none, some (decide (c = 0)), none, none]))) =
      fun _ => PMF.pure (decide (m = .nonErasing)) := by
    funext c
    cases m <;> simp
  rw [hconst, PMF.bind_const]

theorem eval_Z_star_nonErasing (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive (P_coin .nonErasing)
        (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
        Z_star κ z).eval true = 1 := by
  rw [Z_star_dummy_eval, PMF.pure_apply]
  simp

theorem eval_Z_star_erasing (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive (P_coin .erasing)
        (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
        Z_star κ z).eval true = 0 := by
  rw [Z_star_dummy_eval, PMF.pure_apply]
  simp

/-! ### Static embedding check on `n = 2` with `C = {1}` -/

/-- A fixed static adversary for `n = 2` that polls corrupted party `1`. -/
def staticPollOneAdv : ExecAdversary 2 CoinIn Bool Unit Unit Unit (Option Bool) :=
  fun _ _ => {
    State := Unit
    init := pure ()
    handle _ _ := do
      let out ← ProbOracleComp.query
        (spec := netSpec (RoutedNetQ 2 CoinIn Unit) (RoutedNetR Bool Unit))
        (.inl (1, .poll))
      let res := match out with
        | .inl o => o
        | .inr () => none
      pure (res, ()) }

/-- Environment for the static embedding check: activates honest `(0, .go)`, asks the adversary to
poll `(1, .poll)`, and outputs `decide (res = some true)`. -/
def staticCheckEnv : Environment 2 CoinIn Bool Unit (Option Bool) := fun _ _ => do
  let _ ← ProbOracleComp.query (spec := execSpec 2 CoinIn Bool Unit (Option Bool)) (.inl (0, .go))
  let res ← ProbOracleComp.query (spec := execSpec 2 CoinIn Bool Unit (Option Bool)) (.inr ())
  pure (decide (res = some true))

theorem static_embedding_check (κ : ℕ) (z : List Bool) :
    adaptiveExec .static (P_coin .erasing)
        (AdaptiveAdversary.ofStatic staticPollOneAdv (fun _ => {1}))
        staticCheckEnv.toAdaptive κ z =
      exec (P_coin .erasing).toStatic staticPollOneAdv {1} staticCheckEnv κ z ∧
      (adaptiveExec .static (P_coin .erasing)
          (AdaptiveAdversary.ofStatic staticPollOneAdv (fun _ => {1}))
          staticCheckEnv.toAdaptive κ z).eval true = 1 / 2 := by
  refine ⟨adaptiveExec_static_ofStatic (P_coin .erasing) staticPollOneAdv
    (fun _ => {1}) staticCheckEnv κ z, ?_⟩
  rw [adaptiveExec_static_ofStatic]
  have hnot : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) := by decide
  have hmem : (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by decide
  have hfold : ∀ s : CoinState,
      List.foldl (fun acc (_ : Fin 2) => acc) s (List.finRange 2) = s := fun _ => rfl
  let A := liftAdversary (n := 2) (In := CoinIn) (Out := Bool) (staticPollOneAdv κ {1})
  let M := corruptRouter {1} ((P_coin .erasing).toStatic κ {1})
  have hrunA : A.runFrom (staticCheckEnv κ z) () =
      ProbOracleComp.query
          (spec := partySpec 2 CoinIn Bool ⊕ₒ
            netSpec (RoutedNetQ 2 CoinIn Unit) (RoutedNetR Bool Unit))
          (.inl (0, .go)) >>= fun _ =>
      ProbOracleComp.query
          (spec := partySpec 2 CoinIn Bool ⊕ₒ
            netSpec (RoutedNetQ 2 CoinIn Unit) (RoutedNetR Bool Unit))
          (.inr (.inl (1, CoinIn.poll))) >>= fun out =>
      pure (decide ((match out with | .inl o => o | .inr () => none) = some true), ()) := by
    dsimp only [staticCheckEnv]
    erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A), StateT.run_lift]
    dsimp only [A, liftAdversary, staticPollOneAdv]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun _ => ?_
    erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A)]
    dsimp only [A, liftAdversary, staticPollOneAdv, liftNet]
    have hln : OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (Sum.inl k))
          fun q => ProbOracleComp.query (Sum.inr q))
        (ProbOracleComp.query
          (spec := netSpec (RoutedNetQ 2 CoinIn Unit) (RoutedNetR Bool Unit))
          (Sum.inl (1, CoinIn.poll))) =
        ProbOracleComp.query
          (spec := partySpec 2 CoinIn Bool ⊕ₒ
            netSpec (RoutedNetQ 2 CoinIn Unit) (RoutedNetR Bool Unit))
          (Sum.inr (Sum.inl (1, CoinIn.poll))) := rfl
    simp only [StateT.run, OracleComp.interpret_bind, OracleComp.interpret_pure, hln,
      bind_assoc, pure_bind]
    refine bind_congr fun out => ?_
    erw [Machine.runFrom_pure (M := A)]
    rfl
  change (Machine.closeProgram (ProbOracleComp.sample (A.comp M).init >>= fun s =>
    Prod.fst <$> (A.comp M).runFrom (staticCheckEnv κ z) s)).eval true = 1 / 2
  have hinitM : M.init = pure ({ party0 := none, delivered1 := none } : CoinState) := by
    simp only [M, corruptRouter, AdaptiveProtocol.toStatic,
      AdaptiveProtocol.applyInitialCorruptions, P_coin, ite_self, hfold, map_pure]
  have hM0 : (M.handle (.inl (0, .go))).run ({ party0 := none, delivered1 := none } : CoinState) =
      (fun c : Fin 2 =>
        (none, { party0 := some (decide (c = 0)), delivered1 := some (decide (c = 0)) })) <$>
        ProbOracleComp.sample (ProbComp.unifFin 1) := by
    simp only [M, corruptRouter, AdaptiveProtocol.toStatic, P_coin, StateT.run, hnot,
      ↓reduceIte, Fin.val_zero, Option.isNone_none, Bool.and_self, bind_pure_comp]
  have hM1 (s : CoinState) : (M.handle (.inr (.inl (1, .poll)))).run s =
      pure (.inl s.delivered1, s) := by
    simp only [M, corruptRouter, AdaptiveProtocol.toStatic, P_coin, hmem, ↓reduceIte,
      StateT.run, Fin.val_one]
    rfl
  have htail (b' : Bool) :
      Prod.fst <$>
        (Equiv.prodAssoc Bool A.State M.State <$>
          M.runFrom
            (ProbOracleComp.query
                (spec := partySpec 2 CoinIn Bool ⊕ₒ
                  netSpec (RoutedNetQ 2 CoinIn Unit) (RoutedNetR Bool Unit))
                (.inr (.inl (1, CoinIn.poll))) >>= fun out =>
              pure (decide ((match out with | .inl o => o | .inr () => none) = some true), ()))
            ({ party0 := some b', delivered1 := some b' } : CoinState)) =
        pure (decide (b' = true)) := by
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hM1, pure_bind,
      Machine.runFrom_pure (M := M)]
    simp only [map_pure, Equiv.prodAssoc_apply, Option.some.injEq]
  rw [Machine.comp_init]
  have hinitA : A.init = pure () := rfl
  erw [hinitM, hinitA, ProbOracleComp.sample_bind, ProbOracleComp.sample_pure, bind_assoc,
    pure_bind, ProbOracleComp.sample_pure, pure_bind]
  erw [Machine.runFrom_comp (A := A) (P := M), hrunA]
  erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), map_bind, hM0,
    map_bind, bind_map_left]
  simp only [Machine.closeProgram_bind, Machine.closeProgram_sample,
    ProbComp.eval_bind, ProbComp.eval_unifFin]
  rw [PMF.bind_apply, tsum_fintype, Fin.sum_univ_two]
  erw [htail (decide ((0 : Fin 2) = 0)), htail (decide ((1 : Fin 2) = 0))]
  simp [Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_apply,
    Probability.PMF.uniformOfFintype, one_div]

/-! ### Erasing vs non-erasing separation -/

private theorem P_coin_erasing_eq_F_coin :
    P_coin .erasing = F_coin.toAdaptive coinReveal := by
  dsimp only [P_coin, F_coin, IdealFunctionality.toAdaptive]
  congr 1
  · funext κ
    congr 1
    ext q s
    rcases q with ⟨i, x⟩ | ⟨⟩
    · fin_cases i <;> cases x
      all_goals
        dsimp only [StateT.run]
        first
          | rfl
          | (simp only [↓reduceIte, Bool.and_eq_true, Option.isNone_iff_eq_none, bind_pure_comp]
             split_ifs <;> rfl)
    · rfl

/-- `P_coin .erasing` adaptively emulates `F_coin.toAdaptive coinReveal` with zero error. -/
theorem adaptiveEmulates_erasing_witness :
    AdaptiveEmulatesWithin .adaptive (P_coin .erasing) (F_coin.toAdaptive coinReveal)
      Polynomial.X (fun _ _ _ => 0) := by
  rw [P_coin_erasing_eq_F_coin]
  exact AdaptiveEmulatesWithin.refl .adaptive (F_coin.toAdaptive coinReveal)

private theorem tsum_pmf_bind_mul {α β : Type} (p : PMF α) (q : α → PMF β) (f : β → ENNReal) :
    ∑' y, (p.bind q) y * f y = ∑' a, p a * ∑' y, q a y * f y := by
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right, mul_assoc]
  rw [tsum_comm]
  exact tsum_congr fun a => ENNReal.tsum_mul_left

private theorem coin_router_corrupt_mono {α : Type} (κ : ℕ)
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ 2 CoinIn Unit)
      (AdaptiveNetR Bool Unit (Option Bool))) α)
    (rs : AdaptiveRouterState CoinState (Option Bool) 2)
    {x : α × AdaptiveRouterState CoinState (Option Bool) 2}
    (hx : x ∈ (closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
      (liftAdaptiveNet netProg) rs)).support) :
    rs.corrupted ⊆ x.2.corrupted := by
  induction netProg using OracleComp.induction generalizing rs with
  | pure a =>
    erw [liftAdaptiveNet_pure, Machine.runFrom_pure, closeEval_pure,
      PMF.mem_support_pure_iff] at hx
    rcases hx with rfl
    exact Finset.Subset.rfl
  | query_bind q cont ih =>
    rcases q with k | q
    · have hstep :
          closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
            (liftAdaptiveNet (OracleComp.query (Sum.inl k) >>= cont)) rs) =
          (ProbComp.unifFin k).eval.bind fun a =>
            closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
              (liftAdaptiveNet (cont a)) rs) := by
        have hk : liftAdaptiveNet (n := 2) (In := CoinIn) (Out := Bool)
            (OracleComp.query (spec := probOracleSpec
              (netSpec (AdaptiveNetQ 2 CoinIn Unit) (AdaptiveNetR Bool Unit (Option Bool))))
              (Sum.inl k)) =
            ProbOracleComp.sample (ProbComp.unifFin k) := by
          simp only [liftAdaptiveNet, OracleComp.interpret_query, sumHandler,
            ProbOracleComp.sample, ProbComp.unifFin]
        rw [liftAdaptiveNet_bind, hk]
        erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left, closeEval_bind,
          closeEval_sample]
      erw [hstep, PMF.mem_support_bind_iff] at hx
      rcases hx with ⟨a, _, hx'⟩
      exact ih a rs hx'
    · have hbind :
          closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
            (liftAdaptiveNet (OracleComp.query (Sum.inr q) >>= cont)) rs) =
          (closeEval (((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).handle
            (.inr q)).run rs)).bind fun y =>
            closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
              (liftAdaptiveNet (cont y.1)) y.2) := by
        erw [liftAdaptiveNet_bind, liftAdaptiveNet_query, Machine.runFrom_bind,
          Machine.runFrom_query, closeEval_bind]
      erw [hbind, PMF.mem_support_bind_iff] at hx
      rcases hx with ⟨y, hy, hx'⟩
      cases q with
      | party i u =>
        simp only [adaptiveRouter, StateT.run] at hy
        split_ifs at hy
        · erw [closeEval_bind, PMF.mem_support_bind_iff] at hy
          rcases hy with ⟨⟨out, s'⟩, _, hy'⟩
          erw [closeEval_pure, PMF.mem_support_pure_iff] at hy'
          rcases hy' with rfl
          dsimp only at hx'
          exact ih (.party out)
            ((F_coin.toAdaptive coinReveal).recordSnapshot κ s' rs.corrupted rs.trace) hx'
        · erw [closeEval_pure, PMF.mem_support_pure_iff] at hy
          rcases hy with rfl
          dsimp only at hx'
          exact ih (.party none) rs hx'
      | net u =>
        simp only [adaptiveRouter, StateT.run] at hy
        erw [closeEval_bind, PMF.mem_support_bind_iff] at hy
        rcases hy with ⟨⟨r, s'⟩, _, hy'⟩
        erw [closeEval_pure, PMF.mem_support_pure_iff] at hy'
        rcases hy' with rfl
        dsimp only at hx'
        exact ih (.net r)
          ((F_coin.toAdaptive coinReveal).recordSnapshot κ s' rs.corrupted rs.trace) hx'
      | corrupt i =>
        simp only [adaptiveRouter, StateT.run] at hy
        erw [closeEval_pure, PMF.mem_support_pure_iff] at hy
        rcases hy with rfl
        dsimp only at hx'
        have hsub : rs.corrupted ⊆
            (if i ∈ rs.corrupted then rs
             else { inner := rs.inner, corrupted := insert i rs.corrupted
                    trace := rs.trace }).corrupted := by
          split_ifs
          · exact Finset.Subset.rfl
          · exact Finset.subset_insert _ _
        exact hsub.trans (ih _ _ hx')

private theorem router_F_coin_no1_indep {α : Type} (κ : ℕ) (b : Bool)
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ 2 CoinIn Unit)
      (AdaptiveNetR Bool Unit (Option Bool))) α)
    (C : Finset (Fin 2)) (h1 : (1 : Fin 2) ∉ C)
    (tr₁ tr₂ : Fin 2 → List (Option Bool))
    (g : α × Finset (Fin 2) → ENNReal)
    (hg : ∀ a C', (1 : Fin 2) ∈ C' → g (a, C') = 0) :
    ∑' x, closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
        (liftAdaptiveNet netProg)
        { inner := { party0 := none, delivered1 := some b }
          corrupted := C, trace := tr₁ }) x *
        g (x.1, x.2.corrupted) =
      ∑' x, closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
        (liftAdaptiveNet netProg)
        { inner := { party0 := none, delivered1 := some false }
          corrupted := C, trace := tr₂ }) x *
        g (x.1, x.2.corrupted) := by
  induction netProg using OracleComp.induction generalizing C tr₁ tr₂ with
  | pure a =>
    erw [liftAdaptiveNet_pure, Machine.runFrom_pure, closeEval_pure]
    erw [Machine.runFrom_pure, closeEval_pure]
    let rs₁ : AdaptiveRouterState CoinState (Option Bool) 2 :=
      { inner := { party0 := none, delivered1 := some b }, corrupted := C, trace := tr₁ }
    let rs₂ : AdaptiveRouterState CoinState (Option Bool) 2 :=
      { inner := { party0 := none, delivered1 := some false }, corrupted := C, trace := tr₂ }
    have hL : (∑' x, PMF.pure (a, rs₁) x * g (x.1, x.2.corrupted)) = g (a, C) := by
      rw [tsum_eq_single (a, rs₁)
        (fun x hx => by simp only [PMF.pure_apply, hx, ↓reduceIte, zero_mul])]
      simp only [PMF.pure_apply, ↓reduceIte, one_mul]
      rfl
    have hR : (∑' x, PMF.pure (a, rs₂) x * g (x.1, x.2.corrupted)) = g (a, C) := by
      rw [tsum_eq_single (a, rs₂)
        (fun x hx => by simp only [PMF.pure_apply, hx, ↓reduceIte, zero_mul])]
      simp only [PMF.pure_apply, ↓reduceIte, one_mul]
      rfl
    exact hL.trans hR.symm
  | query_bind q cont ih =>
    rcases q with k | q
    · have hstep (b' : Bool) (tr : Fin 2 → List (Option Bool)) :
          closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
            (liftAdaptiveNet (OracleComp.query (Sum.inl k) >>= cont))
            { inner := { party0 := none, delivered1 := some b' }
              corrupted := C, trace := tr }) =
          (ProbComp.unifFin k).eval.bind fun a =>
            closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
              (liftAdaptiveNet (cont a))
              { inner := { party0 := none, delivered1 := some b' }
                corrupted := C, trace := tr }) := by
        have hk : liftAdaptiveNet (n := 2) (In := CoinIn) (Out := Bool)
            (OracleComp.query (spec := probOracleSpec
              (netSpec (AdaptiveNetQ 2 CoinIn Unit) (AdaptiveNetR Bool Unit (Option Bool))))
              (Sum.inl k)) =
            ProbOracleComp.sample (ProbComp.unifFin k) := by
          simp only [liftAdaptiveNet, OracleComp.interpret_query, sumHandler,
            ProbOracleComp.sample, ProbComp.unifFin]
        rw [liftAdaptiveNet_bind, hk]
        erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left, closeEval_bind,
          closeEval_sample]
      rw [hstep b tr₁, hstep false tr₂]
      simp only [tsum_pmf_bind_mul]
      exact tsum_congr fun a => congrArg ((ProbComp.unifFin k).eval a * ·) (ih a C h1 tr₁ tr₂)
    · have hbind (b' : Bool) (tr : Fin 2 → List (Option Bool)) :
          closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
            (liftAdaptiveNet (OracleComp.query (Sum.inr q) >>= cont))
            { inner := { party0 := none, delivered1 := some b' }
              corrupted := C, trace := tr }) =
          (closeEval (((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).handle
            (.inr q)).run { inner := { party0 := none, delivered1 := some b' }
                            corrupted := C, trace := tr })).bind fun y =>
            closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
              (liftAdaptiveNet (cont y.1)) y.2) := by
        erw [liftAdaptiveNet_bind, liftAdaptiveNet_query, Machine.runFrom_bind,
          Machine.runFrom_query, closeEval_bind]
      rw [hbind b tr₁, hbind false tr₂]
      cases q with
      | party i u =>
        have hi : i = 0 ∨ i = 1 :=
          match i with
          | ⟨0, _⟩ => Or.inl (Fin.ext rfl)
          | ⟨1, _⟩ => Or.inr (Fin.ext rfl)
        rcases hi with rfl | rfl
        · by_cases h0 : (0 : Fin 2) ∈ C
          · cases u <;>
              (simp only [adaptiveRouter, F_coin, IdealFunctionality.toAdaptive, StateT.run, h0,
                Fin.val_zero, Nat.zero_ne_one, ↓reduceIte, Option.isNone_none, Option.isNone_some,
                Bool.true_and, Bool.false_eq_true, ProbOracleComp.sample_pure, closeEval_bind,
                closeEval_pure, AdaptiveProtocol.recordSnapshot, PMF.pure_bind];
               exact ih _ C h1 _ _)
          · simp only [adaptiveRouter, StateT.run, h0, ↓reduceIte, closeEval_pure, PMF.pure_bind]
            exact ih _ C h1 tr₁ tr₂
        · simp only [adaptiveRouter, StateT.run, h1, ↓reduceIte, closeEval_pure, PMF.pure_bind]
          exact ih _ C h1 tr₁ tr₂
      | net u =>
        cases u
        simp only [adaptiveRouter, F_coin, IdealFunctionality.toAdaptive, StateT.run,
          ProbOracleComp.sample_pure, closeEval_bind, closeEval_pure,
          AdaptiveProtocol.recordSnapshot, PMF.pure_bind]
        exact ih _ C h1 _ _
      | corrupt i =>
        have hmem_ne : PartyMemory.erasing ≠ .nonErasing := by decide
        have hi : i = 0 ∨ i = 1 :=
          match i with
          | ⟨0, _⟩ => Or.inl (Fin.ext rfl)
          | ⟨1, _⟩ => Or.inr (Fin.ext rfl)
        rcases hi with rfl | rfl
        · dsimp only [adaptiveRouter, StateT.run]
          split_ifs with h0
          · simp only [F_coin, IdealFunctionality.toAdaptive, coinReveal,
              AdaptiveProtocol.corruptionReport, Fin.val_zero, hmem_ne, ↓reduceIte,
              closeEval_pure, PMF.pure_bind]
            exact ih _ C h1 tr₁ tr₂
          · simp only [F_coin, IdealFunctionality.toAdaptive, coinReveal,
              AdaptiveProtocol.corruptionReport, Fin.val_zero, hmem_ne, ↓reduceIte,
              closeEval_pure, PMF.pure_bind]
            have h1' : (1 : Fin 2) ∉ insert 0 C := by simpa [Finset.mem_insert] using h1
            exact ih _ (insert 0 C) h1' tr₁ tr₂
        · simp only [adaptiveRouter, F_coin, IdealFunctionality.toAdaptive, coinReveal,
            AdaptiveProtocol.corruptionReport, StateT.run, Fin.val_one, Nat.one_ne_zero, hmem_ne,
            ↓reduceIte, closeEval_pure, PMF.pure_bind, h1]
          have hzero (b' : Bool) (tr : Fin 2 → List (Option Bool)) :
              ∑' x, closeEval ((adaptiveRouter .adaptive
                  (F_coin.toAdaptive coinReveal) κ ∅).runFrom
                  (liftAdaptiveNet (cont (.corrupt (some { current := some b', history := none }))))
                  { inner := { party0 := none, delivered1 := some b' }
                    corrupted := insert 1 C, trace := tr }) x * g (x.1, x.2.corrupted) = 0 := by
            rw [tsum_eq_zero_iff]
            intro x
            by_cases hx : closeEval ((adaptiveRouter .adaptive
                (F_coin.toAdaptive coinReveal) κ ∅).runFrom
                (liftAdaptiveNet (cont (.corrupt (some { current := some b', history := none }))))
                { inner := { party0 := none, delivered1 := some b' }
                  corrupted := insert 1 C, trace := tr }) x = 0
            · exact mul_eq_zero_of_left hx _
            · have hxsup : x ∈ (closeEval ((adaptiveRouter .adaptive
                  (F_coin.toAdaptive coinReveal) κ ∅).runFrom
                  (liftAdaptiveNet (cont (.corrupt (some { current := some b', history := none }))))
                  { inner := { party0 := none, delivered1 := some b' }
                    corrupted := insert 1 C, trace := tr })).support := by
                erw [PMF.mem_support_iff]; exact hx
              have hsub := coin_router_corrupt_mono κ _ _ hxsup
              exact mul_eq_zero_of_right _ (hg x.1 x.2.corrupted
                (hsub (Finset.mem_insert_self 1 C)))
          erw [hzero b tr₁, hzero false tr₂]

private theorem eval_F_coin_Z_star_le_half
    (S : AdaptiveAdversary 2 CoinIn Bool Unit Unit (Option Bool)
      (AdaptiveNetQ 2 CoinIn Unit) (AdaptiveNetR Bool Unit (Option Bool))) :
    (adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S Z_star 0 []).eval true ≤ 1 / 2 := by
  have hrun_adv : ∀ (sS : (S.machine 0).State),
      (liftAdaptiveAdversary (S.machine 0)).runFrom (Z_star 0 []) sS =
        ProbOracleComp.query
            (spec := adaptiveExecSpec 2 CoinIn Bool (AdaptiveNetQ 2 CoinIn Unit)
              (AdaptiveNetR Bool Unit (Option Bool)))
            (.inl (.party 0 .go)) >>= fun _ =>
        ProbOracleComp.query (.inl (.party 0 .erase)) >>= fun _ =>
        ProbOracleComp.query (.inl (.party 1 .poll)) >>= fun optB =>
        liftAdaptiveNet (((S.machine 0).handle (.corrupt 0)).run sS) >>= fun x3 =>
        ProbOracleComp.query (.inl .status) >>= fun (C : Finset (Fin 2)) =>
        pure (match optB, x3.1 with
          | some b, .corrupt (some r) =>
              decide (C = {0} ∧ r.history = some [none, some b, none, none])
          | _, _ => false, x3.2) := by
    intro sS
    dsimp only [Z_star]
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary]
    rw [StateT.run_lift, bind_assoc]
    simp only [pure_bind]
    refine bind_congr fun _ => ?_
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary]
    rw [StateT.run_lift, bind_assoc]
    simp only [pure_bind]
    refine bind_congr fun _ => ?_
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary]
    rw [StateT.run_lift, bind_assoc]
    simp only [pure_bind]
    refine bind_congr fun optB => ?_
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary]
    refine bind_congr fun x3 => ?_
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary]
    erw [StateT.run_lift, bind_assoc]
  have hrun_exec : ∀ (sS : (S.machine 0).State)
      (rs : (adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) 0 (S.initial 0)).State),
      (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S 0).runFrom
          (Z_star 0 []) (sS, rs) =
        let p0 := if (0 : Fin 2) ∈ rs.corrupted then pure (none, rs)
          else do
            let (out, s') ← ((F_coin.toAdaptive coinReveal).machine 0 |>.handle
              (.inl (0, .go))).run rs.inner
            pure (out, (F_coin.toAdaptive coinReveal).recordSnapshot 0 s' rs.corrupted rs.trace)
        p0 >>= fun x0 =>
        let p1 := if (0 : Fin 2) ∈ x0.2.corrupted then pure (none, x0.2)
          else do
            let (out, s') ← ((F_coin.toAdaptive coinReveal).machine 0 |>.handle
              (.inl (0, .erase))).run x0.2.inner
            pure (out, (F_coin.toAdaptive coinReveal).recordSnapshot 0 s'
              x0.2.corrupted x0.2.trace)
        p1 >>= fun x1 =>
        let p2 := if (1 : Fin 2) ∈ x1.2.corrupted then pure (none, x1.2)
          else do
            let (out, s') ← ((F_coin.toAdaptive coinReveal).machine 0 |>.handle
              (.inl (1, .poll))).run x1.2.inner
            pure (out, (F_coin.toAdaptive coinReveal).recordSnapshot 0 s'
              x1.2.corrupted x1.2.trace)
        p2 >>= fun x2 =>
        ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) 0 (S.initial 0)).runFrom
          (liftAdaptiveNet (((S.machine 0).handle (.corrupt 0)).run sS)) x2.2) >>= fun x3 =>
        pure (let ⟨⟨netReply, sS'⟩, rs'⟩ := x3
          (match x2.1, netReply with
          | some b, .corrupt (some r) =>
              decide (rs'.corrupted = {0} ∧ r.history = some [none, some b, none, none])
          | _, _ => false, (sS', rs'))) := by
    intro sS rs
    let M := adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) 0 (S.initial 0)
    have hparty (i : Fin 2) (x : CoinIn) (rs' : M.State) :
        (M.handle (.inl (.party i x))).run rs' =
          if i ∈ rs'.corrupted then pure (none, rs')
          else ((F_coin.toAdaptive coinReveal).machine 0 |>.handle (.inl (i, x))).run rs'.inner >>=
            fun p => pure (p.1, (F_coin.toAdaptive coinReveal).recordSnapshot 0 p.2
              rs'.corrupted rs'.trace) := rfl
    have hstatus (rs' : M.State) :
        (M.handle (.inl .status)).run rs' = pure (rs'.corrupted, rs') := rfl
    dsimp only [adaptiveExecMachine]
    erw [Machine.runFrom_comp, hrun_adv]
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hparty, map_bind]
    refine bind_congr fun x0 => ?_
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hparty, map_bind]
    refine bind_congr fun x1 => ?_
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hparty, map_bind]
    refine bind_congr fun x2 => ?_
    erw [Machine.runFrom_bind (M := M), map_bind]
    refine bind_congr fun x3 => ?_
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hstatus, pure_bind,
      Machine.runFrom_pure (M := M)]
    simp only [map_pure, Equiv.prodAssoc_apply]
    rfl
  have hfold : (F_coin.toAdaptive coinReveal).applyInitialCorruptions 0 (S.initial 0)
      { party0 := none, delivered1 := none } = { party0 := none, delivered1 := none } := by
    simp only [AdaptiveProtocol.applyInitialCorruptions, IdealFunctionality.toAdaptive, ite_self]
    rfl
  have hinit_exec :
      ProbOracleComp.sample (spec := OracleSpec.empty)
          (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S 0).init =
        ProbOracleComp.sample (spec := OracleSpec.empty) (S.machine 0).init >>= fun sS =>
          pure (sS, { inner := { party0 := none, delivered1 := none }
                      corrupted := S.initial 0
                      trace := fun _ => [none] }) := by
    have hfold2 : List.foldl (fun acc (_ : Fin 2) => acc)
        ({ party0 := none, delivered1 := none } : CoinState) (List.finRange 2) =
        { party0 := none, delivered1 := none } := rfl
    dsimp only [adaptiveExecMachine, Machine.comp_init, liftAdaptiveAdversary, adaptiveRouter,
      F_coin, IdealFunctionality.toAdaptive, AdaptiveProtocol.applyInitialCorruptions, coinReveal]
    simp only [ite_self, hfold2, pure_bind]
    erw [ProbOracleComp.sample_bind]
    refine bind_congr fun sS => ?_
    erw [ProbOracleComp.sample_pure]
    rfl
  let mkCS (p d : Option Bool) : ((F_coin.toAdaptive coinReveal).machine 0).State :=
    ({ party0 := p, delivered1 := d } : CoinState)
  let getP0 (s : ((F_coin.toAdaptive coinReveal).machine 0).State) : Option Bool :=
    (s : CoinState).party0
  let getD1 (s : ((F_coin.toAdaptive coinReveal).machine 0).State) : Option Bool :=
    (s : CoinState).delivered1
  have hgo (s : ((F_coin.toAdaptive coinReveal).machine 0).State) :
      ((F_coin.toAdaptive coinReveal).machine 0 |>.handle (.inl (0, .go))).run s =
        if ((getP0 s).isNone && (getD1 s).isNone) = true then
          ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
            pure ((none : protocolSpec 2 CoinIn Bool Unit Unit (.inl (0, .go))),
              mkCS (some (decide (c = 0))) (some (decide (c = 0))))
        else pure ((none : protocolSpec 2 CoinIn Bool Unit Unit (.inl (0, .go))), s) := by
    simp only [F_coin, IdealFunctionality.toAdaptive, StateT.run, Fin.val_zero, ↓reduceIte,
      getP0, getD1, mkCS]
    split_ifs <;> simp [ProbOracleComp.sample_pure]
  have herase (s : ((F_coin.toAdaptive coinReveal).machine 0).State) :
      ((F_coin.toAdaptive coinReveal).machine 0 |>.handle (.inl (0, .erase))).run s =
        pure ((none : protocolSpec 2 CoinIn Bool Unit Unit (.inl (0, .erase))),
          mkCS none (getD1 s)) := by
    simp only [F_coin, IdealFunctionality.toAdaptive, StateT.run, Fin.val_zero, ↓reduceIte,
      ProbOracleComp.sample_pure, mkCS, getD1]
  have hpoll (s : ((F_coin.toAdaptive coinReveal).machine 0).State) :
      ((F_coin.toAdaptive coinReveal).machine 0 |>.handle (.inl (1, .poll))).run s =
        pure ((getD1 s : protocolSpec 2 CoinIn Bool Unit Unit (.inl (1, .poll))), s) := by
    simp only [F_coin, IdealFunctionality.toAdaptive, StateT.run, Fin.val_one, ↓reduceIte,
      ProbOracleComp.sample_pure, getD1]
  have hsnap (s : ((F_coin.toAdaptive coinReveal).machine 0).State)
      (C : Finset (Fin 2)) (tr : Fin 2 → List (Option Bool)) :
      (F_coin.toAdaptive coinReveal).recordSnapshot 0 s C tr =
        { inner := s
          corrupted := C
          trace := fun j => tr j ++ [coinReveal 0 s j] } := rfl
  have hfalse_of_none (hc : ∀ sS,
      closeEval (Prod.fst <$>
        (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S 0).runFrom
          (Z_star 0 [])
          (sS, { inner := { party0 := none, delivered1 := none }
                 corrupted := S.initial 0
                 trace := fun _ => [none] })) = PMF.pure false) :
      (adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S Z_star 0 []).eval true ≤ 1 / 2 := by
    have hev : (adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S Z_star 0 []).eval =
        PMF.pure false := by
      change closeEval (ProbOracleComp.sample
          (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S 0).init >>= fun s =>
        Prod.fst <$> (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S 0).runFrom
          (Z_star 0 []) s) = PMF.pure false
      rw [hinit_exec]
      erw [bind_assoc, closeEval_bind]
      have hbc :
          (closeEval (ProbOracleComp.sample (S.machine 0).init)).bind (fun _ => PMF.pure false) =
            PMF.pure false := PMF.bind_const _ _
      rw [← hbc]
      congr 1
      funext sS
      erw [pure_bind, hc]
    rw [hev, PMF.pure_apply]
    simp
  by_cases h0 : (0 : Fin 2) ∈ S.initial 0
  · refine hfalse_of_none fun sS => ?_
    erw [hrun_exec]
    simp only [h0, ↓reduceIte, pure_bind]
    split_ifs
    · simp only [pure_bind, map_bind, map_pure, closeEval_bind, closeEval_pure, PMF.bind_const]
    · erw [hpoll]
      dsimp only [getD1]
      simp only [pure_bind, map_bind, map_pure]
      rw [closeEval_bind, closeEval_pure, PMF.bind_const]
  · by_cases h1 : (1 : Fin 2) ∈ S.initial 0
    · refine hfalse_of_none fun sS => ?_
      erw [hrun_exec]
      simp only [h0, ↓reduceIte]
      erw [hgo]
      dsimp only [getP0, getD1, mkCS]
      simp only [Option.isNone_none, Bool.and_self, ↓reduceIte, bind_assoc, pure_bind,
        hsnap, h0, map_bind]
      rw [closeEval_bind, closeEval_sample]
      have hbc :
          (ProbComp.unifFin 1).eval.bind (fun _ => PMF.pure false) = PMF.pure false :=
        PMF.bind_const _ _
      rw [← hbc]
      congr 1
      funext c
      erw [herase]
      dsimp only [getD1, mkCS]
      simp only [pure_bind, h1, ↓reduceIte, map_pure]
      rw [closeEval_bind, closeEval_pure, PMF.bind_const]
    · have hinit : S.initial 0 = ∅ := by
        ext i
        rcases i with ⟨i, hi⟩
        interval_cases i <;> simp [h0, h1]
      have h0_not : (0 : Fin 2) ∉ (∅ : Finset (Fin 2)) := Finset.notMem_empty 0
      have h1_not : (1 : Fin 2) ∉ (∅ : Finset (Fin 2)) := Finset.notMem_empty 1
      let gMatch (b : Bool) :
          (AdaptiveNetR Bool Unit (Option Bool) × (S.machine 0).State) × Finset (Fin 2) →
            ENNReal := fun (res, C') =>
        if C' = {0} then
          match res.1 with
          | .corrupt (some r) => if r.history = some [none, some b, none, none] then 1 else 0
          | _ => 0
        else 0
      have hg_one (b : Bool) res C' (h1mem : (1 : Fin 2) ∈ C') : gMatch b (res, C') = 0 := by
        have hne : C' ≠ {0} := by
          intro heq
          rw [heq] at h1mem
          revert h1mem
          decide
        simp [gMatch, hne]
      let trC (c : Fin 2) : Fin 2 → List (Option Bool) := fun j =>
        [none,
          if j.val = 0 then some (decide (c = 0)) else some (decide (c = 0)),
          if j.val = 0 then none else some (decide (c = 0)),
          if j.val = 0 then none else some (decide (c = 0))]
      have hexp :
          (adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S Z_star 0 []).eval true =
            ∑' sS : (S.machine 0).State, closeEval (ProbOracleComp.sample (S.machine 0).init) sS *
              ∑' c : Fin 2, (ProbComp.unifFin 1).eval c *
                ∑' x, closeEval
                    ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) 0 ∅).runFrom
                      (liftAdaptiveNet (((S.machine 0).handle (.corrupt 0)).run sS))
                      { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
                        corrupted := ∅
                        trace := trC c }) x *
                  gMatch (decide (c = 0)) (x.1, x.2.corrupted) := by
        change (closeEval (ProbOracleComp.sample
            (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S 0).init >>= fun s =>
          Prod.fst <$> (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S 0).runFrom
            (Z_star 0 []) s)) true = _
        rw [hinit_exec]
        erw [bind_assoc, closeEval_bind]
        rw [PMF.bind_apply]
        refine tsum_congr fun sS => congrArg (closeEval (ProbOracleComp.sample (S.machine 0).init)
          sS * ·) ?_
        erw [pure_bind, hrun_exec]
        simp only [hinit, h0_not, ↓reduceIte]
        erw [hgo]
        dsimp only [getP0, getD1, mkCS]
        simp only [Option.isNone_none, Bool.and_self, ↓reduceIte, bind_assoc, pure_bind, hsnap,
          h0_not, map_bind]
        rw [closeEval_bind, closeEval_sample, PMF.bind_apply]
        refine tsum_congr fun c => congrArg ((ProbComp.unifFin 1).eval c * ·) ?_
        erw [herase]
        dsimp only [getD1, mkCS]
        simp only [bind_assoc, pure_bind, h1_not, ↓reduceIte]
        erw [hpoll]
        dsimp only [getD1]
        simp only [pure_bind, map_pure, coinReveal, List.cons_append, List.nil_append]
        rw [closeEval_bind, PMF.bind_apply]
        refine tsum_congr fun x => congrArg (_ * ·) ?_
        rw [closeEval_pure, PMF.pure_apply]
        rcases x with ⟨⟨netR, sS'⟩, rs'⟩
        cases netR with
        | party _ | net _ => simp [gMatch]
        | corrupt rep =>
          cases rep with
          | none => simp [gMatch]
          | some r =>
            by_cases hC : rs'.corrupted = {0} <;>
              by_cases hH : r.history = some [none, some (decide (c = 0)), none, none] <;>
              simp [gMatch, hC, hH]
      rw [hexp]
      have hinner (sS : (S.machine 0).State) :
          ∑' c : Fin 2, (ProbComp.unifFin 1).eval c *
              ∑' x, closeEval
                  ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) 0 ∅).runFrom
                    (liftAdaptiveNet (((S.machine 0).handle (.corrupt 0)).run sS))
                    { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
                      corrupted := ∅
                      trace := trC c }) x *
                gMatch (decide (c = 0)) (x.1, x.2.corrupted) ≤
            1 / 2 := by
        let μ : PMF ((AdaptiveNetR Bool Unit (Option Bool) × (S.machine 0).State) ×
            AdaptiveRouterState CoinState (Option Bool) 2) :=
          closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) 0 ∅).runFrom
            (liftAdaptiveNet (((S.machine 0).handle (.corrupt 0)).run sS))
            { inner := { party0 := none, delivered1 := some false }
              corrupted := ∅
              trace := fun _ => [none] })
        have hind (c : Fin 2) :
            ∑' x, closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) 0 ∅).runFrom
                (liftAdaptiveNet (((S.machine 0).handle (.corrupt 0)).run sS))
                { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
                  corrupted := ∅
                  trace := trC c }) x *
              gMatch (decide (c = 0)) (x.1, x.2.corrupted) =
            ∑' x, μ x * gMatch (decide (c = 0)) (x.1, x.2.corrupted) :=
          router_F_coin_no1_indep 0 (decide (c = 0)) (((S.machine 0).handle (.corrupt 0)).run sS)
            ∅ h1_not (trC c) (fun _ => [none]) (gMatch (decide (c = 0)))
            (hg_one (decide (c = 0)))
        have hunif (c : Fin 2) :
            (Probability.PMF.uniformOfFintype (Fin (1 + 1))) c = (2 : ENNReal)⁻¹ := by
          simp [Probability.PMF.uniformOfFintype]
        simp_rw [hind, ProbComp.eval_unifFin]
        rw [tsum_fintype, Fin.sum_univ_two]
        simp only [Fin.isValue, hunif, decide_true]
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← tsum_add]
        have hpt (x : (AdaptiveNetR Bool Unit (Option Bool) × (S.machine 0).State) ×
            AdaptiveRouterState CoinState (Option Bool) 2) :
            ((2 : ENNReal)⁻¹) * (μ x * gMatch true (x.1, x.2.corrupted)) +
              ((2 : ENNReal)⁻¹) * (μ x * gMatch false (x.1, x.2.corrupted)) ≤
              ((2 : ENNReal)⁻¹) * μ x := by
          have hdisj :
              gMatch true (x.1, x.2.corrupted) + gMatch false (x.1, x.2.corrupted) ≤ 1 := by
            rcases x with ⟨⟨netR, sS'⟩, rs'⟩
            dsimp [gMatch]
            cases netR with
            | party _ | net _ => simp
            | corrupt rep =>
              cases rep with
              | none => simp
              | some r =>
                by_cases hC : rs'.corrupted = {0}
                · simp only [hC, ↓reduceIte]
                  split_ifs with hT hF
                  · exfalso
                    rw [hT] at hF
                    cases hF
                  · simp
                  · simp
                  · simp
                · simp [hC]
          calc ((2 : ENNReal)⁻¹) * (μ x * gMatch true (x.1, x.2.corrupted)) +
                ((2 : ENNReal)⁻¹) * (μ x * gMatch false (x.1, x.2.corrupted))
              = ((2 : ENNReal)⁻¹) * (μ x *
                  (gMatch true (x.1, x.2.corrupted) + gMatch false (x.1, x.2.corrupted))) := by
                ring
            _ ≤ ((2 : ENNReal)⁻¹) * (μ x * 1) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdisj zero_le) zero_le
            _ = ((2 : ENNReal)⁻¹) * μ x := by ring
        calc ∑' x, (((2 : ENNReal)⁻¹) * (μ x * gMatch true (x.1, x.2.corrupted)) +
                ((2 : ENNReal)⁻¹) * (μ x * gMatch false (x.1, x.2.corrupted)))
            ≤ ∑' x, ((2 : ENNReal)⁻¹) * μ x := tsum_le_tsum hpt
          _ = ((2 : ENNReal)⁻¹) * ∑' x, μ x := ENNReal.tsum_mul_left
          _ = (1 : ENNReal) / 2 := by rw [PMF.tsum_coe, mul_one, one_div]
      calc ∑' sS : (S.machine 0).State, closeEval (ProbOracleComp.sample (S.machine 0).init) sS *
              ∑' c : Fin 2, (ProbComp.unifFin 1).eval c *
                ∑' x, closeEval
                    ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) 0 ∅).runFrom
                      (liftAdaptiveNet (((S.machine 0).handle (.corrupt 0)).run sS))
                      { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
                        corrupted := ∅
                        trace := trC c }) x *
                  gMatch (decide (c = 0)) (x.1, x.2.corrupted)
          ≤ ∑' sS : (S.machine 0).State,
              closeEval (ProbOracleComp.sample (S.machine 0).init) sS * ((1 : ENNReal) / 2) :=
            tsum_le_tsum fun sS => mul_le_mul_of_nonneg_left (hinner sS) zero_le
        _ = (∑' sS, closeEval (ProbOracleComp.sample (S.machine 0).init) sS) * (1 / 2) :=
            ENNReal.tsum_mul_right
        _ = 1 / 2 := by rw [PMF.tsum_coe, one_mul]

/-- `P_coin .nonErasing` cannot be adaptively emulated by `F_coin.toAdaptive coinReveal` with any
concrete error below `1 / 2`. -/
theorem not_adaptiveEmulatesWithin_nonErasing_witness
    {g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (hε : ε 1 5 0 < 1 / 2) :
    ¬ AdaptiveEmulatesWithin .adaptive (P_coin .nonErasing) (F_coin.toAdaptive coinReveal)
      g ε := by
  intro hadv
  obtain ⟨S, pS, hS, hSg, hbound⟩ :=
    hadv _ _ (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit) 1
      (adaptiveDummyAdversary_polyBounded _ _ _)
  have h1 : adaptiveAdvantage .adaptive (P_coin .nonErasing) (F_coin.toAdaptive coinReveal)
      (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit) S Z_star 0 [] ≤
      ε 1 5 0 :=
    hbound Z_star 5 Z_star_polyBounded 0 []
  have hP := eval_Z_star_nonErasing 0 []
  have hQ := eval_F_coin_Z_star_le_half S
  have hP_real : ((adaptiveExec .adaptive (P_coin .nonErasing)
      (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
      Z_star 0 []).eval true).toReal = 1 := by
    rw [hP]; simp
  have hQ_real : ((adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S
      Z_star 0 []).eval true).toReal ≤ 1 / 2 := by
    simpa [ENNReal.toReal_div] using
      ENNReal.toReal_mono (by norm_num) hQ
  have hlow : (1 / 2 : ℝ) ≤
      (adaptiveAdvantage .adaptive (P_coin .nonErasing) (F_coin.toAdaptive coinReveal)
        (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
        S Z_star 0 [] : ℝ) := by
    rw [adaptiveAdvantage, Game.coe_advantage, Game.coe_succProbability,
      Game.coe_succProbability, hP_real]
    have h := le_abs_self (1 - ((adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S
      Z_star 0 []).eval true).toReal)
    linarith
  have hε_real : (ε 1 5 0 : ℝ) < 1 / 2 := by exact_mod_cast hε
  have h1_real : (adaptiveAdvantage .adaptive (P_coin .nonErasing) (F_coin.toAdaptive coinReveal)
      (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
      S Z_star 0 [] : ℝ) ≤ (ε 1 5 0 : ℝ) := by
    exact_mod_cast h1
  linarith

end CslibFrontierTests.Crypto.UCAdaptive
