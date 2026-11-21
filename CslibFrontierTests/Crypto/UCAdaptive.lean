/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.UC.Adaptive

/-!
# Tests for adaptive corruptions in the UC execution

Exercises `CslibFrontier.Crypto.Protocols.UC.Adaptive` on a concrete two-party coin-flipping
protocol `P_coin`, ideal functionality `F_coin` (`F_coin_toStatic_eq`), and corruption-tracking
`F_corrTrack`:

* Router unit tests checking `.static` vs `.adaptive`, `.nonErasing` vs `.erasing`, and `.status`.
* Concrete `corruptAdv` witness (`PolyBounded`, `.status` reports `{0, 1}` in `.adaptive` mode)
  and `.corrupt` branch check for `adaptiveExec_static_eq_adaptive_of_noCorrupt`
  (`corruptPre_static_eq_adaptive`).
* Static embedding checks (`static_embedding_check`, `staticCheckEnv_toAdaptive_polyBounded`,
  `static_adaptive_embedding_check`) via `AdaptiveAdversary.ofStatic` and `Environment.toAdaptive`.
* Ideal-functionality corruption tracking (`P_corrTrack_toStatic_eq`, `F_corrTrack_midRun_corrupt`).
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
          if i.val = 0 ∧ s.party0.isNone && s.delivered1.isNone then do
            let c ← ProbOracleComp.sample (ProbComp.unifFin 1)
            let b := decide (c = 0)
            pure (none, { party0 := some b, delivered1 := some b })
          else pure (none, s)
      | .inl (i, .erase) => fun s =>
          pure (none, if i.val = 0 then { s with party0 := none } else s)
      | .inl (i, .poll) => fun s =>
          pure (if i.val = 1 then s.delivered1 else none, s)
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
        if i.val = 0 ∧ s.party0.isNone && s.delivered1.isNone then do
          let c ← ProbComp.unifFin 1
          let b := decide (c = 0)
          pure (none, { party0 := some b, delivered1 := some b })
        else pure (none, s)
    | i, .erase => fun s =>
        pure (none, if i.val = 0 then { s with party0 := none } else s)
    | i, .poll => fun s =>
        pure (if i.val = 1 then s.delivered1 else none, s)
  onBackdoor _ s := pure ((), s)

/-- Local state-leakage view map `reveal` for `F_coin`: party `0` exposes `party0` until `.erase`,
and party `1` exposes its delivered output `delivered1`. -/
def coinReveal (_ : ℕ) (s : F_coin.State) (i : Fin 2) : Option Bool :=
  if i.val = 0 then s.party0 else s.delivered1

theorem F_coin_toStatic_eq :
    (F_coin.toAdaptive coinReveal).toStatic = F_coin.toProtocol :=
  F_coin.toStatic_toAdaptive_of_initIndep _ fun _ _ => rfl

/-! ### Router unit tests on explicit states -/

private def coinInitRS (C₀ : Finset (Fin 2)) :
    AdaptiveRouterState CoinState (Option Bool) 2 :=
  { inner := { party0 := none, delivered1 := none }
    corrupted := C₀
    trace := fun _ => [none] }

private theorem router_static_ignores_corrupt_one :
    ((adaptiveRouter .static (P_coin .erasing) 0 {0}).handle (.inr (.corrupt 1))).run
        (coinInitRS {0}) = pure (.corrupt none, coinInitRS {0}) := rfl

private theorem router_static_reports_corrupt_zero :
    ((adaptiveRouter .static (P_coin .erasing) 0 {0}).handle (.inr (.corrupt 0))).run
        (coinInitRS {0}) =
      pure (.corrupt (some { current := none, history := none }), coinInitRS {0}) := rfl

private theorem router_adaptive_corrupts_one_mid_run (b : Bool) :
    let sMid : AdaptiveRouterState CoinState (Option Bool) 2 :=
      ⟨{ party0 := some b, delivered1 := some b }, ∅, fun _ => [none, some b]⟩
    ((adaptiveRouter .adaptive (P_coin .erasing) 0 ∅).handle (.inr (.corrupt 1))).run sMid =
      pure (.corrupt (some { current := some b, history := none }),
        { sMid with corrupted := {1} }) := by
  intro sMid; simp [adaptiveRouter, P_coin, AdaptiveProtocol.corruptionReport, StateT.run, sMid]

private theorem router_nonErasing_vs_erasing_trace (b : Bool) :
    let sGo := (P_coin .nonErasing).recordSnapshot 0 { party0 := some b, delivered1 := some b }
      ∅ (fun _ => [none])
    let sEraseNon := (P_coin .nonErasing).recordSnapshot 0 { party0 := none, delivered1 := some b }
      ∅ sGo.trace
    let sEraseEr := (P_coin .erasing).recordSnapshot 0 { party0 := none, delivered1 := some b }
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
  simp [adaptiveRouter, StateT.run]; rfl

/-! ### Concrete adversary and status check -/

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

/-- Environment that instructs `corruptAdv` to corrupt `0` and checks `.status = {0, 1}`. -/
def corruptCheckEnv :
    AdaptiveEnvironment 2 CoinIn Bool (Fin 2) (AdaptiveNetR Bool Unit (Option Bool)) :=
  fun _ _ => do
    let _ ← ProbOracleComp.query
      (spec := adaptiveExecSpec 2 CoinIn Bool (Fin 2) (AdaptiveNetR Bool Unit (Option Bool)))
      (.inr 0)
    let C : Finset (Fin 2) ← ProbOracleComp.query
      (spec := adaptiveExecSpec 2 CoinIn Bool (Fin 2) (AdaptiveNetR Bool Unit (Option Bool)))
      (.inl .status)
    pure (decide (C = ({0, 1} : Finset (Fin 2))))

private theorem corruptCheckEnv_eval_eq (mode : CorruptionMode) (κ : ℕ) (z : List Bool)
    (C' : Finset (Fin 2)) (rep : Option (CorruptionReport (Option Bool)))
    (hcor : ((adaptiveRouter mode (P_coin .erasing) κ {1}).handle (.inr (.corrupt 0))).run
        ⟨{ party0 := none, delivered1 := none }, {1}, fun _ => [none]⟩ =
      pure (.corrupt rep, ⟨{ party0 := none, delivered1 := none }, C', fun _ => [none]⟩)) :
    (adaptiveExec mode (P_coin .erasing) corruptAdv corruptCheckEnv κ z).eval
      (decide (C' = ({0, 1} : Finset (Fin 2)))) = 1 := by
  let A := liftAdaptiveAdversary (n := 2) (In := CoinIn) (Out := Bool)
    (corruptAdv.machine κ)
  let M := adaptiveRouter mode (P_coin .erasing) κ (corruptAdv.initial κ)
  let sInit : AdaptiveRouterState CoinState (Option Bool) 2 :=
    ⟨{ party0 := none, delivered1 := none }, {1}, fun _ => [none]⟩
  have hMinit : M.init = pure sInit := by
    simp only [M, sInit, adaptiveRouter, P_coin, AdaptiveProtocol.applyInitialCorruptions,
      corruptAdv, pure_bind]
    congr 1; congr 1; funext i; fin_cases i <;> rfl
  have hrunA : A.runFrom (corruptCheckEnv κ z) () =
      ProbOracleComp.query
          (spec := adaptiveProtocolSpec 2 CoinIn Bool Unit Unit (Option Bool))
          (.inr (.corrupt 0)) >>= fun _ =>
      ProbOracleComp.query (.inl .status) >>= fun (C : Finset (Fin 2)) =>
      pure (decide (C = ({0, 1} : Finset (Fin 2))), ()) := by
    dsimp only [corruptCheckEnv]
    erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A), StateT.run_lift]
    dsimp only [A, liftAdaptiveAdversary, corruptAdv]; simp only [bind_assoc, pure_bind]
    exact bind_congr fun _ => by
      erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A)]
      simp only [Machine.runFrom_pure]; rfl
  rw [adaptiveExec, Machine.run]
  change (Machine.closeProgram do
    let s ← ProbOracleComp.sample (A.comp M).init
    Prod.fst <$> (A.comp M).runFrom (corruptCheckEnv κ z) s).eval
      (decide (C' = ({0, 1} : Finset (Fin 2)))) = 1
  rw [Machine.comp_init]
  erw [hMinit, ProbOracleComp.sample_bind, ProbOracleComp.sample_pure, bind_assoc, pure_bind,
    ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_comp (A := A) (P := M), hrunA,
    Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), map_bind, hcor, map_pure]
  simp [Machine.closeProgram_pure, ProbComp.eval_pure]

theorem corruptAdv_adaptiveExec_status (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive (P_coin .erasing) corruptAdv corruptCheckEnv κ z).eval true = 1 := by
  have h := corruptCheckEnv_eval_eq .adaptive κ z {0, 1}
    (some { current := none, history := none }) <| by
    have hnot : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) := by decide
    simp only [adaptiveRouter, StateT.run, P_coin, hnot, ↓reduceIte,
      AdaptiveProtocol.corruptionReport]; rfl
  simpa using h

/-- Adversary that initially corrupts `{1}` and sends only `.corrupt 1` (`NoNewCorrupt`). -/
def corruptPreAdv :
    AdaptiveAdversary 2 CoinIn Bool Unit Unit (Option Bool)
      Unit (AdaptiveNetR Bool Unit (Option Bool)) where
  initial _ := {1}
  machine _ := {
    State := Unit
    init := pure ()
    handle _ _ := do
      let r ← ProbOracleComp.query
        (spec := netSpec (AdaptiveNetQ 2 CoinIn Unit) (AdaptiveNetR Bool Unit (Option Bool)))
        (.corrupt 1)
      pure (r, ()) }

/-- Environment querying `corruptPreAdv` and checking that `.corrupt 1` returns `some _`. -/
def corruptPreEnv :
    AdaptiveEnvironment 2 CoinIn Bool Unit (AdaptiveNetR Bool Unit (Option Bool)) :=
  fun _ _ => do
    let r ← ProbOracleComp.query
      (spec := adaptiveExecSpec 2 CoinIn Bool Unit (AdaptiveNetR Bool Unit (Option Bool)))
      (.inr ())
    pure (match r with | .corrupt (some rep) => rep.current == none | _ => false)

theorem corruptPre_static_eq_adaptive (κ : ℕ) (z : List Bool) :
    adaptiveExec .static (P_coin .erasing) corruptPreAdv corruptPreEnv κ z =
      adaptiveExec .adaptive (P_coin .erasing) corruptPreAdv corruptPreEnv κ z ∧
      (adaptiveExec .adaptive (P_coin .erasing) corruptPreAdv corruptPreEnv κ z).eval true = 1 := by
  have hno : corruptPreAdv.NoNewCorrupt := fun _ _ _ => by
    dsimp only [corruptPreAdv, StateT.run]
    exact .bind (.query (by decide)) fun _ => .pure _
  refine ⟨adaptiveExec_static_eq_adaptive_of_noCorrupt _ _ hno _ κ z, ?_⟩
  let A := liftAdaptiveAdversary (n := 2) (In := CoinIn) (Out := Bool) (corruptPreAdv.machine κ)
  let M := adaptiveRouter .adaptive (P_coin .erasing) κ (corruptPreAdv.initial κ)
  let sInit : AdaptiveRouterState CoinState (Option Bool) 2 :=
    ⟨{ party0 := none, delivered1 := none }, {1}, fun _ => [none]⟩
  have hMinit : M.init = pure sInit := by
    simp only [M, sInit, adaptiveRouter, P_coin, AdaptiveProtocol.applyInitialCorruptions,
      corruptPreAdv, pure_bind]
    congr 1; congr 1; funext i; fin_cases i <;> rfl
  have hrunA : A.runFrom (corruptPreEnv κ z) () =
      ProbOracleComp.query
          (spec := adaptiveProtocolSpec 2 CoinIn Bool Unit Unit (Option Bool))
          (.inr (.corrupt 1)) >>= fun r =>
      pure (match r with | .corrupt (some rep) => rep.current == none | _ => false, ()) := by
    dsimp only [corruptPreEnv]
    erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A)]
    dsimp only [A, liftAdaptiveAdversary, Machine.liftRight, corruptPreAdv, liftAdaptiveNet,
      Machine.liftRightProgram, StateT.run]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_pure, bind_assoc, pure_bind]
    exact bind_congr fun _ => by erw [Machine.runFrom_pure (M := A)]; rfl
  have hmem : (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by decide
  have hcor : (M.handle (.inr (.corrupt 1))).run sInit =
      pure (.corrupt (some { current := none, history := none }), sInit) := by
    simp only [M, sInit, adaptiveRouter, StateT.run, hmem, ↓reduceIte,
      AdaptiveProtocol.corruptionReport]
    rfl
  rw [adaptiveExec, Machine.run]
  change (Machine.closeProgram (ProbOracleComp.sample (A.comp M).init >>= fun s =>
    Prod.fst <$> (A.comp M).runFrom (corruptPreEnv κ z) s)).eval true = 1
  rw [Machine.comp_init]
  erw [hMinit, ProbOracleComp.sample_bind, ProbOracleComp.sample_pure, bind_assoc, pure_bind,
    ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_comp (A := A) (P := M), hrunA,
    Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), map_bind, hcor, pure_bind,
    Machine.runFrom_pure (M := M), map_pure, Equiv.prodAssoc_apply]
  simp [Machine.closeProgram_pure, ProbComp.eval_pure]

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
      ProbOracleComp.query (.inl (0, .go)) >>= fun _ =>
      ProbOracleComp.query
          (spec := partySpec 2 CoinIn Bool ⊕ₒ
            netSpec (RoutedNetQ 2 CoinIn Unit) (RoutedNetR Bool Unit))
          (.inr (.inl (1, CoinIn.poll))) >>= fun out =>
      pure (decide ((match out with | .inl o => o | .inr () => none) = some true), ()) := by
    dsimp only [staticCheckEnv]
    erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A), StateT.run_lift]
    dsimp only [A, liftAdversary, staticPollOneAdv]; simp only [bind_assoc, pure_bind]
    exact bind_congr fun _ => by
      erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A)]
      dsimp only [A, liftAdversary, Machine.liftRight, staticPollOneAdv, liftNet,
        Machine.liftRightProgram, StateT.run]
      simp only [OracleComp.interpret_bind, OracleComp.interpret_pure, bind_assoc, pure_bind]
      exact bind_congr fun _ => by erw [Machine.runFrom_pure (M := A)]; rfl
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
      ↓reduceIte, Fin.val_zero, Option.isNone_none, Bool.and_self, and_self, bind_pure_comp]
  have hM1 (s : CoinState) : (M.handle (.inr (.inl (1, .poll)))).run s =
      pure (.inl s.delivered1, s) := by
    simp only [M, corruptRouter, AdaptiveProtocol.toStatic, P_coin, hmem, ↓reduceIte,
      StateT.run, Fin.val_one]; rfl
  have htail (b' : Bool) : Prod.fst <$> (Equiv.prodAssoc Bool A.State M.State <$> M.runFrom
      (ProbOracleComp.query
          (spec := partySpec 2 CoinIn Bool ⊕ₒ
            netSpec (RoutedNetQ 2 CoinIn Unit) (RoutedNetR Bool Unit))
          (.inr (.inl (1, CoinIn.poll))) >>= fun out =>
        pure (decide ((match out with | .inl o => o | .inr () => none) = some true), ()))
      ({ party0 := some b', delivered1 := some b' } : CoinState)) = pure (decide (b' = true)) := by
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hM1, pure_bind,
      Machine.runFrom_pure (M := M)]
    simp only [map_pure, Equiv.prodAssoc_apply, Option.some.injEq]
  rw [Machine.comp_init]; have hinitA : A.init = pure () := rfl
  erw [hinitM, hinitA, ProbOracleComp.sample_bind, ProbOracleComp.sample_pure, bind_assoc,
    pure_bind, ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_comp (A := A) (P := M),
    hrunA, Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), map_bind, hM0,
    map_bind, bind_map_left]
  simp only [Machine.closeProgram_bind, Machine.closeProgram_sample,
    ProbComp.eval_bind, ProbComp.eval_unifFin]
  rw [PMF.bind_apply, tsum_fintype, Fin.sum_univ_two]
  erw [htail (decide ((0 : Fin 2) = 0)), htail (decide ((1 : Fin 2) = 0))]
  simp [Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_apply,
    Probability.PMF.uniformOfFintype, one_div]

theorem staticCheckEnv_polyBounded : staticCheckEnv.PolyBounded 2 := fun κ _ => by
  simp only [Polynomial.eval_ofNat]
  change (staticCheckEnv κ _).IsQueryBounded 2
  unfold staticCheckEnv
  exact OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
    OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
      OracleComp.IsCostBounded.pure _ 0

theorem staticCheckEnv_toAdaptive_polyBounded : staticCheckEnv.toAdaptive.PolyBounded 2 :=
  staticCheckEnv_polyBounded.toAdaptive

theorem static_adaptive_embedding_check (κ : ℕ) (z : List Bool) :
    adaptiveExec .adaptive (P_coin .erasing)
        (AdaptiveAdversary.ofStatic staticPollOneAdv (fun _ => {1}))
        staticCheckEnv.toAdaptive κ z =
      exec (P_coin .erasing).toStatic staticPollOneAdv {1} staticCheckEnv κ z ∧
      (adaptiveExec .adaptive (P_coin .erasing)
          (AdaptiveAdversary.ofStatic staticPollOneAdv (fun _ => {1}))
          staticCheckEnv.toAdaptive κ z).eval true = 1 / 2 := by
  refine ⟨adaptiveExec_adaptive_ofStatic (P_coin .erasing) staticPollOneAdv
    (fun _ => {1}) staticCheckEnv κ z, ?_⟩
  rw [adaptiveExec_adaptive_ofStatic, ← (static_embedding_check κ z).1]
  exact (static_embedding_check κ z).2

/-! ### Ideal-functionality corruption notification check (`Canetti2020`, pp. 28:73–74) -/

/-- Ideal functionality whose state tracks its corrupted party set (`C`-dependent `init`, backdoor
readout). -/
def F_corrTrack : IdealFunctionality 2 Unit Unit Unit (Finset (Fin 2)) where
  State := Finset (Fin 2)
  init _ C := pure C
  onInput _ _ := pure none
  onBackdoor _ := get

/-- Embedding `F_corrTrack` with `onCorrupt := insert` recovers `F_corrTrack.toProtocol` via
`toStatic` and records mid-run corruptions in `F`'s state. -/
def P_corrTrack : AdaptiveProtocol 2 Unit Unit Unit (Finset (Fin 2)) (Finset (Fin 2)) :=
  F_corrTrack.toAdaptive (fun _ s _ => s) fun _ i s =>
    insert (α := Fin 2) (γ := Finset (Fin 2)) i s

theorem P_corrTrack_toStatic_eq :
    P_corrTrack.toStatic = F_corrTrack.toProtocol := by
  refine F_corrTrack.toStatic_toAdaptive _ _ fun κ C => ?_
  dsimp only [IdealFunctionality.toAdaptive, F_corrTrack]
  erw [map_pure]
  apply congrArg pure
  ext j
  have hfr : List.finRange 2 = [0, 1] := rfl
  dsimp only [AdaptiveProtocol.applyInitialCorruptions]
  rw [hfr]
  by_cases h0 : (0 : Fin 2) ∈ C <;> by_cases h1 : (1 : Fin 2) ∈ C <;>
    fin_cases j <;> simp [h0, h1]

theorem F_corrTrack_midRun_corrupt (κ : ℕ) (z : List Bool) :
    let corrTrackAdv :
        AdaptiveAdversary 2 Unit Unit Unit (Finset (Fin 2)) (Finset (Fin 2))
          (Fin 2 ⊕ Unit) (AdaptiveNetR Unit (Finset (Fin 2)) (Finset (Fin 2))) :=
      { initial := fun _ => ∅
        machine := fun _ =>
          { State := Unit
            init := pure ()
            handle
              | .inl i => fun _ => ProbOracleComp.query (.corrupt i) >>= fun r => pure (r, ())
              | .inr () => fun _ => ProbOracleComp.query (.net ()) >>= fun r => pure (r, ()) } }
    let Z : AdaptiveEnvironment 2 Unit Unit
        (Fin 2 ⊕ Unit) (AdaptiveNetR Unit (Finset (Fin 2)) (Finset (Fin 2))) :=
      fun _ _ => do
        let _ ← ProbOracleComp.query
          (spec := adaptiveExecSpec 2 Unit Unit (Fin 2 ⊕ Unit)
            (AdaptiveNetR Unit (Finset (Fin 2)) (Finset (Fin 2)))) (.inr (.inl 1))
        let res ← ProbOracleComp.query
          (spec := adaptiveExecSpec 2 Unit Unit (Fin 2 ⊕ Unit)
            (AdaptiveNetR Unit (Finset (Fin 2)) (Finset (Fin 2)))) (.inr (.inr ()))
        pure (decide (res = .net {1}))
    (adaptiveExec .adaptive P_corrTrack corrTrackAdv Z κ z).eval true = 1 := by
  intro corrTrackAdv Z
  let A := liftAdaptiveAdversary (n := 2) (In := Unit) (Out := Unit) (corrTrackAdv.machine κ)
  let M := adaptiveRouter .adaptive P_corrTrack κ ∅
  have hfold : List.foldl (fun acc (_ : Fin 2) => acc) (∅ : Finset (Fin 2)) (List.finRange 2) = ∅ :=
    rfl
  have hMinit : M.init = pure ({ inner := ∅, corrupted := ∅, trace := fun _ => [∅] } :
      AdaptiveRouterState (Finset (Fin 2)) (Finset (Fin 2)) 2) := by
    simp only [M, adaptiveRouter, P_corrTrack, IdealFunctionality.toAdaptive, F_corrTrack,
      AdaptiveProtocol.applyInitialCorruptions, Finset.notMem_empty, ↓reduceIte, hfold, pure_bind]
  have hrunA : A.runFrom (Z κ z) () =
      ProbOracleComp.query (.inr (.corrupt 1)) >>= fun _ =>
      ProbOracleComp.query
          (spec := adaptiveProtocolSpec 2 Unit Unit Unit (Finset (Fin 2)) (Finset (Fin 2)))
          (.inr (.net ())) >>= fun res => pure (decide (res = .net {1}), ()) := by
    dsimp only [Z]
    erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A)]
    dsimp only [A, liftAdaptiveAdversary, Machine.liftRight, corrTrackAdv, liftAdaptiveNet,
      Machine.liftRightProgram, StateT.run]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_pure, bind_assoc, pure_bind]
    exact bind_congr fun _ => by
      erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A)]
      simp only [Machine.runFrom_pure]; rfl
  rw [adaptiveExec, Machine.run]
  change (Machine.closeProgram do
    let s ← ProbOracleComp.sample (A.comp M).init
    Prod.fst <$> (A.comp M).runFrom (Z κ z) s).eval true = 1
  rw [Machine.comp_init]
  erw [hMinit, ProbOracleComp.sample_bind, ProbOracleComp.sample_pure, bind_assoc, pure_bind,
    ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_comp (A := A) (P := M), hrunA,
    Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M)]
  dsimp only [M, adaptiveRouter, StateT.run, P_corrTrack, IdealFunctionality.toAdaptive,
    F_corrTrack]
  simp only [Finset.notMem_empty, ↓reduceIte, pure_bind]
  erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M)]
  dsimp only [M, adaptiveRouter, StateT.run, P_corrTrack, IdealFunctionality.toAdaptive,
    F_corrTrack, get, getThe, MonadStateOf.get, StateT.get]
  erw [pure_bind, pure_bind, Machine.runFrom_pure, map_pure, Equiv.prodAssoc_apply]
  have hins : insert (1 : Fin 2) (∅ : Finset (Fin 2)) = {1} := by decide
  simp only [Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_apply, hins,
    decide_true, ↓reduceIte]

end CslibFrontierTests.Crypto.UCAdaptive
