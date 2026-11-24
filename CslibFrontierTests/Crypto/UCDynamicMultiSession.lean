/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Negligible
import CslibFrontier.Crypto.Protocols.UC.DynamicMultiSession
import CslibFrontier.Tactic.Negligible

/-!
# Tests for Dynamic-SID Multi-Session UC Composition

Concrete witnesses over an infinite session identifier type `SID = ℕ` exercising
`Cslib.Crypto.Protocols.UC.DynamicMultiSession`:
* **Lazy first-touch isolation & budget bound**: querying arbitrarily large `sid : ℕ` (`42`, `999`)
  leaves untouched sessions `none`, `touchedSessions_transcript_card_le` and
  `mem_support_dynParLazy_init_touched_card_le` bound the `Finset ℕ` of touched/initialized
  sessions by the program's query budget, and `eval_run_dynParLazy_eq_parFin` matches eager
  `SSP.parFin`.
* **Dynamic-SID UC composition**: `dynChooseOuter : DynHybridProtocol ℕ 2 (ℕ × Bool) Bool ...`
  adaptively picks session identifiers `2 * baseSid` and `2 * baseSid + 1 + c.val` at runtime
  (unreachable by any fixed `Fin m` family over `ℕ`), satisfying `EmulatesDummyWithin.composeDyn`,
  `EmulatesWithin.composeDyn`, `Emulates.composeDyn`, and `Realizes.composeDyn`, paired with a
  non-vacuity separation witness at `κ = 0`, `baseSid = 500`, `C = ∅` and `C = {0}`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCDynamicMultiSession

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.UC
open OracleComp (IsCostBounded)
open scoped NNReal

/-! ### Self-contained relay protocol and dynamic-SID outer hybrid -/

private structure LatchState : Type where
  last : Option Bool := none
  deriving DecidableEq

private def latchStep (b : Bool) (s : LatchState) : Option Bool × LatchState :=
  if b then (some true, { last := some true }) else (s.last, s)

private def idealLatch : IdealFunctionality 2 Bool Bool Unit Unit where
  State := LatchState
  init := fun _ _ => pure { last := none }
  onInput := fun _ b s => pure (latchStep b s)
  onBackdoor := fun () s => pure ((), s)

private def faultyLatch : Protocol 2 Bool Bool Unit Unit := fun κ _ =>
  { State := LatchState
    init := pure { last := none }
    handle
      | .inl (_, b) => fun s =>
          ProbOracleComp.sample (ProbComp.unifFin (2 ^ (κ + 1) - 1)) >>= fun r =>
            pure (latchStep (if r.val = 0 then !b else b) s)
      | .inr () => fun s => pure ((), s) }

/-- Outer hybrid protocol indexed by `SID = ℕ`: on input `(p, (baseSid, b))`, samples a private
coin `c` and adaptively queries dynamic sessions `2 * baseSid` and `2 * baseSid + 1 + c.val`. -/
private def dynChooseOuter : DynHybridProtocol ℕ 2 (ℕ × Bool) Bool Unit Unit Bool Bool :=
  fun _ _ =>
    { State := Unit
      init := pure ()
      handle
        | .inl (p, (baseSid, b)) => fun s => do
            let c ← ProbOracleComp.sample (ProbComp.unifFin 1)
            let x₀ ← ProbOracleComp.query
              (⟨2 * baseSid, p, b⟩ : DynSessionCall ℕ 2 Bool)
            let x₁ ← ProbOracleComp.query
              (⟨2 * baseSid + 1 + c.val, p, b⟩ : DynSessionCall ℕ 2 Bool)
            pure (some (x₀.getD false && x₁.getD false), s)
        | .inr () => fun s => pure ((), s) }

private def zDyn (p : Fin 2) (baseSid : ℕ) : Environment 2 (ℕ × Bool) Bool
    (RoutedNetQ 2 (ℕ × Bool) (DynNetQ ℕ Unit (RoutedNetQ 2 Bool Unit)))
    (RoutedNetR Bool (Unit ⊕ RoutedNetR Bool Unit)) := fun _ _ =>
  ProbOracleComp.query (Sum.inl (p, (baseSid, true))) >>= fun res => pure (!(res.getD false))

private theorem idealLatch_polyBounded : idealLatch.toProtocol.PolyBounded 1 := fun _ _ =>
  ⟨(IsCostBounded.pure _ 0).mono (by simp),
    fun q _ => by cases q <;> exact (IsCostBounded.pure _ 0).mono (by simp)⟩

private theorem faultyLatch_polyBounded : faultyLatch.PolyBounded 1 := fun κ _ =>
  ⟨(IsCostBounded.pure _ 0).mono (by simp), fun q _ => by cases q with
    | inl _ =>
      exact ((Machine.isQueryBounded_sample (IsCostBounded.query (2 ^ (κ + 1) - 1))).bind
        fun _ => IsCostBounded.pure _ 0).mono (by simp)
    | inr _ => exact (IsCostBounded.pure _ 0).mono (by simp)⟩

private theorem dynChooseOuter_polyBounded : dynChooseOuter.PolyBounded 3 := fun _ _ =>
  ⟨(IsCostBounded.pure _ 0).mono (by simp), fun q _ => by cases q with
    | inl pb =>
      exact ((Machine.isQueryBounded_sample (IsCostBounded.query 1)).bind fun c =>
        (IsCostBounded.query (Sum.inr (⟨2 * pb.2.1, pb.1, pb.2.2⟩ : DynSessionCall ℕ 2 Bool))).bind
          fun _ =>
        (IsCostBounded.query
          (Sum.inr (⟨2 * pb.2.1 + 1 + c.val, pb.1, pb.2.2⟩ : DynSessionCall ℕ 2 Bool))).bind
          fun _ => IsCostBounded.pure _ 0).mono (by simp)
    | inr _ => exact (IsCostBounded.pure _ 0).mono (by simp)⟩

private theorem zDyn_polyBounded (p : Fin 2) (baseSid : ℕ) : (zDyn p baseSid).PolyBounded 1 :=
  fun _ _ =>
    ((IsCostBounded.query (Sum.inr (Sum.inl (p, (baseSid, true))))).bind fun _ =>
      IsCostBounded.pure _ 0).mono (by simp)

/-! ### Lazy first-touch isolation, touched-session cardinality, and reindexing witness -/

private def dynTouchProg :
    ProbOracleComp
      (dynSessionSpec ℕ (protocolSpec 2 Bool Bool (RoutedNetQ 2 Bool Unit)
        (RoutedNetR Bool Unit)))
      (Option Bool × Option Bool) := do
  let _ ← ProbOracleComp.query (42, Sum.inl ((0 : Fin 2), true))
  let r₁ ← ProbOracleComp.query (999, Sum.inl ((0 : Fin 2), false))
  let r₀ ← ProbOracleComp.query (42, Sum.inl ((0 : Fin 2), false))
  pure (r₁, r₀)

private theorem dynTouchProg_bounded : dynTouchProg.IsQueryBounded 3 :=
  ((IsCostBounded.query (Sum.inr (42, Sum.inl ((0 : Fin 2), true)))).bind fun _ =>
    (IsCostBounded.query (Sum.inr (999, Sum.inl ((0 : Fin 2), false)))).bind fun _ =>
      (IsCostBounded.query (Sum.inr (42, Sum.inl ((0 : Fin 2), false)))).bind fun _ =>
        IsCostBounded.pure _ 0).mono (by simp)

/-- Lazy isolation over `SID = ℕ`: writing `true` in session `42` leaves session `999` at `none`. -/
example :
    ((dynSessionRouter (SID := ℕ) (∅ : Finset (Fin 2)) (idealLatch.toProtocol 0 ∅)).run
      dynTouchProg).eval = PMF.pure (none, some true) := by
  simp only [Machine.run, Machine.link, dynTouchProg, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.runFrom_pure]
  dsimp only [dynSessionRouter, dynParLazy, corruptRouter, idealLatch,
    IdealFunctionality.toProtocol, latchStep, StateT.run]
  simp only [Finset.notMem_empty, ↓reduceIte, Bool.false_eq_true, ProbOracleComp.sample_pure,
    pure_bind, Function.update_self,
    Function.update_of_ne (by decide : (42 : ℕ) ≠ 999),
    Function.update_of_ne (by decide : (999 : ℕ) ≠ 42),
    Machine.closeProgram_pure, ProbComp.eval_pure, map_pure]

/-- Any supported execution of `dynTouchProg` against `dynSessionRouter` initializes at most
`3` sessions in `ℕ` and matches eager `SSP.parFin (Fin 4)` via `allocMachine`. -/
theorem dynTouchProg_touched_and_bridge :
    (∀ res s', (res, s') ∈ (Machine.closeEval
      ((dynSessionRouter (SID := ℕ) ∅ (idealLatch.toProtocol 0 ∅)).runFrom
        dynTouchProg (fun _ => none))).support →
      ∃ S : Finset ℕ, S.card ≤ 3 ∧ ∀ sid, (s' sid).isSome → sid ∈ S) ∧
    ((dynSessionRouter (SID := ℕ) ∅ (idealLatch.toProtocol 0 ∅)).run dynTouchProg).eval =
      ((SSP.parFin fun _ : Fin 4 => corruptRouter ∅ (idealLatch.toProtocol 0 ∅)).run
        ((allocMachine ℕ 3 _).link dynTouchProg)).eval :=
  ⟨fun _ _ hmem => mem_support_dynParLazy_init_touched_card_le _ dynTouchProg_bounded hmem,
   eval_run_dynParLazy_eq_parFin _ 3 dynTouchProg_bounded⟩

/-- Transcript-level bound witness: any supported transcript of `dynTouchProg` against an
arbitrary stateful oracle touches a `Finset ℕ` of cardinality at most `3`. -/
theorem dynTouchProg_transcript_card_le {State : Type}
    (oracle : (q : ℕ ⊕ (ℕ × ((Fin 2 × Bool) ⊕ RoutedNetQ 2 Bool Unit))) →
      StateT State PMF _)
    {s s' : State} {res : Option Bool × Option Bool}
    {t : OracleComp.Transcript (probOracleSpec (dynSessionSpec ℕ
      (protocolSpec 2 Bool Bool (RoutedNetQ 2 Bool Unit) (RoutedNetR Bool Unit))))}
    (hmem : (res, s', t) ∈
      ((OracleComp.interpret (OracleComp.withTranscript oracle)
        dynTouchProg).run (s, [])).support) :
    (touchedSessions t).card ≤ 3 :=
  touchedSessions_transcript_card_le dynTouchProg_bounded oracle hmem

/-! ### Single-session realization and dynamic-SID UC composition witness -/

private abbrev faultyR (C : Finset (Fin 2)) (κ : ℕ) := corruptRouter C (faultyLatch κ C)
private abbrev idealR (C : Finset (Fin 2)) (κ : ℕ) := corruptRouter C (idealLatch.toProtocol κ C)

private theorem advantage_corruptRouter_faulty_ideal_le (C : Finset (Fin 2)) (κ q : ℕ)
    (prog : ProbOracleComp (protocolSpec 2 Bool Bool (RoutedNetQ 2 Bool Unit)
      (RoutedNetR Bool Unit)) Bool) (hq : OracleComp.IsQueryBounded prog q) (s : LatchState) :
    Game.advantage (Prod.fst <$> Machine.closeProgram ((faultyR C κ).runFrom prog s)).eval
        (Prod.fst <$> Machine.closeProgram ((idealR C κ).runFrom prog s)).eval ≤
      (q : ℝ≥0) * ((1 : ℝ≥0) / 2 ^ (κ + 1)) := by
  induction hq generalizing s with
  | pure a _ =>
    simp only [faultyR, idealR, corruptRouter, faultyLatch, idealLatch,
      IdealFunctionality.toProtocol, Machine.runFrom_pure, Machine.closeProgram_pure,
      Game.advantage_self]
    exact zero_le
  | liftBind e cont n _ ih =>
    change Game.advantage (Prod.fst <$> Machine.closeProgram ((faultyR C κ).runFrom
      (OracleComp.query e >>= cont) s)).eval (Prod.fst <$> Machine.closeProgram
      ((idealR C κ).runFrom (OracleComp.query e >>= cont) s)).eval ≤ _
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      show (faultyR C κ).runFrom (OracleComp.query e >>= cont) s = (faultyR C κ).runFrom
        (OracleComp.query e) s >>= fun x => (faultyR C κ).runFrom (cont x.1) x.2 by
        dsimp only [faultyR, corruptRouter, faultyLatch]; rw [Machine.runFrom_bind],
      show (idealR C κ).runFrom (OracleComp.query e >>= cont) s = (idealR C κ).runFrom
        (OracleComp.query e) s >>= fun x => (idealR C κ).runFrom (cont x.1) x.2 by
        dsimp only [idealR, corruptRouter, idealLatch, IdealFunctionality.toProtocol]
        rw [Machine.runFrom_bind]]
    have hstep : ∀ {α : Type} (out : Option Bool → α) (pb : Fin 2 × Bool) (k : α × LatchState →
        ProbOracleComp _ Bool), (∀ x, Game.advantage (Prod.fst <$> Machine.closeProgram
          ((faultyR C κ).runFrom (k x) x.2)).eval (Prod.fst <$> Machine.closeProgram
          ((idealR C κ).runFrom (k x) x.2)).eval ≤ (n : ℝ≥0) * ((1 : ℝ≥0) / 2 ^ (κ + 1))) →
        Game.advantage (Prod.fst <$> Machine.closeProgram (ProbOracleComp.sample (ProbComp.unifFin
          (2 ^ (κ + 1) - 1)) >>= fun r => let x := (out (latchStep (if r.val = 0 then !pb.2
            else pb.2) s).1, (latchStep (if r.val = 0 then !pb.2 else pb.2) s).2)
          (faultyR C κ).runFrom (k x) x.2)).eval (Prod.fst <$> Machine.closeProgram
          ((idealR C κ).runFrom (k (out (latchStep pb.2 s).1, (latchStep pb.2 s).2))
          (latchStep pb.2 s).2)).eval ≤
          (n : ℝ≥0) * ((1 : ℝ≥0) / 2 ^ (κ + 1)) + (1 : ℝ≥0) / 2 ^ (κ + 1) := by
      intro α out pb k hk
      let mid : Game := (Prod.fst <$> Machine.closeProgram ((faultyR C κ).runFrom
        (k (out (latchStep pb.2 s).1, (latchStep pb.2 s).2)) (latchStep pb.2 s).2)).eval
      refine (Game.advantage_triangle _ mid _).trans ?_
      rw [add_comm ((n : ℝ≥0) * _)]
      refine add_le_add ?_ (hk (out (latchStep pb.2 s).1, (latchStep pb.2 s).2))
      simp only [Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_map,
        map_bind, ProbComp.eval_bind, ProbComp.eval_unifFin]
      refine (Game.advantage_bind_uniformOfFintype_of_ne_le 0 _ mid fun r hr => ?_).trans_eq ?_
      · have hne : r.val ≠ 0 := by simpa using Fin.val_ne_of_ne hr
        dsimp only [mid]
        simp only [hne, ↓reduceIte, ProbComp.eval_map]
      · simp [Fintype.card_fin, Nat.sub_add_cancel (Nat.one_le_pow (κ + 1) 2 (by decide)),
          one_div]
    cases e with
    | inl k =>
      rw [show ((faultyR C κ).runFrom (OracleComp.query (.inl k)) s >>= fun x =>
          (faultyR C κ).runFrom (cont x.1) x.2) = ProbOracleComp.sample (ProbComp.unifFin k) >>=
          fun a => (faultyR C κ).runFrom (cont a) s by
          dsimp only [faultyR, corruptRouter, faultyLatch]
          rw [Machine.runFrom_call]
          simp [Machine.handler, StateT.run_lift, bind_pure_comp, bind_map_left],
        show ((idealR C κ).runFrom (OracleComp.query (.inl k)) s >>= fun x =>
          (idealR C κ).runFrom (cont x.1) x.2) = ProbOracleComp.sample (ProbComp.unifFin k) >>=
          fun a => (idealR C κ).runFrom (cont a) s by
          dsimp only [idealR, corruptRouter, idealLatch, IdealFunctionality.toProtocol]
          rw [Machine.runFrom_call]
          simp [Machine.handler, StateT.run_lift, bind_pure_comp, bind_map_left]]
      simp only [Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_map,
        map_bind, ProbComp.eval_bind]
      refine Game.advantage_bind_le_nnreal _ _ _ fun a => ?_
      simpa [ProbComp.eval_map] using
        (ih a s).trans (le_add_of_nonneg_right (by positivity : (0 : ℝ≥0) ≤ 1 / 2 ^ (κ + 1)))
    | inr eq =>
      change Game.advantage (Prod.fst <$> Machine.closeProgram ((faultyR C κ).runFrom
        (ProbOracleComp.query eq) s >>= fun x => (faultyR C κ).runFrom (cont x.1) x.2)).eval
        (Prod.fst <$> Machine.closeProgram ((idealR C κ).runFrom (ProbOracleComp.query eq) s >>=
        fun x => (idealR C κ).runFrom (cont x.1) x.2)).eval ≤ _
      rcases eq with pb | (pb | u)
      · by_cases hC : pb.1 ∈ C
        · simp only [faultyR, idealR, corruptRouter, faultyLatch, idealLatch,
            IdealFunctionality.toProtocol, Machine.runFrom_query, hC, ↓reduceIte, StateT.run]
          exact (ih none s).trans (le_add_of_nonneg_right (by positivity))
        · simp only [faultyR, idealR, corruptRouter, faultyLatch, idealLatch,
            IdealFunctionality.toProtocol, Machine.runFrom_query, hC, ↓reduceIte, StateT.run,
            bind_pure_comp, bind_map_left, ProbOracleComp.sample_pure, pure_bind]
          exact hstep id pb (fun x => cont x.1) fun x => ih x.1 x.2
      · by_cases hC : pb.1 ∈ C
        · simp only [faultyR, idealR, corruptRouter, faultyLatch, idealLatch,
            IdealFunctionality.toProtocol, Machine.runFrom_query, hC, ↓reduceIte, StateT.run,
            bind_pure_comp, ProbOracleComp.sample_pure]
          exact hstep Sum.inl pb (fun x => cont x.1) fun x => ih x.1 x.2
        · simp only [faultyR, idealR, corruptRouter, faultyLatch, idealLatch,
            IdealFunctionality.toProtocol, Machine.runFrom_query, hC, ↓reduceIte, StateT.run]
          exact (ih (.inl none) s).trans (le_add_of_nonneg_right (by positivity))
      · simp only [faultyR, idealR, corruptRouter, faultyLatch, idealLatch,
          IdealFunctionality.toProtocol, Machine.runFrom_query, StateT.run,
          ProbOracleComp.sample_pure]
        exact (ih (.inr ()) s).trans (le_add_of_nonneg_right (by positivity))

private theorem faultyLatch_emulatesDummyWithin :
    EmulatesDummyWithin faultyLatch idealLatch.toProtocol 1
      (fun pZ κ => ((pZ.eval κ : ℕ) : ℝ≥0) / 2 ^ (κ + 1)) := by
  refine ⟨dummyAdversary 2 _ _, dummyAdversary_polyBounded 2 _ _, fun C Z pZ hZ κ z => ?_⟩
  simp only [advantage, exec_dummyAdversary, Machine.run, Machine.link, corruptRouter, faultyLatch,
    idealLatch, IdealFunctionality.toProtocol, ProbOracleComp.sample_pure, pure_bind,
    Machine.closeProgram_map]
  exact (advantage_corruptRouter_faulty_ideal_le C κ (pZ.eval κ) (Z κ z) (hZ κ z)
    { last := none }).trans (le_of_eq (by simp [div_eq_mul_inv]))

private theorem faultyLatch_realizes : Realizes faultyLatch idealLatch := by
  refine faultyLatch_emulatesDummyWithin.emulatesWithin.emulates fun pA pZ => ?_
  have hneg : Negligible fun κ => (((absorbPoly pZ pA).eval κ : ℕ) : ℝ≥0) * ((2⁻¹ : ℝ≥0) ^ κ) := by
    negligible
  intro k
  simpa [div_eq_mul_inv, pow_succ, mul_inv, mul_left_comm, mul_comm, mul_assoc] using
    (hneg k).const_mul (2⁻¹ : ℝ≥0)

/-- Asymptotic dynamic-SID UC composition over `SID = ℕ`. -/
theorem composeDyn_dynChooseOuter_realizes :
    Emulates (composeDyn dynChooseOuter faultyLatch)
      (composeDyn dynChooseOuter idealLatch.toProtocol) :=
  Realizes.composeDyn dynChooseOuter_polyBounded faultyLatch_polyBounded idealLatch_polyBounded
    faultyLatch_realizes

/-- Concrete dynamic-SID composition via `EmulatesDummyWithin.composeDyn`. -/
theorem composeDyn_dynChooseOuter_emulatesDummyWithin :
    EmulatesDummyWithin (composeDyn dynChooseOuter faultyLatch)
      (composeDyn dynChooseOuter idealLatch.toProtocol) (2 * 1 + 1)
      (fun pZ κ => ((absorbPoly pZ 3).eval κ + 1) •
        ((((dynSessionHopPoly pZ 3 1 1 1).eval κ : ℕ) : ℝ≥0) / 2 ^ (κ + 1))) :=
  EmulatesDummyWithin.composeDyn dynChooseOuter_polyBounded faultyLatch_polyBounded
    idealLatch_polyBounded faultyLatch_emulatesDummyWithin

/-- Non-vacuity witness at `κ = 0`, `baseSid = 500`, `C = ∅` and `C = {0}`:
dynamically chosen sessions `1000` and `1001 + c.val` yield distinguishing advantage `3 / 4 > 0`. -/
theorem composeDyn_nonvacuity (C : Finset (Fin 2)) (p : Fin 2) (hp : p ∉ C) (baseSid : ℕ) :
    let adv := advantage (composeDyn dynChooseOuter faultyLatch)
      (composeDyn dynChooseOuter idealLatch.toProtocol)
      (dummyAdversary 2 _ _) (dynHybridSim (SID := ℕ) (dummyAdversary 2 _ _))
      C (zDyn p baseSid) 0 []
    adv = 3 / 4 ∧ (1 / 2 : ℝ≥0) < adv := by
  have hne : ∀ c : Fin 2, 2 * baseSid + 1 + c.val ≠ 2 * baseSid := fun c => by omega
  have habs : absorbDynHybrid C dynChooseOuter (zDyn p baseSid) 0 [] =
      ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
        ProbOracleComp.query (2 * baseSid, Sum.inl (p, true)) >>= fun x₀ =>
          ProbOracleComp.query (2 * baseSid + 1 + c.val, Sum.inl (p, true)) >>= fun x₁ =>
            pure (!(x₀.getD false && x₁.getD false)) := by
    dsimp only [absorbDynHybrid, zDyn, dynChooseOuter, Machine.link, routeCorrupt, dynHybridWrap]
    rw [ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [StateT.run]
    simp only [hp, ↓reduceIte, Machine.runFrom_pure, map_bind, map_pure]
    rw [liftDynParty]
    erw [OracleComp.interpret_bind, ProbOracleComp.interpret_sample]
    rw [bind_assoc]
    refine congrArg (Bind.bind (ProbOracleComp.sample (ProbComp.unifFin 1))) (funext fun c => ?_)
    erw [OracleComp.interpret_bind, OracleComp.interpret_query]
    change (ProbOracleComp.query (2 * baseSid, Sum.inl (p, true)) >>= _) = _
    refine congrArg (Bind.bind (ProbOracleComp.query (2 * baseSid, Sum.inl (p, true))))
      (funext fun x₀ => ?_)
    change (ProbOracleComp.query (2 * baseSid + 1 + c.val, Sum.inl (p, true)) >>= _) = _
    refine congrArg
      (Bind.bind (ProbOracleComp.query (2 * baseSid + 1 + c.val, Sum.inl (p, true))))
      (funext fun x₁ => ?_)
    simp only [Option.getD_some]
  have hlink_adv :
      (liftAdversary (n := 2) (In := ℕ × Bool) (Out := Bool)
        (dynHybridSimMachine (dummyAdversary 2 _ _ 0 C))).link (zDyn p baseSid 0 []) =
        zDyn p baseSid 0 [] := by
    dsimp only [zDyn, Machine.link, liftAdversary, Machine.liftRight, dynHybridSimMachine]
    rw [ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
    simp only [StateT.run_lift, Machine.runFrom_pure, bind_assoc, pure_bind, map_bind, map_pure]
  have hexec_ideal :
      (exec (composeDyn dynChooseOuter idealLatch.toProtocol)
        (dynHybridSim (SID := ℕ) (dummyAdversary 2 _ _)) C (zDyn p baseSid) 0 []).eval =
        PMF.pure false := by
    have hrun :
        exec (composeDyn dynChooseOuter idealLatch.toProtocol)
          (dynHybridSim (SID := ℕ) (dummyAdversary 2 _ _)) C (zDyn p baseSid) 0 [] =
          (dynSessionRouter (SID := ℕ) C (idealLatch.toProtocol 0 C)).run
            (absorbDynHybrid C dynChooseOuter (zDyn p baseSid) 0 []) := by
      dsimp only [exec, execMachine, composeDyn, dynHybridSim, absorbDynHybrid]
      rw [corruptRouter_comp, Machine.run_comp, Machine.run_comp, hlink_adv]
    rw [hrun, habs]
    simp only [Machine.run, Machine.link, dynSessionRouter, dynParLazy, corruptRouter,
      idealLatch, IdealFunctionality.toProtocol, latchStep,
      Machine.runFrom_bind, Machine.runFrom_sample, Machine.runFrom_query, Machine.runFrom_pure,
      ProbOracleComp.sample_pure, pure_bind, StateT.run, hp, ↓reduceIte,
      map_bind, map_pure, Machine.closeProgram_bind, Machine.closeProgram_map,
      Machine.closeProgram_sample, Machine.closeProgram_pure, ProbComp.eval_bind,
      ProbComp.eval_map, ProbComp.eval_pure, ProbComp.eval_unifFin, PMF.bind_map,
      PMF.pure_bind, Function.comp_def]
    refine Eq.trans (congrArg (Probability.PMF.uniformOfFintype (Fin 2)).bind (funext fun c => by
      simp only [Function.update_of_ne (hne c), Machine.closeProgram_pure, ProbComp.eval_pure,
        PMF.pure_bind, Option.getD_some, Bool.and_self, Bool.not_true])) (PMF.bind_const _ _)
  have hexec_real :
      (exec (composeDyn dynChooseOuter faultyLatch)
        (dummyAdversary 2 _ _) C (zDyn p baseSid) 0 []).eval =
        (Probability.PMF.uniformOfFintype (Fin 2)).bind fun _ =>
        (Probability.PMF.uniformOfFintype (Fin 2)).bind fun r₀ =>
        (Probability.PMF.uniformOfFintype (Fin 2)).bind fun r₁ =>
          PMF.pure (!(decide (r₀.val ≠ 0) && decide (r₁.val ≠ 0))) := by
    rw [exec_composeDyn_dummy, habs]
    simp only [Machine.run, Machine.link, dynSessionRouter, dynParLazy, corruptRouter,
      faultyLatch, latchStep,
      Machine.runFrom_bind, Machine.runFrom_sample, Machine.runFrom_query, Machine.runFrom_pure,
      ProbOracleComp.sample_pure, pure_bind, StateT.run, hp, ↓reduceIte,
      map_bind, map_pure, Machine.closeProgram_bind, Machine.closeProgram_map,
      Machine.closeProgram_sample, Machine.closeProgram_pure, ProbComp.eval_bind,
      ProbComp.eval_map, ProbComp.eval_pure, ProbComp.eval_unifFin, PMF.bind_map,
      PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    refine congrArg (Probability.PMF.uniformOfFintype (Fin 2)).bind (funext fun c => ?_)
    refine congrArg (Probability.PMF.uniformOfFintype (Fin 2)).bind (funext fun r₀ => ?_)
    simp only [Function.update_of_ne (hne c), Machine.closeProgram_bind,
      Machine.closeProgram_sample, Machine.closeProgram_pure, ProbComp.eval_bind,
      ProbComp.eval_pure, ProbComp.eval_unifFin, PMF.bind_bind, PMF.pure_bind]
    refine congrArg (Probability.PMF.uniformOfFintype (Fin 2)).bind (funext fun r₁ => ?_)
    cases r₀ using Fin.cases with
    | zero =>
      cases r₁ using Fin.cases with
      | zero => rfl
      | succ j₁ => fin_cases j₁; rfl
    | succ j₀ =>
      fin_cases j₀
      cases r₁ using Fin.cases with
      | zero => rfl
      | succ j₁ => fin_cases j₁; rfl
  have hid : (exec (composeDyn dynChooseOuter idealLatch.toProtocol)
      (dynHybridSim (SID := ℕ) (dummyAdversary 2 _ _)) C (zDyn p baseSid) 0 []).eval true = 0 := by
    rw [hexec_ideal]
    simp [PMF.pure_apply]
  have hreal : (exec (composeDyn dynChooseOuter faultyLatch)
      (dummyAdversary 2 _ _) C (zDyn p baseSid) 0 []).eval true = 3 / 4 := by
    rw [hexec_real]
    simp only [PMF.bind_apply, PMF.bind_const, Probability.PMF.uniformOfFintype_apply,
      Fintype.card_fin, Nat.cast_ofNat, tsum_fintype]
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, ne_eq, not_true_eq_false, decide_false,
      one_ne_zero, not_false_eq_true, decide_true, Bool.false_and, Bool.not_false, Bool.true_and,
      Bool.not_true, PMF.pure_apply, ↓reduceIte, Bool.true_eq_false, mul_one, mul_zero, add_zero]
    rw [ENNReal.inv_two_add_inv_two, mul_one]
    simpa [ENNReal.coe_div] using congrArg ((↑) : ℝ≥0 → ENNReal)
      (by norm_num : (2⁻¹ + 2⁻¹ * 2⁻¹ : ℝ≥0) = 3 / 4)
  have hadv : advantage (composeDyn dynChooseOuter faultyLatch)
      (composeDyn dynChooseOuter idealLatch.toProtocol)
      (dummyAdversary 2 _ _) (dynHybridSim (SID := ℕ) (dummyAdversary 2 _ _))
      C (zDyn p baseSid) 0 [] = 3 / 4 := by
    simp only [advantage, Game.advantage, Game.succProbability, hid, hreal, ENNReal.toNNReal_div,
      ENNReal.toNNReal_ofNat]
    norm_num
  exact ⟨hadv, by rw [hadv]; norm_num⟩

example : advantage (composeDyn dynChooseOuter faultyLatch)
    (composeDyn dynChooseOuter idealLatch.toProtocol)
    (dummyAdversary 2 _ _) (dynHybridSim (SID := ℕ) (dummyAdversary 2 _ _))
    ∅ (zDyn 0 500) 0 [] = 3 / 4 :=
  (composeDyn_nonvacuity ∅ 0 (by simp) 500).1

example : advantage (composeDyn dynChooseOuter faultyLatch)
    (composeDyn dynChooseOuter idealLatch.toProtocol)
    (dummyAdversary 2 _ _) (dynHybridSim (SID := ℕ) (dummyAdversary 2 _ _))
    {0} (zDyn 1 500) 0 [] = 3 / 4 :=
  (composeDyn_nonvacuity {0} 1 (by simp) 500).1

end CslibFrontierTests.Crypto.UCDynamicMultiSession
