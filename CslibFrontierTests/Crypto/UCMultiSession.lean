/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Protocols.UC.MultiSession
import CslibFrontier.Tactic.Negligible

/-! # Multi-session UC composition tests -/
namespace CslibFrontierTests.Crypto.UCMultiSession
open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.UC
open OracleComp (IsCostBounded)
open scoped NNReal

/-- Per-session state tracking the last latched `true` value. -/
structure RelayState : Type where
  /-- Last latched Boolean output (`some true` once triggered). -/
  last : Option Bool := none
  deriving DecidableEq

private def relayStep (b : Bool) (s : RelayState) : Option Bool × RelayState :=
  if b then (some true, { last := some true }) else (s.last, s)

/-- Ideal relay (`n = 2` parties): `b = true` latches `some true`; `b = false` reads `s.last`. -/
def idealRelay : IdealFunctionality 2 Bool Bool Unit Unit where
  State := RelayState; init := fun _ _ => pure { last := none }
  onInput := fun _ b s => pure (relayStep b s); onBackdoor := fun () s => pure ((), s)

/-- Faulty relay (`n = 2` parties): flips each party input `b` with prob `1 / 2 ^ (κ + 1)`. -/
def faultyRelay : Protocol 2 Bool Bool Unit Unit := fun κ _ =>
  { State := RelayState, init := pure { last := none }, handle
      | .inl (_, b) => fun s => ProbOracleComp.sample (ProbComp.unifFin (2 ^ (κ + 1) - 1)) >>=
          fun r => pure (relayStep (if r.val = 0 then !b else b) s)
      | .inr () => fun s => pure ((), s) }

/-- Two-session outer hybrid (`m = 2, n = 2`) returning the conjunction of both sessions. -/
def orOuter : MultiHybridProtocol 2 2 Bool Bool Unit Unit Bool Bool := fun _ _ =>
  { State := Unit, init := pure (), handle
      | .inl (p, b) => fun s => ProbOracleComp.query ⟨0, p, b⟩ >>= fun x₀ =>
          ProbOracleComp.query ⟨1, p, b⟩ >>= fun x₁ =>
            pure (some (x₀.getD false && x₁.getD false), s)
      | .inr () => fun s => pure ((), s) }

/-- Distinguisher activating party `p` with `true` and checking if conjunction dropped. -/
def zOr (p : Fin 2) : Environment 2 Bool Bool
    (RoutedNetQ 2 Bool (MultiNetQ 2 Unit (RoutedNetQ 2 Bool Unit)))
    (RoutedNetR Bool (Unit ⊕ RoutedNetR Bool Unit)) := fun _ _ =>
  ProbOracleComp.query (Sum.inl (p, true)) >>= fun res => pure (!(res.getD false))

theorem idealRelay_polyBounded : idealRelay.toProtocol.PolyBounded 1 := fun _ _ =>
  ⟨(IsCostBounded.pure _ 0).mono (by simp),
    fun q _ => by cases q <;> exact (IsCostBounded.pure _ 0).mono (by simp)⟩

theorem faultyRelay_polyBounded : faultyRelay.PolyBounded 1 := fun κ _ =>
  ⟨(IsCostBounded.pure _ 0).mono (by simp), fun q _ => by cases q with
    | inl _ => exact ((Machine.isQueryBounded_sample (IsCostBounded.query (2 ^ (κ + 1) - 1))).bind
        fun _ => IsCostBounded.pure _ 0).mono (by simp)
    | inr _ => exact (IsCostBounded.pure _ 0).mono (by simp)⟩

theorem orOuter_polyBounded : orOuter.PolyBounded 2 := fun _ _ =>
  ⟨(IsCostBounded.pure _ 0).mono (by simp), fun q _ => by cases q with
    | inl pb => exact ((IsCostBounded.query (Sum.inr (⟨0, pb.1, pb.2⟩ : SubSessionCall 2 2 Bool)))
        |>.bind fun _ => (IsCostBounded.query (Sum.inr (⟨1, pb.1, pb.2⟩ : SubSessionCall 2 2 Bool)))
        |>.bind fun _ => IsCostBounded.pure _ 0).mono (by simp)
    | inr _ => exact (IsCostBounded.pure _ 0).mono (by simp)⟩

theorem zOr_polyBounded (p : Fin 2) : (zOr p).PolyBounded 1 := fun _ _ =>
  ((IsCostBounded.query (Sum.inr (Sum.inl (p, true)))).bind fun _ =>
    IsCostBounded.pure _ 0).mono (by simp)

/-- State-isolation test: writing `true` in session `0` leaves session `1` at `none`. -/
example : ((sessionRouter (∅ : Finset (Fin 2)) (fun _ => idealRelay.toProtocol 0 ∅)).run do
      let _ ← ProbOracleComp.query ((0 : Fin 2), Sum.inl ((0 : Fin 2), true))
      let r₁ ← ProbOracleComp.query ((1 : Fin 2), Sum.inl ((0 : Fin 2), false))
      let r₀ ← ProbOracleComp.query ((0 : Fin 2), Sum.inl ((0 : Fin 2), false))
      pure (r₁, r₀)).eval = PMF.pure (none, some true) := by
  simp only [Machine.run, Machine.link, sessionRouter, corruptRouter, idealRelay,
    IdealFunctionality.toProtocol, relayStep, SSP.parFin, Machine.runFrom_bind,
    Machine.runFrom_query, Machine.closeProgram_map, Machine.closeProgram_bind, OracleComp.pi,
    pure_bind, ProbComp.eval_map, ProbComp.eval_bind]
  simp [StateT.run, ProbOracleComp.sample_pure, Machine.runFrom_pure, Machine.closeProgram_pure,
    ProbComp.eval_pure, Fin.cons_zero, Function.update_self, Function.update_of_ne]

private abbrev faultyR (C : Finset (Fin 2)) (κ : ℕ) := corruptRouter C (faultyRelay κ C)
private abbrev idealR (C : Finset (Fin 2)) (κ : ℕ) := corruptRouter C (idealRelay.toProtocol κ C)

private theorem advantage_corruptRouter_faulty_ideal_le (C : Finset (Fin 2)) (κ q : ℕ)
    (prog : ProbOracleComp (protocolSpec 2 Bool Bool (RoutedNetQ 2 Bool Unit)
      (RoutedNetR Bool Unit)) Bool) (hq : OracleComp.IsQueryBounded prog q) (s : RelayState) :
    Game.advantage (Prod.fst <$> Machine.closeProgram ((faultyR C κ).runFrom prog s)).eval
        (Prod.fst <$> Machine.closeProgram ((idealR C κ).runFrom prog s)).eval ≤
      (q : ℝ≥0) * ((1 : ℝ≥0) / 2 ^ (κ + 1)) := by
  induction hq generalizing s with
  | pure a _ =>
    simp only [faultyR, idealR, corruptRouter, faultyRelay, idealRelay,
      IdealFunctionality.toProtocol, Machine.runFrom_pure, Machine.closeProgram_pure,
      Game.advantage_self]; exact zero_le
  | liftBind e cont n _ ih =>
    change Game.advantage (Prod.fst <$> Machine.closeProgram ((faultyR C κ).runFrom
      (OracleComp.query e >>= cont) s)).eval (Prod.fst <$> Machine.closeProgram
      ((idealR C κ).runFrom (OracleComp.query e >>= cont) s)).eval ≤ _
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      show (faultyR C κ).runFrom (OracleComp.query e >>= cont) s = (faultyR C κ).runFrom
        (OracleComp.query e) s >>= fun x => (faultyR C κ).runFrom (cont x.1) x.2 by
        dsimp only [faultyR, corruptRouter, faultyRelay]; rw [Machine.runFrom_bind],
      show (idealR C κ).runFrom (OracleComp.query e >>= cont) s = (idealR C κ).runFrom
        (OracleComp.query e) s >>= fun x => (idealR C κ).runFrom (cont x.1) x.2 by
        dsimp only [idealR, corruptRouter, idealRelay, IdealFunctionality.toProtocol]
        rw [Machine.runFrom_bind]]
    have hstep : ∀ {α : Type} (out : Option Bool → α) (pb : Fin 2 × Bool) (k : α × RelayState →
        ProbOracleComp _ Bool), (∀ x, Game.advantage (Prod.fst <$> Machine.closeProgram
          ((faultyR C κ).runFrom (k x) x.2)).eval (Prod.fst <$> Machine.closeProgram
          ((idealR C κ).runFrom (k x) x.2)).eval ≤ (n : ℝ≥0) * ((1 : ℝ≥0) / 2 ^ (κ + 1))) →
        Game.advantage (Prod.fst <$> Machine.closeProgram (ProbOracleComp.sample (ProbComp.unifFin
          (2 ^ (κ + 1) - 1)) >>= fun r => let x := (out (relayStep (if r.val = 0 then !pb.2
            else pb.2) s).1, (relayStep (if r.val = 0 then !pb.2 else pb.2) s).2)
          (faultyR C κ).runFrom (k x) x.2)).eval (Prod.fst <$> Machine.closeProgram
          ((idealR C κ).runFrom (k (out (relayStep pb.2 s).1, (relayStep pb.2 s).2))
          (relayStep pb.2 s).2)).eval ≤
          (n : ℝ≥0) * ((1 : ℝ≥0) / 2 ^ (κ + 1)) + (1 : ℝ≥0) / 2 ^ (κ + 1) := by
      intro α out pb k hk
      let mid : Game := (Prod.fst <$> Machine.closeProgram ((faultyR C κ).runFrom
        (k (out (relayStep pb.2 s).1, (relayStep pb.2 s).2)) (relayStep pb.2 s).2)).eval
      refine (Game.advantage_triangle _ mid _).trans ?_; rw [add_comm ((n : ℝ≥0) * _)]
      refine add_le_add ?_ (hk (out (relayStep pb.2 s).1, (relayStep pb.2 s).2))
      simp only [Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_map,
        map_bind, ProbComp.eval_bind, ProbComp.eval_unifFin]
      refine (Game.advantage_bind_uniformOfFintype_of_ne_le 0 _ mid fun r hr => ?_).trans_eq ?_
      · have hne : r.val ≠ 0 := by simpa using Fin.val_ne_of_ne hr
        dsimp only [mid]; simp only [hne, ↓reduceIte, ProbComp.eval_map]
      · simp [Fintype.card_fin, Nat.sub_add_cancel (Nat.one_le_pow (κ + 1) 2 (by decide)),
          one_div]
    cases e with
    | inl k =>
      rw [show ((faultyR C κ).runFrom (OracleComp.query (.inl k)) s >>= fun x =>
          (faultyR C κ).runFrom (cont x.1) x.2) = ProbOracleComp.sample (ProbComp.unifFin k) >>=
          fun a => (faultyR C κ).runFrom (cont a) s by
          dsimp only [faultyR, corruptRouter, faultyRelay]; rw [Machine.runFrom_call]
          simp [Machine.handler, StateT.run_lift, bind_pure_comp, bind_map_left],
        show ((idealR C κ).runFrom (OracleComp.query (.inl k)) s >>= fun x =>
          (idealR C κ).runFrom (cont x.1) x.2) = ProbOracleComp.sample (ProbComp.unifFin k) >>=
          fun a => (idealR C κ).runFrom (cont a) s by
          dsimp only [idealR, corruptRouter, idealRelay, IdealFunctionality.toProtocol]
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
        · simp only [faultyR, idealR, corruptRouter, faultyRelay, idealRelay,
            IdealFunctionality.toProtocol, Machine.runFrom_query, hC, ↓reduceIte, StateT.run]
          exact (ih none s).trans (le_add_of_nonneg_right (by positivity))
        · simp only [faultyR, idealR, corruptRouter, faultyRelay, idealRelay,
            IdealFunctionality.toProtocol, Machine.runFrom_query, hC, ↓reduceIte, StateT.run,
            bind_pure_comp, bind_map_left, ProbOracleComp.sample_pure, pure_bind]
          exact hstep id pb (fun x => cont x.1) fun x => ih x.1 x.2
      · by_cases hC : pb.1 ∈ C
        · simp only [faultyR, idealR, corruptRouter, faultyRelay, idealRelay,
            IdealFunctionality.toProtocol, Machine.runFrom_query, hC, ↓reduceIte, StateT.run,
            bind_pure_comp, ProbOracleComp.sample_pure]
          exact hstep Sum.inl pb (fun x => cont x.1) fun x => ih x.1 x.2
        · simp only [faultyR, idealR, corruptRouter, faultyRelay, idealRelay,
            IdealFunctionality.toProtocol, Machine.runFrom_query, hC, ↓reduceIte, StateT.run]
          exact (ih (.inl none) s).trans (le_add_of_nonneg_right (by positivity))
      · simp only [faultyR, idealR, corruptRouter, faultyRelay, idealRelay,
          IdealFunctionality.toProtocol, Machine.runFrom_query, StateT.run,
          ProbOracleComp.sample_pure]
        exact (ih (.inr ()) s).trans (le_add_of_nonneg_right (by positivity))

theorem faultyRelay_emulatesDummyWithin : EmulatesDummyWithin faultyRelay idealRelay.toProtocol 1
    (fun pZ κ => ((pZ.eval κ : ℕ) : ℝ≥0) / 2 ^ (κ + 1)) := by
  refine ⟨dummyAdversary 2 _ _, dummyAdversary_polyBounded 2 _ _, fun C Z pZ hZ κ z => ?_⟩
  simp only [advantage, exec_dummyAdversary, Machine.run, Machine.link, corruptRouter, faultyRelay,
    idealRelay, IdealFunctionality.toProtocol, ProbOracleComp.sample_pure, pure_bind,
    Machine.closeProgram_map]
  exact (advantage_corruptRouter_faulty_ideal_le C κ (pZ.eval κ) (Z κ z) (hZ κ z)
    { last := none }).trans (le_of_eq (by simp [div_eq_mul_inv]))

theorem faultyRelay_realizes : Realizes faultyRelay idealRelay := by
  refine faultyRelay_emulatesDummyWithin.emulatesWithin.emulates fun pA pZ => ?_
  have hneg : Negligible fun κ => (((absorbPoly pZ pA).eval κ : ℕ) : ℝ≥0) * ((2⁻¹ : ℝ≥0) ^ κ) := by
    negligible
  intro k; simpa [div_eq_mul_inv, pow_succ, mul_inv, mul_left_comm, mul_comm, mul_assoc] using
    (hneg k).const_mul (2⁻¹ : ℝ≥0)

/-- Multi-session composition (`m = 2, n = 2`) for `orOuter` and `faultyRelay` vs `idealRelay`. -/
theorem composeMulti_orOuter_realizes :
    Emulates (composeMulti orOuter faultyRelay) (composeMulti orOuter idealRelay.toProtocol) :=
  Realizes.composeMulti orOuter_polyBounded faultyRelay_polyBounded idealRelay_polyBounded
    faultyRelay_realizes

/-- `EmulatesDummyWithin.composeMulti` at `m = 2`, with its explicit `2 • ε` bound. -/
theorem composeMulti_orOuter_emulatesDummyWithin :
    EmulatesDummyWithin (composeMulti orOuter faultyRelay)
      (composeMulti orOuter idealRelay.toProtocol) (Polynomial.C 2 * 1 + 1) (fun pZ κ =>
        2 • ((((sessionHopPoly 2 pZ 2 1 1 1).eval κ : ℕ) : ℝ≥0) / 2 ^ (κ + 1))) := by
  -- Elaborate without the expected type to avoid a whnf timeout unifying `m • ε` at `m = 2`.
  have h := EmulatesDummyWithin.composeMulti orOuter_polyBounded faultyRelay_polyBounded
    idealRelay_polyBounded faultyRelay_emulatesDummyWithin
  exact h

/-- Non-vacuity witness at `κ = 0`, `C = ∅`, and `C = {0}`: `3 / 4 > 1 / 2` and `≤ 2 • (1 / 2)`. -/
theorem composeMulti_orOuter_nonvacuity (C : Finset (Fin 2)) (p : Fin 2) (hp : p ∉ C) :
    let adv := advantage (composeMulti orOuter faultyRelay) (composeMulti orOuter
      idealRelay.toProtocol) (dummyAdversary 2 _ _) (multiHybridSim fun _ => dummyAdversary 2 _ _)
      C (zOr p) 0 []
    adv = 3 / 4 ∧ (1 / 2 : ℝ≥0) < adv ∧ adv ≤ 2 • (1 / 2 : ℝ≥0) := by
  have habs : absorbMultiHybrid C orOuter (zOr p) 0 [] = (ProbOracleComp.query ((0 : Fin 2),
      Sum.inl (p, true)) >>= fun x₀ => ProbOracleComp.query ((1 : Fin 2), Sum.inl (p, true)) >>=
        fun x₁ => pure (!(x₀.getD false && x₁.getD false))) := by
    dsimp only [absorbMultiHybrid, zOr, orOuter, Machine.link, routeCorrupt, multiHybridWrap,
      liftMultiParty]
    rw [ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [StateT.run]; simp only [hp, ↓reduceIte, map_bind]
    erw [OracleComp.interpret_bind, OracleComp.interpret_query]
    dsimp only [OracleComp.sumHandler]; erw [bind_assoc]
  have hid : (exec (composeMulti orOuter idealRelay.toProtocol) (multiHybridSim
      fun _ => dummyAdversary 2 _ _) C (zOr p) 0 []).eval true = 0 := by
    rw [eval_exec_composeFamily_multiHybridSim, habs]
    dsimp only [Machine.run, Machine.link, SSP.parFin, execMachine, dummyAdversary, liftAdversary]
    rw [Machine.liftRight_id]
    simp only [Machine.comp, Machine.id, corruptRouter, idealRelay, IdealFunctionality.toProtocol,
      relayStep, hp, ↓reduceIte, OracleComp.pi, ProbOracleComp.sample_pure, StateT.run,
      StateT.run_lift, bind_pure_comp, Machine.runFrom_bind, Machine.runFrom_map,
      Machine.runFrom_query, map_pure, Machine.closeProgram_pure, ProbComp.eval_pure,
      Equiv.prodAssoc_apply, Prod.map_apply, id_eq, Function.update_of_ne (Fin.zero_ne_one.symm),
      Option.getD_some, Bool.and_self, Bool.not_true, PMF.pure_apply, Bool.true_eq_false]
  have hreal : (exec (composeMulti orOuter faultyRelay) (dummyAdversary 2 _ _) C (zOr p) 0 []).eval
      true = 3 / 4 := by
    rw [exec_composeFamily_dummy, habs]
    simp only [Machine.run, Machine.link, sessionRouter, corruptRouter, faultyRelay, relayStep,
      SSP.parFin, Machine.runFrom_bind, Machine.runFrom_map, Machine.runFrom_query, OracleComp.pi,
      ProbOracleComp.sample_pure, pure_bind, map_pure, map_bind, Functor.map_map, hp, ↓reduceIte,
      StateT.run, bind_pure_comp, Fin.cons_zero, bind_map_left, Machine.closeProgram_bind,
      Machine.closeProgram_map, Machine.closeProgram_sample, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_unifFin, Prod.map_apply, id_eq, Function.update_of_ne (Fin.zero_ne_one.symm)]
    trans (2 : ENNReal)⁻¹ * (2⁻¹ + 2⁻¹) + 2⁻¹ * 2⁻¹
    · simp only [PMF.bind_apply, PMF.map_apply, Probability.PMF.uniformOfFintype_apply,
        Fintype.card_fin, tsum_fintype]; simp [Fin.sum_univ_succ]
    · rw [ENNReal.inv_two_add_inv_two, mul_one]
      simpa [ENNReal.coe_div] using congrArg ((↑) : ℝ≥0 → ENNReal)
        (by norm_num : (2⁻¹ + 2⁻¹ * 2⁻¹ : ℝ≥0) = 3 / 4)
  have hadv : advantage (composeMulti orOuter faultyRelay) (composeMulti orOuter
      idealRelay.toProtocol) (dummyAdversary 2 _ _) (multiHybridSim fun _ => dummyAdversary 2 _ _)
      C (zOr p) 0 [] = 3 / 4 := by
    simp only [advantage, Game.advantage, Game.succProbability, hid, hreal, ENNReal.toNNReal_div,
      ENNReal.toNNReal_ofNat]; norm_num
  exact ⟨hadv, by rw [hadv]; norm_num, by rw [hadv, ← NNReal.coe_le_coe]; norm_num⟩

example : advantage (composeMulti orOuter faultyRelay) (composeMulti orOuter idealRelay.toProtocol)
    (dummyAdversary 2 _ _) (multiHybridSim fun _ => dummyAdversary 2 _ _) ∅ (zOr 0) 0 [] = 3 / 4 :=
  (composeMulti_orOuter_nonvacuity ∅ 0 (by simp)).1

example : advantage (composeMulti orOuter faultyRelay) (composeMulti orOuter idealRelay.toProtocol)
    (dummyAdversary 2 _ _) (multiHybridSim fun _ => dummyAdversary 2 _ _) {0} (zOr 1) 0 [] =
      3 / 4 :=
  (composeMulti_orOuter_nonvacuity {0} 1 (by simp)).1

end CslibFrontierTests.Crypto.UCMultiSession
