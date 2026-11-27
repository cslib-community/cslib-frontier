/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/
module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Protocols.UC.GlobalSetup
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm

/-!
# Tests for UC with Global Setup (EUC / GUC)

Checked witnesses exercising `CslibFrontier.Crypto.Protocols.UC.GlobalSetup`:
- Shared live `G` state across outer hybrid protocol and subroutine (`xorWithCoin` composed with
  `coinReaderProto` returns `true` with probability `1`, whereas composing `xorWithCoin` with
  `indepCoinFunc.toGlobalProtocol` returns `true` with probability `1/2`, separating the two and
  witnessing non-vacuity of `GEmulates.compose`).
- Concrete and asymptotic dummy-adversary completeness, transitivity, and composition instantiations
  and polynomial budget bounds.
- Local-vs-global non-programmability separation (`localCoinProto` UC-realizes `indepCoinFunc`
  with zero advantage, while `coinReaderProto` fails to GUC-realize `indepCoinFunc` against
  `coinSetup` with advantage `1/2` against every simulator).
-/

public section

namespace CslibFrontierTests.Crypto.UCGlobalSetup

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open scoped NNReal ENNReal

/-- A global hybrid protocol that queries both party `0` of its subroutine and `coinSetup` directly,
testing whether both returned the same bit. -/
def xorWithCoin :
    GlobalHybridProtocol 1 Unit Bool Unit Unit Unit Bool (netSpec Unit Bool) :=
  fun _ _ => {
    State := Unit
    init := pure ()
    handle
      | .inl (_, _) => StateT.lift (do
          let subOut ← ProbOracleComp.query
            (spec := partySpec 1 Unit Bool ⊕ₒ netSpec Unit Bool) (.inl ((0 : Fin 1), ()))
          let gBit ← ProbOracleComp.query
            (spec := partySpec 1 Unit Bool ⊕ₒ netSpec Unit Bool) (.inr ())
          return subOut.map (fun b => decide (b = gBit)))
      | .inr _ => pure () }

theorem xorWithCoin_polyBounded : xorWithCoin.PolyBounded 2 := fun _ _ => by
  rw [Polynomial.eval_ofNat]
  refine ⟨OracleComp.IsCostBounded.pure _ 2, fun q s => ?_⟩
  rcases q with p | _
  · dsimp only [xorWithCoin]
    erw [StateT.run_lift, bind_pure_comp]
    refine (OracleComp.isCostBounded_map_iff _ _ _).mpr ?_
    refine ((OracleComp.IsCostBounded.query _).bind fun _ =>
      ((OracleComp.IsCostBounded.query _).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0)).mono (by omega)
  · exact OracleComp.IsCostBounded.pure _ 2

theorem coinReaderProto_polyBounded : coinReaderProto.PolyBounded 1 := fun _ _ => by
  rw [Polynomial.eval_one]
  refine ⟨OracleComp.IsCostBounded.pure _ 1, fun q s => ?_⟩
  rcases q with p | _
  · dsimp only [coinReaderProto]
    erw [StateT.run_lift, bind_pure_comp, Functor.map_map]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
  · exact OracleComp.IsCostBounded.pure _ 1

/-- Environment polling party `0` once and checking whether the returned output equals `some true`.
-/
def askPartyG {AdvQ AdvR : Type} :
    GlobalEnvironment 1 Unit Bool AdvQ AdvR (netSpec Unit Bool) := fun _ _ => do
  let r ← ProbOracleComp.query
    (spec := execSpec 1 Unit Bool AdvQ AdvR ⊕ₒ netSpec Unit Bool) (.inl (.inl ((0 : Fin 1), ())))
  return decide (r = some true)

theorem askPartyG_polyBounded {AdvQ AdvR : Type} :
    (askPartyG : GlobalEnvironment 1 Unit Bool AdvQ AdvR (netSpec Unit Bool)).PolyBounded 1 :=
  fun _ _ => by
  rw [Polynomial.eval_one]
  simp only [askPartyG, bind_pure_comp, ProbOracleComp.query]
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- Because `xorWithCoin` and `coinReaderProto` share the same live `coinSetup` instance in
`gCompose`, querying party `0` deterministically yields `true` with probability `1`. -/
theorem eval_gExec_xorWithCoin_coinReader (κ : ℕ) (z : List Bool) :
    (GlobalExec coinSetup (gCompose xorWithCoin coinReaderProto)
      (gDummyAdversary 1 _ _ _) ∅ askPartyG κ z).eval = PMF.pure true := by
  have hrunFrom : ∀ c : Bool,
      (gExecMachine coinSetup (gCompose xorWithCoin coinReaderProto)
        (gDummyAdversary 1 _ _ _) κ ∅).runFrom (askPartyG κ z) (((), ((), ())), c) =
      pure (true, (((), ((), ())), c)) := fun c => by
    dsimp only [askPartyG]
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    have hq :
        ((gExecMachine coinSetup (gCompose xorWithCoin coinReaderProto)
          (gDummyAdversary 1 _ _ _) κ ∅).handle (Sum.inl (Sum.inl ((0 : Fin 1), ())))).run
          (((), ((), ())), c) =
        pure (some true, (((), ((), ())), c)) := by
      simp only [gExecMachine, Machine.comp, gLiftAdversary, gDummyAdversary, shareRight,
        routeCorrupt, gCompose, gHybridWrap, xorWithCoin, coinReaderProto, liftPartyWithG,
        coinSetup, StateT.run, StateT.lift, Finset.notMem_empty, ↓reduceIte, Machine.runFrom_bind,
        Machine.runFrom_map, Machine.runFrom_query, bind_pure_comp, interp_norm, Functor.map_map,
        map_pure, Prod.map_apply, id_eq, Equiv.prodAssoc_apply, Option.map_some,
        decide_true]
      rfl
    erw [hq, pure_bind, Machine.runFrom_pure]
    rfl
  rw [GlobalExec, Machine.run, Machine.link, Machine.closeProgram_bind,
    Machine.closeProgram_sample, ProbComp.eval_bind]
  dsimp only [gExecMachine, Machine.comp, shareRight, routeCorrupt, gCompose, gHybridWrap,
    xorWithCoin, coinReaderProto, coinSetup, gLiftAdversary, gDummyAdversary]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind,
    PMF.pure_bind, PMF.map, Function.comp_def]
  conv_rhs => rw [← PMF.bind_const (ProbComp.unifFin 1).eval (PMF.pure true)]
  congr 1; funext rG
  erw [hrunFrom (decide (rG.val = 1)), map_pure, Machine.closeProgram_pure, ProbComp.eval_pure]

private theorem eval_gExec_xorWithCoin_indepCoin_eq {AdvQ AdvR : Type}
    (S : GlobalExecAdversary 1 Unit Bool
      (Unit ⊕ RoutedNetQ 1 Unit Unit) (Unit ⊕ RoutedNetR Bool Unit)
      AdvQ AdvR (netSpec Unit Bool))
    (κ : ℕ) (z : List Bool) :
    (GlobalExec coinSetup (gCompose xorWithCoin indepCoinFunc.toGlobalProtocol)
      S ∅ askPartyG κ z).eval =
      (ProbComp.unifFin 1).eval.bind fun rG =>
        (ProbComp.unifFin 1).eval.bind fun rP =>
          PMF.pure (decide (decide (rP.val = 1) = decide (rG.val = 1))) := by
  have hrunFrom : ∀ (sS : (S κ ∅).State) (r c : Bool),
      (gExecMachine coinSetup (gCompose xorWithCoin indepCoinFunc.toGlobalProtocol)
        S κ ∅).runFrom (askPartyG κ z) ((sS, ((), r)), c) =
      pure (decide (r = c), ((sS, ((), r)), c)) := fun sS r c => by
    dsimp only [askPartyG]
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    have hq :
        ((gExecMachine coinSetup (gCompose xorWithCoin indepCoinFunc.toGlobalProtocol)
          S κ ∅).handle (Sum.inl (Sum.inl ((0 : Fin 1), ())))).run ((sS, ((), r)), c) =
        pure (some (decide (r = c)), ((sS, ((), r)), c)) := by
      simp only [gExecMachine, Machine.comp, gLiftAdversary, shareRight, routeCorrupt,
        gCompose, gHybridWrap, xorWithCoin, liftPartyWithG, IdealFunctionality.toGlobalProtocol,
        indepCoinFunc, coinSetup, StateT.run, StateT.lift, Finset.notMem_empty, ↓reduceIte,
        Machine.runFrom_map, Machine.runFrom_query, ProbOracleComp.sample_pure, bind_pure_comp,
        interp_norm, Functor.map_map]
      rfl
    erw [hq, pure_bind, Machine.runFrom_pure]
    simp only [Option.some.injEq]
    rfl
  rw [GlobalExec, Machine.run, Machine.link, Machine.closeProgram_bind, Machine.closeProgram_sample,
    ProbComp.eval_bind]
  dsimp only [gExecMachine, Machine.comp, shareRight, routeCorrupt, gCompose, gHybridWrap,
    xorWithCoin, IdealFunctionality.toGlobalProtocol, indepCoinFunc, coinSetup, gLiftAdversary]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind,
    PMF.pure_bind, PMF.map, Function.comp_def]
  congr 1; funext rG
  congr 1; funext rP
  have hcongr : ((S κ ∅).init.eval.bind fun sS =>
      (Machine.closeProgram (Prod.fst <$> (gExecMachine coinSetup
        (gCompose xorWithCoin indepCoinFunc.toGlobalProtocol) S κ ∅).runFrom (askPartyG κ z)
        ((sS, ((), decide (rP.val = 1))), decide (rG.val = 1)))).eval) =
      ((S κ ∅).init.eval.bind fun _ =>
        PMF.pure (decide (decide (rP.val = 1) = decide (rG.val = 1)))) := by
    congr 1; funext sS
    erw [hrunFrom sS (decide (rP.val = 1)) (decide (rG.val = 1)), map_pure,
      Machine.closeProgram_pure, ProbComp.eval_pure]
  dsimp only [gExecMachine, Machine.comp, shareRight, routeCorrupt, gCompose, gHybridWrap,
    xorWithCoin, IdealFunctionality.toGlobalProtocol, indepCoinFunc, coinSetup,
    gLiftAdversary] at hcongr
  rw [hcongr, PMF.bind_const]

/-- Composing `xorWithCoin` with `indepCoinFunc` (which ignores `coinSetup`) matches the direct
`coinSetup` bit only with probability `1 / 2`, regardless of the adversary `S`. -/
theorem eval_gExec_xorWithCoin_indepCoin {AdvQ AdvR : Type}
    (S : GlobalExecAdversary 1 Unit Bool
      (Unit ⊕ RoutedNetQ 1 Unit Unit) (Unit ⊕ RoutedNetR Bool Unit)
      AdvQ AdvR (netSpec Unit Bool))
    (κ : ℕ) (z : List Bool) (b : Bool) :
    (GlobalExec coinSetup (gCompose xorWithCoin indepCoinFunc.toGlobalProtocol)
      S ∅ askPartyG κ z).eval b = (1 / 2 : ℝ≥0∞) := by
  rw [eval_gExec_xorWithCoin_indepCoin_eq]
  rw [PMF.bind_apply, tsum_fintype, Fin.sum_univ_two]
  simp only [PMF.bind_apply, tsum_fintype, ProbComp.eval_unifFin,
    Probability.PMF.uniformOfFintype_apply, Fintype.card_fin, PMF.pure_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  cases b <;>
    (norm_num
     simp only [← one_div]
     rw [show (1 / 2 : ℝ≥0∞) * (1 / 2) + (1 / 2) * (1 / 2) =
       (1 / 2 + 1 / 2) * (1 / 2) by ring, ENNReal.add_halves, one_mul])

/-- Non-vacuity witness for `GEmulates.compose`: `gCompose xorWithCoin coinReaderProto` does not
GUC-emulate `gCompose xorWithCoin indepCoinFunc.toGlobalProtocol`. -/
theorem not_gEmulates_gCompose_xorWithCoin :
    ¬ GEmulates coinSetup
      (gCompose xorWithCoin coinReaderProto)
      (gCompose xorWithCoin indepCoinFunc.toGlobalProtocol) := by
  intro h
  obtain ⟨S, _, _, hadv⟩ := h _ _ (gDummyAdversary 1 _ _ _) 1
    (gDummyAdversary_polyBounded 1 _ _ _)
  obtain ⟨ν, hν, hbound⟩ := hadv 1
  obtain ⟨m, hm⟩ := (negligible_iff ν).mp hν 0 (1 / 2 : ℝ≥0) (by norm_num)
  have hlt := hm m le_rfl
  simp only [pow_zero, one_mul] at hlt
  have hle := hbound ∅ askPartyG askPartyG_polyBounded m []
  have hadv_eq : gAdvantage coinSetup
      (gCompose xorWithCoin coinReaderProto)
      (gCompose xorWithCoin indepCoinFunc.toGlobalProtocol)
      (gDummyAdversary 1 _ _ _) S ∅ askPartyG m [] = 1 / 2 := by
    rw [gAdvantage, eval_gExec_xorWithCoin_coinReader, Game.advantage_pure_true_left,
      Game.failProbability, eval_gExec_xorWithCoin_indepCoin S m [] false]
    rw [← ENNReal.coe_inj, ENNReal.coe_toNNReal (by norm_num)]
    norm_num
  rw [hadv_eq] at hle
  exact not_lt_of_ge hle hlt

/-! ### Positive GUC composition, dummy completeness, budgets, and separation checks -/

/-- Positive shared-setup EUC composition for `xorWithCoin` and `coinReaderProto`. -/
example :
    GEmulates coinSetup
      (gCompose xorWithCoin coinReaderProto)
      (gCompose xorWithCoin coinReaderProto) :=
  (GEmulates.refl coinSetup coinReaderProto).compose xorWithCoin_polyBounded

/-- Concrete composition and transitivity instantiate cleanly with explicit polynomial overhead. -/
example :
    GEmulatesWithin coinSetup
      (gCompose xorWithCoin coinReaderProto)
      (gCompose xorWithCoin coinReaderProto)
      (Polynomial.X * (Polynomial.X.comp (Polynomial.X + 1) + 1 + 2) +
        (Polynomial.X.comp (Polynomial.X + 1) + 1 + 1))
      (fun _ _ _ => 0) :=
  (GEmulatesWithin.refl coinSetup coinReaderProto).compose xorWithCoin_polyBounded

/-- Dummy-adversary completeness equivalence in the `coinSetup` model. -/
example :
    GEmulates coinSetup coinReaderProto coinReaderProto ↔
      GEmulatesDummy coinSetup coinReaderProto coinReaderProto :=
  gEmulates_iff_gEmulatesDummy coinSetup coinReaderProto coinReaderProto

/-- Explicit polynomial budgets of `gCompose`, `gAbsorbHybrid`, and `gAbsorbAdversary`. -/
example (C : Finset (Fin 1)) :
    (gCompose xorWithCoin coinReaderProto).PolyBounded ((2 + 1) * (1 + 2) + (1 + 1)) ∧
      (gAbsorbHybrid (NQ := Unit) (NR := Bool) C xorWithCoin
        (askPartyG : GlobalEnvironment 1 Unit Bool
          (RoutedNetQ 1 Unit (Unit ⊕ RoutedNetQ 1 Unit Unit))
          (RoutedNetR Bool (Unit ⊕ RoutedNetR Bool Bool))
          (netSpec Unit Bool))).PolyBounded
        (absorbPoly 1 2) ∧
      ∀ κ, (absorbPoly 1 2).eval κ = 7 :=
  ⟨gCompose_polyBounded xorWithCoin_polyBounded coinReaderProto_polyBounded,
    gAbsorbHybrid_polyBounded C xorWithCoin_polyBounded askPartyG_polyBounded,
    fun κ => by simp⟩

/-- Checked local-vs-global separation pair: `localCoinProto` UC-realizes `indepCoinFunc` with zero
error, while `coinReaderProto` fails to GUC-realize `indepCoinFunc` against `coinSetup`. -/
example :
    Realizes localCoinProto indepCoinFunc ∧ ¬ GRealizes coinSetup coinReaderProto indepCoinFunc :=
  ⟨localCoinProto_realizes_indepCoinFunc, not_gRealizes_coinSetup⟩

example (g : Polynomial ℕ) :
    ¬ GRealizesWithin coinSetup coinReaderProto indepCoinFunc g (fun _ _ _ => (1 / 4 : ℝ≥0)) :=
  not_gRealizesWithin_coinSetup g (fun _ _ _ => (1 / 4 : ℝ≥0)) 0 (by norm_num)

end CslibFrontierTests.Crypto.UCGlobalSetup
