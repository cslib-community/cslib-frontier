/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

-- upstream: local-only (tests)

import CslibFrontier.Crypto.Protocols.UC.AdaptiveToStatic
import CslibFrontier.Crypto.Protocols.UC.AdaptiveDummyAdversary
-- Non-module test import: reuses the shared `P_coin`/`F_coin`/`corruptAdv` fixture from
-- `UCAdaptive`; ordinary `module`-mode clients of the public API live in
-- `UCAdaptiveDummyModule.lean`.
import CslibFrontierTests.Crypto.UCAdaptive

/-!
# Tests for `AdaptiveToStatic` and `AdaptiveDummyAdversary`

Exercises `AdaptiveAdversary.clampStatic`, `adaptiveDummyAdversary`, `Z_star`, the erasing-party
`adaptiveEmulates_erasing_witness` (holds by reflexivity via `P_coin_erasing_eq_F_coin`), and the
headline bridge/dummy witnesses (`AdaptiveEmulatesWithin.static_of_adaptive`,
`AdaptiveEmulates.static_of_adaptive`, `emulatesDummyWithin`,
`adaptiveEmulates_iff_adaptiveEmulatesDummy`).
-/

namespace CslibFrontierTests.Crypto.UCAdaptiveDummy

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open CslibFrontierTests.Crypto.UCAdaptive
open OracleComp (sumHandler)
open scoped NNReal

/-! ### Clamped adversary tests (`AdaptiveAdversary.clampStatic`) -/

theorem corruptAdv_noNewCorrupt_clampStatic : corruptAdv.clampStatic.NoNewCorrupt :=
  corruptAdv.noNewCorrupt_clampStatic

theorem corruptAdv_clampStatic_polyBounded : corruptAdv.clampStatic.PolyBounded 1 :=
  corruptAdv_polyBounded.clampStatic

theorem corruptAdv_clampStatic_status (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive (P_coin .erasing) corruptAdv.clampStatic corruptCheckEnv κ z).eval
        false = 1 := by
  rw [← adaptiveExec_static_eq_adaptive_clampStatic]
  let A := liftAdaptiveAdversary (n := 2) (In := CoinIn) (Out := Bool) (corruptAdv.machine κ)
  let M := adaptiveRouter .static (P_coin .erasing) κ (corruptAdv.initial κ)
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
      ProbOracleComp.query
          (spec := adaptiveProtocolSpec 2 CoinIn Bool Unit Unit (Option Bool))
          (.inl .status) >>= fun (C : Finset (Fin 2)) =>
      pure (decide (C = ({0, 1} : Finset (Fin 2))), ()) := by
    dsimp only [corruptCheckEnv]
    erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A), StateT.run_lift]
    dsimp only [A, liftAdaptiveAdversary, corruptAdv]
    simp only [bind_assoc, pure_bind]
    exact bind_congr fun _ => by
      erw [Machine.runFrom_bind (M := A), Machine.runFrom_query (M := A)]
      simp only [Machine.runFrom_pure]; rfl
  have hnot : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) := by decide
  have hneq : ({1} : Finset (Fin 2)) ≠ {0, 1} := by decide
  have hcor : (M.handle (.inr (.corrupt 0))).run sInit = pure (.corrupt none, sInit) := by
    simp only [M, sInit, adaptiveRouter, StateT.run, hnot, ↓reduceIte]; rfl
  have hstatus : (M.handle (.inl .status)).run sInit = pure (sInit.corrupted, sInit) := rfl
  rw [adaptiveExec, Machine.run]
  change (Machine.closeProgram (ProbOracleComp.sample (A.comp M).init >>= fun s =>
    Prod.fst <$> (A.comp M).runFrom (corruptCheckEnv κ z) s)).eval false = 1
  rw [Machine.comp_init]
  erw [hMinit, ProbOracleComp.sample_bind, ProbOracleComp.sample_pure, bind_assoc, pure_bind,
    ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_comp (A := A) (P := M), hrunA,
    Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hcor, pure_bind,
    Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hstatus, pure_bind,
    Machine.runFrom_pure (M := M), map_pure, Equiv.prodAssoc_apply,
    Machine.closeProgram_pure, ProbComp.eval_pure, PMF.pure_apply]
  simp only [sInit, hneq, decide_false, ↓reduceIte]

/-! ### Distinguishing environment `Z_star` and dummy-adversary witnesses -/

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
  have hgo : (M.handle (.inl (.party 0 .go))).run
      { inner := { party0 := none, delivered1 := none }
        corrupted := ∅, trace := fun _ => [none] } =
      (fun c : Fin 2 =>
        (none, { inner := { party0 := some (decide (c = 0)), delivered1 := some (decide (c = 0)) }
                 corrupted := ∅
                 trace := fun i =>
                   [none,
                     if i.val = 0 then some (decide (c = 0)) else some (decide (c = 0))] })) <$>
        ProbOracleComp.sample (ProbComp.unifFin 1) := by
    simp only [M, adaptiveRouter, P_coin, StateT.run, Fin.val_zero,
      Finset.notMem_empty, ↓reduceIte, Option.isNone_none, Bool.and_self, bind_pure_comp,
      AdaptiveProtocol.recordSnapshot, List.cons_append, List.nil_append]
    rfl
  have herase (c : Fin 2) : (M.handle (.inl (.party 0 .erase))).run
      { inner := { party0 := some (decide (c = 0)), delivered1 := some (decide (c = 0)) }
        corrupted := ∅
        trace := fun i =>
          [none, if i.val = 0 then some (decide (c = 0)) else some (decide (c = 0))] } =
      pure (none,
        { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
          corrupted := ∅
          trace := fun i =>
            [none,
              if i.val = 0 then some (decide (c = 0)) else some (decide (c = 0)),
              if i.val = 0 then none else some (decide (c = 0))] }) := by
    simp only [M, adaptiveRouter, P_coin, StateT.run, Fin.val_zero,
      Finset.notMem_empty, ↓reduceIte, pure_bind, AdaptiveProtocol.recordSnapshot,
      List.cons_append, List.nil_append]
    rfl
  have hpoll (c : Fin 2) : (M.handle (.inl (.party 1 .poll))).run
      { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
        corrupted := ∅
        trace := fun i =>
          [none,
            if i.val = 0 then some (decide (c = 0)) else some (decide (c = 0)),
            if i.val = 0 then none else some (decide (c = 0))] } =
      pure (some (decide (c = 0)),
        { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
          corrupted := ∅
          trace := fun i =>
            [none,
              if i.val = 0 then some (decide (c = 0)) else some (decide (c = 0)),
              if i.val = 0 then none else some (decide (c = 0)),
              if i.val = 0 then none else some (decide (c = 0))] }) := by
    simp only [M, adaptiveRouter, P_coin, StateT.run, Fin.val_one,
      Finset.notMem_empty, ↓reduceIte, pure_bind, AdaptiveProtocol.recordSnapshot,
      List.cons_append, List.nil_append]
    rfl
  have hcor0 (c : Fin 2) : (M.handle (.inr (.corrupt 0))).run
      { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
        corrupted := ∅
        trace := fun i =>
          [none,
            if i.val = 0 then some (decide (c = 0)) else some (decide (c = 0)),
            if i.val = 0 then none else some (decide (c = 0)),
            if i.val = 0 then none else some (decide (c = 0))] } =
      pure (.corrupt (some { current := none, history :=
          if m = .nonErasing then some [none, some (decide (c = 0)), none, none] else none }),
        { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
          corrupted := {0}
          trace := fun i =>
            [none,
              if i.val = 0 then some (decide (c = 0)) else some (decide (c = 0)),
              if i.val = 0 then none else some (decide (c = 0)),
              if i.val = 0 then none else some (decide (c = 0))] }) := by
    simp only [M, adaptiveRouter, P_coin, StateT.run, Finset.notMem_empty, ↓reduceIte,
      AdaptiveProtocol.corruptionReport, Fin.val_zero]
    rfl
  change (Machine.closeProgram (ProbOracleComp.sample M.init >>= fun s =>
    Prod.fst <$> M.runFrom (Z_star κ z) s)).eval = PMF.pure (decide (m = .nonErasing))
  erw [hinit, ProbOracleComp.sample_pure, pure_bind]
  dsimp only [Z_star]
  erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hgo, map_bind,
    bind_map_left, Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_bind]
  dsimp only
  refine (congrArg (PMF.bind _) (funext fun c => ?_)).trans (PMF.bind_const _ _)
  erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), herase, pure_bind,
    Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hpoll, pure_bind,
    Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hcor0, pure_bind,
    Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hstatus, pure_bind,
    Machine.runFrom_pure (M := M), map_pure]
  cases m <;> simp [Machine.closeProgram_pure, ProbComp.eval_pure]

theorem eval_Z_star_nonErasing (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive (P_coin .nonErasing)
        (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
        Z_star κ z).eval true = 1 := by
  rw [Z_star_dummy_eval, PMF.pure_apply]; simp

theorem eval_Z_star_erasing (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive (P_coin .erasing)
        (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
        Z_star κ z).eval true = 0 := by
  rw [Z_star_dummy_eval, PMF.pure_apply]; simp

/-! ### Erasing reflexivity and headline bridge / dummy-adversary witnesses -/

/-- `P_coin .erasing` and `F_coin.toAdaptive coinReveal` share the same machine, view map, and
trivial `onCorrupt := fun _ _ s => s`, so they agree definitionally. -/
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
          | (simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bind_pure_comp]
             split_ifs <;> rfl)
    · rfl

/-- `P_coin .erasing` adaptively emulates `F_coin.toAdaptive coinReveal` with zero error by
reflexivity (`AdaptiveEmulatesWithin.refl` via `P_coin_erasing_eq_F_coin`), rather than a
non-trivial simulation argument. -/
theorem adaptiveEmulates_erasing_witness :
    AdaptiveEmulatesWithin .adaptive (P_coin .erasing) (F_coin.toAdaptive coinReveal)
      Polynomial.X (fun _ _ _ => 0) := by
  rw [P_coin_erasing_eq_F_coin]
  exact AdaptiveEmulatesWithin.refl .adaptive (F_coin.toAdaptive coinReveal)

theorem erasing_adaptiveEmulates :
    AdaptiveEmulates .adaptive (P_coin .erasing) (F_coin.toAdaptive coinReveal) :=
  adaptiveEmulates_erasing_witness.emulates fun _ _ _ => by simp

theorem erasing_staticEmulatesWithin :
    AdaptiveEmulatesWithin .static (P_coin .erasing) (F_coin.toAdaptive coinReveal)
      Polynomial.X (fun _ _ _ => 0) :=
  adaptiveEmulates_erasing_witness.static_of_adaptive

theorem erasing_staticEmulates :
    AdaptiveEmulates .static (P_coin .erasing) (F_coin.toAdaptive coinReveal) :=
  erasing_adaptiveEmulates.static_of_adaptive

theorem erasing_emulatesDummyWithin :
    AdaptiveEmulatesDummyWithin .adaptive (P_coin .erasing) (F_coin.toAdaptive coinReveal)
      (Polynomial.X.comp (Polynomial.X + 1)) (fun _ _ => 0) :=
  adaptiveEmulates_erasing_witness.emulatesDummyWithin

theorem erasing_adaptiveEmulatesDummy :
    AdaptiveEmulatesDummy .adaptive (P_coin .erasing) (F_coin.toAdaptive coinReveal) :=
  (adaptiveEmulates_iff_adaptiveEmulatesDummy .adaptive
    (P_coin .erasing) (F_coin.toAdaptive coinReveal)).mp erasing_adaptiveEmulates

end CslibFrontierTests.Crypto.UCAdaptiveDummy
