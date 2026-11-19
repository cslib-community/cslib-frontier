/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

-- upstream: local-only (tests)

import CslibFrontier.Crypto.Protocols.UC.AdaptiveDummyAdversary
import CslibFrontier.Crypto.Protocols.UC.AdaptiveToStatic
import CslibFrontier.Probability.PMF.Expect
-- Non-module test imports: reuse the shared `P_coin`/`F_coin`/`Z_star` fixtures from
-- `UCAdaptive` and `UCAdaptiveDummy`; ordinary `module`-mode clients of the public UC APIs live in
-- `UCAdaptiveDummyModule.lean`.
import CslibFrontierTests.Crypto.UCAdaptive
import CslibFrontierTests.Crypto.UCAdaptiveDummy

/-!
# Separation witness between erasing and non-erasing parties

Proves `not_adaptiveEmulatesWithin_nonErasing_witness` (at `κ = 0`, `pA = 1`, `pZ = 5`, and
`ε 1 5 0 < 1 / 2`, gap `1 / 2`) and `not_adaptiveEmulates_nonErasing` (`¬ AdaptiveEmulates`),
showing `P_coin .nonErasing` cannot be adaptively emulated by `F_coin.toAdaptive coinReveal`.

In `UCAdaptiveDummy.lean`, `P_coin .erasing` already emulates `F_coin.toAdaptive coinReveal` by
reflexivity (`adaptiveEmulates_erasing_witness`). Together these give a concrete witness
motivating why adaptive realization depends on memory erasure in the snapshot corruption model of
`UC.Adaptive`, where `.erasing` only suppresses `CorruptionReport.history`
([CanettiFischlin2001], Theorems 8 and 11, unformalized).
-/

namespace CslibFrontierTests.Crypto.UCAdaptiveSeparation

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open CslibFrontierTests.Crypto.UCAdaptive
open CslibFrontierTests.Crypto.UCAdaptiveDummy
open OracleComp (sumHandler)
open Machine (closeEval closeEval_pure closeEval_bind closeEval_map closeEval_sample)
open scoped ENNReal NNReal

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
    dsimp only [liftAdaptiveNet]
    erw [Machine.liftRightProgram_pure, Machine.runFrom_pure, closeEval_pure]
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
    simp only [PFunctor.FreeM.bind_eq_bind]
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
        dsimp only [liftAdaptiveNet]
        rw [Machine.liftRightProgram_bind, liftAdaptiveNet_unifFin]
        erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left, closeEval_bind,
          closeEval_sample]
      rw [hstep b tr₁, hstep false tr₂]
      simp only [Probability.PMF.tsum_bind_mul]
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
        dsimp only [liftAdaptiveNet]
        erw [Machine.liftRightProgram_bind, Machine.liftRightProgram_query, Machine.runFrom_bind,
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
                Fin.val_zero, Nat.zero_ne_one, and_false, ↓reduceIte,
                Option.isNone_none, Option.isNone_some, Bool.true_and, Bool.false_eq_true,
                ProbOracleComp.sample_pure, closeEval_bind, closeEval_pure,
                AdaptiveProtocol.recordSnapshot, PMF.pure_bind];
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
              have hsub := corrupted_subset_of_mem_support_router _ κ ∅ _ _ hxsup
              exact mul_eq_zero_of_right _ (hg x.1 x.2.corrupted
                (hsub (Finset.mem_insert_self 1 C)))
          erw [hzero b tr₁, hzero false tr₂]

private theorem eval_F_coin_Z_star_le_half
    (S : AdaptiveAdversary 2 CoinIn Bool Unit Unit (Option Bool)
      (AdaptiveNetQ 2 CoinIn Unit) (AdaptiveNetR Bool Unit (Option Bool))) (κ : ℕ) :
    (adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S Z_star κ []).eval true ≤ 1 / 2 := by
  have hrun_adv : ∀ (sS : (S.machine κ).State),
      (liftAdaptiveAdversary (S.machine κ)).runFrom (Z_star κ []) sS =
        ProbOracleComp.query
            (spec := adaptiveExecSpec 2 CoinIn Bool (AdaptiveNetQ 2 CoinIn Unit)
              (AdaptiveNetR Bool Unit (Option Bool)))
            (.inl (.party 0 .go)) >>= fun _ =>
        ProbOracleComp.query (.inl (.party 0 .erase)) >>= fun _ =>
        ProbOracleComp.query (.inl (.party 1 .poll)) >>= fun optB =>
        liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS) >>= fun x3 =>
        ProbOracleComp.query (.inl .status) >>= fun (C : Finset (Fin 2)) =>
        pure (match optB, x3.1 with
          | some b, .corrupt (some r) =>
              decide (C = {0} ∧ r.history = some [none, some b, none, none])
          | _, _ => false, x3.2) := by
    intro sS
    dsimp only [Z_star]
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary, Machine.liftRight]
    rw [StateT.run_lift, bind_assoc]
    simp only [pure_bind]
    refine bind_congr fun _ => ?_
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary, Machine.liftRight]
    rw [StateT.run_lift, bind_assoc]
    simp only [pure_bind]
    refine bind_congr fun _ => ?_
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary, Machine.liftRight]
    rw [StateT.run_lift, bind_assoc]
    simp only [pure_bind]
    refine bind_congr fun optB => ?_
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary, Machine.liftRight]
    refine bind_congr fun x3 => ?_
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary, Machine.liftRight]
    erw [StateT.run_lift, bind_assoc]
  have hrun_exec : ∀ (sS : (S.machine κ).State)
      (rs : (adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ (S.initial κ)).State),
      (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S κ).runFrom
          (Z_star κ []) (sS, rs) =
        let p0 := if (0 : Fin 2) ∈ rs.corrupted then pure (none, rs)
          else do
            let (out, s') ← ((F_coin.toAdaptive coinReveal).machine κ |>.handle
              (.inl (0, .go))).run rs.inner
            pure (out, (F_coin.toAdaptive coinReveal).recordSnapshot κ s' rs.corrupted rs.trace)
        p0 >>= fun x0 =>
        let p1 := if (0 : Fin 2) ∈ x0.2.corrupted then pure (none, x0.2)
          else do
            let (out, s') ← ((F_coin.toAdaptive coinReveal).machine κ |>.handle
              (.inl (0, .erase))).run x0.2.inner
            pure (out, (F_coin.toAdaptive coinReveal).recordSnapshot κ s'
              x0.2.corrupted x0.2.trace)
        p1 >>= fun x1 =>
        let p2 := if (1 : Fin 2) ∈ x1.2.corrupted then pure (none, x1.2)
          else do
            let (out, s') ← ((F_coin.toAdaptive coinReveal).machine κ |>.handle
              (.inl (1, .poll))).run x1.2.inner
            pure (out, (F_coin.toAdaptive coinReveal).recordSnapshot κ s'
              x1.2.corrupted x1.2.trace)
        p2 >>= fun x2 =>
        ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ (S.initial κ)).runFrom
          (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS)) x2.2) >>= fun x3 =>
        pure (let ⟨⟨netReply, sS'⟩, rs'⟩ := x3
          (match x2.1, netReply with
          | some b, .corrupt (some r) =>
              decide (rs'.corrupted = {0} ∧ r.history = some [none, some b, none, none])
          | _, _ => false, (sS', rs'))) := by
    intro sS rs
    let M := adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ (S.initial κ)
    have hparty (i : Fin 2) (x : CoinIn) (rs' : M.State) :
        (M.handle (.inl (.party i x))).run rs' =
          if i ∈ rs'.corrupted then pure (none, rs')
          else ((F_coin.toAdaptive coinReveal).machine κ |>.handle (.inl (i, x))).run rs'.inner >>=
            fun p => pure (p.1, (F_coin.toAdaptive coinReveal).recordSnapshot κ p.2
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
  have hinit_exec :
      ProbOracleComp.sample (spec := OracleSpec.empty)
          (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S κ).init =
        ProbOracleComp.sample (spec := OracleSpec.empty) (S.machine κ).init >>= fun sS =>
          pure (sS, { inner := { party0 := none, delivered1 := none }
                      corrupted := S.initial κ
                      trace := fun _ => [none] }) := by
    have hfold2 : List.foldl (fun acc (_ : Fin 2) => acc)
        ({ party0 := none, delivered1 := none } : CoinState) (List.finRange 2) =
        { party0 := none, delivered1 := none } := rfl
    dsimp only [adaptiveExecMachine, Machine.comp_init, liftAdaptiveAdversary, Machine.liftRight,
      adaptiveRouter, F_coin, IdealFunctionality.toAdaptive,
      AdaptiveProtocol.applyInitialCorruptions, coinReveal]
    simp only [ite_self, hfold2, pure_bind]
    erw [ProbOracleComp.sample_bind]
    refine bind_congr fun sS => ?_
    erw [ProbOracleComp.sample_pure]
    rfl
  let mkCS (p d : Option Bool) : ((F_coin.toAdaptive coinReveal).machine κ).State :=
    ({ party0 := p, delivered1 := d } : CoinState)
  let getP0 (s : ((F_coin.toAdaptive coinReveal).machine κ).State) : Option Bool :=
    (s : CoinState).party0
  let getD1 (s : ((F_coin.toAdaptive coinReveal).machine κ).State) : Option Bool :=
    (s : CoinState).delivered1
  have hgo (s : ((F_coin.toAdaptive coinReveal).machine κ).State) :
      ((F_coin.toAdaptive coinReveal).machine κ |>.handle (.inl (0, .go))).run s =
        if ((getP0 s).isNone && (getD1 s).isNone) = true then
          ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
            pure ((none : protocolSpec 2 CoinIn Bool Unit Unit (.inl (0, .go))),
              mkCS (some (decide (c = 0))) (some (decide (c = 0))))
        else pure ((none : protocolSpec 2 CoinIn Bool Unit Unit (.inl (0, .go))), s) := by
    simp only [F_coin, IdealFunctionality.toAdaptive, StateT.run, Fin.val_zero, true_and,
      getP0, getD1, mkCS]
    split_ifs <;> simp [ProbOracleComp.sample_pure]
  have herase (s : ((F_coin.toAdaptive coinReveal).machine κ).State) :
      ((F_coin.toAdaptive coinReveal).machine κ |>.handle (.inl (0, .erase))).run s =
        pure ((none : protocolSpec 2 CoinIn Bool Unit Unit (.inl (0, .erase))),
          mkCS none (getD1 s)) := by
    simp only [F_coin, IdealFunctionality.toAdaptive, StateT.run, Fin.val_zero, ↓reduceIte,
      ProbOracleComp.sample_pure, mkCS, getD1]
  have hpoll (s : ((F_coin.toAdaptive coinReveal).machine κ).State) :
      ((F_coin.toAdaptive coinReveal).machine κ |>.handle (.inl (1, .poll))).run s =
        pure ((getD1 s : protocolSpec 2 CoinIn Bool Unit Unit (.inl (1, .poll))), s) := by
    simp only [F_coin, IdealFunctionality.toAdaptive, StateT.run, Fin.val_one, ↓reduceIte,
      ProbOracleComp.sample_pure, getD1]
  have hsnap (s : ((F_coin.toAdaptive coinReveal).machine κ).State)
      (C : Finset (Fin 2)) (tr : Fin 2 → List (Option Bool)) :
      (F_coin.toAdaptive coinReveal).recordSnapshot κ s C tr =
        { inner := s
          corrupted := C
          trace := fun j => tr j ++ [coinReveal κ s j] } := rfl
  have hfalse_of_none (hc : ∀ sS,
      closeEval (Prod.fst <$>
        (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S κ).runFrom
          (Z_star κ [])
          (sS, { inner := { party0 := none, delivered1 := none }
                 corrupted := S.initial κ
                 trace := fun _ => [none] })) = PMF.pure false) :
      (adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S Z_star κ []).eval true ≤ 1 / 2 := by
    have hev : (adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S Z_star κ []).eval =
        PMF.pure false := by
      change closeEval (ProbOracleComp.sample
          (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S κ).init >>= fun s =>
        Prod.fst <$> (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S κ).runFrom
          (Z_star κ []) s) = PMF.pure false
      rw [hinit_exec]
      erw [bind_assoc, closeEval_bind]
      have hbc :
          (closeEval (ProbOracleComp.sample (S.machine κ).init)).bind (fun _ => PMF.pure false) =
            PMF.pure false := PMF.bind_const _ _
      rw [← hbc]
      congr 1
      funext sS
      erw [pure_bind, hc]
    rw [hev, PMF.pure_apply]
    simp
  by_cases h0 : (0 : Fin 2) ∈ S.initial κ
  · refine hfalse_of_none fun sS => ?_
    erw [hrun_exec]
    simp only [h0, ↓reduceIte, pure_bind]
    split_ifs
    · simp only [pure_bind, map_bind, map_pure, closeEval_bind, closeEval_pure, PMF.bind_const]
    · erw [hpoll]
      dsimp only [getD1]
      simp only [pure_bind, map_bind, map_pure]
      rw [closeEval_bind, closeEval_pure, PMF.bind_const]
  · by_cases h1 : (1 : Fin 2) ∈ S.initial κ
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
    · have hinit : S.initial κ = ∅ := by
        ext i
        rcases i with ⟨i, hi⟩
        interval_cases i <;> simp [h0, h1]
      have h0_not : (0 : Fin 2) ∉ (∅ : Finset (Fin 2)) := Finset.notMem_empty 0
      have h1_not : (1 : Fin 2) ∉ (∅ : Finset (Fin 2)) := Finset.notMem_empty 1
      let gMatch (b : Bool) :
          (AdaptiveNetR Bool Unit (Option Bool) × (S.machine κ).State) × Finset (Fin 2) →
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
          (adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S Z_star κ []).eval true =
            ∑' sS : (S.machine κ).State, closeEval (ProbOracleComp.sample (S.machine κ).init) sS *
              ∑' c : Fin 2, (ProbComp.unifFin 1).eval c *
                ∑' x, closeEval
                    ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
                      (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
                      { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
                        corrupted := ∅
                        trace := trC c }) x *
                  gMatch (decide (c = 0)) (x.1, x.2.corrupted) := by
        change (closeEval (ProbOracleComp.sample
            (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S κ).init >>= fun s =>
          Prod.fst <$> (adaptiveExecMachine .adaptive (F_coin.toAdaptive coinReveal) S κ).runFrom
            (Z_star κ []) s)) true = _
        rw [hinit_exec]
        erw [bind_assoc, closeEval_bind]
        rw [PMF.bind_apply]
        refine tsum_congr fun sS => congrArg (closeEval (ProbOracleComp.sample (S.machine κ).init)
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
      have hinner (sS : (S.machine κ).State) :
          ∑' c : Fin 2, (ProbComp.unifFin 1).eval c *
              ∑' x, closeEval
                  ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
                    (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
                    { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
                      corrupted := ∅
                      trace := trC c }) x *
                gMatch (decide (c = 0)) (x.1, x.2.corrupted) ≤
            1 / 2 := by
        let μ : PMF ((AdaptiveNetR Bool Unit (Option Bool) × (S.machine κ).State) ×
            AdaptiveRouterState CoinState (Option Bool) 2) :=
          closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
            (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
            { inner := { party0 := none, delivered1 := some false }
              corrupted := ∅
              trace := fun _ => [none] })
        have hind (c : Fin 2) :
            ∑' x, closeEval ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
                (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
                { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
                  corrupted := ∅
                  trace := trC c }) x *
              gMatch (decide (c = 0)) (x.1, x.2.corrupted) =
            ∑' x, μ x * gMatch (decide (c = 0)) (x.1, x.2.corrupted) :=
          router_F_coin_no1_indep κ (decide (c = 0)) (((S.machine κ).handle (.corrupt 0)).run sS)
            ∅ h1_not (trC c) (fun _ => [none]) (gMatch (decide (c = 0)))
            (hg_one (decide (c = 0)))
        have hunif (c : Fin 2) :
            (Probability.PMF.uniformOfFintype (Fin (1 + 1))) c = (2 : ENNReal)⁻¹ := by
          simp [Probability.PMF.uniformOfFintype]
        simp_rw [hind, ProbComp.eval_unifFin]
        rw [tsum_fintype, Fin.sum_univ_two]
        simp only [Fin.isValue, hunif, decide_true]
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← tsum_add]
        have hpt (x : (AdaptiveNetR Bool Unit (Option Bool) × (S.machine κ).State) ×
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
      calc ∑' sS : (S.machine κ).State, closeEval (ProbOracleComp.sample (S.machine κ).init) sS *
              ∑' c : Fin 2, (ProbComp.unifFin 1).eval c *
                ∑' x, closeEval
                    ((adaptiveRouter .adaptive (F_coin.toAdaptive coinReveal) κ ∅).runFrom
                      (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
                      { inner := { party0 := none, delivered1 := some (decide (c = 0)) }
                        corrupted := ∅
                        trace := trC c }) x *
                  gMatch (decide (c = 0)) (x.1, x.2.corrupted)
          ≤ ∑' sS : (S.machine κ).State,
              closeEval (ProbOracleComp.sample (S.machine κ).init) sS * ((1 : ENNReal) / 2) :=
            tsum_le_tsum fun sS => mul_le_mul_of_nonneg_left (hinner sS) zero_le
        _ = (∑' sS, closeEval (ProbOracleComp.sample (S.machine κ).init) sS) * (1 / 2) :=
            ENNReal.tsum_mul_right
        _ = 1 / 2 := by rw [PMF.tsum_coe, one_mul]

private theorem nonErasing_advantage_ge_half
    (S : AdaptiveAdversary 2 CoinIn Bool Unit Unit (Option Bool)
      (AdaptiveNetQ 2 CoinIn Unit) (AdaptiveNetR Bool Unit (Option Bool))) (κ : ℕ) :
    (1 / 2 : ℝ) ≤ (adaptiveAdvantage .adaptive (P_coin .nonErasing) (F_coin.toAdaptive coinReveal)
      (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
      S Z_star κ [] : ℝ) := by
  have hP := eval_Z_star_nonErasing κ []
  have hQ := eval_F_coin_Z_star_le_half S κ
  have hP_real : ((adaptiveExec .adaptive (P_coin .nonErasing)
      (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
      Z_star κ []).eval true).toReal = 1 := by
    rw [hP]; simp
  have hQ_real : ((adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S
      Z_star κ []).eval true).toReal ≤ 1 / 2 := by
    simpa [ENNReal.toReal_div] using ENNReal.toReal_mono (by norm_num) hQ
  rw [adaptiveAdvantage, Game.coe_advantage, Game.coe_succProbability,
    Game.coe_succProbability, hP_real]
  have h := le_abs_self (1 - ((adaptiveExec .adaptive (F_coin.toAdaptive coinReveal) S
    Z_star κ []).eval true).toReal)
  linarith

/-- Single-point separation at `κ = 0` (`pA = 1`, `pZ = 5`, `ε 1 5 0 < 1 / 2`, gap `1 / 2`,
ideal success probability `≤ 1 / 2` vs. real `1`): `P_coin .nonErasing` cannot be adaptively
emulated by `F_coin.toAdaptive coinReveal` under `AdaptiveEmulatesWithin .adaptive _ _ g ε`. -/
theorem not_adaptiveEmulatesWithin_nonErasing_witness
    {g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (hε : ε 1 5 0 < 1 / 2) :
    ¬ AdaptiveEmulatesWithin .adaptive (P_coin .nonErasing) (F_coin.toAdaptive coinReveal)
      g ε := by
  intro hadv
  obtain ⟨S, -, -, -, hbound⟩ :=
    hadv _ _ (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit) 1
      (adaptiveDummyAdversary_polyBounded _ _ _)
  have h1 : (adaptiveAdvantage .adaptive (P_coin .nonErasing) (F_coin.toAdaptive coinReveal)
      (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
      S Z_star 0 [] : ℝ) ≤ (ε 1 5 0 : ℝ) := by
    exact_mod_cast hbound Z_star 5 Z_star_polyBounded 0 []
  have hlow := nonErasing_advantage_ge_half S 0
  have hε_real : (ε 1 5 0 : ℝ) < 1 / 2 := by exact_mod_cast hε
  linarith

/-- Asymptotic nonvacuity witness: `P_coin .nonErasing` does not adaptively emulate
`F_coin.toAdaptive coinReveal` under `AdaptiveEmulates .adaptive`, since every simulator has
distinguishing gap at least `1 / 2` against `Z_star` at every `κ`. -/
theorem not_adaptiveEmulates_nonErasing :
    ¬ AdaptiveEmulates .adaptive (P_coin .nonErasing) (F_coin.toAdaptive coinReveal) := by
  intro hadv
  obtain ⟨S, -, -, hbound⟩ :=
    hadv _ _ (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit) 1
      (adaptiveDummyAdversary_polyBounded _ _ _)
  obtain ⟨ν, hν, hadvν⟩ := hbound 5
  obtain ⟨κ, hκ⟩ := ((hν 0).eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0) < 1 / 2))).exists
  have h1 : (adaptiveAdvantage .adaptive (P_coin .nonErasing) (F_coin.toAdaptive coinReveal)
      (adaptiveDummyAdversary (View := Option Bool) (fun _ => ∅) Unit Unit)
      S Z_star κ [] : ℝ) ≤ (ν κ : ℝ) := by
    exact_mod_cast hadvν Z_star Z_star_polyBounded κ []
  have hlow := nonErasing_advantage_ge_half S κ
  simp only [pow_zero, one_mul] at hκ
  have hκ_real : (ν κ : ℝ) < 1 / 2 := by exact_mod_cast hκ
  linarith

end CslibFrontierTests.Crypto.UCAdaptiveSeparation
