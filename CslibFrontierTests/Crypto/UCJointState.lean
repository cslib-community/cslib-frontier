/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.SSP.ParFinLazy
import CslibFrontier.Crypto.Protocols.UC.JointState
import CslibFrontierTests.Crypto.UCMultiSession

/-! # Joint-state UC witness tests -/
namespace CslibFrontierTests.Crypto.UCJointState
open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.UC
open CslibFrontierTests.Crypto.UCMultiSession

/-- Uniform-bit ideal functionality (`n = 2`): samples a bit at `init` and outputs it on poll. -/
private def coinFunc : IdealFunctionality 2 Unit Bool Unit Unit where
  State := Bool
  init _ _ := (fun r : Fin 2 => decide (r.val = 0)) <$> ProbComp.unifFin 1
  onInput _ _ s := pure (some s, s)
  onBackdoor _ s := pure ((), s)

/-- Uniform-bit functionality with a nontrivial backdoor (`BackR := Bool`) revealing the coin. -/
private def coinBackdoorFunc : IdealFunctionality 2 Unit Bool Unit Bool where
  State := Bool
  init _ _ := (fun r : Fin 2 => decide (r.val = 0)) <$> ProbComp.unifFin 1
  onInput _ _ s := pure (some s, s)
  onBackdoor _ s := pure (s, s)

/-- Deliberately wrong shared-copy functionality: ignores `ssid` and shares one global coin. -/
private def wrongSharedCoinFunc :
    IdealFunctionality 2 (SubSessionInput (Fin 2) Unit) Bool
      (SubSessionBackdoor (Fin 2) Unit) Unit where
  State := Bool
  init _ _ := (fun r : Fin 2 => decide (r.val = 0)) <$> ProbComp.unifFin 1
  onInput _ _ s := pure (some s, s)
  onBackdoor _ s := pure ((), s)

/-- Single-session coin machine used to witness lazy sampling (`SSP.run_parFinLazy_eq_parFin`). -/
private def coinMachine : Machine OracleSpec.empty (fun _ : Unit => Bool) where
  State := Bool
  init := (fun r : Fin 2 => decide (r.val = 0)) <$> ProbComp.unifFin 1
  handle _ s := pure (s, s)

/-- Witness 1 (lazy creation is real): polling only copy `1` leaves `sessions 0 = none` and
initializes copy `1`. -/
theorem lazy_creation_witness :
    ((Machine.closeProgram
        ((fun (_, s') => decide (s'.sessions 0 = none ∧ (s'.sessions 1).isSome)) <$>
          (corruptRouter ∅ ((coinFunc.multiSession (Fin 2)).toProtocol 0 ∅)).runFrom
            (ProbOracleComp.query (Sum.inl ((0 : Fin 2), ⟨(1 : Fin 2), ()⟩)))
            { secParam := 0, corrupted := ∅, sessions := fun _ => none })).eval) =
      PMF.pure true := by
  simp only [corruptRouter, IdealFunctionality.multiSession, IdealFunctionality.toProtocol,
    coinFunc, Machine.runFrom_query, StateT.run, Machine.closeProgram_map,
    Machine.closeProgram_sample, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_unifFin, Finset.notMem_empty, ↓reduceIte, pure_bind, bind_map_left,
    PMF.map_bind]
  ext b
  simp only [PMF.bind_apply, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
    tsum_fintype, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, decide_true,
    PMF.pure_apply]
  cases b <;> simp [ENNReal.inv_two_add_inv_two]

private def twoCopiesEnv : Environment 2 (SubSessionInput (Fin 2) Unit) Bool
    (RoutedNetQ 2 (SubSessionInput (Fin 2) Unit) (SubSessionBackdoor (Fin 2) Unit))
    (RoutedNetR Bool Unit) := fun _ _ => do
  let b₀ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), ⟨(0 : Fin 2), ()⟩))
  let b₁ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), ⟨(1 : Fin 2), ()⟩))
  pure (decide (b₀ = b₁))

/-- Witness 2 (copies are independent, not shared): `coinFunc.multiSession` yields
`Pr[b₀ = b₁] = 1/2`, whereas the wrong shared-state functionality yields `1`, so the executions
differ. -/
theorem copies_independent_witness :
    (exec (coinFunc.multiSession (Fin 2)).toProtocol
        (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval true = (2 : ENNReal)⁻¹ ∧
      (exec wrongSharedCoinFunc.toProtocol
        (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval true = 1 ∧
      (exec (coinFunc.multiSession (Fin 2)).toProtocol
        (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval ≠
      (exec wrongSharedCoinFunc.toProtocol
        (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval := by
  have hInd : (exec (coinFunc.multiSession (Fin 2)).toProtocol
      (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval true = (2 : ENNReal)⁻¹ := by
    rw [exec_dummyAdversary]
    simp only [twoCopiesEnv, corruptRouter, IdealFunctionality.multiSession,
      IdealFunctionality.toProtocol, coinFunc, Machine.run, Machine.link,
      Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
      Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_map,
      Machine.closeProgram_pure, ProbOracleComp.sample_pure, pure_bind, map_bind,
      bind_map_left, StateT.run, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_unifFin, Function.update_of_ne Fin.zero_ne_one.symm,
      Finset.notMem_empty, ↓reduceIte, PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
    simp only [PMF.bind_apply, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
      tsum_fintype, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, PMF.pure_apply,
      Nat.one_ne_zero, decide_false, decide_true, Option.some.injEq, Bool.true_eq_false,
      Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add]
    rw [← mul_add]
    simp [ENNReal.inv_two_add_inv_two]
  have hShared : (exec wrongSharedCoinFunc.toProtocol
      (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval true = 1 := by
    rw [exec_dummyAdversary]
    simp only [twoCopiesEnv, corruptRouter, IdealFunctionality.toProtocol, wrongSharedCoinFunc,
      Machine.run, Machine.link, Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
      Machine.closeProgram_bind, Machine.closeProgram_sample, ProbOracleComp.sample_pure, pure_bind,
      bind_map_left, StateT.run, ProbComp.eval_bind,
      ProbComp.eval_unifFin, Finset.notMem_empty, ↓reduceIte]
    simp only [PMF.bind_apply, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
      tsum_fintype, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one]
    simp [ENNReal.inv_two_add_inv_two]
  refine ⟨hInd, hShared, fun heq => ?_⟩
  have h12 := congrArg (fun p : PMF Bool => p true) heq
  rw [hInd, hShared] at h12
  norm_num at h12

private theorem link_routeCorrupt_hybridWrap_inr_inl
    {n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR β : Type} (C : Finset (Fin n))
    (M : Machine (partySpec n SubIn SubOut) (protocolSpec n In Out NetQ NetR))
    (s₀ : M.State) (hInit : M.init = pure s₀) (q : NQ) (i : Fin n) (x : In)
    (f : RoutedNetR Out (NetR ⊕ NR) → Option Out → β) :
    (routeCorrupt C (hybridWrap (NQ := NQ) (NR := NR) M)).link
        (ProbOracleComp.query (.inr (.inr (.inr q))) >>= fun r =>
          ProbOracleComp.query (.inl (i, x)) >>= fun r₁ => pure (f r r₁)) =
      ProbOracleComp.query (spec := protocolSpec n SubIn SubOut NQ NR) (.inr q) >>= fun a =>
        (if i ∈ C then pure none
          else Prod.fst <$> liftParty ((M.handle (.inl (i, x))).run s₀)) >>=
          fun r₁ => pure (f (.inr (.inr a)) r₁) := by
  have h0 : (routeCorrupt C (hybridWrap (NQ := NQ) (NR := NR) M)).init = pure s₀ := hInit
  have h1 : ∀ (s : M.State), ((routeCorrupt C (hybridWrap (NQ := NQ) (NR := NR) M)).handle
      (.inr (.inr (.inr q)))).run s = (fun a => (Sum.inr (Sum.inr a), s)) <$>
        ProbOracleComp.query (spec := protocolSpec n SubIn SubOut NQ NR) (.inr q) := fun s => by
    erw [routeCorrupt_handle_inr_inr]
    change (fun p => (Sum.inr p.1, p.2)) <$>
      (StateT.lift (Sum.inr <$> ProbOracleComp.query (spec := protocolSpec n SubIn SubOut NQ NR)
        (.inr q)) : StateT M.State _ _).run s = _
    erw [StateT.run_lift]
    simp only [bind_pure_comp, Functor.map_map]
  erw [Machine.link, h0, ProbOracleComp.sample_pure, pure_bind, Machine.runFrom_bind,
    Machine.runFrom_query, h1, bind_map_left, map_bind]
  refine bind_congr fun a => ?_
  erw [Machine.runFrom_bind, Machine.runFrom_query, routeCorrupt_handle_inl]
  simp only [Machine.runFrom_pure]
  by_cases hi : i ∈ C
  · simp only [hi, ↓reduceIte]
    change Prod.fst <$> (pure (none, s₀) >>= fun x₁ => pure (f (.inr (.inr a)) x₁.1, x₁.2)) = _
    simp only [pure_bind, map_pure]
  · simp only [hi, ↓reduceIte]
    change Prod.fst <$> (liftParty ((M.handle (.inl (i, x))).run s₀) >>= fun p =>
      pure (f (.inr (.inr a)) p.1, p.2)) = _
    simp only [map_bind, map_pure, bind_map_left]

private theorem liftParty_toJoint_bind
    {m n : ℕ} {SubIn SubOut BackQ BackR α : Type}
    (c : SubSessionCall m n SubIn)
    (cont : Option SubOut →
      ProbOracleComp (multiPartySpec m n SubIn SubOut) α) :
    liftParty (NetQ := RoutedNetQ n (SubSessionInput (Fin m) SubIn)
        (SubSessionBackdoor (Fin m) BackQ))
      (NetR := RoutedNetR SubOut BackR)
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => OracleComp.query
            (spec := probOracleSpec (partySpec n (SubSessionInput (Fin m) SubIn) SubOut))
            (Sum.inl k))
          fun (c' : SubSessionCall m n SubIn) => ProbOracleComp.query
            (spec := partySpec n (SubSessionInput (Fin m) SubIn) SubOut)
            (c'.party, ⟨c'.session, c'.input⟩))
        (ProbOracleComp.query c >>= fun r : Option SubOut => cont r)) =
      ProbOracleComp.query (spec := protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
          (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
          (RoutedNetR SubOut BackR))
        (Sum.inl (c.party, ⟨c.session, c.input⟩)) >>= fun r : Option SubOut =>
      liftParty (NetQ := RoutedNetQ n (SubSessionInput (Fin m) SubIn)
          (SubSessionBackdoor (Fin m) BackQ))
        (NetR := RoutedNetR SubOut BackR)
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => OracleComp.query
              (spec := probOracleSpec (partySpec n (SubSessionInput (Fin m) SubIn) SubOut))
              (Sum.inl k))
            fun (c' : SubSessionCall m n SubIn) => ProbOracleComp.query
              (spec := partySpec n (SubSessionInput (Fin m) SubIn) SubOut)
              (c'.party, ⟨c'.session, c'.input⟩))
          (cont r)) := by
  erw [OracleComp.interpret_bind, OracleComp.interpret_query]
  dsimp only [OracleComp.sumHandler, liftParty]
  erw [OracleComp.interpret_bind, OracleComp.interpret_query]

private theorem liftParty_toJoint_pure
    {m n : ℕ} {SubIn SubOut BackQ BackR α : Type} (a : α) :
    liftParty (NetQ := RoutedNetQ n (SubSessionInput (Fin m) SubIn)
        (SubSessionBackdoor (Fin m) BackQ))
      (NetR := RoutedNetR SubOut BackR)
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => OracleComp.query
            (spec := probOracleSpec (partySpec n (SubSessionInput (Fin m) SubIn) SubOut))
            (Sum.inl k))
          fun (c : SubSessionCall m n SubIn) => ProbOracleComp.query
            (spec := partySpec n (SubSessionInput (Fin m) SubIn) SubOut)
            (c.party, ⟨c.session, c.input⟩))
        (pure a)) = pure a := by
  dsimp only [liftParty]
  erw [OracleComp.interpret_pure]

private theorem liftParty_toJoint_one
    {m n : ℕ} {SubIn SubOut BackQ BackR α : Type}
    (c : SubSessionCall m n SubIn) (f : Option SubOut → α) :
    liftParty (NetQ := RoutedNetQ n (SubSessionInput (Fin m) SubIn)
        (SubSessionBackdoor (Fin m) BackQ))
      (NetR := RoutedNetR SubOut BackR)
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => OracleComp.query
            (spec := probOracleSpec (partySpec n (SubSessionInput (Fin m) SubIn) SubOut))
            (Sum.inl k))
          fun (c' : SubSessionCall m n SubIn) => ProbOracleComp.query
            (spec := partySpec n (SubSessionInput (Fin m) SubIn) SubOut)
            (c'.party, ⟨c'.session, c'.input⟩))
        (ProbOracleComp.query c >>= fun r : Option SubOut => pure (f r))) =
      ProbOracleComp.query (spec := protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
          (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
          (RoutedNetR SubOut BackR))
        (Sum.inl (c.party, ⟨c.session, c.input⟩)) >>= fun r : Option SubOut => pure (f r) := by
  erw [liftParty_toJoint_bind c (fun r => pure (f r))]
  exact bind_congr fun r => liftParty_toJoint_pure (f r)

private theorem liftParty_toJoint_two
    {m n : ℕ} {SubIn SubOut BackQ BackR α : Type}
    (c₀ c₁ : SubSessionCall m n SubIn) (f : Option SubOut → Option SubOut → α) :
    liftParty (NetQ := RoutedNetQ n (SubSessionInput (Fin m) SubIn)
        (SubSessionBackdoor (Fin m) BackQ))
      (NetR := RoutedNetR SubOut BackR)
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => OracleComp.query
            (spec := probOracleSpec (partySpec n (SubSessionInput (Fin m) SubIn) SubOut))
            (Sum.inl k))
          fun (c' : SubSessionCall m n SubIn) => ProbOracleComp.query
            (spec := partySpec n (SubSessionInput (Fin m) SubIn) SubOut)
            (c'.party, ⟨c'.session, c'.input⟩))
        (ProbOracleComp.query c₀ >>= fun x₀ : Option SubOut =>
          ProbOracleComp.query c₁ >>= fun x₁ : Option SubOut => pure (f x₀ x₁))) =
      ProbOracleComp.query (spec := protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
          (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
          (RoutedNetR SubOut BackR))
        (Sum.inl (c₀.party, ⟨c₀.session, c₀.input⟩)) >>= fun x₀ : Option SubOut =>
      ProbOracleComp.query (spec := protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
          (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
          (RoutedNetR SubOut BackR))
        (Sum.inl (c₁.party, ⟨c₁.session, c₁.input⟩)) >>= fun x₁ : Option SubOut =>
        pure (f x₀ x₁) := by
  erw [liftParty_toJoint_bind c₀ (fun x₀ =>
    ProbOracleComp.query c₁ >>= fun x₁ => pure (f x₀ x₁))]
  refine bind_congr fun x₀ => ?_
  erw [liftParty_toJoint_bind c₁ (fun x₁ => pure (f x₀ x₁))]
  exact bind_congr fun x₁ => liftParty_toJoint_pure (f x₀ x₁)

private theorem tsum_ite_add_mul_eq {α : Type}
    (c₁ c₂ : α) {dc₁ : ∀ a, Decidable (a = c₁)} {dc₂ : ∀ a, Decidable (a = c₂)}
    (v₁ v₂ : ENNReal) (f : α → ENNReal) :
    (∑' a, (v₁ * (@ite _ (a = c₁) (dc₁ a) (1 : ENNReal) 0) +
      v₂ * (@ite _ (a = c₂) (dc₂ a) (1 : ENNReal) 0)) * f a) =
      v₁ * f c₁ + v₂ * f c₂ := by
  classical
  have hsplit : ∀ a,
      (v₁ * (@ite _ (a = c₁) (dc₁ a) (1 : ENNReal) 0) +
        v₂ * (@ite _ (a = c₂) (dc₂ a) (1 : ENNReal) 0)) * f a =
        (if a = c₁ then v₁ * f c₁ else 0) + (if a = c₂ then v₂ * f c₂ else 0) := by
    intro a
    split_ifs <;> simp_all [add_mul]
  simp_rw [hsplit]
  rw [CompleteLattice.summable.tsum_add CompleteLattice.summable]
  simp [tsum_ite_eq]

private theorem tsum_ite_mul_eq {α : Type}
    (c : α) {dc : ∀ a, Decidable (a = c)} (f : α → ENNReal) :
    (∑' a, (@ite _ (a = c) (dc a) (1 : ENNReal) 0) * f a) = f c := by
  have h := tsum_ite_add_mul_eq c c (dc₁ := dc) (dc₂ := dc) 1 0 f
  simp only [one_mul, zero_mul, add_zero] at h
  exact h

/-- Witness 3 (demux equality on a nontrivial instance at corrupted party `C = {1}`): concrete
probabilities match on both sides of `exec_compose_toJoint_multiSession` for `orOuter` and
`idealRelay`, exercising the corrupted-party network route `.inr (.inl (1, ...))`. -/
theorem demux_nontrivial_corrupted_witness :
    let A : ExecAdversary 2 Bool Bool
        (Unit ⊕ RoutedNetQ 2 (SubSessionInput (Fin 2) Bool) (SubSessionBackdoor (Fin 2) Unit))
        (Unit ⊕ RoutedNetR Bool Unit) (Fin 2 × SubSessionInput (Fin 2) Bool) (Option Bool) :=
      fun _ _ => {
        State := Unit
        init := pure ()
        handle | q, () => do
          let r ← ProbOracleComp.query (.inr (.inr (.inl q)))
          pure (Sum.elim (fun _ => none) (Sum.elim (fun _ => none)
            (Sum.elim id (fun _ => none))) r, ()) }
    let Z : Environment 2 Bool Bool (Fin 2 × SubSessionInput (Fin 2) Bool) (Option Bool) :=
      fun _ _ => do
        let r₀ ← ProbOracleComp.query (.inr ((1 : Fin 2), ⟨(0 : Fin 2), true⟩))
        let r₁ ← ProbOracleComp.query (.inl ((0 : Fin 2), false))
        pure ((r₀ == some true) && (r₁ == some false))
    (exec (compose orOuter.toJoint (idealRelay.multiSession (Fin 2)).toProtocol) A {1} Z 0 []).eval
        true = 1 ∧
      (exec (composeMulti orOuter idealRelay.toProtocol) (jointDemux A) {1} Z 0 []).eval
        true = 1 := by
  intro A Z
  have hL : (exec (compose orOuter.toJoint (idealRelay.multiSession (Fin 2)).toProtocol)
      A {1} Z 0 []).eval true = 1 := by
    let sNone : idealRelay.State := { last := none }
    let sTrue : idealRelay.State := { last := some true }
    have hRelayOn : ∀ i b (s : idealRelay.State), idealRelay.onInput i b s =
        pure (if b then (some true, sTrue) else (s.last, s)) := fun _ b _ => by
      cases b <;> rfl
    have hRelayInit : idealRelay.init 0 {1} = pure sNone := rfl
    have hNoneLast : sNone.last = none := rfl
    have hTrueLast : sTrue.last = some true := rfl
    have hA : (liftAdversary (n := 2) (In := Bool) (Out := Bool) (A 0 {1})).link (Z 0 []) =
        (ProbOracleComp.query (.inr (.inr (.inr (.inl ((1 : Fin 2), ⟨(0 : Fin 2), true⟩))))) >>=
          fun r => ProbOracleComp.query (.inl ((0 : Fin 2), false)) >>= fun r₁ =>
            pure (((Sum.elim (fun _ => none) (Sum.elim (fun _ => none)
              (Sum.elim id (fun _ => none))) r == some true) && (r₁ == some false)))) := by
      rw [Machine.link]
      dsimp only [liftAdversary, A, Z]
      erw [ProbOracleComp.sample_pure, pure_bind]
    rw [exec, execMachine, compose, corruptRouter_comp, Machine.run_comp, Machine.run_comp, hA]
    erw [link_routeCorrupt_hybridWrap_inr_inl _ _ (() : Unit) rfl]
    simp only [Finset.mem_singleton, Fin.zero_ne_one, ↓reduceIte, MultiHybridProtocol.toJoint,
      orOuter, StateT.run]
    erw [liftParty_toJoint_two]
    simp only [map_bind, map_pure, bind_assoc, pure_bind, Sum.elim_inr]
    simp only [pure_bind, Machine.run, Machine.link, corruptRouter,
      IdealFunctionality.multiSession, IdealFunctionality.toProtocol,
      Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
      ProbOracleComp.sample_pure, StateT.run_map, map_bind,
      Finset.mem_singleton, Fin.zero_ne_one, ↓reduceIte]
    simp only [StateT.run, hRelayInit, hRelayOn, pure_bind, Function.update_self,
      Function.update_of_ne Fin.zero_ne_one.symm, Sum.elim_inl, id_eq,
      hNoneLast, hTrueLast, Option.getD_some, Option.getD_none, Bool.false_eq_true,
      Bool.true_and, beq_self_eq_true, Machine.closeProgram_bind,
      Machine.closeProgram_sample, Machine.closeProgram_map, Machine.closeProgram_pure,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map,
      PMF.pure_apply, ↓reduceIte]
  refine ⟨hL, ?_⟩
  rw [← exec_compose_toJoint_multiSession]
  exact hL

/-- Witness 4 (lazy sampling via `SSP.run_parFinLazy_eq_parFin` at `m = 2` touching `1, 0, 1`):
session `1` keeps the same coin across two calls while session `0` samples independently. -/
theorem lazy_sampling_witness :
    let prog : ProbOracleComp
        (SSP.sessionSpec 2 (fun _ : Unit => Bool)) Bool := do
      let b₁ ← ProbOracleComp.query ((1 : Fin 2), ())
      let b₀ ← ProbOracleComp.query ((0 : Fin 2), ())
      let b₁' ← ProbOracleComp.query ((1 : Fin 2), ())
      pure (decide (b₁ = b₁' ∧ b₀ = b₁))
    ((SSP.parFinLazy (fun _ : Fin 2 => coinMachine)).run prog).eval true = (2 : ENNReal)⁻¹ ∧
      ((SSP.parFin (fun _ : Fin 2 => coinMachine)).run prog).eval true = (2 : ENNReal)⁻¹ := by
  intro prog
  have hE : ((SSP.parFin (fun _ : Fin 2 => coinMachine)).run prog).eval true =
      (2 : ENNReal)⁻¹ := by
    simp only [Machine.run, Machine.link, SSP.parFin, coinMachine, prog,
      OracleComp.pi_succ, OracleComp.pi_zero, Machine.runFrom_bind, Machine.runFrom_query,
      Machine.runFrom_pure, Machine.closeProgram_bind, Machine.closeProgram_sample,
      Machine.closeProgram_map, Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, ProbComp.eval_unifFin, pure_bind, map_bind, Functor.map_map,
      bind_map_left, StateT.run, Fin.cons_zero, PMF.bind_bind, PMF.pure_bind, PMF.pure_map,
      show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
    simp only [PMF.bind_apply, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
      tsum_fintype, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, PMF.pure_apply,
      Nat.one_ne_zero, decide_false, decide_true]
    rw [← mul_add]
    simp [ENNReal.inv_two_add_inv_two]
  refine ⟨?_, hE⟩
  rw [SSP.run_parFinLazy_eq_parFin]
  exact hE

private def backdoorAdv : ExecAdversary 2 Unit Bool
    (Unit ⊕ RoutedNetQ 2 (SubSessionInput (Fin 2) Unit) (SubSessionBackdoor (Fin 2) Unit))
    (Unit ⊕ RoutedNetR Bool Bool) (Fin 2) Bool :=
  fun _ _ => {
    State := Unit
    init := pure ()
    handle | j, () => do
      let r ← ProbOracleComp.query (.inr (.inr (.inr ⟨j, ()⟩)))
      pure (Sum.elim (fun _ => false) (Sum.elim (fun _ => false)
        (Sum.elim (fun _ => false) id)) r, ()) }

private def backdoorEnv (iPoll : Fin 2) : Environment 2 Unit Bool (Fin 2) Bool :=
  fun _ _ => do
    let bBack ← ProbOracleComp.query (.inr (0 : Fin 2))
    let bPoll ← ProbOracleComp.query (.inl (iPoll, ()))
    pure (some bBack == bPoll)

private def backdoorRelay : MultiHybridProtocol 2 2 Unit Bool Unit Unit Unit Bool :=
  fun _ _ => {
    State := Unit
    init := pure ()
    handle
      | .inl (p, _), _ => do
        let r ← ProbOracleComp.query ⟨p, p, ()⟩
        pure (r, ())
      | .inr _, _ => pure ((), ()) }

private theorem backdoor_creation_prefix (iPoll : Fin 2) :
    let pollProb : Bool → ENNReal := fun b₀ =>
      (match Function.update (fun _ : Fin 2 => (none : Option Bool)) 0 (some b₀) iPoll with
      | some st => PMF.pure (some b₀ == some st)
      | none =>
        (Probability.PMF.uniformOfFintype (Fin 2)).bind fun r =>
          PMF.pure (some b₀ == some (decide (r.val = 0)))) true
    (exec (compose backdoorRelay.toJoint (coinBackdoorFunc.multiSession (Fin 2)).toProtocol)
        backdoorAdv ∅ (backdoorEnv iPoll) 0 []).eval true =
      (2 : ENNReal)⁻¹ * pollProb true + (2 : ENNReal)⁻¹ * pollProb false := by
  intro pollProb
  have hA : (liftAdversary (n := 2) (In := Unit) (Out := Bool) (backdoorAdv 0 ∅)).link
      (backdoorEnv iPoll 0 []) =
      (ProbOracleComp.query (.inr (.inr (.inr (.inr ⟨(0 : Fin 2), ()⟩)))) >>= fun r =>
        ProbOracleComp.query (.inl (iPoll, ())) >>= fun bPoll =>
          pure (some (Sum.elim (fun _ => false) (Sum.elim (fun _ => false)
            (Sum.elim (fun _ => false) id)) r) == bPoll)) := by
    rw [Machine.link]
    dsimp only [liftAdversary, backdoorAdv, backdoorEnv]
    erw [ProbOracleComp.sample_pure, pure_bind]
  rw [exec, execMachine, compose, corruptRouter_comp, Machine.run_comp, Machine.run_comp, hA]
  erw [link_routeCorrupt_hybridWrap_inr_inl _ _ (() : Unit) rfl]
  simp only [Finset.notMem_empty, ↓reduceIte, MultiHybridProtocol.toJoint, backdoorRelay,
    StateT.run]
  erw [liftParty_toJoint_one]
  simp only [map_bind, map_pure, bind_assoc, pure_bind, Sum.elim_inr]
  simp only [pure_bind, bind_map_left, Machine.run, Machine.link, corruptRouter,
    coinBackdoorFunc, IdealFunctionality.multiSession, IdealFunctionality.toProtocol,
    Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
    ProbOracleComp.sample_pure, StateT.run_map, map_bind,
    Finset.notMem_empty, ↓reduceIte]
  simp only [StateT.run, Machine.closeProgram_bind, Machine.closeProgram_sample,
    Machine.closeProgram_map, Machine.closeProgram_pure, ProbComp.eval_map, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_unifFin, PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
  simp only [PMF.bind_apply, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
    tsum_fintype, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, decide_true,
    decide_false, Nat.one_ne_zero]
  simp only [Sum.elim_inr, id_eq, pure_bind, PMF.pure_apply, pollProb]
  by_cases hPoll : iPoll = 0
  · simp only [hPoll, Function.update_self, ProbComp.eval_pure, PMF.pure_apply]
    rw [tsum_ite_mul_eq, tsum_ite_mul_eq]
    simp
  · simp only [Function.update_of_ne hPoll, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_unifFin, PMF.bind_apply, Probability.PMF.uniformOfFintype_apply,
      Fintype.card_fin, tsum_fintype, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one,
      decide_true, decide_false, Nat.one_ne_zero, PMF.pure_apply]
    rw [tsum_ite_add_mul_eq, tsum_ite_add_mul_eq]
    simp

/-- Witness 5 (creation by a backdoor query): first touching copy `0` via backdoor query `⟨0, ()⟩`
initializes copy `0` (`Pr[backdoor = poll₀] = 1`), copy `1` stays independent
(`Pr[backdoor₀ = poll₁] = 1/2`), and the nontrivial `Bool` backdoor passes through
`exec_compose_toJoint_multiSession`. -/
theorem backdoor_creation_witness :
    let A : ExecAdversary 2 Unit Bool
        (Unit ⊕ RoutedNetQ 2 (SubSessionInput (Fin 2) Unit) (SubSessionBackdoor (Fin 2) Unit))
        (Unit ⊕ RoutedNetR Bool Bool) (Fin 2) Bool := backdoorAdv
    let Zsame : Environment 2 Unit Bool (Fin 2) Bool := backdoorEnv 0
    let Zind : Environment 2 Unit Bool (Fin 2) Bool := backdoorEnv 1
    let ρ : MultiHybridProtocol 2 2 Unit Bool Unit Unit Unit Bool := backdoorRelay
    (exec (compose ρ.toJoint (coinBackdoorFunc.multiSession (Fin 2)).toProtocol)
        A ∅ Zsame 0 []).eval true = 1 ∧
      (exec (composeMulti ρ coinBackdoorFunc.toProtocol)
        (jointDemux A) ∅ Zsame 0 []).eval true = 1 ∧
      (exec (compose ρ.toJoint (coinBackdoorFunc.multiSession (Fin 2)).toProtocol)
        A ∅ Zind 0 []).eval true = (2 : ENNReal)⁻¹ ∧
      (exec (composeMulti ρ coinBackdoorFunc.toProtocol)
        (jointDemux A) ∅ Zind 0 []).eval true = (2 : ENNReal)⁻¹ := by
  intro A Zsame Zind ρ
  have hSame : (exec (compose ρ.toJoint (coinBackdoorFunc.multiSession (Fin 2)).toProtocol)
      A ∅ Zsame 0 []).eval true = 1 := by
    rw [show Zsame = backdoorEnv 0 from rfl, backdoor_creation_prefix 0]
    simp [Function.update_self, PMF.pure_apply, ENNReal.inv_two_add_inv_two]
  have hInd : (exec (compose ρ.toJoint (coinBackdoorFunc.multiSession (Fin 2)).toProtocol)
      A ∅ Zind 0 []).eval true = (2 : ENNReal)⁻¹ := by
    rw [show Zind = backdoorEnv 1 from rfl, backdoor_creation_prefix 1]
    simp [PMF.bind_apply, Probability.PMF.uniformOfFintype_apply, tsum_fintype, Fin.sum_univ_two,
      ← mul_add, ENNReal.inv_two_add_inv_two]
  refine ⟨hSame, ?_, hInd, ?_⟩
  · rw [← exec_compose_toJoint_multiSession]
    exact hSame
  · rw [← exec_compose_toJoint_multiSession]
    exact hInd

/-! ### End-to-end joint-state composition -/

/-- Non-vacuous reverse joint-state corollary on `orOuter`, `faultyRelay`, and `idealRelay`:
two sessions of `faultyRelay` emulate `orOuter.toJoint` composed with
`idealRelay.multiSession (Fin 2)`. -/
theorem orOuter_faultyRelay_emulates_toJoint :
    Emulates (composeMulti orOuter faultyRelay)
      (compose orOuter.toJoint (idealRelay.multiSession (Fin 2)).toProtocol) :=
  Realizes.composeMulti_toJoint orOuter_polyBounded faultyRelay_polyBounded
    idealRelay_polyBounded faultyRelay_realizes

/-- At `κ = 0`, for the fixed dummy adversary and the fixed simulator
`jointMux (multiHybridSim fun _ => dummyAdversary 2 _ _)`, the distinguishing advantage between
the two worlds of `orOuter_faultyRelay_emulates_toJoint` is `3 / 4`. This shows the two worlds
differ (the error is not identically zero); it does not refute `Emulates` (the flip probability is
`1 / 2 ^ (κ + 1)`, so the error is negligible in `κ`). -/
theorem orOuter_faultyRelay_toJoint_advantage_zero :
    advantage (composeMulti orOuter faultyRelay)
      (compose orOuter.toJoint (idealRelay.multiSession (Fin 2)).toProtocol)
      (dummyAdversary 2 _ _) (jointMux (multiHybridSim fun _ => dummyAdversary 2 _ _))
      ∅ (zOr 0) 0 [] = 3 / 4 := by
  simp only [advantage, Game.advantage]
  rw [← exec_composeMulti_toJoint]
  exact (composeMulti_orOuter_nonvacuity ∅ 0 (by simp)).1

/-- Signature check for `Realizes.compose_toJoint` with identity `ρHat` via `Emulates.refl`
(not a non-trivial security witness). -/
example :
    Emulates (compose orOuter.toJoint (idealRelay.multiSession (Fin 2)).toProtocol)
      (composeMulti orOuter idealRelay.toProtocol) :=
  Realizes.compose_toJoint orOuter_polyBounded (Emulates.refl _)

/-- Signature check for `Realizes.compose_toJoint_trans` on `orOuter` and `idealRelay` with a
hypothetical outer realization `hρG` (not a security witness). -/
example {GQ GR : Type} (G : IdealFunctionality 2 Bool Bool GQ GR)
    (hρG : Realizes (composeMulti orOuter idealRelay.toProtocol) G) :
    Realizes (compose orOuter.toJoint (idealRelay.multiSession (Fin 2)).toProtocol) G :=
  Realizes.compose_toJoint_trans orOuter_polyBounded (Emulates.refl _) hρG

/-- Signature check for `RealizesWithin.compose_toJoint` with identity `ρHat` via
`EmulatesWithin.refl`, confirming the explicit overhead polynomial (not a security witness). -/
example :
    EmulatesWithin (compose orOuter.toJoint (idealRelay.multiSession (Fin 2)).toProtocol)
      (composeMulti orOuter idealRelay.toProtocol)
      (Polynomial.X + compSimPoly (Polynomial.X.comp (Polynomial.X + 1) + 1))
      (fun _ _ _ => 0) :=
  RealizesWithin.compose_toJoint orOuter_polyBounded (EmulatesWithin.refl _)

end CslibFrontierTests.Crypto.UCJointState
