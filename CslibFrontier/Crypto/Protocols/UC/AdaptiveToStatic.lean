/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Adaptive

/-!
# Static emulation from adaptive emulation (`AdaptiveToStatic`)

Derives static UC emulation from adaptive UC emulation by clamping adversaries
(`AdaptiveAdversary.clampStatic`) and inspecting post-execution corruption sets via `.status`
(`AdaptiveEmulatesWithin.static_of_adaptive`, `AdaptiveEmulates.static_of_adaptive`).

These reductions are a sanity bridge checking consistency between the `.adaptive` and `.static`
modes in the snapshot corruption model (`UC.Adaptive`), rather than a theorem stated in
[Canetti2020]: checking whether the simulator corrupted any party outside `A.initial κ` costs one
environment query, shifting the environment-budget argument in `AdaptiveEmulatesWithin` from `pZ`
to `pZ + 1`.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open Machine (closeEval closeEval_pure closeEval_bind closeEval_map closeEval_sample
  mem_support_closeEval_pure mem_support_closeEval_bind mem_support_closeEval_map
  closeEval_bind_le mem_support_closeEval_runFrom_invariant)
open scoped ENNReal NNReal

section AdaptiveToStatic

variable {n : ℕ} {In Out NetQ NetR View AdvQ AdvR : Type}
variable {NetQ₁ NetR₁ View₁ NetQ₂ NetR₂ View₂ : Type}

/-- Lifting a private uniform-choice query past `adaptivePartySpec n In Out` yields the
corresponding `ProbOracleComp.sample`. -/
theorem liftAdaptiveNet_unifFin {Q R : Type} (k : ℕ) :
    Machine.liftRightProgram (adaptivePartySpec n In Out)
        (OracleComp.query (spec := probOracleSpec (netSpec Q R)) (Sum.inl k)) =
      ProbOracleComp.sample (ProbComp.unifFin k) := by
  simp only [Machine.liftRightProgram, ProbOracleComp.sample, ProbComp.unifFin,
    OracleComp.interpret_query, sumHandler, OracleComp.substitute_query]

/-- Rewrite an adaptive network program to drop `.corrupt i` queries for `i ∉ C₀` (returning
`pure (.corrupt none)`), matching `.static` router behavior. -/
@[expose] def clampNetProgram (C₀ : Finset (Fin n)) {α : Type}
    (program : ProbOracleComp
      (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α) :
    ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec
        (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))) (Sum.inl k))
      fun q => match q with
        | .party i x => ProbOracleComp.query (.party i x)
        | .corrupt i =>
            if i ∈ C₀ then ProbOracleComp.query (.corrupt i) else pure (.corrupt none)
        | .net nq => ProbOracleComp.query (.net nq))
    program

private theorem isQueryBounded_clampNetProgram (C₀ : Finset (Fin n)) {α : Type}
    {program : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α}
    {m : ℕ} (h : program.IsQueryBounded m) :
    (clampNetProgram (n := n) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      (View := View) C₀ program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  rcases q with k | (⟨i, x⟩ | i | nq)
  · exact OracleComp.IsCostBounded.query _
  · exact OracleComp.IsCostBounded.query _
  · dsimp only [sumHandler, Sum.elim_inr]
    split_ifs
    · exact OracleComp.IsCostBounded.query _
    · exact OracleComp.IsCostBounded.pure _ 1
  · exact OracleComp.IsCostBounded.query _

private theorem noNewCorrupt_clampNetProgram (C₀ : Finset (Fin n)) {α : Type}
    (program : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α) :
    NoNewCorruptProgram C₀ (clampNetProgram C₀ program) := by
  induction program using OracleComp.induction with
  | pure _ => exact .pure _
  | query_bind q _ ih =>
    simp only [PFunctor.FreeM.bind_eq_bind]
    rcases q with k | (⟨i, x⟩ | i | nq)
    · exact .bind (.query trivial) ih
    · exact .bind (.query trivial) ih
    · rw [clampNetProgram, OracleComp.interpret_bind, OracleComp.interpret_query]
      dsimp only [sumHandler]
      by_cases hi : i ∈ C₀ <;> simp only [hi, ↓reduceIte, pure_bind]
      · exact .bind (.query hi) ih
      · exact ih (.corrupt none)
    · exact .bind (.query trivial) ih

/-- Clamp an adaptive adversary so it drops any `.corrupt i` query for `i ∉ A.initial κ`. -/
@[expose] def AdaptiveAdversary.clampStatic
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) :
    AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR where
  initial := A.initial
  machine κ := {
    State := (A.machine κ).State
    init := (A.machine κ).init
    handle q s := clampNetProgram (A.initial κ) (((A.machine κ).handle q).run s) }

/-- A clamped adaptive adversary never queries `.corrupt i` for `i ∉ A.initial κ`. -/
theorem AdaptiveAdversary.noNewCorrupt_clampStatic
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) :
    A.clampStatic.NoNewCorrupt :=
  fun κ q s => noNewCorrupt_clampNetProgram (A.initial κ) (((A.machine κ).handle q).run s)

/-- Clamping an adaptive adversary preserves its call budget. -/
theorem AdaptiveAdversary.PolyBounded.clampStatic
    {A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR} {pA : Polynomial ℕ}
    (hA : A.PolyBounded pA) : A.clampStatic.PolyBounded pA := fun κ =>
  ⟨(hA κ).1, fun q s => isQueryBounded_clampNetProgram (A.initial κ) ((hA κ).2 q s)⟩

private def clampRouterHandler (C₀ : Finset (Fin n)) :
    AdaptiveNetQ n In NetQ →
      ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR View)
        (AdaptiveNetR Out NetR View)
  | .party i x =>
      ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View)
        (.inr (.party i x))
  | .corrupt i =>
      if i ∈ C₀ then
        ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View)
          (.inr (.corrupt i))
      else pure (.corrupt none)
  | .net nq =>
      ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View) (.inr (.net nq))

private theorem liftAdaptiveNet_clampNetProgram (C₀ : Finset (Fin n)) {α : Type}
    (netProg : ProbOracleComp
      (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α) :
    liftAdaptiveNet (n := n) (In := In) (Out := Out) (clampNetProgram C₀ netProg) =
      OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query
            (spec := probOracleSpec (adaptiveProtocolSpec n In Out NetQ NetR View)) (.inl k))
          (clampRouterHandler C₀))
        netProg := by
  dsimp only [liftAdaptiveNet, Machine.liftRightProgram, clampNetProgram]
  erw [OracleComp.interpret_interpret]
  congr 1 with q
  rcases q with k | (⟨i, x⟩ | i | nq)
  · rfl
  · exact ProbOracleComp.interpret_query _ _ _
  · dsimp only [sumHandler, clampRouterHandler]
    split_ifs
    · exact ProbOracleComp.interpret_query _ _ _
    · rfl
  · exact ProbOracleComp.interpret_query _ _ _

private theorem runFrom_adaptiveRouter_clampNetProgram_static {α β : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (rs : AdaptiveRouterState (P.machine κ).State View n) (hrs : rs.corrupted = C₀)
    (f g : α × AdaptiveRouterState (P.machine κ).State View n → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a rs', rs'.corrupted = C₀ → f (a, rs') = g (a, rs')) :
    ((adaptiveRouter .static P κ C₀).runFrom (liftAdaptiveNet (clampNetProgram C₀ netProg)) rs >>=
        f) =
      ((adaptiveRouter .static P κ C₀).runFrom (liftAdaptiveNet netProg) rs >>= g) := by
  rw [liftAdaptiveNet_clampNetProgram]
  refine Machine.runFrom_interpret_intertwine
    (adaptiveRouter .static P κ C₀) (adaptiveRouter .static P κ C₀)
    (clampRouterHandler C₀)
    (fun q =>
      ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View) (.inr q))
    (fun _ => True) (fun rs₁ rs₂ => rs₁ = rs₂ ∧ rs₁.corrupted = C₀)
    netProg (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    rs rs ⟨rfl, hrs⟩ f g (fun a rs₁ _ hR => hR.1 ▸ hfg a rs₁ hR.2)
    fun q rs₁ _ k₁ k₂ _ ⟨rfl, hrs₁⟩ hcont => ?_
  cases q with
  | party i x =>
    dsimp only [clampRouterHandler]
    erw [Machine.runFrom_query]; dsimp only [adaptiveRouter, StateT.run]
    by_cases hi : i ∈ rs₁.corrupted <;> simp only [hi, ↓reduceIte]
    · erw [bind_assoc, bind_assoc]
      exact bind_congr fun ⟨out, _⟩ => by erw [pure_bind]; exact hcont (.party out) _ _ ⟨rfl, hrs₁⟩
    · erw [pure_bind]; exact hcont (.party none) _ _ ⟨rfl, hrs₁⟩
  | net nq =>
    dsimp only [clampRouterHandler]
    erw [Machine.runFrom_query]; dsimp only [adaptiveRouter, StateT.run]
    erw [bind_assoc, bind_assoc]
    exact bind_congr fun ⟨r, _⟩ => by erw [pure_bind]; exact hcont (.net r) _ _ ⟨rfl, hrs₁⟩
  | corrupt i =>
    dsimp only [clampRouterHandler]
    by_cases hi : i ∈ C₀ <;> simp only [hi, ↓reduceIte]
    · have hi' : i ∈ rs₁.corrupted := hrs₁ ▸ hi
      erw [Machine.runFrom_query]; dsimp only [adaptiveRouter, StateT.run]
      simp only [hi', ↓reduceIte]; erw [pure_bind]
      exact hcont (.corrupt (some (P.corruptionReport κ i rs₁))) _ _ ⟨rfl, hrs₁⟩
    · have hi' : i ∉ rs₁.corrupted := hrs₁ ▸ hi
      erw [Machine.runFrom_pure, Machine.runFrom_query]; dsimp only [adaptiveRouter, StateT.run]
      simp only [hi', ↓reduceIte]; erw [pure_bind]
      exact hcont (.corrupt none) _ _ ⟨rfl, hrs₁⟩

/-- Clamping `A` does not change `.static` execution. -/
theorem adaptiveExec_static_clampStatic
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec .static P A.clampStatic Z κ z = adaptiveExec .static P A Z κ z := by
  simp only [adaptiveExec, Machine.run, Machine.link]
  refine congrArg Machine.closeProgram ?_
  erw [sample_adaptiveExecMachine_init, sample_adaptiveExecMachine_init]
  refine bind_congr fun s₀ => bind_congr fun sA =>
    runFrom_adaptiveExecMachine_intertwine .static .static P A.clampStatic A κ Eq
      (fun a sA₁ _ rs _ _ hA hrs hcont => by
        subst hA
        exact runFrom_adaptiveRouter_clampNetProgram_static P κ (A.initial κ)
          (((A.machine κ).handle a).run sA₁) rs hrs _ _ fun res rs' hrs' =>
          hcont res.1 res.2 res.2 rs' rfl hrs')
      (Z κ z) sA sA rfl _ rfl

/-- In `.static` mode, any adversary `A` executes identically to `A.clampStatic` in `.adaptive`
mode. -/
theorem adaptiveExec_static_eq_adaptive_clampStatic
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec .static P A Z κ z = adaptiveExec .adaptive P A.clampStatic Z κ z :=
  (adaptiveExec_static_clampStatic P A Z κ z).symm.trans
    (adaptiveExec_static_eq_adaptive_of_noCorrupt P A.clampStatic A.noNewCorrupt_clampStatic
      Z κ z)

/-! #### Closing and evaluating joint router states for `static_of_adaptive` -/

private noncomputable def execState (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    {α : Type} (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (κ : ℕ) :
    PMF (α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n)) :=
  closeEval (ProbOracleComp.sample (adaptiveExecMachine mode P A κ).init >>=
    fun s => (adaptiveExecMachine mode P A κ).runFrom program s)

private def queryStatus :
    ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) (Finset (Fin n)) :=
  ProbOracleComp.query (spec := adaptiveExecSpec n In Out AdvQ AdvR) (.inl .status)

private theorem eval_adaptiveExec_eq_execState_map (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    (adaptiveExec mode P A Z κ z).eval = (execState mode P A (Z κ z) κ).map Prod.fst := by
  change closeEval _ = (closeEval _).map Prod.fst
  erw [closeEval_bind, closeEval_bind, PMF.map_bind]
  exact congrArg (PMF.bind _) (funext fun _ => closeEval_map _ _)

private theorem eval_adaptiveExec_status_post (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (f : Bool → Finset (Fin n) → Bool)
    (κ : ℕ) (z : List Bool) :
    (adaptiveExec mode P A (fun κ z => do
        let b ← Z κ z
        let C ← queryStatus
        pure (f b C)) κ z).eval =
      (execState mode P A (Z κ z) κ).map fun x => f x.1 x.2.2.corrupted := by
  change closeEval _ = (closeEval _).map _
  have hrun (s : (adaptiveExecMachine mode P A κ).State) :
      Prod.fst <$> (adaptiveExecMachine mode P A κ).runFrom
          (Z κ z >>= fun b => queryStatus >>= fun C => pure (f b C)) s =
        (fun x => f x.1 x.2.2.corrupted) <$>
          (adaptiveExecMachine mode P A κ).runFrom (Z κ z) s := by
    rcases s with ⟨sA, rs⟩
    erw [Machine.runFrom_bind, map_eq_pure_bind, map_eq_pure_bind, bind_assoc]
    refine bind_congr fun ⟨b, sA', rs'⟩ => ?_
    erw [Machine.runFrom_bind, queryStatus, Machine.runFrom_query,
      adaptiveExecMachine_handle_inl_status]
    simp only [Machine.runFrom_pure]; rfl
  erw [closeEval_bind, closeEval_bind, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun s => ?_)
  erw [hrun s, closeEval_map]; rfl

private theorem queriesSatisfy_liftAdaptiveNet {C₀ : Finset (Fin n)} {α : Type}
    {netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α}
    (hno : NoNewCorruptProgram C₀ netProg) :
    OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => match q with | .inr (.corrupt i) => i ∈ C₀ | _ => True)
      (liftAdaptiveNet (n := n) (In := In) (Out := Out) netProg) := by
  induction netProg using OracleComp.induction with
  | pure _ => exact .pure _
  | query_bind q _ ih =>
    simp only [PFunctor.FreeM.bind_eq_bind] at hno ⊢
    have hq := OracleComp.QueriesSatisfy.liftBind_iff.mp hno
    dsimp only [liftAdaptiveNet]
    rcases q with k | q
    · rw [Machine.liftRightProgram_bind, liftAdaptiveNet_unifFin]
      exact .bind (.query trivial) fun a => ih a (hq.2 a)
    · rw [Machine.liftRightProgram_bind]; erw [Machine.liftRightProgram_query]
      refine .bind (.query ?_) fun a => ih a (hq.2 a)
      cases q <;> exact hq.1

private theorem corrupted_rel_of_mem_support_router {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (InvC : Fin n → Prop) (R : Finset (Fin n) → Finset (Fin n) → Prop)
    (hR_refl : ∀ C, R C C) (hR_trans : ∀ {a b c}, R a b → R b c → R a c)
    (hinv : OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => match q with | .inr (.corrupt i) => InvC i | _ => True)
      (liftAdaptiveNet (n := n) (In := In) (Out := Out) netProg))
    (hcor : ∀ C i, InvC i → R C (if i ∈ C then C else insert i C))
    (rs : AdaptiveRouterState (P.machine κ).State View n)
    {x : α × AdaptiveRouterState (P.machine κ).State View n}
    (hx : x ∈ (closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
      (liftAdaptiveNet netProg) rs)).support) :
    R rs.corrupted x.2.corrupted := by
  refine mem_support_closeEval_runFrom_invariant (adaptiveRouter .adaptive P κ C₀)
    (fun q => match q with | .inr (.corrupt i) => InvC i | _ => True)
    (fun s₁ s₂ => R s₁.corrupted s₂.corrupted)
    (fun _ => hR_refl _) hR_trans (liftAdaptiveNet netProg) hinv rs hx
    fun q s' y hq hy => ?_
  dsimp only [adaptiveRouter, adaptiveProtocolSpec, adaptivePartySpec, netSpec,
    StateT.run] at s' y hy ⊢
  rcases q with (⟨i, u⟩ | _) | (⟨i, u⟩ | i | nq)
  · by_cases hi : i ∈ s'.corrupted <;> simp only [hi, ↓reduceIte] at hy
    · rcases mem_support_closeEval_pure.mp hy with rfl; exact hR_refl _
    · rcases mem_support_closeEval_bind.mp hy with ⟨_, _, hy'⟩
      rcases mem_support_closeEval_pure.mp hy' with rfl; exact hR_refl _
  · rcases mem_support_closeEval_pure.mp hy with rfl; exact hR_refl _
  · by_cases hi : i ∈ s'.corrupted <;> simp only [hi, ↓reduceIte] at hy
    · rcases mem_support_closeEval_bind.mp hy with ⟨_, _, hy'⟩
      rcases mem_support_closeEval_pure.mp hy' with rfl; exact hR_refl _
    · rcases mem_support_closeEval_pure.mp hy with rfl; exact hR_refl _
  · rcases mem_support_closeEval_pure.mp hy with rfl
    by_cases hi : i ∈ s'.corrupted <;> simpa [hi] using hcor s'.corrupted i hq
  · rcases mem_support_closeEval_bind.mp hy with ⟨_, _, hy'⟩
    rcases mem_support_closeEval_pure.mp hy' with rfl; exact hR_refl _

private theorem corrupted_rel_of_mem_support_execMachine {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (InvC : Fin n → Prop) (R : Finset (Fin n) → Finset (Fin n) → Prop)
    (hR_refl : ∀ C, R C C) (hR_trans : ∀ {a b c}, R a b → R b c → R a c)
    (hadv : ∀ a sA', OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => match q with | .inr (.corrupt i) => InvC i | _ => True)
      (liftAdaptiveNet (n := n) (In := In) (Out := Out) (((A.machine κ).handle a).run sA')))
    (hcor : ∀ C i, InvC i → R C (if i ∈ C then C else insert i C))
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n)
    {x : α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n)}
    (hx : x ∈
      (closeEval ((adaptiveExecMachine .adaptive P A κ).runFrom program (sA, rs))).support) :
    R rs.corrupted x.2.2.corrupted := by
  refine mem_support_closeEval_runFrom_invariant (adaptiveExecMachine .adaptive P A κ)
    (fun _ => True) (fun s₁ s₂ => R s₁.2.corrupted s₂.2.corrupted)
    (fun _ => hR_refl _) hR_trans program
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _) (sA, rs) hx
    fun q ⟨sA', rs'⟩ y _ hy => ?_
  rcases q with (⟨i, u⟩ | _) | a
  · erw [adaptiveExecMachine_handle_inl_party] at hy
    by_cases hi : i ∈ rs'.corrupted <;> simp only [hi, ↓reduceIte] at hy
    · rcases mem_support_closeEval_pure.mp hy with rfl; exact hR_refl _
    · rcases mem_support_closeEval_bind.mp hy with ⟨_, _, hy'⟩
      rcases mem_support_closeEval_pure.mp hy' with rfl; exact hR_refl _
  · erw [adaptiveExecMachine_handle_inl_status] at hy
    rcases mem_support_closeEval_pure.mp hy with rfl; exact hR_refl _
  · change y ∈ (closeEval ((fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
        (adaptiveRouter .adaptive P κ (A.initial κ)).runFrom
          (liftAdaptiveNet (((A.machine κ).handle a).run sA')) rs')).support at hy
    rcases mem_support_closeEval_map.mp hy with ⟨⟨⟨r, sA''⟩, rs''⟩, hz, rfl⟩
    exact corrupted_rel_of_mem_support_router P κ (A.initial κ) _ InvC R hR_refl hR_trans
      (hadv a sA') hcor rs' (x := ((r, sA''), rs'')) hz

/-- Any support state of `adaptiveRouter .adaptive P κ C₀` run on `liftAdaptiveNet netProg`
contains the starting corruption set `rs.corrupted`. -/
theorem corrupted_subset_of_mem_support_router {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (rs : AdaptiveRouterState (P.machine κ).State View n)
    {x : α × AdaptiveRouterState (P.machine κ).State View n}
    (hx : x ∈ (closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
      (liftAdaptiveNet netProg) rs)).support) :
    rs.corrupted ⊆ x.2.corrupted :=
  corrupted_rel_of_mem_support_router P κ C₀ netProg (fun _ => True) (· ⊆ ·)
    (fun _ => Finset.Subset.rfl) Finset.Subset.trans
    (OracleComp.QueriesSatisfy.of_forall (fun q => by rcases q with _ | (_ | _ | _) <;> trivial) _)
    (fun C i _ => by split_ifs <;> simp [Finset.subset_insert]) rs hx

private theorem corrupted_eq_of_mem_support_execState_noNewCorrupt
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (hno : A.NoNewCorrupt) {α : Type}
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α) (κ : ℕ)
    {x : α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n)}
    (hx : x ∈ (execState .adaptive P A program κ).support) :
    x.2.2.corrupted = A.initial κ := by
  simp only [execState] at hx
  erw [sample_adaptiveExecMachine_init] at hx
  rcases mem_support_closeEval_bind.mp hx with ⟨s₀, _, hx⟩
  rcases mem_support_closeEval_bind.mp hx with ⟨sA, _, hx⟩
  exact corrupted_rel_of_mem_support_execMachine P A κ program (· ∈ A.initial κ)
    (fun C₁ C₂ => C₁ = A.initial κ → C₂ = A.initial κ)
    (fun _ h => h) (fun h₁ h₂ hc => h₂ (h₁ hc))
    (fun a sA' => queriesSatisfy_liftAdaptiveNet (hno κ a sA'))
    (fun C i hi hC => by subst C; simp [hi]) sA _ hx rfl

private theorem closeEval_router_adaptive_le_clamp {α β : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (rs : AdaptiveRouterState (P.machine κ).State View n) (hrs : rs.corrupted = C₀)
    (f g : α × AdaptiveRouterState (P.machine κ).State View n → ProbOracleComp OracleSpec.empty β)
    (y : β)
    (hfg : ∀ (a : α) (rs₁ : AdaptiveRouterState (P.machine κ).State View n),
      rs₁.corrupted = C₀ → closeEval (f (a, rs₁)) y ≤ closeEval (g (a, rs₁)) y)
    (hzero : ∀ (a : α) (rs₁ : AdaptiveRouterState (P.machine κ).State View n),
      ¬ (rs₁.corrupted ⊆ C₀) → closeEval (f (a, rs₁)) y = 0) :
    closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
        (liftAdaptiveNet netProg) rs >>= f) y ≤
      closeEval ((adaptiveRouter .adaptive P κ C₀).runFrom
        (liftAdaptiveNet (clampNetProgram C₀ netProg)) rs >>= g) y := by
  rw [liftAdaptiveNet_clampNetProgram]
  refine Machine.closeEval_runFrom_interpret_le_intertwine
    (adaptiveRouter .adaptive P κ C₀) (adaptiveRouter .adaptive P κ C₀)
    (fun q => ProbOracleComp.query (spec := adaptiveProtocolSpec n In Out NetQ NetR View) (.inr q))
    (clampRouterHandler C₀)
    (fun _ => True) (fun rs₁ rs₂ => rs₁ = rs₂ ∧ rs₁.corrupted = C₀)
    (fun rs₁ => ¬ rs₁.corrupted ⊆ C₀)
    netProg (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    rs rs ⟨rfl, hrs⟩ f g y
    (fun a rs₁ _ hR => hR.1 ▸ hfg a rs₁ hR.2) hzero
    (fun q s₁' z _ hT hz hsub => hT ((corrupted_subset_of_mem_support_router P κ C₀
      (ProbOracleComp.query q) s₁' (x := z) (by
        erw [liftAdaptiveNet, Machine.liftRightProgram_query]; exact hz)).trans hsub))
    fun q rs₁ _ k₁ k₂ _ ⟨rfl, hrs₁⟩ hcont htrap => ?_
  cases q with
  | party i u =>
    dsimp only [clampRouterHandler]
    erw [Machine.runFrom_query]; dsimp only [adaptiveRouter, StateT.run]
    by_cases hi : i ∈ rs₁.corrupted <;> simp only [hi, ↓reduceIte]
    · erw [bind_assoc, bind_assoc]
      refine closeEval_bind_le _ _ _ y fun ⟨out, s'⟩ => ?_
      erw [pure_bind, pure_bind]; exact hcont (.party out) _ _ ⟨rfl, hrs₁⟩
    · erw [pure_bind, pure_bind]; exact hcont (.party none) _ _ ⟨rfl, hrs₁⟩
  | net nq =>
    dsimp only [clampRouterHandler]
    erw [Machine.runFrom_query]; dsimp only [adaptiveRouter, StateT.run]
    erw [bind_assoc, bind_assoc]
    refine closeEval_bind_le _ _ _ y fun ⟨r, s'⟩ => ?_
    erw [pure_bind, pure_bind]; exact hcont (.net r) _ _ ⟨rfl, hrs₁⟩
  | corrupt i =>
    dsimp only [clampRouterHandler]
    by_cases hi : i ∈ C₀ <;> simp only [hi, ↓reduceIte]
    · have hi' : i ∈ rs₁.corrupted := hrs₁ ▸ hi
      erw [Machine.runFrom_query]; dsimp only [adaptiveRouter, StateT.run]
      simp only [hi', ↓reduceIte]; erw [pure_bind]
      exact hcont (.corrupt (some (P.corruptionReport κ i rs₁))) _ _ ⟨rfl, hrs₁⟩
    · have hi' : i ∉ rs₁.corrupted := hrs₁ ▸ hi
      erw [Machine.runFrom_query, Machine.runFrom_pure]
      dsimp only [adaptiveRouter, StateT.run] at rs₁ htrap ⊢
      simp only [hi', ↓reduceIte]; erw [pure_bind, pure_bind]
      rw [htrap _ _ fun hsub => hi (hsub (Finset.mem_insert_self i rs₁.corrupted))]
      exact zero_le

private theorem closeEval_execMachine_adaptive_le_clampStatic {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n)
    (hrs : rs.corrupted = A.initial κ)
    (y : α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n))
    (hy : y.2.2.corrupted = A.initial κ) :
    closeEval ((adaptiveExecMachine .adaptive P A κ).runFrom program (sA, rs)) y ≤
      closeEval ((adaptiveExecMachine .adaptive P A.clampStatic κ).runFrom program (sA, rs)) y := by
  suffices h :
      closeEval ((adaptiveExecMachine .adaptive P A κ).runFrom program (sA, rs) >>= pure) y ≤
        closeEval ((adaptiveExecMachine .adaptive P A.clampStatic κ).runFrom program (sA, rs) >>=
          pure) y by
    simpa only [bind_pure] using h
  refine Machine.closeEval_runFrom_le_intertwine
    (adaptiveExecMachine .adaptive P A κ) (adaptiveExecMachine .adaptive P A.clampStatic κ)
    (fun _ => True) (fun x₁ x₂ => x₁ = x₂ ∧ x₁.2.corrupted = A.initial κ)
    (fun x₁ => ¬ x₁.2.corrupted ⊆ A.initial κ)
    program (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    (sA, rs) (sA, rs) ⟨rfl, hrs⟩ pure pure y
    (fun _ _ _ hR => hR.1 ▸ le_rfl)
    (fun a s₁ hT => by
      rw [closeEval_pure]
      exact PMF.pure_apply_of_ne _ _ fun heq => by
        rcases heq with rfl; exact hT (hy ▸ Finset.Subset.rfl))
    (fun q ⟨sA', rs'⟩ z _ hT hz hsub => hT ((corrupted_rel_of_mem_support_execMachine P A κ
      (ProbOracleComp.query q) (fun _ => True) (· ⊆ ·) (fun _ => Finset.Subset.rfl)
      Finset.Subset.trans
      (fun _ _ => OracleComp.QueriesSatisfy.of_forall
        (fun r => by rcases r with _ | (_ | _ | _) <;> trivial) _)
      (fun C i _ => by split_ifs <;> simp [Finset.subset_insert]) sA' rs'
      (by erw [Machine.runFrom_query]; exact hz)).trans hsub))
    fun q ⟨sA₁, rs₁⟩ _ k₁ k₂ _ ⟨hEq, hrs₁⟩ hcont htrap => ?_
  cases hEq; rcases q with (⟨i, u⟩ | _) | a
  · erw [adaptiveExecMachine_handle_inl_party]
    by_cases hi : i ∈ rs₁.corrupted <;> simp only [hi, ↓reduceIte]
    · erw [pure_bind, pure_bind]; exact hcont none _ _ ⟨rfl, hrs₁⟩
    · erw [bind_assoc, bind_assoc]
      refine closeEval_bind_le _ _ _ y fun ⟨out, s'⟩ => ?_
      erw [pure_bind, pure_bind]; exact hcont out _ _ ⟨rfl, hrs₁⟩
  · erw [adaptiveExecMachine_handle_inl_status]
    erw [pure_bind, pure_bind]
    exact hcont rs₁.corrupted _ _ ⟨rfl, hrs₁⟩
  · change closeEval (((fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
        (adaptiveRouter .adaptive P κ (A.initial κ)).runFrom
          (liftAdaptiveNet (((A.machine κ).handle a).run sA₁)) rs₁) >>= k₁) y ≤
      closeEval (((fun (p : (AdvR × (A.machine κ).State) × _) => (p.1.1, (p.1.2, p.2))) <$>
        (adaptiveRouter .adaptive P κ (A.initial κ)).runFrom
          (liftAdaptiveNet (clampNetProgram (A.initial κ) (((A.machine κ).handle a).run sA₁)))
          rs₁) >>= k₂) y
    erw [bind_map_left, bind_map_left]
    exact closeEval_router_adaptive_le_clamp P κ (A.initial κ)
      (((A.machine κ).handle a).run sA₁) rs₁ hrs₁ _ _ y
      (fun res rs' hrs' => hcont res.1 (res.2, rs') (res.2, rs') ⟨rfl, hrs'⟩)
      fun res rs' hnot => htrap res.1 (res.2, rs') hnot

private theorem execState_adaptive_le_clampStatic {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α) (κ : ℕ)
    (y : α × ((A.machine κ).State × AdaptiveRouterState (P.machine κ).State View n))
    (hy : y.2.2.corrupted = A.initial κ) :
    execState .adaptive P A program κ y ≤ execState .adaptive P A.clampStatic program κ y := by
  simp only [execState]
  erw [sample_adaptiveExecMachine_init, sample_adaptiveExecMachine_init]
  exact closeEval_bind_le _ _ _ y fun s₀ => closeEval_bind_le _ _ _ y fun sA =>
    closeEval_execMachine_adaptive_le_clampStatic P A κ program sA _ rfl y hy

private theorem apply_true_status_post_le
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (S : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂ AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) (target : Bool) :
    let C₀ := S.initial κ
    let Z_post : AdaptiveEnvironment n In Out AdvQ AdvR := fun κ' z' => do
      let b ← Z κ' z'
      let C ← queryStatus
      pure ((b == target) && decide (C = C₀))
    (adaptiveExec .adaptive Q S Z_post κ z).eval true ≤
      (adaptiveExec .adaptive Q S.clampStatic Z κ z).eval target := by
  intro C₀ Z_post
  rw [eval_adaptiveExec_status_post, eval_adaptiveExec_eq_execState_map,
    PMF.map_apply, PMF.map_apply]
  refine tsum_le_tsum fun x => ?_
  by_cases h1 : x.1 = target <;> by_cases h2 : x.2.2.corrupted = C₀
  · simp only [h1, h2, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]
    exact execState_adaptive_le_clampStatic Q S (Z κ z) κ x h2
  all_goals simp [h1, h2, Ne.symm]

private theorem apply_true_status_post_eq_noNewCorrupt
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR) (hno : A.NoNewCorrupt)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) (target : Bool) :
    let C₀ := A.initial κ
    let Z_post : AdaptiveEnvironment n In Out AdvQ AdvR := fun κ' z' => do
      let b ← Z κ' z'
      let C ← queryStatus
      pure ((b == target) && decide (C = C₀))
    (adaptiveExec .adaptive P A Z_post κ z).eval true =
      (adaptiveExec .adaptive P A Z κ z).eval target := by
  intro C₀ Z_post
  rw [eval_adaptiveExec_status_post, eval_adaptiveExec_eq_execState_map,
    PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases hsup : execState .adaptive P A (Z κ z) κ x = 0
  · simp [hsup]
  · have hC := corrupted_eq_of_mem_support_execState_noNewCorrupt P A hno (Z κ z) κ
      ((PMF.mem_support_iff _ _).mpr hsup)
    by_cases hb : x.1 = target <;> simp [hC, C₀, hb, Ne.symm]

private theorem eval_Z_status_eq_pure
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (C₀ : Finset (Fin n)) (κ : ℕ) (z : List Bool) :
    let Z_status : AdaptiveEnvironment n In Out AdvQ AdvR := fun _ _ => do
      let C ← queryStatus
      pure (decide (C = C₀))
    (adaptiveExec .adaptive P A Z_status κ z).eval = PMF.pure (decide (A.initial κ = C₀)) := by
  intro Z_status
  change closeEval (ProbOracleComp.sample (adaptiveExecMachine .adaptive P A κ).init >>=
    fun s => Prod.fst <$> (adaptiveExecMachine .adaptive P A κ).runFrom (Z_status κ z) s) =
    PMF.pure (decide (A.initial κ = C₀))
  erw [sample_adaptiveExecMachine_init]
  have hstep (sA : (A.machine κ).State) (rs : AdaptiveRouterState (P.machine κ).State View n) :
      Prod.fst <$> (adaptiveExecMachine .adaptive P A κ).runFrom (Z_status κ z) (sA, rs) =
        pure (decide (rs.corrupted = C₀)) := by
    erw [Machine.runFrom_bind, queryStatus, Machine.runFrom_query,
      adaptiveExecMachine_handle_inl_status]
    simp only [Machine.runFrom_pure]; rfl
  rw [closeEval_bind]
  refine (congrArg (PMF.bind _) (funext fun s₀ => ?_)).trans (PMF.bind_const _ _)
  rw [closeEval_bind]
  exact (congrArg (PMF.bind _) (funext fun sA => by erw [hstep, closeEval_pure])).trans
    (PMF.bind_const _ _)

private theorem static_advantage_le_of_adaptive_clampStatic
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR)
    (S : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂ AdvQ AdvR)
    {pZ : Polynomial ℕ} {ν : ℕ → ℝ≥0}
    (hadv : ∀ (Z' : AdaptiveEnvironment n In Out AdvQ AdvR), Z'.PolyBounded (pZ + 1) →
      ∀ κ z, adaptiveAdvantage .adaptive P Q A.clampStatic S Z' κ z ≤ ν κ)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (hZ : Z.PolyBounded pZ)
    (κ : ℕ) (z : List Bool) :
    adaptiveAdvantage .static P Q A S.clampStatic Z κ z ≤ ν κ := by
  have heqP : adaptiveExec .static P A Z κ z = adaptiveExec .adaptive P A.clampStatic Z κ z :=
    adaptiveExec_static_eq_adaptive_clampStatic P A Z κ z
  have heqQ : adaptiveExec .static Q S.clampStatic Z κ z =
      adaptiveExec .adaptive Q S.clampStatic Z κ z :=
    adaptiveExec_static_eq_adaptive_of_noCorrupt Q S.clampStatic S.noNewCorrupt_clampStatic Z κ z
  rw [adaptiveAdvantage, heqP, heqQ]
  by_cases hinit : S.initial κ = A.initial κ
  · let Z_post (target : Bool) : AdaptiveEnvironment n In Out AdvQ AdvR := fun κ' z' => do
      let b ← Z κ' z'
      let C ← queryStatus
      pure ((b == target) && decide (C = A.initial κ))
    have hZ_post (target : Bool) : (Z_post target).PolyBounded (pZ + 1) := fun κ' z' => by
      exact (OracleComp.IsCostBounded.bind (hZ κ' z') fun _ =>
        OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query (cost := fun _ => 1) _)
          fun _ => OracleComp.IsCostBounded.pure _ 0).mono
        (by simp only [Polynomial.eval_add, Polynomial.eval_one]; omega)
    have hbound (target : Bool) :
        ((adaptiveExec .adaptive P A.clampStatic Z κ z).eval target).toReal -
          ((adaptiveExec .adaptive Q S.clampStatic Z κ z).eval target).toReal ≤ (ν κ : ℝ) := by
      have hPA : (adaptiveExec .adaptive P A.clampStatic (Z_post target) κ z).eval true =
          (adaptiveExec .adaptive P A.clampStatic Z κ z).eval target :=
        apply_true_status_post_eq_noNewCorrupt P A.clampStatic
          A.noNewCorrupt_clampStatic Z κ z target
      have hQS : (adaptiveExec .adaptive Q S (Z_post target) κ z).eval true ≤
          (adaptiveExec .adaptive Q S.clampStatic Z κ z).eval target := by
        dsimp only [Z_post]; rw [← hinit]
        exact apply_true_status_post_le Q S Z κ z target
      have hQS_real := ENNReal.toReal_mono (PMF.apply_ne_top _ _) hQS
      have hadv_real :
          |((adaptiveExec .adaptive P A.clampStatic Z κ z).eval target).toReal -
            ((adaptiveExec .adaptive Q S (Z_post target) κ z).eval true).toReal| ≤ (ν κ : ℝ) := by
        have h := NNReal.coe_le_coe.mpr (hadv (Z_post target) (hZ_post target) κ z)
        rwa [adaptiveAdvantage, Game.coe_advantage, Game.coe_succProbability,
          Game.coe_succProbability, hPA] at h
      linarith [(abs_sub_le_iff.mp hadv_real).1]
    have hsum (p : PMF Bool) : (p true).toReal + (p false).toReal = 1 := by
      simpa [Game.succProbability, Game.failProbability] using
        congrArg NNReal.toReal (Game.succProbability_add_failProbability p)
    rw [← NNReal.coe_le_coe, Game.coe_advantage, Game.coe_succProbability,
      Game.coe_succProbability, abs_sub_le_iff]
    exact ⟨hbound true, by
      linarith [hbound false, hsum (adaptiveExec .adaptive P A.clampStatic Z κ z).eval,
        hsum (adaptiveExec .adaptive Q S.clampStatic Z κ z).eval]⟩
  · let Z_status : AdaptiveEnvironment n In Out AdvQ AdvR := fun _ _ => do
      let C ← queryStatus
      pure (decide (C = A.initial κ))
    have hZ_status : Z_status.PolyBounded (pZ + 1) := fun κ' z' => by
      exact (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query (cost := fun _ => 1) _)
        fun _ => OracleComp.IsCostBounded.pure _ 0).mono
        (by simp only [Polynomial.eval_add, Polynomial.eval_one]; omega)
    have hadv_st := hadv Z_status hZ_status κ z
    have hP_st : (adaptiveExec .adaptive P A.clampStatic Z_status κ z).eval = PMF.pure true := by
      simpa only [AdaptiveAdversary.clampStatic, decide_true] using
        eval_Z_status_eq_pure P A.clampStatic (A.initial κ) κ z
    have hQ_st : (adaptiveExec .adaptive Q S Z_status κ z).eval = PMF.pure false := by
      simpa only [hinit, decide_false] using
        eval_Z_status_eq_pure Q S (A.initial κ) κ z
    have h1 : (1 : ℝ≥0) ≤ ν κ := by
      simpa [adaptiveAdvantage, hP_st, hQ_st, Game.succProbability] using hadv_st
    exact (Game.advantage_le_one _ _).trans h1

/-- Adaptive emulation implies static emulation (sanity bridge, not a theorem of `[Canetti2020]`).
Checking whether the simulator corrupted any party outside `A.initial κ` via `.status` costs one
environment query, shifting the error's environment-budget argument from `pZ` to `pZ + 1`. -/
theorem AdaptiveEmulatesWithin.static_of_adaptive
    {P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    {g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : AdaptiveEmulatesWithin .adaptive P Q g ε) :
    AdaptiveEmulatesWithin .static P Q g (fun pA pZ => ε pA (pZ + 1)) := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hpS, hadv⟩ := h AdvQ AdvR A.clampStatic pA hA.clampStatic
  refine ⟨S.clampStatic, pS, hS.clampStatic, hpS, fun Z pZ hZ κ z =>
    static_advantage_le_of_adaptive_clampStatic P Q A S (hadv · (pZ + 1) ·) Z hZ κ z⟩

/-- Asymptotic adaptive emulation implies asymptotic static emulation (sanity bridge, not a theorem
of `[Canetti2020]`). -/
theorem AdaptiveEmulates.static_of_adaptive
    {P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    (h : AdaptiveEmulates .adaptive P Q) : AdaptiveEmulates .static P Q := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hper_Z⟩ := h AdvQ AdvR A.clampStatic pA hA.clampStatic
  refine ⟨S.clampStatic, pS, hS.clampStatic, fun pZ => ?_⟩
  obtain ⟨ν, hν, hadv⟩ := hper_Z (pZ + 1)
  exact ⟨ν, hν, fun Z hZ κ z =>
    static_advantage_le_of_adaptive_clampStatic P Q A S hadv Z hZ κ z⟩

end AdaptiveToStatic

end Cslib.Crypto.Protocols.UC
