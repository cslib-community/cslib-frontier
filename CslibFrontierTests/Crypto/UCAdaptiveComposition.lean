/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Protocols.UC.AdaptiveComposition

/-!
# Checked tests for adaptive single-session UC composition

Tests for `CslibFrontier.Crypto.Protocols.UC.AdaptiveComposition` covering:
1. A stateful 2-party hybrid (`tagHybrid`) over a stateful subroutine (`subStore`) in both
   `.erasing` and `.nonErasing` memory modes, exercising mid-execution `.corrupt 0`, snapshot
   preservation vs. erasure, `.status` reporting, honest party isolation, and `.static` rejection.
2. Call-budget preservation (`PolyBounded`), `ViewStableOnCorrupt`, `adaptiveExec_compose_dummy`,
   and `eval_adaptiveExec_compose_sim` under `CorruptSync`.
3. Non-vacuity and separation via `relay1` + `bitConst b` (`not_adaptiveEmulatesDummyWithin`),
   an explicit `badInitAdv` (`initial ≠ C₀`) caught by `.status`, and instantiations of
   `AdaptiveEmulatesDummyWithin.compose`, `AdaptiveEmulatesWithin.compose`, and
   `AdaptiveEmulates.compose`.
-/

namespace CslibTests.Crypto.UCAdaptiveComposition

open Cslib
open Cslib.Crypto
open Cslib.Crypto.Protocols.UC
open scoped NNReal

/-! ### Stateful 2-party hybrid and subroutine with snapshots and mid-run corruption -/

/-- Two-party mutable bit-slot subroutine. Party `(i, some b)` writes `some b` at slot `i` and
returns `some b`; `(i, none)` reads `s i`. Corrupting party `i` clears `i`'s live slot to `none`
while leaving party `j ≠ i` untouched (and preserving pre-corruption snapshots when
`.nonErasing`). -/
@[expose] public def subStore (mem : PartyMemory) :
    AdaptiveProtocol 2 (Option Bool) (Option Bool) Unit Unit (Option Bool) where
  machine _ := {
    State := Fin 2 → Option Bool
    init := pure (fun _ => none)
    handle
      | .inl (i, some b) => fun s =>
          pure (some b, fun j => if j = i then some b else s j)
      | .inl (i, none) => fun s => pure (s i, s)
      | .inr () => fun s => pure ((), s) }
  view _ i s := s i
  onCorrupt _ i s :=
    if mem = .erasing then (fun j => if j = i then none else s j) else s
  memory := mem

/-- Outer 2-party hybrid protocol calling `subStore` via `partySpec` and mirroring party inputs
into its own per-party slot. Corrupting party `i` clears `i`'s outer live slot to `none` in
`.erasing` mode (while leaving `j ≠ i` untouched), and leaves snapshots/views intact in
`.nonErasing` mode. -/
@[expose] public def tagHybrid (mem : PartyMemory) :
    AdaptiveHybridProtocol 2 (Option Bool) (Option Bool) Unit Unit
      (Option Bool) (Option Bool) (Option Bool) where
  machine _ := {
    State := Fin 2 → Option Bool
    init := pure (fun _ => none)
    handle
      | .inl (i, some b) => fun s => do
          let subOut ← ProbOracleComp.query (spec := partySpec 2 (Option Bool) (Option Bool))
            (i, some b)
          pure (subOut.join, fun j => if j = i then some b else s j)
      | .inl (i, none) => fun s => do
          let subOut ← ProbOracleComp.query (spec := partySpec 2 (Option Bool) (Option Bool))
            (i, none)
          pure (subOut.join, s)
      | .inr () => fun s => pure ((), s) }
  view _ i s := s i
  onCorrupt _ i s :=
    if mem = .erasing then (fun j => if j = i then none else s j) else s
  memory := mem

public theorem subStore_viewStable (mem : PartyMemory) : (subStore mem).ViewStableOnCorrupt := by
  intro hmem κ j i s
  have hm : mem = .nonErasing := hmem
  subst hm
  rfl

public theorem tagHybrid_viewStable (mem : PartyMemory) : (tagHybrid mem).ViewStableOnCorrupt := by
  intro hmem κ j i s
  have hm : mem = .nonErasing := hmem
  subst hm
  rfl

public theorem subStore_polyBounded (mem : PartyMemory) : (subStore mem).PolyBounded 1 := by
  intro κ
  dsimp only [subStore, StateT.run]
  simp only [Polynomial.eval_one]
  refine ⟨(OracleComp.IsCostBounded.pure _ 0).mono (by simp), fun q s => ?_⟩
  rcases q with ⟨i, (_ | b)⟩ | ⟨⟩ <;>
    exact (OracleComp.IsCostBounded.pure _ 0).mono (by simp)

public theorem tagHybrid_polyBounded (mem : PartyMemory) : (tagHybrid mem).PolyBounded 1 := by
  intro κ
  simp only [Polynomial.eval_one]
  refine ⟨?_, fun q s => ?_⟩
  · change (((tagHybrid mem).machine κ).init).IsQueryBounded 1
    exact (OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  · change (((tagHybrid mem).machine κ).handle q |>.run s).IsQueryBounded 1
    rcases q with ⟨i, (_ | b)⟩ | ⟨⟩
    · exact (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (by omega)
    · exact (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (by omega)
    · exact (OracleComp.IsCostBounded.pure _ 0).mono (by omega)

public theorem compose_tagHybrid_subStore_polyBounded (mem : PartyMemory) :
    (composeAdaptive (tagHybrid mem) (subStore mem)).PolyBounded ((1 + 1) * (1 + 1) + 1) :=
  composeAdaptive_polyBounded (tagHybrid_polyBounded mem) (subStore_polyBounded mem)

public abbrev SubStoreExecSpec :=
  adaptiveExecSpec 2 (Option Bool) (Option Bool)
    (AdaptiveNetQ 2 (Option Bool) (Unit ⊕ RoutedNetQ 2 (Option Bool) Unit))
    (AdaptiveNetR (Option Bool) (Unit ⊕ RoutedNetR (Option Bool) Unit)
      (AdaptiveHybridView (Option Bool) (Option Bool)))

/-- Environment exercising honest party `0` (`some true`), honest party `1` (`some false`),
mid-execution dynamic corruption `.corrupt 0`, `.status`, honest party `1` read (confirming
party `1` is unaffected and uncorrupted), and post-corruption activation of party `0` (returning
`none`). Checks that both `.outer` and `.sub` reports have `current = some true, history = some
[none, some true, some true]` when `expectHistory = true` (`.nonErasing`) and `current = none,
history = none` when `false` (`.erasing`). -/
@[expose] public def dynCorruptEnv (expectHistory : Bool) :
    AdaptiveEnvironment 2 (Option Bool) (Option Bool)
      (AdaptiveNetQ 2 (Option Bool) (Unit ⊕ RoutedNetQ 2 (Option Bool) Unit))
      (AdaptiveNetR (Option Bool) (Unit ⊕ RoutedNetR (Option Bool) Unit)
        (AdaptiveHybridView (Option Bool) (Option Bool))) :=
  fun _ _ => do
    let out0 : Option (Option Bool) ←
      ProbOracleComp.query (spec := SubStoreExecSpec) (.inl (.party 0 (some true)))
    let out1Pre : Option (Option Bool) ←
      ProbOracleComp.query (spec := SubStoreExecSpec) (.inl (.party 1 (some false)))
    let rep0 : AdaptiveNetR (Option Bool) (Unit ⊕ RoutedNetR (Option Bool) Unit)
        (AdaptiveHybridView (Option Bool) (Option Bool)) ←
      ProbOracleComp.query (spec := SubStoreExecSpec) (.inr (.corrupt 0))
    let st : Finset (Fin 2) ←
      ProbOracleComp.query (spec := SubStoreExecSpec) (.inl .status)
    let out1Post : Option (Option Bool) ←
      ProbOracleComp.query (spec := SubStoreExecSpec) (.inl (.party 1 none))
    let out0Post : Option (Option Bool) ←
      ProbOracleComp.query (spec := SubStoreExecSpec) (.inl (.party 0 (some false)))
    let expectedCur : Option Bool := if expectHistory then some true else none
    let expectedHist : Option (List (Option Bool)) :=
      if expectHistory then some [none, some true, some true] else none
    let expectedRep : AdaptiveHybridView (Option Bool) (Option Bool) :=
      { outer := { current := expectedCur, history := expectedHist }
        sub := { current := expectedCur, history := expectedHist } }
    pure
      (out0 == some (some true) &&
       out1Pre == some (some false) &&
       rep0 == .corrupt (some { current := expectedRep, history := none }) &&
       st == ({0} : Finset (Fin 2)) &&
       out1Post == some (some false) &&
       out0Post == none)

/-- Environment testing `.static` rejection: with `C₀ = ∅`, querying `.corrupt 0` mid-run
returns `.corrupt none`, `.status` remains `∅`, and party `0` remains honest. -/
@[expose] public def staticRejectEnv :
    AdaptiveEnvironment 2 (Option Bool) (Option Bool)
      (AdaptiveNetQ 2 (Option Bool) (Unit ⊕ RoutedNetQ 2 (Option Bool) Unit))
      (AdaptiveNetR (Option Bool) (Unit ⊕ RoutedNetR (Option Bool) Unit)
        (AdaptiveHybridView (Option Bool) (Option Bool))) :=
  fun _ _ => do
    let out0 : Option (Option Bool) ←
      ProbOracleComp.query (spec := SubStoreExecSpec) (.inl (.party 0 (some true)))
    let rep0 : AdaptiveNetR (Option Bool) (Unit ⊕ RoutedNetR (Option Bool) Unit)
        (AdaptiveHybridView (Option Bool) (Option Bool)) ←
      ProbOracleComp.query (spec := SubStoreExecSpec) (.inr (.corrupt 0))
    let st : Finset (Fin 2) ←
      ProbOracleComp.query (spec := SubStoreExecSpec) (.inl .status)
    let out0Post : Option (Option Bool) ←
      ProbOracleComp.query (spec := SubStoreExecSpec) (.inl (.party 0 none))
    pure
      (out0 == some (some true) &&
       rep0 == .corrupt none &&
       st == (∅ : Finset (Fin 2)) &&
       out0Post == some (some true))

private theorem eval_dynCorruptEnv_aux (mem : PartyMemory) (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive
      (composeAdaptive (tagHybrid mem) (subStore mem))
      (adaptiveDummyAdversary (fun _ => ∅) _ _)
      (dynCorruptEnv (decide (mem = .nonErasing))) κ z).eval = PMF.pure true := by
  rw [adaptiveExec_dummyAdversary, Machine.run, Machine.link]
  let P := composeAdaptive (tagHybrid mem) (subStore mem)
  let M := adaptiveRouter .adaptive P κ ∅
  let s0_comp : AdaptiveComposeState (Fin 2 → Option Bool) (Option Bool)
      (Fin 2 → Option Bool) (Option Bool) 2 :=
    { outer := { inner := fun _ => none, corrupted := ∅, trace := fun _ => [none] }
      sub := { inner := fun _ => none, corrupted := ∅, trace := fun _ => [none] } }
  have hfold : ∀ acc : AdaptiveComposeState (Fin 2 → Option Bool) (Option Bool)
        (Fin 2 → Option Bool) (Option Bool) 2,
      List.foldl (fun a (_ : Fin 2) => a) acc (List.finRange 2) = acc := fun _ => rfl
  have hPinit : (P.machine κ).init = pure s0_comp := by
    dsimp only [P, composeAdaptive, tagHybrid, subStore]
    simp only [pure_bind]
    rfl
  have hApp : P.applyInitialCorruptions κ ∅ s0_comp = s0_comp := by
    dsimp only [AdaptiveProtocol.applyInitialCorruptions]
    simp only [Finset.notMem_empty, ↓reduceIte]
    rfl
  have hMinit : M.init = pure
      { inner := s0_comp, corrupted := ∅, trace := fun i => [P.view κ i s0_comp] } := by
    dsimp only [M, adaptiveRouter]
    erw [hPinit, pure_bind, hApp]
  change Machine.closeEval (ProbOracleComp.sample M.init >>= fun s =>
    Prod.fst <$> M.runFrom (dynCorruptEnv (decide (mem = .nonErasing)) κ z) s) = PMF.pure true
  erw [hMinit, Machine.closeEval_bind, Machine.closeEval_sample, ProbComp.eval_pure, PMF.pure_bind]
  dsimp only [dynCorruptEnv]
  erw [Machine.runFrom_bind, Machine.runFrom_query]
  simp only [M, P, adaptiveRouter, composeAdaptive, tagHybrid, subStore, subPartyMachine,
    StateT.run, Finset.notMem_empty, ↓reduceIte, pure_bind, Machine.runFrom_bind,
    Machine.runFrom_query, Machine.runFrom_pure, Option.join_some, s0_comp,
    AdaptiveHybridProtocol.recordSnapshot, AdaptiveProtocol.recordSnapshot]
  erw [pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
  simp only [StateT.run, Finset.notMem_empty, ↓reduceIte, pure_bind,
    Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure, Option.join_some]
  erw [pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
  simp only [StateT.run, Finset.notMem_empty, ↓reduceIte,
    AdaptiveHybridProtocol.corruptionReport, AdaptiveProtocol.corruptionReport]
  erw [pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
  erw [pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
  simp only [StateT.run, Finset.mem_insert, Fin.isValue, Finset.notMem_empty,
    Machine.runFrom_pure, true_or, ↓reduceIte]
  erw [pure_bind, map_pure, Machine.closeEval_pure]
  congr 1
  cases mem <;> (
    simp only [↓reduceIte, reduceCtorEq, Fin.reduceEq, Fin.isValue, Finset.insert_empty,
      decide_true, List.cons_append, List.nil_append, beq_self_eq_true]
    dsimp only [Bind.bind, Option.bind, Pure.pure, Option.join, id]
    simp only [beq_self_eq_true, Bool.and_true])

public theorem eval_dynCorruptEnv_adaptive_nonErasing (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive
      (composeAdaptive (tagHybrid .nonErasing) (subStore .nonErasing))
      (adaptiveDummyAdversary (fun _ => ∅) _ _) (dynCorruptEnv true) κ z).eval =
      PMF.pure true := by
  simpa using eval_dynCorruptEnv_aux .nonErasing κ z

public theorem eval_dynCorruptEnv_adaptive_erasing (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive
      (composeAdaptive (tagHybrid .erasing) (subStore .erasing))
      (adaptiveDummyAdversary (fun _ => ∅) _ _) (dynCorruptEnv false) κ z).eval =
      PMF.pure true := by
  simpa using eval_dynCorruptEnv_aux .erasing κ z

public theorem eval_staticRejectEnv_static_nonErasing (κ : ℕ) (z : List Bool) :
    (adaptiveExec .static
      (composeAdaptive (tagHybrid .nonErasing) (subStore .nonErasing))
      (adaptiveDummyAdversary (fun _ => ∅) _ _) staticRejectEnv κ z).eval =
      PMF.pure true := by
  rw [adaptiveExec_dummyAdversary, Machine.run, Machine.link]
  let P := composeAdaptive (tagHybrid .nonErasing) (subStore .nonErasing)
  let M := adaptiveRouter .static P κ ∅
  let s0_comp : AdaptiveComposeState (Fin 2 → Option Bool) (Option Bool)
      (Fin 2 → Option Bool) (Option Bool) 2 :=
    { outer := { inner := fun _ => none, corrupted := ∅, trace := fun _ => [none] }
      sub := { inner := fun _ => none, corrupted := ∅, trace := fun _ => [none] } }
  have hfold : ∀ acc : AdaptiveComposeState (Fin 2 → Option Bool) (Option Bool)
        (Fin 2 → Option Bool) (Option Bool) 2,
      List.foldl (fun a (_ : Fin 2) => a) acc (List.finRange 2) = acc := fun _ => rfl
  have hPinit : (P.machine κ).init = pure s0_comp := by
    dsimp only [P, composeAdaptive, tagHybrid, subStore]
    simp only [pure_bind]
    rfl
  have hApp : P.applyInitialCorruptions κ ∅ s0_comp = s0_comp := by
    dsimp only [AdaptiveProtocol.applyInitialCorruptions]
    simp only [Finset.notMem_empty, ↓reduceIte]
    rfl
  have hMinit : M.init = pure
      { inner := s0_comp, corrupted := ∅, trace := fun i => [P.view κ i s0_comp] } := by
    dsimp only [M, adaptiveRouter]
    erw [hPinit, pure_bind, hApp]
  change Machine.closeEval (ProbOracleComp.sample M.init >>= fun s =>
    Prod.fst <$> M.runFrom (staticRejectEnv κ z) s) = PMF.pure true
  erw [hMinit, Machine.closeEval_bind, Machine.closeEval_sample, ProbComp.eval_pure, PMF.pure_bind]
  dsimp only [staticRejectEnv]
  erw [Machine.runFrom_bind, Machine.runFrom_query]
  simp only [M, P, adaptiveRouter, composeAdaptive, tagHybrid, subStore, subPartyMachine,
    StateT.run, Finset.notMem_empty, ↓reduceIte, pure_bind, Machine.runFrom_bind,
    Machine.runFrom_query, Machine.runFrom_pure, Option.join_some, s0_comp,
    AdaptiveHybridProtocol.recordSnapshot, AdaptiveProtocol.recordSnapshot]
  erw [pure_bind]
  dsimp only
  simp only [Finset.notMem_empty, ↓reduceIte]
  erw [pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
  simp only [StateT.run]
  erw [pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
  simp only [StateT.run, Finset.notMem_empty, ↓reduceIte, pure_bind,
    Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure]
  erw [pure_bind, map_pure, Machine.closeEval_pure]
  dsimp only [Bind.bind, Option.bind, Pure.pure, Option.join, id]
  simp only [beq_self_eq_true, Bool.true_and]

/-- Concrete execution regrouping check for `tagHybrid` + `subStore` in both `.erasing` and
`.nonErasing` modes (`adaptiveExec_compose_dummy`). -/
public theorem exec_compose_dummy_subStore (mode : CorruptionMode) (mem : PartyMemory)
    (C₀ : ℕ → Finset (Fin 2))
    (Z : AdaptiveEnvironment 2 (Option Bool) (Option Bool)
      (AdaptiveNetQ 2 (Option Bool) (Unit ⊕ RoutedNetQ 2 (Option Bool) Unit))
      (AdaptiveNetR (Option Bool) (Unit ⊕ RoutedNetR (Option Bool) Unit)
        (AdaptiveHybridView (Option Bool) (Option Bool))))
    (κ : ℕ) (z : List Bool) :
    adaptiveExec mode (composeAdaptive (tagHybrid mem) (subStore mem))
      (adaptiveDummyAdversary C₀ _ _) Z κ z =
      adaptiveExec mode (subStore mem) (adaptiveDummyAdversary C₀ _ _)
        (absorbAdaptiveHybrid mode C₀ (tagHybrid mem) Z) κ z :=
  adaptiveExec_compose_dummy mode C₀ (tagHybrid mem) (subStore mem)
    (tagHybrid_viewStable mem) (subStore_viewStable mem) Z κ z

/-- The adaptive dummy adversary is trivially `CorruptSync` with any protocol. -/
public theorem adaptiveDummyAdversary_corruptSync {n : ℕ} {In Out NQ NR View : Type}
    (mode : CorruptionMode) (C₀ : ℕ → Finset (Fin n))
    (φ : AdaptiveProtocol n In Out NQ NR View) :
    (adaptiveDummyAdversary C₀ NQ NR :
      AdaptiveAdversary n In Out NQ NR View
        (AdaptiveNetQ n In NQ) (AdaptiveNetR Out NR View)).CorruptSync mode C₀ φ := by
  refine ⟨rfl, fun κ q sS rφ _ x hx => ?_⟩
  dsimp only [adaptiveDummyAdversary, Machine.id, liftAdaptiveNet, Machine.liftRightProgram,
    StateT.run] at hx
  erw [OracleComp.interpret_bind, OracleComp.interpret_query, Machine.runFrom_bind,
    Machine.runFrom_query] at hx
  rcases Machine.mem_support_closeEval_bind.mp hx with ⟨⟨_, r1⟩, hr1, hx'⟩
  erw [OracleComp.interpret_pure, Machine.runFrom_pure] at hx'
  have h2 : x.2 = r1 := (Prod.mk.inj (Machine.mem_support_closeEval_pure.mp hx')).2
  rw [h2]
  clear hx hx' h2
  rcases q with ⟨i, y⟩ | i | nq
  · dsimp only [adaptiveRouter, StateT.run] at hr1
    split_ifs at hr1
    · rcases Machine.mem_support_closeEval_bind.mp hr1 with ⟨_, _, hr1'⟩
      rw [(Prod.mk.inj (Machine.mem_support_closeEval_pure.mp hr1')).2]; rfl
    · rw [(Prod.mk.inj (Machine.mem_support_closeEval_pure.mp hr1)).2]
  · cases mode
    · dsimp only [adaptiveRouter, StateT.run] at hr1
      split_ifs at hr1 <;>
        rw [(Prod.mk.inj (Machine.mem_support_closeEval_pure.mp hr1)).2] <;> rfl
    · dsimp only [adaptiveRouter, StateT.run] at hr1
      split_ifs at hr1 with hi <;>
        rw [(Prod.mk.inj (Machine.mem_support_closeEval_pure.mp hr1)).2] <;>
        simp [hi, Finset.insert_eq_of_mem]
  · dsimp only [adaptiveRouter, StateT.run] at hr1
    rcases Machine.mem_support_closeEval_bind.mp hr1 with ⟨_, _, hr1'⟩
    rw [(Prod.mk.inj (Machine.mem_support_closeEval_pure.mp hr1')).2]; rfl

/-- Concrete simulator regrouping check (`eval_adaptiveExec_compose_sim`) on `tagHybrid` +
`subStore` with `adaptiveDummyAdversary` as `CorruptSync` simulator. -/
public theorem eval_compose_sim_subStore (mode : CorruptionMode) (mem : PartyMemory)
    (C₀ : ℕ → Finset (Fin 2))
    (Z : AdaptiveEnvironment 2 (Option Bool) (Option Bool)
      (AdaptiveNetQ 2 (Option Bool) (Unit ⊕ RoutedNetQ 2 (Option Bool) Unit))
      (AdaptiveNetR (Option Bool) (Unit ⊕ RoutedNetR (Option Bool) Unit)
        (AdaptiveHybridView (Option Bool) (Option Bool))))
    (κ : ℕ) (z : List Bool) :
    (adaptiveExec mode (composeAdaptive (tagHybrid mem) (subStore mem))
      (adaptiveHybridSim mode C₀ (adaptiveDummyAdversary C₀ Unit Unit)) Z κ z).eval =
      (adaptiveExec mode (subStore mem) (adaptiveDummyAdversary C₀ Unit Unit)
        (absorbAdaptiveHybrid mode C₀ (tagHybrid mem) Z) κ z).eval :=
  eval_adaptiveExec_compose_sim mode C₀ (tagHybrid mem) (subStore mem)
    (tagHybrid_viewStable mem) (subStore_viewStable mem)
    (adaptiveDummyAdversary C₀ Unit Unit)
    (adaptiveDummyAdversary_corruptSync mode C₀ (subStore mem)) Z κ z

/-! ### Non-vacuity, separation, initial-corruption mismatch witness, and headline compose -/

/-- One-party constant-bit adaptive protocol whose honest party output is `b : Bool`. -/
@[expose] public def bitConst (mem : PartyMemory) (b : Bool) :
    AdaptiveProtocol 1 Unit Bool Unit Unit Bool where
  machine _ := {
    State := Unit
    init := pure ()
    handle
      | .inl _ => fun s => pure (b, s)
      | .inr () => fun s => pure ((), s) }
  view _ _ _ := b
  onCorrupt _ _ s := s
  memory := mem

/-- One-party identity hybrid protocol forwarding party `0` to the subroutine (`bitConst`). -/
@[expose] public def relay1 (mem : PartyMemory) :
    AdaptiveHybridProtocol 1 Unit Bool Unit Unit Unit Bool Unit where
  machine _ := {
    State := Unit
    init := pure ()
    handle
      | .inl (i, x) => fun s => do
          let r ← ProbOracleComp.query (spec := partySpec 1 Unit Bool) (i, x)
          pure (r.getD false, s)
      | .inr () => fun s => pure ((), s) }
  view _ _ _ := ()
  onCorrupt _ _ s := s
  memory := mem

public theorem bitConst_viewStable (mem : PartyMemory) (b : Bool) :
    (bitConst mem b).ViewStableOnCorrupt := by
  intro hmem _ _ _ _
  have hm : mem = .nonErasing := hmem
  subst hm
  rfl

public theorem relay1_viewStable (mem : PartyMemory) : (relay1 mem).ViewStableOnCorrupt := by
  intro hmem _ _ _ _
  have hm : mem = .nonErasing := hmem
  subst hm
  rfl

public theorem relay1_polyBounded (mem : PartyMemory) : (relay1 mem).PolyBounded 1 := by
  intro κ
  simp only [Polynomial.eval_one]
  refine ⟨?_, fun q s => ?_⟩
  · change (((relay1 mem).machine κ).init).IsQueryBounded 1
    exact (OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  · change (((relay1 mem).machine κ).handle q |>.run s).IsQueryBounded 1
    rcases q with ⟨i, x⟩ | ⟨⟩
    · exact (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (by omega)
    · exact (OracleComp.IsCostBounded.pure _ 0).mono (by omega)

public abbrev RelayExecSpec :=
  adaptiveExecSpec 1 Unit Bool
    (AdaptiveNetQ 1 Unit (Unit ⊕ RoutedNetQ 1 Unit Unit))
    (AdaptiveNetR Bool (Unit ⊕ RoutedNetR Bool Unit) (AdaptiveHybridView Unit Bool))

/-- Two-query environment checking `.status == ∅` and activating honest party `0`, returning
`true` iff `.status = ∅` and party `0` outputs `some true`. -/
@[expose] public def askParty0Env :
    AdaptiveEnvironment 1 Unit Bool
      (AdaptiveNetQ 1 Unit (Unit ⊕ RoutedNetQ 1 Unit Unit))
      (AdaptiveNetR Bool (Unit ⊕ RoutedNetR Bool Unit) (AdaptiveHybridView Unit Bool)) :=
  fun _ _ => do
    let st : Finset (Fin 1) ← ProbOracleComp.query (spec := RelayExecSpec) (.inl .status)
    let r : Option Bool ← ProbOracleComp.query (spec := RelayExecSpec) (.inl (.party 0 ()))
    pure (decide (st = ∅) && (r == some true))

public theorem eval_adaptiveExec_compose_relay1 (mode : CorruptionMode) (mem : PartyMemory)
    (b : Bool) (A : AdaptiveAdversary 1 Unit Bool
      (Unit ⊕ RoutedNetQ 1 Unit Unit) (Unit ⊕ RoutedNetR Bool Unit)
      (AdaptiveHybridView Unit Bool)
      (AdaptiveNetQ 1 Unit (Unit ⊕ RoutedNetQ 1 Unit Unit))
      (AdaptiveNetR Bool (Unit ⊕ RoutedNetR Bool Unit) (AdaptiveHybridView Unit Bool)))
    (z : List Bool) :
    (adaptiveExec mode (composeAdaptive (relay1 mem) (bitConst mem b)) A askParty0Env 0 z).eval =
      PMF.pure (decide (A.initial 0 = ∅) && b) := by
  let P := composeAdaptive (relay1 mem) (bitConst mem b)
  let M := adaptiveExecMachine mode P A 0
  let sComp0 : AdaptiveComposeState Unit Unit Unit Bool 1 :=
    { outer := { inner := (), corrupted := ∅, trace := fun _ => [()] }
      sub := { inner := (), corrupted := ∅, trace := fun _ => [b] } }
  let s0 : AdaptiveRouterState (AdaptiveComposeState Unit Unit Unit Bool 1)
      (AdaptiveHybridView Unit Bool) 1 :=
    let s1 := P.applyInitialCorruptions 0 (A.initial 0) sComp0
    { inner := s1, corrupted := A.initial 0, trace := fun i => [P.view 0 i s1] }
  have hPinit : (P.machine 0).init = pure sComp0 := by
    dsimp only [P, composeAdaptive, relay1, bitConst]
    simp only [pure_bind]
    rfl
  rw [adaptiveExec, Machine.run, Machine.link]
  erw [sample_adaptiveExecMachine_init mode P A 0, hPinit, ProbOracleComp.sample_pure, pure_bind]
  change Machine.closeEval
    (ProbOracleComp.sample (A.machine 0).init >>= fun sA =>
      Prod.fst <$> M.runFrom (askParty0Env 0 z) (sA, s0)) = PMF.pure (decide (A.initial 0 = ∅) && b)
  have hinner : ∀ sA₀ : (A.machine 0).State,
      Machine.closeEval (Prod.fst <$> M.runFrom (askParty0Env 0 z) (sA₀, s0)) =
        PMF.pure (decide (A.initial 0 = ∅) && b) := by
    intro sA₀
    have hst : (M.handle (.inl .status)).run (sA₀, s0) = pure (s0.corrupted, (sA₀, s0)) := rfl
    have hcor_eq : s0.corrupted = A.initial 0 := rfl
    dsimp only [askParty0Env]
    erw [Machine.runFrom_bind, Machine.runFrom_query, hst, pure_bind,
      Machine.runFrom_bind, Machine.runFrom_query]
    have hA_inl : StateT.lift (σ := (A.machine 0).State)
        (ProbOracleComp.query (spec := adaptivePartySpec 1 Unit Bool ⊕ₒ netSpec
          (AdaptiveNetQ 1 Unit (Unit ⊕ RoutedNetQ 1 Unit Unit))
          (AdaptiveNetR Bool (Unit ⊕ RoutedNetR Bool Unit) (AdaptiveHybridView Unit Bool)))
          (.inl (.party 0 ()))) sA₀ =
        (fun a => (a, sA₀)) <$> ProbOracleComp.query (Sum.inl (AdaptivePartyQ.party 0 ())) := by
      change (StateT.lift _).run sA₀ = _
      rw [StateT.run_lift, bind_pure_comp]
    by_cases h0 : (0 : Fin 1) ∈ A.initial 0
    · have hne : A.initial 0 ≠ ∅ := Finset.ne_empty_of_mem h0
      have hp0 : (M.handle (.inl (.party 0 ()))).run (sA₀, s0) = pure (none, (sA₀, s0)) := by
        dsimp only [M, adaptiveExecMachine, Machine.comp, liftAdaptiveAdversary, Machine.liftRight,
          StateT.run]
        erw [hA_inl, Machine.runFrom_map, Machine.runFrom_query]
        simp only [adaptiveRouter, StateT.run, hcor_eq, h0, ↓reduceIte, map_pure]
        rfl
      erw [hp0, pure_bind, Machine.runFrom_pure, map_pure, Machine.closeEval_pure]
      simp [hcor_eq, hne]
    · have hempty : A.initial 0 = ∅ := by
        ext x; cases Fin.eq_zero x; simp [h0]
      have hsub_not : (0 : Fin 1) ∉ s0.inner.sub.corrupted := by
        dsimp only [s0, P, AdaptiveProtocol.applyInitialCorruptions, composeAdaptive, sComp0]
        simp only [hempty, Finset.notMem_empty, ↓reduceIte]
        exact Finset.notMem_empty 0
      have hp0 : ∃ sNext, (M.handle (.inl (.party 0 ()))).run (sA₀, s0) =
          pure (some b, (sA₀, sNext)) := by
        refine ⟨?sNext, ?hp⟩
        case hp =>
          dsimp only [M, adaptiveExecMachine, Machine.comp, liftAdaptiveAdversary,
            Machine.liftRight, StateT.run]
          erw [hA_inl, Machine.runFrom_map, Machine.runFrom_query]
          simp only [adaptiveRouter, P, composeAdaptive, relay1, bitConst, subPartyMachine,
            StateT.run, hcor_eq, h0, ↓reduceIte, pure_bind, Machine.runFrom_bind,
            Machine.runFrom_query, hsub_not, Machine.runFrom_pure, Option.getD_some, map_pure]
          rfl
      obtain ⟨sNext, hp0⟩ := hp0
      erw [hp0, pure_bind, Machine.runFrom_pure, map_pure, Machine.closeEval_pure]
      simp [hcor_eq, hempty]
  change Machine.closeEval
    (ProbOracleComp.sample (A.machine 0).init >>= fun sA =>
      Prod.fst <$> M.runFrom (askParty0Env 0 z) (sA, s0)) = PMF.pure (decide (A.initial 0 = ∅) && b)
  erw [Machine.closeEval_bind, Machine.closeEval_sample]
  calc
    (ProbComp.eval (A.machine 0).init).bind
        (fun sA₀ => Machine.closeEval (Prod.fst <$> M.runFrom (askParty0Env 0 z) (sA₀, s0))) =
      (ProbComp.eval (A.machine 0).init).bind
        (fun _ => PMF.pure (decide (A.initial 0 = ∅) && b)) := by
        congr 1; funext sA₀; exact hinner sA₀
    _ = PMF.pure (decide (A.initial 0 = ∅) && b) := PMF.bind_const _ _

/-- Non-vacuity / separation witness: `composeAdaptive (relay1 mem) (bitConst mem true)` cannot
adaptively dummy-emulate `composeAdaptive (relay1 mem) (bitConst mem false)` within any bound `< 1`
(across all `CorruptionMode` and `PartyMemory` combinations). -/
public theorem not_adaptiveEmulatesDummyWithin_compose_bitConst (mode : CorruptionMode)
    (mem : PartyMemory) (pD : Polynomial ℕ) (ε : Polynomial ℕ → ℕ → ℝ≥0)
    (hε : ε 2 0 < 1) :
    ¬ AdaptiveEmulatesDummyWithin mode
      (composeAdaptive (relay1 mem) (bitConst mem true))
      (composeAdaptive (relay1 mem) (bitConst mem false)) pD ε := by
  intro h
  obtain ⟨S_D, _, hadv⟩ := h (fun _ => ∅)
  have hZ : AdaptiveEnvironment.PolyBounded askParty0Env 2 := by
    intro κ z
    simp only [Polynomial.eval_ofNat]
    change (askParty0Env κ z).IsQueryBounded 2
    exact (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
      OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  have hle := hadv askParty0Env 2 hZ 0 []
  have hreal : (adaptiveExec mode (composeAdaptive (relay1 mem) (bitConst mem true))
      (adaptiveDummyAdversary (fun _ => ∅) _ _) askParty0Env 0 []).eval = PMF.pure true := by
    simpa [adaptiveDummyAdversary] using eval_adaptiveExec_compose_relay1 mode mem true
      (adaptiveDummyAdversary (fun _ => ∅) _ _) []
  have hideal : (adaptiveExec mode (composeAdaptive (relay1 mem) (bitConst mem false))
      S_D askParty0Env 0 []).eval = PMF.pure false := by
    simpa using eval_adaptiveExec_compose_relay1 mode mem false S_D []
  have hadv1 : adaptiveAdvantage mode
      (composeAdaptive (relay1 mem) (bitConst mem true))
      (composeAdaptive (relay1 mem) (bitConst mem false))
      (adaptiveDummyAdversary (fun _ => ∅) _ _) S_D askParty0Env 0 [] = 1 := by
    rw [adaptiveAdvantage, hreal, hideal, Game.advantage_pure_true_left]
    simp [Game.failProbability]
  rw [hadv1] at hle
  exact not_lt_of_ge hle hε

/-- Explicit initial-corruption mismatch witness (`badInitAdv.initial ≠ C₀`) caught by `.status`,
explaining why `S_D.initial = C₀` is enforced in `CorruptSync` and `AdaptiveEmulatesDummyWithin`. -/
@[expose] public def badInitAdv :
    AdaptiveAdversary 1 Unit Bool (Unit ⊕ RoutedNetQ 1 Unit Unit) (Unit ⊕ RoutedNetR Bool Unit)
      (AdaptiveHybridView Unit Bool)
      (AdaptiveNetQ 1 Unit (Unit ⊕ RoutedNetQ 1 Unit Unit))
      (AdaptiveNetR Bool (Unit ⊕ RoutedNetR Bool Unit) (AdaptiveHybridView Unit Bool)) where
  initial _ := {0}
  machine _ := Machine.id _

public theorem badInitAdv_advantage_one (mode : CorruptionMode) (mem : PartyMemory)
    (z : List Bool) :
    adaptiveAdvantage mode
      (composeAdaptive (relay1 mem) (bitConst mem true))
      (composeAdaptive (relay1 mem) (bitConst mem true))
      (adaptiveDummyAdversary (fun _ => ∅) _ _) badInitAdv askParty0Env 0 z = 1 := by
  have hreal : (adaptiveExec mode (composeAdaptive (relay1 mem) (bitConst mem true))
      (adaptiveDummyAdversary (fun _ => ∅) _ _) askParty0Env 0 z).eval = PMF.pure true := by
    simpa [adaptiveDummyAdversary] using eval_adaptiveExec_compose_relay1 mode mem true
      (adaptiveDummyAdversary (fun _ => ∅) _ _) z
  have hbad : (adaptiveExec mode (composeAdaptive (relay1 mem) (bitConst mem true))
      badInitAdv askParty0Env 0 z).eval = PMF.pure false := by
    have h0 : badInitAdv.initial 0 ≠ ∅ := by simp [badInitAdv]
    simpa [h0] using eval_adaptiveExec_compose_relay1 mode mem true badInitAdv z
  rw [adaptiveAdvantage, hreal, hbad, Game.advantage_pure_true_left]
  simp [Game.failProbability]

/-! ### Headline composition theorem instantiations -/

public theorem absorb_askParty0Env_polyBounded (mode : CorruptionMode) (mem : PartyMemory)
    (C₀ : ℕ → Finset (Fin 1)) :
    AdaptiveEnvironment.PolyBounded (absorbAdaptiveHybrid mode C₀ (relay1 mem) askParty0Env)
      (absorbPoly 2 1) := by
  refine absorbAdaptiveHybrid_polyBounded mode C₀ (relay1_polyBounded mem) ?_
  intro κ z
  simp only [Polynomial.eval_ofNat]
  change (askParty0Env κ z).IsQueryBounded 2
  exact (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
    OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
      OracleComp.IsCostBounded.pure _ 0).mono (by omega)

public theorem hybridSim_dummy_polyBounded (mode : CorruptionMode)
    (C₀ : ℕ → Finset (Fin 2)) :
    (adaptiveHybridSim (In := Option Bool) (Out := Option Bool) (NetQ := Unit) (NetR := Unit)
      (Viewρ := Option Bool) mode C₀
      (adaptiveDummyAdversary C₀ Unit Unit :
        AdaptiveAdversary 2 (Option Bool) (Option Bool) Unit Unit (Option Bool)
          (AdaptiveNetQ 2 (Option Bool) Unit)
          (AdaptiveNetR (Option Bool) Unit (Option Bool)))).PolyBounded (1 + 1) := by
  refine adaptiveHybridSim_polyBounded mode C₀ ?_
  intro κ
  simp only [Polynomial.eval_one]
  refine ⟨?_, fun q s => ?_⟩
  · change (((adaptiveDummyAdversary C₀ Unit Unit).machine κ).init).IsQueryBounded 1
    exact (OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  · change (((adaptiveDummyAdversary C₀ Unit Unit).machine κ).handle q |>.run s).IsQueryBounded 1
    exact (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
      OracleComp.IsCostBounded.pure _ 0).mono (by omega)

public theorem advantage_compose_subStore_zero (mode : CorruptionMode) (mem : PartyMemory)
    (C₀ : ℕ → Finset (Fin 2))
    (Z : AdaptiveEnvironment 2 (Option Bool) (Option Bool)
      (AdaptiveNetQ 2 (Option Bool) (Unit ⊕ RoutedNetQ 2 (Option Bool) Unit))
      (AdaptiveNetR (Option Bool) (Unit ⊕ RoutedNetR (Option Bool) Unit)
        (AdaptiveHybridView (Option Bool) (Option Bool))))
    (κ : ℕ) (z : List Bool) :
    adaptiveAdvantage mode (composeAdaptive (tagHybrid mem) (subStore mem))
      (composeAdaptive (tagHybrid mem) (subStore mem))
      (adaptiveDummyAdversary C₀ _ _)
      (adaptiveHybridSim mode C₀ (adaptiveDummyAdversary C₀ Unit Unit)) Z κ z = 0 := by
  rw [adaptiveAdvantage_compose mode C₀ (tagHybrid mem) (subStore mem) (subStore mem)
    (tagHybrid_viewStable mem) (subStore_viewStable mem) (subStore_viewStable mem)
    (adaptiveDummyAdversary C₀ Unit Unit)
    (adaptiveDummyAdversary_corruptSync mode C₀ (subStore mem)) Z κ z,
    adaptiveAdvantage_self]

public theorem compose_dummy_within_bitConst (mode : CorruptionMode) (mem : PartyMemory) :
    ∃ (pD : Polynomial ℕ) (ε : Polynomial ℕ → ℕ → ℝ≥0), AdaptiveEmulatesDummyWithin mode
      (composeAdaptive (relay1 mem) (bitConst mem true))
      (composeAdaptive (relay1 mem) (bitConst mem true)) pD ε :=
  ⟨_, _, (AdaptiveEmulatesWithin.refl mode (bitConst mem true)).emulatesDummyWithin.compose
    (relay1_viewStable mem) (bitConst_viewStable mem true) (bitConst_viewStable mem true)
    (relay1_polyBounded mem)⟩

public theorem compose_within_bitConst (mode : CorruptionMode) (mem : PartyMemory) :
    ∃ g ε, AdaptiveEmulatesWithin mode
      (composeAdaptive (relay1 mem) (bitConst mem true))
      (composeAdaptive (relay1 mem) (bitConst mem true)) g ε :=
  ⟨_, _, (AdaptiveEmulatesWithin.refl mode (bitConst mem true)).compose
    (relay1_viewStable mem) (bitConst_viewStable mem true) (bitConst_viewStable mem true)
    (relay1_polyBounded mem)⟩

public theorem compose_asymptotic_bitConst (mode : CorruptionMode) (mem : PartyMemory) :
    AdaptiveEmulates mode
      (composeAdaptive (relay1 mem) (bitConst mem true))
      (composeAdaptive (relay1 mem) (bitConst mem true)) :=
  (AdaptiveEmulates.refl mode (bitConst mem true)).compose
    (relay1_viewStable mem) (bitConst_viewStable mem true) (bitConst_viewStable mem true)
    (relay1_polyBounded mem)

end CslibTests.Crypto.UCAdaptiveComposition
