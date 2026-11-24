/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

-- upstream: local-only (tests)

import CslibFrontier.Crypto.Protocols.UC.AdaptiveStorage
import CslibFrontier.Crypto.Protocols.UC.AdaptiveDummyAdversary
import CslibFrontier.Probability.PMF.Expect

/-!
# Checked tests for write-once non-erasing storage and coin exposure

Tests `CslibFrontier.Crypto.Protocols.UC.AdaptiveStorage`:
1. Prefix monotonicity (`WriteOnceState.TapePrefix`), per-party isolation, and erased-input
   preservation across `.party`, `.net`, and `onCorrupt` transitions in `eraseSecretProto`.
2. Concrete call-budget preservation (`PolyBounded.withWriteOnce`), honest-phase / uncorrupted
   execution equivalence (`runFrom_adaptiveRouter_withWriteOnce_noCorrupt`), projection equivalence
   (`adaptiveExec_withWriteOnce_project`), and `.nonErasing` → `.erasing` implications
   (`AdaptiveEmulates.of_writeOnce`, `AdaptiveEmulates.erasing_of_writeOnce`).
3. Concrete separation witness (`ephemeralCoin` vs `F_ephemeral`): `ephemeralCoin .erasing`
   equals `F_ephemeral.toAdaptive ephemeralReveal` in the snapshot model (zero distinguishing
   advantage), whereas wrapping `ephemeralCoin .erasing` with `withWriteOnce .nonErasing` exposes
   party `0`'s intra-activation discarded coin flip on `tapes 0`, yielding advantage `1 / 2` and
   refuting `AdaptiveEmulatesWithin` / `AdaptiveEmulates`.
-/

namespace CslibFrontierTests.Crypto.UCAdaptiveStorage

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open OracleComp (sumHandler)
open Machine (closeEval closeEval_pure closeEval_bind closeEval_map closeEval_sample
  mem_support_closeEval_pure)
open scoped ENNReal NNReal

/-! ### 1. Erased-input witness & prefix monotonicity -/

/-- Inputs for a two-party secret-erasing protocol: store a bit or erase local memory. -/
inductive SecretIn : Type
  | store (b : Bool)
  | erase
  deriving DecidableEq, Repr

/-- Two-party protocol where party `0` stores a bit in local state and clears it on `.erase` or
`onCorrupt` (so snapshot views report `none` after erasure). -/
def eraseSecretProto (mem : PartyMemory) :
    AdaptiveProtocol 2 SecretIn Bool Unit Unit (Option Bool) where
  machine _ := {
    State := Fin 2 → Option Bool
    init := pure fun _ => none
    handle
      | .inl (i, .store b) => fun s =>
          pure (some b, fun j => if j = i then some b else s j)
      | .inl (i, .erase) => fun s =>
          pure (none, fun j => if j = i then none else s j)
      | .inr () => fun s => pure ((), s) }
  view _ i s := s i
  onCorrupt _ i s := fun j => if j = i then none else s j
  memory := mem

private def eraseSecretInitRS (mem : PartyMemory) :
    AdaptiveRouterState (WriteOnceState (Fin 2 → Option Bool) SecretIn Bool (Option Bool) 2)
      (WriteOnceView SecretIn Bool (Option Bool)) 2 :=
  { inner := { inner := fun _ => none, initCoins := [], tapes := fun _ => [] }
    corrupted := ∅
    trace := fun _ => [{ current := none, tape := if mem = .nonErasing then some [] else none }] }

/-- After storing `true`, erasing party `0`'s state, sending a `.net` query, and corrupting `0`:
`withWriteOnce .nonErasing` keeps both activation records on `tapes 0`, leaves `tapes 1` empty,
and satisfies `TapePrefix` at every step, whereas `withWriteOnce .erasing` returns `tape := none`
and `history := none`. -/
theorem eraseSecret_writeOnce_nonErasing_vs_erasing :
    let Pwo := (eraseSecretProto .erasing).withWriteOnce .nonErasing
    let R := adaptiveRouter .adaptive Pwo 0 ∅
    let prog : ProbOracleComp
        (adaptiveProtocolSpec 2 SecretIn Bool Unit Unit (WriteOnceView SecretIn Bool (Option Bool)))
        (AdaptiveNetR Bool Unit (WriteOnceView SecretIn Bool (Option Bool))) := do
      let _ ← ProbOracleComp.query (.inl (.party 0 (.store true)))
      let _ ← ProbOracleComp.query (.inl (.party 0 .erase))
      let _ ← ProbOracleComp.query (.inr (.net ()))
      ProbOracleComp.query (Sum.inr (.corrupt 0))
    let expectedRecs : List (PartyActivationRecord SecretIn Bool (Option Bool)) :=
      [ { input := .store true, output := some true, coins := [], postView := some true },
        { input := .erase, output := none, coins := [], postView := none } ]
    (R.runFrom prog (eraseSecretInitRS .nonErasing)).map (fun x =>
        (x.1, x.2.inner.tapes 0, x.2.inner.tapes 1)) =
      pure (.corrupt (some {
        current := { current := none, tape := some expectedRecs }
        history := some
          [ { current := none, tape := some [] },
            { current := some true, tape := some [expectedRecs[0]] },
            { current := none, tape := some expectedRecs },
            { current := none, tape := some expectedRecs } ] }),
        expectedRecs, []) := by
  dsimp only
  simp only [eraseSecretProto, AdaptiveProtocol.withWriteOnce, AdaptiveProtocol.recordSnapshot,
    AdaptiveProtocol.corruptionReport, adaptiveRouter, eraseSecretInitRS, recordCoins,
    recordCoinsFrom, OracleComp.interpret_pure, Machine.runFrom_bind, Machine.runFrom_query,
    StateT.run, pure_bind]
  rfl

theorem eraseSecret_writeOnce_erasing_hides_tape :
    let Pwo := (eraseSecretProto .erasing).withWriteOnce .erasing
    let R := adaptiveRouter .adaptive Pwo 0 ∅
    let prog : ProbOracleComp
        (adaptiveProtocolSpec 2 SecretIn Bool Unit Unit (WriteOnceView SecretIn Bool (Option Bool)))
        (AdaptiveNetR Bool Unit (WriteOnceView SecretIn Bool (Option Bool))) := do
      let _ ← ProbOracleComp.query (.inl (.party 0 (.store true)))
      let _ ← ProbOracleComp.query (.inl (.party 0 .erase))
      ProbOracleComp.query (Sum.inr (.corrupt 0))
    Prod.fst <$> R.runFrom prog (eraseSecretInitRS .erasing) =
      pure (.corrupt (some { current := { current := none, tape := none }, history := none })) := by
  dsimp only
  simp only [eraseSecretProto, AdaptiveProtocol.withWriteOnce, AdaptiveProtocol.recordSnapshot,
    AdaptiveProtocol.corruptionReport, adaptiveRouter, eraseSecretInitRS, recordCoins,
    recordCoinsFrom, OracleComp.interpret_pure, Machine.runFrom_bind, Machine.runFrom_query,
    StateT.run]
  rfl

/-! ### 2. Ephemeral coin-flipping protocol and ideal functionality -/

/-- Inputs for `ephemeralCoin` and `F_ephemeral`. -/
inductive EphIn : Type
  | go
  | poll
  deriving DecidableEq, Repr

/-- Ideal functionality: party `0` samples a secret bit `b` on `.go` and delivers it only to
party `1` on `.poll`. -/
@[reducible] def F_ephemeral : IdealFunctionality 2 EphIn Bool Unit Unit where
  State := Option Bool
  init _ _ := pure none
  onInput
    | i, .go => fun s =>
        if i.val = 0 ∧ s.isNone then do
          let c ← ProbComp.unifFin 1
          pure (none, some (decide (c = 0)))
        else pure (none, s)
    | i, .poll => fun s => pure (if i.val = 1 then s else none, s)
  onBackdoor _ s := pure ((), s)

/-- Leakage view for `F_ephemeral`: party `0` leaks `none` (the coin is never kept in party `0`'s
state), while party `1` reveals its delivered output. -/
def ephemeralReveal (_ : ℕ) (s : Option Bool) (i : Fin 2) : Option Bool :=
  if i.val = 1 then s else none

/-- Concrete protocol with identical snapshot state/views to `F_ephemeral.toAdaptive
ephemeralReveal`: party `0` discards the coin `c` immediately after setting `delivered1`. -/
def ephemeralCoin (mem : PartyMemory) :
    AdaptiveProtocol 2 EphIn Bool Unit Unit (Option Bool) where
  machine κ := (F_ephemeral.toAdaptive ephemeralReveal).machine κ
  view κ i s := ephemeralReveal κ s i
  onCorrupt _ _ s := s
  memory := mem

theorem ephemeralCoin_erasing_eq_ideal :
    ephemeralCoin .erasing = F_ephemeral.toAdaptive ephemeralReveal := rfl

/-- In the snapshot `.erasing` model, `ephemeralCoin .erasing` trivially emulates `F_ephemeral`. -/
theorem ephemeralCoin_erasing_emulates :
    AdaptiveEmulates .adaptive (ephemeralCoin .erasing)
      (F_ephemeral.toAdaptive ephemeralReveal) := by
  rw [ephemeralCoin_erasing_eq_ideal]
  exact AdaptiveEmulates.refl .adaptive _

theorem ephemeralCoin_polyBounded (mem : PartyMemory) :
    (ephemeralCoin mem).PolyBounded 1 := fun _ => by
  refine ⟨(OracleComp.IsCostBounded.pure _ 0).mono (by simp), fun q s => ?_⟩
  rw [Polynomial.eval_one]
  rcases q with ⟨i, x⟩ | q
  · cases x
    · dsimp only [ephemeralCoin, IdealFunctionality.toAdaptive, F_ephemeral, StateT.run]
      split_ifs
      · rw [ProbComp.unifFin, ProbOracleComp.sample_bind]
        exact OracleComp.IsCostBounded.bind
          (by dsimp [ProbOracleComp.sample]; exact OracleComp.IsCostBounded.query (Sum.inl 1))
          (fun _ => OracleComp.IsCostBounded.pure _ 0)
      · exact (OracleComp.IsCostBounded.pure _ 0).mono (by simp)
    · dsimp only [ephemeralCoin, IdealFunctionality.toAdaptive, F_ephemeral, StateT.run]
      exact (OracleComp.IsCostBounded.pure _ 0).mono (by simp)
  · cases q
    exact (OracleComp.IsCostBounded.pure _ 0).mono (by simp)

theorem ephemeralCoin_writeOnce_polyBounded :
    ((ephemeralCoin .erasing).withWriteOnce .nonErasing).PolyBounded 1 :=
  (ephemeralCoin_polyBounded .erasing).withWriteOnce .nonErasing

/-! ### 3. Concrete separation: coin-exposing write-once storage breaks emulation -/

private def extractCoinFromReport
    (rep : AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool))) : Option Bool :=
  match rep with
  | .corrupt (some r) =>
      match r.current.tape with
      | some (rec₀ :: _) =>
          match rec₀.coins with
          | ⟨1, c⟩ :: _ => some (decide (c = 0))
          | _ => none
      | _ => none
  | _ => none

/-- Distinguishing environment with budget `5`: checks initial `.status` is empty, triggers
party `0` to flip its coin, corrupts party `0` mid-run, verifies party `1` remained honest via
`.status`, polls party `1`, and checks whether the coin extracted from party `0`'s write-once tape
equals party `1`'s output. -/
def Z_coinLeak :
    AdaptiveEnvironment 2 EphIn Bool
      (AdaptiveNetQ 2 EphIn Unit)
      (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool))) :=
  fun _ _ => do
    let st0 : Finset (Fin 2) ← ProbOracleComp.query
      (spec := adaptiveExecSpec 2 EphIn Bool (AdaptiveNetQ 2 EphIn Unit)
        (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool))))
      (Sum.inl .status)
    let _ ← ProbOracleComp.query
      (spec := adaptiveExecSpec 2 EphIn Bool (AdaptiveNetQ 2 EphIn Unit)
        (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool))))
      (Sum.inl (.party 0 .go))
    let rep0 : AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool)) ←
      ProbOracleComp.query
        (spec := adaptiveExecSpec 2 EphIn Bool (AdaptiveNetQ 2 EphIn Unit)
          (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool))))
        (Sum.inr (.corrupt 0))
    let st1 : Finset (Fin 2) ← ProbOracleComp.query
      (spec := adaptiveExecSpec 2 EphIn Bool (AdaptiveNetQ 2 EphIn Unit)
        (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool))))
      (Sum.inl .status)
    let out1 : Option Bool ← ProbOracleComp.query
      (spec := adaptiveExecSpec 2 EphIn Bool (AdaptiveNetQ 2 EphIn Unit)
        (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool))))
      (Sum.inl (.party 1 .poll))
    pure (match extractCoinFromReport rep0, out1 with
      | some g, some b => decide (st0 = ∅ ∧ st1 = ({0} : Finset (Fin 2)) ∧ g = b)
      | _, _ => false)

theorem Z_coinLeak_polyBounded : Z_coinLeak.PolyBounded 5 := fun κ _ => by
  dsimp only [Z_coinLeak]
  rw [Polynomial.eval_ofNat]
  refine OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
    OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
      OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
        OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
          OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query _) fun _ =>
            OracleComp.IsCostBounded.pure _ 0

/-- In the real world (`(ephemeralCoin .erasing).withWriteOnce .nonErasing` + dummy adversary),
`Z_coinLeak` extracts `c` from party `0`'s write-once `coins` tape and outputs `true` w.p. `1`. -/
theorem eval_real_Z_coinLeak (κ : ℕ) (z : List Bool) :
    (adaptiveExec .adaptive ((ephemeralCoin .erasing).withWriteOnce .nonErasing)
      (adaptiveDummyAdversary (fun _ => ∅) _ _) Z_coinLeak κ z).eval = PMF.pure true := by
  rw [adaptiveExec_dummyAdversary, Machine.run, Machine.link]
  let Pwo := (ephemeralCoin .erasing).withWriteOnce .nonErasing
  let R := adaptiveRouter .adaptive Pwo κ ∅
  have hinit : R.init = pure
      { inner := { inner := none, initCoins := [], tapes := fun _ => [] }
        corrupted := ∅
        trace := fun _ => [{ current := none, tape := some [] }] } := by
    have hfold : List.foldl (fun (acc : WriteOnceState (Option Bool) EphIn Bool (Option Bool) 2)
          (_ : Fin 2) => { inner := acc.inner, initCoins := acc.initCoins, tapes := acc.tapes })
        ({ inner := none, initCoins := [], tapes := fun _ => [] } :
          WriteOnceState (Option Bool) EphIn Bool (Option Bool) 2) (List.finRange 2) =
        { inner := none, initCoins := [], tapes := fun _ => [] } := rfl
    dsimp only [R, adaptiveRouter, Pwo, AdaptiveProtocol.withWriteOnce, ephemeralCoin,
      IdealFunctionality.toAdaptive, F_ephemeral, AdaptiveProtocol.applyInitialCorruptions,
      ephemeralReveal, recordProbCoins, recordProbCoinsFrom]
    simp only [OracleComp.interpret_pure, StateT.run_pure, Finset.notMem_empty, ↓reduceIte,
      ite_self, hfold, pure_bind]
  change closeEval (ProbOracleComp.sample R.init >>= fun s =>
    Prod.fst <$> R.runFrom (Z_coinLeak κ z) s) = PMF.pure true
  erw [hinit, closeEval_bind, closeEval_sample, ProbComp.eval_pure, PMF.pure_bind]
  dsimp only [Z_coinLeak]
  erw [Machine.runFrom_bind, Machine.runFrom_query]
  dsimp only [R, adaptiveRouter, StateT.run]
  erw [pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
  have hgo_step :
      (R.handle (.inl (.party 0 .go))).run
          { inner := { inner := none, initCoins := [], tapes := fun _ => [] }
            corrupted := ∅
            trace := fun _ => [{ current := none, tape := some [] }] } =
        ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
          let b := decide (c = 0)
          let rec₀ : PartyActivationRecord EphIn Bool (Option Bool) :=
            { input := .go, output := none, coins := [⟨1, c⟩], postView := none }
          let s1 : WriteOnceState (Option Bool) EphIn Bool (Option Bool) 2 :=
            { inner := some b, initCoins := [], tapes := fun j => if j = 0 then [rec₀] else [] }
          pure (none, Pwo.recordSnapshot κ s1 ∅
            (fun _ => [{ current := none, tape := some [] }])) := by
    dsimp only [R, Pwo, adaptiveRouter, AdaptiveProtocol.withWriteOnce, ephemeralCoin,
      IdealFunctionality.toAdaptive, F_ephemeral, ephemeralReveal, StateT.run]
    simp only [Finset.notMem_empty, ↓reduceIte, Fin.val_zero, zero_ne_one, Option.isNone_none,
      and_self, ProbOracleComp.sample_bind, ProbOracleComp.sample_pure, recordCoins,
      recordCoinsFrom_bind, recordCoinsFrom_sample_unifFin, recordCoinsFrom_pure,
      bind_map_left, pure_bind, List.nil_append, bind_assoc]
    rfl
  erw [hgo_step, bind_assoc, map_bind, closeEval_bind, closeEval_sample]
  rw [← PMF.bind_const (ProbComp.unifFin 1).eval (PMF.pure true)]
  refine congrArg (PMF.bind (ProbComp.unifFin 1).eval) (funext fun c => ?_)
  erw [pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
  dsimp only [R, Pwo, adaptiveRouter, AdaptiveProtocol.withWriteOnce,
    AdaptiveProtocol.recordSnapshot, AdaptiveProtocol.corruptionReport, StateT.run]
  simp only [Finset.notMem_empty, ↓reduceIte]
  erw [pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
  dsimp only [StateT.run]
  erw [pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
  dsimp only [StateT.run, ephemeralCoin, IdealFunctionality.toAdaptive, F_ephemeral]
  simp only [Finset.mem_insert, Fin.isValue, Finset.notMem_empty, or_false, ↓reduceIte,
    Fin.val_one, Fin.reduceEq, ProbOracleComp.sample_pure]
  erw [pure_bind, Machine.runFrom_pure, map_pure, closeEval_pure]
  simp only [extractCoinFromReport]
  exact congrArg PMF.pure (decide_eq_true ⟨trivial, rfl, trivial⟩)

private theorem corrupted_subset_of_mem_support_F_eph {α : Type} (κ : ℕ) (C₀ : Finset (Fin 2))
    (prog : ProbOracleComp
      (adaptiveProtocolSpec 2 EphIn Bool Unit Unit (Option Bool)) α)
    (rs : AdaptiveRouterState (Option Bool) (Option Bool) 2)
    {x : α × AdaptiveRouterState (Option Bool) (Option Bool) 2}
    (hx : x ∈ (closeEval ((adaptiveRouter .adaptive
      (F_ephemeral.toAdaptive ephemeralReveal) κ C₀).runFrom prog rs)).support) :
    rs.corrupted ⊆ x.2.corrupted := by
  refine Machine.mem_support_closeEval_runFrom_invariant
    (adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ C₀)
    (fun _ => True) (fun rs₁ rs₂ => rs₁.corrupted ⊆ rs₂.corrupted)
    (fun _ => Finset.Subset.refl _) (fun h₁₂ h₂₃ => h₁₂.trans h₂₃) prog
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) prog)
    rs hx fun q rs' {y} _ hy => ?_
  rcases q with (⟨i, u⟩ | _) | (⟨i, u⟩ | i | nq)
  · dsimp only [adaptiveRouter, StateT.run] at hy
    by_cases hi : i ∈ rs'.corrupted
    · simp only [hi, ↓reduceIte] at hy
      rcases mem_support_closeEval_pure.mp hy with ⟨rfl, rfl⟩
      exact Finset.Subset.refl _
    · simp only [hi, ↓reduceIte] at hy
      erw [Machine.mem_support_closeEval_bind] at hy
      obtain ⟨_, _, hy'⟩ := hy
      rcases mem_support_closeEval_pure.mp hy' with ⟨rfl, rfl⟩
      exact Finset.Subset.refl _
  · dsimp only [adaptiveRouter, StateT.run] at hy
    rcases mem_support_closeEval_pure.mp hy with ⟨rfl, rfl⟩
    exact Finset.Subset.refl _
  · dsimp only [adaptiveRouter, StateT.run] at hy
    by_cases hi : i ∈ rs'.corrupted
    · simp only [hi, ↓reduceIte] at hy
      erw [Machine.mem_support_closeEval_bind] at hy
      obtain ⟨_, _, hy'⟩ := hy
      rcases mem_support_closeEval_pure.mp hy' with ⟨rfl, rfl⟩
      exact Finset.Subset.refl _
    · simp only [hi, ↓reduceIte] at hy
      rcases mem_support_closeEval_pure.mp hy with ⟨rfl, rfl⟩
      exact Finset.Subset.refl _
  · dsimp only [adaptiveRouter, StateT.run] at hy
    rcases mem_support_closeEval_pure.mp hy with ⟨rfl, rfl⟩
    by_cases hi : i ∈ rs'.corrupted
    · simp only [hi, ↓reduceIte]
      exact Finset.Subset.refl _
    · simp only [hi, ↓reduceIte]
      exact Finset.subset_insert _ _
  · dsimp only [adaptiveRouter, StateT.run] at hy
    erw [Machine.mem_support_closeEval_bind] at hy
    obtain ⟨_, _, hy'⟩ := hy
    rcases mem_support_closeEval_pure.mp hy' with ⟨rfl, rfl⟩
    exact Finset.Subset.refl _

private theorem mem_support_F_eph_inner_eq {α : Type} (κ : ℕ) (C₀ : Finset (Fin 2)) (b : Bool)
    (prog : ProbOracleComp
      (adaptiveProtocolSpec 2 EphIn Bool Unit Unit (Option Bool)) α)
    (rs : AdaptiveRouterState (Option Bool) (Option Bool) 2) (hrs : rs.inner = some b)
    {x : α × AdaptiveRouterState (Option Bool) (Option Bool) 2}
    (hx : x ∈ (closeEval ((adaptiveRouter .adaptive
      (F_ephemeral.toAdaptive ephemeralReveal) κ C₀).runFrom prog rs)).support) :
    x.2.inner = some b := by
  have hinv := Machine.mem_support_closeEval_runFrom_invariant
    (adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ C₀)
    (fun _ => True) (fun rs₁ rs₂ => rs₁.inner = some b → rs₂.inner = some b)
    (fun _ h => h) (fun h₁₂ h₂₃ h => h₂₃ (h₁₂ h)) prog
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) prog)
    rs hx fun q rs' {y} _ hy hinner => by
      rcases q with (⟨i, u⟩ | _) | (⟨i, u⟩ | i | nq)
      · dsimp only [adaptiveRouter, StateT.run] at hy
        by_cases hi : i ∈ rs'.corrupted
        · simp only [hi, ↓reduceIte] at hy
          rcases mem_support_closeEval_pure.mp hy with ⟨rfl, rfl⟩; exact hinner
        · simp only [hi, ↓reduceIte] at hy
          erw [Machine.mem_support_closeEval_bind] at hy
          obtain ⟨⟨_, s'⟩, hs', hy'⟩ := hy
          rcases mem_support_closeEval_pure.mp hy' with ⟨rfl, rfl⟩
          cases u <;>
            simp only [F_ephemeral, IdealFunctionality.toAdaptive, StateT.run, hinner,
              Option.isNone_some, Bool.false_eq_true, and_false, ↓reduceIte,
              ProbOracleComp.sample_pure] at hs'
          · erw [mem_support_closeEval_pure] at hs'; rcases hs' with ⟨rfl, rfl⟩; rfl
          · erw [mem_support_closeEval_pure] at hs'; rcases hs' with ⟨rfl, rfl⟩; rfl
      · dsimp only [adaptiveRouter, StateT.run] at hy
        rcases mem_support_closeEval_pure.mp hy with ⟨rfl, rfl⟩; exact hinner
      · dsimp only [adaptiveRouter, StateT.run] at hy
        by_cases hi : i ∈ rs'.corrupted
        · simp only [hi, ↓reduceIte] at hy
          erw [Machine.mem_support_closeEval_bind] at hy
          obtain ⟨⟨_, s'⟩, hs', hy'⟩ := hy
          rcases mem_support_closeEval_pure.mp hy' with ⟨rfl, rfl⟩
          cases u <;>
            simp only [F_ephemeral, IdealFunctionality.toAdaptive, StateT.run, hinner,
              Option.isNone_some, Bool.false_eq_true, and_false, ↓reduceIte,
              ProbOracleComp.sample_pure] at hs'
          · erw [mem_support_closeEval_pure] at hs'; rcases hs' with ⟨rfl, rfl⟩; rfl
          · erw [mem_support_closeEval_pure] at hs'; rcases hs' with ⟨rfl, rfl⟩; rfl
        · simp only [hi, ↓reduceIte] at hy
          rcases mem_support_closeEval_pure.mp hy with ⟨rfl, rfl⟩; exact hinner
      · dsimp only [adaptiveRouter, StateT.run] at hy
        rcases mem_support_closeEval_pure.mp hy with ⟨rfl, rfl⟩
        dsimp only [IdealFunctionality.toAdaptive]
        by_cases hi : i ∈ rs'.corrupted <;> simp [hi, hinner]
      · dsimp only [adaptiveRouter, StateT.run] at hy
        erw [Machine.mem_support_closeEval_bind] at hy
        obtain ⟨⟨_, s'⟩, hs', hy'⟩ := hy
        rcases mem_support_closeEval_pure.mp hy' with ⟨rfl, rfl⟩
        simp only [F_ephemeral, IdealFunctionality.toAdaptive, StateT.run] at hs'
        erw [mem_support_closeEval_pure] at hs'
        rcases hs' with ⟨rfl, rfl⟩; exact hinner
  exact hinv hrs

private theorem router_F_eph_no1_indep {α : Type} (κ : ℕ) (b : Bool)
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ 2 EphIn Unit)
      (AdaptiveNetR Bool Unit (Option Bool))) α)
    (C : Finset (Fin 2)) (h1 : (1 : Fin 2) ∉ C)
    (tr₁ tr₂ : Fin 2 → List (Option Bool))
    (g : α × Finset (Fin 2) → ENNReal)
    (hg : ∀ a C', (1 : Fin 2) ∈ C' → g (a, C') = 0) :
    ∑' x, closeEval ((adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
        (liftAdaptiveNet netProg) { inner := some b, corrupted := C, trace := tr₁ }) x *
        g (x.1, x.2.corrupted) =
      ∑' x, closeEval ((adaptiveRouter .adaptive
          (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
        (liftAdaptiveNet netProg) { inner := some false, corrupted := C, trace := tr₂ }) x *
        g (x.1, x.2.corrupted) := by
  induction netProg using OracleComp.induction generalizing C tr₁ tr₂ with
  | pure a =>
    dsimp only [liftAdaptiveNet]
    erw [Machine.liftRightProgram_pure, Machine.runFrom_pure, closeEval_pure]
    erw [Machine.runFrom_pure, closeEval_pure]
    let rs₁ : AdaptiveRouterState (Option Bool) (Option Bool) 2 :=
      { inner := some b, corrupted := C, trace := tr₁ }
    let rs₂ : AdaptiveRouterState (Option Bool) (Option Bool) 2 :=
      { inner := some false, corrupted := C, trace := tr₂ }
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
          closeEval ((adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
            (liftAdaptiveNet (OracleComp.query (Sum.inl k) >>= cont))
            { inner := some b', corrupted := C, trace := tr }) =
          (ProbComp.unifFin k).eval.bind fun a =>
            closeEval ((adaptiveRouter .adaptive
              (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
              (liftAdaptiveNet (cont a)) { inner := some b', corrupted := C, trace := tr }) := by
        dsimp only [liftAdaptiveNet]
        rw [Machine.liftRightProgram_bind]
        have hlu : Machine.liftRightProgram (adaptivePartySpec 2 EphIn Bool)
            (OracleComp.query (spec := probOracleSpec
              (netSpec (AdaptiveNetQ 2 EphIn Unit) (AdaptiveNetR Bool Unit (Option Bool))))
              (Sum.inl k)) = ProbOracleComp.sample (ProbComp.unifFin k) := by
          simp only [Machine.liftRightProgram, ProbOracleComp.sample, ProbComp.unifFin,
            OracleComp.interpret_query, sumHandler, OracleComp.substitute_query]
        rw [hlu]
        erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left, closeEval_bind,
          closeEval_sample]
      rw [hstep b tr₁, hstep false tr₂]
      simp only [Probability.PMF.tsum_bind_mul]
      exact tsum_congr fun a => congrArg ((ProbComp.unifFin k).eval a * ·) (ih a C h1 tr₁ tr₂)
    · have hbind (b' : Bool) (tr : Fin 2 → List (Option Bool)) :
          closeEval ((adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
            (liftAdaptiveNet (OracleComp.query (Sum.inr q) >>= cont))
            { inner := some b', corrupted := C, trace := tr }) =
          (closeEval (((adaptiveRouter .adaptive
            (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).handle (.inr q)).run
              { inner := some b', corrupted := C, trace := tr })).bind fun y =>
            closeEval ((adaptiveRouter .adaptive
              (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
              (liftAdaptiveNet (cont y.1)) y.2) := by
        dsimp only [liftAdaptiveNet]
        erw [Machine.liftRightProgram_bind, Machine.liftRightProgram_query, Machine.runFrom_bind,
          Machine.runFrom_query, closeEval_bind]
      rw [hbind b tr₁, hbind false tr₂]
      cases q with
      | party i u =>
        have hi : i = 0 ∨ i = 1 := match i with
          | ⟨0, _⟩ => Or.inl (Fin.ext rfl)
          | ⟨1, _⟩ => Or.inr (Fin.ext rfl)
        rcases hi with rfl | rfl
        · by_cases h0 : (0 : Fin 2) ∈ C
          · cases u
            · have hp (b' : Bool) (tr : Fin 2 → List (Option Bool)) :
                  closeEval (((adaptiveRouter .adaptive
                    (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).handle
                      (.inr (.party 0 .go))).run
                        { inner := some b', corrupted := C, trace := tr }) =
                  PMF.pure (.party none,
                    { inner := some b'
                      corrupted := C
                      trace := fun j => tr j ++ [ephemeralReveal κ (some b') j] }) := by
                simp only [adaptiveRouter, F_ephemeral, IdealFunctionality.toAdaptive, StateT.run,
                  h0, Fin.val_zero, Option.isNone_some, Bool.false_eq_true, and_false, ↓reduceIte,
                  ProbOracleComp.sample_pure, closeEval_bind, closeEval_pure,
                  AdaptiveProtocol.recordSnapshot, PMF.pure_bind]
              rw [hp b tr₁, hp false tr₂, PMF.pure_bind, PMF.pure_bind]
              exact ih _ C h1 _ _
            · have hp (b' : Bool) (tr : Fin 2 → List (Option Bool)) :
                  closeEval (((adaptiveRouter .adaptive
                    (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).handle
                      (.inr (.party 0 .poll))).run
                        { inner := some b', corrupted := C, trace := tr }) =
                  PMF.pure (.party none,
                    { inner := some b'
                      corrupted := C
                      trace := fun j => tr j ++ [ephemeralReveal κ (some b') j] }) := by
                simp only [adaptiveRouter, F_ephemeral, IdealFunctionality.toAdaptive, StateT.run,
                  h0, Fin.val_zero, ↓reduceIte, ProbOracleComp.sample_pure, closeEval_pure,
                  AdaptiveProtocol.recordSnapshot, pure_bind, Nat.zero_ne_one]
              rw [hp b tr₁, hp false tr₂, PMF.pure_bind, PMF.pure_bind]
              exact ih _ C h1 _ _
          · have hp (b' : Bool) (tr : Fin 2 → List (Option Bool)) :
                closeEval (((adaptiveRouter .adaptive
                  (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).handle (.inr (.party 0 u))).run
                    { inner := some b', corrupted := C, trace := tr }) =
                PMF.pure (.party none, { inner := some b', corrupted := C, trace := tr }) := by
              simp only [adaptiveRouter, StateT.run, h0, ↓reduceIte, closeEval_pure]
            rw [hp b tr₁, hp false tr₂, PMF.pure_bind, PMF.pure_bind]
            exact ih _ C h1 tr₁ tr₂
        · have hp (b' : Bool) (tr : Fin 2 → List (Option Bool)) :
              closeEval (((adaptiveRouter .adaptive
                (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).handle (.inr (.party 1 u))).run
                  { inner := some b', corrupted := C, trace := tr }) =
              PMF.pure (.party none, { inner := some b', corrupted := C, trace := tr }) := by
            simp only [adaptiveRouter, StateT.run, h1, ↓reduceIte, closeEval_pure]
          rw [hp b tr₁, hp false tr₂, PMF.pure_bind, PMF.pure_bind]
          exact ih _ C h1 tr₁ tr₂
      | net u =>
        cases u
        have hp (b' : Bool) (tr : Fin 2 → List (Option Bool)) :
            closeEval (((adaptiveRouter .adaptive
              (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).handle (.inr (.net ()))).run
                { inner := some b', corrupted := C, trace := tr }) =
            PMF.pure (.net (),
              { inner := some b'
                corrupted := C
                trace := fun j => tr j ++ [ephemeralReveal κ (some b') j] }) := by
          simp only [adaptiveRouter, F_ephemeral, IdealFunctionality.toAdaptive, StateT.run,
            ProbOracleComp.sample_pure, closeEval_pure, AdaptiveProtocol.recordSnapshot, pure_bind]
        rw [hp b tr₁, hp false tr₂, PMF.pure_bind, PMF.pure_bind]
        exact ih _ C h1 _ _
      | corrupt i =>
        have hmem_ne : PartyMemory.erasing ≠ .nonErasing := by decide
        have hi : i = 0 ∨ i = 1 := match i with
          | ⟨0, _⟩ => Or.inl (Fin.ext rfl)
          | ⟨1, _⟩ => Or.inr (Fin.ext rfl)
        rcases hi with rfl | rfl
        · dsimp only [adaptiveRouter, StateT.run]
          split_ifs with h0
          · simp only [F_ephemeral, IdealFunctionality.toAdaptive, ephemeralReveal,
              AdaptiveProtocol.corruptionReport, Fin.val_zero, hmem_ne, ↓reduceIte,
              closeEval_pure, PMF.pure_bind]
            exact ih _ C h1 tr₁ tr₂
          · simp only [F_ephemeral, IdealFunctionality.toAdaptive, ephemeralReveal,
              AdaptiveProtocol.corruptionReport, Fin.val_zero, hmem_ne, ↓reduceIte,
              closeEval_pure, PMF.pure_bind]
            have h1' : (1 : Fin 2) ∉ insert 0 C := by simpa [Finset.mem_insert] using h1
            exact ih _ (insert 0 C) h1' tr₁ tr₂
        · simp only [adaptiveRouter, F_ephemeral, IdealFunctionality.toAdaptive, ephemeralReveal,
            AdaptiveProtocol.corruptionReport, StateT.run, Fin.val_one, hmem_ne,
            ↓reduceIte, closeEval_pure, PMF.pure_bind, h1]
          have hzero (b' : Bool) (tr : Fin 2 → List (Option Bool)) :
              ∑' x, closeEval ((adaptiveRouter .adaptive
                  (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
                  (liftAdaptiveNet (cont (.corrupt (some { current := some b', history := none }))))
                  { inner := some b', corrupted := insert 1 C, trace := tr }) x *
                g (x.1, x.2.corrupted) = 0 := by
            rw [tsum_eq_zero_iff]
            intro x
            by_cases hx : closeEval ((adaptiveRouter .adaptive
                (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
                (liftAdaptiveNet (cont (.corrupt (some { current := some b', history := none }))))
                { inner := some b', corrupted := insert 1 C, trace := tr }) x = 0
            · exact mul_eq_zero_of_left hx _
            · have hxsup : x ∈ (closeEval ((adaptiveRouter .adaptive
                  (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
                  (liftAdaptiveNet (cont (.corrupt (some { current := some b', history := none }))))
                  { inner := some b', corrupted := insert 1 C, trace := tr })).support := by
                erw [PMF.mem_support_iff]; exact hx
              have hsub := corrupted_subset_of_mem_support_F_eph κ ∅ _ _ hxsup
              exact mul_eq_zero_of_right _ (hg x.1 x.2.corrupted
                (hsub (Finset.mem_insert_self 1 C)))
          erw [hzero b tr₁, hzero false tr₂]

/-- In the ideal world (`F_ephemeral.toAdaptive ephemeralReveal`), any simulator `S` fails to
prevent `Z_coinLeak` from distinguishing with probability better than `1 / 2`. -/
theorem eval_ideal_Z_coinLeak_le_half
    (S : AdaptiveAdversary 2 EphIn Bool Unit Unit (Option Bool)
      (AdaptiveNetQ 2 EphIn Unit)
      (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool)))) (κ : ℕ) :
    (adaptiveExec .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S Z_coinLeak κ []).eval
        true ≤ 1 / 2 := by
  have hrun_adv : ∀ (sS : (S.machine κ).State),
      (liftAdaptiveAdversary (S.machine κ)).runFrom (Z_coinLeak κ []) sS =
        ProbOracleComp.query
            (spec := adaptiveProtocolSpec 2 EphIn Bool Unit Unit (Option Bool))
            (.inl .status) >>= fun (C0 : Finset (Fin 2)) =>
        ProbOracleComp.query (.inl (.party 0 .go)) >>= fun _ =>
        liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS) >>= fun x1 =>
        ProbOracleComp.query (.inl .status) >>= fun (C1 : Finset (Fin 2)) =>
        ProbOracleComp.query (.inl (.party 1 .poll)) >>= fun optB =>
        pure (match extractCoinFromReport x1.1, optB with
          | some g, some b => decide (C0 = ∅ ∧ C1 = ({0} : Finset (Fin 2)) ∧ g = b)
          | _, _ => false, x1.2) := by
    intro sS
    dsimp only [Z_coinLeak]
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    dsimp only [liftAdaptiveAdversary, Machine.liftRight]
    erw [StateT.run_lift, bind_assoc]
  have hrun_exec : ∀ (sS : (S.machine κ).State)
      (rs : (adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal)
        κ (S.initial κ)).State),
      (adaptiveExecMachine .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S κ).runFrom
          (Z_coinLeak κ []) (sS, rs) =
        let p0 := if (0 : Fin 2) ∈ rs.corrupted then pure (none, rs)
          else do
            let (out, s') ← ((F_ephemeral.toAdaptive ephemeralReveal).machine κ |>.handle
              (.inl (0, .go))).run rs.inner
            pure (out, (F_ephemeral.toAdaptive ephemeralReveal).recordSnapshot κ s'
              rs.corrupted rs.trace)
        p0 >>= fun x0 =>
        ((adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ (S.initial κ)).runFrom
          (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS)) x0.2) >>= fun x1 =>
        let p3 := if (1 : Fin 2) ∈ x1.2.corrupted then pure (none, x1.2)
          else do
            let (out, s') ← ((F_ephemeral.toAdaptive ephemeralReveal).machine κ |>.handle
              (.inl (1, .poll))).run x1.2.inner
            pure (out, (F_ephemeral.toAdaptive ephemeralReveal).recordSnapshot κ s'
              x1.2.corrupted x1.2.trace)
        p3 >>= fun x3 =>
        pure (let ⟨⟨netReply, sS'⟩, rs'⟩ := x1
          (match extractCoinFromReport netReply, x3.1 with
          | some g, some b =>
              decide (rs.corrupted = ∅ ∧ rs'.corrupted = ({0} : Finset (Fin 2)) ∧ g = b)
          | _, _ => false, (sS', x3.2))) := by
    intro sS rs
    let M := adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ (S.initial κ)
    have hparty (i : Fin 2) (x : EphIn) (rs' : M.State) :
        (M.handle (.inl (.party i x))).run rs' =
          if i ∈ rs'.corrupted then pure (none, rs')
          else ((F_ephemeral.toAdaptive ephemeralReveal).machine κ |>.handle
              (.inl (i, x))).run rs'.inner >>=
            fun p => pure (p.1, (F_ephemeral.toAdaptive ephemeralReveal).recordSnapshot κ p.2
              rs'.corrupted rs'.trace) := rfl
    have hstatus (rs' : M.State) :
        (M.handle (.inl .status)).run rs' = pure (rs'.corrupted, rs') := rfl
    dsimp only [adaptiveExecMachine]
    erw [Machine.runFrom_comp, hrun_adv]
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hstatus, pure_bind]
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hparty, map_bind]
    refine bind_congr fun x0 => ?_
    erw [Machine.runFrom_bind (M := M), map_bind]
    refine bind_congr fun x1 => ?_
    erw [Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hstatus, pure_bind,
      Machine.runFrom_bind (M := M), Machine.runFrom_query (M := M), hparty, map_bind]
    refine bind_congr fun x3 => ?_
    erw [Machine.runFrom_pure (M := M)]
    simp only [map_pure, Equiv.prodAssoc_apply]
    rfl
  have hinit_exec :
      ProbOracleComp.sample (spec := OracleSpec.empty)
          (adaptiveExecMachine .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S κ).init =
        ProbOracleComp.sample (spec := OracleSpec.empty) (S.machine κ).init >>= fun sS =>
          pure (sS, { inner := none, corrupted := S.initial κ, trace := fun _ => [none] }) := by
    have hfold2 : List.foldl (fun acc (_ : Fin 2) => acc) (none : Option Bool)
        (List.finRange 2) = none := rfl
    dsimp only [adaptiveExecMachine, Machine.comp_init, liftAdaptiveAdversary, Machine.liftRight,
      adaptiveRouter, F_ephemeral, IdealFunctionality.toAdaptive,
      AdaptiveProtocol.applyInitialCorruptions, ephemeralReveal]
    simp only [ite_self, hfold2, pure_bind]
    erw [ProbOracleComp.sample_bind]
    refine bind_congr fun sS => ?_
    erw [ProbOracleComp.sample_pure]
    rfl
  have hgo (s : ((F_ephemeral.toAdaptive ephemeralReveal).machine κ).State) :
      ((F_ephemeral.toAdaptive ephemeralReveal).machine κ |>.handle (.inl (0, .go))).run s =
        if s.isNone = true then
          ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
            pure ((none : protocolSpec 2 EphIn Bool Unit Unit (.inl (0, .go))),
              (some (decide (c = 0)) : Option Bool))
        else pure ((none : protocolSpec 2 EphIn Bool Unit Unit (.inl (0, .go))), s) := by
    simp only [F_ephemeral, IdealFunctionality.toAdaptive, StateT.run, Fin.val_zero, true_and]
    split_ifs <;> simp [ProbOracleComp.sample_pure]
  have hpoll (s : ((F_ephemeral.toAdaptive ephemeralReveal).machine κ).State) :
      ((F_ephemeral.toAdaptive ephemeralReveal).machine κ |>.handle (.inl (1, .poll))).run s =
        pure ((s : protocolSpec 2 EphIn Bool Unit Unit (.inl (1, .poll))), s) := by
    simp only [F_ephemeral, IdealFunctionality.toAdaptive, StateT.run, Fin.val_one, ↓reduceIte,
      ProbOracleComp.sample_pure]
  have hsnap (s : ((F_ephemeral.toAdaptive ephemeralReveal).machine κ).State)
      (C : Finset (Fin 2)) (tr : Fin 2 → List (Option Bool)) :
      (F_ephemeral.toAdaptive ephemeralReveal).recordSnapshot κ s C tr =
        { inner := s, corrupted := C, trace := fun j => tr j ++ [ephemeralReveal κ s j] } := rfl
  have hfalse_of_none (hc : ∀ sS,
      closeEval (Prod.fst <$>
        (adaptiveExecMachine .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S κ).runFrom
          (Z_coinLeak κ [])
          (sS, { inner := none, corrupted := S.initial κ, trace := fun _ => [none] })) =
        PMF.pure false) :
      (adaptiveExec .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S Z_coinLeak κ []).eval
          true ≤ 1 / 2 := by
    have hev :
        (adaptiveExec .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S Z_coinLeak κ []).eval =
          PMF.pure false := by
      change closeEval (ProbOracleComp.sample
          (adaptiveExecMachine .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S κ).init >>=
            fun s =>
          Prod.fst <$>
            (adaptiveExecMachine .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S κ).runFrom
              (Z_coinLeak κ []) s) = PMF.pure false
      rw [hinit_exec]
      erw [bind_assoc, closeEval_bind]
      rw [← PMF.bind_const (closeEval (ProbOracleComp.sample (S.machine κ).init)) (PMF.pure false)]
      congr 1; funext sS; erw [pure_bind, hc]
    rw [hev, PMF.pure_apply]
    simp
  by_cases hinit : S.initial κ = ∅
  · have h0_not : (0 : Fin 2) ∉ (∅ : Finset (Fin 2)) := Finset.notMem_empty 0
    have h1_not : (1 : Fin 2) ∉ (∅ : Finset (Fin 2)) := Finset.notMem_empty 1
    let gMatch (b : Bool) :
        (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool)) × (S.machine κ).State) ×
          Finset (Fin 2) → ENNReal := fun (res, C') =>
      if C' = ({0} : Finset (Fin 2)) then
        if extractCoinFromReport res.1 = some b then 1 else 0
      else 0
    have hg_one (b : Bool) res C' (h1mem : (1 : Fin 2) ∈ C') : gMatch b (res, C') = 0 := by
      have hne : C' ≠ {0} := by
        intro heq; rw [heq] at h1mem; revert h1mem; decide
      simp [gMatch, hne]
    let trC (c : Fin 2) : Fin 2 → List (Option Bool) := fun j =>
      [none, if j.val = 1 then some (decide (c = 0)) else none]
    have hrun_router_eq :
        ∀ {α : Type}
          (p : ProbOracleComp (adaptiveProtocolSpec 2 EphIn Bool Unit Unit (Option Bool)) α)
          (rs : AdaptiveRouterState (Option Bool) (Option Bool) 2),
          (adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ
              (S.initial κ)).runFrom p rs =
            (adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
              p rs := by
      intro α p rs; dsimp only [adaptiveRouter]; rw [hinit]
    have htrC_eq : ∀ c : Fin 2,
        (fun j : Fin 2 => [none, ephemeralReveal κ (some (decide (c = 0))) j]) = trC c := by
      intro c; funext j; rfl
    have hexp :
        (adaptiveExec .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S Z_coinLeak κ []).eval
            true =
          ∑' sS : (S.machine κ).State, closeEval (ProbOracleComp.sample (S.machine κ).init) sS *
            ∑' c : Fin 2, (ProbComp.unifFin 1).eval c *
              ∑' x, closeEval
                  ((adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
                    (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
                    { inner := some (decide (c = 0))
                      corrupted := ∅
                      trace := trC c }) x *
                gMatch (decide (c = 0)) (x.1, x.2.corrupted) := by
      change (closeEval (ProbOracleComp.sample
          (adaptiveExecMachine .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S κ).init >>=
            fun s =>
          Prod.fst <$>
            (adaptiveExecMachine .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S κ).runFrom
              (Z_coinLeak κ []) s)) true = _
      rw [hinit_exec]
      erw [bind_assoc, closeEval_bind]
      rw [PMF.bind_apply]
      refine tsum_congr fun sS =>
        congrArg (closeEval (ProbOracleComp.sample (S.machine κ).init) sS * ·) ?_
      erw [pure_bind, hrun_exec]
      simp only [hinit, h0_not, ↓reduceIte]
      erw [hgo]
      simp only [Option.isNone_none, ↓reduceIte, hsnap]
      erw [bind_assoc, bind_assoc, map_bind]
      rw [closeEval_bind, closeEval_sample, PMF.bind_apply]
      refine tsum_congr fun c => congrArg ((ProbComp.unifFin 1).eval c * ·) ?_
      erw [pure_bind, pure_bind, htrC_eq, map_bind]
      rw [closeEval_bind, PMF.bind_apply]
      refine tsum_congr fun x => ?_
      erw [hrun_router_eq]
      by_cases hx0 : closeEval ((adaptiveRouter .adaptive
          (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
          (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
          { inner := some (decide (c = 0)), corrupted := ∅, trace := trC c }) x = 0
      · erw [hx0]; simp only [zero_mul]
      · have hxsup : x ∈ (closeEval ((adaptiveRouter .adaptive
            (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
            (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
            { inner := some (decide (c = 0)), corrupted := ∅, trace := trC c })).support := by
          erw [PMF.mem_support_iff]; exact hx0
        have hinner_eq := mem_support_F_eph_inner_eq κ ∅ (decide (c = 0))
          (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
          { inner := some (decide (c = 0)), corrupted := ∅, trace := trC c } rfl hxsup
        refine congrArg (_ * ·) ?_
        by_cases h1x : (1 : Fin 2) ∈ x.2.corrupted
        · simp only [h1x, ↓reduceIte, pure_bind, map_pure, closeEval_pure, PMF.pure_apply]
          have hCne : x.2.corrupted ≠ {0} := by
            intro heq; rw [heq] at h1x; revert h1x; decide
          cases hopt : extractCoinFromReport x.1.1 <;> simp [gMatch, hCne]
        · simp only [h1x, ↓reduceIte]
          erw [hpoll]
          rw [hinner_eq]
          erw [pure_bind, map_pure, closeEval_pure, PMF.pure_apply]
          cases hopt : extractCoinFromReport x.1.1 with
          | none => simp [gMatch, hopt]
          | some g =>
            by_cases hC : x.2.corrupted = {0} <;> by_cases hgb : g = decide (c = 0) <;>
              simp [gMatch, hopt, hC, hgb]
    rw [hexp]
    have hinner (sS : (S.machine κ).State) :
        ∑' c : Fin 2, (ProbComp.unifFin 1).eval c *
            ∑' x, closeEval ((adaptiveRouter .adaptive
                (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
              (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
              { inner := some (decide (c = 0)), corrupted := ∅, trace := trC c }) x *
              gMatch (decide (c = 0)) (x.1, x.2.corrupted) ≤ 1 / 2 := by
      let μ : PMF ((AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool)) ×
          (S.machine κ).State) × AdaptiveRouterState (Option Bool) (Option Bool) 2) :=
        closeEval ((adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
          (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
          { inner := some false, corrupted := ∅, trace := fun _ => [none] })
      have hind (c : Fin 2) :
          ∑' x, closeEval ((adaptiveRouter .adaptive
              (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
              (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
              { inner := some (decide (c = 0)), corrupted := ∅, trace := trC c }) x *
            gMatch (decide (c = 0)) (x.1, x.2.corrupted) =
          ∑' x, μ x * gMatch (decide (c = 0)) (x.1, x.2.corrupted) :=
        router_F_eph_no1_indep κ (decide (c = 0)) (((S.machine κ).handle (.corrupt 0)).run sS)
          ∅ h1_not (trC c) (fun _ => [none]) (gMatch (decide (c = 0)))
          (hg_one (decide (c = 0)))
      have hunif (c : Fin 2) :
          (Probability.PMF.uniformOfFintype (Fin (1 + 1))) c = (2 : ENNReal)⁻¹ := by
        simp [Probability.PMF.uniformOfFintype]
      simp_rw [hind, ProbComp.eval_unifFin]
      rw [tsum_fintype, Fin.sum_univ_two]
      simp only [Fin.isValue, hunif, decide_true]
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← tsum_add]
      have hpt (x : (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool)) ×
          (S.machine κ).State) × AdaptiveRouterState (Option Bool) (Option Bool) 2) :
          ((2 : ENNReal)⁻¹) * (μ x * gMatch true (x.1, x.2.corrupted)) +
            ((2 : ENNReal)⁻¹) * (μ x * gMatch false (x.1, x.2.corrupted)) ≤
            ((2 : ENNReal)⁻¹) * μ x := by
        have hdisj :
            gMatch true (x.1, x.2.corrupted) + gMatch false (x.1, x.2.corrupted) ≤ 1 := by
          dsimp [gMatch]
          split_ifs with hC hT hF <;> simp_all
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
              ∑' x, closeEval ((adaptiveRouter .adaptive
                  (F_ephemeral.toAdaptive ephemeralReveal) κ ∅).runFrom
                (liftAdaptiveNet (((S.machine κ).handle (.corrupt 0)).run sS))
                { inner := some (decide (c = 0)), corrupted := ∅, trace := trC c }) x *
                gMatch (decide (c = 0)) (x.1, x.2.corrupted)
        ≤ ∑' sS : (S.machine κ).State,
            closeEval (ProbOracleComp.sample (S.machine κ).init) sS * (1 / 2) :=
          tsum_le_tsum fun sS => mul_le_mul_of_nonneg_left (hinner sS) zero_le
      _ = (∑' sS, closeEval (ProbOracleComp.sample (S.machine κ).init) sS) * (1 / 2) :=
          ENNReal.tsum_mul_right
      _ = 1 / 2 := by rw [PMF.tsum_coe, one_mul]
  · refine hfalse_of_none fun sS => ?_
    erw [hrun_exec]
    have hfalse_fin : ∀ (opt : Option Bool) (C1 : Finset (Fin 2))
        (b1 : Option Bool),
        (match opt, b1 with
        | some g, some b => decide (S.initial κ = ∅ ∧ C1 = ({0} : Finset (Fin 2)) ∧ g = b)
        | _, _ => false) = false := by
      intro opt C1 b1
      cases opt <;> cases b1 <;> simp [hinit]
    simp_rw [hfalse_fin]
    simp only [map_bind, map_pure, closeEval_bind, closeEval_pure, PMF.bind_const]

private theorem writeOnce_advantage_ge_half
    (S : AdaptiveAdversary 2 EphIn Bool Unit Unit (Option Bool)
      (AdaptiveNetQ 2 EphIn Unit)
      (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool)))) (κ : ℕ) :
    (1 / 2 : ℝ) ≤ (adaptiveAdvantage .adaptive
      ((ephemeralCoin .erasing).withWriteOnce .nonErasing)
      (F_ephemeral.toAdaptive ephemeralReveal)
      (adaptiveDummyAdversary (fun _ => ∅) _ _) S Z_coinLeak κ [] : ℝ) := by
  have hreal : ((adaptiveExec .adaptive ((ephemeralCoin .erasing).withWriteOnce .nonErasing)
      (adaptiveDummyAdversary (fun _ => ∅) _ _) Z_coinLeak κ []).eval true).toReal = 1 := by
    rw [eval_real_Z_coinLeak]; simp
  have hideal : ((adaptiveExec .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S
      Z_coinLeak κ []).eval true).toReal ≤ 1 / 2 := by
    simpa [ENNReal.toReal_div] using
      ENNReal.toReal_mono (by norm_num) (eval_ideal_Z_coinLeak_le_half S κ)
  rw [adaptiveAdvantage, Game.coe_advantage, Game.coe_succProbability,
    Game.coe_succProbability, hreal]
  have h := le_abs_self (1 - ((adaptiveExec .adaptive (F_ephemeral.toAdaptive ephemeralReveal) S
    Z_coinLeak κ []).eval true).toReal)
  linarith

/-- Concrete separation witness: `(ephemeralCoin .erasing).withWriteOnce .nonErasing` cannot
adaptively emulate `F_ephemeral.toAdaptive ephemeralReveal` within any bound `< 1 / 2` at
`κ = 0`, `pA = 1`, `pZ = 5`. -/
theorem not_adaptiveEmulatesWithin_writeOnce
    (g : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0)
    (hbound : ε 1 5 0 < 1 / 2) :
    ¬ AdaptiveEmulatesWithin .adaptive
        ((ephemeralCoin .erasing).withWriteOnce .nonErasing)
        (F_ephemeral.toAdaptive ephemeralReveal) g ε := by
  intro h
  obtain ⟨S, _, _, _, hadv⟩ := h (AdaptiveNetQ 2 EphIn Unit)
    (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool)))
    (adaptiveDummyAdversary (fun _ => ∅) _ _) 1 (adaptiveDummyAdversary_polyBounded _ _ _)
  have h1 : (adaptiveAdvantage .adaptive ((ephemeralCoin .erasing).withWriteOnce .nonErasing)
      (F_ephemeral.toAdaptive ephemeralReveal)
      (adaptiveDummyAdversary (fun _ => ∅) _ _) S Z_coinLeak 0 [] : ℝ) ≤ (ε 1 5 0 : ℝ) := by
    exact_mod_cast hadv Z_coinLeak 5 Z_coinLeak_polyBounded 0 []
  have hlow := writeOnce_advantage_ge_half S 0
  have hε_real : (ε 1 5 0 : ℝ) < 1 / 2 := by exact_mod_cast hbound
  linarith

/-- Asymptotic separation witness: `(ephemeralCoin .erasing).withWriteOnce .nonErasing` does
not adaptively emulate `F_ephemeral.toAdaptive ephemeralReveal`, even though
`ephemeralCoin .erasing` already emulates it (`ephemeralCoin_erasing_emulates`). -/
theorem not_adaptiveEmulates_writeOnce :
    ¬ AdaptiveEmulates .adaptive
        ((ephemeralCoin .erasing).withWriteOnce .nonErasing)
        (F_ephemeral.toAdaptive ephemeralReveal) := by
  intro h
  obtain ⟨S, _, _, hadv⟩ := h (AdaptiveNetQ 2 EphIn Unit)
    (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool)))
    (adaptiveDummyAdversary (fun _ => ∅) _ _) 1 (adaptiveDummyAdversary_polyBounded _ _ _)
  obtain ⟨ν, hν, hadvν⟩ := hadv 5
  obtain ⟨κ, hκ⟩ := ((hν 0).eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0) < 1 / 2))).exists
  have h1 : (adaptiveAdvantage .adaptive ((ephemeralCoin .erasing).withWriteOnce .nonErasing)
      (F_ephemeral.toAdaptive ephemeralReveal)
      (adaptiveDummyAdversary (fun _ => ∅) _ _) S Z_coinLeak κ [] : ℝ) ≤ (ν κ : ℝ) := by
    exact_mod_cast hadvν Z_coinLeak Z_coinLeak_polyBounded κ []
  have hlow := writeOnce_advantage_ge_half S κ
  simp only [pow_zero, one_mul] at hκ
  have hκ_real : (ν κ : ℝ) < 1 / 2 := by exact_mod_cast hκ
  linarith

/-! ### 4. Instantiations of write-once storage, transparency, and `.nonErasing` → `.erasing` -/

theorem eraseSecret_writeOnce_tapePrefix (κ : ℕ)
    (prog : ProbOracleComp
      (adaptiveProtocolSpec 2 SecretIn Bool Unit Unit (WriteOnceView SecretIn Bool (Option Bool)))
      (AdaptiveNetR Bool Unit (WriteOnceView SecretIn Bool (Option Bool))))
    {rs' : AdaptiveRouterState
      (WriteOnceState (Fin 2 → Option Bool) SecretIn Bool (Option Bool) 2)
      (WriteOnceView SecretIn Bool (Option Bool)) 2}
    {r : AdaptiveNetR Bool Unit (WriteOnceView SecretIn Bool (Option Bool))}
    (hx : (r, rs') ∈ (closeEval ((adaptiveRouter .adaptive
      ((eraseSecretProto .erasing).withWriteOnce .nonErasing) κ ∅).runFrom
        prog (eraseSecretInitRS .nonErasing))).support) :
    (eraseSecretInitRS .nonErasing).inner.TapePrefix rs'.inner ∧
      (eraseSecretInitRS .nonErasing).corrupted ⊆ rs'.corrupted :=
  mem_support_closeEval_adaptiveRouter_withWriteOnce_tapePrefix
    .adaptive (eraseSecretProto .erasing) .nonErasing κ ∅ prog (eraseSecretInitRS .nonErasing) hx

theorem eraseSecret_writeOnce_noCorrupt {α : Type} (κ : ℕ)
    (program : ProbOracleComp (adaptiveProtocolSpec 2 SecretIn Bool Unit Unit (Option Bool)) α)
    (hno : OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => match q with
        | .inl _ => True
        | .inr (.corrupt _) => False
        | .inr _ => True) program) :
    (Prod.fst <$> (adaptiveRouter .adaptive ((eraseSecretProto .erasing).withWriteOnce .nonErasing)
        κ ∅).runFrom
        (OracleComp.interpret
          (sumHandler
            (fun k => OracleComp.query (spec := probOracleSpec
              (adaptiveProtocolSpec 2 SecretIn Bool Unit Unit
                (WriteOnceView SecretIn Bool (Option Bool)))) (Sum.inl k))
            fun q => match q with
              | .inl p => ProbOracleComp.query (Sum.inl p)
              | .inr (.party i x) =>
                  projectWriteOnceNetR (eraseSecretProto .erasing).memory <$>
                    ProbOracleComp.query (Sum.inr (.party i x))
              | .inr (.corrupt _) => ProbOracleComp.sample (ProbComp.unifFin 0) >>=
                  fun _ => pure (.corrupt none)
              | .inr (.net nq) =>
                  projectWriteOnceNetR (eraseSecretProto .erasing).memory <$>
                    ProbOracleComp.query (Sum.inr (.net nq)))
          program) (eraseSecretInitRS .nonErasing)) =
      (Prod.fst <$> (adaptiveRouter .adaptive (eraseSecretProto .erasing) κ ∅).runFrom program
        { inner := fun _ => none, corrupted := ∅, trace := fun _ => [none] }) := by
  have h := runFrom_adaptiveRouter_withWriteOnce_noCorrupt .adaptive (eraseSecretProto .erasing)
    .nonErasing κ ∅ program
    (hno.mono fun q hq => by rcases q with _ | (⟨i, x⟩ | i | nq) <;> simp_all)
    (eraseSecretInitRS .nonErasing)
    { inner := fun _ => none, corrupted := ∅, trace := fun _ => [none] }
    ⟨rfl, rfl, fun _ => rfl⟩ (fun x => pure x.1) (fun x => pure x.1)
    (fun _ _ _ _ => rfl)
  rw [map_eq_pure_bind, map_eq_pure_bind]
  refine Eq.trans ?_ h
  congr 4
  funext q
  rcases q with _ | (⟨i, x⟩ | i | nq) <;> rfl

private def liftErasingReport (r : CorruptionReport (Option Bool)) :
    CorruptionReport (WriteOnceView EphIn Bool (Option Bool)) :=
  { current := { current := r.current, tape := none }, history := none }

private def liftErasingNetR :
    AdaptiveNetR Bool Unit (Option Bool) →
      AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool))
  | .party out => .party out
  | .corrupt rep => .corrupt (rep.map liftErasingReport)
  | .net r => .net r

private theorem router_ephemeralCoin_liftErasing {α β : Type} (κ : ℕ) (C₀ : Finset (Fin 2))
    (netProg : ProbOracleComp
      (netSpec (AdaptiveNetQ 2 EphIn Unit)
        (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool)))) α)
    (rs₁ : AdaptiveRouterState
      (WriteOnceState (Option Bool) EphIn Bool (Option Bool) 2)
      (WriteOnceView EphIn Bool (Option Bool)) 2)
    (rs₂ : AdaptiveRouterState (Option Bool) (Option Bool) 2)
    (hinner : rs₁.inner.inner = rs₂.inner) (hcor : rs₁.corrupted = rs₂.corrupted)
    (f : α × AdaptiveRouterState
      (WriteOnceState (Option Bool) EphIn Bool (Option Bool) 2)
      (WriteOnceView EphIn Bool (Option Bool)) 2 → ProbOracleComp OracleSpec.empty β)
    (g : α × AdaptiveRouterState (Option Bool) (Option Bool) 2 → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a rs₁' rs₂', rs₁'.inner.inner = rs₂'.inner → rs₁'.corrupted = rs₂'.corrupted →
      f (a, rs₁') = g (a, rs₂')) :
    ((adaptiveRouter .adaptive ((ephemeralCoin .erasing).withWriteOnce .erasing) κ C₀).runFrom
        (liftAdaptiveNet netProg) rs₁ >>= f) =
      ((adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ C₀).runFrom
        (liftAdaptiveNet (OracleComp.interpret
          (sumHandler
            (fun k => OracleComp.query (spec := probOracleSpec
              (netSpec (AdaptiveNetQ 2 EphIn Unit) (AdaptiveNetR Bool Unit (Option Bool))))
              (.inl k))
            fun nq => liftErasingNetR <$> ProbOracleComp.query
              (spec := netSpec (AdaptiveNetQ 2 EphIn Unit) (AdaptiveNetR Bool Unit (Option Bool)))
              nq)
          netProg)) rs₂ >>= g) := by
  dsimp only [liftAdaptiveNet, Machine.liftRightProgram]
  rw [OracleComp.interpret_interpret, OracleComp.interpret_sumHandler]
  let q₁ : (q : AdaptiveNetQ 2 EphIn Unit) →
      ProbOracleComp (adaptiveProtocolSpec 2 EphIn Bool Unit Unit
        (WriteOnceView EphIn Bool (Option Bool)))
        (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool))) := fun q =>
    ProbOracleComp.query (Sum.inr q)
  let q₂ : (q : AdaptiveNetQ 2 EphIn Unit) →
      ProbOracleComp (adaptiveProtocolSpec 2 EphIn Bool Unit Unit (Option Bool))
        (AdaptiveNetR Bool Unit (WriteOnceView EphIn Bool (Option Bool))) := fun q =>
    liftErasingNetR <$> ProbOracleComp.query (Sum.inr q)
  have hleft :
      (fun k : ℕ => OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query (spec := probOracleSpec
            (adaptiveProtocolSpec 2 EphIn Bool Unit Unit (Option Bool))) (Sum.inl k))
          fun q => ProbOracleComp.query
            (spec := adaptiveProtocolSpec 2 EphIn Bool Unit Unit (Option Bool)) (Sum.inr q))
        (OracleComp.query (spec := probOracleSpec
          (netSpec (AdaptiveNetQ 2 EphIn Unit) (AdaptiveNetR Bool Unit (Option Bool))))
          (Sum.inl k))) =
      fun k => OracleComp.query (Sum.inl k) :=
    funext fun k => (OracleComp.interpret_query _ (Sum.inl k)).trans rfl
  have hcomp :
      (fun q : AdaptiveNetQ 2 EphIn Unit => OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (.inl k)) fun q => ProbOracleComp.query (.inr q))
        (liftErasingNetR <$> ProbOracleComp.query q)) = q₂ :=
    funext fun q =>
      (OracleComp.interpret_map _ _ _).trans (congrArg _ (OracleComp.interpret_query _ _))
  erw [hleft, hcomp]
  refine (Machine.runFrom_interpret_intertwine
    (adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ C₀)
    (adaptiveRouter .adaptive ((ephemeralCoin .erasing).withWriteOnce .erasing) κ C₀)
    q₂ q₁ (fun _ => True)
    (fun s₂ s₁ => s₁.inner.inner = s₂.inner ∧ s₁.corrupted = s₂.corrupted)
    netProg (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    rs₂ rs₁ ⟨hinner, hcor⟩ g f (fun a s₂ s₁ hR => (hfg a s₁ s₂ hR.1 hR.2).symm)
    fun q rs₂' rs₁' k₂ k₁ _ ⟨hi_eq, hc_eq⟩ hcont => ?_).symm
  dsimp only [q₁, q₂]
  erw [Machine.runFrom_map, Machine.runFrom_query, Machine.runFrom_query, bind_map_left]
  dsimp only [adaptiveRouter, StateT.run]
  cases q with
  | party i x =>
    by_cases hi : i ∈ rs₁'.corrupted
    · have hi₂ : i ∈ rs₂'.corrupted := hc_eq ▸ hi
      simp only [hi, hi₂, ↓reduceIte]
      dsimp only [AdaptiveProtocol.withWriteOnce, ephemeralCoin, StateT.run]
      rw [hi_eq]
      have hrec : ((F_ephemeral.toAdaptive ephemeralReveal).machine κ).handle (.inl (i, x))
            rs₂'.inner =
          Prod.fst <$> recordCoins
            (((F_ephemeral.toAdaptive ephemeralReveal).machine κ).handle
              (.inl (i, x)) rs₂'.inner) :=
        (fst_map_recordCoins _).symm
      conv_rhs => erw [bind_assoc, bind_assoc]
      conv_lhs => rw [hrec]; erw [bind_map_left, bind_assoc]
      refine bind_congr fun ⟨⟨out, s'⟩, coins⟩ => ?_
      erw [pure_bind, pure_bind, pure_bind]
      exact hcont (.party out) _ _ ⟨rfl, hc_eq⟩
    · have hi₂ : i ∉ rs₂'.corrupted := hc_eq ▸ hi
      simp only [hi, hi₂, ↓reduceIte, pure_bind]
      exact hcont (.party none) rs₂' rs₁' ⟨hi_eq, hc_eq⟩
  | corrupt i =>
    simp only [pure_bind]
    by_cases hi : i ∈ rs₁'.corrupted
    · have hi₂ : i ∈ rs₂'.corrupted := hc_eq ▸ hi
      simp only [hi, hi₂, ↓reduceIte]
      dsimp only [Prod.map, id_eq]
      have hrep : AdaptiveNetR.corrupt (NetR := Unit) (some
            (((ephemeralCoin .erasing).withWriteOnce .erasing).corruptionReport κ i rs₁')) =
          liftErasingNetR (AdaptiveNetR.corrupt (NetR := Unit)
            (some ((F_ephemeral.toAdaptive ephemeralReveal).corruptionReport κ i rs₂'))) := by
        simp only [liftErasingNetR, liftErasingReport, Option.map_some,
          AdaptiveProtocol.corruptionReport, AdaptiveProtocol.withWriteOnce, ephemeralCoin,
          IdealFunctionality.toAdaptive, hi_eq]
        rfl
      erw [← hrep, pure_bind]
      exact hcont _ rs₂' rs₁' ⟨hi_eq, hc_eq⟩
    · have hi₂ : i ∉ rs₂'.corrupted := hc_eq ▸ hi
      simp only [hi, hi₂, ↓reduceIte]
      dsimp only [Prod.map, id_eq]
      have hrep : AdaptiveNetR.corrupt (NetR := Unit) (some
            (((ephemeralCoin .erasing).withWriteOnce .erasing).corruptionReport κ i
              { inner := ((ephemeralCoin .erasing).withWriteOnce .erasing).onCorrupt κ i
                  rs₁'.inner
                corrupted := insert i rs₁'.corrupted
                trace := rs₁'.trace })) =
          liftErasingNetR (AdaptiveNetR.corrupt (NetR := Unit)
            (some ((F_ephemeral.toAdaptive ephemeralReveal).corruptionReport κ i
              { inner := (F_ephemeral.toAdaptive ephemeralReveal).onCorrupt κ i rs₂'.inner
                corrupted := insert i rs₂'.corrupted
                trace := rs₂'.trace }))) := by
        simp only [liftErasingNetR, liftErasingReport, Option.map_some,
          AdaptiveProtocol.corruptionReport, AdaptiveProtocol.withWriteOnce, ephemeralCoin,
          IdealFunctionality.toAdaptive, hi_eq]
        rfl
      erw [← hrep, pure_bind]
      have hi_eq' : (((ephemeralCoin .erasing).withWriteOnce .erasing).onCorrupt κ i
            rs₁'.inner).inner =
          (F_ephemeral.toAdaptive ephemeralReveal).onCorrupt κ i rs₂'.inner := by
        simp [AdaptiveProtocol.withWriteOnce, ephemeralCoin, IdealFunctionality.toAdaptive, hi_eq]
      exact hcont _ _ _ ⟨hi_eq', congrArg (insert i) hc_eq⟩
  | net nq =>
    dsimp only [AdaptiveProtocol.withWriteOnce, ephemeralCoin, StateT.run]
    rw [hi_eq]
    conv_rhs => erw [bind_assoc, bind_assoc]
    conv_lhs => erw [bind_assoc]
    refine bind_congr fun ⟨r, s'⟩ => ?_
    erw [pure_bind, pure_bind]
    exact hcont (.net r) _ _ ⟨rfl, hc_eq⟩

private theorem exec_ephemeral_withWriteOnce_erasing_eq {AdvQ AdvR : Type}
    (A : AdaptiveAdversary 2 EphIn Bool Unit Unit
      (WriteOnceView EphIn Bool (Option Bool)) AdvQ AdvR)
    (Z : AdaptiveEnvironment 2 EphIn Bool AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec .adaptive ((ephemeralCoin .erasing).withWriteOnce .erasing) A Z κ z =
      adaptiveExec .adaptive (F_ephemeral.toAdaptive ephemeralReveal)
        (mapNetRAdversary liftErasingNetR A) Z κ z := by
  simp only [adaptiveExec, Machine.run, Machine.link]
  refine congrArg Machine.closeProgram ?_
  erw [Machine.sample_comp_init, Machine.sample_comp_init]
  have hPinit₁ : ProbOracleComp.sample (spec := OracleSpec.empty)
      ((adaptiveRouter .adaptive ((ephemeralCoin .erasing).withWriteOnce .erasing) κ
        (A.initial κ)).init) =
      pure { inner := { inner := none, initCoins := [], tapes := fun _ => [] }
             corrupted := A.initial κ
             trace := fun _ => [{ current := none, tape := none }] } := by
    have hfold1 : List.foldl (fun (acc : WriteOnceState (Option Bool) EphIn Bool (Option Bool) 2)
          (_ : Fin 2) => { inner := acc.inner, initCoins := acc.initCoins, tapes := acc.tapes })
        ({ inner := none, initCoins := [], tapes := fun _ => [] } :
          WriteOnceState (Option Bool) EphIn Bool (Option Bool) 2) (List.finRange 2) =
        { inner := none, initCoins := [], tapes := fun _ => [] } := rfl
    dsimp only [adaptiveRouter, AdaptiveProtocol.withWriteOnce, ephemeralCoin,
      IdealFunctionality.toAdaptive, F_ephemeral, AdaptiveProtocol.applyInitialCorruptions,
      ephemeralReveal, recordProbCoins, recordProbCoinsFrom]
    have hne : PartyMemory.erasing ≠ .nonErasing := by decide
    simp only [OracleComp.interpret_pure, StateT.run_pure, ProbOracleComp.sample_pure,
      pure_bind, hfold1, ite_self, hne, ↓reduceIte]
  have hPinit₂ : ProbOracleComp.sample (spec := OracleSpec.empty)
      ((adaptiveRouter .adaptive (F_ephemeral.toAdaptive ephemeralReveal) κ
        (A.initial κ)).init) =
      pure { inner := none, corrupted := A.initial κ, trace := fun _ => [none] } := by
    have hfold2 : List.foldl (fun acc (_ : Fin 2) => acc) (none : Option Bool)
        (List.finRange 2) = none := rfl
    dsimp only [adaptiveRouter, F_ephemeral, IdealFunctionality.toAdaptive,
      AdaptiveProtocol.applyInitialCorruptions, ephemeralReveal]
    simp only [ite_self, hfold2, ProbOracleComp.sample_pure, pure_bind]
  dsimp only [mapNetRAdversary] at hPinit₂ ⊢
  erw [hPinit₁, hPinit₂, pure_bind, pure_bind, bind_assoc, bind_assoc]
  refine bind_congr fun sA => ?_
  erw [pure_bind, pure_bind, map_eq_pure_bind, map_eq_pure_bind]
  refine Machine.runFrom_intertwine
    (adaptiveExecMachine .adaptive ((ephemeralCoin .erasing).withWriteOnce .erasing) A κ)
    (adaptiveExecMachine .adaptive (F_ephemeral.toAdaptive ephemeralReveal)
      (mapNetRAdversary liftErasingNetR A) κ)
    (fun _ => True)
    (fun x₁ x₂ => x₁.1 = x₂.1 ∧ x₁.2.inner.inner = x₂.2.inner ∧ x₁.2.corrupted = x₂.2.corrupted)
    (Z κ z) (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    (sA, _) (sA, _) ⟨rfl, rfl, rfl⟩ (fun x => pure x.1) (fun x => pure x.1)
    (fun _ _ _ _ => rfl) fun q ⟨sA₁, rs₁'⟩ ⟨sA₂, rs₂'⟩ k₁ k₂ _ ⟨hsA, hi, hc⟩ hcont => ?_
  dsimp only [adaptiveExecMachine, Machine.comp, liftAdaptiveAdversary, Machine.liftRight]
    at sA₁ rs₁' sA₂ rs₂' hsA
  subst hsA
  rcases q with (⟨i, x⟩ | _) | a
  · erw [adaptiveExecMachine_handle_inl_party, adaptiveExecMachine_handle_inl_party]
    by_cases hi_mem : i ∈ rs₁'.corrupted
    · have hi₂ : i ∈ rs₂'.corrupted := hc ▸ hi_mem
      simp only [hi_mem, hi₂, ↓reduceIte]
      erw [pure_bind, pure_bind]
      exact hcont none _ _ ⟨rfl, hi, hc⟩
    · have hi₂ : i ∉ rs₂'.corrupted := hc ▸ hi_mem
      simp only [hi_mem, hi₂, ↓reduceIte]
      dsimp only [AdaptiveProtocol.withWriteOnce, ephemeralCoin, StateT.run]
      rw [hi]
      have hrec : ((F_ephemeral.toAdaptive ephemeralReveal).machine κ).handle (.inl (i, x))
            rs₂'.inner =
          Prod.fst <$> recordCoins
            (((F_ephemeral.toAdaptive ephemeralReveal).machine κ).handle
              (.inl (i, x)) rs₂'.inner) :=
        (fst_map_recordCoins _).symm
      conv_lhs => erw [bind_assoc, bind_assoc]
      conv_rhs => rw [hrec]; erw [bind_map_left, bind_assoc]
      refine bind_congr fun ⟨⟨out, s'⟩, coins⟩ => ?_
      erw [pure_bind, pure_bind, pure_bind]
      exact hcont out _ _ ⟨rfl, rfl, hc⟩
  · erw [adaptiveExecMachine_handle_inl_status, adaptiveExecMachine_handle_inl_status,
      pure_bind, pure_bind]
    rw [hc]
    exact hcont rs₂'.corrupted _ _ ⟨rfl, hi, hc⟩
  · change (Equiv.prodAssoc _ _ _ <$> (adaptiveRouter .adaptive
        ((ephemeralCoin .erasing).withWriteOnce .erasing) κ (A.initial κ)).runFrom
        (liftAdaptiveNet (((A.machine κ).handle a).run sA₁)) rs₁' >>= k₁) =
      Equiv.prodAssoc _ _ _ <$> (adaptiveRouter .adaptive
        (F_ephemeral.toAdaptive ephemeralReveal) κ (A.initial κ)).runFrom
        (liftAdaptiveNet (((mapNetRAdversary liftErasingNetR A).machine κ).handle a |>.run
          sA₁)) rs₂' >>= k₂
    erw [bind_map_left, bind_map_left]
    exact router_ephemeralCoin_liftErasing κ (A.initial κ) (((A.machine κ).handle a).run sA₁)
      rs₁' rs₂' hi hc _ _
      fun ⟨r, sA'⟩ rs₁'' rs₂'' hi' hc' => hcont r (sA', rs₁'') (sA', rs₂'') ⟨rfl, hi', hc'⟩

theorem ephemeralCoin_writeOnce_erasing_emulates :
    AdaptiveEmulates .adaptive ((ephemeralCoin .erasing).withWriteOnce .erasing)
      (F_ephemeral.toAdaptive ephemeralReveal) := by
  intro AdvQ AdvR A pA hA
  refine ⟨mapNetRAdversary liftErasingNetR A, pA, hA.mapNetR _,
    fun _ => ⟨0, negligible_zero, fun Z _ κ z => ?_⟩⟩
  rw [adaptiveAdvantage, exec_ephemeral_withWriteOnce_erasing_eq A Z κ z, Game.advantage_self]
  simp

theorem ephemeralCoin_of_writeOnce_instantiation
    (h : AdaptiveEmulates .adaptive ((ephemeralCoin .erasing).withWriteOnce .nonErasing)
      (F_ephemeral.toAdaptive ephemeralReveal)) :
    AdaptiveEmulates .adaptive (ephemeralCoin .erasing)
      (F_ephemeral.toAdaptive ephemeralReveal) ∧
      AdaptiveEmulates .adaptive ((ephemeralCoin .erasing).withWriteOnce .erasing)
        (F_ephemeral.toAdaptive ephemeralReveal) :=
  ⟨AdaptiveEmulates.of_writeOnce h, AdaptiveEmulates.erasing_of_writeOnce h⟩

end CslibFrontierTests.Crypto.UCAdaptiveStorage
