/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.MultiSession
import CslibFrontier.Languages.Probabilistic.Oracle.Vector
import CslibFrontier.Languages.Probabilistic.RandomOracle

/-!
# Lazy multi-session ideal functionality and parallel-package bridge

This module defines the named data structures and lazy multi-session ideal functionality
`IdealFunctionality.multiSession` (`F̂`), together with the lazy parallel package runner
`parFinLazy` and its distributional equivalence `run_parFinLazy_eq_parFin` with `SSP.parFin`.

This provides the lazy multi-session ideal functionality and initialization bridge needed for
joint-state UC composition ([CanettiRabin2003], CRYPTO 2003, LNCS 2729, p. 273; locators follow
the proceedings version; ePrint 2002/047 was not inspected), adapted to static corruptions and
this library's call-bounded, pull-only UC execution model (see `Cslib.Crypto.Protocols.UC.Emulates`
for the call-budget model vs. PPT ITMs).

## Modelling decisions and relation to [CanettiRabin2003]

1. **Named structures (zero projection chains).** `SubSessionInput`, `SubSessionBackdoor`, and
   `MultiSessionState` replace raw nested products/options.
2. **Lazy multi-session extension `F.multiSession`.** For any `[DecidableEq SSID]`,
   `IdealFunctionality.multiSession SSID F` stores `(secParam, corrupted, sessions)` and creates a
   fresh copy of `F` with `F.init secParam corrupted` on the first party input or backdoor query
   for a given `ssid`, keeping distinct `ssid`s independent ([CanettiRabin2003], p. 273).
3. **Pull-model deviation (stronger ideal).** On p. 273 of [CanettiRabin2003], `F̂` sends `ssid` to
   the adversary whenever a copy outputs to a party ("Sending ssid to the adversary implies
   that F̂ does not hide which copy of F is being activated within F̂."). In the pull execution
   here, neither `F` nor `IdealFunctionality.multiSession` notifies the adversary; party outputs
   wait until polled, so `IdealFunctionality.multiSession` hides which copy honest parties activate
   and reveals an `ssid` only on copies the adversary queries itself on the backdoor. Consequently,
   `IdealFunctionality.multiSession` is a *stronger* ideal functionality, making
   `Realizes ρ̂ (F.multiSession (Fin m))` at least as demanding as the source premise (the safe
   direction: weaker theorem, no overclaim; a realistic `ρ̂` that leaks `ssid` on the network may
   fail to realize the pull `F̂`).
4. **Lazy-vs-eager equivalence via `RandomOracle`.** `run_parFinLazy_eq_parFin` derives equality
   of lazy first-touch initialization and eager `SSP.parFin` sampling from
   `RandomOracle.pi_bind_eq_map_fst_of_complete_eq` by restricting each `ProbComp` initializer to
   its finite support and separating the once-sampled initial state table from mutable per-session
   state.
5. **Scope and joint state vs. global setup.** Joint state here is internal to a single subroutine
   protocol, not a GUC/EUC global setup shared outside it.

## Main definitions

* `Cslib.Crypto.Protocols.UC.SubSessionInput`, `Cslib.Crypto.Protocols.UC.SubSessionBackdoor`,
  `Cslib.Crypto.Protocols.UC.MultiSessionState`: named data structures for multi-session
  functionalities.
* `Cslib.Crypto.Protocols.UC.IdealFunctionality.multiSession`: lazy multi-session extension `F̂`.
* `Cslib.Crypto.Protocols.UC.parFinLazy`: lazy first-touch parallel package runner.

## Main results

* `Cslib.Crypto.Protocols.UC.run_parFinLazy_eq_parFin`: lazy first-touch initialization agrees
  in distribution with eager `SSP.parFin` initialization.

## References

* [R. Canetti and T. Rabin, *Universal Composition with Joint State*][CanettiRabin2003], CRYPTO
  2003, LNCS 2729, pp. 265–281 (`F̂`, p. 273).
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open scoped NNReal

/-! ### Named structures and lazy multi-session functionality -/

/-- A party input to a multi-session functionality or joint-state protocol: sub-session `ssid`
with value `input` ([CanettiRabin2003], p. 273, the `(ssid, v)` part of `(sid, ssid, v)`). -/
structure SubSessionInput (SSID SubIn : Type) : Type where
  /-- Sub-session identifier. -/
  ssid : SSID
  /-- Party input (or poll token) for sub-session `ssid`. -/
  input : SubIn
  deriving DecidableEq

/-- An adversary backdoor query to copy `ssid` of the multi-session functionality. -/
structure SubSessionBackdoor (SSID BackQ : Type) : Type where
  /-- Target sub-session identifier. -/
  ssid : SSID
  /-- Backdoor query for sub-session `ssid`. -/
  query : BackQ
  deriving DecidableEq

/-- State of `F.multiSession`: the security parameter and corrupted set recorded at invocation
(so that copies can be created later) and the lazily created copies. -/
structure MultiSessionState (n : ℕ) (SSID FState : Type) : Type where
  /-- Security parameter fixed at functionality invocation. -/
  secParam : ℕ
  /-- Static corruption set fixed at functionality invocation. -/
  corrupted : Finset (Fin n)
  /-- Lazily initialized per-session states (`none` until first message). -/
  sessions : SSID → Option FState

/-- Multi-session extension `F̂` of an ideal functionality `F` for any `[DecidableEq SSID]`:
creates a fresh copy of `F` with `F.init secParam corrupted` on the first party input or backdoor
query for `ssid`, and activates that copy ([CanettiRabin2003], p. 273). In this pull-only model,
`IdealFunctionality.multiSession` does not notify the adversary on honest-party activations, making
it a stronger ideal functionality than the source's `F̂`. -/
@[expose] def IdealFunctionality.multiSession {n : ℕ} {SubIn SubOut BackQ BackR : Type}
    (SSID : Type) [DecidableEq SSID]
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) :
    IdealFunctionality n (SubSessionInput SSID SubIn) SubOut
      (SubSessionBackdoor SSID BackQ) BackR where
  State := MultiSessionState n SSID F.State
  init κ C := pure { secParam := κ, corrupted := C, sessions := fun _ => none }
  onInput i req s := do
    let fState ← match s.sessions req.ssid with
      | some st => pure st
      | none => F.init s.secParam s.corrupted
    let (out, fState') ← (F.onInput i req.input).run fState
    return (out, { s with sessions := Function.update s.sessions req.ssid (some fState') })
  onBackdoor req s := do
    let fState ← match s.sessions req.ssid with
      | some st => pure st
      | none => F.init s.secParam s.corrupted
    let (resp, fState') ← (F.onBackdoor req.query).run fState
    return (resp, { s with sessions := Function.update s.sessions req.ssid (some fState') })

/-! ### Lazy-vs-eager parallel package equivalence -/

/-- Lazy variant of `SSP.parFin`: initializes each session `j : Fin m` on first query to `j` via
`(M j).init` rather than sampling all `m` initial states upfront. -/
@[expose] def parFinLazy {m : ℕ} {ιE : Type} {E : ιE → Type}
    (M : Fin m → Machine OracleSpec.empty E) :
    Machine OracleSpec.empty (SSP.sessionSpec m E) where
  State := (j : Fin m) → Option (M j).State
  init := pure fun _ => none
  handle
    | (j, q) => fun s => do
        let st ← match s j with
          | some st => pure st
          | none => ProbOracleComp.sample (M j).init
        let (r, st') ← ((M j).handle q).run st
        return (r, Function.update s j (some st'))

section LazyBridge

open Probability

private theorem support_finite_probComp {α : Type} (p : ProbComp α) : p.support.Finite := by
  induction p using OracleComp.induction with
  | pure a => simp [OracleComp.support]
  | query_bind k cont ih =>
    rw [OracleComp.support, OracleComp.supportWith_freeMBind, OracleComp.supportWith_query]
    simpa only [Set.biUnion_univ] using Set.finite_iUnion ih

private def EvalSupport {α : Type} (p : ProbComp α) : Type :=
  { a : α // a ∈ p.eval.support }

private instance {α : Type} (p : ProbComp α) : Finite (EvalSupport p) :=
  (ProbComp.support_eval p ▸ support_finite_probComp p).to_subtype

private noncomputable def evalSupportPMF {α : Type} (p : ProbComp α) : PMF (EvalSupport p) :=
  ⟨fun x => p.eval x.1, by
    have hind : Set.indicator p.eval.support (fun a => p.eval a) = fun a => p.eval a := by
      funext a
      by_cases ha : a ∈ p.eval.support
      · simp [Set.indicator_of_mem ha]
      · simp only [Set.indicator_of_notMem ha]
        rw [PMF.mem_support_iff, not_not] at ha
        exact ha.symm
    exact hasSum_subtype_iff_indicator.mpr (hind ▸ p.eval.2)⟩

private theorem evalSupportPMF_map_val {α : Type} (p : ProbComp α) :
    (evalSupportPMF p).map Subtype.val = p.eval := by
  ext a
  erw [PMF.map_apply]
  by_cases ha : a ∈ p.eval.support
  · rw [tsum_eq_single ⟨a, ha⟩]
    · simp only [evalSupportPMF, ↓reduceIte]
      rfl
    · intro x hx
      rw [ite_eq_right]
      intro hval
      exact hx (Subtype.ext hval.symm)
  · have hzero : p.eval a = 0 := by simpa [PMF.mem_support_iff] using ha
    simp only [evalSupportPMF]
    erw [hzero]
    rw [tsum_eq_zero_iff.mpr]
    intro x
    rw [ite_eq_right]
    intro hval
    exact absurd (hval ▸ x.2) ha

/-- Variant of `ProbComp.eval_pi` without `[∀ j, Finite (α j)]`: restricts each `p j` to its
finite support subtype `EvalSupport (p j)` so `Probability.PMF.pi` applies to arbitrary state
types `α j`. Uses `Probability.PMF.pi_fin_succ_dep` in the step case. -/
private theorem eval_pi_eq_pi_evalSupportPMF :
    ∀ {m : ℕ} {α : Fin m → Type} (p : (j : Fin m) → ProbComp (α j)),
      ProbComp.eval (OracleComp.pi p) =
        (Probability.PMF.pi fun j => evalSupportPMF (p j)).map (fun t j => (t j).1)
  | 0, α, p => by
    ext r
    have hr : r = fun j => j.elim0 := funext fun j => j.elim0
    subst hr
    simp only [OracleComp.pi_zero, ProbComp.eval_pure, PMF.map_apply, Probability.PMF.pi_apply,
      Fin.prod_univ_zero]
    rw [tsum_eq_single (fun j => Fin.elim0 j)]
    · simp only [PMF.pure_apply, ↓reduceIte]
      split_ifs with h
      · rfl
      · exact absurd (funext fun j => j.elim0) h
    · intro b hb
      exact absurd (funext fun j => Fin.elim0 j) hb
  | m + 1, α, p => by
    rw [Probability.PMF.pi_fin_succ_dep, PMF.map_bind, OracleComp.pi_succ, ProbComp.eval_bind]
    simp_rw [ProbComp.eval_map, eval_pi_eq_pi_evalSupportPMF (fun j => p j.succ)]
    rw [← evalSupportPMF_map_val (p 0)]
    erw [PMF.bind_map]
    refine congrArg (evalSupportPMF (p 0)).bind (funext fun x₀ => ?_)
    simp only [Function.comp_def, PMF.map_comp]
    congr 1 with rest : 1
    funext j
    cases j using Fin.cases <;> rfl

/-- Lazy first-touch initialization agrees in distribution with eager `SSP.parFin` initialization
for any adaptive client `program`, via `RandomOracle.pi_bind_eq_map_fst_of_complete_eq`. -/
theorem run_parFinLazy_eq_parFin {m : ℕ} {ιE : Type} {E : ιE → Type} {α : Type}
    (M : Fin m → Machine OracleSpec.empty E) (program : ProbOracleComp (SSP.sessionSpec m E) α) :
    ((parFinLazy M).run program).eval = ((SSP.parFin M).run program).eval := by
  let InitSup := fun j : Fin m => EvalSupport (M j).init
  let initPMF : ∀ j : Fin m, PMF (InitSup j) := fun j => evalSupportPMF (M j).init
  let StateL := ((j : Fin m) → Option (M j).State) × RandomOracle.Cache InitSup
  let StateE := ((j : Fin m) → (M j).State) × ((j : Fin m) → InitSup j)
  let InvL : StateL → Prop := fun s => ∀ j, (s.1 j).isSome ↔ (s.2 j).isSome
  let oracleL : (q : ℕ ⊕ (Fin m × ιE)) →
      StateT StateL PMF (probOracleSpec (SSP.sessionSpec m E) q)
    | .inl k, s => (ProbComp.unifFin k).eval.map (·, s)
    | .inr (j, e), (cur, cache) =>
      match cur j, cache j with
      | some st, some _ =>
          ((Machine.closeProgram (((M j).handle e).run st)).eval).map fun (r, st') =>
            (r, (Function.update cur j (some st'), cache))
      | _, _ =>
          (initPMF j).bind fun x₀ =>
            ((Machine.closeProgram (((M j).handle e).run x₀.1)).eval).map fun (r, st') =>
              (r, (Function.update cur j (some st'), Function.update cache j (some x₀)))
  let oracleE : (q : ℕ ⊕ (Fin m × ιE)) →
      StateT StateE PMF (probOracleSpec (SSP.sessionSpec m E) q)
    | .inl k, s => (ProbComp.unifFin k).eval.map (·, s)
    | .inr (j, e), (curE, table) =>
        ((Machine.closeProgram (((M j).handle e).run (curE j))).eval).map fun (r, st') =>
          (r, (Function.update curE j st', table))
  let oracleEClean : (q : ℕ ⊕ (Fin m × ιE)) →
      StateT ((j : Fin m) → (M j).State) PMF (probOracleSpec (SSP.sessionSpec m E) q) :=
    fun q s => (Machine.closeProgram ((SSP.parFin M).handler q s)).eval
  let oracleLClean : (q : ℕ ⊕ (Fin m × ιE)) →
      StateT ((j : Fin m) → Option (M j).State) PMF (probOracleSpec (SSP.sessionSpec m E) q) :=
    fun q s => (Machine.closeProgram ((parFinLazy M).handler q s)).eval
  let relate : StateL → PMF StateE := fun (cur, cache) =>
    (RandomOracle.complete initPMF cache).map fun table =>
      (fun j => (cur j).getD (table j).1, table)
  have hInv : ∀ q (s : StateL), InvL s →
      ∀ a (s' : StateL), (a, s') ∈ (oracleL q s).support → InvL s' := by
    rintro (k | ⟨j, e⟩) ⟨cur, cache⟩ hs a ⟨cur', cache'⟩ hmem
    · simp only [oracleL, PMF.mem_support_map_iff] at hmem
      rcases hmem with ⟨_, _, heq⟩
      cases heq
      exact hs
    · cases hcur : cur j with
      | some st =>
        have hcache : (cache j).isSome := (hs j).mp (by simp [hcur])
        obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.mp hcache
        simp only [oracleL, hcur, hx₀, PMF.mem_support_map_iff] at hmem
        rcases hmem with ⟨⟨r, st'⟩, _, heq⟩
        cases heq
        intro i
        by_cases hi : i = j
        · subst hi; simp [hx₀]
        · simpa [Function.update_of_ne hi] using hs i
      | none =>
        have hcache : cache j = none :=
          Option.not_isSome_iff_eq_none.mp fun h => by
            have := (hs j).mpr h
            simp [hcur] at this
        simp only [oracleL, hcur, hcache, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
        rcases hmem with ⟨x₀, _, ⟨r, st'⟩, _, heq⟩
        cases heq
        intro i
        by_cases hi : i = j
        · subst hi; simp
        · simpa [Function.update_of_ne hi] using hs i
  have hStep : ∀ q (s : StateL), InvL s →
      (oracleL q s).bind (fun (a, s') => (relate s').map (a, ·)) =
        (relate s).bind (oracleE q) := by
    rintro (k | ⟨j, e⟩) ⟨cur, cache⟩ hs
    · simp only [oracleL, oracleE, relate, PMF.bind_map, PMF.map_comp, Function.comp_def]
      simp_rw [← PMF.bind_pure_comp]
      exact PMF.bind_comm _ _ _
    · cases hcur : cur j with
      | some st =>
        have hcache : (cache j).isSome := (hs j).mp (by simp [hcur])
        obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.mp hcache
        simp only [oracleL, oracleE, relate, hcur, hx₀, Option.getD_some, PMF.bind_map,
          PMF.map_comp, Function.comp_def]
        simp_rw [← PMF.bind_pure_comp]
        rw [PMF.bind_comm]
        refine congrArg (RandomOracle.complete initPMF cache).bind (funext fun table => ?_)
        refine congrArg _ (funext fun ⟨r, st'⟩ => ?_)
        refine congrArg (PMF.pure ·) (Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl))
        by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      | none =>
        have hcache : cache j = none :=
          Option.not_isSome_iff_eq_none.mp fun h => by
            have := (hs j).mpr h
            simp [hcur] at this
        simp only [oracleL, oracleE, relate, hcur, hcache, PMF.bind_bind, PMF.bind_map,
          PMF.map_comp, Function.comp_def]
        have hcomm (x₀ : InitSup j) :
            ((Machine.closeProgram (((M j).handle e).run x₀.1)).eval.bind fun p =>
              (RandomOracle.complete initPMF (Function.update cache j (some x₀))).map fun table =>
                (p.1, (fun i => (Function.update cur j (some p.2) i).getD (table i).1, table))) =
            (RandomOracle.complete initPMF (Function.update cache j (some x₀))).bind fun table =>
              (Machine.closeProgram (((M j).handle e).run x₀.1)).eval.map fun p =>
                (p.1, (Function.update (fun i => (cur i).getD (table i).1) j p.2, table)) := by
          simp_rw [← PMF.bind_pure_comp]
          rw [PMF.bind_comm]
          refine congrArg _ (funext fun table => congrArg _ (funext fun ⟨r, st'⟩ => ?_))
          refine congrArg PMF.pure (Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl))
          by_cases hi : i = j
          · subst hi; simp
          · simp [Function.update_of_ne hi]
        refine (congrArg (initPMF j).bind (funext fun x₀ => hcomm x₀)).trans ?_
        have hpair :
            ((initPMF j).bind fun x₀ =>
              (RandomOracle.complete initPMF (Function.update cache j (some x₀))).bind fun table =>
                (Machine.closeProgram (((M j).handle e).run x₀.1)).eval.map fun p =>
                  (p.1, (Function.update (fun i => (cur i).getD (table i).1) j p.2, table))) =
            ((initPMF j).bind fun x₀ =>
              (RandomOracle.complete initPMF (Function.update cache j (some x₀))).map
                (x₀, ·)).bind fun p =>
              (Machine.closeProgram (((M j).handle e).run p.1.1)).eval.map fun q =>
                (q.1, (Function.update (fun i => (cur i).getD (p.2 i).1) j q.2, p.2)) := by
          simp only [PMF.bind_bind]
          refine congrArg (initPMF j).bind (funext fun x₀ => ?_)
          erw [PMF.bind_map]
          rfl
        rw [hpair]
        have hans := RandomOracle.answer_complete initPMF cache j
        rw [RandomOracle.answer_of_none initPMF cache j hcache] at hans
        simp only [PMF.monad_bind_eq_bind] at hans
        erw [PMF.bind_map] at hans
        simp only [Function.comp_def] at hans
        rw [hans]
        erw [PMF.bind_map]
        refine congrArg (RandomOracle.complete initPMF cache).bind (funext fun table => ?_)
        simp only [Option.getD_none, Function.comp_def]
  have hSim := OracleComp.run_interpret_simulation_of_invariant oracleL oracleE relate InvL
    hInv hStep program (fun _ => none, fun _ => none) (fun _ => by simp)
  have hComplete :
      (((OracleComp.interpret oracleL program).run (fun _ => none, fun _ => none)).map
          (fun x => (x.1, x.2.2))).bind (fun (result, cache') =>
            (RandomOracle.complete initPMF cache').map (result, ·)) =
        (RandomOracle.complete initPMF (fun _ => none)).bind fun table =>
          (((OracleComp.interpret oracleEClean program).run (fun j => (table j).1)).map
            Prod.fst).map (·, table) := by
    have hproj := congrArg (PMF.map fun x : α × StateE => (x.1, x.2.2)) hSim
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hproj
    have hL :
        (((OracleComp.interpret oracleL program).run (fun _ => none, fun _ => none)).bind
            fun x => (relate x.2).map fun y => (x.1, y.2)) =
          (((OracleComp.interpret oracleL program).run (fun _ => none, fun _ => none)).map
              (fun x => (x.1, x.2.2))).bind fun (result, cache') =>
            (RandomOracle.complete initPMF cache').map (result, ·) := by
      rw [PMF.bind_map]
      refine congrArg _ (funext fun ⟨a, ⟨cur', cache'⟩⟩ => ?_)
      simp [relate, PMF.map_comp, Function.comp_def]
    have hEclean : ∀ (table : ∀ j, InitSup j) (curE : ∀ j, (M j).State),
        ((OracleComp.interpret oracleE program).run (curE, table)).map (fun x => (x.1, x.2.2)) =
          (((OracleComp.interpret oracleEClean program).run curE).map Prod.fst).map (·, table) := by
      intro table curE
      have hmap := OracleComp.run_interpret_map_state oracleE oracleEClean Prod.fst
        (by
          rintro (k | ⟨j, e⟩) ⟨curE', t'⟩
          · simp [oracleE, oracleEClean, SSP.parFin, Machine.handler, StateT.lift,
              Machine.closeProgram_sample, Machine.closeProgram_map, ProbComp.eval_map,
              PMF.map_comp, Function.comp_def]
          · simp only [oracleE, oracleEClean, SSP.parFin, Machine.handler,
              Machine.closeProgram_map, ProbComp.eval_map, PMF.map_comp]
            congr 1 with ⟨r, st'⟩ : 1) program (curE, table)
      have hconst : ∀ x ∈ ((OracleComp.interpret oracleE program).run (curE, table)).support,
          x.2.2 = table := by
        intro x hx
        exact OracleComp.run_interpret_invariant oracleE (fun s => s.2 = table)
          (by
            rintro (k | ⟨j, e⟩) ⟨c, t⟩ ht a ⟨c', t'⟩ hmem
            · simp only [oracleE, PMF.mem_support_map_iff] at hmem
              rcases hmem with ⟨_, _, heq⟩
              cases heq; exact ht
            · simp only [oracleE, PMF.mem_support_map_iff] at hmem
              rcases hmem with ⟨⟨r, st'⟩, _, heq⟩
              cases heq; exact ht)
          program (curE, table) rfl x.1 x.2 hx
      calc
        ((OracleComp.interpret oracleE program).run (curE, table)).map (fun x => (x.1, x.2.2))
            = ((OracleComp.interpret oracleE program).run (curE, table)).map
                (fun x => (x.1, table)) := by
              refine Probability.PMF.map_congr_on_support _ _ _ fun x hx => ?_
              rw [hconst x hx]
        _ = (((OracleComp.interpret oracleE program).run (curE, table)).map
              (fun (a, s') => (a, s'.1))).map (fun x => (x.1, table)) := by
              simp [PMF.map_comp, Function.comp_def]
        _ = _ := by
              rw [hmap, PMF.map_comp]
              simp [Function.comp_def]
    rw [← hL, hproj]
    simp only [relate, PMF.bind_map, Function.comp_def]
    refine congrArg _ (funext fun table => ?_)
    exact hEclean table (fun j => (table j).1)
  have hPi := RandomOracle.pi_bind_eq_map_fst_of_complete_eq initPMF hComplete
  have hLazyClean :
      (((OracleComp.interpret oracleL program).run (fun _ => none, fun _ => none)).map
          (fun x => (x.1, x.2.2))).map Prod.fst =
        ((OracleComp.interpret oracleLClean program).run (fun _ => none)).map Prod.fst := by
    have hmap := OracleComp.run_interpret_map_state_of_invariant oracleL oracleLClean Prod.fst
      InvL hInv (by
        rintro (k | ⟨j, e⟩) ⟨cur, cache⟩ hs
        · simp [oracleL, oracleLClean, parFinLazy, Machine.handler, StateT.lift,
            Machine.closeProgram_sample, Machine.closeProgram_map, ProbComp.eval_map,
            PMF.map_comp, Function.comp_def]
        · cases hcur : cur j with
          | some st =>
            have hcache : (cache j).isSome := (hs j).mp (by simp [hcur])
            obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.mp hcache
            simp only [oracleL, oracleLClean, parFinLazy, Machine.handler, sumHandler, hcur, hx₀,
              StateT.run, pure_bind, Machine.closeProgram_bind, Machine.closeProgram_pure,
              ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
              Function.comp_def, ← PMF.bind_pure_comp]
          | none =>
            have hcache : cache j = none :=
              Option.not_isSome_iff_eq_none.mp fun h => by
                have := (hs j).mpr h
                simp [hcur] at this
            simp only [oracleL, oracleLClean, parFinLazy, Machine.handler, sumHandler, hcur, hcache,
              StateT.run, Machine.closeProgram_bind, Machine.closeProgram_sample,
              Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_pure]
            conv_rhs => rw [← evalSupportPMF_map_val (M j).init]
            erw [PMF.bind_map]
            simp only [PMF.bind_bind, PMF.pure_bind, Function.comp_def, ← PMF.bind_pure_comp]
            rfl)
      program (fun _ => none, fun _ => none) (fun _ => by simp)
    have hfst := congrArg (PMF.map Prod.fst) hmap
    simpa [PMF.map_comp, Function.comp_def] using hfst
  have hParFin : ((SSP.parFin M).run program).eval =
      (Probability.PMF.pi initPMF).bind fun table =>
        ((OracleComp.interpret oracleEClean program).run (fun j => (table j).1)).map Prod.fst := by
    rw [SSP.eval_run (SSP.parFin M) program]
    change (ProbComp.eval (OracleComp.pi fun j => (M j).init)).bind _ = _
    rw [eval_pi_eq_pi_evalSupportPMF]
    erw [PMF.bind_map]
    rfl
  have hParFinLazy : ((parFinLazy M).run program).eval =
      ((OracleComp.interpret oracleLClean program).run (fun _ => none)).map Prod.fst := by
    rw [SSP.eval_run (parFinLazy M) program]
    simp only [parFinLazy, ProbComp.eval_pure, PMF.pure_bind, oracleLClean]
    rfl
  rw [hParFinLazy, hParFin]
  simp only [PMF.monad_bind_eq_bind] at hPi
  rw [hPi]
  exact hLazyClean.symm

end LazyBridge

end Cslib.Crypto.Protocols.UC
