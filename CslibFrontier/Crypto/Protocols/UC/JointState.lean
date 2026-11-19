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
# Universal composition with joint state (step theorems and lazy multi-session functionality)

This module defines the lazy multi-session extension `IdealFunctionality.multiSession`, the lazy
parallel-session equivalence `run_parFinLazy_eq_parFin`, the sub-session relabelling
`MultiHybridProtocol.toJoint`, the explicit demultiplexing and multiplexing adversaries `jointDemux`
and `jointMux`, and the fixed-session step theorems `EmulatesWithin.toJoint_multiSession` and
`EmulatesWithin.multiSession_toJoint` for this library's call-bounded, static-corruption port-model
emulation notions (`UC.EmulatesWithin`, `UC.Emulates`, `UC.Realizes`).

These form the second half of the proof of Theorem 1 of [CanettiRabin2003] (CRYPTO 2003, LNCS 2729,
pp. 273–274; locators follow the proceedings version; ePrint 2002/047 was not inspected), adapted
to a fixed finite session count `m`, static corruptions, pull-only execution, and this library's
call-bounded statistical model (see `Cslib.Crypto.Protocols.UC.Emulates` for the call-budget
model vs. PPT ITMs).

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
   here, neither `F` nor `F.multiSession` notifies the adversary; party outputs wait until polled,
   so `F.multiSession` hides which copy honest parties activate and reveals an `ssid` only on
   copies the adversary queries itself on the backdoor. Consequently, `F.multiSession` is a
   *stronger* ideal functionality, making `Realizes ρ̂ (F.multiSession (Fin m))` at least as
   demanding as the source premise (the safe direction: weaker theorem, no overclaim; a realistic
   `ρ̂` that leaks `ssid` on the network may fail to realize the pull `F̂`).
4. **Sub-session relabelling `toJoint` and fixed `m`.** `MultiHybridProtocol.toJoint ρ` relabels
   each `SubSessionCall` `⟨session, party, input⟩` as `(party, ⟨session, input⟩)` (adapting `π̃`
   on p. 274 of [CanettiRabin2003] to a fixed finite `Fin m` family; dynamic `SID` creation and
   push-model `ssid` notifications are out of scope).
5. **Explicit demux/mux adversaries under static corruption.** `jointDemux` and `jointMux`
   translate network queries between the single-protocol `F̂`-hybrid interface and the `m`-session
   `composeMulti` interface while preserving replies (`NetR ⊕ RoutedNetR SubOut BackR`). Static
   corruptions `C : Finset (Fin n)` are shared across `ρ`, all copies of `F`, and `ρ̂`, so
   corrupted-party internal state translation ([CanettiRabin2003], p. 274, item 3) is unneeded.
6. **Lazy-vs-eager equivalence via `RandomOracle`.** `run_parFinLazy_eq_parFin` derives equality
   of lazy first-touch initialization and eager `SSP.parFin` sampling from
   `RandomOracle.pi_bind_eq_map_fst_of_complete_eq` by restricting each `ProbComp` initializer to
   its finite support and separating the once-sampled initial state table from mutable per-session
   state.
7. **Scope and joint state vs. global setup.** Joint state here is internal to a single subroutine
   protocol `ρ̂`, not a GUC/EUC global setup shared outside `ρ̂`. Structural isolation and
   unrestricted compliance hold by types (`OracleSpec.empty` closed machines and `SubSessionCall`).

## Main definitions

* `Cslib.Crypto.Protocols.UC.SubSessionInput`, `Cslib.Crypto.Protocols.UC.SubSessionBackdoor`,
  `Cslib.Crypto.Protocols.UC.MultiSessionState`: named data structures for multi-session
  functionalities.
* `Cslib.Crypto.Protocols.UC.IdealFunctionality.multiSession`: lazy multi-session extension `F̂`.
* `Cslib.Crypto.Protocols.UC.parFinLazy`: lazy first-touch parallel package runner.
* `Cslib.Crypto.Protocols.UC.MultiHybridProtocol.toJoint`: relabelling `π̃` targeting `F̂`.
* `Cslib.Crypto.Protocols.UC.demuxNetQuery`, `Cslib.Crypto.Protocols.UC.muxNetQuery`,
  `Cslib.Crypto.Protocols.UC.jointDemux`, `Cslib.Crypto.Protocols.UC.jointMux`: explicit
  demultiplexing and multiplexing adversaries.

## Main results

* `Cslib.Crypto.Protocols.UC.run_parFinLazy_eq_parFin`: lazy first-touch initialization agrees
  in distribution with eager `SSP.parFin` initialization.
* `Cslib.Crypto.Protocols.UC.toJoint_polyBounded`,
  `Cslib.Crypto.Protocols.UC.jointDemux_polyBounded`,
  `Cslib.Crypto.Protocols.UC.jointMux_polyBounded`: call-budget preservation.
* `Cslib.Crypto.Protocols.UC.exec_compose_toJoint_multiSession`,
  `Cslib.Crypto.Protocols.UC.exec_composeMulti_toJoint`: exact execution identities between
  `compose ρ.toJoint (F.multiSession (Fin m)).toProtocol` and `composeMulti ρ F.toProtocol`.
* `Cslib.Crypto.Protocols.UC.EmulatesWithin.toJoint_multiSession`,
  `Cslib.Crypto.Protocols.UC.EmulatesWithin.multiSession_toJoint`: fixed-session concrete
  emulation steps in both directions with zero error and `Polynomial.X + 1` overhead.

## References

* [R. Canetti and T. Rabin, *Universal Composition with Joint State*][CanettiRabin2003], CRYPTO
  2003, LNCS 2729, pp. 265–281 (Theorem 1, `F̂`, p. 273; proof, p. 274).
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
`F.multiSession` does not notify the adversary on honest-party activations, making it a stronger
ideal functionality than the source's `F̂`. -/
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

/-! ### Sub-session relabelling and explicit demux/mux adversaries -/

/-- Relabel a multi-session hybrid protocol `ρ` (`SubSessionCall` subroutine calls) to a
single-subroutine `HybridProtocol` targeting `F.multiSession (Fin m)` (`π̃` in
[CanettiRabin2003], p. 274). -/
@[expose] def MultiHybridProtocol.toJoint {m n : ℕ} {In Out NetQ NetR SubIn SubOut : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut) :
    HybridProtocol n In Out NetQ NetR (SubSessionInput (Fin m) SubIn) SubOut :=
  fun κ C =>
    { State := (ρ κ C).State
      init := (ρ κ C).init
      handle := fun q s =>
        OracleComp.interpret
          (sumHandler
            (fun k => OracleComp.query
              (spec := probOracleSpec (partySpec n (SubSessionInput (Fin m) SubIn) SubOut))
              (Sum.inl k))
            fun c => do
              ProbOracleComp.query
                (spec := partySpec n (SubSessionInput (Fin m) SubIn) SubOut)
                (c.party, ⟨c.session, c.input⟩))
          (((ρ κ C).handle q).run s) }

/-- Relabelling `ρ` via `toJoint` preserves its polynomial call budget `pρ` unchanged. -/
theorem toJoint_polyBounded {m n : ℕ} {In Out NetQ NetR SubIn SubOut : Type}
    {ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut} {pρ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) : (ρ.toJoint).PolyBounded pρ := fun κ C => by
  refine ⟨(hρ κ C).1, fun q s => ?_⟩
  refine OracleComp.IsCostBounded.interpret (fun r => ?_) ((hρ κ C).2 q s)
  cases r with
  | inl k => exact OracleComp.IsCostBounded.query (Sum.inl k)
  | inr c =>
    exact OracleComp.IsCostBounded.query
      (spec := probOracleSpec (partySpec n (SubSessionInput (Fin m) SubIn) SubOut))
      (Sum.inr (c.party, ⟨c.session, c.input⟩))

/-- Translate a network query of the `F̂`-hybrid execution (`compose ρ.toJoint F̂`) to the
corresponding network query of the `m`-session execution (`composeMulti ρ F.toProtocol`), keeping
replies identical. -/
@[expose] def demuxNetQuery {m n : ℕ} {In NetQ SubIn BackQ : Type} :
    RoutedNetQ n In (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn)
      (SubSessionBackdoor (Fin m) BackQ)) →
      RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
  | .inl p => .inl p
  | .inr (.inl q) => .inr (.outer q)
  | .inr (.inr (.inl (i, req))) => .inr (.sub req.ssid (.inl (i, req.input)))
  | .inr (.inr (.inr req)) => .inr (.sub req.ssid (.inr req.query))

/-- Inverse network query translation from the `m`-session interface (`composeMulti ρ F.toProtocol`)
to the `F̂`-hybrid interface (`compose ρ.toJoint F̂`). -/
@[expose] def muxNetQuery {m n : ℕ} {In NetQ SubIn BackQ : Type} :
    RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ)) →
      RoutedNetQ n In (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn)
        (SubSessionBackdoor (Fin m) BackQ))
  | .inl p => .inl p
  | .inr (.outer q) => .inr (.inl q)
  | .inr (.sub j (.inl (i, x))) => .inr (.inr (.inl (i, ⟨j, x⟩)))
  | .inr (.sub j (.inr bq)) => .inr (.inr (.inr ⟨j, bq⟩))

private theorem muxNetQuery_demuxNetQuery {m n : ℕ} {In NetQ SubIn BackQ : Type}
    (q : RoutedNetQ n In (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn)
      (SubSessionBackdoor (Fin m) BackQ))) :
    muxNetQuery (demuxNetQuery q) = q := by
  rcases q with p | q | ⟨i, req⟩ | req <;> rfl

private theorem demuxNetQuery_muxNetQuery {m n : ℕ} {In NetQ SubIn BackQ : Type}
    (q : RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))) :
    demuxNetQuery (muxNetQuery q) = q := by
  rcases q with p | q | ⟨j, ⟨i, x⟩ | bq⟩ <;> rfl

/-- Translate the network query interface of a machine via `f` without modifying replies or state.
-/
@[expose] def mapNetMachine {NQ₁ NQ₂ R AdvQ AdvR : Type} (f : NQ₁ → NQ₂)
    (A : Machine (netSpec NQ₁ R) (netSpec AdvQ AdvR)) :
    Machine (netSpec NQ₂ R) (netSpec AdvQ AdvR) where
  State := A.State
  init := A.init
  handle q s :=
    OracleComp.interpret
      (sumHandler
        (fun k => OracleComp.query (spec := probOracleSpec (netSpec NQ₂ R)) (Sum.inl k))
        fun nq => do ProbOracleComp.query (spec := netSpec NQ₂ R) (f nq))
      ((A.handle q).run s)

private theorem isBounded_mapNetMachine {NQ₁ NQ₂ R AdvQ AdvR : Type} (f : NQ₁ → NQ₂)
    {A : Machine (netSpec NQ₁ R) (netSpec AdvQ AdvR)} {t : ℕ} (h : A.IsBounded t) :
    (mapNetMachine f A).IsBounded t := by
  refine ⟨h.1, fun q s => ?_⟩
  refine OracleComp.IsCostBounded.interpret (fun r => ?_) (h.2 q s)
  cases r with
  | inl k => exact OracleComp.IsCostBounded.query (Sum.inl k)
  | inr nq => exact OracleComp.IsCostBounded.query (Sum.inr (f nq))

/-- Explicit demultiplexing adversary for `compose ρ.toJoint (F.multiSession (Fin m)).toProtocol`
running against `composeMulti ρ F.toProtocol` ([CanettiRabin2003], p. 274). -/
@[expose] def jointDemux {m n : ℕ} {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    (A : ExecAdversary n In Out
      (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR) :
    ExecAdversary n In Out (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR :=
  fun κ C => mapNetMachine demuxNetQuery (A κ C)

/-- Explicit multiplexing adversary in the reverse direction: maps `composeMulti ρ F.toProtocol`
queries to `compose ρ.toJoint (F.multiSession (Fin m)).toProtocol`. -/
@[expose] def jointMux {m n : ℕ} {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    (A : ExecAdversary n In Out (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR) :
    ExecAdversary n In Out
      (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR :=
  fun κ C => mapNetMachine muxNetQuery (A κ C)

/-- `jointDemux A` preserves `A`'s polynomial call budget `pA`. -/
theorem jointDemux_polyBounded {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    {A : ExecAdversary n In Out
      (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR}
    {pA : Polynomial ℕ} (hA : A.PolyBounded pA) : (jointDemux A).PolyBounded pA :=
  fun κ C => isBounded_mapNetMachine demuxNetQuery (hA κ C)

/-- `jointMux A` preserves `A`'s polynomial call budget `pA`. -/
theorem jointMux_polyBounded {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    {A : ExecAdversary n In Out (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR}
    {pA : Polynomial ℕ} (hA : A.PolyBounded pA) : (jointMux A).PolyBounded pA :=
  fun κ C => isBounded_mapNetMachine muxNetQuery (hA κ C)

/-! ### Execution identities and concrete step theorems -/

section DemuxProof

private def mapRightProg {ιL ιR₁ ιR₂ : Type} {L : ιL → Type}
    {R : ιR₂ → Type} {α : Type} (f : ιR₁ → ιR₂)
    (prog : ProbOracleComp (L ⊕ₒ (R ∘ f)) α) : ProbOracleComp (L ⊕ₒ R) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec (L ⊕ₒ R)) (Sum.inl k))
      fun q => match q with
        | .inl p => ProbOracleComp.query (spec := L ⊕ₒ R) (Sum.inl p)
        | .inr r => ProbOracleComp.query (spec := L ⊕ₒ R) (Sum.inr (f r)))
    prog

private theorem mapRightProg_pure {ιL ιR₁ ιR₂ : Type} {L : ιL → Type}
    {R : ιR₂ → Type} {α : Type} (f : ιR₁ → ιR₂) (a : α) :
    mapRightProg (L := L) (R := R) f (pure a) = pure a := rfl

private theorem mapRightProg_bind {ιL ιR₁ ιR₂ : Type} {L : ιL → Type}
    {R : ιR₂ → Type} {α β : Type} (f : ιR₁ → ιR₂)
    (p : ProbOracleComp (L ⊕ₒ (R ∘ f)) α)
    (k : α → ProbOracleComp (L ⊕ₒ (R ∘ f)) β) :
    mapRightProg (L := L) (R := R) f (p >>= k) =
      mapRightProg (L := L) (R := R) f p >>= fun a =>
        mapRightProg (L := L) (R := R) f (k a) :=
  OracleComp.interpret_bind _ _ _

private theorem mapRightProg_map {ιL ιR₁ ιR₂ : Type} {L : ιL → Type}
    {R : ιR₂ → Type} {α β : Type} (f : ιR₁ → ιR₂) (g : α → β)
    (p : ProbOracleComp (L ⊕ₒ (R ∘ f)) α) :
    mapRightProg (L := L) (R := R) f (g <$> p) =
      g <$> mapRightProg (L := L) (R := R) f p :=
  OracleComp.interpret_map _ _ _

private theorem runFrom_query_inl_coin {ιI ιO : Type} {I : ιI → Type} {O : ιO → Type}
    (M : Machine I O) (k : ℕ) (s : M.State) :
    M.runFrom (OracleComp.query (Sum.inl k)) s =
      (fun a => (a, s)) <$> ProbOracleComp.sample (ProbComp.unifFin k) := by
  dsimp only [Machine.runFrom]
  erw [OracleComp.run_interpret_query]
  simp only [Machine.handler, sumHandler]
  exact StateT.run_lift _ s

private theorem link_liftAdversary_mapNetMachine {n : ℕ} {In Out NQ₁ NQ₂ R AdvQ AdvR α : Type}
    (f : NQ₁ → NQ₂) (A : Machine (netSpec NQ₁ R) (netSpec AdvQ AdvR))
    (prog : ProbOracleComp (execSpec n In Out AdvQ AdvR) α) :
    (liftAdversary (n := n) (In := In) (Out := Out) (mapNetMachine f A)).link prog =
      mapRightProg (L := partySpec n In Out) (R := netSpec NQ₂ R) f
        ((liftAdversary (n := n) (In := In) (Out := Out) A).link prog) := by
  simp only [Machine.link, mapRightProg_bind, mapRightProg_map]
  rw [show mapRightProg (L := partySpec n In Out) (R := netSpec NQ₂ R) f
      (ProbOracleComp.sample (liftAdversary (n := n) (In := In) (Out := Out) A).init) =
      ProbOracleComp.sample
        (liftAdversary (n := n) (In := In) (Out := Out) (mapNetMachine f A)).init by
    dsimp only [mapRightProg]
    rw [ProbOracleComp.interpret_sample]
    exact (OracleComp.substitute_eq_interpret _ _).symm]
  refine congrArg _ (funext fun s => ?_)
  induction prog using OracleComp.induction generalizing s with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [PFunctor.FreeM.bind_eq_bind]
    erw [Machine.runFrom_bind, Machine.runFrom_bind, mapRightProg_bind]
    cases q with
    | inl k =>
      erw [runFrom_query_inl_coin, runFrom_query_inl_coin]
      erw [mapRightProg_map]
      simp only [mapRightProg]
      erw [ProbOracleComp.interpret_sample, (OracleComp.substitute_eq_interpret _ _).symm]
      simp only [bind_map_left, map_bind]
      exact bind_congr fun a => ih a s
    | inr e =>
      cases e with
      | inl p =>
        erw [Machine.runFrom_query, Machine.runFrom_query]
        change Prod.fst <$> ((StateT.lift (ProbOracleComp.query (.inl p))).run s >>= fun x =>
            (liftAdversary (mapNetMachine f A)).runFrom (cont x.1) x.2) =
          Prod.fst <$> (mapRightProg (L := partySpec n In Out) (R := netSpec NQ₂ R) f
            ((StateT.lift (ProbOracleComp.query (.inl p))).run s) >>= fun x =>
              mapRightProg (L := partySpec n In Out) (R := netSpec NQ₂ R) f
                ((liftAdversary A).runFrom (cont x.1) x.2))
        rw [StateT.run_lift, StateT.run_lift, bind_pure_comp, bind_pure_comp,
          mapRightProg_map, bind_map_left, bind_map_left, map_bind, map_bind]
        exact bind_congr fun a => ih a s
      | inr adv =>
        erw [Machine.runFrom_query, Machine.runFrom_query]
        change Prod.fst <$> (Machine.liftRightProgram (partySpec n In Out)
            (OracleComp.interpret _ ((A.handle adv).run s)) >>= fun x =>
              (liftAdversary (mapNetMachine f A)).runFrom (cont x.1) x.2) =
          Prod.fst <$> (mapRightProg (L := partySpec n In Out) (R := netSpec NQ₂ R) f
            (Machine.liftRightProgram (partySpec n In Out) ((A.handle adv).run s)) >>= fun x =>
              mapRightProg (L := partySpec n In Out) (R := netSpec NQ₂ R) f
                ((liftAdversary A).runFrom (cont x.1) x.2))
        have hint : Machine.liftRightProgram (partySpec n In Out)
            (OracleComp.interpret
              (sumHandler
                (fun k => OracleComp.query (spec := probOracleSpec (netSpec NQ₂ R)) (Sum.inl k))
                fun nq => ProbOracleComp.query (spec := netSpec NQ₂ R) (f nq))
              ((A.handle adv).run s)) =
            mapRightProg (L := partySpec n In Out) (R := netSpec NQ₂ R) f
              (Machine.liftRightProgram (partySpec n In Out) ((A.handle adv).run s)) := by
          dsimp only [Machine.liftRightProgram, mapRightProg]
          erw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
          congr 1 with r : 1
          cases r with
          | inl k => rfl
          | inr nq => rfl
        rw [hint, map_bind, map_bind]
        exact bind_congr fun x => ih x.1 x.2

private def relabelSessionHandler {m n : ℕ} {SubIn SubOut BackQ BackR : Type} :
    (q : Fin m × ((Fin n × SubIn) ⊕ RoutedNetQ n SubIn BackQ)) →
      ProbOracleComp (protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
        (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
        (RoutedNetR SubOut BackR))
        ((SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn BackQ)
          (RoutedNetR SubOut BackR))) q)
  | (j, .inl (i, x)) => ProbOracleComp.query (Sum.inl (i, ⟨j, x⟩))
  | (j, .inr (.inl (i, x))) => ProbOracleComp.query (Sum.inr (Sum.inl (i, ⟨j, x⟩)))
  | (j, .inr (.inr bq)) => ProbOracleComp.query (Sum.inr (Sum.inr ⟨j, bq⟩))

private def relabelSessionProg {m n : ℕ} {SubIn SubOut BackQ BackR α : Type}
    (prog : ProbOracleComp
      (SSP.sessionSpec m
        (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn BackQ) (RoutedNetR SubOut BackR))) α) :
    ProbOracleComp
      (protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
        (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
        (RoutedNetR SubOut BackR)) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
          (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
          (RoutedNetR SubOut BackR)))
        (Sum.inl k))
      relabelSessionHandler)
    prog

private theorem interpret_liftParty_toJoint {m n : ℕ} {SubIn SubOut BackQ BackR α : Type}
    (prog : ProbOracleComp (multiPartySpec m n SubIn SubOut) α) :
    liftParty (NetQ := RoutedNetQ n (SubSessionInput (Fin m) SubIn)
        (SubSessionBackdoor (Fin m) BackQ))
      (NetR := RoutedNetR SubOut BackR)
      (OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query
            (spec := probOracleSpec (partySpec n (SubSessionInput (Fin m) SubIn) SubOut))
            (Sum.inl k))
          fun c => ProbOracleComp.query
            (spec := partySpec n (SubSessionInput (Fin m) SubIn) SubOut)
            (c.party, ⟨c.session, c.input⟩))
        prog) =
      relabelSessionProg
        (liftMultiParty (NQ := RoutedNetQ n SubIn BackQ) (NR := RoutedNetR SubOut BackR) prog) := by
  dsimp only [liftParty, liftMultiParty, relabelSessionProg]
  erw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
  congr 1 with r : 1
  cases r with
  | inl k => rfl
  | inr c =>
    dsimp only [sumHandler]
    erw [OracleComp.interpret_query]

private theorem link_toJoint_eq_relabelSessionProg {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR α : Type}
    (C : Finset (Fin n)) (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (κ : ℕ)
    (prog : ProbOracleComp
      (protocolSpec n In Out
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn)
          (SubSessionBackdoor (Fin m) BackQ)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut BackR))) α) :
    (routeCorrupt C
        (hybridWrap (NQ := RoutedNetQ n (SubSessionInput (Fin m) SubIn)
          (SubSessionBackdoor (Fin m) BackQ))
          (NR := RoutedNetR SubOut BackR) (ρ.toJoint κ C))).link prog =
      relabelSessionProg
        ((routeCorrupt C
          (multiHybridWrap (NQ := RoutedNetQ n SubIn BackQ) (NR := RoutedNetR SubOut BackR)
            (ρ κ C))).link
          (mapRightProg (L := partySpec n In Out)
          (R := netSpec (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ)))
            (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut BackR)))
          demuxNetQuery prog)) := by
  simp only [Machine.link, routeCorrupt, hybridWrap, multiHybridWrap, MultiHybridProtocol.toJoint]
  change (ProbOracleComp.sample (ρ κ C).init >>= fun sρ =>
      Prod.fst <$> (routeCorrupt C (hybridWrap (ρ.toJoint κ C))).runFrom prog sρ) =
    relabelSessionProg (ProbOracleComp.sample (ρ κ C).init >>= fun sρ =>
      Prod.fst <$> (routeCorrupt C (multiHybridWrap (ρ κ C))).runFrom
        (mapRightProg (L := partySpec n In Out)
          (R := netSpec (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ)))
            (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut BackR)))
          demuxNetQuery prog) sρ)
  rw [relabelSessionProg, OracleComp.interpret_bind]
  have hsamp :
      OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query
            (spec := probOracleSpec (protocolSpec n (SubSessionInput (Fin m) SubIn) SubOut
              (RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
              (RoutedNetR SubOut BackR)))
            (Sum.inl k))
          relabelSessionHandler)
        (ProbOracleComp.sample (spec := SSP.sessionSpec m (protocolSpec n SubIn SubOut
          (RoutedNetQ n SubIn BackQ) (RoutedNetR SubOut BackR))) (ρ κ C).init) =
      ProbOracleComp.sample (ρ κ C).init := by
    rw [ProbOracleComp.interpret_sample]
    exact (OracleComp.substitute_eq_interpret _ _).symm
  rw [hsamp]
  refine congrArg _ (funext fun sρ => ?_)
  rw [OracleComp.interpret_map]
  refine congrArg (Prod.fst <$> ·) ?_
  induction prog using OracleComp.induction generalizing sρ with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind, mapRightProg, OracleComp.interpret_bind]
    erw [Machine.runFrom_bind, Machine.runFrom_bind, OracleComp.interpret_bind]
    cases q with
    | inl k =>
      simp only [OracleComp.interpret_query, sumHandler]
      erw [runFrom_query_inl_coin, runFrom_query_inl_coin]
      erw [OracleComp.interpret_map, ProbOracleComp.interpret_sample,
        (OracleComp.substitute_eq_interpret _ _).symm]
      erw [bind_map_left]
      exact bind_congr fun a => ih a sρ
    | inr e =>
      cases e with
      | inl p =>
        simp only [OracleComp.interpret_query, sumHandler]
        erw [Machine.runFrom_query, Machine.runFrom_query]
        by_cases hp : p.1 ∈ C
        · simp only [routeCorrupt, hp, ↓reduceIte, StateT.run]
          erw [OracleComp.interpret_pure]
          simp only [pure_bind]
          exact ih none sρ
        · simp only [routeCorrupt, hp, ↓reduceIte, hybridWrap, multiHybridWrap,
            MultiHybridProtocol.toJoint, StateT.run]
          erw [interpret_liftParty_toJoint (((ρ κ C).handle (.inl p)).run sρ)]
          exact bind_congr fun x => ih x.1 x.2
      | inr nq =>
        rcases nq with ⟨i, x⟩ | q | ⟨i, req⟩ | req
        · simp only [OracleComp.interpret_query, sumHandler, demuxNetQuery]
          erw [Machine.runFrom_query, Machine.runFrom_query]
          by_cases hi : i ∈ C
          · simp only [routeCorrupt, hi, ↓reduceIte, hybridWrap, multiHybridWrap,
              MultiHybridProtocol.toJoint]
            repeat erw [StateT.run_map]
            simp only [StateT.run]
            erw [interpret_liftParty_toJoint (((ρ κ C).handle (.inl (i, x))).run sρ)]
            erw [OracleComp.interpret_map, bind_map_left, bind_map_left]
            exact bind_congr fun p => ih (Sum.inl p.1) p.2
          · simp only [routeCorrupt, hi, ↓reduceIte, StateT.run]
            erw [OracleComp.interpret_pure]
            simp only [pure_bind]
            exact ih (.inl none) sρ
        · simp only [OracleComp.interpret_query, sumHandler, demuxNetQuery]
          erw [Machine.runFrom_query, Machine.runFrom_query]
          simp only [routeCorrupt, hybridWrap, multiHybridWrap, MultiHybridProtocol.toJoint]
          simp only [StateT.run_map]
          simp only [StateT.run]
          erw [liftParty_map, liftMultiParty_map]
          erw [interpret_liftParty_toJoint (((ρ κ C).handle (.inr q)).run sρ)]
          erw [OracleComp.interpret_map, OracleComp.interpret_map]
          simp only [Functor.map_map, bind_map_left]
          exact bind_congr fun (x : NetR × _) => ih (Sum.inr (Sum.inl x.1)) x.2
        all_goals
          simp only [OracleComp.interpret_query, sumHandler, demuxNetQuery]
          erw [Machine.runFrom_query, Machine.runFrom_query]
          simp only [routeCorrupt, hybridWrap, multiHybridWrap]
          repeat erw [StateT.run_map]
          repeat erw [StateT.run_lift]
          simp only [bind_pure_comp, Functor.map_map, bind_map_left]
          erw [OracleComp.interpret_map, OracleComp.interpret_query]
          dsimp only [sumHandler, relabelSessionHandler]
          rw [bind_map_left]
          exact bind_congr fun r => ih (Sum.inr (Sum.inr r)) sρ

private theorem eval_run_multiSession_relabel {m n : ℕ}
    {SubIn SubOut BackQ BackR α : Type}
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) (C : Finset (Fin n)) (κ : ℕ)
    (prog : ProbOracleComp
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn BackQ)
        (RoutedNetR SubOut BackR))) α) :
    ((corruptRouter C ((F.multiSession (Fin m)).toProtocol κ C)).run
        (relabelSessionProg prog)).eval =
      ((SSP.parFin fun _ : Fin m => corruptRouter C (F.toProtocol κ C)).run prog).eval := by
  let M : Fin m → Machine OracleSpec.empty (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn BackQ)
      (RoutedNetR SubOut BackR)) :=
    fun _ => corruptRouter C (F.toProtocol κ C)
  let stripHandler :
      (q : Fin m × ((Fin n × SubIn) ⊕ RoutedNetQ n SubIn BackQ)) →
        ProbOracleComp (SSP.sessionSpec m (protocolSpec n SubIn SubOut
          (RoutedNetQ n SubIn BackQ) (RoutedNetR SubOut BackR)))
          ((SSP.sessionSpec m (protocolSpec n SubIn SubOut
            (RoutedNetQ n SubIn BackQ) (RoutedNetR SubOut BackR))) q)
    | (j, Sum.inl (i, x)) =>
        if i ∈ C then pure none else ProbOracleComp.query (j, Sum.inl (i, x))
    | (j, Sum.inr (Sum.inl (i, x))) =>
        if i ∈ C then ProbOracleComp.query (j, Sum.inr (Sum.inl (i, x))) else pure (Sum.inl none)
    | (j, Sum.inr (Sum.inr bq)) => ProbOracleComp.query (j, Sum.inr (Sum.inr bq))
  let stripProg :=
    OracleComp.interpret
      (sumHandler
        (fun k => OracleComp.query (spec := probOracleSpec _) (Sum.inl k))
        stripHandler)
      prog
  let P₁ := parFinLazy M
  let P₂ := corruptRouter C ((F.multiSession (Fin m)).toProtocol κ C)
  let rep : P₁.State → P₂.State := fun s => { secParam := κ, corrupted := C, sessions := s }
  have h_rs : relabelSessionProg stripProg =
      OracleComp.interpret
        (fun q =>
          OracleComp.interpret
            (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (Sum.inl k))
              relabelSessionHandler)
            (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (Sum.inl k))
              stripHandler q))
        prog := by
    dsimp only [relabelSessionProg, stripProg]
    exact OracleComp.interpret_interpret _ _ prog
  have hP₂ : (P₂.run (relabelSessionProg prog)).eval =
      (P₂.run (relabelSessionProg stripProg)).eval := by
    rw [SSP.eval_run P₂ (relabelSessionProg prog), SSP.eval_run P₂ (relabelSessionProg stripProg)]
    rw [show P₂.init = pure { secParam := κ, corrupted := C, sessions := fun _ => none } from rfl]
    erw [ProbComp.eval_pure, PMF.pure_bind, PMF.pure_bind]
    rw [h_rs]
    dsimp only [relabelSessionProg]
    erw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
    have hint :
        OracleComp.interpret (m := StateT P₂.State PMF)
          (fun q => OracleComp.interpret (fun q s => (Machine.closeProgram (P₂.handler q s)).eval)
            (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (Sum.inl k))
              relabelSessionHandler q)) prog =
          OracleComp.interpret (m := StateT P₂.State PMF)
            (fun q => OracleComp.interpret (fun q s => (Machine.closeProgram (P₂.handler q s)).eval)
              (OracleComp.interpret
                (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (Sum.inl k))
                  relabelSessionHandler)
                (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (Sum.inl k))
                  stripHandler q))) prog := by
      congr 1
      funext q
      rcases q with k | ⟨j, ⟨i, x⟩ | ⟨i, x⟩ | bq⟩
      · rfl
      · dsimp only [sumHandler, stripHandler]
        by_cases hi : i ∈ C
        · simp only [hi, ↓reduceIte, OracleComp.interpret_pure, relabelSessionHandler]
          ext s
          erw [OracleComp.interpret_query, StateT.run_pure]
          simp only [P₂, corruptRouter, hi, ↓reduceIte, Machine.handler, sumHandler]
          rfl
        · simp [hi, relabelSessionHandler]
      · dsimp only [sumHandler, stripHandler]
        by_cases hi : i ∈ C
        · simp [hi, relabelSessionHandler]
        · simp only [hi, ↓reduceIte, OracleComp.interpret_pure, relabelSessionHandler]
          ext s
          erw [OracleComp.interpret_query, StateT.run_pure]
          simp only [P₂, corruptRouter, hi, ↓reduceIte, Machine.handler, sumHandler]
          rfl
      · rfl
    rw [hint]
  have hLazy : (P₂.run (relabelSessionProg stripProg)).eval = (P₁.run stripProg).eval := by
    rw [SSP.eval_run P₂ (relabelSessionProg stripProg), SSP.eval_run P₁ stripProg]
    rw [show P₂.init = pure { secParam := κ, corrupted := C, sessions := fun _ => none } from rfl,
      show P₁.init = pure fun _ => none from rfl]
    erw [ProbComp.eval_pure, ProbComp.eval_pure, PMF.pure_bind, PMF.pure_bind]
    rw [h_rs]
    dsimp only [stripProg]
    erw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
    have hmap := OracleComp.run_interpret_map_state
      (fun q s => (OracleComp.interpret (m := StateT P₁.State PMF)
        (fun q s => (Machine.closeProgram (P₁.handler q s)).eval)
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (Sum.inl k))
          stripHandler q)).run s)
      (fun q s => (OracleComp.interpret (m := StateT P₂.State PMF)
        (fun q s => (Machine.closeProgram (P₂.handler q s)).eval)
        (OracleComp.interpret
          (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (Sum.inl k))
            relabelSessionHandler)
          (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (Sum.inl k))
            stripHandler q))).run s)
      rep
      (by
        rintro (k | ⟨j, q⟩) s
        · conv_lhs => erw [OracleComp.interpret_query]
          conv_rhs => erw [OracleComp.interpret_query]
          simp [P₁, P₂, Machine.handler, sumHandler, StateT.lift, StateT.run,
            Machine.closeProgram_sample, Machine.closeProgram_map, ProbComp.eval_map,
            PMF.map_comp, Function.comp_def]
        · dsimp only [P₁, parFinLazy, M, corruptRouter, IdealFunctionality.toProtocol] at s
          rcases q with ⟨i, x⟩ | ⟨i, x⟩ | bq
          · dsimp only [sumHandler, stripHandler]
            by_cases hi : i ∈ C
            · simp only [hi, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure]
              erw [PMF.pure_map]
              rfl
            · simp only [hi, ↓reduceIte]
              conv_lhs => erw [OracleComp.interpret_query]
              conv_rhs => erw [OracleComp.interpret_query]
              change ((Machine.closeProgram ((P₁.handle (j, Sum.inl (i, x))).run s)).eval).map
                  (fun (a, s') => (a, rep s')) =
                (Machine.closeProgram ((P₂.handle (Sum.inl (i, ⟨j, x⟩))).run (rep s))).eval
              simp only [P₁, P₂, M, parFinLazy, corruptRouter, IdealFunctionality.multiSession,
                IdealFunctionality.toProtocol, hi, ↓reduceIte, rep, StateT.run]
              cases s j with
              | none =>
                simp [Machine.closeProgram_bind, Machine.closeProgram_sample,
                  ProbComp.eval_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]
              | some st =>
                simp only [Machine.closeProgram_bind, Machine.closeProgram_sample,
                  Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_pure,
                  pure_bind, PMF.map_bind, PMF.pure_map]
          · dsimp only [sumHandler, stripHandler]
            by_cases hi : i ∈ C
            · simp only [hi, ↓reduceIte]
              conv_lhs => erw [OracleComp.interpret_query]
              conv_rhs => erw [OracleComp.interpret_query]
              change ((Machine.closeProgram
                  ((P₁.handle (j, Sum.inr (Sum.inl (i, x)))).run s)).eval).map
                  (fun (a, s') => (a, rep s')) =
                (Machine.closeProgram
                  ((P₂.handle (Sum.inr (Sum.inl (i, ⟨j, x⟩)))).run (rep s))).eval
              simp only [P₁, P₂, M, parFinLazy, corruptRouter, IdealFunctionality.multiSession,
                IdealFunctionality.toProtocol, hi, ↓reduceIte, rep, StateT.run_map]
              simp only [StateT.run]
              cases s j with
              | none =>
                simp [Machine.closeProgram_bind, Machine.closeProgram_sample,
                  Machine.closeProgram_map, ProbComp.eval_bind, ProbComp.eval_map, PMF.map_bind,
                  PMF.map_comp, Function.comp_def]
              | some st =>
                simp [Machine.closeProgram_map, ProbComp.eval_map,
                  pure_bind, PMF.map_comp, Function.comp_def]
            · simp only [hi, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure]
              erw [PMF.pure_map]
              rfl
          · dsimp only [sumHandler, stripHandler]
            conv_lhs => erw [OracleComp.interpret_query]
            conv_rhs => erw [OracleComp.interpret_query]
            change ((Machine.closeProgram ((P₁.handle (j, Sum.inr (Sum.inr bq))).run s)).eval).map
                (fun (a, s') => (a, rep s')) =
              (Machine.closeProgram ((P₂.handle (Sum.inr (Sum.inr ⟨j, bq⟩))).run (rep s))).eval
            simp only [P₁, P₂, M, parFinLazy, corruptRouter, IdealFunctionality.multiSession,
              IdealFunctionality.toProtocol, rep, StateT.run_map]
            simp only [StateT.run]
            cases s j with
            | none =>
              simp [Machine.closeProgram_bind, Machine.closeProgram_sample,
                Machine.closeProgram_map, ProbComp.eval_bind, ProbComp.eval_map, PMF.map_bind,
                PMF.map_comp, Function.comp_def]
            | some st =>
              simp [Machine.closeProgram_map, ProbComp.eval_map,
                pure_bind, PMF.map_comp, Function.comp_def])
      prog (fun _ => none)
    have hfst := congrArg (PMF.map Prod.fst) hmap
    rw [PMF.map_comp] at hfst
    dsimp only [StateT.run] at hfst
    exact hfst.symm
  have hEager : ((SSP.parFin M).run stripProg).eval = ((SSP.parFin M).run prog).eval := by
    rw [SSP.eval_run (SSP.parFin M) stripProg, SSP.eval_run (SSP.parFin M) prog]
    refine congrArg _ (funext fun s0 => congrArg (PMF.map Prod.fst)
      (congrArg (fun p => StateT.run p s0) ?_))
    dsimp only [stripProg]
    erw [OracleComp.interpret_interpret]
    have hint :
        OracleComp.interpret (m := StateT ((j : Fin m) → (M j).State) PMF)
          (fun q => OracleComp.interpret
            (fun q s => (Machine.closeProgram ((SSP.parFin M).handler q s)).eval)
            (sumHandler (fun k => OracleComp.query (spec := probOracleSpec _) (Sum.inl k))
              stripHandler q)) prog =
          OracleComp.interpret (m := StateT ((j : Fin m) → (M j).State) PMF)
            (fun q s => (Machine.closeProgram ((SSP.parFin M).handler q s)).eval) prog := by
      congr 1
      funext q
      rcases q with k | ⟨j, ⟨i, x⟩ | ⟨i, x⟩ | bq⟩
      · erw [OracleComp.interpret_query]
      · dsimp only [sumHandler, stripHandler]
        by_cases hi : i ∈ C
        · simp only [hi, ↓reduceIte]
          funext s
          erw [OracleComp.interpret_pure]
          erw [show (pure none : StateT ((j : Fin m) → (M j).State) PMF _) s =
              PMF.pure (none, s) from StateT.run_pure _ _]
          dsimp only [M, corruptRouter, IdealFunctionality.toProtocol] at s
          have h_noop :
              (SSP.parFin M).handler (Sum.inr (j, Sum.inl (i, x))) s = pure (none, s) := by
            simp only [M, SSP.parFin, Machine.handler, sumHandler, corruptRouter,
              IdealFunctionality.toProtocol, hi, ↓reduceIte, StateT.run]
            erw [show (pure none : StateT F.State (ProbOracleComp _) _) (s j) =
                pure (none, s j) from StateT.run_pure _ _]
            simp only [map_pure]
            congr 2
            funext k
            by_cases hk : k = j <;> simp [Function.update, hk]
          rw [h_noop]
          erw [Machine.closeProgram_pure, ProbComp.eval_pure]
          rfl
        · simp only [hi, ↓reduceIte]
          erw [OracleComp.interpret_query]
      · dsimp only [sumHandler, stripHandler]
        by_cases hi : i ∈ C
        · simp only [hi, ↓reduceIte]
          erw [OracleComp.interpret_query]
        · simp only [hi, ↓reduceIte]
          funext s
          erw [OracleComp.interpret_pure]
          erw [show (pure (Sum.inl none) : StateT ((j : Fin m) → (M j).State) PMF _) s =
              PMF.pure (Sum.inl none, s) from StateT.run_pure _ _]
          dsimp only [M, corruptRouter, IdealFunctionality.toProtocol] at s
          have h_noop : (SSP.parFin M).handler (Sum.inr (j, Sum.inr (Sum.inl (i, x)))) s =
              pure (Sum.inl none, s) := by
            simp only [M, SSP.parFin, Machine.handler, sumHandler, corruptRouter,
              IdealFunctionality.toProtocol, hi, ↓reduceIte, StateT.run]
            erw [show (pure (Sum.inl none) : StateT F.State (ProbOracleComp _) _) (s j) =
                pure (Sum.inl none, s j) from StateT.run_pure _ _]
            simp only [map_pure]
            congr 2
            funext k
            by_cases hk : k = j <;> simp [Function.update, hk]
          rw [h_noop]
          erw [Machine.closeProgram_pure, ProbComp.eval_pure]
          rfl
      · erw [OracleComp.interpret_query]
    exact hint
  rw [hP₂, hLazy, run_parFinLazy_eq_parFin, hEager]

private theorem jointDemux_jointMux {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    (A : ExecAdversary n In Out (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR) :
    jointDemux (m := m) (n := n) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR)
      (SubIn := SubIn) (SubOut := SubOut) (BackQ := BackQ) (BackR := BackR)
      (jointMux A) = A := by
  funext κ C
  dsimp only [jointDemux, jointMux, mapNetMachine]
  cases hA : A κ C with
  | mk State init handle =>
    congr 1
    funext q s
    change OracleComp.interpret _ (OracleComp.interpret _ ((handle q).run s)) = (handle q).run s
    erw [OracleComp.interpret_interpret]
    have hid :
        (fun r => OracleComp.interpret
            (sumHandler
              (fun k => OracleComp.query
                (spec := probOracleSpec (netSpec
                  (RoutedNetQ n In (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ)))
                  (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut BackR))))
                (Sum.inl k))
              fun nq => ProbOracleComp.query (demuxNetQuery nq))
            (sumHandler
              (fun k => OracleComp.query
                (spec := probOracleSpec (netSpec
                  (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn)
                    (SubSessionBackdoor (Fin m) BackQ)))
                  (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut BackR))))
                (Sum.inl k))
              (fun nq => ProbOracleComp.query (muxNetQuery nq)) r)) =
        fun r => OracleComp.query r := by
      funext r
      cases r with
      | inl k => rfl
      | inr nq =>
        dsimp only [sumHandler]
        erw [OracleComp.interpret_query]
        change ProbOracleComp.query (demuxNetQuery (muxNetQuery nq)) = _
        rw [demuxNetQuery_muxNetQuery]
        rfl
    rw [hid, OracleComp.interpret_query_eq_self]

end DemuxProof

/-- A step of the proof of Theorem 1 of [CanettiRabin2003] (p. 274), not that theorem;
fixed-session joint-state execution identity for this library's call-bounded UC execution model:
`compose ρ.toJoint (F.multiSession (Fin m)).toProtocol` with adversary `A` and
`composeMulti ρ F.toProtocol` with `jointDemux A` have identical output distributions. -/
theorem exec_compose_toJoint_multiSession {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (F : IdealFunctionality n SubIn SubOut BackQ BackR)
    (A : ExecAdversary n In Out
      (NetQ ⊕ RoutedNetQ n (SubSessionInput (Fin m) SubIn) (SubSessionBackdoor (Fin m) BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR)
    (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    (exec (compose ρ.toJoint (F.multiSession (Fin m)).toProtocol) A C Z κ z).eval =
      (exec (composeMulti ρ F.toProtocol) (jointDemux A) C Z κ z).eval := by
  simp only [exec, execMachine, compose, composeMulti, composeFamily, corruptRouter_comp,
    Machine.run_comp]
  rw [link_toJoint_eq_relabelSessionProg, eval_run_multiSession_relabel,
    ← link_liftAdversary_mapNetMachine]
  rfl

/-- A step of the proof of Theorem 1 of [CanettiRabin2003] (p. 274), not that theorem;
fixed-session reverse joint-state execution identity for this library's call-bounded UC execution
model: `composeMulti ρ F.toProtocol` with adversary `A` and
`compose ρ.toJoint (F.multiSession (Fin m)).toProtocol` with `jointMux A` have identical output
distributions. -/
theorem exec_composeMulti_toJoint {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR AdvQ AdvR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (F : IdealFunctionality n SubIn SubOut BackQ BackR)
    (A : ExecAdversary n In Out (MultiNetQ m NetQ (RoutedNetQ n SubIn BackQ))
      (NetR ⊕ RoutedNetR SubOut BackR) AdvQ AdvR)
    (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    (exec (composeMulti ρ F.toProtocol) A C Z κ z).eval =
      (exec (compose ρ.toJoint (F.multiSession (Fin m)).toProtocol) (jointMux A) C Z κ z).eval := by
  rw [exec_compose_toJoint_multiSession, jointDemux_jointMux]

/-- A step of the proof of Theorem 1 of [CanettiRabin2003] (p. 274), not that theorem;
fixed-session joint-state step for this library's call-bounded `EmulatesWithin` relation:
`compose ρ.toJoint (F.multiSession (Fin m)).toProtocol` emulates `composeMulti ρ F.toProtocol` with
overhead `Polynomial.X + 1` and zero distinguishing error via the explicit demultiplexing adversary
`jointDemux`. Fixed number `m` of sessions chosen in advance; static corruption; pull execution
where `F.multiSession` hides honest-party activations. -/
theorem EmulatesWithin.toJoint_multiSession {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) :
    EmulatesWithin
      (UC.compose ρ.toJoint (F.multiSession (Fin m)).toProtocol)
      (UC.composeMulti ρ F.toProtocol)
      (Polynomial.X + 1)
      (fun _ _ _ => 0) := by
  intro AdvQ AdvR A pA hA
  refine ⟨jointDemux A, pA, jointDemux_polyBounded hA, fun κ => ?_, fun C Z pZ _ κ z => ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    have h := SimPolyBound.refl pA κ
    simp only [Polynomial.eval_X] at h
    exact Nat.le_succ_of_le h
  · simp only [advantage, Game.advantage, exec_compose_toJoint_multiSession, nndist_self, le_rfl]

/-- A step of the proof of Theorem 1 of [CanettiRabin2003] (p. 274), not that theorem;
fixed-session reverse joint-state step for this library's call-bounded `EmulatesWithin`
relation: `composeMulti ρ F.toProtocol` emulates
`compose ρ.toJoint (F.multiSession (Fin m)).toProtocol` with overhead `Polynomial.X + 1` and zero
distinguishing error via `jointMux`. Fixed number `m` of sessions chosen in advance; static
corruption; pull execution. -/
theorem EmulatesWithin.multiSession_toJoint {m n : ℕ}
    {In Out NetQ NetR SubIn SubOut BackQ BackR : Type}
    (ρ : MultiHybridProtocol m n In Out NetQ NetR SubIn SubOut)
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) :
    EmulatesWithin
      (UC.composeMulti ρ F.toProtocol)
      (UC.compose ρ.toJoint (F.multiSession (Fin m)).toProtocol)
      (Polynomial.X + 1)
      (fun _ _ _ => 0) := by
  intro AdvQ AdvR A pA hA
  refine ⟨jointMux A, pA, jointMux_polyBounded hA, fun κ => ?_, fun C Z pZ _ κ z => ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    have h := SimPolyBound.refl pA κ
    simp only [Polynomial.eval_X] at h
    exact Nat.le_succ_of_le h
  · simp only [advantage, Game.advantage, exec_composeMulti_toJoint, nndist_self, le_rfl]

end Cslib.Crypto.Protocols.UC
