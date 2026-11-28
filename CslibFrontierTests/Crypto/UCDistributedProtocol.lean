/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Protocols.UC.DistributedProtocol

/-!
# Tests for `DistributedProtocol` per-party state isolation builder

Exercises `CslibFrontier.Crypto.Protocols.UC.DistributedProtocol` on concrete two-party protocols
`P_msg` and `P_corruptMark`:

* Call-budget certificate transfer (`toMachine_isBounded`, `toProtocol_polyBounded`,
  `toAdaptive_polyBounded`).
* Initial distribution support characterization (`mem_support_init_iff`).
* Static honest-party isolation in `corruptRouter` (`corruptRouter_runFrom_parties_eq`) and in the
  full `execMachine` against an explicit adversary (`execMachine_runFrom_parties_eq`).
* Adaptive honest-party isolation in `adaptiveRouter` with non-trivial `onCorrupt`
  (`adaptiveRouter_runFrom_parties_eq`, `toAdaptive_onCorrupt_parties_ne`) and corruption report
  view (`toAdaptive_corruptionReport_current`).
* Adaptive-to-static round-trip (`toAdaptive_toStatic_of_onCorrupt_eq`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCDistributedProtocol

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC

/-! ### Concrete two-party message-passing distributed protocol -/

/-- Party inputs for `P_msg`. -/
inductive MsgIn : Type
  | send
  | poll
  deriving DecidableEq

/-- Concrete two-party distributed protocol: party `0` samples a uniform initial coin and writes
it to the shared network buffer on `.send`; any party returns its local bit on `.poll`.
`onCorrupt` is the identity. -/
@[reducible] def P_msg : DistributedProtocol 2 MsgIn Bool Unit (Option Bool) where
  PartyState := Option Bool
  NetState := Option Bool
  initParty _ i :=
    if i = 0 then do
      let c ← ProbComp.unifFin 1
      pure (some (decide (c = 0)))
    else pure none
  initNet _ := pure none
  onInput _ _ inp := fun (ps, ns) =>
    match inp with
    | .send => pure (none, (ps, ps))
    | .poll => pure (ps, (ps, ns))
  onNet _ _ := fun ns => pure (ns, ns)
  onCorrupt _ _ ps := ps

/-- Polynomial call-budget witness for `P_msg`. -/
theorem P_msg_polyBounded : P_msg.PolyBounded 1 0 0 0 where
  initParty _ i := by
    by_cases hi : i = 0
    · simp only [P_msg, hi, ↓reduceIte, Polynomial.eval_one]
      exact (OracleComp.IsCostBounded.query 1).bind fun _ => OracleComp.IsCostBounded.pure _ 0
    · simp only [P_msg, hi, ↓reduceIte, Polynomial.eval_one]
      exact (OracleComp.IsCostBounded.pure (none : Option Bool) 0).mono (by omega)
  initNet _ := by
    simpa only [P_msg, Polynomial.eval_zero] using
      OracleComp.IsCostBounded.pure (none : Option Bool) 0
  onInput _ _ inp ps ns := by
    cases inp <;> simpa only [P_msg, Polynomial.eval_zero, StateT.run] using
      OracleComp.IsCostBounded.pure _ 0
  onNet _ _ ns := by
    simpa only [P_msg, Polynomial.eval_zero, StateT.run] using OracleComp.IsCostBounded.pure _ 0

/-- Call-budget check for `P_msg.toMachine` via `toMachine_isBounded`. -/
theorem P_msg_toMachine_isBounded (κ : ℕ) : (P_msg.toMachine κ).IsBounded (2 * 1 + 0 + 0 + 0) :=
  P_msg.toMachine_isBounded
    (by simpa only [Polynomial.eval_one] using P_msg_polyBounded.initParty κ)
    (by simpa only [Polynomial.eval_zero] using P_msg_polyBounded.initNet κ)
    (by simpa only [Polynomial.eval_zero] using P_msg_polyBounded.onInput κ)
    (by simpa only [Polynomial.eval_zero] using P_msg_polyBounded.onNet κ)

/-- Call-budget check for `P_msg.toProtocol` via `toProtocol_polyBounded`. -/
theorem P_msg_toProtocol_polyBounded :
    P_msg.toProtocol.PolyBounded (Polynomial.C 2 * 1 + 0 + 0 + 0) :=
  DistributedProtocol.toProtocol_polyBounded P_msg_polyBounded

/-- Call-budget check for `P_msg.toAdaptive` via `toAdaptive_polyBounded`. -/
theorem P_msg_toAdaptive_polyBounded (mem : PartyMemory) :
    (P_msg.toAdaptive mem).PolyBounded (Polynomial.C 2 * 1 + 0 + 0 + 0) :=
  DistributedProtocol.toAdaptive_polyBounded P_msg_polyBounded mem

/-- Initial-support check: party `1`'s initial state is `none` and `net` is `none` on every
supported initial state of `P_msg.toMachine κ`. -/
theorem P_msg_init_support (κ : ℕ) (s : DistributedState 2 (Option Bool) (Option Bool))
    (hs : s ∈ (ProbComp.eval (P_msg.toMachine κ).init).support) :
    s.parties 1 = none ∧ s.net = none := by
  rw [P_msg.mem_support_init_iff] at hs
  rcases hs with ⟨hparties, hnet⟩
  have h1 := hparties 1
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [P_msg, hne, ↓reduceIte, ProbComp.eval_pure, PMF.mem_support_pure_iff] at h1 hnet
  exact ⟨h1, hnet⟩

/-- Adaptive-to-static round-trip check for `P_msg`. -/
theorem P_msg_toAdaptive_toStatic (mem : PartyMemory) :
    (P_msg.toAdaptive mem).toStatic = P_msg.toProtocol :=
  P_msg.toAdaptive_toStatic_of_onCorrupt_eq mem fun _ _ _ => rfl

/-- Concrete corruption report check on an explicit `DistributedState` by `rfl`. -/
example (mem : PartyMemory) (κ : ℕ) :
    ((P_msg.toAdaptive mem).corruptionReport κ 0
      { inner := { parties := fun i => if i = 0 then some true else some false, net := none }
        corrupted := ∅
        trace := fun _ => [] }).current = some true := rfl

/-! ### Static honest-party isolation with an explicit adversary -/

/-- Concrete adversary that sends `.send` on behalf of corrupted party `0` and queries the
network buffer. -/
@[reducible] def A_msg :
    ExecAdversary 2 MsgIn Bool Unit (Option Bool) Unit (Option Bool) :=
  fun _ _ =>
  { State := Unit
    init := pure ()
    handle := fun _ s => do
      let _ ← ProbOracleComp.query (.inl ((0 : Fin 2), MsgIn.send))
      let buf ← ProbOracleComp.query (.inr ())
      match buf with
      | .inr r => pure (r, s)
      | .inl _ => pure (none, s) }

/-- Concrete static environment program interacting only with corrupted party `0` and the
adversary, never directly activating honest party `1`. -/
def staticEnvProg : ProbOracleComp (execSpec 2 MsgIn Bool Unit (Option Bool)) (Option Bool) := do
  let _ ← ProbOracleComp.query (.inl ((0 : Fin 2), MsgIn.send))
  let buf ← ProbOracleComp.query (.inr ())
  pure buf

private theorem staticEnvProg_queriesSatisfy :
    OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => ∀ x : MsgIn, q ≠ .inl ((1 : Fin 2), x)) staticEnvProg :=
  OracleComp.QueriesSatisfy.bind
    (OracleComp.QueriesSatisfy.query fun _ h => by simp at h)
    fun _ => OracleComp.QueriesSatisfy.bind
      (OracleComp.QueriesSatisfy.query fun _ h => by simp at h)
      fun _ => OracleComp.QueriesSatisfy.pure _

/-- Static `corruptRouter` preserves honest party `1`'s local state across corrupted-party
activations and network queries when `C = {0}`. -/
theorem P_msg_corruptRouter_honest_isolated (κ : ℕ)
    (s : DistributedState 2 (Option Bool) (Option Bool))
    {y : Option Bool × DistributedState 2 (Option Bool) (Option Bool)}
    (hy : y ∈ (Machine.closeEval ((corruptRouter ({0} : Finset (Fin 2)) (P_msg.toMachine κ)).runFrom
      (do
        let _ ← ProbOracleComp.query (.inl ((0 : Fin 2), MsgIn.send))
        let _ ← ProbOracleComp.query (.inr (.inl ((0 : Fin 2), MsgIn.send)))
        let _ ← ProbOracleComp.query (.inr (.inr ()))
        pure (none : Option Bool)) s)).support) :
    y.2.parties 1 = s.parties 1 := by
  refine P_msg.corruptRouter_runFrom_parties_eq κ {0} 1 (by decide) _ ?_ s hy
  exact OracleComp.QueriesSatisfy.bind
    (OracleComp.QueriesSatisfy.query fun _ h => by simp at h)
    fun _ => OracleComp.QueriesSatisfy.bind
      (OracleComp.QueriesSatisfy.query fun _ h => by cases h)
      fun _ => OracleComp.QueriesSatisfy.bind
        (OracleComp.QueriesSatisfy.query fun _ h => by cases h)
        fun _ => OracleComp.QueriesSatisfy.pure _

/-- Full `execMachine` with adversary `A_msg` preserves honest party `1`'s local state when
`C = {0}`. -/
theorem P_msg_execMachine_honest_isolated (κ : ℕ)
    (sP : DistributedState 2 (Option Bool) (Option Bool))
    {a : Option Bool} {sA' : Unit} {sP' : DistributedState 2 (Option Bool) (Option Bool)}
    (hy : (a, sA', sP') ∈ (Machine.closeEval
      ((execMachine P_msg.toProtocol A_msg κ {0}).runFrom staticEnvProg ((), sP))).support) :
    sP'.parties 1 = sP.parties 1 :=
  P_msg.execMachine_runFrom_parties_eq A_msg κ {0} 1 (by decide) staticEnvProg
    staticEnvProg_queriesSatisfy () sP hy

/-! ### Adaptive honest-party isolation with non-trivial `onCorrupt` -/

/-- Concrete two-party protocol whose `onCorrupt` actively mutates the corrupted party's local
state to `true`. -/
@[reducible] def P_corruptMark : DistributedProtocol 2 MsgIn Bool Unit Bool where
  PartyState := Bool
  NetState := Bool
  initParty _ _ := pure false
  initNet _ := pure false
  onInput _ _ inp := fun (ps, ns) =>
    match inp with
    | .send => pure (none, (true, true))
    | .poll => pure (some ps, (ps, ns))
  onNet _ _ := fun ns => pure (ns, ns)
  onCorrupt _ _ _ := true

/-- Non-trivial `onCorrupt` on party `0` still leaves party `1`'s local state untouched. -/
theorem P_corruptMark_onCorrupt_ne (mem : PartyMemory) (κ : ℕ)
    (s : DistributedState 2 Bool Bool) :
    ((P_corruptMark.toAdaptive mem).onCorrupt κ 0 s).parties 1 = s.parties 1 :=
  P_corruptMark.toAdaptive_onCorrupt_parties_ne mem κ (by decide) s

/-- Adaptive environment program that activates party `0`, queries the network, and adaptively
corrupts party `0`, never touching party `1`. -/
def adaptiveEnvProg :
    ProbOracleComp (adaptiveProtocolSpec 2 MsgIn Bool Unit Bool Bool)
      (AdaptiveNetR Bool Bool Bool) := do
  let _ ← ProbOracleComp.query (.inl (.party 0 .send))
  let _ ← ProbOracleComp.query (.inr (.net ()))
  ProbOracleComp.query
    (spec := adaptiveProtocolSpec 2 MsgIn Bool Unit Bool Bool) (.inr (.corrupt 0))

private theorem adaptiveEnvProg_queriesSatisfy :
    OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q =>
        (∀ x : MsgIn, q ≠ .inl (.party (1 : Fin 2) x)) ∧ q ≠ .inr (.corrupt (1 : Fin 2)))
      adaptiveEnvProg := by
  refine OracleComp.QueriesSatisfy.bind
    (OracleComp.QueriesSatisfy.query ?_) fun _ =>
    OracleComp.QueriesSatisfy.bind
      (OracleComp.QueriesSatisfy.query ?_) fun _ =>
      OracleComp.QueriesSatisfy.query ?_
  · exact ⟨(fun _ h => by simp at h), by simp⟩
  · exact ⟨(fun _ h => by simp at h), by simp⟩
  · exact ⟨(fun _ h => by simp at h), by simp⟩

/-- Under `.adaptive` routing on `P_corruptMark`, activating and corrupting party `0` (plus a
network query) leaves honest party `1` uncorrupted and preserves its local state. -/
theorem P_corruptMark_adaptive_honest_isolated (mem : PartyMemory) (κ : ℕ)
    (s : AdaptiveRouterState (DistributedState 2 Bool Bool) Bool 2)
    (hs : (1 : Fin 2) ∉ s.corrupted)
    {y : AdaptiveNetR Bool Bool Bool × AdaptiveRouterState (DistributedState 2 Bool Bool) Bool 2}
    (hy : y ∈ (Machine.closeEval
      ((adaptiveRouter .adaptive (P_corruptMark.toAdaptive mem) κ ∅).runFrom
        adaptiveEnvProg s)).support) :
    (1 : Fin 2) ∉ y.2.corrupted ∧ y.2.inner.parties 1 = s.inner.parties 1 :=
  P_corruptMark.adaptiveRouter_runFrom_parties_eq .adaptive mem κ ∅ 1 adaptiveEnvProg
    adaptiveEnvProg_queriesSatisfy s hs hy

/-- Positive test of the `onCorrupt` hook under `.adaptive` routing: starting from the all-false
initial state and corrupting party `0` produces a point mass whose report carries the post-hook
`current := true` alongside the pre-corruption trace (`some [false]` when `.nonErasing`, `none`
when `.erasing`), mutating party `0`'s cell to `true` while leaving party `1`'s cell at `false`. -/
theorem P_corruptMark_adaptive_corrupt_marks_zero (mem : PartyMemory) (κ : ℕ) :
    Machine.closeEval
      ((adaptiveRouter .adaptive (P_corruptMark.toAdaptive mem) κ ∅).runFrom
        (ProbOracleComp.query
          (spec := adaptiveProtocolSpec 2 MsgIn Bool Unit Bool Bool) (.inr (.corrupt 0)))
        { inner := { parties := fun _ => false, net := false }
          corrupted := ∅
          trace := fun _ => [false] }) =
      PMF.pure
        (.corrupt (some { current := true
                          history := if mem = .nonErasing then some [false] else none }),
         { inner := { parties := fun i => decide (i = 0), net := false }
           corrupted := {0}
           trace := fun _ => [false] }) := by
  let M := adaptiveRouter .adaptive (P_corruptMark.toAdaptive mem) κ ∅
  let q : AdaptivePartyQ 2 MsgIn ⊕ AdaptiveNetQ 2 MsgIn Unit := .inr (.corrupt 0)
  let sM : M.State :=
    { inner := { parties := fun _ => false, net := false }
      corrupted := ∅
      trace := fun _ => [false] }
  have h0 : (0 : Fin 2) ∉ (∅ : Finset (Fin 2)) := by decide
  change Machine.closeEval (M.runFrom (ProbOracleComp.query q) sM) = _
  rw [Machine.runFrom_query]
  dsimp only [M, q, sM, adaptiveRouter, StateT.run]
  simp only [h0, ↓reduceIte, Machine.closeEval_pure]
  congr 1
  refine Prod.ext ?_ ?_
  · cases mem <;>
      simp [AdaptiveProtocol.corruptionReport, DistributedProtocol.toAdaptive, P_corruptMark]
  · simp only [DistributedProtocol.toAdaptive, P_corruptMark, insert_empty_eq]
    congr 1
    apply DistributedState.ext
    · funext i
      fin_cases i <;> decide
    · rfl

/-- Under `.adaptive` routing on `P_msg` (where `onCorrupt` is the identity), when party `0` starts
uncorrupted, activating party `0`, querying the network, and corrupting party `0` returns
`.corrupt (some report)` revealing party `0`'s exact local state `s.inner.parties 0`. -/
theorem P_msg_adaptive_corrupt_reveals (mem : PartyMemory) (κ : ℕ)
    (s : AdaptiveRouterState (DistributedState 2 (Option Bool) (Option Bool)) (Option Bool) 2)
    (hs0 : (0 : Fin 2) ∉ s.corrupted)
    {y : AdaptiveNetR Bool (Option Bool) (Option Bool) ×
      AdaptiveRouterState (DistributedState 2 (Option Bool) (Option Bool)) (Option Bool) 2}
    (hy : y ∈ (Machine.closeEval
      ((adaptiveRouter .adaptive (P_msg.toAdaptive mem) κ ∅).runFrom
        (do
          let _ ← ProbOracleComp.query (.inl (.party (0 : Fin 2) MsgIn.send))
          let _ ← ProbOracleComp.query (.inr (.net ()))
          ProbOracleComp.query
            (spec := adaptiveProtocolSpec 2 MsgIn Bool Unit (Option Bool) (Option Bool))
            (.inr (.corrupt 0))) s)).support) :
    ∃ report, y.1 = .corrupt (some report) ∧ report.current = s.inner.parties 0 := by
  let M := adaptiveRouter .adaptive (P_msg.toAdaptive mem) κ ∅
  let q₁ : AdaptivePartyQ 2 MsgIn ⊕ AdaptiveNetQ 2 MsgIn Unit := .inl (.party 0 .send)
  let q₂ : AdaptivePartyQ 2 MsgIn ⊕ AdaptiveNetQ 2 MsgIn Unit := .inr (.net ())
  let q₃ : AdaptivePartyQ 2 MsgIn ⊕ AdaptiveNetQ 2 MsgIn Unit := .inr (.corrupt 0)
  let sM : M.State := s
  let yM : AdaptiveNetR Bool (Option Bool) (Option Bool) × M.State := y
  have hy' : yM ∈ (Machine.closeEval (M.runFrom
      (ProbOracleComp.query q₁ >>= fun _ =>
        ProbOracleComp.query q₂ >>= fun _ => ProbOracleComp.query q₃) sM)).support := hy
  rw [Machine.runFrom_bind, Machine.runFrom_query, Machine.mem_support_closeEval_bind] at hy'
  obtain ⟨⟨_, s₁⟩, hs₁, hy'⟩ := hy'
  rw [Machine.runFrom_bind, Machine.runFrom_query, Machine.mem_support_closeEval_bind] at hy'
  obtain ⟨⟨_, s₂⟩, hs₂, hy'⟩ := hy'
  rw [Machine.runFrom_query] at hy'
  have hs₁_step : s₁.corrupted = s.corrupted ∧ s₁.inner.parties 0 = s.inner.parties 0 := by
    dsimp only [M, q₁, sM, adaptiveRouter, StateT.run] at hs₁
    simp only [hs0, ↓reduceIte] at hs₁
    erw [Machine.mem_support_closeEval_bind] at hs₁
    obtain ⟨⟨_, inner₁⟩, hinner₁, hs₁'⟩ := hs₁
    erw [Machine.mem_support_closeEval_pure] at hs₁'
    have hcor : s₁.corrupted = s.corrupted := congrArg (fun p => p.2.corrupted) hs₁'
    have hin : s₁.inner = inner₁ := congrArg (fun p => p.2.inner) hs₁'
    dsimp only [DistributedProtocol.toAdaptive, DistributedProtocol.toMachine, P_msg,
      StateT.run] at hinner₁
    erw [Machine.mem_support_closeEval_bind] at hinner₁
    obtain ⟨⟨_, ps₁, ns₁⟩, hps₁, hinner₁'⟩ := hinner₁
    erw [Machine.closeEval_sample, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hps₁
    erw [Machine.mem_support_closeEval_pure] at hinner₁'
    have hps : ps₁ = s.inner.parties 0 := congrArg (fun p => p.2.1) hps₁
    have h0 : inner₁.parties 0 = ps₁ := by
      have := congrArg (fun p => p.2.parties 0) hinner₁'
      simpa only [Function.update_self] using this
    exact ⟨hcor, (congrArg (fun st => st.parties 0) hin).trans (h0.trans hps)⟩
  have hs₂_step : s₂.corrupted = s.corrupted ∧ s₂.inner.parties 0 = s.inner.parties 0 := by
    dsimp only [M, q₂, adaptiveRouter, StateT.run] at hs₂
    erw [Machine.mem_support_closeEval_bind] at hs₂
    obtain ⟨⟨_, inner₂⟩, hinner₂, hs₂'⟩ := hs₂
    erw [Machine.mem_support_closeEval_pure] at hs₂'
    have hnet : inner₂.parties = s₁.inner.parties :=
      P_msg.mem_support_closeEval_handle_net κ () s₁.inner hinner₂
    exact ⟨(congrArg (fun p => p.2.corrupted) hs₂').trans hs₁_step.1,
      (congrArg (fun p => p.2.inner.parties 0) hs₂').trans
        ((congrFun hnet 0).trans hs₁_step.2)⟩
  have hs₂0 : (0 : Fin 2) ∉ s₂.corrupted := hs₂_step.1 ▸ hs0
  dsimp only [M, q₃, adaptiveRouter, StateT.run] at hy'
  simp only [hs₂0, ↓reduceIte] at hy'
  erw [Machine.mem_support_closeEval_pure] at hy'
  refine ⟨_, congrArg Prod.fst hy', ?_⟩
  simp only [AdaptiveProtocol.corruptionReport, DistributedProtocol.toAdaptive, P_msg,
    Function.update_self, hs₂_step.2]

end CslibFrontierTests.Crypto.UCDistributedProtocol
