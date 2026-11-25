/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Time
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryTake
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.InputFromTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.OutputToTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
import CslibFrontier.Computability.Machines.Turing.MultiTape.Tactic.Step
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.EncLen

public import CslibFrontier.Computability.Probabilistic.Oracle.Time.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.Oracle.Normalization
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-! # Internal machine constructions for explicit oracle time

The quantitative halting contracts `ComputesOracleInTimeOn` and `ComputesOracleInTime` are
re-exported by `Oracle.Time`; their closed/open lifts, buffered sequential machine composition
`oComp`, halting conversions and joint-state proofs stay in this implementation module.
-/

public section

namespace Cslib.Probability

open _root_.Turing.MultiTapePTM.Internal.Oracle

open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
  _root_.Turing.MultiTapePTM

/-! ### Private machine-level helpers -/

private theorem of_computesTidily {Operation α β : Type} [DecidableEq Operation]
    [Finite Operation] {input : α ↪ List Bool} {output : β ↪ List Bool} {t : α → ℕ}
    {program : α → WordOracleComp Operation β}
    {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Operation)
    (h : ∀ a, machine.ComputesTidily (input a) (t a) (output <$> program a)) :
    ComputesOracleInTimeOn input output t program := by
  refine ⟨inferInstance, k, Control, inferInstance, machine, fun a State oracle s => ?_⟩
  refine ⟨((h a).runOracle oracle s).symm, ?_⟩
  exact ((h a) []).halted oracle s (machine.initialConfig (input a))
    (Cfg.init_eq_wordsCfg machine.initial (input a)) (fun _ => rfl)

private theorem runOracleConfigFrom_ofClosed {k : ℕ} {State Operation : Type}
    [DecidableEq Operation] (machine : MultiTapePTM k Bool State) (fuel : ℕ) {x : List Bool}
    (ch : Operation → Channel Bool) (cfg : Config k Bool State Empty x) :
    (ofClosed (Operation := Operation) machine).runOracleConfigFrom fuel
        { tapes := cfg.tapes, channels := ch } =
      (fun final => { tapes := final.tapes, channels := ch }) <$>
        ProbOracleComp.sample (machine.runClosedConfigFrom fuel cfg) := by
  let embed (c : Config k Bool State Empty x) : Config k Bool State Operation x :=
    { tapes := c.tapes, channels := ch }
  have hsim := MultiTapeMachine.runConfigFrom_map machine
    (ofClosed (Operation := Operation) machine)
    (fun choices => choices <$> ProbOracleComp.sample
      (spec := fun _ : Operation × List Bool => List Bool) (ProbComp.uniform Bool))
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun oracle _ => oracle.elim) (fun op word => ProbOracleComp.query (op, word)) embed
    (fun c => by
      cases hs : c.tapes.state with
      | none => simp [MultiTapeMachine.runConfigFrom, embed, hs]
      | some state =>
        have hanswer : c.answerSymbols = Empty.elim := funext fun oracle => oracle.elim
        dsimp only [embed]
        simp only [MultiTapeMachine.runConfigFrom, hs, hanswer, bind_map_left, map_bind]
        congr 1 with bit : 1
        cases htr : machine.tr state c.tapes.inputSymbol c.tapes.workTapeSymbols Empty.elim bit with
        | step action symbol move =>
          simp only [ofClosed, htr, map_pure]
          congr 1
          refine Config.ext rfl (funext fun op => ?_)
          cases hop : ch op
          simp [Config.step, hop]
        | query oracle next => exact oracle.elim)
  change MultiTapeMachine.runConfigFrom (ofClosed (Operation := Operation) machine) _ _ fuel
    (embed cfg) = _
  rw [hsim]
  simp only [runClosedConfigFrom, MultiTapePTM.runConfigFrom, ProbOracleComp.sample,
    OracleComp.substitute_eq_interpret, OracleComp.interpret_map,
    MultiTapeMachine.interpret_runConfigFrom]
  congr 2 with oracle : 1
  exact oracle.elim

private theorem runWith_runOracleConfigFrom_ofClosed {k : ℕ} {State Operation OracleState : Type}
    [DecidableEq Operation] (machine : MultiTapePTM k Bool State)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (fuel : ℕ) {x : List Bool} (ch : Operation → Channel Bool)
    (cfg : Config k Bool State Empty x) (s : OracleState) :
    ProbOracleComp.runWith oracle
        ((ofClosed (Operation := Operation) machine).runOracleConfigFrom fuel
          { tapes := cfg.tapes, channels := ch }) s =
      (ProbComp.eval (machine.runClosedConfigFrom fuel cfg)).map
        (fun final => ({ tapes := final.tapes, channels := ch }, s)) := by
  rw [runOracleConfigFrom_ofClosed, ProbOracleComp.runWith_map, ProbOracleComp.runWith_sample,
    PMF.map_comp]
  rfl

private theorem ofClosed_spec {k : ℕ} {State Operation α β : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool} {t : α → ℕ} {program : α → ProbComp β}
    (machine : MultiTapePTM k Bool State)
    (hmachine : ∀ a, (ProbComp.eval (program a)).map output =
        ProbComp.eval (machine.runClosed (t a) (input a)) ∧
      ∀ final ∈ (ProbComp.eval (machine.runConfigFrom (ProbComp.uniform Bool) Empty.elim
          (t a) (machine.initialConfig (input a)))).support,
        final.tapes.state = none) :
    ∀ a (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (output <$> ProbOracleComp.sample (program a)) s =
        ProbOracleComp.runWith oracle
          ((ofClosed (Operation := Operation) machine).runOracle (t a) (input a)) s ∧
      ∀ final ∈ (ProbOracleComp.runWith oracle
          ((ofClosed (Operation := Operation) machine).runOracleConfigFrom (t a)
            ((ofClosed (Operation := Operation) machine).initialConfig (input a))) s).support,
        final.1.tapes.state = none := by
  intro a OracleState oracle s
  obtain ⟨hout, hhalt⟩ := hmachine a
  refine ⟨?_, ?_⟩
  · rw [run_interpret_runOracle_ofClosed, ← hout, ← ProbOracleComp.sample_map,
      ProbOracleComp.runWith_sample, ProbComp.eval_map]
  · intro final hfinal
    change final ∈ (ProbOracleComp.runWith oracle
      ((ofClosed (Operation := Operation) machine).runOracleConfigFrom (t a)
        { tapes := (machine.initialConfig (input a)).tapes, channels := fun _ => {} })
      s).support at hfinal
    rw [runWith_runOracleConfigFrom_ofClosed] at hfinal
    obtain ⟨cfg, hcfg, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hhalt cfg hcfg

section BufferedOracleComp

variable {k₀ k₁ : ℕ} {State₀ State₁ Operation OracleState : Type} {x : List Bool}

private def oReserve (k₁ : ℕ) (cfg : Config k₀ Bool State₀ Operation x) :
    Config (k₁ + k₀) Bool State₀ Operation x :=
  cfg.embed (Fin.natAddEmb k₁) (fun _ _ => none) (fun _ => 0)

private def oBuffer (k₁ : ℕ) (cfg : Config k₀ Bool State₀ Operation x) :
    Config (k₁ + k₀ + 2) Bool State₀ Operation x :=
  (OutputToTape.config (oReserve k₁ cfg)).embed Fin.castSuccEmb (fun _ _ => none) (fun _ => 0)

private def oSource (m₁ : MultiTapePTM k₀ Bool State₀ Operation) (k₁ : ℕ) :
    MultiTapePTM (k₁ + k₀ + 2) Bool State₀ Operation :=
  ((m₁.extendTapes (Fin.natAddEmb k₁)).outputToTape).extendTapes Fin.castSuccEmb

private def oConsumer (m₂ : MultiTapePTM k₁ Bool State₁ Operation) (k₀ : ℕ) :
    MultiTapePTM (k₁ + k₀ + 2) Bool State₁ Operation :=
  (m₂.extendTapes (Fin.castAddEmb k₀)).inputFromTape

private noncomputable def oContinuation (m₂ : MultiTapePTM k₁ Bool State₁ Operation) (k₀ : ℕ)
    (mark : Bool) : MultiTapePTM (k₁ + k₀ + 2) Bool
      ((MarkWorkState ⊕ RewindWorkState) ⊕ State₁) Operation :=
  (ofDeterministic (prepareInput (k₁ + k₀) mark)).seq (oConsumer m₂ k₀)

private noncomputable def oComp (m₂ : MultiTapePTM k₁ Bool State₁ Operation)
    (m₁ : MultiTapePTM k₀ Bool State₀ Operation) (mark : Bool) :
    MultiTapePTM (k₁ + k₀ + 2) Bool
      (State₀ ⊕ ((MarkWorkState ⊕ RewindWorkState) ⊕ State₁)) Operation :=
  (oSource m₁ k₁).seq (oContinuation m₂ k₀ mark)

private def oConsumerConfig (mark : Bool) (cfg₀ : Config k₀ Bool State₀ Operation x)
    (cfg₁ : Config k₁ Bool State₁ Operation cfg₀.tapes.output) :
    Config (k₁ + k₀ + 2) Bool State₁ Operation x :=
  InputFromTape.config mark
    (cfg₁.embed (Fin.castAddEmb k₀)
      (oReserve k₁ cfg₀).tapes.workTapes (oReserve k₁ cfg₀).tapes.workTapePos)
    x cfg₀.tapes.inputPos

private def oReady (mark : Bool) (k₁ : ℕ) (cfg₀ : Config k₀ Bool State₀ Operation x) :
    Config (k₁ + k₀ + 2) Bool (MarkWorkState ⊕ RewindWorkState) Operation x where
  tapes := ⟨none, cfg₀.tapes.inputPos,
    Fin.append (oReserve k₁ cfg₀).tapes.workTapes
      ![tapeOfList cfg₀.tapes.output, Function.update (fun _ => none) (-1) (some mark)],
    Fin.append (oReserve k₁ cfg₀).tapes.workTapePos (fun _ => 0), []⟩
  channels := cfg₀.channels

private theorem oBuffer_tapes (k₁ : ℕ) (cfg₀ : Config k₀ Bool State₀ Operation x) :
    (oBuffer k₁ cfg₀).tapes =
      ⟨cfg₀.tapes.state, cfg₀.tapes.inputPos,
        Fin.append (oReserve k₁ cfg₀).tapes.workTapes
          ![tapeOfList cfg₀.tapes.output, fun _ => none],
        Fin.append (oReserve k₁ cfg₀).tapes.workTapePos
          ![(cfg₀.tapes.output.length : ℤ), 0], []⟩ := by
  have happend {α : Type} (f : Fin (k₁ + k₀) → α) (a b : α) :
      Fin.lastCases b (Fin.lastCases a f) = Fin.append f ![a, b] := by
    have hsnoc {n : ℕ} (f : Fin n → α) (a : α) :
        (Fin.lastCases a f : Fin (n + 1) → α) = Fin.snoc f a := by
      funext i
      induction i using Fin.lastCases <;> simp
    change Fin.lastCases b (Fin.lastCases a f) = Fin.append f (Fin.cons a (Fin.cons b Fin.elim0))
    rw [hsnoc, hsnoc, Fin.append_right_cons, Fin.append_right_eq_snoc]
    rfl
  simp only [oBuffer, Config.embed, OutputToTape.config, MultiTapeTM.embed_castSucc,
    MultiTapeTM.outCfg, happend]
  rfl

private theorem runFrom_oPrepare (mark : Bool) (k₁ : ℕ)
    (cfg₀ : Config k₀ Bool State₀ Operation x) :
    (prepareInput (k₁ + k₀) mark).runFrom
        ((oBuffer k₁ cfg₀).tapes.withState
          (some (prepareInput (k₁ + k₀) mark).q₀)) (cfg₀.tapes.output.length + 4) =
      (oReady mark k₁ cfg₀).tapes := by
  rw [MultiTapeTM.runFrom_prepareInput mark _ cfg₀.tapes.output
    (by rw [oBuffer_tapes]; simp) (by rw [oBuffer_tapes]; simp) (by rw [oBuffer_tapes]; simp)]
  rw [oBuffer_tapes]
  tm_step [oReady, Fin.castAdd_ne_natAdd]

private theorem start_oReady (m₂ : MultiTapePTM k₁ Bool State₁ Operation) (mark : Bool)
    (cfg₀ : Config k₀ Bool State₀ Operation x) :
    Sequential.start (oConsumer m₂ k₀) (oReady mark k₁ cfg₀) =
      oConsumerConfig mark cfg₀
        { tapes := Cfg.init m₂.initial cfg₀.tapes.output, channels := cfg₀.channels } := by
  tm_step [oReady, oConsumerConfig, Config.embed, MultiTapeTM.embed_castAdd, oReserve,
    MultiTapeTM.embed_natAdd]

private theorem runOracleConfigFrom_oSource [DecidableEq Operation]
    (m₁ : MultiTapePTM k₀ Bool State₀ Operation) (k₁ fuel : ℕ) (x : List Bool) :
    (oSource m₁ k₁).runOracleConfigFrom fuel ((oSource m₁ k₁).initialConfig x) =
      oBuffer k₁ <$> m₁.runOracleConfigFrom fuel (m₁.initialConfig x) := by
  simp only [oSource, runOracleConfigFrom,
    MultiTapeMachine.initialConfig_extendTapes,
    MultiTapeMachine.initialConfig_outputToTape,
    MultiTapePTM.runConfigFrom_embed,
    MultiTapePTM.runConfigFrom_outputToTape,
    Functor.map_map]
  rfl

private theorem runOracleConfigFrom_oConsumer [DecidableEq Operation]
    (m₂ : MultiTapePTM k₁ Bool State₁ Operation) (mark : Bool)
    (cfg₀ : Config k₀ Bool State₀ Operation x)
    (cfg₁ : Config k₁ Bool State₁ Operation cfg₀.tapes.output) (fuel : ℕ) :
    (oConsumer m₂ k₀).runOracleConfigFrom fuel (oConsumerConfig mark cfg₀ cfg₁) =
      oConsumerConfig mark cfg₀ <$> m₂.runOracleConfigFrom fuel cfg₁ := by
  simp only [oConsumer, oConsumerConfig, runOracleConfigFrom,
    MultiTapePTM.runConfigFrom_inputFromTape,
    MultiTapePTM.runConfigFrom_embed,
    Functor.map_map]
  rfl

private theorem runWith_oContinuation [DecidableEq Operation]
    (m₂ : MultiTapePTM k₁ Bool State₁ Operation)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (mark : Bool) (cfg₀ : Config k₀ Bool State₀ Operation x) (prepareTime runTime : ℕ)
    (s₁ : OracleState) (hprepare : cfg₀.tapes.output.length + 4 ≤ prepareTime)
    (hrun : ∀ final ∈ (ProbOracleComp.runWith oracle
      (m₂.runOracleConfigFrom runTime
        { tapes := Cfg.init m₂.initial cfg₀.tapes.output, channels := cfg₀.channels }) s₁).support,
      final.1.tapes.state = none) :
    ProbOracleComp.runWith oracle
      ((oContinuation m₂ k₀ mark).runOracleConfigFrom (prepareTime + runTime)
        (Sequential.start (oContinuation m₂ k₀ mark) (oBuffer k₁ cfg₀))) s₁ =
      (ProbOracleComp.runWith oracle (m₂.runOracleConfigFrom runTime
        { tapes := Cfg.init m₂.initial cfg₀.tapes.output, channels := cfg₀.channels }) s₁).map
        (fun (final, s₂) => (Sequential.right (oConsumerConfig mark cfg₀ final), s₂)) := by
  let prep := prepareInput (k₁ + k₀) mark
  let initial := Sequential.start (ofDeterministic prep) (oBuffer k₁ cfg₀)
  have hdet := runFrom_oPrepare mark k₁ cfg₀
  change prep.runFrom initial.tapes (cfg₀.tapes.output.length + 4) = _ at hdet
  have hprep : prep.runFrom initial.tapes prepareTime = (oReady mark k₁ cfg₀).tapes := by
    rw [prep.runFrom_eq_of_halt initial.tapes hprepare (by rw [hdet]; rfl), hdet]
  have hstate : ProbOracleComp.runWith oracle
      ((ofDeterministic prep).runOracleConfigFrom prepareTime initial) s₁ =
      PMF.pure (oReady mark k₁ cfg₀, s₁) := by
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hprep]
    rfl
  have hconsumer_halt : ∀ final ∈ (ProbOracleComp.runWith oracle
      ((oConsumer m₂ k₀).runOracleConfigFrom runTime
        (oConsumerConfig mark cfg₀
          { tapes := Cfg.init m₂.initial cfg₀.tapes.output, channels := cfg₀.channels }))
      s₁).support, final.1.tapes.state = none := by
    intro final hfinal
    rw [runOracleConfigFrom_oConsumer, ProbOracleComp.runWith_map] at hfinal
    obtain ⟨⟨res, s₂⟩, hres, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hrun (res, s₂) hres
  change ProbOracleComp.runWith oracle
    (((ofDeterministic prep).seq (oConsumer m₂ k₀)).runOracleConfigFrom
      _ (Sequential.left (oConsumer m₂ k₀) initial)) s₁ = _
  rw [run_interpret_runOracleConfigFrom_seq _ _ oracle _ prepareTime runTime s₁
    (by simp [hstate, oReady])
    (by
      rintro ⟨resCfg, resState⟩ hresult
      rw [hstate, PMF.mem_support_pure_iff] at hresult
      rcases Prod.mk.inj hresult with ⟨rfl, rfl⟩
      rw [start_oReady]
      exact hconsumer_halt),
    hstate, PMF.pure_bind, start_oReady, runOracleConfigFrom_oConsumer, ProbOracleComp.runWith_map,
    PMF.map_comp]
  rfl

private theorem runWith_oComp [DecidableEq Operation]
    (m₁ : MultiTapePTM k₀ Bool State₀ Operation)
    (m₂ : MultiTapePTM k₁ Bool State₁ Operation)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (mark : Bool) (x : List Bool) (t₁ t₂ : ℕ) (s : OracleState)
    (hfirst : ∀ final ∈ (ProbOracleComp.runWith oracle
      (m₁.runOracleConfigFrom t₁ (m₁.initialConfig x)) s).support,
      final.1.tapes.state = none)
    (hsecond : ∀ result ∈ (ProbOracleComp.runWith oracle
      (m₁.runOracleConfigFrom t₁ (m₁.initialConfig x)) s).support,
      ∀ final ∈ (ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom t₂
          { tapes := Cfg.init m₂.initial result.1.tapes.output,
            channels := result.1.channels }) result.2).support,
        final.1.tapes.state = none) :
    ProbOracleComp.runWith oracle ((oComp m₂ m₁ mark).runOracleConfigFrom
        (t₁ + (t₁ + 4 + t₂)) ((oComp m₂ m₁ mark).initialConfig x)) s =
      (ProbOracleComp.runWith oracle (m₁.runOracleConfigFrom t₁ (m₁.initialConfig x)) s).bind
        (fun (cfg₀, s₁) =>
          (ProbOracleComp.runWith oracle (m₂.runOracleConfigFrom t₂
            { tapes := Cfg.init m₂.initial cfg₀.tapes.output,
              channels := cfg₀.channels }) s₁).map
            (fun (cfg₁, s₂) =>
              (Sequential.right (Sequential.right (oConsumerConfig mark cfg₀ cfg₁)), s₂))) := by
  have hlen : ∀ result ∈ (ProbOracleComp.runWith oracle
      (m₁.runOracleConfigFrom t₁ (m₁.initialConfig x)) s).support,
      result.1.tapes.output.length ≤ t₁ := by
    rintro ⟨cfg₀, s₁⟩ hres
    have h := length_output_le_of_mem_support_runOracleConfigFrom m₁ oracle t₁
      (m₁.initialConfig x) s hres
    simpa [MultiTapeMachine.initialConfig, Cfg.init] using h
  change ProbOracleComp.runWith oracle
    (((oSource m₁ k₁).seq (oContinuation m₂ k₀ mark)).runOracleConfigFrom
      _ (Sequential.left (oContinuation m₂ k₀ mark) ((oSource m₁ k₁).initialConfig x))) s = _
  rw [run_interpret_runOracleConfigFrom_seq _ _ oracle _ t₁ (t₁ + 4 + t₂) s
    (by
      intro result hresult
      rw [runOracleConfigFrom_oSource, ProbOracleComp.runWith_map] at hresult
      obtain ⟨⟨cfg₀, s₁⟩, hcfg₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      exact hfirst (cfg₀, s₁) hcfg₀)
    (by
      intro result hresult final hfinal
      rw [runOracleConfigFrom_oSource, ProbOracleComp.runWith_map] at hresult
      obtain ⟨⟨cfg₀, s₁⟩, hcfg₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      dsimp only [Prod.map_apply, id_eq] at hfinal
      have hlen₀ : cfg₀.tapes.output.length ≤ t₁ := hlen (cfg₀, s₁) hcfg₀
      rw [runWith_oContinuation m₂ oracle mark cfg₀ (t₁ + 4) t₂ s₁
        (by omega) (hsecond (cfg₀, s₁) hcfg₀)] at hfinal
      obtain ⟨⟨cfg₁, s₂⟩, hcfg₁, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
      change cfg₁.tapes.state.map Sum.inr = none
      rw [hsecond (cfg₀, s₁) hcfg₀ (cfg₁, s₂) hcfg₁]
      rfl),
    runOracleConfigFrom_oSource, ProbOracleComp.runWith_map, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨cfg₀, s₁⟩ hcfg₀ => ?_
  dsimp only [Function.comp_def, Prod.map_apply, id_eq]
  have hlen₀ : cfg₀.tapes.output.length ≤ t₁ := hlen (cfg₀, s₁) hcfg₀
  rw [runWith_oContinuation m₂ oracle mark cfg₀ (t₁ + 4) t₂ s₁
    (by omega) (hsecond (cfg₀, s₁) hcfg₀), PMF.map_comp]
  rfl

end BufferedOracleComp

/-! ### Basic properties of `ComputesOracleInTimeOn` -/

namespace ComputesOracleInTimeOn

variable {Operation α β γ : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
  {t t₁ t₂ : α → ℕ} {program program' : α → WordOracleComp Operation γ}

/-- Finiteness of the operation channel type is part of the certificate. -/
theorem finite_operations (h : ComputesOracleInTimeOn input output t program) :
    Finite Operation := h.1

/-- Enlarging the step schedule preserves halting oracle realization unconditionally, without
requiring the larger schedule to be computable. -/
theorem mono (h : ComputesOracleInTimeOn input output t₁ program) (hle : ∀ a, t₁ a ≤ t₂ a) :
    ComputesOracleInTimeOn input output t₂ program := by
  obtain ⟨hops, k, Control, hfinite, machine, hmachine⟩ := h
  refine ⟨hops, k, Control, hfinite, machine, fun a State oracle s => ?_⟩
  obtain ⟨hlaw, hhalt⟩ := hmachine a State oracle s
  have hcfg := run_interpret_runOracleConfigFrom_eq_of_halted machine oracle
    (machine.initialConfig (input a)) (hle a) s hhalt
  refine ⟨?_, ?_⟩
  · rw [hlaw, runOracle_eq_map, runOracle_eq_map, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_map, hcfg]
  · intro final hfinal
    rw [hcfg] at hfinal
    exact hhalt final hfinal

/-- Equality of the complete joint output/state semantics preserves halting oracle realization. -/
theorem congr (h : ComputesOracleInTimeOn input output t program)
    (heq : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (program a) s =
        ProbOracleComp.runWith oracle (program' a) s) :
    ComputesOracleInTimeOn input output t program' := by
  obtain ⟨hops, k, Control, hfinite, machine, hmachine⟩ := h
  refine ⟨hops, k, Control, hfinite, machine, fun a State oracle s => ?_⟩
  obtain ⟨hlaw, hhalt⟩ := hmachine a State oracle s
  refine ⟨?_, hhalt⟩
  simpa only [ProbOracleComp.runWith_map, heq] using hlaw

/-- Every supported encoded output has length at most `t a`, regardless of oracle reply lengths. -/
theorem length_le (h : ComputesOracleInTimeOn input output t program) (a : α)
    {State : Type} (oracle : Operation × List Bool → StateT State PMF (List Bool))
    (s s' : State) {result : γ}
    (hresult : (result, s') ∈ (ProbOracleComp.runWith oracle (program a) s).support) :
    (output result).length ≤ t a := by
  obtain ⟨_, k, Control, _, machine, hmachine⟩ := h
  have hmap : (output result, s') ∈
      (ProbOracleComp.runWith oracle (output <$> program a) s).support := by
    rw [ProbOracleComp.runWith_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(result, s'), hresult, rfl⟩
  rw [(hmachine a State oracle s).1] at hmap
  exact machine.length_output_runOracle_le oracle (t a) (input a) (output result) s s' hmap

/-- Instrumenting the private oracle state with a transcript shows that `program a` makes at most
`t a` external queries on every path, each of payload length at most `t a`. -/
theorem query_bounds (h : ComputesOracleInTimeOn input output t program) (a : α) :
    (program a).IsQueryBounded (t a) ∧
      (program a).QueriesSatisfy fun request => request.2.length ≤ t a := by
  obtain ⟨_, k, Control, _, machine, hmachine⟩ := h
  obtain ⟨hcalls, hsize⟩ := machine.query_bounds_runOracle (t a) (input a)
  have hrun (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      (s s' : State) (result : List Bool)
      (transcript : OracleComp.Transcript (fun _ : Operation × List Bool => List Bool))
      (hmem : (result, s', transcript) ∈ (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (output <$> program a) (s, [])).support) :
      transcript.length ≤ t a ∧ ∀ entry ∈ transcript, entry.1.2.length ≤ t a := by
    rw [(hmachine a (State × OracleComp.Transcript (fun _ : Operation × List Bool => List Bool))
      (OracleComp.withTranscript oracle) (s, [])).1] at hmem
    exact ⟨hcalls.length_transcript_le oracle hmem, hsize.forall_mem_transcript oracle hmem⟩
  have hcalls' : ProbOracleComp.IsQueryBounded (output <$> program a) (t a) :=
    ProbOracleComp.isQueryBounded_of_length_transcript_le fun State oracle s s' result
      transcript hmem => (hrun State oracle s s' result transcript hmem).1
  have hsize' : ProbOracleComp.QueriesSatisfy
      (fun request => request.2.length ≤ t a) (output <$> program a) :=
    ProbOracleComp.queriesSatisfy_of_forall_mem_transcript fun State oracle s s' result
      transcript hmem => (hrun State oracle s s' result transcript hmem).2
  exact ⟨(OracleComp.isCostBounded_map_iff _ _ _).mp hcalls',
    (OracleComp.queriesSatisfy_map_iff _ _).mp hsize'⟩

/-- Every execution path of `program a` makes at most `t a` external queries. -/
theorem isQueryBounded (h : ComputesOracleInTimeOn input output t program) (a : α) :
    (program a).IsQueryBounded (t a) :=
  (h.query_bounds a).1

/-- Every external query issued by `program a` has payload length at most `t a`. -/
theorem queriesSatisfy_length_le (h : ComputesOracleInTimeOn input output t program) (a : α) :
    (program a).QueriesSatisfy fun request => request.2.length ≤ t a :=
  (h.query_bounds a).2

/-- A step-`t` oracle realization automatically satisfies the `(t, t)` time-and-query bound. -/
theorem computesOracleInTimeAndQueriesOn (h : ComputesOracleInTimeOn input output t program) :
    ComputesOracleInTimeAndQueriesOn input output t t program :=
  ⟨h, h.isQueryBounded⟩

/-- Sampling one private fair bit takes `1` step and leaves every external oracle untouched. -/
theorem uniform_bool [Finite Operation] (input : α ↪ List Bool) :
    ComputesOracleInTimeOn (Operation := Operation) input encBool (fun _ => 1)
      (fun _ => ProbOracleComp.sample (ProbComp.uniform Bool)) :=
  of_computesTidily coinMachine fun a => computesTidily_coinMachine (input a)

/-- One bounded-prefix external query `(op, q)` reading at most `limit` reply bits runs in
`4 * q.length + 2 * limit + 6` steps. -/
theorem query_take_pair [Finite Operation] (op : Operation) :
    ComputesOracleInTimeOn (encPair encBits encUnary) encBits
      (fun request : List Bool × ℕ => 4 * request.1.length + 2 * request.2 + 6)
      (fun request => List.take request.2 <$>
        ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool)
          (op, request.1)) :=
  of_computesTidily (queryTakePTM op) fun request =>
    (computesTidily_queryTakePTM op request.1 request.2).congr fun _ _ _ => by
      simp only [encBits, Function.Embedding.coe_refl, id_map]

-- Unconditional `ComputesOracleInTimeOn.bind` at `2 * t₁ a + t₂' a + 4` does not hold because
-- `ComputesOracleInTimeOn` allows `m₁` to halt with unsubmitted symbols in `queryBuffer`, which
-- `oComp` passes into `m₂`. Whenever `m₂`'s joint tape-and-state law from `cfg₀.channels` agrees
-- with its run from empty channels (`m₂.initialConfig`), `oComp m₂ m₁ true` composes both phases
-- in `2 * t₁ a + t₂' a + 4` steps; this covers both `bind_sample_left` and `bind_sample_right`.
private theorem oComp_computesOracleInTimeOn [Finite Operation]
    {first : α → WordOracleComp Operation β} {second : β → WordOracleComp Operation γ}
    {t₂ : β → ℕ} {t₂' : α → ℕ} {k₁ k₂ : ℕ} {State₁ State₂ : Type}
    [Finite State₁] [Finite State₂]
    (m₁ : MultiTapePTM k₁ Bool State₁ Operation)
    (m₂ : MultiTapePTM k₂ Bool State₂ Operation)
    (hm₁ : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (middle <$> first a) s =
        ProbOracleComp.runWith oracle (m₁.runOracle (t₁ a) (input a)) s ∧
      ∀ final ∈ (ProbOracleComp.runWith oracle
          (m₁.runOracleConfigFrom (t₁ a) (m₁.initialConfig (input a))) s).support,
        final.1.tapes.state = none)
    (hm₂ : ∀ b (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (output <$> second b) s =
        ProbOracleComp.runWith oracle (m₂.runOracle (t₂ b) (middle b)) s ∧
      ∀ final ∈ (ProbOracleComp.runWith oracle
          (m₂.runOracleConfigFrom (t₂ b) (m₂.initialConfig (middle b))) s).support,
        final.1.tapes.state = none)
    (ht₂ : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      s s' b, (b, s') ∈ (ProbOracleComp.runWith oracle (first a) s).support → t₂ b ≤ t₂' a)
    (hchannels : ∀ a (State : Type)
      (oracle : Operation × List Bool → StateT State PMF (List Bool)) s cfg₀ s₁,
      (cfg₀, s₁) ∈ (ProbOracleComp.runWith oracle
        (m₁.runOracleConfigFrom (t₁ a) (m₁.initialConfig (input a))) s).support →
      (ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom (t₂' a)
          { tapes := Cfg.init m₂.initial cfg₀.tapes.output, channels := cfg₀.channels }) s₁).map
        (Prod.map (fun c => (c.tapes.output, c.tapes.state)) id) =
      (ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom (t₂' a) (m₂.initialConfig cfg₀.tapes.output)) s₁).map
        (Prod.map (fun c => (c.tapes.output, c.tapes.state)) id)) :
    ComputesOracleInTimeOn input output (fun a => 2 * t₁ a + t₂' a + 4)
      (fun a => do
        let b ← first a
        second b) := by
  refine ⟨inferInstance, k₂ + k₁ + 2, _, inferInstance, oComp m₂ m₁ true,
    fun a State oracle s => ?_⟩
  obtain ⟨hlaw₁, hhalt₁⟩ := hm₁ a State oracle s
  have hmem_word : ∀ cfg₀ s₁,
      (cfg₀, s₁) ∈ (ProbOracleComp.runWith oracle
        (m₁.runOracleConfigFrom (t₁ a) (m₁.initialConfig (input a))) s).support →
      ∃ b, (b, s₁) ∈ (ProbOracleComp.runWith oracle (first a) s).support ∧
        middle b = cfg₀.tapes.output := by
    intro cfg₀ s₁ hcfg₀
    have hout_mem : (cfg₀.tapes.output, s₁) ∈
        (ProbOracleComp.runWith oracle (m₁.runOracle (t₁ a) (input a)) s).support := by
      rw [runOracle_eq_map, ProbOracleComp.runWith_map]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(cfg₀, s₁), hcfg₀, rfl⟩
    rw [← hlaw₁, ProbOracleComp.runWith_map] at hout_mem
    obtain ⟨⟨b, s₁'⟩, hb, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hout_mem
    rcases Prod.mk.inj heq with ⟨hmid, rfl⟩
    exact ⟨b, hb, hmid⟩
  have hpad₂ : ∀ (b : β) (s₁ : State),
      (b, s₁) ∈ (ProbOracleComp.runWith oracle (first a) s).support →
      ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom (t₂' a) (m₂.initialConfig (middle b))) s₁ =
      ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom (t₂ b) (m₂.initialConfig (middle b))) s₁ :=
    fun b s₁ hb => run_interpret_runOracleConfigFrom_eq_of_halted m₂ oracle
      (m₂.initialConfig (middle b)) (ht₂ a State oracle s s₁ b hb) s₁ (hm₂ b State oracle s₁).2
  have hhalt₂_word : ∀ word (b : β) (s₁ : State),
      (b, s₁) ∈ (ProbOracleComp.runWith oracle (first a) s).support →
      middle b = word →
      ∀ final ∈ (ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom (t₂' a) (m₂.initialConfig word)) s₁).support,
        final.1.tapes.state = none := by
    rintro _ b s₁ hb rfl final hfinal
    rw [hpad₂ b s₁ hb] at hfinal
    exact (hm₂ b State oracle s₁).2 final hfinal
  have hhalt₂_open : ∀ result ∈ (ProbOracleComp.runWith oracle
      (m₁.runOracleConfigFrom (t₁ a) (m₁.initialConfig (input a))) s).support,
      ∀ final ∈ (ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom (t₂' a)
          { tapes := Cfg.init m₂.initial result.1.tapes.output,
            channels := result.1.channels }) result.2).support,
        final.1.tapes.state = none := by
    rintro ⟨cfg₀, s₁⟩ hcfg₀ ⟨cfg₁, s₂⟩ hfinal
    obtain ⟨b, hb, hmid⟩ := hmem_word cfg₀ s₁ hcfg₀
    have hmap : ((cfg₁.tapes.output, cfg₁.tapes.state), s₂) ∈ ((ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom (t₂' a)
          { tapes := Cfg.init m₂.initial cfg₀.tapes.output,
            channels := cfg₀.channels }) s₁).map
        (Prod.map (fun c => (c.tapes.output, c.tapes.state)) id)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨(cfg₁, s₂), hfinal, rfl⟩
    rw [hchannels a State oracle s cfg₀ s₁ hcfg₀] at hmap
    obtain ⟨⟨cfg₁', s₂'⟩, hcfg₁', heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
    rcases Prod.mk.inj heq with ⟨houtst, rfl⟩
    rw [← (Prod.mk.inj houtst).2]
    exact hhalt₂_word cfg₀.tapes.output b s₁ hb hmid (cfg₁', s₂') hcfg₁'
  have hstep : 2 * t₁ a + t₂' a + 4 = t₁ a + (t₁ a + 4 + t₂' a) := by omega
  dsimp only
  rw [hstep]
  have hcomp := runWith_oComp m₁ m₂ oracle true (input a) (t₁ a) (t₂' a) s hhalt₁ hhalt₂_open
  refine ⟨?_, ?_⟩
  · have hout := congrArg (PMF.map (Prod.map (fun final => final.tapes.output) id)) hcomp
    conv_rhs => rw [runOracle_eq_map, ProbOracleComp.runWith_map]
    refine Eq.trans ?_ hout.symm
    rw [PMF.map_bind, map_bind, ProbOracleComp.runWith_bind]
    classical
    let cont (p : List Bool × State) : PMF (List Bool × State) :=
      if h : ∃ b, middle b = p.1 then
        ProbOracleComp.runWith oracle (output <$> second (Classical.choose h)) p.2
      else PMF.pure ([], p.2)
    have hcont (b : β) (s₁ : State) :
        cont (middle b, s₁) = ProbOracleComp.runWith oracle (output <$> second b) s₁ := by
      have hex : ∃ b', middle b' = middle b := ⟨b, rfl⟩
      have hchoose : Classical.choose hex = b := middle.injective (Classical.choose_spec hex)
      simp only [cont, hex, ↓reduceDIte, hchoose]
    calc (ProbOracleComp.runWith oracle (first a) s).bind
          (fun bs => ProbOracleComp.runWith oracle (output <$> second bs.1) bs.2)
        = (ProbOracleComp.runWith oracle (first a) s).bind
            (fun bs => cont (middle bs.1, bs.2)) :=
          PMF.bind_congr_on_support _ _ _ fun ⟨b, s₁⟩ _ => (hcont b s₁).symm
      _ = ((ProbOracleComp.runWith oracle (first a) s).map
            (fun bs => (middle bs.1, bs.2))).bind cont := by
          rw [PMF.bind_map]; rfl
      _ = (ProbOracleComp.runWith oracle (middle <$> first a) s).bind cont := by
          rw [ProbOracleComp.runWith_map]; rfl
      _ = (ProbOracleComp.runWith oracle (m₁.runOracle (t₁ a) (input a)) s).bind cont := by
          rw [hlaw₁]
      _ = (ProbOracleComp.runWith oracle
            (m₁.runOracleConfigFrom (t₁ a) (m₁.initialConfig (input a))) s).bind
            (fun r => cont (r.1.tapes.output, r.2)) := by
          rw [runOracle_eq_map, ProbOracleComp.runWith_map, PMF.bind_map]
          rfl
      _ = _ := by
          refine PMF.bind_congr_on_support _ _ _ fun ⟨cfg₀, s₁⟩ hcfg₀ => ?_
          obtain ⟨b, hb, hmid⟩ := hmem_word cfg₀ s₁ hcfg₀
          rw [PMF.map_comp]
          change cont (cfg₀.tapes.output, s₁) =
            PMF.map (Prod.map Prod.fst id ∘
              Prod.map (fun c => (c.tapes.output, c.tapes.state)) id)
              (ProbOracleComp.runWith oracle
                (m₂.runOracleConfigFrom (t₂' a)
                  { tapes := Cfg.init m₂.initial cfg₀.tapes.output,
                    channels := cfg₀.channels }) s₁)
          rw [← PMF.map_comp, hchannels a State oracle s cfg₀ s₁ hcfg₀, PMF.map_comp]
          change cont (cfg₀.tapes.output, s₁) = PMF.map (Prod.map (fun c => c.tapes.output) id)
            (ProbOracleComp.runWith oracle
              (m₂.runOracleConfigFrom (t₂' a) (m₂.initialConfig cfg₀.tapes.output)) s₁)
          rw [← ProbOracleComp.runWith_map, ← runOracle_eq_map, ← hmid, hcont b s₁,
            (hm₂ b State oracle s₁).1, runOracle_eq_map, runOracle_eq_map,
            ProbOracleComp.runWith_map, ProbOracleComp.runWith_map, hpad₂ b s₁ hb]
  · intro final hfinal
    rw [hcomp] at hfinal
    obtain ⟨⟨cfg₀, s₁⟩, hcfg₀, htarget⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨cfg₁, s₂⟩, hcfg₁, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htarget
    change (cfg₁.tapes.state.map Sum.inr).map Sum.inr = none
    rw [hhalt₂_open (cfg₀, s₁) hcfg₀ (cfg₁, s₂) hcfg₁]
    rfl

/-- Sequence a closed halting probabilistic computation `ProbOracleComp.sample (first a)` before
any halting oracle continuation `second`, in `2 * t₁ a + t₂' a + 4` steps. -/
theorem bind_sample_left {first : α → ProbComp β} {second : β → WordOracleComp Operation γ}
    {t₂ : β → ℕ} {t₂' : α → ℕ}
    (hfirst : ComputesInTimeOn input middle t₁ first)
    (hsecond : ComputesOracleInTimeOn middle output t₂ second)
    (ht₂ : ∀ a b, b ∈ (ProbComp.eval (first a)).support → t₂ b ≤ t₂' a) :
    ComputesOracleInTimeOn input output (fun a => 2 * t₁ a + t₂' a + 4)
      (fun a => do
        let b ← ProbOracleComp.sample (first a)
        second b) := by
  obtain ⟨k₁, State₁, hfin₁, m₁, hm₁⟩ := hfirst
  obtain ⟨hops, k₂, State₂, hfin₂, m₂, hm₂⟩ := hsecond
  refine oComp_computesOracleInTimeOn (ofClosed m₁) m₂ (ofClosed_spec m₁ hm₁) hm₂ ?_ ?_
  · intro a State oracle s s' b hb
    rw [ProbOracleComp.runWith_sample, PMF.mem_support_map_iff] at hb
    obtain ⟨b', hb', heq⟩ := hb
    exact (Prod.mk.inj heq).1 ▸ ht₂ a b' hb'
  · intro a State oracle s cfg₀ s₁ hcfg₀
    change (cfg₀, s₁) ∈ (ProbOracleComp.runWith oracle
      ((ofClosed m₁).runOracleConfigFrom (t₁ a)
        { tapes := (m₁.initialConfig (input a)).tapes, channels := fun _ => {} }) s).support
      at hcfg₀
    rw [runWith_runOracleConfigFrom_ofClosed, PMF.mem_support_map_iff] at hcfg₀
    obtain ⟨_, _, heq⟩ := hcfg₀
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    rfl

/-- Sequence a halting oracle computation `first a` before a closed halting continuation
`ProbOracleComp.sample (second b)`, in `2 * t₁ a + t₂' a + 4` steps. -/
theorem bind_sample_right {first : α → WordOracleComp Operation β} {second : β → ProbComp γ}
    {t₂ : β → ℕ} {t₂' : α → ℕ}
    (hfirst : ComputesOracleInTimeOn input middle t₁ first)
    (hsecond : ComputesInTimeOn middle output t₂ second)
    (ht₂ : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      s s' b, (b, s') ∈ (ProbOracleComp.runWith oracle (first a) s).support → t₂ b ≤ t₂' a) :
    ComputesOracleInTimeOn input output (fun a => 2 * t₁ a + t₂' a + 4)
      (fun a => do
        let b ← first a
        ProbOracleComp.sample (second b)) := by
  obtain ⟨hops, k₁, State₁, hfin₁, m₁, hm₁⟩ := hfirst
  obtain ⟨k₂, State₂, hfin₂, m₂, hm₂⟩ := hsecond
  refine oComp_computesOracleInTimeOn m₁ (ofClosed m₂) hm₁ (ofClosed_spec m₂ hm₂) ht₂ ?_
  intro a State oracle s cfg₀ s₁ _
  change (ProbOracleComp.runWith oracle ((ofClosed m₂).runOracleConfigFrom (t₂' a)
      { tapes := (m₂.initialConfig cfg₀.tapes.output).tapes, channels := cfg₀.channels }) s₁).map
      (Prod.map (fun c => (c.tapes.output, c.tapes.state)) id) =
    (ProbOracleComp.runWith oracle ((ofClosed m₂).runOracleConfigFrom (t₂' a)
      { tapes := (m₂.initialConfig cfg₀.tapes.output).tapes, channels := fun _ => {} }) s₁).map
      (Prod.map (fun c => (c.tapes.output, c.tapes.state)) id)
  rw [runWith_runOracleConfigFrom_ofClosed, runWith_runOracleConfigFrom_ofClosed,
    PMF.map_comp, PMF.map_comp]
  rfl

/-- A polynomially bounded halting oracle schedule gives a strict `IsOraclePPTOn` certificate. -/
theorem isOraclePPTOn (ht : PolyBounded (fun a => (input a).length) t)
    (h : ComputesOracleInTimeOn input output t program) :
    IsOraclePPTOn input output program := by
  obtain ⟨c, d, hle⟩ := ht.exists_le
  obtain ⟨hops, k, Control, hfinite, machine, hmachine⟩ := h.mono hle
  exact ⟨hops, k, Control, hfinite, machine, c, d,
    fun a State oracle s => (hmachine a State oracle s).1⟩

end ComputesOracleInTimeOn

/-- A program returning its declared encoding has the same explicit-time halting oracle
certificates. -/
theorem computesOracleInTimeOn_iff_encoded {Operation α β : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool} {t : α → ℕ}
    {program : α → WordOracleComp Operation β} :
    ComputesOracleInTimeOn input output t program ↔
      ComputesOracleInTimeOn input encBits t (fun a => output <$> program a) := by
  simp only [ComputesOracleInTimeOn, encBits, Function.Embedding.coe_refl, id_map]

/-- Lift a closed halting realization to an open oracle realization via `ProbOracleComp.sample`,
preserving the exact step schedule `t`. -/
theorem ComputesInTimeOn.computesOracleInTimeOn {Operation α β : Type} [DecidableEq Operation]
    [Finite Operation] {input : α ↪ List Bool} {output : β ↪ List Bool} {t : α → ℕ}
    {program : α → ProbComp β} (h : ComputesInTimeOn input output t program) :
    ComputesOracleInTimeOn (Operation := Operation) input output t
      (fun a => ProbOracleComp.sample (program a)) := by
  obtain ⟨k, State, hfinite, machine, hmachine⟩ := h
  exact ⟨inferInstance, k, State, hfinite, ofClosed machine, ofClosed_spec machine hmachine⟩

/-- A sampled closed program certified without external channels (`Operation := Empty`) is a closed
halting realization with the exact same step schedule `t`. -/
theorem ComputesOracleInTimeOn.computesInTimeOn {α β : Type}
    {input : α ↪ List Bool} {output : β ↪ List Bool} {t : α → ℕ}
    {program : α → ProbComp β}
    (h : ComputesOracleInTimeOn (Operation := Empty) input output t
      (fun a => ProbOracleComp.sample (program a))) :
    ComputesInTimeOn input output t program := by
  obtain ⟨_, k, Control, hfinite, machine, hmachine⟩ := h
  refine ⟨k, Control, hfinite, machine, fun a => ?_⟩
  obtain ⟨hlaw, hhalt⟩ := hmachine a Unit (fun q => q.1.elim) ()
  refine ⟨?_, ?_⟩
  · have hout := congrArg (PMF.map Prod.fst) hlaw
    rw [← ProbOracleComp.sample_map, ProbOracleComp.runWith_sample,
      runOracle_eq_sample_runClosed, ProbOracleComp.runWith_sample,
      PMF.map_comp, PMF.map_comp, ProbComp.eval_map] at hout
    have hid : (Prod.fst ∘ fun word : List Bool => (word, ())) = id := rfl
    rwa [hid, PMF.map_id, PMF.map_id] at hout
  · intro final hfinal
    apply hhalt (final, ())
    rw [MultiTapePTM.runOracleConfigFrom_empty, ProbOracleComp.runWith_sample]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, hfinal, rfl⟩

end Cslib.Probability

/-- Lift a plain deterministic time-and-space computation to a halting oracle realization with the
exact same step bound `t`. -/
theorem Turing.MultiTapeTM.ComputableInTimeAndSpace.computesOracleInTimeOn
    {Operation α β : Type} [DecidableEq Operation] [Finite Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f input output t s) :
    Cslib.Probability.ComputesOracleInTimeOn (Operation := Operation) input output t
      (fun a => pure (f a)) :=
  (h.computesInTimeOn.computesOracleInTimeOn (Operation := Operation)).congr
    fun _ _ _ _ => by simp

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeTM

/-- Deterministically prepare the input of a halting oracle program in
`2 * tf a + tp (prepare a) + 4` steps. -/
theorem ComputesOracleInTimeOn.preprocess {Operation α β γ : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {tp : β → ℕ} {tf sf : α → ℕ} {program : β → WordOracleComp Operation γ} {prepare : α → β}
    (hprogram : ComputesOracleInTimeOn middle output tp program)
    (hprepare : ComputableInTimeAndSpace prepare input middle tf sf) :
    ComputesOracleInTimeOn input output (fun a => 2 * tf a + tp (prepare a) + 4)
      (fun a => program (prepare a)) := by
  refine (hprogram.bind_sample_left hprepare.computesInTimeOn ?_).congr fun _ _ _ _ => by simp
  intro a b hb
  rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hb
  rw [hb]

/-- Deterministically postprocess every result of a halting oracle program in
`2 * tp a + tf' a + 4` steps. -/
theorem ComputesOracleInTimeOn.map {Operation α β γ : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {tp tf' : α → ℕ} {tf sf : β → ℕ} {program : α → WordOracleComp Operation β} {f : β → γ}
    (hprogram : ComputesOracleInTimeOn input middle tp program)
    (hf : ComputableInTimeAndSpace f middle output tf sf)
    (htf : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      s s' b, (b, s') ∈ (ProbOracleComp.runWith oracle (program a) s).support → tf b ≤ tf' a) :
    ComputesOracleInTimeOn input output (fun a => 2 * tp a + tf' a + 4)
      (fun a => f <$> program a) := by
  refine (hprogram.bind_sample_right hf.computesInTimeOn htf).congr fun _ _ _ _ => ?_
  simp

/-- Postprocess a halting oracle program with a deterministic length-indexed bound under a monotone
step function, using `hprogram.length_le` to bound intermediate encoded words by `tp a`. -/
theorem ComputesOracleInTimeOn.map_ofLength {Operation α β γ : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {tp : α → ℕ} {tf sf : ℕ → ℕ} {program : α → WordOracleComp Operation β} {f : β → γ}
    (hprogram : ComputesOracleInTimeOn input middle tp program)
    (hf : ComputableInTimeAndSpaceOfLength f middle output tf sf)
    (hmono : Monotone tf) :
    ComputesOracleInTimeOn input output (fun a => 2 * tp a + tf (tp a) + 4)
      (fun a => f <$> program a) :=
  hprogram.map hf fun a _ oracle s s' _ hb => hmono (hprogram.length_le a oracle s s' hb)

/-- Issue one bounded-prefix external query `(op, request a)` reading at most `limit a` reply bits,
given a plain deterministic computation preparing `(request a, limit a)`. -/
theorem ComputesOracleInTimeOn.query_take {Operation α : Type} [DecidableEq Operation]
    [Finite Operation] (op : Operation) {input : α ↪ List Bool}
    {request : α → List Bool} {limit : α → ℕ} {tf sf : α → ℕ}
    (hprepare : ComputableInTimeAndSpace (fun a => (request a, limit a))
      input (encPair encBits encUnary) tf sf) :
    ComputesOracleInTimeOn input encBits
      (fun a => 2 * tf a + (4 * (request a).length + 2 * limit a + 6) + 4)
      (fun a => List.take (limit a) <$>
        ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool)
          (op, request a)) :=
  (ComputesOracleInTimeOn.query_take_pair op).preprocess hprepare

/-- **Uniform strict oracle PPT is equivalent to halting oracle realization under a polynomially
bounded step schedule.** The forward direction normalizes any `IsOraclePPTOn` witness via
`IsOraclePPTOn.oraclePhase`; the backward direction pads via `ComputesOracleInTimeOn.mono`. -/
theorem isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn
    {Operation α β : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → WordOracleComp Operation β} :
    IsOraclePPTOn input output program ↔
      ∃ t, PolyBounded (fun a => (input a).length) t ∧
        ComputesOracleInTimeOn input output t program := by
  constructor
  · intro h
    obtain ⟨hops, k, Control, hfinite, machine, c, d, htidy⟩ := h.oraclePhase
    exact ⟨fun a => c * ((input a).length + 1) ^ d,
      PolyBounded.of_forall_le c d (fun _ => le_rfl),
      @of_computesTidily Operation α β _ hops input output _ program
        k Control hfinite machine htidy⟩
  · rintro ⟨t, ht, hcomp⟩
    exact hcomp.isOraclePPTOn ht

/-! ### Joint `(t, q)` properties and parameterized API -/

namespace ComputesOracleInTimeAndQueriesOn

variable {Operation α β γ : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
  {t t₁ t₂ q q₁ q₂ : α → ℕ} {program program' : α → WordOracleComp Operation γ}

/-- Monotonicity in both the step schedule and the query budget. -/
theorem mono (h : ComputesOracleInTimeAndQueriesOn input output t₁ q₁ program)
    (ht : ∀ a, t₁ a ≤ t₂ a) (hq : ∀ a, q₁ a ≤ q₂ a) :
    ComputesOracleInTimeAndQueriesOn input output t₂ q₂ program :=
  ⟨h.1.mono ht, fun a => (h.2 a).mono (hq a)⟩

/-- Deterministic preprocessing updates the step bound while preserving the query budget. -/
theorem preprocess {tp qp : β → ℕ} {tf sf : α → ℕ}
    {program : β → WordOracleComp Operation γ} {prepare : α → β}
    (hprogram : ComputesOracleInTimeAndQueriesOn middle output tp qp program)
    (hprepare : ComputableInTimeAndSpace prepare input middle tf sf) :
    ComputesOracleInTimeAndQueriesOn input output
      (fun a => 2 * tf a + tp (prepare a) + 4) (fun a => qp (prepare a))
      (fun a => program (prepare a)) :=
  ⟨hprogram.1.preprocess hprepare, fun a => hprogram.2 (prepare a)⟩

/-- Deterministic postprocessing updates the step bound while preserving the query budget `q a`. -/
theorem map {tp qp tf' : α → ℕ} {tf sf : β → ℕ}
    {program : α → WordOracleComp Operation β} {f : β → γ}
    (hprogram : ComputesOracleInTimeAndQueriesOn input middle tp qp program)
    (hf : ComputableInTimeAndSpace f middle output tf sf)
    (htf : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      s s' b, (b, s') ∈ (ProbOracleComp.runWith oracle (program a) s).support → tf b ≤ tf' a) :
    ComputesOracleInTimeAndQueriesOn input output (fun a => 2 * tp a + tf' a + 4) qp
      (fun a => f <$> program a) :=
  ⟨hprogram.1.map hf htf, fun a => (OracleComp.isCostBounded_map_iff _ _ _).mpr (hprogram.2 a)⟩

/-- Closed private sampling followed by an oracle continuation preserves the continuation's query
budget bound `q₂' a`. -/
theorem bind_sample_left {first : α → ProbComp β} {second : β → WordOracleComp Operation γ}
    {t₂ q₂ : β → ℕ} {t₂' q₂' : α → ℕ}
    (hfirst : ComputesInTimeOn input middle t₁ first)
    (hsecond : ComputesOracleInTimeAndQueriesOn middle output t₂ q₂ second)
    (ht₂ : ∀ a b, b ∈ (ProbComp.eval (first a)).support → t₂ b ≤ t₂' a)
    (hq₂ : ∀ a b, q₂ b ≤ q₂' a) :
    ComputesOracleInTimeAndQueriesOn input output (fun a => 2 * t₁ a + t₂' a + 4) q₂'
      (fun a => do
        let b ← ProbOracleComp.sample (first a)
        second b) := by
  refine ⟨hsecond.1.bind_sample_left hfirst ht₂, fun a => ?_⟩
  simpa using (ProbOracleComp.IsQueryBounded.sample (first a)).bind
    fun b => (hsecond.2 b).mono (hq₂ a b)

/-- An oracle computation followed by closed private postprocessing preserves the oracle
computation's query budget `q₁ a`. -/
theorem bind_sample_right {first : α → WordOracleComp Operation β} {second : β → ProbComp γ}
    {t₂ : β → ℕ} {t₂' : α → ℕ}
    (hfirst : ComputesOracleInTimeAndQueriesOn input middle t₁ q₁ first)
    (hsecond : ComputesInTimeOn middle output t₂ second)
    (ht₂ : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      s s' b, (b, s') ∈ (ProbOracleComp.runWith oracle (first a) s).support → t₂ b ≤ t₂' a) :
    ComputesOracleInTimeAndQueriesOn input output (fun a => 2 * t₁ a + t₂' a + 4) q₁
      (fun a => do
        let b ← first a
        ProbOracleComp.sample (second b)) := by
  refine ⟨hfirst.1.bind_sample_right hsecond ht₂, fun a => ?_⟩
  simpa using (hfirst.2 a).bind fun b => ProbOracleComp.IsQueryBounded.sample (second b)

end ComputesOracleInTimeAndQueriesOn

namespace ComputesOracleInTime

variable {Operation β : Type} [DecidableEq Operation] {output : β ↪ List Bool}
  {t t₁ t₂ : ℕ → ℕ → ℕ} {program program' : ℕ → List Bool → WordOracleComp Operation β}

/-- Expose the underlying `ComputesOracleInTimeOn` certificate on `encPair encUnary encBits`. -/
theorem on (h : ComputesOracleInTime output t program) :
    ComputesOracleInTimeOn (encPair encUnary encBits) output
      (fun input => t input.1 input.2.length) (fun input => program input.1 input.2) := h

/-- Enlarging a parameterized step schedule preserves halting oracle realization unconditionally. -/
theorem mono (h : ComputesOracleInTime output t₁ program) (hle : ∀ n m, t₁ n m ≤ t₂ n m) :
    ComputesOracleInTime output t₂ program :=
  h.on.mono fun input => hle input.1 input.2.length

/-- Equality of the complete joint output/state semantics preserves parameterized halting
realization. -/
theorem congr (h : ComputesOracleInTime output t program)
    (heq : ∀ n aux (State : Type)
      (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (program n aux) s =
        ProbOracleComp.runWith oracle (program' n aux) s) :
    ComputesOracleInTime output t program' :=
  h.on.congr fun input => heq input.1 input.2

/-- Every execution path of `program n aux` makes at most `t n aux.length` external queries. -/
theorem isQueryBounded (h : ComputesOracleInTime output t program) (n : ℕ) (aux : List Bool) :
    (program n aux).IsQueryBounded (t n aux.length) :=
  h.on.isQueryBounded (n, aux)

/-- Every supported encoded output on `(n, aux)` has length at most `t n aux.length`. -/
theorem length_le (h : ComputesOracleInTime output t program) (n : ℕ) (aux : List Bool)
    {State : Type} (oracle : Operation × List Bool → StateT State PMF (List Bool))
    (s s' : State) {result : β}
    (hresult : (result, s') ∈ (ProbOracleComp.runWith oracle (program n aux) s).support) :
    (output result).length ≤ t n aux.length :=
  h.on.length_le (n, aux) oracle s s' hresult

/-- A polynomially bounded parameterized halting oracle schedule gives `IsOraclePPT`. -/
theorem isOraclePPT (ht : PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) (Function.uncurry t))
    (h : ComputesOracleInTime output t program) :
    IsOraclePPT output program :=
  IsOraclePPTOn.isOraclePPT (h.on.isOraclePPTOn (by growth_poly))

end ComputesOracleInTime

/-- **Parameterized uniform strict oracle PPT is equivalent to `ComputesOracleInTime` under a
polynomially bounded schedule in `n + aux.length`.** -/
theorem isOraclePPT_iff_exists_polyBounded_computesOracleInTime
    {Operation β : Type} [DecidableEq Operation] {output : β ↪ List Bool}
    {program : ℕ → List Bool → WordOracleComp Operation β} :
    IsOraclePPT output program ↔
      ∃ t : ℕ → ℕ → ℕ,
        PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) (Function.uncurry t) ∧
        ComputesOracleInTime output t program := by
  constructor
  · intro h
    obtain ⟨t₀, ht₀, hcomp⟩ := isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn.mp h.on
    obtain ⟨c, d, hle⟩ := ht₀.exists_le
    refine ⟨fun n m => c * 2 ^ d * (n + m + 1) ^ d,
      PolyBounded.of_forall_le (c * 2 ^ d) d (fun p => le_rfl), ?_⟩
    refine hcomp.mono fun input => (hle input).trans ?_
    have hsize : (encPair encUnary encBits input).length + 1 ≤
        2 * (input.1 + input.2.length + 1) := by
      enc_len
    calc c * ((encPair encUnary encBits input).length + 1) ^ d
        ≤ c * (2 * (input.1 + input.2.length + 1)) ^ d :=
          Nat.mul_le_mul_left c (Nat.pow_le_pow_left hsize d)
      _ = c * 2 ^ d * (input.1 + input.2.length + 1) ^ d := by
          rw [Nat.mul_pow, ← Nat.mul_assoc]
  · rintro ⟨t, ht, hcomp⟩
    exact hcomp.isOraclePPT ht

/-- **Parameterized uniform strict oracle PPT is equivalent to `ComputesOracleInTimeAndQueries`
under polynomially bounded time and query schedules.** -/
theorem isOraclePPT_iff_exists_polyBounded_computesOracleInTimeAndQueries
    {Operation β : Type} [DecidableEq Operation] {output : β ↪ List Bool}
    {program : ℕ → List Bool → WordOracleComp Operation β} :
    IsOraclePPT output program ↔
      ∃ t q : ℕ → ℕ → ℕ,
        PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) (Function.uncurry t) ∧
        PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) (Function.uncurry q) ∧
        ComputesOracleInTimeAndQueries output t q program := by
  constructor
  · intro h
    obtain ⟨t, ht, hcomp⟩ := isOraclePPT_iff_exists_polyBounded_computesOracleInTime.mp h
    exact ⟨t, t, ht, ht, hcomp, hcomp.isQueryBounded⟩
  · rintro ⟨t, _, ht, _, hcomp, _⟩
    exact hcomp.isOraclePPT ht

end Cslib.Probability
