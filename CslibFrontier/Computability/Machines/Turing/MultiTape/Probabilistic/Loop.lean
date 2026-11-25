/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryTake
public import CslibFrontier.Languages.Probabilistic.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Tactic.Step
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Simulation

/-!
# Repeating a probabilistic oracle machine until a tape goes blank

`repeatUntilBlank i body` runs `body` repeatedly. After each round it reads the cell under the
head of work tape `i`, without moving a head, and halts if that cell is blank. Every round of a
`Turing.MultiTapePTM.RunsWords` specification ends with all heads on the first cells of their
words, so the loop stops exactly when the word on tape `i` is empty. The body always runs at least
once. Rounds may halt at random times; the remaining rounds start from the halted configuration,
with its tapes, oracle channels and external oracle state.

## Main definitions

* `Turing.MultiTapePTM.repeatUntilBlank`: the looping machine.
* `Turing.MultiTapePTM.RepeatUntilBlank.fromCheck`: the same transition table started at its test.

## Main results

* `Turing.MultiTapePTM.RunsWords.repeatUntilBlank_round`: one round followed by the remaining loop.
* `Turing.MultiTapePTM.RunsWords.repeatUntilBlank`: `rounds + 1` rounds governed by an invariant
  run `OracleComp.iterate rounds step` followed by `last` within `(rounds + 1) * (t + 1)` steps,
  preserving the joint law of the tape words and the external oracle state.

## References

Adapts cslib's `Plumbing/RepeatUntilBlank`, by Christian Reitwiessner, to probabilistic oracle
machines and the joint stateful semantics of `Turing.MultiTapePTM.RunsWords`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeTM

variable {k : ℕ} {State Operation OracleState : Type} {x : List Bool} [DecidableEq Operation]

/-- Clocked runs compose by sequencing their programs. -/
theorem runOracleConfigFrom_add {S : Type}
    (machine : MultiTapePTM k Bool S Operation) (first second : ℕ)
    (cfg : Config k Bool S Operation x) :
    machine.runOracleConfigFrom (first + second) cfg =
      machine.runOracleConfigFrom first cfg >>= machine.runOracleConfigFrom second :=
  MultiTapeMachine.runConfigFrom_add machine _ _ first second cfg

namespace RepeatUntilBlank

/-- Embed an action of the repeated machine, sending its halt to the blank test. -/
def runAction : MultiTapeMachine.Action k Bool State Operation →
    MultiTapeMachine.Action k Bool (State ⊕ Unit) Operation
  | .step action symbol move =>
    .step { action with state := handOver () action.state } symbol move
  | .query op next => .query op (.inl next)

/-- The instruction that writes nothing, moves no head and enters `q`. -/
def idle {S : Type} (q : Option S) : Turing.Action k Bool S :=
  { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := q }

/-- The blank test: halt if the cell under the head of work tape `i` is blank, and otherwise
restart at `initial`, moving no head and writing nothing. -/
def checkAction (i : Fin k) (initial : State) (work : Fin k → Option Bool) :
    MultiTapeMachine.Action k Bool (State ⊕ Unit) Operation :=
  .step (idle ((work i).map fun _ => .inl initial)) (fun _ => none) (fun _ => 0)

end RepeatUntilBlank

open RepeatUntilBlank

/-- `body`, with its halting transitions sent to a test of the cell under the head of work tape
`i`: a blank cell halts the loop, and any other cell restarts `body`. -/
def repeatUntilBlank (i : Fin k) (body : MultiTapePTM k Bool State Operation) :
    MultiTapePTM k Bool (State ⊕ Unit) Operation where
  initial := .inl body.initial
  tr q symbol work answer bit := match q with
    | .inl q => runAction (body.tr q symbol work answer bit)
    | .inr () => checkAction i body.initial work

namespace RepeatUntilBlank

/-- The loop's transition table, started at its blank test. -/
def fromCheck (i : Fin k) (body : MultiTapePTM k Bool State Operation) :
    MultiTapePTM k Bool (State ⊕ Unit) Operation :=
  { repeatUntilBlank i body with initial := .inr () }

/-- A configuration of the repeated machine as one of the loop: a live state `q` becomes `.inl q`
and the halted state becomes the blank test `.inr ()`. -/
def runConfig (cfg : Config k Bool State Operation x) :
    Config k Bool (State ⊕ Unit) Operation x :=
  { cfg with tapes := cfg.tapes.mapState (handOver ()) }

variable (i : Fin k) (body : MultiTapePTM k Bool State Operation)

/-- Starting at the test changes only the initial state, not the clocked program. -/
theorem runOracleConfigFrom_fromCheck (fuel : ℕ)
    (cfg : Config k Bool (State ⊕ Unit) Operation x) :
    (fromCheck i body).runOracleConfigFrom fuel cfg =
      (repeatUntilBlank i body).runOracleConfigFrom fuel cfg :=
  (MultiTapeMachine.runConfigFrom_map (repeatUntilBlank i body) (fromCheck i body) _ _ _ _
    id (fun _ => (id_map _).symm) fuel cfg).trans (id_map _)

/-- While the repeated machine is live, one loop instruction mirrors its complete program. -/
theorem runOracleConfigFrom_one_runConfig (cfg : Config k Bool State Operation x)
    (h : cfg.tapes.state ≠ none) :
    (repeatUntilBlank i body).runOracleConfigFrom 1 (runConfig cfg) =
      runConfig <$> body.runOracleConfigFrom 1 cfg := by
  obtain ⟨state, hs⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (runConfig cfg).tapes.state = some (.inl state) := by
    simp [runConfig, Cfg.mapState, hs]
  dsimp only [runOracleConfigFrom, MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom]
  rw [hstate, hs, show (runConfig cfg).tapes.inputSymbol = cfg.tapes.inputSymbol from rfl,
    show (runConfig cfg).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols from rfl,
    show (runConfig cfg).answerSymbols = cfg.answerSymbols from rfl]
  simp only [bind_map_left, map_bind]
  congr 1
  funext bit
  rw [show (repeatUntilBlank i body).tr (.inl state) cfg.tapes.inputSymbol
    cfg.tapes.workTapeSymbols cfg.answerSymbols bit = runAction (body.tr state
      cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit) from rfl]
  cases body.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit <;>
    simp [runAction, runConfig, Config.step, Config.receive, Turing.Action.apply, Cfg.mapState]

variable (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))

/-- The loop runs a clocked phase of `body` and then continues from its configuration, even when
`body` halts at a random time: an early halt reaches the blank test early, and the extra time is
absorbed because the remaining loop halts within its own clock. -/
theorem run_interpret_runOracleConfigFrom_add (cfg : Config k Bool State Operation x)
    (fuel rest : ℕ) (s : OracleState)
    (hrest : ∀ result ∈ (ProbOracleComp.runWith oracle (body.runOracleConfigFrom fuel cfg)
        s).support,
      ∀ final ∈ (ProbOracleComp.runWith oracle
          ((repeatUntilBlank i body).runOracleConfigFrom rest (runConfig result.1))
          result.2).support,
        final.1.tapes.state = none) :
    ProbOracleComp.runWith oracle
        ((repeatUntilBlank i body).runOracleConfigFrom (fuel + rest) (runConfig cfg)) s =
    (ProbOracleComp.runWith oracle (body.runOracleConfigFrom fuel cfg) s).bind (fun result =>
      ProbOracleComp.runWith oracle
          ((repeatUntilBlank i body).runOracleConfigFrom rest (runConfig result.1)) result.2) := by
  induction fuel generalizing cfg s with
  | zero =>
    simp only [Nat.zero_add, runOracleConfigFrom, MultiTapePTM.runConfigFrom,
      MultiTapeMachine.runConfigFrom_zero, ProbOracleComp.runWith_pure, PMF.pure_bind]
  | succ fuel ih =>
    by_cases hhalt : cfg.tapes.state = none
    · have hpure : body.runOracleConfigFrom (fuel + 1) cfg = pure cfg :=
        MultiTapeMachine.runConfigFrom_halted _ _ _ _ cfg hhalt
      rw [hpure, ProbOracleComp.runWith_pure, PMF.pure_bind, Nat.add_comm (fuel + 1) rest]
      exact run_interpret_runOracleConfigFrom_add_of_halted _ oracle _ rest (fuel + 1) s
        (hrest (cfg, s) (by simp [hpure]))
    · rw [show fuel + 1 + rest = 1 + (fuel + rest) by lia, runOracleConfigFrom_add,
        runOracleConfigFrom_one_runConfig i body cfg hhalt, bind_map_left,
        ProbOracleComp.runWith_bind, show fuel + 1 = 1 + fuel by lia, runOracleConfigFrom_add,
        ProbOracleComp.runWith_bind, PMF.bind_bind]
      apply Probability.PMF.bind_congr_on_support
      rintro ⟨next, s'⟩ hnext
      refine ih _ _ fun r hr => hrest r ?_
      rw [show fuel + 1 = 1 + fuel by lia, runOracleConfigFrom_add, ProbOracleComp.runWith_bind]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨(next, s'), hnext, hr⟩

/-- An instruction that writes nothing and moves no head changes only the control state of a word
configuration. -/
theorem apply_idle_wordsCfg {S : Type} (q q' : Option S) (ws : Fin k → List Bool)
    (out : List Bool) : (idle q).apply (wordsCfg x q' ws out) = wordsCfg x q ws out := by
  tm_step [idle]

omit [DecidableEq Operation] in
/-- Such an instruction also leaves every oracle channel unchanged. -/
theorem step_idle_channels {S : Type} (cfg : Config k Bool S Operation x) (q : Option S) :
    (cfg.step (idle q) (fun _ => none) (fun _ => 0)).channels = cfg.channels := by
  funext op
  simp [Config.step]

end RepeatUntilBlank

open RepeatUntilBlank

/-- At the blank test on an empty word, the loop halts after one instruction. -/
theorem RunsWords.fromCheck_nil (i : Fin k) (body : MultiTapePTM k Bool State Operation)
    {ws : Fin k → List Bool} {out₀ : List Bool} (hi : ws i = []) :
    (fromCheck i body).RunsWords x ws out₀ 1 (pure ()) (fun _ => ws) (fun _ => []) := by
  intro OracleState oracle s cfg htapes hbuf
  have hsym : cfg.tapes.workTapeSymbols i = none := by
    simp [htapes, Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hi]
  dsimp only
  rw [run_interpret_runOracleConfigFrom_succ_step (fromCheck i body) oracle 0 cfg s
      (by rw [htapes]; rfl) (action := idle none) (symbol := fun _ => none) (move := fun _ => 0)
      (fun _ => by simp only [fromCheck, repeatUntilBlank, checkAction, hsym, Option.map_none]),
    show cfg.step (idle none) (fun _ => none) (fun _ => 0) =
        { tapes := wordsCfg x none ws out₀, channels := cfg.channels } from
      Config.ext (by rw [Config.step, htapes, apply_idle_wordsCfg]) (step_idle_channels cfg none)]
  simpa only [runOracleConfigFrom, MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom_zero,
    ProbOracleComp.runWith_pure, PMF.pure_map, List.append_nil, PMF.support_pure,
    Set.mem_singleton_iff, forall_eq, true_and] using hbuf

/-- At the blank test on a non-empty word, the loop restarts its body after one instruction. -/
theorem RunsWords.fromCheck_ne_nil (i : Fin k) {body : MultiTapePTM k Bool State Operation}
    {ws : Fin k → List Bool} {out₀ : List Bool} {t : ℕ} {α : Type}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws' : α → Fin k → List Bool} {emit : α → List Bool} (hi : ws i ≠ [])
    (h : (repeatUntilBlank i body).RunsWords x ws out₀ t program ws' emit) :
    (fromCheck i body).RunsWords x ws out₀ (t + 1) program ws' emit := by
  intro OracleState oracle s cfg htapes hbuf
  obtain ⟨b, rest, hb⟩ := List.exists_cons_of_ne_nil hi
  have hsym : cfg.tapes.workTapeSymbols i = some b := by
    simp [htapes, Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hb]
  dsimp only
  rw [run_interpret_runOracleConfigFrom_succ_step (fromCheck i body) oracle t cfg s
      (by rw [htapes]; rfl) (action := idle (some (.inl body.initial))) (symbol := fun _ => none)
      (move := fun _ => 0)
      (fun _ => by simp only [fromCheck, repeatUntilBlank, checkAction, hsym, Option.map_some]),
    runOracleConfigFrom_fromCheck]
  exact h OracleState oracle s _ (by rw [Config.step, htapes, apply_idle_wordsCfg]; rfl)
    fun op => by simpa [step_idle_channels] using hbuf op

/-- One round of `body`, followed by the loop started at its blank test. The round's final tape
words and emitted output must determine its program value. -/
theorem RunsWords.repeatUntilBlank_round (i : Fin k) {body : MultiTapePTM k Bool State Operation}
    {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t₁ t₂ : ℕ} {α β : Type}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {prog₂ : α → ProbOracleComp (fun _ : Operation × List Bool => List Bool) β}
    {ws₁ : α → Fin k → List Bool} {emit₁ : α → List Bool}
    {ws₂ : α → β → Fin k → List Bool} {emit₂ : α → β → List Bool}
    (hinj : Function.Injective (fun a => (ws₁ a, emit₁ a)))
    (h₁ : body.RunsWords x ws₀ out₀ t₁ prog₁ ws₁ emit₁)
    (h₂ : ∀ a (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s s' : OracleState),
      (a, s') ∈ (ProbOracleComp.runWith oracle prog₁ s).support →
      (fromCheck i body).RunsWords x (ws₁ a) (out₀ ++ emit₁ a) t₂ (prog₂ a) (ws₂ a) (emit₂ a)) :
    (repeatUntilBlank i body).RunsWords x ws₀ out₀ (t₁ + t₂)
      (prog₁ >>= fun a => (fun b => (a, b)) <$> prog₂ a)
      (fun p : α × β => ws₂ p.1 p.2) (fun p : α × β => emit₁ p.1 ++ emit₂ p.1 p.2) := by
  intro OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some body.initial) ws₀ out₀, channels := cfg.channels }
  let f (a : α) : Cfg k Bool State x := wordsCfg x none (ws₁ a) (out₀ ++ emit₁ a)
  have hf : Function.Injective f := fun _ _ heq =>
    hinj (Prod.ext (wordsCfg_injective heq).1 (wordsCfg_injective heq).2)
  have hcheck (mid : Config k Bool State Operation x) (a : α) (hmid : mid.tapes = f a) :
      (runConfig mid).tapes =
        wordsCfg x (some (fromCheck i body).initial) (ws₁ a) (out₀ ++ emit₁ a) := by
    simp only [runConfig, hmid, f, mapState_wordsCfg, handOver_none]
    rfl
  dsimp only
  rw [Config.ext (by rw [htapes]; rfl : cfg.tapes = (runConfig cfg₀).tapes) rfl,
    run_interpret_runOracleConfigFrom_add i body oracle cfg₀ t₁ t₂ s fun ⟨mid, s₁⟩ hmid => by
      obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
      rw [← runOracleConfigFrom_fromCheck]
      exact (h₂ a OracleState oracle s s₁ ha).halted oracle s₁ (runConfig mid)
        (hcheck mid a hmidTapes) hmidBuf]
  refine ⟨law_bind Config.tapes Config.tapes hf
      (fun a b => wordsCfg x none (ws₂ a b) (out₀ ++ (emit₁ a ++ emit₂ a b)))
      (h₁ OracleState oracle s cfg₀ rfl hbuf).1 fun ⟨mid, s₁⟩ hmid => ?_, fun final hfinal op => ?_⟩
  · obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
    have hlaw := ((h₂ a OracleState oracle s s₁ ha) OracleState oracle s₁
      (runConfig mid) (hcheck mid a hmidTapes) hmidBuf).1
    rw [runOracleConfigFrom_fromCheck] at hlaw
    exact ⟨a, hmidTapes, hlaw.trans (congrArg _ (funext fun ⟨_, _⟩ => by simp [List.append_assoc]))⟩
  · obtain ⟨⟨mid, s₁⟩, hmid, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
    rw [← runOracleConfigFrom_fromCheck] at hfinal
    exact ((h₂ a OracleState oracle s s₁ ha) OracleState oracle s₁
      (runConfig mid) (hcheck mid a hmidTapes) hmidBuf).2 final hfinal op

/-- A loop of `rounds + 1` rounds. Round `n < rounds` runs `step s` from the words `ws s` of a
state `s` satisfying `invariant n s`, and leaves a non-empty word on tape `i`; the last round runs
`last s` and leaves tape `i` empty. The loop then runs `OracleComp.iterate rounds step` followed by
`last` within `(rounds + 1) * (t + 1)` steps, preserving the joint law of the tape words and the
external oracle state, and emits nothing. -/
theorem RunsWords.repeatUntilBlank (i : Fin k) {body : MultiTapePTM k Bool State Operation}
    {σ : Type} {ws : σ → Fin k → List Bool} (hws : Function.Injective ws)
    {step last : σ → ProbOracleComp (fun _ : Operation × List Bool => List Bool) σ}
    {out₀ : List Bool} {t rounds : ℕ} {s₀ : σ}
    (invariant : ℕ → σ → Prop) (hbase : invariant 0 s₀)
    (hstep : ∀ n < rounds, ∀ s, invariant n s →
      body.RunsWords x (ws s) out₀ t (step s) ws (fun _ => []))
    (hlast : ∀ s, invariant rounds s → body.RunsWords x (ws s) out₀ t (last s) ws (fun _ => []))
    (hpreserve : ∀ n < rounds, ∀ s, invariant n s →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (s' : σ),
        (s', st') ∈ (ProbOracleComp.runWith oracle (step s)
            st).support → invariant (n + 1) s' ∧ ws s' i ≠ [])
    (hstop : ∀ s, invariant rounds s →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (s' : σ),
        (s', st') ∈ (ProbOracleComp.runWith oracle (last s) st).support → ws s' i = []) :
    (repeatUntilBlank i body).RunsWords x (ws s₀) out₀ ((rounds + 1) * (t + 1))
      (OracleComp.iterate rounds step s₀ >>= last) ws (fun _ => []) := by
  have hinj : Function.Injective (fun s => (ws s, ([] : List Bool))) :=
    fun _ _ h => hws (congrArg Prod.fst h)
  suffices h : ∀ m n s, n + m = rounds → invariant n s →
      (MultiTapePTM.repeatUntilBlank i body).RunsWords x (ws s) out₀ ((m + 1) * (t + 1))
        (OracleComp.iterate m step s >>= last) ws (fun _ => []) from
    h rounds 0 s₀ (Nat.zero_add _) hbase
  intro m
  induction m with
  | zero =>
    rintro n s rfl hs
    simpa only [map_pure, bind_pure_comp, Functor.map_map, OracleComp.iterate_zero, pure_bind,
      Nat.zero_add, Nat.one_mul, id_map'] using
      ((hlast s hs).repeatUntilBlank_round i hinj (prog₂ := fun _ => pure ())
        (ws₂ := fun a _ => ws a) (emit₂ := fun _ _ => []) fun a _ _ _ _ ha => by
          simpa using RunsWords.fromCheck_nil i body (hstop s hs _ _ _ _ a ha)).of_map
        Prod.fst ws (fun _ => [])
  | succ m ih =>
    intro n s hn hs
    rw [show (m + 1 + 1) * (t + 1) = t + ((m + 1) * (t + 1) + 1) by ring,
      OracleComp.iterate_succ_bind, bind_assoc]
    simpa only [map_bind, Functor.map_map, id_map'] using
      ((hstep n (by lia) s hs).repeatUntilBlank_round i hinj
        (prog₂ := fun a => OracleComp.iterate m step a >>= last) (ws₂ := fun _ b => ws b)
        (emit₂ := fun _ _ => []) fun a _ _ _ _ ha => by
          obtain ⟨ha', hne⟩ := hpreserve n (by lia) s hs _ _ _ _ a ha
          simpa using RunsWords.fromCheck_ne_nil i hne (ih (n + 1) a (by lia) ha')).of_map
        Prod.snd ws (fun _ => [])

end Turing.MultiTapePTM
