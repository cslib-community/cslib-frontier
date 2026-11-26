/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.CoinFixing
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Configuration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Deterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Counting the accepting coins in polynomial space

This file computes, for a verifier machine, the number of coin values whose programs accept after
a history (`Cslib.Complexity.Interaction.accepted`), within space polynomial in the input and the
history, and in exponential time.

* A replay keeping only whether it is still live
  (`Cslib.Complexity.Interaction.aliveStep`) decides whether the program of given coins accepts
  after a history (`Cslib.Complexity.Interaction.accepts_eq_true_iff`), in polynomial time
  (`Cslib.Complexity.Interaction.computableInPolyTime_accepts`): it folds one instruction per
  coin over the configuration of the machine, whose storage grows by a bounded amount per
  instruction.
* The coin values are enumerated by the binary counter of the shared streaming count
  `Cslib.Complexity.streamAcceptCount`, and the accepting ones are counted with a binary accumulator
  (`Cslib.Complexity.Interaction.countAccepts`,
  `Cslib.Complexity.Interaction.countAccepts_eq_accepted`), within polynomial space
  (`Turing.MultiTapeTM.ComputableInPolySpace`,
  `Cslib.Complexity.Interaction.computableInPolySpace_countAccepts`).

## Main definitions

* `Cslib.Complexity.Interaction.accepts`: whether the program of given coins accepts.
* `Cslib.Complexity.Interaction.countAccepts`: the number of accepting coin values.

## Main results

* `Cslib.Complexity.Interaction.computableInPolyTime_accepts`: acceptance in polynomial time.
* `Cslib.Complexity.Interaction.countAccepts_eq_accepted`: the count of accepting coin values.
* `Cslib.Complexity.Interaction.computableInPolySpace_countAccepts`: the count in polynomial
  space.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

namespace Interaction

/-! ### A live replay -/

/-- Histories, encoded as lists of pairs of words. -/
abbrev encHistory : History ↪ List Bool := encList (encPair encBits encBits)

variable {k : ℕ} {Control Operation Entry : Type} [DecidableEq Operation] [Inhabited Entry]
  (matchOp : Operation → Entry → Bool) (entryPair : Entry → List Bool × List Bool)
  (M : MultiTapePTM k Bool Control Operation)

variable (k Control Operation Entry) in
/-- The state of a replay that only records whether it is still live: the configuration, the rest
of the history and liveness. -/
abbrev AliveState := MultiTapeMachine.FiniteConfig k Bool Control Operation × List Entry × Bool

/-- The instruction of `M` in the configuration `cfg` with the coin `b`, unless it has halted. -/
def instruction (cfg : MultiTapeMachine.FiniteConfig k Bool Control Operation) (b : Bool) :
    Option (MultiTapeMachine.Action k Bool Control Operation) :=
  cfg.tapes.state.map fun c =>
    M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b

/-- Answer a request on the channel `op` from the history, moving to the control state `next`, or
stop when the history is exhausted or sends another message. -/
def answerFromHistory (t : ℕ) (op : Operation) (next : Control)
    (s : AliveState k Control Operation Entry) : AliveState k Control Operation Entry :=
  let ⟨cfg, rest, _⟩ := s
  if rest.isEmpty then (cfg, rest, false)
  else if matchOp op (rest.headD default) &&
      (entryPair (rest.headD default)).1 == (cfg.channels op).1 then
    (cfg.receive op next ((entryPair (rest.headD default)).2.take t), rest.tail, true)
  else (cfg, rest, false)

/-- The live replay step by its liveness and instruction. -/
def taggedStep (t : ℕ) :
    Bool × Option (MultiTapeMachine.Action k Bool Control Operation) →
      AliveState k Control Operation Entry → AliveState k Control Operation Entry
  | (false, _), s => s
  | (true, none), s => s
  | (true, some (.step action symbol move)), s =>
    let ⟨cfg, rest, _⟩ := s
    (cfg.step action symbol move, rest, true)
  | (true, some (.query op next)), s => answerFromHistory matchOp entryPair t op next s

/-- One instruction of a live replay: `taggedStep` dispatched by liveness and `instruction`. -/
def aliveStep (t : ℕ) (s : AliveState k Control Operation Entry) (b : Bool) :
    AliveState k Control Operation Entry :=
  let ⟨cfg, _, live⟩ := s
  taggedStep matchOp entryPair t (live, instruction M cfg b) s

/-- The live replay of `M` on the input `x` with the coins `r` against the history `h`, its replies
truncated to the number of coins. -/
def aliveRun (x r : List Bool) (h : List Entry) : AliveState k Control Operation Entry :=
  r.foldl (aliveStep matchOp entryPair M r.length)
    (MultiTapeMachine.FiniteConfig.init M.initial x, h, true)

/-- Whether the program of the coins `r` accepts after the history `h`: the replay is live, has
consumed the whole history and has output `[true]`. -/
def accepts (x r : List Bool) (h : List Entry) : Bool :=
  let ⟨cfg, rest, live⟩ := aliveRun matchOp entryPair M x r h
  live && rest.isEmpty && decide (cfg.tapes.output = [true])

theorem aliveStep_of_false (t : ℕ)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control Operation) (h : List Entry) (b : Bool) :
    aliveStep matchOp entryPair M t (cfg, h, false) b = (cfg, h, false) := rfl

theorem foldl_aliveStep_false (t : ℕ) (l : List Bool)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control Operation) (h : List Entry) :
    l.foldl (aliveStep matchOp entryPair M t) (cfg, h, false) = (cfg, h, false) := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

section SingleProver

variable (MUnit : MultiTapePTM k Bool Control Unit)

/-- For a single-prover machine, `aliveStep` is `replayStep` where a failure stops the replay. -/
private theorem aliveStep_eq_replayStep (t : ℕ)
    (s : AliveState k Control Unit (List Bool × List Bool)) (b : Bool) :
    aliveStep (fun _ _ => true) id MUnit t s b =
      if s.2.2 then
        match replayStep MUnit t (s.1, s.2.1) b with
        | .ok p => (p.1, p.2, true)
        | .error _ => (s.1, s.2.1, false)
      else s := by
  obtain ⟨cfg, rest, _ | _⟩ := s
  · rfl
  · simp only [aliveStep, instruction, replayStep, ite_true]
    cases cfg.tapes.state with
    | none => rfl
    | some c =>
      simp only [Option.map_some]
      cases MUnit.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
      | step => rfl
      | query op next =>
        simp only [taggedStep, answerFromHistory, Bool.true_and, id_eq]
        cases rest with
        | nil => rfl
        | cons e rest =>
          obtain ⟨m, y⟩ := e
          simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.headD_cons,
            List.tail_cons, beq_iff_eq]
          split_ifs with hm <;> simp

private theorem foldl_bind_error {α β γ : Type*} (f : β → γ → Except α β) (l : List γ) (e : α) :
    l.foldl (fun (acc : Except α β) x => acc.bind fun b => f b x) (.error e) = .error e := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- The live replay follows the replay while it succeeds, and freezes at the failing configuration
on the first error (recording the channel message when pausing on an empty history). -/
private theorem foldl_aliveStep (t : ℕ) (l : List Bool)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control Unit) (h : History) :
    match l.foldl (fun acc b => Except.bind acc fun p => replayStep MUnit t p b) (.ok (cfg, h))
    with
    | .ok p => l.foldl (aliveStep (fun _ _ => true) id MUnit t) (cfg, h, true) = (p.1, p.2, true)
    | .error e =>
      (l.foldl (aliveStep (fun _ _ => true) id MUnit t) (cfg, h, true)).2.2 = false ∧
      (∀ m, e = some m →
        ((l.foldl (aliveStep (fun _ _ => true) id MUnit t) (cfg, h, true)).1.channels ()).1
          = m) := by
  induction l generalizing cfg h with
  | nil => rfl
  | cons b l ih =>
    have hbind : (Except.ok (cfg, h)).bind (fun p => replayStep MUnit t p b) =
        replayStep MUnit t (cfg, h) b := rfl
    simp only [List.foldl_cons, aliveStep_eq_replayStep, ite_true, hbind]
    rcases hr : replayStep MUnit t (cfg, h) b with e | ⟨cfg', h'⟩
    · simp only [foldl_bind_error, foldl_aliveStep_false, true_and]
      rintro m rfl
      unfold replayStep at hr
      cases hst : cfg.tapes.state with
      | none => simp [hst] at hr
      | some c =>
        simp only [hst] at hr
        cases htr : MUnit.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols b with
        | step => simp [htr] at hr
        | query op next =>
          cases h with
          | nil => simpa [htr] using hr
          | cons _ _ => simp only [htr] at hr; split_ifs at hr; cases hr
    · exact ih cfg' h'

private theorem aliveRun_spec (x r : List Bool) (h : History) :
    match simulate MUnit r.length x r h with
    | .ok p => aliveRun (fun _ _ => true) id MUnit x r h = (p.1, p.2, true)
    | .error e =>
      (aliveRun (fun _ _ => true) id MUnit x r h).2.2 = false ∧
      (∀ m, e = some m → ((aliveRun (fun _ _ => true) id MUnit x r h).1.channels ()).1 = m) :=
  foldl_aliveStep MUnit r.length r (MultiTapeMachine.FiniteConfig.init MUnit.initial x) h

/-- When the replay succeeds on `x`, `r`, `h`, the live replay stops at the same state and stays
live. -/
theorem aliveRun_of_simulate_ok {x r : List Bool} {h : History}
    {p : MultiTapeMachine.FiniteConfig k Bool Control Unit × History}
    (hsim : simulate MUnit r.length x r h = .ok p) :
    aliveRun (fun _ _ => true) id MUnit x r h = (p.1, p.2, true) := by
  have hrun := aliveRun_spec MUnit x r h
  rwa [hsim] at hrun

/-- When the replay pauses waiting for a reply to `m`, the live replay stops inactive with `m` on
channel `()`. -/
theorem aliveRun_of_simulate_error_some {x r : List Bool} {h : History} {m : List Bool}
    (hsim : simulate MUnit r.length x r h = .error (some m)) :
    ∃ cfg rem, aliveRun (fun _ _ => true) id MUnit x r h = (cfg, rem, false) ∧
      (cfg.channels ()).1 = m := by
  have hrun := aliveRun_spec MUnit x r h
  rw [hsim] at hrun
  exact ⟨_, _, Prod.ext rfl (Prod.ext rfl hrun.1), hrun.2 m rfl⟩

/-- **The live replay decides acceptance**: `accepts` holds exactly when the program of the coins
accepts after the history. -/
theorem accepts_eq_true_iff (x r : List Bool) (h : History) :
    accepts (fun _ _ => true) id MUnit x r h = true ↔
      outcome (coinProgram MUnit r.length x r) h = .done true := by
  have hrun := aliveRun_spec MUnit x r h
  rw [outcome_coinProgram]
  unfold accepts
  rcases hsim : simulate MUnit r.length x r h with e | ⟨cfg, rest⟩ <;> rw [hsim] at hrun
  · simp only [hrun.1, Bool.false_and, Bool.false_eq_true, false_iff]
    rcases e with _ | m <;> simp [Except.map, replayOutcome]
  · rw [hrun]
    cases rest <;> simp [Except.map, replayOutcome]

/-- `accepts_eq_true_iff` for any number of coins equal to the length of the coins. -/
private theorem accepts_eq_true_iff_of_length {x r : List Bool} {t : ℕ} (hr : r.length = t)
    (h : History) :
    accepts (fun _ _ => true) id MUnit x r h = true ↔
      outcome (coinProgram MUnit t x r) h = .done true := by
  subst hr
  exact accepts_eq_true_iff MUnit x r h

end SingleProver

/-! ### The live replay in polynomial time -/

section PolyTime

open ComputableInPolyTime

variable [Finite Control] [Fintype Operation] {encEntry : Entry ↪ List Bool}
  (hmatch : ∀ op, ComputableInPolyTime (matchOp op) encEntry encBool)
  (hpair : ComputableInPolyTime entryPair encEntry (encPair encBits encBits))

/-- Live replay states, encoded by their fields. -/
noncomputable abbrev encAliveState (encEntry : Entry ↪ List Bool) :
    AliveState k Control Operation Entry ↪ List Bool :=
  encPair encFiniteConfig (encPair (encList encEntry) encBool)

omit [DecidableEq Operation] in
/-- The instruction is polynomial-time: it reads finitely many observations. -/
theorem computableInPolyTime_instruction :
    ComputableInPolyTime
      (fun p : MultiTapeMachine.FiniteConfig k Bool Control Operation × Bool =>
        instruction M p.1 p.2) (encPair encFiniteConfig encBool)
      (encFinite (Option (MultiTapeMachine.Action k Bool Control Operation))) := by
  have hobs : ComputableInPolyTime
      (fun p : MultiTapeMachine.FiniteConfig k Bool Control Operation × Bool =>
        (p.1.tapes.state, p.1.tapes.inputSymbol, p.1.tapes.workTapeSymbols, p.1.answerSymbols, p.2))
      (encPair encFiniteConfig encBool)
      (encPair (encFinite (Option Control)) (encPair (encFinEnum (Option Bool))
        (encPair (encFinEnum (Fin k → Option Bool)) (encPair (encFinite (Operation → Option Bool))
          encBool)))) := by
    fun_prop
  exact ((of_finite fun obs : Option Control × Option Bool × (Fin k → Option Bool) ×
      (Operation → Option Bool) × Bool => obs.1.map fun c =>
        M.tr c obs.2.1 obs.2.2.1 obs.2.2.2.1 obs.2.2.2.2).comp hobs).of_enc_eq fun _ => rfl

include hmatch hpair in
/-- Answering from the history is polynomial-time. -/
private theorem computableInPolyTime_answerFromHistory (op : Operation) (next : Control) :
    ComputableInPolyTime
      (fun p : (ℕ × AliveState k Control Operation Entry) × Bool =>
        answerFromHistory matchOp entryPair p.1.1 op next p.1.2)
      (encPair (encPair encUnary (encAliveState encEntry)) encBool)
      (encAliveState encEntry) := by
  fun_prop [answerFromHistory]

include hmatch hpair in
/-- **A step of the live replay is polynomial-time.** -/
private theorem computableInPolyTime_aliveStep :
    ComputableInPolyTime
      (fun p : (ℕ × AliveState k Control Operation Entry) × Bool =>
        aliveStep matchOp entryPair M p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encAliveState encEntry)) encBool)
      (encAliveState encEntry) := by
  unfold aliveStep
  refine finite_cases (tag := fun p : (ℕ × AliveState k Control Operation Entry) × Bool =>
      (p.1.2.2.2, instruction M p.1.2.1 p.2))
    (branch := fun tag p => taggedStep matchOp entryPair p.1.1 tag p.1.2)
    (tagEncoding := encPair encBool (encFinite (Option (MultiTapeMachine.Action k Bool Control
      Operation)))) ?_ ?_
  · have h := computableInPolyTime_instruction M
    fun_prop
  · intro tag
    match tag with
    | (false, _) | (true, none) => exact (fst _ _).snd'
    | (true, some (.step action symbol move)) => fun_prop [taggedStep]
    | (true, some (.query op next)) =>
      exact computableInPolyTime_answerFromHistory matchOp entryPair hmatch hpair op next

omit [Finite Control] [Fintype Operation] in
/-- A step of the live replay grows the storage by a bounded amount and consumes the history. -/
private theorem aliveStep_spaceBound {n i t : ℕ} {h : List Entry}
    {s : AliveState k Control Operation Entry}
    (hs : MultiTapeMachine.FiniteConfig.SpaceBound n i t s.1 ∧ s.2.1 <:+ h) (b : Bool) :
    MultiTapeMachine.FiniteConfig.SpaceBound n (i + 1) t
      (aliveStep matchOp entryPair M t s b).1 ∧
      (aliveStep matchOp entryPair M t s b).2.1 <:+ h := by
  obtain ⟨cfg, rest, _ | _⟩ := s
  · exact ⟨hs.1.mono le_rfl (by lia) le_rfl, hs.2⟩
  · dsimp only at hs ⊢
    obtain ⟨hspace, hsuffix⟩ := hs
    rcases hst : cfg.tapes.state with _ | c
    · simp only [aliveStep, instruction, hst, Option.map_none, taggedStep]
      exact ⟨hspace.mono le_rfl (by lia) le_rfl, hsuffix⟩
    · rcases htr : M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
        ⟨action, symbol, move⟩ | ⟨op, next⟩
      · simp only [aliveStep, instruction, hst, Option.map_some, htr, taggedStep]
        exact ⟨hspace.step action symbol move, hsuffix⟩
      · simp only [aliveStep, instruction, hst, Option.map_some, htr, taggedStep,
          answerFromHistory]
        cases rest with
        | nil => exact ⟨hspace.mono le_rfl (by lia) le_rfl, hsuffix⟩
        | cons e rest =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.headD_cons,
            List.tail_cons]
          by_cases hcond : (matchOp op e && (entryPair e).1 == (cfg.channels op).1) = true <;>
            simp only [hcond, ↓reduceIte]
          · exact ⟨hspace.receive op next _ (List.length_take_le _ _),
              (List.suffix_cons _ _).trans hsuffix⟩
          · exact ⟨hspace.mono le_rfl (by lia) le_rfl, hsuffix⟩

include hmatch hpair in
/-- **The live replay is polynomial-time** in the input, the coins and the history. -/
theorem computableInPolyTime_aliveRun :
    ComputableInPolyTime (fun p : List Bool × List Bool × List Entry =>
      aliveRun matchOp entryPair M p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits (encList encEntry)))
      (encAliveState encEntry) := by
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  unfold aliveRun
  refine (foldlWith_spec (par := fun p : List Bool × List Bool × List Entry => p.2.1.length)
    (list := fun p => p.2.1)
    (init := fun p => (MultiTapeMachine.FiniteConfig.init M.initial p.1, p.2.2, true))
    (step := aliveStep matchOp entryPair M) (encP := encUnary) (encA := encBool) (encL := encBits)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (computableInPolyTime_aliveStep matchOp entryPair M hmatch hpair)
    (fun p consumed s => MultiTapeMachine.FiniteConfig.SpaceBound p.1.length consumed.length
      p.2.1.length s.1 ∧ s.2.1 <:+ p.2.2)
    (fun p => ⟨MultiTapeMachine.FiniteConfig.spaceBound_init _ _ _, List.suffix_refl _⟩)
    (fun p consumed s b _ hs => by simpa using aliveStep_spaceBound matchOp entryPair M hs b)
    (size := fun p => 2 * cf * (3 *
      (encPair encBits (encPair encBits (encList encEntry)) p).length + 1) +
      2 * (encPair encBits (encPair encBits (encList encEntry)) p).length + 3)
    (by growth_poly)
    (fun p consumed s hprefix hs => ?_)).1
  have hcfg := hcf _ _ _ _ hs.1
  have hhist := length_encList_sublist encEntry hs.2.sublist
  have hcons : consumed.length ≤ p.2.1.length := hprefix.length_le
  simp only [encAliveState, length_encPair, encBool_apply, List.length_singleton, encBits_apply]
    at hcfg hhist ⊢
  have hcfg' := Nat.mul_le_mul_left 2 (hcfg.trans (Nat.mul_le_mul_left cf
    (show p.1.length + consumed.length + p.2.1.length + 1 ≤ 3 * (2 * p.1.length + 1 +
      (2 * p.2.1.length + 1 + (encList encEntry p.2.2).length)) + 1 by lia)))
  rw [← Nat.mul_assoc] at hcfg'
  lia

omit [Fintype Operation] in
include hmatch hpair in
/-- **Acceptance is polynomial-time** in the input, the coins and the history. -/
theorem computableInPolyTime_accepts [Finite Operation] :
    Turing.MultiTapeTM.ComputableInPolyTime (fun p : List Bool × List Bool × List Entry =>
      accepts matchOp entryPair M p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits (encList encEntry))) encBool := by
  cases nonempty_fintype Operation
  have := computableInPolyTime_aliveRun matchOp entryPair M (encEntry := encEntry) hmatch hpair
  fun_prop [accepts]

end PolyTime

/-! ### Counting the accepting coins -/

section Count

variable {α : Type} (MUnit : MultiTapePTM k Bool Control Unit) (enc : α ↪ List Bool) (fuel : α → ℕ)

/-- The number of accepting values of `fuel a` coins after the history `h`, counted by trying the
coins one after another with a binary counter (`Cslib.Complexity.streamAcceptCount`). -/
def countAccepts (q : α × History) : ℕ :=
  streamAcceptCount
    (fun p : (α × History) × List Bool =>
      let ⟨⟨a, h⟩, r⟩ := p
      accepts (fun _ _ => true) id MUnit (enc a) r h)
    q (fuel q.1)

/-- **The count of accepting coins**: `countAccepts` is the number of coin values of `fuel a` coins
whose programs accept after the history. -/
theorem countAccepts_eq_accepted (q : α × History) :
    countAccepts MUnit enc fuel q = accepted (coinFamily MUnit (fuel q.1) (enc q.1)) q.2 := by
  rw [countAccepts, streamAcceptCount_eq_acceptCount, acceptCount, accepted]
  exact congrArg Finset.card (Finset.filter_congr fun r _ =>
    accepts_eq_true_iff_of_length MUnit (List.length_ofFn (f := r)) q.2)

/-- **The count of accepting coins within polynomial space**, in the input and the history, for a
number of coins computed in polynomial time. -/
theorem computableInPolySpace_countAccepts [Finite Control]
    (hfuel : Turing.MultiTapeTM.ComputableInPolyTime fuel enc encUnary) :
    Turing.MultiTapeTM.ComputableInPolySpace (countAccepts MUnit enc fuel) (encPair enc encHistory)
      encNat := by
  have hacc := computableInPolyTime_accepts (fun _ _ => true) id MUnit
    (encEntry := encPair encBits encBits) (fun _ => .const true) .id'
  have hverify : ComputableInPolyTime
      (fun p : (α × History) × List Bool =>
        accepts (fun _ _ => true) id MUnit (enc p.1.1) p.2 p.1.2)
      (encPair (encPair enc encHistory) encBits) encBool := by fun_prop
  exact (computableInPolySpace_acceptCount (.of_polyTime hverify)
    (hfuel.comp (.fst _ _))).congr fun q => (streamAcceptCount_eq_acceptCount _ q _).symm

end Count

end Interaction

end Cslib.Complexity
