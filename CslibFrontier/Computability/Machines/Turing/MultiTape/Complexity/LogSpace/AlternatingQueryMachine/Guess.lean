/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.AlternatingQueryMachine
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Routines
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# The guessing machine of an alternating query machine

The guessing machine `Turing.AlternatingQueryMachine.guess M` of an alternating query machine `M`
is a nondeterministic query machine on the states of `M` paired with a phase. Each step of `M` takes
two of its steps: first a guess of the player of the state, checked against `M.universal` (a
wrong guess halts and rejects), then the move. Its callbacks are computed within linear space when
those of `M` are, so it compiles with `Turing.NondeterministicQueryMachine.exists_routines`.

## Main definitions

* `Turing.AlternatingQueryMachine.guess`: the guessing machine.
* `Turing.AlternatingQueryMachine.encGuessState`: the encoding of its states.

## Main results

* `Turing.AlternatingQueryMachine.guess_step_none`,
  `Turing.AlternatingQueryMachine.guess_step_some_true`: the guess and the move of a live state.
* `Turing.AlternatingQueryMachine.guess_replay`: every replay of the guessing machine visits a
  state of a replay of `M`.
* `Turing.AlternatingQueryMachine.guess_halted_replay`: if every branch of `M` halts within `t`
  steps, every branch of the guessing machine halts within `2 * t` steps.
* `Turing.AlternatingQueryMachine.guess_query_inSpace`,
  `Turing.AlternatingQueryMachine.guess_next_inSpace`,
  `Turing.AlternatingQueryMachine.guess_halted_inSpace`,
  `Turing.AlternatingQueryMachine.guess_accept_inSpace`: the callbacks within linear space, in the
  shape taken by `Turing.NondeterministicQueryMachine.exists_routines`.
-/

@[expose] public section

namespace Turing.AlternatingQueryMachine

open MultiTapeTM

variable {σ : Type*} (M : AlternatingQueryMachine σ)

/-- **The guessing machine** of `M`, on the states of `M` paired with a phase. In phase `none` the
choice `g` is a guess of the player of the state `s`: it leads to phase `some true` when
`g = M.universal s` and to the halted rejecting phase `some false` otherwise. In phase `some true`
the choice is a move of `M`, after which the phase is `none` again. -/
def guess : NondeterministicQueryMachine (σ × Option Bool) where
  init := (M.init, none)
  query p := M.query p.1
  next
    | ((s, none), _, g) => (s, some (g == M.universal s))
    | ((s, some _), r, b) => (M.next (s, r, b), none)
  halted p := p.2 == some false || M.halted p.1
  accept p := p.2 != some false && M.accept p.1

/-- The encoding of the states of the guessing machine: the framed state of `M`, then the phase as a
framed option bit. -/
abbrev encGuessState {σ : Type} (encS : σ ↪ List Bool) : σ × Option Bool ↪ List Bool :=
  encPair encS (encOption encBool)

@[simp]
theorem guess_halted (s : σ) (o : Option Bool) :
    M.guess.halted (s, o) = (o == some false || M.halted s) := rfl

@[simp]
theorem guess_accept (s : σ) (o : Option Bool) :
    M.guess.accept (s, o) = (o != some false && M.accept s) := rfl

/-- **The guess**: at a live state in phase `none`, the choice `g` is checked against the player
of the state. -/
theorem guess_step_none (input : List Bool) {s : σ} (hs : M.halted s = false) (g : Bool) :
    M.guess.step input (s, none) g = (s, some (g == M.universal s)) := by
  have hh : M.guess.halted (s, none) = false := by rw [guess_halted, hs]; rfl
  rw [NondeterministicQueryMachine.step, hh]
  rfl

/-- **The move**: at a live state after a correct guess, the choice `b` is a move of `M`. -/
theorem guess_step_some_true (input : List Bool) {s : σ} (hs : M.halted s = false) (b : Bool) :
    M.guess.step input (s, some true) b = (M.step input s b, none) := by
  have hh : M.guess.halted (s, some true) = false := by rw [guess_halted, hs]; rfl
  simp only [NondeterministicQueryMachine.step, hh, hs, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- One step of the guessing machine keeps the state of `M` or takes one step of `M`. -/
private theorem guess_step_fst (input : List Bool) (s : σ) (p : Option Bool) (b : Bool) :
    (M.guess.step input (s, p) b).1 = s ∨ (M.guess.step input (s, p) b).1 = M.step input s b := by
  cases hs : M.halted s
  · rcases p with _ | _ | _
    · exact .inl (congrArg Prod.fst (M.guess_step_none input hs b))
    · exact .inl (congrArg Prod.fst (NondeterministicQueryMachine.step_of_halted _ _ rfl b))
    · exact .inr (congrArg Prod.fst (M.guess_step_some_true input hs b))
  · exact .inl (congrArg Prod.fst (NondeterministicQueryMachine.step_of_halted _ _
      (by rw [guess_halted, hs, Bool.or_true]) b))

/-- **Replays of the guessing machine follow replays of `M`**: every state the guessing machine
reaches from `(s, p)` pairs a state that `M` reaches from `s` with a phase. -/
theorem guess_replay (input : List Bool) : ∀ (choices : List Bool) (s : σ) (p : Option Bool),
    ∃ (choices' : List Bool) (p' : Option Bool),
      M.guess.replay input choices (s, p) = (M.replay input choices' s, p') := by
  intro choices
  induction choices with
  | nil => exact fun s p => ⟨[], p, rfl⟩
  | cons b choices ih =>
    intro s p
    obtain ⟨choices', p', h⟩ :=
      ih (M.guess.step input (s, p) b).1 (M.guess.step input (s, p) b).2
    rw [NondeterministicQueryMachine.replay_cons]
    rcases M.guess_step_fst input s p b with h₁ | h₁
    · exact ⟨choices', p', h.trans (by rw [h₁])⟩
    · exact ⟨b :: choices', p', h.trans (by rw [h₁, NondeterministicQueryMachine.replay_cons])⟩

/-- **Halting bound of the guessing machine**: if every branch of `M` from `s` halts within `t`
steps, every branch of the guessing machine from `(s, none)` halts within `2 * t` steps. -/
theorem guess_halted_replay {input : List Bool} {s : σ} {t : ℕ}
    (h : ∀ choices : List Bool, t ≤ choices.length → M.halted (M.replay input choices s) = true) :
    ∀ choices : List Bool, 2 * t ≤ choices.length →
      M.guess.halted (M.guess.replay input choices (s, none)) = true := by
  have hof {s : σ} (hs : M.halted s = true) (choices : List Bool) :
      M.guess.halted (M.guess.replay input choices (s, none)) = true := by
    have hh : M.guess.halted (s, none) = true := by rw [guess_halted, hs, Bool.or_true]
    rw [NondeterministicQueryMachine.replay_of_halted _ _ hh, hh]
  induction t generalizing s with
  | zero => exact fun choices _ => hof (h [] le_rfl) choices
  | succ t ih =>
    intro choices hlen
    cases hs : M.halted s
    · rcases choices with _ | ⟨g, _ | ⟨b, rest⟩⟩
      · simp at hlen
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · simp only [List.length_cons] at hlen
        rw [NondeterministicQueryMachine.replay_cons, M.guess_step_none input hs]
        cases g == M.universal s
        · rw [NondeterministicQueryMachine.replay_of_halted _ _
            (rfl : M.guess.halted (s, some false) = true)]
          rfl
        · rw [NondeterministicQueryMachine.replay_cons, M.guess_step_some_true input hs]
          exact ih (fun choices hc => h (b :: choices) (by simp only [List.length_cons]; omega))
            rest (by omega)
    · exact hof hs choices

end Turing.AlternatingQueryMachine

namespace Turing.AlternatingQueryMachine

open MultiTapeTM ComputableInSpace
open NondeterministicQueryMachine (encReadChoice)

variable {σ : Type} {encS : σ ↪ List Bool} (M : AlternatingQueryMachine σ)

/-- The query of the guessing machine, the query of `M`, within linear space in the state. -/
theorem guess_query_inSpace
    (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length) :
    ComputableInSpace M.guess.query (encGuessState encS) encNat
      fun p => (encGuessState encS p).length := by
  have h := budget_comp_linear hquery (fst encS (encOption encBool))
  exact h

/-- Whether a state of the guessing machine has halted, within linear space in the state. -/
theorem guess_halted_inSpace
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length) :
    ComputableInSpace M.guess.halted (encGuessState encS) encBool
      fun p => (encGuessState encS p).length :=
  budget_finite (encC := encBool) (fun q : Option Bool × Bool => q.1 == some false || q.2)
    (budget_prod (snd encS (encOption encBool))
      (budget_comp_linear hhalted (fst encS (encOption encBool))))

/-- Whether a state of the guessing machine accepts, within linear space in the state. -/
theorem guess_accept_inSpace
    (haccept : ComputableInSpace M.accept encS encBool fun s => (encS s).length) :
    ComputableInSpace M.guess.accept (encGuessState encS) encBool
      fun p => (encGuessState encS p).length :=
  budget_finite (encC := encBool) (fun q : Option Bool × Bool => q.1 != some false && q.2)
    (budget_prod (snd encS (encOption encBool))
      (budget_comp_linear haccept (fst encS (encOption encBool))))

/-- The step of the guessing machine, from a state, a read and a choice, within linear space in
the encoded state, read and choice: a guess checked by `M.universal`, or a move of `M`. -/
theorem guess_next_inSpace
    (hnext : ComputableInSpace M.next (encPair encS encReadChoice) encS
      fun p => (encPair encS encReadChoice p).length)
    (huniversal : ComputableInSpace M.universal encS encBool fun s => (encS s).length) :
    ComputableInSpace M.guess.next (encPair (encGuessState encS) encReadChoice)
      (encGuessState encS) fun p => (encPair (encGuessState encS) encReadChoice p).length := by
  have hp := fst (encGuessState encS) encReadChoice
  have hrc := snd (encGuessState encS) encReadChoice
  have hs := fst' hp
  exact (budget_ite (budget_optionIsSome (snd' hp))
    (budget_prod (budget_comp_linear hnext (budget_prod hs hrc))
      (budget_const (encB := encOption encBool) none))
    (budget_prod hs (budget_optionSome
      (budget_finite (encC := encBool) (fun q : Bool × Bool => q.1 == q.2)
        (budget_prod (snd' hrc) (budget_comp_linear huniversal hs)))))).of_enc_eq
    fun ⟨⟨_, o⟩, _, _⟩ => by cases o <;> rfl

end Turing.AlternatingQueryMachine
