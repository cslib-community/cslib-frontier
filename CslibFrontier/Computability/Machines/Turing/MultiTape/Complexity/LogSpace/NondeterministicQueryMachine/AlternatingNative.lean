/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Compiler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify

/-!
# Native alternating control for binary-choice query passes

The native machine of `Turing.NondeterministicQueryMachine.Native` runs an initializer, then
rounds of one binary choice followed by a deterministic pass, then a finalizer. Its alternating
counterpart `Turing.NondeterministicQueryMachine.Native.altMachine` has the same instructions and
one more finite register, the *guess register* `Option Bool`. A choice made with an empty register
is recorded in it (a guess); a choice made with a recorded guess is a move, and empties the
register. The choice state is universal exactly when the recorded guess is `true`. No abstract
state is put in native control: the register holds one bit.

This is the native side of the compilation of alternating query machines
(`Turing.AlternatingQueryMachine`): there the abstract machine checks each guess against the player
of its state and rejects a wrong guess, so the move that follows a right guess is made by the
player of the state.
-/

@[expose] public section

namespace Turing.NondeterministicQueryMachine

namespace Native

/-- The guess register after a choice `b`: an empty register records `b` (a guess); a recorded
guess is cleared (the choice was a move). -/
def nextGuess : Option Bool → Bool → Option Bool
  | none, b => some b
  | some _, _ => none

variable {SI SF : Type} {SP : Bool → Type}

/-- The guess register after an instruction at native state `q` under the choice `b`: only the
choice state updates it. -/
def trackGuess : State SI SP SF → Option Bool → Bool → Option Bool
  | .choose, g, b => nextGuess g b
  | _, g, _ => g

/-- The universal states of the alternating native machine: the choice state with the recorded
guess `true`. -/
def isUniversal : State SI SP SF × Option Bool → Bool
  | (.choose, some true) => true
  | _ => false

variable {k : ℕ} (I : MultiTapeTM k Bool SI) (P : (b : Bool) → MultiTapeTM k Bool (SP b))
  (F : MultiTapeTM k Bool SF) (C : Fin k)

/-- The deterministic machine of the move `b` of the alternating native machine: the native
instruction under the choice `b`, with the guess register updated by `trackGuess`. -/
noncomputable def guessTM (b : Bool) : MultiTapeTM k Bool (State SI SP SF × Option Bool) :=
  MultiTapeTM.ofTr (.init I.q₀, none) fun p input work =>
    relabelAction (Option.map (·, trackGuess p.1 p.2 b)) (instruction I P F C p.1 input work b)

/-- **The alternating native machine**: the native machine with a guess register, whose choice
state is universal exactly when the recorded guess is `true`. -/
noncomputable def altMachine : MultiTapeATM k Bool (State SI SP SF × Option Bool) :=
  MultiTapeATM.ofTMs (guessTM I P F C) isUniversal

end Native

namespace Routines

variable {α σ : Type} {M : NondeterministicQueryMachine σ} {start : α → σ}
  {enc : α ↪ List Bool} {S : α → ℕ} (R : Routines M start enc S)

/-- The compiled alternating native machine of the routines. -/
noncomputable abbrev atm : MultiTapeATM R.k Bool (Native.State R.SI R.SP R.SF × Option Bool) :=
  Native.altMachine R.I R.P R.F R.C

/-- The configuration of the alternating native machine at the boundary of a round: the abstract
state `s` and its continuation flag on the work tapes, the guess register `g`, and native control
at the choice state, or at the finalizer when `s` has halted. -/
def boundaryCfg (a : α) (s : σ) (g : Option Bool) :
    Cfg R.k Bool (Native.State R.SI R.SP R.SF × Option Bool) (enc a) :=
  wordsCfg (enc a) (some (if M.halted s then .finish R.F.q₀ else .choose, g))
    (R.boundary s (!M.halted s)) []

end Routines

end Turing.NondeterministicQueryMachine
