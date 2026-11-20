/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Output relations of nondeterministic machines

A halted computation contributes its output payload if the output starts with the bit `true`.
Thus `[true]` represents a successful empty payload, and an input is outside the domain
when no path contributes a payload. The same machine can produce several distinct payloads.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State α : Type}

/-- A computation of `M` on `input` halts with the acceptance tag followed by `output`. -/
def Produces (M : MultiTapeNTM k Bool State) (input output : List Bool) : Prop :=
  ∃ path : M.ComputationPath input, path.last.Halted ∧ path.last.output = true :: output

/-- One finite nondeterministic machine realizes the output relation and has a polynomial clock
depending only on the encoded input length. A path that gets stuck contributes no output. -/
def ComputesRelationInPolyTime (R : α → List Bool → Prop) (enc : α ↪ List Bool) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapeNTM k Bool State)
    (clock : Polynomial ℕ), ∀ a,
      M.RunsInTime (enc a) (clock.eval (enc a).length) ∧ ∀ w, R a w ↔ M.Produces (enc a) w

/-- Under the decision convention, acceptance is successful production of the empty word. -/
theorem produces_nil_iff_accepts (M : MultiTapeNTM k Bool State) (input : List Bool) :
    M.Produces input [] ↔ M.Accepts input := Iff.rfl

end Turing.MultiTapeNTM
