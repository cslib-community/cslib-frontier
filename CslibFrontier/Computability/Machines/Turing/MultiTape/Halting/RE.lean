/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec
public import Mathlib.Computability.RE

/-!
# Recursively enumerable sets

A set is recursively enumerable (`Turing.MultiTapeTM.IsRE`) with respect to an encoding when some
machine with a binary alphabet and finitely many states halts on the encoding of exactly its
elements: the Turing-recognizable sets of [Sipser, Definition 3.5][Sipser2013], with halting in
place of acceptance. They are the right-hand side of `MIP* = RE`, whose
left-hand side is `Cslib.Complexity.MIPStar`.

The machine's run is partial recursive (`Turing.MultiTapeTM.partrec_eval`), so a recursively
enumerable set is recursively enumerable in Mathlib's sense, `REPred`, whenever its encoding is
computable (`Turing.MultiTapeTM.IsRE.rePred`).

## Main definitions

* `Turing.MultiTapeTM.IsRE`: recursive enumerability by the halting of a native machine.

## Main results

* `Turing.MultiTapeTM.IsRE.rePred`, `Turing.MultiTapeTM.IsRE.rePred_bits`: the bridge to Mathlib's
  `REPred`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α : Type*}

/-- `L` is recursively enumerable with respect to the encoding `enc`: some machine with a binary
alphabet and finitely many states halts on `enc a` exactly when `a ∈ L`. -/
def IsRE (L : Set α) (enc : α ↪ List Bool) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ∀ a, a ∈ L ↔ tm.Halts (enc a)

/-- A set that is recursively enumerable with respect to a computable encoding is recursively
enumerable in Mathlib's sense. -/
theorem IsRE.rePred [Primcodable α] {L : Set α} {enc : α ↪ List Bool} (hL : IsRE L enc)
    (henc : Computable enc) : REPred (· ∈ L) := by
  obtain ⟨k, State, _, tm, h⟩ := hL
  exact ((tm.partrec_eval.comp henc).dom_re).of_eq fun a => by
    rw [dom_eval_iff_halts, ← h]

/-- A language that is recursively enumerable with respect to `encBits` is recursively enumerable
in Mathlib's sense. -/
theorem IsRE.rePred_bits {L : Set (List Bool)} (hL : IsRE L encBits) : REPred (· ∈ L) :=
  hL.rePred Computable.id

end Turing.MultiTapeTM
