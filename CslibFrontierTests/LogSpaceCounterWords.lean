/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words

/-! # Consequences of the counter-program word operations

The logspace-to-polynomial-time bridge applied to the new list lookup.
-/

public section

namespace Turing.MultiTapeTM.Tests.LogSpaceCounterWords

/-- Lookup in a list of bit strings is computable in polynomial time, by the (tidy)
logspace-to-polynomial-time bridge. -/
example : ComputableTidilyInPolyTime (fun p : List (List Bool) × ℕ => p.1[p.2]?)
    (encPair (encList encBits) encUnary) (encOption encBits) :=
  (ComputableInLogSpace.getElem? encBits).computableTidilyInPolyTime

-- Canonical output boundary: missing entries, including an empty input list, carry a tag.
example : encOption encBits (([] : List (List Bool))[0]?) = [false] := rfl
example : encOption encBits ([[true]][1]?) = [false] := rfl
example : encOption encBits ([([] : List Bool)][0]?) = [true] := rfl

-- Exercise the transducer, rather than only the requested output encoding. The fuel
-- includes the halt; halt instructions emit no further bits.
private def lookupOutput (l : List (List Bool)) (k : ℕ) : List Bool :=
  (List.range 64).flatMap fun i => CounterProgram.Words.lookupProgram.emitted
    (CounterProgram.Words.lookupProgram.run (encPair (encList encBits) encUnary (l, k)) i)

example : lookupOutput [] 0 = [false] := by decide
example : lookupOutput [[true]] 1 = [false] := by decide
example : lookupOutput [[]] 0 = [true] := by decide

-- The actual missing branch emits the tag and then halts, without changing registers.
example : CounterProgram.Words.lookupProgram.instr 19 = .emit false 20 := rfl
example : CounterProgram.Words.lookupProgram.instr 20 = .halt [] := rfl

end Turing.MultiTapeTM.Tests.LogSpaceCounterWords
