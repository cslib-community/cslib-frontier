/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

import CslibFrontier.Computability.Automata.MPDA.OneHole
import Mathlib.Tactic.FinCases

/-! Clients of the public hole API under module encapsulation: on two stacks, the complete run
`↓₀ ↓₁ ↑₀ ↑₁` has a crossing, so it is not `1`-hole-bounded and, by the one-hole theorem, not
well-nested; the complete run `↓₀ ↓₁ ↑₁ ↑₀` is well-nested and so `0`-hole-bounded. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MPDA.Holes

open Cslib Cslib.Automata Cslib.Automata.MPDA

/-- One control state, one input letter, and every stack operation on two stacks. -/
private def anyOp : MPDA 2 Unit Unit Unit where
  Tr _ _ _ := True
  start := {()}
  accept := {()}

/-- Crossing pushes and pops on two stacks: `↓₀ ↓₁ ↑₀ ↑₁`. -/
private def crossing : List (Unit × Op 2 Unit) :=
  [((), .push 0 ()), ((), .push 1 ()), ((), .pop 0 ()), ((), .pop 1 ())]

/-- Nested pushes and pops on two stacks: `↓₀ ↓₁ ↑₁ ↑₀`. -/
private def nested : List (Unit × Op 2 Unit) :=
  [((), .push 0 ()), ((), .push 1 ()), ((), .pop 1 ()), ((), .pop 0 ())]

private theorem crossing_run :
    anyOp.configLTS.MTr ⟨(), Stacks.empty⟩ crossing ⟨(), Stacks.empty⟩ := by
  refine .stepL (s2 := ⟨(), Function.update Stacks.empty 0 [()]⟩) ?_ <|
    .stepL (s2 := ⟨(), Function.update (Function.update Stacks.empty 0 [()]) 1 [()]⟩) ?_ <|
    .stepL (s2 := ⟨(), Function.update Stacks.empty 1 [()]⟩) ?_ <|
    .stepL ?_ .refl <;>
  refine configLTS_tr.mpr ⟨trivial, ?_⟩ <;>
  simp only [Op.apply_push, Op.apply_pop] <;>
  funext k <;> fin_cases k <;> simp [Stacks.empty]

/-- The push on stack `0` is matched by the pop at position `2`, and the push on stack `1` in
between is still pending there. -/
private theorem crossing_crossing : Crossing crossing :=
  ⟨0, 1, 0, 1, 2, by decide, by decide, by decide, ⟨(), (), rfl⟩, ⟨(), (), rfl⟩,
    ⟨by decide, 0, ⟨(), (), rfl⟩, ⟨(), (), rfl⟩,
      fun k => by rcases k with _ | _ | k <;> simp [crossing, List.extract, net, Op.net], rfl⟩,
    by decide, by decide, 1, ⟨(), (), rfl⟩,
      fun k => by rcases k with _ | _ | k <;> simp [crossing, List.extract, net, Op.net]⟩

example : ¬HoleBounded 1 crossing := crossing_crossing.not_holeBounded_one

/-- The one-hole theorem turns the crossing into a proof that the complete run is not
well-nested. -/
example : ¬WellNested crossing := fun hw =>
  crossing_crossing.not_holeBounded_one ((holeBounded_one_iff_wellNested crossing_run).mpr hw)

example : HoleBounded 0 nested := (WellNested.pushPop (.pushPop .nil .nil) .nil).holeBounded_zero

end CslibFrontierTests.MPDA.Holes
