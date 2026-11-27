/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

-- `import all`: the kernel evaluates `stepTop` and `runTop`, the propagator `propagate` with its
-- private `Inst.run`, `Inst.emit`, `Inst.backAll`, `Inst.remAll`, …, and the emitter's
-- `Inst.forward`, `Inst.fwd`, `Inst.mkLayer`, …, whose bodies are not exposed; the test also names
-- the private `clause`.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP
import all CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackPropagator
import Mathlib.Data.Fin.VecNotation

/-! A kernel-checked client of the knapsack propagator. Four items of weights `3, 4, 5, 2` and
profits `4, 5, 6, 3`, the capacity `7` and the profit bound `9`, with item `1` fixed to `1`: the
kernel runs the propagator, which removes the value `1` of items `3` and `2` and the value `0` of
item `0`, and the checker, which accepts the proof. By `mem_removed_iff` the removed values are
unsupported, and the value `1` of item `0`, which is not removed, is supported. A proof extended by
an unjustified removal is rejected. -/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBKnapsackPropagatorDecide

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Knapsack

/-- The weights. -/
def w : Fin 4 → ℕ := ![3, 4, 5, 2]

/-- The profits. -/
def p : Fin 4 → ℕ := ![4, 5, 6, 3]

/-- The domains: item `1` fixed to `1`, the others free. -/
def dom : Fin 4 → Option Bool := ![none, some true, none, none]

theorem removed_eq : (propagate w p 7 9 dom).removed = [(3, true), (2, true), (0, false)] := by
  decide +kernel

/-- The checker accepts the proof, as `checkRed_propagate` says of every instance. -/
example : checkRed (propFormula w p 7 9) none (propagate w p 7 9 dom).proof
    (some (List.range 4)) = true := by
  decide +kernel

/-- **Item `2` cannot be taken**: with item `1` taken, no set of weight at most `7` and profit at
least `9` contains item `2`. -/
example : ¬ Supported w p 7 9 dom 2 true :=
  ((mem_removed_iff w p 7 9 dom 2 true).1 (by rw [removed_eq]; decide)).2

/-- **Item `0` must be taken.** -/
example : ¬ Supported w p 7 9 dom 0 false :=
  ((mem_removed_iff w p 7 9 dom 0 false).1 (by rw [removed_eq]; decide)).2

/-- **Taking item `0` is supported**, the value not being removed. -/
example : Supported w p 7 9 dom 0 true := by
  by_contra h
  have := (mem_removed_iff w p 7 9 dom 0 true).2 ⟨.inl rfl, h⟩
  rw [removed_eq] at this
  simp at this

/-- **An unjustified removal is rejected**: appending `x₁ ⇒ x₀ ≠ 1`, which no RUP step derives,
makes the checker reject the proof. -/
example : checkRed (propFormula w p 7 9) none
    ⟨(propagate w p 7 9 dom).proof.steps ++ [.step (.rup (clause [(1, false), (0, false)]) [.neg])],
      .noClaim⟩ (some (List.range 4)) = false := by
  decide +kernel

end CslibFrontierTests.Logics.Propositional.VeriPBKnapsackPropagatorDecide
