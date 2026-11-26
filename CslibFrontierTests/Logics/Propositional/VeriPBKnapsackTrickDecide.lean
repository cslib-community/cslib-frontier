/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

-- `import all`: the kernel evaluates `stepTop` and `runTop`, the propagator `Inst.propagate` with
-- its private `Inst.emit`, `Inst.forward`, `Inst.backAll`, `Inst.remAll`, …, and the Boolean
-- emitter's partial sums, whose bodies are not exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP
import all CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackTrick
import CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackTrickProof

/-! A kernel-checked client of the two-equality knapsack propagator. Two items, `x₀ ∈ {0, 1, 2}` of
weight `2` and profit `1`, and `x₁ ∈ {0, 1}` of weight `3` and profit `2`, the weight
`W ∈ {0, …, 4}` and the profit `P ∈ {2, 3}`: the solutions are `(x₀, x₁) = (2, 0)`, of weight
`4` and profit `2`, and `(0, 1)`, of weight `3` and profit `2`. The kernel runs the propagator,
which removes the value `1` of `x₀`, the values `0, 1, 2` of `W` and the value `3` of `P`, and
the checker, which accepts the proof. By `mem_removed_iff` and `mem_removedW_iff` the removed
values are unsupported, and the value `2` of `x₀`, not removed, is supported. A proof extended
by an unjustified removal is rejected. -/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBKnapsackTrickDecide

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Knapsack.Trick

/-- The instance. -/
def J : Inst :=
  ⟨2, fun j => [2, 3].getD j 0, fun j => [1, 2].getD j 0,
    fun j => [[(0, true), (1, true), (2, true)], [(0, true), (1, true)]].getD j [],
    [(0, true), (1, true), (2, true), (3, true), (4, true)], [(2, true), (3, true)]⟩

theorem removed_eq : J.propagate.removed = [(0, 1)] := by decide +kernel

theorem removedW_eq : J.propagate.removedW = [0, 1, 2] := by decide +kernel

theorem removedP_eq : J.propagate.removedP = [1] := by decide +kernel

/-- The checker accepts the proof, as `Inst.checkRed_propagate` says of every instance. -/
example : checkRed J.formula none J.propagate.proof (some J.pres) = true := by
  decide +kernel

/-- **`x₀ = 1` is unsupported**: no solution takes it. -/
example : ¬ J.SupportedN 0 1 :=
  (J.mem_removed_iff.1 (by rw [removed_eq]; decide)).2.2

/-- **`W = 2` is unsupported.** -/
example : ¬ J.SupportedS false 2 :=
  (J.mem_removedW_iff.1 (by rw [removedW_eq]; decide)).2

/-- **`x₀ = 2` is supported**, the value not being removed. -/
example : J.SupportedN 0 2 := by
  by_contra h
  have := J.mem_removed_iff.2 ⟨by decide, by decide, h⟩
  rw [removed_eq] at this
  simp at this

/-- **An unjustified removal is rejected**: appending `[x₀ ≠ 0]`, which no RUP step derives,
makes the checker reject the proof. -/
example : checkRed J.formula none
    ⟨J.propagate.proof.steps ++ [.step (.rup (Knapsack.clause [(0, false)]) [.neg])], .noClaim⟩
    (some J.pres) = false := by
  decide +kernel

end CslibFrontierTests.Logics.Propositional.VeriPBKnapsackTrickDecide
