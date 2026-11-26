/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

-- `import all`: the kernel evaluates `stepTop` and the text front end, whose bodies are not
-- exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text
import CslibFrontier.Logics.Propositional.PseudoBoolean.Reification

/-! The reification combinators of `CslibFrontier.Logics.Propositional.PseudoBoolean.Reification`
on small proofs, checked by `decide +kernel`:

* the reification `x3 ⇔ 2 x1 + x2 ≥ 2` of a fresh variable, under an objective, as
  `runTop_reify` predicts, and its rejection for a variable that is not fresh;
* `reifySteps`, which reifies `x3 ⇔ x1 + x2 ≥ 2`, wraps `x3` from the unit clauses `x1` and `x2`,
  unwraps `x1 + x2 ≥ 2` and refutes `~x1 + ~x2 ≥ 1`.

The proof is also written out as kernel text, `reifyText`, as a small printer of the steps renders
it (the printer is outside the test suite), and the text front end accepts it. VeriPB 3.0.2 and
CakePB both report `s VERIFIED UNSATISFIABLE` on this text with `F₁Text`. The ordinary-import
client of the same API is `CslibFrontierTests.Logics.Propositional.VeriPBReify`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBReifyDecide

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB PBConstr

/-! ### Reification of a fresh variable -/

/-- `2 x1 + x2 ≥ 2`. -/
def C₀ : PBConstr := ⟨[(2, (0, true)), (1, (1, true))], 2⟩

/-- `x1 + x2 ≥ 1`, with the objective `x1 - x2` and the preserved set `{x1}`. -/
def F₀ : List PBConstr := [⟨[(1, (0, true)), (1, (1, true))], 1⟩]

def f₀ : Objective := ⟨[(0, 1), (1, -1)], 0⟩

def s₀ : State := State.init F₀ (some f₀) (some [0])

example : s₀.fresh 2 = true := by decide +kernel

/-- The reification of `x3` adds `x3 ⇒ C₀` and `C₀ ⇒ x3` at `3` and `5`, as `runTop_reify`
predicts. -/
example : runTop F₀ (some f₀) s₀ (reify 2 C₀) =
    some ((s₀.addStrengthened 3 (impl [(2, true)] C₀)).addStrengthened 5
      (impl [(2, false)] C₀.negate)) :=
  runTop_reify (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : (runTop F₀ (some f₀) s₀ (reify 2 C₀)).isSome = true := by decide +kernel

/-- `x2` is not fresh: it is in the formula, and the reification is rejected. -/
example : runTop F₀ (some f₀) s₀ (reify 1 C₀) = none := by decide +kernel

/-- With `x3` preserved, the witness may not touch it, and the reification is rejected. -/
example : runTop F₀ none (State.init F₀ none (some [2])) [reifyFwd 2 C₀] = none := by
  decide +kernel

/-! ### Wrapping and unwrapping -/

/-- `x1 ≥ 1`, `x2 ≥ 1`, `~x1 + ~x2 ≥ 1`. -/
def F₁ : List PBConstr :=
  [⟨[(1, (0, true))], 1⟩, ⟨[(1, (1, true))], 1⟩, ⟨[(1, (0, false)), (1, (1, false))], 1⟩]

/-- `x1 + x2 ≥ 2`. -/
def C₁ : PBConstr := ⟨[(1, (0, true)), (1, (1, true))], 2⟩

/-- Reify `x3 ⇔ C₁` (constraints `5` and `7`), wrap `x3` from `7` and the unit clauses `1` and
`2` (`8`, `9`), unwrap `C₁` from `5` and `9` (`10`), and add `3` (`11`, a contradiction). -/
def reifySteps : List TopStep :=
  reify 2 C₁ ++ [.step (resolveGuard 7 1 1), .step (resolveGuard 8 2 1),
    .step (resolveGuard 5 9 2), .step (.pol [.id 10, .id 3, .add])]

example : checkRed F₁ none ⟨reifySteps, .unsat 11⟩ = true := by decide +kernel

/-- The wrapped constraint `9` is `x3 ≥ 1`, and the unwrapped `10` is `C₁`. -/
example : (runTop F₁ none (State.init F₁ none none) reifySteps).map
    (fun s => (lookup s.db 9, lookup s.db 10)) =
    some (some ⟨[(1, (2, true))], 1⟩, some C₁) := by decide +kernel

def reifyText : String :=
  "pseudo-Boolean proof version 3.0\nf 3 ;\n" ++
  "red 2 ~x3 1 x1 1 x2 >= 2 : x3 -> 0 : subproof\nqed ;\n" ++
  "red 1 x3 1 ~x2 1 ~x1 >= 1 : x3 -> 1 : subproof\nqed ;\n" ++
  "pol 7 1 1 * + ;\npol 8 2 1 * + ;\npol 5 9 2 * + ;\npol 10 3 + ;\n" ++
  "output NONE ;\nconclusion UNSAT : 11 ;\nend pseudo-Boolean proof ;\n"

def F₁Text : String :=
  "* #variable= 2 #constraint= 3\n1 x1 >= 1 ;\n1 x2 >= 1 ;\n1 ~x1 1 ~x2 >= 1 ;\n"

example : Text.checkOPB F₁Text reifyText = some (.unsat 11) := by decide +kernel

end CslibFrontierTests.Logics.Propositional.VeriPBReifyDecide
