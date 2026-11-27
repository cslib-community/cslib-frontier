/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.Lean.DPLL.RefutationSize

/-!
# The size of the DPLL solver's refutations

On PHP(3, 2), with pigeon `i` in hole `j` numbered `2 * i + j`, the kernel runs the solver with
`decide`: the refutation it finds has 21 nodes and 11 leaves, and its LRAT certificate 11 steps.
This lies between the lower bound `(2 / 2 + 1) ^ (2 / 2) = 2` of
`pow_half_le_size_refutation?_pigeonhole` and the upper bound `2 ^ (6 + 1) = 128` of
`size_lt_of_refutation?_eq_some` for its 6 variables. The numbering is injective, so the
lower-bound theorems apply to it.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.DPLL.RefutationSize

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Algorithms.Lean.DPLL

/-- PHP(3, 2) over `ℕ`: pigeon `i` in hole `j` is the variable `2 * i + j`. -/
private abbrev php : CNF ℕ := (pigeonhole 3 2).relabel fun x => 2 * x.1 + x.2

private theorem injective_index : Function.Injective fun x : Fin 3 × Fin 2 => 2 * x.1.val + x.2 :=
  by decide

example : (refutation? php).map (·.size) = some 21 := by decide

example : (match solve php with
    | .unsat cert => some cert.size
    | .sat _ => none) = some 11 := by
  decide

example : php.vars.toFinset.card = 6 := by decide

example : ∃ d, refutation? php = some d ∧ (2 / 2 + 1) ^ (2 / 2) ≤ d.size :=
  pow_half_le_size_refutation?_pigeonhole injective_index (by decide)

example : ∃ cert, solve php = .unsat cert ∧ (2 / 2 + 1) ^ (2 / 2) ≤ cert.size :=
  pow_half_le_size_solve_pigeonhole injective_index (by decide)

end CslibFrontierTests.Algorithms.Lean.DPLL.RefutationSize
