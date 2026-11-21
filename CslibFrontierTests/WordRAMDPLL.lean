/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Algorithms.WordRAM.DPLL.Solver
public meta import CslibFrontier.Algorithms.WordRAM.DPLL.Solver

/-! An ordinary-module client of the DPLL solver on the word RAM: the encoding of small formulas,
runs of the exported compiled program that return the solver's answer and model, and the exported
cost theorem `program_spec` at word size `64`. -/

set_option linter.hashCommand false

public section

namespace CslibFrontierTests.WordRAMDPLL

open Cslib.WordRAM Cslib.Logic.PL Cslib.Algorithms.WordRAM.DPLL

/-- Every clause over two variables: unsatisfiable. -/
def full : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- `x2 ∨ x0`, `¬x0`: satisfiable, with `x0` false and `x2` true. -/
def unitFirst : CNF ℕ := [[(2, true), (0, true)], [(0, false)]]

-- The input: the bound `N = 3`, then each clause as its length and the codes `2 v + b`.
example : encode 3 unitFirst = [3, 2, 5, 1, 1, 0] := rfl

/-- Run the compiled solver at word size `64` and read its output list. -/
def runList (p : Program .standard 32) : ℕ → State 32 → Option (List ℕ × ℕ)
  | 0, _ => none
  | fuel + 1, s =>
    match step 64 p s with
    | .next t => (runList p fuel t).map fun ln => (ln.1, ln.2 + 1)
    | .halt v => some (outputList s.data.mem v, 1)
    | .fault => none

/-- The solver on `encode N φ` with a generous instruction budget. -/
def runSolver (N : ℕ) (φ : CNF ℕ) : Option (List ℕ × ℕ) :=
  runList program 100000 (State.init (encode N φ))

-- An unsatisfiable formula gives `[0]`, the output of `solve`, in `2013` instructions.
#guard runSolver 2 full == some ([0], 2013)

#guard answerWords 2 full == [0]

-- A satisfiable formula gives `1` and the solver's model on the variables below `N`.
#guard (runSolver 3 unitFirst).map Prod.fst == some [1, 0, 0, 1]

#guard answerWords 3 unitFirst == [1, 0, 0, 1]

-- The empty formula: the model with every variable false.
#guard (runSolver 2 []).map Prod.fst == some [1, 0, 0]

-- The empty clause is falsified at once.
#guard (runSolver 1 [[]]).map Prod.fst == some [0]

-- `program_spec` bounds the count by `2 ^ 3 · (46 · 13 + 64) + 10 · 2 + 8 · 13 + 21 = 5441`.

example : (encode 2 full).length = 13 ∧ Cslib.Algorithms.Lean.DPLL.depth full = 2 := by decide

-- The hypothesis of `program_spec` holds at word size `64`, so the solver returns the output of
-- `solve` within the bound.
example : ∃ n ≤ 2 ^ (Cslib.Algorithms.Lean.DPLL.depth full + 1) * (46 * (encode 2 full).length +
      64) + 10 * 2 + 8 * (encode 2 full).length + 21,
    ExecutesList 64 program (State.init (encode 2 full)) (answerWords 2 full) n :=
  program_spec 2 full (by decide) (w := 64) (by decide)

end CslibFrontierTests.WordRAMDPLL

end
