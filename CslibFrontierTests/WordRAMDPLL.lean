/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Algorithms.WordRAM.DPLL.Refutation
public meta import CslibFrontier.Algorithms.WordRAM.DPLL.Refutation

/-! An ordinary-module client of the DPLL solver on the word RAM: the encoding of small formulas,
runs of the exported compiled program that return the solver's answer and model, and the exported
cost theorem `program_spec` at word size `64`; then the variant that writes its search tree. -/

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

-- An unsatisfiable formula gives `[0]`, the output of `solve`, in `1587` instructions.
#guard runSolver 2 full == some ([0], 1587)

#guard answerWords 2 full == [0]

-- A satisfiable formula gives `1` and the solver's model on the variables below `N`.
#guard (runSolver 3 unitFirst).map Prod.fst == some [1, 0, 0, 1]

#guard answerWords 3 unitFirst == [1, 0, 0, 1]

/-- `x0 ∨ x1 ∨ ¬x0`: without a unit clause, the search branches on the variable that occurs
first. -/
def firstOccurrence : CNF ℕ := [[(0, true), (1, true), (0, false)]]

#guard (runSolver 2 firstOccurrence).map Prod.fst == some [1, 1, 0]

#guard answerWords 2 firstOccurrence == [1, 1, 0]

-- The empty formula: the model with every variable false.
#guard (runSolver 2 []).map Prod.fst == some [1, 0, 0]

-- The empty clause is falsified at once.
#guard (runSolver 1 [[]]).map Prod.fst == some [0]

-- `program_spec` bounds the count by `2 ^ 3 · (37 · 13 + 62) + 10 · 2 + 14 = 4378`.

example : (encode 2 full).length = 13 ∧ Cslib.Algorithms.Lean.DPLL.depth full = 2 := by decide

-- The hypothesis of `program_spec` holds at word size `64`, so the solver returns the output of
-- `solve` within the bound.
example : ∃ n ≤ 2 ^ (Cslib.Algorithms.Lean.DPLL.depth full + 1) * (37 * (encode 2 full).length +
      62) + 10 * 2 + 14,
    ExecutesList 64 program (State.init (encode 2 full)) (answerWords 2 full) n :=
  program_spec 2 full (by decide) (w := 64) (by decide)

/-! ### The variant writing the search tree -/

/-- The variant on `encode N φ` with a generous instruction budget. -/
def runSolverLog (N : ℕ) (φ : CNF ℕ) : Option (List ℕ × ℕ) :=
  runList programLog 100000 (State.init (encode N φ))

-- On `full`, the clauses start at addresses `2, 5, 8, 11` and the literal array at `T = 14`. The
-- search branches on `x0` (cell `14 + 1`), propagates `x1` (cell `14 + 3`), which falsifies the
-- clause at `11`, and its negation, which falsifies the clause at `8`; then on `¬x0` it
-- propagates `x1` again, falsifying the clauses at `5` and at `2`. The output is `0` followed by
-- these words in preorder.
#guard (runSolverLog 2 full).map Prod.fst == some [0, 15, 17, 11, 8, 17, 5, 2]

#guard refutationWords 2 full == [0, 15, 17, 11, 8, 17, 5, 2]

-- The words read back to a tree with four leaves, and nothing is left over.
#guard (decodeTree full 7 [15, 17, 11, 8, 17, 5, 2]).map (fun r => (r.1.leafCount, r.2)) ==
  some (4, [])

-- On a satisfiable formula the variant returns the model, as the solver does.
#guard (runSolverLog 3 unitFirst).map Prod.fst == some [1, 0, 0, 1]

#guard refutationWords 3 unitFirst == answerWords 3 unitFirst

-- The search tree of `full` has four leaves, so every run takes at least four instructions.
example : (Cslib.Algorithms.Lean.DPLL.searchTree full 2 []).leafCount = 4 := by decide

/-- The numbering `(i, j) ↦ 2 i + j` of the variables of `PHP^3_2`. -/
def number (p : Fin 3 × Fin 2) : ℕ := 2 * (p.1 : ℕ) + p.2

theorem number_injective : Function.Injective number := fun p q h => by
  have := p.2.isLt
  have := q.2.isLt
  simp only [number] at h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

-- The hypotheses of `programLog_pigeonhole` hold for `PHP^3_2` numbered by `number`, with `N = 6`
-- at word size `64`.
example : (∃ k ≤ 301 * 2 ^ 6 * (encode 6 ((CNF.pigeonhole 3 2).relabel number)).length,
        ExecutesList 64 programLog (State.init (encode 6 ((CNF.pigeonhole 3 2).relabel number)))
          (refutationWords 6 ((CNF.pigeonhole 3 2).relabel number)) k) ∧
      ∀ v k, Executes 64 programLog (State.init (encode 6 ((CNF.pigeonhole 3 2).relabel number)))
        v k → (2 / 2 + 1) ^ (2 / 2) ≤ k :=
  programLog_pigeonhole number_injective (by decide) 6 (by decide) (w := 64) (by decide)

end CslibFrontierTests.WordRAMDPLL

end
