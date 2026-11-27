/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.Algorithms.WordRAM.LRAT.Checker

/-! The LRAT checker on the word RAM: the encoding of a small formula and certificate, runs of the
compiled program that accept a certificate and reject others, and the hypothesis of
`program_spec` at word size `64`. -/

set_option linter.hashCommand false

namespace CslibFrontierTests.WordRAMLRAT

open Cslib.WordRAM Cslib.Logic.PL Std.Tactic.BVDecide Cslib.Algorithms.WordRAM.LRAT

/-- Every clause over two variables. -/
def φ : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- The refutation: the unit clause `a`, then the empty clause. -/
def cert : Array LRAT.IntAction :=
  #[.addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]]

-- The input: the number of clauses, each clause as its length and the codes `2 v + b`, then the
-- steps: `1, 5, [1, 1], [2, 1, 2]` adds clause `5` = `a` with hints `1, 2`, and `0, [3, 5, 3, 4]`
-- is the empty clause with hints `5, 3, 4`.
example : encode φ cert =
    [4, 2, 1, 3, 2, 1, 2, 2, 0, 3, 2, 0, 2, 1, 5, 1, 1, 2, 1, 2, 0, 3, 5, 3, 4] := rfl

example : φ.checkLRAT cert = true := by decide

/-- The compiled checker at word size `64` with a generous instruction budget. -/
def runChecker (ψ : CNF ℕ) (c : Array LRAT.IntAction) : Option (ℕ × ℕ) :=
  run 64 program 100000 (State.init (encode ψ c))

-- The checker accepts the certificate in `324` instructions; `program_spec` bounds the count by
-- `60 · 25 + 20 · 9 + 21 = 1701`, where `9` is the total length of the hinted clauses.
#guard runChecker φ cert == some (1, 324)

example : certWork φ cert = 9 := by decide

-- Hints that do not propagate to a conflict are rejected.
#guard runChecker φ #[.addEmpty 5 #[3, 4]] == some (0, 121)

-- A certificate must reach an empty-clause step.
#guard (runChecker φ #[.addRup 5 #[1] #[1, 2]]).map Prod.fst == some 0

-- RAT steps are rejected.
#guard (runChecker φ #[.addRat 5 #[1] (0, true) #[] #[], .addEmpty 6 #[5, 3, 4]]).map Prod.fst ==
  some 0

-- A hint naming a deleted clause is rejected.
#guard (runChecker φ #[.addRup 5 #[1] #[1, 2], .del #[5], .addEmpty 6 #[5, 3, 4]]).map
  Prod.fst == some 0

-- A repeated literal counts once: `a ∨ a` forces `a`, which falsifies `¬a`.
#guard (runChecker [[(0, true), (0, true)], [(0, false)]] #[.addEmpty 3 #[1, 2]]).map Prod.fst ==
  some 1

-- The hypothesis of `program_spec` holds at word size `64`, so the checker halts with the answer
-- of `checkLRAT` within the bound.
example : ∃ n ≤ 60 * (encode φ cert).length + 20 * certWork φ cert + 21,
    Executes 64 program (State.init (encode φ cert)) 1 n :=
  program_spec φ cert (w := 64) (by decide)

end CslibFrontierTests.WordRAMLRAT
