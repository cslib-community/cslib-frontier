/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.Algorithms.WordRAM.LRAT.Checker

/-! The LRAT checker on the word RAM: the encoding of a small formula and certificate, runs of the
compiled program that accept a certificate and reject others, the quantities of the coarser bound
of `program_spec_dbWidth`, and the hypothesis of both bounds at word size `64`, also on a
certificate of width `0`. -/

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

-- The quantities of `program_spec_dbWidth`: the longest clause of the database has length `2`, the
-- formula is encoded by `12` words, and the certificate has `5` hints and is encoded by `12` words,
-- so `certWork φ cert = 9 ≤ 5 · 2` and the coarser bound is `80 · (12 + 12 · 2) + 81 = 2961`.
example : dbWidth φ cert = 2 := by decide

example : CNF.lratHintCount cert.toList = 5 := by decide

example : (φ.flatMap Cslib.Algorithms.WordRAM.ClauseCode.encodeClause).length = 12 := by decide

example : (stepWords cert.toList).length = 12 := by decide

-- An added clause can be the widest: the RUP step adds a clause of length `3`.
example : dbWidth [[(0, true)]] #[.addRup 2 #[1, 2, 3] #[], .addEmpty 3 #[]] = 3 := by decide

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

-- The coarser bound at word size `64`.
example : ∃ n ≤ 2961, Executes 64 program (State.init (encode φ cert)) 1 n := by
  obtain ⟨n, hn, he⟩ := program_spec_dbWidth φ cert (w := 64) (by decide)
  exact ⟨n, hn.trans_eq (by decide), he⟩

/-- A certificate of width `0`: `100` deletions over the empty formula, encoded by `300` words. -/
def dels : Array LRAT.IntAction := Array.replicate 100 (.del #[1])

example : dbWidth [] dels = 0 := by decide +kernel

example : (stepWords dels.toList).length = 300 := by decide +kernel

-- The checker reads every deletion before rejecting the certificate, which never reaches an
-- empty-clause step: the run grows with the certificate although no clause is ever read.
#guard runChecker [] dels == some (0, 2118)

-- The coarser bound still charges every step at width `0`: `80 · (0 + 300 · max 1 0) + 81 = 24081`.
example : ∃ n ≤ 24081, Executes 64 program (State.init (encode [] dels)) 0 n := by
  obtain ⟨n, hn, he⟩ := program_spec_dbWidth [] dels (w := 64) (by decide +kernel)
  exact ⟨n, hn.trans_eq (by decide +kernel), he⟩

end CslibFrontierTests.WordRAMLRAT
