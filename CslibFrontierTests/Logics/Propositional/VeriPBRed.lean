/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance

/-! The VeriPB checker with redundance-based strengthening: a `red` step on a satisfiable
database whose witness repairs a solution violating the new constraint; a symmetry-breaking `red`
step with the swap witness `x0 ↔ x1` and all its proof goals, accepted and used to refute a
formula; the same step with a witness that does not repair, or with an unproved goal, rejected. -/

namespace CslibFrontierTests.Logics.Propositional.VeriPBRed

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB

/-! ### Repairing a solution -/

/-- The satisfiable database `x1 >= 1`, as constraint `1`. -/
def G : List PBConstr := [⟨[(1, (1, true))], 1⟩]

/-- `x0 >= 1`, which does not follow from `G`. -/
def D : PBConstr := ⟨[(1, (0, true))], 1⟩

/-- The witness `x0 ↦ 1`. -/
def setX0 : Witness := [(0, .one)]

/-- `red x0 >= 1 : x0 -> 1` needs no subproof: goal `#1`, `D|ω`, is `1 >= 1`, trivially true,
and `ω` touches no literal of constraint `1`. `~D` takes number `2`, and the step returns the
next number `3`, which `D` takes. -/
example : redCheck (initDb G) 2 D setX0 [] none = some 3 := by decide

/-- A solution of `G` that violates `D`: `x1` true, `x0` false. -/
def σ₀ : ℕ → Bool := fun v => v == 1

example : (∀ c ∈ G, c.Holds σ₀) ∧ ¬ D.Holds σ₀ := by decide

-- The repaired assignment `σ₀ ∘ ω` sets `x0` true and satisfies both `G` and `D`.
example : (∀ c ∈ G, c.Holds (Witness.apply σ₀ setX0)) ∧ D.Holds (Witness.apply σ₀ setX0) := by
  decide

-- As a step of a proof, `D` joins the database as constraint `3`.
example : runTop (initDb G) 2 [.red D setX0 [] none] = some ((3, D.normalize) :: initDb G, 4) := by
  decide

/-! ### Breaking a symmetry -/

/-- `x0 ↔ x1` and exactly one of `x0`, `x1`: unsatisfiable, and symmetric under swapping the two
variables. Constraints `1`–`4`: `x0 + x1 >= 1`, `~x0 + ~x1 >= 1`, `x0 + ~x1 >= 1`,
`~x0 + x1 >= 1`. -/
def F : List PBConstr :=
  [⟨[(1, (0, true)), (1, (1, true))], 1⟩, ⟨[(1, (0, false)), (1, (1, false))], 1⟩,
    ⟨[(1, (0, true)), (1, (1, false))], 1⟩, ⟨[(1, (0, false)), (1, (1, true))], 1⟩]

/-- The swap `x0 ↦ x1`, `x1 ↦ x0`. -/
def swap : Witness := [(0, .lit (1, true)), (1, .lit (0, true))]

/-- `~x0 >= 1`. -/
def C : PBConstr := ⟨[(1, (0, false))], 1⟩

/-- `red ~x0 >= 1 : x0 -> x1 x1 -> x0` breaks the symmetry. `~C`, that is `x0 >= 1`, is
constraint `5`. Goal `#1`, `~x1 >= 1`, follows by RUP from its negation `6` (`x1`), `5` and `2`.
The goals of constraints `1`–`4` are the constraints with `x0` and `x1` swapped, which are
constraints `1`, `2`, `4` and `3`: they are in the database and need no subproof. `C` is then
constraint `8`, and RUP from `8`, `3`, `1` gives the contradiction `9`. -/
def proof : RedProof :=
  ⟨[.red C swap [.goal .self [.rup ⟨[], 1⟩ [.id 6, .id 5, .id 2]] 7] none,
    .step (.rup ⟨[], 1⟩ [.id 8, .id 3, .id 1])], 9⟩

example : checkRed F proof = true := by decide

theorem F_unsat (σ : ℕ → Bool) : ¬ ∀ c ∈ F, c.Holds σ :=
  not_satisfiable_of_checkRed (P := proof) (by decide) σ

-- The database goals may also be proved explicitly, each by RUP from its negation.
example : checkRed F
    ⟨[.red C swap
        [.goal .self [.rup ⟨[], 1⟩ [.id 6, .id 5, .id 2]] 7,
          .goal (.db 1) [.rup ⟨[], 1⟩ [.id 8, .id 1]] 9,
          .goal (.db 2) [.rup ⟨[], 1⟩ [.id 10, .id 2]] 11,
          .goal (.db 3) [.rup ⟨[], 1⟩ [.id 12, .id 4]] 13,
          .goal (.db 4) [.rup ⟨[], 1⟩ [.id 14, .id 3]] 15] none,
      .step (.rup ⟨[], 1⟩ [.id 16, .id 3, .id 1])], 17⟩ = true := by
  decide

-- Goal `#1` is not in the database: without its subproof the step is rejected.
example : checkRed F ⟨[.red C swap [] none, .step (.rup ⟨[], 1⟩ [.id 6, .id 3, .id 1])], 7⟩ =
    false := by
  decide

-- Without a witness, goal `#1` is `C` itself, which nothing covers.
example : checkRed F ⟨[.red C [] [] none, .step (.rup ⟨[], 1⟩ [.id 6, .id 3, .id 1])], 7⟩ =
    false := by
  decide

-- The witness `x0 ↦ 0` makes goal `#1` trivial, but the goal of constraint `1` becomes `x1 >= 1`,
-- which does not follow from the database and `x0`: its subproof fails.
example : checkRed F
    ⟨[.red C [(0, .zero)] [.goal (.db 1) [.rup ⟨[], 1⟩ [.id 6, .id 1]] 7] none,
      .step (.rup ⟨[], 1⟩ [.id 8, .id 3, .id 1])], 9⟩ = false := by
  decide

-- A `red` subproof may instead derive a contradiction from `~C`: then `C` follows outright.
example : checkRed F
    ⟨[.red C [] [.step (.rup ⟨[], 1⟩ [.id 5, .id 4, .id 2])] (some 6),
      .step (.rup ⟨[], 1⟩ [.id 7, .id 3, .id 1])], 8⟩ = true := by
  decide

end CslibFrontierTests.Logics.Propositional.VeriPBRed
