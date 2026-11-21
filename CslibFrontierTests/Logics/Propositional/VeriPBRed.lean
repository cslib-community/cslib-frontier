/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

-- `import all`: the `decide` checks below evaluate `stepTop`, whose body is not exposed, and its
-- private helpers.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance

/-! The VeriPB checker with redundance-based strengthening: a `red` step on a satisfiable
database whose witness repairs a solution violating the new constraint; a symmetry-breaking `red`
step with the swap witness `x0 ↔ x1` and all its proof goals, accepted and used to refute a
formula; the same step with a witness that does not repair, or with an unproved goal, rejected;
and, with an objective, a `red` step whose witness raises the objective, accepted without the
objective and rejected with it. -/

set_option linter.privateModule false

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
example : redCheck none (initDb G) 2 D setX0 [] none = some 3 := by decide

/-- A solution of `G` that violates `D`: `x1` true, `x0` false. -/
def σ₀ : ℕ → Bool := fun v => v == 1

example : (∀ c ∈ G, c.Holds σ₀) ∧ ¬ D.Holds σ₀ := by decide

-- The repaired assignment `σ₀ ∘ ω` sets `x0` true and satisfies both `G` and `D`.
example : (∀ c ∈ G, c.Holds (Witness.apply σ₀ setX0)) ∧ D.Holds (Witness.apply σ₀ setX0) := by
  decide

-- As a step of a proof without a subproof, `¬D` takes no number and `D` joins the database as
-- constraint `2`, as in VeriPB.
example : runTop G none (State.init G) [.red D setX0 none none] =
    some ⟨(2, D.normalize) :: initDb G, 3, none, none, initDb G, true, false⟩ := by
  decide

-- With a subproof, even an empty one, `¬D` takes `2` and `D` takes `3`.
example : runTop G none (State.init G) [.red D setX0 (some []) none] =
    some ⟨(3, D.normalize) :: initDb G, 4, none, none, initDb G, true, false⟩ := by
  decide

/-! ### Promoting to the core -/

-- `core id 1` on the input constraint `1`, already in the core set, is a no-op (§5.1): the core
-- set is unchanged, however often it is repeated.
example : runTop G none (State.init G) [.core [1], .core [1]] = some (State.init G) := by
  decide

-- A derived constraint is promoted once.
example : runTop G none (State.init G) [.red D setX0 none none, .core [2, 2], .core [2]] =
    some ⟨(2, D.normalize) :: initDb G, 3, none, none, (2, D.normalize) :: initDb G, true,
      false⟩ := by
  decide

-- `core id` needs at least one ID.
example : runTop G none (State.init G) [.core []] = none := by decide

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
  ⟨[.red C swap (some [.goal .self [.rup ⟨[], 1⟩ [.id 6, .id 5, .id 2]] 7]) none,
    .step (.rup ⟨[], 1⟩ [.id 8, .id 3, .id 1])], .unsat 9⟩

example : checkRed F none proof = true := by decide

theorem F_unsat (σ : ℕ → Bool) : ¬ ∀ c ∈ F, c.Holds σ :=
  not_satisfiable_of_checkRed (obj := none) (P := proof) (by decide) rfl σ

-- The database goals may also be proved explicitly, each by RUP from its negation.
example : checkRed F none
    ⟨[.red C swap (some
        [.goal .self [.rup ⟨[], 1⟩ [.id 6, .id 5, .id 2]] 7,
          .goal (.db 1) [.rup ⟨[], 1⟩ [.id 8, .id 1]] 9,
          .goal (.db 2) [.rup ⟨[], 1⟩ [.id 10, .id 2]] 11,
          .goal (.db 3) [.rup ⟨[], 1⟩ [.id 12, .id 4]] 13,
          .goal (.db 4) [.rup ⟨[], 1⟩ [.id 14, .id 3]] 15]) none,
      .step (.rup ⟨[], 1⟩ [.id 16, .id 3, .id 1])], .unsat 17⟩ = true := by
  decide

-- Goal `#1` is not in the database: without its subproof the step is rejected.
example : checkRed F none
    ⟨[.red C swap (some []) none, .step (.rup ⟨[], 1⟩ [.id 6, .id 3, .id 1])], .unsat 7⟩ =
      false := by
  decide

-- Without a witness, goal `#1` is `C` itself, which nothing covers.
example : checkRed F none
    ⟨[.red C [] (some []) none, .step (.rup ⟨[], 1⟩ [.id 6, .id 3, .id 1])], .unsat 7⟩ = false := by
  decide

-- The witness `x0 ↦ 0` makes goal `#1` trivial, but the goal of constraint `1` becomes `x1 >= 1`,
-- which does not follow from the database and `x0`: its subproof fails.
example : checkRed F none
    ⟨[.red C [(0, .zero)] (some [.goal (.db 1) [.rup ⟨[], 1⟩ [.id 6, .id 1]] 7]) none,
      .step (.rup ⟨[], 1⟩ [.id 8, .id 3, .id 1])], .unsat 9⟩ = false := by
  decide

-- A `red` subproof may instead derive a contradiction from `~C`: then `C` follows outright.
example : checkRed F none
    ⟨[.red C [] (some [.step (.rup ⟨[], 1⟩ [.id 5, .id 4, .id 2])]) (some 6),
      .step (.rup ⟨[], 1⟩ [.id 7, .id 3, .id 1])], .unsat 8⟩ = true := by
  decide

/-! ### Preserving an optimal solution -/

/-- `x0 + x1 >= 1` and `x1 + x2 >= 1`, constraints `1` and `2`. -/
def H : List PBConstr :=
  [⟨[(1, (0, true)), (1, (1, true))], 1⟩, ⟨[(1, (1, true)), (1, (2, true))], 1⟩]

/-- The objective `x0 + x1 + x2`. -/
def f : Objective := ⟨[(0, 1), (1, 1), (2, 1)], 0⟩

/-- `x0 >= 1`. -/
def X0 : PBConstr := ⟨[(1, (0, true))], 1⟩

-- `red x0 >= 1 : x0 -> 1` repairs every solution, so for the decision problem it is accepted,
example : redCheck none (initDb H) 3 X0 [(0, .one)] [] none = some 4 := by decide

-- but it raises the objective: the goal `#2`, `f|ω ≤ f`, is `x0 >= 1`, which `~x0 >= 1` does
-- not imply, so for the objective `f` the step is rejected.
example : objGoal f [(0, .one)] = ⟨[(1, (0, true))], 1⟩ := by decide
example : redCheck (some f) (initDb H) 3 X0 [(0, .one)] [] none = none := by decide

/-- `~x0 >= 1`. -/
def NX0 : PBConstr := ⟨[(1, (0, false))], 1⟩

-- `red ~x0 >= 1 : x0 -> 0 x1 -> 1` does not raise the objective under `x0 >= 1`: its goal `#2`,
-- `x0 + x1 >= 1`, follows from `x0 >= 1` by adding a literal axiom.
example : redCheck (some f) (initDb H) 3 NX0 [(0, .zero), (1, .one)] [] none = some 4 := by
  decide

end CslibFrontierTests.Logics.Propositional.VeriPBRed
