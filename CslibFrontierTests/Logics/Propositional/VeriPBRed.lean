/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

-- `import all`: the `decide` checks below evaluate `stepTop`, whose body is not exposed, and its
-- private helpers.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import CslibFrontier.Logics.Propositional.PseudoBoolean.Output
import CslibFrontierTests.Logics.Propositional.VeriPBAuxFixtures
import CslibFrontierTests.Logics.Propositional.VeriPBDomFixtures

/-! The VeriPB checker with redundance-based strengthening: a `red` step on a satisfiable
database whose witness repairs a solution violating the new constraint; a symmetry-breaking `red`
step with the swap witness `x0 ↔ x1` and all its proof goals, accepted and used to refute a
formula; the same step with a witness that does not repair, or with an unproved goal, rejected;
and, with an objective, a `red` step whose witness raises the objective, accepted without the
objective and rejected with it; an `EQUIENUMERABLE` output section, checked by `decide`, with
its soundness theorems applied; and orders and dominance: a lexicographic order on two bits whose
transitivity and reflexivity proofs check, giving a preorder, and a relation whose transitivity
proof fails or whose fresh variables are not fresh; and a symmetry-breaking `dom` step deriving
the lex-leader constraint, which certifies the optimum of a symmetric objective, rejected for an
asymmetric objective, without a loaded order, and for the order loaded over the swapped
literals. -/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBRed

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB
open CslibFrontierTests.Logics.Propositional.VeriPBText (lex2 lex2Trans lex2Refl notAuxO notAuxSpec
  notAuxTrans notAuxRefl)

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
example : runTop G none (State.init G none none) [.red D setX0 none none] =
    some ⟨(2, D.normalize) :: initDb G, 3, none, none, initDb G, true, false, none, none, [], [],
      none, none⟩ := by
  decide

-- With a subproof, even an empty one, `¬D` takes `2` and `D` takes `3`.
example : runTop G none (State.init G none none) [.red D setX0 (some []) none] =
    some ⟨(3, D.normalize) :: initDb G, 4, none, none, initDb G, true, false, none, none, [], [],
      none, none⟩ := by
  decide

/-! ### Promoting to the core -/

-- `core id 1` on the input constraint `1`, already in the core set, is a no-op (§5.1): the core
-- set is unchanged, however often it is repeated.
example : runTop G none (State.init G none none) [.core [1], .core [1]] =
    some (State.init G none none) := by
  decide

-- A derived constraint is promoted once.
example : runTop G none (State.init G none none) [.red D setX0 none none, .core [2, 2], .core [2]] =
    some ⟨(2, D.normalize) :: initDb G, 3, none, none, (2, D.normalize) :: initDb G, true,
      false, none, none, [], [], none, none⟩ := by
  decide

-- `core id` needs at least one ID.
example : runTop G none (State.init G none none) [.core []] = none := by decide

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
  ⟨[.red C swap (some [.goal (.hash 1) [.rup ⟨[], 1⟩ [.id 6, .id 5, .id 2]] 7]) none,
    .step (.rup ⟨[], 1⟩ [.id 8, .id 3, .id 1])], .unsat 9⟩

example : checkRed F none proof = true := by decide

theorem F_unsat (σ : ℕ → Bool) : ¬ ∀ c ∈ F, c.Holds σ :=
  not_satisfiable_of_checkRed (obj := none) (P := proof) (pres := none) (by decide) rfl σ

-- The database goals may also be proved explicitly, each by RUP from its negation.
example : checkRed F none
    ⟨[.red C swap (some
        [.goal (.hash 1) [.rup ⟨[], 1⟩ [.id 6, .id 5, .id 2]] 7,
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

/-! ### Orders and dominance

The order `lex2` and its proofs are shared with the text tests
(`CslibFrontierTests.Logics.Propositional.VeriPBDomFixtures`). -/

/-- The fresh right variables `14`, `15`, and no fresh auxiliary variables. -/
def lex2W : TransVars := ⟨[14, 15], [], []⟩

example : lex2.defCheck [] lex2W lex2Trans lex2Refl = true := by decide

/-- The check gives a genuine preorder on assignments, for the order loaded over `x0, x1`. -/
theorem lex2_isPreorder : IsPreorder (ℕ → Bool) (LoadedOrder.Le ⟨lex2, [(0, true), (1, true)]⟩) :=
  LoadedOrder.isPreorder ⟨Order.good_of_defCheck (sp := []) (w := lex2W) (trans := lex2Trans)
    (refl := lex2Refl) (by decide), rfl, by simp [lex2]⟩

-- The relation `u1 ∨ v1` is not transitive (nor reflexive): the same transitivity proof fails.
example : Order.defCheck ⟨[10], [12], [], [], [⟨[(1, (10, true)), (1, (12, true))], 1⟩]⟩ []
    ⟨[14], [], []⟩ lex2Trans lex2Refl = false := by
  decide

-- Fresh right variables must be fresh.
example : lex2.defCheck [] ⟨[12, 15], [], []⟩ lex2Trans lex2Refl = false := by decide

/-- The strict order `u1 < v1` on one bit, `~u1 + v1 >= 2`. It is transitive, vacuously: its
premises `u < v` and `v < w` sum to the contradiction `4` already. It is not reflexive. -/
def ltBit : Order := ⟨[10], [12], [], [], [⟨[(1, (10, false)), (1, (12, true))], 2⟩]⟩

/-- Its transitivity proof: `1 + 2` is a contradiction. -/
def ltBitTrans : OrderProof := ⟨[.goal (.hash 1) [.pol [.id 1, .id 2, .add]] 4], none⟩

-- The transitivity check passes, and only the reflexivity check fails: the negation `5` of the
-- goal `~u1 + u1 >= 2` is not a contradiction.
example : (ltBit.transCheck ⟨[14], [], []⟩ ltBitTrans).isSome = true ∧
    ltBit.reflCheck 5 ⟨[.goal (.hash 1) [] 5], none⟩ = false ∧
    ltBit.defCheck [] ⟨[14], [], []⟩ ltBitTrans ⟨[.goal (.hash 1) [] 5], none⟩ = false := by
  decide

example : notAuxO.defCheck notAuxSpec ⟨[14], [21], [22]⟩ notAuxTrans notAuxRefl = true := by
  decide
-- The fresh auxiliary variables must be fresh, and as many as `a`; the specification must be
-- derived by witnesses on `a`.
example : notAuxO.defCheck notAuxSpec ⟨[14], [20], [22]⟩ notAuxTrans notAuxRefl = false ∧
    notAuxO.defCheck notAuxSpec ⟨[14], [], []⟩ notAuxTrans notAuxRefl = false ∧
    notAuxO.defCheck [⟨[(10, .one)], some [], none⟩, ⟨[(20, .zero)], some [], none⟩]
      ⟨[14], [21], [22]⟩ notAuxTrans notAuxRefl = false := by
  decide

-- The relation `∃ ρ, S⪯(x, y, ρ) ∧ O⪯(x, y, ρ)` is decided by trying the values of `$a1`:
-- `0 ⪯ 1` and `1 ⪯ 1`, and not `1 ⪯ 0`.
example : notAuxO.Le [false] [true] ∧ notAuxO.Le [true] [true] := by decide
example : ¬ notAuxO.Le [true] [false] := by decide

/-- The check gives a preorder on assignments, for `notAuxO` loaded over `x0`. -/
theorem notAux_isPreorder : IsPreorder (ℕ → Bool) (LoadedOrder.Le ⟨notAuxO, [(0, true)]⟩) :=
  LoadedOrder.isPreorder ⟨Order.good_of_defCheck (sp := notAuxSpec) (w := ⟨[14], [21], [22]⟩)
    (trans := notAuxTrans) (refl := notAuxRefl) (by decide), rfl, by decide⟩

/-- `x0 + x1 >= 1`, symmetric under swapping `x0` and `x1`. -/
def S : List PBConstr := [⟨[(1, (0, true)), (1, (1, true))], 1⟩]

/-- `~x0 + x1 >= 1`, that is `x0 ≤ x1`: the lex-leader constraint `z ⪯ z∘swap` for
`z = (x0, x1)`. -/
def lead : PBConstr := ⟨[(1, (0, false)), (1, (1, true))], 1⟩

/-- Symmetry breaking by dominance: define and load `lex2` over `x0, x1`, and derive `lead` by
`dom` with the swap. `¬lead` is `2`; goal `#1`, the order goal, follows from `¬lead`; goal `#2`
adds `O⪯(z, z↾ω)`, which is `lead` itself, as `3`, and `2 + 3` is the contradiction `4`; for an
objective, goal `#3` is `f|ω ≤ f`. `lead` is `5`. Then `soli ~x0 x1` logs the value `1` and adds
the improving constraint `6`, `f ≤ 0`, which with `1` gives the contradiction `7`. -/
def domProof : RedProof :=
  ⟨[.defOrder "lex2" lex2 [] lex2W lex2Trans lex2Refl, .loadOrder "lex2" [(0, true), (1, true)],
    .dom lead swap (some [.goal (.hash 2) [.pol [.id 2, .id 3, .add]] 4]) none,
    .soli [(0, false), (1, true)], .step (.pol [.id 1, .id 6, .add])],
    .bounds (some 1) 7 (some 1) none⟩

/-- The symmetric objective `x0 + x1`. -/
def fSym : Objective := ⟨[(0, 1), (1, 1)], 0⟩

example : checkRed S (some fSym) domProof = true := by decide

/-- The proof certifies that the optimum is `1`. -/
theorem fSym_optimum (σ : ℕ → Bool) (hσ : ∀ c ∈ S, c.Holds σ) : 1 ≤ fSym.eval σ :=
  le_eval_of_checkRed (pres := none) (P := domProof) (by decide) rfl σ hσ

-- The objective `x0 + 2 x1` is not symmetric: the swap raises it where `¬lead` holds, goal `#3`
-- fails, and the step is rejected. (Its optimum `1` is reached only at `x0`, which `lead`
-- excludes.)
example : checkRed S (some ⟨[(0, 1), (1, 2)], 0⟩) domProof = false := by decide

-- `dom` needs a loaded order.
example : checkRed S (some fSym) ⟨domProof.steps.drop 2, domProof.conclusion⟩ = false := by
  decide

-- Loaded over `x1, x0` instead, `lead` is not the lex-leader constraint: the order goal
-- `z↾ω ⪯ z` becomes `x0 ≤ x1`, which `¬lead` contradicts, goal `#2` is no longer refuted, and the
-- step is rejected.
example : checkRed S (some fSym)
    ⟨[.defOrder "lex2" lex2 [] lex2W lex2Trans lex2Refl, .loadOrder "lex2" [(1, true), (0, true)],
      .dom lead swap (some [.goal (.hash 2) [.pol [.id 2, .id 3, .add]] 4]) none],
      .noClaim⟩ = false := by
  decide

/-! ### An output section -/

/-- `G` preserving `x1`: the input. -/
def GI : Instance := ⟨G, none, some [1]⟩

/-- The output formula: `x0 >= 1` and `x1 >= 1`, preserving `x1`. -/
def GO : Instance := ⟨[D, ⟨[(1, (1, true))], 1⟩], none, some [1]⟩

/-- `red x0 >= 1 : x0 -> 1` moves only the unpreserved `x0`; `core id 2` puts it in the core set,
which is then the output formula. -/
def outProof : RedProof := ⟨[.red D setX0 none none, .core [2]], .noClaim⟩

/-- The `EQUIENUMERABLE` output of `outProof`, with an infinite bound. -/
def outGO : Output := ⟨.equienumerable, GO, none⟩

theorem checkRedOutput_outProof :
    checkRedOutput G none outProof (some [1]) ⟨.equienumerable, some GO⟩ = some outGO := by
  decide

-- Its guarantee: below any bound, the solutions of `G` and of `GO` project alike to `x1`.
example : semOutput GI none GO .equienumerable :=
  semOutput_of_checkRedOutput checkRedOutput_outProof

-- So `G` and `GO` have the same projected solutions.
example : projections G [1] = projections GO.constraints [1] :=
  projections_eq_of_checkRedOutput checkRedOutput_outProof rfl rfl

-- `x0` is not preserved in the input, so `EQUIENUMERABLE` with `x0` preserved is rejected.
example : checkRedOutput G none outProof (some [1])
    ⟨.equienumerable, some { GO with preserved := some [0, 1] }⟩ = none := by
  decide

end CslibFrontierTests.Logics.Propositional.VeriPBRed
