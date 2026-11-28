/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate.PropagateSound
-- `#guard` runs the propagation engine at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate.PropagateSound

/-! The soundness theorem of the propagation engine of the VeriPB elaborator
(`Cslib.Logic.PL.VeriPB.Elab.Engine.Built.rup_of_rupHints`) applies to an engine built from `x₁`
and `¬x₁`: the engine reports a conflict for the negation of `0 ≥ 1`, and so `0 ≥ 1` follows by
the kernel's reverse unit propagation from the database holding `x₁` as constraint `1` and `¬x₁`
as constraint `2`. For the satisfiable `x₁` alone the engine reports no conflict. -/

set_option linter.hashCommand false
set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBEngine

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Elab

/-- The constraint `x₁ ≥ 1`. -/
def pos : PBConstr := ⟨[(1, (1, true))], 1⟩

/-- The constraint `¬x₁ ≥ 1`. -/
def neg : PBConstr := ⟨[(1, (1, false))], 1⟩

/-- The contradiction `0 ≥ 1`. -/
def falsum : PBConstr := ⟨[], 1⟩

/-- The engine holding `x₁`, named by the kernel hint `1`. -/
def e₁ : Engine := (Engine.new.add pos (.id 1)).1

/-- The engine holding `x₁` and `¬x₁`, named by the kernel hints `1` and `2`. -/
def e₂ : Engine := (e₁.add neg (.id 2)).1

/-- The kernel database with `x₁` as `1` and `¬x₁` as `2`. -/
def db : List (ℕ × PBConstr) := [(1, pos), (2, neg)]

-- The engine finds a conflict for the negation of `0 ≥ 1` from `x₁` and `¬x₁`, and none from `x₁`.
#guard (e₂.rupHints falsum.negate).2.isSome
#guard !(e₁.rupHints falsum.negate).2.isSome

/-- The hints and constraints of the engine `e₂`, by engine index. -/
def D₂ : ℕ → Option (Hint × PBConstr) :=
  Function.update (Function.update (fun _ => none) (Engine.new.add pos (.id 1)).2
    (some (.id 1, pos))) (e₁.add neg (.id 2)).2 (some (.id 2, neg))

/-- The engine is built by its operations, holding `x₁` and `¬x₁` under their hints. -/
theorem e₂_built : Engine.Built e₂ D₂ := .add _ _ (.add _ _ .new)

/-- The database holds each constraint of the engine under its hint. -/
theorem db_holds : ∀ i h c, D₂ i = some (h, c) → resolve db falsum.negate h = some c := by
  intro i h c hD
  simp only [D₂, Function.update_apply] at hD
  split_ifs at hD <;> cases hD <;> rfl

/-- **The engine's verdict is a RUP proof**: given the conflict the engine reports (checked
above by `#guard`), `0 ≥ 1` follows from the database by the kernel's `rup`. -/
example (hr : (e₂.rupHints falsum.negate).2.isSome = true) : ∃ hs, rup db falsum hs = true :=
  e₂_built.rup_of_rupHints db_holds hr

end CslibFrontierTests.Logics.Propositional.VeriPBEngine
