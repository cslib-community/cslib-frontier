/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Iteration

/-!
# Sequential composition of bounded probabilistic iteration

Library infrastructure (no cited result): splits `OracleComp.iterate (a + b) step initial` into
a prefix of `a` iterations followed by `b` iterations.

## Main results

* `Cslib.OracleComp.iterate_add`: running `a + b` iterations equals running `a` iterations and
  continuing with `b` iterations.
-/

public section

namespace Cslib.OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {State : Type v}

/-- Library infrastructure (no cited result): running `a + b` iterations of `step` equals running
`a` iterations and continuing from the resulting state for `b` iterations. -/
theorem iterate_add (a b : ℕ) (step : State → OracleComp spec State) (initial : State) :
    iterate (a + b) step initial = iterate a step initial >>= iterate b step := by
  induction b with
  | zero =>
    rw [Nat.add_zero]
    change iterate a step initial = iterate a step initial >>= pure
    exact (bind_pure _).symm
  | succ b ih => rw [Nat.add_succ, iterate_succ, ih, bind_assoc]; rfl

end Cslib.OracleComp
