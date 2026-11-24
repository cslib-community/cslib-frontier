/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Languages.Probabilistic.QueryCount

/-!
# Query-cost bounds for bounded probabilistic iteration

Library infrastructure (no cited result): lifts a uniform per-step `OracleComp.IsCostBounded`
budget `c` to an additive budget `count * c` for `OracleComp.iterate count step initial`.

## Main results

* `Cslib.OracleComp.IsCostBounded.iterate`: `count` iterations of steps bounded by `c` are
  cost-bounded by `count * c`.
-/

public section

namespace Cslib.OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {State : Type v}

/-- Library infrastructure (no cited result): `count` iterations of a step whose calls each cost
at most `c` are cost-bounded by `count * c`. -/
theorem IsCostBounded.iterate {cost : ι → ℕ} {step : State → OracleComp spec State} {c : ℕ}
    (hstep : ∀ s, IsCostBounded cost (step s) c) (count : ℕ) (initial : State) :
    IsCostBounded cost (OracleComp.iterate count step initial) (count * c) := by
  induction count generalizing initial with
  | zero =>
    rw [OracleComp.iterate_zero, Nat.zero_mul]
    exact IsCostBounded.pure initial 0
  | succ count ih =>
    rw [OracleComp.iterate_succ_bind, Nat.succ_mul, Nat.add_comm]
    exact (hstep initial).bind fun s => ih s

end Cslib.OracleComp
