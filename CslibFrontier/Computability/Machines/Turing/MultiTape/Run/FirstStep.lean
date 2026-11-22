/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Deterministic`)

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# The first step of a run

`Turing.MultiTapeTM.runFrom_succ` splits a run of `t + 1` steps after its first `t` steps. A proof
that follows a machine from a given configuration needs the other split, after the first step:
`Turing.MultiTapeTM.runFrom_succ_eq_step`, which is `Function.iterate_succ_apply` read through
`runFrom`.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- A run of one more step, split after its first step. -/
lemma runFrom_succ_eq_step (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input)
    (n : ℕ) : tm.runFrom c (n + 1) = tm.runFrom (tm.step c) n :=
  Function.iterate_succ_apply _ _ _

end Turing.MultiTapeTM
