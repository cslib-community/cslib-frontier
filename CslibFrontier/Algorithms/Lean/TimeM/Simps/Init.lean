/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp set `time_simps`

Declares the simp set `time_simps`, in a file of its own because an attribute cannot be used in
the file declaring it. `CslibFrontier.Algorithms.Lean.TimeM.Simps` tags the laws of the time monad
and defines the tactic `time_spec` that uses the set.

## Main definitions

* `time_simps`: pushes `.ret` and `.time` through a program in `Cslib.Algorithms.Lean.TimeM`.
-/

public meta section

/-- The simp set `time_simps` pushes the projections `.ret` and `.time` of
`Cslib.Algorithms.Lean.TimeM` through a program: through `>>=`, `pure`, `<$>`, `<*>`, `tick` and
the loop combinators, and through every program whose return value or cost is stated as an
equation tagged `@[time_simps]`. It also normalizes the length, sum and map of a `cons` or empty
list and removes the zero cost of `pure`.

Use it as `simp only [time_simps]`, before any call of `simp` with its default set. The cost of a
`List.foldlM` is rewritten by `time_foldlM_eq_sum_map`, whose side condition says that the step
cost ignores the accumulator. In `simp [time_simps]` the default set first rewrites the step
`do tick 1; pure (g acc x)` to `(fun _ => g acc x) <$> tick 1` (`bind_pure_comp`), and the fold
lemma is then not applied. -/
register_simp_attr time_simps

end
