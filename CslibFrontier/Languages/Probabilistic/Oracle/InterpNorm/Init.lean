/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp set `interp_norm`

Declares the simp set `interp_norm`, in a file of its own because an attribute cannot be used in
the file declaring it. `CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm` tags its lemmas.

## Main definitions

* `interp_norm`: steps `OracleComp.interpret handler program` and the `StateT.run` around it
  through the syntax of a concrete `program`, leaving the handler calls and the base monad's
  `pure`, `>>=` and `<$>`.
-/

public meta section

/-- The simp set `interp_norm` runs the interpreter on a concrete program: it pushes
`OracleComp.interpret handler` through `pure`, `>>=`, `<$>`, queries and embedded samples, and
pushes `StateT.run` through the `StateT` operations this produces. It unfolds
`OracleComp.sumHandler`, so that a query tagged `Sum.inl` or `Sum.inr` reaches its own handler.

What remains are the handler's calls at explicit states, `(oracle q).run s`, or
`StateT.run (fun s => …) s₀` for a handler given by a `fun`, joined by the `pure`, `>>=` and `<$>`
of the base monad, which `pmf_norm` normalizes when that monad is `PMF`:
`simp only [interp_norm, pmf_norm]`. The run of a part that is not concrete, such as an adversary,
stays as `(OracleComp.interpret handler (adversary x)).run s`.

Use it in place of a hand list that names interpreter lemmas. A list of `StateT.run` laws alone,
for a `StateT` program with no interpreter, or a lone `OracleComp.sumHandler` is clearer written
out.

The set keeps the run in `OracleComp.interpret` form, the form of public statements and of
handlers that make oracle calls themselves. The set `runWith_norm` instead folds a closed run into
`ProbOracleComp.runWith` and keeps black-box adversary runs intact; it omits
`OracleComp.interpret_bind` and `StateT.run_bind` for that reason. Use one or the other in a
`simp only` call, never both. -/
register_simp_attr interp_norm

end
