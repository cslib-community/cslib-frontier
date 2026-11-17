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

/-- The simp set `interp_norm` runs the oracle interpreter on a concrete program. To compute
`(OracleComp.interpret handler program).run s` for a `program` written out as a `do` block, a
proof calls `simp only [interp_norm, pmf_norm]`, adding the definitions to unfold and the local
facts to use, instead of listing the stepping lemmas.

The set pushes `OracleComp.interpret handler` through `pure`, `>>=`, `<$>`, queries and embedded
samples, and pushes `StateT.run` through the `StateT` operations this produces. It unfolds
`OracleComp.sumHandler`, so that a query tagged `Sum.inl` or `Sum.inr` reaches its own handler.
`CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm` lists the members.

What remains are the handler's calls at explicit states, `(oracle q).run s`, or
`StateT.run (fun s => …) s₀` for a handler given by a `fun`, joined by the `pure`, `>>=` and `<$>`
of the monad the handler lives in. The set holds no law of that monad. Over `PMF`, or under
`ProbComp.eval`, the set `pmf_norm` rewrites these to `PMF.pure`, `PMF.bind` and `PMF.map` and
normalizes them. The run of a part that is not concrete, such as an adversary, stays as
`(OracleComp.interpret handler (adversary x)).run s`.

Use the set where a hand list would name interpreter lemmas. It stands for all of them, and for
the single-step forms `OracleComp.run_interpret_pure`, `OracleComp.run_interpret_bind`,
`OracleComp.run_interpret_map`, `OracleComp.run_interpret_query` and
`ProbOracleComp.run_interpret_sample`, which a list using the set no longer names. Two kinds of
list are clearer written out: `StateT.run` laws alone, for a `StateT` program with no interpreter
in the goal, and a lone `OracleComp.sumHandler`, which unfolds one definition. A proof that takes
one named step with `rw`, or whose next step depends on the exact shape a hand list leaves, also
keeps its lemma names.

The set keeps a run in `OracleComp.interpret` form. That is the form to use when the statement, a
hypothesis or the lemma applied next speaks of `OracleComp.interpret`, and when the handler makes
oracle calls itself, as a reduction's handler does, so that the run is not a `PMF`. The set
`runWith_norm`, of `CslibFrontier.Languages.Probabilistic.Oracle.Norm`, instead folds a closed run
into `ProbOracleComp.runWith` and steps that, so a proof that continues with the `runWith` lemmas
uses it. It leaves out `OracleComp.interpret_bind` and `StateT.run_bind`, which would rewrite
inside a run before it is folded. For that reason a `simp only` call takes one of the two sets,
never both. -/
register_simp_attr interp_norm

end
