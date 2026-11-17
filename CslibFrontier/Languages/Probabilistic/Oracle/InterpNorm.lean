/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Norm
public import CslibFrontier.Languages.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm.Init
public import CslibFrontier.Languages.Probabilistic.Simulation

/-!
# Stepping the oracle interpreter through a concrete program

Tags the lemmas of the simp set `interp_norm`. To compute
`(OracleComp.interpret handler program).run s` for a `program` written out as a `do` block, a
proof calls `simp only [interp_norm, pmf_norm]`, adding the definitions to unfold and the local
facts to use, instead of listing the stepping lemmas:

* the interpreter over program syntax: `OracleComp.interpret_pure`, `OracleComp.interpret_bind`,
  `OracleComp.interpret_map`, `OracleComp.interpret_query`, `ProbOracleComp.interpret_query`;
* the handler of a sum interface: `OracleComp.sumHandler` is unfolded, so that a query tagged
  `Sum.inl` or `Sum.inr` reaches its own handler;
* an embedded private sample and the handlers of uniform draws that answer it:
  `ProbOracleComp.interpret_sample`, `OracleComp.run_interpret_lift`,
  `ProbComp.interpret_unifFin`, `ProbComp.interpret_unifOracle`;
* `StateT.run` over what these leave: `StateT.run_pure`, `StateT.run_bind`, `StateT.run_map`,
  `StateT.run_lift`.

The result is made of the handler's calls at explicit states, written `(oracle q).run s`, or
`StateT.run (fun s => …) s₀` when the handler is given by a `fun`, joined by the `pure`, `>>=` and
`<$>` of the monad the handler lives in. The set holds no law of that monad. Over `PMF`, or under
`ProbComp.eval`, the set `pmf_norm` rewrites these to `PMF.pure`, `PMF.bind` and `PMF.map` and
normalizes them. A part of the program that is not concrete, such as an adversary, stays as
`(OracleComp.interpret handler (adversary x)).run s`.

## When to use it

Use the set where a hand list would name interpreter lemmas: it stands for all of them, and for
the single-step forms `OracleComp.run_interpret_pure`, `OracleComp.run_interpret_bind`,
`OracleComp.run_interpret_map`, `OracleComp.run_interpret_query` and
`ProbOracleComp.run_interpret_sample`, which a list using the set no longer names.

Two kinds of list are clearer written out: `StateT.run` laws alone, for a `StateT` program with no
interpreter in the goal, and a lone `OracleComp.sumHandler`, which unfolds one definition. A proof
that takes one named step with `rw`, or whose next step depends on the exact shape a hand list
leaves, also keeps its lemma names.

## `interp_norm` and `runWith_norm`

`interp_norm` keeps a run in `OracleComp.interpret` form. That is the form to use when the
statement, a hypothesis or the lemma applied next speaks of `OracleComp.interpret`, and when the
handler makes oracle calls itself, as a reduction's handler does, so that the run is not a `PMF`.

`runWith_norm`, of `CslibFrontier.Languages.Probabilistic.Oracle.Norm`, folds a closed run into
`ProbOracleComp.runWith` and steps that instead, so a proof that continues with the `runWith`
lemmas uses it. It leaves out `OracleComp.interpret_bind` and `StateT.run_bind`, which would
rewrite inside a run before it is folded. For that reason a `simp only` call takes one of the two
sets, never both.

## Main results

* `Cslib.ProbComp.interpret_unifOracle`: answering each uniform draw of a closed program by its
  distribution gives `ProbComp.eval` of the program.
-/

public section

namespace Cslib

/-- Answering each uniform draw of a closed program by its distribution gives the program's law.

This is `OracleComp.evalWith_eq_interpret` at `ProbComp.unifOracle`, read from right to left and
with `ProbComp.eval` folded. Tagging that lemma in reverse would not do for `interp_norm`: it
would turn every interpretation in `PMF` into `OracleComp.evalWith`, and would leave
`OracleComp.evalWith ProbComp.unifOracle program` here, which the `ProbComp.eval` lemmas of
`pmf_norm` do not match. -/
theorem ProbComp.interpret_unifOracle {α : Type} (program : ProbComp α) :
    OracleComp.interpret ProbComp.unifOracle program = ProbComp.eval program :=
  (OracleComp.evalWith_eq_interpret _ _).symm

end Cslib

attribute [interp_norm]
  Cslib.OracleComp.interpret_pure
  Cslib.OracleComp.interpret_bind
  Cslib.OracleComp.interpret_map
  Cslib.OracleComp.interpret_query
  Cslib.OracleComp.sumHandler
  Cslib.ProbOracleComp.interpret_query
  Cslib.ProbOracleComp.interpret_sample
  Cslib.ProbComp.interpret_unifFin
  Cslib.ProbComp.interpret_unifOracle
  Cslib.OracleComp.run_interpret_lift
  StateT.run_pure
  StateT.run_bind
  StateT.run_map
  StateT.run_lift

end
