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

Tags the lemmas of the simp set `interp_norm`, with which `simp only [interp_norm, pmf_norm]`
computes `(OracleComp.interpret handler program).run s` for a `program` written out as a `do`
block. The docstring of the attribute, in
`CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm.Init`, says what the set leaves, when to
use it and how it differs from `runWith_norm`.

The members are:

* the interpreter over program syntax: `OracleComp.interpret_pure`, `OracleComp.interpret_bind`,
  `OracleComp.interpret_map`, `OracleComp.interpret_query`, `ProbOracleComp.interpret_query`;
* the handler of a sum interface: `OracleComp.sumHandler`, which is unfolded;
* an embedded private sample and the handlers of uniform draws that answer it:
  `ProbOracleComp.interpret_sample`, `OracleComp.run_interpret_lift`,
  `ProbComp.interpret_unifFin`, `ProbComp.interpret_unifOracle`;
* `StateT.run` over what these leave: `StateT.run_pure`, `StateT.run_bind`, `StateT.run_map`,
  `StateT.run_lift`.

All are existing declarations except `ProbComp.interpret_unifOracle`, stated here for the set: it
is `OracleComp.evalWith_eq_interpret` at `ProbComp.unifOracle`, oriented so that the interpreter
is rewritten to `ProbComp.eval`.
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
