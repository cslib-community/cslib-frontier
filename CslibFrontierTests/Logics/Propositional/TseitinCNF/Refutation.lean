/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.TseitinCNF.Refutation
import Mathlib.Data.Fin.VecNotation

/-!
# Tautologies from LRAT refutations

Contraposition, `(p → q) → ¬q → ¬p`, over arbitrary `Prop` atoms, proved from an LRAT refutation
of the numbered Tseitin transformation of its negation. The kernel runs the checker through
`decide`. The certificate was produced by the CDCL solver of #5946 on the transformation in
DIMACS form; its last step derives the empty clause from the unit clause asserting the negation
and the learned unit clause 31.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.TseitinCNF.Refutation

open Cslib.Logic.PL Cslib.Logic.PL.Proposition
open Std.Tactic.BVDecide (LRAT.IntAction)

private abbrev p : Proposition (Fin 2) := .atom 0
private abbrev q : Proposition (Fin 2) := .atom 1

/-- Negation, written with the constructors. -/
private abbrev neg (A : Proposition (Fin 2)) : Proposition (Fin 2) := .imp A .falsum

/-- Contraposition, `(p → q) → ¬q → ¬p`. -/
private abbrev contraposition : Proposition (Fin 2) := .imp (.imp p q) (.imp (neg q) (neg p))

/-- A refutation of the numbered Tseitin transformation of `¬contraposition`. -/
private def cert : Array LRAT.IntAction := #[
  .addRup 23 #[-5, -2] #[18, 19],
  .addRup 24 #[-3, -1, -5] #[22, 23],
  .addRup 25 #[7, -3, -5] #[12, 24],
  .addRup 26 #[-3, -5, 8] #[25, 10],
  .addRup 27 #[8, -3] #[9, 26],
  .addRup 28 #[-3, 9] #[27, 7],
  .addRup 29 #[9] #[6, 28],
  .addRup 30 #[-11, 10] #[29, 4],
  .addRup 31 #[-11] #[30, 5],
  .addEmpty 32 #[1, 31]]

private theorem cert_ok : (neg contraposition).tseitinNumberedCNF.checkLRAT cert = true := by
  decide

/-- Contraposition over `Prop`, from the certificate. -/
example (a b : Prop) : (a → b) → ¬b → ¬a := by
  simpa using eval_prop_of_checkLRAT cert_ok ![a, b]

/-- The same certificate gives the truth-table statement. -/
example (v : Fin 2 → Bool) : contraposition.eval v = true :=
  eval_of_checkLRAT cert_ok v

/-- The accepted certificate with one wrong hint, 20 for 19 in its first step, is rejected. -/
example : (neg contraposition).tseitinNumberedCNF.checkLRAT
    (cert.set! 0 (.addRup 23 #[-5, -2] #[18, 20])) = false := by
  decide

end CslibFrontierTests.Logics.Propositional.TseitinCNF.Refutation
