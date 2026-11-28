/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PlaistedGreenbaumCNF.Refutation
import Mathlib.Data.Fin.VecNotation

/-!
# Tautologies from LRAT refutations

Contraposition, `(p → q) → ¬q → ¬p`, over arbitrary `Prop` atoms, proved from an LRAT refutation
of the numbered Plaisted–Greenbaum transformation of its negation. The kernel runs the checker
through `decide`. The certificate was produced by CaDiCaL 3.0.0 (`cadical --lrat --no-binary`) on
the transformation in DIMACS form, without its deletion steps.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.PlaistedGreenbaumCNF.Refutation

open Cslib.Logic.PL Cslib.Logic.PL.Proposition
open Std.Tactic.BVDecide (LRAT.IntAction)

private abbrev p : Proposition (Fin 2) := .atom 0
private abbrev q : Proposition (Fin 2) := .atom 1

/-- Negation, written with the constructors. -/
private abbrev neg (A : Proposition (Fin 2)) : Proposition (Fin 2) := .imp A .falsum

/-- Contraposition, `(p → q) → ¬q → ¬p`. -/
private abbrev contraposition : Proposition (Fin 2) := .imp (.imp p q) (.imp (neg q) (neg p))

/-- A refutation of the numbered Plaisted–Greenbaum transformation of `¬contraposition`. -/
private def cert : Array LRAT.IntAction := #[
  .addRup 13 #[-9, 10] #[1, 2],
  .addRup 14 #[-9] #[3, 13],
  .addRup 15 #[3] #[14, 4],
  .addRup 16 #[-8] #[14, 5],
  .addRup 17 #[5] #[16, 6],
  .addRup 18 #[-7] #[16, 7],
  .addRup 19 #[1] #[18, 8],
  .addRup 20 #[-6] #[18, 9],
  .addRup 21 #[-2, 4] #[17, 10],
  .addRup 22 #[-2] #[11, 21],
  .addEmpty 23 #[15, 19, 22, 12]]

private theorem cert_ok :
    (neg contraposition).plaistedGreenbaumNumberedCNF.checkLRAT cert = true := by
  decide

/-- Contraposition over `Prop`, from the certificate. -/
example (a b : Prop) : (a → b) → ¬b → ¬a := by
  simpa using eval_prop_of_checkLRATRat (CNF.checkLRATRat_of_checkLRAT cert_ok) ![a, b]

/-- The same certificate gives the truth-table statement. -/
example (v : Fin 2 → Bool) : contraposition.eval v = true :=
  eval_of_checkLRATRat (CNF.checkLRATRat_of_checkLRAT cert_ok) v

/-- The accepted certificate with one wrong hint, 3 for 2 in its first step, is rejected. -/
example : (neg contraposition).plaistedGreenbaumNumberedCNF.checkLRAT
    (cert.set! 0 (.addRup 13 #[-9, 10] #[1, 3])) = false := by
  decide

end CslibFrontierTests.Logics.Propositional.PlaistedGreenbaumCNF.Refutation
