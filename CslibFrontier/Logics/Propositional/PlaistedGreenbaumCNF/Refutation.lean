/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Logics.Propositional.PlaistedGreenbaumCNF.Numbered

/-! # Tautologies from LRAT refutations

A proposition `A` over the atoms `Fin n` is a tautology when its negation `¬A`, written
`A → ⊥`, has no model. The numbered Plaisted–Greenbaum transformation of `¬A` is equisatisfiable
with `¬A` (`Cslib.Logic.PL.Proposition.satisfiable_plaistedGreenbaumNumberedCNF_iff`), and an
LRAT certificate that `Cslib.Logic.PL.CNF.checkLRAT` accepts shows that a CNF has no model
(`Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRAT`). So an accepted certificate for the
transformation of `¬A` proves that `A` is true under every Boolean valuation
(`Cslib.Logic.PL.Proposition.eval_of_checkLRAT`), and then, classically, under every valuation
in `Prop` (`Cslib.Logic.PL.Proposition.eval_prop_of_checkLRAT`).

The checker is written with structural recursion, so `decide` can prove that it accepts a given
certificate, with the kernel evaluating the checker. Proving a goal this way uses no native
evaluation; only finding the certificate does, and that step is untrusted.

Only the direction from a model of `¬A` to a model of the transformation is used here. On the
goals of `lrat_tauto`'s benchmarks the Plaisted–Greenbaum transformation has about half the
clauses of the Tseitin transformation (`Cslib.Logic.PL.Proposition.tseitinCNF`), and its
certificates checked faster in the kernel than those for a numbered Tseitin transformation.

## Main results

* `Cslib.Logic.PL.Proposition.eval_of_checkLRAT`: a refuted negation gives a truth-table
  tautology.
* `Cslib.Logic.PL.Proposition.eval_prop_of_checkLRAT`: the same over `Prop`.
-/

public section

namespace Cslib.Logic.PL.Proposition

open Std.Tactic.BVDecide (LRAT.IntAction)

variable {n : ℕ}

/-- **A refuted negation is a tautology.** If the checker accepts a certificate for the numbered
Plaisted–Greenbaum transformation of `¬A`, then `A` is true under every Boolean valuation. -/
theorem eval_of_checkLRAT {A : Proposition (Fin n)} {cert : Array LRAT.IntAction}
    (h : (imp A falsum).plaistedGreenbaumNumberedCNF.checkLRAT cert = true) (v : Fin n → Bool) :
    A.eval v = true := by
  by_contra hv
  refine CNF.not_satisfiable_of_checkLRAT h
    ((satisfiable_plaistedGreenbaumNumberedCNF_iff _).2 ⟨v, ?_⟩)
  simpa using hv

/-- **A refuted negation is a tautology over `Prop`.** If the checker accepts a certificate for
the numbered Plaisted–Greenbaum transformation of `¬A`, then `A` holds under every valuation in
`Prop`. The proof is classical. -/
theorem eval_prop_of_checkLRAT {A : Proposition (Fin n)} {cert : Array LRAT.IntAction}
    (h : (imp A falsum).plaistedGreenbaumNumberedCNF.checkLRAT cert = true) (v : Fin n → Prop) :
    A.eval v :=
  eval_prop_of_forall_eval_bool A (eval_of_checkLRAT h) v

end Cslib.Logic.PL.Proposition
