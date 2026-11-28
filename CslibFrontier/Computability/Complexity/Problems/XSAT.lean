/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Classes.NP.Witness

/-!
# The promise problem xSAT

`Cslib.Complexity.xSAT` is the promise problem of [Goldreich, Exercise 2.36][Goldreich2006DraftR1]
(following Even, Selman and Yacobi): its instances are pairs `(φ₁, φ₂)` of CNF formulas, the
yes-instances those with `φ₁` satisfiable and `φ₂` unsatisfiable, and the no-instances those with
`φ₁` unsatisfiable and `φ₂` satisfiable. It lies in the promise versions of both NP and coNP
(`Cslib.Complexity.xSAT_mem_PromiseNP_inter_promiseClass_coNP`, Part 1 of the exercise): the NP
set `{(φ₁, φ₂) | φ₁ ∈ SAT}` and the coNP set `{(φ₁, φ₂) | φ₂ ∈ UNSAT}` each contain the
yes-instances and avoid the no-instances. Part 2 of the exercise, that every promise problem in
`PromiseNP` is Cook-reducible to xSAT, is not formalized here.

## Main definitions

* `Cslib.Complexity.xSAT`: the promise problem xSAT.

## Main results

* `Cslib.Complexity.xSAT_mem_PromiseNP_inter_promiseClass_coNP`: xSAT is in promise-NP and in
  promise-coNP.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft of December 2006,
  Exercise 2.36][Goldreich2006DraftR1]
* [S. Even, A. L. Selman, Y. Yacobi, *The complexity of promise problems with applications to
  public-key cryptography*][EvenSelmanYacobi1984]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL PromiseProblem Turing.MultiTapeTM

/-- The promise problem **xSAT** [Goldreich, Exercise 2.36][Goldreich2006DraftR1]: pairs of CNF
formulas, with yes-instances `(φ₁, φ₂)` where `φ₁` is satisfiable and `φ₂` is not, and
no-instances where `φ₁` is unsatisfiable and `φ₂` is satisfiable. -/
def xSAT : PromiseProblem (CNF ℕ × CNF ℕ) where
  yes := SAT ×ˢ UNSAT
  no := UNSAT ×ˢ SAT
  disjoint := Set.disjoint_left.2 fun _ h h' => h'.1 h.1

@[simp] theorem yes_xSAT : xSAT.yes = SAT ×ˢ UNSAT := rfl

@[simp] theorem no_xSAT : xSAT.no = UNSAT ×ˢ SAT := rfl

/-- **xSAT is in promise-NP ∩ promise-coNP** [Goldreich, Exercise 2.36(1)][Goldreich2006DraftR1],
for the pair encoding of CNF formulas: the NP set of pairs with a satisfiable first formula and the
coNP set of pairs with an unsatisfiable second formula both separate the yes-instances from the
no-instances. -/
theorem xSAT_mem_PromiseNP_inter_promiseClass_coNP :
    xSAT ∈ PromiseNP (encPair encCNF encCNF) ∩ promiseClass (coNP (encPair encCNF encCNF)) :=
  ⟨⟨Prod.fst ⁻¹' SAT,
      PolyTimeReducible.mem_NP ⟨Prod.fst, .fst encCNF encCNF, fun _ => Iff.rfl⟩
        CookLevin.SAT_npComplete.1,
      fun _ h => h.1, Set.disjoint_left.2 fun _ h h' => h'.1 h⟩,
    ⟨Prod.snd ⁻¹' UNSAT,
      PolyTimeReducible.mem_coNP ⟨Prod.snd, .snd encCNF encCNF, fun _ => Iff.rfl⟩
        CookLevin.UNSAT_coNPComplete.1,
      fun _ h => h.2, Set.disjoint_left.2 fun _ h h' => h h'.2⟩⟩

end Cslib.Complexity
