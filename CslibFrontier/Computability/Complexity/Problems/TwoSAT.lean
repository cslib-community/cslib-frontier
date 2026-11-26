/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Logics.Propositional.CNF.TwoCNF

/-!
# 2SAT

`Cslib.Complexity.TwoSAT` is the set of satisfiable formulas in conjunctive normal form whose
clauses have at most two literals, over variables numbered by `ℕ` and encoded as for `SAT`
(`Cslib.Complexity.encCNF`) [Papadimitriou94]. A formula outside
`TwoSAT` has a clause of width greater than two, the empty clause, or a variable `x` with a path
from `x` to `¬x` and one back in its implication graph
(`Cslib.Complexity.notMem_TwoSAT_iff`), by the theorem of Aspvall, Plass and Tarjan
(`Cslib.Logic.PL.CNF.not_satisfiable_iff_of_width_le_two`) [AspvallPlassTarjan1979].

## Main definitions

* `Cslib.Complexity.TwoSAT`.

## Main results

* `Cslib.Complexity.notMem_TwoSAT_iff`: the formulas outside `TwoSAT`.

## References

* [B. Aspvall, M. F. Plass, R. E. Tarjan, *A linear-time algorithm for testing the truth of
  certain quantified boolean formulas*][AspvallPlassTarjan1979]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL

/-- The satisfiable formulas whose clauses have at most two literals. -/
def TwoSAT : Set (CNF ℕ) := {φ | (∀ c ∈ φ, c.length ≤ 2) ∧ φ.Satisfiable}

theorem mem_TwoSAT {φ : CNF ℕ} : φ ∈ TwoSAT ↔ (∀ c ∈ φ, c.length ≤ 2) ∧ φ.Satisfiable :=
  Iff.rfl

/-- **The formulas outside `TwoSAT`**: those with a clause of width greater than two, the empty
clause, or a variable `x` with a path from `x` to `¬x` and one back in the implication graph. -/
theorem notMem_TwoSAT_iff {φ : CNF ℕ} :
    φ ∉ TwoSAT ↔ (∃ c ∈ φ, 2 < c.length) ∨ [] ∈ φ ∨
      ∃ v, Relation.ReflTransGen φ.Implies (v, true) (v, false) ∧
        Relation.ReflTransGen φ.Implies (v, false) (v, true) := by
  by_cases hw : ∀ c ∈ φ, c.length ≤ 2
  · have hno : ¬∃ c ∈ φ, 2 < c.length := fun ⟨c, hc, h⟩ => h.not_ge (hw c hc)
    simp only [mem_TwoSAT, iff_true_intro hw, true_and, hno, false_or,
      CNF.not_satisfiable_iff_of_width_le_two hw]
  · refine iff_of_true (fun h => hw h.1) (Or.inl ?_)
    simpa only [not_forall, exists_prop, not_le] using hw

end Cslib.Complexity
