/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TQBF.QuantifierFree
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# TAUTOLOGY is coNP-complete

A *Boolean formula* is built from variables, the constants, negation, conjunction and disjunction
[Arora and Barak, Section 2.3][AroraBarak09]. These are the quantifier-free formulas of
`Cslib.Logic.PL.QBF` (`Cslib.Logic.PL.QBF.QuantifierFree`), encoded by their tokens in prefix
order (`Cslib.Complexity.encQBF`). `TAUTOLOGY` is the set of quantifier-free formulas over variables
numbered by natural numbers that are true under every assignment
[Arora and Barak, Example 2.23][AroraBarak07]. A formula with a quantifier is not in `TAUTOLOGY`;
this is a total language on `QBF ℕ`, not a promise problem. Restricting to formulas in conjunctive
normal form would make the problem polynomial-time, so general formulas are essential.

A quantifier-free formula is evaluated by one scan of its tokens from right to left, with a stack
of truth values (`Cslib.Logic.PL.QBF.evalStep`): a variable or a constant pushes its value, a
negation negates the top value, and a binary connective combines the two values on top. On the
tokens of a quantifier-free formula the scan pushes its value (`Cslib.Logic.PL.QBF.foldl_evalStep`),
in polynomial time when the assignment is the indicator of a list of variables
(`Cslib.Complexity.computableInPolyTime_evalTokens`). The shared scan and its
polynomial-time proof live in
`CslibFrontier.Computability.Complexity.Problems.TQBF.QuantifierFree`.

A formula is not a tautology when it has a quantifier or some assignment falsifies it, and a
falsifying assignment is the set of its true variables among the variables of the formula, a
subset witness (`Cslib.Complexity.mem_NP_of_subsetWitness`). So `TAUTOLOGY ∈ coNP`
(`Cslib.Complexity.TAUTOLOGY_mem_coNP`). Negation reduces `UNSAT` to `TAUTOLOGY`
(`Cslib.Complexity.UNSAT_reducible_TAUTOLOGY`), so `TAUTOLOGY` is coNP-complete by the Cook–Levin
theorem (`Cslib.Complexity.TAUTOLOGY_coNPComplete`).

## Main definitions

* `Cslib.Complexity.TAUTOLOGY`: the quantifier-free formulas true under every assignment.

## Main results

* `Cslib.Complexity.TAUTOLOGY_mem_coNP`, `Cslib.Complexity.UNSAT_reducible_TAUTOLOGY`,
  `Cslib.Complexity.TAUTOLOGY_coNPHard`, `Cslib.Complexity.TAUTOLOGY_coNPComplete`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Logic.PL ComputableInPolyTime TQBF

/-- **TAUTOLOGY**: the Boolean formulas, over variables numbered by natural numbers, that are true
under every assignment [Arora and Barak, Example 2.23][AroraBarak07]. Formulas with quantifiers
are not members. -/
def TAUTOLOGY : Set (QBF ℕ) := {φ | φ.QuantifierFree ∧ ∀ σ : ℕ → Bool, φ.eval σ = true}

theorem mem_TAUTOLOGY {φ : QBF ℕ} :
    φ ∈ TAUTOLOGY ↔ φ.QuantifierFree ∧ ∀ σ : ℕ → Bool, φ.eval σ = true := Iff.rfl

/-- The negation of a formula in conjunctive normal form is a tautology exactly when the formula
is unsatisfiable. -/
theorem not_ofCNF_mem_TAUTOLOGY_iff {φ : CNF ℕ} : (QBF.ofCNF φ).not ∈ TAUTOLOGY ↔ φ ∈ UNSAT := by
  simp [mem_TAUTOLOGY, QBF.quantifierFree_ofCNF, mem_UNSAT, CNF.Satisfiable]

/-- The complement of `TAUTOLOGY` as a subset problem: a formula is not a tautology exactly when
it has a quantifier or the set of its true variables, among the variables of its tokens, makes
it false. -/
private theorem compl_TAUTOLOGY_eq :
    TAUTOLOGYᶜ = {φ | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ φ.tokens.map Prod.snd) ∧
      (¬φ.QuantifierFree ∨ φ.eval (fun v => decide (v ∈ S)) = false)} := by
  ext φ
  simp only [Set.mem_compl_iff, mem_TAUTOLOGY, not_and_or, not_forall, Bool.not_eq_true,
    Set.mem_ofPred_eq]
  constructor
  · rintro (h | ⟨σ, hσ⟩)
    · exact ⟨∅, by simp, .inl h⟩
    · refine ⟨((φ.tokens.map Prod.snd).filter σ).toFinset, fun v hv => ?_, .inr ?_⟩
      · exact List.mem_of_mem_filter (List.mem_toFinset.1 hv)
      · rw [← hσ]
        refine QBF.eval_congr fun w hw => ?_
        have hmem : w ∈ φ.tokens.map Prod.snd :=
          List.mem_map.2 ⟨_, QBF.mem_tokens_of_mem_freeVars hw, rfl⟩
        by_cases h : σ w <;> simp [h, hmem]
  · rintro ⟨S, -, h | h⟩
    · exact .inl h
    · exact .inr ⟨_, h⟩

/-- **TAUTOLOGY is in coNP:** a non-tautology has a quantifier or a falsifying assignment, given by
its true variables. -/
theorem TAUTOLOGY_mem_coNP : TAUTOLOGY ∈ coNP encQBF := by
  rw [mem_coNP, compl_TAUTOLOGY_eq]
  refine mem_NP_of_subsetWitness (encγ := encNat) (vs := fun φ : QBF ℕ => φ.tokens.map Prod.snd)
    (check := fun p : QBF ℕ × List ℕ => !decide p.1.QuantifierFree ||
      !(p.1.tokens.reverse.foldl (QBF.evalStep fun v => p.2.contains v) []).headD false)
    (by fun_prop) ?_ fun φ l _ _ => ?_
  · have h₁ : ComputableInPolyTime (fun p : QBF ℕ × List ℕ => decide p.1.QuantifierFree)
        (encPair encQBF (encList encNat)) encBool :=
      computableInPolyTime_decide_quantifierFree.comp (fst _ _)
    have h₂ := computableInPolyTime_evalTokens
    fun_prop
  · by_cases hφ : φ.QuantifierFree
    · simp [hφ, QBF.foldl_evalStep hφ]
    · simp [hφ]

/-- **UNSAT reduces to TAUTOLOGY** by negation. -/
theorem UNSAT_reducible_TAUTOLOGY : PolyTimeReducible encCNF encQBF UNSAT TAUTOLOGY :=
  ⟨fun φ => (QBF.ofCNF φ).not, by unfold encCNF; fun_prop,
    fun _ => not_ofCNF_mem_TAUTOLOGY_iff.symm⟩

/-- TAUTOLOGY is coNP-hard. -/
theorem TAUTOLOGY_coNPHard : coNPHard encQBF TAUTOLOGY :=
  CookLevin.UNSAT_coNPComplete.2.trans UNSAT_reducible_TAUTOLOGY

/-- **TAUTOLOGY is coNP-complete** [Arora and Barak, Example 2.23][AroraBarak07]. -/
theorem TAUTOLOGY_coNPComplete : coNPComplete encQBF TAUTOLOGY :=
  ⟨TAUTOLOGY_mem_coNP, TAUTOLOGY_coNPHard⟩

end Cslib.Complexity
