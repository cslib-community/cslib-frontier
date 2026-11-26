/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteEquivalence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Rule directions, an unreachable singleton, and a noncanonical two-coordinate move. -/

open Cslib.Complexity.NCL
open HWord.RewriteGadget Cslib.PostCorrespondence

namespace CslibFrontierTests.RewriteEquivalence

private def rules : Fin 2 → Rule 2 :=
  ![⟨0, 0, 0, 1, Or.inl rfl⟩, ⟨0, 0, 1, 0, Or.inr rfl⟩]

private theorem source_move : Rewrites (RuleSet rules) [0, 0] [1, 0] :=
  ⟨[], (rules 1).domino, [], ⟨1, Or.inl rfl⟩, rfl, rfl⟩

example : HWord.Reachable (compatibility rules) (word ![0, 0]) (word ![1, 0]) :=
  (word_reachable_iff rules (by decide) _ _).mpr (.single source_move)

example : HWord.Reachable (compatibility rules) (word ![1, 0]) (word ![0, 0]) :=
  (word_reachable_iff rules (by decide) _ _).mpr (.single (symm source_move))

private theorem no_singleton_rewrite (a : Fin 2) (t : List (Fin 2)) :
    ¬Rewrites (RuleSet rules) [a] t := by
  rintro ⟨before, domino, after, ⟨i, hd | hd⟩, hs, _⟩
  all_goals
    subst domino
    have h := congrArg List.length hs
    simp only [List.length_cons, List.length_nil, List.length_append, Rule.domino,
      Rule.reverse] at h
    omega

example : ¬HWord.Reachable (compatibility rules)
    (word (fun _ : Fin 1 => (0 : Fin 2))) (word (fun _ : Fin 1 => 1)) := by
  intro h
  have hs := (word_reachable_iff rules (by decide) _ _).mp h
  have he := (Relation.reflTransGen_iff_eq (no_singleton_rewrite 0)).mp hs
  simp [List.ofFn_succ] at he

private noncomputable def marked (a b : Fin 2) : Fin 7 → Fin (Fintype.card (Symbol 2 2)) :=
  code ∘ ![.start, .pair none (some 0), .marker 0, .pair (some a) (some b),
    .marker 1, .pair (some 0) none, .finish]

private theorem marked_legal (a b : Fin 2) : HWord.Legal (compatibility rules) (marked a b) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    apply (compatibility_adj rules _ _).mpr
    fin_cases a <;> fin_cases b <;> simp [Compatible, rules]

private theorem marked_step : HWord.Step (compatibility rules) (marked 0 0) (marked 1 1) := by
  refine ⟨marked_legal 0 0, marked_legal 1 1, 3, ?_, ?_⟩
  · intro h
    have he := code.injective h
    simp at he
  · intro j hj
    fin_cases j <;> simp_all [marked]

example : Relation.RelatesWithinSteps (Rewrites (RuleSet rules))
    (List.ofFn (readout rules (marked 0 0) (marked_legal 0 0)))
    (List.ofFn (readout rules (marked 1 1) (marked_legal 1 1))) 2 := by
  apply step_readout rules marked_step
  · simp [marked]
  · simp [marked]

end CslibFrontierTests.RewriteEquivalence
