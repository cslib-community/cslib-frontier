/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Source
public import CslibFrontier.Computability.Complexity.Classes.Space.TQBF.Prenex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.List.Counting

/-!
# Regular source instances in polynomial time

Prepare arbitrary upstream `TQBFCNF` inputs for the NCL emitter. Reject free variables, replace
an empty conjunction by a fixed true instance, and replace a formula containing an empty clause
by a fixed false instance. The remaining source has a nonempty prefix and nonempty clauses.
Repeated binders retain their ordinary shadowing semantics.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Source.Input`: upstream alternating prenex CNF inputs.
* `Cslib.Complexity.NCL.QBF.Source.Regular`: closed inputs with a nonempty prefix, matrix and
  clauses.
* `Cslib.Complexity.NCL.QBF.Source.normalize`: replace the degenerate inputs by fixed instances.

## Main results

* `Cslib.Complexity.NCL.QBF.Source.normalize_regular`: every normalized input is regular.
* `Cslib.Complexity.NCL.QBF.Source.normalize_mem_iff`: normalization preserves `TQBFCNF`.
* `Cslib.Complexity.NCL.QBF.Source.computableInPolyTime_normalize`: normalization is
  polynomial-time in the upstream binary encoding.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Source

open Cslib.Logic.PL Cslib.Logic.PL.QBF

/-- An upstream alternating prenex CNF input, with variable names encoded in binary. -/
abbrev Input := List (ℕ × ℕ) × CNF ℕ

/-- Closed inputs with at least one quantifier round, one clause, and one literal per clause. -/
@[expose] def Regular (x : Input) : Prop :=
  (rounds x.1 (ofCNF x.2)).Closed ∧ x.1 ≠ [] ∧ x.2 ≠ [] ∧ [] ∉ x.2

/-- A fixed true regular source: `∃ x, ∀ y, x`. -/
@[expose] def yesInput : Input := ([(0, 1)], [[(0, true)]])

/-- A fixed false regular source: `∃ x, ∀ y, y`. -/
@[expose] def noInput : Input := ([(0, 1)], [[(1, true)]])

/-- Every literal's name occurs in the prefix, including shadowed names. -/
@[expose] def isClosedInput (x : Input) : Bool :=
  x.2.all fun c => c.all fun l => decide (l.1 ∈ roundVars x.1)

private theorem isClosedInput_eq_true_iff (x : Input) :
    isClosedInput x = true ↔ (rounds x.1 (ofCNF x.2)).Closed := by
  simp only [isClosedInput, List.all_eq_true, decide_eq_true_eq, closed_rounds_ofCNF_iff]

/-- Normalize without evaluating the quantified formula. -/
@[expose] def normalize (x : Input) : Input :=
  if isClosedInput x then
    if x.2.isEmpty then yesInput else if x.2.any List.isEmpty then noInput else x
  else noInput

private theorem yes_regular : Regular yesInput := by unfold Regular yesInput; decide +kernel

private theorem no_regular : Regular noInput := by unfold Regular noInput; decide +kernel

private theorem yes_mem : yesInput ∈ TQBFCNF := by unfold TQBFCNF TQBF yesInput; decide +kernel

private theorem no_notMem : noInput ∉ TQBFCNF := by unfold TQBFCNF TQBF noInput; decide +kernel

private theorem prefix_nonempty (ps : List (ℕ × ℕ)) (φ : CNF ℕ)
    (hc : (rounds ps (ofCNF φ)).Closed) (hφ : φ ≠ []) (he : [] ∉ φ) : ps ≠ [] := by
  intro hp
  subst ps
  cases φ with
  | nil => exact hφ rfl
  | cons c cs =>
    cases c with
    | nil => exact he (List.mem_cons_self ..)
    | cons l ls =>
      have hv := (closed_rounds_ofCNF_iff [] ((l :: ls) :: cs)).1 hc _
        (List.mem_cons_self ..) l (List.mem_cons_self ..)
      simp [roundVars] at hv

/-- Every normalized input has the nondegenerate closed source shape used by the emitter. -/
theorem normalize_regular (x : Input) : Regular (normalize x) := by
  unfold normalize
  split_ifs with hc hnil hempty
  · exact yes_regular
  · exact no_regular
  · have hclosed := (isClosedInput_eq_true_iff x).1 hc
    have hφ : x.2 ≠ [] := fun he => hnil (by simp [he])
    have he : [] ∉ x.2 := fun hm => hempty (List.any_eq_true.2 ⟨[], hm, rfl⟩)
    exact ⟨hclosed, prefix_nonempty x.1 x.2 hclosed hφ he, hφ, he⟩
  · exact no_regular

private theorem eval_rounds_constant (ps : List (ℕ × ℕ)) (φ : QBF ℕ) (b : Bool)
    (h : ∀ σ, φ.eval σ = b) : ∀ σ, (rounds ps φ).eval σ = b := by
  induction ps with
  | nil => exact h
  | cons p ps ih =>
    intro σ
    simp only [rounds] at ih
    simp only [rounds, List.foldr_cons, eval_ex, eval_all, ih, Bool.and_self, Bool.or_self]

private theorem empty_mem (ps : List (ℕ × ℕ)) : (ps, []) ∈ TQBFCNF :=
  ⟨(closed_rounds_ofCNF_iff ps []).2 (by simp),
    eval_rounds_constant ps (ofCNF []) true (fun _ => rfl) _⟩

private theorem empty_clause_notMem (ps : List (ℕ × ℕ)) (φ : CNF ℕ) (he : [] ∈ φ) :
    (ps, φ) ∉ TQBFCNF := by
  have hfalse : ∀ σ : ℕ → Bool, (ofCNF φ).eval σ = false := by
    intro σ
    rw [eval_ofCNF, Bool.eq_false_iff]
    intro htrue
    exact Bool.noConfusion ((CNF.eval_eq_true_iff σ φ).1 htrue [] he)
  have hf := eval_rounds_constant ps (ofCNF φ) false hfalse (fun _ => false)
  exact fun h => Bool.noConfusion (hf.symm.trans h.2)

/-- **Normalization preserves the full upstream source language**, including inputs with free
variables, empty prefixes, empty matrices, and empty clauses. -/
theorem normalize_mem_iff (x : Input) : normalize x ∈ TQBFCNF ↔ x ∈ TQBFCNF := by
  unfold normalize
  split_ifs with hc hnil hempty
  · have he : x.2 = [] := List.isEmpty_iff.1 hnil
    have hx : x ∈ TQBFCNF := by
      change (x.1, x.2) ∈ TQBFCNF
      rw [he]
      exact empty_mem x.1
    exact iff_of_true yes_mem hx
  · have he : [] ∈ x.2 := by
      obtain ⟨c, hm, he⟩ := List.any_eq_true.1 hempty
      exact (List.isEmpty_iff.1 he) ▸ hm
    exact iff_of_false no_notMem (empty_clause_notMem x.1 x.2 he)
  · rfl
  · exact iff_of_false no_notMem (fun h => hc ((isClosedInput_eq_true_iff x).2 h.1))

open _root_.Turing.MultiTapeTM

/-- Normalization is polynomial-time in the upstream alternating prenex CNF encoding. -/
@[fun_prop]
theorem computableInPolyTime_normalize :
    ComputableInPolyTime normalize encPrenexCNF encPrenexCNF := by
  unfold normalize isClosedInput yesInput noInput encPrenexCNF roundVars encCNF
  simp only [List.decide_mem_eq_any]
  fun_prop

end Cslib.Complexity.NCL.QBF.Source
