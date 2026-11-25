/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.DNFWidth
public import CslibFrontier.Foundations.Data.BitString.Agree

/-! # Tests for approximating small formulas by narrow ones

On three variables: the subcube bound for words agreeing on two coordinates and for a term on two
distinct variables, where it is attained; removing a repeated literal; negating a term: the
negation of the contradictory term `x₀ ∧ ¬x₀` is a tautological clause, and that of the consistent
`x₀ ∧ ¬x₁ ∧ x₀` is not; and the DNF and CNF forms of O'Donnell's Proposition 4.9 for the formula
`(x₀ ∧ x₁ ∧ x₂) ∨ ¬x₀` and its dual, with `ε = 1 / 2`, where `log₂ (2 / (1 / 2)) = 2`, giving
consistent terms and non-tautological clauses without repeated literals. -/

public section

namespace CslibFrontierTests.BooleanAnalysisDNFWidth

open Cslib Cslib.BitString Finset Logic.PL

/-- The words of three bits with `x₀ = true` and `x₁ = false` agree on `{0, 1}`, so there are at
most `2 ^ (3 - 2) = 2` of them. -/
example : #({x : Fin 3 → Bool | x 0 = true ∧ x 1 = false} : Finset (Fin 3 → Bool)) ≤ 2 :=
  (card_le_of_forall_agree (F := {0, 1}) (by decide)).trans_eq (by decide)

/-- The term `x₀ ∧ ¬x₁` on two distinct variables is satisfied by exactly `2 ^ (3 - 2)` inputs:
the subcube bound is attained. -/
example : #{x : Fin 3 → Bool | Term.eval x [(0, true), (1, false)] = true} =
    2 ^ (Fintype.card (Fin 3) - Term.width ([(0, true), (1, false)] : Term (Fin 3))) :=
  le_antisymm (Term.card_filter_eval_le _) (by decide)

/-- The term `x₀ ∧ x₀` is consistent and mentions one variable, so removing the repeated literal
leaves one literal. -/
example : ([(0, true), (0, true)] : Term (Fin 3)).dedup.length = 1 :=
  (Term.length_dedup_of_consistent (by decide)).trans (by decide)

/-- Removing the repeated literal from `x₀ ∧ ¬x₁ ∧ x₀` leaves the function `x₀ ∧ ¬x₁`. -/
example (x : Fin 3 → Bool) :
    Term.eval x ([(0, true), (1, false), (0, true)] : Term (Fin 3)).dedup = (x 0 && !x 1) := by
  rw [Term.eval_dedup]
  simp only [Term.eval_cons, Term.eval_nil, Literal.eval]
  cases x 0 <;> cases x 1 <;> rfl

/-- Negating the literals of the term `x₀ ∧ ¬x₁ ∧ x₀`, repeated literal included, gives a clause
of the same three literals. -/
example : (Term.negate ([(0, true), (1, false), (0, true)] : Term (Fin 3))).length = 3 := by
  rw [Term.length_negate]
  rfl

/-- The contradictory term `x₀ ∧ ¬x₀` is inconsistent, so its negation `¬x₀ ∨ x₀` is a
tautological clause. -/
example : CNF.isTautClause (Term.negate ([(0, true), (0, false)] : Term (Fin 3))) = true := by
  rw [Term.isTautClause_negate]
  decide

/-- The term `x₀ ∧ ¬x₁ ∧ x₀` is consistent, repeated literal included, so its negation is not a
tautological clause. -/
example :
    CNF.isTautClause (Term.negate ([(0, true), (1, false), (0, true)] : Term (Fin 3))) = false := by
  rw [Term.isTautClause_negate]
  decide

/-- `log₂ (2 / (1 / 2)) = 2`. -/
theorem logb_two_div_half : Real.logb 2 (2 / (1 / 2)) = 2 := by
  rw [show (2 : ℝ) / (1 / 2) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow two_pos (by norm_num)]

/-- The DNF `(x₀ ∧ x₁ ∧ x₂) ∨ ¬x₀` of size `2` is `1/2`-close to a DNF of size at most `2` with
consistent terms of at most `2` distinct literals. -/
example : ∃ ψ : DNF (Fin 3), ψ.length ≤ 2 ∧
    (∀ t ∈ ψ, t.Nodup ∧ t.consistent = true ∧ (t.length : ℝ) ≤ 2) ∧
    (hammingDist (fun x : Fin 3 → Bool =>
      DNF.eval x [[(0, true), (1, true), (2, true)], [(0, false)]]) fun x => DNF.eval x ψ : ℝ) /
      2 ^ 3 ≤ 1 / 2 := by
  obtain ⟨ψ, hlen, hwidth, hdist⟩ := exists_dnf_hammingDist_div_le (ι := Fin 3)
    [[(0, true), (1, true), (2, true)], [(0, false)]] (ε := 1 / 2) (by norm_num)
  refine ⟨ψ, hlen, fun t ht => ⟨(hwidth t ht).1, (hwidth t ht).2.1,
    (hwidth t ht).2.2.trans_eq (by simpa using logb_two_div_half)⟩, ?_⟩
  simpa using hdist

/-- Deleting the wide term of `(x₀ ∧ x₁ ∧ x₂) ∨ ¬x₀` changes the function on one input of
eight, within the `ε = 1 / 2` of the previous example. -/
example : hammingDist (fun x : Fin 3 → Bool =>
    DNF.eval x [[(0, true), (1, true), (2, true)], [(0, false)]])
      (fun x => DNF.eval x [[(0, false)]]) = 1 := by
  decide

/-- The CNF `(x₀ ∨ x₁ ∨ x₂) ∧ ¬x₀` of size `2` is `1/2`-close to a CNF of size at most `2` with
non-tautological clauses of at most `2` distinct literals. -/
example : ∃ ψ : CNF (Fin 3), ψ.length ≤ 2 ∧
    (∀ c ∈ ψ, c.Nodup ∧ CNF.isTautClause c = false ∧ (c.length : ℝ) ≤ 2) ∧
    (hammingDist (fun x : Fin 3 → Bool =>
      CNF.eval x [[(0, true), (1, true), (2, true)], [(0, false)]]) fun x => CNF.eval x ψ : ℝ) /
      2 ^ 3 ≤ 1 / 2 := by
  obtain ⟨ψ, hlen, hwidth, hdist⟩ := exists_cnf_hammingDist_div_le (ι := Fin 3)
    [[(0, true), (1, true), (2, true)], [(0, false)]] (ε := 1 / 2) (by norm_num)
  refine ⟨ψ, hlen, fun c hc => ⟨(hwidth c hc).1, (hwidth c hc).2.1,
    (hwidth c hc).2.2.trans_eq (by simpa using logb_two_div_half)⟩, ?_⟩
  simpa using hdist

end CslibFrontierTests.BooleanAnalysisDNFWidth

end
