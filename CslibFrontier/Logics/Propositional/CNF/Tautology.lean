/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF

/-!
# Tautological clauses

A clause is a *tautology* when it contains a literal and its negation (`CNF.isTautClause`); it is
then satisfied by every assignment (`CNF.eval_eq_true_of_isTautClause`). Removing repeated
literals from a clause that is not a tautology leaves one literal per variable
(`CNF.nodup_map_fst_dedup_of_not_isTautClause`) and does not change its value
(`CNF.eval_dedup_clause`). These facts were extracted from the SAT branching rules of
`CslibFrontier.Logics.Propositional.CNF.Branching` so that other clients can use them without that
module; for terms, `Term.isTautClause_negate` in `CslibFrontier.Logics.Propositional.DNF.ModelCount`
relates them to `Term.consistent`.

## Main definitions

* `Cslib.Logic.PL.CNF.isTautClause`: the clause contains a literal and its negation.

## Main results

* `Cslib.Logic.PL.CNF.eval_eq_true_of_isTautClause`: a tautological clause is always true.
* `Cslib.Logic.PL.CNF.nodup_map_fst_dedup_of_not_isTautClause`: a deduplicated non-tautological
  clause has distinct variables.
* `Cslib.Logic.PL.CNF.eval_dedup_clause`: deduplicating a clause keeps its value.
-/

public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*} [DecidableEq V]

/-- Whether a clause contains complementary literals `l` and `¬l` (making it a tautology). -/
@[expose] def isTautClause (c : Clause V) : Bool :=
  c.any fun l => decide (Std.Sat.Literal.negate l ∈ c)

/-- A tautological clause evaluates to `true` under every assignment. -/
theorem eval_eq_true_of_isTautClause {c : Clause V} (ht : isTautClause c = true) (σ : V → Bool) :
    c.eval σ = true := by
  simp only [isTautClause, List.any_eq_true, decide_eq_true_eq] at ht
  obtain ⟨l, hl, hneg⟩ := ht
  rw [Clause.eval_eq_true_iff]
  by_cases h : σ l.1 = l.2
  · exact ⟨l, hl, h⟩
  · refine ⟨Std.Sat.Literal.negate l, hneg, ?_⟩
    obtain ⟨v, b⟩ := l
    cases b <;> cases hσ : σ v <;> simp_all [Std.Sat.Literal.negate]

/-- Deduplicating a non-tautological clause produces distinct variables. -/
theorem nodup_map_fst_dedup_of_not_isTautClause {c : Clause V} (ht : isTautClause c = false) :
    (c.dedup.map Prod.fst).Nodup := by
  have hnt : ∀ l ∈ c, Std.Sat.Literal.negate l ∉ c := by
    intro l hl hneg
    have : isTautClause c = true := by
      simp only [isTautClause, List.any_eq_true, decide_eq_true_eq]
      exact ⟨l, hl, hneg⟩
    rw [ht] at this
    exact Bool.noConfusion this
  have hinj : Set.InjOn (Prod.fst : Literal V → V) {l | l ∈ c.dedup} := by
    rintro ⟨v₁, b₁⟩ h₁ ⟨v₂, b₂⟩ h₂ hv
    dsimp only at hv
    subst hv
    rw [Set.mem_ofPred_eq, List.mem_dedup] at h₁ h₂
    cases b₁ <;> cases b₂
    · rfl
    · exact absurd h₂ (hnt (v₁, false) h₁)
    · exact absurd h₂ (hnt (v₁, true) h₁)
    · rfl
  exact c.nodup_dedup.map_on hinj

/-- Deduplicating a clause preserves its evaluation under every assignment. -/
theorem eval_dedup_clause (c : Clause V) (σ : V → Bool) :
    Clause.eval σ c.dedup = Clause.eval σ c := by
  rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  simp only [List.mem_dedup]

end Cslib.Logic.PL.CNF
