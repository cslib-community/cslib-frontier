/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
public import CslibFrontier.Logics.Propositional.Semantics

/-! # The Tseitin transformation of a proposition

Tseitin's transformation [Tseitin][Tseitin1983] turns a proposition into a formula in
conjunctive normal form of linear size by naming subformulas. Here every subformula `B` of `A`
that is not an atom gets the variable `Sum.inr B` of `CNF (Atom ⊕ Proposition Atom)`, and an atom
`x` is its own variable `Sum.inl x` (`Proposition.tseitinVar`). Equal subformulas share a
variable. For every subformula `B = op(C, D)` the *definitional clauses* say that the variable of
`B` carries `op` of the variables of `C` and `D`; for `B = ⊥` they say that its variable is false
(`Proposition.tseitinDefs`). The formula `Proposition.tseitinCNF A` adds the unit clause asserting
the variable of `A`.

This is not the Tseitin formula of a graph (`Cslib.Logic.PL.CNF.tseitinFormula`), a parity
formula from the same paper. `Cslib.Circuits.Boolean.tseitinCNF` is the same construction for De
Morgan gate lists, where wires play the role of subformulas.

The two formulas have the same models up to the fresh variables
(`Proposition.eval_tseitinCNF_eq_true_iff`): an assignment `σ` satisfies `A.tseitinCNF` exactly
when its restriction `σ ∘ Sum.inl` to the atoms satisfies `A` and `σ` gives every fresh variable
in the formula the value of its subformula, that is, `σ` agrees with the extension
`Proposition.tseitinExtend (σ ∘ Sum.inl)` on the variables of the formula. So every model of `A`
extends to a model of `A.tseitinCNF` (`Proposition.eval_tseitinCNF_tseitinExtend`), uniquely on
the variables of the formula (`Proposition.eq_of_eval_tseitinCNF`), and the two are equisatisfiable
(`Proposition.satisfiable_tseitinCNF_iff`).

**Source and conventions.** Tseitin [Tseitin1983, §1, p. 467] gives the three clauses defining
the variable of a conjunction, a disjunction and an implication, and tests whether a formula is a
tautology by adding the unit clause of the *negated* variable of the whole formula. Here the
variable of the formula is asserted positively instead, so that the transformation is satisfiable
exactly when the formula is; a tautology test applies it to `¬A`. CSLib's propositions have no
negation connective, `¬A` being `A → ⊥`, so negation goes through the implication clauses, and `⊥`
gets the unit clause making its variable false.

The fresh variables keep the formula short: `A.tseitinCNF` has at most `3 · A.size + 1` clauses
(`Proposition.length_tseitinCNF_le`), each with at most three literals
(`Proposition.length_le_three_of_mem_tseitinCNF`).

## Main definitions

* `Cslib.Logic.PL.Proposition.tseitinVar`: the variable of a subformula.
* `Cslib.Logic.PL.Proposition.tseitinDefs`: the definitional clauses of the subformulas.
* `Cslib.Logic.PL.Proposition.tseitinCNF`: the Tseitin transformation.
* `Cslib.Logic.PL.Proposition.tseitinExtend`: an assignment of the atoms, extended to the fresh
  variables by evaluation.
* `Cslib.Logic.PL.Proposition.size`: the number of nodes of a proposition.

## Main results

* `Cslib.Logic.PL.Proposition.eval_tseitinCNF_eq_true_iff`: the models of `A.tseitinCNF`.
* `Cslib.Logic.PL.Proposition.eval_tseitinCNF_tseitinExtend`: every model of `A` extends.
* `Cslib.Logic.PL.Proposition.eq_of_eval_tseitinCNF`: uniquely on the variables of the formula.
* `Cslib.Logic.PL.Proposition.satisfiable_tseitinCNF_iff`: equisatisfiability.
* `Cslib.Logic.PL.Proposition.length_tseitinCNF_le`,
  `Cslib.Logic.PL.Proposition.length_le_three_of_mem_tseitinCNF`: linear size.

## References

* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983],
  §1, p. 467 of the 1983 reprint
-/

@[expose] public section

namespace Cslib.Logic.PL.Proposition

variable {Atom : Type*}

/-- The variable of a subformula in the Tseitin transformation: an atom is its own variable and
any other subformula is a fresh variable. -/
def tseitinVar : Proposition Atom → Atom ⊕ Proposition Atom
  | atom x => .inl x
  | falsum => .inr falsum
  | and A B => .inr (and A B)
  | or A B => .inr (or A B)
  | imp A B => .inr (imp A B)

/-- The definitional clauses of the subformulas of a proposition: for `B = op(C, D)`, three
clauses saying that the variable of `B` is `op` of the variables of `C` and `D`, and for `B = ⊥`
the unit clause saying that its variable is false. -/
def tseitinDefs : Proposition Atom → CNF (Atom ⊕ Proposition Atom)
  | atom _ => []
  | falsum => [[(.inr falsum, false)]]
  | and A B =>
    [[(.inr (and A B), false), (A.tseitinVar, true)],
      [(.inr (and A B), false), (B.tseitinVar, true)],
      [(.inr (and A B), true), (A.tseitinVar, false), (B.tseitinVar, false)]] ++
      A.tseitinDefs ++ B.tseitinDefs
  | or A B =>
    [[(.inr (or A B), true), (A.tseitinVar, false)],
      [(.inr (or A B), true), (B.tseitinVar, false)],
      [(.inr (or A B), false), (A.tseitinVar, true), (B.tseitinVar, true)]] ++
      A.tseitinDefs ++ B.tseitinDefs
  | imp A B =>
    [[(.inr (imp A B), true), (A.tseitinVar, true)],
      [(.inr (imp A B), true), (B.tseitinVar, false)],
      [(.inr (imp A B), false), (A.tseitinVar, false), (B.tseitinVar, true)]] ++
      A.tseitinDefs ++ B.tseitinDefs

/-- **The Tseitin transformation** [Tseitin][Tseitin1983]: the definitional clauses of the
subformulas of `A`, and the unit clause asserting the variable of `A`. -/
def tseitinCNF (A : Proposition Atom) : CNF (Atom ⊕ Proposition Atom) :=
  [(A.tseitinVar, true)] :: A.tseitinDefs

/-- An assignment of the atoms, extended to the fresh variables by giving the variable of every
subformula its value. -/
def tseitinExtend (v : Atom → Bool) : Atom ⊕ Proposition Atom → Bool :=
  Sum.elim v (eval v)

/-- The number of nodes of a proposition: atoms and `⊥` have size one. -/
def size : Proposition Atom → ℕ
  | atom _ | falsum => 1
  | and A B | or A B | imp A B => A.size + B.size + 1

/-! ### Semantics -/

@[simp] theorem tseitinExtend_tseitinVar (v : Atom → Bool) (A : Proposition Atom) :
    tseitinExtend v A.tseitinVar = A.eval v := by
  cases A <;> rfl

/-- The definitional clauses hold under the extension of any assignment of the atoms. -/
theorem eval_tseitinDefs_tseitinExtend (v : Atom → Bool) (A : Proposition Atom) :
    A.tseitinDefs.eval (tseitinExtend v) = true := by
  induction A with
  | atom | falsum => rfl
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp only [tseitinDefs, CNF.eval_append, ihA, ihB, Bool.and_true, CNF.eval_cons,
      Clause.eval_cons, Literal.eval_mk, tseitinExtend_tseitinVar, CNF.eval_nil, Clause.eval_nil]
    simp only [tseitinExtend, Sum.elim_inr, eval_and_bool, eval_or_bool, eval_imp_bool]
    cases A.eval v <;> cases B.eval v <;> rfl

/-- Under an assignment satisfying the definitional clauses, the variable of `A` carries the
value of `A` at the atoms. -/
theorem eval_tseitinVar_of_eval_tseitinDefs {σ : Atom ⊕ Proposition Atom → Bool}
    {A : Proposition Atom} (h : A.tseitinDefs.eval σ = true) :
    σ A.tseitinVar = A.eval (σ ∘ Sum.inl) := by
  induction A with
  | atom x => rfl
  | falsum => simpa [tseitinDefs, tseitinVar] using h
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp only [tseitinDefs, CNF.eval_append, Bool.and_eq_true] at h
    obtain ⟨⟨hgate, hA⟩, hB⟩ := h
    simp only [CNF.eval_cons, Clause.eval_cons, Literal.eval_mk, CNF.eval_nil, Clause.eval_nil,
      ihA hA, ihB hB] at hgate
    simp only [tseitinVar, eval_and_bool, eval_or_bool, eval_imp_bool]
    revert hgate
    cases σ (.inr _) <;> cases A.eval (σ ∘ Sum.inl) <;> cases B.eval (σ ∘ Sum.inl) <;> decide

/-- Under an assignment satisfying the definitional clauses of `A`, the variables of those
clauses and the variable of `A` carry the values of the extension of the assignment's atoms. -/
private theorem eq_tseitinExtend_of_eval_tseitinDefs {σ : Atom ⊕ Proposition Atom → Bool}
    {A : Proposition Atom} (h : A.tseitinDefs.eval σ = true) {y : Atom ⊕ Proposition Atom}
    (hy : y = A.tseitinVar ∨ y ∈ A.tseitinDefs.vars) :
    σ y = tseitinExtend (σ ∘ Sum.inl) y := by
  induction A with
  | atom x =>
    rcases hy with rfl | hy
    · rfl
    · simp [tseitinDefs, CNF.vars] at hy
  | falsum =>
    have hy : y = falsum.tseitinVar := by simpa [tseitinDefs, CNF.vars, tseitinVar] using hy
    subst hy
    rw [eval_tseitinVar_of_eval_tseitinDefs h, tseitinExtend_tseitinVar]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    have hAB := h
    simp only [tseitinDefs, CNF.eval_append, Bool.and_eq_true] at hAB
    obtain ⟨⟨-, hA⟩, hB⟩ := hAB
    have hself : σ (.inr _) = tseitinExtend (σ ∘ Sum.inl) (.inr _) :=
      (eval_tseitinVar_of_eval_tseitinDefs h).trans (tseitinExtend_tseitinVar _ _).symm
    rcases hy with rfl | hy
    · exact hself
    · obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.1 hy
      simp only [tseitinDefs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl | rfl | rfl) | hc) | hc
      all_goals first
        | exact ihA hA (.inr (CNF.mem_vars.2 ⟨c, hc, b, hb⟩))
        | exact ihB hB (.inr (CNF.mem_vars.2 ⟨c, hc, b, hb⟩))
        | (simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb
           rcases hb with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
             first | exact hself | exact ihA hA (.inl rfl) | exact ihB hB (.inl rfl))

/-- **The models of the Tseitin transformation**: an assignment satisfies `A.tseitinCNF` exactly
when its restriction to the atoms satisfies `A` and it agrees, on the variables of the formula,
with the extension of that restriction. -/
theorem eval_tseitinCNF_eq_true_iff (σ : Atom ⊕ Proposition Atom → Bool) (A : Proposition Atom) :
    A.tseitinCNF.eval σ = true ↔
      A.eval (σ ∘ Sum.inl) = true ∧
        ∀ y ∈ A.tseitinCNF.vars, σ y = tseitinExtend (σ ∘ Sum.inl) y := by
  refine ⟨fun h => ?_, fun ⟨hA, hagree⟩ => ?_⟩
  · simp only [tseitinCNF, CNF.eval_cons, Clause.eval_cons, Literal.eval_mk, Clause.eval_nil,
      Bool.or_false, beq_iff_eq, Bool.and_eq_true] at h
    refine ⟨(eval_tseitinVar_of_eval_tseitinDefs h.2).symm.trans h.1, fun y hy => ?_⟩
    simp only [tseitinCNF, CNF.vars, List.flatten_cons, List.map_cons, List.cons_append,
      List.nil_append, List.mem_cons] at hy
    exact eq_tseitinExtend_of_eval_tseitinDefs h.2 hy
  · rw [CNF.eval_congr hagree]
    simp [tseitinCNF, eval_tseitinDefs_tseitinExtend, hA]

/-- **Every model of `A` extends to a model of `A.tseitinCNF`**: the value of the Tseitin
transformation under the extension of an assignment is the value of `A`. -/
theorem eval_tseitinCNF_tseitinExtend (v : Atom → Bool) (A : Proposition Atom) :
    A.tseitinCNF.eval (tseitinExtend v) = A.eval v := by
  simp [tseitinCNF, eval_tseitinDefs_tseitinExtend]

/-- **Models of the Tseitin transformation are determined by the atoms**: two models that agree
on the atoms agree on every variable of the formula. -/
theorem eq_of_eval_tseitinCNF {σ τ : Atom ⊕ Proposition Atom → Bool} {A : Proposition Atom}
    (hσ : A.tseitinCNF.eval σ = true) (hτ : A.tseitinCNF.eval τ = true)
    (hatoms : σ ∘ Sum.inl = τ ∘ Sum.inl) {y : Atom ⊕ Proposition Atom}
    (hy : y ∈ A.tseitinCNF.vars) : σ y = τ y := by
  rw [((eval_tseitinCNF_eq_true_iff σ A).1 hσ).2 y hy,
    ((eval_tseitinCNF_eq_true_iff τ A).1 hτ).2 y hy, hatoms]

/-- **The Tseitin transformation preserves satisfiability.** -/
theorem satisfiable_tseitinCNF_iff (A : Proposition Atom) :
    A.tseitinCNF.Satisfiable ↔ ∃ v : Atom → Bool, A.eval v = true :=
  ⟨fun ⟨σ, hσ⟩ => ⟨σ ∘ Sum.inl, ((eval_tseitinCNF_eq_true_iff σ A).1 hσ).1⟩,
    fun ⟨v, hv⟩ => ⟨tseitinExtend v, (eval_tseitinCNF_tseitinExtend v A).trans hv⟩⟩

/-! ### Size -/

theorem length_tseitinDefs_le (A : Proposition Atom) : A.tseitinDefs.length ≤ 3 * A.size := by
  induction A with
  | atom | falsum => simp [tseitinDefs, size]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp only [tseitinDefs, List.length_append, List.length_cons, List.length_nil, size]
    omega

/-- **The Tseitin transformation has linearly many clauses.** -/
theorem length_tseitinCNF_le (A : Proposition Atom) : A.tseitinCNF.length ≤ 3 * A.size + 1 := by
  simpa [tseitinCNF, Nat.add_comm] using length_tseitinDefs_le A

/-- **Every clause of the Tseitin transformation has at most three literals.** -/
theorem length_le_three_of_mem_tseitinCNF {A : Proposition Atom}
    {c : Clause (Atom ⊕ Proposition Atom)} (hc : c ∈ A.tseitinCNF) : c.length ≤ 3 := by
  have defs : ∀ B : Proposition Atom, ∀ c ∈ B.tseitinDefs, c.length ≤ 3 := fun B => by
    induction B with
    | atom | falsum => simp [tseitinDefs]
    | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
      intro c hc
      simp only [tseitinDefs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl | rfl | rfl) | hc) | hc
      exacts [by simp, by simp, by simp, ihA c hc, ihB c hc]
  rcases List.mem_cons.1 hc with rfl | hc
  exacts [by simp, defs A c hc]

end Cslib.Logic.PL.Proposition
