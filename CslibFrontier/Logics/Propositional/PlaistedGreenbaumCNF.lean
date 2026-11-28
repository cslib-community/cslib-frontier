/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.TseitinCNF

/-! # The Plaisted–Greenbaum transformation of a proposition

Plaisted and Greenbaum [Plaisted and Greenbaum][PlaistedGreenbaum1986] observed that the
Tseitin transformation (`Cslib.Logic.PL.Proposition.tseitinCNF`) needs only one direction of
each definition. For a subformula occurring positively, that is under an even number of
antecedents of `→`, its variable only has to imply the subformula; for one occurring negatively,
the subformula only has to imply its variable. `Proposition.plaistedGreenbaumDefs pol A` keeps,
for every subformula of `A`, the definitional clauses of the direction its polarity needs, where
`pol` is the polarity of `A` itself and the antecedent of `→` flips it.
`Proposition.plaistedGreenbaumCNF A` adds the unit clause asserting the variable of `A`.

The clauses are among those of the Tseitin transformation, with the same variables
(`Proposition.mem_tseitinCNF_of_mem_plaistedGreenbaumCNF`), so every model of `A` still extends to a
model (`Proposition.eval_plaistedGreenbaumCNF_tseitinExtend`) and every clause has at most three
literals (`Proposition.length_le_three_of_mem_tseitinCNF`). In the other direction every model of
the transformation restricts to a model of `A` (`Proposition.eval_of_eval_plaistedGreenbaumCNF`), so
the two are equisatisfiable (`Proposition.satisfiable_plaistedGreenbaumCNF_iff`). Unlike for the
Tseitin transformation, the extension of a model of `A` is not unique: a variable of a subformula
that occurs only positively may be false while the subformula is true
(`Proposition.not_forall_eq_of_eval_plaistedGreenbaumCNF`). In exchange there are at most
two clauses for each node of `A` instead of three (`Proposition.length_plaistedGreenbaumCNF_le`).

**Source and conventions.** Plaisted and Greenbaum [PlaistedGreenbaum1986, pp. 293–297]
define, for a first-order formula `A`, conjunctions `A⁺` and `A⁻` of one-directional definitions
(§1, p. 294): `(A ∧ B)⁺` contains `L_{A ∧ B} ⊃ L_A ∧ L_B`, `(A ∨ B)⁺` contains
`L_{A ∨ B} ⊃ L_A ∨ L_B`, and `(A ⊃ B)⁺` contains `L_{A ⊃ B} ⊃ (L_A ⊃ L_B)` together with `A⁻`
and `B⁺`, with the reverse implications in `A⁻`. An atom is its own literal, with `A⁺ = A⁻`
empty (p. 295), and the clause set of `A` is the clauses of `A⁺` together with the unit clause
`L_A`, asserted positively. Their Theorem 1 (p. 295) is the restriction of models
(`Proposition.eval_of_eval_plaistedGreenbaumCNF`), their Lemma 1 (p. 297) the extension
(`Proposition.eval_plaistedGreenbaumCNF_tseitinExtend`), and their Theorem 2 and Corollary
(p. 297) equisatisfiability (`Proposition.satisfiable_plaistedGreenbaumCNF_iff`). Here the
construction is specialised to propositions: there are no quantifiers or equivalences, and `⊥`,
which the paper does not have, gets the clause `¬x` at positive polarity and nothing at negative
polarity. As in the paper, which gives different subformulas different predicates, equal
subformulas share a variable.

## Main definitions

* `Cslib.Logic.PL.Proposition.plaistedGreenbaumDefs`: the definitional clauses needed at a
  polarity.
* `Cslib.Logic.PL.Proposition.plaistedGreenbaumCNF`: the Plaisted–Greenbaum transformation.

## Main results

* `Cslib.Logic.PL.Proposition.mem_tseitinCNF_of_mem_plaistedGreenbaumCNF`: its clauses are
  clauses of the Tseitin transformation.
* `Cslib.Logic.PL.Proposition.eval_of_eval_plaistedGreenbaumCNF`: every model restricts to a model
  of the proposition.
* `Cslib.Logic.PL.Proposition.satisfiable_plaistedGreenbaumCNF_iff`: equisatisfiability.
* `Cslib.Logic.PL.Proposition.not_forall_eq_of_eval_plaistedGreenbaumCNF`: models are not
  determined by the atoms.
* `Cslib.Logic.PL.Proposition.length_plaistedGreenbaumCNF_le`: at most `2 · A.size + 1` clauses.

## References

* [D. A. Plaisted and S. Greenbaum, *A structure-preserving clause form
  translation*][PlaistedGreenbaum1986], pp. 293–297
-/

@[expose] public section

namespace Cslib.Logic.PL.Proposition

variable {Atom : Type*}

/-- The definitional clauses of the subformulas of a proposition occurring at polarity `pol`
(`true` for positive). At positive polarity the clauses say that the variable of `B = op(C, D)`
implies `op` of the variables of `C` and `D`, at negative polarity that it is implied by it; the
antecedent of `→` has the opposite polarity. -/
def plaistedGreenbaumDefs : Bool → Proposition Atom → CNF (Atom ⊕ Proposition Atom)
  | _, atom _ => []
  | true, falsum => [[(.inr falsum, false)]]
  | false, falsum => []
  | true, and A B =>
    [[(.inr (and A B), false), (A.tseitinVar, true)],
      [(.inr (and A B), false), (B.tseitinVar, true)]] ++
      A.plaistedGreenbaumDefs true ++ B.plaistedGreenbaumDefs true
  | false, and A B =>
    [[(.inr (and A B), true), (A.tseitinVar, false), (B.tseitinVar, false)]] ++
      A.plaistedGreenbaumDefs false ++ B.plaistedGreenbaumDefs false
  | true, or A B =>
    [[(.inr (or A B), false), (A.tseitinVar, true), (B.tseitinVar, true)]] ++
      A.plaistedGreenbaumDefs true ++ B.plaistedGreenbaumDefs true
  | false, or A B =>
    [[(.inr (or A B), true), (A.tseitinVar, false)],
      [(.inr (or A B), true), (B.tseitinVar, false)]] ++
      A.plaistedGreenbaumDefs false ++ B.plaistedGreenbaumDefs false
  | true, imp A B =>
    [[(.inr (imp A B), false), (A.tseitinVar, false), (B.tseitinVar, true)]] ++
      A.plaistedGreenbaumDefs false ++ B.plaistedGreenbaumDefs true
  | false, imp A B =>
    [[(.inr (imp A B), true), (A.tseitinVar, true)],
      [(.inr (imp A B), true), (B.tseitinVar, false)]] ++
      A.plaistedGreenbaumDefs true ++ B.plaistedGreenbaumDefs false

/-- **The Plaisted–Greenbaum transformation** [Plaisted and Greenbaum][PlaistedGreenbaum1986]:
the definitional clauses needed for the subformulas of `A` at their polarities, and the unit
clause asserting the variable of `A`. -/
def plaistedGreenbaumCNF (A : Proposition Atom) : CNF (Atom ⊕ Proposition Atom) :=
  [(A.tseitinVar, true)] :: A.plaistedGreenbaumDefs true

/-- The definitional clauses needed at a polarity are definitional clauses of the Tseitin
transformation. -/
theorem mem_tseitinDefs_of_mem_plaistedGreenbaumDefs {pol : Bool} {A : Proposition Atom}
    {c : Clause (Atom ⊕ Proposition Atom)} (hc : c ∈ A.plaistedGreenbaumDefs pol) :
    c ∈ A.tseitinDefs := by
  induction A generalizing pol with
  | atom x => simp [plaistedGreenbaumDefs] at hc
  | falsum => cases pol <;> simp_all [plaistedGreenbaumDefs, tseitinDefs]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    cases pol <;>
      simp only [plaistedGreenbaumDefs, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hc <;>
      simp only [tseitinDefs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] <;>
      grind

/-- **The clauses of the Plaisted–Greenbaum transformation are clauses of the Tseitin
transformation.** -/
theorem mem_tseitinCNF_of_mem_plaistedGreenbaumCNF {A : Proposition Atom}
    {c : Clause (Atom ⊕ Proposition Atom)} (hc : c ∈ A.plaistedGreenbaumCNF) :
    c ∈ A.tseitinCNF := by
  rcases List.mem_cons.mp hc with rfl | hc
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (mem_tseitinDefs_of_mem_plaistedGreenbaumDefs hc)

/-! ### Semantics -/

/-- **Every model of `A` extends to a model of the Plaisted–Greenbaum transformation**, by the
same extension as for the Tseitin transformation. -/
theorem eval_plaistedGreenbaumCNF_tseitinExtend (v : Atom → Bool) (A : Proposition Atom) :
    A.plaistedGreenbaumCNF.eval (tseitinExtend v) = A.eval v := by
  cases h : A.eval v
  · simp [plaistedGreenbaumCNF, h]
  · rw [CNF.eval_eq_true_iff]
    intro c hc
    have := (eval_tseitinCNF_tseitinExtend v A).trans h
    rw [CNF.eval_eq_true_iff] at this
    exact this c (mem_tseitinCNF_of_mem_plaistedGreenbaumCNF hc)

/-- Under an assignment satisfying the definitional clauses needed at polarity `pol`, if the
variable of `A` has the value `pol` then so does `A` at the atoms. -/
theorem eval_eq_of_eval_plaistedGreenbaumDefs {σ : Atom ⊕ Proposition Atom → Bool} {pol : Bool}
    {A : Proposition Atom} (h : (A.plaistedGreenbaumDefs pol).eval σ = true)
    (hvar : σ A.tseitinVar = pol) : A.eval (σ ∘ Sum.inl) = pol := by
  induction A generalizing pol with
  | atom x => exact hvar
  | falsum => cases pol <;> simp_all [plaistedGreenbaumDefs, tseitinVar]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    cases pol <;>
    · simp only [plaistedGreenbaumDefs, CNF.eval_append, Bool.and_eq_true] at h
      obtain ⟨⟨hgate, hA⟩, hB⟩ := h
      simp only [tseitinVar] at hvar
      simp only [CNF.eval_cons, Clause.eval_cons, Literal.eval_mk, CNF.eval_nil, Clause.eval_nil,
        hvar] at hgate
      have ihA' := @ihA
      have ihB' := @ihB
      simp only [eval_and_bool, eval_or_bool, eval_imp_bool]
      revert hgate ihA' ihB' hA hB
      cases σ A.tseitinVar <;> cases σ B.tseitinVar <;>
        cases A.eval (σ ∘ Sum.inl) <;> cases B.eval (σ ∘ Sum.inl) <;> simp_all

/-- **Every model of the Plaisted–Greenbaum transformation restricts to a model of `A`.** -/
theorem eval_of_eval_plaistedGreenbaumCNF {σ : Atom ⊕ Proposition Atom → Bool}
    {A : Proposition Atom} (h : A.plaistedGreenbaumCNF.eval σ = true) :
    A.eval (σ ∘ Sum.inl) = true := by
  simp only [plaistedGreenbaumCNF, CNF.eval_cons, Clause.eval_cons, Literal.eval_mk,
    Clause.eval_nil, Bool.or_false, beq_iff_eq, Bool.and_eq_true] at h
  exact eval_eq_of_eval_plaistedGreenbaumDefs h.2 h.1

/-- **Models of the Plaisted–Greenbaum transformation are not determined by the atoms**, unlike
those of the Tseitin transformation (`Proposition.eq_of_eval_tseitinCNF`). In `(x ∧ x) ∨ x` the
conjunction occurs positively, so with `x` true its variable may be true or false. -/
theorem not_forall_eq_of_eval_plaistedGreenbaumCNF [Nonempty Atom] :
    ¬ ∀ (A : Proposition Atom) (σ τ : Atom ⊕ Proposition Atom → Bool),
      A.plaistedGreenbaumCNF.eval σ = true → A.plaistedGreenbaumCNF.eval τ = true →
        σ ∘ Sum.inl = τ ∘ Sum.inl → ∀ y ∈ A.plaistedGreenbaumCNF.vars, σ y = τ y := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty Atom›
  let τ : Atom ⊕ Proposition Atom → Bool
    | .inr (.and _ _) => false
    | _ => true
  have := h (.or (.and (.atom x) (.atom x)) (.atom x)) (fun _ => true) τ rfl rfl rfl
    (.inr (.and (.atom x) (.atom x)))
    (CNF.mem_vars.2 ⟨[(.inr (.and (.atom x) (.atom x)), false), (.inl x, true)],
      by simp [plaistedGreenbaumCNF, plaistedGreenbaumDefs, tseitinVar], false,
      List.mem_cons_self⟩)
  exact Bool.noConfusion this

/-- **The Plaisted–Greenbaum transformation preserves satisfiability.** -/
theorem satisfiable_plaistedGreenbaumCNF_iff (A : Proposition Atom) :
    A.plaistedGreenbaumCNF.Satisfiable ↔ ∃ v : Atom → Bool, A.eval v = true :=
  ⟨fun ⟨σ, hσ⟩ => ⟨σ ∘ Sum.inl, eval_of_eval_plaistedGreenbaumCNF hσ⟩,
    fun ⟨v, hv⟩ => ⟨tseitinExtend v, (eval_plaistedGreenbaumCNF_tseitinExtend v A).trans hv⟩⟩

/-! ### Size -/

theorem length_plaistedGreenbaumDefs_le (pol : Bool) (A : Proposition Atom) :
    (A.plaistedGreenbaumDefs pol).length ≤ 2 * A.size := by
  induction A generalizing pol with
  | atom x => simp [plaistedGreenbaumDefs]
  | falsum => cases pol <;> simp [plaistedGreenbaumDefs, size]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    have := ihA true; have := ihA false; have := ihB true; have := ihB false
    cases pol <;>
      simp only [plaistedGreenbaumDefs, List.length_append, List.length_cons, List.length_nil,
        size] <;> omega

/-- **The Plaisted–Greenbaum transformation has at most two clauses per node**, and one more. -/
theorem length_plaistedGreenbaumCNF_le (A : Proposition Atom) :
    A.plaistedGreenbaumCNF.length ≤ 2 * A.size + 1 := by
  simpa [plaistedGreenbaumCNF, Nat.add_comm] using length_plaistedGreenbaumDefs_le true A

end Cslib.Logic.PL.Proposition
