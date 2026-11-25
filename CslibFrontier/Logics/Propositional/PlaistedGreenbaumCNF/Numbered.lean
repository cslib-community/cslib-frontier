/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PlaistedGreenbaumCNF

/-! # The Plaisted–Greenbaum transformation with numbered variables

The Plaisted–Greenbaum transformation `Cslib.Logic.PL.Proposition.plaistedGreenbaumCNF` names a
subformula by the subformula itself, so comparing two of its variables costs as much as comparing
two subformulas. Here the variables are numbers. A proposition over the atoms `Fin n` is
traversed once, in post-order: the atom `i` is the variable `i`, and every other node gets the
next unused number, counting from `n`. Each node prepends to an accumulator the definitional
clauses its polarity needs, so no list is copied (`Proposition.plaistedGreenbaumClauses`). At
positive polarity they say that the node's variable implies the node, at negative polarity the
converse; the antecedent of `→` flips the polarity. No running-time bound is stated here.

A number names one occurrence of a subformula, so it has one polarity. Equal subformulas at
different positions get different numbers, and so may get different directions of their
definitions.

The numbered transformation is the Plaisted–Greenbaum transformation up to renaming and the order
of the clauses: renaming every number to the variable of the subformula it was given
(`Proposition.plaistedGreenbaumNumberedVar`) turns it into a permutation of
`A.plaistedGreenbaumCNF` (`Proposition.perm_relabel_plaistedGreenbaumNumberedCNF`). This renaming
is not injective, since equal subformulas share a variable of `A.plaistedGreenbaumCNF`. The
models therefore transfer in one direction through the renaming, and in the other by a direct
argument: every model of the numbered transformation satisfies `A` at the atoms
(`Proposition.eval_of_eval_plaistedGreenbaumNumberedCNF`). So the two are equisatisfiable
(`Proposition.satisfiable_plaistedGreenbaumNumberedCNF_iff`) and have the same size bound.

## Main definitions

* `Cslib.Logic.PL.Proposition.plaistedGreenbaumClauses`: the traversal at a polarity, returning a
  `Cslib.Logic.PL.Proposition.PlaistedGreenbaumResult`.
* `Cslib.Logic.PL.Proposition.plaistedGreenbaumNumberedCNF`: the numbered transformation.
* `Cslib.Logic.PL.Proposition.plaistedGreenbaumLabels`,
  `Cslib.Logic.PL.Proposition.plaistedGreenbaumNumberedVar`: the subformula at every number.

## Main results

* `Cslib.Logic.PL.Proposition.perm_relabel_plaistedGreenbaumNumberedCNF`: it is the
  Plaisted–Greenbaum transformation up to renaming and order.
* `Cslib.Logic.PL.Proposition.satisfiable_plaistedGreenbaumNumberedCNF_iff`: equisatisfiability.
* `Cslib.Logic.PL.Proposition.length_plaistedGreenbaumNumberedCNF_le`: at most two clauses per
  node, and one more.

## References

* [D. A. Plaisted and S. Greenbaum, *A structure-preserving clause form
  translation*][PlaistedGreenbaum1986]
-/

@[expose] public section

namespace Cslib.Logic.PL.Proposition

variable {n : ℕ}

/-- The result of the Plaisted–Greenbaum traversal of a subformula. -/
structure PlaistedGreenbaumResult where
  /-- The variable of the subformula. -/
  var : ℕ
  /-- The first number not yet used. -/
  next : ℕ
  /-- The clauses so far, those of the subformula first. -/
  clauses : CNF ℕ

/-- The Plaisted–Greenbaum traversal of a proposition over `Fin n` at the polarity `pol` (`true`
for positive). From the first unused number `k` and the clauses `acc` so far, it returns the
variable of the proposition, the next unused number, and the clauses with the definitional
clauses of the subformulas prepended: for a node `op(B, C)` with variable `x`, those saying that
`x` implies `op` of the variables of `B` and `C` at positive polarity, and the converse at
negative polarity. The antecedent of `→` has the opposite polarity. The numbering does not depend
on the polarity. -/
def plaistedGreenbaumClauses :
    Proposition (Fin n) → Bool → ℕ → CNF ℕ → PlaistedGreenbaumResult
  | atom i, _, k, acc => ⟨i, k, acc⟩
  | falsum, pol, k, acc => ⟨k, k + 1, bif pol then [(k, false)] :: acc else acc⟩
  | and A B, pol, k, acc =>
    let a := plaistedGreenbaumClauses A pol k acc
    let b := plaistedGreenbaumClauses B pol a.next a.clauses
    let x := b.next
    ⟨x, x + 1, (bif pol then [[(x, false), (a.var, true)], [(x, false), (b.var, true)]]
      else [[(x, true), (a.var, false), (b.var, false)]]) ++ b.clauses⟩
  | or A B, pol, k, acc =>
    let a := plaistedGreenbaumClauses A pol k acc
    let b := plaistedGreenbaumClauses B pol a.next a.clauses
    let x := b.next
    ⟨x, x + 1, (bif pol then [[(x, false), (a.var, true), (b.var, true)]]
      else [[(x, true), (a.var, false)], [(x, true), (b.var, false)]]) ++ b.clauses⟩
  | imp A B, pol, k, acc =>
    let a := plaistedGreenbaumClauses A (!pol) k acc
    let b := plaistedGreenbaumClauses B pol a.next a.clauses
    let x := b.next
    ⟨x, x + 1, (bif pol then [[(x, false), (a.var, false), (b.var, true)]]
      else [[(x, true), (a.var, true)], [(x, true), (b.var, false)]]) ++ b.clauses⟩

/-- **The Plaisted–Greenbaum transformation with numbered variables**
[Plaisted and Greenbaum][PlaistedGreenbaum1986]: the clauses of the traversal from the number `n`
on at positive polarity, and the unit clause asserting the variable of the proposition. -/
def plaistedGreenbaumNumberedCNF (A : Proposition (Fin n)) : CNF ℕ :=
  let r := A.plaistedGreenbaumClauses true n []
  [(r.var, true)] :: r.clauses

/-! ### Renaming to the Plaisted–Greenbaum transformation -/

/-- The subformulas of a proposition that get numbers, in the order of their numbers: the
subformulas other than atoms, in post-order. -/
def plaistedGreenbaumLabels : Proposition (Fin n) → List (Proposition (Fin n))
  | atom _ => []
  | falsum => [falsum]
  | and A B => A.plaistedGreenbaumLabels ++ B.plaistedGreenbaumLabels ++ [and A B]
  | or A B => A.plaistedGreenbaumLabels ++ B.plaistedGreenbaumLabels ++ [or A B]
  | imp A B => A.plaistedGreenbaumLabels ++ B.plaistedGreenbaumLabels ++ [imp A B]

/-- The variable of `A.plaistedGreenbaumCNF` named by a number in `A.plaistedGreenbaumNumberedCNF`:
an atom below `n`, and the subformula it was given from `n` on. -/
def plaistedGreenbaumNumberedVar (A : Proposition (Fin n)) (j : ℕ) :
    Fin n ⊕ Proposition (Fin n) :=
  if h : j < n then .inl ⟨j, h⟩ else .inr (A.plaistedGreenbaumLabels.getD (j - n) falsum)

/-- The traversal from `k` at polarity `pol`, renamed by a map sending the atoms to themselves and
the numbers from `k` on to the subformulas they are given, is the definitional clauses of the
Plaisted–Greenbaum transformation at `pol` before the renamed accumulator, up to order. -/
private theorem perm_relabel_plaistedGreenbaumClauses (A : Proposition (Fin n)) (pol : Bool) (k : ℕ)
    (acc : CNF ℕ) (g : ℕ → Fin n ⊕ Proposition (Fin n)) (hatom : ∀ i : Fin n, g i = .inl i)
    (hlabel : ∀ j (B : Proposition (Fin n)),
      A.plaistedGreenbaumLabels[j]? = some B → g (k + j) = .inr B) :
    (A.plaistedGreenbaumClauses pol k acc).next = k + A.plaistedGreenbaumLabels.length ∧
      g (A.plaistedGreenbaumClauses pol k acc).var = A.tseitinVar ∧
      ((A.plaistedGreenbaumClauses pol k acc).clauses.relabel g).Perm
        (A.plaistedGreenbaumDefs pol ++ acc.relabel g) := by
  induction A generalizing pol k acc with
  | atom i => exact ⟨by simp [plaistedGreenbaumClauses, plaistedGreenbaumLabels], hatom i,
      by cases pol <;> simp [plaistedGreenbaumClauses, plaistedGreenbaumDefs]⟩
  | falsum =>
    have hk : g k = .inr falsum := by simpa only [Nat.add_zero] using hlabel 0 falsum rfl
    cases pol <;>
      exact ⟨by simp [plaistedGreenbaumClauses, plaistedGreenbaumLabels],
        by simpa [plaistedGreenbaumClauses, tseitinVar] using hk,
        by simp [plaistedGreenbaumClauses, plaistedGreenbaumDefs, CNF.relabel, Clause.relabel, hk]⟩
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    have hlA (j C) (hC : A.plaistedGreenbaumLabels[j]? = some C) : g (k + j) = .inr C :=
      hlabel j C <| by
        simp only [plaistedGreenbaumLabels, List.append_assoc]
        rwa [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hC).1]
    have hlB (j C) (hC : B.plaistedGreenbaumLabels[j]? = some C) :
        g (k + A.plaistedGreenbaumLabels.length + j) = .inr C := by
      rw [Nat.add_assoc]
      refine hlabel _ C ?_
      simp only [plaistedGreenbaumLabels, List.append_assoc]
      rwa [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left (List.getElem?_eq_some_iff.1 hC).1]
    rw [plaistedGreenbaumClauses]
    generalize ha : A.plaistedGreenbaumClauses _ k acc = a
    obtain ⟨hkA, hvA, hpA⟩ := ha ▸ ihA _ k acc hlA
    generalize hb : B.plaistedGreenbaumClauses _ a.next a.clauses = b
    obtain ⟨hkB, hvB, hpB⟩ := hb ▸ ihB _ a.next a.clauses (hkA ▸ hlB)
    have hx := hlabel (A.plaistedGreenbaumLabels.length + B.plaistedGreenbaumLabels.length) _
      (by simp [plaistedGreenbaumLabels]; rfl)
    rw [← Nat.add_assoc, ← hkA, ← hkB] at hx
    have key := hpB.trans ((hpA.append_left _).trans (List.perm_append_comm_assoc ..))
    refine ⟨by simp [hkB, hkA, plaistedGreenbaumLabels]; omega, hx, ?_⟩
    cases pol <;>
      simpa [plaistedGreenbaumDefs, CNF.relabel, Clause.relabel, hx, hvA, hvB] using key

/-- **The numbered Plaisted–Greenbaum transformation is the Plaisted–Greenbaum transformation up
to renaming and the order of the clauses.** -/
theorem perm_relabel_plaistedGreenbaumNumberedCNF (A : Proposition (Fin n)) :
    (A.plaistedGreenbaumNumberedCNF.relabel A.plaistedGreenbaumNumberedVar).Perm
      A.plaistedGreenbaumCNF := by
  obtain ⟨-, hv, hp⟩ := perm_relabel_plaistedGreenbaumClauses A true n []
    A.plaistedGreenbaumNumberedVar (fun i => by simp [plaistedGreenbaumNumberedVar])
    (fun j B h => by simp [plaistedGreenbaumNumberedVar, List.getD_eq_getElem?_getD, h])
  simpa [plaistedGreenbaumNumberedCNF, plaistedGreenbaumCNF, CNF.relabel, Clause.relabel, hv]
    using hp

/-- Under an assignment satisfying the clauses of the traversal at polarity `pol`, the
accumulator holds, and if the variable of the proposition has the value `pol`, so does the
proposition at the atoms. -/
private theorem eval_plaistedGreenbaumClauses {σ : ℕ → Bool} (A : Proposition (Fin n)) (pol : Bool)
    (k : ℕ) (acc : CNF ℕ) (h : (A.plaistedGreenbaumClauses pol k acc).clauses.eval σ = true) :
    acc.eval σ = true ∧
      (σ (A.plaistedGreenbaumClauses pol k acc).var = pol →
        (A.eval fun i : Fin n => σ i) = pol) := by
  induction A generalizing pol k acc with
  | atom i => exact ⟨h, id⟩
  | falsum =>
    cases pol <;>
      simp only [plaistedGreenbaumClauses, Bool.cond_true, Bool.cond_false, CNF.eval_cons,
        Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, Bool.or_false, Bool.and_eq_true,
        beq_iff_eq] at h ⊢
    · exact ⟨h, fun _ => rfl⟩
    · exact ⟨h.2, fun hp => (hp.symm.trans h.1).symm⟩
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    rw [plaistedGreenbaumClauses] at h ⊢
    generalize ha : A.plaistedGreenbaumClauses _ k acc = a at h ⊢
    generalize hb : B.plaistedGreenbaumClauses _ a.next a.clauses = b at h ⊢
    simp only [CNF.eval_append, Bool.and_eq_true] at h
    obtain ⟨hgate, hbc⟩ := h
    obtain ⟨hac, hB⟩ := (hb ▸ ihB _ a.next a.clauses) hbc
    obtain ⟨hacc, hA⟩ := (ha ▸ ihA _ k acc) hac
    refine ⟨hacc, ?_⟩
    simp only [eval_and_bool, eval_or_bool, eval_imp_bool]
    cases pol <;>
    · simp only [Bool.cond_true, Bool.cond_false, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
        Literal.eval_mk, Clause.eval_nil, Bool.or_false, Bool.and_true, Bool.and_eq_true] at hgate
      revert hgate hA hB
      generalize σ a.var = va, σ b.var = vb, σ b.next = vx
      generalize A.eval (fun i : Fin n => σ i) = ea, B.eval (fun i : Fin n => σ i) = eb
      revert va vb vx ea eb
      decide

/-- **Every model of the numbered Plaisted–Greenbaum transformation satisfies the proposition**
at the atoms. -/
theorem eval_of_eval_plaistedGreenbaumNumberedCNF {σ : ℕ → Bool} {A : Proposition (Fin n)}
    (h : A.plaistedGreenbaumNumberedCNF.eval σ = true) : (A.eval fun i : Fin n => σ i) = true := by
  simp only [plaistedGreenbaumNumberedCNF, CNF.eval_cons, Clause.eval_cons, Literal.eval_mk,
    Clause.eval_nil, Bool.or_false, beq_iff_eq, Bool.and_eq_true] at h
  exact (eval_plaistedGreenbaumClauses A true n [] h.2).2 h.1

/-- **The numbered Plaisted–Greenbaum transformation preserves satisfiability.** -/
theorem satisfiable_plaistedGreenbaumNumberedCNF_iff (A : Proposition (Fin n)) :
    A.plaistedGreenbaumNumberedCNF.Satisfiable ↔ ∃ v : Fin n → Bool, A.eval v = true := by
  refine ⟨fun ⟨σ, hσ⟩ => ⟨_, eval_of_eval_plaistedGreenbaumNumberedCNF hσ⟩, fun ⟨v, hv⟩ =>
    ⟨tseitinExtend v ∘ A.plaistedGreenbaumNumberedVar, ?_⟩⟩
  rw [← CNF.eval_relabel]
  exact (perm_relabel_plaistedGreenbaumNumberedCNF A).all_eq.trans
    ((eval_plaistedGreenbaumCNF_tseitinExtend v A).trans hv)

/-! ### Size -/

/-- **The numbered Plaisted–Greenbaum transformation has at most two clauses per node**, and one
more. -/
theorem length_plaistedGreenbaumNumberedCNF_le (A : Proposition (Fin n)) :
    A.plaistedGreenbaumNumberedCNF.length ≤ 2 * A.size + 1 := by
  have := (perm_relabel_plaistedGreenbaumNumberedCNF A).length_eq
  simp only [CNF.relabel, List.length_map] at this
  exact this ▸ length_plaistedGreenbaumCNF_le A

end Cslib.Logic.PL.Proposition
