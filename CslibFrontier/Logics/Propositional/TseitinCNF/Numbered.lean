/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PlaistedGreenbaumCNF

/-! # The Tseitin and Plaisted–Greenbaum transformations with numbered variables

The Tseitin transformation `Cslib.Logic.PL.Proposition.tseitinCNF` names a subformula by the
subformula itself, so comparing two of its variables costs as much as comparing two subformulas.
Here the variables are numbers. A proposition over the atoms `Fin n` is traversed once, in
post-order: the atom `i` is the variable `i`, and every other node gets the next unused number,
counting from `n`. Each node prepends its definitional clauses to an accumulator, so no list is
copied (`Proposition.tseitinClauses`). No running-time bound is stated here.

The traversal takes a polarity: positive, negative, or both, and the antecedent of `→` flips it.
At both it keeps every definitional clause, which gives the numbered Tseitin transformation
(`Proposition.tseitinNumberedCNF`). At a positive or negative polarity it keeps only the direction
of each definition that the polarity needs, as Plaisted and Greenbaum do
(`Cslib.Logic.PL.Proposition.plaistedGreenbaumCNF`); started at positive polarity it gives the
numbered Plaisted–Greenbaum transformation (`Proposition.plaistedGreenbaumNumberedCNF`), with at
most two clauses per node instead of three. A number names one occurrence of a subformula, so it
has one polarity, and "both" is never needed below a positive root.

Each numbered transformation is the corresponding named one up to renaming and the order of the
clauses: renaming every number to the variable of the subformula it was given
(`Proposition.tseitinNumberedVar`) turns it into a permutation of `A.tseitinCNF`
(`Proposition.perm_relabel_tseitinNumberedCNF`) or of `A.plaistedGreenbaumCNF`
(`Proposition.perm_relabel_plaistedGreenbaumNumberedCNF`). Equal subformulas at different
positions get different numbers, so this renaming is not injective. The models therefore transfer
in one direction through the renaming, and in the other by a direct argument: every model of a
numbered transformation satisfies `A` at the atoms (`Proposition.eval_of_eval_tseitinNumberedCNF`,
`Proposition.eval_of_eval_plaistedGreenbaumNumberedCNF`). So each is equisatisfiable with `A`
(`Proposition.satisfiable_tseitinNumberedCNF_iff`,
`Proposition.satisfiable_plaistedGreenbaumNumberedCNF_iff`) and has the size bound of the named
transformation.

## Main definitions

* `Cslib.Logic.PL.Proposition.tseitinClauses`: the traversal at a polarity, returning a
  `Cslib.Logic.PL.Proposition.TseitinResult`.
* `Cslib.Logic.PL.Proposition.tseitinNumberedCNF`: the numbered Tseitin transformation.
* `Cslib.Logic.PL.Proposition.plaistedGreenbaumNumberedCNF`: the numbered Plaisted–Greenbaum
  transformation.
* `Cslib.Logic.PL.Proposition.tseitinLabels`, `Cslib.Logic.PL.Proposition.tseitinNumberedVar`:
  the subformula at every number.

## Main results

* `Cslib.Logic.PL.Proposition.perm_relabel_tseitinNumberedCNF`,
  `Cslib.Logic.PL.Proposition.perm_relabel_plaistedGreenbaumNumberedCNF`: they are the named
  transformations up to renaming and order.
* `Cslib.Logic.PL.Proposition.satisfiable_tseitinNumberedCNF_iff`,
  `Cslib.Logic.PL.Proposition.satisfiable_plaistedGreenbaumNumberedCNF_iff`: equisatisfiability.
* `Cslib.Logic.PL.Proposition.length_tseitinNumberedCNF_le`,
  `Cslib.Logic.PL.Proposition.length_le_three_of_mem_tseitinNumberedCNF`,
  `Cslib.Logic.PL.Proposition.length_plaistedGreenbaumNumberedCNF_le`: linear size.

## References

* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
* [D. A. Plaisted and S. Greenbaum, *A structure-preserving clause form
  translation*][PlaistedGreenbaum1986]
-/

@[expose] public section

namespace Cslib.Logic.PL.Proposition

variable {n : ℕ}

/-- The result of the Tseitin traversal of a subformula. -/
structure TseitinResult where
  /-- The variable of the subformula. -/
  var : ℕ
  /-- The first number not yet used. -/
  next : ℕ
  /-- The clauses so far, those of the subformula first. -/
  clauses : CNF ℕ

/-- The Tseitin traversal of a proposition over `Fin n`, at the polarity `pol`: `some true` for
positive, `some false` for negative and `none` for both. From the first unused number `k` and the
clauses `acc` so far, it returns the variable of the proposition, the next unused number, and the
clauses with the definitional clauses of the subformulas prepended: for a node `op(B, C)` with
variable `x`, those saying that `x` implies `op` of the variables of `B` and `C` at positive
polarity, the converse at negative polarity, and both at both. The antecedent of `→` has the
opposite polarity. The numbering does not depend on the polarity. -/
def tseitinClauses : Proposition (Fin n) → Option Bool → ℕ → CNF ℕ → TseitinResult
  | atom i, _, k, acc => ⟨i, k, acc⟩
  | falsum, some false, k, acc => ⟨k, k + 1, acc⟩
  | falsum, _, k, acc => ⟨k, k + 1, [(k, false)] :: acc⟩
  | and A B, pol, k, acc =>
    let a := tseitinClauses A pol k acc
    let b := tseitinClauses B pol a.next a.clauses
    let x := b.next
    let pos := [[(x, false), (a.var, true)], [(x, false), (b.var, true)]]
    let neg := [[(x, true), (a.var, false), (b.var, false)]]
    ⟨x, x + 1, match pol with
      | some true => pos ++ b.clauses
      | some false => neg ++ b.clauses
      | none => pos ++ neg ++ b.clauses⟩
  | or A B, pol, k, acc =>
    let a := tseitinClauses A pol k acc
    let b := tseitinClauses B pol a.next a.clauses
    let x := b.next
    let pos := [[(x, false), (a.var, true), (b.var, true)]]
    let neg := [[(x, true), (a.var, false)], [(x, true), (b.var, false)]]
    ⟨x, x + 1, match pol with
      | some true => pos ++ b.clauses
      | some false => neg ++ b.clauses
      | none => neg ++ pos ++ b.clauses⟩
  | imp A B, pol, k, acc =>
    let a := tseitinClauses A (pol.map not) k acc
    let b := tseitinClauses B pol a.next a.clauses
    let x := b.next
    let pos := [[(x, false), (a.var, false), (b.var, true)]]
    let neg := [[(x, true), (a.var, true)], [(x, true), (b.var, false)]]
    ⟨x, x + 1, match pol with
      | some true => pos ++ b.clauses
      | some false => neg ++ b.clauses
      | none => neg ++ pos ++ b.clauses⟩

/-- **The Tseitin transformation with numbered variables**: the clauses of the traversal from
the number `n` on, and the unit clause asserting the variable of the proposition. -/
def tseitinNumberedCNF (A : Proposition (Fin n)) : CNF ℕ :=
  let r := A.tseitinClauses none n []
  [(r.var, true)] :: r.clauses

/-- **The Plaisted–Greenbaum transformation with numbered variables**
[Plaisted and Greenbaum][PlaistedGreenbaum1986]: the clauses of the traversal from the number `n`
on at positive polarity, and the unit clause asserting the variable of the proposition. -/
def plaistedGreenbaumNumberedCNF (A : Proposition (Fin n)) : CNF ℕ :=
  let r := A.tseitinClauses (some true) n []
  [(r.var, true)] :: r.clauses

/-! ### Renaming to the Tseitin transformation -/

/-- The subformulas of a proposition that get numbers, in the order of their numbers: the
subformulas other than atoms, in post-order. -/
def tseitinLabels : Proposition (Fin n) → List (Proposition (Fin n))
  | atom _ => []
  | falsum => [falsum]
  | and A B => A.tseitinLabels ++ B.tseitinLabels ++ [and A B]
  | or A B => A.tseitinLabels ++ B.tseitinLabels ++ [or A B]
  | imp A B => A.tseitinLabels ++ B.tseitinLabels ++ [imp A B]

/-- The variable of `A.tseitinCNF` named by a number in `A.tseitinNumberedCNF`: an atom below
`n`, and the subformula it was given from `n` on. -/
def tseitinNumberedVar (A : Proposition (Fin n)) (j : ℕ) : Fin n ⊕ Proposition (Fin n) :=
  if h : j < n then .inl ⟨j, h⟩ else .inr (A.tseitinLabels.getD (j - n) falsum)

/-- The traversal from `k` at polarity `pol`, renamed by a map sending the atoms to themselves and
the numbers from `k` on to the subformulas they are given, is the definitional clauses of the
Tseitin transformation (at `none`) or of the Plaisted–Greenbaum transformation (at `some p`)
before the renamed accumulator, up to order. -/
theorem perm_relabel_tseitinClauses (A : Proposition (Fin n)) (pol : Option Bool) (k : ℕ)
    (acc : CNF ℕ) (g : ℕ → Fin n ⊕ Proposition (Fin n)) (hatom : ∀ i : Fin n, g i = .inl i)
    (hlabel : ∀ j (B : Proposition (Fin n)), A.tseitinLabels[j]? = some B → g (k + j) = .inr B) :
    (A.tseitinClauses pol k acc).next = k + A.tseitinLabels.length ∧
      g (A.tseitinClauses pol k acc).var = A.tseitinVar ∧
      ((A.tseitinClauses pol k acc).clauses.relabel g).Perm
        (pol.elim A.tseitinDefs (fun p => A.plaistedGreenbaumDefs p) ++ acc.relabel g) := by
  induction A generalizing pol k acc with
  | atom i => exact ⟨by simp [tseitinClauses, tseitinLabels], hatom i,
      by rcases pol with _ | _ | _ <;> simp [tseitinClauses, tseitinDefs, plaistedGreenbaumDefs]⟩
  | falsum =>
    have hk := hlabel 0 falsum rfl
    simp only [Nat.add_zero] at hk
    rcases pol with _ | _ | _ <;>
      refine ⟨by simp [tseitinClauses, tseitinLabels],
        by simpa [tseitinClauses, tseitinVar] using hk, ?_⟩ <;>
      simp [tseitinClauses, tseitinDefs, plaistedGreenbaumDefs, CNF.relabel, Clause.relabel, hk]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    have hlA : ∀ j C, A.tseitinLabels[j]? = some C → g (k + j) = .inr C := fun j C hC =>
      hlabel j C (by
        simp only [tseitinLabels, List.append_assoc]
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hC).1]
        exact hC)
    have hlB : ∀ j C, B.tseitinLabels[j]? = some C →
        g (k + A.tseitinLabels.length + j) = .inr C := fun j C hC => by
      rw [Nat.add_assoc]
      refine hlabel _ C ?_
      simp only [tseitinLabels, List.append_assoc]
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left (List.getElem?_eq_some_iff.1 hC).1]
      exact hC
    rcases pol with _ | _ | _ <;> rw [tseitinClauses] <;>
    · generalize ha : A.tseitinClauses _ k acc = a
      obtain ⟨hkA, hvA, hpA⟩ := ha ▸ ihA _ k acc hlA
      generalize hb : B.tseitinClauses _ a.next a.clauses = b
      obtain ⟨hkB, hvB, hpB⟩ := hb ▸ ihB _ a.next a.clauses (hkA ▸ hlB)
      have hx := hlabel (A.tseitinLabels.length + B.tseitinLabels.length) _
        (by simp [tseitinLabels]; rfl)
      rw [← Nat.add_assoc, ← hkA, ← hkB] at hx
      have key := hpB.trans ((hpA.append_left _).trans (List.perm_append_comm_assoc ..))
      refine ⟨by simp [hkB, hkA, tseitinLabels]; omega, hx, ?_⟩
      simpa [tseitinDefs, plaistedGreenbaumDefs, CNF.relabel, Clause.relabel, hx, hvA, hvB]
        using key

/-- **The numbered Tseitin transformation is the Tseitin transformation up to renaming and the
order of the clauses.** -/
theorem perm_relabel_tseitinNumberedCNF (A : Proposition (Fin n)) :
    (A.tseitinNumberedCNF.relabel A.tseitinNumberedVar).Perm A.tseitinCNF := by
  obtain ⟨-, hv, hp⟩ := perm_relabel_tseitinClauses A none n [] A.tseitinNumberedVar
    (fun i => by simp [tseitinNumberedVar])
    (fun j B h => by simp [tseitinNumberedVar, List.getD_eq_getElem?_getD, h])
  simpa [tseitinNumberedCNF, tseitinCNF, CNF.relabel, Clause.relabel, hv] using hp

/-- **The numbered Plaisted–Greenbaum transformation is the Plaisted–Greenbaum transformation up
to renaming and the order of the clauses.** -/
theorem perm_relabel_plaistedGreenbaumNumberedCNF (A : Proposition (Fin n)) :
    (A.plaistedGreenbaumNumberedCNF.relabel A.tseitinNumberedVar).Perm A.plaistedGreenbaumCNF := by
  obtain ⟨-, hv, hp⟩ := perm_relabel_tseitinClauses A (some true) n [] A.tseitinNumberedVar
    (fun i => by simp [tseitinNumberedVar])
    (fun j B h => by simp [tseitinNumberedVar, List.getD_eq_getElem?_getD, h])
  simpa [plaistedGreenbaumNumberedCNF, plaistedGreenbaumCNF, CNF.relabel, Clause.relabel, hv]
    using hp

/-- The numbered Tseitin transformation under an assignment read through the renaming is the
Tseitin transformation under the assignment. -/
theorem eval_tseitinNumberedCNF_comp (τ : Fin n ⊕ Proposition (Fin n) → Bool)
    (A : Proposition (Fin n)) :
    A.tseitinNumberedCNF.eval (τ ∘ A.tseitinNumberedVar) = A.tseitinCNF.eval τ := by
  rw [← CNF.eval_relabel]
  exact (perm_relabel_tseitinNumberedCNF A).all_eq

/-- Under an assignment satisfying the clauses of the traversal at polarity `pol`, the
accumulator holds, and if the variable of the proposition has a value `p` that the polarity
allows, `p` itself when `pol = some p` and either when `pol = none`, then so does the proposition
at the atoms. -/
theorem eval_tseitinClauses {σ : ℕ → Bool} (A : Proposition (Fin n)) (pol : Option Bool) (k : ℕ)
    (acc : CNF ℕ) (h : (A.tseitinClauses pol k acc).clauses.eval σ = true) :
    acc.eval σ = true ∧ ∀ p : Bool, pol ≠ some (!p) →
      σ (A.tseitinClauses pol k acc).var = p → (A.eval fun i : Fin n => σ i) = p := by
  induction A generalizing pol k acc with
  | atom i => exact ⟨h, fun _ _ h => h⟩
  | falsum =>
    rcases pol with _ | _ | _ <;>
      simp only [tseitinClauses, CNF.eval_cons, Clause.eval_cons, Literal.eval_mk,
        Clause.eval_nil, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at h ⊢
    · exact ⟨h.2, fun p _ hp => (hp.symm.trans h.1).symm⟩
    · exact ⟨h, fun p hp _ => by cases p <;> simp_all⟩
    · exact ⟨h.2, fun p _ hp => (hp.symm.trans h.1).symm⟩
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    rcases pol with _ | _ | _ <;> rw [tseitinClauses] at h ⊢ <;>
    · generalize ha : A.tseitinClauses _ k acc = a at h ⊢
      generalize hb : B.tseitinClauses _ a.next a.clauses = b at h ⊢
      have ihB := hb ▸ ihB _ a.next a.clauses
      have ihA := ha ▸ ihA _ k acc
      simp only [CNF.eval_append, Bool.and_eq_true] at h
      obtain ⟨hgate, hbc⟩ := h
      obtain ⟨hac, hB⟩ := ihB hbc
      obtain ⟨hacc, hA⟩ := ihA hac
      refine ⟨hacc, ?_⟩
      simp only [CNF.eval_cons, CNF.eval_nil, Clause.eval_cons, Literal.eval_mk, Clause.eval_nil,
        Bool.or_false, Bool.and_true, Bool.and_eq_true] at hgate
      simp only [eval_and_bool, eval_or_bool, eval_imp_bool]
      revert hgate hA hB
      generalize σ a.var = va
      generalize σ b.var = vb
      generalize σ b.next = vx
      generalize A.eval (fun i : Fin n => σ i) = ea
      generalize B.eval (fun i : Fin n => σ i) = eb
      revert va vb vx ea eb
      decide

/-- **Every model of the numbered Tseitin transformation satisfies the proposition** at the
atoms. -/
theorem eval_of_eval_tseitinNumberedCNF {σ : ℕ → Bool} {A : Proposition (Fin n)}
    (h : A.tseitinNumberedCNF.eval σ = true) : (A.eval fun i : Fin n => σ i) = true := by
  simp only [tseitinNumberedCNF, CNF.eval_cons, Clause.eval_cons, Literal.eval_mk,
    Clause.eval_nil, Bool.or_false, beq_iff_eq, Bool.and_eq_true] at h
  exact (eval_tseitinClauses A none n [] h.2).2 true (by simp) h.1

/-- **Every model of the numbered Plaisted–Greenbaum transformation satisfies the proposition**
at the atoms. -/
theorem eval_of_eval_plaistedGreenbaumNumberedCNF {σ : ℕ → Bool} {A : Proposition (Fin n)}
    (h : A.plaistedGreenbaumNumberedCNF.eval σ = true) : (A.eval fun i : Fin n => σ i) = true := by
  simp only [plaistedGreenbaumNumberedCNF, CNF.eval_cons, Clause.eval_cons, Literal.eval_mk,
    Clause.eval_nil, Bool.or_false, beq_iff_eq, Bool.and_eq_true] at h
  exact (eval_tseitinClauses A (some true) n [] h.2).2 true (by simp) h.1

/-- **The numbered Tseitin transformation preserves satisfiability.** -/
theorem satisfiable_tseitinNumberedCNF_iff (A : Proposition (Fin n)) :
    A.tseitinNumberedCNF.Satisfiable ↔ ∃ v : Fin n → Bool, A.eval v = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, eval_of_eval_tseitinNumberedCNF hσ⟩
  · rintro ⟨v, hv⟩
    exact ⟨tseitinExtend v ∘ A.tseitinNumberedVar, (eval_tseitinNumberedCNF_comp _ A).trans
      ((eval_tseitinCNF_tseitinExtend v A).trans hv)⟩

/-- **The numbered Plaisted–Greenbaum transformation preserves satisfiability.** -/
theorem satisfiable_plaistedGreenbaumNumberedCNF_iff (A : Proposition (Fin n)) :
    A.plaistedGreenbaumNumberedCNF.Satisfiable ↔ ∃ v : Fin n → Bool, A.eval v = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, eval_of_eval_plaistedGreenbaumNumberedCNF hσ⟩
  · rintro ⟨v, hv⟩
    refine ⟨tseitinExtend v ∘ A.tseitinNumberedVar, ?_⟩
    rw [← CNF.eval_relabel]
    exact (perm_relabel_plaistedGreenbaumNumberedCNF A).all_eq.trans
      ((eval_plaistedGreenbaumCNF_tseitinExtend v A).trans hv)

/-! ### Size -/

/-- **The numbered Tseitin transformation has linearly many clauses.** -/
theorem length_tseitinNumberedCNF_le (A : Proposition (Fin n)) :
    A.tseitinNumberedCNF.length ≤ 3 * A.size + 1 := by
  have := (perm_relabel_tseitinNumberedCNF A).length_eq
  simp only [CNF.relabel, List.length_map] at this
  exact this ▸ length_tseitinCNF_le A

/-- **The numbered Plaisted–Greenbaum transformation has at most two clauses per node**, and one
more. -/
theorem length_plaistedGreenbaumNumberedCNF_le (A : Proposition (Fin n)) :
    A.plaistedGreenbaumNumberedCNF.length ≤ 2 * A.size + 1 := by
  have := (perm_relabel_plaistedGreenbaumNumberedCNF A).length_eq
  simp only [CNF.relabel, List.length_map] at this
  exact this ▸ length_plaistedGreenbaumCNF_le A

/-- **Every clause of the numbered Tseitin transformation has at most three literals.** -/
theorem length_le_three_of_mem_tseitinNumberedCNF {A : Proposition (Fin n)} {c : Clause ℕ}
    (hc : c ∈ A.tseitinNumberedCNF) : c.length ≤ 3 := by
  have := length_le_three_of_mem_tseitinCNF ((perm_relabel_tseitinNumberedCNF A).subset
    (List.mem_map_of_mem (f := Clause.relabel A.tseitinNumberedVar) hc))
  simpa using this

end Cslib.Logic.PL.Proposition
