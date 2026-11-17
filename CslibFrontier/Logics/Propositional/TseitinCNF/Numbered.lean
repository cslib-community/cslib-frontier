/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import Cslib.Algorithms.Lean.TimeM
public import CslibFrontier.Logics.Propositional.TseitinCNF

/-! # The Tseitin transformation with numbered variables, and its running time

The Tseitin transformation `Cslib.Logic.PL.Proposition.tseitinCNF` names a subformula by the
subformula itself, so comparing two of its variables costs as much as comparing two subformulas.
Here the variables are numbers. A proposition over the atoms `Fin n` is traversed once, in
post-order: the atom `i` is the variable `i`, and every other node gets the next unused number,
counting from `n`. Each node prepends its definitional clauses to an accumulator, so no list is
copied (`Proposition.tseitinClausesM`).

The traversal is written once, for any monad, with an action `visit` run at every node. At `Id`
it is the numbered transformation `Proposition.tseitinNumberedCNF`. At `TimeM ℕ` with
`visit = tick 1` it is `Proposition.tseitinNumberedT`, whose value is the numbered
transformation (`Proposition.ret_tseitinNumberedT`) and whose time is the number of nodes
(`Proposition.time_tseitinNumberedT`).

**Cost model.** One unit of time per node of the proposition. Everything else a node does is
counted as free: reading the results of its children, incrementing the counter, and prepending at
most three clauses of at most three literals. That is constant work per node, so the count is
linear running time in the usual RAM model; as with every use of `TimeM`, the correspondence
between the ticks and the work is by inspection of the definition, not proved.

The numbered transformation is the Tseitin transformation up to renaming and the order of the
clauses: renaming every number to the variable of the subformula it was given
(`Proposition.tseitinNumberedVar`) turns it into a permutation of `A.tseitinCNF`
(`Proposition.perm_relabel_tseitinNumberedCNF`). Equal subformulas at different positions get
different numbers, so this renaming is not injective. The models therefore transfer in one
direction through the renaming, and in the other by a direct argument: every model of the
numbered transformation satisfies `A` at the atoms (`Proposition.eval_of_eval_tseitinNumberedCNF`).
So the two are equisatisfiable (`Proposition.satisfiable_tseitinNumberedCNF_iff`) and have the
same size bounds.

## Main definitions

* `Cslib.Logic.PL.Proposition.tseitinClausesM`: the traversal, for any monad, returning a
  `Cslib.Logic.PL.Proposition.TseitinResult`.
* `Cslib.Logic.PL.Proposition.tseitinNumberedCNF`: the numbered transformation.
* `Cslib.Logic.PL.Proposition.tseitinNumberedT`: the traversal, counting nodes.
* `Cslib.Logic.PL.Proposition.tseitinLabels`, `Cslib.Logic.PL.Proposition.tseitinNumberedVar`:
  the subformula at every number.

## Main results

* `Cslib.Logic.PL.Proposition.ret_tseitinNumberedT`,
  `Cslib.Logic.PL.Proposition.time_tseitinNumberedT`: the counted traversal computes the numbered
  transformation in time `A.size`.
* `Cslib.Logic.PL.Proposition.perm_relabel_tseitinNumberedCNF`: it is the Tseitin transformation
  up to renaming and order.
* `Cslib.Logic.PL.Proposition.satisfiable_tseitinNumberedCNF_iff`: equisatisfiability.
* `Cslib.Logic.PL.Proposition.length_tseitinNumberedCNF_le`,
  `Cslib.Logic.PL.Proposition.length_le_three_of_mem_tseitinNumberedCNF`: linear size.

## References

* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
-/

@[expose] public section

namespace Cslib.Logic.PL.Proposition

open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM (tick)

variable {n : ℕ} {m : Type → Type} [Monad m]

/-- The result of the Tseitin traversal of a subformula. -/
structure TseitinResult where
  /-- The variable of the subformula. -/
  var : ℕ
  /-- The first number not yet used. -/
  next : ℕ
  /-- The clauses so far, those of the subformula first. -/
  clauses : CNF ℕ

/-- The Tseitin traversal of a proposition over `Fin n`, running `visit` at every node. From the
first unused number `k` and the clauses `acc` so far, it returns the variable of the proposition,
the next unused number, and the clauses with those of the subformulas prepended. -/
def tseitinClausesM (visit : m Unit) : Proposition (Fin n) → ℕ → CNF ℕ → m TseitinResult
  | atom i, k, acc => do
    visit
    pure ⟨i, k, acc⟩
  | falsum, k, acc => do
    visit
    pure ⟨k, k + 1, [(k, false)] :: acc⟩
  | and A B, k, acc => do
    visit
    let a ← tseitinClausesM visit A k acc
    let b ← tseitinClausesM visit B a.next a.clauses
    let x := b.next
    pure ⟨x, x + 1, [(x, false), (a.var, true)] :: [(x, false), (b.var, true)] ::
      [(x, true), (a.var, false), (b.var, false)] :: b.clauses⟩
  | or A B, k, acc => do
    visit
    let a ← tseitinClausesM visit A k acc
    let b ← tseitinClausesM visit B a.next a.clauses
    let x := b.next
    pure ⟨x, x + 1, [(x, true), (a.var, false)] :: [(x, true), (b.var, false)] ::
      [(x, false), (a.var, true), (b.var, true)] :: b.clauses⟩
  | imp A B, k, acc => do
    visit
    let a ← tseitinClausesM visit A k acc
    let b ← tseitinClausesM visit B a.next a.clauses
    let x := b.next
    pure ⟨x, x + 1, [(x, true), (a.var, true)] :: [(x, true), (b.var, false)] ::
      [(x, false), (a.var, false), (b.var, true)] :: b.clauses⟩

/-- A monad morphism commutes with the Tseitin traversal. -/
theorem _root_.Cslib.IsMonadHom.map_tseitinClausesM {m' : Type → Type} [Monad m']
    {f : ∀ {α}, m α → m' α} (hf : Cslib.IsMonadHom m m' f) (visit : m Unit)
    (A : Proposition (Fin n)) (k : ℕ) (acc : CNF ℕ) :
    f (tseitinClausesM visit A k acc) = tseitinClausesM (f visit) A k acc := by
  induction A generalizing k acc with
  | atom i | falsum => simp [tseitinClausesM, hf.map_bind, hf.map_pure]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp [tseitinClausesM, hf.map_bind, hf.map_pure, ihA, ihB]

/-- The Tseitin traversal of a proposition, without side effects. -/
def tseitinClauses (A : Proposition (Fin n)) (k : ℕ) (acc : CNF ℕ) : TseitinResult :=
  Id.run (tseitinClausesM (pure ()) A k acc)

/-- **The Tseitin transformation with numbered variables**: the clauses of the traversal from
the number `n` on, and the unit clause asserting the variable of the proposition. -/
def tseitinNumberedCNF (A : Proposition (Fin n)) : CNF ℕ :=
  let r := A.tseitinClauses n []
  [(r.var, true)] :: r.clauses

/-- The numbered Tseitin transformation, counting one unit of time per node. -/
def tseitinNumberedT (A : Proposition (Fin n)) : TimeM ℕ (CNF ℕ) := do
  let r ← tseitinClausesM (tick 1) A n []
  pure ([(r.var, true)] :: r.clauses)

/-- **The counted traversal computes the numbered Tseitin transformation.** -/
@[simp] theorem ret_tseitinNumberedT (A : Proposition (Fin n)) :
    A.tseitinNumberedT.ret = A.tseitinNumberedCNF := by
  have := Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_tseitinClausesM (tick 1) A n [])
  simp only [TimeM.ret_tick] at this
  simp [tseitinNumberedT, tseitinNumberedCNF, tseitinClauses, ← this]

/-- The traversal visits every node once. -/
theorem time_tseitinClausesM (A : Proposition (Fin n)) (k : ℕ) (acc : CNF ℕ) :
    (tseitinClausesM (tick 1) A k acc).time = A.size := by
  induction A generalizing k acc with
  | atom i | falsum => simp [tseitinClausesM, size]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp [tseitinClausesM, size, ihA, ihB]
    omega

/-- **The numbered Tseitin transformation takes time `A.size`**, one unit per node. -/
@[simp] theorem time_tseitinNumberedT (A : Proposition (Fin n)) :
    A.tseitinNumberedT.time = A.size := by
  simp [tseitinNumberedT, time_tseitinClausesM]

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

/-- The traversal from `k`, renamed by a map sending the atoms to themselves and the numbers from
`k` on to the subformulas they are given, is the definitional clauses of the Tseitin
transformation before the renamed accumulator, up to order. -/
theorem perm_relabel_tseitinClauses (A : Proposition (Fin n)) (k : ℕ) (acc : CNF ℕ)
    (g : ℕ → Fin n ⊕ Proposition (Fin n)) (hatom : ∀ i : Fin n, g i = .inl i)
    (hlabel : ∀ j (B : Proposition (Fin n)), A.tseitinLabels[j]? = some B → g (k + j) = .inr B) :
    (A.tseitinClauses k acc).next = k + A.tseitinLabels.length ∧
      g (A.tseitinClauses k acc).var = A.tseitinVar ∧
      ((A.tseitinClauses k acc).clauses.relabel g).Perm (A.tseitinDefs ++ acc.relabel g) := by
  induction A generalizing k acc with
  | atom i => exact ⟨by simp [tseitinClauses, tseitinClausesM, tseitinLabels],
      hatom i, by
        simp [tseitinClauses, tseitinClausesM, tseitinDefs]⟩
  | falsum =>
    have hk := hlabel 0 falsum rfl
    simp only [Nat.add_zero] at hk
    refine ⟨by simp [tseitinClauses, tseitinClausesM, tseitinLabels], ?_, ?_⟩
    · simpa [tseitinClauses, tseitinClausesM, tseitinVar] using hk
    · simp [tseitinClauses, tseitinClausesM, tseitinDefs, CNF.relabel, Clause.relabel, hk]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    obtain ⟨hkA, hvA, hpA⟩ := ihA k acc fun j C hC => hlabel j C (by
      simp only [tseitinLabels, List.append_assoc]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hC).1]
      exact hC)
    obtain ⟨hkB, hvB, hpB⟩ := ihB (A.tseitinClauses k acc).next (A.tseitinClauses k acc).clauses
      fun j C hC => by
        rw [hkA, Nat.add_assoc]
        refine hlabel _ C ?_
        simp only [tseitinLabels, List.append_assoc]
        rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
          List.getElem?_append_left (List.getElem?_eq_some_iff.1 hC).1]
        exact hC
    rw [tseitinClauses, tseitinClausesM]
    simp only [Id.run_bind, Id.run_pure, show ∀ (C : Proposition (Fin n)) k acc,
      Id.run (tseitinClausesM (pure ()) C k acc) = C.tseitinClauses k acc from fun _ _ _ => rfl]
    generalize A.tseitinClauses k acc = a at *
    generalize B.tseitinClauses a.next a.clauses = b at *
    have hx := hlabel (A.tseitinLabels.length + B.tseitinLabels.length) _
      (by simp [tseitinLabels]; rfl)
    rw [← Nat.add_assoc, ← hkA, ← hkB] at hx
    have key : (b.clauses.relabel g).Perm (A.tseitinDefs ++ B.tseitinDefs ++ acc.relabel g) :=
      hpB.trans ((hpA.append_left _).trans (by simpa using List.perm_append_comm_assoc ..))
    refine ⟨by simp [hkB, hkA, tseitinLabels]; omega, hx, ?_⟩
    simpa [tseitinDefs, CNF.relabel, Clause.relabel, hx, hvA, hvB] using key

/-- **The numbered Tseitin transformation is the Tseitin transformation up to renaming and the
order of the clauses.** -/
theorem perm_relabel_tseitinNumberedCNF (A : Proposition (Fin n)) :
    (A.tseitinNumberedCNF.relabel A.tseitinNumberedVar).Perm A.tseitinCNF := by
  obtain ⟨-, hv, hp⟩ := perm_relabel_tseitinClauses A n [] A.tseitinNumberedVar
    (fun i => by simp [tseitinNumberedVar])
    (fun j B h => by simp [tseitinNumberedVar, List.getD_eq_getElem?_getD, h])
  simpa [tseitinNumberedCNF, tseitinCNF, CNF.relabel, Clause.relabel, hv] using hp

/-- The numbered Tseitin transformation under an assignment read through the renaming is the
Tseitin transformation under the assignment. -/
theorem eval_tseitinNumberedCNF_comp (τ : Fin n ⊕ Proposition (Fin n) → Bool)
    (A : Proposition (Fin n)) :
    A.tseitinNumberedCNF.eval (τ ∘ A.tseitinNumberedVar) = A.tseitinCNF.eval τ := by
  rw [← CNF.eval_relabel]
  exact (perm_relabel_tseitinNumberedCNF A).all_eq

/-- Under an assignment satisfying the clauses of the traversal, the accumulator holds and the
variable of the proposition carries its value at the atoms. -/
theorem eval_tseitinClauses {σ : ℕ → Bool} (A : Proposition (Fin n)) (k : ℕ) (acc : CNF ℕ)
    (h : (A.tseitinClauses k acc).clauses.eval σ = true) :
    acc.eval σ = true ∧ σ (A.tseitinClauses k acc).var = A.eval fun i : Fin n => σ i := by
  induction A generalizing k acc with
  | atom i => exact ⟨h, rfl⟩
  | falsum =>
    simp only [tseitinClauses, tseitinClausesM, Id.run_bind, Id.run_pure, CNF.eval_cons,
      Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, Bool.or_false, Bool.and_eq_true,
      beq_iff_eq] at h ⊢
    exact ⟨h.2, h.1⟩
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    rw [tseitinClauses, tseitinClausesM] at h ⊢
    simp only [Id.run_bind, Id.run_pure, show ∀ (C : Proposition (Fin n)) k acc,
      Id.run (tseitinClausesM (pure ()) C k acc) = C.tseitinClauses k acc from fun _ _ _ => rfl]
      at h ⊢
    have ihA := ihA k acc
    have ihB := ihB (A.tseitinClauses k acc).next (A.tseitinClauses k acc).clauses
    generalize A.tseitinClauses k acc = a at *
    generalize B.tseitinClauses a.next a.clauses = b at *
    simp only [CNF.eval_cons, Bool.and_eq_true] at h
    obtain ⟨hc₁, hc₂, hc₃, hb⟩ := h
    obtain ⟨ha, hvb⟩ := ihB hb
    obtain ⟨hacc, hva⟩ := ihA ha
    refine ⟨hacc, ?_⟩
    simp only [Clause.eval_cons, Literal.eval_mk, Clause.eval_nil, Bool.or_false, hva, hvb]
      at hc₁ hc₂ hc₃
    simp only [eval_and_bool, eval_or_bool, eval_imp_bool]
    revert hc₁ hc₂ hc₃
    cases σ b.next <;> cases A.eval (fun i : Fin n => σ i) <;>
      cases B.eval (fun i : Fin n => σ i) <;> decide

/-- **Every model of the numbered Tseitin transformation satisfies the proposition** at the
atoms. -/
theorem eval_of_eval_tseitinNumberedCNF {σ : ℕ → Bool} {A : Proposition (Fin n)}
    (h : A.tseitinNumberedCNF.eval σ = true) : (A.eval fun i : Fin n => σ i) = true := by
  simp only [tseitinNumberedCNF, CNF.eval_cons, Clause.eval_cons, Literal.eval_mk,
    Clause.eval_nil, Bool.or_false, beq_iff_eq, Bool.and_eq_true] at h
  exact (eval_tseitinClauses A n [] h.2).2.symm.trans h.1

/-- **The numbered Tseitin transformation preserves satisfiability.** -/
theorem satisfiable_tseitinNumberedCNF_iff (A : Proposition (Fin n)) :
    A.tseitinNumberedCNF.Satisfiable ↔ ∃ v : Fin n → Bool, A.eval v = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, eval_of_eval_tseitinNumberedCNF hσ⟩
  · rintro ⟨v, hv⟩
    exact ⟨tseitinExtend v ∘ A.tseitinNumberedVar, (eval_tseitinNumberedCNF_comp _ A).trans
      ((eval_tseitinCNF_tseitinExtend v A).trans hv)⟩

/-! ### Size -/

/-- **The numbered Tseitin transformation has linearly many clauses.** -/
theorem length_tseitinNumberedCNF_le (A : Proposition (Fin n)) :
    A.tseitinNumberedCNF.length ≤ 3 * A.size + 1 := by
  have := (perm_relabel_tseitinNumberedCNF A).length_eq
  simp only [CNF.relabel, List.length_map] at this
  exact this ▸ length_tseitinCNF_le A

/-- **Every clause of the numbered Tseitin transformation has at most three literals.** -/
theorem length_le_three_of_mem_tseitinNumberedCNF {A : Proposition (Fin n)} {c : Clause ℕ}
    (hc : c ∈ A.tseitinNumberedCNF) : c.length ≤ 3 := by
  have := length_le_three_of_mem_tseitinCNF ((perm_relabel_tseitinNumberedCNF A).subset
    (List.mem_map_of_mem (f := Clause.relabel A.tseitinNumberedVar) hc))
  simpa using this

end Cslib.Logic.PL.Proposition
