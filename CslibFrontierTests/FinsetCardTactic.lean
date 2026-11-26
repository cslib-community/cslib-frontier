/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the finset_card tactic)

public import CslibFrontier.Init
public import CslibFrontier.Tactic.FinsetCard

/-!
# Tests for `finset_card`
-/

public section

namespace FinsetCardTest

open scoped Finset

/-! ### Finite-universe quorum intersection and Boolean set algebra -/

example {α : Type*} [Fintype α] [DecidableEq α] (Q₁ Q₂ : Finset α)
    (h₁ : Fintype.card α < 2 * Q₁.card) (h₂ : Fintype.card α < 2 * Q₂.card) :
    0 < (Q₁ ∩ Q₂).card := by
  finset_card

example {α : Type*} [Fintype α] [DecidableEq α] (Q₁ Q₂ F : Finset α)
    (hb : 3 * F.card < Fintype.card α)
    (h₁ : Fintype.card α - F.card ≤ Q₁.card)
    (h₂ : Fintype.card α - F.card ≤ Q₂.card) :
    F.card < (Q₁ ∩ Q₂).card ∧ 0 < ((Q₁ ∩ Q₂) \ F).card := by
  finset_card

example {α : Type*} [Fintype α] [DecidableEq α] (S₁ S₂ F : Finset α)
    (h₁ : (Fintype.card α + F.card) / 2 < #S₁)
    (h₂ : (Fintype.card α + F.card) / 2 < #S₂) :
    #F < #(S₁ ∩ S₂) := by
  finset_card

example {α : Type*} [Fintype α] [DecidableEq α] (S T : Finset α) :
    (Sᶜ : Finset α).card + S.card = Fintype.card α ∧
      (S ∪ T).card + (S ∩ T).card = S.card + T.card := by
  finset_card

/-! ### Non-`Fintype` Boolean set algebra -/

example {α : Type*} [DecidableEq α] (Q₁ Q₂ F₂ : Finset α) :
    ((Q₂ \ Q₁) \ F₂).card + (Q₂ ∩ F₂).card =
      (Q₂ \ Q₁).card + (Q₁ ∩ Q₂ ∩ F₂).card := by
  finset_card

example {α : Type*} [DecidableEq α] (Q₁ Q₂ F₁ F₂ : Finset α)
    (h : (Q₂ \ Q₁).card + (F₁ ∩ Q₁).card < ((Q₂ \ Q₁) \ F₂).card + (Q₁ ∩ Q₂).card) :
    (F₂ ∩ Q₂).card < ((Q₁ ∩ Q₂) \ F₁).card + (Q₂ ∩ F₂).card := by
  finset_card

/-! ### Set relations and classical / mixed `DecidableEq` instances -/

example {α : Type*} (S T U : Finset α) (hST : S ⊆ T) (hTU : Disjoint T U) :
    Disjoint S U := by
  finset_card

example {α : Type*} [DecidableEq α] (A B C : Finset α)
    (hAB : A ⊆ B ∪ C) (hd : Disjoint A B) :
    A ⊆ C := by
  finset_card

example {α : Type*} [DecidableEq α] (A B : Finset α)
    (hsub : A ⊆ B) (hcard : B.card ≤ A.card) :
    A = B := by
  finset_card

example {α : Type*} [DecidableEq α] (A B : Finset α) (hne : A ≠ B) (hsub : A ⊆ B) :
    A.card < B.card := by
  finset_card

/-! ### Pigeonhole and nonemptiness witness goals -/

example {α : Type*} [Fintype α] [DecidableEq α] (Q₁ Q₂ F : Finset α)
    (hF : 3 * F.card < Fintype.card α)
    (h₁ : Fintype.card α - F.card ≤ Q₁.card)
    (h₂ : Fintype.card α - F.card ≤ Q₂.card) :
    ∃ p ∈ Q₁ ∩ Q₂, p ∉ F := by
  finset_card

example {α : Type*} [Fintype α] [DecidableEq α] (C : Finset α) (p : α)
    (hC : C.card + 1 < Fintype.card α) :
    ∃ q, q ∉ insert p C := by
  finset_card

example {α : Type*} [DecidableEq α] (S T : Finset α) (h : T.card < S.card) :
    ∃ x, x ∈ S \ T := by
  finset_card

/-! ### Points, singletons, `insert`, `erase`, and zero-atom memberships -/

example {P : Type*} [Fintype P] (F : Finset P) (i j : P)
    (hn : Fintype.card P ≤ 2) (hF : F.Nonempty) (hi : i ∉ F) (hj : j ∉ F) :
    i = j := by
  finset_card

example {P : Type*} [DecidableEq P] (S : Finset P) (x y : P)
    (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
    2 ≤ (insert x S).card ∧ 1 ≤ (S.erase x).card ∧ ({x} : Finset P).card = 1 := by
  finset_card

-- Eight unrelated point-membership hypotheses are eliminated without consuming Venn atoms.
example {P : Type*} [Fintype P] [DecidableEq P] (Q₁ Q₂ F : Finset P)
    (p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ : P)
    (_hp₁ : p₁ ∉ F) (_hp₂ : p₂ ∉ F) (_hp₃ : p₃ ∉ F) (_hp₄ : p₄ ∉ F)
    (_hp₅ : p₅ ∉ F) (_hp₆ : p₆ ∉ F) (_hp₇ : p₇ ∉ F) (_hp₈ : p₈ ∉ F)
    (h₁ : Fintype.card P < 2 * Q₁.card) (h₂ : Fintype.card P < 2 * Q₂.card) :
    (Q₁ ∩ Q₂).Nonempty := by
  finset_card

-- Goal-focused atom pruning ignores unrelated outer Finsets when > 5 exist in scope.
example {α : Type*} [DecidableEq α] (A B C U₁ U₂ U₃ U₄ : Finset α)
    (_hU₁ : U₁ ⊆ U₂) (_hU₂ : U₃ ⊆ U₄) (hAB : A ⊆ B ∪ C) :
    (A \ B).card ≤ C.card := by
  finset_card

/-! ### Filter subsets, disjoint fibers, and partitions -/

example {P V : Type*} [Fintype P] [DecidableEq V]
    (vote : P → V) (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (h₁ : Fintype.card P < 2 * (Finset.univ.filter fun p => vote p = v₁).card)
    (h₂ : Fintype.card P < 2 * (Finset.univ.filter fun p => vote p = v₂).card) :
    False := by
  finset_card

example {P : Type*} [Fintype P] (vote : P → Bool) :
    ({p : P | vote p = true} : Finset P).card +
      ({p : P | vote p = false} : Finset P).card = Fintype.card P := by
  finset_card

example {P : Type*} [DecidableEq P] (S : Finset P) (pred : P → Prop) [DecidablePred pred] :
    (S.filter pred).card + (S.filter fun p => ¬ pred p).card = S.card := by
  finset_card

example {P : Type*} [Fintype P] (f : P → ℕ) (k₁ k₂ : Fin 3) (hne : k₁ ≠ k₂) :
    let grp : Fin 3 → Finset P := fun k => Finset.univ.filter fun p => f p % 3 = k.val
    Disjoint (grp k₁) (grp k₂) := by
  intro grp
  finset_card

/-! ### `Finset.map` and `Finset.image` bounds across carriers -/

example {P : Type*} [Fintype P] {t : ℕ} (emb : Fin (t + 1) ↪ P)
    (S : Finset (Fin (t + 1))) (hS : S.card = t + 1) :
    t + 1 ≤ Fintype.card P ∧ (S.map emb).card = t + 1 := by
  finset_card

example {P : Type*} [Fintype P] {t : ℕ} (kings : Fin (t + 1) ↪ P) (F : Finset P)
    (hF : F.card ≤ t) (hsub : Finset.univ.map kings ⊆ F) : False := by
  finset_card

example {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 3 * k < Fintype.card V)
    (A : Finset V) (m : V → V) (hkA : A.card ≤ k) :
    let I : Finset V := (A ∪ A.image m)ᶜ
    k < I.card := by
  intro I
  finset_card

example {α β : Type*} [DecidableEq β] (f : α → β) (S : Finset α) (T : Finset β)
    (h : S.card < (S.image f).card + T.card) :
    0 < T.card := by
  finset_card

/-! ### Unfolding definitions and passing local hints in brackets -/

/-- Sample quorum predicate (`|P| - t ≤ |Q|`) for bracket-unfolding test. -/
def isTwoThirds {P : Type*} [Fintype P] (t : ℕ) (Q : Finset P) : Prop :=
  Fintype.card P - t ≤ Q.card

private theorem threshold_pos (n t : ℕ) (h : 3 * t < n) : t < n - 2 * t := by omega

private theorem isTwoThirds_iff {P : Type*} [Fintype P] (t : ℕ) (Q : Finset P) :
    isTwoThirds t Q ↔ Fintype.card P - t ≤ Q.card := Iff.rfl

example {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ} (Q₁ Q₂ F : Finset P)
    (qs : Finset (Finset P)) (_hq : ∀ A ∈ qs, ∀ B ∈ qs, t + 1 ≤ (A ∩ B).card)
    (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (h₁ : isTwoThirds t Q₁) (h₂ : isTwoThirds t Q₂) :
    ∃ p ∈ Q₁ ∩ Q₂, p ∉ F := by
  finset_card [isTwoThirds_iff, threshold_pos (Fintype.card P) t hn]

/-- Unrelated `Fin 10` point disequalities and unrelated `Finset β` carriers exceeding `maxAtoms`
do not trigger atom promotion or `maxAtoms` errors when solving a `Finset α` goal. -/
example {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (Q₁ Q₂ : Finset α) (h₁ : Fintype.card α < 2 * Q₁.card) (h₂ : Fintype.card α < 2 * Q₂.card)
    (k₁ k₂ k₃ k₄ k₅ k₆ k₇ : Fin 10)
    (_hk₁ : k₁ ≠ k₂) (_hk₂ : k₂ ≠ k₃) (_hk₃ : k₃ ≠ k₄)
    (_hk₄ : k₄ ≠ k₅) (_hk₅ : k₅ ≠ k₆) (_hk₆ : k₆ ≠ k₇)
    (B₁ B₂ B₃ B₄ B₅ B₆ : Finset β) (_hB : (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆).card ≤ 10) :
    (Q₁ ∩ Q₂).Nonempty := by
  finset_card

/-! ### Diagnostic failure modes -/

/--
error: finset_card: no `Finset` or `Fintype.card` terms found; use `omega` for plain arithmetic.
  a b : ℕ
  h : a < b
  ⊢ a ≤ b
-/
#guard_msgs in
example (a b : ℕ) (h : a < b) : a ≤ b := by
  finset_card

/--
error: finset_card: carrier 'α' has 6 atomic finsets (limit: 5): [A₁, A₂, A₃, A₄, A₅, A₆].
  Bound or combine intermediate sets before calling `finset_card`.
-/
#guard_msgs (whitespace := lax) in
example {α : Type*} [DecidableEq α] (A₁ A₂ A₃ A₄ A₅ A₆ : Finset α) :
    (A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅ ∩ A₆).card ≤ A₁.card := by
  finset_card

/--
Note: finset_card reduced 1 finite-set carrier(s) to Venn-region cardinalities, and `omega`
  could not close the resulting Presburger goal:
-/
#guard_msgs (whitespace := lax, substring := true) in
example {α : Type*} [Fintype α] [DecidableEq α] (Q₁ Q₂ : Finset α)
    (h₁ : Fintype.card α ≤ 2 * Q₁.card) (h₂ : Fintype.card α ≤ 2 * Q₂.card) :
    0 < (Q₁ ∩ Q₂).card := by
  finset_card

end FinsetCardTest

end
