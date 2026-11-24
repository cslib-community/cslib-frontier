/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Sigma.OneHot
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.MonomialExtension
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum

/-!
# Clause sums

A *clause* is a list of literals together with a weight; it contributes its weight when all its
literals hold and `1` otherwise. A *clause sum* sums the product of the contributions of a family
of clauses over all assignments of the bits (`clauseSum`). This file adds two variants:

* `clauseSumWith x`: some bits are fixed to `x`, and the sum runs over the others. Adding one clause
  for every fixed bit, with the variable of that bit as weight, turns the clause sum into the
  monomial extension of `clauseSumWith` (`clauseSum_withInputs`).
* `domainClauseSum x`: the hidden part is a function `g : ∀ d, E d` on a finite domain, and a
  literal about `g` says `g d = e` or `g d ≠ e`. Through the one-hot encoding of `g` and clauses
  that force one value at every point (`oneHotLits`, `oneHotWeights`), it is a clause sum over bits
  (`domainClauseSum_eq_clauseSumWith`).

## Main definitions

* `Cslib.Circuits.Arithmetic.clauseSum`, `clauseSumWith`, `domainClauseSum`.
* `Cslib.Circuits.Arithmetic.withInputs`, `inputWeights`, `oneHotLits`, `oneHotWeights`.

## Main results

* `Cslib.Circuits.Arithmetic.clauseSum_withInputs`.
* `Cslib.Circuits.Arithmetic.domainClauseSum_eq_clauseSumWith`,
  `Cslib.Circuits.Arithmetic.domainClauseSum_sumElim`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  modules `Nc.WidePerm`, `Nc.FinDom` and `Paper.CircuitPhi` (`clauseSum_inputs`)
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial Finset

variable {R : Type*} [CommSemiring R]

/-- A *clause sum*: the sum, over the bits `x`, of the product over the clauses `κ` of the weight
of `κ` if all its literals hold, and `1` otherwise. A literal `(b, e)` holds when `x b = e`. -/
@[expose] noncomputable def clauseSum {R V Θ : Type*} [CommSemiring R] [Fintype V] [DecidableEq V]
    [Fintype Θ] (lits : Θ → List (V × Bool)) (wt : Θ → R) : R :=
  ∑ x : V → Bool, ∏ κ, if ∀ l ∈ lits κ, x l.1 = l.2 then wt κ else 1

section With

variable {ι α Θ : Type*} [Fintype α] [DecidableEq α] [Fintype Θ]

/-- A clause sum with the bits on `ι` fixed to `x`: the sum runs over the bits on `α` only. -/
@[expose] def clauseSumWith (lits : Θ → List ((ι ⊕ α) × Bool)) (wt : Θ → R) (x : ι → Bool) : R :=
  ∑ a : α → Bool, ∏ κ, if ∀ l ∈ lits κ, Sum.elim x a l.1 = l.2 then wt κ else 1

/-- One more clause for every fixed bit: the literal that the bit is set. -/
@[expose] def withInputs (lits : Θ → List ((ι ⊕ α) × Bool)) : Θ ⊕ ι → List ((ι ⊕ α) × Bool) :=
  Sum.elim lits fun b => [(Sum.inl b, true)]

/-- The weights: the constants `wt`, and the variable of every fixed bit. -/
@[expose] noncomputable def inputWeights (wt : Θ → R) : Θ ⊕ ι → MvPolynomial ι R :=
  Sum.elim (fun κ => C (wt κ)) X

/-- **Fixed bits as variables.** With one clause per fixed bit whose weight is its variable, the
clause sum over all bits is the monomial extension of the clause sum with fixed bits. -/
theorem clauseSum_withInputs [Fintype ι] [DecidableEq ι] (lits : Θ → List ((ι ⊕ α) × Bool))
    (wt : Θ → R) :
    clauseSum (withInputs lits) (inputWeights wt) = monomialExtension (clauseSumWith lits wt) := by
  classical
  unfold clauseSum monomialExtension clauseSumWith
  rw [← (Equiv.sumArrowEquivProdArrow ι α Bool).symm.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [map_sum, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [Fintype.prod_sum_type, map_prod]
  refine congrArg₂ (· * ·) (prod_congr rfl fun κ _ => ?_) (prod_congr rfl fun b _ => ?_)
  · have e : (Equiv.sumArrowEquivProdArrow ι α Bool).symm (x, a) = Sum.elim x a := rfl
    simp only [withInputs, inputWeights, Sum.elim_inl, e]
    rw [apply_ite (C : R → MvPolynomial ι R), map_one]
    split_ifs <;> rfl
  · cases hx : x b <;> simp [withInputs, inputWeights, hx]

end With

section Domain

variable {ι D Θ : Type*} [Fintype D] [DecidableEq D] {E : D → Type*} [∀ d, Fintype (E d)]
  [∀ d, DecidableEq (E d)] [Fintype Θ]

/-- A clause sum over the functions `g : ∀ d, E d`, with the bits on `ι` fixed to `x`. A literal
`(⟨d, e⟩, b)` about `g` says `g d = e` (for `b = true`) or `g d ≠ e`. -/
@[expose] def domainClauseSum (lits : Θ → List ((ι ⊕ Σ d, E d) × Bool)) (wt : Θ → R)
    (x : ι → Bool) : R :=
  ∑ g : ∀ d, E d, ∏ κ, if ∀ l ∈ lits κ, Sum.elim x (Pi.oneHot g) l.1 = l.2 then wt κ else 1

/-- The clauses of `lits`, then one clause per point that no value is taken, then one per pair of
bits that both are set. -/
@[expose] noncomputable def oneHotLits (lits : Θ → List ((ι ⊕ Σ d, E d) × Bool)) :
    Θ ⊕ D ⊕ ((Σ d, E d) × (Σ d, E d)) → List ((ι ⊕ Σ d, E d) × Bool)
  | .inl κ => lits κ
  | .inr (.inl d) => (univ : Finset (E d)).toList.map fun e => (.inr ⟨d, e⟩, false)
  | .inr (.inr (p, q)) => [(.inr p, true), (.inr q, true)]

/-- Their weights: those of `wt`, `0` for a point without a value, and `0` for two values at one
point. -/
@[expose] def oneHotWeights (wt : Θ → R) : Θ ⊕ D ⊕ ((Σ d, E d) × (Σ d, E d)) → R
  | .inl κ => wt κ
  | .inr (.inl _) => 0
  | .inr (.inr (p, q)) => if p.1 = q.1 ∧ p ≠ q then 0 else 1

/-- **Clause sums over finite domains are clause sums over bits**: the bits are the one-hot
encoding of the function, and the clauses `oneHotLits` with weights `oneHotWeights` kill every
assignment of the bits that is not one. -/
theorem domainClauseSum_eq_clauseSumWith (lits : Θ → List ((ι ⊕ Σ d, E d) × Bool)) (wt : Θ → R)
    (x : ι → Bool) :
    domainClauseSum lits wt x = clauseSumWith (oneHotLits lits) (oneHotWeights wt) x := by
  unfold domainClauseSum clauseSumWith
  refine sum_of_injOn Pi.oneHot Pi.oneHot_injective.injOn (fun _ _ => mem_univ _) ?_ ?_
  · intro a _ ha
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    -- `a` is no one-hot encoding: some point has no set bit, or two
    have hna : ¬ ∀ d, ∃! e, a ⟨d, e⟩ = true := fun h =>
      ha (by simpa using (Pi.exists_oneHot_eq_iff a).2 h)
    obtain ⟨d, hd⟩ := not_forall.1 hna
    by_cases hex : ∃ e, a ⟨d, e⟩ = true
    · obtain ⟨e, he⟩ := hex
      obtain ⟨e', he', hne⟩ : ∃ e', a ⟨d, e'⟩ = true ∧ e' ≠ e := by
        by_contra h
        push Not at h
        exact hd ⟨e, he, h⟩
      have : (∏ q : (Σ d, E d) × (Σ d, E d),
          if ∀ l ∈ oneHotLits lits (.inr (.inr q)), Sum.elim x a l.1 = l.2 then
            oneHotWeights (E := E) wt (.inr (.inr q)) else 1) = 0 := by
        refine prod_eq_zero (mem_univ (⟨d, e'⟩, ⟨d, e⟩)) ?_
        have hpq : (⟨d, e'⟩ : Σ d, E d) ≠ ⟨d, e⟩ := fun h => hne (eq_of_heq (Sigma.mk.inj h).2)
        simp [oneHotLits, oneHotWeights, he, he', hpq]
      rw [this, mul_zero, mul_zero]
    · push Not at hex
      have : (∏ d : D, if ∀ l ∈ oneHotLits lits (.inr (.inl d)), Sum.elim x a l.1 = l.2 then
            oneHotWeights (E := E) wt (.inr (.inl d)) else 1) = 0 := by
        refine prod_eq_zero (mem_univ d) ((ite_eq_left fun l hl => ?_).trans rfl)
        simp only [oneHotLits, List.mem_map, Finset.mem_toList, mem_univ, true_and] at hl
        obtain ⟨e, rfl⟩ := hl
        simpa using hex e
      rw [this, zero_mul, mul_zero]
  · intro g _
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    have h1 : (∏ d : D, if ∀ l ∈ oneHotLits lits (.inr (.inl d)),
          Sum.elim x (Pi.oneHot g) l.1 = l.2 then oneHotWeights (E := E) wt (.inr (.inl d)) else 1)
          = 1 := by
      refine prod_eq_one fun d _ => ite_eq_right fun h => ?_
      have := h (.inr ⟨d, g d⟩, false) (by simp [oneHotLits])
      simp at this
    have h2 : (∏ q : (Σ d, E d) × (Σ d, E d),
          if ∀ l ∈ oneHotLits lits (.inr (.inr q)), Sum.elim x (Pi.oneHot g) l.1 = l.2 then
            oneHotWeights (E := E) wt (.inr (.inr q)) else 1) = 1 := by
      refine prod_eq_one ?_
      rintro ⟨⟨d, e⟩, ⟨d', e'⟩⟩ _
      split_ifs with h
      · simp only [oneHotLits, List.forall_mem_cons, Sum.elim_inr, Pi.oneHot_apply,
          decide_eq_true_eq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        simp only [oneHotWeights]
        refine ite_eq_right ?_
        rintro ⟨hd, hne⟩
        subst hd
        exact hne rfl
      · rfl
    rw [h1, h2, mul_one, mul_one]
    rfl

/-- Clauses whose product does not depend on the function factor out of the sum. -/
theorem domainClauseSum_sumElim {Θ' : Type*} [Fintype Θ'] (lits : Θ → List ((ι ⊕ Σ d, E d) × Bool))
    (wt : Θ → R) (lits' : Θ' → List ((ι ⊕ Σ d, E d) × Bool)) (wt' : Θ' → R) (x : ι → Bool) (c : R)
    (h : ∀ g : ∀ d, E d,
      (∏ κ, if ∀ l ∈ lits' κ, Sum.elim x (Pi.oneHot g) l.1 = l.2 then wt' κ else 1) = c) :
    domainClauseSum (Sum.elim lits lits') (Sum.elim wt wt') x = domainClauseSum lits wt x * c := by
  unfold domainClauseSum
  rw [sum_mul]
  refine sum_congr rfl fun g _ => ?_
  rw [Fintype.prod_sum_type, ← h g]
  rfl

end Domain

end Cslib.Circuits.Arithmetic
