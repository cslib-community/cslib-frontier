/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Network
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option

/-!
# Routing a tensor through two hubs

Lemma A.3 of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. A tensor that is a sum of `r`
products of a tensor on one part of its parties and a tensor on the other is a restriction of the
product of the wires from its parties to two hubs and one wire of dimension `r` between the hubs
(`Cslib.PartyTensor.push_le_prod_wire_hubs`). With two further parties as hubs this is
`Cslib.PartyTensor.push_inl_le_prod_wire_hubs`.

## Main results

* `Cslib.PartyTensor.push_le_prod_wire_hubs`, `Cslib.PartyTensor.push_inl_le_prod_wire_hubs`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma A.3 (§A.2) of the paper; module `Paper.Prices` (`lem_hubs`, `lem_hubs_further`)
-/

public section

namespace Cslib.PartyTensor

open Finset

variable {K : Type} [CommSemiring K] {I : Type} [Fintype I] [DecidableEq I]

/-- **Paper: Lemma A.3 (lem:hubs).** Let `I = I₁ ⊔ I₂`, and let a tensor `t` on `I` with index sizes
`n_p` be a sum of `r` products of a tensor on `I₁` and one on `I₂`. For two further parties
`o₁, o₂`, `t` is a restriction of `∏_{p ∈ I₁} ⟨n_p⟩_{p o₁} · ⟨r⟩_{o₁ o₂} · ∏_{p ∈ I₂} ⟨n_p⟩_{p o₂}`,
also when `o₁, o₂` are identified with given parties. In Lean the paper's I is A, its part I₁ is
given by the predicate S, and α j, β j are the factors of the j-th product, functions of the indices
in I₁ and in I₂. The map π places the parties of A among those of a set I that also contains o₁ and
o₂, in any way; `push_inl_le_prod_wire_hubs` is the case of two further parties. -/
theorem push_le_prod_wire_hubs {A : Type} [Fintype A] [DecidableEq A] (π : A → I)
    (t : PartyTensor K A) (S : A → Prop) [DecidablePred S]
    {r : ℕ} (α β : Fin r → (∀ a, t.Index a) → K)
    (hα : ∀ j x x', (∀ a, S a → x a = x' a) → α j x = α j x')
    (hβ : ∀ j x x', (∀ a, ¬ S a → x a = x' a) → β j x = β j x')
    (hs : ∀ x, t.entry x = ∑ j, α j x * β j x) (o₁ o₂ : I) :
    push π t ≤
      prod (fun a => wire K (Fintype.card (t.Index a)) (π a) (if S a then o₁ else o₂)) *
          wire K r o₁ o₂ := by
  classical
  let Λ : Option A → Type := fun o => match o with
    | none => Fin r
    | some a => t.Index a
  let iΛ : ∀ o, Fintype (Λ o) := fun o => match o with
    | none => inferInstanceAs (Fintype (Fin r))
    | some a => inferInstanceAs (Fintype (t.Index a))
  let ξ : A ⊕ Bool → I := Sum.elim π fun b => if b then o₁ else o₂
  let src : Option A → A ⊕ Bool := fun o => o.elim (Sum.inr true) Sum.inl
  let tgt : Option A → A ⊕ Bool := fun o => o.elim (Sum.inr false) fun a => Sum.inr (decide (S a))
  let tab : A ⊕ Bool → (∀ a, t.Index a) → (∀ o, Λ o) → K := fun v x l => match v with
    | Sum.inl a => if x a = l (some a) then 1 else 0
    | Sum.inr true => α (l none) fun a => l (some a)
    | Sum.inr false => β (l none) fun a => l (some a)
  have key := push_le_of_edges π ξ t Λ src tgt tab (by
    rintro (a | b) x x' l l' hx hl
    · have h1 := hx a rfl
      have h2 : l (some a) = l' (some a) := hl (some a) (Or.inl rfl)
      change (if x a = l (some a) then (1 : K) else 0) = if x' a = l' (some a) then 1 else 0
      rw [h1, h2]
    · cases b
      · have h1 : l none = l' none := hl none (Or.inr rfl)
        change β (l none) _ = β (l' none) _
        rw [h1]
        refine hβ _ _ _ fun a ha => hl (some a) (Or.inr ?_)
        change Sum.inr (decide (S a)) = _
        simp [ha]
      · have h1 : l none = l' none := hl none (Or.inl rfl)
        change α (l none) _ = α (l' none) _
        rw [h1]
        refine hα _ _ _ fun a ha => hl (some a) (Or.inr ?_)
        change Sum.inr (decide (S a)) = _
        simp [ha]) (by
    intro x
    have e1 : ∀ l : ∀ o, Λ o, ∏ v, tab v x l =
        (∏ a, if x a = l (some a) then (1 : K) else 0) *
          (α (l none) (fun a => l (some a)) * β (l none) fun a => l (some a)) := by
      intro l
      rw [Fintype.prod_sum_type]
      congr 1
      rw [Fintype.prod_bool]
    simp only [e1]
    rw [hs]
    symm
    refine (Fintype.sum_equiv (Equiv.piOptionEquivProd (β := Λ)) _
      (fun z : Λ none × (∀ a, Λ (some a)) => (∏ a, if x a = z.2 a then (1 : K) else 0) *
          (α z.1 z.2 * β z.1 z.2)) fun l => rfl).trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hy
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right fun hxy => ha hxy.symm), zero_mul]
    · simp)
  refine key.trans ((antisymmRel_prod_reindex _ (Equiv.optionEquivSumPUnit A).symm).1.trans
    ((antisymmRel_prod_sum _).1.trans
        (mul_le_mul' (prod_le_prod fun a => ?_) ((antisymmRel_prod_unique _).1.trans ?_))))
  · change wire K (Fintype.card (t.Index a)) (π a) (if decide (S a) then o₁ else o₂) ≤ _
    simp only [decide_eq_true_eq]
    exact le_refl _
  · change wire K (Fintype.card (Fin r)) o₁ o₂ ≤ _
    rw [Fintype.card_fin]

/-- Lemma A.3 for two further parties `o₁, o₂`: the parties are `I₁ ⊔ I₂` and the two hubs. -/
theorem push_inl_le_prod_wire_hubs {I₁ I₂ : Type} [Fintype I₁] [DecidableEq I₁] [Fintype I₂]
    [DecidableEq I₂]
    (t : PartyTensor K (I₁ ⊕ I₂)) {r : ℕ} (α : Fin r → (∀ p, t.Index (Sum.inl p)) → K)
        (β : Fin r → (∀ p, t.Index (Sum.inr p)) → K)
    (hs : ∀ x, t.entry x = ∑ j, α j (fun p => x (Sum.inl p)) * β j fun p => x (Sum.inr p)) :
    push (Sum.inl : I₁ ⊕ I₂ → (I₁ ⊕ I₂) ⊕ Bool) t ≤
      prod (fun p : I₁ => wire K (Fintype.card (t.Index (Sum.inl p))) (Sum.inl (Sum.inl p))
          (Sum.inr true)) *
        wire K r (Sum.inr true) (Sum.inr false) *
        prod fun p : I₂ => wire K (Fintype.card (t.Index (Sum.inr p))) (Sum.inl (Sum.inr p))
            (Sum.inr false) := by
  have key :=
      push_le_prod_wire_hubs (Sum.inl : I₁ ⊕ I₂ → (I₁ ⊕ I₂) ⊕ Bool) t (fun a => a.isLeft = true)
    (fun j x => α j fun p => x (Sum.inl p)) (fun j x => β j fun p => x (Sum.inr p))
    (fun j x x' h => congrArg (α j) (funext fun p => h (Sum.inl p) rfl))
    (fun j x x' h => congrArg (β j) (funext fun p => h (Sum.inr p) (by simp))) hs (Sum.inr true)
        (Sum.inr false)
  refine key.trans ((mul_le_mul' (antisymmRel_prod_sum _).1 (le_refl _)).trans ?_)
  exact (antisymmRel_mul_assoc _ _ _).le.trans
      ((mul_le_mul' le_rfl (antisymmRel_mul_comm _ _).le).trans
    (antisymmRel_mul_assoc _ _ _).ge)

end Cslib.PartyTensor
