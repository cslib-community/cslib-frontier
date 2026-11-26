/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ComputedWithin
public import CslibFrontier.Foundations.Data.MvPolynomial.SetMultilinearProjection

/-!
# Balanced products

Let the variables of a polynomial be divided into `k ≥ 2` blocks. If the polynomial is computed
by a circuit with `s` nodes, then its set-multilinear part on all blocks
(`MvPolynomial.smProj blk univ`, the part that is linear in every block) is a sum of products
`g * h`: for every *balanced* set `S` of blocks, one with `k / 3 ≤ |S| ≤ 2 k / 3`, there are `s`
products, in which `g` is set-multilinear on `S` and `h` on the other blocks
(`Flat.exists_balanced_products`). So the part of the polynomial on all blocks is a sum, over the
balanced sets, of tensors of rank at most `s` across the set and its complement. The semiring of
coefficients is arbitrary.

This is [AnthropicVPVNP2026], Lemma E.4, an argument as in depth reduction: walk from the output
towards the inputs along a factor whose part has more than `2 k / 3` blocks, until a factor is
balanced. In the source (modules `Nc.CaseI.Multi` and `Paper.Flat`) the parts are given by their
coefficients; here they are the projections `MvPolynomial.smProj`, whose product rule
`MvPolynomial.smProj_mul` is the step of the walk.

## Main results

* `Flat.exists_balanced_products_of_steps`: the statement for a list of gates.
* `Flat.exists_balanced_products`: the statement for `ComputedWithin`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma E.4 (balanced products); modules `Nc.CaseI.Multi` and `Paper.Flat`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset MvPolynomial

variable {σ K : Type*} [CommSemiring K] {k : ℕ}

/-- The balanced subsets of a set of blocks. -/
private def bal (S : Finset (Fin k)) : Finset (Finset (Fin k)) :=
  S.powerset.filter fun A => k ≤ 3 * A.card ∧ 3 * A.card ≤ 2 * k

private theorem mem_bal {S A : Finset (Fin k)} :
    A ∈ bal S ↔ A ⊆ S ∧ k ≤ 3 * A.card ∧ 3 * A.card ≤ 2 * k := by
  rw [bal, mem_filter, mem_powerset]

/-- `f` is a sum, over the gates `δ < s` and the balanced sets `A ⊆ S`, of the part of the gate
on `A` times a polynomial that is set-multilinear on the rest of `S`. -/
private def Dec (blk : σ → Fin k) (l : ℕ → MvPolynomial σ K) (s : ℕ) (S : Finset (Fin k))
    (f : MvPolynomial σ K) : Prop :=
  ∃ h : Fin s → Finset (Fin k) → MvPolynomial σ K,
    (∀ δ, ∀ A ∈ bal S, IsSetMultilinear blk (S \ A) (h δ A)) ∧
      f = ∑ δ : Fin s, ∑ A ∈ bal S, smProj blk A (l δ) * h δ A

section Dec

variable {blk : σ → Fin k} {l : ℕ → MvPolynomial σ K} {s : ℕ} {S : Finset (Fin k)}

private theorem Dec.zero : Dec blk l s S 0 :=
  ⟨fun _ _ => 0, fun _ _ _ => .zero, by simp⟩

private theorem Dec.add {f g : MvPolynomial σ K} (hf : Dec blk l s S f) (hg : Dec blk l s S g) :
    Dec blk l s S (f + g) := by
  obtain ⟨h, h1, rfl⟩ := hf
  obtain ⟨h', h1', rfl⟩ := hg
  refine ⟨fun δ A => h δ A + h' δ A, fun δ A hA => (h1 δ A hA).add (h1' δ A hA), ?_⟩
  simp only [mul_add, sum_add_distrib]

private theorem Dec.sum {ι : Type*} (B : Finset ι) {f : ι → MvPolynomial σ K}
    (hf : ∀ i ∈ B, Dec blk l s S (f i)) : Dec blk l s S (∑ i ∈ B, f i) := by
  classical
  induction B using Finset.induction_on with
  | empty => simpa using Dec.zero
  | insert i B hi ih =>
    rw [sum_insert hi]
    exact (hf i (mem_insert_self i B)).add (ih fun j hj => hf j (mem_insert_of_mem hj))

/-- One product: the part of a gate on a balanced set, times a polynomial on the rest. -/
private theorem Dec.single {A : Finset (Fin k)} (hA : A ∈ bal S) {δ : ℕ} (hδ : δ < s)
    {q : MvPolynomial σ K} (hq : IsSetMultilinear blk (S \ A) q) :
    Dec blk l s S (smProj blk A (l δ) * q) := by
  classical
  refine ⟨fun δ' A' => if δ' = ⟨δ, hδ⟩ ∧ A' = A then q else 0, fun δ' A' _ => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact h.2 ▸ hq
    · exact .zero
  · rw [sum_eq_single (⟨δ, hδ⟩ : Fin s) (fun b _ hb => sum_eq_zero fun A' _ => by simp [hb])
      (by simp), sum_eq_single A (fun A' _ hA' => by simp [hA']) (fun h => absurd hA h)]
    simp

/-- A decomposition on `S` times a polynomial on the rest of a larger set `S'`. -/
private theorem Dec.mul {S' : Finset (Fin k)} (hS : S ⊆ S') {f q : MvPolynomial σ K}
    (hf : Dec blk l s S f) (hq : IsSetMultilinear blk (S' \ S) q) :
    Dec blk l s S' (f * q) := by
  classical
  obtain ⟨h, h1, rfl⟩ := hf
  have hsub : bal S ⊆ bal S' := fun A hA =>
    mem_bal.2 ⟨(mem_bal.1 hA).1.trans hS, (mem_bal.1 hA).2⟩
  refine ⟨fun δ A => if A ∈ bal S then h δ A * q else 0, fun δ A _ => ?_, ?_⟩
  · dsimp only
    split_ifs with hA
    · have hAS := (mem_bal.1 hA).1
      rw [show S' \ A = S \ A ∪ S' \ S by
        ext i
        simp only [mem_union, mem_sdiff]
        constructor
        · exact fun ⟨h1, h2⟩ => (em (i ∈ S)).imp (fun h => ⟨h, h2⟩) fun h => ⟨h1, h⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨hS h1, h2⟩
          · exact ⟨h1, fun h => h2 (hAS h)⟩]
      exact (h1 δ A hA).mul hq (disjoint_left.2 fun i hi hi' =>
        (mem_sdiff.1 hi').2 (mem_sdiff.1 hi).1)
    · exact .zero
  · rw [sum_mul]
    refine sum_congr rfl fun δ _ => ?_
    rw [sum_mul, ← sum_subset hsub fun A _ hA => by simp only [ite_eq_right hA, mul_zero]]
    exact sum_congr rfl fun A hA => by simp only [ite_eq_left hA, mul_assoc]

end Dec

/-- The induction over the gates: the part of a gate on more than `2 k / 3` blocks is a sum of
balanced products. -/
private theorem dec_gate {s : ℕ} {l : ℕ → MvPolynomial σ K} (blk : σ → Fin k)
    (hl : ∀ γ < s, (∃ i, l γ = X i) ∨ (∃ a, l γ = C a) ∨
      (∃ i < γ, ∃ j < γ, l γ = l i + l j) ∨ (∃ i < γ, ∃ j < γ, l γ = l i * l j))
    (hk : 2 ≤ k) (γ : ℕ) (hγ : γ < s) (S : Finset (Fin k)) (hS : 2 * k < 3 * S.card) :
    Dec blk l s S (smProj blk S (l γ)) := by
  induction γ using Nat.strong_induction_on generalizing S with
  | _ γ ih =>
    rcases hl γ hγ with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
    · rw [h1, smProj_X, ite_eq_right fun h => by rw [h, card_singleton] at hS; omega]
      exact Dec.zero
    · rw [h1, smProj_C, ite_eq_right fun h => by rw [h, card_empty] at hS; omega]
      exact Dec.zero
    · rw [h1, map_add]
      exact (ih i hi (by omega) S hS).add (ih j hj (by omega) S hS)
    · rw [h1, smProj_mul]
      refine Dec.sum _ fun A hA => ?_
      have hAS := mem_powerset.1 hA
      have hcard : (S \ A).card + A.card = S.card := card_sdiff_add_card_eq_card hAS
      have hSA : S \ (S \ A) = A := Finset.sdiff_sdiff_eq_self hAS
      by_cases c1 : 2 * k < 3 * A.card
      · exact (ih i hi (by omega) A c1).mul hAS (isSetMultilinear_smProj blk _ _)
      by_cases c2 : k ≤ 3 * A.card
      · exact Dec.single (mem_bal.2 ⟨hAS, c2, by omega⟩) (by omega)
          (isSetMultilinear_smProj blk _ _)
      rw [mul_comm]
      by_cases c3 : 2 * k < 3 * (S \ A).card
      · exact (ih j hj (by omega) _ c3).mul sdiff_subset
          (hSA.symm ▸ isSetMultilinear_smProj blk _ _)
      · exact Dec.single (mem_bal.2 ⟨sdiff_subset, by omega, by omega⟩) (by omega)
          (hSA.symm ▸ isSetMultilinear_smProj blk _ _)

/-- **Balanced products, for a list of gates** ([AnthropicVPVNP2026], Lemma E.4). If every entry
`l γ`, `γ < s`, of a list of polynomials is a variable, a constant, or the sum or product of two
earlier entries, then the set-multilinear part of an entry on all of `k ≥ 2` blocks is a sum, over
the sets `S` of blocks with `k ≤ 3 |S| ≤ 2 k`, of `s` products of a polynomial that is
set-multilinear on `S` and one that is set-multilinear on the other blocks. -/
theorem exists_balanced_products_of_steps {s : ℕ} {l : ℕ → MvPolynomial σ K} (blk : σ → Fin k)
    (hl : ∀ γ < s, (∃ i, l γ = X i) ∨ (∃ a, l γ = C a) ∨
      (∃ i < γ, ∃ j < γ, l γ = l i + l j) ∨ (∃ i < γ, ∃ j < γ, l γ = l i * l j))
    (hk : 2 ≤ k) {γ : ℕ} (hγ : γ < s) :
    ∃ g h : Finset (Fin k) → Fin s → MvPolynomial σ K,
      (∀ S δ, IsSetMultilinear blk S (g S δ)) ∧ (∀ S δ, IsSetMultilinear blk Sᶜ (h S δ)) ∧
      smProj blk univ (l γ) =
        ∑ S with k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k, ∑ δ, g S δ * h S δ := by
  classical
  obtain ⟨h, h1, h2⟩ := dec_gate blk hl hk γ hγ univ (by
    rw [card_univ, Fintype.card_fin]
    omega)
  have hbal : bal (univ : Finset (Fin k)) =
      univ.filter fun S => k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k := by
    ext S
    simp [mem_bal]
  refine ⟨fun S δ => smProj blk S (l δ), fun S δ => if S ∈ bal univ then h δ S else 0,
    fun S δ => isSetMultilinear_smProj blk S _, fun S δ => ?_, ?_⟩
  · dsimp only
    split_ifs with hS
    · exact compl_eq_univ_sdiff S ▸ h1 δ S hS
    · exact .zero
  · rw [h2, sum_comm, ← hbal]
    exact sum_congr rfl fun S hS => sum_congr rfl fun δ _ => by simp only [ite_eq_left hS]

/-- **Balanced products** ([AnthropicVPVNP2026], Lemma E.4). If a polynomial is computed by a
circuit with at most `s` nodes, then its set-multilinear part on all of `k ≥ 2` blocks of
variables is a sum, over the sets `S` of blocks with `k ≤ 3 |S| ≤ 2 k`, of `s` products of a
polynomial that is set-multilinear on `S` and one that is set-multilinear on the other blocks. -/
theorem exists_balanced_products {P : MvPolynomial σ K} {s : ℕ} (hP : ComputedWithin P s)
    (blk : σ → Fin k) (hk : 2 ≤ k) :
    ∃ g h : Finset (Fin k) → Fin s → MvPolynomial σ K,
      (∀ S δ, IsSetMultilinear blk S (g S δ)) ∧ (∀ S δ, IsSetMultilinear blk Sᶜ (h S δ)) ∧
      smProj blk univ P =
        ∑ S with k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k, ∑ δ, g S δ * h S δ := by
  obtain ⟨l, hl, γ, hγ, rfl⟩ := hP.exists_steps
  exact exists_balanced_products_of_steps blk hl hk hγ

end Cslib.Circuits.Arithmetic.Separation.Flat
