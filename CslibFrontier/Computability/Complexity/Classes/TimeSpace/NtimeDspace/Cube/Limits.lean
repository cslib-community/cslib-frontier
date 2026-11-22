/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Limits of the method: pieces of the crossing over OR and AND, and over the integers

This file formalizes the two lower bounds of `separating-ntime-from-space.tex`, §8 ("Limits and open
problems"), on
the number of bits through which pieces of the crossing must factor.

Following §8, a function `Γ` of two arguments *factors through `c` bits* if
`Γ(z, z') = ∑_{θ ∈ {0,1}^c} φ(z, θ) φ'(z', θ)`, and *over OR and AND* if the same holds with `⋁`
and `∧`. The cuts are those of §5: the row cut separates `(x, y)` from `(u, v)`, and the column
cut separates `(x, u)` from `(y, v)`.

## Main definitions

* `FactorsThrough Γ c`: `Γ : α → β → ℤ` factors through `c` bits, with
  `φ : α → (Fin c → Bool) → ℤ` and `φ' : β → (Fin c → Bool) → ℤ`.
* `FactorsThroughOr Γ c`: `Γ : α → β → Bool` factors over OR and AND through `c` bits, with
  Boolean `φ, φ'`; that is, `Γ z z' = true ↔ ∃ θ, φ z θ = true ∧ φ' z' θ = true`.

## Main results

* `card_le_of_factorsThroughOr`: the fooling-set bound. If `Γ` factors over OR and AND through
  `c` bits, a set of ones of `Γ` no two of which can be crossed has at most `2^c` elements.
* `rank_le_of_factorsThrough`: a function that factors through `c` bits has rank at most `2^c`
  over `ℚ`.
* `prop_boolean` (Proposition 8.1, `prop:boolean`). For
  `P : Fin N → (Fin λ → Bool) → (Fin λ → Bool) → (Fin λ → Bool) → (Fin λ → Bool) → Bool`,
  arguments in the order `x y u v`, with `(∃ i, P i x y u v = true) ↔ (x = v ∧ y = u)`, and each
  `P i` factoring over OR and AND through `r i` bits across the row cut and `c i` bits across the
  column cut, some `i` has `2 ^ (4 * λ) ≤ N ^ 2 * 2 ^ (r i + c i)`. This is the paper's
  `r_i + c_i ≥ 4λ − 2 log N` after exponentiating. `prop_boolean_each` gives the intermediate
  statement of the paper's proof: the same `i` has `2^(2λ) ≤ N · 2^(r i)` and
  `2^(2λ) ≤ N · 2^(c i)`.
* `prop_barrier` (Proposition 8.2, `prop:barrier`). For
  `P : Fin N → (Fin a → Bool) → (Fin a → Bool) → ℤ` with `∑ i, P i x v = [x = v]`, and each
  `P i` factoring through `r i` bits and through `c i` bits, some `i` has
  `2 ^ a ≤ N * 2 ^ min (r i) (c i)`, the paper's `min(r_i, c_i) ≥ a − log N`.

## Differences from the paper

* The bounds are stated multiplicatively with natural-number powers instead of with `log N`;
  for `N ≥ 1` they are equivalent to the paper's. `N ≥ 1` is not assumed: it follows from the
  hypotheses, since the crossing, and the equality matrix, are not identically zero.
* `⋁_i Π_i` is the existential `∃ i, P i x y u v = true`, and the piece names `Π_i` become
  `P i` (`Π` is binder notation in Lean).
* In Proposition 8.1 the row factorization is of `fun (x, y) (u, v) => P i x y u v` and the column
  factorization of `fun (x, u) (y, v) => P i x y u v`, matching the cuts of §5. In
  Proposition 8.2 (the case `b = 0`, where both cuts separate `x` from `v`) both factorizations
  are of `P i` itself, as the statement says.
* The integrality of `φ, φ'` in `FactorsThrough` is as in the paper; the rank argument works over
  `ℚ`, and so would equally apply to rational `φ, φ'`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

/-- `Γ` *factors through `c` bits* (`separating-ntime-from-space.tex`, §8): `Γ z z' = ∑_θ φ z θ * φ'
z' θ` over
`θ ∈ {0,1}^c`. -/
def FactorsThrough {α β : Type*} (Γ : α → β → ℤ) (c : ℕ) : Prop :=
  ∃ φ : α → (Fin c → Bool) → ℤ, ∃ φ' : β → (Fin c → Bool) → ℤ,
    ∀ z z', Γ z z' = ∑ θ, φ z θ * φ' z' θ

/-- `Γ` *factors over OR and AND through `c` bits* (`separating-ntime-from-space.tex`, §8):
`Γ z z' = ⋁_θ (φ z θ ∧ φ' z' θ)` over `θ ∈ {0,1}^c`. -/
def FactorsThroughOr {α β : Type*} (Γ : α → β → Bool) (c : ℕ) : Prop :=
  ∃ φ : α → (Fin c → Bool) → Bool, ∃ φ' : β → (Fin c → Bool) → Bool,
    ∀ z z', Γ z z' = true ↔ ∃ θ, φ z θ = true ∧ φ' z' θ = true

/-! ### The Boolean bound -/

/-- The fooling-set bound: if `Γ` factors over OR and AND through `c` bits, and `S` indexes ones
`(f s, g s)` of `Γ` such that `Γ (f s) (g t)` forces `s = t`, then `S` has at most `2^c`
elements. Each one lies in a rectangle `{φ · θ} × {φ' · θ}` of ones, and no rectangle contains
two of them. -/
theorem card_le_of_factorsThroughOr {α β γ : Type*} {Γ : α → β → Bool} {c : ℕ}
    (hΓ : FactorsThroughOr Γ c) (S : Finset γ) (f : γ → α) (g : γ → β)
    (hone : ∀ s ∈ S, Γ (f s) (g s) = true)
    (hfool : ∀ s ∈ S, ∀ t ∈ S, Γ (f s) (g t) = true → s = t) :
    S.card ≤ 2 ^ c := by
  classical
  obtain ⟨φ, φ', h⟩ := hΓ
  have hθ : ∀ s ∈ S, ∃ θ, φ (f s) θ = true ∧ φ' (g s) θ = true :=
    fun s hs => (h _ _).1 (hone s hs)
  choose! θ hθ using hθ
  calc S.card ≤ (univ : Finset (Fin c → Bool)).card := by
        refine card_le_card_of_injOn θ (fun s _ => mem_coe.2 (mem_univ _)) ?_
        intro s hs t ht hst
        exact hfool s hs t ht ((h _ _).2 ⟨θ s, (hθ s hs).1, hst ▸ (hθ t ht).2⟩)
    _ = 2 ^ c := by simp

/-- The intermediate statement of the proof of Proposition 8.1: one piece `P i` has at least
`2^(2λ)/N` ones, and so `2^(2λ) ≤ N · 2^(r i)` and `2^(2λ) ≤ N · 2^(c i)`. -/
theorem prop_boolean_each {lam N : ℕ}
    (P : Fin N → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) →
      Bool)
    (hP : ∀ x y u v, (∃ i, P i x y u v = true) ↔ (x = v ∧ y = u))
    (r c : Fin N → ℕ)
    (hr : ∀ i, FactorsThroughOr
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 p.2 q.1 q.2) (r i))
    (hc : ∀ i, FactorsThroughOr
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 q.1 p.2 q.2) (c i)) :
    ∃ i, 2 ^ (2 * lam) ≤ N * 2 ^ r i ∧ 2 ^ (2 * lam) ≤ N * 2 ^ c i := by
  classical
  -- the ones of `P i`, indexed by `(x, y)`; every one has `v = x` and `u = y`
  let ones : Fin N → Finset ((Fin lam → Bool) × (Fin lam → Bool)) := fun i =>
    univ.filter fun p => P i p.1 p.2 p.2 p.1 = true
  obtain ⟨i₀, -⟩ := (hP (fun _ => false) (fun _ => false) (fun _ => false)
    (fun _ => false)).2 ⟨rfl, rfl⟩
  have hne : (univ : Finset (Fin N)).Nonempty := ⟨i₀, mem_univ _⟩
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun i => (ones i).card) hne
  refine ⟨i, ?_⟩
  -- pigeonhole: the ones of the pieces cover the `2^(2λ)` points with `x = v`, `y = u`
  have hcover : 2 ^ (2 * lam) ≤ N * (ones i).card := by
    have h1 : (univ : Finset ((Fin lam → Bool) × (Fin lam → Bool))) ⊆ univ.biUnion ones := by
      intro p _
      obtain ⟨j, hj⟩ := (hP p.1 p.2 p.2 p.1).2 ⟨rfl, rfl⟩
      exact mem_biUnion.2 ⟨j, mem_univ _, mem_filter.2 ⟨mem_univ _, hj⟩⟩
    have h2 := (card_le_card h1).trans card_biUnion_le
    have h3 : ∑ j, (ones j).card ≤ (univ : Finset (Fin N)).card • (ones i).card :=
      sum_le_card_nsmul _ _ _ fun j _ => hi j (mem_univ _)
    have hcard : (univ : Finset ((Fin lam → Bool) × (Fin lam → Bool))).card = 2 ^ (2 * lam) := by
      simp [two_mul, pow_add]
    rw [card_univ, Fintype.card_fin, smul_eq_mul] at h3
    rw [← hcard]
    exact h2.trans h3
  have hmem : ∀ s ∈ ones i, P i s.1 s.2 s.2 s.1 = true := fun s hs => (mem_filter.1 hs).2
  -- each factorization covers the ones by `2^bits` rectangles, each containing at most one
  have hrow : (ones i).card ≤ 2 ^ r i := by
    refine card_le_of_factorsThroughOr (hr i) (ones i) id (fun p => (p.2, p.1)) hmem ?_
    intro s _ t _ hst
    obtain ⟨h1, h2⟩ := (hP _ _ _ _).1 ⟨i, hst⟩
    exact Prod.ext h1 h2
  have hcol : (ones i).card ≤ 2 ^ c i := by
    refine card_le_of_factorsThroughOr (hc i) (ones i) id (fun p => (p.2, p.1)) hmem ?_
    intro s _ t _ hst
    obtain ⟨h1, h2⟩ := (hP _ _ _ _).1 ⟨i, hst⟩
    exact Prod.ext h1 h2.symm
  exact ⟨hcover.trans (Nat.mul_le_mul_left _ hrow), hcover.trans (Nat.mul_le_mul_left _ hcol)⟩

/-- **Proposition 8.1** (`prop:boolean`). If Boolean pieces `P i` of the crossing
`[x = v][y = u]` of strings of `λ` bits satisfy `⋁_i P i = [x = v][y = u]`, and each `P i`
factors over OR and AND through `r i` bits across the row cut (`(x, y)` against `(u, v)`) and
through `c i` bits across the column cut (`(x, u)` against `(y, v)`), then for some `i`,
`2^(4λ) ≤ N² · 2^(r i + c i)`, that is, `r i + c i ≥ 4λ − 2 log N`. -/
theorem prop_boolean {lam N : ℕ}
    (P : Fin N → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) → (Fin lam → Bool) →
      Bool)
    (hP : ∀ x y u v, (∃ i, P i x y u v = true) ↔ (x = v ∧ y = u))
    (r c : Fin N → ℕ)
    (hr : ∀ i, FactorsThroughOr
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 p.2 q.1 q.2) (r i))
    (hc : ∀ i, FactorsThroughOr
      (fun p q : (Fin lam → Bool) × (Fin lam → Bool) => P i p.1 q.1 p.2 q.2) (c i)) :
    ∃ i, 2 ^ (4 * lam) ≤ N ^ 2 * 2 ^ (r i + c i) := by
  obtain ⟨i, h1, h2⟩ := prop_boolean_each P hP r c hr hc
  refine ⟨i, ?_⟩
  calc 2 ^ (4 * lam) = 2 ^ (2 * lam) * 2 ^ (2 * lam) := by rw [← pow_add]; ring_nf
    _ ≤ (N * 2 ^ r i) * (N * 2 ^ c i) := Nat.mul_le_mul h1 h2
    _ = N ^ 2 * 2 ^ (r i + c i) := by ring

/-! ### The integer bound -/

/-- Subadditivity of the rank of matrices over a field. -/
theorem rank_add_le {m n K : Type*} [Fintype m] [Fintype n] [Field K] (A B : Matrix m n K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Subadditivity of the rank over a finite sum. -/
theorem rank_sum_le {ι m n K : Type*} [Fintype m] [Fintype n] [Field K] (s : Finset ι)
    (M : ι → Matrix m n K) : (∑ i ∈ s, M i).rank ≤ ∑ i ∈ s, (M i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, sum_insert hj]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- A function that factors through `c` bits has rank at most `2^c` over `ℚ`: its matrix is the
product of a matrix with `2^c` columns and one with `2^c` rows. -/
theorem rank_le_of_factorsThrough {α β : Type*} [Fintype α] [Fintype β] {Γ : α → β → ℤ} {c : ℕ}
    (hΓ : FactorsThrough Γ c) : (Matrix.of fun z z' => (Γ z z' : ℚ)).rank ≤ 2 ^ c := by
  obtain ⟨φ, φ', h⟩ := hΓ
  have hmul : (Matrix.of fun z z' => (Γ z z' : ℚ)) =
      Matrix.of (fun z θ => (φ z θ : ℚ)) * Matrix.of (fun θ z' => (φ' z' θ : ℚ)) := by
    ext z z'
    simp [Matrix.mul_apply, h]
  rw [hmul]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans ?_)
  simp

/-- **Proposition 8.2** (`prop:barrier`). If integer pieces `P i` of the equality matrix on
strings of `a` bits satisfy `∑_i P i x v = [x = v]`, and each `P i` factors through `r i` bits and
through `c i` bits, then for some `i`, `2^a ≤ N · 2^min(r i, c i)`, that is,
`min(r i, c i) ≥ a − log N`. -/
theorem prop_barrier {a N : ℕ} (P : Fin N → (Fin a → Bool) → (Fin a → Bool) → ℤ)
    (hP : ∀ x v, ∑ i, P i x v = if x = v then 1 else 0)
    (r c : Fin N → ℕ) (hr : ∀ i, FactorsThrough (P i) (r i))
    (hc : ∀ i, FactorsThrough (P i) (c i)) :
    ∃ i, 2 ^ a ≤ N * 2 ^ min (r i) (c i) := by
  classical
  let M : Fin N → Matrix (Fin a → Bool) (Fin a → Bool) ℚ := fun i =>
    Matrix.of fun x v => (P i x v : ℚ)
  have hsum : ∑ i, M i = 1 := by
    ext x v
    have := congrArg (fun z : ℤ => (z : ℚ)) (hP x v)
    simp only [Int.cast_sum] at this
    rw [Matrix.sum_apply, Matrix.one_apply]
    simp only [M, Matrix.of_apply]
    rw [this]
    split_ifs <;> simp
  obtain ⟨i₀, -, -⟩ : ∃ i ∈ (univ : Finset (Fin N)), P i (fun _ => false) (fun _ => false) ≠ 0 :=
    exists_ne_zero_of_sum_ne_zero (by rw [hP]; simp)
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun i => (M i).rank) ⟨i₀, mem_univ _⟩
  refine ⟨i, ?_⟩
  have hrank : 2 ^ a ≤ N * (M i).rank := by
    have h1 : (1 : Matrix (Fin a → Bool) (Fin a → Bool) ℚ).rank = 2 ^ a := by simp
    have h2 := rank_sum_le univ M
    have h3 : ∑ j, (M j).rank ≤ (univ : Finset (Fin N)).card • (M i).rank :=
      sum_le_card_nsmul _ _ _ fun j _ => hi j (mem_univ _)
    rw [card_univ, Fintype.card_fin, smul_eq_mul] at h3
    rw [hsum, h1] at h2
    exact h2.trans h3
  have hmin : (M i).rank ≤ 2 ^ min (r i) (c i) := by
    rcases le_total (r i) (c i) with h | h
    · rw [min_eq_left h]; exact rank_le_of_factorsThrough (hr i)
    · rw [min_eq_right h]; exact rank_le_of_factorsThrough (hc i)
  exact hrank.trans (Nat.mul_le_mul_left _ hmin)

end Cslib.Complexity.NtimeDspace.Cube
