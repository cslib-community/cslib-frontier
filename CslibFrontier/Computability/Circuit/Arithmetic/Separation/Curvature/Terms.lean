/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.GlueDeterminant

/-!
# States, and the terms of the expansion of `det [[X, AΛB], [B'ΛA', Y]]`

For the coefficients step of the proof of Proposition B.2 (prop:identity) of *VP ≠ VNP over every
field* [AnthropicVPVNP2026]. A state is a pair of finite sets of natural numbers, and its energy is
`∑ (2 i + 1)` over both sets (`energy`, `lowStates`). For a set `T` of inner indices, `termMat T`
is the matrix whose determinant is the term of `T` in the expansion of
`det [[X, AΛB], [B'ΛA', Y]]` (`Matrix.det_sumElim_smul_add`); it is a glued matrix
(`termMat_eq_glue`, `Matrix.glue`), so the term is a product. In the paper's letters `X = M₁`,
`Y = M₂`, `A = F`, `A' = F'`, `B = G`, `B' = −G'` and `Λ = D`.

## Main definitions

* `energy`, `lowStates`, `termMat`, `rowGroup`, `colGroup`.

## Main results

* `mem_lowStates`, `termMat_eq_glue`, `card_colGroup`, `card_rowGroup`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition B.2 of the paper; module `Nc.Cross.Near`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Matrix Finset

/-- The energy `∑ (2i+1)` of a set. -/
@[expose] def energy (S : Finset ℕ) : ℕ := ∑ i ∈ S, (2 * i + 1)

/-- The states of energy at most `E`. -/
@[expose] def lowStates (E : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((range E).powerset ×ˢ (range E).powerset).filter
    fun s => s.1.card = s.2.card ∧ energy s.1 + energy s.2 ≤ E

theorem lt_of_mem_of_energy_le {S : Finset ℕ} {E i : ℕ} (h : energy S ≤ E) (hi : i ∈ S) : i < E :=
    by
  have : 2 * i + 1 ≤ energy S := Finset.single_le_sum (f := fun i => 2 * i + 1)
      (fun _ _ => Nat.zero_le _) hi
  omega

theorem mem_lowStates {E : ℕ} {s : Finset ℕ × Finset ℕ} :
    s ∈ lowStates E ↔ s.1.card = s.2.card ∧ energy s.1 + energy s.2 ≤ E := by
  unfold lowStates
  rw [mem_filter, mem_product, mem_powerset, mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, h⟩⟩
  · exact mem_range.2 (lt_of_mem_of_energy_le (by omega) hi)
  · exact mem_range.2 (lt_of_mem_of_energy_le (by omega) hi)

section

variable {p q ρ : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] [Fintype ρ]
    [DecidableEq ρ]
variable {R : Type*} [CommRing R]

/-- The upper rows `(X, 0, A, 0)` and `(0, Y, 0, B')` of the big matrix. -/
@[expose] def topRows (X : Matrix p p R) (A : Matrix p ρ R) (Y : Matrix q q R) (B' : Matrix q ρ R) :
    p ⊕ q → (p ⊕ q) ⊕ (ρ ⊕ ρ) → R :=
  fun i => Sum.elim (fromBlocks X 0 0 Y i) (fromBlocks A 0 0 B' i)

/-- The parts `(0, −B, 0, 0)` and `(−A', 0, 0, 0)` of the lower rows, without the factors from `Λ`.
-/
@[expose] def lowRows (A' : Matrix ρ p R) (B : Matrix ρ q R) : ρ ⊕ ρ → (p ⊕ q) ⊕ (ρ ⊕ ρ) → R :=
  fun r => Sum.elim (-(fromBlocks 0 B A' 0 : Matrix (ρ ⊕ ρ) (p ⊕ q) R) r) 0

/-- The parts of the lower rows with the entry 1. -/
@[expose] def unitRows : ρ ⊕ ρ → (p ⊕ q) ⊕ (ρ ⊕ ρ) → R :=
  fun r => Sum.elim 0 ((1 : Matrix (ρ ⊕ ρ) (ρ ⊕ ρ) R) r)

/-- The matrix of the term of `T`: in the lower rows in `T` the first part is taken, in the others
the entry 1. -/
@[expose] def termMat (T : Finset (ρ ⊕ ρ)) (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    Matrix ((p ⊕ q) ⊕ (ρ ⊕ ρ)) ((p ⊕ q) ⊕ (ρ ⊕ ρ)) R :=
  of (Sum.elim (topRows X A Y B') (T.piecewise (lowRows A' B) unitRows))

/-- Columns of the first group. -/
@[expose] def colGroup : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop
  | Sum.inl (Sum.inl _) => True
  | Sum.inl (Sum.inr _) => False
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _) => False

/-- Rows of the first group. -/
@[expose] def rowGroup (T : Finset (ρ ⊕ ρ)) : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop
  | Sum.inl (Sum.inl _) => True
  | Sum.inl (Sum.inr _) => False
  | Sum.inr (Sum.inl r) => Sum.inl r ∉ T
  | Sum.inr (Sum.inr r) => Sum.inr r ∈ T

instance : DecidablePred (colGroup : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) := fun i =>
  match i with
  | Sum.inl (Sum.inl _) => isTrue trivial
  | Sum.inl (Sum.inr _) => isFalse id
  | Sum.inr (Sum.inl _) => isTrue trivial
  | Sum.inr (Sum.inr _) => isFalse id

instance (T : Finset (ρ ⊕ ρ)) : DecidablePred (rowGroup T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) := fun i =>
  match i with
  | Sum.inl (Sum.inl _) => isTrue trivial
  | Sum.inl (Sum.inr _) => isFalse id
  | Sum.inr (Sum.inl r) => inferInstanceAs (Decidable (Sum.inl r ∉ T))
  | Sum.inr (Sum.inr r) => inferInstanceAs (Decidable (Sum.inr r ∈ T))

omit [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] [Fintype ρ] in
/-- The matrix of a term falls into two blocks: one made of `X, A, A'` and one made of `Y, B, B'`.
-/
theorem termMat_eq_glue (T : Finset (ρ ⊕ ρ)) (X : Matrix p p R) (A : Matrix p ρ R)
    (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    termMat T X A A' Y B B' =
      Matrix.glue (rowGroup T) colGroup (termMat T X A A' 0 0 0) (termMat T 0 0 0 Y B B') := by
  ext i j
  rcases i with (i | i) | (i | i)
  · rcases j with (j | j) |
      (j | j) <;> simp [termMat, Matrix.glue_apply, rowGroup, colGroup, topRows]
  · rcases j with (j | j) |
      (j | j) <;> simp [termMat, Matrix.glue_apply, rowGroup, colGroup, topRows]
  · by_cases hi : Sum.inl i ∈ T <;> rcases j with (j | j) | (j | j) <;>
      simp [termMat, Matrix.glue_apply, rowGroup, colGroup, lowRows, unitRows, hi]
  · by_cases hi : Sum.inr i ∈ T <;> rcases j with (j | j) | (j | j) <;>
      simp [termMat, Matrix.glue_apply, rowGroup, colGroup, lowRows, unitRows, hi]

omit [DecidableEq p] [DecidableEq q] [DecidableEq ρ] in
theorem card_colGroup : (univ.filter (colGroup : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop)).card =
    Fintype.card p + Fintype.card ρ := by
  have h : univ.filter (colGroup : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) =
      disjSum (disjSum univ ∅) (disjSum univ ∅) := by
    ext i
    rcases i with (i | i) | (i | i) <;> simp [colGroup]
  rw [h]
  simp [Finset.card_univ]

omit [DecidableEq p] [DecidableEq q] in
theorem card_rowGroup (T : Finset (ρ ⊕ ρ)) :
    (univ.filter (rowGroup T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop)).card + T.toLeft.card =
    Fintype.card p + Fintype.card ρ + T.toRight.card := by
  have h : univ.filter (rowGroup T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) =
      disjSum (disjSum univ ∅) (disjSum T.toLeftᶜ T.toRight) := by
    ext i
    rcases i with (i | i) | (i | i) <;> simp [rowGroup]
  rw [h]
  have := Finset.card_add_card_compl T.toLeft
  simp only [card_disjSum, Finset.card_univ, card_empty]
  omega

end

end Cslib.Circuits.Arithmetic.Separation.Curvature
