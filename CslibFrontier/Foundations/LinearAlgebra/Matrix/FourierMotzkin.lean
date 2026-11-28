/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/FourierMotzkin.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fourier–Motzkin elimination

Fourier–Motzkin elimination removes one variable from a finite system of linear inequalities over
a linearly ordered field. A variable occurring with coefficients `a i` is eliminated by keeping
the rows with `a i = 0` and adding, for every pair of rows `p, q` with `a p > 0 > a q`, the
nonnegative combination `-a q • row p + a p • row q`, in which the variable cancels. The new
system is solvable exactly when the old one is solvable for some value of the eliminated variable.
Iterating this step eliminates any finite block of variables.

The combinations are recorded as an explicit matrix with nonnegative entries, so that every
consequence of the projected system is a nonnegative combination of the original rows. This is
what the algebraic proofs of Farkas' lemma and linear-programming duality in
`CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas` and
`CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming` use. Unlike Mathlib's
topological Farkas lemma `ProperCone.hyperplane_separation`, everything here works over any
linearly ordered field, in particular over `ℚ`.

## Main definitions

* `Matrix.FourierMotzkin.Row`: the index type of the rows produced by one elimination step.
* `Matrix.FourierMotzkin.combination`: the nonnegative combination matrix of one elimination step.

## Main results

* `Matrix.FourierMotzkin.exists_smul_add_le_iff`: one elimination step,
  `(∃ t, t • a + v ≤ b) ↔ combination a *ᵥ v ≤ combination a *ᵥ b`.
* `Matrix.FourierMotzkin.exists_projection`: eliminating a finite block of variables `y` from
  `A *ᵥ y + B *ᵥ z ≤ b` gives a system `(T * B) *ᵥ z ≤ T *ᵥ b`, where `T` is entrywise
  nonnegative and `T * A = 0`.

## References

* [MatousekGartner2007], Section 6.7
* [Schrijver1986], Section 12.2
* [Ziegler1995], Section 1.2
-/

public section

open Matrix

namespace Matrix.FourierMotzkin

variable {K : Type*} [Field K] [LinearOrder K]
variable {ι : Type*} [DecidableEq ι]

/-- The rows produced by eliminating a variable whose coefficient column is `a`: the rows `i`
with `a i = 0`, and the pairs `(p, q)` with `a p > 0 > a q`. -/
abbrev Row (a : ι → K) : Type _ :=
  {i // a i = 0} ⊕ ({p // 0 < a p} × {q // a q < 0})

/-- The combination matrix of one Fourier–Motzkin step for the column `a`. A row `i` with
`a i = 0` is kept, and a pair `(p, q)` with `a p > 0 > a q` gives `-a q • row p + a p • row q`. -/
def combination (a : ι → K) : Matrix (Row a) ι K :=
  Matrix.of <| Sum.elim (fun i => Pi.single (i : ι) 1)
    fun (p, q) => Pi.single (p : ι) (-a q) + Pi.single (q : ι) (a p)

/-- A row with zero coefficient is kept unchanged. -/
@[simp]
theorem combination_inl (a : ι → K) (i : {i // a i = 0}) :
    combination a (.inl i) = Pi.single (i : ι) 1 := by
  rw [combination]
  rfl

/-- A pair `(p, q)` combines rows `p` and `q` with weights `-a q` and `a p`. -/
@[simp]
theorem combination_inr (a : ι → K) (p : {p // 0 < a p}) (q : {q // a q < 0}) :
    combination a (.inr (p, q)) = Pi.single (p : ι) (-a q) + Pi.single (q : ι) (a p) := by
  rw [combination]
  rfl

/-- The entries of a Fourier–Motzkin combination matrix are nonnegative. -/
theorem combination_nonneg [IsStrictOrderedRing K] (a : ι → K) (r : Row a) (i : ι) :
    0 ≤ combination a r i := by
  rcases r with i' | ⟨p, q⟩
  · rw [combination_inl, Pi.single_apply]
    split_ifs <;> norm_num
  · rw [combination_inr, Pi.add_apply, Pi.single_apply, Pi.single_apply]
    split_ifs <;> linarith [p.property, q.property]

variable [Fintype ι]

/-- The kept row `i` of `combination a *ᵥ v` is `v i`. -/
theorem combination_mulVec_inl (a v : ι → K) (i : {i // a i = 0}) :
    (combination a *ᵥ v) (.inl i) = v i := by
  change combination a (.inl i) ⬝ᵥ v = _
  rw [combination_inl, single_dotProduct, one_mul]

/-- The combined row `(p, q)` of `combination a *ᵥ v` is `-a q * v p + a p * v q`. -/
theorem combination_mulVec_inr (a v : ι → K) (p : {p // 0 < a p}) (q : {q // a q < 0}) :
    (combination a *ᵥ v) (.inr (p, q)) = -a q * v p + a p * v q := by
  change combination a (.inr (p, q)) ⬝ᵥ v = _
  rw [combination_inr, add_dotProduct, single_dotProduct, single_dotProduct]

/-- The eliminated variable cancels in every combined row. -/
theorem combination_mulVec_self (a : ι → K) : combination a *ᵥ a = 0 := by
  funext r
  rcases r with i | ⟨p, q⟩
  · exact (combination_mulVec_inl a a i).trans i.property
  · simp only [combination_mulVec_inr, Pi.zero_apply]
    ring

variable [IsStrictOrderedRing K]

omit [DecidableEq ι] [Fintype ι] [IsStrictOrderedRing K] in
/-- Between two finite families, with every lower value below every upper value, lies a point. -/
private theorem exists_between_of_le {α β : Type*} [Finite α] [Finite β] (f : α → K) (g : β → K)
    (h : ∀ a b, f a ≤ g b) : ∃ t, (∀ a, f a ≤ t) ∧ ∀ b, t ≤ g b := by
  rcases isEmpty_or_nonempty α with _ | _
  · rcases isEmpty_or_nonempty β with _ | _
    · exact ⟨0, isEmptyElim, isEmptyElim⟩
    · obtain ⟨b₀, hb₀⟩ := Finite.exists_min g
      exact ⟨g b₀, isEmptyElim, hb₀⟩
  · obtain ⟨a₀, ha₀⟩ := Finite.exists_max f
    exact ⟨f a₀, ha₀, h a₀⟩

/-- **One step of Fourier–Motzkin elimination**: the system `t • a + v ≤ b` is solvable in `t`
exactly when the combined system without `t` holds. -/
theorem exists_smul_add_le_iff (a v b : ι → K) :
    (∃ t : K, t • a + v ≤ b) ↔ combination a *ᵥ v ≤ combination a *ᵥ b := by
  constructor
  · rintro ⟨t, ht⟩ r
    have hle : (combination a *ᵥ (t • a + v)) r ≤ (combination a *ᵥ b) r :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ht i) (combination_nonneg a r i)
    rwa [mulVec_add, mulVec_smul, combination_mulVec_self, smul_zero, zero_add] at hle
  · intro h
    obtain ⟨t, hlo, hhi⟩ := exists_between_of_le (fun q : {q // a q < 0} => (b q - v q) / a q)
      (fun p : {p // 0 < a p} => (b p - v p) / a p) fun q p => by
        have := h (.inr (p, q))
        rw [combination_mulVec_inr, combination_mulVec_inr] at this
        rw [div_le_iff_of_neg q.property, div_mul_eq_mul_div, div_le_iff₀ p.property]
        nlinarith [p.property, q.property]
    refine ⟨t, fun i => ?_⟩
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases lt_trichotomy (a i) 0 with hi | hi | hi
    · linarith [(div_le_iff_of_neg hi).1 (hlo ⟨i, hi⟩)]
    · simpa [hi, combination_mulVec_inl] using h (.inl ⟨i, hi⟩)
    · linarith [(le_div_iff₀ hi).1 (hhi ⟨i, hi⟩)]

omit [LinearOrder K] [DecidableEq ι] [Fintype ι] [IsStrictOrderedRing K] in
/-- Split off the `none` column of a matrix indexed by `Option α`. -/
private theorem mulVec_option {α : Type*} [Fintype α] (A : Matrix ι (Option α) K)
    (y : Option α → K) :
    A *ᵥ y = y none • (fun i => A i none) + A.submatrix id some *ᵥ (y ∘ some) := by
  funext i
  simp only [mulVec, dotProduct, Fintype.sum_option, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    submatrix_apply, id, Function.comp_apply]
  ring

universe u v w

/-- The block of variables `κ` can be eliminated from every finite system over `K` with `μ`
further variables whose rows lie in universe `u`: for each `A *ᵥ y + B *ᵥ z ≤ b` there is an
entrywise nonnegative `T` with `T * A = 0` whose projected system `(T * B) *ᵥ z ≤ T *ᵥ b` is
solvable exactly when the original one is solvable for some `y`. This is the induction motive of
`exists_projection`. -/
private def Eliminable (K : Type*) [Field K] [LinearOrder K] (μ : Type w) [Fintype μ]
    (κ : Type v) [Fintype κ] : Prop :=
  ∀ (ι : Type u) [Fintype ι] (A : Matrix ι κ K) (B : Matrix ι μ K) (b : ι → K),
    ∃ (ρ : Type u) (_ : Fintype ρ) (T : Matrix ρ ι K), (∀ r i, 0 ≤ T r i) ∧ T * A = 0 ∧
      ∀ z, (∃ y, A *ᵥ y + B *ᵥ z ≤ b) ↔ (T * B) *ᵥ z ≤ T *ᵥ b

variable {μ : Type w} [Fintype μ]

omit [IsStrictOrderedRing K] in
/-- Eliminability is invariant under renaming the eliminated variables. -/
private theorem Eliminable.of_equiv {α β : Type v} [Fintype α] [Fintype β] (e : α ≃ β)
    (h : Eliminable.{u} K μ α) : Eliminable.{u} K μ β := by
  intro ι _ A B b
  obtain ⟨ρ, _, T, hT, hTA, hiff⟩ := h ι (A.submatrix id e) B b
  refine ⟨ρ, inferInstance, T, hT, Matrix.ext fun r j => ?_, fun z => Iff.trans ⟨?_, ?_⟩ (hiff z)⟩
  · simpa [Matrix.mul_apply] using congr_fun (congr_fun hTA r) (e.symm j)
  · rintro ⟨y, hy⟩
    exact ⟨y ∘ e, by simpa [submatrix_mulVec_equiv, Function.comp_assoc] using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y ∘ e.symm, by simpa [submatrix_mulVec_equiv] using hy⟩

/-- With no variables to eliminate, the system itself (`T = 1`) is its own projection. -/
private theorem eliminable_pEmpty : Eliminable.{u} K μ PEmpty.{v + 1} := by
  classical
  intro ι _ A B b
  have h0 (y : PEmpty.{v + 1} → K) : A *ᵥ y = 0 := funext fun _ => by simp [mulVec, dotProduct]
  have : Nonempty (PEmpty.{v + 1} → K) := ⟨PEmpty.elim⟩
  refine ⟨ι, inferInstance, 1, fun r i => ?_, Matrix.ext fun _ j => j.elim, fun z => ?_⟩
  · rw [Matrix.one_apply]
    split_ifs <;> norm_num
  · simp [h0]

/-- **One more variable.** If `α` can be eliminated, so can `Option α`: one Fourier–Motzkin step
(`exists_smul_add_le_iff`) removes the variable `none`, and the remaining variables are then
eliminated from the combined system `combination a * A₀ *ᵥ y + combination a * B *ᵥ z ≤
combination a *ᵥ b`. -/
private theorem Eliminable.option {α : Type v} [Fintype α]
    (h : Eliminable.{u} K μ α) : Eliminable.{u} K μ (Option α) := by
  classical
  intro ι _ A B b
  set a : ι → K := fun i => A i none
  set A₀ : Matrix ι α K := A.submatrix id some
  obtain ⟨ρ, _, T, hT, hTA, hiff⟩ :=
    h (Row a) (combination a * A₀) (combination a * B) (combination a *ᵥ b)
  refine ⟨ρ, inferInstance, T * combination a,
    fun r i => Finset.sum_nonneg fun s _ => mul_nonneg (hT r s) (combination_nonneg a s i),
    Matrix.ext fun r j => ?_, fun z => ?_⟩
  · cases j with
    | none =>
      change ((T * combination a) *ᵥ a) r = 0
      rw [← mulVec_mulVec, combination_mulVec_self, mulVec_zero, Pi.zero_apply]
    | some k =>
      change (T * combination a * A₀) r k = 0
      rw [Matrix.mul_assoc, hTA]
      rfl
  · rw [mulVec_mulVec] at hiff
    simp_rw [Matrix.mul_assoc, ← hiff z, ← mulVec_mulVec, ← mulVec_add, ← exists_smul_add_le_iff]
    exact ⟨fun ⟨y, hy⟩ => ⟨y ∘ some, y none, by rwa [← add_assoc, ← mulVec_option]⟩,
      fun ⟨y₀, t, ht⟩ => ⟨fun j => j.elim t y₀, by rwa [mulVec_option, add_assoc]⟩⟩

/-- **Fourier–Motzkin projection.** Eliminating a finite block of variables `y` from the system
`A *ᵥ y + B *ᵥ z ≤ b` yields a finite system `(T * B) *ᵥ z ≤ T *ᵥ b` in the remaining variables
`z`, whose rows are nonnegative combinations `T` of the original rows cancelling every column of
`A` [Schrijver1986, Section 12.2]. -/
theorem exists_projection {ι : Type u} [Fintype ι] {κ : Type v} [Fintype κ] {μ : Type w}
    [Fintype μ] (A : Matrix ι κ K) (B : Matrix ι μ K) (b : ι → K) :
    ∃ (ρ : Type u) (_ : Fintype ρ) (T : Matrix ρ ι K), (∀ r i, 0 ≤ T r i) ∧ T * A = 0 ∧
      ∀ z, (∃ y, A *ᵥ y + B *ᵥ z ≤ b) ↔ (T * B) *ᵥ z ≤ T *ᵥ b := by
  classical
  -- Induction on the eliminated block `κ`: empty, `Option`, and transport along equivalences.
  have : Eliminable.{u} K μ κ :=
    Fintype.induction_empty_option (P := fun κ _ => Eliminable.{u} K μ κ)
      (fun _ _ _ e h => by
        let : Fintype _ := Fintype.ofEquiv _ e.symm
        exact h.of_equiv e)
      eliminable_pEmpty (fun _ _ h => h.option) κ
  exact this ι A B b

end Matrix.FourierMotzkin
