/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Noise
public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.LpNorm
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tensorization of two-function hypercontractivity

For a correlation `ρ`, the expectation `𝔼_x f x · T_ρ g x` of `f` against the noise operator
applied to `g` is the expectation of `f x g y` over a `ρ`-correlated pair `(x, y)`. A
*two-function hypercontractive inequality* bounds it by `‖f‖_p ‖g‖_q`. Such an inequality
*tensorizes*: if it holds on a single bit, it holds on every cube (the **Two-Function
Hypercontractivity Induction Theorem**, `BitString.expect_mul_noiseOp_le_of_unit`)
[O'Donnell, Section 9.4][ODonnell2014].

The proof is *induction by restrictions*. On the cube over `ι ⊕ κ` the noise operator acts on the
two blocks of coordinates independently (`BitString.noiseOp_sumElim`), since a random mask on
`ι ⊕ κ` is a pair of independent masks (`BitString.bernoulliAverage_sumElim`). Fixing the bits in
`ι`, the inequality on `κ` bounds the inner expectation by the product of the norms of the
restrictions; these norms are functions of the bits in `ι`, to which the inequality on `ι`
applies, and their norms are the norms of `f` and `g` (`BitString.lpNorm_sumElim`). The noise
operator also commutes with renaming the coordinates (`BitString.noiseOp_comp_arrowCongr`), so
induction over `Fin n` reaches every finite coordinate type.

The same induction tensorizes *reverse* two-function inequalities
`‖f‖_p ‖g‖_q ≤ 𝔼_x f x · T_ρ g x` for nonnegative `f` and `g`
(`BitString.le_expect_mul_noiseOp_of_unit`), and for positive `f` and nonnegative `g`
(`BitString.le_expect_mul_noiseOp_of_unit_of_pos`), the form needed for a negative exponent `p`
[O'Donnell, Exercise 10.6(c)][ODonnell2014]; the norms of the restrictions are nonnegative, and
positive for positive functions, so the inequality on `ι` applies to them.

## Main results

* `Cslib.BitString.noiseOp_sumElim`: the noise operator on a disjoint union of coordinates is
  the composition of the noise operators on the two blocks.
* `Cslib.BitString.expect_mul_noiseOp_le_of_unit`: the Two-Function Hypercontractivity Induction
  Theorem.
* `Cslib.BitString.le_expect_mul_noiseOp_of_unit`,
  `Cslib.BitString.le_expect_mul_noiseOp_of_unit_of_pos`: the same induction for reverse
  two-function inequalities between nonnegative functions, and between a positive and a
  nonnegative function.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### The noise operator on split coordinates -/

/-- **The noise operator on a disjoint union of coordinates** applies the noise operator on the
bits in `κ` and then the noise operator on the bits in `ι`. -/
theorem noiseOp_sumElim (ρ : ℝ) (g : (ι ⊕ κ → Bool) → ℝ) (x₁ : ι → Bool) (x₂ : κ → Bool) :
    noiseOp ρ g (Sum.elim x₁ x₂) =
      noiseOp ρ (fun y₁ => noiseOp ρ (fun y₂ => g (Sum.elim y₁ y₂)) x₂) x₁ := by
  have h (P₁ : ι → Bool) (P₂ : κ → Bool) :
      Sum.elim x₁ x₂ + Sum.elim P₁ P₂ = Sum.elim (x₁ + P₁) (x₂ + P₂) := by
    funext i
    cases i <;> rfl
  simp only [noiseOp, bernoulliAverage_sumElim, h]

/-! ### Tensorization -/

/-- On the cube over `ι ⊕ κ`, the expectation of `f` against `T_ρ g` averages, over the bits
`x₁` in `ι` and a mask `P` on `ι`, the expectation over the bits in `κ` of the restriction of `f`
to `x₁` against `T_ρ` of the restriction of `g` to `x₁ + P`. -/
private theorem expect_mul_noiseOp_sumElim (ρ : ℝ) (f g : (ι ⊕ κ → Bool) → ℝ) :
    𝔼 x, f x * noiseOp ρ g x =
      𝔼 x₁, bernoulliAverage ((1 - ρ) / 2) fun P => 𝔼 x₂, f (Sum.elim x₁ x₂) *
        noiseOp ρ (fun y₂ => g (Sum.elim (x₁ + P) y₂)) x₂ := by
  rw [Fintype.expect_sumElim]
  simp only [noiseOp_sumElim]
  refine expect_congr rfl fun x₁ _ => ?_
  rw [bernoulliAverage_expect_comm]
  refine expect_congr rfl fun x₂ _ => ?_
  rw [noiseOp, ← bernoulliAverage_const_mul]

/-- The comparison `Φ (𝔼_x f x · T_ρ g x) (‖f‖_p ‖g‖_q)` for all functions `f` and `g` on the
cube over `ι` with values in `S` and `T`: a forward inequality is `Φ = (· ≤ ·)` with
`S = T = univ`, a reverse one `Φ = (· ≥ ·)`. -/
private def TwoFunction (Φ : ℝ → ℝ → Prop) (S T : Set ℝ) (p q ρ : ℝ) (ι : Type*) [Fintype ι]
    [DecidableEq ι] : Prop :=
  ∀ f g : (ι → Bool) → ℝ, (∀ x, f x ∈ S) → (∀ x, g x ∈ T) →
    Φ (𝔼 x, f x * noiseOp ρ g x) (lpNorm p f * lpNorm q g)

/-- A two-function comparison transfers along a renaming of the coordinates. -/
private theorem TwoFunction.of_equiv {Φ : ℝ → ℝ → Prop} {S T : Set ℝ} {p q ρ : ℝ} (e : ι ≃ κ)
    (h : TwoFunction Φ S T p q ρ ι) : TwoFunction Φ S T p q ρ κ := fun f g hf hg => by
  have h' := h (fun x => f fun j => x (e.symm j)) (fun x => g fun j => x (e.symm j))
    (fun _ => hf _) fun _ => hg _
  simp only [noiseOp_comp_arrowCongr, lpNorm_comp_arrowCongr] at h'
  rwa [Fintype.expect_comp_arrowCongr e fun y => f y * noiseOp ρ g y] at h'

/-- **Tensorization by induction over `Fin n`**: a two-function comparison that holds on the cube
over no coordinates, and passes from the cube over `Fin n` to the cube over `Fin n ⊕ Unit`, holds
on every cube. -/
private theorem TwoFunction.of_fin {Φ : ℝ → ℝ → Prop} {S T : Set ℝ} {p q ρ : ℝ}
    (h₀ : TwoFunction Φ S T p q ρ (Fin 0))
    (hstep : ∀ n, TwoFunction Φ S T p q ρ (Fin n) → TwoFunction Φ S T p q ρ (Fin n ⊕ Unit)) :
    TwoFunction Φ S T p q ρ ι := by
  have hfin (n : ℕ) : TwoFunction Φ S T p q ρ (Fin n) := by
    induction n with
    | zero => exact h₀
    | succ n ih =>
      exact (hstep n ih).of_equiv
        ((Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv)
  exact (hfin _).of_equiv (Fintype.equivFin ι).symm

/-- A two-function inequality holds on the cube over no coordinates. -/
private theorem expect_mul_noiseOp_le_of_isEmpty [IsEmpty ι] {p q ρ : ℝ} (hp : p ≠ 0)
    (hq : q ≠ 0) (f g : (ι → Bool) → ℝ) :
    𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g := by
  let x₀ : ι → Bool := isEmptyElim
  have h : (fun x => f x * noiseOp ρ g x) = fun _ => f x₀ * g x₀ :=
    funext fun x => by rw [Subsingleton.elim x x₀, noiseOp_of_isEmpty]
  rw [h, Fintype.expect_const, lpNorm_of_isEmpty hp f x₀, lpNorm_of_isEmpty hq g x₀, ← abs_mul]
  exact le_abs_self _

/-- **The induction step**: two-function inequalities on the cubes over `ι` and over `κ` give
the inequality on the cube over `ι ⊕ κ`. -/
private theorem expect_mul_noiseOp_le_sum {p q ρ : ℝ} (hρ : -1 ≤ ρ) (hρ' : ρ ≤ 1)
    (hι : ∀ f g : (ι → Bool) → ℝ, 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g)
    (hκ : ∀ f g : (κ → Bool) → ℝ, 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g)
    (f g : (ι ⊕ κ → Bool) → ℝ) : 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g := by
  -- the norms of the restrictions, as functions of the bits in `ι`
  let F : (ι → Bool) → ℝ := fun x₁ => lpNorm p fun x₂ => f (Sum.elim x₁ x₂)
  let G : (ι → Bool) → ℝ := fun y₁ => lpNorm q fun y₂ => g (Sum.elim y₁ y₂)
  have hr : 0 ≤ (1 - ρ) / 2 := by linarith
  have hr' : (1 - ρ) / 2 ≤ 1 := by linarith
  calc 𝔼 x, f x * noiseOp ρ g x
      = 𝔼 x₁, bernoulliAverage ((1 - ρ) / 2) fun P => 𝔼 x₂, f (Sum.elim x₁ x₂) *
          noiseOp ρ (fun y₂ => g (Sum.elim (x₁ + P) y₂)) x₂ := expect_mul_noiseOp_sumElim ρ f g
    _ ≤ 𝔼 x₁, bernoulliAverage ((1 - ρ) / 2) fun P => F x₁ * G (x₁ + P) :=
        expect_le_expect fun x₁ _ => bernoulliAverage_mono hr hr' fun P => hκ _ _
    _ = 𝔼 x₁, F x₁ * noiseOp ρ G x₁ := by
        simp only [noiseOp, bernoulliAverage_const_mul]
    _ ≤ lpNorm p F * lpNorm q G := hι F G
    _ = lpNorm p f * lpNorm q g := by
        rw [lpNorm_sumElim p f, lpNorm_sumElim q g]

/-- **The Two-Function Hypercontractivity Induction Theorem**: if the two-function inequality
`𝔼_x f x · T_ρ g x ≤ ‖f‖_p ‖g‖_q` holds for all functions of a single bit, then it holds for all
functions on every cube. Here `𝔼_x f x · T_ρ g x` is the expectation of `f x g y` over a
`ρ`-correlated pair `(x, y)` [O'Donnell, Section 9.4][ODonnell2014]. -/
theorem expect_mul_noiseOp_le_of_unit {p q ρ : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ 1)
    (h : ∀ f g : (Unit → Bool) → ℝ, 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g)
    (f g : (ι → Bool) → ℝ) : 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g :=
  TwoFunction.of_fin (Φ := (· ≤ ·)) (S := .univ) (T := .univ)
    (fun f g _ _ => expect_mul_noiseOp_le_of_isEmpty hp hq f g)
    (fun _ ih f g _ _ => expect_mul_noiseOp_le_sum (by linarith) hρ'
      (fun f g => ih f g (fun _ => trivial) fun _ => trivial) h f g)
    f g (fun _ => trivial) fun _ => trivial

/-! ### Tensorization of reverse inequalities -/

/-! Reverse inequalities are tensorized for functions with values in `S` and `T`, each the set of
nonnegative or of positive reals: negative exponents need positive functions. -/

/-- Values in the nonnegative or the positive reals are nonnegative. -/
private theorem nonneg_of_mem {S : Set ℝ} (hS : S = Set.Ici 0 ∨ S = Set.Ioi 0) {y : ℝ}
    (hy : y ∈ S) : 0 ≤ y := by
  rcases hS with rfl | rfl
  exacts [hy, le_of_lt hy]

/-- The norm of a function with values in the nonnegative (positive) reals is nonnegative
(positive). -/
private theorem lpNorm_mem {S : Set ℝ} (hS : S = Set.Ici 0 ∨ S = Set.Ioi 0) (p : ℝ)
    {f : (κ → Bool) → ℝ} (hf : ∀ x, f x ∈ S) : lpNorm p f ∈ S := by
  rcases hS with rfl | rfl
  exacts [lpNorm_nonneg p f, lpNorm_pos p hf]

/-- A reverse two-function inequality holds for nonnegative functions on the cube over no
coordinates, in particular for functions with values in `S` and `T`. -/
private theorem le_expect_mul_noiseOp_of_isEmpty [IsEmpty ι] {S T : Set ℝ}
    (hS : S = Set.Ici 0 ∨ S = Set.Ioi 0) (hT : T = Set.Ici 0 ∨ T = Set.Ioi 0) {p q ρ : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) {f g : (ι → Bool) → ℝ} (hf : ∀ x, f x ∈ S) (hg : ∀ x, g x ∈ T) :
    lpNorm p f * lpNorm q g ≤ 𝔼 x, f x * noiseOp ρ g x := by
  let x₀ : ι → Bool := isEmptyElim
  have h : (fun x => f x * noiseOp ρ g x) = fun _ => f x₀ * g x₀ :=
    funext fun x => by rw [Subsingleton.elim x x₀, noiseOp_of_isEmpty]
  rw [h, Fintype.expect_const, lpNorm_of_isEmpty hp f x₀, lpNorm_of_isEmpty hq g x₀,
    abs_of_nonneg (nonneg_of_mem hS (hf x₀)), abs_of_nonneg (nonneg_of_mem hT (hg x₀))]

/-- **The induction step for reverse inequalities**: reverse two-function inequalities on the
cubes over `ι` and over `κ` give the inequality on the cube over `ι ⊕ κ`. -/
private theorem le_expect_mul_noiseOp_sum {S T : Set ℝ} (hS : S = Set.Ici 0 ∨ S = Set.Ioi 0)
    (hT : T = Set.Ici 0 ∨ T = Set.Ioi 0) {p q ρ : ℝ} (hρ : -1 ≤ ρ) (hρ' : ρ ≤ 1)
    (hι : ∀ f g : (ι → Bool) → ℝ, (∀ x, f x ∈ S) → (∀ x, g x ∈ T) →
      lpNorm p f * lpNorm q g ≤ 𝔼 x, f x * noiseOp ρ g x)
    (hκ : ∀ f g : (κ → Bool) → ℝ, (∀ x, f x ∈ S) → (∀ x, g x ∈ T) →
      lpNorm p f * lpNorm q g ≤ 𝔼 x, f x * noiseOp ρ g x)
    {f g : (ι ⊕ κ → Bool) → ℝ} (hf : ∀ x, f x ∈ S) (hg : ∀ x, g x ∈ T) :
    lpNorm p f * lpNorm q g ≤ 𝔼 x, f x * noiseOp ρ g x := by
  -- the norms of the restrictions, as functions of the bits in `ι`
  let F : (ι → Bool) → ℝ := fun x₁ => lpNorm p fun x₂ => f (Sum.elim x₁ x₂)
  let G : (ι → Bool) → ℝ := fun y₁ => lpNorm q fun y₂ => g (Sum.elim y₁ y₂)
  have hr : 0 ≤ (1 - ρ) / 2 := by linarith
  have hr' : (1 - ρ) / 2 ≤ 1 := by linarith
  calc lpNorm p f * lpNorm q g = lpNorm p F * lpNorm q G := by
        rw [lpNorm_sumElim p f, lpNorm_sumElim q g]
    _ ≤ 𝔼 x₁, F x₁ * noiseOp ρ G x₁ :=
        hι F G (fun _ => lpNorm_mem hS p fun _ => hf _) fun _ => lpNorm_mem hT q fun _ => hg _
    _ = 𝔼 x₁, bernoulliAverage ((1 - ρ) / 2) fun P => F x₁ * G (x₁ + P) := by
        simp only [noiseOp, bernoulliAverage_const_mul]
    _ ≤ 𝔼 x₁, bernoulliAverage ((1 - ρ) / 2) fun P => 𝔼 x₂, f (Sum.elim x₁ x₂) *
          noiseOp ρ (fun y₂ => g (Sum.elim (x₁ + P) y₂)) x₂ :=
        expect_le_expect fun x₁ _ => bernoulliAverage_mono hr hr' fun P =>
          hκ _ _ (fun _ => hf _) fun _ => hg _
    _ = 𝔼 x, f x * noiseOp ρ g x := (expect_mul_noiseOp_sumElim ρ f g).symm

/-- Tensorization of reverse two-function inequalities for functions with values in `S` and `T`,
each the set of nonnegative or of positive reals. -/
private theorem le_expect_mul_noiseOp_of_unit_of_mem {S T : Set ℝ}
    (hS : S = Set.Ici 0 ∨ S = Set.Ioi 0) (hT : T = Set.Ici 0 ∨ T = Set.Ioi 0) {p q ρ : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (h : ∀ f g : (Unit → Bool) → ℝ, (∀ x, f x ∈ S) → (∀ x, g x ∈ T) →
      lpNorm p f * lpNorm q g ≤ 𝔼 x, f x * noiseOp ρ g x)
    {f g : (ι → Bool) → ℝ} (hf : ∀ x, f x ∈ S) (hg : ∀ x, g x ∈ T) :
    lpNorm p f * lpNorm q g ≤ 𝔼 x, f x * noiseOp ρ g x :=
  TwoFunction.of_fin (Φ := (· ≥ ·))
    (fun _ _ hf hg => le_expect_mul_noiseOp_of_isEmpty hS hT hp hq hf hg)
    (fun _ ih _ _ hf hg => le_expect_mul_noiseOp_sum hS hT (by linarith) hρ' ih h hf hg) f g hf hg

/-- **Tensorization of reverse two-function inequalities**: if the reverse two-function
inequality `‖f‖_p ‖g‖_q ≤ 𝔼_x f x · T_ρ g x` holds for all nonnegative functions of
a single bit, then it holds for all nonnegative functions on every cube
[O'Donnell, Exercise 10.6(c)][ODonnell2014]. -/
theorem le_expect_mul_noiseOp_of_unit {p q ρ : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ 1)
    (h : ∀ f g : (Unit → Bool) → ℝ, (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      lpNorm p f * lpNorm q g ≤ 𝔼 x, f x * noiseOp ρ g x)
    {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm p f * lpNorm q g ≤ 𝔼 x, f x * noiseOp ρ g x :=
  le_expect_mul_noiseOp_of_unit_of_mem (S := Set.Ici 0) (T := Set.Ici 0) (.inl rfl) (.inl rfl)
    hp hq hρ hρ' h hf hg

/-- **Tensorization of reverse two-function inequalities for positive `f`**: if the reverse
two-function inequality `‖f‖_p ‖g‖_q ≤ 𝔼_x f x · T_ρ g x` holds for all positive `f` and
nonnegative `g` of a single bit, then it holds for all positive `f` and nonnegative `g` on every
cube. This is the form needed for a negative exponent `p`
[O'Donnell, Exercise 10.6(c)][ODonnell2014]. -/
theorem le_expect_mul_noiseOp_of_unit_of_pos {p q ρ : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ 1)
    (h : ∀ f g : (Unit → Bool) → ℝ, (∀ x, 0 < f x) → (∀ x, 0 ≤ g x) →
      lpNorm p f * lpNorm q g ≤ 𝔼 x, f x * noiseOp ρ g x)
    {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm p f * lpNorm q g ≤ 𝔼 x, f x * noiseOp ρ g x :=
  le_expect_mul_noiseOp_of_unit_of_mem (S := Set.Ioi 0) (T := Set.Ici 0) (.inr rfl) (.inl rfl)
    hp hq hρ hρ' h hf hg

end Cslib.BitString
