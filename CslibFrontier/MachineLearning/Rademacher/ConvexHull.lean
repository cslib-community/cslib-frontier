/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.Rademacher.Basic
public import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Rademacher complexity of convex hulls

Taking the convex hull of a bounded set of vectors or real-valued functions does not change its
Rademacher complexity [MohriRostamizadehTalwalkar2018, Lemma 7.4]
[ShalevShwartzBenDavid2014, Lemma 26.7]. For every fixed sign vector `σ : Fin m → Bool`, the
correlation functional `f ↦ 𝔼 i, signVal (σ i) * f (S i)` is affine, so its sublevel sets are
convex. Hence the supremum over `convexHull ℝ F` equals the supremum over `F` pointwise in `σ`,
and averaging over `σ` gives `R̂_S(conv F) = R̂_S(F)` (and `R_m(conv F) = R_m(F)` under any
distribution on a finite domain).

Unlike [BartlettMendelson2002, Theorem 12(2)], whose two-sided Rademacher complexity takes the
absolute value `|∑ i, σ_i f(z_i)|` and is therefore also invariant under taking the symmetric
(absolute) convex hull, this library uses the one-sided Rademacher complexity of
[MohriRostamizadehTalwalkar2018] and [ShalevShwartzBenDavid2014]. The convex hull invariance holds
verbatim for the one-sided definition with no symmetry requirement on `F`.

## Main results

* `Cslib.MachineLearning.abs_le_of_mem_convexHull`: a pointwise `|·| ≤ B` bound extends from `F`
  to `convexHull ℝ F`.
* `Cslib.MachineLearning.rademacherAverage_convexHull`: for a bounded set `A : Set (Fin m → ℝ)`,
  `rademacherAverage` of `convexHull ℝ A` equals that of `A`
  [ShalevShwartzBenDavid2014, Lemma 26.7].
* `Cslib.MachineLearning.empiricalRademacherComplexity_convexHull`:
  `R̂_S(conv F) = R̂_S(F)` [MohriRostamizadehTalwalkar2018, Lemma 7.4].
* `Cslib.MachineLearning.rademacherComplexity_convexHull`:
  `R_m(conv F) = R_m(F)` on a finite domain.

## References

* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Section 7.3.3, Lemma 7.4 (p. 157)
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Chapter 26, Lemma 26.7
* [P. L. Bartlett, S. Mendelson, *Rademacher and Gaussian complexities: risk bounds and
  structural results*][BartlettMendelson2002], Theorem 12(2) (two-sided variant)
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.MachineLearning

open Cslib.BitString

/-- A pointwise uniform bound `|f z| ≤ B` extends from a function class `F` to its convex hull. -/
theorem abs_le_of_mem_convexHull {Z : Type*} {F : Set (Z → ℝ)} {B : ℝ}
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) {f : Z → ℝ} (hf : f ∈ convexHull ℝ F) (z : Z) :
    |f z| ≤ B := by
  have hconv : Convex ℝ {g : Z → ℝ | ∀ x, |g x| ≤ B} := fun g₁ hg₁ g₂ hg₂ a b ha hb hab x => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * g₁ x + b * g₂ x| ≤ |a * g₁ x| + |b * g₂ x| := abs_add_le _ _
      _ = a * |g₁ x| + b * |g₂ x| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * B + b * B := add_le_add
          (mul_le_mul_of_nonneg_left (hg₁ x) ha) (mul_le_mul_of_nonneg_left (hg₂ x) hb)
      _ = B := by rw [← add_mul, hab, one_mul]
  exact (convexHull_min (fun g hg => hF g hg) hconv hf) z

/-- The sublevel set `{v | 𝔼 i, signVal (σ i) * v i ≤ M}` is convex, so a linear correlation with
fixed signs bounded on `A` stays bounded on `convexHull ℝ A`. -/
private theorem expect_signVal_mul_le_of_mem_convexHull {m : ℕ} {A : Set (Fin m → ℝ)}
    {σ : Fin m → Bool} {M : ℝ} (hA : ∀ v ∈ A, 𝔼 i, signVal (σ i) * v i ≤ M)
    {v : Fin m → ℝ} (hv : v ∈ convexHull ℝ A) :
    𝔼 i, signVal (σ i) * v i ≤ M := by
  have hconv : Convex ℝ {u : Fin m → ℝ | 𝔼 i, signVal (σ i) * u i ≤ M} :=
    fun u₁ hu₁ u₂ hu₂ a b ha hb hab => by
      have hlin : 𝔼 i, signVal (σ i) * (a • u₁ + b • u₂) i =
          a * (𝔼 i, signVal (σ i) * u₁ i) + b * (𝔼 i, signVal (σ i) * u₂ i) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_expect,
          ← Finset.expect_add_distrib]
        exact Finset.expect_congr rfl fun i _ => by ring
      change 𝔼 i, signVal (σ i) * (a • u₁ + b • u₂) i ≤ M
      rw [hlin]
      exact (add_le_add (mul_le_mul_of_nonneg_left hu₁ ha)
        (mul_le_mul_of_nonneg_left hu₂ hb)).trans_eq (by rw [← add_mul, hab, one_mul])
  exact convexHull_min (fun u hu => hA u hu) hconv hv

/-- A real average bound for `A : Set (Fin m → ℝ)` whose coordinates are bounded by `B`. -/
private theorem bddAbove_range_expect_sub {m : ℕ} {A : Set (Fin m → ℝ)} {B : ℝ}
    (hA : ∀ v ∈ A, ∀ i, |v i| ≤ B) (σ : Fin m → Bool) :
    BddAbove (Set.range fun v : A => 𝔼 i, signVal (σ i) * v.1 i) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, by rintro _ ⟨v, rfl⟩; simp⟩
  · have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    refine ⟨B, ?_⟩
    rintro _ ⟨v, rfl⟩
    refine Finset.expect_le Finset.univ_nonempty fun i _ => ?_
    exact (le_abs_self _).trans (by rw [abs_mul, abs_signVal, one_mul]; exact hA v.1 v.2 i)

/-- **Rademacher average of a convex hull** [ShalevShwartzBenDavid2014, Lemma 26.7]: taking the
convex hull of a uniformly bounded set `A : Set (Fin m → ℝ)` preserves its Rademacher average. -/
theorem rademacherAverage_convexHull {m : ℕ} {A : Set (Fin m → ℝ)} {B : ℝ}
    (hA : ∀ v ∈ A, ∀ i, |v i| ≤ B) :
    rademacherAverage (fun v : convexHull ℝ A => v.1) =
      rademacherAverage (fun v : A => v.1) := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · have : IsEmpty (↥(convexHull ℝ (∅ : Set (Fin m → ℝ)))) := by
      simp only [convexHull_empty, Set.isEmpty_coe_sort]
    have : IsEmpty (↥(∅ : Set (Fin m → ℝ))) := Set.isEmpty_coe_sort.mpr rfl
    rw [rademacherAverage_of_isEmpty, rademacherAverage_of_isEmpty]
  refine le_antisymm ?_ (rademacherAverage_le_of_forall_exists
    (fun v i => abs_le_of_mem_convexHull hA v.2 i)
    fun v => ⟨⟨v.1, subset_convexHull ℝ A v.2⟩, rfl⟩)
  have : Nonempty A := hne.to_subtype
  have : Nonempty (convexHull ℝ A) := (hne.mono (subset_convexHull ℝ A)).to_subtype
  rw [rademacherAverage_def, rademacherAverage_def]
  exact Finset.expect_le_expect fun σ _ => ciSup_le fun v =>
    expect_signVal_mul_le_of_mem_convexHull
      (fun u hu => le_ciSup (bddAbove_range_expect_sub hA σ) ⟨u, hu⟩) v.2

/-- Every element of `convexHull ℝ F` evaluates at `S` inside the convex hull of the images of `F`
under evaluation at `S`. -/
private theorem eval_mem_convexHull {Z : Type*} {F : Set (Z → ℝ)} {m : ℕ} (S : Fin m → Z)
    {f : Z → ℝ} (hf : f ∈ convexHull ℝ F) :
    (fun i => f (S i)) ∈ convexHull ℝ ((fun g : Z → ℝ => fun i => g (S i)) '' F) :=
  let A : Set (Fin m → ℝ) := (fun g : Z → ℝ => fun i => g (S i)) '' F
  convexHull_min (t := {g | (fun i => g (S i)) ∈ convexHull ℝ A})
    (fun g hg => subset_convexHull ℝ A ⟨g, hg, rfl⟩)
    (fun _ hg₁ _ hg₂ _ _ ha hb hab => (convex_convexHull ℝ A) hg₁ hg₂ ha hb hab) hf

/-- **Empirical Rademacher complexity of a convex hull** [MohriRostamizadehTalwalkar2018,
Lemma 7.4]: for a uniformly bounded function class `F : Set (Z → ℝ)` and any sample `S : Fin m → Z`,
`R̂_S(conv F) = R̂_S(F)`. -/
theorem empiricalRademacherComplexity_convexHull {Z : Type*} {F : Set (Z → ℝ)} {B : ℝ}
    (hF : ∀ f ∈ F, ∀ i, |f i| ≤ B) {m : ℕ} (S : Fin m → Z) :
    empiricalRademacherComplexity (convexHull ℝ F) S =
      empiricalRademacherComplexity F S := by
  let A : Set (Fin m → ℝ) := (fun g : Z → ℝ => fun i => g (S i)) '' F
  have hA : ∀ v ∈ A, ∀ i, |v i| ≤ B := by rintro _ ⟨g, hg, rfl⟩ i; exact hF g hg (S i)
  have hF_eq : empiricalRademacherComplexity F S = rademacherAverage (fun v : A => v.1) := by
    rw [empiricalRademacherComplexity_def]
    exact rademacherAverage_eq_of_forall_exists (fun g i => hF g.1 g.2 (S i))
      (fun v i => hA v.1 v.2 i) (fun g => ⟨⟨fun i => g.1 (S i), ⟨g.1, g.2, rfl⟩⟩, rfl⟩)
      fun ⟨_, g, hg, rfl⟩ => ⟨⟨g, hg⟩, rfl⟩
  refine le_antisymm ?_ (empiricalRademacherComplexity_mono (subset_convexHull ℝ F)
    (fun f hf z => abs_le_of_mem_convexHull hF hf z) S)
  rw [hF_eq, ← rademacherAverage_convexHull hA, empiricalRademacherComplexity_def]
  exact rademacherAverage_le_of_forall_exists
    (fun v i => abs_le_of_mem_convexHull hA v.2 i)
    fun f => ⟨⟨fun i => f.1 (S i), eval_mem_convexHull S f.2⟩, rfl⟩

/-- **Rademacher complexity of a convex hull** [MohriRostamizadehTalwalkar2018, Lemma 7.4]:
for a uniformly bounded function class `F : Set (Z → ℝ)` on a finite domain `Z`,
`R_m(conv F) = R_m(F)`. -/
theorem rademacherComplexity_convexHull {Z : Type*} [Fintype Z] (D : PMF Z)
    {F : Set (Z → ℝ)} {B : ℝ} (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) (m : ℕ) :
    rademacherComplexity D (convexHull ℝ F) m = rademacherComplexity D F m := by
  rw [rademacherComplexity_def, rademacherComplexity_def]
  exact Finset.sum_congr rfl fun S _ => by
    rw [empiricalRademacherComplexity_convexHull hF S]

end Cslib.MachineLearning
