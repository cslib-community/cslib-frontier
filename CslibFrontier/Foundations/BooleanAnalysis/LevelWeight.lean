/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.Noise
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Fourier weight by degree

The *degree-`k` part* of a real function `f` on the cube is `f^{=k} = ∑_{|S| = k} f̂(S) χ_S`
(`BitString.levelPart`), and its *Fourier weight at degree `k`* is
`W^k[f] = ∑_{|S| = k} f̂(S) ^ 2` (`BitString.levelWeight`)
[O'Donnell, Definition 1.19][ODonnell2014]. The degree-`k` part keeps exactly the Fourier
coefficients on the sets of size `k` (`BitString.fourierCoeff_levelPart`), has degree at most `k`
(`BitString.levelPart_mem_lowDegree`), and the parts sum to `f` (`BitString.sum_levelPart`). The
parts of different degrees are orthogonal, and the part of degree `k` has squared norm `W^k[f]`
(`BitString.expect_levelPart_mul_levelPart`) [O'Donnell, Exercise 1.18][ODonnell2014], so the
weights sum to `𝔼 f ^ 2` (`BitString.sum_levelWeight`), and the noise stability is
`Stab_ρ[f] = ∑_k ρ ^ k W^k[f]` (`BitString.noiseStability_eq_sum_levelWeight`)
[O'Donnell, Theorem 2.49][ODonnell2014]. The weight at degree zero is the squared
mean (`BitString.levelWeight_zero`), the weight at degree one is `∑ᵢ f̂({i}) ^ 2`
(`BitString.levelWeight_one`), and the weights above a level `t` are the Fourier weight
`∑_{t < |S|} f̂(S) ^ 2` that the library uses for spectral concentration
(`BitString.sum_levelWeight_Ioc`). The degree-one coefficients themselves sum to the correlation
`𝔼_x f(x) (x₁ + ⋯ + xₙ)` with the sum of the signs
(`BitString.sum_fourierCoeff_singleton_eq_expect`) [O'Donnell, equation (2.3)][ODonnell2014]. For
a function invariant under permutations of the `n` coordinates the degree-one coefficients are all
equal, so `W^1[f] · n = (𝔼_x f(x) ∑ᵢ xᵢ)²` (`BitString.levelWeight_one_mul_card_of_comp_perm`), or
`W^1[f] = (𝔼_x f(x) ∑ᵢ xᵢ / √n)²` (`BitString.levelWeight_one_eq_sq_expect_mul_of_comp_perm`)
[O'Donnell, Exercise 5.30][ODonnell2014].

## Main definitions

* `Cslib.BitString.levelPart`: the degree-`k` part `f^{=k}` of a real function.
* `Cslib.BitString.levelWeight`: the Fourier weight `W^k[f]` at degree `k`.

## Main results

* `Cslib.BitString.fourierCoeff_levelPart`: the Fourier coefficients of `f^{=k}`.
* `Cslib.BitString.sum_levelPart`: `f` is the sum of its parts of each degree.
* `Cslib.BitString.expect_levelPart_mul_levelPart`: the parts are orthogonal, with
  `‖f^{=k}‖² = W^k[f]`.
* `Cslib.BitString.sum_levelWeight`: the weights sum to `𝔼 f ^ 2`, and to one for a Boolean
  function read as signs (`Cslib.BitString.sum_levelWeight_signVal`).
* `Cslib.BitString.noiseStability_eq_sum_levelWeight`: `Stab_ρ[f] = ∑_k ρ ^ k W^k[f]`.
* `Cslib.BitString.levelWeight_zero`, `Cslib.BitString.levelWeight_one`,
  `Cslib.BitString.sum_levelWeight_Ioc`: the weights at degrees zero and one and the weight above
  a level.
* `Cslib.BitString.sum_fourierCoeff_singleton_eq_expect`: `∑ᵢ f̂({i}) = 𝔼 f(x) (x₁ + ⋯ + xₙ)`.
* `Cslib.BitString.fourierCoeff_singleton_eq_of_comp_swap`,
  `Cslib.BitString.levelWeight_one_mul_card_of_comp_perm`,
  `Cslib.BitString.levelWeight_one_eq_sq_expect_mul_of_comp_perm`: the degree-one coefficients and
  weight of a symmetric function.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The degree-`k` part `f^{=k} = ∑_{|S| = k} f̂(S) χ_S` of a real function on the cube
[O'Donnell, Definition 1.19][ODonnell2014]. -/
@[expose] noncomputable def levelPart (k : ℕ) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ S with #S = k, fourierCoeff f S * chi ℝ S x

/-- The Fourier weight `W^k[f] = ∑_{|S| = k} f̂(S) ^ 2` of a real function at degree `k`
[O'Donnell, Definition 1.19][ODonnell2014]. -/
@[expose] noncomputable def levelWeight (k : ℕ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S with #S = k, fourierCoeff f S ^ 2

/-- The degree-`k` part as a combination of all the characters, with weight zero off size `k`. -/
theorem levelPart_eq_sum_ite (k : ℕ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    levelPart k f x = ∑ S, (if #S = k then fourierCoeff f S else 0) * chi ℝ S x := by
  simp only [levelPart, sum_filter, ite_mul, zero_mul]

/-- The degree-`k` part keeps the Fourier coefficients on the sets of size `k` and no others. -/
@[simp] theorem fourierCoeff_levelPart (k : ℕ) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (levelPart k f) S = if #S = k then fourierCoeff f S else 0 := by
  rw [funext (levelPart_eq_sum_ite k f), fourierCoeff_sum_mul_chi]

/-- The degree-`k` part has degree at most `k`. -/
theorem levelPart_mem_lowDegree (k : ℕ) (f : (ι → Bool) → ℝ) :
    levelPart k f ∈ lowDegree ℝ ι k := by
  have h : levelPart k f = ∑ S with #S = k, fourierCoeff f S • chi ℝ S := by
    funext x
    simp [levelPart]
  rw [h]
  exact Submodule.sum_mem _ fun S hS =>
    Submodule.smul_mem _ _ ((mem_filter.1 hS).2 ▸ chi_mem_lowDegree S)

/-- **A function is the sum of its parts of each degree.** -/
theorem sum_levelPart (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    ∑ k ∈ range (Fintype.card ι + 1), levelPart k f x = f x := by
  simp only [levelPart]
  rw [sum_fiberwise_of_maps_to (g := card)
    (fun S _ => mem_range.2 (Nat.lt_succ_of_le (card_le_univ S))), sum_fourierCoeff_mul_chi]

/-- **The parts of different degrees are orthogonal**, and the part of degree `k` has squared
norm `W^k[f]` [O'Donnell, Exercise 1.18][ODonnell2014]. -/
theorem expect_levelPart_mul_levelPart (j k : ℕ) (f : (ι → Bool) → ℝ) :
    𝔼 x, levelPart j f x * levelPart k f x = if j = k then levelWeight k f else 0 := by
  rw [expect_mul_eq_sum_fourierCoeff_mul]
  simp only [fourierCoeff_levelPart]
  split_ifs with h
  · subst h
    rw [levelWeight, sum_filter]
    refine sum_congr rfl fun S _ => ?_
    split_ifs <;> ring
  · refine sum_eq_zero fun S _ => ?_
    split_ifs with hj hk
    · exact absurd (hj.symm.trans hk) h
    all_goals simp

/-- The part of degree `k` has squared norm `W^k[f]`. -/
theorem expect_levelPart_sq (k : ℕ) (f : (ι → Bool) → ℝ) :
    𝔼 x, levelPart k f x ^ 2 = levelWeight k f := by
  simp only [sq, expect_levelPart_mul_levelPart, ↓reduceIte]

/-- The Fourier weight at each degree is nonnegative. -/
theorem levelWeight_nonneg (k : ℕ) (f : (ι → Bool) → ℝ) : 0 ≤ levelWeight k f :=
  sum_nonneg fun _ _ => sq_nonneg _

/-- There is no Fourier weight above the number of coordinates. -/
theorem levelWeight_eq_zero_of_card_lt {k : ℕ} (hk : Fintype.card ι < k) (f : (ι → Bool) → ℝ) :
    levelWeight k f = 0 := by
  refine sum_eq_zero fun S hS => ?_
  have := card_le_univ S
  have := (mem_filter.1 hS).2
  omega

/-- **Parseval's identity by degree**: the Fourier weights sum to `𝔼 f ^ 2`. -/
theorem sum_levelWeight (f : (ι → Bool) → ℝ) :
    ∑ k ∈ range (Fintype.card ι + 1), levelWeight k f = 𝔼 x, f x ^ 2 := by
  simp only [levelWeight]
  rw [sum_fiberwise_of_maps_to (g := card)
    (fun S _ => mem_range.2 (Nat.lt_succ_of_le (card_le_univ S))),
    expect_sq_eq_sum_fourierCoeff_sq]

/-- The Fourier weights of a Boolean function read as signs sum to one. -/
theorem sum_levelWeight_signVal (f : (ι → Bool) → Bool) :
    ∑ k ∈ range (Fintype.card ι + 1), levelWeight k (fun x => signVal (f x)) = 1 := by
  rw [sum_levelWeight, expect_sq_eq_sum_fourierCoeff_sq, sum_fourierCoeff_sq_signVal]

/-- **The Fourier formula for the noise stability by degree**: `Stab_ρ[f] = ∑_k ρ ^ k W^k[f]`
[O'Donnell, Theorem 2.49][ODonnell2014]. -/
theorem noiseStability_eq_sum_levelWeight (ρ : ℝ) (f : (ι → Bool) → ℝ) :
    noiseStability ρ f = ∑ k ∈ range (Fintype.card ι + 1), ρ ^ k * levelWeight k f := by
  rw [noiseStability_eq_sum, ← sum_fiberwise_of_maps_to (g := card)
    fun S _ => mem_range.2 (Nat.lt_succ_of_le (card_le_univ S))]
  refine sum_congr rfl fun k _ => ?_
  rw [levelWeight, mul_sum]
  exact sum_congr rfl fun S hS => by rw [(mem_filter.1 hS).2]

/-- The Fourier weight at degree zero is the squared mean. -/
theorem levelWeight_zero (f : (ι → Bool) → ℝ) : levelWeight 0 f = (𝔼 x, f x) ^ 2 := by
  have h : (univ.filter fun S : Finset ι => #S = 0) = {∅} := by
    ext S
    simp
  rw [levelWeight, h, sum_singleton, fourierCoeff_empty]

/-- The Fourier weight at degree one is the sum of the squared degree-one coefficients,
`W^1[f] = ∑ᵢ f̂({i}) ^ 2`. -/
theorem levelWeight_one (f : (ι → Bool) → ℝ) :
    levelWeight 1 f = ∑ i, fourierCoeff f {i} ^ 2 := by
  have h : (univ.filter fun S : Finset ι => #S = 1) =
      univ.map ⟨fun i => {i}, singleton_injective⟩ := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk, card_eq_one]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  rw [levelWeight, h, sum_map]
  rfl

/-- **The degree-one coefficients and the vote count**: the degree-one Fourier coefficients of `f`
sum to its correlation with the sum of the signs of the bits
[O'Donnell, equation (2.3)][ODonnell2014]. -/
theorem sum_fourierCoeff_singleton_eq_expect (f : (ι → Bool) → ℝ) :
    ∑ i, fourierCoeff f {i} = 𝔼 x, f x * ∑ i, signVal (x i) := by
  simp only [fourierCoeff, chi_singleton, mul_sum]
  exact (expect_sum_comm _ _ _).symm

/-- The Fourier weights above level `t` are the Fourier weight on the sets of more than `t`
coordinates. -/
theorem sum_levelWeight_Ioc (f : (ι → Bool) → ℝ) (t : ℕ) :
    ∑ k ∈ Ioc t (Fintype.card ι), levelWeight k f = ∑ S with t < #S, fourierCoeff f S ^ 2 := by
  rw [← sum_fiberwise_of_maps_to (g := card) (t := Ioc t (Fintype.card ι))
    (fun S hS => mem_Ioc.2 ⟨(mem_filter.1 hS).2, card_le_univ S⟩)]
  refine sum_congr rfl fun k hk => ?_
  rw [levelWeight, filter_filter]
  refine sum_congr (filter_congr fun S _ => ?_) fun _ _ => rfl
  exact ⟨fun h => ⟨h ▸ (mem_Ioc.1 hk).1, h⟩, fun h => h.2⟩

/-! ### Degree-one weight of symmetric functions -/

/-- If `f` is unchanged when coordinates `i` and `j` are swapped, its degree-one Fourier
coefficients at `i` and `j` agree. -/
theorem fourierCoeff_singleton_eq_of_comp_swap {f : (ι → Bool) → ℝ} {i j : ι}
    (hf : ∀ x, f (x ∘ Equiv.swap i j) = f x) : fourierCoeff f {i} = fourierCoeff f {j} := by
  have h := fourierCoeff_comp_arrowCongr (Equiv.swap i j) f {i}
  rw [Equiv.symm_swap, map_singleton, Equiv.coe_toEmbedding, Equiv.swap_apply_left] at h
  rw [← h]
  exact congrArg (fourierCoeff · {i}) (funext fun x => (hf x).symm)

/-- **Degree-one weight of a symmetric function.** If `f` is invariant under permutations of the
coordinates, all its degree-one coefficients are equal, so
`W^1[f] · n = (∑ᵢ f̂({i}))² = (𝔼_x f(x) ∑ᵢ xᵢ)²`, where `xᵢ = signVal (x i)` and `n` is the
number of coordinates [O'Donnell, Exercise 5.30][ODonnell2014]. -/
theorem levelWeight_one_mul_card_of_comp_perm {f : (ι → Bool) → ℝ}
    (hf : ∀ (σ : Equiv.Perm ι) x, f (x ∘ σ) = f x) :
    levelWeight 1 f * Fintype.card ι = (𝔼 x, f x * ∑ i, signVal (x i)) ^ 2 := by
  have hc (i j : ι) : fourierCoeff f {i} = fourierCoeff f {j} :=
    fourierCoeff_singleton_eq_of_comp_swap (hf _)
  rw [← sum_fourierCoeff_singleton_eq_expect, sq, sum_mul_sum, levelWeight_one, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  simp only [← hc i, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- **Degree-one weight of a symmetric function**, normalized: for `f` invariant under
permutations of the `n` coordinates, `W^1[f] = (𝔼_x f(x) · ∑ᵢ xᵢ / √n)²`, where
`xᵢ = signVal (x i)` [O'Donnell, Exercise 5.30][ODonnell2014]. -/
theorem levelWeight_one_eq_sq_expect_mul_of_comp_perm {f : (ι → Bool) → ℝ}
    (hf : ∀ (σ : Equiv.Perm ι) x, f (x ∘ σ) = f x) :
    levelWeight 1 f =
      (𝔼 x, f x * ((√(Fintype.card ι : ℝ))⁻¹ * ∑ i, signVal (x i))) ^ 2 := by
  have h := levelWeight_one_mul_card_of_comp_perm hf
  obtain hn | hn := (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)).eq_or_lt
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by exact_mod_cast hn.symm)
    simp [levelWeight_one]
  simp only [mul_left_comm _ (√(Fintype.card ι : ℝ))⁻¹, ← mul_expect, mul_pow, inv_pow,
    Real.sq_sqrt hn.le, ← h]
  field_simp

end Cslib.BitString
