/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.SmallBias
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Limitations on small-bias generators

We read the bits `Bool` as the field `GF(2)` (exclusive or and conjunction, the ring structure
under which the library's parities and inner products of bit strings are sums and products).
If the output bits of a sample space `G : σ → ι → Bool`, as functions of the seed, all lie in a
fixed affine translate of a subspace `W` of the functions `σ → Bool` (each output bit is a constant
plus an element of `W`), and there are more output bits than the dimension of `W`, then some
nonempty set of output bits has a constant sum, so `G`, with a uniform seed, has bias `±1` there
(`Cslib.BitString.exists_abs_bias_eq_one_of_finrank_lt`).

This gives the limitations on small-bias generators of [Goldreich, Exercise
8.37][Goldreich2007DraftR4]. An `ε`-bias generator `G : {0,1}^k → {0,1}^ℓ` with `ε < 1` whose
output bits are `GF(2)` polynomials of total degree at most `d` in the seed bits has
`ℓ ≤ ∑_{i=1}^d C(k, i)`: the polynomials, without their free terms, lie in the span of the
products of between one and `d` seed bits (`Cslib.BitString.le_sum_choose_of_isSmallBias`).
Whatever the degree, `ℓ < 2^k`, since the functions vanishing at a fixed seed form a subspace of
dimension `2^k - 1` (`Cslib.BitString.card_lt_card_of_isSmallBias`, for any finite seed set), and
if `ℓ > k`, then `G` is not a linear map (`Cslib.BitString.not_exists_linearMap_of_isSmallBias`,
the case `d = 1`).

## Main results

* `Cslib.BitString.exists_abs_bias_eq_one_of_finrank_lt`: few dimensions force a constant parity.
* `Cslib.BitString.le_sum_choose_of_isSmallBias`: the degree bound of Exercise 8.37.
* `Cslib.BitString.card_lt_card_of_isSmallBias`: Corollary 1 of Exercise 8.37, `ℓ < 2^k`.
* `Cslib.BitString.not_exists_linearMap_of_isSmallBias`: Corollary 2 of Exercise 8.37.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft of March 2007,
  Exercise 8.37][Goldreich2007DraftR4]
-/

public section

namespace Cslib.BitString

open Finset Probability Module

variable {σ ι : Type*} [Fintype σ] [Nonempty σ] [Fintype ι] [DecidableEq ι]

/-- **A low-dimensional span of the output bits forces a constant parity.** If every output bit
`s ↦ G s i` of a sample space is a constant plus an element of a subspace `W` of the functions on
the seeds, and there are more output bits than the dimension of `W`, then some nonempty set `S` of
output bits has a constant parity, so the bias of `G` at `S`, with a uniform seed, is `±1`. -/
theorem exists_abs_bias_eq_one_of_finrank_lt (G : σ → ι → Bool) (W : Submodule Bool (σ → Bool))
    (hW : ∀ i, ∃ c : Bool, (fun s => G s i) - Function.const σ c ∈ W)
    (hdim : finrank Bool W < Fintype.card ι) :
    ∃ S : Finset ι, S.Nonempty ∧ |bias ((PMF.uniformOfFintype σ).map G) S| = 1 := by
  choose c hc using hW
  let w : ι → W := fun i => ⟨_, hc i⟩
  have hw : ¬ LinearIndependent Bool w := fun h => hdim.not_ge h.fintype_card_le_finrank
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hw
  refine ⟨({i | g i = true} : Finset ι), ⟨i₀, by simpa using Bool.eq_true_of_not_eq_false hi₀⟩, ?_⟩
  -- The parity of the output on `S` is the constant `∑_{i ∈ S} c i`.
  have hconst (s : σ) :
      parityOn ({i | g i = true} : Finset ι) (G s) = ∑ i with g i = true, c i := by
    have h := congrArg (fun v : W => (v : σ → Bool) s) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Pi.sub_apply, Function.const_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply,
      w] at h
    rw [parityOn_eq_sum, sum_filter, sum_filter, ← sub_eq_zero, ← sum_sub_distrib]
    refine Eq.trans (sum_congr rfl fun i _ => ?_) h
    cases g i <;> cases G s i <;> cases c i <;> rfl
  rw [bias_uniformOfFintype_map]
  simp_rw [chi_eq_signVal_parityOn, hconst]
  rw [Finset.expect_const univ_nonempty]
  cases ∑ i with g i = true, c i <;> simp [signVal]

/-- An `ε`-biased sample space with `ε < 1` has its output bits outside every translate of a
subspace of smaller dimension than their number. -/
theorem card_le_finrank_of_isSmallBias {G : σ → ι → Bool} {ε : ℝ} (hε : ε < 1)
    (hG : IsSmallBias ε ((PMF.uniformOfFintype σ).map G)) (W : Submodule Bool (σ → Bool))
    (hW : ∀ i, ∃ c : Bool, (fun s => G s i) - Function.const σ c ∈ W) :
    Fintype.card ι ≤ finrank Bool W := by
  by_contra h
  obtain ⟨S, hS, h1⟩ := exists_abs_bias_eq_one_of_finrank_lt G W hW (not_le.1 h)
  linarith [hG S hS]

/-- **Corollary 1 of [Goldreich, Exercise 8.37][Goldreich2007DraftR4]**: an `ε`-biased sample space
with `ε < 1` has fewer output bits than seeds; for an `ε`-bias generator with `k`-bit seeds,
`ℓ(k) < 2^k`, whatever the degree of its output bits. -/
theorem card_lt_card_of_isSmallBias {G : σ → ι → Bool} {ε : ℝ} (hε : ε < 1)
    (hG : IsSmallBias ε ((PMF.uniformOfFintype σ).map G)) :
    Fintype.card ι < Fintype.card σ := by
  classical
  obtain ⟨s₀⟩ := ‹Nonempty σ›
  let T : Finset (σ → Bool) := (univ.erase s₀).image fun s => Pi.single s true
  have hW (i : ι) : ∃ c : Bool, (fun s => G s i) - Function.const σ c ∈
      Submodule.span Bool (T : Set (σ → Bool)) := by
    refine ⟨G s₀ i, ?_⟩
    suffices (fun s => G s i) - Function.const σ (G s₀ i) =
        ∑ s ∈ univ.erase s₀, (G s i - G s₀ i) • Pi.single s true from
      this ▸ Submodule.sum_mem _ fun s hs =>
        Submodule.smul_mem _ _ (Submodule.subset_span (mem_image_of_mem _ hs))
    funext t
    simp only [Pi.sub_apply, Function.const_apply, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_zero, sum_ite_eq]
    by_cases ht : t = s₀ <;> simp [ht, show (true : Bool) = 1 from rfl]
  have h := (card_le_finrank_of_isSmallBias hε hG _ hW).trans
    ((finrank_span_finset_le_card (R := Bool) T).trans card_image_le)
  rw [card_erase_of_mem (mem_univ _), card_univ] at h
  have := Fintype.card_pos (α := σ)
  omega

/-- On bits, a positive power is the identity. -/
private theorem bool_pow_of_ne_zero (b : Bool) {n : ℕ} (hn : n ≠ 0) : b ^ n = b := by
  cases b
  exacts [zero_pow hn, one_pow n]

/-- **Limitations on small-bias generators** [Goldreich, Exercise 8.37][Goldreich2007DraftR4]: if
`G : {0,1}^k → {0,1}^ℓ`, with a uniform seed, is `ε`-biased for some `ε < 1`, and each output bit
of `G` is a `GF(2)` polynomial in the seed bits of total degree at most `d`, then
`ℓ ≤ ∑_{i=1}^d C(k, i)`. -/
theorem le_sum_choose_of_isSmallBias {k ℓ : ℕ} {G : (Fin k → Bool) → Fin ℓ → Bool} {ε : ℝ}
    (hε : ε < 1) (hG : IsSmallBias ε ((PMF.uniformOfFintype (Fin k → Bool)).map G)) {d : ℕ}
    (p : Fin ℓ → MvPolynomial (Fin k) Bool) (hdeg : ∀ i, (p i).totalDegree ≤ d)
    (hp : ∀ s i, MvPolynomial.eval s (p i) = G s i) :
    ℓ ≤ ∑ i ∈ Icc 1 d, k.choose i := by
  classical
  let 𝒯 : Finset (Finset (Fin k)) := (Icc 1 d).biUnion fun i => powersetCard i univ
  let m : Finset (Fin k) → (Fin k → Bool) → Bool := fun T s => ∏ j ∈ T, s j
  let W := Submodule.span Bool ((𝒯.image m : Finset _) : Set ((Fin k → Bool) → Bool))
  have hm (e : Fin k →₀ ℕ) (he : e ≠ 0) (hle : (e.sum fun _ n => n) ≤ d) : m e.support ∈ W := by
    have hcard : #e.support ≤ e.sum fun _ n => n := by
      rw [Finsupp.sum, card_eq_sum_ones]
      exact sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj)
    exact Submodule.subset_span (mem_image_of_mem _ (mem_biUnion.2
      ⟨#e.support, mem_Icc.2 ⟨card_pos.2 (Finsupp.support_nonempty_iff.2 he), hcard.trans hle⟩,
        mem_powersetCard.2 ⟨subset_univ _, rfl⟩⟩))
  have hW (i : Fin ℓ) : ∃ c : Bool, (fun s => G s i) - Function.const _ c ∈ W := by
    refine ⟨(p i).coeff 0, ?_⟩
    suffices (fun s => G s i) - Function.const _ ((p i).coeff 0) =
        ∑ e ∈ (p i).support with e ≠ 0, (p i).coeff e • m e.support from
      this ▸ Submodule.sum_mem _ fun e he => Submodule.smul_mem _ _ (hm e (mem_filter.1 he).2
        ((MvPolynomial.le_totalDegree (mem_filter.1 he).1).trans (hdeg i)))
    funext s
    simp only [Pi.sub_apply, Function.const_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, m]
    rw [← hp, MvPolynomial.eval_eq, ← sum_filter_add_sum_filter_not _ (· ≠ 0)]
    have h0 : ∑ e ∈ (p i).support with ¬e ≠ 0,
        (p i).coeff e * ∏ j ∈ e.support, s j ^ e j = (p i).coeff 0 := by
      rw [sum_eq_single 0 (fun e he he0 => absurd he0 (by simpa using (mem_filter.1 he).2))
        (by simp [MvPolynomial.mem_support_iff])]
      simp
    rw [h0, add_sub_cancel_right]
    exact sum_congr rfl fun e _ => congrArg _ (prod_congr rfl fun j hj =>
      bool_pow_of_ne_zero _ (Finsupp.mem_support_iff.1 hj))
  have h := (card_le_finrank_of_isSmallBias hε hG W hW).trans
    ((finrank_span_finset_le_card (R := Bool) _).trans card_image_le)
  rw [Fintype.card_fin, card_biUnion fun _ _ _ _ hij => pairwise_disjoint_powersetCard _ hij] at h
  simpa [card_powersetCard] using h

/-- **Corollary 2 of [Goldreich, Exercise 8.37][Goldreich2007DraftR4]**: an `ε`-bias generator
`G : {0,1}^k → {0,1}^ℓ` with `ε < 1` and `ℓ > k` is not a `GF(2)`-linear map. -/
theorem not_exists_linearMap_of_isSmallBias {k ℓ : ℕ} {G : (Fin k → Bool) → Fin ℓ → Bool}
    {ε : ℝ} (hε : ε < 1) (hG : IsSmallBias ε ((PMF.uniformOfFintype (Fin k → Bool)).map G))
    (hℓ : k < ℓ) : ¬ ∃ L : (Fin k → Bool) →ₗ[Bool] Fin ℓ → Bool, ⇑L = G := by
  rintro ⟨L, rfl⟩
  let e : Fin k → Fin k → Bool := fun j j' => if j = j' then 1 else 0
  let p : Fin ℓ → MvPolynomial (Fin k) Bool := fun i =>
    ∑ j, MvPolynomial.C (L (e j) i) * MvPolynomial.X j
  have hdeg (i : Fin ℓ) : (p i).totalDegree ≤ 1 :=
    MvPolynomial.totalDegree_finsetSum_le fun j _ =>
      (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_X])
  have hp (s : Fin k → Bool) (i : Fin ℓ) : MvPolynomial.eval s (p i) = L s i := by
    simp only [p, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      LinearMap.pi_apply_eq_sum_univ L s, Finset.sum_apply]
    exact sum_congr rfl fun j _ => by simp [mul_comm, e]
  have h := le_sum_choose_of_isSmallBias hε hG p hdeg hp
  simp at h; omega

end Cslib.BitString
