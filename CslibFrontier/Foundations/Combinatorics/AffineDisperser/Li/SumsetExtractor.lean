/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.AffineSource
public import CslibFrontier.Probability.Extractor.TwoSource
public import CslibFrontier.Probability.SmallBias
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.MinEntropy.ChainRule
import CslibFrontier.Probability.MinEntropy.Flat
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sumset extractors: structural theory, Fourier convolution, and bent-function extraction

This module develops foundational theory for `(k₁, k₂, ε)` sumset extractors
(`Cslib.AffineDisperser.Li.IsSumsetExtractor`), building toward explicit sumset extractors for
frontier circuit bounds (#7793):

1. **Structural properties of `IsSumsetExtractor`:**
   symmetry (`IsSumsetExtractor.symm`), monotonicity (`IsSumsetExtractor.mono`), translation and
   linear-automorphism invariance (`IsSumsetExtractor.comp_add_right`,
   `IsSumsetExtractor.comp_linearEquiv`), smooth `(k, δ)`-source robustness
   (`IsSumsetExtractor.dist_le_of_isSource`), flat-source equivalence
   (`isSumsetExtractor_iff_flat`), min-entropy monotonicity under independent XOR
   (`max_le_minEntropy_sumset`), and the zero-padded reduction to
   `Cslib.Probability.IsTwoSourceExtractor` (`isTwoSourceExtractor_append_of_isSumsetExtractor`).

2. **Fourier convolution and an unconditional explicit high-entropy sumset extractor:**
   for independent bit-string distributions `A` and `B`, the XOR-sum `A + B` multiplies their
   Walsh–Hadamard biases (`bias_sumset`). Consequently, any Boolean function with uniform Fourier
   coefficient bound `|f̂(S)| ≤ β` extracts from `(k₁, k₂)` sumset sources with error at most
   `β · 2 ^ (n - (k₁ + k₂) / 2) / 2` (`dist_map_sumset_bool_le_of_fourierCoeff_le`).
   Instantiating this with the explicit inner-product bent function `splitDotProduct n` yields an
   unconditional `(k₁, k₂, 2 ^ ((n + n % 2 - k₁ - k₂) / 2) / 2)` sumset extractor for every length
   `n` (`isSumsetExtractor_splitDotProduct`), extracting whenever `k₁ + k₂ > n + n % 2` (so
   `k₁ + k₂ > n` for every even `n`). On even length `n = 2 * r`, this threshold is exact:
   `splitDotProduct (2 * r)` fails to extract at `k₁ = k₂ = r`
   (`not_isSumsetExtractor_splitDotProduct_half`).

This module does **not** formalize [Li2023], ECCC TR23-023 revision 1, Theorem 7.13 (which achieves
logarithmic min-entropy `c(ε) log n`); that explicit low-entropy construction remains open in #7793.

## Main definitions

* `Cslib.AffineDisperser.Li.splitDotProduct`: explicit inner-product bent function on even lengths
  `2 * r` (and its linear-last-bit extension on odd lengths `2 * r + 1`).

## Main results

* `Cslib.AffineDisperser.Li.IsSumsetExtractor.symm`, `.mono`, `.comp_add_right`,
  `.comp_linearEquiv`, `.dist_le_of_isSource`: basic closure and robustness properties.
* `Cslib.AffineDisperser.Li.isSumsetExtractor_iff_flat`: reduction to flat sources of sizes
  `2 ^ k₁` and `2 ^ k₂`.
* `Cslib.AffineDisperser.Li.max_le_minEntropy_sumset`: adding an independent source preserves
  min-entropy.
* `Cslib.AffineDisperser.Li.isTwoSourceExtractor_append_of_isSumsetExtractor`: a sumset extractor on
  `BitString (n₁ + n₂)` yields a two-source extractor via `Fin.append`.
* `Cslib.AffineDisperser.Li.bias_sumset`: `bias (A + B) S = bias A S * bias B S`.
* `Cslib.AffineDisperser.Li.dist_map_sumset_bool_le_of_fourierCoeff_le`: Fourier-norm sumset
  extraction bound.
* `Cslib.AffineDisperser.Li.abs_fourierCoeff_splitDotProduct_le`,
  `Cslib.AffineDisperser.Li.isSumsetExtractor_splitDotProduct`,
  `Cslib.AffineDisperser.Li.not_isSumsetExtractor_splitDotProduct_half`: unconditional explicit
  high-entropy sumset extractor and exactness of its `k₁ + k₂ > n` threshold.

## References

* [B. Chor and O. Goldreich, *Unbiased Bits from Sources of Weak Randomness and Probabilistic
  Communication Complexity*][ChorGoldreich1988]
* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023],
  ECCC TR23-023 revision 1, Definition 1.1 (p. 1) and Theorem 7.13 (p. 36)
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Chapter 6 (locator not verified against primary PDF)
-/

public section

namespace Cslib.AffineDisperser.Li

open Cslib.BitString Cslib.Probability Cslib.Probability.PMF Finset
open scoped NNReal

/-! ### Structural properties of `IsSumsetExtractor` -/

section Structure

variable {n m : ℕ} {ext : BitString n → BitString m} {k₁ k₂ k₁' k₂' : ℕ} {ε ε' : ℝ}

/-- Independent sumset distribution is commutative. -/
private theorem sumset_comm {n : ℕ} (A B : PMF (BitString n)) :
    (A.bind fun a => B.map fun b => a + b) = B.bind fun b => A.map fun a => b + a := by
  simp only [PMF.map, Function.comp_def]
  rw [PMF.bind_comm]
  refine congrArg (B.bind ·) (funext fun b => congrArg (A.bind ·) (funext fun a => ?_))
  rw [add_comm]

/-- Sumset extraction is symmetric in the two min-entropy parameters. -/
theorem IsSumsetExtractor.symm (hext : IsSumsetExtractor ext k₁ k₂ ε) :
    IsSumsetExtractor ext k₂ k₁ ε := fun A B hA hB => by
  rw [sumset_comm]
  exact hext B A hB hA

/-- Sumset extractors remain valid for larger min-entropies and larger error bounds. -/
theorem IsSumsetExtractor.mono (hext : IsSumsetExtractor ext k₁ k₂ ε)
    (hk₁ : k₁ ≤ k₁') (hk₂ : k₂ ≤ k₂') (hε : ε ≤ ε') :
    IsSumsetExtractor ext k₁' k₂' ε' :=
  fun A B hA hB =>
    (hext A B ((Nat.cast_le.mpr hk₁).trans hA) ((Nat.cast_le.mpr hk₂).trans hB)).trans hε

/-- Shifting the input of a sumset extractor by a constant preserves `IsSumsetExtractor`. -/
theorem IsSumsetExtractor.comp_add_right (hext : IsSumsetExtractor ext k₁ k₂ ε) (c : BitString n) :
    IsSumsetExtractor (fun x => ext (x + c)) k₁ k₂ ε := by
  intro A B hA hB
  have hmap : ((A.bind fun a => B.map fun b => a + b).map fun x => ext (x + c)) =
      ((A.bind fun a => (B.map fun b => b + c).map fun b' => a + b').map ext) := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, add_assoc]
  rw [hmap]
  exact hext A (B.map fun b => b + c) hA
    (le_minEntropy_map_of_injOn B (add_left_injective c).injOn hB)

/-- Precomposing a sumset extractor with a `Bool`-linear equivalence preserves
`IsSumsetExtractor`. -/
theorem IsSumsetExtractor.comp_linearEquiv (hext : IsSumsetExtractor ext k₁ k₂ ε)
    (e : BitString n ≃ₗ[Bool] BitString n) :
    IsSumsetExtractor (fun x => ext (e x)) k₁ k₂ ε := by
  intro A B hA hB
  have hmap : ((A.bind fun a => B.map fun b => a + b).map fun x => ext (e x)) =
      (((A.map e).bind fun a' => (B.map e).map fun b' => a' + b').map ext) := by
    simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, map_add]
  rw [hmap]
  exact hext (A.map e) (B.map e) (le_minEntropy_map_of_injOn A e.injective.injOn hA)
    (le_minEntropy_map_of_injOn B e.injective.injOn hB)

/-- **Smooth-source robustness**: a `(k₁, k₂, ε)` sumset extractor applied to a `(k₁, δ₁)`-source
and an independent `(k₂, δ₂)`-source outputs a distribution within `δ₁ + δ₂ + ε` of uniform. -/
theorem IsSumsetExtractor.dist_le_of_isSource (hext : IsSumsetExtractor ext k₁ k₂ ε)
    {A B : PMF (BitString n)} {δ₁ δ₂ : ℝ≥0}
    (hA : IsSource A k₁ δ₁) (hB : IsSource B k₂ δ₂) :
    dist ((A.bind fun a => B.map fun b => a + b).map ext)
      (PMF.uniformOfFintype (BitString m)) ≤ δ₁ + δ₂ + ε := by
  obtain ⟨A', hA', hdA⟩ := hA
  obtain ⟨B', hB', hdB⟩ := hB
  let sumA : PMF (BitString n) := A.bind fun a => B.map fun b => a + b
  let sumMid : PMF (BitString n) := A'.bind fun a => B.map fun b => a + b
  let sumB' : PMF (BitString n) := A'.bind fun a => B'.map fun b => a + b
  have h1 : dist (sumA.map ext) (sumMid.map ext) ≤ δ₁ :=
    (dist_map_le sumA sumMid ext).trans ((dist_bind_le A A' _).trans hdA)
  have h2 : dist (sumMid.map ext) (sumB'.map ext) ≤ δ₂ := by
    refine (dist_map_le sumMid sumB' ext).trans ?_
    change dist (A'.bind fun a => B.map fun b => a + b)
      (A'.bind fun a => B'.map fun b => a + b) ≤ δ₂
    rw [sumset_comm A' B, sumset_comm A' B']
    exact (dist_bind_le B B' _).trans hdB
  have h3 := hext A' B' hA' hB'
  have ht1 := dist_triangle (sumA.map ext) (sumMid.map ext) (PMF.uniformOfFintype (BitString m))
  have ht2 := dist_triangle (sumMid.map ext) (sumB'.map ext) (PMF.uniformOfFintype (BitString m))
  linarith

/-- **Flat-source characterization of sumset extractors**: `ext` is a `(k₁, k₂, ε)` sumset
extractor if and only if it extracts with error at most `ε` from the XOR-sum of every pair of
independent flat sources of sizes `2 ^ k₁` and `2 ^ k₂`. -/
theorem isSumsetExtractor_iff_flat :
    IsSumsetExtractor ext k₁ k₂ ε ↔
      ∀ (S₁ S₂ : Finset (BitString n)) (h₁ : S₁.card = 2 ^ k₁) (h₂ : S₂.card = 2 ^ k₂),
        dist (((PMF.uniformOfFinset S₁
              (card_ne_zero.mp (h₁.trans_ne (pow_ne_zero k₁ two_ne_zero)))).bind
            fun a => (PMF.uniformOfFinset S₂
              (card_ne_zero.mp (h₂.trans_ne (pow_ne_zero k₂ two_ne_zero)))).map
              fun b => a + b).map ext)
          (PMF.uniformOfFintype (BitString m)) ≤ ε := by
  constructor
  · intro hext S₁ S₂ h₁ h₂
    refine hext _ _ ?_ ?_
    · rw [minEntropy_uniformOfFinset, h₁, Nat.cast_pow, Nat.cast_ofNat, Real.logb_two_pow]
    · rw [minEntropy_uniformOfFinset, h₂, Nat.cast_pow, Nat.cast_ofNat, Real.logb_two_pow]
  · intro hflat A B hA hB
    obtain ⟨mixA, rfl⟩ := exists_eq_bind_uniformOfFinset_of_le_minEntropy A hA
    obtain ⟨mixB, rfl⟩ := exists_eq_bind_uniformOfFinset_of_le_minEntropy B hB
    have hrew :
        (((mixA.bind fun S₁ => PMF.uniformOfFinset S₁.val
            (card_ne_zero.mp (S₁.property.trans_ne (pow_ne_zero k₁ two_ne_zero)))).bind
          fun a => (mixB.bind fun S₂ => PMF.uniformOfFinset S₂.val
            (card_ne_zero.mp (S₂.property.trans_ne (pow_ne_zero k₂ two_ne_zero)))).map
            fun b => a + b).map ext) =
        mixA.bind fun S₁ => mixB.bind fun S₂ =>
          ((PMF.uniformOfFinset S₁.val
              (card_ne_zero.mp (S₁.property.trans_ne (pow_ne_zero k₁ two_ne_zero)))).bind
            fun a => (PMF.uniformOfFinset S₂.val
              (card_ne_zero.mp (S₂.property.trans_ne (pow_ne_zero k₂ two_ne_zero)))).map
              fun b => a + b).map ext := by
      simp only [PMF.bind_bind, PMF.map_bind]
      refine congrArg (mixA.bind ·) (funext fun S₁ => ?_)
      rw [PMF.bind_comm]
    rw [hrew]
    refine dist_bind_left_le_of_le mixA _ _ fun S₁ _ =>
      dist_bind_left_le_of_le mixB _ _ fun S₂ _ => hflat S₁.val S₂.val S₁.property S₂.property

/-- Adding an independent source on `BitString n` never decreases min-entropy. -/
theorem max_le_minEntropy_sumset (A B : PMF (BitString n)) :
    max (minEntropy A) (minEntropy B) ≤
      minEntropy (A.bind fun a => B.map fun b => a + b) := by
  have hright (P Q : PMF (BitString n)) :
      minEntropy Q ≤ minEntropy (P.bind fun a => Q.map fun b => a + b) := by
    exact le_minEntropy_bind P (fun a => Q.map fun b => a + b) fun a _ =>
      le_minEntropy_map_of_injOn Q (add_right_injective a).injOn le_rfl
  exact max_le (sumset_comm A B ▸ hright B A) (hright A B)

/-- **Sumset extractors yield two-source extractors**: evaluating a `(k₁, k₂, ε)` sumset extractor
on `Fin.append x y` yields a `(k₁, k₂, ε)` two-source extractor on `BitString n₁ × BitString n₂`. -/
theorem isTwoSourceExtractor_append_of_isSumsetExtractor {n₁ n₂ m k₁ k₂ : ℕ} {ε : ℝ}
    {ext : BitString (n₁ + n₂) → BitString m} (hext : IsSumsetExtractor ext k₁ k₂ ε) :
    IsTwoSourceExtractor (fun (x : BitString n₁) (y : BitString n₂) => ext (Fin.append x y))
      (k₁ : ℝ) (k₂ : ℝ) ε := by
  intro p q hp hq
  let padL : BitString n₁ → BitString (n₁ + n₂) := fun x => Fin.append x 0
  let padR : BitString n₂ → BitString (n₁ + n₂) := fun y => Fin.append 0 y
  have hpadL_inj : Function.Injective padL := fun x₁ x₂ h => funext fun i => by
    simpa only [padL, Fin.append_left] using congrFun h (Fin.castAdd n₂ i)
  have hpadR_inj : Function.Injective padR := fun y₁ y₂ h => funext fun j => by
    simpa only [padR, Fin.append_right] using congrFun h (Fin.natAdd n₁ j)
  have hadd (x : BitString n₁) (y : BitString n₂) : padL x + padR y = Fin.append x y := by
    funext i
    refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
      simp only [Pi.add_apply, padL, padR, Fin.append_left, Fin.append_right, Pi.zero_apply,
        add_zero, zero_add]
  have hlaw : (p.bind fun x => q.map fun y => ext (Fin.append x y)) =
      (((p.map padL).bind fun a => (q.map padR).map fun b => a + b).map ext) := by
    simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, hadd]
  rw [hlaw]
  exact hext (p.map padL) (q.map padR) (le_minEntropy_map_of_injOn p hpadL_inj.injOn hp)
    (le_minEntropy_map_of_injOn q hpadR_inj.injOn hq)

end Structure

/-! ### Fourier convolution for sumset sources -/

section Fourier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Fourier convolution on the Boolean cube**: the Walsh–Hadamard bias of the XOR-sum of two
independent distributions equals the product of their biases. -/
theorem bias_sumset (A B : PMF (ι → Bool)) (S : Finset ι) :
    bias (A.bind fun a => B.map fun b => a + b) S = bias A S * bias B S := by
  rw [bias, sum_bind_mul]
  simp only [sum_map_mul, chi_add]
  calc ∑ a, (A a).toReal * ∑ b, (B b).toReal * (chi ℝ S a * chi ℝ S b)
      = ∑ a, (A a).toReal * (chi ℝ S a * ∑ b, (B b).toReal * chi ℝ S b) :=
        Finset.sum_congr rfl fun a _ => congrArg ((A a).toReal * ·) (by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring)
    _ = (∑ a, (A a).toReal * chi ℝ S a) * ∑ b, (B b).toReal * chi ℝ S b := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring

/-- **Fourier-spectrum bound for sumset extraction**: if every Fourier coefficient of
`fun x => signVal (f x)` has magnitude at most `β`, then for independent sources `A, B` of
min-entropies at least `k₁` and `k₂`, `f (A + B)` is within `β * 2 ^ (|ι| - (k₁ + k₂) / 2) / 2`
of a uniform bit. -/
theorem dist_map_sumset_bool_le_of_fourierCoeff_le (f : (ι → Bool) → Bool) {β k₁ k₂ : ℝ}
    (hβ : ∀ S : Finset ι, |fourierCoeff (fun x => signVal (f x)) S| ≤ β)
    {A B : PMF (ι → Bool)} (hA : k₁ ≤ minEntropy A) (hB : k₂ ≤ minEntropy B) :
    dist ((A.bind fun a => B.map fun b => a + b).map f) (PMF.uniformOfFintype Bool) ≤
      β * 2 ^ ((Fintype.card ι : ℝ) - (k₁ + k₂) / 2) / 2 := by
  have hβ0 : 0 ≤ β := (abs_nonneg _).trans (hβ ∅)
  set P := A.bind fun a => B.map fun b => a + b
  rw [dist_map_uniformOfFintype_bool]
  have hexp : ∑ x, (P x).toReal * signVal (f x) =
      ∑ S, fourierCoeff (fun x => signVal (f x)) S * (bias A S * bias B S) := by
    calc ∑ x, (P x).toReal * signVal (f x)
        = ∑ x, (P x).toReal * ∑ S, fourierCoeff (fun y => signVal (f y)) S * chi ℝ S x :=
          Finset.sum_congr rfl fun x _ => by rw [sum_fourierCoeff_mul_chi]
      _ = ∑ S, fourierCoeff (fun y => signVal (f y)) S * ∑ x, (P x).toReal * chi ℝ S x := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ S, fourierCoeff (fun y => signVal (f y)) S * (bias A S * bias B S) :=
          Finset.sum_congr rfl fun S _ => by rw [← bias, bias_sumset]
  rw [hexp]
  gcongr
  have hsum (C : PMF (ι → Bool)) {k : ℝ} (hC : k ≤ minEntropy C) :
      ∑ S, bias C S ^ 2 ≤ (2 : ℝ) ^ Fintype.card ι * (2 : ℝ) ^ (-k) := by
    rw [sum_bias_sq]
    gcongr
    exact (collisionProbability_le_rpow_neg_minEntropy C).trans
      (Real.rpow_le_rpow_of_exponent_le one_le_two (neg_le_neg hC))
  have hsumA := hsum A hA
  have hsumB := hsum B hB
  have hcs_sq : (∑ S, |bias A S| * |bias B S|) ^ 2 ≤
      (2 ^ ((Fintype.card ι : ℝ) - (k₁ + k₂) / 2)) ^ 2 := by
    calc (∑ S, |bias A S| * |bias B S|) ^ 2
        ≤ (∑ S, |bias A S| ^ 2) * ∑ S, |bias B S| ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ S, bias A S ^ 2) * ∑ S, bias B S ^ 2 := by simp only [sq_abs]
      _ ≤ (2 ^ Fintype.card ι * 2 ^ (-k₁)) * (2 ^ Fintype.card ι * 2 ^ (-k₂)) := by
          gcongr
      _ = (2 ^ ((Fintype.card ι : ℝ) - (k₁ + k₂) / 2)) ^ 2 := by
          rw [← Real.rpow_natCast (2 : ℝ) (Fintype.card ι), ← Real.rpow_natCast _ 2,
            ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos,
            ← Real.rpow_add two_pos]
          congr 1
          push_cast
          ring
  have hcs : ∑ S, |bias A S| * |bias B S| ≤ 2 ^ ((Fintype.card ι : ℝ) - (k₁ + k₂) / 2) :=
    (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (by positivity) two_ne_zero).mp hcs_sq
  calc |∑ S, fourierCoeff (fun x => signVal (f x)) S * (bias A S * bias B S)|
      ≤ ∑ S, |fourierCoeff (fun x => signVal (f x)) S| * (|bias A S| * |bias B S|) := by
        simp only [← abs_mul]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S, β * (|bias A S| * |bias B S|) := by gcongr with S; exact hβ S
    _ ≤ β * 2 ^ ((Fintype.card ι : ℝ) - (k₁ + k₂) / 2) := by rw [← Finset.mul_sum]; gcongr

end Fourier

/-! ### Explicit bent-function sumset extractor (`splitDotProduct`) -/

section SplitDotProduct

/-- **Explicit inner-product bent function on `BitString n`**: on even length `n = 2 * r`, the
inner product `∑ i : Fin r, x i * x (r + i)` of the two halves; on odd length `n = 2 * r + 1`, the
same inner product XORed with the final bit `x (2 * r)`. -/
@[expose] def splitDotProduct (n : ℕ) (x : BitString n) : Bool :=
  (∑ i : Fin (n / 2), x ⟨i.val, by omega⟩ * x ⟨n / 2 + i.val, by omega⟩) +
    if h : n % 2 = 1 then x ⟨2 * (n / 2), by omega⟩ else false

/-- Split `Fin n` into `Fin (n / 2) ⊕ Fin (n / 2) ⊕ Fin (n % 2)`. -/
private def splitFinEquiv (n : ℕ) :
    Fin n ≃ (Fin (n / 2) ⊕ Fin (n / 2)) ⊕ Fin (n % 2) where
  toFun i :=
    if h1 : i.val < n / 2 then Sum.inl (Sum.inl ⟨i.val, h1⟩)
    else if h2 : i.val < 2 * (n / 2) then Sum.inl (Sum.inr ⟨i.val - n / 2, by omega⟩)
    else Sum.inr ⟨i.val - 2 * (n / 2), by omega⟩
  invFun
    | Sum.inl (Sum.inl j) => ⟨j.val, by omega⟩
    | Sum.inl (Sum.inr j) => ⟨n / 2 + j.val, by omega⟩
    | Sum.inr k => ⟨2 * (n / 2) + k.val, by omega⟩
  left_inv i := by
    by_cases h1 : i.val < n / 2
    · simp only [h1, ↓reduceDIte]
    · by_cases h2 : i.val < 2 * (n / 2)
      · simp only [h1, h2, ↓reduceDIte]
        ext; dsimp only; omega
      · simp only [h1, h2, ↓reduceDIte]
        ext; dsimp only; omega
  right_inv x := by
    rcases x with (j | j) | k
    · simp [j.isLt]
    · have h1 : ¬ n / 2 + j.val < n / 2 := by omega
      have h2 : n / 2 + j.val < 2 * (n / 2) := by have := j.isLt; omega
      simp only [h1, h2, ↓reduceDIte]
      congr 2; ext; dsimp only; omega
    · have h1 : ¬ 2 * (n / 2) + k.val < n / 2 := by omega
      have h2 : ¬ 2 * (n / 2) + k.val < 2 * (n / 2) := by omega
      simp only [h1, h2, ↓reduceDIte]
      congr 1; ext; dsimp only; omega

/-- The bit-string equivalence corresponding to `splitFinEquiv`. -/
private def splitBitEquiv (n : ℕ) :
    BitString n ≃ (BitString (n / 2) × BitString (n / 2)) × BitString (n % 2) :=
  ((splitFinEquiv n).arrowCongr (Equiv.refl Bool)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ Bool).trans
      (Equiv.prodCongr (Equiv.sumArrowEquivProdArrow _ _ Bool) (Equiv.refl _)))

private theorem splitBitEquiv_symm_left (n : ℕ)
    (a b : BitString (n / 2)) (c : BitString (n % 2)) (i : Fin (n / 2)) :
    (splitBitEquiv n).symm ((a, b), c) ⟨i.val, by omega⟩ = a i := by
  have heq : (⟨i.val, by omega⟩ : Fin n) = (splitFinEquiv n).symm (Sum.inl (Sum.inl i)) := rfl
  rw [heq]
  simp [splitBitEquiv]

private theorem splitBitEquiv_symm_right (n : ℕ)
    (a b : BitString (n / 2)) (c : BitString (n % 2)) (i : Fin (n / 2)) :
    (splitBitEquiv n).symm ((a, b), c) ⟨n / 2 + i.val, by omega⟩ = b i := by
  have heq :
      (⟨n / 2 + i.val, by omega⟩ : Fin n) = (splitFinEquiv n).symm (Sum.inl (Sum.inr i)) := rfl
  rw [heq]
  simp [splitBitEquiv]

private theorem splitBitEquiv_symm_rem (n : ℕ)
    (a b : BitString (n / 2)) (c : BitString (n % 2)) (k : Fin (n % 2)) :
    (splitBitEquiv n).symm ((a, b), c) ⟨2 * (n / 2) + k.val, by omega⟩ = c k := by
  have heq : (⟨2 * (n / 2) + k.val, by omega⟩ : Fin n) = (splitFinEquiv n).symm (Sum.inr k) := rfl
  rw [heq]
  simp [splitBitEquiv]

private theorem splitDotProduct_splitBitEquiv_symm (n : ℕ)
    (a b : BitString (n / 2)) (c : BitString (n % 2)) :
    splitDotProduct n ((splitBitEquiv n).symm ((a, b), c)) =
      (a ⬝ᵥ b) + if h : n % 2 = 1 then c ⟨0, by omega⟩ else false := by
  unfold splitDotProduct
  congr 1
  · simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [splitBitEquiv_symm_left, splitBitEquiv_symm_right]
  · split_ifs with h
    · have h0 := splitBitEquiv_symm_rem n a b c ⟨0, by omega⟩
      simpa only [add_zero] using h0
    · rfl

/-- Exact Walsh–Hadamard transform of the inner-product bent function on
`BitString r × BitString r`: every Fourier coefficient has absolute value `2⁻¹ ^ r`. -/
private theorem abs_sum_signVal_dotProduct_mul_chi (r : ℕ) (S₁ S₂ : Finset (Fin r)) :
    |∑ p : BitString r × BitString r,
        signVal (p.1 ⬝ᵥ p.2) * (chi ℝ S₁ p.1 * chi ℝ S₂ p.2)| = 2 ^ r := by
  let u₁ : BitString r := fun i => decide (i ∈ S₁)
  let u₂ : BitString r := fun i => decide (i ∈ S₂)
  have hchi (T : Finset (Fin r)) (u : BitString r) (hu : ∀ i, u i = decide (i ∈ T))
      (x : BitString r) : chi ℝ T x = signVal (u ⬝ᵥ x) := by
    rw [signVal_dotProduct]
    congr 1
    ext i
    simp [hu]
  have hsum : (∑ p : BitString r × BitString r,
      signVal (p.1 ⬝ᵥ p.2) * (chi ℝ S₁ p.1 * chi ℝ S₂ p.2)) =
      2 ^ r * signVal (u₂ ⬝ᵥ u₁) := by
    rw [Fintype.sum_prod_type_right]
    have hinner (y : BitString r) :
        (∑ x : BitString r, signVal (x ⬝ᵥ y) * (chi ℝ S₁ x * chi ℝ S₂ y)) =
          (if y + u₁ = 0 then (2 : ℝ) ^ r else 0) * signVal (u₂ ⬝ᵥ y) := by
      have hterm (x : BitString r) :
          signVal (x ⬝ᵥ y) * (chi ℝ S₁ x * chi ℝ S₂ y) =
            (if (y + u₁) ⬝ᵥ x then (-1 : ℝ) else 1) * signVal (u₂ ⬝ᵥ y) := by
        rw [hchi S₁ u₁ fun _ => rfl, hchi S₂ u₂ fun _ => rfl, ← mul_assoc, ← signVal_xor,
          ← Bool.add_eq_xor, dotProduct_comm x y,
          ← add_dotProduct]
        cases (y + u₁) ⬝ᵥ x <;> simp [signVal]
      simp_rw [hterm]
      rw [← Finset.sum_mul, sum_ite_dotProduct (R := ℝ) (y + u₁), Fintype.card_fin]
    simp_rw [hinner]
    rw [Finset.sum_eq_single u₁]
    · rw [BitString.add_self, ite_eq_left rfl]
    · intro y _ hy
      have hne : y + u₁ ≠ 0 := fun h => hy (by
        simpa [add_assoc, BitString.add_self] using congrArg (· + u₁) h)
      rw [ite_eq_right hne, zero_mul]
    · exact fun h => absurd (Finset.mem_univ u₁) h
  rw [hsum, abs_mul, abs_of_nonneg (by positivity), abs_signVal, mul_one]

/-- Every Fourier coefficient of `splitDotProduct n` has magnitude at most `2⁻¹ ^ (n / 2)`
(and on even length `n = 2 * r`, exact magnitude `2⁻¹ ^ r`, i.e., `splitDotProduct (2 * r)` is a
bent function). -/
theorem abs_fourierCoeff_splitDotProduct_le (n : ℕ) (S : Finset (Fin n)) :
    |fourierCoeff (fun x => signVal (splitDotProduct n x)) S| ≤ (2⁻¹ : ℝ) ^ (n / 2) := by
  let S₁ : Finset (Fin (n / 2)) := Finset.univ.filter fun j => (⟨j.val, by omega⟩ : Fin n) ∈ S
  let S₂ : Finset (Fin (n / 2)) :=
    Finset.univ.filter fun j => (⟨n / 2 + j.val, by omega⟩ : Fin n) ∈ S
  let S₃ : Finset (Fin (n % 2)) :=
    Finset.univ.filter fun k => (⟨2 * (n / 2) + k.val, by omega⟩ : Fin n) ∈ S
  have hchi (a b : BitString (n / 2)) (c : BitString (n % 2)) :
      chi ℝ S ((splitBitEquiv n).symm ((a, b), c)) =
        (chi ℝ S₁ a * chi ℝ S₂ b) * chi ℝ S₃ c := by
    rw [chi_eq_prod_univ,
      ← Fintype.prod_equiv (splitFinEquiv n).symm
        (fun idx => if (splitFinEquiv n).symm idx ∈ S then
          (-1 : ℝ) ^ ((splitBitEquiv n).symm ((a, b), c) ((splitFinEquiv n).symm idx)).toNat
        else 1)
        (fun i => if i ∈ S then (-1 : ℝ) ^ ((splitBitEquiv n).symm ((a, b), c) i).toNat else 1)
        (fun _ => rfl),
      Fintype.prod_sum_type, Fintype.prod_sum_type]
    have hbranch {ι : Type} [Fintype ι] [DecidableEq ι] (emb : ι → Fin n) (v : ι → Bool)
        (T : Finset ι) (hT : ∀ j, emb j ∈ S ↔ j ∈ T)
        (hv : ∀ j, (splitBitEquiv n).symm ((a, b), c) (emb j) = v j) :
        (∏ j : ι, if emb j ∈ S then
            (-1 : ℝ) ^ ((splitBitEquiv n).symm ((a, b), c) (emb j)).toNat else 1) =
          chi ℝ T v := by
      rw [chi_eq_prod_univ]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hv j]
      by_cases hj : j ∈ T <;> simp [hT j, hj]
    congr 1
    · congr 1
      · exact hbranch (fun j => (splitFinEquiv n).symm (Sum.inl (Sum.inl j))) a S₁
          (fun j => by simp [S₁, splitFinEquiv]) (fun j => by simp [splitBitEquiv])
      · exact hbranch (fun j => (splitFinEquiv n).symm (Sum.inl (Sum.inr j))) b S₂
          (fun j => by simp [S₂, splitFinEquiv]) (fun j => by simp [splitBitEquiv])
    · exact hbranch (fun k => (splitFinEquiv n).symm (Sum.inr k)) c S₃
        (fun k => by simp [S₃, splitFinEquiv]) (fun k => by simp [splitBitEquiv])
  rw [fourierCoeff_eq_sum, Fintype.card_fin,
    ← Fintype.sum_equiv (splitBitEquiv n).symm
      (fun q => signVal (splitDotProduct n ((splitBitEquiv n).symm q)) *
        chi ℝ S ((splitBitEquiv n).symm q))
      (fun x => signVal (splitDotProduct n x) * chi ℝ S x)
      (fun _ => rfl),
    Fintype.sum_prod_type]
  have hfactor :
      (∑ p : BitString (n / 2) × BitString (n / 2), ∑ c : BitString (n % 2),
        signVal (splitDotProduct n ((splitBitEquiv n).symm (p, c))) *
          chi ℝ S ((splitBitEquiv n).symm (p, c))) =
      (∑ p : BitString (n / 2) × BitString (n / 2),
        signVal (p.1 ⬝ᵥ p.2) * (chi ℝ S₁ p.1 * chi ℝ S₂ p.2)) *
      (∑ c : BitString (n % 2),
        signVal (if h : n % 2 = 1 then c ⟨0, by omega⟩ else false) * chi ℝ S₃ c) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [splitDotProduct_splitBitEquiv_symm, hchi, Bool.add_eq_xor, signVal_xor]
    ring
  rw [hfactor, abs_div, abs_mul, abs_sum_signVal_dotProduct_mul_chi,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n)]
  have htail : |∑ c : BitString (n % 2),
      signVal (if h : n % 2 = 1 then c ⟨0, by omega⟩ else false) * chi ℝ S₃ c| ≤
      2 ^ (n % 2) :=
    (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul, abs_signVal, abs_chi])
  calc _ ≤ (2 : ℝ) ^ (n / 2) * 2 ^ (n % 2) / 2 ^ n := by gcongr
    _ = (2⁻¹ : ℝ) ^ (n / 2) := by
        have hdecomp : n = n / 2 + n / 2 + n % 2 := by omega
        conv_lhs => rhs; rw [hdecomp]
        rw [pow_add, pow_add, inv_pow]
        field_simp

/-- **Unconditional explicit high-entropy sumset extractor**: for every length `n` and min-entropies
`k₁, k₂`, `splitDotProduct n` is a `(k₁, k₂, 2 ^ ((n + n % 2 - k₁ - k₂) / 2) / 2)` sumset
extractor. On even lengths `n = 2 * r`, the error is `2 ^ ((n - k₁ - k₂) / 2) / 2`, which is
strictly below `1 / 2` whenever `k₁ + k₂ > n`.

This is an unconditional high-entropy sumset extractor (compare [ChorGoldreich1988] for two-source
inner product), not [Li2023] Theorem 7.13 (which requires logarithmic entropy `c(ε) log n` and
remains open in #7793). -/
theorem isSumsetExtractor_splitDotProduct (n k₁ k₂ : ℕ) :
    IsSumsetExtractor (fun x : BitString n => fun _ : Fin 1 => splitDotProduct n x) k₁ k₂
      (2 ^ (((n + n % 2 : ℕ) - (k₁ : ℝ) - k₂) / 2) / 2) := by
  intro A B hA hB
  let e : BitString 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool
  have hlaw : ((A.bind fun a => B.map fun b => a + b).map
      fun x : BitString n => fun _ : Fin 1 => splitDotProduct n x) =
      ((A.bind fun a => B.map fun b => a + b).map (splitDotProduct n)).map e.symm := by
    rw [PMF.map_comp]
    rfl
  have hunif : PMF.uniformOfFintype (BitString 1) =
      (PMF.uniformOfFintype Bool).map e.symm :=
    (PMF.uniformOfFintype_map_equiv e.symm).symm
  rw [hlaw, hunif]
  refine (dist_map_le _ _ e.symm).trans ?_
  have hbound := dist_map_sumset_bool_le_of_fourierCoeff_le (splitDotProduct n)
    (abs_fourierCoeff_splitDotProduct_le n) hA hB
  rw [Fintype.card_fin] at hbound
  refine hbound.trans_eq ?_
  congr 1
  rw [inv_pow, ← Real.rpow_natCast (2 : ℝ) (n / 2), ← Real.rpow_neg zero_le_two,
    ← Real.rpow_add two_pos]
  congr 1
  have hdiv : (n : ℝ) = 2 * (n / 2 : ℕ) + (n % 2 : ℕ) := by
    exact_mod_cast (Nat.div_add_mod n 2).symm
  push_cast
  linarith

/-- **Exactness of the `k₁ + k₂ > n` threshold for `splitDotProduct`**: on even length `2 * r`,
two independent copies of the uniform distribution on strings supported on the first `r` bits each
have min-entropy `r`, yet their XOR-sum also vanishes on the last `r` bits, so `splitDotProduct`
is identically `false` on it and fails to extract with any error `< 1 / 2`. -/
theorem not_isSumsetExtractor_splitDotProduct_half (r : ℕ) {ε : ℝ} (hε : ε < 1 / 2) :
    ¬ IsSumsetExtractor (fun x : BitString (2 * r) => fun _ : Fin 1 => splitDotProduct (2 * r) x)
      r r ε := by
  intro hext
  let pad : BitString r → BitString (2 * r) := fun u i =>
    if h : i.val < r then u ⟨i.val, h⟩ else false
  have hpad_inj : Function.Injective pad := fun u₁ u₂ h => funext fun j => by
    have := congrFun h ⟨j.val, by omega⟩
    simpa only [pad, j.isLt, ↓reduceDIte] using this
  let A : PMF (BitString (2 * r)) := (PMF.uniformOfFintype (BitString r)).map pad
  have hminA : (r : ℝ) ≤ minEntropy A := le_minEntropy_map_of_injOn _ hpad_inj.injOn
    (minEntropy_uniformOfFintype.trans (BitString.logb_card r)).ge
  have hzero (u v : BitString r) : splitDotProduct (2 * r) (pad u + pad v) = false := by
    unfold splitDotProduct
    have hmod : ¬ (2 * r) % 2 = 1 := by omega
    rw [dite_eq_right hmod, ← Bool.zero_eq_false, add_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hge : ¬ (2 * r) / 2 + i.val < r := by omega
    simp only [Pi.add_apply, pad, dite_eq_right hge, ← Bool.zero_eq_false, add_zero, mul_zero]
  have hconst : ((A.bind fun a => A.map fun b => a + b).map
      fun x : BitString (2 * r) => fun _ : Fin 1 => splitDotProduct (2 * r) x) =
      PMF.pure (fun _ : Fin 1 => false) := by
    simp only [A, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, hzero]
    have hinner : (PMF.uniformOfFintype (BitString r)).map
        (Function.const (BitString r) (fun _ : Fin 1 => false)) =
        PMF.pure (fun _ : Fin 1 => false) := PMF.map_const ..
    change ((PMF.uniformOfFintype (BitString r)).bind fun _ =>
      (PMF.uniformOfFintype (BitString r)).map
        (Function.const (BitString r) (fun _ : Fin 1 => false))) = _
    rw [hinner, PMF.bind_const]
  have hdist := hext A A hminA hminA
  rw [hconst] at hdist
  let e : BitString 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool
  have h1 := dist_map_le (PMF.pure (fun _ : Fin 1 => false))
    (PMF.uniformOfFintype (BitString 1)) e
  have hpure_map : (PMF.pure (fun _ : Fin 1 => false)).map e = PMF.pure false := by
    simp [PMF.map, e]
  rw [hpure_map, PMF.uniformOfFintype_map_equiv e, dist_uniformOfFintype_bool] at h1
  have hfalse : ((PMF.pure false) true).toReal = 0 := by simp [PMF.pure_apply]
  rw [hfalse] at h1
  norm_num at h1
  linarith

end SplitDotProduct

end Cslib.AffineDisperser.Li
