/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.Data.BitString.Threshold
import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Polynomial threshold functions and Chow's theorem

A Boolean function `f` is a *polynomial threshold function over a family `T` of sets* if, read as
signs `F = (-1) ^ f`, it is the sign of a real function `p` on the cube that vanishes nowhere and
whose Fourier coefficients vanish outside `T` (`BitString.IsPTFOn`); it is a *polynomial threshold
function of degree at most `k`* if `T` is the family of sets of at most `k` coordinates
(`BitString.IsPTF`) [O'Donnell, Definition 5.4][ODonnell2014]. "The sign of `p`" is written
`0 < F(x) p(x)` for every `x`.

The book writes `f = sgn(p)` with `sgn(0) = 1`, and insists that `p` vanish nowhere in the proof
of Chow's theorem [O'Donnell, Theorem 5.1][ODonnell2014]. For degree at most `k` the two notions
agree, since adding a small constant to `p` removes its zeros without changing its signs or its
degree (this equivalence is not proved here); at `k = 1` they are the *linear threshold
functions* `sgn(a₀ + a₁ x₁ + ⋯ + aₙ xₙ)` [O'Donnell, Definition 2.5][ODonnell2014]. For a general
family `T` not containing `∅` the constant cannot be adjusted, and `IsPTFOn T` is strictly
narrower than the book's notion: `x₁ + x₂` represents a function over `{{1}, {2}}` that no such `p`
without zeros represents.

Since `F p = |p| ≥ G p` pointwise for any Boolean `G`, with equality only where `G = F` because
`p` vanishes nowhere, Plancherel's identity shows that a polynomial threshold function over `T` is
determined, among all Boolean functions, by its Fourier coefficients on `T` (**Chow's theorem**,
`BitString.IsPTFOn.eq_of_fourierCoeff_eq`). For degree at most `k` this is
[O'Donnell, Theorems 5.1 and 5.8][ODonnell2014] (`BitString.IsPTF.eq_of_fourierCoeff_eq`); for a
general family it is a generalization that uses the absence of zeros.

The threshold function `Th^n_j`, and with it majority, AND, OR and the constants, is the sign of
`j - 1 / 2 - weight x`, so it is a linear threshold function (`BitString.isPTF_one_threshold`);
so is each literal `±χᵢ` (`BitString.isPTF_one_xor`) [O'Donnell, Exercise 2.2][ODonnell2014].
Composing with `w ↦ z + w ∘ π`, which negates the inputs selected by `z` and identifies those
with the same image under `π`, keeps every output bit of degree at most one, so it preserves
polynomial threshold functions of degree at most `k` (`BitString.IsPTF.comp_add_comp`), in
particular linear threshold functions [O'Donnell, Section 5.5][ODonnell2014].

If `F p ≥ 0` everywhere for some nonzero `p` with Fourier coefficients vanishing outside `T`, then
comparing `𝔼 |p| = ∑_{S ∈ T} F̂(S) p̂(S)` with `|p̂(S)| ≤ 𝔼 |p|` shows that the Fourier coefficients
of `F` on `T` have absolute values summing to at least one
(`BitString.one_le_sum_abs_fourierCoeff_of_nonneg_mul`) [O'Donnell, Theorem 5.10][ODonnell2014];
its proof allows zeros of `p`, so this covers every representation `f = sgn(p)` with `sgn(0) = 1`
and `p` not identically zero, for every family. The book leaves `p ≢ 0` implicit; it is needed,
since for `T = ∅`, `p = 0` and the constant `F = 1` the sum is zero. The case of all
sets is `BitString.one_le_sum_abs_fourierCoeff_signVal`.

## Main definitions

* `Cslib.BitString.IsPTFOn`, `Cslib.BitString.IsPTF`: polynomial threshold functions over a
  family of sets and of bounded degree.

## Main results

* `Cslib.BitString.isPTF_iff`: the degree form with `∀ S, k < #S → p̂(S) = 0`.
* `Cslib.BitString.isPTFOn_of_fourierCoeff_eq_zero`, `Cslib.BitString.isPTF_card`: a Boolean
  function whose coefficients vanish outside `T` is a polynomial threshold function over `T`, so
  every Boolean function on `n` coordinates has degree at most `n`.
* `Cslib.BitString.isPTF_one_threshold`, `Cslib.BitString.isPTF_one_xor`: threshold functions,
  among them majority, AND, OR and the constants, and the literals `±χᵢ` are linear threshold
  functions.
* `Cslib.BitString.IsPTF.comp_add_comp`: negating and identifying input variables preserves
  polynomial threshold functions of degree at most `k`.
* `Cslib.BitString.IsPTFOn.eq_of_fourierCoeff_eq`, `Cslib.BitString.IsPTF.eq_of_fourierCoeff_eq`:
  Chow's theorem.
* `Cslib.BitString.one_le_sum_abs_fourierCoeff_of_nonneg_mul`,
  `Cslib.BitString.IsPTFOn.one_le_sum_abs_fourierCoeff`: the Fourier coefficients on the family
  have absolute values summing to at least one.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*}

/-- Where `f`, read as signs, times `p` is nonnegative, it is `|p|`. -/
theorem signVal_mul_eq_abs {f : (ι → Bool) → Bool} {p : (ι → Bool) → ℝ}
    (hp : ∀ x, 0 ≤ signVal (f x) * p x) (x : ι → Bool) : signVal (f x) * p x = |p x| := by
  rw [← abs_of_nonneg (hp x), abs_mul, abs_signVal, one_mul]

variable [Fintype ι] [DecidableEq ι]

/-- `f` is a polynomial threshold function over the family `T` of sets: read as signs, it is the
sign of a real function `p` on the cube, vanishing nowhere, whose Fourier coefficients vanish
outside `T` [O'Donnell, Definition 5.4][ODonnell2014]. For a family not containing `∅` this is
narrower than the book's `f = sgn(p)` with `sgn(0) = 1`. -/
@[expose] def IsPTFOn (T : Finset (Finset ι)) (f : (ι → Bool) → Bool) : Prop :=
  ∃ p : (ι → Bool) → ℝ, (∀ S ∉ T, fourierCoeff p S = 0) ∧ ∀ x, 0 < signVal (f x) * p x

/-- `f` is a polynomial threshold function of degree at most `k`: the sign of a real function of
Fourier degree at most `k` that vanishes nowhere [O'Donnell, Definition 5.4][ODonnell2014],
equivalently, after adding a small constant, of any real function of degree at most `k`. At
`k = 1` these are the linear threshold functions [O'Donnell, Definition 2.5][ODonnell2014]. -/
@[expose] def IsPTF (k : ℕ) (f : (ι → Bool) → Bool) : Prop :=
  IsPTFOn {S | #S ≤ k} f

/-- A polynomial threshold function of degree at most `k`, with the degree bound on the Fourier
coefficients. -/
theorem isPTF_iff {k : ℕ} {f : (ι → Bool) → Bool} :
    IsPTF k f ↔ ∃ p : (ι → Bool) → ℝ,
      (∀ S : Finset ι, k < #S → fourierCoeff p S = 0) ∧ ∀ x, 0 < signVal (f x) * p x := by
  simp only [IsPTF, IsPTFOn, mem_filter, mem_univ, true_and, not_le]

/-- Enlarging the family preserves being a polynomial threshold function. -/
theorem IsPTFOn.mono {T U : Finset (Finset ι)} {f : (ι → Bool) → Bool} (hTU : T ⊆ U)
    (hf : IsPTFOn T f) : IsPTFOn U f :=
  let ⟨p, hpT, hp⟩ := hf
  ⟨p, fun S hS => hpT S fun h => hS (hTU h), hp⟩

/-- Raising the degree bound preserves being a polynomial threshold function. -/
theorem IsPTF.mono {k l : ℕ} {f : (ι → Bool) → Bool} (hkl : k ≤ l) (hf : IsPTF k f) :
    IsPTF l f :=
  IsPTFOn.mono (fun S hS => mem_filter.2 ⟨mem_univ S, (mem_filter.1 hS).2.trans hkl⟩) hf

/-- The negation of a polynomial threshold function over `T` is one, the sign of `-p`. -/
theorem IsPTFOn.not {T : Finset (Finset ι)} {f : (ι → Bool) → Bool} (hf : IsPTFOn T f) :
    IsPTFOn T fun x => !f x := by
  obtain ⟨p, hpT, hp⟩ := hf
  refine ⟨fun x => -p x, fun S hS => ?_, fun x => ?_⟩
  · simp only [fourierCoeff, neg_mul, expect_neg_distrib, neg_eq_zero]
    exact hpT S hS
  · rw [signVal_not, neg_mul_neg]
    exact hp x

/-- **Negating and identifying input variables preserves polynomial threshold functions**: if `f`
is a polynomial threshold function of degree at most `k`, then so is `w ↦ f (z + w ∘ π)` for every
string `z` of negations and every map `π` of the coordinates of `f` to those of `w`
[O'Donnell, Section 5.5][ODonnell2014]. Its polynomial is `p` composed with the same map, each
of whose output bits has degree at most one. -/
theorem IsPTF.comp_add_comp {κ : Type*} [Fintype κ] [DecidableEq κ] {k : ℕ}
    {f : (ι → Bool) → Bool} (hf : IsPTF k f) (z : ι → Bool) (π : ι → κ) :
    IsPTF k fun w : κ → Bool => f (z + fun i => w (π i)) := by
  obtain ⟨p, hpdeg, hp⟩ := isPTF_iff.1 hf
  refine isPTF_iff.2 ⟨fun w => p (z + fun i => w (π i)), fun S hS => ?_, fun w => hp _⟩
  refine fourierCoeff_eq_zero_of_mem_lowDegree (comp_mem_lowDegree (fun i => ?_)
    (mem_lowDegree_iff_fourierCoeff_eq_zero.2 hpdeg)) hS
  simp only [Pi.add_apply, Bool.add_eq_xor]
  cases z i
  · simpa only [Bool.false_xor] using bitVal_mem_lowDegree (R := ℝ) (π i)
  · have h₁ : (fun w : κ → Bool => bitVal ℝ (true ^^ w (π i))) =
        1 - fun w : κ → Bool => bitVal ℝ (w (π i)) :=
      funext fun w => by rw [Bool.true_xor, bitVal_not, Pi.sub_apply, Pi.one_apply]
    rw [h₁]
    exact one_sub_mem_lowDegree (bitVal_mem_lowDegree (π i))

/-- **Threshold functions are linear threshold functions**: `Th^n_j` holds exactly when
`j - 1 / 2 - weight x` is negative, and the weight has degree one. This covers majority
(`majority n = Th^n_⌈n/2⌉`), AND (`threshold n n`), OR (`threshold n 1`) and the constants
(`threshold n 0` and `threshold n (n + 1)`) among the examples of
[O'Donnell, Exercise 2.2][ODonnell2014]; the literals are `BitString.isPTF_one_xor`. -/
theorem isPTF_one_threshold (n j : ℕ) : IsPTF 1 (threshold n j) := by
  refine isPTF_iff.2 ⟨fun x => (j : ℝ) - 1 / 2 - weight x, fun S hS => ?_, fun x => ?_⟩
  · exact fourierCoeff_eq_zero_of_mem_lowDegree
      (sub_mem (const_mem_lowDegree 1 _) weight_mem_lowDegree) hS
  · rw [threshold_apply]
    by_cases h : j ≤ weight x
    · have : (j : ℝ) ≤ weight x := by exact_mod_cast h
      simp only [h, decide_true, signVal_true]
      linarith
    · have : (weight x : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : weight x + 1 ≤ j)
      simp only [h, decide_false, signVal_false]
      linarith

/-- A Boolean function whose Fourier coefficients, read as signs, vanish outside `T` is a
polynomial threshold function over `T`: the sign of itself. -/
theorem isPTFOn_of_fourierCoeff_eq_zero {T : Finset (Finset ι)} {f : (ι → Bool) → Bool}
    (h : ∀ S ∉ T, fourierCoeff (fun x => signVal (f x)) S = 0) : IsPTFOn T f :=
  ⟨_, h, fun x => by rw [signVal_mul_self]; exact one_pos⟩

/-- **Literals are linear threshold functions**: `x ↦ b ⊕ x_i`, read as signs, is `±χ_i`, which
has degree one, so it is the sign of itself. With `BitString.isPTF_one_threshold` this covers all
the examples of [O'Donnell, Exercise 2.2][ODonnell2014]. -/
theorem isPTF_one_xor (b : Bool) (i : ι) : IsPTF 1 fun x => b ^^ x i :=
  isPTFOn_of_fourierCoeff_eq_zero fun S hS => by
    rw [fourierCoeff_signVal_xor]
    refine ite_eq_right_iff.2 fun h => absurd ?_ hS
    subst h
    exact mem_filter.2 ⟨mem_univ _, (card_singleton i).le⟩

/-- Every Boolean function on `n` coordinates is a polynomial threshold function of degree at
most `n` [O'Donnell, Section 5.1, after Example 5.5][ODonnell2014]. -/
theorem isPTF_card (f : (ι → Bool) → Bool) : IsPTF (Fintype.card ι) f :=
  isPTFOn_of_fourierCoeff_eq_zero fun S hS =>
    absurd (mem_filter.2 ⟨mem_univ S, card_le_univ S⟩) hS

/-- Correlating with a function whose Fourier coefficients vanish outside `T` only involves the
coefficients on `T`. -/
theorem expect_mul_eq_sum_of_fourierCoeff_eq_zero {T : Finset (Finset ι)}
    {p : (ι → Bool) → ℝ} (hpT : ∀ S ∉ T, fourierCoeff p S = 0) (g : (ι → Bool) → ℝ) :
    𝔼 x, g x * p x = ∑ S ∈ T, fourierCoeff g S * fourierCoeff p S := by
  rw [expect_mul_eq_sum_fourierCoeff_mul]
  exact (sum_subset (subset_univ T) fun S _ hS => by rw [hpT S hS, mul_zero]).symm

/-- **Chow's theorem**: a polynomial threshold function over `T` is determined, among all Boolean
functions, by its Fourier coefficients on `T`. For the degree-`k` families this is
[O'Donnell, Theorems 5.1 and 5.8][ODonnell2014]; for a general family it generalizes them, using
that `p` vanishes nowhere. -/
theorem IsPTFOn.eq_of_fourierCoeff_eq {T : Finset (Finset ι)} {f g : (ι → Bool) → Bool}
    (hf : IsPTFOn T f)
    (hfg : ∀ S ∈ T, fourierCoeff (fun x => signVal (g x)) S =
      fourierCoeff (fun x => signVal (f x)) S) :
    g = f := by
  obtain ⟨p, hpT, hp⟩ := hf
  have hle (x : ι → Bool) : signVal (g x) * p x ≤ signVal (f x) * p x := by
    simpa only [signVal_mul_eq_abs (fun x => (hp x).le) x, abs_mul, abs_signVal, one_mul] using
      le_abs_self (signVal (g x) * p x)
  have heq : 𝔼 x, signVal (g x) * p x = 𝔼 x, signVal (f x) * p x := by
    simp only [expect_mul_eq_sum_of_fourierCoeff_eq_zero hpT]
    exact sum_congr rfl fun S hS => by rw [hfg S hS]
  funext x
  by_contra hx
  refine (expect_lt_expect (fun y _ => hle y) ⟨x, mem_univ x, ?_⟩).ne heq
  simpa only [Bool.eq_not_of_ne hx, signVal_not, neg_mul] using neg_lt_self (hp x)

/-- **Chow's theorem for polynomial threshold functions of degree at most `k`**: such a function
is determined, among all Boolean functions, by its Fourier coefficients of degree at most `k`; at
`k = 1`, a linear threshold function by its coefficients of degree at most one
[O'Donnell, Theorems 5.1 and 5.8][ODonnell2014]. -/
theorem IsPTF.eq_of_fourierCoeff_eq {k : ℕ} {f g : (ι → Bool) → Bool} (hf : IsPTF k f)
    (hfg : ∀ S : Finset ι, #S ≤ k → fourierCoeff (fun x => signVal (g x)) S =
      fourierCoeff (fun x => signVal (f x)) S) :
    g = f :=
  IsPTFOn.eq_of_fourierCoeff_eq hf fun S hS => hfg S (mem_filter.1 hS).2

/-- **The Fourier coefficients of a polynomial threshold function on its family**: if, read as
signs, `F p ≥ 0` everywhere for a nonzero real `p` whose Fourier coefficients vanish outside `T`,
then the Fourier coefficients of `F` on `T` have absolute values summing to at least one
[O'Donnell, Theorem 5.10][ODonnell2014]. The function `p` may vanish somewhere, so this covers
the book's `f = sgn(p)` with `sgn(0) = 1` for every family, provided `p` is not identically zero;
the book leaves that assumption implicit, and it is necessary: for `T = ∅`, `p = 0` and the
constant `F = 1` the sum is zero. -/
theorem one_le_sum_abs_fourierCoeff_of_nonneg_mul {T : Finset (Finset ι)}
    {f : (ι → Bool) → Bool} {p : (ι → Bool) → ℝ} (hpT : ∀ S ∉ T, fourierCoeff p S = 0)
    (hp₀ : p ≠ 0) (hp : ∀ x, 0 ≤ signVal (f x) * p x) :
    1 ≤ ∑ S ∈ T, |fourierCoeff (fun x => signVal (f x)) S| := by
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hp₀
  have hpos : 0 < 𝔼 x, |p x| :=
    expect_pos' (fun x _ => abs_nonneg _) ⟨x₀, mem_univ x₀, abs_pos.2 hx₀⟩
  have key : 𝔼 x, |p x| ≤ (∑ S ∈ T, |fourierCoeff (fun x => signVal (f x)) S|) * 𝔼 x, |p x| :=
    calc 𝔼 x, |p x| = 𝔼 x, signVal (f x) * p x :=
          expect_congr rfl fun x _ => (signVal_mul_eq_abs hp x).symm
      _ = ∑ S ∈ T, fourierCoeff (fun x => signVal (f x)) S * fourierCoeff p S :=
          expect_mul_eq_sum_of_fourierCoeff_eq_zero hpT _
      _ ≤ ∑ S ∈ T, |fourierCoeff (fun x => signVal (f x)) S| * 𝔼 x, |p x| :=
          sum_le_sum fun S _ => (le_abs_self _).trans <| (abs_mul _ _).trans_le <|
            mul_le_mul_of_nonneg_left (abs_fourierCoeff_le_expect_abs p S) (abs_nonneg _)
      _ = (∑ S ∈ T, |fourierCoeff (fun x => signVal (f x)) S|) * 𝔼 x, |p x| := (sum_mul ..).symm
  exact le_of_mul_le_mul_right (by rwa [one_mul]) hpos

/-- **The Fourier coefficients of a polynomial threshold function on its family** have absolute
values summing to at least one [O'Donnell, Theorem 5.10][ODonnell2014]. -/
theorem IsPTFOn.one_le_sum_abs_fourierCoeff {T : Finset (Finset ι)} {f : (ι → Bool) → Bool}
    (hf : IsPTFOn T f) : 1 ≤ ∑ S ∈ T, |fourierCoeff (fun x => signVal (f x)) S| := by
  obtain ⟨p, hpT, hp⟩ := hf
  refine one_le_sum_abs_fourierCoeff_of_nonneg_mul hpT ?_ fun x => (hp x).le
  rintro rfl
  simpa using hp (Classical.arbitrary _)

end Cslib.BitString
