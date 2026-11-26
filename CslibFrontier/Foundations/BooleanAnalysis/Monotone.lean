/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Foundations.BooleanAnalysis.Decomposition
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.NormNum

/-!
# Influences of monotone and unate Boolean functions

The derivative in `i` of a Boolean function read as signs takes the values `0` and `±1`, so its
square is its absolute value (`BitString.sq_derivative_signVal`). The coefficient of a function on
`{i}` is the average of its derivative in `i`, so for every Boolean function it is at most the
influence of `i` in absolute value (`BitString.abs_fourierCoeff_singleton_le_influence`). With the
order `false < true` on bits and the signs `signVal false = 1`, `signVal true = -1`, the derivative
of a monotone function is nonnegative, so its influences are its degree-one coefficients
(`BitString.influence_eq_fourierCoeff_singleton_of_monotone`)
[O'Donnell, Section 2.2][ODonnell2014]; for an antitone function they are their negatives.

A Boolean function is *unate in direction `i`* (`BitString.IsUnateIn`) if raising bit `i`
either never lowers its value or never raises it, and *unate* (`BitString.IsUnate`) if it is unate
in every direction [O'Donnell, Exercise 2.5][ODonnell2014]; monotone and antitone functions are
unate (`Monotone.isUnate`, `Antitone.isUnate`). The derivative in `i`, read as signs, has a
constant sign exactly when `f` is unate in direction `i`, that is, exactly when the influence of
`i`, the average of the absolute value of the derivative, equals the absolute value of the
coefficient on `{i}`, the average of the derivative
(`BitString.abs_fourierCoeff_singleton_eq_influence_iff`)
[O'Donnell, Exercise 2.5(a)][ODonnell2014].

The degree-one coefficients carry at most the variance
(`BitString.sum_fourierCoeff_singleton_sq_le`), so by the Cauchy–Schwarz inequality their absolute
values sum to at most `√(n σ²)` (`BitString.sq_sum_abs_fourierCoeff_singleton_le`). A unate
function on `n` coordinates with variance `σ²` therefore has total influence at most `√(n σ²)`
(`BitString.IsUnate.totalInfluence_le_sqrt_card_mul`), in particular at most `√n`
(`BitString.IsUnate.totalInfluence_le_sqrt_card`) [O'Donnell, Exercise 2.23][ODonnell2014]; so do
monotone and antitone functions (`BitString.totalInfluence_le_sqrt_card_mul_of_monotone`,
`BitString.totalInfluence_le_sqrt_card_of_monotone`). Linear threshold functions are unate
(`CslibFrontier.Foundations.BooleanAnalysis.Unate`).

## Main definitions

* `Cslib.BitString.IsUnateIn`, `Cslib.BitString.IsUnate`: unate functions.

## Main results

* `Monotone.isUnate`, `Antitone.isUnate`: monotone and antitone functions are unate.
* `Cslib.BitString.derivative_signVal_nonneg_iff`,
  `Cslib.BitString.derivative_signVal_nonpos_iff`: the derivative in `i`, read as signs, has a
  sign exactly where raising bit `i` moves the value in the corresponding direction.
* `Cslib.BitString.derivative_signVal_nonneg_of_monotone`,
  `Cslib.BitString.derivative_signVal_nonpos_of_antitone`: the sign of the derivatives of a
  monotone or antitone function.
* `Cslib.BitString.abs_fourierCoeff_singleton_le_influence`: a degree-one coefficient is at most
  the influence in absolute value.
* `Cslib.BitString.influence_eq_fourierCoeff_singleton_of_monotone`,
  `Cslib.BitString.influence_eq_neg_fourierCoeff_singleton_of_antitone`: the influences of a
  monotone or antitone function are its degree-one coefficients, up to sign.
* `Cslib.BitString.fourierCoeff_singleton_nonneg_of_monotone`,
  `Cslib.BitString.fourierCoeff_singleton_nonpos_of_antitone`: the sign of the degree-one
  coefficients of a monotone or antitone function.
* `Cslib.BitString.sum_fourierCoeff_singleton_sq_le`: the degree-one weight is at most the
  variance.
* `Cslib.BitString.sq_sum_abs_fourierCoeff_singleton_le`: the degree-one coefficients sum to at
  most `√(n σ²)` in absolute value.
* `Cslib.BitString.abs_fourierCoeff_singleton_eq_influence_iff`: the influence of `i` is the
  absolute value of the coefficient on `{i}` exactly when the function is unate in direction `i`.
* `Cslib.BitString.sum_influence_sq_le_of_monotone`: the squared influences of a monotone function
  sum to at most its variance.
* `Cslib.BitString.totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone`,
  `Cslib.BitString.totalInfluence_eq_neg_sum_fourierCoeff_singleton_of_antitone`: the total
  influence of a monotone function is the sum of its degree-one coefficients.
* `Cslib.BitString.IsUnate.totalInfluence_le_sqrt_card_mul`,
  `Cslib.BitString.IsUnate.totalInfluence_le_sqrt_card`: unate functions have total influence at
  most `√(n σ²) ≤ √n`.
* `Cslib.BitString.totalInfluence_le_sqrt_card_mul_of_monotone`,
  `Cslib.BitString.totalInfluence_le_sqrt_card_of_monotone`,
  `Cslib.BitString.totalInfluence_le_sqrt_card_mul_of_antitone`,
  `Cslib.BitString.totalInfluence_le_sqrt_card_of_antitone`: monotone and antitone functions have
  total influence at most `√(n σ²) ≤ √n`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι] {f : (ι → Bool) → Bool}

/-- The derivative in `i` of a Boolean function read as signs is nonnegative at `x` exactly when
raising bit `i` of `x` from `false` (sign `1`) to `true` (sign `-1`) does not lower the value. -/
theorem derivative_signVal_nonneg_iff (f : (ι → Bool) → Bool) (i : ι) (x : ι → Bool) :
    0 ≤ derivative i (fun x => signVal (f x)) x ↔ f (update x i false) ≤ f (update x i true) := by
  simp only [derivative]
  cases f (update x i false) <;> cases f (update x i true) <;> norm_num

/-- The derivative in `i` of a Boolean function read as signs is nonpositive at `x` exactly when
raising bit `i` of `x` does not raise the value. -/
theorem derivative_signVal_nonpos_iff (f : (ι → Bool) → Bool) (i : ι) (x : ι → Bool) :
    derivative i (fun x => signVal (f x)) x ≤ 0 ↔ f (update x i true) ≤ f (update x i false) := by
  simp only [derivative]
  cases f (update x i false) <;> cases f (update x i true) <;> norm_num

/-- The derivative of a monotone Boolean function read as signs is nonnegative: raising bit `i`
from `false` (sign `1`) to `true` (sign `-1`) can only raise the value. -/
theorem derivative_signVal_nonneg_of_monotone (hf : Monotone f) (i : ι) (x : ι → Bool) :
    0 ≤ derivative i (fun x => signVal (f x)) x :=
  (derivative_signVal_nonneg_iff f i x).2 <|
    hf (update_le_update_iff'.2 (Bool.false_le true) : update x i false ≤ update x i true)

/-- The derivative of an antitone Boolean function read as signs is nonpositive. -/
theorem derivative_signVal_nonpos_of_antitone (hf : Antitone f) (i : ι) (x : ι → Bool) :
    derivative i (fun x => signVal (f x)) x ≤ 0 :=
  (derivative_signVal_nonpos_iff f i x).2 <|
    hf (update_le_update_iff'.2 (Bool.false_le true) : update x i false ≤ update x i true)

/-- `f` is **unate in direction `i`**: changing bit `i` from `false` to `true` either never
lowers the value of `f` or never raises it [O'Donnell, Exercise 2.5][ODonnell2014]. -/
@[expose] def IsUnateIn (i : ι) (f : (ι → Bool) → Bool) : Prop :=
  (∀ x, f (update x i false) ≤ f (update x i true)) ∨
    ∀ x, f (update x i true) ≤ f (update x i false)

/-- `f` is **unate**: it is unate in every direction [O'Donnell, Exercise 2.5][ODonnell2014];
equivalently (not proved here), it is monotone up to negating some of its input bits. -/
@[expose] def IsUnate (f : (ι → Bool) → Bool) : Prop :=
  ∀ i, IsUnateIn i f

/-- A monotone function is unate. -/
theorem _root_.Monotone.isUnate {f : (ι → Bool) → Bool} (hf : Monotone f) : IsUnate f :=
  fun i => Or.inl fun x =>
    hf (update_le_update_iff'.2 (Bool.false_le true) : update x i false ≤ update x i true)

/-- An antitone function is unate. -/
theorem _root_.Antitone.isUnate {f : (ι → Bool) → Bool} (hf : Antitone f) : IsUnate f :=
  fun i => Or.inr fun x =>
    hf (update_le_update_iff'.2 (Bool.false_le true) : update x i false ≤ update x i true)

variable [Fintype ι]

/-- The coefficient of a Boolean function, read as signs, on `{i}` is at most the influence of `i`
in absolute value. -/
theorem abs_fourierCoeff_singleton_le_influence (f : (ι → Bool) → Bool) (i : ι) :
    |fourierCoeff (fun x => signVal (f x)) {i}| ≤ influence i (fun x => signVal (f x)) := by
  rw [fourierCoeff_singleton_eq_expect_derivative, influence]
  simp only [sq_derivative_signVal]
  exact abs_expect_le _ _

/-- **The influences of a monotone Boolean function are its degree-one coefficients**: for a
monotone function read as signs, the influence of `i` is the coefficient on `{i}`
[O'Donnell, Section 2.2][ODonnell2014]. -/
theorem influence_eq_fourierCoeff_singleton_of_monotone (hf : Monotone f) (i : ι) :
    influence i (fun x => signVal (f x)) = fourierCoeff (fun x => signVal (f x)) {i} := by
  rw [fourierCoeff_singleton_eq_expect_derivative, influence]
  exact expect_congr rfl fun x _ => by
    rw [sq_derivative_signVal, abs_of_nonneg (derivative_signVal_nonneg_of_monotone hf i x)]

/-- The influences of an antitone Boolean function read as signs are the negatives of its
degree-one coefficients. -/
theorem influence_eq_neg_fourierCoeff_singleton_of_antitone (hf : Antitone f) (i : ι) :
    influence i (fun x => signVal (f x)) = -fourierCoeff (fun x => signVal (f x)) {i} := by
  rw [fourierCoeff_singleton_eq_expect_derivative, influence, ← expect_neg_distrib]
  exact expect_congr rfl fun x _ => by
    rw [sq_derivative_signVal, abs_of_nonpos (derivative_signVal_nonpos_of_antitone hf i x)]

/-- A monotone Boolean function read as signs has nonnegative degree-one coefficients. -/
theorem fourierCoeff_singleton_nonneg_of_monotone (hf : Monotone f) (i : ι) :
    0 ≤ fourierCoeff (fun x => signVal (f x)) {i} :=
  influence_eq_fourierCoeff_singleton_of_monotone hf i ▸ influence_nonneg i _

/-- An antitone Boolean function read as signs has nonpositive degree-one coefficients. -/
theorem fourierCoeff_singleton_nonpos_of_antitone (hf : Antitone f) (i : ι) :
    fourierCoeff (fun x => signVal (f x)) {i} ≤ 0 := by
  have h := influence_nonneg i fun x => signVal (f x)
  rw [influence_eq_neg_fourierCoeff_singleton_of_antitone hf i] at h
  linarith

/-- **The degree-one weight is at most the variance**: the squared coefficients on the singletons
sum to at most the variance. -/
theorem sum_fourierCoeff_singleton_sq_le (g : (ι → Bool) → ℝ) :
    ∑ i, fourierCoeff g {i} ^ 2 ≤ 𝔼 x, (g x - 𝔼 y, g y) ^ 2 := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq]
  calc ∑ i, fourierCoeff g {i} ^ 2 = ∑ S ∈ univ.image (fun i : ι => {i}), fourierCoeff g S ^ 2 :=
        by rw [sum_image fun _ _ _ _ hab => singleton_injective hab]
    _ ≤ ∑ S with S ≠ ∅, fourierCoeff g S ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg (fun S hS => ?_) fun _ _ _ => sq_nonneg _
        obtain ⟨i, -, rfl⟩ := mem_image.1 hS
        exact mem_filter.2 ⟨mem_univ _, singleton_ne_empty i⟩

/-- **The degree-one coefficients sum to at most `√(n σ²)` in absolute value**, in squared form:
`(∑ i, |ĝ({i})|) ^ 2 ≤ n σ²`, by Cauchy–Schwarz, since the degree-one weight is at most the variance
`σ²`. -/
theorem sq_sum_abs_fourierCoeff_singleton_le (g : (ι → Bool) → ℝ) :
    (∑ i, |fourierCoeff g {i}|) ^ 2 ≤ Fintype.card ι * 𝔼 x, (g x - 𝔼 y, g y) ^ 2 :=
  calc (∑ i, |fourierCoeff g {i}|) ^ 2 ≤ #(univ : Finset ι) * ∑ i, |fourierCoeff g {i}| ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ Fintype.card ι * 𝔼 x, (g x - 𝔼 y, g y) ^ 2 := by
        simp only [card_univ, sq_abs]
        exact mul_le_mul_of_nonneg_left (sum_fourierCoeff_singleton_sq_le g) (Nat.cast_nonneg _)

/-- **The influence of a unate direction** [O'Donnell, Exercise 2.5(a)][ODonnell2014]: for a
Boolean function read as signs, the influence of `i` equals the absolute value of the coefficient
on `{i}` exactly when the function is unate in direction `i`. The inequality `≤` always holds
(`BitString.abs_fourierCoeff_singleton_le_influence`). -/
theorem abs_fourierCoeff_singleton_eq_influence_iff (f : (ι → Bool) → Bool) (i : ι) :
    |fourierCoeff (fun x => signVal (f x)) {i}| = influence i (fun x => signVal (f x)) ↔
      IsUnateIn i f := by
  set D := derivative i (fun x => signVal (f x))
  have hinf : influence i (fun x => signVal (f x)) = 𝔼 x, |D x| :=
    expect_congr rfl fun x _ => sq_derivative_signVal f i x
  rw [fourierCoeff_singleton_eq_expect_derivative, hinf, IsUnateIn]
  simp only [← derivative_signVal_nonneg_iff, ← derivative_signVal_nonpos_iff]
  constructor
  · intro h
    rcases le_total 0 (𝔼 x, D x) with hD | hD
    · rw [abs_of_nonneg hD] at h
      have h0 : 𝔼 x, (|D x| - D x) = 0 := by rw [expect_sub_distrib, h, sub_self]
      have h0' := (expect_eq_zero_iff_of_nonneg fun x _ => sub_nonneg.2 (le_abs_self (D x))).1 h0
      exact Or.inl fun x => by linarith [h0' x (mem_univ x), abs_nonneg (D x)]
    · rw [abs_of_nonpos hD] at h
      have h0 : 𝔼 x, (|D x| + D x) = 0 := by rw [expect_add_distrib, ← h, neg_add_cancel]
      have h0' := (expect_eq_zero_iff_of_nonneg fun x _ => by linarith [neg_abs_le (D x)]).1 h0
      exact Or.inr fun x => by linarith [h0' x (mem_univ x), abs_nonneg (D x)]
  · rintro (h | h)
    · rw [abs_of_nonneg (expect_nonneg fun x _ => h x)]
      exact expect_congr rfl fun x _ => (abs_of_nonneg (h x)).symm
    · have hD : 𝔼 x, D x ≤ 0 := by
        rw [← neg_nonneg, ← expect_neg_distrib]
        exact expect_nonneg fun x _ => neg_nonneg.2 (h x)
      rw [abs_of_nonpos hD, ← expect_neg_distrib]
      exact expect_congr rfl fun x _ => (abs_of_nonpos (h x)).symm

/-- For a monotone Boolean function read as signs, the squared influences sum to at most the
variance. -/
theorem sum_influence_sq_le_of_monotone (hf : Monotone f) :
    ∑ i, influence i (fun x => signVal (f x)) ^ 2 ≤
      𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 := by
  simp only [influence_eq_fourierCoeff_singleton_of_monotone hf]
  exact sum_fourierCoeff_singleton_sq_le _

/-- **The total influence of a monotone function** is the sum of its degree-one Fourier
coefficients, read as signs [O'Donnell, Proposition 2.31][ODonnell2014]. -/
theorem totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone (hf : Monotone f) :
    totalInfluence (fun x => signVal (f x)) = ∑ i, fourierCoeff (fun x => signVal (f x)) {i} :=
  sum_congr rfl fun i _ => influence_eq_fourierCoeff_singleton_of_monotone hf i

/-- The total influence of an antitone function is minus the sum of its degree-one Fourier
coefficients, read as signs. -/
theorem totalInfluence_eq_neg_sum_fourierCoeff_singleton_of_antitone (hf : Antitone f) :
    totalInfluence (fun x => signVal (f x)) = -∑ i, fourierCoeff (fun x => signVal (f x)) {i} := by
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun i _ => influence_eq_neg_fourierCoeff_singleton_of_antitone hf i

/-- **Unate functions have total influence at most `√(n σ²)`**: a unate Boolean function on `n`
coordinates, read as signs with variance `σ²`, has total influence at most `√(n σ²)`, refining
[O'Donnell, Exercise 2.23][ODonnell2014]. Its influences are its degree-one coefficients in
absolute value, which sum to at most `√(n σ²)` by Cauchy–Schwarz. -/
theorem IsUnate.totalInfluence_le_sqrt_card_mul (hf : IsUnate f) :
    totalInfluence (fun x => signVal (f x)) ≤
      √(Fintype.card ι * 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) := by
  have h : totalInfluence (fun x => signVal (f x)) =
      ∑ i, |fourierCoeff (fun x => signVal (f x)) {i}| :=
    sum_congr rfl fun i _ => ((abs_fourierCoeff_singleton_eq_influence_iff f i).2 (hf i)).symm
  exact Real.le_sqrt_of_sq_le (h ▸ sq_sum_abs_fourierCoeff_singleton_le _)

/-- **Unate functions have total influence at most `√n`**: a unate Boolean function on `n`
coordinates, read as signs, has total influence at most `√n`, since its variance is at most one
[O'Donnell, Exercise 2.23][ODonnell2014]. -/
theorem IsUnate.totalInfluence_le_sqrt_card (hf : IsUnate f) :
    totalInfluence (fun x => signVal (f x)) ≤ √(Fintype.card ι) :=
  hf.totalInfluence_le_sqrt_card_mul.trans <| Real.sqrt_le_sqrt <|
    mul_le_of_le_one_right (Nat.cast_nonneg _) (expect_sub_expect_sq_signVal_le_one f)

/-- **Monotone functions have total influence at most `√(n σ²)`**: a monotone Boolean function on
`n` coordinates, read as signs with variance `σ²`, has total influence at most `√(n σ²)`,
refining [O'Donnell, Exercise 2.23][ODonnell2014]. -/
theorem totalInfluence_le_sqrt_card_mul_of_monotone (hf : Monotone f) :
    totalInfluence (fun x => signVal (f x)) ≤
      √(Fintype.card ι * 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) :=
  hf.isUnate.totalInfluence_le_sqrt_card_mul

/-- Antitone functions have total influence at most `√(n σ²)`: an antitone Boolean function on `n`
coordinates, read as signs with variance `σ²`, has total influence at most `√(n σ²)`. -/
theorem totalInfluence_le_sqrt_card_mul_of_antitone (hf : Antitone f) :
    totalInfluence (fun x => signVal (f x)) ≤
      √(Fintype.card ι * 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) :=
  hf.isUnate.totalInfluence_le_sqrt_card_mul

/-- **Monotone functions have total influence at most `√n`**: a monotone Boolean function on `n`
coordinates, read as signs, has total influence at most `√n`
[O'Donnell, Exercise 2.23][ODonnell2014]. -/
theorem totalInfluence_le_sqrt_card_of_monotone (hf : Monotone f) :
    totalInfluence (fun x => signVal (f x)) ≤ √(Fintype.card ι) :=
  hf.isUnate.totalInfluence_le_sqrt_card

/-- Antitone functions have total influence at most `√n`: an antitone Boolean function on `n`
coordinates, read as signs, has total influence at most `√n`. -/
theorem totalInfluence_le_sqrt_card_of_antitone (hf : Antitone f) :
    totalInfluence (fun x => signVal (f x)) ≤ √(Fintype.card ι) :=
  hf.isUnate.totalInfluence_le_sqrt_card

end Cslib.BitString
