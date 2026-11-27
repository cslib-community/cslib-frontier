/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Bernoulli
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith

/-!
# Noise stability and noise sensitivity

Flipping each bit of a string `x` independently with probability `(1 - ρ) / 2` gives a random
string `y` that is *`ρ`-correlated* with `x`. The *noise operator* `T_ρ` (`BitString.noiseOp`)
averages a real function over this noise, `T_ρ f x = 𝔼_y f y`. It damps the Fourier coefficient of
`S` by `ρ ^ |S|` (`BitString.fourierCoeff_noiseOp`), so it has Fourier expansion
`∑_S ρ ^ |S| f̂(S) χ_S` (`BitString.noiseOp_eq_sum`), the noise operators form a semigroup,
`T_ρ T_σ = T_{ρ σ}` (`BitString.noiseOp_noiseOp`), and each is self-adjoint
(`BitString.expect_mul_noiseOp_comm`).

The *noise stability* `Stab_ρ[f] = 𝔼_x f x T_ρ f x` (`BitString.noiseStability`) is the
correlation of `f` at two `ρ`-correlated strings. It is `∑_S ρ ^ |S| f̂(S) ^ 2`
(`BitString.noiseStability_eq_sum`), so on `0 ≤ ρ ≤ 1` it increases with `ρ` from the squared
mean `(𝔼 f) ^ 2` to the second moment `𝔼 f ^ 2`.

The *noise sensitivity* `NS_δ[f]` of a Boolean function (`BitString.noiseSensitivity`) is the
probability that `f x ≠ f y` when `y` flips each bit of a uniform `x` independently with
probability `δ`. Reading `f` as the function `F = (-1) ^ f` with values `±1`, it is
`NS_δ[f] = 1 / 2 - 1 / 2 Stab_{1 - 2 δ}[F]` (`BitString.noiseSensitivity_eq_noiseStability`),
hence `NS_δ[f] = ∑_S (1 - (1 - 2 δ) ^ |S|) / 2 F̂(S) ^ 2` (`BitString.noiseSensitivity_eq_sum`)
[O'Donnell, Section 2.4][ODonnell2014], and `NS_δ[f] ≤ δ I[F]`, at most `δ` times the total
influence (`BitString.noiseSensitivity_le_mul_totalInfluence`)
[O'Donnell, Exercise 2.42][ODonnell2014]. A function close to a constant `b` is also stable
under noise: `f x ≠ f y` forces `x` or `y`, each uniform, to lie where `f ≠ b`, so `NS_δ[f]` is
at most twice the relative Hamming distance from `f` to `b`
(`BitString.noiseSensitivity_le_two_mul_hammingDist_div`), and at most twice the distance to
the nearer constant (`BitString.noiseSensitivity_le_two_mul_min`)
[O'Donnell, Exercise 2.39][ODonnell2014].

The noised string is `x + P`, the coordinatewise exclusive or of `x` with a random mask `P` of
`BitString.bernoulliAverage`, bit strings adding in Mathlib's Boolean ring structure on
`Bool`. The coordinates of the mask are independent:
the average of a product of functions of the separate coordinates factorizes
(`BitString.bernoulliAverage_prod`), so the character of `S` averages to `(1 - 2 p) ^ |S|`
over a mask of rate `p` (`BitString.bernoulliAverage_chi`). In particular, for `0 ≤ δ ≤ 1`
the parity of `k` independent bits that are `1` with probability `1 - δ` is `1` with
probability `1/2 - (2δ - 1)^k / 2` (`BitString.bernoulliAverage_parityOn`, Arora–Barak,
Exercise 17.1, corrected). For other real `δ` the same formula holds as an identity of
signed-weight averages.

## Main definitions

* `Cslib.BitString.noiseOp`, `Cslib.BitString.noiseOpₗ`: the noise operator `T_ρ`, and the same
  as a linear map.
* `Cslib.BitString.noiseStability`: the noise stability of a real function.
* `Cslib.BitString.noiseSensitivity`: the noise sensitivity of a Boolean function.

## Main results

* `Cslib.BitString.bernoulliAverage_parityOn`, `Cslib.BitString.parityOn_bernoulliAverage_le`:
  the parity of biased independent bits [Arora–Barak, Exercise 17.1][AroraBarak07].
* `Cslib.BitString.noiseOp_eq_sum`, `Cslib.BitString.fourierCoeff_noiseOp`: the Fourier expansion
  of `T_ρ f` [O'Donnell, Proposition 2.47][ODonnell2014].
* `Cslib.BitString.noiseOp_noiseOp`: the noise operators form a semigroup.
* `Cslib.BitString.noiseOp_nonneg`, `Cslib.BitString.noiseOp_pos`,
  `Cslib.BitString.noiseOp_pos_of_nonneg`: the noise operator preserves nonnegativity and
  positivity, and for `|ρ| < 1` makes nonzero nonnegative functions positive.
* `Cslib.BitString.noiseOp_comp_arrowCongr`, `Cslib.BitString.noiseOp_of_isEmpty`: the noise
  operator commutes with renaming the coordinates and is the identity on the cube over no
  coordinates.
* `Cslib.BitString.expect_mul_noiseOp_comm`: the noise operator is self-adjoint.
* `Cslib.BitString.noiseStability_eq_sum`: the Fourier formula for the noise stability
  [O'Donnell, Theorem 2.49][ODonnell2014], and `Cslib.BitString.noiseStability_derivative_eq_sum`
  for the noise stability of a derivative.
* `Cslib.BitString.sq_expect_le_noiseStability`, `Cslib.BitString.noiseStability_le_expect_sq`,
  `Cslib.BitString.noiseStability_mono`: the noise stability lies between the squared mean and the
  second moment, increasingly in `ρ`.
* `Cslib.BitString.sq_fourierCoeff_noiseOp_le`, `Cslib.BitString.expect_sub_expect_sq_noiseOp_le`:
  for `|ρ| ≤ 1`, `(T_ρ f)^(S) ^ 2 ≤ f̂(S) ^ 2` and `Var[T_ρ f] ≤ Var[f]`.
* `Cslib.BitString.noiseSensitivity_eq_noiseStability`, `Cslib.BitString.noiseSensitivity_eq_sum`:
  the noise sensitivity through the noise stability and its Fourier formula
  [O'Donnell, Definition 2.43 and Theorem 2.49][ODonnell2014].
* `Cslib.BitString.noiseSensitivity_le_mul_totalInfluence`: the noise sensitivity at `δ` is at
  most `δ` times the total influence.
* `Cslib.BitString.noiseSensitivity_le_two_mul_hammingDist_div`,
  `Cslib.BitString.noiseSensitivity_le_two_mul_min`: the noise sensitivity is at most twice the
  relative Hamming distance to either constant, and to the nearer one
  [O'Donnell, Exercise 2.39][ODonnell2014].

## Usage

For `hδ : δ ≤ 1` and `f : (ι → Bool) → Bool`, `noiseSensitivity_le_two_mul_hammingDist_div hδ f b`
bounds `noiseSensitivity δ f` by twice the relative Hamming distance
`hammingDist f (fun _ => b) / 2 ^ Fintype.card ι` from `f` to the constant `b`, and
`noiseSensitivity_le_two_mul_min hδ f` by twice the distance to the nearer constant. That distance
is the book's `α = min(Pr[F = 1], Pr[F = -1])` for `F = (-1) ^ f`; both constants enter the
minimum, so the convention that `false` reads as `1` does not matter. The book also asks for
`0 ≤ δ`, which is not needed: below `0`, where `noiseSensitivity δ f` is no longer a probability,
the bound of Exercise 2.42 is nonpositive. The same distance is the `ε` of Proposition 1.15 in
`CslibFrontier.Foundations.BooleanAnalysis.Variance`, so
`(noiseSensitivity_le_two_mul_min hδ f).trans (two_mul_min_le_expect_sub_expect_sq_signVal f)`
bounds the noise sensitivity by the variance of `F`. The checked clients in
[CslibFrontierTests/BooleanAnalysisNearlyConstant.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisNearlyConstant.lean)
apply both bounds to the conjunction of two bits, show that the bound is attained there at
`δ = 1`, and chain the bound with Proposition 1.15.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The character of `S` averages to `(1 - 2 p) ^ |S|` over a random mask of rate `p`: each of its
coordinates is selected, negating the sign, with probability `p`. -/
theorem bernoulliAverage_chi (p : ℝ) (S : Finset ι) :
    bernoulliAverage p (chi ℝ S) = (1 - 2 * p) ^ #S := by
  rw [funext (chi_eq_prod_univ S),
    bernoulliAverage_prod p fun i b => if i ∈ S then (-1) ^ b.toNat else 1,
    ← prod_const, ← Fintype.prod_ite_mem S]
  refine prod_congr rfl fun i _ => ?_
  split_ifs
  · simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one]; ring
  · ring

/-- **Arora–Barak, Exercise 17.1, corrected** (web draft 2007-01-08, p. 348/364). If the bits
`X_i` are independent with `Pr[X_i = 1] = 1 - δ`, the parity `X` of the bits in `S` has
`Pr[X = 1] = 1/2 - (2δ - 1)^|S| / 2`. The statement is an identity of `bernoulliAverage`, a
finite signed-weight average, for every real `δ`; it is a probability when `0 ≤ δ ≤ 1`. The draft
prints `1/2 + (1 - 2δ)^k`, which is false (at
`k = 1` it gives `3/2 - 2δ` for `Pr[X_1 = 1] = 1 - δ`). The bound the text uses (p. 322/338) is
`parityOn_bernoulliAverage_le`. -/
theorem bernoulliAverage_parityOn (δ : ℝ) (S : Finset ι) :
    bernoulliAverage (1 - δ) (fun x => if parityOn S x then 1 else 0) =
      1 / 2 - (2 * δ - 1) ^ #S / 2 := by
  have h : (fun x : ι → Bool => if parityOn S x then (1 : ℝ) else 0) =
      fun x => 1 / 2 - 1 / 2 * chi ℝ S x := by
    funext x
    rw [chi_eq_neg_one_pow_parityOn]
    cases parityOn S x <;> norm_num
  rw [h, bernoulliAverage_sub, bernoulliAverage_const, bernoulliAverage_const_mul,
    bernoulliAverage_chi]
  ring

/-- For `0 ≤ δ ≤ 1`, the parity of `|S|` independent bits that are `1` with probability `1 - δ`
is `1` with probability at most `1/2 + (1 - 2δ)^|S| / 2`. The inequality between the
signed-weight averages holds for every real `δ`. For `0 ≤ δ ≤ 1/2` this gives the bound
`1/2 + (1 - 2δ)^k` that Arora–Barak cite Exercise 17.1 for (web draft 2007-01-08, p. 322/338). -/
theorem parityOn_bernoulliAverage_le (δ : ℝ) (S : Finset ι) :
    bernoulliAverage (1 - δ) (fun x => if parityOn S x then 1 else 0) ≤
      1 / 2 + (1 - 2 * δ) ^ #S / 2 := by
  rw [bernoulliAverage_parityOn, show 2 * δ - 1 = -(1 - 2 * δ) by ring]
  rcases Nat.even_or_odd #S with he | ho
  · linarith [he.neg_pow (1 - 2 * δ), he.pow_nonneg (1 - 2 * δ)]
  · linarith [ho.neg_pow (1 - 2 * δ)]

/-! ### The noise operator -/

/-- The **noise operator** `T_ρ`: the average of `f` at a string `ρ`-correlated with `x`, which
flips each bit of `x` independently with probability `(1 - ρ) / 2`. It is an average over a
probability distribution when `-1 ≤ ρ ≤ 1`. -/
noncomputable def noiseOp (ρ : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  bernoulliAverage ((1 - ρ) / 2) fun P => f (x + P)

/-- **The Fourier expansion of `T_ρ f`**: the noise operator damps the coefficient of `S` by
`ρ ^ |S|` [O'Donnell, Proposition 2.47][ODonnell2014]. -/
theorem noiseOp_eq_sum (ρ : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    noiseOp ρ f x = ∑ S, ρ ^ #S * fourierCoeff f S * chi ℝ S x := by
  have hf (P : ι → Bool) : f (x + P) = ∑ S, (fourierCoeff f S * chi ℝ S x) * chi ℝ S P := by
    simp only [← sum_fourierCoeff_mul_chi f (x + P), chi_add, mul_assoc]
  simp only [noiseOp, hf, bernoulliAverage_sum, bernoulliAverage_const_mul, bernoulliAverage_chi,
    show 1 - 2 * ((1 - ρ) / 2) = ρ by ring]
  exact sum_congr rfl fun S _ => by ring

/-- **The noise operator damps the Fourier coefficient of `S` by `ρ ^ |S|`**
[O'Donnell, Proposition 2.47][ODonnell2014]. -/
theorem fourierCoeff_noiseOp (ρ : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (noiseOp ρ f) S = ρ ^ #S * fourierCoeff f S := by
  rw [funext (noiseOp_eq_sum ρ f), fourierCoeff_sum_mul_chi]

/-- The characters are eigenfunctions of the noise operator. -/
theorem noiseOp_chi (ρ : ℝ) (S : Finset ι) (x : ι → Bool) :
    noiseOp ρ (chi ℝ S) x = ρ ^ #S * chi ℝ S x := by
  simp only [noiseOp, chi_add, bernoulliAverage_const_mul, bernoulliAverage_chi]
  rw [show 1 - 2 * ((1 - ρ) / 2) = ρ by ring, mul_comm]

/-- At `ρ = 1` no bit is flipped, so the noise operator is the identity. -/
@[simp] theorem noiseOp_one (f : (ι → Bool) → ℝ) : noiseOp 1 f = f := by
  funext x
  simp [noiseOp, bernoulliAverage_zero, show (x + fun _ => false) = x from add_zero x]

/-- At `ρ = 0` the noised string is uniform, so the noise operator returns the mean. -/
theorem noiseOp_zero (f : (ι → Bool) → ℝ) (x : ι → Bool) : noiseOp 0 f x = 𝔼 y, f y := by
  rw [noiseOp_eq_sum, sum_eq_single ∅ (fun S _ hS => by simp [hS]) (by simp)]
  simp

/-- The noise operator fixes the constants. -/
@[simp] theorem noiseOp_const (ρ c : ℝ) (x : ι → Bool) : noiseOp ρ (fun _ => c) x = c :=
  bernoulliAverage_const _ c

/-- For `|ρ| ≤ 1`, the noise operator maps positive functions to positive functions. -/
theorem noiseOp_pos {ρ : ℝ} (hρ : -1 ≤ ρ) (hρ' : ρ ≤ 1) {g : (ι → Bool) → ℝ}
    (hg : ∀ x, 0 < g x) (x : ι → Bool) : 0 < noiseOp ρ g x := by
  obtain ⟨y, -, hy⟩ := exists_min_image univ g univ_nonempty
  calc 0 < g y := hg y
    _ = bernoulliAverage ((1 - ρ) / 2) fun _ => g y := (bernoulliAverage_const _ _).symm
    _ ≤ noiseOp ρ g x :=
        bernoulliAverage_mono (by linarith) (by linarith) fun P => hy _ (mem_univ _)

/-- For `|ρ| ≤ 1`, the noise operator maps nonnegative functions to nonnegative functions. -/
theorem noiseOp_nonneg {ρ : ℝ} (hρ : -1 ≤ ρ) (hρ' : ρ ≤ 1) {g : (ι → Bool) → ℝ}
    (hg : ∀ x, 0 ≤ g x) (x : ι → Bool) : 0 ≤ noiseOp ρ g x :=
  calc (0 : ℝ) = bernoulliAverage ((1 - ρ) / 2) fun _ => 0 := (bernoulliAverage_const _ _).symm
    _ ≤ noiseOp ρ g x := bernoulliAverage_mono (by linarith) (by linarith) fun _ => hg _

/-- For `-1 < ρ < 1`, the noise operator maps a nonnegative function that is positive somewhere
to a positive function: every point is reached with positive probability. -/
theorem noiseOp_pos_of_nonneg {ρ : ℝ} (hρ : -1 < ρ) (hρ' : ρ < 1) {g : (ι → Bool) → ℝ}
    (hg : ∀ x, 0 ≤ g x) {y : ι → Bool} (hy : 0 < g y) (x : ι → Bool) : 0 < noiseOp ρ g x := by
  have hw (P : ι → Bool) := bernoulliWeight_pos (p := (1 - ρ) / 2) (by linarith) (by linarith) P
  refine sum_pos' (fun P _ => mul_nonneg (hw P).le (hg _)) ⟨x + y, mem_univ _, mul_pos (hw _) ?_⟩
  have hxy : x + (x + y) = y := funext fun i => by
    change x i + (x i + y i) = y i
    cases x i <;> cases y i <;> rfl
  simpa only [hxy] using hy

/-- The noise operator is additive. -/
theorem noiseOp_add (ρ : ℝ) (f g : (ι → Bool) → ℝ) (x : ι → Bool) :
    noiseOp ρ (fun y => f y + g y) x = noiseOp ρ f x + noiseOp ρ g x :=
  bernoulliAverage_add _ _ _

/-- The noise operator commutes with subtraction. -/
theorem noiseOp_sub (ρ : ℝ) (f g : (ι → Bool) → ℝ) (x : ι → Bool) :
    noiseOp ρ (fun y => f y - g y) x = noiseOp ρ f x - noiseOp ρ g x :=
  bernoulliAverage_sub _ _ _

/-- The noise operator commutes with scaling. -/
theorem noiseOp_const_mul (ρ c : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    noiseOp ρ (fun y => c * f y) x = c * noiseOp ρ f x :=
  bernoulliAverage_const_mul _ _ _

/-- The noise operator `T_ρ`, as a linear map. -/
noncomputable def noiseOpₗ (ρ : ℝ) : ((ι → Bool) → ℝ) →ₗ[ℝ] (ι → Bool) → ℝ where
  toFun := noiseOp ρ
  map_add' f g := funext (noiseOp_add ρ f g)
  map_smul' c f := funext (noiseOp_const_mul ρ c f)

/-- The linear map `noiseOpₗ ρ` applies the noise operator `T_ρ`. -/
@[simp] theorem noiseOpₗ_apply (ρ : ℝ) (f : (ι → Bool) → ℝ) : noiseOpₗ ρ f = noiseOp ρ f :=
  rfl

/-- **The noise operators form a semigroup**: `T_ρ T_σ = T_{ρ σ}`. -/
theorem noiseOp_noiseOp (ρ σ : ℝ) (f : (ι → Bool) → ℝ) :
    noiseOp ρ (noiseOp σ f) = noiseOp (ρ * σ) f :=
  fourierCoeff_injective <| funext fun S => by
    simp only [fourierCoeff_noiseOp, mul_pow, mul_assoc]

/-- The noise operator commutes with renaming the coordinates. -/
theorem noiseOp_comp_arrowCongr {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (ρ : ℝ)
    (g : (κ → Bool) → ℝ) (x : ι → Bool) :
    noiseOp ρ (fun y : ι → Bool => g fun j => y (e.symm j)) x =
      noiseOp ρ g fun j => x (e.symm j) :=
  bernoulliAverage_reindex e _ fun Q => g ((fun j => x (e.symm j)) + Q)

/-- On the cube over no coordinates, a single point, the noise operator is the identity. -/
theorem noiseOp_of_isEmpty [IsEmpty ι] (ρ : ℝ) (g : (ι → Bool) → ℝ) (x : ι → Bool) :
    noiseOp ρ g x = g x := by
  simp [noiseOp, Subsingleton.elim (x + ·) (fun _ => x), bernoulliAverage_const]

/-- The correlation of `f` with `T_ρ g` is the sum of the products of the Fourier coefficients
damped by `ρ ^ |S|`. -/
theorem expect_mul_noiseOp_eq_sum (ρ : ℝ) (f g : (ι → Bool) → ℝ) :
    𝔼 x, f x * noiseOp ρ g x = ∑ S, ρ ^ #S * (fourierCoeff f S * fourierCoeff g S) := by
  rw [expect_mul_eq_sum_fourierCoeff_mul]
  exact sum_congr rfl fun S _ => by rw [fourierCoeff_noiseOp, mul_left_comm]

/-- **The noise operator is self-adjoint**: `𝔼 f T_ρ g = 𝔼 (T_ρ f) g`. -/
theorem expect_mul_noiseOp_comm (ρ : ℝ) (f g : (ι → Bool) → ℝ) :
    𝔼 x, f x * noiseOp ρ g x = 𝔼 x, noiseOp ρ f x * g x := by
  simp only [mul_comm (noiseOp ρ f _), expect_mul_noiseOp_eq_sum, mul_comm (fourierCoeff f _)]

/-! ### Noise stability -/

/-- The **noise stability** `Stab_ρ[f]` of `f` at `ρ`: the correlation `𝔼 f x f y` of `f` at a
uniform string `x` and a string `y` that is `ρ`-correlated with `x`. -/
noncomputable def noiseStability (ρ : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  𝔼 x, f x * noiseOp ρ f x

/-- **The Fourier formula for the noise stability**: `Stab_ρ[f] = ∑_S ρ ^ |S| f̂(S) ^ 2`
[O'Donnell, Theorem 2.49][ODonnell2014]. -/
theorem noiseStability_eq_sum (ρ : ℝ) (f : (ι → Bool) → ℝ) :
    noiseStability ρ f = ∑ S, ρ ^ #S * fourierCoeff f S ^ 2 := by
  simp only [noiseStability, expect_mul_noiseOp_eq_sum, sq]

/-- **The Fourier formula for the noise stability of a derivative**:
`Stab_ρ[Dᵢ f] = ∑_{S ∋ i} ρ ^ (|S| - 1) f̂(S) ^ 2`. -/
theorem noiseStability_derivative_eq_sum (ρ : ℝ) (i : ι) (f : (ι → Bool) → ℝ) :
    noiseStability ρ (derivative i f) = ∑ S with i ∈ S, ρ ^ (#S - 1) * fourierCoeff f S ^ 2 := by
  rw [noiseStability_eq_sum, sum_filter_mem_eq_sum_filter_notMem i, sum_filter]
  refine sum_congr rfl fun T _ => ?_
  by_cases hT : i ∈ T <;> simp [fourierCoeff_derivative, hT, card_insert_of_notMem]

/-- **The noise stability of a derivative**: `ρ Stab_ρ[Dᵢ f]` weighs the squared coefficient of
`f` on each set containing `i` by `ρ` to the size of the set. -/
theorem mul_noiseStability_derivative (ρ : ℝ) (i : ι) (f : (ι → Bool) → ℝ) :
    ρ * noiseStability ρ (derivative i f) = ∑ S with i ∈ S, ρ ^ #S * fourierCoeff f S ^ 2 := by
  rw [noiseStability_derivative_eq_sum, mul_sum]
  exact sum_congr rfl fun S hS => by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (card_pos.2 ⟨i, (mem_filter.1 hS).2⟩)]

/-- At `ρ = 1` the noise stability is the second moment. -/
theorem noiseStability_one (f : (ι → Bool) → ℝ) : noiseStability 1 f = 𝔼 x, f x ^ 2 := by
  simp only [noiseStability, noiseOp_one, sq]

/-- At `ρ = 0` the noise stability is the squared mean. -/
theorem noiseStability_zero (f : (ι → Bool) → ℝ) : noiseStability 0 f = (𝔼 x, f x) ^ 2 := by
  simp only [noiseStability, noiseOp_zero, ← expect_mul, sq]

/-- On `0 ≤ ρ`, the noise stability increases with `ρ`. -/
theorem noiseStability_mono {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρσ : ρ ≤ σ) (f : (ι → Bool) → ℝ) :
    noiseStability ρ f ≤ noiseStability σ f := by
  simp only [noiseStability_eq_sum]
  exact sum_le_sum fun S _ =>
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ hρσ _) (sq_nonneg _)

/-- On `0 ≤ ρ`, the noise stability is at least the squared mean. -/
theorem sq_expect_le_noiseStability {ρ : ℝ} (hρ : 0 ≤ ρ) (f : (ι → Bool) → ℝ) :
    (𝔼 x, f x) ^ 2 ≤ noiseStability ρ f :=
  noiseStability_zero f ▸ noiseStability_mono le_rfl hρ f

/-- On `0 ≤ ρ`, the noise stability is nonnegative. -/
theorem noiseStability_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (f : (ι → Bool) → ℝ) :
    0 ≤ noiseStability ρ f :=
  (sq_nonneg _).trans (sq_expect_le_noiseStability hρ f)

/-- On `|ρ| ≤ 1`, the noise stability is at most the second moment. -/
theorem noiseStability_le_expect_sq {ρ : ℝ} (hρ : |ρ| ≤ 1) (f : (ι → Bool) → ℝ) :
    noiseStability ρ f ≤ 𝔼 x, f x ^ 2 := by
  rw [noiseStability_eq_sum, expect_sq_eq_sum_fourierCoeff_sq]
  exact sum_le_sum fun S _ => mul_le_of_le_one_left (sq_nonneg _)
    ((le_abs_self _).trans (abs_pow ρ #S ▸ pow_le_one₀ (abs_nonneg ρ) hρ))

/-- On `|ρ| ≤ 1`, the noise operator does not increase the squared Fourier coefficients:
`(T_ρ f)^(S) ^ 2 ≤ f̂(S) ^ 2`. -/
theorem sq_fourierCoeff_noiseOp_le {ρ : ℝ} (hρ : |ρ| ≤ 1) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (noiseOp ρ f) S ^ 2 ≤ fourierCoeff f S ^ 2 := by
  rw [fourierCoeff_noiseOp, mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _)
    ((sq_le_one_iff_abs_le_one _).2 (abs_pow ρ #S ▸ pow_le_one₀ (abs_nonneg ρ) hρ))

/-- On `|ρ| ≤ 1`, the noise operator does not increase the variance: `Var[T_ρ f] ≤ Var[f]`. -/
theorem expect_sub_expect_sq_noiseOp_le {ρ : ℝ} (hρ : |ρ| ≤ 1) (f : (ι → Bool) → ℝ) :
    𝔼 x, (noiseOp ρ f x - 𝔼 y, noiseOp ρ f y) ^ 2 ≤ 𝔼 x, (f x - 𝔼 y, f y) ^ 2 := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq, expect_sub_expect_sq_eq_sum_fourierCoeff_sq]
  exact sum_le_sum fun S _ => sq_fourierCoeff_noiseOp_le hρ f S

/-! ### Noise sensitivity -/

/-- The **noise sensitivity** `NS_δ[f]` of a Boolean function `f` at `δ`: the probability that
`f x ≠ f y` for a uniform string `x` and the string `y` that flips each bit of `x` independently
with probability `δ`. -/
noncomputable def noiseSensitivity (δ : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  𝔼 x, bernoulliAverage δ fun P => if f x ≠ f (x + P) then 1 else 0

/-- **The noise sensitivity through the noise stability**:
`NS_δ[f] = 1 / 2 - 1 / 2 Stab_{1 - 2 δ}[F]`, for `F` the function `f` with values `±1`. -/
theorem noiseSensitivity_eq_noiseStability (δ : ℝ) (f : (ι → Bool) → Bool) :
    noiseSensitivity δ f = 1 / 2 - 1 / 2 * noiseStability (1 - 2 * δ) fun x => signVal (f x) := by
  have h (a b : Bool) :
      (if a ≠ b then (1 : ℝ) else 0) = 1 / 2 - 1 / 2 * (signVal a * signVal b) := by
    cases a <;> cases b <;> norm_num
  simp only [noiseSensitivity, noiseStability, noiseOp, show (1 - (1 - 2 * δ)) / 2 = δ by ring, h,
    bernoulliAverage_sub, bernoulliAverage_const, bernoulliAverage_const_mul, expect_sub_distrib,
    Fintype.expect_const, mul_expect]

/-- **The Fourier formula for the noise sensitivity**:
`NS_δ[f] = ∑_S (1 - (1 - 2 δ) ^ |S|) / 2 F̂(S) ^ 2`, for `F` the function `f` with values `±1`
[O'Donnell, Theorem 2.49][ODonnell2014]. -/
theorem noiseSensitivity_eq_sum (δ : ℝ) (f : (ι → Bool) → Bool) :
    noiseSensitivity δ f =
      ∑ S, (1 - (1 - 2 * δ) ^ #S) / 2 * fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  have h (S : Finset ι) (c : ℝ) : (1 - (1 - 2 * δ) ^ #S) / 2 * c ^ 2 =
      1 / 2 * c ^ 2 - 1 / 2 * ((1 - 2 * δ) ^ #S * c ^ 2) := by
    ring
  simp only [noiseSensitivity_eq_noiseStability, noiseStability_eq_sum, h, sum_sub_distrib,
    ← mul_sum, sum_fourierCoeff_sq_signVal, mul_one]

/-- With no noise, `f` never changes. -/
@[simp] theorem noiseSensitivity_zero (f : (ι → Bool) → Bool) : noiseSensitivity 0 f = 0 := by
  have h (x : ι → Bool) : (x + fun _ => false) = x := add_zero x
  simp [noiseSensitivity, bernoulliAverage_zero, h]

/-- On `0 ≤ δ ≤ 1`, the noise sensitivity is a probability. -/
theorem noiseSensitivity_mem_Icc {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (f : (ι → Bool) → Bool) :
    noiseSensitivity δ f ∈ Set.Icc 0 1 := by
  refine ⟨expect_nonneg fun x _ => ?_, expect_le univ_nonempty fun x _ => ?_⟩
  · simpa only [bernoulliAverage_const] using bernoulliAverage_mono hδ hδ' (f := fun _ => 0)
      fun _ => by split_ifs <;> norm_num
  · simpa only [bernoulliAverage_const] using bernoulliAverage_mono hδ hδ' (g := fun _ => 1)
      fun _ => by split_ifs <;> norm_num

/-- On `δ ≤ 1 / 2`, the noise sensitivity increases with `δ`. -/
theorem noiseSensitivity_mono {δ δ' : ℝ} (hδδ' : δ ≤ δ') (hδ' : δ' ≤ 1 / 2)
    (f : (ι → Bool) → Bool) : noiseSensitivity δ f ≤ noiseSensitivity δ' f := by
  simp only [noiseSensitivity_eq_noiseStability]
  linarith [noiseStability_mono (by linarith : 0 ≤ 1 - 2 * δ')
    (by linarith : 1 - 2 * δ' ≤ 1 - 2 * δ) fun x => signVal (f x)]

/-- **The noise sensitivity is at most `δ` times the total influence**: `NS_δ[f] ≤ δ I[F]` for
`δ ≤ 1`, for `F` the function `f` with values `±1` [O'Donnell, Exercise 2.42][ODonnell2014]. -/
theorem noiseSensitivity_le_mul_totalInfluence {δ : ℝ} (hδ : δ ≤ 1) (f : (ι → Bool) → Bool) :
    noiseSensitivity δ f ≤ δ * totalInfluence (fun x => signVal (f x)) := by
  rw [noiseSensitivity_eq_sum, totalInfluence_eq_sum_card_mul_fourierCoeff_sq, mul_sum]
  refine sum_le_sum fun S _ => ?_
  have h := one_add_mul_sub_le_pow (show -1 ≤ 1 - 2 * δ by linarith) #S
  nlinarith [sq_nonneg (fourierCoeff (fun x => signVal (f x)) S)]

/-- **The noise sensitivity is at most twice the distance to either constant**: for `δ ≤ 1`,
`NS_δ[f] ≤ 2 Pr[f ≠ b]`, since `f x ≠ f y` forces `x` or `y`, each uniform, to lie where `f ≠ b`. -/
theorem noiseSensitivity_le_two_mul_hammingDist_div {δ : ℝ} (hδ : δ ≤ 1)
    (f : (ι → Bool) → Bool) (b : Bool) :
    noiseSensitivity δ f ≤ 2 * ((hammingDist f (fun _ => b) : ℝ) / 2 ^ Fintype.card ι) := by
  rcases lt_or_ge δ 0 with hδ₀ | hδ₀
  · -- at negative rates the bound of Exercise 2.42 is nonpositive
    exact (noiseSensitivity_le_mul_totalInfluence hδ f).trans <| (mul_nonpos_of_nonpos_of_nonneg
      hδ₀.le (totalInfluence_nonneg _)).trans (by positivity)
  set g : (ι → Bool) → ℝ := fun x => if f x ≠ b then 1 else 0
  have hpt (x P : ι → Bool) : (if f x ≠ f (x + P) then (1 : ℝ) else 0) ≤ g x + g (x + P) := by
    simp only [g]; cases f x <;> cases f (x + P) <;> cases b <;> simp
  calc noiseSensitivity δ f
      ≤ 𝔼 x, bernoulliAverage δ fun P => g x + g (x + P) :=
        expect_le_expect fun x _ => bernoulliAverage_mono hδ₀ hδ (hpt x)
    _ = 2 * 𝔼 x, g x := by
        simp only [bernoulliAverage_add, bernoulliAverage_const, expect_add_distrib,
          ← bernoulliAverage_expect_comm, add_comm _ (_ : ι → Bool), Fintype.expect_add_left]
        ring
    _ = 2 * ((hammingDist f (fun _ => b) : ℝ) / 2 ^ Fintype.card ι) := by
        rw [show (2 : ℝ) ^ Fintype.card ι = Fintype.card (ι → Bool) by simp,
          hammingDist_div_eq_expect]

/-- **Nearly constant functions are stable under noise** [O'Donnell, Exercise 2.39][ODonnell2014]:
for `δ ≤ 1`, `NS_δ[f] ≤ 2 α` for `α = min (Pr[F = 1], Pr[F = -1])` with `F = (-1) ^ f`, the
relative Hamming distance from `f` to the nearer constant. -/
theorem noiseSensitivity_le_two_mul_min {δ : ℝ} (hδ : δ ≤ 1) (f : (ι → Bool) → Bool) :
    noiseSensitivity δ f ≤
      2 * min ((hammingDist f (fun _ => false) : ℝ) / 2 ^ Fintype.card ι)
        (hammingDist f (fun _ => true) / 2 ^ Fintype.card ι) := by
  rw [mul_min_of_nonneg _ _ zero_le_two]
  exact le_min (noiseSensitivity_le_two_mul_hammingDist_div hδ f false)
    (noiseSensitivity_le_two_mul_hammingDist_div hδ f true)

end Cslib.BitString
