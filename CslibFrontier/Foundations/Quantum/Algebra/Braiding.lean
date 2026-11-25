/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.PauliFamily
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Foundations.Data.BitString.OddPairs
import CslibFrontier.Tactic.CommuteLeft

/-!
# Braiding relations from anticommutation, consistency and linearity

The Pauli braiding relations `Z(b) X(a) = (-1)^{a·b} X(a) Z(b)` are what the Pauli-family defect
bound (`Cslib.Quantum.expect_norm_pauliFamily_sub_sq_le`) needs from a strategy. The braiding test
of [Natarajan and Vidick, §4][NatarajanVidick2017] (arXiv:1610.03574v1) certifies only part of
them directly: anticommutation for the pairs with `a · b = 1`, through an anticommutation game
played on the observables of the other player. This file derives the rest, in any state of any
star-ordered algebra, for Alice's unitaries `X(a)`, `Z(b)` and Bob's consistent copies `X'(a)`,
`Z'(b)` commuting with them.

* **Transfer** (the step in the proof of their §4.3.2, Lemma 18, p. 21): a relation between two
  observables of one player passes to consistent observables of the other,
  `‖Z X - s X Z‖_φ ≤ 2 ‖X - X'‖_φ + 2 ‖Z - Z'‖_φ + ‖X' Z' - s Z' X'‖_φ`
  (`Cslib.Quantum.norm_mul_sub_smul_mul_le_of_consistent`, averaged in
  `Cslib.Quantum.expect_norm_mul_sub_smul_mul_sq_le_of_consistent`).
* **Commutation** (their §4.3.3, Lemma 19, p. 22): for `a · b = 0`, write `Z(b) ≈ Z(c) Z(c + b)`
  with `c · a = 1` and anticommute `X(a)` past both factors
  (`Cslib.Quantum.norm_mul_sub_mul_le_of_anticommute`).
  Averaging over the half of the `c` with `c · a = 1`
  (`Cslib.BitString.le_two_mul_expect_ite_of_forall`), and using `X(0) = 1` for `a = 0`, gives
  the braiding defect for every pair (`Cslib.Quantum.expect_norm_braid_sq_le`):
  `E_{a,b} ‖Z(b) X(a) - (-1)^{a·b} X(a) Z(b)‖²_φ ≤ 33 E_{a,b} [a · b = 1] α(a, b)² +
  32 (E ‖Z(c) Z(c') - Z(c + c')‖² + E κ_Z² + E κ_X²)`,
  where `α(a, b) = ‖X(a) Z(b) + Z(b) X(a)‖_φ`, the masked average over the pairs with `a · b = 1` is
  `Cslib.BitString.oddExpect`, and `κ` are the consistency distances.
* **The Pauli-family defect** then follows from anticommutation, consistency and linearity
  (`Cslib.Quantum.expect_norm_pauliFamily_sub_sq_le_of_anticommute`).

**Where this starts, relative to the source.** The source applies its lemmas to the averaged
marginal observables of its eq. (11), which are self-adjoint contractions but need not be unitary.
Here the inputs are unitary families with `X(0) = 1`, such as the rounded, exactly linear
observables of the linearity test, and Bob's consistent unitary copies. The source states the
anticommutation hypothesis as a conditional average `E_{a,b | a·b = 1}`; here it enters as the
masked unconditional average `E_{a,b} [a · b = 1] α(a, b)²`, which equals
`Pr[a · b = 1] · E_{a,b | a·b = 1} α(a, b)²` and so is at most the conditional average. The
commutation step likewise averages over all `c` with the mask `c · a = 1` and uses that a nonzero
`a` has `c · a = 1` for exactly half of the `c`.

`X(0) = 1` holds for the character observables of a projective measurement
(`Cslib.Quantum.Measurement.charObs_zero`), such as the rounded observables of the linearity test.
Deriving the anticommutation defects from a strategy's success in an anticommutation game, and the
remaining steps toward Pauli rigidity, are tracked in cslib-community/cslib-frontier#6149.

## Main results

* `Cslib.Quantum.norm_mul_sub_smul_mul_le_of_consistent`: transfer through consistency.
* `Cslib.Quantum.norm_mul_sub_mul_le_of_anticommute`: commutation from anticommutation.
* `Cslib.Quantum.expect_norm_braid_sq_le`: the averaged braiding defect.
* `Cslib.Quantum.expect_norm_pauliFamily_sub_sq_le_of_anticommute`: the Pauli-family defect.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Quantum

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A]

/-- **Transfer of a commutation relation through consistency.** If the contractions `X` and `Z`
commute with the contractions `Z'` and `X'` respectively, then
`‖Z X - s X Z‖_φ ≤ 2 ‖X - X'‖_φ + 2 ‖Z - Z'‖_φ + ‖X' Z' - s Z' X'‖_φ`
for every phase `s` with `‖s‖ = 1`. -/
theorem norm_mul_sub_smul_mul_le_of_consistent (φ : AlgState A) {X Z X' Z' : A}
    (hX : star X * X ≤ 1) (hZ : star Z * Z ≤ 1) (hX' : star X' * X' ≤ 1)
    (hZ' : star Z' * Z' ≤ 1) (hXZ' : Commute X Z') (hZX' : Commute Z X') {s : ℂ}
    (hs : ‖s‖ = 1) :
    φ.norm (Z * X - s • (X * Z)) ≤
      2 * φ.norm (X - X') + 2 * φ.norm (Z - Z') + φ.norm (X' * Z' - s • (Z' * X')) := by
  have cX := φ.approx_norm_sub X X'
  have cZ := φ.approx_norm_sub Z Z'
  have chain := calc
      Z * X ≈[φ; φ.norm (X - X')] Z * X' := cX.mul_left hZ
    _ = X' * Z := hZX'.eq
    _ ≈[φ; φ.norm (Z - Z')] X' * Z' := cZ.mul_left hX'
    _ ≈[φ; φ.norm (X' * Z' - s • (Z' * X'))] s • (Z' * X') := φ.approx_norm_sub _ _
    _ ≈[φ; ‖s‖ * φ.norm (X - X')] s • (Z' * X) := (cX.symm.mul_left hZ').smul s
    _ = s • (X * Z') := by rw [hXZ'.eq]
    _ ≈[φ; ‖s‖ * φ.norm (Z - Z')] s • (X * Z) := (cZ.symm.mul_left hX).smul s
  rw [hs, one_mul, one_mul] at chain
  have h := AlgState.approx_iff.mp chain
  linarith

/-- **Squared transfer**: under the hypotheses of
`Cslib.Quantum.norm_mul_sub_smul_mul_le_of_consistent`,
`‖Z X - s X Z‖²_φ ≤ 9 (‖X - X'‖²_φ + ‖Z - Z'‖²_φ + ‖X' Z' - s Z' X'‖²_φ)`. -/
theorem norm_mul_sub_smul_mul_sq_le_of_consistent (φ : AlgState A) {X Z X' Z' : A}
    (hX : star X * X ≤ 1) (hZ : star Z * Z ≤ 1) (hX' : star X' * X' ≤ 1)
    (hZ' : star Z' * Z' ≤ 1) (hXZ' : Commute X Z') (hZX' : Commute Z X') {s : ℂ}
    (hs : ‖s‖ = 1) :
    φ.norm (Z * X - s • (X * Z)) ^ 2 ≤
      9 * (φ.norm (X - X') ^ 2 + φ.norm (Z - Z') ^ 2 + φ.norm (X' * Z' - s • (Z' * X')) ^ 2) := by
  have h := norm_mul_sub_smul_mul_le_of_consistent φ hX hZ hX' hZ' hXZ' hZX' hs
  set a := φ.norm (X - X')
  set b := φ.norm (Z - Z')
  set c := φ.norm (X' * Z' - s • (Z' * X'))
  calc φ.norm (Z * X - s • (X * Z)) ^ 2
      ≤ (2 * a + 2 * b + c) ^ 2 := pow_le_pow_left₀ (φ.norm_nonneg _) h 2
    _ ≤ 9 * (a ^ 2 + b ^ 2 + c ^ 2) := by
        linarith [sq_nonneg (2 * a - 2 * b), sq_nonneg (a - 2 * c), sq_nonneg (b - 2 * c)]

/-- **Averaged transfer of a commutation relation through consistency**: over any finite family,
`E_i ‖Z_i X_i - s_i X_i Z_i‖²_φ ≤ 9 (E_i ‖X_i - X'_i‖²_φ + E_i ‖Z_i - Z'_i‖²_φ +
E_i ‖X'_i Z'_i - s_i Z'_i X'_i‖²_φ)`. -/
theorem expect_norm_mul_sub_smul_mul_sq_le_of_consistent {ι : Type*} [Fintype ι]
    (φ : AlgState A) (X Z X' Z' : ι → A) (s : ι → ℂ) (hX : ∀ i, star (X i) * X i ≤ 1)
    (hZ : ∀ i, star (Z i) * Z i ≤ 1) (hX' : ∀ i, star (X' i) * X' i ≤ 1)
    (hZ' : ∀ i, star (Z' i) * Z' i ≤ 1) (hXZ' : ∀ i, Commute (X i) (Z' i))
    (hZX' : ∀ i, Commute (Z i) (X' i)) (hs : ∀ i, ‖s i‖ = 1) :
    𝔼 i, φ.norm (Z i * X i - s i • (X i * Z i)) ^ 2 ≤
      9 * (𝔼 i, φ.norm (X i - X' i) ^ 2 + 𝔼 i, φ.norm (Z i - Z' i) ^ 2 +
        𝔼 i, φ.norm (X' i * Z' i - s i • (Z' i * X' i)) ^ 2) := by
  calc 𝔼 i, φ.norm (Z i * X i - s i • (X i * Z i)) ^ 2
      ≤ 𝔼 i, 9 * (φ.norm (X i - X' i) ^ 2 + φ.norm (Z i - Z' i) ^ 2 +
          φ.norm (X' i * Z' i - s i • (Z' i * X' i)) ^ 2) :=
        expect_le_expect fun i _ => norm_mul_sub_smul_mul_sq_le_of_consistent φ (hX i) (hZ i)
          (hX' i) (hZ' i) (hXZ' i) (hZX' i) (hs i)
    _ = _ := by rw [← mul_expect, expect_add_distrib, expect_add_distrib]

section Commutation

variable {ι : Type*}

/-- **Commutation from anticommutation, pointwise** (the chain of
[Natarajan and Vidick, §4.3.3, Lemma 19][NatarajanVidick2017]). Let Alice's unitaries `X(a)`,
`Z(b)` commute with Bob's unitaries `X'(a)`, `Z'(b)`. Writing `Z(b) ≈ Z(c) Z(c + b)` and
anticommuting `X(a)` past both factors, with Bob's copies carrying the factors that are in the way,
gives, for all `a`, `b`, `c`,
`‖Z(b) X(a) - X(a) Z(b)‖_φ ≤ 2ℓ + 2κ_Z(c + b) + α(a, c) + α(a, c + b) + 2κ_X(a)`, where
`ℓ = ‖Z(c) Z(c + b) - Z(b)‖_φ`, `κ` are the consistency distances to Bob's copies and
`α(a, c) = ‖X(a) Z(c) + Z(c) X(a)‖_φ` is the anticommutation defect. It is useful when
`a · b = 0` and `c · a = 1`, so that both `c · a` and `(c + b) · a` are `1` and the anticommutation
defects are small. -/
theorem norm_mul_sub_mul_le_of_anticommute (φ : AlgState A) (X Z X' Z' : (ι → Bool) → A)
    (hX : ∀ a, X a ∈ unitary A) (hZ : ∀ b, Z b ∈ unitary A) (hX' : ∀ a, X' a ∈ unitary A)
    (hZ' : ∀ b, Z' b ∈ unitary A) (hXZ' : ∀ a b, Commute (X a) (Z' b))
    (hZZ' : ∀ b b', Commute (Z b) (Z' b')) (hZX' : ∀ b a, Commute (Z b) (X' a)) (a b c : ι → Bool) :
    φ.norm (Z b * X a - X a * Z b) ≤
      2 * φ.norm (Z c * Z (c + b) - Z b) + 2 * φ.norm (Z (c + b) - Z' (c + b)) +
        φ.norm (X a * Z c + Z c * X a) + φ.norm (X a * Z (c + b) + Z (c + b) * X a) +
        2 * φ.norm (X a - X' a) := by
  have hℓ := φ.approx_norm_sub (Z c * Z (c + b)) (Z b)
  have hκZ := φ.approx_norm_sub (Z (c + b)) (Z' (c + b))
  have hκX := φ.approx_norm_sub (X a) (X' a)
  have hα : ∀ d, X a * Z d ≈[φ; φ.norm (X a * Z d + Z d * X a)] -(Z d * X a) := fun d => by
    simpa only [sub_neg_eq_add] using φ.approx_norm_sub (X a * Z d) (-(Z d * X a))
  have chain := calc
      X a * Z b ≈[φ; φ.norm (Z c * Z (c + b) - Z b)] X a * (Z c * Z (c + b)) :=
        hℓ.symm.mul_left_unitary (hX a)
    _ = X a * Z c * Z (c + b) := (mul_assoc _ _ _).symm
    _ ≈[φ; φ.norm (Z (c + b) - Z' (c + b))] X a * Z c * Z' (c + b) :=
        hκZ.mul_left_unitary (by unitary_mem)
    _ = Z' (c + b) * (X a * Z c) := by commute_left [hXZ', hZZ']
    _ ≈[φ; φ.norm (X a * Z c + Z c * X a)] Z' (c + b) * -(Z c * X a) :=
        (hα c).mul_left_unitary (hZ' _)
    _ = -(Z c * X a * Z' (c + b)) := by rw [mul_neg]; commute_left [hXZ', hZZ']
    _ ≈[φ; φ.norm (Z (c + b) - Z' (c + b))] -(Z c * X a * Z (c + b)) :=
        (hκZ.symm.mul_left_unitary (by unitary_mem)).neg
    _ = -(Z c * (X a * Z (c + b))) := by rw [mul_assoc]
    _ ≈[φ; φ.norm (X a * Z (c + b) + Z (c + b) * X a)] -(Z c * -(Z (c + b) * X a)) :=
        ((hα (c + b)).mul_left_unitary (hZ c)).neg
    _ = Z c * Z (c + b) * X a := by rw [mul_neg, neg_neg, mul_assoc]
    _ ≈[φ; φ.norm (X a - X' a)] Z c * Z (c + b) * X' a := hκX.mul_left_unitary (by unitary_mem)
    _ = X' a * (Z c * Z (c + b)) := by commute_left [hZX']
    _ ≈[φ; φ.norm (Z c * Z (c + b) - Z b)] X' a * Z b := hℓ.mul_left_unitary (hX' a)
    _ = Z b * X' a := by commute_left [hZX']
    _ ≈[φ; φ.norm (X a - X' a)] Z b * X a := hκX.symm.mul_left_unitary (hZ b)
  rw [AlgState.approx_iff, AlgState.norm_sub_comm] at chain
  linarith

/-- The braiding defect pointwise in `(a, b)`: when `X(0) = 1`,
`β(a, b)² ≤ [a · b = 1] α(a, b)² +
32 (E_c ℓ(c, c + b)² + E_c κ_Z(c)² + κ_X(a)² + E_c [a · c = 1] α(a, c)²)`. -/
private theorem norm_braid_sq_le [Fintype ι] [DecidableEq ι] (φ : AlgState A)
    (X Z X' Z' : (ι → Bool) → A)
    (hX : ∀ a, X a ∈ unitary A) (hZ : ∀ b, Z b ∈ unitary A) (hX' : ∀ a, X' a ∈ unitary A)
    (hZ' : ∀ b, Z' b ∈ unitary A) (hXZ' : ∀ a b, Commute (X a) (Z' b))
    (hZZ' : ∀ b b', Commute (Z b) (Z' b')) (hZX' : ∀ b a, Commute (Z b) (X' a)) (hX0 : X 0 = 1)
    (a b : ι → Bool) :
    φ.norm (Z b * X a - (BitString.signVal (a ⬝ᵥ b) : ℂ) • (X a * Z b)) ^ 2 ≤
      (if a ⬝ᵥ b = true then φ.norm (X a * Z b + Z b * X a) ^ 2 else 0) +
        32 * (𝔼 c, φ.norm (Z c * Z (c + b) - Z b) ^ 2 + 𝔼 c, φ.norm (Z c - Z' c) ^ 2 +
          φ.norm (X a - X' a) ^ 2 +
          𝔼 c, if a ⬝ᵥ c = true then φ.norm (X a * Z c + Z c * X a) ^ 2 else 0) := by
  classical
  set ℓ : (ι → Bool) → ℝ := fun c => φ.norm (Z c * Z (c + b) - Z b)
  set κZ : (ι → Bool) → ℝ := fun c => φ.norm (Z c - Z' c)
  set κX := φ.norm (X a - X' a)
  set m : (ι → Bool) → ℝ := fun c => if a ⬝ᵥ c = true then φ.norm (X a * Z c + Z c * X a) ^ 2
    else 0
  have hm : ∀ c, 0 ≤ m c := fun c => by simp only [m]; split_ifs <;> positivity
  change _ ≤ m b + 32 * (𝔼 c, ℓ c ^ 2 + 𝔼 c, κZ c ^ 2 + κX ^ 2 + 𝔼 c, m c)
  have hE : 0 ≤ 𝔼 c, ℓ c ^ 2 + 𝔼 c, κZ c ^ 2 + κX ^ 2 + 𝔼 c, m c := by
    have h1 : 0 ≤ 𝔼 c, ℓ c ^ 2 := expect_nonneg fun c _ => sq_nonneg _
    have h2 : 0 ≤ 𝔼 c, κZ c ^ 2 := expect_nonneg fun c _ => sq_nonneg _
    have h3 : 0 ≤ 𝔼 c, m c := expect_nonneg fun c _ => hm c
    positivity
  by_cases hab : a ⬝ᵥ b = true
  · have e : φ.norm (Z b * X a - (BitString.signVal (a ⬝ᵥ b) : ℂ) • (X a * Z b)) ^ 2 = m b := by
      simp only [m, hab, ite_true, BitString.signVal_true]
      congr 2
      rw [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, sub_neg_eq_add, add_comm]
    rw [e]
    linarith
  have hab' : a ⬝ᵥ b = false := by simpa using hab
  rw [hab', BitString.signVal_false, Complex.ofReal_one, one_smul]
  by_cases ha : a = 0
  · subst ha
    rw [hX0, mul_one, one_mul, sub_self, AlgState.norm_zero, zero_pow two_ne_zero]
    linarith [hm b]
  set R : (ι → Bool) → ℝ := fun c =>
    2 * ℓ c ^ 2 + 2 * κZ (c + b) ^ 2 + 2 * κX ^ 2 + m c + m (c + b)
  have hR : ∀ c, 0 ≤ R c := fun c => by
    have := hm c; have := hm (c + b); positivity
  have hpt : ∀ c, a ⬝ᵥ c = true → φ.norm (Z b * X a - X a * Z b) ^ 2 ≤ 8 * R c := by
    intro c hac
    have hacb : a ⬝ᵥ (c + b) = true := by rw [dotProduct_add, hac, hab']; rfl
    have h := norm_mul_sub_mul_le_of_anticommute φ X Z X' Z' hX hZ hX' hZ' hXZ' hZZ' hZX' a b c
    simp only [R, m, hac, hacb, ite_true]
    set x := φ.norm (Z c * Z (c + b) - Z b)
    set y := φ.norm (Z (c + b) - Z' (c + b))
    set z := φ.norm (X a * Z c + Z c * X a)
    set w := φ.norm (X a * Z (c + b) + Z (c + b) * X a)
    calc φ.norm (Z b * X a - X a * Z b) ^ 2 ≤ (2 * x + 2 * y + z + w + 2 * κX) ^ 2 :=
          pow_le_pow_left₀ (φ.norm_nonneg _) h 2
      _ ≤ 8 * (2 * x ^ 2 + 2 * y ^ 2 + 2 * κX ^ 2 + z ^ 2 + w ^ 2) := by
          linarith [sq_nonneg (2 * x + 2 * y - 2 * κX - z - w), sq_nonneg (2 * x - 2 * y),
            sq_nonneg (2 * κX - z - w), sq_nonneg (z - w)]
  -- half of the `c` have `a · c = 1`: twice the masked average of the bound
  have hβ := BitString.le_two_mul_expect_ite_of_forall ha hpt
  have hmask : 𝔼 c, (if a ⬝ᵥ c = true then 8 * R c else 0) ≤ 𝔼 c, 8 * R c :=
    expect_le_expect fun c _ => by split_ifs <;> [exact le_rfl; exact by have := hR c; positivity]
  have hshift : ∀ f : (ι → Bool) → ℝ, 𝔼 c, f (c + b) = 𝔼 c, f c := fun f => by
    simp only [add_comm _ b]
    exact Fintype.expect_add_left f b
  have hR' : 𝔼 c, R c = 2 * 𝔼 c, ℓ c ^ 2 + 2 * 𝔼 c, κZ c ^ 2 + 2 * κX ^ 2 + 2 * 𝔼 c, m c := by
    simp only [R, expect_add_distrib, ← mul_expect, Fintype.expect_const]
    rw [hshift (fun c => κZ c ^ 2), hshift m]
    ring
  rw [← mul_expect] at hmask
  have := hm b
  linarith

/-- **Braiding relations from anticommutation, consistency and linearity**, averaged
([Natarajan and Vidick, §4.3.2, Lemma 18 and §4.3.3, Lemma 19][NatarajanVidick2017]): if
`X(0) = 1`, then `E_{a,b} ‖Z(b) X(a) - (-1)^{a·b} X(a) Z(b)‖²_φ` is at most
`33 E_{a,b} [a · b = 1] ‖X(a) Z(b) + Z(b) X(a)‖²_φ +
32 (E_{c,c'} ‖Z(c) Z(c') - Z(c + c')‖²_φ + E_c κ_Z(c)² + E_a κ_X(a)²)`. -/
theorem expect_norm_braid_sq_le [Fintype ι] [DecidableEq ι] (φ : AlgState A)
    (X Z X' Z' : (ι → Bool) → A)
    (hX : ∀ a, X a ∈ unitary A) (hZ : ∀ b, Z b ∈ unitary A) (hX' : ∀ a, X' a ∈ unitary A)
    (hZ' : ∀ b, Z' b ∈ unitary A) (hXZ' : ∀ a b, Commute (X a) (Z' b))
    (hZZ' : ∀ b b', Commute (Z b) (Z' b')) (hZX' : ∀ b a, Commute (Z b) (X' a)) (hX0 : X 0 = 1) :
    𝔼 a, 𝔼 b, φ.norm (Z b * X a - (BitString.signVal (a ⬝ᵥ b) : ℂ) • (X a * Z b)) ^ 2 ≤
      33 * BitString.oddExpect (fun a b => φ.norm (X a * Z b + Z b * X a) ^ 2) +
        32 * (𝔼 c, 𝔼 c', φ.norm (Z c * Z c' - Z (c + c')) ^ 2 + 𝔼 c, φ.norm (Z c - Z' c) ^ 2 +
          𝔼 a, φ.norm (X a - X' a) ^ 2) := by
  have hpt := norm_braid_sq_le φ X Z X' Z' hX hZ hX' hZ' hXZ' hZZ' hZX' hX0
  refine (expect_le_expect fun a _ => expect_le_expect fun b _ => hpt a b).trans (le_of_eq ?_)
  have hℓ : 𝔼 _a : ι → Bool, 𝔼 b, 𝔼 c, φ.norm (Z c * Z (c + b) - Z b) ^ 2 =
      𝔼 c, 𝔼 c', φ.norm (Z c * Z c' - Z (c + c')) ^ 2 := by
    rw [Fintype.expect_const, expect_comm]
    refine expect_congr rfl fun c _ => ?_
    rw [← Fintype.expect_add_left (fun c' => φ.norm (Z c * Z c' - Z (c + c')) ^ 2) c]
    simp only [BitString.add_cancel_left]
  simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const] at hℓ ⊢
  rw [hℓ, BitString.oddExpect_def]
  ring

/-- **The Pauli-family defect from anticommutation, consistency and linearity.** Combining the
braiding bound with the Pauli-family defect bound
(`Cslib.Quantum.expect_norm_pauliFamily_sub_sq_le`): if `X(0) = 1`, the defect
`E_{p,q} ‖P(p) P(q) - P(pq)‖²_φ` of the family `P(a, b, s) = s X(a) Z(b)` is bounded by the
consistency distances, the anticommutation defects on the pairs with `a · b = 1`, and the linearity
defects of `X` and `Z`. -/
theorem expect_norm_pauliFamily_sub_sq_le_of_anticommute [Fintype ι] [DecidableEq ι]
    (φ : AlgState A) (X Z X' Z' : (ι → Bool) → A)
    (hX : ∀ a, X a ∈ unitary A) (hZ : ∀ b, Z b ∈ unitary A) (hX' : ∀ a, X' a ∈ unitary A)
    (hZ' : ∀ b, Z' b ∈ unitary A) (hXZ' : ∀ a b, Commute (X a) (Z' b))
    (hZZ' : ∀ b b', Commute (Z b) (Z' b')) (hZX' : ∀ b a, Commute (Z b) (X' a)) (hX0 : X 0 = 1) :
    𝔼 p, 𝔼 q, φ.norm (pauliFamily X Z p * pauliFamily X Z q - pauliFamily X Z (p * q)) ^ 2 ≤
      5 * (40 * 𝔼 c, φ.norm (Z c - Z' c) ^ 2 + 32 * 𝔼 a, φ.norm (X a - X' a) ^ 2 +
        33 * BitString.oddExpect (fun a b => φ.norm (X a * Z b + Z b * X a) ^ 2) +
        𝔼 a, 𝔼 a', φ.norm (X a * X a' - X (a + a')) ^ 2 +
        33 * 𝔼 b, 𝔼 b', φ.norm (Z b * Z b' - Z (b + b')) ^ 2) := by
  have h₁ := expect_norm_pauliFamily_sub_sq_le φ X Z Z' hX hZ hZ' hXZ' hZZ'
  have h₂ := expect_norm_braid_sq_le φ X Z X' Z' hX hZ hX' hZ' hXZ' hZZ' hZX' hX0
  refine h₁.trans ?_
  linarith [h₂]

end Commutation

end Cslib.Quantum
