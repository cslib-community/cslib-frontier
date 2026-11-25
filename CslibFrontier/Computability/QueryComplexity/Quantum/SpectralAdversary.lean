/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.WeightedAdversary
public import CslibFrontier.Computability.QueryComplexity.SpectralSensitivity
public import CslibFrontier.Foundations.Quantum.Measurement.Overlap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hadamard
import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm
import CslibFrontier.Foundations.Quantum.Measurement.Restrict

/-!
# Spectral and negative-weight quantum adversary bounds

This module develops the spectral adversary (`Cslib.Quantum.spectralAdversary`, denoted `ADV`) and
general negative-weight adversary (`Cslib.Quantum.generalAdversary`, denoted `ADV±`) bounds on
quantum query complexity, together with their bridges to sensitivity and weighted adversary
schemes:

* **Negative-weight adversary bound** [HoyerLeeSpalek2007], Theorem 2: for any real symmetric
  matrix `Γ` supported on `{(x, y) | P x ∧ P y ∧ f x ≠ f y}`, a `T`-query algorithm computing `f`
  on `P` with error at most `ε ≤ 1/2` satisfies
  `(1 - 2√(ε(1-ε))) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ` for Boolean functions
  (`Cslib.Quantum.one_sub_mul_opNorm_le_general_boolean`), and
  `(1 - 2√(ε(1-ε)) - ε) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ` (hence also with `- 2ε`) for arbitrary finite
  output alphabets (`Cslib.Quantum.one_sub_mul_opNorm_le_general`).
* **Nonnegative spectral adversary bound** [BarnumSaksSzegedy2003] (as reviewed in
  [HoyerLeeSpalek2007], Section 1.1, Theorem 1): when `0 ≤ Γ`, the nonnegative sign structure gives
  `(1 - δ) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ` for any uniform final-state overlap bound `δ`
  (`Cslib.Quantum.one_sub_mul_opNorm_le_spectral`).
* **Hierarchies and nonnegative barriers**:
  `Cslib.Quantum.spectralSensitivity_le_spectralAdversary` (`λ(f) ≤ ADV(f)`),
  `Cslib.Quantum.WeightScheme.le_spectralAdversary` (`Alb₃(f) ≤ ADV(f)`, original proof
  formalizing the equivalence), `Cslib.Quantum.spectralAdversary_le_generalAdversary`
  (`ADV(f) ≤ ADV±(f)`), and the Hamming-distance barrier
  `k · ‖Γ‖ ≤ N · maxDiffNorm Γ` for `0 ≤ Γ`
  (`Cslib.Quantum.spectralAdversary_le_div_of_hammingDist_ge`).

## Main definitions

* `Cslib.Quantum.diffMatrix`: the coordinate-disagreement matrix `Dᵢ[x, y] = 1` iff `xᵢ ≠ yᵢ`.
* `Cslib.Quantum.maxDiffNorm`: `max_{i < N} ‖Γ ∘ Dᵢ‖` (`0` when `N = 0`).
* `Cslib.Quantum.IsAdversaryMatrix`: support predicate `Γ[x, y] ≠ 0 → P x ∧ P y ∧ f x ≠ f y`.
* `Cslib.Quantum.spectralAdversary`: supremum of `‖Γ‖ / maxDiffNorm Γ` over nonnegative
  symmetric adversary matrices.
* `Cslib.Quantum.generalAdversary`: supremum of `‖Γ‖ / maxDiffNorm Γ` over all real symmetric
  adversary matrices.

## Main results

* `Cslib.Quantum.spectralAdversary_le_iff` and `Cslib.Quantum.generalAdversary_le_iff`:
  strict-`module` upper-bound characterizations of `ADV(f)` and `ADV±(f)`.
* `Cslib.Quantum.one_sub_mul_generalAdversary_le_boolean`: negative-weight lower bound for
  Boolean outputs.
* `Cslib.Quantum.one_sub_mul_generalAdversary_le` and
  `Cslib.Quantum.one_sub_mul_generalAdversary_le_hls`: negative-weight lower bounds for finite
  output alphabets.
* `Cslib.Quantum.one_sub_mul_spectralAdversary_le`: spectral adversary lower bound.
* `Cslib.Quantum.spectralSensitivity_le_spectralAdversary`,
  `Cslib.Quantum.WeightScheme.le_spectralAdversary`, and
  `Cslib.Quantum.spectralAdversary_le_generalAdversary`: method hierarchy.
* `Cslib.Quantum.spectralAdversary_le_div_of_hammingDist_ge`: Hamming-distance barrier on `ADV`.

## References

* [H. Barnum, M. Saks, M. Szegedy, *Quantum query complexity and semidefinite programming*]
  [BarnumSaksSzegedy2003] (definition and theorem reviewed in [HoyerLeeSpalek2007], Section 1.1)
* [P. Høyer, T. Lee, R. Špalek, *Negative weights make adversaries stronger*][HoyerLeeSpalek2007]
* [S. Zhang, *On the power of Ambainis lower bounds*][Zhang2005]
-/

public section

namespace Cslib.Quantum

open Finset Function Matrix
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

variable {N : ℕ}

section Helpers

private theorem sum_sq_mul_coord_eq {κ ι : Type*} [Fintype κ] [Fintype ι]
    (u : EuclideanSpace ℝ κ) (φ : κ → EuclideanSpace ℂ ι) :
    ∑ p : ι × Bool, ∑ x,
        (u.ofLp x * if p.2 then ((φ x).ofLp p.1).im else ((φ x).ofLp p.1).re) ^ 2 =
      ∑ x, (u.ofLp x * ‖φ x‖) ^ 2 := by
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, mul_pow, EuclideanSpace.norm_sq_eq, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Fintype.sum_bool,
    Bool.false_eq_true, ↓reduceIte]
  ring

/-- Vector-matrix-inner-product Cauchy–Schwarz bound:
`|∑ x y, M[x, y] u_x v_y Re⟨φ_x, ψ_y⟩| ≤ ‖M‖ √(∑ x u_x² ‖φ_x‖²) √(∑ y v_y² ‖ψ_y‖²)`. -/
private theorem abs_sum_mul_re_inner_le {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (M : Matrix κ κ ℝ) (u v : EuclideanSpace ℝ κ) (φ ψ : κ → EuclideanSpace ℂ ι) :
    |∑ x, ∑ y, M x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (ψ y))| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ *
        √(∑ x, (u.ofLp x * ‖φ x‖) ^ 2) * √(∑ y, (v.ofLp y * ‖ψ y‖) ^ 2) := by
  let coord (χ : κ → EuclideanSpace ℂ ι) (x : κ) (p : ι × Bool) : ℝ :=
    if p.2 then ((χ x).ofLp p.1).im else ((χ x).ofLp p.1).re
  have hre (x y : κ) : RCLike.re (inner ℂ (φ x) (ψ y)) =
      ∑ p : ι × Bool, coord φ x p * coord ψ y p := by
    rw [PiLp.inner_apply, map_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun k _ => ?_
    simp only [RCLike.inner_apply', RCLike.re_to_complex, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, coord]
    ring
  have hrewrite :
      (∑ x, ∑ y, M x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (ψ y))) =
      ∑ p : ι × Bool, ∑ x, ∑ y,
        (u.ofLp x * coord φ x p) * M x y * (v.ofLp y * coord ψ y p) := by
    simp only [hre, mul_sum]
    conv_lhs => enter [2, x]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [hrewrite, Matrix.l2_opNorm_toEuclideanCLM]
  calc |∑ p : ι × Bool, ∑ x, ∑ y,
        (u.ofLp x * coord φ x p) * M x y * (v.ofLp y * coord ψ y p)|
      ≤ ∑ p : ι × Bool, ‖M‖ * √(∑ x, (u.ofLp x * coord φ x p) ^ 2) *
          √(∑ y, (v.ofLp y * coord ψ y p) ^ 2) :=
          (abs_sum_le_sum_abs _ _).trans
            (sum_le_sum fun p _ => Matrix.abs_sum_mul_le_l2_opNorm M _ _)
    _ = ‖M‖ * ∑ p : ι × Bool,
          √(∑ x, (u.ofLp x * coord φ x p) ^ 2) * √(∑ y, (v.ofLp y * coord ψ y p) ^ 2) := by
          simp only [mul_assoc, ← mul_sum]
    _ ≤ ‖M‖ * (√(∑ p : ι × Bool, ∑ x, (u.ofLp x * coord φ x p) ^ 2) *
          √(∑ p : ι × Bool, ∑ y, (v.ofLp y * coord ψ y p) ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le univ
            (fun _ => sum_nonneg fun _ _ => sq_nonneg _)
            (fun _ => sum_nonneg fun _ _ => sq_nonneg _)) (norm_nonneg _)
    _ = ‖M‖ * √(∑ x, (u.ofLp x * ‖φ x‖) ^ 2) * √(∑ y, (v.ofLp y * ‖ψ y‖) ^ 2) := by
          rw [sum_sq_mul_coord_eq u φ, sum_sq_mul_coord_eq v ψ, mul_assoc]

/-- Algebraic bound maximizing `√((1 - p) q) + √(p (1 - q))` for `0 ≤ p, q ≤ ε ≤ 1/2`. -/
private theorem mul_add_mul_le_two_mul_sqrt {a b p q ε : ℝ}
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hpε : p ≤ ε) (hqε : q ≤ ε) (hε : 2 * ε ≤ 1)
    (hap : a ^ 2 + p ≤ 1) (hbq : b ^ 2 + q ≤ 1) :
    a * √q + √p * b ≤ 2 * √(ε * (1 - ε)) := by
  have h1p : 0 ≤ 1 - p := by linarith
  have h1q : 0 ≤ 1 - q := by linarith
  have hε1 : 0 ≤ 1 - ε := by linarith
  have hε0 : 0 ≤ ε := hp0.trans hpε
  have hsum : a * √q + √p * b ≤ √((1 - p) * q) + √(p * (1 - q)) := by
    rw [Real.sqrt_mul h1p, Real.sqrt_mul hp0]
    gcongr <;> exact Real.le_sqrt_of_sq_le (by linarith)
  have hquad {x : ℝ} (hx0 : 0 ≤ x) (hxε : x ≤ ε) : x * (1 - x) ≤ ε * (1 - ε) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hxε) (by linarith : 0 ≤ 1 - ε - x)]
  have hprod : √((1 - p) * q) * √(p * (1 - q)) ≤ ε * (1 - ε) := by
    rw [← Real.sqrt_mul (mul_nonneg h1p hq0)]
    exact (Real.sqrt_le_sqrt <|
      (mul_le_mul (hquad hp0 hpε) (hquad hq0 hqε) (mul_nonneg hq0 h1q)
        (mul_nonneg hε0 hε1)).trans_eq' (by ring)).trans_eq
      (Real.sqrt_mul_self (mul_nonneg hε0 hε1))
  have hlin : (1 - p) * q + p * (1 - q) ≤ 2 * (ε * (1 - ε)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hpε) (by linarith : 0 ≤ 1 - 2 * q),
      mul_nonneg (sub_nonneg.2 hqε) (by linarith : 0 ≤ 1 - 2 * ε)]
  have hsq : (√((1 - p) * q) + √(p * (1 - q))) ^ 2 ≤ (2 * √(ε * (1 - ε))) ^ 2 := by
    rw [add_sq, Real.sq_sqrt (mul_nonneg h1p hq0), Real.sq_sqrt (mul_nonneg hp0 h1q),
      mul_pow, Real.sq_sqrt (mul_nonneg hε0 hε1)]
    linarith
  exact hsum.trans ((sq_le_sq₀ (by positivity) (by positivity)).1 hsq)

end Helpers

section Definitions

/-- Coordinate-disagreement matrix `Dᵢ`: entry `(x, y)` is `1` if `xᵢ ≠ yᵢ` and `0` otherwise. -/
@[expose] def diffMatrix (i : Fin N) : Matrix (BitString N) (BitString N) ℝ :=
  Matrix.of fun x y => if x i ≠ y i then 1 else 0

@[simp] theorem diffMatrix_apply (i : Fin N) (x y : BitString N) :
    diffMatrix i x y = if x i ≠ y i then 1 else 0 :=
  rfl

theorem diffMatrix_transpose (i : Fin N) : (diffMatrix i)ᵀ = diffMatrix i := by
  ext x y
  simp [ne_comm]

/-- Maximum coordinate-masked operator norm `max_{i < N} ‖Γ ∘ Dᵢ‖` (`0` when `N = 0`). -/
noncomputable def maxDiffNorm (Γ : Matrix (BitString N) (BitString N) ℝ) : ℝ :=
  (((univ : Finset (Fin N)).sup fun i =>
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix i))‖₊ : NNReal) : ℝ)

theorem maxDiffNorm_nonneg (Γ : Matrix (BitString N) (BitString N) ℝ) : 0 ≤ maxDiffNorm Γ :=
  NNReal.coe_nonneg _

theorem norm_toEuclideanCLM_hadamard_le_maxDiffNorm
    (Γ : Matrix (BitString N) (BitString N) ℝ) (i : Fin N) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix i))‖ ≤ maxDiffNorm Γ := by
  unfold maxDiffNorm
  exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun j =>
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix j))‖₊) (mem_univ i))

theorem maxDiffNorm_le_iff {Γ : Matrix (BitString N) (BitString N) ℝ} {K : ℝ} (hK : 0 ≤ K) :
    maxDiffNorm Γ ≤ K ↔ ∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix i))‖ ≤ K := by
  refine ⟨fun h i => (norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ i).trans h, fun h => ?_⟩
  unfold maxDiffNorm
  rw [← Real.coe_toNNReal K hK, NNReal.coe_le_coe, Finset.sup_le_iff]
  intro i _
  exact (Real.le_toNNReal_iff_coe_le hK).2 (h i)

/-- Support condition for an adversary matrix of a partial function `(P, f)`: every nonzero
entry `(x, y)` connects valid inputs with distinct outputs. -/
@[expose] def IsAdversaryMatrix {α : Type*} (P : BitString N → Prop) (f : BitString N → α)
    (Γ : Matrix (BitString N) (BitString N) ℝ) : Prop :=
  ∀ x y, Γ x y ≠ 0 → P x ∧ P y ∧ f x ≠ f y

private theorem abs_le_maxDiffNorm {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {Γ : Matrix (BitString N) (BitString N) ℝ} (hΓ : IsAdversaryMatrix P f Γ) (x y : BitString N) :
    |Γ x y| ≤ maxDiffNorm Γ := by
  by_cases hxy0 : Γ x y = 0
  · simp only [hxy0, abs_zero, maxDiffNorm_nonneg Γ]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 fun h => (hΓ x y hxy0).2.2 (congrArg f h)
  have hle := Matrix.abs_entry_le_norm_toEuclideanCLM (Γ.hadamard (diffMatrix i)) x y
  simp only [Matrix.hadamard_apply, diffMatrix_apply, hi, ne_eq, not_false_eq_true, ↓reduceIte,
    mul_one] at hle
  exact hle.trans (norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ i)

theorem eq_zero_of_maxDiffNorm_eq_zero {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {Γ : Matrix (BitString N) (BitString N) ℝ} (hΓ : IsAdversaryMatrix P f Γ)
    (h0 : maxDiffNorm Γ = 0) : Γ = 0 :=
  Matrix.ext fun x y => abs_nonpos_iff.1 ((abs_le_maxDiffNorm hΓ x y).trans_eq h0)

/-- **Nonnegative spectral adversary bound `ADV(f)`** ([BarnumSaksSzegedy2003], as reviewed in
[HoyerLeeSpalek2007], Section 1.1, Definition 1): the supremum of `‖Γ‖ / maxDiffNorm Γ` over real
symmetric nonnegative matrices supported on pairs `(x, y)` with `P x`, `P y`, and `f x ≠ f y`. -/
noncomputable def spectralAdversary {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    ℝ :=
  sSup {r : ℝ | ∃ Γ : Matrix (BitString N) (BitString N) ℝ,
    Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧ IsAdversaryMatrix P f Γ ∧
      r = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ}

/-- **Negative-weight adversary bound `ADV±(f)`** ([HoyerLeeSpalek2007], Definition 2):
the supremum of `‖Γ‖ / maxDiffNorm Γ` over all real symmetric matrices supported on pairs
`(x, y)` with `P x`, `P y`, and `f x ≠ f y`. -/
noncomputable def generalAdversary {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    ℝ :=
  sSup {r : ℝ | ∃ Γ : Matrix (BitString N) (BitString N) ℝ,
    Γ.IsSymm ∧ IsAdversaryMatrix P f Γ ∧
      r = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ}

private theorem norm_div_maxDiffNorm_le_card {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ ≤ (Fintype.card (BitString N) : ℝ) := by
  rcases (maxDiffNorm_nonneg Γ).eq_or_lt with h0 | hpos
  · simp only [← h0, div_zero, Nat.cast_nonneg]
  have hsum (g : BitString N → ℝ) (hg : ∀ z, g z ≤ maxDiffNorm Γ) :
      ∑ z, g z ≤ (Fintype.card (BitString N) : ℝ) * maxDiffNorm Γ :=
    (sum_le_sum fun z _ => hg z).trans_eq (by simp only [sum_const, card_univ, nsmul_eq_mul])
  have hschur := Matrix.opNorm_toEuclideanCLM_le_sqrt Γ (by positivity) (by positivity)
    (fun x => hsum _ (abs_le_maxDiffNorm hΓ x)) (fun y => hsum _ (abs_le_maxDiffNorm hΓ · y))
  rw [Real.sqrt_mul_self (by positivity)] at hschur
  exact (div_le_iff₀ hpos).2 hschur

theorem bddAbove_generalAdversary {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    BddAbove {r : ℝ | ∃ Γ : Matrix (BitString N) (BitString N) ℝ,
      Γ.IsSymm ∧ IsAdversaryMatrix P f Γ ∧
        r = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ} :=
  ⟨Fintype.card (BitString N), by
    rintro r ⟨Γ, -, hΓ, rfl⟩
    exact norm_div_maxDiffNorm_le_card hΓ⟩

theorem bddAbove_spectralAdversary {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    BddAbove {r : ℝ | ∃ Γ : Matrix (BitString N) (BitString N) ℝ,
      Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧ IsAdversaryMatrix P f Γ ∧
        r = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ} :=
  ⟨Fintype.card (BitString N), by
    rintro r ⟨Γ, -, -, hΓ, rfl⟩
    exact norm_div_maxDiffNorm_le_card hΓ⟩

theorem spectralAdversary_nonneg {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    0 ≤ spectralAdversary P f :=
  Real.sSup_nonneg fun _ ⟨Γ, _, _, _, h⟩ => h ▸ div_nonneg (norm_nonneg _) (maxDiffNorm_nonneg Γ)

theorem generalAdversary_nonneg {α : Type*} (P : BitString N → Prop) (f : BitString N → α) :
    0 ≤ generalAdversary P f :=
  Real.sSup_nonneg fun _ ⟨Γ, _, _, h⟩ => h ▸ div_nonneg (norm_nonneg _) (maxDiffNorm_nonneg Γ)

theorem le_spectralAdversary {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {Γ : Matrix (BitString N) (BitString N) ℝ} (hsym : Γ.IsSymm) (hnonneg : ∀ x y, 0 ≤ Γ x y)
    (hΓ : IsAdversaryMatrix P f Γ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ ≤ spectralAdversary P f :=
  le_csSup (bddAbove_spectralAdversary P f) ⟨Γ, hsym, hnonneg, hΓ, rfl⟩

theorem le_generalAdversary {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {Γ : Matrix (BitString N) (BitString N) ℝ} (hsym : Γ.IsSymm)
    (hΓ : IsAdversaryMatrix P f Γ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ ≤ generalAdversary P f :=
  le_csSup (bddAbove_generalAdversary P f) ⟨Γ, hsym, hΓ, rfl⟩

private theorem div_maxDiffNorm_le_of_mul {Γ : Matrix (BitString N) (BitString N) ℝ}
    {K : ℝ} (hK : 0 ≤ K)
    (h : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ K * maxDiffNorm Γ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ ≤ K := by
  rcases (maxDiffNorm_nonneg Γ).eq_or_lt with h0 | hm
  · simp only [← h0, div_zero, hK]
  · exact (div_le_iff₀ hm).2 h

private theorem mul_maxDiffNorm_of_div_le {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ) {K : ℝ}
    (h : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ ≤ K) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ K * maxDiffNorm Γ := by
  rcases (maxDiffNorm_nonneg Γ).eq_or_lt with h0 | hm
  · rw [← h0, mul_zero, eq_zero_of_maxDiffNorm_eq_zero hΓ h0.symm, map_zero, norm_zero]
  · exact (div_le_iff₀ hm).1 h

/-- Upper-bound characterization of `spectralAdversary` (`ADV(f) ≤ K` for `K ≥ 0`). -/
theorem spectralAdversary_le_iff {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {K : ℝ} (hK : 0 ≤ K) :
    spectralAdversary P f ≤ K ↔
      ∀ Γ : Matrix (BitString N) (BitString N) ℝ, Γ.IsSymm → (∀ x y, 0 ≤ Γ x y) →
        IsAdversaryMatrix P f Γ → ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ K * maxDiffNorm Γ := by
  refine ⟨fun hle Γ hsym hnonneg hΓ =>
    mul_maxDiffNorm_of_div_le hΓ ((le_spectralAdversary hsym hnonneg hΓ).trans hle), fun h => ?_⟩
  refine Real.sSup_le ?_ hK
  rintro r ⟨Γ, hsym, hnonneg, hΓ, rfl⟩
  exact div_maxDiffNorm_le_of_mul hK (h Γ hsym hnonneg hΓ)

/-- Upper-bound characterization of `generalAdversary` (`ADV±(f) ≤ K` for `K ≥ 0`). -/
theorem generalAdversary_le_iff {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    {K : ℝ} (hK : 0 ≤ K) :
    generalAdversary P f ≤ K ↔
      ∀ Γ : Matrix (BitString N) (BitString N) ℝ, Γ.IsSymm →
        IsAdversaryMatrix P f Γ → ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ K * maxDiffNorm Γ := by
  refine ⟨fun hle Γ hsym hΓ =>
    mul_maxDiffNorm_of_div_le hΓ ((le_generalAdversary hsym hΓ).trans hle), fun h => ?_⟩
  refine Real.sSup_le ?_ hK
  rintro r ⟨Γ, hsym, hΓ, rfl⟩
  exact div_maxDiffNorm_le_of_mul hK (h Γ hsym hΓ)

/-- `ADV(f) ≤ ADV±(f)`: the negative-weight adversary bound is at least the nonnegative spectral
adversary bound. -/
theorem spectralAdversary_le_generalAdversary {α : Type*} (P : BitString N → Prop)
    (f : BitString N → α) : spectralAdversary P f ≤ generalAdversary P f :=
  Real.sSup_le (fun _ ⟨_, hsym, _, hΓ, h⟩ => h ▸ le_generalAdversary hsym hΓ)
    (generalAdversary_nonneg P f)

end Definitions

section ProgressCore

variable {W : Type*} [Fintype W]

/-- Bilinear adversary progress measure `W(φ) = ∑_{x,y} Γ[x, y] u_x v_y Re⟨φ_x, φ_y⟩`. -/
private noncomputable def advForm (Γ : Matrix (BitString N) (BitString N) ℝ)
    (u v : EuclideanSpace ℝ (BitString N)) (φ : BitString N → State N W) : ℝ :=
  ∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (φ y))

private theorem advForm_step_eq (Γ : Matrix (BitString N) (BitString N) ℝ)
    (u v : EuclideanSpace ℝ (BitString N))
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (t : ℕ) :
    advForm Γ u v (fun x => run U ψ₀ x t) - advForm Γ u v (fun x => run U ψ₀ x (t + 1)) =
      2 * ∑ i : Fin N, ∑ x, ∑ y,
        (Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
          RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t))) := by
  have hdiff (x y : BitString N) :
      RCLike.re (inner ℂ (run U ψ₀ x t) (run U ψ₀ y t)) -
        RCLike.re (inner ℂ (run U ψ₀ x (t + 1)) (run U ψ₀ y (t + 1))) =
      2 * ∑ i : Fin N, diffMatrix i x y *
        RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t))) := by
    have hrun : inner ℂ (run U ψ₀ x (t + 1)) (run U ψ₀ y (t + 1)) =
        inner ℂ (phaseOracle x (run U ψ₀ x t)) (phaseOracle y (run U ψ₀ y t)) :=
      (U (t + 1)).inner_map_map _ _
    have hre2 (z : ℂ) : RCLike.re (2 * z) = 2 * RCLike.re z := by
      simp [RCLike.re_to_complex]
    rw [hrun, inner_phaseOracle_phaseOracle, ← map_sub, sub_sub_cancel, hre2, map_sum,
      Finset.sum_filter]
    congr 1
    exact sum_congr rfl fun i _ => by
      simp only [diffMatrix_apply, ne_eq]; split_ifs <;> simp only [one_mul, zero_mul]
  simp only [advForm, ← sum_sub_distrib, ← mul_sub, hdiff, mul_sum]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun x _ => sum_congr rfl fun y _ => by
    rw [Matrix.hadamard_apply]; ring

private theorem advForm_step_sub_le (Γ : Matrix (BitString N) (BitString N) ℝ)
    (u v : EuclideanSpace ℝ (BitString N)) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (t : ℕ) :
    |advForm Γ u v (fun x => run U ψ₀ x t) - advForm Γ u v (fun x => run U ψ₀ x (t + 1))| ≤
      2 * maxDiffNorm Γ := by
  have hctrl (w : EuclideanSpace ℝ (BitString N)) (hw : ‖w‖ ≤ 1) :
      ∑ i : Fin N, ∑ x, (w.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2 ≤ 1 := by
    rw [sum_comm]
    calc ∑ x, ∑ i : Fin N, (w.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2
        = ∑ x, w.ofLp x ^ 2 * ∑ i : Fin N, ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 :=
            sum_congr rfl fun x _ => by simp only [mul_pow, ← mul_sum]
      _ ≤ ∑ x, w.ofLp x ^ 2 := sum_le_sum fun x _ =>
            mul_le_of_le_one_right (sq_nonneg _) (sum_sq_norm_ctrlProj_le U hψ₀ x t)
      _ ≤ 1 := (EuclideanSpace.norm_le_one_iff_sum_sq_le_one w).1 hw
  rw [advForm_step_eq, abs_mul, abs_of_nonneg zero_le_two]
  refine mul_le_mul_of_nonneg_left ?_ zero_le_two
  calc |∑ i : Fin N, ∑ x, ∑ y,
        (Γ.hadamard (diffMatrix i)) x y * u.ofLp x * v.ofLp y *
          RCLike.re (inner ℂ (ctrlProj i (run U ψ₀ x t)) (ctrlProj i (run U ψ₀ y t)))|
      ≤ ∑ i : Fin N, maxDiffNorm Γ *
          (√(∑ x, (u.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2) *
           √(∑ y, (v.ofLp y * ‖ctrlProj i (run U ψ₀ y t)‖) ^ 2)) :=
          (abs_sum_le_sum_abs _ _).trans <| sum_le_sum fun i _ => by
            have hb := abs_sum_mul_re_inner_le (Γ.hadamard (diffMatrix i)) u v
              (fun x => ctrlProj i (run U ψ₀ x t)) (fun y => ctrlProj i (run U ψ₀ y t))
            rw [mul_assoc] at hb
            exact hb.trans (mul_le_mul_of_nonneg_right
              (norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ i) (by positivity))
    _ = maxDiffNorm Γ * ∑ i : Fin N,
          √(∑ x, (u.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2) *
          √(∑ y, (v.ofLp y * ‖ctrlProj i (run U ψ₀ y t)‖) ^ 2) := (mul_sum _ _ _).symm
    _ ≤ maxDiffNorm Γ *
          (√(∑ i : Fin N, ∑ x, (u.ofLp x * ‖ctrlProj i (run U ψ₀ x t)‖) ^ 2) *
           √(∑ i : Fin N, ∑ y, (v.ofLp y * ‖ctrlProj i (run U ψ₀ y t)‖) ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le univ
            (fun _ => sum_nonneg fun _ _ => sq_nonneg _)
            (fun _ => sum_nonneg fun _ _ => sq_nonneg _)) (maxDiffNorm_nonneg Γ)
    _ ≤ maxDiffNorm Γ * (1 * 1) := mul_le_mul_of_nonneg_left
          (mul_le_mul (Real.sqrt_le_one.2 (hctrl u hu)) (Real.sqrt_le_one.2 (hctrl v hv))
            (Real.sqrt_nonneg _) zero_le_one)
          (maxDiffNorm_nonneg Γ)
    _ = maxDiffNorm Γ := by rw [mul_one, mul_one]

private theorem abs_inner_toEuclideanCLM_sub_advForm_le
    (Γ : Matrix (BitString N) (BitString N) ℝ)
    (u v : EuclideanSpace ℝ (BitString N)) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) :
    |inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) - advForm Γ u v (fun x => run U ψ₀ x T)| ≤
      2 * T * maxDiffNorm Γ := by
  have h0 : inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) =
      advForm Γ u v (fun x => run U ψ₀ x 0) := by
    have hinner : inner ℂ (U 0 ψ₀) (U 0 ψ₀) = (1 : ℂ) := by
      rw [LinearIsometry.inner_map_map, inner_self_eq_norm_sq_to_K, hψ₀]; norm_num
    rw [Matrix.inner_toEuclideanCLM]
    simp only [advForm, run, hinner, dotProduct, Matrix.mulVec, mul_sum, RCLike.one_re]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [h0, (sum_range_sub' (fun t => advForm Γ u v (fun x => run U ψ₀ x t)) T).symm]
  calc |∑ t ∈ range T,
        (advForm Γ u v (fun x => run U ψ₀ x t) -
          advForm Γ u v (fun x => run U ψ₀ x (t + 1)))|
      ≤ ∑ _t ∈ range T, 2 * maxDiffNorm Γ := (abs_sum_le_sum_abs _ _).trans <|
          sum_le_sum fun t _ => advForm_step_sub_le Γ u v hu hv U hψ₀ t
    _ = 2 * T * maxDiffNorm Γ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

private theorem advForm_proj_terms_le
    (Γ : Matrix (BitString N) (BitString N) ℝ)
    (u v : EuclideanSpace ℝ (BitString N)) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (αs βs : BitString N → State N W) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (hnorm : ∀ x, ‖αs x‖ ^ 2 + ‖βs x‖ ^ 2 ≤ 1 ∧ ‖βs x‖ ^ 2 ≤ ε) :
    |∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (αs x) (βs y)) +
        ∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (αs y))| ≤
      2 * √(ε * (1 - ε)) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ∧
      |advForm Γ u v βs| ≤ ε * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by
  have hvec (w : EuclideanSpace ℝ (BitString N)) (hw : ‖w‖ ≤ 1) :
      (√(∑ x, (w.ofLp x * ‖αs x‖) ^ 2)) ^ 2 + ∑ x, (w.ofLp x * ‖βs x‖) ^ 2 ≤ 1 ∧
      ∑ x, (w.ofLp x * ‖βs x‖) ^ 2 ≤ ε := by
    have hw1 := (EuclideanSpace.norm_le_one_iff_sum_sq_le_one w).1 hw
    rw [Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _), ← sum_add_distrib]
    refine ⟨(sum_le_sum fun x _ => ?_).trans hw1,
      (sum_le_sum fun x _ => ?_).trans <| by
        rw [← sum_mul]; exact (mul_le_mul_of_nonneg_right hw1 hε0).trans_eq (one_mul ε)⟩
    · calc (w.ofLp x * ‖αs x‖) ^ 2 + (w.ofLp x * ‖βs x‖) ^ 2
          = w.ofLp x ^ 2 * (‖αs x‖ ^ 2 + ‖βs x‖ ^ 2) := by ring
        _ ≤ w.ofLp x ^ 2 := mul_le_of_le_one_right (sq_nonneg _) (hnorm x).1
    · rw [mul_pow]; exact mul_le_mul_of_nonneg_left (hnorm x).2 (sq_nonneg _)
  have hAB := mul_add_mul_le_two_mul_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
    (sum_nonneg fun _ _ => sq_nonneg _) (hvec u hu).2 (hvec v hv).2 hε
    (hvec u hu).1 (hvec v hv).1
  have hBB : √(∑ x, (u.ofLp x * ‖βs x‖) ^ 2) * √(∑ y, (v.ofLp y * ‖βs y‖) ^ 2) ≤ ε :=
    (mul_le_mul (Real.sqrt_le_sqrt (hvec u hu).2) (Real.sqrt_le_sqrt (hvec v hv).2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hε0)
  refine ⟨(abs_add_le _ _).trans <| (add_le_add (abs_sum_mul_re_inner_le Γ u v αs βs)
      (abs_sum_mul_re_inner_le Γ u v βs αs)).trans <| ?_, ?_⟩
  · calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * _ * _ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * _ * _
        = (_ * _ + _ * _) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by ring
      _ ≤ 2 * √(ε * (1 - ε)) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ :=
          mul_le_mul_of_nonneg_right hAB (norm_nonneg _)
  · exact (abs_sum_mul_re_inner_le Γ u v βs βs).trans <| by
      rw [mul_assoc, mul_comm ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖]
      exact mul_le_mul_of_nonneg_right hBB (norm_nonneg _)

private theorem abs_advForm_final_le_of_proj {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ)
    (u v : EuclideanSpace ℝ (BitString N)) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    |advForm Γ u v (fun x => run U ψ₀ x T)| ≤
      (2 * √(ε * (1 - ε)) + ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ∧
      (∀ _h : (∀ x y, P x → P y → f x ≠ f y →
          ∀ k, k ∉ S_out (f x) → k ∈ S_out (f y)),
        |advForm Γ u v (fun x => run U ψ₀ x T)| ≤
          2 * √(ε * (1 - ε)) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖) := by
  classical
  let αs : BitString N → State N W := fun x =>
    if P x then projOutcomes (· ∈ S_out (f x)) (run U ψ₀ x T) else 0
  let βs : BitString N → State N W := fun x =>
    if P x then projOutcomes (fun k => ¬(k ∈ S_out (f x))) (run U ψ₀ x T) else 0
  have hnorm_sq (x : BitString N) : ‖αs x‖ ^ 2 + ‖βs x‖ ^ 2 ≤ 1 ∧ ‖βs x‖ ^ 2 ≤ ε := by
    by_cases hx : P x
    · have hα : ‖αs x‖ ^ 2 = measureProb (run U ψ₀ x T) (S_out (f x)) := by
        simp only [αs, hx, ↓reduceIte, norm_projOutcomes_sq_mem]
      have hcomp : univ.filter (fun k => ¬(k ∈ S_out (f x))) = (S_out (f x))ᶜ := by
        ext k; simp only [mem_filter, mem_univ, true_and, mem_compl]
      have hβ : ‖βs x‖ ^ 2 = 1 - measureProb (run U ψ₀ x T) (S_out (f x)) := by
        simp only [βs, hx, ↓reduceIte, norm_projOutcomes_sq, hcomp, measureProb_compl, norm_run,
          hψ₀, one_pow]
      exact ⟨by linarith, by linarith [herr x hx]⟩
    · simp only [αs, βs, hx, ↓reduceIte, norm_zero, zero_pow two_ne_zero, add_zero, zero_le_one,
        hε0, and_self]
  have ⟨hcross, hββ⟩ := advForm_proj_terms_le Γ u v hu hv αs βs hε0 hε hnorm_sq
  have hsum_all : advForm Γ u v (fun x => run U ψ₀ x T) =
      (∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (αs x) (βs y)) +
        ∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (βs x) (αs y))) +
      advForm Γ u v βs := by
    simp only [advForm, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    by_cases hxy0 : Γ x y = 0
    · simp only [hxy0, zero_mul, add_zero]
    · obtain ⟨hx, hy, hf⟩ := hΓ x y hxy0
      have haa : inner ℂ (αs x) (αs y) = 0 := by
        simp only [αs, hx, hy, ↓reduceIte]
        exact inner_projOutcomes_eq_zero _ _
          (fun _ ⟨h1, h2⟩ => Finset.disjoint_left.1 (hdisj hf) h1 h2) _ _
      rw [show run U ψ₀ x T = αs x + βs x by
          simp only [αs, βs, hx, ↓reduceIte]; exact (projOutcomes_add_projOutcomes_not _ _).symm,
        show run U ψ₀ y T = αs y + βs y by
          simp only [αs, βs, hy, ↓reduceIte]; exact (projOutcomes_add_projOutcomes_not _ _).symm,
        inner_add_left, inner_add_right, inner_add_right, haa, zero_add]
      simp only [map_add]; ring
  refine ⟨hsum_all ▸ (abs_add_le _ _).trans ((add_le_add hcross hββ).trans_eq (by ring)), ?_⟩
  intro hβ
  have hβzero : advForm Γ u v βs = 0 := sum_eq_zero fun x _ => sum_eq_zero fun y _ => by
    by_cases hxy0 : Γ x y = 0
    · simp only [hxy0, zero_mul]
    · obtain ⟨hx, hy, hf⟩ := hΓ x y hxy0
      have hbb : inner ℂ (βs x) (βs y) = 0 := by
        simp only [βs, hx, hy, ↓reduceIte]
        exact inner_projOutcomes_eq_zero _ _ (fun k ⟨h1, h2⟩ => h2 (hβ x y hx hy hf k h1)) _ _
      simp only [hbb, map_zero, mul_zero]
  rwa [hsum_all, hβzero, add_zero]

private theorem one_sub_mul_opNorm_le_of_advForm
    (Γ : Matrix (BitString N) (BitString N) ℝ)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    {c : ℝ} (hc : 0 ≤ c)
    (hfin : ∀ u v : EuclideanSpace ℝ (BitString N), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      |advForm Γ u v (fun x => run U ψ₀ x T)| ≤ c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖) :
    (1 - c) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ 2 * T * maxDiffNorm Γ := by
  have hbound := Matrix.opNorm_toEuclideanCLM_le_of_inner Γ
    (add_nonneg (mul_nonneg hc (norm_nonneg _))
      (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (maxDiffNorm_nonneg _)))
    fun u v hu hv => by
      have ht := abs_inner_toEuclideanCLM_sub_advForm_le Γ u v hu hv U hψ₀ T
      have hf := hfin u v hu hv
      linarith [le_abs_self (inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v)),
        (abs_le.1 ht).2, (abs_le.1 hf).2]
  linarith

/-- **Negative-weight adversary bound for Boolean outputs** ([HoyerLeeSpalek2007], Theorem 2):
for any real matrix `Γ` supported on `{(x, y) | P x ∧ P y ∧ f x ≠ f y}` and any `T`-query
algorithm accepting `x ∈ P` with `f x = true` with probability at least `1 - ε` and accepting
`x ∈ P` with `f x = false` with probability at most `ε ≤ 1/2`,
`(1 - 2√(ε(1-ε))) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ`. -/
theorem one_sub_mul_opNorm_le_general_boolean {P : BitString N → Prop}
    {f : BitString N → Bool} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_acc : Finset (Fin N × Bool × W)) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (h₁ : ∀ x, P x → f x = true → 1 - ε ≤ measureProb (run U ψ₀ x T) S_acc)
    (h₀ : ∀ x, P x → f x = false → measureProb (run U ψ₀ x T) S_acc ≤ ε) :
    (1 - 2 * √(ε * (1 - ε))) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤
      2 * T * maxDiffNorm Γ := by
  classical
  let S_out : Bool → Finset (Fin N × Bool × W) := fun b => if b then S_acc else S_accᶜ
  have hdisj : Pairwise (Disjoint on S_out) := fun b₁ b₂ hne => by
    cases b₁ <;> cases b₂ <;>
      simp only [Function.onFun, S_out, Bool.false_eq_true, ↓reduceIte] <;>
      first | exact absurd rfl hne | exact disjoint_compl_left | exact disjoint_compl_right
  have herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x)) := fun x hx => by
    cases hfx : f x
    · simp only [S_out, Bool.false_eq_true, ↓reduceIte, measureProb_compl, norm_run, hψ₀, one_pow]
      linarith [h₀ x hx hfx]
    · simpa only [S_out, ↓reduceIte] using h₁ x hx hfx
  exact one_sub_mul_opNorm_le_of_advForm Γ U hψ₀ T
    (mul_nonneg zero_le_two (Real.sqrt_nonneg _))
    fun u v hu hv =>
      (abs_advForm_final_le_of_proj hΓ u v hu hv U hψ₀ T S_out hdisj hε0 hε herr).2
        fun x y _ _ hne k hk => by cases hfx : f x <;> cases hfy : f y <;> simp_all [S_out]

private theorem c_mul_generalAdversary_le {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {c : ℝ} {T : ℕ}
    (hc_mat : ∀ Γ : Matrix (BitString N) (BitString N) ℝ, Γ.IsSymm → IsAdversaryMatrix P f Γ →
      c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ 2 * T * maxDiffNorm Γ) :
    c * generalAdversary P f ≤ 2 * T := by
  rcases le_or_gt c 0 with hc0 | hcpos
  · exact (mul_nonpos_of_nonpos_of_nonneg hc0 (generalAdversary_nonneg P f)).trans (by positivity)
  · rw [← le_div_iff₀' hcpos]
    refine (generalAdversary_le_iff (by positivity)).2 fun Γ hsym hΓ => ?_
    rw [div_mul_eq_mul_div, le_div_iff₀' hcpos]
    exact hc_mat Γ hsym hΓ

/-- **Negative-weight adversary lower bound `ADV±(f)` for Boolean functions**
([HoyerLeeSpalek2007], Theorem 2):
`(1 - 2√(ε(1-ε))) ADV±(f) ≤ 2 T`. -/
theorem one_sub_mul_generalAdversary_le_boolean {P : BitString N → Prop}
    {f : BitString N → Bool} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_acc : Finset (Fin N × Bool × W)) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (h₁ : ∀ x, P x → f x = true → 1 - ε ≤ measureProb (run U ψ₀ x T) S_acc)
    (h₀ : ∀ x, P x → f x = false → measureProb (run U ψ₀ x T) S_acc ≤ ε) :
    (1 - 2 * √(ε * (1 - ε))) * generalAdversary P f ≤ 2 * T :=
  c_mul_generalAdversary_le fun _ _ hΓ =>
    one_sub_mul_opNorm_le_general_boolean hΓ U hψ₀ T S_acc hε0 hε h₁ h₀

/-- **Negative-weight adversary bound for arbitrary finite output alphabets**: if a `T`-query
algorithm outputs `f x` with probability at least `1 - ε` (`ε ≤ 1/2`) via pairwise disjoint
outcome regions `S_out a`, then `(1 - 2√(ε(1-ε)) - ε) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ`. -/
theorem one_sub_mul_opNorm_le_general {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    (1 - 2 * √(ε * (1 - ε)) - ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤
      2 * T * maxDiffNorm Γ := by
  rw [sub_sub]
  exact one_sub_mul_opNorm_le_of_advForm Γ U hψ₀ T
    (add_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) hε0)
    fun u v hu hv =>
      (abs_advForm_final_le_of_proj hΓ u v hu hv U hψ₀ T S_out hdisj hε0 hε herr).1

/-- Weakened form matching [HoyerLeeSpalek2007], Theorem 2:
`(1 - 2√(ε(1-ε)) - 2ε) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ`. -/
theorem one_sub_mul_opNorm_le_general_hls {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hΓ : IsAdversaryMatrix P f Γ)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    (1 - 2 * √(ε * (1 - ε)) - 2 * ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤
      2 * T * maxDiffNorm Γ := by
  have hb := one_sub_mul_opNorm_le_general hΓ U hψ₀ T S_out hdisj hε0 hε herr
  linarith [mul_le_mul_of_nonneg_right hε0 (norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ))]

/-- **Negative-weight adversary bound `ADV±(f)` for finite outputs**:
`(1 - 2√(ε(1-ε)) - ε) ADV±(f) ≤ 2 T`. -/
theorem one_sub_mul_generalAdversary_le {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    (1 - 2 * √(ε * (1 - ε)) - ε) * generalAdversary P f ≤ 2 * T :=
  c_mul_generalAdversary_le fun _ _ hΓ =>
    one_sub_mul_opNorm_le_general hΓ U hψ₀ T S_out hdisj hε0 hε herr

/-- Weakened form matching [HoyerLeeSpalek2007], Theorem 2:
`(1 - 2√(ε(1-ε)) - 2ε) ADV±(f) ≤ 2 T`. -/
theorem one_sub_mul_generalAdversary_le_hls {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    (1 - 2 * √(ε * (1 - ε)) - 2 * ε) * generalAdversary P f ≤ 2 * T :=
  c_mul_generalAdversary_le fun _ _ hΓ =>
    one_sub_mul_opNorm_le_general_hls hΓ U hψ₀ T S_out hdisj hε0 hε herr

/-- **Nonnegative spectral adversary matrix bound** ([BarnumSaksSzegedy2003], as reviewed in
[HoyerLeeSpalek2007], Section 1.1, Theorem 1): when `0 ≤ Γ` and `Γ` is supported on
`{(x, y) | P x ∧ P y ∧ f x ≠ f y}`, a final-state overlap bound `δ` yields
`(1 - δ) ‖Γ‖ ≤ 2 T · maxDiffNorm Γ` for any output type `α`. -/
theorem one_sub_mul_opNorm_le_spectral {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {Γ : Matrix (BitString N) (BitString N) ℝ}
    (hnonneg : ∀ x y, 0 ≤ Γ x y) (hΓ : IsAdversaryMatrix P f Γ)
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    {δ : ℝ} (hδ : ∀ x y, P x → P y → f x ≠ f y →
      ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)‖ ≤ δ) :
    (1 - δ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ 2 * T * maxDiffNorm Γ := by
  by_cases hzero : Γ = 0
  · simp only [hzero, map_zero, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg T)) (maxDiffNorm_nonneg 0)
  have hδ0 : 0 ≤ δ := by
    by_contra! hneg
    exact hzero <| Matrix.ext fun x y => by_contra fun hxy =>
      let ⟨hx, hy, hf⟩ := hΓ x y hxy
      hneg.not_ge ((norm_nonneg _).trans (hδ x y hx hy hf))
  refine one_sub_mul_opNorm_le_of_advForm Γ U hψ₀ T hδ0 fun u v hu hv => ?_
  calc |advForm Γ u v (fun x => run U ψ₀ x T)|
      ≤ ∑ x, ∑ y, Γ x y * |u.ofLp x| * |v.ofLp y| * δ :=
        (abs_sum_le_sum_abs _ _).trans <| sum_le_sum fun x _ =>
          (abs_sum_le_sum_abs _ _).trans <| sum_le_sum fun y _ => by
            by_cases hxy : Γ x y = 0
            · simp only [hxy, zero_mul, abs_zero, le_refl]
            obtain ⟨hx, hy, hf⟩ := hΓ x y hxy
            simp only [abs_mul, abs_of_nonneg (hnonneg x y)]
            exact mul_le_mul_of_nonneg_left ((RCLike.abs_re_le_norm _).trans (hδ x y hx hy hf))
              (mul_nonneg (mul_nonneg (hnonneg x y) (abs_nonneg _)) (abs_nonneg _))
    _ = δ * inner ℝ (Matrix.absVec u) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (Matrix.absVec v)) := by
          rw [Matrix.inner_toEuclideanCLM]
          simp only [dotProduct, Matrix.mulVec, mul_sum, Matrix.absVec_apply]
          exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    _ ≤ δ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (Matrix.abs_inner_toEuclideanCLM_le_opNorm Γ
            (Matrix.norm_absVec_le hu) (Matrix.norm_absVec_le hv))) hδ0

/-- **Nonnegative spectral adversary lower bound `ADV(f)`** ([BarnumSaksSzegedy2003],
Section 1.1 of [HoyerLeeSpalek2007]):
`(1 - δ) ADV(f) ≤ 2 T` from any final-state overlap bound `δ`. -/
theorem one_sub_mul_spectralAdversary_le_of_inner {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) {δ : ℝ}
    (hδ : ∀ x y, P x → P y → f x ≠ f y → ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)‖ ≤ δ) :
    (1 - δ) * spectralAdversary P f ≤ 2 * T := by
  rcases le_or_gt (1 - δ) 0 with hc0 | hcpos
  · exact (mul_nonpos_of_nonpos_of_nonneg hc0 (spectralAdversary_nonneg P f)).trans (by positivity)
  · rw [← le_div_iff₀' hcpos]
    refine (spectralAdversary_le_iff (by positivity)).2 fun Γ _ hnonneg hΓ => ?_
    rw [div_mul_eq_mul_div, le_div_iff₀' hcpos]
    exact one_sub_mul_opNorm_le_spectral hnonneg hΓ U hψ₀ T hδ

/-- **Nonnegative spectral adversary lower bound `ADV(f)`** for finite-output algorithms with
error probability at most `ε ≤ 1/2`: `(1 - 2√(ε(1-ε))) ADV(f) ≤ 2 T`. -/
theorem one_sub_mul_spectralAdversary_le {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S_out : α → Finset (Fin N × Bool × W)) (hdisj : Pairwise (Disjoint on S_out))
    {ε : ℝ} (hε : 2 * ε ≤ 1)
    (herr : ∀ x, P x → 1 - ε ≤ measureProb (run U ψ₀ x T) (S_out (f x))) :
    (1 - 2 * √(ε * (1 - ε))) * spectralAdversary P f ≤ 2 * T := by
  classical
  refine one_sub_mul_spectralAdversary_le_of_inner U hψ₀ T fun x y hx hy hf => ?_
  have hc : measureProb (run U ψ₀ y T) (S_out (f y))ᶜ ≤ ε := by
    rw [measureProb_compl, norm_run, hψ₀, one_pow]
    linarith [herr y hy]
  exact norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀]) (by rw [norm_run, hψ₀])
    (herr x hx) ((measureProb_mono (run U ψ₀ y T) (hdisj hf).le_compl_right).trans hc) hε

end ProgressCore

section HierarchyAndBarriers

/-- **Spectral sensitivity is at most the nonnegative spectral adversary**
([AaronsonBenDavidKothariRaoTal2021], via the sensitivity-graph adjacency matrix):
`λ(f) ≤ ADV(f)`. -/
theorem spectralSensitivity_le_spectralAdversary (f : BooleanFunction N) :
    BitString.spectralSensitivity f ≤ spectralAdversary (fun _ => True) f := by
  let Γ := (BitString.sensitivityGraph f).adjMatrix ℝ
  have hsym : Γ.IsSymm := SimpleGraph.isSymm_adjMatrix _
  have hnonneg : ∀ x y, 0 ≤ Γ x y := fun x y => by
    simp only [Γ, SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num
  have hΓ : IsAdversaryMatrix (fun _ => True) f Γ := fun x y hne => by
    have hadj : (BitString.sensitivityGraph f).Adj x y := by
      by_contra h; exact hne (by simp only [Γ, SimpleGraph.adjMatrix_apply, h, ↓reduceIte])
    obtain ⟨i, hi, rfl⟩ := BitString.sensitivityGraph_adj.1 hadj
    exact ⟨trivial, trivial, Ne.symm hi⟩
  have hmax : maxDiffNorm Γ ≤ 1 := (maxDiffNorm_le_iff zero_le_one).2 fun i => by
    have hrow (x : BitString N) : ∑ y, |(Γ.hadamard (diffMatrix i)) x y| ≤ 1 := by
      rw [Finset.sum_eq_single (Function.update x i (!x i))]
      · simp only [Matrix.hadamard_apply, Γ, SimpleGraph.adjMatrix_apply, diffMatrix_apply]
        split_ifs <;> norm_num
      · intro y _ hyne
        by_cases hadj : (BitString.sensitivityGraph f).Adj x y
        · obtain ⟨j, _, rfl⟩ := BitString.sensitivityGraph_adj.1 hadj
          simp [Function.update_of_ne (Ne.symm fun h : j = i => hyne (h ▸ rfl))]
        · simp [Γ, hadj]
      · exact fun hmem => absurd (mem_univ _) hmem
    refine (Matrix.opNorm_toEuclideanCLM_le_sqrt _ zero_le_one zero_le_one hrow fun y => ?_).trans
      (by norm_num)
    exact (sum_congr rfl fun x _ => by
      rw [Matrix.hadamard_apply, Matrix.hadamard_apply, ← Matrix.transpose_apply Γ x y, hsym.eq,
        ← Matrix.transpose_apply (diffMatrix i) x y, diffMatrix_transpose]).trans_le (hrow y)
  have hspec_le : BitString.spectralSensitivity f ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ :=
    BitString.spectralSensitivity_le_of_forall_sum_le (norm_nonneg _) fun u w _ _ hu1 hw1 => by
      rw [← BitString.inner_toEuclideanCLM_adjMatrix_sensitivityGraph]
      exact (le_abs_self _).trans <| Matrix.abs_inner_toEuclideanCLM_le_opNorm Γ
        ((EuclideanSpace.norm_le_one_iff_sum_sq_le_one _).2 hu1.le)
        ((EuclideanSpace.norm_le_one_iff_sum_sq_le_one _).2 hw1.le)
  rcases (maxDiffNorm_nonneg Γ).eq_or_lt with h0 | hm
  · exact (by simpa [eq_zero_of_maxDiffNorm_eq_zero hΓ h0.symm] using hspec_le :
      BitString.spectralSensitivity f ≤ 0).trans (spectralAdversary_nonneg _ _)
  · exact (hspec_le.trans_eq (div_one _).symm).trans <|
      (div_le_div_of_nonneg_left (norm_nonneg _) hm hmax).trans
        (le_spectralAdversary hsym hnonneg hΓ)

/-- Weight matrix `A[x, y] = ∑_{p ∈ S.R, p = (x, y)} S.w p` associated with a weight scheme. -/
private noncomputable def wsRaw (S : WeightScheme N) : Matrix (BitString N) (BitString N) ℝ :=
  Matrix.of fun x y => ∑ p ∈ S.R with p = (x, y), S.w p

/-- Normalized nonnegative symmetric matrix associated with a weight scheme `S`:
`Γ[x, y] = (A[x, y] + A[y, x]) / (z(x) z(y))` with `z(x) = √(wtFst x + wtSnd x)`. -/
private noncomputable def wsMatrix (S : WeightScheme N) : Matrix (BitString N) (BitString N) ℝ :=
  Matrix.of fun x y =>
    (wsRaw S x y + wsRaw S y x) / (√(S.wtFst x + S.wtSnd x) * √(S.wtFst y + S.wtSnd y))

private theorem wsMatrix_isSymm (S : WeightScheme N) : (wsMatrix S).IsSymm := by
  ext x y
  simp only [Matrix.transpose_apply, wsMatrix, Matrix.of_apply]
  ring

private theorem wsMatrix_nonneg (S : WeightScheme N) (x y : BitString N) : 0 ≤ wsMatrix S x y := by
  classical
  refine div_nonneg (add_nonneg ?_ ?_) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) <;>
    exact sum_nonneg fun p hp => S.w_nonneg p (mem_filter.1 hp).1

private theorem sum_wsRaw_mul (S : WeightScheme N) (g : BitString N → BitString N → ℝ) :
    ∑ x, ∑ y, wsRaw S x y * g x y = ∑ p ∈ S.R, S.w p * g p.1 p.2 := by
  classical
  calc ∑ x, ∑ y, wsRaw S x y * g x y
      = ∑ x, ∑ y, ∑ p ∈ S.R, if p = (x, y) then S.w p * g x y else 0 := by
          simp only [wsRaw, Matrix.of_apply, sum_filter, sum_mul, ite_mul, zero_mul]
    _ = ∑ x, ∑ p ∈ S.R, ∑ y, if p = (x, y) then S.w p * g x y else 0 :=
          sum_congr rfl fun _ _ => sum_comm
    _ = ∑ p ∈ S.R, ∑ x, ∑ y, if p = (x, y) then S.w p * g x y else 0 := sum_comm
    _ = ∑ p ∈ S.R, S.w p * g p.1 p.2 :=
          sum_congr rfl fun p _ => by
            rw [← Fintype.sum_prod_type (f := fun xy : BitString N × BitString N =>
              if p = xy then S.w p * g xy.1 xy.2 else 0), Fintype.sum_ite_eq]

private theorem wsMatrix_isAdversary {α : Type*} {P : BitString N → Prop} {f : BitString N → α}
    (S : WeightScheme N) (hS : ∀ p ∈ S.R, P p.1 ∧ P p.2 ∧ f p.1 ≠ f p.2) :
    IsAdversaryMatrix P f (wsMatrix S) := by
  classical
  intro x y hne
  have hex : (∃ p ∈ S.R, p = (x, y)) ∨ ∃ p ∈ S.R, p = (y, x) := by
    by_contra hnone
    push Not at hnone
    have hw0 {a b : BitString N} (h : ∀ p ∈ S.R, p ≠ (a, b)) : wsRaw S a b = 0 :=
      sum_eq_zero fun p hp => absurd (mem_filter.1 hp).2 (h p (mem_filter.1 hp).1)
    exact hne (by simp [wsMatrix, hw0 hnone.1, hw0 hnone.2])
  rcases hex with ⟨p, hp, hpx⟩ | ⟨p, hp, hpy⟩
  · have h := hS p hp; rw [hpx] at h; exact h
  · have h := hS p hp; rw [hpy] at h; exact ⟨h.2.1, h.1, h.2.2.symm⟩

private theorem wsMatrix_mul_sqrt (S : WeightScheme N) (x y : BitString N) :
    wsMatrix S x y * (√(S.wtFst x + S.wtSnd x) * √(S.wtFst y + S.wtSnd y)) =
      wsRaw S x y + wsRaw S y x := by
  classical
  by_cases hz : √(S.wtFst x + S.wtSnd x) * √(S.wtFst y + S.wtSnd y) = 0
  · have hzero (u v : BitString N) (hzu : √(S.wtFst u + S.wtSnd u) = 0) :
        wsRaw S u v = 0 ∧ wsRaw S v u = 0 := by
      have hsum0 := Real.sqrt_eq_zero'.1 hzu
      have hf0 : S.wtFst u = 0 := by linarith [S.wtFst_nonneg u, S.wtSnd_nonneg u]
      have hs0 : S.wtSnd u = 0 := by linarith [S.wtFst_nonneg u, S.wtSnd_nonneg u]
      rw [WeightScheme.wtFst,
        sum_eq_zero_iff_of_nonneg fun q hq => S.w_nonneg q (mem_filter.1 hq).1] at hf0
      rw [WeightScheme.wtSnd,
        sum_eq_zero_iff_of_nonneg fun q hq => S.w_nonneg q (mem_filter.1 hq).1] at hs0
      exact ⟨sum_eq_zero fun p hp => hf0 p
          (mem_filter.2 ⟨(mem_filter.1 hp).1, congrArg Prod.fst (mem_filter.1 hp).2⟩),
        sum_eq_zero fun p hp => hs0 p
          (mem_filter.2 ⟨(mem_filter.1 hp).1, congrArg Prod.snd (mem_filter.1 hp).2⟩)⟩
    obtain ⟨h1, h2⟩ : wsRaw S x y = 0 ∧ wsRaw S y x = 0 := by
      rcases mul_eq_zero.1 hz with h | h
      exacts [hzero x y h, (hzero y x h).symm]
    simp only [wsMatrix, Matrix.of_apply, h1, h2, add_zero, zero_div, zero_mul]
  · exact div_mul_cancel₀ _ hz

private theorem wsMatrix_opNorm_ge_one (S : WeightScheme N) (hW : 0 < S.weightSum) :
    1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (wsMatrix S)‖ := by
  classical
  let z : BitString N → ℝ := fun x => √(S.wtFst x + S.wtSnd x)
  let w₀ : EuclideanSpace ℝ (BitString N) := WithLp.toLp 2 fun x => z x / √(2 * S.weightSum)
  have hfst : ∑ x, S.wtFst x = S.weightSum :=
    sum_fiberwise_of_maps_to (s := S.R) (g := Prod.fst) (t := univ) (f := S.w)
      fun _ _ => mem_univ _
  have hsnd : ∑ y, S.wtSnd y = S.weightSum :=
    sum_fiberwise_of_maps_to (s := S.R) (g := Prod.snd) (t := univ) (f := S.w)
      fun _ _ => mem_univ _
  have hw₀_sq : ‖w₀‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    dsimp only [w₀, z]
    simp_rw [div_pow, Real.sq_sqrt (add_nonneg (S.wtFst_nonneg _) (S.wtSnd_nonneg _)),
      Real.sq_sqrt (by linarith : 0 ≤ 2 * S.weightSum), ← sum_div, sum_add_distrib, hfst, hsnd,
      ← two_mul]
    exact div_self (by positivity)
  have hw₀ : ‖w₀‖ = 1 := by rw [← Real.sqrt_sq (norm_nonneg w₀), hw₀_sq, Real.sqrt_one]
  have hA_sum : ∑ x, ∑ y, wsRaw S x y = S.weightSum := by
    simpa only [mul_one, WeightScheme.weightSum] using sum_wsRaw_mul S fun _ _ => 1
  have hray : inner ℝ w₀ (Matrix.toEuclideanCLM (𝕜 := ℝ) (wsMatrix S) w₀) = 1 := by
    rw [Matrix.inner_toEuclideanCLM]
    simp only [dotProduct, Matrix.mulVec, w₀, mul_sum]
    calc ∑ x, ∑ y, (z x / √(2 * S.weightSum)) * (wsMatrix S x y * (z y / √(2 * S.weightSum)))
        = (∑ x, ∑ y, (wsRaw S x y + wsRaw S y x)) / (2 * S.weightSum) := by
            simp_rw [sum_div]
            refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
            rw [show (z x / √(2 * S.weightSum)) * (wsMatrix S x y * (z y / √(2 * S.weightSum))) =
              (wsMatrix S x y * (z x * z y)) / (√(2 * S.weightSum) * √(2 * S.weightSum)) by ring,
              wsMatrix_mul_sqrt, Real.mul_self_sqrt (by linarith)]
      _ = 1 := by
            simp_rw [Finset.sum_add_distrib]
            rw [hA_sum, sum_comm (f := fun x y => wsRaw S y x), hA_sum, ← two_mul]
            exact div_self (by positivity)
  exact hray.symm.trans_le
    ((le_abs_self _).trans (Matrix.abs_inner_toEuclideanCLM_le_opNorm (wsMatrix S) hw₀.le hw₀.le))

private theorem wsMatrix_hadamard_bilin_eq (S : WeightScheme N) (i : Fin N)
    (a b : EuclideanSpace ℝ (BitString N)) :
    ∑ x, ∑ y, wsMatrix S x y * diffMatrix i x y * (|a.ofLp x| * |b.ofLp y|) =
      ∑ p ∈ S.R with p.1 i ≠ p.2 i,
        (S.w p / (√(S.wtFst p.1 + S.wtSnd p.1) * √(S.wtFst p.2 + S.wtSnd p.2))) *
          (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) := by
  classical
  let z : BitString N → ℝ := fun x => √(S.wtFst x + S.wtSnd x)
  let g (x y : BitString N) : ℝ := diffMatrix i x y * (|a.ofLp x| * |b.ofLp y|) / (z x * z y)
  calc ∑ x, ∑ y, wsMatrix S x y * diffMatrix i x y * (|a.ofLp x| * |b.ofLp y|)
      = ∑ x, ∑ y, (wsRaw S x y * g x y + wsRaw S y x * g x y) :=
          sum_congr rfl fun x _ => sum_congr rfl fun y _ => by
            simp only [wsMatrix, Matrix.of_apply, z, g]; ring
    _ = (∑ x, ∑ y, wsRaw S x y * g x y) + (∑ y, ∑ x, wsRaw S y x * g x y) := by
          simp_rw [sum_add_distrib]
          conv_lhs => rhs; rw [sum_comm]
    _ = ∑ p ∈ S.R, S.w p * (g p.1 p.2 + g p.2 p.1) := by
          rw [sum_wsRaw_mul, sum_wsRaw_mul, ← sum_add_distrib]
          exact sum_congr rfl fun p _ => (mul_add _ _ _).symm
    _ = ∑ p ∈ S.R with p.1 i ≠ p.2 i,
          (S.w p / (z p.1 * z p.2)) *
            (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) := by
          rw [sum_filter]
          refine sum_congr rfl fun p _ => ?_
          simp only [g, diffMatrix_apply, ne_comm]
          split_ifs with hpi
          · ring
          · simp only [zero_mul, zero_div, add_zero, mul_zero]

private theorem sum_fiber_endpoint_le (S : WeightScheme N) (i : Fin N)
    (k : BitString N × BitString N → BitString N)
    (wt : BitString N → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (g : BitString N × BitString N → ℝ) (φ : BitString N → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ x ∈ S.R.image k, (∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ k p = x, g p) ≤ K * wt x) :
    ∑ p ∈ S.R with p.1 i ≠ p.2 i, φ (k p) * g p / (S.wtFst (k p) + S.wtSnd (k p)) ≤
      K * ∑ x, φ x * (wt x / (S.wtFst x + S.wtSnd x)) := by
  classical
  rw [← sum_fiberwise_of_maps_to (s := S.R.filter fun p => p.1 i ≠ p.2 i)
    (g := k) (t := univ) (fun _ _ => mem_univ _), mul_sum]
  refine sum_le_sum fun x _ => ?_
  have hfiber : ∑ p ∈ (S.R.filter fun p => p.1 i ≠ p.2 i) with k p = x,
      φ (k p) * g p / (S.wtFst (k p) + S.wtSnd (k p)) =
      φ x * (∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ k p = x, g p) / (S.wtFst x + S.wtSnd x) := by
    rw [mul_sum, sum_div]
    refine sum_congr (by ext p; simp only [mem_filter, and_assoc]) fun p hp => ?_
    rw [(mem_filter.1 hp).2.2]
  rw [hfiber]
  have hle : ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ k p = x, g p ≤ K * wt x := by
    by_cases hxk : x ∈ S.R.image k
    · exact hbd x hxk
    · rw [sum_eq_zero fun p hp =>
        absurd (mem_image.2 ⟨p, (mem_filter.1 hp).1, (mem_filter.1 hp).2.2⟩) hxk]
      exact mul_nonneg hK (hwt x)
  calc φ x * (∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ k p = x, g p) / (S.wtFst x + S.wtSnd x)
      ≤ φ x * (K * wt x) / (S.wtFst x + S.wtSnd x) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle (hφ x))
            (add_nonneg (S.wtFst_nonneg x) (S.wtSnd_nonneg x))
    _ = K * (φ x * (wt x / (S.wtFst x + S.wtSnd x))) := by ring

private theorem wsMatrix_pair_bound (S : WeightScheme N) (i : Fin N)
    (a b : EuclideanSpace ℝ (BitString N)) {c : ℝ} (hc : 0 < c)
    (p : BitString N × BitString N) (hp : p ∈ S.R.filter fun p => p.1 i ≠ p.2 i) :
    (S.w p / (√(S.wtFst p.1 + S.wtSnd p.1) * √(S.wtFst p.2 + S.wtSnd p.2))) *
        (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) ≤
      ((a.ofLp p.1 ^ 2 + b.ofLp p.1 ^ 2) * (c * S.u p i) / (S.wtFst p.1 + S.wtSnd p.1) +
        (a.ofLp p.2 ^ 2 + b.ofLp p.2 ^ 2) * (S.v p i / c) / (S.wtFst p.2 + S.wtSnd p.2)) / 2 := by
  obtain ⟨hpR, hpi⟩ := mem_filter.1 hp
  have hu0 := S.u_nonneg p hpR i hpi
  have hv0 := S.v_nonneg p hpR i hpi
  have hwt1 := add_nonneg (S.wtFst_nonneg p.1) (S.wtSnd_nonneg p.1)
  have hwt2 := add_nonneg (S.wtFst_nonneg p.2) (S.wtSnd_nonneg p.2)
  set u' := (c * S.u p i) / (S.wtFst p.1 + S.wtSnd p.1)
  set v' := (S.v p i / c) / (S.wtFst p.2 + S.wtSnd p.2)
  have hsq : (S.w p / (√(S.wtFst p.1 + S.wtSnd p.1) * √(S.wtFst p.2 + S.wtSnd p.2))) ^ 2 ≤
      u' * v' := by
    rcases (S.w_nonneg p hpR).eq_or_lt with hw0 | _
    · rw [← hw0, zero_div, zero_pow two_ne_zero]; positivity
    · rw [div_pow, mul_pow, Real.sq_sqrt hwt1, Real.sq_sqrt hwt2]
      refine (div_le_div_of_nonneg_right (S.sq_le p hpR i hpi)
        (mul_nonneg hwt1 hwt2)).trans_eq ?_
      dsimp only [u', v']
      rw [div_mul_div_comm, mul_comm c (S.u p i), mul_assoc (S.u p i), mul_comm c,
        div_mul_cancel₀ _ hc.ne']
  have h1 := two_mul_mul_le_of_sq_le_mul (abs_nonneg (a.ofLp p.1)) (abs_nonneg (b.ofLp p.2))
    (by positivity) (by positivity) hsq
  have h2 := two_mul_mul_le_of_sq_le_mul (abs_nonneg (b.ofLp p.1)) (abs_nonneg (a.ofLp p.2))
    (by positivity) (by positivity) hsq
  simp only [sq_abs] at h1 h2
  have hsum : (a.ofLp p.1 ^ 2 + b.ofLp p.1 ^ 2) * (c * S.u p i) / (S.wtFst p.1 + S.wtSnd p.1) +
      (a.ofLp p.2 ^ 2 + b.ofLp p.2 ^ 2) * (S.v p i / c) / (S.wtFst p.2 + S.wtSnd p.2) =
      (u' * a.ofLp p.1 ^ 2 + v' * b.ofLp p.2 ^ 2) +
        (u' * b.ofLp p.1 ^ 2 + v' * a.ofLp p.2 ^ 2) := by
    dsimp only [u', v']; ring
  linarith

private theorem wsMatrix_maxDiffNorm_le (S : WeightScheme N) {vA vB : ℝ}
    (hvA : 0 < vA) (hvB : 0 < vB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, S.loadFst x i ≤ vA * S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, S.loadSnd y i ≤ vB * S.wtSnd y) :
    maxDiffNorm (wsMatrix S) ≤ √(vA * vB) := by
  classical
  set c := √vB / √vA
  have hc : 0 < c := div_pos (Real.sqrt_pos.2 hvB) (Real.sqrt_pos.2 hvA)
  have hc_eq : c * vA = √(vA * vB) := by
    rw [div_mul_eq_mul_div, div_eq_iff (Real.sqrt_ne_zero'.2 hvA), Real.sqrt_mul hvA.le,
      mul_comm √vA, mul_assoc, Real.mul_self_sqrt hvA.le]
  have hc_eq' : vB / c = √(vA * vB) := by
    rw [div_div_eq_mul_div, div_eq_iff (Real.sqrt_ne_zero'.2 hvB), Real.sqrt_mul hvA.le,
      mul_assoc, Real.mul_self_sqrt hvB.le, mul_comm]
  refine (maxDiffNorm_le_iff (Real.sqrt_nonneg _)).2 fun i =>
    Matrix.opNorm_toEuclideanCLM_le_of_inner _ (Real.sqrt_nonneg _) fun a b ha hb => ?_
  rw [Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, mul_sum, Matrix.hadamard_apply]
  let φ : BitString N → ℝ := fun x => a.ofLp x ^ 2 + b.ofLp x ^ 2
  have hφ : ∀ x, 0 ≤ φ x := fun x => add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc ∑ x, ∑ y, a.ofLp x * (wsMatrix S x y * diffMatrix i x y * b.ofLp y)
      ≤ ∑ p ∈ S.R with p.1 i ≠ p.2 i,
          (S.w p / (√(S.wtFst p.1 + S.wtSnd p.1) * √(S.wtFst p.2 + S.wtSnd p.2))) *
            (|a.ofLp p.1| * |b.ofLp p.2| + |a.ofLp p.2| * |b.ofLp p.1|) := by
        rw [← wsMatrix_hadamard_bilin_eq]
        exact sum_le_sum fun x _ => sum_le_sum fun y _ =>
          (mul_le_mul_of_nonneg_left ((le_abs_self _).trans_eq (abs_mul _ _))
            (mul_nonneg (wsMatrix_nonneg S x y)
              (by rw [diffMatrix_apply]; split_ifs <;> norm_num))).trans_eq' (by ring)
    _ ≤ (√(vA * vB) * (∑ x, φ x * (S.wtFst x / (S.wtFst x + S.wtSnd x)) +
          ∑ y, φ y * (S.wtSnd y / (S.wtFst y + S.wtSnd y)))) / 2 := by
        refine (sum_le_sum fun p hp => wsMatrix_pair_bound S i a b hc p hp).trans ?_
        rw [← sum_div, sum_add_distrib, mul_add]
        refine div_le_div_of_nonneg_right (add_le_add ?_ ?_) zero_le_two
        · exact sum_fiber_endpoint_le S i Prod.fst S.wtFst S.wtFst_nonneg (fun p => c * S.u p i)
            φ hφ (Real.sqrt_nonneg _) fun x hx => by
              rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left (hA x hx i) hc.le).trans_eq
                (by rw [← mul_assoc, hc_eq])
        · exact sum_fiber_endpoint_le S i Prod.snd S.wtSnd S.wtSnd_nonneg (fun p => S.v p i / c)
            φ hφ (Real.sqrt_nonneg _) fun y hy => by
              rw [← sum_div]; exact (div_le_div_of_nonneg_right (hB y hy i) hc.le).trans_eq
                (by rw [mul_div_right_comm, hc_eq'])
    _ ≤ √(vA * vB) * 2 / 2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by
        rw [← sum_add_distrib]
        calc ∑ x, (φ x * (S.wtFst x / (S.wtFst x + S.wtSnd x)) +
              φ x * (S.wtSnd x / (S.wtFst x + S.wtSnd x)))
            ≤ ∑ x, φ x := sum_le_sum fun x _ => by
                by_cases hs : S.wtFst x + S.wtSnd x = 0
                · simp only [hs, div_zero, mul_zero, add_zero]; positivity
                · rw [← mul_add, ← add_div, div_self hs, mul_one]
          _ ≤ 2 := by
                simp only [φ, sum_add_distrib]
                linarith [(EuclideanSpace.norm_le_one_iff_sum_sq_le_one a).1 ha,
                  (EuclideanSpace.norm_le_one_iff_sum_sq_le_one b).1 hb])
        (Real.sqrt_nonneg _)) zero_le_two
    _ = √(vA * vB) := by ring

/-- **Weighted bounds are at most the spectral adversary** (original proof /
[HoyerLeeSpalek2007]): any `WeightScheme` supported on `{(x, y) | P x ∧ P y ∧ f x ≠ f y}`
with `0 < S.weightSum` and `mA · loadFst x i ≤ wtFst x`, `mB · loadSnd y i ≤ wtSnd y` satisfies
`√(mA · mB) ≤ ADV(f)`. -/
theorem WeightScheme.le_spectralAdversary {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (S : WeightScheme N) (hW : 0 < S.weightSum)
    (hS : ∀ p ∈ S.R, P p.1 ∧ P p.2 ∧ f p.1 ≠ f p.2)
    {mA mB : ℝ} (hmA : 0 ≤ mA) (hmB : 0 ≤ mB)
    (hA : ∀ x ∈ S.R.image Prod.fst, ∀ i, mA * S.loadFst x i ≤ S.wtFst x)
    (hB : ∀ y ∈ S.R.image Prod.snd, ∀ i, mB * S.loadSnd y i ≤ S.wtSnd y) :
    √(mA * mB) ≤ spectralAdversary P f := by
  rcases hmA.eq_or_lt with rfl | hmA_pos
  · simp only [zero_mul, Real.sqrt_zero, spectralAdversary_nonneg]
  rcases hmB.eq_or_lt with rfl | hmB_pos
  · simp only [mul_zero, Real.sqrt_zero, spectralAdversary_nonneg]
  let Γ := wsMatrix S
  have hΓ : IsAdversaryMatrix P f Γ := wsMatrix_isAdversary S hS
  have hnorm1 : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := wsMatrix_opNorm_ge_one S hW
  have hmax : maxDiffNorm Γ ≤ (√(mA * mB))⁻¹ := by
    rw [← Real.sqrt_inv, mul_inv]
    exact wsMatrix_maxDiffNorm_le S (inv_pos.2 hmA_pos) (inv_pos.2 hmB_pos)
      (fun x hx i => by rw [inv_mul_eq_div, le_div_iff₀' hmA_pos]; exact hA x hx i)
      (fun y hy i => by rw [inv_mul_eq_div, le_div_iff₀' hmB_pos]; exact hB y hy i)
  have hm_pos : 0 < maxDiffNorm Γ := (maxDiffNorm_nonneg Γ).lt_of_ne fun h0 => by
    simp only [eq_zero_of_maxDiffNorm_eq_zero hΓ h0.symm, map_zero, norm_zero] at hnorm1; linarith
  calc √(mA * mB) ≤ 1 / maxDiffNorm Γ := by
        rw [one_div]; exact (le_inv_comm₀ hm_pos (Real.sqrt_pos.2 (mul_pos hmA_pos hmB_pos))).1 hmax
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDiffNorm Γ := by gcongr
    _ ≤ spectralAdversary P f :=
        _root_.Cslib.Quantum.le_spectralAdversary (wsMatrix_isSymm S) (wsMatrix_nonneg S) hΓ

/-- **Hamming-distance barrier for nonnegative adversary matrices** (property-testing / distance
barrier noted in [HoyerLeeSpalek2007], Section 7.2): if `0 ≤ Γ` and every nonzero entry
`(x, y)` has Hamming distance at least `k`, then `k · ‖Γ‖ ≤ N · maxDiffNorm Γ`. -/
theorem mul_opNorm_le_mul_maxDiffNorm_of_hammingDist_ge
    {Γ : Matrix (BitString N) (BitString N) ℝ} (hnonneg : ∀ x y, 0 ≤ Γ x y) {k : ℕ}
    (hk : ∀ x y, Γ x y ≠ 0 → k ≤ #{i : Fin N | x i ≠ y i}) :
    (k : ℝ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ N * maxDiffNorm Γ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simpa only [Nat.cast_zero, zero_mul] using
      mul_nonneg (Nat.cast_nonneg _) (maxDiffNorm_nonneg Γ)
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 hk_pos
  have hnorm_le := Matrix.opNorm_toEuclideanCLM_le_of_inner Γ
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (maxDiffNorm_nonneg _)) hk0.le)
    fun u v hu hv => (le_div_iff₀' hk0).2 <| by
      have huPos := Matrix.norm_absVec_le hu
      have hvPos := Matrix.norm_absVec_le hv
      calc (k : ℝ) * inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v)
          ≤ (k : ℝ) * inner ℝ (Matrix.absVec u)
              (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (Matrix.absVec v)) :=
            mul_le_mul_of_nonneg_left (Matrix.inner_toEuclideanCLM_le_absVec hnonneg u v) hk0.le
        _ ≤ ∑ i : Fin N, inner ℝ (Matrix.absVec u) (Matrix.toEuclideanCLM (𝕜 := ℝ)
              (Γ.hadamard (diffMatrix i)) (Matrix.absVec v)) := by
            simp only [Matrix.inner_toEuclideanCLM, dotProduct, Matrix.mulVec, mul_sum,
              Matrix.absVec_apply, Matrix.hadamard_apply]
            conv_rhs => rw [sum_comm]; enter [2, x]; rw [sum_comm]
            refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
            rw [show ∑ i : Fin N, |u.ofLp x| * (Γ x y * diffMatrix i x y * |v.ofLp y|) =
                Γ x y * (∑ i : Fin N, diffMatrix i x y) * |u.ofLp x| * |v.ofLp y| by
              simp only [mul_sum, sum_mul]; exact sum_congr rfl fun i _ => by ring]
            by_cases hxy0 : Γ x y = 0
            · simp only [hxy0, mul_zero, zero_mul, le_refl]
            · have hdiff : (k : ℝ) ≤ ∑ i : Fin N, diffMatrix i x y := by
                simpa only [Finset.card_filter, Nat.cast_sum, diffMatrix_apply, Nat.cast_ite,
                  Nat.cast_one, Nat.cast_zero] using (Nat.cast_le (α := ℝ)).2 (hk x y hxy0)
              have hmul := mul_le_mul_of_nonneg_right hdiff
                (mul_nonneg (mul_nonneg (hnonneg x y) (abs_nonneg (u.ofLp x)))
                  (abs_nonneg (v.ofLp y)))
              linarith
        _ ≤ N * maxDiffNorm Γ := (sum_le_sum fun i _ => ((le_abs_self _).trans
              (Matrix.abs_inner_toEuclideanCLM_le_opNorm _ huPos hvPos)).trans
              (norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ i)).trans_eq
              (by simp only [sum_const, card_fin, nsmul_eq_mul])
  exact (le_div_iff₀' hk0).1 hnorm_le

/-- **Hamming-distance barrier on `ADV(f)`**: if every distinguishing pair `(x, y)` of valid
inputs has Hamming distance at least `k > 0`, then `ADV(f) ≤ N / k`. -/
theorem spectralAdversary_le_div_of_hammingDist_ge {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} {k : ℕ} (hk0 : 0 < k)
    (hk : ∀ x y, P x → P y → f x ≠ f y → k ≤ #{i : Fin N | x i ≠ y i}) :
    spectralAdversary P f ≤ (N : ℝ) / k := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.2 hk0
  refine (spectralAdversary_le_iff (by positivity)).2 fun Γ _ hnonneg hΓ => ?_
  rw [div_mul_eq_mul_div, le_div_iff₀' hk_pos]
  exact mul_opNorm_le_mul_maxDiffNorm_of_hammingDist_ge hnonneg fun x y hxy0 =>
    let ⟨hx, hy, hf⟩ := hΓ x y hxy0
    hk x y hx hy hf

end HierarchyAndBarriers

end Cslib.Quantum
