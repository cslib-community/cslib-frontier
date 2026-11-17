/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.AlgState
public import CslibFrontier.Foundations.Algebra.Order.Star.Pi
public import CslibFrontier.Probability.PMF

/-!
# Approximation in a state

Rigidity and self-testing arguments for nonlocal games are long chains of approximations
`A ≈_δ B`: two operators are close *in the state* `φ`, `‖A - B‖_φ ≤ δ`, where `‖·‖_φ` is the
state-dependent norm `√(Re φ(a⋆a))`
[Ji, Natarajan, Vidick, Wright and Yuen, §5.2, Definition 5.16][JNVWY2020]. The relation
`a ≈[φ; δ] b` (`Cslib.Quantum.AlgState.Approx`) is that statement. Definition 5.16 bounds the
squared distance, averaged over questions, by `O(δ)`; here the distance itself is bounded by `δ`,
so `a ≈[φ; √δ] b` is the paper's `≈_δ` up to the constant. Its errors add along
chains: there is a `Trans` instance, so

```
calc a ≈[φ; δ₁] b := h₁
  _ ≈[φ; δ₂] c := h₂
```

proves `a ≈[φ; δ₁ + δ₂] c`. Closeness is preserved by sums, scalar multiples and multiplication
on the left by contractions (`Cslib.Quantum.AlgState.Approx.mul_left`), and close operators have
close expectations (`Cslib.Quantum.AlgState.Approx.norm_apply_sub_le`). Multiplication on the right
does not preserve closeness in a state; arguments that need it move the operator to the other
prover first.

Most closeness statements in the literature are *on average* over a question distribution `μ`:
`E_{q ∼ μ} ‖A_q - B_q‖²_φ ≤ δ²`. These need no separate theory. The weighted state
`Cslib.Quantum.AlgState.avg μ φ` on the product algebra `Q → A` gives the families `A = (A_q)_q` the
averaged norm (`Cslib.Quantum.AlgState.norm_avg_sq`), so averaged closeness is `A ≈[avg μ φ; δ] B`
and the whole calculus applies to it unchanged.

## Main definitions

* `Cslib.Quantum.AlgState.Approx`: closeness `‖a - b‖_φ ≤ δ` in a state, notation `a ≈[φ; δ] b`.
* `Cslib.Quantum.AlgState.avg`: the weighted state `f ↦ ∑_q μ(q) φ_q(f_q)` on a product algebra.

## Main results

* `Cslib.Quantum.AlgState.Approx.trans`: errors add along chains.
* `Cslib.Quantum.AlgState.Approx.mul_left`: left multiplication by a contraction preserves
  closeness.
* `Cslib.Quantum.AlgState.Approx.norm_apply_sub_le`: close operators have close expectations.
* `Cslib.Quantum.AlgState.norm_avg_sq`: the state norm of the weighted state is the averaged norm.
* `Cslib.Quantum.AlgState.approx_avg_iff`: averaged closeness, `E_q ‖f_q - g_q‖² ≤ δ²`.

## References

* [Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, *MIP* = RE*][JNVWY2020]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset
open scoped ComplexOrder

namespace AlgState

section Approx

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A]

/-- `a` and `b` are `δ`-close in the state `φ`: `‖a - b‖_φ ≤ δ`. -/
def Approx (φ : AlgState A) (δ : ℝ) (a b : A) : Prop :=
  φ.norm (a - b) ≤ δ

@[inherit_doc] scoped[Cslib.Quantum] notation:50 a " ≈[" φ "; " δ "] " b:50 =>
  Cslib.Quantum.AlgState.Approx φ δ a b

variable {φ : AlgState A} {a b c a' b' : A} {δ δ' : ℝ}

theorem approx_iff : (a ≈[φ; δ] b) ↔ φ.norm (a - b) ≤ δ :=
  Iff.rfl

theorem approx_self (φ : AlgState A) (a : A) : a ≈[φ; 0] a := by
  simp [Approx]

theorem Approx.refl (hδ : 0 ≤ δ) (a : A) : a ≈[φ; δ] a := by
  simpa [Approx] using hδ

theorem Approx.nonneg (h : a ≈[φ; δ] b) : 0 ≤ δ :=
  (φ.norm_nonneg _).trans h

theorem Approx.symm (h : a ≈[φ; δ] b) : b ≈[φ; δ] a := by
  rwa [Approx, norm_sub_comm]

theorem approx_comm : (a ≈[φ; δ] b) ↔ (b ≈[φ; δ] a) :=
  ⟨Approx.symm, Approx.symm⟩

theorem Approx.mono (h : a ≈[φ; δ] b) (hδ : δ ≤ δ') : a ≈[φ; δ'] b :=
  h.trans hδ

/-- Errors add along chains of approximations. -/
theorem Approx.trans (h₁ : a ≈[φ; δ] b) (h₂ : b ≈[φ; δ'] c) : a ≈[φ; δ + δ'] c := by
  have : a - c = (a - b) + (b - c) := by abel
  rw [Approx, this]
  exact (φ.norm_add_le _ _).trans (add_le_add h₁ h₂)

instance : @Trans A A A (Approx φ δ) (Approx φ δ') (Approx φ (δ + δ')) :=
  ⟨Approx.trans⟩

theorem approx_of_eq (h : a = b) (hδ : 0 ≤ δ) : a ≈[φ; δ] b :=
  h ▸ Approx.refl hδ a

theorem Approx.add (h : a ≈[φ; δ] b) (h' : a' ≈[φ; δ'] b') : a + a' ≈[φ; δ + δ'] b + b' := by
  have : a + a' - (b + b') = (a - b) + (a' - b') := by abel
  rw [Approx, this]
  exact (φ.norm_add_le _ _).trans (add_le_add h h')

theorem Approx.neg (h : a ≈[φ; δ] b) : -a ≈[φ; δ] -b := by
  rwa [Approx, neg_sub_neg, norm_sub_comm]

theorem Approx.sub (h : a ≈[φ; δ] b) (h' : a' ≈[φ; δ'] b') : a - a' ≈[φ; δ + δ'] b - b' := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

theorem Approx.smul (h : a ≈[φ; δ] b) (z : ℂ) : z • a ≈[φ; ‖z‖ * δ] z • b := by
  rw [Approx, ← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_left h (_root_.norm_nonneg z)

/-- Left multiplication by a contraction does not increase the state norm. -/
theorem norm_mul_le_of_star_mul_self_le_one (φ : AlgState A) {u : A} (hu : star u * u ≤ 1)
    (x : A) : φ.norm (u * x) ≤ φ.norm x := by
  rw [norm_eq_sqrt, norm_eq_sqrt]
  refine Real.sqrt_le_sqrt (φ.re_apply_mono ?_)
  have := star_left_conjugate_le_conjugate hu x
  simpa [star_mul, mul_assoc] using this

/-- Left multiplication by a contraction preserves closeness. -/
theorem Approx.mul_left (h : a ≈[φ; δ] b) {u : A} (hu : star u * u ≤ 1) :
    u * a ≈[φ; δ] u * b := by
  rw [Approx, ← mul_sub]
  exact (φ.norm_mul_le_of_star_mul_self_le_one hu _).trans h

/-- Left multiplication by an operator that stretches the state norm by at most `k` turns
`δ`-closeness into `kδ`-closeness. -/
theorem Approx.mul_left_of_norm_mul_le (h : a ≈[φ; δ] b) {u : A} {k : ℝ} (hk : 0 ≤ k)
    (hu : ∀ y, φ.norm (u * y) ≤ k * φ.norm y) : u * a ≈[φ; k * δ] u * b := by
  rw [Approx, ← mul_sub]
  exact (hu _).trans (mul_le_mul_of_nonneg_left h hk)

/-- The expectation of an operator is bounded by its state norm. -/
theorem norm_apply_le_norm (φ : AlgState A) (a : A) : ‖φ a‖ ≤ φ.norm a := by
  simpa using φ.norm_apply_star_mul_le 1 a

/-- Close operators have close expectations. -/
theorem Approx.norm_apply_sub_le (h : a ≈[φ; δ] b) : ‖φ a - φ b‖ ≤ δ := by
  rw [← map_sub]
  exact (φ.norm_apply_le_norm _).trans h

/-- Close operators have close correlations with any fixed operator:
`|φ(c⋆a) - φ(c⋆b)| ≤ ‖c‖_φ δ`. -/
theorem Approx.norm_apply_star_mul_sub_le (h : a ≈[φ; δ] b) (c : A) :
    ‖φ (star c * a) - φ (star c * b)‖ ≤ φ.norm c * δ := by
  rw [← map_sub, ← mul_sub]
  exact (φ.norm_apply_star_mul_le c _).trans (mul_le_mul_of_nonneg_left h (φ.norm_nonneg c))

end Approx

/-! ### Averages over questions -/

section Avg

variable {A : Type*} [Ring A] [PartialOrder A] [Algebra ℂ A]
  {Q : Type*} [Fintype Q]

/-- The **weighted state** `f ↦ ∑_q μ(q) φ_q(f_q)` on the product algebra `Q → A`. -/
noncomputable def avg (μ : PMF Q) (φ : Q → AlgState A) : AlgState (Q → A) where
  toFun f := ∑ q, ((μ q).toReal : ℂ) * φ q (f q)
  map_add' f g := by simp [map_add, mul_add, sum_add_distrib]
  map_smul' z f := by simp [map_smul, mul_sum, mul_left_comm]
  monotone' f g h := by
    refine sum_le_sum fun q _ => mul_le_mul_of_nonneg_left ((φ q).apply_mono (h q)) ?_
    exact_mod_cast ENNReal.toReal_nonneg
  map_one' := by
    simp only [Pi.one_apply, map_one, mul_one]
    exact_mod_cast Cslib.Probability.PMF.sum_toReal μ

theorem avg_apply (μ : PMF Q) (φ : Q → AlgState A) (f : Q → A) :
    avg μ φ f = ∑ q, ((μ q).toReal : ℂ) * φ q (f q) :=
  rfl

variable [StarRing A] [StarOrderedRing A] [StarModule ℂ A] [SelfAdjointDecompose A]

/-- The state norm of the weighted state is the averaged norm,
`‖f‖²_{avg μ φ} = ∑_q μ(q) ‖f_q‖²_{φ_q}`. -/
theorem norm_avg_sq (μ : PMF Q) (φ : Q → AlgState A) (f : Q → A) :
    (avg μ φ).norm f ^ 2 = ∑ q, (μ q).toReal * (φ q).norm (f q) ^ 2 := by
  rw [norm_sq, avg_apply, Complex.re_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [norm_sq, Pi.mul_apply, Pi.star_apply, Complex.re_ofReal_mul]

/-- **Averaged closeness**: `f ≈[avg μ φ; δ] g` exactly when `E_q ‖f_q - g_q‖² ≤ δ²`. -/
theorem approx_avg_iff {μ : PMF Q} {φ : Q → AlgState A} {f g : Q → A} {δ : ℝ} (hδ : 0 ≤ δ) :
    (f ≈[avg μ φ; δ] g) ↔ ∑ q, (μ q).toReal * (φ q).norm (f q - g q) ^ 2 ≤ δ ^ 2 := by
  rw [Approx, ← norm_avg_sq, ← Pi.sub_def]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _ _) hδ two_ne_zero).symm

/-- Closeness for every question gives closeness on average. -/
theorem approx_avg_of_forall {μ : PMF Q} {φ : Q → AlgState A} {f g : Q → A} {δ : ℝ}
    (h : ∀ q, f q ≈[φ q; δ] g q) (hδ : 0 ≤ δ) : f ≈[avg μ φ; δ] g := by
  rw [approx_avg_iff hδ]
  calc ∑ q, (μ q).toReal * (φ q).norm (f q - g q) ^ 2 ≤ ∑ q, (μ q).toReal * δ ^ 2 :=
        sum_le_sum fun q _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _ _) (h q) 2) ENNReal.toReal_nonneg
    _ = δ ^ 2 := by rw [← sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]

end Avg

end AlgState

end Cslib.Quantum
