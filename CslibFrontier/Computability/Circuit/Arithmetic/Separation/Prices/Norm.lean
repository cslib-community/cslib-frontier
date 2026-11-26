/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Norms of loads

For the proof of Theorem G.2 (thm:laws) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]: the
norms `‖n‖² = Σ n_e² / α e` of loads (`Separation.Prices.loadNorm`, a weighted Euclidean norm by
`Separation.Prices.loadNorm_eq_norm`). If `Σ_e α e · w(e)² ≤ Σ_ν β ν · w(ν)²`, there is a new load
of norm at most `(1 + η) S R` that costs at least as much as `S` times an old load of norm at most
`R` (`Separation.Prices.exists_load`).

## Main definitions

* `Separation.Prices.loadNorm`, `Separation.Prices.Loads`.

## Main results

* `Separation.Prices.loadNorm_add_le`, `Separation.Prices.loadNorm_sum_le`,
  `Separation.Prices.sum_mul_le_loadNorm`, `Separation.Prices.finite_loads`,
  `Separation.Prices.exists_load`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem G.2 of the paper; module `Nc.Price.Norm`
-/

@[expose] public section


namespace Cslib.Circuits.Arithmetic.Separation.Prices

open Finset

section Norm

variable {E : Type} [Fintype E]

/-- The norm of a load: √(Σ n_e²/α e). -/
noncomputable def loadNorm (α : E → ℝ) (n : E → ℝ) : ℝ := √(∑ e, n e ^ 2 / α e)

theorem loadNorm_eq_norm (α : E → ℝ) (hα : ∀ e, 0 < α e) (n : E → ℝ) :
    loadNorm α n = ‖(WithLp.toLp 2 fun e => n e / √(α e) : EuclideanSpace ℝ E)‖ := by
  rw [EuclideanSpace.norm_eq, loadNorm]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (hα e).le]

theorem loadNorm_nonneg (α : E → ℝ) (n : E → ℝ) : 0 ≤ loadNorm α n := Real.sqrt_nonneg _

theorem loadNorm_add_le (α : E → ℝ) (hα : ∀ e, 0 < α e) (n n' : E → ℝ) :
    loadNorm α (fun e => n e + n' e) ≤ loadNorm α n + loadNorm α n' := by
  rw [loadNorm_eq_norm α hα, loadNorm_eq_norm α hα, loadNorm_eq_norm α hα]
  exact (congrArg norm (PiLp.ext fun e => add_div (n e) (n' e) _)).trans_le (norm_add_le _ _)

theorem loadNorm_smul (α : E → ℝ) {c : ℝ} (hc : 0 ≤ c) (n : E → ℝ) :
    loadNorm α (fun e => c * n e) = c * loadNorm α n := by
  simp_rw [loadNorm, mul_pow, mul_div_assoc, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem loadNorm_mono (α : E → ℝ) (hα : ∀ e, 0 < α e) {n n' : E → ℝ} (h0 : ∀ e, 0 ≤ n e)
    (h : ∀ e, n e ≤ n' e) : loadNorm α n ≤ loadNorm α n' :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun e _ =>
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (h0 e) (h e) 2) (hα e).le)

theorem loadNorm_zero (α : E → ℝ) : loadNorm α (fun _ => 0) = 0 := by simp [loadNorm]

theorem loadNorm_sum_le {B : Type*} (s : Finset B) (α : E → ℝ) (hα : ∀ e, 0 < α e) (n : B → E → ℝ) :
    loadNorm α (fun e => ∑ β ∈ s, n β e) ≤ ∑ β ∈ s, loadNorm α (n β) := by
  rw [loadNorm_eq_norm α hα]
  exact ((congrArg norm (PiLp.ext fun _ => by simp [Finset.sum_div])).trans_le
    (norm_sum_le s _)).trans (Finset.sum_le_sum fun β _ => (loadNorm_eq_norm α hα (n β)).ge)

theorem le_loadNorm (α : E → ℝ) (hα : ∀ e, 0 < α e) (n : E → ℝ) (e : E) :
    n e ≤ loadNorm α n * √(α e) := by
  rw [loadNorm, ← Real.sqrt_mul' _ (hα e).le]
  exact (le_abs_self _).trans <| Real.abs_le_sqrt <| (div_le_iff₀ (hα e)).1 <|
    Finset.single_le_sum (fun i _ => div_nonneg (sq_nonneg _) (hα i).le) (Finset.mem_univ e)

/-- Cauchy–Schwarz. -/
theorem sum_mul_le_loadNorm (α : E → ℝ) (hα : ∀ e, 0 < α e) (n w : E → ℝ) :
    ∑ e, n e * w e ≤ loadNorm α n * √(∑ e, α e * w e ^ 2) := by
  rw [loadNorm, ← Real.sqrt_mul (Finset.sum_nonneg fun e _ => div_nonneg (sq_nonneg _) (hα e).le)]
  refine (le_abs_self _).trans <| Real.abs_le_sqrt ?_
  have e1 (e) : n e / √(α e) * (√(α e) * w e) = n e * w e := by
    have := (Real.sqrt_pos.2 (hα e)).ne'
    field_simp
  simpa only [e1, div_pow, mul_pow, fun e => Real.sq_sqrt (hα e).le] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun e => n e / √(α e)) (fun e => √(α e) * w e)

end Norm

/-- Natural loads of bounded norm: a finite set. -/
def Loads {N : Type} [Fintype N] (β : N → ℝ) (r : ℝ) : Type :=
  {x : N → ℕ // loadNorm β (fun ν => (x ν : ℝ)) ≤ r}

theorem finite_loads {N : Type} [Fintype N] (β : N → ℝ) (hβ : ∀ ν, 0 < β ν) (r : ℝ) :
    Finite (Loads β r) :=
  Set.Finite.to_subtype (s := {x : N → ℕ | loadNorm β (fun ν => (x ν : ℝ)) ≤ r}) <|
    (Set.Finite.pi' fun ν : N => Set.finite_Iic ⌊r * √(β ν)⌋₊).subset fun x hx ν =>
      Nat.le_floor <| (le_loadNorm β hβ (fun ν => (x ν : ℝ)) ν).trans <|
        mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg _)

/-- One price: if Σα·w² ≤ Σβ·w′² and ‖n‖ ≤ R, then for S large (S·η·R ≥ ‖1‖) there is a natural load
x with ‖x‖ ≤ (1+η)·S·R and Σ S·n·w ≤ Σ x·w′. -/
theorem exists_load {E N : Type} [Fintype E] [Fintype N] (α : E → ℝ) (hα : ∀ e, 0 < α e)
    (β : N → ℝ) (hβ : ∀ ν, 0 < β ν) (w : E → ℝ) (w' : N → ℝ) (hw' : ∀ ν, 0 ≤ w' ν)
    (h : ∑ e, α e * w e ^ 2 ≤ ∑ ν, β ν * w' ν ^ 2) (n : E → ℕ) {R η : ℝ} (hR : 0 ≤ R)
    (hη : 0 ≤ η) (hn : loadNorm α (fun e => (n e : ℝ)) ≤ R) (S : ℕ)
        (hS : loadNorm β (fun _ => 1) ≤ S * η * R) :
    ∃ x : N → ℕ, loadNorm β (fun ν => (x ν : ℝ)) ≤ (1 + η) * S * R ∧
      ∑ e, ((S * n e : ℕ) : ℝ) * w e ≤ ∑ ν, (x ν : ℝ) * w' ν := by
  set W := √(∑ ν, β ν * w' ν ^ 2) with hW
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hQ0 : 0 ≤ ∑ ν, β ν * w' ν ^ 2 :=
    Finset.sum_nonneg fun ν _ => mul_nonneg (hβ ν).le (sq_nonneg _)
  have hWsq : W ^ 2 = ∑ ν, β ν * w' ν ^ 2 := Real.sq_sqrt hQ0
  have h1 : ∑ e, ((S * n e : ℕ) : ℝ) * w e ≤ S * R * W := by
    have e1 : ∑ e, ((S * n e : ℕ) : ℝ) * w e = S * ∑ e, (n e : ℝ) * w e := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by push_cast; ring
    rw [e1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hS0
    refine (sum_mul_le_loadNorm α hα _ _).trans ?_
    exact mul_le_mul hn (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _) hR
  rcases hW0.eq_or_lt with h0 | h0
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · simp only [Nat.cast_zero, loadNorm_zero]
      positivity
    · rw [← h0, mul_zero] at h1
      simpa using h1
  · refine ⟨fun ν => ⌈S * R / W * (β ν * w' ν)⌉₊, ?_, ?_⟩
    · have h2 : loadNorm β (fun ν => ((⌈S * R / W * (β ν * w' ν)⌉₊ : ℕ) : ℝ)) ≤
          loadNorm β (fun ν => S * R / W * (β ν * w' ν) + 1) := by
        refine loadNorm_mono β hβ (fun ν => Nat.cast_nonneg _) fun ν => ?_
        exact (Nat.ceil_lt_add_one (mul_nonneg (by positivity)
          (mul_nonneg (hβ ν).le (hw' ν)))).le
      have h3 : loadNorm β (fun ν => β ν * w' ν) = W := by
        rw [loadNorm, hW]
        congr 1
        refine Finset.sum_congr rfl fun ν _ => ?_
        have := (hβ ν).ne'
        field_simp
      refine h2.trans ((loadNorm_add_le β hβ _ _).trans ?_)
      rw [loadNorm_smul β (by positivity), h3, div_mul_cancel₀ _ h0.ne']
      linarith
    · refine h1.trans ?_
      have h4 : S * R * W = ∑ ν, S * R / W * (β ν * w' ν) * w' ν := by
        simp only [mul_assoc, ← sq, ← Finset.mul_sum, ← hWsq]
        field_simp
      rw [h4]
      exact Finset.sum_le_sum fun ν _ => mul_le_mul_of_nonneg_right (Nat.le_ceil _) (hw' ν)

end Cslib.Circuits.Arithmetic.Separation.Prices
