/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
public import Cslib.Foundations.Data.BitString
import CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary

/-!
# Weighted progress measures for quantum query adversary arguments

A `T`-query quantum algorithm (`Cslib.Quantum.run`) running from a unit initial state `ψ₀` preserves
inner products up to the positions where two inputs `x` and `y` differ:
one controlled phase-oracle step changes `⟨ψ, φ⟩` by `2 ∑_{i : xᵢ ≠ yᵢ} ⟨Π_i ψ, Π_i φ⟩`
(`Cslib.Quantum.inner_phaseOracle_phaseOracle`), where `Π_i` is `Cslib.Quantum.ctrlProj`.

For any finite set `R` of input pairs and nonnegative pair weights
`γ : BitString N × BitString N → ℝ`, the **weighted progress measure** after `t` queries is
`∑_{(x, y) ∈ R} γ(x, y) |⟨ψₓᵗ, ψ_yᵗ⟩|` (`Cslib.Quantum.weightedProgress`). Identifying
`Cslib.Quantum.run` with `Cslib.Quantum.runValue Cslib.Quantum.phaseStep`
(`Cslib.Quantum.runValue_phaseStep`) specializes the general value-query progress bounds of
`CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary` directly to phase-oracle
algorithms (`weightedProgress_zero`, `weightedProgress_zero_sub_le`, and
`Cslib.Quantum.one_sub_mul_sum_le_of_sq_le`), used by the spectral sensitivity bound
(`CslibFrontier.Computability.QueryComplexity.Quantum.Adversary`) and weighted adversary schemes
(`CslibFrontier.Computability.QueryComplexity.Quantum.WeightedAdversary`).

## Main definitions

* `Cslib.Quantum.weightedProgress`: weighted sum of state overlaps over a pair set after
  `t` queries.

## Main results

* `Cslib.Quantum.inner_phaseOracle_phaseOracle`: one query changes the overlap of two states by
  `2 ∑_{i : xᵢ ≠ yᵢ} ⟨Π_i ψ, Π_i φ⟩`.
* `Cslib.Quantum.norm_inner_phaseOracle_phaseOracle_ge`: per-step overlap loss bound.
* `Cslib.Quantum.sum_sq_norm_ctrlProj_le`: the query magnitudes of a unit state sum to at most `1`.
* `Cslib.Quantum.weightedProgress_zero`: at time `0`, `weightedProgress` equals `∑ p ∈ R, γ p`.
* `Cslib.Quantum.weightedProgress_zero_sub_le`: `T` queries lower `weightedProgress` by at most
  `T * (∑ x ∈ R.image Prod.fst, α x + ∑ y ∈ R.image Prod.snd, β y)`.
* `Cslib.Quantum.one_sub_mul_sum_le_of_sq_le`: generic weighted adversary inequality.
-/

public section

namespace Cslib.Quantum

open Finset Function

variable {N : ℕ} {W : Type*} [Fintype W]

/-- **One query on two inputs**: the oracles of `x` and `y` differ only on the query indices `i`
with `xᵢ ≠ yᵢ` and control bit `1`, so applying them changes the overlap of two states by
`2 ∑_{i : xᵢ ≠ yᵢ} ⟨Π_i ψ, Π_i φ⟩`. -/
theorem inner_phaseOracle_phaseOracle (x y : Fin N → Bool) (ψ φ : State N W) :
    inner ℂ (phaseOracle x ψ) (phaseOracle y φ) =
      inner ℂ ψ φ - 2 * ∑ i with x i ≠ y i, inner ℂ (ctrlProj i ψ) (ctrlProj i φ) := by
  classical
  simp only [PiLp.inner_apply, RCLike.inner_apply', mul_sum]
  rw [sum_comm, ← sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  obtain ⟨j, b, w⟩ := p
  simp only [phaseOracle_apply, ctrlProj, PiLp.toLp_apply]
  cases b
  · simp
  · by_cases hj : x j = y j
    · have : ∀ i ∈ univ.filter (fun i => x i ≠ y i), (2 : ℂ) *
          ((starRingEnd ℂ) (if j = i ∧ true = true then ψ.ofLp (j, true, w) else 0) *
            (if j = i ∧ true = true then φ.ofLp (j, true, w) else 0)) = 0 := by
        intro i hi
        have hji : j ≠ i := by grind
        simp [hji]
      rw [sum_eq_zero this, hj]
      cases y j <;> simp
    · rw [sum_eq_single j]
      · cases hx : x j <;> cases hy : y j <;> simp_all <;> ring
      · intro i _ hij
        simp [Ne.symm hij]
      · intro h
        simp [hj] at h

/-- One query lowers the overlap of the states on two inputs by at most
`2 ∑_{i : xᵢ ≠ yᵢ} ‖Π_i ψ‖ ‖Π_i φ‖`. -/
theorem norm_inner_phaseOracle_phaseOracle_ge (x y : Fin N → Bool) (ψ φ : State N W) :
    ‖inner ℂ ψ φ‖ - 2 * ∑ i with x i ≠ y i, ‖ctrlProj i ψ‖ * ‖ctrlProj i φ‖ ≤
      ‖inner ℂ (phaseOracle x ψ) (phaseOracle y φ)‖ := by
  rw [inner_phaseOracle_phaseOracle]
  have h₁ : ‖∑ i with x i ≠ y i, inner ℂ (ctrlProj i ψ) (ctrlProj i φ)‖ ≤
      ∑ i with x i ≠ y i, ‖ctrlProj i ψ‖ * ‖ctrlProj i φ‖ :=
    (norm_sum_le _ _).trans (sum_le_sum fun i _ => norm_inner_le_norm _ _)
  have h₂ := norm_sub_norm_le (inner ℂ ψ φ)
    (2 * ∑ i with x i ≠ y i, inner ℂ (ctrlProj i ψ) (ctrlProj i φ))
  rw [norm_mul, RCLike.norm_ofNat] at h₂
  linarith

/-- The query magnitudes of a unit state sum to at most `1`. -/
theorem sum_sq_norm_ctrlProj_le (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (x : BitString N) (t : ℕ) :
    ∑ i, ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 ≤ 1 :=
  calc
    ∑ i, ‖ctrlProj i (run U ψ₀ x t)‖ ^ 2 ≤ ∑ i, regProb (run U ψ₀ x t) i :=
      sum_le_sum fun i _ => norm_sq_ctrlProj_le i _
    _ = 1 := by rw [sum_regProb, norm_run, hψ₀, one_pow]

/-- The weighted progress measure of a quantum query adversary argument: the weighted sum of state
overlaps on `R` after `t` queries. -/
noncomputable def weightedProgress (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W)
    (R : Finset (BitString N × BitString N)) (γ : BitString N × BitString N → ℝ) (t : ℕ) : ℝ :=
  ∑ p ∈ R, γ p * ‖inner ℂ (run U ψ₀ p.1 t) (run U ψ₀ p.2 t)‖

private theorem weightedProgress_eq_valueWeightedProgress
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W)
    (R : Finset (BitString N × BitString N)) (γ : BitString N × BitString N → ℝ) (t : ℕ) :
    weightedProgress U ψ₀ R γ t = valueWeightedProgress phaseStep U ψ₀ R γ t := by
  simp only [weightedProgress, valueWeightedProgress, runValue_phaseStep]

/-- Before any query the states agree, so the weighted progress measure is `∑ p ∈ R, γ p`. -/
theorem weightedProgress_zero (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (R : Finset (BitString N × BitString N))
    (γ : BitString N × BitString N → ℝ) :
    weightedProgress U ψ₀ R γ 0 = ∑ p ∈ R, γ p := by
  rw [weightedProgress_eq_valueWeightedProgress]
  exact valueWeightedProgress_zero phaseStep U hψ₀ R γ

/-- **Telescoping**: `T` queries lower `weightedProgress` by at most `T` times the endpoint
weight budgets. -/
theorem weightedProgress_zero_sub_le
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1)
    (R : Finset (BitString N × BitString N)) (γ : BitString N × BitString N → ℝ)
    (a b : BitString N × BitString N → Fin N → ℝ) (α β : BitString N → ℝ)
    (hγ : ∀ p ∈ R, 0 ≤ γ p)
    (ha : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ a p i)
    (hb : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ b p i)
    (hγsq : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → γ p ^ 2 ≤ a p i * b p i)
    (hα : ∀ x ∈ R.image Prod.fst, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.1 = x, a p i ≤ α x)
    (hβ : ∀ y ∈ R.image Prod.snd, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.2 = y, b p i ≤ β y)
    (T : ℕ) :
    weightedProgress U ψ₀ R γ 0 - weightedProgress U ψ₀ R γ T ≤
      T * (∑ x ∈ R.image Prod.fst, α x + ∑ y ∈ R.image Prod.snd, β y) := by
  simpa only [weightedProgress_eq_valueWeightedProgress] using
    valueWeightedProgress_zero_sub_le phaseStep U hψ₀ R γ a b α β hγ ha hb hγsq hα hβ T

/-- **Weighted quantum adversary inequality**: if after `T` queries the states on every pair in
`R` have overlap at most `δ`, and weights `a, b` satisfy `γ(p)² ≤ a(p, i) b(p, i)` whenever
`p.1 i ≠ p.2 i` with coordinatewise fiber budgets `α` and `β`, then
`(1 - δ) ∑_{p ∈ R} γ p ≤ T (∑_{x ∈ fst(R)} α x + ∑_{y ∈ snd(R)} β y)`. -/
theorem one_sub_mul_sum_le_of_sq_le
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (R : Finset (BitString N × BitString N)) (γ : BitString N × BitString N → ℝ)
    {δ : ℝ} (hδ : ∀ p ∈ R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ)
    (a b : BitString N × BitString N → Fin N → ℝ) (α β : BitString N → ℝ)
    (hγ : ∀ p ∈ R, 0 ≤ γ p)
    (ha : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ a p i)
    (hb : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ b p i)
    (hγsq : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → γ p ^ 2 ≤ a p i * b p i)
    (hα : ∀ x ∈ R.image Prod.fst, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.1 = x, a p i ≤ α x)
    (hβ : ∀ y ∈ R.image Prod.snd, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.2 = y, b p i ≤ β y) :
    (1 - δ) * ∑ p ∈ R, γ p ≤
      T * (∑ x ∈ R.image Prod.fst, α x + ∑ y ∈ R.image Prod.snd, β y) :=
  one_sub_mul_sum_le_of_sq_le_value phaseStep U hψ₀ T R γ
    (by simpa only [runValue_phaseStep] using hδ) a b α β hγ ha hb hγsq hα hβ

end Cslib.Quantum
