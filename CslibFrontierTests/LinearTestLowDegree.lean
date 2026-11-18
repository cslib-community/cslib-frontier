/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.Approximation.Hastad.LinearTest
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Checked clients of the corrected Corollary 19.13 of Arora and Barak (Exercise 19.2): the
noise-weighted and the absolute low-degree cubic Fourier sums, at sample parameters.

**The printed corollary is false.** The table `nae` on three bits is `true` (sign `-1`) exactly at
`000` and `111`. Its sign is `1/2 - (χ₀₁ + χ₀₂ + χ₁₂) / 2` (`fourierCoeff_nae`). At noise rate
`ρ = 1/4` the linearity test accepts it with probability `1/2 + 1/64` (`linearProb_nae`), so
`δ = 1/64`. For every `k ≥ 2` the unweighted low-degree cubic sum is `-1/4`
(`sum_lowDegree_cube_nae`), below `2δ - ε = -7/32` at `ε = 1/4`. The printed cutoff
`ln (1/ε) / (2ρ) = 2 ln 4` exceeds `2`, so every admissible `k` is a counterexample. -/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearTestLowDegree

open Finset Cslib.BitString Cslib.PCP.Hastad

/-- At `ε = e⁻¹` and `ρ = 1/4` the cutoff `k = 2` suffices: `ln e / (1/2) = 2`. -/
example {β : Type} [Fintype β] [DecidableEq β] (A : (β → Bool) → Bool) {δ : ℝ}
    (hA : 1 / 2 + δ ≤ linearProb id (1 / 4) A A) :
    2 * δ - Real.exp (-1) ≤ ∑ T ∈ univ.filter (fun T : Finset β => #T ≤ 2),
      |fourierCoeff (fun g => signVal (A g)) T| ^ 3 := by
  refine two_mul_sub_le_sum_lowDegree_abs_cube (by norm_num) (by norm_num) (Real.exp_pos _)
    ?_ A hA
  rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  norm_num

/-- Lemma 19.12 at noise rate `0`: the correlation is the cubic Fourier sum. -/
example {β : Type} [Fintype β] [DecidableEq β] (A : (β → Bool) → Bool) :
    linearCorr id 0 A A = ∑ T : Finset β, fourierCoeff (fun g => signVal (A g)) T ^ 3 := by
  simp [linearCorr_id_eq_sum]

/-! ### The counterexample to the printed Corollary 19.13 -/

/-- The table on three bits that is `true` (sign `-1`) exactly at `000` and `111`. -/
private def nae (g : Fin 3 → Bool) : Bool := g 0 == g 1 && g 1 == g 2

/-- The sign of `nae` as a combination of characters. -/
private theorem signVal_nae (x : Fin 3 → Bool) :
    signVal (nae x) = 1 / 2 - 1 / 2 * chi ℝ {0, 1} x - 1 / 2 * chi ℝ {0, 2} x -
      1 / 2 * chi ℝ {1, 2} x := by
  simp only [chi_eq_prod_signVal, prod_pair (show (0 : Fin 3) ≠ 1 by decide),
    prod_pair (show (0 : Fin 3) ≠ 2 by decide), prod_pair (show (1 : Fin 3) ≠ 2 by decide), nae]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> norm_num [signVal]

/-- The Fourier coefficients of `nae`: `1/2` at `∅`, `-1/2` at the three pairs, `0` elsewhere. -/
private theorem fourierCoeff_nae (T : Finset (Fin 3)) :
    fourierCoeff (fun g => signVal (nae g)) T =
      (if T = ∅ then 1 / 2 else 0) - 1 / 2 * (if {0, 1} = T then 1 else 0) -
        1 / 2 * (if {0, 2} = T then 1 else 0) - 1 / 2 * (if {1, 2} = T then 1 else 0) := by
  simp only [signVal_nae]
  rw [fourierCoeff_sub, fourierCoeff_sub, fourierCoeff_sub, fourierCoeff_const,
    fourierCoeff_const_mul, fourierCoeff_const_mul, fourierCoeff_const_mul, fourierCoeff_chi,
    fourierCoeff_chi, fourierCoeff_chi]

private theorem univ_finset_fin_three : (univ : Finset (Finset (Fin 3))) =
    {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by
  decide

/-- Lemma 19.12 at `ρ = 1/4`: the test accepts `nae` with probability `1/2 + 1/64`. -/
private theorem linearProb_nae : linearProb id (1 / 4) nae nae = 1 / 2 + 1 / 64 := by
  rw [linearProb_eq_add_linearCorr, linearCorr_id_eq_sum, univ_finset_fin_three]
  simp (disch := decide) only [sum_insert, sum_singleton, fourierCoeff_nae]
  simp (config := { decide := true })
  norm_num

/-- For every `k ≥ 2`, the unweighted low-degree cubic sum of `nae` is `-1/4`. -/
private theorem sum_lowDegree_cube_nae {k : ℕ} (hk : 2 ≤ k) :
    ∑ T ∈ univ.filter (fun T : Finset (Fin 3) => #T ≤ k),
      fourierCoeff (fun g => signVal (nae g)) T ^ 3 = -1 / 4 := by
  rw [sum_filter, univ_finset_fin_three]
  simp (disch := decide) only [sum_insert, sum_singleton, fourierCoeff_nae]
  simp (config := { decide := true })
  simp only [hk, ite_true]
  norm_num

/-- At `k = 2`: acceptance `1/2 + δ` with `δ = 1/64`, but the unweighted sum `-1/4` is below
`2δ - ε = -7/32` for `ε = 1/4`. -/
example : ∑ T ∈ univ.filter (fun T : Finset (Fin 3) => #T ≤ 2),
      fourierCoeff (fun g => signVal (nae g)) T ^ 3 < 2 * (1 / 64) - 1 / 4 := by
  rw [sum_lowDegree_cube_nae le_rfl]
  norm_num

/-- **The printed Corollary 19.13 is false** [Arora and Barak, draft 2007-01-08, p. 393/409].
Its hypotheses hold for `nae` with `ρ = ε = 1/4` (in `(0, 1/2)` and `(0, 1)`) and `δ = 1/64 > 0`:
the test accepts with probability at least `1/2 + δ`. Yet for every `k` at or above the cutoff
`ln (1/ε) / (2ρ)`, the unweighted sum `∑_{#T ≤ k} F̂(T) ^ 3` is below `2δ - ε`. -/
example : ∃ (A : (Fin 3 → Bool) → Bool) (ρ ε δ : ℝ), 0 < ρ ∧ ρ < 1 / 2 ∧ 0 < ε ∧ ε < 1 ∧
    0 < δ ∧ 1 / 2 + δ ≤ linearProb id ρ A A ∧
    ∀ k : ℕ, Real.log (1 / ε) / (2 * ρ) ≤ k →
      ∑ T ∈ univ.filter (fun T : Finset (Fin 3) => #T ≤ k),
        fourierCoeff (fun g => signVal (A g)) T ^ 3 < 2 * δ - ε := by
  refine ⟨nae, 1 / 4, 1 / 4, 1 / 64, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, linearProb_nae.ge, fun k hk => ?_⟩
  -- the cutoff `2 ln 4` exceeds `2`, since `e < 4`
  have hlog : 1 < Real.log 4 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (Real.exp_one_lt_d9.trans (by norm_num))
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) < k := by
      have h4 : Real.log (1 / (1 / 4 : ℝ)) / (2 * (1 / 4)) = 2 * Real.log 4 := by norm_num; ring
      linarith
    exact_mod_cast this.le
  rw [sum_lowDegree_cube_nae hk2]
  norm_num

end CslibFrontierTests.LinearTestLowDegree
