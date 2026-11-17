/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.Approximation.Hastad.LinearTest

/-! Checked clients of the corrected Corollary 19.13 of Arora and Barak (Exercise 19.2): the
noise-weighted and the absolute low-degree cubic Fourier sums, at sample parameters. -/

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

end CslibFrontierTests.LinearTestLowDegree
