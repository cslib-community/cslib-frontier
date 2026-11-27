/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.NaturalProof.Restriction

open Cslib Cslib.BitString Cslib.Circuits.Boolean Cslib.Probability Filter
open scoped Topology

/-- For the fixed exponent one half, a majority of truth tables eventually satisfy the property
that every restriction fixing at most `n - √n` coordinates remains nonconstant. -/
example : ∀ᶠ n : ℕ in atTop,
    (1 / 2 : ℝ) ≤ ((PMF.uniformOfFintype (BitString n → Bool)).toOuterMeasure
      {f | ∀ ρ : PartialAssignment (Fin n), (ρ.support.card : ℝ) ≤ n - (n : ℝ) ^ (1 / 2 : ℝ) →
        ¬ ∃ b : Bool, ∀ x, ρ.Agrees x → f x = b}).toReal := by
  have h := tendsto_prob_no_constant_restriction (1 / 2) (by norm_num [Set.mem_Ioo])
  exact (h.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono
    fun _ hn => le_of_lt hn
