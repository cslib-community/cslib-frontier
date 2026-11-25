/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.CircuitLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Element distinctness on binary-basis circuits -/

open Cslib.Circuits Cslib.Circuits.Boolean Filter

-- Three four-bit records. Moving one set bit makes the last two records coincide.
example : elementDistinctness 3 4 (fun i => decide (i.val = 4 ∨ i.val = 9)) = true := by
  decide +kernel

example : elementDistinctness 3 4 (fun i => decide (i.val = 4 ∨ i.val = 8)) = false := by
  decide +kernel

-- Even the smallest circuit eventually exceeds every fixed linear gate budget.
example (A : ℝ) : ∀ᶠ m : ℕ in atTop,
    let k := 2 * Nat.clog 2 m
    A * (m * k : ℕ) <
      complexity (fullInterpretation (k := 2)) (single (elementDistinctness m k)) := by
  obtain ⟨ε, c, hε, hc, h⟩ := elementDistinctness_circuit_lower_bound
  let n (m : ℕ) := m * (2 * Nat.clog 2 m)
  have grow : Tendsto n atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_ge_atTop 2] with m hm
    exact Nat.le_mul_of_pos_right m (Nat.mul_pos (by decide) (Nat.clog_pos (by decide) hm))
  have factor : Tendsto (fun m => c * (Real.logb 2 (n m)) ^ ε) atTop atTop :=
    ((tendsto_rpow_atTop hε).comp ((Real.tendsto_logb_atTop (by norm_num : 1 < (2 : ℝ))).comp
      (tendsto_natCast_atTop_atTop.comp grow))).const_mul_atTop hc
  filter_upwards [h, factor.eventually_ge_atTop A] with m hm hA
  obtain ⟨C, hC, hs⟩ := exists_computes_size_eq_complexity
    (I := fullInterpretation (k := 2)) (f := single (elementDistinctness m (2 * Nat.clog 2 m)))
  calc
    A * (n m : ℝ) ≤ (c * (Real.logb 2 (n m)) ^ ε) * n m := by gcongr
    _ = c * n m * (Real.logb 2 (n m)) ^ ε := by ring
    _ < _ := hs ▸ hm C hC
