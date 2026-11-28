/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Circuit.Boolean.CountingBound
import CslibFrontier.Computability.Circuit.Boolean.Hierarchy
import CslibFrontier.Computability.Circuit.Counting
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Checked clients of the Arora–Barak counting results of Sections 6.3 and 6.4 (web draft
2007-01-08).

* Theorem 6.15 in the draft's own size measure, which counts the `n` input vertices: for
  `n ≥ 100`, at most `2 ^ (2 ^ n / 4)` functions have circuits with fewer than `2 ^ n / (10 n)`
  vertices. This is the translation described on
  `Cslib.Circuits.Boolean.card_computableFunctions_two_pow_div_five_mul_le`.
* The hypotheses of `Cslib.Circuits.Boolean.SIZE_sub_ssubset_of_isLittleO` (Theorem 6.17) are
  satisfiable: `T n = n + 1` and `T' n = (n + 1) ^ 3 + 1` meet all of them. -/

set_option linter.privateModule false

namespace CslibFrontierTests.CircuitSizeHierarchy

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Filter Asymptotics
open scoped Finset

/-- Arora–Barak, Theorem 6.15, with the draft's vertex count `complexity + n`. -/
example (n : ℕ) (hn : 100 ≤ n) :
    #{f : BooleanFunction n |
      ((complexity interpretation (single f) + n : ℕ) : ℝ) < 2 ^ n / (10 * n)} ≤
      2 ^ (2 ^ n / 4) := by
  rw [← Set.ncard_coe_finset]
  refine (Set.ncard_le_ncard fun f hf => ?_).trans
    (card_computableFunctions_two_pow_div_five_mul_le (by omega))
  rw [Finset.mem_coe, Finset.mem_filter] at hf
  rw [mem_computableFunctions_iff_complexity_le, Nat.le_div_iff_mul_le (by omega)]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [lt_div_iff₀ (by positivity)] at hf
  push_cast at hf
  have : (complexity interpretation (single f) : ℝ) * (5 * n) ≤ 2 ^ n := by nlinarith
  exact_mod_cast this

/-- The hypotheses of Arora–Barak, Theorem 6.17, at `T n = n + 1` and `T' n = (n + 1) ^ 3 + 1`. -/
example : SIZE (fun n => (n + 1) - n) ⊂ SIZE (fun n => ((n + 1) ^ 3 + 1) - n) := by
  refine SIZE_sub_ssubset_of_isLittleO (fun n => n.lt_succ_self) (fun n => ?_) ?_ ?_
  · have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (n + 1)
    omega
  · filter_upwards [Nat.eventually_add_one_pow_mul_lt_pow 4 Nat.one_lt_two,
      eventually_ge_atTop 200] with n hn h200
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [lt_div_iff₀ (by positivity)]
    have h1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ n.succ_pos
    have : ((n + 1) ^ 3 + 1) * (100 * n) < 2 ^ n := by
      calc ((n + 1) ^ 3 + 1) * (100 * n) ≤ (n + 1) ^ 3 * 200 * n := by nlinarith
        _ ≤ (n + 1) ^ 3 * (n + 1) * n := by gcongr; omega
        _ = (n + 1) ^ 4 * n := by ring
        _ < 2 ^ n := hn
    exact_mod_cast this
  · have hlin : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hlog := (Real.isLittleO_log_id_atTop.comp_tendsto hlin).const_mul_left 1
    have h := (isBigO_refl (fun n : ℕ => (n : ℝ) + 1) atTop).mul_isLittleO hlog
    refine (h.congr_left fun n => by simp).trans_isBigO ?_
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
    simp only [Function.comp_apply, id, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    push_cast
    nlinarith

end CslibFrontierTests.CircuitSizeHierarchy
