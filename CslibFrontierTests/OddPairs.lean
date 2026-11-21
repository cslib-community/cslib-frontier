/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Data.BitString.OddPairs

/-! # Averages over the odd pairs of bit strings

Concrete instances: on one bit, the only odd pair is `(1, 1)`, so the masked average of the
constant `1` is `1/4`, the density of the odd pairs; with no bits there are no odd pairs; and with
both functions equal to `1`, the half-average bound is an equality.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.OddPairs

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- On one bit, one of the four pairs is odd. -/
example : oddExpect (ι := Unit) (fun _ _ => (1 : ℝ)) = 1 / 4 := by
  have hcard : ∀ a : Unit → Bool, ((#{b : Unit → Bool | a ⬝ᵥ b = true} : ℕ) : ℝ) =
      if a () then 1 else 0 := fun a => by
    have : ∀ a : Unit → Bool, #{b : Unit → Bool | a ⬝ᵥ b = true} = if a () then 1 else 0 := by
      decide
    rw [this a]; split_ifs <;> simp
  have hsum : ∑ a : Unit → Bool, (if a () then (1 : ℝ) else 0) = 1 := by
    rw [← (Equiv.funUnique Unit Bool).symm.sum_comp]
    simp
  rw [oddExpect_def, Fintype.expect_eq_sum_div_card]
  simp only [Fintype.expect_eq_sum_div_card, ← sum_filter, sum_const, nsmul_eq_mul, mul_one,
    hcard, Fintype.card_fun, Fintype.card_unit, Fintype.card_bool]
  rw [div_eq_mul_inv _ ((2 ^ 1 : ℕ) : ℝ)]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, hsum]
  norm_num

/-- **Half average**, with both functions equal to `1`: the factor `2` is exactly what is needed,
since half of the strings `c` have `a · c = 1`. -/
example : (1 : ℝ) ≤ 2 * 𝔼 c : Unit → Bool, if (fun _ => true) ⬝ᵥ c = true then 1 else 0 :=
  le_two_mul_expect_ite_of_forall (a := fun _ : Unit => true) (fun h => by
    simpa using congrFun h ()) (h := fun _ => (1 : ℝ)) fun _ _ => le_rfl

/-- The odd pairs of one-bit strings have density `1/4`. -/
example : ((oddPairs Unit).dens : ℝ) = 1 / 4 := by
  rw [dens_oddPairs, Fintype.card_unit]
  norm_num

/-- With no bits there are no odd pairs, and every masked average vanishes. -/
example (f : (Empty → Bool) → (Empty → Bool) → ℝ) : oddExpect f = 0 := by
  rw [oddExpect_eq_dens_smul, dens_oddPairs, Fintype.card_empty]
  norm_num

end CslibFrontierTests.OddPairs
