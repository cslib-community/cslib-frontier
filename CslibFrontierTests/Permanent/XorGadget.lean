/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of the XOR gadget)

import CslibFrontier.Computability.Complexity.Problems.Permanent.XorGadget

/-! Checked clients of the XOR gadget of Arora and Barak's Figure 9.3: a concrete digraph in
which the replaced edges have weight `1`, as in the proof of Theorem 9.8. -/

set_option linter.privateModule false

namespace Cslib.Complexity.XorGadget

open Finset Equiv

/-- The complete digraph with loops on three vertices, every edge of weight `1`. -/
def ones : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun _ _ => 1

/-- Two of the six cycle covers of the complete digraph use exactly one of the edges `0 → 1`
and `1 → 2`: `(0 1)` and `(1 2)`. Replacing both edges by the gadget therefore gives a digraph
on seven vertices whose permanent is `4 · 2 = 8`. -/
example : (replace ones 0 1 1 2).permanent = 8 := by
  rw [permanent_replace ones (by decide)]
  simp only [ones, Matrix.of_apply, prod_const_one, sum_const, nsmul_eq_mul, mul_one]
  rw [show (univ.filter fun σ : Perm (Fin 3) => Xor (σ 0 = 1) (σ 1 = 2)).card = 2 by decide]
  rfl

/-- The cover `(0 1)` uses `0 → 1` but not `1 → 2`; its corresponding covers of the replaced
digraph weigh `4` in total. -/
example : ∑ π ∈ lift 0 1 1 2 (swap (0 : Fin 3) 1), ∏ z, replace ones 0 1 1 2 z (π z) = 4 := by
  rw [sum_lift ones (Or.inl ⟨by decide, by decide⟩)]
  simp [ones]

end Cslib.Complexity.XorGadget
