/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.GUOAccumulator.Security
import CslibFrontier.Crypto.Negligible.Basic

/-!
# The accumulator's security under strong RSA: checked instances

Checks for `CslibFrontier/Crypto/Computational/GUOAccumulator/Security.lean`:

* At the public parameters `(N, g) = (15, 2)`, where the order `4` of `2` is known, the hash
  `H = 3` admits a forgery: `c = 8 = 2 ^ 3`, the membership proof `a = 2` (`2 ^ 3 = 8`) and the
  non-membership proof `(b, γ) = (8, 0)` (`8 ^ 3 ≡ 2 [MOD 15]`). The constant adversary that outputs
  it wins `guoAccumulatorGame` with probability `1` (`guoAccumulatorGame_const`).
* The security theorem applied to that adversary: the strong RSA assumption does not hold for the
  constant setup `(15, 2)`.
* `H x ≠ 1` is needed: at `(N, g) = (4, 2)`, where the strong RSA assumption holds
  (`strongRSA_const_four_two` in `CslibFrontierTests/Crypto/StrongRSA.lean`), the hash `H = 1`
  admits the forgery `c = 1`, `a = 1`, `(b, γ) = (2, 0)`, which wins with probability `1`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GUOAccumulatorSecurity

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### A forgery when the order is known -/

example : GUOForgery.isValid (fun _ => 3) ⟨15, 2⟩ ⟨8, [], 2, 8, 0⟩ = true := by decide

/-- The constant forgery `(c, x, a, (b, γ)) = (8, [], 2, (8, 0))` wins with probability `1` at
`(N, g) = (15, 2)` with `H = 3`. -/
theorem guoAccumulatorGame_const (n : ℕ) :
    guoAccumulatorGame (fun _ => PMF.pure ⟨15, 2⟩) (fun _ => 3)
      (fun _ _ => pure ⟨8, [], 2, 8, 0⟩) n = PMF.pure true := by
  have h : GUOForgery.isValid (fun _ => 3) ⟨15, 2⟩ ⟨8, [], 2, 8, 0⟩ = true := by decide
  simp [guoAccumulatorGame, h]

/-- The security theorem, applied to the constant forger above, shows that the strong RSA
assumption does not hold for the constant setup `(15, 2)`. -/
example : ¬ StrongRSA fun _ => PMF.pure ⟨15, 2⟩ := by
  intro hS
  have hA : GUOForger.IsPPT fun _ _ => pure ⟨8, [], 2, 8, 0⟩ :=
    (ComputableInPolyTime.const _).isPPTOn
  have hneg := hS.negligible_guoAccumulatorGame (H := fun _ => 3) (by simp)
    (ComputableInPolyTime.const _) hA
  simp only [guoAccumulatorGame_const] at hneg
  exact not_negligible_const (by simp [Game.succProbability]) hneg

/-! ### `H x ≠ 1` is needed -/

/-- With `H = 1`, the forgery `(c, x, a, (b, γ)) = (1, [], 1, (2, 0))` wins with probability `1` at
`(N, g) = (4, 2)`, where the strong RSA assumption holds (`strongRSA_const_four_two` in
`CslibFrontierTests/Crypto/StrongRSA.lean`). -/
example (n : ℕ) :
    guoAccumulatorGame (fun _ => PMF.pure ⟨4, 2⟩) (fun _ => 1)
      (fun _ _ => pure ⟨1, [], 1, 2, 0⟩) n = PMF.pure true := by
  have h : GUOForgery.isValid (fun _ => 1) ⟨4, 2⟩ ⟨1, [], 1, 2, 0⟩ = true := by decide
  simp [guoAccumulatorGame, h]

end CslibFrontierTests.Crypto.GUOAccumulatorSecurity
