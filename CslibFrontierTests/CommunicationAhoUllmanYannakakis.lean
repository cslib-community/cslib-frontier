/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Communication.AhoUllmanYannakakis

/-! Checked clients of the Aho–Ullman–Yannakakis bound [AroraBarak07, Chapter 12, Exercise 7]:
the one-piece tiling of a constant function gives a protocol with no communication, and the
bound applies to equality on `Fin n`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.CommunicationAhoUllmanYannakakis

open Cslib Cslib.Communication

/-- A one-piece tiling needs no communication: `2 ⌈log₂ 1⌉ ⌈log₂ 2⌉ = 0`. -/
example : Protocol.ecomplexityFun (fun (_ : Bool) (_ : ℕ) => true) ≤ 0 := by
  have h := (RectanglePartition.constant Bool ℕ true).ecomplexityFun_run_le
  rw [RectanglePartition.run_constant] at h
  simpa [RectanglePartition.constant] using h

/-- Equality on `Fin n`: `C(EQ) ≤ 8 ⌊log₂ χ(EQ)⌋²`. -/
example (n : ℕ) :
    Protocol.ecomplexityFun (fun x y : Fin n => decide (x = y)) ≤
      (8 * Nat.log 2 (tilingNumber fun x y : Fin n => decide (x = y)).toNat ^ 2 : ℕ) :=
  ecomplexityFun_le_eight_mul_log_tilingNumber_sq _

end CslibFrontierTests.CommunicationAhoUllmanYannakakis
