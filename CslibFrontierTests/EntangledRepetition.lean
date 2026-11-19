/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.EntangledRepetition
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-! # Entangled repetition of CHSH -/

set_option linter.privateModule false

open Cslib.PCP.TwoProverGame
open scoped Real

example {n : ℕ} (hn : 0 < n) : (chsh.pow n).quantumValue ≤ Real.cos (π / 8) ^ 2 := by
  rw [← quantumValue_chsh]
  exact chsh.quantumValue_pow_le_of_pos hn
