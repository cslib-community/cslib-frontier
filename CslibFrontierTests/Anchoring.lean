/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.Anchoring
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-! # Anchoring the CHSH game -/

set_option linter.privateModule false

open Cslib.PCP.TwoProverGame
open scoped unitInterval Real ENNReal

private noncomputable def half : I := ⟨1 / 2, by constructor <;> norm_num⟩

example : (chsh.anchored half).questions (none, none) = 1 / 4 := by
  rw [anchored_questions_apply]
  norm_num [half, ENNReal.ofReal_div_of_pos]
  rw [← ENNReal.inv_pow]
  norm_num

example : (chsh.anchored half).value = 15 / 16 := by
  rw [value_anchored, value_chsh]
  norm_num [half]

example : (chsh.anchored half).quantumValue = 1 - (1 - Real.cos (π / 8) ^ 2) / 4 := by
  rw [quantumValue_anchored, quantumValue_chsh]
  norm_num [half]
  ring
