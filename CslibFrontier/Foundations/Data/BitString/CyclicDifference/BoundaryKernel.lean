/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.CyclicDifference.Boundary
import CslibFrontier.Foundations.Logic.Function.UpdateKernel

/-!
# Exact kernel of cyclic adjacent identification

The prescribed `zeroPort` quotient identifies exactly the selected cyclic pair. Its public
retained-port identities supply the characterization, including the two-port and wrap cases,
without unfolding the coordinate arithmetic or using graph infrastructure.
-/

public section

namespace Cslib.BitString

/-- The prescribed adjacent quotient merges exactly the selected cyclic pair. -/
theorem zeroPort_kernel {n : ℕ} (i a b : Fin (n + 2)) :
    zeroPort i a = zeroPort i b ↔
      Function.update id (finRotate (n + 2) i) i a =
        Function.update id (finRotate (n + 2) i) i b := by
  rw [Function.update_id_apply_eq_iff]
  constructor
  · intro h
    have hh := congrArg (retainPort i) h
    have ha := retainPort_zeroPort i a
    have hb := retainPort_zeroPort i b
    grind
  · intro h
    rcases h with hab | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact congrArg (zeroPort i) hab
    · rw [ha, hb]
      exact (zeroPort_next i).symm
    · rw [ha, hb]
      exact zeroPort_next i

end Cslib.BitString
