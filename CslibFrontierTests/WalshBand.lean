/-
Copyright (c) 2026 Samuel Schlesinger, Shengye Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Shengye Tao
-/

module

import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.WalshBand
import Mathlib.Algebra.Field.ZMod

/-! Checked instances for Walsh sign agreement and rank on a band of overlaps. -/

namespace CslibFrontierTests.WalshBand

open Finset Cslib

-- On overlap sizes one and two, a rank-five matrix on the sixteen supports
-- gives opposite signs in characteristic three.
example : ∃ A : Matrix (Finset (Fin 4)) (Finset (Fin 4)) (ZMod 3),
    A.rank ≤ 5 ∧ A {0, 1} {1, 2} = -1 ∧ A {0, 1} {0, 1, 2} = 1 := by
  obtain ⟨A, hr, h⟩ := exists_low_rank_eq_walsh_on_band (ZMod 3) 4 1 2
  refine ⟨A, hr.trans (by decide), ?_, ?_⟩
  · exact (h {0, 1} {1, 2} (by decide) (by decide)).trans (by decide)
  · exact (h {0, 1} {0, 1, 2} (by decide) (by decide)).trans (by decide)

-- A singleton odd layer in characteristic two has sign +1.
example : ∃ A : Matrix (Finset (Fin 3)) (Finset (Fin 3)) (ZMod 2),
    A.rank ≤ 1 ∧ A {0} {0} = 1 := by
  obtain ⟨A, hr, h⟩ := exists_low_rank_eq_walsh_on_band (ZMod 2) 3 1 1
  exact ⟨A, hr.trans (by decide), (h {0} {0} (by decide) (by decide)).trans (by decide)⟩

-- No columns are necessary when the overlap band is empty.
example : ∃ A : Matrix (Finset (Fin 0)) (Finset (Fin 0)) ℚ, A.rank = 0 := by
  obtain ⟨A, hr, _⟩ := exists_low_rank_eq_walsh_on_band ℚ 0 0 0
  exact ⟨A, Nat.eq_zero_of_le_zero (by simpa using hr)⟩

end CslibFrontierTests.WalshBand
