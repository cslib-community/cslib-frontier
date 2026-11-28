/-
Copyright (c) 2026 Samuel Schlesinger, Shengye Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Shengye Tao
-/

module

import CslibFrontier.Foundations.Data.MvPolynomial.ConsecutiveLayers

/-! Checked instances for integer interpolation on consecutive Hamming layers. -/

namespace CslibFrontierTests.ConsecutiveLayers

open Finset MvPolynomial Cslib

-- Three adjacent layers starting above zero, with mixed-sign prescribed data.
example : ∃ p : MvPolynomial (Fin 4) ℤ, p.totalDegree ≤ 2 ∧ (∀ i, p.degreeOf i ≤ 1) ∧
    eval (fun i => if i ∈ ({0} : Finset (Fin 4)) then (1 : ℤ) else 0) p = -2 ∧
    eval (fun i => if i ∈ ({1, 3} : Finset (Fin 4)) then (1 : ℤ) else 0) p = 7 ∧
    eval (fun i => if i ∈ ({0, 2, 3} : Finset (Fin 4)) then (1 : ℤ) else 0) p = 0 := by
  let v : ℕ → ℤ := fun w => if w = 1 then -2 else if w = 2 then 7 else 0
  obtain ⟨p, hd, hm, h⟩ := exists_multilinear_of_consecutive_weights 4 1 3 v
  exact ⟨p, hd, hm, h {0} (by decide) (by decide),
    h {1, 3} (by decide) (by decide), h {0, 2, 3} (by decide) (by decide)⟩

-- The construction also applies when the cube consists only of its empty support.
example : ∃ p : MvPolynomial (Fin 0) ℤ, p.totalDegree = 0 ∧
    eval (fun _ => (0 : ℤ)) p = -3 := by
  obtain ⟨p, hd, _, h⟩ := exists_multilinear_of_consecutive_weights 0 0 1 (fun _ => -3)
  exact ⟨p, Nat.eq_zero_of_le_zero hd, by simpa using h ∅ (by decide) (by decide)⟩

end CslibFrontierTests.ConsecutiveLayers
