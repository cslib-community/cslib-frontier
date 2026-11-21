/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.InterpolationSum
import CslibFrontier.Computability.PolyTime.InterpolationGrid
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm

open Cslib.Circuits.Frontier.FastContraction InterpolationGrid Turing Turing.MultiTapeTM

private def sample : Fin 7 → Input
  | 0 => ⟨3, 1, 2, 0, 0, 0⟩
  | 1 => ⟨3, 1, 2, 0, 1, 2 ^ 60⟩
  | 2 => ⟨3, 1, 2, 1, 0, 0⟩
  | 3 => ⟨3, 1, 1, 0, 0, 0⟩
  | 4 => ⟨3, 1, 7, 1, 0, 0⟩
  | 5 => ⟨3, 1, 2, 3, 2 ^ 60, 0⟩
  | 6 => ⟨0, 0, 0, 0, 0, 1⟩

private def expected : Fin 7 → Bool × Bool
  | 0 => (true, false)
  | 1 => (true, true)
  | 2 | 3 => (true, true)
  | 4 => (true, false)
  | 5 | 6 => (false, false)

-- One machine handles both signed numerator and denominator bits, including their different
-- center/padding behavior, and runs in the input's bit length even at very large query indices.
example : ∃ (c d t : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM t Bool Q), ∀ i : Fin 7,
    let x := sample i
    let time := c * ((encInput x).length + 1) ^ d
    tm.ComputesTidilyInTimeAndSpace (encInput x) (encPair encBool encBool (expected i))
      time time := by
  obtain ⟨c, d, t, Q, hQ, tm, h⟩ := Internal.NormalForm.polyTime computableInPolyTime_run
  refine ⟨c, d, t, Q, hQ, tm, fun i => ?_⟩
  have hv : run (sample i) = expected i := by fin_cases i <;> rfl
  simpa only [hv] using h (sample i)

-- The empty interpolation always has zero coefficient, at any represented bit.
example (m p k : ℕ) (y : List (List ℕ)) (r : Fin (modulus m).length) (b : Fin p) :
    ((representative m p ((Cslib.GaloisRingArith.pval p (modulus m)
      (Cslib.GaloisRingArith.interp p (modulus m) (points m 0) y)).coeff k)).coeff
      r.val).val.testBit b.val = false := by
  rw [← bit_interp, bit_sum]
  simp
