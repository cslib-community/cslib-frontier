/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.MIP.AxisSoundness
import CslibFrontier.Foundations.Data.MvPolynomial.DisjointVars

/-! The axis at zero and one shares its address, while the two point values are distinct.
An honest proof for the identity polynomial can store an independent word at a reserved key. -/

namespace CslibFrontierTests.MIP.AxisTest

open Cslib Cslib.Probability Cslib.Complexity Cslib.Complexity.MIP MvPolynomial

example : axisTableKey true 0 [1] = axisTableKey true 0 [2] ∧
    pointTableKey [1] ≠ pointTableKey [2] := by decide

example : ∃ π : List Bool → Bool, (∀ x : Fin 1 → ZMod 3, proofPoint π 3 x = x 0) ∧
    ProofWord.value π [true, true] 2 = 3 ∧
    ∀ precision, (Prover.ofProof π).run (axisRound 1 3 precision) () = PMF.pure (true, ()) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let A : MvPolynomial (Fin 1) (ZMod 3) := X 0
  have hA : A ∈ restrictDegree (Fin 1) (ZMod 3) 1 := X_mem_restrictDegree le_rfl _
  obtain ⟨lines, hon⟩ := exists_axisTable_of_mem_restrictDegree hA
  let other := fun _ : List Bool => 3
  let table := extendAxisTable (fun x => eval x A) lines other
  obtain ⟨π, hπ⟩ := ProofWord.exists_value_eq_mod table
  obtain ⟨hf, hr⟩ := hon other π fun key _ => hπ key _
  refine ⟨π, fun x => ?_, ?_, hr⟩
  · simp [hf, A]
  · rw [hπ, show table [true, true] = 3 from extendAxisTable_reserved _ _ _ []]
    decide

-- In dimension one over 10009 residues, even one mistaken point fits the local-correction
-- radius. The arithmetic bound covers two sumcheck coordinates of degree three.
example :
    let k := (4 * axisGapDenominator 1).size
    (2 : ℝ) * (3 + 1) / 10009 + 3 * ((1 + 1) * 1 / 10009 ^ 1 + 1 / 2 ^ k) +
      2 / 2 ^ k ≤ 1 / 2 :=
  arithmeticError_le_half (n := 1) (p := 10009) (R := 2) (d := 3) (H := 1)
    (by decide) (by norm_num)

end CslibFrontierTests.MIP.AxisTest
