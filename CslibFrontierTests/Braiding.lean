/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.Algebra.Braiding
import CslibFrontier.Foundations.Quantum.PauliTwirl

/-! # Braiding relations from anticommutation, consistency and linearity

Checked clients: the transfer through consistency, in any state of any star-ordered algebra, and
the evaluation of the masked anticommutation defect. A concrete instance: the commuting phase flips
`Z^a`, `Z^b`, as their own consistent copies, satisfy `Z^b Z^a = Z^a Z^b` with every input `0`, so
the averaged transfer certifies commutation.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Braiding

open Matrix Cslib Cslib.Quantum Finset
open scoped BigOperators MatrixOrder ComplexOrder

/-- **Pointwise transfer**, in any state of any star-ordered algebra. -/
example {A : Type} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
    [StarModule ℂ A] [SelfAdjointDecompose A] (φ : AlgState A) {X Z X' Z' : A}
    (hX : X ∈ unitary A) (hZ : Z ∈ unitary A) (hX' : X' ∈ unitary A) (hZ' : Z' ∈ unitary A)
    (hXZ' : Commute X Z') (hZX' : Commute Z X') :
    φ.norm (Z * X + X * Z) ≤
      2 * φ.norm (X - X') + 2 * φ.norm (Z - Z') + φ.norm (X' * Z' + Z' * X') := by
  simpa using norm_mul_sub_smul_mul_le_of_consistent φ hX hZ hX' hZ' hXZ' hZX'
    (s := -1) (by simp)

/-- **Concrete instance**: commuting phase flips, as their own copies, have no defect. -/
example {n : Type} [Fintype n] [DecidableEq n] (φ : AlgState (Matrix (n → Bool) (n → Bool) ℂ)) :
    𝔼 p : (n → Bool) × (n → Bool), φ.norm (pauliZPow p.2 * pauliZPow p.1 -
      (1 : ℂ) • (pauliZPow p.1 * pauliZPow p.2)) ^ 2 ≤ 0 := by
  have hZ : ∀ a, pauliZPow a ∈ unitary (Matrix (n → Bool) (n → Bool) ℂ) :=
    pauliZPow_mem_unitaryGroup
  have hc : ∀ a b, Commute (pauliZPow (ι := n) a) (pauliZPow b) := fun a b => by
    rw [Commute, SemiconjBy, pauliZPow_mul, pauliZPow_mul, add_comm]
  have h := expect_norm_mul_sub_smul_mul_sq_le_of_consistent (ι := (n → Bool) × (n → Bool)) φ
    (fun p => pauliZPow p.1) (fun p => pauliZPow p.2) (fun p => pauliZPow p.1)
    (fun p => pauliZPow p.2) (fun _ => 1) (fun _ => hZ _) (fun _ => hZ _) (fun _ => hZ _)
    (fun _ => hZ _) (fun _ => hc _ _) (fun _ => hc _ _) (fun _ => by simp)
  refine h.trans ?_
  simp [(hc _ _).eq, AlgState.norm_zero]

/-- The masked anticommutation defect vanishes off the pairs with `a · c = 1`. -/
example {ι A : Type} [Fintype ι] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    [Algebra ℂ A] [StarModule ℂ A] [SelfAdjointDecompose A] (φ : AlgState A)
    (X Z : (ι → Bool) → A) :
    anticommDefectSq φ X Z 0 0 = 0 :=
  anticommDefectSq_of_dotProduct_eq_false φ X Z (by rw [zero_dotProduct]; rfl)

end CslibFrontierTests.Braiding
