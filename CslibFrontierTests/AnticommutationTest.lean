/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.AnticommutationTest
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled

/-! # The anticommutation test

Two concrete instances. The optimal EPR strategy for CHSH wins with probability exactly
`cos²(π/8)`, so the squared anticommutation defect of its first player's observables is `0` in its
state. And the CHSH operator transfer, applied with the EPR strategy on every odd pair and the
consistent transposes on the second tensor factor, certifies that those second-factor observables
anticommute in the EPR state.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.AnticommutationTest

open Cslib Cslib.PCP Cslib.Quantum Finset Matrix
open scoped BigOperators Real MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

/-- The first player's observables of the EPR strategy act on the first factor. -/
theorem observable_alice_chshEPR (x : Bool) :
    (TwoProverGame.chshEPR.toCommuting.alice x).observable =
      kroneckerOne (κ := Bool) (TwoProverGame.chshAliceObservable x) := by
  rw [← POVM.observable_ofObservable (TwoProverGame.chshAliceObservable x)
    (TwoProverGame.isHermitian_chshAliceObservable x)
    (TwoProverGame.chshAliceObservable_mul_self x), POVM.observable, map_sub]
  rfl

/-- **Concrete masked client of the CHSH operator transfer.** With the optimal EPR strategy for
every odd pair and, as consistency observables, the transposes `1 ⊗ Zᵀ`, `1 ⊗ Xᵀ` on the *second*
tensor factor, which agree exactly with the first player's `Z ⊗ 1`, `X ⊗ 1` on the EPR pair, every
input of the transfer vanishes, so the masked anticommutation defect of the second-factor
observables is `0` in the EPR state. This checks the role and state conventions of the transfer. -/
example :
    𝔼 a, 𝔼 b, anticommDefectSq TwoProverGame.chshEPR.toCommuting.state
      (fun _ : Unit → Bool =>
        oneKronecker (ι := Bool) (TwoProverGame.chshAliceObservable false)ᵀ)
      (fun _ => oneKronecker (ι := Bool) (TwoProverGame.chshAliceObservable true)ᵀ) a b ≤ 0 := by
  set φ := TwoProverGame.chshEPR.toCommuting.state
  have hφ : φ = AlgState.vector (maxEntangled Bool) norm_maxEntangled := by
    change AlgState.vector bell norm_bell = _
    congr 1
    exact bell_eq_maxEntangled
  have hcons : ∀ x, φ.norm (oneKronecker (ι := Bool) (TwoProverGame.chshAliceObservable x)ᵀ -
      (TwoProverGame.chshEPR.toCommuting.alice x).observable) = 0 := fun x => by
    have h := AlgState.approx_iff.mp (AlgState.kroneckerOne_approx_oneKronecker_transpose
      (TwoProverGame.isHermitian_chshAliceObservable x)
      (TwoProverGame.chshAliceObservable_mul_self x))
    rw [← hφ, AlgState.norm_sub_comm] at h
    rw [observable_alice_chshEPR]
    exact le_antisymm h (φ.norm_nonneg _)
  have hU : ∀ x, oneKronecker (ι := Bool) (TwoProverGame.chshAliceObservable x)ᵀ ∈
      unitary (Matrix (Bool × Bool) (Bool × Bool) ℂ) := fun x => by
    refine Unitary.map_mem _ ?_
    refine IsSelfAdjoint.mem_unitary_of_mul_self ?_ ?_
    · change (TwoProverGame.chshAliceObservable x)ᵀᴴ = (TwoProverGame.chshAliceObservable x)ᵀ
      rw [conjTranspose_transpose_eq_transpose_conjTranspose,
        (TwoProverGame.isHermitian_chshAliceObservable x).eq]
    · rw [← transpose_mul, TwoProverGame.chshAliceObservable_mul_self, transpose_one]
  have h := expect_anticommDefectSq_le_of_chsh (ι := Unit) φ
    (fun _ => oneKronecker (ι := Bool) (TwoProverGame.chshAliceObservable false)ᵀ)
    (fun _ => oneKronecker (ι := Bool) (TwoProverGame.chshAliceObservable true)ᵀ)
    (fun _ _ => TwoProverGame.chshEPR.toCommuting) (fun _ _ _ => rfl)
    (fun _ => (Unitary.star_mul_self_of_mem (hU false)).le)
    (fun _ => (Unitary.star_mul_self_of_mem (hU true)).le)
    (fun _ _ _ => by
      rw [observable_alice_chshEPR]; exact (commute_kroneckerOne_oneKronecker _ _).symm)
    (fun _ _ _ => by
      rw [observable_alice_chshEPR]; exact (commute_kroneckerOne_oneKronecker _ _).symm)
    (fun _ _ => 0) (fun _ _ _ => by
      rw [TwoProverGame.commutingWinProb_toCommuting, TwoProverGame.quantumWinProb_chsh_chshEPR,
        sub_zero])
  refine h.trans (le_of_eq ?_)
  simp only [hcons, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_self,
    Fintype.expect_const, mul_zero, add_zero]

/-- **Concrete instance**: the optimal EPR strategy's first-player observables anticommute
exactly in its state. -/
example : TwoProverGame.chshEPR.toCommuting.state.norm
    ((TwoProverGame.chshEPR.toCommuting.alice false).observable *
        (TwoProverGame.chshEPR.toCommuting.alice true).observable +
      (TwoProverGame.chshEPR.toCommuting.alice true).observable *
        (TwoProverGame.chshEPR.toCommuting.alice false).observable) ^ 2 ≤ 0 := by
  have h := norm_anticomm_sq_le_of_chsh TwoProverGame.chshEPR.toCommuting (ε := 0) (by
    rw [TwoProverGame.commutingWinProb_toCommuting, TwoProverGame.quantumWinProb_chsh_chshEPR,
      sub_zero])
  simpa using h

end CslibFrontierTests.AnticommutationTest
