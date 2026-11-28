/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Quantum.Bell
import CslibFrontier.Foundations.Quantum.DensityMatrix.QuantumPinsker

/-! Quantum Pinsker gives a nonzero lower bound for a pure qubit against the mixed state. -/

namespace CslibFrontierTests.QuantumPinsker

open Cslib.Quantum Matrix

example :
    (↑(1 / 2 : ℝ) : WithTop ℝ) ≤
      relativeEntropy (pureState (ket false)) (partialTraceRight (pureState bell)) := by
  let ρ := pureState (ket false)
  let σ := partialTraceRight (pureState bell)
  let U : Matrix Bool Bool ℂ := diagonal fun b => if b then -1 else 1
  have hU : U ∈ unitaryGroup Bool ℂ := by
    dsimp only [U]
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    cases i <;> simp
  have hσ : σ = (2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
    change partialTraceRight (pureState bell) = _
    rw [bell, partialTraceRight_pureState_maxEntangled, Fintype.card_bool, Nat.cast_ofNat]
  have hreal : (Uᴴ * (ρ - σ)).trace.re = 1 := by
    rw [hσ]
    simp only [U, diagonal_conjTranspose, trace, diag_apply, diagonal_mul, Matrix.sub_apply,
      Matrix.smul_apply, Fintype.sum_bool, Matrix.one_apply_eq]
    norm_num [ρ, pureState_apply, ket_apply, Complex.star_def, Complex.inv_re, Complex.inv_im,
      Complex.mul_re]
  have hnorm := re_trace_conjTranspose_mul_le_traceNorm (ρ - σ) U hU
  rw [hreal] at hnorm
  refine (WithTop.coe_le_coe.mpr ?_).trans
    (traceNorm_sub_sq_div_two_le_relativeEntropy (isDensityMatrix_pureState (norm_ket false))
      (isDensityMatrix_pureState norm_bell).partialTraceRight)
  nlinarith [sq_nonneg ((ρ - σ).traceNorm - 1)]

end CslibFrontierTests.QuantumPinsker
