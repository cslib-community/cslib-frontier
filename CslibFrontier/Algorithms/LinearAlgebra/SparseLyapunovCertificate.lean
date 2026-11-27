/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.SparseLDLCertificate
public import CslibFrontier.Foundations.Analysis.ODE.Hurwitz

/-!
# Kernel-checked sparse Lyapunov certificates prove exponential stability

This module composes the sparse checker `Cslib.LinearAlgebra.SparseLyapunovCert.check` with the
quadratic Lyapunov criterion `Matrix.isExponentiallyStable_toEuclideanCLM_of_posDef`, as the
dense client of #8552 does for `Cslib.LinearAlgebra.LyapunovCert`. For rational `n × n`
matrices `A` and `P` given by sparse rows (`Cslib.LinearAlgebra.ofSparse`), an accepted
certificate proves that `ẋ = A x`, with `A` read over `ℝ`, is exponentially stable in the
Euclidean norm. Acceptance is a Boolean computation that the kernel evaluates
(`decide +kernel`).

The checker is sound, not complete: rejection says nothing about `A`. Instability has its own
certificate, `Cslib.LinearAlgebra.SparseInstabilityCert`, the sparse form of the dense
`Cslib.LinearAlgebra.InstabilityCert`; its clients below have the statements of the dense ones in
`CslibFrontier.Algorithms.LinearAlgebra.LyapunovCertificate`.

## Main results

* `Cslib.LinearAlgebra.SparseLyapunovCert.isExponentiallyStable_of_check`: acceptance gives
  exponential stability of `ẋ = A x` on `EuclideanSpace ℝ (Fin n)`.
* `Cslib.LinearAlgebra.SparseInstabilityCert.exists_mem_spectrum_le_re_of_check`,
  `Cslib.LinearAlgebra.SparseInstabilityCert.sqrt_mul_exp_le_norm_of_check`,
  `Cslib.LinearAlgebra.SparseInstabilityCert.not_isAsymptoticallyStable_of_check`,
  `Cslib.LinearAlgebra.SparseInstabilityCert.not_isLyapunovStable_of_check`,
  `Cslib.LinearAlgebra.SparseInstabilityCert.tendsto_norm_of_check`: an eigenvalue with
  `re μ ≥ ε`, the growth bound, and (in)stability, as for the dense certificate.
-/

public section

open Matrix Mathlib.Tactic.Matrix

namespace Cslib.LinearAlgebra.SparseLyapunovCert

/-- **Certificate acceptance proves exponential stability.** If the kernel accepts `c` for the
sparse rational matrices `A` and `P`, then `ẋ = A x`, with `A` read over `ℝ`, is exponentially
stable in the Euclidean norm. -/
theorem isExponentiallyStable_of_check {c : SparseLyapunovCert} {n : ℕ}
    {A P : List (List (ℕ × ℚ))} (h : c.check n A P = true) :
    (toEuclideanCLM (𝕜 := ℝ) ((ofSparse n n A).map ((↑) : ℚ → ℝ))).IsExponentiallyStable :=
  have ⟨hP, hQ⟩ := posDef_of_check h
  isExponentiallyStable_toEuclideanCLM_of_posDef hP hQ

end Cslib.LinearAlgebra.SparseLyapunovCert

namespace Cslib.LinearAlgebra.SparseInstabilityCert

variable {c : SparseInstabilityCert} {n : ℕ} {A P : List (List (ℕ × ℚ))}

/-- **An eigenvalue to the right of the certified rate.** If the kernel accepts `c` for the
sparse rational matrices `A` and `P`, then `A`, read over `ℝ`, has a complex eigenvalue `μ` with
`c.rate ≤ re μ`. -/
theorem exists_mem_spectrum_le_re_of_check (h : c.check n A P = true) :
    ∃ μ ∈ spectrum ℂ (((ofSparse n n A).map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ)),
      (c.rate : ℝ) ≤ μ.re :=
  have ⟨hx, hQ⟩ := sound_of_check h
  exists_mem_spectrum_le_re_of_posSemidef hQ hx

/-- **Exponential growth.** If the kernel accepts `c` for `A` and `P`, then the solution
`exp (t • A) *ᵥ x₀` from the certified `x₀` satisfies `‖x t‖ ≥ √(-(x₀ᵀ P x₀) / ‖P‖) exp (ε t)`
in the Euclidean norm for `t ≥ 0`, with `ε = c.rate` of any sign. -/
theorem sqrt_mul_exp_le_norm_of_check (h : c.check n A P = true) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (-((fun i => ((ofList n c.x₀ i : ℚ) : ℝ)) ⬝ᵥ (ofSparse n n P).map ((↑) : ℚ → ℝ) *ᵥ
        (fun i => ((ofList n c.x₀ i : ℚ) : ℝ))) /
        ‖toEuclideanCLM (𝕜 := ℝ) ((ofSparse n n P).map ((↑) : ℚ → ℝ))‖) *
        Real.exp (c.rate * t) ≤
      ‖WithLp.toLp 2 (NormedSpace.exp (t • (ofSparse n n A).map ((↑) : ℚ → ℝ)) *ᵥ
        (fun i => ((ofList n c.x₀ i : ℚ) : ℝ)))‖ :=
  have ⟨_, hQ⟩ := sound_of_check h
  sqrt_mul_exp_le_norm_exp_smul_mulVec hQ _ ht

/-- **No asymptotic stability.** If the kernel accepts `c` for `A` and `P` with a nonnegative
rate, then `ẋ = A x` is not asymptotically stable. -/
theorem not_isAsymptoticallyStable_of_check (h : c.check n A P = true) (hε : 0 ≤ c.rate) :
    ¬(toEuclideanCLM (𝕜 := ℝ) ((ofSparse n n A).map ((↑) : ℚ → ℝ))).IsAsymptoticallyStable :=
  have ⟨hx, hQ⟩ := sound_of_check h
  not_isAsymptoticallyStable_toEuclideanCLM_of_posSemidef (Rat.cast_nonneg.2 hε) hQ hx

/-- **Instability.** If the kernel accepts `c` for `A` and `P` with a positive rate, then
`ẋ = A x` is not Lyapunov stable. -/
theorem not_isLyapunovStable_of_check (h : c.check n A P = true) (hε : 0 < c.rate) :
    ¬(toEuclideanCLM (𝕜 := ℝ) ((ofSparse n n A).map ((↑) : ℚ → ℝ))).IsLyapunovStable :=
  have ⟨hx, hQ⟩ := sound_of_check h
  not_isLyapunovStable_toEuclideanCLM_of_posSemidef (Rat.cast_pos.2 hε) hQ hx

/-- **An unbounded trajectory.** If the kernel accepts `c` for `A` and `P` with a positive rate,
then the solution `exp (t • A) *ᵥ x₀` from the certified `x₀` tends to infinity in the Euclidean
norm. -/
theorem tendsto_norm_of_check (h : c.check n A P = true) (hε : 0 < c.rate) :
    Filter.Tendsto (fun t : ℝ => ‖WithLp.toLp 2 (NormedSpace.exp
      (t • (ofSparse n n A).map ((↑) : ℚ → ℝ)) *ᵥ (fun i => ((ofList n c.x₀ i : ℚ) : ℝ)))‖)
      Filter.atTop Filter.atTop :=
  have ⟨hx, hQ⟩ := sound_of_check h
  tendsto_norm_exp_smul_mulVec_atTop (Rat.cast_pos.2 hε) hQ hx

end Cslib.LinearAlgebra.SparseInstabilityCert
