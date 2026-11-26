/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.SparseLDLCertificate
public import CslibFrontier.Foundations.Analysis.ODE.LinearLyapunov

/-!
# Kernel-checked sparse Lyapunov certificates prove exponential stability

This module composes the sparse checker `Cslib.LinearAlgebra.SparseLyapunovCert.check` with the
quadratic Lyapunov criterion `Matrix.isExponentiallyStable_toEuclideanCLM_of_posDef`, as the
dense client of #8552 does for `Cslib.LinearAlgebra.LyapunovCert`. For rational `n × n`
matrices `A` and `P` given by sparse rows (`Cslib.LinearAlgebra.ofSparse`), an accepted
certificate proves that `ẋ = A x`, with `A` read over `ℝ`, is exponentially stable in the
Euclidean norm. Acceptance is a Boolean computation that the kernel evaluates
(`decide +kernel`).

The checker is sound, not complete: rejection says nothing about `A`.

## Main results

* `Cslib.LinearAlgebra.SparseLyapunovCert.isExponentiallyStable_of_check`: acceptance gives
  exponential stability of `ẋ = A x` on `EuclideanSpace ℝ (Fin n)`.
-/

public section

open Matrix

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
