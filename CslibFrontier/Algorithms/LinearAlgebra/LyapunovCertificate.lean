/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.LDLCertificate
public import CslibFrontier.Foundations.Analysis.ODE.LinearLyapunov

/-!
# Kernel-checked Lyapunov certificates prove exponential stability

This module composes the exact rational checker `Cslib.LinearAlgebra.LyapunovCert.check` with the
quadratic Lyapunov criterion `Matrix.isExponentiallyStable_toEuclideanCLM_of_posDef`. For rational
`n × n` matrices `A` and `P`, given by their rows, an accepted certificate proves that the linear
system `ẋ = A x`, with `A` read over `ℝ`, is exponentially stable: there are constants `M` and
`α > 0` such that every trajectory on `[0, ∞)` satisfies `‖x t‖ ≤ M exp (-α t) ‖x 0‖` in the
Euclidean norm. Acceptance is a Boolean computation that the kernel evaluates (`decide +kernel`),
so no compiled code is trusted.

To use it, write `A` and `P` as lists of rational rows, let an untrusted tool (for instance SciPy's
`solve_continuous_lyapunov` followed by rational reconstruction and SymPy's `LDLdecomposition`)
find `LDLᵀ` witnesses for `P` and for the residual `-(Aᵀ P + P A)`, which the checker recomputes
from `A` and `P`, and prove `c.check n A P = true` by `decide +kernel`. Then
`Cslib.LinearAlgebra.LyapunovCert.isExponentiallyStable_of_check` gives stability of the operator
`Matrix.toEuclideanCLM` of the real matrix. Through `Matrix.isTrajectoryOn_toEuclideanCLM_iff` this
covers every coordinate solution `x : ℝ → Fin n → ℝ` of `x' = A *ᵥ x`, measured in the Euclidean
norm of `WithLp.toLp 2 (x t)` (not the supremum norm of `Fin n → ℝ`).

## Rejection is not instability

The checker is sound, not complete. It rejects a stable system whenever the supplied `P` or one of
the two witnesses is wrong, for example after rounding, so rejection says nothing about `A`. Only a
separate theorem, such as an unbounded trajectory, proves instability.

## Main results

* `Cslib.LinearAlgebra.LyapunovCert.isExponentiallyStable_of_check`: acceptance gives exponential
  stability of `ẋ = A x` on `EuclideanSpace ℝ (Fin n)`.
-/

public section

open Matrix Mathlib.Tactic.Matrix

namespace Cslib.LinearAlgebra.LyapunovCert

variable {c : LyapunovCert} {n : ℕ} {A P : List (List ℚ)}

/-- **Certificate acceptance proves exponential stability.** If the kernel accepts `c` for the
rational matrices with rows `A` and `P`, then `ẋ = A x`, with `A` read over `ℝ`, is exponentially
stable in the Euclidean norm: every trajectory on `[0, ∞)` satisfies `‖x t‖ ≤ M exp (-α t) ‖x 0‖`
for constants `M` and `α > 0` that do not depend on the trajectory. -/
theorem isExponentiallyStable_of_check (h : c.check n A P = true) :
    (toEuclideanCLM (𝕜 := ℝ) ((ofLists n n A).map ((↑) : ℚ → ℝ))).IsExponentiallyStable :=
  have ⟨hP, hQ⟩ := posDef_of_check h
  isExponentiallyStable_toEuclideanCLM_of_posDef hP hQ

end Cslib.LinearAlgebra.LyapunovCert
