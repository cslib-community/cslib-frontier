/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.LDLCertificate
public import CslibFrontier.Foundations.Analysis.ODE.Hurwitz

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
the two witnesses is wrong, for example after rounding, so rejection says nothing about `A`.
Instability needs a certificate of its own, below.

## Instability certificates

Lyapunov's instability theorem, in shifted form: if `P` is symmetric but not necessarily definite,
`ε` is rational of either sign, `x₀ᵀ P x₀ < 0` and

  `(A - ε • 1)ᵀ * P + P * (A - ε • 1) ⪯ 0`,

then along `x t = exp (t • A) *ᵥ x₀` the energy `V = xᵀ P x` satisfies `V' ≤ 2 ε V`, so
`V t ≤ exp (2 ε t) V 0 < 0`. Since `-V ≤ ‖P‖ ‖x‖²`, the trajectory grows:
`‖x t‖ ≥ √(-(x₀ᵀ P x₀) / ‖P‖) exp (ε t)` for `t ≥ 0`, with `‖P‖` the `ℓ²` operator norm. The
certificate `Cslib.LinearAlgebra.InstabilityCert` lists `ε`, `x₀` and an `LDLᵀ` witness for
`-((A - ε • 1)ᵀ * P + P * (A - ε • 1)) ⪰ 0`, recomputed from `A`, `ε` and `P` in integers by the
residual check `LDLCert.factorsLyapunovResidual` that `LyapunovCert.check` also uses. A
semidefinite residual suffices for the bound, so the witness may be singular; the strict
inequality `≺ 0` of the textbook statement is the special case of a positive diagonal. The sparse
form `Cslib.LinearAlgebra.SparseInstabilityCert` checks the same conditions through the envelope
checker of `SparseLyapunovCert`, including rounded witnesses with a diagonally dominant remainder;
its clients are in `CslibFrontier.Algorithms.LinearAlgebra.SparseLyapunovCertificate`.

An accepted certificate gives:

* for every `ε`, the growth bound above: some trajectory decays no faster than `exp (ε t)`. For
  `ε < 0` this is a certified lower bound on settling times
  (`InstabilityCert.lt_dotProduct_self_of_check`), complementing the upper bounds of the decay
  certificates of `Cslib.LinearAlgebra.DecayCert`;
* with `ε ≥ 0`, that `ẋ = A x` is not asymptotically (hence not exponentially) stable;
* with `ε > 0`, that it is not Lyapunov stable and that `‖exp (t • A) *ᵥ x₀‖ → ∞`;
* for every `ε`, an eigenvalue `μ` of `A` over `ℂ` with `ε ≤ re μ`, i.e. a spectral abscissa
  `α(A) = max re μ ≥ ε` (`Matrix.exists_mem_spectrum_le_re_of_posSemidef`).

A stability certificate for the rows `shiftRows n σ A` of `A - σ • 1` gives `α(A) < σ`
(`LyapunovCert.re_lt_of_check_shiftRows`), so the two certificates together bracket the spectral
abscissa, `ε ≤ α(A) < σ`.

**Converse (not formalized here).** For `ε > 0` the certificate exists iff `α(A) > 0`. If `A` has
an eigenvalue with `re λ > 0`, choose a rational `ε` with `0 < ε < re λ` that is not the real part
of any eigenvalue. Then `A - ε • 1` has no eigenvalue on the imaginary axis and at least one in the
right half-plane, and the Lyapunov inertia theorem (Ostrowski–Schneider, Taussky) gives a
symmetric `P` with `(A - ε • 1)ᵀ P + P (A - ε • 1) ≺ 0` whose number of negative eigenvalues is
the number of eigenvalues of `A - ε • 1` with positive real part, so some `x₀ᵀ P x₀ < 0`. Both
conditions are strict, so a rational perturbation of `P` and a rational `x₀` still satisfy them,
and the rational residual, being positive definite, has exact `LDLᵀ` factors. Only the soundness
direction is proved here.

**The boundary `α(A) = 0` is not decided.** The stability certificate needs `α(A) < 0` and the
instability certificate with `ε > 0` needs `α(A) ≥ ε > 0`, since both rest on open conditions.
Neither applies to the ideal LC matrix `!![0, 1; -1, 0]`, which is Lyapunov stable but not
asymptotically stable, nor to the double integrator `!![0, 1; 0, 0]`, which is unstable with linear
growth. With `ε = 0` the instability certificate still refutes asymptotic stability, as for the LC
matrix with `P = -1`, but it never proves an unbounded trajectory.

## Main results

* `Cslib.LinearAlgebra.LyapunovCert.isExponentiallyStable_of_check`: acceptance gives exponential
  stability of `ẋ = A x` on `EuclideanSpace ℝ (Fin n)`.
* `Cslib.LinearAlgebra.InstabilityCert.exists_mem_spectrum_le_re_of_check`: an accepted
  instability certificate gives an eigenvalue `μ` of `A` with `ε ≤ re μ`.
* `Cslib.LinearAlgebra.InstabilityCert.sqrt_mul_exp_le_norm_of_check`: the explicit growth bound
  `‖exp (t • A) *ᵥ x₀‖ ≥ C exp (ε t)`, for a rate of any sign.
* `Cslib.LinearAlgebra.InstabilityCert.lt_dotProduct_self_of_check`: a lower bound on settling.
* `Cslib.LinearAlgebra.LyapunovCert.re_lt_of_check_shiftRows`: a stability certificate for
  `A - σ • 1` puts the spectrum of `A` in `re μ < σ`.
* `Cslib.LinearAlgebra.InstabilityCert.not_isLyapunovStable_of_check`,
  `Cslib.LinearAlgebra.InstabilityCert.tendsto_norm_of_check`: with `ε > 0`, instability and an
  unbounded trajectory.
* `Cslib.LinearAlgebra.InstabilityCert.not_isAsymptoticallyStable_of_check`,
  `Cslib.LinearAlgebra.InstabilityCert.not_isExponentiallyStable_of_check`: with `ε ≥ 0`, no
  asymptotic stability.

## References

* A. M. Lyapunov, *The general problem of the stability of motion*, 1892, for the instability
  theorem.
* A. Ostrowski and H. Schneider, *Some theorems on the inertia of general matrices*, J. Math.
  Anal. Appl. 4 (1962), and O. Taussky, *A generalization of a theorem of Lyapunov*, J. SIAM 9
  (1961), for the inertia theorem cited in the converse.
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

/-- **A shifted stability certificate bounds the spectrum.** If the kernel accepts `c` for the
rows `shiftRows n σ A` of `A - σ • 1` and `P`, then every complex eigenvalue of `A`, read over
`ℝ`, has real part less than `σ`. With an instability certificate of rate `ε` for `A`, this
brackets the spectral abscissa: `ε ≤ α(A) < σ`. -/
theorem re_lt_of_check_shiftRows {σ : ℚ} (h : c.check n (shiftRows n σ A) P = true) :
    ∀ μ ∈ spectrum ℂ (((ofLists n n A).map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ)),
      μ.re < σ := by
  have hS := isHurwitz_of_isExponentiallyStable (isExponentiallyStable_of_check h)
  rw [ofLists_shiftRows] at hS
  refine IsHurwitz.re_lt_of_sub (σ := σ) ?_
  convert hS using 1
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [one_apply_ne hij]

end Cslib.LinearAlgebra.LyapunovCert

namespace Cslib.LinearAlgebra.InstabilityCert

variable {c : InstabilityCert} {n : ℕ} {A P : List (List ℚ)}

/-- **An eigenvalue to the right of the certified rate.** If the kernel accepts `c` for the
rational matrices with rows `A` and `P`, then `A`, read over `ℝ`, has a complex eigenvalue `μ`
with `c.rate ≤ re μ`. -/
theorem exists_mem_spectrum_le_re_of_check (h : c.check n A P = true) :
    ∃ μ ∈ spectrum ℂ (((ofLists n n A).map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ)),
      (c.rate : ℝ) ≤ μ.re :=
  have ⟨hx, hQ⟩ := sound_of_check h
  exists_mem_spectrum_le_re_of_posSemidef hQ hx

/-- **Exponential growth.** If the kernel accepts `c` for `A` and `P`, then the solution
`exp (t • A) *ᵥ x₀` of `ẋ = A x` from the certified `x₀` satisfies
`‖x t‖ ≥ √(-(x₀ᵀ P x₀) / ‖P‖) exp (ε t)` in the Euclidean norm for `t ≥ 0`, with `ε = c.rate`
and the `ℓ²` operator norm `‖P‖`. The constant is positive. -/
theorem sqrt_mul_exp_le_norm_of_check (h : c.check n A P = true) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (-((fun i => ((ofList n c.x₀ i : ℚ) : ℝ)) ⬝ᵥ (ofLists n n P).map ((↑) : ℚ → ℝ) *ᵥ
        (fun i => ((ofList n c.x₀ i : ℚ) : ℝ))) /
        ‖toEuclideanCLM (𝕜 := ℝ) ((ofLists n n P).map ((↑) : ℚ → ℝ))‖) *
        Real.exp (c.rate * t) ≤
      ‖WithLp.toLp 2 (NormedSpace.exp (t • (ofLists n n A).map ((↑) : ℚ → ℝ)) *ᵥ
        (fun i => ((ofList n c.x₀ i : ℚ) : ℝ)))‖ :=
  have ⟨_, hQ⟩ := sound_of_check h
  sqrt_mul_exp_le_norm_exp_smul_mulVec hQ _ ht

/-- **The state has not settled.** If the kernel accepts `c` for `A` and `P`, then the solution
`x t = exp (t • A) *ᵥ x₀` from the certified `x₀` satisfies `r < x t ⬝ᵥ x t` at every `t ≥ 0`
with `‖P‖ r < exp (2 ε t) * -(x₀ᵀ P x₀)`, for `ε = c.rate` of any sign. For `ε < 0` this is a
certified lower bound on the time to settle into `x ⬝ᵥ x ≤ r`, complementing the upper bound
`Cslib.LinearAlgebra.DecayInequalities.dotProduct_self_le_of_stateSettles`. -/
theorem lt_dotProduct_self_of_check (h : c.check n A P = true) {r t : ℝ} (ht : 0 ≤ t)
    (hr : ‖toEuclideanCLM (𝕜 := ℝ) ((ofLists n n P).map ((↑) : ℚ → ℝ))‖ * r <
      Real.exp (2 * c.rate * t) * -((fun i => ((ofList n c.x₀ i : ℚ) : ℝ)) ⬝ᵥ
        (ofLists n n P).map ((↑) : ℚ → ℝ) *ᵥ (fun i => ((ofList n c.x₀ i : ℚ) : ℝ)))) :
    r < NormedSpace.exp (t • (ofLists n n A).map ((↑) : ℚ → ℝ)) *ᵥ
        (fun i => ((ofList n c.x₀ i : ℚ) : ℝ)) ⬝ᵥ
      NormedSpace.exp (t • (ofLists n n A).map ((↑) : ℚ → ℝ)) *ᵥ
        (fun i => ((ofList n c.x₀ i : ℚ) : ℝ)) := by
  have ⟨_, hQ⟩ := sound_of_check h
  exact lt_of_mul_lt_mul_left (hr.trans_le (exp_mul_neg_le_norm_mul_dotProduct_self hQ _ ht))
    (norm_nonneg _)

/-- **No asymptotic stability.** If the kernel accepts `c` for `A` and `P` with a nonnegative
rate, then `ẋ = A x` is not asymptotically stable. -/
theorem not_isAsymptoticallyStable_of_check (h : c.check n A P = true) (hε : 0 ≤ c.rate) :
    ¬(toEuclideanCLM (𝕜 := ℝ) ((ofLists n n A).map ((↑) : ℚ → ℝ))).IsAsymptoticallyStable :=
  have ⟨hx, hQ⟩ := sound_of_check h
  not_isAsymptoticallyStable_toEuclideanCLM_of_posSemidef (Rat.cast_nonneg.2 hε) hQ hx

/-- **No exponential stability.** If the kernel accepts `c` for `A` and `P` with a nonnegative
rate, then `ẋ = A x` is not exponentially stable. -/
theorem not_isExponentiallyStable_of_check (h : c.check n A P = true) (hε : 0 ≤ c.rate) :
    ¬(toEuclideanCLM (𝕜 := ℝ) ((ofLists n n A).map ((↑) : ℚ → ℝ))).IsExponentiallyStable :=
  fun hA => not_isAsymptoticallyStable_of_check h hε hA.isAsymptoticallyStable

/-- **Instability.** If the kernel accepts `c` for `A` and `P` with a positive rate, then
`ẋ = A x` is not Lyapunov stable. -/
theorem not_isLyapunovStable_of_check (h : c.check n A P = true) (hε : 0 < c.rate) :
    ¬(toEuclideanCLM (𝕜 := ℝ) ((ofLists n n A).map ((↑) : ℚ → ℝ))).IsLyapunovStable :=
  have ⟨hx, hQ⟩ := sound_of_check h
  not_isLyapunovStable_toEuclideanCLM_of_posSemidef (Rat.cast_pos.2 hε) hQ hx

/-- **An unbounded trajectory.** If the kernel accepts `c` for `A` and `P` with a positive rate,
then the solution `exp (t • A) *ᵥ x₀` of `ẋ = A x` from the certified `x₀` tends to infinity in
the Euclidean norm. -/
theorem tendsto_norm_of_check (h : c.check n A P = true) (hε : 0 < c.rate) :
    Filter.Tendsto (fun t : ℝ => ‖WithLp.toLp 2 (NormedSpace.exp
      (t • (ofLists n n A).map ((↑) : ℚ → ℝ)) *ᵥ (fun i => ((ofList n c.x₀ i : ℚ) : ℝ)))‖)
      Filter.atTop Filter.atTop :=
  have ⟨hx, hQ⟩ := sound_of_check h
  tendsto_norm_exp_smul_mulVec_atTop (Rat.cast_pos.2 hε) hQ hx

end Cslib.LinearAlgebra.InstabilityCert
