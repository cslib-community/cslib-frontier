/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests of the sparse LTI impulse-response certificates)

import CslibFrontier.Algorithms.LinearAlgebra.SparseImpulseCertificate

/-! # Tests for sparse decay and energy certificates of LTI impulse responses

A `module` client with ordinary imports. Every acceptance and rejection is closed by
`decide +kernel`, and the soundness theorems are applied through their public statements.

* The scalar client `A = -1`, `B = C = 1` by sparse rows: decay with `P = 1` and
  `α = β = γ = 1`, stability and settling below `1/10` after `T = 5/2`; an overclaimed rate and a
  wrong transpose are rejected.
* One section of an RLC ladder, `A = !![-1, -1; 1, -1]`, `B = e₀`, `C = e₁ᵀ`, with Gramian
  `W = !![1/8, 1/8; 1/8, 3/8]` and energy `1/8`: decay with `P = 1`; the upper bound from `W`,
  with an exact witness and with a witness that has a diagonally dominant remainder; the lower
  bound from `Q = W` and the Lyapunov matrix `P = 1`; the enclosure `[1/8, 1/8]`; overclaimed
  bounds in both directions are rejected.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.SparseImpulseCertificate

open Set Matrix MeasureTheory Cslib.LinearAlgebra

/-! ### The scalar client -/

/-- `ẋ = -x + u`, `y = x`, by sparse rows. -/
def scalar : SparseRatLTI 1 1 1 :=
  ⟨[[(0, -1)]], [[(0, -1)]], [[(0, 1)]], [[(0, 1)]], [[(0, 1)]], [[(0, 1)]]⟩

/-- The envelope witness of the `1 × 1` zero matrix. -/
def zero₁ : EnvLDLCert := ⟨[(0, [1])], [0], []⟩

/-- `P = 1`, `α = β = γ = 1`, `lo = hi = 1`: every residual is `0`. -/
def scalarDecay : SparseDecayCert :=
  ⟨⟨1, 1, 1, 1, 1⟩, [[(0, 1)]], zero₁, zero₁, zero₁, zero₁, zero₁⟩

theorem scalarDecay_ok : scalarDecay.check scalar = true := by decide +kernel

/-- Overclaiming the rate `α = 2` is rejected. -/
example : ({ scalarDecay with α := 2 } : SparseDecayCert).check scalar = false := by
  decide +kernel

/-- A model whose listed transpose is wrong is rejected. -/
example : scalarDecay.check ({ scalar with At := [[(0, 1)]] } : SparseRatLTI 1 1 1) = false := by
  decide +kernel

example : (toEuclideanCLM (𝕜 := ℝ) scalar.toSystem.A).IsExponentiallyStable :=
  (SparseDecayCert.decayInequalities scalarDecay_ok).isExponentiallyStable

/-- Settling: for `‖v‖₂ ≤ 1`, `‖h t v‖₂ ≤ 1/10` for `t ≥ 5/2`. -/
example {v : Fin 1 → ℝ} (hv : v ⬝ᵥ v ≤ 1) {t : ℝ} (ht : 5 / 2 ≤ t) :
    scalar.toSystem.responseKernel t *ᵥ v ⬝ᵥ scalar.toSystem.responseKernel t *ᵥ v ≤ 1/100 := by
  have hs : scalarDecay.impulseSettles 1 (1/100) (5/2) 12 = true := by decide +kernel
  have hD := SparseDecayCert.decayInequalities scalarDecay_ok
  have := hD.responseKernel_mulVec_sq_le_of_impulseSettles hs (v := v) (t := t)
    (by exact_mod_cast hv) (by norm_num; linarith)
  norm_num at this
  exact this

/-! ### One section of an RLC ladder -/

/-- `L = C = 1`, unit series resistance at the source and unit shunt resistance at the load:
`A = !![-1, -1; 1, -1]`, the input drives the inductor current and the output is the capacitor
voltage. -/
def rlc : SparseRatLTI 2 1 1 :=
  ⟨[[(0, -1), (1, -1)], [(0, 1), (1, -1)]], [[(0, -1), (1, 1)], [(0, -1), (1, -1)]],
    [[(0, 1)], []], [[(0, 1)]], [[(1, 1)]], [[], [(0, 1)]]⟩

/-- The envelope witness of the `2 × 2` zero matrix. -/
def zero₂ : EnvLDLCert := ⟨[(0, [1]), (1, [1])], [0, 0], []⟩

/-- `P = 1` at the rate `α = 1`, with `γ = β = 1`: `γ P - Cᵀ C = diag (1, 0)`. -/
theorem rlc_decay : (⟨⟨1, 1, 1, 1, 1⟩, [[(0, 1)], [(1, 1)]], zero₂, zero₂, zero₂,
    ⟨[(0, [1]), (1, [1])], [1, 0], []⟩, zero₁⟩ : SparseDecayCert).check rlc = true := by
  decide +kernel

/-- The Gramian `W = !![1/8, 1/8; 1/8, 3/8]` solves `Aᵀ W + W A + Cᵀ C = 0`. -/
def gramian : List (List (ℕ × ℚ)) := [[(0, 1/8), (1, 1/8)], [(0, 1/8), (1, 3/8)]]

/-- The upper bound `1/8` from `W`, with the exact factorization `W = L diag (1/8, 1/4) Lᵀ`. -/
def rlcUpper : SparseEnergyBoundCert :=
  ⟨gramian, ⟨[(0, [1]), (0, [1, 1])], [1/8, 1/4], []⟩, zero₂, 1/8⟩

theorem rlcUpper_ok : rlcUpper.check rlc = true := by decide +kernel

/-- The same bound with `L = 1`, `d = (0, 1/4)` and the diagonally dominant remainder
`R = !![1/8, 1/8; 1/8, 1/8]`. -/
example : ({ rlcUpper with
    posW := ⟨[(0, [1]), (1, [1])], [0, 1/4], [[(0, 1/8), (1, 1/8)], [(0, 1/8), (1, 1/8)]]⟩ } :
      SparseEnergyBoundCert).check rlc = true := by
  decide +kernel

/-- Claiming the upper bound `1/9` is rejected. -/
example : ({ rlcUpper with bound := 1/9 } : SparseEnergyBoundCert).check rlc = false := by
  decide +kernel

/-- The lower bound `1/8` from `Q = W`, with stability from `P = 1`:
`-(Aᵀ P + P A) = 2 • 1`. -/
def rlcLower : SparseEnergyLowerCert :=
  ⟨[[(0, 1)], [(1, 1)]], ⟨rlc.At, ⟨[(0, [1]), (1, [1])], [1, 1], []⟩,
    ⟨[(0, [1]), (1, [1])], [2, 2], []⟩⟩, gramian, zero₂, 1/8⟩

theorem rlcLower_ok : rlcLower.check rlc = true := by decide +kernel

/-- Claiming the lower bound `1/7` is rejected. -/
example : ({ rlcLower with bound := 1/7 } : SparseEnergyLowerCert).check rlc = false := by
  decide +kernel

/-- **The enclosure.** The impulse-response energy is exactly `1/8`. -/
example : IntegrableOn (fun t => ∑ i, ∑ j, rlc.toSystem.responseKernel t i j ^ 2) (Ioi 0) ∧
    ∫ t in Ioi 0, ∑ i, ∑ j, rlc.toSystem.responseKernel t i j ^ 2 ∈ Icc (1/8 : ℝ) (1/8) := by
  simpa [rlcLower, rlcUpper] using
    SparseEnergyLowerCert.integrableOn_Ioi_and_integral_mem_Icc rlcLower_ok rlcUpper_ok

end CslibFrontierTests.SparseImpulseCertificate
