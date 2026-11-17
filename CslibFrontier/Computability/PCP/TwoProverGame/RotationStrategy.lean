/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-!
# The rotation strategy for the CHSH game

Arora and Barak's entangled strategy for CHSH [Arora and Barak, Section 20.3.2, printed
pp. 414–415 / PDF pp. 430–431][AroraBarak07]: Alice and Bob share the EPR pair
`(|00⟩ + |11⟩)/√2` (`Cslib.Quantum.bell`). On question `1`, Alice rotates her qubit by `π/8` and
Bob rotates his by `-π/8`; on question `0` neither acts. Each then measures in the computational
basis and answers the outcome (`Cslib.PCP.TwoProverGame.chshRotationStrategy`). Rotating by `θ`
(`chshRotation`) maps `|0⟩` to `cos θ |0⟩ + sin θ |1⟩` and `|1⟩` to `-sin θ |0⟩ + cos θ |1⟩`, as in
the source's computation.
Measuring after a rotation is the measurement `Cslib.Quantum.POVM.comap` of the rotation, whose
outcome probabilities are those of the rotated state (`Cslib.Quantum.POVM.prob_comap`).

On the EPR pair the correlation of the rotations by `α` and `β` is `cos (2 (α - β))`
(`Cslib.PCP.TwoProverGame.correlation_chshRotationStrategy`). The strategy therefore wins with
probability `(5 + √2) / 8 = 1/4 · 1 + 1/2 · cos²(π/8) + 1/4 · 1/2`
(`Cslib.PCP.TwoProverGame.quantumWinProb_chsh_chshRotationStrategy`): the answers agree always
on questions `(0, 0)`, with probability `cos²(π/8)` on `(0, 1)` and `(1, 0)`, and with
probability `1/2` on `(1, 1)`. This is at least `0.8`
(`Cslib.PCP.TwoProverGame.four_div_five_le_quantumWinProb_chsh_chshRotationStrategy`, Arora and
Barak's Theorem 20.16), but below the optimum `cos²(π/8)` attained by
`Cslib.PCP.TwoProverGame.chshEPR`.

## Main definitions

* `Cslib.PCP.TwoProverGame.chshRotation`: the real rotation of a qubit.
* `Cslib.PCP.TwoProverGame.chshRotationStrategy`: the rotation strategy.

## Main results

* `Cslib.PCP.TwoProverGame.quantumWinProb_chsh_chshRotationStrategy`: it wins CHSH with
  probability `(5 + √2) / 8`.
* `Cslib.PCP.TwoProverGame.four_div_five_le_quantumWinProb_chsh_chshRotationStrategy`:
  **Arora–Barak Theorem 20.16**, it wins with probability at least `0.8`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft dated 2007-01-08,
  Section 20.3.2][AroraBarak07]
-/

@[expose] public section

namespace Cslib.PCP.TwoProverGame

open Cslib.Quantum Matrix Real

/-- The **rotation of a qubit by the angle `θ`**: `|0⟩ ↦ cos θ |0⟩ + sin θ |1⟩` and
`|1⟩ ↦ -sin θ |0⟩ + cos θ |1⟩`, with `false` for `|0⟩`. -/
noncomputable def chshRotation (θ : ℝ) : Matrix Bool Bool ℂ :=
  fun b c => if b = c then (cos θ : ℂ) else if b then (sin θ : ℂ) else -(sin θ : ℂ)

theorem chshRotation_mem_unitaryGroup (θ : ℝ) : chshRotation θ ∈ unitaryGroup Bool ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
  have h : (sin θ : ℂ) ^ 2 + (cos θ : ℂ) ^ 2 = 1 := by exact_mod_cast sin_sq_add_cos_sq θ
  ext b c
  cases b <;> cases c <;>
    simp only [chshRotation, Matrix.mul_apply, Fintype.sum_bool, conjTranspose_apply,
      Complex.star_def, map_neg, Complex.conj_ofReal, one_apply_eq, one_apply_ne, ne_eq,
      Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, ↓reduceIte] <;>
    first | linear_combination h | ring

/-- Measuring in the computational basis after rotating by `θ`. -/
noncomputable def chshRotatedMeasurement (θ : ℝ) : POVM Bool Bool :=
  POVM.basis.comap (chshRotation θ) (chshRotation_mem_unitaryGroup θ)

/-- The observable of the rotated measurement: `cos (2θ) Z - sin (2θ) X`. -/
theorem observable_chshRotatedMeasurement (θ : ℝ) :
    (chshRotatedMeasurement θ).observable = Matrix.of fun b c =>
      if b = c then (if b then -(cos (2 * θ) : ℂ) else (cos (2 * θ) : ℂ))
      else -(sin (2 * θ) : ℂ) := by
  have hc : (cos (2 * θ) : ℂ) = (cos θ : ℂ) ^ 2 - (sin θ : ℂ) ^ 2 := by
    exact_mod_cast cos_two_mul' θ
  have hs : (sin (2 * θ) : ℂ) = 2 * (sin θ : ℂ) * (cos θ : ℂ) := by
    exact_mod_cast sin_two_mul θ
  ext b c
  cases b <;> cases c <;>
    simp only [chshRotatedMeasurement, POVM.comap, POVM.observable, POVM.basis_effect,
      chshRotation, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_bool, conjTranspose_apply,
      Complex.star_def, map_neg, Complex.conj_ofReal, Matrix.single_apply, true_and,
      false_and, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Matrix.of_apply, hc, hs] <;>
    ring

/-- The **rotation strategy** of [Arora and Barak, Section 20.3.2][AroraBarak07]: the EPR pair,
with Alice rotating by `π/8` on question `1`, Bob rotating by `-π/8` on question `1`, and both
measuring in the computational basis. -/
noncomputable def chshRotationStrategy : QuantumStrategy Bool Bool Bool Bool Bool Bool where
  state := bell
  norm_state := norm_bell
  alice x := chshRotatedMeasurement (bif x then π / 8 else 0)
  bob y := chshRotatedMeasurement (bif y then -(π / 8) else 0)

/-- On the EPR pair, measuring after rotations by `α` and `β` has correlation `cos (2 (α - β))`. -/
theorem correlation_chshRotationStrategy (x y : Bool) :
    chshRotationStrategy.correlation x y =
      cos (2 * ((bif x then π / 8 else 0) - (bif y then -(π / 8) else 0))) := by
  have hS : chshRotationStrategy.state = maxEntangled Bool := bell_eq_maxEntangled
  have hA : chshRotationStrategy.alice x = chshRotatedMeasurement (bif x then π / 8 else 0) := rfl
  have hB : chshRotationStrategy.bob y = chshRotatedMeasurement (bif y then -(π / 8) else 0) := rfl
  rw [QuantumStrategy.correlation, hS, hA, hB, observable_chshRotatedMeasurement,
    observable_chshRotatedMeasurement, star_maxEntangled_dotProduct_kronecker_mulVec, mul_sub,
    cos_sub]
  simp only [Fintype.sum_bool, Fintype.card_bool, Matrix.of_apply, ite_true, Bool.true_eq_false,
    Bool.false_eq_true, ite_false]
  generalize cos (2 * (bif x then π / 8 else 0)) = a
  generalize sin (2 * (bif x then π / 8 else 0)) = b
  generalize cos (2 * (bif y then -(π / 8) else 0)) = c
  generalize sin (2 * (bif y then -(π / 8) else 0)) = d
  rw [show (-(a : ℂ) * -(c : ℂ) + -(b : ℂ) * -(d : ℂ) + (-(b : ℂ) * -(d : ℂ) + (a : ℂ) * c)) /
      ((2 : ℕ) : ℂ) = ((a * c + b * d : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- The rotation strategy wins CHSH with probability `(5 + √2) / 8`. -/
theorem quantumWinProb_chsh_chshRotationStrategy :
    chsh.quantumWinProb chshRotationStrategy = (5 + √2) / 8 := by
  rw [quantumWinProb_chsh]
  simp only [correlation_chshRotationStrategy, Bool.cond_true, Bool.cond_false]
  have h1 : 2 * (π / 8 - 0) = π / 4 := by ring
  have h2 : 2 * (0 - -(π / 8)) = π / 4 := by ring
  have h3 : 2 * (π / 8 - -(π / 8)) = π / 2 := by ring
  rw [sub_zero, mul_zero, h1, h2, h3, cos_zero, cos_pi_div_four, cos_pi_div_two]
  ring

/-- **Arora–Barak Theorem 20.16**: the rotation strategy wins CHSH with probability at least `0.8`
[Arora and Barak, Theorem 20.16, printed p. 414 / PDF p. 430][AroraBarak07]. The exact value is
`(5 + √2) / 8` (`quantumWinProb_chsh_chshRotationStrategy`). -/
theorem four_div_five_le_quantumWinProb_chsh_chshRotationStrategy :
    4 / 5 ≤ chsh.quantumWinProb chshRotationStrategy := by
  rw [quantumWinProb_chsh_chshRotationStrategy]
  nlinarith [sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2), sqrt_nonneg 2]

end Cslib.PCP.TwoProverGame
