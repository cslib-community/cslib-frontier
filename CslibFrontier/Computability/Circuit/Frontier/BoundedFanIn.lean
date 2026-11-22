/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.BoundedDegree
public import CslibFrontier.Computability.Circuit.Frontier.LowerBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Frontier lower bounds for bounded fan-in

The frontier lower bound for fan-in at most `r`
(`Cslib.Circuits.Frontier.eventually_lt_mul_multiarySize`) is conditional on the layout hypothesis
for maximum degree `r + 1`. Gaussian vertex-score layouts provide it with the coefficient
`A_d = 3d/(2d - 3) · arccos (2√(d - 1)/d) / π` for every `d ≥ 3`
(`Cslib.Circuits.Frontier.layoutBound_degree`). So circuits of fan-in at most `r` deciding dense
rectangle-free sets have `s` multiary gates (`arity ≥ 2`) with `(r - 1) s > (1 + 1/A_{r+1} - ε) n`
(`Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_multiarySize`; constant and unary
gates are free).

In degree four the correlation `2√3/4` is `cos (π/6)`, so `A_4 = 2/5`
(`Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_four`), and circuits of fan-in at most three
have `2 s > (7/2 - ε) n`
(`Cslib.Circuits.Frontier.eventually_seven_div_two_lt_two_mul_multiarySize`).

## Main results

* `Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_innerSize`: the bound for fan-in at
  most `r`.
* `Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_four`: `A_4 = 2/5`.
* `Cslib.Circuits.Frontier.eventually_seven_div_two_lt_two_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_seven_div_two_lt_two_mul_innerSize`: the bound for fan-in at
  most three.
-/

public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics Real

/-- In degree four the Gaussian vertex-score coefficient is `2/5`: the adjacent correlation is
`2√3/4 = cos (π/6)`. -/
theorem Gaussian.degreeCoefficient_four : Gaussian.degreeCoefficient 4 = 2 / 5 := by
  have h : Gaussian.vertexCorrelation 4 = cos (π / 6) := by
    rw [Gaussian.vertexCorrelation, cos_pi_div_six]
    push_cast
    norm_num
    ring
  rw [Gaussian.degreeCoefficient, Gaussian.vertexCoefficient, h,
    arccos_cos (by positivity) (by linarith [pi_pos])]
  field_simp
  norm_num

universe u v

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **The frontier lower bound for fan-in at most `r`, charging only multiary gates**, by Gaussian
vertex-score layouts. Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite alphabet `U` with
at least two symbols, with `log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every
`ε > 0` and all large `n`, every circuit of fan-in at most `r ≥ 2` deciding `S_n`, over any basis
and interpretation on `U`, has `s` multiary gates (`arity ≥ 2`; constant and unary gates are free)
with `(r - 1) s > (1 + 1/A_{r+1} - ε) n`, where `A_d` is `Gaussian.degreeCoefficient d`. -/
theorem eventually_degreeCoefficient_lt_mul_multiarySize {r : ℕ} (hr : 2 ≤ r)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (1 + 1 / Gaussian.degreeCoefficient (r + 1) - ε) * n < (r - 1) * c.multiarySize :=
  eventually_lt_mul_multiarySize hr (Gaussian.degreeCoefficient_pos (by omega))
    (layoutBound_degree (by omega)) hSK hε

/-- **The frontier lower bound for fan-in at most `r`**, by Gaussian vertex-score layouts. Let
`S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite alphabet `U` with at least two symbols, with
`log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`,
every circuit of fan-in at most `r ≥ 2` deciding `S_n`, over any basis and interpretation on `U`,
has `s` inner gates with `(r - 1) s > (1 + 1/A_{r+1} - ε) n`, where `A_d` is
`Gaussian.degreeCoefficient d`. -/
theorem eventually_degreeCoefficient_lt_mul_innerSize {r : ℕ} (hr : 2 ≤ r)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (1 + 1 / Gaussian.degreeCoefficient (r + 1) - ε) * n < (r - 1) * c.innerSize :=
  eventually_lt_mul_innerSize hr (Gaussian.degreeCoefficient_pos (by omega))
    (layoutBound_degree (by omega)) hSK hε

/-- **The frontier lower bound for fan-in at most three, charging only multiary gates.** Under the
hypotheses of `eventually_degreeCoefficient_lt_mul_multiarySize`, every circuit of fan-in at most
three deciding `S_n` has `s` multiary gates with `2 s > (7/2 - ε) n`. -/
theorem eventually_seven_div_two_lt_two_mul_multiarySize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc (S n) →
        (7 / 2 - ε) * n < 2 * c.multiarySize := by
  have h := eventually_degreeCoefficient_lt_mul_multiarySize.{u, v} (r := 3) (by norm_num) hSK hε
  norm_num only [Gaussian.degreeCoefficient_four] at h
  exact h

/-- **The frontier lower bound for fan-in at most three.** Under the hypotheses of
`eventually_degreeCoefficient_lt_mul_innerSize`, every circuit of fan-in at most three deciding
`S_n` has `s` inner gates with `2 s > (7/2 - ε) n`. -/
theorem eventually_seven_div_two_lt_two_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc (S n) →
        (7 / 2 - ε) * n < 2 * c.innerSize := by
  filter_upwards [eventually_seven_div_two_lt_two_mul_multiarySize.{u, v} hSK hε] with n hn
  intro σ I Acc c hfan hS
  exact (hn σ I Acc c hfan hS).trans_le
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr c.multiarySize_le_innerSize) zero_le_two)

end Cslib.Circuits.Frontier
