/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.BoundedDegree
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Switched
public import CslibFrontier.Computability.Circuit.Frontier.AverageCase
public import CslibFrontier.Computability.Circuit.Frontier.LowerBound

/-!
# Frontier lower bounds for fan-in two

The frontier lower bound for fan-in two (`Cslib.Circuits.Frontier.eventually_lt_multiarySize`) is
conditional on the layout hypothesis `LayoutBound 3 A`, and gives `s > (1 + 1/A - ε) n` multiary
gates (`arity = 2`; constant and unary gates are free). Three layout bounds remove the hypothesis:

* median-switched Gaussian vertex-score layouts [Gaspers2026] give `A = 2 c₃` with
  `c₃ = (3 / (4π)) arccos (5 / 6)` (`Cslib.Circuits.Frontier.layoutBound_switched`), so
  `1 + 1/A = L₃ = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972`;
* median edge-score layouts give `A = 2p` with `p = (3 / (2π)) arccos ((1 + 2√2)/4)`
  (`Cslib.Circuits.Frontier.layoutBound_gaussian`), so `1 + 1/A = L ≈ 4.562498`;
* vertex-score layouts give `A = 1/3` (`Cslib.Circuits.Frontier.layoutBound_one_third`), so
  `1 + 1/A = 4`.

Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite alphabet `U` with at least two
symbols, with `log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all
large `n`, every circuit of fan-in at most two deciding `S_n`, over any basis and interpretation
on `U`, has more than

* `(L₃ - ε) n` multiary gates (`arity = 2`; constant and unary gates are free), with
  `L₃ = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972`
  (`Cslib.Circuits.Frontier.eventually_switched_sub_mul_lt_multiarySize`,
  `Cslib.Circuits.Frontier.multiaryLowerBound_switched`,
  `Cslib.Circuits.Frontier.multiaryLowerBound_457597_div_100000`, and their `innerSize` companions
  `eventually_switched_sub_mul_lt_innerSize`, `eventually_457597_div_100000_sub_mul_lt_innerSize`,
  `eventually_183_div_40_sub_mul_lt_innerSize`);
* `(L - ε) n` inner gates, with `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5624977`
  (`Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize`,
  `eventually_114_div_25_sub_mul_lt_innerSize`);
* `(4 - ε) n` inner gates (`Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_innerSize`).

The Gaussian layout bound and the `(L - ε) n` and `(114/25 - ε) n` lower bounds derived from it
are original to this library.

Constant and unary gates (`arity ≤ 1`) are not counted in `multiarySize`; the `innerSize`
companions follow via `c.multiarySize ≤ c.innerSize`. The hypotheses are those of
`Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_multiarySize`: the bounds apply to every family
of dense rectangle-free sets, and to a particular family once it is shown to be one.

The same coefficients hold for the bundled worst-case claims (`MultiaryLowerBound`,
`CircuitLowerBound`) and average-case claims (`MultiaryAverageCaseBound`, `AverageCaseBound`):
circuits of fan-in two with at most `(L₃ - ε) n` multiary gates agree with a set of bias at most
`b_n` on large rectangles on at most a `1/2 + b_n + exp (-γ n)` fraction of the inputs.

## Main results

* `Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize`: `s > (L - ε) n`.
* `Cslib.Circuits.Frontier.eventually_114_div_25_sub_mul_lt_innerSize`: `s > (114/25 - ε) n`.
* `Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_innerSize`: `s > (4 - ε) n`.
* `Cslib.Circuits.Frontier.circuitLowerBound_gaussian`,
  `Cslib.Circuits.Frontier.circuitLowerBound_114_div_25`,
  `Cslib.Circuits.Frontier.circuitLowerBound_four`: the bundled worst-case `innerSize` claims.
* `Cslib.Circuits.Frontier.averageCaseBound_gaussian`,
  `Cslib.Circuits.Frontier.averageCaseBound_114_div_25`,
  `Cslib.Circuits.Frontier.averageCaseBound_four`: the bundled average-case `innerSize` claims.
* `Cslib.Circuits.Frontier.eventually_switched_sub_mul_lt_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_switched_sub_mul_lt_innerSize`,
  `Cslib.Circuits.Frontier.eventually_457597_div_100000_sub_mul_lt_innerSize`,
  `Cslib.Circuits.Frontier.eventually_183_div_40_sub_mul_lt_innerSize`: the median-switched
  Gaussian bounds `s > (L₃ - ε) n` (`L₃ ≈ 4.575972`).
* `Cslib.Circuits.Frontier.multiaryLowerBound_switched`,
  `Cslib.Circuits.Frontier.multiaryLowerBound_457597_div_100000`,
  `Cslib.Circuits.Frontier.circuitLowerBound_switched`,
  `Cslib.Circuits.Frontier.circuitLowerBound_457597_div_100000`,
  `Cslib.Circuits.Frontier.circuitLowerBound_183_div_40`: bundled worst-case median-switched
  claims.
* `Cslib.Circuits.Frontier.multiaryAverageCaseBound_switched`,
  `Cslib.Circuits.Frontier.multiaryAverageCaseBound_457597_div_100000`,
  `Cslib.Circuits.Frontier.averageCaseBound_switched`,
  `Cslib.Circuits.Frontier.averageCaseBound_457597_div_100000`,
  `Cslib.Circuits.Frontier.averageCaseBound_183_div_40`: bundled average-case median-switched
  claims.

## References

* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
-/

public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics Real

universe u v

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **The Gaussian frontier lower bound for fan-in two.** Let `S_n ⊆ U^n` be `K_n`-rectangle-free
sets over a finite alphabet `U` with at least two symbols, with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`, every circuit of fan-in
at most two deciding `S_n`, over any basis and interpretation on `U`, has more than `(L - ε) n`
inner gates, where `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. Original to this library. -/
theorem eventually_gaussian_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n < c.innerSize := by
  have h := eventually_lt_innerSize (mul_pos two_pos Gaussian.gaussianCoefficient_pos)
    layoutBound_gaussian hSK hε
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

/-- **The `(4.56 - ε) n` frontier lower bound for fan-in two.** Under the hypotheses of
`eventually_gaussian_sub_mul_lt_innerSize`, for every `ε > 0` and all large `n`, every circuit of
fan-in at most two deciding `S_n`, over any basis and interpretation on `U`, has more than
`(114/25 - ε) n` inner gates. -/
theorem eventually_114_div_25_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (114 / 25 - ε) * n < c.innerSize := by
  filter_upwards [eventually_gaussian_sub_mul_lt_innerSize.{u, v} hSK hε] with n hn
  intro σ I Acc c hfan hS
  refine lt_of_le_of_lt ?_ (hn σ I Acc c hfan hS)
  exact mul_le_mul_of_nonneg_right (by linarith [Gaussian.circuitCoefficient_ge_456])
    (Nat.cast_nonneg n)

/-- **The `(4 - ε) n` frontier lower bound for fan-in two.** Under the hypotheses of
`eventually_gaussian_sub_mul_lt_innerSize`, for every `ε > 0` and all large `n`, every circuit of
fan-in at most two deciding `S_n`, over any basis and interpretation on `U`, has more than
`(4 - ε) n` inner gates. The layout bound is that of Gaussian vertex scores. -/
theorem eventually_four_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (4 - ε) * n < c.innerSize := by
  have h := eventually_lt_innerSize (by norm_num) layoutBound_one_third hSK hε
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at h

/-! ### The bundled claims -/

/-- **Circuits of fan-in two deciding dense rectangle-free sets need `(L - ε) n` gates**, by
median edge-score layouts, where `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem circuitLowerBound_gaussian :
    CircuitLowerBound.{u, v} (1 + π / (3 * arccos ((1 + 2 * √2) / 4))) := by
  have h := circuitLowerBound_of_layoutBound.{u, v}
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

/-- **Circuits of fan-in two deciding dense rectangle-free sets need `(4.56 - ε) n` gates**: the
Gaussian coefficient is at least `114/25`. -/
theorem circuitLowerBound_114_div_25 : CircuitLowerBound.{u, v} (114 / 25) :=
  circuitLowerBound_gaussian.mono Gaussian.circuitCoefficient_ge_456

/-- **Circuits of fan-in two deciding dense rectangle-free sets need `(4 - ε) n` gates**, by
Gaussian vertex-score layouts. -/
theorem circuitLowerBound_four : CircuitLowerBound.{u, v} 4 := by
  have h := circuitLowerBound_of_layoutBound.{u, v} (by norm_num) layoutBound_one_third
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at h

/-- **Circuits of fan-in two below `(L - ε) n` gates barely beat guessing** on sets of small bias
on large rectangles, by median edge-score layouts, where
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem averageCaseBound_gaussian :
    AverageCaseBound.{u, v} (1 + π / (3 * arccos ((1 + 2 * √2) / 4))) := by
  have h := averageCaseBound_of_layoutBound.{u, v}
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

/-- **Circuits of fan-in two below `(4.56 - ε) n` gates barely beat guessing** on sets of small
bias on large rectangles: the Gaussian coefficient is at least `114/25`. -/
theorem averageCaseBound_114_div_25 : AverageCaseBound.{u, v} (114 / 25) :=
  averageCaseBound_gaussian.mono Gaussian.circuitCoefficient_ge_456

/-- **Circuits of fan-in two below `(4 - ε) n` gates barely beat guessing** on sets of small bias
on large rectangles, by Gaussian vertex-score layouts. -/
theorem averageCaseBound_four : AverageCaseBound.{u, v} 4 := by
  have h := averageCaseBound_of_layoutBound.{u, v} (by norm_num) layoutBound_one_third
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at h

/-! ### Median-switched Gaussian bounds (`4.57597 n`) -/

/-- **The median-switched Gaussian frontier lower bound for fan-in two, charging only multiary
gates.** Under the hypotheses of `eventually_gaussian_sub_mul_lt_innerSize`, for every `ε > 0`
and all large `n`, every circuit of fan-in at most two deciding `S_n`, over any basis and
interpretation on `U`, has more than `(L₃ - ε) n` multiary gates (`arity = 2`; constant and unary
gates are free), where `L₃ = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972`. Original to this library
(instantiating the frontier framework with `layoutBound_switched`). -/
theorem eventually_switched_sub_mul_lt_multiarySize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1 + 2 * π / (3 * arccos (5 / 6)) - ε) * n < c.multiarySize := by
  have h := eventually_lt_multiarySize (mul_pos two_pos Switched.switchedCoefficient_pos)
    layoutBound_switched hSK hε
  rwa [Switched.one_add_inv_two_mul_switchedCoefficient] at h

/-- **The median-switched Gaussian frontier lower bound for fan-in two.** Under the hypotheses of
`eventually_gaussian_sub_mul_lt_innerSize`, for every `ε > 0` and all large `n`, every circuit of
fan-in at most two deciding `S_n`, over any basis and interpretation on `U`, has more than
`(L₃ - ε) n` inner gates, where `L₃ = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972`. Original to this
library (instantiating the frontier framework with `layoutBound_switched`). -/
theorem eventually_switched_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1 + 2 * π / (3 * arccos (5 / 6)) - ε) * n < c.innerSize := by
  filter_upwards [eventually_switched_sub_mul_lt_multiarySize.{u, v} hSK hε] with n hn
  intro σ I Acc c hfan hS
  exact (hn σ I Acc c hfan hS).trans_le (Nat.cast_le.mpr c.multiarySize_le_innerSize)

/-- **The `(4.57597 - ε) n` frontier lower bound for fan-in two.** Under the hypotheses of
`eventually_switched_sub_mul_lt_innerSize`, every circuit of fan-in at most two deciding `S_n`
has more than `(457597/100000 - ε) n` inner gates. -/
theorem eventually_457597_div_100000_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (457597 / 100000 - ε) * n < c.innerSize := by
  filter_upwards [eventually_switched_sub_mul_lt_innerSize.{u, v} hSK hε] with n hn
  intro σ I Acc c hfan hS
  refine lt_of_le_of_lt ?_ (hn σ I Acc c hfan hS)
  exact mul_le_mul_of_nonneg_right (by linarith [Switched.circuitCoefficient_ge_457597])
    (Nat.cast_nonneg n)

/-- **The `(4.575 - ε) n` frontier lower bound for fan-in two.** Under the hypotheses of
`eventually_switched_sub_mul_lt_innerSize`, every circuit of fan-in at most two deciding `S_n`
has more than `(183/40 - ε) n` inner gates. -/
theorem eventually_183_div_40_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (183 / 40 - ε) * n < c.innerSize := by
  filter_upwards [eventually_switched_sub_mul_lt_innerSize.{u, v} hSK hε] with n hn
  intro σ I Acc c hfan hS
  refine lt_of_le_of_lt ?_ (hn σ I Acc c hfan hS)
  exact mul_le_mul_of_nonneg_right (by linarith [Switched.circuitCoefficient_ge_183_div_40])
    (Nat.cast_nonneg n)

/-- **Circuits of fan-in two deciding dense rectangle-free sets need `(L₃ - ε) n` multiary gates**,
by median-switched Gaussian vertex-score layouts (`layoutBound_switched`), where
`L₃ = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972`. Original to this library. -/
theorem multiaryLowerBound_switched :
    MultiaryLowerBound.{u, v} (1 + 2 * π / (3 * arccos (5 / 6))) := by
  have h := multiaryLowerBound_of_layoutBound.{u, v}
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched
  rwa [Switched.one_add_inv_two_mul_switchedCoefficient] at h

/-- **Circuits of fan-in two deciding dense rectangle-free sets need `(4.57597 - ε) n` multiary
gates**: the switched coefficient satisfies `L₃ ≥ 457597/100000`. -/
theorem multiaryLowerBound_457597_div_100000 : MultiaryLowerBound.{u, v} (457597 / 100000) :=
  multiaryLowerBound_switched.mono Switched.circuitCoefficient_ge_457597

/-- **Circuits of fan-in two deciding dense rectangle-free sets need `(L₃ - ε) n` gates**, by
median-switched Gaussian vertex-score layouts (`layoutBound_switched`), where
`L₃ = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972`. Original to this library. -/
theorem circuitLowerBound_switched :
    CircuitLowerBound.{u, v} (1 + 2 * π / (3 * arccos (5 / 6))) :=
  multiaryLowerBound_switched.circuitLowerBound

/-- **Circuits of fan-in two deciding dense rectangle-free sets need `(4.57597 - ε) n` gates**:
the switched coefficient satisfies `L₃ ≥ 457597/100000`. -/
theorem circuitLowerBound_457597_div_100000 : CircuitLowerBound.{u, v} (457597 / 100000) :=
  multiaryLowerBound_457597_div_100000.circuitLowerBound

/-- **Circuits of fan-in two deciding dense rectangle-free sets need `(4.575 - ε) n` gates**:
the switched coefficient satisfies `L₃ ≥ 183/40`. -/
theorem circuitLowerBound_183_div_40 : CircuitLowerBound.{u, v} (183 / 40) :=
  circuitLowerBound_switched.mono Switched.circuitCoefficient_ge_183_div_40

/-- **Circuits of fan-in two below `(L₃ - ε) n` multiary gates barely beat guessing** on sets of
small bias on large rectangles, by `layoutBound_switched`. Original to this library. -/
theorem multiaryAverageCaseBound_switched :
    MultiaryAverageCaseBound.{u, v} (1 + 2 * π / (3 * arccos (5 / 6))) := by
  have h := multiaryAverageCaseBound_of_layoutBound.{u, v}
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched
  rwa [Switched.one_add_inv_two_mul_switchedCoefficient] at h

/-- **Circuits of fan-in two below `(4.57597 - ε) n` multiary gates barely beat guessing**. -/
theorem multiaryAverageCaseBound_457597_div_100000 :
    MultiaryAverageCaseBound.{u, v} (457597 / 100000) :=
  multiaryAverageCaseBound_switched.mono Switched.circuitCoefficient_ge_457597

/-- **Circuits of fan-in two below `(L₃ - ε) n` gates barely beat guessing** on sets of small
bias on large rectangles, by `layoutBound_switched`. Original to this library. -/
theorem averageCaseBound_switched :
    AverageCaseBound.{u, v} (1 + 2 * π / (3 * arccos (5 / 6))) :=
  multiaryAverageCaseBound_switched.averageCaseBound

/-- **Circuits of fan-in two below `(4.57597 - ε) n` gates barely beat guessing**. -/
theorem averageCaseBound_457597_div_100000 : AverageCaseBound.{u, v} (457597 / 100000) :=
  multiaryAverageCaseBound_457597_div_100000.averageCaseBound

/-- **Circuits of fan-in two below `(4.575 - ε) n` gates barely beat guessing**. -/
theorem averageCaseBound_183_div_40 : AverageCaseBound.{u, v} (183 / 40) :=
  averageCaseBound_switched.mono Switched.circuitCoefficient_ge_183_div_40

end Cslib.Circuits.Frontier
