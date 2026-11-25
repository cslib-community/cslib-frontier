/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.BoundedDegree
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.WeightedKernel
public import CslibFrontier.Computability.Circuit.Frontier.Linear.LowerBound
public import CslibFrontier.Computability.Circuit.Frontier.LowerBound
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Frontier lower bounds for bounded fan-in

The frontier lower bound for fan-in at most `r`
(`Cslib.Circuits.Frontier.eventually_lt_mul_multiarySize`,
`Cslib.Circuits.Frontier.eventually_lt_mul_innerSize`) is conditional on the layout hypothesis for
maximum degree `r + 1`. Two families of Gaussian vertex-score layouts instantiate it:

* **Uniform distance kernel** (`Cslib.Circuits.Frontier.layoutBound_degree`): provides
  `A_d = 3d/(2d - 3) · arccos (2√(d - 1)/d) / π` for every `d ≥ 3`, so circuits of fan-in at most
  `r` deciding dense rectangle-free sets have `s` multiary gates (`arity ≥ 2`; constant and unary
  gates are free) satisfying `(r - 1) s > (1 + 1/A_{r+1} - ε) n`
  (`Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_innerSize`). In degree four,
  `A_4 = 2/5` (`Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_four`), giving
  `2 s > (7/2 - ε) n` at `r = 3` (`eventually_seven_div_two_lt_two_mul_multiarySize`,
  `eventually_seven_div_two_lt_two_mul_innerSize`).
* **Degree-weighted max-product walk kernel**
  (`Cslib.Circuits.Frontier.layoutBound_of_weightedKernel`): weights each quotient edge by
  `((D_u - 1)(D_v - 1)) ^ (-1/4)` and sums against the exact multigraph handshake
  `∑_e (1 - 1 / D_u - 1 / D_v) = |E| - |V|`, sharpening the constants for `r = 3, 4, 5`:
  * **`r = 3` (`d = 4`)**: `LayoutBound 4 (1 / 3)` (`layoutBound_four_one_third`) upgrades
    `2 s > (7 / 2 - ε) n` to **`2 s > (4 - ε) n`**, i.e. **`s > (2 - ε) n`**
    (`eventually_four_sub_mul_lt_two_mul_multiarySize`,
    `eventually_four_sub_mul_lt_two_mul_innerSize`,
    `eventually_two_sub_mul_lt_multiarySize_fanInThree`,
    `eventually_two_sub_mul_lt_innerSize_fanInThree`), and likewise for nondeterministic circuits
    with arbitrary witness count and totally regular linear maps;
  * **`r = 4` (`d = 5`)**: `LayoutBound 5 ((5 / 3) arccos (4 / 5) / π)`
    (`layoutBound_five_weighted`) gives `3 s > (1 + 3π / (5 arccos (4 / 5)) - ε) n` (`≥ 3.929 n`,
    up from `≈ 3.278 n`);
  * **`r = 5` (`d = 6`)**: `LayoutBound 6 ((3 / 2) arccos (√5 / 3) / π)`
    (`layoutBound_six_weighted`) gives `4 s > (1 + 2π / (3 arccos (√5 / 3)) - ε) n` (`≥ 3.87 n`,
    up from `≈ 3.153 n`).

## Main results

* `Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_innerSize`: uniform-kernel bound for
  fan-in at most `r`.
* `Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_four`: `A_4 = 2/5`.
* `Cslib.Circuits.Frontier.eventually_seven_div_two_lt_two_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_seven_div_two_lt_two_mul_innerSize`: uniform-kernel
  `2 s > (7/2 - ε) n` bound at `r = 3`.
* `Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_two_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_two_mul_innerSize`,
  `Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_multiarySize_fanInThree`,
  `Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_fanInThree`: upgraded
  `2 s > (4 - ε) n` (`s > (2 - ε) n`) bounds for fan-in three via `layoutBound_four_one_third`.
* `Cslib.Circuits.Frontier.eventually_weightedFive_lt_three_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_weightedFive_lt_three_mul_innerSize`,
  `Cslib.Circuits.Frontier.eventually_3929_div_1000_lt_three_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_3929_div_1000_lt_three_mul_innerSize`: upgraded `r = 4`
  bounds (`3 s > (3.929 - ε) n`).
* `Cslib.Circuits.Frontier.eventually_weightedSix_lt_four_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_weightedSix_lt_four_mul_innerSize`,
  `Cslib.Circuits.Frontier.eventually_387_div_100_lt_four_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_387_div_100_lt_four_mul_innerSize`: upgraded `r = 5` bounds
  (`4 s > (3.87 - ε) n`).
* `Frontier.eventually_four_sub_mul_lt_two_mul_innerSize_of_nondeterministicDecides`,
  `Frontier.eventually_four_sub_mul_lt_two_mul_innerSize_of_isTotallyRegular`:
  nondeterministic and linear-map counterparts (along with `*_of_nondeterministicDecides` and
  `*_of_isTotallyRegular` for `r = 4, 5`).
-/

public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics Matrix Real

/-- In degree four the uniform Gaussian vertex-score coefficient is `2/5`: the adjacent correlation
is `2√3/4 = cos (π/6)`. -/
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

section WorstCaseAndNondet

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

omit [Finite U] [Nontrivial U] in
private theorem eventually_lt_mul_innerSize_of_multiarySize {r : ℕ} {c_lo k : ℝ} (hk : 0 ≤ k)
    (h : ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        c_lo * n < k * c.multiarySize) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        c_lo * n < k * c.innerSize := by
  filter_upwards [h] with n hn σ I Acc c hfan hS
  exact (hn σ I Acc c hfan hS).trans_le
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr c.multiarySize_le_innerSize) hk)

omit [Finite U] [Nontrivial U] in
private theorem eventually_lt_mul_multiarySize_of_le {r : ℕ} {c₁ c₂ ε k : ℝ} (hc : c₂ ≤ c₁)
    (h : ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (c₁ - ε) * n < k * c.multiarySize) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (c₂ - ε) * n < k * c.multiarySize := by
  filter_upwards [h] with n hn σ I Acc c hfan hdec
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hc ε) (Nat.cast_nonneg n)).trans_lt
    (hn σ I Acc c hfan hdec)

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
        (7 / 2 - ε) * n < 2 * c.innerSize :=
  eventually_lt_mul_innerSize_of_multiarySize zero_le_two
    (eventually_seven_div_two_lt_two_mul_multiarySize.{u, v} hSK hε)

/-! ### Upgraded degree-weighted walk-kernel bounds (`r = 3, 4, 5`) -/

/-- **Upgraded fan-in-three frontier lower bound (`2 s > (4 - ε) n`), charging only multiary
gates.** By the degree-weighted max-product walk kernel
(`layoutBound_four_one_third : LayoutBound 4 (1 / 3)`), every circuit of fan-in at most three
deciding `S_n` has `s` multiary gates (`arity ≥ 2`) satisfying `2 s > (4 - ε) n`. -/
theorem eventually_four_sub_mul_lt_two_mul_multiarySize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc (S n) →
        (4 - ε) * n < 2 * c.multiarySize := by
  have h := eventually_lt_mul_multiarySize.{u, v} (r := 3) (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 3) layoutBound_four_one_third hSK hε
  norm_num only at h
  exact h

/-- **Upgraded fan-in-three frontier lower bound (`2 s > (4 - ε) n`).** Every circuit of fan-in at
most three deciding `S_n` has `s` inner gates satisfying `2 s > (4 - ε) n`. -/
theorem eventually_four_sub_mul_lt_two_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc (S n) →
        (4 - ε) * n < 2 * c.innerSize :=
  eventually_lt_mul_innerSize_of_multiarySize zero_le_two
    (eventually_four_sub_mul_lt_two_mul_multiarySize.{u, v} hSK hε)

/-- **Upgraded fan-in-three multiary gate-count bound (`s > (2 - ε) n`).** Dividing
`eventually_four_sub_mul_lt_two_mul_multiarySize` by `2` gives `(2 - ε) n < c.multiarySize`. -/
theorem eventually_two_sub_mul_lt_multiarySize_fanInThree
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc (S n) →
        (2 - ε) * n < c.multiarySize := by
  filter_upwards [eventually_four_sub_mul_lt_two_mul_multiarySize.{u, v} hSK
    (show 0 < 2 * ε by positivity)] with n hn σ I Acc c hfan hdec
  have h := hn σ I Acc c hfan hdec
  linarith

/-- **Upgraded fan-in-three gate-count bound (`s > (2 - ε) n`).** Dividing
`eventually_four_sub_mul_lt_two_mul_innerSize` by `2` gives `(2 - ε) n < c.innerSize` for fan-in
at most three. -/
theorem eventually_two_sub_mul_lt_innerSize_fanInThree
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc (S n) →
        (2 - ε) * n < c.innerSize := by
  filter_upwards [eventually_two_sub_mul_lt_multiarySize_fanInThree.{u, v} hSK hε] with
    n hn σ I Acc c hfan hdec
  exact (hn σ I Acc c hfan hdec).trans_le (Nat.cast_le.mpr c.multiarySize_le_innerSize)

/-- **Nondeterministic fan-in-three frontier lower bound (`2 s > (4 - ε) n`, uniform in witness
count `k`).** -/
theorem eventually_four_sub_mul_lt_two_mul_innerSize_of_nondeterministicDecides
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 3 → c.NondeterministicDecides I Acc (S n) →
        (4 - ε) * n < 2 * c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_nondeterministicDecides.{u, v} (r := 3) (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 3) layoutBound_four_one_third hSK hε
  norm_num only at h
  exact h

/-- **Upgraded fan-in-four frontier lower bound (`3 s > (1 + 3π / (5 arccos (4 / 5)) - ε) n`),
charging only multiary gates.** -/
theorem eventually_weightedFive_lt_three_mul_multiarySize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 4 → c.Decides I Acc (S n) →
        (1 + 3 * π / (5 * arccos (4 / 5)) - ε) * n < 3 * c.multiarySize := by
  have h := eventually_lt_mul_multiarySize.{u, v} (r := 4) (by norm_num)
    WeightedKernel.fiveCoefficient_pos layoutBound_five_weighted hSK hε
  rwa [WeightedKernel.one_add_inv_fiveCoefficient, show ((4 : ℕ) : ℝ) - 1 = 3 by norm_num] at h

/-- **Upgraded fan-in-four frontier lower bound (`3 s > (1 + 3π / (5 arccos (4 / 5)) - ε) n`).** -/
theorem eventually_weightedFive_lt_three_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 4 → c.Decides I Acc (S n) →
        (1 + 3 * π / (5 * arccos (4 / 5)) - ε) * n < 3 * c.innerSize :=
  eventually_lt_mul_innerSize_of_multiarySize (by positivity)
    (eventually_weightedFive_lt_three_mul_multiarySize.{u, v} hSK hε)

/-- **Rational fan-in-four frontier lower bound (`3 s > (3.929 - ε) n`), charging only multiary
gates.** -/
theorem eventually_3929_div_1000_lt_three_mul_multiarySize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 4 → c.Decides I Acc (S n) →
        (3929 / 1000 - ε) * n < 3 * c.multiarySize :=
  eventually_lt_mul_multiarySize_of_le WeightedKernel.fiveCircuitCoefficient_ge_3929
    (eventually_weightedFive_lt_three_mul_multiarySize.{u, v} hSK hε)

/-- **Rational fan-in-four frontier lower bound (`3 s > (3.929 - ε) n`).** -/
theorem eventually_3929_div_1000_lt_three_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 4 → c.Decides I Acc (S n) →
        (3929 / 1000 - ε) * n < 3 * c.innerSize :=
  eventually_lt_mul_innerSize_of_multiarySize (by positivity)
    (eventually_3929_div_1000_lt_three_mul_multiarySize.{u, v} hSK hε)

/-- **Nondeterministic fan-in-four frontier lower bound.** -/
theorem eventually_weightedFive_lt_three_mul_innerSize_of_nondeterministicDecides
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 4 → c.NondeterministicDecides I Acc (S n) →
        (1 + 3 * π / (5 * arccos (4 / 5)) - ε) * n < 3 * c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_nondeterministicDecides.{u, v} (r := 4) (by norm_num)
    WeightedKernel.fiveCoefficient_pos layoutBound_five_weighted hSK hε
  rwa [WeightedKernel.one_add_inv_fiveCoefficient, show ((4 : ℕ) : ℝ) - 1 = 3 by norm_num] at h

/-- **Upgraded fan-in-five frontier lower bound (`4 s > (1 + 2π / (3 arccos (√5 / 3)) - ε) n`),
charging only multiary gates.** -/
theorem eventually_weightedSix_lt_four_mul_multiarySize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 5 → c.Decides I Acc (S n) →
        (1 + 2 * π / (3 * arccos (√5 / 3)) - ε) * n < 4 * c.multiarySize := by
  have h := eventually_lt_mul_multiarySize.{u, v} (r := 5) (by norm_num)
    WeightedKernel.sixCoefficient_pos layoutBound_six_weighted hSK hε
  rwa [WeightedKernel.one_add_inv_sixCoefficient, show ((5 : ℕ) : ℝ) - 1 = 4 by norm_num] at h

/-- **Upgraded fan-in-five frontier lower bound (`4 s > (1 + 2π / (3 arccos (√5 / 3)) - ε) n`).** -/
theorem eventually_weightedSix_lt_four_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 5 → c.Decides I Acc (S n) →
        (1 + 2 * π / (3 * arccos (√5 / 3)) - ε) * n < 4 * c.innerSize :=
  eventually_lt_mul_innerSize_of_multiarySize (by positivity)
    (eventually_weightedSix_lt_four_mul_multiarySize.{u, v} hSK hε)

/-- **Rational fan-in-five frontier lower bound (`4 s > (3.87 - ε) n`), charging only multiary
gates.** -/
theorem eventually_387_div_100_lt_four_mul_multiarySize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 5 → c.Decides I Acc (S n) →
        (387 / 100 - ε) * n < 4 * c.multiarySize :=
  eventually_lt_mul_multiarySize_of_le WeightedKernel.sixCircuitCoefficient_ge_387
    (eventually_weightedSix_lt_four_mul_multiarySize.{u, v} hSK hε)

/-- **Rational fan-in-five frontier lower bound (`4 s > (3.87 - ε) n`).** -/
theorem eventually_387_div_100_lt_four_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 5 → c.Decides I Acc (S n) →
        (387 / 100 - ε) * n < 4 * c.innerSize :=
  eventually_lt_mul_innerSize_of_multiarySize (by positivity)
    (eventually_387_div_100_lt_four_mul_multiarySize.{u, v} hSK hε)

/-- **Nondeterministic fan-in-five frontier lower bound.** -/
theorem eventually_weightedSix_lt_four_mul_innerSize_of_nondeterministicDecides
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 5 → c.NondeterministicDecides I Acc (S n) →
        (1 + 2 * π / (3 * arccos (√5 / 3)) - ε) * n < 4 * c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_nondeterministicDecides.{u, v} (r := 5) (by norm_num)
    WeightedKernel.sixCoefficient_pos layoutBound_six_weighted hSK hε
  rwa [WeightedKernel.one_add_inv_sixCoefficient, show ((5 : ℕ) : ℝ) - 1 = 4 by norm_num] at h

end WorstCaseAndNondet

/-! ### Upgraded linear-map lower bounds (`r = 3, 4, 5`) -/

/-- **Upgraded fan-in-three lower bound (`2 s > (4 - ε) N`, i.e. `s > (2 - ε) N`) for totally
regular linear maps.** -/
theorem eventually_four_sub_mul_lt_two_mul_innerSize_of_isTotallyRegular {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v}) (I : Interpretation σ F)
      (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N), M.IsTotallyRegular →
        c.FanInAtMost 3 → c.Computes I (fun x => M *ᵥ x) → c.LinearCapacity I →
          (4 - ε) * N < 2 * c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_isTotallyRegular.{u, v} (r := 3) (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 3) layoutBound_four_one_third hε
  norm_num only at h
  exact h

/-- **Upgraded fan-in-three lower bound (`2 s > (4 - ε) N`) for totally regular linear maps over
finite fields**, over every basis. -/
theorem eventually_four_sub_mul_lt_two_mul_innerSize_of_isTotallyRegular_finite {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        M.IsTotallyRegular → c.FanInAtMost 3 → c.Computes I (fun x => M *ᵥ x) →
          (4 - ε) * N < 2 * c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_isTotallyRegular_finite.{u, v} (r := 3) (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 3) layoutBound_four_one_third hε
  norm_num only at h
  exact h

/-- **Upgraded fan-in-three lower bound (`2 s > (4 - ε) N`) for totally regular linear maps over
infinite fields**, over every polynomial basis. -/
theorem eventually_four_sub_mul_lt_two_mul_innerSize_of_isTotallyRegular_isPolynomial {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), I.IsPolynomial → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), M.IsTotallyRegular → c.FanInAtMost 3 →
          c.Computes I (fun x => M *ᵥ x) → (4 - ε) * N < 2 * c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_isTotallyRegular_isPolynomial.{u, v} (r := 3)
    (by norm_num) (by norm_num : (0 : ℝ) < 1 / 3) layoutBound_four_one_third hε
  norm_num only at h
  exact h

/-- **Upgraded fan-in-four lower bound (`3 s > (1 + 3π / (5 arccos (4 / 5)) - ε) N`) for totally
regular linear maps.** -/
theorem eventually_weightedFive_lt_three_mul_innerSize_of_isTotallyRegular {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v}) (I : Interpretation σ F)
      (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N), M.IsTotallyRegular →
        c.FanInAtMost 4 → c.Computes I (fun x => M *ᵥ x) → c.LinearCapacity I →
          (1 + 3 * π / (5 * arccos (4 / 5)) - ε) * N < 3 * c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_isTotallyRegular.{u, v} (r := 4) (by norm_num)
    WeightedKernel.fiveCoefficient_pos layoutBound_five_weighted hε
  rwa [WeightedKernel.one_add_inv_fiveCoefficient, show ((4 : ℕ) : ℝ) - 1 = 3 by norm_num] at h

/-- **Upgraded fan-in-five lower bound (`4 s > (1 + 2π / (3 arccos (√5 / 3)) - ε) N`) for totally
regular linear maps.** -/
theorem eventually_weightedSix_lt_four_mul_innerSize_of_isTotallyRegular {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v}) (I : Interpretation σ F)
      (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N), M.IsTotallyRegular →
        c.FanInAtMost 5 → c.Computes I (fun x => M *ᵥ x) → c.LinearCapacity I →
          (1 + 2 * π / (3 * arccos (√5 / 3)) - ε) * N < 4 * c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_isTotallyRegular.{u, v} (r := 5) (by norm_num)
    WeightedKernel.sixCoefficient_pos layoutBound_six_weighted hε
  rwa [WeightedKernel.one_add_inv_sixCoefficient, show ((5 : ℕ) : ℝ) - 1 = 4 by norm_num] at h

end Cslib.Circuits.Frontier
