/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.BoundedPolynomial
public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
public import Mathlib.Algebra.BigOperators.Expect
import CslibFrontier.Foundations.Probability.InnerProductResampling

/-!
# Weighted point variance in the low-individual-degree test

The weights are the effects of a polynomial measurement. Factoring the weights
turns the state expectation of each sandwich into a squared GNS distance.
The product resampling inequality then bounds the global variance by the sum
of the single-coordinate variances, as in §7 and Lemma 8.3 of
[JNVWY2020LowIndividualDegree].

## Main definitions

* `Cslib.PCP.LowIndividualDegree.weightedPointVariance`: the weighted variation
  at independently sampled points.
* `Cslib.PCP.LowIndividualDegree.weightedPointResampling`: the variation when
  one uniformly chosen coordinate is resampled.

## Main results

* `Cslib.PCP.LowIndividualDegree.weightedPointVariance_le_resampling`: global
  variance is at most dimension times single-coordinate variance.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset Function MvPolynomial
open scoped BigOperators

variable {A F : Type*} {m d : ℕ} [Field F] [Fintype F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The weighted state distance between point effects selected by the same polynomial
at independent uniform points. This uses the sum over polynomial outcomes. -/
@[expose] noncomputable def weightedPointVariance (φ : AlgState A) (L : Point F m → Measurement F A)
    (T : Measurement (BoundedPolynomial F m d) A) : ℝ :=
  𝔼 u : Point F m, 𝔼 v : Point F m, ∑ g,
    let D := (L v).effect (eval v g.val) - (L u).effect (eval u g.val)
    (φ (star D * T.effect g * D)).re

/-- The weighted state distance when resampling one uniform coordinate. -/
@[expose] noncomputable def weightedPointResampling
    (φ : AlgState A) (L : Point F m → Measurement F A)
    (T : Measurement (BoundedPolynomial F m d) A) : ℝ :=
  𝔼 i : Fin m, 𝔼 u : Point F m, 𝔼 a : F, ∑ g,
    let v := update u i a
    let D := (L v).effect (eval v g.val) - (L u).effect (eval u g.val)
    (φ (star D * T.effect g * D)).re

/-- A step of the low-degree variance estimate. The global weighted point variance
is at most the dimension times the variance under a uniform coordinate update. -/
theorem weightedPointVariance_le_resampling (φ : AlgState A)
    (L : Point F m → Measurement F A) (T : Measurement (BoundedPolynomial F m d) A) :
    weightedPointVariance φ L T ≤ m * weightedPointResampling φ L T := by
  classical
  choose K hK using fun g => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (T.nonneg g)
  let : InnerProductSpace ℝ φ.toPositiveLinearMap.GNS := InnerProductSpace.complexToReal
  let V (g : BoundedPolynomial F m d) (u : Point F m) : φ.toPositiveLinearMap.GNS :=
    φ.toPreGNS (K g * (L u).effect (eval u g.val))
  let P (g : BoundedPolynomial F m d) (u v : Point F m) :=
    (L v).effect (eval v g.val) - (L u).effect (eval u g.val)
  have he (g : BoundedPolynomial F m d) (u v : Point F m) :
      (φ (star (P g u v) * T.effect g * P g u v)).re = ‖V g u - V g v‖ ^ 2 := by
    rw [norm_sub_rev]
    dsimp only [V]
    rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe, ← map_sub,
      ← mul_sub]
    change _ = φ.norm (K g * P g u v) ^ 2
    rw [AlgState.norm_sq, hK g, star_mul]
    simp only [mul_assoc]
  change (𝔼 u : Point F m, 𝔼 v : Point F m, ∑ g,
      (φ (star (P g u v) * T.effect g * P g u v)).re) ≤
    m * (𝔼 i : Fin m, 𝔼 u : Point F m, 𝔼 a : F, ∑ g,
      (φ (star (P g u (update u i a)) * T.effect g * P g u (update u i a))).re)
  simp only [he]
  have hcard (f : Fin m → ℝ) : m * (𝔼 i, f i) = ∑ i, f i := by
    simpa only [Fintype.card_fin] using Fintype.card_mul_expect f
  rw [hcard]
  simp only [expect_sum_comm]
  rw [sum_comm]
  exact sum_le_sum fun g _ =>
    Fintype.expect_expect_norm_sub_sq_le_sum_expect_expect_norm_sub_update_sq (V g)

end Cslib.PCP.LowIndividualDegree
