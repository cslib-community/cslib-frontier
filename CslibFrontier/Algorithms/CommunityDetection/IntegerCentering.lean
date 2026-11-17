/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.CommunityDetection.Algorithm
public import CslibFrontier.Probability.StochasticBlockModel.Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer centering and row-margin transfer

The exactly represented matrix `B = D² A - c (J-I)` differs from `D²` times the ideal shifted
centered matrix by `(D² m-c) J + (c-D² p) I`, where `m=(p+q)/2`. If `c` approximates `D² m`
within one and lies in `[0,D²]`, the change in every true-label row margin is at most `n+D²`.
This deterministic comparison lets integer arithmetic reuse the stochastic block model's
row-margin concentration theorem without requiring rational edge probabilities.
-/

public section

namespace Cslib.Algorithms.CommunityDetection

open Finset Matrix BitString Probability.StochasticBlockModel
open scoped unitInterval

variable {n : ℕ}

/-- Integer centering differs from the ideal shifted matrix by a constant rank-one matrix
and a scalar diagonal matrix. -/
theorem integerMatrix_cast_eq (params : PowerParameters) (p q : I)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (integerMatrix params G).map (Int.castRingHom ℝ) =
      (params.resolution : ℝ) ^ 2 • shiftedCenteredAdjacency p q G +
      ((params.resolution : ℝ) ^ 2 * midpoint p q - params.center) •
        Matrix.of (fun _ _ => (1 : ℝ)) +
      ((params.center : ℝ) - (params.resolution : ℝ) ^ 2 * p) • 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [integerMatrix, shiftedCenteredAdjacency, centeredAdjacency, gap,
      Probability.StochasticBlockModel.midpoint]
    ring
  · by_cases ha : G.Adj i j <;>
      simp [integerMatrix, Matrix.map_apply, shiftedCenteredAdjacency, centeredAdjacency,
        SimpleGraph.adjMatrix, hij, ha, gap, Probability.StochasticBlockModel.midpoint] <;> ring

/-- Centering within the scaled probability interval bounds every integer matrix entry. -/
theorem abs_integerMatrix_le (params : PowerParameters)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : params.center ≤ params.resolution ^ 2) (i j : Fin n) :
    |((integerMatrix params G i j : ℤ) : ℝ)| ≤ (params.resolution : ℝ) ^ 2 := by
  have hc' : (params.center : ℝ) ≤ (params.resolution : ℝ) ^ 2 := by exact_mod_cast hc
  have hcz : (0 : ℝ) ≤ params.center := Nat.cast_nonneg _
  by_cases hij : i = j
  · simp [integerMatrix, hij]
  · by_cases ha : G.Adj i j
    · simp only [integerMatrix, hij, ite_false, ha, ite_true, Int.cast_sub, Int.cast_pow,
        Int.cast_natCast]
      rw [abs_of_nonneg (sub_nonneg.mpr hc')]
      linarith
    · simpa [integerMatrix, hij, ha] using hc'

/-- The diagonal correction between integer and ideal centering has magnitude at most `D²`. -/
theorem abs_diagonal_error_le (params : PowerParameters) (p : I)
    (hc : params.center ≤ params.resolution ^ 2) :
    |(params.center : ℝ) - (params.resolution : ℝ) ^ 2 * p| ≤
      (params.resolution : ℝ) ^ 2 := by
  have hc' : (params.center : ℝ) ≤ (params.resolution : ℝ) ^ 2 := by exact_mod_cast hc
  have hp0 := mul_nonneg (sq_nonneg (params.resolution : ℝ)) p.2.1
  have hp1 := mul_le_mul_of_nonneg_left p.2.2 (sq_nonneg (params.resolution : ℝ))
  have hcz : (0 : ℝ) ≤ params.center := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Replacing exact real centering by an integer numerator changes every true-label row
margin by at most `n+D²`, for every graph and every labeling. -/
theorem abs_integerMatrix_margin_sub_le (params : PowerParameters) (p q : I)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (g : Fin n → Bool)
    (hc : params.center ≤ params.resolution ^ 2)
    (hcenter : |(params.resolution : ℝ) ^ 2 * midpoint p q - params.center| ≤ 1)
    (i : Fin n) :
    |signVal (g i) * ∑ j, (integerMatrix params G).map (Int.castRingHom ℝ) i j * signVal (g j) -
        (params.resolution : ℝ) ^ 2 *
          (signVal (g i) * ∑ j, shiftedCenteredAdjacency p q G i j * signVal (g j))| ≤
      (n : ℝ) + (params.resolution : ℝ) ^ 2 := by
  let S : ℝ := (params.resolution : ℝ) ^ 2
  let a : ℝ := S * midpoint p q - params.center
  let b : ℝ := (params.center : ℝ) - S * p
  have hrow := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ =>
    (M.mulVec fun j => signVal (g j)) i) (integerMatrix_cast_eq params p q G)
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at hrow
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul] at hrow
  have heq : signVal (g i) *
        ∑ j, (integerMatrix params G).map (Int.castRingHom ℝ) i j * signVal (g j) -
      S * (signVal (g i) * ∑ j, shiftedCenteredAdjacency p q G i j * signVal (g j)) =
        signVal (g i) * (a * ∑ j, signVal (g j)) + b := by
    calc
      _ = signVal (g i) * (a * ∑ j, signVal (g j)) + b *
          (signVal (g i) * signVal (g i)) := by
        rw [hrow]
        dsimp only [S, a, b]
        ring
      _ = _ := by rw [signVal_mul_self, mul_one]
  have hsum : |∑ j : Fin n, signVal (g j)| ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ j : Fin n, |signVal (g j)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp
  rw [heq]
  calc
    |signVal (g i) * (a * ∑ j, signVal (g j)) + b|
        ≤ |signVal (g i) * (a * ∑ j, signVal (g j))| + |b| := abs_add_le _ _
    _ ≤ (n : ℝ) + S := by
      apply add_le_add _ (abs_diagonal_error_le params p hc)
      calc
        |signVal (g i) * (a * ∑ j, signVal (g j))| =
            |a| * |∑ j, signVal (g j)| := by simp only [abs_mul, abs_signVal, one_mul]
        _ ≤ 1 * |∑ j, signVal (g j)| :=
          mul_le_mul_of_nonneg_right hcenter (abs_nonneg _)
        _ ≤ n := by simpa only [one_mul] using hsum

end Cslib.Algorithms.CommunityDetection
