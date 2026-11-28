/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Frontier.PolynomialWitness
import CslibFrontier.Foundations.Combinatorics.SetFamily.ShadowDegeneracy

/-!
# Checked `module` clients for `Frontier.PolynomialWitness`

1. Exact evaluation of `polyThreshold 2 2 = 10` under `module` encapsulation.
2. Concrete down-closed set system check for `card_filter_card_ge_le`.
3. Finite-`n` quartic (`deg ≤ 4`) dense rectangle-free witness (`n = 8`, density `≥ 128`).
4. End-to-end `(4.57596) n` deterministic, nondeterministic, and `O(n ^ (-1/3))` two-sided
   correlation bounds for quartic polynomials over `𝔽₂`.
-/

public section

open Cslib Cslib.Circuits Cslib.Circuits.Frontier Finset Filter Real

namespace CslibFrontierTests.FrontierPolynomialWitness

/-! ### 1. Exact value of `polyThreshold 2 2` -/

/-- Exact evaluation of `polyThreshold 2 2` under `module` encapsulation. -/
theorem polyThreshold_two_two : polyThreshold 2 2 = 10 := by
  rw [polyThreshold]
  have h4 : (((2 : ℕ).factorial * 2 : ℕ) : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) = 2 := by
    rw [show (((2 : ℕ).factorial * 2 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul two_pos.le]
    norm_num
  rw [h4]
  norm_num

/-! ### 2. Concrete check of `Finset.card_filter_card_ge_le` over infinite ground type `ℕ` -/

private def natSkeleton : Finset (Finset ℕ) :=
  (({0, 1, 2, 3} : Finset ℕ).powerset).filter fun I => #I ≤ 2

private theorem natSkeleton_downClosed :
    ∀ ⦃I J : Finset ℕ⦄, J ⊆ I → I ∈ natSkeleton → J ∈ natSkeleton := by
  intro I J hJI hI
  rw [natSkeleton, mem_filter, mem_powerset] at hI ⊢
  exact ⟨hJI.trans hI.1, (card_le_card hJI).trans hI.2⟩

example : #{I ∈ natSkeleton | 2 ≤ #I} ≤ #{I ∈ natSkeleton | #I = 1} ^ 1 * 2 ^ 4 :=
  Finset.card_filter_card_ge_le (p := 2) (d := 4) (by decide) natSkeleton_downClosed (by decide)

/-! ### 3. Finite-`n` quartic dense rectangle-free witness at `n = 8` -/

example : ∃ f ∈ BitString.lowDegree (ZMod 2) (Fin 8) 4,
    RectangleFree {x | f x = 1} (polyThreshold 2 10) ∧
    RectangleFree {x | f x = 0} (polyThreshold 2 10) ∧
    128 ≤ {x | f x = 1}.ncard := by
  obtain ⟨f, hf, hfree, hdense⟩ := exists_quartic_rectangleFree 8
  exact ⟨f, hf, hfree 1, hfree 0, by simpa using hdense⟩

/-! ### 4. End-to-end `4.57596 n` deterministic, nondeterministic & correlation bounds -/

example : ∃ f : ∀ n, (Fin n → Bool) → ZMod 2,
    (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4) ∧
    ∀ᶠ n in atTop,
      ∀ (k : ℕ) (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ (n + k) 1),
        c.FanInAtMost 2 → c.NondeterministicDecides I Acc {x | f n x = 1} →
          (457596 / 100000 : ℝ) * n < c.innerSize := by
  obtain ⟨f, hf, H⟩ := exists_quartic_switched_lt_innerSize_nondeterministic.{0}
  refine ⟨f, hf, ?_⟩
  filter_upwards [H (ε := 1 / 100000) (by norm_num)] with n hn k σ I Acc c hfan hdec
  refine lt_of_le_of_lt ?_ (hn k σ I Acc c hfan hdec)
  exact mul_le_mul_of_nonneg_right
    (by linarith [Switched.circuitCoefficient_ge_457597]) (Nat.cast_nonneg n)

/-- Two-sided `|correlation| ≤ 2 (n + 1) ^ (-1/3) + 2 exp (-γ n)` up to `4.57596 n` inner gates
for a family of degree-`4` quartic polynomials. -/
example : ∃ f : ∀ n, (Fin n → Bool) → ZMod 2,
    (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4) ∧
    ∃ γ > 0, ∀ᶠ n in atTop,
      ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost 2 →
        (c.innerSize : ℝ) ≤ (457596 / 100000 : ℝ) * n →
          |correlation {x | f n x = 1} {x | c.eval I x 0 ∈ Acc}| ≤
            2 * ((n : ℝ) + 1) ^ (-(1 / 3 : ℝ)) + 2 * Real.exp (-(γ * n)) := by
  obtain ⟨f, hf, H⟩ := exists_quartic_abs_correlation_le_457597_div_100000.{0}
    (β := 1 / 3) (by norm_num) (by norm_num)
  obtain ⟨γ, hγ, hEv⟩ := H (ε := 1 / 100000) (by norm_num)
  refine ⟨f, hf, γ, hγ, ?_⟩
  filter_upwards [hEv] with n hn σ I Acc c hfan hsize
  exact hn σ I Acc c hfan (by linarith)

end CslibFrontierTests.FrontierPolynomialWitness
