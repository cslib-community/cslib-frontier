/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Circuit.Frontier.Correlation
public import CslibFrontier.Computability.Circuit.Frontier.FanInTwo
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound
public import CslibFrontier.Computability.Circuit.Frontier.Linear.Unconditional
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
public import CslibFrontier.Computability.Circuit.Frontier.Witness
import CslibFrontier.Computability.Circuit.Frontier.BoundedFanIn

/-! Circuit and layout clients of the matched-pair Gaussian bound. -/

public section

open Cslib.Circuits Cslib.Circuits.Frontier Matrix Real Filter Set

namespace CslibFrontierTests.FrontierPairBound

/-! ### 1. `@[expose]` definitional checks and strict numerical hierarchy -/

example : Gaussian.PairBound.pairBoundCoefficient = 277773 / 2000000 := rfl

example : Gaussian.PairBound.rawRatio = 7071 / 10000 := rfl

example : Gaussian.PairBound.pairBoundCoefficient < 5 / 36 ∧
    (5 / 36 : ℝ) < Switched.switchedCoefficient ∧
    Switched.switchedCoefficient < Gaussian.gaussianCoefficient :=
  ⟨Gaussian.PairBound.pairBoundCoefficient_lt_five_div_thirty_six,
    Gaussian.PairBound.five_div_thirty_six_lt_switchedCoefficient,
    Switched.switchedCoefficient_lt_gaussianCoefficient⟩

example : CubicLayoutBound Gaussian.PairBound.pairBoundCoefficient ∧
    CubicLayoutBound (5 / 36) ∧
    LayoutBound 3 (2 * Gaussian.PairBound.pairBoundCoefficient) ∧
    LayoutBound 3 (5 / 18) :=
  ⟨cubicLayoutBound_pairBound, cubicLayoutBound_five_div_thirty_six,
    layoutBound_pairBound, layoutBound_five_div_eighteen⟩

/-! ### 2. Unconditional non-vacuous worst-case, nondeterministic, and average-case witnesses -/

/-- Worst-case multiary gate bound on a dense rectangle-free family. -/
example : ∃ (S : ∀ n, Set (Fin n → Bool)) (K : ℕ → ℕ), DenseRectangleFree S K ∧
    ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1277773 / 277773 - 1 / 1000 : ℝ) * n < c.multiarySize := by
  obtain ⟨S, hrf, hlog, hdef, _⟩ := exists_rectangleFree_family
  have hSK : DenseRectangleFree S (fun n => n + 2) := ⟨hrf, hlog, hdef⟩
  exact ⟨S, fun n => n + 2, hSK,
    multiaryLowerBound_pairBound.{0, 0} Bool S _ hSK _ (by norm_num)⟩

/-- Nondeterministic gate bound on a dense rectangle-free family. -/
example : ∃ (S : ∀ n, Set (Fin n → Bool)) (K : ℕ → ℕ), DenseRectangleFree S K ∧
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 → c.NondeterministicDecides I Acc (S n) →
        (1277773 / 277773 - 1 / 1000 : ℝ) * n < c.innerSize := by
  obtain ⟨S, hrf, hlog, hdef, _⟩ := exists_rectangleFree_family
  have hSK : DenseRectangleFree S (fun n => n + 2) := ⟨hrf, hlog, hdef⟩
  exact ⟨S, fun n => n + 2, hSK,
    eventually_pairBound_sub_mul_lt_innerSize_of_nondeterministicDecides.{0, 0} hSK (by norm_num)⟩

/-- Average-case multiary gate bound on a family with small rectangle bias. -/
example : ∃ (S : ∀ n, Set (Fin n → Bool)) (γ : ℝ), 0 < γ ∧
    ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 2 →
        (c.multiarySize : ℝ) ≤ (1277773 / 277773 - 1 / 1000) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤
            1 / 2 + 1 / ((n : ℝ) + 1) + Real.exp (-(γ * n)) := by
  obtain ⟨S, hbias, hlog, _⟩ := exists_rectangleBias_family
  obtain ⟨γ, hγ, H⟩ := multiaryAverageCaseBound_pairBound.{0, 0} (1 / 1000) (by norm_num)
  exact ⟨S, γ, hγ, H Bool S (fun n => (n + 1) ^ 3) (fun n => 1 / ((n : ℝ) + 1)) hbias hlog⟩

/-! ### 3. Unconditional `hardForm` correlation (`2.80n`) and Cauchy linear-map (`4.60 N`) checks -/

example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool)
    (Acc : Set Bool) (C : Circuit σ n 1), C.FanInAtMost 2 →
      (C.multiarySize : ℝ) ≤ 14 / 5 * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_of_lt_pairBound_multiarySize.{0} (by norm_num)

example : ∀ᶠ N in atTop, ∀ (c : Circuit (arithSignature ℚ) N N),
    c.Computes (arithInterpretation ℚ) (fun x => Matrix.cauchyNat ℚ N *ᵥ x) →
      (1277773 / 277773 - 1 / 1000 : ℝ) * N < c.innerSize := by
  filter_upwards [eventually_pairBound_sub_mul_lt_innerSize_of_isTotallyRegular_isPolynomial.{0, 0}
    (ε := 1 / 1000) (by norm_num)] with N hN c hc
  exact hN ℚ _ _ isPolynomial_arithInterpretation _ c (isTotallyRegular_cauchyNat N)
    c.fanInAtMost_two_arith hc

example : ∀ᶠ N in atTop, ∀ (q : ℕ) [Fact q.Prime], 2 * N ≤ q → ∀ (σ : Signature.{0})
    (I : Interpretation σ (ZMod q)) (c : Circuit σ N N), c.FanInAtMost 2 →
      c.Computes I (fun x => Matrix.cauchyNat (ZMod q) N *ᵥ x) →
        (1277773 / 277773 - 1 / 1000 : ℝ) * N < c.innerSize := by
  filter_upwards [eventually_pairBound_sub_mul_lt_innerSize_of_isTotallyRegular.{0, 0}
    (ε := 1 / 1000) (by norm_num)] with N hN q _ hq σ I c hfan hc
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  exact hN (ZMod q) σ I _ c (isTotallyRegular_cauchyNat_zmod hq) hfan hc
    (c.linearCapacity_of_finite I)

end CslibFrontierTests.FrontierPairBound
