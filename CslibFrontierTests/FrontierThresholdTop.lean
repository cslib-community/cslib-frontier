/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Frontier.ThresholdTop
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Basic

/-! Checked clients for frontier lower bounds with unbounded-real-weight threshold tops. -/

open Cslib.Circuits Cslib.Circuits.Frontier Cslib.Communication Real Filter

namespace CslibFrontierTests.FrontierThresholdTop

/-! ### Irrational-weight halfspaces and order-rank compression -/

/-- A concrete two-party halfspace with irrational weights `π` and `√2`. -/
example :
    let irrationalHalfspace (a b : Fin 4 → Bool) : Bool :=
      decide (∑ i : Fin 4, (if a i then π ^ (i.val + 1) else 0) +
        ∑ j : Fin 4, (if b j then -(√2 ^ (j.val + 1)) else 0) < 0)
    IsHalfspaceComb 1 irrationalHalfspace ∧ signRank irrationalHalfspace ≤ 2 := by
  intro irrationalHalfspace
  have h1 : IsHalfspaceComb 1 irrationalHalfspace :=
    ⟨fun v => v 0,
      fun _ a => ∑ i : Fin 4, if a i then π ^ (i.val + 1) else 0,
      fun _ b => ∑ j : Fin 4, if b j then -(√2 ^ (j.val + 1)) else 0,
      fun _ _ => rfl⟩
  exact ⟨h1, signRank_le_two_of_isHalfspaceComb_one h1⟩

example [DecidablePred (IsHalfspaceComb 2 (α := Fin 3) (β := Fin 3))] :
    (Finset.univ.filter fun f : Fin 3 → Fin 3 → Bool => IsHalfspaceComb 2 f).card ≤
      2 ^ 4 * 6 ^ 12 := by
  simpa using card_isHalfspaceComb_le 2 (Fin 3) (Fin 3)

/-! ### Unconditional `4.57597 n` average-case bound instantiated with `exists_halfspaceCombBias` -/

/-- Non-vacuous end-to-end instantiation: for `t = 3` unbounded-real-weight threshold units on top
of any fan-in-two Boolean program with at most `(4.57597 - 1/100) n` inner gates, some Boolean
family `S_n` has agreement at most `1/2 + 1/(n + 1) + exp (-γ n)`. -/
example : ∃ (S : ∀ n, Set (Fin n → Bool)) (γ : ℝ), 0 < γ ∧
    ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (g : ℕ)
      (p : Program σ n g) (T : ThresholdTop Bool n g 3),
      p.FanInAtMost 2 → (p.innerGates.card : ℝ) ≤ (457597 / 100000 - 1 / 100) * n →
        agreement (S n) {x | T.eval p I x = true} ≤
          1 / 2 + 1 / ((n : ℝ) + 1) + Real.exp (-(γ * n)) := by
  obtain ⟨S, hS, hK, -⟩ := exists_halfspaceCombBias_family 3
  obtain ⟨γ, hγ, H⟩ := eventually_agreement_thresholdTop_le_457597.{0, 0}
    (ε := 1 / 100) (by norm_num)
  exact ⟨S, γ, hγ, H Bool (fun _ => 3) (fun n => 8 * (n + 1) ^ 3 + 8)
    (fun n => 1 / ((n : ℝ) + 1)) S hS hK⟩

/-! ### Single-cut Forster bound (`1.89399 n`) on `hardForm` -/

example : ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (g : ℕ)
    (p : Program σ n g) (T : ThresholdTop Bool n g 1),
    p.FanInAtMost 2 → (∀ x, T.eval p I x = hardForm n x) →
      (189399 / 100000 - 1 / 100 : ℝ) * n < p.innerGates.card :=
  eventually_lt_innerSize_thresholdTop_hardForm_189399.{0} (ε := 1 / 100) (by norm_num)

end CslibFrontierTests.FrontierThresholdTop
