/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Frontier.Correlation
import CslibFrontier.Computability.Circuit.Frontier.FanInTwo
import CslibFrontier.Computability.Circuit.Frontier.Ledger.Unconditional
import CslibFrontier.Computability.Circuit.Frontier.Linear.Unconditional
import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic

/-! Checked clients for the median-switched Gaussian frontier lower bounds. -/

open Cslib.Circuits Cslib.Circuits.Frontier Matrix Real Filter

namespace CslibFrontierTests.FrontierSwitched

/-! ### Exact numerical comparisons -/

example : Switched.switchedCoefficient < Gaussian.gaussianCoefficient :=
  Switched.switchedCoefficient_lt_gaussianCoefficient

example : (457597 / 100000 : ℝ) ≤ 1 + 2 * π / (3 * arccos (5 / 6)) :=
  Switched.circuitCoefficient_ge_457597

example : (183 / 40 : ℝ) ≤ 1 + 2 * π / (3 * arccos (5 / 6)) :=
  Switched.circuitCoefficient_ge_183_div_40

example : (278798 / 100000 : ℝ) ≤ 1 + π / (3 * arccos (5 / 6)) :=
  Switched.correlationThreshold_ge

example : (114 / 25 : ℝ) < 183 / 40 := by norm_num

example : (1 + π / (3 * arccos ((1 + 2 * √2) / 4))) <
    (1 + 2 * π / (3 * arccos (5 / 6))) := by
  rw [← Gaussian.one_add_inv_two_mul_gaussianCoefficient,
    ← Switched.one_add_inv_two_mul_switchedCoefficient]
  have h1 := Switched.switchedCoefficient_pos
  have h2 := Switched.switchedCoefficient_lt_gaussianCoefficient
  have hlt : 1 / (2 * Gaussian.gaussianCoefficient) < 1 / (2 * Switched.switchedCoefficient) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  linarith

/-! ### Concrete interval-to-cutwidth check on the theta multigraph (with parallel edges) -/

/-- The cubic theta multigraph: two vertices joined by three parallel edges. -/
private def thetaGraph : Multigraph Bool (Fin 3) where
  src _ := false
  tgt _ := true

example : ∃ σ : Layout Bool, thetaGraph.width σ ≤ 3 :=
  Switched.exists_width_le_of_intervals thetaGraph
    (fun v => by cases v <;> simp [Multigraph.incidenceSet, thetaGraph])
    0 (fun _ => 0) (fun _ => 0)
    (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => ⟨0, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩)
    (fun t _ => by
      have h : (Switched.intervalBag (fun _ : Bool => 0) (fun _ : Bool => 0) t).card ≤
          Fintype.card Bool := Finset.card_le_univ _
      simpa using h)

/-! ### Non-vacuous client instantiations -/

example : CircuitLowerBound.{0, 0} (457597 / 100000) :=
  circuitLowerBound_457597_div_100000

example : AverageCaseBound.{0, 0} (183 / 40) :=
  averageCaseBound_183_div_40

example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
    ∀ (σ : Cslib.Circuits.Signature.{0}) (I : Cslib.Circuits.Interpretation σ Bool)
      (Acc : Set Bool) (C : Cslib.Circuits.Circuit σ n 1), C.FanInAtMost 2 →
        (C.innerSize : ℝ) ≤ 2787 / 1000 * n →
          |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_2787

example : ∀ᶠ N in atTop,
    ∀ (c : Circuit (arithSignature ℚ) N N),
      c.Computes (arithInterpretation ℚ) (fun x => Matrix.cauchyNat ℚ N *ᵥ x) →
        (457597 / 100000 - 1 / 100 : ℝ) * N < c.innerSize := by
  filter_upwards [eventually_switched_sub_mul_lt_innerSize_arith_cauchyNat.{0} (ε := 1 / 100)
    (by norm_num)] with N hN c hc
  refine lt_of_le_of_lt ?_ (hN ℚ c hc)
  exact mul_le_mul_of_nonneg_right
    (by linarith [Switched.circuitCoefficient_ge_457597]) (Nat.cast_nonneg N)

example : ∀ᶠ N in atTop, ∀ (q : ℕ) [Fact q.Prime], 2 * N ≤ q →
    ∀ (σ : Signature.{0})
      (I : Interpretation σ (ZMod q)) (c : Circuit σ N N),
        c.FanInAtMost 2 → c.Computes I (fun x => Matrix.cauchyNat (ZMod q) N *ᵥ x) →
          (1 + 2 * π / (3 * arccos (5 / 6)) - 1 / 100) * N < c.innerSize :=
  eventually_switched_sub_mul_lt_innerSize_cauchyNat_zmod.{0} (ε := 1 / 100) (by norm_num)

end CslibFrontierTests.FrontierSwitched
