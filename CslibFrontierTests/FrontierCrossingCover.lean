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

/-! Checked clients for the crossing-cover Gaussian-wave frontier lower bounds. -/

open Cslib.Circuits Cslib.Circuits.Frontier Cslib.Circuits.Frontier.CrossingCover Matrix Real Filter

namespace CslibFrontierTests.FrontierCrossingCover

/-! ### Certified alternating wave sum and numerical comparisons -/

example : alternatingWaveSum 13 < 130649 / 1000000 := alternatingWaveSum_13_lt

example : 0 ≤ alternatingWaveSum 13 :=
  alternatingWaveSum_nonneg_of_odd (by decide)

example : (4827 / 1000 : ℝ) < 630649 / 130649 := by norm_num
example : (2913 / 1000 : ℝ) < 380649 / 130649 := by norm_num

example : ar2AltWaveSum 13 = alternatingWaveSum 13 :=
  ar2AltWaveSum_eq_alternatingWaveSum 13

/-! ### Strict concrete check on the cubic theta multigraph (parallel edges) -/

/-- The cubic theta multigraph: two vertices joined by three parallel edges. -/
private def thetaGraph : Multigraph Bool (Fin 3) where
  src _ := false
  tgt _ := true

example : crossingCover thetaGraph (fun v => v) = 1 := by
  refine le_antisymm ?_ ?_
  · refine csInf_le (OrderBot.bddBelow _) ?_
    refine ⟨{false}, fun e hne => ?_, by simp⟩
    exact Or.inl (by simp [thetaGraph])
  · by_contra hlt
    have h0 : crossingCover thetaGraph (fun v => v) = 0 := by omega
    have hmem : 0 ∈ {k : ℕ | ∃ C : Finset Bool, IsCrossingCover thetaGraph (fun v => v) C ∧
        C.card = k} := by
      rw [← h0]
      exact Nat.sInf_mem ⟨2, Finset.univ, fun _ _ => Or.inl (Finset.mem_univ _), by simp⟩
    obtain ⟨C, hC, hcard⟩ := hmem
    have hE : C = ∅ := Finset.card_eq_zero.mp hcard
    have := hC (0 : Fin 3) (by simp [thetaGraph])
    simp [hE, thetaGraph] at this

example : ∃ lay : Layout Bool, (thetaGraph.width lay : ℝ) ≤ (1 : ℕ) + 6 :=
  exists_width_le_max_crossingCover thetaGraph
    (fun v => by cases v <;> simp [Multigraph.incidenceSet, thetaGraph])
    [false, true] (fun v => by cases v <;> simp) 1
    (fun i _ => by
      match i with
      | 0 => simp [crossingCover_const]
      | 1 =>
        refine csInf_le (OrderBot.bddBelow _) ?_
        refine ⟨{false}, fun e _ => Or.inl (by simp [thetaGraph]), by simp⟩
      | i + 2 =>
        have htake : ([false, true] : List Bool).take (i + 2) = [false, true] := by
          simp
        rw [htake]
        have hconst : (fun v : Bool => decide (v ∈ ([false, true] : List Bool))) =
            fun _ => true := by ext v; cases v <;> simp
        rw [hconst, crossingCover_const]
        exact Nat.zero_le 1)

/-! ### Top-level layout bounds and downstream frontier lower bounds -/

example : LayoutBound 3 (130649 / 500000) := layoutBound_crossingCover

example : MultiaryLowerBound.{0, 0} (630649 / 130649) := multiaryLowerBound_crossingCover
example : CircuitLowerBound.{0, 0} (630649 / 130649) := circuitLowerBound_crossingCover
example : CircuitLowerBound.{0, 0} (4827 / 1000) := circuitLowerBound_4827_div_1000

example : MultiaryAverageCaseBound.{0, 0} (630649 / 130649) :=
  multiaryAverageCaseBound_crossingCover
example : AverageCaseBound.{0, 0} (630649 / 130649) := averageCaseBound_crossingCover
example : AverageCaseBound.{0, 0} (4827 / 1000) := averageCaseBound_4827_div_1000

example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
    ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool) (C : Circuit σ n 1),
      C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ 2913 / 1000 * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_2913

example : ∀ᶠ N in atTop,
    ∀ (c : Circuit (arithSignature ℚ) N N),
      c.Computes (arithInterpretation ℚ) (fun x => cauchyNat ℚ N *ᵥ x) →
        (4827 / 1000 - 1 / 100 : ℝ) * N < c.innerSize := by
  filter_upwards [eventually_crossingCover_sub_mul_lt_innerSize_arith_cauchyNat.{0} (ε := 1 / 100)
    (by norm_num)] with N hN c hc
  refine lt_of_le_of_lt ?_ (hN ℚ c hc)
  exact mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg N)

example : ∀ᶠ N in atTop, ∀ (q : ℕ) [Fact q.Prime], 2 * N ≤ q →
    ∀ (σ : Signature.{0}) (I : Interpretation σ (ZMod q)) (c : Circuit σ N N),
      c.FanInAtMost 2 → c.Computes I (fun x => cauchyNat (ZMod q) N *ᵥ x) →
        (630649 / 130649 - 1 / 100 : ℝ) * N < c.innerSize :=
  eventually_crossingCover_sub_mul_lt_innerSize_cauchyNat_zmod.{0} (ε := 1 / 100) (by norm_num)

end CslibFrontierTests.FrontierCrossingCover
