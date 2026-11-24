/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game

/-!
# Expected advantage of two-stage games

`Game.advantage_bind_le` and `Game.advantage_bind_le_of_support` bound the advantage between two
games with a common first stage by a uniform bound on the advantages of the second stages. This
module gives the bound by the expectation of these advantages over the first stage, as an extended
non-negative real, and the resulting step of a hybrid argument for two-stage games whose first
stages differ as well.

## Main results

* `Cslib.Crypto.Game.coe_advantage_bind_le_tsum`: the advantage between two games with a common
  first stage is at most the expected advantage of the second stages.
* `Cslib.Crypto.Game.coe_advantage_bind_bind_le`: replacing both stages costs at most the advantage
  of replacing the first stage plus the expected advantage of replacing the second.
-/

public section

namespace Cslib.Crypto.Game

open scoped ENNReal NNReal

/-- The acceptance probability of a game exceeds that of another game by at most their
advantage. -/
private theorem apply_true_le_add_advantage (game1 game2 : Game) :
    game1 true ≤ game2 true + (advantage game1 game2 : ℝ≥0∞) := by
  have h : game1.succProbability ≤ game2.succProbability + advantage game1 game2 := by
    rw [advantage, NNReal.nndist_eq]
    exact tsub_le_iff_left.mp (le_max_left _ _)
  calc game1 true = (game1.succProbability : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)).symm
    _ ≤ ((game2.succProbability + advantage game1 game2 : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr h
    _ = game2 true + (advantage game1 game2 : ℝ≥0∞) := by
        rw [ENNReal.coe_add, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]

/-- **Expected advantage.** The advantage between two games with a common first stage `d` is at
most the expectation over `d` of the advantage between the second stages. -/
theorem coe_advantage_bind_le_tsum {α : Type*} (d : PMF α) (game1 game2 : α → Game) :
    (advantage (d.bind game1) (d.bind game2) : ℝ≥0∞) ≤
      ∑' a, d a * (advantage (game1 a) (game2 a) : ℝ≥0∞) := by
  have key (g1 g2 : α → Game) : (d.bind g1) true ≤
      (d.bind g2) true + ∑' a, d a * (advantage (g1 a) (g2 a) : ℝ≥0∞) := by
    have hpt (a : α) : d a * g1 a true ≤
        d a * g2 a true + d a * (advantage (g1 a) (g2 a) : ℝ≥0∞) :=
      (mul_le_mul' le_rfl (apply_true_le_add_advantage _ _)).trans_eq (mul_add _ _ _)
    simp only [PMF.bind_apply]
    rw [← tsum_add]
    exact tsum_le_tsum hpt
  have hle (a : α) : d a * (advantage (game1 a) (game2 a) : ℝ≥0∞) ≤ d a := by
    calc d a * (advantage (game1 a) (game2 a) : ℝ≥0∞) ≤ d a * 1 := by
          gcongr
          exact ENNReal.coe_le_one_iff.mpr (advantage_le_one _ _)
      _ = d a := mul_one _
  have hB : ∑' a, d a * (advantage (game1 a) (game2 a) : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((tsum_le_tsum hle).trans_eq d.tsum_coe)
  have h21 : (d.bind game2) true ≤
      (d.bind game1) true + ∑' a, d a * (advantage (game1 a) (game2 a) : ℝ≥0∞) := by
    refine (key game2 game1).trans_eq ?_
    congr 1
    exact tsum_congr fun a => by rw [advantage_comm]
  have h := ENNReal.ofReal_le_ofReal (advantage_le_of_apply_le hB (key game1 game2) h21)
  rwa [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hB] at h

/-- **One step of a hybrid argument for two-stage games.** Replacing the first stage `p` by `q` and
the second stage `game1` by `game2` costs at most the advantage of replacing the first stage in
front of `game1`, plus the expectation over `q` of the advantage between the second stages. -/
theorem coe_advantage_bind_bind_le {α : Type*} (p q : PMF α) (game1 game2 : α → Game) :
    (advantage (p.bind game1) (q.bind game2) : ℝ≥0∞) ≤
      advantage (p.bind game1) (q.bind game1) +
        ∑' a, q a * (advantage (game1 a) (game2 a) : ℝ≥0∞) := by
  refine (ENNReal.coe_le_coe.mpr (advantage_triangle _ (q.bind game1) _)).trans ?_
  rw [ENNReal.coe_add]
  exact add_le_add le_rfl (coe_advantage_bind_le_tsum q game1 game2)

end Cslib.Crypto.Game
