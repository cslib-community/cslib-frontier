/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.NetworkCreation.FLMPS
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Checked witnesses for NRTV Ch. 19 §19.2 network creation games (FLMPS 2003)

Kernel-checked examples (with zero `native_decide`) exercising
`CslibFrontier.GameTheory.NetworkCreation.FLMPS` across `Fin 3` and `Fin 4`:

1. **Disconnected `⊤` cost boundary and redundant-purchase non-equilibrium (`Fin 3`).**
2. **Exact `OPT` crossover at `α = 2` (`Fin 3`)** and regime-dependent equilibrium separation
   between `completeProfile`, `centerStarProfile`, and `leafStarProfile` (`α = 1 / 2` vs
   `α = 3 / 2`).
3. **Four-cycle `C_4` (`Fin 4`)**: a diameter-`2` graph that is neither complete nor a tree,
   achieving `OPT = 24` at the crossover `α = 2` (Exercise 19.2).
4. **Internal-sponsored 4-path `P_4` (`Fin 4`)**: a genuine non-star tree pure Nash equilibrium at
   `α = 3` whose social cost `29` strictly exceeds `OPT = 27` (`PoA > 1` while `PoS = 1`) and
   satisfies the tree bound `29 ≤ 5 · 27` and general bound `29 ≤ (6 √3 + 2) · 27`.
-/

public section

namespace CslibFrontierTests.NetworkCreationNRTV

open Cslib.GameTheory
open Cslib.GameTheory.NetworkCreationGame

/-- Concrete game with `α = 1 / 2 < 1` (`PoA = PoS = 1`, unique NE `K_n`). -/
noncomputable def gameHalf : NetworkCreationGame where
  alpha := 1 / 2
  alpha_pos := by norm_num

/-- Concrete game with `1 ≤ α = 3 / 2 < 2` (`K_n` optimal, stars are pure NE, `PoA ≤ 4 / 3`). -/
noncomputable def gameThreeHalves : NetworkCreationGame where
  alpha := 3 / 2
  alpha_pos := by norm_num

/-- Concrete game at the crossover `α = 2` (`K_n`, stars, and `C_4` all socially optimal). -/
def gameTwo : NetworkCreationGame where
  alpha := 2
  alpha_pos := by norm_num

/-- Concrete game with `α = 3 > 2` (stars uniquely optimal; `P_4` is a suboptimal tree NE). -/
def gameThree : NetworkCreationGame where
  alpha := 3
  alpha_pos := by norm_num

private theorem univ_fin3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide

private theorem univ_fin4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide

private theorem sum_fin3 (f : Fin 3 → ℝ) : ∑ x : Fin 3, f x = f 0 + f 1 + f 2 := by
  rw [univ_fin3]
  simp only [Finset.mem_insert, Finset.mem_singleton, (by decide : (0 : Fin 3) ≠ 1),
    (by decide : (0 : Fin 3) ≠ 2), (by decide : (1 : Fin 3) ≠ 2), or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton]
  ring

private theorem sum_fin4 (f : Fin 4 → ℝ) : ∑ x : Fin 4, f x = f 0 + f 1 + f 2 + f 3 := by
  rw [univ_fin4]
  simp only [Finset.mem_insert, Finset.mem_singleton, (by decide : (0 : Fin 4) ≠ 1),
    (by decide : (0 : Fin 4) ≠ 2), (by decide : (0 : Fin 4) ≠ 3), (by decide : (1 : Fin 4) ≠ 2),
    (by decide : (1 : Fin 4) ≠ 3), (by decide : (2 : Fin 4) ≠ 3), or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton]
  ring

/-! ## Disconnected and redundant-edge boundary checks (`Fin 3`) -/

/-- Empty profile on `Fin 3`: disconnected, so player cost and social cost equal `⊤`. -/
def emptyProfile3 : Fin 3 → Finset (Fin 3) := fun _ => ∅

theorem playerCost_emptyProfile3 : gameThree.playerCost emptyProfile3 0 = ⊤ := by
  rw [playerCost_eq_top_iff]
  refine ⟨1, fun hr => ?_⟩
  obtain ⟨p⟩ := hr
  cases p with
  | @cons _ w _ hadj _ =>
    rw [formedGraph_adj] at hadj
    simp [emptyProfile3] at hadj

theorem socialCost_emptyProfile3 : gameThree.socialCost emptyProfile3 = ⊤ := by
  apply gameThree.socialCost_eq_top_of_not_connected
  intro hconn
  obtain ⟨p⟩ := hconn (0 : Fin 3) 1
  cases p with
  | @cons _ w _ hadj _ =>
    rw [formedGraph_adj] at hadj
    simp [emptyProfile3] at hadj

/-- All-buy profile on `Fin 3` (with self-loops and doubly bought edges): not a pure NE. -/
def redundantAll3 : Fin 3 → Finset (Fin 3) := fun _ => Finset.univ

theorem not_isPureNash_redundantAll3 : ¬ gameThree.IsPureNash redundantAll3 := fun hs =>
  hs.notMem_self 0 (Finset.mem_univ 0)

/-! ## Exact `OPT` crossover and equilibria on `Fin 3` -/

theorem optSocialCost_fin3_values :
    gameHalf.optSocialCost (Fin 3) = 15 / 2 ∧
      gameThreeHalves.optSocialCost (Fin 3) = 21 / 2 ∧
      gameTwo.optSocialCost (Fin 3) = 12 ∧
      gameThree.optSocialCost (Fin 3) = 14 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gameHalf.optSocialCost_eq_completeSocialCost (by norm_num [gameHalf])]
    norm_num [completeSocialCost, gameHalf]
  · rw [gameThreeHalves.optSocialCost_eq_completeSocialCost (by norm_num [gameThreeHalves])]
    norm_num [completeSocialCost, gameThreeHalves]
  · rw [gameTwo.optSocialCost_eq_completeSocialCost (by norm_num [gameTwo])]
    norm_num [completeSocialCost, gameTwo]
  · rw [gameThree.optSocialCost_eq_starSocialCost (by norm_num [gameThree])]
    norm_num [starSocialCost, gameThree]

/-- For `α = 1 / 2 < 1`, `completeProfile` on `Fin 3` is a pure Nash equilibrium, whereas
`centerStarProfile 0` is not (since `formedGraph ≠ ⊤`). -/
theorem fin3_alpha_half_equilibria :
    gameHalf.IsPureNash (completeProfile (V := Fin 3)) ∧
      ¬ gameHalf.IsPureNash (centerStarProfile (0 : Fin 3)) := by
  refine ⟨gameHalf.isPureNash_completeProfile (by norm_num [gameHalf]), fun hs => ?_⟩
  have htop := hs.formedGraph_eq_top_of_alpha_lt_one (by norm_num [gameHalf])
  have hadj : (formedGraph (centerStarProfile (0 : Fin 3))).Adj 1 2 := by
    rw [htop]
    decide
  rw [formedGraph_centerStarProfile, SimpleGraph.starGraph_adj] at hadj
  exact absurd hadj (by decide)

/-- For `α = 3 / 2 > 1`, both `centerStarProfile` and `leafStarProfile` are pure Nash equilibria
on `Fin 3`, whereas `completeProfile` is not (player `0` profits by dropping edge `{0, 2}`). -/
theorem fin3_alpha_three_halves_equilibria :
    gameThreeHalves.IsPureNash (centerStarProfile (0 : Fin 3)) ∧
      gameThreeHalves.IsPureNash (leafStarProfile (0 : Fin 3)) ∧
      ¬ gameThreeHalves.IsPureNash (completeProfile (V := Fin 3)) := by
  refine ⟨gameThreeHalves.isPureNash_centerStarProfile 0 (by norm_num [gameThreeHalves]),
    gameThreeHalves.isPureNash_leafStarProfile 0 (by norm_num [gameThreeHalves]), fun hs => ?_⟩
  let s := completeProfile (V := Fin 3)
  let s' := Function.update s 0 ({1} : Finset (Fin 3))
  have hadj01 : (formedGraph s').Adj 0 1 := by
    rw [formedGraph_adj]
    exact ⟨by decide, Or.inl (by simp [s'])⟩
  have hadj12 : (formedGraph s').Adj 1 2 := by
    rw [formedGraph_adj]
    exact ⟨by decide, Or.inl (by simp [s', s, completeProfile])⟩
  have hreach' : ∀ v : Fin 3, (formedGraph s').Reachable 0 v := by
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.refl 0
    · exact hadj01.reachable
    · exact hadj01.reachable.trans hadj12.reachable
  have hle := hs.connectedPlayerCost_le 0 {1} hreach'
  have hd_s : ∑ v : Fin 3, ((formedGraph s).dist 0 v : ℝ) = 2 := by
    rw [formedGraph_completeProfile, sum_fin3]
    have h01 : (⊤ : SimpleGraph (Fin 3)).dist 0 1 = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (by decide)
    have h02 : (⊤ : SimpleGraph (Fin 3)).dist 0 2 = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (by decide)
    simp only [SimpleGraph.dist_self, Nat.cast_zero, h01, h02, Nat.cast_one]
    norm_num
  have hd_s' : ∑ v : Fin 3, ((formedGraph s').dist 0 v : ℝ) ≤ 3 := by
    rw [sum_fin3]
    have h01 : (formedGraph s').dist 0 1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj01
    have h02 : (formedGraph s').dist 0 2 ≤ 2 := by
      have htri := hadj01.reachable.dist_triangle_left 2
      have h12 : (formedGraph s').dist 1 2 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj12
      omega
    have h02R : ((formedGraph s').dist 0 2 : ℝ) ≤ 2 := by exact_mod_cast h02
    simp only [SimpleGraph.dist_self, Nat.cast_zero, h01, Nat.cast_one, zero_add]
    linarith
  have hcard_s : ((s 0).card : ℝ) = 2 := by
    have : (s 0).card = 2 := by decide
    exact_mod_cast this
  unfold connectedPlayerCost at hle
  rw [Function.update_self, Finset.card_singleton, Nat.cast_one] at hle
  dsimp only [s, s'] at hd_s hd_s' hcard_s
  rw [hcard_s, hd_s] at hle
  simp only [gameThreeHalves] at hle
  linarith

/-! ## Four-player (`Fin 4`) cycle `C_4` and path `P_4` witnesses -/

/-- Directed 4-cycle profile `0 → 1 → 2 → 3 → 0` on `Fin 4`: forms `C_4` (diameter `2`, `4` edges,
neither complete nor a tree). -/
def cycle4Profile : Fin 4 → Finset (Fin 4)
  | 0 => {1}
  | 1 => {2}
  | 2 => {3}
  | 3 => {0}

private theorem cycle4_adj_succ (i : Fin 4) : (formedGraph cycle4Profile).Adj i (i + 1) := by
  fin_cases i <;>
    (rw [formedGraph_adj]; exact ⟨by decide, Or.inl (by decide)⟩)

theorem connected_cycle4Profile : (formedGraph cycle4Profile).Connected := by
  have hr0 : ∀ v : Fin 4, (formedGraph cycle4Profile).Reachable 0 v := by
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.refl 0
    · exact (cycle4_adj_succ 0).reachable
    · exact (cycle4_adj_succ 0).reachable.trans (cycle4_adj_succ 1).reachable
    · exact ((cycle4_adj_succ 3).symm).reachable
  exact ⟨fun u v => (hr0 u).symm.trans (hr0 v)⟩

theorem diam_cycle4Profile (u v : Fin 4) : (formedGraph cycle4Profile).dist u v ≤ 2 := by
  have hcases : v = u ∨ v = u + 1 ∨ v = (u + 1) + 1 ∨ u = v + 1 := by
    fin_cases u <;> fin_cases v <;> decide
  rcases hcases with rfl | rfl | rfl | rfl
  · simp
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (cycle4_adj_succ u)]
    omega
  · have ha := SimpleGraph.dist_eq_one_iff_adj.mpr (cycle4_adj_succ u)
    have hb := SimpleGraph.dist_eq_one_iff_adj.mpr (cycle4_adj_succ (u + 1))
    exact (connected_cycle4Profile.dist_triangle (v := u + 1)).trans (by omega)
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (cycle4_adj_succ v).symm]
    omega

/-- At `α = 2`, `C_4` achieves `optSocialCost (Fin 4) = 24`, witnessing Exercise 19.2 (diameter-`2`
non-star, non-complete graphs are socially optimal at `α = 2`). -/
theorem cycle4Profile_optimal_at_two :
    gameTwo.connectedSocialCost cycle4Profile = gameTwo.optSocialCost (Fin 4) ∧
      gameTwo.optSocialCost (Fin 4) = 24 := by
  have hclean : gameTwo.connectedSocialCost cycle4Profile =
      gameTwo.graphSocialCost (formedGraph cycle4Profile) :=
    gameTwo.connectedSocialCost_eq_graphSocialCost_of_clean
      (fun u => by fin_cases u <;> decide)
      (fun u v huv => by fin_cases u <;> fin_cases v <;> simp [cycle4Profile] at huv ⊢)
  have hopt_eq := (gameTwo.graphSocialCost_eq_optSocialCost_iff_of_alpha_eq_two rfl
    connected_cycle4Profile).mpr diam_cycle4Profile
  have hval : gameTwo.optSocialCost (Fin 4) = 24 := by
    rw [gameTwo.optSocialCost_eq_completeSocialCost (by norm_num [gameTwo])]
    norm_num [completeSocialCost, gameTwo]
  exact ⟨hclean.trans hopt_eq, hval⟩

/-- Internal-sponsored 4-path profile `0 — 1 — 2 — 3` (`1` buys `{0, 2}`, `2` buys `{3}`):
a non-star tree pure Nash equilibrium for `α = 3` (`socialCost = 29 > 27 = OPT`, while
`29 ≤ 5 * 27 = 135`). -/
def internalPath4 : Fin 4 → Finset (Fin 4)
  | 0 => ∅
  | 1 => {0, 2}
  | 2 => {3}
  | 3 => ∅

theorem isTree_internalPath4 : (formedGraph internalPath4).IsTree := by
  have h01 : (formedGraph internalPath4).Adj 0 1 := by
    rw [formedGraph_adj]; exact ⟨by decide, Or.inr (by decide)⟩
  have h12 : (formedGraph internalPath4).Adj 1 2 := by
    rw [formedGraph_adj]; exact ⟨by decide, Or.inl (by decide)⟩
  have h23 : (formedGraph internalPath4).Adj 2 3 := by
    rw [formedGraph_adj]; exact ⟨by decide, Or.inl (by decide)⟩
  have hr0 : ∀ v : Fin 4, (formedGraph internalPath4).Reachable 0 v := by
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.refl 0
    · exact h01.reachable
    · exact h01.reachable.trans h12.reachable
    · exact (h01.reachable.trans h12.reachable).trans h23.reachable
  have hconn : (formedGraph internalPath4).Connected :=
    ⟨fun u v => (hr0 u).symm.trans (hr0 v)⟩
  rw [SimpleGraph.isTree_iff_connected_and_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  refine ⟨hconn, ?_⟩
  have hcard : ∑ u : Fin 4, (internalPath4 u).card = 3 := by decide
  rw [← sum_card_eq_card_edgeFinset
    (fun u => by fin_cases u <;> decide)
    (fun u v huv => by fin_cases u <;> fin_cases v <;> simp [internalPath4] at huv ⊢),
    hcard]
  decide

private theorem dist_internalPath4 :
    (formedGraph internalPath4).dist 0 1 = 1 ∧
      (formedGraph internalPath4).dist 1 2 = 1 ∧
      (formedGraph internalPath4).dist 2 3 = 1 ∧
      (formedGraph internalPath4).dist 0 2 = 2 ∧
      (formedGraph internalPath4).dist 1 3 = 2 ∧
      (formedGraph internalPath4).dist 0 3 = 3 := by
  let H := formedGraph internalPath4
  have hconn := isTree_internalPath4.connected
  have h01 : H.Adj 0 1 := by rw [formedGraph_adj]; exact ⟨by decide, Or.inr (by decide)⟩
  have h12 : H.Adj 1 2 := by rw [formedGraph_adj]; exact ⟨by decide, Or.inl (by decide)⟩
  have h23 : H.Adj 2 3 := by rw [formedGraph_adj]; exact ⟨by decide, Or.inl (by decide)⟩
  have hd01 : H.dist 0 1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h01
  have hd12 : H.dist 1 2 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h12
  have hd23 : H.dist 2 3 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h23
  have hd02 : H.dist 0 2 = 2 := by
    have hle : H.dist 0 2 ≤ 2 := by
      have htri := hconn.dist_triangle (u := 0) (v := 1) (w := 2)
      dsimp only [H] at hd01 hd12 ⊢
      omega
    have hnadj : ¬ H.Adj 0 2 := by rw [formedGraph_adj]; decide
    have hge := hconn.one_lt_dist_of_ne_of_not_adj (by decide) hnadj
    dsimp only [H] at hle hge ⊢
    omega
  have hd13 : H.dist 1 3 = 2 := by
    have hle : H.dist 1 3 ≤ 2 := by
      have htri := hconn.dist_triangle (u := 1) (v := 2) (w := 3)
      dsimp only [H] at hd12 hd23 ⊢
      omega
    have hnadj : ¬ H.Adj 1 3 := by rw [formedGraph_adj]; decide
    have hge := hconn.one_lt_dist_of_ne_of_not_adj (by decide) hnadj
    dsimp only [H] at hle hge ⊢
    omega
  have hd03 : H.dist 0 3 = 3 := by
    have hle : H.dist 0 3 ≤ 3 := by
      have htri := hconn.dist_triangle (u := 0) (v := 2) (w := 3)
      dsimp only [H] at hd02 hd23 ⊢
      omega
    have hnadj : ¬ H.Adj 0 3 := by rw [formedGraph_adj]; decide
    have hge2 := hconn.one_lt_dist_of_ne_of_not_adj (by decide) hnadj
    have hne2 : H.dist 0 3 ≠ 2 := by
      intro h2
      have hed2 : H.edist 0 3 = 2 := by
        rw [← (hconn 0 3).coe_dist_eq_edist, h2]
        rfl
      obtain ⟨_, -, ⟨x, hx⟩⟩ := SimpleGraph.edist_eq_two_iff.mp hed2
      rw [SimpleGraph.mem_commonNeighbors] at hx
      rcases hx with ⟨ha, hb⟩
      rw [formedGraph_adj] at ha hb
      fin_cases x <;> simp [internalPath4] at ha hb
    dsimp only [H] at hle hge2 hne2 ⊢
    omega
  exact ⟨hd01, hd12, hd23, hd02, hd13, hd03⟩

private theorem dist_sum_ge_three (s' : Fin 4 → Finset (Fin 4)) (u : Fin 4)
    (hr : ∀ v : Fin 4, (formedGraph s').Reachable u v) :
    3 ≤ ∑ v : Fin 4, ((formedGraph s').dist u v : ℝ) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
  simp only [SimpleGraph.dist_self, Nat.cast_zero, add_zero]
  have hcard3 : (Finset.univ.erase u).card = 3 := by fin_cases u <;> decide
  calc (3 : ℝ) = ∑ _v ∈ Finset.univ.erase u, (1 : ℝ) := by
        rw [Finset.sum_const, hcard3, nsmul_eq_mul, mul_one]
        norm_num
    _ ≤ ∑ v ∈ Finset.univ.erase u, ((formedGraph s').dist u v : ℝ) :=
        Finset.sum_le_sum fun v hv => by
          exact_mod_cast (hr v).pos_dist_of_ne (Finset.ne_of_mem_erase hv).symm

/-- `internalPath4` has social cost `29 > 27 = OPT` at `α = 3`, and is a genuine pure Nash
equilibrium: a concrete non-star tree equilibrium exercising `socialCost_le_five_of_isTree`. -/
theorem isPureNash_internalPath4 :
    gameThree.IsPureNash internalPath4 ∧
      gameThree.connectedSocialCost internalPath4 = 29 ∧
      gameThree.optSocialCost (Fin 4) = 27 := by
  obtain ⟨hd01, hd12, hd23, hd02, hd13, hd03⟩ := dist_internalPath4
  have hd10 : (formedGraph internalPath4).dist 1 0 = 1 := by
    rw [SimpleGraph.dist_comm]; exact hd01
  have hd21 : (formedGraph internalPath4).dist 2 1 = 1 := by
    rw [SimpleGraph.dist_comm]; exact hd12
  have hd32 : (formedGraph internalPath4).dist 3 2 = 1 := by
    rw [SimpleGraph.dist_comm]; exact hd23
  have hd20 : (formedGraph internalPath4).dist 2 0 = 2 := by
    rw [SimpleGraph.dist_comm]; exact hd02
  have hd31 : (formedGraph internalPath4).dist 3 1 = 2 := by
    rw [SimpleGraph.dist_comm]; exact hd13
  have hd30 : (formedGraph internalPath4).dist 3 0 = 3 := by
    rw [SimpleGraph.dist_comm]; exact hd03
  have hcost0 : gameThree.connectedPlayerCost internalPath4 0 = 6 := by
    unfold connectedPlayerCost
    rw [sum_fin4]
    have hc : (internalPath4 0).card = 0 := by decide
    simp only [hc, Nat.cast_zero, mul_zero, SimpleGraph.dist_self, hd01, hd02, hd03, Nat.cast_one,
      Nat.cast_ofNat]
    norm_num
  have hcost1 : gameThree.connectedPlayerCost internalPath4 1 = 10 := by
    unfold connectedPlayerCost
    rw [sum_fin4]
    have hc : (internalPath4 1).card = 2 := by decide
    simp only [hc, SimpleGraph.dist_self, Nat.cast_zero, hd10, hd12, hd13, Nat.cast_one,
      Nat.cast_ofNat, gameThree]
    norm_num
  have hcost2 : gameThree.connectedPlayerCost internalPath4 2 = 7 := by
    unfold connectedPlayerCost
    rw [sum_fin4]
    have hc : (internalPath4 2).card = 1 := by decide
    simp only [hc, SimpleGraph.dist_self, Nat.cast_zero, hd20, hd21, hd23, Nat.cast_one,
      Nat.cast_ofNat, gameThree]
    norm_num
  have hcost3 : gameThree.connectedPlayerCost internalPath4 3 = 6 := by
    unfold connectedPlayerCost
    rw [sum_fin4]
    have hc : (internalPath4 3).card = 0 := by decide
    simp only [hc, Nat.cast_zero, mul_zero, SimpleGraph.dist_self, hd30, hd31, hd32, Nat.cast_one,
      Nat.cast_ofNat]
    norm_num
  have hsc : gameThree.connectedSocialCost internalPath4 = 29 := by
    unfold connectedSocialCost
    rw [sum_fin4, hcost0, hcost1, hcost2, hcost3]
    norm_num
  have hopt : gameThree.optSocialCost (Fin 4) = 27 := by
    rw [gameThree.optSocialCost_eq_starSocialCost (by norm_num [gameThree])]
    norm_num [starSocialCost, gameThree]
  refine ⟨?_, hsc, hopt⟩
  intro u t
  let s := internalPath4
  rw [gameThree.playerCost_of_connected isTree_internalPath4.connected]
  by_cases hreach' : ∀ v : Fin 4, (formedGraph (Function.update s u t)).Reachable u v
  · rw [gameThree.playerCost_of_forall_reachable hreach', WithTop.coe_le_coe]
    fin_cases u
    · -- Player 0 (baseline cost 6)
      change gameThree.connectedPlayerCost internalPath4 0 ≤
        gameThree.connectedPlayerCost (Function.update s 0 t) 0
      rcases Nat.lt_trichotomy t.card 1 with h0 | h1 | h2
      · have ht : t = ∅ := Finset.card_eq_zero.mp (by omega)
        have heq : Function.update s 0 t = internalPath4 := by
          ext x; fin_cases x <;> simp [s, ht, internalPath4]
        rw [heq]
      · rw [hcost0]
        unfold connectedPlayerCost
        rw [Function.update_self]
        simp only [gameThree]
        obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
        rw [Finset.card_singleton, Nat.cast_one, sum_fin4]
        have hd1' : (1 : ℝ) ≤ ((formedGraph (Function.update s 0 {w})).dist 0 1 : ℝ) := by
          exact_mod_cast (hreach' 1).pos_dist_of_ne (by decide)
        have hd2' : (1 : ℝ) ≤ ((formedGraph (Function.update s 0 {w})).dist 0 2 : ℝ) := by
          exact_mod_cast (hreach' 2).pos_dist_of_ne (by decide)
        have hd3' : (1 : ℝ) ≤ ((formedGraph (Function.update s 0 {w})).dist 0 3 : ℝ) := by
          exact_mod_cast (hreach' 3).pos_dist_of_ne (by decide)
        fin_cases w
        · have hn3 : ¬ (formedGraph (Function.update s 0 {0})).Adj 0 3 := by
            rw [formedGraph_adj]; decide
          have h3ge2 : (2 : ℝ) ≤ ((formedGraph (Function.update s 0 {0})).dist 0 3 : ℝ) := by
            exact_mod_cast (hreach' 3).one_lt_dist_of_ne_of_not_adj (by decide) hn3
          simp only [SimpleGraph.dist_self, Nat.cast_zero]
          linarith
        · have hn3 : ¬ (formedGraph (Function.update s 0 {1})).Adj 0 3 := by
            rw [formedGraph_adj]; decide
          have h3ge2 : (2 : ℝ) ≤ ((formedGraph (Function.update s 0 {1})).dist 0 3 : ℝ) := by
            exact_mod_cast (hreach' 3).one_lt_dist_of_ne_of_not_adj (by decide) hn3
          simp only [SimpleGraph.dist_self, Nat.cast_zero]
          linarith
        · have hn3 : ¬ (formedGraph (Function.update s 0 {2})).Adj 0 3 := by
            rw [formedGraph_adj]; decide
          have h3ge2 : (2 : ℝ) ≤ ((formedGraph (Function.update s 0 {2})).dist 0 3 : ℝ) := by
            exact_mod_cast (hreach' 3).one_lt_dist_of_ne_of_not_adj (by decide) hn3
          simp only [SimpleGraph.dist_self, Nat.cast_zero]
          linarith
        · have hn2 : ¬ (formedGraph (Function.update s 0 {3})).Adj 0 2 := by
            rw [formedGraph_adj]; decide
          have h2ge2 : (2 : ℝ) ≤ ((formedGraph (Function.update s 0 {3})).dist 0 2 : ℝ) := by
            exact_mod_cast (hreach' 2).one_lt_dist_of_ne_of_not_adj (by decide) hn2
          simp only [SimpleGraph.dist_self, Nat.cast_zero]
          linarith
      · rw [hcost0]
        unfold connectedPlayerCost
        rw [Function.update_self]
        simp only [gameThree]
        have ht2 : (2 : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast h2
        have hsum_ge3 := dist_sum_ge_three (Function.update s 0 t) 0 hreach'
        linarith
    · -- Player 1 (baseline cost 10)
      change gameThree.connectedPlayerCost internalPath4 1 ≤
        gameThree.connectedPlayerCost (Function.update s 1 t) 1
      rw [hcost1]
      unfold connectedPlayerCost
      rw [Function.update_self]
      simp only [gameThree]
      have h0_mem : (0 : Fin 4) ∈ t := by
        by_contra h0t
        obtain ⟨p⟩ := (hreach' 0).symm
        cases p with
        | @cons _ w _ hadj _ =>
          rw [formedGraph_adj] at hadj
          fin_cases w <;> simp [s, internalPath4, h0t] at hadj
      have h23_mem : (2 : Fin 4) ∈ t ∨ (3 : Fin 4) ∈ t := by
        by_contra hnot
        push Not at hnot
        have hclosed : ∀ a b : Fin 4, (formedGraph (Function.update s 1 t)).Adj a b →
            (a ∈ ({0, 1} : Finset (Fin 4)) → b ∈ ({0, 1} : Finset (Fin 4))) := by
          intro a b hab ha
          rw [formedGraph_adj] at hab
          fin_cases a <;> fin_cases b <;>
            simp [s, internalPath4, hnot.1, hnot.2] at hab ha ⊢
        have hwalk : ∀ a b : Fin 4, (formedGraph (Function.update s 1 t)).Walk a b →
            a ∈ ({0, 1} : Finset (Fin 4)) → b ∈ ({0, 1} : Finset (Fin 4)) := by
          intro a b q
          induction q with
          | nil => exact id
          | @cons a b d hab _ ih => exact fun ha => ih (hclosed a b hab ha)
        obtain ⟨q⟩ := hreach' 2
        have h2in := hwalk 1 2 q (by decide)
        exact absurd h2in (by decide)
      have ht_ge2 : 2 ≤ t.card := by
        rcases h23_mem with h2m | h3m
        · exact Finset.one_lt_card.mpr ⟨0, h0_mem, 2, h2m, by decide⟩
        · exact Finset.one_lt_card.mpr ⟨0, h0_mem, 3, h3m, by decide⟩
      rcases lt_or_eq_of_le ht_ge2 with ht3 | ht2
      · have ht3R : (3 : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast ht3
        have hsum_ge3 := dist_sum_ge_three (Function.update s 1 t) 1 hreach'
        linarith
      · have hex : ∃ v ∈ ({0, 2, 3} : Finset (Fin 4)), v ∉ t :=
          Finset.exists_mem_notMem_of_card_lt_card (by rw [← ht2]; decide)
        obtain ⟨v, hv_in, hvt⟩ := hex
        have h1v_ne : (1 : Fin 4) ≠ v := by
          fin_cases v <;> simp at hv_in ⊢
        have hnadj : ¬ (formedGraph (Function.update s 1 t)).Adj 1 v := by
          rw [formedGraph_adj]
          rintro ⟨-, hv1 | h1v⟩
          · rw [Function.update_self] at hv1
            exact hvt hv1
          · rw [Function.update_of_ne h1v_ne.symm] at h1v
            fin_cases v <;> simp [s, internalPath4] at h1v
        have hv_ge2 : (2 : ℝ) ≤ ((formedGraph (Function.update s 1 t)).dist 1 v : ℝ) := by
          exact_mod_cast (hreach' v).one_lt_dist_of_ne_of_not_adj h1v_ne hnadj
        have hd0' : (1 : ℝ) ≤ ((formedGraph (Function.update s 1 t)).dist 1 0 : ℝ) := by
          exact_mod_cast (hreach' 0).pos_dist_of_ne (by decide)
        have hd2' : (1 : ℝ) ≤ ((formedGraph (Function.update s 1 t)).dist 1 2 : ℝ) := by
          exact_mod_cast (hreach' 2).pos_dist_of_ne (by decide)
        have hd3' : (1 : ℝ) ≤ ((formedGraph (Function.update s 1 t)).dist 1 3 : ℝ) := by
          exact_mod_cast (hreach' 3).pos_dist_of_ne (by decide)
        have hsum4 : 4 ≤ ∑ x : Fin 4, ((formedGraph (Function.update s 1 t)).dist 1 x : ℝ) := by
          rw [sum_fin4]
          simp only [SimpleGraph.dist_self, Nat.cast_zero]
          fin_cases v
          · exact absurd h0_mem hvt
          · exact absurd rfl h1v_ne
          · change (2 : ℝ) ≤ ((formedGraph (Function.update s 1 t)).dist 1 2 : ℝ) at hv_ge2
            linarith
          · change (2 : ℝ) ≤ ((formedGraph (Function.update s 1 t)).dist 1 3 : ℝ) at hv_ge2
            linarith
        have ht2R : (t.card : ℝ) = 2 := by exact_mod_cast ht2.symm
        rw [ht2R]
        linarith
    · -- Player 2 (baseline cost 7)
      change gameThree.connectedPlayerCost internalPath4 2 ≤
        gameThree.connectedPlayerCost (Function.update s 2 t) 2
      have h3_mem : (3 : Fin 4) ∈ t := by
        by_contra h3t
        obtain ⟨p⟩ := (hreach' 3).symm
        cases p with
        | @cons _ w _ hadj _ =>
          rw [formedGraph_adj] at hadj
          fin_cases w <;> simp [s, internalPath4, h3t] at hadj
      have ht_ge1 : 1 ≤ t.card := Finset.card_pos.mpr ⟨3, h3_mem⟩
      rcases lt_or_eq_of_le ht_ge1 with ht2 | ht1
      · rw [hcost2]
        unfold connectedPlayerCost
        rw [Function.update_self]
        simp only [gameThree]
        have ht2R : (2 : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast ht2
        have hsum_ge3 := dist_sum_ge_three (Function.update s 2 t) 2 hreach'
        linarith
      · have ht_eq : t = {3} := by
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp ht1.symm
          rw [hw] at h3_mem
          rw [hw, Finset.mem_singleton.mp h3_mem]
        have heq : Function.update s 2 t = internalPath4 := by
          ext x; fin_cases x <;> simp [s, ht_eq, internalPath4]
        rw [heq]
    · -- Player 3 (baseline cost 6)
      change gameThree.connectedPlayerCost internalPath4 3 ≤
        gameThree.connectedPlayerCost (Function.update s 3 t) 3
      rcases Nat.lt_trichotomy t.card 1 with h0 | h1 | h2
      · have ht : t = ∅ := Finset.card_eq_zero.mp (by omega)
        have heq : Function.update s 3 t = internalPath4 := by
          ext x; fin_cases x <;> simp [s, ht, internalPath4]
        rw [heq]
      · rw [hcost3]
        unfold connectedPlayerCost
        rw [Function.update_self]
        simp only [gameThree]
        obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
        rw [Finset.card_singleton, Nat.cast_one, sum_fin4]
        have hd0' : (1 : ℝ) ≤ ((formedGraph (Function.update s 3 {w})).dist 3 0 : ℝ) := by
          exact_mod_cast (hreach' 0).pos_dist_of_ne (by decide)
        have hd1' : (1 : ℝ) ≤ ((formedGraph (Function.update s 3 {w})).dist 3 1 : ℝ) := by
          exact_mod_cast (hreach' 1).pos_dist_of_ne (by decide)
        have hd2' : (1 : ℝ) ≤ ((formedGraph (Function.update s 3 {w})).dist 3 2 : ℝ) := by
          exact_mod_cast (hreach' 2).pos_dist_of_ne (by decide)
        fin_cases w
        · have hn1 : ¬ (formedGraph (Function.update s 3 {0})).Adj 3 1 := by
            rw [formedGraph_adj]; decide
          have h1ge2 : (2 : ℝ) ≤ ((formedGraph (Function.update s 3 {0})).dist 3 1 : ℝ) := by
            exact_mod_cast (hreach' 1).one_lt_dist_of_ne_of_not_adj (by decide) hn1
          simp only [SimpleGraph.dist_self, Nat.cast_zero]
          linarith
        · have hn0 : ¬ (formedGraph (Function.update s 3 {1})).Adj 3 0 := by
            rw [formedGraph_adj]; decide
          have h0ge2 : (2 : ℝ) ≤ ((formedGraph (Function.update s 3 {1})).dist 3 0 : ℝ) := by
            exact_mod_cast (hreach' 0).one_lt_dist_of_ne_of_not_adj (by decide) hn0
          simp only [SimpleGraph.dist_self, Nat.cast_zero]
          linarith
        · have hn0 : ¬ (formedGraph (Function.update s 3 {2})).Adj 3 0 := by
            rw [formedGraph_adj]; decide
          have h0ge2 : (2 : ℝ) ≤ ((formedGraph (Function.update s 3 {2})).dist 3 0 : ℝ) := by
            exact_mod_cast (hreach' 0).one_lt_dist_of_ne_of_not_adj (by decide) hn0
          simp only [SimpleGraph.dist_self, Nat.cast_zero]
          linarith
        · have hn0 : ¬ (formedGraph (Function.update s 3 {3})).Adj 3 0 := by
            rw [formedGraph_adj]; decide
          have h0ge2 : (2 : ℝ) ≤ ((formedGraph (Function.update s 3 {3})).dist 3 0 : ℝ) := by
            exact_mod_cast (hreach' 0).one_lt_dist_of_ne_of_not_adj (by decide) hn0
          simp only [SimpleGraph.dist_self, Nat.cast_zero]
          linarith
      · rw [hcost3]
        unfold connectedPlayerCost
        rw [Function.update_self]
        simp only [gameThree]
        have ht2 : (2 : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast h2
        have hsum_ge3 := dist_sum_ge_three (Function.update s 3 t) 3 hreach'
        linarith
  · rw [gameThree.playerCost_eq_top_iff.mpr (not_forall.mp hreach')]
    exact le_top

/-- Concrete instantiation of `PoA ≤ 4 / 3`, tree `PoA ≤ 5` (on suboptimal `P_4`!), and
`PoA ≤ 6 √α + 2` on `Fin 4`. -/
theorem fin4_poa_bounds :
    gameThreeHalves.connectedSocialCost (centerStarProfile (0 : Fin 4)) ≤
      4 / 3 * gameThreeHalves.optSocialCost (Fin 4) ∧
    gameThree.connectedSocialCost internalPath4 ≤
      5 * gameThree.optSocialCost (Fin 4) ∧
    gameThree.connectedSocialCost internalPath4 ≤
      (6 * Real.sqrt gameThree.alpha + 2) * gameThree.optSocialCost (Fin 4) := by
  have hs15 := gameThreeHalves.isPureNash_centerStarProfile (0 : Fin 4)
    (by norm_num [gameThreeHalves])
  have hs_p4 := isPureNash_internalPath4.1
  exact ⟨hs15.socialCost_le_four_thirds_of_alpha_lt_two (by norm_num [gameThreeHalves]),
    hs_p4.socialCost_le_five_of_isTree isTree_internalPath4,
    hs_p4.socialCost_le_six_mul_sqrt_add_two⟩

end CslibFrontierTests.NetworkCreationNRTV
