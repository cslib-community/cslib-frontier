/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.NetworkFormation.LocalConnection.Bounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checked witnesses for local connection bounds (`LocalConnection.Bounds`)

Kernel-checked examples (with zero `native_decide` and zero internal unfolding) exercising
`CslibFrontier.GameTheory.NetworkFormation.LocalConnection.Bounds` via public equation lemmas:

1. **Small-`α` regime separation (`Fin 3`, `α = 1 / 2` and `α = 3 / 2`):** `completeProfile` is
   a pure NE at `α = 1 / 2` while `starCenterProfile 0` is not (Exercise 19.3 uniqueness of `K_n`),
   and for `α = 3 / 2`, `⊤` is uniquely socially optimal (`Exercise 19.1`) while stars are pure
   NEs bounded by `PoA ≤ 4 / 3`.
2. **Four-cycle `C_4` (`Fin 4`, `α = 2`):** a diameter-`2` graph that is neither complete nor a
   star, socially optimal at `α = 2` with social cost `24` (Exercise 19.2).
3. **Internal-sponsored 4-path `P_4` (`Fin 4`, `α = 3`):** a non-star tree pure Nash equilibrium
   with `socialCost 3 internalPath4 = 29 > 27 = OPT`, exercising strict star uniqueness for
   `α > 2` (Exercise 19.1), tree `PoA ≤ 5` (FLMPS Theorem 2), tightened Lemma 19.4 (`3d - 1`),
   and the `O(√α)` corollaries (`3√(4α + 1) - 1` and `6√α + 2`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.LocalConnectionBounds

open Finset SimpleGraph Cslib.GameTheory.LocalConnection
open scoped ENNReal

/-! ### 1. Small-`α` regime separation on `Fin 3` (`α = 1 / 2` vs `α = 3 / 2`) -/

/-- For `α = 1 / 2 < 1`, `completeProfile` on `Fin 3` is a pure Nash equilibrium and socially
optimal, whereas `starCenterProfile 0` is not a pure NE (since `formedGraph ≠ ⊤`). -/
theorem fin3_alpha_half_equilibria :
    IsPureNash (1 / 2 : ℝ) (completeProfile : Profile (Fin 3)) ∧
      IsSocialOptimum (1 / 2 : ℝ) (completeProfile : Profile (Fin 3)) ∧
      ¬ IsPureNash (1 / 2 : ℝ) (starCenterProfile (0 : Fin 3)) := by
  have hcNE := isPureNash_completeProfile (V := Fin 3) (α := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨hcNE, hcNE.isSocialOptimum_of_lt_one (by norm_num) (by norm_num), fun hs => ?_⟩
  have htop := hs.formedGraph_eq_top_of_lt_one (by norm_num) (by norm_num)
  have hadj : (formedGraph (starCenterProfile (0 : Fin 3))).Adj 1 2 := by
    rw [htop]
    decide
  rw [formedGraph_starCenterProfile, starGraph_adj] at hadj
  exact absurd hadj (by decide)

/-- Strict uniqueness of `⊤` at `α = 3 / 2 < 2` rejects `starGraph 0` on `Fin 3`, while
`starCenterProfile 0` satisfies `PoA ≤ 4 / 3` against `completeProfile`. -/
theorem fin3_alpha_three_halves_opt_and_poa :
    IsOptimalNetwork (3 / 2 : ℝ) (⊤ : SimpleGraph (Fin 3)) ∧
      ¬ IsOptimalNetwork (3 / 2 : ℝ) (starGraph (0 : Fin 3)) ∧
      socialCost (3 / 2 : ℝ) (starCenterProfile (0 : Fin 3)) ≤
        (4 / 3) * socialCost (3 / 2 : ℝ) (completeProfile : Profile (Fin 3)) := by
  have hopt_top : IsOptimalNetwork (3 / 2 : ℝ) (⊤ : SimpleGraph (Fin 3)) :=
    (isOptimalNetwork_iff_eq_top_of_lt_two (V := Fin 3) (by norm_num) (by norm_num)).mpr rfl
  have hnot_star : ¬ IsOptimalNetwork (3 / 2 : ℝ) (starGraph (0 : Fin 3)) := by
    rw [isOptimalNetwork_iff_eq_top_of_lt_two (by norm_num) (by norm_num)]
    intro h
    have hadj : (starGraph (0 : Fin 3)).Adj 1 2 := by
      rw [h]
      decide
    rw [starGraph_adj] at hadj
    exact absurd hadj (by decide)
  have hstar_ne := isPureNash_starCenterProfile (α := 3 / 2) (by norm_num) (0 : Fin 3)
  have htop_conn : (formedGraph (completeProfile : Profile (Fin 3))).Connected := by
    rw [formedGraph_completeProfile]
    exact connected_top
  exact ⟨hopt_top, hnot_star,
    hstar_ne.socialCost_le_four_thirds_mul_of_lt_two (by norm_num) (by norm_num) htop_conn⟩

/-! ### 2. Four-cycle `C_4` at `α = 2` (`Exercise 19.2`) -/

/-- Directed 4-cycle profile `0 → 1 → 2 → 3 → 0` on `Fin 4`: forms `C_4` (diameter `2`, `4` edges,
neither complete nor a tree/star). -/
def cycle4Profile : Profile (Fin 4)
  | 0 => LinkSet.ofFinset 0 {1}
  | 1 => LinkSet.ofFinset 1 {2}
  | 2 => LinkSet.ofFinset 2 {3}
  | 3 => LinkSet.ofFinset 3 {0}

private theorem cycle4_adj_succ (i : Fin 4) : (formedGraph cycle4Profile).Adj i (i + 1) := by
  rw [formedGraph_adj]
  left
  fin_cases i <;> simp [cycle4Profile]

theorem connected_cycle4Profile : (formedGraph cycle4Profile).Connected := by
  have hr0 : ∀ v : Fin 4, (formedGraph cycle4Profile).Reachable 0 v := by
    intro v
    fin_cases v
    · exact Reachable.rfl
    · exact (cycle4_adj_succ 0).reachable
    · exact (cycle4_adj_succ 0).reachable.trans (cycle4_adj_succ 1).reachable
    · exact (cycle4_adj_succ 3).symm.reachable
  exact ⟨fun u v => (hr0 u).symm.trans (hr0 v)⟩

theorem diam_cycle4Profile (u v : Fin 4) : (formedGraph cycle4Profile).dist u v ≤ 2 := by
  have hcases : v = u ∨ v = u + 1 ∨ v = (u + 1) + 1 ∨ u = v + 1 := by
    fin_cases u <;> fin_cases v <;> decide
  rcases hcases with rfl | rfl | rfl | rfl
  · simp
  · rw [dist_eq_one_iff_adj.mpr (cycle4_adj_succ u)]; omega
  · have ha := dist_eq_one_iff_adj.mpr (cycle4_adj_succ u)
    have hb := dist_eq_one_iff_adj.mpr (cycle4_adj_succ (u + 1))
    exact (connected_cycle4Profile.dist_triangle (v := u + 1)).trans (by omega)
  · rw [dist_eq_one_iff_adj.mpr (cycle4_adj_succ v).symm]; omega

/-- `C_4` is neither `⊤` nor any star `starGraph r`, yet is socially optimal at `α = 2` with
`socialCost 2 cycle4Profile = 24` (`Exercise 19.2`). -/
theorem cycle4Profile_optimal_at_two :
    IsOptimalNetwork 2 (formedGraph cycle4Profile) ∧
      IsSocialOptimum 2 cycle4Profile ∧
      socialCost 2 cycle4Profile = 24 ∧
      formedGraph cycle4Profile ≠ ⊤ ∧
      ∀ r : Fin 4, formedGraph cycle4Profile ≠ starGraph r := by
  have hopt_net : IsOptimalNetwork 2 (formedGraph cycle4Profile) :=
    isOptimalNetwork_two_iff.mpr ⟨connected_cycle4Profile, diam_cycle4Profile⟩
  have hnd : NoDoubleEdges cycle4Profile := fun u v huv hvu => by
    fin_cases u <;> fin_cases v <;> simp [cycle4Profile] at huv hvu
  have hopt_prof : IsSocialOptimum 2 cycle4Profile :=
    hnd.isSocialOptimum_iff_isOptimalNetwork.mpr hopt_net
  have hsc : socialCost 2 cycle4Profile = 24 := by
    have hopt_eq : socialCost 2 cycle4Profile = networkCost 2 (⊤ : SimpleGraph (Fin 4)) := by
      have he1 := hopt_prof completeProfile
      have he2 := (isSocialOptimum_completeProfile (V := Fin 4) (α := 2)
        (by norm_num) (by norm_num)) cycle4Profile
      have heq := le_antisymm he1 he2
      have htop_conn : (formedGraph (completeProfile : Profile (Fin 4))).Connected := by
        rw [formedGraph_completeProfile]
        exact connected_top
      rw [socialECost_eq_ofReal_of_connected (by norm_num) connected_cycle4Profile,
        socialECost_eq_ofReal_of_connected (by norm_num) htop_conn,
        ENNReal.ofReal_eq_ofReal_iff (socialCost_nonneg (by norm_num) _)
          (socialCost_nonneg (by norm_num) _)] at heq
      rwa [noDoubleEdges_completeProfile.socialCost_eq_networkCost,
        formedGraph_completeProfile] at heq
    rw [hopt_eq, networkCost_top, Fintype.card_fin, show Nat.choose 4 2 = 6 by decide]
    norm_num
  have hne_top : formedGraph cycle4Profile ≠ ⊤ := by
    intro h
    have hadj : (formedGraph cycle4Profile).Adj 0 2 := by rw [h]; decide
    rw [formedGraph_adj] at hadj
    simp [cycle4Profile] at hadj
  have hne_star : ∀ r : Fin 4, formedGraph cycle4Profile ≠ starGraph r := by
    intro r hr
    fin_cases r
    · have hadj : (formedGraph cycle4Profile).Adj 0 2 := by
        have : ¬ (starGraph (0 : Fin 4)).Adj 1 2 := by rw [starGraph_adj]; decide
        have ha : (formedGraph cycle4Profile).Adj 1 2 := cycle4_adj_succ 1
        rw [hr] at ha
        exact absurd ha this
      rw [formedGraph_adj] at hadj
      simp [cycle4Profile] at hadj
    · have ha : (formedGraph cycle4Profile).Adj 2 3 := cycle4_adj_succ 2
      rw [hr, starGraph_adj] at ha
      exact absurd ha (by decide)
    · have ha : (formedGraph cycle4Profile).Adj 0 3 := (cycle4_adj_succ 3).symm
      rw [hr, starGraph_adj] at ha
      exact absurd ha (by decide)
    · have ha : (formedGraph cycle4Profile).Adj 0 1 := cycle4_adj_succ 0
      rw [hr, starGraph_adj] at ha
      exact absurd ha (by decide)
  exact ⟨hopt_net, hopt_prof, hsc, hne_top, hne_star⟩

/-! ### 3. Internal-sponsored `P₄` (`α = 3`): suboptimal tree equilibrium (`SC = 29 > 27`) -/

/-- Internal-sponsored 4-path `0 — 1 — 2 — 3` (`1` buys `{0, 2}`, `2` buys `{3}`). -/
def internalPath4 : Profile (Fin 4)
  | 0 => ∅
  | 1 => LinkSet.ofFinset 1 {0, 2}
  | 2 => LinkSet.ofFinset 2 {3}
  | 3 => ∅

private theorem internalPath4_noDoubleEdges : NoDoubleEdges internalPath4 := fun u v huv hvu => by
  fin_cases u <;> fin_cases v <;> simp [internalPath4] at huv hvu

theorem isTree_internalPath4 : (formedGraph internalPath4).IsTree := by
  have h01 : (formedGraph internalPath4).Adj 0 1 := by
    rw [formedGraph_adj]; right; simp [internalPath4]
  have h12 : (formedGraph internalPath4).Adj 1 2 := by
    rw [formedGraph_adj]; left; simp [internalPath4]
  have h23 : (formedGraph internalPath4).Adj 2 3 := by
    rw [formedGraph_adj]; left; simp [internalPath4]
  have hr0 : ∀ v : Fin 4, (formedGraph internalPath4).Reachable 0 v := by
    intro v
    fin_cases v
    · exact Reachable.rfl
    · exact h01.reachable
    · exact h01.reachable.trans h12.reachable
    · exact (h01.reachable.trans h12.reachable).trans h23.reachable
  have hconn : (formedGraph internalPath4).Connected :=
    ⟨fun u v => (hr0 u).symm.trans (hr0 v)⟩
  rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← edgeFinset_card]
  refine ⟨hconn, ?_⟩
  have hcard : ∑ u : Fin 4, (internalPath4 u).neighbors.card = 3 := by
    rw [Fin.sum_univ_four]
    simp [internalPath4]
  rw [← ncard_edgeSet_eq_card_edgeFinset, ← internalPath4_noDoubleEdges.sum_card_neighbors_eq,
    hcard, Fintype.card_fin]

private theorem dist_internalPath4 :
    (formedGraph internalPath4).dist 0 1 = 1 ∧
      (formedGraph internalPath4).dist 1 2 = 1 ∧
      (formedGraph internalPath4).dist 2 3 = 1 ∧
      (formedGraph internalPath4).dist 0 2 = 2 ∧
      (formedGraph internalPath4).dist 1 3 = 2 ∧
      (formedGraph internalPath4).dist 0 3 = 3 := by
  let H := formedGraph internalPath4
  have hconn := isTree_internalPath4.connected
  have h01 : H.Adj 0 1 := by rw [formedGraph_adj]; right; simp [internalPath4]
  have h12 : H.Adj 1 2 := by rw [formedGraph_adj]; left; simp [internalPath4]
  have h23 : H.Adj 2 3 := by rw [formedGraph_adj]; left; simp [internalPath4]
  have hd01 : H.dist 0 1 = 1 := dist_eq_one_iff_adj.mpr h01
  have hd12 : H.dist 1 2 = 1 := dist_eq_one_iff_adj.mpr h12
  have hd23 : H.dist 2 3 = 1 := dist_eq_one_iff_adj.mpr h23
  have hd02 : H.dist 0 2 = 2 := by
    have hle : H.dist 0 2 ≤ 2 := by
      have htri := hconn.dist_triangle (u := 0) (v := 1) (w := 2)
      dsimp only [H] at hd01 hd12 ⊢; omega
    have hnadj : ¬ H.Adj 0 2 := by
      rw [formedGraph_adj]
      simp [internalPath4]
    have hge := hconn.one_lt_dist_of_ne_of_not_adj (by decide) hnadj
    dsimp only [H] at hle hge ⊢; omega
  have hd13 : H.dist 1 3 = 2 := by
    have hle : H.dist 1 3 ≤ 2 := by
      have htri := hconn.dist_triangle (u := 1) (v := 2) (w := 3)
      dsimp only [H] at hd12 hd23 ⊢; omega
    have hnadj : ¬ H.Adj 1 3 := by
      rw [formedGraph_adj]
      simp [internalPath4]
    have hge := hconn.one_lt_dist_of_ne_of_not_adj (by decide) hnadj
    dsimp only [H] at hle hge ⊢; omega
  have hd03 : H.dist 0 3 = 3 := by
    have hle : H.dist 0 3 ≤ 3 := by
      have htri := hconn.dist_triangle (u := 0) (v := 2) (w := 3)
      dsimp only [H] at hd02 hd23 ⊢; omega
    have hnadj : ¬ H.Adj 0 3 := by
      rw [formedGraph_adj]
      simp [internalPath4]
    have hge2 := hconn.one_lt_dist_of_ne_of_not_adj (by decide) hnadj
    have hne2 : H.dist 0 3 ≠ 2 := by
      intro h2
      have hed2 : H.edist 0 3 = 2 := by
        rw [← (hconn 0 3).coe_dist_eq_edist, h2]; rfl
      obtain ⟨_, -, ⟨x, hx⟩⟩ := edist_eq_two_iff.mp hed2
      rw [mem_commonNeighbors] at hx
      rcases hx with ⟨ha, hb⟩
      rw [formedGraph_adj] at ha hb
      fin_cases x <;> simp [internalPath4] at ha hb
    dsimp only [H] at hle hge2 hne2 ⊢; omega
  exact ⟨hd01, hd12, hd23, hd02, hd13, hd03⟩

private theorem dist_sum_ge_three (s' : Profile (Fin 4)) (u : Fin 4)
    (hr : ∀ v : Fin 4, (formedGraph s').Reachable u v) :
    3 ≤ ∑ v : Fin 4, ((formedGraph s').dist u v : ℝ) := by
  rw [← sum_erase_add _ _ (mem_univ u)]
  simp only [SimpleGraph.dist_self, Nat.cast_zero, add_zero]
  have hcard3 : (univ.erase u).card = 3 := by fin_cases u <;> decide
  calc (3 : ℝ) = ∑ _v ∈ univ.erase u, (1 : ℝ) := by
        rw [sum_const, hcard3, nsmul_eq_mul, mul_one]; norm_num
    _ ≤ ∑ v ∈ univ.erase u, ((formedGraph s').dist u v : ℝ) :=
        sum_le_sum fun v hv =>
          by exact_mod_cast (hr v).pos_dist_of_ne (ne_of_mem_erase hv).symm

private theorem internalPath4_leaf_cost_le {u : Fin 4} (hu : u = 0 ∨ u = 3)
    (a : LinkSet (Fin 4) u)
    (hr : ∀ v : Fin 4, (formedGraph (Function.update internalPath4 u a)).Reachable u v) :
    (6 : ℝ) ≤ playerCost 3 (Function.update internalPath4 u a) u := by
  let s' := Function.update internalPath4 u a
  rcases Nat.lt_trichotomy a.neighbors.card 1 with h0 | h1 | h2
  · have ha : a = ∅ := LinkSet.ext (Finset.card_eq_zero.mp (by omega))
    have heq : Function.update internalPath4 u a = internalPath4 := by
      ext x
      rcases hu with rfl | rfl <;> fin_cases x <;> simp [ha, internalPath4]
    rw [heq, playerCost_def]
    have hd := dist_internalPath4
    have hc : (internalPath4 u).neighbors.card = 0 := by
      rcases hu with rfl | rfl <;> simp [internalPath4]
    rw [hc, Nat.cast_zero, mul_zero, zero_add, Fin.sum_univ_four]
    rcases hu with rfl | rfl
    · simp only [SimpleGraph.dist_self, hd.1, hd.2.2.2.1, hd.2.2.2.2.2]; norm_num
    · rw [SimpleGraph.dist_comm (u := 3) (v := 0), SimpleGraph.dist_comm (u := 3) (v := 1),
        SimpleGraph.dist_comm (u := 3) (v := 2), SimpleGraph.dist_self, hd.2.2.2.2.2,
        hd.2.2.2.2.1, hd.2.2.1]
      norm_num
  · rw [playerCost_def, Function.update_self, h1, Nat.cast_one]
    let nb : Fin 4 := if u = 0 then 1 else 2
    have hsub : (formedGraph s').neighborFinset u ⊆ insert nb a.neighbors := by
      intro v hv
      rw [mem_neighborFinset] at hv
      have hvu : v ≠ u := hv.ne.symm
      rw [formedGraph_adj] at hv
      rcases hv with hva | huv
      · simp only [s', Function.update_self, LinkSet.mem_iff] at hva
        exact mem_insert_of_mem hva
      · simp only [s', Function.update_of_ne hvu] at huv
        rcases hu with rfl | rfl <;>
          (fin_cases v <;> simp [internalPath4] at huv ⊢) <;>
          simp [nb]
    have hcard_lt : ((formedGraph s').neighborFinset u).card < (univ.erase u).card := by
      have h1' : (insert nb a.neighbors).card ≤ 2 := (card_insert_le _ _).trans (by omega)
      have h2' : (univ.erase u).card = 3 := by fin_cases u <;> decide
      exact lt_of_le_of_lt ((card_le_card hsub).trans h1') (by omega)
    obtain ⟨w, hw_erase, hw_not⟩ := exists_mem_notMem_of_card_lt_card hcard_lt
    have hwu : u ≠ w := (ne_of_mem_erase hw_erase).symm
    have hnadj : ¬ (formedGraph s').Adj u w := by
      rwa [mem_neighborFinset] at hw_not
    have hw2 : (2 : ℝ) ≤ ((formedGraph s').dist u w : ℝ) := by
      exact_mod_cast (hr w).one_lt_dist_of_ne_of_not_adj hwu hnadj
    have hsum4 : (4 : ℝ) ≤ ∑ v : Fin 4, ((formedGraph s').dist u v : ℝ) := by
      rw [← sum_erase_add _ _ (mem_univ u), SimpleGraph.dist_self, Nat.cast_zero, add_zero,
        ← sum_erase_add _ _ hw_erase]
      have hcard2 : ((univ.erase u).erase w).card = 2 := by
        rw [card_erase_of_mem hw_erase]; fin_cases u <;> decide
      have hrest : (2 : ℝ) ≤ ∑ v ∈ (univ.erase u).erase w, ((formedGraph s').dist u v : ℝ) := by
        calc (2 : ℝ) = ∑ _v ∈ (univ.erase u).erase w, (1 : ℝ) := by
              rw [sum_const, hcard2, nsmul_eq_mul, mul_one]; norm_num
          _ ≤ _ := sum_le_sum fun v hv => by
              have hv' := (mem_erase.mp hv).2
              exact_mod_cast (hr v).pos_dist_of_ne (ne_of_mem_erase hv').symm
      linarith
    linarith
  · rw [playerCost_def, Function.update_self]
    have ha2 : (2 : ℝ) ≤ (a.neighbors.card : ℝ) := by exact_mod_cast h2
    have hsum := dist_sum_ge_three s' u hr
    linarith

/-- At `α = 3 > 2`, `internalPath4` is a genuine non-star tree pure Nash equilibrium whose social
cost `29` strictly exceeds `OPT = 27 = networkCost 3 (starGraph 0)`. -/
theorem isPureNash_three_internalPath4 :
    IsPureNash 3 internalPath4 ∧
      socialCost 3 internalPath4 = 29 ∧
      socialCost 3 (starCenterProfile (0 : Fin 4)) = 27 ∧
      ¬ IsOptimalNetwork 3 (formedGraph internalPath4) := by
  obtain ⟨hd01, hd12, hd23, hd02, hd13, hd03⟩ := dist_internalPath4
  have hd10 : (formedGraph internalPath4).dist 1 0 = 1 := by rw [dist_comm]; exact hd01
  have hd21 : (formedGraph internalPath4).dist 2 1 = 1 := by rw [dist_comm]; exact hd12
  have hd32 : (formedGraph internalPath4).dist 3 2 = 1 := by rw [dist_comm]; exact hd23
  have hd20 : (formedGraph internalPath4).dist 2 0 = 2 := by rw [dist_comm]; exact hd02
  have hd31 : (formedGraph internalPath4).dist 3 1 = 2 := by rw [dist_comm]; exact hd13
  have hd30 : (formedGraph internalPath4).dist 3 0 = 3 := by rw [dist_comm]; exact hd03
  have hcost0 : playerCost 3 internalPath4 0 = 6 := by
    rw [playerCost_def, Fin.sum_univ_four]
    have hc : (internalPath4 0).neighbors.card = 0 := by simp [internalPath4]
    simp only [hc, Nat.cast_zero, mul_zero, SimpleGraph.dist_self, hd01, hd02, hd03, Nat.cast_one,
      Nat.cast_ofNat]
    norm_num
  have hcost1 : playerCost 3 internalPath4 1 = 10 := by
    rw [playerCost_def, Fin.sum_univ_four]
    have hc : (internalPath4 1).neighbors.card = 2 := by
      simp only [internalPath4, LinkSet.neighbors_ofFinset]; decide
    simp only [hc, SimpleGraph.dist_self, Nat.cast_zero, hd10, hd12, hd13, Nat.cast_one,
      Nat.cast_ofNat]
    norm_num
  have hcost2 : playerCost 3 internalPath4 2 = 7 := by
    rw [playerCost_def, Fin.sum_univ_four]
    have hc : (internalPath4 2).neighbors.card = 1 := by
      simp only [internalPath4, LinkSet.neighbors_ofFinset]; decide
    simp only [hc, SimpleGraph.dist_self, Nat.cast_zero, hd20, hd21, hd23, Nat.cast_one,
      Nat.cast_ofNat]
    norm_num
  have hcost3 : playerCost 3 internalPath4 3 = 6 := by
    rw [playerCost_def, Fin.sum_univ_four]
    have hc : (internalPath4 3).neighbors.card = 0 := by simp [internalPath4]
    simp only [hc, Nat.cast_zero, mul_zero, SimpleGraph.dist_self, hd30, hd31, hd32, Nat.cast_one,
      Nat.cast_ofNat]
    norm_num
  have hsc : socialCost 3 internalPath4 = 29 := by
    rw [socialCost_def, Fin.sum_univ_four, hcost0, hcost1, hcost2, hcost3]
    norm_num
  have hstar_sc : socialCost 3 (starCenterProfile (0 : Fin 4)) = 27 := by
    rw [(noDoubleEdges_starCenterProfile (0 : Fin 4)).socialCost_eq_networkCost,
      formedGraph_starCenterProfile, networkCost_starGraph, Fintype.card_fin]
    norm_num
  have hnot_opt : ¬ IsOptimalNetwork 3 (formedGraph internalPath4) := by
    rw [isOptimalNetwork_iff_exists_starGraph_of_two_lt (by norm_num)]
    rintro ⟨r, hr⟩
    have hd_star : (formedGraph internalPath4).dist 0 3 ≤ 2 := by
      have ha : (starGraph r).dist 0 r ≤ 1 := by
        by_cases h0 : (0 : Fin 4) = r
        · subst h0; simp
        · exact (dist_eq_one_iff_adj.mpr (starGraph_center_adj' (Ne.symm h0))).le
      have hb : (starGraph r).dist r 3 ≤ 1 := by
        by_cases h3 : r = (3 : Fin 4)
        · subst h3; simp
        · exact (dist_eq_one_iff_adj.mpr (starGraph_center_adj h3)).le
      rw [hr]
      exact ((connected_starGraph r).dist_triangle (v := r)).trans (by omega)
    omega
  refine ⟨?_, hsc, hstar_sc, hnot_opt⟩
  intro u a
  let s' := Function.update internalPath4 u a
  by_cases hreach' : ∀ v : Fin 4, (formedGraph s').Reachable u v
  · rw [playerECost_eq_ofReal_of_connected (by norm_num) isTree_internalPath4.connected,
      playerECost_eq_ofReal_of_forall_reachable (by norm_num) hreach',
      ENNReal.ofReal_le_ofReal_iff (playerCost_nonneg (by norm_num) s' u)]
    rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by fin_cases u <;> simp) with
      rfl | rfl | rfl | rfl
    · -- Player 0 (baseline cost 6)
      rw [hcost0]
      exact internalPath4_leaf_cost_le (Or.inl rfl) a hreach'
    · -- Player 1 (baseline cost 10)
      rw [hcost1, playerCost_def, show s' 1 = a from Function.update_self _ _ _]
      have h0_mem : (0 : Fin 4) ∈ a.neighbors := by
        by_contra h0t
        obtain ⟨q⟩ := (hreach' 0).symm
        cases q with
        | @cons _ w _ hadj _ =>
          rw [formedGraph_adj] at hadj
          fin_cases w <;> simp [s', internalPath4, h0t] at hadj
      have h23_mem : (2 : Fin 4) ∈ a.neighbors ∨ (3 : Fin 4) ∈ a.neighbors := by
        by_contra hnot
        push Not at hnot
        have hclosed : ∀ x y : Fin 4, (formedGraph s').Adj x y →
            x ∈ ({0, 1} : Finset (Fin 4)) → y ∈ ({0, 1} : Finset (Fin 4)) := by
          intro x y hxy hx
          rw [formedGraph_adj] at hxy
          fin_cases x <;> fin_cases y <;>
            simp [s', internalPath4, hnot.1, hnot.2] at hxy hx ⊢
        have hwalk : ∀ x y : Fin 4, (formedGraph s').Walk x y →
            x ∈ ({0, 1} : Finset (Fin 4)) → y ∈ ({0, 1} : Finset (Fin 4)) := by
          intro x y q
          induction q with
          | nil => exact id
          | @cons _ _ _ hxy _ ih => exact fun hx => ih (hclosed _ _ hxy hx)
        obtain ⟨q⟩ := hreach' 2
        exact absurd (hwalk 1 2 q (by decide)) (by decide)
      have ha_ge2 : 2 ≤ a.neighbors.card := by
        rcases h23_mem with h2m | h3m
        · exact one_lt_card.mpr ⟨0, h0_mem, 2, h2m, by decide⟩
        · exact one_lt_card.mpr ⟨0, h0_mem, 3, h3m, by decide⟩
      rcases lt_or_eq_of_le ha_ge2 with ha3 | ha2
      · have ha3R : (3 : ℝ) ≤ (a.neighbors.card : ℝ) := by exact_mod_cast ha3
        have hsum := dist_sum_ge_three s' 1 hreach'
        linarith
      · obtain ⟨v, hv_in, hvt⟩ :=
          exists_mem_notMem_of_card_lt_card (by rw [← ha2]; decide : a.neighbors.card <
            ({0, 2, 3} : Finset (Fin 4)).card)
        have h1v_ne : (1 : Fin 4) ≠ v := by fin_cases v <;> simp at hv_in ⊢
        have hnadj : ¬ (formedGraph s').Adj 1 v := by
          rw [formedGraph_adj]
          rintro (hv1 | h1v)
          · simp only [s', Function.update_self, LinkSet.mem_iff] at hv1
            exact hvt hv1
          · simp only [s', Function.update_of_ne h1v_ne.symm] at h1v
            fin_cases v <;> simp [internalPath4] at h1v
        have hv_ge2 : (2 : ℝ) ≤ ((formedGraph s').dist 1 v : ℝ) := by
          exact_mod_cast (hreach' v).one_lt_dist_of_ne_of_not_adj h1v_ne hnadj
        have hd0' : (1 : ℝ) ≤ ((formedGraph s').dist 1 0 : ℝ) := by
          exact_mod_cast (hreach' 0).pos_dist_of_ne (by decide)
        have hd2' : (1 : ℝ) ≤ ((formedGraph s').dist 1 2 : ℝ) := by
          exact_mod_cast (hreach' 2).pos_dist_of_ne (by decide)
        have hd3' : (1 : ℝ) ≤ ((formedGraph s').dist 1 3 : ℝ) := by
          exact_mod_cast (hreach' 3).pos_dist_of_ne (by decide)
        have hsum4 : 4 ≤ ∑ x : Fin 4, ((formedGraph s').dist 1 x : ℝ) := by
          rw [Fin.sum_univ_four]
          simp only [SimpleGraph.dist_self, Nat.cast_zero]
          rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by fin_cases v <;> simp) with
            rfl | rfl | rfl | rfl
          · exact absurd h0_mem hvt
          · exact absurd rfl h1v_ne
          · linarith
          · linarith
        have ha2R : (a.neighbors.card : ℝ) = 2 := by exact_mod_cast ha2.symm
        rw [ha2R]
        linarith
    · -- Player 2 (baseline cost 7)
      have h3_mem : (3 : Fin 4) ∈ a.neighbors := by
        by_contra h3t
        obtain ⟨q⟩ := (hreach' 3).symm
        cases q with
        | @cons _ w _ hadj _ =>
          rw [formedGraph_adj] at hadj
          fin_cases w <;> simp [s', internalPath4, h3t] at hadj
      have ha_ge1 : 1 ≤ a.neighbors.card := card_pos.mpr ⟨3, h3_mem⟩
      rcases lt_or_eq_of_le ha_ge1 with ha2 | ha1
      · rw [hcost2, playerCost_def, show s' 2 = a from Function.update_self _ _ _]
        have ha2R : (2 : ℝ) ≤ (a.neighbors.card : ℝ) := by exact_mod_cast ha2
        have hsum := dist_sum_ge_three s' 2 hreach'
        linarith
      · have ha_eq : a = internalPath4 2 := by
          obtain ⟨w, hw⟩ := card_eq_one.mp ha1.symm
          rw [hw] at h3_mem
          have hw3 : w = 3 := (mem_singleton.mp h3_mem).symm
          subst hw3
          exact LinkSet.ext (by rw [hw]; simp [internalPath4])
        have heq : Function.update internalPath4 2 a = internalPath4 := by
          ext x; fin_cases x <;> simp [ha_eq, internalPath4]
        simp only [s', heq, le_refl]
    · -- Player 3 (baseline cost 6)
      rw [hcost3]
      exact internalPath4_leaf_cost_le (Or.inr rfl) a hreach'
  · rw [playerECost_eq_top_iff.mpr (not_forall.mp hreach')]
    exact le_top

/-- Concrete instantiation of tree `PoA ≤ 5`, tightened Lemma 19.4 (`3d - 1 = 8`), and
`PoA ≤ 3√(4α + 1) - 1 ≤ 6√α + 2` on `internalPath4` at `α = 3`. -/
theorem fin4_internalPath4_poa_bounds :
    socialCost 3 internalPath4 ≤ 5 * socialCost 3 (starCenterProfile (0 : Fin 4)) ∧
      socialCost 3 internalPath4 ≤
        (3 * ((formedGraph internalPath4).diam : ℝ) - 1) *
          socialCost 3 (starCenterProfile (0 : Fin 4)) ∧
      socialECost 3 internalPath4 ≤
        ENNReal.ofReal (3 * Real.sqrt (4 * 3 + 1) - 1) *
          socialECost 3 (starCenterProfile (0 : Fin 4)) ∧
      socialECost 3 internalPath4 ≤
        ENNReal.ofReal (6 * Real.sqrt 3 + 2) *
          socialECost 3 (starCenterProfile (0 : Fin 4)) := by
  have hs := isPureNash_three_internalPath4.1
  have hstar_conn : (formedGraph (starCenterProfile (0 : Fin 4))).Connected := by
    rw [formedGraph_starCenterProfile]
    exact connected_starGraph 0
  exact ⟨hs.socialCost_le_five_mul_of_isTree (by norm_num) isTree_internalPath4 hstar_conn,
    hs.socialCost_le_three_diam_sub_one_mul (by norm_num) hstar_conn,
    hs.socialECost_le_three_mul_sqrt_four_add_one_sub_one_mul (by norm_num) _,
    hs.socialECost_le_six_mul_sqrt_add_two_mul (by norm_num) _⟩

end CslibFrontierTests.GameTheory.LocalConnectionBounds
