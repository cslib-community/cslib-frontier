/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.NetworkFormation.LocalConnection
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests and boundary witnesses for the local connection game

Ordinary `module` client exercising `Cslib.GameTheory.LocalConnection` through its public API:

* **Disconnection boundary (`Fin 3`):** the empty profile `fun _ => ∅` has
  `SimpleGraph.dist 0 1 = 0` under Mathlib's junk convention, yet `socialECost α = ⊤`, so it is
  neither a pure Nash equilibrium nor socially optimal for any `α`.
* **Sharpness of `|V| ≥ 3` in `isStableNetwork_top_iff`:** on `Fin 2`, `⊤ = starGraph 0` is stable
  at `α = 5 > 1`, whereas on `Fin 3` it is unstable.
* **Star and clique equilibria and optima (`Fin 4`, `α = 1` and `α = 3`):** both
  `starCenterProfile` and `starLeafProfile` are pure Nash equilibria for `α ≥ 1`, and
  `networkCost_one_starGraph_div_top` evaluates to `7 / 6 < 4 / 3` on `Fin 4`.
* **Price of stability strictly above `1` (`Fin 3`, `α = 3 / 2`):** every pure Nash equilibrium on
  `Fin 3` at `α = 3 / 2` has real social cost `11`, strictly exceeding the optimal complete-graph
  cost `21 / 2` (exact price of stability `22 / 21`).
* **Odd-diameter sharpness on `P₄` (`Fin 4`, `α = 2`):** `pathFourProfile` (`0 — 1 — 2 — 3`, with
  `1` sponsoring `{0, 2}` and `2` sponsoring `{3}`) is a pure Nash equilibrium of diameter `3`,
  witnessing `2 * √2 < 3 = √(4 · 2 + 1)` (tightness of `IsPureNash.diam_le_sqrt_four_mul_add_one`
  and the odd-parity `+ 1` term omitted in [TardosWexler2007], Theorem 19.5).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.LocalConnection

open Finset SimpleGraph Cslib.GameTheory.LocalConnection
open scoped ENNReal

/-! ### 1. Disconnection boundary on `Fin 3` -/

/-- The empty strategy profile on `Fin 3`, forming `⊥`. -/
abbrev emptyThree : Profile (Fin 3) :=
  fun _ => ∅

/-- Mathlib's `SimpleGraph.dist` returns `0` on unreachable vertices of `emptyThree`. -/
theorem dist_emptyThree_zero : (formedGraph emptyThree).dist 0 1 = 0 := by
  simp only [formedGraph_empty, dist_bot]

/-- `socialECost` evaluates to `⊤` on the disconnected profile `emptyThree`. -/
theorem socialECost_emptyThree_eq_top (α : ℝ) : socialECost α emptyThree = ⊤ := by
  rw [socialECost_eq_top_iff]
  simp only [formedGraph_empty, not_connected_bot, not_false_eq_true]

/-- For every `α : ℝ` (in particular `α > 0`), the empty profile on `Fin 3` is not a pure Nash
equilibrium. -/
theorem not_isPureNash_emptyThree (α : ℝ) : ¬ IsPureNash α emptyThree :=
  fun hs => hs.socialECost_ne_top (socialECost_emptyThree_eq_top α)

/-- For every `α : ℝ`, the empty profile on `Fin 3` is not socially optimal. -/
theorem not_isSocialOptimum_emptyThree (α : ℝ) : ¬ IsSocialOptimum α emptyThree := by
  intro hopt
  have hle := hopt (starCenterProfile 0)
  rw [socialECost_emptyThree_eq_top α, top_le_iff, socialECost_eq_top_iff,
    formedGraph_starCenterProfile] at hle
  exact hle (connected_starGraph 0)

/-! ### 2. Sharpness of `3 ≤ Fintype.card V` for clique stability -/

/-- On `Fin 2`, `⊤` coincides with `starGraph 0` and remains stable at `α = 5 > 1`. -/
theorem isStableNetwork_top_fin2_five : IsStableNetwork 5 (⊤ : SimpleGraph (Fin 2)) := by
  have htop_eq : (⊤ : SimpleGraph (Fin 2)) = starGraph 0 := by
    ext u v
    fin_cases u <;> fin_cases v <;> simp
  rw [htop_eq]
  exact isStableNetwork_starGraph (by norm_num) 0

/-- On `Fin 3`, `⊤` is not stable at `α = 5 > 1`. -/
theorem not_isStableNetwork_top_fin3_five : ¬ IsStableNetwork 5 (⊤ : SimpleGraph (Fin 3)) := by
  rw [isStableNetwork_top_iff (by norm_num) (by decide)]
  norm_num

/-! ### 3. Star and clique equilibria at `α = 1`, `α = 3 / 2`, and `α = 3` -/

example : IsPureNash 1 (starCenterProfile (0 : Fin 4)) :=
  isPureNash_starCenterProfile (by norm_num) 0

example : IsPureNash 1 (starLeafProfile (0 : Fin 4)) :=
  isPureNash_starLeafProfile (by norm_num) 0

example : IsPureNash 1 (completeProfile : Profile (Fin 4)) :=
  isPureNash_completeProfile (by norm_num) (by norm_num)

example : IsSocialOptimum 3 (starCenterProfile (0 : Fin 4)) :=
  isSocialOptimum_starCenterProfile (by norm_num) 0

example :
    networkCost 1 (starGraph (0 : Fin 4)) / networkCost 1 (⊤ : SimpleGraph (Fin 4)) = 7 / 6 := by
  rw [networkCost_one_starGraph_div_top (by decide) 0]
  simp only [Fintype.card_fin]
  norm_num

/-! ### 4. Strict `PoS > 1` witness on `Fin 3` for `1 < α < 2` (`α = 3 / 2`) -/

/-- On `Fin 3` at `α = 3 / 2`, the optimal complete-graph profile has social cost `21 / 2`. -/
theorem socialCost_completeProfile_fin3 :
    socialCost (3 / 2) (completeProfile : Profile (Fin 3)) = 21 / 2 := by
  rw [noDoubleEdges_completeProfile.socialCost_eq_networkCost, formedGraph_completeProfile,
    networkCost_top]
  simp only [Fintype.card_fin]
  norm_num

/-- On `Fin 3` at `α = 3 / 2`, **every** pure Nash equilibrium `s` has social cost `11`, strictly
exceeding the optimal cost `21 / 2` (exact price of stability `22 / 21 > 1`). -/
theorem socialCost_eq_eleven_of_isPureNash_fin3 {s : Profile (Fin 3)}
    (hs : IsPureNash (3 / 2) s) :
    socialCost (3 / 2) s = 11 := by
  let G := formedGraph s
  have hc : G.Connected := hs.connected
  have hm_ge : 2 ≤ G.edgeSet.ncard := by
    have h1 := hc.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_coe_set_eq] at h1
    omega
  have hm_le : G.edgeSet.ncard ≤ 3 := by
    rw [ncard_edgeSet_eq_card_edgeFinset]
    exact G.card_edgeFinset_le_card_choose_two.trans (by decide)
  have hm_ne3 : G.edgeSet.ncard ≠ 3 := by
    intro h3
    rw [ncard_edgeSet_eq_card_edgeFinset] at h3
    have htop_card : #(⊤ : SimpleGraph (Fin 3)).edgeFinset = 3 := by
      rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
      decide
    have hG_top : G = ⊤ := by
      rw [← edgeFinset_inj]
      exact eq_of_subset_of_card_le (edgeFinset_mono le_top) (by omega)
    have hstab : IsStableNetwork (3 / 2) (⊤ : SimpleGraph (Fin 3)) := ⟨s, hG_top, hs⟩
    have hle1 := (isStableNetwork_top_iff (by norm_num) (by decide)).mp hstab
    linarith
  have hm2 : G.edgeSet.ncard = 2 := by omega
  have hlow := two_mul_card_mul_le_sum_dist_add_two_mul_edges hc.preconnected
  rw [Fintype.card_fin, hm2] at hlow
  have hup : (∑ u : Fin 3, ∑ v : Fin 3, G.dist u v) + 2 * 2 ≤ 12 := by
    have hadj_sum : 2 * 2 = ∑ u : Fin 3, ∑ v : Fin 3, if G.Adj u v then 1 else 0 := by
      have hdeg := G.sum_degrees_eq_twice_card_edges
      rw [← ncard_edgeSet_eq_card_edgeFinset, hm2] at hdeg
      rw [← hdeg]
      refine sum_congr rfl fun u _ => ?_
      rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]
    have h12 : (12 : ℕ) = ∑ u : Fin 3, ∑ v : Fin 3, if u ≠ v then 2 else 0 := by decide
    rw [hadj_sum, h12, ← sum_add_distrib]
    refine sum_le_sum fun u _ => ?_
    rw [← sum_add_distrib]
    refine sum_le_sum fun v _ => ?_
    by_cases huv : u = v
    · subst huv
      simp only [SimpleGraph.dist_self, SimpleGraph.irrefl, ↓reduceIte, ne_eq, not_true_eq_false,
        le_refl]
    · simp only [ne_eq, huv, not_false_eq_true, ↓reduceIte]
      by_cases hadj : G.Adj u v
      · simp only [hadj, ↓reduceIte, dist_eq_one_iff_adj.mpr hadj, le_refl]
      · simp only [hadj, ↓reduceIte, add_zero]
        obtain ⟨p, hp, hplen⟩ := (hc u v).exists_path_of_dist
        have hlt : p.length < 3 := by simpa only [Fintype.card_fin] using hp.length_lt
        omega
  have hdist8 : (∑ u : Fin 3, ∑ v : Fin 3, G.dist u v) = 8 := by omega
  rw [hs.socialCost_eq_networkCost (by norm_num), networkCost_def, hm2]
  have hcast : (∑ u : Fin 3, ∑ v : Fin 3, (G.dist u v : ℝ)) =
      ((∑ u : Fin 3, ∑ v : Fin 3, G.dist u v : ℕ) : ℝ) := by push_cast; rfl
  rw [hcast, hdist8]
  norm_num

/-! ### 5. `P₄` at `α = 2`: diameter `3 > 2√2` pure NE (`Theorem 19.5` parity witness) -/

/-- Path profile `0 — 1 — 2 — 3` on `Fin 4`: vertex `1` sponsors `{0, 2}` and vertex `2` sponsors
`{3}`. -/
abbrev pathFourProfile : Profile (Fin 4)
  | 0 => ∅
  | 1 => LinkSet.ofFinset 1 {0, 2}
  | 2 => LinkSet.ofFinset 2 {3}
  | 3 => ∅

/-- `pathFourProfile` forms a path of diameter `3`. -/
theorem diam_pathFourProfile : (formedGraph pathFourProfile).diam = 3 := by
  let G := formedGraph pathFourProfile
  have h01 : G.Adj 0 1 := by simp [G]
  have h12 : G.Adj 1 2 := by simp [G]
  have h23 : G.Adj 2 3 := by simp [G]
  have hconn : G.Connected := by
    rw [connected_iff]
    refine ⟨fun u v => ?_, ⟨0⟩⟩
    have hr0 : ∀ x : Fin 4, G.Reachable 0 x := by
      intro x
      fin_cases x
      · exact Reachable.rfl
      · exact h01.reachable
      · exact h01.reachable.trans h12.reachable
      · exact h01.reachable.trans (h12.reachable.trans h23.reachable)
    exact (hr0 u).symm.trans (hr0 v)
  have hed_le : G.ediam ≤ 3 := by
    rw [ediam_le_iff]
    have h01' : G.edist 0 1 ≤ 1 := edist_le h01.toWalk
    have h12' : G.edist 1 2 ≤ 1 := edist_le h12.toWalk
    have h23' : G.edist 2 3 ≤ 1 := edist_le h23.toWalk
    have h02' : G.edist 0 2 ≤ 2 := (G.edist_triangle (v := 1)).trans (by
      calc G.edist 0 1 + G.edist 1 2 ≤ 1 + 1 := add_le_add h01' h12'
        _ = 2 := rfl)
    have h13' : G.edist 1 3 ≤ 2 := (G.edist_triangle (v := 2)).trans (by
      calc G.edist 1 2 + G.edist 2 3 ≤ 1 + 1 := add_le_add h12' h23'
        _ = 2 := rfl)
    have h03' : G.edist 0 3 ≤ 3 := (G.edist_triangle (v := 2)).trans (by
      calc G.edist 0 2 + G.edist 2 3 ≤ 2 + 1 := add_le_add h02' h23'
        _ = 3 := rfl)
    intro u v
    rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by fin_cases u <;> simp) with
      rfl | rfl | rfl | rfl <;>
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by fin_cases v <;> simp) with
      rfl | rfl | rfl | rfl
    all_goals first
      | simp only [SimpleGraph.edist_self, zero_le]
      | exact h01'.trans (by decide)
      | (rw [SimpleGraph.edist_comm]; exact h01'.trans (by decide))
      | exact h12'.trans (by decide)
      | (rw [SimpleGraph.edist_comm]; exact h12'.trans (by decide))
      | exact h23'.trans (by decide)
      | (rw [SimpleGraph.edist_comm]; exact h23'.trans (by decide))
      | exact h02'.trans (by decide)
      | (rw [SimpleGraph.edist_comm]; exact h02'.trans (by decide))
      | exact h13'.trans (by decide)
      | (rw [SimpleGraph.edist_comm]; exact h13'.trans (by decide))
      | exact h03'
      | (rw [SimpleGraph.edist_comm]; exact h03')
  have hed_03 : 2 < G.edist 0 3 := by
    rw [two_lt_edist_iff]
    refine ⟨by decide, by simp [G], ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rw [mem_commonNeighbors] at hz
    rcases (show z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 by fin_cases z <;> simp) with
      rfl | rfl | rfl | rfl <;> simp [G] at hz
  have hd_ge : 3 ≤ G.diam := by
    have hediam_ne : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
    have hlt : 2 < G.dist 0 3 := by
      rw [← (hconn 0 3).coe_dist_eq_edist] at hed_03
      exact_mod_cast hed_03
    have hle_d : G.dist 0 3 ≤ G.diam := dist_le_diam hediam_ne
    omega
  have hd_le : G.diam ≤ 3 := by
    rw [SimpleGraph.diam]
    exact ENat.toNat_le_of_le_natCast hed_le
  change G.diam = 3
  omega

/-- On `pathFourProfile`, `2 * √2 < diam` (witnessing the odd-diameter `+ 1` parity gap in
[TardosWexler2007], Theorem 19.5), while `diam = √(4 · 2 + 1)` with equality. -/
theorem two_mul_sqrt_two_lt_diam_pathFourProfile :
    2 * Real.sqrt 2 < ((formedGraph pathFourProfile).diam : ℝ) := by
  rw [diam_pathFourProfile, Nat.cast_ofNat]
  have hlt_sq : (2 * Real.sqrt 2) ^ 2 < (3 : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  nlinarith [Real.sqrt_nonneg 2]

theorem diam_pathFourProfile_eq_sqrt_nine :
    ((formedGraph pathFourProfile).diam : ℝ) = Real.sqrt (4 * 2 + 1) := by
  rw [diam_pathFourProfile]
  have h9 : (4 * 2 + 1 : ℝ) = (3 : ℝ) ^ 2 := by norm_num
  rw [h9, Real.sqrt_sq (by norm_num)]
  norm_num

/-- `pathFourProfile` is a pure Nash equilibrium at `α = 2`: on any connected `4`-vertex graph `H`,
`∑ v, H.dist u v ≥ 6 - H.degree u`, matching each player's equilibrium cost (`6, 8, 6, 6`). -/
theorem isPureNash_two_pathFourProfile : IsPureNash 2 pathFourProfile := by
  have hdeg_dist : ∀ (H : SimpleGraph (Fin 4)) [DecidableRel H.Adj] (u : Fin 4),
      (∀ v, H.Reachable u v) → 6 - H.degree u ≤ ∑ v : Fin 4, H.dist u v := by
    intro H _ u hr
    have hlow : ∑ v ∈ univ.erase u, (if H.Adj u v then 1 else 2) ≤
        ∑ v ∈ univ.erase u, H.dist u v := by
      refine sum_le_sum fun v hv => ?_
      have hvu : u ≠ v := (mem_erase.mp hv).1.symm
      by_cases hadj : H.Adj u v
      · simp only [hadj, ↓reduceIte, dist_eq_one_iff_adj.mpr hadj, le_refl]
      · simp only [hadj, ↓reduceIte]
        exact (hr v).one_lt_dist_of_ne_of_not_adj hvu hadj
    rw [← sum_erase_add _ _ (mem_univ u)]
    simp only [SimpleGraph.dist_self, add_zero]
    have hdeg_le : H.degree u ≤ 3 := by
      have := H.degree_lt_card_verts u
      rw [Fintype.card_fin] at this
      omega
    have heval : (∑ v ∈ univ.erase u, if H.Adj u v then 1 else 2) = 6 - H.degree u := by
      have h1 : ∀ v ∈ univ.erase u,
          (if H.Adj u v then 1 else 2) + (if H.Adj u v then 1 else 0) = 2 :=
        fun v _ => by split_ifs <;> rfl
      have hsum2 : (∑ v ∈ univ.erase u, (if H.Adj u v then 1 else 2)) +
          (∑ v ∈ univ.erase u, if H.Adj u v then 1 else 0) = 6 := by
        rw [← sum_add_distrib, sum_congr rfl h1, sum_const, card_erase_of_mem (mem_univ u),
          card_univ, Fintype.card_fin]
        rfl
      have hdeg_eq : (∑ v ∈ univ.erase u, if H.Adj u v then 1 else 0) = H.degree u := by
        rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]
        rw [← sum_erase_add _ _ (mem_univ u)]
        simp only [SimpleGraph.irrefl, ↓reduceIte, add_zero]
      omega
    omega
  have hconn_base : (formedGraph pathFourProfile).Connected := by
    have hd3 := diam_pathFourProfile
    exact connected_iff_diam_ne_zero.mpr (by omega)
  have hdist_base : ∀ u : Fin 4, (∑ v : Fin 4, (formedGraph pathFourProfile).dist u v) =
      if u = 1 ∨ u = 2 then 4 else 6 := by
    have h01 : (formedGraph pathFourProfile).dist 0 1 = 1 :=
      dist_eq_one_iff_adj.mpr (by simp)
    have h10 : (formedGraph pathFourProfile).dist 1 0 = 1 :=
      dist_eq_one_iff_adj.mpr (by simp)
    have h12 : (formedGraph pathFourProfile).dist 1 2 = 1 :=
      dist_eq_one_iff_adj.mpr (by simp)
    have h21 : (formedGraph pathFourProfile).dist 2 1 = 1 :=
      dist_eq_one_iff_adj.mpr (by simp)
    have h23 : (formedGraph pathFourProfile).dist 2 3 = 1 :=
      dist_eq_one_iff_adj.mpr (by simp)
    have h32 : (formedGraph pathFourProfile).dist 3 2 = 1 :=
      dist_eq_one_iff_adj.mpr (by simp)
    have hd02 : (formedGraph pathFourProfile).dist 0 2 = 2 := by
      have hed : (formedGraph pathFourProfile).edist 0 2 = 2 := by
        rw [edist_eq_two_iff]
        refine ⟨by decide, by simp, ⟨1, ?_⟩⟩
        rw [mem_commonNeighbors]
        exact ⟨by simp, by simp⟩
      rw [SimpleGraph.dist, hed]; rfl
    have hd20 : (formedGraph pathFourProfile).dist 2 0 = 2 := by
      rw [SimpleGraph.dist_comm]; exact hd02
    have hd13 : (formedGraph pathFourProfile).dist 1 3 = 2 := by
      have hed : (formedGraph pathFourProfile).edist 1 3 = 2 := by
        rw [edist_eq_two_iff]
        refine ⟨by decide, by simp, ⟨2, ?_⟩⟩
        rw [mem_commonNeighbors]
        exact ⟨by simp, by simp⟩
      rw [SimpleGraph.dist, hed]; rfl
    have hd31 : (formedGraph pathFourProfile).dist 3 1 = 2 := by
      rw [SimpleGraph.dist_comm]; exact hd13
    have hd03 : (formedGraph pathFourProfile).dist 0 3 = 3 := by
      have hle : (formedGraph pathFourProfile).dist 0 3 ≤ 3 := by
        simpa only [diam_pathFourProfile] using
          dist_le_diam (connected_iff_ediam_ne_top.mp hconn_base) (u := 0) (v := 3)
      have hgt : 2 < (formedGraph pathFourProfile).dist 0 3 := by
        have hed : 2 < (formedGraph pathFourProfile).edist 0 3 := by
          rw [two_lt_edist_iff]
          refine ⟨by decide, by simp, ?_⟩
          rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          rw [mem_commonNeighbors] at hz
          rcases (show z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 by fin_cases z <;> simp) with
            rfl | rfl | rfl | rfl <;> simp at hz
        rw [← (hconn_base 0 3).coe_dist_eq_edist] at hed
        exact_mod_cast hed
      omega
    have hd30 : (formedGraph pathFourProfile).dist 3 0 = 3 := by
      rw [SimpleGraph.dist_comm]; exact hd03
    intro u
    rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by fin_cases u <;> simp) with
      rfl | rfl | rfl | rfl
    · rw [Fin.sum_univ_four, SimpleGraph.dist_self, h01, hd02, hd03]; decide
    · rw [Fin.sum_univ_four, h10, SimpleGraph.dist_self, h12, hd13]; decide
    · rw [Fin.sum_univ_four, hd20, h21, SimpleGraph.dist_self, h23]; decide
    · rw [Fin.sum_univ_four, hd30, hd31, h32, SimpleGraph.dist_self]; decide
  intro u a
  let s' := Function.update pathFourProfile u a
  by_cases htop : playerECost 2 s' u = ⊤
  · rw [htop]; exact le_top
  · have hr' : ∀ v, (formedGraph s').Reachable u v := playerECost_ne_top_iff.mp htop
    rw [playerECost_eq_ofReal_of_connected (by norm_num) hconn_base u,
      playerECost_eq_ofReal_of_forall_reachable (by norm_num) hr',
      ENNReal.ofReal_le_ofReal_iff (playerCost_nonneg (by norm_num) s' u)]
    have hlow_dist := hdeg_dist (formedGraph s') u hr'
    have hlow_real : ((6 - (formedGraph s').degree u : ℕ) : ℝ) ≤
        ∑ v : Fin 4, ((formedGraph s').dist u v : ℝ) := by exact_mod_cast hlow_dist
    have hbase_real : (∑ v : Fin 4, ((formedGraph pathFourProfile).dist u v : ℝ)) =
        ((if u = 1 ∨ u = 2 then 4 else 6 : ℕ) : ℝ) := by exact_mod_cast hdist_base u
    rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by fin_cases u <;> simp) with
      rfl | rfl | rfl | rfl
    · -- Player 0: original cost 6; if `a = ∅` unchanged, else `#a ≥ 1` and `deg ≤ #a + 1`.
      by_cases ha0 : a.neighbors = ∅
      · have ha_eq : a = pathFourProfile 0 := LinkSet.ext ha0
        have hs'_eq : s' = pathFourProfile := by
          simpa only [s', ha_eq] using Function.update_eq_self (0 : Fin 4) pathFourProfile
        rw [hs'_eq]
      · have ha_pos : 1 ≤ a.neighbors.card := card_pos.mpr (nonempty_iff_ne_empty.mpr ha0)
        have hdeg : (formedGraph s').degree 0 ≤ a.neighbors.card + 1 := by
          rw [← card_neighborFinset_eq_degree]
          have hsub : (formedGraph s').neighborFinset 0 ⊆ insert 1 a.neighbors := by
            intro v hv
            rw [mem_neighborFinset] at hv
            have hv0 : v ≠ 0 := hv.ne.symm
            rw [formedGraph_adj] at hv
            simp only [s', Function.update_self, Function.update_of_ne hv0] at hv
            rcases hv with hva | h0v
            · exact mem_insert_of_mem hva
            · rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by fin_cases v <;> simp) with
                rfl | rfl | rfl | rfl
              · exact False.elim (hv0 rfl)
              · exact mem_insert_self 1 _
              · exact False.elim (by simp at h0v)
              · exact False.elim (by simp at h0v)
          exact (card_le_card hsub).trans (card_insert_le _ _)
        rw [playerCost_def, playerCost_def, hbase_real]
        have hc0 : (pathFourProfile 0).neighbors.card = 0 := by simp
        have hite0 : (if (0 : Fin 4) = 1 ∨ (0 : Fin 4) = 2 then 4 else 6) = 6 := by decide
        rw [hc0, hite0]
        simp only [Nat.cast_zero, mul_zero, zero_add, Nat.cast_ofNat, s', Function.update_self]
        have : (6 : ℝ) ≤
            2 * (a.neighbors.card : ℝ) + ((6 - (formedGraph s').degree 0 : ℕ) : ℝ) := by
          have : 6 ≤ 2 * a.neighbors.card + (6 - (formedGraph s').degree 0) := by omega
          exact_mod_cast this
        linarith
    · -- Player 1: cost `4 + 4 = 8`; no other vertex sponsors links to `1`, and `#a ≥ 2`.
      have h0_mem : (0 : Fin 4) ∈ a.neighbors := by
        obtain ⟨q⟩ := (hr' 0).symm
        cases q with
        | @cons _ w _ hadj_0w _ =>
          have hw0 : w ≠ 0 := hadj_0w.ne.symm
          rw [formedGraph_adj] at hadj_0w
          rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by fin_cases w <;> simp) with
            rfl | rfl | rfl | rfl
          · exact False.elim (hw0 rfl)
          · simp only [s', Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
              Function.update_self] at hadj_0w
            exact LinkSet.mem_iff.mp (hadj_0w.resolve_left (by simp))
          · simp only [s', Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
              Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)] at hadj_0w
            exact False.elim (by simp at hadj_0w)
          · simp only [s', Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
              Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1)] at hadj_0w
            exact False.elim (by simp at hadj_0w)
      have h23_mem : (2 : Fin 4) ∈ a.neighbors ∨ (3 : Fin 4) ∈ a.neighbors := by
        let S01 : Finset (Fin 4) := {0, 1}
        have h0_in : (1 : Fin 4) ∈ S01 := by decide
        have h2_out : (2 : Fin 4) ∉ S01 := by decide
        obtain ⟨q⟩ := hr' 2
        by_contra! hnone
        have hall : ∀ (x y : Fin 4), (formedGraph s').Walk x y → x ∈ S01 → y ∈ S01 := by
          intro x y w hx
          induction w with
          | nil => exact hx
          | @cons x y z hadj _ ih =>
            refine ih ?_
            by_contra hy_out
            rw [formedGraph_adj] at hadj
            rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 by fin_cases x <;> simp) with
              rfl | rfl | rfl | rfl <;>
            rcases (show y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 by fin_cases y <;> simp) with
              rfl | rfl | rfl | rfl
            all_goals first
              | exact False.elim (by revert hx; decide)
              | exact False.elim (by revert hy_out; decide)
              | (simp only [s', Function.update_self,
                  Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
                  Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
                  Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1),
                  LinkSet.mem_iff, hnone.1, hnone.2, false_or] at hadj;
                 exact False.elim (by simp at hadj))
        exact h2_out (hall 1 2 q h0_in)
      have ha2 : 2 ≤ a.neighbors.card := by
        rcases h23_mem with h2 | h3
        · exact card_le_card (show ({0, 2} : Finset (Fin 4)) ⊆ a.neighbors by
            intro x hx; simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption)
        · exact card_le_card (show ({0, 3} : Finset (Fin 4)) ⊆ a.neighbors by
            intro x hx; simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption)
      have hdeg : (formedGraph s').degree 1 ≤ a.neighbors.card := by
        rw [← card_neighborFinset_eq_degree]
        refine card_le_card fun v hv => ?_
        rw [mem_neighborFinset] at hv
        have hv1 : v ≠ 1 := hv.ne.symm
        rw [formedGraph_adj] at hv
        simp only [s', Function.update_self, Function.update_of_ne hv1] at hv
        rcases hv with hva | h1v
        · exact hva
        · rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by fin_cases v <;> simp) with
            rfl | rfl | rfl | rfl
          · exact False.elim (by simp at h1v)
          · exact False.elim (hv1 rfl)
          · exact False.elim (by simp at h1v)
          · exact False.elim (by simp at h1v)
      rw [playerCost_def, playerCost_def, hbase_real]
      have hc1 : (pathFourProfile 1).neighbors.card = 2 := by
        rw [LinkSet.neighbors_ofFinset]; decide
      have hite1 : (if (1 : Fin 4) = 1 ∨ (1 : Fin 4) = 2 then 4 else 6) = 4 := by decide
      rw [hc1, hite1]
      simp only [Nat.cast_ofNat, s', Function.update_self]
      have : (8 : ℝ) ≤
          2 * (a.neighbors.card : ℝ) + ((6 - (formedGraph s').degree 1 : ℕ) : ℝ) := by
        have : 8 ≤ 2 * a.neighbors.card + (6 - (formedGraph s').degree 1) := by omega
        exact_mod_cast this
      linarith
    · -- Player 2: original cost `2 + 4 = 6`; `3 ∈ a` (`#a ≥ 1`) and `deg ≤ #a + 1`.
      have h3_mem : (3 : Fin 4) ∈ a.neighbors := by
        obtain ⟨q⟩ := (hr' 3).symm
        cases q with
        | @cons _ w _ hadj_3w _ =>
          have hw3 : w ≠ 3 := hadj_3w.ne.symm
          rw [formedGraph_adj] at hadj_3w
          rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by fin_cases w <;> simp) with
            rfl | rfl | rfl | rfl
          · simp only [s', Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2),
              Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2)] at hadj_3w
            exact False.elim (by simp at hadj_3w)
          · simp only [s', Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2),
              Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)] at hadj_3w
            exact False.elim (by simp at hadj_3w)
          · simp only [s', Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2),
              Function.update_self] at hadj_3w
            exact LinkSet.mem_iff.mp (hadj_3w.resolve_left (by simp))
          · exact False.elim (hw3 rfl)
      have ha_pos : 1 ≤ a.neighbors.card := card_pos.mpr ⟨3, h3_mem⟩
      have hdeg : (formedGraph s').degree 2 ≤ a.neighbors.card + 1 := by
        rw [← card_neighborFinset_eq_degree]
        have hsub : (formedGraph s').neighborFinset 2 ⊆ insert 1 a.neighbors := by
          intro v hv
          rw [mem_neighborFinset] at hv
          have hv2 : v ≠ 2 := hv.ne.symm
          rw [formedGraph_adj] at hv
          simp only [s', Function.update_self, Function.update_of_ne hv2] at hv
          rcases hv with hva | h2v
          · exact mem_insert_of_mem hva
          · rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by fin_cases v <;> simp) with
              rfl | rfl | rfl | rfl
            · exact False.elim (by simp at h2v)
            · exact mem_insert_self 1 _
            · exact False.elim (hv2 rfl)
            · exact False.elim (by simp at h2v)
        exact (card_le_card hsub).trans (card_insert_le _ _)
      rw [playerCost_def, playerCost_def, hbase_real]
      have hc2 : (pathFourProfile 2).neighbors.card = 1 := by
        rw [LinkSet.neighbors_ofFinset]; decide
      have hite2 : (if (2 : Fin 4) = 1 ∨ (2 : Fin 4) = 2 then 4 else 6) = 4 := by decide
      rw [hc2, hite2]
      simp only [Nat.cast_one, Nat.cast_ofNat, s', Function.update_self]
      have : (6 : ℝ) ≤
          2 * (a.neighbors.card : ℝ) + ((6 - (formedGraph s').degree 2 : ℕ) : ℝ) := by
        have : 6 ≤ 2 * a.neighbors.card + (6 - (formedGraph s').degree 2) := by omega
        exact_mod_cast this
      linarith
    · -- Player 3: symmetric to Player 0 (`0` edges, original cost `6`).
      by_cases ha3 : a.neighbors = ∅
      · have ha_eq : a = pathFourProfile 3 := LinkSet.ext ha3
        have hs'_eq : s' = pathFourProfile := by
          simpa only [s', ha_eq] using Function.update_eq_self (3 : Fin 4) pathFourProfile
        rw [hs'_eq]
      · have ha_pos : 1 ≤ a.neighbors.card := card_pos.mpr (nonempty_iff_ne_empty.mpr ha3)
        have hdeg : (formedGraph s').degree 3 ≤ a.neighbors.card + 1 := by
          rw [← card_neighborFinset_eq_degree]
          have hsub : (formedGraph s').neighborFinset 3 ⊆ insert 2 a.neighbors := by
            intro v hv
            rw [mem_neighborFinset] at hv
            have hv3 : v ≠ 3 := hv.ne.symm
            rw [formedGraph_adj] at hv
            simp only [s', Function.update_self, Function.update_of_ne hv3] at hv
            rcases hv with hva | h3v
            · exact mem_insert_of_mem hva
            · rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by fin_cases v <;> simp) with
                rfl | rfl | rfl | rfl
              · exact False.elim (by simp at h3v)
              · exact False.elim (by simp at h3v)
              · exact mem_insert_self 2 _
              · exact False.elim (hv3 rfl)
          exact (card_le_card hsub).trans (card_insert_le _ _)
        rw [playerCost_def, playerCost_def, hbase_real]
        have hc3 : (pathFourProfile 3).neighbors.card = 0 := by simp
        have hite3 : (if (3 : Fin 4) = 1 ∨ (3 : Fin 4) = 2 then 4 else 6) = 6 := by decide
        rw [hc3, hite3]
        simp only [Nat.cast_zero, mul_zero, zero_add, Nat.cast_ofNat, s', Function.update_self]
        have : (6 : ℝ) ≤
            2 * (a.neighbors.card : ℝ) + ((6 - (formedGraph s').degree 3 : ℕ) : ℝ) := by
          have : 6 ≤ 2 * a.neighbors.card + (6 - (formedGraph s').degree 3) := by omega
          exact_mod_cast this
        linarith

end CslibFrontierTests.GameTheory.LocalConnection
