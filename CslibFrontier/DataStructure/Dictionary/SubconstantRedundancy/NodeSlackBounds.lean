/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.SeedBounds
import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Node, Pool, Waiting-List, and Hash-Seed Redundancy Slack Bounds

This module bounds the per-level node-metadata, root-value-pool directory, waiting-list, and
hash-seed components of `(canonicalSchedule h).redundancySlack` by `O(n / redundancyRatio n R)`
across `ValidRegime` ([LiLiangYuZhou2024], `arXiv:2310.20536v1`, Sections 5.2 and 5.4–5.6,
PDF pp. 27–36 / printed pp. 26–35).

## Main results

* `leaf_and_deficit_slack_le`, `nonLeaf_tables_slack_le`, `rootExtra_and_poolDir_slack_le`,
  `waitingLists_and_hashSeeds_slack_le`: inverse-redundancy bounds on the non-shared-table
  components of `redundancySlack`.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

/-- At any valid level `ℓ ≤ depth`, `canonicalSchedule` floor load equals integer division
`n / N_ℓ`. -/
theorem canonicalSchedule_nFloor_div_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hℓ : ℓ ≤ (canonicalSchedule h).depth) :
    (canonicalSchedule h).nFloor ℓ = n / (canonicalSchedule h).numNodes ℓ :=
  canonicalSchedule_nFloor_eq h ℓ ▸ canonicalSchedule_numNodes_eq h hℓ ▸ rfl

/-- Window radius `delta j ≥ 1` at every level `j ≤ depth` in `canonicalSchedule`. -/
theorem delta_pos_of_le_depth {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {j : ℕ}
    (hj : j ≤ (canonicalSchedule h).depth) :
    1 ≤ (canonicalSchedule h).delta j := by
  have hy1 : 1 ≤ (canonicalSchedule h).nFloor j := le_trans (by decide) (nFloor_ge_pow_256 h hj)
  rw [canonicalSchedule_delta_eq h j, delta, ← canonicalSchedule_nFloor_eq h j]
  exact (Nat.le_nthRoot_iff (by decide)).mpr (by rw [one_pow]; exact Nat.one_le_pow 2 _ hy1)

private theorem numNodes_mul_tableCap_of_schedule (P : TreeSchedule) {ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (hlt : ℓ < P.depth)
    (hnf_div : P.nFloor (ℓ + 1) = P.nFloor ℓ / P.branchFactor ℓ)
    (hd_next_pos : 1 ≤ P.delta (ℓ + 1))
    (h10d : ℓ = 1 → 10 * P.delta 1 ≤ P.branchFactor 1 * P.delta 2) :
    P.numNodes ℓ * P.tableCap ℓ ≤ 3 * P.numNodes (ℓ + 1) * P.delta (ℓ + 1) := by
  have hdiv := Nat.div_add_mod (P.nFloor ℓ) (P.branchFactor ℓ)
  have hmod := Nat.mod_lt (P.nFloor ℓ) (P.branchFactor_pos ℓ)
  rw [← hnf_div] at hdiv
  have hB_le := Nat.le_mul_of_pos_right (P.branchFactor ℓ) hd_next_pos
  have hBd_le := Nat.mul_le_mul_left (P.branchFactor ℓ)
    (P.delta_lt_nFloor (ℓ + 1) (by omega) hlt).le
  have hsub : P.branchFactor ℓ * P.nLow (ℓ + 1) =
      P.branchFactor ℓ * P.nFloor (ℓ + 1) - P.branchFactor ℓ * P.delta (ℓ + 1) := by
    rw [TreeSchedule.nLow, ite_eq_right (by omega), Nat.mul_sub]
  have hcap_le : P.tableCap ℓ ≤ 3 * (P.branchFactor ℓ * P.delta (ℓ + 1)) := by
    rcases eq_or_lt_of_le h1 with rfl | hgt1
    · have h10 : 10 * P.delta 1 ≤ P.branchFactor 1 * P.delta (1 + 1) := h10d rfl
      change P.nFloor 1 + P.delta 1 - P.branchFactor 1 * P.nLow (1 + 1) ≤ _
      rw [hsub]; omega
    · rw [TreeSchedule.tableCap, ite_eq_right (by omega), ite_eq_left hlt, hsub,
        TreeSchedule.nLow, ite_eq_right (by omega)]
      omega
  calc P.numNodes ℓ * P.tableCap ℓ
      ≤ P.numNodes ℓ * (3 * (P.branchFactor ℓ * P.delta (ℓ + 1))) :=
        Nat.mul_le_mul_left _ hcap_le
    _ = 3 * P.numNodes (ℓ + 1) * P.delta (ℓ + 1) := by rw [P.numNodes_succ ℓ]; ring

/-- Level-`ℓ` storage table slots across the forest are bounded by `3 * N_{ℓ+1} * Δ_{ℓ+1}`. -/
theorem numNodes_mul_tableCap_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (hlt : ℓ < (canonicalSchedule h).depth) :
    (canonicalSchedule h).numNodes ℓ * (canonicalSchedule h).tableCap ℓ ≤
      3 * (canonicalSchedule h).numNodes (ℓ + 1) * (canonicalSchedule h).delta (ℓ + 1) := by
  have hS17 := canonical_cumBranchBits_add_seventeen_le h (canonicalSchedule_depth h ▸ hlt)
  refine numNodes_mul_tableCap_of_schedule (canonicalSchedule h) h1 hlt ?_
    (delta_pos_of_le_depth h hlt) ?_
  · rw [canonicalSchedule_nFloor_eq h (ℓ + 1), canonicalSchedule_nFloor_eq h ℓ,
      canonicalSchedule_branchFactor_eq h ℓ]
    exact nFloor_succ_eq_div (by omega)
  · rintro rfl
    rw [canonicalSchedule_delta_eq h 1, canonicalSchedule_branchFactor_eq h 1,
      canonicalSchedule_delta_eq h 2]
    exact ten_mul_delta_le_branchFactor_mul_delta_succ hS17
      (canonicalSchedule_nFloor_eq h 2 ▸ (by decide : 8 ≤ 256 ^ 9).trans (nFloor_ge_pow_256 h hlt))

private theorem leaf_and_deficit_of_schedule (P : TreeSchedule) {n r : ℕ}
    (hcap : P.cap = n)
    (hNk_r : P.numNodes P.depth * r ≤ n)
    (hnf_div : P.nFloor P.depth = n / P.numNodes P.depth)
    (hd_pos : 1 ≤ P.delta P.depth)
    (hNd_r : P.numNodes P.depth * P.delta P.depth * r ≤ n) :
    (3 * P.numNodes P.depth + 3 * (P.cap - P.numNodes P.depth * P.nLow P.depth)) * r ≤ 9 * n := by
  have hk2 := P.two_le_depth
  have hdiv := Nat.div_add_mod n (P.numNodes P.depth)
  have hmod := Nat.mod_lt n (P.numNodes_pos P.depth)
  rw [← hnf_div] at hdiv
  have hNd_le := Nat.mul_le_mul_left (P.numNodes P.depth)
    (P.delta_lt_nFloor P.depth (by omega) le_rfl).le
  have hN_le := Nat.le_mul_of_pos_right (P.numNodes P.depth) hd_pos
  have hdef : P.cap - P.numNodes P.depth * P.nLow P.depth ≤
      2 * (P.numNodes P.depth * P.delta P.depth) := by
    rw [hcap, TreeSchedule.nLow, ite_eq_right (by omega), Nat.mul_sub]
    omega
  calc (3 * P.numNodes P.depth + 3 * (P.cap - P.numNodes P.depth * P.nLow P.depth)) * r
      ≤ (3 * P.numNodes P.depth + 3 * (2 * (P.numNodes P.depth * P.delta P.depth))) * r := by
        gcongr
    _ = 3 * (P.numNodes P.depth * r) + 6 * (P.numNodes P.depth * P.delta P.depth * r) := by ring
    _ ≤ 9 * n := by omega

/-- Total leaf-slack and value deficit bit budget scaled by `r` is bounded by `9 * n`. -/
theorem leaf_and_deficit_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (3 * (canonicalSchedule h).numNodes (canonicalSchedule h).depth +
      3 * ((canonicalSchedule h).cap -
        (canonicalSchedule h).numNodes (canonicalSchedule h).depth *
          (canonicalSchedule h).nLow (canonicalSchedule h).depth)) *
      redundancyRatio n R ≤ 9 * n := by
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  have hk2 := two_le_treeDepth U (redundancyRatio n R)
  have hNT := (numNodes_mul_targetSize_bounds (hT_pos _ le_rfl) (hT_le _ le_rfl)).1
  have hcub := numNodes_mul_delta_mul_levelScale_cubed_le (by omega)
    (hT_pos _ le_rfl) (hT_le _ le_rfl)
  rw [targetSize_eq_levelScale_pow (by omega)] at hNT
  simp only [levelScale, lt_self_iff_false, ↓reduceIte] at hNT hcub
  refine leaf_and_deficit_of_schedule (canonicalSchedule h) (canonicalSchedule_cap h) ?_
    (canonicalSchedule_nFloor_div_eq h le_rfl) (delta_pos_of_le_depth h le_rfl) ?_
  · rw [canonicalSchedule_numNodes_eq h le_rfl, canonicalSchedule_depth]
    exact (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _)).trans hNT
  · rw [canonicalSchedule_numNodes_eq h le_rfl, canonicalSchedule_delta_eq h _,
      canonicalSchedule_depth]
    exact (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _)).trans hcub

private theorem single_nonLeaf_tableMeta_of_schedule (P : TreeSchedule) {n r s ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (hlt : ℓ < P.depth)
    (hs_ge_r : r ≤ s)
    (hy_ge : 256 ^ 9 ≤ P.nFloor ℓ)
    (hid_def : P.idBits ℓ = 4 * Nat.clog 2 (2 * max (P.nFloor ℓ) 1))
    (hid_le : P.idBits ℓ + 2 ≤ 150 * s)
    (hNtc : P.numNodes ℓ * P.tableCap ℓ ≤ 3 * P.numNodes (ℓ + 1) * P.delta (ℓ + 1))
    (hd_pos : 1 ≤ P.delta (ℓ + 1))
    (hcub : P.numNodes (ℓ + 1) * P.delta (ℓ + 1) * s ^ 3 ≤ n) :
    P.numNodes ℓ *
        (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
          P.tableCap ℓ *
            (Nat.clog 2 (2 * (P.nFloor ℓ + 1)) + Nat.clog 2 (P.tableCap ℓ + 1))) *
      r ^ 2 ≤ 36000 * n := by
  have htc_id : P.tableCap ℓ ≤ 2 ^ P.idBits ℓ := by
    refine le_trans ?_ (P.nHigh_le_two_pow_idBits ℓ h1 hlt.le)
    rcases eq_or_lt_of_le h1 with rfl | hgt1
    · exact Nat.sub_le (P.nFloor 1 + P.delta 1) _
    · rw [TreeSchedule.tableCap, ite_eq_right (by omega), ite_eq_left hlt, TreeSchedule.nLow,
        ite_eq_right (by omega)]
      omega
  have hpow := Nat.two_pow_pos (P.idBits ℓ)
  have hcl_nf : Nat.clog 2 (2 * (P.nFloor ℓ + 1)) ≤ P.idBits ℓ := by
    have hc := Nat.le_pow_clog Nat.one_lt_two (2 * max (P.nFloor ℓ) 1)
    have hc1 := Nat.clog_pos Nat.one_lt_two (by omega : 2 ≤ 2 * max (P.nFloor ℓ) 1)
    have : Nat.clog 2 (2 * (P.nFloor ℓ + 1)) ≤ Nat.clog 2 (2 * max (P.nFloor ℓ) 1) + 1 :=
      Nat.clog_le_of_le_pow (by rw [pow_succ']; omega)
    omega
  have hcl_tc : Nat.clog 2 (P.tableCap ℓ + 1) ≤ P.idBits ℓ + 1 :=
    Nat.clog_le_of_le_pow (by rw [pow_succ']; omega)
  have hN_le : P.numNodes ℓ ≤ P.numNodes (ℓ + 1) * P.delta (ℓ + 1) := by
    rw [P.numNodes_succ, Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (P.branchFactor_pos ℓ) hd_pos)
  have hN77 : P.numNodes ℓ * (77 * P.tableCap ℓ + 9) ≤
      240 * (P.numNodes (ℓ + 1) * P.delta (ℓ + 1)) := by
    rw [Nat.mul_assoc 3] at hNtc
    rw [Nat.mul_add, Nat.mul_left_comm]; omega
  calc P.numNodes ℓ *
        (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
          P.tableCap ℓ *
            (Nat.clog 2 (2 * (P.nFloor ℓ + 1)) + Nat.clog 2 (P.tableCap ℓ + 1))) * r ^ 2
      ≤ P.numNodes ℓ * ((75 * P.tableCap ℓ * (P.idBits ℓ + 2) + 9 * (P.idBits ℓ + 2)) +
          P.tableCap ℓ * (2 * (P.idBits ℓ + 2))) * r ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add
          (succinctTableMetaBits_le htc_id) (Nat.mul_le_mul_left _ (by omega))))
    _ = P.numNodes ℓ * (77 * P.tableCap ℓ + 9) * (P.idBits ℓ + 2) * r ^ 2 := by ring
    _ ≤ 240 * (P.numNodes (ℓ + 1) * P.delta (ℓ + 1)) * (150 * s) * s ^ 2 := by gcongr
    _ = 36000 * (P.numNodes (ℓ + 1) * P.delta (ℓ + 1) * s ^ 3) := by ring
    _ ≤ 36000 * n := Nat.mul_le_mul_left 36000 hcub

/-- A product of two numbers whose squares are at most `c` is at most `c`. -/
private theorem mul_le_of_sq_le {a b c : ℕ} (ha : a ^ 2 ≤ c) (hb : b ^ 2 ≤ c) : a * b ≤ c := by
  rcases le_total a b with h | h
  · exact (Nat.mul_le_mul_right b h).trans ((sq b).symm ▸ hb)
  · exact (Nat.mul_le_mul_left a h).trans ((sq a).symm ▸ ha)

private theorem sum_mul_le_of_mul_sq_le {S : Finset ℕ} {f : ℕ → ℕ} {r B : ℕ}
    (hr1 : 1 ≤ r) (hcard : S.card ≤ r) (hbound : ∀ ℓ ∈ S, f ℓ * r ^ 2 ≤ B) :
    (∑ ℓ ∈ S, f ℓ) * r ≤ B := by
  refine Nat.le_of_mul_le_mul_right ?_ hr1
  calc (∑ ℓ ∈ S, f ℓ) * r * r
      = ∑ ℓ ∈ S, f ℓ * r ^ 2 := by rw [Nat.mul_assoc, ← sq, Finset.sum_mul]
    _ ≤ ∑ _ℓ ∈ S, B := Finset.sum_le_sum hbound
    _ = S.card * B := by simp
    _ ≤ B * r := by rw [Nat.mul_comm B r]; exact Nat.mul_le_mul_right B hcard

private theorem nonLeaf_tables_of_schedule (P : TreeSchedule) {n r : ℕ}
    (hr1 : 1 ≤ r) (hk_le_r : P.depth ≤ r)
    (hsingle : ∀ ℓ, 1 ≤ ℓ → ℓ < P.depth →
      P.numNodes ℓ *
        (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
          P.tableCap ℓ *
            (Nat.clog 2 (2 * (P.nFloor ℓ + 1)) + Nat.clog 2 (P.tableCap ℓ + 1))) *
        r ^ 2 ≤ 36000 * n) :
    ((∑ ℓ ∈ Finset.Ico 2 P.depth,
        P.numNodes ℓ *
          (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
            P.tableCap ℓ * Nat.clog 2 (2 * (P.nFloor ℓ + 1)))) +
      P.numNodes 1 *
        (succinctTableMetaBits (P.idBits 1) (P.tableCap 1) +
          P.tableCap 1 *
            (Nat.clog 2 (2 * (P.nFloor 1 + 1)) + Nat.clog 2 (P.tableCap 1 + 1)))) *
      r ≤ 72000 * n := by
  rw [Nat.add_mul]
  refine (Nat.add_le_add (sum_mul_le_of_mul_sq_le (B := 36000 * n) hr1
    (by rw [Nat.card_Ico]; omega) fun ℓ hℓ => ?_)
    ((Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) r)).trans
      (hsingle 1 le_rfl (by have := P.two_le_depth; omega)))).trans (by omega)
  obtain ⟨h2, hlt⟩ := Finset.mem_Ico.mp hℓ
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _))).trans (hsingle ℓ (by omega) hlt)

/-- Total metadata and payload overhead of all non-leaf tables scaled by `r` is bounded
by `72000 * n`. -/
theorem nonLeaf_tables_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    ((∑ ℓ ∈ Finset.Ico 2 (canonicalSchedule h).depth,
        (canonicalSchedule h).numNodes ℓ *
          (succinctTableMetaBits ((canonicalSchedule h).idBits ℓ)
              ((canonicalSchedule h).tableCap ℓ) +
            (canonicalSchedule h).tableCap ℓ *
              Nat.clog 2 (2 * ((canonicalSchedule h).nFloor ℓ + 1)))) +
      (canonicalSchedule h).numNodes 1 *
        (succinctTableMetaBits ((canonicalSchedule h).idBits 1)
            ((canonicalSchedule h).tableCap 1) +
          (canonicalSchedule h).tableCap 1 *
            (Nat.clog 2 (2 * ((canonicalSchedule h).nFloor 1 + 1)) +
              Nat.clog 2 ((canonicalSchedule h).tableCap 1 + 1)))) *
      redundancyRatio n R ≤ 72000 * n := by
  have hr256 : 256 ≤ redundancyRatio n R := h.redundancyRatio_bounds.1
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  refine nonLeaf_tables_of_schedule (canonicalSchedule h) h.one_le_redundancyRatio
    ((canonicalSchedule_depth h).symm ▸ h.treeDepth_le_redundancyRatio)
    fun ℓ h1 hlt => ?_
  have hlt_k : ℓ < treeDepth U (redundancyRatio n R) := by rwa [← canonicalSchedule_depth h]
  have hs_ge_r := r_le_levelScale (ℓ := ℓ + 1) (by omega) h.four_mul_redundancyRatio_le_log_univ
  refine single_nonLeaf_tableMeta_of_schedule (canonicalSchedule h) h1 hlt hs_ge_r
    (nFloor_ge_pow_256 h hlt.le)
    (canonicalSchedule_idBits_eq h ℓ ▸ canonicalSchedule_nFloor_eq h ℓ ▸ rfl) ?_
    (numNodes_mul_tableCap_le h h1 hlt) (delta_pos_of_le_depth h hlt) ?_
  · have := Nat.add_sub_cancel ℓ 1 ▸ idBits_pred_le_mul_levelScale hr256 (by omega : 2 ≤ ℓ + 1)
      hlt_k (hT_pos ℓ hlt_k.le) (hT_le ℓ hlt_k.le)
    rw [canonicalSchedule_idBits_eq h ℓ]
    omega
  · rw [canonicalSchedule_numNodes_eq h hlt, canonicalSchedule_delta_eq h (ℓ + 1)]
    exact numNodes_mul_delta_mul_levelScale_cubed_le (by omega) (hT_pos (ℓ + 1) hlt_k)
      (hT_le (ℓ + 1) hlt_k)

private theorem rootExtra_and_poolDir_of_schedule (P : TreeSchedule) {n r L s1 p_max : ℕ}
    (hn2 : 2 ≤ n) (hL_eq : L = Nat.log 2 n)
    (h10_L : 10 ≤ L) (hpL : 2 * (p_max + 2) + 1 ≤ L) (hL_s1 : L ≤ s1) (hr_le_L : r ≤ L)
    (hcap : P.cap = n)
    (hpad_pow : P.paddedUniv ≤ 2 ^ (2 * (p_max + 2) * L))
    (hN1_nf : P.numNodes 1 * P.nFloor 1 ≤ n)
    (hcub1 : P.numNodes 1 * P.delta 1 * s1 ^ 3 ≤ n)
    (hNtc1 : P.numNodes 1 * P.tableCap 1 ≤ 3 * P.numNodes 2 * P.delta 2)
    (hN2d2 : P.numNodes 2 * P.delta 2 ≤ n)
    (hN1_L9 : P.numNodes 1 * L ^ 9 ≤ n) :
    ((P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) *
        Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap) +
      P.rootPoolDirBits) * r ≤ 8 * n := by
  have hn_ge : 2 ^ L ≤ n := hL_eq ▸ Nat.pow_log_le_self 2 (by omega)
  have hn_lt : n < 2 ^ (L + 1) := hL_eq ▸ Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hN2_nl : P.numNodes 2 * P.nLow 2 ≤ n := hcap ▸ P.numNodes_two_mul_nLow_two_le_cap
  -- the root slots beyond the value pool, each with at most `s1 ^ 2` extra quotient bits
  have hextra_le : P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap ≤
      P.numNodes 1 * P.delta 1 := by
    have htc1 : P.tableCap 1 = P.nFloor 1 + P.delta 1 - P.branchFactor 1 * P.nLow 2 := rfl
    have hN2 : P.numNodes 2 = P.numNodes 1 * P.branchFactor 1 := P.numNodes_succ 1
    rw [TreeSchedule.rootValPoolCap, hcap, htc1, Nat.mul_sub, ← Nat.mul_assoc, ← hN2, Nat.mul_add]
    omega
  have hq_le : Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap) ≤ s1 ^ 2 := by
    have hpad_n : P.cap ≤ P.paddedUniv := by
      have := P.univ_le_padded
      dsimp only [TreeSchedule.paddedUniv, TreeSchedule.branchFactor]; omega
    refine Nat.clog_le_of_le_pow ((Nat.div_le_self _ _).trans ?_)
    calc P.paddedUniv + P.cap - 1 ≤ 2 ^ (2 * (p_max + 2) * L + 1) := by rw [pow_succ']; omega
      _ ≤ 2 ^ s1 ^ 2 := Nat.pow_le_pow_right Nat.two_pos (by
          have := Nat.mul_le_mul (hpL.trans hL_s1) hL_s1
          rw [Nat.add_mul, Nat.one_mul] at this
          rw [sq]; omega)
  have hextra_r : (P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) *
      Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap) * r ≤ n :=
    calc _ ≤ P.numNodes 1 * P.delta 1 * s1 ^ 2 * s1 :=
          Nat.mul_le_mul (Nat.mul_le_mul hextra_le hq_le) (hr_le_L.trans hL_s1)
      _ = P.numNodes 1 * P.delta 1 * s1 ^ 3 := by ring
      _ ≤ n := hcub1
  -- the pool directory: pointers of `L ≤ ptrBits ≤ 2 * L` bits, slabs of `ptrBits ^ 2` slots
  set ptrBits := Nat.clog 2 (P.cap + 2)
  have hptr_lo : L ≤ ptrBits :=
    (Nat.clog_pow 2 L Nat.one_lt_two).ge.trans (Nat.clog_mono_right 2 (by omega))
  have hptr_hi : ptrBits ≤ 2 * L := Nat.clog_le_of_le_pow
    ((by omega : P.cap + 2 ≤ 2 * 2 ^ (L + 1)).trans ((pow_succ' 2 _).symm.le.trans
      (Nat.pow_le_pow_right Nat.two_pos (by omega))))
  set K := max P.rootSlabSize 1
  have hK_eq : K = ptrBits ^ 2 := max_eq_left (Nat.one_le_pow 2 ptrBits (by omega))
  have hdiv : ∀ x, x / K * (ptrBits * r) ≤ x := fun x =>
    (Nat.mul_le_mul_left _ (hK_eq ▸ sq ptrBits ▸
      Nat.mul_le_mul_left _ (hr_le_L.trans hptr_lo))).trans (Nat.div_mul_le_self x K)
  have hdiv_tc : P.numNodes 1 * (P.tableCap 1 / K) * (ptrBits * r) ≤ 3 * n :=
    calc _ = P.numNodes 1 * (P.tableCap 1 / K * (ptrBits * r)) := Nat.mul_assoc ..
      _ ≤ P.numNodes 1 * P.tableCap 1 := Nat.mul_le_mul_left _ (hdiv _)
      _ ≤ 3 * n := hNtc1.trans (by rw [Nat.mul_assoc]; omega)
  have hdiv_pool : P.rootValPoolCap / K * (ptrBits * r) ≤ n :=
    (hdiv _).trans (by rw [TreeSchedule.rootValPoolCap]; omega)
  have hrem_dir : (P.numNodes 1 * (1 + K) + 4) * (ptrBits * r) ≤ 3 * n := by
    have hL2 : 1 ≤ L ^ 2 := Nat.one_le_pow 2 L (by omega)
    have hK5 : 1 + K ≤ 5 * L ^ 2 := by rw [hK_eq]; nlinarith only [hptr_hi, hL2]
    have hK9 : P.numNodes 1 * (1 + K) + 4 ≤ P.numNodes 1 * (9 * L ^ 2) :=
      calc _ ≤ P.numNodes 1 * (5 * L ^ 2) + P.numNodes 1 * (4 * L ^ 2) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hK5)
              ((by omega : 4 ≤ 4 * L ^ 2).trans (Nat.le_mul_of_pos_left _ (P.numNodes_pos 1)))
        _ = P.numNodes 1 * (9 * L ^ 2) := by ring
    calc (P.numNodes 1 * (1 + K) + 4) * (ptrBits * r)
        ≤ P.numNodes 1 * (9 * L ^ 2) * (2 * L * L) :=
          Nat.mul_le_mul hK9 (Nat.mul_le_mul hptr_hi hr_le_L)
      _ = 18 * L ^ 4 * P.numNodes 1 := by ring
      _ ≤ L ^ 5 * L ^ 4 * P.numNodes 1 := by
          gcongr; exact (by norm_num : 18 ≤ 10 ^ 5).trans (Nat.pow_le_pow_left h10_L 5)
      _ = P.numNodes 1 * L ^ 9 := by ring
      _ ≤ 3 * n := by omega
  have hdir_r : P.rootPoolDirBits * r ≤ 7 * n :=
    calc P.rootPoolDirBits * r
        = P.numNodes 1 * (P.tableCap 1 / K) * (ptrBits * r) +
            P.rootValPoolCap / K * (ptrBits * r) +
            (P.numNodes 1 * (1 + K) + 4) * (ptrBits * r) := by
          change (P.numNodes 1 * (P.tableCap 1 / K + 1 + K) + P.rootValPoolCap / K + 4) *
            ptrBits * r = _
          ring
      _ ≤ 7 * n := by omega
  rw [Nat.add_mul]; omega

/-- Root extra quotient bits and pool directory overhead scaled by `r` is bounded by `8 * n`. -/
theorem rootExtra_and_poolDir_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (((canonicalSchedule h).numNodes 1 * (canonicalSchedule h).tableCap 1 -
        (canonicalSchedule h).rootValPoolCap) *
      Nat.clog 2 (((canonicalSchedule h).paddedUniv + (canonicalSchedule h).cap - 1) /
        (canonicalSchedule h).cap) +
      (canonicalSchedule h).rootPoolDirBits) * redundancyRatio n R ≤ 8 * n := by
  have hr256 : 256 ≤ redundancyRatio n R := h.redundancyRatio_bounds.1
  obtain ⟨hL_s1, _⟩ := h.log_univ_bounds
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  have h1_lt : 1 < treeDepth U (redundancyRatio n R) := two_le_treeDepth U (redundancyRatio n R)
  have hp := h.mul_param_le_log (by decide : 3 ≤ 2560000)
  have h1_lt_d : 1 < (canonicalSchedule h).depth := by rwa [canonicalSchedule_depth]
  have hls1 : levelScale U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) 1 =
      Nat.log 2 U := ite_eq_left h1_lt
  refine rootExtra_and_poolDir_of_schedule (canonicalSchedule h) h.two_le_n rfl (by omega)
    (by omega) hL_s1 h.redundancyRatio_le_log (canonicalSchedule_cap h)
    (paddedUniv_le_two_pow_mul_log h) ?_ ?_ (numNodes_mul_tableCap_le h le_rfl h1_lt_d) ?_ ?_
  · exact (canonicalSchedule_nFloor_div_eq h h1_lt_d.le).symm ▸ Nat.mul_div_le n _
  · rw [canonicalSchedule_numNodes_eq h h1_lt_d.le, canonicalSchedule_delta_eq h 1]
    exact hls1 ▸ numNodes_mul_delta_mul_levelScale_cubed_le le_rfl (hT_pos 1 h1_lt.le)
      (hT_le 1 h1_lt.le)
  · rw [canonicalSchedule_numNodes_eq h h1_lt_d, canonicalSchedule_delta_eq h 2]
    have hs2 : 0 < levelScale U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) 2 :=
      (by omega : 0 < redundancyRatio n R).trans_le
        (r_le_levelScale (by decide) h.four_mul_redundancyRatio_le_log_univ)
    exact (Nat.le_mul_of_pos_right _ (Nat.pow_pos hs2)).trans
      (numNodes_mul_delta_mul_levelScale_cubed_le (by decide : 1 ≤ 2) (hT_pos 2 h1_lt)
        (hT_le 2 h1_lt))
  · have hNT1 := (numNodes_mul_targetSize_bounds (hT_pos 1 h1_lt.le) (hT_le 1 h1_lt.le)).1
    rw [targetSize_eq_levelScale_pow le_rfl, hls1] at hNT1
    rw [canonicalSchedule_numNodes_eq h h1_lt_d.le]
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL_s1 9)).trans hNT1

private theorem waitingLists_and_hashSeeds_of_schedule (P : TreeSchedule) {n U r s1 : ℕ}
    (hr256 : 256 ≤ r) (hr2_n : r ^ 2 ≤ n) (hr_s1 : r ≤ s1) (hs1_eq : s1 = Nat.log 2 U)
    (h4r : 4 * r ≤ Nat.log 2 U)
    (hdepth_eq : P.depth = treeDepth U r) (hcap_eq : P.cap = n) (hk_le_r : P.depth ≤ r)
    (hpad_s1 : P.paddedUniv ≤ 2 ^ (s1 ^ 2))
    (hsq_all : ∀ ℓ < P.depth, (P.routerSeedBits ℓ) ^ 2 ≤ P.nFloor ℓ)
    (hd_pos_all : ∀ j ≤ P.depth, 1 ≤ P.delta j)
    (hid_pred_all : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ P.depth → P.idBits (ℓ - 1) ≤ 148 * levelScale U r P.depth ℓ)
    (hcub_all : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.depth →
      P.numNodes ℓ * P.delta ℓ * (levelScale U r P.depth ℓ) ^ 3 ≤ n)
    (hNT_all : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.depth →
      P.numNodes ℓ * (levelScale U r P.depth ℓ) ^ 9 ≤ n ∧
        (levelScale U r P.depth ℓ) ^ 9 ≤ P.nFloor ℓ ∧
        P.numNodes ℓ * P.nFloor ℓ ≤ n) :
    (P.allWaitingListsBits + P.allHashSeedsBits) * r ≤ 1700 * n := by
  subst hs1_eq
  have hr1 : 1 ≤ r := by omega
  have hd2 := P.two_le_depth
  have hs_r : ∀ ℓ, 1 ≤ ℓ → r ≤ levelScale U r P.depth ℓ := fun ℓ h1 =>
    hdepth_eq ▸ r_le_levelScale h1 h4r
  have hwait_r : P.allWaitingListsBits * r ≤ 740 * n := by
    refine sum_mul_le_of_mul_sq_le hr1 (by rw [Nat.card_Icc]; omega) fun ℓ hℓ => ?_
    obtain ⟨h2, hle⟩ := Finset.mem_Icc.mp hℓ
    have hd_pos := hd_pos_all ℓ hle
    calc P.numNodes ℓ * waitingListBits (P.waitCap ℓ) (P.idBits ℓ) (P.idBits (ℓ - 1)) * r ^ 2
        ≤ P.numNodes ℓ * (5 * P.delta ℓ * (148 * levelScale U r P.depth ℓ)) *
            levelScale U r P.depth ℓ ^ 2 := by
          gcongr
          · exact (P.waitingListBits_le_of_two_le h2 hle).trans
              (Nat.mul_le_mul (by omega) (hid_pred_all ℓ h2 hle))
          · exact hs_r ℓ (by omega)
      _ = 740 * (P.numNodes ℓ * P.delta ℓ * levelScale U r P.depth ℓ ^ 3) := by ring
      _ ≤ 740 * n := Nat.mul_le_mul_left 740 (hcub_all ℓ (by omega) hle)
  have hseed0_r : P.routerSeedBits 0 * r ≤ n :=
    mul_le_of_sq_le (by have := hsq_all 0 (by omega); rwa [P.nFloor_zero, hcap_eq] at this) hr2_n
  have hseed_sum_r :
      (∑ ℓ ∈ Finset.Icc 1 P.depth, P.numNodes ℓ * P.nodeHashSeedBits ℓ) * r ≤ 900 * n := by
    refine sum_mul_le_of_mul_sq_le hr1 (by rw [Nat.card_Icc]; omega) fun ℓ hℓ => ?_
    obtain ⟨h1, hle⟩ := Finset.mem_Icc.mp hℓ
    obtain ⟨hNT, hs9_nf, hN_nf⟩ := hNT_all ℓ h1 hle
    have hs := hs_r ℓ h1
    set s := levelScale U r P.depth ℓ
    have hrouter : P.numNodes ℓ * (if ℓ < P.depth then P.routerSeedBits ℓ else 0) * r ^ 2 ≤
        n := by
      split_ifs with hlt
      · rw [Nat.mul_assoc]
        have hpow : (r ^ 2) ^ 2 ≤ P.nFloor ℓ := by
          rw [← pow_mul]
          exact (show r ^ 4 ≤ s ^ 9 by gcongr <;> omega).trans hs9_nf
        exact (Nat.mul_le_mul_left _ (mul_le_of_sq_le (hsq_all ℓ hlt) hpow)).trans hN_nf
      · simp
    -- the ID-compressor seed takes `O(s ^ 2)` bits at the roots and `O(s)` bits below
    have hic : FeistelPerm.idCompressorSeedBits (P.idBits ℓ) (P.idCompRightUniv ℓ) ≤
        894 * s ^ 2 := by
      have hs2 : s ≤ s ^ 2 := Nat.le_self_pow two_ne_zero s
      rcases eq_or_lt_of_le h1 with rfl | hgt1
      · have hs_eq : s = Nat.log 2 U := ite_eq_left (by omega)
        have hls2 : levelScale U r P.depth 2 ≤ Nat.log 2 U := by
          by_cases h : 2 < P.depth <;> simp [levelScale, h, Nat.log_le_self, hr_s1]
        have hid1 : P.idBits 1 ≤ 148 * levelScale U r P.depth 2 := hid_pred_all 2 le_rfl hd2
        have hsq : 1 ≤ Nat.log 2 U ^ 2 ∧ 148 * Nat.log 2 U ≤ Nat.log 2 U ^ 2 :=
          ⟨Nat.one_le_pow _ _ (by omega), (Nat.mul_le_mul_right _ (by omega)).trans_eq (sq _).symm⟩
        have hcl1 : Nat.clog 2 (max (P.idCompRightUniv 1) 2) ≤ Nat.log 2 U ^ 2 :=
          Nat.clog_le_of_le_pow (max_le ((Nat.le_mul_of_pos_left _ (Nat.mul_pos
            (P.branchFactor_pos 0) (Nat.two_pow_pos _))).trans hpad_s1)
            (Nat.le_self_pow (by omega) 2))
        have := FeistelPerm.idCompressorSeedBits_le (P.idBits 1) (P.idCompRightUniv 1)
        rw [hs_eq]; omega
      · have := P.idCompressorSeedBits_le_of_two_le hgt1 hle
        have := hid_pred_all ℓ hgt1 hle
        omega
    have hidc : P.numNodes ℓ *
        FeistelPerm.idCompressorSeedBits (P.idBits ℓ) (P.idCompRightUniv ℓ) * r ^ 2 ≤ 894 * n :=
      calc _ ≤ P.numNodes ℓ * (894 * s ^ 2) * s ^ 2 := by gcongr
        _ = 894 * (P.numNodes ℓ * s ^ 4) := by ring
        _ ≤ 894 * (P.numNodes ℓ * s ^ 9) := by gcongr <;> omega
        _ ≤ 894 * n := Nat.mul_le_mul_left _ hNT
    rw [TreeSchedule.nodeHashSeedBits, ite_eq_right (by omega), Nat.mul_add, Nat.add_mul]; omega
  rw [TreeSchedule.allHashSeedsBits, Nat.add_mul, Nat.add_mul]; omega

/-- Total bits for waiting lists and all node hash seeds scaled by `r` is bounded by
`1700 * n`. -/
theorem waitingLists_and_hashSeeds_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    ((canonicalSchedule h).allWaitingListsBits + (canonicalSchedule h).allHashSeedsBits) *
      redundancyRatio n R ≤ 1700 * n := by
  obtain ⟨hr256, _, hr10⟩ := h.redundancyRatio_bounds
  obtain ⟨hL_s1, _⟩ := h.log_univ_bounds
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  have hk := canonicalSchedule_depth h
  have hr2_n : (redundancyRatio n R) ^ 2 ≤ n :=
    ((Nat.pow_le_pow_right h.one_le_redundancyRatio (by decide : 2 ≤ 10)).trans hr10).trans
      (Nat.log_le_self 2 n)
  have hp := h.mul_param_le_log (by decide : 2 ≤ 2560000)
  have h2p_s1 : 2 * (p_max + 2) * Nat.log 2 n ≤ (Nat.log 2 U) ^ 2 :=
    ((Nat.mul_le_mul_right _ (by omega : 2 * (p_max + 2) ≤ Nat.log 2 n)).trans
      (sq _).symm.le).trans (Nat.pow_le_pow_left hL_s1 2)
  refine waitingLists_and_hashSeeds_of_schedule (canonicalSchedule h) hr256 hr2_n
    (h.redundancyRatio_le_log.trans hL_s1) rfl
    h.four_mul_redundancyRatio_le_log_univ hk (canonicalSchedule_cap h)
    (hk.symm ▸ h.treeDepth_le_redundancyRatio)
    ((paddedUniv_le_two_pow_mul_log h).trans (Nat.pow_le_pow_right Nat.two_pos h2p_s1))
    (fun ℓ hlt => routerSeedBits_sq_le_nFloor h hlt)
    (fun j hj => delta_pos_of_le_depth h hj) (fun ℓ h2 hle => ?_) (fun ℓ h1 hle => ?_)
    fun ℓ h1 hle => ?_
  · rw [canonicalSchedule_idBits_eq h (ℓ - 1), hk]
    exact idBits_pred_le_mul_levelScale hr256 h2 (hk ▸ hle)
      (hT_pos (ℓ - 1) (by omega)) (hT_le (ℓ - 1) (by omega))
  · rw [canonicalSchedule_numNodes_eq h hle, canonicalSchedule_delta_eq h ℓ, hk]
    exact numNodes_mul_delta_mul_levelScale_cubed_le h1 (hT_pos ℓ (hk ▸ hle))
      (hT_le ℓ (hk ▸ hle))
  · rw [canonicalSchedule_numNodes_eq h hle, canonicalSchedule_nFloor_eq h ℓ, hk,
      ← targetSize_eq_levelScale_pow h1]
    exact ⟨(numNodes_mul_targetSize_bounds (hT_pos ℓ (hk ▸ hle)) (hT_le ℓ (hk ▸ hle))).1,
      (targetSize_le_nFloor_and_lt (hT_pos ℓ (hk ▸ hle)) (hT_le ℓ (hk ▸ hle))).1, Nat.mul_div_le ..⟩

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
