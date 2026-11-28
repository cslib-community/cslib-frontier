/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.NodeSeeds
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.NodeSlackBounds
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# End-to-End Pure Subconstant-Redundancy Bit-Budget Bound (`infoBits + O(R)`)

This module is the top-level parameter and space-accounting entry point for the Section 5
multi-level dictionary tree of [LiLiangYuZhou2024] (`arXiv:2310.20536v1`, Sections 5.1–5.2 and
5.4–5.6, PDF pp. 25–36 / printed pp. 24–35), publicly re-exporting `Schedule`, `BitBudget`,
`Canonical`, `NodeSeeds`, `SeedBounds`, and `NodeSlackBounds` and proving the headline pure space
theorem `totalTreeBits_le_infoBits_add` bounding the arithmetic bit budget of the intended
Section 5 layout (not tied to an operational state by an explicit bit-packing encoding):

```text
(canonicalSchedule h).totalTreeBits ≤ infoBits U V n + spaceConst * R
```

for an explicit universal constant `spaceConst` across all
`ValidRegime U V n R p_min q_min p_max q_max` (with no upper bound on `V`).

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.spaceConst`: explicit universal constant
  `O(1)` in `infoBits U V n + spaceConst * R`.

## Main results

* `redundancySlack_le_mul_effRedundancy`: `redundancySlack` is bounded uniformly across all `1 ≤ V`
  by `150000 * effRedundancy n R`.
* `totalTreeBits_le_infoBits_add`: total pure tree representation bit budget of the intended
  Section 5 layout is at most `infoBits U V n + spaceConst * R` (with `spaceConst = 160000`).

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

/-- Two factors below `2 ^ (L / 2)` have a product below any `n ≥ 2 ^ L`. -/
private theorem mul_le_of_le_two_pow_half {a b L n : ℕ} (ha : a ≤ 2 ^ (L / 2))
    (hb : b ≤ 2 ^ (L / 2)) (hn : 2 ^ L ≤ n) : a * b ≤ n :=
  calc a * b ≤ 2 ^ (L / 2 + L / 2) := by rw [pow_add]; exact Nat.mul_le_mul ha hb
    _ ≤ n := (Nat.pow_le_pow_right Nat.two_pos (by omega)).trans hn

/-- From level `1` on, the lower load threshold is at most the expected load and fits in the key
IDs. -/
private theorem TreeSchedule.nLow_le (P : TreeSchedule) {ℓ : ℕ} (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.depth) : P.nLow ℓ ≤ P.nFloor ℓ ∧ P.nLow ℓ ≤ 2 ^ P.idBits ℓ := by
  have := P.nHigh_le_two_pow_idBits ℓ h1 hℓ
  rw [TreeSchedule.nLow, ite_eq_right (by omega)]
  omega

/-- From level `2` on, a table holds at most the lower load threshold of its node. -/
private theorem TreeSchedule.tableCap_le_nLow (P : TreeSchedule) {ℓ : ℕ} (h2 : 2 ≤ ℓ)
    (hℓ : ℓ ≤ P.depth) : P.tableCap ℓ ≤ P.nLow ℓ := by
  rw [TreeSchedule.tableCap, ite_eq_right (by omega)]
  split_ifs with hlt
  · exact Nat.sub_le _ _
  · rw [show ℓ = P.depth by omega]

/-- The shared carry-less multiplication table takes at most `n / r` bits. -/
private theorem clmul_of_schedule (P : TreeSchedule) {n r L : ℕ}
    (hn2 : 2 ≤ n) (hL_eq : L = Nat.log 2 n) (h2M : 2560000 ≤ L) (hr_le_L : r ≤ L)
    (hcap : P.cap = n) (hpad_L2 : P.paddedUniv ≤ 2 ^ (L ^ 2)) :
    2 ^ (2 * (Nat.log 2 (max P.cap 2) / 3)) * (6 * Nat.clog 2 (max P.paddedUniv 2) + 6) * r ≤
      n := by
  have hn_2L : 2 ^ L ≤ n := hL_eq ▸ Nat.pow_log_le_self 2 (by omega)
  have hcl_pad : Nat.clog 2 (max P.paddedUniv 2) ≤ L ^ 2 :=
    Nat.clog_le_of_le_pow (max_le hpad_L2 (Nat.le_self_pow (by positivity) 2))
  have hpoly : (6 * L ^ 2 + 6) * L ≤ 2 ^ (L / 3) := by
    have hL2 : 6 ≤ L ^ 2 := (by omega : 6 ≤ L).trans (Nat.le_self_pow (by decide) L)
    have hL_4q : L ≤ 4 * (L / 3) := by omega
    calc (6 * L ^ 2 + 6) * L ≤ 7 * L ^ 2 * L := by gcongr; omega
      _ ≤ 7 * (4 * (L / 3)) ^ 2 * (4 * (L / 3)) := by gcongr
      _ = 448 * (L / 3) ^ 3 := by ring
      _ ≤ L / 3 * (L / 3) ^ 3 := by gcongr; omega
      _ ≤ 2 ^ (L / 3) := by
        rw [← pow_succ']; exact Nat.pow_le_two_pow (by decide) (by omega)
  calc 2 ^ (2 * (Nat.log 2 (max P.cap 2) / 3)) * (6 * Nat.clog 2 (max P.paddedUniv 2) + 6) * r
      = 2 ^ (2 * (L / 3)) * (6 * Nat.clog 2 (max P.paddedUniv 2) + 6) * r := by
        rw [hcap, max_eq_left hn2, ← hL_eq]
    _ ≤ 2 ^ (2 * (L / 3)) * ((6 * L ^ 2 + 6) * L) := by rw [Nat.mul_assoc]; gcongr
    _ ≤ 2 ^ (2 * (L / 3)) * 2 ^ (L / 3) := Nat.mul_le_mul_left _ hpoly
    _ = 2 ^ (3 * (L / 3)) := by ring
    _ ≤ n := (Nat.pow_le_pow_right Nat.two_pos (by omega)).trans hn_2L

/-- The shared leaf tables (matching permutations and minimap headers) and the carry-less
multiplication table take at most `3 * n / r` bits. -/
private theorem leafAndClmul_of_schedule (P : TreeSchedule) {n r L t : ℕ}
    (hn2 : 2 ≤ n) (hL_eq : L = Nat.log 2 n) (h2M : 2560000 ≤ L)
    (ht_eq : t = Nat.log 2 L) (ht_ge : 300 ≤ t) (hr10 : r ^ 10 ≤ L)
    (hcap : P.cap = n)
    (hnf_k_le : P.nFloor P.depth ≤ 2 * r ^ 9)
    (hid_k_def : P.idBits P.depth = 4 * Nat.clog 2 (2 * max (P.nFloor P.depth) 1))
    (hpad_L2 : P.paddedUniv ≤ 2 ^ (L ^ 2)) :
    let U_leaf := 2 ^ P.idBits P.depth
    let n_leaf := P.nLow P.depth
    let matchBits := U_leaf * (U_leaf + n_leaf) * Nat.clog 2 (U_leaf + n_leaf + 1)
    let minimapTabBits := U_leaf *
        Minimap.headerUniv U_leaf n_leaf (P.quotUniv P.depth * P.valBound) n_leaf *
        Nat.clog 2 (2 * n_leaf ^ 2 + 2)
    let clmulBits := 2 ^ (2 * (Nat.log 2 (max P.cap 2) / 3)) *
        (6 * Nat.clog 2 (max P.paddedUniv 2) + 6)
    (matchBits + minimapTabBits + clmulBits) * r ≤ 3 * n := by
  intro U_leaf n_leaf matchBits minimapTabBits clmulBits
  have hd2 := P.two_le_depth
  have ht_pow : 2 ^ t ≤ L := ht_eq ▸ Nat.pow_log_le_self 2 (by omega)
  have hr_le_L : r ≤ L := (Nat.le_self_pow (by decide : 10 ≠ 0) r).trans hr10
  have hn_2L : 2 ^ L ≤ n := hL_eq ▸ Nat.pow_log_le_self 2 (by omega)
  have hclmul_r : clmulBits * r ≤ n :=
    clmul_of_schedule P hn2 hL_eq h2M hr_le_L hcap hpad_L2
  set s := t / 10
  have hp : 1024 ≤ 2 ^ (9 * s + 10) :=
    Nat.pow_le_pow_right Nat.two_pos (by omega : 10 ≤ 9 * s + 10)
  have hr_2s : r ≤ 2 ^ (s + 1) := by
    refine (Nat.pow_le_pow_iff_left (by decide : 10 ≠ 0)).mp ?_
    rw [← Nat.pow_mul]
    exact hr10.trans ((ht_eq ▸ Nat.lt_pow_succ_log_self Nat.one_lt_two L).le.trans
      (Nat.pow_le_pow_right Nat.two_pos (by omega)))
  have hnf_s : P.nFloor P.depth ≤ 2 ^ (9 * s + 10) :=
    hnf_k_le.trans ((Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hr_2s 9)).trans_eq (by ring))
  have hid : P.idBits P.depth ≤ 36 * s + 44 := by
    have : Nat.clog 2 (2 * max (P.nFloor P.depth) 1) ≤ 9 * s + 11 :=
      Nat.clog_le_of_le_pow (by
        rw [max_eq_left (P.nFloor_pos P.depth le_rfl), pow_succ']; omega)
    omega
  obtain ⟨hn_leaf_nf, hn_leaf_U⟩ : n_leaf ≤ P.nFloor P.depth ∧ n_leaf ≤ U_leaf :=
    P.nLow_le (by omega) le_rfl
  have hn_leaf_le : n_leaf ≤ 2 ^ (9 * s + 10) := hn_leaf_nf.trans hnf_s
  -- every exponent below is at most `48 * (s + 1) * 2 ^ (9 * s + 10)`, which is at most `L / 2`
  have hexp_half : 48 * (s + 1) * 2 ^ (9 * s + 10) ≤ L / 2 := by
    have hd : s - 30 < 2 ^ (s - 30) := Nat.lt_two_pow_self
    have h2t : 2 ^ t = 2 * 2 ^ (t - 1) := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    calc 48 * (s + 1) * 2 ^ (9 * s + 10)
        ≤ 2 ^ 11 * 2 ^ (s - 30) * 2 ^ (9 * s + 10) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (11 + (s - 30) + (9 * s + 10)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (t - 1) := Nat.pow_le_pow_right Nat.two_pos (by omega)
      _ ≤ L / 2 := by omega
  have hexp_lin : 48 * (s + 1) * 1024 ≤ L / 2 := (Nat.mul_le_mul_left _ hp).trans hexp_half
  have hr_half : r ≤ 2 ^ (L / 2) := hr_2s.trans (Nat.pow_le_pow_right Nat.two_pos (by omega))
  have hmatch_le : matchBits ≤ 2 ^ (L / 2) := by
    have hU1 : 1 ≤ 2 ^ P.idBits P.depth := Nat.two_pow_pos _
    have hcl : Nat.clog 2 (U_leaf + n_leaf + 1) ≤ P.idBits P.depth + 2 :=
      Nat.clog_le_of_le_pow (by rw [pow_add]; omega)
    calc matchBits
        ≤ 2 ^ P.idBits P.depth * (2 * 2 ^ P.idBits P.depth) * 2 ^ (P.idBits P.depth + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (hcl.trans Nat.lt_two_pow_self.le)
      _ = 2 ^ (3 * P.idBits P.depth + 3) := by ring
      _ ≤ 2 ^ (L / 2) := Nat.pow_le_pow_right Nat.two_pos (by omega)
  have hminimap_le : minimapTabBits ≤ 2 ^ (L / 2) := by
    have hU_pow : U_leaf ≤ 2 ^ (36 * s + 44) := Nat.pow_le_pow_right Nat.two_pos hid
    have hcl2 : Nat.clog 2 (2 * n_leaf ^ 2 + 2) ≤ 18 * s + 22 := by
      have h1 : 1 ≤ (2 ^ (9 * s + 10)) ^ 2 := Nat.one_le_pow _ _ (Nat.two_pow_pos _)
      have h2 := Nat.pow_le_pow_left hn_leaf_le 2
      exact Nat.clog_le_of_le_pow (by
        rw [show 18 * s + 22 = 2 + (9 * s + 10) * 2 by ring, pow_add, pow_mul]; omega)
    calc minimapTabBits
        ≤ (U_leaf * U_leaf.choose n_leaf * (2 * n_leaf) ^ n_leaf) * 2 ^ (18 * s + 22) :=
          Nat.mul_le_mul (Minimap.queryTableSize_le (P.nLow_pos le_rfl))
            (hcl2.trans Nat.lt_two_pow_self.le)
      _ ≤ 2 ^ (36 * s + 44) * (2 ^ (36 * s + 44)) ^ n_leaf * (2 ^ (9 * s + 11)) ^ n_leaf *
            2 ^ (18 * s + 22) := by
          gcongr
          · exact (Nat.choose_le_pow ..).trans (Nat.pow_le_pow_left hU_pow _)
          · rw [pow_succ']; omega
      _ = 2 ^ ((45 * s + 55) * n_leaf + (54 * s + 66)) := by
          rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (L / 2) := Nat.pow_le_pow_right Nat.two_pos <|
          calc (45 * s + 55) * n_leaf + (54 * s + 66)
              ≤ (45 * s + 55) * 2 ^ (9 * s + 10) + (3 * s - 7) * 2 ^ (9 * s + 10) :=
                Nat.add_le_add (Nat.mul_le_mul_left _ hn_leaf_le)
                  ((by omega : 54 * s + 66 ≤ (3 * s - 7) * 1024).trans (Nat.mul_le_mul_left _ hp))
            _ = 48 * (s + 1) * 2 ^ (9 * s + 10) := by rw [← Nat.add_mul]; congr 1; omega
            _ ≤ L / 2 := hexp_half
  have hm_r := mul_le_of_le_two_pow_half hmatch_le hr_half hn_2L
  have hmm_r := mul_le_of_le_two_pow_half hminimap_le hr_half hn_2L
  rw [Nat.add_mul, Nat.add_mul]
  omega

/-- The metadata of a node at a level `j ≥ 3` takes at most `t ^ 15` bits, when the key IDs at
levels `j - 1` and `j` have `O(t)` bits and the expected load of the node is at most `t ^ 11`. -/
private theorem nodeMetaBits_le_of_schedule (P : TreeSchedule) {t j : ℕ} (ht_ge : 300 ≤ t)
    (hj3 : 3 ≤ j) (hjk : j ≤ P.depth)
    (hid : P.idBits (j - 1) ≤ 444 * t ∧ P.idBits j ≤ 444 * t) (hnf : P.nFloor j ≤ t ^ 11)
    (hsq : j < P.depth → (P.routerSeedBits j) ^ 2 ≤ P.nFloor j) :
    P.nodeMetaBits j ≤ t ^ 15 := by
  obtain ⟨hid_prev, hid_cur⟩ := hid
  have ht11 : 1 ≤ t ^ 11 := Nat.one_le_pow _ _ (by omega)
  have h45 : 45000 * t ^ 12 ≤ t ^ 15 :=
    (Nat.mul_le_mul_right _ ((by norm_num : 45000 ≤ 300 ^ 3).trans
      (Nat.pow_le_pow_left ht_ge 3))).trans_eq (by ring)
  -- all node metadata is a product of a factor `O(t ^ 11)` and a factor `O(t)`
  have hmul : ∀ {a b : ℕ} (c₁ c₂ : ℕ), a ≤ c₁ * t ^ 11 → b ≤ c₂ * t →
      a * b ≤ c₁ * c₂ * t ^ 12 := fun c₁ c₂ ha hb =>
    (Nat.mul_le_mul ha hb).trans_eq (by ring)
  have hdel := P.delta_lt_nFloor j (by omega) hjk
  obtain ⟨hlo_nf, hlo_id⟩ := P.nLow_le (by omega : 1 ≤ j) hjk
  have hseed : P.nodeHashSeedBits j ≤ 2671 * t ^ 12 := by
    have hic := P.idCompressorSeedBits_le_of_two_le (by omega : 2 ≤ j) hjk
    have hrsb : (if j < P.depth then P.routerSeedBits j else 0) ≤ t ^ 11 := by
      split_ifs with hlt
      · exact (Nat.le_self_pow two_ne_zero _).trans ((hsq hlt).trans hnf)
      · exact Nat.zero_le _
    have h11 : t ^ 11 ≤ t ^ 12 := Nat.pow_le_pow_right (by omega) (by decide)
    have h1 : t ≤ t ^ 12 := Nat.le_self_pow (by decide) t
    dsimp only [TreeSchedule.nodeHashSeedBits]
    rw [ite_eq_right (by omega)]
    omega
  have hwait := (P.waitingListBits_le_of_two_le (by omega : 2 ≤ j) hjk).trans
    (hmul 5 444 (by omega) hid_prev)
  dsimp only [TreeSchedule.nodeMetaBits]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  split_ifs with hlt
  · have htc := P.tableCap_le_nLow (by omega : 2 ≤ j) hjk
    have hstb := (succinctTableMetaBits_le (htc.trans hlo_id)).trans
      ((Nat.add_mul ..).ge.trans (hmul 84 446 (by omega) (by omega)))
    omega
  · obtain rfl : j = P.depth := by omega
    have hcl : Nat.clog 2 (Nat.choose (2 ^ P.idBits P.depth) (P.nLow P.depth) *
        (2 * P.nLow P.depth) ^ P.nLow P.depth) ≤ 1 * 889 * t ^ 12 := by
      refine (Nat.clog_le_of_le_pow ?_).trans (hmul 1 889
        (by omega : P.nLow P.depth ≤ 1 * t ^ 11)
        (by omega : 2 * P.idBits P.depth + 1 ≤ 889 * t))
      calc Nat.choose (2 ^ P.idBits P.depth) (P.nLow P.depth) *
            (2 * P.nLow P.depth) ^ P.nLow P.depth
          ≤ (2 ^ P.idBits P.depth) ^ P.nLow P.depth *
              (2 ^ (P.idBits P.depth + 1)) ^ P.nLow P.depth :=
            Nat.mul_le_mul (Nat.choose_le_pow ..)
              (Nat.pow_le_pow_left (by rw [pow_succ']; omega) _)
        _ = 2 ^ (P.nLow P.depth * (2 * P.idBits P.depth + 1)) := by
            rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    omega

/-- The shared level-`3` DFS subtree lookup table takes at most `n / r` bits. -/
private theorem dfs_of_schedule (P : TreeSchedule) {n r L t : ℕ}
    (hn2 : 2 ≤ n) (hL_eq : L = Nat.log 2 n) (h2M : 2560000 ≤ L)
    (ht_eq : t = Nat.log 2 L) (ht_ge : 300 ≤ t) (hr_le_L : r ≤ L)
    (hcap : P.cap = n) (hk_le_r : P.depth ≤ r)
    (hk_3t : 3 ≤ P.depth → P.depth ≤ 3 * t)
    (hid_j : 3 ≤ P.depth → ∀ j, 3 ≤ j → j ≤ P.depth →
      P.idBits (j - 1) ≤ 444 * t ∧ P.idBits j ≤ 444 * t)
    (hnf_j : 3 ≤ P.depth → ∀ j, 3 ≤ j → j ≤ P.depth → P.nFloor j ≤ t ^ 11)
    (hrat_j : 3 ≤ P.depth → ∀ j, 3 ≤ j → j ≤ P.depth → P.numNodes j / P.numNodes 3 ≤ t ^ 11)
    (hsq_j : ∀ j < P.depth, (P.routerSeedBits j) ^ 2 ≤ P.nFloor j) :
    (if 3 ≤ P.depth then
      2 ^ (P.subtreeMetaBits 3 + P.idBits 3) * (Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3)
    else 0) * r ≤ n := by
  split_ifs with h3
  · have ht_pow : 2 ^ t ≤ L := ht_eq ▸ Nat.pow_log_le_self 2 (by omega)
    have hn_2L : 2 ^ L ≤ n := hL_eq ▸ Nat.pow_log_le_self 2 (by omega)
    have ht31_L : 512 * t ^ 31 ≤ L := by
      have hd : t / 32 - 9 < 2 ^ (t / 32 - 9) := Nat.lt_two_pow_self
      have ht_2m : t ≤ 2 ^ 9 * 2 ^ (t / 32 - 9) := by omega
      rw [← pow_add, Nat.add_sub_cancel' (by omega)] at ht_2m
      calc 512 * t ^ 31 ≤ 2 ^ 9 * (2 ^ (t / 32)) ^ 31 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht_2m 31)
        _ = 2 ^ (9 + t / 32 * 31) := by rw [← pow_mul, ← pow_add]
        _ ≤ L := (Nat.pow_le_pow_right Nat.two_pos (by omega)).trans ht_pow
    have hsub_half : P.subtreeMetaBits 3 + P.idBits 3 ≤ L / 2 := by
      have hsum : P.subtreeMetaBits 3 ≤ 3 * t * (t ^ 11 * t ^ 15) := by
        refine (Finset.sum_le_card_nsmul _ _ (t ^ 11 * t ^ 15) fun j hj => ?_).trans ?_
        · obtain ⟨hj3, hjk⟩ := mem_Icc.mp hj
          exact Nat.mul_le_mul (hrat_j h3 j hj3 hjk) (nodeMetaBits_le_of_schedule P ht_ge hj3 hjk
            (hid_j h3 j hj3 hjk) (hnf_j h3 j hj3 hjk) (hsq_j j))
        · rw [Nat.card_Icc, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (by have := hk_3t h3; omega)
      have hid3 := (hid_j h3 3 le_rfl h3).2
      have ht27 : t ≤ t ^ 27 := Nat.le_self_pow (by decide) t
      have h447 : 447 * t ^ 27 ≤ t ^ 31 :=
        (Nat.mul_le_mul_right _ ((by norm_num : 447 ≤ 300 ^ 4).trans
          (Nat.pow_le_pow_left ht_ge 4))).trans_eq (by ring)
      rw [show 3 * t * (t ^ 11 * t ^ 15) = 3 * t ^ 27 by ring] at hsum
      omega
    have hmul_L : (Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3) * r ≤ 2 ^ (L / 2) := by
      have hL2 := Nat.add_two_le_two_pow (by omega : 2 ≤ L)
      have hn_lt : n < 2 ^ (L + 1) := hL_eq ▸ Nat.lt_pow_succ_log_self Nat.one_lt_two n
      have hcl : Nat.clog 2 (P.cap + P.depth + 2) ≤ L + 2 :=
        Nat.clog_le_of_le_pow (by rw [pow_succ']; omega)
      have ht31 : t ≤ t ^ 31 := Nat.le_self_pow (by decide) t
      have hid3 := (hid_j h3 3 le_rfl h3).2
      calc (Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3) * r
          ≤ 5 * (L / 2) * (3 * (L / 2)) := Nat.mul_le_mul (by omega) (by omega)
        _ = 15 * (L / 2) ^ 2 := by ring
        _ ≤ L / 2 * (L / 2) ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ (L / 2) := by
          rw [← pow_succ']; exact Nat.pow_le_two_pow (by decide) (by omega)
    rw [Nat.mul_assoc]
    exact mul_le_of_le_two_pow_half (Nat.pow_le_pow_right Nat.two_pos hsub_half) hmul_L hn_2L
  · simp

theorem sharedTables_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).sharedTablesBits * redundancyRatio n R ≤ 4 * n := by
  obtain ⟨hr256, _, hr10⟩ := h.redundancyRatio_bounds
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  have hp := h.mul_param_le_log le_rfl
  have ht_ge := h.three_hundred_le_log_log
  have hk2 := two_le_treeDepth U (redundancyRatio n R)
  have hkr := h.treeDepth_le_redundancyRatio
  have hdepth := canonicalSchedule_depth h
  set P := canonicalSchedule h
  set r := redundancyRatio n R
  set k := treeDepth U r
  set L := Nat.log 2 n
  set t := Nat.log 2 L
  have hpad_L2 : P.paddedUniv ≤ 2 ^ L ^ 2 :=
    (paddedUniv_le_two_pow_mul_log h).trans (Nat.pow_le_pow_right Nat.two_pos
      (by rw [sq]; exact Nat.mul_le_mul_right _ (by omega)))
  have hnf_k_le : P.nFloor P.depth ≤ 2 * r ^ 9 := by
    have hhi := (targetSize_le_nFloor_and_lt (hT_pos k le_rfl) (hT_le k le_rfl)).2
    rw [targetSize_eq_levelScale_pow (by omega), levelScale, ite_eq_right (lt_irrefl _)] at hhi
    rw [canonicalSchedule_nFloor_eq h, hdepth]
    exact hhi.le
  have h1 := leafAndClmul_of_schedule P (L := L) (t := t) h.two_le_n rfl (by omega) rfl ht_ge
    hr10 (canonicalSchedule_cap h) hnf_k_le
    (by rw [canonicalSchedule_idBits_eq h _, canonicalSchedule_nFloor_eq h _]; rfl) hpad_L2
  have hiter2_le : Nat.iterLog 2 U ≤ 3 * t :=
    Nat.lt_succ_iff.mp <| Nat.log_lt_of_lt_pow' (Nat.succ_ne_zero _) <|
      calc Nat.log 2 U ≤ (2 ^ (t + 1)) ^ 2 := h.log_univ_le_sq_log.trans
            (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self Nat.one_lt_two L).le 2)
        _ = 2 ^ (2 * t + 2) := by ring
        _ < 2 ^ (3 * t + 1) := Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
  -- from level `3` on, every level scale is at most `3 * t`
  have h4r : 3 ≤ P.depth → 4 * r < 3 * t + 1 := fun h3 =>
    (lt_iterLog_of_lt_treeDepth le_rfl (by omega : 2 < k)).trans_le (by omega)
  have hls_3t : 3 ≤ P.depth → ∀ j, 3 ≤ j → levelScale U r k j ≤ 3 * t := fun h3 j hj3 => by
    have := h4r h3
    dsimp only [levelScale]
    split_ifs
    · exact (Nat.iterLog_anti_left U (by omega : 2 ≤ j)).trans hiter2_le
    · omega
  have hscale_t11 : 3 ≤ P.depth → ∀ j, 3 ≤ j → 2 * levelScale U r k j ^ 9 ≤ t ^ 11 :=
    fun h3 j hj3 =>
      calc 2 * levelScale U r k j ^ 9
          ≤ 2 * (3 * t) ^ 9 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hls_3t h3 j hj3) 9)
        _ = 2 * 3 ^ 9 * t ^ 9 := by ring
        _ ≤ t ^ 2 * t ^ 9 := Nat.mul_le_mul_right _
            ((by norm_num : 2 * 3 ^ 9 ≤ 300 ^ 2).trans (Nat.pow_le_pow_left ht_ge 2))
        _ = t ^ 11 := by ring
  have h2 := dfs_of_schedule P (L := L) (t := t) h.two_le_n rfl (by omega) rfl ht_ge
    h.redundancyRatio_le_log (canonicalSchedule_cap h) (hdepth ▸ hkr)
    (fun h3 => by have := h4r h3; omega)
    (fun h3 j hj3 hjk => by
      have hpred : P.idBits (j - 1) ≤ 148 * (3 * t) :=
        (canonicalSchedule_idBits_eq h (j - 1)).trans_le ((idBits_pred_le_mul_levelScale hr256
          (by omega : 2 ≤ j) (by omega) (hT_pos (j - 1) (by omega))
          (hT_le (j - 1) (by omega))).trans (Nat.mul_le_mul_left 148 (hls_3t h3 j hj3)))
      have hstep := P.idBits_step_le (j - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hstep
      exact ⟨by omega, by omega⟩)
    (fun h3 j hj3 hjk => by
      have hhi := (targetSize_le_nFloor_and_lt (hT_pos j (by omega)) (hT_le j (by omega))).2
      rw [targetSize_eq_levelScale_pow (by omega)] at hhi
      exact (canonicalSchedule_nFloor_eq h j).trans_le (hhi.le.trans (hscale_t11 h3 j hj3)))
    (fun h3 j hj3 hjk => by
      have hhi3 := (numNodes_mul_targetSize_bounds (hT_pos 3 (by omega)) (hT_le 3 (by omega))).2
      have hNj := (Nat.le_mul_of_pos_right _ (hT_pos j (by omega))).trans
        (numNodes_mul_targetSize_bounds (hT_pos j (by omega)) (hT_le j (by omega))).1
      rw [targetSize_eq_levelScale_pow (by decide : 1 ≤ 3)] at hhi3
      refine (Nat.div_le_of_le_mul ?_).trans (hscale_t11 h3 3 le_rfl)
      rw [canonicalSchedule_numNodes_eq h hjk, canonicalSchedule_numNodes_eq h h3]
      exact (hNj.trans hhi3.le).trans_eq (by ring))
    (fun j hlt => routerSeedBits_sq_le_nFloor h hlt)
  exact (Nat.add_mul ..).le.trans ((Nat.add_le_add h1 h2).trans (by omega))

/-- Operational metadata bit budget `(canonicalSchedule h).treeMetaBits` is bounded by
`n / redundancyRatio n R` across `ValidRegime`. -/
theorem treeMeta_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).treeMetaBits * redundancyRatio n R ≤ n := by
  set L := Nat.log 2 n
  have hp : 2560000 * (q_min + p_max + 4) ≤ L := h.mul_param_le_log le_rfl
  have hn_lt : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hcl : Nat.clog 2 ((canonicalSchedule h).cap + 1) ≤ L + 1 :=
    Nat.clog_le_of_le_pow (by rw [canonicalSchedule_cap]; omega)
  calc (canonicalSchedule h).treeMetaBits * redundancyRatio n R
      ≤ 2 * L * L := Nat.mul_le_mul (by dsimp only [TreeSchedule.treeMetaBits]; omega)
        h.redundancyRatio_le_log
    _ ≤ L * L * L := by gcongr; omega
    _ = L ^ 3 := by ring
    _ ≤ 2 ^ L := Nat.pow_le_two_pow (by decide) (by omega)
    _ ≤ n := Nat.pow_log_le_self 2 (by have := h.two_le_n; omega)

private theorem redundancySlack_sub_one_of_schedule (P : TreeSchedule) {n r : ℕ}
    (hb1 : (3 * P.numNodes P.depth + 3 * (P.cap - P.numNodes P.depth * P.nLow P.depth)) * r ≤
      9 * n)
    (hb2 : ((∑ ℓ ∈ Finset.Ico 2 P.depth,
        P.numNodes ℓ *
          (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
            P.tableCap ℓ * Nat.clog 2 (2 * (P.nFloor ℓ + 1)))) +
      P.numNodes 1 *
        (succinctTableMetaBits (P.idBits 1) (P.tableCap 1) +
          P.tableCap 1 *
            (Nat.clog 2 (2 * (P.nFloor 1 + 1)) + Nat.clog 2 (P.tableCap 1 + 1)))) * r ≤
      72000 * n)
    (hb3 : ((P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) *
        Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap) + P.rootPoolDirBits) * r ≤ 8 * n)
    (hb4 : (P.allWaitingListsBits + P.allHashSeedsBits) * r ≤ 1700 * n)
    (hb5 : P.sharedTablesBits * r ≤ 4 * n)
    (hb6 : P.treeMetaBits * r ≤ n) :
    (P.redundancySlack - 1) * r ≤ 74000 * n := by
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add hb1 hb2) hb3) hb4) hb5) hb6
  simp only [← Nat.add_mul] at hsum
  refine (Nat.mul_le_mul_right r ?_).trans (hsum.trans (by omega))
  dsimp only [TreeSchedule.redundancySlack]
  omega

/-- Total redundancy slack `(canonicalSchedule h).redundancySlack` is bounded uniformly across all
`1 ≤ V` by `150000 * effRedundancy n R` across `ValidRegime`. -/
theorem redundancySlack_le_mul_effRedundancy {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).redundancySlack ≤ 150000 * effRedundancy n R := by
  have hRe1 : 1 ≤ effRedundancy n R := effRedundancy_pos h.redundancy_pos n
  have hsub_r := redundancySlack_sub_one_of_schedule (canonicalSchedule h)
    (leaf_and_deficit_slack_le h) (nonLeaf_tables_slack_le h)
    (rootExtra_and_poolDir_slack_le h) (waitingLists_and_hashSeeds_slack_le h)
    (sharedTables_slack_le h) (treeMeta_slack_le h)
  have hsub_Re := le_two_mul_effRedundancy_of_mul_ratio_le h.redundancy_pos
    h.one_le_redundancyRatio hsub_r
  omega

/-- Explicit universal constant `O(1)` in the pure tree bit-budget bound
`totalTreeBits ≤ infoBits U V n + spaceConst * R`. -/
def spaceConst : ℕ := 160000

/-- **Headline Section 5 Pure Tree Bit-Budget Bound** (`[LiLiangYuZhou2024, Sections 5.2 & 5.6]`):
across all `ValidRegime U V n R p_min q_min p_max q_max` (with no upper bound on `V`),
the arithmetic bit budget `totalTreeBits` of the intended Section 5 layout satisfies
`(canonicalSchedule h).totalTreeBits ≤ infoBits U V n + spaceConst * R`
(with `spaceConst = 160000`). Note that `totalTreeBits` computes the arithmetic bit budget of
the intended layout and is not tied to an operational state by an explicit Word-RAM bit-packing
encoding. -/
theorem totalTreeBits_le_infoBits_add {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).totalTreeBits ≤ infoBits U V n + spaceConst * R := by
  have hU3 : 3 * (canonicalSchedule h).cap ≤ (canonicalSchedule h).paddedUniv := by
    have h2n := h.two_mul_n_le_univ
    have hpad := (canonicalSchedule h).univ_le_padded
    rw [canonicalSchedule_univ, canonicalSchedule_cap] at hpad
    rw [canonicalSchedule_cap]
    dsimp only [TreeSchedule.paddedUniv, TreeSchedule.branchFactor]
    omega
  have htot := (canonicalSchedule h).totalTreeBits_le_padded_infoBits_add (fun ℓ _ hlt => by
    rw [canonicalSchedule_cap, canonicalSchedule_nFloor_div_eq h hlt.le]
    exact (Nat.lt_mul_div_succ n ((canonicalSchedule h).numNodes_pos ℓ)).le) hU3
  rw [canonicalSchedule_valBound, canonicalSchedule_cap] at htot
  have hpad_info := infoBits_paddedUniv_le h
  have hslack := redundancySlack_le_mul_effRedundancy h
  have hRe_pos : 1 ≤ effRedundancy n R := effRedundancy_pos h.redundancy_pos n
  have hRe_le : effRedundancy n R ≤ R := effRedundancy_le n R
  dsimp only [spaceConst]
  omega

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
