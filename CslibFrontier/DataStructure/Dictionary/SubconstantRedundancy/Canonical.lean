/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.Schedule
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.LogStar
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Canonical Large-Parameter Schedule and Probabilistic Concentration Readiness

This module builds on `CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.Schedule` to
formalize the polynomial-universe large-parameter regime (`ValidRegime`), the canonical Section 5
parameter instantiation (`canonicalSchedule`), and its probabilistic concentration readiness
(`canonicalSchedule_concentrationReady`) ([LiLiangYuZhou2024, Sections 5.1–5.2 and 5.4–5.6];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 25–36 / printed pp. 24–35).
For the end-to-end pure bit-budget bound `totalTreeBits ≤ infoBits U V n + spaceConst * R`, see
`Params.lean`.

## Scope and adaptations

* **Clamped redundancy (`effRedundancy`) and small-node child-router regime switch**:
  `effRedundancy n R` clamps `R` below `n / max 256 (2 ^ log* n)` so `r ≥ 256` and
  `2 ^ log* n ≤ r` hold across all `R ≤ n` without inflating `thresholdN`. Nodes with
  `nLow ℓ < childRouterThreshold epsInv alphaInv` switch from Thorup's `DoubleTabulation` to exact
  `(2 * childRouterHalfInd (nHigh ℓ))`-wise `trinomialPolyHash`, avoiding `childRouterThreshold` in
  `thresholdN`.
* **Out-of-scope gaps**: Word-RAM `Memory.Prog` compilation, Section 4 small-`R` adapter trees
  (`R < n / log₂ ^ 0.1 n`), strong history independence, dynamic resizing in `|S|`, and
  super-polynomial key universes (`U > n ^ (1 + α_max)`) are out of scope here.

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.routerEpsInv`, `routerAlphaInv`,
  `thresholdLogN`, `thresholdN`, `ValidRegime`, `canonicalSchedule`.

## Main results

* `ValidRegime.treeDepth_le_logStar_add_four`,
  `ValidRegime.treeDepth_add_one_le_three_mul_logStar`: stopping-depth bounds in terms of `log* n`.
* `canonicalSchedule_concentrationReady`: `canonicalSchedule` satisfies `ConcentrationReady`.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

/-! ## Section 2: Large-parameter polynomial-`U` regime and `canonicalSchedule` -/

/-- Inverse space exponent `ε_inv = max 12 (2 * (p_max + 3))` for `DoubleTabulation` child
routers across polynomial universes `U ≤ n ^ (1 + p_max / q_max)`. -/
def routerEpsInv (p_max : ℕ) : ℕ :=
  max 12 (2 * (p_max + 3))

theorem routerEpsInv_eq (p_max : ℕ) :
    routerEpsInv p_max = max 12 (2 * (p_max + 3)) := by rfl

/-- Gap exponent `α_inv = max q_min 1 + 1` (`≥ 2`) for `DoubleTabulation` child routers across
polynomial universes `n ^ (1 + p_min / q_min) ≤ U`. -/
def routerAlphaInv (q_min : ℕ) : ℕ :=
  max q_min 1 + 1

theorem routerAlphaInv_eq (q_min : ℕ) :
    routerAlphaInv q_min = max q_min 1 + 1 := by rfl

/-- Base-2 logarithm threshold `L₀(q_min, p_max)` above which `2 ^ L₀ ≤ n` ensures all
poly-logarithmic and polynomial-gap inequalities in Section 5. -/
def thresholdLogN (q_min p_max : ℕ) : ℕ :=
  max (2 ^ 250 * 2 ^ 50) (2560000 * (max q_min 1 + p_max + 4) ^ 4)

/-- Minimum dictionary capacity `n₀(q_min, p_max) = 2 ^ thresholdLogN q_min p_max` for the
Section 5 large-parameter polynomial-`U` regime. -/
@[expose]
def thresholdN (q_min p_max : ℕ) : ℕ :=
  2 ^ thresholdLogN q_min p_max

theorem thresholdN_eq (q_min p_max : ℕ) :
    thresholdN q_min p_max = 2 ^ thresholdLogN q_min p_max := rfl

theorem two_pow_300_le_thresholdLogN (q_min p_max : ℕ) :
    2 ^ 250 * 2 ^ 50 ≤ thresholdLogN q_min p_max :=
  le_max_left _ _

theorem poly_le_thresholdLogN (q_min p_max : ℕ) :
    2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ thresholdLogN q_min p_max :=
  le_max_right _ _

/-- Large-parameter polynomial-universe regime of `[LiLiangYuZhou2024, Section 5]`
(`n / (log₂ n) ^ 0.1 ≤ R ≤ n`, `n ^ (1 + p_min / q_min) ≤ U ≤ n ^ (1 + p_max / q_max)`,
`1 ≤ V`, `thresholdN q_min p_max ≤ n`). -/
structure ValidRegime (U V n R p_min q_min p_max q_max : ℕ) : Prop where
  p_min_pos : 1 ≤ p_min
  q_min_pos : 1 ≤ q_min
  q_max_pos : 1 ≤ q_max
  val_pos : 1 ≤ V
  n_ge_threshold : thresholdN q_min p_max ≤ n
  univ_lower : n ^ (q_min + p_min) ≤ U ^ q_min
  univ_upper : U ^ q_max ≤ n ^ (q_max + p_max)
  redundancy_pos : 1 ≤ R
  redundancy_le : R ≤ n
  redundancy_lower : n ^ 10 ≤ R ^ 10 * Nat.log 2 n

namespace ValidRegime

variable {U V n R p_min q_min p_max q_max : ℕ}

theorem thresholdLogN_le_log (h : ValidRegime U V n R p_min q_min p_max q_max) :
    thresholdLogN q_min p_max ≤ Nat.log 2 n :=
  (Nat.le_log_iff_pow_le Nat.one_lt_two
    (Nat.pos_of_ne_zero (Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le h.n_ge_threshold))).ne').mpr
    h.n_ge_threshold

theorem four_le_thresholdLogN (q_min p_max : ℕ) :
    4 ≤ thresholdLogN q_min p_max :=
  have h1 : 1 ≤ (max q_min 1 + p_max + 4) ^ 4 := Nat.one_le_pow 4 _ (by omega)
  (by omega : 4 ≤ 2560000 * (max q_min 1 + p_max + 4) ^ 4).trans (poly_le_thresholdLogN q_min p_max)

theorem four_le_log (h : ValidRegime U V n R p_min q_min p_max q_max) :
    4 ≤ Nat.log 2 n :=
  (four_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log

theorem poly_le_log (h : ValidRegime U V n R p_min q_min p_max q_max) :
    2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ Nat.log 2 n :=
  (poly_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log

theorem mul_param_le_log (h : ValidRegime U V n R p_min q_min p_max q_max) {c : ℕ}
    (hc : c ≤ 2560000) :
    c * (q_min + p_max + 4) ≤ Nat.log 2 n :=
  (Nat.mul_le_mul hc ((by omega : q_min + p_max + 4 ≤ max q_min 1 + p_max + 4).trans
    (Nat.le_self_pow (by decide) _))).trans h.poly_le_log

theorem three_hundred_le_log_log (h : ValidRegime U V n R p_min q_min p_max q_max) :
    300 ≤ Nat.log 2 (Nat.log 2 n) := by
  refine (Nat.le_log_iff_pow_le Nat.one_lt_two (by have := h.four_le_log; omega)).mpr ?_
  rw [show (300 : ℕ) = 250 + 50 by decide, Nat.pow_add 2 250 50]
  exact (two_pow_300_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log

theorem two_le_n (h : ValidRegime U V n R p_min q_min p_max q_max) : 2 ≤ n :=
  (Nat.pow_le_pow_right Nat.two_pos
    (by have := four_le_thresholdLogN q_min p_max; omega : 1 ≤ _)).trans h.n_ge_threshold

theorem univ_le_pow (h : ValidRegime U V n R p_min q_min p_max q_max) :
    U ≤ n ^ (p_max + 1) := by
  have hexp : q_max + p_max ≤ q_max * (p_max + 1) := by have := h.q_max_pos; nlinarith
  have hpow : U ^ q_max ≤ (n ^ (p_max + 1)) ^ q_max := calc
    U ^ q_max ≤ n ^ (q_max + p_max) := h.univ_upper
    _ ≤ n ^ (q_max * (p_max + 1)) := Nat.pow_le_pow_right (by have := h.two_le_n; omega) hexp
    _ = (n ^ (p_max + 1)) ^ q_max := by rw [← Nat.pow_mul, Nat.mul_comm]
  exact (Nat.pow_le_pow_iff_left (by have := h.q_max_pos; omega)).mp hpow

theorem n_pow_succ_le_univ_pow (h : ValidRegime U V n R p_min q_min p_max q_max) :
    n ^ (q_min + 1) ≤ U ^ q_min :=
  (Nat.pow_le_pow_right (by have := h.two_le_n; omega)
    (by have := h.p_min_pos; omega)).trans h.univ_lower

theorem two_mul_n_le_univ (h : ValidRegime U V n R p_min q_min p_max q_max) :
    2 * n ≤ U := by
  have h2n : 2 ^ q_min ≤ n :=
    (Nat.pow_le_pow_right Nat.two_pos (by
      have := h.mul_param_le_log (by decide : 1 ≤ 2560000); omega)).trans
      (Nat.pow_log_le_self 2 (by have := h.two_le_n; omega))
  have hpow : (2 * n) ^ q_min ≤ U ^ q_min := calc
    (2 * n) ^ q_min = 2 ^ q_min * n ^ q_min := Nat.mul_pow 2 n q_min
    _ ≤ n * n ^ q_min := Nat.mul_le_mul_right _ h2n
    _ = n ^ (q_min + 1) := (pow_succ' n q_min).symm
    _ ≤ U ^ q_min := h.n_pow_succ_le_univ_pow
  exact (Nat.pow_le_pow_iff_left (by have := h.q_min_pos; omega)).mp hpow

theorem log_univ_bounds (h : ValidRegime U V n R p_min q_min p_max q_max) :
    Nat.log 2 n ≤ Nat.log 2 U ∧ Nat.log 2 U ≤ 2 * (p_max + 1) * Nat.log 2 n := by
  have hUn : n ≤ U := by have := h.two_mul_n_le_univ; omega
  have hL4 : 4 ≤ Nat.log 2 n := h.four_le_log
  refine ⟨Nat.log_mono_right hUn, Nat.lt_succ_iff.mp
    ((Nat.log_lt_iff_lt_pow Nat.one_lt_two (by have := h.two_le_n; omega)).mpr ?_)⟩
  calc U ≤ n ^ (p_max + 1) := h.univ_le_pow
    _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ (p_max + 1) :=
        Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le _
    _ = 2 ^ ((Nat.log 2 n + 1) * (p_max + 1)) := (Nat.pow_mul 2 _ _).symm
    _ < 2 ^ (2 * (p_max + 1) * Nat.log 2 n + 1) :=
        Nat.pow_lt_pow_right Nat.one_lt_two (by nlinarith)

theorem four_mul_log_univ_le_sq_log (h : ValidRegime U V n R p_min q_min p_max q_max) :
    4 * Nat.log 2 U ≤ (Nat.log 2 n) ^ 2 := by
  have hp := h.mul_param_le_log (by decide : 8 ≤ 2560000)
  calc 4 * Nat.log 2 U ≤ 4 * (2 * (p_max + 1) * Nat.log 2 n) :=
        Nat.mul_le_mul_left 4 h.log_univ_bounds.2
    _ = 8 * (p_max + 1) * Nat.log 2 n := by ring
    _ ≤ Nat.log 2 n * Nat.log 2 n := Nat.mul_le_mul_right _ (by omega)
    _ = (Nat.log 2 n) ^ 2 := (sq _).symm

theorem log_univ_le_sq_log (h : ValidRegime U V n R p_min q_min p_max q_max) :
    Nat.log 2 U ≤ (Nat.log 2 n) ^ 2 := by
  have := h.four_mul_log_univ_le_sq_log; omega

theorem two_pow_logStar_le_log_log (h : ValidRegime U V n R p_min q_min p_max q_max) :
    2 ^ Nat.logStar n ≤ 32 * (Nat.log 2 (Nat.log 2 n) + 1) := by
  have _ := h.four_le_log
  set L := Nat.log 2 n
  set t := Nat.log 2 L
  have hcl1 : Nat.clog 2 n ≤ L + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
  have hcl2 : Nat.clog 2 (Nat.clog 2 n) ≤ t + 2 :=
    (Nat.clog_mono_right 2 hcl1).trans (Nat.clog_le_of_le_pow
      ((Nat.lt_pow_succ_log_self Nat.one_lt_two L : L < 2 ^ (t + 1)).trans_le
        (Nat.pow_le_pow_right Nat.two_pos (by omega))))
  have h2m : 2 ^ Nat.clog 2 (Nat.clog 2 (Nat.clog 2 n)) ≤ 2 * (t + 2) := by
    rcases Nat.eq_zero_or_pos (Nat.clog 2 (Nat.clog 2 n)) with h0 | hpos
    · simp [h0]; omega
    · exact (Nat.pow_clog_le_mul Nat.one_lt_two hpos.ne').trans (Nat.mul_le_mul_left 2 hcl2)
  calc 2 ^ Nat.logStar n
      ≤ 2 ^ (Nat.clog 2 (Nat.clog 2 (Nat.clog 2 n)) + 3) :=
        Nat.pow_le_pow_right Nat.two_pos (Nat.logStar_le_triple_clog_add_three n)
    _ = 8 * 2 ^ Nat.clog 2 (Nat.clog 2 (Nat.clog 2 n)) := by rw [Nat.pow_add]; ring
    _ ≤ 32 * (t + 1) := by omega

theorem redundancyRatio_bounds (h : ValidRegime U V n R p_min q_min p_max q_max) :
    minRedundancyRatio ≤ redundancyRatio n R ∧
      2 ^ Nat.logStar n ≤ redundancyRatio n R ∧
      (redundancyRatio n R) ^ 10 ≤ Nat.log 2 n := by
  set L := Nat.log 2 n
  set t := Nat.log 2 L
  set s := t / 10
  have hL4 : 4 ≤ L := h.four_le_log
  have ht_ge : 300 ≤ t := h.three_hundred_le_log_log
  have ht_pow : 2 ^ t ≤ L := Nat.pow_log_le_self 2 (by omega)
  have h704s : 704 * s ≤ 2 ^ s := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show 30 ≤ s by omega)
    have hmul : 2 ^ 15 * (15 + d) ^ 2 ≤ 2 ^ s :=
      (Nat.mul_le_mul_left _ (Nat.sq_le_two_pow (by omega))).trans
        (by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right Nat.two_pos (by omega))
    have hlin : 15 + d ≤ (15 + d) ^ 2 := Nat.le_self_pow (by decide) _
    have : 2 ^ 15 = 32768 := by decide
    nlinarith
  have hn_large : 2 * 704 * s ≤ n := by
    have h1 : 2 * (704 * s) ≤ 2 * L :=
      (Nat.mul_le_mul_left 2 (h704s.trans (Nat.pow_le_pow_right Nat.two_pos (by omega)))).trans
        (Nat.mul_le_mul_left 2 ht_pow)
    have h2L : 2 * L ≤ 2 ^ L :=
      ((Nat.mul_le_mul_right L (by omega : 2 ≤ L)).trans_eq (sq L).symm).trans
        (Nat.sq_le_two_pow hL4)
    exact ((Nat.mul_assoc 2 704 s).symm ▸ h1.trans h2L).trans
      (Nat.pow_log_le_self 2 (by have := h.two_le_n; omega))
  set M := max minRedundancyRatio (2 ^ Nat.logStar n)
  have hls : 2 ^ Nat.logStar n ≤ 32 * (t + 1) := h.two_pow_logStar_le_log_log
  have hM_le : M ≤ 352 * s := max_le (by dsimp [minRedundancyRatio]; omega) (by omega)
  have hM_le_n : M ≤ n := by omega
  refine ⟨minRedundancyRatio_le_redundancyRatio ((le_max_left _ _).trans hM_le_n),
    two_pow_logStar_le_redundancyRatio ((le_max_right _ _).trans hM_le_n), ?_⟩
  have hr_eq : redundancyRatio n R = n / effRedundancy n R := by
    dsimp only [redundancyRatio]; rw [max_eq_left (effRedundancy_pos h.redundancy_pos n)]
  dsimp only [effRedundancy] at hr_eq
  by_cases hR_le : R ≤ max 1 (n / M)
  · rw [min_eq_left hR_le] at hr_eq
    have hprod : (redundancyRatio n R) ^ 10 * R ^ 10 ≤ L * R ^ 10 := by
      rw [← Nat.mul_pow, hr_eq, Nat.mul_comm L]
      exact (Nat.pow_le_pow_left (Nat.div_mul_le_self n R) 10).trans h.redundancy_lower
    exact Nat.le_of_mul_le_mul_right hprod (Nat.pow_pos h.redundancy_pos)
  · have hM_pos : 0 < M := lt_of_lt_of_le (by decide : 0 < minRedundancyRatio) (le_max_left _ _)
    have hdiv_ge1 : 1 ≤ n / M := (Nat.le_div_iff_mul_le hM_pos).mpr (by omega)
    rw [min_eq_right (not_le.mp hR_le).le, max_eq_right hdiv_ge1] at hr_eq
    have hr_le_2M : redundancyRatio n R ≤ 2 * M := by
      rw [hr_eq]
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hdiv_ge1).mpr
        (by nlinarith [Nat.div_add_mod n M, Nat.mod_lt n hM_pos]))
    calc (redundancyRatio n R) ^ 10 ≤ (2 ^ s) ^ 10 := Nat.pow_le_pow_left (by omega) 10
      _ = 2 ^ (s * 10) := (Nat.pow_mul 2 s 10).symm
      _ ≤ 2 ^ t := Nat.pow_le_pow_right Nat.two_pos (by omega)
      _ ≤ L := ht_pow

theorem one_le_redundancyRatio (h : ValidRegime U V n R p_min q_min p_max q_max) :
    1 ≤ redundancyRatio n R :=
  (by decide : 1 ≤ minRedundancyRatio).trans h.redundancyRatio_bounds.1

theorem redundancyRatio_le_log (h : ValidRegime U V n R p_min q_min p_max q_max) :
    redundancyRatio n R ≤ Nat.log 2 n :=
  (Nat.le_self_pow (by decide : 10 ≠ 0) _).trans h.redundancyRatio_bounds.2.2

theorem treeDepth_le_logStar_add_four (h : ValidRegime U V n R p_min q_min p_max q_max) :
    treeDepth U (redundancyRatio n R) ≤ Nat.logStar n + 4 := by
  set L := Nat.log 2 n
  have hpL : 2 * (p_max + 1) ≤ L := by
    have := h.mul_param_le_log (by decide : 2 ≤ 2560000); omega
  have hexp_le : (L + 1) * (p_max + 1) ≤ 2 ^ L := by
    have hL4 : 4 ≤ L := h.four_le_log
    calc (L + 1) * (p_max + 1) ≤ (2 * L) * (p_max + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = L * (2 * (p_max + 1)) := by ring
      _ ≤ L * L := Nat.mul_le_mul_left L hpL
      _ = L ^ 2 := (sq L).symm
      _ ≤ 2 ^ L := Nat.sq_le_two_pow hL4
  have hU_tower : U ≤ 2 ^ (2 ^ L) :=
    h.univ_le_pow.trans <|
      (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le _).trans
        ((Nat.pow_mul 2 _ _).symm ▸ Nat.pow_le_pow_right Nat.two_pos hexp_le)
  have hU_ls : Nat.logStar U ≤ Nat.logStar n + 2 := (Nat.logStar_le_iff).mpr <|
    hU_tower.trans (Nat.pow_le_pow_right Nat.two_pos (Nat.pow_le_pow_right Nat.two_pos
      ((Nat.log_le_self 2 n).trans (Nat.le_twoTower_logStar n))))
  have hk_le := (treeDepth_le U (redundancyRatio n R)).trans
    (Nat.add_le_add_right ((Nat.floorLogStar_le_logStar U).trans hU_ls) 2)
  omega

theorem three_le_logStar (h : ValidRegime U V n R p_min q_min p_max q_max) :
    3 ≤ Nat.logStar n := by
  by_contra hlt
  have htw := (Nat.le_twoTower_logStar n).trans
    (Nat.twoTower_monotone (by omega : Nat.logStar n ≤ 2))
  have h16 : 2 ^ 4 ≤ n :=
    (Nat.pow_le_pow_right Nat.two_pos h.four_le_log).trans
      (Nat.pow_log_le_self 2 (by have := h.two_le_n; omega))
  have : Nat.twoTower 2 = 4 := by decide
  omega

theorem treeDepth_add_one_le_three_mul_logStar
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    treeDepth U (redundancyRatio n R) + 1 ≤ 3 * Nat.logStar n := by
  have := h.treeDepth_le_logStar_add_four; have := h.three_le_logStar; omega

theorem treeDepth_le_redundancyRatio (h : ValidRegime U V n R p_min q_min p_max q_max) :
    treeDepth U (redundancyRatio n R) ≤ redundancyRatio n R := by
  obtain ⟨_, hr_ls, _⟩ := h.redundancyRatio_bounds
  have hk_le := h.treeDepth_le_logStar_add_four
  rcases eq_or_lt_of_le h.three_le_logStar with h3 | hgt
  · rw [← h3] at hk_le hr_ls
    omega
  · have := Nat.sq_le_two_pow (Nat.succ_le_of_lt hgt)
    nlinarith

theorem two_pow_eighteen_mul_log_univ_pow_le
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n := by
  set L := Nat.log 2 n
  have hp := h.mul_param_le_log (by decide : 324 ≤ 2560000)
  calc 2 ^ 18 * (Nat.log 2 U) ^ 9
      = (4 * Nat.log 2 U) ^ 9 := by rw [show (2 : ℕ) ^ 18 = 4 ^ 9 by decide, ← Nat.mul_pow]
    _ ≤ (L ^ 2) ^ 9 := Nat.pow_le_pow_left h.four_mul_log_univ_le_sq_log 9
    _ = L ^ 18 := (Nat.pow_mul L 2 9).symm
    _ ≤ 2 ^ L := Nat.pow_le_two_pow (by decide) (by omega)
    _ ≤ n := Nat.pow_log_le_self 2 (by have := h.two_le_n; omega)

theorem four_mul_redundancyRatio_le_log_univ
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    4 * redundancyRatio n R ≤ Nat.log 2 U := by
  obtain ⟨hr256, _, hr10⟩ := h.redundancyRatio_bounds
  have h4r : 4 * redundancyRatio n R ≤ (redundancyRatio n R) ^ 10 :=
    ((Nat.mul_le_mul_right _ (by dsimp [minRedundancyRatio] at hr256; omega)).trans_eq
      (sq _).symm).trans (Nat.pow_le_pow_right (by dsimp [minRedundancyRatio] at hr256; omega)
      (by decide))
  exact (h4r.trans hr10).trans h.log_univ_bounds.1

end ValidRegime

theorem canonical_target_bounds {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (∀ j ≤ treeDepth U (redundancyRatio n R),
        1 ≤ targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) j) ∧
      (∀ j ≤ treeDepth U (redundancyRatio n R),
        targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) j ≤ n) := by
  have hstep : ∀ i < treeDepth U (redundancyRatio n R),
      2 ^ 18 * targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) (i + 1) ≤
        targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) i :=
    fun i hi => two_pow_eighteen_mul_targetSize_succ_le h.redundancyRatio_bounds.1
      h.four_mul_redundancyRatio_le_log_univ h.two_pow_eighteen_mul_log_univ_pow_le hi
  refine ⟨fun j hj => targetSize_pos (by have := h.two_le_n; omega) h.one_le_redundancyRatio
    h.four_mul_redundancyRatio_le_log_univ hj rfl, targetSize_le_of_step hstep⟩

theorem canonical_cumBranchBits_add_seventeen_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hlt : ℓ < treeDepth U (redundancyRatio n R)) :
    cumBranchBits n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ + 17 ≤
      cumBranchBits n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) (ℓ + 1) := by
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  exact cumBranchBits_add_seventeen_le (hT_pos ℓ hlt.le) (hT_pos (ℓ + 1) hlt) (hT_le ℓ hlt.le)
    (two_pow_eighteen_mul_targetSize_succ_le h.redundancyRatio_bounds.1
      h.four_mul_redundancyRatio_le_log_univ h.two_pow_eighteen_mul_log_univ_pow_le hlt)

theorem canonical_nFloor_ge_pow_256 {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hℓ : ℓ ≤ treeDepth U (redundancyRatio n R)) :
    256 ^ 9 ≤ nFloor n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := by
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  have hr256 : minRedundancyRatio ≤ redundancyRatio n R := h.redundancyRatio_bounds.1
  have h4r : 4 * redundancyRatio n R ≤ Nat.log 2 U := h.four_mul_redundancyRatio_le_log_univ
  have hn18 : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n := h.two_pow_eighteen_mul_log_univ_pow_le
  obtain ⟨hlo, _⟩ := targetSize_le_nFloor_and_lt (hT_pos ℓ hℓ) (hT_le ℓ hℓ)
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · have h0 : targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) 0 = n := rfl
    have hr_val : 256 ≤ Nat.log 2 U := by dsimp [minRedundancyRatio] at hr256; omega
    exact (((Nat.pow_le_pow_left hr_val 9).trans
      (Nat.le_mul_of_pos_left _ (by positivity))).trans hn18).trans (h0 ▸ hlo)
  · rw [targetSize_eq_levelScale_pow hpos] at hlo
    exact (Nat.pow_le_pow_left (hr256.trans (r_le_levelScale hpos h4r)) 9).trans hlo

/-- **Canonical Section 5 parameter schedule** instantiated from `(U, V, n, R, q_min, p_max)`
under `ValidRegime` ([LiLiangYuZhou2024, Sections 5.1–5.2]). -/
def canonicalSchedule {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) : TreeSchedule :=
  let r := redundancyRatio n R
  let k := treeDepth U r
  have hS17 : ∀ ℓ < k, cumBranchBits n U r k ℓ + 17 ≤ cumBranchBits n U r k (ℓ + 1) :=
    fun ℓ hlt => canonical_cumBranchBits_add_seventeen_le h hlt
  have hstep_nf : ∀ ℓ < k, branchFactor n U r k ℓ * nFloor n U r k (ℓ + 1) ≤ nFloor n U r k ℓ :=
    fun ℓ hlt => by
      rw [nFloor_succ_eq_div (by have := hS17 ℓ hlt; omega)]
      exact Nat.mul_div_le _ _
  have hnF8 : ∀ ℓ ≤ k, 256 ^ 9 ≤ nFloor n U r k ℓ :=
    fun ℓ hℓ => canonical_nFloor_ge_pow_256 h hℓ
  have h1_le_256 : 1 ≤ 256 ^ 9 := Nat.one_le_pow 9 256 (by decide)
  have h8_le_256 : 8 ≤ 256 ^ 9 := by decide
  { univ := U
    valBound := V
    cap := n
    depth := k
    branchBits := branchBits n U r k
    nFloor := nFloor n U r k
    delta := delta n U r k
    idBits := idBits n U r k
    quotOne := quotUnivOne n U r k
    epsInv := routerEpsInv p_max
    alphaInv := routerAlphaInv q_min
    val_pos := h.val_pos
    two_le_cap := h.two_le_n
    two_le_depth := two_le_treeDepth U r
    quotOne_pos := by
      dsimp only [quotUnivOne]
      set step := branchFactor n U r k 0 * 2 ^ idBits n U r k 1
      have hstep_pos : 1 ≤ step := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
      exact (Nat.le_div_iff_mul_le hstep_pos).mpr (by have := h.two_le_n; omega)
    nFloor_zero := by simp [nFloor, numNodes, cumBranchBits]
    nFloor_pos := fun ℓ hℓ => h1_le_256.trans (hnF8 ℓ hℓ)
    branchBits_pos := fun ℓ hlt => by
      have := hS17 ℓ hlt
      dsimp only [branchBits]
      omega
    delta_lt_nFloor := fun ℓ h1 hℓ => by
      have hy8 := h8_le_256.trans (hnF8 ℓ hℓ)
      have h2d := two_mul_delta_le_nFloor_of_eight_le hy8
      omega
    nFloor_step_le := hstep_nf
    inner_cap_le := fun ℓ h2 hlt => by
      have h10 := ten_mul_delta_le_branchFactor_mul_delta_succ (hS17 ℓ hlt)
        (h8_le_256.trans (hnF8 (ℓ + 1) hlt))
      have hnf := hstep_nf ℓ hlt
      have hd_next := two_mul_delta_le_nFloor_of_eight_le
        (h8_le_256.trans (hnF8 (ℓ + 1) hlt))
      change branchFactor n U r k ℓ * (nFloor n U r k (ℓ + 1) - delta n U r k (ℓ + 1)) ≤
        nFloor n U r k ℓ - delta n U r k ℓ
      rw [Nat.mul_sub]
      omega
    root_cap_le := by
      have hk2 : 2 ≤ k := two_le_treeDepth U r
      change branchFactor n U r k 1 * (nFloor n U r k 2 - delta n U r k 2) ≤
        nFloor n U r k 1 + delta n U r k 1
      calc branchFactor n U r k 1 * (nFloor n U r k 2 - delta n U r k 2)
          ≤ branchFactor n U r k 1 * nFloor n U r k 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ nFloor n U r k 1 := hstep_nf 1 (by omega)
        _ ≤ nFloor n U r k 1 + delta n U r k 1 := Nat.le_add_right _ _
    idBits_step_le := fun ℓ h1 hlt => by
      have h4 := four_mul_branchBits_add_idBits_succ_le (by have := hS17 ℓ hlt; omega)
        (h1_le_256.trans (hnF8 (ℓ + 1) hlt))
      have := hS17 ℓ hlt
      omega
    nHigh_le_two_pow_idBits := fun ℓ h1 hℓ => by
      have hd := two_mul_delta_le_nFloor_of_eight_le (h8_le_256.trans (hnF8 ℓ hℓ))
      have hy1 : 1 ≤ nFloor n U r k ℓ := h1_le_256.trans (hnF8 ℓ hℓ)
      calc nFloor n U r k ℓ + delta n U r k ℓ
          ≤ 2 * max (nFloor n U r k ℓ) 1 := by rw [max_eq_left hy1]; omega
        _ ≤ 2 ^ Nat.clog 2 (2 * max (nFloor n U r k ℓ) 1) := Nat.le_pow_clog Nat.one_lt_two _
        _ ≤ 2 ^ idBits n U r k ℓ :=
            Nat.pow_le_pow_right Nat.two_pos (by dsimp only [idBits]; omega)
    univ_le_padded := by
      dsimp only [quotUnivOne, branchFactor]
      set step := 2 ^ branchBits n U r k 0 * 2 ^ idBits n U r k 1
      have hstep_pos : 0 < step := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
      have hdiv := Nat.div_add_mod (U + n + step - 1) step
      have hmod := Nat.mod_lt (U + n + step - 1) hstep_pos
      have hn2 := h.two_le_n
      change U + n ≤ step * ((U + n + step - 1) / step)
      omega }

@[simp]
theorem canonicalSchedule_univ {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).univ = U := by rfl

@[simp]
theorem canonicalSchedule_valBound {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).valBound = V := by rfl

@[simp]
theorem canonicalSchedule_cap {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).cap = n := by rfl

@[simp]
theorem canonicalSchedule_depth {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).depth = treeDepth U (redundancyRatio n R) := by rfl

theorem canonicalSchedule_branchBits {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) (ℓ : ℕ) :
    (canonicalSchedule h).branchBits ℓ =
      branchBits n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := by rfl

@[simp]
theorem canonicalSchedule_quotOne {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).quotOne =
      quotUnivOne n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) := by rfl

@[simp]
theorem canonicalSchedule_epsInv {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).epsInv = routerEpsInv p_max := by rfl

@[simp]
theorem canonicalSchedule_alphaInv {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).alphaInv = routerAlphaInv q_min := by rfl

theorem canonicalSchedule_cumBranchBits_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    ∀ ℓ ≤ (canonicalSchedule h).depth,
      (canonicalSchedule h).cumBranchBits ℓ =
        cumBranchBits n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := by
  intro ℓ hℓ
  induction ℓ with
  | zero => simp [TreeSchedule.cumBranchBits, cumBranchBits]
  | succ j ih =>
    have hj : j < treeDepth U (redundancyRatio n R) := Nat.lt_of_succ_le hℓ
    have hS17 := canonical_cumBranchBits_add_seventeen_le h hj
    rw [TreeSchedule.cumBranchBits, ih hj.le, canonicalSchedule_branchBits]
    dsimp only [branchBits]; omega

theorem canonicalSchedule_numNodes_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hℓ : ℓ ≤ (canonicalSchedule h).depth) :
    (canonicalSchedule h).numNodes ℓ =
      numNodes n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := by
  dsimp only [TreeSchedule.numNodes, numNodes]
  rw [canonicalSchedule_cumBranchBits_eq h ℓ hℓ]

theorem canonicalSchedule_branchFactor_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) (ℓ : ℕ) :
    (canonicalSchedule h).branchFactor ℓ =
      branchFactor n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := by rfl

theorem canonicalSchedule_nFloor_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) (ℓ : ℕ) :
    (canonicalSchedule h).nFloor ℓ =
      nFloor n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := by rfl

theorem canonicalSchedule_delta_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) (ℓ : ℕ) :
    (canonicalSchedule h).delta ℓ =
      delta n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := by rfl

theorem canonicalSchedule_idBits_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) (ℓ : ℕ) :
    (canonicalSchedule h).idBits ℓ =
      idBits n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := by rfl

theorem canonicalSchedule_two_mul_delta_le_nFloor {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hℓ : ℓ ≤ (canonicalSchedule h).depth) :
    2 * (canonicalSchedule h).delta ℓ ≤ (canonicalSchedule h).nFloor ℓ :=
  two_mul_delta_le_nFloor_of_eight_le
    ((by decide : 8 ≤ 256 ^ 9).trans (canonical_nFloor_ge_pow_256 h hℓ))

theorem canonicalSchedule_childRouterHalfInd_nHigh_zero_le
    {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    FeistelPerm.childRouterHalfInd ((canonicalSchedule h).nHigh 0) ≤ 3 * Nat.log 2 n + 7 := by
  have hnh0 : (canonicalSchedule h).nHigh 0 = n := rfl
  have hn_le : max n 2 ≤ 2 ^ (Nat.log 2 n + 1) := by
    rw [max_eq_left h.two_le_n]
    exact (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
  have hcl : Nat.clog 2 (max n 2) ≤ Nat.log 2 n + 1 := Nat.clog_le_of_le_pow hn_le
  rw [FeistelPerm.childRouterHalfInd_eq, hnh0]
  omega

private theorem canonical_gap_bound {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hlt : ℓ < (canonicalSchedule h).depth) :
    2 ^ (canonicalSchedule h).branchBits ℓ * (canonicalSchedule h).routerRightUniv ℓ ≤
      ((canonicalSchedule h).routerRightUniv ℓ) ^ max (canonicalSchedule h).alphaInv 1 := by
  set r := redundancyRatio n R
  set k := treeDepth U r
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  have hα : max (canonicalSchedule h).alphaInv 1 = q_min + 1 := by
    have := h.q_min_pos; change max (max q_min 1 + 1) 1 = q_min + 1; omega
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · set T0 := 2 ^ idBits n U r k 1 * quotUnivOne n U r k
    change 2 ^ branchBits n U r k 0 * T0 ≤ T0 ^ max (canonicalSchedule h).alphaInv 1
    rw [hα]
    have h1_lt : 1 ≤ k := by have := two_le_treeDepth U r; omega
    have hB0_le : 2 ^ branchBits n U r k 0 ≤ n := by
      have hNT1 := (numNodes_mul_targetSize_bounds (hT_pos 1 h1_lt) (hT_le 1 h1_lt)).1
      simpa [branchBits, numNodes, cumBranchBits] using
        (Nat.le_mul_of_pos_right _ (hT_pos 1 h1_lt)).trans hNT1
    have hU_le : U ≤ n * T0 := by
      have hpad : U + n ≤ 2 ^ branchBits n U r k 0 * T0 := by
        simpa only [canonicalSchedule, branchFactor, T0, Nat.mul_assoc] using
          (canonicalSchedule h).univ_le_padded
      exact (Nat.le_add_right U n).trans (hpad.trans (Nat.mul_le_mul_right T0 hB0_le))
    have hn_T0 : n ≤ T0 ^ q_min := Nat.le_of_mul_le_mul_left (by
      calc n ^ q_min * n = n ^ (q_min + 1) := (pow_succ n q_min).symm
        _ ≤ U ^ q_min := h.n_pow_succ_le_univ_pow
        _ ≤ (n * T0) ^ q_min := Nat.pow_le_pow_left hU_le q_min
        _ = n ^ q_min * T0 ^ q_min := Nat.mul_pow n T0 q_min)
      (Nat.pow_pos (by have := h.two_le_n; omega))
    exact (Nat.mul_le_mul_right T0 (hB0_le.trans hn_T0)).trans_eq (pow_succ T0 q_min).symm
  · set d := idBits n U r k ℓ - branchBits n U r k ℓ
    change 2 ^ branchBits n U r k ℓ * (if ℓ = 0 then _ else 2 ^ d) ≤
      (if ℓ = 0 then _ else 2 ^ d) ^ max (canonicalSchedule h).alphaInv 1
    rw [ite_eq_right hpos.ne', hα]
    have hS : cumBranchBits n U r k ℓ + 17 ≤ cumBranchBits n U r k (ℓ + 1) :=
      canonical_cumBranchBits_add_seventeen_le h hlt
    have h4 : 4 * branchBits n U r k ℓ + idBits n U r k (ℓ + 1) ≤ idBits n U r k ℓ :=
      four_mul_branchBits_add_idBits_succ_le (Nat.le_of_add_right_le hS)
        ((by decide : 1 ≤ 256 ^ 9).trans (canonical_nFloor_ge_pow_256 h hlt))
    have hexp : idBits n U r k ℓ ≤ d * (q_min + 1) :=
      (by dsimp only [d]; omega : idBits n U r k ℓ ≤ d * 2).trans
        (Nat.mul_le_mul_left d (by have := h.q_min_pos; omega))
    calc 2 ^ branchBits n U r k ℓ * 2 ^ d
        = 2 ^ idBits n U r k ℓ := by rw [← Nat.pow_add]; congr 1; dsimp only [d]; omega
      _ ≤ 2 ^ (d * (q_min + 1)) := Nat.pow_le_pow_right Nat.two_pos hexp
      _ = (2 ^ d) ^ (q_min + 1) := Nat.pow_mul 2 _ _

private theorem canonical_conc_bound {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hlt : ℓ < (canonicalSchedule h).depth) :
    let m := FeistelPerm.childRouterHalfInd ((canonicalSchedule h).nHigh ℓ)
    2 ^ (canonicalSchedule h).branchBits ℓ * (150 * m) ^ 3 ≤ (canonicalSchedule h).nLow ℓ := by
  intro m
  set P := canonicalSchedule h
  set r := redundancyRatio n R
  set k := treeDepth U r
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · set L := Nat.log 2 n
    have hp := h.mul_param_le_log (by decide : 750 ≤ 2560000)
    have hm_le := canonicalSchedule_childRouterHalfInd_nHigh_zero_le h
    have h150_le : (150 * m) ^ 3 ≤ L ^ 8 := by
      have hprod : 150 * m ≤ L ^ 2 :=
        (by omega : 150 * m ≤ 750 * L).trans
          ((Nat.mul_le_mul_right L (by omega)).trans_eq (sq L).symm)
      exact ((Nat.pow_le_pow_left hprod 3).trans_eq (Nat.pow_mul L 2 3).symm).trans
        (Nat.pow_le_pow_right (by omega) (by decide))
    have h1_le : 1 ≤ k := by have := two_le_treeDepth U r; omega
    have hNT1 := (numNodes_mul_targetSize_bounds (hT_pos 1 h1_le) (hT_le 1 h1_le)).1
    have hT1_ge : 2 * L ^ 8 ≤ targetSize n U r k 1 := by
      have hT1 : targetSize n U r k 1 = (Nat.log 2 U) ^ 9 := by
        rw [targetSize_eq_levelScale_pow le_rfl]
        dsimp only [levelScale]; rw [ite_eq_left (by have := two_le_treeDepth U r; omega)]; simp
      rw [hT1]
      exact ((Nat.mul_le_mul_right _ (by omega : 2 ≤ L)).trans_eq (pow_succ' L 8).symm).trans
        (Nat.pow_le_pow_left h.log_univ_bounds.1 9)
    have hN1 : 2 ^ P.branchBits 0 = numNodes n U r k 1 := by
      change 2 ^ branchBits n U r k 0 = 2 ^ cumBranchBits n U r k 1
      simp [branchBits, cumBranchBits]
    have hmul2 : 2 * (2 ^ P.branchBits 0 * (150 * m) ^ 3) ≤ n := by
      rw [hN1]
      calc 2 * (numNodes n U r k 1 * (150 * m) ^ 3)
          ≤ numNodes n U r k 1 * (2 * L ^ 8) := by
            rw [Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 h150_le)
        _ ≤ numNodes n U r k 1 * targetSize n U r k 1 := Nat.mul_le_mul_left _ hT1_ge
        _ ≤ n := hNT1
    have hnl0 : P.nLow 0 = n - 1 := rfl
    have := h.two_le_n
    rw [hnl0]; omega
  · set s := levelScale U r k (ℓ + 1)
    have hr256 := h.redundancyRatio_bounds.1
    have hs_ge : 256 ≤ s :=
      hr256.trans (r_le_levelScale (by omega) h.four_mul_redundancyRatio_le_log_univ)
    have hid_le : idBits n U r k ℓ ≤ 148 * s := by
      have hlt_k : ℓ < k := hlt
      simpa only [Nat.add_sub_cancel] using idBits_pred_le_mul_levelScale hr256
        (by omega : 2 ≤ ℓ + 1) hlt_k (hT_pos ℓ hlt_k.le) (hT_le ℓ hlt_k.le)
    have hy8 : 8 ≤ nFloor n U r k ℓ :=
      (by decide : 8 ≤ 256 ^ 9).trans (canonical_nFloor_ge_pow_256 h hlt.le)
    have hd_cur := two_mul_delta_le_nFloor_of_eight_le hy8
    have hnh_le : max (P.nHigh ℓ) 2 ≤ 2 * max (nFloor n U r k ℓ) 1 := by
      rw [show P.nHigh ℓ = nFloor n U r k ℓ + delta n U r k ℓ from ite_eq_right hpos.ne',
        max_eq_left (by omega : 1 ≤ nFloor n U r k ℓ)]
      omega
    have hm_le : m ≤ 112 * s := by
      have := Nat.clog_mono_right 2 hnh_le
      have : m = 3 * Nat.clog 2 (max (P.nHigh ℓ) 2) + 4 :=
        FeistelPerm.childRouterHalfInd_eq (P.nHigh ℓ)
      dsimp only [idBits] at hid_le
      omega
    have hcube_s : 2 * (150 * m) ^ 3 ≤ s ^ 9 := by
      have hcoeff : 2 * 16800 ^ 3 ≤ 256 ^ 6 := by decide
      calc 2 * (150 * m) ^ 3 ≤ 2 * (16800 * s) ^ 3 :=
            Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 3)
        _ = (2 * 16800 ^ 3) * s ^ 3 := by ring
        _ ≤ s ^ 6 * s ^ 3 := Nat.mul_le_mul_right _ (hcoeff.trans (Nat.pow_le_pow_left hs_ge 6))
        _ = s ^ 9 := (Nat.pow_add s 6 3).symm
    have hlo_next : s ^ 9 ≤ nFloor n U r k (ℓ + 1) := by
      have hlo := (targetSize_le_nFloor_and_lt (hT_pos (ℓ + 1) hlt) (hT_le (ℓ + 1) hlt)).1
      rwa [targetSize_eq_levelScale_pow (by omega)] at hlo
    have h2mul : 2 * (2 ^ P.branchBits ℓ * (150 * m) ^ 3) ≤ nFloor n U r k ℓ := by
      rw [Nat.mul_left_comm]
      exact (Nat.mul_le_mul_left _ (hcube_s.trans hlo_next)).trans (P.nFloor_step_le ℓ hlt)
    rw [show P.nLow ℓ = nFloor n U r k ℓ - delta n U r k ℓ from ite_eq_right hpos.ne']
    omega

private theorem rpow_two_thirds_le_two_mul_succ {μ x : ℝ} {d : ℕ}
    (hμ_pos : 0 < μ) (hμ_le : μ ≤ 2 * x) (hx2 : x ^ 2 ≤ ((d : ℝ) + 1) ^ 3) :
    μ ^ ((2 : ℝ) / 3) ≤ 2 * ((d : ℝ) + 1) := by
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp ?_
  calc (μ ^ ((2 : ℝ) / 3)) ^ 3
      = μ ^ 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul hμ_pos.le]; norm_num
    _ ≤ (2 * x) ^ 2 := pow_le_pow_left₀ hμ_pos.le hμ_le 2
    _ = 4 * x ^ 2 := by ring
    _ ≤ 8 * ((d : ℝ) + 1) ^ 3 := by linarith only [hx2, sq_nonneg x]
    _ = (2 * ((d : ℝ) + 1)) ^ 3 := by ring

private theorem canonical_window_contained {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hlt : ℓ < (canonicalSchedule h).depth) (m b_load : ℕ)
    (hm_lo : (canonicalSchedule h).nLow ℓ ≤ m) (hm_hi : m ≤ (canonicalSchedule h).nHigh ℓ)
    (hb_lo : (m : ℝ) / (2 : ℝ) ^ (canonicalSchedule h).branchBits ℓ -
        ((1 : ℝ) / 5) *
          ((m : ℝ) / (2 : ℝ) ^ (canonicalSchedule h).branchBits ℓ) ^ ((2 : ℝ) / 3) ≤
        (b_load : ℝ))
    (hb_hi : (b_load : ℝ) ≤
      (m : ℝ) / (2 : ℝ) ^ (canonicalSchedule h).branchBits ℓ +
        ((1 : ℝ) / 5) *
          ((m : ℝ) / (2 : ℝ) ^ (canonicalSchedule h).branchBits ℓ) ^ ((2 : ℝ) / 3)) :
    (canonicalSchedule h).nLow (ℓ + 1) ≤ b_load ∧
      b_load ≤ (canonicalSchedule h).nHigh (ℓ + 1) := by
  set P := canonicalSchedule h
  set r := redundancyRatio n R
  set k := treeDepth U r
  set B := branchFactor n U r k ℓ
  set x := nFloor n U r k (ℓ + 1)
  set y := nFloor n U r k ℓ
  set d_next := delta n U r k (ℓ + 1)
  have hS17 : cumBranchBits n U r k ℓ + 17 ≤ cumBranchBits n U r k (ℓ + 1) :=
    canonical_cumBranchBits_add_seventeen_le h hlt
  have hx_ge : 256 ^ 9 ≤ x := canonical_nFloor_ge_pow_256 h hlt
  have h8x : 8 ≤ x := (by decide : 8 ≤ 256 ^ 9).trans hx_ge
  have hd_le_x : 2 * d_next ≤ x := two_mul_delta_le_nFloor_of_eight_le h8x
  have hd_next_ge : 256 ^ 6 ≤ d_next := by
    rw [show d_next = Nat.nthRoot 3 (x ^ 2) from rfl, Nat.le_nthRoot_iff (by decide)]
    exact ((show (256 ^ 6) ^ 3 = (256 ^ 9) ^ 2 by decide) ▸ Nat.pow_le_pow_left hx_ge 2)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (Nat.two_pow_pos _ : 1 ≤ B)
  have hx_eq : x = y / B := nFloor_succ_eq_div (by omega)
  have hy_lo : (B : ℝ) * x ≤ y := by exact_mod_cast (hx_eq ▸ Nat.mul_div_le y B)
  have hy_hi : (y : ℝ) ≤ (B : ℝ) * (x + 1) := by
    exact_mod_cast (hx_eq ▸ Nat.lt_mul_div_succ y (Nat.two_pow_pos _) : y < B * (x + 1)).le
  set μ : ℝ := (m : ℝ) / (B : ℝ)
  have hB_cast : (2 : ℝ) ^ P.branchBits ℓ = (B : ℝ) := (Nat.cast_pow 2 _).symm
  rw [hB_cast] at hb_lo hb_hi
  have hm_band : (B : ℝ) * x - (B : ℝ) * d_next / 10 - B ≤ m ∧
      (m : ℝ) ≤ (B : ℝ) * (x + 1) + (B : ℝ) * d_next / 10 := by
    have hdn : (0 : ℝ) ≤ (B : ℝ) * d_next / 10 := by positivity
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · change n - 1 ≤ m at hm_lo
      change m ≤ n at hm_hi
      have hy0 : y = n := by simp [y, nFloor, numNodes, cumBranchBits]
      have hml : (y : ℝ) ≤ m + 1 := by exact_mod_cast (by omega : y ≤ m + 1)
      have hmh : (m : ℝ) ≤ y := by exact_mod_cast (by omega : m ≤ y)
      exact ⟨by linarith, by linarith⟩
    · set δ := delta n U r k ℓ
      have hd_le_y : 2 * δ ≤ y := two_mul_delta_le_nFloor_of_eight_le
        ((by decide : 8 ≤ 256 ^ 9).trans (canonical_nFloor_ge_pow_256 h hlt.le))
      change (if ℓ = 0 then n - 1 else y - δ) ≤ m at hm_lo
      change m ≤ (if ℓ = 0 then n else y + δ) at hm_hi
      rw [ite_eq_right hpos.ne'] at hm_lo hm_hi
      have h10r : (10 : ℝ) * δ ≤ B * d_next := by
        exact_mod_cast ten_mul_delta_le_branchFactor_mul_delta_succ hS17 h8x
      have hml : (y : ℝ) ≤ m + δ := by exact_mod_cast (by omega : y ≤ m + δ)
      have hmh : (m : ℝ) ≤ y + δ := by exact_mod_cast hm_hi
      exact ⟨by linarith, by linarith⟩
  have hμ_lo : (x : ℝ) - d_next / 10 - 1 ≤ μ := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hμ_hi : μ ≤ (x : ℝ) + d_next / 10 + 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hμ_pos : 0 < μ := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast (P.nLow_pos hlt.le).trans hm_lo
    positivity
  have hdev_le : ((1 : ℝ) / 5) * μ ^ ((2 : ℝ) / 3) ≤ ((2 : ℝ) / 5) * (d_next + 1) := by
    have hx_r : (10 : ℝ) ≤ x := by exact_mod_cast (by decide : 10 ≤ 256 ^ 9).trans hx_ge
    have hd_r : (2 : ℝ) * d_next ≤ x := by exact_mod_cast hd_le_x
    have hx2 : (x : ℝ) ^ 2 ≤ ((d_next : ℝ) + 1) ^ 3 := by
      exact_mod_cast (Nat.lt_pow_nthRoot_add_one (by decide) (x ^ 2)).le
    have hdev := rpow_two_thirds_le_two_mul_succ hμ_pos (by linarith) hx2
    linarith only [hdev]
  have hd_big : (10 : ℝ) ≤ d_next := by exact_mod_cast (by decide : 10 ≤ 256 ^ 6).trans hd_next_ge
  change (if ℓ + 1 = 0 then n - 1 else x - d_next) ≤ b_load ∧
    b_load ≤ (if ℓ + 1 = 0 then n else x + d_next)
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hlo : (x : ℝ) < b_load + 1 + d_next := by linarith only [hb_lo, hμ_lo, hdev_le, hd_big]
  have hhi : (b_load : ℝ) < x + d_next + 1 := by linarith only [hb_hi, hμ_hi, hdev_le, hd_big]
  have hlo : x < b_load + 1 + d_next := by exact_mod_cast hlo
  have hhi : b_load < x + d_next + 1 := by exact_mod_cast hhi
  omega

/-- **`canonicalSchedule` concentration readiness**: across the entire `ValidRegime`,
`canonicalSchedule h` satisfies all six probabilistic concentration conditions in
`TreeSchedule.ConcentrationReady` (`Section 5.4`, `Claim 5.4`, and `Lemma 5.3`). -/
theorem canonicalSchedule_concentrationReady {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).ConcentrationReady where
  six_le_nFloor ℓ hℓ := (by decide : 6 ≤ 256 ^ 9).trans (canonical_nFloor_ge_pow_256 h hℓ)
  two_mul_delta_le_nFloor ℓ _ hℓ := canonicalSchedule_two_mul_delta_le_nFloor h hℓ
  gap_bound _ hlt := canonical_gap_bound h hlt
  conc_bound _ hlt := canonical_conc_bound h hlt
  window_contained _ hlt := canonical_window_contained h hlt
  id_collision_bound ℓ h1 hℓ := nHigh_sq_mul_nFloor_sq_le_four_mul_two_pow_idBits h1
    ((by decide : 8 ≤ 256 ^ 9).trans (canonical_nFloor_ge_pow_256 h hℓ))

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
