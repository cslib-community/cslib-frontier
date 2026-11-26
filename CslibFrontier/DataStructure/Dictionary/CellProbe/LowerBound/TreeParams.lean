/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.OuterGame
import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.Base

/-!
# Multi-Level Tree Parameter Helpers and Yao Wrappers

Numeric logarithm/power inequalities, the `iterLog` meta-tree parameter verifier
`iterLog_tree_bounds`, the single-node `NodeOuterHyp` interface, algebraic redundancy combination
helpers, and the Yao coin-fixing wrappers transferring deterministic lower bounds to randomized
schemes. Independent of the Section 8.1 modified inner game.

## Main definitions

* `Cslib.DataStructure.Dictionary.CellProbe.NodeOuterHyp`: uniform single-node `OuterLemma`
  hypothesis consumed by `LowerBound.ModeBounds`.

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.iterLog_tree_bounds`: fanout and redundancy inequalities
  for the iterated-logarithm `MetaTree`.
* `Cslib.DataStructure.Dictionary.CellProbe.combine_iterLogStar_and_sublinear`: algebraic pairing of
  `Ω(log* n)` and `Ω(log(n / max R 1))` bounds.
* `Cslib.DataStructure.Dictionary.CellProbe.le_expectedSeqProbes_query_of_det`,
  `Cslib.DataStructure.Dictionary.CellProbe.le_expectedSeqProbes_update_of_det`: deterministic to
  zero-error randomized lifting helpers.
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary

theorem real_le_logb_of_two_pow_le {M U : ℕ} (h : 2 ^ M ≤ U) :
    (M : ℝ) ≤ Real.logb 2 U := by
  simpa only [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] using
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by exact_mod_cast h : (2 : ℝ) ^ M ≤ U)

theorem logb_le_real_of_le_two_pow {x : ℝ} {k : ℕ} (hx : 0 < x) (h : x ≤ (2 : ℝ) ^ k) :
    Real.logb 2 x ≤ (k : ℝ) := by
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hx h
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl

theorem probeThresh_le_gamma_logb {γ U : ℝ} {H : ℕ} (hγ : 0 ≤ γ)
    (hH : ((H - 1 : ℕ) : ℝ) ≤ Real.logb 2 U) :
    6 * (((H - 1 : ℕ) : ℝ) * (4 * γ / 25)) ≤ γ * Real.logb 2 U := by
  linarith [mul_le_mul_of_nonneg_left hH hγ, mul_nonneg hγ (Nat.cast_nonneg (H - 1))]

/-- Single-node `OuterLemma` hypothesis shared by the `iterLog` and geometric meta-tree bounds. -/
@[expose] def NodeOuterHyp (withQueries : Bool) {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) (γ : ℝ)
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) : Prop :=
  ∀ {R t : ℝ}, ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R →
    ∀ (T : MetaTree), 0 < t → ∀ {ℓ b : ℕ}, 1 ≤ ℓ → T.nodeStop (ℓ + 1) b ≤ n →
      2 ^ 64 ≤ T.fanout (ℓ + 1) → 11 / γ ≤ Real.logb 2 U → 6 * t ≤ γ * Real.logb 2 U →
      (n : ℝ) ^ (1 - γ / 2) ≤ (T.blockSize ℓ : ℝ) →
      (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U →
      100 * R ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)) →
      R ≤ (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U →
      (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
          ∑' ops, (modeDist withQueries U V n hU hV ops).toReal *
            (T.nodeCost D_det n (modeStride withQueries) ops ℓ b : ℝ) ∨
        (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
          ∑' ops, (modeDist withQueries U V n hU hV ops).toReal *
            (T.nodeProbes D_det n (modeStride withQueries) ops (ℓ + 1) b : ℝ)

private theorem floorLogStar_sub_one_le_logb {n U : ℕ} (hn : 2 ≤ n) (hnU : n ≤ U) :
    ((Nat.floorLogStar n - 1 : ℕ) : ℝ) ≤ Real.logb 2 U := by
  have hf : Nat.floorLogStar n = Nat.floorLogStar (Nat.log 2 n) + 1 :=
    Nat.floorLogStar_of_gt_one (by omega)
  have hle1 : Nat.floorLogStar n - 1 ≤ Nat.log 2 n := by
    rw [hf, Nat.add_sub_cancel]; exact Nat.floorLogStar_le_self _
  have hle3 : Real.logb 2 n ≤ Real.logb 2 U :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast hnU)
  exact ((Nat.cast_le.mpr hle1).trans (Real.natLog_le_logb n 2)).trans hle3

private theorem eight_mul_le_two_pow {q : ℕ} (hq : 6 ≤ q) : 8 * q ≤ 2 ^ q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hq
  induction d with
  | zero => decide
  | succ d ih => rw [show 6 + (d + 1) = (6 + d) + 1 by omega, Nat.pow_succ]; omega

theorem logb_le_rpow_of_ge_pow {γ : ℝ} (hγ : 0 < γ) {n : ℕ}
    (hn_big : 2 ^ (2 * (Nat.ceil (4 / γ) + 1) * (2 * (Nat.ceil (4 / γ) + 1) + 2)) ≤ n) :
    Real.logb 2 n ≤ (n : ℝ) ^ (γ / 2) := by
  generalize hM_def : Nat.ceil (4 / γ) + 1 = M at hn_big
  have hM_pos : 1 ≤ M := by rw [← hM_def]; exact Nat.le_add_left 1 _
  have hc : 4 / γ ≤ (M : ℝ) := by
    rw [← hM_def]; exact (Nat.le_ceil (4 / γ)).trans (by push_cast; linarith)
  clear hM_def
  have hn1 : 1 ≤ n := (Nat.one_le_pow _ _ Nat.two_pos).trans hn_big
  set L := Nat.log 2 n
  have hL_ge : 2 * M * (2 * M + 2) ≤ L :=
    (Nat.log_pow Nat.one_lt_two _).symm.trans_le (Nat.log_mono_right hn_big)
  set q := L / (2 * M)
  have hq_ge : 2 * M + 2 ≤ q := (Nat.le_div_iff_mul_le (by positivity)).mpr
    (by rw [mul_comm]; exact hL_ge)
  have hL1_le : L + 1 ≤ (2 * M + 1) * (q + 1) := by
    have hdiv := Nat.div_add_mod L (2 * M)
    have hmod := Nat.mod_lt L (show 0 < 2 * M by positivity)
    dsimp only [q] at *; nlinarith
  have hL1_pow : L + 1 ≤ 2 ^ (2 * q) := by
    have h2M_pow : 2 * M + 1 ≤ 2 ^ q :=
      (Nat.lt_two_pow_self (n := 2 * M)).trans_le (Nat.pow_le_pow_right Nat.two_pos (by omega))
    calc L + 1 ≤ (2 * M + 1) * (q + 1) := hL1_le
      _ ≤ 2 ^ q * 2 ^ q := Nat.mul_le_mul h2M_pow Nat.lt_two_pow_self
      _ = 2 ^ (2 * q) := by rw [← Nat.pow_add, two_mul]
  have hlog_lt : Real.logb 2 n ≤ ((L + 1 : ℕ) : ℝ) :=
    logb_le_real_of_le_two_pow (by exact_mod_cast hn1)
      (by exact_mod_cast (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le)
  have hpow_le_n : ((2 : ℝ) ^ (2 * M * q : ℕ)) ≤ (n : ℝ) := by
    exact_mod_cast ((Nat.pow_le_pow_right Nat.two_pos (Nat.mul_div_le L (2 * M))).trans
      (Nat.pow_log_le_self 2 (by omega)))
  have hM_pos' : (0 : ℝ) < M := by exact_mod_cast hM_pos
  have hrpow1 : (2 : ℝ) ^ (2 * q : ℕ) ≤ (n : ℝ) ^ (1 / (M : ℝ)) := by
    have h := Real.rpow_le_rpow (by positivity) hpow_le_n (one_div_nonneg.mpr hM_pos'.le)
    have hexp_eq : ((2 * M * q : ℕ) : ℝ) * (1 / (M : ℝ)) = ((2 * q : ℕ) : ℝ) := by
      push_cast; field_simp
    rwa [← Real.rpow_natCast (2 : ℝ) (2 * M * q), ← Real.rpow_mul zero_le_two, hexp_eq,
      Real.rpow_natCast] at h
  have hrpow2 : (n : ℝ) ^ (1 / (M : ℝ)) ≤ (n : ℝ) ^ (γ / 2) :=
    Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn1)
      ((div_le_iff₀ hM_pos').mpr (by linarith only [(div_le_iff₀ hγ).mp hc]))
  exact hlog_lt.trans
    ((Nat.cast_le (α := ℝ).mpr hL1_pow).trans (by push_cast; exact hrpow1.trans hrpow2))

/-- Shared `iterLogMetaTree` structural bounds across Theorems 1.1 and 1.3(1). -/
theorem iterLog_tree_bounds {γ c_R : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hcR : 0 ≤ c_R)
    {c_tree s_off n U k k' : ℕ}
    (hct8 : 8 ≤ c_tree) (hct_ceil : 808 * (c_R + 1) / γ ≤ (c_tree : ℝ))
    (hs_off : s_off = Nat.logStar (max 71 (4 * c_tree * (4 * c_tree + 71))) + 2)
    (hn : 2 ≤ n) (hnU : n ≤ U) (hfls : 4 ≤ Nat.floorLogStar n)
    (hk_lo : 2 * s_off + 6 ≤ k) (hk_hi : k ≤ Nat.logStar n)
    (hk' : k' = min k (Nat.floorLogStar n - 1)) :
    2 ≤ k' - s_off ∧ (k : ℝ) / 4 ≤ ((k' - s_off - 1 : ℕ) : ℝ) ∧
      ((k' - s_off - 1 : ℕ) : ℝ) ≤ Real.logb 2 U ∧
      ((max (Nat.iterLog k n) 1 : ℕ) : ℝ) ≤ (Nat.iterLog k' n : ℝ) ∧
      (n : ℝ) ≤ ((iterLogMetaTree n k' c_tree).blockSize 1 : ℝ) * Real.logb 2 n ∧
      (∀ ℓ ∈ Finset.Ico 1 (k' - s_off),
        (iterLogMetaTree n k' c_tree).blockSize (ℓ + 1) ≤ n / 2 ∧
          2 ^ 64 ≤ (iterLogMetaTree n k' c_tree).fanout (ℓ + 1) ∧
          ((iterLogMetaTree n k' c_tree).fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U ∧
          100 * (c_R * (n : ℝ) * (Nat.iterLog k' n : ℝ)) ≤
            ((iterLogMetaTree n k' c_tree).blockSize (ℓ + 1) : ℝ) *
              Real.logb 2 ((iterLogMetaTree n k' c_tree).fanout (ℓ + 1)) ∧
          c_R * (n : ℝ) * (Nat.iterLog k' n : ℝ) ≤
            (γ / 2) * ((iterLogMetaTree n k' c_tree).blockSize ℓ : ℝ) * Real.logb 2 U) := by
  generalize hs_def : Nat.logStar (max 71 (4 * c_tree * (4 * c_tree + 71))) = s at hs_off
  have hM_le_tw : max 71 (4 * c_tree * (4 * c_tree + 71)) ≤ Nat.twoTower (s + 1) :=
    (Nat.logStar_le_iff.mp (hs_def.le)).trans (Nat.twoTower_lt_twoTower_succ s).le
  have hct_808 : 808 * (c_R + 1) ≤ (c_tree : ℝ) := by
    linarith only [(div_le_iff₀ hγ).mp hct_ceil,
      mul_le_mul_of_nonneg_left hγ1 (Nat.cast_nonneg (α := ℝ) c_tree)]
  have hk_le_fls : k ≤ (Nat.floorLogStar n - 1) + 2 := by
    have h1 := Nat.logStar_le_floorLogStar_add_one n; omega
  have hH_ge : 2 ≤ k' - s_off := by omega
  have hk_r : (k : ℝ) / 4 ≤ ((k' - s_off - 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]; exact_mod_cast (by omega : k ≤ (k' - s_off - 1) * 4)
  have hH1_logU : ((k' - s_off - 1 : ℕ) : ℝ) ≤ Real.logb 2 U :=
    (Nat.cast_le.mpr (by omega : k' - s_off - 1 ≤ Nat.floorLogStar n - 1)).trans
      (floorLogStar_sub_one_le_logb hn hnU)
  have hiter_k'_gt1 : 1 < Nat.iterLog k' n := Nat.lt_floorLogStar_iff.mp (by omega)
  have hmax_le : max (Nat.iterLog k n) 1 ≤ Nat.iterLog k' n :=
    max_le (Nat.iterLog_anti_left n (by omega)) (by omega)
  have h2n_le : 2 * Nat.iterLog 1 n ≤ 2 * n * Nat.iterLog k' n :=
    (Nat.mul_le_mul_left 2 (Nat.iterLog_le_self 1 n)).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hH_le_height : k' - s_off ≤ (iterLogMetaTree n k' c_tree).height := by
    have h2log1 : 2 * Nat.iterLog 1 n ≤ c_tree * n * Nat.iterLog k' n :=
      h2n_le.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right n (by omega)))
    have hh := le_height_iterLogMetaTree_add (c := c_tree) hn (by omega) h2log1
    rw [hs_def] at hh; omega
  clear hs_def
  generalize hT_def : iterLogMetaTree n k' c_tree = T at hH_le_height ⊢
  have hb1_mul : (c_tree - 2) * n * Nat.iterLog k' n ≤ T.blockSize 1 * Nat.iterLog 1 n := by
    have hm := mul_iterLog_le_blockSize_one_add_iterLogMetaTree hn k' c_tree
    rw [hT_def, Nat.mul_assoc] at hm
    rw [Nat.mul_assoc] at h2n_le
    rw [Nat.mul_assoc, Nat.sub_mul]; omega
  have hn_le_b1 : (n : ℝ) ≤ (T.blockSize 1 : ℝ) * Real.logb 2 n := by
    have h1 : n ≤ T.blockSize 1 * Nat.iterLog 1 n :=
      (Nat.le_mul_of_pos_left n (by omega : 0 < c_tree - 2)).trans
        ((Nat.le_mul_of_pos_right _ (by omega)).trans hb1_mul)
    have h2 : (n : ℝ) ≤ (T.blockSize 1 : ℝ) * (Nat.log 2 n : ℝ) := by
      simpa only [Nat.iterLog_succ, Nat.iterLog_zero, Nat.cast_mul] using
        (Nat.cast_le (α := ℝ).mpr h1)
    exact h2.trans (mul_le_mul_of_nonneg_left (Real.natLog_le_logb n 2) (Nat.cast_nonneg _))
  refine ⟨hH_ge, hk_r, hH1_logU, by exact_mod_cast hmax_le, hn_le_b1, fun ℓ hℓ => ?_⟩
  have hℓ_ge : 1 ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
  have hℓ1_le_H : ℓ + 1 ≤ k' - s_off := (Finset.mem_Ico.mp hℓ).2
  have hblock_half : T.blockSize (ℓ + 1) ≤ n / 2 :=
    hT_def ▸ (le_height_iterLogMetaTree_iff hn k' c_tree (ℓ + 1)).mp
      (hℓ1_le_H.trans (hT_def ▸ hH_le_height))
  have hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1) := by
    rw [← hT_def]; exact two_pow_le_fanout_iterLogMetaTree n k' c_tree (by omega)
  have hx_ge_M : max 71 (4 * c_tree * (4 * c_tree + 71)) ≤ Nat.iterLog (ℓ + 1) n := by
    refine hM_le_tw.trans ?_
    by_contra hlt; push Not at hlt
    have hle1 : Nat.iterLog s (Nat.iterLog (ℓ + 1) n) ≤ 1 :=
      Nat.iterLog_le_one_iff_lt_twoTower.mpr hlt
    have hstep_le : (s + 1) + (ℓ + 1) ≤ k' := by clear hF_lo; omega
    have h0 : Nat.iterLog ((s + 1) + (ℓ + 1)) n = 0 := by
      rw [Nat.iterLog_add, Nat.iterLog_succ]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with hz | ho <;> [rw [hz]; rw [ho]] <;> rfl
    have hle0 := (Nat.iterLog_anti_left n hstep_le).trans_eq h0
    clear hF_lo; omega
  have hx71 : 71 ≤ Nat.iterLog (ℓ + 1) n := (_root_.le_max_left 71 _).trans hx_ge_M
  have hy71 : 71 ≤ Nat.iterLog ℓ n := hx71.trans (Nat.iterLog_anti_left n (Nat.le_succ ℓ))
  have hx_ge_ct : c_tree ≤ Nat.iterLog (ℓ + 1) n := by
    have h1 : c_tree ≤ 4 * c_tree * (4 * c_tree + 71) :=
      (Nat.le_mul_of_pos_left _ (by decide)).trans
        (Nat.le_mul_of_pos_right _ (by clear hF_lo; omega))
    exact (h1.trans (_root_.le_max_right 71 _)).trans hx_ge_M
  have hlog1_logU : (Nat.iterLog 1 n : ℝ) ≤ Real.logb 2 U := by
    simpa only [Nat.iterLog_succ, Nat.iterLog_zero, Nat.cast_ofNat] using
      (Real.natLog_le_logb n 2).trans
        (Real.logb_le_logb_of_le (by norm_num)
          (by exact_mod_cast (show 0 < n by clear hF_lo; omega)) (by exact_mod_cast hnU))
  have hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U := by
    have hfm := fanout_mul_iterLog_le_iterLogMetaTree n k' c_tree
      (show 2 ≤ ℓ + 1 by clear hF_lo; omega) hx71
    rw [hT_def, Nat.add_sub_cancel] at hfm
    have hfm1 : T.fanout (ℓ + 1) * Nat.iterLog (ℓ + 1) n ≤ Nat.iterLog 1 n :=
      hfm.trans (Nat.iterLog_anti_left n hℓ_ge)
    have h2_div : 2 / γ ≤ (Nat.iterLog (ℓ + 1) n : ℝ) :=
      ((div_le_div_of_nonneg_right (by linarith) hγ.le).trans hct_ceil).trans
        (by exact_mod_cast hx_ge_ct)
    have hmul : (T.fanout (ℓ + 1) : ℝ) * (2 / γ) ≤ Real.logb 2 U :=
      (mul_le_mul_of_nonneg_left h2_div (Nat.cast_nonneg _)).trans
        (by rw [← Nat.cast_mul]; exact (Nat.cast_le.mpr hfm1).trans hlog1_logU)
    exact ((le_div_iff₀ (div_pos zero_lt_two hγ)).mpr hmul).trans_eq (by field_simp)
  have hct_sub : ((c_tree - 2 : ℕ) : ℝ) = (c_tree : ℝ) - 2 := by
    rw [Nat.cast_sub (by clear hF_lo; omega)]; norm_num
  set R := c_R * (n : ℝ) * (Nat.iterLog k' n : ℝ)
  have hR_in : R ≤ (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U := by
    have htel := blockSize_one_mul_iterLog_le_two_mul_iterLogMetaTree n k' c_tree hℓ_ge hy71
    rw [hT_def] at htel
    have h1 : (c_tree - 2) * n * Nat.iterLog k' n ≤ 2 * (T.blockSize ℓ * Nat.iterLog 1 n) :=
      (hb1_mul.trans htel).trans
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.iterLog_anti_left n hℓ_ge)))
    have hct_r : 4 * c_R / γ ≤ ((c_tree - 2 : ℕ) : ℝ) := by
      have h2γ : 2 ≤ 8 / γ := by rw [le_div_iff₀ hγ]; linarith
      have : 4 * c_R / γ + 8 / γ ≤ 808 * (c_R + 1) / γ :=
        (add_div _ _ _).symm.trans_le (div_le_div_of_nonneg_right (by linarith) hγ.le)
      linarith
    have hmul : R * (4 / γ) ≤ 2 * ((T.blockSize ℓ : ℝ) * Real.logb 2 U) := by
      calc R * (4 / γ) = (4 * c_R / γ) * (n : ℝ) * (Nat.iterLog k' n : ℝ) := by dsimp [R]; ring
        _ ≤ ((c_tree - 2 : ℕ) : ℝ) * (n : ℝ) * (Nat.iterLog k' n : ℝ) := by gcongr
        _ ≤ 2 * ((T.blockSize ℓ : ℝ) * (Nat.iterLog 1 n : ℝ)) := by exact_mod_cast h1
        _ ≤ 2 * ((T.blockSize ℓ : ℝ) * Real.logb 2 U) := by gcongr
    exact ((le_div_iff₀ (by positivity : 0 < 4 / γ)).mpr hmul).trans_eq
      (by have : γ ≠ 0 := hγ.ne'; field_simp; ring)
  have hR_out : 100 * R ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)) := by
    set x := Nat.iterLog (ℓ + 1) n
    set q := x / 3
    have h8q : 8 * q ≤ 2 ^ q := eight_mul_le_two_pow (by dsimp [q]; omega)
    have hpow_y : 2 ^ x ≤ Nat.iterLog ℓ n :=
      Nat.pow_log_le_self 2 (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hy71))
    have hmul_pow : 2 * x * 2 ^ q ≤ Nat.iterLog ℓ n :=
      calc 2 * x * 2 ^ q ≤ (8 * q) * 2 ^ q := Nat.mul_le_mul_right _ (by dsimp [q]; omega)
        _ ≤ 2 ^ q * 2 ^ q := Nat.mul_le_mul_right _ h8q
        _ = 2 ^ (2 * q) := by rw [← Nat.pow_add, two_mul]
        _ ≤ 2 ^ x := Nat.pow_le_pow_right Nat.two_pos (by dsimp [q]; omega)
        _ ≤ Nat.iterLog ℓ n := hpow_y
    have hpow_le_F : 2 ^ q ≤ T.fanout (ℓ + 1) := by
      have hdiv_ge : 2 ^ q ≤ Nat.iterLog ℓ n / (2 * x) :=
        (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hmul_pow)
      have hd1 : (ℓ - 1) + 1 = ℓ := Nat.sub_add_cancel hℓ_ge
      have hidx : ℓ + 1 = (ℓ - 1) + 2 := (congrArg (· + 1) hd1).symm
      rw [← hT_def, iterLogMetaTree_fanout, hidx]
      simp only [iterLogFanout, hd1, ← hidx]
      exact (hdiv_ge.trans (_root_.le_max_right _ _)).trans (Nat.le_mul_of_pos_left _ Nat.two_pos)
    have hlog_F : (x : ℝ) / 4 ≤ Real.logb 2 (T.fanout (ℓ + 1)) := by
      have hx_r : (x : ℝ) ≤ 4 * (q : ℝ) := by
        exact_mod_cast (show x ≤ 4 * q by clear hF_lo h8q; dsimp [q]; omega)
      linarith [real_le_logb_of_two_pow_le hpow_le_F]
    have htel1 := blockSize_one_mul_iterLog_le_two_mul_iterLogMetaTree n k' c_tree
      (show 1 ≤ ℓ + 1 by clear hF_lo h8q; omega) hx71
    rw [hT_def] at htel1
    have h1_r : ((c_tree - 2 : ℕ) : ℝ) * (n : ℝ) * (Nat.iterLog k' n : ℝ) ≤
        2 * ((T.blockSize (ℓ + 1) : ℝ) * (x : ℝ)) := by exact_mod_cast hb1_mul.trans htel1
    have hmul1 : 800 * R ≤ 2 * ((T.blockSize (ℓ + 1) : ℝ) * (x : ℝ)) :=
      calc 800 * R = (800 * c_R) * (n : ℝ) * (Nat.iterLog k' n : ℝ) := by dsimp [R]; ring
        _ ≤ ((c_tree - 2 : ℕ) : ℝ) * (n : ℝ) * (Nat.iterLog k' n : ℝ) := by gcongr; linarith
        _ ≤ 2 * ((T.blockSize (ℓ + 1) : ℝ) * (x : ℝ)) := h1_r
    have hmul2 := mul_le_mul_of_nonneg_left hlog_F (Nat.cast_nonneg (T.blockSize (ℓ + 1)))
    linarith
  exact ⟨hblock_half, hF_lo, hF_hi, hR_out, hR_in⟩

theorem outer_budget_time_le {γ t U m : ℝ} (hγ : 0 < γ) (hm : 0 ≤ m)
    (h11 : 11 / γ ≤ Real.logb 2 U) (ht : 6 * t ≤ γ * Real.logb 2 U) :
    7 * m + 2 * m * t ≤ 2 * γ * m * Real.logb 2 U := by
  nlinarith [(div_le_iff₀ hγ).mp h11]

theorem exists_gamma_query {α c_w : ℝ} (hα : 0 < α) (hcw : 0 ≤ c_w) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ (20 + 24 * c_w) * γ = α / (1 + α) :=
  ⟨α / ((20 + 24 * c_w) * (1 + α)), by positivity,
    (div_le_one (by positivity)).mpr (by nlinarith),
    by field_simp⟩

theorem exists_gamma_update {α_V c_w : ℝ} (hα_V : 0 < α_V) (hcw : 0 ≤ c_w) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ (5 + c_w) * γ ≤ min (1 / 4) (α_V / 16) := by
  have hη : 0 < min (1 / 4) (α_V / 16) := by positivity
  exact ⟨min (1 / 20) (min (1 / 4) (α_V / 16) / (5 + c_w)), by positivity,
    (min_le_left _ _).trans (by norm_num),
    (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans_eq
      (mul_div_cancel₀ _ (by positivity))⟩

theorem le_expectedSeqProbes_query_of_det {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) {B : ℝ}
    (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
        ops ((P.runSeq ops).map Prod.fst))
    (hdet : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w},
      (∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      B ≤ ∑' ops, (insertQueryDeleteDist U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal B ≤
      ∑' ops, insertQueryDeleteDist U V n hU hV ops * P.expectedSeqProbes ops := by
  obtain ⟨D_det, _, hcorr_det, hle_exp⟩ :=
    exists_det_indexedScheme_insertQueryDeleteDist hU hV P hcorr
  exact (ofReal_le_tsum_seqProbes_of_toReal_le _ D_det (hdet hcorr_det)).trans hle_exp

theorem le_expectedSeqProbes_update_of_det {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) {B : ℝ}
    (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
      ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
        ops ((P.runSeq ops).map Prod.fst))
    (hdet : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w},
      (∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      B ≤ ∑' ops, (insertDeleteDist U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal B ≤
      ∑' ops, insertDeleteDist U V n hU hV ops * P.expectedSeqProbes ops := by
  obtain ⟨D_det, _, hcorr_det, hle_exp⟩ :=
    exists_det_indexedScheme_insertDeleteDist hU hV P hcorr
  exact (ofReal_le_tsum_seqProbes_of_toReal_le _ D_det (hdet hcorr_det)).trans hle_exp

theorem iterLog_logStar_space_le {U V n cells w : ℕ} {c_R : ℝ} (hn : 2 ≤ n)
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + c_R * (n : ℝ)) :
    1 ≤ Nat.logStar n ∧
      ((cells * w : ℕ) : ℝ) ≤
        benchmarkBits U V n +
          c_R * (n : ℝ) * ((max (Nat.iterLog (Nat.logStar n) n) 1 : ℕ) : ℝ) := by
  have hk1 : 1 ≤ Nat.logStar n :=
    (by decide : 1 ≤ Nat.logStar 2).trans (Nat.logStar_mono hn)
  have hle : Nat.iterLog (Nat.logStar n) n ≤ 1 :=
    (Nat.iterLog_anti_left n (Nat.floorLogStar_le_logStar n)).trans
      (Nat.iterLog_floorLogStar_le_one n)
  exact ⟨hk1, by simpa only [max_eq_right hle, Nat.cast_one, mul_one] using hspace⟩

theorem combine_iterLogStar_and_sublinear {c₁ c₂ L R E : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hL_nn : 0 ≤ L) (hE_nn : 0 ≤ E)
    (hb₁ : c₁ * (n : ℝ) * L ≤ E)
    (hb₂ : R ≤ (n : ℝ) → c₂ * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1) ≤ E) :
    (min c₁ c₂ / 2) * (n : ℝ) * (L + max 0 (Real.logb 2 ((n : ℝ) / max R 1))) ≤ E := by
  have hm₁ : min c₁ c₂ * (n : ℝ) * L ≤ E :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) (Nat.cast_nonneg n)) hL_nn).trans hb₁
  have hm₂ : min c₁ c₂ * (n : ℝ) * max 0 (Real.logb 2 ((n : ℝ) / max R 1)) ≤ E := by
    have hmax_pos : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (_root_.le_max_right R 1)
    by_cases hRn : R ≤ (n : ℝ)
    · have hlog_nn : 0 ≤ Real.logb 2 ((n : ℝ) / max R 1) :=
        Real.logb_nonneg (by norm_num)
          ((one_le_div hmax_pos).mpr (max_le hRn (Nat.one_le_cast.mpr (by omega))))
      rw [max_eq_right hlog_nn]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) (Nat.cast_nonneg n)) hlog_nn).trans
        (hb₂ hRn)
    · have hlog_np : Real.logb 2 ((n : ℝ) / max R 1) ≤ 0 :=
        Real.logb_nonpos (by norm_num) (div_nonneg (Nat.cast_nonneg n) hmax_pos.le)
          ((div_le_one hmax_pos).mpr ((not_le.mp hRn).le.trans (_root_.le_max_left R 1)))
      rwa [max_eq_left hlog_np, mul_zero]
  linarith

theorem mul_le_linear_of_le_half {c L n K : ℝ} (hn : 0 ≤ n) (hL_nn : 0 ≤ L)
    (hc1 : c ≤ 1 / (2 * K)) (hK : 0 < K) (hLK : L ≤ K) :
    c * n * L ≤ n / 2 := by
  have hck : c * L ≤ 1 / 2 :=
    (mul_le_mul hc1 hLK hL_nn (by positivity)).trans_eq (by field_simp)
  calc c * n * L = c * L * n := by ring
    _ ≤ (1 / 2) * n := mul_le_mul_of_nonneg_right hck hn
    _ = n / 2 := by ring

end Cslib.DataStructure.Dictionary.CellProbe
