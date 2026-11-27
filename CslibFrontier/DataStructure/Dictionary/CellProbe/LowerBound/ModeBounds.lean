/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.TreeParams
import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.Base

/-!
# Mode-Generic Iterated-Log and Sublinear-Redundancy Lower Bounds

Proves the mode-parameterized (`withQueries : Bool`) multi-level cell-probe lower bounds
`det_expectedSeqProbes_mode_ge_iterLog` and `det_expectedSeqProbes_mode_ge_sublinear` against an
arbitrary single-node `NodeOuterHyp`. Consumed in parallel by `LowerBound.Query` and
`LowerBound.Update`.

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_mode_ge_iterLog`: `Ω(n · k)`
  expected probes under `iterLog` redundancy.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_mode_ge_sublinear`:
  `Ω(n · log(n / max R 1))` expected probes under sublinear redundancy.
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary

theorem det_expectedSeqProbes_mode_ge_iterLog (withQueries : Bool)
    {γ c_R : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hcR : 0 ≤ c_R) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (_hn : 2 ≤ n) (hU : 2 * n ≤ U) (hV : 1 ≤ V)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
        (_hnode : NodeOuterHyp withQueries hU hV γ D_det),
        c * (n : ℝ) * (k : ℝ) ≤
          ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ) := by
  generalize hc_tree : max 8 (Nat.ceil (808 * (c_R + 1) / γ)) = c_tree
  have hct8 : 8 ≤ c_tree := hc_tree ▸ _root_.le_max_left 8 _
  have hct_ceil : 808 * (c_R + 1) / γ ≤ (c_tree : ℝ) :=
    (Nat.le_ceil _).trans (by rw [← hc_tree]; exact_mod_cast _root_.le_max_right 8 _)
  clear hc_tree
  generalize hs_off : Nat.logStar (max 71 (4 * c_tree * (4 * c_tree + 71))) + 2 = s_off
  generalize hM_exp : max 32 (max (Nat.ceil (11 / γ))
    (2 * (Nat.ceil (4 / γ) + 1) * (2 * (Nat.ceil (4 / γ) + 1) + 2))) = M_exp
  have hM32 : 32 ≤ M_exp := hM_exp ▸ _root_.le_max_left 32 _
  have hM11 : Nat.ceil (11 / γ) ≤ M_exp :=
    hM_exp ▸ (_root_.le_max_left _ _).trans (_root_.le_max_right 32 _)
  have hMrpow : 2 * (Nat.ceil (4 / γ) + 1) * (2 * (Nat.ceil (4 / γ) + 1) + 2) ≤ M_exp :=
    hM_exp ▸ (_root_.le_max_right _ _).trans (_root_.le_max_right 32 _)
  clear hM_exp
  generalize hK_cap : max (2 * s_off + 6) (Nat.logStar (2 ^ M_exp) + 1) = K_cap
  have hK_pos : 1 ≤ K_cap := by rw [← hK_cap]; exact le_trans (by omega) (_root_.le_max_left _ _)
  let c := min (1 / (2 * (K_cap : ℝ))) (γ / 1600)
  refine ⟨c, by positivity, ?_⟩
  intro U V n k cells w hn hU hV hk_lo hk_hi hspace D_det hcorr hnode
  have hc2 : c ≤ γ / 1600 := min_le_right _ _
  have hnU : n ≤ U := Nat.le_trans (Nat.le_mul_of_pos_left n (by decide)) hU
  by_cases hbig : 2 ^ M_exp ≤ n ∧ 2 * s_off + 6 ≤ k
  · obtain ⟨hpow_N₀, hk_s⟩ := hbig
    have hfls : 4 ≤ Nat.floorLogStar n :=
      (Nat.four_le_floorLogStar_two_pow (le_rfl : 32 ≤ 32)).trans
        (Nat.floorLogStar_mono ((Nat.pow_le_pow_right Nat.two_pos hM32).trans hpow_N₀))
    generalize hk' : min k (Nat.floorLogStar n - 1) = k'
    obtain ⟨hH_ge, hk_r, hH1_logU, hmax_le, hn_le_b1, hlevels⟩ :=
      iterLog_tree_bounds hγ hγ1 hcR hct8 hct_ceil hs_off.symm hn hnU hfls hk_s hk_hi hk'.symm
    set T := iterLogMetaTree n k' c_tree
    set H := k' - s_off
    set R := c_R * (n : ℝ) * (Nat.iterLog k' n : ℝ)
    set t := ((H - 1 : ℕ) : ℝ) * (4 * γ / 25)
    have hspace_R : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R :=
      hspace.trans (by dsimp only [R]; gcongr)
    have h11_logU : 11 / γ ≤ Real.logb 2 U :=
      (Nat.le_ceil _).trans (real_le_logb_of_two_pow_le
        (((Nat.pow_le_pow_right Nat.two_pos hM11).trans hpow_N₀).trans hnU))
    have ht_pos : 0 < t := mul_pos (Nat.cast_pos.mpr (by omega)) (by positivity)
    have ht_hi : 6 * t ≤ γ * Real.logb 2 U := probeThresh_le_gamma_logb hγ.le hH1_logU
    have hm_lo_1 : (n : ℝ) ^ (1 - γ / 2) ≤ (T.blockSize 1 : ℝ) := by
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hrpow_eq : (n : ℝ) ^ (1 - γ / 2) * (n : ℝ) ^ (γ / 2) = (n : ℝ) := by
        rw [← Real.rpow_add hn_pos, sub_add_cancel, Real.rpow_one]
      exact le_of_mul_le_mul_right ((mul_le_mul_of_nonneg_left (logb_le_rpow_of_ge_pow hγ
        ((Nat.pow_le_pow_right Nat.two_pos hMrpow).trans hpow_N₀))
          (Real.rpow_nonneg hn_pos.le _)).trans (hrpow_eq.trans_le hn_le_b1))
        (Real.logb_pos one_lt_two (Nat.one_lt_cast.mpr (by omega)))
    have htree := det_expectedSeqProbes_ge_of_outer_tree withQueries hU hV T
      (iterLogMetaTree_horizon n k' c_tree) hH_ge (fun ℓ hℓ => (hlevels ℓ hℓ).1) hγ
      (D_det := D_det) fun ℓ hℓ b hb => by
        obtain ⟨_, hF_lo, hF_hi, hR_out, hR_in⟩ := hlevels ℓ hℓ
        have hℓ_ge : 1 ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
        exact hnode hspace_R T ht_pos hℓ_ge
          ((T.nodeStop_le_horizon hb).trans_eq (iterLogMetaTree_horizon n k' c_tree))
          hF_lo h11_logU ht_hi
          (hm_lo_1.trans (by exact_mod_cast T.blockSize_strictMono.monotone hℓ_ge))
          hF_hi hR_out hR_in
    refine (?_ : c * (n : ℝ) * (k : ℝ) ≤ ((H - 1 : ℕ) : ℝ) * (γ / 400) * (n : ℝ)).trans htree
    calc c * (n : ℝ) * (k : ℝ)
        ≤ (γ / 1600) * (n : ℝ) * (k : ℝ) := by gcongr
      _ = ((k : ℝ) / 4) * (γ / 400) * (n : ℝ) := by ring
      _ ≤ ((H - 1 : ℕ) : ℝ) * (γ / 400) * (n : ℝ) := by gcongr
  · have hk_le_K : k ≤ K_cap := by
      rw [← hK_cap]
      by_cases hn_lt : n < 2 ^ M_exp
      · exact (hk_hi.trans (Nat.logStar_mono hn_lt.le)).trans
          ((Nat.le_succ _).trans (_root_.le_max_right _ _))
      · exact (Nat.lt_of_not_ge fun hge => hbig ⟨Nat.not_lt.mp hn_lt, hge⟩).le.trans
          (_root_.le_max_left _ _)
    exact (mul_le_linear_of_le_half (Nat.cast_nonneg n) (Nat.cast_nonneg k) (min_le_left _ _)
      (by exact_mod_cast hK_pos) (by exact_mod_cast hk_le_K)).trans
      (det_expectedSeqProbes_ge_linear withQueries hU hV (D_det := D_det) hcorr)

private theorem fanout_geomMetaTree_of_two_le (n m₁_half : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (geomMetaTree n m₁_half).fanout ℓ = 2 ^ 64 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  rw [Nat.add_comm 2 d, geomMetaTree_fanout]; rfl

private theorem height_geomMetaTree_le_logb {n : ℕ} (hn : 2 ≤ n) (m₁_half : ℕ) :
    ((geomMetaTree n m₁_half).height : ℝ) ≤ Real.logb 2 n := by
  set T := geomMetaTree n m₁_half
  set H := T.height
  rcases Nat.eq_zero_or_pos H with h0 | hpos
  · rw [h0, Nat.cast_zero]
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.le_of_succ_le hn)
  · have hb : T.blockSize H ≤ n :=
      ((le_height_geomMetaTree_iff hn m₁_half H).mp le_rfl).trans (Nat.div_le_self n 2)
    exact real_le_logb_of_two_pow_le ((T.two_pow_le_blockSize H).trans hb)

theorem det_expectedSeqProbes_mode_ge_sublinear (withQueries : Bool)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (_hn : 2 ≤ n) (hU : 2 * n ≤ U) (hV : 1 ≤ V)
        (_hR_hi : R ≤ (n : ℝ))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
        (_hnode : NodeOuterHyp withQueries hU hV γ D_det),
        c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1) ≤
          ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ) := by
  generalize hM_exp : max (Nat.ceil (2 * ((2 ^ 64 : ℕ) : ℝ) / γ)) (Nat.ceil (11 / γ)) = M_exp
  have hM_fan : ((2 ^ 64 : ℕ) : ℝ) ≤ (γ / 2) * (M_exp : ℝ) :=
    le_of_mul_le_mul_left (((div_le_iff₀ hγ).mp ((Nat.le_ceil _).trans
      (Nat.cast_le.mpr (hM_exp ▸ _root_.le_max_left _ _)))).trans_eq (by ring)) two_pos
  have hM11 : 11 / γ ≤ (M_exp : ℝ) :=
    (Nat.le_ceil _).trans (by rw [← hM_exp]; exact_mod_cast _root_.le_max_right _ _)
  clear hM_exp
  generalize hK_log : max ((M_exp : ℝ) + 1) (268 / γ) = K_log
  have hK_pos : 0 < K_log :=
    (by positivity : 0 < 268 / γ).trans_le (hK_log ▸ _root_.le_max_right _ _)
  have hK_M : (M_exp : ℝ) ≤ K_log :=
    (by linarith : (M_exp : ℝ) ≤ (M_exp : ℝ) + 1).trans (hK_log ▸ _root_.le_max_left _ _)
  have hK_γ : 134 / γ ≤ K_log :=
    (div_le_div_of_nonneg_right (by norm_num) hγ.le).trans (hK_log ▸ _root_.le_max_right _ _)
  clear hK_log
  let c := min (1 / (2 * K_log)) (γ ^ 2 / 104800)
  refine ⟨c, by positivity, ?_⟩
  intro U V n cells w R hn hU hV hR_hi hspace D_det hcorr hnode
  set R₁ := max R 1
  have hR1_ge : 1 ≤ R₁ := _root_.le_max_right R 1
  have hR_le_R1 : R ≤ R₁ := _root_.le_max_left R 1
  have hn1 : (1 : ℝ) ≤ n := mod_cast (by decide : 1 ≤ 2).trans hn
  have hR1_le_n : R₁ ≤ (n : ℝ) := max_le hR_hi hn1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog_div_nn : 0 ≤ Real.logb 2 ((n : ℝ) / R₁) :=
    Real.logb_nonneg (by norm_num) ((one_le_div (by positivity)).mpr hR1_le_n)
  generalize hm₁ : max (Nat.ceil R₁) (Nat.ceil ((n : ℝ) ^ (1 - γ / 2))) = m₁_half
  have hm₁_R : R₁ ≤ (m₁_half : ℝ) :=
    (Nat.le_ceil R₁).trans (by rw [← hm₁]; exact_mod_cast _root_.le_max_left _ _)
  have hm₁_n : (n : ℝ) ^ (1 - γ / 2) ≤ (m₁_half : ℝ) :=
    (Nat.le_ceil _).trans (by rw [← hm₁]; exact_mod_cast _root_.le_max_right _ _)
  have hm₁_pos : 1 ≤ m₁_half :=
    (Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne').trans
      (hm₁ ▸ _root_.le_max_left _ _)
  have hm₁_ub : (m₁_half : ℝ) ≤ 2 * max R₁ ((n : ℝ) ^ (1 - γ / 2)) := by
    have h2ceil {x : ℝ} (hx : 1 ≤ x) : (Nat.ceil x : ℝ) ≤ 2 * x :=
      (Nat.ceil_lt_add_one (by linarith)).le.trans (by linarith)
    rw [← hm₁, Nat.cast_max, mul_max_of_nonneg _ _ zero_le_two]
    exact max_le_max (h2ceil hR1_ge) (h2ceil (Real.one_le_rpow hn1 (by linarith)))
  clear hm₁
  set T := geomMetaTree n m₁_half
  set H := T.height
  have hlog_H : Real.logb 2 ((n : ℝ) / R₁) ≤ (2 / γ) * (3 + 64 * (H : ℝ)) := by
    have hlt_nat := max_eq_right hm₁_pos ▸ lt_mul_pow_height_geomMetaTree n m₁_half
    have hpow_eq : (8 : ℝ) * (((2 ^ 64 : ℕ) : ℝ) ^ H) = (2 : ℝ) ^ (3 + 64 * H) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, pow_add]; ring
    have hle_max : (n : ℝ) ≤ max R₁ ((n : ℝ) ^ (1 - γ / 2)) * (2 : ℝ) ^ (3 + 64 * H) :=
      calc (n : ℝ) ≤ 4 * (m₁_half : ℝ) * ((2 ^ 64 : ℕ) : ℝ) ^ H := by exact_mod_cast hlt_nat.le
        _ ≤ 4 * (2 * max R₁ ((n : ℝ) ^ (1 - γ / 2))) * (((2 ^ 64 : ℕ) : ℝ) ^ H) := by gcongr
        _ = max R₁ ((n : ℝ) ^ (1 - γ / 2)) * ((8 : ℝ) * (((2 ^ 64 : ℕ) : ℝ) ^ H)) := by ring
        _ = max R₁ ((n : ℝ) ^ (1 - γ / 2)) * (2 : ℝ) ^ (3 + 64 * H) := by rw [hpow_eq]
    rcases le_total ((n : ℝ) ^ (1 - γ / 2)) R₁ with hmax | hmax
    · rw [max_eq_left hmax] at hle_max
      have hl := logb_le_real_of_le_two_pow (by positivity)
        ((div_le_iff₀ (show 0 < R₁ by positivity)).mpr (hle_max.trans_eq (mul_comm _ _)))
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hl
      have h2γ : 1 ≤ 2 / γ := (one_le_div hγ).mpr (by linarith)
      exact hl.trans ((one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right h2γ (by positivity)))
    · rw [max_eq_right hmax] at hle_max
      have hl := Real.logb_le_logb_of_le one_lt_two hn_pos hle_max
      rw [Real.logb_mul (by positivity) (by positivity),
        Real.logb_rpow_eq_mul_logb_of_pos hn_pos, Real.logb_pow,
        Real.logb_self_eq_one one_lt_two, mul_one,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hl
      have hlogn : Real.logb 2 n ≤ (2 / γ) * (3 + 64 * (H : ℝ)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hγ]; linarith
      exact (Real.logb_le_logb_of_le (by norm_num) (by positivity)
        (div_le_self hn_pos.le hR1_ge)).trans hlogn
  have hnU : n ≤ U := Nat.le_trans (Nat.le_mul_of_pos_left n (by decide)) hU
  by_cases hbig : 2 ^ M_exp ≤ n ∧ 2 ≤ H
  · obtain ⟨hpow_N₀, hH_ge⟩ := hbig
    have hM_logU : (M_exp : ℝ) ≤ Real.logb 2 U := real_le_logb_of_two_pow_le (hpow_N₀.trans hnU)
    have h11_logU : 11 / γ ≤ Real.logb 2 U := hM11.trans hM_logU
    have hfan_U : ((2 ^ 64 : ℕ) : ℝ) ≤ (γ / 2) * Real.logb 2 U :=
      hM_fan.trans (mul_le_mul_of_nonneg_left hM_logU (by positivity))
    have hH_logU : ((H - 1 : ℕ) : ℝ) ≤ Real.logb 2 U :=
      ((Nat.cast_le.mpr (Nat.sub_le H 1)).trans (height_geomMetaTree_le_logb hn m₁_half)).trans
        (Real.logb_le_logb_of_le (by norm_num) hn_pos (by exact_mod_cast hnU))
    set t := ((H - 1 : ℕ) : ℝ) * (4 * γ / 25)
    have ht_pos : 0 < t := mul_pos (Nat.cast_pos.mpr (by omega)) (by positivity)
    have ht_hi : 6 * t ≤ γ * Real.logb 2 U := probeThresh_le_gamma_logb hγ.le hH_logU
    have hspace_R1 : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R₁ := hspace.trans (by linarith)
    have hb1_ge : 2 * (m₁_half : ℝ) ≤ (T.blockSize 1 : ℝ) := by
      simpa [T, max_eq_right hm₁_pos] using
        Nat.cast_le (α := ℝ).mpr (blockSize_geomMetaTree n m₁_half le_rfl).symm.le
    have htree := det_expectedSeqProbes_ge_of_outer_tree withQueries hU hV T
      (geomMetaTree_horizon n m₁_half) hH_ge
      (fun ℓ hℓ => (le_height_geomMetaTree_iff hn m₁_half (ℓ + 1)).mp (Finset.mem_Ico.mp hℓ).2)
      hγ (D_det := D_det) fun ℓ hℓ b hb => by
        have hℓ_ge : 1 ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
        have hfan : T.fanout (ℓ + 1) = 2 ^ 64 := fanout_geomMetaTree_of_two_le n m₁_half (by omega)
        have hbℓ_ge : 2 * (m₁_half : ℝ) ≤ (T.blockSize ℓ : ℝ) :=
          hb1_ge.trans (by exact_mod_cast T.blockSize_strictMono.monotone hℓ_ge)
        have hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (T.blockSize ℓ : ℝ) :=
          by linarith [Nat.cast_nonneg (α := ℝ) m₁_half]
        have hR_outer : 100 * R₁ ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)) := by
          have hb1_next : 2 * R₁ ≤ (T.blockSize (ℓ + 1) : ℝ) :=
            (mul_le_mul_of_nonneg_left hm₁_R (by norm_num)).trans
              (hb1_ge.trans (by exact_mod_cast T.blockSize_strictMono.monotone (by omega)))
          rw [hfan, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
            Real.logb_self_eq_one one_lt_two, mul_one, Nat.cast_ofNat]
          linarith
        have hR_in : R₁ ≤ (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U := by
          have hγU : 1 ≤ (γ / 2) * Real.logb 2 U := by linarith [(div_le_iff₀ hγ).mp h11_logU]
          have hmR : R₁ ≤ (T.blockSize ℓ : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) m₁_half]
          exact (one_mul R₁).symm.trans_le
            ((mul_le_mul hγU hmR (by positivity) (by positivity)).trans_eq (by ring))
        exact hnode hspace_R1 T ht_pos hℓ_ge
          ((T.nodeStop_le_horizon hb).trans_eq (geomMetaTree_horizon n m₁_half))
          hfan.ge h11_logU ht_hi hm_lo (hfan ▸ hfan_U) hR_outer hR_in
    refine (?_ : c * (n : ℝ) * Real.logb 2 ((n : ℝ) / R₁) ≤
      ((H - 1 : ℕ) : ℝ) * (γ / 400) * (n : ℝ)).trans htree
    have hH_sub : (H : ℝ) - 1 = ((H - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hlog_H1 : Real.logb 2 ((n : ℝ) / R₁) ≤ (262 / γ) * ((H - 1 : ℕ) : ℝ) :=
      hlog_H.trans ((mul_le_mul_of_nonneg_left
        (by linarith [(Nat.ofNat_le_cast.mpr hH_ge : (2 : ℝ) ≤ H)] :
          3 + 64 * (H : ℝ) ≤ 131 * ((H - 1 : ℕ) : ℝ))
        (by positivity)).trans_eq (by ring))
    calc c * (n : ℝ) * Real.logb 2 ((n : ℝ) / R₁)
        ≤ (γ ^ 2 / 104800) * (n : ℝ) * ((262 / γ) * ((H - 1 : ℕ) : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (min_le_right _ _) hn_pos.le) hlog_H1
            hlog_div_nn (by positivity)
      _ = ((H - 1 : ℕ) : ℝ) * (γ / 400) * (n : ℝ) := by field_simp; ring
  · have hlog_le_K : Real.logb 2 ((n : ℝ) / R₁) ≤ K_log := by
      by_cases hn_lt : n < 2 ^ M_exp
      · exact (logb_le_real_of_le_two_pow (by positivity)
          ((div_le_self hn_pos.le hR1_ge).trans (by exact_mod_cast hn_lt.le))).trans hK_M
      · have hH_le1 : (H : ℝ) ≤ 1 := mod_cast Nat.lt_succ_iff.mp
          (Nat.lt_of_not_ge fun hge => hbig ⟨Nat.not_lt.mp hn_lt, hge⟩)
        exact hlog_H.trans
          ((mul_le_mul_of_nonneg_left (by linarith) (by positivity)).trans
            ((by ring : (2 / γ) * (3 + 64 * 1) = 134 / γ).symm ▸ hK_γ))
    exact (mul_le_linear_of_le_half hn_pos.le hlog_div_nn (min_le_left _ _) hK_pos hlog_le_K).trans
      (det_expectedSeqProbes_ge_linear withQueries hU hV (D_det := D_det) hcorr)

end Cslib.DataStructure.Dictionary.CellProbe
