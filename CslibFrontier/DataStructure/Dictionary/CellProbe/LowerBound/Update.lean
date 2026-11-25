/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.OuterGame
import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.ModifiedInner
import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.ModeBounds

/-!
# Update-Only Cell-Probe Lower Bounds (Theorem 1.3)

Public deterministic and zero-error randomized cell-probe lower bounds on `insertDeleteDist` under
`U ≥ 3 * n` and `V ≥ U ^ (2 + α_V) / n ^ 2` without query-time constraints ([LiLiangYuZhou2023],
Theorem 1.3(1)–(2), Section 8, pp. 27–30 / PDF pp. 28–31).

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_iterLog`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_iterLog`
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_iterLogStar`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_iterLogStar`
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_sublinear`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_sublinear`
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_iterLogStar_add_log_div`
* `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_iterLogStar_add_log_div`
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary

/-- Unified single-node update-only `OuterLemma` on `insertDeleteDist` under
`U ^ (2 + α_V) ≤ V * n ^ 2` and `w ≤ c_w * (log₂ U + log₂ V)` ([LiLiangYuZhou2023], Section 8,
pp. 27–30 / PDF pp. 28–31). -/
private theorem outer_lemma_update_of_val_ge {U V n cells w : ℕ} {α_V c_w γ : ℝ}
    (hα_V : 0 < α_V) (hγ : 0 < γ)
    (hγ_le : (5 + c_w) * γ ≤ min (1 / 4) (α_V / 16))
    (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
    (hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
    (hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) :
    NodeOuterHyp false (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV γ D_det := by
  intro R t hspace T ht ℓ b hℓ ht_stop hF_lo h11 ht_hi _hm_lo hF_hi hR_outer hR_in
  have hbud : 2 * R + 7 * (T.blockSize ℓ : ℝ) + 2 * (T.blockSize ℓ : ℝ) * t +
      γ * (T.blockSize ℓ : ℝ) * (w : ℝ) + 2 * γ * (T.blockSize ℓ : ℝ) * Real.logb 2 U ≤
      ((T.blockSize ℓ : ℝ) / 2) * Real.logb 2 V -
        (T.blockSize ℓ : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
    clear hF_lo
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hU_pos : (0 : ℝ) < U := Nat.cast_pos.mpr (by omega)
    have hV_pos : (0 : ℝ) < V := Nat.cast_pos.mpr hV
    have hlogU_nn : 0 ≤ Real.logb 2 U :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ U by omega))
    have hlogV_nn : 0 ≤ Real.logb 2 V :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hV)
    have hlogn_nn : 0 ≤ Real.logb 2 n :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
    have hlog_V_lo : (2 + α_V) * Real.logb 2 U ≤ Real.logb 2 V + 2 * Real.logb 2 n := by
      have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (Real.rpow_pos_of_pos hU_pos _) hV_lo
      rwa [Real.logb_rpow_eq_mul_logb_of_pos hU_pos,
        Real.logb_mul hV_pos.ne' (pow_ne_zero 2 hn_pos.ne'), Real.logb_pow, Nat.cast_ofNat] at hl
    set gap := (1 / 2) * Real.logb 2 V - Real.logb 2 U + Real.logb 2 n
    have hgap1 : (α_V / 2) * Real.logb 2 U ≤ gap := by dsimp only [gap]; linarith
    set η := min (1 / 4) (α_V / 16)
    have hη_pos : 0 < η := by dsimp only [η]; positivity
    have hconv1 : 4 * η * Real.logb 2 U ≤ (1 - 2 * η) * gap := by
      have h1 : 4 * η ≤ (1 - 2 * η) * (α_V / 2) :=
        (show 4 * η = (1 / 2) * (8 * η) by ring).trans_le <|
          mul_le_mul (by linarith [min_le_left (1 / 4 : ℝ) (α_V / 16)])
            (by linarith [min_le_right (1 / 4 : ℝ) (α_V / 16)]) (by positivity)
            (by linarith [min_le_left (1 / 4 : ℝ) (α_V / 16)])
      exact ((mul_le_mul_of_nonneg_right h1 hlogU_nn).trans_eq (mul_assoc _ _ _)).trans
        (mul_le_mul_of_nonneg_left (a := 1 - 2 * η) hgap1
          (by linarith [min_le_left (1 / 4 : ℝ) (α_V / 16)]))
    have hgap_lb : η * (Real.logb 2 U + Real.logb 2 V) ≤ gap := by
      have h4 := mul_le_mul_of_nonneg_left (show Real.logb 2 U + Real.logb 2 V ≤
        3 * Real.logb 2 U + 2 * gap by dsimp only [gap]; linarith [hlogn_nn]) hη_pos.le
      have := mul_nonneg hη_pos.le hlogU_nn
      linarith
    set m := (T.blockSize ℓ : ℝ)
    have hm_nn : 0 ≤ m := Nat.cast_nonneg _
    have h12 := outer_budget_time_le hγ hm_nn h11 ht_hi
    have h3 : γ * m * (w : ℝ) ≤ c_w * γ * m * (Real.logb 2 U + Real.logb 2 V) := by
      have := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ γ * m); linarith
    have h4 : 5 * γ * m * Real.logb 2 U ≤ 5 * γ * m * (Real.logb 2 U + Real.logb 2 V) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hlogV_nn) (by positivity)
    have h5 : ((5 + c_w) * γ) * (m * (Real.logb 2 U + Real.logb 2 V)) ≤
        η * (m * (Real.logb 2 U + Real.logb 2 V)) :=
      mul_le_mul_of_nonneg_right hγ_le (by positivity)
    have h6 : η * (m * (Real.logb 2 U + Real.logb 2 V)) ≤ m * gap :=
      (mul_le_mul_of_nonneg_left hgap_lb hm_nn).trans_eq' (by ring)
    rw [show (m / 2) * Real.logb 2 V - m * Real.logb 2 ((U : ℝ) / (n : ℝ)) = m * gap by
      rw [Real.logb_div hU_pos.ne' hn_pos.ne']
      dsimp only [gap]; ring]
    linarith
  exact outer_lemma_insertDelete hU hV hspace hspace T hcorr hγ ht hℓ ht_stop hF_lo hF_hi
    hR_outer hbud

/-- Deterministic **Theorem 1.3(1)** ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and
Section 8, pp. 27–30 / PDF pp. 28–31): update-only (`insertDeleteDist`) `Ω(n * k)` cell-probe
lower bound for `3 * n ≤ U` and `U ^ (2 + α_V) ≤ V * n ^ 2` under redundancy
`≤ c_R * n * max 1 (log^{(k)} n)` (correctness up to `3 * n + 1` allows one trailing `.query` step
so `decodeDict` is well-defined after the `3 * n` `PUnit`-returning updates). -/
theorem det_expectedSeqProbes_update_ge_iterLog {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (k : ℝ) ≤
          ∑' ops, (insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨γ, hγ, hγ1, hγ_le⟩ := exists_gamma_update hα_V hcw
  obtain ⟨c, hc, hmode⟩ := det_expectedSeqProbes_mode_ge_iterLog false hγ hγ1 hcR
  exact ⟨c, hc, fun {_U _V n _k _cells _w} hn hU hV hV_lo hk_lo hk_hi hw hspace {_D_det} hcorr =>
    hmode hn (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV hk_lo hk_hi hspace
      (by simpa only [modeHorizon, modeStride, Bool.false_eq_true, ↓reduceIte,
        show n + 2 * n = 3 * n by ring] using hcorr)
      (outer_lemma_update_of_val_ge hα_V hγ hγ_le hn hU hV hV_lo hw hcorr)⟩

/-- Zero-error randomized **Theorem 1.3(1)** ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and
Section 8, pp. 27–30 / PDF pp. 28–31) in the Las Vegas oblivious model (`3 * n + 1` correctness
horizon for `decodeDict` on update-only `insertDeleteDist`). -/
theorem expectedSeqProbes_update_ge_iterLog {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * (k : ℝ)) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_update_ge_iterLog hα_V hcR hcw
  exact ⟨c, hc, fun hn hU hV hV_lo hk_lo hk_hi hw hspace P hcorr =>
    le_expectedSeqProbes_update_of_det _ hV P hcorr (hdet hn hU hV hV_lo hk_lo hk_hi hw hspace)⟩

/-- Deterministic `Ω(n * log* n)` specialization of Theorem 1.3(1) at `k = Nat.logStar n` (`O(n)`
redundancy). -/
theorem det_expectedSeqProbes_update_ge_iterLogStar {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + c_R * (n : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (Nat.logStar n : ℝ) ≤
          ∑' ops, (insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_update_ge_iterLog hα_V hcR hcw
  exact ⟨c, hc, fun hn hU hV hV_lo hw hspace _ hcorr =>
    let ⟨hk1, hspace'⟩ := iterLog_logStar_space_le hn hspace
    hdet hn hU hV hV_lo hk1 le_rfl hw hspace' hcorr⟩

/-- Zero-error randomized `Ω(n * log* n)` specialization of Theorem 1.3(1) at `k = Nat.logStar n`
(Las Vegas oblivious model). -/
theorem expectedSeqProbes_update_ge_iterLogStar {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + c_R * (n : ℝ))
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * (Nat.logStar n : ℝ)) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_update_ge_iterLogStar hα_V hcR hcw
  exact ⟨c, hc, fun hn hU hV hV_lo hw hspace P hcorr =>
    le_expectedSeqProbes_update_of_det _ hV P hcorr (hdet hn hU hV hV_lo hw hspace)⟩

/-- Deterministic **Theorem 1.3(2)** ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and
Section 8, pp. 27–30 / PDF pp. 28–31): update-only (`insertDeleteDist`)
`Ω(n * log₂(n / max R 1))` cell-probe lower bound for `3 * n ≤ U`, `U ^ (2 + α_V) ≤ V * n ^ 2`,
and `R ≤ n` (vanishing at the `R = n` boundary, with `3 * n + 1` correctness horizon for
`decodeDict`). -/
theorem det_expectedSeqProbes_update_ge_sublinear {α_V c_w : ℝ}
    (hα_V : 0 < α_V) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1) ≤
          ∑' ops, (insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨γ, hγ, hγ1, hγ_le⟩ := exists_gamma_update hα_V hcw
  obtain ⟨c, hc, hmode⟩ := det_expectedSeqProbes_mode_ge_sublinear false hγ hγ1
  exact ⟨c, hc, fun {_U _V n _cells _w _R} hn hU hV hV_lo hR_hi hw hspace {_D_det} hcorr =>
    hmode hn (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV hR_hi hspace
      (by simpa only [modeHorizon, modeStride, Bool.false_eq_true, ↓reduceIte,
        show n + 2 * n = 3 * n by ring] using hcorr)
      (outer_lemma_update_of_val_ge hα_V hγ hγ_le hn hU hV hV_lo hw hcorr)⟩

/-- Zero-error randomized **Theorem 1.3(2)** ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and
Section 8, pp. 27–30 / PDF pp. 28–31) in the Las Vegas oblivious model (vanishing at `R = n`). -/
theorem expectedSeqProbes_update_ge_sublinear {α_V c_w : ℝ}
    (hα_V : 0 < α_V) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1)) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_update_ge_sublinear hα_V hcw
  exact ⟨c, hc, fun hn hU hV hV_lo hR_hi hw hspace P hcorr =>
    le_expectedSeqProbes_update_of_det _ hV P hcorr (hdet hn hU hV hV_lo hR_hi hw hspace)⟩

/-- Combined deterministic **Theorem 1.3(1)–(2)**
(`Ω(n * (log* n + log₂(n / max R 1)))`) on `insertDeleteDist` across all `R ≤ c_R * n`
([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and Section 8, p. 27 / PDF p. 28). -/
theorem det_expectedSeqProbes_update_ge_iterLogStar_add_log_div {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1))) ≤
          ∑' ops, (insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨c₁, hc₁, hdet₁⟩ := det_expectedSeqProbes_update_ge_iterLogStar hα_V hcR hcw
  obtain ⟨c₂, hc₂, hdet₂⟩ := det_expectedSeqProbes_update_ge_sublinear hα_V hcw
  exact ⟨min c₁ c₂ / 2, by positivity, fun hn hU hV hV_lo hR_hi hw hspace _ hcorr =>
    combine_iterLogStar_and_sublinear hn (Nat.cast_nonneg _)
      (tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
      (hdet₁ hn hU hV hV_lo hw (hspace.trans (by linarith)) hcorr)
      fun hRn => hdet₂ hn hU hV hV_lo hRn hw hspace hcorr⟩

/-- Combined zero-error randomized **Theorem 1.3(1)–(2)**
(`Ω(n * (log* n + log₂(n / max R 1)))`) on `insertDeleteDist` across all `R ≤ c_R * n` in the
Las Vegas oblivious model ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and Section 8, p. 27 /
PDF p. 28). -/
theorem expectedSeqProbes_update_ge_iterLogStar_add_log_div {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) *
          ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1)))) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_update_ge_iterLogStar_add_log_div hα_V hcR hcw
  exact ⟨c, hc, fun hn hU hV hV_lo hR_hi hw hspace P hcorr =>
    le_expectedSeqProbes_update_of_det _ hV P hcorr (hdet hn hU hV hV_lo hR_hi hw hspace)⟩

end Cslib.DataStructure.Dictionary.CellProbe
