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
# Insert-Query-Delete Lower Bounds (Theorems 1.1 and 1.2)

Public deterministic and zero-error randomized cell-probe lower bounds on `insertQueryDeleteDist`
across all alphabet/value regimes (`V ≤ U ^ 3` from `OuterGame` and `V > U ^ 3` from Section 8.1
`ModifiedInner`): Theorem 1.1 / 3.1 (`Ω(k)` and `Ω(log* n)`), Theorem 1.2 / 6.1
(`Ω(log(n / max R 1))`), and their combined trade-off.

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_of_iterLog_redundancy`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_of_iterLog_redundancy`
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_iterLogStar`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_iterLogStar`
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_of_sublinear_redundancy`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_of_sublinear_redundancy`
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_iterLogStar_add_log_div`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_iterLogStar_add_log_div`
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary

/-- Unified single-node `OuterLemma` on `insertQueryDeleteDist` across both `V ≤ U ^ 3` (Section 5)
and `V > U ^ 3` (Section 8.1) under `w ≤ c_w * (log₂ U + log₂ V)`. -/
private theorem outer_lemma_both_val_regimes {U V n cells w : ℕ} {α c_w γ : ℝ}
    (hα : 0 < α) (hcw : 0 ≤ c_w) (hγ : 0 < γ)
    (hγ_eq : (20 + 24 * c_w) * γ = α / (1 + α))
    (hn : 2 ≤ n) (hU : 4 * n ≤ U) (hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
    (hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) :
    NodeOuterHyp true (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV γ D_det := by
  intro R t hspace T ht ℓ b hℓ ht_stop hF_lo h11 ht_hi hm_lo hF_hi hR_outer hR_in
  have hα_frac : α / (1 + α) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by clear hF_lo; omega)
  have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (show 0 < U by clear hF_lo; omega)
  have hV_pos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  have hlogU_nn : 0 ≤ Real.logb 2 U :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ U by clear hF_lo; omega))
  have hlogn_nn : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by clear hF_lo; omega))
  have h11_mul : 11 ≤ γ * Real.logb 2 U := by have := (div_le_iff₀ hγ).mp h11; linarith
  set m := (T.blockSize ℓ : ℝ)
  have hm_nn : 0 ≤ m := Nat.cast_nonneg _
  by_cases hV3 : (V : ℝ) ≤ (U : ℝ) ^ 3
  · have hbud : R + 11 * m + 6 * m * t + γ * m * (w : ℝ) + (3 / 2) * γ * m * Real.logb 2 U ≤
        (m / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
      clear hF_lo
      have hlogV : Real.logb 2 V ≤ 3 * Real.logb 2 U := by
        simpa only [Real.logb_pow, Nat.cast_ofNat] using
          Real.logb_le_logb_of_le one_lt_two hV_pos hV3
      have hsumV : Real.logb 2 U + Real.logb 2 V ≤ 4 * Real.logb 2 U := by linarith only [hlogV]
      have hw_le : (w : ℝ) ≤ 4 * c_w * Real.logb 2 U := by
        linarith only [hw, mul_le_mul_of_nonneg_left hsumV hcw]
      have hlog_poly : (1 + α) * Real.logb 2 n ≤ Real.logb 2 U := by
        simpa only [Real.logb_rpow_eq_mul_logb_of_pos hn_pos] using
          Real.logb_le_logb_of_le one_lt_two (Real.rpow_pos_of_pos hn_pos _) hU_poly
      have hlog_div : (α / (1 + α)) * Real.logb 2 U ≤ Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
        rw [Real.logb_div hU_pos.ne' hn_pos.ne']
        have h1 : Real.logb 2 n ≤ Real.logb 2 U / (1 + α) :=
          (le_div_iff₀ (by positivity : 0 < 1 + α)).mpr (by linarith)
        have hid : Real.logb 2 U - Real.logb 2 U / (1 + α) = (α / (1 + α)) * Real.logb 2 U := by
          field_simp; ring
        linarith
      have hcoef : (4 + 4 * c_w) * γ ≤ α / (2 * (1 + α)) := by
        rw [mul_comm 2 (1 + α), ← div_div, ← hγ_eq]
        linarith only [mul_nonneg hcw hγ.le, hγ]
      have h4 : ((4 + 4 * c_w) * γ) * (m * Real.logb 2 U) ≤
          (α / (2 * (1 + α))) * (m * Real.logb 2 U) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      have h5 : (α / (2 * (1 + α))) * (m * Real.logb 2 U) ≤
          (m / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)) :=
        calc _ = (m / 2) * ((α / (1 + α)) * Real.logb 2 U) := by rw [div_mul_eq_div_div]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hlog_div (by positivity)
      have hγm : 0 ≤ γ * m := by positivity
      linarith only [hR_in, mul_le_mul_of_nonneg_right h11_mul hm_nn,
        mul_le_mul_of_nonneg_right ht_hi hm_nn, mul_le_mul_of_nonneg_left hw_le hγm, h4, h5]
    exact outer_lemma_insertQueryDelete hU hV hspace hspace T hcorr hγ ht hℓ ht_stop hm_lo hF_lo
      hF_hi hR_outer hbud
  · push Not at hV3
    have hbud : 2 * R + 7 * m + 2 * m * t + γ * m * (w : ℝ) + 2 * γ * m * Real.logb 2 U ≤
        (m / 2) * Real.logb 2 V - m * Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
      clear hF_lo
      have hlogV : 3 * Real.logb 2 U ≤ Real.logb 2 V := by
        simpa only [Real.logb_pow, Nat.cast_ofNat] using
          (Real.logb_lt_logb one_lt_two (by positivity) hV3).le
      have hsumV : Real.logb 2 U + Real.logb 2 V ≤ 2 * Real.logb 2 V := by
        linarith only [hlogV, hlogU_nn]
      have hw_le : (w : ℝ) ≤ 2 * c_w * Real.logb 2 V := by
        linarith only [hw, mul_le_mul_of_nonneg_left hsumV hcw]
      have hγ20 : 5 * γ ≤ 1 / 4 := by linarith only [mul_nonneg hcw hγ.le, hγ_eq, hα_frac]
      have hcw12 : 2 * c_w * γ ≤ 1 / 12 := by linarith only [hγ, hγ_eq, hα_frac]
      have hgap_V : (1 / 4) * Real.logb 2 U + (1 / 12) * Real.logb 2 V ≤
          (1 / 2) * Real.logb 2 V - Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
        rw [Real.logb_div hU_pos.ne' hn_pos.ne']; linarith only [hlogV, hlogn_nn]
      have h12 : 7 * m + 2 * m * t ≤ 2 * γ * m * Real.logb 2 U :=
        outer_budget_time_le hγ hm_nn h11 ht_hi
      have h4 : (5 * γ) * (m * Real.logb 2 U) ≤ (1 / 4) * (m * Real.logb 2 U) :=
        mul_le_mul_of_nonneg_right hγ20 (by positivity)
      have h5 : (2 * c_w * γ) * (m * Real.logb 2 V) ≤ (1 / 12) * (m * Real.logb 2 V) :=
        mul_le_mul_of_nonneg_right hcw12 (mul_nonneg hm_nn (by linarith only [hlogV, hlogU_nn]))
      have h6 := mul_le_mul_of_nonneg_left hgap_V hm_nn
      have hγm : 0 ≤ γ * m := by positivity
      linarith only [hR_in, h12, mul_le_mul_of_nonneg_left hw_le hγm, h4, h5, h6]
    exact outer_lemma_largeVal_insertQueryDelete
      (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV hspace hspace T hcorr hγ
      ht hℓ ht_stop hF_lo hF_hi hR_outer hbud

/-- Deterministic **Theorem 1.1 / Theorem 3.1** ([LiLiangYuZhou2023], Section 1, p. 1 / PDF p. 2 and
Section 3, pp. 10–13 / PDF pp. 11–14; Section 7, pp. 26–27 / PDF pp. 27–28): for any `α > 0`,
`c_R ≥ 0`, and `c_w ≥ 0`, there exists `c > 0` such that any step-indexed `IndexedScheme` exact on
admissible histories up to `4 * n + 1` with space
`≤ benchmarkBits U V n + c_R * n * max 1 (log^{(k)} n)` incurs at least `c * n * k` expected cell
probes on `insertQueryDeleteDist`. -/
theorem det_expectedSeqProbes_ge_of_iterLog_redundancy {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (k : ℝ) ≤
          ∑' ops, (insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨γ, hγ, hγ1, hγ_eq⟩ := exists_gamma_query hα hcw
  obtain ⟨c, hc, hmode⟩ := det_expectedSeqProbes_mode_ge_iterLog true hγ hγ1 hcR
  exact ⟨c, hc, fun {_U _V n _k _cells _w} hn hU hU_poly hV hk_lo hk_hi hw hspace {_D_det} hcorr =>
    hmode hn (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV hk_lo hk_hi hspace
      (by
        have h4n : n + 3 * n = 4 * n := by omega
        simpa only [modeHorizon, modeStride, ↓reduceIte, h4n] using hcorr)
      (outer_lemma_both_val_regimes hα hcw hγ hγ_eq hn hU hU_poly hV hw hcorr)⟩

/-- Zero-error randomized **Theorem 1.1 / Theorem 3.1** ([LiLiangYuZhou2023], Section 1, p. 1 /
PDF p. 2 and Section 3, pp. 10–13 / PDF pp. 11–14): any zero-error (Las Vegas)
`CellProbe.Randomized.Scheme` on oblivious `insertQueryDeleteDist` storing `n` keys in `[U]`
(`U ≥ n ^ (1 + α)`) with `≤ benchmarkBits U V n + c_R * n * max 1 (log^{(k)} n)` bits of memory
incurs `≥ c * n * k` expected cell probes (bounded-error Monte Carlo schemes and adaptive
adversaries are not covered). -/
theorem expectedSeqProbes_ge_of_iterLog_redundancy {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * (k : ℝ)) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_ge_of_iterLog_redundancy hα hcR hcw
  exact ⟨c, hc, fun hn hU hU_poly hV hk_lo hk_hi hw hspace P hcorr =>
    le_expectedSeqProbes_query_of_det _ hV P hcorr (hdet hn hU hU_poly hV hk_lo hk_hi hw hspace)⟩

/-- Deterministic `Ω(n * log* n)` specialization of Theorem 1.1 at `k = Nat.logStar n` (`O(n)`
redundancy). -/
theorem det_expectedSeqProbes_ge_iterLogStar {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + c_R * (n : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (Nat.logStar n : ℝ) ≤
          ∑' ops, (insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_ge_of_iterLog_redundancy hα hcR hcw
  refine ⟨c, hc, fun hn hU hU_poly hV hw hspace _ hcorr => ?_⟩
  obtain ⟨hk1, hspace'⟩ := iterLog_logStar_space_le hn hspace
  exact hdet hn hU hU_poly hV hk1 le_rfl hw hspace' hcorr

/-- Zero-error randomized `Ω(n * log* n)` specialization of Theorem 1.1 at `k = Nat.logStar n`
(`O(n)` bits of redundancy, Las Vegas oblivious model). -/
theorem expectedSeqProbes_ge_iterLogStar {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + c_R * (n : ℝ))
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * (Nat.logStar n : ℝ)) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_ge_iterLogStar hα hcR hcw
  exact ⟨c, hc, fun hn hU hU_poly hV hw hspace P hcorr =>
    le_expectedSeqProbes_query_of_det _ hV P hcorr (hdet hn hU hU_poly hV hw hspace)⟩

/-- Deterministic **Theorem 1.2 / Theorem 6.1** ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and
Section 6, pp. 25–26 / PDF pp. 26–27): for any `α > 0` and `c_w ≥ 0`, there exists `c > 0` such that
any step-indexed `IndexedScheme` exact on admissible histories up to `4 * n + 1` with `R ≤ n` bits
of redundancy (`cells * w ≤ benchmarkBits U V n + R`) incurs at least
`c * n * log₂(n / max R 1)` expected cell probes on `insertQueryDeleteDist` (at the `R = n`
boundary `log₂(n / max R 1) = 0`; see `det_expectedSeqProbes_ge_iterLogStar_add_log_div` for the
combined bound across `R ≤ c_R * n`). -/
theorem det_expectedSeqProbes_ge_of_sublinear_redundancy {α c_w : ℝ}
    (hα : 0 < α) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1) ≤
          ∑' ops, (insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨γ, hγ, hγ1, hγ_eq⟩ := exists_gamma_query hα hcw
  obtain ⟨c, hc, hmode⟩ := det_expectedSeqProbes_mode_ge_sublinear true hγ hγ1
  exact ⟨c, hc, fun {_U _V n _cells _w _R} hn hU hU_poly hV hR_hi hw hspace {_D_det} hcorr =>
    hmode hn (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV hR_hi hspace
      (by
        have h4n : n + 3 * n = 4 * n := by omega
        simpa only [modeHorizon, modeStride, ↓reduceIte, h4n] using hcorr)
      (outer_lemma_both_val_regimes hα hcw hγ hγ_eq hn hU hU_poly hV hw hcorr)⟩

/-- Zero-error randomized **Theorem 1.2 / Theorem 6.1** ([LiLiangYuZhou2023], Section 1, p. 2 /
PDF p. 3 and Section 6, pp. 25–26 / PDF pp. 26–27): any zero-error (Las Vegas)
`CellProbe.Randomized.Scheme` on oblivious `insertQueryDeleteDist` storing `n` keys in `[U]`
(`U ≥ n ^ (1 + α)`) with `R ≤ n` bits of redundancy incurs at least `c * n * log₂(n / max R 1)`
expected cell probes (vanishing at `R = n`). -/
theorem expectedSeqProbes_ge_of_sublinear_redundancy {α c_w : ℝ}
    (hα : 0 < α) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1)) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_ge_of_sublinear_redundancy hα hcw
  exact ⟨c, hc, fun hn hU hU_poly hV hR_hi hw hspace P hcorr =>
    le_expectedSeqProbes_query_of_det _ hV P hcorr (hdet hn hU hU_poly hV hR_hi hw hspace)⟩

/-- Combined deterministic **Theorems 1.1 & 1.2** (`Ω(n * (log* n + log₂(n / max R 1)))`) across
all `R ≤ c_R * n` ([LiLiangYuZhou2023], Section 1, pp. 1–2 / PDF pp. 2–3). -/
theorem det_expectedSeqProbes_ge_iterLogStar_add_log_div {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1))) ≤
          ∑' ops, (insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨c₁, hc₁, hdet₁⟩ := det_expectedSeqProbes_ge_iterLogStar hα hcR hcw
  obtain ⟨c₂, hc₂, hdet₂⟩ := det_expectedSeqProbes_ge_of_sublinear_redundancy hα hcw
  exact ⟨min c₁ c₂ / 2, by positivity, fun hn hU hU_poly hV hR_hi hw hspace _ hcorr =>
    combine_iterLogStar_and_sublinear hn (Nat.cast_nonneg _)
      (tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
      (hdet₁ hn hU hU_poly hV hw (hspace.trans (by linarith)) hcorr)
      fun hRn => hdet₂ hn hU hU_poly hV hRn hw hspace hcorr⟩

/-- Combined zero-error randomized **Theorems 1.1 & 1.2**
(`Ω(n * (log* n + log₂(n / max R 1)))`) across all `R ≤ c_R * n` in the Las Vegas oblivious model
([LiLiangYuZhou2023], Section 1, pp. 1–2 / PDF pp. 2–3). -/
theorem expectedSeqProbes_ge_iterLogStar_add_log_div {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) *
          ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1)))) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_ge_iterLogStar_add_log_div hα hcR hcw
  exact ⟨c, hc, fun hn hU hU_poly hV hR_hi hw hspace P hcorr =>
    le_expectedSeqProbes_query_of_det _ hV P hcorr (hdet hn hU hU_poly hV hR_hi hw hspace)⟩

end Cslib.DataStructure.Dictionary.CellProbe
