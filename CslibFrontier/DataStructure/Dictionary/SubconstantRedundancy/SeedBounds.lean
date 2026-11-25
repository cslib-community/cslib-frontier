/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.BitBudget
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.Canonical
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Padding Entropy and Regime-Switched Router Seed Bit Bounds

This module proves the sentinel-padding entropy bound `infoBits_paddedUniv_le`, the
`SuccinctBucket` metadata bound `succinctTableMetaBits_le`, and the uniform quadratic seed bound
`routerSeedBits_sq_le_nFloor` across both the `DoubleTabulation` (`nLow ℓ ≥ childRouterThreshold`)
and small-node `trinomialPolyHash` (`nLow ℓ < childRouterThreshold`) child-router regimes of
[LiLiangYuZhou2024] (`arXiv:2310.20536v1`, Sections 5.1–5.2 and 5.4, PDF pp. 25–30 and 32–33 /
printed pp. 24–29 and 31–32).

## Main results

* `infoBits_paddedUniv_le`: sentinel and alignment padding from `U` to `paddedUniv` increases
  `infoBits` by at most `2 * effRedundancy n R + 1` bits.
* `succinctTableMetaBits_le`: linear-in-`(m * I)` upper bound on `SuccinctBucket` metadata bits.
* `TreeSchedule.idCompressorSeedBits_le_of_two_le`, `TreeSchedule.waitingListBits_le_of_two_le`:
  general `TreeSchedule` bit-width bounds on non-root ID-compressor seeds and waiting lists.
* `routerSeedBits_sq_le_nFloor`: `(routerSeedBits ℓ) ^ 2 ≤ nFloor ℓ` at every level `0 ≤ ℓ < depth`
  across both child-router regimes.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

/-! ## Section 1: Inverse-redundancy scaling and sentinel-padding entropy bound -/

/-- The key count `n` is bounded by `2 * R_eff * r`. -/
theorem n_le_two_mul_effRedundancy_mul_ratio {n R : ℕ}
    (hR : 1 ≤ R) (hr1 : 1 ≤ redundancyRatio n R) :
    n ≤ 2 * effRedundancy n R * redundancyRatio n R := by
  set Re := effRedundancy n R
  set r := redundancyRatio n R
  have hRe1 : 1 ≤ Re := effRedundancy_pos hR n
  have hr_eq : r = n / Re := by
    dsimp only [r, redundancyRatio]
    rw [max_eq_left hRe1]
  have hdiv := Nat.div_add_mod n Re
  have hmod := Nat.mod_lt n hRe1
  rw [← hr_eq] at hdiv
  nlinarith

/-- Inverse-redundancy transfer bound: `Q * r ≤ C * n` implies `Q ≤ 2 * C * R_eff`. -/
theorem le_two_mul_effRedundancy_of_mul_ratio_le {n R Q C : ℕ}
    (hR : 1 ≤ R) (hr1 : 1 ≤ redundancyRatio n R)
    (hQ : Q * redundancyRatio n R ≤ C * n) :
    Q ≤ 2 * C * effRedundancy n R := by
  have hn := n_le_two_mul_effRedundancy_mul_ratio hR hr1
  have hmul : Q * redundancyRatio n R ≤ (2 * C * effRedundancy n R) * redundancyRatio n R := by
    calc Q * redundancyRatio n R ≤ C * n := hQ
      _ ≤ C * (2 * effRedundancy n R * redundancyRatio n R) := Nat.mul_le_mul_left C hn
      _ = (2 * C * effRedundancy n R) * redundancyRatio n R := by ring
  exact Nat.le_of_mul_le_mul_right hmul hr1

private theorem choose_add_le_choose_mul_pow_two {U E n Re : ℕ}
    (hnU : 2 * n ≤ U) (hnE : n * E ≤ (U + 1 - n) * Re) :
    (U + E).choose n ≤ U.choose n * 2 ^ (2 * Re) := by
  set W := U + 1 - n
  have hW : (0 : ℝ) < W := by dsimp only [W]; exact_mod_cast (by omega : 0 < U + 1 - n)
  have hch := Nat.pow_mul_choose_le_choose_mul_pow (d := U) (m := U + E) (s := n)
    (Nat.le_add_right U E)
  rw [show U + E + 1 - n = W + E by omega] at hch
  -- `(1 + E / W) ^ n ≤ exp (n * E / W) ≤ exp Re ≤ 4 ^ Re`.
  have hexp : (1 + (E : ℝ) / W) ^ n ≤ 2 ^ (2 * Re) := by
    have hnδ : (n : ℝ) * (E / W) ≤ Re := by
      rw [mul_div_assoc', div_le_iff₀ hW, mul_comm (Re : ℝ)]; exact_mod_cast hnE
    calc (1 + (E : ℝ) / W) ^ n ≤ Real.exp (E / W) ^ n := by
          gcongr; linarith [Real.add_one_le_exp ((E : ℝ) / W)]
      _ ≤ Real.exp 1 ^ Re := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_one]; exact Real.exp_le_exp.mpr hnδ
      _ ≤ 2 ^ (2 * Re) := by
          rw [pow_mul]; gcongr; linarith [Real.exp_one_lt_d9]
  have hWE : ((W + E : ℕ) : ℝ) = W * (1 + E / W) := by push_cast; field_simp
  have key : (W : ℝ) ^ n * (U + E).choose n ≤ (W : ℝ) ^ n * (U.choose n * 2 ^ (2 * Re)) :=
    calc (W : ℝ) ^ n * (U + E).choose n ≤ U.choose n * ((W + E : ℕ) : ℝ) ^ n := by
          exact_mod_cast hch
      _ = (W : ℝ) ^ n * (U.choose n * (1 + E / W) ^ n) := by rw [hWE, mul_pow]; ring
      _ ≤ _ := by gcongr
  exact_mod_cast le_of_mul_le_mul_left key (by positivity)

/-- `2 ^ idBits ≤ 256 * nFloor ^ 4` at a level with positive floor load. -/
private theorem two_pow_idBits_le {n U r k ℓ : ℕ} (hy : 1 ≤ nFloor n U r k ℓ) :
    2 ^ idBits n U r k ℓ ≤ 256 * nFloor n U r k ℓ ^ 4 := by
  rw [idBits, max_eq_left hy, Nat.mul_comm, Nat.pow_mul]
  calc (2 ^ Nat.clog 2 (2 * nFloor n U r k ℓ)) ^ 4 ≤ (2 * (2 * nFloor n U r k ℓ)) ^ 4 :=
        Nat.pow_le_pow_left (Nat.pow_clog_le_mul Nat.one_lt_two (by omega)) 4
    _ = 256 * nFloor n U r k ℓ ^ 4 := by ring

/-- Upper bound on the padded universe size:
`paddedUniv ≤ U + n + 4096 * n * (log₂ U) ^ 27`. -/
private theorem paddedUniv_le_add_mul_log_pow {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).paddedUniv ≤ U + n + 4096 * n * (Nat.log 2 U) ^ 27 := by
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  set P := canonicalSchedule h
  set r := redundancyRatio n R
  set k := treeDepth U r
  have h1_lt : 1 ≤ k := by have := two_le_treeDepth U r; omega
  obtain ⟨hNT1, _⟩ := numNodes_mul_targetSize_bounds (hT_pos 1 h1_lt) (hT_le 1 h1_lt)
  obtain ⟨hlo1, hhi1⟩ := targetSize_le_nFloor_and_lt (hT_pos 1 h1_lt) (hT_le 1 h1_lt)
  set s1 := Nat.log 2 U
  have hT1_eq : targetSize n U r k 1 = s1 ^ 9 := by
    rw [targetSize_eq_levelScale_pow le_rfl]
    dsimp only [levelScale]
    rw [ite_eq_left (by have := two_le_treeDepth U r; omega)]
    rfl
  have hid1_pow : 2 ^ idBits n U r k 1 ≤ 4096 * s1 ^ 36 :=
    calc 2 ^ idBits n U r k 1 ≤ 256 * nFloor n U r k 1 ^ 4 :=
          two_pow_idBits_le ((hT_pos 1 h1_lt).trans hlo1)
      _ ≤ 256 * (2 * s1 ^ 9) ^ 4 := by gcongr; omega
      _ = 4096 * s1 ^ 36 := by ring
  set step := branchFactor n U r k 0 * 2 ^ idBits n U r k 1
  have hstep_le : step ≤ 4096 * n * s1 ^ 27 := by
    have hB0 : branchFactor n U r k 0 = numNodes n U r k 1 := by
      simp [branchFactor, branchBits, numNodes, cumBranchBits]
    calc step = numNodes n U r k 1 * 2 ^ idBits n U r k 1 := by dsimp only [step]; rw [hB0]
      _ ≤ numNodes n U r k 1 * (4096 * s1 ^ 36) := Nat.mul_le_mul_left _ hid1_pow
      _ = (numNodes n U r k 1 * s1 ^ 9) * (4096 * s1 ^ 27) := by ring
      _ ≤ n * (4096 * s1 ^ 27) := Nat.mul_le_mul_right _ (hT1_eq ▸ hNT1)
      _ = 4096 * n * s1 ^ 27 := by ring
  have hUpad_le : P.paddedUniv ≤ U + n + step := by
    dsimp only [P, TreeSchedule.paddedUniv]
    rw [canonicalSchedule_branchFactor_eq, canonicalSchedule_idBits_eq, canonicalSchedule_quotOne]
    dsimp only [quotUnivOne]
    have hmul : ((U + n + step - 1) / step) * step ≤ U + n + step - 1 :=
      Nat.div_mul_le_self _ step
    rw [Nat.mul_comm] at hmul
    change step * ((U + n + step - 1) / step) ≤ U + n + step
    have := h.two_le_n
    omega
  omega

/-- Sentinel and top-level alignment padding from `U` to `(canonicalSchedule h).paddedUniv`
increases `infoBits` by at most `2 * effRedundancy n R + 1` bits across `ValidRegime`. -/
theorem infoBits_paddedUniv_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    infoBits (canonicalSchedule h).paddedUniv V n ≤
      infoBits U V n + 2 * effRedundancy n R + 1 := by
  set P := canonicalSchedule h
  set r := redundancyRatio n R
  set Re := effRedundancy n R
  have hr256 := h.redundancyRatio_bounds.1
  have h4r : 4 * r ≤ Nat.log 2 U := h.four_mul_redundancyRatio_le_log_univ
  set s1 := Nat.log 2 U
  have hs1_ge : 256 ≤ s1 := by dsimp [minRedundancyRatio] at hr256; omega
  have hUpad_le : P.paddedUniv ≤ U + n + 4096 * n * s1 ^ 27 := paddedUniv_le_add_mul_log_pow h
  have hUpad_ge : U ≤ P.paddedUniv :=
    (canonicalSchedule_univ h).ge.trans ((Nat.le_add_right _ _).trans P.univ_le_padded)
  set E := P.paddedUniv - U
  have hUpad_eq : P.paddedUniv = U + E := (Nat.add_sub_of_le hUpad_ge).symm
  have hE_le : E ≤ 4097 * n * s1 ^ 27 := by
    have hs1_pos : 1 ≤ s1 ^ 27 := Nat.one_le_pow 27 s1 (by omega)
    have hn_le : n ≤ n * s1 ^ 27 := Nat.le_mul_of_pos_right n hs1_pos
    nlinarith
  set L := Nat.log 2 n
  have hn_Re : n ≤ 2 * L * Re :=
    (n_le_two_mul_effRedundancy_mul_ratio h.redundancy_pos h.one_le_redundancyRatio).trans
      ((Nat.mul_le_mul_left _ h.redundancyRatio_le_log).trans_eq (by ring))
  have hgap_U : 16388 * n * s1 ^ 27 * L ≤ U := by
    have hp : 16388 * (q_min + p_max + 4) ≤ L :=
      h.mul_param_le_log (by decide : 16388 ≤ 2560000)
    have hprod_L : 16388 * s1 ^ 27 * L ≤ L ^ 56 := by
      calc 16388 * s1 ^ 27 * L ≤ L * (L ^ 2) ^ 27 * L :=
            Nat.mul_le_mul_right L
              (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h.log_univ_le_sq_log 27))
        _ = L ^ 56 := by rw [← Nat.pow_mul]; ring
    set D := 56 * q_min
    have hD_pos : 1 ≤ D := by have := h.q_min_pos; dsimp only [D]; omega
    have h4D2 : 4 * D ^ 2 ≤ L := by
      dsimp only [D]
      have hq4 : q_min ^ 2 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
        (Nat.pow_le_pow_left (by omega : q_min ≤ max q_min 1 + p_max + 4) 2).trans
          (Nat.pow_le_pow_right (by omega) (by decide))
      have hpoly : 2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ L := h.poly_le_log
      have : 4 * (56 * q_min) ^ 2 = 12544 * q_min ^ 2 := by ring
      omega
    have hLD : L ^ D ≤ n :=
      (Nat.pow_le_two_pow hD_pos h4D2).trans
        (Nat.pow_log_le_self 2 (by have := h.two_le_n; omega))
    have hpow_q : (16388 * n * s1 ^ 27 * L) ^ q_min ≤ U ^ q_min := by
      calc (16388 * n * s1 ^ 27 * L) ^ q_min
          = n ^ q_min * (16388 * s1 ^ 27 * L) ^ q_min := by ring
        _ ≤ n ^ q_min * (L ^ 56) ^ q_min :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprod_L q_min)
        _ = n ^ q_min * L ^ D := by rw [← Nat.pow_mul]
        _ ≤ n ^ q_min * n := Nat.mul_le_mul_left _ hLD
        _ = n ^ (q_min + 1) := (pow_succ n q_min).symm
        _ ≤ U ^ q_min := h.n_pow_succ_le_univ_pow
    exact (Nat.pow_le_pow_iff_left (by have := h.q_min_pos; omega)).mp hpow_q
  have hnE : n * E ≤ (U + 1 - n) * Re :=
    calc n * E ≤ (2 * L * Re) * (4097 * n * s1 ^ 27) := Nat.mul_le_mul hn_Re hE_le
      _ = (8194 * n * s1 ^ 27 * L) * Re := by ring
      _ ≤ (U + 1 - n) * Re := Nat.mul_le_mul_right Re (by
          have := h.two_mul_n_le_univ
          have : 8194 * n * s1 ^ 27 * L * 2 = 16388 * n * s1 ^ 27 * L := by ring
          omega)
  have hch := choose_add_le_choose_mul_pow_two h.two_mul_n_le_univ hnE
  rw [← hUpad_eq] at hch
  refine Nat.clog_le_of_le_pow ?_
  calc P.paddedUniv.choose n * V ^ n
      ≤ (U.choose n * 2 ^ (2 * Re)) * V ^ n := Nat.mul_le_mul_right _ hch
    _ = (U.choose n * V ^ n) * 2 ^ (2 * Re) := by ring
    _ ≤ (2 ^ infoBits U V n) * 2 ^ (2 * Re) :=
        Nat.mul_le_mul_right _ (Nat.le_pow_clog Nat.one_lt_two _)
    _ ≤ 2 ^ (infoBits U V n + 2 * Re + 1) := by
        rw [← Nat.pow_add]
        exact Nat.pow_le_pow_right Nat.two_pos (by omega)

/-! ## Section 2: `SuccinctBucket` metadata and regime-switched `routerSeedBits` bounds -/

theorem succinctTableMetaBits_le {I m : ℕ} (hm : m ≤ 2 ^ I) :
    succinctTableMetaBits I m ≤ 75 * m * (I + 2) + 9 * (I + 2) := by
  have hq : FeistelQuotient.quotientBits (2 ^ I) m ≤ I := by
    calc FeistelQuotient.quotientBits (2 ^ I) m
        ≤ FeistelQuotient.keyBits (2 ^ I) := by
          have := FeistelQuotient.quotientBits_add_bucketBits hm
          omega
      _ = I := by simp [FeistelQuotient.keyBits]
  have hll : Dynamic.logLogFactor m ≤ I + 2 := by
    dsimp only [Dynamic.logLogFactor]
    have hm4 : max m 4 ≤ 2 ^ (I + 2) := by
      refine max_le (hm.trans (Nat.pow_le_pow_right Nat.two_pos (by omega))) ?_
      exact (show 4 = 2 ^ 2 by decide) ▸ Nat.pow_le_pow_right Nat.two_pos (by omega)
    have hcl1 : Nat.clog 2 (max m 4) ≤ I + 2 := Nat.clog_le_of_le_pow hm4
    exact (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans hcl1
  have hloc := (SuccinctBucket.localMetaLen_mul_effBucketPosBits_le m).trans
    (Nat.mul_le_mul_left (54 * m) hll)
  have hglob := (SuccinctBucket.globalMetaLen_mul_globalPtrBits_le m).trans
    (Nat.mul_le_mul_left (20 * m) hll)
  have htri : 3 * Cslib.Probability.trinomialDeg
      (2 ^ FeistelQuotient.quotientBits (2 ^ I) m) (SuccinctBucket.totalMicroBits m) ≤
      9 * (I + 2) := by
    have htd := Cslib.Probability.trinomialDeg_le_three_mul
      (2 ^ FeistelQuotient.quotientBits (2 ^ I) m) (SuccinctBucket.totalMicroBits m)
    have h1 : Nat.clog 2 (max (2 ^ FeistelQuotient.quotientBits (2 ^ I) m) 2) ≤ I + 2 := by
      refine Nat.clog_le_of_le_pow (max_le ?_ ?_)
      · exact Nat.pow_le_pow_right Nat.two_pos (by omega)
      · exact Nat.le_self_pow (by omega) 2
    have h2 : max (SuccinctBucket.totalMicroBits m) 1 ≤ I + 2 := by
      have htmb : SuccinctBucket.totalMicroBits m ≤ I :=
        SuccinctBucket.totalMicroBits_le_of_le_pow hm le_rfl
      omega
    have hmax : max (Nat.clog 2 (max (2 ^ FeistelQuotient.quotientBits (2 ^ I) m) 2))
        (max (SuccinctBucket.totalMicroBits m) 1) ≤ I + 2 := max_le h1 h2
    omega
  have hmq : m * FeistelQuotient.quotientBits (2 ^ I) m ≤ m * (I + 2) := by gcongr; omega
  dsimp only [succinctTableMetaBits]
  nlinarith

theorem TreeSchedule.idCompressorSeedBits_le_of_two_le (P : TreeSchedule) {ℓ : ℕ}
    (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) :
    FeistelPerm.idCompressorSeedBits (P.idBits ℓ) (P.idCompRightUniv ℓ) ≤
      6 * max (P.idBits (ℓ - 1)) 1 := by
  have hstep := P.idBits_step_le (ℓ - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at hstep
  have hcl_rem : Nat.clog 2 (max (P.idCompRightUniv ℓ) 2) ≤ max (P.idBits (ℓ - 1)) 1 := by
    dsimp only [TreeSchedule.idCompRightUniv]
    rw [ite_eq_right (by omega)]
    refine Nat.clog_le_of_le_pow (max_le ?_ ?_)
    · refine Nat.pow_le_pow_right Nat.two_pos ?_
      dsimp only [TreeSchedule.remBits]
      omega
    · exact Nat.le_self_pow (by omega) 2
  have hid_le : max (P.idBits ℓ) 1 ≤ max (P.idBits (ℓ - 1)) 1 :=
    max_le (by omega) (le_max_right _ _)
  exact (FeistelPerm.idCompressorSeedBits_le (P.idBits ℓ) (P.idCompRightUniv ℓ)).trans
    (Nat.mul_le_mul_left 6 (max_le hcl_rem hid_le))

theorem TreeSchedule.waitingListBits_le_of_two_le (P : TreeSchedule) {ℓ : ℕ}
    (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) :
    waitingListBits (P.waitCap ℓ) (P.idBits ℓ) (P.idBits (ℓ - 1)) ≤
      (4 * P.delta ℓ + 1) * P.idBits (ℓ - 1) := by
  have hd_lt := P.delta_lt_nFloor ℓ (by omega) hℓ
  have hnh_id := P.nHigh_le_two_pow_idBits ℓ (by omega) hℓ
  have hstep := P.idBits_step_le (ℓ - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at hstep
  have hcl_w : Nat.clog 2 (2 * P.delta ℓ + 1) ≤ P.idBits ℓ :=
    Nat.clog_le_of_le_pow (by omega)
  dsimp only [waitingListBits, TreeSchedule.waitCap]
  have hmul : 2 * P.delta ℓ * (P.idBits ℓ + P.idBits (ℓ - 1)) ≤
      4 * P.delta ℓ * P.idBits (ℓ - 1) := by
    calc 2 * P.delta ℓ * (P.idBits ℓ + P.idBits (ℓ - 1))
        ≤ 2 * P.delta ℓ * (P.idBits (ℓ - 1) + P.idBits (ℓ - 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 4 * P.delta ℓ * P.idBits (ℓ - 1) := by ring
  nlinarith

private theorem mul_spaceConst_le_threshold (ε_inv α_inv : ℕ) :
    256 * FeistelPerm.childRouterSpaceConst ε_inv α_inv ≤
      FeistelPerm.childRouterThreshold ε_inv α_inv := by
  rw [FeistelPerm.childRouterSpaceConst_eq, FeistelPerm.childRouterThreshold_eq]
  set E := max ε_inv 1
  set c := FeistelPerm.childRouterChars ε_inv
  set A := c * max α_inv 1
  set q := FeistelPerm.childRouterRep ε_inv α_inv
  set d := 2 * q * c
  have hE1 : 1 ≤ E := le_max_right _ _
  have hc_eq : c = 2 * E := FeistelPerm.childRouterChars_eq ε_inv
  have hc2 : 2 ≤ c := by omega
  have hA2 : 2 ≤ A := le_mul_of_le_of_one_le hc2 (le_max_right α_inv 1)
  have hq_eq : q = A + 2 := FeistelPerm.childRouterRep_eq ε_inv α_inv
  have hd_ge : 16 ≤ d := by dsimp only [d]; nlinarith
  have hd_pow : d ^ E ≤ 2 ^ (d * E) := by
    calc d ^ E ≤ (2 ^ d) ^ E := Nat.pow_le_pow_left Nat.lt_two_pow_self.le E
      _ = 2 ^ (d * E) := (Nat.pow_mul 2 d E).symm
  have hexp_le : 8 + d * E + (2 * c ^ 2 + c + 2) ≤
      A * max (4 * c * d ^ q * (c * (6 * A + 8)) ^ (2 * c * q)) (4 * (2 * c * q + 1) ^ 2) := by
    have hD_eq : 2 * c * q = d := by dsimp only [d]; ring
    rw [hD_eq]
    have h1 : 8 + d * E + (2 * c ^ 2 + c + 2) ≤ 4 * (d + 1) ^ 2 := by
      have hEc : E ≤ c := by omega
      have hcd : c ≤ d := by dsimp only [d]; nlinarith
      nlinarith
    calc 8 + d * E + (2 * c ^ 2 + c + 2)
        ≤ 4 * (d + 1) ^ 2 := h1
      _ ≤ max (4 * c * d ^ q * (c * (6 * A + 8)) ^ d) (4 * (d + 1) ^ 2) := le_max_right _ _
      _ ≤ A * max (4 * c * d ^ q * (c * (6 * A + 8)) ^ d) (4 * (d + 1) ^ 2) :=
          Nat.le_mul_of_pos_left _ (by omega)
  calc 256 * (d ^ E * 2 ^ (2 * c ^ 2 + c + 2))
      ≤ 2 ^ 8 * (2 ^ (d * E) * 2 ^ (2 * c ^ 2 + c + 2)) := by
        have h256 : (256 : ℕ) = 2 ^ 8 := by decide
        rw [h256]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hd_pow)
    _ = 2 ^ (8 + d * E + (2 * c ^ 2 + c + 2)) := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right Nat.two_pos hexp_le

private theorem paddedUniv_le_two_mul_pow {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).paddedUniv ≤ 2 * n ^ (p_max + 2) := by
  set P := canonicalSchedule h
  have h4r : 4 * redundancyRatio n R ≤ Nat.log 2 U := h.four_mul_redundancyRatio_le_log_univ
  have hr1 := h.one_le_redundancyRatio
  set s1 := Nat.log 2 U
  have hUpad_le : P.paddedUniv ≤ U + n + 4096 * n * s1 ^ 27 := paddedUniv_le_add_mul_log_pow h
  set L := Nat.log 2 n
  have hp : 4097 * (q_min + p_max + 4) ≤ L :=
    h.mul_param_le_log (by decide : 4097 ≤ 2560000)
  have h4097 : 4097 * s1 ^ 27 ≤ L ^ 55 := by
    calc 4097 * s1 ^ 27 ≤ L * (L ^ 2) ^ 27 :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h.log_univ_le_sq_log 27)
      _ = L ^ 55 := by rw [← Nat.pow_mul]; ring
  have hL55 : L ^ 55 ≤ n :=
    (Nat.pow_le_two_pow (by decide) (by omega)).trans
      (Nat.pow_log_le_self 2 (by have := h.two_le_n; omega))
  have hs1_pos : 1 ≤ s1 ^ 27 := Nat.one_le_pow 27 s1 (by omega)
  have hstep_n2 : n + 4096 * n * s1 ^ 27 ≤ n ^ (p_max + 2) := by
    calc n + 4096 * n * s1 ^ 27 ≤ n * s1 ^ 27 + 4096 * n * s1 ^ 27 :=
          Nat.add_le_add_right (Nat.le_mul_of_pos_right n hs1_pos) _
      _ = n * (4097 * s1 ^ 27) := by ring
      _ ≤ n * L ^ 55 := Nat.mul_le_mul_left n h4097
      _ ≤ n * n := Nat.mul_le_mul_left n hL55
      _ = n ^ 2 := (sq n).symm
      _ ≤ n ^ (p_max + 2) := Nat.pow_le_pow_right (by have := h.two_le_n; omega) (by omega)
  have hU_pow : U ≤ n ^ (p_max + 2) :=
    h.univ_le_pow.trans (Nat.pow_le_pow_right (by have := h.two_le_n; omega) (by omega))
  calc P.paddedUniv ≤ U + (n + 4096 * n * s1 ^ 27) := by omega
    _ ≤ n ^ (p_max + 2) + n ^ (p_max + 2) := Nat.add_le_add hU_pow hstep_n2
    _ = 2 * n ^ (p_max + 2) := (two_mul _).symm

/-- Coarse power-of-two upper bound on the padded universe:
`paddedUniv ≤ 2 ^ (2 * (p_max + 2) * log₂ n)`. -/
theorem paddedUniv_le_two_pow_mul_log {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).paddedUniv ≤ 2 ^ (2 * (p_max + 2) * Nat.log 2 n) := by
  set L := Nat.log 2 n
  have hL4 : 4 ≤ L := h.four_le_log
  have hn_2L : n ≤ 2 ^ (L + 1) := (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
  have hexp : (L + 1) * (p_max + 2) + 1 ≤ 2 * (p_max + 2) * L := by
    nlinarith [Nat.mul_le_mul_left (p_max + 2) hL4]
  calc (canonicalSchedule h).paddedUniv
      ≤ 2 * n ^ (p_max + 2) := paddedUniv_le_two_mul_pow h
    _ ≤ 2 * (2 ^ (L + 1)) ^ (p_max + 2) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn_2L _)
    _ = 2 ^ ((L + 1) * (p_max + 2) + 1) := by rw [← Nat.pow_mul, ← pow_succ']
    _ ≤ 2 ^ (2 * (p_max + 2) * L) := Nat.pow_le_pow_right Nat.two_pos hexp

/-- At every tree level `j ≤ depth`, floor load satisfies `nFloor j ≥ 256 ^ 9`. -/
theorem nFloor_ge_pow_256 {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {j : ℕ}
    (hj : j ≤ (canonicalSchedule h).depth) :
    256 ^ 9 ≤ (canonicalSchedule h).nFloor j := by
  rw [canonicalSchedule_depth] at hj
  rw [canonicalSchedule_nFloor_eq]
  exact canonical_nFloor_ge_pow_256 h hj

private theorem routerSeedBits_sq_le_of_ge_threshold {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hlt : ℓ < (canonicalSchedule h).depth)
    (hth : FeistelPerm.childRouterThreshold (canonicalSchedule h).epsInv
      (canonicalSchedule h).alphaInv ≤ (canonicalSchedule h).nLow ℓ) :
    let P := canonicalSchedule h
    (FeistelPerm.childRouterSeedBits (FeistelPerm.childRouterChars P.epsInv)
      (FeistelPerm.childRouterRep P.epsInv P.alphaInv)
      (FeistelPerm.childRouterCharBits (FeistelPerm.childRouterChars P.epsInv)
        (P.routerRightUniv ℓ))
      (P.branchBits ℓ)) ^ 2 ≤ P.nFloor ℓ := by
  intro P
  set B_seed := FeistelPerm.childRouterSeedBits (FeistelPerm.childRouterChars P.epsInv)
    (FeistelPerm.childRouterRep P.epsInv P.alphaInv)
    (FeistelPerm.childRouterCharBits (FeistelPerm.childRouterChars P.epsInv)
      (P.routerRightUniv ℓ))
    (P.branchBits ℓ)
  have hT_r_pos : 1 ≤ P.routerRightUniv ℓ := by
    dsimp only [TreeSchedule.routerRightUniv]
    split_ifs
    · exact Nat.mul_pos (Nat.two_pow_pos _) P.quotOne_pos
    · exact Nat.two_pow_pos _
  have hpow := FeistelPerm.childRouterSeedBits_pow_le P.epsInv P.alphaInv (P.branchBits ℓ) hT_r_pos
  have h256C : 256 * FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv ≤ P.nFloor ℓ := by
    have hc := mul_spaceConst_le_threshold P.epsInv P.alphaInv
    have hnl_nf : P.nLow ℓ ≤ P.nFloor ℓ := by
      dsimp only [TreeSchedule.nLow]
      split_ifs with h0
      · subst h0; rw [P.nFloor_zero]; omega
      · exact Nat.sub_le _ _
    exact (hc.trans hth).trans hnl_nf
  by_cases hB0_one : B_seed = 0
  · rw [hB0_one]; simp
  have hB_pos : 1 ≤ B_seed := Nat.pos_of_ne_zero hB0_one
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · have hE_ge : 2 * (p_max + 3) ≤ max P.epsInv 1 := by
      dsimp only [P]
      rw [canonicalSchedule_epsInv, routerEpsInv_eq]
      exact (le_max_right 12 _).trans (le_max_left _ 1)
    have hdom_eq : 2 ^ P.branchBits 0 * P.routerRightUniv 0 = P.paddedUniv := by
      dsimp only [TreeSchedule.routerRightUniv, TreeSchedule.paddedUniv,
        TreeSchedule.branchFactor]
      rw [ite_eq_left rfl, ← Nat.mul_assoc]
    have hUpad_le2 := paddedUniv_le_two_mul_pow h
    have hnf0 : P.nFloor 0 = n := by rw [P.nFloor_zero]; exact canonicalSchedule_cap h
    rw [hnf0] at h256C ⊢
    have hpow0 : (B_seed ^ 2) ^ (p_max + 3) ≤ n ^ (p_max + 3) := by
      calc (B_seed ^ 2) ^ (p_max + 3)
          = B_seed ^ (2 * (p_max + 3)) := (Nat.pow_mul B_seed 2 _).symm
        _ ≤ B_seed ^ max P.epsInv 1 := Nat.pow_le_pow_right hB_pos hE_ge
        _ ≤ FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv * P.paddedUniv := by
            rwa [hdom_eq] at hpow
        _ ≤ FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv * (2 * n ^ (p_max + 2)) :=
            Nat.mul_le_mul_left _ hUpad_le2
        _ = (2 * FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv) * n ^ (p_max + 2) := by
            ring
        _ ≤ n * n ^ (p_max + 2) := Nat.mul_le_mul_right _ (by omega)
        _ = n ^ (p_max + 3) := (pow_succ' n _).symm
    exact (Nat.pow_le_pow_iff_left (by omega : p_max + 3 ≠ 0)).mp hpow0
  · have hE_ge12 : 12 ≤ max P.epsInv 1 := by
      dsimp only [P]
      rw [canonicalSchedule_epsInv, routerEpsInv_eq]
      exact (le_max_left 12 _).trans (le_max_left _ 1)
    set y := P.nFloor ℓ
    have hy1 : 1 ≤ y := (Nat.one_le_pow 9 256 (by decide)).trans (nFloor_ge_pow_256 h hlt.le)
    have hdom_ℓ : 2 ^ P.branchBits ℓ * P.routerRightUniv ℓ = 2 ^ P.idBits ℓ := by
      dsimp only [TreeSchedule.routerRightUniv]
      rw [ite_eq_right hpos.ne', ← Nat.pow_add]
      have hstep_id := P.idBits_step_le ℓ hpos hlt
      congr 1; omega
    have hid_pow : 2 ^ P.idBits ℓ ≤ 256 * y ^ 4 := by
      have := two_pow_idBits_le (hy1.trans_eq (canonicalSchedule_nFloor_eq h ℓ))
      rwa [← canonicalSchedule_idBits_eq h, ← canonicalSchedule_nFloor_eq h] at this
    have hpow6 : (B_seed ^ 2) ^ 6 ≤ y ^ 6 := by
      calc (B_seed ^ 2) ^ 6 = B_seed ^ 12 := (Nat.pow_mul B_seed 2 6).symm
        _ ≤ B_seed ^ max P.epsInv 1 := Nat.pow_le_pow_right hB_pos hE_ge12
        _ ≤ FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv * 2 ^ P.idBits ℓ := by
            rwa [hdom_ℓ] at hpow
        _ ≤ FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv * (256 * y ^ 4) := by gcongr
        _ = (256 * FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv) * y ^ 4 := by ring
        _ ≤ y * y ^ 4 := Nat.mul_le_mul_right _ h256C
        _ = y ^ 5 := (pow_succ' y 4).symm
        _ ≤ y ^ 6 := Nat.pow_le_pow_right hy1 (by decide)
    exact (Nat.pow_le_pow_iff_left (by decide : 6 ≠ 0)).mp hpow6

private theorem routerSeedBits_sq_le_of_lt_threshold {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hlt : ℓ < (canonicalSchedule h).depth) :
    let P := canonicalSchedule h
    (2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) *
      Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ)) ^ 2 ≤ P.nFloor ℓ := by
  intro P
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · set L := Nat.log 2 n
    have hp : 48 * (q_min + p_max + 4) ≤ L := h.mul_param_le_log (by decide : 48 ≤ 2560000)
    have hm_le : FeistelPerm.childRouterHalfInd (P.nHigh 0) ≤ 4 * L := by
      have : FeistelPerm.childRouterHalfInd (P.nHigh 0) ≤ 3 * L + 7 :=
        canonicalSchedule_childRouterHalfInd_nHigh_zero_le h
      omega
    have htd0 : Cslib.Probability.trinomialDeg (P.routerRightUniv 0) (P.branchBits 0) ≤
        3 * (2 * (p_max + 2) * L) := by
      have hT0_le : P.routerRightUniv 0 ≤ P.paddedUniv := by
        dsimp only [TreeSchedule.routerRightUniv, TreeSchedule.paddedUniv,
          TreeSchedule.branchFactor]
        rw [ite_eq_left rfl, Nat.mul_assoc]
        exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      have hb0 : P.branchBits 0 ≤ L := by
        dsimp only [P]
        simp only [canonicalSchedule_branchBits, branchBits, cumBranchBits,
          Nat.succ_ne_zero, ↓reduceIte, Nat.sub_zero]
        exact Nat.log_mono_right (Nat.div_le_self n _)
      have hL : L ≤ 2 * (p_max + 2) * L := Nat.le_mul_of_pos_left _ (by omega)
      have hcl : Nat.clog 2 (max (P.routerRightUniv 0) 2) ≤ 2 * (p_max + 2) * L :=
        Nat.clog_le_of_le_pow (max_le (hT0_le.trans (paddedUniv_le_two_pow_mul_log h))
          (Nat.le_self_pow (by omega) 2))
      exact (Cslib.Probability.trinomialDeg_le_three_mul _ _).trans
        (Nat.mul_le_mul_left 3 (max_le hcl (max_le (hb0.trans hL) (by omega))))
    have hprod_L3 : 2 * FeistelPerm.childRouterHalfInd (P.nHigh 0) *
        Cslib.Probability.trinomialDeg (P.routerRightUniv 0) (P.branchBits 0) ≤ L ^ 3 :=
      calc _ ≤ 2 * (4 * L) * (3 * (2 * (p_max + 2) * L)) := by gcongr
        _ = (48 * (p_max + 2)) * L ^ 2 := by ring
        _ ≤ L * L ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ = L ^ 3 := by ring
    rw [P.nFloor_zero, show P.cap = n from canonicalSchedule_cap h]
    calc _ ≤ (L ^ 3) ^ 2 := Nat.pow_le_pow_left hprod_L3 2
      _ = L ^ 6 := by ring
      _ ≤ 2 ^ L := Nat.pow_le_two_pow (by decide) (by omega)
      _ ≤ n := Nat.pow_log_le_self 2 (by have := h.two_le_n; omega)
  · set y := P.nFloor ℓ
    have hy_ge : 256 ^ 9 ≤ y := nFloor_ge_pow_256 h hlt.le
    have hy1 : 1 ≤ y := (Nat.one_le_pow 9 256 (by decide)).trans hy_ge
    set ly := Nat.clog 2 (2 * max y 1) with hly
    rw [max_eq_left hy1] at hly
    have hly_ge : 73 ≤ ly := by
      rw [hly]
      refine (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr ?_
      have : (256 : ℕ) ^ 9 = 2 ^ 72 := by decide
      omega
    have hly_pow : 2 ^ (ly - 1) < 2 * y :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp (by omega)
    have hm_le : FeistelPerm.childRouterHalfInd (P.nHigh ℓ) ≤ 4 * ly := by
      have hhd : 2 * P.delta ℓ ≤ y := canonicalSchedule_two_mul_delta_le_nFloor h hlt.le
      have hnh_eq : P.nHigh ℓ = y + P.delta ℓ := by
        dsimp only [TreeSchedule.nHigh]
        rw [ite_eq_right hpos.ne']
      have hcl : Nat.clog 2 (max (P.nHigh ℓ) 2) ≤ ly :=
        hly ▸ Nat.clog_mono_right 2 (by rw [hnh_eq]; omega)
      rw [FeistelPerm.childRouterHalfInd_eq]
      omega
    have htd_le : Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ) ≤
        12 * ly := by
      have hid_eq : P.idBits ℓ = 4 * ly := by
        dsimp only [P, ly, y]
        rw [canonicalSchedule_idBits_eq, idBits, ← canonicalSchedule_nFloor_eq]
      have hstep_id := P.idBits_step_le ℓ hpos hlt
      have hT_le : max (P.routerRightUniv ℓ) 2 ≤ 2 ^ (4 * ly) := by
        dsimp only [TreeSchedule.routerRightUniv]
        rw [ite_eq_right hpos.ne']
        exact max_le (Nat.pow_le_pow_right Nat.two_pos (by omega)) (Nat.le_self_pow (by omega) 2)
      have := Cslib.Probability.trinomialDeg_le_three_mul (P.routerRightUniv ℓ) (P.branchBits ℓ)
      have := max_le (Nat.clog_le_of_le_pow hT_le) (show max (P.branchBits ℓ) 1 ≤ 4 * ly by omega)
      omega
    -- With `s = (ly - 1) / 8 ≥ 9`:
    -- `2 * (96 * ly ^ 2) ^ 2 ≤ (s ^ 2) ^ 8 ≤ 2 ^ (8 * s) ≤ 2 ^ (ly - 1)`.
    have h2_sq : 2 * (96 * ly ^ 2) ^ 2 ≤ 2 ^ (ly - 1) := by
      set s := (ly - 1) / 8
      have hs : 9 ≤ s := by omega
      calc 2 * (96 * ly ^ 2) ^ 2 ≤ 2 * (96 * (9 * s) ^ 2) ^ 2 := by gcongr; omega
        _ = 120932352 * s ^ 4 := by ring
        _ ≤ s ^ 12 * s ^ 4 := by
            gcongr; exact le_trans (by norm_num) (Nat.pow_le_pow_left hs 12)
        _ = (s ^ 2) ^ 8 := by ring
        _ ≤ (2 ^ s) ^ 8 := Nat.pow_le_pow_left (Nat.sq_le_two_pow (by omega)) 8
        _ ≤ 2 ^ (ly - 1) := by rw [← pow_mul]; exact Nat.pow_le_pow_right Nat.two_pos (by omega)
    have hprod_le : 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) *
        Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ) ≤ 96 * ly ^ 2 :=
      calc _ ≤ 2 * (4 * ly) * (12 * ly) := by gcongr
        _ = 96 * ly ^ 2 := by ring
    have := Nat.pow_le_pow_left hprod_le 2
    omega

/-- Uniform quadratic bound on `routerSeedBits ℓ` across **both** the `DoubleTabulation`
(`nLow ℓ ≥ childRouterThreshold`) and small-node `trinomialPolyHash`
(`nLow ℓ < childRouterThreshold`) regimes: `(routerSeedBits ℓ) ^ 2 ≤ nFloor ℓ` for every
`0 ≤ ℓ < depth`. -/
theorem routerSeedBits_sq_le_nFloor {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hlt : ℓ < (canonicalSchedule h).depth) :
    ((canonicalSchedule h).routerSeedBits ℓ) ^ 2 ≤ (canonicalSchedule h).nFloor ℓ := by
  dsimp only [TreeSchedule.routerSeedBits]
  split_ifs with hth
  · exact routerSeedBits_sq_le_of_ge_threshold h hlt hth
  · exact routerSeedBits_sq_le_of_lt_threshold h hlt

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
