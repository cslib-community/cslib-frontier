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
  have hRe1 : 1 ≤ effRedundancy n R := effRedundancy_pos hR n
  rw [redundancyRatio, max_eq_left hRe1] at hr1 ⊢
  nlinarith [Nat.lt_mul_div_succ n hRe1]

/-- Inverse-redundancy transfer bound: `Q * r ≤ C * n` implies `Q ≤ 2 * C * R_eff`. -/
theorem le_two_mul_effRedundancy_of_mul_ratio_le {n R Q C : ℕ}
    (hR : 1 ≤ R) (hr1 : 1 ≤ redundancyRatio n R)
    (hQ : Q * redundancyRatio n R ≤ C * n) :
    Q ≤ 2 * C * effRedundancy n R := by
  refine Nat.le_of_mul_le_mul_right (hQ.trans ?_) hr1
  exact (Nat.mul_le_mul_left C (n_le_two_mul_effRedundancy_mul_ratio hR hr1)).trans_eq (by ring)

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

/-- The ID universe `2 ^ (4 * ⌈log₂ (2 * y)⌉)` of a level of floor load `y ≥ 1` is at most
`256 * y ^ 4`. -/
private theorem two_pow_four_mul_clog_le {y : ℕ} (hy : 1 ≤ y) :
    2 ^ (4 * Nat.clog 2 (2 * max y 1)) ≤ 256 * y ^ 4 := by
  rw [max_eq_left hy, Nat.mul_comm 4, Nat.pow_mul]
  exact (Nat.pow_le_pow_left (Nat.pow_clog_le_mul Nat.one_lt_two (by omega)) 4).trans_eq (by ring)

/-- Upper bound on the padded universe size: `paddedUniv ≤ U + n * (log₂ n) ^ 55`, from the
level-1 alignment step `B₀ * 2 ^ I₁ ≤ 4096 * n * (log₂ U) ^ 27` and `log₂ U ≤ (log₂ n) ^ 2`. -/
private theorem paddedUniv_le_add_mul_log_pow {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).paddedUniv ≤ U + n * Nat.log 2 n ^ 55 := by
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  set r := redundancyRatio n R
  set k := treeDepth U r
  have hk : 1 < k := two_le_treeDepth U r
  have hT1 := hT_pos 1 hk.le
  obtain ⟨hNT1, -⟩ := numNodes_mul_targetSize_bounds hT1 (hT_le 1 hk.le)
  obtain ⟨hlo1, hhi1⟩ := targetSize_le_nFloor_and_lt hT1 (hT_le 1 hk.le)
  rw [show targetSize n U r k 1 = Nat.log 2 U ^ 9 by
    rw [targetSize_eq_levelScale_pow le_rfl, levelScale, ite_eq_left hk]; rfl] at hT1 hNT1 hlo1 hhi1
  set s1 := Nat.log 2 U
  set step := branchFactor n U r k 0 * 2 ^ idBits n U r k 1 with hstep
  have hstep_le : step ≤ 4096 * (n * s1 ^ 27) :=
    calc step = numNodes n U r k 1 * 2 ^ idBits n U r k 1 := by
          simp [hstep, branchFactor, branchBits, numNodes, cumBranchBits]
      _ ≤ numNodes n U r k 1 * (256 * (2 * s1 ^ 9) ^ 4) := Nat.mul_le_mul_left _
          ((two_pow_four_mul_clog_le (hT1.trans hlo1)).trans (by gcongr))
      _ = 4096 * (numNodes n U r k 1 * s1 ^ 9 * s1 ^ 27) := by ring
      _ ≤ 4096 * (n * s1 ^ 27) := by gcongr
  have hpad : (canonicalSchedule h).paddedUniv ≤ U + n + step := by
    rw [TreeSchedule.paddedUniv, canonicalSchedule_branchFactor_eq, canonicalSchedule_idBits_eq,
      canonicalSchedule_quotOne]
    exact (Nat.mul_div_le (U + n + step - 1) step).trans (by have := h.two_le_n; omega)
  have hL : 4097 ≤ Nat.log 2 n :=
    (h.mul_param_le_log (by decide : 4097 ≤ 2560000)).trans' (by omega)
  have hLU := h.log_univ_bounds.1
  have hs1 : n ≤ n * s1 ^ 27 := Nat.le_mul_of_pos_right n (Nat.pow_pos (by omega))
  calc (canonicalSchedule h).paddedUniv ≤ U + 4097 * (n * s1 ^ 27) := by omega
    _ ≤ U + Nat.log 2 n * (n * (Nat.log 2 n ^ 2) ^ 27) := by
        gcongr; exact h.log_univ_le_sq_log
    _ = U + n * Nat.log 2 n ^ 55 := by ring

/-- Sentinel and top-level alignment padding from `U` to `(canonicalSchedule h).paddedUniv`
increases `infoBits` by at most `2 * effRedundancy n R + 1` bits across `ValidRegime`. -/
theorem infoBits_paddedUniv_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    infoBits (canonicalSchedule h).paddedUniv V n ≤
      infoBits U V n + 2 * effRedundancy n R + 1 := by
  set P := canonicalSchedule h
  set Re := effRedundancy n R
  set L := Nat.log 2 n
  have hn2 := h.two_le_n
  have h2nU := h.two_mul_n_le_univ
  have hL4 : 4 ≤ L := h.four_le_log
  have hUpad_le : P.paddedUniv ≤ U + n * L ^ 55 := paddedUniv_le_add_mul_log_pow h
  obtain ⟨E, hE⟩ : ∃ E, P.paddedUniv = U + E := Nat.exists_eq_add_of_le <| by
    have hp : P.univ + P.cap ≤ P.paddedUniv := P.univ_le_padded
    have hu : P.univ = U := canonicalSchedule_univ h
    omega
  have hn_Re : n ≤ 2 * L * Re :=
    (n_le_two_mul_effRedundancy_mul_ratio h.redundancy_pos h.one_le_redundancyRatio).trans
      ((Nat.mul_le_mul_left _ h.redundancyRatio_le_log).trans_eq (by ring))
  -- the polynomial gap `n ^ (q_min + 1) ≤ U ^ q_min` absorbs the factor `4 * L ^ 56`
  have hgap_U : 4 * n * L ^ 56 ≤ U := by
    have hq := h.q_min_pos
    have h4D2 : 4 * (57 * q_min) ^ 2 ≤ L := by
      have hq4 : q_min ^ 2 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
        (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
      linarith [h.poly_le_log]
    refine (Nat.pow_le_pow_iff_left (by omega : q_min ≠ 0)).mp ?_
    calc (4 * n * L ^ 56) ^ q_min = n ^ q_min * (4 * L ^ 56) ^ q_min := by ring
      _ ≤ n ^ q_min * (L ^ 57) ^ q_min := by
          gcongr; exact (Nat.mul_le_mul_right _ hL4).trans_eq (pow_succ' L 56).symm
      _ = n ^ q_min * L ^ (57 * q_min) := by rw [← pow_mul]
      _ ≤ n ^ q_min * n := Nat.mul_le_mul_left _
          ((Nat.pow_le_two_pow (by omega) h4D2).trans (Nat.pow_log_le_self 2 (by omega)))
      _ = n ^ (q_min + 1) := (pow_succ n q_min).symm
      _ ≤ U ^ q_min := h.n_pow_succ_le_univ_pow
  have hnE : n * E ≤ (U + 1 - n) * Re := by
    refine Nat.le_of_mul_le_mul_left (c := 2) ?_ (by decide)
    calc 2 * (n * E) ≤ 2 * ((2 * L * Re) * (n * L ^ 55)) := by gcongr; omega
      _ = (4 * n * L ^ 56) * Re := by ring
      _ ≤ (2 * (U + 1 - n)) * Re := Nat.mul_le_mul_right Re (hgap_U.trans (by omega))
      _ = 2 * ((U + 1 - n) * Re) := by ring
  have hch := choose_add_le_choose_mul_pow_two h2nU hnE
  rw [← hE] at hch
  refine Nat.clog_le_of_le_pow ?_
  calc P.paddedUniv.choose n * V ^ n
      ≤ (U.choose n * 2 ^ (2 * Re)) * V ^ n := Nat.mul_le_mul_right _ hch
    _ = (U.choose n * V ^ n) * 2 ^ (2 * Re) := by ring
    _ ≤ 2 ^ infoBits U V n * 2 ^ (2 * Re + 1) := Nat.mul_le_mul
        (Nat.le_pow_clog Nat.one_lt_two _) (Nat.pow_le_pow_right Nat.two_pos (by omega))
    _ = 2 ^ (infoBits U V n + 2 * Re + 1) := by rw [← pow_add, add_assoc]

/-! ## Section 2: `SuccinctBucket` metadata and regime-switched `routerSeedBits` bounds -/

/-- `trinomialDeg T s ≤ 3 * M` whenever `T ≤ 2 ^ M` and `s ≤ M` with `1 ≤ M`. -/
private theorem trinomialDeg_le_of_le_two_pow {T s M : ℕ} (hM : 1 ≤ M) (hT : T ≤ 2 ^ M)
    (hs : s ≤ M) : Cslib.Probability.trinomialDeg T s ≤ 3 * M :=
  (Cslib.Probability.trinomialDeg_le_three_mul T s).trans <| Nat.mul_le_mul_left 3 <| max_le
    (Nat.clog_le_of_le_pow (max_le hT (Nat.le_self_pow (by omega) 2))) (max_le hs hM)

theorem succinctTableMetaBits_le {I m : ℕ} (hm : m ≤ 2 ^ I) :
    succinctTableMetaBits I m ≤ 75 * m * (I + 2) + 9 * (I + 2) := by
  have hq : FeistelQuotient.quotientBits (2 ^ I) m ≤ I :=
    FeistelQuotient.quotientBits_le_of_le_pow le_rfl
  have hll : Dynamic.logLogFactor m ≤ I + 2 :=
    (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans <| Nat.clog_le_of_le_pow <| max_le
      (hm.trans (Nat.pow_le_pow_right Nat.two_pos (by omega)))
      (Nat.pow_le_pow_right Nat.two_pos (by omega) : 2 ^ 2 ≤ 2 ^ (I + 2))
  have hloc := (SuccinctBucket.localMetaLen_mul_effBucketPosBits_le m).trans
    (Nat.mul_le_mul_left (54 * m) hll)
  have hglob := (SuccinctBucket.globalMetaLen_mul_globalPtrBits_le m).trans
    (Nat.mul_le_mul_left (20 * m) hll)
  have htri := trinomialDeg_le_of_le_two_pow (M := I + 2) (by omega)
    (Nat.pow_le_pow_right Nat.two_pos (hq.trans (by omega)))
    ((SuccinctBucket.totalMicroBits_le_of_le_pow hm le_rfl).trans (by omega))
  rw [succinctTableMetaBits]
  linarith [Nat.mul_le_mul_left m hq]

theorem TreeSchedule.idCompressorSeedBits_le_of_two_le (P : TreeSchedule) {ℓ : ℕ}
    (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) :
    FeistelPerm.idCompressorSeedBits (P.idBits ℓ) (P.idCompRightUniv ℓ) ≤
      6 * max (P.idBits (ℓ - 1)) 1 := by
  have hstep := P.idBits_step_le (ℓ - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at hstep
  have hcl : Nat.clog 2 (max (P.idCompRightUniv ℓ) 2) ≤ max (P.idBits (ℓ - 1)) 1 := by
    rw [TreeSchedule.idCompRightUniv, ite_eq_right (by omega), TreeSchedule.remBits]
    exact Nat.clog_le_of_le_pow (max_le (Nat.pow_le_pow_right Nat.two_pos (by omega))
      (Nat.le_self_pow (by omega) 2))
  have := FeistelPerm.idCompressorSeedBits_le (P.idBits ℓ) (P.idCompRightUniv ℓ)
  omega

theorem TreeSchedule.waitingListBits_le_of_two_le (P : TreeSchedule) {ℓ : ℕ}
    (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) :
    waitingListBits (P.waitCap ℓ) (P.idBits ℓ) (P.idBits (ℓ - 1)) ≤
      (4 * P.delta ℓ + 1) * P.idBits (ℓ - 1) := by
  have hd_lt := P.delta_lt_nFloor ℓ (by omega) hℓ
  have hnh_id := P.nHigh_le_two_pow_idBits ℓ (by omega) hℓ
  have hstep := P.idBits_step_le (ℓ - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at hstep
  have hcl_w : Nat.clog 2 (2 * P.delta ℓ + 1) ≤ P.idBits ℓ := Nat.clog_le_of_le_pow (by omega)
  have hmul : 2 * P.delta ℓ * (P.idBits ℓ + P.idBits (ℓ - 1)) ≤
      2 * P.delta ℓ * (2 * P.idBits (ℓ - 1)) := Nat.mul_le_mul_left _ (by omega)
  rw [waitingListBits, TreeSchedule.waitCap]
  linarith

private theorem mul_spaceConst_le_threshold (ε_inv α_inv : ℕ) :
    256 * FeistelPerm.childRouterSpaceConst ε_inv α_inv ≤
      FeistelPerm.childRouterThreshold ε_inv α_inv := by
  rw [FeistelPerm.childRouterSpaceConst_eq, FeistelPerm.childRouterThreshold_eq]
  set E := max ε_inv 1
  set c := FeistelPerm.childRouterChars ε_inv
  set A := c * max α_inv 1
  set q := FeistelPerm.childRouterRep ε_inv α_inv
  have hE1 : 1 ≤ E := le_max_right _ _
  have hc_eq : c = 2 * E := FeistelPerm.childRouterChars_eq ε_inv
  have hq_eq : q = A + 2 := FeistelPerm.childRouterRep_eq ε_inv α_inv
  have hA : 1 ≤ A := Nat.mul_pos (by omega) (by omega)
  rw [show 2 * q * c = 2 * c * q by ring]
  set d := 2 * c * q
  have hcd : c ≤ d :=
    (Nat.le_mul_of_pos_left c Nat.two_pos).trans (Nat.le_mul_of_pos_right _ (by omega))
  calc 256 * (d ^ E * 2 ^ (2 * c ^ 2 + c + 2))
      ≤ 2 ^ 8 * ((2 ^ d) ^ E * 2 ^ (2 * c ^ 2 + c + 2)) := by
        gcongr; exacts [by norm_num, Nat.lt_two_pow_self.le]
    _ = 2 ^ (8 + (d * E + (2 * c ^ 2 + c + 2))) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ 2 ^ (4 * (d + 1) ^ 2) := Nat.pow_le_pow_right Nat.two_pos (by nlinarith)
    _ ≤ _ := Nat.pow_le_pow_right Nat.two_pos
        ((le_max_right _ _).trans (Nat.le_mul_of_pos_left _ hA))

private theorem paddedUniv_le_two_mul_pow {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).paddedUniv ≤ 2 * n ^ (p_max + 2) := by
  have hn := h.two_le_n
  have hL : 4 * 55 ^ 2 ≤ Nat.log 2 n :=
    (h.mul_param_le_log (by decide : 4 * 55 ^ 2 ≤ 2560000)).trans' (by omega)
  have hL55 : Nat.log 2 n ^ 55 ≤ n :=
    (Nat.pow_le_two_pow (by decide) hL).trans (Nat.pow_log_le_self 2 (by omega))
  calc (canonicalSchedule h).paddedUniv
      ≤ U + n * Nat.log 2 n ^ 55 := paddedUniv_le_add_mul_log_pow h
    _ ≤ n ^ (p_max + 1) * n + n ^ p_max * n * n := Nat.add_le_add
        (h.univ_le_pow.trans (Nat.le_mul_of_pos_right _ (by omega)))
        (Nat.mul_le_mul (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))) hL55)
    _ = 2 * n ^ (p_max + 2) := by ring

/-- Coarse power-of-two upper bound on the padded universe:
`paddedUniv ≤ 2 ^ (2 * (p_max + 2) * log₂ n)`. -/
theorem paddedUniv_le_two_pow_mul_log {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).paddedUniv ≤ 2 ^ (2 * (p_max + 2) * Nat.log 2 n) := by
  have hL4 : 4 ≤ Nat.log 2 n := h.four_le_log
  calc (canonicalSchedule h).paddedUniv
      ≤ 2 * n ^ (p_max + 2) := paddedUniv_le_two_mul_pow h
    _ ≤ 2 * (2 ^ (Nat.log 2 n + 1)) ^ (p_max + 2) := Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le _)
    _ = 2 ^ ((Nat.log 2 n + 1) * (p_max + 2) + 1) := by rw [← Nat.pow_mul, ← pow_succ']
    _ ≤ 2 ^ (2 * (p_max + 2) * Nat.log 2 n) := Nat.pow_le_pow_right Nat.two_pos (by nlinarith)

/-- At every tree level `j ≤ depth`, floor load satisfies `nFloor j ≥ 256 ^ 9`. -/
theorem nFloor_ge_pow_256 {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {j : ℕ}
    (hj : j ≤ (canonicalSchedule h).depth) :
    256 ^ 9 ≤ (canonicalSchedule h).nFloor j := by
  rw [canonicalSchedule_depth] at hj
  rw [canonicalSchedule_nFloor_eq]
  exact canonical_nFloor_ge_pow_256 h hj

/-- The root router maps the padded universe: `2 ^ s₀ * T₀ = paddedUniv`. -/
private theorem TreeSchedule.two_pow_branchBits_mul_routerRightUniv_zero (P : TreeSchedule) :
    2 ^ P.branchBits 0 * P.routerRightUniv 0 = P.paddedUniv := by
  simp [routerRightUniv, paddedUniv, branchFactor, Nat.mul_assoc]

/-- The canonical ID width in terms of the floor load of the schedule. -/
private theorem canonicalSchedule_idBits_eq_clog {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) (ℓ : ℕ) :
    (canonicalSchedule h).idBits ℓ =
      4 * Nat.clog 2 (2 * max ((canonicalSchedule h).nFloor ℓ) 1) := by
  rw [canonicalSchedule_idBits_eq, idBits, ← canonicalSchedule_nFloor_eq]

/-- Root extraction for the `DoubleTabulation` seed bound: if `B ^ E ≤ C * D` with
`2 * (q + 1) ≤ E`, a domain `D ≤ c * y ^ q` and a constant `c * C ≤ y`, then `B ^ 2 ≤ y`. -/
private theorem sq_le_of_pow_le_mul {B E C D c y q : ℕ} (hE : 2 * (q + 1) ≤ E)
    (hB : B ^ E ≤ C * D) (hD : D ≤ c * y ^ q) (hC : c * C ≤ y) : B ^ 2 ≤ y := by
  rcases Nat.eq_zero_or_pos B with rfl | hB1
  · simp
  refine (Nat.pow_le_pow_iff_left (Nat.succ_ne_zero q)).mp ?_
  calc (B ^ 2) ^ (q + 1) = B ^ (2 * (q + 1)) := (pow_mul B 2 _).symm
    _ ≤ C * D := (Nat.pow_le_pow_right hB1 hE).trans hB
    _ ≤ c * C * y ^ q := (Nat.mul_le_mul_left C hD).trans_eq (by ring)
    _ ≤ y ^ (q + 1) := (Nat.mul_le_mul_right _ hC).trans_eq (pow_succ' y q).symm

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
  have hT_pos : 1 ≤ P.routerRightUniv ℓ := by
    rw [TreeSchedule.routerRightUniv]; split_ifs
    exacts [Nat.mul_pos (Nat.two_pow_pos _) P.quotOne_pos, Nat.two_pow_pos _]
  have hpow := FeistelPerm.childRouterSeedBits_pow_le P.epsInv P.alphaInv (P.branchBits ℓ) hT_pos
  have hnl_nf : P.nLow ℓ ≤ P.nFloor ℓ := by
    have := P.nFloor_zero
    rw [TreeSchedule.nLow]; split_ifs with h0 <;> [(subst h0; omega); omega]
  have h256C := ((mul_spaceConst_le_threshold P.epsInv P.alphaInv).trans hth).trans hnl_nf
  have hE : max 12 (2 * (p_max + 3)) ≤ max P.epsInv 1 := by
    rw [canonicalSchedule_epsInv, routerEpsInv_eq]; exact le_max_left _ _
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · rw [P.two_pow_branchBits_mul_routerRightUniv_zero] at hpow
    rw [P.nFloor_zero, show P.cap = n from canonicalSchedule_cap h] at h256C ⊢
    exact sq_le_of_pow_le_mul (by omega) hpow (paddedUniv_le_two_mul_pow h) (by omega)
  · have hdom : 2 ^ P.branchBits ℓ * P.routerRightUniv ℓ = 2 ^ P.idBits ℓ := by
      have := P.idBits_step_le ℓ hpos hlt
      rw [TreeSchedule.routerRightUniv, ite_eq_right hpos.ne', ← pow_add]
      congr 1; omega
    rw [hdom, canonicalSchedule_idBits_eq_clog] at hpow
    exact sq_le_of_pow_le_mul (q := 4) (by omega) hpow (two_pow_four_mul_clog_le
      ((Nat.one_le_pow 9 256 (by decide)).trans (nFloor_ge_pow_256 h hlt.le))) h256C

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
    have hm_le : FeistelPerm.childRouterHalfInd (P.nHigh 0) ≤ 3 * L + 7 :=
      canonicalSchedule_childRouterHalfInd_nHigh_zero_le h
    have hb0 : P.branchBits 0 ≤ L := by
      simp only [P, canonicalSchedule_branchBits, branchBits, cumBranchBits,
        Nat.succ_ne_zero, ↓reduceIte, Nat.sub_zero]
      exact Nat.log_mono_right (Nat.div_le_self n _)
    have htd0 : Cslib.Probability.trinomialDeg (P.routerRightUniv 0) (P.branchBits 0) ≤
        3 * (2 * (p_max + 2) * L) :=
      trinomialDeg_le_of_le_two_pow (Nat.mul_pos (by omega) (by omega))
        (((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans_eq
          P.two_pow_branchBits_mul_routerRightUniv_zero).trans (paddedUniv_le_two_pow_mul_log h))
        (hb0.trans (Nat.le_mul_of_pos_left _ (by omega)))
    rw [P.nFloor_zero, show P.cap = n from canonicalSchedule_cap h]
    calc (2 * FeistelPerm.childRouterHalfInd (P.nHigh 0) *
          Cslib.Probability.trinomialDeg (P.routerRightUniv 0) (P.branchBits 0)) ^ 2
        ≤ (2 * (4 * L) * (3 * (2 * (p_max + 2) * L))) ^ 2 := by gcongr; omega
      _ = (48 * (p_max + 2) * L ^ 2) ^ 2 := by ring
      _ ≤ (L * L ^ 2) ^ 2 := by gcongr; omega
      _ = L ^ 6 := by ring
      _ ≤ 2 ^ L := Nat.pow_le_two_pow (by decide) (by omega)
      _ ≤ n := Nat.pow_log_le_self 2 (by have := h.two_le_n; omega)
  · set y := P.nFloor ℓ
    have hy_ge : 256 ^ 9 ≤ y := nFloor_ge_pow_256 h hlt.le
    have hid_eq : P.idBits ℓ = 4 * Nat.clog 2 (2 * max y 1) := canonicalSchedule_idBits_eq_clog h ℓ
    set ly := Nat.clog 2 (2 * max y 1)
    have hly_ge : 72 < ly := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega)
    have hly_pow : 2 ^ (ly - 1) < 2 * max y 1 :=
      Nat.pow_pred_clog_lt_self Nat.one_lt_two (by omega)
    have hhd : 2 * P.delta ℓ ≤ y := canonicalSchedule_two_mul_delta_le_nFloor h hlt.le
    have hm_le : FeistelPerm.childRouterHalfInd (P.nHigh ℓ) ≤ 4 * ly := by
      have hcl : Nat.clog 2 (max (P.nHigh ℓ) 2) ≤ ly := Nat.clog_mono_right 2 <| by
        rw [TreeSchedule.nHigh, ite_eq_right hpos.ne']; omega
      rw [FeistelPerm.childRouterHalfInd_eq]
      omega
    have htd_le : Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ) ≤
        3 * (4 * ly) := by
      have hstep_id := P.idBits_step_le ℓ hpos hlt
      refine trinomialDeg_le_of_le_two_pow (by omega) ?_ (by omega)
      rw [TreeSchedule.routerRightUniv, ite_eq_right hpos.ne']
      exact Nat.pow_le_pow_right Nat.two_pos (by omega)
    -- `2 * (96 * ly ^ 2) ^ 2 ≤ 2 ^ (ly - 1)` for `ly ≥ 73`, through `(ly / 4) ^ 2 ≤ 2 ^ (ly / 4)`
    have h2_sq : 2 * (96 * ly ^ 2) ^ 2 ≤ 2 ^ (ly - 1) :=
      calc 2 * (96 * ly ^ 2) ^ 2 ≤ 2 * (96 * (5 * (ly / 4)) ^ 2) ^ 2 := by gcongr; omega
        _ = 11520000 * ((ly / 4) ^ 2) ^ 2 := by ring
        _ ≤ 2 ^ 24 * (2 ^ (ly / 4)) ^ 2 :=
            Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (Nat.sq_le_two_pow (by omega)) 2)
        _ = 2 ^ (24 + ly / 4 * 2) := by rw [← pow_mul, ← pow_add]
        _ ≤ 2 ^ (ly - 1) := Nat.pow_le_pow_right Nat.two_pos (by omega)
    have hprod : (2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) *
        Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ)) ^ 2 ≤
        (96 * ly ^ 2) ^ 2 :=
      Nat.pow_le_pow_left ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm_le) htd_le).trans_eq
        (by ring)) 2
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
