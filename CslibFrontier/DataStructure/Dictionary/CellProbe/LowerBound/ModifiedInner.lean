/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.OuterGame
import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.PrefixMessage
import CslibFrontier.Probability.Conditioning
import CslibFrontier.Probability.PMF.Expect

/-!
# Section 8.1 Modified Inner Game and Outer Lemmas

Public endpoints for the Section 8.1 query-free inner game of [LiLiangYuZhou2023] (Lemma 8.1,
pp. 28–30): `queryFreeInnerDist`, its consistency probability bound, segment-rest expectation bound,
the update-only `OuterLemma` (`outer_lemma_insertDelete`), and the large-value `OuterLemma`
(`outer_lemma_largeVal_insertQueryDelete`).

All internal replay, symmetry, target-fiber, and prefix-free message helpers are imported privately
so downstream callers receive only these five public declarations.

## Main definitions

* `Cslib.DataStructure.Dictionary.CellProbe.queryFreeInnerDist`: conditional `(seed, B)`
  distribution for the query-free inner game of Section 8.1.

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.prob_isModeSeedConsistent_queryFreeInnerDist_le`:
  Section 8.1 Lemma 8.1 consistency upper bound.
* `Cslib.DataStructure.Dictionary.CellProbe.expected_card_modeConsistent_segmentRest_lt_half_le`:
  half-block consistency expectation bound.
* `Cslib.DataStructure.Dictionary.CellProbe.outer_lemma_insertDelete`: update-only `OuterLemma`.
* `Cslib.DataStructure.Dictionary.CellProbe.outer_lemma_largeVal_insertQueryDelete`: large-value
  (`V > U ^ 3`) `OuterLemma` for `insertQueryDeleteDist`.
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.Probability

/-! #### Public Section 8.1 theorems (Lemma 8.1 and update-only / large-value `OuterLemma`) -/

private theorem disjoint_insertedSet_activeKeys {U V n t₀ r : ℕ} (s : HardKeyValSeed U V n)
    (hr : t₀ + r ≤ n) :
    Disjoint (s.insertedSet t₀ r hr) (s.activeKeys t₀ (Nat.le_of_add_right_le hr)) := by
  refine Finset.disjoint_left.mpr fun u hu hact => ?_
  simp only [HardKeyValSeed.insertedSet, segInsertedKeys_apply, HardKeyValSeed.activeKeys,
    HardKeyValSeed.permKeyEmb, Finset.mem_image, Finset.mem_map, Finset.mem_univ, true_and,
    windowEmb_apply, Function.Embedding.trans_apply, Equiv.coe_toEmbedding] at hu hact
  obtain ⟨j, rfl⟩ := hu
  obtain ⟨k, hk⟩ := hact
  have hge : s.keys (liftDelPerm s.delPerm ⟨n + (t₀ + j.val), by have := j.isLt; omega⟩) =
      s.keys ⟨n + (t₀ + j.val), by have := j.isLt; omega⟩ := by
    rw [liftDelPerm_apply_ge s.delPerm (by omega) (by have := j.isLt; omega)]
  rw [← hge] at hk
  have hidx := congrArg Fin.val ((liftDelPerm s.delPerm).injective (s.keys.injective hk))
  dsimp only at hidx
  have := k.isLt; omega

open Classical in
/-- Query-free inner-game conditional `(seed, B)` distribution sampling `B ⊆ Finset.univ \ K`
uniformly among `m`-subsets with `(A ∩ B).card = g` under `3 * n ≤ U` ([LiLiangYuZhou2023],
Section 8.1, Lemma 8.1, p. 28 / PDF p. 29). -/
noncomputable def queryFreeInnerDist {U V n : ℕ} (t₀ m g : ℕ) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
    (hg : g ≤ m) (ht₀ : t₀ + m ≤ n) :
    PMF (HardKeyValSeed U V n × Finset (Fin U)) :=
  innerPoolDist (by omega) hV
    (fun s => (((Finset.univ \ s.activeKeys t₀ (Nat.le_of_add_right_le ht₀)).powersetCard m).filter
      fun B => (s.insertedSet t₀ m ht₀ ∩ B).card = g))
    (fun s => by
      have ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
      have hsub : s.insertedSet t₀ m ht₀ ⊆ Finset.univ \ s.activeKeys t₀ ht₀_n :=
        Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, disjoint_insertedSet_activeKeys s ht₀⟩
      have hcard_pool : (Finset.univ \ s.activeKeys t₀ ht₀_n).card = U - n := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin, card_activeKeys s ht₀_n]
      rw [← Finset.card_pos, card_inter_filter_powersetCard hsub (card_insertedSet s ht₀),
        hcard_pool]
      exact mul_pos (Nat.choose_pos hg) (Nat.choose_pos (by omega)))

open Classical in
/-- **Lemma 8.1** ([LiLiangYuZhou2023], Section 8.1, pp. 28–30 / PDF pp. 29–31, adapted with the
deterministic `c = 1` probe cap and Step 6 internal Markov sub-conditioning): under `3 * n ≤ U`,
`2 ≤ m`, `2 * m ≤ n`, and `g < m / 2`, the probability of `IsModeSeedConsistent` on
`queryFreeInnerDist` (`|A ∩ B| = g`) is at most `U ^ (-γ * m)`. -/
theorem prob_isModeSeedConsistent_queryFreeInnerDist_le (withQueries : Bool)
    {U V n t₀ m g cells w : ℕ} {γ R t : ℝ}
    (hU : 3 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (hm_n : 2 * m ≤ n)
    (hg : g < m / 2) (ht₀ : t₀ + m ≤ n)
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
    (hbudget : 2 * R + 7 * (m : ℝ) + 2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
      2 * γ * (m : ℝ) * Real.logb 2 U ≤
      ((m : ℝ) / 2) * Real.logb 2 V - (m : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)))
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) :
    (((queryFreeInnerDist t₀ m g hU hV (by omega) ht₀).map fun sb =>
      decide (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2)) true).toReal ≤
      (U : ℝ) ^ (-γ * (m : ℝ)) := by
  let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  let pool (s : HardKeyValSeed U V n) := Finset.univ \ s.activeKeys t₀ ht₀_n
  let ctx : PoolCtx U V n t₀ m g (U - n) ht₀ :=
    { pool := pool
      hcard := fun s => by
        dsimp only [pool]
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin, card_activeKeys s ht₀_n]
      hA := fun s =>
        Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, disjoint_insertedSet_activeKeys s ht₀⟩
      hdisj := fun _ => Finset.sdiff_disjoint
      hact := fun τ _ s => by
        dsimp only [pool]
        rw [actSeed8Equiv_activeKeys, Finset.map_sdiff]
        congr 1; ext x; simp only [Finset.mem_univ, Finset.mem_map, Equiv.coe_toEmbedding, true_iff]
        exact ⟨τ.symm x, trivial, τ.apply_symm_apply x⟩
      Fg := fun s => ((pool s).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card = g
      hFg := fun _ => rfl
      hne := fun s => by
        rw [← Finset.card_pos, card_inter_filter_powersetCard
          (Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, disjoint_insertedSet_activeKeys s ht₀⟩)
          (card_insertedSet s ht₀), Finset.card_sdiff,
          Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          card_activeKeys s ht₀_n]
        exact mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)) }
  exact prob_queryFreePool_eq_le withQueries hU hV hm hm_n hg hspace hbudget hcorr ctx

open Classical in
/-- Claim 4.2 far-candidate expectation bound for `IsModeSeedConsistent` over the remaining
inserted-key pool `s.insertedSet t₀ r_rest hrest` ([LiLiangYuZhou2023], Section 4.3, Claim 4.2,
p. 17 / PDF p. 18 and Section 8.1, Lemma 8.1, p. 28 / PDF p. 29). -/
theorem expected_card_modeConsistent_segmentRest_lt_half_le (withQueries : Bool)
    {U V n t₀ m r_rest cells w : ℕ} {γ R t : ℝ}
    (hU : 3 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (hm_n : 2 * m ≤ n)
    (hrest_ge : 2 * m ≤ r_rest) (hrest : t₀ + r_rest ≤ n)
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
    (hbudget : 2 * R + 7 * (m : ℝ) + 2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
      2 * γ * (m : ℝ) * Real.logb 2 U ≤
      ((m : ℝ) / 2) * Real.logb 2 V - (m : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)))
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) :
    let ht₀ : t₀ + m ≤ n := by omega
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
    (∑ s : HardKeyValSeed U V n, ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
      ((((((s.insertedSet t₀ r_rest hrest).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2).filter
        (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t s)).card : ℕ) : ℝ)) ≤
      (r_rest.choose m : ℝ) * (U : ℝ) ^ (-γ * (m : ℝ)) := by
  dsimp only
  let ht₀ : t₀ + m ≤ n := by omega
  let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  let pool (s : HardKeyValSeed U V n) := s.insertedSet t₀ r_rest hrest
  have hcard_pool (s : HardKeyValSeed U V n) : (pool s).card = r_rest :=
    card_insertedSet s hrest
  have hA_pool (s : HardKeyValSeed U V n) : s.insertedSet t₀ m ht₀ ⊆ pool s := fun u hu => by
    simp only [pool, HardKeyValSeed.insertedSet, segInsertedKeys_apply, Finset.mem_image,
      Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨r, rfl⟩ := hu
    exact ⟨⟨r.val, by omega⟩, rfl⟩
  have hne : ∀ s : HardKeyValSeed U V n,
      (((pool s).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2).Nonempty := fun s => by
    have h0 : (((pool s).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card = 0).Nonempty := by
      rw [← Finset.card_pos, card_inter_filter_powersetCard (hA_pool s) (card_insertedSet s ht₀),
        hcard_pool]
      exact mul_pos (Nat.choose_pos (Nat.zero_le m)) (Nat.choose_pos (by omega))
    obtain ⟨B, hB⟩ := h0
    exact ⟨B, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hB).1,
      by rw [(Finset.mem_filter.mp hB).2]; omega⟩⟩
  refine (prob_and_expect_innerPoolDist_lt_half_le (by omega) hV ht₀ hrest_ge
    (Real.rpow_nonneg (Nat.cast_nonneg U) _) pool hcard_pool hA_pool
    (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t) (fun g hg hne_g => ?_) hne).2
  exact prob_queryFreePool_eq_le withQueries hU hV hm hm_n hg hspace hbudget hcorr
    { pool := pool
      hcard := hcard_pool
      hA := hA_pool
      hdisj := fun s => disjoint_insertedSet_activeKeys s hrest
      hact := fun τ δ s => actSeed8Equiv_insertedSet τ δ s t₀ r_rest hrest
      Fg := _
      hFg := fun _ => rfl
      hne := hne_g }

private theorem outer_lemma_of_val_budget (withQueries : Bool) {U V n cells w : ℕ}
    {R_outer R_inner γ t : ℝ} (hU : 3 * n ≤ U) (hV : 1 ≤ V)
    (hspace_outer : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_outer)
    (hspace_inner : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_inner)
    (T : MetaTree) {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (hγ : 0 < γ) (ht : 0 < t) {ℓ b : ℕ} (hℓ : 1 ≤ ℓ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (hR_outer : 100 * R_outer ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
    (hbudget_inner : 2 * R_inner + 7 * (T.blockSize ℓ : ℝ) + 2 * (T.blockSize ℓ : ℝ) * t +
      γ * (T.blockSize ℓ : ℝ) * (w : ℝ) + 2 * γ * (T.blockSize ℓ : ℝ) * Real.logb 2 U ≤
      ((T.blockSize ℓ : ℝ) / 2) * Real.logb 2 V -
        (T.blockSize ℓ : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ))) :
    (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        ∑' ops, (modeDist withQueries U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeCost D_det n (modeStride withQueries) ops ℓ b : ℝ) ∨
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
        ∑' ops, (modeDist withQueries U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeProbes D_det n (modeStride withQueries) ops (ℓ + 1) b : ℝ) := by
  have hm_ge2 : 2 ≤ T.blockSize ℓ :=
    (Nat.pow_le_pow_right (by decide) hℓ).trans (T.two_pow_le_blockSize ℓ)
  have hF_ge2 : 2 ≤ T.fanout (ℓ + 1) := T.two_le_fanout (Nat.le_add_left 1 ℓ)
  have hm_n : 2 * T.blockSize ℓ ≤ n := by
    clear hF_lo
    have h1 : 2 * T.blockSize ℓ ≤ T.blockSize ℓ * T.fanout (ℓ + 1) := by
      rw [mul_comm 2]; exact Nat.mul_le_mul_left _ hF_ge2
    have h2 : T.blockSize (ℓ + 1) ≤ T.nodeStop (ℓ + 1) b :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos b)
    rw [T.blockSize_succ] at h2; omega
  have hU2 : 2 ≤ U := by clear hF_lo; omega
  exact outer_node_lower_bound withQueries
    (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hU2 hV hspace_outer T hcorr
    hγ ht hℓ ht_stop hF_lo hF_hi hR_outer fun i _ => by
      clear hF_lo
      have hFh : 2 ≤ T.fanout (ℓ + 1) - i.val := by omega
      exact expected_card_modeConsistent_segmentRest_lt_half_le withQueries hU hV hm_ge2 hm_n
        (Nat.mul_le_mul_right _ hFh) (nodeStart_add_rest_le T ht_stop i.val i.isLt.le)
        hspace_inner hbudget_inner hcorr

/-- Update-only **Outer Lemma** on `insertDeleteDist` ([LiLiangYuZhou2023], Section 8.1, pp. 27–30 /
PDF pp. 28–31, combining Protocol 1 `outer_node_lower_bound false` with Lemma 8.1). -/
theorem outer_lemma_insertDelete {U V n cells w : ℕ} {R_outer R_inner γ t : ℝ}
    (hU : 3 * n ≤ U) (hV : 1 ≤ V)
    (hspace_outer : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_outer)
    (hspace_inner : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_inner)
    (T : MetaTree) {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (hγ : 0 < γ) (ht : 0 < t) {ℓ b : ℕ} (hℓ : 1 ≤ ℓ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (hR_outer : 100 * R_outer ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
    (hbudget_inner : 2 * R_inner + 7 * (T.blockSize ℓ : ℝ) + 2 * (T.blockSize ℓ : ℝ) * t +
      γ * (T.blockSize ℓ : ℝ) * (w : ℝ) + 2 * γ * (T.blockSize ℓ : ℝ) * Real.logb 2 U ≤
      ((T.blockSize ℓ : ℝ) / 2) * Real.logb 2 V -
        (T.blockSize ℓ : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ))) :
    (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        ∑' ops, (insertDeleteDist U V n (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU)
          hV ops).toReal * (T.nodeCost D_det n 2 ops ℓ b : ℝ) ∨
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
        ∑' ops, (insertDeleteDist U V n (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU)
          hV ops).toReal * (T.nodeProbes D_det n 2 ops (ℓ + 1) b : ℝ) := by
  exact
    outer_lemma_of_val_budget false hU hV hspace_outer hspace_inner T
      (by simpa only [modeHorizon, modeStride, Bool.false_eq_true, ↓reduceIte,
        show n + 2 * n = 3 * n by ring] using hcorr)
      hγ ht hℓ ht_stop hF_lo hF_hi hR_outer hbudget_inner

/-- Large-value **Outer Lemma** on `insertQueryDeleteDist` ([LiLiangYuZhou2023], Sections 7 and 8.1,
combining `outer_node_lower_bound true` with Lemma 8.1 so word sizes `w = Θ(log U + log V)` remain
covered when `V > U ^ 3` without secondary hash-table reductions). -/
theorem outer_lemma_largeVal_insertQueryDelete {U V n cells w : ℕ} {R_outer R_inner γ t : ℝ}
    (hU : 3 * n ≤ U) (hV : 1 ≤ V)
    (hspace_outer : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_outer)
    (hspace_inner : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_inner)
    (T : MetaTree) {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (hγ : 0 < γ) (ht : 0 < t) {ℓ b : ℕ} (hℓ : 1 ≤ ℓ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (hR_outer : 100 * R_outer ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
    (hbudget_inner : 2 * R_inner + 7 * (T.blockSize ℓ : ℝ) + 2 * (T.blockSize ℓ : ℝ) * t +
      γ * (T.blockSize ℓ : ℝ) * (w : ℝ) + 2 * γ * (T.blockSize ℓ : ℝ) * Real.logb 2 U ≤
      ((T.blockSize ℓ : ℝ) / 2) * Real.logb 2 V -
        (T.blockSize ℓ : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ))) :
    (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        ∑' ops, (insertQueryDeleteDist U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeCost D_det n 3 ops ℓ b : ℝ) ∨
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
        ∑' ops, (insertQueryDeleteDist U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeProbes D_det n 3 ops (ℓ + 1) b : ℝ) := by
  exact
    outer_lemma_of_val_budget true hU hV hspace_outer hspace_inner T
      (by simpa only [modeHorizon, modeStride, ↓reduceIte,
        show n + 3 * n = 4 * n by ring] using hcorr)
      hγ ht hℓ ht_stop hF_lo hF_hi hR_outer hbudget_inner

end Cslib.DataStructure.Dictionary.CellProbe
