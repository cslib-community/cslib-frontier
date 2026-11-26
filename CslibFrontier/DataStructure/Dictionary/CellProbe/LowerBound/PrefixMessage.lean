/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.PoolSymmetry
import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.TargetFiber
import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
import CslibFrontier.Foundations.Data.Finset.OrderEmb
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.Probability.Coding.PrefixFreeEntropy
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map

/-!
# Section 8.1 Six-Piece Prefix-Free Message Proof

Implements the 6-piece prefix-free encoding argument of Lemma 8.1 ([LiLiangYuZhou2023], pp. 28–30)
bounding `Pr[IsModeSeedConsistent]` over an equivariant candidate pool context `PoolCtx`.

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.prob_queryFreePool_eq_le`: Shannon/prefix-free upper
  bound on the consistency probability under `innerPoolDist`.
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.BitString Cslib.Probability Cslib.Probability.Coding InformationTheory
open Finset (orderSubset orderSubset_apply image_orderSubset)

private theorem modeCandidateOps_congr (withQueries : Bool) {U V n t₀ m : ℕ}
    {s₁ s₂ : HardKeyValSeed U V n} (ht₀ : t₀ + m ≤ n) {B₁ B₂ : Finset (Fin U)}
    (hB₁ : B₁.card = m) (hB₂ : B₂.card = m)
    (ha : (fun r => segInsertedKeys s₁.keys t₀ m ht₀ r) =
      fun r => segInsertedKeys s₂.keys t₀ m ht₀ r)
    (hB : B₁ = B₂)
    (hd : (fun r => segDeletedKeys s₁.keys s₁.delPerm t₀ m ht₀ r) =
      fun r => segDeletedKeys s₂.keys s₂.delPerm t₀ m ht₀ r)
    (hkv : ∀ x ∈ B₁, s₁.kv x = s₂.kv x) :
    s₁.modeCandidateOps withQueries t₀ m ht₀ B₁ hB₁ =
      s₂.modeCandidateOps withQueries t₀ m ht₀ B₂ hB₂ := by
  subst hB
  have ha_emb : segInsertedKeys s₁.keys t₀ m ht₀ = segInsertedKeys s₂.keys t₀ m ht₀ :=
    Function.Embedding.ext (congrFun ha)
  have hd_emb : segDeletedKeys s₁.keys s₁.delPerm t₀ m ht₀ =
      segDeletedKeys s₂.keys s₂.delPerm t₀ m ht₀ :=
    Function.Embedding.ext (congrFun hd)
  rw [HardKeyValSeed.modeCandidateOps_eq, HardKeyValSeed.modeCandidateOps_eq]
  cases withQueries
  · simp only [Bool.false_eq_true, ↓reduceIte, HardKeyValSeed.candidateUpdateOps_eq,
      ha_emb, hd_emb, candidateDeleteInsertOps]
    refine List.flatMap_congr fun r _ => ?_
    rw [hkv _ (by rw [orderSubset_apply]; exact Finset.orderEmbOfFin_mem B₁ hB₁ _)]
  · simp only [↓reduceIte, HardKeyValSeed.candidateOps_eq, ha_emb, hd_emb]
    exact candidateQueryDeleteInsertOps_congr _ hB₁ _ hkv

private theorem decodeDict_modeCandidateOps_eq (withQueries : Bool) {U V n t₀ m cells w : ℕ}
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (s : HardKeyValSeed U V n) (ht₀ : t₀ + m ≤ n) {B : Finset (Fin U)} (hB : B.card = m)
    (hdisj : Disjoint B (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀))) :
    let stride := modeStride withQueries
    let step₀ := n + stride * t₀
    let C_bef := memAt D_det (s.modeOps withQueries) step₀
    let C_post := (D_det.runInterval step₀ C_bef (s.modeCandidateOps withQueries t₀ m ht₀ B hB)).2
    decodeDict D_det (n + stride * (t₀ + m)) C_post =
      (fun u => if u ∈ (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
          Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)) ∪ B
        then some (s.kv u).val else none) := by
  dsimp only
  let stride := modeStride withQueries
  let step₀ := n + stride * t₀
  let pref_bef := (s.modeOps withQueries).take step₀
  obtain ⟨hvh, hlen, hst⟩ := validHistory_and_run_modeCandidateOps withQueries s ht₀ hB hdisj
  have hpost_eq : (D_det.runInterval step₀ (memAt D_det (s.modeOps withQueries) step₀)
      (s.modeCandidateOps withQueries t₀ m ht₀ B hB)).2 =
      (D_det.runSeq (pref_bef ++ s.modeCandidateOps withQueries t₀ m ht₀ B hB)).2 := by
    symm; dsimp only [memAt, pref_bef, step₀]
    rw [IndexedScheme.runSeq, IndexedScheme.runInterval_append, Nat.zero_add,
      s.length_take_modeOps withQueries (Nat.le_of_add_right_le ht₀)]
    rfl
  have hle : (pref_bef ++ s.modeCandidateOps withQueries t₀ m ht₀ B hB).length ≤
      modeHorizon withQueries n := by
    rw [hlen]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ht₀) n
  have hdec := decodeDict_runSeq_eq hcorr hvh hle
  rw [hlen, ← hpost_eq] at hdec
  exact hdec.trans hst

private theorem dom_eq_of_ite_some_eq {α β : Type*} [DecidableEq α] {S₁ S₂ : Finset α}
    {f₁ f₂ : α → β}
    (h : (fun u => if u ∈ S₁ then some (f₁ u) else none) =
      fun u => if u ∈ S₂ then some (f₂ u) else none) :
    S₁ = S₂ ∧ ∀ u ∈ S₁, f₁ u = f₂ u := by
  have hS : S₁ = S₂ := Finset.ext fun u => by
    have hu := congrFun h u
    by_cases h1 : u ∈ S₁ <;> by_cases h2 : u ∈ S₂ <;> simp [h1, h2] at hu ⊢
  exact ⟨hS, fun u hu => by simpa [hu, hS ▸ hu] using congrFun h u⟩

private theorem ite_mem_congr {α β : Type*} [DecidableEq α] {S₁ S₂ : Finset α}
    {f₁ f₂ : α → β} (z : β) (hS : S₁ = S₂) (hf : ∀ u ∈ S₁, f₁ u = f₂ u) :
    (fun u => if u ∈ S₁ then f₁ u else z) = fun u => if u ∈ S₂ then f₂ u else z := by
  subst hS
  funext u
  by_cases hu : u ∈ S₁
  · simp [hu, hf u hu]
  · simp [hu]

open Classical in
theorem prob_queryFreePool_eq_le (withQueries : Bool) {U V n t₀ m g P_size cells w : ℕ}
    {γ R t : ℝ} (hU : 3 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (hm_n : 2 * m ≤ n)
    (hg : g < m / 2) {ht₀ : t₀ + m ≤ n}
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
    (hbudget : 2 * R + 7 * (m : ℝ) + 2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
      2 * γ * (m : ℝ) * Real.logb 2 U ≤
      ((m : ℝ) / 2) * Real.logb 2 V - (m : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)))
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (ctx : PoolCtx U V n t₀ m g P_size ht₀) :
    (((innerPoolDist (by omega) hV ctx.Fg ctx.hne).map fun sb =>
      decide (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2)) true).toReal ≤
      (U : ℝ) ^ (-γ * (m : ℝ)) := by
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
  let Ω := HardKeyValSeed U V n × Finset (Fin U)
  let μ_g : PMF Ω := innerPoolDist (by omega : 2 * n ≤ U) hV ctx.Fg ctx.hne
  let stride := modeStride withQueries
  let step₀ := n + stride * t₀
  let step_end := n + stride * (t₀ + m)
  let M_cap : ℝ := (2 : ℝ) ^ (R + 1) * (U : ℝ) ^ (γ * (m : ℝ))
  let K_cap : ℕ := Nat.floor M_cap
  have hU_pos_nat : 1 ≤ U := by omega
  have hU_pos : (0 : ℝ) < (U : ℝ) := by positivity
  by_contra hgt
  push Not at hgt
  -- Sub-condition on stateFiber.card ≤ M_cap using prob_gt_cap_stateFiber_le
  let W_cons (sb : Ω) : Bool :=
    decide (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2)
  let W_bad (sb : Ω) : Bool :=
    decide (M_cap < ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ))
  let W (sb : Ω) : Bool :=
    decide (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2 ∧
      ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ) ≤ M_cap)
  have hbad_le : ((μ_g.map W_bad) true).toReal ≤ (1 / 2) * (U : ℝ) ^ (-γ * (m : ℝ)) :=
    prob_gt_cap_stateFiber_le (by omega) hU_pos_nat hV hspace ctx D_det step_end
  have hunion : ((μ_g.map W_cons) true).toReal ≤
      ((μ_g.map W) true).toReal + ((μ_g.map W_bad) true).toReal := by
    rw [PMF.map_apply_toReal, PMF.map_apply_toReal, PMF.map_apply_toReal, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun sb _ => ?_
    dsimp only [W_cons, W, W_bad]
    by_cases hc : IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2 <;>
      by_cases hle : ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ) ≤ M_cap <;>
      simp [hc, hle, not_lt.2, lt_of_not_ge]
  have hpW_gt : (1 / 2) * (U : ℝ) ^ (-γ * (m : ℝ)) < ((μ_g.map W) true).toReal := by
    change (U : ℝ) ^ (-γ * (m : ℝ)) < ((μ_g.map W_cons) true).toReal at hgt; linarith
  have hpW_pos : 0 < ((μ_g.map W) true).toReal := lt_trans (by positivity) hpW_gt
  have hW0 : (μ_g.map W) true ≠ 0 := fun h0 => by
    simp only [h0, ENNReal.toReal_zero, lt_self_iff_false] at hpW_pos
  have hlog_pW : -γ * (m : ℝ) * Real.logb 2 U - 1 < Real.logb 2 (((μ_g.map W) true).toReal) := by
    have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hpW_gt
    rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hU_pos _).ne',
      show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.logb_inv,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Real.logb_rpow_eq_mul_logb_of_pos hU_pos] at hlog
    linarith
  let p : PMF Ω := PMF.conditionalSnd (μ_g.map fun sb => (W sb, sb)) true
  have hp_supp (sb : Ω) (hsb : sb ∈ p.support) :
      sb.2 ∈ ctx.Fg sb.1 ∧ IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2 ∧
        ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ) ≤ M_cap := by
    have hW_mem : true ∈ ((μ_g.map fun x => (W x, x)).map Prod.fst).support := by
      rw [_root_.PMF.map_comp]; exact (_root_.PMF.mem_support_iff _ _).mpr hW0
    have hp_ne : p sb ≠ 0 := (_root_.PMF.mem_support_iff p sb).mp hsb
    rw [PMF.conditionalSnd_apply _ _ hW_mem] at hp_ne
    have hmap_ne : (μ_g.map fun x => (W x, x)) (true, sb) ≠ 0 :=
      fun h0 => hp_ne (by simp only [h0, ENNReal.zero_div])
    obtain ⟨x, hx_supp, hx_eq⟩ := (_root_.PMF.mem_support_map_iff _ _ (true, sb)).mp
      ((_root_.PMF.mem_support_iff _ _).mpr hmap_ne)
    obtain ⟨hWx, hxsb⟩ := Prod.mk.inj hx_eq
    subst hxsb
    have hW_true := of_decide_eq_true hWx
    have hx_Fg : x.2 ∈ ctx.Fg x.1 := by
      have hμ_ne : μ_g x ≠ 0 := (_root_.PMF.mem_support_iff μ_g x).mp hx_supp
      by_contra hnFg
      have h0 : (μ_g x).toReal = 0 := by
        dsimp only [μ_g]; rw [toReal_innerPoolDist_apply, ite_eq_right hnFg]
      exact (ENNReal.toReal_pos hμ_ne (PMF.apply_ne_top μ_g x)).ne' h0
    exact ⟨hx_Fg, hW_true.1, hW_true.2⟩
  -- Define execution objects and 6-piece codeword on Ω
  let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  let C_bef (sb : Ω) := memAt D_det (sb.1.modeOps withQueries) step₀
  let ops_A (sb : Ω) := elemSlice n stride (sb.1.modeOps withQueries) t₀ (t₀ + m)
  let ops_B (sb : Ω) : List (Dynamic.Op U) :=
    if hB : sb.2.card = m then sb.1.modeCandidateOps withQueries t₀ m ht₀ sb.2 hB else []
  let S_A (sb : Ω) := D_det.probedCellsInterval step₀ (C_bef sb) (ops_A sb)
  let C_A (sb : Ω) := (D_det.runInterval step₀ (C_bef sb) (ops_A sb)).2
  let S_B (sb : Ω) := D_det.probedCellsInterval step₀ (C_bef sb) (ops_B sb)
  let C_B (sb : Ω) := (D_det.runInterval step₀ (C_bef sb) (ops_B sb)).2
  let C_mix (sb : Ω) := mixMem (C_bef sb) (C_A sb) (S_B sb)
  let SB_sim (sb : Ω) := D_det.probedCellsInterval step₀ (C_mix sb) (ops_B sb)
  let CB_sim (sb : Ω) := (D_det.runInterval step₀ (C_mix sb) (ops_B sb)).2
  let I_AB (sb : Ω) := S_A sb ∩ SB_sim sb
  let Δ_set (sb : Ω) := (I_AB sb).filter fun j => C_A sb j ≠ CB_sim sb j
  let dict_B (sb : Ω) := (pairBOf t₀ m ht₀ sb).val
  let m₁ (sb : Ω) := encodeRestr sb.2 sb.1.kv
  let m₂ (sb : Ω) := encodeFintype (C_mix sb)
  let m₃ (sb : Ω) := encodeRestr (SB_sim sb) (fun j => decide (j ∈ I_AB sb))
  let m₄ (sb : Ω) := encodeRestr (I_AB sb) (fun j => decide (j ∈ Δ_set sb))
  let m₅ (sb : Ω) := encodeRestr (Δ_set sb) (C_A sb)
  let m₆ (sb : Ω) := encodeMemFinset (stateFiber D_det step_end (dict_B sb)) K_cap (C_B sb)
  let msg (sb : Ω) := m₁ sb ++ (m₂ sb ++ (m₃ sb ++ (m₄ sb ++ (m₅ sb ++ m₆ sb))))
  -- Decoded state facts for any sb with sb.2 ∈ ctx.Fg sb.1
  have hstate (sb : Ω) (hFg_sb : sb.2 ∈ ctx.Fg sb.1) :
      let K := sb.1.activeKeys t₀ ht₀_n
      let D := Finset.univ.image (segDeletedKeys sb.1.keys sb.1.delPerm t₀ m ht₀)
      let A := sb.1.insertedSet t₀ m ht₀
      sb.2.card = m ∧ Disjoint sb.2 K ∧ Disjoint A K ∧
        decodeDict D_det step₀ (C_bef sb) =
          (fun u => if u ∈ K then some (sb.1.kv u).val else none) ∧
        decodeDict D_det step_end (C_A sb) =
          (fun u => if u ∈ (K \ D) ∪ A then some (sb.1.kv u).val else none) ∧
        C_B sb ∈ stateFiber D_det step_end (dict_B sb) := by
    dsimp only
    have hB_mp := Finset.mem_powersetCard.mp (Finset.mem_filter.mp (ctx.hFg sb.1 ▸ hFg_sb)).1
    have hB_card : sb.2.card = m := hB_mp.2
    have hdisj_B : Disjoint sb.2 (sb.1.activeKeys t₀ ht₀_n) :=
      (ctx.hdisj sb.1).mono_left hB_mp.1
    have hdisj_A : Disjoint (sb.1.insertedSet t₀ m ht₀) (sb.1.activeKeys t₀ ht₀_n) :=
      (ctx.hdisj sb.1).mono_left (ctx.hA sb.1)
    have hdec_bef : decodeDict D_det step₀ (C_bef sb) =
        fun u => if u ∈ sb.1.activeKeys t₀ ht₀_n then some (sb.1.kv u).val else none := by
      have hvh_b := sb.1.validHistory_take_modeOps withQueries ht₀_n
      have hlen_b := sb.1.length_take_modeOps withQueries ht₀_n
      have hle_b : ((sb.1.modeOps withQueries).take step₀).length ≤ modeHorizon withQueries n := by
        rw [hlen_b]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ht₀_n) n
      have hd := decodeDict_runSeq_eq hcorr hvh_b hle_b
      rw [hlen_b] at hd
      exact hd.trans (run_take_modeOps_eq_ite withQueries sb.1 ht₀_n)
    have hdec_A : decodeDict D_det step_end (C_A sb) =
        fun u => if u ∈ (sb.1.activeKeys t₀ ht₀_n \
            Finset.univ.image (segDeletedKeys sb.1.keys sb.1.delPerm t₀ m ht₀)) ∪
            sb.1.insertedSet t₀ m ht₀
          then some (sb.1.kv u).val else none := by
      have hopsA_cand : ops_A sb = sb.1.modeCandidateOps withQueries t₀ m ht₀
          (sb.1.insertedSet t₀ m ht₀) (card_insertedSet sb.1 ht₀) :=
        sb.1.elemSlice_modeOps_eq_trueCandidate withQueries ht₀
      dsimp only [C_A]; rw [hopsA_cand]
      exact decodeDict_modeCandidateOps_eq withQueries hcorr sb.1 ht₀ _ hdisj_A
    have hCB_mem : C_B sb ∈ stateFiber D_det step_end (dict_B sb) := by
      have hopsB_eq : ops_B sb = sb.1.modeCandidateOps withQueries t₀ m ht₀ sb.2 hB_card :=
        dite_eq_left hB_card
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      dsimp only [C_B, dict_B]
      rw [hopsB_eq, val_pairBOf_eq sb.1 ht₀ hB_card hdisj_B]
      exact decodeDict_modeCandidateOps_eq withQueries hcorr sb.1 ht₀ hB_card hdisj_B
    exact ⟨hB_card, hdisj_B, hdisj_A, hdec_bef, hdec_A, hCB_mem⟩
  -- Prefix-freeness and target8 injectivity on each obs8 fiber of p.support
  have hdecode (sb₁ : Ω) (hsb₁ : sb₁ ∈ p.support) (sb₂ : Ω) (hsb₂ : sb₂ ∈ p.support)
      (hobs : obs8 t₀ m ht₀ sb₁ = obs8 t₀ m ht₀ sb₂) (hpref : msg sb₁ <+: msg sb₂) :
      msg sb₁ = msg sb₂ ∧ target8 t₀ m ht₀ sb₁ = target8 t₀ m ht₀ sb₂ := by
    obtain ⟨hFg₁, _, hcap₁⟩ := hp_supp sb₁ hsb₁
    obtain ⟨hFg₂, _, hcap₂⟩ := hp_supp sb₂ hsb₂
    obtain ⟨hBc₁, hdisjB₁, hdisjA₁, hdec_bef₁, hdec_A₁, hCB_mem₁⟩ := hstate sb₁ hFg₁
    obtain ⟨hBc₂, hdisjB₂, hdisjA₂, hdec_bef₂, hdec_A₂, hCB_mem₂⟩ := hstate sb₂ hFg₂
    obtain ⟨ha, hobs_rest⟩ := Prod.mk.inj hobs
    obtain ⟨hB, hd⟩ := Prod.mk.inj hobs_rest
    have hA_eq : sb₁.1.insertedSet t₀ m ht₀ = sb₂.1.insertedSet t₀ m ht₀ := by
      dsimp only [HardKeyValSeed.insertedSet]
      rw [Function.Embedding.ext (congrFun ha)]
    obtain ⟨hm₁, hp2⟩ := prefix_append_of_length_eq
      (by simp only [m₁, length_encodeRestr, hB]) hpref
    have hkvB : ∀ x ∈ sb₁.2, sb₁.1.kv x = sb₂.1.kv x := encodeRestr_inj hB hm₁
    have hopsB : ops_B sb₁ = ops_B sb₂ := by
      dsimp only [ops_B]; rw [dite_eq_left hBc₁, dite_eq_left hBc₂]
      exact modeCandidateOps_congr withQueries ht₀ hBc₁ hBc₂ ha hB hd hkvB
    obtain ⟨hm₂, hp3⟩ := prefix_append_of_length_eq
      (by simp only [m₂, length_encodeFintype]) hp2
    have hcm : C_mix sb₁ = C_mix sb₂ := encodeFintype_injective hm₂
    have hSB_sim : SB_sim sb₁ = SB_sim sb₂ := by dsimp only [SB_sim]; rw [hcm, hopsB]
    have hSB_eq (sb : Ω) : SB_sim sb = S_B sb :=
      (runInterval_mixMem_eq_of_probedCellsInterval_subset D_det step₀ (C_bef sb) (C_A sb)
        (S_B sb) (ops_B sb) subset_rfl).2.2.1
    have hSB : S_B sb₁ = S_B sb₂ := (hSB_eq sb₁).symm.trans (hSB_sim.trans (hSB_eq sb₂))
    obtain ⟨hm₃, hp4⟩ := prefix_append_of_length_eq
      (by simp only [m₃, length_encodeRestr, hSB_sim]) hp3
    have hI_AB : I_AB sb₁ = I_AB sb₂ :=
      encodeRestr_subset_inj Finset.inter_subset_right Finset.inter_subset_right hSB_sim hm₃
    obtain ⟨hm₄, hp5⟩ := prefix_append_of_length_eq
      (by simp only [m₄, length_encodeRestr, hI_AB]) hp4
    have hΔ : Δ_set sb₁ = Δ_set sb₂ :=
      encodeRestr_subset_inj (Finset.filter_subset _ _) (Finset.filter_subset _ _) hI_AB hm₄
    obtain ⟨hm₅, hp6⟩ := prefix_append_of_length_eq
      (by simp only [m₅, length_encodeRestr, hΔ]) hp5
    have hm₆ : m₆ sb₁ = m₆ sb₂ := (prefix_append_of_length_eq (v₁ := []) (v₂ := [])
      (by simp only [m₆, length_encodeMemFinset]) (by simpa only [List.append_nil] using hp6)).1
    have hCA : C_A sb₁ = C_A sb₂ := by
      funext j
      by_cases hjΔ : j ∈ Δ_set sb₁
      · exact encodeRestr_inj hΔ hm₅ j hjΔ
      · by_cases hjI : j ∈ I_AB sb₁
        · have hj₁ : C_A sb₁ j = CB_sim sb₁ j :=
            of_not_not fun hne => hjΔ (Finset.mem_filter.mpr ⟨hjI, hne⟩)
          have hj₂ : C_A sb₂ j = CB_sim sb₂ j :=
            of_not_not fun hne => (hΔ ▸ hjΔ) (Finset.mem_filter.mpr ⟨hI_AB ▸ hjI, hne⟩)
          dsimp only [CB_sim] at hj₁ hj₂
          rw [hj₁, hj₂, hcm, hopsB]
        · have hrec (sb : Ω) (hnot : j ∉ I_AB sb) : C_A sb j = C_mix sb j :=
            (mixMem_eq_postMem_of_notMem_inter D_det step₀ (C_bef sb) (ops_A sb)
              (S_B sb) (S_B sb) Finset.inter_subset_left
              (by dsimp only [I_AB] at hnot; rwa [hSB_eq sb] at hnot)).symm
          rw [hrec sb₁ hjI, hrec sb₂ (hI_AB ▸ hjI), hcm]
    -- Recover K \ D and kv on (K \ D) ∪ A from C_A
    let KD₁ := sb₁.1.activeKeys t₀ ht₀_n \
      Finset.univ.image (segDeletedKeys sb₁.1.keys sb₁.1.delPerm t₀ m ht₀)
    let KD₂ := sb₂.1.activeKeys t₀ ht₀_n \
      Finset.univ.image (segDeletedKeys sb₂.1.keys sb₂.1.delPerm t₀ m ht₀)
    have hdecA_eq := congrArg (decodeDict D_det step_end) hCA
    rw [hdec_A₁, hdec_A₂] at hdecA_eq
    obtain ⟨hKDA_eq, hkv_KDA_val⟩ := dom_eq_of_ite_some_eq hdecA_eq
    have hKD_eq : KD₁ = KD₂ := by
      dsimp only [KD₁, KD₂]
      rw [← Finset.union_sdiff_cancel_right
            (Finset.disjoint_of_subset_left Finset.sdiff_subset hdisjA₁.symm),
          ← Finset.union_sdiff_cancel_right
            (Finset.disjoint_of_subset_left Finset.sdiff_subset hdisjA₂.symm),
          hKDA_eq, hA_eq]
    have hkv_KDA (u : Fin U) (hu : u ∈ KD₁ ∪ sb₁.1.insertedSet t₀ m ht₀) :
        sb₁.1.kv u = sb₂.1.kv u := Fin.ext (hkv_KDA_val u hu)
    -- Recover dict_B, C_B, and C_bef
    have hdictB : dict_B sb₁ = dict_B sb₂ := by
      dsimp only [dict_B]
      rw [val_pairBOf_eq sb₁.1 ht₀ hBc₁ hdisjB₁, val_pairBOf_eq sb₂.1 ht₀ hBc₂ hdisjB₂]
      refine ite_mem_congr none (congrArg₂ (· ∪ ·) hKD_eq hB) fun u hu => ?_
      rcases Finset.mem_union.mp hu with huKD | huB
      · rw [hkv_KDA u (Finset.mem_union_left _ huKD)]
      · rw [hkvB u huB]
    have hCB : C_B sb₁ = C_B sb₂ :=
      encodeMemFinset_inj hCB_mem₁ (hdictB ▸ hCB_mem₂) (Nat.le_floor hcap₁)
        (by simpa only [m₆, hdictB] using hm₆)
    have hCbef : C_bef sb₁ = C_bef sb₂ := funext fun j => by
      by_cases hj : j ∈ S_B sb₁
      · exact (mixMem_of_mem hj : C_mix sb₁ j = C_bef sb₁ j).symm.trans
          ((congrFun hcm j).trans (mixMem_of_mem (hSB ▸ hj) : C_mix sb₂ j = C_bef sb₂ j))
      · have hj₂ : j ∉ D_det.probedCellsInterval step₀ (C_bef sb₂) (ops_B sb₂) := by
          rwa [show D_det.probedCellsInterval step₀ (C_bef sb₂) (ops_B sb₂) = S_B sb₂ from rfl,
            ← hSB]
        exact (D_det.nextMem_runInterval_eq_of_notMem_probedCellsInterval step₀ (C_bef sb₁)
          (ops_B sb₁) hj).symm.trans ((congrFun hCB j).trans
            (D_det.nextMem_runInterval_eq_of_notMem_probedCellsInterval step₀ (C_bef sb₂)
              (ops_B sb₂) hj₂))
    have hdec_bef_eq := congrArg (decodeDict D_det step₀) hCbef
    rw [hdec_bef₁, hdec_bef₂] at hdec_bef_eq
    obtain ⟨hK_eq, hkv_K_val⟩ := dom_eq_of_ite_some_eq hdec_bef_eq
    refine ⟨by simp only [msg, hm₁, hm₂, hm₃, hm₄, hm₅, hm₆], Prod.ext hKD_eq ?_⟩
    dsimp only [target8]
    refine ite_mem_congr _
      (congrArg₂ (· ∪ ·) (congrArg₂ (· ∪ ·) hK_eq hA_eq) hB) fun u hu => ?_
    rcases Finset.mem_union.mp hu with huKA | huB
    · rcases Finset.mem_union.mp huKA with huK | huA
      · rw [Fin.ext (hkv_K_val u huK)]
      · rw [hkv_KDA u (Finset.mem_union_right _ huA)]
    · rw [hkvB u huB]
  -- Prefix-free entropy compression vs conditioned fiber entropy lower bound
  let joint_ot := p.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)
  have hcomp_bound : PMF.conditionalEntropy joint_ot ≤
      ∑ sb : Ω, (p sb).toReal * ((msg sb).length : ℝ) :=
    conditionalEntropy_map_le_expected_length_of_isPrefixFree p (obs8 t₀ m ht₀) (target8 t₀ m ht₀)
      msg (fun _ _ ⟨sb₁, ⟨h₁, ho₁⟩, hy₁⟩ _ ⟨sb₂, ⟨h₂, ho₂⟩, hy₂⟩ hp => by
        subst hy₁; subst hy₂; exact (hdecode sb₁ h₁ sb₂ h₂ (ho₁.trans ho₂.symm) hp).1)
      (fun sb₁ h₁ sb₂ h₂ hobs heq =>
        (hdecode sb₁ h₁ sb₂ h₂ hobs ⟨[], by simpa only [List.append_nil] using heq⟩).2)
  let M_nat := (U - 3 * m).choose (n - m) * V ^ (n + 2 * m - g)
  have hM_pos : (0 : ℝ) < (M_nat : ℝ) := by
    dsimp only [M_nat]; exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.pow_pos hV)
  have hent_lo : Real.logb 2 (((μ_g.map W) true).toReal) + Real.logb 2 (M_nat : ℝ) ≤
      PMF.conditionalEntropy joint_ot :=
    logb_prob_add_logb_le_conditionalEntropy_of_fiber_le μ_g W (obs8 t₀ m ht₀) (target8 t₀ m ht₀)
      hM_pos hW0 (fiber_le_queryFreePoolDist hU hV hm_n hg ctx)
  -- Lower bound Real.logb 2 M_nat
  have hlog_M : benchmarkBits U V n + (3 / 2) * (m : ℝ) * Real.logb 2 V -
      (m : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)) - 5 * (m : ℝ) ≤ Real.logb 2 (M_nat : ℝ) := by
    have hc_pos : (0 : ℝ) < ((U - 3 * m).choose (n - m) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hv_pos : (0 : ℝ) < ((V ^ (n + 2 * m - g) : ℕ) : ℝ) := by exact_mod_cast Nat.pow_pos hV
    have hM_split : Real.logb 2 (M_nat : ℝ) =
        Real.logb 2 ((U - 3 * m).choose (n - m)) + ((n + 2 * m - g : ℕ) : ℝ) * Real.logb 2 V := by
      dsimp only [M_nat]
      rw [Nat.cast_mul, Real.logb_mul hc_pos.ne' hv_pos.ne', Nat.cast_pow, Real.logb_pow]
    have hchoose_gap := logb_choose_sub_logb_sub_three_mul_choose_sub_le hU
      (by omega : 1 ≤ m) (by omega : m ≤ n)
    have hexp_ge : (n : ℝ) + (3 / 2) * (m : ℝ) ≤ ((n + 2 * m - g : ℕ) : ℝ) := by
      have : 2 * (g : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 * g ≤ m)
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      linarith
    have hlogV_nn : 0 ≤ Real.logb 2 V := Real.logb_nonneg (by norm_num) (by exact_mod_cast hV)
    have hv_gap := mul_le_mul_of_nonneg_right hexp_ge hlogV_nn
    rw [hM_split, benchmarkBits_eq]
    linarith
  -- Pointwise length bound on p.support
  have hlen_pt (sb : Ω) (hsb : sb ∈ p.support) :
      ((msg sb).length : ℝ) ≤ benchmarkBits U V n + (m : ℝ) * Real.logb 2 V + 2 * R +
        2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) + γ * (m : ℝ) * Real.logb 2 U + 3 := by
    obtain ⟨hFg_sb, hcons, hcap⟩ := hp_supp sb hsb
    obtain ⟨hBc, _, _, _, _, hCB_mem⟩ := hstate sb hFg_sb
    obtain ⟨hBc', hΔ_le_raw, _, hSB_le_raw⟩ := hcons
    have hopsB_eq : ops_B sb = sb.1.modeCandidateOps withQueries t₀ m ht₀ sb.2 hBc' :=
      dite_eq_left hBc'
    obtain ⟨_, _, hSB_eq, hCB_on⟩ := runInterval_mixMem_eq_of_probedCellsInterval_subset D_det
      step₀ (C_bef sb) (C_A sb) (S_B sb) (ops_B sb) subset_rfl
    have hSB_cap : ((S_B sb).card : ℝ) ≤ (m : ℝ) * t := by
      dsimp only [S_B]; rw [hopsB_eq]; exact hSB_le_raw
    have hΔ_cap : ((Δ_set sb).card : ℝ) ≤ γ * (m : ℝ) := by
      have heq_set : Δ_set sb = (S_A sb ∩ S_B sb).filter fun j => C_A sb j ≠ C_B sb j := by
        dsimp only [Δ_set, I_AB, SB_sim, CB_sim, C_mix]
        rw [hSB_eq]
        exact Finset.filter_congr fun j hj => by rw [hCB_on j (Finset.inter_subset_right hj)]
      rw [heq_set]; dsimp only [S_A, S_B, C_A, C_B]; simp only [hopsB_eq]; exact hΔ_le_raw
    have hm1 : ((m₁ sb).length : ℝ) ≤ (m : ℝ) * Real.logb 2 V + 1 := by
      dsimp only [m₁]; rw [length_encodeRestr, Fintype.card_fin, hBc]
      refine (clog_two_lt_logb_add_one (pow_pos (by omega : 0 < V) m)).le.trans ?_
      rw [Nat.cast_pow, Real.logb_pow]
    have hm2 : ((m₂ sb).length : ℝ) ≤ benchmarkBits U V n + R := by
      dsimp only [m₂]
      rw [length_encodeFintype, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        ← pow_mul, Nat.clog_pow _ _ (by norm_num), mul_comm]
      exact hspace
    have hm3 : ((m₃ sb).length : ℝ) ≤ (m : ℝ) * t := by
      simpa only [m₃, SB_sim, C_mix, length_encodeRestr_bool, hSB_eq] using hSB_cap
    have hm4 : ((m₄ sb).length : ℝ) ≤ (m : ℝ) * t := by
      simpa only [m₄, I_AB, SB_sim, C_mix, length_encodeRestr_bool, hSB_eq] using
        (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)).trans hSB_cap
    have hm5 : ((m₅ sb).length : ℝ) ≤ γ * (m : ℝ) * (w : ℝ) := by
      dsimp only [m₅]; rw [length_encodeRestr_fin_two_pow, Nat.cast_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hΔ_cap (Nat.cast_nonneg w)
    have hm6 : ((m₆ sb).length : ℝ) ≤ R + 2 + γ * (m : ℝ) * Real.logb 2 U := by
      dsimp only [m₆]; rw [length_encodeMemFinset]
      have hfib_pos : 1 ≤ (stateFiber D_det step_end (dict_B sb)).card :=
        Finset.card_pos.mpr ⟨C_B sb, hCB_mem⟩
      have hK_pos : 1 ≤ K_cap := hfib_pos.trans (Nat.le_floor hcap)
      have hclog := (clog_two_lt_logb_add_one hK_pos).le
      have hK_le_M : (K_cap : ℝ) ≤ M_cap := Nat.floor_le (by dsimp only [M_cap]; positivity)
      have hlogK : Real.logb 2 (K_cap : ℝ) ≤ R + 1 + γ * (m : ℝ) * Real.logb 2 U := by
        refine (Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hK_pos)
          hK_le_M).trans_eq ?_
        dsimp only [M_cap]
        rw [Real.logb_mul (by positivity) (by positivity),
          Real.logb_rpow (by norm_num) (by norm_num),
          Real.logb_rpow_eq_mul_logb_of_pos hU_pos]
      linarith
    simp only [msg, List.length_append, Nat.cast_add]; linarith
  set C_upper := benchmarkBits U V n + (m : ℝ) * Real.logb 2 V + 2 * R +
    2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) + γ * (m : ℝ) * Real.logb 2 U + 3
  have hexp_msg : (∑ sb : Ω, (p sb).toReal * ((msg sb).length : ℝ)) ≤ C_upper := by
    refine (Finset.sum_le_sum fun sb _ => ?_).trans_eq
      (by rw [← Finset.sum_mul, PMF.sum_toReal p, one_mul] : ∑ sb, (p sb).toReal * C_upper = _)
    by_cases hsb : sb ∈ p.support
    · exact mul_le_mul_of_nonneg_left (hlen_pt sb hsb) ENNReal.toReal_nonneg
    · simp [(_root_.PMF.apply_eq_zero_iff p sb).2 hsb]
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  dsimp only [C_upper] at hexp_msg
  linarith

end Cslib.DataStructure.Dictionary.CellProbe
