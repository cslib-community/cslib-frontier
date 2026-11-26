/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.QueryInsert
-- Reads private `compDispatch_spec` and unfolds `compFeistelCoordsProg`.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
-- Reads private `QueryInsert` effect lemmas and unfolds `compQueryWithHashGenProg` and insert ops.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.QueryInsert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Dictionary-Level Lookup and Split Insertion Specifications (`DictStateInv`)

Establishes `DictStateInv`, `FixedCoupled`, and amortized `memoryCost` bounds for compacted lookup
(`compQueryWithHashGenProg_dict_spec`) and two-phase split insertion
(`compInsertSearchWithHashGenProg_dict_spec`, `compInsertHit_dict_spec`,
`compInsertMiss_dict_spec`).

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compQueryWithHashGenProg_dict_spec`:
  dictionary-level lookup correctness and `O(1 + probeExcess)` `memoryCost` bound.
* `compInsertSearchWithHashGenProg_dict_spec`, `compInsertHit_dict_spec`,
  `compInsertMiss_dict_spec`:
  dictionary-level Phase 1 search, hit update, and miss append specifications.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure StateTransitionSpec.clientResult_map
  StateTransitionSpec.fst_snd_runClient_map
attribute [local simp] Realization.memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-- Dictionary-level specification of `compQueryWithHashGenProg`: establishes
`CompQueryWithHashPre`, leaves `s` unchanged, returns `s_abs u`, and bounds `memoryCost` by
`38 + 12 * probeExcess`. -/
theorem compQueryWithHashGenProg_dict_spec {metaBase itemBase U V w N m_items : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hfit_off : Fits w (metaBase + offCompItems U w N))
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_items : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (u : Fin U) :
    let q := keyQuotient (bucketBits N) u.val
    let h_q := hValOfSeed U N θ q
    let d := ((mkCompParams U V w N, (metaBase, itemBase)), (u.val, h_q))
    let prog := compQueryWithHashGenProg d
    CompQueryWithHashPre w d s ∧
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = s_abs u ∧
    memoryCost prog s ≤
      38 + 12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
  intro q h_q d prog
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  set b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
  set m := mOfSeed U N θ q
  obtain ⟨hb_eq, hq_eq, hm_eq, hb_lt, hm_lt, hslot, hpre⟩ :=
    compDispatch_spec henv hfit_off hinv hcpl hm_items u
  have hwf := ghostDictParamsWf henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hg_env := ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hfix_spec := queryWithHashProg_dict_spec (w := ghostW w) hwf hg_env θ hinv u
  have hchain : IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) (L b m) := by
    rw [hcpl.lm_eq]; exact hb_inv.hchains.1 b hb_lt m hm_lt
  have hc_lt : ∀ j ∈ L b m, j < bCount N (compGmAt metaBase U w N s.mem) b := fun j hj => by
    rw [hcpl.gm_eq]; exact ((hb_inv.hchain_mem b hb_lt m hm_lt j).mp hj).1
  obtain ⟨hst_qb, hres_qb, hcost_qb⟩ := compQueryBodyGenProg_spec (q_target := q)
    henv hcpl hslot hm_items hb_lt hm_lt hchain hc_lt
  obtain ⟨hlen_pr, hovf_pr, _⟩ := chain_and_overflow_le_probeExcess θ hb_inv u
  have hprog_eq : prog =
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q)) >>= fun c =>
        compQueryBodyGenProg (((mkCompParams U V w N, (metaBase, itemBase)), c.1), c.2)) := rfl
  have hc_res : (Memory.spec 0).clientResult s
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q))) = ((b, q), m) :=
    clientResult_compFeistelCoordsProg U V w N u.val h_q s
  have hfix_eq : (Memory.spec 0).clientResult s_fix
      (queryWithHashProg U V (ghostW w) N ((0, u.val), h_q)) =
      (Memory.spec 0).clientResult s_fix
        (queryBodyProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m)) := by
    unfold queryWithHashProg queryWithHashGenProg
    simp only [p_bucketBits_mk, p_bucketMask_mk, queryBodyGenProg_mk, pure_bind]
    rw [and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q,
      Nat.shiftRight_eq_div_pow u.val (bucketBits N)]
    rfl
  refine ⟨hpre, ?_, ?_, ?_⟩
  · rw [hprog_eq, StateTransitionSpec.clientState_bind, clientState_compFeistelCoordsProg, hc_res]
    exact hst_qb
  · rw [hprog_eq, StateTransitionSpec.clientResult_bind, clientState_compFeistelCoordsProg,
      hc_res, hres_qb, ← hfix_eq]
    exact hfix_spec.2.2.1
  · rw [hprog_eq, memoryCost_bind_of_clientState_eq (clientState_compFeistelCoordsProg _ s) _,
      memoryCost_compFeistelCoordsProg, hc_res, zero_add]
    rw [hcpl.gm_eq, show epochHashSpace U (ghostW w) N = hashSpace U (ghostW w) N from rfl]
      at hcost_qb
    dsimp only [b, q, m] at hcost_qb hlen_pr hovf_pr ⊢
    unfold probeExcess
    omega

/-- Dictionary-level specification of Phase 1 (`compInsertSearchWithHashGenProg`) of split
compacted insertion. -/
theorem compInsertSearchWithHashGenProg_dict_spec {metaBase itemBase U V w N m_items : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hfit_off : Fits w (metaBase + offCompItems U w N))
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_items : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (u : Fin U) :
    let q := keyQuotient (bucketBits N) u.val
    let h_q := hValOfSeed U N θ q
    let b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
    let m := mOfSeed U N θ q
    let d := ((mkCompParams U V w N, (metaBase, itemBase)), (u.val, h_q))
    let prog := compInsertSearchWithHashGenProg d
    let res_sb := (Memory.spec 0).clientResult s_fix
      (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m))
    CompQueryWithHashPre w d s ∧
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = ((sbFound res_sb, res_sb.2), (b, m)) ∧
    (sbFound res_sb = 1 ↔ (s_abs u).isSome) ∧
    (sbFound res_sb = 1 →
      ∃ j < bCount N (compGmAt metaBase U w N s.mem) b,
        res_sb.2 = slotOf N (compGmAt metaBase U w N s.mem) b j) ∧
    memoryCost prog s ≤
      32 + 12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
  intro q h_q b m d prog res_sb
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  obtain ⟨hb_eq, hq_eq, hm_eq, hb_lt, hm_lt, hslot, hpre⟩ :=
    compDispatch_spec henv hfit_off hinv hcpl hm_items u
  have hg_env := ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hchain : IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) (L b m) := by
    rw [hcpl.lm_eq]; exact hb_inv.hchains.1 b hb_lt m hm_lt
  have hc_lt : ∀ j ∈ L b m, j < bCount N (compGmAt metaBase U w N s.mem) b := fun j hj => by
    rw [hcpl.gm_eq]; exact ((hb_inv.hchain_mem b hb_lt m hm_lt j).mp hj).1
  obtain ⟨hst_sb, hres_sb, hcost_sb⟩ := compSearchBucketGenProg_spec (q_target := q)
    henv hcpl hslot hm_items hb_lt hm_lt hchain hc_lt
  have hsb_fix := searchBucketProg_bucket_spec hb_inv hg_env hb_lt (q_target := q) (m := m)
    rfl hm_lt
  dsimp only at hsb_fix
  have hres_branch := hsb_fix.2.2
  have hbm := bucketMapOfState_feistelBucket henv.le_U (hValOfSeed U N θ) s_abs u
  have hc_res : (Memory.spec 0).clientResult s
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q))) = ((b, q), m) :=
    clientResult_compFeistelCoordsProg U V w N u.val h_q s
  obtain ⟨hlen_pr, hovf_pr, _⟩ := chain_and_overflow_le_probeExcess θ hb_inv u
  have hprog_eq : prog =
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q)) >>= fun c =>
        compSearchBucketGenProg (((mkCompParams U V w N, (metaBase, itemBase)), c.1), c.2) >>=
          fun res => compPackInsertSearchResProg (res, c)) := rfl
  have hhit : (sbFound res_sb = 1 ↔ (s_abs u).isSome) ∧
      (sbFound res_sb = 1 →
        ∃ j < bCount N (compGmAt metaBase U w N s.mem) b,
          res_sb.2 = slotOf N (compGmAt metaBase U w N s.mem) b j) := by
    by_cases hex : ∃ j < bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b,
        quotAt 0 U (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem
          (slotOf N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b j) = q
    · rw [ite_eq_left hex] at hres_branch
      rw [← hbm, hcpl.gm_eq]
      exact ⟨⟨fun _ => (hb_inv.hmap_dom b hb_lt q).mpr hex, fun _ => hres_branch.1⟩,
        fun _ => ⟨res_sb.1.2, hres_branch.2.1, hres_branch.2.2.2⟩⟩
    · rw [ite_eq_right hex] at hres_branch
      change sbFound res_sb = 0 at hres_branch
      exact ⟨⟨by omega, fun hs => (hex ((hb_inv.hmap_dom b hb_lt q).mp (hbm ▸ hs))).elim⟩,
        by omega⟩
  refine ⟨hpre, ?_, ?_, hhit.1, hhit.2, ?_⟩
  · rw [hprog_eq, StateTransitionSpec.clientState_bind, clientState_compFeistelCoordsProg, hc_res,
      StateTransitionSpec.clientState_bind, hst_sb, clientState_compPackInsertSearchResProg]
  · rw [hprog_eq, StateTransitionSpec.clientResult_bind, clientState_compFeistelCoordsProg, hc_res,
      StateTransitionSpec.clientResult_bind, hst_sb, hres_sb,
      clientResult_compPackInsertSearchResProg]
  · rw [hprog_eq, memoryCost_bind_of_clientState_eq (clientState_compFeistelCoordsProg _ s) _,
      memoryCost_compFeistelCoordsProg, hc_res, zero_add,
      memoryCost_bind_of_clientState_eq hst_sb _, memoryCost_compPackInsertSearchResProg, add_zero]
    rw [hcpl.gm_eq, show epochHashSpace U (ghostW w) N = hashSpace U (ghostW w) N from rfl]
      at hcost_sb
    dsimp only [b, q, m] at hcost_sb hlen_pr hovf_pr ⊢
    unfold probeExcess
    omega

private theorem insertWithHashProg_clientState_hit (U V w₀ n_max u v h_q : ℕ)
    (s_fix : Memory.State)
    (b q m : ℕ)
    (hb_eq : (h_q &&& (2 ^ bucketBits n_max - 1)) ^^^ (u &&& (2 ^ bucketBits n_max - 1)) = b)
    (hq_eq : u >>> bucketBits n_max = q)
    (hm_eq : h_q >>> bucketBits n_max = m)
    (res_sb : (ℕ × ℕ) × ℕ)
    (hres : (Memory.spec 0).clientResult s_fix
      (searchBucketProg U V w₀ n_max (hashSpace U w₀ n_max) (((0, b), q), m)) = res_sb)
    (hst : (Memory.spec 0).clientState s_fix
      (searchBucketProg U V w₀ n_max (hashSpace U w₀ n_max) (((0, b), q), m)) = s_fix)
    (hfound : res_sb.1.1 = 1) :
    (Memory.spec 0).clientState s_fix (insertWithHashProg U V w₀ n_max (((0, u), v), h_q)) =
      (Memory.spec 0).clientState s_fix
        (writeValProg U V w₀ n_max (hashSpace U w₀ n_max) ((0, res_sb.2), v)) := by
  unfold insertWithHashProg insertWithHashGenProg
  simp only [p_bucketBits_mk, p_bucketMask_mk, insertBodyGenProg_mk, pure_bind]
  rw [hb_eq, hq_eq, hm_eq]
  unfold insertBodyProg insertBodyGenProg
  simp only [searchBucketGenProg_mk, writeValGenProg_mk, insertNewGenProg_mk, pure_bind]
  rw [StateTransitionSpec.clientState_bind, hst, hres, ite_eq_left hfound]

private theorem insertWithHashProg_clientState_miss (U V w₀ n_max u v h_q : ℕ)
    (s_fix : Memory.State) (b q m : ℕ)
    (hb_eq : (h_q &&& (2 ^ bucketBits n_max - 1)) ^^^ (u &&& (2 ^ bucketBits n_max - 1)) = b)
    (hq_eq : u >>> bucketBits n_max = q)
    (hm_eq : h_q >>> bucketBits n_max = m)
    (hst : (Memory.spec 0).clientState s_fix
      (searchBucketProg U V w₀ n_max (hashSpace U w₀ n_max) (((0, b), q), m)) = s_fix)
    (hmiss : ((Memory.spec 0).clientResult s_fix
      (searchBucketProg U V w₀ n_max (hashSpace U w₀ n_max) (((0, b), q), m))).1.1 ≠ 1)
    (htot : totalSlots n_max (gmAt 0 U V w₀ n_max (hashSpace U w₀ n_max) s_fix.mem) < n_max)
    (hb : b < numBuckets n_max) :
    (Memory.spec 0).clientState s_fix (insertWithHashProg U V w₀ n_max (((0, u), v), h_q)) =
      (Memory.spec 0).clientState
        ((Memory.spec 0).clientState s_fix
          (pushBackSlotProg U V w₀ n_max (hashSpace U w₀ n_max) (((0, b), q), v)))
        (prependIfIndexedProg U V w₀ n_max (hashSpace U w₀ n_max)
          (((0, b), m),
            bCount n_max (gmAt 0 U V w₀ n_max (hashSpace U w₀ n_max) s_fix.mem) b)) := by
  unfold insertWithHashProg insertWithHashGenProg
  simp only [p_bucketBits_mk, p_bucketMask_mk, insertBodyGenProg_mk, pure_bind]
  rw [hb_eq, hq_eq, hm_eq]
  unfold insertBodyProg insertBodyGenProg
  simp only [searchBucketGenProg_mk, writeValGenProg_mk, insertNewGenProg_mk, pure_bind]
  rw [StateTransitionSpec.clientState_bind, hst, ite_eq_right hmiss]
  unfold insertNewProg insertNewGenProg
  simp only [readTotalSlotsGenProg_mk, p_nMax_mk, readBucketCountGenProg_mk,
    pushBackSlotGenProg_mk, prependIfIndexedGenProg_mk, pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_readTotalSlotsProg,
    clientResult_readTotalSlotsProg, ite_eq_left htot,
    StateTransitionSpec.clientState_bind, clientState_readBucketCountProg,
    clientResult_readBucketCountProg (0, b) s_fix hb,
    StateTransitionSpec.clientState_bind]

/-- Dictionary-level specification of Phase 2a (hit path: `found = 1`) of split compacted
insertion (`compWritePhysValGenProg`). -/
theorem compInsertHit_dict_spec {metaBase itemBase U V w N m_items : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hfit_off : Fits w (metaBase + offCompItems U w N))
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_items : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (u : Fin U) (v : ℕ) (hv : v < V)
    (hfound : sbFound ((Memory.spec 0).clientResult s_fix
      (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val),
          keyQuotient (bucketBits N) u.val),
          mOfSeed U N θ (keyQuotient (bucketBits N) u.val)))) = 1) :
    let q := keyQuotient (bucketBits N) u.val
    let b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
    let m := mOfSeed U N θ q
    let res_sb := (Memory.spec 0).clientResult s_fix
      (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m))
    let d_wv := (((mkCompParams U V w N, (metaBase, itemBase)), res_sb.2), v)
    let s' := (Memory.spec 0).clientState s (compWritePhysValGenProg d_wv)
    CompWritePhysValPre w d_wv s ∧
    CompOpFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem ∧
    memoryCost (compWritePhysValGenProg d_wv) s ≤ 8 ∧
    ∃ s_fix' : Memory.State,
      DictStateInv U V (ghostW w) N 0 θ (Function.update s_abs u (some v)) s_fix' ∧
      FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro q b m res_sb d_wv s'
  set h_q := hValOfSeed U N θ q
  have hsrch := compInsertSearchWithHashGenProg_dict_spec henv hfit_off hinv hcpl hm_items u
  obtain ⟨_, _, _, hf_iff, hf_slot, _⟩ := hsrch
  have hsome : (s_abs u).isSome := hf_iff.mp hfound
  obtain ⟨j_hit, hj_bc, hphys_eq⟩ := hf_slot hfound
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) (hValOfSeed U N θ) u.val
  have hm_lt : m < numMicroPerBucket N := mOfSeed_lt U N θ q
  have hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem) := by
    rw [hcpl.gm_eq]; exact hb_inv.hslot
  have hv_lt : v < 2 ^ valBits V := hv.trans_le (Nat.le_pow_clog (by decide) V)
  have hwf := ghostDictParamsWf henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hg_env := ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hins_fix := insertWithHashProg_dict_spec (w := ghostW w) hwf hg_env θ hinv u v
    ⟨Or.inr hsome, hv⟩
  set s_fix' := (Memory.spec 0).clientState s_fix
    (insertWithHashProg U V (ghostW w) N (((0, u.val), v), h_q))
  have hst_sb_fix :
      (Memory.spec 0).clientState s_fix
        (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m)) =
        s_fix :=
    (searchBucketProg_bucket_spec hb_inv hg_env hb_lt (q_target := q) (m := m) rfl hm_lt).1
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState s_fix
      (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, res_sb.2), v)) :=
    insertWithHashProg_clientState_hit U V (ghostW w) N u.val v h_q s_fix b q m
      (and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q)
      (Nat.shiftRight_eq_div_pow u.val (bucketBits N)) rfl res_sb rfl hst_sb_fix hfound
  obtain ⟨hfr_wv, hcpl_wv⟩ :=
    compWritePhysValGenProg_effect henv hcpl hslot hm_items hb_lt hj_bc hv_lt
  have hphys_lt : slotOf N (compGmAt metaBase U w N s.mem) b j_hit < N :=
    (slotOf_lt_and_injective hslot).1 b hb_lt j_hit hj_bc
  have eff_wv_fix := writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) hwf.1 hphys_lt hv_lt s_fix
  have hgm'_eq : compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem := by
    dsimp only [s', d_wv]
    rw [hphys_eq]
    exact hcpl_wv.gm_eq.trans (eff_wv_fix.2.2.2.2.2.trans hcpl.gm_eq.symm)
  refine ⟨⟨U, V, N, m_items, s_fix, b, j_hit, rfl, henv, hcpl, hslot, hm_items,
      hb_lt, hj_bc, hphys_eq⟩,
    ?_, hgm'_eq, memoryCost_compWritePhysValGenProg_le _ s, s_fix', hins_fix.2.2.2.1, ?_⟩
  · dsimp only [s', d_wv]; rw [hphys_eq]; exact hfr_wv
  · dsimp only [s', d_wv]; rw [hs_fix'_eq, hphys_eq]; exact hcpl_wv

/-- Dictionary-level specification of Phase 2b (miss path: `found ≠ 1`, executed after
`growZeroCode` extends `s` to `s_grown` with `s_grown.mem = s.mem` and `n + 1 ≤ m_cap`) of split
compacted insertion (`compInsertAppendNewGenProg`). -/
theorem compInsertMiss_dict_spec {metaBase itemBase U V w N m_cap : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s s_grown : Memory.State}
    (henv_grown : CompEpochEnv U V w N metaBase itemBase m_cap s_grown)
    (hmem_grown : s_grown.mem = s.mem)
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (htot_lt : totalSlots N (compGmAt metaBase U w N s.mem) < N)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap)
    (u : Fin U) (v : ℕ) (hv : v < V)
    (hmiss : sbFound ((Memory.spec 0).clientResult s_fix
      (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val),
          keyQuotient (bucketBits N) u.val),
          mOfSeed U N θ (keyQuotient (bucketBits N) u.val)))) ≠ 1) :
    let q := keyQuotient (bucketBits N) u.val
    let b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
    let m := mOfSeed U N θ q
    let d_app := ((((mkCompParams U V w N, (metaBase, itemBase)), (b, m)), (u.val, v)))
    let s' := (Memory.spec 0).clientState s_grown (compInsertAppendNewGenProg d_app)
    CompInsertAppendNewPre w d_app s_grown ∧
    CompOpFrame metaBase itemBase U V w N m_cap s_grown s' ∧
    memoryCost (compInsertAppendNewGenProg d_app) s_grown +
      98 * slotPotential N (compGmAt metaBase U w N s'.mem) ≤
      98 * slotPotential N (compGmAt metaBase U w N s.mem) + 200 ∧
    ∃ s_fix' : Memory.State,
      DictStateInv U V (ghostW w) N 0 θ (Function.update s_abs u (some v)) s_fix' ∧
      FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro q b m d_app s'
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) (hValOfSeed U N θ) u.val
  have hm_lt : m < numMicroPerBucket N := mOfSeed_lt U N θ q
  have hwf := ghostDictParamsWf henv_grown.pos_w henv_grown.le_U henv_grown.lt_pow_U
    henv_grown.le_pow_V
  have hg_env := ghostDictEnvGen henv_grown.pos_w henv_grown.le_U henv_grown.lt_pow_U
    henv_grown.le_pow_V
  have hslot : SlotStoreInv N (compGmAt metaBase U w N s_grown.mem) := by
    rw [hmem_grown, hcpl.gm_eq]; exact hb_inv.hslot
  have hcpl_grown : FixedCoupled metaBase itemBase U V w N s_fix s_grown :=
    ⟨hmem_grown ▸ hcpl.gm_eq, hmem_grown ▸ hcpl.lm_eq, hmem_grown ▸ hcpl.win_inv,
     fun i => hmem_grown ▸ hcpl.td_lt i, fun i => hmem_grown ▸ hcpl.dt_lt i,
     fun d hd => hmem_grown ▸ hcpl.quot_eq d (hmem_grown ▸ hd),
     fun d hd => hmem_grown ▸ hcpl.val_eq d (hmem_grown ▸ hd)⟩
  have htot_grown : totalSlots N (compGmAt metaBase U w N s_grown.mem) < N := by
    rwa [hmem_grown]
  have hm_cap_grown : totalSlots N (compGmAt metaBase U w N s_grown.mem) + 1 ≤ m_cap := by
    rwa [hmem_grown]
  have hq_lt : q < 2 ^ quotientBits U N :=
    keyQuotient_lt_two_pow_quotientBits henv_grown.le_U u.isLt
  have hq_shift : u.val >>> bucketBits N < 2 ^ quotientBits U N := by
    rwa [Nat.shiftRight_eq_div_pow]
  have hv_lt : v < 2 ^ valBits V := hv.trans_le (Nat.le_pow_clog (by decide) V)
  have hold_grown : lmHead N (compLmAt metaBase U w N s_grown.mem) b m ≤ effBucketCap N := by
    rw [hmem_grown, hcpl.lm_eq]
    exact (hb_inv.hchains.1 b hb_lt m hm_lt).head_le_cap
  have hcard_lt : (Dictionary.dom s_abs).card < N := by
    rw [← hinv.htot]
    change totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) < N
    rwa [← hcpl.gm_eq]
  have hins_fix := insertWithHashProg_dict_spec (w := ghostW w) hwf hg_env θ hinv u v
    ⟨Or.inl hcard_lt, hv⟩
  set h_q := hValOfSeed U N θ q
  set s_fix' := (Memory.spec 0).clientState s_fix
    (insertWithHashProg U V (ghostW w) N (((0, u.val), v), h_q))
  have hst_sb_fix :
      (Memory.spec 0).clientState s_fix
        (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), m)) =
        s_fix :=
    (searchBucketProg_bucket_spec hb_inv hg_env hb_lt (q_target := q) (m := m) rfl hm_lt).1
  have htot_fix :
      totalSlots N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) < N := by
    rwa [← hcpl.gm_eq]
  have hs_fix'_eq : s_fix' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s_fix
        (pushBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), v)))
      (prependIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, b), m), bCount N (compGmAt metaBase U w N s_grown.mem) b)) := by
    rw [show bCount N (compGmAt metaBase U w N s_grown.mem) b =
        bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b from by
      rw [hmem_grown, hcpl.gm_eq]; rfl]
    exact insertWithHashProg_clientState_miss U V (ghostW w) N u.val v h_q s_fix b q m
      (and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q)
      (Nat.shiftRight_eq_div_pow u.val (bucketBits N)) rfl hst_sb_fix hmiss htot_fix hb_lt
  obtain ⟨hfr_app, hcpl_app, hcost_app⟩ := compInsertAppendNewGenProg_effect
    henv_grown hcpl_grown hslot hb_lt hm_lt htot_grown hm_cap_grown hq_lt hv_lt hold_grown
  rw [hmem_grown] at hcost_app
  refine ⟨⟨U, V, N, m_cap, s_fix, rfl, u.isLt.trans henv_grown.lt_pow_U, hq_shift, hv_lt,
      henv_grown, hcpl_grown, hslot, hb_lt, hm_lt, htot_grown, hm_cap_grown, hold_grown⟩,
    hfr_app, hcost_app, s_fix', hins_fix.2.2.2.1, ?_⟩
  rw [hs_fix'_eq]
  exact hcpl_app


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
