/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.WorkPotential
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.ScanMeta
import Mathlib.Tactic.Positivity

/-!
# `fastInsert` Success and Clean-Window Preservation for `SuccinctWhpFastProb`

Internal proof (`fastInsert_some_and_clean_props`) showing `fastInsert` always returns `some fs1`
and maintains the clean-epoch buffer-allocation and rebuild-work invariants under `GoodSeedOnWindow`
(not re-exported by `SuccinctWhpFastProb`).
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

private theorem not_mem_dom_of_bufLookup_some {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) {u : Fin U} (hu_ndom : u ∉ Dictionary.dom dict)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U))) (hu_W : u ∈ W_keys)
    (hinj_rkey : Set.InjOn (fpReducedKey c U n_max θ.2) (W_keys : Set (Fin U)))
    {tr : BufTrie} {m : ℕ → Option (ℕ × ℕ)} {st_tag : ℕ}
    (hv_tr : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr m)
    (hrel : BufMapRel (numBucketsWhp n_max) st_tag fs.bktCount fs.locState
      (fs.rKeyAt c U n_max θ) m)
    (hlk_some :
      (bufLookup (cTabWhp c) (bCharWhp n_max) tr (fpReducedKey c U n_max θ.2 u)).isSome = true) :
    False := by
  have hrk_lt := fpReducedKey_lt c U n_max θ.2 u
  cases hlk : bufLookup (cTabWhp c) (bCharWhp n_max) tr (fpReducedKey c U n_max θ.2 u) with
  | none => rw [hlk] at hlk_some; cases hlk_some
  | some bp0 =>
    rcases bp0 with ⟨b', l'⟩
    rw [hv_tr.lookup_eq hrk_lt] at hlk
    obtain ⟨hb', hl', _, hrk_eq⟩ := (hrel.2 _ b' l').mp hlk
    obtain ⟨hm', _⟩ := hc.mem_dom_of_loc hb' hl'
    let u' : Fin U := ⟨fs.keyValAt c U n_max θ.1 b' l', (hc.active_item b' hb' l' hl').1⟩
    have hrk_u' : fpReducedKey c U n_max θ.2 u' = fpReducedKey c U n_max θ.2 u := by
      dsimp only [FastState.rKeyAt] at hrk_eq
      simpa [u'.isLt, u'] using hrk_eq
    exact hu_ndom (hinj_rkey (hdom_sub hm') hu_W hrk_u' ▸ hm')

theorem fastInsert_some_and_clean_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys W_ins BadIns : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hcw : CleanWindowFast c U V n_max θ W_keys BadIns fs dict)
    {u : Fin U} {v : ℕ} (hval : Dynamic.valid V n_max dict (.insert u v))
    (hu_ins : u ∈ W_ins)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hu_W : u ∈ W_keys)
    (hinj_rkey : Set.InjOn (fpReducedKey c U n_max θ.2) (W_keys : Set (Fin U)))
    (hbal_nxt : BalancedBuckets U n_max (bktHash c U n_max θ.1)
      (Dictionary.dom (Dynamic.step dict (.insert u v)).1))
    (hbad_def : ∀ x ∈ W_ins,
      (∃ y ∈ W_keys.filter (fun w =>
        feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) w.val =
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) x.val),
        x ≠ y ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt x = fpHash c U n_max θ.2 salt y) →
      x ∈ BadIns)
    (hbad_lt : #BadIns < 2 * sMaxWhp c n_max) :
    ∃ fs1,
      fastInsert c U n_max θ fs u v = some fs1 ∧
      fs1.epochClock = fs.epochClock ∧
      (fs1.buf fs1.curEp).itemAlloc ≤
        #(BadIns.filter fun x =>
          bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs1.buf fs1.curEp)
            (fpReducedKey c U n_max θ.2 x)) ∧
      stageWorkRemaining c n_max fs1 = stageWorkRemaining c n_max fs ∧
      SaltBoundAt c U n_max θ W_keys fs1 := by
  have hv := hcw.valid
  have hc := hv.toCore
  set h1 := bktHash c U n_max θ.1
  set b := feistelBucket (bWhp n_max) h1 u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt (bWhp n_max) h1 u.val
  have hom_m := fun s => overmarsStep_meta c U n_max b θ s
  unfold fastInsert fastInsertAlloc fastInsertFresh
  dsimp only
  cases hfl : fastFindLoc c U n_max θ fs u with
  | some loc =>
    dsimp only
    set fs' : FastState :=
      { fs with valArr := Function.update fs.valArr (fs.physSlot n_max b loc) v }
    obtain ⟨h1m, h2m, h3m, h4m, h5m, h6m, h7m, h8m, h9m, h10m⟩ := hom_m fs'
    refine ⟨overmarsStep c U n_max θ b fs', rfl, h1m, ?_, ?_, ?_⟩
    · rw [h3m, h2m]; exact hcw.buf_alloc
    · exact stageWorkRemaining_eq_of_meta c n_max h4m h5m h6m h7m h9m h10m
        (by dsimp only [FastState.oldEp]; rw [h3m, h2m])
    · intro hs2 hdi; rw [h4m] at hs2; rw [h7m, h6m] at hdi
      rw [h8m, h7m, h9m]; exact hcw.salt_bound hs2 hdi
  | none =>
    dsimp only
    have hfl_sp := hv.fastFindLoc_spec u
    dsimp only at hfl_sp; rw [hfl] at hfl_sp
    have hu_ndom : u ∉ Dictionary.dom dict := Dictionary.notMem_dom_iff.mpr hfl_sp
    -- 1. Guard 1 (`totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0)`) is false:
    have hg1 : ¬(totalLocalCoordsWhp n_max ≤ fs.bktCount b ∨
        (capFrontWhp n_max ≤ fs.bktCount b ∧ fs.poolFreeTop = 0)) := by
      set dict' := (Dynamic.step dict (.insert u v)).1
      have hdom' : Dictionary.dom dict' = insert u (Dictionary.dom dict) := by
        ext x
        by_cases hx : x = u
        · subst hx; simp [dict', Dictionary.dom]
        · simp [dict', Dictionary.dom, hx]
      have hcard_dom' : #(Dictionary.dom dict') ≤ n_max := by
        rw [hdom', Finset.card_insert_of_notMem hu_ndom]
        rcases hval.1 with hlt | hsome
        · omega
        · rw [hfl_sp] at hsome; cases hsome
      let X' : Fin (numBucketsWhp n_max) → ℕ :=
        fun b' => #((Dictionary.dom dict').filter fun w =>
          feistelBucket (bWhp n_max) h1 w.val = b'.val)
      have hX'_eq : ∀ b' : Fin (numBucketsWhp n_max),
          X' b' = if b'.val = b then fs.bktCount b + 1 else fs.bktCount b'.val := by
        intro b'
        dsimp only [X', h1]
        rw [hdom', Finset.filter_insert]
        by_cases hbb : b = b'.val
        · have heq : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b'.val := hbb
          rw [ite_eq_left heq, Finset.card_insert_of_notMem
            (fun hm => hu_ndom (mem_filter.mp hm).1), ite_eq_left hbb.symm, ← hbb,
            hc.bktCount_eq_card_filter hb]
        · have hne : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val ≠ b'.val := hbb
          rw [ite_eq_right hne, ite_eq_right (Ne.symm hbb), hc.bktCount_eq_card_filter b'.isLt]
      have hsum_X' : ∑ b', X' b' = #(Dictionary.dom dict') := by
        have h1_sum : ∀ w ∈ Dictionary.dom dict', (1 : ℕ) =
            ∑ b' : Fin (numBucketsWhp n_max),
              if feistelBucket (bWhp n_max) h1 w.val = b'.val then 1 else 0 := by
          intro w _
          let bw : Fin (numBucketsWhp n_max) :=
            ⟨feistelBucket (bWhp n_max) h1 w.val, feistelBucket_lt (bWhp n_max) h1 w.val⟩
          rw [Fintype.sum_eq_single bw]
          · simp [bw]
          · intro b' hb'; simp [show feistelBucket (bWhp n_max) h1 w.val ≠ b'.val from
              fun h => hb' (Fin.ext h.symm)]
        calc ∑ b' : Fin (numBucketsWhp n_max), X' b'
            = ∑ b' : Fin (numBucketsWhp n_max), ∑ w ∈ Dictionary.dom dict',
                if feistelBucket (bWhp n_max) h1 w.val = b'.val then 1 else 0 :=
              Fintype.sum_congr _ _ fun b' => by dsimp only [X']; rw [Finset.card_filter]
          _ = ∑ w ∈ Dictionary.dom dict', ∑ b' : Fin (numBucketsWhp n_max),
                if feistelBucket (bWhp n_max) h1 w.val = b'.val then 1 else 0 := Finset.sum_comm
          _ = ∑ _w ∈ Dictionary.dom dict', 1 := Finset.sum_congr rfl fun w hw => (h1_sum w hw).symm
          _ = #(Dictionary.dom dict') := by simp
      obtain ⟨hcb_lt, _, hpool_le⟩ := sum_sub_capFront_le_poolSize hc.hth X'
        (hsum_X'.trans_le hcard_dom')
        (fun b' => by rw [hsum_X']; exact (hbal_nxt b').1)
        (fun b' => by rw [hsum_X']; exact (hbal_nxt b').2)
      have hb_cb := hcb_lt ⟨b, hb⟩
      rw [hX'_eq ⟨b, hb⟩, ite_eq_left rfl] at hb_cb
      have hcb_pos : 0 < capBackWhp n_max := by
        unfold capBackWhp; have := slabScale_pos n_max; positivity
      have hX_lt_tot : fs.bktCount b < totalLocalCoordsWhp n_max := by
        unfold totalLocalCoordsWhp; omega
      rintro (hge | ⟨hcf_le, htop0⟩)
      · omega
      · have hsum_add1 :
            (∑ b' ∈ range (numBucketsWhp n_max), (fs.bktCount b' - capFrontWhp n_max)) + 1 =
              ∑ b' : Fin (numBucketsWhp n_max), (X' b' - capFrontWhp n_max) := by
          rw [← Fin.sum_univ_eq_sum_range]
          have hpt : ∀ b' : Fin (numBucketsWhp n_max),
              X' b' - capFrontWhp n_max =
                (fs.bktCount b'.val - capFrontWhp n_max) + (if b' = ⟨b, hb⟩ then 1 else 0) := by
            intro b'; rw [hX'_eq b']
            by_cases hbb : b' = ⟨b, hb⟩
            · subst hbb; simp; omega
            · have hv_ne : b'.val ≠ b := fun h => hbb (Fin.ext h)
              simp [hbb, hv_ne]
          simp_rw [hpt]
          rw [Finset.sum_add_distrib]
          simp
        have hcons := hc.pool_conservation
        omega
    rw [ite_eq_right hg1]
    -- 2. Guard 2 (Stage-1 `rKey` collision in `buf curEp` or `buf oldEp`) is false:
    set rKey := fpReducedKey c U n_max θ.2 u
    have hrk_lt : rKey < 2 ^ (cTabWhp c * bCharWhp n_max) := fpReducedKey_lt c U n_max θ.2 u
    have hg2 : ¬((bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome = true ∨
        (fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome = true)) := by
      rintro (hcur_some | ⟨hs3, hold_some⟩)
      · obtain ⟨_, _, cm, hvc, hrc⟩ := hc.bufCur_valid
        exact not_mem_dom_of_bufLookup_some hc hu_ndom hdom_sub hu_W hinj_rkey hvc hrc hcur_some
      · have hbo := hc.bufOld_valid; rw [ite_eq_left hs3] at hbo
        obtain ⟨_, _, om, hvo, hro⟩ := hbo
        exact not_mem_dom_of_bufLookup_some hc hu_ndom hdom_sub hu_W hinj_rkey hvo hro hold_some
    rw [ite_eq_right hg2]
    -- 3. Guard 3 (`2 * sMaxWhp ≤ itemAlloc`) is false since `itemAlloc ≤ #BadIns`:
    have hia_lt : (fs.buf fs.curEp).itemAlloc < 2 * sMaxWhp c n_max :=
      hcw.buf_alloc.trans_lt ((Finset.card_filter_le _ _).trans_lt hbad_lt)
    have hg3 : ¬((btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true ∧
        (!bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey) = true ∧
        2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc) := by
      rintro ⟨_, _, hge⟩; omega
    rw [ite_eq_right hg3]
    -- Now `fastInsert` returns `some (overmarsStep ... fsInserted)`!
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · exact (hom_m _).1.trans (by
        by_cases hfpc : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true
        · rw [ite_eq_left hfpc]
        · rw [ite_eq_right hfpc])
    · -- Check `(fs1.buf fs1.curEp).itemAlloc ≤ #(AllocBadKeys)`!
      rw [(hom_m _).2.2.1, (hom_m _).2.1]
      by_cases hfpc : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true
      · rw [ite_eq_left hfpc]
        change (Function.update fs.buf fs.curEp
            (bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey b (fs.bktCount b))
            fs.curEp).itemAlloc ≤
          #(BadIns.filter fun x =>
            bufEverPresent (cTabWhp c) (bCharWhp n_max)
              (Function.update fs.buf fs.curEp
                (bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey b (fs.bktCount b))
                fs.curEp)
              (fpReducedKey c U n_max θ.2 x))
        rw [Function.update_self]
        -- Show `u ∈ BadIns` from `hfpc`!
        have hu_bad : u ∈ BadIns := by
          obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b hb
          have hs_b := hc.bktSalt_lt b hb
          have hfp_lt : fpOfSalt c U n_max θ.2 (fs.bktSalt b) u < 2 ^ fpBitsWhp n_max := by
            dsimp only [fpOfSalt]; simp [hs_b, fpHash_lt]
          cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u) with
          | none => rw [hlk] at hfpc; cases hfpc
          | some loc_v =>
            rw [hvl.lookup_eq hc.hth (hv.liveInsCount_le hb) hfp_lt] at hlk
            obtain ⟨hlv, _, hfp_v⟩ := (hrl.2 _ loc_v).mp hlk
            obtain ⟨hm_v, hfb_v⟩ := hc.mem_dom_of_loc hb hlv
            let y : Fin U := ⟨fs.keyValAt c U n_max θ.1 b loc_v, (hc.active_item b hb loc_v hlv).1⟩
            have hy_ne : u ≠ y := fun h => hu_ndom (h ▸ hm_v)
            refine hbad_def u hu_ins ⟨y, mem_filter.mpr ⟨hdom_sub hm_v, hfb_v⟩, hy_ne,
              ⟨fs.bktSalt b, hs_b⟩, ?_⟩
            have h1_fp : fpOfSalt c U n_max θ.2 (fs.bktSalt b) u =
                fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs_b⟩ u := by
              dsimp only [fpOfSalt]; simp [hs_b]
            have h2_fp : fs.fpAt c U n_max θ (fs.bktSalt b) b loc_v =
                fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs_b⟩ y := by
              dsimp only [FastState.fpAt]; simp [hs_b, y.isLt, y]
            exact h1_fp.symm.trans (hfp_v.symm.trans h2_fp)
        obtain ⟨_, _, _, hvc, _⟩ := hc.bufCur_valid
        have hins := hvc.insert_spec (b := b) (loc := fs.bktCount b) hrk_lt
        set tr' := bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey b (fs.bktCount b)
        have hsub_ev : BadIns.filter (fun x =>
            bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
              (fpReducedKey c U n_max θ.2 x)) ⊆
            BadIns.filter (fun x =>
              bufEverPresent (cTabWhp c) (bCharWhp n_max) tr'
                (fpReducedKey c U n_max θ.2 x)) := by
          intro x hx
          rw [mem_filter] at hx ⊢
          refine ⟨hx.1, ?_⟩
          rw [hins.2.2.2.2.1 _ (fpReducedKey_lt c U n_max θ.2 x)]
          split_ifs
          · rfl
          · exact hx.2
        by_cases hev : bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey = true
        · rw [(hins.2.2.2.2.2.1 hev).2]
          exact hcw.buf_alloc.trans (Finset.card_le_card hsub_ev)
        · have hu_nin : u ∉ BadIns.filter (fun x =>
              bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
                (fpReducedKey c U n_max θ.2 x)) := by
            rw [mem_filter]; rintro ⟨_, ht⟩; exact hev ht
          have hu_in' : u ∈ BadIns.filter (fun x =>
              bufEverPresent (cTabWhp c) (bCharWhp n_max) tr'
                (fpReducedKey c U n_max θ.2 x)) := by
            rw [mem_filter]; refine ⟨hu_bad, ?_⟩
            rw [hins.2.2.2.2.1 _ hrk_lt, ite_eq_left rfl]
          have hins_sub : insert u (BadIns.filter (fun x =>
              bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
                (fpReducedKey c U n_max θ.2 x))) ⊆
              BadIns.filter (fun x =>
                bufEverPresent (cTabWhp c) (bCharWhp n_max) tr'
                  (fpReducedKey c U n_max θ.2 x)) :=
            Finset.insert_subset_iff.mpr ⟨hu_in', hsub_ev⟩
          calc tr'.itemAlloc
              ≤ (fs.buf fs.curEp).itemAlloc + 1 := by rw [hins.2.2.2.1]; split_ifs; omega
            _ ≤ #(BadIns.filter fun x =>
                  bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
                    (fpReducedKey c U n_max θ.2 x)) + 1 := Nat.add_le_add_right hcw.buf_alloc 1
            _ = #(insert u (BadIns.filter fun x =>
                  bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
                    (fpReducedKey c U n_max θ.2 x))) :=
                (Finset.card_insert_of_notMem hu_nin).symm
            _ ≤ _ := Finset.card_le_card hins_sub
      · rw [ite_eq_right hfpc]
        exact hcw.buf_alloc
    · have hne_ep : fs.oldEp ≠ fs.curEp := by
        dsimp only [FastState.oldEp]; rcases hc.curEp_or with h | h <;> omega
      have hwk_i : ∀ (s_i : FastState),
          s_i.rebStage = fs.rebStage → s_i.stageCursor = fs.stageCursor →
          s_i.dirtyCount = fs.dirtyCount → s_i.dirtyIdx = fs.dirtyIdx →
          s_i.rebCandSalt = fs.rebCandSalt → s_i.rebScanCursor = fs.rebScanCursor →
          (s_i.buf s_i.oldEp).nodeAlloc = (fs.buf fs.oldEp).nodeAlloc →
          stageWorkRemaining c n_max (overmarsStep c U n_max θ b s_i) =
            stageWorkRemaining c n_max fs := by
        intro s_i r1 r2 r3 r4 r5 r6 r7
        obtain ⟨_, q2, q3, q4, q5, q6, q7, _, q9, q10⟩ := hom_m s_i
        refine stageWorkRemaining_eq_of_meta c n_max (q4.trans r1) (q5.trans r2)
          (q6.trans r3) (q7.trans r4) (q9.trans r5) (q10.trans r6) ?_
        have hold_eq : (overmarsStep c U n_max θ b s_i).oldEp = s_i.oldEp := by
          dsimp only [FastState.oldEp]; rw [q2]
        rw [hold_eq, q3]; exact r7
      by_cases hfpc : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true
      · rw [ite_eq_left hfpc]
        refine hwk_i _ rfl rfl rfl rfl rfl rfl ?_
        change (Function.update fs.buf fs.curEp _ fs.oldEp).nodeAlloc = _
        rw [Function.update_of_ne hne_ep]
      · rw [ite_eq_right hfpc]
        exact hwk_i _ rfl rfl rfl rfl rfl rfl rfl
    · have hst_i : ∀ (s_i : FastState),
          s_i.rebStage = fs.rebStage → s_i.dirtyCount = fs.dirtyCount →
          s_i.dirtyIdx = fs.dirtyIdx → s_i.dirtyBuckets = fs.dirtyBuckets →
          s_i.rebCandSalt = fs.rebCandSalt →
          SaltBoundAt c U n_max θ W_keys (overmarsStep c U n_max θ b s_i) := by
        intro s_i r1 r2 r3 r4 r5
        obtain ⟨_, _, _, q4, _, q6, q7, q8, q9, _⟩ := hom_m s_i
        intro hs2 hdi
        rw [q4, r1] at hs2; rw [q7, q6, r3, r2] at hdi
        rw [q8, q7, q9, r4, r3, r5]
        exact hcw.salt_bound hs2 hdi
      by_cases hfpc : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true
      · rw [ite_eq_left hfpc]; exact hst_i _ rfl rfl rfl rfl rfl
      · rw [ite_eq_right hfpc]; exact hst_i _ rfl rfl rfl rfl rfl

end Cslib.DataStructure.Dictionary.SuccinctWhp
