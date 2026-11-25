/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Rt
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Helpers
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Walk
import CslibFrontier.Tactic.Realize

/-!
# Parameter-Free `bufDeleteGenProg` Subroutine

Certified `O_c(1)` `bufDelete` clearing `nodeActive leaf := 0` while preserving `BufEpFrame`
and opposite-buffer representations.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufDeleteGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufDeleteGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufDeleteGen`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- `BufRt` leaf helper for `bufDelete`: clears `nodeActive leaf := 0` if currently active. -/
@[irreducible] private def bufDeleteLeafRtProg (d : BufRt × ℕ) : Memory.Prog Unit := do
  let rt := d.1
  let idxLI ← pure (4 * d.2 + 2)
  let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
  if id1 = 0 then
    pure ()
  else
    let idxAct ← pure (4 * d.2 + 3)
    let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
    if act = 0 then
      pure ()
    else
      let zero_v ← pure 0
      writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct), zero_v)

private theorem bufDeleteLeafRtProg_eq (d : BufRt × ℕ) :
    bufDeleteLeafRtProg d = (do
      let rt := d.1
      let idxLI ← pure (4 * d.2 + 2)
      let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
      if id1 = 0 then
        pure ()
      else
        let idxAct ← pure (4 * d.2 + 3)
        let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
        if act = 0 then
          pure ()
        else
          let zero_v ← pure 0
          writePackedGenProg
            ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct), zero_v)) := by
  unfold bufDeleteLeafRtProg; rfl

private theorem realizes_bufDeleteLeafRt :
    Realizes .exact bufDeleteLeafRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1 ∧ d.2 < brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufDeleteLeafRtProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, leaf⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hleaf⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hleaf
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)

/-- Parameter-free `bufDelete` (`d = (((cp, base), ep), rKey)`). -/
@[irreducible] def bufDeleteGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (cp_base_ep, rKey) => do
    let rt ← mkBufRtGenProg cp_base_ep
    let one_v ← pure 1
    let zero_v ← pure 0
    let wres ← bufWalkLoopGenProg ((rt, (one_v, (zero_v, rKey))), brCTab rt)
    let (alive, leafRest) := wres
    if alive = 0 then
      pure ()
    else
      bufDeleteLeafRtProg (rt, leafRest.1)

theorem bufDeleteGenProg_spec {c U V w n_max base ep rKey : ℕ}
    {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn) :
    let prog := bufDeleteGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey)
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufDelete (cTabWhp c) (bCharWhp n_max) tr rKey
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc :=
    fun v ch hnz => hv.bounds.2.2.1 v ch hnz
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hw_st, hw_mc, hw_vp, _, hw_a1⟩ :=
    bufWalkLoop_spec henv hep hrep hv.bounds.1 hchild (cTabWhp c) 1 0 rKey hv.bounds.1
  have hw1 := hw_a1 rfl
  have hm_seg : base + brOffMeta rt +
      packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := (rt_seg_le c U V w n_max base ep hep).2.2.2.1
  obtain ⟨hna32, hia32, _, h32_c, hc_le_m, hm_le_i⟩ :
      brHdrNA rt < 32 ∧ brHdrIA rt < 32 ∧ brHdrNA rt ≠ brHdrIA rt ∧ 32 ≤ brOffChild rt ∧
      brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffMeta rt ∧
      brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffItems rt := rt_disj_le c U V w n_max base ep hep
  have hrep_meta : ∀ u < tr.nodeAlloc,
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 2) =
        tr.nodeLeafItem u ∧
      (tr.nodeLeafItem u ≠ 0 →
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 3) =
          tr.nodeActive u) :=
    (bufTrieMemRep_iff_rt.mp hrep).2.2.2.2.2.2.1
  dsimp only
  unfold bufDeleteGenProg
  simp only [pure_bind]
  have hbr_cTab : brCTab rt = cTabWhp c := rfl
  set wprog := bufWalkLoopGenProg ((rt, (1, (0, rKey))), cTabWhp c)
  set wres := (Memory.spec 0).clientResult s wprog
  have hs'_pre : (Memory.spec 0).clientState s
      (mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt' =>
        bufWalkLoopGenProg ((rt', (1, (0, rKey))), brCTab rt') >>= fun wr =>
          if wr.1 = 0 then pure () else bufDeleteLeafRtProg (rt', wr.2.1)) =
      (Memory.spec 0).clientState s
        (if wres.1 = 0 then pure () else bufDeleteLeafRtProg (rt, wres.2.1)) := by
    rw [clientState_bind, hrt_st, hrt_res, hbr_cTab,
      clientState_bind, hw_st]
  rw [hs'_pre]
  dsimp only [bufDelete]
  rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
  · rw [hwk] at hw1
    rw [ite_eq_left hw1]
    have hst_pure : (Memory.spec 0).clientState s (pure ()) = s := rfl
    rw [hst_pure]
    refine ⟨rfl, ?_, ?_, hrep, BufEpFrame.refl _⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hrt_st, hrt_res, hrt_mc, hbr_cTab, hw_st, hw_mc, ite_eq_left hw1]
      change 0 + (2 * cTabWhp c + 0) ≤ _; omega
    · refine validProg_bind hrt_vp ?_
      rw [hrt_st, hrt_res, hbr_cTab]
      refine validProg_bind hw_vp ?_
      rw [hw_st, ite_eq_left hw1]
      exact validProg_pure _
  · rw [hwk] at hw1
    dsimp only
    obtain ⟨_, hw_eq, hlf_lt⟩ := hw1
    have hw_one : wres.1 = 1 := congrArg Prod.fst hw_eq
    have hw_lf : wres.2.1 = leaf := congrArg (fun p => p.2.1) hw_eq
    have hna_max := hrep.1
    have hidx2 : 4 * leaf + 2 < 6 * maxTrieNodesWhp c n_max := by omega
    have hidx3 : 4 * leaf + 3 < 6 * maxTrieNodesWhp c n_max := by omega
    obtain ⟨hli_eq, hact_eq⟩ := hrep_meta leaf hlf_lt
    have hwres_nz : wres.1 ≠ 0 := by omega
    rw [ite_eq_right hwres_nz, hw_lf]
    have hmc_all : memoryCost
        (mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt' =>
          bufWalkLoopGenProg ((rt', (1, (0, rKey))), brCTab rt') >>= fun wr =>
            if wr.1 = 0 then pure () else bufDeleteLeafRtProg (rt', wr.2.1)) s ≤
        2 * cTabWhp c + 8 := by
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hrt_st, hrt_res, hrt_mc, hbr_cTab, hw_st, hw_mc, ite_eq_right hwres_nz, hw_lf,
        bufDeleteLeafRtProg_eq]
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_readPackedGen]
      split_ifs with h1
      · change 0 + (2 * cTabWhp c + (2 + 0)) ≤ _; omega
      · simp only [memoryCost_bind, memoryCost_readPackedGen]
        split_ifs with h2
        · change 0 + (2 * cTabWhp c + (2 + (2 + 0))) ≤ _; omega
        · rw [memoryCost_writePackedGen]
          omega
    have hvp_all : ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt' =>
          bufWalkLoopGenProg ((rt', (1, (0, rKey))), brCTab rt') >>= fun wr =>
            if wr.1 = 0 then pure () else bufDeleteLeafRtProg (rt', wr.2.1)) := by
      refine validProg_bind hrt_vp ?_
      rw [hrt_st, hrt_res, hbr_cTab]
      refine validProg_bind hw_vp ?_
      rw [hw_st, ite_eq_right hwres_nz, hw_lf, bufDeleteLeafRtProg_eq]
      simp only [pure_bind]
      refine validProg_bind (validProg_readPacked hw hidx2 hm_seg) ?_
      rw [clientState_readPackedGen]
      split_ifs with h1
      · exact validProg_pure _
      · refine validProg_bind (validProg_readPacked hw hidx3 hm_seg) ?_
        rw [clientState_readPackedGen]
        split_ifs with h2
        · exact validProg_pure _
        · exact validProg_writePacked hw hgk hidx3 hm_seg
    have hleaf_st : (Memory.spec 0).clientState s (bufDeleteLeafRtProg (rt, leaf)) =
        if tr.nodeLeafItem leaf = 0 then s
        else if tr.nodeActive leaf = 0 then s
        else
          { mem := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * leaf + 3) 0,
            frontier := s.frontier } := by
      rw [bufDeleteLeafRtProg_eq]
      simp only [pure_bind]
      rw [clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl, hli_eq]
      by_cases hli0 : tr.nodeLeafItem leaf = 0
      · rw [ite_eq_left hli0, ite_eq_left hli0]; rfl
      · rw [ite_eq_right hli0, ite_eq_right hli0, clientState_bind,
          clientState_readPackedGen, clientResult_readPackedGen, hact_eq hli0]
        by_cases hact0 : tr.nodeActive leaf = 0
        · rw [ite_eq_left hact0, ite_eq_left hact0]; rfl
        · rw [ite_eq_right hact0, ite_eq_right hact0, clientState_writePackedGen]
    rw [hleaf_st]
    by_cases hli0 : tr.nodeLeafItem leaf = 0
    · rw [ite_eq_left hli0, ite_eq_left (Or.inl hli0)]
      exact ⟨rfl, hmc_all, hvp_all, hrep, BufEpFrame.refl _⟩
    · rw [ite_eq_right hli0]
      by_cases hact0 : tr.nodeActive leaf = 0
      · rw [ite_eq_left hact0, ite_eq_left (Or.inr hact0)]
        exact ⟨rfl, hmc_all, hvp_all, hrep, BufEpFrame.refl _⟩
      · have hnot_or : ¬(tr.nodeLeafItem leaf = 0 ∨ tr.nodeActive leaf = 0) :=
          fun h => h.elim hli0 hact0
        rw [ite_eq_right hact0, ite_eq_right hnot_or]
        set mem' := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem
          (4 * leaf + 3) 0
        have hfr : BufEpFrame base c U V w n_max ep s.mem mem' :=
          bufEpFrame_writeMeta hw hep hidx3
        have h0_lt : 0 < 2 ^ globalPtrBits n_max := Nat.two_pow_pos _
        refine ⟨rfl, hmc_all, hvp_all, ?_, hfr⟩
        obtain ⟨hna, hia, hhna, hhia, hch, hpar, hlf, hit⟩ := bufTrieMemRep_iff_rt.mp hrep
        rw [bufTrieMemRep_iff_rt]
        dsimp only
        rw [← show rt = mkBufRt c U V w n_max base ep from rfl] at hhna hhia hch hpar hlf hit ⊢
        refine ⟨hna, hia,
          (writePacked_outside hw _ hidx3 _ (by omega)).trans hhna,
          (writePacked_outside hw _ hidx3 _ (by omega)).trans hhia,
          fun u hu ch' hch' => ?_,
          fun u hu1 hu => ⟨(readPacked_writePacked_of_ne hw s.mem (by omega) 0).trans
            (hpar u hu1 hu).1,
            (readPacked_writePacked_of_ne hw s.mem (by omega) 0).trans (hpar u hu1 hu).2⟩,
          fun u hu => ⟨(readPacked_writePacked_of_ne hw s.mem (by omega) 0).trans (hlf u hu).1,
            fun hnz => by
              by_cases hul : u = leaf
              · subst hul
                rw [Function.update_self]
                exact readPacked_writePacked_self _ _ _ s.mem (4 * u + 3) h0_lt
              · rw [Function.update_of_ne hul]
                exact (readPacked_writePacked_of_ne hw s.mem (by omega) 0).trans
                  ((hlf u hu).2 hnz)⟩,
          fun id hid => ⟨(readPacked_writePacked_disjoint hw
              (show id < 6 * qEpochWhp n_max + 6 by omega) hidx3 (Or.inr (by omega))).trans
              (hit id hid).1,
            (readPacked_writePacked_disjoint hw
              (show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega) hidx3
              (Or.inr (by omega))).trans (hit id hid).2.1,
            (readPacked_writePacked_disjoint hw
              (show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega) hidx3
              (Or.inr (by omega))).trans (hit id hid).2.2⟩⟩
        have huc_lt : u * 2 ^ bCharWhp n_max + ch' < trieChildEntriesWhp c n_max := by
          unfold trieChildEntriesWhp
          calc u * 2 ^ bCharWhp n_max + ch'
              < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch' _
            _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
            _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
        exact (readPacked_writePacked_disjoint hw huc_lt hidx3 (Or.inl (by omega))).trans
          (hch u hu ch' hch')

theorem realizes_bufDeleteGen :
    Realizes .exact bufDeleteGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      BufReadGenPre
      (fun _ _ => 0) := by
  unfold bufDeleteGenProg
  have hmrt := realizes_mkBufRtGen
  have hwl := realizes_bufWalkLoopGen
  have hdl := realizes_bufDeleteLeafRt
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, ep⟩, rKey⟩
    obtain ⟨c, U, V, w₀, n_max, tr, mapFn, henv, rfl, hep, hrep, hv⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc :=
      fun v ch hnz => hv.bounds.2.2.1 v ch hnz
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
    obtain ⟨hsafe, hw_st, _, _, _, hw_a1⟩ :=
      bufWalkLoop_spec henv hep hrep hv.bounds.1 hchild (cTabWhp c) 1 0 rKey hv.bounds.1
    have hw1 := hw_a1 rfl
    simp only [hrt_st, hrt_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hsafe
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brCTab, brMaxNodes] at *
       rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
       · rw [hwk] at hw1; omega
       · rw [hwk] at hw1
         obtain ⟨_, hw_eq, hlf_lt⟩ := hw1
         exact (congrArg (fun p => p.2.1) hw_eq) ▸ hlf_lt.trans_le hrep.1)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
