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
# Parameter-Free `bufLookupGenProg` Subroutine

Certified `O_c(1)` `bufLookup` returning `(1, (b, loc))` on active match and `(0, (0, 0))`
otherwise without mutating memory.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufLookupGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufLookupGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufLookupGen`
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

/-- `BufRt` leaf helper for `bufLookup`: checks `nodeLeafItem` and `nodeActive`, then reads
`(b, loc)`. -/
@[irreducible] private def bufLookupLeafRtProg (d : BufRt × ℕ) :
    Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt := d.1
  let idxLI ← pure (4 * d.2 + 2)
  let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
  if id1 = 0 then
    pure (0, (0, 0))
  else
    let idxAct ← pure (4 * d.2 + 3)
    let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
    if act = 0 then
      pure (0, (0, 0))
    else
      let id ← pure (id1 - 1)
      bufReadItemPairRtProg (rt, id)

private theorem bufLookupLeafRtProg_eq (d : BufRt × ℕ) :
    bufLookupLeafRtProg d = (do
      let rt := d.1
      let idxLI ← pure (4 * d.2 + 2)
      let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
      if id1 = 0 then
        pure (0, (0, 0))
      else
        let idxAct ← pure (4 * d.2 + 3)
        let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
        if act = 0 then
          pure (0, (0, 0))
        else
          let id ← pure (id1 - 1)
          bufReadItemPairRtProg (rt, id)) := by
  unfold bufLookupLeafRtProg; rfl

/-- Precondition for `bufLookupLeafRtProg`. -/
private def BufLookupLeafPre (w : ℕ) (d : BufRt × ℕ) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max base ep tr,
    WhpLargeEnv c U V w₀ n_max w base ∧ (ep = 0 ∨ ep = 1) ∧
    d.1 = mkBufRt c U V w₀ n_max base ep ∧
    BufTrieMemRep base c U V w₀ n_max ep tr s.mem ∧
    d.2 < tr.nodeAlloc ∧
    (tr.nodeLeafItem d.2 ≠ 0 → tr.nodeLeafItem d.2 ≤ tr.itemAlloc)

private theorem realizes_bufLookupLeafRt :
    Realizes .exact bufLookupLeafRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BufLookupLeafPre
      (fun _ _ => 0) := by
  unfold bufLookupLeafRtProg
  have hrp := realizes_readPackedGen
  have hrip := realizes_bufReadItemPairRt
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, leaf⟩
    obtain ⟨c, U, V, w₀, n_max, base, ep, tr, henv, hep, rfl, hrep, hleaf, hli_le⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hna_max : tr.nodeAlloc ≤ maxTrieNodesWhp c n_max := hrep.1
    have hia_le : tr.itemAlloc ≤ qEpochWhp n_max := hrep.2.1
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    have hrep_li : readPacked (base + brOffMeta (mkBufRt c U V w n_max base ep))
        (globalPtrBits n_max) w s.mem (4 * leaf + 2) = tr.nodeLeafItem leaf := by
      have hm := hrep.2.2.2.2.2.2.1 leaf hleaf
      rcases hep with rfl | rfl <;> exact hm.1
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (simp only [brBase, brOffMeta, brGBits, brW, brQEp, mkBufRt,
         clientResult_readPackedGen] at *
       rw [hrep_li] at *
       have hnz : tr.nodeLeafItem leaf ≠ 0 := by omega
       have hle := hli_le hnz
       have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
       omega)

/-- Parameter-free `bufLookup` (`d = (((cp, base), ep), rKey)`), returning `(0, (0, 0))` on `none`
and `(1, (b, loc))` on `some (b, loc)`. -/
@[irreducible] def bufLookupGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ →
    Memory.Prog (ℕ × (ℕ × ℕ))
  | (cp_base_ep, rKey) => do
    let rt ← mkBufRtGenProg cp_base_ep
    let one_v ← pure 1
    let zero_v ← pure 0
    let wres ← bufWalkLoopGenProg ((rt, (one_v, (zero_v, rKey))), brCTab rt)
    let (alive, leafRest) := wres
    if alive = 0 then
      pure (0, (0, 0))
    else
      bufLookupLeafRtProg (rt, leafRest.1)

theorem bufLookupGenProg_spec {c U V w n_max base ep rKey : ℕ}
    {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn) :
    let prog := bufLookupGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match bufLookup (cTabWhp c) (bCharWhp n_max) tr rKey with
       | none => (0, (0, 0))
       | some (b, loc) => (1, (b, loc))) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc :=
    fun v ch hnz => hv.bounds.2.2.1 v ch hnz
  have hleaf_ia : ∀ u < tr.nodeAlloc, tr.nodeLeafItem u ≠ 0 → tr.nodeLeafItem u ≤ tr.itemAlloc :=
    fun u hu hnz => hv.bounds.2.2.2 u hu hnz
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hw_st, hw_mc, hw_vp, _, hw_a1⟩ :=
    bufWalkLoop_spec henv hep hrep hv.bounds.1 hchild (cTabWhp c) 1 0 rKey hv.bounds.1
  have hw1 := hw_a1 rfl
  obtain ⟨_, _, _, hm_seg, hi_seg⟩ := rt_seg_le c U V w n_max base ep hep
  have hrep_meta : ∀ u < tr.nodeAlloc,
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 2) =
        tr.nodeLeafItem u ∧
      (tr.nodeLeafItem u ≠ 0 →
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 3) =
          tr.nodeActive u) := by
    have hm := hrep.2.2.2.2.2.2.1
    rcases hep with rfl | rfl <;> exact hm
  have hrep_items : ∀ id < tr.itemAlloc,
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem (qEpochWhp n_max + id) =
        tr.itemBucket id ∧
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem (2 * qEpochWhp n_max + id) =
        tr.itemLoc id := by
    have hi := hrep.2.2.2.2.2.2.2
    rcases hep with rfl | rfl <;> exact fun id hid => (hi id hid).2
  unfold bufLookupGenProg
  simp only [pure_bind]
  set wprog := bufWalkLoopGenProg ((rt, (1, (0, rKey))), cTabWhp c)
  set wres := (Memory.spec 0).clientResult s wprog
  have hbr_cTab : brCTab rt = cTabWhp c := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hrt_st, hrt_res, hbr_cTab,
      clientState_bind, hw_st]
    split_ifs with hz
    · rfl
    · rw [bufLookupLeafRtProg_eq]
      simp only [pure_bind]
      rw [clientState_bind, clientState_readPackedGen]
      split_ifs with h1
      · rfl
      · rw [clientState_bind, clientState_readPackedGen]
        split_ifs with h2
        · rfl
        · rw [bufReadItemPairRtProg_eq]
          simp only [pure_bind]
          rw [clientState_bind, clientState_readPackedGen,
            clientState_bind, clientState_readPackedGen]
          rfl
  · rw [clientResult_bind, hrt_st, hrt_res, hbr_cTab,
      clientResult_bind, hw_st]
    dsimp only [bufLookup]
    rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
    · rw [hwk] at hw1
      rw [ite_eq_left hw1]; rfl
    · rw [hwk] at hw1
      obtain ⟨_, hw_eq, hlf_lt⟩ := hw1
      have hw_one : wres.1 = 1 := congrArg Prod.fst hw_eq
      have hw_lf : wres.2.1 = leaf := congrArg (fun p => p.2.1) hw_eq
      rw [ite_eq_right (by omega : wres.1 ≠ 0), hw_lf, bufLookupLeafRtProg_eq]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedGen,
        clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl]
      obtain ⟨hli_eq, hact_eq⟩ := hrep_meta leaf hlf_lt
      rw [hli_eq]
      by_cases hli0 : tr.nodeLeafItem leaf = 0
      · simp [hli0]
      · rw [ite_eq_right hli0, clientResult_bind,
          clientState_readPackedGen, clientResult_readPackedGen, hact_eq hli0]
        by_cases hact0 : tr.nodeActive leaf = 0
        · simp [hli0, hact0]
        · rw [ite_eq_right hact0]
          simp only [hli0, hact0, false_or, ↓reduceIte]
          have hid_lt : tr.nodeLeafItem leaf - 1 < tr.itemAlloc := by
            have := hleaf_ia leaf hlf_lt hli0; omega
          obtain ⟨hb_eq, hloc_eq⟩ := hrep_items (tr.nodeLeafItem leaf - 1) hid_lt
          rw [bufReadItemPairRtProg_eq]
          simp only [pure_bind, clientResult_bind,
            clientResult_readPackedGen, StateTransitionSpec.clientResult_pure]
          exact Prod.ext rfl (Prod.ext hb_eq hloc_eq)
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrt_st, hrt_res, hrt_mc, hbr_cTab, hw_st, hw_mc]
    split_ifs with hz
    · change 0 + (2 * cTabWhp c + 0) ≤ _; omega
    · rw [bufLookupLeafRtProg_eq]
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_readPackedGen]
      split_ifs with h1
      · change 0 + (2 * cTabWhp c + (2 + 0)) ≤ _; omega
      · simp only [memoryCost_bind, memoryCost_readPackedGen]
        split_ifs with h2
        · change 0 + (2 * cTabWhp c + (2 + (2 + 0))) ≤ _; omega
        · rw [bufReadItemPairRtProg_eq]
          simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
            memoryCost_readPackedGen]
          change 0 + (2 * cTabWhp c + (2 + (2 + (2 + (2 + 0))))) ≤ _; omega
  · refine validProg_bind hrt_vp ?_
    rw [hrt_st, hrt_res, hbr_cTab]
    refine validProg_bind hw_vp ?_
    rw [hw_st]
    split_ifs with hz
    · exact validProg_pure _
    · rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
      · rw [hwk] at hw1; exact absurd hw1 hz
      · rw [hwk] at hw1
        obtain ⟨_, hw_eq, hlf_lt⟩ := hw1
        have hw_lf : wres.2.1 = leaf := congrArg (fun p => p.2.1) hw_eq
        change ValidProg w (base + largeSpaceWhp c U V w n_max) s
          (bufLookupLeafRtProg (rt, wres.2.1))
        rw [hw_lf, bufLookupLeafRtProg_eq]
        have hna_max := hrep.1
        have hia_le := hrep.2.1
        simp only [pure_bind]
        refine validProg_bind
          (validProg_readPacked hw (show 4 * leaf + 2 < 6 * maxTrieNodesWhp c n_max by omega)
            hm_seg) ?_
        rw [clientState_readPackedGen, clientResult_readPackedGen,
          show brBase rt = base from rfl, show brGBits rt = globalPtrBits n_max from rfl,
          show brW rt = w from rfl, (hrep_meta leaf hlf_lt).1]
        split_ifs with hli0
        · exact validProg_pure _
        · refine validProg_bind
            (validProg_readPacked hw (show 4 * leaf + 3 < 6 * maxTrieNodesWhp c n_max by omega)
              hm_seg) ?_
          rw [clientState_readPackedGen]
          split_ifs with hact0
          · exact validProg_pure _
          · have hid_lt : tr.nodeLeafItem leaf - 1 < tr.itemAlloc := by
              have := hleaf_ia leaf hlf_lt hli0; omega
            rw [bufReadItemPairRtProg_eq]
            simp only [pure_bind]
            refine validProg_bind
              (validProg_readPacked hw
                (show brQEp rt + (tr.nodeLeafItem leaf - 1) < 6 * qEpochWhp n_max + 6
                  by dsimp [rt, mkBufRt, brQEp]; omega) hi_seg) ?_
            rw [clientState_readPackedGen]
            exact validProg_bind
              (validProg_readPacked hw
                (show 2 * brQEp rt + (tr.nodeLeafItem leaf - 1) < 6 * qEpochWhp n_max + 6
                  by dsimp [rt, mkBufRt, brQEp]; omega) hi_seg)
              (validProg_pure _)

theorem realizes_bufLookupGen :
    Realizes .exact bufLookupGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BufReadGenPre
      (fun _ _ => 0) := by
  unfold bufLookupGenProg
  have hmrt := realizes_mkBufRtGen
  have hwl := realizes_bufWalkLoopGen
  have hll := realizes_bufLookupLeafRt
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, ep⟩, rKey⟩
    obtain ⟨c, U, V, w₀, n_max, tr, mapFn, henv, rfl, hep, hrep, hv⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc :=
      fun v ch hnz => hv.bounds.2.2.1 v ch hnz
    have hleaf_ia : ∀ u < tr.nodeAlloc, tr.nodeLeafItem u ≠ 0 → tr.nodeLeafItem u ≤ tr.itemAlloc :=
      fun u hu hnz => hv.bounds.2.2.2 u hu hnz
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
    | (have hbr_c : brCTab (mkBufRt c U V w n_max base ep) = cTabWhp c := rfl
       simp only [hbr_c] at *
       rw [hw_st]
       rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
       · rw [hwk] at hw1; omega
       · rw [hwk] at hw1
         obtain ⟨_, hw_eq, hlf_lt⟩ := hw1
         have hw_lf := congrArg (fun p => p.2.1) hw_eq
         exact ⟨c, U, V, w, n_max, base, ep, tr, henv, hep, rfl, hrep,
           hw_lf ▸ hlf_lt, fun hnz => hleaf_ia _ (hw_lf ▸ hlf_lt) hnz⟩)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
