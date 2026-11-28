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
import CslibFrontier.Tactic.Realize

/-!
# Parameter-Free `bufCheckSlotGenProg` Subroutine

Certified `O_c(1)` `bufCheckSlot` verification reading `itemBucket id`, `itemLoc id`, and
`nodeActive leaf` for a log entry `id` without mutating memory.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufCheckSlotGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufCheckSlotGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufCheckSlotGen`
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

/-- Leaf check helper for `bufCheckSlot` (`d = ((rt, id), leaf)` with `id < qEp`,
`leaf < maxNodes`). -/
@[irreducible] private def bufCheckSlotLeafRtProg
    (d : (BufRt × ℕ) × ℕ) : Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt := d.1.1
  let id ← pure d.1.2
  let leaf ← pure d.2
  let idxLI ← pure (4 * leaf + 2)
  let li ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
  let id1 ← pure (id + 1)
  if li = id1 then
    let idxAct ← pure (4 * leaf + 3)
    let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
    if act = 0 then
      pure (0, (0, 0))
    else
      bufReadItemPairRtProg (rt, id)
  else
    pure (0, (0, 0))

private theorem bufCheckSlotLeafRtProg_eq (d : (BufRt × ℕ) × ℕ) :
    bufCheckSlotLeafRtProg d = (do
      let rt := d.1.1
      let id ← pure d.1.2
      let leaf ← pure d.2
      let idxLI ← pure (4 * leaf + 2)
      let li ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
      let id1 ← pure (id + 1)
      if li = id1 then
        let idxAct ← pure (4 * leaf + 3)
        let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
        if act = 0 then
          pure (0, (0, 0))
        else
          bufReadItemPairRtProg (rt, id)
      else
        pure (0, (0, 0))) := by
  unfold bufCheckSlotLeafRtProg; rfl

private theorem realizes_bufCheckSlotLeafRt :
    Realizes .exact bufCheckSlotLeafRtProg
      (WordEncoding.encode (α := (BufRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w d _ => BufRtEnvGen w d.1.1 ∧ d.1.2 < brQEp d.1.1 ∧ d.2 < brMaxNodes d.1.1)
      (fun _ _ => 0) := by
  unfold bufCheckSlotLeafRtProg
  have hrp := realizes_readPackedGen
  have hrip := realizes_bufReadItemPairRt
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨⟨rt, id⟩, leaf⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hid, hleaf⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brQEp, brMaxNodes] at hid hleaf ⊢
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | exact hid

/-- In-bounds helper for `bufCheckSlot` (`d = (rt, id)` with `id < qEp`). -/
@[irreducible] private def bufCheckSlotInBoundsRtProg
    (d : BufRt × ℕ) : Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt := d.1
  let id ← pure d.2
  let leaf ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), id)
  let addrNA ← pure (brBase rt + brHdrNA rt)
  let na ← Memory.read addrNA
  if leaf < na then
    bufCheckSlotLeafRtProg ((rt, id), leaf)
  else
    pure (0, (0, 0))

private theorem bufCheckSlotInBoundsRtProg_eq (d : BufRt × ℕ) :
    bufCheckSlotInBoundsRtProg d = (do
      let rt := d.1
      let id ← pure d.2
      let leaf ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), id)
      let addrNA ← pure (brBase rt + brHdrNA rt)
      let na ← Memory.read addrNA
      if leaf < na then
        bufCheckSlotLeafRtProg ((rt, id), leaf)
      else
        pure (0, (0, 0))) := by
  unfold bufCheckSlotInBoundsRtProg; rfl

private theorem realizes_bufCheckSlotInBoundsRt :
    Realizes .exact bufCheckSlotInBoundsRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w d s => BufRtEnvGen w d.1 ∧ d.2 < brQEp d.1 ∧
        s.mem (brBase d.1 + brHdrNA d.1) ≤ brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufCheckSlotInBoundsRtProg
  have hrp := realizes_readPackedGen
  have hsl := realizes_bufCheckSlotLeafRt
  have hcs_p : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  have hcr_r : ∀ a s', (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, id⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hid, hna_le⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brQEp, brMaxNodes, brBase, brHdrNA] at hid hna_le ⊢
    obtain ⟨_, _, _, _, _, hq6_le⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
    have hna32 : brHdrNA (mkBufRt c U V w n_max base ep) < 32 :=
      (rt_disj_le c U V w n_max base ep hep).1
    simp only [hcs_p, hcs_r, hcr_r] at *
    first
    | exact henv.fits_hdr_addr hna32
    | exact rt_items_safe henv hep (by omega)
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | exact hid
    | (dsimp only [mkBufRt, brMaxNodes, brBase, brHdrNA] at *; omega)

/-- Parameter-free `bufCheckSlot` (`d = (((cp, base), ep), id)`), returning `(0, (0, 0))` on `none`
and `(1, (b, loc))` on `some (b, loc)`. -/
@[irreducible] def bufCheckSlotGenProg (d : ((WhpCoreParams × ℕ) × ℕ) × ℕ) :
    Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt ← mkBufRtGenProg d.1
  let addrIA ← pure (brBase rt + brHdrIA rt)
  let ia ← Memory.read addrIA
  if d.2 < ia then
    bufCheckSlotInBoundsRtProg (rt, d.2)
  else
    pure (0, (0, 0))

theorem bufCheckSlotGenProg_spec {c U V w n_max base ep id : ℕ}
    {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn) :
    let prog := bufCheckSlotGenProg (((mkWhpCoreParams c U V w n_max, base), ep), id)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match bufCheckSlot tr id with
       | none => (0, (0, 0))
       | some (b, loc) => (1, (b, loc))) ∧
    memoryCost prog s ≤ 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  obtain ⟨hna_lt_sp, hia_lt_sp, _, hm_seg, hi_seg⟩ := rt_seg_le c U V w n_max base ep hep
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
  obtain ⟨hna_max, hia_le, hmem_na, hmem_ia, -, -, hrep_meta, hrep_items⟩ :=
    bufTrieMemRep_iff_rt.mp hrep
  set rt := mkBufRt c U V w n_max base ep
  unfold bufCheckSlotGenProg
  simp only [pure_bind]
  dsimp only [bufCheckSlot]
  by_cases hid : id < tr.itemAlloc
  · obtain ⟨hlf_r, hb_r, hloc_r⟩ := hrep_items id hid
    set leaf := tr.itemLeaf id
    have hid6 : id < 6 * qEpochWhp n_max + 6 := by omega
    have hidB : brQEp rt + id < 6 * qEpochWhp n_max + 6 := by dsimp [rt, mkBufRt, brQEp]; omega
    have hidL : 2 * brQEp rt + id < 6 * qEpochWhp n_max + 6 := by dsimp [rt, mkBufRt, brQEp]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hrt_st, hrt_res,
        clientState_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, ite_eq_left hid, bufCheckSlotInBoundsRtProg_eq]
      simp only [pure_bind]
      rw [clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen, clientState_bind, clientState_memRead,
        clientResult_memRead]
      split_ifs with h1
      · rw [bufCheckSlotLeafRtProg_eq]
        simp only [pure_bind]
        rw [clientState_bind, clientState_readPackedGen]
        split_ifs with h2
        · rw [clientState_bind, clientState_readPackedGen]
          split_ifs with h3
          · rfl
          · rw [bufReadItemPairRtProg_eq]
            simp only [pure_bind]
            rw [clientState_bind, clientState_readPackedGen,
              clientState_bind, clientState_readPackedGen]
            rfl
        · rfl
      · rfl
    · rw [clientResult_bind, hrt_st, hrt_res,
        clientResult_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, ite_eq_left hid, ite_eq_left hid,
        bufCheckSlotInBoundsRtProg_eq]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedGen,
        clientResult_readPackedGen, clientResult_bind, clientState_memRead,
        clientResult_memRead, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl,
        show brW rt = w from rfl, hlf_r, hmem_na]
      by_cases hlf_lt : leaf < tr.nodeAlloc
      · rw [ite_eq_left hlf_lt, bufCheckSlotLeafRtProg_eq]
        simp only [pure_bind]
        rw [clientResult_bind, clientState_readPackedGen,
          clientResult_readPackedGen, show brBase rt = base from rfl,
          show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl]
        obtain ⟨hli_eq, hact_eq⟩ := hrep_meta leaf hlf_lt
        rw [hli_eq]
        by_cases hli_id : tr.nodeLeafItem leaf = id + 1
        · rw [ite_eq_left hli_id, clientResult_bind, clientState_readPackedGen,
            clientResult_readPackedGen, hact_eq (by omega)]
          by_cases hact0 : tr.nodeActive leaf = 0
          · simp [hli_id, hact0]
          · simp only [hli_id, hact0, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
            rw [bufReadItemPairRtProg_eq]
            simp only [pure_bind, clientResult_bind,
              clientResult_readPackedGen, StateTransitionSpec.clientResult_pure]
            exact Prod.ext rfl (Prod.ext hb_r hloc_r)
        · simp [hli_id]
      · rw [ite_eq_right hlf_lt]
        have hz := hv.bounds.2.1 leaf (Nat.not_lt.mp hlf_lt)
        simp [leaf, hz]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hrt_st, hrt_res, hrt_mc, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, memoryCost_memRead_and_write.1, ite_eq_left hid,
        bufCheckSlotInBoundsRtProg_eq]
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_readPackedGen, memoryCost_memRead_and_write.1]
      split_ifs with h1
      · rw [bufCheckSlotLeafRtProg_eq]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
          memoryCost_readPackedGen]
        split_ifs with h2
        · simp only [memoryCost_bind, memoryCost_readPackedGen]
          split_ifs with h3
          · change 0 + (1 + (2 + (1 + (2 + (2 + 0))))) ≤ 12; omega
          · rw [bufReadItemPairRtProg_eq]
            simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
              memoryCost_readPackedGen]
            change 0 + (1 + (2 + (1 + (2 + (2 + (2 + (2 + 0))))))) ≤ 12; omega
        · change 0 + (1 + (2 + (1 + (2 + 0)))) ≤ 12; omega
      · change 0 + (1 + (2 + (1 + 0))) ≤ 12; omega
    · refine validProg_bind hrt_vp ?_
      rw [hrt_st, hrt_res]
      refine validProg_bind (validProg_read hia_lt_sp) ?_
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_ia,
        ite_eq_left hid, bufCheckSlotInBoundsRtProg_eq]
      simp only [pure_bind]
      refine validProg_bind (validProg_readPacked hw hid6 hi_seg) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl, hlf_r]
      refine validProg_bind (validProg_read hna_lt_sp) ?_
      rw [clientState_memRead, clientResult_memRead, hmem_na]
      split_ifs with hlf_lt
      · rw [bufCheckSlotLeafRtProg_eq]
        simp only [pure_bind]
        refine validProg_bind
          (validProg_readPacked hw (show 4 * leaf + 2 < 6 * maxTrieNodesWhp c n_max by omega)
            hm_seg) ?_
        rw [clientState_readPackedGen]
        split_ifs with h2
        · refine validProg_bind
            (validProg_readPacked hw (show 4 * leaf + 3 < 6 * maxTrieNodesWhp c n_max by omega)
              hm_seg) ?_
          rw [clientState_readPackedGen]
          split_ifs with h3
          · exact validProg_pure _
          · rw [bufReadItemPairRtProg_eq]
            simp only [pure_bind]
            refine validProg_bind (validProg_readPacked hw hidB hi_seg) ?_
            rw [clientState_readPackedGen]
            exact validProg_bind (validProg_readPacked hw hidL hi_seg) (validProg_pure _)
        · exact validProg_pure _
      · exact validProg_pure _
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hrt_st, hrt_res,
        clientState_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, ite_eq_right hid]
      rfl
    · rw [clientResult_bind, hrt_st, hrt_res,
        clientResult_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, ite_eq_right hid, ite_eq_right hid]
      rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hrt_st, hrt_res, hrt_mc, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, memoryCost_memRead_and_write.1, ite_eq_right hid]
      change 0 + (1 + 0) ≤ 12; omega
    · refine validProg_bind hrt_vp ?_
      rw [hrt_st, hrt_res]
      refine validProg_bind (validProg_read hia_lt_sp) ?_
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_ia,
        ite_eq_right hid]
      exact validProg_pure _

theorem realizes_bufCheckSlotGen :
    Realizes .exact bufCheckSlotGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BufReadGenPre
      (fun _ _ => 0) := by
  unfold bufCheckSlotGenProg
  have hmrt := realizes_mkBufRtGen
  have hsib := realizes_bufCheckSlotInBoundsRt
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  have hcr_r : ∀ a s', (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, ep⟩, id⟩
    obtain ⟨c, U, V, w₀, n_max, tr, mapFn, henv, rfl, hep, hrep, _⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
    have hia32 : brHdrIA (mkBufRt c U V w n_max base ep) < 32 :=
      (rt_disj_le c U V w n_max base ep hep).2.1
    have hmem_na : s.mem (base + brHdrNA (mkBufRt c U V w n_max base ep)) = tr.nodeAlloc := by
      have hn := hrep.2.2.1; rcases hep with rfl | rfl <;> exact hn
    have hmem_ia : s.mem (base + brHdrIA (mkBufRt c U V w n_max base ep)) = tr.itemAlloc := by
      have hi := hrep.2.2.2.1; rcases hep with rfl | rfl <;> exact hi
    simp only [hrt_st, hrt_res, hcs_r, hcr_r] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact henv.fits_hdr_addr hia32
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brBase, brHdrIA, brHdrNA] at hmem_ia hmem_na
       simp only [mkBufRt, brBase, brHdrIA, brQEp, brHdrNA, brMaxNodes, hmem_na] at *
       simp only [hmem_ia] at *
       have := hrep.1
       have := hrep.2.1
       omega)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
