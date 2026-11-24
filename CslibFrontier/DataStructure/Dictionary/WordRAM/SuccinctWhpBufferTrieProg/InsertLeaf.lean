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
# Internal Leaf Commit Helpers (`bufInsertLeafRtProg`)

Internal leaf-item allocation and active-item update subroutine consumed privately by `Insert`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufInsertLeafRtProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BufInsertLeafPre`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufInsertLeafRt`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufInsertLeafRtProg_spec`
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

/-- Write `(itemLeaf id, itemBucket id, itemLoc id) := (leaf, b, loc)` for `id < qEp`
(`d = (((rt, id), leaf), (b, loc))`). -/
@[irreducible] private def bufWriteItemTripleRtProg
    (d : ((BufRt × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1.1.1
  let id ← pure d.1.1.2
  let idxB ← pure (brQEp rt + id)
  let idxL ← pure (2 * brQEp rt + id)
  writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), id), d.1.2)
  writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxB), d.2.1)
  writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxL), d.2.2)

private theorem realizes_bufWriteItemTripleRt :
    Realizes .exact bufWriteItemTripleRtProg
      (WordEncoding.encode (α := ((BufRt × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1.1.1 ∧ d.1.1.2 < brQEp d.1.1.1)
      (fun _ _ => 0) := by
  unfold bufWriteItemTripleRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨⟨⟨rt, id⟩, leaf⟩, ⟨b, loc⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hid⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brQEp] at hid ⊢
    obtain ⟨_, _, _, _, _, hq6_le⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_items_safe henv hep (by omega)

private theorem bufWriteItemTripleRtProg_spec {c U V w n_max base ep id leaf b loc : ℕ}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hid : id < qEpochWhp n_max)
    (hleaf : leaf < maxTrieNodesWhp c n_max)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := bufWriteItemTripleRtProg (((rt, id), leaf), (b, loc))
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem ∧
    readPacked (base + brOffItems rt) (globalPtrBits n_max) w s'.mem id = leaf ∧
    readPacked (base + brOffItems rt) (globalPtrBits n_max) w s'.mem
      (qEpochWhp n_max + id) = b ∧
    readPacked (base + brOffItems rt) (globalPtrBits n_max) w s'.mem
      (2 * qEpochWhp n_max + id) = loc ∧
    (∀ idx < 6 * qEpochWhp n_max + 6,
      idx ≠ id → idx ≠ qEpochWhp n_max + id → idx ≠ 2 * qEpochWhp n_max + id →
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, a < base + brOffItems rt ∨
      base + brOffItems rt +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hi_seg := (rt_seg_le c U V w n_max base ep hep).2.2.2.2
  obtain ⟨_, _, htl_lt, _, _, hmt_lt, _, _⟩ := large_bounds_lt_n_max hth
  have hM_le := henv.numBuckets_le_n_max
  have hlf_g : leaf < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hb_g : b < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hloc_g : loc < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  set qEp := qEpochWhp n_max
  have hi0 : id < 6 * qEp + 6 := by omega
  have hi1 : qEp + id < 6 * qEp + 6 := by omega
  have hi2 : 2 * qEp + id < 6 * qEp + 6 := by omega
  have hpos_q : 0 < qEp := by unfold qEp qEpochWhp; have := slabScale_pos n_max; positivity
  set rt := mkBufRt c U V w n_max base ep
  unfold bufWriteItemTripleRtProg
  simp only [pure_bind]
  set m1 := writePacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem id leaf
  set m2 := writePacked (base + brOffItems rt) (globalPtrBits n_max) w m1 (qEp + id) b
  set m3 := writePacked (base + brOffItems rt) (globalPtrBits n_max) w m2 (2 * qEp + id) loc
  have hs'_eq : (Memory.spec 0).clientState s
      (writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), id), leaf) >>=
        fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), brQEp rt + id), b) >>= fun _ =>
            writePackedGenProg
              ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), 2 * brQEp rt + id), loc)) =
      { mem := m3, frontier := s.frontier } := rfl
  rw [hs'_eq]
  refine ⟨rfl, rfl, ?_,
    ((bufEpFrame_writeItems_lt3q hw hep (by omega)).trans
      (bufEpFrame_writeItems_lt3q hw hep (by omega))).trans
      (bufEpFrame_writeItems_lt3q hw hep (by omega)),
    ?_, ?_, readPacked_writePacked_self _ _ _ m2 (2 * qEp + id) hloc_g,
    fun idx _ hn0 hn1 hn2 => ?_, fun a ha => ?_⟩
  · refine validProg_bind (validProg_writePacked hw hgk hi0 hi_seg) ?_
    rw [clientState_writePackedGen]
    refine validProg_bind (validProg_writePacked hw hgk hi1 hi_seg) ?_
    rw [clientState_writePackedGen]
    exact validProg_writePacked hw hgk hi2 hi_seg
  · exact (readPacked_writePacked_of_ne hw m2 (by omega) loc).trans
      ((readPacked_writePacked_of_ne hw m1 (by omega) b).trans
        (readPacked_writePacked_self _ _ _ s.mem id hlf_g))
  · exact (readPacked_writePacked_of_ne hw m2 (by omega) loc).trans
      (readPacked_writePacked_self _ _ _ m1 (qEp + id) hb_g)
  · exact (readPacked_writePacked_of_ne hw m2 hn2 loc).trans
      ((readPacked_writePacked_of_ne hw m1 hn1 b).trans
        (readPacked_writePacked_of_ne hw s.mem hn0 leaf))
  · exact (writePacked_outside hw _ hi2 _ (by cases ha <;> omega)).trans
      ((writePacked_outside hw _ hi1 _ (by cases ha <;> omega)
        ).trans (writePacked_outside hw _ hi0 _ (by cases ha <;> omega)))

/-- Fresh-slot branch of `bufInsert` (`id1 = 0`, `d = ((rt, leaf), (b, loc))`). -/
@[irreducible] private def bufInsertFreshRtProg
    (d : (BufRt × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1.1
  let leaf ← pure d.1.2
  let addrIA ← pure (brBase rt + brHdrIA rt)
  let id ← Memory.read addrIA
  let id1 ← pure (id + 1)
  Memory.write addrIA id1
  let idxLI ← pure (4 * leaf + 2)
  let idxAct ← pure (4 * leaf + 3)
  let one_v ← pure 1
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI), id1)
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct), one_v)
  bufWriteItemTripleRtProg (((rt, id), leaf), d.2)

private theorem realizes_bufInsertFreshRt :
    Realizes .exact bufInsertFreshRtProg
      (WordEncoding.encode (α := (BufRt × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d s => BufRtEnvGen w d.1.1 ∧ d.1.2 < brMaxNodes d.1.1 ∧
        s.mem (brBase d.1.1 + brHdrIA d.1.1) < brQEp d.1.1)
      (fun _ _ => 0) := by
  unfold bufInsertFreshRtProg
  have hwp := realizes_writePackedGen
  have hwt := realizes_bufWriteItemTripleRt
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  have hcr_r : ∀ a s', (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a := fun _ _ => rfl
  have hcs_w : ∀ a v s', (Memory.spec 0).clientState s' (Memory.write a v) =
      { mem := Function.update s'.mem a v, frontier := s'.frontier } := fun _ _ _ => rfl
  have hcs_wp : ∀ x s', (Memory.spec 0).clientState s' (writePackedGenProg x) =
      { mem := writePacked (x.1.1.1.1 + x.1.1.1.2) x.1.1.2.1 x.1.1.2.2 s'.mem x.1.2 x.2,
        frontier := s'.frontier } := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨⟨rt, leaf⟩, ⟨b, loc⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hleaf, hid_lt⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes, brQEp, brBase, brHdrIA] at hleaf hid_lt ⊢
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    have hia32 : brHdrIA (mkBufRt c U V w n_max base ep) < 32 :=
      (rt_disj_le c U V w n_max base ep hep).2.1
    simp only [hcs_r, hcr_r, hcs_w, hcs_wp] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr hia32
    | exact henv.fits_of_le_n_max (by dsimp [mkBufRt, brBase, brHdrIA] at *; omega)
    | exact rt_meta_safe henv hep (by omega)
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brBase, brHdrIA, brQEp] at *; omega)

/-- Existing-slot branch of `bufInsert` (`id1 ≠ 0`, `id = id1 - 1 < qEp`,
`d = (((rt, leaf), id), (b, loc))`). -/
@[irreducible] private def bufInsertUpdRtProg
    (d : ((BufRt × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1.1.1
  let leaf ← pure d.1.1.2
  let id ← pure d.1.2
  let idxAct ← pure (4 * leaf + 3)
  let idxB ← pure (brQEp rt + id)
  let idxL ← pure (2 * brQEp rt + id)
  let one_v ← pure 1
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct), one_v)
  writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxB), d.2.1)
  writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxL), d.2.2)

private theorem realizes_bufInsertUpdRt :
    Realizes .exact bufInsertUpdRtProg
      (WordEncoding.encode (α := ((BufRt × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1.1.1 ∧ d.1.1.2 < brMaxNodes d.1.1.1 ∧
        d.1.2 < brQEp d.1.1.1)
      (fun _ _ => 0) := by
  unfold bufInsertUpdRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨⟨⟨rt, leaf⟩, id⟩, ⟨b, loc⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hleaf, hid⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes, brQEp] at hleaf hid ⊢
    obtain ⟨_, _, _, _, htm_le, hq6_le⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)
    | exact rt_items_safe henv hep (by omega)

/-- Leaf completion helper for `bufInsert` (`d = ((rt, leaf), (b, loc))`). -/
@[irreducible] def bufInsertLeafRtProg :
    (BufRt × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((rt, leaf), b_loc) => do
    let idxLI ← pure (4 * leaf + 2)
    let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
    if id1 = 0 then
      bufInsertFreshRtProg ((rt, leaf), b_loc)
    else
      let id ← pure (id1 - 1)
      bufInsertUpdRtProg (((rt, leaf), id), b_loc)

/-- Precondition for `bufInsertLeafRtProg`. -/
@[expose] def BufInsertLeafPre (w : ℕ) :
    (BufRt × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((rt, leaf), _), s =>
    ∃ c U V w₀ n_max base ep tr,
      WhpLargeEnv c U V w₀ n_max w base ∧ (ep = 0 ∨ ep = 1) ∧
      rt = mkBufRt c U V w₀ n_max base ep ∧
      BufTrieMemRep base c U V w₀ n_max ep tr s.mem ∧
      leaf < tr.nodeAlloc ∧
      tr.itemAlloc < qEpochWhp n_max ∧
      tr.nodeLeafItem leaf ≤ tr.itemAlloc

theorem realizes_bufInsertLeafRt :
    Realizes .exact bufInsertLeafRtProg
      (WordEncoding.encode (α := (BufRt × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      BufInsertLeafPre
      (fun _ _ => 0) := by
  unfold bufInsertLeafRtProg
  have hrp := realizes_readPackedGen
  have hfr := realizes_bufInsertFreshRt
  have hup := realizes_bufInsertUpdRt
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨⟨rt, leaf⟩, ⟨b, loc⟩⟩
    obtain ⟨c, U, V, w₀, n_max, base, ep, tr, henv, hep, rfl, hrep, hleaf, hia_lt, hli_le⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hna_max := hrep.1
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    have hrep_li : readPacked (base + brOffMeta (mkBufRt c U V w n_max base ep))
        (globalPtrBits n_max) w s.mem (4 * leaf + 2) = tr.nodeLeafItem leaf := by
      have hm := hrep.2.2.2.2.2.2.1 leaf hleaf
      rcases hep with rfl | rfl <;> exact hm.1
    have hmem_ia : s.mem (base + brHdrIA (mkBufRt c U V w n_max base ep)) = tr.itemAlloc := by
      have hi := hrep.2.2.2.1
      rcases hep with rfl | rfl <;> exact hi
    first
    | (dsimp only; exact rt_meta_safe henv hep (by omega))
    | (simp only [hcs] at *
       simp only [mkBufRt, brBase, brOffMeta, brGBits, brW, brMaxNodes, brHdrIA, brQEp,
         clientResult_readPackedGen] at *
       rw [hrep_li] at *
       rw [hmem_ia] at *
       have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
       first
       | exact henv.fits_const (by decide)
       | exact henv.fits_of_le_n_max (by omega)
       | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
       | omega)

theorem bufInsertLeafRtProg_spec {c U V w n_max base ep leaf b loc : ℕ}
    {tr1 : BufTrie} {s1 : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr1 s1.mem)
    (hlf_lt : leaf < tr1.nodeAlloc)
    (hia_lt : tr1.itemAlloc < qEpochWhp n_max)
    (hli_le : tr1.nodeLeafItem leaf ≤ tr1.itemAlloc)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := bufInsertLeafRtProg ((rt, leaf), (b, loc))
    let id1 := tr1.nodeLeafItem leaf
    let tr' : BufTrie :=
      if id1 = 0 then
        let id := tr1.itemAlloc
        { tr1 with
          itemAlloc := id + 1
          nodeLeafItem := Function.update tr1.nodeLeafItem leaf (id + 1)
          nodeActive := Function.update tr1.nodeActive leaf 1
          itemLeaf := Function.update tr1.itemLeaf id leaf
          itemBucket := Function.update tr1.itemBucket id b
          itemLoc := Function.update tr1.itemLoc id loc }
      else
        let id := id1 - 1
        { tr1 with
          nodeActive := Function.update tr1.nodeActive leaf 1
          itemBucket := Function.update tr1.itemBucket id b
          itemLoc := Function.update tr1.itemLoc id loc }
    let s' := (Memory.spec 0).clientState s1 prog
    s'.frontier = s1.frontier ∧
    memoryCost prog s1 ≤ 24 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s1 prog ∧
    BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
    BufEpFrame base c U V w n_max ep s1.mem s'.mem := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hia_lt_sp, _, hm_seg, hi_seg⟩ :
      base + brHdrNA rt < base + largeSpaceWhp c U V w n_max ∧
      base + brHdrIA rt < base + largeSpaceWhp c U V w n_max ∧
      base + brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max ∧
      base + brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max ∧
      base + brOffItems rt + packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max := rt_seg_le c U V w n_max base ep hep
  obtain ⟨hna32, hia32, hna_ne_ia, h32_c, hc_le_m, hm_le_i⟩ :
      brHdrNA rt < 32 ∧ brHdrIA rt < 32 ∧ brHdrNA rt ≠ brHdrIA rt ∧ 32 ≤ brOffChild rt ∧
      brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffMeta rt ∧
      brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffItems rt := rt_disj_le c U V w n_max base ep hep
  obtain ⟨hM_ge, _, htl_lt, _, _, _, hq_lt, _⟩ := large_bounds_lt_n_max hth
  have hM_le := henv.numBuckets_le_n_max
  have hna_max := hrep.1
  have hlf_max : leaf < maxTrieNodesWhp c n_max := hlf_lt.trans_le hna_max
  have hidx2 : 4 * leaf + 2 < 6 * maxTrieNodesWhp c n_max := by omega
  have hidx3 : 4 * leaf + 3 < 6 * maxTrieNodesWhp c n_max := by omega
  have h1_g : 1 < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hrep_li : readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s1.mem (4 * leaf + 2) =
      tr1.nodeLeafItem leaf := ((bufTrieMemRep_iff_rt.mp hrep).2.2.2.2.2.2.1 leaf hlf_lt).1
  have hmem_ia : s1.mem (base + brHdrIA rt) = tr1.itemAlloc :=
    (bufTrieMemRep_iff_rt.mp hrep).2.2.2.1
  dsimp only
  unfold bufInsertLeafRtProg
  simp only [pure_bind]
  by_cases hid1 : tr1.nodeLeafItem leaf = 0
  · rw [ite_eq_left hid1]
    set id := tr1.itemAlloc
    have hid1_fit : Fits w (id + 1) := henv.fits_of_le_n_max (by omega)
    have hid1_g : id + 1 < 2 ^ globalPtrBits n_max :=
      lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    set sa : Memory.State :=
      { mem := Function.update s1.mem (base + brHdrIA rt) (id + 1), frontier := s1.frontier }
    set sb : Memory.State :=
      { mem := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w sa.mem
          (4 * leaf + 2) (id + 1),
        frontier := s1.frontier }
    set sc : Memory.State :=
      { mem := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w sb.mem (4 * leaf + 3) 1,
        frontier := s1.frontier }
    have ht_spec := bufWriteItemTripleRtProg_spec henv hep hia_lt hlf_max hb hloc (s := sc)
    dsimp only at ht_spec
    change _ ∧ _ ∧ _ ∧ _ ∧
      readPacked (base + brOffItems rt) _ _ _ _ = _ ∧
      readPacked (base + brOffItems rt) _ _ _ _ = _ ∧
      readPacked (base + brOffItems rt) _ _ _ _ = _ ∧
      (∀ idx < 6 * qEpochWhp n_max + 6, _ → _ → _ →
        readPacked (base + brOffItems rt) _ _ _ _ = readPacked (base + brOffItems rt) _ _ _ _) ∧
      (∀ a, a < base + brOffItems rt ∨
        base + brOffItems rt + packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤ a →
        _ = _) at ht_spec
    obtain ⟨hfr_t, hmc_t, hvp_t, hbfr_t, hit0, hit1, hit2, hit_oth, hit_out⟩ := ht_spec
    set sd := (Memory.spec 0).clientState sc (bufWriteItemTripleRtProg (((rt, id), leaf), (b, loc)))
    have hs'_eq : (Memory.spec 0).clientState s1
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) = sd := by
      rw [clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen]
      change (Memory.spec 0).clientState s1
        (if readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s1.mem (4 * leaf + 2) = 0
         then _ else _) = sd
      rw [hrep_li, ite_eq_left hid1]
      unfold bufInsertFreshRtProg
      simp only [pure_bind]
      rw [clientState_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, clientState_bind,
        clientState_memWrite, clientState_bind, clientState_writePackedGen,
        clientState_bind, clientState_writePackedGen]
      rfl
    have hmc_all : memoryCost
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) s1 ≤ 24 := by
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [clientState_readPackedGen, clientResult_readPackedGen, memoryCost_readPackedGen]
      change 2 + memoryCost
        (if readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s1.mem (4 * leaf + 2) = 0
         then _ else _) s1 ≤ 24
      rw [hrep_li, ite_eq_left hid1]
      unfold bufInsertFreshRtProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_ia,
        memoryCost_memRead_and_write.1, clientState_memWrite, memoryCost_memRead_and_write.2,
        clientState_writePackedGen, memoryCost_writePackedGen,
        clientState_writePackedGen, memoryCost_writePackedGen]
      change 2 + (1 + (1 + (4 + (4 + memoryCost _ sc)))) ≤ 24
      rw [hmc_t]
    have hvp_all : ValidProg w (base + largeSpaceWhp c U V w n_max) s1
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) := by
      refine validProg_bind (validProg_readPacked hw hidx2 hm_seg) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen]
      change ValidProg _ _ s1
        (if readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s1.mem (4 * leaf + 2) = 0
         then _ else _)
      rw [hrep_li, ite_eq_left hid1]
      unfold bufInsertFreshRtProg
      simp only [pure_bind]
      refine validProg_bind (validProg_read hia_lt_sp) ?_
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_ia]
      refine validProg_bind (validProg_write hia_lt_sp hid1_fit) ?_
      rw [clientState_memWrite]
      refine validProg_bind (validProg_writePacked hw hgk hidx2 hm_seg) ?_
      rw [clientState_writePackedGen]
      refine validProg_bind (validProg_writePacked hw hgk hidx3 hm_seg) ?_
      rw [clientState_writePackedGen]
      exact hvp_t
    rw [hs'_eq]
    have hbfr_all : BufEpFrame base c U V w n_max ep s1.mem sd.mem :=
      (((bufEpFrame_write_hdrIA hw hep).trans (bufEpFrame_writeMeta hw hep hidx2)).trans
        (bufEpFrame_writeMeta hw hep hidx3)).trans hbfr_t
    refine ⟨hfr_t, hmc_all, hvp_all, ?_, hbfr_all⟩
    have hsd_na : sd.mem (base + brHdrNA rt) = s1.mem (base + brHdrNA rt) := by
      rw [hit_out _ (Or.inl (by omega))]
      dsimp only [sc, sb, sa]
      rw [writePacked_outside hw _ hidx3 _ (by omega),
        writePacked_outside hw _ hidx2 _ (by omega),
        Function.update_of_ne (by omega)]
    have hsd_ia : sd.mem (base + brHdrIA rt) = id + 1 := by
      rw [hit_out _ (Or.inl (by omega))]
      dsimp only [sc, sb, sa]
      rw [writePacked_outside hw _ hidx3 _ (by omega),
        writePacked_outside hw _ hidx2 _ (by omega),
        Function.update_self]
    have hsd_ch : ∀ u < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
        readPacked (base + brOffChild rt) (globalPtrBits n_max) w sd.mem
          (u * 2 ^ bCharWhp n_max + c') =
          readPacked (base + brOffChild rt) (globalPtrBits n_max) w s1.mem
            (u * 2 ^ bCharWhp n_max + c') := by
      intro u hu c' hc'
      have hidx_c : u * 2 ^ bCharWhp n_max + c' < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + c'
            < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hc' _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      have h_dc : readPacked (base + brOffChild rt) (globalPtrBits n_max) w sd.mem
          (u * 2 ^ bCharWhp n_max + c') =
          readPacked (base + brOffChild rt) (globalPtrBits n_max) w sc.mem
            (u * 2 ^ bCharWhp n_max + c') :=
        readPacked_congr hw (hidx := hidx_c) fun a ⟨ha1, ha2⟩ => hit_out a (Or.inl (by omega))
      rw [h_dc]
      dsimp only [sc, sb, sa]
      exact (readPacked_writePacked_disjoint hw hidx_c hidx3 (Or.inl (by omega))).trans
        ((readPacked_writePacked_disjoint hw hidx_c hidx2 (Or.inl (by omega))).trans
          (readPacked_update_outside hw hidx_c (Or.inl (by omega))))
    have hsd_meta_dc : ∀ idx < 6 * maxTrieNodesWhp c n_max,
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w sd.mem idx =
          readPacked (base + brOffMeta rt) (globalPtrBits n_max) w sc.mem idx :=
      fun idx hidx => readPacked_congr hw (hidx := hidx) fun a ⟨_,
        ha2⟩ => hit_out a (Or.inl (by omega))
    have hsc_items : ∀ idx < 6 * qEpochWhp n_max + 6,
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w sc.mem idx =
          readPacked (base + brOffItems rt) (globalPtrBits n_max) w s1.mem idx := by
      intro idx hidx
      dsimp only [sc, sb, sa]
      exact (readPacked_writePacked_disjoint hw hidx hidx3 (Or.inr (by omega))).trans
        ((readPacked_writePacked_disjoint hw hidx hidx2 (Or.inr (by omega))).trans
          (readPacked_update_outside hw hidx (Or.inl (by omega))))
    obtain ⟨hna, _, hhna, _, hch, hpar, hlf, hit⟩ := bufTrieMemRep_iff_rt.mp hrep
    rw [bufTrieMemRep_iff_rt]
    dsimp only
    refine ⟨hna, by omega, hsd_na.trans hhna, hsd_ia,
      fun u hu c' hc' => (hsd_ch u hu c' hc').trans (hch u hu c' hc'),
      fun u hu1 hu => ?_, fun u hu => ?_, fun j hj => ?_⟩
    · rw [hsd_meta_dc _ (by omega), hsd_meta_dc _ (by omega)]
      dsimp only [sc, sb, sa]
      exact ⟨(readPacked_writePacked_of_ne hw _ (by omega) 1).trans
          ((readPacked_writePacked_of_ne hw _ (by omega) (id + 1)).trans
            ((readPacked_update_outside hw
                (show 4 * u < 6 * maxTrieNodesWhp c n_max by omega) (Or.inl (by omega))).trans
              (hpar u hu1 hu).1)),
        (readPacked_writePacked_of_ne hw _ (by omega) 1).trans
          ((readPacked_writePacked_of_ne hw _ (by omega) (id + 1)).trans
            ((readPacked_update_outside hw
                (show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega) (Or.inl (by omega))).trans
              (hpar u hu1 hu).2))⟩
    · rw [hsd_meta_dc _ (by omega)]
      by_cases hul : u = leaf
      · subst hul
        simp only [Function.update_self]
        dsimp only [sc, sb]
        refine ⟨(readPacked_writePacked_of_ne hw sb.mem (by omega) 1).trans
          (readPacked_writePacked_self _ _ _ sa.mem (4 * u + 2) hid1_g), fun _ => ?_⟩
        rw [hsd_meta_dc _ (by omega)]
        exact readPacked_writePacked_self _ _ _ sb.mem (4 * u + 3) h1_g
      · simp only [Function.update_of_ne hul]
        dsimp only [sc, sb, sa]
        refine ⟨(readPacked_writePacked_of_ne hw _ (by omega) 1).trans
          ((readPacked_writePacked_of_ne hw _ (by omega) (id + 1)).trans
            ((readPacked_update_outside hw
                (show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega) (Or.inl (by omega))).trans
              (hlf u hu).1)), fun hnz => ?_⟩
        rw [hsd_meta_dc _ (by omega)]
        dsimp only [sc, sb, sa]
        exact (readPacked_writePacked_of_ne hw _ (by omega) 1).trans
          ((readPacked_writePacked_of_ne hw _ (by omega) (id + 1)).trans
            ((readPacked_update_outside hw
                (show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega) (Or.inl (by omega))).trans
              ((hlf u hu).2 hnz)))
    · by_cases hji : j = id
      · subst hji
        simp only [Function.update_self]
        exact ⟨hit0, hit1, hit2⟩
      · have hj_lt : j < id := by omega
        simp only [Function.update_of_ne hji]
        exact ⟨(hit_oth _ (by omega) hji (by omega) (by omega)).trans
            ((hsc_items _ (by omega)).trans (hit j hj_lt).1),
          (hit_oth _ (by omega) (by omega) (by omega) (by omega)).trans
            ((hsc_items _ (by omega)).trans (hit j hj_lt).2.1),
          (hit_oth _ (by omega) (by omega) (by omega) (by omega)).trans
            ((hsc_items _ (by omega)).trans (hit j hj_lt).2.2)⟩
  · rw [ite_eq_right hid1]
    set id := tr1.nodeLeafItem leaf - 1
    have hid_ia : id < tr1.itemAlloc := by omega
    have hid_q : id < qEpochWhp n_max := hid_ia.trans hia_lt
    have hb_g : b < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    have hloc_g : loc < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    set qEp := qEpochWhp n_max
    have hiB : qEp + id < 6 * qEp + 6 := by omega
    have hiL : 2 * qEp + id < 6 * qEp + 6 := by omega
    set ma := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w s1.mem (4 * leaf + 3) 1
    set mb := writePacked (base + brOffItems rt) (globalPtrBits n_max) w ma (qEp + id) b
    set mc := writePacked (base + brOffItems rt) (globalPtrBits n_max) w mb (2 * qEp + id) loc
    have hs'_eq : (Memory.spec 0).clientState s1
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) =
        { mem := mc, frontier := s1.frontier } := by
      rw [clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl,
        hrep_li, ite_eq_right hid1]
      unfold bufInsertUpdRtProg
      simp only [pure_bind]
      rw [clientState_bind, clientState_writePackedGen,
        clientState_bind, clientState_writePackedGen,
        clientState_writePackedGen]
      rfl
    have hmc_all : memoryCost
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) s1 ≤ 24 := by
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [clientState_readPackedGen, clientResult_readPackedGen, memoryCost_readPackedGen,
        show brBase rt = base from rfl, show brGBits rt = globalPtrBits n_max from rfl,
        show brW rt = w from rfl, hrep_li, ite_eq_right hid1]
      unfold bufInsertUpdRtProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_writePackedGen]
      omega
    have hvp_all : ValidProg w (base + largeSpaceWhp c U V w n_max) s1
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) := by
      refine validProg_bind (validProg_readPacked hw hidx2 hm_seg) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen,
        show brBase rt = base from rfl, show brGBits rt = globalPtrBits n_max from rfl,
        show brW rt = w from rfl, hrep_li, ite_eq_right hid1]
      unfold bufInsertUpdRtProg
      simp only [pure_bind]
      refine validProg_bind (validProg_writePacked hw hgk hidx3 hm_seg) ?_
      rw [clientState_writePackedGen]
      refine validProg_bind (validProg_writePacked hw hgk hiB hi_seg) ?_
      rw [clientState_writePackedGen]
      exact validProg_writePacked hw hgk hiL hi_seg
    rw [hs'_eq]
    have hbfr_all : BufEpFrame base c U V w n_max ep s1.mem mc :=
      ((bufEpFrame_writeMeta hw hep hidx3).trans
        (bufEpFrame_writeItems_lt3q hw hep (by omega))).trans
        (bufEpFrame_writeItems_lt3q hw hep (by omega))
    refine ⟨rfl, hmc_all, hvp_all, ?_, hbfr_all⟩
    have hmc_hdr : ∀ h < 32, mc (base + h) = s1.mem (base + h) := fun h hh =>
      (writePacked_outside hw _ hiL _ (by omega)).trans
        ((writePacked_outside hw _ hiB _ (by omega)).trans
          (writePacked_outside hw _ hidx3 _ (by omega)))
    have hmc_ch : ∀ u < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
        readPacked (base + brOffChild rt) (globalPtrBits n_max) w mc
          (u * 2 ^ bCharWhp n_max + c') =
          readPacked (base + brOffChild rt) (globalPtrBits n_max) w s1.mem
            (u * 2 ^ bCharWhp n_max + c') := by
      intro u hu c' hc'
      have hidx_c : u * 2 ^ bCharWhp n_max + c' < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + c'
            < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hc' _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      exact (readPacked_writePacked_disjoint hw hidx_c hiL (Or.inl (by omega))).trans
        ((readPacked_writePacked_disjoint hw hidx_c hiB (Or.inl (by omega))).trans
          (readPacked_writePacked_disjoint hw hidx_c hidx3 (Or.inl (by omega))))
    have hmc_meta : ∀ idx < 6 * maxTrieNodesWhp c n_max,
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w mc idx =
          readPacked (base + brOffMeta rt) (globalPtrBits n_max) w ma idx := fun idx hidx =>
      (readPacked_writePacked_disjoint hw hidx hiL (Or.inl (by omega))).trans
        (readPacked_writePacked_disjoint hw hidx hiB (Or.inl (by omega)))
    have hma_items : ∀ idx < 6 * qEp + 6,
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w ma idx =
          readPacked (base + brOffItems rt) (globalPtrBits n_max) w s1.mem idx := fun idx hidx =>
      readPacked_writePacked_disjoint hw hidx hidx3 (Or.inr (by omega))
    obtain ⟨hna, hia, hhna, hhia, hch, hpar, hlf, hit⟩ := bufTrieMemRep_iff_rt.mp hrep
    rw [bufTrieMemRep_iff_rt]
    dsimp only
    refine ⟨hna, hia,
      (hmc_hdr _ hna32).trans hhna,
      (hmc_hdr _ hia32).trans hhia,
      fun u hu c' hc' => (hmc_ch u hu c' hc').trans (hch u hu c' hc'),
      fun u hu1 hu => ?_, fun u hu => ?_, fun j hj => ?_⟩
    · rw [hmc_meta _ (by omega), hmc_meta _ (by omega)]
      exact ⟨(readPacked_writePacked_of_ne hw s1.mem (by omega) 1).trans (hpar u hu1 hu).1,
        (readPacked_writePacked_of_ne hw s1.mem (by omega) 1).trans (hpar u hu1 hu).2⟩
    · rw [hmc_meta _ (by omega)]
      by_cases hul : u = leaf
      · subst hul
        simp only [Function.update_self]
        refine ⟨(readPacked_writePacked_of_ne hw s1.mem (by omega) 1).trans (hlf u hu).1,
          fun _ => ?_⟩
        rw [hmc_meta _ (by omega)]
        exact readPacked_writePacked_self _ _ _ s1.mem (4 * u + 3) h1_g
      · simp only [Function.update_of_ne hul]
        refine ⟨(readPacked_writePacked_of_ne hw s1.mem (by omega) 1).trans (hlf u hu).1,
          fun hnz => ?_⟩
        rw [hmc_meta _ (by omega)]
        exact (readPacked_writePacked_of_ne hw s1.mem (by omega) 1).trans ((hlf u hu).2 hnz)
    · have hj0 : readPacked (base + brOffItems rt) (globalPtrBits n_max) w mc j = tr1.itemLeaf j :=
        ((readPacked_writePacked_of_ne hw mb (by omega) loc).trans
          ((readPacked_writePacked_of_ne hw ma (by omega) b).trans
            (hma_items _ (by omega)))).trans (hit j hj).1
      by_cases hji : j = id
      · subst hji
        simp only [Function.update_self]
        exact ⟨hj0,
          (readPacked_writePacked_of_ne hw mb (by omega) loc).trans
            (readPacked_writePacked_self _ _ _ ma (qEp + id) hb_g),
          readPacked_writePacked_self _ _ _ mb (2 * qEp + id) hloc_g⟩
      · simp only [Function.update_of_ne hji]
        exact ⟨hj0,
          ((readPacked_writePacked_of_ne hw mb (by omega) loc).trans
            ((readPacked_writePacked_of_ne hw ma (by omega) b).trans
              (hma_items _ (by omega)))).trans (hit j hj).2.1,
          ((readPacked_writePacked_of_ne hw mb (by omega) loc).trans
            ((readPacked_writePacked_of_ne hw ma (by omega) b).trans
              (hma_items _ (by omega)))).trans (hit j hj).2.2⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
