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
# Internal Path-Allocation Loop (`bufEnsureLoopGenProg`)

Internal node-allocating path builder shared privately with `Insert`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufEnsureLoopGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufEnsureLoopGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufEnsureLoop_spec`
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

/-- Write `(nodeParent u, nodeChar u, nodeLeafItem u) := (cur, ch, 0)` for a freshly allocated
trie node `u < maxNodes` (`d = ((rt, u), (cur, ch))`). -/
@[irreducible] private def bufAllocMetaRtProg (d : (BufRt × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1.1
  let u ← pure d.1.2
  let idx0 ← pure (4 * u)
  let idx1 ← pure (4 * u + 1)
  let idx2 ← pure (4 * u + 2)
  let zero_v ← pure 0
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idx0), d.2.1)
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idx1), d.2.2)
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idx2), zero_v)

private theorem realizes_bufAllocMetaRt :
    Realizes .exact bufAllocMetaRtProg
      (WordEncoding.encode (α := (BufRt × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1.1 ∧ d.1.2 < brMaxNodes d.1.1)
      (fun _ _ => 0) := by
  unfold bufAllocMetaRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨⟨rt, u⟩, ⟨cur, ch⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hu⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hu ⊢
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)

private theorem bufAllocMetaRtProg_spec {c U V w n_max base ep u cur ch : ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hu : u < maxTrieNodesWhp c n_max)
    (hcur : cur < maxTrieNodesWhp c n_max) (hch : ch < 2 ^ bCharWhp n_max) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := bufAllocMetaRtProg ((rt, u), (cur, ch))
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem ∧
    readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s'.mem (4 * u + 0) = cur ∧
    readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s'.mem (4 * u + 1) = ch ∧
    readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s'.mem (4 * u + 2) = 0 ∧
    (∀ idx < 6 * maxTrieNodesWhp c n_max,
      idx ≠ 4 * u → idx ≠ 4 * u + 1 → idx ≠ 4 * u + 2 →
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, a < base + brOffMeta rt ∨
      base + brOffMeta rt +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hm_seg := (rt_seg_le c U V w n_max base ep hep).2.2.2.1
  obtain ⟨_, _, _, _, _, hmt_lt, _, hpbc_lt⟩ := large_bounds_lt_n_max hth
  have hcur_g : cur < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hch_g : ch < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have h0_g : 0 < 2 ^ globalPtrBits n_max := Nat.two_pow_pos _
  have hi0 : 4 * u < 6 * maxTrieNodesWhp c n_max := by omega
  have hi1 : 4 * u + 1 < 6 * maxTrieNodesWhp c n_max := by omega
  have hi2 : 4 * u + 2 < 6 * maxTrieNodesWhp c n_max := by omega
  set rt := mkBufRt c U V w n_max base ep
  unfold bufAllocMetaRtProg
  simp only [pure_bind]
  set m1 := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u) cur
  set m2 := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w m1 (4 * u + 1) ch
  set m3 := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w m2 (4 * u + 2) 0
  have hs'_eq : (Memory.spec 0).clientState s
      (writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * u), cur) >>=
        fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * u + 1), ch) >>= fun _ =>
            writePackedGenProg
              ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * u + 2), 0)) =
      { mem := m3, frontier := s.frontier } := rfl
  rw [hs'_eq]
  refine ⟨rfl, rfl, ?_,
    ((bufEpFrame_writeMeta hw hep hi0).trans (bufEpFrame_writeMeta hw hep hi1)).trans
      (bufEpFrame_writeMeta hw hep hi2),
    ?_, ?_, readPacked_writePacked_self _ _ _ m2 (4 * u + 2) h0_g,
    fun idx _ hn0 hn1 hn2 => ?_, fun a ha => ?_⟩
  · refine validProg_bind (validProg_writePacked hw hgk hi0 hm_seg) ?_
    rw [clientState_writePackedGen]
    refine validProg_bind (validProg_writePacked hw hgk hi1 hm_seg) ?_
    rw [clientState_writePackedGen]
    exact validProg_writePacked hw hgk hi2 hm_seg
  · exact (readPacked_writePacked_of_ne hw m2 (by omega) 0).trans
      ((readPacked_writePacked_of_ne hw m1 (by omega) ch).trans
        (readPacked_writePacked_self _ _ _ s.mem (4 * u) hcur_g))
  · exact (readPacked_writePacked_of_ne hw m2 (by omega) 0).trans
      (readPacked_writePacked_self _ _ _ m1 (4 * u + 1) hch_g)
  · exact (readPacked_writePacked_of_ne hw m2 hn2 0).trans
      ((readPacked_writePacked_of_ne hw m1 hn1 ch).trans
        (readPacked_writePacked_of_ne hw s.mem hn0 cur))
  · exact (writePacked_outside hw _ hi2 _ (by cases ha <;> omega)).trans
      ((writePacked_outside hw _ hi1 _ (by cases ha <;> omega)
        ).trans (writePacked_outside hw _ hi0 _ (by cases ha <;> omega)))

/-- Allocate one missing child node `u := nodeAlloc` along `(cur, ch)`
(`d = ((rt, (cur, ch)), r_nxt)`). -/
@[irreducible] private def bufAllocNodeRtProg
    (d : (BufRt × (ℕ × ℕ)) × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let rt := d.1.1
  let cur ← pure d.1.2.1
  let ch ← pure d.1.2.2
  let addrNA ← pure (brBase rt + brHdrNA rt)
  let u ← Memory.read addrNA
  let u1 ← pure (u + 1)
  Memory.write addrNA u1
  let idxC ← pure (cur * brPowBChar rt + ch)
  writePackedGenProg ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), idxC), u)
  bufAllocMetaRtProg ((rt, u), (cur, ch))
  pure (u, d.2)

/-- Precondition for `bufAllocNodeRtProg`. -/
private def BufAllocNodePre (w : ℕ) (d : (BufRt × (ℕ × ℕ)) × ℕ) (s : Memory.State) : Prop :=
  BufRtEnvGen w d.1.1 ∧
  d.1.2.1 < brMaxNodes d.1.1 ∧
  d.1.2.2 < brPowBChar d.1.1 ∧
  s.mem (brBase d.1.1 + brHdrNA d.1.1) < brMaxNodes d.1.1

private theorem realizes_bufAllocNodeRt :
    Realizes .exact bufAllocNodeRtProg
      (WordEncoding.encode (α := (BufRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      BufAllocNodePre
      (fun _ _ => 0) := by
  unfold bufAllocNodeRtProg
  have hwp := realizes_writePackedGen
  have ham := realizes_bufAllocMetaRt
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  have hcr_r : ∀ a s', (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨⟨rt, ⟨cur, ch⟩⟩, r_nxt⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hcur, hch, hu_lt⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes, brPowBChar, brBase, brHdrNA] at hcur hch hu_lt
    have hmt_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.1
    obtain ⟨_, _, _, htc_le, _, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have htc_n : trieChildEntriesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htc_le
    have hna32 : brHdrNA (mkBufRt c U V w n_max base ep) < 32 :=
      (rt_disj_le c U V w n_max base ep hep).1
    have hprod_le : cur * 2 ^ bCharWhp n_max ≤ trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      exact Nat.mul_le_mul_right _ hcur.le
    have hidx_lt : cur * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc cur * 2 ^ bCharWhp n_max + ch
          < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch _
        _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur
    simp only [hcs_r, hcr_r] at *
    first
    | exact henv.fits_hdr_addr hna32
    | exact henv.fits_of_le_n_max (by dsimp [mkBufRt, brBase, brHdrNA, brPowBChar] at *; omega)
    | exact rt_child_safe henv hep hidx_lt
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brBase, brHdrNA, brMaxNodes] at *; omega)

private theorem bufAllocNodeRtProg_spec {c U V w n_max base ep cur ch r_nxt : ℕ}
    {tr : BufTrie} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (_halloc : 1 ≤ tr.nodeAlloc)
    (hu_lt : tr.nodeAlloc < maxTrieNodesWhp c n_max)
    (hcur : cur < tr.nodeAlloc) (hch : ch < 2 ^ bCharWhp n_max) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt)
    let u := tr.nodeAlloc
    let tr1 : BufTrie :=
      { tr with
        nodeAlloc := u + 1
        trieChild := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
        nodeParent := Function.update tr.nodeParent u cur
        nodeChar := Function.update tr.nodeChar u ch
        nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    (Memory.spec 0).clientResult s prog = (u, r_nxt) ∧
    memoryCost prog s = 18 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufTrieMemRep base c U V w n_max ep tr1 s'.mem ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨hna_lt_sp, _, hc_seg, _, _⟩ :
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
  have hmt_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.1
  set u := tr.nodeAlloc
  have hmem_na : s.mem (base + brHdrNA rt) = u := (bufTrieMemRep_iff_rt.mp hrep).2.2.1
  have hu1_fit : Fits w (u + 1) := henv.fits_of_le_n_max (by omega)
  have hu_g : u < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hcur_max : cur < maxTrieNodesWhp c n_max := hcur.trans hu_lt
  set idxC := cur * 2 ^ bCharWhp n_max + ch
  have hidxC : idxC < trieChildEntriesWhp c n_max := by
    unfold trieChildEntriesWhp
    calc cur * 2 ^ bCharWhp n_max + ch
        < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch _
      _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
      _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur_max
  set s1 : Memory.State :=
    { mem := Function.update s.mem (base + brHdrNA rt) (u + 1), frontier := s.frontier }
  set s2 : Memory.State :=
    { mem := writePacked (base + brOffChild rt) (globalPtrBits n_max) w s1.mem idxC u,
      frontier := s.frontier }
  have hm_spec := bufAllocMetaRtProg_spec henv hep hu_lt hcur_max hch (s := s2)
  dsimp only at hm_spec
  change _ ∧ _ ∧ _ ∧ _ ∧
    readPacked (base + brOffMeta rt) _ _ _ _ = _ ∧
    readPacked (base + brOffMeta rt) _ _ _ _ = _ ∧
    readPacked (base + brOffMeta rt) _ _ _ _ = _ ∧
    (∀ idx < 6 * maxTrieNodesWhp c n_max, _ → _ → _ →
      readPacked (base + brOffMeta rt) _ _ _ _ = readPacked (base + brOffMeta rt) _ _ _ _) ∧
    (∀ a, a < base + brOffMeta rt ∨
      base + brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤ a →
      _ = _) at hm_spec
  obtain ⟨hfr3, hmc3, hvp3, hbfr3, hm0_eq, hm1_eq, hm2_eq, hm_oth, hm_out⟩ := hm_spec
  set s3 := (Memory.spec 0).clientState s2 (bufAllocMetaRtProg ((rt, u), (cur, ch)))
  dsimp only
  unfold bufAllocNodeRtProg
  simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (Memory.read (brBase rt + brHdrNA rt) >>= fun u' =>
        Memory.write (brBase rt + brHdrNA rt) (u' + 1) >>= fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), cur * brPowBChar rt + ch), u')
            >>= fun _ =>
            bufAllocMetaRtProg ((rt, u'), (cur, ch)) >>= fun _ => pure (u', r_nxt)) = s3 := by
    rw [clientState_bind, clientState_memRead, clientResult_memRead,
      show brBase rt = base from rfl, hmem_na, clientState_bind,
      clientState_memWrite, clientState_bind, clientState_writePackedGen,
      clientState_bind, StateTransitionSpec.clientState_pure]
    rfl
  have hres_eq : (Memory.spec 0).clientResult s
      (Memory.read (brBase rt + brHdrNA rt) >>= fun u' =>
        Memory.write (brBase rt + brHdrNA rt) (u' + 1) >>= fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), cur * brPowBChar rt + ch), u')
            >>= fun _ =>
            bufAllocMetaRtProg ((rt, u'), (cur, ch)) >>= fun _ => pure (u', r_nxt)) =
      (u, r_nxt) := by
    rw [clientResult_bind, clientState_memRead, clientResult_memRead,
      show brBase rt = base from rfl, hmem_na, clientResult_bind,
      clientState_memWrite, clientResult_bind, clientState_writePackedGen,
      clientResult_bind, StateTransitionSpec.clientResult_pure]
  have hmc_eq : memoryCost
      (Memory.read (brBase rt + brHdrNA rt) >>= fun u' =>
        Memory.write (brBase rt + brHdrNA rt) (u' + 1) >>= fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), cur * brPowBChar rt + ch), u')
            >>= fun _ =>
            bufAllocMetaRtProg ((rt, u'), (cur, ch)) >>= fun _ => pure (u', r_nxt)) s = 18 := by
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_na,
      memoryCost_memRead_and_write.1, clientState_memWrite, memoryCost_memRead_and_write.2,
      clientState_writePackedGen, memoryCost_writePackedGen]
    change 1 + (1 + (4 + (memoryCost (bufAllocMetaRtProg ((rt, u), (cur, ch))) s2 + 0))) = 18
    rw [hmc3]
  have hvp_eq : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (Memory.read (brBase rt + brHdrNA rt) >>= fun u' =>
        Memory.write (brBase rt + brHdrNA rt) (u' + 1) >>= fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), cur * brPowBChar rt + ch), u')
            >>= fun _ =>
            bufAllocMetaRtProg ((rt, u'), (cur, ch)) >>= fun _ => pure (u', r_nxt)) := by
    refine validProg_bind (validProg_read hna_lt_sp) ?_
    rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_na]
    refine validProg_bind (validProg_write hna_lt_sp hu1_fit) ?_
    rw [clientState_memWrite]
    refine validProg_bind (validProg_writePacked hw hgk hidxC hc_seg) ?_
    rw [clientState_writePackedGen]
    exact validProg_bind hvp3 (validProg_pure _)
  rw [hs'_eq]
  have hbfr_all : BufEpFrame base c U V w n_max ep s.mem s3.mem :=
    ((bufEpFrame_write_hdrNA hw hep).trans (bufEpFrame_writeChild hw hep hidxC)).trans hbfr3
  refine ⟨hfr3, hres_eq, hmc_eq, hvp_eq, ?_, hbfr_all⟩
  -- Prove `BufTrieMemRep` for `tr1` on `s3.mem`
  have hs2_hdrNA : s2.mem (base + brHdrNA rt) = u + 1 := by
    dsimp only [s2, s1]
    rw [writePacked_outside hw _ hidxC _ (by omega), Function.update_self]
  have hs3_hdrNA : s3.mem (base + brHdrNA rt) = u + 1 :=
    (hm_out _ (Or.inl (by omega))).trans hs2_hdrNA
  have hs2_hdrIA : s2.mem (base + brHdrIA rt) = s.mem (base + brHdrIA rt) := by
    dsimp only [s2, s1]
    rw [writePacked_outside hw _ hidxC _ (by omega),
      Function.update_of_ne (by omega)]
  have hs3_hdrIA : s3.mem (base + brHdrIA rt) = s.mem (base + brHdrIA rt) :=
    (hm_out _ (Or.inl (by omega))).trans hs2_hdrIA
  have hs3_child : ∀ v < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
      readPacked (base + brOffChild rt) (globalPtrBits n_max) w s3.mem
        (v * 2 ^ bCharWhp n_max + c') =
        Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u) v c' := by
    intro v hv c' hc'
    have hvc_lt : v * 2 ^ bCharWhp n_max + c' < trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc v * 2 ^ bCharWhp n_max + c'
          < v * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hc' _
        _ = (v + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hv
    have hs3_s2 : readPacked (base + brOffChild rt) (globalPtrBits n_max) w s3.mem
        (v * 2 ^ bCharWhp n_max + c') =
        readPacked (base + brOffChild rt) (globalPtrBits n_max) w s2.mem
          (v * 2 ^ bCharWhp n_max + c') :=
      readPacked_congr hw (hidx := hvc_lt) fun a ⟨ha1, ha2⟩ => hm_out a (Or.inl (by omega))
    rw [hs3_s2]
    dsimp only [s2]
    by_cases hvc : v = cur ∧ c' = ch
    · rcases hvc with ⟨rfl, rfl⟩
      simp only [Function.update_self]
      exact readPacked_writePacked_self _ _ _ s1.mem idxC hu_g
    · have hne_idx : v * 2 ^ bCharWhp n_max + c' ≠ idxC :=
        fun heq => hvc ((child_idx_eq_iff hc' hch).mp heq)
      rw [readPacked_writePacked_of_ne hw s1.mem hne_idx u]
      dsimp only [s1]
      rw [readPacked_update_outside hw hvc_lt (Or.inl (by omega))]
      have hrep_c : readPacked (base + brOffChild rt) (globalPtrBits n_max) w s.mem
          (v * 2 ^ bCharWhp n_max + c') = tr.trieChild v c' := by
        have hc_r := hrep.2.2.2.2.1 v hv c' hc'
        rcases hep with rfl | rfl <;> exact hc_r
      rw [hrep_c]
      by_cases hv_eq : v = cur
      · subst hv_eq
        have hc_ne : c' ≠ ch := fun h => hvc ⟨rfl, h⟩
        simp [hc_ne]
      · simp [hv_eq]
  have hs2_meta : ∀ idx < 6 * maxTrieNodesWhp c n_max,
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s2.mem idx =
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem idx := by
    intro idx hidx
    dsimp only [s2, s1]
    exact (readPacked_writePacked_disjoint hw hidx hidxC (Or.inr (by omega))).trans
      (readPacked_update_outside hw hidx (Or.inl (by omega)))
  have hs3_items : ∀ idx < 6 * qEpochWhp n_max + 6,
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s3.mem idx =
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem idx := by
    intro idx hidx
    have h32 : readPacked (base + brOffItems rt) (globalPtrBits n_max) w s3.mem idx =
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w s2.mem idx :=
      readPacked_congr hw (hidx := hidx) fun a ⟨ha1, _⟩ => hm_out a (Or.inr (by omega))
    rw [h32]
    dsimp only [s2, s1]
    exact (readPacked_writePacked_disjoint hw hidx hidxC (Or.inr (by omega))).trans
      (readPacked_update_outside hw hidx (Or.inl (by omega)))
  obtain ⟨_, hia, _, hhia, _, hpar, hlf, hit⟩ := bufTrieMemRep_iff_rt.mp hrep
  rw [bufTrieMemRep_iff_rt]
  dsimp only
  refine ⟨by omega, hia, hs3_hdrNA, hs3_hdrIA.trans hhia, hs3_child,
    fun w' hw1 hw_lt => ?_, fun w' hw_lt => ?_, fun id hid => ?_⟩
  · by_cases hwu : w' = u
    · subst hwu
      simp only [Function.update_self]
      exact ⟨hm0_eq, hm1_eq⟩
    · have hw_u : w' < u := by omega
      simp only [Function.update_of_ne hwu]
      exact ⟨(hm_oth _ (by omega) (by omega) (by omega) (by omega)).trans
          ((hs2_meta _ (by omega)).trans (hpar w' hw1 hw_u).1),
        (hm_oth _ (by omega) (by omega) (by omega) (by omega)).trans
          ((hs2_meta _ (by omega)).trans (hpar w' hw1 hw_u).2)⟩
  · by_cases hwu : w' = u
    · subst hwu
      simp only [Function.update_self]
      exact ⟨hm2_eq, fun hnz => absurd rfl hnz⟩
    · have hw_u : w' < u := by omega
      simp only [Function.update_of_ne hwu]
      exact ⟨(hm_oth _ (by omega) (by omega) (by omega) (by omega)).trans
          ((hs2_meta _ (by omega)).trans (hlf w' hw_u).1),
        fun hnz => (hm_oth _ (by omega) (by omega) (by omega) (by omega)).trans
          ((hs2_meta _ (by omega)).trans ((hlf w' hw_u).2 hnz))⟩
  · exact ⟨(hs3_items _ (by omega)).trans (hit id hid).1,
      (hs3_items _ (by omega)).trans (hit id hid).2.1,
      (hs3_items _ (by omega)).trans (hit id hid).2.2⟩

/-- Precondition for one step of `bufEnsurePath` (`p = (rt, (cur, r_cur))`). -/
def BufEnsureStepPre (w : ℕ) : BufRt × (ℕ × ℕ) → Memory.State → Prop
  | (rt, (cur, _)), s =>
    BufRtEnvGen w rt ∧
    cur < brMaxNodes rt ∧
    s.mem (brBase rt + brHdrNA rt) < brMaxNodes rt

/-- One character-allocation step of `bufEnsurePath`. -/
def bufEnsureStepProg : BufRt × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (rt, (cur, r_cur)) => do
    let ch ← pure (r_cur &&& brMaskBChar rt)
    let idx ← pure (cur * brPowBChar rt + ch)
    let nxt ← readPackedGenProg (((brBase rt, brOffChild rt), (brGBits rt, brW rt)), idx)
    let r_nxt ← pure (r_cur >>> brBChar rt)
    if nxt = 0 then
      bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt)
    else
      pure (nxt, r_nxt)

private theorem memoryCost_bufEnsureStepProg_pos (p : BufRt × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (bufEnsureStepProg p) s := by
  unfold bufEnsureStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, memoryCost_readPackedGen]
  omega

private theorem realizes_bufEnsureStep :
    Realizes .exact bufEnsureStepProg
      (WordEncoding.encode (α := BufRt × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      BufEnsureStepPre
      (fun _ _ => 0) := by
  unfold bufEnsureStepProg
  have hrp := realizes_readPackedGen
  have han := realizes_bufAllocNodeRt
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, ⟨cur, r_cur⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hcur, hna_lt⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hcur
    obtain ⟨_, _, _, htc_le, _, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have htc_n : trieChildEntriesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htc_le
    have hch_lt : r_cur &&& (2 ^ bCharWhp n_max - 1) < 2 ^ bCharWhp n_max := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hidx_lt : cur * 2 ^ bCharWhp n_max + (r_cur &&& (2 ^ bCharWhp n_max - 1)) <
        trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc cur * 2 ^ bCharWhp n_max + (r_cur &&& (2 ^ bCharWhp n_max - 1))
          < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch_lt _
        _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur
    first
    | exact rt_child_safe henv hep hidx_lt
    | (dsimp only [mkBufRt, brMaxNodes, brMaskBChar, brPowBChar, brBChar, brBase, brOffChild,
         brGBits, brW] at hna_lt ⊢
       simp only [hcs] at *
       first
       | exact henv.fits_of_le_n_max (hidx_lt.le.trans htc_n)
       | exact ⟨⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩, hcur, hch_lt, hna_lt⟩)

/-- Parameter-free wrapper for `iterate bufEnsureStepProg`. -/
def bufEnsureLoopGenProg :
    (BufRt × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((rt, x), rem) => iterate bufEnsureStepProg rt rem x

theorem realizes_bufEnsureLoopGen :
    Realizes .exact bufEnsureLoopGenProg
      (WordEncoding.encode (α := (BufRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((rt, x), rem) s => iterationSafe bufEnsureStepProg BufEnsureStepPre w rt rem x s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := BufRt))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_bufEnsureStep
    memoryCost_bufEnsureStepProg_pos

theorem bufEnsureLoop_spec {c U V w n_max base ep : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    ∀ rem (tr : BufTrie) (cur r_cur : ℕ) (s : Memory.State),
      BufTrieMemRep base c U V w n_max ep tr s.mem →
      1 ≤ tr.nodeAlloc →
      tr.nodeAlloc + rem ≤ maxTrieNodesWhp c n_max →
      cur < tr.nodeAlloc →
      (∀ v ch, tr.trieChild v ch < tr.nodeAlloc) →
      (∀ w' < tr.nodeAlloc, tr.nodeLeafItem w' ≤ tr.itemAlloc) →
      let prog := bufEnsureLoopGenProg ((rt, (cur, r_cur)), rem)
      let pPure := bufEnsurePath (bCharWhp n_max) r_cur rem 0 tr cur
      let tr1 := pPure.1
      let leaf := pPure.2
      let s1 := (Memory.spec 0).clientState s prog
      iterationSafe bufEnsureStepProg BufEnsureStepPre w rt rem (cur, r_cur) s ∧
      s1.frontier = s.frontier ∧
      ((Memory.spec 0).clientResult s prog).1 = leaf ∧
      memoryCost prog s ≤ 20 * rem ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      BufTrieMemRep base c U V w n_max ep tr1 s1.mem ∧
      BufEpFrame base c U V w n_max ep s.mem s1.mem ∧
      leaf < tr1.nodeAlloc ∧
      tr1.itemAlloc = tr.itemAlloc ∧
      tr1.nodeLeafItem leaf ≤ tr1.itemAlloc := by
  intro rt rem
  have hw := henv.2.1
  have hc_seg := (rt_seg_le c U V w n_max base ep hep).2.2.1
  induction rem with
  | zero =>
    intro tr cur r_cur s hrep _ _ hcur _ hli_ia
    exact ⟨trivial, rfl, rfl, Nat.zero_le _, validProg_pure _,
      hrep, BufEpFrame.refl _, hcur, rfl, hli_ia cur hcur⟩
  | succ rem ih =>
    intro tr cur r_cur s hrep halloc hna_rem hcur hchild_lt hli_ia
    have hu_lt : tr.nodeAlloc < maxTrieNodesWhp c n_max := by omega
    have hcur_max : cur < maxTrieNodesWhp c n_max := hcur.trans hu_lt
    have hmem_na : s.mem (brBase rt + brHdrNA rt) = tr.nodeAlloc := by
      have h := hrep.2.2.1; rcases hep with rfl | rfl <;> exact h
    have hpre : BufEnsureStepPre w (rt, (cur, r_cur)) s :=
      ⟨⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩, hcur_max, hmem_na ▸ hu_lt⟩
    set ch := r_cur % 2 ^ bCharWhp n_max with hch_def
    have hch_eq : r_cur &&& brMaskBChar rt = ch := by
      dsimp only [rt, mkBufRt, brMaskBChar, ch]
      exact Nat.and_two_pow_sub_one_eq_mod r_cur (bCharWhp n_max)
    have hch_lt : ch < 2 ^ bCharWhp n_max := Nat.mod_lt _ (Nat.two_pow_pos _)
    set idx := cur * 2 ^ bCharWhp n_max + ch
    have hidx_lt : idx < trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc cur * 2 ^ bCharWhp n_max + ch
          < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch_lt _
        _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur_max
    set r_nxt := r_cur / 2 ^ bCharWhp n_max with hr_def
    have hr_eq : r_cur >>> brBChar rt = r_nxt := by
      dsimp only [rt, mkBufRt, brBChar, r_nxt]
      exact Nat.shiftRight_eq_div_pow r_cur (bCharWhp n_max)
    have hrep_ch : readPacked (brBase rt + brOffChild rt) (brGBits rt) (brW rt) s.mem
        (cur * brPowBChar rt + (r_cur &&& brMaskBChar rt)) = tr.trieChild cur ch := by
      rw [hch_eq]
      have hc := hrep.2.2.2.2.1 cur hcur_max ch hch_lt
      rcases hep with rfl | rfl <;> exact hc
    set stepP := bufEnsureStepProg (rt, (cur, r_cur))
    have hidx_rt : cur * brPowBChar rt + (r_cur &&& brMaskBChar rt) = idx := by
      rw [hch_eq]; rfl
    dsimp only [bufEnsurePath]
    rw [laneGet_zero_eq_mod]
    by_cases hn0 : tr.trieChild cur ch = 0
    · rw [ite_eq_left hn0, bufEnsurePath_add_off]
      set u := tr.nodeAlloc
      set tr_step : BufTrie :=
        { tr with
          nodeAlloc := u + 1
          trieChild := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
          nodeParent := Function.update tr.nodeParent u cur
          nodeChar := Function.update tr.nodeChar u ch
          nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
      obtain ⟨hfr_a, hres_a, hmc_a, hvp_a, hrep_a, hbfr_a⟩ :=
        bufAllocNodeRtProg_spec henv hep hrep halloc hu_lt hcur hch_lt (r_nxt := r_nxt) (s := s)
      set s_step := (Memory.spec 0).clientState s (bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt))
      have hstep_st : (Memory.spec 0).clientState s stepP = s_step := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        rw [clientState_bind, clientState_readPackedGen,
          clientResult_readPackedGen, hrep_ch, ite_eq_left hn0, hch_eq, hr_eq]
      have hstep_res : (Memory.spec 0).clientResult s stepP = (u, r_nxt) := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        rw [clientResult_bind, clientState_readPackedGen,
          clientResult_readPackedGen, hrep_ch, ite_eq_left hn0, hch_eq, hr_eq]
        exact hres_a
      have hstep_mc : memoryCost stepP s = 20 := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [memoryCost_readPackedGen, clientState_readPackedGen, clientResult_readPackedGen,
          hrep_ch, ite_eq_left hn0, hch_eq, hr_eq, hmc_a]
      have hstep_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s stepP := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        refine validProg_bind (validProg_readPacked hw (hidx_rt.symm ▸ hidx_lt) hc_seg) ?_
        rw [clientState_readPackedGen, clientResult_readPackedGen, hrep_ch, hch_eq, hr_eq,
          ite_eq_left hn0]
        exact hvp_a
      have hchild_step : ∀ v c', tr_step.trieChild v c' < tr_step.nodeAlloc := by
        intro v c'
        dsimp only [tr_step]
        by_cases hv : v = cur
        · subst hv
          by_cases hc' : c' = ch
          · subst hc'; simp
          · simp only [Function.update_self, Function.update_of_ne hc']
            exact (hchild_lt v c').trans (Nat.lt_succ_self u)
        · simp only [Function.update_of_ne hv]
          exact (hchild_lt v c').trans (Nat.lt_succ_self u)
      have hli_step : ∀ w' < tr_step.nodeAlloc, tr_step.nodeLeafItem w' ≤ tr_step.itemAlloc := by
        intro w' hw'
        dsimp only [tr_step] at hw' ⊢
        by_cases hwu : w' = u
        · subst hwu; simp
        · rw [Function.update_of_ne hwu]
          exact hli_ia w' (by omega)
      obtain ⟨hsafe_r, hfr_r, hres_r, hmc_r, hvp_r, hrep_r, hbfr_r, hlf_lt, hia_r, hli_r⟩ :=
        ih tr_step u r_nxt s_step hrep_a (by dsimp [tr_step]; omega)
          (by dsimp [tr_step, u]; omega) (by dsimp [tr_step]; omega) hchild_step hli_step
      have hst_all : (Memory.spec 0).clientState s
          (bufEnsureLoopGenProg ((rt, (cur, r_cur)), rem + 1)) =
          (Memory.spec 0).clientState s_step (bufEnsureLoopGenProg ((rt, (u, r_nxt)), rem)) := by
        change (Memory.spec 0).clientState s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') = _
        rw [clientState_bind, hstep_st, hstep_res]
        rfl
      have hres_all : (Memory.spec 0).clientResult s
          (bufEnsureLoopGenProg ((rt, (cur, r_cur)), rem + 1)) =
          (Memory.spec 0).clientResult s_step (bufEnsureLoopGenProg ((rt, (u, r_nxt)), rem)) := by
        change (Memory.spec 0).clientResult s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') = _
        rw [clientResult_bind, hstep_st, hstep_res]
        rfl
      rw [hst_all, hres_all]
      refine ⟨⟨hpre, ?_⟩, hfr_r.trans hfr_a, hres_r, ?_, ?_, hrep_r, hbfr_a.trans hbfr_r,
        hlf_lt, hia_r, hli_r⟩
      · rw [clientState_width, hstep_st, clientResult_width, hstep_res]
        exact hsafe_r
      · change memoryCost (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') s ≤
          20 * (rem + 1)
        simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        change memoryCost stepP s +
          memoryCost (bufEnsureLoopGenProg
            ((rt, (Memory.spec 0).clientResult s stepP), rem))
            ((Memory.spec 0).clientState s stepP) ≤ 20 * (rem + 1)
        rw [hstep_st, hstep_res, hstep_mc]
        omega
      · change ValidProg w (base + largeSpaceWhp c U V w n_max) s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s')
        refine validProg_bind hstep_vp ?_
        change ValidProg w (base + largeSpaceWhp c U V w n_max)
          ((Memory.spec 0).clientState s stepP)
          (bufEnsureLoopGenProg ((rt, (Memory.spec 0).clientResult s stepP), rem))
        rw [hstep_st, hstep_res]
        exact hvp_r
    · rw [ite_eq_right hn0, bufEnsurePath_add_off]
      set nxt := tr.trieChild cur ch
      have hstep_st : (Memory.spec 0).clientState s stepP = s := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        rw [clientState_bind, clientState_readPackedGen,
          clientResult_readPackedGen, hrep_ch, ite_eq_right hn0]
        rfl
      have hstep_res : (Memory.spec 0).clientResult s stepP = (nxt, r_nxt) := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        rw [clientResult_bind, clientState_readPackedGen,
          clientResult_readPackedGen, hrep_ch, ite_eq_right hn0, hr_eq]
        rfl
      have hstep_mc : memoryCost stepP s = 2 := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [memoryCost_readPackedGen, clientState_readPackedGen, clientResult_readPackedGen,
          hrep_ch, ite_eq_right hn0]
        rfl
      have hstep_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s stepP := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        refine validProg_bind (validProg_readPacked hw (hidx_rt.symm ▸ hidx_lt) hc_seg) ?_
        rw [clientState_readPackedGen, clientResult_readPackedGen, hrep_ch, ite_eq_right hn0]
        exact validProg_pure _
      obtain ⟨hsafe_r, hfr_r, hres_r, hmc_r, hvp_r, hrep_r, hbfr_r, hlf_lt, hia_r, hli_r⟩ :=
        ih tr nxt r_nxt s hrep halloc (by omega) (hchild_lt cur ch) hchild_lt hli_ia
      have hst_all : (Memory.spec 0).clientState s
          (bufEnsureLoopGenProg ((rt, (cur, r_cur)), rem + 1)) =
          (Memory.spec 0).clientState s (bufEnsureLoopGenProg ((rt, (nxt, r_nxt)), rem)) := by
        change (Memory.spec 0).clientState s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') = _
        rw [clientState_bind, hstep_st, hstep_res]
        rfl
      have hres_all : (Memory.spec 0).clientResult s
          (bufEnsureLoopGenProg ((rt, (cur, r_cur)), rem + 1)) =
          (Memory.spec 0).clientResult s (bufEnsureLoopGenProg ((rt, (nxt, r_nxt)), rem)) := by
        change (Memory.spec 0).clientResult s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') = _
        rw [clientResult_bind, hstep_st, hstep_res]
        rfl
      rw [hst_all, hres_all]
      refine ⟨⟨hpre, ?_⟩, hfr_r, hres_r, ?_, ?_, hrep_r, hbfr_r, hlf_lt, hia_r, hli_r⟩
      · rw [clientState_width, hstep_st, clientResult_width, hstep_res]
        exact hsafe_r
      · change memoryCost (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') s ≤
          20 * (rem + 1)
        simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        change memoryCost stepP s +
          memoryCost (bufEnsureLoopGenProg
            ((rt, (Memory.spec 0).clientResult s stepP), rem))
            ((Memory.spec 0).clientState s stepP) ≤ 20 * (rem + 1)
        rw [hstep_st, hstep_res, hstep_mc]
        omega
      · change ValidProg w (base + largeSpaceWhp c U V w n_max) s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s')
        refine validProg_bind hstep_vp ?_
        change ValidProg w (base + largeSpaceWhp c U V w n_max)
          ((Memory.spec 0).clientState s stepP)
          (bufEnsureLoopGenProg ((rt, (Memory.spec 0).clientResult s stepP), rem))
        rw [hstep_st, hstep_res]
        exact hvp_r

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
