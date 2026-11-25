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

private theorem child_idx_lt {c n_max v c' : ℕ} (hv : v < maxTrieNodesWhp c n_max)
    (hc : c' < 2 ^ bCharWhp n_max) : v * 2 ^ bCharWhp n_max + c' < trieChildEntriesWhp c n_max :=
  (Nat.add_lt_add_left hc _).trans_le <| by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hv

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
    have hidx_lt := child_idx_lt hcur hch
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
  have hmt_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.1
  have hcur_max : cur < maxTrieNodesWhp c n_max := hcur.trans hu_lt
  have hidxC := child_idx_lt hcur_max hch
  obtain ⟨hna_lt_sp, _, hc_seg, _, _⟩ := rt_seg_le c U V w n_max base ep hep
  obtain ⟨hna32, hia32, hna_ne_ia, h32_c, hc_le_m, hm_le_i⟩ := rt_disj_le c U V w n_max base ep hep
  obtain ⟨-, hia, hmem_na, hhia, hch_r, hpar, hlf, hit⟩ := bufTrieMemRep_iff_rt.mp hrep
  set rt := mkBufRt c U V w n_max base ep with hrt
  set u := tr.nodeAlloc
  replace hmem_na : s.mem (brBase rt + brHdrNA rt) = u := hmem_na
  have hu1_fit : Fits w (u + 1) := henv.fits_of_le_n_max (by omega)
  have hu_g : u < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  set idxC := cur * 2 ^ bCharWhp n_max + ch
  set s1 : Memory.State :=
    { mem := Function.update s.mem (base + brHdrNA rt) (u + 1), frontier := s.frontier }
  set s2 : Memory.State :=
    { mem := writePacked (base + brOffChild rt) (globalPtrBits n_max) w s1.mem idxC u,
      frontier := s.frontier }
  have hm_spec := bufAllocMetaRtProg_spec henv hep hu_lt hcur_max hch (s := s2)
  dsimp only at hm_spec
  rw [← hrt] at hm_spec
  obtain ⟨hfr3, hmc3, hvp3, hbfr3, hm0_eq, hm1_eq, hm2_eq, hm_oth, hm_out⟩ := hm_spec
  set s3 := (Memory.spec 0).clientState s2 (bufAllocMetaRtProg ((rt, u), (cur, ch)))
  have hst : (Memory.spec 0).clientState s (bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt)) = s3 := by
    unfold bufAllocNodeRtProg
    simp only [pure_bind]
    rw [clientState_bind, clientState_memRead, clientResult_memRead, hmem_na, clientState_bind,
      clientState_memWrite, clientState_bind, clientState_writePackedGen, clientState_bind,
      clientState_pure_whp]
    rfl
  have hres : (Memory.spec 0).clientResult s (bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt)) =
      (u, r_nxt) := by
    unfold bufAllocNodeRtProg
    simp only [pure_bind]
    rw [clientResult_bind, clientState_memRead, clientResult_memRead, hmem_na, clientResult_bind,
      clientResult_bind, clientResult_bind, clientResult_pure_whp]
  have hmc : memoryCost (bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt)) s = 18 := by
    unfold bufAllocNodeRtProg
    simp only [pure_bind, memoryCost_bind', clientResult_memRead, hmem_na,
      memoryCost_memRead_and_write.1, memoryCost_memRead_and_write.2, memoryCost_writePackedGen,
      memoryCost_pure]
    change 1 + (1 + (4 + (memoryCost (bufAllocMetaRtProg ((rt, u), (cur, ch))) s2 + 0))) = 18
    rw [hmc3]
  have hvp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt)) := by
    unfold bufAllocNodeRtProg
    simp only [pure_bind]
    refine validProg_bind (validProg_read hna_lt_sp) ?_
    rw [clientState_memRead, clientResult_memRead, hmem_na]
    refine validProg_bind (validProg_write hna_lt_sp hu1_fit) ?_
    rw [clientState_memWrite]
    refine validProg_bind (validProg_writePacked hw hgk hidxC hc_seg) ?_
    rw [clientState_writePackedGen]
    exact validProg_bind hvp3 (validProg_pure _)
  dsimp only
  rw [hst]
  refine ⟨hfr3, hres, hmc, hvp, ?_,
    ((bufEpFrame_write_hdrNA hw hep).trans (bufEpFrame_writeChild hw hep hidxC)).trans hbfr3⟩
  -- Prove `BufTrieMemRep` for `tr1` on `s3.mem`
  have hs3_hdr : ∀ a < base + 32,
      s3.mem a = Function.update s.mem (base + brHdrNA rt) (u + 1) a := fun a ha =>
    (hm_out a (Or.inl (by omega))).trans (writePacked_outside hw _ hidxC _ (by omega))
  have hs3_child : ∀ v < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
      readPacked (base + brOffChild rt) (globalPtrBits n_max) w s3.mem
        (v * 2 ^ bCharWhp n_max + c') =
        Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u) v c' := by
    intro v hv c' hc'
    have hvc_lt := child_idx_lt hv hc'
    rw [readPacked_congr hw (hidx := hvc_lt) fun a ⟨ha1, ha2⟩ => hm_out a (Or.inl (by omega))]
    dsimp only [s2]
    by_cases hvc : v = cur ∧ c' = ch
    · rcases hvc with ⟨rfl, rfl⟩
      simp only [Function.update_self]
      exact readPacked_writePacked_self _ _ _ s1.mem idxC hu_g
    · rw [readPacked_writePacked_of_ne hw s1.mem
        (fun heq => hvc ((child_idx_eq_iff hc' hch).mp heq)) u]
      dsimp only [s1]
      rw [readPacked_update_outside hw hvc_lt (Or.inl (by omega)), hch_r v hv c' hc']
      by_cases hv_eq : v = cur
      · subst hv_eq
        simp [show c' ≠ ch from fun h => hvc ⟨rfl, h⟩]
      · simp [hv_eq]
  have hs3_meta : ∀ v < u, ∀ j < 4,
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s3.mem (4 * v + j) =
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * v + j) := by
    intro v hv j hj
    have hidx : 4 * v + j < 6 * maxTrieNodesWhp c n_max := by omega
    exact (hm_oth _ hidx (by omega) (by omega) (by omega)).trans
      ((readPacked_writePacked_disjoint hw hidx hidxC (Or.inr (by omega))).trans
        (readPacked_update_outside hw hidx (Or.inl (by omega))))
  have hs3_items : ∀ idx < 6 * qEpochWhp n_max + 6,
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s3.mem idx =
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem idx := fun idx hidx =>
    (readPacked_congr hw (hidx := hidx) fun a ⟨ha1, _⟩ => hm_out a (Or.inr (by omega))).trans
      ((readPacked_writePacked_disjoint hw hidx hidxC (Or.inr (by omega))).trans
        (readPacked_update_outside hw hidx (Or.inl (by omega))))
  rw [bufTrieMemRep_iff_rt]
  dsimp only
  rw [← hrt]
  refine ⟨by omega, hia, (hs3_hdr _ (by omega)).trans (Function.update_self ..),
    ((hs3_hdr _ (by omega)).trans (Function.update_of_ne (by omega) ..)).trans hhia, hs3_child,
    fun v hv1 hv_lt => ?_, fun v hv_lt => ?_, fun id hid => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hv_lt with hv_u | rfl
    · simp only [Function.update_of_ne hv_u.ne]
      exact ⟨(hs3_meta v hv_u 0 (by omega)).trans (hpar v hv1 hv_u).1,
        (hs3_meta v hv_u 1 (by omega)).trans (hpar v hv1 hv_u).2⟩
    · simp only [Function.update_self]
      exact ⟨hm0_eq, hm1_eq⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hv_lt with hv_u | rfl
    · simp only [Function.update_of_ne hv_u.ne]
      exact ⟨(hs3_meta v hv_u 2 (by omega)).trans (hlf v hv_u).1,
        fun hnz => (hs3_meta v hv_u 3 (by omega)).trans ((hlf v hv_u).2 hnz)⟩
    · simp only [Function.update_self]
      exact ⟨hm2_eq, fun hnz => absurd rfl hnz⟩
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
    have hidx_lt := child_idx_lt hcur hch_lt
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

/-- Peel the first `bufEnsureStepProg` off `bufEnsureLoopGenProg`, given the step's final state
and result. -/
private theorem bufEnsureLoop_succ {w F rem : ℕ} {rt : BufRt} {x x' : ℕ × ℕ}
    {s s' : Memory.State}
    (hst : (Memory.spec 0).clientState s (bufEnsureStepProg (rt, x)) = s')
    (hres : (Memory.spec 0).clientResult s (bufEnsureStepProg (rt, x)) = x') :
    (Memory.spec 0).clientState s (bufEnsureLoopGenProg ((rt, x), rem + 1)) =
      (Memory.spec 0).clientState s' (bufEnsureLoopGenProg ((rt, x'), rem)) ∧
    (Memory.spec 0).clientResult s (bufEnsureLoopGenProg ((rt, x), rem + 1)) =
      (Memory.spec 0).clientResult s' (bufEnsureLoopGenProg ((rt, x'), rem)) ∧
    (memoryCost (bufEnsureStepProg (rt, x)) s ≤ 20 →
      memoryCost (bufEnsureLoopGenProg ((rt, x'), rem)) s' ≤ 20 * rem →
      memoryCost (bufEnsureLoopGenProg ((rt, x), rem + 1)) s ≤ 20 * (rem + 1)) ∧
    (ValidProg w F s (bufEnsureStepProg (rt, x)) →
      ValidProg w F s' (bufEnsureLoopGenProg ((rt, x'), rem)) →
      ValidProg w F s (bufEnsureLoopGenProg ((rt, x), rem + 1))) ∧
    (BufEnsureStepPre w (rt, x) s →
      iterationSafe bufEnsureStepProg BufEnsureStepPre w rt rem x' s' →
      iterationSafe bufEnsureStepProg BufEnsureStepPre w rt (rem + 1) x s) := by
  subst hst hres
  refine ⟨clientState_bind _ _ _, clientResult_bind _ _ _, fun h1 h2 => ?_, validProg_bind,
    fun hpre hsafe => ⟨hpre, ?_⟩⟩
  · rw [show memoryCost (bufEnsureLoopGenProg ((rt, x), rem + 1)) s = _ from
      memoryCost_bind' _ _ _]
    exact (Nat.add_le_add h1 h2).trans_eq (by ring)
  · rwa [clientState_width, clientResult_width]

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
    obtain ⟨-, -, hmem_na, -, hch_r, -⟩ := bufTrieMemRep_iff_rt.mp hrep
    replace hmem_na : s.mem (brBase rt + brHdrNA rt) = tr.nodeAlloc := hmem_na
    have hpre : BufEnsureStepPre w (rt, (cur, r_cur)) s :=
      ⟨⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩, hcur_max, hmem_na ▸ hu_lt⟩
    set ch := r_cur % 2 ^ bCharWhp n_max with hch_def
    have hch_eq : r_cur &&& brMaskBChar rt = ch := by
      dsimp only [rt, mkBufRt, brMaskBChar, ch]
      exact Nat.and_two_pow_sub_one_eq_mod r_cur (bCharWhp n_max)
    have hch_lt : ch < 2 ^ bCharWhp n_max := Nat.mod_lt _ (Nat.two_pow_pos _)
    set r_nxt := r_cur / 2 ^ bCharWhp n_max with hr_def
    have hr_eq : r_cur >>> brBChar rt = r_nxt := by
      dsimp only [rt, mkBufRt, brBChar, r_nxt]
      exact Nat.shiftRight_eq_div_pow r_cur (bCharWhp n_max)
    have hrep_ch : readPacked (brBase rt + brOffChild rt) (brGBits rt) (brW rt) s.mem
        (cur * brPowBChar rt + ch) = tr.trieChild cur ch := hch_r cur hcur_max ch hch_lt
    -- The step reads the child slot, then runs `k`.
    obtain ⟨hst_k, hres_k, hmc_k, hvp_k⟩ :
        let k := if tr.trieChild cur ch = 0 then bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt)
          else pure (tr.trieChild cur ch, r_nxt)
        let stepP := bufEnsureStepProg (rt, (cur, r_cur))
        (Memory.spec 0).clientState s stepP = (Memory.spec 0).clientState s k ∧
        (Memory.spec 0).clientResult s stepP = (Memory.spec 0).clientResult s k ∧
        memoryCost stepP s = 2 + memoryCost k s ∧
        (ValidProg w (base + largeSpaceWhp c U V w n_max) s k →
          ValidProg w (base + largeSpaceWhp c U V w n_max) s stepP) := by
      dsimp only [bufEnsureStepProg]
      simp only [pure_bind, hch_eq, hr_eq]
      refine ⟨?_, ?_, ?_, fun h => validProg_bind
        (validProg_readPacked hw (child_idx_lt hcur_max hch_lt) hc_seg) ?_⟩
      · rw [clientState_bind, clientState_readPackedGen, clientResult_readPackedGen, hrep_ch]
      · rw [clientResult_bind, clientState_readPackedGen, clientResult_readPackedGen, hrep_ch]
      · rw [memoryCost_bind', memoryCost_readPackedGen, clientState_readPackedGen,
          clientResult_readPackedGen, hrep_ch]
      · rwa [clientState_readPackedGen, clientResult_readPackedGen, hrep_ch]
    dsimp only [bufEnsurePath]
    rw [laneGet_zero_eq_mod]
    by_cases hn0 : tr.trieChild cur ch = 0
    · rw [ite_eq_left hn0, bufEnsurePath_add_off]
      rw [ite_eq_left hn0] at hst_k hres_k hmc_k hvp_k
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
        ih tr_step u r_nxt _ hrep_a (by dsimp [tr_step]; omega)
          (by dsimp [tr_step, u]; omega) (by dsimp [tr_step]; omega) hchild_step hli_step
      obtain ⟨hst, hres, hmc, hvp, hsafe⟩ := bufEnsureLoop_succ (rem := rem) hst_k
        (hres_k.trans hres_a)
      rw [hst, hres]
      exact ⟨hsafe hpre hsafe_r, hfr_r.trans hfr_a, hres_r,
        hmc (hmc_k.trans_le (Nat.add_le_add_left hmc_a.le 2)) hmc_r, hvp (hvp_k hvp_a) hvp_r, hrep_r,
        hbfr_a.trans hbfr_r, hlf_lt, hia_r, hli_r⟩
    · rw [ite_eq_right hn0, bufEnsurePath_add_off]
      rw [ite_eq_right hn0] at hst_k hres_k hmc_k hvp_k
      obtain ⟨hsafe_r, hfr_r, hres_r, hmc_r, hvp_r, hrep_r, hbfr_r, hlf_lt, hia_r, hli_r⟩ :=
        ih tr (tr.trieChild cur ch) r_nxt s hrep halloc (by omega) (hchild_lt cur ch) hchild_lt
          hli_ia
      obtain ⟨hst, hres, hmc, hvp, hsafe⟩ := bufEnsureLoop_succ (rem := rem)
        (hst_k.trans (clientState_pure_whp _ _)) (hres_k.trans (clientResult_pure_whp _ _))
      rw [hst, hres]
      exact ⟨hsafe hpre hsafe_r, hfr_r, hres_r, hmc (hmc_k.trans_le (by omega : 2 + 0 ≤ 20)) hmc_r,
        hvp (hvp_k (validProg_pure _)) hvp_r, hrep_r, hbfr_r, hlf_lt, hia_r, hli_r⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
