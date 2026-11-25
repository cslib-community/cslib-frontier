/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Helpers
import CslibFrontier.Tactic.Realize

/-!
# Shared Node-Split Primitives and Opaque Call Wrappers for `btreeInsertGenProg`

Provides bit-width bounds on `splitFullNode`, the 3-node + `alloc` frame theorem
`threeNodeWrites_and_alloc_sliceRep`, and `@[irreducible]` call wrappers (`writeNodeOpProg`,
`splitNodeOpProg`, `wordInsertOpProg`, `writeSplitFourOpProg`) shared across root-split,
proactive-split descent, and leaf insertion.
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

theorem splitFullNode_bits_lt {c n_max : ℕ} {nd : BTreeNode}
    (hth : whpThreshold c ≤ n_max)
    (hk : nd.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv : nd.valsWord < 2 ^ valsWordBitsWhp n_max) :
    let res := splitFullNode (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) nd
    res.left.metaWord < 2 ^ nodeMetaBitsWhp n_max ∧
    res.left.keysWord < 2 ^ keysWordBitsWhp n_max ∧
    res.left.valsWord < 2 ^ valsWordBitsWhp n_max ∧
    res.sep < 2 ^ keyLaneBitsWhp n_max ∧
    res.right.metaWord < 2 ^ nodeMetaBitsWhp n_max ∧
    res.right.keysWord < 2 ^ keysWordBitsWhp n_max ∧
    res.right.valsWord < 2 ^ valsWordBitsWhp n_max := by
  obtain ⟨ht3, hmeta_cap, _, _⟩ := (btree_slice_param_bounds hth).1
  have hsep_lt : laneGet (fpBitsWhp n_max + 2) nd.keysWord (tMinWhp n_max - 1) <
      2 ^ keyLaneBitsWhp n_max := by
    rw [laneGet_eq_div_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have htk_lt : wordTakeLow (fpBitsWhp n_max + 2) (tMinWhp n_max) nd.keysWord <
      2 ^ keysWordBitsWhp n_max := by
    unfold keysWordBitsWhp keyLaneBitsWhp
    exact (wordTakeLow_lt _ _ _).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  have htk1_lt : wordTakeLow (fpBitsWhp n_max + 2) (tMinWhp n_max - 1) nd.keysWord <
      2 ^ keysWordBitsWhp n_max := by
    unfold keysWordBitsWhp keyLaneBitsWhp
    exact (wordTakeLow_lt _ _ _).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  have htv_lt : wordTakeLow (valLaneBitsWhp n_max) (tMinWhp n_max) nd.valsWord <
      2 ^ valsWordBitsWhp n_max := by
    unfold valsWordBitsWhp
    exact (wordTakeLow_lt _ _ _).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  have hdk_lt : wordDropLow (fpBitsWhp n_max + 2) (tMinWhp n_max) nd.keysWord <
      2 ^ keysWordBitsWhp n_max := by
    rw [wordDropLow_eq_div]; exact (Nat.div_le_self _ _).trans_lt hk
  have hdv_lt : wordDropLow (valLaneBitsWhp n_max) (tMinWhp n_max) nd.valsWord <
      2 ^ valsWordBitsWhp n_max := by
    rw [wordDropLow_eq_div]; exact (Nat.div_le_self _ _).trans_lt hv
  unfold splitFullNode
  by_cases hlf : metaIsLeaf nd.metaWord = true
  · simp only [hlf, ↓reduceIte, mkNodeMeta]
    exact ⟨by omega, htk_lt, htv_lt, hsep_lt, by omega, hdk_lt, hdv_lt⟩
  · simp only [hlf, Bool.false_eq_true, ↓reduceIte, mkNodeMeta]
    exact ⟨by omega, htk1_lt, htv_lt, hsep_lt, by omega, hdk_lt, hdv_lt⟩

/-- Shared 4-write frame lemma for proactive root/child splits: writing 3 nodes `(idx1, nd1)`,
`(idx2, nd2)`, `(idx3, nd3)` below `newA` followed by `writeSliceAllocGenProg` establishes
`BTreeSliceMemRep` for the updated slice and frames all other slices, other `bktMeta` fields, and
outside segments. -/
theorem threeNodeWrites_and_alloc_sliceRep
    {c U V w n_max base sIdx newA idx1 idx2 idx3 : ℕ}
    {sl : BTreeSlice} {nd1 nd2 nd3 : BTreeNode} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hnewA_hi : newA ≤ nSliceWhp n_max)
    (hu1 : idx1 < newA) (hu2 : idx2 < newA) (hu3 : idx3 < newA)
    (hcov : ∀ v < newA, v < sl.alloc ∨ v = idx1 ∨ v = idx2 ∨ v = idx3)
    (hm1 : nd1.metaWord < 2 ^ nodeMetaBitsWhp n_max)
    (hk1 : nd1.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv1 : nd1.valsWord < 2 ^ valsWordBitsWhp n_max)
    (hm2 : nd2.metaWord < 2 ^ nodeMetaBitsWhp n_max)
    (hk2 : nd2.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv2 : nd2.valsWord < 2 ^ valsWordBitsWhp n_max)
    (hm3 : nd3.metaWord < 2 ^ nodeMetaBitsWhp n_max)
    (hk3 : nd3.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv3 : nd3.valsWord < 2 ^ valsWordBitsWhp n_max) :
    let p0 := (mkWhpCoreParams c U V w n_max, base)
    let prog :=
      writeBTreeNodeGenProg (((p0, sIdx), idx1), (nd1.metaWord, (nd1.keysWord, nd1.valsWord))) >>=
      fun _ =>
      writeBTreeNodeGenProg (((p0, sIdx), idx2), (nd2.metaWord, (nd2.keysWord, nd2.valsWord))) >>=
      fun _ =>
      writeBTreeNodeGenProg (((p0, sIdx), idx3), (nd3.metaWord, (nd3.keysWord, nd3.valsWord))) >>=
      fun _ =>
      writeSliceAllocGenProg ((p0, sIdx), newA)
    let nodes3 := Function.update
      (Function.update (Function.update sl.nodes idx1 nd1) idx2 nd2) idx3 nd3
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 40 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx ⟨newA, sl.root, nodes3⟩ s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ idx < 16 * numBucketsWhp n_max,
      idx ≠ 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, (a < base + offBktMeta c U V w n_max ∨
        (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
        base + offTrieChild0 c U V w n_max ≤ a) →
      s'.mem a = s.mem a) := by
  have hw := henv.2.1
  set p0 := (mkWhpCoreParams c U V w n_max, base)
  set w1 := writeBTreeNodeGenProg (((p0, sIdx), idx1), (nd1.metaWord, (nd1.keysWord, nd1.valsWord)))
  set w2 := writeBTreeNodeGenProg (((p0, sIdx), idx2), (nd2.metaWord, (nd2.keysWord, nd2.valsWord)))
  set w3 := writeBTreeNodeGenProg (((p0, sIdx), idx3), (nd3.metaWord, (nd3.keysWord, nd3.valsWord)))
  set w4 := writeSliceAllocGenProg ((p0, sIdx), newA)
  set s1 := (Memory.spec 0).clientState s w1
  set s2 := (Memory.spec 0).clientState s1 w2
  set s3 := (Memory.spec 0).clientState s2 w3
  obtain ⟨hfr1, hmc1, hvp1, hup1, hoth1, hout1⟩ :=
    writeBTreeNodeGenProg_spec (nd := nd1) henv hsIdx (hu1.trans_le hnewA_hi) hm1 hk1 hv1 (s := s)
  obtain ⟨hfr2, hmc2, hvp2, hup2, hoth2, hout2⟩ :=
    writeBTreeNodeGenProg_spec (nd := nd2) henv hsIdx (hu2.trans_le hnewA_hi) hm2 hk2 hv2 (s := s1)
  obtain ⟨hfr3, hmc3, hvp3, hup3, hoth3, hout3⟩ :=
    writeBTreeNodeGenProg_spec (nd := nd3) henv hsIdx (hu3.trans_le hnewA_hi) hm3 hk3 hv3 (s := s2)
  dsimp only at hfr1 hmc1 hvp1 hup1 hoth1 hout1 hfr2 hmc2 hvp2 hup2 hoth2 hout2
  dsimp only at hfr3 hmc3 hvp3 hup3 hoth3 hout3
  have hout123 : ∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
      s3.mem a = s.mem a := fun a ha =>
    (hout3 a ha).trans ((hout2 a ha).trans (hout1 a ha))
  have hoff := largeOffsetChain c U V w n_max
  have hbm_s3 : ∀ i < 16 * numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s3.mem i =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem i :=
    fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ => hout123 a (Or.inl (by omega))
  let aux0 : ℕ → BTreeNode := fun v =>
    if v < sl.alloc then sl.nodes v
    else ⟨readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s.mem
            (sIdx * nSliceWhp n_max + v),
          readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s.mem
            (sIdx * nSliceWhp n_max + v),
          readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s.mem
            (sIdx * nSliceWhp n_max + v)⟩
  have haux0 : ∀ v < newA,
      let idx_v := sIdx * nSliceWhp n_max + v
      readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s.mem idx_v =
        (aux0 v).metaWord ∧
      readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s.mem idx_v =
        (aux0 v).keysWord ∧
      readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s.mem idx_v =
        (aux0 v).valsWord := fun v _ => by
    dsimp only [aux0]
    split_ifs with hv_lt
    · exact hrep.2.2.2 v hv_lt
    · exact ⟨rfl, rfl, rfl⟩
  have hs1_nd := hup1 ⟨newA, sl.root, aux0⟩ hnewA_hi (fun v hv _ => haux0 v hv)
  have hs2_nd := hup2 ⟨newA, sl.root, Function.update aux0 idx1 nd1⟩ hnewA_hi
    (fun v hv _ => hs1_nd v hv)
  have hs3_nd := hup3
    ⟨newA, sl.root, Function.update (Function.update aux0 idx1 nd1) idx2 nd2⟩ hnewA_hi
    (fun v hv _ => hs2_nd v hv)
  set nodes3 := Function.update
    (Function.update (Function.update sl.nodes idx1 nd1) idx2 nd2) idx3 nd3
  have hnodes_s3 : ∀ u < newA,
      let idx_u := sIdx * nSliceWhp n_max + u
      readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s3.mem idx_u =
        (nodes3 u).metaWord ∧
      readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s3.mem idx_u =
        (nodes3 u).keysWord ∧
      readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s3.mem idx_u =
        (nodes3 u).valsWord := fun u hu => by
    have heq_u : Function.update (Function.update (Function.update aux0 idx1 nd1) idx2 nd2)
        idx3 nd3 u = nodes3 u := by
      dsimp only [nodes3]
      by_cases h3 : u = idx3
      · subst h3; simp
      · rw [Function.update_of_ne h3, Function.update_of_ne h3]
        by_cases h2 : u = idx2
        · subst h2; simp
        · rw [Function.update_of_ne h2, Function.update_of_ne h2]
          by_cases h1 : u = idx1
          · subst h1; simp
          · rw [Function.update_of_ne h1, Function.update_of_ne h1]
            rcases hcov u hu with hlt | h1' | h2' | h3'
            · simp [aux0, hlt]
            · exact absurd h1' h1
            · exact absurd h2' h2
            · exact absurd h3' h3
    simpa only [heq_u] using hs3_nd u hu
  have hroot_s3 : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s3.mem
      (16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)) = sl.root :=
    (hbm_s3 _ (by omega)).trans hrep.2.2.1
  obtain ⟨hfr4, hmc4, hvp4, hrep4, hoth4, hbm4, hout4⟩ :=
    writeSliceAllocGenProg_sliceRep (nodes := nodes3) henv hsIdx hnewA_hi hroot_s3 hnodes_s3
      (s := s3)
  dsimp only at hfr4 hmc4 hvp4 hrep4 hoth4 hbm4 hout4 ⊢
  have hs'_eq : (Memory.spec 0).clientState s (w1 >>= fun _ => w2 >>= fun _ => w3 >>= fun _ => w4) =
      (Memory.spec 0).clientState s3 w4 := by
    rw [clientState_bind, clientState_bind,
      clientState_bind]
  dsimp only [w1, w2, w3, w4] at hs'_eq ⊢
  rw [hs'_eq]
  refine ⟨hfr4.trans (hfr3.trans (hfr2.trans hfr1)), ?_, ?_, hrep4, ?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    change memoryCost w1 s + (memoryCost w2 s1 + (memoryCost w3 s2 + memoryCost w4 s3)) = 40
    rw [hmc1, hmc2, hmc3, hmc4]
  · refine validProg_bind hvp1 ?_
    refine validProg_bind hvp2 ?_
    exact validProg_bind hvp3 hvp4
  · intro sIdx' hsIdx' hne sl₂ hr₂
    exact hoth4 sIdx' hsIdx' hne sl₂
      (hoth3 sIdx' hsIdx' hne sl₂ (hoth2 sIdx' hsIdx' hne sl₂ (hoth1 sIdx' hsIdx' hne sl₂ hr₂)))
  · intro idx hidx hneA
    exact (hbm4 idx hidx hneA).trans (hbm_s3 idx hidx)
  · intro a ha
    rcases ha with ha1 | ⟨ha2, ha3⟩ | ha4
    · exact (hout4 a (Or.inl ha1)).trans (hout123 a (Or.inl (by omega)))
    · exact (hout4 a (Or.inr ha2)).trans (hout123 a (Or.inl ha3))
    · exact (hout4 a (Or.inr (by omega))).trans (hout123 a (Or.inr ha4))


/-- Opaque call wrapper for `writeBTreeNodeGenProg` so multi-write subroutines do not cause
exponential state unfolding inside `realize`. -/
@[expose, irreducible] def writeNodeOpProg
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))) : Memory.Prog Unit :=
  writeBTreeNodeGenProg d

theorem realizes_writeNodeOp :
    Realizes .exact writeNodeOpProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), sIdx), u), _) _ =>
        WhpLargeEnvGen w cp base ∧ sIdx < 3 * wpM cp ∧ u < wpNSlice cp)
      (fun _ _ => 0) := by
  unfold writeNodeOpProg; exact realizes_writeBTreeNodeGen

/-- Opaque call wrapper for `splitFullNodeGenProg`. -/
@[expose, irreducible] def splitNodeOpProg
    (d : WhpCoreParams × (ℕ × (ℕ × ℕ))) :
    Memory.Prog ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ)))) :=
  splitFullNodeGenProg d

theorem realizes_splitNodeOp :
    Realizes .exact splitNodeOpProg
      (WordEncoding.encode (α := WhpCoreParams × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ)))))
      (fun w (cp, _) _ => ∃ base, WhpLargeEnvGen w cp base)
      (fun _ _ => 0) := by
  unfold splitNodeOpProg; exact realizes_splitFullNodeGen

theorem clientResult_splitNodeOpProg {c U V w n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    (nd : BTreeNode) (s : Memory.State) :
    let out := splitFullNode (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) nd
    (Memory.spec 0).clientResult s
      (splitNodeOpProg
        (mkWhpCoreParams c U V w n_max, (nd.metaWord, (nd.keysWord, nd.valsWord)))) =
      ((out.left.metaWord, (out.left.keysWord, out.left.valsWord)),
       (out.sep, (out.right.metaWord, (out.right.keysWord, out.right.valsWord)))) := by
  unfold splitNodeOpProg; exact clientResult_splitFullNodeGenProg hth nd s

/-- Opaque call wrapper for `wordInsertAtGenProg`. -/
@[expose, irreducible] def wordInsertOpProg (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  wordInsertAtGenProg d

theorem realizes_wordInsertOp :
    Realizes .exact wordInsertOpProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w (((wL, r), v), wW) _ =>
        ∃ m, r ≤ m ∧ (m + 1) * wL < w ∧ v < 2 ^ wL ∧ wW < 2 ^ (m * wL))
      (fun _ _ => 0) := by
  unfold wordInsertOpProg; exact realizes_wordInsertAtGen

private def writeSplitFourBody
    (d : (((WhpCoreParams × ℕ) × ℕ) ×
      (((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))) × ((ℕ × (ℕ × (ℕ × ℕ))) × ℕ)))) :
    Memory.Prog Unit := do
  let nSlice ← pure (wpNSlice d.1.1.1)
  let w ← pure (wpW d.1.1.1)
  let gBits ← pure (wpGlobalPtrBits d.1.1.1)
  let offBm ← pure (wpOffBktMeta d.1.1.1)
  let offM ← pure (wpOffBtMeta d.1.1.1)
  let bM ← pure (wpNodeMetaBits d.1.1.1)
  let offK ← pure (wpOffBtKeys d.1.1.1)
  let bK ← pure (wpKeysWordBits d.1.1.1)
  let offV ← pure (wpOffBtVals d.1.1.1)
  let bV ← pure (wpValsWordBits d.1.1.1)
  let g1 ← pure (d.1.2 * nSlice + d.2.1.1.1)
  writePackedGenProg ((((d.1.1.2, offM), (bM, w)), g1), d.2.1.1.2.1)
  writePackedGenProg ((((d.1.1.2, offK), (bK, w)), g1), d.2.1.1.2.2.1)
  writePackedGenProg ((((d.1.1.2, offV), (bV, w)), g1), d.2.1.1.2.2.2)
  let g2 ← pure (d.1.2 * nSlice + d.2.1.2.1)
  writePackedGenProg ((((d.1.1.2, offM), (bM, w)), g2), d.2.1.2.2.1)
  writePackedGenProg ((((d.1.1.2, offK), (bK, w)), g2), d.2.1.2.2.2.1)
  writePackedGenProg ((((d.1.1.2, offV), (bV, w)), g2), d.2.1.2.2.2.2)
  let g3 ← pure (d.1.2 * nSlice + d.2.2.1.1)
  writePackedGenProg ((((d.1.1.2, offM), (bM, w)), g3), d.2.2.1.2.1)
  writePackedGenProg ((((d.1.1.2, offK), (bK, w)), g3), d.2.2.1.2.2.1)
  writePackedGenProg ((((d.1.1.2, offV), (bV, w)), g3), d.2.2.1.2.2.2)
  let b ← pure (d.1.2 / 3)
  let role ← pure (d.1.2 % 3)
  let idxA ← pure (16 * b + 10 + 2 * role)
  writePackedGenProg ((((d.1.1.2, offBm), (gBits, w)), idxA), d.2.2.2)

private theorem realizes_writeSplitFourBody :
    Realizes .exact writeSplitFourBody
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) ×
        (((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))) × ((ℕ × (ℕ × (ℕ × ℕ))) × ℕ)))))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => WhpLargeEnvGen w d.1.1.1 d.1.1.2 ∧
        d.1.2 < 3 * wpM d.1.1.1 ∧
        d.2.1.1.1 < wpNSlice d.1.1.1 ∧
        d.2.1.2.1 < wpNSlice d.1.1.1 ∧
        d.2.2.1.1 < wpNSlice d.1.1.1)
      (fun _ _ => 0) := by
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, ⟨⟨⟨u1, nd1⟩, ⟨u2, nd2⟩⟩, ⟨⟨u3, nd3⟩, newA⟩⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hsIdx, hu1, hu2, hu3⟩ := h
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    have htot_le := totalBTreeNodesWhp_le_n_max hth
    simp only [wp_large_M hth, wp_large_nSlice hth, wp_large_w hth,
      wp_large_globalPtrBits hth, wp_large_offBktMeta hth,
      wp_large_offBtMeta hth, wp_large_nodeMetaBits hth,
      wp_large_offBtKeys hth, wp_large_keysWordBits hth,
      wp_large_offBtVals hth, wp_large_valsWordBits hth] at hsIdx hu1 hu2 hu3 ⊢
    have hidx1 : sIdx * nSliceWhp n_max + u1 < totalBTreeNodesWhp n_max := by
      unfold totalBTreeNodesWhp
      calc sIdx * nSliceWhp n_max + u1 < sIdx * nSliceWhp n_max + nSliceWhp n_max :=
            Nat.add_lt_add_left hu1 _
        _ = (sIdx + 1) * nSliceWhp n_max := by ring
        _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx
    have hidx2 : sIdx * nSliceWhp n_max + u2 < totalBTreeNodesWhp n_max := by
      unfold totalBTreeNodesWhp
      calc sIdx * nSliceWhp n_max + u2 < sIdx * nSliceWhp n_max + nSliceWhp n_max :=
            Nat.add_lt_add_left hu2 _
        _ = (sIdx + 1) * nSliceWhp n_max := by ring
        _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx
    have hidx3 : sIdx * nSliceWhp n_max + u3 < totalBTreeNodesWhp n_max := by
      unfold totalBTreeNodesWhp
      calc sIdx * nSliceWhp n_max + u3 < sIdx * nSliceWhp n_max + nSliceWhp n_max :=
            Nat.add_lt_add_left hu3 _
        _ = (sIdx + 1) * nSliceWhp n_max := by ring
        _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (hidx1.le.trans htot_le)
    | exact henv.fits_of_le_n_max (hidx2.le.trans htot_le)
    | exact henv.fits_of_le_n_max (hidx3.le.trans htot_le)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.btMeta_safe hidx1
    | exact henv.btKeys_safe hidx1
    | exact henv.btVals_safe hidx1
    | exact henv.btMeta_safe hidx2
    | exact henv.btKeys_safe hidx2
    | exact henv.btVals_safe hidx2
    | exact henv.btMeta_safe hidx3
    | exact henv.btKeys_safe hidx3
    | exact henv.btVals_safe hidx3
    | exact henv.bktMeta_safe (by omega)


/-- Opaque 4-write split helper (`3` node writes + `writeSliceAlloc`) so `ensureAndSplitRootGenProg`
and `descendSplitStepGenProg` perform only a single subroutine reindexing instead of four. -/
@[irreducible] def writeSplitFourOpProg
    (d : (((WhpCoreParams × ℕ) × ℕ) ×
      (((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))) × ((ℕ × (ℕ × (ℕ × ℕ))) × ℕ)))) :
    Memory.Prog Unit :=
  writeSplitFourBody d

theorem realizes_writeSplitFourOp :
    Realizes .exact writeSplitFourOpProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) ×
        (((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))) × ((ℕ × (ℕ × (ℕ × ℕ))) × ℕ)))))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), sIdx), (((u1, _), (u2, _)), ((u3, _), _))) _ =>
        WhpLargeEnvGen w cp base ∧
        sIdx < 3 * wpM cp ∧
        u1 < wpNSlice cp ∧
        u2 < wpNSlice cp ∧
        u3 < wpNSlice cp)
      (fun _ _ => 0) := by
  unfold writeSplitFourOpProg; exact realizes_writeSplitFourBody

theorem writeSplitFourOpProg_eq
    (p : (WhpCoreParams × ℕ) × ℕ)
    (idx1 : ℕ) (nd1 : ℕ × (ℕ × ℕ))
    (idx2 : ℕ) (nd2 : ℕ × (ℕ × ℕ))
    (idx3 : ℕ) (nd3 : ℕ × (ℕ × ℕ))
    (newA : ℕ) :
    writeSplitFourOpProg (p, (((idx1, nd1), (idx2, nd2)), ((idx3, nd3), newA))) =
      (writeBTreeNodeGenProg ((p, idx1), nd1) >>= fun _ =>
       writeBTreeNodeGenProg ((p, idx2), nd2) >>= fun _ =>
       writeBTreeNodeGenProg ((p, idx3), nd3) >>= fun _ =>
       writeSliceAllocGenProg (p, newA)) := by
  unfold writeSplitFourOpProg writeSplitFourBody writeBTreeNodeGenProg writeSliceAllocGenProg
  simp only [pure_bind, bind_assoc]

theorem clientState_bind_pure {α : Type} (m : Memory.Prog Unit)
    (a : α) (s : Memory.State) :
    (Memory.spec 0).clientState s (m >>= fun _ => pure a) =
      (Memory.spec 0).clientState s m := by
  rw [clientState_bind]; rfl

theorem clientResult_bind_pure {α : Type} (m : Memory.Prog Unit)
    (a : α) (s : Memory.State) :
    (Memory.spec 0).clientResult s (m >>= fun _ => pure a) = a := by
  rw [clientResult_bind, StateTransitionSpec.clientResult_pure]

theorem clientState_bind_pure_ite {α : Type} (m : Memory.Prog Unit)
    (cond : Prop) [Decidable cond] (a b : α) (s : Memory.State) :
    (Memory.spec 0).clientState s (m >>= fun _ => if cond then pure a else pure b) =
      (Memory.spec 0).clientState s m := by
  rw [clientState_bind]
  split_ifs <;> rfl

theorem clientResult_bind_pure_ite {α : Type} (m : Memory.Prog Unit)
    (cond : Prop) [Decidable cond] (a b : α) (s : Memory.State) :
    (Memory.spec 0).clientResult s (m >>= fun _ => if cond then pure a else pure b) =
      if cond then a else b := by
  rw [clientResult_bind]
  split_ifs <;> rfl

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
