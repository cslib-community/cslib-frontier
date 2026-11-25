/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Pre
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.EnsureRoot
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.DescendSplit
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.FinishLeaf
import CslibFrontier.Tactic.Realize

/-!
# Certified SWAR Top-Down Proactive-Split B+-Tree Insertion (`btreeInsertGenProg`)

Assembles `ensureAndSplitRootGenProg`, `descendSplitLoopGenProg`, and `finishLeafInsertGenProg`
into `btreeInsertGenProg` with its `O(1)` (`≤ 2426`) specification and `Realizes .exact`
certificate.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeInsertGenProg`: parameter-free
  `Memory.Prog` implementation of `btreeInsert`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeInsertGenProg_spec`: exact refinement,
  `memoryCost ≤ 2426`, `ValidProg`, `ValidWhpSlice` preservation, and slice/segment frame laws.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_btreeInsertGen`: `Realizes .exact`
  certificate with zero local work.
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

/-- Parameter-free `btreeInsert` (`d = ((((cp, base), sIdx), q), val)`), factored cleanly into
`ensureAndSplitRootGenProg`, `descendSplitLoopGenProg`, and `finishLeafInsertGenProg`. -/
@[irreducible] def btreeInsertGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), sIdx), q), val) => do
    let ar1 ← ensureAndSplitRootGenProg ((cp, base), sIdx)
    let ar2 ← descendSplitLoopGenProg (((((cp, base), sIdx), q), ar1), wpHMaxBTree cp)
    finishLeafInsertGenProg (((((cp, base), sIdx), ar2.2), q), val)

theorem btreeInsertGenProg_spec {c U V w n_max base sIdx insCount q val : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) (hval : val < 2 ^ valLaneBitsWhp n_max) :
    let prog := btreeInsertGenProg ((((mkWhpCoreParams c U V w n_max, base), sIdx), q), val)
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q val
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 2426 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx sl' s'.mem ∧
    ValidWhpSlice n_max (insCount + 1) sl' (Function.update mapFn q (some val)) ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ idx < 16 * numBucketsWhp n_max,
      idx ≠ 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) →
      idx ≠ 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3) →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, (a < base + offBktMeta c U V w n_max ∨
        (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
        base + offTrieChild0 c U V w n_max ≤ a) →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hv_ins := (hv.insert_spec hth hins hq hval).2
  obtain ⟨hfr1, hres1, hmc1, hvp1, hrep1, halloc1, ⟨T1, hrt1, hht1, hnf1, hv1⟩,
    hoth1, hbm1, hout1⟩ := ensureAndSplitRootGenProg_spec henv hsIdx hins hrep hv (s := s)
  set s1 := (Memory.spec 0).clientState s
    (ensureAndSplitRootGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx))
  have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
    Nat.sub_lt (Nat.two_pow_pos _) one_pos
  obtain ⟨hfr2, hres2, hmc2, hvp2, _, hrep2, ⟨isR, cntL, loL, hiL, hcntL, hqlo, hqhi, hhiL, hvlf⟩,
    hoth2, hbm2, hout2⟩ :=
    descendSplitLoopGenProg_spec henv hsIdx hrep1 halloc1.le hrt1 hnf1 hht1
      (Nat.zero_le q) (by omega) hhi hv1 (s := s1) (fuel := hMaxBTree)
  set sl1 := splitRootIfFull (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
    (ensureRootSlice sl)
  set d0 := (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
  set s2 := (Memory.spec 0).clientState s1
    (descendSplitLoopGenProg ((d0, (sl1.alloc, sl1.root)), hMaxBTree))
  set p := descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
    hMaxBTree sl1 sl1.root q
  obtain ⟨hfr3, hmc3, hvp3, hrep3, hoth3, hout3⟩ :=
    finishLeafInsertGenProg_spec henv hsIdx hrep2 hcntL hqlo hqhi hhiL hval hvlf (s := s2)
  have hoff := largeOffsetChain c U V w n_max
  unfold btreeInsertGenProg
  dsimp only [d0]
  simp only [wp_large_hMaxBTree hth]
  rw [clientState_bind, hres1, clientState_bind, hres2]
  refine ⟨hfr3.trans (hfr2.trans hfr1), ?_, ?_, hrep3, hv_ins, ?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s1, s2, d0] at hmc1 hmc2 hmc3 hres1 hres2 ⊢
    rw [hres1, hres2, hmc3]
    rw [hMaxBTree_eq] at hmc2 ⊢
    omega
  · refine validProg_bind hvp1 ?_
    rw [hres1]
    refine validProg_bind hvp2 ?_
    rw [hres2]
    exact hvp3
  · intro sIdx' hsIdx' hne sl₂ hr₂
    exact hoth3 sIdx' hsIdx' hne sl₂ (hoth2 sIdx' hsIdx' hne sl₂ (hoth1 sIdx' hsIdx' hne sl₂ hr₂))
  · intro idx hidx h1 h2
    exact (readPacked_congr hw (mem₂ := s2.mem) (fun a ⟨_, ha2⟩ => hout3 a (Or.inl (by omega)))
      hidx).trans ((hbm2 idx hidx h1).trans (hbm1 idx hidx h1 h2))
  · intro a ha
    exact (hout3 a (by omega)).trans ((hout2 a ha).trans (hout1 a ha))

theorem realizes_btreeInsertGen :
    Realizes .exact btreeInsertGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      BTreeModGenPre
      (fun _ _ => 0) := by
  unfold btreeInsertGenProg
  have her := realizes_ensureAndSplitRootGen
  have hdsl := realizes_descendSplitLoopGen
  have hfl := realizes_finishLeafInsertGen
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, sIdx⟩, q⟩, val⟩
    dsimp only [BTreeModGenPre] at h
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv, hq, hval⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    obtain ⟨_, hres1, _, _, hrep1, halloc1, ⟨T1, hrt1, hht1, hnf1, hv1⟩, _, _, _⟩ :=
      ensureAndSplitRootGenProg_spec henv hsIdx hins hrep hv (s := s)
    have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
      Nat.sub_lt (Nat.two_pow_pos _) one_pos
    simp only [hres1, wp_large_hMaxBTree hth] at *
  · exact ⟨c, U, V, w, n_max, insCount, sl, mapFn, henv, rfl, hsIdx, hins, hrep, hv⟩
  · exact (descendSplitLoopGenProg_spec henv hsIdx hrep1 halloc1.le hrt1 hnf1 hht1
      (Nat.zero_le q) (by omega) hhi hv1
      (s := (Memory.spec 0).clientState s
        (ensureAndSplitRootGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx)))
      (fuel := hMaxBTree)).2.2.2.2.1
  · obtain ⟨_, hres2, _, _, _, hrep2, ⟨isR, cntL, loL, hiL, hcntL, hqlo, hqhi, hhiL, hvlf⟩,
      _, _, _⟩ :=
      descendSplitLoopGenProg_spec henv hsIdx hrep1 halloc1.le hrt1 hnf1 hht1
        (Nat.zero_le q) (by omega) hhi hv1
        (s := (Memory.spec 0).clientState s
          (ensureAndSplitRootGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx)))
        (fuel := hMaxBTree)
    rw [hres2]
    exact ⟨c, U, V, w, n_max, _, isR, cntL, loL, hiL, mapFn,
      henv, rfl, hsIdx, hrep2, hcntL, hqlo, hqhi, hhiL, hval, hvlf⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
