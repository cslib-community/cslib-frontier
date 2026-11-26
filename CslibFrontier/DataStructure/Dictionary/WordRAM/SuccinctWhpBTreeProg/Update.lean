/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Pre
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Helpers
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.LocateHit
import CslibFrontier.Tactic.Realize

/-!
# Certified SWAR B+-Tree In-Place Leaf Value Update (`btreeUpdateGenProg`)

Parameter-free `Memory.Prog` implementation, `O(1)` specification, and `Realizes .exact`
certificate for `btreeUpdate`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeUpdateGenProg`: parameter-free
  `Memory.Prog` implementation of `btreeUpdate`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeUpdateGenProg_spec`: exact refinement,
  `memoryCost ≤ 274`, `ValidProg`, and slice/segment frame laws.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_btreeUpdateGen`: `Realizes .exact`
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

/-- Parameter-free `btreeUpdate` (`d = ((((cp, base), sIdx), q), newVal)`). -/
@[irreducible] def btreeUpdateGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), sIdx), q), newVal) => do
    let loc ← btreeLocateHitGenProg (((cp, base), sIdx), q)
    let (hitFlag, rest) := loc
    let (lr, nd) := rest
    let (leafIdx, r) := lr
    let (mW, kv) := nd
    let (kW, vW) := kv
    let z0 ← pure 0
    if hitFlag = z0 then
      pure ()
    else do
      let v' ← wordUpdateAtGenProg (((wpWVal cp, r), newVal), vW)
      writeBTreeNodeGenProg ((((cp, base), sIdx), leafIdx), (mW, (kW, v')))

theorem btreeUpdateGenProg_spec {c U V w n_max base sIdx insCount q newVal : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) (hval : newVal < 2 ^ valLaneBitsWhp n_max) :
    let prog := btreeUpdateGenProg ((((mkWhpCoreParams c U V w n_max, base), sIdx), q), newVal)
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q newVal
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 274 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx sl' s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  obtain ⟨hst, hmc, hvp, hres⟩ :=
    btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
  dsimp only at hst hmc hvp hres ⊢
  unfold btreeUpdateGenProg
  simp only [wp_large_wVal hth, pure_bind]
  rcases hres with ⟨hres0, _, _, hupd0⟩ |
      ⟨leafIdx, r, hres1, hleaf_lt, hrc, hcnt_le, hm_lt, hk_lt, _, hvw_cnt, _, _, hupd1⟩
  · rw [hupd0 newVal, clientState_bind, hst, hres0]
    refine ⟨rfl, ?_, ?_, hrep, fun _ _ _ _ hr => hr, fun _ _ => rfl⟩
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres0]
      simp only [↓reduceIte, memoryCost_pure]; omega
    · refine validProg_bind hvp ?_
      rw [hst, hres0]; exact validProg_pure _
  · set nd := sl.nodes leafIdx
    set cnt := metaCount nd.metaWord
    let nd' : BTreeNode :=
      ⟨nd.metaWord, nd.keysWord, wordUpdateAt (valLaneBitsWhp n_max) r newVal nd.valsWord⟩
    have hv'_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max := by
      unfold valsWordBitsWhp
      exact (wordUpdateAt_lt hrc hval hvw_cnt).trans_le
        (Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul_right _ (hcnt_le.trans (Nat.sub_le _ _))))
    obtain ⟨hwn_fr, hwn_mc, hwn_vp, hwn_rep, hwn_other, hwn_out⟩ :=
      writeBTreeNodeGenProg_inPlace_sliceRep (nd' := nd') henv hsIdx hrep hleaf_lt
        hm_lt hk_lt hv'_lt (s := s)
    rw [hupd1 newVal, clientState_bind, hst, hres1]
    simp only [Nat.one_ne_zero, ↓reduceIte]
    rw [clientState_bind, clientState_wordUpdateAtGenProg, clientResult_wordUpdateAtGenProg]
    refine ⟨hwn_fr, ?_, ?_, hwn_rep, hwn_other, hwn_out⟩
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres1]
      simp only [Nat.one_ne_zero, ↓reduceIte]
      rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, clientState_wordUpdateAtGenProg,
        memoryCost_wordUpdateAtGenProg, memoryCost_writeBTreeNodeGenProg]
      omega
    · refine validProg_bind hvp ?_
      rw [hst, hres1]; simp only [Nat.one_ne_zero, ↓reduceIte]
      refine validProg_bind (validWhpProg_wordUpdateAtGenProg _) ?_
      rw [clientState_wordUpdateAtGenProg, clientResult_wordUpdateAtGenProg]
      exact hwn_vp

theorem realizes_btreeUpdateGen :
    Realizes .exact btreeUpdateGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      BTreeModGenPre
      (fun _ _ => 0) := by
  unfold btreeUpdateGenProg
  have hloc := realizes_btreeLocateHitGen
  have hwu := realizes_wordUpdateAtGen
  have hwn := realizes_writeBTreeNodeGen
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, sIdx⟩, q⟩, newVal⟩
    dsimp only [BTreeModGenPre] at *
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv, hq, hval⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
  · exact ⟨c, U, V, w, n_max, insCount, sl, mapFn, henv, rfl, hsIdx, hins, hrep, hv, hq⟩
  all_goals
    obtain ⟨_, _, _, hres⟩ := btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
    dsimp only at hres
    rcases hres with ⟨hres0, _⟩ |
        ⟨leafIdx, r, hres1, hleaf_lt, hrc, hcnt_le, _, _, _, hvw_cnt, _⟩
    · simp_all
    simp only [hres1] at *
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    have ht8 := eight_le_tMinWhp hth
  · simp only [wp_large_wVal hth]
    exact ⟨metaCount (sl.nodes leafIdx).metaWord,
      by unfold valLaneBitsWhp; positivity, hrc,
      (Nat.mul_le_mul_right _ (by omega)).trans_lt hvw_lt, hval, hvw_cnt⟩
  · exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · simp only [wp_large_M hth]; exact hsIdx
  · simp only [wp_large_nSlice hth]; exact hleaf_lt.trans_le hrep.1

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
