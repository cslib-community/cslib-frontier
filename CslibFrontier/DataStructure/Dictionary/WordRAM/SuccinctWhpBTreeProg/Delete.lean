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
# Certified SWAR B+-Tree Lazy Leaf Deletion (`btreeDeleteGenProg`)

Parameter-free `Memory.Prog` implementation, `O(1)` specification, and `Realizes .exact`
certificate for `btreeDelete`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeDeleteGenProg`: parameter-free
  `Memory.Prog` implementation of `btreeDelete`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeDeleteGenProg_spec`: exact refinement,
  `memoryCost ≤ 274`, `ValidProg`, and slice/segment frame laws.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_btreeDeleteGen`: `Realizes .exact`
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

/-- Parameter-free `btreeDelete` (`d = (((cp, base), sIdx), q)`). -/
@[irreducible] def btreeDeleteGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), sIdx), q) => do
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
      let cnt ← pure (mW / 2)
      let m' ← pure (1 + 2 * (cnt - 1))
      let k' ← wordDeleteAtGenProg ((wpWKey cp, r), kW)
      let v' ← wordDeleteAtGenProg ((wpWVal cp, r), vW)
      writeBTreeNodeGenProg ((((cp, base), sIdx), leafIdx), (m', (k', v')))

theorem btreeDeleteGenProg_spec {c U V w n_max base sIdx insCount q : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) :
    let prog := btreeDeleteGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q
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
  obtain ⟨_, hmeta_cap, _, _⟩ := (btree_slice_param_bounds hth).1
  obtain ⟨hst, hmc, hvp, hres⟩ :=
    btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
  dsimp only at hst hmc hvp hres ⊢
  unfold btreeDeleteGenProg
  simp only [wp_large_wKey hth, wp_large_wVal hth, pure_bind]
  rcases hres with ⟨hres0, _, hdel0, _⟩ |
      ⟨leafIdx, r, hres1, hleaf_lt, hrc, hcnt_le, _, _, hkw_cnt, hvw_cnt, _, hdel1, _⟩
  · have hloc := bind_of_readOnly hst hres0 hvp
    rw [hdel0]
    simp only [(hloc _ _).1, (hloc _ _).2.2.1, (hloc _ _).2.2.2,
      ↓reduceIte, memoryCost_pure, Nat.add_zero]
    exact ⟨rfl, hmc.trans (by decide), validProg_pure _, hrep, fun _ _ _ _ hr => hr, fun _ _ => rfl⟩
  · set nd := sl.nodes leafIdx
    set cnt := metaCount nd.metaWord
    have hcnt_pos : 1 ≤ cnt := by omega
    have hcnt_div : nd.metaWord / 2 = cnt := rfl
    let nd' : BTreeNode :=
      ⟨mkNodeMeta true (cnt - 1),
        wordDeleteAt (fpBitsWhp n_max + 2) r nd.keysWord,
        wordDeleteAt (valLaneBitsWhp n_max) r nd.valsWord⟩
    have hm'_lt : nd'.metaWord < 2 ^ nodeMetaBitsWhp n_max := by
      dsimp only [nd', mkNodeMeta]; simp only [↓reduceIte]; omega
    have hdel_lt {b w0 : ℕ} (hw0 : w0 < 2 ^ (cnt * b)) :
        wordDeleteAt b r w0 < 2 ^ (2 * tMinWhp n_max * b) :=
      (wordDeleteAt_lt (m := cnt - 1) (Nat.le_sub_one_of_lt hrc)
        (by rwa [Nat.sub_add_cancel hcnt_pos])).trans_le
        (Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul_right b ((Nat.sub_le cnt 1).trans (hcnt_le.trans (Nat.sub_le _ _)))))
    have hk'_lt : nd'.keysWord < 2 ^ keysWordBitsWhp n_max := hdel_lt hkw_cnt
    have hv'_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max := hdel_lt hvw_cnt
    obtain ⟨hwn_fr, _, hwn_vp, hwn_rep, hwn_other, hwn_out⟩ :=
      writeBTreeNodeGenProg_inPlace_sliceRep (nd' := nd') henv hsIdx hrep hleaf_lt
        hm'_lt hk'_lt hv'_lt (s := s)
    have hloc := bind_of_readOnly hst hres1 hvp
    rw [hdel1]
    simp only [(hloc _ _).1, (hloc _ _).2.2.1, (hloc _ _).2.2.2,
      Nat.one_ne_zero, ↓reduceIte, hcnt_div]
    rw [clientState_bind, clientState_wordDeleteAtGenProg, clientResult_wordDeleteAtGenProg,
      clientState_bind, clientState_wordDeleteAtGenProg, clientResult_wordDeleteAtGenProg]
    refine ⟨hwn_fr, ?_, ?_, hwn_rep, hwn_other, hwn_out⟩
    · simpa only [memoryCost_bind', memoryCost_wordDeleteAtGenProg,
        memoryCost_writeBTreeNodeGenProg, Nat.zero_add] using Nat.add_le_add_right hmc 12
    · refine validProg_bind (validWhpProg_wordDeleteAtGenProg _) ?_
      rw [clientState_wordDeleteAtGenProg, clientResult_wordDeleteAtGenProg]
      refine validProg_bind (validWhpProg_wordDeleteAtGenProg _) ?_
      rw [clientState_wordDeleteAtGenProg, clientResult_wordDeleteAtGenProg]
      exact hwn_vp

theorem realizes_btreeDeleteGen :
    Realizes .exact btreeDeleteGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      BTreeQueryGenPre
      (fun _ _ => 0) := by
  unfold btreeDeleteGenProg
  have hloc := realizes_btreeLocateHitGen
  have hwd := realizes_wordDeleteAtGen
  have hwn := realizes_writeBTreeNodeGen
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, q⟩
    dsimp only [BTreeQueryGenPre] at *
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv, hq⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
  · exact ⟨c, U, V, w, n_max, insCount, sl, mapFn, henv, rfl, hsIdx, hins, hrep, hv, hq⟩
  · decide
  · exact henv.fits_const (by decide)
  all_goals
    obtain ⟨_, _, _, hres⟩ := btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
    dsimp only at hres
    rcases hres with ⟨hres0, _⟩ |
        ⟨leafIdx, r, hres1, hleaf_lt, hrc, hcnt_le, _, _, hkw_cnt, hvw_cnt, _⟩
    · simp_all
    simp only [hres1] at *
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    have ht8 := eight_le_tMinWhp hth
    have hcnt_div : (sl.nodes leafIdx).metaWord / 2 = metaCount (sl.nodes leafIdx).metaWord := rfl
  · rw [hcnt_div]; omega
  · have hkl2 : 2 ≤ keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp fpBitsWhp; omega
    have : 1 + 2 * ((sl.nodes leafIdx).metaWord / 2 - 1) < w := by
      have : 2 * (2 * tMinWhp n_max) ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max := by
        rw [Nat.mul_comm 2 (2 * tMinWhp n_max)]; exact Nat.mul_le_mul_left _ hkl2
      rw [hcnt_div]; omega
    exact this.trans Nat.lt_two_pow_self
  · simp only [wp_large_wKey hth]
    refine ⟨metaCount (sl.nodes leafIdx).metaWord - 1,
      by unfold keyLaneBitsWhp; positivity, by omega,
      (Nat.mul_le_mul_right _ (by omega)).trans_lt hkw_lt, ?_⟩
    rwa [Nat.sub_add_cancel (by omega)]
  · simp only [wp_large_wVal hth]
    refine ⟨metaCount (sl.nodes leafIdx).metaWord - 1,
      by unfold valLaneBitsWhp; positivity, by omega,
      (Nat.mul_le_mul_right _ (by omega)).trans_lt hvw_lt, ?_⟩
    rwa [Nat.sub_add_cancel (by omega)]
  · exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · simp only [wp_large_M hth]; exact hsIdx
  · simp only [wp_large_nSlice hth]; exact hleaf_lt.trans_le hrep.1

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
