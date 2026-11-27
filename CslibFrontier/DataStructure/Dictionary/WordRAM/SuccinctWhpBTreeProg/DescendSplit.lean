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
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.SplitOps
import CslibFrontier.Tactic.Realize

/-!
# Top-Down Proactive-Splitting Descent (`descendSplitLoopGenProg`)

Implements and certifies phase 2 of `btreeInsertGenProg`: descending from a non-full internal node
to a guaranteed non-full leaf via `Realizes.iterate₀`, proactively splitting any full child along
the search path.
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

private def SplitFullChildPre (w : ℕ)
    (x : ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) ×
      (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))) (_s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max,
    WhpLargeEnv c U V w₀ n_max w x.1.1.1.1.2 ∧
    x.1.1.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    x.1.1.1.2 < 3 * numBucketsWhp n_max ∧
    x.1.2.1 + 1 ≤ nSliceWhp n_max ∧
    x.1.2.2 < x.1.2.1 ∧
    x.2.2.1 < x.1.2.1 ∧
    x.2.1.1.1 < 2 * tMinWhp n_max - 1 ∧
    x.2.1.1.2 ≤ x.2.1.1.1 ∧
    x.2.1.2.1 < 2 ^ (x.2.1.1.1 * keyLaneBitsWhp n_max) ∧
    x.2.1.2.2 < 2 ^ ((x.2.1.1.1 + 1) * valLaneBitsWhp n_max)

private def splitFullChildBody
    (x : ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) ×
      (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))) : Memory.Prog (ℕ × ℕ) := do
  let sp ← splitNodeOpProg (x.1.1.1.1.1, x.2.2.2)
  let rightIdx ← pure x.1.2.1
  let newAlloc ← pure (x.1.2.1 + 1)
  let pMeta ← pure (2 * (x.2.1.1.1 + 1))
  let pKeys ← wordInsertOpProg (((wpWKey x.1.1.1.1.1, x.2.1.1.2), sp.2.1), x.2.1.2.1)
  let r1 ← pure (x.2.1.1.2 + 1)
  let pVals ← wordInsertOpProg (((wpWVal x.1.1.1.1.1, r1), rightIdx), x.2.1.2.2)
  writeSplitFourOpProg (x.1.1.1, (((x.2.2.1, sp.1), (rightIdx, sp.2.2)),
    ((x.1.2.2, (pMeta, (pKeys, pVals))), newAlloc)))
  if sp.2.1 < x.1.1.2 then
    pure (newAlloc, rightIdx)
  else
    pure (newAlloc, x.2.2.1)

private theorem realizes_splitFullChildBody :
    Realizes .exact splitFullChildBody
      (WordEncoding.encode (α := ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) ×
        (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))))
      (WordEncoding.encode (α := ℕ × ℕ))
      SplitFullChildPre
      (fun _ _ => 0) := by
  have hsp := realizes_splitNodeOp
  have hwi := realizes_wordInsertOp
  have hsf := realizes_writeSplitFourOp
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨⟨cp, base⟩, sIdx⟩, q⟩, ⟨alloc, cur⟩⟩, ⟨⟨⟨c0, r0⟩, ⟨pKW, pVW⟩⟩,
      ⟨childIdx, ⟨cmW, ⟨ckW, cvW⟩⟩⟩⟩⟩
    dsimp only [SplitFullChildPre] at h
    obtain ⟨c, U, V, w₀, n_max, henv, rfl, hsIdx, halloc1, hcur, hchild, hc0, hr_le,
      hkw_cnt, hvw_cnt⟩ := h
    have hth := henv.2.2.2.1
    obtain rfl := henv.2.2.1
    have ht8 := eight_le_tMinWhp hth
    have hns_lt_n := (large_bounds_lt_n_max hth).2.1
    obtain ⟨_, _, _, hns_lt_v⟩ := (btree_slice_param_bounds hth).1
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    have hkl2 : 2 ≤ keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp fpBitsWhp; omega
    simp only [wp_large_M hth] at *
    try simp only [wp_large_nSlice hth] at *
    try simp only [wp_large_wKey hth] at *
    try simp only [wp_large_wVal hth] at *
    have h2t_k : 2 * tMinWhp n_max ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h4t_k : 2 * (2 * tMinWhp n_max) ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max := by
      rw [Nat.mul_comm 2 (2 * tMinWhp n_max)]; exact Nat.mul_le_mul_left _ hkl2
    first
    | omega
    | exact ⟨base, c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact henv.fits_of_le_n_max (by omega)
    | exact (by omega : 2 * (c0 + 1) < w).trans Nat.lt_two_pow_self
    | exact (by omega : c0 + 1 < w).trans Nat.lt_two_pow_self
    | exact (by omega : r0 + 1 < w).trans Nat.lt_two_pow_self
    | (refine ⟨c0, hr_le, (Nat.mul_le_mul_right _ (by omega)).trans_lt hkw_lt, ?_, hkw_cnt⟩
       have hres := clientResult_splitNodeOpProg (U := U) (V := V) (w := w) hth ⟨cmW, ckW, cvW⟩ s
       dsimp only at hres
       rw [hres]
       unfold splitFullNode keyLaneBitsWhp
       by_cases hlf : metaIsLeaf cmW = true <;>
         (simp only [hlf, Bool.false_eq_true, ↓reduceIte]
          rw [laneGet_eq_div_mod]
          exact Nat.mod_lt _ (Nat.two_pow_pos _)))
    | refine ⟨c0 + 1, Nat.succ_le_succ hr_le,
        (Nat.mul_le_mul_right _ (by omega)).trans_lt hvw_lt,
        (by omega : alloc < nSliceWhp n_max).trans hns_lt_v, hvw_cnt⟩

/-- Opaque full-child split-and-link subroutine for `descendSplitStepGenProg`. -/
@[irreducible] private def splitFullChildOpProg
    (x : ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) ×
      (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))) : Memory.Prog (ℕ × ℕ) :=
  splitFullChildBody x

private theorem realizes_splitFullChildOp :
    Realizes .exact splitFullChildOpProg
      (WordEncoding.encode (α := ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) ×
        (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))))
      (WordEncoding.encode (α := ℕ × ℕ))
      SplitFullChildPre
      (fun _ _ => 0) := by
  unfold splitFullChildOpProg; exact realizes_splitFullChildBody

/-- Precondition for one proactive-splitting descent step
`d = ((((cp, base), sIdx), q), (alloc, cur))`. -/
private def DescendSplitStepGenPre (w : ℕ)
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max sl isRoot lo hi mapFn T,
    WhpLargeEnv c U V w₀ n_max w d.1.1.1.2 ∧
    d.1.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    d.1.1.2 < 3 * numBucketsWhp n_max ∧
    BTreeSliceMemRep d.1.1.1.2 c U V w₀ n_max d.1.1.2 sl s.mem ∧
    sl.alloc = d.2.1 ∧
    sl.alloc + 1 ≤ nSliceWhp n_max ∧
    T.rootIdx = d.2.2 ∧
    metaCount (sl.nodes d.2.2).metaWord < 2 * tMinWhp n_max - 1 ∧
    lo ≤ d.1.2 ∧ d.1.2 ≤ hi ∧ hi < 2 ^ fpBitsWhp n_max ∧
    ValidSubtree isRoot (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.alloc sl.nodes lo hi mapFn T

/-- Single step of `descendSplitToLeaf` (`d = ((((cp, base), sIdx), q), (alloc, cur))`). -/
private def descendSplitStepGenProg
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let nd ← readBTreeNodeGenProg (d.1.1, d.2.2)
  let isLf ← pure (nd.1 % 2)
  let z1 ← pure 1
  if isLf = z1 then
    pure d.2
  else do
    let cnt ← pure (nd.1 / 2)
    let r ← swarRankGenProg (d.1.1.1.1, ((cnt, d.1.2), nd.2.1))
    let childIdx ← laneGetGenProg ((wpWVal d.1.1.1.1, nd.2.2), r)
    let childNd ← readBTreeNodeGenProg (d.1.1, childIdx)
    let childCnt ← pure (childNd.1 / 2)
    let fullCnt ← pure (2 * wpTMin d.1.1.1.1 - 1)
    if childCnt = fullCnt then
      splitFullChildOpProg (d, (((cnt, r), (nd.2.1, nd.2.2)), (childIdx, childNd)))
    else
      pure (d.2.1, childIdx)

private theorem memoryCost_descendSplitStepGenProg_pos
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (descendSplitStepGenProg d) s := by
  unfold descendSplitStepGenProg
  rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readBTreeNodeGenProg]
  omega

private theorem realizes_descendSplitStepGen :
    Realizes .exact descendSplitStepGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      DescendSplitStepGenPre
      (fun _ _ => 0) := by
  unfold descendSplitStepGenProg
  have hrn := realizes_readBTreeNodeGen
  have hsr := realizes_swarRankGen
  have hlg := realizes_laneGetGen
  have hsfc := realizes_splitFullChildOp
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, sIdx⟩, q⟩, ⟨alloc, cur⟩⟩
    dsimp only [DescendSplitStepGenPre] at h
    obtain ⟨c, U, V, w₀, n_max, sl, isRoot, lo, hi, mapFn, T,
      henv, rfl, hsIdx, hrep, rfl, halloc1, hrt, hnf, hqlo, hqhi, hhi, hv⟩ := h
    have hth := henv.2.2.2.1
    obtain rfl := henv.2.2.1
    have ht8 := eight_le_tMinWhp hth
    have hns_lt_n := (large_bounds_lt_n_max hth).2.1
    obtain ⟨ht3, _, hkey_lt, hns_lt_v⟩ := (btree_slice_param_bounds hth).1
    obtain ⟨hcur_lt, hcnt_le, _, hkw_cnt, _, _, hlanes⟩ := validSubtree_root_bounds hth hhi hv
    rw [hrt] at hcur_lt hcnt_le hkw_cnt hlanes
    obtain ⟨hcs_n, hres_n, _, _⟩ := readBTreeNodeGenProg_spec hth henv.2.1 hsIdx hcur_lt hrep
      (s := s)
    dsimp only at hcs_n hres_n
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    have hcnt_div : (sl.nodes cur).metaWord / 2 = metaCount (sl.nodes cur).metaWord := rfl
    simp only [hcs_n, hres_n] at *
    try simp only [wp_large_M hth] at *
    try simp only [wp_large_nSlice hth] at *
    try simp only [wp_large_tMin hth] at *
    try simp only [wp_large_wVal hth] at *
    try simp only [clientResult_swarRankGenProg hth] at *
    try simp only [clientResult_laneGetGenProg] at *
    try first
      | decide
      | omega
      | exact henv.fits_const (by decide)
      | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · refine ⟨⟨base, c, U, V, w, n_max, henv, rfl⟩, ?_, ?_, ?_, ?_⟩
    · simp only [wp_large_capLanes hth]; change metaCount _ < _; omega
    · simp only [wp_large_powFp hth]; exact hqhi.trans_lt hhi
    · simp only [wp_large_wKey hth]; exact hkw_cnt
    · simp only [wp_large_wKey hth, wp_large_powFp hth]; exact hlanes
  · exact (Nat.le_mul_of_pos_left _ (by omega)).trans_lt hvw_lt
  · rw [hcnt_div]
    have hr_le : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max)
        (metaCount (sl.nodes cur).metaWord) q (sl.nodes cur).keysWord ≤
        metaCount (sl.nodes cur).metaWord := by
      rw [swarRank_eq_count_lt (by omega) hkey_lt (hqhi.trans_lt hhi) hkw_cnt hlanes]
      exact (card_filter_le _ _).trans_eq (card_range _)
    exact ((Nat.mul_le_mul_right _ (hr_le.trans (by omega))).trans_lt hvw_lt).trans
      Nat.lt_two_pow_self
  all_goals
    cases T with
    | leaf idx c0 =>
      rcases hrt.symm with rfl
      have hm1 : (sl.nodes cur).metaWord % 2 = 1 := by
        simp [hv.2.1, mkNodeMeta, Nat.add_mul_mod_self_left]
      simp_all
    | branch idx c0 childTrees =>
      rcases hrt.symm with rfl
      obtain ⟨hr_le, _, _, _⟩ := branch_child_routing (by omega) hkey_lt hv hhi hqlo hqhi
      obtain ⟨_, hmeta, _, _, _, hvw_cnt, _, _, _, _, _, _, hcs_sub⟩ := hv
      have hc0_eq : metaCount (sl.nodes cur).metaWord = c0 := by rw [hmeta, metaCount_mkNodeMeta]
      let r_fin : Fin (c0 + 1) := ⟨swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
        (sl.nodes cur).keysWord, Nat.lt_succ_of_le hr_le⟩
      have hval_r : laneGet (valLaneBitsWhp n_max) (sl.nodes cur).valsWord
          (swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q (sl.nodes cur).keysWord) =
          (childTrees r_fin).rootIdx := (hcs_sub r_fin).1
      have hchild_lt : (childTrees r_fin).rootIdx < sl.alloc :=
        (((hcs_sub r_fin).2).leafCount_le_card_nodeSet).1 _ (childTrees r_fin).rootIdx_mem_nodeSet
      obtain ⟨hndc_st, hndc_res, _, _⟩ :=
        readBTreeNodeGenProg_spec hth henv.2.1 hsIdx hchild_lt hrep (s := s)
      dsimp only at hndc_st hndc_res
      rw [hc0_eq] at hnf hkw_cnt
      simp only [hcnt_div, hc0_eq, hval_r, hndc_st, hndc_res] at *
      try dsimp only [SplitFullChildPre]
      have h2t_lt : 2 * tMinWhp n_max < w :=
        (Nat.le_mul_of_pos_right _ (by unfold keyLaneBitsWhp; positivity)).trans_lt hkw_lt
      first
      | omega
      | exact h2t_lt.trans Nat.lt_two_pow_self
      | exact ⟨c, U, V, w, n_max, henv, rfl, hsIdx, halloc1, hcur_lt, hchild_lt, hnf, hr_le,
          hkw_cnt, hvw_cnt⟩


/-- Bounded `iterate` loop refining `descendSplitToLeaf`
(`d = (((((cp, base), sIdx), q), (alloc, cur)), fuel)`). -/
def descendSplitLoopGenProg :
    ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((d0, ac), fuel) => iterate descendSplitStepGenProg d0 fuel ac

/-- Precondition for `descendSplitLoopGenProg`
(`d = (((((cp, base), sIdx), q), (alloc, cur)), fuel)`). -/
def DescendSplitLoopGenPre (w : ℕ) :
    ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((d0, ac), fuel), s =>
    iterationSafe descendSplitStepGenProg DescendSplitStepGenPre w d0 fuel ac s

theorem realizes_descendSplitLoopGen :
    Realizes .exact descendSplitLoopGenProg
      (WordEncoding.encode (α := ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      DescendSplitLoopGenPre
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_descendSplitStepGen memoryCost_descendSplitStepGenProg_pos

/-- One unrolled iteration of `descendSplitLoopGenProg`: a safe step with known final state and
result, cost at most `52` and valid history reduces the loop's facts to the remaining loop's. -/
private theorem descendSplitLoop_succ {w F f : ℕ} {d0 : ((WhpCoreParams × ℕ) × ℕ) × ℕ}
    {a r : ℕ × ℕ} {s s₁ : Memory.State}
    (hpre : DescendSplitStepGenPre w (d0, a) s)
    (hstep : (Memory.spec 0).clientState s (descendSplitStepGenProg (d0, a)) = s₁ ∧
      (Memory.spec 0).clientResult s (descendSplitStepGenProg (d0, a)) = r ∧
      memoryCost (descendSplitStepGenProg (d0, a)) s ≤ 52 ∧
      ValidProg w F s (descendSplitStepGenProg (d0, a))) :
    (Memory.spec 0).clientState s (descendSplitLoopGenProg ((d0, a), f + 1)) =
      (Memory.spec 0).clientState s₁ (descendSplitLoopGenProg ((d0, r), f)) ∧
    (Memory.spec 0).clientResult s (descendSplitLoopGenProg ((d0, a), f + 1)) =
      (Memory.spec 0).clientResult s₁ (descendSplitLoopGenProg ((d0, r), f)) ∧
    (memoryCost (descendSplitLoopGenProg ((d0, r), f)) s₁ ≤ 52 * f →
      memoryCost (descendSplitLoopGenProg ((d0, a), f + 1)) s ≤ 52 * (f + 1)) ∧
    (ValidProg w F s₁ (descendSplitLoopGenProg ((d0, r), f)) →
      ValidProg w F s (descendSplitLoopGenProg ((d0, a), f + 1))) ∧
    (iterationSafe descendSplitStepGenProg DescendSplitStepGenPre w d0 f r s₁ →
      iterationSafe descendSplitStepGenProg DescendSplitStepGenPre w d0 (f + 1) a s) := by
  obtain ⟨hst, hres, hmc, hvp⟩ := hstep
  have hit : descendSplitLoopGenProg ((d0, a), f + 1) =
      descendSplitStepGenProg (d0, a) >>= fun r => descendSplitLoopGenProg ((d0, r), f) := rfl
  rw [hit]
  refine ⟨by rw [clientState_bind, hst, hres], by rw [clientResult_bind, hst, hres], fun h => ?_,
    fun h => validProg_bind hvp (by rw [hst, hres]; exact h),
    fun h => ⟨hpre, by rw [hst, hres]; exact h⟩⟩
  rw [memoryCost_bind', hst, hres]
  omega

theorem descendSplitLoopGenProg_spec {isRoot : Bool}
    {c U V w n_max base sIdx q cur fuel lo hi : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {T : BTreeTree} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (halloc_fuel : sl.alloc + fuel ≤ nSliceWhp n_max)
    (hrt : T.rootIdx = cur)
    (hnf : metaCount (sl.nodes cur).metaWord < 2 * tMinWhp n_max - 1)
    (hht_le : T.height ≤ fuel)
    (hqlo : lo ≤ q) (hqhi : q ≤ hi) (hhi : hi < 2 ^ fpBitsWhp n_max)
    (hv : ValidSubtree isRoot (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.alloc sl.nodes lo hi mapFn T) :
    let d0 := (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
    let prog := descendSplitLoopGenProg ((d0, (sl.alloc, cur)), fuel)
    let p := descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      fuel sl cur q
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    (Memory.spec 0).clientResult s prog = (p.1.alloc, p.2) ∧
    memoryCost prog s ≤ 52 * fuel ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    DescendSplitLoopGenPre w ((d0, (sl.alloc, cur)), fuel) s ∧
    BTreeSliceMemRep base c U V w n_max sIdx p.1 s'.mem ∧
    (∃ isR cntL loL hiL,
      cntL < 2 * tMinWhp n_max - 1 ∧
      loL ≤ q ∧ q ≤ hiL ∧ hiL < 2 ^ fpBitsWhp n_max ∧
      ValidSubtree isR (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        p.1.alloc p.1.nodes loL hiL mapFn (.leaf p.2 cntL)) ∧
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
  unfold DescendSplitLoopGenPre
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have ht8 := eight_le_tMinWhp hth
  obtain ⟨ht3, hmeta_cap, hkey_lt, hns_lt⟩ := (btree_slice_param_bounds hth).1
  set d0 := (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
  induction fuel generalizing isRoot cur lo hi sl T s with
  | zero =>
    cases T with
    | branch idx c0 cs => simp [BTreeTree.height] at hht_le
    | leaf idx c0 =>
      dsimp only [BTreeTree.rootIdx] at hrt
      subst idx
      have hc0 : c0 < 2 * tMinWhp n_max - 1 := by rwa [hv.2.1, metaCount_mkNodeMeta] at hnf
      exact ⟨rfl, rfl, by simp [descendSplitLoopGenProg, iterate, memoryCost_pure],
        validProg_pure _, trivial, hrep,
        ⟨isRoot, c0, lo, hi, hc0, hqlo, hqhi, hhi, hv⟩,
        fun _ _ _ _ hr => hr, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | succ f ih =>
    have hsafe1 : DescendSplitStepGenPre w (d0, (sl.alloc, cur)) s :=
      ⟨c, U, V, w, n_max, sl, isRoot, lo, hi, mapFn, T,
        henv, rfl, hsIdx, hrep, rfl, by omega, hrt, hnf, hqlo, hqhi, hhi, hv⟩
    obtain ⟨hcur_lt, _, _, _, _, _, _⟩ := validSubtree_root_bounds hth hhi hv
    rw [hrt] at hcur_lt
    obtain ⟨hcs_n, hres_n, hmc_n, hvp_n⟩ := readBTreeNodeGenProg_spec hth hw hsIdx hcur_lt hrep
      (s := s)
    dsimp only at hcs_n hres_n hmc_n hvp_n
    cases T with
    | leaf idx c0 =>
      rcases hrt.symm with rfl
      have hmeta : (sl.nodes cur).metaWord = mkNodeMeta true c0 := hv.2.1
      have hmod1 : (sl.nodes cur).metaWord % 2 = 1 := by
        simp [hmeta, mkNodeMeta, Nat.add_mul_mod_self_left]
      have hstep : (Memory.spec 0).clientState s
            (descendSplitStepGenProg (d0, (sl.alloc, cur))) = s ∧
          (Memory.spec 0).clientResult s
            (descendSplitStepGenProg (d0, (sl.alloc, cur))) = (sl.alloc, cur) ∧
          memoryCost (descendSplitStepGenProg (d0, (sl.alloc, cur))) s ≤ 52 ∧
          ValidProg w (base + largeSpaceWhp c U V w n_max) s
            (descendSplitStepGenProg (d0, (sl.alloc, cur))) := by
        unfold descendSplitStepGenProg
        simp only [pure_bind]
        refine ⟨?_, ?_, ?_, validProg_bind hvp_n ?_⟩
        · rw [clientState_bind, hcs_n, hres_n, ite_eq_left hmod1]; rfl
        · rw [clientResult_bind, hcs_n, hres_n, ite_eq_left hmod1]; rfl
        · rw [memoryCost_bind', hcs_n, hmc_n, hres_n, ite_eq_left hmod1, memoryCost_pure]; omega
        · rw [hcs_n, hres_n, ite_eq_left hmod1]
          exact validProg_pure _
      have hdesc_eq : descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (f + 1) sl cur q =
          descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            f sl cur q := by
        cases f <;> simp [descendSplitToLeaf, hmeta]
      obtain ⟨hS, hR, hM, hV, hI⟩ := descendSplitLoop_succ (f := f) hsafe1 hstep
      obtain ⟨ih_fr, ih_res, ih_mc, ih_vp, ih_safe, ih_rep, ih_lf, ih_oth, ih_bm, ih_out⟩ :=
        ih (cur := cur) (T := .leaf cur c0) hrep (by omega) rfl hnf (by simp [BTreeTree.height])
          hqlo hqhi hhi hv (s := s)
      dsimp only
      rw [hS, hR, hdesc_eq]
      exact ⟨ih_fr, ih_res, hM ih_mc, hV ih_vp, hI ih_safe, ih_rep, ih_lf, ih_oth, ih_bm, ih_out⟩
    | branch idx c0 cs =>
      rcases hrt.symm with rfl
      obtain ⟨hr_le, hclo_q, hq_chi, _⟩ := branch_child_routing (by omega) hkey_lt hv hhi hqlo hqhi
      obtain ⟨_, hmeta, _, _, hkw_cur, hvw_cur, _, hhi_last, hmono, hnot_cur, _, _, hcs_sub⟩ := hv
      have hc0_lt : c0 < 2 * tMinWhp n_max - 1 := by rwa [hmeta, metaCount_mkNodeMeta] at hnf
      have hmod0 : (sl.nodes cur).metaWord % 2 ≠ 1 := by simp [hmeta, mkNodeMeta]
      have hcnt_div : (sl.nodes cur).metaWord / 2 = c0 := hmeta ▸ metaCount_mkNodeMeta false c0
      set r := swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q (sl.nodes cur).keysWord
      let r_fin : Fin (c0 + 1) := ⟨r, Nat.lt_succ_of_le hr_le⟩
      set childIdx := (cs r_fin).rootIdx
      have hval_r : laneGet (valLaneBitsWhp n_max) (sl.nodes cur).valsWord r = childIdx :=
        (hcs_sub r_fin).1
      have hchi_le : childHi (fpBitsWhp n_max + 2) hi c0 (sl.nodes cur).keysWord r ≤ hi := by
        unfold childHi
        split_ifs with hrc
        · rcases eq_or_lt_of_le (by omega : r ≤ c0 - 1) with heq | hlt
          · exact heq ▸ hhi_last.le
          · exact (hmono r (c0 - 1) hlt (by omega)).le.trans hhi_last.le
        · exact le_rfl
      have hchild_ht : (cs r_fin).height ≤ f := by
        have := Finset.le_sup (f := fun i => (cs i).height) (mem_univ r_fin)
        simp only [BTreeTree.height] at hht_le; omega
      obtain ⟨hchild_lt, hcnt_c_le, _, _, hk_c, hv_c, _⟩ :=
        validSubtree_root_bounds hth (hchi_le.trans_lt hhi) (hcs_sub r_fin).2
      dsimp only [childIdx] at *
      obtain ⟨hndc_st, hndc_res, hndc_mc, hndc_vp⟩ :=
        readBTreeNodeGenProg_spec hth hw hsIdx hchild_lt hrep (s := s)
      dsimp only at hndc_st hndc_res hndc_mc hndc_vp
      have hcntc_div : (sl.nodes childIdx).metaWord / 2 =
          metaCount (sl.nodes childIdx).metaWord := rfl
      have hr_eq_sw : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
          (sl.nodes cur).keysWord = r := rfl
      by_cases hfull_c : metaCount (sl.nodes childIdx).metaWord = 2 * tMinWhp n_max - 1
      · -- Subcase B1: Child `childIdx` is full (`splitFullNode` + 3 node writes + alloc)
        set spPure := splitFullNode (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (sl.nodes childIdx)
        obtain ⟨hlM, hlK, hlV, hsep_lt, hrM, hrK, hrV⟩ := splitFullNode_bits_lt hth hk_c hv_c
        let parentNd' : BTreeNode :=
          ⟨mkNodeMeta false (c0 + 1),
            wordInsertAt (fpBitsWhp n_max + 2) r spPure.sep (sl.nodes cur).keysWord,
            wordInsertAt (valLaneBitsWhp n_max) (r + 1) sl.alloc (sl.nodes cur).valsWord⟩
        have hmP : parentNd'.metaWord < 2 ^ nodeMetaBitsWhp n_max := by
          dsimp only [parentNd', mkNodeMeta]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
        have hkP : parentNd'.keysWord < 2 ^ keysWordBitsWhp n_max := by
          dsimp only [parentNd', keysWordBitsWhp, keyLaneBitsWhp]
          exact (wordInsertAt_lt hr_le hsep_lt hkw_cur).trans_le
            (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
        have hvP : parentNd'.valsWord < 2 ^ valsWordBitsWhp n_max := by
          dsimp only [parentNd', valsWordBitsWhp]
          have hr_v : sl.alloc < 2 ^ valLaneBitsWhp n_max :=
            (by omega : sl.alloc < nSliceWhp n_max).trans hns_lt
          exact (wordInsertAt_lt (Nat.succ_le_succ hr_le) hr_v hvw_cur).trans_le
            (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
        obtain ⟨hfr4, hmc4, hvp4, hrep4, hoth4, hbm4, hout4⟩ :=
          threeNodeWrites_and_alloc_sliceRep (newA := sl.alloc + 1)
            (idx1 := childIdx) (idx2 := sl.alloc) (idx3 := cur)
            (nd1 := spPure.left) (nd2 := spPure.right) (nd3 := parentNd')
            henv hsIdx hrep (by omega) (by omega) (by omega) (by omega)
            (fun v hv_lt => by omega) hlM hlK hlV hrM hrK hrV hmP hkP hvP (s := s)
        set nodes3 := Function.update
          (Function.update (Function.update sl.nodes childIdx spPure.left) sl.alloc spPure.right)
          cur parentNd'
        set sl_mid : BTreeSlice := ⟨sl.alloc + 1, sl.root, nodes3⟩
        set p0 := (mkWhpCoreParams c U V w n_max, base)
        set w4prog :=
          writeBTreeNodeGenProg (((p0, sIdx), childIdx),
            (spPure.left.metaWord, (spPure.left.keysWord, spPure.left.valsWord))) >>= fun _ =>
          writeBTreeNodeGenProg (((p0, sIdx), sl.alloc),
            (spPure.right.metaWord, (spPure.right.keysWord, spPure.right.valsWord))) >>= fun _ =>
          writeBTreeNodeGenProg (((p0, sIdx), cur),
            (parentNd'.metaWord, (parentNd'.keysWord, parentNd'.valsWord))) >>= fun _ =>
          writeSliceAllocGenProg ((p0, sIdx), sl.alloc + 1)
        set s4 := (Memory.spec 0).clientState s w4prog
        set nextCur := if spPure.sep < q then sl.alloc else childIdx
        have hsp_res := clientResult_splitFullNodeGenProg (U := U) (V := V) (w := w)
          hth (sl.nodes childIdx) s
        dsimp only at hsp_res
        have hmP_eq : parentNd'.metaWord = 2 * (c0 + 1) := by
          simp [parentNd', mkNodeMeta]
        have hstep : (Memory.spec 0).clientState s
              (descendSplitStepGenProg (d0, (sl.alloc, cur))) = s4 ∧
            (Memory.spec 0).clientResult s
              (descendSplitStepGenProg (d0, (sl.alloc, cur))) = (sl.alloc + 1, nextCur) ∧
            memoryCost (descendSplitStepGenProg (d0, (sl.alloc, cur))) s ≤ 52 ∧
            ValidProg w (base + largeSpaceWhp c U V w n_max) s
              (descendSplitStepGenProg (d0, (sl.alloc, cur))) := by
          unfold descendSplitStepGenProg splitFullChildOpProg splitFullChildBody
            splitNodeOpProg wordInsertOpProg
          simp only [d0, pure_bind, wp_large_wVal hth, wp_large_wKey hth, wp_large_tMin hth]
          refine ⟨?_, ?_, ?_, validProg_bind hvp_n ?_⟩
          · rw [clientState_bind, hcs_n, hres_n]; simp only [hmod0, ↓reduceIte, hcnt_div]
            rw [clientState_bind, clientState_swarRankGenProg, clientResult_swarRankGenProg hth,
              clientState_bind, clientState_laneGetGenProg, clientResult_laneGetGenProg, hr_eq_sw,
              hval_r, clientState_bind, hndc_st, hndc_res]
            dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]
            rw [clientState_bind, clientState_splitFullNodeGenProg, hsp_res]
            dsimp only
            rw [clientState_bind, clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg,
              clientState_bind, clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg,
              clientState_bind_pure_ite, writeSplitFourOpProg_eq, ← hmP_eq]
            dsimp only [s4, w4prog, parentNd', keyLaneBitsWhp, spPure, childIdx]
          · rw [clientResult_bind, hcs_n, hres_n]; simp only [hmod0, ↓reduceIte, hcnt_div]
            rw [clientResult_bind, clientState_swarRankGenProg, clientResult_swarRankGenProg hth,
              clientResult_bind, clientState_laneGetGenProg, clientResult_laneGetGenProg, hr_eq_sw,
              hval_r, clientResult_bind, hndc_st, hndc_res]
            dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]
            rw [clientResult_bind, clientState_splitFullNodeGenProg, hsp_res]
            dsimp only
            rw [clientResult_bind, clientState_wordInsertAtGenProg,
              clientResult_wordInsertAtGenProg, clientResult_bind, clientState_wordInsertAtGenProg,
              clientResult_wordInsertAtGenProg, clientResult_bind_pure_ite]
            dsimp only [nextCur]
            split_ifs <;> rfl
          · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hcs_n, hmc_n, hres_n]
            simp only [hmod0, ↓reduceIte, hcnt_div]
            rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, clientState_swarRankGenProg,
              memoryCost_swarRankGenProg, clientResult_swarRankGenProg hth,
              ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, clientState_laneGetGenProg,
              memoryCost_laneGetGenProg, clientResult_laneGetGenProg, hr_eq_sw, hval_r,
              ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hndc_st, hndc_mc, hndc_res]
            dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]
            rw [memoryCost_bind, clientState_splitFullNodeGenProg,
              memoryCost_splitFullNodeGenProg, hsp_res]
            dsimp only
            rw [memoryCost_bind, clientState_wordInsertAtGenProg, memoryCost_wordInsertAtGenProg,
              clientResult_wordInsertAtGenProg, memoryCost_bind, clientState_wordInsertAtGenProg,
              memoryCost_wordInsertAtGenProg, clientResult_wordInsertAtGenProg, memoryCost_bind]
            have hite_mc (s_end) : memoryCost
                (if spPure.sep < q then pure (sl.alloc + 1, sl.alloc)
                 else pure (sl.alloc + 1, (cs r_fin).rootIdx)) s_end = 0 := by
              split_ifs <;> rfl
            rw [hite_mc, Nat.add_zero, writeSplitFourOpProg_eq, ← hmP_eq]
            dsimp only [w4prog, parentNd', keyLaneBitsWhp, childIdx] at hmc4 ⊢
            rw [hmc4]
          · rw [hcs_n, hres_n]; simp only [hmod0, ↓reduceIte, hcnt_div]
            refine validProg_bind (validWhpProg_swarRankGenProg _) ?_
            rw [clientState_swarRankGenProg, clientResult_swarRankGenProg hth]
            refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
            rw [clientState_laneGetGenProg, clientResult_laneGetGenProg, hr_eq_sw, hval_r]
            refine validProg_bind hndc_vp ?_
            rw [hndc_st, hndc_res]; dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]
            refine validProg_bind (validWhpProg_splitFullNodeGenProg _) ?_
            rw [clientState_splitFullNodeGenProg, hsp_res]; dsimp only
            refine validProg_bind (validWhpProg_wordInsertAtGenProg _) ?_
            rw [clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg]
            refine validProg_bind (validWhpProg_wordInsertAtGenProg _) ?_
            rw [clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg,
              writeSplitFourOpProg_eq, ← hmP_eq]
            refine validProg_bind hvp4 ?_
            split_ifs <;> exact validProg_pure _
        -- Downward subtree split witness via `splitFullNode_spec`
        have hchild_ne_cur : childIdx ≠ cur := fun heq =>
          hnot_cur r_fin (heq ▸ (cs r_fin).rootIdx_mem_nodeSet)
        have hlr_ne : childIdx ≠ sl.alloc := by omega
        have hcur_ne_r : cur ≠ sl.alloc := by omega
        have hl_nd : nodes3 childIdx = spPure.left := by
          simp only [nodes3, Function.update_of_ne hchild_ne_cur, Function.update_of_ne hlr_ne,
            Function.update_self]
        have hr_nd : nodes3 sl.alloc = spPure.right := by
          simp only [nodes3, Function.update_of_ne hcur_ne_r.symm, Function.update_self]
        have herase : ∀ v ∈ (cs r_fin).nodeSet.erase childIdx,
            nodes3 v = sl.nodes v ∧ v ≠ childIdx ∧ v ≠ sl.alloc := by
          intro v hv_er
          obtain ⟨hv_ne_c, hv_mem⟩ := mem_erase.mp hv_er
          have hv_lt : v < sl.alloc := (((hcs_sub r_fin).2).leafCount_le_card_nodeSet).1 v hv_mem
          have hv_ne_r : v ≠ sl.alloc := by omega
          refine ⟨?_, hv_ne_c, hv_ne_r⟩
          simp only [nodes3,
            Function.update_of_ne (fun heq : v = cur => hnot_cur r_fin (heq ▸ hv_mem)),
            Function.update_of_ne hv_ne_r, Function.update_of_ne hv_ne_c]
        obtain ⟨leftT, rightT, hrtL, hrtR, hcntL_le, hcntR_eq, hhtL, hhtR, _, _,
          _, hclo_sep, hsep_chi, _, hvL, hvR⟩ :=
          splitFullNode_spec (alloc' := sl.alloc + 1) (nodes' := nodes3)
            (leftIdx := childIdx) (rightIdx := sl.alloc) (by omega) (hcs_sub r_fin).2 hfull_c
            (by omega) (by omega) (by omega) hlr_ne hl_nd hr_nd herase
        have hdesc_eq : descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max)
            (tMinWhp n_max) (f + 1) sl cur q =
            descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max)
              (tMinWhp n_max) f sl_mid nextCur q := by
          simp only [descendSplitToLeaf, hmeta, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta,
            Bool.false_eq_true, ↓reduceIte, hr_eq_sw, hval_r, beq_iff_eq]
          rw [ite_eq_left hfull_c]
        obtain ⟨isR, Tn, lon, hin, hrtn, hnfn, hhtn, hlon, hhin, hhin_lt, hvn⟩ :
            ∃ isR Tn lon hin, Tn.rootIdx = nextCur ∧
              metaCount (sl_mid.nodes nextCur).metaWord < 2 * tMinWhp n_max - 1 ∧ Tn.height ≤ f ∧
              lon ≤ q ∧ q ≤ hin ∧ hin < 2 ^ fpBitsWhp n_max ∧
              ValidSubtree isR (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                sl_mid.alloc sl_mid.nodes lon hin mapFn Tn := by
          dsimp only [nextCur]
          split_ifs with hsq
          · dsimp only [spPure, childIdx] at hsq
            exact ⟨_, rightT, _, _, hrtR, hcntR_eq.trans_lt (by omega), hhtR.trans_le hchild_ht,
              by omega, hq_chi, hchi_le.trans_lt hhi, hvR⟩
          · dsimp only [spPure, childIdx] at hsq
            exact ⟨_, leftT, _, _, hrtL, hcntL_le.trans_lt (by omega), hhtL.trans_le hchild_ht,
              hclo_q, by omega, hsep_chi.trans_le (hchi_le.trans hhi.le), hvL⟩
        obtain ⟨hS, hR, hM, hV, hI⟩ :=
          descendSplitLoop_succ (f := f) hsafe1 hstep
        obtain ⟨ih_fr, ih_res, ih_mc, ih_vp, ih_safe, ih_rep, ih_lf, ih_oth, ih_bm, ih_out⟩ :=
          ih hrep4 (by dsimp [sl_mid]; omega) hrtn hnfn hhtn hlon hhin hhin_lt hvn (s := s4)
        rw [hS, hR, hdesc_eq]
        exact ⟨ih_fr.trans hfr4, ih_res, hM ih_mc, hV ih_vp, hI ih_safe, ih_rep, ih_lf,
          fun sIdx' hsIdx' hne sl₂ hr₂ => ih_oth sIdx' hsIdx' hne sl₂ (hoth4 _ hsIdx' hne _ hr₂),
          fun idx hidx hneA => (ih_bm idx hidx hneA).trans (hbm4 idx hidx hneA),
          fun a ha => (ih_out a ha).trans (hout4 a ha)⟩
      · -- Subcase B2: Child `childIdx` is already non-full (`< 2 * tMin - 1`)
        have hnf_c : metaCount (sl.nodes childIdx).metaWord < 2 * tMinWhp n_max - 1 :=
          lt_of_le_of_ne hcnt_c_le hfull_c
        have hstep : (Memory.spec 0).clientState s
              (descendSplitStepGenProg (d0, (sl.alloc, cur))) = s ∧
            (Memory.spec 0).clientResult s
              (descendSplitStepGenProg (d0, (sl.alloc, cur))) = (sl.alloc, childIdx) ∧
            memoryCost (descendSplitStepGenProg (d0, (sl.alloc, cur))) s ≤ 52 ∧
            ValidProg w (base + largeSpaceWhp c U V w n_max) s
              (descendSplitStepGenProg (d0, (sl.alloc, cur))) := by
          unfold descendSplitStepGenProg
          simp only [d0, pure_bind, wp_large_wVal hth, wp_large_tMin hth]
          refine ⟨?_, ?_, ?_, validProg_bind hvp_n ?_⟩
          · rw [clientState_bind, hcs_n, hres_n]; simp only [hmod0, ↓reduceIte, hcnt_div]
            rw [clientState_bind, clientState_swarRankGenProg, clientResult_swarRankGenProg hth,
              clientState_bind, clientState_laneGetGenProg, clientResult_laneGetGenProg, hr_eq_sw,
              hval_r, clientState_bind, hndc_st, hndc_res]
            dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]; rfl
          · rw [clientResult_bind, hcs_n, hres_n]; simp only [hmod0, ↓reduceIte, hcnt_div]
            rw [clientResult_bind, clientState_swarRankGenProg, clientResult_swarRankGenProg hth,
              clientResult_bind, clientState_laneGetGenProg, clientResult_laneGetGenProg, hr_eq_sw,
              hval_r, clientResult_bind, hndc_st, hndc_res]
            dsimp only; rw [hcntc_div]
            simp only [hfull_c, ↓reduceIte, StateTransitionSpec.clientResult_pure]; rfl
          · rw [memoryCost_bind', hcs_n, hmc_n, hres_n]; simp only [hmod0, ↓reduceIte, hcnt_div]
            rw [memoryCost_bind', clientState_swarRankGenProg, memoryCost_swarRankGenProg,
              clientResult_swarRankGenProg hth, memoryCost_bind', clientState_laneGetGenProg,
              memoryCost_laneGetGenProg, clientResult_laneGetGenProg, hr_eq_sw, hval_r,
              memoryCost_bind', hndc_st, hndc_mc, hndc_res]
            dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte, memoryCost_pure]; omega
          · rw [hcs_n, hres_n]; simp only [hmod0, ↓reduceIte, hcnt_div]
            refine validProg_bind (validWhpProg_swarRankGenProg _) ?_
            rw [clientState_swarRankGenProg, clientResult_swarRankGenProg hth]
            refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
            rw [clientState_laneGetGenProg, clientResult_laneGetGenProg, hr_eq_sw, hval_r]
            refine validProg_bind hndc_vp ?_
            rw [hndc_st, hndc_res]; dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]
            exact validProg_pure _
        have hdesc_eq : descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max)
            (tMinWhp n_max) (f + 1) sl cur q =
            descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max)
              (tMinWhp n_max) f sl childIdx q := by
          simp only [descendSplitToLeaf, hmeta, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta,
            Bool.false_eq_true, ↓reduceIte, hr_eq_sw, hval_r, beq_iff_eq]
          rw [ite_eq_right hfull_c]
        obtain ⟨hS, hR, hM, hV, hI⟩ := descendSplitLoop_succ (f := f) hsafe1 hstep
        obtain ⟨ih_fr, ih_res, ih_mc, ih_vp, ih_safe, ih_rep, ih_lf, ih_oth, ih_bm, ih_out⟩ :=
          ih (cur := childIdx) hrep (by omega) rfl hnf_c hchild_ht hclo_q hq_chi
            (hchi_le.trans_lt hhi) (hcs_sub r_fin).2 (s := s)
        rw [hS, hR, hdesc_eq]
        exact ⟨ih_fr, ih_res, hM ih_mc, hV ih_vp, hI ih_safe, ih_rep, ih_lf, ih_oth, ih_bm, ih_out⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
