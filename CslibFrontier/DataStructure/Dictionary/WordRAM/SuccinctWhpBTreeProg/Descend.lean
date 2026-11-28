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
# Read-Only Root-to-Leaf B+-Tree Descent (`descendLoopGenProg`)

Implements and certifies the bounded `iterate` read-only root-to-leaf descent subroutine
`descendLoopGenProg` over `Basis.exact`.
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

/-- Precondition for one read-only descent step `d = ((((cp, base), sIdx), q), cur)`. -/
private def DescendStepGenPre (w : ℕ)
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max sl isRoot lo hi mapFn T,
    WhpLargeEnv c U V w₀ n_max w d.1.1.1.2 ∧
    d.1.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    d.1.1.2 < 3 * numBucketsWhp n_max ∧
    BTreeSliceMemRep d.1.1.1.2 c U V w₀ n_max d.1.1.2 sl s.mem ∧
    T.rootIdx = d.2 ∧
    lo ≤ d.1.2 ∧ d.1.2 ≤ hi ∧ hi < 2 ^ fpBitsWhp n_max ∧
    ValidSubtree isRoot (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.alloc sl.nodes lo hi mapFn T

/-- Single step of `descendToLeaf` (`d = ((((cp, base), sIdx), q), cur)`). -/
private def descendStepGenProg
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let nd ← readBTreeNodeGenProg (d.1.1, d.2)
  let isLf ← pure (nd.1 % 2)
  let z1 ← pure 1
  if isLf = z1 then
    pure d.2
  else do
    let cnt ← pure (nd.1 / 2)
    let r ← swarRankGenProg (d.1.1.1.1, ((cnt, d.1.2), nd.2.1))
    laneGetGenProg ((wpWVal d.1.1.1.1, nd.2.2), r)

private theorem memoryCost_descendStepGenProg_pos
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (descendStepGenProg d) s := by
  unfold descendStepGenProg
  rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readBTreeNodeGenProg]
  omega

private theorem realizes_descendStepGen :
    Realizes .exact descendStepGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      DescendStepGenPre
      (fun _ _ => 0) := by
  unfold descendStepGenProg
  realize [realizes_readBTreeNodeGen, realizes_swarRankGen, realizes_laneGetGen]
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, sIdx⟩, q⟩, cur⟩
    dsimp only [DescendStepGenPre] at h
    obtain ⟨c, U, V, w₀, n_max, sl, isRoot, lo, hi, mapFn, T,
      henv, rfl, hsIdx, hrep, hrt, hqlo, hqhi, hhi, hv⟩ := h
    have hth := henv.2.2.2.1
    obtain rfl := henv.2.2.1
    obtain ⟨hcur_lt, hcnt_le, _, hkw_cnt, _, _, hlanes⟩ := validSubtree_root_bounds hth hhi hv
    rw [hrt] at hcur_lt hcnt_le hkw_cnt hlanes
    obtain ⟨hcs_n, hres_n, _, _⟩ := readBTreeNodeGenProg_spec hth henv.2.1 hsIdx hcur_lt hrep
      (s := s)
    dsimp only at hcs_n hres_n
    have ht8 := eight_le_tMinWhp hth
    have hvw_lt := henv.valsWordBits_lt_w
    try simp only [hcs_n, hres_n, wp_large_M hth, wp_large_nSlice hth, wp_large_wVal hth]
  all_goals try first | decide | exact henv.fits_const (by decide)
  · exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · exact hsIdx
  · exact hcur_lt.trans_le hrep.1
  · refine ⟨⟨base, c, U, V, w, n_max, henv, rfl⟩, ?_,
      (wp_large_powFp hth).symm ▸ hqhi.trans_lt hhi, (wp_large_wKey hth).symm ▸ hkw_cnt, ?_⟩
    · rw [wp_large_capLanes hth]
      exact Nat.lt_of_le_of_lt hcnt_le (by omega)
    · rwa [wp_large_wKey hth, wp_large_powFp hth]
  · exact (Nat.le_mul_of_pos_left _ (by omega)).trans_lt hvw_lt
  · rw [clientResult_swarRankGenProg hth]
    obtain ⟨ht3, _, hkey_lt, _⟩ := (btree_slice_param_bounds hth).1
    change swarRank _ _ (metaCount (sl.nodes cur).metaWord) _ _ * _ + _ < _
    have hrank_le : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max)
        (metaCount (sl.nodes cur).metaWord) q (sl.nodes cur).keysWord ≤
        metaCount (sl.nodes cur).metaWord := by
      rw [swarRank_eq_count_lt (by omega) hkey_lt (hqhi.trans_lt hhi) hkw_cnt hlanes]
      exact (card_filter_le _ _).trans_eq (card_range _)
    exact ((Nat.mul_le_mul_right _ (hrank_le.trans (by omega : _ ≤ 2 * tMinWhp n_max))).trans_lt
      hvw_lt).trans Nat.lt_two_pow_self

/-- Bounded `iterate` loop refining `descendToLeaf`
(`d = (((((cp, base), sIdx), q), cur), fuel)`). -/
def descendLoopGenProg :
    ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((d0, cur), fuel) => iterate descendStepGenProg d0 fuel cur

/-- Precondition for `descendLoopGenProg` (`d = (((((cp, base), sIdx), q), cur), fuel)`). -/
def DescendLoopGenPre (w : ℕ) :
    ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | ((d0, cur), fuel), s =>
    iterationSafe descendStepGenProg DescendStepGenPre w d0 fuel cur s

theorem realizes_descendLoopGen :
    Realizes .exact descendLoopGenProg
      (WordEncoding.encode (α := ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      DescendLoopGenPre
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizes_descendStepGen memoryCost_descendStepGenProg_pos

theorem descendLoopGenProg_spec {isRoot : Bool}
    {c U V w n_max base sIdx q cur fuel lo hi : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {T : BTreeTree} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hrt : T.rootIdx = cur) (hqlo : lo ≤ q) (hqhi : q ≤ hi) (hhi : hi < 2 ^ fpBitsWhp n_max)
    (hv : ValidSubtree isRoot (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.alloc sl.nodes lo hi mapFn T) :
    let d0 := (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
    let prog := descendLoopGenProg ((d0, cur), fuel)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl.nodes fuel cur q ∧
    memoryCost prog s = 6 * fuel ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    DescendLoopGenPre w ((d0, cur), fuel) s := by
  unfold DescendLoopGenPre
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  obtain ⟨ht3, _, hkey_lt, _⟩ := (btree_slice_param_bounds hth).1
  set d0 := (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
  induction fuel generalizing isRoot cur lo hi T with
  | zero =>
    exact ⟨rfl, rfl, rfl, validProg_pure cur, trivial⟩
  | succ f ih =>
    have hsafe1 : DescendStepGenPre w (d0, cur) s :=
      ⟨c, U, V, w, n_max, sl, isRoot, lo, hi, mapFn, T,
        henv, rfl, hsIdx, hrep, hrt, hqlo, hqhi, hhi, hv⟩
    obtain ⟨hcur_lt, _, _, _, _, _, _⟩ := validSubtree_root_bounds hth hhi hv
    rw [hrt] at hcur_lt
    obtain ⟨hcs_n, hres_n, hmc_n, hvp_n⟩ := readBTreeNodeGenProg_spec hth hw hsIdx hcur_lt hrep
      (s := s)
    dsimp only at hcs_n hres_n hmc_n hvp_n
    have hstep_st : (Memory.spec 0).clientState s (descendStepGenProg (d0, cur)) = s := by
      unfold descendStepGenProg
      simp only [pure_bind]
      rw [clientState_bind, hcs_n, hres_n]
      split_ifs
      · rfl
      · rw [clientState_bind, clientState_swarRankGenProg, clientState_laneGetGenProg]
    have hstep_mc : memoryCost (descendStepGenProg (d0, cur)) s = 6 := by
      unfold descendStepGenProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
      rw [memoryCost_bind, hcs_n, hmc_n, hres_n]
      split_ifs
      · rfl
      · rw [memoryCost_bind, clientState_swarRankGenProg, memoryCost_swarRankGenProg,
          memoryCost_laneGetGenProg]
    have hstep_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (descendStepGenProg (d0, cur)) := by
      unfold descendStepGenProg
      simp only [pure_bind]
      refine validProg_bind hvp_n ?_
      rw [hcs_n, hres_n]
      split_ifs
      · exact validProg_pure cur
      · exact validProg_bind (validWhpProg_swarRankGenProg _)
          (clientState_swarRankGenProg _ _ ▸ validWhpProg_laneGetGenProg _)
    have hnext : ∃ (isRoot' : Bool) (cur' lo' hi' : ℕ) (T' : BTreeTree),
        (Memory.spec 0).clientResult s (descendStepGenProg (d0, cur)) = cur' ∧
        descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          sl.nodes (f + 1) cur q =
          descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            sl.nodes f cur' q ∧
        T'.rootIdx = cur' ∧ lo' ≤ q ∧ q ≤ hi' ∧ hi' < 2 ^ fpBitsWhp n_max ∧
        ValidSubtree isRoot' (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          sl.alloc sl.nodes lo' hi' mapFn T' := by
      cases T with
      | leaf idx c0 =>
        obtain rfl : cur = idx := hrt.symm
        have hmeta : (sl.nodes cur).metaWord = mkNodeMeta true c0 := hv.2.1
        have hmod1 : (sl.nodes cur).metaWord % 2 = 1 := by
          simp [hmeta, mkNodeMeta, Nat.add_mul_mod_self_left]
        refine ⟨isRoot, cur, lo, hi, .leaf cur c0, ?_, ?_, rfl, hqlo, hqhi, hhi, hv⟩
        · unfold descendStepGenProg
          simp only [d0, pure_bind, clientResult_bind, hcs_n, hres_n, hmod1, ↓reduceIte,
            StateTransitionSpec.clientResult_pure]
        · cases f <;> simp [descendToLeaf, hmeta]
      | branch idx c0 cs =>
        obtain rfl : cur = idx := hrt.symm
        obtain ⟨hr_le, hclo_q, hq_chi, _⟩ :=
          branch_child_routing (by omega) hkey_lt hv hhi hqlo hqhi
        obtain ⟨_, hmeta, _, _, _, _, _, hhi_last, hmono, _, _, _, hcs_sub⟩ := hv
        have hmod0 : (sl.nodes cur).metaWord % 2 ≠ 1 := by simp [hmeta, mkNodeMeta]
        have hcnt_div : (sl.nodes cur).metaWord / 2 = c0 := hmeta ▸ metaCount_mkNodeMeta false c0
        let r_fin : Fin (c0 + 1) := ⟨swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
          (sl.nodes cur).keysWord, Nat.lt_succ_of_le hr_le⟩
        have hval_r : laneGet (valLaneBitsWhp n_max) (sl.nodes cur).valsWord r_fin.val =
            (cs r_fin).rootIdx := (hcs_sub r_fin).1
        have hchi_le : childHi (fpBitsWhp n_max + 2) hi c0 (sl.nodes cur).keysWord r_fin.val ≤
            hi := childHi_le hhi_last.le hmono
        refine ⟨false, (cs r_fin).rootIdx, _, _, cs r_fin, ?_, ?_, rfl,
          hclo_q, hq_chi, hchi_le.trans_lt hhi, (hcs_sub r_fin).2⟩
        · unfold descendStepGenProg
          simpa only [d0, pure_bind, clientResult_bind, hcs_n, hres_n, hmod0, ↓reduceIte,
            hcnt_div, wp_large_wVal hth, clientResult_swarRankGenProg hth,
            clientResult_laneGetGenProg] using hval_r
        · dsimp only [r_fin] at hval_r ⊢
          simp [descendToLeaf, hmeta, hval_r]
    obtain ⟨isRoot', cur', lo', hi', T', hstep_res, hdesc_eq, hrt', hlo', hhi', hhi_lt', hv'⟩ :=
      hnext
    obtain ⟨ih_st, ih_res, ih_mc, ih_vp, ih_safe⟩ := ih hrt' hlo' hhi' hhi_lt' hv'
    dsimp only [descendLoopGenProg, iterate] at ih_st ih_res ih_mc ih_vp ⊢
    refine ⟨?_, ?_, ?_, validProg_bind hstep_vp ?_, hsafe1, ?_⟩
    · rwa [clientState_bind, hstep_st, hstep_res]
    · rwa [clientResult_bind, hstep_st, hstep_res, hdesc_eq]
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_st, hstep_res, hstep_mc, ih_mc]
      omega
    · simpa only [hstep_st, hstep_res] using ih_vp
    · simpa only [hstep_st, hstep_res] using ih_safe

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
