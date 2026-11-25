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
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Walk
import CslibFrontier.Tactic.Realize

/-!
# Parameter-Free `bufEverPresentGenProg` Subroutine

Certified `O_c(1)` `bufEverPresent` query checking whether `rKey` has ever been inserted into
the epoch character-trie buffer `ep`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufEverPresentGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufEverPresentGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufEverPresentGen`
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

/-- `BufRt` leaf helper for `bufEverPresent`. -/
private def bufEverLeafRtProg (d : BufRt × ℕ) : Memory.Prog ℕ := do
  let rt := d.1
  let idx ← pure (4 * d.2 + 2)
  let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idx)
  if id1 = 0 then pure 0 else pure 1

private theorem realizes_bufEverLeafRt :
    Realizes .exact bufEverLeafRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => BufRtEnvGen w d.1 ∧ d.2 < brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufEverLeafRtProg
  have hrp := realizes_readPackedGen
  realize
  all_goals
    rcases d with ⟨rt, leaf⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hleaf⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hleaf
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)

/-- Parameter-free `bufEverPresent` (`d = (((cp, base), ep), rKey)`), returning `1` or `0`. -/
@[irreducible] def bufEverPresentGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (cp_base_ep, rKey) => do
    let rt ← mkBufRtGenProg cp_base_ep
    let one_v ← pure 1
    let zero_v ← pure 0
    let wres ← bufWalkLoopGenProg ((rt, (one_v, (zero_v, rKey))), brCTab rt)
    let (alive, leafRest) := wres
    if alive = 0 then
      pure 0
    else
      bufEverLeafRtProg (rt, leafRest.1)

theorem bufEverPresentGenProg_spec {c U V w n_max base ep rKey : ℕ}
    {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn) :
    let prog := bufEverPresentGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if bufEverPresent (cTabWhp c) (bCharWhp n_max) tr rKey then 1 else 0) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hw := henv.2.1
  obtain ⟨hnone, hsome⟩ :=
    bufWalkLoop_root_bind_spec (rKey := rKey) 0 bufEverLeafRtProg henv hep hrep hv
  set rt := mkBufRt c U V w n_max base ep
  have hm_seg := (rt_seg_le c U V w n_max base ep hep).meta_le
  have hrep_li : ∀ u < tr.nodeAlloc,
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 2) =
        tr.nodeLeafItem u := by
    have h := hrep.2.2.2.2.2.2.1
    rcases hep with rfl | rfl <;> exact fun u hu => (h u hu).1
  unfold bufEverPresentGenProg bufEverPresent
  simp only [pure_bind]
  rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
  · obtain ⟨hst, hres, hmc, hvp⟩ := hnone hwk
    exact ⟨hst, hres, hmc.trans_le (Nat.le_add_right _ _), hvp⟩
  obtain ⟨hlf_lt, hst, hres, hmc, hvp⟩ := hsome leaf hwk
  unfold bufEverLeafRtProg at hst hres hmc hvp
  simp only [pure_bind] at hst hres hmc hvp
  refine ⟨hst.trans ?_, hres.trans ?_, hmc.trans_le ?_, hvp ?_⟩
  · rw [clientState_bind, clientState_readPackedGen]
    split_ifs <;> rfl
  · rw [clientResult_bind, clientState_readPackedGen,
      clientResult_readPackedGen, show brBase rt = base from rfl,
      show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl,
      hrep_li leaf hlf_lt]
    by_cases hli : tr.nodeLeafItem leaf = 0 <;> simp [hli]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readPackedGen]
    split_ifs <;> (change 2 * cTabWhp c + (2 + 0) ≤ _; omega)
  · have hidx_lt : 4 * leaf + 2 < 6 * maxTrieNodesWhp c n_max := by
      have := hrep.1; omega
    refine validProg_bind (validProg_readPacked hw hidx_lt hm_seg) ?_
    rw [clientState_readPackedGen]
    split_ifs <;> exact validProg_pure _

theorem realizes_bufEverPresentGen :
    Realizes .exact bufEverPresentGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      BufReadGenPre
      (fun _ _ => 0) := by
  unfold bufEverPresentGenProg
  have hmrt := realizes_mkBufRtGen
  have hwl := realizes_bufWalkLoopGen
  have hel := realizes_bufEverLeafRt
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, ep⟩, rKey⟩
    obtain ⟨c, U, V, w₀, n_max, tr, mapFn, henv, rfl, hep, hrep, hv⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
    obtain ⟨hsafe, hw_st, _, _, _, hw_a1⟩ :=
      bufWalkLoop_spec henv hep hrep hv.bounds.1 hv.bounds.2.2.1 (cTabWhp c) 1 0 rKey hv.bounds.1
    have hw1 := hw_a1 rfl
    simp only [hrt_st, hrt_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hsafe
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brCTab, brMaxNodes] at *
       rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
       · rw [hwk] at hw1; omega
       · rw [hwk] at hw1
         obtain ⟨_, hw_eq, hlf_lt⟩ := hw1
         exact (congrArg (fun p => p.2.1) hw_eq) ▸ hlf_lt.trans_le hrep.1)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
