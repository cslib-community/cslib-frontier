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
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Ensure
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.InsertLeaf
import CslibFrontier.Tactic.Realize

/-!
# Parameter-Free `bufInsertGenProg` Subroutine

Certified `O_c(1)` `bufInsert` combining `bufEnsureLoopGenProg` and `bufInsertLeafRtProg` while
preserving `BufEpFrame` and `BufTrieMemRep`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BufInsertGenPre`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufInsertGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufInsertGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufInsertGen`
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

/-- Precondition for `bufInsertGenProg` (`d = ((((cp, base), ep), rKey), (b, loc))`). -/
@[expose] def BufInsertGenPre (w : ℕ) :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((((cp, base), ep), _), (b, loc)), s =>
    ∃ c U V w₀ n_max tr mapFn,
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      (ep = 0 ∨ ep = 1) ∧
      BufTrieMemRep base c U V w₀ n_max ep tr s.mem ∧
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn ∧
      tr.nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      tr.itemAlloc < qEpochWhp n_max ∧
      b < numBucketsWhp n_max ∧
      loc < totalLocalCoordsWhp n_max

/-- Parameter-free `bufInsert` (`d = ((((cp, base), ep), rKey), (b, loc))`). -/
@[irreducible] def bufInsertGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp_base_ep, rKey), b_loc) => do
    let rt ← mkBufRtGenProg cp_base_ep
    let zero_v ← pure 0
    let eres ← bufEnsureLoopGenProg ((rt, (zero_v, rKey)), brCTab rt)
    bufInsertLeafRtProg ((rt, eres.1), b_loc)

/-- Child pointers and leaf items of a valid trie stay below their allocation counters. -/
private theorem validBufTrie_shape {cTab bChar : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn) :
    (∀ v ch, tr.trieChild v ch < tr.nodeAlloc) ∧
      ∀ w' < tr.nodeAlloc, tr.nodeLeafItem w' ≤ tr.itemAlloc :=
  ⟨fun v ch => (eq_or_ne (tr.trieChild v ch) 0).elim (fun h => h ▸ hv.bounds.1)
      (hv.bounds.2.2.1 v ch),
    fun w' hw' => (eq_or_ne (tr.nodeLeafItem w') 0).elim (fun h => h ▸ Nat.zero_le _)
      (hv.bounds.2.2.2 w' hw')⟩

theorem bufInsertGenProg_spec {c U V w n_max base ep rKey b loc : ℕ}
    {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn)
    (hna_cap : tr.nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max)
    (hia_cap : tr.itemAlloc < qEpochWhp n_max)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let prog := bufInsertGenProg ((((mkWhpCoreParams c U V w n_max, base), ep), rKey), (b, loc))
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufInsert (cTabWhp c) (bCharWhp n_max) tr rKey b loc
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 20 * cTabWhp c + 24 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  have hth := henv.2.2.2.1
  obtain ⟨hchild_lt, hli_ia⟩ := validBufTrie_shape hv
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hfr1, hres1, hmc1, hvp1, hrep1, hbfr1, hlf_lt1, hia_eq1, hli_le1⟩ :=
    bufEnsureLoop_spec henv hep (cTabWhp c) tr 0 rKey s hrep hv.bounds.1 hna_cap hv.bounds.1
      hchild_lt hli_ia
  set pPure := bufEnsurePath (bCharWhp n_max) rKey (cTabWhp c) 0 tr 0
  set eprog := bufEnsureLoopGenProg ((rt, (0, rKey)), cTabWhp c)
  set s1 := (Memory.spec 0).clientState s eprog
  obtain ⟨hfr2, hmc2, hvp2, hrep2, hbfr2⟩ :=
    bufInsertLeafRtProg_spec henv hep hrep1 hlf_lt1 (hia_eq1 ▸ hia_cap) hli_le1 hb hloc (s1 := s1)
  have hbr_cTab : brCTab rt = cTabWhp c := rfl
  dsimp only
  unfold bufInsertGenProg
  simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt' =>
        bufEnsureLoopGenProg ((rt', (0, rKey)), brCTab rt') >>= fun er =>
          bufInsertLeafRtProg ((rt', er.1), (b, loc))) =
      (Memory.spec 0).clientState s1 (bufInsertLeafRtProg ((rt, pPure.2), (b, loc))) := by
    rw [clientState_bind, hrt_st, hrt_res, hbr_cTab,
      clientState_bind, hres1]
  rw [hs'_eq]
  refine ⟨hfr2.trans hfr1, ?_, ?_, hrep2, hbfr1.trans hbfr2⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrt_st, hrt_res, hrt_mc, hbr_cTab, hres1]
    change 0 + (memoryCost eprog s + memoryCost (bufInsertLeafRtProg ((rt, pPure.2), (b, loc))) s1)
      ≤ _
    dsimp only [eprog, rt] at hmc1 hmc2 ⊢
    omega
  · refine validProg_bind hrt_vp ?_
    rw [hrt_st, hrt_res, hbr_cTab]
    refine validProg_bind hvp1 ?_
    rw [hres1]
    exact hvp2

theorem realizes_bufInsertGen :
    Realizes .exact bufInsertGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      BufInsertGenPre
      (fun _ _ => 0) := by
  unfold bufInsertGenProg
  have hmrt := realizes_mkBufRtGen
  have hel := realizes_bufEnsureLoopGen
  have hil := realizes_bufInsertLeafRt
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, ep⟩, rKey⟩, ⟨b, loc⟩⟩
    obtain ⟨c, U, V, w₀, n_max, tr, mapFn, henv, rfl, hep, hrep, hv,
      hna_cap, hia_cap, _, _⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    obtain ⟨hchild_lt, hli_ia⟩ := validBufTrie_shape hv
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
    obtain ⟨hsafe, _, hres1, _, _, hrep1, _, hlf_lt1, hia_eq1, hli_le1⟩ :=
      bufEnsureLoop_spec henv hep (cTabWhp c) tr 0 rKey s hrep hv.bounds.1 hna_cap hv.bounds.1
        hchild_lt hli_ia
    simp only [hrt_st, hrt_res] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hsafe
    | exact ⟨c, U, V, w, n_max, base, ep, _, henv, hep, rfl, hrep1,
        hres1 ▸ hlf_lt1, hia_eq1 ▸ hia_cap, hres1 ▸ hli_le1⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
