/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochAdvance
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Large Fast-Epoch Block-Pool Mutation Wrappers and Slot-Removal Programs

This module defines the `BlockPool` mutation wrappers, in-place `BufTrie` relocation lemmas, and
the `fastRemoveAtProg` / `fastPopAnyProg` `Memory.Prog` implementations (together with their
`RealizesBounded .exact` certificates and unindexing / step-level relocation helpers) for the
deamortized worst-case WHP resizable succinct dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.fastRemoveAtProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.fastRemoveAtCost`: `O_c(1)`
  slot-removal program and memory-cost bound across all three tiers, shadow compaction, and
  candidate-salt search.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.fastPopAnyProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.fastPopAnyCost`: `O_c(1)` migration
  pop program and memory-cost bound on `(bp.ownerOf 0).1`.

## Main results

* `fastBpWriteAtProg_spec`, `fastBpAppendProg_spec`, `fastBpPopBktBackProg_spec`,
  `fastBpOwnerOfZeroProg_spec`: frame-aware `BlockPool` mutation and owner-lookup specifications.
* `poolRefines_bpWriteAt`, `poolRefines_bpAppend`, `poolRefines_bpSwapPop`: bijective
  `PoolItemsRefines` preservation across overwrite, append, and swap-pop.
* `bufInsert_active_props`, `fastBufInsertProg_update_spec`: in-place `BufTrie` relocation without
  increasing `nodeAlloc` or `itemAlloc`.
* `bpPairAt_eq_of_fixed_pool`, `pagePair_partner_eq_of_io`: slot-pair and partner-page congruence
  across metadata-only updates.
* `realizesBounded_fastRemoveAt`, `realizesBounded_fastPopAny`: `RealizesBounded .exact`
  certificates for `fastRemoveAtProg` and `fastPopAnyProg`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Frame & Refinement Helpers for `BlockPool` and In-Place `BufTrie` Updates -/

theorem cTab_add_one_mul_le_maxTrieNodes {c N : ℕ} (hth : whpThreshold c ≤ N) :
    1 + cTabWhp c * qEpochWhp N + cTabWhp c ≤ maxTrieNodesWhp c N := by
  have hm : bMinWhp c ≤ Nat.log 2 N := bMinWhp_le_log hth
  have h1 : Nat.log 2 N ≤ Nat.clog 2 (max N 4) :=
    (Nat.log_mono_right (le_max_left N 4)).trans (Nat.log_le_clog 2 _)
  have hbm : bMinWhp c ≤ slabScale N :=
    hm.trans (h1.trans (Nat.le_pow_clog Nat.one_lt_two _))
  have hc_le : cTabWhp c ≤ slabScale N := by
    have hce : cTabWhp c ≤ codeExpWhp c := by
      rw [codeExpWhp_eq]
      unfold cTabWhp
      nlinarith [one_le_cEff c, le_qTabWhp c]
    have hbm_ge : codeExpWhp c ≤ bMinWhp c := by rw [bMinWhp_eq]; omega
    exact hce.trans (hbm_ge.trans hbm)
  have hL_le_Q : slabScale N ≤ qEpochWhp N := by
    change slabScale N ≤ slabScale N ^ 18
    exact Nat.le_self_pow (by decide) _
  have hm_eq : maxTrieNodesWhp c N = cTabWhp c * qEpochWhp N + qEpochWhp N + 2 := by
    unfold maxTrieNodesWhp; ring
  omega

/-- Pure in-place characterization of `bufInsert` when `mapFn rKey = some (b₀, loc₀)`:
leaves `nodeAlloc`, `itemAlloc`, `trieChild`, `nodeParent`, `nodeChar`, `nodeLeafItem` unchanged,
preserves `RawBufTrieBounds`/`RawClearableBounds`, and updates a single unique active slot
`id₀ < tr.itemAlloc` from `some (b₀, loc₀)` to `some (b, loc)`. -/
theorem bufInsert_active_props {cTab bChar rKey b₀ loc₀ b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)}
    (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : rKey < 2 ^ (cTab * bChar))
    (hmk : mapFn rKey = some (b₀, loc₀)) :
    let tr' := bufInsert cTab bChar tr rKey b loc
    tr'.nodeAlloc = tr.nodeAlloc ∧
    tr'.itemAlloc = tr.itemAlloc ∧
    (RawBufTrieBounds tr → RawBufTrieBounds tr') ∧
    (RawClearableBounds tr → RawClearableBounds tr') ∧
    (∀ id, bufCheckSlot tr id = none → bufCheckSlot tr' id = none) ∧
    (∃ id₀ : ℕ, ∀ id',
      (id' ≠ id₀ → bufCheckSlot tr' id' = bufCheckSlot tr id') ∧
      (∀ b' loc', bufCheckSlot tr' id₀ = some (b', loc') →
        b' = b ∧ loc' = loc ∧ bufCheckSlot tr id₀ = some (b₀, loc₀))) := by
  dsimp only
  have hlk : bufLookup cTab bChar tr rKey = some (b₀, loc₀) :=
    (hv.lookup_eq hk).trans hmk
  unfold bufLookup at hlk
  cases hwk : bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => rw [hwk] at hlk; cases hlk
  | some leaf =>
    rw [hwk] at hlk; dsimp only at hlk
    by_cases hzero : tr.nodeLeafItem leaf = 0 ∨ tr.nodeActive leaf = 0
    · rw [ite_eq_left hzero] at hlk; cases hlk
    · rw [ite_eq_right hzero] at hlk
      have hli_nz : tr.nodeLeafItem leaf ≠ 0 := fun h => hzero (Or.inl h)
      have hact_nz : tr.nodeActive leaf ≠ 0 := fun h => hzero (Or.inr h)
      have hpair : (tr.itemBucket (tr.nodeLeafItem leaf - 1),
          tr.itemLoc (tr.nodeLeafItem leaf - 1)) = (b₀, loc₀) := Option.some.inj hlk
      have hbi : tr.itemBucket (tr.nodeLeafItem leaf - 1) = b₀ := congrArg Prod.fst hpair
      have hlo : tr.itemLoc (tr.nodeLeafItem leaf - 1) = loc₀ := congrArg Prod.snd hpair
      set id₀ := tr.nodeLeafItem leaf - 1
      have hpath : bufEnsurePath bChar rKey cTab 0 tr 0 = (tr, leaf) :=
        bufEnsurePath_eq_of_walk_some cTab 0 tr 0 leaf hwk
      have hspec_none : ∀ id, bufCheckSlot tr id = none →
          bufCheckSlot (bufInsert cTab bChar tr rKey b loc) id = none :=
        (hv.insert_spec hk).2.2.2.2.2.2 (by rw [hmk]; exact Option.some_ne_none _) |>.2.2
      have htr'_eq : bufInsert cTab bChar tr rKey b loc =
          { tr with
            nodeActive := Function.update tr.nodeActive leaf 1
            itemBucket := Function.update tr.itemBucket id₀ b
            itemLoc := Function.update tr.itemLoc id₀ loc } := by
        unfold bufInsert; rw [hpath]; dsimp only; rw [ite_eq_right hli_nz]
      refine ⟨by rw [htr'_eq], by rw [htr'_eq], fun hb => by rw [htr'_eq]; exact hb,
        fun hc => by rw [htr'_eq]; exact hc, hspec_none, ⟨id₀, fun id' => ⟨?_, ?_⟩⟩⟩
      · intro hne
        rw [htr'_eq]
        unfold bufCheckSlot; dsimp only
        by_cases hid' : id' < tr.itemAlloc
        · rw [ite_eq_left hid', ite_eq_left hid']
          by_cases hlf : tr.itemLeaf id' = leaf
          · have hneq_li : tr.nodeLeafItem (tr.itemLeaf id') ≠ id' + 1 := by rw [hlf]; omega
            rw [ite_eq_right (fun h => hneq_li h.1), ite_eq_right (fun h => hneq_li h.1)]
          · simp only [Function.update_of_ne hlf, Function.update_of_ne hne]
        · rw [ite_eq_right hid', ite_eq_right hid']
      · intro b' loc' hchk'
        rw [htr'_eq] at hchk'
        unfold bufCheckSlot at hchk'; dsimp only at hchk'
        by_cases hid : id₀ < tr.itemAlloc
        · rw [ite_eq_left hid] at hchk'
          by_cases hc : tr.nodeLeafItem (tr.itemLeaf id₀) = id₀ + 1 ∧
              Function.update tr.nodeActive leaf 1 (tr.itemLeaf id₀) ≠ 0
          · rw [ite_eq_left hc, Function.update_self, Function.update_self] at hchk'
            have hp := Option.some.inj hchk'
            refine ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm, ?_⟩
            unfold bufCheckSlot; rw [ite_eq_left hid]
            by_cases hlf : tr.itemLeaf id₀ = leaf
            · rw [ite_eq_left ⟨hc.1, hlf ▸ hact_nz⟩, hbi, hlo]
            · have hact' : tr.nodeActive (tr.itemLeaf id₀) ≠ 0 := by
                simpa only [Function.update_of_ne hlf] using hc.2
              rw [ite_eq_left ⟨hc.1, hact'⟩, hbi, hlo]
          · rw [ite_eq_right hc] at hchk'; cases hchk'
        · rw [ite_eq_right hid] at hchk'; cases hchk'

/-- In-place `fastBufInsertProg` specification valid even at `itemAlloc = qEpochWhp fl.N` when
updating an already-active key `mapFn rk ≠ none`. -/
theorem fastBufInsertProg_update_spec {fl : FastEpochLayout} {w role rk b loc : ℕ}
    {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hrole : role < 2)
    (hv : ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N) (extractBufTrie (fl.trieL role) s.mem) mapFn)
    (hraw : RawBufTrieBounds (extractBufTrie (fl.trieL role) s.mem))
    (hna : (extractBufTrie (fl.trieL role) s.mem).nodeAlloc + cTabWhp fl.c ≤
      maxTrieNodesWhp fl.c fl.N)
    (hia : (extractBufTrie (fl.trieL role) s.mem).itemAlloc ≤ qEpochWhp fl.N)
    (hact : mapFn rk ≠ none)
    (hk : rk < 2 ^ (cTabWhp fl.c * bCharWhp fl.N))
    (hb : b < 2 ^ globalPtrBits fl.N) (hloc : loc < 2 ^ globalPtrBits fl.N) :
    let s' := (Memory.spec 0).clientState s (fastBufInsertProg ((fl.pBase, role), (rk, (b, loc))))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBufInsertProg ((fl.pBase, role), (rk, (b, loc)))) s ≤ 24 * cTabWhp fl.c + 42 ∧
    extractBufTrie (fl.trieL role) s'.mem =
      bufInsert (cTabWhp fl.c) (bCharWhp fl.N) (extractBufTrie (fl.trieL role) s.mem) rk b loc ∧
    ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N) (extractBufTrie (fl.trieL role) s'.mem)
      (Function.update mapFn rk (some (b, loc))) ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    extractBufTrie (fl.trieL (1 - role)) s'.mem = extractBufTrie (fl.trieL (1 - role)) s.mem ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  cases hr.1.w_eq
  obtain ⟨hfr, hr', hc, _⟩ := fastBufInsertProg_ready (role := role) (rk := rk) (b := b)
    (loc := loc) hr
  have hst : (Memory.spec 0).clientState s
      (fastBufInsertProg ((fl.pBase, role), (rk, (b, loc)))) =
      (Memory.spec 0).clientState s
        (bufInsertBoundedProg ((fl.trieL role).toCtx, (rk, (b, loc)))) := by
    unfold fastBufInsertProg; dsimp only
    rw [ite_eq_left hrole, StateTransitionSpec.clientState_bind,
      clientState_loadTrieCtxProg, clientResult_loadTrieCtxProg hr.2.1 hrole]
  obtain ⟨_, _, hext, hv', hout⟩ :=
    bufInsertBoundedProg_update_spec (hr.1.trie_valid hrole) hv hraw hna hia hact hk hb hloc
  have hct : (fl.trieL role).cTab = cTabWhp fl.c := rfl
  have hbc : (fl.trieL role).bChar = bCharWhp fl.N := rfl
  rw [hct, hbc] at hext hv'
  rw [← hst] at hext hv' hout
  obtain ⟨hbp_eq, hfm_eq, hm2_eq, hm0_eq, hbt_eq, htr_o, hout_io, hout_fast⟩ :=
    fastTrieMod_frame hr.1 hrole hout
  exact ⟨hfr, hr', hc, hext, hv', hbp_eq, hfm_eq, hm2_eq, hm0_eq, hbt_eq, htr_o,
    hout_io, hout_fast⟩

/-- Frame theorem: any mutation leaving `¬fl.bpL.OwnsAddr` and bucket meta lanes `5 ≤ sl < 16`
unchanged preserves `FastEpochMeta`, all `BTreeSlice`s, both `BufTrie`s, `metaBase`,
`metaBase + 2`, both hash seed representations, and outside `¬fl.OwnsFastAddr`. -/
theorem fastBpMod_frame {fl : FastEpochLayout} {w fr : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hv : fl.Valid w fr)
    (hout : ∀ addr, ¬fl.bpL.OwnsAddr addr → m₂ addr = m₁ addr)
    (hlanes : ∀ b' < fl.mp.M, ∀ sl', 5 ≤ sl' → sl' < 16 →
      readPacked (fl.mp.metaBase + fl.mp.offBktMeta) fl.mp.ptrB fl.mp.w m₂ (16 * b' + sl') =
        readPacked (fl.mp.metaBase + fl.mp.offBktMeta) fl.mp.ptrB fl.mp.w m₁ (16 * b' + sl')) :
    extractFastMeta fl m₂ = extractFastMeta fl m₁ ∧
    m₂ fl.metaBase = m₁ fl.metaBase ∧
    m₂ (fl.metaBase + 2) = m₁ (fl.metaBase + 2) ∧
    (∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r m₂ = extractBTreeSlice fl.btL b r m₁) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) m₂ = extractBufTrie (fl.trieL r) m₁) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → m₂ addr = m₁ addr) := by
  have hmv := hv.mp_valid
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := by
    have := hmv.offBktMeta_ge; dsimp [FastEpochLayout.mp, epochBpMetaLayout] at this; exact this
  have hdisj_low : ∀ off, off < 18 → off ≠ 1 → ¬(10 ≤ off ∧ off < 17) →
      ¬fl.bpL.OwnsAddr (fl.metaBase + off) := fun off hoff hne1 h10 hbp => by
    rcases hbp with hma | hia
    · rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with
          (h1 | ⟨hlo, hhi⟩) | ⟨hlo, hhi⟩
      · change fl.metaBase + off = fl.metaBase + 1 at h1; omega
      · dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hlo hhi; omega
      · change fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ fl.metaBase + off at hlo
        omega
    · exact hv.disj_fast_io (fl.metaBase + off) (Or.inl ⟨by omega, by omega⟩) hia
  have hdisj_hi : ∀ addr, fl.metaBase + offBTreeMeta fl.c fl.w fl.N ≤ addr →
      addr < fl.metaBase + offPageDir fl.c fl.w fl.N → ¬fl.bpL.OwnsAddr addr := by
    intro addr hlo hhi hbp
    rcases hbp with hma | hia
    · rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with
          (h1 | ⟨_, h2⟩) | ⟨_, h2⟩
      · have : offBTreeMeta fl.c fl.w fl.N ≥ 32 := by
          have : offBktMeta fl.c fl.w fl.N ≤ offBTreeMeta fl.c fl.w fl.N := by
            unfold offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir; omega
          omega
        dsimp [FastEpochLayout.mp, epochBpMetaLayout] at h1; omega
      · have : offBTreeMeta fl.c fl.w fl.N ≥ 32 := by
          have : offBktMeta fl.c fl.w fl.N ≤ offBTreeMeta fl.c fl.w fl.N := by
            unfold offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir; omega
          omega
        dsimp [FastEpochLayout.mp, epochBpMetaLayout] at h2; omega
      · have : offTailOwner fl.c fl.w fl.N + packedWords (16 * maxTailWhp fl.N)
            (globalPtrBits fl.N) fl.w = offBTreeMeta fl.c fl.w fl.N := rfl
        dsimp [FastEpochLayout.mp, epochBpMetaLayout] at h2; omega
    · have : offBktMeta fl.c fl.w fl.N ≤ offBTreeMeta fl.c fl.w fl.N := by
        unfold offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir; omega
      exact hv.disj_fast_io addr (Or.inr ⟨by omega, hhi⟩) hia
  have hm_eq : ∀ off, off < 18 → off ≠ 1 → ¬(10 ≤ off ∧ off < 17) →
      m₂ (fl.metaBase + off) = m₁ (fl.metaBase + off) := fun off h1 h2 h3 =>
    hout _ (hdisj_low off h1 h2 h3)
  refine ⟨?_, ?_, hm_eq 2 (by decide) (by decide) (by decide), ?_, ?_, ?_⟩
  · unfold extractFastMeta
    simp only [hm_eq 3 (by decide) (by decide) (by decide),
      hm_eq 4 (by decide) (by decide) (by decide),
      hm_eq 5 (by decide) (by decide) (by decide),
      hm_eq 6 (by decide) (by decide) (by decide),
      hm_eq 7 (by decide) (by decide) (by decide),
      hm_eq 8 (by decide) (by decide) (by decide),
      hm_eq 9 (by decide) (by decide) (by decide),
      hm_eq 17 (by decide) (by decide) (by decide)]
    congr 1
    all_goals (
      funext b
      split_ifs with hb
      · exact hlanes b hb _ (by omega) (by omega)
      · rfl)
  · simpa only [Nat.add_zero] using hm_eq 0 (by decide) (by decide) (by decide)
  · intro b hb r hr
    have hbv := hv.bt_valid
    have hd1 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hd2 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hnd : fl.metaBase + offBTreeVals fl.c fl.w fl.N +
        packedWords (totalBTreeNodesWhp fl.N) (valsWordBitsWhp fl.N) fl.w ≤
        fl.metaBase + offPageDir fl.c fl.w fl.N := by
      have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) (role := 0) (by decide)
      have h0 : offBTreeVals fl.c fl.w fl.N +
          packedWords (totalBTreeNodesWhp fl.N) (valsWordBitsWhp fl.N) fl.w ≤
          offTrieChild fl.c fl.w fl.N 0 := by
        dsimp only [offTrieChild]; omega
      omega
    have hlo_m : ∀ p < totalBTreeNodesWhp fl.N,
        readPacked (fl.metaBase + offBTreeMeta fl.c fl.w fl.N) (nodeMetaBitsWhp fl.N) fl.w m₂ p =
          readPacked (fl.metaBase + offBTreeMeta fl.c fl.w fl.N) (nodeMetaBitsWhp fl.N) fl.w
            m₁ p := fun p hp => by
      refine readPacked_congr hw_pos (fun addr ⟨h1, h2⟩ => ?_) hp
      apply hout; apply hdisj_hi addr (by omega)
      have : offBTreeMeta fl.c fl.w fl.N +
          packedWords (totalBTreeNodesWhp fl.N) (nodeMetaBitsWhp fl.N) fl.w ≤
          offBTreeKeys fl.c fl.w fl.N := by
        dsimp [FastEpochLayout.btL, epochBTreeLayout, BTreeEpochLayout.totalNodes] at hd1
        have : 3 * numBucketsWhp fl.N * nSliceWhp fl.N = totalBTreeNodesWhp fl.N := rfl
        rw [this] at hd1; omega
      have hkv : offBTreeKeys fl.c fl.w fl.N ≤ offBTreeVals fl.c fl.w fl.N := Nat.le_add_right _ _
      omega
    have hlo_k : ∀ p < totalBTreeNodesWhp fl.N,
        readPacked (fl.metaBase + offBTreeKeys fl.c fl.w fl.N) (keysWordBitsWhp fl.N) fl.w m₂ p =
          readPacked (fl.metaBase + offBTreeKeys fl.c fl.w fl.N) (keysWordBitsWhp fl.N) fl.w
            m₁ p := fun p hp => by
      refine readPacked_congr hw_pos (fun addr ⟨h1, h2⟩ => ?_) hp
      apply hout; apply hdisj_hi addr
      · have : offBTreeMeta fl.c fl.w fl.N ≤ offBTreeKeys fl.c fl.w fl.N := Nat.le_add_right _ _
        omega
      · dsimp [FastEpochLayout.btL, epochBTreeLayout, BTreeEpochLayout.totalNodes] at hd2
        have : 3 * numBucketsWhp fl.N * nSliceWhp fl.N = totalBTreeNodesWhp fl.N := rfl
        rw [this] at hd2; omega
    have hlo_v : ∀ p < totalBTreeNodesWhp fl.N,
        readPacked (fl.metaBase + offBTreeVals fl.c fl.w fl.N) (valsWordBitsWhp fl.N) fl.w m₂ p =
          readPacked (fl.metaBase + offBTreeVals fl.c fl.w fl.N) (valsWordBitsWhp fl.N) fl.w
            m₁ p := fun p hp => by
      refine readPacked_congr hw_pos (fun addr ⟨h1, h2⟩ => ?_) hp
      apply hout; apply hdisj_hi addr
      · have hmk : offBTreeMeta fl.c fl.w fl.N ≤ offBTreeKeys fl.c fl.w fl.N := Nat.le_add_right _ _
        have hkv : offBTreeKeys fl.c fl.w fl.N ≤ offBTreeVals fl.c fl.w fl.N := Nat.le_add_right _ _
        omega
      · exact lt_of_lt_of_le h2 hnd
    have ha := hlanes b hb (6 + 2 * r) (by omega) (by omega)
    have hrt := hlanes b hb (7 + 2 * r) (by omega) (by omega)
    unfold extractBTreeSlice
    dsimp only [FastEpochLayout.btL, epochBTreeLayout]
    have h6 : 16 * b + 6 + 2 * r = 16 * b + (6 + 2 * r) := by omega
    have h7 : 16 * b + 7 + 2 * r = 16 * b + (7 + 2 * r) := by omega
    rw [h6, h7]
    dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at ha hrt
    rw [ha, hrt]
    congr 1; funext u
    by_cases hu : u < nSliceWhp fl.N
    · simp only [hu, ↓reduceIte]
      have hidx_lt : (3 * b + r) * nSliceWhp fl.N + u < totalBTreeNodesWhp fl.N := by
        have htot : totalBTreeNodesWhp fl.N = 3 * numBucketsWhp fl.N * nSliceWhp fl.N := rfl
        rw [htot]
        have h1 : 3 * b + r < 3 * numBucketsWhp fl.N := by omega
        calc (3 * b + r) * nSliceWhp fl.N + u
            < (3 * b + r) * nSliceWhp fl.N + nSliceWhp fl.N := Nat.add_lt_add_left hu _
          _ = (3 * b + r + 1) * nSliceWhp fl.N := by ring
          _ ≤ 3 * numBucketsWhp fl.N * nSliceWhp fl.N := Nat.mul_le_mul_right _ h1
      rw [hlo_m _ hidx_lt, hlo_k _ hidx_lt, hlo_v _ hidx_lt]
    · simp only [hu, ↓reduceIte]
  · intro r hr
    apply extractBufTrie_congr hw_pos
    intro addr hown
    have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) hr
    have hlo_bt : offBTreeMeta fl.c fl.w fl.N ≤ offTrieChild fl.c fl.w fl.N 0 := by
      unfold offTrieChild offBTreeVals offBTreeKeys; omega
    dsimp only [FastEpochLayout.trieL, epochTrieLayout, TrieLayout.OwnsAddr] at hown
    apply hout; apply hdisj_hi addr
    · rcases hown with h | h | h <;> omega
    · rcases hown with h | h | h <;> omega
  · exact fun addr ha => hout addr fun hbp => ha (fl.owns_of_bp hv hbp)

/-- Exact specification of `fastBpOwnerOfZeroProg` when `0 < bp.nSide`. -/
theorem fastBpOwnerOfZeroProg_spec {fl : FastEpochLayout} {w : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s)
    (hcv : (extractBlockPool fl.mp s.mem).CoreValid)
    (hpos : 0 < (extractBlockPool fl.mp s.mem).nSide) :
    let r := (Memory.spec 0).clientResult s (fastBpOwnerOfZeroProg fl.pBase)
    memoryCost (fastBpOwnerOfZeroProg fl.pBase) s ≤ 40 ∧
    r = (extractBlockPool fl.mp s.mem).ownerOf 0 ∧
    r.1 < numBucketsWhp fl.N ∧
    r.2 < (extractBlockPool fl.mp s.mem).bktCount r.1 := by
  dsimp only
  unfold fastBpOwnerOfZeroProg
  rw [prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_loadBpMetaCtxProg, clientResult_loadBpMetaCtxProg hr.2.1,
    memoryCost_loadBpMetaCtxProg]
  have hres := bpOwnerOfProg_spec hcv hpos
  have hc := (bpOwnerOfProg_frame fl.mp 0).frame.cost_le s
  obtain ⟨hb, hl, _⟩ := hcv.ownerOf_bounds_and_toPhys hpos
  exact ⟨by omega, hres, by rw [hres]; exact hb, by rw [hres]; exact hl⟩

/-- Full `FastEpoch` specification of `fastBpWriteAtProg`. -/
theorem fastBpWriteAtProg_spec {fl : FastEpochLayout} {w slack b loc q v : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hbp : fl.bpL.StateInv slack s.mem)
    (hb : b < numBucketsWhp fl.N)
    (hloc : loc < (extractBlockPool fl.mp s.mem).bktCount b)
    (hq : q < 2 ^ fl.io.pgL.qBits) (hval : v < 2 ^ fl.io.pgL.vBits) :
    let s' := (Memory.spec 0).clientState s (fastBpWriteAtProg ((fl.pBase, (b, loc)), (q, v)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBpWriteAtProg ((fl.pBase, (b, loc)), (q, v))) s ≤ 75 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    fl.bpL.StateInv slack s'.mem ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp s.mem).bktCount b',
      bpPairAt fl.bpL s'.mem b' loc' =
        if b' = b ∧ loc' = loc then (q, v) else bpPairAt fl.bpL s.mem b' loc') ∧
    (fl.io.usePaged ≠ 0 →
      extractPageUnperm fl.io.pgL s'.mem = extractPageUnperm fl.io.pgL s.mem ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  obtain ⟨hfr, hr', hc, hout⟩ := fastBpWriteAtProg_ready (b := b) (loc := loc) (q := q) (v := v) hr
  have hst : (Memory.spec 0).clientState s (fastBpWriteAtProg ((fl.pBase, (b, loc)), (q, v))) =
      (Memory.spec 0).clientState s (bpWriteAtProg fl.bpL b loc q v) := by
    unfold fastBpWriteAtProg bpWriteAtProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hr.2.1]
  have hwf : fl.bpL.Valid fl.bpL.mp.w s.frontier := by
    have : w = fl.bpL.mp.w := hr.1.w_eq
    exact this ▸ hr.1.bp_valid
  obtain ⟨_, hex, hinv', hpair, hpart⟩ :=
    bpWriteAtProg_spec hwf hbp hb hloc hq hval
  have hlanes : ∀ b' < fl.mp.M, ∀ sl', 5 ≤ sl' → sl' < 16 →
      readPacked (fl.mp.metaBase + fl.mp.offBktMeta) fl.mp.ptrB fl.mp.w
        ((Memory.spec 0).clientState s (fastBpWriteAtProg ((fl.pBase, (b, loc)), (q, v)))).mem
        (16 * b' + sl') =
      readPacked (fl.mp.metaBase + fl.mp.offBktMeta) fl.mp.ptrB fl.mp.w s.mem (16 * b' + sl') := by
    intro b' hb' sl' h5 h16
    rw [hst]
    exact (bpWriteAtProg_frame hwf b loc q v).bkt_other s b' sl' hb' h5 h16
  rw [← hst] at hex hinv' hpair hpart
  obtain ⟨hfm, hm0, hm2, hbt, htr, hof⟩ := fastBpMod_frame hr.1 hout hlanes
  exact ⟨hfr, hr', hc, hex, hinv', hfm, hm0, hm2, hbt, htr, hof, hpair, hpart⟩

/-- Full `FastEpoch` specification of `fastBpAppendProg`. -/
theorem fastBpAppendProg_spec {fl : FastEpochLayout} {w b q v : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hbp : fl.bpL.StateInv 0 s.mem)
    (hb : b < numBucketsWhp fl.N)
    (hn_lt : (extractBlockPool fl.mp s.mem).nSide < fl.N)
    (hcnt_lt : (extractBlockPool fl.mp s.mem).bktCount b < capMaxWhp fl.N)
    (hcap_io : fl.io.AppendCap (extractBlockPool fl.mp s.mem).nSide s.mem)
    (hq : q < 2 ^ fl.io.pgL.qBits) (hval : v < 2 ^ fl.io.pgL.vBits) :
    let bp₀ := extractBlockPool fl.mp s.mem
    let s' := (Memory.spec 0).clientState s (fastBpAppendProg ((fl.pBase, b), (q, v)))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBpAppendProg ((fl.pBase, b), (q, v))) s ≤ 5327 ∧
    fl.bpL.StateInv slack' s'.mem ∧
    (extractBlockPool fl.mp s'.mem).nSide = bp₀.nSide + 1 ∧
    (extractBlockPool fl.mp s'.mem).bktCount b = bp₀.bktCount b + 1 ∧
    (∀ b' ≠ b, (extractBlockPool fl.mp s'.mem).bktCount b' = bp₀.bktCount b') ∧
    bpPairAt fl.bpL s'.mem b (bp₀.bktCount b) = (q, v) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ loc' < bp₀.bktCount b',
      bpPairAt fl.bpL s'.mem b' loc' = bpPairAt fl.bpL s.mem b' loc') ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (extractPagePair fl.io.pgL s.mem).totalItems + 1 ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  obtain ⟨hfr, hr', hc, hlanes, hout⟩ := fastBpAppendProg_ready (b := b) (q := q) (v := v) hr
  have hst : (Memory.spec 0).clientState s (fastBpAppendProg ((fl.pBase, b), (q, v))) =
      (Memory.spec 0).clientState s (bpAppendProg fl.bpL b q v) := by
    unfold fastBpAppendProg bpAppendProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hr.2.1]
  have hcap_eq : fl.mp.maxSlabs * fl.mp.K = capMaxWhp fl.N := by
    change maxSlabsPerBktWhp fl.N * slabSizeWhp fl.N = capMaxWhp fl.N
    unfold maxSlabsPerBktWhp slabSizeWhp capMaxWhp; ring
  have hwf : fl.bpL.Valid fl.bpL.mp.w s.frontier := by
    have : w = fl.bpL.mp.w := hr.1.w_eq
    exact this ▸ hr.1.bp_valid
  obtain ⟨_, hbp', hns', hbc_b, hbc_ne, hnew, hold, hpart⟩ :=
    bpAppendProg_spec hwf hbp hb hn_lt (hcap_eq.symm ▸ hcnt_lt)
      hcap_io hq hval
  change _ at hbp' hns' hbc_b hbc_ne hnew hold hpart
  have hst' : (Memory.spec 0).clientState s (bpAppendProg fl.bpL b q v) =
      (Memory.spec 0).clientState s (fastBpAppendProg ((fl.pBase, b), (q, v))) := hst.symm
  rw [hst'] at hbp' hns' hbc_b hbc_ne hnew hold hpart
  obtain ⟨hfm, hm0, hm2, hbt, htr, hof⟩ := fastBpMod_frame hr.1 hout hlanes
  exact ⟨hfr, hr', hc, hbp', hns', hbc_b, hbc_ne, hnew, hold, hfm, hm0, hm2, hbt, htr, hof, hpart⟩

/-- Full `FastEpoch` specification of `fastBpPopBktBackProg`. -/
theorem fastBpPopBktBackProg_spec {fl : FastEpochLayout} {w b : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hbp : fl.bpL.StateInv 0 s.mem)
    (hb : b < numBucketsWhp fl.N)
    (hcnt : 0 < (extractBlockPool fl.mp s.mem).bktCount b) :
    let bp₀ := extractBlockPool fl.mp s.mem
    let s' := (Memory.spec 0).clientState s (fastBpPopBktBackProg (fl.pBase, b))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBpPopBktBackProg (fl.pBase, b)) s ≤ 8527 ∧
    fl.bpL.StateInv slack' s'.mem ∧
    (extractBlockPool fl.mp s'.mem).nSide = bp₀.nSide - 1 ∧
    (extractBlockPool fl.mp s'.mem).bktCount b = bp₀.bktCount b - 1 ∧
    (∀ b' ≠ b, (extractBlockPool fl.mp s'.mem).bktCount b' = bp₀.bktCount b') ∧
    (∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp s'.mem).bktCount b',
      bpPairAt fl.bpL s'.mem b' loc' = bpPairAt fl.bpL s.mem b' loc') ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (extractPagePair fl.io.pgL s.mem).totalItems - 1 ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  obtain ⟨hfr, hr', hc, hlanes, hout⟩ := fastBpPopBktBackProg_ready (b := b) hr
  have hst : (Memory.spec 0).clientState s (fastBpPopBktBackProg (fl.pBase, b)) =
      (Memory.spec 0).clientState s (bpPopBktBackProg fl.bpL b) := by
    unfold fastBpPopBktBackProg bpPopBktBackProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hr.2.1]
  have hwf : fl.bpL.Valid fl.bpL.mp.w s.frontier := by
    have : w = fl.bpL.mp.w := hr.1.w_eq
    exact this ▸ hr.1.bp_valid
  obtain ⟨_, hbp', hns', hbc_b, hbc_ne, hold, hpart⟩ :=
    bpPopBktBackProg_spec hwf hbp hb hcnt
  have hst' : (Memory.spec 0).clientState s (bpPopBktBackProg fl.bpL b) =
      (Memory.spec 0).clientState s (fastBpPopBktBackProg (fl.pBase, b)) := hst.symm
  rw [hst'] at hbp' hns' hbc_b hbc_ne hold hpart
  obtain ⟨hfm, hm0, hm2, hbt, htr, hof⟩ := fastBpMod_frame hr.1 hout hlanes
  exact ⟨hfr, hr', hc, hbp', hns', hbc_b, hbc_ne, hold, hfm, hm0, hm2, hbt, htr, hof, hpart⟩

/-- Overwriting `(b, loc)` in `BlockPool` with `(keyQuotient u, v.val)` refines
`Function.update s_abs u (some v)`. -/
theorem poolRefines_bpWriteAt {fl : FastEpochLayout} {θ_bkt : BktSeed fl.c fl.U fl.N}
    {m₁ m₂ : ℕ → ℕ} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {b loc : ℕ} {u : Fin fl.U} (v : Fin fl.V)
    (hbp_eq : extractBlockPool fl.mp m₂ = extractBlockPool fl.mp m₁)
    (hcv : (extractBlockPool fl.mp m₁).CoreValid)
    (href : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
      (extractBlockPool fl.mp m₁).nSide
      (fun p => ((extractBlockPool fl.mp m₁).ownerOf p).1) (slotIoPairAt fl.io m₁) s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hloc : loc < (extractBlockPool fl.mp m₁).bktCount b)
    (hb_u : b = epochBucket fl.c fl.U fl.N θ_bkt u)
    (hq_u : (bpPairAt fl.bpL m₁ b loc).1 = keyQuotient (bWhp fl.N) u.val)
    (hpair : ∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp m₁).bktCount b',
      bpPairAt fl.bpL m₂ b' loc' =
        if b' = b ∧ loc' = loc then (keyQuotient (bWhp fl.N) u.val, v.val)
        else bpPairAt fl.bpL m₁ b' loc') :
    PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
      (extractBlockPool fl.mp m₂).nSide
      (fun p => ((extractBlockPool fl.mp m₂).ownerOf p).1) (slotIoPairAt fl.io m₂)
      (Function.update s_abs u (some v)) := by
  rw [hbp_eq]
  set bp := extractBlockPool fl.mp m₁
  set p := bp.toPhys b loc
  have hp_lt : p < bp.nSide := hcv.toPhys_lt hb hloc
  have how_p : (bp.ownerOf p).1 = b := by rw [hcv.ownerOf_toPhys hb hloc]
  have hpr_conv : ∀ q < bp.nSide,
      slotIoPairAt fl.io m₂ q =
        bpPairAt fl.bpL m₂ (bp.ownerOf q).1 (bp.ownerOf q).2 := fun q hq => by
    obtain ⟨_, _, htp⟩ := hcv.ownerOf_bounds_and_toPhys hq
    unfold bpPairAt; dsimp only [FastEpochLayout.bpL]; rw [hbp_eq, htp]
  have hpr1_conv : ∀ q < bp.nSide,
      slotIoPairAt fl.io m₁ q =
        bpPairAt fl.bpL m₁ (bp.ownerOf q).1 (bp.ownerOf q).2 := fun q hq => by
    obtain ⟨_, _, htp⟩ := hcv.ownerOf_bounds_and_toPhys hq
    unfold bpPairAt; dsimp only [FastEpochLayout.bpL]; rw [htp]
  refine href.update_at v hp_lt (how_p.trans hb_u) ?_ ?_ ?_
  · rw [hpr1_conv p hp_lt, hcv.ownerOf_toPhys hb hloc]; exact hq_u
  · rw [hpr_conv p hp_lt, hcv.ownerOf_toPhys hb hloc, hpair b hb loc hloc,
      ite_eq_left ⟨rfl, rfl⟩]
  · intro q hq hne
    obtain ⟨hbq, hlq, htpq⟩ := hcv.ownerOf_bounds_and_toPhys hq
    have hnot : ¬((bp.ownerOf q).1 = b ∧ (bp.ownerOf q).2 = loc) := by
      rintro ⟨h1, h2⟩; apply hne
      rw [← htpq, h1, h2]
    rw [hpr_conv q hq, hpair _ hbq _ hlq, ite_eq_right hnot, ← hpr1_conv q hq]

/-- Appending an absent key `(u, v)` at `(b, bp₁.bktCount b)` via `bpAppendProg` refines
`Function.update s_abs u (some v)`. -/
theorem poolRefines_bpAppend {fl : FastEpochLayout} {θ_bkt : BktSeed fl.c fl.U fl.N}
    {m₁ m₂ : ℕ → ℕ} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {b : ℕ} {u : Fin fl.U} (v : Fin fl.V)
    (hcv₁ : (extractBlockPool fl.mp m₁).CoreValid)
    (hcv₂ : (extractBlockPool fl.mp m₂).CoreValid)
    (href : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
      (extractBlockPool fl.mp m₁).nSide
      (fun p => ((extractBlockPool fl.mp m₁).ownerOf p).1) (slotIoPairAt fl.io m₁) s_abs)
    (habs : s_abs u = none)
    (hb : b < numBucketsWhp fl.N)
    (hb_u : b = epochBucket fl.c fl.U fl.N θ_bkt u)
    (hbc_b : (extractBlockPool fl.mp m₂).bktCount b = (extractBlockPool fl.mp m₁).bktCount b + 1)
    (hbc_ne : ∀ b' ≠ b, (extractBlockPool fl.mp m₂).bktCount b' =
      (extractBlockPool fl.mp m₁).bktCount b')
    (hnew : bpPairAt fl.bpL m₂ b ((extractBlockPool fl.mp m₁).bktCount b) =
      (keyQuotient (bWhp fl.N) u.val, v.val))
    (hold : ∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp m₁).bktCount b',
      bpPairAt fl.bpL m₂ b' loc' = bpPairAt fl.bpL m₁ b' loc') :
    PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
      (extractBlockPool fl.mp m₂).nSide
      (fun p => ((extractBlockPool fl.mp m₂).ownerOf p).1) (slotIoPairAt fl.io m₂)
      (Function.update s_abs u (some v)) := by
  set bp₁ := extractBlockPool fl.mp m₁
  set bp₂ := extractBlockPool fl.mp m₂
  have hslot_pair : ∀ p < bp₂.nSide,
      slotIoPairAt fl.io m₂ p = bpPairAt fl.bpL m₂ (bp₂.ownerOf p).1 (bp₂.ownerOf p).2 := by
    intro p hp; obtain ⟨_, _, htp⟩ := hcv₂.ownerOf_bounds_and_toPhys hp
    unfold bpPairAt; dsimp only [FastEpochLayout.bpL]; rw [htp]
  have hno_old : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp₁.bktCount b',
      ¬(b' = epochBucket fl.c fl.U fl.N θ_bkt u ∧
        (bpPairAt fl.bpL m₁ b' loc').1 = keyQuotient (bWhp fl.N) u.val) := by
    intro b' hb' loc' hl' ⟨h1, h2⟩
    have hp := hcv₁.toPhys_lt hb' hl'
    have hfb : (bp₁.ownerOf (bp₁.toPhys b' loc')).1 = feistelBucket (bWhp fl.N)
        (bktHash fl.c fl.U fl.N θ_bkt) u.val := by
      rw [hcv₁.ownerOf_toPhys hb' hl']; exact h1
    have hs := href.lookup_eq_some hp hfb h2
    rw [habs] at hs; cases hs
  have hslot_orig : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp₁.bktCount b',
      b' < 2 ^ bWhp fl.N ∧ (bpPairAt fl.bpL m₁ b' loc').2 < fl.V ∧
      ∃ u' : Fin fl.U, feistelBucket (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt) u'.val = b' ∧
        keyQuotient (bWhp fl.N) u'.val = (bpPairAt fl.bpL m₁ b' loc').1 := by
    intro b' hb' loc' hl'
    have hp := hcv₁.toPhys_lt hb' hl'
    have hsv := href.slot_valid _ hp
    rw [hcv₁.ownerOf_toPhys hb' hl'] at hsv
    exact hsv
  have hpair_lt : ∀ p < bp₂.nSide,
      ((bp₂.ownerOf p).1 = b ∧ (bp₂.ownerOf p).2 = bp₁.bktCount b) ∨
      (bp₂.ownerOf p).2 < bp₁.bktCount (bp₂.ownerOf p).1 := by
    intro p hp
    obtain ⟨hb', hl', _⟩ := hcv₂.ownerOf_bounds_and_toPhys hp
    by_cases hbe : (bp₂.ownerOf p).1 = b
    · rw [hbe, hbc_b] at hl'
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hl') with heq | hlt
      · exact Or.inl ⟨hbe, heq⟩
      · exact Or.inr (by rw [hbe]; exact hlt)
    · rw [hbc_ne _ hbe] at hl'; exact Or.inr hl'
  refine
    { slot_valid := fun p hp => by
        obtain ⟨hb', hl', _⟩ := hcv₂.ownerOf_bounds_and_toPhys hp
        rw [hslot_pair p hp]
        rcases hpair_lt p hp with ⟨hbe, hle⟩ | hlt
        · rw [hbe, hle, hnew]; dsimp only
          exact ⟨by rw [hb_u]; exact feistelBucket_lt _ _ _, v.isLt, ⟨u, hb_u.symm, rfl⟩⟩
        · rw [hold _ hb' _ hlt]; exact hslot_orig _ hb' _ hlt
      slot_inj := fun p₁ hp₁ p₂ hp₂ he1 he2 => by
        obtain ⟨hb₁, _, htp₁⟩ := hcv₂.ownerOf_bounds_and_toPhys hp₁
        obtain ⟨hb₂, _, htp₂⟩ := hcv₂.ownerOf_bounds_and_toPhys hp₂
        rw [hslot_pair p₁ hp₁, hslot_pair p₂ hp₂] at he2
        rcases hpair_lt p₁ hp₁ with ⟨hb1_e, hl1_e⟩ | hl1_lt
        · rcases hpair_lt p₂ hp₂ with ⟨hb2_e, hl2_e⟩ | hl2_lt
          · rw [← htp₁, ← htp₂, hb1_e, hb2_e, hl1_e, hl2_e]
          · rw [hb1_e, hl1_e, hnew, hold _ hb₂ _ hl2_lt] at he2
            exact absurd ⟨by rw [← he1, hb1_e, hb_u], he2.symm⟩ (hno_old _ hb₂ _ hl2_lt)
        · rcases hpair_lt p₂ hp₂ with ⟨hb2_e, hl2_e⟩ | hl2_lt
          · rw [hb2_e, hl2_e, hnew, hold _ hb₁ _ hl1_lt] at he2
            exact absurd ⟨by rw [he1, hb2_e, hb_u], he2⟩ (hno_old _ hb₁ _ hl1_lt)
          · rw [hold _ hb₁ _ hl1_lt, hold _ hb₂ _ hl2_lt] at he2
            have hpq := href.slot_inj _ (hcv₁.toPhys_lt hb₁ hl1_lt) _ (hcv₁.toPhys_lt hb₂ hl2_lt)
              (by rw [hcv₁.ownerOf_toPhys hb₁ hl1_lt, hcv₁.ownerOf_toPhys hb₂ hl2_lt]; exact he1)
              he2
            have hloc_eq : ((bp₁.ownerOf (bp₁.toPhys (bp₂.ownerOf p₁).1 (bp₂.ownerOf p₁).2)).2) =
                (bp₁.ownerOf (bp₁.toPhys (bp₂.ownerOf p₂).1 (bp₂.ownerOf p₂).2)).2 :=
              congrArg (fun x => (bp₁.ownerOf x).2) hpq
            rw [hcv₁.ownerOf_toPhys hb₁ hl1_lt, hcv₁.ownerOf_toPhys hb₂ hl2_lt] at hloc_eq
            rw [← htp₁, ← htp₂, he1, hloc_eq]
      models := fun u' v' => by
        by_cases hu : u' = u
        · subst hu; rw [Function.update_self, Option.some.injEq]
          constructor
          · rintro rfl
            have hl_n : bp₁.bktCount b < bp₂.bktCount b := by rw [hbc_b]; exact Nat.lt_succ_self _
            refine ⟨bp₂.toPhys b (bp₁.bktCount b), hcv₂.toPhys_lt hb hl_n, ?_, ?_, ?_⟩
            · rw [hcv₂.ownerOf_toPhys hb hl_n]; exact hb_u
            · change (bpPairAt fl.bpL m₂ b (bp₁.bktCount b)).1 = _; rw [hnew]
            · change (bpPairAt fl.bpL m₂ b (bp₁.bktCount b)).2 = _; rw [hnew]
          · rintro ⟨p, hp, h1, h2, h3⟩
            obtain ⟨hb', _, _⟩ := hcv₂.ownerOf_bounds_and_toPhys hp
            rw [hslot_pair p hp] at h2 h3
            rcases hpair_lt p hp with ⟨hbe, hle⟩ | hlt
            · rw [hbe, hle, hnew] at h3; exact Fin.ext h3
            · rw [hold _ hb' _ hlt] at h2
              exact absurd ⟨h1, h2⟩ (hno_old _ hb' _ hlt)
        · rw [Function.update_of_ne hu, href.models u' v']
          constructor
          · rintro ⟨p, hp, h1, h2, h3⟩
            obtain ⟨hb', hl', htp'⟩ := hcv₁.ownerOf_bounds_and_toPhys hp
            have hl2 : (bp₁.ownerOf p).2 < bp₂.bktCount (bp₁.ownerOf p).1 := by
              by_cases hbe : (bp₁.ownerOf p).1 = b
              · rw [hbe, hbc_b]; rw [hbe] at hl'; exact Nat.lt_succ_of_lt hl'
              · rwa [hbc_ne _ hbe]
            refine ⟨bp₂.toPhys (bp₁.ownerOf p).1 (bp₁.ownerOf p).2, hcv₂.toPhys_lt hb' hl2,
              ?_, ?_, ?_⟩
            · rw [hcv₂.ownerOf_toPhys hb' hl2]; exact h1
            · change (bpPairAt fl.bpL m₂ (bp₁.ownerOf p).1 (bp₁.ownerOf p).2).1 = _
              rw [hold _ hb' _ hl']; unfold bpPairAt; dsimp only [FastEpochLayout.bpL]
              rw [htp']; exact h2
            · change (bpPairAt fl.bpL m₂ (bp₁.ownerOf p).1 (bp₁.ownerOf p).2).2 = _
              rw [hold _ hb' _ hl']; unfold bpPairAt; dsimp only [FastEpochLayout.bpL]
              rw [htp']; exact h3
          · rintro ⟨p, hp, h1, h2, h3⟩
            obtain ⟨hb', _, _⟩ := hcv₂.ownerOf_bounds_and_toPhys hp
            rw [hslot_pair p hp] at h2 h3
            rcases hpair_lt p hp with ⟨hbe, hle⟩ | hlt
            · rw [hbe, hle, hnew] at h2; rw [hbe] at h1
              exact absurd (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq
                (h1.symm.trans hb_u) h2.symm)) hu
            · rw [hold _ hb' _ hlt] at h2 h3
              refine ⟨bp₁.toPhys (bp₂.ownerOf p).1 (bp₂.ownerOf p).2, hcv₁.toPhys_lt hb' hlt,
                ?_, h2, h3⟩
              rw [hcv₁.ownerOf_toPhys hb' hlt]; exact h1 }

/-- Removing slot `(b, delLoc)` (swapping `(b, lastLoc)` down when `delLoc < lastLoc` and
popping `lastLoc = cnt - 1`) via `bpPopBktBackProg` refines `Function.update s_abs u none`. -/
theorem poolRefines_bpSwapPop {fl : FastEpochLayout} {θ_bkt : BktSeed fl.c fl.U fl.N}
    {m₁ m₂ : ℕ → ℕ} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {b delLoc : ℕ} {u : Fin fl.U}
    (hcv₁ : (extractBlockPool fl.mp m₁).CoreValid)
    (hcv₂ : (extractBlockPool fl.mp m₂).CoreValid)
    (href : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
      (extractBlockPool fl.mp m₁).nSide
      (fun p => ((extractBlockPool fl.mp m₁).ownerOf p).1) (slotIoPairAt fl.io m₁) s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hdel : delLoc < (extractBlockPool fl.mp m₁).bktCount b)
    (hb_u : b = epochBucket fl.c fl.U fl.N θ_bkt u)
    (hq_u : (bpPairAt fl.bpL m₁ b delLoc).1 = keyQuotient (bWhp fl.N) u.val)
    (hbc_b : (extractBlockPool fl.mp m₂).bktCount b = (extractBlockPool fl.mp m₁).bktCount b - 1)
    (hbc_ne : ∀ b' ≠ b, (extractBlockPool fl.mp m₂).bktCount b' =
      (extractBlockPool fl.mp m₁).bktCount b')
    (hpair : ∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp m₂).bktCount b',
      bpPairAt fl.bpL m₂ b' loc' =
        if b' = b ∧ loc' = delLoc then
          bpPairAt fl.bpL m₁ b ((extractBlockPool fl.mp m₁).bktCount b - 1)
        else bpPairAt fl.bpL m₁ b' loc') :
    PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
      (extractBlockPool fl.mp m₂).nSide
      (fun p => ((extractBlockPool fl.mp m₂).ownerOf p).1) (slotIoPairAt fl.io m₂)
      (Function.update s_abs u none) := by
  set bp₁ := extractBlockPool fl.mp m₁
  set bp₂ := extractBlockPool fl.mp m₂
  set lastLoc := bp₁.bktCount b - 1
  have hlast_lt : lastLoc < bp₁.bktCount b := by omega
  let srcLoc : ℕ → ℕ → ℕ := fun b' loc' =>
    if b' = b ∧ loc' = delLoc then lastLoc else loc'
  have hsrc_lt : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp₂.bktCount b',
      srcLoc b' loc' < bp₁.bktCount b' := fun b' _ loc' hl' => by
    dsimp only [srcLoc]
    by_cases hc : b' = b ∧ loc' = delLoc
    · rw [ite_eq_left hc, hc.1]; exact hlast_lt
    · rw [ite_eq_right hc]
      by_cases hbe : b' = b
      · rw [hbe, hbc_b] at hl'; rw [hbe]; omega
      · rwa [hbc_ne _ hbe] at hl'
  have hsrc_ne_del : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp₂.bktCount b',
      ¬(b' = b ∧ srcLoc b' loc' = delLoc) := fun b' _ loc' hl' ⟨hbe, hse⟩ => by
    dsimp only [srcLoc] at hse
    by_cases hc : b' = b ∧ loc' = delLoc
    · rw [ite_eq_left hc] at hse
      rw [hbe, hbc_b] at hl'; omega
    · rw [ite_eq_right hc] at hse; exact hc ⟨hbe, hse⟩
  have hsrc_pair : ∀ p < bp₂.nSide,
      slotIoPairAt fl.io m₂ p =
        slotIoPairAt fl.io m₁ (bp₁.toPhys (bp₂.ownerOf p).1
          (srcLoc (bp₂.ownerOf p).1 (bp₂.ownerOf p).2)) := by
    intro p hp
    obtain ⟨hb', hl', htp'⟩ := hcv₂.ownerOf_bounds_and_toPhys hp
    have h2 : slotIoPairAt fl.io m₂ p =
        bpPairAt fl.bpL m₂ (bp₂.ownerOf p).1 (bp₂.ownerOf p).2 := by
      unfold bpPairAt; dsimp only [FastEpochLayout.bpL]; rw [htp']
    rw [h2, hpair _ hb' _ hl']
    dsimp only [srcLoc]
    split_ifs with hc
    · rw [hc.1]; rfl
    · rfl
  have hp_src : ∀ b' loc', (hb' : b' < numBucketsWhp fl.N) → (hl' : loc' < bp₂.bktCount b') →
      bp₁.toPhys b' (srcLoc b' loc') < bp₁.nSide :=
    fun b' loc' hb' hl' => hcv₁.toPhys_lt hb' (hsrc_lt b' hb' loc' hl')
  refine
    { slot_valid := fun p hp => by
        obtain ⟨hb', hl', _⟩ := hcv₂.ownerOf_bounds_and_toPhys hp
        have hsv := href.slot_valid _ (hp_src _ _ hb' hl')
        rw [hcv₁.ownerOf_toPhys hb' (hsrc_lt _ hb' _ hl')] at hsv
        rwa [hsrc_pair p hp]
      slot_inj := fun p₁ hp₁ p₂ hp₂ he1 he2 => by
        obtain ⟨hb₁, hl₁, htp₁⟩ := hcv₂.ownerOf_bounds_and_toPhys hp₁
        obtain ⟨hb₂, hl₂, htp₂⟩ := hcv₂.ownerOf_bounds_and_toPhys hp₂
        rw [hsrc_pair p₁ hp₁, hsrc_pair p₂ hp₂] at he2
        have hpe := href.slot_inj _ (hp_src _ _ hb₁ hl₁) _ (hp_src _ _ hb₂ hl₂)
          (by rw [hcv₁.ownerOf_toPhys hb₁ (hsrc_lt _ hb₁ _ hl₁),
            hcv₁.ownerOf_toPhys hb₂ (hsrc_lt _ hb₂ _ hl₂)]; exact he1)
          he2
        have hloc_e : srcLoc (bp₂.ownerOf p₁).1 (bp₂.ownerOf p₁).2 =
            srcLoc (bp₂.ownerOf p₂).1 (bp₂.ownerOf p₂).2 := by
          have := congrArg (fun x => (bp₁.ownerOf x).2) hpe
          rwa [hcv₁.ownerOf_toPhys hb₁ (hsrc_lt _ hb₁ _ hl₁),
            hcv₁.ownerOf_toPhys hb₂ (hsrc_lt _ hb₂ _ hl₂)] at this
        have hl12 : (bp₂.ownerOf p₁).2 = (bp₂.ownerOf p₂).2 := by
          dsimp only [srcLoc] at hloc_e
          by_cases h1 : (bp₂.ownerOf p₁).1 = b ∧ (bp₂.ownerOf p₁).2 = delLoc
          · by_cases h2 : (bp₂.ownerOf p₂).1 = b ∧ (bp₂.ownerOf p₂).2 = delLoc
            · exact h1.2.trans h2.2.symm
            · rw [ite_eq_left h1, ite_eq_right h2] at hloc_e
              have hb2e : (bp₂.ownerOf p₂).1 = b := he1.symm.trans h1.1
              rw [hb2e, hbc_b] at hl₂; omega
          · by_cases h2 : (bp₂.ownerOf p₂).1 = b ∧ (bp₂.ownerOf p₂).2 = delLoc
            · rw [ite_eq_right h1, ite_eq_left h2] at hloc_e
              have hb1e : (bp₂.ownerOf p₁).1 = b := he1.trans h2.1
              rw [hb1e, hbc_b] at hl₁; omega
            · rwa [ite_eq_right h1, ite_eq_right h2] at hloc_e
        rw [← htp₁, ← htp₂, he1, hl12]
      models := fun u' v' => by
        by_cases hu : u' = u
        · subst hu; rw [Function.update_self]
          refine ⟨by rintro ⟨⟩, fun ⟨p, hp, h1, h2, _⟩ => ?_⟩
          obtain ⟨hb', hl', _⟩ := hcv₂.ownerOf_bounds_and_toPhys hp
          rw [hsrc_pair p hp] at h2
          have hpe := href.slot_inj _ (hp_src _ _ hb' hl') _ (hcv₁.toPhys_lt hb hdel)
            (by rw [hcv₁.ownerOf_toPhys hb' (hsrc_lt _ hb' _ hl'),
              hcv₁.ownerOf_toPhys hb hdel]; exact h1.trans hb_u.symm)
            (h2.trans hq_u.symm)
          have hpair_eq := congrArg bp₁.ownerOf hpe
          rw [hcv₁.ownerOf_toPhys hb' (hsrc_lt _ hb' _ hl'),
            hcv₁.ownerOf_toPhys hb hdel] at hpair_eq
          exact False.elim (hsrc_ne_del _ hb' _ hl'
            ⟨congrArg Prod.fst hpair_eq, congrArg Prod.snd hpair_eq⟩)
        · rw [Function.update_of_ne hu, href.models u' v']
          constructor
          · rintro ⟨p, hp, h1, h2, h3⟩
            obtain ⟨hb', hl', htp'⟩ := hcv₁.ownerOf_bounds_and_toPhys hp
            have hne_del : ¬((bp₁.ownerOf p).1 = b ∧ (bp₁.ownerOf p).2 = delLoc) := by
              rintro ⟨hbe, hle⟩
              have hq_e : (slotIoPairAt fl.io m₁ p).1 = keyQuotient (bWhp fl.N) u.val := by
                rw [← htp', hbe, hle]; exact hq_u
              have : u' = u := Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq
                (h1.symm.trans (hbe.trans hb_u)) (h2.symm.trans hq_e))
              exact hu this
            by_cases hlast : (bp₁.ownerOf p).1 = b ∧ (bp₁.ownerOf p).2 = lastLoc
            · have hdl_lt : delLoc < bp₂.bktCount b := by
                rw [hbc_b]
                have : delLoc ≠ lastLoc := fun he => hne_del ⟨hlast.1, hlast.2.trans he.symm⟩
                omega
              refine ⟨bp₂.toPhys b delLoc, hcv₂.toPhys_lt hb hdl_lt, ?_, ?_, ?_⟩
              · rw [hcv₂.ownerOf_toPhys hb hdl_lt]; rw [← hlast.1]; exact h1
              · rw [hsrc_pair _ (hcv₂.toPhys_lt hb hdl_lt),
                  hcv₂.ownerOf_toPhys hb hdl_lt]
                change (slotIoPairAt fl.io m₁ (bp₁.toPhys b (srcLoc b delLoc))).1 = _
                dsimp only [srcLoc]; rw [ite_eq_left ⟨rfl, rfl⟩, ← hlast.1, ← hlast.2, htp']
                exact h2
              · rw [hsrc_pair _ (hcv₂.toPhys_lt hb hdl_lt),
                  hcv₂.ownerOf_toPhys hb hdl_lt]
                change (slotIoPairAt fl.io m₁ (bp₁.toPhys b (srcLoc b delLoc))).2 = _
                dsimp only [srcLoc]; rw [ite_eq_left ⟨rfl, rfl⟩, ← hlast.1, ← hlast.2, htp']
                exact h3
            · have hl2 : (bp₁.ownerOf p).2 < bp₂.bktCount (bp₁.ownerOf p).1 := by
                by_cases hbe : (bp₁.ownerOf p).1 = b
                · rw [hbe, hbc_b]; have : (bp₁.ownerOf p).2 ≠ lastLoc :=
                    fun he => hlast ⟨hbe, he⟩
                  rw [hbe] at hl'; omega
                · rwa [hbc_ne _ hbe]
              refine ⟨bp₂.toPhys (bp₁.ownerOf p).1 (bp₁.ownerOf p).2, hcv₂.toPhys_lt hb' hl2,
                ?_, ?_, ?_⟩
              · rw [hcv₂.ownerOf_toPhys hb' hl2]; exact h1
              · rw [hsrc_pair _ (hcv₂.toPhys_lt hb' hl2), hcv₂.ownerOf_toPhys hb' hl2]
                dsimp only [srcLoc]; rw [ite_eq_right hne_del, htp']; exact h2
              · rw [hsrc_pair _ (hcv₂.toPhys_lt hb' hl2), hcv₂.ownerOf_toPhys hb' hl2]
                dsimp only [srcLoc]; rw [ite_eq_right hne_del, htp']; exact h3
          · rintro ⟨p, hp, h1, h2, h3⟩
            obtain ⟨hb', hl', _⟩ := hcv₂.ownerOf_bounds_and_toPhys hp
            rw [hsrc_pair p hp] at h2 h3
            refine ⟨bp₁.toPhys (bp₂.ownerOf p).1 (srcLoc (bp₂.ownerOf p).1 (bp₂.ownerOf p).2),
              hp_src _ _ hb' hl', ?_, h2, h3⟩
            rw [hcv₁.ownerOf_toPhys hb' (hsrc_lt _ hb' _ hl')]; exact h1 }

/-! ## Section 2: Unindexing, Relocating, and `fastRemoveAtProg` Definitions -/

private def fastDelShadowTryStepProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, (b, role)), (fp, _delLoc)) => do
    let sc ← fastReadBktLaneProg (pBase, (b, 15))
    if sc ≠ 0 then do
      let sRole ← shadowRoleProg role
      fastBTreeDeleteProg ((pBase, (b, sRole)), fp)
    else pure ()

private theorem fastDelShadowTryStepProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)}
    {s : Memory.State} (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastDelShadowTryStepProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨fp, _⟩⟩
  unfold fastDelShadowTryStepProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_shadowRoleProg]
    exact fastBTreeDeleteProg_pre (x := ((pBase, (b, _)), fp)) h
  · exact h

private theorem realizesBounded_fastDelShadowTryStep :
    RealizesBounded .exact fastDelShadowTryStepProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have hsr := realizesBounded_shadowRole
  have hbd := realizesBounded_fastBTreeDelete
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨fp, _⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktLaneProg,
      runClient_state_shadowRoleProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

private def fastDelTryStepProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, (b, role)), (delLoc, u_val)) => do
    let ta ← fastReadMetaProg (pBase, 6)
    let tb ← fastReadMetaProg (pBase, 7)
    let tp ← fastReadMetaProg (pBase, 9)
    if ta = 1 ∧ tb = b ∧ delLoc < tp then do
      let ts ← fastReadMetaProg (pBase, 8)
      let fpT ← fastFpHashProg (pBase, (ts, u_val))
      let tRole ← tryRoleProg role
      fastBTreeDeleteProg ((pBase, (b, tRole)), fpT)
    else pure ()

private theorem fastDelTryStepProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)}
    {s : Memory.State} (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastDelTryStepProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨delLoc, u_val⟩⟩
  unfold fastDelTryStepProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
      StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
      StateTransitionSpec.clientState_bind, clientState_tryRoleProg]
    exact fastBTreeDeleteProg_pre (x := ((pBase, (b, _)), _)) h
  · exact h

private theorem realizesBounded_fastDelTryStep :
    RealizesBounded .exact fastDelTryStepProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hfp := realizesBounded_fastFpHash
  have htr := realizesBounded_tryRole
  have hbd := realizesBounded_fastBTreeDelete
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨delLoc, u_val⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg,
      runClient_state_fastFpHashProg, runClient_state_tryRoleProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-- Delete `u_val` (at `b, delLoc`) from `curRole b`, plus from `shadowRoleOf (curRole b)` if
`shadowCode b ≠ 0` and from `tryRoleOf (curRole b)` if `tryAct = 1 ∧ tryBkt = b ∧ delLoc < tryPos`
(`¬ReadsWidth`). -/
private def fastDeleteFromBTreesProg : (ℕ × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((pBase, (b, delLoc)), u_val) => do
    let M ← Memory.read (pBase + 11)
    if b < M then do
      let salt ← fastReadBktLaneProg (pBase, (b, 5))
      let role ← fastReadBktLaneProg (pBase, (b, 12))
      let fp ← fastFpHashProg (pBase, (salt, u_val))
      fastBTreeDeleteProg ((pBase, (b, role)), fp)
      fastDelShadowTryStepProg ((pBase, (b, role)), (fp, delLoc))
      fastDelTryStepProg ((pBase, (b, role)), (delLoc, u_val))
    else pure ()

private theorem fastDeleteFromBTreesProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastDeleteFromBTreesProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, delLoc⟩⟩, u_val⟩
  unfold fastDeleteFromBTreesProg; dsimp only
  rw [StateTransitionSpec.clientState_bind,
    show (Memory.spec 0).clientState s (Memory.read (pBase + 11)) = s from rfl]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    refine fastDelTryStepProg_pre (x := ((pBase, _), _)) ?_; dsimp only
    refine fastDelShadowTryStepProg_pre (x := ((pBase, _), _)) ?_; dsimp only
    exact fastBTreeDeleteProg_pre (x := ((pBase, (_, _)), _)) h
  · exact h

private theorem realizesBounded_fastDeleteFromBTrees :
    RealizesBounded .exact fastDeleteFromBTreesProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have hfp := realizesBounded_fastFpHash
  have hbd := realizesBounded_fastBTreeDelete
  have hds := realizesBounded_fastDelShadowTryStep
  have hdt := realizesBounded_fastDelTryStep
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, delLoc⟩⟩, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktLaneProg,
      runClient_state_fastFpHashProg] at *
    first
    | exact ⟨fl, rfl, hr⟩
    | exact fastBTreeDeleteProg_pre (x := ((fl.pBase, (b, _)), _)) ⟨fl, rfl, hr⟩
    | exact fastDelShadowTryStepProg_pre (x := ((fl.pBase, (b, _)), (_, delLoc)))
        (fastBTreeDeleteProg_pre (x := ((fl.pBase, (b, _)), _)) ⟨fl, rfl, hr⟩)
    | omega)

/-- Remove key `u_val` stored at `(b, delLoc)` from whichever tier indexes it (`BufCur`, `BufOld`
when `subStep < Q / 2`, or `BTree(b, curRole b)` + `shadow`/`tryMap`). -/
private def fastUnindexAtProg : (ℕ × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((pBase, (b, delLoc)), u_val) => do
    let rk ← fastRKeyProg (pBase, u_val)
    let curR ← fastReadMetaProg (pBase, 3)
    if curR < 2 then do
      let hc ← fastBufLookupProg ((pBase, curR), rk)
      if hc.1 = 1 ∧ hc.2.1 = b ∧ hc.2.2 = delLoc then
        fastBufDeleteProg ((pBase, curR), rk)
      else do
        let ss ← fastReadMetaProg (pBase, 4)
        let qMax ← Memory.read (pBase + 23)
        if ss < qMax / 2 then do
          let oldR ← pure (1 - curR)
          let ho ← fastBufLookupProg ((pBase, oldR), rk)
          if ho.1 = 1 ∧ ho.2.1 = b ∧ ho.2.2 = delLoc then
            fastBufDeleteProg ((pBase, oldR), rk)
          else
            fastDeleteFromBTreesProg ((pBase, (b, delLoc)), u_val)
        else
          fastDeleteFromBTreesProg ((pBase, (b, delLoc)), u_val)
    else pure ()

private theorem fastUnindexAtProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastUnindexAtProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, delLoc⟩⟩, u_val⟩
  unfold fastUnindexAtProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastRKeyProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastBufLookupProg]
    split_ifs
    · exact fastBufDeleteProg_pre (x := ((pBase, _), _)) h
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
        StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read (pBase + 23)) = s from rfl]
      split_ifs
      · rw [pure_bind, StateTransitionSpec.clientState_bind, clientState_fastBufLookupProg]
        split_ifs
        · exact fastBufDeleteProg_pre (x := ((pBase, _), _)) h
        · exact fastDeleteFromBTreesProg_pre (x := ((pBase, (b, delLoc)), u_val)) h
      · exact fastDeleteFromBTreesProg_pre (x := ((pBase, (b, delLoc)), u_val)) h
  · exact h

private theorem realizesBounded_fastUnindexAt :
    RealizesBounded .exact fastUnindexAtProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrk := realizesBounded_fastRKey
  have hrm := realizesBounded_fastReadMeta
  have hbl := realizesBounded_fastBufLookup
  have hbd := realizesBounded_fastBufDelete
  have hdt := realizesBounded_fastDeleteFromBTrees
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, delLoc⟩⟩, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastRKeyProg,
      runClient_state_fastReadMetaProg, runClient_state_fastBufLookupProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

private def fastRelocShadowStepProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, (b, role)), (fp, delLoc)) => do
    let sc ← fastReadBktLaneProg (pBase, (b, 15))
    let nCap ← Memory.read (pBase + 0)
    if sc ≠ 0 ∧ delLoc < sc - 1 then do
      let sRole ← shadowRoleProg role
      fastBTreeInsertProg ((pBase, (b, sRole)), (fp, delLoc))
      let shIns ← fastReadBktLaneProg (pBase, (b, 14))
      if shIns < nCap then
        fastWriteBktLaneProg ((pBase, (b, 14)), shIns + 1)
      else pure ()
    else pure ()

private theorem fastRelocShadowStepProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)}
    {s : Memory.State} (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastRelocShadowStepProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨fp, delLoc⟩⟩
  unfold fastRelocShadowStepProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
    StateTransitionSpec.clientState_bind,
    show (Memory.spec 0).clientState s (Memory.read (pBase + 0)) = s from rfl]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_shadowRoleProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_fastReadBktLaneProg]
    split_ifs
    · refine fastWriteBktLaneProg_pre (x := ((pBase, _), _)) ?_; dsimp only [fastArgPBase]
      exact fastBTreeInsertProg_pre (x := ((pBase, (b, _)), (fp, delLoc))) h
    · exact fastBTreeInsertProg_pre (x := ((pBase, (b, _)), (fp, delLoc))) h
  · exact h

private theorem realizesBounded_fastRelocShadowStep :
    RealizesBounded .exact fastRelocShadowStepProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have hwl := realizesBounded_fastWriteBktLane
  have hsr := realizesBounded_shadowRole
  have hbi := realizesBounded_fastBTreeInsert
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨fp, delLoc⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm0' : s.mem (fl.pBase + 0) = fl.N := hr.2.1 0 (by decide)
    have hm0 : s.mem fl.pBase = fl.N := by rwa [Nat.add_zero] at hm0'
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktLaneProg,
      runClient_state_shadowRoleProg, hm0', hm0] at *
    first
    | exact ⟨fl, rfl, hr⟩
    | exact fastBTreeInsertProg_pre (x := ((fl.pBase, _), _)) ⟨fl, rfl, hr⟩
    | omega)

private def fastRelocTryInsProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, (b, tRole)), (fpT, delLoc)) => do
    let lk ← fastBTreeLookupProg ((pBase, (b, tRole)), fpT)
    if lk.1 = 1 then
      advanceTrySaltProg pBase
    else do
      let nCap ← Memory.read (pBase + 0)
      fastBTreeInsertProg ((pBase, (b, tRole)), (fpT, delLoc))
      let ti ← fastReadMetaProg (pBase, 17)
      if ti < nCap then
        fastWriteMetaProg ((pBase, 17), ti + 1)
      else pure ()

private theorem fastRelocTryInsProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)}
    {s : Memory.State} (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastRelocTryInsProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, tRole⟩⟩, ⟨fpT, delLoc⟩⟩
  unfold fastRelocTryInsProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastBTreeLookupProg]
  split_ifs
  · exact advanceTrySaltProg_pre h
  · rw [StateTransitionSpec.clientState_bind,
      show (Memory.spec 0).clientState s (Memory.read (pBase + 0)) = s from rfl,
      StateTransitionSpec.clientState_bind]
    have h1 := fastBTreeInsertProg_pre (x := ((pBase, (b, tRole)), (fpT, delLoc))) h
    rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
    split_ifs
    · exact fastWriteMetaProg_pre (x := ((pBase, 17), _)) h1
    · exact h1

private theorem realizesBounded_fastRelocTryIns :
    RealizesBounded .exact fastRelocTryInsProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hbl := realizesBounded_fastBTreeLookup
  have had := realizesBounded_advanceTrySalt
  have hbi := realizesBounded_fastBTreeInsert
  have hrm := realizesBounded_fastReadMeta
  have hwm := realizesBounded_fastWriteMeta
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, tRole⟩⟩, ⟨fpT, delLoc⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm0' : s.mem (fl.pBase + 0) = fl.N := hr.2.1 0 (by decide)
    have hm0 : s.mem fl.pBase = fl.N := by rwa [Nat.add_zero] at hm0'
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastBTreeLookupProg,
      runClient_state_fastReadMetaProg, hm0', hm0] at *
    first
    | exact ⟨fl, rfl, hr⟩
    | exact fastBTreeInsertProg_pre (x := ((fl.pBase, _), _)) ⟨fl, rfl, hr⟩
    | omega)

private def fastRelocTryStepProg : (ℕ × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | ((pBase, (b, role)), ((delLoc, lastLoc), u_last)) => do
    let ta ← fastReadMetaProg (pBase, 6)
    let tb ← fastReadMetaProg (pBase, 7)
    let tp ← fastReadMetaProg (pBase, 9)
    if ta = 1 ∧ tb = b then do
      let ts ← fastReadMetaProg (pBase, 8)
      let fpT ← fastFpHashProg (pBase, (ts, u_last))
      let tRole ← tryRoleProg role
      if lastLoc < tp then
        fastBTreeUpdateProg ((pBase, (b, tRole)), (fpT, delLoc))
      else if delLoc < tp then
        fastRelocTryInsProg ((pBase, (b, tRole)), (fpT, delLoc))
      else pure ()
    else pure ()

private theorem fastRelocTryStepProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)}
    {s : Memory.State} (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastRelocTryStepProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨⟨delLoc, lastLoc⟩, u_last⟩⟩
  unfold fastRelocTryStepProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  by_cases hc : (Memory.spec 0).clientResult s (fastReadMetaProg (pBase, 6)) = 1 ∧
      (Memory.spec 0).clientResult s (fastReadMetaProg (pBase, 7)) = b
  · rw [ite_eq_left hc, StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
      StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
      StateTransitionSpec.clientState_bind, clientState_tryRoleProg]
    by_cases hlt : lastLoc < (Memory.spec 0).clientResult s (fastReadMetaProg (pBase, 9))
    · rw [ite_eq_left hlt]
      exact fastBTreeUpdateProg_pre (x := ((pBase, _), _)) h
    · rw [ite_eq_right hlt]
      by_cases hdel : delLoc < (Memory.spec 0).clientResult s (fastReadMetaProg (pBase, 9))
      · rw [ite_eq_left hdel]
        exact fastRelocTryInsProg_pre (x := ((pBase, _), _)) h
      · rw [ite_eq_right hdel]; exact h
  · rw [ite_eq_right hc]; exact h

private theorem realizesBounded_fastRelocTryStep :
    RealizesBounded .exact fastRelocTryStepProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hfp := realizesBounded_fastFpHash
  have htr := realizesBounded_tryRole
  have hbu := realizesBounded_fastBTreeUpdate
  have hti := realizesBounded_fastRelocTryIns
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨⟨delLoc, lastLoc⟩, u_last⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg,
      runClient_state_fastFpHashProg, runClient_state_tryRoleProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-- Relocate `u_last` (in `BTree(b, curRole b)`) from `lastLoc` to `delLoc < lastLoc`, keeping
`shadow` and `tryMap` consistent. -/
private def fastRelocBTreeProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, (b, delLoc)), (lastLoc, u_last)) => do
    let M ← Memory.read (pBase + 11)
    if b < M ∧ delLoc < lastLoc then do
      let salt ← fastReadBktLaneProg (pBase, (b, 5))
      let role ← fastReadBktLaneProg (pBase, (b, 12))
      let fp ← fastFpHashProg (pBase, (salt, u_last))
      fastBTreeUpdateProg ((pBase, (b, role)), (fp, delLoc))
      fastRelocShadowStepProg ((pBase, (b, role)), (fp, delLoc))
      fastRelocTryStepProg ((pBase, (b, role)), ((delLoc, lastLoc), u_last))
    else pure ()

private theorem fastRelocBTreeProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastRelocBTreeProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, delLoc⟩⟩, ⟨lastLoc, u_last⟩⟩
  unfold fastRelocBTreeProg; dsimp only
  rw [StateTransitionSpec.clientState_bind,
    show (Memory.spec 0).clientState s (Memory.read (pBase + 11)) = s from rfl]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    exact fastRelocTryStepProg_pre (x := ((pBase, _), _))
      (fastRelocShadowStepProg_pre (x := ((pBase, _), _))
        (fastBTreeUpdateProg_pre (x := ((pBase, _), _)) h))
  · exact h

private theorem realizesBounded_fastRelocBTree :
    RealizesBounded .exact fastRelocBTreeProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have hfp := realizesBounded_fastFpHash
  have hbu := realizesBounded_fastBTreeUpdate
  have hrs := realizesBounded_fastRelocShadowStep
  have hrt := realizesBounded_fastRelocTryStep
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, delLoc⟩⟩, ⟨lastLoc, u_last⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktLaneProg,
      runClient_state_fastFpHashProg] at *
    first
    | exact ⟨fl, rfl, hr⟩
    | exact fastBTreeUpdateProg_pre (x := ((fl.pBase, (b, _)), (_, delLoc))) ⟨fl, rfl, hr⟩
    | exact fastRelocShadowStepProg_pre (x := ((fl.pBase, (b, _)), (_, delLoc)))
        (fastBTreeUpdateProg_pre (x := ((fl.pBase, (b, _)), (_, delLoc))) ⟨fl, rfl, hr⟩)
    | omega)

/-- Relocate `u_last` from `(b, lastLoc)` to `(b, delLoc)` across `BufCur`, `BufOld`, or `BTree`.
-/
private def fastRelocLastProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, (b, delLoc)), (lastLoc, u_last)) => do
    let rk ← fastRKeyProg (pBase, u_last)
    let curR ← fastReadMetaProg (pBase, 3)
    if curR < 2 then do
      let hc ← fastBufLookupProg ((pBase, curR), rk)
      if hc.1 = 1 ∧ hc.2.1 = b ∧ hc.2.2 = lastLoc then
        fastBufInsertProg ((pBase, curR), (rk, (b, delLoc)))
      else do
        let ss ← fastReadMetaProg (pBase, 4)
        let qMax ← Memory.read (pBase + 23)
        if ss < qMax / 2 then do
          let oldR ← pure (1 - curR)
          let ho ← fastBufLookupProg ((pBase, oldR), rk)
          if ho.1 = 1 ∧ ho.2.1 = b ∧ ho.2.2 = lastLoc then
            fastBufInsertProg ((pBase, oldR), (rk, (b, delLoc)))
          else
            fastRelocBTreeProg ((pBase, (b, delLoc)), (lastLoc, u_last))
        else
          fastRelocBTreeProg ((pBase, (b, delLoc)), (lastLoc, u_last))
    else pure ()

private theorem fastRelocLastProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastRelocLastProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, delLoc⟩⟩, ⟨lastLoc, u_last⟩⟩
  unfold fastRelocLastProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastRKeyProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastBufLookupProg]
    split_ifs
    · exact fastBufInsertProg_pre (x := ((pBase, _), (_, (b, delLoc)))) h
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
        StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read (pBase + 23)) = s from rfl]
      split_ifs
      · rw [pure_bind, StateTransitionSpec.clientState_bind, clientState_fastBufLookupProg]
        split_ifs
        · exact fastBufInsertProg_pre (x := ((pBase, _), (_, (b, delLoc)))) h
        · exact fastRelocBTreeProg_pre (x := ((pBase, (b, delLoc)), (lastLoc, u_last))) h
      · exact fastRelocBTreeProg_pre (x := ((pBase, (b, delLoc)), (lastLoc, u_last))) h
  · exact h

private theorem realizesBounded_fastRelocLast :
    RealizesBounded .exact fastRelocLastProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrk := realizesBounded_fastRKey
  have hrm := realizesBounded_fastReadMeta
  have hbl := realizesBounded_fastBufLookup
  have hbi := realizesBounded_fastBufInsert
  have hrb := realizesBounded_fastRelocBTree
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, delLoc⟩⟩, ⟨lastLoc, u_last⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastRKeyProg,
      runClient_state_fastReadMetaProg, runClient_state_fastBufLookupProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

private def fastSwapLastDownProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, b), (delLoc, lastLoc)) =>
    if delLoc < lastLoc then do
      let qvLast ← fastBpReadAtProg (pBase, (b, lastLoc))
      let uLast ← fastFeistelReconProg (pBase, (b, qvLast.1))
      fastBpWriteAtProg ((pBase, (b, delLoc)), qvLast)
      fastRelocLastProg ((pBase, (b, delLoc)), (lastLoc, uLast))
    else pure ()

private theorem fastSwapLastDownProg_pre {w : ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastSwapLastDownProg x)) := by
  rcases x with ⟨⟨pBase, b⟩, ⟨delLoc, lastLoc⟩⟩
  unfold fastSwapLastDownProg; dsimp only
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg,
      StateTransitionSpec.clientState_bind, clientState_fastFeistelReconProg,
      StateTransitionSpec.clientState_bind]
    refine fastRelocLastProg_pre (x := ((pBase, _), _)) ?_; dsimp only
    exact fastBpWriteAtProg_pre (x := ((pBase, (b, delLoc)), _)) h
  · exact h

private theorem realizesBounded_fastSwapLastDown :
    RealizesBounded .exact fastSwapLastDownProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hbr := realizesBounded_fastBpReadAt
  have hfr := realizesBounded_fastFeistelRecon
  have hbw := realizesBounded_fastBpWriteAt
  have hrl := realizesBounded_fastRelocLast
  realize
  all_goals (
    rcases d with ⟨⟨pBase, b⟩, ⟨delLoc, lastLoc⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastBpReadAtProg,
      runClient_state_fastFeistelReconProg] at *
    first
    | exact ⟨fl, rfl, hr⟩
    | exact fastBpWriteAtProg_pre (x := ((fl.pBase, (b, delLoc)), _)) ⟨fl, rfl, hr⟩)

private def fastPromoteShadowIfDoneProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((pBase, b), cnt) => do
    let sc ← fastReadBktLaneProg (pBase, (b, 15))
    if sc = cnt then do
      let role ← fastReadBktLaneProg (pBase, (b, 12))
      let sRole ← shadowRoleProg role
      let shIns ← fastReadBktLaneProg (pBase, (b, 14))
      fastWriteBktLaneProg ((pBase, (b, 12)), sRole)
      fastWriteBktLaneProg ((pBase, (b, 13)), shIns)
      fastWriteBktLaneProg ((pBase, (b, 15)), 0)
    else pure ()

private theorem fastPromoteShadowIfDoneProg_pre {w : ℕ} {x : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastPromoteShadowIfDoneProg x)) := by
  rcases x with ⟨⟨pBase, b⟩, cnt⟩
  unfold fastPromoteShadowIfDoneProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_shadowRoleProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    refine fastWriteBktLaneProg_pre (x := ((pBase, _), _)) ?_; dsimp only [fastArgPBase]
    refine fastWriteBktLaneProg_pre (x := ((pBase, _), _)) ?_; dsimp only [fastArgPBase]
    exact fastWriteBktLaneProg_pre (x := ((pBase, (b, 12)), _)) h
  · exact h

private theorem realizesBounded_fastPromoteShadowIfDone :
    RealizesBounded .exact fastPromoteShadowIfDoneProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have hwl := realizesBounded_fastWriteBktLane
  have hsr := realizesBounded_shadowRole
  realize
  all_goals (
    rcases d with ⟨⟨pBase, b⟩, cnt⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktLaneProg,
      runClient_state_shadowRoleProg] at *
    first
    | exact ⟨fl, rfl, hr⟩
    | exact fastWriteBktLaneProg_pre (x := ((fl.pBase, (b, 12)), _)) ⟨fl, rfl, hr⟩
    | exact fastWriteBktLaneProg_pre (x := ((fl.pBase, (b, 13)), _))
        (fastWriteBktLaneProg_pre (x := ((fl.pBase, (b, 12)), _)) ⟨fl, rfl, hr⟩)
    | omega)

private def fastClampTryPosProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, b), (cnt, lastLoc)) => do
    let ta ← fastReadMetaProg (pBase, 6)
    let tb ← fastReadMetaProg (pBase, 7)
    let tp ← fastReadMetaProg (pBase, 9)
    if ta = 1 ∧ tb = b ∧ tp = cnt then
      fastWriteMetaProg ((pBase, 9), lastLoc)
    else pure ()

private theorem fastClampTryPosProg_pre {w : ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastClampTryPosProg x)) := by
  rcases x with ⟨⟨pBase, b⟩, ⟨cnt, lastLoc⟩⟩
  unfold fastClampTryPosProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  split_ifs
  · exact fastWriteMetaProg_pre (x := ((pBase, 9), lastLoc)) h
  · exact h

private theorem realizesBounded_fastClampTryPos :
    RealizesBounded .exact fastClampTryPosProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hwm := realizesBounded_fastWriteMeta
  realize
  all_goals (
    rcases d with ⟨⟨pBase, b⟩, ⟨cnt, lastLoc⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-- Remove and swap-pop key `u_val` stored at `(b, delLoc)` (`b < M, delLoc < bktCount b`) in
`O_c(1)` worst-case time, preserving all three index tiers, `shadow` compaction (auto-promoting
when `shadowCode b = cnt`), and `tryMap` (clamping `tryPos` when `tryPos = cnt`, advancing
`trySalt` on collision) (`¬ReadsWidth`). -/
def fastRemoveAtProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, b), (delLoc, u_val)) => do
    let M ← Memory.read (pBase + 11)
    if b < M then do
      let cnt ← fastReadBktCntProg (pBase, b)
      if delLoc < cnt then do
        let lastLoc ← pure (cnt - 1)
        fastUnindexAtProg ((pBase, (b, delLoc)), u_val)
        fastSwapLastDownProg ((pBase, b), (delLoc, lastLoc))
        fastBpPopBktBackProg (pBase, b)
        fastPromoteShadowIfDoneProg ((pBase, b), cnt)
        fastClampTryPosProg ((pBase, b), (cnt, lastLoc))
      else pure ()
    else pure ()

theorem fastRemoveAtProg_pre {w : ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : FastProgPre w (fastArgPBase x) s) :
    FastProgPre w (fastArgPBase x) ((Memory.spec 0).clientState s (fastRemoveAtProg x)) := by
  rcases x with ⟨⟨pBase, b⟩, ⟨delLoc, u_val⟩⟩
  dsimp only [fastArgPBase] at h ⊢
  unfold fastRemoveAtProg; dsimp only
  rw [StateTransitionSpec.clientState_bind,
    show (Memory.spec 0).clientState s (Memory.read (pBase + 11)) = s from rfl]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg]
    split_ifs
    · rw [pure_bind, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
      exact fastClampTryPosProg_pre (x := ((pBase, _), _))
        (fastPromoteShadowIfDoneProg_pre (x := ((pBase, _), _))
          (fastBpPopBktBackProg_pre (x := (pBase, _))
            (fastSwapLastDownProg_pre (x := ((pBase, _), _))
              (fastUnindexAtProg_pre (x := ((pBase, _), _)) h))))
    · exact h
  · exact h

theorem realizesBounded_fastRemoveAt :
    RealizesBounded .exact fastRemoveAtProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hbc := realizesBounded_fastReadBktCnt
  have hui := realizesBounded_fastUnindexAt
  have hsw := realizesBounded_fastSwapLastDown
  have hbp := realizesBounded_fastBpPopBktBack
  have hpr := realizesBounded_fastPromoteShadowIfDone
  have hcl := realizesBounded_fastClampTryPos
  realize
  all_goals (
    rcases d with ⟨⟨pBase, b⟩, ⟨delLoc, u_val⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktCntProg] at *
    first
    | exact ⟨fl, rfl, hr⟩
    | exact fastUnindexAtProg_pre (x := ((fl.pBase, (b, delLoc)), u_val)) ⟨fl, rfl, hr⟩
    | exact fastSwapLastDownProg_pre (x := ((fl.pBase, b), (delLoc, _)))
        (fastUnindexAtProg_pre (x := ((fl.pBase, (b, delLoc)), u_val)) ⟨fl, rfl, hr⟩)
    | exact fastBpPopBktBackProg_pre (x := (fl.pBase, b))
        (fastSwapLastDownProg_pre (x := ((fl.pBase, b), (delLoc, _)))
          (fastUnindexAtProg_pre (x := ((fl.pBase, (b, delLoc)), u_val)) ⟨fl, rfl, hr⟩))
    | exact fastPromoteShadowIfDoneProg_pre (x := ((fl.pBase, b), _))
        (fastBpPopBktBackProg_pre (x := (fl.pBase, b))
          (fastSwapLastDownProg_pre (x := ((fl.pBase, b), (delLoc, _)))
            (fastUnindexAtProg_pre (x := ((fl.pBase, (b, delLoc)), u_val)) ⟨fl, rfl, hr⟩)))
    | omega)

/-- Migration pop on a non-empty large fast epoch (`0 < bp.nSide`): pops the tail entry of bucket
`(bp.ownerOf 0).1` in `O_c(1)` worst-case time without calling `advanceSubEpochProg`
(`¬ReadsWidth`). -/
def fastPopAnyProg (pBase : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let ow ← fastBpOwnerOfZeroProg pBase
  let b ← pure ow.1
  let cnt ← fastReadBktCntProg (pBase, b)
  if 0 < cnt then do
    let lastLoc ← pure (cnt - 1)
    let qv ← fastBpReadAtProg (pBase, (b, lastLoc))
    let u_val ← fastFeistelReconProg (pBase, (b, qv.1))
    fastRemoveAtProg ((pBase, b), (lastLoc, u_val))
    pure (u_val, qv.2)
  else
    pure (0, 0)

theorem realizesBounded_fastPopAny :
    RealizesBounded .exact fastPopAnyProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hoo := realizesBounded_fastBpOwnerOfZero
  have hbc := realizesBounded_fastReadBktCnt
  have hbr := realizesBounded_fastBpReadAt
  have hfr := realizesBounded_fastFeistelRecon
  have hrm := realizesBounded_fastRemoveAt
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastBpOwnerOfZeroProg,
      runClient_state_fastReadBktCntProg, runClient_state_fastBpReadAtProg,
      runClient_state_fastFeistelReconProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-! ## Section 3: Unconditional Specification of `fastRemoveAtProg` and Potential Preservation -/

/-- Worst-case `O_c(1)` memory cost bound for `fastRemoveAtProg`, independent of `N, U, V, w`. -/
@[expose] def fastRemoveAtCost (c : ℕ) : ℕ :=
  40 * cTabWhp c + 12 * dTabWhp c * (cTabWhp c + 2) + 180 * hMaxBTree + 10000

/-- Worst-case `O_c(1)` memory cost bound for `fastPopAnyProg`, independent of `N, U, V, w`. -/
@[expose] def fastPopAnyCost (c : ℕ) : ℕ :=
  fastRemoveAtCost c + 2 * dTabWhp c * (cTabWhp c + 2) + 200

private theorem bufDelete_props {cTab bChar rKey : ℕ} {tr : BufTrie} :
    let tr' := bufDelete cTab bChar tr rKey
    tr'.nodeAlloc = tr.nodeAlloc ∧
    tr'.itemAlloc = tr.itemAlloc ∧
    (RawBufTrieBounds tr → RawBufTrieBounds tr') ∧
    (RawClearableBounds tr → RawClearableBounds tr') ∧
    (∀ id b loc, bufCheckSlot tr' id = some (b, loc) →
      bufCheckSlot tr id = some (b, loc)) := by
  dsimp only
  unfold bufDelete
  cases hwk : bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => exact ⟨rfl, rfl, id, id, fun _ _ _ h => h⟩
  | some nd =>
    dsimp only
    by_cases hcond : tr.nodeLeafItem nd = 0 ∨ tr.nodeActive nd = 0
    · rw [ite_eq_left hcond]
      exact ⟨rfl, rfl, id, id, fun _ _ _ h => h⟩
    · rw [ite_eq_right hcond]
      refine ⟨rfl, rfl, fun h => h, fun h => h, fun id b loc h => ?_⟩
      unfold bufCheckSlot at h ⊢
      by_cases hid : id < tr.itemAlloc
      · rw [ite_eq_left hid] at h ⊢; dsimp only at h ⊢
        by_cases hc : tr.nodeLeafItem (tr.itemLeaf id) = id + 1 ∧
            Function.update tr.nodeActive nd 0 (tr.itemLeaf id) ≠ 0
        · rw [ite_eq_left hc] at h
          have hnl : tr.itemLeaf id ≠ nd := fun he => by
            have := hc.2; rw [he, Function.update_self] at this; exact this rfl
          have hact : tr.nodeActive (tr.itemLeaf id) ≠ 0 := by
            simpa only [Function.update_of_ne hnl] using hc.2
          rw [ite_eq_left ⟨hc.1, hact⟩]; exact h
        · rw [ite_eq_right hc] at h; cases h
      · rw [ite_eq_right hid] at h; cases h

private theorem bufCheckSlot_mono_none {cTab bChar rKey : ℕ} {tr : BufTrie} {id : ℕ}
    (hn : bufCheckSlot tr id = none) :
    bufCheckSlot (bufDelete cTab bChar tr rKey) id = none := by
  cases h' : bufCheckSlot (bufDelete cTab bChar tr rKey) id with
  | none => rfl
  | some p =>
    exact (Option.some_ne_none p ((bufDelete_props.2.2.2.2 id p.1 p.2 h').symm.trans hn)).elim

private theorem bktLane_val_eq {fl : FastEpochLayout} {s : Memory.State} {b lane : ℕ}
    (hpt : fl.ParamTable s.mem) (hb : b < numBucketsWhp fl.N)
    (hlane : lane = 5 ∨ 12 ≤ lane ∧ lane < 16) :
    (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, lane))) =
      if lane = 5 then (extractFastMeta fl s.mem).bktSalt b
      else if lane = 12 then (extractFastMeta fl s.mem).curRole b
      else if lane = 13 then (extractFastMeta fl s.mem).curIns b
      else if lane = 14 then (extractFastMeta fl s.mem).shadowIns b
      else (extractFastMeta fl s.mem).shadowCode b := by
  rw [clientResult_fastReadBktLaneProg hpt hb (by omega)]
  unfold extractFastMeta; dsimp only
  rcases hlane with rfl | ⟨h12, h16⟩
  · simp [hb]
  · rcases (by omega : lane = 12 ∨ lane = 13 ∨ lane = 14 ∨ lane = 15) with rfl | rfl | rfl | rfl
      <;> simp [hb]

private theorem fastDelShadowTryStepProg_spec {fl : FastEpochLayout} {w b role fp delLoc : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s)
    (hb : b < numBucketsWhp fl.N) (hrole : role < 3) (hfp : fp < 2 ^ fpBitsWhp fl.N)
    {shMap : ℕ → Option ℕ}
    (hsh_ok : (extractFastMeta fl s.mem).shadowCode b ≠ 0 →
      (extractFastMeta fl s.mem).shadowIns b ≤ 8 * slabScale fl.N ^ 12 ∧
      ValidWhpSlice fl.N ((extractFastMeta fl s.mem).shadowIns b)
        (extractBTreeSlice fl.btL b (shadowRoleOf role) s.mem) shMap) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s
      (fastDelShadowTryStepProg ((fl.pBase, (b, role)), (fp, delLoc)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastDelShadowTryStepProg ((fl.pBase, (b, role)), (fp, delLoc))) s ≤
      6 * hMaxBTree + 60 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractFastMeta fl s'.mem = fm ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      (b' ≠ b ∨ r ≠ shadowRoleOf role) →
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    (fm.shadowCode b ≠ 0 →
      ValidWhpSlice fl.N (fm.shadowIns b)
        (extractBTreeSlice fl.btL b (shadowRoleOf role) s'.mem)
        (Function.update shMap fp none)) ∧
    (fm.shadowCode b = 0 → s' = s) := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  have hsc_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 15))) =
      fm.shadowCode b := by
    have := bktLane_val_eq hr.2.1 hb (Or.inr ⟨by decide, by decide⟩) (lane := 15)
    simpa only [show (15 = 5) = False from by decide, show (15 = 12) = False from by decide,
      show (15 = 13) = False from by decide, show (15 = 14) = False from by decide,
      Bool.false_eq_true, ite_false] using this
  have hcm15 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 15)) s
  unfold fastDelShadowTryStepProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadBktLaneProg, hsc_r]
  by_cases hcond : fm.shadowCode b ≠ 0
  · rw [ite_eq_left hcond, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_shadowRoleProg, clientResult_shadowRoleProg, memoryCost_shadowRoleProg]
    obtain ⟨hsr_lt, _⟩ := shadowRoleOf_lt_and_ne hrole
    obtain ⟨hins, hv_sh⟩ := hsh_ok hcond
    obtain ⟨hfr, hr', hc, hv', hother, hbp, hfm, hm2, hm0, htr, hoi, hof⟩ :=
      fastBTreeDeleteProg_spec hr hb hsr_lt hins hv_sh hfp
    exact ⟨hfr, hr', by omega, hbp, hfm, hm0, hm2, htr, hoi, hof, hother,
      fun _ => hv', fun h => absurd h hcond⟩
  · rw [ite_eq_right hcond]
    have hc_p : memoryCost (pure () : Memory.Prog Unit) s = 0 := rfl
    refine ⟨rfl, hr, by omega, rfl, rfl, rfl, rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun h1 => absurd h1 hcond, fun _ => rfl⟩

private theorem fastDelTryStepProg_spec {fl : FastEpochLayout} {w b role delLoc : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s : Memory.State} (u : Fin fl.U)
    (hr : FastLayoutReady w fl s)
    (hfp_rep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s.mem)
    (hb : b < numBucketsWhp fl.N) (hrole : role < 3)
    {tryMap : ℕ → Option ℕ}
    (htry_ok : (extractFastMeta fl s.mem).tryAct = 1 → (extractFastMeta fl s.mem).tryBkt = b →
      ∃ _ : (extractFastMeta fl s.mem).trySalt < sMaxWhp fl.c fl.N,
        (extractFastMeta fl s.mem).tryIns ≤ 8 * slabScale fl.N ^ 12 ∧
        ValidWhpSlice fl.N (extractFastMeta fl s.mem).tryIns
          (extractBTreeSlice fl.btL b (tryRoleOf role) s.mem) tryMap) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s
      (fastDelTryStepProg ((fl.pBase, (b, role)), (delLoc, u.val)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastDelTryStepProg ((fl.pBase, (b, role)), (delLoc, u.val))) s ≤
      2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * hMaxBTree + 80 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractFastMeta fl s'.mem = fm ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      (b' ≠ b ∨ r ≠ tryRoleOf role) →
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    (fm.tryAct = 1 → fm.tryBkt = b → delLoc < fm.tryPos →
      ∀ hs : fm.trySalt < sMaxWhp fl.c fl.N,
      ValidWhpSlice fl.N fm.tryIns
        (extractBTreeSlice fl.btL b (tryRoleOf role) s'.mem)
        (Function.update tryMap (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ u).val none)) ∧
    (¬(fm.tryAct = 1 ∧ fm.tryBkt = b ∧ delLoc < fm.tryPos) → s' = s) := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  have hpt := hr.2.1
  have hr6 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 6)) = fm.tryAct :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hr7 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 7)) = fm.tryBkt :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hr9 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 9)) = fm.tryPos :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hr8 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 8)) = fm.trySalt :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hc6 := memoryCost_fastReadMetaProg (fl.pBase, 6) s
  have hc7 := memoryCost_fastReadMetaProg (fl.pBase, 7) s
  have hc9 := memoryCost_fastReadMetaProg (fl.pBase, 9) s
  have hc8 := memoryCost_fastReadMetaProg (fl.pBase, 8) s
  unfold fastDelTryStepProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr6,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr7,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr9]
  by_cases hcond : fm.tryAct = 1 ∧ fm.tryBkt = b ∧ delLoc < fm.tryPos
  · obtain ⟨hs, hins, hv_t⟩ := htry_ok hcond.1 hcond.2.1
    obtain ⟨hfp_r, hfp_c⟩ := fastFpHashProg_spec hr hfp_rep ⟨fm.trySalt, hs⟩ u
    dsimp only at hfp_r hfp_c
    obtain ⟨htr_lt, _⟩ := tryRoleOf_lt_and_ne hrole
    have hfp_lt : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ u).val < 2 ^ fpBitsWhp fl.N :=
      (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ u).isLt
    rw [ite_eq_left hcond,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hr8,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastFpHashProg, hfp_r,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_tryRoleProg, clientResult_tryRoleProg, memoryCost_tryRoleProg]
    obtain ⟨hfr, hr', hc, hv', hother, hbp, hfm, hm2, hm0, htr, hoi, hof⟩ :=
      fastBTreeDeleteProg_spec hr hb htr_lt hins hv_t hfp_lt
    exact ⟨hfr, hr', by omega, hbp, hfm, hm0, hm2, htr, hoi, hof, hother,
      fun _ _ _ hs' => by
        simpa only [show (⟨fm.trySalt, hs'⟩ : Fin (sMaxWhp fl.c fl.N)) = ⟨fm.trySalt, hs⟩
          from rfl] using hv',
      fun h => absurd hcond h⟩
  · rw [ite_eq_right hcond]
    have hc_p : memoryCost (pure () : Memory.Prog Unit) s = 0 := rfl
    refine ⟨rfl, hr, by omega, rfl, rfl, rfl, rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun h1 h2 h3 _ => absurd ⟨h1, h2, h3⟩ hcond, fun _ => rfl⟩

/-- Intermediate 3-tier indexing invariant omitting a single slot `(holeB, holeLoc)` inside
bucket `holeB`, parameterized by the abstract tier maps `mapCur`, `mapOld`, `mapBTree`. -/
private structure TierInvHoleWith (slackCur : ℕ) (fl : FastEpochLayout)
    (seeds : EpochHashSeeds fl.c fl.U fl.N) (mem : ℕ → ℕ)
    (holeB holeLoc : ℕ) (usePopCnt : Bool)
    (mapCur mapOld : ℕ → Option (ℕ × ℕ)) (mapBTree : ℕ → ℕ → Option ℕ) : Prop where
  role_lt : (extractFastMeta fl mem).curBufRole < 2
  subStep_lt : (extractFastMeta fl mem).subStep < qEpochWhp fl.N
  bkt_meta_bounds : ∀ b' < numBucketsWhp fl.N,
    (extractFastMeta fl mem).bktSalt b' < sMaxWhp fl.c fl.N ∧
    (extractFastMeta fl mem).curRole b' < 3 ∧
    (extractFastMeta fl mem).curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
    ((extractFastMeta fl mem).shadowCode b' = 0 →
      ¬((extractFastMeta fl mem).tryAct = 1 ∧ (extractFastMeta fl mem).tryBkt = b') →
      (extractFastMeta fl mem).curIns b' < 6 * slabScale fl.N ^ 12)
  cur_valid : ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N)
    (extractBufTrie (fl.trieL (extractFastMeta fl mem).curBufRole) mem) mapCur
  cur_raw : RawBufTrieBounds (extractBufTrie (fl.trieL (extractFastMeta fl mem).curBufRole) mem)
  cur_clr : RawClearableBounds (extractBufTrie (fl.trieL (extractFastMeta fl mem).curBufRole) mem)
  cur_ia : (extractBufTrie (fl.trieL (extractFastMeta fl mem).curBufRole) mem).itemAlloc ≤
    (extractFastMeta fl mem).subStep + slackCur
  cur_na : (extractBufTrie (fl.trieL (extractFastMeta fl mem).curBufRole) mem).nodeAlloc ≤
    1 + cTabWhp fl.c *
      (extractBufTrie (fl.trieL (extractFastMeta fl mem).curBufRole) mem).itemAlloc
  cur_sound : ∀ rk b' loc', mapCur rk = some (b', loc') →
    b' < numBucketsWhp fl.N ∧ loc' < (extractBlockPool fl.mp mem).bktCount b' ∧
    ¬(b' = holeB ∧ loc' = holeLoc) ∧
    ∃ u' : Fin fl.U, rKeyOf fl.c fl.U fl.N seeds.fp u' = rk ∧
      fastKeyAt fl seeds.bkt mem b' loc' = u'.val
  old_valid_half : (extractFastMeta fl mem).subStep < qEpochWhp fl.N / 2 →
    ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem) mapOld ∧
    RawBufTrieBounds
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem) ∧
    RawClearableBounds
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem) ∧
    (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem).itemAlloc ≤
      qEpochWhp fl.N ∧
    (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem).nodeAlloc ≤
      1 + cTabWhp fl.c * qEpochWhp fl.N ∧
    (extractFastMeta fl mem).drainPos ≤ qEpochWhp fl.N ∧
    (∀ id < min (extractFastMeta fl mem).drainPos
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem).itemAlloc,
      bufCheckSlot
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem) id = none) ∧
    (∀ rk b' loc', mapOld rk = some (b', loc') →
      mapCur rk = none ∧
      b' < numBucketsWhp fl.N ∧ loc' < (extractBlockPool fl.mp mem).bktCount b' ∧
      ¬(b' = holeB ∧ loc' = holeLoc) ∧
      ∃ u' : Fin fl.U, rKeyOf fl.c fl.U fl.N seeds.fp u' = rk ∧
        fastKeyAt fl seeds.bkt mem b' loc' = u'.val)
  old_clear_half : ¬((extractFastMeta fl mem).subStep < qEpochWhp fl.N / 2) →
    mapOld = (fun _ => none) ∧
    (extractFastMeta fl mem).tryAct = 0 ∧
    ClearableBufTrie
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem) ∧
    RawClearableBounds
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem) ∧
    (extractBufTrie (fl.trieL (1 - (extractFastMeta fl mem).curBufRole)) mem).nodeAlloc ≤
      max 1 ((1 + cTabWhp fl.c * qEpochWhp fl.N) -
        4 * (cTabWhp fl.c + 2) * ((extractFastMeta fl mem).subStep - qEpochWhp fl.N / 2))
  bt_valid : ∀ (b' : ℕ), b' < numBucketsWhp fl.N →
    ValidWhpSlice fl.N ((extractFastMeta fl mem).curIns b')
      (extractBTreeSlice fl.btL b' ((extractFastMeta fl mem).curRole b') mem) (mapBTree b')
  bt_sound : ∀ (b' : ℕ) (hb' : b' < numBucketsWhp fl.N) (fp loc' : ℕ),
    mapBTree b' fp = some loc' →
    loc' < (extractBlockPool fl.mp mem).bktCount b' ∧ ¬(b' = holeB ∧ loc' = holeLoc) ∧
    ∃ u' : Fin fl.U,
      (fpHash fl.c fl.U fl.N seeds.fp
        ⟨(extractFastMeta fl mem).bktSalt b', (bkt_meta_bounds b' hb').1⟩ u').val = fp ∧
      fastKeyAt fl seeds.bkt mem b' loc' = u'.val ∧
      (∀ b₁ l₁, mapCur (rKeyOf fl.c fl.U fl.N seeds.fp u') = some (b₁, l₁) →
        fastKeyAt fl seeds.bkt mem b₁ l₁ ≠ u'.val) ∧
      (∀ b₂ l₂, mapOld (rKeyOf fl.c fl.U fl.N seeds.fp u') = some (b₂, l₂) →
        fastKeyAt fl seeds.bkt mem b₂ l₂ ≠ u'.val)
  complete : ∀ (b' : ℕ) (hb' : b' < numBucketsWhp fl.N) (loc' : ℕ),
    loc' < (extractBlockPool fl.mp mem).bktCount b' → ¬(b' = holeB ∧ loc' = holeLoc) →
    ∃ u' : Fin fl.U,
      fastKeyAt fl seeds.bkt mem b' loc' = u'.val ∧
      (mapCur (rKeyOf fl.c fl.U fl.N seeds.fp u') = some (b', loc') ∨
        mapOld (rKeyOf fl.c fl.U fl.N seeds.fp u') = some (b', loc') ∨
        mapBTree b' (fpHash fl.c fl.U fl.N seeds.fp
          ⟨(extractFastMeta fl mem).bktSalt b', (bkt_meta_bounds b' hb').1⟩ u').val = some loc')
  shadow : ∀ b' < numBucketsWhp fl.N, (extractFastMeta fl mem).shadowCode b' ≠ 0 →
    let shPos := (extractFastMeta fl mem).shadowCode b' - 1
    let cnt := (extractBlockPool fl.mp mem).bktCount b'
    let effCnt := if usePopCnt ∧ b' = holeB then cnt - 1 else cnt
    shPos < cnt ∧ ¬((extractFastMeta fl mem).tryAct = 1 ∧ (extractFastMeta fl mem).tryBkt = b') ∧
    4 * (extractFastMeta fl mem).shadowIns b' + 5 * (effCnt - shPos) ≤ 20 * slabScale fl.N ^ 12 ∧
    8 * ((extractFastMeta fl mem).curIns b' - 6 * slabScale fl.N ^ 12) + (effCnt - shPos) ≤
      4 * slabScale fl.N ^ 12 ∧
    ∃ shMap : ℕ → Option ℕ,
      ValidWhpSlice fl.N ((extractFastMeta fl mem).shadowIns b')
        (extractBTreeSlice fl.btL b' (shadowRoleOf ((extractFastMeta fl mem).curRole b')) mem)
        shMap ∧
      (∀ fp, shMap fp =
        match mapBTree b' fp with
        | some loc' => if loc' < shPos then some loc' else none
        | none => none)
  tryAct_le : (extractFastMeta fl mem).tryAct ≤ 1
  try_ok : (extractFastMeta fl mem).tryAct = 1 →
    let fm := extractFastMeta fl mem
    let bt := fm.tryBkt
    let cnt := (extractBlockPool fl.mp mem).bktCount bt
    let effCnt := if usePopCnt ∧ bt = holeB then cnt - 1 else cnt
    fm.subStep < qEpochWhp fl.N / 2 ∧
    ∃ (hb_t : bt < numBucketsWhp fl.N) (hs_t : fm.trySalt < sMaxWhp fl.c fl.N),
      fm.tryPos ≤ cnt ∧ fm.shadowCode bt = 0 ∧
      4 * fm.tryIns + 5 * (effCnt - fm.tryPos) ≤ 20 * slabScale fl.N ^ 12 ∧
      ∃ tryMap : ℕ → Option ℕ,
        ValidWhpSlice fl.N fm.tryIns
          (extractBTreeSlice fl.btL bt (tryRoleOf (fm.curRole bt)) mem) tryMap ∧
        (∀ fp loc', tryMap fp = some loc' →
          loc' < fm.tryPos ∧ ¬(bt = holeB ∧ loc' = holeLoc) ∧
          ∃ u' : Fin fl.U,
            fastKeyAt fl seeds.bkt mem bt loc' = u'.val ∧
            mapBTree bt (fpHash fl.c fl.U fl.N seeds.fp
              ⟨fm.bktSalt bt, (bkt_meta_bounds bt hb_t).1⟩ u').val = some loc' ∧
            (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u').val = fp) ∧
        (∀ loc' < fm.tryPos, ¬(bt = holeB ∧ loc' = holeLoc) → ∀ u' : Fin fl.U,
          fastKeyAt fl seeds.bkt mem bt loc' = u'.val →
          mapBTree bt (fpHash fl.c fl.U fl.N seeds.fp
            ⟨fm.bktSalt bt, (bkt_meta_bounds bt hb_t).1⟩ u').val = some loc' →
          tryMap (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u').val = some loc')

private def TierInvHole (slackCur : ℕ) (fl : FastEpochLayout)
    (seeds : EpochHashSeeds fl.c fl.U fl.N) (mem : ℕ → ℕ)
    (holeB holeLoc : ℕ) (usePopCnt : Bool) : Prop :=
  ∃ mapCur mapOld mapBTree,
    TierInvHoleWith slackCur fl seeds mem holeB holeLoc usePopCnt mapCur mapOld mapBTree

private theorem fastDeleteFromBTreesProg_spec {slackCur : ℕ} {fl : FastEpochLayout}
    {w slack b delLoc : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State} (u : Fin fl.U)
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hdel : delLoc < (extractBlockPool fl.mp s.mem).bktCount b)
    (hk_u : fastKeyAt fl seeds.bkt s.mem b delLoc = u.val)
    (hcur_ne : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s.mem)
      (rKeyOf fl.c fl.U fl.N seeds.fp u) ≠ some (b, delLoc))
    (hold_ne : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2 →
      bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
        (rKeyOf fl.c fl.U fl.N seeds.fp u) ≠ some (b, delLoc)) :
    let fm := extractFastMeta fl s.mem
    let bp := extractBlockPool fl.mp s.mem
    let s' := (Memory.spec 0).clientState s
      (fastDeleteFromBTreesProg ((fl.pBase, (b, delLoc)), u.val))
    s'.frontier = s.frontier ∧ FastLayoutReady w fl s' ∧
    memoryCost (fastDeleteFromBTreesProg ((fl.pBase, (b, delLoc)), u.val)) s ≤
      4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 18 * hMaxBTree + 220 ∧
    extractBlockPool fl.mp s'.mem = bp ∧
    extractFastMeta fl s'.mem = fm ∧
    s'.mem fl.metaBase = fl.N ∧ s'.mem (fl.metaBase + 2) = 0 ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s'.mem).itemAlloc =
      (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem).itemAlloc ∧
    (∀ id b' loc',
      bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s'.mem) id =
        some (b', loc') →
      bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) id =
        some (b', loc')) ∧
    TierInvHole slackCur fl seeds s'.mem b delLoc false := by
  dsimp only
  have hr := hinv.ready hv rfl
  have hpt := hr.2.1
  let fm := extractFastMeta fl s.mem
  let bp := extractBlockPool fl.mp s.mem
  let Q := qEpochWhp fl.N
  have hrole_lt : fm.curBufRole < 2 := hinv.role_lt
  have hold_lt : 1 - fm.curBufRole < 2 := by omega
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, hta_le, htry_all⟩ := hinv.tiers
  have hrk_lt : rKeyOf fl.c fl.U fl.N seeds.fp u < 2 ^ (cTabWhp fl.c * bCharWhp fl.N) :=
    rKeyOf_lt fl.c fl.U fl.N seeds.fp u
  have hmc_ne : mapCur (rKeyOf fl.c fl.U fl.N seeds.fp u) ≠ some (b, delLoc) := by
    rwa [← hv_cur.lookup_eq hrk_lt]
  have hmo_ne : mapOld (rKeyOf fl.c fl.U fl.N seeds.fp u) ≠ some (b, delLoc) := by
    by_cases hsub : fm.subStep < Q / 2
    · have hho := hold_half; rw [ite_eq_left hsub] at hho
      have := hold_ne hsub
      rwa [← hho.1.lookup_eq hrk_lt]
    · have hho := hold_half; rw [ite_eq_right hsub] at hho; rw [hho.1]; simp
  obtain ⟨hs_u, hrl_u, hci_u, _⟩ := hinv.bkt_meta_bounds b hb
  let fp_u := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u).val
  have hfp_lt : fp_u < 2 ^ fpBitsWhp fl.N :=
    (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u).isLt
  have hmb_u : mapBTree b fp_u = some delLoc := by
    obtain ⟨u₀, hk₀, htier⟩ := hcomp b hb delLoc hdel
    have hu₀ : u₀ = u := Fin.ext (hk₀.symm.trans hk_u)
    subst hu₀
    rcases htier with h1 | h2 | h3
    · exact absurd h1 hmc_ne
    · exact absurd h2 hmo_ne
    · exact h3
  have hm11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := hpt 11 (by decide)
  have hs5_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 5))) =
      fm.bktSalt b := by
    have := bktLane_val_eq hpt hb (Or.inl rfl) (lane := 5); simpa using this
  have hs12_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12))) =
      fm.curRole b := by
    have := bktLane_val_eq hpt hb (Or.inr ⟨by decide, by decide⟩) (lane := 12)
    simpa only [show (12 = 5) = False from by decide, ite_true, ite_false] using this
  obtain ⟨hfp_r, hfp_c⟩ := fastFpHashProg_spec hr hinv.seed_fp ⟨fm.bktSalt b, hs_u⟩ u
  dsimp only at hfp_r hfp_c
  have hc5 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 5)) s
  have hc12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s
  unfold fastDeleteFromBTreesProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s from rfl,
    hm11_r, prog_memoryCost_read, ite_eq_left hb,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadBktLaneProg, hs5_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadBktLaneProg, hs12_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastFpHashProg, hfp_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  obtain ⟨hfr1, hr1, hc1, hv1, hoth1, hbp1, hfm1, hm2_1, hm0_1, htr1, hoi1, hof1⟩ :=
    fastBTreeDeleteProg_spec hr hb hrl_u hci_u (hbt_all b hb).1 hfp_lt
  generalize hs1_def : (Memory.spec 0).clientState s
    (fastBTreeDeleteProg ((fl.pBase, (b, fm.curRole b)), fp_u)) = s1
  rw [hs1_def] at hfr1 hr1 hv1 hoth1 hbp1 hfm1 hm2_1 hm0_1 htr1 hoi1 hof1
  have hsr_p := shadowRoleOf_lt_and_ne hrl_u
  have htr_p := tryRoleOf_lt_and_ne hrl_u
  have htr_ne_sh : tryRoleOf (fm.curRole b) ≠ shadowRoleOf (fm.curRole b) := by
    have hlt : fm.curRole b < 3 := hrl_u
    unfold tryRoleOf shadowRoleOf
    rcases (by omega : fm.curRole b = 0 ∨ fm.curRole b = 1 ∨ fm.curRole b = 2) with
      h | h | h <;> simp [h]
  have hsh_ex : fm.shadowCode b ≠ 0 →
      ∃ sm : ℕ → Option ℕ,
        fm.shadowIns b ≤ 8 * slabScale fl.N ^ 12 ∧
        ValidWhpSlice fl.N (fm.shadowIns b)
          (extractBTreeSlice fl.btL b (shadowRoleOf (fm.curRole b)) s.mem) sm ∧
        (∀ fp, sm fp = match mapBTree b fp with
          | some loc' => if loc' < fm.shadowCode b - 1 then some loc' else none
          | none => none) := fun hsc => by
    obtain ⟨_, _, hbd, _, sm, hvs, heq⟩ := hsh_all b hb hsc
    have hbd' : 4 * fm.shadowIns b + 5 * (bp.bktCount b - (fm.shadowCode b - 1)) ≤
        20 * slabScale fl.N ^ 12 := hbd
    exact ⟨sm, by omega, hvs, heq⟩
  classical
  let shMap₀ : ℕ → Option ℕ :=
    if h : fm.shadowCode b ≠ 0 then (hsh_ex h).choose else fun _ => none
  have hsh1_ok : (extractFastMeta fl s1.mem).shadowCode b ≠ 0 →
      (extractFastMeta fl s1.mem).shadowIns b ≤ 8 * slabScale fl.N ^ 12 ∧
      ValidWhpSlice fl.N ((extractFastMeta fl s1.mem).shadowIns b)
        (extractBTreeSlice fl.btL b (shadowRoleOf (fm.curRole b)) s1.mem) shMap₀ := fun hsc => by
    rw [hfm1] at hsc ⊢
    obtain ⟨hins, hvs, _⟩ := (hsh_ex hsc).choose_spec
    refine ⟨hins, ?_⟩
    rw [hoth1 b hb (shadowRoleOf (fm.curRole b)) hsr_p.1 (Or.inr hsr_p.2)]
    dsimp only [shMap₀]; rw [dite_eq_left hsc]; exact hvs
  obtain ⟨hfr2, hr2, hc2, hbp2, hfm2, hm0_2, hm2_2, htr2, hoi2, hof2, hoth2, hv2, _⟩ :=
    fastDelShadowTryStepProg_spec hr1 hb hrl_u hfp_lt hsh1_ok
  generalize hs2_def : (Memory.spec 0).clientState s1
    (fastDelShadowTryStepProg ((fl.pBase, (b, fm.curRole b)), (fp_u, delLoc))) = s2
  rw [hs2_def] at hfr2 hr2 hbp2 hfm2 hm0_2 hm2_2 htr2 hoi2 hof2 hoth2 hv2
  have hof12 : ∀ a, ¬fl.OwnsFastAddr a → s2.mem a = s.mem a :=
    fun a ha => (hof2 a ha).trans (hof1 a ha)
  have hbp12 : extractBlockPool fl.mp s2.mem = bp := hbp2.trans hbp1
  have hoi12 : ∀ a, fl.io.OwnsAddr a → s2.mem a = s.mem a :=
    fun a ha => (hoi2 a ha).trans (hoi1 a ha)
  have hfp_rep2 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s2.mem :=
    (FastEpochInvGen.fixed_pool_core hv hinv hbp12 hoi12 hof12).2.2.1
  have htry_ex : fm.tryAct = 1 ∧ fm.tryBkt = b →
      ∃ (hs : fm.trySalt < sMaxWhp fl.c fl.N) (tm : ℕ → Option ℕ),
        fm.tryIns ≤ 8 * slabScale fl.N ^ 12 ∧
        ValidWhpSlice fl.N fm.tryIns
          (extractBTreeSlice fl.btL b (tryRoleOf (fm.curRole b)) s.mem) tm ∧
        (∀ fp loc', tm fp = some loc' →
          loc' < fm.tryPos ∧ ∃ u' : Fin fl.U,
            fastKeyAt fl seeds.bkt s.mem b loc' = u'.val ∧
            mapBTree b (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val =
              some loc' ∧
            (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ u').val = fp) ∧
        (∀ loc' < fm.tryPos, ∀ u' : Fin fl.U,
          fastKeyAt fl seeds.bkt s.mem b loc' = u'.val →
          mapBTree b (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val =
            some loc' →
          tm (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ u').val = some loc') := fun ht => by
    obtain ⟨_, hb_t, hs_t, _, _, hbd, tm, hvt, h1, h2⟩ := htry_all ht.1
    have hbd' : 4 * fm.tryIns + 5 * (bp.bktCount fm.tryBkt - fm.tryPos) ≤
        20 * slabScale fl.N ^ 12 := hbd
    have hbe : fm.tryBkt = b := ht.2
    refine ⟨hs_t, tm, by omega, ?_, ?_, ?_⟩
    · have := hvt; rw [hbe] at this; exact this
    · intro fp loc' hm
      obtain ⟨hlt, u', hk', hmb', hf'⟩ := h1 fp loc' hm
      refine ⟨hlt, u', hbe ▸ hk', ?_, hf'⟩
      exact (mapBTree_fpHash_congr mapBTree hbe (congrArg fm.bktSalt hbe) u').symm.trans hmb'
    · intro loc' hlt u' hk' hmb'
      exact h2 loc' hlt u' (by rw [hbe]; exact hk')
        ((mapBTree_fpHash_congr mapBTree hbe (congrArg fm.bktSalt hbe) u').trans hmb')
  let tryMap₀ : ℕ → Option ℕ :=
    if h : fm.tryAct = 1 ∧ fm.tryBkt = b then (htry_ex h).choose_spec.choose else fun _ => none
  have htry2_ok : (extractFastMeta fl s2.mem).tryAct = 1 →
      (extractFastMeta fl s2.mem).tryBkt = b →
      ∃ _ : (extractFastMeta fl s2.mem).trySalt < sMaxWhp fl.c fl.N,
        (extractFastMeta fl s2.mem).tryIns ≤ 8 * slabScale fl.N ^ 12 ∧
        ValidWhpSlice fl.N (extractFastMeta fl s2.mem).tryIns
          (extractBTreeSlice fl.btL b (tryRoleOf (fm.curRole b)) s2.mem) tryMap₀ := by
    intro h1 h2; rw [hfm2, hfm1] at h1 h2 ⊢
    have hc : fm.tryAct = 1 ∧ fm.tryBkt = b := ⟨h1, h2⟩
    refine ⟨(htry_ex hc).choose, (htry_ex hc).choose_spec.choose_spec.1, ?_⟩
    rw [hoth2 b hb (tryRoleOf (fm.curRole b)) htr_p.1 (Or.inr htr_ne_sh),
      hoth1 b hb (tryRoleOf (fm.curRole b)) htr_p.1 (Or.inr htr_p.2.1)]
    dsimp only [tryMap₀]; rw [dite_eq_left hc]
    exact (htry_ex hc).choose_spec.choose_spec.2.1
  obtain ⟨hfr3, hr3, hc3', hbp3, hfm3, hm0_3, hm2_3, htr3, hoi3, hof3, hoth3, hv3, hnoop3⟩ :=
    fastDelTryStepProg_spec u hr2 hfp_rep2 hb hrl_u htry2_ok
  generalize hs3_def : (Memory.spec 0).clientState s2
    (fastDelTryStepProg ((fl.pBase, (b, fm.curRole b)), (delLoc, u.val))) = s3
  rw [hs3_def] at hfr3 hr3 hbp3 hfm3 hm0_3 hm2_3 htr3 hoi3 hof3 hoth3 hv3 hnoop3
  have hcost_tot : memoryCost (fastReadBktLaneProg (fl.pBase, (b, 5))) s +
      memoryCost (fastReadBktLaneProg (fl.pBase, (b, 12))) s +
      memoryCost (fastFpHashProg (fl.pBase, (fm.bktSalt b, u.val))) s +
      memoryCost (fastBTreeDeleteProg ((fl.pBase, (b, fm.curRole b)), fp_u)) s +
      memoryCost (fastDelShadowTryStepProg ((fl.pBase, (b, fm.curRole b)), (fp_u, delLoc))) s1 +
      memoryCost (fastDelTryStepProg ((fl.pBase, (b, fm.curRole b)), (delLoc, u.val))) s2 + 1 ≤
      4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 18 * hMaxBTree + 220 := by
    change memoryCost (fastDelShadowTryStepProg ((fl.pBase, (b, fm.curRole b)),
      (fp_u, delLoc))) s1 ≤ 6 * hMaxBTree + 60 at hc2
    change memoryCost (fastDelTryStepProg ((fl.pBase, (b, fm.curRole b)),
      (delLoc, u.val))) s2 ≤
      2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * hMaxBTree + 80 at hc3'
    have hmul : 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
        4 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by ring
    change memoryCost (fastFpHashProg (fl.pBase, (fm.bktSalt b, u.val))) s ≤
      12 + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) at hfp_c
    change memoryCost (fastBTreeDeleteProg ((fl.pBase, (b, fm.curRole b)), fp_u)) s ≤
      6 * hMaxBTree + 50 at hc1
    omega
  have hbp_tot : extractBlockPool fl.mp s3.mem = bp := hbp3.trans (hbp2.trans hbp1)
  have hfm_tot : extractFastMeta fl s3.mem = fm := hfm3.trans (hfm2.trans hfm1)
  have hoi_tot : ∀ a, fl.io.OwnsAddr a → s3.mem a = s.mem a :=
    fun a ha => (hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha))
  have htr_tot : ∀ r < 2, extractBufTrie (fl.trieL r) s3.mem =
      extractBufTrie (fl.trieL r) s.mem := fun r hrr =>
    (htr3 r hrr).trans ((htr2 r hrr).trans (htr1 r hrr))
  have hke : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
      fastKeyAt fl seeds.bkt s3.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
    fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp_tot hoi_tot hb' hl'
  refine ⟨hfr3.trans (hfr2.trans hfr1), hr3, ?_, hbp_tot, hfm_tot,
    (hm0_3.trans (hm0_2.trans hm0_1)).trans hinv.hdr_N,
    (hm2_3.trans (hm2_2.trans hm2_1)).trans hinv.mode_zero,
    hoi_tot, fun a ha => (hof3 a ha).trans (hof12 a ha),
    by rw [htr_tot _ hold_lt],
    fun id b' loc' h => by rwa [htr_tot _ hold_lt] at h,
    mapCur, mapOld, Function.update mapBTree b (Function.update (mapBTree b) fp_u none), ?_⟩
  · linarith only [hcost_tot]
  exact
    { role_lt := by rw [hfm_tot]; exact hrole_lt
      subStep_lt := by rw [hfm_tot]; exact hinv.subStep_lt
      bkt_meta_bounds := fun b' hb' => by rw [hfm_tot]; exact hinv.bkt_meta_bounds b' hb'
      cur_valid := by rw [hfm_tot, htr_tot _ hrole_lt]; exact hv_cur
      cur_raw := by rw [hfm_tot, htr_tot _ hrole_lt]; exact hrb_cur
      cur_clr := by rw [hfm_tot, htr_tot _ hrole_lt]; exact hrc_cur
      cur_ia := by rw [hfm_tot, htr_tot _ hrole_lt]; exact hia_cur
      cur_na := by rw [hfm_tot, htr_tot _ hrole_lt]; exact hna_cur
      cur_sound := fun rk' b' loc' hm => by
        obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk' b' loc' hm
        refine ⟨hb', by rw [hbp_tot]; exact hl', ?_, u', hrk', (hke b' loc' hb' hl').trans hk'⟩
        rintro ⟨hbe, hle⟩
        have hku : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by rwa [hbe, hle] at hk'
        have hu' : u' = u := Fin.ext (hku.symm.trans hk_u)
        exact hmc_ne (by rw [← hu', hrk']; exact hm.trans (by rw [hbe, hle]))
      old_valid_half := fun hsub => by
        rw [hfm_tot] at hsub ⊢; rw [htr_tot _ hold_lt, hbp_tot]
        have hho := hold_half; rw [ite_eq_left hsub] at hho
        obtain ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_o, hclr_o, hold_snd⟩ := hho
        refine ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_o, hclr_o, fun rk' b' loc' hm => ?_⟩
        obtain ⟨hcn, hb', hl', u', hrk', hk'⟩ := hold_snd rk' b' loc' hm
        refine ⟨hcn, hb', hl', ?_, u', hrk', (hke b' loc' hb' hl').trans hk'⟩
        rintro ⟨hbe, hle⟩
        have hku : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by rwa [hbe, hle] at hk'
        have hu' : u' = u := Fin.ext (hku.symm.trans hk_u)
        exact hmo_ne (by rw [← hu', hrk']; exact hm.trans (by rw [hbe, hle]))
      old_clear_half := fun hsub => by
        rw [hfm_tot] at hsub ⊢; rw [htr_tot _ hold_lt]
        have hho := hold_half; rwa [ite_eq_right hsub] at hho
      bt_valid := fun b' hb' => by
        rw [hfm_tot]
        by_cases hbb : b' = b
        · rw [hbb, Function.update_self,
            hoth3 b hb _ hrl_u (Or.inr htr_p.2.1.symm),
            hoth2 b hb _ hrl_u (Or.inr hsr_p.2.symm)]
          exact hv1
        · rw [Function.update_of_ne hbb]
          have hrl' := (hinv.bkt_meta_bounds b' hb').2.1
          rw [hoth3 b' hb' _ hrl' (Or.inl hbb), hoth2 b' hb' _ hrl' (Or.inl hbb),
            hoth1 b' hb' _ hrl' (Or.inl hbb)]
          exact (hbt_all b' hb').1
      bt_sound := fun b' hb' fp' loc' hm => by
        have hbs_eq : (extractFastMeta fl s3.mem).bktSalt b' = fm.bktSalt b' :=
          congrArg (fun m => m.bktSalt b') hfm_tot
        by_cases hbb : b' = b
        · rw [hbb, Function.update_self] at hm
          by_cases hfe : fp' = fp_u
          · rw [hfe, Function.update_self] at hm; cases hm
          · rw [Function.update_of_ne hfe] at hm
            obtain ⟨hl', u', hf', hk', hd1, hd2⟩ := (hbt_all b hb).2 fp' loc' hm
            have hbs_b : (extractFastMeta fl s3.mem).bktSalt b' = fm.bktSalt b :=
              hbs_eq.trans (congrArg fm.bktSalt hbb)
            refine ⟨by rw [hbp_tot, hbb]; exact hl', ?_, u',
              (congrArg Fin.val (fpHash_congr_salt hbs_b u')).trans hf',
              (hke b' loc' hb' (by rwa [hbb])).trans (by simpa only [hbb] using hk'),
              fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
            · rintro ⟨_, hle⟩
              have hku : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by rwa [hle] at hk'
              have hu' : u' = u := Fin.ext (hku.symm.trans hk_u)
              exact hfe (hf'.symm.trans (by rw [hu']))
            · obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
              rw [hke b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁
            · have hsub : fm.subStep < Q / 2 := by
                by_contra hn; have hho := hold_half; rw [ite_eq_right hn] at hho
                rw [hho.1] at hm₂; cases hm₂
              have hho := hold_half; rw [ite_eq_left hsub] at hho
              obtain ⟨_, hb₂, hl₂, _⟩ := hho.2.2.2.2.2.2.2 _ b₂ l₂ hm₂
              rw [hke b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂
        · rw [Function.update_of_ne hbb] at hm
          obtain ⟨hl', u', hf', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
          refine ⟨by rw [hbp_tot]; exact hl', fun h => hbb h.1, u',
            (congrArg Fin.val (fpHash_congr_salt hbs_eq u')).trans hf',
            (hke b' loc' hb' hl').trans hk',
            fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
          · obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
            rw [hke b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁
          · have hsub : fm.subStep < Q / 2 := by
              by_contra hn; have hho := hold_half; rw [ite_eq_right hn] at hho
              rw [hho.1] at hm₂; cases hm₂
            have hho := hold_half; rw [ite_eq_left hsub] at hho
            obtain ⟨_, hb₂, hl₂, _⟩ := hho.2.2.2.2.2.2.2 _ b₂ l₂ hm₂
            rw [hke b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂
      complete := fun b' hb' loc' hl' hne => by
        rw [hbp_tot] at hl'
        obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hl'
        refine ⟨u', (hke b' loc' hb' hl').trans hk', ?_⟩
        rcases ht' with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · refine Or.inr (Or.inr ?_)
          have hbs_eq : (extractFastMeta fl s3.mem).bktSalt b' = fm.bktSalt b' :=
            congrArg (fun m => m.bktSalt b') hfm_tot
          rw [congrArg Fin.val
            (fpHash_congr_salt (h₂ := (hinv.bkt_meta_bounds b' hb').1) hbs_eq u')]
          by_cases hbb : b' = b
          · have h3b : mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
                ⟨fm.bktSalt b, hs_u⟩ u').val = some loc' :=
              (mapBTree_fpHash_congr mapBTree hbb (congrArg fm.bktSalt hbb) u').symm.trans h3
            have hne_fp : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val ≠ fp_u := by
              intro h
              have : some loc' = some delLoc := h3b.symm.trans (by rw [h]; exact hmb_u)
              exact hne ⟨hbb, Option.some.inj this⟩
            have hfp_eq : (fpHash fl.c fl.U fl.N seeds.fp
                ⟨fm.bktSalt b', (hinv.bkt_meta_bounds b' hb').1⟩ u').val =
                (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val :=
              congrArg Fin.val (fpHash_congr_salt (congrArg fm.bktSalt hbb) u')
            rw [hfp_eq, hbb, Function.update_self, Function.update_of_ne hne_fp]; exact h3b
          · rw [Function.update_of_ne hbb]; exact h3
      shadow := fun b' hb' hsc => by
        have hsc0 : fm.shadowCode b' ≠ 0 := by rwa [← hfm_tot]
        obtain ⟨h1, h2, h3, h4, sm, hvs, heq⟩ := hsh_all b' hb' hsc0
        rw [hfm_tot, hbp_tot]
        have h2' : ¬(fm.tryAct = 1 ∧ fm.tryBkt = b') := fun h => by
          have ha : (extractFastMeta fl s.mem).tryAct = 1 := h.1
          have hb2 : (extractFastMeta fl s.mem).tryBkt = b' := h.2
          simp [ha, hb2] at h2
        refine ⟨h1, h2', by simpa using h3, by simpa using h4, ?_⟩
        have hsr' := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
        by_cases hbb : b' = b
        · rw [hbb]
          refine ⟨Function.update shMap₀ fp_u none, ?_, fun fp => ?_⟩
          · rw [hoth3 b hb _ hsr_p.1 (Or.inr htr_ne_sh.symm)]
            have := hv2 (by rw [hfm1]; exact hbb ▸ hsc0)
            rwa [hfm1] at this
          · by_cases hfe : fp = fp_u
            · rw [hfe, Function.update_self, Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hfe, Function.update_self, Function.update_of_ne hfe]
              have hscb : fm.shadowCode b ≠ 0 := hbb ▸ hsc0
              have hspec := (hsh_ex hscb).choose_spec.2.2 fp
              dsimp only [shMap₀]; rw [dite_eq_left hscb]; exact hspec
        · refine ⟨sm, ?_, fun fp => by rw [Function.update_of_ne hbb]; exact heq fp⟩
          rw [hoth3 b' hb' _ hsr' (Or.inl hbb), hoth2 b' hb' _ hsr' (Or.inl hbb),
            hoth1 b' hb' _ hsr' (Or.inl hbb)]
          exact hvs
      tryAct_le := by rw [hfm_tot]; exact hta_le
      try_ok := fun hta1 => by
        have hta0 : fm.tryAct = 1 := by rwa [← hfm_tot]
        obtain ⟨hsub, hb_t, hs_t, htp, hsc, hbd, tm, hvt, htm1, htm2⟩ := htry_all hta0
        have htb_eq : (extractFastMeta fl s3.mem).tryBkt = fm.tryBkt :=
          congrArg FastEpochMeta.tryBkt hfm_tot
        have hts_eq : (extractFastMeta fl s3.mem).trySalt = fm.trySalt :=
          congrArg FastEpochMeta.trySalt hfm_tot
        have htp_eq : (extractFastMeta fl s3.mem).tryPos = fm.tryPos :=
          congrArg FastEpochMeta.tryPos hfm_tot
        have hti_eq : (extractFastMeta fl s3.mem).tryIns = fm.tryIns :=
          congrArg FastEpochMeta.tryIns hfm_tot
        have hcr_eq : (extractFastMeta fl s3.mem).curRole fm.tryBkt = fm.curRole fm.tryBkt :=
          congrArg (fun m => m.curRole fm.tryBkt) hfm_tot
        have hbs_eq : (extractFastMeta fl s3.mem).bktSalt fm.tryBkt = fm.bktSalt fm.tryBkt :=
          congrArg (fun m => m.bktSalt fm.tryBkt) hfm_tot
        dsimp only
        have hbs_fn : ∀ hb' : (extractFastMeta fl s3.mem).tryBkt < numBucketsWhp fl.N,
            (extractFastMeta fl s3.mem).bktSalt (extractFastMeta fl s3.mem).tryBkt =
              fm.bktSalt fm.tryBkt := fun _ => by rw [htb_eq, hbs_eq]
        have hbt_cast : ∀ tm : ℕ → Option ℕ,
            ValidWhpSlice fl.N fm.tryIns
              (extractBTreeSlice fl.btL fm.tryBkt (tryRoleOf (fm.curRole fm.tryBkt)) s3.mem) tm →
            ValidWhpSlice fl.N (extractFastMeta fl s3.mem).tryIns
              (extractBTreeSlice fl.btL (extractFastMeta fl s3.mem).tryBkt
                (tryRoleOf ((extractFastMeta fl s3.mem).curRole
                  (extractFastMeta fl s3.mem).tryBkt)) s3.mem) tm := fun tm h => by
          rwa [htb_eq, hti_eq, hcr_eq]
        refine ⟨by rw [hfm_tot]; exact hsub, by rw [htb_eq]; exact hb_t,
          by rw [hts_eq]; exact hs_t, by rw [hbp_tot, htp_eq, htb_eq]; exact htp,
          by rw [hfm_tot]; exact hsc, by rw [hbp_tot, hfm_tot]; simpa using hbd, ?_⟩
        have htr' := (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds _ hb_t).2.1).1
        by_cases htb : fm.tryBkt = b
        · by_cases hdl_lt : delLoc < fm.tryPos
          · let fpT_u := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u).val
            refine ⟨Function.update tryMap₀ fpT_u none, hbt_cast _ ?_, ?_, ?_⟩
            · have hv3' := hv3 (by rw [hfm2, hfm1]; exact hta0)
                (by rw [hfm2, hfm1]; exact htb) (by rw [hfm2, hfm1]; exact hdl_lt)
                (by rw [hfm2, hfm1]; exact hs_t)
              have hti12 : (extractFastMeta fl s2.mem).tryIns = fm.tryIns :=
                congrArg FastEpochMeta.tryIns (hfm2.trans hfm1)
              have hts12 : (extractFastMeta fl s2.mem).trySalt = fm.trySalt :=
                congrArg FastEpochMeta.trySalt (hfm2.trans hfm1)
              rw [hti12, congrArg Fin.val (fpHash_congr_salt hts12 u)] at hv3'
              rwa [htb]
            · intro fp' loc' hm
              by_cases hfe : fp' = fpT_u
              · rw [hfe, Function.update_self] at hm; cases hm
              · rw [Function.update_of_ne hfe] at hm
                have hc : fm.tryAct = 1 ∧ fm.tryBkt = b := ⟨hta0, htb⟩
                have hm' : (htry_ex hc).choose_spec.choose fp' = some loc' := by
                  dsimp only [tryMap₀] at hm; rwa [dite_eq_left hc] at hm
                obtain ⟨hlt, u', hk', hmb', hf'⟩ :=
                  (htry_ex hc).choose_spec.choose_spec.2.2.1 fp' loc' hm'
                have hlb : loc' < bp.bktCount fm.tryBkt := lt_of_lt_of_le hlt htp
                have hne_l : loc' ≠ delLoc := fun hl => by
                  have hk_eq : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by rwa [hl] at hk'
                  have hu' : u' = u := Fin.ext (hk_eq.symm.trans hk_u)
                  exact hfe (hf'.symm.trans (by rw [hu']))
                have hne_t : ¬((extractFastMeta fl s3.mem).tryBkt = b ∧ loc' = delLoc) :=
                  fun h => hne_l h.2
                have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val ≠
                    fp_u := fun h =>
                  hne_l (Option.some.inj (hmb'.symm.trans (by rw [h]; exact hmb_u)))
                have hmb_upd : Function.update (mapBTree b) fp_u none
                    (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val = some loc' := by
                  rw [Function.update_of_ne hfp_ne]; exact hmb'
                refine ⟨by rw [htp_eq]; exact hlt, hne_t, u',
                  by rw [htb_eq]; exact (hke _ loc' hb_t hlb).trans (by rwa [htb]), ?_,
                  (congrArg Fin.val (fpHash_congr_salt hts_eq u')).trans hf'⟩
                exact (mapBTree_fpHash_congr
                  (Function.update mapBTree b (Function.update (mapBTree b) fp_u none))
                  (htb_eq.trans htb) ((hbs_fn (htb_eq ▸ hb_t)).trans (congrArg fm.bktSalt htb))
                  u').trans (by rw [Function.update_self]; exact hmb_upd)
            · intro loc' hlt hne u' hk' hmb'
              have hlt' : loc' < fm.tryPos := by rwa [htp_eq] at hlt
              have hlb : loc' < bp.bktCount fm.tryBkt := lt_of_lt_of_le hlt' htp
              have hk0 : fastKeyAt fl seeds.bkt s.mem fm.tryBkt loc' = u'.val :=
                (hke _ loc' hb_t hlb).symm.trans (by rwa [htb_eq] at hk')
              have hne_l : loc' ≠ delLoc := fun hl => hne ⟨htb_eq.trans htb, hl⟩
              have hmb_u' : Function.update mapBTree b (Function.update (mapBTree b) fp_u none) b
                  (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val = some loc' :=
                (mapBTree_fpHash_congr
                  (Function.update mapBTree b (Function.update (mapBTree b) fp_u none))
                  (htb_eq.trans htb) ((hbs_fn (htb_eq ▸ hb_t)).trans (congrArg fm.bktSalt htb))
                  u').symm.trans hmb'
              rw [Function.update_self] at hmb_u'
              have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val ≠
                  fp_u := fun h => by rw [h, Function.update_self] at hmb_u'; cases hmb_u'
              rw [Function.update_of_ne hfp_ne] at hmb_u'
              have hc : fm.tryAct = 1 ∧ fm.tryBkt = b := ⟨hta0, htb⟩
              have hk0b : fastKeyAt fl seeds.bkt s.mem b loc' = u'.val := by rwa [htb] at hk0
              have htu := (htry_ex hc).choose_spec.choose_spec.2.2.2 loc' hlt' u' hk0b hmb_u'
              have hfpt_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u').val ≠
                  fpT_u := fun h => by
                have htu_u := (htry_ex hc).choose_spec.choose_spec.2.2.2
                  delLoc hdl_lt u hk_u hmb_u
                have heq : (htry_ex hc).choose_spec.choose
                    (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u').val =
                    (htry_ex hc).choose_spec.choose fpT_u := by rw [h]
                exact hne_l (Option.some.inj (htu.symm.trans (heq.trans htu_u)))
              rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts_eq u'),
                Function.update_of_ne hfpt_ne]
              dsimp only [tryMap₀]; rw [dite_eq_left hc]; exact htu
          · refine ⟨tm, hbt_cast _ ?_, ?_, ?_⟩
            · have hs3_eq : s3 = s2 :=
                hnoop3 (by rw [hfm2, hfm1]; exact fun h => hdl_lt h.2.2)
              have hsl : extractBTreeSlice fl.btL fm.tryBkt (tryRoleOf (fm.curRole fm.tryBkt))
                  s3.mem =
                  extractBTreeSlice fl.btL fm.tryBkt (tryRoleOf (fm.curRole fm.tryBkt)) s.mem := by
                rw [hs3_eq, htb, hoth2 b hb _ htr_p.1 (Or.inr htr_ne_sh),
                  hoth1 b hb _ htr_p.1 (Or.inr htr_p.2.1)]
              rw [hsl]; exact hvt
            · intro fp' loc' hm
              obtain ⟨hlt, u', hk', hmb', hf'⟩ := htm1 fp' loc' hm
              have hlb : loc' < bp.bktCount fm.tryBkt := lt_of_lt_of_le hlt htp
              have hne_l : loc' ≠ delLoc := by
                have h1 : loc' < fm.tryPos := hlt
                have h2 : ¬(delLoc < fm.tryPos) := hdl_lt
                omega
              have hmb_b : mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
                  ⟨fm.bktSalt b, hs_u⟩ u').val = some loc' :=
                (mapBTree_fpHash_congr mapBTree htb (congrArg fm.bktSalt htb) u').symm.trans hmb'
              have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val ≠
                  fp_u := fun h =>
                hne_l (Option.some.inj (hmb_b.symm.trans (by rw [h]; exact hmb_u)))
              have hmb_upd : Function.update (mapBTree b) fp_u none
                  (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val = some loc' := by
                rw [Function.update_of_ne hfp_ne]; exact hmb_b
              refine ⟨by rw [htp_eq]; exact hlt, fun h => hne_l h.2, u',
                by rw [htb_eq]; exact (hke _ loc' hb_t hlb).trans hk', ?_,
                (congrArg Fin.val (fpHash_congr_salt hts_eq u')).trans hf'⟩
              exact (mapBTree_fpHash_congr
                (Function.update mapBTree b (Function.update (mapBTree b) fp_u none))
                (htb_eq.trans htb) ((hbs_fn (htb_eq ▸ hb_t)).trans (congrArg fm.bktSalt htb))
                u').trans (by rw [Function.update_self]; exact hmb_upd)
            · intro loc' hlt _ u' hk' hmb'
              have hlt' : loc' < fm.tryPos := by rwa [htp_eq] at hlt
              have hlb : loc' < bp.bktCount fm.tryBkt := lt_of_lt_of_le hlt' htp
              have hk0 : fastKeyAt fl seeds.bkt s.mem fm.tryBkt loc' = u'.val :=
                (hke _ loc' hb_t hlb).symm.trans (htb_eq ▸ hk')
              have hmb_u' : Function.update mapBTree b (Function.update (mapBTree b) fp_u none) b
                  (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val = some loc' :=
                (mapBTree_fpHash_congr
                  (Function.update mapBTree b (Function.update (mapBTree b) fp_u none))
                  (htb_eq.trans htb) ((hbs_fn (htb_eq ▸ hb_t)).trans (congrArg fm.bktSalt htb))
                  u').symm.trans hmb'
              rw [Function.update_self] at hmb_u'
              have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hs_u⟩ u').val ≠
                  fp_u := fun h => by rw [h, Function.update_self] at hmb_u'; cases hmb_u'
              rw [Function.update_of_ne hfp_ne] at hmb_u'
              rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts_eq u')]
              exact htm2 loc' hlt' u' hk0
                ((mapBTree_fpHash_congr mapBTree htb (congrArg fm.bktSalt htb) u').trans hmb_u')
        · refine ⟨tm, hbt_cast _ ?_, ?_, ?_⟩
          · rw [hoth3 _ hb_t _ htr' (Or.inl htb), hoth2 _ hb_t _ htr' (Or.inl htb),
              hoth1 _ hb_t _ htr' (Or.inl htb)]
            exact hvt
          · intro fp' loc' hm
            obtain ⟨hlt, u', hk', hmb', hf'⟩ := htm1 fp' loc' hm
            have hlb : loc' < bp.bktCount fm.tryBkt := lt_of_lt_of_le hlt htp
            refine ⟨by rw [htp_eq]; exact hlt, fun h => htb (htb_eq.symm.trans h.1), u',
              by rw [htb_eq]; exact (hke _ loc' hb_t hlb).trans hk', ?_,
              (congrArg Fin.val (fpHash_congr_salt hts_eq u')).trans hf'⟩
            exact (mapBTree_fpHash_congr
              (Function.update mapBTree b (Function.update (mapBTree b) fp_u none))
              htb_eq (hbs_fn (htb_eq ▸ hb_t)) u').trans
              (by rw [Function.update_of_ne htb]; exact hmb')
          · intro loc' hlt _ u' hk' hmb'
            have hlt' : loc' < fm.tryPos := by rwa [htp_eq] at hlt
            have hlb : loc' < bp.bktCount fm.tryBkt := lt_of_lt_of_le hlt' htp
            have hmb0 : Function.update mapBTree b (Function.update (mapBTree b) fp_u none)
                fm.tryBkt (fpHash fl.c fl.U fl.N seeds.fp
                  ⟨fm.bktSalt fm.tryBkt, (hinv.bkt_meta_bounds _ hb_t).1⟩ u').val = some loc' :=
              (mapBTree_fpHash_congr
                (Function.update mapBTree b (Function.update (mapBTree b) fp_u none))
                htb_eq (hbs_fn (htb_eq ▸ hb_t)) u').symm.trans hmb'
            rw [Function.update_of_ne htb] at hmb0
            rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts_eq u')]
            exact htm2 loc' hlt' u'
              ((hke _ loc' hb_t hlb).symm.trans (by rwa [htb_eq] at hk')) hmb0 }

private theorem fastUnindexAtProg_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack b delLoc : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (u : Fin fl.U)
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hdel : delLoc < (extractBlockPool fl.mp s.mem).bktCount b)
    (hk_u : fastKeyAt fl seeds.bkt s.mem b delLoc = u.val) :
    let fm := extractFastMeta fl s.mem
    let bp := extractBlockPool fl.mp s.mem
    let s' := (Memory.spec 0).clientState s (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u.val))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u.val)) s ≤
      6 * cTabWhp fl.c + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 18 * hMaxBTree + 280 ∧
    extractBlockPool fl.mp s'.mem = bp ∧
    extractFastMeta fl s'.mem = fm ∧
    s'.mem fl.metaBase = fl.N ∧
    s'.mem (fl.metaBase + 2) = 0 ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s'.mem).itemAlloc =
      (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem).itemAlloc ∧
    (∀ id b' loc',
      bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s'.mem) id = some (b', loc') →
      bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) id = some (b', loc')) ∧
    TierInvHole slackCur fl seeds s'.mem b delLoc false := by
  dsimp only
  have hr := hinv.ready hv rfl
  have hpt := hr.2.1
  let fm := extractFastMeta fl s.mem
  let bp := extractBlockPool fl.mp s.mem
  let Q := qEpochWhp fl.N
  let rk := rKeyOf fl.c fl.U fl.N seeds.fp u
  have hrk_lt : rk < 2 ^ (cTabWhp fl.c * bCharWhp fl.N) :=
    rKeyOf_lt fl.c fl.U fl.N seeds.fp u
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, hta_le, htry_all⟩ := hinv.tiers
  have hrole_lt : fm.curBufRole < 2 := hinv.role_lt
  have hold_lt : 1 - fm.curBufRole < 2 := by omega
  have hcur_spec := fastBufLookupProg_spec hr hrole_lt hv_cur hrk_lt
  obtain ⟨hrk_r, hrk_c⟩ := fastRKeyProg_spec hr hinv.seed_fp u
  have hr3_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 3)) = fm.curBufRole :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hc3 := memoryCost_fastReadMetaProg (fl.pBase, 3) s
  unfold fastUnindexAtProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastRKeyProg, hrk_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr3_r, ite_eq_left hrole_lt,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastBufLookupProg, hcur_spec.1]
  by_cases hcur_hit : mapCur rk = some (b, delLoc)
  · rw [hcur_hit]; dsimp only
    rw [ite_eq_left ⟨rfl, rfl, rfl⟩]
    obtain ⟨hfr, hr', hc_del, hext, hv_c', hbp', hfm', hm2', hm0', hbt', htr_o, hoi, hof⟩ :=
      fastBufDeleteProg_spec hr hrole_lt hv_cur hrk_lt
    generalize hs1_def : (Memory.spec 0).clientState s
      (fastBufDeleteProg ((fl.pBase, fm.curBufRole), rk)) = s1
    rw [hs1_def] at hfr hr' hext hv_c' hbp' hfm' hm2' hm0' hbt' htr_o hoi hof
    have hke : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
        fastKeyAt fl seeds.bkt s1.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
      fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp' hoi hb' hl'
    have ⟨hna_eq, hia_eq, hrb_f, hrc_f, _⟩ :=
      bufDelete_props (cTab := cTabWhp fl.c) (bChar := bCharWhp fl.N) (rKey := rk)
        (tr := extractBufTrie (fl.trieL fm.curBufRole) s.mem)
    have hcost_c : memoryCost (fastBufLookupProg ((fl.pBase, fm.curBufRole),
        rKeyOf fl.c fl.U fl.N seeds.fp u)) s ≤ 2 * cTabWhp fl.c + 18 := hcur_spec.2
    have hcost_d : memoryCost (fastBufDeleteProg ((fl.pBase, fm.curBufRole),
        rKeyOf fl.c fl.U fl.N seeds.fp u)) s ≤ 2 * cTabWhp fl.c + 18 := hc_del
    refine ⟨hfr, hr', by omega, hbp', hfm', hm0'.trans hinv.hdr_N,
      hm2'.trans hinv.mode_zero, hoi, hof, by rw [htr_o],
      fun id b' loc' h => by rwa [htr_o] at h,
      Function.update mapCur rk none, mapOld, mapBTree, ?_⟩
    exact
      { role_lt := by rw [hfm']; exact hrole_lt
        subStep_lt := by rw [hfm']; exact hinv.subStep_lt
        bkt_meta_bounds := fun b' hb' => by rw [hfm']; exact hinv.bkt_meta_bounds b' hb'
        cur_valid := by rw [hfm']; exact hv_c'
        cur_raw := by rw [hfm', hext]; exact hrb_f hrb_cur
        cur_clr := by rw [hfm', hext]; exact hrc_f hrc_cur
        cur_ia := by rw [hfm', hext, hia_eq]; exact hia_cur
        cur_na := by rw [hfm', hext, hna_eq, hia_eq]; exact hna_cur
        cur_sound := fun rk' b' loc' hm => by
          by_cases hrke : rk' = rk
          · subst hrke; rw [Function.update_self] at hm; cases hm
          · rw [Function.update_of_ne hrke] at hm
            obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk' b' loc' hm
            refine ⟨hb', by rw [hbp']; exact hl', ?_, u', hrk', (hke b' loc' hb' hl').trans hk'⟩
            rintro ⟨hbe, hle⟩
            have hku : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by rwa [hbe, hle] at hk'
            have hu' : u' = u := Fin.ext (hku.symm.trans hk_u)
            exact hrke (hrk'.symm.trans (by rw [hu']))
        old_valid_half := fun hsub => by
          rw [hfm'] at hsub ⊢; rw [htr_o, hbp']
          have hho := hold_half; rw [ite_eq_left hsub] at hho
          obtain ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_o, hclr_o, hold_snd⟩ := hho
          refine ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_o, hclr_o, fun rk' b' loc' hm => ?_⟩
          obtain ⟨hcn, hb', hl', u', hrk', hk'⟩ := hold_snd rk' b' loc' hm
          have hrk_ne : rk' ≠ rk := fun h => by subst h; rw [hcur_hit] at hcn; cases hcn
          refine ⟨by rw [Function.update_of_ne hrk_ne]; exact hcn, hb', hl', ?_, u', hrk',
            (hke b' loc' hb' hl').trans hk'⟩
          rintro ⟨hbe, hle⟩
          have hku : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by rwa [hbe, hle] at hk'
          have hu' : u' = u := Fin.ext (hku.symm.trans hk_u)
          exact hrk_ne (hrk'.symm.trans (by rw [hu']))
        old_clear_half := fun hsub => by
          rw [hfm'] at hsub ⊢; rw [htr_o]
          have hho := hold_half; rwa [ite_eq_right hsub] at hho
        bt_valid := fun b' hb' => by
          rw [hfm', hbt' b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1]; exact (hbt_all b' hb').1
        bt_sound := fun b' hb' fp' loc' hm => by
          obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
          have hbs_eq := congrArg (fun m => m.bktSalt b') hfm'
          refine ⟨by rw [hbp']; exact hl', ?_, u',
            (congrArg Fin.val (fpHash_congr_salt hbs_eq u')).trans hfp',
            (hke b' loc' hb' hl').trans hk', fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
          · rintro ⟨hbe, hle⟩
            have hku : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by rwa [hbe, hle] at hk'
            have hu' : u' = u := Fin.ext (hku.symm.trans hk_u)
            exact hd1 b delLoc (by rw [hu']; exact hcur_hit) (by rw [hu']; exact hk_u)
          · by_cases he : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
            · rw [he, Function.update_self] at hm₁; cases hm₁
            · rw [Function.update_of_ne he] at hm₁
              obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
              rw [hke b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁
          · have hsub : fm.subStep < Q / 2 := by
              by_contra hn
              have hho := hold_half; rw [ite_eq_right hn] at hho
              rw [hho.1] at hm₂; cases hm₂
            have hho := hold_half; rw [ite_eq_left hsub] at hho
            obtain ⟨_, hb₂, hl₂, _⟩ := hho.2.2.2.2.2.2.2 _ b₂ l₂ hm₂
            rw [hke b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂
        complete := fun b' hb' loc' hl' hne => by
          rw [hbp'] at hl'
          obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hl'
          refine ⟨u', (hke b' loc' hb' hl').trans hk', ?_⟩
          rcases ht' with h1 | h2 | h3
          · by_cases he : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
            · rw [he, hcur_hit] at h1; cases h1; exact absurd ⟨rfl, rfl⟩ hne
            · exact Or.inl (by rw [Function.update_of_ne he]; exact h1)
          · exact Or.inr (Or.inl h2)
          · have hbs_eq := congrArg (fun m => m.bktSalt b') hfm'
            exact Or.inr (Or.inr
              ((mapBTree_fpHash_congr mapBTree rfl hbs_eq u').trans h3))
        shadow := fun b' hb' hsc => by
          have hsc0 : fm.shadowCode b' ≠ 0 := by rw [hfm'] at hsc; exact hsc
          obtain ⟨h1, h2, h3, h4, sm, hvs, heq⟩ := hsh_all b' hb' hsc0
          rw [hfm', hbp']
          have hsr_lt := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
          exact ⟨h1, fun h => by simp [h.1, h.2] at h2, by simpa using h3, by simpa using h4, sm,
            by rw [hbt' b' hb' _ hsr_lt]; exact hvs, heq⟩
        tryAct_le := by rw [hfm']; exact hta_le
        try_ok := fun hta1 => by
          have hta0 : fm.tryAct = 1 := by rw [hfm'] at hta1; exact hta1
          obtain ⟨hsub, hb_t, hs_t, htp, hsc, hbd, tm, hvt, htm1, htm2⟩ := htry_all hta0
          have htb_eq := congrArg FastEpochMeta.tryBkt hfm'
          have hts_eq := congrArg FastEpochMeta.trySalt hfm'
          have htp_eq := congrArg FastEpochMeta.tryPos hfm'
          have hti_eq := congrArg FastEpochMeta.tryIns hfm'
          have hcr_eq := congrArg (fun m => m.curRole fm.tryBkt) hfm'
          have hbs_eq := congrArg (fun m => m.bktSalt fm.tryBkt) hfm'
          have htr_lt := (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds _ hb_t).2.1).1
          refine ⟨by rw [hfm']; exact hsub, by rw [htb_eq]; exact hb_t,
            by rw [hts_eq]; exact hs_t, by rw [hbp', htp_eq, htb_eq]; exact htp,
            by rw [hfm']; exact hsc, by rw [hbp', hfm']; simpa using hbd, tm, ?_, ?_, ?_⟩
          · rw [htb_eq, hti_eq, hcr_eq, hbt' _ hb_t _ htr_lt]; exact hvt
          · intro fp' loc' hm
            obtain ⟨hlt, u', hk', hmb, hfp'⟩ := htm1 fp' loc' hm
            have hlb : loc' < bp.bktCount fm.tryBkt := lt_of_lt_of_le hlt htp
            refine ⟨by rw [htp_eq]; exact hlt, ?_, u',
              by rw [htb_eq]; exact (hke _ loc' hb_t hlb).trans hk',
              (mapBTree_fpHash_congr mapBTree htb_eq (by rw [htb_eq, hbs_eq]) u').trans hmb,
              (congrArg Fin.val (fpHash_congr_salt hts_eq u')).trans hfp'⟩
            rintro ⟨hbt_eq, hle⟩
            have hbt0 : fm.tryBkt = b := htb_eq.symm.trans hbt_eq
            have hmb' : mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
                ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ u').val = some delLoc := by
              rw [← hle]
              exact (mapBTree_fpHash_congr mapBTree hbt0 (congrArg fm.bktSalt hbt0) u').symm.trans
                hmb
            have hk'' : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by
              rwa [hbt0, hle] at hk'
            obtain ⟨_, u'', _, hk_u'', hd1, _⟩ := (hbt_all b hb).2 _ _ hmb'
            have hu'' : u'' = u := Fin.ext (hk_u''.symm.trans hk_u)
            exact hd1 b delLoc (by rw [hu'']; exact hcur_hit) (by rw [hu'']; exact hk_u)
          · intro loc' hlt _ u' hk' hmb
            have hlt' : loc' < fm.tryPos := by rwa [htp_eq] at hlt
            have hlb : loc' < bp.bktCount fm.tryBkt := lt_of_lt_of_le hlt' htp
            rw [congrArg Fin.val (fpHash_congr_salt hts_eq u')]
            exact htm2 loc' hlt' u'
              ((hke _ loc' hb_t hlb).symm.trans (by rwa [htb_eq] at hk'))
              ((mapBTree_fpHash_congr mapBTree htb_eq (by rw [htb_eq, hbs_eq]) u').symm.trans
                hmb) }
  · split_ifs with hcur_cond
    · exfalso
      cases hc : mapCur rk with
      | none => rw [hc] at hcur_cond; exact absurd hcur_cond.1 (by decide)
      | some p =>
        rw [hc] at hcur_cond
        exact hcur_hit (hc.trans (congrArg some (Prod.ext hcur_cond.2.1 hcur_cond.2.2)))
    have hr4_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 4)) = fm.subStep :=
      clientResult_fastReadMetaProg hpt (by decide)
    have hc4 := memoryCost_fastReadMetaProg (fl.pBase, 4) s
    have hr23_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s := rfl
    have hr23_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 23)) = Q :=
      hpt 23 (by decide)
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hr4_r,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      hr23_st, hr23_r, prog_memoryCost_read]
    by_cases hsub : fm.subStep < Q / 2
    · rw [ite_eq_left hsub, pure_bind]
      have hho := hold_half; rw [ite_eq_left hsub] at hho
      obtain ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_o, hclr_o, hold_snd⟩ := hho
      have hold_spec := fastBufLookupProg_spec hr hold_lt hv_o hrk_lt
      rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastBufLookupProg, hold_spec.1]
      by_cases ho_hit : mapOld rk = some (b, delLoc)
      · rw [ho_hit]; dsimp only; rw [ite_eq_left ⟨rfl, rfl, rfl⟩]
        obtain ⟨hfr, hr', hc_del, hext, hv_o', hbp', hfm', hm2', hm0', hbt', htr_c, hoi, hof⟩ :=
          fastBufDeleteProg_spec hr hold_lt hv_o hrk_lt
        generalize hs1_def : (Memory.spec 0).clientState s
          (fastBufDeleteProg ((fl.pBase, 1 - fm.curBufRole), rk)) = s1
        rw [hs1_def] at hfr hr' hext hv_o' hbp' hfm' hm2' hm0' hbt' htr_c hoi hof
        have hc_role : 1 - (1 - fm.curBufRole) = fm.curBufRole := by omega
        rw [hc_role] at htr_c
        have hke : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
            fastKeyAt fl seeds.bkt s1.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
          fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp' hoi hb' hl'
        have ⟨hna_eq, hia_eq, hrb_f, hrc_f, hchk_mono⟩ :=
          bufDelete_props (cTab := cTabWhp fl.c) (bChar := bCharWhp fl.N) (rKey := rk)
            (tr := extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem)
        have hcost_c : memoryCost (fastBufLookupProg ((fl.pBase, fm.curBufRole),
            rKeyOf fl.c fl.U fl.N seeds.fp u)) s ≤ 2 * cTabWhp fl.c + 18 := hcur_spec.2
        have hcost_o : memoryCost (fastBufLookupProg ((fl.pBase, 1 - fm.curBufRole),
            rKeyOf fl.c fl.U fl.N seeds.fp u)) s ≤ 2 * cTabWhp fl.c + 18 := hold_spec.2
        have hcost_d : memoryCost (fastBufDeleteProg ((fl.pBase, 1 - fm.curBufRole),
            rKeyOf fl.c fl.U fl.N seeds.fp u)) s ≤ 2 * cTabWhp fl.c + 18 := hc_del
        refine ⟨hfr, hr', by omega,
          hbp', hfm', hm0'.trans hinv.hdr_N, hm2'.trans hinv.mode_zero, hoi, hof,
          by rw [hext, hia_eq],
          fun id b' loc' h => hchk_mono id b' loc' (by rwa [hext] at h),
          mapCur, Function.update mapOld rk none, mapBTree, ?_⟩
        exact
          { role_lt := by rw [hfm']; exact hrole_lt
            subStep_lt := by rw [hfm']; exact hinv.subStep_lt
            bkt_meta_bounds := fun b' hb' => by rw [hfm']; exact hinv.bkt_meta_bounds b' hb'
            cur_valid := by rw [hfm', htr_c]; exact hv_cur
            cur_raw := by rw [hfm', htr_c]; exact hrb_cur
            cur_clr := by rw [hfm', htr_c]; exact hrc_cur
            cur_ia := by rw [hfm', htr_c]; exact hia_cur
            cur_na := by rw [hfm', htr_c]; exact hna_cur
            cur_sound := fun rk' b' loc' hm => by
              obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk' b' loc' hm
              refine ⟨hb', by rw [hbp']; exact hl', ?_, u', hrk', (hke b' loc' hb' hl').trans hk'⟩
              rintro ⟨hbe, hle⟩
              have hku : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by rwa [hbe, hle] at hk'
              have hu' : u' = u := Fin.ext (hku.symm.trans hk_u)
              exact hcur_hit (by rw [show rk = rk' from (by rw [← hrk', hu']), hm, hbe, hle])
            old_valid_half := fun _ => by
              rw [hfm', hbp']
              refine ⟨hv_o', hext ▸ hrb_f hrb_o, hext ▸ hrc_f hrc_o,
                by rw [hext, hia_eq]; exact hia_o, by rw [hext, hna_eq]; exact hna_o, hdp_o,
                fun id hid => by
                  rw [hext, hia_eq] at hid; rw [hext]
                  exact bufCheckSlot_mono_none (hclr_o id hid),
                fun rk' b' loc' hm => by
                  by_cases hrke : rk' = rk
                  · subst hrke; rw [Function.update_self] at hm; cases hm
                  · rw [Function.update_of_ne hrke] at hm
                    obtain ⟨hcn, hb', hl', u', hrk', hk'⟩ := hold_snd rk' b' loc' hm
                    refine ⟨hcn, hb', hl', ?_, u', hrk', (hke b' loc' hb' hl').trans hk'⟩
                    rintro ⟨hbe, hle⟩
                    have hku : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by
                      rwa [hbe, hle] at hk'
                    have hu' : u' = u := Fin.ext (hku.symm.trans hk_u)
                    exact hrke (hrk'.symm.trans (by rw [hu']))⟩
            old_clear_half := fun hn => absurd (by rw [hfm']; exact hsub) hn
            bt_valid := fun b' hb' => by
              rw [hfm', hbt' b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1]
              exact (hbt_all b' hb').1
            bt_sound := fun b' hb' fp' loc' hm => by
              obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
              have hbs_eq := congrArg (fun m => m.bktSalt b') hfm'
              refine ⟨by rw [hbp']; exact hl', ?_, u',
                (congrArg Fin.val (fpHash_congr_salt hbs_eq u')).trans hfp',
                (hke b' loc' hb' hl').trans hk', fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
              · rintro ⟨hbe, hle⟩
                have hku : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by
                  rwa [hbe, hle] at hk'
                have hu' : u' = u := Fin.ext (hku.symm.trans hk_u)
                exact hd2 b delLoc (by rw [hu']; exact ho_hit) (by rw [hu']; exact hk_u)
              · obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
                rw [hke b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁
              · by_cases he : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
                · rw [he, Function.update_self] at hm₂; cases hm₂
                · rw [Function.update_of_ne he] at hm₂
                  obtain ⟨_, hb₂, hl₂, _⟩ := hold_snd _ b₂ l₂ hm₂
                  rw [hke b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂
            complete := fun b' hb' loc' hl' hne => by
              rw [hbp'] at hl'
              obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hl'
              refine ⟨u', (hke b' loc' hb' hl').trans hk', ?_⟩
              rcases ht' with h1 | h2 | h3
              · exact Or.inl h1
              · by_cases he : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
                · rw [he, ho_hit] at h2; cases h2; exact absurd ⟨rfl, rfl⟩ hne
                · exact Or.inr (Or.inl (by rw [Function.update_of_ne he]; exact h2))
              · have hbs_eq := congrArg (fun m => m.bktSalt b') hfm'
                exact Or.inr (Or.inr
                  ((mapBTree_fpHash_congr mapBTree rfl hbs_eq u').trans h3))
            shadow := fun b' hb' hsc => by
              have hsc0 : fm.shadowCode b' ≠ 0 := by rw [hfm'] at hsc; exact hsc
              obtain ⟨h1, h2, h3, h4, sm, hvs, heq⟩ := hsh_all b' hb' hsc0
              rw [hfm', hbp']
              have hsr_lt := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
              exact ⟨h1, fun h => by simp [h.1, h.2] at h2, by simpa using h3,
                by simpa using h4, sm, by rw [hbt' b' hb' _ hsr_lt]; exact hvs, heq⟩
            tryAct_le := by rw [hfm']; exact hta_le
            try_ok := fun hta1 => by
              have hta0 : fm.tryAct = 1 := by rw [hfm'] at hta1; exact hta1
              obtain ⟨hsub', hb_t, hs_t, htp, hsc, hbd, tm, hvt, htm1, htm2⟩ := htry_all hta0
              have htb_eq := congrArg FastEpochMeta.tryBkt hfm'
              have hts_eq := congrArg FastEpochMeta.trySalt hfm'
              have htp_eq := congrArg FastEpochMeta.tryPos hfm'
              have hti_eq := congrArg FastEpochMeta.tryIns hfm'
              have hcr_eq := congrArg (fun m => m.curRole fm.tryBkt) hfm'
              have hbs_eq := congrArg (fun m => m.bktSalt fm.tryBkt) hfm'
              have htr_lt := (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds _ hb_t).2.1).1
              refine ⟨by rw [hfm']; exact hsub', by rw [htb_eq]; exact hb_t,
                by rw [hts_eq]; exact hs_t, by rw [hbp', htp_eq, htb_eq]; exact htp,
                by rw [hfm']; exact hsc, by rw [hbp', hfm']; simpa using hbd, tm, ?_, ?_, ?_⟩
              · rw [htb_eq, hti_eq, hcr_eq, hbt' _ hb_t _ htr_lt]; exact hvt
              · intro fp' loc' hm
                obtain ⟨hlt, u', hk', hmb, hfp'⟩ := htm1 fp' loc' hm
                have hlb : loc' < bp.bktCount fm.tryBkt := lt_of_lt_of_le hlt htp
                refine ⟨by rw [htp_eq]; exact hlt, ?_, u',
                  by rw [htb_eq]; exact (hke _ loc' hb_t hlb).trans hk',
                  (mapBTree_fpHash_congr mapBTree htb_eq (by rw [htb_eq, hbs_eq]) u').trans hmb,
                  (congrArg Fin.val (fpHash_congr_salt hts_eq u')).trans hfp'⟩
                rintro ⟨hbt_eq, hle⟩
                have hbt0 : fm.tryBkt = b := htb_eq.symm.trans hbt_eq
                have hmb' : mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
                    ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ u').val = some delLoc := by
                  rw [← hle]
                  exact (mapBTree_fpHash_congr mapBTree hbt0
                    (congrArg fm.bktSalt hbt0) u').symm.trans hmb
                have hk'' : fastKeyAt fl seeds.bkt s.mem b delLoc = u'.val := by
                  rwa [hbt0, hle] at hk'
                obtain ⟨_, u'', _, hk_u'', _, hd2⟩ := (hbt_all b hb).2 _ _ hmb'
                have hu'' : u'' = u := Fin.ext (hk_u''.symm.trans hk_u)
                exact hd2 b delLoc (by rw [hu'']; exact ho_hit) (by rw [hu'']; exact hk_u)
              · intro loc' hlt _ u' hk' hmb
                have hlt' : loc' < fm.tryPos := by rwa [htp_eq] at hlt
                have hlb : loc' < bp.bktCount fm.tryBkt := lt_of_lt_of_le hlt' htp
                rw [congrArg Fin.val (fpHash_congr_salt hts_eq u')]
                exact htm2 loc' hlt' u'
                  ((hke _ loc' hb_t hlb).symm.trans (by rwa [htb_eq] at hk'))
                  ((mapBTree_fpHash_congr mapBTree htb_eq
                    (by rw [htb_eq, hbs_eq]) u').symm.trans hmb) }
      · split_ifs with hold_cond
        · exfalso
          cases ho : mapOld rk with
          | none => rw [ho] at hold_cond; exact absurd hold_cond.1 (by decide)
          | some p =>
            rw [ho] at hold_cond
            exact ho_hit (ho.trans (congrArg some (Prod.ext hold_cond.2.1 hold_cond.2.2)))
        have hc_ne : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
            (extractBufTrie (fl.trieL fm.curBufRole) s.mem) rk ≠ some (b, delLoc) := by
          rw [hv_cur.lookup_eq hrk_lt]; exact hcur_hit
        have ho_ne : fm.subStep < Q / 2 → bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
            (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) rk ≠ some (b, delLoc) :=
          fun _ => by rw [hv_o.lookup_eq hrk_lt]; exact ho_hit
        have ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
          fastDeleteFromBTreesProg_spec u hv hinv hb hdel hk_u hc_ne ho_ne
        have hcost_c : memoryCost (fastBufLookupProg ((fl.pBase, fm.curBufRole),
            rKeyOf fl.c fl.U fl.N seeds.fp u)) s ≤ 2 * cTabWhp fl.c + 18 := hcur_spec.2
        have hcost_o : memoryCost (fastBufLookupProg ((fl.pBase, 1 - fm.curBufRole),
            rKeyOf fl.c fl.U fl.N seeds.fp u)) s ≤ 2 * cTabWhp fl.c + 18 := hold_spec.2
        exact ⟨h1, h2, by omega, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    · rw [ite_eq_right hsub]
      have hc_ne : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
          (extractBufTrie (fl.trieL fm.curBufRole) s.mem) rk ≠ some (b, delLoc) := by
        rw [hv_cur.lookup_eq hrk_lt]; exact hcur_hit
      have ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
        fastDeleteFromBTreesProg_spec u hv hinv hb hdel hk_u hc_ne
          (fun h => absurd h hsub)
      have hcost_c : memoryCost (fastBufLookupProg ((fl.pBase, fm.curBufRole),
          rKeyOf fl.c fl.U fl.N seeds.fp u)) s ≤ 2 * cTabWhp fl.c + 18 := hcur_spec.2
      exact ⟨h1, h2, by omega, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-! ### Relocation Subprogram Specifications -/

private theorem fastRelocShadowStepProg_spec {fl : FastEpochLayout} {w b role fp delLoc : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s)
    (hb : b < numBucketsWhp fl.N) (hrole : role < 3)
    (hfp : fp < 2 ^ fpBitsWhp fl.N) (hdel_val : delLoc < 2 ^ valLaneBitsWhp fl.N)
    {shMap : ℕ → Option ℕ}
    (hsh_ok : (extractFastMeta fl s.mem).shadowCode b ≠ 0 →
      (extractFastMeta fl s.mem).shadowIns b < 5 * slabScale fl.N ^ 12 ∧
      ValidWhpSlice fl.N ((extractFastMeta fl s.mem).shadowIns b)
        (extractBTreeSlice fl.btL b (shadowRoleOf role) s.mem) shMap) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s
      (fastRelocShadowStepProg ((fl.pBase, (b, role)), (fp, delLoc)))
    let act := fm.shadowCode b ≠ 0 ∧ delLoc < fm.shadowCode b - 1
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastRelocShadowStepProg ((fl.pBase, (b, role)), (fp, delLoc))) s ≤
      72 * hMaxBTree + 150 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3, (b' ≠ b ∨ r ≠ shadowRoleOf role) →
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    (act →
      extractFastMeta fl s'.mem =
        { fm with shadowIns := Function.update fm.shadowIns b (fm.shadowIns b + 1) } ∧
      ValidWhpSlice fl.N (fm.shadowIns b + 1)
        (extractBTreeSlice fl.btL b (shadowRoleOf role) s'.mem)
        (Function.update shMap fp (some delLoc))) ∧
    (¬act → s' = s) := by
  dsimp only
  let fm := extractFastMeta fl s.mem
  have hpt := hr.2.1
  have hm0 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N :=
    hpt 0 (by decide)
  have hsc_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 15))) =
      fm.shadowCode b := by
    have := bktLane_val_eq hpt hb (Or.inr ⟨by decide, by decide⟩) (lane := 15)
    simpa only [show (15 = 5) = False from by decide, show (15 = 12) = False from by decide,
      show (15 = 13) = False from by decide, show (15 = 14) = False from by decide,
      Bool.false_eq_true, ite_false] using this
  have hcm15 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 15)) s
  unfold fastRelocShadowStepProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadBktLaneProg, hsc_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s from rfl,
    hm0, prog_memoryCost_read]
  by_cases hcond : fm.shadowCode b ≠ 0 ∧ delLoc < fm.shadowCode b - 1
  · rw [ite_eq_left hcond,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_shadowRoleProg, clientResult_shadowRoleProg, memoryCost_shadowRoleProg,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
    obtain ⟨hsr_lt, _⟩ := shadowRoleOf_lt_and_ne hrole
    obtain ⟨hsi_lt, hv_sh⟩ := hsh_ok hcond.1
    have hsi_le8 : (extractFastMeta fl s.mem).shadowIns b ≤ 8 * slabScale fl.N ^ 12 := by omega
    obtain ⟨hfr1, hr1, hc1, hv1, hoth1, hbp1, hfm1, hm2_1, hm0_1, htr1, hoi1, hof1⟩ :=
      fastBTreeInsertProg_spec hr hb hsr_lt hsi_le8 hv_sh hfp hdel_val
    generalize hs1_def : (Memory.spec 0).clientState s
      (fastBTreeInsertProg ((fl.pBase, (b, shadowRoleOf role)), (fp, delLoc))) = s1
    rw [hs1_def] at hfr1 hr1 hv1 hoth1 hbp1 hfm1 hm2_1 hm0_1 htr1 hoi1 hof1
    have h64 := hr.1.bounds_le_N.1
    have hsi_lt_N : (extractFastMeta fl s.mem).shadowIns b < fl.N := by omega
    have h14_r : (Memory.spec 0).clientResult s1 (fastReadBktLaneProg (fl.pBase, (b, 14))) =
        (extractFastMeta fl s.mem).shadowIns b := by
      have := bktLane_val_eq hr1.2.1 hb (Or.inr ⟨by decide, by decide⟩) (lane := 14)
      rw [hfm1] at this
      simpa only [show (14 = 5) = False from by decide, show (14 = 12) = False from by decide,
        show (14 = 13) = False from by decide, ite_true, ite_false] using this
    have hc14 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 14)) s1
    have hcw14 := memoryCost_fastWriteBktLaneProg
      ((fl.pBase, (b, 14)), (extractFastMeta fl s.mem).shadowIns b + 1) s1
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadBktLaneProg, h14_r, ite_eq_left hsi_lt_N]
    obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hof2, hoi2⟩ := fastWriteBktLaneProg_frame
      (b := b) (lane := 14) (val := (extractFastMeta fl s.mem).shadowIns b + 1) hr1
    obtain ⟨hm2_2, hfm2⟩ := extractFastMeta_writeBktLane hr1 hb
      (lane := 14) (Or.inr ⟨by decide, by decide⟩)
      (val := (extractFastMeta fl s.mem).shadowIns b + 1) (by omega)
    have hm0_2 : ((Memory.spec 0).clientState s1
        (fastWriteBktLaneProg ((fl.pBase, (b, 14)),
          (extractFastMeta fl s.mem).shadowIns b + 1))).mem
        fl.metaBase = s1.mem fl.metaBase :=
      hof2 fl.metaBase hr1.1.not_ownsFast_hdr0
    rw [hfm1] at hfm2
    rw [ite_eq_right (by decide : (14 : ℕ) ≠ 5), ite_eq_right (by decide : (14 : ℕ) ≠ 12),
      ite_eq_right (by decide : (14 : ℕ) ≠ 13), ite_eq_left rfl] at hfm2
    have hbt_s : extractBTreeSlice fl.btL b (shadowRoleOf role)
        ((Memory.spec 0).clientState s1 (fastWriteBktLaneProg
          ((fl.pBase, (b, 14)), (extractFastMeta fl s.mem).shadowIns b + 1))).mem =
        extractBTreeSlice fl.btL b (shadowRoleOf role) s1.mem := hbt2 b hb _ hsr_lt
    refine ⟨hfr2.trans hfr1, hr2, by omega, hbp2.trans hbp1, hm0_2.trans hm0_1,
      hm2_2.trans hm2_1, fun r hrr => (htr2 r hrr).trans (htr1 r hrr),
      fun a ha => (hoi2 a ha).trans (hoi1 a ha),
      fun a ha => (hof2 a ha).trans (hof1 a ha),
      fun b' hb' r hrr hne => (hbt2 b' hb' r hrr).trans (hoth1 b' hb' r hrr hne),
      fun _ => ⟨hfm2, by rw [hbt_s]; exact hv1⟩, fun h => absurd hcond h⟩
  · rw [ite_eq_right hcond]
    have hcp : memoryCost (pure () : Memory.Prog Unit) s = 0 := rfl
    refine ⟨rfl, hr, by omega, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ _ _ _ => rfl, fun h => absurd h hcond, fun _ => rfl⟩

private theorem fastRelocTryInsProg_spec {fl : FastEpochLayout} {w b role fpT delLoc : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s)
    (hb : b < numBucketsWhp fl.N) (hrole : role < 3)
    (htb : (extractFastMeta fl s.mem).tryBkt = b)
    (hcr : (extractFastMeta fl s.mem).curRole b = role)
    (hfp : fpT < 2 ^ fpBitsWhp fl.N) (hdel_val : delLoc < 2 ^ valLaneBitsWhp fl.N)
    {tryMap : ℕ → Option ℕ}
    (hti_lt : (extractFastMeta fl s.mem).tryIns < 5 * slabScale fl.N ^ 12)
    (hvt : ValidWhpSlice fl.N (extractFastMeta fl s.mem).tryIns
      (extractBTreeSlice fl.btL b (tryRoleOf role) s.mem) tryMap) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s
      (fastRelocTryInsProg ((fl.pBase, (b, tryRoleOf role)), (fpT, delLoc)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastRelocTryInsProg ((fl.pBase, (b, tryRoleOf role)), (fpT, delLoc))) s ≤
      78 * hMaxBTree + 170 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3, (b' ≠ b ∨ r ≠ tryRoleOf role) →
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    ((tryMap fpT = none ∧
        extractFastMeta fl s'.mem = { fm with tryIns := fm.tryIns + 1 } ∧
        ValidWhpSlice fl.N (fm.tryIns + 1)
          (extractBTreeSlice fl.btL b (tryRoleOf role) s'.mem)
          (Function.update tryMap fpT (some delLoc))) ∨
      (∃ wLoc, tryMap fpT = some wLoc ∧
        extractFastMeta fl s'.mem =
          { fm with
            trySalt := if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0
            tryPos := 0
            tryIns := 0 } ∧
        ValidWhpSlice fl.N 0
          (extractBTreeSlice fl.btL b (tryRoleOf role) s'.mem) (fun _ => none))) := by
  dsimp only
  obtain ⟨htr_lt, _⟩ := tryRoleOf_lt_and_ne hrole
  have hti_le8 : (extractFastMeta fl s.mem).tryIns ≤ 8 * slabScale fl.N ^ 12 := by omega
  obtain ⟨hlk_r, hlk_c⟩ := fastBTreeLookupProg_spec hr hb htr_lt hti_le8 hvt hfp
  unfold fastRelocTryInsProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastBTreeLookupProg, hlk_r]
  cases hhit : tryMap fpT with
  | some wLoc =>
    dsimp only; rw [ite_eq_left rfl]
    obtain ⟨hfr, hr', hc, hbp, htr, hoi, hof, hm2, hspec⟩ := advanceTrySaltProg_frame hr
    have hm0 : ((Memory.spec 0).clientState s (advanceTrySaltProg fl.pBase)).mem fl.metaBase =
        s.mem fl.metaBase := hof fl.metaBase hr.1.not_ownsFast_hdr0
    obtain ⟨hfm', hv_z, hoth⟩ := hspec (by rw [htb]; exact hb)
    rw [htb, hcr] at hv_z hoth
    refine ⟨hfr, hr', by omega, hbp, hm0, hm2, htr, hoi, hof, hoth,
      Or.inr ⟨wLoc, rfl, hfm', hv_z⟩⟩
  | none =>
    dsimp only; rw [ite_eq_right (by decide : (0 : ℕ) ≠ 1)]
    have hm0_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N :=
      hr.2.1 0 (by decide)
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s from rfl,
      hm0_r, prog_memoryCost_read,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
    obtain ⟨hfr1, hr1, hc1, hv1, hoth1, hbp1, hfm1, hm2_1, hm0_1, htr1, hoi1, hof1⟩ :=
      fastBTreeInsertProg_spec hr hb htr_lt hti_le8 hvt hfp hdel_val
    generalize hs1_def : (Memory.spec 0).clientState s
      (fastBTreeInsertProg ((fl.pBase, (b, tryRoleOf role)), (fpT, delLoc))) = s1
    rw [hs1_def] at hfr1 hr1 hv1 hoth1 hbp1 hfm1 hm2_1 hm0_1 htr1 hoi1 hof1
    have h64 := hr.1.bounds_le_N.1
    have hti_lt_N : (extractFastMeta fl s.mem).tryIns < fl.N := by omega
    have hr17_r : (Memory.spec 0).clientResult s1 (fastReadMetaProg (fl.pBase, 17)) =
        (extractFastMeta fl s.mem).tryIns := by
      have := clientResult_fastReadMetaProg (off := 17) hr1.2.1 (by decide)
      change (Memory.spec 0).clientResult s1 (fastReadMetaProg (fl.pBase, 17)) =
        (extractFastMeta fl s1.mem).tryIns at this
      rwa [hfm1] at this
    have hc17 := memoryCost_fastReadMetaProg (fl.pBase, 17) s1
    have hcw17 := memoryCost_fastWriteMetaProg
      ((fl.pBase, 17), (extractFastMeta fl s.mem).tryIns + 1) s1
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hr17_r, ite_eq_left hti_lt_N]
    obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hoi2, hof2, hm2_2, hfm2⟩ :=
      extractFastMeta_writeMeta (off := 17) (val := (extractFastMeta fl s.mem).tryIns + 1)
        hr1 (Or.inr rfl)
    have hm0_2 : ((Memory.spec 0).clientState s1
        (fastWriteMetaProg ((fl.pBase, 17), (extractFastMeta fl s.mem).tryIns + 1))).mem
        fl.metaBase = s1.mem fl.metaBase := hof2 fl.metaBase hr1.1.not_ownsFast_hdr0
    simp only [show (17 = 3) = False from by decide, show (17 = 4) = False from by decide,
      show (17 = 5) = False from by decide, show (17 = 6) = False from by decide,
      show (17 = 7) = False from by decide, show (17 = 8) = False from by decide,
      show (17 = 9) = False from by decide, ite_false] at hfm2
    rw [hfm1] at hfm2
    refine ⟨hfr2.trans hfr1, hr2, by omega, hbp2.trans hbp1, hm0_2.trans hm0_1,
      hm2_2.trans hm2_1, fun r hrr => (htr2 r hrr).trans (htr1 r hrr),
      fun a ha => (hoi2 a ha).trans (hoi1 a ha),
      fun a ha => (hof2 a ha).trans (hof1 a ha),
      fun b' hb' r hrr hne => (hbt2 b' hb' r hrr).trans (hoth1 b' hb' r hrr hne),
      Or.inl ⟨rfl, hfm2, by rw [hbt2 b hb _ htr_lt]; exact hv1⟩⟩

private theorem fastRelocTryStepProg_spec {fl : FastEpochLayout}
    {w b role delLoc lastLoc : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s : Memory.State} (uLast : Fin fl.U)
    (hr : FastLayoutReady w fl s)
    (hfp_rep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s.mem)
    (hb : b < numBucketsWhp fl.N) (hrole : role < 3)
    (hcr : (extractFastMeta fl s.mem).curRole b = role)
    (hdel_val : delLoc < 2 ^ valLaneBitsWhp fl.N)
    {tryMap : ℕ → Option ℕ}
    (htry_ok : (extractFastMeta fl s.mem).tryAct = 1 → (extractFastMeta fl s.mem).tryBkt = b →
      ∃ hs : (extractFastMeta fl s.mem).trySalt < sMaxWhp fl.c fl.N,
        (extractFastMeta fl s.mem).tryIns ≤ 5 * slabScale fl.N ^ 12 ∧
        (¬(lastLoc < (extractFastMeta fl s.mem).tryPos) →
          delLoc < (extractFastMeta fl s.mem).tryPos →
          (extractFastMeta fl s.mem).tryIns < 5 * slabScale fl.N ^ 12) ∧
        (lastLoc < (extractFastMeta fl s.mem).tryPos →
          tryMap (fpHash fl.c fl.U fl.N seeds.fp
            ⟨(extractFastMeta fl s.mem).trySalt, hs⟩ uLast).val = some lastLoc) ∧
        ValidWhpSlice fl.N (extractFastMeta fl s.mem).tryIns
          (extractBTreeSlice fl.btL b (tryRoleOf role) s.mem) tryMap) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s
      (fastRelocTryStepProg ((fl.pBase, (b, role)), ((delLoc, lastLoc), uLast.val)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastRelocTryStepProg ((fl.pBase, (b, role)), ((delLoc, lastLoc), uLast.val))) s ≤
      2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree + 200 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3, (b' ≠ b ∨ r ≠ tryRoleOf role) →
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    ((¬(fm.tryAct = 1 ∧ fm.tryBkt = b) ∨ ¬(delLoc < fm.tryPos)) ∧
        ¬(fm.tryAct = 1 ∧ fm.tryBkt = b ∧ lastLoc < fm.tryPos) →
      s' = s) ∧
    (fm.tryAct = 1 → fm.tryBkt = b → ∀ hs : fm.trySalt < sMaxWhp fl.c fl.N,
      let fpT := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ uLast).val
      (lastLoc < fm.tryPos →
        extractFastMeta fl s'.mem = fm ∧
        ValidWhpSlice fl.N fm.tryIns
          (extractBTreeSlice fl.btL b (tryRoleOf role) s'.mem)
          (Function.update tryMap fpT (some delLoc))) ∧
      (¬(lastLoc < fm.tryPos) → delLoc < fm.tryPos →
        (tryMap fpT = none ∧
          extractFastMeta fl s'.mem = { fm with tryIns := fm.tryIns + 1 } ∧
          ValidWhpSlice fl.N (fm.tryIns + 1)
            (extractBTreeSlice fl.btL b (tryRoleOf role) s'.mem)
            (Function.update tryMap fpT (some delLoc))) ∨
        (∃ wLoc, tryMap fpT = some wLoc ∧
          extractFastMeta fl s'.mem =
            { fm with
              trySalt := if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0
              tryPos := 0
              tryIns := 0 } ∧
          ValidWhpSlice fl.N 0
            (extractBTreeSlice fl.btL b (tryRoleOf role) s'.mem) (fun _ => none)))) := by
  dsimp only
  have hpt := hr.2.1
  have hr6 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 6)) =
      (extractFastMeta fl s.mem).tryAct := clientResult_fastReadMetaProg hpt (by decide)
  have hr7 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 7)) =
      (extractFastMeta fl s.mem).tryBkt := clientResult_fastReadMetaProg hpt (by decide)
  have hr9 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 9)) =
      (extractFastMeta fl s.mem).tryPos := clientResult_fastReadMetaProg hpt (by decide)
  have hr8 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 8)) =
      (extractFastMeta fl s.mem).trySalt := clientResult_fastReadMetaProg hpt (by decide)
  have hc6 := memoryCost_fastReadMetaProg (fl.pBase, 6) s
  have hc7 := memoryCost_fastReadMetaProg (fl.pBase, 7) s
  have hc9 := memoryCost_fastReadMetaProg (fl.pBase, 9) s
  have hc8 := memoryCost_fastReadMetaProg (fl.pBase, 8) s
  unfold fastRelocTryStepProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr6,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr7,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr9]
  by_cases hact : (extractFastMeta fl s.mem).tryAct = 1 ∧ (extractFastMeta fl s.mem).tryBkt = b
  · rw [ite_eq_left hact,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hr8]
    obtain ⟨hs, hti_le5, hti_lt5, h_last, hvt⟩ := htry_ok hact.1 hact.2
    obtain ⟨hfp_r, hfp_c⟩ := fastFpHashProg_spec hr hfp_rep
      ⟨(extractFastMeta fl s.mem).trySalt, hs⟩ uLast
    dsimp only at hfp_r hfp_c
    have hfp_lt := (fpHash fl.c fl.U fl.N seeds.fp
      ⟨(extractFastMeta fl s.mem).trySalt, hs⟩ uLast).isLt
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastFpHashProg, hfp_r,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_tryRoleProg, clientResult_tryRoleProg, memoryCost_tryRoleProg]
    obtain ⟨htr_lt, _⟩ := tryRoleOf_lt_and_ne hrole
    by_cases hlt : lastLoc < (extractFastMeta fl s.mem).tryPos
    · rw [ite_eq_left hlt]
      have hti_le8 : (extractFastMeta fl s.mem).tryIns ≤ 8 * slabScale fl.N ^ 12 := by omega
      obtain ⟨hfr, hr', hc, hv', hoth, hbp, hfm, hm2, hm0, htr, hoi, hof⟩ :=
        fastBTreeUpdateProg_spec hr hb htr_lt hti_le8 hvt hfp_lt hdel_val
      have hsome : (tryMap (fpHash fl.c fl.U fl.N seeds.fp
          ⟨(extractFastMeta fl s.mem).trySalt, hs⟩ uLast).val).isSome = true := by
        rw [h_last hlt]; rfl
      rw [hsome, ite_eq_left rfl] at hv'
      exact ⟨hfr, hr', by omega, hbp, hm0, hm2, htr, hoi, hof, hoth,
        fun h => absurd ⟨hact.1, hact.2, hlt⟩ h.2,
        fun _ _ _ => ⟨fun _ => ⟨hfm, hv'⟩, fun hn _ => absurd hlt hn⟩⟩
    · rw [ite_eq_right hlt]
      by_cases hdel : delLoc < (extractFastMeta fl s.mem).tryPos
      · rw [ite_eq_left hdel]
        obtain ⟨hfr, hr', hc, hbp, hm0, hm2, htr, hoi, hof, hoth, hres⟩ :=
          fastRelocTryInsProg_spec hr hb hrole hact.2 hcr hfp_lt hdel_val (hti_lt5 hlt hdel) hvt
        exact ⟨hfr, hr', by omega, hbp, hm0, hm2, htr, hoi, hof, hoth,
          fun h => False.elim (h.1.elim (· hact) (· hdel)),
          fun _ _ _ => ⟨fun hl => absurd hl hlt, fun _ _ => hres⟩⟩
      · rw [ite_eq_right hdel]
        have hcp : memoryCost (pure () : Memory.Prog Unit) s = 0 := rfl
        refine ⟨rfl, hr, by omega, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
          fun _ _ _ _ _ => rfl, fun _ => rfl,
          fun _ _ _ => ⟨fun hl => absurd hl hlt, fun _ hd => absurd hd hdel⟩⟩
  · rw [ite_eq_right hact]
    have hcp : memoryCost (pure () : Memory.Prog Unit) s = 0 := rfl
    refine ⟨rfl, hr, by omega, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ _ _ _ => rfl, fun _ => rfl,
      fun h1 h2 _ => absurd ⟨h1, h2⟩ hact⟩

/-- Step helper rewriting `TierInvHoleWith` across a single `fastBpWriteAtProg` whose only write
is overwriting `(b, delLoc)` (the already-excluded hole!). -/
private theorem tierInvHole_of_bpWriteAt {slackCur : ℕ} {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s s' : Memory.State} {b delLoc q v : ℕ}
    {mapCur mapOld : ℕ → Option (ℕ × ℕ)} {mapBTree : ℕ → ℕ → Option ℕ}
    (hv : fl.Valid w s.frontier)
    (hbp_inv : fl.bpL.StateInv 0 s.mem)
    (hbp_eq : extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem)
    (hfm_eq : extractFastMeta fl s'.mem = extractFastMeta fl s.mem)
    (hbt_eq : ∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem)
    (htr_eq : ∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem)
    (hpair : ∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp s.mem).bktCount b',
      bpPairAt fl.bpL s'.mem b' loc' =
        if b' = b ∧ loc' = delLoc then (q, v) else bpPairAt fl.bpL s.mem b' loc')
    (ht : TierInvHoleWith slackCur fl seeds s.mem b delLoc false mapCur mapOld mapBTree) :
    TierInvHoleWith slackCur fl seeds s'.mem b delLoc false mapCur mapOld mapBTree := by
  have _ := hv; have _ := hbp_inv
  have hkey_ne : ∀ b' loc', b' < numBucketsWhp fl.N →
      loc' < (extractBlockPool fl.mp s.mem).bktCount b' → ¬(b' = b ∧ loc' = delLoc) →
      fastKeyAt fl seeds.bkt s'.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' := by
    intro b' loc' hb' hl' hne
    unfold fastKeyAt
    have hp := hpair b' hb' loc' hl'
    rw [ite_eq_right hne] at hp
    rw [hp]
  refine
    { role_lt := by rw [hfm_eq]; exact ht.role_lt
      subStep_lt := by rw [hfm_eq]; exact ht.subStep_lt
      bkt_meta_bounds := fun b' hb' => by rw [hfm_eq]; exact ht.bkt_meta_bounds b' hb'
      cur_valid := by rw [hfm_eq, htr_eq _ ht.role_lt]; exact ht.cur_valid
      cur_raw := by rw [hfm_eq, htr_eq _ ht.role_lt]; exact ht.cur_raw
      cur_clr := by rw [hfm_eq, htr_eq _ ht.role_lt]; exact ht.cur_clr
      cur_ia := by rw [hfm_eq, htr_eq _ ht.role_lt]; exact ht.cur_ia
      cur_na := by rw [hfm_eq, htr_eq _ ht.role_lt]; exact ht.cur_na
      cur_sound := fun rk b' loc' hm => by
        obtain ⟨hb', hl', hne, u', hrk', hk'⟩ := ht.cur_sound rk b' loc' hm
        exact ⟨hb', by rw [hbp_eq]; exact hl', hne, u', hrk',
          (hkey_ne b' loc' hb' hl' hne).trans hk'⟩
      old_valid_half := fun hsub => by
        rw [hfm_eq] at hsub ⊢
        have hold_lt : 1 - (extractFastMeta fl s.mem).curBufRole < 2 := by
          have := ht.role_lt; omega
        rw [htr_eq _ hold_lt, hbp_eq]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, hsnd⟩ := ht.old_valid_half hsub
        refine ⟨h1, h2, h3, h4, h5, h6, h7, fun rk b' loc' hm => ?_⟩
        obtain ⟨hcn, hb', hl', hne, u', hrk', hk'⟩ := hsnd rk b' loc' hm
        exact ⟨hcn, hb', hl', hne, u', hrk', (hkey_ne b' loc' hb' hl' hne).trans hk'⟩
      old_clear_half := fun hsub => by
        rw [hfm_eq] at hsub ⊢
        have hold_lt : 1 - (extractFastMeta fl s.mem).curBufRole < 2 := by
          have := ht.role_lt; omega
        rw [htr_eq _ hold_lt]; exact ht.old_clear_half hsub
      bt_valid := fun b' hb' => by
        rw [hfm_eq, hbt_eq b' hb' _ (ht.bkt_meta_bounds b' hb').2.1]
        exact ht.bt_valid b' hb'
      bt_sound := fun b' hb' fp' loc' hm => by
        obtain ⟨hl', hne, u', hf', hk', hd1, hd2⟩ := ht.bt_sound b' hb' fp' loc' hm
        have hbs := congrArg (fun m => m.bktSalt b') hfm_eq
        refine ⟨by rw [hbp_eq]; exact hl', hne, u',
          (congrArg Fin.val (fpHash_congr_salt (h₂ := (ht.bkt_meta_bounds b' hb').1) hbs u')).trans
            hf',
          (hkey_ne b' loc' hb' hl' hne).trans hk', fun b₁ l₁ hm₁ => ?_, fun b₂ l₂ hm₂ => ?_⟩
        · obtain ⟨hb₁, hl₁, hne₁, _⟩ := ht.cur_sound _ b₁ l₁ hm₁
          rw [hkey_ne b₁ l₁ hb₁ hl₁ hne₁]; exact hd1 b₁ l₁ hm₁
        · have hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2 := by
            by_contra hn; rw [(ht.old_clear_half hn).1] at hm₂; cases hm₂
          obtain ⟨_, hb₂, hl₂, hne₂, _⟩ := (ht.old_valid_half hsub).2.2.2.2.2.2.2 _ b₂ l₂ hm₂
          rw [hkey_ne b₂ l₂ hb₂ hl₂ hne₂]; exact hd2 b₂ l₂ hm₂
      complete := fun b' hb' loc' hl' hne => by
        rw [hbp_eq] at hl'
        obtain ⟨u', hk', htier⟩ := ht.complete b' hb' loc' hl' hne
        refine ⟨u', (hkey_ne b' loc' hb' hl' hne).trans hk', ?_⟩
        rcases htier with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · have hbs := congrArg (fun m => m.bktSalt b') hfm_eq
          exact Or.inr (Or.inr ((mapBTree_fpHash_congr mapBTree rfl hbs u').trans h3))
      shadow := fun b' hb' hsc => by
        have hsc0 : (extractFastMeta fl s.mem).shadowCode b' ≠ 0 := by rw [hfm_eq] at hsc; exact hsc
        obtain ⟨h1, h2, h3, h4, sm, hvs, heq⟩ := ht.shadow b' hb' hsc0
        rw [hfm_eq, hbp_eq]
        have hsr := (shadowRoleOf_lt_and_ne (ht.bkt_meta_bounds b' hb').2.1).1
        exact ⟨h1, h2, h3, h4, sm, by rw [hbt_eq b' hb' _ hsr]; exact hvs, heq⟩
      tryAct_le := by rw [hfm_eq]; exact ht.tryAct_le
      try_ok := fun hta1 => by
        have hta0 : (extractFastMeta fl s.mem).tryAct = 1 := by rw [hfm_eq] at hta1; exact hta1
        obtain ⟨hsub, hb_t, hs_t, htp, hsc, hbd, tm, hvt, htm1, htm2⟩ := ht.try_ok hta0
        have htb_eq := congrArg FastEpochMeta.tryBkt hfm_eq
        have hts_eq := congrArg FastEpochMeta.trySalt hfm_eq
        have htp_eq := congrArg FastEpochMeta.tryPos hfm_eq
        have hti_eq := congrArg FastEpochMeta.tryIns hfm_eq
        have hcr_eq := congrArg (fun m => m.curRole (extractFastMeta fl s.mem).tryBkt) hfm_eq
        have hbs_eq := congrArg (fun m => m.bktSalt (extractFastMeta fl s.mem).tryBkt) hfm_eq
        have htr_lt := (tryRoleOf_lt_and_ne (ht.bkt_meta_bounds _ hb_t).2.1).1
        refine ⟨by rw [hfm_eq]; exact hsub, by rw [htb_eq]; exact hb_t,
          by rw [hts_eq]; exact hs_t, by rw [hbp_eq, htp_eq, htb_eq]; exact htp,
          by rw [hfm_eq]; exact hsc, by rw [hbp_eq, hfm_eq]; exact hbd, tm, ?_, ?_, ?_⟩
        · rw [htb_eq, hti_eq, hcr_eq, hbt_eq _ hb_t _ htr_lt]; exact hvt
        · intro fp' loc' hm
          obtain ⟨hlt, hne, u', hk', hmb, hf'⟩ := htm1 fp' loc' hm
          have hlb := lt_of_lt_of_le hlt htp
          exact ⟨by rw [htp_eq]; exact hlt, by rwa [htb_eq], u',
            by rw [htb_eq]; exact (hkey_ne _ loc' hb_t hlb hne).trans hk',
            (mapBTree_fpHash_congr mapBTree htb_eq (by rw [htb_eq, hbs_eq]) u').trans hmb,
            (congrArg Fin.val (fpHash_congr_salt hts_eq u')).trans hf'⟩
        · intro loc' hlt hne u' hk' hmb
          have hlt' : loc' < (extractFastMeta fl s.mem).tryPos := by rwa [htp_eq] at hlt
          have hne' : ¬((extractFastMeta fl s.mem).tryBkt = b ∧ loc' = delLoc) := by
            rwa [htb_eq] at hne
          have hlb := lt_of_lt_of_le hlt' htp
          rw [congrArg Fin.val (fpHash_congr_salt (h₂ := hs_t) hts_eq u')]
          exact htm2 loc' hlt' hne' u'
            ((hkey_ne _ loc' hb_t hlb hne').symm.trans (htb_eq ▸ hk'))
            ((mapBTree_fpHash_congr mapBTree htb_eq (by rw [htb_eq, hbs_eq]) u').symm.trans
              hmb) }

private theorem bpStateInv_congr_io {fl : FastEpochLayout} {w fr slack : ℕ}
    {m₁ m₂ : ℕ → ℕ}
    (hv : fl.Valid w fr) (hbp_inv : fl.bpL.StateInv slack m₁)
    (hbp_eq : extractBlockPool fl.mp m₂ = extractBlockPool fl.mp m₁)
    (hoi : ∀ addr, fl.io.OwnsAddr addr → m₂ addr = m₁ addr) :
    fl.bpL.StateInv slack m₂ :=
  ⟨hbp_eq ▸ hbp_inv.1, hbp_eq ▸ hbp_inv.2.1,
    hbp_eq ▸ (fl.io.congr_of_outside hv.io_valid.w_pos hbp_inv.2.2 hoi).1⟩

theorem bpPairAt_eq_of_fixed_pool {fl : FastEpochLayout} {w fr slack : ℕ}
    {m₁ m₂ : ℕ → ℕ}
    (hv : fl.Valid w fr) (hbp_inv : fl.bpL.StateInv slack m₁)
    (hbp_eq : extractBlockPool fl.mp m₂ = extractBlockPool fl.mp m₁)
    (hoi : ∀ addr, fl.io.OwnsAddr addr → m₂ addr = m₁ addr)
    {b loc : ℕ} (hb : b < numBucketsWhp fl.N)
    (hloc : loc < (extractBlockPool fl.mp m₁).bktCount b) :
    bpPairAt fl.bpL m₂ b loc = bpPairAt fl.bpL m₁ b loc := by
  unfold bpPairAt; dsimp only [FastEpochLayout.bpL]
  rw [hbp_eq]
  have hp_lt := hbp_inv.1.core.toPhys_lt hb hloc
  dsimp only [FastEpochLayout.bpL] at hp_lt
  exact (fl.io.congr_of_outside hv.io_valid.w_pos hbp_inv.2.2 hoi).2 _ hp_lt

theorem pagePair_partner_eq_of_io {fl : FastEpochLayout} {w fr slack : ℕ}
    {m₁ m₂ : ℕ → ℕ} (hv : fl.Valid w fr) (hup : fl.io.usePaged ≠ 0)
    (hbp_inv : fl.bpL.StateInv slack m₁)
    (hoi : ∀ addr, fl.io.OwnsAddr addr → m₂ addr = m₁ addr) :
    extractPageUnperm fl.io.pgL m₂ = extractPageUnperm fl.io.pgL m₁ ∧
    extractPagePair fl.io.pgL m₂ = extractPagePair fl.io.pgL m₁ ∧
    ∀ idx < (extractPagePair fl.io.pgL m₁).virtLen fl.io.partner.side,
      slotIoPairAt fl.io.partner m₂ idx = slotIoPairAt fl.io.partner m₁ idx := by
  have hw := hv.io_valid.w_pos
  have hio_inv : fl.io.StateInv (extractBlockPool fl.mp m₁).nSide slack m₁ := hbp_inv.2.2
  simp only [SlotIoLayout.StateInv, hup, ↓reduceIte] at hio_inv
  have howns_m : ∀ a, fl.io.pgL.OwnsMetaAddr a → m₂ a = m₁ a := fun a ha =>
    hoi a (by unfold SlotIoLayout.OwnsAddr; rw [ite_eq_right hup]; exact Or.inl ha)
  have howns_i : ∀ a, fl.io.pgL.OwnsItemAddr a → m₂ a = m₁ a := fun a ha =>
    hoi a (by unfold SlotIoLayout.OwnsAddr; rw [ite_eq_right hup]; exact Or.inr ha)
  have hu_eq : extractPageUnperm fl.io.pgL m₂ = extractPageUnperm fl.io.pgL m₁ :=
    extractPageUnperm_congr hw howns_m
  have hp_eq : extractPagePair fl.io.pgL m₂ = extractPagePair fl.io.pgL m₁ :=
    congrArg PageUnpermState.st hu_eq
  refine ⟨hu_eq, hp_eq, fun idx hidx => ?_⟩
  have hup_p : fl.io.partner.usePaged ≠ 0 := hup
  unfold slotIoPairAt
  rw [ite_eq_right hup_p, ite_eq_right hup_p]
  change (extractPageUnperm fl.io.pgL m₂).virtAt (arenaPairAt fl.io.pgL m₂)
      fl.io.partner.side idx =
    (extractPageUnperm fl.io.pgL m₁).virtAt (arenaPairAt fl.io.pgL m₁) fl.io.partner.side idx
  rw [hu_eq]
  unfold PageUnpermState.virtAt
  have hlt : (extractPageUnperm fl.io.pgL m₁).toPhys fl.io.partner.side idx < fl.io.pgL.nCap := by
    have hp_lt := hio_inv.1.toPhys_lt hidx
    exact hp_lt.trans_le hio_inv.2.2.2.1
  exact arenaPairAt_congr hw howns_i hlt

private theorem fastPromoteShadowIfDoneProg_spec {fl : FastEpochLayout} {w b cnt : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s) (hb : b < numBucketsWhp fl.N)
    (hcnt_gt : 0 < cnt)
    (hrole : (extractFastMeta fl s.mem).curRole b < 3)
    (hsh_ins : (extractFastMeta fl s.mem).shadowCode b = cnt →
      (extractFastMeta fl s.mem).shadowIns b ≤ 5 * slabScale fl.N ^ 12) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s (fastPromoteShadowIfDoneProg ((fl.pBase, b), cnt))
    let fm' := extractFastMeta fl s'.mem
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastPromoteShadowIfDoneProg ((fl.pBase, b), cnt)) s ≤ 65 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fm.shadowCode b ≠ cnt → s' = s) ∧
    (fm.shadowCode b = cnt →
      fm' = { fm with
        curRole := Function.update fm.curRole b (shadowRoleOf (fm.curRole b))
        curIns := Function.update fm.curIns b (fm.shadowIns b)
        shadowCode := Function.update fm.shadowCode b 0 }) := by
  dsimp only
  have hv := hr.1
  have hpt := hr.2.1
  set fm := extractFastMeta fl s.mem
  have h15_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 15))) =
      fm.shadowCode b := by
    have := bktLane_val_eq hpt hb (Or.inr ⟨by decide, by decide⟩) (lane := 15)
    simpa only [show (15 = 5) = False from by decide, show (15 = 12) = False from by decide,
      show (15 = 13) = False from by decide, show (15 = 14) = False from by decide,
      Bool.false_eq_true, ite_false] using this
  have c15 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 15)) s
  unfold fastPromoteShadowIfDoneProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadBktLaneProg, h15_r]
  by_cases hdone : fm.shadowCode b = cnt
  · have hsr_lt := (shadowRoleOf_lt_and_ne hrole).1
    have hsi_le : fm.shadowIns b ≤ fl.N := by
      have h1 := hsh_ins hdone; have h2 := hv.bounds_le_N.1; omega
    have h12_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12))) =
        fm.curRole b := by
      have := bktLane_val_eq hpt hb (Or.inr ⟨by decide, by decide⟩) (lane := 12)
      simpa only [show (12 = 5) = False from by decide, ite_true, ite_false] using this
    have h14_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 14))) =
        fm.shadowIns b := by
      have := bktLane_val_eq hpt hb (Or.inr ⟨by decide, by decide⟩) (lane := 14)
      simpa only [show (14 = 5) = False from by decide, show (14 = 12) = False from by decide,
        show (14 = 13) = False from by decide, ite_true, ite_false] using this
    have c12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s
    have c14 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 14)) s
    rw [ite_eq_left hdone,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadBktLaneProg, h12_r,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_shadowRoleProg, clientResult_shadowRoleProg, memoryCost_shadowRoleProg,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadBktLaneProg, h14_r]
    have hcw1 := memoryCost_fastWriteBktLaneProg
      ((fl.pBase, (b, 12)), shadowRoleOf (fm.curRole b)) s
    obtain ⟨hfr1, hr1, hbp1, hbt1, htr1, hof1, hoi1⟩ := fastWriteBktLaneProg_frame
      (b := b) (lane := 12) (val := shadowRoleOf (fm.curRole b)) hr
    have hsr_le : shadowRoleOf (fm.curRole b) ≤ fl.N := by
      have h64 : 64 ≤ fl.N := (whpThreshold_ge_64 fl.c).trans hv.thresh_le; omega
    obtain ⟨hm2_1, hfm1⟩ := extractFastMeta_writeBktLane hr hb (lane := 12)
      (Or.inr ⟨by decide, by decide⟩) (val := shadowRoleOf (fm.curRole b)) hsr_le
    generalize hs1_def : (Memory.spec 0).clientState s
      (fastWriteBktLaneProg ((fl.pBase, (b, 12)), shadowRoleOf (fm.curRole b))) = s1
    rw [hs1_def] at hfr1 hr1 hbp1 hbt1 htr1 hof1 hoi1 hm2_1 hfm1
    have hcw2 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 13)), fm.shadowIns b) s1
    obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hof2, hoi2⟩ := fastWriteBktLaneProg_frame
      (b := b) (lane := 13) (val := fm.shadowIns b) hr1
    obtain ⟨hm2_2, hfm2⟩ := extractFastMeta_writeBktLane hr1 hb (lane := 13)
      (Or.inr ⟨by decide, by decide⟩) (val := fm.shadowIns b) hsi_le
    generalize hs2_def : (Memory.spec 0).clientState s1
      (fastWriteBktLaneProg ((fl.pBase, (b, 13)), fm.shadowIns b)) = s2
    rw [hs2_def] at hfr2 hr2 hbp2 hbt2 htr2 hof2 hoi2 hm2_2 hfm2
    have hcw3 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 15)), 0) s2
    obtain ⟨hfr3, hr3, hbp3, hbt3, htr3, hof3, hoi3⟩ := fastWriteBktLaneProg_frame
      (b := b) (lane := 15) (val := 0) hr2
    obtain ⟨hm2_3, hfm3⟩ := extractFastMeta_writeBktLane hr2 hb (lane := 15)
      (Or.inr ⟨by decide, by decide⟩) (val := 0) (Nat.zero_le _)
    generalize hs3_def : (Memory.spec 0).clientState s2
      (fastWriteBktLaneProg ((fl.pBase, (b, 15)), 0)) = s3
    rw [hs3_def] at hfr3 hr3 hbp3 hbt3 htr3 hof3 hoi3 hm2_3 hfm3
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs2_def, hs3_def]
    rw [ite_eq_right (by decide : (12 : ℕ) ≠ 5), ite_eq_left rfl] at hfm1
    rw [ite_eq_right (by decide : (13 : ℕ) ≠ 5), ite_eq_right (by decide : (13 : ℕ) ≠ 12),
      ite_eq_left rfl] at hfm2
    rw [ite_eq_right (by decide : (15 : ℕ) ≠ 5), ite_eq_right (by decide : (15 : ℕ) ≠ 12),
      ite_eq_right (by decide : (15 : ℕ) ≠ 13), ite_eq_right (by decide : (15 : ℕ) ≠ 14)] at hfm3
    have hm0_3 : s3.mem fl.metaBase = s.mem fl.metaBase :=
      (hof3 fl.metaBase hr2.1.not_ownsFast_hdr0).trans
        ((hof2 fl.metaBase hr1.1.not_ownsFast_hdr0).trans
          (hof1 fl.metaBase hv.not_ownsFast_hdr0))
    refine ⟨hfr3.trans (hfr2.trans hfr1), hr3, by omega, hbp3.trans (hbp2.trans hbp1),
      hm0_3, hm2_3.trans (hm2_2.trans hm2_1),
      fun b' hb' r hrr => (hbt3 b' hb' r hrr).trans ((hbt2 b' hb' r hrr).trans (hbt1 b' hb' r hrr)),
      fun r hrr => (htr3 r hrr).trans ((htr2 r hrr).trans (htr1 r hrr)),
      fun a ha => (hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha)),
      fun a ha => (hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha)),
      fun h => absurd hdone h, fun _ => ?_⟩
    rw [hfm3, hfm2, hfm1]
  · rw [ite_eq_right hdone]
    have hcp : memoryCost (pure () : Memory.Prog Unit) s = 0 := rfl
    have _ := hcnt_gt
    exact ⟨rfl, hr, by omega, rfl, rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun h => absurd h hdone⟩

private theorem fastClampTryPosProg_spec {fl : FastEpochLayout} {w b cnt lastLoc : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s
      (fastClampTryPosProg ((fl.pBase, b), (cnt, lastLoc)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastClampTryPosProg ((fl.pBase, b), (cnt, lastLoc))) s ≤ 25 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    extractFastMeta fl s'.mem =
      if fm.tryAct = 1 ∧ fm.tryBkt = b ∧ fm.tryPos = cnt then
        { fm with tryPos := lastLoc }
      else fm := by
  dsimp only
  have hpt := hr.2.1
  set fm := extractFastMeta fl s.mem
  have hr6 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 6)) = fm.tryAct :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hr7 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 7)) = fm.tryBkt :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hr9 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 9)) = fm.tryPos :=
    clientResult_fastReadMetaProg hpt (by decide)
  have c6 := memoryCost_fastReadMetaProg (fl.pBase, 6) s
  have c7 := memoryCost_fastReadMetaProg (fl.pBase, 7) s
  have c9 := memoryCost_fastReadMetaProg (fl.pBase, 9) s
  unfold fastClampTryPosProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr6,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr7,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hr9]
  by_cases hc : fm.tryAct = 1 ∧ fm.tryBkt = b ∧ fm.tryPos = cnt
  · rw [ite_eq_left hc, ite_eq_left hc]
    have cw9 := memoryCost_fastWriteMetaProg ((fl.pBase, 9), lastLoc) s
    obtain ⟨hfr, hr', hbp, hbt, htr, hoi, hof, hm2, hfm⟩ :=
      extractFastMeta_writeMeta (off := 9) (val := lastLoc) hr (Or.inl ⟨by decide, by decide⟩)
    have hm0 : ((Memory.spec 0).clientState s
        (fastWriteMetaProg ((fl.pBase, 9), lastLoc))).mem fl.metaBase = s.mem fl.metaBase :=
      hof fl.metaBase hr.1.not_ownsFast_hdr0
    rw [ite_eq_right (by decide : (9 : ℕ) ≠ 3), ite_eq_right (by decide : (9 : ℕ) ≠ 4),
      ite_eq_right (by decide : (9 : ℕ) ≠ 5), ite_eq_right (by decide : (9 : ℕ) ≠ 6),
      ite_eq_right (by decide : (9 : ℕ) ≠ 7), ite_eq_right (by decide : (9 : ℕ) ≠ 8),
      ite_eq_left rfl] at hfm
    exact ⟨hfr, hr', by omega, hbp, hm0, hm2, hbt, htr, hoi, hof, hfm⟩
  · rw [ite_eq_right hc, ite_eq_right hc]
    have hcp : memoryCost (pure () : Memory.Prog Unit) s = 0 := rfl
    exact ⟨rfl, hr, by omega, rfl, rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl, rfl⟩

private theorem extractBufTrie_congr_of_not_bt {fl : FastEpochLayout} {w fr role : ℕ}
    {m₁ m₂ : ℕ → ℕ} (hv : fl.Valid w fr) (hrole : role < 2)
    (hbt : ∀ addr, ¬fl.btL.OwnsAddr addr → m₂ addr = m₁ addr) :
    extractBufTrie (fl.trieL role) m₂ = extractBufTrie (fl.trieL role) m₁ := by
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  exact extractBufTrie_congr (show 0 < (fl.trieL role).w from hw_pos) fun a ha =>
    hbt a (fun h => fl.disj_btree_trie hv hrole h ha)

private theorem fastDeleteFromBTreesProg_trie_eq {fl : FastEpochLayout} {w b delLoc u_val : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s) :
    ∀ r < 2,
      extractBufTrie (fl.trieL r)
        ((Memory.spec 0).clientState s
          (fastDeleteFromBTreesProg ((fl.pBase, (b, delLoc)), u_val))).mem =
      extractBufTrie (fl.trieL r) s.mem := by
  intro r hrl
  have hdel : ∀ (st : Memory.State) (b0 r0 q0 : ℕ), FastLayoutReady w fl st →
      FastLayoutReady w fl
        ((Memory.spec 0).clientState st (fastBTreeDeleteProg ((fl.pBase, (b0, r0)), q0))) ∧
      extractBufTrie (fl.trieL r)
        ((Memory.spec 0).clientState st (fastBTreeDeleteProg ((fl.pBase, (b0, r0)), q0))).mem =
        extractBufTrie (fl.trieL r) st.mem := fun st b0 r0 q0 hst => by
    obtain ⟨_, hst', hout⟩ := fastBTreeDeleteProg_ready (b := b0) (role := r0) (q := q0) hst
    exact ⟨hst', extractBufTrie_congr_of_not_bt hst.1 hrl hout⟩
  unfold fastDeleteFromBTreesProg; dsimp only
  rw [StateTransitionSpec.clientState_bind,
    show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s from rfl,
    prog_clientResult_read]
  by_cases hb : b < s.mem (fl.pBase + 11)
  · rw [ite_eq_left hb,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    set salt := (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 5)))
    set role := (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12)))
    set fp := (Memory.spec 0).clientResult s (fastFpHashProg (fl.pBase, (salt, u_val)))
    set s1 := (Memory.spec 0).clientState s (fastBTreeDeleteProg ((fl.pBase, (b, role)), fp))
    obtain ⟨hr1, ht1⟩ := hdel s b role fp hr
    have hsh : FastLayoutReady w fl
          ((Memory.spec 0).clientState s1
            (fastDelShadowTryStepProg ((fl.pBase, (b, role)), (fp, delLoc)))) ∧
        extractBufTrie (fl.trieL r)
          ((Memory.spec 0).clientState s1
            (fastDelShadowTryStepProg ((fl.pBase, (b, role)), (fp, delLoc)))).mem =
          extractBufTrie (fl.trieL r) s1.mem := by
      unfold fastDelShadowTryStepProg; dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg]
      split_ifs
      · rw [StateTransitionSpec.clientState_bind, clientState_shadowRoleProg]
        exact hdel s1 b _ fp hr1
      · exact ⟨hr1, rfl⟩
    set s2 := (Memory.spec 0).clientState s1
      (fastDelShadowTryStepProg ((fl.pBase, (b, role)), (fp, delLoc)))
    have ht3 : extractBufTrie (fl.trieL r)
        ((Memory.spec 0).clientState s2
          (fastDelTryStepProg ((fl.pBase, (b, role)), (delLoc, u_val)))).mem =
        extractBufTrie (fl.trieL r) s2.mem := by
      unfold fastDelTryStepProg; dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
        StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
        StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
      split_ifs
      · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
          StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
          StateTransitionSpec.clientState_bind, clientState_tryRoleProg]
        exact (hdel s2 b _ _ hsh.1).2
      · rfl
    exact ht3.trans (hsh.2.trans ht1)
  · rw [ite_eq_right hb]; rfl

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
