/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochCtx
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFallback
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deamortized Large-Epoch Mutating Wrappers, Initialization, Shadow Compaction, and Sub-Epoch Drain

This module implements the `pBase`-addressed mutating primitives, zeroed-region initialization
(`fastInitZeroedProg`), deamortized per-bucket B+-tree shadow compaction (`fastShadowSteps8Prog`),
and the fallback-entry subroutine (`fastEnterFallbackProg`, invoked at the sub-epoch midpoint by
`advanceSubEpochProg` in `LargeEpochAdvance.lean`) for the SOSA 2024
with-high-probability succinct dynamic dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Design

1. **Compositional `FastProgPre` preservation:** Every mutating `pBase` wrapper (`fastBp*`,
   `fastBuf*`, `fastBTree*`, `fastEnterFallbackProg`) modifies only words inside `fl.OwnsFastAddr`
   while preserving `s.frontier`, so `FastLayoutReady w fl` and `FastProgPre w pBase` compose
   sequentially across arbitrary binds without re-proving parameter-table or seed bounds.
2. **Fallback isolation at sub-epoch midpoint:** Inside `fastShadowStepProg` and `drainTickProg`,
   every step preserves `FastEpochInv` (`fallbackMode = 0`) on **100% of hash seeds** (if a bad seed
   exhausts `sMaxWhp c N` salts, `drainTryStepProg` resets `tryPos := 0` and stays in `tryAct = 1`).
   Fallback transition (`fastEnterFallbackProg`) occurs at a single point in `advanceSubEpochProg`
   (`subStep + 1 = Q / 2` with unfinished drain), and at `subStep + 1 = Q` `BufOld` is guaranteed
   deterministically cleared (`nodeAlloc = 1`, `itemAlloc = 0`) on all seeds.
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

/-! ## Section 1: Ownership Inclusions and Mutating `pBase` Wrappers -/

private def readParam2Prog : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (pBase, (i, j)) => do
    let a ← Memory.read (pBase + i)
    let b ← Memory.read (pBase + j)
    pure (a, b)

@[simp] private theorem runClient_state_readParam2Prog
    (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (readParam2Prog x)).2.1 = s := by
  rcases x with ⟨pBase, ⟨i, j⟩⟩; rfl

private theorem clientState_readParam2Prog (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (readParam2Prog x) = s :=
  runClient_state_readParam2Prog x s

private theorem realizesBounded_readParam2 :
    RealizesBounded .exact readParam2Prog
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (pBase, (i, j)) s =>
        6 ≤ w ∧ i < 64 ∧ j < 64 ∧ pBase + 64 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨pBase, ⟨i, j⟩⟩
    obtain ⟨hw6, hi, hj, hp⟩ := h
    have hfr := hmem.1; dsimp only [Fits] at hfr ⊢
    omega)

private def readParam4Prog : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((pBase, ij), kl) => do
    let ab ← readParam2Prog (pBase, ij)
    let cd ← readParam2Prog (pBase, kl)
    pure (ab, cd)

@[simp] private theorem runClient_state_readParam4Prog
    (x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (readParam4Prog x)).2.1 = s := by
  rcases x with ⟨⟨pBase, ⟨i, j⟩⟩, ⟨k, l⟩⟩; rfl

private theorem clientState_readParam4Prog
    (x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (readParam4Prog x) = s :=
  runClient_state_readParam4Prog x s

private theorem realizesBounded_readParam4 :
    RealizesBounded .exact readParam4Prog
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (fun w ((pBase, (i, j)), (k, l)) s =>
        6 ≤ w ∧ i < 64 ∧ j < 64 ∧ k < 64 ∧ l < 64 ∧ pBase + 64 ≤ s.frontier)
      (fun _ _ => 0) := by
  have hp := realizesBounded_readParam2
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨i, j⟩⟩, ⟨k, l⟩⟩
    obtain ⟨hw6, hi, hj, hk, hl, hpb⟩ := h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr := hmem.1; dsimp only [Fits] at hfr ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_readParam2Prog] at *
    omega)

theorem offTrie_mono {c w N role : ℕ} (hrole : role < 2) :
    offBktMeta c w N ≤ offBTreeVals c w N ∧
    offBTreeVals c w N + packedWords (totalBTreeNodesWhp N) (valsWordBitsWhp N) w ≤
      offTrieChild c w N 0 ∧
    offTrieChild c w N 0 ≤ offTrieChild c w N role ∧
    offTrieChild c w N role +
      packedWords (maxTrieNodesWhp c N * 2 ^ bCharWhp N) (globalPtrBits N) w ≤
      offTrieNode c w N 0 ∧
    offTrieNode c w N 0 ≤ offTrieNode c w N role ∧
    offTrieNode c w N role + packedWords (6 * maxTrieNodesWhp c N) (globalPtrBits N) w ≤
      offTrieItem c w N 0 ∧
    offTrieItem c w N 0 ≤ offTrieItem c w N role ∧
    offTrieItem c w N role + packedWords (6 * qEpochWhp N + 6) (globalPtrBits N) w ≤
      offPageDir c w N := by
  rcases role with _ | _ | _ <;> try omega
  all_goals (
    simp only [offPageDir, offTrieItem, offTrieNode, offTrieChild, trieItemWords, trieNodeWords,
      trieChildWords, offBTreeVals, offBTreeKeys, offBTreeMeta, offTailOwner, offSlabOwner,
      offTailDir, offSlabDir]
    omega)

theorem SlotIoLayout.partner_congr_of_outside {io : SlotIoLayout} {nSide slack : ℕ}
    {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < io.pgL.w) (hio : io.StateInv nSide slack mem₁)
    (hout : ∀ addr, io.OwnsAddr addr → mem₂ addr = mem₁ addr) (hnz : io.usePaged ≠ 0) :
    extractPageUnperm io.pgL mem₂ = extractPageUnperm io.pgL mem₁ ∧
    ∀ idx < (extractPagePair io.pgL mem₁).virtLen io.partner.side,
      slotIoPairAt io.partner mem₂ idx = slotIoPairAt io.partner mem₁ idx := by
  have hown_pg : ∀ addr, io.pgL.OwnsAddr addr → mem₂ addr = mem₁ addr := fun addr ha => by
    apply hout addr; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
  have hu_eq : extractPageUnperm io.pgL mem₂ = extractPageUnperm io.pgL mem₁ :=
    extractPageUnperm_congr hw (fun a ha => hown_pg a (Or.inl ha))
  refine ⟨hu_eq, fun idx hidx => ?_⟩
  unfold SlotIoLayout.StateInv at hio; rw [ite_eq_right hnz] at hio
  obtain ⟨hi, _, _, hti, _, _, _⟩ := hio
  have hp_lt : (extractPageUnperm io.pgL mem₁).toPhys io.partner.side idx < io.pgL.nCap :=
    (hi.toPhys_lt hidx).trans_le hti
  unfold slotIoPairAt
  have hp_nz : io.partner.usePaged ≠ 0 := hnz
  rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu_eq]
  unfold PageUnpermState.virtAt
  exact arenaPairAt_congr hw (fun a ha => hown_pg a (Or.inr ha)) hp_lt

theorem FastEpochLayout.owns_of_bpMeta {fl : FastEpochLayout} {w fr addr : ℕ}
    (hv : fl.Valid w fr) (hma : fl.mp.OwnsMetaAddr addr) : fl.OwnsFastAddr addr := by
  have hmv := hv.mp_valid
  rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (rfl | ⟨h10, h17⟩) | ⟨hlo, hhi⟩
  · exact Or.inl ⟨by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega,
      by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega⟩
  · exact Or.inl ⟨by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at *; omega,
      by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at *; omega⟩
  · refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hlo; exact hlo
    · dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hhi
      have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) (role := 0) (by decide)
      have hob : offTailOwner fl.c fl.w fl.N + packedWords (16 * maxTailWhp fl.N)
          (globalPtrBits fl.N) fl.w = offBTreeMeta fl.c fl.w fl.N := rfl
      have hbt_v : offBTreeMeta fl.c fl.w fl.N ≤ offBTreeVals fl.c fl.w fl.N := by
        unfold offBTreeVals offBTreeKeys; omega
      omega

theorem FastEpochLayout.owns_of_bp {fl : FastEpochLayout} {w fr addr : ℕ}
    (hv : fl.Valid w fr) (hba : fl.bpL.OwnsAddr addr) : fl.OwnsFastAddr addr := by
  rcases hba with hma | hia
  · exact fl.owns_of_bpMeta hv hma
  · exact Or.inr (Or.inr hia)

theorem FastEpochLayout.owns_of_fb {fl : FastEpochLayout} {w fr addr : ℕ}
    (hv : fl.Valid w fr) (hfa : fl.fbL.OwnsAddr addr) : fl.OwnsFastAddr addr := by
  rcases hfa with rfl | hba
  · exact Or.inl ⟨by dsimp [FastEpochLayout.fbL, FastEpochLayout.bpL, FastEpochLayout.mp,
      epochBpMetaLayout]; omega,
      by dsimp [FastEpochLayout.fbL, FastEpochLayout.bpL, FastEpochLayout.mp,
        epochBpMetaLayout]; omega⟩
  · exact fl.owns_of_bp hv hba

theorem FastEpochLayout.owns_of_trie {fl : FastEpochLayout} {w fr role addr : ℕ}
    (_hv : fl.Valid w fr) (hrole : role < 2) (hta : (fl.trieL role).OwnsAddr addr) :
    fl.OwnsFastAddr addr := by
  have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) hrole
  dsimp only [FastEpochLayout.trieL, epochTrieLayout, TrieLayout.OwnsAddr] at hta
  refine Or.inr (Or.inl ⟨?_, ?_⟩)
  · rcases hta with h1 | h2 | h3 <;> omega
  · rcases hta with h1 | h2 | h3 <;> omega

theorem FastEpochLayout.owns_of_btree {fl : FastEpochLayout} {w fr addr : ℕ}
    (hv : fl.Valid w fr) (hbt : fl.btL.OwnsAddr addr) : fl.OwnsFastAddr addr := by
  have hbv := hv.bt_valid
  have hd0 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd1 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd2 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) (role := 0) (by decide)
  dsimp only [FastEpochLayout.btL, epochBTreeLayout, BTreeEpochLayout.OwnsAddr,
    BTreeEpochLayout.totalNodes] at hbt hd0 hd1 hd2
  have htot : 3 * numBucketsWhp fl.N * nSliceWhp fl.N = totalBTreeNodesWhp fl.N := rfl
  rw [htot] at hbt hd1 hd2
  refine Or.inr (Or.inl ⟨?_, ?_⟩)
  · rcases hbt with h1 | h2 | h3 | h4 <;> omega
  · rcases hbt with h1 | h2 | h3 | h4 <;> omega

theorem FastEpochLayout.disj_btree_bpTable {fl : FastEpochLayout} {addr : ℕ}
    (hbt : fl.btL.OwnsAddr addr)
    (htab : (fl.metaBase + offSlabDir fl.c fl.w fl.N ≤ addr ∧
      addr < fl.metaBase + offBTreeMeta fl.c fl.w fl.N)) : False := by
  dsimp only [FastEpochLayout.btL, epochBTreeLayout, BTreeEpochLayout.OwnsAddr] at hbt
  have hd : offBktMeta fl.c fl.w fl.N +
      packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w ≤
      offSlabDir fl.c fl.w fl.N := Nat.le_refl _
  have hk : offBTreeMeta fl.c fl.w fl.N ≤ offBTreeKeys fl.c fl.w fl.N := Nat.le_add_right _ _
  have hv : offBTreeKeys fl.c fl.w fl.N ≤ offBTreeVals fl.c fl.w fl.N := Nat.le_add_right _ _
  rcases hbt with h1 | h2 | h3 | h4 <;> omega

theorem FastEpochLayout.disj_btree_trie {fl : FastEpochLayout} {w fr role addr : ℕ}
    (hv : fl.Valid w fr) (hrole : role < 2)
    (hbt : fl.btL.OwnsAddr addr) (htr : (fl.trieL role).OwnsAddr addr) : False := by
  have hbv := hv.bt_valid
  have hd0 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd1 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd2 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) hrole
  dsimp only [FastEpochLayout.btL, epochBTreeLayout, BTreeEpochLayout.OwnsAddr,
    BTreeEpochLayout.totalNodes] at hbt hd0 hd1 hd2
  dsimp only [FastEpochLayout.trieL, epochTrieLayout, TrieLayout.OwnsAddr] at htr
  have htot : 3 * numBucketsWhp fl.N * nSliceWhp fl.N = totalBTreeNodesWhp fl.N := rfl
  rw [htot] at hbt hd1 hd2
  rcases hbt with h1 | h2 | h3 | h4 <;> (rcases htr with t1 | t2 | t3 <;> omega)

theorem FastEpochLayout.disj_trie_bpAndMeta {fl : FastEpochLayout} {w fr role addr : ℕ}
    (hv : fl.Valid w fr) (hrole : role < 2) (htr : (fl.trieL role).OwnsAddr addr) :
    ¬((fl.metaBase ≤ addr ∧ addr < fl.metaBase + offTrieChild fl.c fl.w fl.N 0) ∨
      fl.io.OwnsAddr addr) := by
  have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) hrole
  have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := by
    have := hv.mp_valid.offBktMeta_ge
    dsimp [FastEpochLayout.mp, epochBpMetaLayout] at this; exact this
  dsimp only [FastEpochLayout.trieL, epochTrieLayout, TrieLayout.OwnsAddr] at htr
  have hbounds : fl.metaBase + offTrieChild fl.c fl.w fl.N 0 ≤ addr ∧
      addr < fl.metaBase + offPageDir fl.c fl.w fl.N := by
    rcases htr with t1 | t2 | t3 <;> exact ⟨by omega, by omega⟩
  rintro (⟨_, hlt⟩ | hia)
  · omega
  · exact hv.disj_fast_io addr (Or.inr ⟨by omega, hbounds.2⟩) hia

/-! ### `fastWriteMetaProg` and `fastWriteBktLaneProg` `FastProgPre` Corollaries -/

/-- Extracts the `pBase` parameter from a nested `((pBase, _), _)` fast-epoch program input. -/
abbrev fastArgPBase {α β : Type} (x : (ℕ × α) × β) : ℕ := x.1.1

theorem fastWriteMetaProg_pre {w : ℕ} {x : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (h : FastProgPre w (fastArgPBase x) s) :
    FastProgPre w (fastArgPBase x) ((Memory.spec 0).clientState s (fastWriteMetaProg x)) := by
  rcases x with ⟨⟨pBase, off⟩, val⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, fastWriteMetaProg_ready hr⟩

theorem fastWriteBktLaneProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × ℕ} {s : Memory.State}
    (h : FastProgPre w (fastArgPBase x) s) :
    FastProgPre w (fastArgPBase x) ((Memory.spec 0).clientState s (fastWriteBktLaneProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, lane⟩⟩, val⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastWriteBktLaneProg_frame hr).2.1⟩

/-- Exact `extractFastMeta` update for `fastWriteMetaProg`. -/
theorem extractFastMeta_writeMeta {fl : FastEpochLayout} {w off val : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hoff : (3 ≤ off ∧ off < 10) ∨ off = 17) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, off), val))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r s'.mem = extractBTreeSlice fl.btL b r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    extractFastMeta fl s'.mem =
      if off = 3 then { fm with curBufRole := val }
      else if off = 4 then { fm with subStep := val }
      else if off = 5 then { fm with drainPos := val }
      else if off = 6 then { fm with tryAct := val }
      else if off = 7 then { fm with tryBkt := val }
      else if off = 8 then { fm with trySalt := val }
      else if off = 9 then { fm with tryPos := val }
      else { fm with tryIns := val } := by
  dsimp only
  have hoff2 : (2 ≤ off ∧ off < 10) ∨ off = 17 := by omega
  have hst := clientState_fastWriteMetaProg (val := val) hr.2.1 hoff2
  have hv := hr.1
  have hmv := hv.mp_valid
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := by
    have := hmv.offBktMeta_ge; dsimp [FastEpochLayout.mp, epochBpMetaLayout] at this; exact this
  set s' := (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, off), val))
  have hmem_ne : ∀ addr, addr ≠ fl.metaBase + off → s'.mem addr = s.mem addr := fun addr hne => by
    rw [hst]; exact Function.update_of_ne hne val s.mem
  have hmem_self : s'.mem (fl.metaBase + off) = val := by rw [hst]; exact Function.update_self ..
  have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr := fun addr ha =>
    hmem_ne addr fun heq => ha (Or.inl ⟨by omega, by omega⟩)
  have hout_io : ∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr := fun addr hia =>
    hmem_ne addr fun heq => hv.disj_fast_io addr (Or.inl ⟨by omega, by omega⟩) hia
  have hbp_eq : extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem := by
    refine extractBlockPool_congr hw_pos hmv.K_ge (by
      have h := hmv.sixteen_MK_le_maxTail; rw [Nat.mul_assoc] at h; omega) fun addr hma => ?_
    refine hmem_ne addr fun heq => ?_
    rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | ⟨h10, h17⟩) | ⟨hlo, _⟩
    · dsimp [FastEpochLayout.mp, epochBpMetaLayout] at h1; omega
    · dsimp [FastEpochLayout.mp, epochBpMetaLayout] at h10 h17; omega
    · dsimp [FastEpochLayout.mp, epochBpMetaLayout] at hlo; omega
  have hbt_eq : ∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r s'.mem = extractBTreeSlice fl.btL b r s.mem := by
    intro b hb r hr_lt
    have hd_bt : offBktMeta fl.c fl.w fl.N ≤ offBTreeMeta fl.c fl.w fl.N := by
      unfold offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir; omega
    have hd_k : offBTreeMeta fl.c fl.w fl.N ≤ offBTreeKeys fl.c fl.w fl.N := Nat.le_add_right _ _
    have hd_v : offBTreeKeys fl.c fl.w fl.N ≤ offBTreeVals fl.c fl.w fl.N := Nat.le_add_right _ _
    refine extractBTreeSlice_congr_entries
      (readPacked_congr hw_pos (N := 16 * numBucketsWhp fl.N)
        (fun a ha => hmem_ne a (by dsimp [FastEpochLayout.btL, epochBTreeLayout] at ha; omega))
        (by omega))
      (readPacked_congr hw_pos (N := 16 * numBucketsWhp fl.N)
        (fun a ha => hmem_ne a (by dsimp [FastEpochLayout.btL, epochBTreeLayout] at ha; omega))
        (by omega))
      fun u hu => ?_
    dsimp only [FastEpochLayout.btL, epochBTreeLayout] at hu ⊢
    have htot : (3 * b + r) * nSliceWhp fl.N + u < totalBTreeNodesWhp fl.N := by
      unfold totalBTreeNodesWhp
      calc (3 * b + r) * nSliceWhp fl.N + u
          < (3 * b + r + 1) * nSliceWhp fl.N := by ring_nf; omega
        _ ≤ (3 * numBucketsWhp fl.N) * nSliceWhp fl.N := Nat.mul_le_mul_right _ (by omega)
    exact ⟨readPacked_congr hw_pos (fun a ha => hmem_ne a (by omega)) htot,
      readPacked_congr hw_pos (fun a ha => hmem_ne a (by omega)) htot,
      readPacked_congr hw_pos (fun a ha => hmem_ne a (by omega)) htot⟩
  have htr_eq : ∀ r < 2,
      extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem := by
    intro r hr_lt
    refine extractBufTrie_congr hw_pos fun addr hta => hmem_ne addr fun heq => ?_
    have hdisj := fl.disj_trie_bpAndMeta hv hr_lt hta
    apply hdisj; left
    have hc0 : 32 ≤ offTrieChild fl.c fl.w fl.N 0 := by
      unfold offTrieChild offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner
        offTailDir offSlabDir
      omega
    omega
  have hbkt_lanes : ∀ idx < 16 * numBucketsWhp fl.N,
      readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s'.mem idx =
        readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s.mem idx :=
    fun idx hi => readPacked_congr hw_pos (fun a ha => hmem_ne a (by omega)) hi
  refine ⟨by rw [hst], fastWriteMetaProg_ready hr, hbp_eq, hbt_eq, htr_eq, hout_io, hout_fast,
    hmem_ne _ (by omega), ?_⟩
  rcases (by omega : off = 3 ∨ off = 4 ∨ off = 5 ∨ off = 6 ∨ off = 7 ∨ off = 8 ∨ off = 9 ∨
      off = 17) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (
    repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
    unfold extractFastMeta; dsimp only
    congr 1
    all_goals first
      | exact hmem_ne _ (by omega)
      | (ext x; split_ifs with hx <;> [exact hbkt_lanes _ (by omega); rfl]))

/-- Exact `extractFastMeta` update for `fastWriteBktLaneProg`. -/
theorem extractFastMeta_writeBktLane {fl : FastEpochLayout} {w b lane val : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hb : b < numBucketsWhp fl.N)
    (hlane : lane = 5 ∨ (12 ≤ lane ∧ lane < 16)) (hval : val ≤ fl.N) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s (fastWriteBktLaneProg ((fl.pBase, (b, lane)), val))
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    extractFastMeta fl s'.mem =
      if lane = 5 then { fm with bktSalt := Function.update fm.bktSalt b val }
      else if lane = 12 then { fm with curRole := Function.update fm.curRole b val }
      else if lane = 13 then { fm with curIns := Function.update fm.curIns b val }
      else if lane = 14 then { fm with shadowIns := Function.update fm.shadowIns b val }
      else { fm with shadowCode := Function.update fm.shadowCode b val } := by
  dsimp only
  have hv := hr.1
  have hmv := hv.mp_valid
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := by
    have := hmv.offBktMeta_ge; dsimp [FastEpochLayout.mp, epochBpMetaLayout] at this; exact this
  have hval_pb : val < 2 ^ globalPtrBits fl.N := lt_of_le_of_lt hval hmv.nCap_lt_ptrB
  have hst := clientState_fastWriteBktLaneProg hr.2.1 hb hlane hval
  have hidx : 16 * b + lane < 16 * numBucketsWhp fl.N := by omega
  set s' := (Memory.spec 0).clientState s (fastWriteBktLaneProg ((fl.pBase, (b, lane)), val))
  have hsc : ∀ k < 32, s'.mem (fl.metaBase + k) = s.mem (fl.metaBase + k) := fun k hk => by
    rw [hst]; exact writePacked_outside hw_pos s.mem hidx val (by omega)
  have hlane_upd : ∀ l0, (l0 = 5 ∨ (12 ≤ l0 ∧ l0 < 16)) → ∀ x,
      (if x < numBucketsWhp fl.N then
        readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s'.mem
          (16 * x + l0) else 0) =
      if l0 = lane then
        Function.update
          (fun b' => if b' < numBucketsWhp fl.N then
            readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s.mem
              (16 * b' + l0) else 0) b val x
      else
        (if x < numBucketsWhp fl.N then
          readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s.mem
            (16 * x + l0) else 0) := by
    intro l0 hl0 x
    by_cases hl_eq : l0 = lane
    · subst hl_eq; rw [ite_eq_left rfl]
      by_cases hxb : x = b
      · subst hxb; rw [Function.update_self, ite_eq_left hb, hst]
        exact readPacked_writePacked_self _ _ _ s.mem _ hval_pb
      · rw [Function.update_of_ne hxb]
        split_ifs with hx
        · rw [hst]; exact readPacked_writePacked_of_ne hw_pos s.mem (by omega) val
        · rfl
    · rw [ite_eq_right hl_eq]
      split_ifs with hx
      · rw [hst]; exact readPacked_writePacked_of_ne hw_pos s.mem (by omega) val
      · rfl
  refine ⟨hsc 2 (by decide), ?_⟩
  rcases (by omega : lane = 5 ∨ lane = 12 ∨ lane = 13 ∨ lane = 14 ∨ lane = 15) with
    rfl | rfl | rfl | rfl | rfl
  all_goals (
    repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
    unfold extractFastMeta; dsimp only
    congr 1
    · exact hsc 3 (by decide)
    · exact hsc 4 (by decide)
    · exact hsc 5 (by decide)
    · exact hsc 6 (by decide)
    · exact hsc 7 (by decide)
    · exact hsc 8 (by decide)
    · exact hsc 9 (by decide)
    · exact hsc 17 (by decide)
    · ext x; simpa using hlane_upd 5 (Or.inl rfl) x
    · ext x; simpa using hlane_upd 12 (Or.inr ⟨by decide, by decide⟩) x
    · ext x; simpa using hlane_upd 13 (Or.inr ⟨by decide, by decide⟩) x
    · ext x; simpa using hlane_upd 14 (Or.inr ⟨by decide, by decide⟩) x
    · ext x; simpa using hlane_upd 15 (Or.inr ⟨by decide, by decide⟩) x)

/-! ### Mutating `BlockPool` and `FallbackPool` Wrappers (`fastBp*`, `fastEnterFallbackProg`) -/

/-- Initialize `BlockPool` metadata on a Phase-1 zeroed region via `pBase` (`¬ReadsWidth`). -/
def fastBpInitProg (pBase : ℕ) : Memory.Prog Unit := do
  let mctx ← loadBpMetaCtxProg pBase
  bpInitZeroedProg mctx

theorem fastBpInitProg_ready {w : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastBpInitProg fl.pBase)
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBpInitProg fl.pBase) s ≤ 19 ∧
    (∀ addr, ¬fl.mp.OwnsMetaAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  unfold fastBpInitProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_loadBpMetaCtxProg, clientResult_loadBpMetaCtxProg hr.2.1,
    memoryCost_loadBpMetaCtxProg]
  have hf := bpInitZeroedProg_frame hr.1.mp_valid.offBktMeta_ge hr.1.mp_valid.w_pos
  have hfr := hf.frame.frontier_eq s
  have hc := hf.frame.cost_le s
  have hout : ∀ addr, ¬fl.mp.OwnsMetaAddr addr →
      ((Memory.spec 0).clientState s (bpInitZeroedProg fl.mp.toCtx)).mem addr = s.mem addr :=
    hf.frame.mem_outside s
  exact ⟨hfr, hr.of_frame hfr (fun a ha => hout a (fun h => ha (fl.owns_of_bpMeta hr.1 h))),
    by omega, hout⟩

theorem fastBpInitProg_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (fastBpInitProg pBase)) := by
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBpInitProg_ready hr).2.1⟩

theorem realizesBounded_fastBpInit :
    RealizesBounded .exact fastBpInitProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlm := realizesBounded_loadBpMetaCtx
  have hiz := realizesBounded_bpInitZeroed
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    try simp only [StateTransitionSpec.clientState, runClient_state_loadBpMetaCtxProg] at *
    first | exact hw6 | exact hp | (
      have hl_res := clientResult_loadBpMetaCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]; simpa using hr.1.mp_valid))

/-- Read `bp.ownerOf 0` in `O(1)` time via `pBase` (`¬ReadsWidth`). -/
@[expose] def fastBpOwnerOfZeroProg (pBase : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let mctx ← loadBpMetaCtxProg pBase
  bpOwnerOfProg (mctx, 0)

@[simp] theorem runClient_state_fastBpOwnerOfZeroProg (pBase : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastBpOwnerOfZeroProg pBase)) = s := by
  change (Memory.spec 0).clientState s (fastBpOwnerOfZeroProg pBase) = s
  unfold fastBpOwnerOfZeroProg
  rw [StateTransitionSpec.clientState_bind, clientState_loadBpMetaCtxProg]
  exact clientState_bpOwnerOfProg _ s

theorem clientState_fastBpOwnerOfZeroProg (pBase : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastBpOwnerOfZeroProg pBase) = s :=
  runClient_state_fastBpOwnerOfZeroProg pBase s

theorem realizesBounded_fastBpOwnerOfZero :
    RealizesBounded .exact fastBpOwnerOfZeroProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlm := realizesBounded_loadBpMetaCtx
  have hoo := realizesBounded_bpOwnerOf
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    try simp only [StateTransitionSpec.clientState, runClient_state_loadBpMetaCtxProg] at *
    first | exact hw6 | exact hp | (
      have hl_res := clientResult_loadBpMetaCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]; simpa using hr.1.mp_valid))

/-- Overwrite `(q, v)` at `(b, loc)` in `BlockPool` via `pBase` (`¬ReadsWidth`). -/
@[expose] def fastBpWriteAtProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, bl), qv) => do
    let bpCtx ← loadBlockPoolCtxProg pBase
    bpWriteAtRawProg ((bpCtx, bl), qv)

theorem fastBpWriteAtProg_ready {w : ℕ} {fl : FastEpochLayout} {b loc q v : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastBpWriteAtProg ((fl.pBase, (b, loc)), (q, v)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBpWriteAtProg ((fl.pBase, (b, loc)), (q, v))) s ≤ 75 ∧
    (∀ addr, ¬fl.bpL.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  unfold fastBpWriteAtProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_loadBlockPoolCtxProg, clientResult_loadBlockPoolCtxProg hr.2.1,
    memoryCost_loadBlockPoolCtxProg]
  have hf := (bpWriteAtProg_frame hr.1.bp_valid b loc q v).frame
  unfold bpWriteAtProg at hf
  exact ⟨hf.frontier_eq s,
    hr.of_frame (hf.frontier_eq s)
      (fun a ha => hf.mem_outside s a (fun h => ha (fl.owns_of_bp hr.1 h))),
    by have := hf.cost_le s; omega, hf.mem_outside s⟩

theorem fastBpWriteAtProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : FastProgPre w (fastArgPBase x) s) :
    FastProgPre w (fastArgPBase x) ((Memory.spec 0).clientState s (fastBpWriteAtProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, loc⟩⟩, ⟨q, v⟩⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBpWriteAtProg_ready hr).2.1⟩

theorem realizesBounded_fastBpWriteAt :
    RealizesBounded .exact fastBpWriteAtProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlb := realizesBounded_loadBlockPoolCtx
  have hbw := realizesBounded_bpWriteAtRaw
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, loc⟩⟩, ⟨q, v⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    try simp only [StateTransitionSpec.clientState, runClient_state_loadBlockPoolCtxProg] at *
    first | exact hw6 | exact hp | (
      have hl_res := clientResult_loadBlockPoolCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]; dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
      first | (rw [BpMetaLayout.ofCtx_toCtx]; exact hr.1.mp_valid)
            | (rw [SlotIoLayout.ofCtx_toCtx]; exact hr.1.io_valid)))

/-- Append `(q, v)` to bucket `b` in `BlockPool` via `pBase` (`¬ReadsWidth`). -/
@[expose] def fastBpAppendProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, b), qv) => do
    let bpCtx ← loadBlockPoolCtxProg pBase
    bpAppendRawProg ((bpCtx, b), qv)

theorem fastBpAppendProg_ready {w : ℕ} {fl : FastEpochLayout} {b q v : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastBpAppendProg ((fl.pBase, b), (q, v)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBpAppendProg ((fl.pBase, b), (q, v))) s ≤ 5327 ∧
    (∀ b' < fl.mp.M, ∀ sl', 5 ≤ sl' → sl' < 16 →
      readPacked (fl.mp.metaBase + fl.mp.offBktMeta) fl.mp.ptrB fl.mp.w s'.mem (16 * b' + sl') =
        readPacked (fl.mp.metaBase + fl.mp.offBktMeta) fl.mp.ptrB fl.mp.w s.mem (16 * b' + sl')) ∧
    (∀ addr, ¬fl.bpL.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  unfold fastBpAppendProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_loadBlockPoolCtxProg, clientResult_loadBlockPoolCtxProg hr.2.1,
    memoryCost_loadBlockPoolCtxProg]
  have hbp := bpAppendProg_frame hr.1.bp_valid b q v
  unfold bpAppendProg at hbp
  exact ⟨hbp.frame.frontier_eq s,
    hr.of_frame (hbp.frame.frontier_eq s)
      (fun a ha => hbp.frame.mem_outside s a (fun h => ha (fl.owns_of_bp hr.1 h))),
    by have := hbp.frame.cost_le s; omega,
    fun b' hb' sl' h5 h16 => hbp.bkt_other s b' sl' hb' h5 h16,
    hbp.frame.mem_outside s⟩

theorem fastBpAppendProg_pre {w : ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (h : FastProgPre w (fastArgPBase x) s) :
    FastProgPre w (fastArgPBase x) ((Memory.spec 0).clientState s (fastBpAppendProg x)) := by
  rcases x with ⟨⟨pBase, b⟩, ⟨q, v⟩⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBpAppendProg_ready hr).2.1⟩

theorem realizesBounded_fastBpAppend :
    RealizesBounded .exact fastBpAppendProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlb := realizesBounded_loadBlockPoolCtx
  have hba := realizesBounded_bpAppendRaw
  realize
  all_goals (
    rcases d with ⟨⟨pBase, b⟩, ⟨q, v⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    try simp only [StateTransitionSpec.clientState, runClient_state_loadBlockPoolCtxProg] at *
    first | exact hw6 | exact hp | (
      have hl_res := clientResult_loadBlockPoolCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]; dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
      first | (rw [BpMetaLayout.ofCtx_toCtx]; exact hr.1.mp_valid)
            | (rw [SlotIoLayout.ofCtx_toCtx]; exact hr.1.io_valid)))

/-- Pop `(b, bktCount b - 1)` from `BlockPool` via `pBase` (`¬ReadsWidth`). -/
@[expose] def fastBpPopBktBackProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, b) => do
    let bpCtx ← loadBlockPoolCtxProg pBase
    bpPopBktBackRawProg (bpCtx, b)

theorem fastBpPopBktBackProg_ready {w : ℕ} {fl : FastEpochLayout} {b : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastBpPopBktBackProg (fl.pBase, b))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBpPopBktBackProg (fl.pBase, b)) s ≤ 8527 ∧
    (∀ b' < fl.mp.M, ∀ sl', 5 ≤ sl' → sl' < 16 →
      readPacked (fl.mp.metaBase + fl.mp.offBktMeta) fl.mp.ptrB fl.mp.w s'.mem (16 * b' + sl') =
        readPacked (fl.mp.metaBase + fl.mp.offBktMeta) fl.mp.ptrB fl.mp.w s.mem (16 * b' + sl')) ∧
    (∀ addr, ¬fl.bpL.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  unfold fastBpPopBktBackProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_loadBlockPoolCtxProg, clientResult_loadBlockPoolCtxProg hr.2.1,
    memoryCost_loadBlockPoolCtxProg]
  have hbp := bpPopBktBackProg_frame hr.1.bp_valid b
  unfold bpPopBktBackProg at hbp
  exact ⟨hbp.frame.frontier_eq s,
    hr.of_frame (hbp.frame.frontier_eq s)
      (fun a ha => hbp.frame.mem_outside s a (fun h => ha (fl.owns_of_bp hr.1 h))),
    by have := hbp.frame.cost_le s; omega,
    fun b' hb' sl' h5 h16 => hbp.bkt_other s b' sl' hb' h5 h16,
    hbp.frame.mem_outside s⟩

theorem fastBpPopBktBackProg_pre {w : ℕ} {x : ℕ × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1 s) :
    FastProgPre w x.1 ((Memory.spec 0).clientState s (fastBpPopBktBackProg x)) := by
  rcases x with ⟨pBase, b⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBpPopBktBackProg_ready hr).2.1⟩

theorem realizesBounded_fastBpPopBktBack :
    RealizesBounded .exact fastBpPopBktBackProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlb := realizesBounded_loadBlockPoolCtx
  have hbp := realizesBounded_bpPopBktBackRaw
  realize
  all_goals (
    rcases d with ⟨pBase, b⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    try simp only [StateTransitionSpec.clientState, runClient_state_loadBlockPoolCtxProg] at *
    first | exact hw6 | exact hp | (
      have hl_res := clientResult_loadBlockPoolCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]; dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
      first | (rw [BpMetaLayout.ofCtx_toCtx]; exact hr.1.mp_valid)
            | (rw [SlotIoLayout.ofCtx_toCtx]; exact hr.1.io_valid)))

/-- Transition in-place from any `CoreValid` `BlockPoolState` into `FallbackPool` (`fallbackMode =
1`) via `pBase` (`¬ReadsWidth`). -/
def fastEnterFallbackProg (pBase : ℕ) : Memory.Prog Unit := do
  let bpCtx ← loadBlockPoolCtxProg pBase
  enterFallbackProg bpCtx

theorem realizesBounded_fastEnterFallback :
    RealizesBounded .exact fastEnterFallbackProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlb := realizesBounded_loadBlockPoolCtx
  have hef := realizesBounded_enterFallback
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    try simp only [StateTransitionSpec.clientState, runClient_state_loadBlockPoolCtxProg] at *
    first | exact hw6 | exact hp | (
      have hl_res := clientResult_loadBlockPoolCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]; dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
      first | (rw [BpMetaLayout.ofCtx_toCtx]; exact hr.1.mp_valid)
            | (rw [SlotIoLayout.ofCtx_toCtx]; exact hr.1.io_valid)))

theorem fastEnterFallbackProg_spec {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hr : FastLayoutReady w fl s)
    (hN : s.mem fl.metaBase = fl.N)
    (hseed : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s.mem)
    (hcv : (extractBlockPool fl.mp s.mem).CoreValid)
    (hns_le : (extractBlockPool fl.mp s.mem).nSide ≤ fl.N)
    (hio : fl.io.StateInv (extractBlockPool fl.mp s.mem).nSide slack s.mem)
    (href : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt)
      (extractBlockPool fl.mp s.mem).nSide
      (fun p => ((extractBlockPool fl.mp s.mem).ownerOf p).1)
      (slotIoPairAt fl.io s.mem) s_abs) :
    let s' := (Memory.spec 0).clientState s (fastEnterFallbackProg fl.pBase)
    s'.frontier = s.frontier ∧
    fl.ParamTable s'.mem ∧
    (extractFallback fl.mp s'.mem).nSide = (extractBlockPool fl.mp s.mem).nSide ∧
    fl.fbL.StateInv slack seeds.bkt s'.mem s_abs ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      extractPageUnperm fl.io.pgL s'.mem = extractPageUnperm fl.io.pgL s.mem ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  unfold fastEnterFallbackProg
  rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
    clientResult_loadBlockPoolCtxProg hr.2.1]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  obtain ⟨hfr, hns, hinv, hout, hpg⟩ := enterFallbackProg_spec (fl := fl.fbL)
    hr.1.fb_valid hN hseed hcv hns_le hio href
  dsimp only [FastEpochLayout.fbL, FastEpochLayout.bpL] at hfr hns hpg ⊢
  have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr →
      ((Memory.spec 0).clientState s (enterFallbackProg (fl.mp.toCtx, fl.io.toCtx))).mem addr =
        s.mem addr :=
    fun addr ha => hout addr (fun hfa => ha (fl.owns_of_fb hr.1 hfa))
  have hr' := hr.of_frame hfr hout_fast
  exact ⟨hfr, hr'.2.1, hns, hinv, hout_fast, hpg⟩

/-! ### Mutating `BufTrie` Wrappers (`fastBufInitEmpty`, `fastBufLookup`, `fastBufInsert`,
`fastBufDelete`, `fastBufCheckSlot`, `fastBufClearSteps`) -/

/-- Initialize `BufTrie` `role ∈ {0, 1}` on a zeroed metadata slice by setting `nodeAlloc := 1`
(`¬ReadsWidth`). -/
def fastBufInitEmptyProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, role) =>
    if role < 2 then do
      let kOi ← pure (if role = 0 then 43 else 44)
      let mbOi ← readParam2Prog (pBase, (1, kOi))
      let pbw ← readParam2Prog (pBase, (10, 2))
      let qm ← Memory.read (pBase + 23)
      writePackedCompGenProg (((mbOi, pbw), 6 * qm), 1)
    else
      pure ()

theorem fastBufInitEmptyProg_ready {w : ℕ} {fl : FastEpochLayout} {role : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastBufInitEmptyProg (fl.pBase, role))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBufInitEmptyProg (fl.pBase, role)) s ≤ 10 ∧
    (role < 2 →
      s'.mem = writePacked (fl.metaBase + (fl.trieL role).offItem) (globalPtrBits fl.N) fl.w s.mem
        (6 * qEpochWhp fl.N) 1 ∧
      ∀ addr, ¬(fl.trieL role).OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  have ⟨hv, hpt, _, _⟩ := hr
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  by_cases hrole : role < 2
  · have hmbOi : (Memory.spec 0).clientResult s
        (readParam2Prog (fl.pBase, (1, if role = 0 then 43 else 44))) =
        (fl.metaBase, (fl.trieL role).offItem) := by
      unfold readParam2Prog
      rcases role with _ | _ | _ <;> try omega
      all_goals simp [hpt 1 (by decide), hpt 43 (by decide), hpt 44 (by decide),
        FastEpochLayout.paramWord, FastEpochLayout.trieL, epochTrieLayout]
    have hpbw : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (10, 2))) =
        (globalPtrBits fl.N, fl.w) := by
      unfold readParam2Prog
      simp [hpt 10 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
    have hqm : s.mem (fl.pBase + 23) = qEpochWhp fl.N := hpt 23 (by decide)
    have hst : (Memory.spec 0).clientState s (fastBufInitEmptyProg (fl.pBase, role)) =
        ⟨writePacked (fl.metaBase + (fl.trieL role).offItem) (globalPtrBits fl.N) fl.w s.mem
          (6 * qEpochWhp fl.N) 1, s.frontier⟩ := by
      unfold fastBufInitEmptyProg; dsimp only
      rw [ite_eq_left hrole, pure_bind, StateTransitionSpec.clientState_bind,
        clientState_readParam2Prog, hmbOi, StateTransitionSpec.clientState_bind,
        clientState_readParam2Prog, hpbw, StateTransitionSpec.clientState_bind]
      simp [hqm, StateTransitionSpec.clientState]
    have hcost : memoryCost (fastBufInitEmptyProg (fl.pBase, role)) s ≤ 10 := by
      unfold fastBufInitEmptyProg; dsimp only
      rw [ite_eq_left hrole, pure_bind, Realization.memoryCost_bind',
        clientState_readParam2Prog]
      have c1 : memoryCost (readParam2Prog (fl.pBase, (1, if role = 0 then 43 else 44))) s = 2 :=
        by unfold readParam2Prog; simp
      have c2 : memoryCost (readParam2Prog (fl.pBase, (10, 2))) s = 2 := by
        unfold readParam2Prog; simp
      rw [c1, hmbOi, Realization.memoryCost_bind', clientState_readParam2Prog, c2, hpbw,
        Realization.memoryCost_bind']
      simp only [prog_memoryCost_read, prog_runClient_state_read, StateTransitionSpec.clientState,
        prog_clientResult_read, hqm, memoryCost_writePackedCompGenProg]
      omega
    have hout_tr : ∀ addr, ¬(fl.trieL role).OwnsAddr addr →
        ((Memory.spec 0).clientState s (fastBufInitEmptyProg (fl.pBase, role))).mem addr =
          s.mem addr := fun addr ha => by
      rw [hst]
      exact writePacked_outside hw_pos s.mem
        (N := 6 * qEpochWhp fl.N + 6) (by omega) 1
        (fun h => ha (Or.inr (Or.inr h)))
    have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr →
        ((Memory.spec 0).clientState s (fastBufInitEmptyProg (fl.pBase, role))).mem addr =
          s.mem addr := fun addr ha =>
      hout_tr addr (fun h => ha (fl.owns_of_trie hv hrole h))
    exact ⟨by rw [hst], hr.of_frame (by rw [hst]) hout_fast, hcost,
      fun _ => ⟨by rw [hst], hout_tr⟩⟩
  · have hst : (Memory.spec 0).clientState s (fastBufInitEmptyProg (fl.pBase, role)) = s := by
      unfold fastBufInitEmptyProg; simp [hrole]
    have hc : memoryCost (fastBufInitEmptyProg (fl.pBase, role)) s = 0 := by
      unfold fastBufInitEmptyProg; simp [hrole]
    rw [hst]
    exact ⟨rfl, hr, by omega, fun h => absurd h hrole⟩

theorem fastBufInitEmptyProg_pre {w : ℕ} {x : ℕ × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1 s) :
    FastProgPre w x.1 ((Memory.spec 0).clientState s (fastBufInitEmptyProg x)) := by
  rcases x with ⟨pBase, role⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBufInitEmptyProg_ready hr).2.1⟩

theorem realizesBounded_fastBufInitEmpty :
    RealizesBounded .exact fastBufInitEmptyProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrp := realizesBounded_readParam2
  have hwk := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨pBase, role⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have ⟨hv, hpt, _, _⟩ := hr
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_readParam2Prog] at *
    first | exact hw6 | exact hp | omega | (split_ifs <;> omega) | (
      have hrole : role < 2 := by assumption
      have htv := hv.trie_valid hrole
      cases hv.w_eq
      have h6q : 6 * qEpochWhp fl.N + 6 < 2 ^ fl.w := htv.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hqm : s.mem (fl.pBase + 23) = qEpochWhp fl.N := hpt 23 (by decide)
      first | (simp only [hqm]; omega) | (
        have hmbOi : ((Memory.spec 0).runClient s
            (readParam2Prog (fl.pBase, (1, if role = 0 then 43 else 44)))).1 =
            (fl.metaBase, (fl.trieL role).offItem) := by
          rcases role with _ | _ | _ <;> [skip; skip; omega]
          all_goals (
            unfold readParam2Prog
            simp [hpt 1 (by decide), hpt 43 (by decide), hpt 44 (by decide),
              FastEpochLayout.paramWord, FastEpochLayout.trieL, epochTrieLayout])
        have hpbw : ((Memory.spec 0).runClient s (readParam2Prog (fl.pBase, (10, 2)))).1 =
            (globalPtrBits fl.N, fl.w) := by
          unfold readParam2Prog
          simp [hpt 10 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
        simp only [StateTransitionSpec.clientResult, hmbOi, hpbw, hqm]
        dsimp only [FastEpochLayout.trieL, epochTrieLayout] at htv ⊢
        exact ⟨6 * qEpochWhp fl.N + 6, hv.w_pos, rfl, htv.2.2.1, by omega,
          htv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩)))

/-- `bufLookup` via `pBase` (`¬ReadsWidth`). -/
def fastBufLookupProg : (ℕ × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((pBase, role), rk) =>
    if role < 2 then do
      let tctx ← loadTrieCtxProg (pBase, role)
      bufLookupBoundedProg (tctx, rk)
    else
      pure (0, (0, 0))

@[simp] theorem runClient_state_fastBufLookupProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastBufLookupProg x)) = s := by
  rcases x with ⟨⟨pBase, role⟩, rk⟩
  unfold clientOutState fastBufLookupProg; dsimp only
  split_ifs
  · rw [prog_runClient_state_bind, clientState_loadTrieCtxProg]
    exact clientState_bufLookupBoundedProg _ s
  · rfl

theorem clientState_fastBufLookupProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastBufLookupProg x) = s :=
  runClient_state_fastBufLookupProg x s

theorem realizesBounded_fastBufLookup :
    RealizesBounded .exact fastBufLookupProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlt := realizesBounded_loadTrieCtx
  have hbl := realizesBounded_bufLookup
  realize
  all_goals (
    rcases d with ⟨⟨pBase, role⟩, rk⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_loadTrieCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have hl_res := clientResult_loadTrieCtxProg hr.2.1 ‹role < 2› (s := s)
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      dsimp only [BufLookupPre, TrieLayout.ofCtx, TrieLayout.toCtx]
      exact hr.1.w_eq.symm ▸ hr.1.trie_valid ‹role < 2›))

/-- `bufInsert` via `pBase` (`¬ReadsWidth`). -/
@[expose] def fastBufInsertProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((pBase, role), rbl) =>
    if role < 2 then do
      let tctx ← loadTrieCtxProg (pBase, role)
      bufInsertBoundedProg (tctx, rbl)
    else
      pure ()

theorem fastBufInsertProg_ready {w : ℕ} {fl : FastEpochLayout} {role rk b loc : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastBufInsertProg ((fl.pBase, role), (rk, (b, loc))))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBufInsertProg ((fl.pBase, role), (rk, (b, loc)))) s ≤
      24 * cTabWhp fl.c + 42 ∧
    (role < 2 → ∀ addr, ¬(fl.trieL role).OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  by_cases hrole : role < 2
  · unfold fastBufInsertProg; dsimp only
    rw [ite_eq_left hrole, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_loadTrieCtxProg, clientResult_loadTrieCtxProg hr.2.1 hrole,
      memoryCost_loadTrieCtxProg]
    obtain ⟨hfr, hc, hout⟩ := bufInsertBoundedProg_frame (hr.1.trie_valid hrole) rk b loc
    have hct : (fl.trieL role).cTab = cTabWhp fl.c := rfl
    rw [hct] at hc
    have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr →
        ((Memory.spec 0).clientState s
          (bufInsertBoundedProg ((fl.trieL role).toCtx, (rk, (b, loc))))).mem addr = s.mem addr :=
      fun addr ha => hout addr (fun h => ha (fl.owns_of_trie hr.1 hrole h))
    exact ⟨hfr, hr.of_frame hfr hout_fast, by omega, fun _ => hout⟩
  · have hst : (Memory.spec 0).clientState s
        (fastBufInsertProg ((fl.pBase, role), (rk, (b, loc)))) = s := by
      unfold fastBufInsertProg; simp [hrole]
    have hc : memoryCost (fastBufInsertProg ((fl.pBase, role), (rk, (b, loc)))) s = 0 := by
      unfold fastBufInsertProg; simp [hrole]
    rw [hst]
    exact ⟨rfl, hr, by omega, fun h => absurd h hrole⟩

theorem fastBufInsertProg_pre {w : ℕ} {x : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))} {s : Memory.State}
    (h : FastProgPre w (fastArgPBase x) s) :
    FastProgPre w (fastArgPBase x) ((Memory.spec 0).clientState s (fastBufInsertProg x)) := by
  rcases x with ⟨⟨pBase, role⟩, ⟨rk, ⟨b, loc⟩⟩⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBufInsertProg_ready hr).2.1⟩

theorem realizesBounded_fastBufInsert :
    RealizesBounded .exact fastBufInsertProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlt := realizesBounded_loadTrieCtx
  have hbi := realizesBounded_bufInsert
  realize
  all_goals (
    rcases d with ⟨⟨pBase, role⟩, ⟨rk, ⟨b, loc⟩⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_loadTrieCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have hl_res := clientResult_loadTrieCtxProg hr.2.1 ‹role < 2› (s := s)
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      dsimp only [BufInsertPre, TrieLayout.ofCtx, TrieLayout.toCtx]
      exact hr.1.w_eq.symm ▸ hr.1.trie_valid ‹role < 2›))

/-- `bufDelete` via `pBase` (`¬ReadsWidth`). -/
def fastBufDeleteProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((pBase, role), rk) =>
    if role < 2 then do
      let tctx ← loadTrieCtxProg (pBase, role)
      bufDeleteBoundedProg (tctx, rk)
    else
      pure ()

theorem fastBufDeleteProg_ready {w : ℕ} {fl : FastEpochLayout} {role rk : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastBufDeleteProg ((fl.pBase, role), rk))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBufDeleteProg ((fl.pBase, role), rk)) s ≤ 2 * cTabWhp fl.c + 18 ∧
    (role < 2 →
      extractBufTrie (fl.trieL role) s'.mem =
        bufDelete (cTabWhp fl.c) (bCharWhp fl.N) (extractBufTrie (fl.trieL role) s.mem) rk ∧
      ∀ addr, ¬(fl.trieL role).OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  by_cases hrole : role < 2
  · unfold fastBufDeleteProg; dsimp only
    rw [ite_eq_left hrole, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_loadTrieCtxProg, clientResult_loadTrieCtxProg hr.2.1 hrole,
      memoryCost_loadTrieCtxProg]
    obtain ⟨hfr, hc, hext, hout⟩ := bufDeleteBoundedProg_spec (hr.1.trie_valid hrole) rk
    have hct : (fl.trieL role).cTab = cTabWhp fl.c := rfl
    have hbc : (fl.trieL role).bChar = bCharWhp fl.N := rfl
    rw [hct] at hc; rw [hct, hbc] at hext
    have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr →
        ((Memory.spec 0).clientState s
          (bufDeleteBoundedProg ((fl.trieL role).toCtx, rk))).mem addr = s.mem addr :=
      fun addr ha => hout addr (fun h => ha (fl.owns_of_trie hr.1 hrole h))
    exact ⟨hfr, hr.of_frame hfr hout_fast, by omega, fun _ => ⟨hext, hout⟩⟩
  · have hst : (Memory.spec 0).clientState s (fastBufDeleteProg ((fl.pBase, role), rk)) = s := by
      unfold fastBufDeleteProg; simp [hrole]
    have hc : memoryCost (fastBufDeleteProg ((fl.pBase, role), rk)) s = 0 := by
      unfold fastBufDeleteProg; simp [hrole]
    rw [hst]
    exact ⟨rfl, hr, by omega, fun h => absurd h hrole⟩

theorem fastBufDeleteProg_pre {w : ℕ} {x : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (h : FastProgPre w (fastArgPBase x) s) :
    FastProgPre w (fastArgPBase x) ((Memory.spec 0).clientState s (fastBufDeleteProg x)) := by
  rcases x with ⟨⟨pBase, role⟩, rk⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBufDeleteProg_ready hr).2.1⟩

theorem realizesBounded_fastBufDelete :
    RealizesBounded .exact fastBufDeleteProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlt := realizesBounded_loadTrieCtx
  have hbd := realizesBounded_bufDelete
  realize
  all_goals (
    rcases d with ⟨⟨pBase, role⟩, rk⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_loadTrieCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have hl_res := clientResult_loadTrieCtxProg hr.2.1 ‹role < 2› (s := s)
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      dsimp only [BufLookupPre, TrieLayout.ofCtx, TrieLayout.toCtx]
      exact hr.1.w_eq.symm ▸ hr.1.trie_valid ‹role < 2›))

/-- `bufCheckSlot` via `pBase` (`¬ReadsWidth`). -/
def fastBufCheckSlotProg : (ℕ × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((pBase, role), id) =>
    if role < 2 then do
      let tctx ← loadTrieCtxProg (pBase, role)
      bufCheckSlotBoundedProg (tctx, id)
    else
      pure (0, (0, 0))

@[simp] theorem runClient_state_fastBufCheckSlotProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastBufCheckSlotProg x)) = s := by
  rcases x with ⟨⟨pBase, role⟩, id⟩
  unfold clientOutState fastBufCheckSlotProg; dsimp only
  split_ifs
  · rw [prog_runClient_state_bind, clientState_loadTrieCtxProg]
    exact clientState_bufCheckSlotBoundedProg _ s
  · rfl

theorem clientState_fastBufCheckSlotProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastBufCheckSlotProg x) = s :=
  runClient_state_fastBufCheckSlotProg x s

theorem realizesBounded_fastBufCheckSlot :
    RealizesBounded .exact fastBufCheckSlotProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlt := realizesBounded_loadTrieCtx
  have hcs := realizesBounded_bufCheckSlot
  realize
  all_goals (
    rcases d with ⟨⟨pBase, role⟩, id⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_loadTrieCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have hl_res := clientResult_loadTrieCtxProg hr.2.1 ‹role < 2› (s := s)
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      dsimp only [BufLookupPre, TrieLayout.ofCtx, TrieLayout.toCtx]
      exact hr.1.w_eq.symm ▸ hr.1.trie_valid ‹role < 2›))

/-- Run `4 * (cTabWhp c + 2)` `bufClearOne` steps on `role ∈ {0, 1}` via `pBase` (`¬ReadsWidth`).
-/
def fastBufClearStepsProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, role) =>
    if role < 2 then do
      let k ← Memory.read (pBase + 28)
      let tctx ← loadTrieCtxProg (pBase, role)
      bufClearStepsBoundedProg (tctx, k)
    else
      pure ()

theorem fastBufClearStepsProg_ready {w : ℕ} {fl : FastEpochLayout} {role : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastBufClearStepsProg (fl.pBase, role))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBufClearStepsProg (fl.pBase, role)) s ≤ 96 * (cTabWhp fl.c + 2) + 11 ∧
    (role < 2 → ∀ addr, ¬(fl.trieL role).OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  by_cases hrole : role < 2
  · have hm28 : s.mem (fl.pBase + 28) = 4 * (cTabWhp fl.c + 2) := hr.2.1 28 (by decide)
    unfold fastBufClearStepsProg; dsimp only
    rw [ite_eq_left hrole]
    have hr_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 28)) = s := rfl
    have hr_res : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 28)) =
        4 * (cTabWhp fl.c + 2) := hm28
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hr_st, hr_res,
      prog_memoryCost_read, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_loadTrieCtxProg, clientResult_loadTrieCtxProg hr.2.1 hrole,
      memoryCost_loadTrieCtxProg]
    obtain ⟨hfr, hc, hout⟩ :=
      bufClearStepsBoundedProg_frame (hr.1.trie_valid hrole) (4 * (cTabWhp fl.c + 2)) s
    have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr →
        ((Memory.spec 0).clientState s
          (bufClearStepsBoundedProg ((fl.trieL role).toCtx, 4 * (cTabWhp fl.c + 2)))).mem addr =
          s.mem addr :=
      fun addr ha => hout addr (fun h => ha (fl.owns_of_trie hr.1 hrole h))
    exact ⟨hfr, hr.of_frame hfr hout_fast, by omega, fun _ => hout⟩
  · have hst : (Memory.spec 0).clientState s (fastBufClearStepsProg (fl.pBase, role)) = s := by
      unfold fastBufClearStepsProg; simp [hrole]
    have hc : memoryCost (fastBufClearStepsProg (fl.pBase, role)) s = 0 := by
      unfold fastBufClearStepsProg; simp [hrole]
    rw [hst]
    exact ⟨rfl, hr, by omega, fun h => absurd h hrole⟩

theorem fastBufClearStepsProg_pre {w : ℕ} {x : ℕ × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1 s) :
    FastProgPre w x.1 ((Memory.spec 0).clientState s (fastBufClearStepsProg x)) := by
  rcases x with ⟨pBase, role⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBufClearStepsProg_ready hr).2.1⟩

theorem realizesBounded_fastBufClearSteps :
    RealizesBounded .exact fastBufClearStepsProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlt := realizesBounded_loadTrieCtx
  have hbc := realizesBounded_bufClearSteps
  realize
  all_goals (
    rcases d with ⟨pBase, role⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_loadTrieCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have hl_res := clientResult_loadTrieCtxProg hr.2.1 ‹role < 2› (s := s)
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      dsimp only [BufLookupPre, TrieLayout.ofCtx, TrieLayout.toCtx]
      exact hr.1.w_eq.symm ▸ hr.1.trie_valid ‹role < 2›))

/-! ### Mutating SWAR B+-Tree Slice Wrappers (`fastBTreeReset`, `fastBTreeLookup`,
`fastBTreeDelete`, `fastBTreeUpdate`, `fastBTreeInsert`) -/

/-- Reset `BTreeSlice (b, role)` (`b < M, role < 3`) in `O(1)` time by zeroing `alloc` and `root`
(`lanes 6 + 2 * role` and `7 + 2 * role` in `offBktMeta`, `¬ReadsWidth`). -/
def fastBTreeResetProg : ℕ × (ℕ × ℕ) → Memory.Prog Unit
  | (pBase, (b, role)) => do
    let M ← Memory.read (pBase + 11)
    if b < M ∧ role < 3 then do
      let mbObm ← readParam2Prog (pBase, (1, 31))
      let pbw ← readParam2Prog (pBase, (10, 2))
      writePackedCompGenProg (((mbObm, pbw), 16 * b + 6 + 2 * role), 0)
      writePackedCompGenProg (((mbObm, pbw), 16 * b + 7 + 2 * role), 0)
    else
      pure ()

theorem fastBTreeResetProg_spec {w : ℕ} {fl : FastEpochLayout} {b role : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastBTreeResetProg (fl.pBase, (b, role)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBTreeResetProg (fl.pBase, (b, role))) s ≤ 14 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (b < numBucketsWhp fl.N → role < 3 →
      ValidWhpSlice fl.N 0 (extractBTreeSlice fl.btL b role s'.mem) (fun _ => none) ∧
      ∀ b' < numBucketsWhp fl.N, ∀ role' < 3, (b' ≠ b ∨ role' ≠ role) →
        extractBTreeSlice fl.btL b' role' s'.mem = extractBTreeSlice fl.btL b' role' s.mem) := by
  dsimp only
  have ⟨hv, hpt, _, _⟩ := hr
  have hmv := hv.mp_valid
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := by
    have := hmv.offBktMeta_ge; dsimp [FastEpochLayout.mp, epochBpMetaLayout] at this; exact this
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  by_cases hcond : b < numBucketsWhp fl.N ∧ role < 3
  · obtain ⟨hb, hrole⟩ := hcond
    have hmbObm : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (1, 31))) =
        (fl.metaBase, offBktMeta fl.c fl.w fl.N) := by
      unfold readParam2Prog
      simp [hpt 1 (by decide), hpt 31 (by decide), FastEpochLayout.paramWord]
    have hpbw : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (10, 2))) =
        (globalPtrBits fl.N, fl.w) := by
      unfold readParam2Prog
      simp [hpt 10 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
    set m1 := writePacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w
      s.mem (16 * b + 6 + 2 * role) 0
    set m2 := writePacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w
      m1 (16 * b + 7 + 2 * role) 0
    have hst : (Memory.spec 0).clientState s (fastBTreeResetProg (fl.pBase, (b, role))) =
        ⟨m2, s.frontier⟩ := by
      unfold fastBTreeResetProg; dsimp only
      have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
      have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
          numBucketsWhp fl.N := hm11
      rw [StateTransitionSpec.clientState_bind, hr11_st, hr11_r, ite_eq_left ⟨hb, hrole⟩,
        StateTransitionSpec.clientState_bind, clientState_readParam2Prog, hmbObm,
        StateTransitionSpec.clientState_bind, clientState_readParam2Prog, hpbw,
        StateTransitionSpec.clientState_bind, clientState_writePackedCompGenProg,
        clientState_writePackedCompGenProg]
    have hcost : memoryCost (fastBTreeResetProg (fl.pBase, (b, role))) s ≤ 14 := by
      unfold fastBTreeResetProg; dsimp only
      have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
      have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
          numBucketsWhp fl.N := hm11
      have c1 : memoryCost (readParam2Prog (fl.pBase, (1, 31))) s = 2 := by
        unfold readParam2Prog; simp
      have c2 : memoryCost (readParam2Prog (fl.pBase, (10, 2))) s = 2 := by
        unfold readParam2Prog; simp
      rw [Realization.memoryCost_bind', hr11_st, hr11_r, prog_memoryCost_read,
        ite_eq_left ⟨hb, hrole⟩, Realization.memoryCost_bind', clientState_readParam2Prog,
        c1, hmbObm, Realization.memoryCost_bind', clientState_readParam2Prog, c2, hpbw,
        Realization.memoryCost_bind', memoryCost_writePackedCompGenProg,
        clientState_writePackedCompGenProg, memoryCost_writePackedCompGenProg]
      omega
    have hi1 : 16 * b + 6 + 2 * role < 16 * numBucketsWhp fl.N := by omega
    have hi2 : 16 * b + 7 + 2 * role < 16 * numBucketsWhp fl.N := by omega
    have hout_bkt : ∀ addr, ¬(fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr ∧
        addr < fl.metaBase + offBktMeta fl.c fl.w fl.N +
          packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w) →
        m2 addr = s.mem addr := fun addr ha =>
      (writePacked_outside hw_pos m1 hi2 0 ha).trans (writePacked_outside hw_pos s.mem hi1 0 ha)
    have hslot_ne : ∀ idx < 16 * numBucketsWhp fl.N,
        idx ≠ 16 * b + 6 + 2 * role → idx ≠ 16 * b + 7 + 2 * role →
        readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w m2 idx =
          readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N)
            (globalPtrBits fl.N) fl.w s.mem idx :=
      fun idx _ hne1 hne2 =>
        (readPacked_writePacked_of_ne hw_pos m1 hne2 0).trans
          (readPacked_writePacked_of_ne hw_pos s.mem hne1 0)
    have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr → m2 addr = s.mem addr := fun addr ha =>
      hout_bkt addr fun hb_in => ha (fl.owns_of_btree hv (Or.inl hb_in))
    have hout_io : ∀ addr, fl.io.OwnsAddr addr → m2 addr = s.mem addr := fun addr hia =>
      hout_bkt addr fun hb_in => hv.bp_valid.disjoint addr (Or.inr (Or.inr (Or.inl hb_in))) hia
    have hbp_eq : extractBlockPool fl.mp m2 = extractBlockPool fl.mp s.mem := by
      have hd1 := hmv.offSlabDir_ge; have hd2 := hmv.offTailDir_ge
      have hd3 := hmv.offSlabOwner_ge; have hd4 := hmv.offTailOwner_ge
      dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hd1 hd2 hd3 hd4
      have hsd : ∀ idx < fl.mp.M * fl.mp.maxSlabs,
          readPacked (fl.mp.metaBase + fl.mp.offSlabDir) fl.mp.ptrB fl.mp.w m2 idx =
            readPacked (fl.mp.metaBase + fl.mp.offSlabDir) fl.mp.ptrB fl.mp.w s.mem idx :=
        fun idx hi => readPacked_congr hw_pos
          (fun a ha => hout_bkt a (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))
          hi
      have htd : ∀ idx < 8 * fl.mp.M * fl.mp.K,
          readPacked (fl.mp.metaBase + fl.mp.offTailDir) fl.mp.ptrB fl.mp.w m2 idx =
            readPacked (fl.mp.metaBase + fl.mp.offTailDir) fl.mp.ptrB fl.mp.w s.mem idx :=
        fun idx hi => readPacked_congr hw_pos
          (fun a ha => hout_bkt a (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))
          hi
      have hso : ∀ idx < 4 * fl.mp.maxBlocks,
          readPacked (fl.mp.metaBase + fl.mp.offSlabOwner) fl.mp.ptrB fl.mp.w m2 idx =
            readPacked (fl.mp.metaBase + fl.mp.offSlabOwner) fl.mp.ptrB fl.mp.w s.mem idx :=
        fun idx hi => readPacked_congr hw_pos
          (fun a ha => hout_bkt a (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))
          hi
      have hto : ∀ idx < 16 * fl.mp.maxTail,
          readPacked (fl.mp.metaBase + fl.mp.offTailOwner) fl.mp.ptrB fl.mp.w m2 idx =
            readPacked (fl.mp.metaBase + fl.mp.offTailOwner) fl.mp.ptrB fl.mp.w s.mem idx :=
        fun idx hi => readPacked_congr hw_pos
          (fun a ha => hout_bkt a (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))
          hi
      unfold extractBlockPool
      have hm_eq : fl.mp.M = numBucketsWhp fl.N := rfl
      have hms_eq : fl.mp.maxSlabs = maxSlabsPerBktWhp fl.N := rfl
      have hk_eq : fl.mp.K = slabSizeWhp fl.N := rfl
      have hmb_eq : fl.mp.maxBlocks = fl.N / slabSizeWhp fl.N + 4 := rfl
      have hmt_eq : fl.mp.maxTail = maxTailWhp fl.N := rfl
      congr 1
      · exact hout_bkt _ (by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega)
      · ext x; by_cases hx : x < fl.mp.M
        · rw [ite_eq_left hx, ite_eq_left hx]
          exact hslot_ne _ (by omega) (by omega) (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · ext x; by_cases hx : x < fl.mp.M
        · rw [ite_eq_left hx, ite_eq_left hx]
          exact hslot_ne _ (by omega) (by omega) (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · ext x; by_cases hx : x < fl.mp.M
        · rw [ite_eq_left hx, ite_eq_left hx]
          exact hslot_ne _ (by omega) (by omega) (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · ext x; by_cases hx : x < fl.mp.M
        · rw [ite_eq_left hx, ite_eq_left hx]
          exact hslot_ne _ (by omega) (by omega) (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · ext x; by_cases hx : x < fl.mp.M
        · rw [ite_eq_left hx, ite_eq_left hx]
          exact hslot_ne _ (by omega) (by omega) (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · ext x y
        by_cases hxy : x < fl.mp.M ∧ y < fl.mp.maxSlabs
        · have hlt : x * fl.mp.maxSlabs + y < fl.mp.M * fl.mp.maxSlabs := by
            calc x * fl.mp.maxSlabs + y
                < (x + 1) * fl.mp.maxSlabs := by ring_nf; omega
              _ ≤ fl.mp.M * fl.mp.maxSlabs := Nat.mul_le_mul_right _ hxy.1
          rw [ite_eq_left hxy, ite_eq_left hxy]; exact hsd _ hlt
        · rw [ite_eq_right hxy, ite_eq_right hxy]
      · ext x y
        by_cases hxy : x < fl.mp.M ∧ y < 6 * fl.mp.K
        · have h6eq : 6 * fl.mp.K * fl.mp.M = 6 * (fl.mp.M * fl.mp.K) := by ring
          have h8eq : 8 * fl.mp.M * fl.mp.K = 8 * (fl.mp.M * fl.mp.K) := by ring
          have hlt : 6 * fl.mp.K * x + y < 8 * fl.mp.M * fl.mp.K := by
            calc 6 * fl.mp.K * x + y
                < 6 * fl.mp.K * (x + 1) := by ring_nf; omega
              _ ≤ 6 * fl.mp.K * fl.mp.M := Nat.mul_le_mul_left _ hxy.1
              _ ≤ 8 * fl.mp.M * fl.mp.K := by omega
          rw [ite_eq_left hxy, ite_eq_left hxy]; exact htd _ hlt
        · rw [ite_eq_right hxy, ite_eq_right hxy]
      · ext x; by_cases hx : x < fl.mp.maxBlocks
        · rw [ite_eq_left hx, ite_eq_left hx]; exact hso _ (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · ext x; by_cases hx : x < fl.mp.maxBlocks
        · rw [ite_eq_left hx, ite_eq_left hx]; exact hso _ (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · ext x; by_cases hx : x < fl.mp.maxBlocks
        · rw [ite_eq_left hx, ite_eq_left hx]; exact hso _ (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · exact hout_bkt _ (by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega)
      · ext x; by_cases hx : x < fl.mp.maxBlocks
        · rw [ite_eq_left hx, ite_eq_left hx]; exact hso _ (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · exact hout_bkt _ (by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega)
      · exact hout_bkt _ (by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega)
      · ext x
        by_cases hx : x < 8 * fl.mp.M
        · have hx_mk : x < fl.mp.M * fl.mp.K :=
            lt_of_lt_of_le hx ((Nat.mul_comm 8 fl.mp.M).le.trans
              (Nat.mul_le_mul_left fl.mp.M (le_trans (by decide : 8 ≤ 64) hmv.K_ge)))
          have h6eq : 6 * fl.mp.M * fl.mp.K = 6 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 6 _ _
          have h8eq : 8 * fl.mp.M * fl.mp.K = 8 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 8 _ _
          rw [ite_eq_left hx, ite_eq_left hx]
          exact htd _ (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · ext x
        by_cases hx : x < 8 * fl.mp.M
        · have hx_mk : x < fl.mp.M * fl.mp.K :=
            lt_of_lt_of_le hx ((Nat.mul_comm 8 fl.mp.M).le.trans
              (Nat.mul_le_mul_left fl.mp.M (le_trans (by decide : 8 ≤ 64) hmv.K_ge)))
          have h7eq : 7 * fl.mp.M * fl.mp.K = 7 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 7 _ _
          have h8eq : 8 * fl.mp.M * fl.mp.K = 8 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 8 _ _
          rw [ite_eq_left hx, ite_eq_left hx]
          exact htd _ (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · ext x
        by_cases hx : x < 8 * fl.mp.M * fl.mp.K
        · have h16mt : 16 * (fl.mp.M * fl.mp.K) ≤ 16 * fl.mp.maxTail := by
            have := hmv.sixteen_MK_le_maxTail; rwa [Nat.mul_assoc] at this
          have h8eq : 8 * fl.mp.M * fl.mp.K = 8 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 8 _ _
          rw [ite_eq_left hx, ite_eq_left hx]; exact hto x (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · ext x
        by_cases hx : x < 8 * fl.mp.M * fl.mp.K
        · have h16mt : 16 * (fl.mp.M * fl.mp.K) ≤ 16 * fl.mp.maxTail := by
            have := hmv.sixteen_MK_le_maxTail; rwa [Nat.mul_assoc] at this
          have h8eq : 8 * fl.mp.M * fl.mp.K = 8 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 8 _ _
          rw [ite_eq_left hx, ite_eq_left hx]; exact hto _ (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx]
      · exact hout_bkt _ (by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega)
      · exact hout_bkt _ (by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega)
      · exact hout_bkt _ (by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega)
      · exact hout_bkt _ (by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega)
    have hfm_eq : extractFastMeta fl m2 = extractFastMeta fl s.mem := by
      unfold extractFastMeta
      congr 1
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
      all_goals (
        ext x; by_cases hx : x < numBucketsWhp fl.N
        · rw [ite_eq_left hx, ite_eq_left hx]; exact hslot_ne _ (by omega) (by omega) (by omega)
        · rw [ite_eq_right hx, ite_eq_right hx])
    have htr_eq : ∀ r < 2,
        extractBufTrie (fl.trieL r) m2 = extractBufTrie (fl.trieL r) s.mem := fun r hr_lt =>
      extractBufTrie_congr hw_pos fun addr hta =>
        hout_bkt addr fun hb_in => fl.disj_btree_trie hv hr_lt (Or.inl hb_in) hta
    have hsl_zero : extractBTreeSlice fl.btL b role m2 =
        ⟨0, 0, (extractBTreeSlice fl.btL b role m2).nodes⟩ := by
      have ha0 : readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w m2
          (16 * b + 6 + 2 * role) = 0 :=
        (readPacked_writePacked_of_ne hw_pos m1 (by omega) 0).trans
          (readPacked_writePacked_self _ _ _ s.mem _ (Nat.two_pow_pos _))
      have hr0 : readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w m2
          (16 * b + 7 + 2 * role) = 0 :=
        readPacked_writePacked_self _ _ _ m1 _ (Nat.two_pow_pos _)
      unfold extractBTreeSlice; dsimp only [FastEpochLayout.btL, epochBTreeLayout]
      rw [ha0, hr0]
    have hsl_other : ∀ b' < numBucketsWhp fl.N, ∀ role' < 3, (b' ≠ b ∨ role' ≠ role) →
        extractBTreeSlice fl.btL b' role' m2 = extractBTreeSlice fl.btL b' role' s.mem := by
      intro b' hb' role' hr' hne
      have hd_bt : offBktMeta fl.c fl.w fl.N +
          packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w ≤
          offBTreeMeta fl.c fl.w fl.N := by
        unfold offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir; omega
      have hd_k : offBTreeMeta fl.c fl.w fl.N ≤ offBTreeKeys fl.c fl.w fl.N := Nat.le_add_right _ _
      have hd_v : offBTreeKeys fl.c fl.w fl.N ≤ offBTreeVals fl.c fl.w fl.N := Nat.le_add_right _ _
      refine extractBTreeSlice_congr_entries
        (by dsimp [FastEpochLayout.btL, epochBTreeLayout]
            exact hslot_ne _ (by omega) (by omega) (by omega))
        (by dsimp [FastEpochLayout.btL, epochBTreeLayout]
            exact hslot_ne _ (by omega) (by omega) (by omega))
        fun u hu => ?_
      dsimp only [FastEpochLayout.btL, epochBTreeLayout] at hu ⊢
      have htot : (3 * b' + role') * nSliceWhp fl.N + u < totalBTreeNodesWhp fl.N := by
        unfold totalBTreeNodesWhp
        calc (3 * b' + role') * nSliceWhp fl.N + u
            < (3 * b' + role' + 1) * nSliceWhp fl.N := by ring_nf; omega
          _ ≤ (3 * numBucketsWhp fl.N) * nSliceWhp fl.N := Nat.mul_le_mul_right _ (by omega)
      exact ⟨readPacked_congr hw_pos (fun a ha => hout_bkt a (by omega)) htot,
        readPacked_congr hw_pos (fun a ha => hout_bkt a (by omega)) htot,
        readPacked_congr hw_pos (fun a ha => hout_bkt a (by omega)) htot⟩
    rw [hst]
    exact ⟨rfl, hr.of_frame rfl hout_fast, hcost, hbp_eq, hfm_eq, hout_bkt _ (by omega),
      htr_eq, hout_io, hout_fast, fun _ _ => ⟨hsl_zero ▸ validWhpSlice_zero .., hsl_other⟩⟩
  · have hst : (Memory.spec 0).clientState s (fastBTreeResetProg (fl.pBase, (b, role))) = s := by
      unfold fastBTreeResetProg
      simp [StateTransitionSpec.clientState, hm11, hcond]
    have hc : memoryCost (fastBTreeResetProg (fl.pBase, (b, role))) s ≤ 14 := by
      unfold fastBTreeResetProg
      simp only [Realization.memoryCost_bind', prog_memoryCost_read, prog_runClient_state_read,
        StateTransitionSpec.clientState, prog_clientResult_read, hm11, hcond, ↓reduceIte,
        memoryCost_pure]
      omega
    rw [hst]
    exact ⟨rfl, hr, hc, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun hb hrole => absurd ⟨hb, hrole⟩ hcond⟩

theorem fastBTreeResetProg_pre {w : ℕ} {x : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (h : FastProgPre w x.1 s) :
    FastProgPre w x.1 ((Memory.spec 0).clientState s (fastBTreeResetProg x)) := by
  rcases x with ⟨pBase, ⟨b, role⟩⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBTreeResetProg_spec hr).2.1⟩

theorem realizesBounded_fastBTreeReset :
    RealizesBounded .exact fastBTreeResetProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrp := realizesBounded_readParam2
  have hwk := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨pBase, ⟨b, role⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have ⟨hv, hpt, _, _⟩ := hr
    have hmv := hv.mp_valid
    have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
    have h16M_w : 16 * numBucketsWhp fl.N < 2 ^ w :=
      lt_of_le_of_lt hmv.sixteen_M_le hmv.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState] at *
    try simp only [runClient_state_readParam2Prog] at *
    first | exact hw6 | exact hp | omega | (
      have hmbObm : ((Memory.spec 0).runClient s (readParam2Prog (fl.pBase, (1, 31)))).1 =
          (fl.metaBase, offBktMeta fl.c fl.w fl.N) := by
        unfold readParam2Prog
        simp [hpt 1 (by decide), hpt 31 (by decide), FastEpochLayout.paramWord]
      have hpbw : ((Memory.spec 0).runClient s (readParam2Prog (fl.pBase, (10, 2)))).1 =
          (globalPtrBits fl.N, fl.w) := by
        unfold readParam2Prog
        simp [hpt 10 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
      simp only [StateTransitionSpec.clientResult, hmbObm, hpbw,
        runClient_state_writePackedCompGenProg]
      refine ⟨16 * numBucketsWhp fl.N, hv.w_pos, hv.w_eq, hmv.ptrB_le, by omega, ?_⟩
      have hd1 := hmv.offSlabDir_ge; have hd2 := hmv.offTailDir_ge
      have hd3 := hmv.offSlabOwner_ge; have hd4 := hmv.offTailOwner_ge
      have hdf := hmv.frontier_ge
      dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hd1 hd2 hd3 hd4 hdf ⊢
      cases hv.w_eq; omega))

/-- `btreeLookup` on `(b, role)` via `pBase` (`¬ReadsWidth`). -/
def fastBTreeLookupProg : (ℕ × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((pBase, (b, role)), q) => do
    let M ← Memory.read (pBase + 11)
    let fpw ← readParam2Prog (pBase, (9, 2))
    if b < M ∧ role < 3 ∧ fpw.1 < fpw.2 then
      if q < (1 <<< fpw.1) then do
        let ctx ← loadBTreeSliceCtxProg (pBase, (b, role))
        btreeLookupBoundedProg (ctx, q)
      else pure (0, 0)
    else pure (0, 0)

@[simp] theorem runClient_state_fastBTreeLookupProg
    (x : (ℕ × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastBTreeLookupProg x)) = s := by
  rcases x with ⟨⟨pBase, ⟨b, role⟩⟩, q⟩
  unfold fastBTreeLookupProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind, prog_runClient_state_read,
    runClient_state_readParam2Prog]
  split_ifs
  · rw [prog_runClient_state_bind, clientState_loadBTreeSliceCtxProg]
    exact clientState_btreeLookupBoundedProg _ s
  all_goals rfl

theorem clientState_fastBTreeLookupProg (x : (ℕ × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastBTreeLookupProg x) = s :=
  runClient_state_fastBTreeLookupProg x s

theorem realizesBounded_fastBTreeLookup :
    RealizesBounded .exact fastBTreeLookupProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrp := realizesBounded_readParam2
  have hlb := realizesBounded_loadBTreeSliceCtx
  have hbl := realizesBounded_btreeLookup
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, role⟩⟩, q⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have ⟨hv, hpt, _, _⟩ := hr
    have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
    have hfpw : ((Memory.spec 0).runClient s (readParam2Prog (fl.pBase, (9, 2)))).1 =
        (fpBitsWhp fl.N, fl.w) := by
      unfold readParam2Prog
      simp [hpt 9 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
      runClient_state_readParam2Prog, runClient_state_loadBTreeSliceCtxProg, hm11, hfpw] at *
    first | exact hw6 | exact hp | omega | (
      have hw_eq := hv.w_eq
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right Nat.one_lt_two (by omega)) | (
      have hl_res := clientResult_loadBTreeSliceCtxProg (b := b) (role := role) (s := s) hpt
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      dsimp only [BTreeKeyOpPre, BTreeSlicePre, unpackSliceCtx, BTreeEpochLayout.toSliceCtx,
        FastEpochLayout.btL, epochBTreeLayout]
      refine ⟨⟨hv.w_eq.symm ▸ hv.bt_valid, by omega, by omega⟩, ?_⟩
      rw [Nat.shiftLeft_eq, one_mul] at *; omega))

/-- `btreeDelete` on `(b, role)` via `pBase` (`¬ReadsWidth`). -/
def fastBTreeDeleteProg : (ℕ × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((pBase, (b, role)), q) => do
    let M ← Memory.read (pBase + 11)
    let fpw ← readParam2Prog (pBase, (9, 2))
    if b < M ∧ role < 3 ∧ fpw.1 < fpw.2 then
      if q < (1 <<< fpw.1) then do
        let ctx ← loadBTreeSliceCtxProg (pBase, (b, role))
        btreeDeleteBoundedProg (ctx, q)
      else pure ()
    else pure ()

theorem fastBTreeDeleteProg_ready {w : ℕ} {fl : FastEpochLayout} {b role q : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastBTreeDeleteProg ((fl.pBase, (b, role)), q))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    (∀ addr, ¬fl.btL.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  have ⟨hv, hpt, _, _⟩ := hr
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hfpw : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (9, 2))) =
      (fpBitsWhp fl.N, fl.w) := by
    unfold readParam2Prog
    simp [hpt 9 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
  unfold fastBTreeDeleteProg; dsimp only
  have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
  have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := hm11
  rw [StateTransitionSpec.clientState_bind, hr11_st, hr11_r,
    StateTransitionSpec.clientState_bind, clientState_readParam2Prog, hfpw]
  by_cases hc1 : b < numBucketsWhp fl.N ∧ role < 3 ∧ fpBitsWhp fl.N < fl.w
  · rw [ite_eq_left hc1]
    by_cases hc2 : q < (1 <<< fpBitsWhp fl.N)
    · rw [ite_eq_left hc2, StateTransitionSpec.clientState_bind, clientState_loadBTreeSliceCtxProg,
        clientResult_loadBTreeSliceCtxProg hpt]
      obtain ⟨hfr, hout⟩ := btreeDeleteBoundedProg_frame (L := fl.btL) hw_pos hc1.1 hc1.2.1 q s
      exact ⟨hfr, hr.of_frame hfr (fun a ha => hout a (fun h => ha (fl.owns_of_btree hv h))), hout⟩
    · rw [ite_eq_right hc2]; exact ⟨rfl, hr, fun _ _ => rfl⟩
  · rw [ite_eq_right hc1]; exact ⟨rfl, hr, fun _ _ => rfl⟩

theorem fastBTreeDeleteProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × ℕ} {s : Memory.State}
    (h : FastProgPre w (fastArgPBase x) s) :
    FastProgPre w (fastArgPBase x) ((Memory.spec 0).clientState s (fastBTreeDeleteProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, role⟩⟩, q⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBTreeDeleteProg_ready hr).2.1⟩

theorem realizesBounded_fastBTreeDelete :
    RealizesBounded .exact fastBTreeDeleteProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrp := realizesBounded_readParam2
  have hlb := realizesBounded_loadBTreeSliceCtx
  have hbd := realizesBounded_btreeDelete
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, role⟩⟩, q⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have ⟨hv, hpt, _, _⟩ := hr
    have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
    have hfpw : ((Memory.spec 0).runClient s (readParam2Prog (fl.pBase, (9, 2)))).1 =
        (fpBitsWhp fl.N, fl.w) := by
      unfold readParam2Prog
      simp [hpt 9 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
      runClient_state_readParam2Prog, runClient_state_loadBTreeSliceCtxProg, hm11, hfpw] at *
    first | exact hw6 | exact hp | omega | (
      have hw_eq := hv.w_eq
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right Nat.one_lt_two (by omega)) | (
      have hl_res := clientResult_loadBTreeSliceCtxProg (b := b) (role := role) (s := s) hpt
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      dsimp only [BTreeKeyOpPre, BTreeSlicePre, unpackSliceCtx, BTreeEpochLayout.toSliceCtx,
        FastEpochLayout.btL, epochBTreeLayout]
      refine ⟨⟨hv.w_eq.symm ▸ hv.bt_valid, by omega, by omega⟩, ?_⟩
      rw [Nat.shiftLeft_eq, one_mul] at *; omega))

private abbrev param4_0 (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := p.1.1
private abbrev param4_1 (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := p.1.2
private abbrev param4_2 (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := p.2.1

/-- `btreeUpdate` on `(b, role)` via `pBase` (`¬ReadsWidth`). -/
def fastBTreeUpdateProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, (b, role)), (q, newVal)) => do
    let M ← Memory.read (pBase + 11)
    let fvw ← readParam4Prog ((pBase, (9, 19)), (2, 2))
    if b < M ∧ role < 3 ∧ param4_0 fvw < param4_2 fvw ∧ param4_1 fvw < param4_2 fvw then
      if q < (1 <<< param4_0 fvw) ∧ newVal < (1 <<< param4_1 fvw) then do
        let ctx ← loadBTreeSliceCtxProg (pBase, (b, role))
        btreeUpdateBoundedProg (ctx, (q, newVal))
      else pure ()
    else pure ()

theorem fastBTreeUpdateProg_ready {w : ℕ} {fl : FastEpochLayout} {b role q newVal : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s
      (fastBTreeUpdateProg ((fl.pBase, (b, role)), (q, newVal)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    (∀ addr, ¬fl.btL.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  have ⟨hv, hpt, _, _⟩ := hr
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hfvw : (Memory.spec 0).clientResult s (readParam4Prog ((fl.pBase, (9, 19)), (2, 2))) =
      ((fpBitsWhp fl.N, valLaneBitsWhp fl.N), (fl.w, fl.w)) := by
    unfold readParam4Prog readParam2Prog
    simp [hpt 9 (by decide), hpt 19 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
  unfold fastBTreeUpdateProg; dsimp only
  have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
  have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := hm11
  rw [StateTransitionSpec.clientState_bind, hr11_st, hr11_r,
    StateTransitionSpec.clientState_bind, clientState_readParam4Prog, hfvw]
  dsimp only
  by_cases hc1 : b < numBucketsWhp fl.N ∧ role < 3 ∧ fpBitsWhp fl.N < fl.w ∧
      valLaneBitsWhp fl.N < fl.w
  · rw [ite_eq_left hc1]
    by_cases hc2 : q < (1 <<< fpBitsWhp fl.N) ∧ newVal < (1 <<< valLaneBitsWhp fl.N)
    · rw [ite_eq_left hc2, StateTransitionSpec.clientState_bind, clientState_loadBTreeSliceCtxProg,
        clientResult_loadBTreeSliceCtxProg hpt]
      obtain ⟨hfr, hout⟩ :=
        btreeUpdateBoundedProg_frame (L := fl.btL) hw_pos hc1.1 hc1.2.1 q newVal s
      exact ⟨hfr, hr.of_frame hfr (fun a ha => hout a (fun h => ha (fl.owns_of_btree hv h))), hout⟩
    · rw [ite_eq_right hc2]; exact ⟨rfl, hr, fun _ _ => rfl⟩
  · rw [ite_eq_right hc1]; exact ⟨rfl, hr, fun _ _ => rfl⟩

theorem fastBTreeUpdateProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : FastProgPre w (fastArgPBase x) s) :
    FastProgPre w (fastArgPBase x) ((Memory.spec 0).clientState s (fastBTreeUpdateProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨q, newVal⟩⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBTreeUpdateProg_ready hr).2.1⟩

theorem realizesBounded_fastBTreeUpdate :
    RealizesBounded .exact fastBTreeUpdateProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrq := realizesBounded_readParam4
  have hlb := realizesBounded_loadBTreeSliceCtx
  have hbu := realizesBounded_btreeUpdate
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨q, newVal⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have ⟨hv, hpt, _, _⟩ := hr
    have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
    have hfvw : ((Memory.spec 0).runClient s
        (readParam4Prog ((fl.pBase, (9, 19)), (2, 2)))).1 =
        ((fpBitsWhp fl.N, valLaneBitsWhp fl.N), (fl.w, fl.w)) := by
      unfold readParam4Prog readParam2Prog
      simp [hpt 9 (by decide), hpt 19 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
      runClient_state_readParam4Prog, runClient_state_loadBTreeSliceCtxProg, hm11, hfvw] at *
    first | exact hw6 | exact hp | omega | (
      have hw_eq := hv.w_eq
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right Nat.one_lt_two (by omega)) | (
      have hl_res := clientResult_loadBTreeSliceCtxProg (b := b) (role := role) (s := s) hpt
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      dsimp only [BTreeKeyValOpPre, BTreeSlicePre, unpackSliceCtx, BTreeEpochLayout.toSliceCtx,
        FastEpochLayout.btL, epochBTreeLayout]
      refine ⟨⟨hv.w_eq.symm ▸ hv.bt_valid, by omega, by omega⟩, ?_, ?_⟩
      all_goals (
        rw [Nat.shiftLeft_eq, one_mul] at *
        omega)))

/-- `btreeInsert` on `(b, role)` via `pBase` (`¬ReadsWidth`). -/
def fastBTreeInsertProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, (b, role)), (q, val)) => do
    let M ← Memory.read (pBase + 11)
    let fvw ← readParam4Prog ((pBase, (9, 19)), (2, 2))
    if b < M ∧ role < 3 ∧ param4_0 fvw < param4_2 fvw ∧ param4_1 fvw < param4_2 fvw then
      if q < (1 <<< param4_0 fvw) ∧ val < (1 <<< param4_1 fvw) then do
        let ctx ← loadBTreeSliceCtxProg (pBase, (b, role))
        btreeInsertBoundedProg (ctx, (q, val))
      else pure ()
    else pure ()

theorem fastBTreeInsertProg_ready {w : ℕ} {fl : FastEpochLayout} {b role q val : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s
      (fastBTreeInsertProg ((fl.pBase, (b, role)), (q, val)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    (∀ addr, ¬fl.btL.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  have ⟨hv, hpt, _, _⟩ := hr
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hfvw : (Memory.spec 0).clientResult s (readParam4Prog ((fl.pBase, (9, 19)), (2, 2))) =
      ((fpBitsWhp fl.N, valLaneBitsWhp fl.N), (fl.w, fl.w)) := by
    unfold readParam4Prog readParam2Prog
    simp [hpt 9 (by decide), hpt 19 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
  unfold fastBTreeInsertProg; dsimp only
  have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
  have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := hm11
  rw [StateTransitionSpec.clientState_bind, hr11_st, hr11_r,
    StateTransitionSpec.clientState_bind, clientState_readParam4Prog, hfvw]
  dsimp only
  by_cases hc1 : b < numBucketsWhp fl.N ∧ role < 3 ∧ fpBitsWhp fl.N < fl.w ∧
      valLaneBitsWhp fl.N < fl.w
  · rw [ite_eq_left hc1]
    by_cases hc2 : q < (1 <<< fpBitsWhp fl.N) ∧ val < (1 <<< valLaneBitsWhp fl.N)
    · rw [ite_eq_left hc2, StateTransitionSpec.clientState_bind, clientState_loadBTreeSliceCtxProg,
        clientResult_loadBTreeSliceCtxProg hpt]
      obtain ⟨hfr, hout⟩ :=
        btreeInsertBoundedProg_frame (L := fl.btL) hw_pos hc1.1 hc1.2.1 q val s
      exact ⟨hfr, hr.of_frame hfr (fun a ha => hout a (fun h => ha (fl.owns_of_btree hv h))), hout⟩
    · rw [ite_eq_right hc2]; exact ⟨rfl, hr, fun _ _ => rfl⟩
  · rw [ite_eq_right hc1]; exact ⟨rfl, hr, fun _ _ => rfl⟩

theorem fastBTreeInsertProg_pre {w : ℕ} {x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : FastProgPre w (fastArgPBase x) s) :
    FastProgPre w (fastArgPBase x) ((Memory.spec 0).clientState s (fastBTreeInsertProg x)) := by
  rcases x with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨q, val⟩⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastBTreeInsertProg_ready hr).2.1⟩

theorem realizesBounded_fastBTreeInsert :
    RealizesBounded .exact fastBTreeInsertProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrq := realizesBounded_readParam4
  have hlb := realizesBounded_loadBTreeSliceCtx
  have hbi := realizesBounded_btreeInsert
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨q, val⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have ⟨hv, hpt, _, _⟩ := hr
    have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
    have hfvw : ((Memory.spec 0).runClient s
        (readParam4Prog ((fl.pBase, (9, 19)), (2, 2)))).1 =
        ((fpBitsWhp fl.N, valLaneBitsWhp fl.N), (fl.w, fl.w)) := by
      unfold readParam4Prog readParam2Prog
      simp [hpt 9 (by decide), hpt 19 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
      runClient_state_readParam4Prog, runClient_state_loadBTreeSliceCtxProg, hm11, hfvw] at *
    first | exact hw6 | exact hp | omega | (
      have hw_eq := hv.w_eq
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right Nat.one_lt_two (by omega)) | (
      have hl_res := clientResult_loadBTreeSliceCtxProg (b := b) (role := role) (s := s) hpt
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      dsimp only [BTreeKeyValOpPre, BTreeSlicePre, unpackSliceCtx, BTreeEpochLayout.toSliceCtx,
        FastEpochLayout.btL, epochBTreeLayout]
      refine ⟨⟨hv.w_eq.symm ▸ hv.bt_valid, by omega, by omega⟩, ?_, ?_⟩
      all_goals (
        rw [Nat.shiftLeft_eq, one_mul] at *
        omega)))

/-! ## Section 2: Zeroed-Region Fast-Epoch Initializer (`fastInitZeroedProg`) -/

/-- Initialize `BlockPool` and both `BufTrie` copies (`role = 0, 1`) on a Phase-1 zeroed metadata
region (`s.mem fl.metaBase = fl.N`, `[metaBase + 1, metaBase + 32) = 0`, `[metaBase + offBktMeta,
metaBase + offPageDir) = 0`), establishing `FastEpochInv fl slack seeds s'.mem (fun _ => none)` in
`O(1)` deterministic instructions (`¬ReadsWidth`). -/
def fastInitZeroedProg (pBase : ℕ) : Memory.Prog Unit := do
  fastBpInitProg pBase
  fastBufInitEmptyProg (pBase, 0)
  fastBufInitEmptyProg (pBase, 1)

theorem realizesBounded_fastInitZeroed :
    RealizesBounded .exact fastInitZeroedProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hbp := realizesBounded_fastBpInit
  have htr := realizesBounded_fastBufInitEmpty
  realize
  all_goals (
    have ⟨hw6, hp⟩ := FastProgPre.pBase_bound h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    first
    | exact h
    | exact fastBpInitProg_pre h
    | exact fastBufInitEmptyProg_pre (x := (d, 0)) (fastBpInitProg_pre h)
    | omega)

theorem fastInitZeroedProg_spec {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hpt : fl.ParamTable s.mem)
    (hN : s.mem fl.metaBase = fl.N)
    (hbkt_rep : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s.mem)
    (hfp_rep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N)
      seeds.fp s.mem)
    (hzero_hdr : ∀ k, 1 ≤ k → k < 32 → s.mem (fl.metaBase + k) = 0)
    (hzero_tab : ∀ addr, fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr →
      addr < fl.metaBase + offPageDir fl.c fl.w fl.N → s.mem addr = 0)
    (hio : fl.io.StateInv 0 slack s.mem) :
    let s' := (Memory.spec 0).clientState s (fastInitZeroedProg fl.pBase)
    s'.frontier = s.frontier ∧
    memoryCost (fastInitZeroedProg fl.pBase) s ≤ 40 ∧
    FastEpochInv fl slack seeds s'.mem (fun _ => none) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      extractPageUnperm fl.io.pgL s'.mem = extractPageUnperm fl.io.pgL s.mem ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  have hr₀ : FastLayoutReady w fl s :=
    ⟨hv, hpt, hbkt_rep.1 ▸ seeds.bkt.1.isLt, hfp_rep.1 ▸ seeds.fp.1.isLt⟩
  have hmv := hv.mp_valid
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := by
    have := hmv.offBktMeta_ge; dsimp [FastEpochLayout.mp, epochBpMetaLayout] at this; exact this
  have hm0 := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) (role := 0) (by decide)
  have hm1 := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) (role := 1) (by decide)
  have hob_bt : offTailOwner fl.c fl.w fl.N + packedWords (16 * maxTailWhp fl.N)
      (globalPtrBits fl.N) fl.w = offBTreeMeta fl.c fl.w fl.N := rfl
  have hbt_le_v : offBTreeMeta fl.c fl.w fl.N ≤ offBTreeVals fl.c fl.w fl.N := by
    unfold offBTreeVals offBTreeKeys; omega
  -- Step 1: `fastBpInitProg`
  obtain ⟨hfr₁, hr₁, hc₁, hout₁⟩ := fastBpInitProg_ready hr₀
  set s₁ := (Memory.spec 0).clientState s (fastBpInitProg fl.pBase)
  have hs₁_eq : s₁ = (Memory.spec 0).clientState s (bpInitProg fl.bpL) := by
    unfold s₁ fastBpInitProg bpInitProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBpMetaCtxProg,
      clientResult_loadBpMetaCtxProg hpt]
    rfl
  have hz_bp : ∀ addr, fl.mp.OwnsMetaAddr addr → s.mem addr = 0 := fun addr hma => by
    rcases fl.owns_of_bpMeta hv hma with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
    · have hsub : fl.metaBase + (addr - fl.metaBase) = addr := by omega
      rw [← hsub]; exact hzero_hdr (addr - fl.metaBase) (by omega) (by omega)
    · exact hzero_tab addr h1 h2
    · exact absurd h3 (hv.bp_valid.disjoint addr hma)
  obtain ⟨_, hex_bp₁, hbp_inv₁, hpg₁⟩ :=
    bpInitProg_spec (hv.w_eq ▸ hv.bp_valid) hz_bp hio
  rw [← hs₁_eq] at hex_bp₁ hbp_inv₁ hpg₁
  dsimp only [FastEpochLayout.bpL] at hex_bp₁ hbp_inv₁ hpg₁
  -- Step 2: `fastBufInitEmptyProg (fl.pBase, 0)`
  obtain ⟨hfr₂, hr₂, hc₂, hres₂⟩ := fastBufInitEmptyProg_ready (role := 0) hr₁
  obtain ⟨hs₂_mem, hout₂⟩ := hres₂ (by decide)
  set s₂ := (Memory.spec 0).clientState s₁ (fastBufInitEmptyProg (fl.pBase, 0))
  have hz_tr₀ : ∀ addr, (fl.trieL 0).OwnsAddr addr → s₁.mem addr = 0 := fun addr hta => by
    rw [hout₁ addr (fun hma => (fl.disj_trie_bpAndMeta hv (by decide) hta)
      (Or.inl (by
        rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (rfl | ⟨h10, h17⟩) | ⟨hlo, hhi⟩ <;>
          (dsimp [FastEpochLayout.mp, epochBpMetaLayout] at *; omega))))]
    rcases fl.owns_of_trie hv (by decide) hta with ⟨_, h2⟩ | ⟨h1, h2⟩ | h3
    · dsimp [FastEpochLayout.trieL, epochTrieLayout, TrieLayout.OwnsAddr] at hta
      rcases hta with t1 | t2 | t3 <;> omega
    · exact hzero_tab addr h1 h2
    · exact absurd h3 (fun hia => (fl.disj_trie_bpAndMeta hv (by decide) hta) (Or.inr hia))
  have htv₀ := (hfr₁.symm ▸ hv).trie_valid (role := 0) (by decide)
  have htr₀_s₂ : extractBufTrie (fl.trieL 0) s₂.mem = emptyBufTrie := by
    rw [hs₂_mem]
    exact extractBufTrie_init_empty (L := fl.trieL 0) hw_pos
      (lt_of_le_of_lt htv₀.2.2.2.2.2.2.1 htv₀.2.2.2.2.2.2.2.1)
      htv₀.2.2.2.2.2.2.2.2.2.2.2.2.2.1 htv₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hz_tr₀
  -- Step 3: `fastBufInitEmptyProg (fl.pBase, 1)`
  obtain ⟨hfr₃, hr₃, hc₃, hres₃⟩ := fastBufInitEmptyProg_ready (role := 1) hr₂
  obtain ⟨hs₃_mem, hout₃⟩ := hres₃ (by decide)
  set s₃ := (Memory.spec 0).clientState s₂ (fastBufInitEmptyProg (fl.pBase, 1))
  have hz_tr₁ : ∀ addr, (fl.trieL 1).OwnsAddr addr → s₂.mem addr = 0 := fun addr hta => by
    rw [hout₂ addr (fun ht0 => epochTrieLayout_disjoint (by decide) (by decide)
      (by decide) ht0 hta)]
    rw [hout₁ addr (fun hma => (fl.disj_trie_bpAndMeta hv (by decide) hta)
      (Or.inl (by
        rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (rfl | ⟨h10, h17⟩) | ⟨hlo, hhi⟩ <;>
          (dsimp [FastEpochLayout.mp, epochBpMetaLayout] at *; omega))))]
    rcases fl.owns_of_trie hv (by decide) hta with ⟨_, h2⟩ | ⟨h1, h2⟩ | h3
    · dsimp [FastEpochLayout.trieL, epochTrieLayout, TrieLayout.OwnsAddr] at hta
      rcases hta with t1 | t2 | t3 <;> omega
    · exact hzero_tab addr h1 h2
    · exact absurd h3 (fun hia => (fl.disj_trie_bpAndMeta hv (by decide) hta) (Or.inr hia))
  have htv₁ := ((hfr₂.trans hfr₁).symm ▸ hv).trie_valid (role := 1) (by decide)
  have htr₁_s₃ : extractBufTrie (fl.trieL 1) s₃.mem = emptyBufTrie := by
    rw [hs₃_mem]
    exact extractBufTrie_init_empty (L := fl.trieL 1) hw_pos
      (lt_of_le_of_lt htv₁.2.2.2.2.2.2.1 htv₁.2.2.2.2.2.2.2.1)
      htv₁.2.2.2.2.2.2.2.2.2.2.2.2.2.1 htv₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hz_tr₁
  have htr₀_s₃ : extractBufTrie (fl.trieL 0) s₃.mem = emptyBufTrie :=
    (extractBufTrie_congr hw_pos fun addr ht0 =>
      hout₃ addr fun ht1 =>
        epochTrieLayout_disjoint (by decide) (by decide) (by decide) ht0 ht1).trans htr₀_s₂
  -- Frame of `s₃` vs `s₁` outside tries (covers `BlockPool`, `FastEpochMeta`, `BTreeSlice`, `io`)
  have hout₂₃_not_trie : ∀ addr,
      ¬(fl.trieL 0).OwnsAddr addr → ¬(fl.trieL 1).OwnsAddr addr → s₃.mem addr = s₁.mem addr :=
    fun addr hn0 hn1 => (hout₃ addr hn1).trans (hout₂ addr hn0)
  have hnot_tr_below : ∀ r < 2, ∀ addr,
      fl.metaBase ≤ addr → addr < fl.metaBase + offTrieChild fl.c fl.w fl.N 0 →
      ¬(fl.trieL r).OwnsAddr addr := fun r hr_lt addr hlo hhi hta =>
    fl.disj_trie_bpAndMeta hv hr_lt hta (Or.inl ⟨hlo, hhi⟩)
  have hnot_tr_io : ∀ r < 2, ∀ addr, fl.io.OwnsAddr addr → ¬(fl.trieL r).OwnsAddr addr :=
    fun r hr_lt addr hia hta => fl.disj_trie_bpAndMeta hv hr_lt hta (Or.inr hia)
  have hbp_s₃ : extractBlockPool fl.mp s₃.mem =
      BlockPoolState.empty fl.mp.M fl.mp.K fl.mp.maxSlabs := by
    refine (extractBlockPool_congr hw_pos hmv.K_ge (by
      have h := hmv.sixteen_MK_le_maxTail; rw [Nat.mul_assoc] at h; omega) fun addr hma => ?_).trans
      hex_bp₁
    have hbounds : fl.metaBase ≤ addr ∧ addr < fl.metaBase + offTrieChild fl.c fl.w fl.N 0 := by
      rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (rfl | ⟨h10, h17⟩) | ⟨hlo, hhi⟩ <;>
        (dsimp [FastEpochLayout.mp, epochBpMetaLayout] at *; exact ⟨by omega, by omega⟩)
    exact hout₂₃_not_trie addr (hnot_tr_below 0 (by decide) addr hbounds.1 hbounds.2)
      (hnot_tr_below 1 (by decide) addr hbounds.1 hbounds.2)
  have hio₁ : fl.io.StateInv 0 slack s₁.mem := by
    have hns1 : (extractBlockPool fl.mp s₁.mem).nSide = 0 := by rw [hex_bp₁]; rfl
    exact hns1 ▸ hbp_inv₁.2.2
  have hio_s₃ : fl.io.StateInv 0 slack s₃.mem ∧
      (fl.io.usePaged ≠ 0 →
        extractPageUnperm fl.io.pgL s₃.mem = extractPageUnperm fl.io.pgL s.mem ∧
        ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
          slotIoPairAt fl.io.partner s₃.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
    have hout_io₂₃ : ∀ a, fl.io.OwnsAddr a → s₃.mem a = s₁.mem a := fun a hia =>
      hout₂₃_not_trie a (hnot_tr_io 0 (by decide) a hia) (hnot_tr_io 1 (by decide) a hia)
    obtain ⟨hio₃, _⟩ := fl.io.congr_of_outside hv.io_valid.w_pos hio₁ hout_io₂₃
    refine ⟨hio₃, fun hnz => ?_⟩
    obtain ⟨hu₁, hp₁⟩ := hpg₁ hnz
    obtain ⟨hu₃, hp₃⟩ := fl.io.partner_congr_of_outside hv.io_valid.w_pos hio₁ hout_io₂₃ hnz
    have hvl₁ : (extractPagePair fl.io.pgL s₁.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side :=
      congrArg (fun u => u.st.virtLen fl.io.partner.side) hu₁
    exact ⟨hu₃.trans hu₁, fun idx hidx => (hp₃ idx (hvl₁.symm ▸ hidx)).trans (hp₁ idx hidx)⟩
  have hbp_inv_s₃ : fl.bpL.StateInv slack s₃.mem := by
    unfold BlockPoolLayout.StateInv; dsimp only [FastEpochLayout.bpL]
    exact ⟨hbp_s₃ ▸ hex_bp₁ ▸ hbp_inv₁.1, by rw [hbp_s₃]; exact Nat.zero_le _,
      by rw [hbp_s₃]; exact hio_s₃.1⟩
  have hzero_s₃_hdr : ∀ k, 2 ≤ k → k < 10 ∨ k = 17 → s₃.mem (fl.metaBase + k) = 0 := by
    intro k hk1 hk2
    have hlt_c0 : fl.metaBase + k < fl.metaBase + offTrieChild fl.c fl.w fl.N 0 := by omega
    rw [hout₂₃_not_trie _ (hnot_tr_below 0 (by decide) _ (Nat.le_add_right _ _) hlt_c0)
      (hnot_tr_below 1 (by decide) _ (Nat.le_add_right _ _) hlt_c0)]
    rw [hout₁ _ (fun hma => by
      rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | ⟨h10, h17⟩) | ⟨hlo, _⟩ <;>
        (dsimp [FastEpochLayout.mp, epochBpMetaLayout] at *; omega))]
    exact hzero_hdr k (by omega) (by omega)
  have hs₁_mem_ne : ∀ a, a ≠ fl.metaBase + 11 → s₁.mem a = s.mem a := fun a hne => by
    unfold s₁ fastBpInitProg bpInitZeroedProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBpMetaCtxProg,
      clientResult_loadBpMetaCtxProg hpt]
    dsimp only [BpMetaLayout.toCtx, FastEpochLayout.mp, epochBpMetaLayout]
    simp only [pure_bind, StateTransitionSpec.clientState, prog_runClient_state_write]
    exact Function.update_of_ne hne 1 s.mem
  have hzero_s₃_bkt : ∀ idx < 16 * numBucketsWhp fl.N,
      readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s₃.mem idx =
        0 := by
    intro idx hidx
    have hlt_w := wordOffset_add_one_lt_packedWords (k := globalPtrBits fl.N) hw_pos hidx
    have hd_sd : offBktMeta fl.c fl.w fl.N +
        packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w ≤
        offBTreeMeta fl.c fl.w fl.N := by
      unfold offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir; omega
    have hz_word : ∀ off < packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w,
        s₃.mem (fl.metaBase + offBktMeta fl.c fl.w fl.N + off) = 0 := by
      intro off hoff
      set a := fl.metaBase + offBktMeta fl.c fl.w fl.N + off
      have ha_lt_c0 : a < fl.metaBase + offTrieChild fl.c fl.w fl.N 0 := by dsimp [a]; omega
      have ha_lt_pd : a < fl.metaBase + offPageDir fl.c fl.w fl.N := by dsimp [a]; omega
      rw [hout₂₃_not_trie a (hnot_tr_below 0 (by decide) a (by dsimp [a]; omega) ha_lt_c0)
        (hnot_tr_below 1 (by decide) a (by dsimp [a]; omega) ha_lt_c0),
        hs₁_mem_ne a (by dsimp [a]; omega)]
      exact hzero_tab a (by dsimp [a]; omega) ha_lt_pd
    exact readPacked_zero (hz_word _ (by omega)) (hz_word _ (by omega))
  have hfm_s₃ : extractFastMeta fl s₃.mem =
      ⟨0, 0, 0, 0, 0, 0, 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ := by
    unfold extractFastMeta
    congr 1
    · exact hzero_s₃_hdr 3 (by decide) (Or.inl (by decide))
    · exact hzero_s₃_hdr 4 (by decide) (Or.inl (by decide))
    · exact hzero_s₃_hdr 5 (by decide) (Or.inl (by decide))
    · exact hzero_s₃_hdr 6 (by decide) (Or.inl (by decide))
    · exact hzero_s₃_hdr 7 (by decide) (Or.inl (by decide))
    · exact hzero_s₃_hdr 8 (by decide) (Or.inl (by decide))
    · exact hzero_s₃_hdr 9 (by decide) (Or.inl (by decide))
    · exact hzero_s₃_hdr 17 (by decide) (Or.inr rfl)
    all_goals (
      ext b; by_cases hb : b < numBucketsWhp fl.N
      · rw [ite_eq_left hb]; exact hzero_s₃_bkt _ (by omega)
      · rw [ite_eq_right hb])
  have hout_all : ∀ addr, ¬fl.OwnsFastAddr addr → s₃.mem addr = s.mem addr := fun addr ha =>
    (hout₃ addr (fun h => ha (fl.owns_of_trie hv (by decide) h))).trans
      ((hout₂ addr (fun h => ha (fl.owns_of_trie hv (by decide) h))).trans
        (hout₁ addr (fun h => ha (fl.owns_of_bpMeta hv h))))
  have hnot_seed : ∀ addr, fl.metaBase + offBktHash ≤ addr →
      addr < fl.metaBase + offBktMeta fl.c fl.w fl.N → ¬fl.OwnsFastAddr addr := by
    intro addr hlo hhi hown
    rcases hown with ⟨h1, h2⟩ | ⟨h1, _⟩ | hia
    · unfold offBktHash at hlo; omega
    · omega
    · exact hv.fb_valid.disjoint_seeds addr hlo (hv.w_eq ▸ hhi) hia
  have hst_tot : (Memory.spec 0).clientState s (fastInitZeroedProg fl.pBase) = s₃ := by
    unfold fastInitZeroedProg
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  have hc_tot : memoryCost (fastInitZeroedProg fl.pBase) s ≤ 40 := by
    unfold fastInitZeroedProg
    rw [Realization.memoryCost_bind', Realization.memoryCost_bind']
    change memoryCost (fastBpInitProg fl.pBase) s +
      (memoryCost (fastBufInitEmptyProg (fl.pBase, 0)) s₁ +
        memoryCost (fastBufInitEmptyProg (fl.pBase, 1)) s₂) ≤ 40
    omega
  rw [hst_tot]
  refine ⟨hfr₃.trans (hfr₂.trans hfr₁), hc_tot, ?_, hout_all, hio_s₃.2⟩
  have hQ_pos : 2 ≤ qEpochWhp fl.N := by
    unfold qEpochWhp
    calc 2 ≤ 2 ^ 18 := by decide
      _ ≤ slabScale fl.N ^ 18 := Nat.pow_le_pow_left (two_le_slabScale fl.N) 18
  have hL12_pos : 1 ≤ slabScale fl.N ^ 12 :=
    Nat.one_le_pow 12 _ (by have := two_le_slabScale fl.N; omega)
  have hsMax_pos : 0 < sMaxWhp fl.c fl.N := by
    unfold sMaxWhp
    exact Nat.mul_pos (by have := one_le_cEff fl.c; omega)
      (by have := two_le_slabScale fl.N; omega)
  have hcr0 : (extractFastMeta fl s₃.mem).curBufRole = 0 :=
    congrArg FastEpochMeta.curBufRole hfm_s₃
  have hss0 : (extractFastMeta fl s₃.mem).subStep = 0 :=
    congrArg FastEpochMeta.subStep hfm_s₃
  have hdp0 : (extractFastMeta fl s₃.mem).drainPos = 0 :=
    congrArg FastEpochMeta.drainPos hfm_s₃
  have hta0 : (extractFastMeta fl s₃.mem).tryAct = 0 :=
    congrArg FastEpochMeta.tryAct hfm_s₃
  have hrole0 : ∀ b, (extractFastMeta fl s₃.mem).curRole b = 0 :=
    fun b => congrFun (congrArg FastEpochMeta.curRole hfm_s₃) b
  have hins0 : ∀ b, (extractFastMeta fl s₃.mem).curIns b = 0 :=
    fun b => congrFun (congrArg FastEpochMeta.curIns hfm_s₃) b
  have hsc0 : ∀ b, (extractFastMeta fl s₃.mem).shadowCode b = 0 :=
    fun b => congrFun (congrArg FastEpochMeta.shadowCode hfm_s₃) b
  have hbm_s₃ : ∀ b < numBucketsWhp fl.N,
      let fm3 := extractFastMeta fl s₃.mem
      fm3.bktSalt b < sMaxWhp fl.c fl.N ∧
      fm3.curRole b < 3 ∧
      fm3.curIns b ≤ 8 * slabScale fl.N ^ 12 ∧
      (fm3.shadowCode b = 0 → ¬(fm3.tryAct = 1 ∧ fm3.tryBkt = b) →
        fm3.curIns b < 6 * slabScale fl.N ^ 12) := fun b _ =>
    ⟨by rw [congrFun (congrArg FastEpochMeta.bktSalt hfm_s₃) b]; exact hsMax_pos,
     by rw [hrole0 b]; decide,
     by rw [hins0 b]; exact Nat.zero_le _,
     fun _ _ => by rw [hins0 b]; omega⟩
  refine
    { param_table := hr₃.2.1
      hdr_N := (hout_all fl.metaBase hv.not_ownsFast_hdr0).trans hN
      mode_zero := hzero_s₃_hdr 2 (by decide) (Or.inl (by decide))
      seed_bkt := hbkt_rep.congr_on hw_pos fun a h1 h2 =>
        hout_all a (hnot_seed a
          (by dsimp only [FastEpochLayout.bktHashBase] at h1; exact h1)
          (by dsimp only [FastEpochLayout.bktHashBase] at h2
              unfold offBktMeta offFpHash offBktHash at *; omega))
      seed_fp := hfp_rep.congr_on hw_pos fun a h1 h2 =>
        hout_all a (hnot_seed a
          (by dsimp only [FastEpochLayout.fpHashBase] at h1
              unfold offFpHash offBktHash at *; omega)
          (by dsimp only [FastEpochLayout.fpHashBase] at h2
              unfold offBktMeta offFpHash offBktHash at *; omega))
      bp_inv := hbp_inv_s₃
      bkt_le_capMax := fun b _ => by
        rw [hbp_s₃]; unfold BlockPoolState.empty BlockPoolState.bktCount; simp
      refines := by
        rw [show (extractBlockPool fl.mp s₃.mem).nSide = 0 by rw [hbp_s₃]; rfl]
        exact PoolItemsRefines.empty ..
      role_lt := by rw [hcr0]; decide
      subStep_lt := by rw [hss0]; omega
      bkt_meta_bounds := hbm_s₃
      tiers := ?_ }
  dsimp only
  rw [hcr0, hss0, hdp0, Nat.sub_zero, htr₀_s₃, htr₁_s₃]
  refine ⟨fun _ => none, fun _ => none, fun _ _ => none,
    validBufTrie_empty _ _, rawBufTrieBounds_empty, rawClearableBounds_empty,
    by dsimp [emptyBufTrie]; omega, by dsimp [emptyBufTrie]; omega,
    (fun _ _ _ h => nomatch h), ?_, ?_, ?_, ?_,
    (by rw [hta0]; exact Nat.zero_le _),
    (fun h01 => by rw [hta0] at h01; nomatch h01)⟩
  · rw [ite_eq_left (by omega : 0 < qEpochWhp fl.N / 2)]
    exact ⟨validBufTrie_empty _ _, rawBufTrieBounds_empty, rawClearableBounds_empty,
      by dsimp [emptyBufTrie]; omega, by dsimp [emptyBufTrie]; omega, Nat.zero_le _,
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => nomatch h⟩
  · intro b hb
    refine ⟨?_, fun _ _ h => nomatch h⟩
    rw [hins0 b, hrole0 b]
    have hsl0 : extractBTreeSlice fl.btL b 0 s₃.mem =
        ⟨0, 0, (extractBTreeSlice fl.btL b 0 s₃.mem).nodes⟩ := by
      unfold extractBTreeSlice; dsimp only [FastEpochLayout.btL, epochBTreeLayout]
      rw [hzero_s₃_bkt _ (by omega), hzero_s₃_bkt _ (by omega)]
    rw [hsl0]; exact validWhpSlice_zero ..
  · intro b _ loc hloc
    rw [hbp_s₃] at hloc
    unfold BlockPoolState.empty BlockPoolState.bktCount at hloc; simp at hloc
  · intro b _ hsc; rw [hsc0 b] at hsc; exact absurd rfl hsc

/-! ## Section 3: Frame Helpers, `FastEpochPreAdvance`, and Deamortized Shadow Compaction -/

theorem fpHash_congr_salt {c U N s₁ s₂ : ℕ} {θ_fp : FpSeed c U N}
    {h₁ : s₁ < sMaxWhp c N} {h₂ : s₂ < sMaxWhp c N} (hs : s₁ = s₂) (u : Fin U) :
    fpHash c U N θ_fp ⟨s₁, h₁⟩ u = fpHash c U N θ_fp ⟨s₂, h₂⟩ u := by
  subst hs; rfl

theorem mapBTree_fpHash_congr (mapBTree : ℕ → ℕ → Option ℕ) {c U N b₁ b₂ s₁ s₂ : ℕ}
    {θ_fp : FpSeed c U N} {h₁ : s₁ < sMaxWhp c N} {h₂ : s₂ < sMaxWhp c N}
    (hb : b₁ = b₂) (hs : s₁ = s₂) (u : Fin U) :
    mapBTree b₁ (fpHash c U N θ_fp ⟨s₁, h₁⟩ u).val =
      mapBTree b₂ (fpHash c U N θ_fp ⟨s₂, h₂⟩ u).val := by
  subst hb; subst hs; rfl

theorem FastEpochLayout.Valid.bounds_le_N {fl : FastEpochLayout} {w fr : ℕ}
    (hv : fl.Valid w fr) :
    64 * slabScale fl.N ^ 12 ≤ fl.N ∧
    capMaxWhp fl.N ≤ fl.N ∧
    sMaxWhp fl.c fl.N ≤ fl.N ∧
    qEpochWhp fl.N ≤ fl.N := by
  have hce := le_codeExpWhp fl.c
  have hell := Dynamic.one_le_logLogFactor fl.N
  have hbc_l : 320 * Dynamic.logLogFactor fl.N ≤ Nat.log 2 fl.N :=
    ((Nat.mul_le_mul_right _ hce).trans (codeExpWhp_mul_ell_le_bCharWhp hv.thresh_le)).trans
      (Nat.div_le_self _ 4)
  have hb6 : 6 ≤ bWhp fl.N := by unfold bWhp; omega
  have hM64 : 64 ≤ numBucketsWhp fl.N :=
    (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hb6
  have hM_L12 := numBucketsWhp_mul_scale_pow12_le hv.thresh_le
  have h64_L12 : 64 * slabScale fl.N ^ 12 ≤ fl.N :=
    (Nat.mul_le_mul_right _ hM64).trans hM_L12
  have hcap : capMaxWhp fl.N ≤ fl.N := by unfold capMaxWhp; omega
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hsMax : sMaxWhp fl.c fl.N ≤ fl.N := by
    refine (sMaxWhp_le_two_pow_bCharWhp hv.thresh_le).trans ?_
    have hbc_le : bCharWhp fl.N ≤ Nat.log 2 fl.N := Nat.div_le_self _ 4
    exact (Nat.pow_le_pow_right (by decide) hbc_le).trans (Nat.pow_log_le_self 2 hN_pos.ne')
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, htl_le, _, _, _, _, _⟩ :=
    largeEpoch_param_bounds hv.thresh_le hv.N_le_U hv.fits_U
  exact ⟨h64_L12, hcap, hsMax, by omega⟩

theorem FastEpochInv.fastKeyAt_inj {fl : FastEpochLayout} {slack b₁ loc₁ b₂ loc₂ : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hinv : FastEpochInv fl slack seeds mem s_abs)
    (hb₁ : b₁ < numBucketsWhp fl.N) (hloc₁ : loc₁ < (extractBlockPool fl.mp mem).bktCount b₁)
    (hb₂ : b₂ < numBucketsWhp fl.N) (hloc₂ : loc₂ < (extractBlockPool fl.mp mem).bktCount b₂)
    (heq : fastKeyAt fl seeds.bkt mem b₁ loc₁ = fastKeyAt fl seeds.bkt mem b₂ loc₂) :
    b₁ = b₂ ∧ loc₁ = loc₂ := by
  obtain ⟨u₁, _, hu₁, _, hb_u₁, hq_u₁, _⟩ := hinv.bktSlot_refines hb₁ hloc₁
  obtain ⟨u₂, _, hu₂, _, hb_u₂, hq_u₂, _⟩ := hinv.bktSlot_refines hb₂ hloc₂
  have hu_eq : u₁ = u₂ := Fin.ext (hu₁.trans (heq.trans hu₂.symm))
  subst hu_eq
  have hb_eq : b₁ = b₂ := hb_u₁.symm.trans hb_u₂
  subst hb_eq
  have hcv : (extractBlockPool fl.mp mem).CoreValid := hinv.bp_inv.1.core
  set p₁ := (extractBlockPool fl.mp mem).toPhys b₁ loc₁
  set p₂ := (extractBlockPool fl.mp mem).toPhys b₁ loc₂
  have hp₁ := hcv.toPhys_lt hb₁ hloc₁
  have hp₂ := hcv.toPhys_lt hb₁ hloc₂
  have how₁ : ((extractBlockPool fl.mp mem).ownerOf p₁).1 = b₁ := by
    rw [hcv.ownerOf_toPhys hb₁ hloc₁]
  have how₂ : ((extractBlockPool fl.mp mem).ownerOf p₂).1 = b₁ := by
    rw [hcv.ownerOf_toPhys hb₁ hloc₂]
  have hqp : (slotIoPairAt fl.io mem p₁).1 = (slotIoPairAt fl.io mem p₂).1 :=
    hq_u₁.symm.trans hq_u₂
  have hp_eq : p₁ = p₂ := hinv.refines.slot_inj p₁ hp₁ p₂ hp₂ (how₁.trans how₂.symm) hqp
  have hloc_eq : ((extractBlockPool fl.mp mem).ownerOf p₁).2 =
      ((extractBlockPool fl.mp mem).ownerOf p₂).2 := congrArg Prod.snd (congrArg _ hp_eq)
  rw [hcv.ownerOf_toPhys hb₁ hloc₁, hcv.ownerOf_toPhys hb₁ hloc₂] at hloc_eq
  exact ⟨rfl, hloc_eq⟩

theorem fastBTreeMod_frame {fl : FastEpochLayout} {w fr b role : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hv : fl.Valid w fr) (_hb : b < numBucketsWhp fl.N) (hrole : role < 3)
    (hout : ∀ addr, ¬fl.btL.OwnsAddr addr → m₂ addr = m₁ addr)
    (hslot : ∀ idx < 16 * numBucketsWhp fl.N,
      idx ≠ 16 * b + 6 + 2 * role → idx ≠ 16 * b + 7 + 2 * role →
      readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w m₂ idx =
        readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w m₁ idx) :
    extractBlockPool fl.mp m₂ = extractBlockPool fl.mp m₁ ∧
    extractFastMeta fl m₂ = extractFastMeta fl m₁ ∧
    m₂ (fl.metaBase + 2) = m₁ (fl.metaBase + 2) ∧
    m₂ fl.metaBase = m₁ fl.metaBase ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) m₂ = extractBufTrie (fl.trieL r) m₁) ∧
    (∀ addr, fl.io.OwnsAddr addr → m₂ addr = m₁ addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → m₂ addr = m₁ addr) := by
  have hmv := hv.mp_valid
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := by
    have := hmv.offBktMeta_ge; dsimp [FastEpochLayout.mp, epochBpMetaLayout] at this; exact this
  have hbt_bds : ∀ addr, fl.btL.OwnsAddr addr →
      fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr ∧
      addr < fl.metaBase + offPageDir fl.c fl.w fl.N := fun addr hbt => by
    have hbv := hv.bt_valid
    have hd0 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hd1 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hd2 := hbv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) (role := 0) (by decide)
    dsimp only [FastEpochLayout.btL, epochBTreeLayout, BTreeEpochLayout.OwnsAddr,
      BTreeEpochLayout.totalNodes] at hbt hd0 hd1 hd2
    have htot : 3 * numBucketsWhp fl.N * nSliceWhp fl.N = totalBTreeNodesWhp fl.N := rfl
    rw [htot] at hbt hd1 hd2
    rcases hbt with b1 | b2 | b3 | b4 <;> exact ⟨by omega, by omega⟩
  have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr → m₂ addr = m₁ addr := fun addr ha =>
    hout addr fun hb_in => ha (fl.owns_of_btree hv hb_in)
  have hout_io : ∀ addr, fl.io.OwnsAddr addr → m₂ addr = m₁ addr := fun addr hia =>
    hout addr fun hb_in =>
      have ⟨hb1, hb2⟩ := hbt_bds addr hb_in
      hv.disj_fast_io addr (Or.inr ⟨by omega, hb2⟩) hia
  have hout_hdr : ∀ k < 32, m₂ (fl.metaBase + k) = m₁ (fl.metaBase + k) := fun k hk =>
    hout (fl.metaBase + k) fun hbt => by
      have ⟨hb1, _⟩ := hbt_bds (fl.metaBase + k) hbt
      omega
  have hnot_bt_tab : ∀ addr,
      fl.metaBase + offSlabDir fl.c fl.w fl.N ≤ addr →
      addr < fl.metaBase + offBTreeMeta fl.c fl.w fl.N → ¬fl.btL.OwnsAddr addr :=
    fun addr hlo hhi hbt => fl.disj_btree_bpTable hbt ⟨hlo, hhi⟩
  have hbp_eq : extractBlockPool fl.mp m₂ = extractBlockPool fl.mp m₁ := by
    have hd1 := hmv.offSlabDir_ge; have hd2 := hmv.offTailDir_ge
    have hd3 := hmv.offSlabOwner_ge; have hd4 := hmv.offTailOwner_ge
    dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hd1 hd2 hd3 hd4
    have hob : offTailOwner fl.c fl.w fl.N + packedWords (16 * maxTailWhp fl.N)
        (globalPtrBits fl.N) fl.w = offBTreeMeta fl.c fl.w fl.N := rfl
    have hsd : ∀ idx < fl.mp.M * fl.mp.maxSlabs,
        readPacked (fl.mp.metaBase + fl.mp.offSlabDir) fl.mp.ptrB fl.mp.w m₂ idx =
          readPacked (fl.mp.metaBase + fl.mp.offSlabDir) fl.mp.ptrB fl.mp.w m₁ idx :=
      fun idx hi => readPacked_congr hw_pos
        (fun a ha => hout a (hnot_bt_tab a
          (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega)
          (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))) hi
    have htd : ∀ idx < 8 * fl.mp.M * fl.mp.K,
        readPacked (fl.mp.metaBase + fl.mp.offTailDir) fl.mp.ptrB fl.mp.w m₂ idx =
          readPacked (fl.mp.metaBase + fl.mp.offTailDir) fl.mp.ptrB fl.mp.w m₁ idx :=
      fun idx hi => readPacked_congr hw_pos
        (fun a ha => hout a (hnot_bt_tab a
          (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega)
          (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))) hi
    have hso : ∀ idx < 4 * fl.mp.maxBlocks,
        readPacked (fl.mp.metaBase + fl.mp.offSlabOwner) fl.mp.ptrB fl.mp.w m₂ idx =
          readPacked (fl.mp.metaBase + fl.mp.offSlabOwner) fl.mp.ptrB fl.mp.w m₁ idx :=
      fun idx hi => readPacked_congr hw_pos
        (fun a ha => hout a (hnot_bt_tab a
          (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega)
          (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))) hi
    have hto : ∀ idx < 16 * fl.mp.maxTail,
        readPacked (fl.mp.metaBase + fl.mp.offTailOwner) fl.mp.ptrB fl.mp.w m₂ idx =
          readPacked (fl.mp.metaBase + fl.mp.offTailOwner) fl.mp.ptrB fl.mp.w m₁ idx :=
      fun idx hi => readPacked_congr hw_pos
        (fun a ha => hout a (hnot_bt_tab a
          (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega)
          (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))) hi
    have hm_eq : fl.mp.M = numBucketsWhp fl.N := rfl
    unfold extractBlockPool
    congr 1
    · exact hout_hdr 1 (by decide)
    · ext x; by_cases hx : x < fl.mp.M
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hslot _ (by omega) (by omega) (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · ext x; by_cases hx : x < fl.mp.M
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hslot _ (by omega) (by omega) (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · ext x; by_cases hx : x < fl.mp.M
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hslot _ (by omega) (by omega) (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · ext x; by_cases hx : x < fl.mp.M
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hslot _ (by omega) (by omega) (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · ext x; by_cases hx : x < fl.mp.M
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hslot _ (by omega) (by omega) (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · ext x y; by_cases hxy : x < fl.mp.M ∧ y < fl.mp.maxSlabs
      · have hlt : x * fl.mp.maxSlabs + y < fl.mp.M * fl.mp.maxSlabs := by
          calc x * fl.mp.maxSlabs + y < (x + 1) * fl.mp.maxSlabs := by ring_nf; omega
            _ ≤ fl.mp.M * fl.mp.maxSlabs := Nat.mul_le_mul_right _ hxy.1
        rw [ite_eq_left hxy, ite_eq_left hxy]; exact hsd _ hlt
      · rw [ite_eq_right hxy, ite_eq_right hxy]
    · ext x y; by_cases hxy : x < fl.mp.M ∧ y < 6 * fl.mp.K
      · have h6eq : 6 * fl.mp.K * fl.mp.M = 6 * (fl.mp.M * fl.mp.K) := by ring
        have h8eq : 8 * fl.mp.M * fl.mp.K = 8 * (fl.mp.M * fl.mp.K) := by ring
        have hlt : 6 * fl.mp.K * x + y < 8 * fl.mp.M * fl.mp.K := by
          calc 6 * fl.mp.K * x + y < 6 * fl.mp.K * (x + 1) := by ring_nf; omega
            _ ≤ 6 * fl.mp.K * fl.mp.M := Nat.mul_le_mul_left _ hxy.1
            _ ≤ 8 * fl.mp.M * fl.mp.K := by omega
        rw [ite_eq_left hxy, ite_eq_left hxy]; exact htd _ hlt
      · rw [ite_eq_right hxy, ite_eq_right hxy]
    · ext x; by_cases hx : x < fl.mp.maxBlocks
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hso _ (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · ext x; by_cases hx : x < fl.mp.maxBlocks
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hso _ (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · ext x; by_cases hx : x < fl.mp.maxBlocks
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hso _ (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · exact hout_hdr 10 (by decide)
    · ext x; by_cases hx : x < fl.mp.maxBlocks
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hso _ (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · exact hout_hdr 11 (by decide)
    · exact hout_hdr 12 (by decide)
    · ext x; by_cases hx : x < 8 * fl.mp.M
      · have hx_mk : x < fl.mp.M * fl.mp.K :=
          lt_of_lt_of_le hx ((Nat.mul_comm 8 fl.mp.M).le.trans
            (Nat.mul_le_mul_left fl.mp.M (le_trans (by decide : 8 ≤ 64) hmv.K_ge)))
        have h6eq : 6 * fl.mp.M * fl.mp.K = 6 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 6 _ _
        have h8eq : 8 * fl.mp.M * fl.mp.K = 8 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 8 _ _
        rw [ite_eq_left hx, ite_eq_left hx]; exact htd _ (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · ext x; by_cases hx : x < 8 * fl.mp.M
      · have hx_mk : x < fl.mp.M * fl.mp.K :=
          lt_of_lt_of_le hx ((Nat.mul_comm 8 fl.mp.M).le.trans
            (Nat.mul_le_mul_left fl.mp.M (le_trans (by decide : 8 ≤ 64) hmv.K_ge)))
        have h7eq : 7 * fl.mp.M * fl.mp.K = 7 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 7 _ _
        have h8eq : 8 * fl.mp.M * fl.mp.K = 8 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 8 _ _
        rw [ite_eq_left hx, ite_eq_left hx]; exact htd _ (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · ext x; by_cases hx : x < 8 * fl.mp.M * fl.mp.K
      · have h16mt : 16 * (fl.mp.M * fl.mp.K) ≤ 16 * fl.mp.maxTail := by
          have := hmv.sixteen_MK_le_maxTail; rwa [Nat.mul_assoc] at this
        have h8eq : 8 * fl.mp.M * fl.mp.K = 8 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 8 _ _
        rw [ite_eq_left hx, ite_eq_left hx]; exact hto x (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · ext x; by_cases hx : x < 8 * fl.mp.M * fl.mp.K
      · have h16mt : 16 * (fl.mp.M * fl.mp.K) ≤ 16 * fl.mp.maxTail := by
          have := hmv.sixteen_MK_le_maxTail; rwa [Nat.mul_assoc] at this
        have h8eq : 8 * fl.mp.M * fl.mp.K = 8 * (fl.mp.M * fl.mp.K) := Nat.mul_assoc 8 _ _
        rw [ite_eq_left hx, ite_eq_left hx]; exact hto _ (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
    · exact hout_hdr 13 (by decide)
    · exact hout_hdr 14 (by decide)
    · exact hout_hdr 15 (by decide)
    · exact hout_hdr 16 (by decide)
  have hfm_eq : extractFastMeta fl m₂ = extractFastMeta fl m₁ := by
    unfold extractFastMeta
    congr 1
    · exact hout_hdr 3 (by decide)
    · exact hout_hdr 4 (by decide)
    · exact hout_hdr 5 (by decide)
    · exact hout_hdr 6 (by decide)
    · exact hout_hdr 7 (by decide)
    · exact hout_hdr 8 (by decide)
    · exact hout_hdr 9 (by decide)
    · exact hout_hdr 17 (by decide)
    all_goals (
      ext x; by_cases hx : x < numBucketsWhp fl.N
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hslot _ (by omega) (by omega) (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx])
  have htr_eq : ∀ r < 2,
      extractBufTrie (fl.trieL r) m₂ = extractBufTrie (fl.trieL r) m₁ := fun r hr_lt =>
    extractBufTrie_congr hw_pos fun addr hta =>
      hout addr fun hb_in => fl.disj_btree_trie hv hr_lt hb_in hta
  have h0_eq : m₂ fl.metaBase = m₁ fl.metaBase := by
    simpa only [Nat.add_zero] using hout_hdr 0 (by decide)
  exact ⟨hbp_eq, hfm_eq, hout_hdr 2 (by decide), h0_eq, htr_eq, hout_io, hout_fast⟩

theorem fastTrieMod_frame {fl : FastEpochLayout} {w fr role : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hv : fl.Valid w fr) (hrole : role < 2)
    (hout : ∀ addr, ¬(fl.trieL role).OwnsAddr addr → m₂ addr = m₁ addr) :
    extractBlockPool fl.mp m₂ = extractBlockPool fl.mp m₁ ∧
    extractFastMeta fl m₂ = extractFastMeta fl m₁ ∧
    m₂ (fl.metaBase + 2) = m₁ (fl.metaBase + 2) ∧
    m₂ fl.metaBase = m₁ fl.metaBase ∧
    (∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r m₂ = extractBTreeSlice fl.btL b r m₁) ∧
    extractBufTrie (fl.trieL (1 - role)) m₂ = extractBufTrie (fl.trieL (1 - role)) m₁ ∧
    (∀ addr, fl.io.OwnsAddr addr → m₂ addr = m₁ addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → m₂ addr = m₁ addr) := by
  have hmv := hv.mp_valid
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hm0 := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) (role := 0) (by decide)
  have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := by
    have := hmv.offBktMeta_ge; dsimp [FastEpochLayout.mp, epochBpMetaLayout] at this; exact this
  have hob : offTailOwner fl.c fl.w fl.N + packedWords (16 * maxTailWhp fl.N)
      (globalPtrBits fl.N) fl.w = offBTreeMeta fl.c fl.w fl.N := rfl
  have hbt_v : offBTreeMeta fl.c fl.w fl.N ≤ offBTreeVals fl.c fl.w fl.N := by
    unfold offBTreeVals offBTreeKeys; omega
  have hbelow : ∀ addr, fl.metaBase ≤ addr →
      addr < fl.metaBase + offTrieChild fl.c fl.w fl.N 0 → m₂ addr = m₁ addr :=
    fun addr hlo hhi => hout addr fun hta =>
      fl.disj_trie_bpAndMeta hv hrole hta (Or.inl ⟨hlo, hhi⟩)
  have hout_io : ∀ addr, fl.io.OwnsAddr addr → m₂ addr = m₁ addr :=
    fun addr hia => hout addr fun hta => fl.disj_trie_bpAndMeta hv hrole hta (Or.inr hia)
  have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr → m₂ addr = m₁ addr :=
    fun addr ha => hout addr fun hta => ha (fl.owns_of_trie hv hrole hta)
  have hbp_eq : extractBlockPool fl.mp m₂ = extractBlockPool fl.mp m₁ := by
    refine extractBlockPool_congr hw_pos hmv.K_ge (by
      have h := hmv.sixteen_MK_le_maxTail; rw [Nat.mul_assoc] at h; omega) fun addr hma => ?_
    rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | ⟨h10, h17⟩) | ⟨hlo, hhi⟩ <;>
      (dsimp [FastEpochLayout.mp, epochBpMetaLayout] at *; exact hbelow addr (by omega) (by omega))
  have hfm_eq : extractFastMeta fl m₂ = extractFastMeta fl m₁ := by
    have hbkt_eq : ∀ idx < 16 * numBucketsWhp fl.N,
        readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w m₂ idx =
          readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w m₁ idx :=
      fun idx hi => readPacked_congr hw_pos (fun a ha => by
        have hd1 := hmv.offSlabDir_ge; dsimp [FastEpochLayout.mp, epochBpMetaLayout] at hd1
        have hd_bt : offSlabDir fl.c fl.w fl.N ≤ offBTreeMeta fl.c fl.w fl.N := by
          unfold offBTreeMeta offTailOwner offSlabOwner offTailDir; omega
        exact hbelow a (by omega) (by omega)) hi
    unfold extractFastMeta
    congr 1
    · exact hbelow _ (by omega) (by omega)
    · exact hbelow _ (by omega) (by omega)
    · exact hbelow _ (by omega) (by omega)
    · exact hbelow _ (by omega) (by omega)
    · exact hbelow _ (by omega) (by omega)
    · exact hbelow _ (by omega) (by omega)
    · exact hbelow _ (by omega) (by omega)
    · exact hbelow _ (by omega) (by omega)
    all_goals (
      ext x; by_cases hx : x < numBucketsWhp fl.N
      · rw [ite_eq_left hx, ite_eq_left hx]; exact hbkt_eq _ (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx])
  have hbt_eq : ∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r m₂ = extractBTreeSlice fl.btL b r m₁ := by
    intro b hb r hr_lt
    refine extractBTreeSlice_congr_entries
      (readPacked_congr hw_pos (N := 16 * numBucketsWhp fl.N)
        (fun a ha => hout a fun hta => fl.disj_btree_trie hv hrole (Or.inl ha) hta) (by omega))
      (readPacked_congr hw_pos (N := 16 * numBucketsWhp fl.N)
        (fun a ha => hout a fun hta => fl.disj_btree_trie hv hrole (Or.inl ha) hta) (by omega))
      fun u hu => ?_
    have htot : (3 * b + r) * (fl.btL).nSlice + u < (fl.btL).totalNodes := by
      dsimp only [FastEpochLayout.btL, epochBTreeLayout, BTreeEpochLayout.totalNodes] at hu ⊢
      calc (3 * b + r) * nSliceWhp fl.N + u
          < (3 * b + r + 1) * nSliceWhp fl.N := by ring_nf; omega
        _ ≤ (3 * numBucketsWhp fl.N) * nSliceWhp fl.N := Nat.mul_le_mul_right _ (by omega)
    exact ⟨readPacked_congr hw_pos
        (fun a ha => hout a fun hta => fl.disj_btree_trie hv hrole (Or.inr (Or.inl ha)) hta) htot,
      readPacked_congr hw_pos
        (fun a ha => hout a fun hta => fl.disj_btree_trie hv hrole
          (Or.inr (Or.inr (Or.inl ha))) hta) htot,
      readPacked_congr hw_pos
        (fun a ha => hout a fun hta => fl.disj_btree_trie hv hrole
          (Or.inr (Or.inr (Or.inr ha))) hta) htot⟩
  have htr_other : extractBufTrie (fl.trieL (1 - role)) m₂ =
      extractBufTrie (fl.trieL (1 - role)) m₁ :=
    extractBufTrie_congr hw_pos fun addr ht' =>
      hout addr fun hta =>
        epochTrieLayout_disjoint (by omega) hrole (by omega) ht' hta
  exact ⟨hbp_eq, hfm_eq, hbelow _ (by omega) (by omega), hbelow _ le_rfl (by omega),
    hbt_eq, htr_other, hout_io, hout_fast⟩

/-- Read `bp.bktCount b` via `pBase` (`¬ReadsWidth`). -/
def fastReadBktCntProg : ℕ × ℕ → Memory.Prog ℕ
  | (pBase, b) => do
    let mctx ← loadBpMetaCtxProg pBase
    bpReadBktCountProg (mctx, b)

@[simp] theorem runClient_state_fastReadBktCntProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastReadBktCntProg x)) = s := by
  rcases x with ⟨pBase, b⟩
  unfold clientOutState fastReadBktCntProg; dsimp only
  rw [prog_runClient_state_bind, clientState_loadBpMetaCtxProg]
  exact clientState_bpReadBktCountProg _ s

theorem clientState_fastReadBktCntProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastReadBktCntProg x) = s :=
  runClient_state_fastReadBktCntProg x s

theorem realizesBounded_fastReadBktCnt :
    RealizesBounded .exact fastReadBktCntProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlm := realizesBounded_loadBpMetaCtx
  have hbc := realizesBounded_bpReadBktCount
  realize
  all_goals (
    rcases d with ⟨pBase, b⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    try simp only [StateTransitionSpec.clientState, runClient_state_loadBpMetaCtxProg] at *
    first | exact hw6 | exact hp | (
      have hl_res := clientResult_loadBpMetaCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]; simpa using hr.1.mp_valid))

theorem fastReadBktCntProg_spec {fl : FastEpochLayout} {w b : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hcv : (extractBlockPool fl.mp s.mem).CoreValid)
    (hb : b < numBucketsWhp fl.N) :
    (Memory.spec 0).clientResult s (fastReadBktCntProg (fl.pBase, b)) =
      (extractBlockPool fl.mp s.mem).bktCount b ∧
    memoryCost (fastReadBktCntProg (fl.pBase, b)) s ≤ 20 := by
  unfold fastReadBktCntProg; dsimp only
  rw [prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_loadBpMetaCtxProg, clientResult_loadBpMetaCtxProg hr.2.1,
    memoryCost_loadBpMetaCtxProg]
  have hres := bpReadBktCountProg_spec hcv hb
  have hc := (bpReadBktCountProg_frame fl.mp b).frame.cost_le s
  exact ⟨hres, by omega⟩

theorem fastBTreeLookupProg_spec {fl : FastEpochLayout} {w b role q insCount : ℕ}
    {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hb : b < numBucketsWhp fl.N) (hrole : role < 3)
    (hins : insCount ≤ 8 * slabScale fl.N ^ 12)
    (hv : ValidWhpSlice fl.N insCount (extractBTreeSlice fl.btL b role s.mem) mapFn)
    (hq : q < 2 ^ fpBitsWhp fl.N) :
    (Memory.spec 0).clientResult s (fastBTreeLookupProg ((fl.pBase, (b, role)), q)) =
      (match mapFn q with | none => (0, 0) | some v => (1, v)) ∧
    memoryCost (fastBTreeLookupProg ((fl.pBase, (b, role)), q)) s ≤ 6 * hMaxBTree + 35 := by
  have ⟨hvf, hpt, _, _⟩ := hr
  cases hvf.w_eq
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hfpw : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (9, 2))) =
      (fpBitsWhp fl.N, fl.w) := by
    unfold readParam2Prog
    simp [hpt 9 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
  have hfp_lt_w : fpBitsWhp fl.N < fl.w := by
    have h8 : 8 ≤ tMinWhp fl.N := hvf.bt_valid.2.2.2.1
    have h4k : 4 * tMinWhp fl.N * (fpBitsWhp fl.N + 2) < fl.w :=
      hvf.bt_valid.2.2.2.2.2.2.2.2.2.1
    nlinarith
  have hc1 : b < numBucketsWhp fl.N ∧ role < 3 ∧ fpBitsWhp fl.N < fl.w :=
    ⟨hb, hrole, hfp_lt_w⟩
  have hc2 : q < (1 <<< fpBitsWhp fl.N) := by rwa [Nat.shiftLeft_eq, one_mul]
  obtain ⟨_, hcost, hres⟩ := btreeLookupBoundedProg_spec (c := fl.c) (N := fl.N) (L := fl.btL)
    hvf.thresh_le rfl hvf.bt_valid hb hrole hins hv hq
  unfold fastBTreeLookupProg; dsimp only
  have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
  have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := hm11
  have c_rp : memoryCost (readParam2Prog (fl.pBase, (9, 2))) s = 2 := by
    unfold readParam2Prog; simp
  rw [prog_clientResult_bind, Realization.memoryCost_bind', hr11_st, hr11_r, prog_memoryCost_read,
    prog_clientResult_bind, Realization.memoryCost_bind', clientState_readParam2Prog, hfpw, c_rp,
    ite_eq_left hc1, ite_eq_left hc2, prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_loadBTreeSliceCtxProg, clientResult_loadBTreeSliceCtxProg hpt,
    memoryCost_loadBTreeSliceCtxProg]
  exact ⟨hres, by omega⟩

theorem fastBTreeInsertProg_spec {fl : FastEpochLayout} {w b role q val insCount : ℕ}
    {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hb : b < numBucketsWhp fl.N) (hrole : role < 3)
    (hins : insCount ≤ 8 * slabScale fl.N ^ 12)
    (hv : ValidWhpSlice fl.N insCount (extractBTreeSlice fl.btL b role s.mem) mapFn)
    (hq : q < 2 ^ fpBitsWhp fl.N) (hval : val < 2 ^ valLaneBitsWhp fl.N) :
    let s' := (Memory.spec 0).clientState s (fastBTreeInsertProg ((fl.pBase, (b, role)), (q, val)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBTreeInsertProg ((fl.pBase, (b, role)), (q, val))) s ≤ 72 * hMaxBTree + 120 ∧
    ValidWhpSlice fl.N (insCount + 1) (extractBTreeSlice fl.btL b role s'.mem)
      (Function.update mapFn q (some val)) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ role' < 3, (b' ≠ b ∨ role' ≠ role) →
      extractBTreeSlice fl.btL b' role' s'.mem = extractBTreeSlice fl.btL b' role' s.mem) ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  have ⟨hvf, hpt, _, _⟩ := hr
  cases hvf.w_eq
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hfvw : (Memory.spec 0).clientResult s (readParam4Prog ((fl.pBase, (9, 19)), (2, 2))) =
      ((fpBitsWhp fl.N, valLaneBitsWhp fl.N), (fl.w, fl.w)) := by
    unfold readParam4Prog readParam2Prog
    simp [hpt 9 (by decide), hpt 19 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
  have hc1 : b < numBucketsWhp fl.N ∧ role < 3 ∧ fpBitsWhp fl.N < fl.w ∧
      valLaneBitsWhp fl.N < fl.w := by
    have h8 : 8 ≤ tMinWhp fl.N := hvf.bt_valid.2.2.2.1
    have h4k : 4 * tMinWhp fl.N * (fpBitsWhp fl.N + 2) < fl.w :=
      hvf.bt_valid.2.2.2.2.2.2.2.2.2.1
    have h4v : 4 * tMinWhp fl.N * valLaneBitsWhp fl.N < fl.w :=
      hvf.bt_valid.2.2.2.2.2.2.2.2.2.2.1
    exact ⟨hb, hrole, by nlinarith, by nlinarith⟩
  have hc2 : q < (1 <<< fpBitsWhp fl.N) ∧ val < (1 <<< valLaneBitsWhp fl.N) := by
    simpa only [Nat.shiftLeft_eq, one_mul] using ⟨hq, hval⟩
  obtain ⟨hfr, hcost, _, _, hv', hother, hslot, hout⟩ :=
    btreeInsertBoundedProg_spec (c := fl.c) (N := fl.N) (L := fl.btL)
      hvf.thresh_le rfl hvf.bt_valid hb hrole hins hv hq hval
  have hst : (Memory.spec 0).clientState s
      (fastBTreeInsertProg ((fl.pBase, (b, role)), (q, val))) =
      (Memory.spec 0).clientState s
        (btreeInsertBoundedProg (fl.btL.toSliceCtx b role, (q, val))) := by
    unfold fastBTreeInsertProg; dsimp only
    have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
    have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
        numBucketsWhp fl.N := hm11
    rw [StateTransitionSpec.clientState_bind, hr11_st, hr11_r,
      StateTransitionSpec.clientState_bind, clientState_readParam4Prog, hfvw]
    dsimp only
    rw [ite_eq_left hc1, ite_eq_left hc2, StateTransitionSpec.clientState_bind,
      clientState_loadBTreeSliceCtxProg, clientResult_loadBTreeSliceCtxProg hpt]
  have hc_tot : memoryCost (fastBTreeInsertProg ((fl.pBase, (b, role)), (q, val))) s ≤
      72 * hMaxBTree + 120 := by
    unfold fastBTreeInsertProg; dsimp only
    have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
    have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
        numBucketsWhp fl.N := hm11
    have c_rq : memoryCost (readParam4Prog ((fl.pBase, (9, 19)), (2, 2))) s = 4 := by
      unfold readParam4Prog readParam2Prog; simp
    rw [Realization.memoryCost_bind', hr11_st, hr11_r, prog_memoryCost_read,
      Realization.memoryCost_bind', clientState_readParam4Prog, hfvw, c_rq]
    dsimp only
    rw [ite_eq_left hc1, ite_eq_left hc2, Realization.memoryCost_bind',
      clientState_loadBTreeSliceCtxProg, clientResult_loadBTreeSliceCtxProg hpt,
      memoryCost_loadBTreeSliceCtxProg]
    omega
  rw [hst]
  obtain ⟨hbp_eq, hfm_eq, hm2_eq, hm0_eq, htr_eq, hout_io, hout_fast⟩ :=
    fastBTreeMod_frame hvf hb hrole hout hslot
  exact ⟨hfr, hr.of_frame hfr hout_fast, hc_tot, hv',
    fun b' hb' role' hrole' hne => hother b' role' hb' hrole' hne,
    hbp_eq, hfm_eq, hm2_eq, hm0_eq, htr_eq, hout_io, hout_fast⟩

theorem fastBufCheckSlotProg_spec {fl : FastEpochLayout} {w role id : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hrole : role < 2)
    (hia : (extractBufTrie (fl.trieL role) s.mem).itemAlloc ≤ qEpochWhp fl.N) :
    (Memory.spec 0).clientResult s (fastBufCheckSlotProg ((fl.pBase, role), id)) =
      (match bufCheckSlot (extractBufTrie (fl.trieL role) s.mem) id with
       | none => (0, (0, 0))
       | some (b, loc) => (1, (b, loc))) ∧
    memoryCost (fastBufCheckSlotProg ((fl.pBase, role), id)) s ≤ 22 := by
  cases hr.1.w_eq
  unfold fastBufCheckSlotProg; dsimp only
  rw [ite_eq_left hrole, prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_loadTrieCtxProg, clientResult_loadTrieCtxProg hr.2.1 hrole,
    memoryCost_loadTrieCtxProg]
  obtain ⟨_, hc, hres⟩ :=
    bufCheckSlotBoundedProg_spec (hr.1.trie_valid hrole) hia id
  exact ⟨hres, by omega⟩

theorem fastBufClearStepsProg_spec {fl : FastEpochLayout} {w role : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hrole : role < 2)
    (hcl : ClearableBufTrie (extractBufTrie (fl.trieL role) s.mem))
    (hna : (extractBufTrie (fl.trieL role) s.mem).nodeAlloc ≤ maxTrieNodesWhp fl.c fl.N) :
    let s' := (Memory.spec 0).clientState s (fastBufClearStepsProg (fl.pBase, role))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBufClearStepsProg (fl.pBase, role)) s ≤ 96 * (cTabWhp fl.c + 2) + 11 ∧
    extractBufTrie (fl.trieL role) s'.mem =
      bufClearSteps (4 * (cTabWhp fl.c + 2)) (extractBufTrie (fl.trieL role) s.mem) ∧
    ClearableBufTrie (extractBufTrie (fl.trieL role) s'.mem) ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    (∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r s'.mem = extractBTreeSlice fl.btL b r s.mem) ∧
    extractBufTrie (fl.trieL (1 - role)) s'.mem = extractBufTrie (fl.trieL (1 - role)) s.mem ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  cases hr.1.w_eq
  obtain ⟨hfr, hr', hc, _⟩ := fastBufClearStepsProg_ready (role := role) hr
  have hm28 : s.mem (fl.pBase + 28) = 4 * (cTabWhp fl.c + 2) := hr.2.1 28 (by decide)
  have hst : (Memory.spec 0).clientState s (fastBufClearStepsProg (fl.pBase, role)) =
      (Memory.spec 0).clientState s
        (bufClearStepsBoundedProg ((fl.trieL role).toCtx, 4 * (cTabWhp fl.c + 2))) := by
    unfold fastBufClearStepsProg; dsimp only
    have hr_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 28)) = s := rfl
    have hr_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 28)) =
        4 * (cTabWhp fl.c + 2) := hm28
    rw [ite_eq_left hrole, StateTransitionSpec.clientState_bind, hr_st, hr_r,
      StateTransitionSpec.clientState_bind, clientState_loadTrieCtxProg,
      clientResult_loadTrieCtxProg hr.2.1 hrole]
  have htv := hr.1.trie_valid hrole
  have htv_tight : (fl.trieL role).Valid (fl.trieL role).w
      ((fl.trieL role).metaBase + (fl.trieL role).offItem +
        packedWords (6 * (fl.trieL role).qMax + 6) (fl.trieL role).ptrB (fl.trieL role).w) :=
    ⟨htv.1, htv.2.1, htv.2.2.1, htv.2.2.2.1, htv.2.2.2.2.1, htv.2.2.2.2.2.1,
      htv.2.2.2.2.2.2.1, htv.2.2.2.2.2.2.2.1, htv.2.2.2.2.2.2.2.2.1,
      htv.2.2.2.2.2.2.2.2.2.1, htv.2.2.2.2.2.2.2.2.2.2.1, htv.2.2.2.2.2.2.2.2.2.2.2.1,
      htv.2.2.2.2.2.2.2.2.2.2.2.2.1, htv.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      htv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, le_rfl⟩
  obtain ⟨_, _, hext, hcl', hout⟩ :=
    bufClearStepsBoundedProg_spec htv_tight (4 * (cTabWhp fl.c + 2)) s hcl hna
  rw [← hst] at hext hcl' hout
  obtain ⟨hbp_eq, hfm_eq, hm2_eq, hm0_eq, hbt_eq, htr_o, hout_io, hout_fast⟩ :=
    fastTrieMod_frame hr.1 hrole hout
  exact ⟨hfr, hr', hc, hext, hcl', hbp_eq, hfm_eq, hm2_eq, hm0_eq, hbt_eq, htr_o,
    hout_io, hout_fast⟩

theorem fastBTreeDeleteProg_spec {fl : FastEpochLayout} {w b role q insCount : ℕ}
    {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hb : b < numBucketsWhp fl.N) (hrole : role < 3)
    (hins : insCount ≤ 8 * slabScale fl.N ^ 12)
    (hv : ValidWhpSlice fl.N insCount (extractBTreeSlice fl.btL b role s.mem) mapFn)
    (hq : q < 2 ^ fpBitsWhp fl.N) :
    let s' := (Memory.spec 0).clientState s (fastBTreeDeleteProg ((fl.pBase, (b, role)), q))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBTreeDeleteProg ((fl.pBase, (b, role)), q)) s ≤ 6 * hMaxBTree + 50 ∧
    ValidWhpSlice fl.N insCount (extractBTreeSlice fl.btL b role s'.mem)
      (Function.update mapFn q none) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ role' < 3, (b' ≠ b ∨ role' ≠ role) →
      extractBTreeSlice fl.btL b' role' s'.mem = extractBTreeSlice fl.btL b' role' s.mem) ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  have ⟨hvf, hpt, _, _⟩ := hr
  cases hvf.w_eq
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hfpw : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (9, 2))) =
      (fpBitsWhp fl.N, fl.w) := by
    unfold readParam2Prog
    simp [hpt 9 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
  have hc1 : b < numBucketsWhp fl.N ∧ role < 3 ∧ fpBitsWhp fl.N < fl.w := by
    have h8 : 8 ≤ tMinWhp fl.N := hvf.bt_valid.2.2.2.1
    have h4k : 4 * tMinWhp fl.N * (fpBitsWhp fl.N + 2) < fl.w :=
      hvf.bt_valid.2.2.2.2.2.2.2.2.2.1
    exact ⟨hb, hrole, by nlinarith⟩
  have hc2 : q < (1 <<< fpBitsWhp fl.N) := by rwa [Nat.shiftLeft_eq, one_mul]
  obtain ⟨hfr, hcost, _, hv', hother, hslot, hout⟩ :=
    btreeDeleteBoundedProg_spec (c := fl.c) (N := fl.N) (L := fl.btL)
      hvf.thresh_le rfl hvf.bt_valid hb hrole hins hv hq
  have hst : (Memory.spec 0).clientState s (fastBTreeDeleteProg ((fl.pBase, (b, role)), q)) =
      (Memory.spec 0).clientState s (btreeDeleteBoundedProg (fl.btL.toSliceCtx b role, q)) := by
    unfold fastBTreeDeleteProg; dsimp only
    have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
    have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
        numBucketsWhp fl.N := hm11
    rw [StateTransitionSpec.clientState_bind, hr11_st, hr11_r,
      StateTransitionSpec.clientState_bind, clientState_readParam2Prog, hfpw,
      ite_eq_left hc1, ite_eq_left hc2, StateTransitionSpec.clientState_bind,
      clientState_loadBTreeSliceCtxProg, clientResult_loadBTreeSliceCtxProg hpt]
  have hc_tot : memoryCost (fastBTreeDeleteProg ((fl.pBase, (b, role)), q)) s ≤
      6 * hMaxBTree + 50 := by
    unfold fastBTreeDeleteProg; dsimp only
    have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
    have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
        numBucketsWhp fl.N := hm11
    have c_rp : memoryCost (readParam2Prog (fl.pBase, (9, 2))) s = 2 := by
      unfold readParam2Prog; simp
    rw [Realization.memoryCost_bind', hr11_st, hr11_r, prog_memoryCost_read,
      Realization.memoryCost_bind', clientState_readParam2Prog, hfpw, c_rp,
      ite_eq_left hc1, ite_eq_left hc2, Realization.memoryCost_bind',
      clientState_loadBTreeSliceCtxProg, clientResult_loadBTreeSliceCtxProg hpt,
      memoryCost_loadBTreeSliceCtxProg]
    omega
  rw [hst]
  obtain ⟨hbp_eq, hfm_eq, hm2_eq, hm0_eq, htr_eq, hout_io, hout_fast⟩ :=
    fastBTreeMod_frame hvf hb hrole hout
      (fun slot hsl _ _ =>
        by simpa only [FastEpochLayout.btL, epochBTreeLayout] using hslot slot hsl)
  exact ⟨hfr, hr.of_frame hfr hout_fast, hc_tot, hv',
    fun b' hb' role' hrole' hne => hother b' role' hb' hrole' hne,
    hbp_eq, hfm_eq, hm2_eq, hm0_eq, htr_eq, hout_io, hout_fast⟩

theorem fastBTreeUpdateProg_spec {fl : FastEpochLayout} {w b role q newVal insCount : ℕ}
    {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hb : b < numBucketsWhp fl.N) (hrole : role < 3)
    (hins : insCount ≤ 8 * slabScale fl.N ^ 12)
    (hv : ValidWhpSlice fl.N insCount (extractBTreeSlice fl.btL b role s.mem) mapFn)
    (hq : q < 2 ^ fpBitsWhp fl.N) (hval : newVal < 2 ^ valLaneBitsWhp fl.N) :
    let s' := (Memory.spec 0).clientState s
      (fastBTreeUpdateProg ((fl.pBase, (b, role)), (q, newVal)))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBTreeUpdateProg ((fl.pBase, (b, role)), (q, newVal))) s ≤
      6 * hMaxBTree + 50 ∧
    ValidWhpSlice fl.N insCount (extractBTreeSlice fl.btL b role s'.mem)
      (if (mapFn q).isSome then Function.update mapFn q (some newVal) else mapFn) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ role' < 3, (b' ≠ b ∨ role' ≠ role) →
      extractBTreeSlice fl.btL b' role' s'.mem = extractBTreeSlice fl.btL b' role' s.mem) ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  have ⟨hvf, hpt, _, _⟩ := hr
  cases hvf.w_eq
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hfvw : (Memory.spec 0).clientResult s (readParam4Prog ((fl.pBase, (9, 19)), (2, 2))) =
      ((fpBitsWhp fl.N, valLaneBitsWhp fl.N), (fl.w, fl.w)) := by
    unfold readParam4Prog readParam2Prog
    simp [hpt 9 (by decide), hpt 19 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
  have hc1 : b < numBucketsWhp fl.N ∧ role < 3 ∧ fpBitsWhp fl.N < fl.w ∧
      valLaneBitsWhp fl.N < fl.w := by
    have h8 : 8 ≤ tMinWhp fl.N := hvf.bt_valid.2.2.2.1
    have h4k : 4 * tMinWhp fl.N * (fpBitsWhp fl.N + 2) < fl.w :=
      hvf.bt_valid.2.2.2.2.2.2.2.2.2.1
    have h4v : 4 * tMinWhp fl.N * valLaneBitsWhp fl.N < fl.w :=
      hvf.bt_valid.2.2.2.2.2.2.2.2.2.2.1
    exact ⟨hb, hrole, by nlinarith, by nlinarith⟩
  have hc2 : q < (1 <<< fpBitsWhp fl.N) ∧ newVal < (1 <<< valLaneBitsWhp fl.N) := by
    simpa only [Nat.shiftLeft_eq, one_mul] using ⟨hq, hval⟩
  obtain ⟨hfr, hcost, _, hv', hother, hslot, hout⟩ :=
    btreeUpdateBoundedProg_spec (c := fl.c) (N := fl.N) (L := fl.btL)
      hvf.thresh_le rfl hvf.bt_valid hb hrole hins hv hq hval
  have hst : (Memory.spec 0).clientState s
      (fastBTreeUpdateProg ((fl.pBase, (b, role)), (q, newVal))) =
      (Memory.spec 0).clientState s
        (btreeUpdateBoundedProg (fl.btL.toSliceCtx b role, (q, newVal))) := by
    unfold fastBTreeUpdateProg; dsimp only
    have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
    have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
        numBucketsWhp fl.N := hm11
    rw [StateTransitionSpec.clientState_bind, hr11_st, hr11_r,
      StateTransitionSpec.clientState_bind, clientState_readParam4Prog, hfvw]
    dsimp only
    rw [ite_eq_left hc1, ite_eq_left hc2, StateTransitionSpec.clientState_bind,
      clientState_loadBTreeSliceCtxProg, clientResult_loadBTreeSliceCtxProg hpt]
  have hc_tot : memoryCost (fastBTreeUpdateProg ((fl.pBase, (b, role)), (q, newVal))) s ≤
      6 * hMaxBTree + 50 := by
    unfold fastBTreeUpdateProg; dsimp only
    have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
    have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
        numBucketsWhp fl.N := hm11
    have c_rq : memoryCost (readParam4Prog ((fl.pBase, (9, 19)), (2, 2))) s = 4 := by
      unfold readParam4Prog readParam2Prog; simp
    rw [Realization.memoryCost_bind', hr11_st, hr11_r, prog_memoryCost_read,
      Realization.memoryCost_bind', clientState_readParam4Prog, hfvw, c_rq]
    dsimp only
    rw [ite_eq_left hc1, ite_eq_left hc2, Realization.memoryCost_bind',
      clientState_loadBTreeSliceCtxProg, clientResult_loadBTreeSliceCtxProg hpt,
      memoryCost_loadBTreeSliceCtxProg]
    omega
  rw [hst]
  obtain ⟨hbp_eq, hfm_eq, hm2_eq, hm0_eq, htr_eq, hout_io, hout_fast⟩ :=
    fastBTreeMod_frame hvf hb hrole hout
      (fun slot hsl _ _ =>
        by simpa only [FastEpochLayout.btL, epochBTreeLayout] using hslot slot hsl)
  exact ⟨hfr, hr.of_frame hfr hout_fast, hc_tot, hv',
    fun b' hb' role' hrole' hne => hother b' role' hb' hrole' hne,
    hbp_eq, hfm_eq, hm2_eq, hm0_eq, htr_eq, hout_io, hout_fast⟩

theorem fastBufLookupProg_spec {fl : FastEpochLayout} {w role rk : ℕ}
    {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hrole : role < 2)
    (hv : ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N) (extractBufTrie (fl.trieL role) s.mem) mapFn)
    (hk : rk < 2 ^ (cTabWhp fl.c * bCharWhp fl.N)) :
    (Memory.spec 0).clientResult s (fastBufLookupProg ((fl.pBase, role), rk)) =
      (match mapFn rk with | none => (0, (0, 0)) | some (b, loc) => (1, (b, loc))) ∧
    memoryCost (fastBufLookupProg ((fl.pBase, role), rk)) s ≤ 2 * cTabWhp fl.c + 18 := by
  cases hr.1.w_eq
  unfold fastBufLookupProg; dsimp only
  rw [ite_eq_left hrole, prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_loadTrieCtxProg, clientResult_loadTrieCtxProg hr.2.1 hrole,
    memoryCost_loadTrieCtxProg]
  obtain ⟨_, hc, hres⟩ := bufLookupBoundedProg_spec (hr.1.trie_valid hrole) hv hk
  have hct : (fl.trieL role).cTab = cTabWhp fl.c := rfl
  rw [hct] at hc
  exact ⟨hres, by omega⟩

theorem fastBufDeleteProg_spec {fl : FastEpochLayout} {w role rk : ℕ}
    {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hrole : role < 2)
    (hv : ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N) (extractBufTrie (fl.trieL role) s.mem) mapFn)
    (hk : rk < 2 ^ (cTabWhp fl.c * bCharWhp fl.N)) :
    let s' := (Memory.spec 0).clientState s (fastBufDeleteProg ((fl.pBase, role), rk))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastBufDeleteProg ((fl.pBase, role), rk)) s ≤ 2 * cTabWhp fl.c + 18 ∧
    extractBufTrie (fl.trieL role) s'.mem =
      bufDelete (cTabWhp fl.c) (bCharWhp fl.N) (extractBufTrie (fl.trieL role) s.mem) rk ∧
    ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N) (extractBufTrie (fl.trieL role) s'.mem)
      (Function.update mapFn rk none) ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    s'.mem fl.metaBase = s.mem fl.metaBase ∧
    (∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r s'.mem = extractBTreeSlice fl.btL b r s.mem) ∧
    extractBufTrie (fl.trieL (1 - role)) s'.mem = extractBufTrie (fl.trieL (1 - role)) s.mem ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  obtain ⟨hfr, hr', hc, hrole_out⟩ := fastBufDeleteProg_ready (role := role) (rk := rk) hr
  obtain ⟨hext, hout⟩ := hrole_out hrole
  obtain ⟨hbp_eq, hfm_eq, hm2_eq, hm0_eq, hbt_eq, htr_o, hout_io, hout_fast⟩ :=
    fastTrieMod_frame hr.1 hrole hout
  exact ⟨hfr, hr', hc, hext, hext ▸ (hv.delete_spec hk).1,
    hbp_eq, hfm_eq, hm2_eq, hm0_eq, hbt_eq, htr_o, hout_io, hout_fast⟩

theorem fastBufInsertProg_spec {fl : FastEpochLayout} {w role rk b loc : ℕ}
    {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hrole : role < 2)
    (hv : ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N) (extractBufTrie (fl.trieL role) s.mem) mapFn)
    (hraw : RawBufTrieBounds (extractBufTrie (fl.trieL role) s.mem))
    (hna : (extractBufTrie (fl.trieL role) s.mem).nodeAlloc + cTabWhp fl.c ≤
      maxTrieNodesWhp fl.c fl.N)
    (hia : (extractBufTrie (fl.trieL role) s.mem).itemAlloc < qEpochWhp fl.N)
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
    bufInsertBoundedProg_spec (hr.1.trie_valid hrole) hv hraw hna hia hk hb hloc
  have hct : (fl.trieL role).cTab = cTabWhp fl.c := rfl
  have hbc : (fl.trieL role).bChar = bCharWhp fl.N := rfl
  rw [hct, hbc] at hext hv'
  rw [← hst] at hext hv' hout
  obtain ⟨hbp_eq, hfm_eq, hm2_eq, hm0_eq, hbt_eq, htr_o, hout_io, hout_fast⟩ :=
    fastTrieMod_frame hr.1 hrole hout
  exact ⟨hfr, hr', hc, hext, hv', hbp_eq, hfm_eq, hm2_eq, hm0_eq, hbt_eq, htr_o,
    hout_io, hout_fast⟩

/-- Pre-advance 3-tier invariant (`curTr.itemAlloc ≤ fm.subStep + slackCur`), unifying
`FastEpochInv` (`slackCur = 0`) and the intermediate state immediately before `advanceSubEpochProg`
after a single `BufCur` insertion (`slackCur = 1`). -/
structure FastEpochInvGen (slackCur : ℕ) (fl : FastEpochLayout) (slack : ℕ)
    (seeds : EpochHashSeeds fl.c fl.U fl.N) (mem : ℕ → ℕ)
    (s_abs : Fin fl.U → Option (Fin fl.V)) : Prop where
  param_table : fl.ParamTable mem
  hdr_N : mem fl.metaBase = fl.N
  mode_zero : mem (fl.metaBase + 2) = 0
  seed_bkt : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
    (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt mem
  seed_fp : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
    (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp mem
  bp_inv : fl.bpL.StateInv slack mem
  bkt_le_capMax : ∀ b < numBucketsWhp fl.N,
    (extractBlockPool fl.mp mem).bktCount b ≤ capMaxWhp fl.N
  refines : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt)
    (extractBlockPool fl.mp mem).nSide
    (fun p => ((extractBlockPool fl.mp mem).ownerOf p).1)
    (slotIoPairAt fl.io mem) s_abs
  role_lt : (extractFastMeta fl mem).curBufRole < 2
  subStep_lt : (extractFastMeta fl mem).subStep < qEpochWhp fl.N
  bkt_meta_bounds : ∀ b < numBucketsWhp fl.N,
    let fm := extractFastMeta fl mem
    fm.bktSalt b < sMaxWhp fl.c fl.N ∧
    fm.curRole b < 3 ∧
    fm.curIns b ≤ 8 * slabScale fl.N ^ 12 ∧
    (fm.shadowCode b = 0 → ¬(fm.tryAct = 1 ∧ fm.tryBkt = b) →
      fm.curIns b < 6 * slabScale fl.N ^ 12)
  tiers :
    let fm := extractFastMeta fl mem
    let bp := extractBlockPool fl.mp mem
    let Q := qEpochWhp fl.N
    let curTr := extractBufTrie (fl.trieL fm.curBufRole) mem
    let oldTr := extractBufTrie (fl.trieL (1 - fm.curBufRole)) mem
    ∃ (mapCur : ℕ → Option (ℕ × ℕ)) (mapOld : ℕ → Option (ℕ × ℕ))
      (mapBTree : ℕ → ℕ → Option ℕ),
      ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N) curTr mapCur ∧
      RawBufTrieBounds curTr ∧
      RawClearableBounds curTr ∧
      curTr.itemAlloc ≤ fm.subStep + slackCur ∧
      curTr.nodeAlloc ≤ 1 + cTabWhp fl.c * curTr.itemAlloc ∧
      (∀ rk b loc, mapCur rk = some (b, loc) →
        b < numBucketsWhp fl.N ∧ loc < bp.bktCount b ∧
        ∃ u : Fin fl.U, rKeyOf fl.c fl.U fl.N seeds.fp u = rk ∧
          fastKeyAt fl seeds.bkt mem b loc = u.val) ∧
      (if fm.subStep < Q / 2 then
        ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N) oldTr mapOld ∧
        RawBufTrieBounds oldTr ∧
        RawClearableBounds oldTr ∧
        oldTr.itemAlloc ≤ Q ∧
        oldTr.nodeAlloc ≤ 1 + cTabWhp fl.c * Q ∧
        fm.drainPos ≤ Q ∧
        (∀ id < min fm.drainPos oldTr.itemAlloc, bufCheckSlot oldTr id = none) ∧
        (∀ rk b loc, mapOld rk = some (b, loc) →
          mapCur rk = none ∧
          b < numBucketsWhp fl.N ∧ loc < bp.bktCount b ∧
          ∃ u : Fin fl.U, rKeyOf fl.c fl.U fl.N seeds.fp u = rk ∧
            fastKeyAt fl seeds.bkt mem b loc = u.val)
      else
        mapOld = (fun _ => none) ∧
        fm.tryAct = 0 ∧
        ClearableBufTrie oldTr ∧
        RawClearableBounds oldTr ∧
        oldTr.nodeAlloc ≤ max 1 ((1 + cTabWhp fl.c * Q) -
          4 * (cTabWhp fl.c + 2) * (fm.subStep - Q / 2))) ∧
      (∀ (b : ℕ) (hb : b < numBucketsWhp fl.N),
        ValidWhpSlice fl.N (fm.curIns b)
          (extractBTreeSlice fl.btL b (fm.curRole b) mem) (mapBTree b) ∧
        (∀ fp loc, mapBTree b fp = some loc →
          loc < bp.bktCount b ∧
          ∃ u : Fin fl.U,
            (fpHash fl.c fl.U fl.N seeds.fp
              ⟨fm.bktSalt b, (bkt_meta_bounds b hb).1⟩ u).val = fp ∧
            fastKeyAt fl seeds.bkt mem b loc = u.val ∧
            (∀ b₁ loc₁, mapCur (rKeyOf fl.c fl.U fl.N seeds.fp u) = some (b₁, loc₁) →
              fastKeyAt fl seeds.bkt mem b₁ loc₁ ≠ u.val) ∧
            (∀ b₂ loc₂, mapOld (rKeyOf fl.c fl.U fl.N seeds.fp u) = some (b₂, loc₂) →
              fastKeyAt fl seeds.bkt mem b₂ loc₂ ≠ u.val))) ∧
      (∀ (b : ℕ) (hb : b < numBucketsWhp fl.N), ∀ loc < bp.bktCount b,
        ∃ u : Fin fl.U,
          fastKeyAt fl seeds.bkt mem b loc = u.val ∧
          (mapCur (rKeyOf fl.c fl.U fl.N seeds.fp u) = some (b, loc) ∨
            mapOld (rKeyOf fl.c fl.U fl.N seeds.fp u) = some (b, loc) ∨
            mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
              ⟨fm.bktSalt b, (bkt_meta_bounds b hb).1⟩ u).val = some loc)) ∧
      (∀ b < numBucketsWhp fl.N, fm.shadowCode b ≠ 0 →
        let shPos := fm.shadowCode b - 1
        let cnt := bp.bktCount b
        shPos < cnt ∧
        !(fm.tryAct = 1 ∧ fm.tryBkt = b) ∧
        4 * fm.shadowIns b + 5 * (cnt - shPos) ≤ 20 * slabScale fl.N ^ 12 ∧
        8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - shPos) ≤ 4 * slabScale fl.N ^ 12 ∧
        ∃ shMap : ℕ → Option ℕ,
          ValidWhpSlice fl.N (fm.shadowIns b)
            (extractBTreeSlice fl.btL b (shadowRoleOf (fm.curRole b)) mem) shMap ∧
          (∀ fp, shMap fp =
            match mapBTree b fp with
            | some loc => if loc < shPos then some loc else none
            | none => none)) ∧
      fm.tryAct ≤ 1 ∧
      (fm.tryAct = 1 →
        let b := fm.tryBkt
        fm.subStep < Q / 2 ∧
        ∃ (hb_try : b < numBucketsWhp fl.N) (hs_try : fm.trySalt < sMaxWhp fl.c fl.N),
          fm.tryPos ≤ bp.bktCount b ∧
          fm.shadowCode b = 0 ∧
          4 * fm.tryIns + 5 * (bp.bktCount b - fm.tryPos) ≤ 20 * slabScale fl.N ^ 12 ∧
          ∃ tryMap : ℕ → Option ℕ,
            ValidWhpSlice fl.N fm.tryIns
              (extractBTreeSlice fl.btL b (tryRoleOf (fm.curRole b)) mem) tryMap ∧
            (∀ fp loc, tryMap fp = some loc →
              loc < fm.tryPos ∧
              ∃ u : Fin fl.U,
                fastKeyAt fl seeds.bkt mem b loc = u.val ∧
                mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
                  ⟨fm.bktSalt b, (bkt_meta_bounds b hb_try).1⟩ u).val = some loc ∧
                (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_try⟩ u).val = fp) ∧
            (∀ loc < fm.tryPos, ∀ u : Fin fl.U,
              fastKeyAt fl seeds.bkt mem b loc = u.val →
              mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
                ⟨fm.bktSalt b, (bkt_meta_bounds b hb_try).1⟩ u).val = some loc →
              tryMap (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_try⟩ u).val = some loc))

theorem FastEpochInv.toGen {fl : FastEpochLayout} {slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)} (slackCur : ℕ)
    (h : FastEpochInv fl slack seeds mem s_abs) :
    FastEpochInvGen slackCur fl slack seeds mem s_abs where
  param_table := h.param_table
  hdr_N := h.hdr_N
  mode_zero := h.mode_zero
  seed_bkt := h.seed_bkt
  seed_fp := h.seed_fp
  bp_inv := h.bp_inv
  bkt_le_capMax := h.bkt_le_capMax
  refines := h.refines
  role_lt := h.role_lt
  subStep_lt := h.subStep_lt
  bkt_meta_bounds := h.bkt_meta_bounds
  tiers := by
    obtain ⟨mc, mo, mb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h.tiers
    exact ⟨mc, mo, mb, h1, h2, h3, h4.trans (Nat.le_add_right _ _), h5, h6, h7, h8, h9, h10,
      h11, h12⟩

theorem FastEpochInvGen.toInv {fl : FastEpochLayout} {slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (h : FastEpochInvGen 0 fl slack seeds mem s_abs) :
    FastEpochInv fl slack seeds mem s_abs where
  param_table := h.param_table
  hdr_N := h.hdr_N
  mode_zero := h.mode_zero
  seed_bkt := h.seed_bkt
  seed_fp := h.seed_fp
  bp_inv := h.bp_inv
  bkt_le_capMax := h.bkt_le_capMax
  refines := h.refines
  role_lt := h.role_lt
  subStep_lt := h.subStep_lt
  bkt_meta_bounds := h.bkt_meta_bounds
  tiers := by
    obtain ⟨mc, mo, mb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h.tiers
    exact ⟨mc, mo, mb, h1, h2, h3, by omega, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem FastEpochInvGen.ready {slackCur : ℕ} {fl : FastEpochLayout} {w fr _slack : ℕ}
    {_seeds : EpochHashSeeds fl.c fl.U fl.N} {s : Memory.State}
    {_s_abs : Fin fl.U → Option (Fin fl.V)}
    (hv : fl.Valid w fr) (hfr : fr = s.frontier)
    (hinv : FastEpochInvGen slackCur fl _slack _seeds s.mem _s_abs) :
    FastLayoutReady w fl s :=
  ⟨hfr ▸ hv, hinv.param_table, hinv.seed_bkt.1 ▸ _seeds.bkt.1.isLt,
    hinv.seed_fp.1 ▸ _seeds.fp.1.isLt⟩

theorem FastEpochInvGen.bktSlot_refines {slackCur : ℕ} {fl : FastEpochLayout} {slack b loc : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hinv : FastEpochInvGen slackCur fl slack seeds mem s_abs)
    (hb : b < numBucketsWhp fl.N) (hloc : loc < (extractBlockPool fl.mp mem).bktCount b) :
    let qv := bpPairAt fl.bpL mem b loc
    let u_val := fastKeyAt fl seeds.bkt mem b loc
    ∃ (u : Fin fl.U) (v : Fin fl.V),
      u.val = u_val ∧ v.val = qv.2 ∧
      epochBucket fl.c fl.U fl.N seeds.bkt u = b ∧
      keyQuotient (bWhp fl.N) u.val = qv.1 ∧
      s_abs u = some v := by
  dsimp only
  have hcv : (extractBlockPool fl.mp mem).CoreValid := hinv.bp_inv.1.core
  set p := (extractBlockPool fl.mp mem).toPhys b loc
  have hp_lt : p < (extractBlockPool fl.mp mem).nSide := hcv.toPhys_lt hb hloc
  have how_p : ((extractBlockPool fl.mp mem).ownerOf p).1 = b := by
    rw [hcv.ownerOf_toPhys hb hloc]
  obtain ⟨hu_lt, hv_lt, hbkt_u, hkq_u, hs_u⟩ := hinv.refines.slot_key_val hp_lt
  have hfn : ∀ (ow : ℕ),
      (∃ (hu : feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt) ow
            (slotIoPairAt fl.io mem p).1 < fl.U)
          (hv : (slotIoPairAt fl.io mem p).2 < fl.V),
        feistelBucket (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt)
          (feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt) ow
            (slotIoPairAt fl.io mem p).1) = ow ∧
        keyQuotient (bWhp fl.N)
          (feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt) ow
            (slotIoPairAt fl.io mem p).1) = (slotIoPairAt fl.io mem p).1 ∧
        s_abs ⟨_, hu⟩ = some ⟨_, hv⟩) →
      ow = b →
      ∃ (u : Fin fl.U) (v : Fin fl.V),
        u.val = fastKeyAt fl seeds.bkt mem b loc ∧ v.val = (bpPairAt fl.bpL mem b loc).2 ∧
        epochBucket fl.c fl.U fl.N seeds.bkt u = b ∧
        keyQuotient (bWhp fl.N) u.val = (bpPairAt fl.bpL mem b loc).1 ∧
        s_abs u = some v := by
    rintro _ ⟨hu, hv, h1, h2, h3⟩ rfl
    exact ⟨⟨_, hu⟩, ⟨_, hv⟩, rfl, rfl, h1, h2, h3⟩
  exact hfn _ ⟨hu_lt, hv_lt, hbkt_u, hkq_u, hs_u⟩ how_p

/-! ### `fastShadowStepProg` and `fastShadowSteps8Prog` -/

/-- Pure `O(1)` computation of `shadowRoleOf r` (`(r + 1) % 3`) as a zero-query `Memory.Prog`. -/
def shadowRoleProg (r : ℕ) : Memory.Prog ℕ :=
  if r = 0 then pure 1 else if r = 1 then pure 2 else pure 0

@[simp] theorem runClient_state_shadowRoleProg (r : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (shadowRoleProg r)) = s := by
  unfold shadowRoleProg; split_ifs <;> rfl

theorem clientState_shadowRoleProg (r : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (shadowRoleProg r) = s :=
  runClient_state_shadowRoleProg r s

@[simp] theorem clientResult_shadowRoleProg (r : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (shadowRoleProg r) = shadowRoleOf r := by
  unfold shadowRoleProg shadowRoleOf; split_ifs <;> simp

@[simp] theorem memoryCost_shadowRoleProg (r : ℕ) (s : Memory.State) :
    memoryCost (shadowRoleProg r) s = 0 := by
  unfold shadowRoleProg; split_ifs <;> simp

theorem realizesBounded_shadowRole :
    RealizesBounded .exact shadowRoleProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w _ _ => 6 ≤ w) (fun _ _ => 0) := by
  realize
  all_goals (
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) h
    dsimp only [Fits] at *; omega)

/-- Pure `O(1)` computation of `tryRoleOf r` (`(r + 2) % 3`) as a zero-query `Memory.Prog`. -/
def tryRoleProg (r : ℕ) : Memory.Prog ℕ :=
  if r = 0 then pure 2 else if r = 1 then pure 0 else pure 1

@[simp] theorem runClient_state_tryRoleProg (r : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (tryRoleProg r)) = s := by
  unfold tryRoleProg; split_ifs <;> rfl

theorem clientState_tryRoleProg (r : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (tryRoleProg r) = s :=
  runClient_state_tryRoleProg r s

@[simp] theorem clientResult_tryRoleProg (r : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (tryRoleProg r) = tryRoleOf r := by
  unfold tryRoleProg tryRoleOf; split_ifs <;> simp

@[simp] theorem memoryCost_tryRoleProg (r : ℕ) (s : Memory.State) :
    memoryCost (tryRoleProg r) s = 0 := by
  unfold tryRoleProg; split_ifs <;> simp

theorem realizesBounded_tryRole :
    RealizesBounded .exact tryRoleProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w _ _ => 6 ≤ w) (fun _ _ => 0) := by
  realize
  all_goals (
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) h
    dsimp only [Fits] at *; omega)

/-- Commit `shadowRoleOf cRole` as the new `curRole b` (`curIns := shIns`, `shadowIns := 0`,
`shadowCode := 0`). -/
def fastCommitShadowProg : ℕ × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (pBase, (b, (shRole, shIns))) => do
    fastWriteBktLaneProg ((pBase, (b, 12)), shRole)
    fastWriteBktLaneProg ((pBase, (b, 13)), shIns)
    fastWriteBktLaneProg ((pBase, (b, 14)), 0)
    fastWriteBktLaneProg ((pBase, (b, 15)), 0)

theorem fastCommitShadowProg_ready {w : ℕ} {fl : FastEpochLayout} {b shRole shIns : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastCommitShadowProg (fl.pBase, (b, (shRole, shIns))))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastCommitShadowProg (fl.pBase, (b, (shRole, shIns)))) s ≤ 40 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ b' < numBucketsWhp fl.N, ∀ role < 3,
      extractBTreeSlice fl.btL b' role s'.mem = extractBTreeSlice fl.btL b' role s.mem) ∧
    (∀ role < 2, extractBufTrie (fl.trieL role) s'.mem = extractBufTrie (fl.trieL role) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  unfold fastCommitShadowProg
  set s1 := (Memory.spec 0).clientState s (fastWriteBktLaneProg ((fl.pBase, (b, 12)), shRole))
  set s2 := (Memory.spec 0).clientState s1 (fastWriteBktLaneProg ((fl.pBase, (b, 13)), shIns))
  set s3 := (Memory.spec 0).clientState s2 (fastWriteBktLaneProg ((fl.pBase, (b, 14)), 0))
  set s4 := (Memory.spec 0).clientState s3 (fastWriteBktLaneProg ((fl.pBase, (b, 15)), 0))
  obtain ⟨hfr1, hr1, hbp1, hbt1, htr1, hof1, hoi1⟩ :=
    fastWriteBktLaneProg_frame (b := b) (lane := 12) (val := shRole) hr
  obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hof2, hoi2⟩ :=
    fastWriteBktLaneProg_frame (b := b) (lane := 13) (val := shIns) hr1
  obtain ⟨hfr3, hr3, hbp3, hbt3, htr3, hof3, hoi3⟩ :=
    fastWriteBktLaneProg_frame (b := b) (lane := 14) (val := 0) hr2
  obtain ⟨hfr4, hr4, hbp4, hbt4, htr4, hof4, hoi4⟩ :=
    fastWriteBktLaneProg_frame (b := b) (lane := 15) (val := 0) hr3
  have hc1 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 12)), shRole) s
  have hc2 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 13)), shIns) s1
  have hc3 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 14)), 0) s2
  have hc4 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 15)), 0) s3
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    Realization.memoryCost_bind', Realization.memoryCost_bind']
  change s4.frontier = s.frontier ∧ FastLayoutReady w fl s4 ∧
    memoryCost (fastWriteBktLaneProg ((fl.pBase, (b, 12)), shRole)) s +
      (memoryCost (fastWriteBktLaneProg ((fl.pBase, (b, 13)), shIns)) s1 +
        (memoryCost (fastWriteBktLaneProg ((fl.pBase, (b, 14)), 0)) s2 +
          memoryCost (fastWriteBktLaneProg ((fl.pBase, (b, 15)), 0)) s3)) ≤ 40 ∧ _
  exact ⟨hfr4.trans (hfr3.trans (hfr2.trans hfr1)), hr4, by omega,
    hbp4.trans (hbp3.trans (hbp2.trans hbp1)),
    fun b' hb' r hr_lt => (hbt4 b' hb' r hr_lt).trans
      ((hbt3 b' hb' r hr_lt).trans ((hbt2 b' hb' r hr_lt).trans (hbt1 b' hb' r hr_lt))),
    fun r hr_lt => (htr4 r hr_lt).trans
      ((htr3 r hr_lt).trans ((htr2 r hr_lt).trans (htr1 r hr_lt))),
    fun a ha => (hoi4 a ha).trans ((hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha))),
    fun a ha => (hof4 a ha).trans ((hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha)))⟩

theorem fastCommitShadowProg_pre {w : ℕ} {x : ℕ × (ℕ × (ℕ × ℕ))} {s : Memory.State}
    (h : FastProgPre w x.1 s) :
    FastProgPre w x.1 ((Memory.spec 0).clientState s (fastCommitShadowProg x)) := by
  rcases x with ⟨pBase, ⟨b, ⟨shRole, shIns⟩⟩⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastCommitShadowProg_ready hr).2.1⟩

theorem realizesBounded_fastCommitShadow :
    RealizesBounded .exact fastCommitShadowProg
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hw := realizesBounded_fastWriteBktLane
  realize
  all_goals (
    rcases d with ⟨pBase, ⟨b, ⟨shRole, shIns⟩⟩⟩
    have ⟨hw6, hp⟩ := FastProgPre.pBase_bound h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    have hp1 : FastProgPre w pBase
        ((Memory.spec 0).runClient s (fastWriteBktLaneProg ((pBase, (b, 12)), shRole))).2.1 :=
      fastWriteBktLaneProg_pre (x := ((pBase, (b, 12)), shRole)) h
    have hp2 : FastProgPre w pBase
        ((Memory.spec 0).runClient
          ((Memory.spec 0).runClient s (fastWriteBktLaneProg ((pBase, (b, 12)), shRole))).2.1
          (fastWriteBktLaneProg ((pBase, (b, 13)), shIns))).2.1 :=
      fastWriteBktLaneProg_pre (x := ((pBase, (b, 13)), shIns)) hp1
    have hp3 : FastProgPre w pBase
        ((Memory.spec 0).runClient
          ((Memory.spec 0).runClient
            ((Memory.spec 0).runClient s (fastWriteBktLaneProg ((pBase, (b, 12)), shRole))).2.1
            (fastWriteBktLaneProg ((pBase, (b, 13)), shIns))).2.1
          (fastWriteBktLaneProg ((pBase, (b, 14)), 0))).2.1 :=
      fastWriteBktLaneProg_pre (x := ((pBase, (b, 14)), 0)) hp2
    first | exact h | exact hp1 | exact hp2 | exact hp3 | omega)

private def fastShadowAdvanceProg : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | ((pBase, b), ((shPos, cnt), (shRole, shIns'))) => do
    let nCap ← Memory.read (pBase + 0)
    if cnt ≤ nCap then
      if shPos < cnt then
        if shPos + 1 < cnt then do
          fastWriteBktLaneProg ((pBase, (b, 14)), shIns')
          fastWriteBktLaneProg ((pBase, (b, 15)), shPos + 2)
        else
          fastCommitShadowProg (pBase, (b, (shRole, shIns')))
      else
        fastCommitShadowProg (pBase, (b, (shRole, shIns')))
    else
      fastCommitShadowProg (pBase, (b, (shRole, shIns')))

private theorem fastShadowAdvanceProg_ready {w : ℕ} {fl : FastEpochLayout}
    {b shPos cnt shRole shIns' : ℕ} {s : Memory.State} (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s
      (fastShadowAdvanceProg ((fl.pBase, b), ((shPos, cnt), (shRole, shIns'))))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (fastShadowAdvanceProg ((fl.pBase, b), ((shPos, cnt), (shRole, shIns')))) s ≤ 42 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ b' < numBucketsWhp fl.N, ∀ role < 3,
      extractBTreeSlice fl.btL b' role s'.mem = extractBTreeSlice fl.btL b' role s.mem) ∧
    (∀ role < 2, extractBufTrie (fl.trieL role) s'.mem = extractBufTrie (fl.trieL role) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  unfold fastShadowAdvanceProg; dsimp only
  have hm0 : s.mem (fl.pBase + 0) = fl.N := hr.2.1 0 (by decide)
  have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
  have hr0_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N := hm0
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hr0_st, hr0_r,
    prog_memoryCost_read]
  obtain ⟨hfr_cm, hr_cm, hcost_cm, hbp_cm, hbt_cm, htr_cm, hoi_cm, hof_cm⟩ :=
    fastCommitShadowProg_ready (b := b) (shRole := shRole) (shIns := shIns') hr
  by_cases hc1 : cnt ≤ fl.N
  · rw [ite_eq_left hc1]
    by_cases hc2 : shPos < cnt
    · rw [ite_eq_left hc2]
      by_cases hc3 : shPos + 1 < cnt
      · rw [ite_eq_left hc3]
        set s1 := (Memory.spec 0).clientState s (fastWriteBktLaneProg ((fl.pBase, (b, 14)), shIns'))
        set s2 := (Memory.spec 0).clientState s1
          (fastWriteBktLaneProg ((fl.pBase, (b, 15)), shPos + 2))
        obtain ⟨hfr1, hr1, hbp1, hbt1, htr1, hof1, hoi1⟩ :=
          fastWriteBktLaneProg_frame (b := b) (lane := 14) (val := shIns') hr
        obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hof2, hoi2⟩ :=
          fastWriteBktLaneProg_frame (b := b) (lane := 15) (val := shPos + 2) hr1
        have c1 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 14)), shIns') s
        have c2 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 15)), shPos + 2) s1
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
        refine ⟨hfr2.trans hfr1, hr2, ?_, hbp2.trans hbp1,
          fun b' hb' r hr_lt => (hbt2 b' hb' r hr_lt).trans (hbt1 b' hb' r hr_lt),
          fun r hr_lt => (htr2 r hr_lt).trans (htr1 r hr_lt),
          fun a ha => (hoi2 a ha).trans (hoi1 a ha),
          fun a ha => (hof2 a ha).trans (hof1 a ha)⟩
        change 1 + (memoryCost (fastWriteBktLaneProg ((fl.pBase, (b, 14)), shIns')) s +
          memoryCost (fastWriteBktLaneProg ((fl.pBase, (b, 15)), shPos + 2)) s1) ≤ 42
        omega
      · rw [ite_eq_right hc3]
        exact ⟨hfr_cm, hr_cm, by omega, hbp_cm, hbt_cm, htr_cm, hoi_cm, hof_cm⟩
    · rw [ite_eq_right hc2]
      exact ⟨hfr_cm, hr_cm, by omega, hbp_cm, hbt_cm, htr_cm, hoi_cm, hof_cm⟩
  · rw [ite_eq_right hc1]
    exact ⟨hfr_cm, hr_cm, by omega, hbp_cm, hbt_cm, htr_cm, hoi_cm, hof_cm⟩

private theorem realizesBounded_fastShadowAdvance :
    RealizesBounded .exact fastShadowAdvanceProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hw := realizesBounded_fastWriteBktLane
  have hc := realizesBounded_fastCommitShadow
  realize
  all_goals (
    rcases d with ⟨⟨pBase, b⟩, ⟨⟨shPos, cnt⟩, ⟨shRole, shIns'⟩⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm0' : s.mem (fl.pBase + 0) = fl.N := hr.2.1 0 (by decide)
    have hm0 : s.mem fl.pBase = fl.N := by rwa [Nat.add_zero] at hm0'
    have hr0_rc : ((Memory.spec 0).runClient s (Memory.read (fl.pBase + 0))).1 = fl.N := hm0'
    have hr0_rc0 : ((Memory.spec 0).runClient s (Memory.read fl.pBase)).1 = fl.N := hm0
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    dsimp only at *
    try simp only [hr0_rc, hr0_rc0, hm0', hm0] at *
    have hp1 : FastProgPre w fl.pBase
        ((Memory.spec 0).runClient s (fastWriteBktLaneProg ((fl.pBase, (b, 14)), shIns'))).2.1 :=
      fastWriteBktLaneProg_pre (x := ((fl.pBase, (b, 14)), shIns')) ⟨fl, rfl, hr⟩
    first
    | exact ⟨fl, rfl, hr⟩
    | exact hp1
    | omega)

private def fastShadowBodyTailProg : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((pBase, b), (shPos, cnt)), fp) => do
    let nCap ← Memory.read (pBase + 0)
    let cRole ← fastReadBktLaneProg (pBase, (b, 12))
    let lk ← fastBTreeLookupProg ((pBase, (b, cRole)), fp)
    let shRole ← shadowRoleProg cRole
    let shIns ← fastReadBktLaneProg (pBase, (b, 14))
    if lk.1 = 1 ∧ lk.2 = shPos ∧ shIns < nCap then do
      fastBTreeInsertProg ((pBase, (b, shRole)), (fp, shPos))
      fastShadowAdvanceProg ((pBase, b), ((shPos, cnt), (shRole, shIns + 1)))
    else
      fastShadowAdvanceProg ((pBase, b), ((shPos, cnt), (shRole, shIns)))

private theorem fastShadowBodyTailProg_ready {w : ℕ} {fl : FastEpochLayout}
    {b shPos cnt fp : ℕ} {s : Memory.State} (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s
      (fastShadowBodyTailProg (((fl.pBase, b), (shPos, cnt)), fp))
    s'.frontier = s.frontier ∧ FastLayoutReady w fl s' := by
  dsimp only
  unfold fastShadowBodyTailProg; dsimp only
  have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
  rw [StateTransitionSpec.clientState_bind, hr0_st,
    StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
    StateTransitionSpec.clientState_bind, clientState_fastBTreeLookupProg,
    StateTransitionSpec.clientState_bind, clientState_shadowRoleProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind]
    obtain ⟨hfr1, hr1, _⟩ := fastBTreeInsertProg_ready hr
    obtain ⟨hfr2, hr2, _⟩ := fastShadowAdvanceProg_ready hr1
    exact ⟨hfr2.trans hfr1, hr2⟩
  · obtain ⟨hfr, hr', _⟩ := fastShadowAdvanceProg_ready hr
    exact ⟨hfr, hr'⟩

private theorem realizesBounded_fastShadowBodyTail :
    RealizesBounded .exact fastShadowBodyTailProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((pBase, _), _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have hlk := realizesBounded_fastBTreeLookup
  have hsr := realizesBounded_shadowRole
  have hbi := realizesBounded_fastBTreeInsert
  have had := realizesBounded_fastShadowAdvance
  realize
  all_goals (
    rcases d with ⟨⟨⟨pBase, b⟩, ⟨shPos, cnt⟩⟩, fp⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm0' : s.mem (fl.pBase + 0) = fl.N := hr.2.1 0 (by decide)
    have hm0 : s.mem fl.pBase = fl.N := by rwa [Nat.add_zero] at hm0'
    have hr0_rc : ((Memory.spec 0).runClient s (Memory.read (fl.pBase + 0))).1 = fl.N := hm0'
    have hr0_rc0 : ((Memory.spec 0).runClient s (Memory.read fl.pBase)).1 = fl.N := hm0
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, hr0_rc, hr0_rc0, hm0', hm0,
      runClient_state_fastReadBktLaneProg, runClient_state_fastBTreeLookupProg,
      runClient_state_shadowRoleProg] at *
    first
    | exact hw6
    | exact ⟨fl, rfl, hr⟩
    | exact fastBTreeInsertProg_pre (x := ((fl.pBase, (b,
        ((Memory.spec 0).runClient s
          (shadowRoleProg ((Memory.spec 0).runClient s
            (fastReadBktLaneProg (fl.pBase, (b, 12)))).1)).1)), (fp, shPos))) ⟨fl, rfl, hr⟩
    | omega)

private def fastShadowBodyProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, b), (shPos, cnt)) => do
    let nCap ← Memory.read (pBase + 0)
    if shPos < cnt ∧ cnt ≤ nCap then do
      let qv ← fastBpReadAtProg (pBase, (b, shPos))
      let u_val ← fastFeistelReconProg (pBase, (b, qv.1))
      let salt ← fastReadBktLaneProg (pBase, (b, 5))
      let fp ← fastFpHashProg (pBase, (salt, u_val))
      fastShadowBodyTailProg (((pBase, b), (shPos, cnt)), fp)
    else
      pure ()

private theorem fastShadowBodyProg_ready {w : ℕ} {fl : FastEpochLayout}
    {b shPos cnt : ℕ} {s : Memory.State} (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastShadowBodyProg ((fl.pBase, b), (shPos, cnt)))
    s'.frontier = s.frontier ∧ FastLayoutReady w fl s' := by
  dsimp only
  unfold fastShadowBodyProg; dsimp only
  have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
  rw [StateTransitionSpec.clientState_bind, hr0_st]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg,
      StateTransitionSpec.clientState_bind, clientState_fastFeistelReconProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastFpHashProg]
    exact fastShadowBodyTailProg_ready hr
  · exact ⟨rfl, hr⟩

private theorem realizesBounded_fastShadowBody :
    RealizesBounded .exact fastShadowBodyProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hra := realizesBounded_fastBpReadAt
  have hrc := realizesBounded_fastFeistelRecon
  have hrl := realizesBounded_fastReadBktLane
  have hfp := realizesBounded_fastFpHash
  have htl := realizesBounded_fastShadowBodyTail
  realize
  all_goals (
    rcases d with ⟨⟨pBase, b⟩, ⟨shPos, cnt⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastBpReadAtProg,
      runClient_state_fastFeistelReconProg, runClient_state_fastReadBktLaneProg,
      runClient_state_fastFpHashProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-- Perform one deamortized shadow-compaction step on bucket `b` (`¬ReadsWidth`). -/
def fastShadowStepProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, b) => do
    let M ← Memory.read (pBase + 11)
    let sc ← fastReadBktLaneProg (pBase, (b, 15))
    if b < M ∧ sc ≠ 0 then do
      let cnt ← fastReadBktCntProg (pBase, b)
      fastShadowBodyProg ((pBase, b), (sc - 1, cnt))
    else
      pure ()

theorem fastShadowStepProg_ready {w : ℕ} {fl : FastEpochLayout} {b : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastShadowStepProg (fl.pBase, b))
    s'.frontier = s.frontier ∧ FastLayoutReady w fl s' := by
  dsimp only
  unfold fastShadowStepProg; dsimp only
  have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
  rw [StateTransitionSpec.clientState_bind, hr11_st,
    StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg]
    exact fastShadowBodyProg_ready hr
  · exact ⟨rfl, hr⟩

theorem fastShadowStepProg_pre {w : ℕ} {x : ℕ × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1 s) :
    FastProgPre w x.1 ((Memory.spec 0).clientState s (fastShadowStepProg x)) := by
  rcases x with ⟨pBase, b⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (fastShadowStepProg_ready hr).2⟩

theorem realizesBounded_fastShadowStep :
    RealizesBounded .exact fastShadowStepProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have hbc := realizesBounded_fastReadBktCnt
  have hbd := realizesBounded_fastShadowBody
  realize
  all_goals (
    rcases d with ⟨pBase, b⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktLaneProg,
      runClient_state_fastReadBktCntProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

theorem fastShadowStepProg_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack b k : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hslack_in : b < numBucketsWhp fl.N → (extractFastMeta fl s.mem).shadowCode b ≠ 0 →
      let fm := extractFastMeta fl s.mem
      let cnt := (extractBlockPool fl.mp s.mem).bktCount b
      4 * fm.shadowIns b + 5 * (cnt - (fm.shadowCode b - 1)) + k ≤ 20 * slabScale fl.N ^ 12 ∧
      8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm.shadowCode b - 1)) + k ≤
        4 * slabScale fl.N ^ 12) :
    let s' := (Memory.spec 0).clientState s (fastShadowStepProg (fl.pBase, b))
    let fm := extractFastMeta fl s.mem
    let fm' := extractFastMeta fl s'.mem
    s'.frontier = s.frontier ∧
    memoryCost (fastShadowStepProg (fl.pBase, b)) s ≤
      360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    fm'.drainPos = fm.drainPos ∧
    fm'.tryAct = fm.tryAct ∧
    fm'.tryBkt = fm.tryBkt ∧
    fm'.trySalt = fm.trySalt ∧
    fm'.tryPos = fm.tryPos ∧
    fm'.tryIns = fm.tryIns ∧
    fm'.bktSalt = fm.bktSalt ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ b' ≠ b, fm'.curRole b' = fm.curRole b' ∧ fm'.curIns b' = fm.curIns b' ∧
      fm'.shadowIns b' = fm.shadowIns b' ∧ fm'.shadowCode b' = fm.shadowCode b') ∧
    (b < numBucketsWhp fl.N → fm'.shadowCode b ≠ 0 →
      let cnt := (extractBlockPool fl.mp s.mem).bktCount b
      4 * fm'.shadowIns b + 5 * (cnt - (fm'.shadowCode b - 1)) + (k + 1) ≤
        20 * slabScale fl.N ^ 12 ∧
      8 * (fm'.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm'.shadowCode b - 1)) + (k + 1) ≤
        4 * slabScale fl.N ^ 12) := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  have hpt := hinv.param_table
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  obtain ⟨h64_L12, hcap_N, _, _⟩ := hv.bounds_le_N
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hm0 : s.mem (fl.pBase + 0) = fl.N := hpt 0 (by decide)
  generalize hsc_res_def :
    (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 15))) = sc_res
  by_cases hguard : b < numBucketsWhp fl.N ∧ sc_res ≠ 0
  · obtain ⟨hb, hsc_res_nz⟩ := hguard
    have hsc_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 15))) =
        fm.shadowCode b := by
      rw [clientResult_fastReadBktLaneProg hpt hb (by decide)]
      unfold fm extractFastMeta; dsimp only; rw [ite_eq_left hb]
    have hsc_nz : fm.shadowCode b ≠ 0 := (hsc_res_def.symm.trans hsc_r) ▸ hsc_res_nz
    obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
      hold_half, hbt_all, hcomp, hsh_all, hta_le, htry_all⟩ := hinv.tiers
    obtain ⟨hsh_lt, hnot_try_b, hsl1_0, hsl2_0, shMap, hv_sh, hsh_eq⟩ := hsh_all b hb hsc_nz
    have hnot_try : ¬(fm.tryAct = 1 ∧ fm.tryBkt = b) := by
      simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hnot_try_b
    obtain ⟨hsl1_k, hsl2_k⟩ := hslack_in hb hsc_nz
    set shPos := fm.shadowCode b - 1
    set cnt := bp.bktCount b
    change shPos < cnt at hsh_lt
    change 4 * fm.shadowIns b + 5 * (cnt - shPos) + k ≤ 20 * slabScale fl.N ^ 12 at hsl1_k
    change 8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - shPos) + k ≤
      4 * slabScale fl.N ^ 12 at hsl2_k
    have hcnt_le : cnt ≤ capMaxWhp fl.N := hinv.bkt_le_capMax b hb
    have hcnt_le_N : cnt ≤ fl.N := hcnt_le.trans hcap_N
    have hcnt_res := fastReadBktCntProg_spec hr₀ hinv.bp_inv.1.core hb
    obtain ⟨hread_st, hread_res, hread_c⟩ := fastBpReadAtProg_spec hr₀ hinv.bp_inv hb hsh_lt
    obtain ⟨u, _, hu_val, _, hb_u, hq_u, _⟩ := hinv.bktSlot_refines hb hsh_lt
    have hq_lt : (bpPairAt fl.bpL s.mem b shPos).1 < 2 ^ quotBitsWhp fl.U fl.N :=
      hq_u ▸ keyQuotient_bWhp_lt hv.N_le_U u
    obtain ⟨hrec_res, hrec_c⟩ := fastFeistelReconProg_spec hr₀ hq_lt hinv.seed_bkt (bkt := b)
    have hu_rec : (Memory.spec 0).clientResult s
        (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s.mem b shPos).1))) = u.val :=
      hrec_res.trans hu_val.symm
    have hsalt_lt : fm.bktSalt b < sMaxWhp fl.c fl.N := (hinv.bkt_meta_bounds b hb).1
    have hsalt_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 5))) =
        fm.bktSalt b := by
      rw [clientResult_fastReadBktLaneProg hpt hb (by decide)]
      unfold fm extractFastMeta; dsimp only; rw [ite_eq_left hb]
    obtain ⟨hfp_res, hfp_c⟩ :=
      fastFpHashProg_spec hr₀ hinv.seed_fp ⟨fm.bktSalt b, hsalt_lt⟩ u
    dsimp only at hfp_res hfp_c
    set fp_u := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hsalt_lt⟩ u).val
    have hfp_lt : fp_u < 2 ^ fpBitsWhp fl.N :=
      (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hsalt_lt⟩ u).isLt
    have hcRole_lt : fm.curRole b < 3 := (hinv.bkt_meta_bounds b hb).2.1
    have hcIns_le : fm.curIns b ≤ 8 * slabScale fl.N ^ 12 := (hinv.bkt_meta_bounds b hb).2.2.1
    have hcRole_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12))) =
        fm.curRole b := by
      rw [clientResult_fastReadBktLaneProg hpt hb (by decide)]
      unfold fm extractFastMeta; dsimp only; rw [ite_eq_left hb]
    have hshIns_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 14))) =
        fm.shadowIns b := by
      rw [clientResult_fastReadBktLaneProg hpt hb (by decide)]
      unfold fm extractFastMeta; dsimp only; rw [ite_eq_left hb]
    obtain ⟨hlk_res, hlk_c⟩ :=
      fastBTreeLookupProg_spec hr₀ hb hcRole_lt hcIns_le (hbt_all b hb).1 hfp_lt
    set shRole := shadowRoleOf (fm.curRole b)
    obtain ⟨hshRole_lt, hshRole_ne⟩ := shadowRoleOf_lt_and_ne hcRole_lt
    have hshIns_lt_5L : fm.shadowIns b < 5 * slabScale fl.N ^ 12 := by omega
    have hshIns_lt_N : fm.shadowIns b < fl.N := by omega
    have hshPos_val : shPos < 2 ^ valLaneBitsWhp fl.N := by
      rw [two_pow_valLaneBitsWhp]; unfold capMaxWhp at hcnt_le; omega
    -- Unfold outer `fastShadowStepProg` + `fastShadowBodyProg` down to `fastShadowBodyTailProg`
    have hstep_eq :
        (Memory.spec 0).clientState s (fastShadowStepProg (fl.pBase, b)) =
          (Memory.spec 0).clientState s
            (fastShadowBodyTailProg (((fl.pBase, b), (shPos, cnt)), fp_u)) ∧
        memoryCost (fastShadowStepProg (fl.pBase, b)) s ≤
          135 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) +
            memoryCost (fastShadowBodyTailProg (((fl.pBase, b), (shPos, cnt)), fp_u)) s := by
      unfold fastShadowStepProg fastShadowBodyProg; dsimp only
      have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
      have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
          numBucketsWhp fl.N := hm11
      have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
      have hr0_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N := hm0
      have c15 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 15)) s
      have c5 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 5)) s
      have hcnt_r : (Memory.spec 0).clientResult s (fastReadBktCntProg (fl.pBase, b)) = cnt :=
        hcnt_res.1
      rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hr11_st, hr11_r,
        prog_memoryCost_read,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastReadBktLaneProg, hsc_res_def,
        ite_eq_left ⟨hb, hsc_res_nz⟩,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastReadBktCntProg, hcnt_r, ← hsc_res_def, hsc_r]
      change (Memory.spec 0).clientState s _ = _ ∧ _
      have hsh_def : fm.shadowCode b - 1 = shPos := rfl
      rw [hsh_def,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hr0_st, hr0_r,
        prog_memoryCost_read,
        ite_eq_left ⟨hsh_lt, hcnt_le_N⟩,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        hread_st, hread_res,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastFeistelReconProg, hu_rec,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastReadBktLaneProg, hsalt_r,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastFpHashProg, hfp_res]
      refine ⟨rfl, ?_⟩
      have hd4 : 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
          2 * (2 * dTabWhp fl.c * (cTabWhp fl.c + 2)) := by ring
      have hc_cnt := hcnt_res.2
      omega
    -- Unify the post-BTree state `s₁` and new `shMap₁` / `shIns₁` across hit vs miss
    have hmid :
        ∃ (s₁ : Memory.State) (shIns₁ : ℕ) (shMap₁ : ℕ → Option ℕ),
          (Memory.spec 0).clientState s
            (fastShadowBodyTailProg (((fl.pBase, b), (shPos, cnt)), fp_u)) =
            (Memory.spec 0).clientState s₁
              (fastShadowAdvanceProg ((fl.pBase, b), ((shPos, cnt), (shRole, shIns₁)))) ∧
          memoryCost (fastShadowBodyTailProg (((fl.pBase, b), (shPos, cnt)), fp_u)) s ≤
            175 + 78 * hMaxBTree +
              memoryCost (fastShadowAdvanceProg ((fl.pBase, b), ((shPos, cnt), (shRole, shIns₁))))
                s₁ ∧
          s₁.frontier = s.frontier ∧
          FastLayoutReady w fl s₁ ∧
          shIns₁ ≤ fm.shadowIns b + 1 ∧
          ValidWhpSlice fl.N shIns₁ (extractBTreeSlice fl.btL b shRole s₁.mem) shMap₁ ∧
          (∀ fp', shMap₁ fp' =
            match mapBTree b fp' with
            | some loc => if loc < shPos + 1 then some loc else none
            | none => none) ∧
          (∀ b' < numBucketsWhp fl.N, ∀ role' < 3, (b' ≠ b ∨ role' ≠ shRole) →
            extractBTreeSlice fl.btL b' role' s₁.mem =
              extractBTreeSlice fl.btL b' role' s.mem) ∧
          extractBlockPool fl.mp s₁.mem = extractBlockPool fl.mp s.mem ∧
          extractFastMeta fl s₁.mem = fm ∧
          s₁.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
          s₁.mem fl.metaBase = s.mem fl.metaBase ∧
          (∀ r < 2, extractBufTrie (fl.trieL r) s₁.mem = extractBufTrie (fl.trieL r) s.mem) ∧
          (∀ addr, fl.io.OwnsAddr addr → s₁.mem addr = s.mem addr) ∧
          (∀ addr, ¬fl.OwnsFastAddr addr → s₁.mem addr = s.mem addr) := by
      unfold fastShadowBodyTailProg; dsimp only
      have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
      have hr0_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N := hm0
      have c12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s
      have c14 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 14)) s
      have hshR_def : shadowRoleOf (fm.curRole b) = shRole := rfl
      rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hr0_st, hr0_r,
        prog_memoryCost_read,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastReadBktLaneProg, hcRole_r,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastBTreeLookupProg, hlk_res,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_shadowRoleProg, clientResult_shadowRoleProg, hshR_def,
        memoryCost_shadowRoleProg,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastReadBktLaneProg, hshIns_r]
      by_cases hhit : mapBTree b fp_u = some shPos
      · rw [hhit]
        dsimp only
        have hc_branch : 1 = 1 ∧ shPos = shPos ∧ fm.shadowIns b < fl.N :=
          ⟨rfl, rfl, hshIns_lt_N⟩
        rw [ite_eq_left hc_branch, StateTransitionSpec.clientState_bind,
          Realization.memoryCost_bind']
        obtain ⟨hfr1, hr1, hc_ins, hv_sh1, hbt_o1, hbp1, hfm1, hm2_1, hm0_1, htr1, hoi1, hof1⟩ :=
          fastBTreeInsertProg_spec (role := shRole) hr₀ hb hshRole_lt
            (by omega : fm.shadowIns b ≤ 8 * _) hv_sh hfp_lt hshPos_val
        refine ⟨_, fm.shadowIns b + 1, Function.update shMap fp_u (some shPos),
          rfl, by omega, hfr1, hr1, le_rfl, hv_sh1, fun fp' => ?_,
          hbt_o1, hbp1, hfm1, hm2_1, hm0_1, htr1, hoi1, hof1⟩
        · by_cases hfp_eq : fp' = fp_u
          · subst hfp_eq; rw [Function.update_self, hhit]
            dsimp only; rw [ite_eq_left (Nat.lt_succ_self _)]
          · rw [Function.update_of_ne hfp_eq, hsh_eq fp']
            cases hm' : mapBTree b fp' with
            | none => rfl
            | some loc =>
              dsimp only
              have hne_loc : loc ≠ shPos := by
                intro heq_l; subst heq_l
                obtain ⟨_, u', hfp_u', hkey_u', _⟩ := (hbt_all b hb).2 fp' shPos hm'
                have hu'_eq : u' = u := Fin.ext (hkey_u'.symm.trans hu_val.symm)
                subst hu'_eq; exact hfp_eq hfp_u'.symm
              by_cases hlt : loc < shPos
              · rw [ite_eq_left hlt, ite_eq_left (by omega : loc < shPos + 1)]
              · rw [ite_eq_right hlt, ite_eq_right (by omega : ¬loc < shPos + 1)]
      · have hc_branch : ¬((match mapBTree b fp_u with | none => (0, 0) | some v => (1, v)).1 = 1 ∧
            (match mapBTree b fp_u with | none => (0, 0) | some v => (1, v)).2 = shPos ∧
            fm.shadowIns b < fl.N) := by
          cases hm : mapBTree b fp_u with
          | none => simp
          | some v =>
            have hne : v ≠ shPos := fun he => hhit (he ▸ hm)
            simp [hne]
        rw [ite_eq_right hc_branch]
        refine ⟨s, fm.shadowIns b, shMap, rfl, by omega, rfl, hr₀, Nat.le_succ _, hv_sh,
          fun fp' => ?_, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
          fun _ _ => rfl, fun _ _ => rfl⟩
        rw [hsh_eq fp']
        cases hm' : mapBTree b fp' with
        | none => rfl
        | some loc =>
          dsimp only
          have hne_loc : loc ≠ shPos := by
            intro heq_l; subst heq_l
            obtain ⟨_, u', hfp_u', hkey_u', _⟩ := (hbt_all b hb).2 fp' shPos hm'
            have hu'_eq : u' = u := Fin.ext (hkey_u'.symm.trans hu_val.symm)
            subst hu'_eq; rw [← hfp_u'] at hm'; exact hhit hm'
          by_cases hlt : loc < shPos
          · rw [ite_eq_left hlt, ite_eq_left (by omega : loc < shPos + 1)]
          · rw [ite_eq_right hlt, ite_eq_right (by omega : ¬loc < shPos + 1)]
    obtain ⟨s₁, shIns₁, shMap₁, htail_st, htail_c, hfr₁, hr₁, hshIns₁_le, hv_sh₁, hshMap₁_eq,
      hbt_o₁, hbp₁, hfm₁, hm2_₁, hm0_₁, htr₁, hoi₁, hof₁⟩ := hmid
    obtain ⟨hfr_adv, hr_adv, hc_adv, hbp_adv, hbt_adv, htr_adv, hoi_adv, hof_adv⟩ :=
      fastShadowAdvanceProg_ready (b := b) (shPos := shPos) (cnt := cnt) (shRole := shRole)
        (shIns' := shIns₁) hr₁
    generalize hs₂_def : (Memory.spec 0).clientState s₁
      (fastShadowAdvanceProg ((fl.pBase, b), ((shPos, cnt), (shRole, shIns₁)))) = s₂
    rw [hs₂_def] at hfr_adv hr_adv hbp_adv hbt_adv htr_adv hoi_adv hof_adv htail_st
    have htot_st : (Memory.spec 0).clientState s (fastShadowStepProg (fl.pBase, b)) = s₂ :=
      hstep_eq.1.trans htail_st
    have htot_c : memoryCost (fastShadowStepProg (fl.pBase, b)) s ≤
        360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree := by
      have h1 := hstep_eq.2
      omega
    clear hstep_eq htail_st htail_c hc_adv hlk_res hlk_c hfp_lt fp_u hfp_res hfp_c hsalt_r
      hu_rec hread_st hread_res hread_c hcnt_res
    have harith_adv : ∀ (c p i i1 ci L kv : ℕ),
        p + 1 < c → i1 ≤ i + 1 →
        4 * i + 5 * (c - p) + kv ≤ 20 * L →
        8 * (ci - 6 * L) + (c - p) + kv ≤ 4 * L →
        (4 * i1 + 5 * (c - (p + 1)) + (kv + 1) ≤ 20 * L) ∧
        (8 * (ci - 6 * L) + (c - (p + 1)) + (kv + 1) ≤ 4 * L) := by
      intros; omega
    have hbp_tot : extractBlockPool fl.mp s₂.mem = bp := hbp_adv.trans hbp₁
    have htr_tot : ∀ r < 2, extractBufTrie (fl.trieL r) s₂.mem =
        extractBufTrie (fl.trieL r) s.mem :=
      fun r hr_lt => (htr_adv r hr_lt).trans (htr₁ r hr_lt)
    have hoi_tot : ∀ addr, fl.io.OwnsAddr addr → s₂.mem addr = s.mem addr :=
      fun a ha => (hoi_adv a ha).trans (hoi₁ a ha)
    have hof_tot : ∀ addr, ¬fl.OwnsFastAddr addr → s₂.mem addr = s.mem addr :=
      fun a ha => (hof_adv a ha).trans (hof₁ a ha)
    have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
        fastKeyAt fl seeds.bkt s₂.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
      fun b' loc' hb' hloc' => by
        unfold fastKeyAt bpPairAt; dsimp only [FastEpochLayout.bpL]
        rw [hbp_tot]
        have hp_lt : bp.toPhys b' loc' < bp.nSide := hinv.bp_inv.1.core.toPhys_lt hb' hloc'
        have hp_eq : slotIoPairAt fl.io s₂.mem (bp.toPhys b' loc') =
            slotIoPairAt fl.io s.mem (bp.toPhys b' loc') :=
          (fl.io.congr_of_outside hv.io_valid.w_pos hinv.bp_inv.2.2 hoi_tot).2 _ hp_lt
        rw [hp_eq]
    have hold_bounds : ∀ rk b₂ l₂, mapOld rk = some (b₂, l₂) →
        b₂ < numBucketsWhp fl.N ∧ l₂ < bp.bktCount b₂ := by
      intro rk b₂ l₂ hm₂
      by_cases hsub : fm.subStep < qEpochWhp fl.N / 2
      · have hh := hold_half; rw [ite_eq_left hsub] at hh
        obtain ⟨_, hb₂, hl₂, _⟩ := hh.2.2.2.2.2.2.2 rk b₂ l₂ hm₂
        exact ⟨hb₂, hl₂⟩
      · have hh := hold_half; rw [ite_eq_right hsub] at hh
        rw [hh.1] at hm₂; cases hm₂
    have hN_s₂ : s₂.mem fl.metaBase = fl.N :=
      (hof_tot fl.metaBase hv.not_ownsFast_hdr0).trans hinv.hdr_N
    have hbp_inv_s₂ : fl.bpL.StateInv slack s₂.mem :=
      ⟨hbp_tot ▸ hinv.bp_inv.1, hbp_tot ▸ hinv.bp_inv.2.1,
       hbp_tot ▸ (fl.io.congr_of_outside hv.io_valid.w_pos hinv.bp_inv.2.2 hoi_tot).1⟩
    have href_s₂ : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt)
        (extractBlockPool fl.mp s₂.mem).nSide
        (fun p => ((extractBlockPool fl.mp s₂.mem).ownerOf p).1)
        (slotIoPairAt fl.io s₂.mem) s_abs := by
      rw [hbp_tot]
      exact hinv.refines.congr (fun _ _ => rfl) fun p hp =>
        (fl.io.congr_of_outside hv.io_valid.w_pos hinv.bp_inv.2.2 hoi_tot).2 p hp
    have hm0_s₁ : s₁.mem (fl.pBase + 0) = fl.N := hr₁.2.1 0 (by decide)
    -- Split `fastShadowAdvanceProg`: `shPos + 1 < cnt` vs commit `shPos + 1 = cnt`
    by_cases hadv : shPos + 1 < cnt
    · have hshIns₁_le_N : shIns₁ ≤ fl.N := by linarith
      have hshPos2_le_N : shPos + 2 ≤ fl.N := (Nat.succ_le_of_lt hadv).trans hcnt_le_N
      obtain ⟨hbnd_k1, hbnd_k2⟩ :=
        harith_adv cnt shPos (fm.shadowIns b) shIns₁ (fm.curIns b) (slabScale fl.N ^ 12) k
          hadv hshIns₁_le hsl1_k hsl2_k
      obtain ⟨hbnd1, hbnd2⟩ :=
        harith_adv cnt shPos (fm.shadowIns b) shIns₁ (fm.curIns b) (slabScale fl.N ^ 12) 0
          hadv hshIns₁_le (by simpa only [Nat.add_zero] using hsl1_0)
          (by simpa only [Nat.add_zero] using hsl2_0)
      have hsub1 : shPos + 2 - 1 = shPos + 1 := rfl
      obtain ⟨hm2_s₂, hfm_s₂⟩ : s₂.mem (fl.metaBase + 2) = 0 ∧
          extractFastMeta fl s₂.mem =
            { fm with
              shadowIns := Function.update fm.shadowIns b shIns₁
              shadowCode := Function.update fm.shadowCode b (shPos + 2) } := by
        have hs₂_eq : s₂ = (Memory.spec 0).clientState
            ((Memory.spec 0).clientState s₁ (fastWriteBktLaneProg ((fl.pBase, (b, 14)), shIns₁)))
            (fastWriteBktLaneProg ((fl.pBase, (b, 15)), shPos + 2)) := by
          rw [← hs₂_def]; unfold fastShadowAdvanceProg; dsimp only
          have hr0_st : (Memory.spec 0).clientState s₁ (Memory.read (fl.pBase + 0)) = s₁ := rfl
          have hr0_r : (Memory.spec 0).clientResult s₁ (Memory.read (fl.pBase + 0)) = fl.N := hm0_s₁
          rw [StateTransitionSpec.clientState_bind, hr0_st, hr0_r,
            ite_eq_left hcnt_le_N, ite_eq_left hsh_lt, ite_eq_left hadv,
            StateTransitionSpec.clientState_bind]
        obtain ⟨_, hr₁a, _⟩ := fastWriteBktLaneProg_frame (b := b) (lane := 14) (val := shIns₁) hr₁
        obtain ⟨hm2_a, hfm_a⟩ := extractFastMeta_writeBktLane hr₁ hb
          (Or.inr ⟨by decide, by decide⟩ : 14 = 5 ∨ (12 ≤ 14 ∧ 14 < 16)) hshIns₁_le_N
        obtain ⟨hm2_b, hfm_b⟩ := extractFastMeta_writeBktLane hr₁a hb
          (Or.inr ⟨by decide, by decide⟩ : 15 = 5 ∨ (12 ≤ 15 ∧ 15 < 16)) hshPos2_le_N
        rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
          ite_eq_left rfl] at hfm_a
        rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
          ite_eq_right (by decide)] at hfm_b
        rw [← hs₂_eq] at hm2_b hfm_b
        exact ⟨hm2_b.trans (hm2_a.trans (hm2_₁.trans hinv.mode_zero)),
          by rw [hfm_b, hfm_a, hfm₁]⟩
      have hcr_eq : (extractFastMeta fl s₂.mem).curBufRole = fm.curBufRole := by rw [hfm_s₂]
      have hss_eq : (extractFastMeta fl s₂.mem).subStep = fm.subStep := by rw [hfm_s₂]
      have hdp_eq : (extractFastMeta fl s₂.mem).drainPos = fm.drainPos := by rw [hfm_s₂]
      have hta_eq : (extractFastMeta fl s₂.mem).tryAct = fm.tryAct := by rw [hfm_s₂]
      have htb_eq : (extractFastMeta fl s₂.mem).tryBkt = fm.tryBkt := by rw [hfm_s₂]
      have hts_eq : (extractFastMeta fl s₂.mem).trySalt = fm.trySalt := by rw [hfm_s₂]
      have htp_eq : (extractFastMeta fl s₂.mem).tryPos = fm.tryPos := by rw [hfm_s₂]
      have hti_eq : (extractFastMeta fl s₂.mem).tryIns = fm.tryIns := by rw [hfm_s₂]
      have hbs_eq : (extractFastMeta fl s₂.mem).bktSalt = fm.bktSalt := by rw [hfm_s₂]
      have hrl_eq : (extractFastMeta fl s₂.mem).curRole = fm.curRole := by rw [hfm_s₂]
      have hci_eq : (extractFastMeta fl s₂.mem).curIns = fm.curIns := by rw [hfm_s₂]
      have hsi_fn : (extractFastMeta fl s₂.mem).shadowIns =
          Function.update fm.shadowIns b shIns₁ := congrArg FastEpochMeta.shadowIns hfm_s₂
      have hsc_fn : (extractFastMeta fl s₂.mem).shadowCode =
          Function.update fm.shadowCode b (shPos + 2) := congrArg FastEpochMeta.shadowCode hfm_s₂
      have hbm_s₂ : ∀ b' < numBucketsWhp fl.N,
          let fm2 := extractFastMeta fl s₂.mem
          fm2.bktSalt b' < sMaxWhp fl.c fl.N ∧
          fm2.curRole b' < 3 ∧
          fm2.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
          (fm2.shadowCode b' = 0 → ¬(fm2.tryAct = 1 ∧ fm2.tryBkt = b') →
            fm2.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' =>
        ⟨by rw [congrFun hbs_eq b']; exact (hinv.bkt_meta_bounds b' hb').1,
         by rw [congrFun hrl_eq b']; exact (hinv.bkt_meta_bounds b' hb').2.1,
         by rw [congrFun hci_eq b']; exact (hinv.bkt_meta_bounds b' hb').2.2.1,
         fun hsc0' hnt' => by
           rw [congrFun hci_eq b']
           rw [hta_eq, htb_eq] at hnt'
           by_cases hbb : b' = b
           · subst hbb; rw [congrFun hsc_fn b', Function.update_self] at hsc0'; nomatch hsc0'
           · rw [congrFun hsc_fn b', Function.update_of_ne hbb] at hsc0'
             exact (hinv.bkt_meta_bounds b' hb').2.2.2 hsc0' hnt'⟩
      have hsl_out : b < numBucketsWhp fl.N → (extractFastMeta fl s₂.mem).shadowCode b ≠ 0 →
          let cnt' := (extractBlockPool fl.mp s.mem).bktCount b
          4 * (extractFastMeta fl s₂.mem).shadowIns b +
            5 * (cnt' - ((extractFastMeta fl s₂.mem).shadowCode b - 1)) + (k + 1) ≤
            20 * slabScale fl.N ^ 12 ∧
          8 * ((extractFastMeta fl s₂.mem).curIns b - 6 * slabScale fl.N ^ 12) +
            (cnt' - ((extractFastMeta fl s₂.mem).shadowCode b - 1)) + (k + 1) ≤
            4 * slabScale fl.N ^ 12 := fun _ _ => by
        dsimp only
        rw [congrFun hsi_fn b, Function.update_self, congrFun hsc_fn b, Function.update_self,
          congrFun hci_eq b, hsub1]
        exact ⟨hbnd_k1, hbnd_k2⟩
      rw [htot_st]
      refine ⟨hfr_adv.trans hfr₁, htot_c, ?_, hbp_tot, hcr_eq, hss_eq, hdp_eq, hta_eq,
        htb_eq, hts_eq, htp_eq, hti_eq, hbs_eq, htr_tot, hoi_tot, hof_tot,
        fun b' hne => ⟨congrFun hrl_eq b', congrFun hci_eq b',
          by rw [congrFun hsi_fn b', Function.update_of_ne hne],
          by rw [congrFun hsc_fn b', Function.update_of_ne hne]⟩,
        hsl_out⟩
      refine
        { param_table := hr_adv.2.1
          hdr_N := hN_s₂
          mode_zero := hm2_s₂
          seed_bkt := hinv.seed_bkt.congr_on hw_pos fun a h1 h2 =>
            hof_tot a (hv.not_ownsFast_seeds
              (by dsimp only [FastEpochLayout.bktHashBase] at h1; exact h1)
              (by dsimp only [FastEpochLayout.bktHashBase] at h2
                  unfold offBktMeta offFpHash offBktHash at *; omega))
          seed_fp := hinv.seed_fp.congr_on hw_pos fun a h1 h2 =>
            hof_tot a (hv.not_ownsFast_seeds
              (by dsimp only [FastEpochLayout.fpHashBase] at h1
                  unfold offFpHash offBktHash at *; omega)
              (by dsimp only [FastEpochLayout.fpHashBase] at h2
                  unfold offBktMeta offFpHash offBktHash at *; omega))
          bp_inv := hbp_inv_s₂
          bkt_le_capMax := fun b' hb' => by rw [hbp_tot]; exact hinv.bkt_le_capMax b' hb'
          refines := href_s₂
          role_lt := by rw [hcr_eq]; exact hinv.role_lt
          subStep_lt := by rw [hss_eq]; exact hinv.subStep_lt
          bkt_meta_bounds := hbm_s₂
          tiers := ?_ }
      dsimp only
      have htr_c := htr_tot fm.curBufRole hinv.role_lt
      have htr_o := htr_tot (1 - fm.curBufRole) (by have := hinv.role_lt; omega)
      refine ⟨mapCur, mapOld, mapBTree,
        by rw [hcr_eq, htr_c]; exact hv_cur,
        by rw [hcr_eq, htr_c]; exact hrb_cur,
        by rw [hcr_eq, htr_c]; exact hrc_cur,
        by rw [hcr_eq, htr_c, hss_eq]; exact hia_cur,
        by rw [hcr_eq, htr_c]; exact hna_cur,
        fun rk b' loc' hm => by
          obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
          exact ⟨hb', by rw [hbp_tot]; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
        ?_, ?_, ?_, ?_, by rw [hta_eq]; exact hta_le, ?_⟩
      · rw [hss_eq, hcr_eq, htr_o, hdp_eq, hbp_tot]
        by_cases hsub : fm.subStep < qEpochWhp fl.N / 2
        · rw [ite_eq_left hsub] at hold_half ⊢
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hold_half
          exact ⟨h1, h2, h3, h4, h5, h6, h7, fun rk b' loc' hm => by
            obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := h8 rk b' loc' hm
            exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩⟩
        · rw [ite_eq_right hsub] at hold_half ⊢
          rw [hta_eq]; exact hold_half
      · intro b' hb'
        rw [hbp_tot]
        refine ⟨?_, fun fp' loc' hm => ?_⟩
        · rw [congrFun hci_eq b', congrFun hrl_eq b']
          have hbt_s₂ : extractBTreeSlice fl.btL b' (fm.curRole b') s₂.mem =
              extractBTreeSlice fl.btL b' (fm.curRole b') s.mem :=
            (hbt_adv b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1).trans
              (hbt_o₁ b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1
                (by by_cases heq : b' = b
                    · subst heq; exact Or.inr hshRole_ne.symm
                    · exact Or.inl heq))
          rw [hbt_s₂]
          exact (hbt_all b' hb').1
        · obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
          exact ⟨hl', u', (congrArg Fin.val (fpHash_congr_salt (congrFun hbs_eq b') u')).trans hfp',
            (hkey_eq b' loc' hb' hl').trans hk',
            fun b₁ l₁ hm₁ => by
              obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
              rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
            fun b₂ l₂ hm₂ => by
              obtain ⟨hb₂, hl₂⟩ := hold_bounds _ b₂ l₂ hm₂
              rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
      · intro b' hb' loc' hloc'
        rw [hbp_tot] at hloc'
        obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
        refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
        rw [fpHash_congr_salt (congrFun hbs_eq b') u']; exact ht'
      · intro b' hb' hsc'
        rw [hta_eq, htb_eq, congrFun hci_eq b', congrFun hrl_eq b', hbp_tot]
        by_cases hbb : b' = b
        · subst hbb
          have hsc_val : (extractFastMeta fl s₂.mem).shadowCode b' = shPos + 2 := by
            rw [congrFun hsc_fn b', Function.update_self]
          have hsi_val : (extractFastMeta fl s₂.mem).shadowIns b' = shIns₁ := by
            rw [congrFun hsi_fn b', Function.update_self]
          rw [hsc_val, hsi_val, hsub1]
          have hbt_sh : extractBTreeSlice fl.btL b' shRole s₂.mem =
              extractBTreeSlice fl.btL b' shRole s₁.mem := hbt_adv b' hb' shRole hshRole_lt
          have hv_sh₂ : ValidWhpSlice fl.N shIns₁
              (extractBTreeSlice fl.btL b' (shadowRoleOf (fm.curRole b')) s₂.mem) shMap₁ := by
            change ValidWhpSlice fl.N shIns₁ (extractBTreeSlice fl.btL b' shRole s₂.mem) shMap₁
            rw [hbt_sh]; exact hv_sh₁
          exact ⟨hadv, hnot_try_b, Nat.le_of_add_right_le hbnd1,
            Nat.le_of_add_right_le hbnd2, shMap₁, hv_sh₂, hshMap₁_eq⟩
        · have hsc_val : (extractFastMeta fl s₂.mem).shadowCode b' = fm.shadowCode b' := by
            rw [congrFun hsc_fn b', Function.update_of_ne hbb]
          have hsi_val : (extractFastMeta fl s₂.mem).shadowIns b' = fm.shadowIns b' := by
            rw [congrFun hsi_fn b', Function.update_of_ne hbb]
          rw [hsc_val] at hsc' ⊢; rw [hsi_val]
          obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc'
          have hr_sm := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
          have hbt_sm : extractBTreeSlice fl.btL b' (shadowRoleOf (fm.curRole b')) s₂.mem =
              extractBTreeSlice fl.btL b' (shadowRoleOf (fm.curRole b')) s.mem :=
            (hbt_adv b' hb' _ hr_sm).trans (hbt_o₁ b' hb' _ hr_sm (Or.inl hbb))
          exact ⟨h1, h2, h3, h4, sm', by rw [hbt_sm]; exact hv_sm', heq_sm'⟩
      · intro hta1
        rw [hta_eq] at hta1
        obtain ⟨hsub, hb_t, hs_t, htp_le, hsc_t, hti_le, tm, hv_tm, ht_s, ht_c⟩ := htry_all hta1
        have hne_tb : fm.tryBkt ≠ b := fun heq => hnot_try ⟨hta1, heq⟩
        have hbs_tb : (extractFastMeta fl s₂.mem).bktSalt (extractFastMeta fl s₂.mem).tryBkt =
            fm.bktSalt fm.tryBkt := by rw [htb_eq, congrFun hbs_eq fm.tryBkt]
        rw [hss_eq, htp_eq, hti_eq, hbp_tot]
        refine ⟨hsub, htb_eq.symm ▸ hb_t, hts_eq.symm ▸ hs_t,
          by rw [htb_eq]; exact htp_le,
          by rw [htb_eq, congrFun hsc_fn fm.tryBkt, Function.update_of_ne hne_tb]; exact hsc_t,
          by rw [htb_eq]; exact hti_le, tm, ?_, ?_, ?_⟩
        · rw [htb_eq, congrFun hrl_eq fm.tryBkt]
          have hr_tr := (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds fm.tryBkt hb_t).2.1).1
          have hbt_tr : extractBTreeSlice fl.btL fm.tryBkt
              (tryRoleOf (fm.curRole fm.tryBkt)) s₂.mem =
              extractBTreeSlice fl.btL fm.tryBkt (tryRoleOf (fm.curRole fm.tryBkt)) s.mem :=
            (hbt_adv _ hb_t _ hr_tr).trans (hbt_o₁ _ hb_t _ hr_tr (Or.inl hne_tb))
          rw [hbt_tr]; exact hv_tm
        · intro fp' loc' htm
          obtain ⟨hl', u', hk', hmb', hfp_t⟩ := ht_s fp' loc' htm
          exact ⟨hl', u',
            by rw [htb_eq]; exact (hkey_eq _ _ hb_t (hl'.trans_le htp_le)).trans hk',
            by rw [mapBTree_fpHash_congr mapBTree htb_eq hbs_tb u']; exact hmb',
            (congrArg Fin.val (fpHash_congr_salt hts_eq u')).trans hfp_t⟩
        · intro loc' hl' u' hk' hmb'
          rw [htb_eq] at hk'
          rw [mapBTree_fpHash_congr mapBTree (h₂ := (hinv.bkt_meta_bounds fm.tryBkt hb_t).1)
            htb_eq hbs_tb u'] at hmb'
          rw [fpHash_congr_salt hts_eq u']
          exact ht_c loc' hl' u' ((hkey_eq _ _ hb_t (hl'.trans_le htp_le)).symm.trans hk') hmb'
    · -- Commit branch (`shPos + 1 = cnt`)
      have hcnt_eq : shPos + 1 = cnt := le_antisymm (Nat.succ_le_of_lt hsh_lt) (Nat.not_lt.mp hadv)
      have hshRole_le_N : shRole ≤ fl.N := by linarith
      have hshIns₁_le_N : shIns₁ ≤ fl.N := by linarith
      obtain ⟨hm2_s₂, hfm_s₂⟩ : s₂.mem (fl.metaBase + 2) = 0 ∧
          extractFastMeta fl s₂.mem =
            { fm with
              curRole := Function.update fm.curRole b shRole
              curIns := Function.update fm.curIns b shIns₁
              shadowIns := Function.update fm.shadowIns b 0
              shadowCode := Function.update fm.shadowCode b 0 } := by
        have hs₂_eq : s₂ = (Memory.spec 0).clientState s₁
            (fastCommitShadowProg (fl.pBase, (b, (shRole, shIns₁)))) := by
          rw [← hs₂_def]; unfold fastShadowAdvanceProg; dsimp only
          have hr0_st : (Memory.spec 0).clientState s₁ (Memory.read (fl.pBase + 0)) = s₁ := rfl
          have hr0_r : (Memory.spec 0).clientResult s₁ (Memory.read (fl.pBase + 0)) = fl.N := hm0_s₁
          rw [StateTransitionSpec.clientState_bind, hr0_st, hr0_r,
            ite_eq_left hcnt_le_N, ite_eq_left hsh_lt, ite_eq_right hadv]
        set w1 := (Memory.spec 0).clientState s₁
          (fastWriteBktLaneProg ((fl.pBase, (b, 12)), shRole))
        set w2 := (Memory.spec 0).clientState w1
          (fastWriteBktLaneProg ((fl.pBase, (b, 13)), shIns₁))
        set w3 := (Memory.spec 0).clientState w2
          (fastWriteBktLaneProg ((fl.pBase, (b, 14)), 0))
        have hs₂_w4' : (Memory.spec 0).clientState w3
            (fastWriteBktLaneProg ((fl.pBase, (b, 15)), 0)) = s₂ := by
          rw [hs₂_eq]; unfold fastCommitShadowProg
          rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
            StateTransitionSpec.clientState_bind]
        obtain ⟨_, hrw1, _⟩ := fastWriteBktLaneProg_frame (b := b) (lane := 12) (val := shRole) hr₁
        obtain ⟨_, hrw2, _⟩ := fastWriteBktLaneProg_frame (b := b) (lane := 13) (val := shIns₁) hrw1
        obtain ⟨_, hrw3, _⟩ := fastWriteBktLaneProg_frame (b := b) (lane := 14) (val := 0) hrw2
        obtain ⟨hm2_1, hfm_w1⟩ := extractFastMeta_writeBktLane hr₁ hb
          (Or.inr ⟨by decide, by decide⟩ : 12 = 5 ∨ (12 ≤ 12 ∧ 12 < 16)) hshRole_le_N
        obtain ⟨hm2_2, hfm_w2⟩ := extractFastMeta_writeBktLane hrw1 hb
          (Or.inr ⟨by decide, by decide⟩ : 13 = 5 ∨ (12 ≤ 13 ∧ 13 < 16)) hshIns₁_le_N
        obtain ⟨hm2_3, hfm_w3⟩ := extractFastMeta_writeBktLane hrw2 hb
          (Or.inr ⟨by decide, by decide⟩ : 14 = 5 ∨ (12 ≤ 14 ∧ 14 < 16)) (Nat.zero_le _)
        obtain ⟨hm2_4, hfm_w4⟩ := extractFastMeta_writeBktLane hrw3 hb
          (Or.inr ⟨by decide, by decide⟩ : 15 = 5 ∨ (12 ≤ 15 ∧ 15 < 16)) (Nat.zero_le _)
        rw [ite_eq_right (by decide), ite_eq_left rfl] at hfm_w1
        rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl] at hfm_w2
        rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
          ite_eq_left rfl] at hfm_w3
        rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
          ite_eq_right (by decide)] at hfm_w4
        rw [hs₂_w4'] at hm2_4 hfm_w4
        exact ⟨hm2_4.trans (hm2_3.trans (hm2_2.trans (hm2_1.trans (hm2_₁.trans hinv.mode_zero)))),
          by rw [hfm_w4, hfm_w3, hfm_w2, hfm_w1, hfm₁]⟩
      have hshMap_full : shMap₁ = mapBTree b := by
        ext fp'; rw [hshMap₁_eq fp']
        cases hm' : mapBTree b fp' with
        | none => rfl
        | some loc' =>
          have hloc_cnt : loc' < shPos + 1 := hcnt_eq ▸ ((hbt_all b hb).2 fp' loc' hm').1
          dsimp only; rw [ite_eq_left hloc_cnt]
      have hshIns₁_lt_6L : shIns₁ < 6 * slabScale fl.N ^ 12 := by linarith
      have hcr_eq : (extractFastMeta fl s₂.mem).curBufRole = fm.curBufRole := by rw [hfm_s₂]
      have hss_eq : (extractFastMeta fl s₂.mem).subStep = fm.subStep := by rw [hfm_s₂]
      have hdp_eq' : (extractFastMeta fl s₂.mem).drainPos = fm.drainPos := by rw [hfm_s₂]
      have hta_eq : (extractFastMeta fl s₂.mem).tryAct = fm.tryAct := by rw [hfm_s₂]
      have htb_eq : (extractFastMeta fl s₂.mem).tryBkt = fm.tryBkt := by rw [hfm_s₂]
      have hts_eq : (extractFastMeta fl s₂.mem).trySalt = fm.trySalt := by rw [hfm_s₂]
      have htp_eq : (extractFastMeta fl s₂.mem).tryPos = fm.tryPos := by rw [hfm_s₂]
      have hti_eq : (extractFastMeta fl s₂.mem).tryIns = fm.tryIns := by rw [hfm_s₂]
      have hbs_eq : (extractFastMeta fl s₂.mem).bktSalt = fm.bktSalt := by rw [hfm_s₂]
      have hrl_fn : (extractFastMeta fl s₂.mem).curRole =
          Function.update fm.curRole b shRole := congrArg FastEpochMeta.curRole hfm_s₂
      have hci_fn : (extractFastMeta fl s₂.mem).curIns =
          Function.update fm.curIns b shIns₁ := congrArg FastEpochMeta.curIns hfm_s₂
      have hsi_fn : (extractFastMeta fl s₂.mem).shadowIns =
          Function.update fm.shadowIns b 0 := congrArg FastEpochMeta.shadowIns hfm_s₂
      have hsc_fn : (extractFastMeta fl s₂.mem).shadowCode =
          Function.update fm.shadowCode b 0 := congrArg FastEpochMeta.shadowCode hfm_s₂
      have hsc_b0 : (extractFastMeta fl s₂.mem).shadowCode b = 0 := by
        rw [congrFun hsc_fn b, Function.update_self]
      have hbm_s₂ : ∀ b' < numBucketsWhp fl.N,
          let fm2 := extractFastMeta fl s₂.mem
          fm2.bktSalt b' < sMaxWhp fl.c fl.N ∧
          fm2.curRole b' < 3 ∧
          fm2.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
          (fm2.shadowCode b' = 0 → ¬(fm2.tryAct = 1 ∧ fm2.tryBkt = b') →
            fm2.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' =>
        ⟨by rw [congrFun hbs_eq b']; exact (hinv.bkt_meta_bounds b' hb').1,
         by by_cases hbb : b' = b
            · subst hbb; rw [congrFun hrl_fn b', Function.update_self]; exact hshRole_lt
            · rw [congrFun hrl_fn b', Function.update_of_ne hbb]
              exact (hinv.bkt_meta_bounds b' hb').2.1,
         by by_cases hbb : b' = b
            · subst hbb; rw [congrFun hci_fn b', Function.update_self]; linarith
            · rw [congrFun hci_fn b', Function.update_of_ne hbb]
              exact (hinv.bkt_meta_bounds b' hb').2.2.1,
         fun hsc0' hnt' => by
           rw [hta_eq, htb_eq] at hnt'
           by_cases hbb : b' = b
           · subst hbb; rw [congrFun hci_fn b', Function.update_self]; exact hshIns₁_lt_6L
           · rw [congrFun hsc_fn b', Function.update_of_ne hbb] at hsc0'
             rw [congrFun hci_fn b', Function.update_of_ne hbb]
             exact (hinv.bkt_meta_bounds b' hb').2.2.2 hsc0' hnt'⟩
      rw [htot_st]
      refine ⟨hfr_adv.trans hfr₁, htot_c, ?_, hbp_tot, hcr_eq, hss_eq, hdp_eq', hta_eq,
        htb_eq, hts_eq, htp_eq, hti_eq, hbs_eq, htr_tot, hoi_tot, hof_tot,
        fun b' hne => ⟨by rw [congrFun hrl_fn b', Function.update_of_ne hne],
          by rw [congrFun hci_fn b', Function.update_of_ne hne],
          by rw [congrFun hsi_fn b', Function.update_of_ne hne],
          by rw [congrFun hsc_fn b', Function.update_of_ne hne]⟩,
        fun _ hsc' => absurd hsc_b0 hsc'⟩
      refine
        { param_table := hr_adv.2.1
          hdr_N := hN_s₂
          mode_zero := hm2_s₂
          seed_bkt := hinv.seed_bkt.congr_on hw_pos fun a h1 h2 =>
            hof_tot a (hv.not_ownsFast_seeds
              (by dsimp only [FastEpochLayout.bktHashBase] at h1; exact h1)
              (by dsimp only [FastEpochLayout.bktHashBase] at h2
                  unfold offBktMeta offFpHash offBktHash at *; omega))
          seed_fp := hinv.seed_fp.congr_on hw_pos fun a h1 h2 =>
            hof_tot a (hv.not_ownsFast_seeds
              (by dsimp only [FastEpochLayout.fpHashBase] at h1
                  unfold offFpHash offBktHash at *; omega)
              (by dsimp only [FastEpochLayout.fpHashBase] at h2
                  unfold offBktMeta offFpHash offBktHash at *; omega))
          bp_inv := hbp_inv_s₂
          bkt_le_capMax := fun b' hb' => by rw [hbp_tot]; exact hinv.bkt_le_capMax b' hb'
          refines := href_s₂
          role_lt := by rw [hcr_eq]; exact hinv.role_lt
          subStep_lt := by rw [hss_eq]; exact hinv.subStep_lt
          bkt_meta_bounds := hbm_s₂
          tiers := ?_ }
      dsimp only
      have htr_c := htr_tot fm.curBufRole hinv.role_lt
      have htr_o := htr_tot (1 - fm.curBufRole) (by have := hinv.role_lt; omega)
      refine ⟨mapCur, mapOld, mapBTree,
        by rw [hcr_eq, htr_c]; exact hv_cur,
        by rw [hcr_eq, htr_c]; exact hrb_cur,
        by rw [hcr_eq, htr_c]; exact hrc_cur,
        by rw [hcr_eq, htr_c, hss_eq]; exact hia_cur,
        by rw [hcr_eq, htr_c]; exact hna_cur,
        fun rk b' loc' hm => by
          obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
          exact ⟨hb', by rw [hbp_tot]; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
        ?_, ?_, ?_, ?_, by rw [hta_eq]; exact hta_le, ?_⟩
      · rw [hss_eq, hcr_eq, htr_o, hdp_eq', hbp_tot]
        by_cases hsub : fm.subStep < qEpochWhp fl.N / 2
        · rw [ite_eq_left hsub] at hold_half ⊢
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hold_half
          exact ⟨h1, h2, h3, h4, h5, h6, h7, fun rk b' loc' hm => by
            obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := h8 rk b' loc' hm
            exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩⟩
        · rw [ite_eq_right hsub] at hold_half ⊢
          rw [hta_eq]; exact hold_half
      · intro b' hb'
        rw [hbp_tot]
        refine ⟨?_, fun fp' loc' hm => ?_⟩
        · by_cases hbb : b' = b
          · subst hbb
            have hrl_b : (extractFastMeta fl s₂.mem).curRole b' = shRole := by
              rw [congrFun hrl_fn b', Function.update_self]
            have hci_b : (extractFastMeta fl s₂.mem).curIns b' = shIns₁ := by
              rw [congrFun hci_fn b', Function.update_self]
            rw [hrl_b, hci_b, hbt_adv b' hb' shRole hshRole_lt, ← hshMap_full]
            exact hv_sh₁
          · have hrl_b : (extractFastMeta fl s₂.mem).curRole b' = fm.curRole b' := by
              rw [congrFun hrl_fn b', Function.update_of_ne hbb]
            have hci_b : (extractFastMeta fl s₂.mem).curIns b' = fm.curIns b' := by
              rw [congrFun hci_fn b', Function.update_of_ne hbb]
            rw [hrl_b, hci_b]
            have hr_b' := (hinv.bkt_meta_bounds b' hb').2.1
            have hbt_b' : extractBTreeSlice fl.btL b' (fm.curRole b') s₂.mem =
                extractBTreeSlice fl.btL b' (fm.curRole b') s.mem :=
              (hbt_adv b' hb' _ hr_b').trans (hbt_o₁ b' hb' _ hr_b' (Or.inl hbb))
            rw [hbt_b']; exact (hbt_all b' hb').1
        · obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
          exact ⟨hl', u', (congrArg Fin.val (fpHash_congr_salt (congrFun hbs_eq b') u')).trans hfp',
            (hkey_eq b' loc' hb' hl').trans hk',
            fun b₁ l₁ hm₁ => by
              obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
              rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
            fun b₂ l₂ hm₂ => by
              obtain ⟨hb₂, hl₂⟩ := hold_bounds _ b₂ l₂ hm₂
              rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
      · intro b' hb' loc' hloc'
        rw [hbp_tot] at hloc'
        obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
        refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
        rw [fpHash_congr_salt (congrFun hbs_eq b') u']; exact ht'
      · intro b' hb' hsc'
        by_cases hbb : b' = b
        · subst hbb; exact absurd hsc_b0 hsc'
        · have hsc_val : (extractFastMeta fl s₂.mem).shadowCode b' = fm.shadowCode b' := by
            rw [congrFun hsc_fn b', Function.update_of_ne hbb]
          have hsi_val : (extractFastMeta fl s₂.mem).shadowIns b' = fm.shadowIns b' := by
            rw [congrFun hsi_fn b', Function.update_of_ne hbb]
          have hci_val : (extractFastMeta fl s₂.mem).curIns b' = fm.curIns b' := by
            rw [congrFun hci_fn b', Function.update_of_ne hbb]
          have hrl_val : (extractFastMeta fl s₂.mem).curRole b' = fm.curRole b' := by
            rw [congrFun hrl_fn b', Function.update_of_ne hbb]
          rw [hsc_val] at hsc' ⊢
          rw [hta_eq, htb_eq, hsi_val, hci_val, hrl_val, hbp_tot]
          obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc'
          have hr_sm := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
          have hbt_sm : extractBTreeSlice fl.btL b' (shadowRoleOf (fm.curRole b')) s₂.mem =
              extractBTreeSlice fl.btL b' (shadowRoleOf (fm.curRole b')) s.mem :=
            (hbt_adv b' hb' _ hr_sm).trans (hbt_o₁ b' hb' _ hr_sm (Or.inl hbb))
          exact ⟨h1, h2, h3, h4, sm', by rw [hbt_sm]; exact hv_sm', heq_sm'⟩
      · intro hta1
        rw [hta_eq] at hta1
        obtain ⟨hsub, hb_t, hs_t, htp_le, hsc_t, hti_le, tm, hv_tm, ht_s, ht_c⟩ := htry_all hta1
        have hne_tb : fm.tryBkt ≠ b := fun heq => hnot_try ⟨hta1, heq⟩
        have hrl_tb : (extractFastMeta fl s₂.mem).curRole fm.tryBkt = fm.curRole fm.tryBkt := by
          rw [congrFun hrl_fn fm.tryBkt, Function.update_of_ne hne_tb]
        have hbs_tb : (extractFastMeta fl s₂.mem).bktSalt (extractFastMeta fl s₂.mem).tryBkt =
            fm.bktSalt fm.tryBkt := by rw [htb_eq, congrFun hbs_eq fm.tryBkt]
        rw [hss_eq, htp_eq, hti_eq, hbp_tot]
        refine ⟨hsub, htb_eq.symm ▸ hb_t, hts_eq.symm ▸ hs_t,
          by rw [htb_eq]; exact htp_le,
          by rw [htb_eq, congrFun hsc_fn fm.tryBkt, Function.update_of_ne hne_tb]; exact hsc_t,
          by rw [htb_eq]; exact hti_le, tm, ?_, ?_, ?_⟩
        · rw [htb_eq, hrl_tb]
          have hr_tr := (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds fm.tryBkt hb_t).2.1).1
          have hbt_tr : extractBTreeSlice fl.btL fm.tryBkt
              (tryRoleOf (fm.curRole fm.tryBkt)) s₂.mem =
              extractBTreeSlice fl.btL fm.tryBkt (tryRoleOf (fm.curRole fm.tryBkt)) s.mem :=
            (hbt_adv _ hb_t _ hr_tr).trans (hbt_o₁ _ hb_t _ hr_tr (Or.inl hne_tb))
          rw [hbt_tr]; exact hv_tm
        · intro fp' loc' htm
          obtain ⟨hl', u', hk', hmb', hfp_t⟩ := ht_s fp' loc' htm
          exact ⟨hl', u',
            by rw [htb_eq]; exact (hkey_eq _ _ hb_t (hl'.trans_le htp_le)).trans hk',
            by rw [mapBTree_fpHash_congr mapBTree htb_eq hbs_tb u']; exact hmb',
            (congrArg Fin.val (fpHash_congr_salt hts_eq u')).trans hfp_t⟩
        · intro loc' hl' u' hk' hmb'
          rw [htb_eq] at hk'
          rw [mapBTree_fpHash_congr mapBTree (h₂ := (hinv.bkt_meta_bounds fm.tryBkt hb_t).1)
            htb_eq hbs_tb u'] at hmb'
          rw [fpHash_congr_salt hts_eq u']
          exact ht_c loc' hl' u' ((hkey_eq _ _ hb_t (hl'.trans_le htp_le)).symm.trans hk') hmb'
  · -- Guard false (`b ≥ M ∨ fm.shadowCode b = 0`): pure no-op!
    have hst : (Memory.spec 0).clientState s (fastShadowStepProg (fl.pBase, b)) = s := by
      unfold fastShadowStepProg; dsimp only
      have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
      have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
          numBucketsWhp fl.N := hm11
      rw [StateTransitionSpec.clientState_bind, hr11_st, hr11_r,
        StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg, hsc_res_def,
        ite_eq_right hguard]
      rfl
    have hc : memoryCost (fastShadowStepProg (fl.pBase, b)) s ≤ 10 := by
      unfold fastShadowStepProg; dsimp only
      have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
      have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
          numBucketsWhp fl.N := hm11
      have c15 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 15)) s
      rw [Realization.memoryCost_bind', hr11_st, hr11_r, prog_memoryCost_read,
        Realization.memoryCost_bind', clientState_fastReadBktLaneProg, hsc_res_def,
        ite_eq_right hguard, memoryCost_pure]
      omega
    rw [hst]
    refine ⟨rfl, by omega, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun hb hsc => ?_⟩
    have hsc_eq : sc_res = fm.shadowCode b := by
      rw [← hsc_res_def, clientResult_fastReadBktLaneProg hpt hb (by decide)]
      unfold fm extractFastMeta; dsimp only; rw [ite_eq_left hb]
    exact absurd ⟨hb, hsc_eq.symm ▸ hsc⟩ hguard

private def fastShadowSteps2Prog : ℕ × ℕ → Memory.Prog Unit
  | x => do fastShadowStepProg x; fastShadowStepProg x

private theorem fastShadowSteps2Prog_pre {w : ℕ} {x : ℕ × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1 s) :
    FastProgPre w x.1 ((Memory.spec 0).clientState s (fastShadowSteps2Prog x)) := by
  unfold fastShadowSteps2Prog; rw [StateTransitionSpec.clientState_bind]
  exact fastShadowStepProg_pre (fastShadowStepProg_pre h)

private theorem realizesBounded_fastShadowSteps2 :
    RealizesBounded .exact fastShadowSteps2Prog
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hs := realizesBounded_fastShadowStep
  realize
  all_goals first | exact h | exact fastShadowStepProg_pre h

private def fastShadowSteps4Prog : ℕ × ℕ → Memory.Prog Unit
  | x => do fastShadowSteps2Prog x; fastShadowSteps2Prog x

private theorem fastShadowSteps4Prog_pre {w : ℕ} {x : ℕ × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1 s) :
    FastProgPre w x.1 ((Memory.spec 0).clientState s (fastShadowSteps4Prog x)) := by
  unfold fastShadowSteps4Prog; rw [StateTransitionSpec.clientState_bind]
  exact fastShadowSteps2Prog_pre (fastShadowSteps2Prog_pre h)

private theorem realizesBounded_fastShadowSteps4 :
    RealizesBounded .exact fastShadowSteps4Prog
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hs := realizesBounded_fastShadowSteps2
  realize
  all_goals first | exact h | exact fastShadowSteps2Prog_pre h

/-- Run `8` deamortized shadow-compaction steps on bucket `b` (`¬ReadsWidth`). -/
def fastShadowSteps8Prog : ℕ × ℕ → Memory.Prog Unit
  | x => do fastShadowSteps4Prog x; fastShadowSteps4Prog x

theorem fastShadowSteps8Prog_pre {w : ℕ} {x : ℕ × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1 s) :
    FastProgPre w x.1 ((Memory.spec 0).clientState s (fastShadowSteps8Prog x)) := by
  unfold fastShadowSteps8Prog; rw [StateTransitionSpec.clientState_bind]
  exact fastShadowSteps4Prog_pre (fastShadowSteps4Prog_pre h)

theorem realizesBounded_fastShadowSteps8 :
    RealizesBounded .exact fastShadowSteps8Prog
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hs := realizesBounded_fastShadowSteps4
  realize
  all_goals first | exact h | exact fastShadowSteps4Prog_pre h

/-- Exact 8-step shadow compaction specification: preserves `FastEpochInvGen` on **100%** of hash
seeds, leaves `BlockPool`, `BufTrie`, and all global/salt metadata untouched, and guarantees `+ 8`
slack on any surviving `shadowCode b ≠ 0`. -/
theorem fastShadowSteps8Prog_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack b : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs) :
    let s' := (Memory.spec 0).clientState s (fastShadowSteps8Prog (fl.pBase, b))
    let fm := extractFastMeta fl s.mem
    let fm' := extractFastMeta fl s'.mem
    s'.frontier = s.frontier ∧
    memoryCost (fastShadowSteps8Prog (fl.pBase, b)) s ≤
      8 * (360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree) ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    fm'.drainPos = fm.drainPos ∧
    fm'.tryAct = fm.tryAct ∧
    fm'.tryBkt = fm.tryBkt ∧
    fm'.trySalt = fm.trySalt ∧
    fm'.tryPos = fm.tryPos ∧
    fm'.tryIns = fm.tryIns ∧
    fm'.bktSalt = fm.bktSalt ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ b' ≠ b, fm'.curRole b' = fm.curRole b' ∧ fm'.curIns b' = fm.curIns b' ∧
      fm'.shadowIns b' = fm.shadowIns b' ∧ fm'.shadowCode b' = fm.shadowCode b') ∧
    (b < numBucketsWhp fl.N → fm'.shadowCode b ≠ 0 →
      let cnt := (extractBlockPool fl.mp s.mem).bktCount b
      4 * fm'.shadowIns b + 5 * (cnt - (fm'.shadowCode b - 1)) + 8 ≤
        20 * slabScale fl.N ^ 12 ∧
      8 * (fm'.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm'.shadowCode b - 1)) + 8 ≤
        4 * slabScale fl.N ^ 12) := by
  dsimp only
  -- Compose two `m`-step specs into a `2*m`-step spec
  have hcomp_step : ∀ (p : ℕ × ℕ → Memory.Prog Unit) (m : ℕ),
      (∀ (k : ℕ) (st : Memory.State),
        fl.Valid w st.frontier →
        FastEpochInvGen slackCur fl slack seeds st.mem s_abs →
        (b < numBucketsWhp fl.N → (extractFastMeta fl st.mem).shadowCode b ≠ 0 →
          let fm0 := extractFastMeta fl st.mem
          let cnt := (extractBlockPool fl.mp st.mem).bktCount b
          4 * fm0.shadowIns b + 5 * (cnt - (fm0.shadowCode b - 1)) + k ≤
            20 * slabScale fl.N ^ 12 ∧
          8 * (fm0.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm0.shadowCode b - 1)) + k ≤
            4 * slabScale fl.N ^ 12) →
        let st' := (Memory.spec 0).clientState st (p (fl.pBase, b))
        let fm0 := extractFastMeta fl st.mem
        let fm1 := extractFastMeta fl st'.mem
        st'.frontier = st.frontier ∧
        memoryCost (p (fl.pBase, b)) st ≤
          m * (360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree) ∧
        FastEpochInvGen slackCur fl slack seeds st'.mem s_abs ∧
        extractBlockPool fl.mp st'.mem = extractBlockPool fl.mp st.mem ∧
        fm1.curBufRole = fm0.curBufRole ∧ fm1.subStep = fm0.subStep ∧
        fm1.drainPos = fm0.drainPos ∧ fm1.tryAct = fm0.tryAct ∧
        fm1.tryBkt = fm0.tryBkt ∧ fm1.trySalt = fm0.trySalt ∧
        fm1.tryPos = fm0.tryPos ∧ fm1.tryIns = fm0.tryIns ∧
        fm1.bktSalt = fm0.bktSalt ∧
        (∀ r < 2, extractBufTrie (fl.trieL r) st'.mem = extractBufTrie (fl.trieL r) st.mem) ∧
        (∀ addr, fl.io.OwnsAddr addr → st'.mem addr = st.mem addr) ∧
        (∀ addr, ¬fl.OwnsFastAddr addr → st'.mem addr = st.mem addr) ∧
        (∀ b' ≠ b, fm1.curRole b' = fm0.curRole b' ∧ fm1.curIns b' = fm0.curIns b' ∧
          fm1.shadowIns b' = fm0.shadowIns b' ∧ fm1.shadowCode b' = fm0.shadowCode b') ∧
        (b < numBucketsWhp fl.N → fm1.shadowCode b ≠ 0 →
          let cnt := (extractBlockPool fl.mp st.mem).bktCount b
          4 * fm1.shadowIns b + 5 * (cnt - (fm1.shadowCode b - 1)) + (k + m) ≤
            20 * slabScale fl.N ^ 12 ∧
          8 * (fm1.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm1.shadowCode b - 1)) +
            (k + m) ≤ 4 * slabScale fl.N ^ 12)) →
      ∀ (k : ℕ) (st : Memory.State),
        fl.Valid w st.frontier →
        FastEpochInvGen slackCur fl slack seeds st.mem s_abs →
        (b < numBucketsWhp fl.N → (extractFastMeta fl st.mem).shadowCode b ≠ 0 →
          let fm0 := extractFastMeta fl st.mem
          let cnt := (extractBlockPool fl.mp st.mem).bktCount b
          4 * fm0.shadowIns b + 5 * (cnt - (fm0.shadowCode b - 1)) + k ≤
            20 * slabScale fl.N ^ 12 ∧
          8 * (fm0.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm0.shadowCode b - 1)) + k ≤
            4 * slabScale fl.N ^ 12) →
        let prog2 : Memory.Prog Unit := do p (fl.pBase, b); p (fl.pBase, b)
        let st' := (Memory.spec 0).clientState st prog2
        let fm0 := extractFastMeta fl st.mem
        let fm1 := extractFastMeta fl st'.mem
        st'.frontier = st.frontier ∧
        memoryCost prog2 st ≤
          (2 * m) * (360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree) ∧
        FastEpochInvGen slackCur fl slack seeds st'.mem s_abs ∧
        extractBlockPool fl.mp st'.mem = extractBlockPool fl.mp st.mem ∧
        fm1.curBufRole = fm0.curBufRole ∧ fm1.subStep = fm0.subStep ∧
        fm1.drainPos = fm0.drainPos ∧ fm1.tryAct = fm0.tryAct ∧
        fm1.tryBkt = fm0.tryBkt ∧ fm1.trySalt = fm0.trySalt ∧
        fm1.tryPos = fm0.tryPos ∧ fm1.tryIns = fm0.tryIns ∧
        fm1.bktSalt = fm0.bktSalt ∧
        (∀ r < 2, extractBufTrie (fl.trieL r) st'.mem = extractBufTrie (fl.trieL r) st.mem) ∧
        (∀ addr, fl.io.OwnsAddr addr → st'.mem addr = st.mem addr) ∧
        (∀ addr, ¬fl.OwnsFastAddr addr → st'.mem addr = st.mem addr) ∧
        (∀ b' ≠ b, fm1.curRole b' = fm0.curRole b' ∧ fm1.curIns b' = fm0.curIns b' ∧
          fm1.shadowIns b' = fm0.shadowIns b' ∧ fm1.shadowCode b' = fm0.shadowCode b') ∧
        (b < numBucketsWhp fl.N → fm1.shadowCode b ≠ 0 →
          let cnt := (extractBlockPool fl.mp st.mem).bktCount b
          4 * fm1.shadowIns b + 5 * (cnt - (fm1.shadowCode b - 1)) + (k + 2 * m) ≤
            20 * slabScale fl.N ^ 12 ∧
          8 * (fm1.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm1.shadowCode b - 1)) +
            (k + 2 * m) ≤ 4 * slabScale fl.N ^ 12) := by
    intro p m hp k st hv0 hi0 hsl0
    dsimp only
    obtain ⟨hfr1, hc1, hi1, hbp1, e1, e2, e3, e4, e5, e6, e7, e8, e9, htr1, hoi1, hof1, hne1,
      hs1⟩ := hp k st hv0 hi0 hsl0
    set st1 := (Memory.spec 0).clientState st (p (fl.pBase, b))
    obtain ⟨hfr2, hc2, hi2, hbp2, f1, f2, f3, f4, f5, f6, f7, f8, f9, htr2, hoi2, hof2, hne2,
      hs2⟩ := hp (k + m) st1 (hfr1.symm ▸ hv0) hi1 (by rwa [hbp1])
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
    refine ⟨hfr2.trans hfr1, ?_, hi2, hbp2.trans hbp1,
      f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4,
      f5.trans e5, f6.trans e6, f7.trans e7, f8.trans e8, f9.trans e9,
      fun r hr_lt => (htr2 r hr_lt).trans (htr1 r hr_lt),
      fun a ha => (hoi2 a ha).trans (hoi1 a ha),
      fun a ha => (hof2 a ha).trans (hof1 a ha),
      fun b' hb_ne =>
        ⟨(hne2 b' hb_ne).1.trans (hne1 b' hb_ne).1,
         (hne2 b' hb_ne).2.1.trans (hne1 b' hb_ne).2.1,
         (hne2 b' hb_ne).2.2.1.trans (hne1 b' hb_ne).2.2.1,
         (hne2 b' hb_ne).2.2.2.trans (hne1 b' hb_ne).2.2.2⟩,
      fun hb hsc => ?_⟩
    · change memoryCost (p (fl.pBase, b)) st + memoryCost (p (fl.pBase, b)) st1 ≤ _
      have : (2 * m) * (360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree) =
          m * (360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree) +
            m * (360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree) := by ring
      rw [this]; omega
    · obtain ⟨g1, g2⟩ := hs2 hb hsc
      rw [hbp1] at g1 g2
      have hkm : k + m + m = k + 2 * m := by ring
      rw [hkm] at g1 g2
      exact ⟨g1, g2⟩
  have h2 := hcomp_step fastShadowStepProg 1 (fun k st hv0 hi0 hsl0 => by
    simpa only [one_mul] using fastShadowStepProg_spec (b := b) (k := k) hv0 hi0 hsl0)
  have h4 := hcomp_step fastShadowSteps2Prog 2 h2
  have h8 := hcomp_step fastShadowSteps4Prog 4 h4
  have hsl_init : b < numBucketsWhp fl.N → (extractFastMeta fl s.mem).shadowCode b ≠ 0 →
      let fm := extractFastMeta fl s.mem
      let cnt := (extractBlockPool fl.mp s.mem).bktCount b
      4 * fm.shadowIns b + 5 * (cnt - (fm.shadowCode b - 1)) + 0 ≤ 20 * slabScale fl.N ^ 12 ∧
      8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm.shadowCode b - 1)) + 0 ≤
        4 * slabScale fl.N ^ 12 := by
    intro hb hsc
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsh_all, _, _⟩ := hinv.tiers
    obtain ⟨_, _, h3, h4_s, _⟩ := hsh_all b hb hsc
    exact ⟨by omega, by omega⟩
  unfold fastShadowSteps8Prog
  have h24 : 2 * 4 = 8 := rfl
  simpa only [Nat.zero_add, h24] using h8 0 s hv hinv hsl_init

/-- Parameterized `k`-slack version of `fastShadowSteps8Prog_spec`, tracking strict `+8` progress
from any starting slack `k`. -/
theorem fastShadowSteps8Prog_spec_slack {slackCur : ℕ} {fl : FastEpochLayout} {w slack b k : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hslack_in : b < numBucketsWhp fl.N → (extractFastMeta fl s.mem).shadowCode b ≠ 0 →
      let fm := extractFastMeta fl s.mem
      let cnt := (extractBlockPool fl.mp s.mem).bktCount b
      4 * fm.shadowIns b + 5 * (cnt - (fm.shadowCode b - 1)) + k ≤ 20 * slabScale fl.N ^ 12 ∧
      8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm.shadowCode b - 1)) + k ≤
        4 * slabScale fl.N ^ 12) :
    let s' := (Memory.spec 0).clientState s (fastShadowSteps8Prog (fl.pBase, b))
    let fm' := extractFastMeta fl s'.mem
    b < numBucketsWhp fl.N → fm'.shadowCode b ≠ 0 →
      let cnt := (extractBlockPool fl.mp s.mem).bktCount b
      4 * fm'.shadowIns b + 5 * (cnt - (fm'.shadowCode b - 1)) + (k + 8) ≤
        20 * slabScale fl.N ^ 12 ∧
      8 * (fm'.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm'.shadowCode b - 1)) + (k + 8) ≤
        4 * slabScale fl.N ^ 12 := by
  have step1 : ∀ (j : ℕ) (st : Memory.State),
      fl.Valid w st.frontier →
      FastEpochInvGen slackCur fl slack seeds st.mem s_abs →
      (b < numBucketsWhp fl.N → (extractFastMeta fl st.mem).shadowCode b ≠ 0 →
        let fm0 := extractFastMeta fl st.mem
        let cnt := (extractBlockPool fl.mp st.mem).bktCount b
        4 * fm0.shadowIns b + 5 * (cnt - (fm0.shadowCode b - 1)) + j ≤ 20 * slabScale fl.N ^ 12 ∧
        8 * (fm0.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm0.shadowCode b - 1)) + j ≤
          4 * slabScale fl.N ^ 12) →
      let st' := (Memory.spec 0).clientState st (fastShadowStepProg (fl.pBase, b))
      fl.Valid w st'.frontier ∧
      FastEpochInvGen slackCur fl slack seeds st'.mem s_abs ∧
      extractBlockPool fl.mp st'.mem = extractBlockPool fl.mp st.mem ∧
      (b < numBucketsWhp fl.N → (extractFastMeta fl st'.mem).shadowCode b ≠ 0 →
        let fm1 := extractFastMeta fl st'.mem
        let cnt := (extractBlockPool fl.mp st'.mem).bktCount b
        4 * fm1.shadowIns b + 5 * (cnt - (fm1.shadowCode b - 1)) + (j + 1) ≤
          20 * slabScale fl.N ^ 12 ∧
        8 * (fm1.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm1.shadowCode b - 1)) +
          (j + 1) ≤ 4 * slabScale fl.N ^ 12) := by
    intro j st hvs his hsj
    obtain ⟨hfr, _, hi', hbp', _, _, _, _, _, _, _, _, _, _, _, _, _, hsl'⟩ :=
      fastShadowStepProg_spec (b := b) (k := j) hvs his hsj
    exact ⟨hfr.symm ▸ hvs, hi', hbp', fun hb hsc => hbp'.symm ▸ hsl' hb hsc⟩
  have dbl : ∀ (p : ℕ × ℕ → Memory.Prog Unit) (m : ℕ),
      (∀ (j : ℕ) (st : Memory.State),
        fl.Valid w st.frontier →
        FastEpochInvGen slackCur fl slack seeds st.mem s_abs →
        (b < numBucketsWhp fl.N → (extractFastMeta fl st.mem).shadowCode b ≠ 0 →
          let fm0 := extractFastMeta fl st.mem
          let cnt := (extractBlockPool fl.mp st.mem).bktCount b
          4 * fm0.shadowIns b + 5 * (cnt - (fm0.shadowCode b - 1)) + j ≤
            20 * slabScale fl.N ^ 12 ∧
          8 * (fm0.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm0.shadowCode b - 1)) + j ≤
            4 * slabScale fl.N ^ 12) →
        let st' := (Memory.spec 0).clientState st (p (fl.pBase, b))
        fl.Valid w st'.frontier ∧
        FastEpochInvGen slackCur fl slack seeds st'.mem s_abs ∧
        extractBlockPool fl.mp st'.mem = extractBlockPool fl.mp st.mem ∧
        (b < numBucketsWhp fl.N → (extractFastMeta fl st'.mem).shadowCode b ≠ 0 →
          let fm1 := extractFastMeta fl st'.mem
          let cnt := (extractBlockPool fl.mp st'.mem).bktCount b
          4 * fm1.shadowIns b + 5 * (cnt - (fm1.shadowCode b - 1)) + (j + m) ≤
            20 * slabScale fl.N ^ 12 ∧
          8 * (fm1.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm1.shadowCode b - 1)) +
            (j + m) ≤ 4 * slabScale fl.N ^ 12)) →
      ∀ (j : ℕ) (st : Memory.State),
        fl.Valid w st.frontier →
        FastEpochInvGen slackCur fl slack seeds st.mem s_abs →
        (b < numBucketsWhp fl.N → (extractFastMeta fl st.mem).shadowCode b ≠ 0 →
          let fm0 := extractFastMeta fl st.mem
          let cnt := (extractBlockPool fl.mp st.mem).bktCount b
          4 * fm0.shadowIns b + 5 * (cnt - (fm0.shadowCode b - 1)) + j ≤
            20 * slabScale fl.N ^ 12 ∧
          8 * (fm0.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm0.shadowCode b - 1)) + j ≤
            4 * slabScale fl.N ^ 12) →
        let st' := (Memory.spec 0).clientState st (do p (fl.pBase, b); p (fl.pBase, b))
        fl.Valid w st'.frontier ∧
        FastEpochInvGen slackCur fl slack seeds st'.mem s_abs ∧
        extractBlockPool fl.mp st'.mem = extractBlockPool fl.mp st.mem ∧
        (b < numBucketsWhp fl.N → (extractFastMeta fl st'.mem).shadowCode b ≠ 0 →
          let fm1 := extractFastMeta fl st'.mem
          let cnt := (extractBlockPool fl.mp st'.mem).bktCount b
          4 * fm1.shadowIns b + 5 * (cnt - (fm1.shadowCode b - 1)) + (j + 2 * m) ≤
            20 * slabScale fl.N ^ 12 ∧
          8 * (fm1.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm1.shadowCode b - 1)) +
            (j + 2 * m) ≤ 4 * slabScale fl.N ^ 12) := by
    intro p m hp j st hvs his hsj
    obtain ⟨hv1, hi1, hbp1, hs1⟩ := hp j st hvs his hsj
    obtain ⟨hv2, hi2, hbp2, hs2⟩ := hp (j + m) _ hv1 hi1 hs1
    rw [StateTransitionSpec.clientState_bind]
    refine ⟨hv2, hi2, hbp2.trans hbp1, fun hb hsc => ?_⟩
    have h := hs2 hb hsc
    have hring : j + m + m = j + 2 * m := by omega
    rwa [hring] at h
  have s2 := dbl fastShadowStepProg 1 step1
  have s4 := dbl fastShadowSteps2Prog 2 s2
  have s8 := dbl fastShadowSteps4Prog 4 s4
  obtain ⟨_, _, hbp8, hsl8⟩ := s8 k s hv hinv hslack_in
  dsimp only
  intro hb hsc
  have h24 : 2 * 4 = 8 := rfl
  have hr := hsl8 hb hsc
  rw [hbp8, h24] at hr
  exact hr

/-- When `shadowCode b = 0`, `fastShadowSteps8Prog (fl.pBase, b)` is a pure no-op (`s' = s`). -/
theorem fastShadowSteps8Prog_eq_of_shadowZero {fl : FastEpochLayout} {b : ℕ} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) (hb : b < numBucketsWhp fl.N)
    (hsc0 : (extractFastMeta fl s.mem).shadowCode b = 0) :
    (Memory.spec 0).clientState s (fastShadowSteps8Prog (fl.pBase, b)) = s := by
  have hstep : (Memory.spec 0).clientState s (fastShadowStepProg (fl.pBase, b)) = s := by
    unfold fastShadowStepProg; dsimp only
    have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
    have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
        numBucketsWhp fl.N := hpt 11 (by decide)
    have hsc_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 15))) = 0 := by
      rw [clientResult_fastReadBktLaneProg hpt hb (by decide)]
      have heq := hsc0
      unfold extractFastMeta at heq; dsimp only at heq
      rwa [ite_eq_left hb] at heq
    rw [StateTransitionSpec.clientState_bind, hr11_st, hr11_r,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg, hsc_r,
      ite_eq_right (fun ⟨_, hne⟩ => hne rfl)]
    rfl
  have h2 : (Memory.spec 0).clientState s (fastShadowSteps2Prog (fl.pBase, b)) = s := by
    unfold fastShadowSteps2Prog; rw [StateTransitionSpec.clientState_bind, hstep, hstep]
  have h4 : (Memory.spec 0).clientState s (fastShadowSteps4Prog (fl.pBase, b)) = s := by
    unfold fastShadowSteps4Prog; rw [StateTransitionSpec.clientState_bind, h2, h2]
  unfold fastShadowSteps8Prog; rw [StateTransitionSpec.clientState_bind, h4, h4]

/-- After `fastInitZeroedProg` on a zeroed header `[metaBase + 1, metaBase + 32) = 0`, all
scalar fast-meta fields (`curBufRole`, `subStep`, `drainPos`, `tryAct`) remain `0`. -/
theorem fastInitZeroedProg_hdr_zero {fl : FastEpochLayout} {w : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s)
    (hzero_hdr : ∀ k, 1 ≤ k → k < 32 → s.mem (fl.metaBase + k) = 0) :
    let s' := (Memory.spec 0).clientState s (fastInitZeroedProg fl.pBase)
    ∀ k, 2 ≤ k → k < 10 → s'.mem (fl.metaBase + k) = 0 := by
  dsimp only
  have hv := hr.1
  have hmv := hv.mp_valid
  obtain ⟨_, hr₁, _, hout₁⟩ := fastBpInitProg_ready hr
  obtain ⟨_, hr₂, _, hres₂⟩ := fastBufInitEmptyProg_ready (role := 0) hr₁
  obtain ⟨_, hout₂⟩ := hres₂ (by decide)
  obtain ⟨_, _, _, hres₃⟩ := fastBufInitEmptyProg_ready (role := 1) hr₂
  obtain ⟨_, hout₃⟩ := hres₃ (by decide)
  intro k hk2 hk10
  have ho_lo : fl.metaBase ≤ fl.metaBase + k := by omega
  have ho_hi : fl.metaBase + k < fl.metaBase + offTrieChild fl.c fl.w fl.N 0 := by
    have h32 : 32 ≤ offBktMeta fl.c fl.w fl.N := hmv.offBktMeta_ge
    have hle : offBktMeta fl.c fl.w fl.N ≤ offTrieChild fl.c fl.w fl.N 0 := by
      unfold offTrieChild offBTreeVals offBTreeKeys offBTreeMeta offTailOwner
        offSlabOwner offTailDir offSlabDir; omega
    omega
  have hn0 : ¬(fl.trieL 0).OwnsAddr (fl.metaBase + k) := fun ht =>
    fl.disj_trie_bpAndMeta hv (by decide) ht (Or.inl ⟨ho_lo, ho_hi⟩)
  have hn1 : ¬(fl.trieL 1).OwnsAddr (fl.metaBase + k) := fun ht =>
    fl.disj_trie_bpAndMeta hv (by decide) ht (Or.inl ⟨ho_lo, ho_hi⟩)
  have hnbp : ¬fl.mp.OwnsMetaAddr (fl.metaBase + k) := fun hm => by
    have h32 : 32 ≤ offBktMeta fl.c fl.w fl.N := hmv.offBktMeta_ge
    rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hm with (he | ⟨h10, _⟩) | ⟨hlo, _⟩ <;>
      (dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at *; omega)
  unfold fastInitZeroedProg
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    hout₃ _ hn1, hout₂ _ hn0, hout₁ _ hnbp]
  exact hzero_hdr k (by omega) (by omega)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
