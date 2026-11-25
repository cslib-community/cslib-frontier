/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeTrieProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBTreeProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFallback
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Large-Epoch 64-Word Parameter Table, `FastEpochInv`, and Read-Only `fastQueryProg`

This module defines the `pBase` 64-word `EpochParamTable` layout (`FastEpochLayout`), constant-time
read-only context loaders (`loadBpMetaCtxProg`, `loadSlotIoCtxProg`, `loadHashStaticCtxProg`,
`loadTrieCtxProg`, `loadBTreeSliceCtxProg`), guarded Stage-1/Stage-2 hash evaluators
(`fastFeistelSplitProg`, `fastFeistelReconProg`, `fastRKeyProg`, `fastFpHashProg`), scalar and
per-bucket lane (`5, 12..15`) accessors, the 3-tier `FastEpochInv` coupling (`BufCur`, `BufOld`,
`BTree(b, curRole b)`, shadow compaction, and `trySalt` search), and the exact read-only
`fastProbeProg` / `fastQueryProg` operations for the deamortized worst-case WHP resizable succinct
dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]).

Because every static epoch parameter is cached in the 64-word `[pBase, pBase + 64)` header block,
every `FastEpoch` `Memory.Prog` takes at most three `ℕ` register arguments (`pBase` plus key/value
words), eliminating wide-tuple register marshalling and keeping `RealizesBounded .exact`
verification uniform under `FastProgPre`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]
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
open Cslib.DataStructure.HashFamily Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.Probability

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: `FastEpochLayout`, 64-Word `paramWord`, and `FastLayoutReady` -/

/-- Named memory layout descriptor for a large hashed epoch (`whpThreshold c ≤ N ≤ U < 2 ^ w`)
whose 64-word static parameter table lives at `[pBase, pBase + 64)` (`0` projection chains). -/
structure FastEpochLayout where
  /-- Failure probability exponent `c`. -/
  c : ℕ
  /-- Key universe `U` (`0 < N ≤ U < 2 ^ w`). -/
  U : ℕ
  /-- Value universe `V` (`0 < V ≤ 2 ^ w`). -/
  V : ℕ
  /-- Machine word bit-width `w`. -/
  w : ℕ
  /-- Epoch capacity `N` (`whpThreshold c ≤ N`). -/
  N : ℕ
  /-- Base word address of this epoch's `[0, epochMetaWordsWhp c w N)` metadata region. -/
  metaBase : ℕ
  /-- Base word address of this epoch's 64-word static parameter block `[pBase, pBase + 64)`. -/
  pBase : ℕ
  /-- Underlying `[0, nSide)` pair-slot descriptor (`usePaged = 0` or `usePaged ≠ 0`). -/
  io : SlotIoLayout

namespace FastEpochLayout

/-- Underlying `BpMetaLayout` at `metaBase`. -/
@[expose] def mp (fl : FastEpochLayout) : BpMetaLayout :=
  epochBpMetaLayout fl.c fl.w fl.N fl.metaBase

/-- Underlying `BlockPoolLayout` pairing `fl.mp` with `fl.io`. -/
@[expose] def bpL (fl : FastEpochLayout) : BlockPoolLayout :=
  ⟨fl.mp, fl.io⟩

/-- Underlying `FallbackLayout` sharing `fl.bpL` when `fallbackMode = 1`. -/
@[expose] def fbL (fl : FastEpochLayout) : FallbackLayout :=
  ⟨fl.c, fl.U, fl.V, fl.bpL⟩

/-- Underlying 3-role SWAR B+-tree layout `epochBTreeLayout`. -/
@[expose] def btL (fl : FastEpochLayout) : BTreeEpochLayout :=
  epochBTreeLayout fl.c fl.w fl.N fl.metaBase

/-- Underlying `BufTrie` layout for role `role ∈ {0, 1}`. -/
@[expose] def trieL (fl : FastEpochLayout) (role : ℕ) : TrieLayout :=
  epochTrieLayout fl.c fl.w fl.N fl.metaBase role

/-- Base word address `metaBase + offBktHash` of the Feistel bucket hash seed. -/
@[expose] def bktHashBase (fl : FastEpochLayout) : ℕ :=
  fl.metaBase + offBktHash

/-- Base word address `metaBase + offFpHash` of the salted fingerprint & `rKey` hash seed. -/
@[expose] def fpHashBase (fl : FastEpochLayout) : ℕ :=
  fl.metaBase + offFpHash fl.c fl.w fl.N

/-- Shared bottom-table offset `offBot` for `BitPackedDoubleTabulation` in epoch `fl`. -/
@[expose] def dtOffBot (fl : FastEpochLayout) : ℕ :=
  BitPackedDoubleTabulation.offBot fl.w (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N)

/-- Canonical `FeistelHashCtx` for epoch `fl`. -/
@[expose] def feistelCtx (fl : FastEpochLayout) : FeistelHashCtx :=
  (((fl.bktHashBase, fl.dtOffBot), (fl.w, redWidthWhp fl.U)),
    ((redBitsWhp fl.c fl.N, cTabWhp fl.c), (dTabWhp fl.c, (bCharWhp fl.N, bWhp fl.N))))

/-- Canonical `FpHash` static context (9 words before `(salt, u_val)`). -/
@[expose] def fpStaticCtx (fl : FastEpochLayout) : FeistelHashCtx :=
  (((fl.fpHashBase, fl.dtOffBot), (fl.w, redWidthWhp fl.U)),
    ((redBitsWhp fl.c fl.N, cTabWhp fl.c), (dTabWhp fl.c, (bCharWhp fl.N, fpBitsWhp fl.N))))

/-- Exact word value at index `k < 64` of the 64-word `EpochParamTable` at `pBase`. -/
@[expose] def paramWord (fl : FastEpochLayout) : ℕ → ℕ
  | 0 => fl.N
  | 1 => fl.metaBase
  | 2 => fl.w
  | 3 => redWidthWhp fl.U
  | 4 => redBitsWhp fl.c fl.N
  | 5 => cTabWhp fl.c
  | 6 => dTabWhp fl.c
  | 7 => bCharWhp fl.N
  | 8 => bWhp fl.N
  | 9 => fpBitsWhp fl.N
  | 10 => globalPtrBits fl.N
  | 11 => numBucketsWhp fl.N
  | 12 => slabSizeWhp fl.N
  | 13 => maxSlabsPerBktWhp fl.N
  | 14 => fl.N / slabSizeWhp fl.N + 4
  | 15 => maxTailWhp fl.N
  | 16 => nodeMetaBitsWhp fl.N
  | 17 => keysWordBitsWhp fl.N
  | 18 => valsWordBitsWhp fl.N
  | 19 => valLaneBitsWhp fl.N
  | 20 => tMinWhp fl.N
  | 21 => nSliceWhp fl.N
  | 22 => maxTrieNodesWhp fl.c fl.N
  | 23 => qEpochWhp fl.N
  | 24 => sMaxWhp fl.c fl.N
  | 25 => capMaxWhp fl.N
  | 26 => 6 * slabScale fl.N ^ 12
  | 27 => 8 * slabScale fl.N ^ 12
  | 28 => 4 * (cTabWhp fl.c + 2)
  | 29 => fl.dtOffBot
  | 30 => offFpHash fl.c fl.w fl.N
  | 31 => offBktMeta fl.c fl.w fl.N
  | 32 => offSlabDir fl.c fl.w fl.N
  | 33 => offTailDir fl.c fl.w fl.N
  | 34 => offSlabOwner fl.c fl.w fl.N
  | 35 => offTailOwner fl.c fl.w fl.N
  | 36 => offBTreeMeta fl.c fl.w fl.N
  | 37 => offBTreeKeys fl.c fl.w fl.N
  | 38 => offBTreeVals fl.c fl.w fl.N
  | 39 => offTrieChild fl.c fl.w fl.N 0
  | 40 => offTrieChild fl.c fl.w fl.N 1
  | 41 => offTrieNode fl.c fl.w fl.N 0
  | 42 => offTrieNode fl.c fl.w fl.N 1
  | 43 => offTrieItem fl.c fl.w fl.N 0
  | 44 => offTrieItem fl.c fl.w fl.N 1
  | 45 => epochMetaWordsWhp fl.c fl.w fl.N
  | 46 => fl.U - 1
  | 47 => fl.V - 1
  | 48 => fl.io.usePaged
  | 49 => fl.io.sideBit
  | 50 => fl.io.pgL.metaBase
  | 51 => fl.io.pgL.offDir
  | 52 => fl.io.pgL.offTail
  | 53 => fl.io.pgL.ptrB
  | 54 => fl.io.pgL.w
  | 55 => fl.io.pgL.pgB
  | 56 => fl.io.pgL.maxPages
  | 57 => fl.io.pgL.itemBase
  | 58 => fl.io.pgL.qBits
  | 59 => fl.io.pgL.vBits
  | 60 => fl.io.pgL.nCap
  | 61 => fl.bktHashBase
  | 62 => fl.fpHashBase
  | _ => 0

/-- Memory `mem` stores `fl.paramWord k` across `[fl.pBase, fl.pBase + 63)`. -/
@[expose] def ParamTable (fl : FastEpochLayout) (mem : ℕ → ℕ) : Prop :=
  ∀ k < 63, mem (fl.pBase + k) = fl.paramWord k

theorem ParamTable.congr {fl : FastEpochLayout} {mem₁ mem₂ : ℕ → ℕ}
    (h : fl.ParamTable mem₁)
    (heq : ∀ addr, fl.pBase ≤ addr → addr < fl.pBase + 63 → mem₂ addr = mem₁ addr) :
    fl.ParamTable mem₂ := fun k hk =>
  (heq (fl.pBase + k) (Nat.le_add_right _ _) (by omega)).trans (h k hk)

/-- Word-address footprint mutable by `FastEpoch` or `FallbackPool` operations (`scalars 0..17`
except `0`, non-seed tables `[offBktMeta, offPageDir)`, plus `fl.io.OwnsAddr`). Note that
`[pBase, pBase + 64)`, `metaBase + 0`, `[metaBase + 18, metaBase + 32)`, and the active hash seeds
`[metaBase + offBktHash, metaBase + offBktMeta)` are strictly outside `OwnsFastAddr`! -/
@[expose] def OwnsFastAddr (fl : FastEpochLayout) (addr : ℕ) : Prop :=
  (fl.metaBase + 1 ≤ addr ∧ addr < fl.metaBase + 18) ∨
  (fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr ∧
    addr < fl.metaBase + offPageDir fl.c fl.w fl.N) ∨
  fl.io.OwnsAddr addr

/-- Static frontier and parameter validity for `FastEpochLayout` (`0` projection chains). -/
structure Valid (fl : FastEpochLayout) (w_mach frontier : ℕ) : Prop where
  thresh_le : whpThreshold fl.c ≤ fl.N
  N_le_U : fl.N ≤ fl.U
  fits_U : Fits w_mach fl.U
  V_pos : 0 < fl.V
  V_le_pow : fl.V ≤ 2 ^ w_mach
  w_eq : w_mach = fl.w
  redWidth_le : redWidthWhp fl.U ≤ w_mach
  pBase_lt_meta : fl.pBase + 64 ≤ fl.metaBase
  meta_frontier : fl.metaBase + epochMetaWordsWhp fl.c fl.w fl.N ≤ frontier
  io_valid : fl.io.Valid w_mach frontier
  w_eq_io : fl.w = fl.io.pgL.w
  qBits_le : quotBitsWhp fl.U fl.N ≤ fl.io.pgL.qBits
  vBits_eq : fl.io.pgL.vBits = valBits fl.V
  disj_pBase_io : ∀ addr, fl.pBase ≤ addr → addr < fl.pBase + 64 → ¬fl.io.OwnsAddr addr
  disj_fast_io : ∀ addr,
    ((fl.metaBase ≤ addr ∧ addr < fl.metaBase + 18) ∨
      (fl.metaBase + 32 ≤ addr ∧ addr < fl.metaBase + offPageDir fl.c fl.w fl.N)) →
    ¬fl.io.OwnsAddr addr

theorem Valid.mp_valid {fl : FastEpochLayout} {w fr : ℕ} (hv : fl.Valid w fr) :
    fl.mp.Valid w fr := by
  have h := valid_epochBpMetaLayout hv.thresh_le hv.N_le_U (hv.w_eq ▸ hv.fits_U) hv.meta_frontier
  cases hv.w_eq
  exact h

theorem Valid.bt_valid {fl : FastEpochLayout} {w fr : ℕ} (hv : fl.Valid w fr) :
    fl.btL.Valid fl.w fr :=
  valid_epochBTreeLayout hv.thresh_le hv.N_le_U (hv.w_eq ▸ hv.fits_U) hv.meta_frontier

theorem Valid.trie_valid {fl : FastEpochLayout} {w fr role : ℕ} (hv : fl.Valid w fr)
    (hrole : role < 2) : (fl.trieL role).Valid fl.w fr :=
  valid_epochTrieLayout hv.thresh_le hv.N_le_U (hv.w_eq ▸ hv.fits_U) hrole hv.meta_frontier

theorem Valid.w_ge_six {fl : FastEpochLayout} {w fr : ℕ} (hv : fl.Valid w fr) : 6 ≤ w := by
  have hb := hv.bt_valid
  have h8 := hb.2.2.2.1
  have h4k := hb.2.2.2.2.2.2.2.2.2.1
  have hw := hv.w_eq
  nlinarith

theorem Valid.w_pos {fl : FastEpochLayout} {w fr : ℕ} (hv : fl.Valid w fr) : 0 < w := by
  have := hv.w_ge_six; omega

theorem Valid.bp_valid {fl : FastEpochLayout} {w fr : ℕ} (hv : fl.Valid w fr) :
    fl.bpL.Valid w fr where
  mp_valid := hv.mp_valid
  io_valid := hv.io_valid
  w_eq_io := hv.w_eq_io
  disjoint addr hma hia := by
    have hmv := hv.mp_valid
    have hend := offEpochEnd_eq_epochMetaWordsWhp (c := fl.c) (w := fl.w) hv.thresh_le
    rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (rfl | ⟨h10, h17⟩) | ⟨hlo, hhi⟩
    · exact hv.disj_fast_io _ (Or.inl ⟨by dsimp [mp, epochBpMetaLayout]; omega,
        by dsimp [mp, epochBpMetaLayout]; omega⟩) hia
    · exact hv.disj_fast_io _ (Or.inl ⟨by dsimp [mp, epochBpMetaLayout] at *; omega,
        by dsimp [mp, epochBpMetaLayout] at *; omega⟩) hia
    · refine hv.disj_fast_io addr (Or.inr ⟨?_, ?_⟩) hia
      · dsimp only [mp, epochBpMetaLayout] at hlo
        have := hmv.offBktMeta_ge; dsimp only [mp, epochBpMetaLayout] at this; omega
      · dsimp only [mp, epochBpMetaLayout] at hhi
        unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
          offBTreeMeta
        omega

theorem Valid.fb_valid {fl : FastEpochLayout} {w fr : ℕ} (hv : fl.Valid w fr) :
    fl.fbL.Valid w fr where
  bp_valid := hv.bp_valid
  mp_eq := hv.w_eq ▸ rfl
  thresh_le := hv.thresh_le
  N_le_U := hv.N_le_U
  fits_U := hv.fits_U
  V_le_pow := hv.V_le_pow
  qBits_le := hv.qBits_le
  vBits_eq := hv.vBits_eq
  disjoint_hdr2 addr h2 hia := by
    rcases h2 with rfl | rfl
    · exact hv.disj_fast_io _ (Or.inl ⟨by dsimp [fbL, bpL, mp, epochBpMetaLayout]; omega,
        by dsimp [fbL, bpL, mp, epochBpMetaLayout]; omega⟩) hia
    · exact hv.disj_fast_io _ (Or.inl ⟨by dsimp [fbL, bpL, mp, epochBpMetaLayout]; omega,
        by dsimp [fbL, bpL, mp, epochBpMetaLayout]; omega⟩) hia
  disjoint_seeds addr hlo hhi hia := by
    cases hv.w_eq
    refine hv.disj_fast_io addr (Or.inr ⟨?_, ?_⟩) hia
    · unfold offBktHash at hlo
      try dsimp only [fbL, bpL, mp, epochBpMetaLayout] at hlo
      omega
    · try dsimp only [fbL, FallbackLayout.N, bpL, mp, epochBpMetaLayout] at hhi
      unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
        offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
      omega

theorem Valid.not_ownsFast_pBase {fl : FastEpochLayout} {w fr addr : ℕ}
    (hv : fl.Valid w fr) (hlo : fl.pBase ≤ addr) (hhi : addr < fl.pBase + 64) :
    ¬fl.OwnsFastAddr addr := by
  have hp := hv.pBase_lt_meta
  rintro (h1 | h2 | hio)
  · omega
  · omega
  · exact hv.disj_pBase_io addr hlo hhi hio

theorem Valid.not_ownsFast_hdr0 {fl : FastEpochLayout} {w fr : ℕ} (hv : fl.Valid w fr) :
    ¬fl.OwnsFastAddr fl.metaBase := by
  rintro (h1 | h2 | hio)
  · omega
  · have := hv.mp_valid.offBktMeta_ge; dsimp [mp, epochBpMetaLayout] at this; omega
  · exact hv.disj_fast_io fl.metaBase (Or.inl ⟨le_rfl, by omega⟩) hio

theorem Valid.not_ownsFast_seeds {fl : FastEpochLayout} {w fr addr : ℕ}
    (hv : fl.Valid w fr)
    (hlo : fl.metaBase + offBktHash ≤ addr)
    (hhi : addr < fl.metaBase + offBktMeta fl.c fl.w fl.N) :
    ¬fl.OwnsFastAddr addr := by
  rintro (h1 | h2 | hio)
  · unfold offBktHash at hlo; omega
  · omega
  · refine hv.disj_fast_io addr (Or.inr ⟨by unfold offBktHash at hlo; omega, ?_⟩) hio
    unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
      offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
    omega

theorem Valid.fbOwns_sub_fastOwns {fl : FastEpochLayout} {w fr addr : ℕ}
    (hv : fl.Valid w fr) (ha : fl.fbL.OwnsAddr addr) : fl.OwnsFastAddr addr := by
  rcases ha with rfl | hma | hia
  · exact Or.inl ⟨by dsimp [fbL, bpL, mp, epochBpMetaLayout]; omega,
      by dsimp [fbL, bpL, mp, epochBpMetaLayout]; omega⟩
  · rcases BpMetaLayout.OwnsMetaAddr.bounds hv.mp_valid hma with (rfl | ⟨h10, h17⟩) | ⟨hlo, hhi⟩
    · exact Or.inl ⟨by dsimp [mp, epochBpMetaLayout]; omega,
        by dsimp [mp, epochBpMetaLayout]; omega⟩
    · exact Or.inl ⟨by dsimp [mp, epochBpMetaLayout] at *; omega,
        by dsimp [mp, epochBpMetaLayout] at *; omega⟩
    · refine Or.inr (Or.inl ⟨hlo, ?_⟩)
      dsimp only [mp, epochBpMetaLayout] at hhi
      unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
        offBTreeMeta
      omega
  · exact Or.inr (Or.inr hia)

end FastEpochLayout

/-- Runtime readiness invariant for `RealizesBounded .exact` on `FastEpoch` programs: combines
`fl.Valid w s.frontier`, `fl.ParamTable s.mem`, and valid Stage-1 odd-multiplier bounds at the two
seed base addresses. Preserved automatically across any `OwnsFastAddr` mutation! -/
@[expose] def FastLayoutReady (w : ℕ) (fl : FastEpochLayout) (s : Memory.State) : Prop :=
  fl.Valid w s.frontier ∧
  fl.ParamTable s.mem ∧
  s.mem fl.bktHashBase < 2 ^ (redWidthWhp fl.U - 1) ∧
  s.mem fl.fpHashBase < 2 ^ (redWidthWhp fl.U - 1)

theorem FastLayoutReady.of_frame {w : ℕ} {fl : FastEpochLayout} {s s' : Memory.State}
    (hr : FastLayoutReady w fl s) (hfr : s'.frontier = s.frontier)
    (hout : ∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) :
    FastLayoutReady w fl s' := by
  obtain ⟨hv, hpt, hbkt, hfp⟩ := hr
  have hsp_bkt := BitPackedDoubleTabulation.space_pos fl.w (cTabWhp fl.c) (dTabWhp fl.c)
    (bCharWhp fl.N) (bWhp fl.N)
  have hsp_fp := BitPackedDoubleTabulation.space_pos fl.w (cTabWhp fl.c) (dTabWhp fl.c)
    (bCharWhp fl.N) (fpBitsWhp fl.N)
  have hbkt_eq : s'.mem fl.bktHashBase = s.mem fl.bktHashBase :=
    hout _ (hv.not_ownsFast_seeds (by unfold FastEpochLayout.bktHashBase; omega)
      (by unfold FastEpochLayout.bktHashBase offBktMeta offFpHash; omega))
  have hfp_eq : s'.mem fl.fpHashBase = s.mem fl.fpHashBase :=
    hout _ (hv.not_ownsFast_seeds
      (by unfold FastEpochLayout.fpHashBase offFpHash; omega)
      (by unfold FastEpochLayout.fpHashBase offBktMeta; omega))
  refine ⟨hfr.symm ▸ hv, hpt.congr fun a h1 h2 =>
    hout a (hv.not_ownsFast_pBase h1 (by omega)), hbkt_eq ▸ hbkt, hfp_eq ▸ hfp⟩

/-- Uniform `RealizesBounded` precondition parameterized solely by `(w, pBase, s)`. -/
@[expose] def FastProgPre (w : ℕ) (pBase : ℕ) (s : Memory.State) : Prop :=
  ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ FastLayoutReady w fl s

theorem FastProgPre.pBase_bound {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    6 ≤ w ∧ pBase + 64 ≤ s.frontier := by
  obtain ⟨fl, rfl, hv, _, _, _⟩ := h
  exact ⟨hv.w_ge_six, hv.pBase_lt_meta.trans (le_trans (Nat.le_add_right _ _) hv.meta_frontier)⟩

/-! ## Section 2: Read-Only `O(1)` Context Loaders and Guarded Hash Evaluators -/

private def readParamPairProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (pBase, (k₁, k₂)) => do
    let v₁ ← Memory.read (pBase + k₁)
    let v₂ ← Memory.read (pBase + k₂)
    pure (v₁, v₂)

@[simp] private theorem runClient_state_readParamPairProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (readParamPairProg x)).2.1 = s := by
  rcases x with ⟨_, ⟨_, _⟩⟩; rfl

private theorem realizesBounded_readParamPair :
    RealizesBounded .exact readParamPairProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (pBase, (k₁, k₂)) s =>
        6 ≤ w ∧ pBase + 64 ≤ s.frontier ∧ k₁ < 64 ∧ k₂ < 64)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨pBase, ⟨k₁, k₂⟩⟩
    obtain ⟨hw6, hp, hk1, hk2⟩ := h
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    omega)

private def readParamQuadProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((pBase, p₁), p₂) => do
    let q₁ ← readParamPairProg (pBase, p₁)
    let q₂ ← readParamPairProg (pBase, p₂)
    pure (q₁, q₂)

@[simp] private theorem runClient_state_readParamQuadProg
    (x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (readParamQuadProg x)).2.1 = s := by
  rcases x with ⟨⟨_, ⟨_, _⟩⟩, ⟨_, _⟩⟩; rfl

private theorem realizesBounded_readParamQuad :
    RealizesBounded .exact readParamQuadProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (fun w ((pBase, (k₁, k₂)), (k₃, k₄)) s =>
        6 ≤ w ∧ pBase + 64 ≤ s.frontier ∧ k₁ < 64 ∧ k₂ < 64 ∧ k₃ < 64 ∧ k₄ < 64)
      (fun _ _ => 0) := by
  have hrp := realizesBounded_readParamPair
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨k₁, k₂⟩⟩, ⟨k₃, k₄⟩⟩
    obtain ⟨hw6, hp, hk1, hk2, hk3, hk4⟩ := h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readParamPairProg] at *
    omega)

/-- Load `BpMetaCtx` (14 words) from `pBase` (`14` reads, `0` writes, `¬ReadsWidth`). -/
def loadBpMetaCtxProg (pBase : ℕ) : Memory.Prog BpMetaCtx := do
  let q1 ← readParamQuadProg ((pBase, (1, 31)), (32, 33))
  let q2 ← readParamQuadProg ((pBase, (34, 35)), (10, 2))
  let q3 ← readParamQuadProg ((pBase, (11, 12)), (13, 14))
  let p4 ← readParamPairProg (pBase, (15, 0))
  pure ((q1, q2), (q3, p4))

@[simp] theorem runClient_state_loadBpMetaCtxProg (pBase : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (loadBpMetaCtxProg pBase)) = s := by
  unfold loadBpMetaCtxProg; simp

theorem clientState_loadBpMetaCtxProg (pBase : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadBpMetaCtxProg pBase) = s :=
  runClient_state_loadBpMetaCtxProg pBase s

theorem memoryCost_loadBpMetaCtxProg (pBase : ℕ) (s : Memory.State) :
    memoryCost (loadBpMetaCtxProg pBase) s = 14 := by
  unfold loadBpMetaCtxProg readParamQuadProg readParamPairProg; simp

theorem clientResult_loadBpMetaCtxProg {fl : FastEpochLayout} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) :
    (Memory.spec 0).clientResult s (loadBpMetaCtxProg fl.pBase) = fl.mp.toCtx := by
  unfold loadBpMetaCtxProg readParamQuadProg readParamPairProg
  simp only [prog_clientResult_bind, prog_runClient_state_bind, prog_runClient_state_read,
    prog_clientResult_read, prog_clientResult_pure, prog_runClient_state_pure]
  repeat rw [hpt _ (by decide)]
  rfl

theorem realizesBounded_loadBpMetaCtx :
    RealizesBounded .exact loadBpMetaCtxProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := BpMetaCtx))
      (fun w pBase s => 6 ≤ w ∧ pBase + 64 ≤ s.frontier) (fun _ _ => 0) := by
  have hrq := realizesBounded_readParamQuad
  have hrp := realizesBounded_readParamPair
  realize
  all_goals (
    obtain ⟨hw6, hp⟩ := h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readParamQuadProg] at *
    first | exact hw6 | exact hp | omega)

/-- Load `SlotIoCtx` (13 words) from `pBase + 48..60` (`13` reads, `0` writes, `¬ReadsWidth`). -/
def loadSlotIoCtxProg (pBase : ℕ) : Memory.Prog SlotIoCtx := do
  let hdr ← readParamPairProg (pBase, (48, 49))
  let q1 ← readParamQuadProg ((pBase, (50, 51)), (52, 53))
  let q2 ← readParamQuadProg ((pBase, (54, 55)), (56, 57))
  let p3 ← readParamPairProg (pBase, (58, 59))
  let nc ← Memory.read (pBase + 60)
  pure (hdr, ((q1, q2), (p3, nc)))

@[simp] theorem runClient_state_loadSlotIoCtxProg (pBase : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (loadSlotIoCtxProg pBase)) = s := by
  unfold loadSlotIoCtxProg; simp

theorem clientState_loadSlotIoCtxProg (pBase : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadSlotIoCtxProg pBase) = s :=
  runClient_state_loadSlotIoCtxProg pBase s

theorem memoryCost_loadSlotIoCtxProg (pBase : ℕ) (s : Memory.State) :
    memoryCost (loadSlotIoCtxProg pBase) s = 13 := by
  unfold loadSlotIoCtxProg readParamQuadProg readParamPairProg; simp

theorem clientResult_loadSlotIoCtxProg {fl : FastEpochLayout} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) :
    (Memory.spec 0).clientResult s (loadSlotIoCtxProg fl.pBase) = fl.io.toCtx := by
  unfold loadSlotIoCtxProg readParamQuadProg readParamPairProg
  simp only [prog_clientResult_bind, prog_runClient_state_bind, prog_runClient_state_read,
    prog_clientResult_read, prog_clientResult_pure, prog_runClient_state_pure]
  repeat rw [hpt _ (by decide)]
  rfl

theorem realizesBounded_loadSlotIoCtx :
    RealizesBounded .exact loadSlotIoCtxProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := SlotIoCtx))
      (fun w pBase s => 6 ≤ w ∧ pBase + 64 ≤ s.frontier) (fun _ _ => 0) := by
  have hrq := realizesBounded_readParamQuad
  have hrp := realizesBounded_readParamPair
  realize
  all_goals (
    obtain ⟨hw6, hp⟩ := h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_readParamQuadProg,
      runClient_state_readParamPairProg] at *
    first | exact hw6 | exact hp | omega)

/-- Load `BlockPoolCtx` from `pBase` (`27` reads, `0` writes, `¬ReadsWidth`). -/
def loadBlockPoolCtxProg (pBase : ℕ) : Memory.Prog BlockPoolCtx := do
  let mctx ← loadBpMetaCtxProg pBase
  let ioctx ← loadSlotIoCtxProg pBase
  pure (mctx, ioctx)

@[simp] theorem runClient_state_loadBlockPoolCtxProg (pBase : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (loadBlockPoolCtxProg pBase)) = s := by
  unfold loadBlockPoolCtxProg; simp

theorem clientState_loadBlockPoolCtxProg (pBase : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadBlockPoolCtxProg pBase) = s :=
  runClient_state_loadBlockPoolCtxProg pBase s

theorem memoryCost_loadBlockPoolCtxProg (pBase : ℕ) (s : Memory.State) :
    memoryCost (loadBlockPoolCtxProg pBase) s = 27 := by
  unfold loadBlockPoolCtxProg
  rw [Realization.memoryCost_bind', memoryCost_loadBpMetaCtxProg, clientState_loadBpMetaCtxProg,
    Realization.memoryCost_bind', memoryCost_loadSlotIoCtxProg, clientState_loadSlotIoCtxProg,
    memoryCost_pure]

theorem clientResult_loadBlockPoolCtxProg {fl : FastEpochLayout} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) :
    (Memory.spec 0).clientResult s (loadBlockPoolCtxProg fl.pBase) = fl.bpL.toCtx :=
  Prod.ext (clientResult_loadBpMetaCtxProg hpt) (clientResult_loadSlotIoCtxProg hpt)

theorem realizesBounded_loadBlockPoolCtx :
    RealizesBounded .exact loadBlockPoolCtxProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := BlockPoolCtx))
      (fun w pBase s => 6 ≤ w ∧ pBase + 64 ≤ s.frontier) (fun _ _ => 0) := by
  have hm := realizesBounded_loadBpMetaCtx
  have hio := realizesBounded_loadSlotIoCtx
  realize
  all_goals (
    obtain ⟨hw6, hp⟩ := h
    try simp only [StateTransitionSpec.clientState, runClient_state_loadBpMetaCtxProg] at *
    first | exact hw6 | exact hp)

/-- Load `FeistelHashCtx` (for `bktHash`, `isFp = 0`) or `fpStaticCtx` (for `fpHash`, `isFp ≠ 0`)
from `(pBase, isFp)` (`9` reads, `0` writes, `¬ReadsWidth`). -/
def loadHashStaticCtxProg : ℕ × ℕ → Memory.Prog FeistelHashCtx
  | (pBase, isFp) => do
    let kHb ← pure (if isFp = 0 then 61 else 62)
    let kOut ← pure (if isFp = 0 then 8 else 9)
    let q1 ← readParamQuadProg ((pBase, (kHb, 29)), (2, 3))
    let p2 ← readParamPairProg (pBase, (4, 5))
    let dt ← Memory.read (pBase + 6)
    let p3 ← readParamPairProg (pBase, (7, kOut))
    pure (q1, (p2, (dt, p3)))

@[simp] theorem runClient_state_loadHashStaticCtxProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (loadHashStaticCtxProg x)) = s := by
  rcases x with ⟨_, _⟩; unfold loadHashStaticCtxProg; simp

theorem clientState_loadHashStaticCtxProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadHashStaticCtxProg x) = s :=
  runClient_state_loadHashStaticCtxProg x s

theorem memoryCost_loadHashStaticCtxProg (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (loadHashStaticCtxProg x) s = 9 := by
  rcases x with ⟨_, _⟩
  unfold loadHashStaticCtxProg readParamQuadProg readParamPairProg
  simp

theorem clientResult_loadFeistelCtx {fl : FastEpochLayout} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) :
    (Memory.spec 0).clientResult s (loadHashStaticCtxProg (fl.pBase, 0)) = fl.feistelCtx := by
  unfold loadHashStaticCtxProg readParamQuadProg readParamPairProg
  simp only [↓reduceIte, pure_bind, prog_clientResult_bind, prog_runClient_state_bind,
    prog_runClient_state_read, prog_clientResult_read, prog_clientResult_pure,
    prog_runClient_state_pure]
  repeat rw [hpt _ (by decide)]
  rfl

theorem clientResult_loadFpStaticCtx {fl : FastEpochLayout} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) :
    (Memory.spec 0).clientResult s (loadHashStaticCtxProg (fl.pBase, 1)) = fl.fpStaticCtx := by
  unfold loadHashStaticCtxProg readParamQuadProg readParamPairProg
  simp only [Nat.one_ne_zero, ↓reduceIte, pure_bind, prog_clientResult_bind,
    prog_runClient_state_bind, prog_runClient_state_read, prog_clientResult_read,
    prog_clientResult_pure, prog_runClient_state_pure]
  repeat rw [hpt _ (by decide)]
  rfl

theorem realizesBounded_loadHashStaticCtx :
    RealizesBounded .exact loadHashStaticCtxProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := FeistelHashCtx))
      (fun w (pBase, _) s => 6 ≤ w ∧ pBase + 64 ≤ s.frontier) (fun _ _ => 0) := by
  have hrq := realizesBounded_readParamQuad
  have hrp := realizesBounded_readParamPair
  realize
  all_goals (
    rcases d with ⟨pBase, isFp⟩
    obtain ⟨hw6, hp⟩ := h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_readParamQuadProg,
      runClient_state_readParamPairProg] at *
    first | exact hw6 | exact hp | omega | (split_ifs <;> omega))

/-- Load `TrieCtx` for `role ∈ {0, 1}` from `(pBase, role)` (`10` reads, `0` writes,
`¬ReadsWidth`). -/
def loadTrieCtxProg : ℕ × ℕ → Memory.Prog TrieCtx
  | (pBase, role) => do
    let kOc ← pure (if role = 0 then 39 else 40)
    let kOn ← pure (if role = 0 then 41 else 42)
    let kOi ← pure (if role = 0 then 43 else 44)
    let q1 ← readParamQuadProg ((pBase, (1, kOc)), (kOn, kOi))
    let p2 ← readParamPairProg (pBase, (10, 2))
    let q3 ← readParamQuadProg ((pBase, (5, 7)), (22, 23))
    pure (q1, (p2, q3))

@[simp] theorem runClient_state_loadTrieCtxProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (loadTrieCtxProg x)) = s := by
  rcases x with ⟨_, _⟩; unfold loadTrieCtxProg; simp

theorem clientState_loadTrieCtxProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadTrieCtxProg x) = s :=
  runClient_state_loadTrieCtxProg x s

theorem memoryCost_loadTrieCtxProg (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (loadTrieCtxProg x) s = 10 := by
  rcases x with ⟨_, _⟩; unfold loadTrieCtxProg readParamQuadProg readParamPairProg; simp

theorem clientResult_loadTrieCtxProg {fl : FastEpochLayout} {role : ℕ} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) (hrole : role < 2) :
    (Memory.spec 0).clientResult s (loadTrieCtxProg (fl.pBase, role)) =
      (fl.trieL role).toCtx := by
  unfold loadTrieCtxProg readParamQuadProg readParamPairProg
  rcases role with _ | role
  · simp only [↓reduceIte, pure_bind, prog_clientResult_bind,
      prog_runClient_state_bind, prog_runClient_state_read, prog_clientResult_read,
      prog_clientResult_pure, prog_runClient_state_pure]
    repeat rw [hpt _ (by decide)]
    rfl
  · rcases role with _ | _
    · simp only [pure_bind, prog_clientResult_bind,
        prog_runClient_state_bind, prog_runClient_state_read, prog_clientResult_read,
        prog_clientResult_pure, prog_runClient_state_pure]
      repeat rw [hpt _ (by decide)]
      rfl
    · omega

theorem realizesBounded_loadTrieCtx :
    RealizesBounded .exact loadTrieCtxProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := TrieCtx))
      (fun w (pBase, _) s => 6 ≤ w ∧ pBase + 64 ≤ s.frontier) (fun _ _ => 0) := by
  have hrq := realizesBounded_readParamQuad
  have hrp := realizesBounded_readParamPair
  realize
  all_goals (
    rcases d with ⟨pBase, role⟩
    obtain ⟨hw6, hp⟩ := h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readParamQuadProg,
      runClient_state_readParamPairProg] at *
    first | exact hw6 | exact hp | omega | (split_ifs <;> omega))

/-- Load `BTreeSliceCtx` for `(b, role)` from `(pBase, (b, role))` (`15` reads, `0` writes,
`¬ReadsWidth`). -/
def loadBTreeSliceCtxProg : ℕ × (ℕ × ℕ) → Memory.Prog BTreeSliceCtx
  | (pBase, (b, role)) => do
    let p1 ← readParamPairProg (pBase, (1, 31))
    let om ← Memory.read (pBase + 36)
    let p2 ← readParamPairProg (pBase, (37, 38))
    let p3 ← readParamPairProg (pBase, (10, 2))
    let wm ← Memory.read (pBase + 16)
    let p4 ← readParamPairProg (pBase, (17, 18))
    let q5 ← readParamQuadProg ((pBase, (9, 19)), (20, 21))
    let nb ← Memory.read (pBase + 11)
    pure (((p1, (om, p2)), (p3, (wm, p4))), (q5, (nb, (b, role))))

@[simp] theorem runClient_state_loadBTreeSliceCtxProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (loadBTreeSliceCtxProg x)) = s := by
  rcases x with ⟨_, ⟨_, _⟩⟩; unfold loadBTreeSliceCtxProg; simp

theorem clientState_loadBTreeSliceCtxProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadBTreeSliceCtxProg x) = s :=
  runClient_state_loadBTreeSliceCtxProg x s

theorem memoryCost_loadBTreeSliceCtxProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (loadBTreeSliceCtxProg x) s = 15 := by
  rcases x with ⟨_, ⟨_, _⟩⟩; unfold loadBTreeSliceCtxProg readParamQuadProg readParamPairProg; simp

theorem clientResult_loadBTreeSliceCtxProg {fl : FastEpochLayout} {b role : ℕ} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) :
    (Memory.spec 0).clientResult s (loadBTreeSliceCtxProg (fl.pBase, (b, role))) =
      fl.btL.toSliceCtx b role := by
  unfold loadBTreeSliceCtxProg readParamQuadProg readParamPairProg
  simp only [prog_clientResult_bind, prog_runClient_state_bind, prog_runClient_state_read,
    prog_clientResult_read, prog_clientResult_pure, prog_runClient_state_pure]
  repeat rw [hpt _ (by decide)]
  rfl

theorem realizesBounded_loadBTreeSliceCtx :
    RealizesBounded .exact loadBTreeSliceCtxProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := BTreeSliceCtx))
      (fun w (pBase, _) s => 6 ≤ w ∧ pBase + 64 ≤ s.frontier) (fun _ _ => 0) := by
  have hrq := realizesBounded_readParamQuad
  have hrp := realizesBounded_readParamPair
  realize
  all_goals (
    rcases d with ⟨pBase, ⟨b, role⟩⟩
    obtain ⟨hw6, hp⟩ := h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_readParamPairProg] at *
    first | exact hw6 | exact hp | omega)

/-! ### Guarded Hash Evaluators (`fastFeistelSplitProg`, `fastFeistelReconProg`, `fastRKeyProg`,
`fastFpHashProg`) -/

private theorem evalSalted_ready_bounds {w : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    0 < redWidthWhp fl.U ∧
    redWidthWhp fl.U ≤ w ∧
    bCharWhp fl.N < w ∧
    bWhp fl.N < w ∧
    fpBitsWhp fl.N < w ∧
    dTabWhp fl.c < 2 ^ w ∧
    cTabWhp fl.c + 1 < 2 ^ w ∧
    BitPackedDoubleTabulation.topEntries (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) < 2 ^ w ∧
    BitPackedDoubleTabulation.botEntries (dTabWhp fl.c) (bCharWhp fl.N) < 2 ^ w ∧
    fl.bktHashBase + BitPackedDoubleTabulation.space w (cTabWhp fl.c) (dTabWhp fl.c)
      (bCharWhp fl.N) (bWhp fl.N) ≤ s.frontier ∧
    fl.fpHashBase + BitPackedDoubleTabulation.space w (cTabWhp fl.c) (dTabWhp fl.c)
      (bCharWhp fl.N) (fpBitsWhp fl.N) ≤ s.frontier := by
  obtain ⟨hv, _, _, _⟩ := hr
  have hw_eq := hv.w_eq
  obtain ⟨_, _, _, hbc_w, hbw_w, hfp_w, _, _, _, htop_le, hbot_le, _, _, _, _, _, _, _, _, _⟩ :=
    largeEpoch_param_bounds hv.thresh_le hv.N_le_U hv.fits_U
  have hN_w : fl.N < 2 ^ w := lt_of_le_of_lt hv.N_le_U hv.fits_U
  have hbc1 : 1 ≤ 2 ^ bCharWhp fl.N := Nat.one_le_two_pow
  have hc1_le : cTabWhp fl.c + 1 ≤
      BitPackedDoubleTabulation.topEntries (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) := by
    unfold BitPackedDoubleTabulation.topEntries dTabWhp
    have hq := le_qTabWhp fl.c
    have hd_pos : 1 ≤ 2 * qTabWhp fl.c * (cTabWhp fl.c + 1) := by nlinarith
    calc cTabWhp fl.c + 1 ≤ (cTabWhp fl.c + 1) * (2 * qTabWhp fl.c * (cTabWhp fl.c + 1)) :=
          Nat.le_mul_of_pos_right _ hd_pos
      _ ≤ _ := Nat.le_mul_of_pos_right _ hbc1
  have hd_le : dTabWhp fl.c ≤ BitPackedDoubleTabulation.botEntries (dTabWhp fl.c) (bCharWhp fl.N) :=
    Nat.le_mul_of_pos_right _ hbc1
  have hend := offEpochEnd_eq_epochMetaWordsWhp (c := fl.c) (w := fl.w) hv.thresh_le
  have hmf := hv.meta_frontier
  subst hw_eq
  refine ⟨redWidthWhp_pos fl.U, hv.redWidth_le, hbc_w, hbw_w, hfp_w,
    lt_of_le_of_lt (hd_le.trans hbot_le) hN_w,
    lt_of_le_of_lt (hc1_le.trans htop_le) hN_w,
    lt_of_le_of_lt htop_le hN_w,
    lt_of_le_of_lt hbot_le hN_w, ?_, ?_⟩
  · dsimp only [FastEpochLayout.bktHashBase]
    unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
      offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
      offBktMeta offFpHash at hend
    omega
  · dsimp only [FastEpochLayout.fpHashBase]
    unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
      offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
      offBktMeta at hend
    omega

/-- Guarded Feistel split `(epochBucket, keyQuotient)` from `(pBase, u_val)` (`¬ReadsWidth`). -/
def fastFeistelSplitProg : ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (pBase, u_val) => do
    let uMax ← Memory.read (pBase + 46)
    if u_val ≤ uMax then do
      let fctx ← loadHashStaticCtxProg (pBase, 0)
      feistelSplitBoundedProg (fctx, u_val)
    else
      pure (0, 0)

@[simp] theorem runClient_state_fastFeistelSplitProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastFeistelSplitProg x)) = s := by
  rcases x with ⟨pBase, u_val⟩
  unfold fastFeistelSplitProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind, prog_runClient_state_read]
  split_ifs
  · rw [prog_runClient_state_bind, clientState_loadHashStaticCtxProg]
    exact clientState_feistelSplitBoundedProg _ s
  · rfl

theorem clientState_fastFeistelSplitProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastFeistelSplitProg x) = s :=
  runClient_state_fastFeistelSplitProg x s

theorem realizesBounded_fastFeistelSplit :
    RealizesBounded .exact fastFeistelSplitProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hl := realizesBounded_loadHashStaticCtx
  have hfs := realizesBounded_feistelSplit
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_loadHashStaticCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have ⟨hv, hpt, hbkt, _⟩ := hr
      obtain ⟨hw0, hw0_le, hbc_w, hbw_w, _, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_bkt, _⟩ :=
        evalSalted_ready_bounds hr
      have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
      have hU_pos : 0 < fl.U := lt_of_lt_of_le (whpThreshold_pos fl.c)
        (hv.thresh_le.trans hv.N_le_U)
      have hu_lt_U : u_val < fl.U := by omega
      have hu_lt_w0 : u_val < 2 ^ redWidthWhp fl.U :=
        hu_lt_U.trans_le (le_two_pow_redWidthWhp fl.U)
      have hq_lt_w0 : u_val >>> bWhp fl.N < 2 ^ redWidthWhp fl.U :=
        (Nat.shiftRight_le _ _).trans_lt hu_lt_w0
      have hl_res := clientResult_loadFeistelCtx (s := s) hpt
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      refine ⟨hbw_w, hu_lt_w0, hv.w_pos, hv.w_eq, hw0, hw0_le, hbc_w, hbw_w.le,
        by rw [hv.w_eq]; rfl, hbkt, Nat.two_pow_pos _, hq_lt_w0, hd_lt, hc1_lt,
        htop_lt, hbot_lt, hfr_bkt⟩))

theorem fastFeistelSplitProg_spec {fl : FastEpochLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s : Memory.State}
    (hr : FastLayoutReady w fl s)
    (hrep : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt s.mem)
    (u : Fin fl.U) :
    (Memory.spec 0).clientResult s (fastFeistelSplitProg (fl.pBase, u.val)) =
      (epochBucket fl.c fl.U fl.N θ_bkt u, keyQuotient (bWhp fl.N) u.val) ∧
    memoryCost (fastFeistelSplitProg (fl.pBase, u.val)) s ≤
      11 + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hr.2.1 46 (by decide)
  have hle : u.val ≤ fl.U - 1 := Nat.le_sub_one_of_lt u.isLt
  obtain ⟨hres, _, hcost⟩ := feistelSplitBoundedProg_spec hr.1.N_le_U hrep u
  unfold fastFeistelSplitProg
  simp only [StateTransitionSpec.clientState, prog_clientResult_bind, Realization.memoryCost_bind',
    prog_clientResult_read, prog_runClient_state_read, prog_memoryCost_read, hum, hle, ↓reduceIte,
    runClient_state_loadHashStaticCtxProg, memoryCost_loadHashStaticCtxProg]
  rw [clientResult_loadFeistelCtx hr.2.1]
  dsimp only [FastEpochLayout.feistelCtx, FastEpochLayout.dtOffBot]
  exact ⟨hres, by rw [hcost]; omega⟩

/-- Guarded Feistel key reconstruction from `(pBase, (bkt, q_val))` (`¬ReadsWidth`). -/
def fastFeistelReconProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (pBase, (bkt, q_val)) => do
    let fctx ← loadHashStaticCtxProg (pBase, 0)
    let ((_, (wv, w0)), (_, (_, (_, bBits)))) := fctx
    if bBits ≤ w0 then do
      let qLim ← pure (w0 - bBits)
      if qLim < wv then
        if q_val < (1 <<< qLim) then
          feistelReconBoundedProg (fctx, (bkt, q_val))
        else
          pure 0
      else
        pure 0
    else
      pure 0

@[simp] theorem runClient_state_fastFeistelReconProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastFeistelReconProg x)) = s := by
  rcases x with ⟨pBase, ⟨bkt, q_val⟩⟩
  unfold clientOutState fastFeistelReconProg; dsimp only
  rw [prog_runClient_state_bind, clientState_loadHashStaticCtxProg]
  split_ifs
  · simp only [pure_bind]
    split_ifs
    · exact clientState_feistelReconBoundedProg _ s
    all_goals rfl
  · rfl

theorem clientState_fastFeistelReconProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastFeistelReconProg x) = s :=
  runClient_state_fastFeistelReconProg x s

theorem realizesBounded_fastFeistelRecon :
    RealizesBounded .exact fastFeistelReconProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hl := realizesBounded_loadHashStaticCtx
  have hrec := realizesBounded_feistelRecon
  realize
  all_goals (
    rcases d with ⟨pBase, ⟨bkt, q_val⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hw_pos := hr.1.w_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw_pos.ne'
    have hl_res : (Memory.spec 0).clientResult s (loadHashStaticCtxProg (fl.pBase, 0)) =
        fl.feistelCtx := clientResult_loadFeistelCtx hr.2.1
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, runClient_state_loadHashStaticCtxProg] at *
    try simp only [hl_res] at *
    dsimp only [FastEpochLayout.feistelCtx, Fits] at *
    have hw_eq := hr.1.w_eq
    have hw_lt_pow : w < 2 ^ w := Nat.lt_two_pow_self
    first | exact hw6 | exact hp | omega | (
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right Nat.one_lt_two (by omega)) | (
      have ⟨hv, _, hbkt, _⟩ := hr
      obtain ⟨hw0, hw0_le, hbc_w, hbw_w, _, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_bkt, _⟩ :=
        evalSalted_ready_bounds hr
      have hbw_pos : 1 ≤ bWhp fl.N := by
        have hM := hv.mp_valid.M_ge
        dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hM
        unfold numBucketsWhp at hM
        by_contra hz; have h0 : bWhp fl.N = 0 := by omega
        rw [h0] at hM; omega
      have hbw_kb : bWhp fl.N ≤ keyBits fl.U := by
        unfold bWhp keyBits
        exact (Nat.sub_le _ _).trans ((Nat.log_mono_right hv.N_le_U).trans (Nat.log_le_clog 2 fl.U))
      have hrw_eq : redWidthWhp fl.U = keyBits fl.U := max_eq_right (by omega)
      have hq_lt : q_val < 2 ^ quotBitsWhp fl.U fl.N := by
        have hlt_sh : q_val < 1 <<< (redWidthWhp fl.U - bWhp fl.N) := by assumption
        rw [Nat.shiftLeft_eq, one_mul, hrw_eq] at hlt_sh
        exact hlt_sh
      have hsum_w : quotBitsWhp fl.U fl.N + bWhp fl.N ≤ w := by
        unfold quotBitsWhp; rw [Nat.sub_add_cancel hbw_kb]
        exact Nat.clog_le_of_le_pow hv.fits_U.le
      have hq_w0 : q_val < 2 ^ redWidthWhp fl.U :=
        lt_of_lt_of_le hq_lt (two_pow_quotBitsWhp_le_redWidthWhp fl.U fl.N)
      exact ⟨quotBitsWhp fl.U fl.N, hbw_w, hsum_w, hq_lt,
        hv.w_pos, hv.w_eq, hw0, hw0_le, hbc_w, hbw_w.le, by rw [hv.w_eq]; rfl, hbkt,
        Nat.two_pow_pos _, hq_w0, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_bkt⟩))

theorem fastFeistelReconProg_spec {fl : FastEpochLayout} {w bkt q_val : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s : Memory.State}
    (hr : FastLayoutReady w fl s)
    (hq_lt : q_val < 2 ^ quotBitsWhp fl.U fl.N)
    (hrep : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt s.mem) :
    (Memory.spec 0).clientResult s (fastFeistelReconProg (fl.pBase, (bkt, q_val))) =
      feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt) bkt q_val ∧
    memoryCost (fastFeistelReconProg (fl.pBase, (bkt, q_val))) s ≤
      12 + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by
  obtain ⟨hv, hpt, _, _⟩ := hr
  have hbw_pos : 1 ≤ bWhp fl.N := by
    have hM := hv.mp_valid.M_ge
    dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hM
    unfold numBucketsWhp at hM
    by_contra hz; have h0 : bWhp fl.N = 0 := by omega
    rw [h0] at hM; omega
  have hbw_kb : bWhp fl.N ≤ keyBits fl.U := by
    unfold bWhp keyBits
    exact (Nat.sub_le _ _).trans ((Nat.log_mono_right hv.N_le_U).trans (Nat.log_le_clog 2 fl.U))
  have hrw_eq : redWidthWhp fl.U = keyBits fl.U := max_eq_right (by omega)
  have hbw_le_rw : bWhp fl.N ≤ redWidthWhp fl.U := hrw_eq ▸ hbw_kb
  have hqLim_eq : redWidthWhp fl.U - bWhp fl.N = quotBitsWhp fl.U fl.N := by rw [hrw_eq]; rfl
  have hqb_lt_w : redWidthWhp fl.U - bWhp fl.N < fl.w := by
    have hsum : quotBitsWhp fl.U fl.N + bWhp fl.N ≤ fl.w := by
      unfold quotBitsWhp; rw [Nat.sub_add_cancel hbw_kb]
      exact Nat.clog_le_of_le_pow (hv.w_eq ▸ hv.fits_U).le
    omega
  have hq_sh : q_val < (1 <<< (redWidthWhp fl.U - bWhp fl.N)) := by
    rwa [hqLim_eq, Nat.shiftLeft_eq, one_mul]
  obtain ⟨hres, _, hcost⟩ := feistelReconBoundedProg_spec hq_lt hrep (bkt := bkt)
  unfold fastFeistelReconProg
  simp only [StateTransitionSpec.clientState, prog_clientResult_bind, Realization.memoryCost_bind',
    runClient_state_loadHashStaticCtxProg, memoryCost_loadHashStaticCtxProg]
  rw [clientResult_loadFeistelCtx hpt]
  simp only [FastEpochLayout.feistelCtx, FastEpochLayout.dtOffBot, hbw_le_rw, ↓reduceIte,
    pure_bind, hqb_lt_w, hq_sh]
  exact ⟨hres, by rw [hcost]; omega⟩

/-- Guarded Stage-1 reduced key `rKeyOf c U N θ_fp u` from `(pBase, u_val)` (`5` reads, `0` writes,
`¬ReadsWidth`). -/
def fastRKeyProg : ℕ × ℕ → Memory.Prog ℕ
  | (pBase, u_val) => do
    let uMax ← Memory.read (pBase + 46)
    if u_val ≤ uMax then do
      let hbFp ← Memory.read (pBase + 62)
      let wr ← readParamPairProg (pBase, (3, 4))
      let α_fp ← Memory.read hbFp
      oddMulReducedProg (wr, (α_fp, u_val))
    else
      pure 0

@[simp] theorem runClient_state_fastRKeyProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastRKeyProg x)) = s := by
  rcases x with ⟨pBase, u_val⟩
  unfold fastRKeyProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind, prog_runClient_state_read]
  split_ifs
  · simp [runClient_state_oddMulReducedProg]
  · rfl

theorem clientState_fastRKeyProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastRKeyProg x) = s :=
  runClient_state_fastRKeyProg x s

theorem realizesBounded_fastRKey :
    RealizesBounded .exact fastRKeyProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrp := realizesBounded_readParamPair
  have hom := realizesBounded_oddMulReduced
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    have ⟨hv, hpt, _, hfp_α⟩ := hr
    obtain ⟨hw0, hw0_le, _, _, _, _, _, _, _, _, hfr_fp⟩ := evalSalted_ready_bounds hr
    have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
    have hhb : s.mem (fl.pBase + 62) = fl.fpHashBase := hpt 62 (by decide)
    have hw0_m : s.mem (fl.pBase + 3) = redWidthWhp fl.U := hpt 3 (by decide)
    have hsp_pos := BitPackedDoubleTabulation.space_pos w (cTabWhp fl.c) (dTabWhp fl.c)
      (bCharWhp fl.N) (fpBitsWhp fl.N)
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_readParamPairProg] at *
    first | exact hw6 | exact hp | decide | omega | (
      have hU_pos : 0 < fl.U := lt_of_lt_of_le (whpThreshold_pos fl.c)
        (hv.thresh_le.trans hv.N_le_U)
      have hu_lt_U : u_val < fl.U := by omega
      have hu_lt_w0 : u_val < 2 ^ redWidthWhp fl.U :=
        hu_lt_U.trans_le (le_two_pow_redWidthWhp fl.U)
      have hwr : ((Memory.spec 0).runClient s (readParamPairProg (fl.pBase, (3, 4)))).1 =
          (redWidthWhp fl.U, redBitsWhp fl.c fl.N) := by
        unfold readParamPairProg; simp [hw0_m, hpt 4 (by decide), FastEpochLayout.paramWord]
      simp only [StateTransitionSpec.clientResult, hwr, hhb]
      exact ⟨hw0, hw0_le, hfp_α, hu_lt_w0⟩))

theorem fastRKeyProg_spec {fl : FastEpochLayout} {w : ℕ}
    {θ_fp : FpSeed fl.c fl.U fl.N} {s : Memory.State}
    (hr : FastLayoutReady w fl s)
    (hrep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) θ_fp s.mem)
    (u : Fin fl.U) :
    (Memory.spec 0).clientResult s (fastRKeyProg (fl.pBase, u.val)) =
      rKeyOf fl.c fl.U fl.N θ_fp u ∧
    memoryCost (fastRKeyProg (fl.pBase, u.val)) s ≤ 5 := by
  have hpt := hr.2.1
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
  have hhb : s.mem (fl.pBase + 62) = fl.fpHashBase := hpt 62 (by decide)
  have hw0 : s.mem (fl.pBase + 3) = redWidthWhp fl.U := hpt 3 (by decide)
  have hrb : s.mem (fl.pBase + 4) = redBitsWhp fl.c fl.N := hpt 4 (by decide)
  have hle : u.val ≤ fl.U - 1 := Nat.le_sub_one_of_lt u.isLt
  have hα_eq : s.mem fl.fpHashBase = θ_fp.1.val := hrep.1
  unfold fastRKeyProg readParamPairProg
  simp only [StateTransitionSpec.clientState, prog_clientResult_bind, Realization.memoryCost_bind',
    prog_clientResult_read, prog_runClient_state_read, prog_memoryCost_read, hum, hle, ↓reduceIte,
    prog_runClient_state_bind, prog_clientResult_pure, prog_runClient_state_pure,
    memoryCost_pure, hhb, hw0, hrb, hα_eq, clientResult_oddMulReducedProg,
    memoryCost_oddMulReducedProg]
  refine ⟨?_, by omega⟩
  unfold rKeyOf multiplyShiftReduced
  rw [oddMulModWord_eq (redWidthWhp_pos fl.U), Nat.shiftRight_eq_div_pow]

/-- Guarded Stage-2 salted fingerprint `(fpHash c U N θ_fp salt u).val` from
`(pBase, (salt, u_val))` (`¬ReadsWidth`). -/
def fastFpHashProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (pBase, (salt, u_val)) => do
    let uMax ← Memory.read (pBase + 46)
    let sMax ← Memory.read (pBase + 24)
    if u_val ≤ uMax then
      if salt < sMax then do
        let hctx ← loadHashStaticCtxProg (pBase, 1)
        evalSaltedBoundedProg (hctx, (salt, u_val))
      else
        pure 0
    else
      pure 0

@[simp] theorem runClient_state_fastFpHashProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastFpHashProg x)) = s := by
  rcases x with ⟨pBase, ⟨salt, u_val⟩⟩
  unfold fastFpHashProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind, prog_runClient_state_read]
  split_ifs
  · rw [prog_runClient_state_bind, clientState_loadHashStaticCtxProg]
    exact clientState_evalSaltedBoundedProg _ s
  all_goals rfl

theorem clientState_fastFpHashProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastFpHashProg x) = s :=
  runClient_state_fastFpHashProg x s

theorem realizesBounded_fastFpHash :
    RealizesBounded .exact fastFpHashProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hl := realizesBounded_loadHashStaticCtx
  have hes := realizesBounded_evalSaltedBounded
  realize
  all_goals (
    rcases d with ⟨pBase, ⟨salt, u_val⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    have ⟨hv, hpt, _, hfp_α⟩ := hr
    obtain ⟨hw0, hw0_le, hbc_w, _, hfp_w, hd_lt, hc1_lt, htop_lt, hbot_lt, _, hfr_fp⟩ :=
      evalSalted_ready_bounds hr
    have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
    have hsm : s.mem (fl.pBase + 24) = sMaxWhp fl.c fl.N := hpt 24 (by decide)
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_loadHashStaticCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have hU_pos : 0 < fl.U := lt_of_lt_of_le (whpThreshold_pos fl.c)
        (hv.thresh_le.trans hv.N_le_U)
      have hu_lt_U : u_val < fl.U := by omega
      have hu_lt_w0 : u_val < 2 ^ redWidthWhp fl.U :=
        hu_lt_U.trans_le (le_two_pow_redWidthWhp fl.U)
      have hsalt_bc : salt < 2 ^ bCharWhp fl.N :=
        lt_of_lt_of_le (by omega : salt < sMaxWhp fl.c fl.N)
          (sMaxWhp_le_two_pow_bCharWhp hv.thresh_le)
      have hl_res := clientResult_loadFpStaticCtx (s := s) hpt
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      exact ⟨hv.w_pos, hv.w_eq, hw0, hw0_le, hbc_w, hfp_w.le, by rw [hv.w_eq]; rfl, hfp_α,
        hsalt_bc, hu_lt_w0, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_fp⟩))

theorem fastFpHashProg_spec {fl : FastEpochLayout} {w : ℕ}
    {θ_fp : FpSeed fl.c fl.U fl.N} {s : Memory.State}
    (hr : FastLayoutReady w fl s)
    (hrep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) θ_fp s.mem)
    (salt : Fin (sMaxWhp fl.c fl.N)) (u : Fin fl.U) :
    (Memory.spec 0).clientResult s (fastFpHashProg (fl.pBase, (salt.val, u.val))) =
      (fpHash fl.c fl.U fl.N θ_fp salt u).val ∧
    memoryCost (fastFpHashProg (fl.pBase, (salt.val, u.val))) s ≤
      12 + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by
  have hpt := hr.2.1
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
  have hsm : s.mem (fl.pBase + 24) = sMaxWhp fl.c fl.N := hpt 24 (by decide)
  have hle : u.val ≤ fl.U - 1 := Nat.le_sub_one_of_lt u.isLt
  have hslt : salt.val < sMaxWhp fl.c fl.N := salt.isLt
  obtain ⟨hres, _, hcost⟩ := evalSaltedBoundedProg_eq_evalSalted (U := fl.U)
    (R_bits := redBitsWhp fl.c fl.N) (redWidthWhp_pos fl.U)
    (sMaxWhp_le_two_pow_bCharWhp hr.1.thresh_le) hrep salt u
  unfold fastFpHashProg
  simp only [StateTransitionSpec.clientState, prog_clientResult_bind, Realization.memoryCost_bind',
    prog_clientResult_read, prog_runClient_state_read, prog_memoryCost_read, hum, hsm,
    hle, hslt, ↓reduceIte, runClient_state_loadHashStaticCtxProg,
    memoryCost_loadHashStaticCtxProg]
  rw [clientResult_loadFpStaticCtx hpt]
  dsimp only [FastEpochLayout.fpStaticCtx, FastEpochLayout.dtOffBot]
  exact ⟨hres, by rw [hcost]; omega⟩

/-! ## Section 3: Fast-Epoch Scalar, Per-Bucket Lane (`5, 12..15`), and `BlockPool` Accessors -/

/-- Read scalar `s.mem (metaBase + off)` for `off < 18` via `pBase` (`2` reads, `¬ReadsWidth`). -/
def fastReadMetaProg : ℕ × ℕ → Memory.Prog ℕ
  | (pBase, off) =>
    if off < 18 then do
      let mb ← Memory.read (pBase + 1)
      Memory.read (mb + off)
    else
      pure 0

@[simp] theorem runClient_state_fastReadMetaProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastReadMetaProg x)) = s := by
  rcases x with ⟨_, off⟩; unfold fastReadMetaProg; dsimp only; split_ifs <;> rfl

theorem clientState_fastReadMetaProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastReadMetaProg x) = s :=
  runClient_state_fastReadMetaProg x s

theorem memoryCost_fastReadMetaProg (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (fastReadMetaProg x) s ≤ 2 := by
  rcases x with ⟨_, off⟩; unfold fastReadMetaProg; dsimp only; split_ifs <;> simp

theorem clientResult_fastReadMetaProg {fl : FastEpochLayout} {off : ℕ} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) (hoff : off < 18) :
    (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, off)) =
      s.mem (fl.metaBase + off) := by
  unfold fastReadMetaProg; simp [hoff, hpt 1 (by decide), FastEpochLayout.paramWord]

theorem realizesBounded_fastReadMeta :
    RealizesBounded .exact fastReadMetaProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨pBase, off⟩
    obtain ⟨fl, rfl, hv, hpt, _, _⟩ := h
    have hw6 := hv.w_ge_six
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hmb : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
    have h32 : 32 ≤ epochMetaWordsWhp fl.c fl.w fl.N := by
      have hend := offEpochEnd_eq_epochMetaWordsWhp (c := fl.c) (w := fl.w) hv.thresh_le
      rw [← hend]
      unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
        offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
        offBktMeta offFpHash offBktHash
      omega
    have hp := hv.pBase_lt_meta
    have hmf := hv.meta_frontier
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    omega)

/-- Write scalar `s.mem (metaBase + off) := val` for `1 ≤ off < 18` (`off ≠ 1`, `off < 10 ∨ off =
17`) via `pBase` (`¬ReadsWidth`). -/
def fastWriteMetaProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((pBase, off), val) =>
    if (2 ≤ off ∧ off < 10) ∨ off = 17 then do
      let mb ← Memory.read (pBase + 1)
      Memory.write (mb + off) val
    else
      pure ()

@[simp] theorem runClient_frontier_fastWriteMetaProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (fastWriteMetaProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨_, _⟩, _⟩; unfold fastWriteMetaProg; dsimp only; split_ifs <;> rfl

theorem memoryCost_fastWriteMetaProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (fastWriteMetaProg x) s ≤ 2 := by
  rcases x with ⟨⟨_, _⟩, _⟩; unfold fastWriteMetaProg; dsimp only; split_ifs <;> simp

theorem clientState_fastWriteMetaProg {fl : FastEpochLayout} {off val : ℕ} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) (hoff : (2 ≤ off ∧ off < 10) ∨ off = 17) :
    (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, off), val)) =
      ⟨Function.update s.mem (fl.metaBase + off) val, s.frontier⟩ := by
  unfold fastWriteMetaProg
  simp [hoff, hpt 1 (by decide), FastEpochLayout.paramWord, StateTransitionSpec.clientState]

theorem fastWriteMetaProg_ready {w : ℕ} {fl : FastEpochLayout} {off val : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    FastLayoutReady w fl
      ((Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, off), val))) := by
  by_cases hoff : (2 ≤ off ∧ off < 10) ∨ off = 17
  · rw [clientState_fastWriteMetaProg hr.2.1 hoff]
    refine hr.of_frame rfl fun addr ha => Function.update_of_ne ?_ val s.mem
    intro heq; apply ha; left; omega
  · have hst : (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, off), val)) = s := by
      unfold fastWriteMetaProg; simp [hoff]
    rwa [hst]

theorem realizesBounded_fastWriteMeta :
    RealizesBounded .exact fastWriteMetaProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨pBase, off⟩, val⟩
    obtain ⟨fl, rfl, hv, hpt, _, _⟩ := h
    have hw6 := hv.w_ge_six
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hmb : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
    have h32 : 32 ≤ epochMetaWordsWhp fl.c fl.w fl.N := by
      have hend := offEpochEnd_eq_epochMetaWordsWhp (c := fl.c) (w := fl.w) hv.thresh_le
      rw [← hend]
      unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
        offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
        offBktMeta offFpHash offBktHash
      omega
    have hp := hv.pBase_lt_meta
    have hmf := hv.meta_frontier
    have hfr_w := hmem.1
    have hval_w : val < 2 ^ w := hwords 2
    dsimp only [Fits] at hfr_w ⊢
    try dsimp only at *
    omega)

/-- Read per-bucket `ptrB`-bit lane `lane < 16` of bucket `b < M` in `offBktMeta` via `pBase`
(`¬ReadsWidth`). -/
def fastReadBktLaneProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (pBase, (b, lane)) => do
    let M ← Memory.read (pBase + 11)
    if b < M ∧ lane < 16 then do
      let mb ← Memory.read (pBase + 1)
      let obm ← Memory.read (pBase + 31)
      let pbw ← readParamPairProg (pBase, (10, 2))
      readPackedCompGenProg (((mb, obm), pbw), 16 * b + lane)
    else
      pure 0

@[simp] theorem runClient_state_fastReadBktLaneProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastReadBktLaneProg x)) = s := by
  rcases x with ⟨_, ⟨_, _⟩⟩
  unfold fastReadBktLaneProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind, prog_runClient_state_read]
  split_ifs <;> simp

theorem clientState_fastReadBktLaneProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastReadBktLaneProg x) = s :=
  runClient_state_fastReadBktLaneProg x s

theorem memoryCost_fastReadBktLaneProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (fastReadBktLaneProg x) s ≤ 7 := by
  rcases x with ⟨_, ⟨_, _⟩⟩
  unfold fastReadBktLaneProg; dsimp only
  simp only [StateTransitionSpec.clientState, Realization.memoryCost_bind', prog_memoryCost_read,
    prog_runClient_state_read]
  split_ifs
  · simp [readParamPairProg]
  · simp

theorem clientResult_fastReadBktLaneProg {fl : FastEpochLayout} {b lane : ℕ} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) (hb : b < numBucketsWhp fl.N) (hlane : lane < 16) :
    (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, lane))) =
      readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s.mem
        (16 * b + lane) := by
  unfold fastReadBktLaneProg readParamPairProg
  simp only [prog_clientResult_bind, prog_runClient_state_bind, prog_clientResult_read,
    prog_runClient_state_read, hpt 11 (by decide), FastEpochLayout.paramWord, hb, hlane, and_self,
    ↓reduceIte, prog_clientResult_pure, prog_runClient_state_pure,
    clientResult_readPackedCompGenProg]
  rw [hpt 1 (by decide), hpt 31 (by decide), hpt 10 (by decide), hpt 2 (by decide)]
  rfl

theorem realizesBounded_fastReadBktLane :
    RealizesBounded .exact fastReadBktLaneProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrp := realizesBounded_readParamPair
  have hrk := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨pBase, ⟨b, lane⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    obtain ⟨hv, hpt, _, _⟩ := hr
    have hmv := hv.mp_valid
    have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
    have hm1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
    have hm31 : s.mem (fl.pBase + 31) = offBktMeta fl.c fl.w fl.N := hpt 31 (by decide)
    have hm10 : s.mem (fl.pBase + 10) = globalPtrBits fl.N := hpt 10 (by decide)
    have hm2 : s.mem (fl.pBase + 2) = fl.w := hpt 2 (by decide)
    have h16M_w : 16 * numBucketsWhp fl.N < 2 ^ w :=
      lt_of_le_of_lt hmv.sixteen_M_le hmv.nCap_lt_two_pow_w
    dsimp only [Fits] at hfr_w ⊢
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readParamPairProg] at *
    first | exact hw6 | exact hp | decide | omega | (
      have hidx : 16 * b + lane < 16 * numBucketsWhp fl.N := by omega
      have hpr : ((Memory.spec 0).runClient s (readParamPairProg (fl.pBase, (10, 2)))).1 =
          (globalPtrBits fl.N, fl.w) := by
        unfold readParamPairProg; simp [hm10, hm2]
      simp only [StateTransitionSpec.clientResult, hm1, hm31, hpr]
      refine ⟨16 * numBucketsWhp fl.N, hv.w_pos, hv.w_eq, hmv.ptrB_le, hidx, ?_⟩
      have hd1 := hmv.offSlabDir_ge; have hd2 := hmv.offTailDir_ge
      have hd3 := hmv.offSlabOwner_ge; have hd4 := hmv.offTailOwner_ge
      have hdf := hmv.frontier_ge
      dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hd1 hd2 hd3 hd4 hdf
      cases hv.w_eq
      omega))

/-- Write per-bucket `ptrB`-bit lane `lane ∈ {5, 12, 13, 14, 15}` of bucket `b < M` in `offBktMeta`
via `pBase` (`¬ReadsWidth`). Restricting to `{5, 12..15}` guarantees structural non-interference
with `BlockPoolState` (`0..4`) and `BTreeEpochLayout` (`6..11`)! -/
def fastWriteBktLaneProg : (ℕ × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((pBase, (b, lane)), val) => do
    let M ← Memory.read (pBase + 11)
    let nCap ← Memory.read (pBase + 0)
    if b < M ∧ (lane = 5 ∨ (12 ≤ lane ∧ lane < 16)) ∧ val ≤ nCap then do
      let mb ← Memory.read (pBase + 1)
      let obm ← Memory.read (pBase + 31)
      let pbw ← readParamPairProg (pBase, (10, 2))
      writePackedCompGenProg ((((mb, obm), pbw), 16 * b + lane), val)
    else
      pure ()

@[simp] theorem runClient_frontier_fastWriteBktLaneProg
    (x : (ℕ × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (fastWriteBktLaneProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨_, ⟨_, _⟩⟩, _⟩
  unfold fastWriteBktLaneProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind, prog_runClient_state_read]
  split_ifs
  · simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
      prog_runClient_state_read, runClient_state_readParamPairProg]
    rw [runClient_state_writePackedCompGenProg]
  · rfl

theorem memoryCost_fastWriteBktLaneProg (x : (ℕ × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (fastWriteBktLaneProg x) s ≤ 10 := by
  rcases x with ⟨⟨_, ⟨_, _⟩⟩, _⟩
  unfold fastWriteBktLaneProg; dsimp only
  simp only [StateTransitionSpec.clientState, Realization.memoryCost_bind', prog_memoryCost_read,
    prog_runClient_state_read]
  split_ifs
  · simp [readParamPairProg]
  · simp

theorem clientState_fastWriteBktLaneProg {fl : FastEpochLayout} {b lane val : ℕ}
    {s : Memory.State} (hpt : fl.ParamTable s.mem)
    (hb : b < numBucketsWhp fl.N) (hlane : lane = 5 ∨ (12 ≤ lane ∧ lane < 16))
    (hval : val ≤ fl.N) :
    (Memory.spec 0).clientState s (fastWriteBktLaneProg ((fl.pBase, (b, lane)), val)) =
      ⟨writePacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s.mem
        (16 * b + lane) val, s.frontier⟩ := by
  unfold fastWriteBktLaneProg readParamPairProg
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind, prog_clientResult_read,
    prog_runClient_state_read, hpt 11 (by decide), hpt 0 (by decide), FastEpochLayout.paramWord,
    hb, hlane, hval, and_self, ↓reduceIte, prog_clientResult_bind, prog_clientResult_pure,
    prog_runClient_state_pure, runClient_state_writePackedCompGenProg]
  rw [hpt 1 (by decide), hpt 31 (by decide), hpt 10 (by decide), hpt 2 (by decide)]
  rfl

theorem fastWriteBktLaneProg_frame {w : ℕ} {fl : FastEpochLayout} {b lane val : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (fastWriteBktLaneProg ((fl.pBase, (b, lane)), val))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ b' < numBucketsWhp fl.N, ∀ role < 3,
      extractBTreeSlice fl.btL b' role s'.mem = extractBTreeSlice fl.btL b' role s.mem) ∧
    (∀ role < 2, extractBufTrie (fl.trieL role) s'.mem = extractBufTrie (fl.trieL role) s.mem) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  dsimp only
  set s' := (Memory.spec 0).clientState s (fastWriteBktLaneProg ((fl.pBase, (b, lane)), val))
  have hfr : s'.frontier = s.frontier :=
    runClient_frontier_fastWriteBktLaneProg ((fl.pBase, (b, lane)), val) s
  have ⟨hv, hpt, _, _⟩ := hr
  have hmv := hv.mp_valid
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  by_cases hcond : b < numBucketsWhp fl.N ∧ (lane = 5 ∨ (12 ≤ lane ∧ lane < 16)) ∧ val ≤ fl.N
  · obtain ⟨hb, hlane, hval⟩ := hcond
    have hst : s' = ⟨writePacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N)
        fl.w s.mem (16 * b + lane) val, s.frontier⟩ :=
      clientState_fastWriteBktLaneProg hpt hb hlane hval
    have hidx : 16 * b + lane < 16 * numBucketsWhp fl.N := by omega
    have hout_bkt : ∀ addr, ¬(fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr ∧
        addr < fl.metaBase + offBktMeta fl.c fl.w fl.N +
          packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w) →
        s'.mem addr = s.mem addr := fun addr ha => by
      rw [hst]; exact writePacked_outside hw_pos s.mem hidx val ha
    have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr := fun addr ha =>
      hout_bkt addr fun hb_in => ha (Or.inr (Or.inl ⟨hb_in.1, by
        have hd1 := hmv.offSlabDir_ge; dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hd1
        unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
          offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
        omega⟩))
    have hout_io : ∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr := fun addr hia =>
      hout_bkt addr fun hb_in => hv.disj_fast_io addr (Or.inr ⟨by
        have := hmv.offBktMeta_ge; dsimp [FastEpochLayout.mp, epochBpMetaLayout] at this; omega,
        by
          have hd1 := hmv.offSlabDir_ge; dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hd1
          unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
            offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
          omega⟩) hia
    have hslot_ne : ∀ idx < 16 * numBucketsWhp fl.N, idx ≠ 16 * b + lane →
        readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s'.mem idx =
          readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N)
            (globalPtrBits fl.N) fl.w s.mem idx :=
      fun idx _ hne => by rw [hst]; exact readPacked_writePacked_of_ne hw_pos s.mem hne val
    have hbp_eq : extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem := by
      have hd1 := hmv.offSlabDir_ge; have hd2 := hmv.offTailDir_ge
      have hd3 := hmv.offSlabOwner_ge; have hd4 := hmv.offTailOwner_ge
      have ho32 := hmv.offBktMeta_ge
      dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hd1 hd2 hd3 hd4 ho32
      have hsd : ∀ idx < fl.mp.M * fl.mp.maxSlabs,
          readPacked (fl.mp.metaBase + fl.mp.offSlabDir) fl.mp.ptrB fl.mp.w s'.mem idx =
            readPacked (fl.mp.metaBase + fl.mp.offSlabDir) fl.mp.ptrB fl.mp.w s.mem idx :=
        fun idx hi => readPacked_congr hw_pos
          (fun a ha => hout_bkt a (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))
          hi
      have htd : ∀ idx < 8 * fl.mp.M * fl.mp.K,
          readPacked (fl.mp.metaBase + fl.mp.offTailDir) fl.mp.ptrB fl.mp.w s'.mem idx =
            readPacked (fl.mp.metaBase + fl.mp.offTailDir) fl.mp.ptrB fl.mp.w s.mem idx :=
        fun idx hi => readPacked_congr hw_pos
          (fun a ha => hout_bkt a (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))
          hi
      have hso : ∀ idx < 4 * fl.mp.maxBlocks,
          readPacked (fl.mp.metaBase + fl.mp.offSlabOwner) fl.mp.ptrB fl.mp.w s'.mem idx =
            readPacked (fl.mp.metaBase + fl.mp.offSlabOwner) fl.mp.ptrB fl.mp.w s.mem idx :=
        fun idx hi => readPacked_congr hw_pos
          (fun a ha => hout_bkt a (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))
          hi
      have hto : ∀ idx < 16 * fl.mp.maxTail,
          readPacked (fl.mp.metaBase + fl.mp.offTailOwner) fl.mp.ptrB fl.mp.w s'.mem idx =
            readPacked (fl.mp.metaBase + fl.mp.offTailOwner) fl.mp.ptrB fl.mp.w s.mem idx :=
        fun idx hi => readPacked_congr hw_pos
          (fun a ha => hout_bkt a (by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at ha; omega))
          hi
      have hs04 : ∀ b' < numBucketsWhp fl.N, ∀ s0 < 5,
          readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s'.mem
            (16 * b' + s0) =
          readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w s.mem
            (16 * b' + s0) := fun b' hb' s0 hs0 =>
        hslot_ne _ (by omega) (by omega)
      unfold extractBlockPool
      dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hsd htd hso hto ⊢
      congr 1
      · exact hout_bkt _ (by omega)
      · ext x; by_cases hx : x < numBucketsWhp fl.N <;>
          [simpa [hx] using hs04 x hx 0 (by decide); simp [hx]]
      · ext x; by_cases hx : x < numBucketsWhp fl.N <;>
          [simpa [hx] using hs04 x hx 1 (by decide); simp [hx]]
      · ext x; by_cases hx : x < numBucketsWhp fl.N <;>
          [simpa [hx] using hs04 x hx 2 (by decide); simp [hx]]
      · ext x; by_cases hx : x < numBucketsWhp fl.N <;>
          [simpa [hx] using hs04 x hx 3 (by decide); simp [hx]]
      · ext x; by_cases hx : x < numBucketsWhp fl.N <;>
          [simpa [hx] using hs04 x hx 4 (by decide); simp [hx]]
      · ext x y
        by_cases hxy : x < numBucketsWhp fl.N ∧ y < maxSlabsPerBktWhp fl.N
        · have hlt : x * maxSlabsPerBktWhp fl.N + y <
              numBucketsWhp fl.N * maxSlabsPerBktWhp fl.N := by
            calc x * maxSlabsPerBktWhp fl.N + y
                < (x + 1) * maxSlabsPerBktWhp fl.N := by ring_nf; omega
              _ ≤ numBucketsWhp fl.N * maxSlabsPerBktWhp fl.N := Nat.mul_le_mul_right _ hxy.1
          simp [hxy, hsd _ hlt]
        · simp [hxy]
      · ext x y
        by_cases hxy : x < numBucketsWhp fl.N ∧ y < 6 * slabSizeWhp fl.N
        · have hlt : 6 * slabSizeWhp fl.N * x + y <
              8 * numBucketsWhp fl.N * slabSizeWhp fl.N := by
            calc 6 * slabSizeWhp fl.N * x + y
                < 6 * slabSizeWhp fl.N * (x + 1) := by ring_nf; omega
              _ ≤ 6 * slabSizeWhp fl.N * numBucketsWhp fl.N := Nat.mul_le_mul_left _ hxy.1
              _ ≤ 8 * numBucketsWhp fl.N * slabSizeWhp fl.N := by nlinarith
          simp [hxy, htd _ hlt]
        · simp [hxy]
      · ext x
        by_cases hx : x < fl.N / slabSizeWhp fl.N + 4
        · have hlt : 4 * x < 4 * (fl.N / slabSizeWhp fl.N + 4) := by omega
          simp [hx, hso (4 * x) hlt]
        · simp [hx]
      · ext x
        by_cases hx : x < fl.N / slabSizeWhp fl.N + 4
        · have hlt : 4 * x + 1 < 4 * (fl.N / slabSizeWhp fl.N + 4) := by omega
          simp [hx, hso (4 * x + 1) hlt]
        · simp [hx]
      · ext x
        by_cases hx : x < fl.N / slabSizeWhp fl.N + 4
        · have hlt : 4 * x + 2 < 4 * (fl.N / slabSizeWhp fl.N + 4) := by omega
          simp [hx, hso (4 * x + 2) hlt]
        · simp [hx]
      · exact hout_bkt _ (by omega)
      · ext x
        by_cases hx : x < fl.N / slabSizeWhp fl.N + 4
        · have hlt : 4 * x + 3 < 4 * (fl.N / slabSizeWhp fl.N + 4) := by omega
          simp [hx, hso (4 * x + 3) hlt]
        · simp [hx]
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
      · ext x
        by_cases hx : x < 8 * numBucketsWhp fl.N
        · have hK64 := hmv.K_ge; dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hK64
          have hlt : 6 * numBucketsWhp fl.N * slabSizeWhp fl.N + x <
              8 * numBucketsWhp fl.N * slabSizeWhp fl.N := by nlinarith
          simp [hx, htd _ hlt]
        · simp [hx]
      · ext x
        by_cases hx : x < 8 * numBucketsWhp fl.N
        · have hK64 := hmv.K_ge; dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hK64
          have hlt : 7 * numBucketsWhp fl.N * slabSizeWhp fl.N + x <
              8 * numBucketsWhp fl.N * slabSizeWhp fl.N := by nlinarith
          simp [hx, htd _ hlt]
        · simp [hx]
      · ext x
        by_cases hx : x < 8 * numBucketsWhp fl.N * slabSizeWhp fl.N
        · have h16mt := hmv.sixteen_MK_le_maxTail
          dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at h16mt
          have hlt : x < 16 * maxTailWhp fl.N := by nlinarith
          simp [hx, hto x hlt]
        · simp [hx]
      · ext x
        by_cases hx : x < 8 * numBucketsWhp fl.N * slabSizeWhp fl.N
        · have h16mt := hmv.sixteen_MK_le_maxTail
          dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at h16mt
          have hlt : 8 * numBucketsWhp fl.N * slabSizeWhp fl.N + x <
              16 * maxTailWhp fl.N := by nlinarith
          simp [hx, hto _ hlt]
        · simp [hx]
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
      · exact hout_bkt _ (by omega)
    have hbt_eq : ∀ b' < numBucketsWhp fl.N, ∀ role < 3,
        extractBTreeSlice fl.btL b' role s'.mem = extractBTreeSlice fl.btL b' role s.mem := by
      intro b' hb' role hrole
      have hd_bt : offBktMeta fl.c fl.w fl.N +
          packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w ≤
          offBTreeMeta fl.c fl.w fl.N := by
        unfold offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir; omega
      have hd_k : offBTreeMeta fl.c fl.w fl.N ≤ offBTreeKeys fl.c fl.w fl.N :=
        Nat.le_add_right _ _
      have hd_v : offBTreeKeys fl.c fl.w fl.N ≤ offBTreeVals fl.c fl.w fl.N :=
        Nat.le_add_right _ _
      refine extractBTreeSlice_congr_entries
        (by dsimp only [FastEpochLayout.btL, epochBTreeLayout]
            exact hslot_ne _ (by omega) (by omega))
        (by dsimp only [FastEpochLayout.btL, epochBTreeLayout]
            exact hslot_ne _ (by omega) (by omega))
        fun u hu => ?_
      dsimp only [FastEpochLayout.btL, epochBTreeLayout] at hu ⊢
      have htot : (3 * b' + role) * nSliceWhp fl.N + u < totalBTreeNodesWhp fl.N := by
        unfold totalBTreeNodesWhp
        calc (3 * b' + role) * nSliceWhp fl.N + u
            < (3 * b' + role + 1) * nSliceWhp fl.N := by ring_nf; omega
          _ ≤ (3 * numBucketsWhp fl.N) * nSliceWhp fl.N := Nat.mul_le_mul_right _ (by omega)
      exact ⟨readPacked_congr hw_pos (fun a ha => hout_bkt a (by omega)) htot,
        readPacked_congr hw_pos (fun a ha => hout_bkt a (by omega)) htot,
        readPacked_congr hw_pos (fun a ha => hout_bkt a (by omega)) htot⟩
    have htr_eq : ∀ role < 2,
        extractBufTrie (fl.trieL role) s'.mem = extractBufTrie (fl.trieL role) s.mem := by
      intro role _
      refine extractBufTrie_congr hw_pos fun addr ha => hout_bkt addr fun hb_in => ?_
      dsimp only [FastEpochLayout.trieL, epochTrieLayout, TrieLayout.OwnsAddr] at ha
      have hd_tr : offBktMeta fl.c fl.w fl.N +
          packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w ≤
          offTrieChild fl.c fl.w fl.N 0 := by
        unfold offTrieChild offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner
          offTailDir offSlabDir
        omega
      have hc01 : offTrieChild fl.c fl.w fl.N 0 ≤ offTrieChild fl.c fl.w fl.N role := by
        unfold offTrieChild; omega
      have hn01 : offTrieChild fl.c fl.w fl.N 0 ≤ offTrieNode fl.c fl.w fl.N role := by
        unfold offTrieNode offTrieChild; omega
      have hi01 : offTrieChild fl.c fl.w fl.N 0 ≤ offTrieItem fl.c fl.w fl.N role := by
        unfold offTrieItem offTrieNode offTrieChild; omega
      rcases ha with h1 | h2 | h3 <;> omega
    exact ⟨hfr, hr.of_frame hfr hout_fast, hbp_eq, hbt_eq, htr_eq, hout_fast, hout_io⟩
  · have hst : s' = s := by
      dsimp only [s', StateTransitionSpec.clientState]
      unfold fastWriteBktLaneProg
      simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        prog_clientResult_read, prog_runClient_state_read, hpt 11 (by decide),
        hpt 0 (by decide), FastEpochLayout.paramWord, hcond, ↓reduceIte,
        prog_runClient_state_pure]
    rw [hst]
    exact ⟨rfl, hr, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem realizesBounded_fastWriteBktLane :
    RealizesBounded .exact fastWriteBktLaneProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrp := realizesBounded_readParamPair
  have hwk := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, lane⟩⟩, val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    obtain ⟨hv, hpt, _, _⟩ := hr
    have hmv := hv.mp_valid
    have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
    have hm0' : s.mem (fl.pBase + 0) = fl.N := hpt 0 (by decide)
    have hm0 : s.mem fl.pBase = fl.N := by rwa [Nat.add_zero] at hm0'
    have hm1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
    have hm31 : s.mem (fl.pBase + 31) = offBktMeta fl.c fl.w fl.N := hpt 31 (by decide)
    have hm10 : s.mem (fl.pBase + 10) = globalPtrBits fl.N := hpt 10 (by decide)
    have hm2 : s.mem (fl.pBase + 2) = fl.w := hpt 2 (by decide)
    have h16M_w : 16 * numBucketsWhp fl.N < 2 ^ w :=
      lt_of_le_of_lt hmv.sixteen_M_le hmv.nCap_lt_two_pow_w
    have hnCap_w : fl.N < 2 ^ w := hmv.nCap_lt_two_pow_w
    dsimp only [Fits] at hfr_w ⊢
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readParamPairProg] at *
    first | exact hw6 | exact hp | decide | omega | (
      have hidx : 16 * b + lane < 16 * numBucketsWhp fl.N := by omega
      have hpr : ((Memory.spec 0).runClient s (readParamPairProg (fl.pBase, (10, 2)))).1 =
          (globalPtrBits fl.N, fl.w) := by
        unfold readParamPairProg; simp [hm10, hm2]
      simp only [StateTransitionSpec.clientResult, hm1, hm31, hpr]
      refine ⟨16 * numBucketsWhp fl.N, hv.w_pos, hv.w_eq, hmv.ptrB_le, hidx, ?_⟩
      have hd1 := hmv.offSlabDir_ge; have hd2 := hmv.offTailDir_ge
      have hd3 := hmv.offSlabOwner_ge; have hd4 := hmv.offTailOwner_ge
      have hdf := hmv.frontier_ge
      dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hd1 hd2 hd3 hd4 hdf
      cases hv.w_eq
      omega))

/-- Read `(q, v)` at `(b, loc)` in `BlockPool` via `pBase` (`¬ReadsWidth`). -/
def fastBpReadAtProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (pBase, (b, loc)) => do
    let bpCtx ← loadBlockPoolCtxProg pBase
    let phys ← bpToPhysProg (bpCtx.1, (b, loc))
    slotIoReadRawProg (bpCtx.2, phys)

@[simp] theorem runClient_state_fastBpReadAtProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastBpReadAtProg x)) = s := by
  rcases x with ⟨pBase, ⟨b, loc⟩⟩
  change (Memory.spec 0).clientState s (fastBpReadAtProg (pBase, (b, loc))) = s
  unfold fastBpReadAtProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
    StateTransitionSpec.clientState_bind, clientState_bpToPhysProg]
  exact clientState_slotIoReadRawProg _ s

theorem clientState_fastBpReadAtProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastBpReadAtProg x) = s :=
  runClient_state_fastBpReadAtProg x s

theorem fastBpReadAtProg_spec
    {fl : FastEpochLayout} {w slack b loc : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hinv : fl.bpL.StateInv slack s.mem)
    (hb : b < fl.mp.M) (hloc : loc < (extractBlockPool fl.mp s.mem).bktCount b) :
    (Memory.spec 0).clientState s (fastBpReadAtProg (fl.pBase, (b, loc))) = s ∧
    (Memory.spec 0).clientResult s (fastBpReadAtProg (fl.pBase, (b, loc))) =
      bpPairAt fl.bpL s.mem b loc ∧
    memoryCost (fastBpReadAtProg (fl.pBase, (b, loc))) s ≤ 71 := by
  refine ⟨clientState_fastBpReadAtProg _ s, ?_⟩
  unfold fastBpReadAtProg; dsimp only
  rw [prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_loadBlockPoolCtxProg, clientResult_loadBlockPoolCtxProg hr.2.1,
    memoryCost_loadBlockPoolCtxProg]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  have htp_res := bpToPhysProg_spec hinv.1.core hinv.2.1 hb hloc
  have htp_c := (bpToPhysProg_frame fl.mp b loc).frame.cost_le s
  have hp_lt := hinv.1.core.toPhys_lt hb hloc
  obtain ⟨hr_res, _⟩ := slotIoReadProg_spec hinv.2.2 hp_lt
  have hr_c := (slotIoReadProg_frame fl.io
    ((extractBlockPool fl.mp s.mem).toPhys b loc)).cost_le s
  unfold slotIoReadProg at hr_res hr_c
  dsimp only [FastEpochLayout.bpL] at htp_res hr_res ⊢
  rw [prog_clientResult_bind, Realization.memoryCost_bind', clientState_bpToPhysProg, htp_res]
  exact ⟨hr_res, by omega⟩

theorem realizesBounded_fastBpReadAt :
    RealizesBounded .exact fastBpReadAtProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlb := realizesBounded_loadBlockPoolCtx
  have htp := realizesBounded_bpToPhys
  have hrr := realizesBounded_slotIoReadRaw
  realize
  all_goals (
    rcases d with ⟨pBase, ⟨b, loc⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    try simp only [StateTransitionSpec.clientState, runClient_state_loadBlockPoolCtxProg,
      runClient_state_bpToPhysProg] at *
    first | exact hw6 | exact hp | (
      have hl_res := clientResult_loadBlockPoolCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
      first | (rw [BpMetaLayout.ofCtx_toCtx]; exact hr.1.mp_valid)
            | (rw [SlotIoLayout.ofCtx_toCtx]; exact hr.1.io_valid)))

/-- Read `bp.bktCount b` via `pBase` (`¬ReadsWidth`). -/
def fastBpBktCountProg : ℕ × ℕ → Memory.Prog ℕ
  | (pBase, b) => do
    let mctx ← loadBpMetaCtxProg pBase
    bpReadBktCountProg (mctx, b)

theorem clientState_fastBpBktCountProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastBpBktCountProg x) = s := by
  rcases x with ⟨pBase, b⟩
  unfold fastBpBktCountProg
  rw [StateTransitionSpec.clientState_bind, clientState_loadBpMetaCtxProg]
  exact clientState_bpReadBktCountProg _ s

theorem realizesBounded_fastBpBktCount :
    RealizesBounded .exact fastBpBktCountProg
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

/-! ## Section 4: Pure `FastEpochMeta`, 3-Tier `FastEpochInv`, and Read-Only `fastQueryProg` -/

/-- Pure snapshot of the fast-path scalar and per-bucket (`5, 12..15`) control lanes (`0`
projection chains). -/
structure FastEpochMeta where
  /-- Active `BufCur` trie role (`0` or `1`; scalar offset `metaBase + 3`). -/
  curBufRole : ℕ
  /-- Current sub-epoch step counter in `[0, qEpochWhp N)` (scalar offset `metaBase + 4`). -/
  subStep : ℕ
  /-- Next `BufOld` item slot to drain during `subStep < Q / 2` (scalar offset `metaBase + 5`). -/
  drainPos : ℕ
  /-- Candidate salt-search active flag (`0` inactive, `1` active; scalar offset `metaBase + 6`). -/
  tryAct : ℕ
  /-- Target bucket index of the active candidate salt search (scalar offset `metaBase + 7`). -/
  tryBkt : ℕ
  /-- Candidate salt value currently being tested for `tryBkt` (scalar offset `metaBase + 8`). -/
  trySalt : ℕ
  /-- Next bucket-local slot to insert into `tryRoleOf` (scalar offset `metaBase + 9`). -/
  tryPos : ℕ
  /-- Number of insertions performed on the `tryRoleOf` B+-tree (scalar offset `metaBase + 17`). -/
  tryIns : ℕ
  /-- Per-bucket active fingerprint salt (lane `5` of `offBktMeta`). -/
  bktSalt : ℕ → ℕ
  /-- Per-bucket active B+-tree slice role in `{0, 1, 2}` (lane `12` of `offBktMeta`). -/
  curRole : ℕ → ℕ
  /-- Per-bucket insertion counter for the active `curRole` B+-tree (lane `13` of `offBktMeta`). -/
  curIns : ℕ → ℕ
  /-- Per-bucket insertion counter for the `shadowRoleOf` B+-tree (lane `14` of `offBktMeta`). -/
  shadowIns : ℕ → ℕ
  /-- Per-bucket encoded shadow-compaction state word (lane `15` of `offBktMeta`). -/
  shadowCode : ℕ → ℕ

/-- Extract `FastEpochMeta` from memory `mem` at `fl`. -/
@[expose] def extractFastMeta (fl : FastEpochLayout) (mem : ℕ → ℕ) : FastEpochMeta where
  curBufRole := mem (fl.metaBase + 3)
  subStep := mem (fl.metaBase + 4)
  drainPos := mem (fl.metaBase + 5)
  tryAct := mem (fl.metaBase + 6)
  tryBkt := mem (fl.metaBase + 7)
  trySalt := mem (fl.metaBase + 8)
  tryPos := mem (fl.metaBase + 9)
  tryIns := mem (fl.metaBase + 17)
  bktSalt := fun b =>
    if b < numBucketsWhp fl.N then
      readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w mem
        (16 * b + 5)
    else 0
  curRole := fun b =>
    if b < numBucketsWhp fl.N then
      readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w mem
        (16 * b + 12)
    else 0
  curIns := fun b =>
    if b < numBucketsWhp fl.N then
      readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w mem
        (16 * b + 13)
    else 0
  shadowIns := fun b =>
    if b < numBucketsWhp fl.N then
      readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w mem
        (16 * b + 14)
    else 0
  shadowCode := fun b =>
    if b < numBucketsWhp fl.N then
      readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w mem
        (16 * b + 15)
    else 0

/-- Shadow compaction role `(curRole + 1) % 3` of bucket `b`. -/
@[expose] def shadowRoleOf (r : ℕ) : ℕ :=
  if r = 0 then 1 else if r = 1 then 2 else 0

/-- Candidate salt-search role `(curRole + 2) % 3` of bucket `b`. -/
@[expose] def tryRoleOf (r : ℕ) : ℕ :=
  if r = 0 then 2 else if r = 1 then 0 else 1

theorem shadowRoleOf_lt_and_ne {r : ℕ} (hr : r < 3) :
    shadowRoleOf r < 3 ∧ shadowRoleOf r ≠ r := by
  unfold shadowRoleOf; rcases r with _ | _ | _ | _ <;> first | decide | omega

theorem tryRoleOf_lt_and_ne {r : ℕ} (hr : r < 3) :
    tryRoleOf r < 3 ∧ tryRoleOf r ≠ r ∧ tryRoleOf r ≠ shadowRoleOf r := by
  unfold tryRoleOf shadowRoleOf; rcases r with _ | _ | _ | _ <;> first | decide | omega

/-- Reconstructed key stored at `(b, loc)` in `fl.bpL`. -/
@[expose] def fastKeyAt (fl : FastEpochLayout) (θ_bkt : BktSeed fl.c fl.U fl.N) (mem : ℕ → ℕ)
    (b loc : ℕ) : ℕ :=
  feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt) b (bpPairAt fl.bpL mem b loc).1

/-- Master 3-tier representation invariant `FastEpochInv` (`fallbackMode = 0`):
couples `BlockPoolLayout.StateInv`, `PoolItemsRefines`, `BufCur`, `BufOld` (`ValidBufTrie` in the
drain half `subStep < Q / 2`; `ClearableBufTrie` in `Q / 2 ≤ subStep < Q`), per-bucket
`ValidWhpSlice` (`curRole`), deamortized shadow compaction (`shadowRoleOf`), and candidate salt
search (`tryRoleOf`) with exact pairwise-disjoint 3-tier partition of all live `(b, loc)` pairs. -/
structure FastEpochInv (fl : FastEpochLayout) (slack : ℕ)
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
      -- Tier 1 (`BufCur`)
      ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N) curTr mapCur ∧
      RawBufTrieBounds curTr ∧
      RawClearableBounds curTr ∧
      curTr.itemAlloc ≤ fm.subStep ∧
      curTr.nodeAlloc ≤ 1 + cTabWhp fl.c * curTr.itemAlloc ∧
      (∀ rk b loc, mapCur rk = some (b, loc) →
        b < numBucketsWhp fl.N ∧ loc < bp.bktCount b ∧
        ∃ u : Fin fl.U, rKeyOf fl.c fl.U fl.N seeds.fp u = rk ∧
          fastKeyAt fl seeds.bkt mem b loc = u.val) ∧
      -- Tier 2 (`BufOld`: draining in `[0, Q / 2)`, clearing in `[Q / 2, Q)`)
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
      -- Tier 3 (`BTree(b, curRole b)`)
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
      -- Completeness across all live `(b, loc)` slots
      (∀ (b : ℕ) (hb : b < numBucketsWhp fl.N), ∀ loc < bp.bktCount b,
        ∃ u : Fin fl.U,
          fastKeyAt fl seeds.bkt mem b loc = u.val ∧
          (mapCur (rKeyOf fl.c fl.U fl.N seeds.fp u) = some (b, loc) ∨
            mapOld (rKeyOf fl.c fl.U fl.N seeds.fp u) = some (b, loc) ∨
            mapBTree b (fpHash fl.c fl.U fl.N seeds.fp
              ⟨fm.bktSalt b, (bkt_meta_bounds b hb).1⟩ u).val = some loc)) ∧
      -- Deamortized shadow compaction invariant (`shadowCode b = 1 + shPos`)
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
      -- Candidate salt-search invariant (`tryAct ≤ 1`)
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

theorem FastEpochInv.ready {fl : FastEpochLayout} {w fr _slack : ℕ}
    {_seeds : EpochHashSeeds fl.c fl.U fl.N} {s : Memory.State}
    {_s_abs : Fin fl.U → Option (Fin fl.V)}
    (hv : fl.Valid w fr) (hfr : fr = s.frontier)
    (hinv : FastEpochInv fl _slack _seeds s.mem _s_abs) :
    FastLayoutReady w fl s :=
  ⟨hfr ▸ hv, hinv.param_table, hinv.seed_bkt.1 ▸ _seeds.bkt.1.isLt,
    hinv.seed_fp.1 ▸ _seeds.fp.1.isLt⟩

theorem FastEpochInv.bktSlot_refines {fl : FastEpochLayout} {slack b loc : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hinv : FastEpochInv fl slack seeds mem s_abs)
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
  have hb_M : b < fl.mp.M := hb
  set p := (extractBlockPool fl.mp mem).toPhys b loc
  have hp_lt : p < (extractBlockPool fl.mp mem).nSide := hcv.toPhys_lt hb_M hloc
  have how_p : ((extractBlockPool fl.mp mem).ownerOf p).1 = b := by
    rw [hcv.ownerOf_toPhys hb_M hloc]
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

theorem FastEpochInv.key_iff_bktQuot {fl : FastEpochLayout} {slack b loc : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hinv : FastEpochInv fl slack seeds mem s_abs)
    (hb : b < numBucketsWhp fl.N) (hloc : loc < (extractBlockPool fl.mp mem).bktCount b)
    (u : Fin fl.U) :
    (b = epochBucket fl.c fl.U fl.N seeds.bkt u ∧
      (bpPairAt fl.bpL mem b loc).1 = keyQuotient (bWhp fl.N) u.val) ↔
    fastKeyAt fl seeds.bkt mem b loc = u.val := by
  obtain ⟨u', _, hu'_val, _, hb_u', hq_u', _⟩ := hinv.bktSlot_refines hb hloc
  constructor
  · rintro ⟨rfl, hq_eq⟩
    unfold fastKeyAt
    rw [hq_eq]
    exact feistelReconstruct_epochBucket fl.c fl.U fl.N seeds.bkt u
  · intro hkey_eq
    have hu_eq : u' = u := Fin.ext (hu'_val.trans hkey_eq)
    subst hu_eq
    exact ⟨hb_u'.symm, hq_u'.symm⟩

/-! ### Read-Only 3-Tier Probe (`fastProbeProg`) and `fastQueryProg` -/

/-- Probe one `BufTrie` copy (`role ∈ {0, 1}`) at `rk` and verify whether the returned `(b', loc')`
matches `(b, q_u)` in `BlockPool`, returning `(hitFlag, (collFlag, (loc', val')))` (`¬ReadsWidth`).
-/
private def fastCheckTrieRoleProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) →
    Memory.Prog (ℕ × (ℕ × (ℕ × ℕ)))
  | ((pBase, role), (rk, (b, q_u))) => do
    let tctx ← loadTrieCtxProg (pBase, role)
    let lk ← bufLookupBoundedProg (tctx, rk)
    if lk.1 = 1 then do
      let qv ← fastBpReadAtProg (pBase, lk.2)
      if lk.2.1 = b then
        if qv.1 = q_u then
          pure (1, (0, (lk.2.2, qv.2)))
        else
          pure (0, (1, (0, 0)))
      else
        pure (0, (1, (0, 0)))
    else
      pure (0, (0, (0, 0)))

@[simp] private theorem runClient_state_fastCheckTrieRoleProg
    (x : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    ((Memory.spec 0).runClient s (fastCheckTrieRoleProg x)).2.1 = s := by
  rcases x with ⟨⟨pBase, role⟩, ⟨rk, ⟨b, q_u⟩⟩⟩
  change (Memory.spec 0).clientState s (fastCheckTrieRoleProg ((pBase, role), (rk, (b, q_u)))) = s
  unfold fastCheckTrieRoleProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_loadTrieCtxProg,
    StateTransitionSpec.clientState_bind, clientState_bufLookupBoundedProg]
  by_cases h1 : ((Memory.spec 0).clientResult s
      (bufLookupBoundedProg ((Memory.spec 0).clientResult s
        (loadTrieCtxProg (pBase, role)), rk))).1 = 1
  · rw [ite_eq_left h1, StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg]
    split_ifs <;> rfl
  · rw [ite_eq_right h1]; rfl

private theorem clientState_fastCheckTrieRoleProg
    (x : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastCheckTrieRoleProg x) = s :=
  runClient_state_fastCheckTrieRoleProg x s

private theorem realizesBounded_fastCheckTrieRole :
    RealizesBounded .exact fastCheckTrieRoleProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ))))
      (fun w ((pBase, role), _) s => role < 2 ∧ FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlt := realizesBounded_loadTrieCtx
  have hbl := realizesBounded_bufLookup
  have hra := realizesBounded_fastBpReadAt
  realize
  all_goals (
    rcases d with ⟨⟨pBase, role⟩, ⟨rk, ⟨b, q_u⟩⟩⟩
    obtain ⟨hrole, fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_loadTrieCtxProg,
      runClient_state_bufLookupBoundedProg] at *
    first | exact hw6 | exact hp | omega | exact ⟨fl, rfl, hr⟩ | (
      have hl_res := clientResult_loadTrieCtxProg (s := s) hr.2.1 hrole
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      have htv := hr.1.trie_valid hrole
      rw [← hr.1.w_eq] at htv
      simpa [BufLookupPre] using htv))

/-- Inner slice lookup & quotient verification for `fastCheckBTreeProg` (`≤ 3` binds). -/
private def fastCheckBTreeSliceProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((pBase, (b, role)), (fp, q_u)) => do
    let sctx ← loadBTreeSliceCtxProg (pBase, (b, role))
    let lk ← btreeLookupBoundedProg (sctx, fp)
    if lk.1 = 1 then do
      let qv ← fastBpReadAtProg (pBase, (b, lk.2))
      if qv.1 = q_u then
        pure (1, (lk.2, qv.2))
      else
        pure (0, (0, 0))
    else
      pure (0, (0, 0))

@[simp] private theorem runClient_state_fastCheckBTreeSliceProg
    (x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (fastCheckBTreeSliceProg x)).2.1 = s := by
  rcases x with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨fp, q_u⟩⟩
  change (Memory.spec 0).clientState s
    (fastCheckBTreeSliceProg ((pBase, (b, role)), (fp, q_u))) = s
  unfold fastCheckBTreeSliceProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_loadBTreeSliceCtxProg,
    StateTransitionSpec.clientState_bind, clientState_btreeLookupBoundedProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg]
    split_ifs <;> rfl
  · rfl

private theorem clientState_fastCheckBTreeSliceProg
    (x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastCheckBTreeSliceProg x) = s :=
  runClient_state_fastCheckBTreeSliceProg x s

private theorem realizesBounded_fastCheckBTreeSlice :
    RealizesBounded .exact fastCheckBTreeSliceProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((pBase, (b, role)), (fp, _)) s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ FastLayoutReady w fl s ∧
          b < numBucketsWhp fl.N ∧ role < 3 ∧ fp < 2 ^ fpBitsWhp fl.N)
      (fun _ _ => 0) := by
  have hls := realizesBounded_loadBTreeSliceCtx
  have hbl := realizesBounded_btreeLookup
  have hra := realizesBounded_fastBpReadAt
  realize
  all_goals (
    rcases d with ⟨⟨pBase, ⟨b, role⟩⟩, ⟨fp, q_u⟩⟩
    obtain ⟨fl, rfl, hr, hb, hrole, hfp⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_loadBTreeSliceCtxProg,
      runClient_state_btreeLookupBoundedProg] at *
    first | exact hw6 | exact hp | omega | exact ⟨fl, rfl, hr⟩ | (
      have hl_res := clientResult_loadBTreeSliceCtxProg (s := s) (b := b) (role := role) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res]
      have hbtv := hr.1.bt_valid; rw [← hr.1.w_eq] at hbtv
      dsimp only [BTreeKeyOpPre, BTreeSlicePre, unpackSliceCtx, BTreeEpochLayout.toSliceCtx]
      exact ⟨⟨hbtv, hb, hrole⟩, hfp⟩))

/-- Fingerprint evaluation & slice dispatch for `fastCheckBTreeProg` (`2` binds). -/
private def fastCheckBTreeFpProg :
    ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | (((pBase, u_val), (b, q_u)), (role, salt)) =>
    if role < 3 then do
      let sr ← readParamPairProg (pBase, (9, 2))
      if sr.1 < sr.2 then do
        let fp ← fastFpHashProg (pBase, (salt, u_val))
        if fp < (1 <<< sr.1) then
          fastCheckBTreeSliceProg ((pBase, (b, role)), (fp, q_u))
        else
          pure (0, (0, 0))
      else
        pure (0, (0, 0))
    else
      pure (0, (0, 0))

@[simp] private theorem runClient_state_fastCheckBTreeFpProg
    (x : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (fastCheckBTreeFpProg x)).2.1 = s := by
  rcases x with ⟨⟨⟨pBase, u_val⟩, ⟨b, q_u⟩⟩, ⟨role, salt⟩⟩
  change (Memory.spec 0).clientState s
    (fastCheckBTreeFpProg (((pBase, u_val), (b, q_u)), (role, salt))) = s
  unfold fastCheckBTreeFpProg; dsimp only
  have hsr : (Memory.spec 0).clientState s (readParamPairProg (pBase, (9, 2))) = s := rfl
  by_cases hr : role < 3
  · rw [ite_eq_left hr, StateTransitionSpec.clientState_bind, hsr]
    by_cases hlt : ((Memory.spec 0).clientResult s (readParamPairProg (pBase, (9, 2)))).1 <
        ((Memory.spec 0).clientResult s (readParamPairProg (pBase, (9, 2)))).2
    · rw [ite_eq_left hlt, StateTransitionSpec.clientState_bind, clientState_fastFpHashProg]
      split_ifs
      · exact clientState_fastCheckBTreeSliceProg _ s
      · rfl
    · rw [ite_eq_right hlt]; rfl
  · rw [ite_eq_right hr]; rfl

private theorem realizesBounded_fastCheckBTreeFp :
    RealizesBounded .exact fastCheckBTreeFpProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (((pBase, _), (b, _)), _) s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ FastLayoutReady w fl s ∧
          b < numBucketsWhp fl.N)
      (fun _ _ => 0) := by
  have hrp := realizesBounded_readParamPair
  have hfp := realizesBounded_fastFpHash
  have hsl := realizesBounded_fastCheckBTreeSlice
  realize
  all_goals (
    rcases d with ⟨⟨⟨pBase, u_val⟩, ⟨b, q_u⟩⟩, ⟨role, salt⟩⟩
    obtain ⟨fl, rfl, hr, hb⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hpt := hr.2.1
    have hw_eq := hr.1.w_eq
    have hsr : ((Memory.spec 0).runClient s (readParamPairProg (fl.pBase, (9, 2)))).1 =
        (fpBitsWhp fl.N, fl.w) := by
      unfold readParamPairProg
      simp [hpt 9 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
      runClient_state_readParamPairProg, runClient_state_fastFpHashProg, hsr] at *
    first | exact hw6 | exact hp | decide | omega | exact ⟨fl, rfl, hr⟩ | (
      try rw [Nat.shiftLeft_eq, one_mul]
      have hfp_lt_w : fpBitsWhp fl.N < w := by omega
      exact Nat.pow_lt_pow_right Nat.one_lt_two hfp_lt_w) | (
      have hrole_lt : role < 3 := by assumption
      refine ⟨fl, rfl, hr, hb, hrole_lt, ?_⟩
      rw [Nat.shiftLeft_eq, one_mul] at *; assumption))

/-- Probe Tier 3 (`BTree(b, curRole b)`) for `(b, q_u)` at key `u_val`, returning
`(hitFlag, (hitLoc, hitVal))` (`¬ReadsWidth`, `3` binds). -/
private def fastCheckBTreeProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((pBase, u_val), (b, q_u)) => do
    let M ← Memory.read (pBase + 11)
    if b < M then do
      let salt ← fastReadBktLaneProg (pBase, (b, 5))
      let role ← fastReadBktLaneProg (pBase, (b, 12))
      fastCheckBTreeFpProg (((pBase, u_val), (b, q_u)), (role, salt))
    else
      pure (0, (0, 0))

@[simp] private theorem runClient_state_fastCheckBTreeProg
    (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (fastCheckBTreeProg x)).2.1 = s := by
  rcases x with ⟨⟨pBase, u_val⟩, ⟨b, q_u⟩⟩
  change (Memory.spec 0).clientState s (fastCheckBTreeProg ((pBase, u_val), (b, q_u))) = s
  unfold fastCheckBTreeProg; dsimp only
  have hm_st : (Memory.spec 0).clientState s (Memory.read (pBase + 11)) = s := rfl
  rw [StateTransitionSpec.clientState_bind, hm_st]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg]
    exact runClient_state_fastCheckBTreeFpProg _ s
  · rfl

private theorem clientState_fastCheckBTreeProg
    (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastCheckBTreeProg x) = s :=
  runClient_state_fastCheckBTreeProg x s

private theorem realizesBounded_fastCheckBTree :
    RealizesBounded .exact fastCheckBTreeProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have hfp := realizesBounded_fastCheckBTreeFp
  realize
  all_goals (
    rcases d with ⟨⟨pBase, u_val⟩, ⟨b, q_u⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hr.2.1 11 (by decide)
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktLaneProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega | exact ⟨fl, rfl, hr, by omega⟩)

/-- Tier-3 tail of `fastProbeProg` (`1` bind). -/
private def fastProbeBTreeTailProg :
    (ℕ × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))
  | ((pBase, u_val), ((b, q_u), coll)) => do
    let c3 ← fastCheckBTreeProg ((pBase, u_val), (b, q_u))
    if c3.1 = 1 then
      pure ((3, coll), (b, c3.2))
    else
      pure ((0, coll), (b, (0, 0)))

@[simp] private theorem runClient_state_fastProbeBTreeTailProg
    (x : (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (fastProbeBTreeTailProg x)).2.1 = s := by
  rcases x with ⟨⟨pBase, u_val⟩, ⟨⟨b, q_u⟩, coll⟩⟩
  unfold fastProbeBTreeTailProg; dsimp only
  rw [prog_runClient_state_bind, clientState_fastCheckBTreeProg]
  split_ifs <;> rfl

private theorem clientState_fastProbeBTreeTailProg
    (x : (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastProbeBTreeTailProg x) = s :=
  runClient_state_fastProbeBTreeTailProg x s

private theorem realizesBounded_fastProbeBTreeTail :
    RealizesBounded .exact fastProbeBTreeTailProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hcb := realizesBounded_fastCheckBTree
  realize
  all_goals (
    rcases d with ⟨⟨pBase, u_val⟩, ⟨⟨b, q_u⟩, coll⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-- Tier-2 + Tier-3 fallback probe after a `BufCur` miss (`curRole < 2`, `≤ 4` binds). -/
private def fastProbeMissCurProg :
    ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))
  | (((pBase, u_val), (curRole, c1Coll)), (bq, rk)) => do
    let sub ← fastReadMetaProg (pBase, 4)
    let qMax ← Memory.read (pBase + 23)
    if sub < (qMax >>> 1) then do
      let oldRole ← pure (1 - curRole)
      let c2 ← fastCheckTrieRoleProg ((pBase, oldRole), (rk, bq))
      if c2.1 = 1 then
        pure ((2, 0), (bq.1, c2.2.2))
      else if c1Coll = 1 then
        fastProbeBTreeTailProg ((pBase, u_val), (bq, 1))
      else if c2.2.1 = 1 then
        fastProbeBTreeTailProg ((pBase, u_val), (bq, 1))
      else
        fastProbeBTreeTailProg ((pBase, u_val), (bq, 0))
    else
      fastProbeBTreeTailProg ((pBase, u_val), (bq, c1Coll))

@[simp] private theorem runClient_state_fastProbeMissCurProg
    (x : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (fastProbeMissCurProg x)).2.1 = s := by
  rcases x with ⟨⟨⟨pBase, u_val⟩, ⟨curRole, c1Coll⟩⟩, ⟨bq, rk⟩⟩
  change (Memory.spec 0).clientState s
    (fastProbeMissCurProg (((pBase, u_val), (curRole, c1Coll)), (bq, rk))) = s
  unfold fastProbeMissCurProg; dsimp only
  have hm_st : (Memory.spec 0).clientState s (Memory.read (pBase + 23)) = s := rfl
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, hm_st]
  by_cases hsub : (Memory.spec 0).clientResult s (fastReadMetaProg (pBase, 4)) <
      (Memory.spec 0).clientResult s (Memory.read (pBase + 23)) >>> 1
  · rw [ite_eq_left hsub, pure_bind, StateTransitionSpec.clientState_bind,
      clientState_fastCheckTrieRoleProg]
    split_ifs <;> first | rfl | exact clientState_fastProbeBTreeTailProg _ s
  · rw [ite_eq_right hsub]
    exact clientState_fastProbeBTreeTailProg _ s

private theorem clientState_fastProbeMissCurProg
    (x : ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastProbeMissCurProg x) = s :=
  runClient_state_fastProbeMissCurProg x s

private theorem realizesBounded_fastProbeMissCur :
    RealizesBounded .exact fastProbeMissCurProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (fun w (((pBase, _), (curRole, _)), _) s => curRole < 2 ∧ FastProgPre w pBase s)
      (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hct := realizesBounded_fastCheckTrieRole
  have htl := realizesBounded_fastProbeBTreeTail
  realize
  all_goals (
    rcases d with ⟨⟨⟨pBase, u_val⟩, ⟨curRole, c1Coll⟩⟩, ⟨⟨b, q_u⟩, rk⟩⟩
    obtain ⟨hcr, fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
      runClient_state_fastReadMetaProg, runClient_state_fastCheckTrieRoleProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

private abbrev checkTrieColl (c : ℕ × (ℕ × (ℕ × ℕ))) : ℕ := c.2.1
private abbrev checkTrieLoc (c : ℕ × (ℕ × (ℕ × ℕ))) : ℕ × ℕ := c.2.2

/-- Full read-only 3-tier probe `fastProbeProg (pBase, u_val)`, returning
`((tierHit, rKeyColl), (b, (hitLoc, hitVal)))` (`¬ReadsWidth`). -/
def fastProbeProg : ℕ × ℕ → Memory.Prog ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))
  | (pBase, u_val) => do
    let bq ← fastFeistelSplitProg (pBase, u_val)
    let rk ← fastRKeyProg (pBase, u_val)
    let curRole ← fastReadMetaProg (pBase, 3)
    if curRole < 2 then do
      let c1 ← fastCheckTrieRoleProg ((pBase, curRole), (rk, bq))
      if c1.1 = 1 then
        pure ((1, 0), (bq.1, checkTrieLoc c1))
      else
        fastProbeMissCurProg (((pBase, u_val), (curRole, checkTrieColl c1)), (bq, rk))
    else
      pure ((0, 0), (bq.1, (0, 0)))

@[simp] theorem runClient_state_fastProbeProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastProbeProg x)) = s := by
  rcases x with ⟨pBase, u_val⟩
  change (Memory.spec 0).clientState s (fastProbeProg (pBase, u_val)) = s
  unfold fastProbeProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastFeistelSplitProg,
    StateTransitionSpec.clientState_bind, clientState_fastRKeyProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  by_cases hcr : (Memory.spec 0).clientResult s (fastReadMetaProg (pBase, 3)) < 2
  · rw [ite_eq_left hcr, StateTransitionSpec.clientState_bind, clientState_fastCheckTrieRoleProg]
    split_ifs
    · rfl
    · exact clientState_fastProbeMissCurProg _ s
  · rw [ite_eq_right hcr]; rfl

theorem clientState_fastProbeProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastProbeProg x) = s :=
  runClient_state_fastProbeProg x s

theorem realizesBounded_fastProbe :
    RealizesBounded .exact fastProbeProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hfs := realizesBounded_fastFeistelSplit
  have hrk := realizesBounded_fastRKey
  have hrm := realizesBounded_fastReadMeta
  have hct := realizesBounded_fastCheckTrieRole
  have hmc := realizesBounded_fastProbeMissCur
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
      runClient_state_fastFeistelSplitProg, runClient_state_fastRKeyProg,
      runClient_state_fastReadMetaProg, runClient_state_fastCheckTrieRoleProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-- Tier-hit flag `res.1.1` (`0` = miss, `1`/`2`/`3` = hit tier) in a `fastProbeProg` result. -/
abbrev fastProbeTier (res : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) : ℕ := res.1.1

/-- Reduced-key collision flag `res.1.2` in a `fastProbeProg` result. -/
abbrev fastProbeColl (res : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) : ℕ := res.1.2

/-- Bucket index `res.2.1` in a `fastProbeProg` result. -/
abbrev fastProbeBkt (res : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) : ℕ := res.2.1

/-- Matched `(slotIdx, val)` pair `res.2.2` in a `fastProbeProg` result. -/
abbrev fastProbeLoc (res : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) : ℕ × ℕ := res.2.2

/-- Matched bucket-local slot index `res.2.2.1` in a `fastProbeProg` result. -/
abbrev fastProbeIdx (res : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) : ℕ := res.2.2.1

/-- Matched value word `res.2.2.2` in a `fastProbeProg` result. -/
abbrev fastProbeVal (res : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) : ℕ := res.2.2.2

/-- Exact specification of `fastProbeProg` under `FastEpochInv` (valid on 100% of hash seeds!). -/
theorem fastProbeProg_spec {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hinv : FastEpochInv fl slack seeds s.mem s_abs) (u : Fin fl.U) :
    let res := (Memory.spec 0).clientResult s (fastProbeProg (fl.pBase, u.val))
    let fm := extractFastMeta fl s.mem
    let bp := extractBlockPool fl.mp s.mem
    let b := epochBucket fl.c fl.U fl.N seeds.bkt u
    let rk := rKeyOf fl.c fl.U fl.N seeds.fp u
    (Memory.spec 0).clientState s (fastProbeProg (fl.pBase, u.val)) = s ∧
    memoryCost (fastProbeProg (fl.pBase, u.val)) s ≤
      360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 4 * cTabWhp fl.c + 6 * hMaxBTree ∧
    fastProbeBkt res = b ∧
    match s_abs u with
    | some v =>
      (fastProbeTier res = 1 ∨ fastProbeTier res = 2 ∨ fastProbeTier res = 3) ∧
      fastProbeIdx res < bp.bktCount b ∧
      fastProbeVal res = v.val ∧
      fastKeyAt fl seeds.bkt s.mem b (fastProbeIdx res) = u.val ∧
      bpPairAt fl.bpL s.mem b (fastProbeIdx res) = (keyQuotient (bWhp fl.N) u.val, v.val)
    | none =>
      fastProbeTier res = 0 ∧ fastProbeLoc res = (0, 0) ∧
      (fastProbeColl res = 0 →
        bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
          (extractBufTrie (fl.trieL fm.curBufRole) s.mem) rk = none ∧
        (fm.subStep < qEpochWhp fl.N / 2 →
          bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
            (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) rk = none)) ∧
      (fastProbeColl res = 1 →
        ∃ u' : Fin fl.U, u' ≠ u ∧ s_abs u' ≠ none ∧
          rKeyOf fl.c fl.U fl.N seeds.fp u' = rk) := by
  dsimp only
  have hr : FastLayoutReady w fl s := hinv.ready hv rfl
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set b := epochBucket fl.c fl.U fl.N seeds.bkt u
  set q_u := keyQuotient (bWhp fl.N) u.val
  set rk := rKeyOf fl.c fl.U fl.N seeds.fp u
  have hb_lt : b < numBucketsWhp fl.N := epochBucket_lt fl.c fl.U fl.N seeds.bkt u
  have hrk_lt : rk < 2 ^ (cTabWhp fl.c * bCharWhp fl.N) := rKeyOf_lt fl.c fl.U fl.N seeds.fp u
  obtain ⟨hfs_r, hfs_c⟩ := fastFeistelSplitProg_spec hr hinv.seed_bkt u
  obtain ⟨hrk_r, hrk_c⟩ := fastRKeyProg_spec hr hinv.seed_fp u
  change (Memory.spec 0).clientResult s (fastFeistelSplitProg (fl.pBase, u.val)) = (b, q_u) at hfs_r
  change (Memory.spec 0).clientResult s (fastRKeyProg (fl.pBase, u.val)) = rk at hrk_r
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, _, _, _, _, hcur_snd, hold_half, hbt_all,
      hcomp, _, _, _⟩ :=
    hinv.tiers
  have hchk_trie : ∀ (role : ℕ) (mFn : ℕ → Option (ℕ × ℕ)),
      role < 2 →
      ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N) (extractBufTrie (fl.trieL role) s.mem) mFn →
      (∀ rk' b' loc', mFn rk' = some (b', loc') →
        b' < numBucketsWhp fl.N ∧ loc' < bp.bktCount b' ∧
        ∃ u' : Fin fl.U, rKeyOf fl.c fl.U fl.N seeds.fp u' = rk' ∧
          fastKeyAt fl seeds.bkt s.mem b' loc' = u'.val) →
      memoryCost (fastCheckTrieRoleProg ((fl.pBase, role), (rk, (b, q_u)))) s ≤
        90 + 2 * cTabWhp fl.c ∧
      (match mFn rk with
       | none =>
         (Memory.spec 0).clientResult s
           (fastCheckTrieRoleProg ((fl.pBase, role), (rk, (b, q_u)))) = (0, (0, (0, 0)))
       | some (b', loc') =>
         if fastKeyAt fl seeds.bkt s.mem b' loc' = u.val then
           b' = b ∧ loc' < bp.bktCount b ∧
           (Memory.spec 0).clientResult s
             (fastCheckTrieRoleProg ((fl.pBase, role), (rk, (b, q_u)))) =
             (1, (0, (loc', (bpPairAt fl.bpL s.mem b loc').2)))
         else
           (Memory.spec 0).clientResult s
             (fastCheckTrieRoleProg ((fl.pBase, role), (rk, (b, q_u)))) = (0, (1, (0, 0))) ∧
           ∃ u' : Fin fl.U, u' ≠ u ∧ s_abs u' ≠ none ∧
             rKeyOf fl.c fl.U fl.N seeds.fp u' = rk) := by
    intro role mFn hrole hvt hsnd
    have htv := hv.trie_valid hrole
    obtain ⟨hbl_st, hbl_c, hbl_r⟩ := bufLookupBoundedProg_spec htv hvt hrk_lt
    unfold fastCheckTrieRoleProg
    rw [prog_clientResult_bind, Realization.memoryCost_bind',
      clientState_loadTrieCtxProg, memoryCost_loadTrieCtxProg,
      clientResult_loadTrieCtxProg hpt hrole,
      prog_clientResult_bind, Realization.memoryCost_bind', hbl_st, hbl_r]
    rw [show (fl.trieL role).cTab = cTabWhp fl.c from rfl] at hbl_c
    cases hm_rk : mFn rk with
    | none =>
      dsimp only
      rw [ite_eq_right Nat.zero_ne_one, prog_clientResult_pure, memoryCost_pure]
      exact ⟨by omega, rfl⟩
    | some pair =>
      rcases pair with ⟨b', loc'⟩
      dsimp only
      obtain ⟨hb', hloc', u', hu'_rk, hu'_key⟩ := hsnd rk b' loc' hm_rk
      obtain ⟨u_s, v_s, hu_s_val, _, _, _, hs_u_s⟩ := hinv.bktSlot_refines hb' hloc'
      have hu_s_eq : u_s = u' := Fin.ext (hu_s_val.trans hu'_key)
      rw [hu_s_eq] at hs_u_s
      obtain ⟨hrd_s, hrd_r, hrd_c⟩ := fastBpReadAtProg_spec hr hinv.bp_inv hb' hloc'
      rw [ite_eq_left rfl, prog_clientResult_bind, Realization.memoryCost_bind', hrd_s, hrd_r]
      have hk_iff := hinv.key_iff_bktQuot hb' hloc' u
      by_cases hkey_eq : fastKeyAt fl seeds.bkt s.mem b' loc' = u.val
      · obtain ⟨hb_eq, hq_eq⟩ := hk_iff.mpr hkey_eq
        subst hb_eq
        rw [ite_eq_left hkey_eq, ite_eq_left rfl, ite_eq_left hq_eq, prog_clientResult_pure,
          memoryCost_pure]
        exact ⟨by omega, rfl, hloc', rfl⟩
      · rw [ite_eq_right hkey_eq]
        have hnot_bq : ¬(b' = b ∧ (bpPairAt fl.bpL s.mem b' loc').1 = q_u) :=
          mt hk_iff.mp hkey_eq
        by_cases hbe : b' = b
        · have hqne : (bpPairAt fl.bpL s.mem b' loc').1 ≠ q_u := fun hq => hnot_bq ⟨hbe, hq⟩
          rw [ite_eq_left hbe, ite_eq_right hqne, prog_clientResult_pure, memoryCost_pure]
          refine ⟨by omega, rfl, u',
            fun he => hkey_eq (hu'_key.trans (congrArg Fin.val he)), ?_, hu'_rk⟩
          rw [hs_u_s]; simp
        · rw [ite_eq_right hbe, prog_clientResult_pure, memoryCost_pure]
          refine ⟨by omega, rfl, u',
            fun he => hkey_eq (hu'_key.trans (congrArg Fin.val he)), ?_, hu'_rk⟩
          rw [hs_u_s]; simp
  obtain ⟨hsalt_lt, hrole_b_lt, hins_le, _⟩ := hinv.bkt_meta_bounds b hb_lt
  obtain ⟨hv_bt, hbt_snd⟩ := hbt_all b hb_lt
  let salt_fin : Fin (sMaxWhp fl.c fl.N) := ⟨fm.bktSalt b, hsalt_lt⟩
  set fp_u := (fpHash fl.c fl.U fl.N seeds.fp salt_fin u).val
  have hfp_lt : fp_u < 2 ^ fpBitsWhp fl.N := (fpHash fl.c fl.U fl.N seeds.fp salt_fin u).isLt
  have hchk_bt :
      memoryCost (fastCheckBTreeProg ((fl.pBase, u.val), (b, q_u))) s ≤
        135 + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * hMaxBTree ∧
      (match mapBTree b fp_u with
       | none =>
         (Memory.spec 0).clientResult s
           (fastCheckBTreeProg ((fl.pBase, u.val), (b, q_u))) = (0, (0, 0))
       | some loc' =>
         if fastKeyAt fl seeds.bkt s.mem b loc' = u.val then
           loc' < bp.bktCount b ∧
           (Memory.spec 0).clientResult s
             (fastCheckBTreeProg ((fl.pBase, u.val), (b, q_u))) =
             (1, (loc', (bpPairAt fl.bpL s.mem b loc').2))
         else
           (Memory.spec 0).clientResult s
             (fastCheckBTreeProg ((fl.pBase, u.val), (b, q_u))) = (0, (0, 0))) := by
    obtain ⟨hfp_r, hfp_c⟩ := fastFpHashProg_spec hr hinv.seed_fp salt_fin u
    change (Memory.spec 0).clientResult s (fastFpHashProg (fl.pBase, (fm.bktSalt b, u.val))) =
      fp_u at hfp_r
    change memoryCost (fastFpHashProg (fl.pBase, (fm.bktSalt b, u.val))) s ≤ _ at hfp_c
    obtain ⟨_, _, _, _, _, hfp_w, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      largeEpoch_param_bounds hv.thresh_le hv.N_le_U (hv.w_eq ▸ hv.fits_U)
    have hfp_w' : fpBitsWhp fl.N < fl.w := hv.w_eq ▸ hfp_w
    have hfp_sh : fp_u < (1 <<< fpBitsWhp fl.N) := by rwa [Nat.shiftLeft_eq, one_mul]
    obtain ⟨hbt_st, hbt_c, hbt_r⟩ := btreeLookupBoundedProg_spec hv.thresh_le rfl hv.bt_valid
      hb_lt hrole_b_lt hins_le hv_bt hfp_lt
    change (Memory.spec 0).clientState s
      (btreeLookupBoundedProg (fl.btL.toSliceCtx b (fm.curRole b), fp_u)) = s at hbt_st
    change memoryCost (btreeLookupBoundedProg (fl.btL.toSliceCtx b (fm.curRole b), fp_u)) s ≤
      _ at hbt_c
    change (Memory.spec 0).clientResult s
      (btreeLookupBoundedProg (fl.btL.toSliceCtx b (fm.curRole b), fp_u)) = _ at hbt_r
    have hs_eq : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 5))) =
        fm.bktSalt b := by
      rw [clientResult_fastReadBktLaneProg hpt hb_lt (by decide)]
      dsimp only [fm, extractFastMeta]; rw [ite_eq_left hb_lt]
    have hr_eq : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12))) =
        fm.curRole b := by
      rw [clientResult_fastReadBktLaneProg hpt hb_lt (by decide)]
      dsimp only [fm, extractFastMeta]; rw [ite_eq_left hb_lt]
    have hc5 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 5)) s
    have hc12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s
    have hsr_r : (Memory.spec 0).clientResult s (readParamPairProg (fl.pBase, (9, 2))) =
        (fpBitsWhp fl.N, fl.w) := by
      unfold readParamPairProg
      simp [hpt 9 (by decide), hpt 2 (by decide), FastEpochLayout.paramWord]
    have hsr_st : (Memory.spec 0).clientState s (readParamPairProg (fl.pBase, (9, 2))) = s := rfl
    have hsr_c : memoryCost (readParamPairProg (fl.pBase, (9, 2))) s = 2 := by
      unfold readParamPairProg; simp
    have hm11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
    have hm11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
        numBucketsWhp fl.N := hpt 11 (by decide)
    unfold fastCheckBTreeProg
    rw [prog_clientResult_bind, Realization.memoryCost_bind', hm11_st, hm11_r,
      prog_memoryCost_read, ite_eq_left hb_lt,
      prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastReadBktLaneProg, hs_eq,
      prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastReadBktLaneProg, hr_eq]
    unfold fastCheckBTreeFpProg; dsimp only
    rw [ite_eq_left hrole_b_lt, prog_clientResult_bind, Realization.memoryCost_bind', hsr_st, hsr_r,
      hsr_c, ite_eq_left hfp_w', prog_clientResult_bind, Realization.memoryCost_bind',
      clientState_fastFpHashProg]
    change _ ∧ _
    rw [hfp_r, ite_eq_left hfp_sh]
    unfold fastCheckBTreeSliceProg; dsimp only
    rw [prog_clientResult_bind, Realization.memoryCost_bind', clientState_loadBTreeSliceCtxProg,
      memoryCost_loadBTreeSliceCtxProg, clientResult_loadBTreeSliceCtxProg hpt,
      prog_clientResult_bind, Realization.memoryCost_bind', hbt_st, hbt_r]
    cases hm_bt : mapBTree b fp_u with
    | none =>
      dsimp only
      rw [ite_eq_right Nat.zero_ne_one, prog_clientResult_pure, memoryCost_pure]
      exact ⟨by omega, rfl⟩
    | some loc' =>
      dsimp only
      obtain ⟨hloc', _⟩ := hbt_snd fp_u loc' hm_bt
      obtain ⟨hrd_s, hrd_r, hrd_c⟩ := fastBpReadAtProg_spec hr hinv.bp_inv hb_lt hloc'
      rw [ite_eq_left rfl, prog_clientResult_bind, Realization.memoryCost_bind', hrd_s, hrd_r]
      have hk_iff := hinv.key_iff_bktQuot hb_lt hloc' u
      by_cases hkey_eq : fastKeyAt fl seeds.bkt s.mem b loc' = u.val
      · obtain ⟨_, hq_eq⟩ := hk_iff.mpr hkey_eq
        rw [ite_eq_left hkey_eq, ite_eq_left hq_eq, prog_clientResult_pure, memoryCost_pure]
        exact ⟨by omega, hloc', rfl⟩
      · have hq_ne : (bpPairAt fl.bpL s.mem b loc').1 ≠ q_u :=
          fun hq => hkey_eq (hk_iff.mp ⟨rfl, hq⟩)
        rw [ite_eq_right hkey_eq, ite_eq_right hq_ne, prog_clientResult_pure, memoryCost_pure]
        exact ⟨by omega, rfl⟩
  obtain ⟨hc_cur, hspec_cur⟩ := hchk_trie fm.curBufRole mapCur hinv.role_lt hv_cur hcur_snd
  obtain ⟨hc_bt, hspec_bt⟩ := hchk_bt
  have hc_m3 := memoryCost_fastReadMetaProg (fl.pBase, 3) s
  have hc_m4 := memoryCost_fastReadMetaProg (fl.pBase, 4) s
  have hdtab4 : 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
      2 * (2 * dTabWhp fl.c * (cTabWhp fl.c + 2)) := by ring
  have hm3_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 3)) = fm.curBufRole :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hm4_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 4)) = fm.subStep :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hq23_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s := rfl
  have hq23_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 23)) =
      qEpochWhp fl.N := hpt 23 (by decide)
  have hsh_div : qEpochWhp fl.N >>> 1 = qEpochWhp fl.N / 2 := Nat.shiftRight_eq_div_pow _ 1
  refine ⟨clientState_fastProbeProg _ s, ?_⟩
  rw [hdtab4]
  unfold fastProbeProg
  rw [prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastFeistelSplitProg, hfs_r,
    prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastRKeyProg, hrk_r,
    prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastReadMetaProg, hm3_r,
    ite_eq_left hinv.role_lt, prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_fastCheckTrieRoleProg]
  dsimp only
  cases hs_u : s_abs u with
  | some v =>
    obtain ⟨p_u, hp_u, how_u, hq_pu, hv_pu⟩ := (hinv.refines.models u v).mp hs_u
    set loc_u := ((extractBlockPool fl.mp s.mem).ownerOf p_u).2
    have hcv : (extractBlockPool fl.mp s.mem).CoreValid := hinv.bp_inv.1.core
    obtain ⟨hb_pu, hloc_u, htp_u⟩ := hcv.ownerOf_bounds_and_toPhys hp_u
    have hb_eq_u : ((extractBlockPool fl.mp s.mem).ownerOf p_u).1 = b := how_u
    rw [hb_eq_u] at hb_pu hloc_u htp_u
    have hpair_u : bpPairAt fl.bpL s.mem b loc_u = (q_u, v.val) := by
      unfold bpPairAt; dsimp only [FastEpochLayout.bpL]; rw [htp_u]; exact Prod.ext hq_pu hv_pu
    have hkey_u : fastKeyAt fl seeds.bkt s.mem b loc_u = u.val :=
      (hinv.key_iff_bktQuot hb_lt hloc_u u).mp ⟨rfl, by rw [hpair_u]⟩
    obtain ⟨u_w, hkey_w, htier_w⟩ := hcomp b hb_lt loc_u hloc_u
    have hu_w_eq : u_w = u := Fin.ext (hkey_w.symm.trans hkey_u)
    rw [hu_w_eq] at htier_w
    rcases htier_w with hm_c | hm_o | hm_b
    · rw [hm_c] at hspec_cur; dsimp only at hspec_cur
      rw [ite_eq_left hkey_u] at hspec_cur
      obtain ⟨_, _, hcr1⟩ := hspec_cur
      rw [hcr1, ite_eq_left rfl, prog_clientResult_pure, memoryCost_pure]
      dsimp only
      exact ⟨by omega, rfl, Or.inl rfl, hloc_u, congrArg Prod.snd hpair_u, hkey_u, hpair_u⟩
    · have hsub_lt : fm.subStep < qEpochWhp fl.N / 2 := by
        by_contra hge
        rw [ite_eq_right hge] at hold_half
        rw [hold_half.1] at hm_o; simp at hm_o
      rw [ite_eq_left hsub_lt] at hold_half
      obtain ⟨hv_old, _, _, _, _, _, _, hold_snd⟩ := hold_half
      obtain ⟨hm_c_none, _⟩ := hold_snd rk b loc_u hm_o
      rw [hm_c_none] at hspec_cur; dsimp only at hspec_cur
      rw [hspec_cur]
      obtain ⟨hc_old, hspec_old⟩ := hchk_trie (1 - fm.curBufRole) mapOld
        (by have := hinv.role_lt; omega) hv_old
        (fun rk' b' loc' hm' => ⟨(hold_snd rk' b' loc' hm').2.1, (hold_snd rk' b' loc' hm').2.2.1,
          (hold_snd rk' b' loc' hm').2.2.2⟩)
      rw [hm_o] at hspec_old; dsimp only at hspec_old
      rw [ite_eq_left hkey_u] at hspec_old
      obtain ⟨_, _, hcr2⟩ := hspec_old
      rw [ite_eq_right Nat.zero_ne_one]
      unfold fastProbeMissCurProg
      rw [prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastReadMetaProg, hm4_r,
        prog_clientResult_bind, Realization.memoryCost_bind', hq23_st, hq23_r,
        prog_memoryCost_read, hsh_div, ite_eq_left hsub_lt, pure_bind,
        prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastCheckTrieRoleProg,
        hcr2, ite_eq_left rfl, prog_clientResult_pure, memoryCost_pure]
      dsimp only
      exact ⟨by omega, rfl, Or.inr (Or.inl rfl), hloc_u, congrArg Prod.snd hpair_u, hkey_u, hpair_u⟩
    · obtain ⟨_, u_bt, _, hkey_bt, hm_c_disj, hm_o_disj⟩ := hbt_snd fp_u loc_u hm_b
      have hu_bt_eq : u_bt = u := Fin.ext (hkey_bt.symm.trans hkey_u)
      rw [hu_bt_eq] at hm_c_disj hm_o_disj
      have hc1_bt : ∃ cl₁,
          (Memory.spec 0).clientResult s
            (fastCheckTrieRoleProg ((fl.pBase, fm.curBufRole), (rk, (b, q_u)))) =
            (0, (cl₁, (0, 0))) := by
        cases hm_c : mapCur rk with
        | none => rw [hm_c] at hspec_cur; exact ⟨0, hspec_cur⟩
        | some p_c =>
          rcases p_c with ⟨b₁, loc₁⟩
          rw [hm_c] at hspec_cur; dsimp only at hspec_cur
          rw [ite_eq_right (hm_c_disj b₁ loc₁ hm_c)] at hspec_cur
          exact ⟨1, hspec_cur.1⟩
      obtain ⟨cl₁, hcr1_bt⟩ := hc1_bt
      rw [hcr1_bt, ite_eq_right Nat.zero_ne_one]
      rw [hm_b] at hspec_bt; dsimp only at hspec_bt
      rw [ite_eq_left hkey_u] at hspec_bt
      obtain ⟨_, hcb3⟩ := hspec_bt
      have htail_hit : ∀ cl,
          (Memory.spec 0).clientResult s
            (fastProbeBTreeTailProg ((fl.pBase, u.val), ((b, q_u), cl))) =
            ((3, cl), (b, (loc_u, (bpPairAt fl.bpL s.mem b loc_u).2))) ∧
          memoryCost (fastProbeBTreeTailProg ((fl.pBase, u.val), ((b, q_u), cl))) s ≤
            135 + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * hMaxBTree := fun cl => by
        unfold fastProbeBTreeTailProg
        rw [prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastCheckBTreeProg,
          hcb3, ite_eq_left rfl, prog_clientResult_pure, memoryCost_pure]
        exact ⟨rfl, by omega⟩
      unfold fastProbeMissCurProg
      rw [prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastReadMetaProg, hm4_r,
        prog_clientResult_bind, Realization.memoryCost_bind', hq23_st, hq23_r,
        prog_memoryCost_read, hsh_div]
      by_cases hsub_lt : fm.subStep < qEpochWhp fl.N / 2
      · rw [ite_eq_left hsub_lt] at hold_half ⊢
        obtain ⟨hv_old, _, _, _, _, _, _, hold_snd⟩ := hold_half
        obtain ⟨hc_old, hspec_old⟩ := hchk_trie (1 - fm.curBufRole) mapOld
          (by have := hinv.role_lt; omega) hv_old
          (fun rk' b' loc' hm' => ⟨(hold_snd rk' b' loc' hm').2.1,
            (hold_snd rk' b' loc' hm').2.2.1, (hold_snd rk' b' loc' hm').2.2.2⟩)
        have hc2_bt : ∃ cl₂,
            (Memory.spec 0).clientResult s
              (fastCheckTrieRoleProg ((fl.pBase, 1 - fm.curBufRole), (rk, (b, q_u)))) =
              (0, (cl₂, (0, 0))) := by
          cases hm_o : mapOld rk with
          | none => rw [hm_o] at hspec_old; exact ⟨0, hspec_old⟩
          | some p_o =>
            rcases p_o with ⟨b₂, loc₂⟩
            rw [hm_o] at hspec_old; dsimp only at hspec_old
            rw [ite_eq_right (hm_o_disj b₂ loc₂ hm_o)] at hspec_old
            exact ⟨1, hspec_old.1⟩
        obtain ⟨cl₂, hcr2_bt⟩ := hc2_bt
        rw [pure_bind, prog_clientResult_bind, Realization.memoryCost_bind',
          clientState_fastCheckTrieRoleProg, hcr2_bt, ite_eq_right Nat.zero_ne_one]
        by_cases hcl1 : cl₁ = 1
        · rw [ite_eq_left hcl1, (htail_hit 1).1]
          have hth1 := (htail_hit 1).2
          exact ⟨by omega, rfl, Or.inr (Or.inr rfl), hloc_u, congrArg Prod.snd hpair_u, hkey_u,
            hpair_u⟩
        · rw [ite_eq_right hcl1]
          by_cases hcl2 : cl₂ = 1
          · rw [ite_eq_left hcl2, (htail_hit 1).1]
            have hth1 := (htail_hit 1).2
            exact ⟨by omega, rfl, Or.inr (Or.inr rfl), hloc_u, congrArg Prod.snd hpair_u, hkey_u,
              hpair_u⟩
          · rw [ite_eq_right hcl2, (htail_hit 0).1]
            have hth0 := (htail_hit 0).2
            exact ⟨by omega, rfl, Or.inr (Or.inr rfl), hloc_u, congrArg Prod.snd hpair_u, hkey_u,
              hpair_u⟩
      · rw [ite_eq_right hsub_lt]; dsimp only
        rw [(htail_hit cl₁).1]
        have hthc := (htail_hit cl₁).2
        exact ⟨by omega, rfl, Or.inr (Or.inr rfl), hloc_u, congrArg Prod.snd hpair_u, hkey_u,
          hpair_u⟩
  | none =>
    have hno_key : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp.bktCount b',
        fastKeyAt fl seeds.bkt s.mem b' loc' ≠ u.val := by
      intro b' hb' loc' hloc' heq
      obtain ⟨u_s, _, hu_s, _, _, _, hs_s⟩ := hinv.bktSlot_refines hb' hloc'
      have : u_s = u := Fin.ext (hu_s.trans heq)
      rw [this, hs_u] at hs_s; simp at hs_s
    have hc3_zero :
        (Memory.spec 0).clientResult s (fastCheckBTreeProg ((fl.pBase, u.val), (b, q_u))) =
          (0, (0, 0)) := by
      cases hm_b : mapBTree b fp_u with
      | none => rw [hm_b] at hspec_bt; exact hspec_bt
      | some loc' =>
        obtain ⟨hloc', _⟩ := hbt_snd fp_u loc' hm_b
        rw [hm_b] at hspec_bt; dsimp only at hspec_bt
        rwa [ite_eq_right (hno_key b hb_lt loc' hloc')] at hspec_bt
    have htail_res : ∀ cl,
        (Memory.spec 0).clientResult s
          (fastProbeBTreeTailProg ((fl.pBase, u.val), ((b, q_u), cl))) =
          ((0, cl), (b, (0, 0))) ∧
        memoryCost (fastProbeBTreeTailProg ((fl.pBase, u.val), ((b, q_u), cl))) s ≤
          135 + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * hMaxBTree := fun cl => by
      unfold fastProbeBTreeTailProg
      rw [prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastCheckBTreeProg,
        hc3_zero, ite_eq_right Nat.zero_ne_one, prog_clientResult_pure, memoryCost_pure]
      exact ⟨rfl, by omega⟩
    have hc1_cases :
        ((Memory.spec 0).clientResult s
          (fastCheckTrieRoleProg ((fl.pBase, fm.curBufRole), (rk, (b, q_u)))) =
            (0, (0, (0, 0))) ∧ mapCur rk = none) ∨
        ((Memory.spec 0).clientResult s
          (fastCheckTrieRoleProg ((fl.pBase, fm.curBufRole), (rk, (b, q_u)))) =
            (0, (1, (0, 0))) ∧
          ∃ u' : Fin fl.U, u' ≠ u ∧ s_abs u' ≠ none ∧ rKeyOf fl.c fl.U fl.N seeds.fp u' = rk) := by
      cases hm_c : mapCur rk with
      | none => rw [hm_c] at hspec_cur; exact Or.inl ⟨hspec_cur, rfl⟩
      | some p_c =>
        rcases p_c with ⟨b', loc'⟩
        obtain ⟨hb', hloc', _⟩ := hcur_snd rk b' loc' hm_c
        rw [hm_c] at hspec_cur; dsimp only at hspec_cur
        rw [ite_eq_right (hno_key b' hb' loc' hloc')] at hspec_cur
        exact Or.inr hspec_cur
    have hcur_lk_eq : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL fm.curBufRole) s.mem) rk = mapCur rk :=
      hv_cur.lookup_eq hrk_lt
    have hc1_fst : ((Memory.spec 0).clientResult s
        (fastCheckTrieRoleProg ((fl.pBase, fm.curBufRole), (rk, (b, q_u))))).1 = 0 := by
      rcases hc1_cases with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    rw [ite_eq_right (by rw [hc1_fst]; decide)]
    unfold fastProbeMissCurProg
    rw [prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastReadMetaProg, hm4_r,
      prog_clientResult_bind, Realization.memoryCost_bind', hq23_st, hq23_r,
      prog_memoryCost_read, hsh_div]
    by_cases hsub_lt : fm.subStep < qEpochWhp fl.N / 2
    · rw [ite_eq_left hsub_lt] at hold_half ⊢
      obtain ⟨hv_old, _, _, _, _, _, _, hold_snd⟩ := hold_half
      obtain ⟨hc_old, hspec_old⟩ := hchk_trie (1 - fm.curBufRole) mapOld
        (by have := hinv.role_lt; omega) hv_old
        (fun rk' b' loc' hm' => ⟨(hold_snd rk' b' loc' hm').2.1,
          (hold_snd rk' b' loc' hm').2.2.1, (hold_snd rk' b' loc' hm').2.2.2⟩)
      have hold_lk_eq : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
          (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) rk = mapOld rk :=
        hv_old.lookup_eq hrk_lt
      have hc2_cases :
          ((Memory.spec 0).clientResult s
            (fastCheckTrieRoleProg ((fl.pBase, 1 - fm.curBufRole), (rk, (b, q_u)))) =
              (0, (0, (0, 0))) ∧ mapOld rk = none) ∨
          ((Memory.spec 0).clientResult s
            (fastCheckTrieRoleProg ((fl.pBase, 1 - fm.curBufRole), (rk, (b, q_u)))) =
              (0, (1, (0, 0))) ∧
            ∃ u' : Fin fl.U, u' ≠ u ∧ s_abs u' ≠ none ∧
              rKeyOf fl.c fl.U fl.N seeds.fp u' = rk) := by
        cases hm_o : mapOld rk with
        | none => rw [hm_o] at hspec_old; exact Or.inl ⟨hspec_old, rfl⟩
        | some p_o =>
          rcases p_o with ⟨b', loc'⟩
          obtain ⟨_, hb', hloc', _⟩ := hold_snd rk b' loc' hm_o
          rw [hm_o] at hspec_old; dsimp only at hspec_old
          rw [ite_eq_right (hno_key b' hb' loc' hloc')] at hspec_old
          exact Or.inr hspec_old
      rw [pure_bind, prog_clientResult_bind, Realization.memoryCost_bind',
        clientState_fastCheckTrieRoleProg]
      rcases hc1_cases with ⟨h1, hm1⟩ | ⟨h1, hw1⟩ <;>
        rcases hc2_cases with ⟨h2, hm2⟩ | ⟨h2, hw2⟩
      · rw [h1, h2, ite_eq_right Nat.zero_ne_one, ite_eq_right Nat.zero_ne_one,
          ite_eq_right Nat.zero_ne_one, (htail_res 0).1]
        have htc := (htail_res 0).2
        dsimp only
        exact ⟨by omega, rfl, rfl, rfl,
          fun _ => ⟨hcur_lk_eq.trans hm1, fun _ => hold_lk_eq.trans hm2⟩,
          fun h01 => absurd h01 (by decide)⟩
      · rw [h1, h2, ite_eq_right Nat.zero_ne_one, ite_eq_right Nat.zero_ne_one,
          ite_eq_left rfl, (htail_res 1).1]
        have htc := (htail_res 1).2
        dsimp only
        exact ⟨by omega, rfl, rfl, rfl, fun h10 => absurd h10 (by decide), fun _ => hw2⟩
      · rw [h1, h2, ite_eq_right Nat.zero_ne_one, ite_eq_left rfl, (htail_res 1).1]
        have htc := (htail_res 1).2
        dsimp only
        exact ⟨by omega, rfl, rfl, rfl, fun h10 => absurd h10 (by decide), fun _ => hw1⟩
      · rw [h1, h2, ite_eq_right Nat.zero_ne_one, ite_eq_left rfl, (htail_res 1).1]
        have htc := (htail_res 1).2
        dsimp only
        exact ⟨by omega, rfl, rfl, rfl, fun h10 => absurd h10 (by decide), fun _ => hw1⟩
    · rw [ite_eq_right hsub_lt]
      rcases hc1_cases with ⟨h1, hm1⟩ | ⟨h1, hw1⟩
      · rw [h1]; dsimp only
        rw [(htail_res 0).1]
        have htc := (htail_res 0).2
        dsimp only
        exact ⟨by omega, rfl, rfl, rfl,
          fun _ => ⟨hcur_lk_eq.trans hm1, fun hlt => absurd hlt hsub_lt⟩,
          fun h01 => absurd h01 (by decide)⟩
      · rw [h1]; dsimp only
        rw [(htail_res 1).1]
        have htc := (htail_res 1).2
        dsimp only
        exact ⟨by omega, rfl, rfl, rfl, fun h10 => absurd h10 (by decide), fun _ => hw1⟩

/-- Read-only `FastEpoch` `query(u)`, returning `(0, 0)` on `none` and `(1, v.val)` on `some v`
(`RealizesBounded .exact`, `¬ReadsWidth`, `clientState = s`, exact on 100% of hash seeds). -/
def fastQueryProg : ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (pBase, u_val) => do
    let pr ← fastProbeProg (pBase, u_val)
    if fastProbeTier pr = 0 then
      pure (0, 0)
    else
      pure (1, fastProbeVal pr)

theorem realizesBounded_fastQuery :
    RealizesBounded .exact fastQueryProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hp := realizesBounded_fastProbe
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
    dsimp only [Fits] at *
    first | exact ⟨fl, rfl, hr⟩ | exact h1_w)

theorem fastQueryProg_spec {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hinv : FastEpochInv fl slack seeds s.mem s_abs) (u : Fin fl.U) :
    (Memory.spec 0).clientState s (fastQueryProg (fl.pBase, u.val)) = s ∧
    memoryCost (fastQueryProg (fl.pBase, u.val)) s ≤
      360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 4 * cTabWhp fl.c + 6 * hMaxBTree ∧
    (Memory.spec 0).clientResult s (fastQueryProg (fl.pBase, u.val)) =
      match s_abs u with
      | none => (0, 0)
      | some v => (1, v.val) := by
  obtain ⟨hst, hc, _, hpr⟩ :=
    fastProbeProg_spec (slack := slack) (seeds := seeds) (s_abs := s_abs) hv hinv u
  unfold fastQueryProg
  rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind, Realization.memoryCost_bind',
    hst]
  dsimp only
  cases hs_u : s_abs u with
  | none =>
    rw [hs_u] at hpr
    rw [ite_eq_left hpr.1, StateTransitionSpec.clientState_pure, prog_clientResult_pure,
      memoryCost_pure]
    exact ⟨rfl, by omega, rfl⟩
  | some v =>
    rw [hs_u] at hpr
    have hnz : ((Memory.spec 0).clientResult s (fastProbeProg (fl.pBase, u.val))).1.1 ≠ 0 := by
      rcases hpr.1 with h | h | h <;> omega
    rw [ite_eq_right hnz, StateTransitionSpec.clientState_pure, prog_clientResult_pure,
      memoryCost_pure, hpr.2.2.1]
    exact ⟨rfl, by omega, rfl⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
