/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochSubEpoch
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deamortized Sub-Epoch Salt Search and `BufOld` Slot Draining (`LargeEpochDrain`)

This module implements the `RealizesBounded .exact` (`¬ReadsWidth`) elementary sub-epoch background
maintenance steps (`fastBufItemAllocProg`, `drainTryStepProg`, and `drainOldSlotProg`) for the large
hashed epoch of the deamortized WHP resizable succinct dictionary ([Bender, Farach-Colton,
J. Kuszmaul, and W. Kuszmaul, SOSA 2024, Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]).

Both `drainTryStepProg` (intra-bucket candidate salt verification via `tryRoleProg`) and
`drainOldSlotProg` (incremental `BufOld` slot migration and `fastBufClearStepsProg` node clearing)
preserve `FastEpochInvGen` unconditionally on **100%** of hash seeds in `O_c(1)` deterministic
instructions; the multi-tick schedulers (`drainTickProg`, `drainTicks16Prog`, `drainTrySteps5Prog`),
`drainPotential` Lyapunov bound, and sub-epoch rollover `advanceSubEpochProg` are established in
`LargeEpochAdvance`.

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

/-! ## Section 1: `fastBufItemAllocProg`, `bufDelete` Scan Lemma, and Fixed-Pool Constructor -/

private def readTrieItemAllocCtxProg : TrieCtx → Memory.Prog ℕ
  | (((mb, _oc), (_on, oi)), ((pb, wv), ((_ct, _bc), (_mn, qm)))) =>
    if pb ≤ wv then
      readPackedCompGenProg (((mb, oi), (pb, wv)), 6 * qm + 1)
    else
      pure 0

@[simp] private theorem runClient_state_readTrieItemAllocCtxProg (ctx : TrieCtx)
    (s : Memory.State) :
    ((Memory.spec 0).runClient s (readTrieItemAllocCtxProg ctx)).2.1 = s := by
  rcases ctx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩
  unfold readTrieItemAllocCtxProg; dsimp only
  split_ifs
  · exact runClient_state_readPackedCompGenProg _ s
  · rfl

private theorem realizesBounded_readTrieItemAllocCtx :
    RealizesBounded .exact readTrieItemAllocCtxProg
      (WordEncoding.encode (α := TrieCtx))
      (WordEncoding.encode (α := ℕ))
      (fun w ctx s => (TrieLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
    dsimp only [TrieLayout.ofCtx] at h
    obtain ⟨hw, hwv, hpb, _, _, _, _, _, hqm_pb, _, _, _, h6q, _, _, hfr⟩ := h
    subst hwv
    have hqm_w : qm < 2 ^ w := hqm_pb.trans_le (Nat.pow_le_pow_right (by decide) hpb)
    dsimp only [Fits] at *
    first
    | omega
    | exact ⟨6 * qm + 6, hw, rfl, hpb, by omega, hfr⟩)

/-- Read `(extractBufTrie (fl.trieL role) s.mem).itemAlloc` via `pBase` (`¬ReadsWidth`). -/
def fastBufItemAllocProg : ℕ × ℕ → Memory.Prog ℕ
  | (pBase, role) =>
    if role < 2 then do
      let tctx ← loadTrieCtxProg (pBase, role)
      readTrieItemAllocCtxProg tctx
    else
      pure 0

@[simp] theorem runClient_state_fastBufItemAllocProg (x : ℕ × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (fastBufItemAllocProg x)) = s := by
  rcases x with ⟨pBase, role⟩
  unfold clientOutState fastBufItemAllocProg; dsimp only
  split_ifs
  · rw [prog_runClient_state_bind, clientState_loadTrieCtxProg]
    exact runClient_state_readTrieItemAllocCtxProg _ s
  · rfl

theorem clientState_fastBufItemAllocProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastBufItemAllocProg x) = s :=
  runClient_state_fastBufItemAllocProg x s

theorem realizesBounded_fastBufItemAlloc :
    RealizesBounded .exact fastBufItemAllocProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlt := realizesBounded_loadTrieCtx
  have hri := realizesBounded_readTrieItemAllocCtx
  realize
  all_goals (
    rcases d with ⟨pBase, role⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_loadTrieCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have hl_res := clientResult_loadTrieCtxProg hr.2.1 ‹role < 2› (s := s)
      simp only [StateTransitionSpec.clientResult] at hl_res ⊢
      rw [hl_res, TrieLayout.ofCtx_toCtx]
      exact hr.1.w_eq.symm ▸ hr.1.trie_valid ‹role < 2›))

theorem fastBufItemAllocProg_spec {fl : FastEpochLayout} {w role : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hrole : role < 2) :
    (Memory.spec 0).clientResult s (fastBufItemAllocProg (fl.pBase, role)) =
      (extractBufTrie (fl.trieL role) s.mem).itemAlloc ∧
    memoryCost (fastBufItemAllocProg (fl.pBase, role)) s ≤ 12 := by
  unfold fastBufItemAllocProg; dsimp only
  rw [ite_eq_left hrole, prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_loadTrieCtxProg, clientResult_loadTrieCtxProg hr.2.1 hrole,
    memoryCost_loadTrieCtxProg]
  unfold readTrieItemAllocCtxProg; dsimp only [TrieLayout.toCtx]
  have hpb_le : (fl.trieL role).ptrB ≤ (fl.trieL role).w := by
    have htv := hr.1.trie_valid hrole
    exact htv.2.1 ▸ htv.2.2.1
  rw [ite_eq_left hpb_le, clientResult_readPackedCompGenProg, memoryCost_readPackedCompGenProg]
  exact ⟨rfl, by omega⟩

/-- Deleting key `rKey` whose walk reaches `tr.itemLeaf id` clears `bufCheckSlot` at `id` to `none`.
-/
theorem bufCheckSlot_bufDelete_self_none {cTab bChar rKey id : ℕ} {tr : BufTrie}
    (hwk : bufWalk bChar tr.trieChild rKey cTab 0 0 = some (tr.itemLeaf id)) :
    bufCheckSlot (bufDelete cTab bChar tr rKey) id = none := by
  unfold bufDelete
  rw [hwk]; dsimp only
  by_cases hcond : tr.nodeLeafItem (tr.itemLeaf id) = 0 ∨ tr.nodeActive (tr.itemLeaf id) = 0
  · rw [ite_eq_left hcond]
    unfold bufCheckSlot
    by_cases hid : id < tr.itemAlloc
    · rw [ite_eq_left hid]; dsimp only
      rcases hcond with h0 | h0 <;> simp [h0]
    · exact ite_eq_right hid
  · rw [ite_eq_right hcond]
    unfold bufCheckSlot; dsimp only
    by_cases hid : id < tr.itemAlloc
    · rw [ite_eq_left hid]; simp [Function.update_self]
    · exact ite_eq_right hid

/-- Shared non-tier fields for rebuilding `FastEpochInvGen` across transitions that preserve
`BlockPool`, `fl.io.OwnsAddr`, and addresses outside `fl.OwnsFastAddr`. -/
theorem FastEpochInvGen.fixed_pool_core {slackCur : ℕ} {fl : FastEpochLayout}
    {w slack : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s s' : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hbp_eq : extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem)
    (hoi : ∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr)
    (hof : ∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) :
    s'.mem fl.metaBase = fl.N ∧
    BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s'.mem ∧
    BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s'.mem ∧
    fl.bpL.StateInv slack s'.mem ∧
    (∀ b < numBucketsWhp fl.N,
      (extractBlockPool fl.mp s'.mem).bktCount b ≤ capMaxWhp fl.N) ∧
    PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt)
      (extractBlockPool fl.mp s'.mem).nSide
      (fun p => ((extractBlockPool fl.mp s'.mem).ownerOf p).1)
      (slotIoPairAt fl.io s'.mem) s_abs := by
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hio := fl.io.congr_of_outside hv.io_valid.w_pos hinv.bp_inv.2.2 hoi
  refine ⟨(hof fl.metaBase hv.not_ownsFast_hdr0).trans hinv.hdr_N,
    hinv.seed_bkt.congr_on hw_pos fun a h1 h2 =>
      hof a (hv.not_ownsFast_seeds
        (by unfold FastEpochLayout.bktHashBase at h1; exact h1)
        (by unfold FastEpochLayout.bktHashBase at h2
            unfold offBktMeta offFpHash; unfold offBktHash at h2 ⊢; omega)),
    hinv.seed_fp.congr_on hw_pos fun a h1 h2 =>
      hof a (hv.not_ownsFast_seeds
        (by unfold FastEpochLayout.fpHashBase at h1
            unfold offFpHash at h1; unfold offBktHash at h1 ⊢; omega)
        (by unfold FastEpochLayout.fpHashBase at h2
            unfold offBktMeta; omega)),
    ⟨hbp_eq ▸ hinv.bp_inv.1, hbp_eq ▸ hinv.bp_inv.2.1, hbp_eq ▸ hio.1⟩,
    fun b hb => by rw [hbp_eq]; exact hinv.bkt_le_capMax b hb, ?_⟩
  rw [hbp_eq]
  exact hinv.refines.congr (fun _ _ => rfl) fun p hp => hio.2 p hp

theorem fastKeyAt_eq_of_fixed_pool {fl : FastEpochLayout} {w slack : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s s' : Memory.State}
    (hv : fl.Valid w s.frontier) (hbp_inv : fl.bpL.StateInv slack s.mem)
    (hbp_eq : extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem)
    (hoi : ∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr)
    {b loc : ℕ} (hb : b < numBucketsWhp fl.N)
    (hloc : loc < (extractBlockPool fl.mp s.mem).bktCount b) :
    fastKeyAt fl θ_bkt s'.mem b loc = fastKeyAt fl θ_bkt s.mem b loc := by
  unfold fastKeyAt bpPairAt; dsimp only [FastEpochLayout.bpL]
  rw [hbp_eq]
  have hp_lt := hbp_inv.1.core.toPhys_lt hb hloc
  dsimp only [FastEpochLayout.bpL] at hp_lt
  rw [(fl.io.congr_of_outside hv.io_valid.w_pos hbp_inv.2.2 hoi).2 _ hp_lt]

/-! ## Section 2: Candidate Salt Search (`advanceTrySalt`, `commitTrySalt`, `drainTryStepProg`) -/

private def writeTryResetMetaProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, nextSalt) => do
    fastWriteMetaProg ((pBase, 8), nextSalt)
    fastWriteMetaProg ((pBase, 9), 0)
    fastWriteMetaProg ((pBase, 17), 0)

private theorem writeTryResetMetaProg_frame {fl : FastEpochLayout} {w nextSalt : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (writeTryResetMetaProg (fl.pBase, nextSalt))
    let fm := extractFastMeta fl s.mem
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (writeTryResetMetaProg (fl.pBase, nextSalt)) s ≤ 15 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r s'.mem = extractBTreeSlice fl.btL b r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    extractFastMeta fl s'.mem =
      { fm with trySalt := nextSalt, tryPos := 0, tryIns := 0 } := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  have c8 := memoryCost_fastWriteMetaProg ((fl.pBase, 8), nextSalt) s
  obtain ⟨hfr1, hr1, hbp1, hbt1, htr1, hoi1, hof1, hm2_1, hfm1⟩ :=
    extractFastMeta_writeMeta (off := 8) (val := nextSalt) hr (Or.inl ⟨by decide, by decide⟩)
  generalize hs1_def :
    (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 8), nextSalt)) = s1
  rw [hs1_def] at hfr1 hr1 hbp1 hbt1 htr1 hoi1 hof1 hm2_1 hfm1
  have c9 := memoryCost_fastWriteMetaProg ((fl.pBase, 9), 0) s1
  obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hoi2, hof2, hm2_2, hfm2⟩ :=
    extractFastMeta_writeMeta (off := 9) (val := 0) hr1 (Or.inl ⟨by decide, by decide⟩)
  generalize hs2_def :
    (Memory.spec 0).clientState s1 (fastWriteMetaProg ((fl.pBase, 9), 0)) = s2
  rw [hs2_def] at hfr2 hr2 hbp2 hbt2 htr2 hoi2 hof2 hm2_2 hfm2
  have c17 := memoryCost_fastWriteMetaProg ((fl.pBase, 17), 0) s2
  obtain ⟨hfr3, hr3, hbp3, hbt3, htr3, hoi3, hof3, hm2_3, hfm3⟩ :=
    extractFastMeta_writeMeta (off := 17) (val := 0) hr2 (Or.inr rfl)
  generalize hs3_def :
    (Memory.spec 0).clientState s2 (fastWriteMetaProg ((fl.pBase, 17), 0)) = s3
  rw [hs3_def] at hfr3 hr3 hbp3 hbt3 htr3 hoi3 hof3 hm2_3 hfm3
  have htot : (Memory.spec 0).clientState s (writeTryResetMetaProg (fl.pBase, nextSalt)) = s3 ∧
      memoryCost (writeTryResetMetaProg (fl.pBase, nextSalt)) s ≤ 15 := by
    unfold writeTryResetMetaProg
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs2_def, hs3_def]
    exact ⟨rfl, by omega⟩
  rw [htot.1]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl] at hfm1
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl] at hfm2
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide)] at hfm3
  exact ⟨hfr3.trans (hfr2.trans hfr1), hr3, htot.2, hbp3.trans (hbp2.trans hbp1),
    fun b hb r hr_lt => (hbt3 b hb r hr_lt).trans ((hbt2 b hb r hr_lt).trans (hbt1 b hb r hr_lt)),
    fun r hr_lt => (htr3 r hr_lt).trans ((htr2 r hr_lt).trans (htr1 r hr_lt)),
    fun a ha => (hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha)),
    fun a ha => (hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha)),
    hm2_3.trans (hm2_2.trans hm2_1), by rw [hfm3, hfm2, hfm1]⟩

private theorem realizesBounded_writeTryResetMeta :
    RealizesBounded .exact writeTryResetMetaProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hw := realizesBounded_fastWriteMeta
  realize
  all_goals (
    rcases d with ⟨pBase, nextSalt⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    have hp1 := fastWriteMetaProg_pre (x := ((fl.pBase, 8), nextSalt)) ⟨fl, rfl, hr⟩
    have hp2 := fastWriteMetaProg_pre (x := ((fl.pBase, 9), 0)) hp1
    first | exact ⟨fl, rfl, hr⟩ | exact hp1 | exact hp2 | omega)

private def nextSaltProg : ℕ × ℕ → Memory.Prog ℕ
  | (ts, sMax) =>
    if ts < sMax then
      if ts + 1 < sMax then pure (ts + 1) else pure 0
    else pure 0

@[simp] private theorem runClient_state_nextSaltProg (x : ℕ × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (nextSaltProg x)).2.1 = s := by
  rcases x with ⟨ts, sMax⟩; unfold nextSaltProg; dsimp only; split_ifs <;> rfl

private theorem clientState_nextSaltProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (nextSaltProg x) = s :=
  runClient_state_nextSaltProg x s

private theorem clientResult_nextSaltProg (ts sMax : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (nextSaltProg (ts, sMax)) =
      if ts + 1 < sMax then ts + 1 else 0 := by
  unfold nextSaltProg
  by_cases h1 : ts + 1 < sMax
  · have h0 : ts < sMax := by omega
    simp [h0, h1]
  · by_cases h0 : ts < sMax <;> simp [h0, h1]

private theorem memoryCost_nextSaltProg (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (nextSaltProg x) s = 0 := by
  rcases x with ⟨ts, sMax⟩; unfold nextSaltProg; dsimp only; split_ifs <;> simp

private theorem realizesBounded_nextSalt :
    RealizesBounded .exact nextSaltProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w (_, sMax) _ => 6 ≤ w ∧ sMax < 2 ^ w) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨ts, sMax⟩
    obtain ⟨hw6, hs⟩ := h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *; omega)

/-- Reset `tryRole` on `tryBkt` and advance `trySalt` (`ts + 1` if `ts + 1 < sMax`, else `0` on bad
seeds so `FastEpochInvGen` holds unconditionally until `Q / 2`). -/
def advanceTrySaltProg (pBase : ℕ) : Memory.Prog Unit := do
  let b ← fastReadMetaProg (pBase, 7)
  let ts ← fastReadMetaProg (pBase, 8)
  let sMax ← Memory.read (pBase + 24)
  let nextSalt ← nextSaltProg (ts, sMax)
  let cRole ← fastReadBktLaneProg (pBase, (b, 12))
  let tRole ← tryRoleProg cRole
  fastBTreeResetProg (pBase, (b, tRole))
  writeTryResetMetaProg (pBase, nextSalt)

theorem advanceTrySaltProg_frame {fl : FastEpochLayout} {w : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (advanceTrySaltProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    let nextSalt := if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (advanceTrySaltProg fl.pBase) s ≤ 52 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (fm.tryBkt < numBucketsWhp fl.N →
      extractFastMeta fl s'.mem = { fm with trySalt := nextSalt, tryPos := 0, tryIns := 0 } ∧
      ValidWhpSlice fl.N 0
        (extractBTreeSlice fl.btL fm.tryBkt (tryRoleOf (fm.curRole fm.tryBkt)) s'.mem)
        (fun _ => none) ∧
      (∀ b' < numBucketsWhp fl.N, ∀ role' < 3,
        (b' ≠ fm.tryBkt ∨ role' ≠ tryRoleOf (fm.curRole fm.tryBkt)) →
        extractBTreeSlice fl.btL b' role' s'.mem = extractBTreeSlice fl.btL b' role' s.mem)) := by
  dsimp only
  have hpt := hr.2.1
  set fm := extractFastMeta fl s.mem
  have hm7 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 7)) = fm.tryBkt :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hm8 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 8)) = fm.trySalt :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hm24 : s.mem (fl.pBase + 24) = sMaxWhp fl.c fl.N := hpt 24 (by decide)
  set nextSalt := if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0
  generalize hcr_res :
    (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (fm.tryBkt, 12))) = cr_raw
  obtain ⟨hfr_r, hr_r, hc_r, hbp_r, hfm_r, hm2_r, htr_r, hoi_r, hof_r, hsl_r⟩ :=
    fastBTreeResetProg_spec (b := fm.tryBkt) (role := tryRoleOf cr_raw) hr
  generalize hs1_def : (Memory.spec 0).clientState s
    (fastBTreeResetProg (fl.pBase, (fm.tryBkt, tryRoleOf cr_raw))) = s1
  rw [hs1_def] at hfr_r hr_r hbp_r hfm_r hm2_r htr_r hoi_r hof_r hsl_r
  obtain ⟨hfr_w, hr_w, hc_w, hbp_w, hbt_w, htr_w, hoi_w, hof_w, hm2_w, hfm_w⟩ :=
    writeTryResetMetaProg_frame (nextSalt := nextSalt) hr_r
  generalize hs2_def :
    (Memory.spec 0).clientState s1 (writeTryResetMetaProg (fl.pBase, nextSalt)) = s2
  rw [hs2_def] at hfr_w hr_w hbp_w hbt_w htr_w hoi_w hof_w hm2_w hfm_w
  have htot : (Memory.spec 0).clientState s (advanceTrySaltProg fl.pBase) = s2 ∧
      memoryCost (advanceTrySaltProg fl.pBase) s ≤ 52 := by
    unfold advanceTrySaltProg; dsimp only
    have hr24_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 24)) = s := rfl
    have hr24_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 24)) =
        sMaxWhp fl.c fl.N := hm24
    have cm7 := memoryCost_fastReadMetaProg (fl.pBase, 7) s
    have cm8 := memoryCost_fastReadMetaProg (fl.pBase, 8) s
    have cl12 := memoryCost_fastReadBktLaneProg (fl.pBase, (fm.tryBkt, 12)) s
    have hns_r : (Memory.spec 0).clientResult s
        (nextSaltProg (fm.trySalt, sMaxWhp fl.c fl.N)) = nextSalt :=
      clientResult_nextSaltProg _ _ s
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hm7,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hm8,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      hr24_st, hr24_r, prog_memoryCost_read,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_nextSaltProg, hns_r, memoryCost_nextSaltProg,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadBktLaneProg, hcr_res,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_tryRoleProg, clientResult_tryRoleProg, memoryCost_tryRoleProg,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      hs1_def, hs2_def]
    exact ⟨rfl, by omega⟩
  rw [htot.1]
  refine ⟨hfr_w.trans hfr_r, hr_w, htot.2, hbp_w.trans hbp_r,
    fun r hr_lt => (htr_w r hr_lt).trans (htr_r r hr_lt),
    fun a ha => (hoi_w a ha).trans (hoi_r a ha),
    fun a ha => (hof_w a ha).trans (hof_r a ha),
    hm2_w.trans hm2_r, fun hb => ?_⟩
  have hcr_eq : cr_raw = fm.curRole fm.tryBkt := by
    rw [← hcr_res, clientResult_fastReadBktLaneProg hpt hb (by decide)]
    change _ = (if fm.tryBkt < numBucketsWhp fl.N then _ else 0)
    rw [ite_eq_left hb]
  subst hcr_eq
  have htr_lt : tryRoleOf (fm.curRole fm.tryBkt) < 3 := by
    unfold tryRoleOf; split_ifs <;> decide
  obtain ⟨hv_z, hsl_o⟩ := hsl_r hb htr_lt
  rw [hfm_r] at hfm_w
  exact ⟨hfm_w, by rw [hbt_w _ hb _ htr_lt]; exact hv_z,
    fun b' hb' r' hr' hne => (hbt_w b' hb' r' hr').trans (hsl_o b' hb' r' hr' hne)⟩

theorem advanceTrySaltProg_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (advanceTrySaltProg pBase)) := by
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (advanceTrySaltProg_frame hr).2.1⟩

theorem realizesBounded_advanceTrySalt :
    RealizesBounded .exact advanceTrySaltProg
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hns := realizesBounded_nextSalt
  have hrl := realizesBounded_fastReadBktLane
  have htr := realizesBounded_tryRole
  have hbr := realizesBounded_fastBTreeReset
  have hwr := realizesBounded_writeTryResetMeta
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm24 : s.mem (fl.pBase + 24) = sMaxWhp fl.c fl.N := hr.2.1 24 (by decide)
    have hsMax_N : sMaxWhp fl.c fl.N ≤ fl.N := hr.1.bounds_le_N.2.2.1
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg,
      runClient_state_nextSaltProg, runClient_state_fastReadBktLaneProg,
      runClient_state_tryRoleProg, hm24] at *
    first
    | exact hw6
    | exact ⟨fl, rfl, hr⟩
    | exact fastBTreeResetProg_pre (x := (fl.pBase,
        (((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 7))).1,
         ((Memory.spec 0).runClient s (tryRoleProg
           ((Memory.spec 0).runClient s (fastReadBktLaneProg (fl.pBase,
             (((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 7))).1, 12)))).1)).1)))
        ⟨fl, rfl, hr⟩
    | omega)

private def clearTryMetaProg (pBase : ℕ) : Memory.Prog Unit := do
  fastWriteMetaProg ((pBase, 6), 0)
  fastWriteMetaProg ((pBase, 9), 0)
  fastWriteMetaProg ((pBase, 17), 0)

private theorem clearTryMetaProg_frame {fl : FastEpochLayout} {w : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (clearTryMetaProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (clearTryMetaProg fl.pBase) s ≤ 15 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r s'.mem = extractBTreeSlice fl.btL b r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    extractFastMeta fl s'.mem = { fm with tryAct := 0, tryPos := 0, tryIns := 0 } := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  have c6 := memoryCost_fastWriteMetaProg ((fl.pBase, 6), 0) s
  obtain ⟨hfr1, hr1, hbp1, hbt1, htr1, hoi1, hof1, hm2_1, hfm1⟩ :=
    extractFastMeta_writeMeta (off := 6) (val := 0) hr (Or.inl ⟨by decide, by decide⟩)
  generalize hs1_def :
    (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 6), 0)) = s1
  rw [hs1_def] at hfr1 hr1 hbp1 hbt1 htr1 hoi1 hof1 hm2_1 hfm1
  have c9 := memoryCost_fastWriteMetaProg ((fl.pBase, 9), 0) s1
  obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hoi2, hof2, hm2_2, hfm2⟩ :=
    extractFastMeta_writeMeta (off := 9) (val := 0) hr1 (Or.inl ⟨by decide, by decide⟩)
  generalize hs2_def :
    (Memory.spec 0).clientState s1 (fastWriteMetaProg ((fl.pBase, 9), 0)) = s2
  rw [hs2_def] at hfr2 hr2 hbp2 hbt2 htr2 hoi2 hof2 hm2_2 hfm2
  have c17 := memoryCost_fastWriteMetaProg ((fl.pBase, 17), 0) s2
  obtain ⟨hfr3, hr3, hbp3, hbt3, htr3, hoi3, hof3, hm2_3, hfm3⟩ :=
    extractFastMeta_writeMeta (off := 17) (val := 0) hr2 (Or.inr rfl)
  generalize hs3_def :
    (Memory.spec 0).clientState s2 (fastWriteMetaProg ((fl.pBase, 17), 0)) = s3
  rw [hs3_def] at hfr3 hr3 hbp3 hbt3 htr3 hoi3 hof3 hm2_3 hfm3
  have htot : (Memory.spec 0).clientState s (clearTryMetaProg fl.pBase) = s3 ∧
      memoryCost (clearTryMetaProg fl.pBase) s ≤ 15 := by
    unfold clearTryMetaProg
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs2_def, hs3_def]
    exact ⟨rfl, by omega⟩
  rw [htot.1]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl] at hfm1
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl] at hfm2
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide)] at hfm3
  exact ⟨hfr3.trans (hfr2.trans hfr1), hr3, htot.2, hbp3.trans (hbp2.trans hbp1),
    fun b hb r hr_lt => (hbt3 b hb r hr_lt).trans ((hbt2 b hb r hr_lt).trans (hbt1 b hb r hr_lt)),
    fun r hr_lt => (htr3 r hr_lt).trans ((htr2 r hr_lt).trans (htr1 r hr_lt)),
    fun a ha => (hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha)),
    fun a ha => (hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha)),
    hm2_3.trans (hm2_2.trans hm2_1), by rw [hfm3, hfm2, hfm1]⟩

private theorem realizesBounded_clearTryMeta :
    RealizesBounded .exact clearTryMetaProg
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hw := realizesBounded_fastWriteMeta
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    have hp1 := fastWriteMetaProg_pre (x := ((fl.pBase, 6), 0)) ⟨fl, rfl, hr⟩
    have hp2 := fastWriteMetaProg_pre (x := ((fl.pBase, 9), 0)) hp1
    first | exact ⟨fl, rfl, hr⟩ | exact hp1 | exact hp2 | omega)

/-- Commit `tryRole` as `curRole` on `tryBkt` (`bktSalt := trySalt`, `curRole := tryRole`,
`curIns := tryIns`, `tryAct := 0`). -/
def commitTrySaltProg (pBase : ℕ) : Memory.Prog Unit := do
  let b ← fastReadMetaProg (pBase, 7)
  let ts ← fastReadMetaProg (pBase, 8)
  let ti ← fastReadMetaProg (pBase, 17)
  let cRole ← fastReadBktLaneProg (pBase, (b, 12))
  let tRole ← tryRoleProg cRole
  fastWriteBktLaneProg ((pBase, (b, 5)), ts)
  fastWriteBktLaneProg ((pBase, (b, 12)), tRole)
  fastWriteBktLaneProg ((pBase, (b, 13)), ti)
  clearTryMetaProg pBase

theorem commitTrySaltProg_frame {fl : FastEpochLayout} {w : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (commitTrySaltProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (commitTrySaltProg fl.pBase) s ≤ 75 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r s'.mem = extractBTreeSlice fl.btL b r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fm.tryBkt < numBucketsWhp fl.N → fm.trySalt ≤ fl.N → fm.tryIns ≤ fl.N →
      s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
      extractFastMeta fl s'.mem =
        { fm with
          tryAct := 0
          tryPos := 0
          tryIns := 0
          bktSalt := Function.update fm.bktSalt fm.tryBkt fm.trySalt
          curRole := Function.update fm.curRole fm.tryBkt (tryRoleOf (fm.curRole fm.tryBkt))
          curIns := Function.update fm.curIns fm.tryBkt fm.tryIns }) := by
  dsimp only
  have hpt := hr.2.1
  set fm := extractFastMeta fl s.mem
  have hm7 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 7)) = fm.tryBkt :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hm8 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 8)) = fm.trySalt :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hm17 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 17)) = fm.tryIns :=
    clientResult_fastReadMetaProg hpt (by decide)
  generalize hcr_res :
    (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (fm.tryBkt, 12))) = cr_raw
  obtain ⟨hfr1, hr1, hbp1, hbt1, htr1, hof1, hoi1⟩ :=
    fastWriteBktLaneProg_frame (b := fm.tryBkt) (lane := 5) (val := fm.trySalt) hr
  generalize hs1_def :
    (Memory.spec 0).clientState s (fastWriteBktLaneProg ((fl.pBase, (fm.tryBkt, 5)), fm.trySalt)) =
      s1
  rw [hs1_def] at hfr1 hr1 hbp1 hbt1 htr1 hof1 hoi1
  obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hof2, hoi2⟩ :=
    fastWriteBktLaneProg_frame (b := fm.tryBkt) (lane := 12) (val := tryRoleOf cr_raw) hr1
  generalize hs2_def :
    (Memory.spec 0).clientState s1
      (fastWriteBktLaneProg ((fl.pBase, (fm.tryBkt, 12)), tryRoleOf cr_raw)) = s2
  rw [hs2_def] at hfr2 hr2 hbp2 hbt2 htr2 hof2 hoi2
  obtain ⟨hfr3, hr3, hbp3, hbt3, htr3, hof3, hoi3⟩ :=
    fastWriteBktLaneProg_frame (b := fm.tryBkt) (lane := 13) (val := fm.tryIns) hr2
  generalize hs3_def :
    (Memory.spec 0).clientState s2
      (fastWriteBktLaneProg ((fl.pBase, (fm.tryBkt, 13)), fm.tryIns)) = s3
  rw [hs3_def] at hfr3 hr3 hbp3 hbt3 htr3 hof3 hoi3
  obtain ⟨hfr4, hr4, hc4, hbp4, hbt4, htr4, hoi4, hof4, hm2_4, hfm4⟩ :=
    clearTryMetaProg_frame hr3
  generalize hs4_def : (Memory.spec 0).clientState s3 (clearTryMetaProg fl.pBase) = s4
  rw [hs4_def] at hfr4 hr4 hbp4 hbt4 htr4 hoi4 hof4 hm2_4 hfm4
  have htot : (Memory.spec 0).clientState s (commitTrySaltProg fl.pBase) = s4 ∧
      memoryCost (commitTrySaltProg fl.pBase) s ≤ 75 := by
    unfold commitTrySaltProg
    have cm7 := memoryCost_fastReadMetaProg (fl.pBase, 7) s
    have cm8 := memoryCost_fastReadMetaProg (fl.pBase, 8) s
    have cm17 := memoryCost_fastReadMetaProg (fl.pBase, 17) s
    have cl12 := memoryCost_fastReadBktLaneProg (fl.pBase, (fm.tryBkt, 12)) s
    have cw5 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (fm.tryBkt, 5)), fm.trySalt) s
    have cw12 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (fm.tryBkt, 12)), tryRoleOf cr_raw) s1
    have cw13 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (fm.tryBkt, 13)), fm.tryIns) s2
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hm7,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hm8,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadMetaProg, hm17,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadBktLaneProg, hcr_res,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_tryRoleProg, clientResult_tryRoleProg, memoryCost_tryRoleProg,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs2_def,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs3_def, hs4_def]
    exact ⟨rfl, by omega⟩
  rw [htot.1]
  refine ⟨hfr4.trans (hfr3.trans (hfr2.trans hfr1)), hr4, htot.2,
    hbp4.trans (hbp3.trans (hbp2.trans hbp1)),
    fun b hb r hr_lt => (hbt4 b hb r hr_lt).trans ((hbt3 b hb r hr_lt).trans
      ((hbt2 b hb r hr_lt).trans (hbt1 b hb r hr_lt))),
    fun r hr_lt => (htr4 r hr_lt).trans ((htr3 r hr_lt).trans
      ((htr2 r hr_lt).trans (htr1 r hr_lt))),
    fun a ha => (hoi4 a ha).trans ((hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha))),
    fun a ha => (hof4 a ha).trans ((hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha))),
    fun hb hts hti => ?_⟩
  have hcr_eq : cr_raw = fm.curRole fm.tryBkt := by
    rw [← hcr_res, clientResult_fastReadBktLaneProg hpt hb (by decide)]
    change _ = (if fm.tryBkt < numBucketsWhp fl.N then _ else 0)
    rw [ite_eq_left hb]
  subst hcr_eq
  have htr_le : tryRoleOf (fm.curRole fm.tryBkt) ≤ fl.N := by
    have := hr.1.bounds_le_N.1
    have : 1 ≤ slabScale fl.N ^ 12 :=
      Nat.one_le_pow 12 _ (by have := two_le_slabScale fl.N; omega)
    unfold tryRoleOf; split_ifs <;> omega
  obtain ⟨hm2_a, hfm_a⟩ := extractFastMeta_writeBktLane hr hb (Or.inl rfl) hts
  obtain ⟨hm2_b, hfm_b⟩ := extractFastMeta_writeBktLane hr1 hb
    (Or.inr ⟨by decide, by decide⟩ : 12 = 5 ∨ (12 ≤ 12 ∧ 12 < 16)) htr_le
  obtain ⟨hm2_c, hfm_c⟩ := extractFastMeta_writeBktLane hr2 hb
    (Or.inr ⟨by decide, by decide⟩ : 13 = 5 ∨ (12 ≤ 13 ∧ 13 < 16)) hti
  rw [ite_eq_left rfl] at hfm_a
  rw [ite_eq_right (by decide), ite_eq_left rfl] at hfm_b
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl] at hfm_c
  rw [hs1_def] at hm2_a hfm_a
  rw [hs2_def] at hm2_b hfm_b
  rw [hs3_def] at hm2_c hfm_c
  exact ⟨hm2_4.trans (hm2_c.trans (hm2_b.trans hm2_a)), by rw [hfm4, hfm_c, hfm_b, hfm_a]⟩

theorem commitTrySaltProg_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (commitTrySaltProg pBase)) := by
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (commitTrySaltProg_frame hr).2.1⟩

theorem realizesBounded_commitTrySalt :
    RealizesBounded .exact commitTrySaltProg
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hrl := realizesBounded_fastReadBktLane
  have htr := realizesBounded_tryRole
  have hwl := realizesBounded_fastWriteBktLane
  have hcm := realizesBounded_clearTryMeta
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg,
      runClient_state_fastReadBktLaneProg, runClient_state_tryRoleProg] at *
    have hp1 := fastWriteBktLaneProg_pre (x := ((fl.pBase,
      (((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 7))).1, 5)),
      ((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 8))).1)) ⟨fl, rfl, hr⟩
    have hp2 := fastWriteBktLaneProg_pre (x := ((fl.pBase,
      (((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 7))).1, 12)),
      ((Memory.spec 0).runClient s (tryRoleProg
        ((Memory.spec 0).runClient s (fastReadBktLaneProg (fl.pBase,
          (((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 7))).1, 12)))).1)).1)) hp1
    have hp3 := fastWriteBktLaneProg_pre (x := ((fl.pBase,
      (((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 7))).1, 13)),
      ((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 17))).1)) hp2
    first | exact hw6 | exact ⟨fl, rfl, hr⟩ | exact hp1 | exact hp2 | exact hp3 | omega)

private def writeStartTryMetaProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, b) => do
    fastWriteMetaProg ((pBase, 6), 1)
    fastWriteMetaProg ((pBase, 7), b)
    writeTryResetMetaProg (pBase, 0)

private theorem writeStartTryMetaProg_frame {fl : FastEpochLayout} {w b : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (writeStartTryMetaProg (fl.pBase, b))
    let fm := extractFastMeta fl s.mem
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (writeStartTryMetaProg (fl.pBase, b)) s ≤ 25 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    extractFastMeta fl s'.mem =
      { fm with tryAct := 1, tryBkt := b, trySalt := 0, tryPos := 0, tryIns := 0 } := by
  dsimp only
  set fm := extractFastMeta fl s.mem
  have c6 := memoryCost_fastWriteMetaProg ((fl.pBase, 6), 1) s
  obtain ⟨hfr1, hr1, hbp1, hbt1, htr1, hoi1, hof1, hm2_1, hfm1⟩ :=
    extractFastMeta_writeMeta (off := 6) (val := 1) hr (Or.inl ⟨by decide, by decide⟩)
  generalize hs1_def :
    (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 6), 1)) = s1
  rw [hs1_def] at hfr1 hr1 hbp1 hbt1 htr1 hoi1 hof1 hm2_1 hfm1
  have c7 := memoryCost_fastWriteMetaProg ((fl.pBase, 7), b) s1
  obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hoi2, hof2, hm2_2, hfm2⟩ :=
    extractFastMeta_writeMeta (off := 7) (val := b) hr1 (Or.inl ⟨by decide, by decide⟩)
  generalize hs2_def :
    (Memory.spec 0).clientState s1 (fastWriteMetaProg ((fl.pBase, 7), b)) = s2
  rw [hs2_def] at hfr2 hr2 hbp2 hbt2 htr2 hoi2 hof2 hm2_2 hfm2
  obtain ⟨hfr3, hr3, hc3, hbp3, hbt3, htr3, hoi3, hof3, hm2_3, hfm3⟩ :=
    writeTryResetMetaProg_frame (nextSalt := 0) hr2
  generalize hs3_def : (Memory.spec 0).clientState s2 (writeTryResetMetaProg (fl.pBase, 0)) = s3
  rw [hs3_def] at hfr3 hr3 hbp3 hbt3 htr3 hoi3 hof3 hm2_3 hfm3
  have htot : (Memory.spec 0).clientState s (writeStartTryMetaProg (fl.pBase, b)) = s3 ∧
      memoryCost (writeStartTryMetaProg (fl.pBase, b)) s ≤ 25 := by
    unfold writeStartTryMetaProg
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs2_def, hs3_def]
    exact ⟨rfl, by omega⟩
  rw [htot.1]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl] at hfm1
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_left rfl] at hfm2
  exact ⟨hfr3.trans (hfr2.trans hfr1), hr3, htot.2, hbp3.trans (hbp2.trans hbp1),
    fun b' hb' r hr_lt =>
      (hbt3 b' hb' r hr_lt).trans ((hbt2 b' hb' r hr_lt).trans (hbt1 b' hb' r hr_lt)),
    fun r hr_lt => (htr3 r hr_lt).trans ((htr2 r hr_lt).trans (htr1 r hr_lt)),
    fun a ha => (hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha)),
    fun a ha => (hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha)),
    hm2_3.trans (hm2_2.trans hm2_1), by rw [hfm3, hfm2, hfm1]⟩

private theorem realizesBounded_writeStartTryMeta :
    RealizesBounded .exact writeStartTryMetaProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hw := realizesBounded_fastWriteMeta
  have hwr := realizesBounded_writeTryResetMeta
  realize
  all_goals (
    rcases d with ⟨pBase, b⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    have hp1 := fastWriteMetaProg_pre (x := ((fl.pBase, 6), 1)) ⟨fl, rfl, hr⟩
    have hp2 := fastWriteMetaProg_pre (x := ((fl.pBase, 7), b)) hp1
    first | exact ⟨fl, rfl, hr⟩ | exact hp1 | exact hp2 | omega)

/-- Initiate candidate salt search on bucket `b` (`tryAct := 1, tryBkt := b, trySalt := 0,
tryPos := 0, tryIns := 0`, resetting `tryRoleOf (curRole b)`). -/
def startTrySaltProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, b) => do
    let cRole ← fastReadBktLaneProg (pBase, (b, 12))
    let tRole ← tryRoleProg cRole
    fastBTreeResetProg (pBase, (b, tRole))
    writeStartTryMetaProg (pBase, b)

theorem startTrySaltProg_frame {fl : FastEpochLayout} {w b : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (startTrySaltProg (fl.pBase, b))
    let fm := extractFastMeta fl s.mem
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (startTrySaltProg (fl.pBase, b)) s ≤ 50 ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (b < numBucketsWhp fl.N →
      extractFastMeta fl s'.mem =
        { fm with tryAct := 1, tryBkt := b, trySalt := 0, tryPos := 0, tryIns := 0 } ∧
      ValidWhpSlice fl.N 0
        (extractBTreeSlice fl.btL b (tryRoleOf (fm.curRole b)) s'.mem) (fun _ => none) ∧
      (∀ b' < numBucketsWhp fl.N, ∀ role' < 3,
        (b' ≠ b ∨ role' ≠ tryRoleOf (fm.curRole b)) →
        extractBTreeSlice fl.btL b' role' s'.mem = extractBTreeSlice fl.btL b' role' s.mem)) := by
  dsimp only
  have hpt := hr.2.1
  set fm := extractFastMeta fl s.mem
  generalize hcr_res :
    (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12))) = cr_raw
  obtain ⟨hfr_r, hr_r, hc_r, hbp_r, hfm_r, hm2_r, htr_r, hoi_r, hof_r, hsl_r⟩ :=
    fastBTreeResetProg_spec (b := b) (role := tryRoleOf cr_raw) hr
  generalize hs1_def :
    (Memory.spec 0).clientState s (fastBTreeResetProg (fl.pBase, (b, tryRoleOf cr_raw))) = s1
  rw [hs1_def] at hfr_r hr_r hbp_r hfm_r hm2_r htr_r hoi_r hof_r hsl_r
  obtain ⟨hfr_w, hr_w, hc_w, hbp_w, hbt_w, htr_w, hoi_w, hof_w, hm2_w, hfm_w⟩ :=
    writeStartTryMetaProg_frame (b := b) hr_r
  generalize hs2_def :
    (Memory.spec 0).clientState s1 (writeStartTryMetaProg (fl.pBase, b)) = s2
  rw [hs2_def] at hfr_w hr_w hbp_w hbt_w htr_w hoi_w hof_w hm2_w hfm_w
  have htot : (Memory.spec 0).clientState s (startTrySaltProg (fl.pBase, b)) = s2 ∧
      memoryCost (startTrySaltProg (fl.pBase, b)) s ≤ 50 := by
    unfold startTrySaltProg
    have cl12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadBktLaneProg, hcr_res,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_tryRoleProg, clientResult_tryRoleProg, memoryCost_tryRoleProg,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def, hs2_def]
    exact ⟨rfl, by omega⟩
  rw [htot.1]
  refine ⟨hfr_w.trans hfr_r, hr_w, htot.2, hbp_w.trans hbp_r,
    fun r hr_lt => (htr_w r hr_lt).trans (htr_r r hr_lt),
    fun a ha => (hoi_w a ha).trans (hoi_r a ha),
    fun a ha => (hof_w a ha).trans (hof_r a ha),
    hm2_w.trans hm2_r, fun hb => ?_⟩
  have hcr_eq : cr_raw = fm.curRole b := by
    rw [← hcr_res, clientResult_fastReadBktLaneProg hpt hb (by decide)]
    change _ = (if b < numBucketsWhp fl.N then _ else 0)
    rw [ite_eq_left hb]
  subst hcr_eq
  have htr_lt : tryRoleOf (fm.curRole b) < 3 := by
    unfold tryRoleOf; split_ifs <;> decide
  obtain ⟨hv_z, hsl_o⟩ := hsl_r hb htr_lt
  rw [hfm_r] at hfm_w
  exact ⟨hfm_w, by rw [hbt_w _ hb _ htr_lt]; exact hv_z,
    fun b' hb' r' hr' hne => (hbt_w b' hb' r' hr').trans (hsl_o b' hb' r' hr' hne)⟩

theorem startTrySaltProg_pre {w : ℕ} {x : ℕ × ℕ} {s : Memory.State} (h : FastProgPre w x.1 s) :
    FastProgPre w x.1 ((Memory.spec 0).clientState s (startTrySaltProg x)) := by
  rcases x with ⟨pBase, b⟩
  obtain ⟨fl, rfl, hr⟩ := h
  exact ⟨fl, rfl, (startTrySaltProg_frame hr).2.1⟩

theorem realizesBounded_startTrySalt :
    RealizesBounded .exact startTrySaltProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have htr := realizesBounded_tryRole
  have hbr := realizesBounded_fastBTreeReset
  have hws := realizesBounded_writeStartTryMeta
  realize
  all_goals (
    rcases d with ⟨pBase, b⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktLaneProg,
      runClient_state_tryRoleProg] at *
    first
    | exact hw6
    | exact ⟨fl, rfl, hr⟩
    | exact fastBTreeResetProg_pre (x := (fl.pBase, (b,
        ((Memory.spec 0).runClient s (tryRoleProg
          ((Memory.spec 0).runClient s (fastReadBktLaneProg (fl.pBase, (b, 12)))).1)).1)))
        ⟨fl, rfl, hr⟩
    | omega)

/-- Read-only check at `tryPos = cnt`: returns `1` iff `drainPos` is active in `BufOld` with bucket
`tryBkt` (`loc < cnt`) and its fingerprint under `trySalt` already hits in `tryMap`. -/
private def drainTryCheckDpInnerProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((pBase, b), (loc, ts)) => do
    let cnt ← fastReadBktCntProg (pBase, b)
    if loc < cnt then do
      let (q, _v) ← fastBpReadAtProg (pBase, (b, loc))
      let u_val ← fastFeistelReconProg (pBase, (b, q))
      let fp_dp ← fastFpHashProg (pBase, (ts, u_val))
      let cRole ← fastReadBktLaneProg (pBase, (b, 12))
      let tRole ← tryRoleProg cRole
      let (hit, _v') ← fastBTreeLookupProg ((pBase, (b, tRole)), fp_dp)
      pure hit
    else
      pure 0

@[simp] private theorem runClient_state_drainTryCheckDpInnerProg
    (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (drainTryCheckDpInnerProg x)).2.1 = s := by
  rcases x with ⟨⟨pBase, b⟩, ⟨loc, ts⟩⟩
  change (Memory.spec 0).clientState s (drainTryCheckDpInnerProg ((pBase, b), (loc, ts))) = s
  unfold drainTryCheckDpInnerProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg]
    rcases (Memory.spec 0).clientResult s (fastBpReadAtProg (pBase, (b, loc))) with ⟨q, _⟩
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_fastFeistelReconProg,
      StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_tryRoleProg,
      StateTransitionSpec.clientState_bind, clientState_fastBTreeLookupProg]
    rcases (Memory.spec 0).clientResult s _ with ⟨_, _⟩
    rfl
  · rfl

private theorem realizesBounded_drainTryCheckDpInner :
    RealizesBounded .exact drainTryCheckDpInnerProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrc := realizesBounded_fastReadBktCnt
  have hra := realizesBounded_fastBpReadAt
  have hfr := realizesBounded_fastFeistelRecon
  have hfp := realizesBounded_fastFpHash
  have hrl := realizesBounded_fastReadBktLane
  have htr := realizesBounded_tryRole
  have hbl := realizesBounded_fastBTreeLookup
  realize
  all_goals (
    rcases d with ⟨⟨pBase, b⟩, ⟨loc, ts⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktCntProg,
      runClient_state_fastBpReadAtProg, runClient_state_fastFeistelReconProg,
      runClient_state_fastFpHashProg, runClient_state_fastReadBktLaneProg,
      runClient_state_tryRoleProg] at *
    first | exact hw6 | exact ⟨fl, rfl, hr⟩ | omega)

private def drainTryCheckDpProg (pBase : ℕ) : Memory.Prog ℕ := do
  let curR ← fastReadMetaProg (pBase, 3)
  let dp ← fastReadMetaProg (pBase, 5)
  let b ← fastReadMetaProg (pBase, 7)
  let ts ← fastReadMetaProg (pBase, 8)
  if curR < 2 then do
    let (act, (b_dp, loc_dp)) ← fastBufCheckSlotProg ((pBase, 1 - curR), dp)
    if act = 1 ∧ b_dp = b then
      drainTryCheckDpInnerProg ((pBase, b), (loc_dp, ts))
    else
      pure 0
  else
    pure 0

@[simp] private theorem runClient_state_drainTryCheckDpProg (pBase : ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (drainTryCheckDpProg pBase)).2.1 = s := by
  change (Memory.spec 0).clientState s (drainTryCheckDpProg pBase) = s
  unfold drainTryCheckDpProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastBufCheckSlotProg]
    rcases (Memory.spec 0).clientResult s _ with ⟨act, ⟨b_dp, loc_dp⟩⟩
    dsimp only
    split_ifs
    · exact runClient_state_drainTryCheckDpInnerProg _ s
    · rfl
  · rfl

private theorem realizesBounded_drainTryCheckDp :
    RealizesBounded .exact drainTryCheckDpProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hcs := realizesBounded_fastBufCheckSlot
  have hin := realizesBounded_drainTryCheckDpInner
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg,
      runClient_state_fastBufCheckSlotProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-- Tail of `drainTryScanSlotProg` once `u_val` is confirmed in `mapBTree b` at `tp`. -/
private def drainTryInsertOrAdvProg : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((pBase, b), (tp, cRole)), u_val) => do
    let ts ← fastReadMetaProg (pBase, 8)
    let fp_try ← fastFpHashProg (pBase, (ts, u_val))
    let tRole ← tryRoleProg cRole
    let (hit, _loc0) ← fastBTreeLookupProg ((pBase, (b, tRole)), fp_try)
    if hit = 1 then
      advanceTrySaltProg pBase
    else do
      let ti ← fastReadMetaProg (pBase, 17)
      let nCap ← Memory.read (pBase + 0)
      if ti < nCap ∧ tp < nCap then do
        fastBTreeInsertProg ((pBase, (b, tRole)), (fp_try, tp))
        fastWriteMetaProg ((pBase, 17), ti + 1)
        fastWriteMetaProg ((pBase, 9), tp + 1)
      else
        pure ()

private theorem drainTryInsertOrAdvProg_pre {w : ℕ} {x : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : FastProgPre w x.1.1.1 s) :
    FastProgPre w x.1.1.1 ((Memory.spec 0).clientState s (drainTryInsertOrAdvProg x)) := by
  rcases x with ⟨⟨⟨pBase, b⟩, ⟨tp, cRole⟩⟩, u_val⟩
  obtain ⟨fl, rfl, hr⟩ := h
  unfold drainTryInsertOrAdvProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
    StateTransitionSpec.clientState_bind, clientState_tryRoleProg,
    StateTransitionSpec.clientState_bind, clientState_fastBTreeLookupProg]
  rcases (Memory.spec 0).clientResult s _ with ⟨hit, _⟩
  dsimp only
  split_ifs with h1
  · exact advanceTrySaltProg_pre ⟨fl, rfl, hr⟩
  · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
      StateTransitionSpec.clientState_bind]
    have hr0 : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
    rw [hr0]
    split_ifs
    · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
      exact fastWriteMetaProg_pre (x := ((fl.pBase, 9), tp + 1))
        (fastWriteMetaProg_pre (x := ((fl.pBase, 17), _))
          (fastBTreeInsertProg_pre (x := ((fl.pBase, (b, _)), (_, tp))) ⟨fl, rfl, hr⟩))
    · exact ⟨fl, rfl, hr⟩

private theorem realizesBounded_drainTryInsertOrAdv :
    RealizesBounded .exact drainTryInsertOrAdvProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((pBase, _), _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hfp := realizesBounded_fastFpHash
  have htr := realizesBounded_tryRole
  have hbl := realizesBounded_fastBTreeLookup
  have had := realizesBounded_advanceTrySalt
  have hbi := realizesBounded_fastBTreeInsert
  have hwm := realizesBounded_fastWriteMeta
  realize
  all_goals (
    rcases d with ⟨⟨⟨pBase, b⟩, ⟨tp, cRole⟩⟩, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm0 : s.mem (fl.pBase + 0) = fl.N := hr.2.1 0 (by decide)
    have hm0_0 : s.mem fl.pBase = fl.N := by rwa [Nat.add_zero] at hm0
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg,
      runClient_state_fastFpHashProg, runClient_state_tryRoleProg,
      runClient_state_fastBTreeLookupProg, hm0, hm0_0] at *
    have hp_ins := fastBTreeInsertProg_pre (x := ((fl.pBase, (b,
      ((Memory.spec 0).runClient s (tryRoleProg cRole)).1)),
      (((Memory.spec 0).runClient s (fastFpHashProg (fl.pBase,
        (((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 8))).1, u_val)))).1, tp)))
      ⟨fl, rfl, hr⟩
    have hp_w1 := fastWriteMetaProg_pre (x := ((fl.pBase, 17),
      ((Memory.spec 0).runClient s (fastReadMetaProg (fl.pBase, 17))).1 + 1)) hp_ins
    first | exact hw6 | exact ⟨fl, rfl, hr⟩ | exact hp_ins | exact hp_w1 | omega)

/-- Scan one slot `tp < cnt` of `tryBkt = b` during candidate salt search. -/
private def drainTryScanSlotProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((pBase, b), tp) => do
    let (q, _v) ← fastBpReadAtProg (pBase, (b, tp))
    let u_val ← fastFeistelReconProg (pBase, (b, q))
    let bs ← fastReadBktLaneProg (pBase, (b, 5))
    let cRole ← fastReadBktLaneProg (pBase, (b, 12))
    let fp_cur ← fastFpHashProg (pBase, (bs, u_val))
    let (hit_c, loc_c) ← fastBTreeLookupProg ((pBase, (b, cRole)), fp_cur)
    if hit_c = 1 ∧ loc_c = tp then
      drainTryInsertOrAdvProg (((pBase, b), (tp, cRole)), u_val)
    else do
      let nCap ← Memory.read (pBase + 0)
      if tp < nCap then
        fastWriteMetaProg ((pBase, 9), tp + 1)
      else
        pure ()

private theorem drainTryScanSlotProg_pre {w : ℕ} {x : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (drainTryScanSlotProg x)) := by
  rcases x with ⟨⟨pBase, b⟩, tp⟩
  obtain ⟨fl, rfl, hr⟩ := h
  unfold drainTryScanSlotProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg]
  rcases (Memory.spec 0).clientResult s (fastBpReadAtProg (fl.pBase, (b, tp))) with ⟨q, _⟩
  dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastFeistelReconProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
    StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
    StateTransitionSpec.clientState_bind, clientState_fastBTreeLookupProg]
  rcases (Memory.spec 0).clientResult s _ with ⟨hit_c, loc_c⟩
  dsimp only
  split_ifs
  · exact drainTryInsertOrAdvProg_pre (x := (((fl.pBase, b), (tp, _)), _)) ⟨fl, rfl, hr⟩
  · rw [StateTransitionSpec.clientState_bind]
    have hr0 : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
    rw [hr0]
    split_ifs
    · exact fastWriteMetaProg_pre (x := ((fl.pBase, 9), tp + 1)) ⟨fl, rfl, hr⟩
    · exact ⟨fl, rfl, hr⟩

private theorem realizesBounded_drainTryScanSlot :
    RealizesBounded .exact drainTryScanSlotProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hra := realizesBounded_fastBpReadAt
  have hfr := realizesBounded_fastFeistelRecon
  have hrl := realizesBounded_fastReadBktLane
  have hfp := realizesBounded_fastFpHash
  have hbl := realizesBounded_fastBTreeLookup
  have hin := realizesBounded_drainTryInsertOrAdv
  have hwm := realizesBounded_fastWriteMeta
  realize
  all_goals (
    rcases d with ⟨⟨pBase, b⟩, tp⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm0 : s.mem (fl.pBase + 0) = fl.N := hr.2.1 0 (by decide)
    have hm0_0 : s.mem fl.pBase = fl.N := by rwa [Nat.add_zero] at hm0
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastBpReadAtProg,
      runClient_state_fastFeistelReconProg, runClient_state_fastReadBktLaneProg,
      runClient_state_fastFpHashProg, runClient_state_fastBTreeLookupProg, hm0, hm0_0] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-- Single candidate salt-search step when `tryAct = 1` (`¬ReadsWidth`). -/
def drainTryStepProg (pBase : ℕ) : Memory.Prog Unit := do
  let ta ← fastReadMetaProg (pBase, 6)
  let b ← fastReadMetaProg (pBase, 7)
  let M ← Memory.read (pBase + 11)
  if ta = 1 ∧ b < M then do
    let cnt ← fastReadBktCntProg (pBase, b)
    let tp ← fastReadMetaProg (pBase, 9)
    if tp < cnt then
      drainTryScanSlotProg ((pBase, b), tp)
    else do
      let coll ← drainTryCheckDpProg pBase
      if coll = 0 then
        commitTrySaltProg pBase
      else
        advanceTrySaltProg pBase
  else
    pure ()

theorem drainTryStepProg_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (drainTryStepProg pBase)) := by
  obtain ⟨fl, rfl, hr⟩ := h
  unfold drainTryStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind]
  have hm11 : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
  rw [hm11]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
    split_ifs
    · exact drainTryScanSlotProg_pre (x := ((fl.pBase, _), _)) ⟨fl, rfl, hr⟩
    · rw [StateTransitionSpec.clientState_bind]
      have hdp_st : (Memory.spec 0).clientState s (drainTryCheckDpProg fl.pBase) = s :=
        runClient_state_drainTryCheckDpProg fl.pBase s
      rw [hdp_st]
      split_ifs
      · exact commitTrySaltProg_pre ⟨fl, rfl, hr⟩
      · exact advanceTrySaltProg_pre ⟨fl, rfl, hr⟩
  · exact ⟨fl, rfl, hr⟩

theorem realizesBounded_drainTryStep :
    RealizesBounded .exact drainTryStepProg
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hrc := realizesBounded_fastReadBktCnt
  have hsc := realizesBounded_drainTryScanSlot
  have hdp := realizesBounded_drainTryCheckDp
  have hcm := realizesBounded_commitTrySalt
  have had := realizesBounded_advanceTrySalt
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg,
      runClient_state_fastReadBktCntProg, runClient_state_drainTryCheckDpProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-- `advanceTrySaltProg` preserves `FastEpochInvGen` unconditionally whenever `tryAct = 1`. -/
theorem advanceTrySaltProg_inv {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hta1 : (extractFastMeta fl s.mem).tryAct = 1) :
    let s' := (Memory.spec 0).clientState s (advanceTrySaltProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    let nextSalt := if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0
    s'.frontier = s.frontier ∧
    memoryCost (advanceTrySaltProg fl.pBase) s ≤ 52 ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    extractFastMeta fl s'.mem = { fm with trySalt := nextSalt, tryPos := 0, tryIns := 0 } := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set nextSalt := if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, hta_le, htry_all⟩ := hinv.tiers
  obtain ⟨hsub, hb_t, hs_t, _, hsc_t, _, _, _, _, _⟩ := htry_all hta1
  obtain ⟨hfr', hr', hc', hbp', htr', hoi', hof', hm2', hspec⟩ := advanceTrySaltProg_frame hr₀
  generalize hs'_def : (Memory.spec 0).clientState s (advanceTrySaltProg fl.pBase) = s'
  rw [hs'_def] at hfr' hr' hbp' htr' hoi' hof' hm2' hspec
  obtain ⟨hfm', hv_z, hsl_o⟩ := hspec hb_t
  have hns_lt : nextSalt < sMaxWhp fl.c fl.N := by
    dsimp only [nextSalt]
    by_cases h1 : fm.trySalt + 1 < sMaxWhp fl.c fl.N
    · rw [ite_eq_left h1]; exact h1
    · rw [ite_eq_right h1]; exact lt_of_le_of_lt (Nat.zero_le _) hs_t
  have hcnt_le : bp.bktCount fm.tryBkt ≤ 4 * slabScale fl.N ^ 12 := hinv.bkt_le_capMax _ hb_t
  have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
      fastKeyAt fl seeds.bkt s'.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
    fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp' hoi' hb' hl'
  have hold_bounds : ∀ rk b₂ l₂, mapOld rk = some (b₂, l₂) →
      b₂ < numBucketsWhp fl.N ∧ l₂ < bp.bktCount b₂ := by
    intro rk b₂ l₂ hm₂
    have hh := hold_half; rw [ite_eq_left hsub] at hh
    obtain ⟨_, hb₂, hl₂, _⟩ := hh.2.2.2.2.2.2.2 rk b₂ l₂ hm₂
    exact ⟨hb₂, hl₂⟩
  have hcr_eq : (extractFastMeta fl s'.mem).curBufRole = fm.curBufRole := by rw [hfm']
  have hss_eq : (extractFastMeta fl s'.mem).subStep = fm.subStep := by rw [hfm']
  have hdp_eq : (extractFastMeta fl s'.mem).drainPos = fm.drainPos := by rw [hfm']
  have hta_eq : (extractFastMeta fl s'.mem).tryAct = fm.tryAct := by rw [hfm']
  have htb_eq : (extractFastMeta fl s'.mem).tryBkt = fm.tryBkt := by rw [hfm']
  have hts_eq : (extractFastMeta fl s'.mem).trySalt = nextSalt := by rw [hfm']
  have htp_eq : (extractFastMeta fl s'.mem).tryPos = 0 := by rw [hfm']
  have hti_eq : (extractFastMeta fl s'.mem).tryIns = 0 := by rw [hfm']
  have hbs_eq : (extractFastMeta fl s'.mem).bktSalt = fm.bktSalt := by rw [hfm']
  have hrl_eq : (extractFastMeta fl s'.mem).curRole = fm.curRole := by rw [hfm']
  have hci_eq : (extractFastMeta fl s'.mem).curIns = fm.curIns := by rw [hfm']
  have hsi_eq : (extractFastMeta fl s'.mem).shadowIns = fm.shadowIns := by rw [hfm']
  have hsc_eq : (extractFastMeta fl s'.mem).shadowCode = fm.shadowCode := by rw [hfm']
  have hbm_s' : ∀ b' < numBucketsWhp fl.N,
      let fm2 := extractFastMeta fl s'.mem
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
       rw [congrFun hsc_eq b'] at hsc0'
       rw [hta_eq, htb_eq] at hnt'
       exact (hinv.bkt_meta_bounds b' hb').2.2.2 hsc0' hnt'⟩
  refine ⟨hfr', hc', ?_, hbp', htr', hoi', hof', hfm'⟩
  obtain ⟨hc_N, hc_sb, hc_sf, hc_bp, hc_cap, hc_ref⟩ :=
    FastEpochInvGen.fixed_pool_core hv hinv hbp' hoi' hof'
  refine
    { param_table := hr'.2.1
      hdr_N := hc_N
      mode_zero := hm2'.trans hinv.mode_zero
      seed_bkt := hc_sb
      seed_fp := hc_sf
      bp_inv := hc_bp
      bkt_le_capMax := hc_cap
      refines := hc_ref
      role_lt := by rw [hcr_eq]; exact hinv.role_lt
      subStep_lt := by rw [hss_eq]; exact hinv.subStep_lt
      bkt_meta_bounds := hbm_s'
      tiers := ?_ }
  dsimp only
  have htr_c := htr' fm.curBufRole hinv.role_lt
  have htr_o := htr' (1 - fm.curBufRole) (by have := hinv.role_lt; omega)
  refine ⟨mapCur, mapOld, mapBTree,
    by rw [hcr_eq, htr_c]; exact hv_cur,
    by rw [hcr_eq, htr_c]; exact hrb_cur,
    by rw [hcr_eq, htr_c]; exact hrc_cur,
    by rw [hcr_eq, htr_c, hss_eq]; exact hia_cur,
    by rw [hcr_eq, htr_c]; exact hna_cur,
    fun rk b' loc' hm => by
      obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
      exact ⟨hb', by rw [hbp']; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
    ?_, ?_, ?_, ?_, by rw [hta_eq]; exact hta_le, ?_⟩
  · rw [hss_eq, hcr_eq, htr_o, hdp_eq, hbp', ite_eq_left hsub]
    rw [ite_eq_left hsub] at hold_half
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hold_half
    exact ⟨h1, h2, h3, h4, h5, h6, h7, fun rk b' loc' hm => by
      obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := h8 rk b' loc' hm
      exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩⟩
  · intro b' hb'
    rw [hbp']
    refine ⟨?_, fun fp' loc' hm => ?_⟩
    · rw [congrFun hci_eq b', congrFun hrl_eq b']
      have hr_b' := (hinv.bkt_meta_bounds b' hb').2.1
      have hne_tr := (tryRoleOf_lt_and_ne hr_b').2.1
      have hdisj : b' ≠ fm.tryBkt ∨ fm.curRole b' ≠ tryRoleOf (fm.curRole fm.tryBkt) := by
        by_cases he : b' = fm.tryBkt
        · subst he; exact Or.inr hne_tr.symm
        · exact Or.inl he
      rw [hsl_o b' hb' _ hr_b' hdisj]
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
    rw [hbp'] at hloc'
    obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
    refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
    rw [fpHash_congr_salt (congrFun hbs_eq b') u']; exact ht'
  · intro b' hb' hsc'
    rw [congrFun hsc_eq b'] at hsc' ⊢
    rw [hta_eq, htb_eq, congrFun hsi_eq b', congrFun hci_eq b', congrFun hrl_eq b', hbp']
    obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc'
    have hne_b : b' ≠ fm.tryBkt := fun he => by subst he; exact hsc' hsc_t
    have hr_sm := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
    rw [hsl_o b' hb' _ hr_sm (Or.inl hne_b)]
    exact ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩
  · intro _
    rw [hss_eq, htp_eq, hti_eq, hbp']
    refine ⟨hsub, htb_eq.symm ▸ hb_t, hts_eq.symm ▸ hns_lt, Nat.zero_le _,
      by rw [htb_eq, congrFun hsc_eq fm.tryBkt]; exact hsc_t,
      by rw [htb_eq]
         have hcap : bp.bktCount fm.tryBkt ≤ capMaxWhp fl.N :=
           hinv.bkt_le_capMax fm.tryBkt hb_t
         unfold capMaxWhp at hcap
         simp only [Nat.mul_zero, Nat.zero_add, Nat.sub_zero]
         exact Nat.mul_le_mul_left 5 hcap |>.trans (by ring_nf; exact le_rfl),
      fun _ => none, ?_,
      (fun _ _ h => (Option.some_ne_none _ h.symm).elim),
      (fun _ h => absurd h (Nat.not_lt_zero _))⟩
    rw [htb_eq, congrFun hrl_eq fm.tryBkt]
    exact hv_z

/-- `commitTrySaltProg` preserves `FastEpochInvGen` unconditionally whenever `tryAct = 1` and
`tryPos = bktCount tryBkt`. -/
theorem commitTrySaltProg_inv {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hta1 : (extractFastMeta fl s.mem).tryAct = 1)
    (htp_cnt : (extractFastMeta fl s.mem).tryPos =
      (extractBlockPool fl.mp s.mem).bktCount (extractFastMeta fl s.mem).tryBkt) :
    let s' := (Memory.spec 0).clientState s (commitTrySaltProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    s'.frontier = s.frontier ∧
    memoryCost (commitTrySaltProg fl.pBase) s ≤ 75 ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ b < numBucketsWhp fl.N, ∀ r < 3,
      extractBTreeSlice fl.btL b r s'.mem = extractBTreeSlice fl.btL b r s.mem) ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    extractFastMeta fl s'.mem =
      { fm with
        tryAct := 0
        tryPos := 0
        tryIns := 0
        bktSalt := Function.update fm.bktSalt fm.tryBkt fm.trySalt
        curRole := Function.update fm.curRole fm.tryBkt (tryRoleOf (fm.curRole fm.tryBkt))
        curIns := Function.update fm.curIns fm.tryBkt fm.tryIns } := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  obtain ⟨h64_L12, _, hsMax_N, _⟩ := hv.bounds_le_N
  have hL12_pos : 1 ≤ slabScale fl.N ^ 12 :=
    Nat.one_le_pow 12 _ (by have := two_le_slabScale fl.N; omega)
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, _, htry_all⟩ := hinv.tiers
  obtain ⟨hsub, hb_t, hs_t, _, hsc_t, hti_le, tm, hv_tm, ht_s, ht_c⟩ := htry_all hta1
  have hti_le_5L : fm.tryIns ≤ 5 * slabScale fl.N ^ 12 := by
    have h0 : bp.bktCount fm.tryBkt - fm.tryPos = 0 := by rw [htp_cnt, Nat.sub_self]
    rw [h0] at hti_le; linarith
  have hti_lt_6L : fm.tryIns < 6 * slabScale fl.N ^ 12 := by linarith
  have hti_le_N : fm.tryIns ≤ fl.N := by linarith
  have hts_le_N : fm.trySalt ≤ fl.N := hs_t.le.trans hsMax_N
  obtain ⟨hfr', hr', hc', hbp', hbt', htr', hoi', hof', hspec⟩ := commitTrySaltProg_frame hr₀
  generalize hs'_def : (Memory.spec 0).clientState s (commitTrySaltProg fl.pBase) = s'
  rw [hs'_def] at hfr' hr' hbp' hbt' htr' hoi' hof' hspec
  obtain ⟨hm2', hfm'⟩ := hspec hb_t hts_le_N hti_le_N
  have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
      fastKeyAt fl seeds.bkt s'.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
    fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp' hoi' hb' hl'
  have hold_bounds : ∀ rk b₂ l₂, mapOld rk = some (b₂, l₂) →
      b₂ < numBucketsWhp fl.N ∧ l₂ < bp.bktCount b₂ := by
    intro rk b₂ l₂ hm₂
    have hh := hold_half; rw [ite_eq_left hsub] at hh
    obtain ⟨_, hb₂, hl₂, _⟩ := hh.2.2.2.2.2.2.2 rk b₂ l₂ hm₂
    exact ⟨hb₂, hl₂⟩
  have hcr_eq : (extractFastMeta fl s'.mem).curBufRole = fm.curBufRole := by rw [hfm']
  have hss_eq : (extractFastMeta fl s'.mem).subStep = fm.subStep := by rw [hfm']
  have hdp_eq : (extractFastMeta fl s'.mem).drainPos = fm.drainPos := by rw [hfm']
  have hta_eq : (extractFastMeta fl s'.mem).tryAct = 0 := by rw [hfm']
  have hbs_fn : (extractFastMeta fl s'.mem).bktSalt =
      Function.update fm.bktSalt fm.tryBkt fm.trySalt := congrArg FastEpochMeta.bktSalt hfm'
  have hrl_fn : (extractFastMeta fl s'.mem).curRole =
      Function.update fm.curRole fm.tryBkt (tryRoleOf (fm.curRole fm.tryBkt)) :=
    congrArg FastEpochMeta.curRole hfm'
  have hci_fn : (extractFastMeta fl s'.mem).curIns =
      Function.update fm.curIns fm.tryBkt fm.tryIns := congrArg FastEpochMeta.curIns hfm'
  have hsi_eq : (extractFastMeta fl s'.mem).shadowIns = fm.shadowIns := by rw [hfm']
  have hsc_eq : (extractFastMeta fl s'.mem).shadowCode = fm.shadowCode := by rw [hfm']
  have htr_lt : tryRoleOf (fm.curRole fm.tryBkt) < 3 :=
    (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds fm.tryBkt hb_t).2.1).1
  have hbm_s' : ∀ b' < numBucketsWhp fl.N,
      let fm2 := extractFastMeta fl s'.mem
      fm2.bktSalt b' < sMaxWhp fl.c fl.N ∧
      fm2.curRole b' < 3 ∧
      fm2.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
      (fm2.shadowCode b' = 0 → ¬(fm2.tryAct = 1 ∧ fm2.tryBkt = b') →
        fm2.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' =>
    ⟨by by_cases he : b' = fm.tryBkt
        · rw [he, congrFun hbs_fn fm.tryBkt, Function.update_self]; exact hs_t
        · rw [congrFun hbs_fn b', Function.update_of_ne he]; exact (hinv.bkt_meta_bounds b' hb').1,
     by by_cases he : b' = fm.tryBkt
        · rw [he, congrFun hrl_fn fm.tryBkt, Function.update_self]; exact htr_lt
        · rw [congrFun hrl_fn b', Function.update_of_ne he]
          exact (hinv.bkt_meta_bounds b' hb').2.1,
     by by_cases he : b' = fm.tryBkt
        · rw [he, congrFun hci_fn fm.tryBkt, Function.update_self]; linarith
        · rw [congrFun hci_fn b', Function.update_of_ne he]
          exact (hinv.bkt_meta_bounds b' hb').2.2.1,
     fun hsc0' _ => by
       by_cases he : b' = fm.tryBkt
       · rw [he, congrFun hci_fn fm.tryBkt, Function.update_self]; exact hti_lt_6L
       · rw [congrFun hci_fn b', Function.update_of_ne he]
         rw [congrFun hsc_eq b'] at hsc0'
         exact (hinv.bkt_meta_bounds b' hb').2.2.2 hsc0' (fun ⟨_, h2⟩ => he h2.symm)⟩
  refine ⟨hfr', hc', ?_, hbp', hbt', htr', hoi', hof', hfm'⟩
  obtain ⟨hc_N, hc_sb, hc_sf, hc_bp, hc_cap, hc_ref⟩ :=
    FastEpochInvGen.fixed_pool_core hv hinv hbp' hoi' hof'
  refine
    { param_table := hr'.2.1
      hdr_N := hc_N
      mode_zero := hm2'.trans hinv.mode_zero
      seed_bkt := hc_sb
      seed_fp := hc_sf
      bp_inv := hc_bp
      bkt_le_capMax := hc_cap
      refines := hc_ref
      role_lt := by rw [hcr_eq]; exact hinv.role_lt
      subStep_lt := by rw [hss_eq]; exact hinv.subStep_lt
      bkt_meta_bounds := hbm_s'
      tiers := ?_ }
  dsimp only
  have htr_c := htr' fm.curBufRole hinv.role_lt
  have htr_o := htr' (1 - fm.curBufRole) (by have := hinv.role_lt; omega)
  refine ⟨mapCur, mapOld, Function.update mapBTree fm.tryBkt tm,
    by rw [hcr_eq, htr_c]; exact hv_cur,
    by rw [hcr_eq, htr_c]; exact hrb_cur,
    by rw [hcr_eq, htr_c]; exact hrc_cur,
    by rw [hcr_eq, htr_c, hss_eq]; exact hia_cur,
    by rw [hcr_eq, htr_c]; exact hna_cur,
    fun rk b' loc' hm => by
      obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
      exact ⟨hb', by rw [hbp']; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
    ?_, ?_, ?_, ?_, by rw [hta_eq]; decide, fun h01 => by rw [hta_eq] at h01; nomatch h01⟩
  · rw [hss_eq, hcr_eq, htr_o, hdp_eq, hbp', ite_eq_left hsub]
    rw [ite_eq_left hsub] at hold_half
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hold_half
    exact ⟨h1, h2, h3, h4, h5, h6, h7, fun rk b' loc' hm => by
      obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := h8 rk b' loc' hm
      exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩⟩
  · intro b' hb'
    rw [hbp']
    refine ⟨?_, fun fp' loc' hm => ?_⟩
    · by_cases he : b' = fm.tryBkt
      · subst he
        have hci_b : (extractFastMeta fl s'.mem).curIns fm.tryBkt = fm.tryIns := by
          rw [congrFun hci_fn fm.tryBkt, Function.update_self]
        have hrl_b : (extractFastMeta fl s'.mem).curRole fm.tryBkt =
            tryRoleOf (fm.curRole fm.tryBkt) := by
          rw [congrFun hrl_fn fm.tryBkt, Function.update_self]
        rw [hci_b, hrl_b, Function.update_self, hbt' fm.tryBkt hb' _ htr_lt]
        exact hv_tm
      · have hci_b : (extractFastMeta fl s'.mem).curIns b' = fm.curIns b' := by
          rw [congrFun hci_fn b', Function.update_of_ne he]
        have hrl_b : (extractFastMeta fl s'.mem).curRole b' = fm.curRole b' := by
          rw [congrFun hrl_fn b', Function.update_of_ne he]
        rw [hci_b, hrl_b, Function.update_of_ne he,
          hbt' b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1]
        exact (hbt_all b' hb').1
    · by_cases he : b' = fm.tryBkt
      · subst he
        rw [Function.update_self] at hm
        obtain ⟨hl_tp, u', hk', hmb_old, hfp_ts⟩ := ht_s fp' loc' hm
        have hl_cnt : loc' < bp.bktCount fm.tryBkt := htp_cnt ▸ hl_tp
        obtain ⟨_, u_old, _, hk_old, hd1, hd2⟩ := (hbt_all fm.tryBkt hb').2 _ loc' hmb_old
        have hu_eq : u_old = u' := Fin.ext (hk_old.symm.trans hk')
        rw [hu_eq] at hd1 hd2
        have hbs_b : (extractFastMeta fl s'.mem).bktSalt fm.tryBkt = fm.trySalt := by
          rw [congrFun hbs_fn fm.tryBkt, Function.update_self]
        exact ⟨hl_cnt, u', (congrArg Fin.val (fpHash_congr_salt hbs_b u')).trans hfp_ts,
          (hkey_eq fm.tryBkt loc' hb' hl_cnt).trans hk',
          fun b₁ l₁ hm₁ => by
            obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
            rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
          fun b₂ l₂ hm₂ => by
            obtain ⟨hb₂, hl₂⟩ := hold_bounds _ b₂ l₂ hm₂
            rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
      · rw [Function.update_of_ne he] at hm
        obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
        have hbs_b : (extractFastMeta fl s'.mem).bktSalt b' = fm.bktSalt b' := by
          rw [congrFun hbs_fn b', Function.update_of_ne he]
        exact ⟨hl', u', (congrArg Fin.val (fpHash_congr_salt hbs_b u')).trans hfp',
          (hkey_eq b' loc' hb' hl').trans hk',
          fun b₁ l₁ hm₁ => by
            obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
            rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
          fun b₂ l₂ hm₂ => by
            obtain ⟨hb₂, hl₂⟩ := hold_bounds _ b₂ l₂ hm₂
            rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
  · intro b' hb' loc' hloc'
    rw [hbp'] at hloc'
    obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
    refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
    rcases ht' with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · right; right
      by_cases he : b' = fm.tryBkt
      · subst he
        have hbs_b : (extractFastMeta fl s'.mem).bktSalt fm.tryBkt = fm.trySalt := by
          rw [congrFun hbs_fn fm.tryBkt, Function.update_self]
        rw [Function.update_self, fpHash_congr_salt hbs_b u']
        exact ht_c loc' (htp_cnt.symm ▸ hloc') u' hk' h3
      · have hbs_b : (extractFastMeta fl s'.mem).bktSalt b' = fm.bktSalt b' := by
          rw [congrFun hbs_fn b', Function.update_of_ne he]
        rw [Function.update_of_ne he, fpHash_congr_salt hbs_b u']
        exact h3
  · intro b' hb' hsc'
    rw [congrFun hsc_eq b'] at hsc' ⊢
    have hne_b : b' ≠ fm.tryBkt := fun he => by subst he; exact hsc' hsc_t
    have hrl_b : (extractFastMeta fl s'.mem).curRole b' = fm.curRole b' := by
      rw [congrFun hrl_fn b', Function.update_of_ne hne_b]
    have hci_b : (extractFastMeta fl s'.mem).curIns b' = fm.curIns b' := by
      rw [congrFun hci_fn b', Function.update_of_ne hne_b]
    rw [hta_eq, congrFun hsi_eq b', hci_b, hrl_b, hbp', Function.update_of_ne hne_b]
    obtain ⟨h1, _, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc'
    have hr_sm := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
    rw [hbt' b' hb' _ hr_sm]
    exact ⟨h1, by simp, h3, h4, sm', hv_sm', heq_sm'⟩

/-- Characterize `drainTryCheckDpProg` when `tryAct = 1` and `tryPos = bktCount tryBkt`. -/
private theorem drainTryCheckDpProg_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hta1 : (extractFastMeta fl s.mem).tryAct = 1)
    (htp_cnt : (extractFastMeta fl s.mem).tryPos =
      (extractBlockPool fl.mp s.mem).bktCount (extractFastMeta fl s.mem).tryBkt) :
    let fm := extractFastMeta fl s.mem
    let b := fm.tryBkt
    memoryCost (drainTryCheckDpProg fl.pBase) s ≤
      220 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * hMaxBTree ∧
    (((Memory.spec 0).clientResult s (drainTryCheckDpProg fl.pBase) = 0 ∧
      ∀ loc_dp (u_dp : Fin fl.U),
        bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) fm.drainPos =
          some (b, loc_dp) →
        fastKeyAt fl seeds.bkt s.mem b loc_dp = u_dp.val →
        ∃ hs_t : fm.trySalt < sMaxWhp fl.c fl.N,
          (Memory.spec 0).clientResult s
            (fastBTreeLookupProg ((fl.pBase, (b, tryRoleOf (fm.curRole b))),
              (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u_dp).val)) = (0, 0)) ∨
     ((Memory.spec 0).clientResult s (drainTryCheckDpProg fl.pBase) = 1 ∧
      ∃ (hs_t : fm.trySalt < sMaxWhp fl.c fl.N) (u v : Fin fl.U),
        u ≠ v ∧ s_abs u ≠ none ∧ s_abs v ≠ none ∧
        epochBucket fl.c fl.U fl.N seeds.bkt u = b ∧
        epochBucket fl.c fl.U fl.N seeds.bkt v = b ∧
        fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u =
          fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ v)) := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  obtain ⟨mapCur, mapOld, mapBTree, _, _, _, _, _, _,
    hold_half, hbt_all, _, _, _, htry_all⟩ := hinv.tiers
  obtain ⟨hsub, hb_t, hs_t, _, _, hti_le, tm, hv_tm, ht_s, _⟩ := htry_all hta1
  set b := fm.tryBkt
  set cnt := bp.bktCount b
  have hcnt_res := fastReadBktCntProg_spec hr₀ hinv.bp_inv.1.core hb_t
  have hm3_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 3)) =
      fm.curBufRole := clientResult_fastReadMetaProg hpt (by decide)
  have hm5_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 5)) =
      fm.drainPos := clientResult_fastReadMetaProg hpt (by decide)
  have hm7_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 7)) =
      b := clientResult_fastReadMetaProg hpt (by decide)
  have hm8_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 8)) =
      fm.trySalt := clientResult_fastReadMetaProg hpt (by decide)
  have cm3 := memoryCost_fastReadMetaProg (fl.pBase, 3) s
  have cm5 := memoryCost_fastReadMetaProg (fl.pBase, 5) s
  have cm7 := memoryCost_fastReadMetaProg (fl.pBase, 7) s
  have cm8 := memoryCost_fastReadMetaProg (fl.pBase, 8) s
  have hh := hold_half; rw [ite_eq_left hsub] at hh
  obtain ⟨hv_old, _, _, hia_old, _, _, _, hold_snd⟩ := hh
  have hold_role : 1 - fm.curBufRole < 2 := by have := hinv.role_lt; omega
  obtain ⟨hcs_res, hcs_c⟩ := fastBufCheckSlotProg_spec hr₀ hold_role hia_old (id := fm.drainPos)
  unfold drainTryCheckDpProg; dsimp only
  rw [prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hm3_r,
    prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hm5_r,
    prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hm7_r,
    prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hm8_r,
    ite_eq_left hinv.role_lt,
    prog_clientResult_bind, Realization.memoryCost_bind',
    clientState_fastBufCheckSlotProg, hcs_res]
  cases hchk : bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem)
      fm.drainPos with
  | none =>
    dsimp only
    rw [ite_eq_right (fun ⟨h01, _⟩ => Nat.zero_ne_one h01),
      prog_clientResult_pure, memoryCost_pure]
    refine ⟨?_, Or.inl ⟨rfl, fun _ _ hsome => by cases hsome⟩⟩
    have h220 : memoryCost (fastReadMetaProg (fl.pBase, 3)) s +
        (memoryCost (fastReadMetaProg (fl.pBase, 5)) s +
          (memoryCost (fastReadMetaProg (fl.pBase, 7)) s +
            (memoryCost (fastReadMetaProg (fl.pBase, 8)) s +
              (memoryCost (fastBufCheckSlotProg ((fl.pBase, 1 - fm.curBufRole),
                fm.drainPos)) s + 0)))) ≤ 220 := by
      linarith only [cm3, cm5, cm7, cm8, hcs_c]
    exact h220.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  | some bl =>
    rcases bl with ⟨b_dp, loc_dp⟩
    dsimp only
    by_cases hbb : b_dp = b
    · subst hbb
      rw [ite_eq_left ⟨rfl, rfl⟩]
      obtain ⟨_, rk_dp, _, _, hmo_dp⟩ := hv_old.checkSlot_some hchk
      obtain ⟨_, _, hloc_dp, u_dp, hrk_dp, hk_dp⟩ := hold_snd rk_dp b loc_dp hmo_dp
      change loc_dp < cnt at hloc_dp
      unfold drainTryCheckDpInnerProg; dsimp only
      rw [prog_clientResult_bind, Realization.memoryCost_bind',
        clientState_fastReadBktCntProg, hcnt_res.1, ite_eq_left hloc_dp]
      obtain ⟨hrd_s, hrd_r, hrd_c⟩ := fastBpReadAtProg_spec hr₀ hinv.bp_inv hb_t hloc_dp
      obtain ⟨u_s, v_s, hu_s, _, hb_dp_u, hq_dp, hs_dp⟩ :=
        hinv.bktSlot_refines hb_t hloc_dp
      have hu_s_eq : u_s = u_dp := Fin.ext (hu_s.trans hk_dp)
      rw [hu_s_eq] at hb_dp_u hq_dp hs_dp
      have hq_lt : (bpPairAt fl.bpL s.mem b loc_dp).1 < 2 ^ quotBitsWhp fl.U fl.N :=
        hq_dp ▸ keyQuotient_bWhp_lt hv.N_le_U u_dp
      obtain ⟨hrec_r, hrec_c⟩ :=
        fastFeistelReconProg_spec hr₀ hq_lt hinv.seed_bkt (bkt := b)
      have hu_rec_dp : (Memory.spec 0).clientResult s
          (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s.mem b loc_dp).1))) =
          u_dp.val := hrec_r.trans hk_dp
      obtain ⟨hfp_r, hfp_c⟩ :=
        fastFpHashProg_spec hr₀ hinv.seed_fp ⟨fm.trySalt, hs_t⟩ u_dp
      dsimp only at hfp_r hfp_c
      set fp_dp := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u_dp).val
      have hfp_lt : fp_dp < 2 ^ fpBitsWhp fl.N :=
        (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u_dp).isLt
      have hcRole_lt : fm.curRole b < 3 := (hinv.bkt_meta_bounds b hb_t).2.1
      have hcRole_r : (Memory.spec 0).clientResult s
          (fastReadBktLaneProg (fl.pBase, (b, 12))) = fm.curRole b := by
        rw [clientResult_fastReadBktLaneProg hpt hb_t (by decide)]
        change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb_t]
      have hti_le_8L : fm.tryIns ≤ 8 * slabScale fl.N ^ 12 := by
        have hsub0 : bp.bktCount b - fm.tryPos = 0 := by
          change bp.bktCount fm.tryBkt - fm.tryPos = 0
          rw [htp_cnt]; exact Nat.sub_self _
        change 4 * fm.tryIns + 5 * (bp.bktCount b - fm.tryPos) ≤ _ at hti_le
        rw [hsub0] at hti_le; linarith
      have htRole_lt : tryRoleOf (fm.curRole b) < 3 := (tryRoleOf_lt_and_ne hcRole_lt).1
      obtain ⟨hlk_r, hlk_c⟩ :=
        fastBTreeLookupProg_spec hr₀ hb_t htRole_lt hti_le_8L hv_tm hfp_lt
      have cl12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s
      have hc_cnt := hcnt_res.2
      rw [prog_clientResult_bind, Realization.memoryCost_bind', hrd_s, hrd_r,
        prog_clientResult_bind, Realization.memoryCost_bind',
        clientState_fastFeistelReconProg, hu_rec_dp,
        prog_clientResult_bind, Realization.memoryCost_bind',
        clientState_fastFpHashProg, hfp_r,
        prog_clientResult_bind, Realization.memoryCost_bind',
        clientState_fastReadBktLaneProg, hcRole_r,
        prog_clientResult_bind, Realization.memoryCost_bind',
        clientState_tryRoleProg, clientResult_tryRoleProg, memoryCost_tryRoleProg,
        prog_clientResult_bind, Realization.memoryCost_bind',
        clientState_fastBTreeLookupProg, hlk_r]
      have hd4 : 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
          2 * (2 * dTabWhp fl.c * (cTabWhp fl.c + 2)) := by ring
      cases htm_dp : tm fp_dp with
      | none =>
        dsimp only
        rw [prog_clientResult_pure, memoryCost_pure]
        refine ⟨by
          linarith only [cm3, cm5, cm7, cm8, hcs_c, hc_cnt, hrd_c, hrec_c, hfp_c, cl12, hlk_c, hd4],
          Or.inl ⟨rfl, fun loc_dp' u_dp' hsome hkey' => ?_⟩⟩
        have hloc_eq : loc_dp = loc_dp' := (Prod.mk.inj (Option.some.inj hsome)).2
        subst hloc_eq
        have hu_eq : u_dp' = u_dp := Fin.ext (hkey'.symm.trans hk_dp)
        subst hu_eq
        exact ⟨hs_t, by rw [hlk_r, htm_dp]⟩
      | some loc_hit =>
        dsimp only
        rw [prog_clientResult_pure, memoryCost_pure]
        obtain ⟨hl_hit, v_hit, hv_key, hmb_hit, hv_fp⟩ := ht_s fp_dp loc_hit htm_dp
        have hl_hit_cnt : loc_hit < cnt := htp_cnt ▸ hl_hit
        obtain ⟨u_sh, v_sh, hu_sh, _, hb_vhit, _, hs_vhit⟩ :=
          hinv.bktSlot_refines hb_t hl_hit_cnt
        have hu_sh_eq : u_sh = v_hit := Fin.ext (hu_sh.trans hv_key)
        rw [hu_sh_eq] at hb_vhit hs_vhit
        obtain ⟨_, u_bt, _, hk_bt, _, hd2_bt⟩ := (hbt_all b hb_t).2 _ loc_hit hmb_hit
        have hu_bt_eq : u_bt = v_hit := Fin.ext (hk_bt.symm.trans hv_key)
        rw [hu_bt_eq] at hd2_bt
        have huv_ne : u_dp ≠ v_hit := by
          intro heq; subst heq
          exact hd2_bt b loc_dp (hrk_dp.symm ▸ hmo_dp) hk_dp
        exact ⟨by
          linarith only [cm3, cm5, cm7, cm8, hcs_c, hc_cnt, hrd_c, hrec_c, hfp_c, cl12, hlk_c, hd4],
          Or.inr ⟨rfl, hs_t, u_dp, v_hit, huv_ne,
            by rw [hs_dp]; simp, by rw [hs_vhit]; simp, hb_dp_u, hb_vhit, Fin.ext hv_fp.symm⟩⟩
    · rw [ite_eq_right (fun ⟨_, h2⟩ => hbb h2), prog_clientResult_pure, memoryCost_pure]
      refine ⟨?_, Or.inl ⟨rfl, fun _ _ hsome =>
        absurd (Prod.mk.inj (Option.some.inj hsome)).1 hbb⟩⟩
      have h220 : memoryCost (fastReadMetaProg (fl.pBase, 3)) s +
          (memoryCost (fastReadMetaProg (fl.pBase, 5)) s +
            (memoryCost (fastReadMetaProg (fl.pBase, 7)) s +
              (memoryCost (fastReadMetaProg (fl.pBase, 8)) s +
                (memoryCost (fastBufCheckSlotProg ((fl.pBase, 1 - fm.curBufRole),
                  fm.drainPos)) s + 0)))) ≤ 220 := by
        linarith only [cm3, cm5, cm7, cm8, hcs_c]
      exact h220.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))

/-- Invariant preservation when advancing `tryPos := tryPos + 1` past a slot `(tryBkt, tryPos)`
not mapped in `mapBTree tryBkt`. -/
private theorem drainTrySkipStep_inv {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hta1 : (extractFastMeta fl s.mem).tryAct = 1)
    (htp_lt : (extractFastMeta fl s.mem).tryPos <
      (extractBlockPool fl.mp s.mem).bktCount (extractFastMeta fl s.mem).tryBkt)
    (hnot_hit : ∀ b' hb', b' = (extractFastMeta fl s.mem).tryBkt →
      ∀ (u : Fin fl.U),
        fastKeyAt fl seeds.bkt s.mem b' (extractFastMeta fl s.mem).tryPos = u.val →
        (Memory.spec 0).clientResult s
          (fastBTreeLookupProg ((fl.pBase, (b', (extractFastMeta fl s.mem).curRole b')),
            (fpHash fl.c fl.U fl.N seeds.fp
              ⟨(extractFastMeta fl s.mem).bktSalt b',
                (hinv.bkt_meta_bounds b' hb').1⟩ u).val)) ≠
          (1, (extractFastMeta fl s.mem).tryPos)) :
    let fm := extractFastMeta fl s.mem
    let s1 := (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 9), fm.tryPos + 1))
    s1.frontier = s.frontier ∧
    FastEpochInvGen slackCur fl slack seeds s1.mem s_abs ∧
    extractBlockPool fl.mp s1.mem = extractBlockPool fl.mp s.mem ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s1.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s1.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s1.mem addr = s.mem addr) ∧
    extractFastMeta fl s1.mem = { fm with tryPos := fm.tryPos + 1 } := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set b := fm.tryBkt
  set tp := fm.tryPos
  set cnt := bp.bktCount b
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, hta_le, htry_all⟩ := hinv.tiers
  obtain ⟨hsub, hb_t, hs_t, htp_le, hsc_t, hti_le, tm, hv_tm, ht_s, ht_c⟩ := htry_all hta1
  have hbs_lt : fm.bktSalt b < sMaxWhp fl.c fl.N := (hinv.bkt_meta_bounds b hb_t).1
  have hcRole_lt : fm.curRole b < 3 := (hinv.bkt_meta_bounds b hb_t).2.1
  have hcIns_le : fm.curIns b ≤ 8 * slabScale fl.N ^ 12 := (hinv.bkt_meta_bounds b hb_t).2.2.1
  obtain ⟨hfr_w, hr_w, hbp_w, hbt_w, htr_w, hoi_w, hof_w, hm2_w, hfm_w⟩ :=
    extractFastMeta_writeMeta (off := 9) (val := tp + 1) hr₀ (Or.inl ⟨by decide, by decide⟩)
  generalize hs1_def :
    (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 9), tp + 1)) = s1
  rw [hs1_def] at hfr_w hr_w hbp_w hbt_w htr_w hoi_w hof_w hm2_w hfm_w
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl] at hfm_w
  have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
      fastKeyAt fl seeds.bkt s1.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
    fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp_w hoi_w hb' hl'
  have hold_bounds : ∀ rk b₂ l₂, mapOld rk = some (b₂, l₂) →
      b₂ < numBucketsWhp fl.N ∧ l₂ < bp.bktCount b₂ := by
    intro rk b₂ l₂ hm₂
    have hh := hold_half; rw [ite_eq_left hsub] at hh
    obtain ⟨_, hb₂, hl₂, _⟩ := hh.2.2.2.2.2.2.2 rk b₂ l₂ hm₂
    exact ⟨hb₂, hl₂⟩
  have hbm_s1 : ∀ b' < numBucketsWhp fl.N,
      let fm2 := extractFastMeta fl s1.mem
      fm2.bktSalt b' < sMaxWhp fl.c fl.N ∧ fm2.curRole b' < 3 ∧
      fm2.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
      (fm2.shadowCode b' = 0 → ¬(fm2.tryAct = 1 ∧ fm2.tryBkt = b') →
        fm2.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' => by
    dsimp only; rw [hfm_w]; exact hinv.bkt_meta_bounds b' hb'
  obtain ⟨hc_N, hc_sb, hc_sf, hc_bp, hc_cap, hc_ref⟩ :=
    FastEpochInvGen.fixed_pool_core hv hinv hbp_w hoi_w hof_w
  refine ⟨hfr_w, ?_, hbp_w, htr_w, hoi_w, hof_w, hfm_w⟩
  refine
    { param_table := hr_w.2.1
      hdr_N := hc_N
      mode_zero := hm2_w.trans hinv.mode_zero
      seed_bkt := hc_sb
      seed_fp := hc_sf
      bp_inv := hc_bp
      bkt_le_capMax := hc_cap
      refines := hc_ref
      role_lt := by rw [hfm_w]; exact hinv.role_lt
      subStep_lt := by rw [hfm_w]; exact hinv.subStep_lt
      bkt_meta_bounds := hbm_s1
      tiers := ?_ }
  dsimp only
  have htr_c := htr_w fm.curBufRole hinv.role_lt
  have htr_o := htr_w (1 - fm.curBufRole) (by have := hinv.role_lt; omega)
  have hcr1 : (extractFastMeta fl s1.mem).curBufRole = fm.curBufRole := by rw [hfm_w]
  have hss1 : (extractFastMeta fl s1.mem).subStep = fm.subStep := by rw [hfm_w]
  have hdp1 : (extractFastMeta fl s1.mem).drainPos = fm.drainPos := by rw [hfm_w]
  have hta1' : (extractFastMeta fl s1.mem).tryAct = fm.tryAct := by rw [hfm_w]
  have htb1 : (extractFastMeta fl s1.mem).tryBkt = fm.tryBkt := by rw [hfm_w]
  have hts1 : (extractFastMeta fl s1.mem).trySalt = fm.trySalt := by rw [hfm_w]
  have htp1 : (extractFastMeta fl s1.mem).tryPos = tp + 1 := by rw [hfm_w]
  have hti1 : (extractFastMeta fl s1.mem).tryIns = fm.tryIns := by rw [hfm_w]
  have hbs1 : (extractFastMeta fl s1.mem).bktSalt = fm.bktSalt := by rw [hfm_w]
  have hrl1 : (extractFastMeta fl s1.mem).curRole = fm.curRole := by rw [hfm_w]
  have hci1 : (extractFastMeta fl s1.mem).curIns = fm.curIns := by rw [hfm_w]
  have hsi1 : (extractFastMeta fl s1.mem).shadowIns = fm.shadowIns := by rw [hfm_w]
  have hsc1 : (extractFastMeta fl s1.mem).shadowCode = fm.shadowCode := by rw [hfm_w]
  refine ⟨mapCur, mapOld, mapBTree,
    by rw [hcr1, htr_c]; exact hv_cur,
    by rw [hcr1, htr_c]; exact hrb_cur,
    by rw [hcr1, htr_c]; exact hrc_cur,
    by rw [hcr1, htr_c, hss1]; exact hia_cur,
    by rw [hcr1, htr_c]; exact hna_cur,
    fun rk b' loc' hm => by
      obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
      exact ⟨hb', by rw [hbp_w]; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
    ?_, ?_, ?_, ?_, by rw [hta1']; exact hta_le, ?_⟩
  · rw [hss1, hcr1, htr_o, hdp1, hbp_w, ite_eq_left hsub]
    rw [ite_eq_left hsub] at hold_half
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hold_half
    exact ⟨h1, h2, h3, h4, h5, h6, h7, fun rk b' loc' hm => by
      obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := h8 rk b' loc' hm
      exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩⟩
  · intro b' hb'
    rw [hbp_w]
    refine ⟨?_, fun fp' loc' hm => ?_⟩
    · rw [congrFun hci1 b', congrFun hrl1 b', hbt_w b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1]
      exact (hbt_all b' hb').1
    · obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
      exact ⟨hl', u',
        (congrArg Fin.val (fpHash_congr_salt (congrFun hbs1 b') u')).trans hfp',
        (hkey_eq b' loc' hb' hl').trans hk',
        fun b₁ l₁ hm₁ => by
          obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
          rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
        fun b₂ l₂ hm₂ => by
          obtain ⟨hb₂, hl₂⟩ := hold_bounds _ b₂ l₂ hm₂
          rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
  · intro b' hb' loc' hloc'
    rw [hbp_w] at hloc'
    obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
    refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
    rw [fpHash_congr_salt (congrFun hbs1 b') u']; exact ht'
  · intro b' hb' hsc'
    rw [congrFun hsc1 b'] at hsc' ⊢
    rw [hta1', htb1, congrFun hsi1 b', congrFun hci1 b', congrFun hrl1 b', hbp_w]
    obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc'
    have hr_sm := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
    rw [hbt_w b' hb' _ hr_sm]
    exact ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩
  · intro _
    have hbnd_ti : 4 * fm.tryIns + 5 * (cnt - (tp + 1)) ≤ 20 * slabScale fl.N ^ 12 := by
      have hsub_tp : cnt - tp = cnt - (tp + 1) + 1 := by omega
      change 4 * fm.tryIns + 5 * (cnt - tp) ≤ 20 * slabScale fl.N ^ 12 at hti_le
      rw [hsub_tp] at hti_le; linarith
    have hbs_tb : (extractFastMeta fl s1.mem).bktSalt
        (extractFastMeta fl s1.mem).tryBkt = fm.bktSalt b := by rw [htb1, congrFun hbs1 b]
    rw [hss1, htp1, hti1, hbp_w]
    refine ⟨hsub, htb1.symm ▸ hb_t, hts1.symm ▸ hs_t,
      by rw [htb1]; exact Nat.succ_le_of_lt htp_lt,
      by rw [htb1, congrFun hsc1 b]; exact hsc_t,
      by rw [htb1]; exact hbnd_ti, tm, ?_, ?_, ?_⟩
    · rw [htb1, congrFun hrl1 b]
      have hr_tr := (tryRoleOf_lt_and_ne hcRole_lt).1
      rw [hbt_w b hb_t _ hr_tr]; exact hv_tm
    · intro fp' loc' htm'
      obtain ⟨hl', u', hk', hmb', hfp'⟩ := ht_s fp' loc' htm'
      exact ⟨Nat.lt_succ_of_lt hl', u',
        by rw [htb1]; exact (hkey_eq b loc' hb_t (hl'.trans htp_lt)).trans hk',
        by rw [mapBTree_fpHash_congr mapBTree (h₂ := hbs_lt) htb1 hbs_tb u']; exact hmb',
        (congrArg Fin.val (fpHash_congr_salt hts1 u')).trans hfp'⟩
    · intro loc' hl' u' hk' hmb'
      rw [htb1] at hk'
      rw [mapBTree_fpHash_congr mapBTree (h₂ := hbs_lt) htb1 hbs_tb u'] at hmb'
      rw [fpHash_congr_salt hts1 u']
      · by_cases hle : loc' = tp
        · subst hle
          have hk0 : fastKeyAt fl seeds.bkt s.mem b tp = u'.val :=
            (hkey_eq b tp hb_t htp_lt).symm.trans hk'
          have hfp_lt' : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hbs_lt⟩ u').val <
              2 ^ fpBitsWhp fl.N :=
            (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hbs_lt⟩ u').isLt
          obtain ⟨hlk', _⟩ :=
            fastBTreeLookupProg_spec hr₀ hb_t hcRole_lt hcIns_le (hbt_all b hb_t).1 hfp_lt'
          exact absurd (by rw [hlk', hmb']) (hnot_hit b hb_t rfl u' hk0)
        · have hl_lt_tp : loc' < tp := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hl') hle
          have hk0 : fastKeyAt fl seeds.bkt s.mem b loc' = u'.val :=
            (hkey_eq b loc' hb_t (hl_lt_tp.trans htp_lt)).symm.trans hk'
          exact ht_c loc' hl_lt_tp u' hk0 hmb'

/-- Unified specification of `drainTryStepProg`: preserves `FastEpochInvGen` unconditionally on
100% of seeds, leaves `BlockPool` and both `BufTrie`s untouched, and when `tryAct = 1` satisfies an
exact 3-way trichotomy (step `tryPos + 1`, advance `trySalt` with a genuine distinct-key collision
witness, or commit `trySalt` with a verified non-collision at `drainPos`). -/
theorem drainTryStepProg_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs) :
    let s' := (Memory.spec 0).clientState s (drainTryStepProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    let fm' := extractFastMeta fl s'.mem
    let bp := extractBlockPool fl.mp s.mem
    s'.frontier = s.frontier ∧
    memoryCost (drainTryStepProg fl.pBase) s ≤
      600 + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 84 * hMaxBTree ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = bp ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    fm'.drainPos = fm.drainPos ∧
    fm'.shadowCode = fm.shadowCode ∧
    fm'.shadowIns = fm.shadowIns ∧
    (fm.tryAct = 0 → s' = s) ∧
    (fm.tryAct = 1 →
      -- Case A: `tryPos < cnt` stepped to `tryPos + 1`
      (fm.tryPos < bp.bktCount fm.tryBkt ∧
        fm'.tryAct = 1 ∧ fm'.tryBkt = fm.tryBkt ∧ fm'.trySalt = fm.trySalt ∧
        fm'.tryPos = fm.tryPos + 1 ∧ fm'.tryIns ≤ fm.tryIns + 1 ∧
        fm'.bktSalt = fm.bktSalt) ∨
      -- Case B: distinct-key collision under `fm.trySalt`, advancing `trySalt`
      (fm'.tryAct = 1 ∧ fm'.tryBkt = fm.tryBkt ∧ fm'.tryPos = 0 ∧ fm'.tryIns = 0 ∧
        fm'.trySalt = (if fm.trySalt + 1 < sMaxWhp fl.c fl.N then fm.trySalt + 1 else 0) ∧
        fm'.bktSalt = fm.bktSalt ∧
        ∃ (hs : fm.trySalt < sMaxWhp fl.c fl.N) (u v : Fin fl.U),
          u ≠ v ∧ s_abs u ≠ none ∧ s_abs v ≠ none ∧
          epochBucket fl.c fl.U fl.N seeds.bkt u = fm.tryBkt ∧
          epochBucket fl.c fl.U fl.N seeds.bkt v = fm.tryBkt ∧
          fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ u =
            fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs⟩ v) ∨
      -- Case C: `tryPos = cnt`, `drainPos` does not collide with `tryMap`, committed `trySalt`
      (fm.tryPos = bp.bktCount fm.tryBkt ∧
        fm'.tryAct = 0 ∧
        (∀ loc_dp (u_dp : Fin fl.U),
          bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) fm.drainPos =
            some (fm.tryBkt, loc_dp) →
          fastKeyAt fl seeds.bkt s.mem fm.tryBkt loc_dp = u_dp.val →
          ∃ hs_t : fm.trySalt < sMaxWhp fl.c fl.N,
            (Memory.spec 0).clientResult s
              (fastBTreeLookupProg ((fl.pBase, (fm.tryBkt, tryRoleOf (fm.curRole fm.tryBkt))),
                (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u_dp).val)) = (0, 0)) ∧
        (∀ b' < numBucketsWhp fl.N, ∀ r < 3,
          extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
        fm'.bktSalt = Function.update fm.bktSalt fm.tryBkt fm.trySalt ∧
        fm'.curRole =
          Function.update fm.curRole fm.tryBkt (tryRoleOf (fm.curRole fm.tryBkt)) ∧
        fm'.curIns = Function.update fm.curIns fm.tryBkt fm.tryIns)) := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  have hpt := hinv.param_table
  obtain ⟨h64_L12, hcap_N, hsMax_N, _⟩ := hv.bounds_le_N
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  have hm6_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 6)) = fm.tryAct :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hm7_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 7)) = fm.tryBkt :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hm0 : s.mem (fl.pBase + 0) = fl.N := hpt 0 (by decide)
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, hta_le, htry_all⟩ := hinv.tiers
  by_cases hta1 : fm.tryAct = 1
  · obtain ⟨hsub, hb_t, hs_t, htp_le, hsc_t, hti_le, tm, hv_tm, ht_s, ht_c⟩ := htry_all hta1
    set b := fm.tryBkt
    set cnt := bp.bktCount b
    set tp := fm.tryPos
    have hcnt_le : cnt ≤ capMaxWhp fl.N := hinv.bkt_le_capMax b hb_t
    have hcnt_le_N : cnt ≤ fl.N := hcnt_le.trans hcap_N
    have hcnt_res := fastReadBktCntProg_spec hr₀ hinv.bp_inv.1.core hb_t
    have hm9_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 9)) = tp :=
      clientResult_fastReadMetaProg hpt (by decide)
    have hguard : fm.tryAct = 1 ∧ b < numBucketsWhp fl.N := ⟨hta1, hb_t⟩
    by_cases htp_lt : tp < cnt
    · -- Scan branch (`tp < cnt`): `drainTryScanSlotProg ((fl.pBase, b), tp)`
      have htp_lt_N : tp < fl.N := lt_of_lt_of_le htp_lt hcnt_le_N
      have htp_val : tp < 2 ^ valLaneBitsWhp fl.N := by
        rw [two_pow_valLaneBitsWhp]; unfold capMaxWhp at hcnt_le; omega
      obtain ⟨hread_st, hread_res, hread_c⟩ := fastBpReadAtProg_spec hr₀ hinv.bp_inv hb_t htp_lt
      obtain ⟨u, v_u, hu_val, _, hb_u, hq_u, hs_u⟩ := hinv.bktSlot_refines hb_t htp_lt
      have hq_lt : (bpPairAt fl.bpL s.mem b tp).1 < 2 ^ quotBitsWhp fl.U fl.N :=
        hq_u ▸ keyQuotient_bWhp_lt hv.N_le_U u
      obtain ⟨hrec_res, hrec_c⟩ := fastFeistelReconProg_spec hr₀ hq_lt hinv.seed_bkt (bkt := b)
      have hu_rec : (Memory.spec 0).clientResult s
          (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s.mem b tp).1))) = u.val :=
        hrec_res.trans hu_val.symm
      have hbs_lt : fm.bktSalt b < sMaxWhp fl.c fl.N := (hinv.bkt_meta_bounds b hb_t).1
      have hcRole_lt : fm.curRole b < 3 := (hinv.bkt_meta_bounds b hb_t).2.1
      have hcIns_le : fm.curIns b ≤ 8 * slabScale fl.N ^ 12 :=
        (hinv.bkt_meta_bounds b hb_t).2.2.1
      have hbs_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 5))) =
          fm.bktSalt b := by
        rw [clientResult_fastReadBktLaneProg hpt hb_t (by decide)]
        change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb_t]
      have hcRole_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12))) =
          fm.curRole b := by
        rw [clientResult_fastReadBktLaneProg hpt hb_t (by decide)]
        change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb_t]
      obtain ⟨hfp_c_res, hfp_c_c⟩ :=
        fastFpHashProg_spec hr₀ hinv.seed_fp ⟨fm.bktSalt b, hbs_lt⟩ u
      dsimp only at hfp_c_res hfp_c_c
      set fp_cur := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hbs_lt⟩ u).val
      have hfp_c_lt : fp_cur < 2 ^ fpBitsWhp fl.N :=
        (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hbs_lt⟩ u).isLt
      obtain ⟨hlk_c_res, hlk_c_c⟩ :=
        fastBTreeLookupProg_spec hr₀ hb_t hcRole_lt hcIns_le (hbt_all b hb_t).1 hfp_c_lt
      have houter :
          (Memory.spec 0).clientState s (drainTryStepProg fl.pBase) =
            (Memory.spec 0).clientState s
              (if ((Memory.spec 0).clientResult s
                    (fastBTreeLookupProg ((fl.pBase, (b, fm.curRole b)), fp_cur))).1 = 1 ∧
                  ((Memory.spec 0).clientResult s
                    (fastBTreeLookupProg ((fl.pBase, (b, fm.curRole b)), fp_cur))).2 = tp then
                drainTryInsertOrAdvProg (((fl.pBase, b), (tp, fm.curRole b)), u.val)
               else do
                 let nCap ← Memory.read (fl.pBase + 0)
                 if tp < nCap then fastWriteMetaProg ((fl.pBase, 9), tp + 1) else pure ()) ∧
          memoryCost (drainTryStepProg fl.pBase) s ≤
            180 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * hMaxBTree +
              memoryCost
                (if ((Memory.spec 0).clientResult s
                      (fastBTreeLookupProg ((fl.pBase, (b, fm.curRole b)), fp_cur))).1 = 1 ∧
                    ((Memory.spec 0).clientResult s
                      (fastBTreeLookupProg ((fl.pBase, (b, fm.curRole b)), fp_cur))).2 = tp then
                  drainTryInsertOrAdvProg (((fl.pBase, b), (tp, fm.curRole b)), u.val)
                 else do
                   let nCap ← Memory.read (fl.pBase + 0)
                   if tp < nCap then fastWriteMetaProg ((fl.pBase, 9), tp + 1) else pure ()) s := by
        unfold drainTryStepProg drainTryScanSlotProg; dsimp only
        have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
        have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
            numBucketsWhp fl.N := hm11
        have cm6 := memoryCost_fastReadMetaProg (fl.pBase, 6) s
        have cm7 := memoryCost_fastReadMetaProg (fl.pBase, 7) s
        have cm9 := memoryCost_fastReadMetaProg (fl.pBase, 9) s
        have cl5 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 5)) s
        have cl12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s
        have hcnt_r : (Memory.spec 0).clientResult s (fastReadBktCntProg (fl.pBase, b)) = cnt :=
          hcnt_res.1
        have hc_cnt := hcnt_res.2
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hm6_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hm7_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          hr11_st, hr11_r, prog_memoryCost_read,
          ite_eq_left hguard,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadBktCntProg, hcnt_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hm9_r,
          ite_eq_left htp_lt,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          hread_st, hread_res]
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastFeistelReconProg, hu_rec,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadBktLaneProg, hbs_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadBktLaneProg, hcRole_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastFpHashProg, hfp_c_res,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastBTreeLookupProg]
        rcases (Memory.spec 0).clientResult s
          (fastBTreeLookupProg ((fl.pBase, (b, fm.curRole b)), fp_cur)) with ⟨h1, l1⟩
        have hd4 : 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
            2 * (2 * dTabWhp fl.c * (cTabWhp fl.c + 2)) := by ring
        exact ⟨rfl, by
          linarith only [cm6, cm7, cm9, hc_cnt, hread_c, hrec_c, cl5, cl12, hfp_c_c, hlk_c_c,
            hd4]⟩
      by_cases hmb_tp : mapBTree b fp_cur = some tp
      · -- `(b, tp)` IS in `mapBTree b`
        have hlk_c_pair : (Memory.spec 0).clientResult s
            (fastBTreeLookupProg ((fl.pBase, (b, fm.curRole b)), fp_cur)) = (1, tp) := by
          rw [hlk_c_res, hmb_tp]
        obtain ⟨hst_out, hc_out⟩ := houter
        rw [hlk_c_pair, ite_eq_left ⟨rfl, rfl⟩] at hst_out hc_out
        have hm8_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 8)) =
            fm.trySalt := clientResult_fastReadMetaProg hpt (by decide)
        obtain ⟨hfp_t_res, hfp_t_c⟩ :=
          fastFpHashProg_spec hr₀ hinv.seed_fp ⟨fm.trySalt, hs_t⟩ u
        dsimp only at hfp_t_res hfp_t_c
        set fp_try := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u).val
        have hfp_t_lt : fp_try < 2 ^ fpBitsWhp fl.N :=
          (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u).isLt
        set tRole := tryRoleOf (fm.curRole b)
        obtain ⟨htRole_lt, htRole_ne_c, htRole_ne_s⟩ := tryRoleOf_lt_and_ne hcRole_lt
        have hti_le_5L : fm.tryIns < 5 * slabScale fl.N ^ 12 := by
          have : 1 ≤ cnt - tp := by omega
          linarith
        have hti_le_8L : fm.tryIns ≤ 8 * slabScale fl.N ^ 12 := by linarith
        have hti_lt_N : fm.tryIns < fl.N := by linarith
        obtain ⟨hlk_t_res, hlk_t_c⟩ :=
          fastBTreeLookupProg_spec hr₀ hb_t htRole_lt hti_le_8L hv_tm hfp_t_lt
        cases htm_q : tm fp_try with
        | some loc0 =>
          -- Collision in `tryMap` (`loc0 < tp`)!
          have hlk_t_pair : (Memory.spec 0).clientResult s
              (fastBTreeLookupProg ((fl.pBase, (b, tRole)), fp_try)) = (1, loc0) := by
            rw [hlk_t_res, htm_q]
          have hins_st :
              (Memory.spec 0).clientState s
                (drainTryInsertOrAdvProg (((fl.pBase, b), (tp, fm.curRole b)), u.val)) =
                (Memory.spec 0).clientState s (advanceTrySaltProg fl.pBase) ∧
              memoryCost (drainTryInsertOrAdvProg (((fl.pBase, b), (tp, fm.curRole b)), u.val)) s ≤
                120 + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * hMaxBTree +
                  memoryCost (advanceTrySaltProg fl.pBase) s := by
            unfold drainTryInsertOrAdvProg; dsimp only
            have cm8 := memoryCost_fastReadMetaProg (fl.pBase, 8) s
            have htR_eq : tryRoleOf (fm.curRole b) = tRole := rfl
            have hlk_t_c' : memoryCost (fastBTreeLookupProg ((fl.pBase, (b, tRole)), fp_try)) s ≤
                6 * hMaxBTree + 35 := hlk_t_c
            rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
              clientState_fastReadMetaProg, hm8_r,
              StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
              clientState_fastFpHashProg, hfp_t_res,
              StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
              clientState_tryRoleProg, clientResult_tryRoleProg, htR_eq, memoryCost_tryRoleProg,
              StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
              clientState_fastBTreeLookupProg, hlk_t_pair, ite_eq_left rfl]
            exact ⟨rfl, by linarith only [cm8, hfp_t_c, hlk_t_c']⟩
          obtain ⟨hfr_a, hc_a, hinv_a, hbp_a, htr_a, hoi_a, hof_a, hfm_a⟩ :=
            advanceTrySaltProg_inv hv hinv hta1
          -- Build distinct-key collision witness `(u, v0)`
          obtain ⟨hloc0_lt, v0, hv0_key, hmb_v0, hv0_fp⟩ := ht_s fp_try loc0 htm_q
          obtain ⟨u_s0, v_s0, hu_s0, _, hb_v0, _, hs_v0⟩ :=
            hinv.bktSlot_refines hb_t (hloc0_lt.trans_le htp_le)
          have hu_s0_eq : u_s0 = v0 := Fin.ext (hu_s0.trans hv0_key)
          rw [hu_s0_eq] at hb_v0 hs_v0
          have huv_ne : u ≠ v0 := by
            intro heq
            subst heq
            exact absurd (Option.some.inj (hmb_v0.symm.trans hmb_tp)) (ne_of_lt hloc0_lt)
          rw [hst_out, hins_st.1]
          have hcost_tot : memoryCost (drainTryStepProg fl.pBase) s ≤
              600 + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 84 * hMaxBTree := by
            have h1 := hins_st.2
            have hd6 : 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
                4 * dTabWhp fl.c * (cTabWhp fl.c + 2) +
                  2 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by ring
            have hm0' : 0 ≤ hMaxBTree := Nat.zero_le _
            linarith only [hc_out, h1, hc_a, hd6, hm0']
          refine ⟨hfr_a, hcost_tot, hinv_a, hbp_a, htr_a, hoi_a, hof_a,
            by rw [hfm_a], by rw [hfm_a], by rw [hfm_a], by rw [hfm_a], by rw [hfm_a],
            fun h0 => absurd (h0.symm.trans hta1) Nat.zero_ne_one, fun _ => Or.inr (Or.inl ?_)⟩
          refine ⟨by rw [hfm_a]; exact hta1, by rw [hfm_a], by rw [hfm_a], by rw [hfm_a],
            by rw [hfm_a], by rw [hfm_a], hs_t, u, v0, huv_ne,
            by rw [hs_u]; simp, by rw [hs_v0]; simp, hb_u, hb_v0,
            Fin.ext hv0_fp.symm⟩
        | none =>
          -- No collision in `tryMap`: insert `(fp_try, tp)`, `tryIns + 1`, `tryPos + 1`!
          have hlk_t_pair : (Memory.spec 0).clientResult s
              (fastBTreeLookupProg ((fl.pBase, (b, tRole)), fp_try)) = (0, 0) := by
            rw [hlk_t_res, htm_q]
          have hm17_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 17)) =
              fm.tryIns := clientResult_fastReadMetaProg hpt (by decide)
          obtain ⟨hfr_i, hr_i, hc_i, hv_tm1, hbt_oi, hbp_i, hfm_i, hm2_i, _, htr_i, hoi_i,
            hof_i⟩ :=
            fastBTreeInsertProg_spec (role := tRole) hr₀ hb_t htRole_lt hti_le_8L hv_tm
              hfp_t_lt htp_val
          generalize hs1_def : (Memory.spec 0).clientState s
            (fastBTreeInsertProg ((fl.pBase, (b, tRole)), (fp_try, tp))) = s1
          rw [hs1_def] at hfr_i hr_i hv_tm1 hbt_oi hbp_i hfm_i hm2_i htr_i hoi_i hof_i
          obtain ⟨hfr_w1, hr_w1, hbp_w1, hbt_w1, htr_w1, hoi_w1, hof_w1, hm2_w1, hfm_w1⟩ :=
            extractFastMeta_writeMeta (off := 17) (val := fm.tryIns + 1) hr_i (Or.inr rfl)
          generalize hs2_def : (Memory.spec 0).clientState s1
            (fastWriteMetaProg ((fl.pBase, 17), fm.tryIns + 1)) = s2
          rw [hs2_def] at hfr_w1 hr_w1 hbp_w1 hbt_w1 htr_w1 hoi_w1 hof_w1 hm2_w1 hfm_w1
          obtain ⟨hfr_w2, hr_w2, hbp_w2, hbt_w2, htr_w2, hoi_w2, hof_w2, hm2_w2, hfm_w2⟩ :=
            extractFastMeta_writeMeta (off := 9) (val := tp + 1) hr_w1
              (Or.inl ⟨by decide, by decide⟩)
          generalize hs3_def : (Memory.spec 0).clientState s2
            (fastWriteMetaProg ((fl.pBase, 9), tp + 1)) = s3
          rw [hs3_def] at hfr_w2 hr_w2 hbp_w2 hbt_w2 htr_w2 hoi_w2 hof_w2 hm2_w2 hfm_w2
          have hins_st :
              (Memory.spec 0).clientState s
                (drainTryInsertOrAdvProg (((fl.pBase, b), (tp, fm.curRole b)), u.val)) = s3 ∧
              memoryCost (drainTryInsertOrAdvProg (((fl.pBase, b), (tp, fm.curRole b)), u.val)) s ≤
                300 + 2 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree := by
            unfold drainTryInsertOrAdvProg; dsimp only
            have cm8 := memoryCost_fastReadMetaProg (fl.pBase, 8) s
            have cm17 := memoryCost_fastReadMetaProg (fl.pBase, 17) s
            have cw17 := memoryCost_fastWriteMetaProg ((fl.pBase, 17), fm.tryIns + 1) s1
            have cw9 := memoryCost_fastWriteMetaProg ((fl.pBase, 9), tp + 1) s2
            have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
            have hr0_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N := hm0
            have htR_eq : tryRoleOf (fm.curRole b) = tRole := rfl
            have hlk_t_c' : memoryCost (fastBTreeLookupProg ((fl.pBase, (b, tRole)), fp_try)) s ≤
                6 * hMaxBTree + 35 := hlk_t_c
            rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
              clientState_fastReadMetaProg, hm8_r,
              StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
              clientState_fastFpHashProg, hfp_t_res,
              StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
              clientState_tryRoleProg, clientResult_tryRoleProg, htR_eq, memoryCost_tryRoleProg,
              StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
              clientState_fastBTreeLookupProg, hlk_t_pair, ite_eq_right Nat.zero_ne_one,
              StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
              clientState_fastReadMetaProg, hm17_r,
              StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
              hr0_st, hr0_r, prog_memoryCost_read,
              ite_eq_left ⟨hti_lt_N, htp_lt_N⟩,
              StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def,
              StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs2_def, hs3_def]
            exact ⟨rfl, by linarith only [cm8, hfp_t_c, hlk_t_c', hc_i, cm17, cw17, cw9]⟩
          rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
            ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
            ite_eq_right (by decide)] at hfm_w1
          rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
            ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
            ite_eq_left rfl] at hfm_w2
          have hfm_s3 : extractFastMeta fl s3.mem =
              { fm with tryPos := tp + 1, tryIns := fm.tryIns + 1 } := by
            rw [hfm_w2, hfm_w1, hfm_i]
          have hbp_tot : extractBlockPool fl.mp s3.mem = bp :=
            hbp_w2.trans (hbp_w1.trans hbp_i)
          have htr_tot : ∀ r < 2,
              extractBufTrie (fl.trieL r) s3.mem = extractBufTrie (fl.trieL r) s.mem :=
            fun r hr_lt => (htr_w2 r hr_lt).trans ((htr_w1 r hr_lt).trans (htr_i r hr_lt))
          have hoi_tot : ∀ a, fl.io.OwnsAddr a → s3.mem a = s.mem a :=
            fun a ha => (hoi_w2 a ha).trans ((hoi_w1 a ha).trans (hoi_i a ha))
          have hof_tot : ∀ a, ¬fl.OwnsFastAddr a → s3.mem a = s.mem a :=
            fun a ha => (hof_w2 a ha).trans ((hof_w1 a ha).trans (hof_i a ha))
          have hm2_tot : s3.mem (fl.metaBase + 2) = 0 :=
            hm2_w2.trans (hm2_w1.trans (hm2_i.trans hinv.mode_zero))
          have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
              fastKeyAt fl seeds.bkt s3.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
            fun b' loc' hb' hl' =>
              fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp_tot hoi_tot hb' hl'
          have hold_bounds : ∀ rk b₂ l₂, mapOld rk = some (b₂, l₂) →
              b₂ < numBucketsWhp fl.N ∧ l₂ < bp.bktCount b₂ := by
            intro rk b₂ l₂ hm₂
            have hh := hold_half; rw [ite_eq_left hsub] at hh
            obtain ⟨_, hb₂, hl₂, _⟩ := hh.2.2.2.2.2.2.2 rk b₂ l₂ hm₂
            exact ⟨hb₂, hl₂⟩
          have hbm_s3 : ∀ b' < numBucketsWhp fl.N,
              let fm2 := extractFastMeta fl s3.mem
              fm2.bktSalt b' < sMaxWhp fl.c fl.N ∧
              fm2.curRole b' < 3 ∧
              fm2.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
              (fm2.shadowCode b' = 0 → ¬(fm2.tryAct = 1 ∧ fm2.tryBkt = b') →
                fm2.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' => by
            dsimp only; rw [hfm_s3]; exact hinv.bkt_meta_bounds b' hb'
          have hcost_tot : memoryCost (drainTryStepProg fl.pBase) s ≤
              600 + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 84 * hMaxBTree := by
            have h1 := hc_out; have h2 := hins_st.2
            have hd6 : 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
                4 * dTabWhp fl.c * (cTabWhp fl.c + 2) +
                  2 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by ring
            linarith only [h1, h2, hd6]
          clear hc_out hins_st hlk_t_c hfp_t_c hlk_c_c hfp_c_c hrec_c hread_c hc_i
          have hinv_s3 : FastEpochInvGen slackCur fl slack seeds s3.mem s_abs := by
            obtain ⟨hc_N, hc_sb, hc_sf, hc_bp, hc_cap, hc_ref⟩ :=
              FastEpochInvGen.fixed_pool_core hv hinv hbp_tot hoi_tot hof_tot
            refine
              { param_table := hr_w2.2.1
                hdr_N := hc_N
                mode_zero := hm2_tot
                seed_bkt := hc_sb
                seed_fp := hc_sf
                bp_inv := hc_bp
                bkt_le_capMax := hc_cap
                refines := hc_ref
                role_lt := by rw [hfm_s3]; exact hinv.role_lt
                subStep_lt := by rw [hfm_s3]; exact hinv.subStep_lt
                bkt_meta_bounds := hbm_s3
                tiers := ?_ }
            dsimp only
            have htr_c := htr_tot fm.curBufRole hinv.role_lt
            have htr_o := htr_tot (1 - fm.curBufRole) (by have := hinv.role_lt; omega)
            have hcr3 : (extractFastMeta fl s3.mem).curBufRole = fm.curBufRole := by rw [hfm_s3]
            have hss3 : (extractFastMeta fl s3.mem).subStep = fm.subStep := by rw [hfm_s3]
            have hdp3 : (extractFastMeta fl s3.mem).drainPos = fm.drainPos := by rw [hfm_s3]
            have hta3 : (extractFastMeta fl s3.mem).tryAct = fm.tryAct := by rw [hfm_s3]
            have htb3 : (extractFastMeta fl s3.mem).tryBkt = fm.tryBkt := by rw [hfm_s3]
            have hts3 : (extractFastMeta fl s3.mem).trySalt = fm.trySalt := by rw [hfm_s3]
            have htp3 : (extractFastMeta fl s3.mem).tryPos = tp + 1 := by rw [hfm_s3]
            have hti3 : (extractFastMeta fl s3.mem).tryIns = fm.tryIns + 1 := by rw [hfm_s3]
            have hbs3 : (extractFastMeta fl s3.mem).bktSalt = fm.bktSalt := by rw [hfm_s3]
            have hrl3 : (extractFastMeta fl s3.mem).curRole = fm.curRole := by rw [hfm_s3]
            have hci3 : (extractFastMeta fl s3.mem).curIns = fm.curIns := by rw [hfm_s3]
            have hsi3 : (extractFastMeta fl s3.mem).shadowIns = fm.shadowIns := by rw [hfm_s3]
            have hsc3 : (extractFastMeta fl s3.mem).shadowCode = fm.shadowCode := by rw [hfm_s3]
            refine ⟨mapCur, mapOld, mapBTree,
              by rw [hcr3, htr_c]; exact hv_cur,
              by rw [hcr3, htr_c]; exact hrb_cur,
              by rw [hcr3, htr_c]; exact hrc_cur,
              by rw [hcr3, htr_c, hss3]; exact hia_cur,
              by rw [hcr3, htr_c]; exact hna_cur,
              fun rk b' loc' hm => by
                obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
                exact ⟨hb', by rw [hbp_tot]; exact hl', u', hrk',
                  (hkey_eq b' loc' hb' hl').trans hk'⟩,
              ?_, ?_, ?_, ?_, by rw [hta3]; exact hta_le, ?_⟩
            · rw [hss3, hcr3, htr_o, hdp3, hbp_tot, ite_eq_left hsub]
              rw [ite_eq_left hsub] at hold_half
              obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hold_half
              exact ⟨h1, h2, h3, h4, h5, h6, h7, fun rk b' loc' hm => by
                obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := h8 rk b' loc' hm
                exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩⟩
            · intro b' hb'
              rw [hbp_tot]
              refine ⟨?_, fun fp' loc' hm => ?_⟩
              · rw [congrFun hci3 b', congrFun hrl3 b']
                have hr_b' := (hinv.bkt_meta_bounds b' hb').2.1
                have hdisj : b' ≠ b ∨ fm.curRole b' ≠ tRole := by
                  by_cases he : b' = b
                  · subst he; exact Or.inr htRole_ne_c.symm
                  · exact Or.inl he
                rw [hbt_w2 b' hb' _ hr_b', hbt_w1 b' hb' _ hr_b',
                  hbt_oi b' hb' _ hr_b' hdisj]
                exact (hbt_all b' hb').1
              · obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
                exact ⟨hl', u',
                  (congrArg Fin.val (fpHash_congr_salt (congrFun hbs3 b') u')).trans hfp',
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
              rw [fpHash_congr_salt (congrFun hbs3 b') u']; exact ht'
            · intro b' hb' hsc'
              rw [congrFun hsc3 b'] at hsc' ⊢
              have hne_b : b' ≠ b := fun he => by subst he; exact hsc' hsc_t
              rw [hta3, htb3, congrFun hsi3 b', congrFun hci3 b', congrFun hrl3 b', hbp_tot]
              obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc'
              have hr_sm := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
              rw [hbt_w2 b' hb' _ hr_sm, hbt_w1 b' hb' _ hr_sm,
                hbt_oi b' hb' _ hr_sm (Or.inl hne_b)]
              exact ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩
            · intro _
              have hbnd_ti : 4 * (fm.tryIns + 1) + 5 * (cnt - (tp + 1)) ≤
                  20 * slabScale fl.N ^ 12 := by
                have hsub_tp : cnt - tp = cnt - (tp + 1) + 1 := by omega
                change 4 * fm.tryIns + 5 * (cnt - tp) ≤ 20 * slabScale fl.N ^ 12 at hti_le
                rw [hsub_tp] at hti_le; linarith
              have hbs_tb : (extractFastMeta fl s3.mem).bktSalt
                  (extractFastMeta fl s3.mem).tryBkt = fm.bktSalt b := by
                rw [htb3, congrFun hbs3 b]
              rw [hss3, htp3, hti3, hbp_tot]
              refine ⟨hsub, htb3.symm ▸ hb_t, hts3.symm ▸ hs_t,
                by rw [htb3]; exact Nat.succ_le_of_lt htp_lt,
                by rw [htb3, congrFun hsc3 b]; exact hsc_t,
                by rw [htb3]; exact hbnd_ti,
                Function.update tm fp_try (some tp), ?_, ?_, ?_⟩
              · rw [htb3, congrFun hrl3 b]
                change ValidWhpSlice fl.N (fm.tryIns + 1)
                  (extractBTreeSlice fl.btL b tRole s3.mem) _
                rw [hbt_w2 b hb_t tRole htRole_lt, hbt_w1 b hb_t tRole htRole_lt]
                exact hv_tm1
              · intro fp' loc' htm'
                by_cases hfe : fp' = fp_try
                · subst hfe
                  rw [Function.update_self, Option.some.injEq] at htm'
                  subst htm'
                  exact ⟨Nat.lt_succ_self _, u,
                    by rw [htb3]; exact (hkey_eq b tp hb_t htp_lt).trans hu_val.symm,
                    by rw [mapBTree_fpHash_congr mapBTree (h₂ := hbs_lt) htb3 hbs_tb u]
                       exact hmb_tp,
                    congrArg Fin.val (fpHash_congr_salt hts3 u)⟩
                · rw [Function.update_of_ne hfe] at htm'
                  obtain ⟨hl', u', hk', hmb', hfp'⟩ := ht_s fp' loc' htm'
                  exact ⟨Nat.lt_succ_of_lt hl', u',
                    by rw [htb3]; exact (hkey_eq b loc' hb_t (hl'.trans htp_lt)).trans hk',
                    by rw [mapBTree_fpHash_congr mapBTree (h₂ := hbs_lt) htb3 hbs_tb u']
                       exact hmb',
                    (congrArg Fin.val (fpHash_congr_salt hts3 u')).trans hfp'⟩
              · intro loc' hl' u' hk' hmb'
                rw [htb3] at hk'
                rw [mapBTree_fpHash_congr mapBTree (h₂ := hbs_lt) htb3 hbs_tb u'] at hmb'
                rw [fpHash_congr_salt hts3 u']
                · by_cases hle : loc' = tp
                  · subst hle
                    have hk0 : fastKeyAt fl seeds.bkt s.mem b tp = u'.val :=
                      (hkey_eq b tp hb_t htp_lt).symm.trans hk'
                    have hu'_eq : u' = u := Fin.ext (hk0.symm.trans hu_val.symm)
                    subst hu'_eq
                    change Function.update tm fp_try (some tp) fp_try = some tp
                    exact Function.update_self ..
                  · have hl_lt_tp : loc' < tp := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hl') hle
                    have hk0 : fastKeyAt fl seeds.bkt s.mem b loc' = u'.val :=
                      (hkey_eq b loc' hb_t (hl_lt_tp.trans htp_lt)).symm.trans hk'
                    have htm_old := ht_c loc' hl_lt_tp u' hk0 hmb'
                    have hfp_ne : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u').val ≠
                        fp_try := by
                      intro heq_fp; rw [heq_fp, htm_q] at htm_old; nomatch htm_old
                    rw [Function.update_of_ne hfp_ne]; exact htm_old
          have hst_s3 : (Memory.spec 0).clientState s (drainTryStepProg fl.pBase) = s3 := by
            -- Re-derive without `houter` (cleared for `omega`): Wait, don't clear `hst_out`!
            exact hst_out.trans (by
              unfold drainTryInsertOrAdvProg; dsimp only
              have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
              have hr0_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N :=
                hm0
              have htR_eq : tryRoleOf (fm.curRole b) = tRole := rfl
              rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm8_r,
                StateTransitionSpec.clientState_bind, clientState_fastFpHashProg, hfp_t_res,
                StateTransitionSpec.clientState_bind, clientState_tryRoleProg,
                clientResult_tryRoleProg, htR_eq,
                StateTransitionSpec.clientState_bind, clientState_fastBTreeLookupProg,
                hlk_t_pair, ite_eq_right Nat.zero_ne_one,
                StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm17_r,
                StateTransitionSpec.clientState_bind, hr0_st, hr0_r,
                ite_eq_left ⟨hti_lt_N, htp_lt_N⟩,
                StateTransitionSpec.clientState_bind, hs1_def,
                StateTransitionSpec.clientState_bind, hs2_def, hs3_def])
          rw [hst_s3]
          exact ⟨hfr_w2.trans (hfr_w1.trans hfr_i), hcost_tot, hinv_s3, hbp_tot, htr_tot,
            hoi_tot, hof_tot, by rw [hfm_s3], by rw [hfm_s3], by rw [hfm_s3], by rw [hfm_s3],
            by rw [hfm_s3], fun h0 => absurd (h0.symm.trans hta1) Nat.zero_ne_one,
            fun _ => Or.inl ⟨htp_lt, by rw [hfm_s3]; exact hta1, by rw [hfm_s3], by rw [hfm_s3],
              by rw [hfm_s3], by rw [hfm_s3], by rw [hfm_s3]⟩⟩
      · -- `(b, tp)` is NOT in `mapBTree b`: simply advance `tryPos := tp + 1`!
        have hnot_cond : ¬(((Memory.spec 0).clientResult s
              (fastBTreeLookupProg ((fl.pBase, (b, fm.curRole b)), fp_cur))).1 = 1 ∧
            ((Memory.spec 0).clientResult s
              (fastBTreeLookupProg ((fl.pBase, (b, fm.curRole b)), fp_cur))).2 = tp) := by
          rw [hlk_c_res]
          cases hm : mapBTree b fp_cur with
          | none => simp
          | some v =>
            have hne : v ≠ tp := fun he => hmb_tp (he ▸ hm)
            simp [hne]
        obtain ⟨hst_out, hc_out⟩ := houter
        rw [ite_eq_right hnot_cond] at hst_out hc_out
        obtain ⟨hfr_w, hinv_s1, hbp_w, htr_w, hoi_w, hof_w, hfm_w⟩ :=
          drainTrySkipStep_inv hv hinv hta1 htp_lt fun b' hb' hbb u' hk' => by
            subst hbb
            have hu'_eq : u' = u := Fin.ext (hk'.symm.trans hu_val.symm)
            subst hu'_eq
            intro heq
            exact hnot_cond ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
        set s1 := (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 9), tp + 1))
        have hst_s1 : (Memory.spec 0).clientState s (drainTryStepProg fl.pBase) = s1 := by
          rw [hst_out]
          have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
          have hr0_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N := hm0
          rw [StateTransitionSpec.clientState_bind, hr0_st, hr0_r, ite_eq_left htp_lt_N]
        have hcost_tot : memoryCost (drainTryStepProg fl.pBase) s ≤
            600 + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 84 * hMaxBTree := by
          have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
          have hr0_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N := hm0
          have cw9 := memoryCost_fastWriteMetaProg ((fl.pBase, 9), tp + 1) s
          rw [Realization.memoryCost_bind', hr0_st, hr0_r, prog_memoryCost_read,
            ite_eq_left htp_lt_N] at hc_out
          have hd6 : 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) ≤
              6 * dTabWhp fl.c * (cTabWhp fl.c + 2) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
          have hm0' : 0 ≤ hMaxBTree := Nat.zero_le _
          linarith only [hc_out, cw9, hd6, hm0']
        rw [hst_s1]
        exact ⟨hfr_w, hcost_tot, hinv_s1, hbp_w, htr_w, hoi_w, hof_w,
          by rw [hfm_w], by rw [hfm_w], by rw [hfm_w], by rw [hfm_w], by rw [hfm_w],
          fun h0 => absurd (h0.symm.trans hta1) Nat.zero_ne_one,
          fun _ => Or.inl ⟨htp_lt, by rw [hfm_w]; exact hta1, by rw [hfm_w], by rw [hfm_w],
            by rw [hfm_w], by rw [hfm_w]; exact Nat.le_succ _, by rw [hfm_w]⟩⟩
    · -- `tp = cnt` branch: check `drainTryCheckDpProg`
      have htp_cnt : tp = cnt := le_antisymm htp_le (Nat.not_lt.mp htp_lt)
      have hdp_spec := drainTryCheckDpProg_spec hv hinv hta1 htp_cnt
      generalize hcoll_def : (Memory.spec 0).clientResult s (drainTryCheckDpProg fl.pBase) = coll
      rw [hcoll_def] at hdp_spec
      have hstep_tp_cnt :
          (Memory.spec 0).clientState s (drainTryStepProg fl.pBase) =
            (Memory.spec 0).clientState s
              (if coll = 0 then commitTrySaltProg fl.pBase else advanceTrySaltProg fl.pBase) ∧
          memoryCost (drainTryStepProg fl.pBase) s ≤
            30 + memoryCost (drainTryCheckDpProg fl.pBase) s +
              memoryCost
                (if coll = 0 then commitTrySaltProg fl.pBase else advanceTrySaltProg fl.pBase) s :=
        by
        unfold drainTryStepProg; dsimp only
        have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
        have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
            numBucketsWhp fl.N := hm11
        have cm6 := memoryCost_fastReadMetaProg (fl.pBase, 6) s
        have cm7 := memoryCost_fastReadMetaProg (fl.pBase, 7) s
        have cm9 := memoryCost_fastReadMetaProg (fl.pBase, 9) s
        have hc_cnt := hcnt_res.2
        have hdp_st : (Memory.spec 0).clientState s (drainTryCheckDpProg fl.pBase) = s :=
          runClient_state_drainTryCheckDpProg fl.pBase s
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hm6_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hm7_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          hr11_st, hr11_r, prog_memoryCost_read, ite_eq_left hguard,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadBktCntProg, hcnt_res.1,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hm9_r, ite_eq_right htp_lt,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          hdp_st, hcoll_def]
        exact ⟨rfl, by linarith only [cm6, cm7, cm9, hc_cnt]⟩
      by_cases hc0 : coll = 0
      · -- Commit branch (`coll = 0`)
        rw [ite_eq_left hc0] at hstep_tp_cnt
        obtain ⟨hfr_c, hc_c, hinv_c, hbp_c, hbt_c, htr_c, hoi_c, hof_c, hfm_c⟩ :=
          commitTrySaltProg_inv hv hinv hta1 htp_cnt
        have hcost_tot : memoryCost (drainTryStepProg fl.pBase) s ≤
            600 + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 84 * hMaxBTree := by
          have h1 := hstep_tp_cnt.2; have h2 := hdp_spec.1
          have hd6 : 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) ≤
              6 * dTabWhp fl.c * (cTabWhp fl.c + 2) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
          linarith only [h1, h2, hc_c, hd6, Nat.zero_le hMaxBTree]
        have hdp_zero : ∀ loc_dp (u_dp : Fin fl.U),
            bufCheckSlot (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) fm.drainPos =
              some (b, loc_dp) →
            fastKeyAt fl seeds.bkt s.mem b loc_dp = u_dp.val →
            ∃ hs_t : fm.trySalt < sMaxWhp fl.c fl.N,
              (Memory.spec 0).clientResult s
                (fastBTreeLookupProg ((fl.pBase, (b, tryRoleOf (fm.curRole b))),
                  (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u_dp).val)) = (0, 0) := by
          rcases hdp_spec.2 with ⟨_, hok⟩ | ⟨h1, _⟩
          · exact hok
          · exact absurd (hc0.symm.trans h1) Nat.zero_ne_one
        rw [hstep_tp_cnt.1]
        exact ⟨hfr_c, hcost_tot, hinv_c, hbp_c, htr_c, hoi_c, hof_c,
          by rw [hfm_c], by rw [hfm_c], by rw [hfm_c], by rw [hfm_c], by rw [hfm_c],
          fun h0 => absurd (h0.symm.trans hta1) Nat.zero_ne_one,
          fun _ => Or.inr (Or.inr ⟨htp_cnt, by rw [hfm_c], hdp_zero, hbt_c,
            by rw [hfm_c], by rw [hfm_c], by rw [hfm_c]⟩)⟩
      · -- Collision at `drainPos` (`coll ≠ 0`): `advanceTrySaltProg`!
        rw [ite_eq_right hc0] at hstep_tp_cnt
        obtain ⟨hfr_a, hc_a, hinv_a, hbp_a, htr_a, hoi_a, hof_a, hfm_a⟩ :=
          advanceTrySaltProg_inv hv hinv hta1
        have hwit : ∃ (hs_t : fm.trySalt < sMaxWhp fl.c fl.N) (u v : Fin fl.U),
            u ≠ v ∧ s_abs u ≠ none ∧ s_abs v ≠ none ∧
            epochBucket fl.c fl.U fl.N seeds.bkt u = b ∧
            epochBucket fl.c fl.U fl.N seeds.bkt v = b ∧
            fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ u =
              fpHash fl.c fl.U fl.N seeds.fp ⟨fm.trySalt, hs_t⟩ v := by
          rcases hdp_spec.2 with ⟨h0, _⟩ | ⟨_, hw⟩
          · exact absurd h0 hc0
          · exact hw
        obtain ⟨hs_w, u_w, v_w, hne_w, hsu_w, hsv_w, hbu_w, hbv_w, hfp_w⟩ := hwit
        have hcost_tot : memoryCost (drainTryStepProg fl.pBase) s ≤
            600 + 6 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 84 * hMaxBTree := by
          have h1 := hstep_tp_cnt.2; have h2 := hdp_spec.1
          have hd6 : 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) ≤
              6 * dTabWhp fl.c * (cTabWhp fl.c + 2) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
          linarith only [h1, h2, hc_a, hd6, Nat.zero_le hMaxBTree]
        rw [hstep_tp_cnt.1]
        exact ⟨hfr_a, hcost_tot, hinv_a, hbp_a, htr_a, hoi_a, hof_a,
          by rw [hfm_a], by rw [hfm_a], by rw [hfm_a], by rw [hfm_a], by rw [hfm_a],
          fun h0 => absurd (h0.symm.trans hta1) Nat.zero_ne_one,
          fun _ => Or.inr (Or.inl ⟨by rw [hfm_a]; exact hta1, by rw [hfm_a], by rw [hfm_a],
            by rw [hfm_a], by rw [hfm_a], by rw [hfm_a], hs_w, u_w, v_w, hne_w, hsu_w, hsv_w,
            hbu_w, hbv_w, hfp_w⟩)⟩
  · -- `fm.tryAct ≠ 1` (`fm.tryAct = 0`): pure no-op!
    have hng : ¬(fm.tryAct = 1 ∧ fm.tryBkt < numBucketsWhp fl.N) := fun ⟨h1, _⟩ => hta1 h1
    have hst : (Memory.spec 0).clientState s (drainTryStepProg fl.pBase) = s := by
      unfold drainTryStepProg
      have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
      have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
          numBucketsWhp fl.N := hm11
      rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm6_r,
        StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm7_r,
        StateTransitionSpec.clientState_bind, hr11_st, hr11_r, ite_eq_right hng]
      rfl
    have hc : memoryCost (drainTryStepProg fl.pBase) s ≤ 10 := by
      unfold drainTryStepProg
      have hr11_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
      have hr11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
          numBucketsWhp fl.N := hm11
      have cm6 := memoryCost_fastReadMetaProg (fl.pBase, 6) s
      have cm7 := memoryCost_fastReadMetaProg (fl.pBase, 7) s
      rw [Realization.memoryCost_bind', clientState_fastReadMetaProg, hm6_r,
        Realization.memoryCost_bind', clientState_fastReadMetaProg, hm7_r,
        Realization.memoryCost_bind', hr11_st, hr11_r, prog_memoryCost_read,
        ite_eq_right hng, memoryCost_pure]
      omega
    rw [hst]
    exact ⟨rfl, by omega, hinv, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun h1 => absurd h1 hta1⟩

/-! ## Section 3: Draining One `BufOld` Slot (`drainOldSlotProg`) -/

/-- Shadow-slice maintenance when `drainOldSlotProg` inserts `(fp, loc)` into `curRole` of `b`. -/
private def drainOldShadowMaintProg : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((pBase, b), (fp, loc)), cIns') => do
    let sc ← fastReadBktLaneProg (pBase, (b, 15))
    let cRole ← fastReadBktLaneProg (pBase, (b, 12))
    let shRole ← shadowRoleProg cRole
    if sc = 0 then do
      let thr6 ← Memory.read (pBase + 26)
      if thr6 ≤ cIns' then do
        fastBTreeResetProg (pBase, (b, shRole))
        fastWriteBktLaneProg ((pBase, (b, 14)), 0)
        fastWriteBktLaneProg ((pBase, (b, 15)), 1)
      else
        pure ()
    else do
      let nCap ← Memory.read (pBase + 0)
      if loc < nCap then
        if loc + 1 < sc then do
          let shIns ← fastReadBktLaneProg (pBase, (b, 14))
          if shIns < nCap then do
            fastBTreeInsertProg ((pBase, (b, shRole)), (fp, loc))
            fastWriteBktLaneProg ((pBase, (b, 14)), shIns + 1)
          else
            pure ()
        else
          pure ()
      else
        pure ()

private theorem drainOldShadowMaintProg_pre {w : ℕ} {x : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ}
    {s : Memory.State} (h : FastProgPre w x.1.1.1 s) :
    FastProgPre w x.1.1.1 ((Memory.spec 0).clientState s (drainOldShadowMaintProg x)) := by
  rcases x with ⟨⟨⟨pBase, b⟩, ⟨fp, loc⟩⟩, cIns'⟩
  obtain ⟨fl, rfl, hr⟩ := h
  unfold drainOldShadowMaintProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
    StateTransitionSpec.clientState_bind, clientState_shadowRoleProg]
  by_cases hsc : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 15))) = 0
  · rw [ite_eq_left hsc, StateTransitionSpec.clientState_bind]
    have hr26 : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 26)) = s := rfl
    rw [hr26]
    by_cases hthr : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 26)) ≤ cIns'
    · rw [ite_eq_left hthr, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind]
      have h1 : FastProgPre w fl.pBase ((Memory.spec 0).clientState s
          (fastBTreeResetProg (fl.pBase, (b, (Memory.spec 0).clientResult s
            (shadowRoleProg ((Memory.spec 0).clientResult s
              (fastReadBktLaneProg (fl.pBase, (b, 12))))))))) :=
        fastBTreeResetProg_pre (x := (fl.pBase, (b, _))) ⟨fl, rfl, hr⟩
      have h2 := fastWriteBktLaneProg_pre (x := ((fl.pBase, (b, 14)), 0)) h1
      exact fastWriteBktLaneProg_pre (x := ((fl.pBase, (b, 15)), 1)) h2
    · rw [ite_eq_right hthr]; exact ⟨fl, rfl, hr⟩
  · rw [ite_eq_right hsc, StateTransitionSpec.clientState_bind]
    have hr0 : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
    rw [hr0]
    by_cases hln : loc < (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0))
    · rw [ite_eq_left hln]
      by_cases hls : loc + 1 <
          (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 15)))
      · rw [ite_eq_left hls, StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg]
        by_cases hsi : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 14))) <
            (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0))
        · rw [ite_eq_left hsi, StateTransitionSpec.clientState_bind]
          have h1 : FastProgPre w fl.pBase ((Memory.spec 0).clientState s
              (fastBTreeInsertProg ((fl.pBase, (b, (Memory.spec 0).clientResult s
                (shadowRoleProg ((Memory.spec 0).clientResult s
                  (fastReadBktLaneProg (fl.pBase, (b, 12))))))), (fp, loc)))) :=
            fastBTreeInsertProg_pre (x := ((fl.pBase, (b, _)), (fp, loc))) ⟨fl, rfl, hr⟩
          exact fastWriteBktLaneProg_pre (x := ((fl.pBase, (b, 14)), _)) h1
        · rw [ite_eq_right hsi]; exact ⟨fl, rfl, hr⟩
      · rw [ite_eq_right hls]; exact ⟨fl, rfl, hr⟩
    · rw [ite_eq_right hln]; exact ⟨fl, rfl, hr⟩

private theorem realizesBounded_drainOldShadowMaint :
    RealizesBounded .exact drainOldShadowMaintProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((pBase, _), _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have hsr := realizesBounded_shadowRole
  have hbr := realizesBounded_fastBTreeReset
  have hwl := realizesBounded_fastWriteBktLane
  have hbi := realizesBounded_fastBTreeInsert
  realize
  all_goals (
    rcases d with ⟨⟨⟨pBase, b⟩, ⟨fp, loc⟩⟩, cIns'⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm0 : s.mem (fl.pBase + 0) = fl.N := hr.2.1 0 (by decide)
    have hm0_0 : s.mem fl.pBase = fl.N := by rwa [Nat.add_zero] at hm0
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktLaneProg,
      runClient_state_shadowRoleProg, hm0, hm0_0] at *
    have hp_rst := fastBTreeResetProg_pre (x := (fl.pBase, (b,
      ((Memory.spec 0).runClient s (shadowRoleProg
        ((Memory.spec 0).runClient s (fastReadBktLaneProg (fl.pBase, (b, 12)))).1)).1)))
      ⟨fl, rfl, hr⟩
    have hp_w14 := fastWriteBktLaneProg_pre (x := ((fl.pBase, (b, 14)), 0)) hp_rst
    have hp_ins := fastBTreeInsertProg_pre (x := ((fl.pBase, (b,
      ((Memory.spec 0).runClient s (shadowRoleProg
        ((Memory.spec 0).runClient s (fastReadBktLaneProg (fl.pBase, (b, 12)))).1)).1)),
      (fp, loc))) ⟨fl, rfl, hr⟩
    first | exact hw6 | exact ⟨fl, rfl, hr⟩ | exact hp_rst | exact hp_w14 | exact hp_ins | omega)

/-- Finish non-colliding `BufOld` slot migration into `BTree(b, curRole b)`. -/
private def drainOldInsertNoCollProg : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (((pBase, oldRole), (dp, rk)), (b, (fp, loc))) => do
    let cRole ← fastReadBktLaneProg (pBase, (b, 12))
    let cIns ← fastReadBktLaneProg (pBase, (b, 13))
    let nCap ← Memory.read (pBase + 0)
    let qMax ← Memory.read (pBase + 23)
    if cIns < nCap ∧ dp < qMax then do
      fastBTreeInsertProg ((pBase, (b, cRole)), (fp, loc))
      fastWriteBktLaneProg ((pBase, (b, 13)), cIns + 1)
      drainOldShadowMaintProg (((pBase, b), (fp, loc)), cIns + 1)
      fastBufDeleteProg ((pBase, oldRole), rk)
      fastWriteMetaProg ((pBase, 5), dp + 1)
    else
      pure ()

private theorem drainOldInsertNoCollProg_pre {w : ℕ}
    {x : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))} {s : Memory.State}
    (h : FastProgPre w x.1.1.1 s) :
    FastProgPre w x.1.1.1 ((Memory.spec 0).clientState s (drainOldInsertNoCollProg x)) := by
  rcases x with ⟨⟨⟨pBase, oldRole⟩, ⟨dp, rk⟩⟩, ⟨b, ⟨fp, loc⟩⟩⟩
  obtain ⟨fl, rfl, hr⟩ := h
  unfold drainOldInsertNoCollProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
    StateTransitionSpec.clientState_bind]
  have hr0 : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
  have hr23 : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s := rfl
  rw [hr0, StateTransitionSpec.clientState_bind, hr23]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    have h1 : FastProgPre w fl.pBase ((Memory.spec 0).clientState s
        (fastBTreeInsertProg ((fl.pBase, (b, (Memory.spec 0).clientResult s
          (fastReadBktLaneProg (fl.pBase, (b, 12))))), (fp, loc)))) :=
      fastBTreeInsertProg_pre (x := ((fl.pBase, (b, _)), (fp, loc))) ⟨fl, rfl, hr⟩
    have h2 := fastWriteBktLaneProg_pre (x := ((fl.pBase, (b, 13)),
      (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 13))) + 1)) h1
    have h3 := drainOldShadowMaintProg_pre (x := (((fl.pBase, b), (fp, loc)),
      (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 13))) + 1)) h2
    have h4 := fastBufDeleteProg_pre (x := ((fl.pBase, oldRole), rk)) h3
    exact fastWriteMetaProg_pre (x := ((fl.pBase, 5), dp + 1)) h4
  · exact ⟨fl, rfl, hr⟩

private theorem realizesBounded_drainOldInsertNoColl :
    RealizesBounded .exact drainOldInsertNoCollProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (((pBase, _), _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrl := realizesBounded_fastReadBktLane
  have hbi := realizesBounded_fastBTreeInsert
  have hwl := realizesBounded_fastWriteBktLane
  have hsm := realizesBounded_drainOldShadowMaint
  have hbd := realizesBounded_fastBufDelete
  have hwm := realizesBounded_fastWriteMeta
  realize
  all_goals (
    rcases d with ⟨⟨⟨pBase, oldRole⟩, ⟨dp, rk⟩⟩, ⟨b, ⟨fp, loc⟩⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm0 : s.mem (fl.pBase + 0) = fl.N := hr.2.1 0 (by decide)
    have hm0_0 : s.mem fl.pBase = fl.N := by rwa [Nat.add_zero] at hm0
    have hm23 : s.mem (fl.pBase + 23) = qEpochWhp fl.N := hr.2.1 23 (by decide)
    have hq_N : qEpochWhp fl.N ≤ fl.N := hr.1.bounds_le_N.2.2.2
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktLaneProg,
      hm0, hm0_0, hm23] at *
    have hp1 := fastBTreeInsertProg_pre (x := ((fl.pBase, (b,
      ((Memory.spec 0).runClient s (fastReadBktLaneProg (fl.pBase, (b, 12)))).1)), (fp, loc)))
      ⟨fl, rfl, hr⟩
    have hp2 := fastWriteBktLaneProg_pre (x := ((fl.pBase, (b, 13)),
      ((Memory.spec 0).runClient s (fastReadBktLaneProg (fl.pBase, (b, 13)))).1 + 1)) hp1
    have hp3 := drainOldShadowMaintProg_pre (x := (((fl.pBase, b), (fp, loc)),
      ((Memory.spec 0).runClient s (fastReadBktLaneProg (fl.pBase, (b, 13)))).1 + 1)) hp2
    have hp4 := fastBufDeleteProg_pre (x := ((fl.pBase, oldRole), rk)) hp3
    first | exact ⟨fl, rfl, hr⟩ | exact hp1 | exact hp2 | exact hp3 | exact hp4 | omega)

/-- Active-slot body of `drainOldSlotProg` after `fastShadowSteps8Prog (pBase, b)`. -/
private def drainOldActiveBodyProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((pBase, oldRole), (dp, (b, loc))) => do
    let cnt ← fastReadBktCntProg (pBase, b)
    let M ← Memory.read (pBase + 11)
    if b < M ∧ loc < cnt then do
      let (q, _v) ← fastBpReadAtProg (pBase, (b, loc))
      let u_val ← fastFeistelReconProg (pBase, (b, q))
      let rk ← fastRKeyProg (pBase, u_val)
      let bs ← fastReadBktLaneProg (pBase, (b, 5))
      let cRole ← fastReadBktLaneProg (pBase, (b, 12))
      let fp ← fastFpHashProg (pBase, (bs, u_val))
      let (hit, _loc') ← fastBTreeLookupProg ((pBase, (b, cRole)), fp)
      if hit = 0 then
        drainOldInsertNoCollProg (((pBase, oldRole), (dp, rk)), (b, (fp, loc)))
      else do
        let sc ← fastReadBktLaneProg (pBase, (b, 15))
        if sc = 0 then
          startTrySaltProg (pBase, b)
        else
          pure ()
    else
      pure ()

private theorem drainOldActiveBodyProg_pre {w : ℕ} {x : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))}
    {s : Memory.State} (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (drainOldActiveBodyProg x)) := by
  rcases x with ⟨⟨pBase, oldRole⟩, ⟨dp, ⟨b, loc⟩⟩⟩
  obtain ⟨fl, rfl, hr⟩ := h
  unfold drainOldActiveBodyProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg,
    StateTransitionSpec.clientState_bind]
  have hm11 : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s := rfl
  rw [hm11]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg]
    rcases (Memory.spec 0).clientResult s (fastBpReadAtProg (fl.pBase, (b, loc))) with ⟨q, _⟩
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_fastFeistelReconProg,
      StateTransitionSpec.clientState_bind, clientState_fastRKeyProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg,
      StateTransitionSpec.clientState_bind, clientState_fastFpHashProg,
      StateTransitionSpec.clientState_bind, clientState_fastBTreeLookupProg]
    rcases (Memory.spec 0).clientResult s _ with ⟨hit, _⟩
    dsimp only
    split_ifs
    · exact drainOldInsertNoCollProg_pre (x := (((fl.pBase, oldRole), (dp, _)), (b, (_, loc))))
        ⟨fl, rfl, hr⟩
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg]
      split_ifs
      · exact startTrySaltProg_pre (x := (fl.pBase, b)) ⟨fl, rfl, hr⟩
      · exact ⟨fl, rfl, hr⟩
  · exact ⟨fl, rfl, hr⟩

private theorem realizesBounded_drainOldActiveBody :
    RealizesBounded .exact drainOldActiveBodyProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrc := realizesBounded_fastReadBktCnt
  have hra := realizesBounded_fastBpReadAt
  have hfr := realizesBounded_fastFeistelRecon
  have hrk := realizesBounded_fastRKey
  have hrl := realizesBounded_fastReadBktLane
  have hfp := realizesBounded_fastFpHash
  have hbl := realizesBounded_fastBTreeLookup
  have hin := realizesBounded_drainOldInsertNoColl
  have hst := realizesBounded_startTrySalt
  realize
  all_goals (
    rcases d with ⟨⟨pBase, oldRole⟩, ⟨dp, ⟨b, loc⟩⟩⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadBktCntProg,
      runClient_state_fastBpReadAtProg, runClient_state_fastFeistelReconProg,
      runClient_state_fastRKeyProg, runClient_state_fastReadBktLaneProg,
      runClient_state_fastFpHashProg, runClient_state_fastBTreeLookupProg] at *
    first | exact ⟨fl, rfl, hr⟩ | omega)

/-- Drain one `BufOld` item-log slot `dp = drainPos` when `subStep < Q / 2` and `tryAct = 0`
(`¬ReadsWidth`). -/
def drainOldSlotProg (pBase : ℕ) : Memory.Prog Unit := do
  let curR ← fastReadMetaProg (pBase, 3)
  let dp ← fastReadMetaProg (pBase, 5)
  let qMax ← Memory.read (pBase + 23)
  if curR < 2 then do
    let oldRole ← pure (1 - curR)
    let ia ← fastBufItemAllocProg (pBase, oldRole)
    if ia ≤ qMax ∧ dp < ia then do
      let (act, (b, loc)) ← fastBufCheckSlotProg ((pBase, oldRole), dp)
      if act = 0 then
        fastWriteMetaProg ((pBase, 5), dp + 1)
      else do
        fastShadowSteps8Prog (pBase, b)
        drainOldActiveBodyProg ((pBase, oldRole), (dp, (b, loc)))
    else
      pure ()
  else
    pure ()

theorem drainOldSlotProg_pre {w pBase : ℕ} {s : Memory.State} (h : FastProgPre w pBase s) :
    FastProgPre w pBase ((Memory.spec 0).clientState s (drainOldSlotProg pBase)) := by
  obtain ⟨fl, rfl, hr⟩ := h
  unfold drainOldSlotProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
    StateTransitionSpec.clientState_bind]
  have hm23 : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s := rfl
  rw [hm23]
  split_ifs
  · rw [pure_bind, StateTransitionSpec.clientState_bind, clientState_fastBufItemAllocProg]
    split_ifs
    · rw [StateTransitionSpec.clientState_bind, clientState_fastBufCheckSlotProg]
      rcases (Memory.spec 0).clientResult s _ with ⟨act, ⟨b, loc⟩⟩
      dsimp only
      split_ifs
      · exact fastWriteMetaProg_pre (x := ((fl.pBase, 5), _)) ⟨fl, rfl, hr⟩
      · rw [StateTransitionSpec.clientState_bind]
        exact drainOldActiveBodyProg_pre (x := ((fl.pBase, _), (_, (b, loc))))
          (fastShadowSteps8Prog_pre (x := (fl.pBase, b)) ⟨fl, rfl, hr⟩)
    · exact ⟨fl, rfl, hr⟩
  · exact ⟨fl, rfl, hr⟩

theorem realizesBounded_drainOldSlot :
    RealizesBounded .exact drainOldSlotProg
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hia := realizesBounded_fastBufItemAlloc
  have hcs := realizesBounded_fastBufCheckSlot
  have hwm := realizesBounded_fastWriteMeta
  have hs8 := realizesBounded_fastShadowSteps8
  have hab := realizesBounded_drainOldActiveBody
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hm23 : s.mem (fl.pBase + 23) = qEpochWhp fl.N := hr.2.1 23 (by decide)
    have hq_N : qEpochWhp fl.N ≤ fl.N := hr.1.bounds_le_N.2.2.2
    have hn_w : fl.N < 2 ^ w := hr.1.mp_valid.nCap_lt_two_pow_w
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg,
      runClient_state_fastBufItemAllocProg, runClient_state_fastBufCheckSlotProg, hm23] at *
    first
    | exact ⟨fl, rfl, hr⟩
    | exact fastShadowSteps8Prog_pre (x := (fl.pBase, _)) ⟨fl, rfl, hr⟩
    | omega)

/-! ### Section 3b: Unconditional Specification of `drainOldSlotProg` -/

/-- Advance `drainPos := drainPos + 1` on an already-inactive `BufOld` slot (`bufCheckSlot = none`)
preserving `FastEpochInvGen` unconditionally. -/
private theorem drainOldSlot_inactive_inv {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hdp_lt : (extractFastMeta fl s.mem).drainPos <
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem).itemAlloc)
    (hnone : bufCheckSlot
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
      (extractFastMeta fl s.mem).drainPos = none) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 5), fm.drainPos + 1))
    s'.frontier = s.frontier ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    extractFastMeta fl s'.mem = { fm with drainPos := fm.drainPos + 1 } := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, hta_le, htry_all⟩ := hinv.tiers
  obtain ⟨hfr', hr', hbp', hbt', htr', hoi', hof', hm2', hfm'⟩ :=
    extractFastMeta_writeMeta (off := 5) (val := fm.drainPos + 1) hr₀
      (Or.inl ⟨by decide, by decide⟩)
  generalize hs'_def :
    (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 5), fm.drainPos + 1)) = s'
  rw [hs'_def] at hfr' hr' hbp' hbt' htr' hoi' hof' hm2' hfm'
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl] at hfm'
  have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
      fastKeyAt fl seeds.bkt s'.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
    fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp' hoi' hb' hl'
  rw [ite_eq_left hsub] at hold_half
  obtain ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_le_Q, hscan_o, hold_snd⟩ := hold_half
  have hbm' : ∀ b' < numBucketsWhp fl.N,
      let fm2 := extractFastMeta fl s'.mem
      fm2.bktSalt b' < sMaxWhp fl.c fl.N ∧ fm2.curRole b' < 3 ∧
      fm2.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
      (fm2.shadowCode b' = 0 → ¬(fm2.tryAct = 1 ∧ fm2.tryBkt = b') →
        fm2.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' => by
    dsimp only; rw [hfm']; exact hinv.bkt_meta_bounds b' hb'
  obtain ⟨hc_N, hc_sb, hc_sf, hc_bp, hc_cap, hc_ref⟩ :=
    FastEpochInvGen.fixed_pool_core hv hinv hbp' hoi' hof'
  refine ⟨hfr', ?_, hbp', htr', hoi', hof', hfm'⟩
  refine
    { param_table := hr'.2.1
      hdr_N := hc_N
      mode_zero := hm2'.trans hinv.mode_zero
      seed_bkt := hc_sb
      seed_fp := hc_sf
      bp_inv := hc_bp
      bkt_le_capMax := hc_cap
      refines := hc_ref
      role_lt := by rw [hfm']; exact hinv.role_lt
      subStep_lt := by rw [hfm']; exact hinv.subStep_lt
      bkt_meta_bounds := hbm'
      tiers := ?_ }
  dsimp only
  have hcr' : (extractFastMeta fl s'.mem).curBufRole = fm.curBufRole := by rw [hfm']
  have hss' : (extractFastMeta fl s'.mem).subStep = fm.subStep := by rw [hfm']
  have hdp' : (extractFastMeta fl s'.mem).drainPos = fm.drainPos + 1 := by rw [hfm']
  have hta' : (extractFastMeta fl s'.mem).tryAct = fm.tryAct := by rw [hfm']
  have htb' : (extractFastMeta fl s'.mem).tryBkt = fm.tryBkt := by rw [hfm']
  have hts' : (extractFastMeta fl s'.mem).trySalt = fm.trySalt := by rw [hfm']
  have htp' : (extractFastMeta fl s'.mem).tryPos = fm.tryPos := by rw [hfm']
  have hti' : (extractFastMeta fl s'.mem).tryIns = fm.tryIns := by rw [hfm']
  have hbs' : (extractFastMeta fl s'.mem).bktSalt = fm.bktSalt := by rw [hfm']
  have hrl' : (extractFastMeta fl s'.mem).curRole = fm.curRole := by rw [hfm']
  have hci' : (extractFastMeta fl s'.mem).curIns = fm.curIns := by rw [hfm']
  have hsi' : (extractFastMeta fl s'.mem).shadowIns = fm.shadowIns := by rw [hfm']
  have hsc' : (extractFastMeta fl s'.mem).shadowCode = fm.shadowCode := by rw [hfm']
  have htr_c := htr' fm.curBufRole hinv.role_lt
  have htr_o := htr' (1 - fm.curBufRole) (by have := hinv.role_lt; omega)
  refine ⟨mapCur, mapOld, mapBTree,
    by rw [hcr', htr_c]; exact hv_cur,
    by rw [hcr', htr_c]; exact hrb_cur,
    by rw [hcr', htr_c]; exact hrc_cur,
    by rw [hcr', htr_c, hss']; exact hia_cur,
    by rw [hcr', htr_c]; exact hna_cur,
    fun rk b' loc' hm => by
      obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
      exact ⟨hb', by rw [hbp']; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
    ?_, ?_, ?_, ?_, by rw [hta']; exact hta_le, ?_⟩
  · rw [hss', hcr', htr_o, hdp', hbp', ite_eq_left hsub]
    refine ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, Nat.succ_le_of_lt (hdp_lt.trans_le hia_o),
      ?_, fun rk b' loc' hm => ?_⟩
    · intro id hid
      have hid_dp : id ≤ fm.drainPos := Nat.le_of_lt_succ (lt_of_lt_of_le hid (min_le_left _ _))
      rcases Nat.eq_or_lt_of_le hid_dp with rfl | hlt
      · exact hnone
      · exact hscan_o id (lt_min hlt (hlt.trans hdp_lt))
    · obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := hold_snd rk b' loc' hm
      exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩
  · intro b' hb'
    rw [hbp']
    refine ⟨?_, fun fp' loc' hm => ?_⟩
    · rw [congrFun hci' b', congrFun hrl' b', hbt' b' hb' _ (hinv.bkt_meta_bounds b' hb').2.1]
      exact (hbt_all b' hb').1
    · obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
      exact ⟨hl', u',
        (congrArg Fin.val (fpHash_congr_salt (congrFun hbs' b') u')).trans hfp',
        (hkey_eq b' loc' hb' hl').trans hk',
        fun b₁ l₁ hm₁ => by
          obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
          rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
        fun b₂ l₂ hm₂ => by
          obtain ⟨_, hb₂, hl₂, _⟩ := hold_snd _ b₂ l₂ hm₂
          rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
  · intro b' hb' loc' hloc'
    rw [hbp'] at hloc'
    obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
    refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
    rw [fpHash_congr_salt (congrFun hbs' b') u']; exact ht'
  · intro b' hb' hsc0
    rw [congrFun hsc' b'] at hsc0 ⊢
    rw [hta', htb', congrFun hsi' b', congrFun hci' b', congrFun hrl' b', hbp']
    obtain ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc0
    have hr_sm := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
    rw [hbt' b' hb' _ hr_sm]
    exact ⟨h1, h2, h3, h4, sm', hv_sm', heq_sm'⟩
  · intro hta1
    rw [hta'] at hta1
    obtain ⟨_, hb_t, hs_t, htp_le, hsc_t, hti_le, tm, hv_tm, ht_s, ht_c⟩ := htry_all hta1
    have hbs_tb : (extractFastMeta fl s'.mem).bktSalt (extractFastMeta fl s'.mem).tryBkt =
        fm.bktSalt fm.tryBkt := by rw [htb', congrFun hbs' fm.tryBkt]
    have hbs_lt := (hinv.bkt_meta_bounds fm.tryBkt hb_t).1
    rw [hss', htp', hti', hbp']
    refine ⟨hsub, htb'.symm ▸ hb_t, hts'.symm ▸ hs_t,
      by rw [htb']; exact htp_le,
      by rw [htb', congrFun hsc' fm.tryBkt]; exact hsc_t,
      by rw [htb']; exact hti_le, tm, ?_, ?_, ?_⟩
    · rw [htb', congrFun hrl' fm.tryBkt]
      rw [hbt' _ hb_t _ (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds _ hb_t).2.1).1]
      exact hv_tm
    · intro fp' loc' htm'
      obtain ⟨hl', u', hk', hmb', hfp'⟩ := ht_s fp' loc' htm'
      exact ⟨hl', u',
        by rw [htb']; exact (hkey_eq _ loc' hb_t (hl'.trans_le htp_le)).trans hk',
        by rw [mapBTree_fpHash_congr mapBTree (h₂ := hbs_lt) htb' hbs_tb u']; exact hmb',
        (congrArg Fin.val (fpHash_congr_salt hts' u')).trans hfp'⟩
    · intro loc' hl' u' hk' hmb'
      rw [htb'] at hk'
      rw [mapBTree_fpHash_congr mapBTree (h₂ := hbs_lt) htb' hbs_tb u'] at hmb'
      rw [fpHash_congr_salt hts' u']
      exact ht_c loc' hl' u' ((hkey_eq _ loc' hb_t (hl'.trans_le htp_le)).symm.trans hk') hmb'

/-- Starting candidate salt search on bucket `b` (`startTrySaltProg (fl.pBase, b)`) preserves
`FastEpochInvGen` unconditionally when `subStep < Q / 2`, `tryAct = 0`, and `shadowCode b = 0`. -/
private theorem startTrySaltProg_inv {slackCur : ℕ} {fl : FastEpochLayout} {w slack b : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hta0 : (extractFastMeta fl s.mem).tryAct = 0)
    (hb : b < numBucketsWhp fl.N)
    (hsc0 : (extractFastMeta fl s.mem).shadowCode b = 0) :
    let s' := (Memory.spec 0).clientState s (startTrySaltProg (fl.pBase, b))
    let fm := extractFastMeta fl s.mem
    s'.frontier = s.frontier ∧
    memoryCost (startTrySaltProg (fl.pBase, b)) s ≤ 50 ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    extractFastMeta fl s'.mem =
      { fm with tryAct := 1, tryBkt := b, trySalt := 0, tryPos := 0, tryIns := 0 } := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, _, _⟩ := hinv.tiers
  obtain ⟨hfr', hr', hc', hbp', htr', hoi', hof', hm2', hspec⟩ :=
    startTrySaltProg_frame (b := b) hr₀
  generalize hs'_def : (Memory.spec 0).clientState s (startTrySaltProg (fl.pBase, b)) = s'
  rw [hs'_def] at hfr' hr' hbp' htr' hoi' hof' hm2' hspec
  obtain ⟨hfm', hv_z, hsl_o⟩ := hspec hb
  have hs0_lt : 0 < sMaxWhp fl.c fl.N := by
    have := (hinv.bkt_meta_bounds b hb).1; omega
  have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
      fastKeyAt fl seeds.bkt s'.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
    fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp' hoi' hb' hl'
  rw [ite_eq_left hsub] at hold_half
  obtain ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_le_Q, hscan_o, hold_snd⟩ := hold_half
  have hbm' : ∀ b' < numBucketsWhp fl.N,
      let fm2 := extractFastMeta fl s'.mem
      fm2.bktSalt b' < sMaxWhp fl.c fl.N ∧ fm2.curRole b' < 3 ∧
      fm2.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
      (fm2.shadowCode b' = 0 → ¬(fm2.tryAct = 1 ∧ fm2.tryBkt = b') →
        fm2.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' => by
    dsimp only; rw [hfm']
    exact ⟨(hinv.bkt_meta_bounds b' hb').1, (hinv.bkt_meta_bounds b' hb').2.1,
      (hinv.bkt_meta_bounds b' hb').2.2.1, fun hsc' _ =>
        (hinv.bkt_meta_bounds b' hb').2.2.2 hsc' (fun ⟨h1, _⟩ =>
          absurd (hta0.symm.trans h1) Nat.zero_ne_one)⟩
  obtain ⟨hc_N, hc_sb, hc_sf, hc_bp, hc_cap, hc_ref⟩ :=
    FastEpochInvGen.fixed_pool_core hv hinv hbp' hoi' hof'
  refine ⟨hfr', hc', ?_, hbp', htr', hoi', hof', hfm'⟩
  refine
    { param_table := hr'.2.1
      hdr_N := hc_N
      mode_zero := hm2'.trans hinv.mode_zero
      seed_bkt := hc_sb
      seed_fp := hc_sf
      bp_inv := hc_bp
      bkt_le_capMax := hc_cap
      refines := hc_ref
      role_lt := by rw [hfm']; exact hinv.role_lt
      subStep_lt := by rw [hfm']; exact hinv.subStep_lt
      bkt_meta_bounds := hbm'
      tiers := ?_ }
  dsimp only
  have hcr' : (extractFastMeta fl s'.mem).curBufRole = fm.curBufRole := by rw [hfm']
  have hss' : (extractFastMeta fl s'.mem).subStep = fm.subStep := by rw [hfm']
  have hdp' : (extractFastMeta fl s'.mem).drainPos = fm.drainPos := by rw [hfm']
  have hta' : (extractFastMeta fl s'.mem).tryAct = 1 := by rw [hfm']
  have htb' : (extractFastMeta fl s'.mem).tryBkt = b := by rw [hfm']
  have hts' : (extractFastMeta fl s'.mem).trySalt = 0 := by rw [hfm']
  have htp' : (extractFastMeta fl s'.mem).tryPos = 0 := by rw [hfm']
  have hti' : (extractFastMeta fl s'.mem).tryIns = 0 := by rw [hfm']
  have hbs' : (extractFastMeta fl s'.mem).bktSalt = fm.bktSalt := by rw [hfm']
  have hrl' : (extractFastMeta fl s'.mem).curRole = fm.curRole := by rw [hfm']
  have hci' : (extractFastMeta fl s'.mem).curIns = fm.curIns := by rw [hfm']
  have hsi' : (extractFastMeta fl s'.mem).shadowIns = fm.shadowIns := by rw [hfm']
  have hsc' : (extractFastMeta fl s'.mem).shadowCode = fm.shadowCode := by rw [hfm']
  have htr_c := htr' fm.curBufRole hinv.role_lt
  have htr_o := htr' (1 - fm.curBufRole) (by have := hinv.role_lt; omega)
  refine ⟨mapCur, mapOld, mapBTree,
    by rw [hcr', htr_c]; exact hv_cur,
    by rw [hcr', htr_c]; exact hrb_cur,
    by rw [hcr', htr_c]; exact hrc_cur,
    by rw [hcr', htr_c, hss']; exact hia_cur,
    by rw [hcr', htr_c]; exact hna_cur,
    fun rk b' loc' hm => by
      obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk b' loc' hm
      exact ⟨hb', by rw [hbp']; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
    ?_, ?_, ?_, ?_, by rw [hta'], ?_⟩
  · rw [hss', hcr', htr_o, hdp', hbp', ite_eq_left hsub]
    exact ⟨hv_o, hrb_o, hrc_o, hia_o, hna_o, hdp_le_Q, hscan_o, fun rk b' loc' hm => by
      obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := hold_snd rk b' loc' hm
      exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩⟩
  · intro b' hb'
    rw [hbp']
    refine ⟨?_, fun fp' loc' hm => ?_⟩
    · rw [congrFun hci' b', congrFun hrl' b']
      have hr_b' := (hinv.bkt_meta_bounds b' hb').2.1
      by_cases hbb : b' = b
      · subst hbb
        rw [hsl_o b' hb' _ hr_b' (Or.inr (tryRoleOf_lt_and_ne hr_b').2.1.symm)]
        exact (hbt_all b' hb').1
      · rw [hsl_o b' hb' _ hr_b' (Or.inl hbb)]
        exact (hbt_all b' hb').1
    · obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
      exact ⟨hl', u',
        (congrArg Fin.val (fpHash_congr_salt (congrFun hbs' b') u')).trans hfp',
        (hkey_eq b' loc' hb' hl').trans hk',
        fun b₁ l₁ hm₁ => by
          obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
          rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
        fun b₂ l₂ hm₂ => by
          obtain ⟨_, hb₂, hl₂, _⟩ := hold_snd _ b₂ l₂ hm₂
          rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
  · intro b' hb' loc' hloc'
    rw [hbp'] at hloc'
    obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
    refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
    rw [fpHash_congr_salt (congrFun hbs' b') u']; exact ht'
  · intro b' hb' hsc_nz
    rw [congrFun hsc' b'] at hsc_nz ⊢
    have hne : b' ≠ b := fun he => by subst he; exact hsc_nz hsc0
    rw [hta', htb', congrFun hsi' b', congrFun hci' b', congrFun hrl' b', hbp']
    obtain ⟨h1, _, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc_nz
    have hr_sm := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
    rw [hsl_o b' hb' _ hr_sm (Or.inl hne)]
    exact ⟨h1, by simp [hne.symm], h3, h4, sm', hv_sm', heq_sm'⟩
  · intro _
    rw [hss', htp', hti', hbp']
    refine ⟨hsub, htb'.symm ▸ hb, hts'.symm ▸ hs0_lt, Nat.zero_le _,
      by rw [htb', congrFun hsc' b]; exact hsc0,
      by rw [htb']
         have hcap : bp.bktCount b ≤ capMaxWhp fl.N := hinv.bkt_le_capMax b hb
         unfold capMaxWhp at hcap
         simp only [Nat.mul_zero, Nat.zero_add, Nat.sub_zero]
         exact (Nat.mul_le_mul_left 5 hcap).trans (by ring_nf; exact le_rfl),
      fun _ => none, ?_,
      (fun _ _ h => (Option.some_ne_none _ h.symm).elim),
      (fun _ h => absurd h (Nat.not_lt_zero _))⟩
    rw [htb', congrFun hrl' b]
    exact hv_z

/-- Low-level frame and transition spec for `drainOldShadowMaintProg`. -/
private theorem drainOldShadowMaintProg_spec {fl : FastEpochLayout} {w b fp loc cIns' : ℕ}
    {shMap : ℕ → Option ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hb : b < numBucketsWhp fl.N)
    (hcRole_lt : (extractFastMeta fl s.mem).curRole b < 3)
    (hfp_lt : fp < 2 ^ fpBitsWhp fl.N)
    (hloc_val : loc < 2 ^ valLaneBitsWhp fl.N)
    (hloc_N : loc < fl.N)
    (hsh_valid : (extractFastMeta fl s.mem).shadowCode b ≠ 0 →
      (extractFastMeta fl s.mem).shadowIns b ≤ 8 * slabScale fl.N ^ 12 ∧
      (extractFastMeta fl s.mem).shadowIns b < fl.N ∧
      ValidWhpSlice fl.N ((extractFastMeta fl s.mem).shadowIns b)
        (extractBTreeSlice fl.btL b
          (shadowRoleOf ((extractFastMeta fl s.mem).curRole b)) s.mem) shMap) :
    let fm := extractFastMeta fl s.mem
    let sc := fm.shadowCode b
    let shRole := shadowRoleOf (fm.curRole b)
    let thr6 := 6 * slabScale fl.N ^ 12
    let s' := (Memory.spec 0).clientState s
      (drainOldShadowMaintProg (((fl.pBase, b), (fp, loc)), cIns'))
    s'.frontier = s.frontier ∧
    FastLayoutReady w fl s' ∧
    memoryCost (drainOldShadowMaintProg (((fl.pBase, b), (fp, loc)), cIns')) s ≤
      180 + 72 * hMaxBTree ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    s'.mem (fl.metaBase + 2) = s.mem (fl.metaBase + 2) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ r < 3, (b' ≠ b ∨ r ≠ shRole) →
      extractBTreeSlice fl.btL b' r s'.mem = extractBTreeSlice fl.btL b' r s.mem) ∧
    (if sc = 0 then
      if thr6 ≤ cIns' then
        extractFastMeta fl s'.mem =
          { fm with
            shadowIns := Function.update fm.shadowIns b 0
            shadowCode := Function.update fm.shadowCode b 1 } ∧
        ValidWhpSlice fl.N 0 (extractBTreeSlice fl.btL b shRole s'.mem) (fun _ => none)
      else
        s' = s
    else
      if loc + 1 < sc then
        extractFastMeta fl s'.mem =
          { fm with shadowIns := Function.update fm.shadowIns b (fm.shadowIns b + 1) } ∧
        ValidWhpSlice fl.N (fm.shadowIns b + 1)
          (extractBTreeSlice fl.btL b shRole s'.mem) (Function.update shMap fp (some loc))
      else
        s' = s) := by
  dsimp only
  have hpt := hr.2.1
  set fm := extractFastMeta fl s.mem
  set sc := fm.shadowCode b
  set shRole := shadowRoleOf (fm.curRole b)
  obtain ⟨hshRole_lt, _⟩ := shadowRoleOf_lt_and_ne hcRole_lt
  have hsc_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 15))) = sc := by
    rw [clientResult_fastReadBktLaneProg hpt hb (by decide)]
    change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb]
  have hcr_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12))) =
      fm.curRole b := by
    rw [clientResult_fastReadBktLaneProg hpt hb (by decide)]
    change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb]
  have hsr_eq : shadowRoleOf (fm.curRole b) = shRole := rfl
  have c15 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 15)) s
  have c12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s
  have hN_pos : 1 ≤ fl.N := by omega
  unfold drainOldShadowMaintProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadBktLaneProg, hsc_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadBktLaneProg, hcr_r,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_shadowRoleProg, clientResult_shadowRoleProg, memoryCost_shadowRoleProg, hsr_eq]
  by_cases hsc0 : sc = 0
  · rw [ite_eq_left hsc0, ite_eq_left hsc0]
    have hr26_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 26)) = s := rfl
    have hr26_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 26)) =
        6 * slabScale fl.N ^ 12 := hpt 26 (by decide)
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      hr26_st, hr26_r, prog_memoryCost_read]
    by_cases hthr : 6 * slabScale fl.N ^ 12 ≤ cIns'
    · rw [ite_eq_left hthr, ite_eq_left hthr]
      obtain ⟨hfr1, hr1, hc1, hbp1, hfm1, hm2_1, htr1, hoi1, hof1, hsl1⟩ :=
        fastBTreeResetProg_spec (b := b) (role := shRole) hr
      generalize hs1_def : (Memory.spec 0).clientState s
        (fastBTreeResetProg (fl.pBase, (b, shRole))) = s1
      rw [hs1_def] at hfr1 hr1 hbp1 hfm1 hm2_1 htr1 hoi1 hof1 hsl1
      obtain ⟨hv_z, hsl_o⟩ := hsl1 hb hshRole_lt
      obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hof2, hoi2⟩ :=
        fastWriteBktLaneProg_frame (b := b) (lane := 14) (val := 0) hr1
      obtain ⟨hm2_2, hfm2⟩ := extractFastMeta_writeBktLane (lane := 14) (val := 0) hr1 hb
        (Or.inr ⟨by decide, by decide⟩) (Nat.zero_le fl.N)
      have cw14 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 14)), 0) s1
      generalize hs2_def : (Memory.spec 0).clientState s1
        (fastWriteBktLaneProg ((fl.pBase, (b, 14)), 0)) = s2
      rw [hs2_def] at hfr2 hr2 hbp2 hbt2 htr2 hof2 hoi2 hm2_2 hfm2
      obtain ⟨hfr3, hr3, hbp3, hbt3, htr3, hof3, hoi3⟩ :=
        fastWriteBktLaneProg_frame (b := b) (lane := 15) (val := 1) hr2
      obtain ⟨hm2_3, hfm3⟩ := extractFastMeta_writeBktLane (lane := 15) (val := 1) hr2 hb
        (Or.inr ⟨by decide, by decide⟩) hN_pos
      have cw15 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 15)), 1) s2
      generalize hs3_def : (Memory.spec 0).clientState s2
        (fastWriteBktLaneProg ((fl.pBase, (b, 15)), 1)) = s3
      rw [hs3_def] at hfr3 hr3 hbp3 hbt3 htr3 hof3 hoi3 hm2_3 hfm3
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_left rfl] at hfm2
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_right (by decide)] at hfm3
      rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs2_def, hs3_def]
      have hm0_le : 0 ≤ hMaxBTree := Nat.zero_le _
      refine ⟨hfr3.trans (hfr2.trans hfr1), hr3,
        by linarith only [c15, c12, hc1, cw14, cw15, hm0_le],
        hbp3.trans (hbp2.trans hbp1),
        fun r hr_lt => (htr3 r hr_lt).trans ((htr2 r hr_lt).trans (htr1 r hr_lt)),
        fun a ha => (hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha)),
        fun a ha => (hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha)),
        hm2_3.trans (hm2_2.trans hm2_1),
        fun b' hb' r' hr' hne =>
          (hbt3 b' hb' r' hr').trans ((hbt2 b' hb' r' hr').trans (hsl_o b' hb' r' hr' hne)),
        by rw [hfm3, hfm2, hfm1],
        by rw [hbt3 b hb shRole hshRole_lt, hbt2 b hb shRole hshRole_lt]; exact hv_z⟩
    · rw [ite_eq_right hthr, ite_eq_right hthr, StateTransitionSpec.clientState_pure,
        memoryCost_pure]
      have hm0_le : 0 ≤ hMaxBTree := Nat.zero_le _
      exact ⟨rfl, hr, by linarith only [c15, c12, hm0_le], rfl, fun _ _ => rfl,
        fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ _ _ _ => rfl, rfl⟩
  · rw [ite_eq_right hsc0, ite_eq_right hsc0]
    have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
    have hr0_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N :=
      hpt 0 (by decide)
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      hr0_st, hr0_r, prog_memoryCost_read, ite_eq_left hloc_N]
    by_cases hls : loc + 1 < sc
    · rw [ite_eq_left hls, ite_eq_left hls]
      obtain ⟨hsi_le, hsi_lt_N, hv_sh⟩ := hsh_valid hsc0
      have hsi_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 14))) =
          fm.shadowIns b := by
        rw [clientResult_fastReadBktLaneProg hpt hb (by decide)]
        change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb]
      have c14 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 14)) s
      rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastReadBktLaneProg, hsi_r, ite_eq_left hsi_lt_N]
      obtain ⟨hfr1, hr1, hc1, hv_sh', hbt_o1, hbp1, hfm1, hm2_1, _, htr1, hoi1, hof1⟩ :=
        fastBTreeInsertProg_spec (role := shRole) hr hb hshRole_lt hsi_le hv_sh hfp_lt hloc_val
      generalize hs1_def : (Memory.spec 0).clientState s
        (fastBTreeInsertProg ((fl.pBase, (b, shRole)), (fp, loc))) = s1
      rw [hs1_def] at hfr1 hr1 hv_sh' hbt_o1 hbp1 hfm1 hm2_1 htr1 hoi1 hof1
      obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hof2, hoi2⟩ :=
        fastWriteBktLaneProg_frame (b := b) (lane := 14) (val := fm.shadowIns b + 1) hr1
      obtain ⟨hm2_2, hfm2⟩ := extractFastMeta_writeBktLane (lane := 14) (val := fm.shadowIns b + 1)
        hr1 hb (Or.inr ⟨by decide, by decide⟩) (Nat.succ_le_of_lt hsi_lt_N)
      have cw14 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 14)), fm.shadowIns b + 1) s1
      generalize hs2_def : (Memory.spec 0).clientState s1
        (fastWriteBktLaneProg ((fl.pBase, (b, 14)), fm.shadowIns b + 1)) = s2
      rw [hs2_def] at hfr2 hr2 hbp2 hbt2 htr2 hof2 hoi2 hm2_2 hfm2
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_left rfl] at hfm2
      rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def, hs2_def]
      refine ⟨hfr2.trans hfr1, hr2,
        by linarith only [c15, c12, c14, hc1, cw14],
        hbp2.trans hbp1,
        fun r hr_lt => (htr2 r hr_lt).trans (htr1 r hr_lt),
        fun a ha => (hoi2 a ha).trans (hoi1 a ha),
        fun a ha => (hof2 a ha).trans (hof1 a ha),
        hm2_2.trans hm2_1,
        fun b' hb' r' hr' hne => (hbt2 b' hb' r' hr').trans (hbt_o1 b' hb' r' hr' hne),
        by rw [hfm2, hfm1],
        by rw [hbt2 b hb shRole hshRole_lt]; exact hv_sh'⟩
    · rw [ite_eq_right hls, ite_eq_right hls, StateTransitionSpec.clientState_pure,
        memoryCost_pure]
      have hm0_le : 0 ≤ hMaxBTree := Nat.zero_le _
      exact ⟨rfl, hr, by linarith only [c15, c12, hm0_le], rfl, fun _ _ => rfl,
        fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ _ _ _ => rfl, rfl⟩

/-- Unconditional invariant step for `drainOldInsertNoCollProg` once a non-colliding `BufOld`
slot `(b, loc)` with key `u` has been checked (with `+8` shadow compaction slack already run). -/
private theorem drainOldInsertNoCollProg_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {b loc : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State} (u : Fin fl.U)
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hta0 : (extractFastMeta fl s.mem).tryAct = 0)
    (hchk : bufCheckSlot
      (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
      (extractFastMeta fl s.mem).drainPos = some (b, loc))
    (hu_key : fastKeyAt fl seeds.bkt s.mem b loc = u.val)
    (hb : b < numBucketsWhp fl.N)
    (hno_hit : (Memory.spec 0).clientResult s (fastBTreeLookupProg
      ((fl.pBase, (b, (extractFastMeta fl s.mem).curRole b)),
        (fpHash fl.c fl.U fl.N seeds.fp
          ⟨(extractFastMeta fl s.mem).bktSalt b,
            (hinv.bkt_meta_bounds b hb).1⟩ u).val)) = (0, 0))
    (hslack : (extractFastMeta fl s.mem).shadowCode b ≠ 0 →
      let fm := extractFastMeta fl s.mem
      let cnt := (extractBlockPool fl.mp s.mem).bktCount b
      4 * fm.shadowIns b + 5 * (cnt - (fm.shadowCode b - 1)) + 8 ≤ 20 * slabScale fl.N ^ 12 ∧
      8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) + (cnt - (fm.shadowCode b - 1)) + 8 ≤
        4 * slabScale fl.N ^ 12) :
    let fm := extractFastMeta fl s.mem
    let oldRole := 1 - fm.curBufRole
    let rk := rKeyOf fl.c fl.U fl.N seeds.fp u
    let fp := (fpHash fl.c fl.U fl.N seeds.fp
      ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ u).val
    let s' := (Memory.spec 0).clientState s
      (drainOldInsertNoCollProg (((fl.pBase, oldRole), (fm.drainPos, rk)), (b, (fp, loc))))
    let fm' := extractFastMeta fl s'.mem
    s'.frontier = s.frontier ∧
    memoryCost
      (drainOldInsertNoCollProg (((fl.pBase, oldRole), (fm.drainPos, rk)), (b, (fp, loc)))) s ≤
      400 + 2 * cTabWhp fl.c + 144 * hMaxBTree ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractBufTrie (fl.trieL fm.curBufRole) s'.mem =
      extractBufTrie (fl.trieL fm.curBufRole) s.mem ∧
    extractBufTrie (fl.trieL oldRole) s'.mem =
      bufDelete (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL oldRole) s.mem) rk ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    fm'.drainPos = fm.drainPos + 1 ∧
    fm'.tryAct = 0 ∧
    fm'.bktSalt = fm.bktSalt ∧
    (∀ b' ≠ b, fm'.curRole b' = fm.curRole b' ∧ fm'.curIns b' = fm.curIns b' ∧
      fm'.shadowIns b' = fm.shadowIns b' ∧ fm'.shadowCode b' = fm.shadowCode b') := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  have hpt := hinv.param_table
  obtain ⟨h64_L12, hcap_N, _, hq_N⟩ := hv.bounds_le_N
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set oldRole := 1 - fm.curBufRole
  have hfm_role_lt : fm.curBufRole < 2 := hinv.role_lt
  have hold_lt : oldRole < 2 := by dsimp only [oldRole]; omega
  have hrole_swap : 1 - oldRole = fm.curBufRole := by dsimp only [oldRole]; omega
  have hbs_lt := (hinv.bkt_meta_bounds b hb).1
  have hcRole_lt := (hinv.bkt_meta_bounds b hb).2.1
  have hcIns_le := (hinv.bkt_meta_bounds b hb).2.2.1
  set cRole := fm.curRole b
  set shRole := shadowRoleOf cRole
  obtain ⟨hshRole_lt, hsh_ne_c⟩ := shadowRoleOf_lt_and_ne hcRole_lt
  set rk := rKeyOf fl.c fl.U fl.N seeds.fp u
  set fp := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hbs_lt⟩ u).val
  have hfp_lt : fp < 2 ^ fpBitsWhp fl.N :=
    (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b, hbs_lt⟩ u).isLt
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, hrb_cur, hrc_cur, hia_cur, hna_cur, hcur_snd,
    hold_half, hbt_all, hcomp, hsh_all, _, _⟩ := hinv.tiers
  rw [ite_eq_left hsub] at hold_half
  obtain ⟨hv_old, hrb_old, hrc_old, hia_old, hna_old, hdp_le_Q, hscan_old, hold_snd⟩ := hold_half
  obtain ⟨hdp_lt_ia, rk_dp, hrk_dp_lt, hwalk_dp, hmo_dp⟩ := hv_old.checkSlot_some hchk
  obtain ⟨hcur_none, _, hloc_lt, u_dp, hrk_dp_eq, hk_dp⟩ := hold_snd rk_dp b loc hmo_dp
  have hu_eq : u_dp = u := Fin.ext (hk_dp.symm.trans hu_key)
  rw [hu_eq] at hrk_dp_eq
  have hrk_eq : rk = rk_dp := hrk_dp_eq
  have hrk_lt : rk < 2 ^ (cTabWhp fl.c * bCharWhp fl.N) := hrk_eq ▸ hrk_dp_lt
  have hdp_lt_Q : fm.drainPos < qEpochWhp fl.N := lt_of_lt_of_le hdp_lt_ia hia_old
  have hcnt_le : bp.bktCount b ≤ capMaxWhp fl.N := hinv.bkt_le_capMax b hb
  have hloc_N : loc < fl.N := lt_of_lt_of_le hloc_lt (hcnt_le.trans hcap_N)
  have hloc_val : loc < 2 ^ valLaneBitsWhp fl.N := by
    rw [two_pow_valLaneBitsWhp]
    have h4 : bp.bktCount b ≤ 4 * slabScale fl.N ^ 12 := hcnt_le
    have hlt : loc < bp.bktCount b := hloc_lt
    linarith only [h4, hlt, Nat.zero_le (slabScale fl.N ^ 12)]
  have hcIns_lt_8L : fm.curIns b < 8 * slabScale fl.N ^ 12 := by
    by_cases hsc0 : fm.shadowCode b = 0
    · have hlt6 : fm.curIns b < 6 * slabScale fl.N ^ 12 :=
        (hinv.bkt_meta_bounds b hb).2.2.2 hsc0 (fun ⟨h1, _⟩ =>
          absurd (hta0.symm.trans h1) Nat.zero_ne_one)
      linarith only [hlt6, Nat.zero_le (slabScale fl.N ^ 12)]
    · have h2 := (hslack hsc0).2
      change 8 * (fm.curIns b - 6 * slabScale fl.N ^ 12) +
        (bp.bktCount b - (fm.shadowCode b - 1)) + 8 ≤ 4 * slabScale fl.N ^ 12 at h2
      omega
  have hcIns_lt_N : fm.curIns b < fl.N := by
    linarith only [hcIns_lt_8L, h64_L12, Nat.zero_le (slabScale fl.N ^ 12)]
  have hmb_none : mapBTree b fp = none := by
    obtain ⟨hlk_r, _⟩ := fastBTreeLookupProg_spec hr₀ hb hcRole_lt hcIns_le (hbt_all b hb).1 hfp_lt
    rw [hlk_r] at hno_hit
    cases hm : mapBTree b fp with
    | none => rfl
    | some v => rw [hm] at hno_hit; cases hno_hit
  -- Read-only lanes at start
  have hcr_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 12))) =
      cRole := by
    rw [clientResult_fastReadBktLaneProg hpt hb (by decide)]
    change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb]
  have hci_r : (Memory.spec 0).clientResult s (fastReadBktLaneProg (fl.pBase, (b, 13))) =
      fm.curIns b := by
    rw [clientResult_fastReadBktLaneProg hpt hb (by decide)]
    change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb]
  -- Extract existing `shMap` if `shadowCode b ≠ 0`
  have hsh_ex : ∃ shMap : ℕ → Option ℕ, fm.shadowCode b ≠ 0 →
      let shPos := fm.shadowCode b - 1
      shPos < bp.bktCount b ∧
      ValidWhpSlice fl.N (fm.shadowIns b)
        (extractBTreeSlice fl.btL b shRole s.mem) shMap ∧
      (∀ fp', shMap fp' =
        match mapBTree b fp' with
        | some l => if l < shPos then some l else none
        | none => none) := by
    by_cases hsc0 : fm.shadowCode b = 0
    · exact ⟨fun _ => none, fun h => absurd hsc0 h⟩
    · obtain ⟨hlt, _, _, _, shMap, hv_sh, hspec_sh⟩ := hsh_all b hb hsc0
      exact ⟨shMap, fun _ => ⟨hlt, hv_sh, hspec_sh⟩⟩
  obtain ⟨shMap, hsh_fn⟩ := hsh_ex
  -- Step 1: `fastBTreeInsertProg` on `(b, cRole)`
  obtain ⟨hfr1, hr1, hc1, hv_cur_bt', hbt_o1, hbp1, hfm1, hm2_1, _, htr1, hoi1, hof1⟩ :=
    fastBTreeInsertProg_spec (role := cRole) hr₀ hb hcRole_lt hcIns_le (hbt_all b hb).1
      hfp_lt hloc_val
  generalize hs1_def : (Memory.spec 0).clientState s
    (fastBTreeInsertProg ((fl.pBase, (b, cRole)), (fp, loc))) = s1
  rw [hs1_def] at hfr1 hr1 hv_cur_bt' hbt_o1 hbp1 hfm1 hm2_1 htr1 hoi1 hof1
  -- Step 2: `fastWriteBktLaneProg` lane 13 := `curIns b + 1`
  obtain ⟨hfr2, hr2, hbp2, hbt2, htr2, hof2, hoi2⟩ :=
    fastWriteBktLaneProg_frame (b := b) (lane := 13) (val := fm.curIns b + 1) hr1
  obtain ⟨hm2_2, hfm2⟩ := extractFastMeta_writeBktLane (lane := 13) (val := fm.curIns b + 1) hr1 hb
    (Or.inr ⟨by decide, by decide⟩) (Nat.succ_le_of_lt hcIns_lt_N)
  have cw13 := memoryCost_fastWriteBktLaneProg ((fl.pBase, (b, 13)), fm.curIns b + 1) s1
  generalize hs2_def : (Memory.spec 0).clientState s1
    (fastWriteBktLaneProg ((fl.pBase, (b, 13)), fm.curIns b + 1)) = s2
  rw [hs2_def] at hfr2 hr2 hbp2 hbt2 htr2 hof2 hoi2 hm2_2 hfm2
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl] at hfm2
  have hfm_s2 : extractFastMeta fl s2.mem =
      { fm with curIns := Function.update fm.curIns b (fm.curIns b + 1) } := by
    rw [hfm2, hfm1]
  -- Step 3: `drainOldShadowMaintProg`
  have hsh_pre2 : (extractFastMeta fl s2.mem).shadowCode b ≠ 0 →
      (extractFastMeta fl s2.mem).shadowIns b ≤ 8 * slabScale fl.N ^ 12 ∧
      (extractFastMeta fl s2.mem).shadowIns b < fl.N ∧
      ValidWhpSlice fl.N ((extractFastMeta fl s2.mem).shadowIns b)
        (extractBTreeSlice fl.btL b
          (shadowRoleOf ((extractFastMeta fl s2.mem).curRole b)) s2.mem) shMap := by
    rw [hfm_s2]; intro hsc_nz
    have hsi_bnd := (hslack hsc_nz).1
    have hsi_le : fm.shadowIns b ≤ 8 * slabScale fl.N ^ 12 := by
      have h0 : 4 * fm.shadowIns b ≤ 20 * slabScale fl.N ^ 12 :=
        (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hsi_bnd)
      exact Nat.le_of_mul_le_mul_left (h0.trans (by
        have hle : 20 ≤ 4 * 8 := by decide
        exact (Nat.mul_le_mul_right _ hle).trans_eq (by ring))) (by decide)
    have hL_pos : 1 ≤ slabScale fl.N ^ 12 :=
      Nat.one_le_pow _ _ (Nat.one_le_two_pow)
    refine ⟨hsi_le, ?_, ?_⟩
    · dsimp only
      exact lt_of_le_of_lt hsi_le (lt_of_lt_of_le (by linarith only [hL_pos]) h64_L12)
    rw [hbt2 b hb shRole hshRole_lt, hbt_o1 b hb shRole hshRole_lt (Or.inr hsh_ne_c)]
    exact (hsh_fn hsc_nz).2.1
  obtain ⟨hfr3, hr3, hc3, hbp3, htr3, hoi3, hof3, hm2_3, hbt_o3, hsh_post⟩ :=
    drainOldShadowMaintProg_spec (fp := fp) (loc := loc) (cIns' := fm.curIns b + 1)
      (shMap := shMap) hr2 hb (by rw [hfm_s2]; exact hcRole_lt) hfp_lt hloc_val hloc_N hsh_pre2
  generalize hs3_def : (Memory.spec 0).clientState s2
    (drainOldShadowMaintProg (((fl.pBase, b), (fp, loc)), fm.curIns b + 1)) = s3
  rw [hs3_def] at hfr3 hr3 hbp3 htr3 hoi3 hof3 hm2_3 hbt_o3 hsh_post
  -- Step 4: `fastBufDeleteProg` on `oldRole` with `rk`
  have hv_old3 : ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL oldRole) s3.mem) mapOld := by
    rw [htr3 oldRole hold_lt, htr2 oldRole hold_lt, htr1 oldRole hold_lt]; exact hv_old
  obtain ⟨hfr4, hr4, hc4, htr4_old, hv_old4, hbp4, hfm4, hm2_4, _, hbt4, htr4_cur, hoi4, hof4⟩ :=
    fastBufDeleteProg_spec hr3 hold_lt hv_old3 hrk_lt
  generalize hs4_def : (Memory.spec 0).clientState s3
    (fastBufDeleteProg ((fl.pBase, oldRole), rk)) = s4
  rw [hs4_def] at hfr4 hr4 htr4_old hv_old4 hbp4 hfm4 hm2_4 hbt4 htr4_cur hoi4 hof4
  -- Step 5: `fastWriteMetaProg ((fl.pBase, 5), fm.drainPos + 1)`
  obtain ⟨hfr5, hr5, hbp5, hbt5, htr5, hoi5, hof5, hm2_5, hfm5⟩ :=
    extractFastMeta_writeMeta (off := 5) (val := fm.drainPos + 1) hr4
      (Or.inl ⟨by decide, by decide⟩)
  have cw5 := memoryCost_fastWriteMetaProg ((fl.pBase, 5), fm.drainPos + 1) s4
  generalize hs5_def : (Memory.spec 0).clientState s4
    (fastWriteMetaProg ((fl.pBase, 5), fm.drainPos + 1)) = s5
  rw [hs5_def] at hfr5 hr5 hbp5 hbt5 htr5 hoi5 hof5 hm2_5 hfm5
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl] at hfm5
  -- Stitch execution path & cost
  have htot_st_c : (Memory.spec 0).clientState s
      (drainOldInsertNoCollProg (((fl.pBase, oldRole), (fm.drainPos, rk)), (b, (fp, loc)))) = s5 ∧
      memoryCost (drainOldInsertNoCollProg
        (((fl.pBase, oldRole), (fm.drainPos, rk)), (b, (fp, loc)))) s ≤
        400 + 2 * cTabWhp fl.c + 144 * hMaxBTree := by
    unfold drainOldInsertNoCollProg; dsimp only
    have c12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s
    have c13 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 13)) s
    have hr0_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 0)) = s := rfl
    have hr0_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 0)) = fl.N :=
      hpt 0 (by decide)
    have hr23_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s := rfl
    have hr23_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 23)) =
        qEpochWhp fl.N := hpt 23 (by decide)
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadBktLaneProg, hcr_r,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadBktLaneProg, hci_r,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      hr0_st, hr0_r, prog_memoryCost_read,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      hr23_st, hr23_r, prog_memoryCost_read,
      ite_eq_left ⟨hcIns_lt_N, hdp_lt_Q⟩,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs2_def,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs3_def,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs4_def, hs5_def]
    exact ⟨rfl, by linarith only [c12, c13, hc1, cw13, hc3, hc4, cw5]⟩
  -- Shared frame equalities across s → s5
  have hbp_s5 : extractBlockPool fl.mp s5.mem = bp :=
    hbp5.trans (hbp4.trans (hbp3.trans (hbp2.trans hbp1)))
  have htr_old_s3 : extractBufTrie (fl.trieL oldRole) s3.mem =
      extractBufTrie (fl.trieL oldRole) s.mem :=
    (htr3 oldRole hold_lt).trans ((htr2 oldRole hold_lt).trans (htr1 oldRole hold_lt))
  have htr_cur_s5 : extractBufTrie (fl.trieL fm.curBufRole) s5.mem =
      extractBufTrie (fl.trieL fm.curBufRole) s.mem := by
    rw [htr5 fm.curBufRole hinv.role_lt, ← hrole_swap, htr4_cur, hrole_swap]
    exact (htr3 _ hinv.role_lt).trans ((htr2 _ hinv.role_lt).trans (htr1 _ hinv.role_lt))
  have htr_old_s5 : extractBufTrie (fl.trieL oldRole) s5.mem =
      bufDelete (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL oldRole) s.mem) rk := by
    rw [htr5 oldRole hold_lt, htr4_old, htr_old_s3]
  have hoi_s5 : ∀ a, fl.io.OwnsAddr a → s5.mem a = s.mem a := fun a ha =>
    (hoi5 a ha).trans ((hoi4 a ha).trans ((hoi3 a ha).trans ((hoi2 a ha).trans (hoi1 a ha))))
  have hof_s5 : ∀ a, ¬fl.OwnsFastAddr a → s5.mem a = s.mem a := fun a ha =>
    (hof5 a ha).trans ((hof4 a ha).trans ((hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha))))
  have hm2_s5 : s5.mem (fl.metaBase + 2) = 0 :=
    hm2_5.trans (hm2_4.trans (hm2_3.trans (hm2_2.trans (hm2_1.trans hinv.mode_zero))))
  have hkey_eq : ∀ b' loc', b' < numBucketsWhp fl.N → loc' < bp.bktCount b' →
      fastKeyAt fl seeds.bkt s5.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' :=
    fun b' loc' hb' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp_s5 hoi_s5 hb' hl'
  -- Compute exact `extractFastMeta fl s3.mem` fields
  have hfm_s3_fields :
      let fm3 := extractFastMeta fl s3.mem
      fm3.curBufRole = fm.curBufRole ∧ fm3.subStep = fm.subStep ∧
      fm3.drainPos = fm.drainPos ∧ fm3.tryAct = 0 ∧ fm3.tryBkt = fm.tryBkt ∧
      fm3.trySalt = fm.trySalt ∧ fm3.tryPos = fm.tryPos ∧ fm3.tryIns = fm.tryIns ∧
      fm3.bktSalt = fm.bktSalt ∧ fm3.curRole = fm.curRole ∧
      fm3.curIns = Function.update fm.curIns b (fm.curIns b + 1) ∧
      (∀ b' ≠ b, fm3.shadowIns b' = fm.shadowIns b' ∧ fm3.shadowCode b' = fm.shadowCode b') ∧
      (if fm.shadowCode b = 0 then
        if 6 * slabScale fl.N ^ 12 ≤ fm.curIns b + 1 then
          fm3.shadowIns b = 0 ∧ fm3.shadowCode b = 1
        else fm3.shadowIns b = fm.shadowIns b ∧ fm3.shadowCode b = 0
      else if loc + 1 < fm.shadowCode b then
        fm3.shadowIns b = fm.shadowIns b + 1 ∧ fm3.shadowCode b = fm.shadowCode b
      else fm3.shadowIns b = fm.shadowIns b ∧ fm3.shadowCode b = fm.shadowCode b) := by
    dsimp only at hsh_post ⊢
    rw [hfm_s2] at hsh_post
    by_cases hsc0 : fm.shadowCode b = 0
    · rw [ite_eq_left hsc0] at hsh_post ⊢
      by_cases hthr : 6 * slabScale fl.N ^ 12 ≤ fm.curIns b + 1
      · rw [ite_eq_left hthr] at hsh_post ⊢
        rw [hsh_post.1]; dsimp only
        exact ⟨rfl, rfl, rfl, hta0, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          fun b' hne => ⟨Function.update_of_ne hne .., Function.update_of_ne hne ..⟩,
          Function.update_self .., Function.update_self ..⟩
      · rw [ite_eq_right hthr] at hsh_post ⊢
        rw [hsh_post, hfm_s2]
        exact ⟨rfl, rfl, rfl, hta0, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          fun _ _ => ⟨rfl, rfl⟩, rfl, hsc0⟩
    · rw [ite_eq_right hsc0] at hsh_post ⊢
      by_cases hls : loc + 1 < fm.shadowCode b
      · rw [ite_eq_left hls] at hsh_post ⊢
        rw [hsh_post.1]; dsimp only
        exact ⟨rfl, rfl, rfl, hta0, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          fun b' hne => ⟨Function.update_of_ne hne .., rfl⟩, Function.update_self .., rfl⟩
      · rw [ite_eq_right hls] at hsh_post ⊢
        rw [hsh_post, hfm_s2]
        exact ⟨rfl, rfl, rfl, hta0, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  obtain ⟨e_cr, e_ss, e_dp, e_ta, _, _, _, _, e_bs, e_rl, e_ci, e_ne, e_sh_b⟩ := hfm_s3_fields
  have hcr5 : (extractFastMeta fl s5.mem).curBufRole = fm.curBufRole := by rw [hfm5, hfm4, e_cr]
  have hss5 : (extractFastMeta fl s5.mem).subStep = fm.subStep := by rw [hfm5, hfm4, e_ss]
  have hdp5 : (extractFastMeta fl s5.mem).drainPos = fm.drainPos + 1 := by rw [hfm5]
  have hta5 : (extractFastMeta fl s5.mem).tryAct = 0 := by rw [hfm5, hfm4, e_ta]
  have hbs5 : (extractFastMeta fl s5.mem).bktSalt = fm.bktSalt := by rw [hfm5, hfm4, e_bs]
  have hrl5 : (extractFastMeta fl s5.mem).curRole = fm.curRole := by rw [hfm5, hfm4, e_rl]
  have hci5 : (extractFastMeta fl s5.mem).curIns =
      Function.update fm.curIns b (fm.curIns b + 1) := by rw [hfm5, hfm4, e_ci]
  have hsi5_eq : (extractFastMeta fl s5.mem).shadowIns = (extractFastMeta fl s3.mem).shadowIns := by
    rw [hfm5, hfm4]
  have hsc5_eq :
      (extractFastMeta fl s5.mem).shadowCode = (extractFastMeta fl s3.mem).shadowCode := by
    rw [hfm5, hfm4]
  have hbm5 : ∀ b' < numBucketsWhp fl.N,
      let fm2 := extractFastMeta fl s5.mem
      fm2.bktSalt b' < sMaxWhp fl.c fl.N ∧ fm2.curRole b' < 3 ∧
      fm2.curIns b' ≤ 8 * slabScale fl.N ^ 12 ∧
      (fm2.shadowCode b' = 0 → ¬(fm2.tryAct = 1 ∧ fm2.tryBkt = b') →
        fm2.curIns b' < 6 * slabScale fl.N ^ 12) := fun b' hb' => by
    dsimp only
    refine ⟨by rw [congrFun hbs5 b']; exact (hinv.bkt_meta_bounds b' hb').1,
      by rw [congrFun hrl5 b']; exact (hinv.bkt_meta_bounds b' hb').2.1, ?_, fun hsc0' _ => ?_⟩
    · by_cases hbb : b' = b
      · subst hbb; rw [congrFun hci5 b', Function.update_self]; omega
      · rw [congrFun hci5 b', Function.update_of_ne hbb]; exact (hinv.bkt_meta_bounds b' hb').2.2.1
    · by_cases hbb : b' = b
      · subst hbb; rw [congrFun hci5 b', Function.update_self]
        rw [congrFun hsc5_eq b'] at hsc0'
        by_cases hsc0 : fm.shadowCode b' = 0
        · rw [ite_eq_left hsc0] at e_sh_b
          by_cases hthr : 6 * slabScale fl.N ^ 12 ≤ fm.curIns b' + 1
          · rw [ite_eq_left hthr] at e_sh_b; rw [e_sh_b.2] at hsc0'; cases hsc0'
          · exact Nat.lt_of_not_le hthr
        · rw [ite_eq_right hsc0] at e_sh_b
          split_ifs at e_sh_b <;> exact absurd (hsc0'.symm.trans e_sh_b.2).symm hsc0
      · rw [congrFun hci5 b', Function.update_of_ne hbb]
        rw [congrFun hsc5_eq b', (e_ne b' hbb).2] at hsc0'
        exact (hinv.bkt_meta_bounds b' hb').2.2.2 hsc0' (fun ⟨h1, _⟩ =>
          absurd (hta0.symm.trans h1) Nat.zero_ne_one)
  have hbt_s5_c : ∀ b' < numBucketsWhp fl.N, ∀ r' < 3, (b' ≠ b ∨ r' ≠ shRole) →
      extractBTreeSlice fl.btL b' r' s5.mem = extractBTreeSlice fl.btL b' r' s2.mem := by
    intro b' hb' r' hr' hne
    have hs54 := hbt5 b' hb' r' hr'
    have hs43 := hbt4 b' hb' r' hr'
    have hsh3 : shadowRoleOf ((extractFastMeta fl s2.mem).curRole b) = shRole := by
      rw [hfm_s2]
    have hs32 := hbt_o3 b' hb' r' hr' (hsh3 ▸ hne)
    exact hs54.trans (hs43.trans hs32)
  have hdel := hv_old.delete_spec hrk_lt
  have hupd_old : ∀ x, Function.update mapOld rk none x =
      if x = rk then none else mapOld x := fun x => by
    by_cases h : x = rk <;> simp [h]
  obtain ⟨hc_N, hc_sb, hc_sf, hc_bp, hc_cap, hc_ref⟩ :=
    FastEpochInvGen.fixed_pool_core hv hinv hbp_s5 hoi_s5 hof_s5
  rw [htot_st_c.1]
  refine ⟨hfr5.trans (hfr4.trans (hfr3.trans (hfr2.trans hfr1))), htot_st_c.2, ?_,
    hbp_s5, htr_cur_s5, htr_old_s5, hoi_s5, hof_s5, hcr5, hss5, hdp5, hta5, hbs5,
    fun b' hne => ⟨congrFun hrl5 b', by rw [congrFun hci5 b', Function.update_of_ne hne],
      by rw [congrFun hsi5_eq b', (e_ne b' hne).1],
      by rw [congrFun hsc5_eq b', (e_ne b' hne).2]⟩⟩
  refine
    { param_table := hr5.2.1
      hdr_N := hc_N
      mode_zero := hm2_s5
      seed_bkt := hc_sb
      seed_fp := hc_sf
      bp_inv := hc_bp
      bkt_le_capMax := hc_cap
      refines := hc_ref
      role_lt := by rw [hcr5]; exact hinv.role_lt
      subStep_lt := by rw [hss5]; exact hinv.subStep_lt
      bkt_meta_bounds := hbm5
      tiers := ?_ }
  dsimp only
  set mapOld' := Function.update mapOld rk none
  set mapBTree' := Function.update mapBTree b (Function.update (mapBTree b) fp (some loc))
  refine ⟨mapCur, mapOld', mapBTree',
    by rw [hcr5, htr_cur_s5]; exact hv_cur,
    by rw [hcr5, htr_cur_s5]; exact hrb_cur,
    by rw [hcr5, htr_cur_s5]; exact hrc_cur,
    by rw [hcr5, htr_cur_s5, hss5]; exact hia_cur,
    by rw [hcr5, htr_cur_s5]; exact hna_cur,
    fun rk' b' loc' hm => by
      obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk' b' loc' hm
      exact ⟨hb', by rw [hbp_s5]; exact hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩,
    ?_, ?_, ?_, ?_, by rw [hta5]; decide, fun h01 => by rw [hta5] at h01; cases h01⟩
  · rw [hss5, hcr5, htr_old_s5, hdp5, hbp_s5, ite_eq_left hsub]
    refine ⟨hdel.1, hrb_old.delete _ _ _, hrc_old.delete _ _ _,
      hdel.2.2.1.symm ▸ hia_old, hdel.2.1.symm ▸ hna_old, by omega, ?_,
      fun rk' b' loc' hm => ?_⟩
    · intro id hid
      rw [hdel.2.2.1] at hid
      have hid_dp : id ≤ fm.drainPos := Nat.le_of_lt_succ (lt_of_lt_of_le hid (min_le_left _ _))
      rcases Nat.eq_or_lt_of_le hid_dp with rfl | hlt
      · exact bufCheckSlot_bufDelete_self_none (hrk_eq ▸ hwalk_dp)
      · exact hdel.2.2.2.2 id (hscan_old id (lt_min hlt (hlt.trans hdp_lt_ia)))
    · by_cases heq : rk' = rk
      · subst heq; simp [mapOld'] at hm
      · simp only [mapOld', Function.update_of_ne heq] at hm
        obtain ⟨hn', hb', hl', u', hrk', hk'⟩ := hold_snd rk' b' loc' hm
        exact ⟨hn', hb', hl', u', hrk', (hkey_eq b' loc' hb' hl').trans hk'⟩
  · intro b' hb'
    rw [hbp_s5]
    refine ⟨?_, fun fp' loc' hm => ?_⟩
    · by_cases hbb : b' = b
      · subst hbb
        rw [congrFun hci5 b', Function.update_self, congrFun hrl5 b']
        change ValidWhpSlice fl.N (fm.curIns b' + 1)
          (extractBTreeSlice fl.btL b' cRole s5.mem) (mapBTree' b')
        rw [hbt_s5_c b' hb' cRole hcRole_lt (Or.inr hsh_ne_c.symm),
          hbt2 b' hb' cRole hcRole_lt]
        simp only [mapBTree', Function.update_self]
        exact hv_cur_bt'
      · rw [congrFun hci5 b', Function.update_of_ne hbb, congrFun hrl5 b']
        have hr_b' := (hinv.bkt_meta_bounds b' hb').2.1
        rw [hbt_s5_c b' hb' _ hr_b' (Or.inl hbb), hbt2 b' hb' _ hr_b',
          hbt_o1 b' hb' _ hr_b' (Or.inl hbb)]
        simp only [mapBTree', Function.update_of_ne hbb]
        exact (hbt_all b' hb').1
    · by_cases hbb : b' = b
      · subst hbb
        simp only [mapBTree', Function.update_self] at hm
        by_cases hfp_eq : fp' = fp
        · subst hfp_eq
          simp only [Function.update_self, Option.some.injEq] at hm
          subst hm
          exact ⟨hloc_lt, u,
            congrArg Fin.val (fpHash_congr_salt (congrFun hbs5 b') u),
            (hkey_eq b' loc hb' hloc_lt).trans hu_key,
            (fun b₁ l₁ hm₁ => by
              change mapCur rk = some (b₁, l₁) at hm₁
              rw [hrk_eq, hcur_none] at hm₁; exact nomatch hm₁),
            (fun b₂ l₂ hm₂ => by
              change mapOld' rk = some (b₂, l₂) at hm₂
              simp [mapOld'] at hm₂)⟩
        · simp only [Function.update_of_ne hfp_eq] at hm
          obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
          exact ⟨hl', u',
            (congrArg Fin.val (fpHash_congr_salt (congrFun hbs5 b') u')).trans hfp',
            (hkey_eq b' loc' hb' hl').trans hk',
            fun b₁ l₁ hm₁ => by
              obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
              rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
            fun b₂ l₂ hm₂ => by
              by_cases hrk' : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
              · rw [hrk'] at hm₂; simp [mapOld'] at hm₂
              · simp only [mapOld', Function.update_of_ne hrk'] at hm₂
                obtain ⟨_, hb₂, hl₂, _⟩ := hold_snd _ b₂ l₂ hm₂
                rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
      · simp only [mapBTree', Function.update_of_ne hbb] at hm
        obtain ⟨hl', u', hfp', hk', hd1, hd2⟩ := (hbt_all b' hb').2 fp' loc' hm
        exact ⟨hl', u',
          (congrArg Fin.val (fpHash_congr_salt (congrFun hbs5 b') u')).trans hfp',
          (hkey_eq b' loc' hb' hl').trans hk',
          fun b₁ l₁ hm₁ => by
            obtain ⟨hb₁, hl₁, _⟩ := hcur_snd _ b₁ l₁ hm₁
            rw [hkey_eq b₁ l₁ hb₁ hl₁]; exact hd1 b₁ l₁ hm₁,
          fun b₂ l₂ hm₂ => by
            by_cases hrk' : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
            · rw [hrk'] at hm₂; simp [mapOld'] at hm₂
            · simp only [mapOld', Function.update_of_ne hrk'] at hm₂
              obtain ⟨_, hb₂, hl₂, _⟩ := hold_snd _ b₂ l₂ hm₂
              rw [hkey_eq b₂ l₂ hb₂ hl₂]; exact hd2 b₂ l₂ hm₂⟩
  · intro b' hb' loc' hloc'
    rw [hbp_s5] at hloc'
    obtain ⟨u', hk', ht'⟩ := hcomp b' hb' loc' hloc'
    refine ⟨u', (hkey_eq b' loc' hb' hloc').trans hk', ?_⟩
    rcases ht' with h1 | h2 | h3
    · exact Or.inl h1
    · by_cases hrk' : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
      · rw [hrk', hrk_eq, hmo_dp, Option.some.injEq, Prod.mk.injEq] at h2
        rcases h2 with ⟨rfl, rfl⟩
        have hu'_eq : u' = u := Fin.ext (hk'.symm.trans hu_key)
        right; right
        simp only [mapBTree', Function.update_self]
        rw [hu'_eq, fpHash_congr_salt (congrFun hbs5 b) u]
        exact Function.update_self ..
      · exact Or.inr (Or.inl (by simp only [mapOld', Function.update_of_ne hrk']; exact h2))
    · right; right
      rw [fpHash_congr_salt (congrFun hbs5 b') u']
      · by_cases hbb : b' = b
        · subst hbb
          simp only [mapBTree', Function.update_self]
          by_cases hfp_eq : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm.bktSalt b', hbs_lt⟩ u').val = fp
          · rw [hfp_eq] at h3; rw [hmb_none] at h3; cases h3
          · rw [Function.update_of_ne hfp_eq]; exact h3
        · simp only [mapBTree', Function.update_of_ne hbb]; exact h3
  · intro b' hb' hsc_nz
    by_cases hbb : b' = b
    · subst hbb
      rw [congrFun hsc5_eq b'] at hsc_nz
      rw [hta5, hbp_s5, congrFun hrl5 b', congrFun hci5 b', Function.update_self,
        congrFun hsi5_eq b', congrFun hsc5_eq b']
      dsimp only at hsh_post
      rw [hfm_s2] at hsh_post
      by_cases hsc0 : fm.shadowCode b' = 0
      · rw [ite_eq_left hsc0] at hsh_post e_sh_b
        by_cases hthr : 6 * slabScale fl.N ^ 12 ≤ fm.curIns b' + 1
        · rw [ite_eq_left hthr] at hsh_post e_sh_b
          have hlt6 : fm.curIns b' < 6 * slabScale fl.N ^ 12 :=
            (hinv.bkt_meta_bounds b' hb').2.2.2 hsc0 (fun ⟨h1, _⟩ =>
              absurd (hta0.symm.trans h1) Nat.zero_ne_one)
          have hcnt_pos : 0 < bp.bktCount b' := Nat.zero_lt_of_lt hloc_lt
          have hcnt4 : bp.bktCount b' ≤ 4 * slabScale fl.N ^ 12 := hcnt_le
          have hci_sub : fm.curIns b' + 1 - 6 * slabScale fl.N ^ 12 = 0 := by omega
          rw [e_sh_b.1, e_sh_b.2]
          refine ⟨by simpa using hcnt_pos, by simp,
            by simpa using (Nat.mul_le_mul_left 5 hcnt4).trans_eq (by ring),
            by simp only [hci_sub, Nat.sub_self, Nat.sub_zero, Nat.mul_zero, Nat.zero_add]
               exact hcnt4,
            fun _ => none, ?_, fun fp' => ?_⟩
          · rw [hbt5 b' hb' shRole hshRole_lt, hbt4 b' hb' shRole hshRole_lt]
            exact hsh_post.2
          · cases h : mapBTree' b' fp' with
            | none => rfl
            | some l => simp
        · rw [ite_eq_right hthr] at e_sh_b
          exact absurd e_sh_b.2 hsc_nz
      · rw [ite_eq_right hsc0] at hsh_post e_sh_b
        obtain ⟨hsp_lt, hv_sh, hspec_sh⟩ := hsh_fn hsc0
        obtain ⟨hsl1, hsl2⟩ := hslack hsc0
        by_cases hls : loc + 1 < fm.shadowCode b'
        · rw [ite_eq_left hls] at hsh_post e_sh_b
          rw [e_sh_b.1, e_sh_b.2]
          refine ⟨hsp_lt, by simp, by omega, by omega,
            Function.update shMap fp (some loc), ?_, fun fp' => ?_⟩
          · rw [hbt5 b' hb' shRole hshRole_lt, hbt4 b' hb' shRole hshRole_lt]
            exact hsh_post.2
          · by_cases hfp_eq : fp' = fp
            · subst hfp_eq
              simp only [Function.update_self, mapBTree', show loc < fm.shadowCode b' - 1 by omega,
                ↓reduceIte]
            · simp only [Function.update_of_ne hfp_eq, mapBTree', Function.update_self]
              exact hspec_sh fp'
        · rw [ite_eq_right hls] at hsh_post e_sh_b
          rw [e_sh_b.1, e_sh_b.2]
          refine ⟨hsp_lt, by simp, by omega, by omega, shMap, ?_, fun fp' => ?_⟩
          · rw [hbt5 b' hb' shRole hshRole_lt, hbt4 b' hb' shRole hshRole_lt,
              hsh_post, hbt2 b' hb' shRole hshRole_lt,
              hbt_o1 b' hb' shRole hshRole_lt (Or.inr hsh_ne_c)]
            exact hv_sh
          · by_cases hfp_eq : fp' = fp
            · subst hfp_eq
              simp only [mapBTree', Function.update_self]
              rw [hspec_sh fp, hmb_none]
              have hnot_lt : ¬(loc < fm.shadowCode b' - 1) := by omega
              rw [ite_eq_right hnot_lt]
            · simp only [mapBTree', Function.update_self, Function.update_of_ne hfp_eq]
              exact hspec_sh fp'
    · rw [congrFun hsc5_eq b', (e_ne b' hbb).2] at hsc_nz
      rw [hta5, hbp_s5, congrFun hrl5 b', congrFun hci5 b', Function.update_of_ne hbb,
        congrFun hsi5_eq b', (e_ne b' hbb).1, congrFun hsc5_eq b', (e_ne b' hbb).2]
      obtain ⟨h1, _, h3, h4, sm', hv_sm', heq_sm'⟩ := hsh_all b' hb' hsc_nz
      have hr_sm := (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
      refine ⟨h1, by simp, h3, h4, sm', ?_, fun fp' => ?_⟩
      · rw [hbt_s5_c b' hb' _ hr_sm (Or.inl hbb), hbt2 b' hb' _ hr_sm,
          hbt_o1 b' hb' _ hr_sm (Or.inl hbb)]
        exact hv_sm'
      · simp only [mapBTree', Function.update_of_ne hbb]; exact heq_sm' fp'

/-- Complete unconditional specification of `drainOldSlotProg`: preserves `FastEpochInvGen` on
**100%** of hash seeds whenever `subStep < Q / 2` and `tryAct = 0`, in `O_c(1)` instructions,
with an exact 4-way classification of the outcome:
1. `ia ≤ drainPos`: pure no-op (`s' = s`);
2. Inactive slot (`bufCheckSlot oldTr dp = none`): advances `drainPos := dp + 1`;
3. Active non-colliding slot `some (b, loc)`: inserts into `BTree(b, curRole b)`, deletes from
   `BufOld`, advances `drainPos := dp + 1`;
4. Active colliding slot `some (b, loc)`: gives a genuine distinct-key collision witness `(u, v)`
   under `fm.bktSalt b`, either stalling on active shadow compaction (`s' = fastShadowSteps8Prog s`,
   `shadowCode' b ≠ 0`) or starting salt search (`tryAct' = 1, tryBkt' = b, trySalt' = 0`).
-/
theorem drainOldSlotProg_spec {slackCur : ℕ} {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl slack seeds s.mem s_abs)
    (hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2)
    (hta0 : (extractFastMeta fl s.mem).tryAct = 0) :
    let s' := (Memory.spec 0).clientState s (drainOldSlotProg fl.pBase)
    let fm := extractFastMeta fl s.mem
    let fm' := extractFastMeta fl s'.mem
    let bp := extractBlockPool fl.mp s.mem
    let oldRole := 1 - fm.curBufRole
    let oldTr := extractBufTrie (fl.trieL oldRole) s.mem
    s'.frontier = s.frontier ∧
    memoryCost (drainOldSlotProg fl.pBase) s ≤
      3600 + 36 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 2 * cTabWhp fl.c + 780 * hMaxBTree ∧
    FastEpochInvGen slackCur fl slack seeds s'.mem s_abs ∧
    extractBlockPool fl.mp s'.mem = bp ∧
    extractBufTrie (fl.trieL fm.curBufRole) s'.mem =
      extractBufTrie (fl.trieL fm.curBufRole) s.mem ∧
    (∀ addr, fl.io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    fm'.bktSalt = fm.bktSalt ∧
    (oldTr.itemAlloc ≤ fm.drainPos → s' = s) ∧
    (fm.drainPos < oldTr.itemAlloc →
      -- Case 1: already-inactive slot (`none`) → `drainPos + 1`
      (bufCheckSlot oldTr fm.drainPos = none ∧
        fm'.drainPos = fm.drainPos + 1 ∧ fm'.tryAct = 0 ∧
        extractBufTrie (fl.trieL oldRole) s'.mem = oldTr ∧
        fm'.shadowCode = fm.shadowCode ∧ fm'.shadowIns = fm.shadowIns ∧
        fm'.curIns = fm.curIns ∧ fm'.curRole = fm.curRole) ∨
      -- Case 2: active slot `some (b, loc)` drained cleanly (`mapBTree b fp = none`)
      (∃ (b loc : ℕ) (u : Fin fl.U),
        b < numBucketsWhp fl.N ∧ loc < bp.bktCount b ∧
        bufCheckSlot oldTr fm.drainPos = some (b, loc) ∧
        fastKeyAt fl seeds.bkt s.mem b loc = u.val ∧
        fm'.drainPos = fm.drainPos + 1 ∧ fm'.tryAct = 0 ∧
        extractBufTrie (fl.trieL oldRole) s'.mem =
          bufDelete (cTabWhp fl.c) (bCharWhp fl.N) oldTr (rKeyOf fl.c fl.U fl.N seeds.fp u) ∧
        (∀ b' ≠ b, fm'.curRole b' = fm.curRole b' ∧ fm'.curIns b' = fm.curIns b' ∧
          fm'.shadowIns b' = fm.shadowIns b' ∧ fm'.shadowCode b' = fm.shadowCode b')) ∨
      -- Case 3: colliding slot stalled on `shadowCode b ≠ 0` after 8 shadow steps
      (∃ (b loc : ℕ) (hb : b < numBucketsWhp fl.N) (u v : Fin fl.U),
        bufCheckSlot oldTr fm.drainPos = some (b, loc) ∧
        fastKeyAt fl seeds.bkt s.mem b loc = u.val ∧
        u ≠ v ∧ s_abs u ≠ none ∧ s_abs v ≠ none ∧
        epochBucket fl.c fl.U fl.N seeds.bkt u = b ∧
        epochBucket fl.c fl.U fl.N seeds.bkt v = b ∧
        fpHash fl.c fl.U fl.N seeds.fp
          ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ u =
          fpHash fl.c fl.U fl.N seeds.fp
            ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ v ∧
        s' = (Memory.spec 0).clientState s (fastShadowSteps8Prog (fl.pBase, b)) ∧
        fm'.shadowCode b ≠ 0 ∧ fm'.tryAct = 0 ∧ fm'.drainPos = fm.drainPos ∧
        extractBufTrie (fl.trieL oldRole) s'.mem = oldTr ∧
        (∀ b' ≠ b, fm'.curRole b' = fm.curRole b' ∧ fm'.curIns b' = fm.curIns b' ∧
          fm'.shadowIns b' = fm.shadowIns b' ∧ fm'.shadowCode b' = fm.shadowCode b')) ∨
      -- Case 4: colliding slot started candidate salt search (`tryAct := 1, tryBkt := b`)
      (∃ (b loc : ℕ) (hb : b < numBucketsWhp fl.N) (u v : Fin fl.U),
        bufCheckSlot oldTr fm.drainPos = some (b, loc) ∧
        fastKeyAt fl seeds.bkt s.mem b loc = u.val ∧
        u ≠ v ∧ s_abs u ≠ none ∧ s_abs v ≠ none ∧
        epochBucket fl.c fl.U fl.N seeds.bkt u = b ∧
        epochBucket fl.c fl.U fl.N seeds.bkt v = b ∧
        fpHash fl.c fl.U fl.N seeds.fp
          ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ u =
          fpHash fl.c fl.U fl.N seeds.fp
            ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ v ∧
        fm'.tryAct = 1 ∧ fm'.tryBkt = b ∧ fm'.trySalt = 0 ∧
        fm'.tryPos = 0 ∧ fm'.tryIns = 0 ∧ fm'.drainPos = fm.drainPos ∧
        fm'.shadowCode b = 0 ∧
        extractBufTrie (fl.trieL oldRole) s'.mem = oldTr ∧
        (fm.shadowCode b = 0 →
          (Memory.spec 0).clientResult s (fastBTreeLookupProg
            ((fl.pBase, (b, fm.curRole b)),
              (fpHash fl.c fl.U fl.N seeds.fp
                ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ u).val)) ≠ (0, 0)))) := by
  dsimp only
  have hr₀ := hinv.ready hv rfl
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  set bp := extractBlockPool fl.mp s.mem
  set oldRole := 1 - fm.curBufRole
  have hold_lt : oldRole < 2 := by have := hinv.role_lt; omega
  have hm3_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 3)) =
      fm.curBufRole := clientResult_fastReadMetaProg hpt (by decide)
  have hm5_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 5)) =
      fm.drainPos := clientResult_fastReadMetaProg hpt (by decide)
  have hr23_st : (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s := rfl
  have hr23_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 23)) =
      qEpochWhp fl.N := hpt 23 (by decide)
  have cm3 := memoryCost_fastReadMetaProg (fl.pBase, 3) s
  have cm5 := memoryCost_fastReadMetaProg (fl.pBase, 5) s
  obtain ⟨hia_r, hia_c⟩ := fastBufItemAllocProg_spec hr₀ hold_lt
  obtain ⟨mapCur, mapOld, mapBTree, hv_cur, _, _, _, _, _, hold_half, _, _, _, _, _⟩ := hinv.tiers
  rw [ite_eq_left hsub] at hold_half
  obtain ⟨hv_old, _, _, hia_old, _, _, _, hold_snd⟩ := hold_half
  by_cases hdp_lt : fm.drainPos < (extractBufTrie (fl.trieL oldRole) s.mem).itemAlloc
  · obtain ⟨hcs_r, hcs_c⟩ := fastBufCheckSlotProg_spec hr₀ hold_lt hia_old (id := fm.drainPos)
    cases hchk : bufCheckSlot (extractBufTrie (fl.trieL oldRole) s.mem) fm.drainPos with
    | none =>
      have hst_eq : (Memory.spec 0).clientState s (drainOldSlotProg fl.pBase) =
          (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, 5), fm.drainPos + 1)) ∧
          memoryCost (drainOldSlotProg fl.pBase) s ≤ 50 := by
        unfold drainOldSlotProg; dsimp only
        have cw5 := memoryCost_fastWriteMetaProg ((fl.pBase, 5), fm.drainPos + 1) s
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hm3_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hm5_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          hr23_st, hr23_r, prog_memoryCost_read, ite_eq_left hinv.role_lt,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          StateTransitionSpec.clientState_pure, prog_clientResult_pure, memoryCost_pure,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastBufItemAllocProg, hia_r, ite_eq_left ⟨hia_old, hdp_lt⟩,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastBufCheckSlotProg, hcs_r, hchk, ite_eq_left rfl]
        exact ⟨rfl, by linarith only [cm3, cm5, hia_c, hcs_c, cw5]⟩
      obtain ⟨hfr', hinv', hbp', htr', hoi', hof', hfm'⟩ :=
        drainOldSlot_inactive_inv hv hinv hsub hdp_lt hchk
      rw [hst_eq.1]
      have hc_le : memoryCost (drainOldSlotProg fl.pBase) s ≤
          3600 + 36 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 2 * cTabWhp fl.c + 780 * hMaxBTree :=
        hst_eq.2.trans (by omega)
      exact ⟨hfr', hc_le, hinv', hbp', htr' fm.curBufRole hinv.role_lt, hoi', hof',
        by rw [hfm'], by rw [hfm'], by rw [hfm'],
        fun hle => absurd hdp_lt (Nat.not_lt.mpr hle),
        fun _ => Or.inl ⟨rfl, by rw [hfm'], by rw [hfm']; exact hta0, htr' oldRole hold_lt,
          by rw [hfm'], by rw [hfm'], by rw [hfm'], by rw [hfm']⟩⟩
    | some bl =>
      rcases bl with ⟨b, loc⟩
      obtain ⟨_, rk_dp, hrk_dp_lt, _, hmo_dp⟩ := hv_old.checkSlot_some hchk
      obtain ⟨_, hb, hloc_lt, u, hrk_u, hu_key⟩ := hold_snd rk_dp b loc hmo_dp
      -- Step 1: `fastShadowSteps8Prog (fl.pBase, b)`
      obtain ⟨hfr1, hc1, hinv1, hbp1, hcr1, hss1, hdp1, hta1, _, _, _, _, hbs1, htr1, hoi1, hof1,
        hne1, hslack1⟩ := fastShadowSteps8Prog_spec (b := b) hv hinv
      generalize hs1_def : (Memory.spec 0).clientState s
        (fastShadowSteps8Prog (fl.pBase, b)) = s1
      rw [hs1_def] at hfr1 hinv1 hbp1 hcr1 hss1 hdp1 hta1 hbs1 htr1 hoi1 hof1 hne1 hslack1
      have hv1 : fl.Valid w s1.frontier := hfr1.symm ▸ hv
      have hr1 := hinv1.ready hv1 rfl
      have hpt1 := hinv1.param_table
      set fm1 := extractFastMeta fl s1.mem
      have hsub1 : fm1.subStep < qEpochWhp fl.N / 2 := hss1.symm ▸ hsub
      have hta1_0 : fm1.tryAct = 0 := hta1.trans hta0
      have hkey1 : fastKeyAt fl seeds.bkt s1.mem b loc = u.val :=
        (fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb hloc_lt).trans hu_key
      have hchk1 : bufCheckSlot (extractBufTrie (fl.trieL (1 - fm1.curBufRole)) s1.mem)
          fm1.drainPos = some (b, loc) := by
        rw [hcr1, hdp1, htr1 oldRole hold_lt]; exact hchk
      have hloc1 : loc < (extractBlockPool fl.mp s1.mem).bktCount b := hbp1.symm ▸ hloc_lt
      have hcnt1_r := fastReadBktCntProg_spec hr1 hinv1.bp_inv.1.core hb
      obtain ⟨hrd_s, hrd_r, hrd_c⟩ := fastBpReadAtProg_spec hr1 hinv1.bp_inv hb hloc1
      obtain ⟨u_s, v_s, hu_s, _, hb_u, hq_u, hs_u⟩ := hinv1.bktSlot_refines hb hloc1
      have hu_eq : u_s = u := Fin.ext (hu_s.trans hkey1)
      rw [hu_eq] at hb_u hq_u hs_u
      have hq_lt : (bpPairAt fl.bpL s1.mem b loc).1 < 2 ^ quotBitsWhp fl.U fl.N :=
        hq_u ▸ keyQuotient_bWhp_lt hv1.N_le_U u
      obtain ⟨hrec_r, hrec_c⟩ := fastFeistelReconProg_spec hr1 hq_lt hinv1.seed_bkt (bkt := b)
      have hu_rec : (Memory.spec 0).clientResult s1
          (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s1.mem b loc).1))) = u.val :=
        hrec_r.trans hkey1
      obtain ⟨hrk_r, hrk_c⟩ := fastRKeyProg_spec hr1 hinv1.seed_fp u
      have hbs1_lt := (hinv1.bkt_meta_bounds b hb).1
      have hcr1_lt := (hinv1.bkt_meta_bounds b hb).2.1
      have hci1_le := (hinv1.bkt_meta_bounds b hb).2.2.1
      have hbs1_r : (Memory.spec 0).clientResult s1 (fastReadBktLaneProg (fl.pBase, (b, 5))) =
          fm1.bktSalt b := by
        rw [clientResult_fastReadBktLaneProg hpt1 hb (by decide)]
        change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb]
      have hcr1_r : (Memory.spec 0).clientResult s1 (fastReadBktLaneProg (fl.pBase, (b, 12))) =
          fm1.curRole b := by
        rw [clientResult_fastReadBktLaneProg hpt1 hb (by decide)]
        change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb]
      obtain ⟨hfp_r, hfp_c⟩ := fastFpHashProg_spec hr1 hinv1.seed_fp ⟨fm1.bktSalt b, hbs1_lt⟩ u
      dsimp only at hfp_r hfp_c
      set fp := (fpHash fl.c fl.U fl.N seeds.fp ⟨fm1.bktSalt b, hbs1_lt⟩ u).val
      have hfp_lt : fp < 2 ^ fpBitsWhp fl.N :=
        (fpHash fl.c fl.U fl.N seeds.fp ⟨fm1.bktSalt b, hbs1_lt⟩ u).isLt
      obtain ⟨mapCur1, mapOld1, mapBTree1, _, _, _, _, _, _, hold_half1, hbt_all1, _, _, _, _⟩ :=
        hinv1.tiers
      obtain ⟨hlk_r, hlk_c⟩ := fastBTreeLookupProg_spec hr1 hb hcr1_lt hci1_le
        (hbt_all1 b hb).1 hfp_lt
      have houter : (Memory.spec 0).clientState s (drainOldSlotProg fl.pBase) =
          (Memory.spec 0).clientState s1
            (if ((Memory.spec 0).clientResult s1
                  (fastBTreeLookupProg ((fl.pBase, (b, fm1.curRole b)), fp))).1 = 0 then
              drainOldInsertNoCollProg
                (((fl.pBase, oldRole), (fm.drainPos, rKeyOf fl.c fl.U fl.N seeds.fp u)),
                  (b, (fp, loc)))
             else do
               let sc ← fastReadBktLaneProg (fl.pBase, (b, 15))
               if sc = 0 then startTrySaltProg (fl.pBase, b) else pure ()) ∧
          memoryCost (drainOldSlotProg fl.pBase) s ≤
            memoryCost (fastShadowSteps8Prog (fl.pBase, b)) s +
            (220 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 6 * hMaxBTree) +
            memoryCost (if ((Memory.spec 0).clientResult s1
                  (fastBTreeLookupProg ((fl.pBase, (b, fm1.curRole b)), fp))).1 = 0 then
              drainOldInsertNoCollProg
                (((fl.pBase, oldRole), (fm.drainPos, rKeyOf fl.c fl.U fl.N seeds.fp u)),
                  (b, (fp, loc)))
             else do
               let sc ← fastReadBktLaneProg (fl.pBase, (b, 15))
               if sc = 0 then startTrySaltProg (fl.pBase, b) else pure ()) s1 := by
        unfold drainOldSlotProg; dsimp only
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hm3_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadMetaProg, hm5_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          hr23_st, hr23_r, prog_memoryCost_read, ite_eq_left hinv.role_lt,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          StateTransitionSpec.clientState_pure, prog_clientResult_pure, memoryCost_pure,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastBufItemAllocProg, hia_r, ite_eq_left ⟨hia_old, hdp_lt⟩,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastBufCheckSlotProg, hcs_r, hchk, ite_eq_right Nat.one_ne_zero,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hs1_def]
        unfold drainOldActiveBodyProg; dsimp only
        have hr11_st : (Memory.spec 0).clientState s1 (Memory.read (fl.pBase + 11)) = s1 := rfl
        have hr11_r : (Memory.spec 0).clientResult s1 (Memory.read (fl.pBase + 11)) =
            numBucketsWhp fl.N := hpt1 11 (by decide)
        have c_cnt := hcnt1_r.2
        have c5 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 5)) s1
        have c12 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 12)) s1
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadBktCntProg, hcnt1_r.1,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          hr11_st, hr11_r, prog_memoryCost_read, ite_eq_left ⟨hb, hloc1⟩,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hrd_s, hrd_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastFeistelReconProg, hu_rec,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastRKeyProg, hrk_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadBktLaneProg, hbs1_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastReadBktLaneProg, hcr1_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastFpHashProg, hfp_r,
          StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_fastBTreeLookupProg]
        have hd4 : 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
            2 * (2 * dTabWhp fl.c * (cTabWhp fl.c + 2)) := by ring
        refine ⟨rfl, ?_⟩
        linarith only [cm3, cm5, hia_c, hcs_c, c_cnt, hrd_c, hrec_c, hrk_c, c5, c12,
          hfp_c, hlk_c, hd4]
      obtain ⟨hst_out, hc_out⟩ := houter
      cases hmb_q : mapBTree1 b fp with
      | none =>
        have hlk0 : (Memory.spec 0).clientResult s1
            (fastBTreeLookupProg ((fl.pBase, (b, fm1.curRole b)), fp)) = (0, 0) := by
          rw [hlk_r, hmb_q]
        rw [hlk0, ite_eq_left rfl] at hst_out hc_out
        obtain ⟨hfr2, hc2, hinv2, hbp2, htr2_c, htr2_o, hoi2, hof2, hcr2, hss2, hdp2, hta2,
          hbs2, hne2⟩ :=
          drainOldInsertNoCollProg_spec u hv1 hinv1 hsub1 hta1_0 hchk1 hkey1 hb hlk0
            (fun hsc => hbp1 ▸ hslack1 hb hsc)
        have hcr_old : 1 - fm1.curBufRole = oldRole := by rw [hcr1]
        have hc2' : memoryCost (drainOldInsertNoCollProg
            (((fl.pBase, oldRole), (fm.drainPos, rKeyOf fl.c fl.U fl.N seeds.fp u)),
              (b, (fp, loc)))) s1 ≤ 400 + 2 * cTabWhp fl.c + 144 * hMaxBTree := by
          rw [← hcr_old, ← hdp1]; exact hc2
        have hst_out' : (Memory.spec 0).clientState s (drainOldSlotProg fl.pBase) =
            (Memory.spec 0).clientState s1 (drainOldInsertNoCollProg
              (((fl.pBase, 1 - fm1.curBufRole),
                (fm1.drainPos, rKeyOf fl.c fl.U fl.N seeds.fp u)), (b, (fp, loc)))) := by
          rw [hcr_old, hdp1]; exact hst_out
        have hcost : memoryCost (drainOldSlotProg fl.pBase) s ≤
            3600 + 36 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 2 * cTabWhp fl.c + 780 * hMaxBTree := by
          have hd36 : 8 * (4 * dTabWhp fl.c * (cTabWhp fl.c + 2)) +
              4 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
              36 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by ring
          have hm0' : 0 ≤ hMaxBTree := Nat.zero_le _
          have hc_mul : 8 * (360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree) =
              2880 + 8 * (4 * dTabWhp fl.c * (cTabWhp fl.c + 2)) + 624 * hMaxBTree := by ring
          linarith only [hc_out, hc1, hc2', hd36, hm0', hc_mul]
        set s2 := (Memory.spec 0).clientState s1 (drainOldInsertNoCollProg
          (((fl.pBase, 1 - fm1.curBufRole),
            (fm1.drainPos, rKeyOf fl.c fl.U fl.N seeds.fp u)), (b, (fp, loc))))
        have htr2_c' : extractBufTrie (fl.trieL fm.curBufRole) s2.mem =
            extractBufTrie (fl.trieL fm.curBufRole) s.mem := by
          have h1 : extractBufTrie (fl.trieL fm.curBufRole) s2.mem =
              extractBufTrie (fl.trieL fm1.curBufRole) s2.mem := by rw [hcr1]
          have h2 : extractBufTrie (fl.trieL fm1.curBufRole) s2.mem =
              extractBufTrie (fl.trieL fm1.curBufRole) s1.mem := htr2_c
          rw [h1, h2, hcr1]; exact htr1 fm.curBufRole hinv.role_lt
        have htr2_o' : extractBufTrie (fl.trieL oldRole) s2.mem =
            bufDelete (cTabWhp fl.c) (bCharWhp fl.N)
              (extractBufTrie (fl.trieL oldRole) s.mem) (rKeyOf fl.c fl.U fl.N seeds.fp u) := by
          have ho : extractBufTrie (fl.trieL (1 - fm1.curBufRole)) s2.mem =
              bufDelete (cTabWhp fl.c) (bCharWhp fl.N)
                (extractBufTrie (fl.trieL (1 - fm1.curBufRole)) s1.mem)
                (rKeyOf fl.c fl.U fl.N seeds.fp u) := htr2_o
          have : extractBufTrie (fl.trieL oldRole) s2.mem =
              extractBufTrie (fl.trieL (1 - fm1.curBufRole)) s2.mem := by rw [hcr_old]
          rw [this, ho, hcr_old, htr1 oldRole hold_lt]
        rw [hst_out']
        refine ⟨hfr2.trans hfr1, hcost, hinv2, hbp2.trans hbp1, htr2_c',
          fun a ha => (hoi2 a ha).trans (hoi1 a ha),
          fun a ha => (hof2 a ha).trans (hof1 a ha),
          hcr2.trans hcr1, hss2.trans hss1, hbs2.trans hbs1,
          fun hle => absurd hdp_lt (Nat.not_lt.mpr hle),
          fun _ => Or.inr (Or.inl ⟨b, loc, u, hb, hloc_lt, rfl, hu_key,
            hdp2.trans (congrArg (· + 1) hdp1), hta2, htr2_o',
            fun b' hne_b =>
              ⟨(hne2 b' hne_b).1.trans (hne1 b' hne_b).1,
               (hne2 b' hne_b).2.1.trans (hne1 b' hne_b).2.1,
               (hne2 b' hne_b).2.2.1.trans (hne1 b' hne_b).2.2.1,
               (hne2 b' hne_b).2.2.2.trans (hne1 b' hne_b).2.2.2⟩⟩)⟩
      | some loc_hit =>
        have hlk1 : (Memory.spec 0).clientResult s1
            (fastBTreeLookupProg ((fl.pBase, (b, fm1.curRole b)), fp)) = (1, loc_hit) := by
          rw [hlk_r, hmb_q]
        rw [hlk1, ite_eq_right Nat.one_ne_zero] at hst_out hc_out
        -- Build distinct-key collision witness `(u, v_hit)` under `fm.bktSalt b`
        obtain ⟨hl_hit, v_hit, hfp_v, hk_v, _, hd2_v⟩ := (hbt_all1 b hb).2 fp loc_hit hmb_q
        obtain ⟨u_sv, v_sv, hu_sv, _, hb_v, _, hs_v⟩ := hinv1.bktSlot_refines hb hl_hit
        have huv_eq : u_sv = v_hit := Fin.ext (hu_sv.trans hk_v)
        rw [huv_eq] at hb_v hs_v
        rw [ite_eq_left hsub1] at hold_half1
        obtain ⟨hv_o1, _, _, _, _, _, _, _⟩ := hold_half1
        have htr_old_eq1 : extractBufTrie (fl.trieL (1 - fm1.curBufRole)) s1.mem =
            extractBufTrie (fl.trieL oldRole) s.mem := by
          rw [hcr1]; exact htr1 oldRole hold_lt
        have hrk_u_lt : rKeyOf fl.c fl.U fl.N seeds.fp u <
            2 ^ (cTabWhp fl.c * bCharWhp fl.N) := hrk_u.symm ▸ hrk_dp_lt
        have hmo1_u : mapOld1 (rKeyOf fl.c fl.U fl.N seeds.fp u) = some (b, loc) := by
          rw [← hv_o1.lookup_eq hrk_u_lt, htr_old_eq1, hv_old.lookup_eq hrk_u_lt, hrk_u]
          exact hmo_dp
        have huv_ne : u ≠ v_hit := by
          intro heq; subst heq; exact hd2_v b loc hmo1_u hkey1
        have hbs_b_eq : fm1.bktSalt b = fm.bktSalt b := congrFun hbs1 b
        have hfp_col : fpHash fl.c fl.U fl.N seeds.fp
              ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ u =
            fpHash fl.c fl.U fl.N seeds.fp
              ⟨fm.bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ v_hit := by
          apply Fin.ext
          have h1 : (fpHash fl.c fl.U fl.N seeds.fp ⟨fm1.bktSalt b, hbs1_lt⟩ u).val =
              (fpHash fl.c fl.U fl.N seeds.fp ⟨fm1.bktSalt b, hbs1_lt⟩ v_hit).val := hfp_v.symm
          rw [← fpHash_congr_salt (h₂ := (hinv.bkt_meta_bounds b hb).1) hbs_b_eq u,
            ← fpHash_congr_salt (h₂ := (hinv.bkt_meta_bounds b hb).1) hbs_b_eq v_hit]
          exact h1
        have hsc1_r : (Memory.spec 0).clientResult s1 (fastReadBktLaneProg (fl.pBase, (b, 15))) =
            fm1.shadowCode b := by
          rw [clientResult_fastReadBktLaneProg hpt1 hb (by decide)]
          change _ = (if b < numBucketsWhp fl.N then _ else 0); rw [ite_eq_left hb]
        have c15 := memoryCost_fastReadBktLaneProg (fl.pBase, (b, 15)) s1
        rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktLaneProg, hsc1_r]
          at hst_out
        rw [Realization.memoryCost_bind', clientState_fastReadBktLaneProg, hsc1_r] at hc_out
        have hd36 : 8 * (4 * dTabWhp fl.c * (cTabWhp fl.c + 2)) +
            4 * dTabWhp fl.c * (cTabWhp fl.c + 2) =
            36 * dTabWhp fl.c * (cTabWhp fl.c + 2) := by ring
        have hc_mul : 8 * (360 + 4 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 78 * hMaxBTree) =
            2880 + 8 * (4 * dTabWhp fl.c * (cTabWhp fl.c + 2)) + 624 * hMaxBTree := by ring
        have hm0' : 0 ≤ hMaxBTree := Nat.zero_le _
        have hct0' : 0 ≤ cTabWhp fl.c := Nat.zero_le _
        by_cases hsc1 : fm1.shadowCode b = 0
        · rw [ite_eq_left hsc1] at hst_out hc_out
          obtain ⟨hfr2, hc2, hinv2, hbp2, htr2, hoi2, hof2, hfm2⟩ :=
            startTrySaltProg_inv hv1 hinv1 hsub1 hta1_0 hb hsc1
          have hcost : memoryCost (drainOldSlotProg fl.pBase) s ≤
              3600 + 36 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 2 * cTabWhp fl.c +
                780 * hMaxBTree := by
            linarith only [hc_out, hc1, c15, hc2, hd36, hc_mul, hm0', hct0']
          rw [hst_out]
          refine ⟨hfr2.trans hfr1, hcost, hinv2, hbp2.trans hbp1,
            (htr2 fm.curBufRole hinv.role_lt).trans (htr1 fm.curBufRole hinv.role_lt),
            fun a ha => (hoi2 a ha).trans (hoi1 a ha),
            fun a ha => (hof2 a ha).trans (hof1 a ha),
            by rw [hfm2]; exact hcr1, by rw [hfm2]; exact hss1, by rw [hfm2]; exact hbs1,
            fun hle => absurd hdp_lt (Nat.not_lt.mpr hle),
            fun _ => Or.inr (Or.inr (Or.inr
              ⟨b, loc, hb, u, v_hit, rfl, hu_key, huv_ne,
                by rw [hs_u]; simp, by rw [hs_v]; simp, hb_u, hb_v, hfp_col,
                by rw [hfm2], by rw [hfm2], by rw [hfm2], by rw [hfm2], by rw [hfm2],
                by rw [hfm2]; exact hdp1, by rw [hfm2]; exact hsc1,
                (htr2 oldRole hold_lt).trans (htr1 oldRole hold_lt), fun hsc0_in => ?_⟩))⟩
          have hs1_eq_s : s1 = s := by
            rw [← hs1_def]
            exact fastShadowSteps8Prog_eq_of_shadowZero hpt hb hsc0_in
          intro hlk_zero
          have hlk_s1 : (Memory.spec 0).clientResult s1 (fastBTreeLookupProg
              ((fl.pBase, (b, fm1.curRole b)), fp)) = (0, 0) := by
            subst hs1_eq_s; exact hlk_zero
          rw [hlk1] at hlk_s1; cases hlk_s1
        · rw [ite_eq_right hsc1, StateTransitionSpec.clientState_pure] at hst_out
          rw [ite_eq_right hsc1, memoryCost_pure] at hc_out
          have hcost : memoryCost (drainOldSlotProg fl.pBase) s ≤
              3600 + 36 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 2 * cTabWhp fl.c +
                780 * hMaxBTree := by
            linarith only [hc_out, hc1, c15, hd36, hc_mul, hm0', hct0']
          rw [hst_out]
          exact ⟨hfr1, hcost, hinv1, hbp1, htr1 fm.curBufRole hinv.role_lt, hoi1, hof1,
            hcr1, hss1, hbs1, fun hle => absurd hdp_lt (Nat.not_lt.mpr hle),
            fun _ => Or.inr (Or.inr (Or.inl ⟨b, loc, hb, u, v_hit,
              rfl, hu_key, huv_ne, by rw [hs_u]; simp, by rw [hs_v]; simp, hb_u, hb_v,
              hfp_col, hs1_def.symm, hsc1, hta1_0, hdp1, htr1 oldRole hold_lt, hne1⟩))⟩
  · -- `itemAlloc ≤ drainPos`: pure no-op!
    have hst_eq : (Memory.spec 0).clientState s (drainOldSlotProg fl.pBase) = s ∧
        memoryCost (drainOldSlotProg fl.pBase) s ≤ 30 := by
      unfold drainOldSlotProg; dsimp only
      rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastReadMetaProg, hm3_r,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastReadMetaProg, hm5_r,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        hr23_st, hr23_r, prog_memoryCost_read, ite_eq_left hinv.role_lt,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        StateTransitionSpec.clientState_pure, prog_clientResult_pure, memoryCost_pure,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastBufItemAllocProg, hia_r,
        ite_eq_right (fun ⟨_, h⟩ => hdp_lt h), StateTransitionSpec.clientState_pure,
        memoryCost_pure]
      exact ⟨rfl, by linarith only [cm3, cm5, hia_c]⟩
    rw [hst_eq.1]
    have hc_le : memoryCost (drainOldSlotProg fl.pBase) s ≤
        3600 + 36 * dTabWhp fl.c * (cTabWhp fl.c + 2) + 2 * cTabWhp fl.c + 780 * hMaxBTree :=
      hst_eq.2.trans (by omega)
    exact ⟨rfl, hc_le, hinv, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl,
      fun _ => rfl, fun h => absurd h hdp_lt⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
