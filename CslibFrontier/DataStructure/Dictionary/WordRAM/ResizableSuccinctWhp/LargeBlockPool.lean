/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolStepProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unified Slot I/O and Deamortized `O(1)` Per-Bucket Block-Pool Allocator (`LargeBlockPool`)

This module provides two layers for large hashed epochs (`whpThreshold c ≤ N ≤ U < 2 ^ w`) of the
deamortized worst-case WHP resizable succinct dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]):

1. **Unified `SlotIoLayout` (direct pair stream, `SplitPair` slide view, and shared
   `PageArenaLayout`):**
   Abstracts `O(1)` worst-case `(quotient, value)` reads, writes, swaps, appends, and pop-backs
   over `[0, nSide)` (`slotIoReadProg`, `slotIoWriteProg`, `slotIoSwapProg`, `slotIoAppendProg`,
   `slotIoPopBackProg`) across three layout encodings: direct stream (`usePaged = 0 ∧ sideBit = 0`
   at `pgL.itemBase`), `SplitPair` two-slice slide view (`usePaged = 0 ∧ sideBit ≠ 0` via
   `SlotIoLayout.splitCfg`, repurposing `pgL.offDir`, `pgL.offTail`, and cursor `pgL.metaBase`),
   and shared `PageUnpermState` arena (`usePaged ≠ 0`, side `decide (sideBit ≠ 0)`) during
   dual-epoch Phase 8 (`migrate`) and Phase 9 (`unperm`).
2. **Deamortized `O(1)` per-bucket `BlockPoolState` (`bpToPhysProg`, `bpOwnerOfProg`,
   `bpAppendProg`, `bpPopBktBackProg`):**
   Maps per-bucket dense coordinates `(b, loc)` (`b < M`, `loc < bktCount b`) bijectively onto
   epoch virtual slots `[0, nSide)` with `O(1)` two-sided translation, per-bucket `ActiveBlock`
   slab promotion/demotion (`16` steps per bucket update, avoiding the Dietz–Sleator `Ω(K log M)`
   single-boundary cup-game bottleneck), and `16`-step `TopClean` boundary maintenance ensuring
   `0` extra item slots (`1 · OPT` space) and `0` intra-bucket `loc` shifts during background
   rebalancing.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SlotIoLayout`, `slotIoPairAt`,
  `slotIoReadProg`, `slotIoWriteProg`, `slotIoSwapProg`, `slotIoAppendProg`, `slotIoPopBackProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.BlockPoolLayout`,
  `epochBlockPoolLayout`, `BlockPoolProg`, `bpPairAt`, `bpInitProg`, `bpReadAtProg`,
  `bpWriteAtProg`, `bpAppendProg`, `bpPopBktBackProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.valid_epochBlockPoolLayout`,
  `bpInitProg_spec`, `bpReadAtProg_spec`, `bpWriteAtProg_spec`, `bpAppendProg_spec`,
  `bpPopBktBackProg_spec`.

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
open Cslib.DataStructure.WordRAM.Resizable.Randomized

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Unified `SlotIoLayout` (Direct, `SplitPair`, and Paged Modes) -/

/-- Unified three-mode descriptor for an epoch's `[0, nSide)` pair-slot array (`0` projection
chains):
* `usePaged = 0 ∧ sideBit = 0`: direct 2-slice stream at `pgL.itemBase`;
* `usePaged = 0 ∧ sideBit ≠ 0`: `SplitPair` slide view (`SlotIoLayout.splitCfg`) with lower slice at
  `(pgL.offDir, pgL.qBits, pgL.vBits)`, upper slice at `(pgL.itemBase, pgL.offTail, pgL.vBits)`, and
  split cursor at `pgL.metaBase`;
* `usePaged ≠ 0`: side `decide (sideBit ≠ 0)` of shared `PageArenaLayout` `pgL`. -/
structure SlotIoLayout where
  /-- `0` for direct / `SplitPair` mode; nonzero for shared `PageArenaLayout` mode. -/
  usePaged : ℕ
  /-- When `usePaged = 0`, `0` selects direct mode and nonzero selects `SplitPair` mode; when
  `usePaged ≠ 0`, `0` selects `E_src` (`false`) and nonzero selects `E_dst` (`true`). -/
  sideBit : ℕ
  /-- Underlying `PageArenaLayout` (also carrying `itemBase`, `offDir`, `offTail`, `metaBase`,
  `qBits`, `vBits`, `w`, and `nCap` for direct and `SplitPair` modes). -/
  pgL : PageArenaLayout

/-- Internal 13-word register-tuple representation of `SlotIoLayout` for `RealizesBounded`. -/
abbrev SlotIoCtx := (ℕ × ℕ) × PageArenaCtx

/-- Pack `SlotIoLayout` into `SlotIoCtx`. -/
@[expose] def SlotIoLayout.toCtx (io : SlotIoLayout) : SlotIoCtx :=
  ((io.usePaged, io.sideBit), io.pgL.toCtx)

/-- Unpack `SlotIoCtx` into `SlotIoLayout`. -/
@[expose] def SlotIoLayout.ofCtx : SlotIoCtx → SlotIoLayout
  | ((up, sb), pctx) => ⟨up, sb, PageArenaLayout.ofCtx pctx⟩

@[simp] theorem SlotIoLayout.ofCtx_toCtx (io : SlotIoLayout) :
    SlotIoLayout.ofCtx io.toCtx = io := by
  rcases io with ⟨_, _, ⟨_, _, _, _, _, _, _, _, _, _, _⟩⟩; rfl

@[simp] theorem SlotIoLayout.toCtx_ofCtx (ctx : SlotIoCtx) :
    (SlotIoLayout.ofCtx ctx).toCtx = ctx := by
  rcases ctx with ⟨⟨_, _⟩, ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩⟩; rfl

/-- Boolean side selected by `io.sideBit`. -/
@[expose] def SlotIoLayout.side (io : SlotIoLayout) : Bool :=
  decide (io.sideBit ≠ 0)

/-- Partner `SlotIoLayout` viewing the opposite side `!(io.side)` of the same `PageArenaLayout`. -/
@[expose] def SlotIoLayout.partner (io : SlotIoLayout) : SlotIoLayout where
  usePaged := io.usePaged
  sideBit := if io.sideBit = 0 then 1 else 0
  pgL := io.pgL

@[simp] theorem SlotIoLayout.partner_side (io : SlotIoLayout) :
    io.partner.side = !io.side := by
  unfold SlotIoLayout.partner SlotIoLayout.side
  by_cases h : io.sideBit = 0 <;> simp [h]

@[simp] theorem SlotIoLayout.partner_pgL (io : SlotIoLayout) :
    io.partner.pgL = io.pgL := rfl

/-- Split-pair view embedded inside a `SlotIoLayout` when `usePaged = 0 ∧ sideBit ≠ 0`:
lower slice at `(offDir, qBits, vBits)`, upper slice at `(itemBase, offTail, vBits)`, cursor word
at `metaBase` (`s_split := mem metaBase`). -/
@[expose] def SlotIoLayout.splitCfg (io : SlotIoLayout) : SplitPairCfg where
  baseLo := io.pgL.offDir
  qBitsLo := io.pgL.qBits
  vBitsLo := io.pgL.vBits
  baseHi := io.pgL.itemBase
  qBitsHi := io.pgL.offTail
  vBitsHi := io.pgL.vBits
  w := io.pgL.w

/-- Logical `(quotient, value)` pair at virtual index `idx` of `io`. -/
@[expose] def slotIoPairAt (io : SlotIoLayout) (mem : ℕ → ℕ) (idx : ℕ) : ℕ × ℕ :=
  if io.usePaged = 0 then
    if io.sideBit = 0 then
      arenaPairAt io.pgL mem idx
    else
      let p := splitPairRead io.splitCfg (mem io.pgL.metaBase) mem idx
      (p.1 % 2 ^ io.pgL.qBits, p.2)
  else
    (extractPageUnperm io.pgL mem).virtAt (arenaPairAt io.pgL mem) io.side idx

theorem slotIoPairAt_bounds {io : SlotIoLayout} (mem : ℕ → ℕ) (idx : ℕ) :
    (slotIoPairAt io mem idx).1 < 2 ^ io.pgL.qBits ∧
    (slotIoPairAt io mem idx).2 < 2 ^ io.pgL.vBits := by
  unfold slotIoPairAt PageUnpermState.virtAt arenaPairAt
  split_ifs with h0 hs
  · exact ⟨pairQuotAt_lt .., pairValAt_lt ..⟩
  · refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
    unfold splitPairRead SlotIoLayout.splitCfg; split_ifs <;> exact pairValAt_lt ..
  · exact ⟨pairQuotAt_lt .., pairValAt_lt ..⟩

/-- Word-address footprint owned by `io`. -/
@[expose] def SlotIoLayout.OwnsAddr (io : SlotIoLayout) (addr : ℕ) : Prop :=
  if io.usePaged = 0 then
    if io.sideBit = 0 then
      io.pgL.OwnsItemAddr addr
    else
      addr = io.pgL.metaBase ∨
      (io.pgL.offDir ≤ addr ∧
        addr < io.pgL.offDir + pairStreamWords io.pgL.nCap io.pgL.qBits io.pgL.vBits io.pgL.w) ∨
      (io.pgL.itemBase ≤ addr ∧
        addr < io.pgL.itemBase + pairStreamWords io.pgL.nCap io.pgL.offTail io.pgL.vBits io.pgL.w)
  else
    io.pgL.OwnsAddr addr

/-- Static frontier validity predicate for `SlotIoLayout` (independent of `s.mem`). -/
@[expose] def SlotIoLayout.Valid (io : SlotIoLayout) (w frontier : ℕ) : Prop :=
  if io.usePaged = 0 then
    0 < w ∧ w = io.pgL.w ∧ io.pgL.qBits ≤ w ∧ io.pgL.vBits ≤ w ∧
    io.pgL.nCap < 2 ^ w ∧
    (if io.sideBit = 0 then
      io.pgL.itemBase + pairStreamWords io.pgL.nCap io.pgL.qBits io.pgL.vBits io.pgL.w ≤ frontier
    else
      io.pgL.qBits ≤ io.pgL.offTail ∧ io.pgL.offTail ≤ w ∧
      io.pgL.metaBase < io.pgL.offDir ∧ io.pgL.offDir + 2 ≤ io.pgL.itemBase ∧
      io.pgL.itemBase + pairStreamWords io.pgL.nCap io.pgL.offTail io.pgL.vBits io.pgL.w ≤ frontier)
  else
    io.pgL.Valid w frontier

theorem SlotIoLayout.Valid.w_pos {io : SlotIoLayout} {w frontier : ℕ}
    (hv : io.Valid w frontier) : 0 < io.pgL.w := by
  unfold SlotIoLayout.Valid at hv
  by_cases h0 : io.usePaged = 0
  · rw [ite_eq_left h0] at hv; exact hv.2.1 ▸ hv.1
  · rw [ite_eq_right h0] at hv; exact hv.2.1 ▸ hv.1

/-- Dynamic memory invariant coupling `io` to `nSide` live virtual slots with `PageUnpermState`
slack `slack`. -/
@[expose] def SlotIoLayout.StateInv (io : SlotIoLayout) (nSide slack : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  if io.usePaged = 0 then
    nSide ≤ io.pgL.nCap ∧ (io.sideBit = 0 ∨ io.pgL.offTail ≤ io.pgL.w)
  else
    let u := extractPageUnperm io.pgL mem
    u.InvWithSlack slack ∧
    u.st.pageSize = io.pgL.pgB ∧
    u.st.totalPages < io.pgL.maxPages ∧
    u.st.totalItems ≤ io.pgL.nCap ∧
    u.st.virtLen io.side = nSide ∧
    (0 < u.cleanPhase → io.side = true) ∧
    u.cleanPhase < 4

theorem SlotIoLayout.StateInv.mono_slack {io : SlotIoLayout} {nSide s₁ s₂ : ℕ} {mem : ℕ → ℕ}
    (h : io.StateInv nSide s₁ mem) (hle : s₁ ≤ s₂) (hs₂ : s₂ ≤ 24) :
    io.StateInv nSide s₂ mem := by
  unfold SlotIoLayout.StateInv at h ⊢
  split_ifs at h ⊢ with h0
  · exact h
  · exact ⟨h.1.mono hle hs₂, h.2⟩

/-- Physical slot-capacity room for appending `1` item to `io` (`nSide + 1 ≤ nCap` when unpaged,
`totalItems + 1 ≤ nCap` when paged). -/
@[expose] def SlotIoLayout.AppendCap (io : SlotIoLayout) (nSide : ℕ) (mem : ℕ → ℕ) : Prop :=
  if io.usePaged = 0 then nSide + 1 ≤ io.pgL.nCap
  else (extractPagePair io.pgL mem).totalItems + 1 ≤ io.pgL.nCap

/-- Word footprint of a 2-slice `(q, v)` stream is monotone in `q_bits`. -/
theorem pairStreamWords_mono_qBits {n q₁ q₂ v w : ℕ} (hq : q₁ ≤ q₂) :
    pairStreamWords n q₁ v w ≤ pairStreamWords n q₂ v w := by
  unfold pairStreamWords packedWords
  have h1 : n * (q₁ + v) ≤ n * (q₂ + v) := Nat.mul_le_mul_left n (by omega)
  exact Nat.add_le_add_right (Nat.div_le_div_right (by omega)) _

private theorem pairAt_congr_mem {base qB vB w n idx : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hw : 0 < w) (hidx : idx < n)
    (heq : ∀ a, base ≤ a → a < base + pairStreamWords n qB vB w → m₂ a = m₁ a) :
    pairQuotAt base qB vB w m₂ idx = pairQuotAt base qB vB w m₁ idx ∧
    pairValAt base qB vB w m₂ idx = pairValAt base qB vB w m₁ idx := by
  have hq_lt := wOffQ_add_one_lt_pairStreamWords (n := n) (q_bits := qB) (v_bits := vB) hw hidx
  have hv_lt := wOffV_add_one_lt_pairStreamWords (n := n) (q_bits := qB) (v_bits := vB) hw hidx
  unfold pairQuotAt pairValAt readBitSlice; dsimp only
  constructor
  · rw [heq (base + wOffQ qB vB w idx) (Nat.le_add_right _ _) (by omega),
      heq (base + wOffQ qB vB w idx + 1) (by omega) (by omega)]
  · rw [heq (base + wOffV qB vB w idx) (Nat.le_add_right _ _) (by omega),
      heq (base + wOffV qB vB w idx + 1) (by omega) (by omega)]

/-- Any memory modification strictly outside `io.OwnsAddr` preserves both `io.StateInv` and
`slotIoPairAt io · idx` on `[0, nSide)`. -/
theorem SlotIoLayout.congr_of_outside {io : SlotIoLayout} {nSide slack : ℕ}
    {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < io.pgL.w)
    (hinv : io.StateInv nSide slack mem₁)
    (heq : ∀ addr, io.OwnsAddr addr → mem₂ addr = mem₁ addr) :
    io.StateInv nSide slack mem₂ ∧
    ∀ idx < nSide, slotIoPairAt io mem₂ idx = slotIoPairAt io mem₁ idx := by
  by_cases h0 : io.usePaged = 0
  · simp only [SlotIoLayout.StateInv, SlotIoLayout.OwnsAddr, h0, ↓reduceIte] at hinv heq ⊢
    refine ⟨hinv, fun idx hidx => ?_⟩
    unfold slotIoPairAt
    rw [ite_eq_left h0, ite_eq_left h0]
    by_cases hs : io.sideBit = 0
    · simp only [hs, ↓reduceIte] at heq ⊢
      exact arenaPairAt_congr hw (fun a ha => heq a ha) (hidx.trans_le hinv.1)
    · simp only [hs, ↓reduceIte] at heq ⊢
      have hmb : mem₂ io.pgL.metaBase = mem₁ io.pgL.metaBase := heq _ (Or.inl rfl)
      rw [hmb]
      unfold splitPairRead SlotIoLayout.splitCfg; dsimp only
      by_cases hsp : idx < mem₁ io.pgL.metaBase
      · rw [ite_eq_left hsp, ite_eq_left hsp]
        have ⟨hq, hv⟩ := pairAt_congr_mem hw (hidx.trans_le hinv.1)
          (fun a h1 h2 => heq a (Or.inr (Or.inl ⟨h1, h2⟩)))
        rw [hq, hv]
      · rw [ite_eq_right hsp, ite_eq_right hsp]
        have ⟨hq, hv⟩ := pairAt_congr_mem hw (hidx.trans_le hinv.1)
          (fun a h1 h2 => heq a (Or.inr (Or.inr ⟨h1, h2⟩)))
        rw [hq, hv]
  · simp only [SlotIoLayout.StateInv, SlotIoLayout.OwnsAddr, h0, ↓reduceIte] at hinv heq ⊢
    have hu_eq : extractPageUnperm io.pgL mem₂ = extractPageUnperm io.pgL mem₁ :=
      extractPageUnperm_congr hw (fun a ha => heq a (Or.inl ha))
    refine ⟨by rw [hu_eq]; exact hinv, fun idx hidx => ?_⟩
    unfold slotIoPairAt
    rw [ite_eq_right h0, ite_eq_right h0, hu_eq]
    obtain ⟨hi, _, _, hti, hvl, _, _⟩ := hinv
    have hp_lt : (extractPageUnperm io.pgL mem₁).toPhys io.side idx < io.pgL.nCap :=
      (hi.toPhys_lt (hvl.symm ▸ hidx)).trans_le hti
    unfold PageUnpermState.virtAt
    exact arenaPairAt_congr hw (fun a ha => heq a (Or.inr ha)) hp_lt

/-- Raw tuple primitive reading `(q, v)` at `idx` from `SlotIoCtx` (`¬ReadsWidth`). -/
@[expose] def slotIoReadRawProg : SlotIoCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | (((up, sb), ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))), idx) =>
    if up = 0 then
      if idx < nc then
        if sb = 0 then
          readPairGenProg (((ib, (qb, vb)), wv), idx)
        else do
          let sp ← Memory.read mb
          if idx < sp then
            readPairGenProg (((od, (qb, vb)), wv), idx)
          else do
            let p ← readPairGenProg (((ib, (ot, vb)), wv), idx)
            if qb < wv then
              let mask ← pure ((1 <<< qb) - 1)
              pure (p.1 &&& mask, p.2)
            else
              pure p
      else
        pure (0, 0)
    else do
      let sb01 ← pure (if sb = 0 then 0 else 1)
      pageReadVirtBoundedProg
        (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sb01, idx))

/-- Read `(q, v)` at virtual index `idx` from `io : SlotIoLayout` (`¬ReadsWidth`). -/
@[expose] def slotIoReadProg (io : SlotIoLayout) (idx : ℕ) : Memory.Prog (ℕ × ℕ) :=
  slotIoReadRawProg (io.toCtx, idx)

theorem realizesBounded_slotIoReadRaw :
    RealizesBounded .exact slotIoReadRawProg
      (WordEncoding.encode (α := SlotIoCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ctx, _) s => (SlotIoLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPairGen
  have hrv := realizesBounded_pageReadVirt
  realize
  all_goals (
    rcases d with ⟨⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩,
      ⟨⟨qb, vb⟩, nc⟩⟩⟩, idx⟩
    unfold SlotIoLayout.Valid SlotIoLayout.ofCtx at h
    dsimp only at *)
  all_goals (
    try (simp only [‹up = 0›, ↓reduceIte] at h
         obtain ⟨hw, hwv, hqb, hvb, _, htail⟩ := h
         subst hwv
         first
         | (simp only [‹sb = 0›, ↓reduceIte] at htail
            have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw
              ‹idx < nc›
            exact ⟨hw, rfl, hqb, hvb, by omega⟩)
         | (simp only [‹¬sb = 0›, ↓reduceIte] at htail
            obtain ⟨hq_ot, hot_w, hmb_od, hod_ib, hib_fr⟩ := htail
            have hfr_w := hmem.1
            have hw_lt : pairStreamWords nc qb vb w ≤ pairStreamWords nc ot vb w :=
              pairStreamWords_mono_qBits hq_ot
            first
            | (dsimp only [Fits] at hfr_w ⊢; omega)
            | (have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw
                 ‹idx < nc›
               exact ⟨hw, rfl, hqb, hvb, by omega⟩)
            | (have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := ot) (v_bits := vb) hw
                 ‹idx < nc›
               exact ⟨hw, rfl, hot_w, hvb, by omega⟩)
            | (have : 1 ≤ 2 ^ qb := Nat.one_le_two_pow
               have : 2 ^ qb < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two ‹qb < w›
               have : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
               try simp only [Nat.shiftLeft_eq, one_mul]
               try dsimp only [Fits]
               omega))))
  all_goals (
    simp only [‹¬up = 0›, ↓reduceIte] at h
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow h.1.ne'
    try dsimp only [PageArenaLayout.ofCtx] at h ⊢
    first | exact h | exact hw1)

theorem slotIoReadProg_frame (io : SlotIoLayout) (idx : ℕ) :
    BoundedFrameProg io.OwnsAddr 20 (slotIoReadProg io idx) := by
  unfold slotIoReadProg slotIoReadRawProg SlotIoLayout.OwnsAddr
  dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  by_cases h0 : io.usePaged = 0
  · simp only [h0, ↓reduceIte]
    refine BoundedFrameProg.ite_prog (idx < io.pgL.nCap)
      (fun _ => BoundedFrameProg.ite_prog (io.sideBit = 0)
        (fun _ => (BoundedFrameProg.readPairGen_prog _ _).mono (C₂ := 20) (fun _ h => h)
          (by decide))
        (fun _ => (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun sp =>
          BoundedFrameProg.ite_prog (idx < sp)
            (fun _ => (BoundedFrameProg.readPairGen_prog _ _).mono (C₂ := 4)
              (fun _ h => h) le_rfl)
            (fun _ => (BoundedFrameProg.bind_prog (BoundedFrameProg.readPairGen_prog _ _) fun p =>
              BoundedFrameProg.ite_prog (io.pgL.qBits < io.pgL.w)
                (fun _ => BoundedFrameProg.bind_prog (BoundedFrameProg.pure_prog _) fun _ =>
                  BoundedFrameProg.pure_prog _)
                (fun _ => BoundedFrameProg.pure_prog _)).mono (C₂ := 4)
              (fun _ h => h) (by omega))).mono (C₂ := 20) (fun _ h => h) (by decide)))
      (fun _ => (BoundedFrameProg.pure_prog (0, 0)).mono (C₂ := 20) (fun _ h => h) (by decide))
  · simp only [h0, ↓reduceIte, pure_bind]
    exact pageReadVirtBoundedProg_frame io.pgL (if io.sideBit = 0 then 0 else 1) idx

theorem slotIoReadProg_spec {io : SlotIoLayout} {nSide slack idx : ℕ} {s : Memory.State}
    (hinv : io.StateInv nSide slack s.mem) (hidx : idx < nSide) :
    (Memory.spec 0).clientResult s (slotIoReadProg io idx) = slotIoPairAt io s.mem idx ∧
    (Memory.spec 0).clientState s (slotIoReadProg io idx) = s := by
  unfold slotIoReadProg slotIoReadRawProg slotIoPairAt
  unfold SlotIoLayout.StateInv at hinv
  dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  by_cases h0 : io.usePaged = 0
  · simp only [h0, ↓reduceIte] at hinv ⊢
    have hlt : idx < io.pgL.nCap := hidx.trans_le hinv.1
    rw [ite_eq_left hlt]
    by_cases hs : io.sideBit = 0
    · rw [ite_eq_left hs, ite_eq_left hs]
      exact ⟨clientResult_readPairGenProg .., clientState_readPairGenProg ..⟩
    · have hot_le : io.pgL.offTail ≤ io.pgL.w := hinv.2.resolve_left hs
      rw [ite_eq_right hs, ite_eq_right hs]
      unfold splitPairRead SlotIoLayout.splitCfg; dsimp only
      have hrd_st : (Memory.spec 0).clientState s (Memory.read io.pgL.metaBase) = s := rfl
      have hrd_res : (Memory.spec 0).clientResult s (Memory.read io.pgL.metaBase) =
          s.mem io.pgL.metaBase := rfl
      by_cases hsp : idx < s.mem io.pgL.metaBase
      · refine ⟨?_, ?_⟩
        · rw [prog_clientResult_bind, hrd_st, hrd_res, ite_eq_left hsp, ite_eq_left hsp,
            clientResult_readPairGenProg]
          exact Prod.ext (Nat.mod_eq_of_lt (pairQuotAt_lt ..)).symm rfl
        · rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res, ite_eq_left hsp,
            clientState_readPairGenProg]
      · have hmod : ∀ x : ℕ, io.pgL.qBits < io.pgL.w →
            x &&& ((1 <<< io.pgL.qBits) - 1) = x % 2 ^ io.pgL.qBits := fun x _ => by
          rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]
        by_cases hqw : io.pgL.qBits < io.pgL.w
        · refine ⟨?_, ?_⟩
          · rw [prog_clientResult_bind, hrd_st, hrd_res, ite_eq_right hsp, ite_eq_right hsp,
              prog_clientResult_bind, clientState_readPairGenProg, clientResult_readPairGenProg,
              ite_eq_left hqw, prog_clientResult_bind,
              show (Memory.spec 0).clientState s (pure _) = s from rfl,
              prog_clientResult_pure, prog_clientResult_pure]
            exact Prod.ext (hmod _ hqw) rfl
          · rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res, ite_eq_right hsp,
              StateTransitionSpec.clientState_bind, clientState_readPairGenProg, ite_eq_left hqw,
              StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure,
              StateTransitionSpec.clientState_pure]
        · have hlt_q : pairQuotAt io.pgL.itemBase io.pgL.offTail io.pgL.vBits io.pgL.w s.mem idx <
              2 ^ io.pgL.qBits :=
            (pairQuotAt_lt ..).trans_le (Nat.pow_le_pow_right two_pos (by omega))
          refine ⟨?_, ?_⟩
          · rw [prog_clientResult_bind, hrd_st, hrd_res, ite_eq_right hsp, ite_eq_right hsp,
              prog_clientResult_bind, clientState_readPairGenProg, clientResult_readPairGenProg,
              ite_eq_right hqw, prog_clientResult_pure]
            exact Prod.ext (Nat.mod_eq_of_lt hlt_q).symm rfl
          · rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res, ite_eq_right hsp,
              StateTransitionSpec.clientState_bind, clientState_readPairGenProg, ite_eq_right hqw,
              StateTransitionSpec.clientState_pure]
  · simp only [h0, ↓reduceIte, pure_bind] at hinv ⊢
    obtain ⟨hi, hps, hmp, hti, hvl, _, _⟩ := hinv
    have hsb_eq : (if io.sideBit = 0 then 0 else 1) = if io.side then 1 else 0 := by
      unfold SlotIoLayout.side; by_cases hz : io.sideBit = 0 <;> simp [hz]
    rw [hsb_eq]
    exact pageReadVirtBoundedProg_spec hi hps hmp hti io.side (hvl.symm ▸ hidx)

/-- Raw tuple primitive writing `(q, v)` at `idx` into `SlotIoCtx` (`¬ReadsWidth`). -/
@[expose] def slotIoWriteRawProg : (SlotIoCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((up, sb), ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))), idx), qv) =>
    if up = 0 then
      if idx < nc then
        if sb = 0 then
          writePairGenProg ((((ib, (qb, vb)), wv), idx), qv)
        else do
          let sp ← Memory.read mb
          if idx < sp then
            writePairGenProg ((((od, (qb, vb)), wv), idx), qv)
          else
            writePairGenProg ((((ib, (ot, vb)), wv), idx), qv)
      else
        pure ()
    else do
      let sb01 ← pure (if sb = 0 then 0 else 1)
      pageWriteVirtBoundedProg
        ((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sb01, idx)), qv)

/-- Write `(q, v)` at virtual index `idx` into `io : SlotIoLayout` (`¬ReadsWidth`). -/
@[expose] def slotIoWriteProg (io : SlotIoLayout) (idx q v : ℕ) : Memory.Prog Unit :=
  slotIoWriteRawProg ((io.toCtx, idx), (q, v))

theorem realizesBounded_slotIoWriteRaw :
    RealizesBounded .exact slotIoWriteRawProg
      (WordEncoding.encode (α := (SlotIoCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (SlotIoLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwp := realizesBounded_writePairGen
  have hwv := realizesBounded_pageWriteVirt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩,
      ⟨⟨qb, vb⟩, nc⟩⟩⟩, idx⟩, qv⟩
    unfold SlotIoLayout.Valid SlotIoLayout.ofCtx at h
    dsimp only at *)
  all_goals (
    try (simp only [‹up = 0›, ↓reduceIte] at h
         obtain ⟨hw, hw_eq, hqb, hvb, _, htail⟩ := h
         subst hw_eq
         first
         | (simp only [‹sb = 0›, ↓reduceIte] at htail
            have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw
              ‹idx < nc›
            exact ⟨hw, rfl, hqb, hvb, by omega⟩)
         | (simp only [‹¬sb = 0›, ↓reduceIte] at htail
            obtain ⟨hq_ot, hot_w, hmb_od, hod_ib, hib_fr⟩ := htail
            have hfr_w := hmem.1
            have hw_lt : pairStreamWords nc qb vb w ≤ pairStreamWords nc ot vb w :=
              pairStreamWords_mono_qBits hq_ot
            first
            | (dsimp only [Fits] at hfr_w ⊢; omega)
            | (have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw
                 ‹idx < nc›
               exact ⟨hw, rfl, hqb, hvb, by omega⟩)
            | (have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := ot) (v_bits := vb) hw
                 ‹idx < nc›
               exact ⟨hw, rfl, hot_w, hvb, by omega⟩))))
  all_goals (
    simp only [‹¬up = 0›, ↓reduceIte] at h
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow h.1.ne'
    try dsimp only [PageArenaLayout.ofCtx] at h ⊢
    first | exact h | exact hw1)

theorem slotIoWriteProg_frame {io : SlotIoLayout} (hw : 0 < io.pgL.w) (idx q v : ℕ) :
    BoundedFrameProg io.OwnsAddr 24 (slotIoWriteProg io idx q v) := by
  unfold slotIoWriteProg slotIoWriteRawProg SlotIoLayout.OwnsAddr
  dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  by_cases h0 : io.usePaged = 0
  · simp only [h0, ↓reduceIte]
    by_cases hs : io.sideBit = 0
    · simp only [hs, ↓reduceIte]
      exact BoundedFrameProg.ite_prog (idx < io.pgL.nCap)
        (fun hp => (BoundedFrameProg.writePairGen_prog hw hp
          (fun _ h1 h2 => ⟨h1, h2⟩)).mono (C₂ := 24) (fun _ h => h) (by decide))
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (C₂ := 24) (fun _ h => h) (by decide))
    · simp only [hs, ↓reduceIte]
      exact BoundedFrameProg.ite_prog (idx < io.pgL.nCap)
        (fun hp => (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun sp =>
          BoundedFrameProg.ite_prog (idx < sp)
            (fun _ => (BoundedFrameProg.writePairGen_prog hw hp
              (fun _ h1 h2 => Or.inr (Or.inl ⟨h1, h2⟩))).mono (C₂ := 8) (fun _ h => h) le_rfl)
            (fun _ => (BoundedFrameProg.writePairGen_prog hw hp
              (fun _ h1 h2 => Or.inr (Or.inr ⟨h1, h2⟩))).mono (C₂ := 8) (fun _ h => h) le_rfl)).mono
          (C₂ := 24) (fun _ h => h) (by decide))
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (C₂ := 24) (fun _ h => h) (by decide))
  · simp only [h0, ↓reduceIte, pure_bind]
    exact pageWriteVirtBoundedProg_frame hw (if io.sideBit = 0 then 0 else 1) idx q v

theorem slotIoWriteProg_spec {io : SlotIoLayout} {nSide slack idx q v : ℕ} {s : Memory.State}
    (hvIo : io.Valid io.pgL.w s.frontier)
    (hinv : io.StateInv nSide slack s.mem) (hidx : idx < nSide)
    (hq : q < 2 ^ io.pgL.qBits) (hv : v < 2 ^ io.pgL.vBits) :
    let s' := (Memory.spec 0).clientState s (slotIoWriteProg io idx q v)
    io.StateInv nSide slack s'.mem ∧
    (∀ idx₂ < nSide,
      slotIoPairAt io s'.mem idx₂ = if idx₂ = idx then (q, v) else slotIoPairAt io s.mem idx₂) ∧
    (io.usePaged ≠ 0 →
      extractPageUnperm io.pgL s'.mem = extractPageUnperm io.pgL s.mem ∧
      ∀ idx₂ < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx₂ = slotIoPairAt io.partner s.mem idx₂) := by
  dsimp only
  unfold slotIoWriteProg slotIoWriteRawProg SlotIoLayout.StateInv
  unfold SlotIoLayout.Valid at hvIo
  unfold SlotIoLayout.StateInv at hinv
  dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  by_cases h0 : io.usePaged = 0
  · simp only [h0, ↓reduceIte] at hvIo hinv ⊢
    obtain ⟨hw, _, _, _, _, htail⟩ := hvIo
    have hlt : idx < io.pgL.nCap := hidx.trans_le hinv.1
    rw [ite_eq_left hlt]
    by_cases hs : io.sideBit = 0
    · rw [ite_eq_left hs, clientState_writePairGenProg]
      refine ⟨hinv, fun idx₂ _ => ?_, fun hne => absurd rfl hne⟩
      unfold slotIoPairAt arenaPairAt
      rw [ite_eq_left h0, ite_eq_left h0, ite_eq_left hs, ite_eq_left hs]
      by_cases heq : idx₂ = idx
      · subst heq; rw [ite_eq_left rfl]
        exact Prod.ext (pairQuotAt_writePair_self hw s.mem hq) (pairValAt_writePair_self s.mem hv)
      · rw [ite_eq_right heq]
        exact Prod.ext (pairQuotAt_writePair_of_ne hw s.mem heq)
          (pairValAt_writePair_of_ne hw s.mem heq)
    · rw [ite_eq_right hs] at htail ⊢
      obtain ⟨hq_ot, hot_w, hmb_od, hod_ib, _⟩ := htail
      have hrd_st : (Memory.spec 0).clientState s (Memory.read io.pgL.metaBase) = s := rfl
      have hrd_res : (Memory.spec 0).clientResult s (Memory.read io.pgL.metaBase) =
          s.mem io.pgL.metaBase := rfl
      rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res]
      have hmem_sp : (if idx < s.mem io.pgL.metaBase then
          (Memory.spec 0).clientState s (writePairGenProg
            ((((io.pgL.offDir, (io.pgL.qBits, io.pgL.vBits)), io.pgL.w), idx), (q, v)))
        else
          (Memory.spec 0).clientState s (writePairGenProg
            ((((io.pgL.itemBase, (io.pgL.offTail, io.pgL.vBits)), io.pgL.w), idx), (q, v)))).mem =
        splitPairWrite io.splitCfg (s.mem io.pgL.metaBase) s.mem idx q v := by
        unfold splitPairWrite SlotIoLayout.splitCfg; dsimp only
        split_ifs <;> rw [clientState_writePairGenProg]
      have hmb_fix : splitPairWrite io.splitCfg (s.mem io.pgL.metaBase) s.mem idx q v
          io.pgL.metaBase = s.mem io.pgL.metaBase := by
        unfold splitPairWrite SlotIoLayout.splitCfg; dsimp only
        split_ifs
        · exact writePair_outside hw hlt s.mem (fun h => by omega)
        · exact writePair_outside hw hlt s.mem (fun h => by omega)
      have hmem_ite : ((Memory.spec 0).clientState s
          (if idx < s.mem io.pgL.metaBase then
            writePairGenProg
              ((((io.pgL.offDir, (io.pgL.qBits, io.pgL.vBits)), io.pgL.w), idx), (q, v))
          else
            writePairGenProg
              ((((io.pgL.itemBase, (io.pgL.offTail, io.pgL.vBits)), io.pgL.w), idx), (q, v)))).mem =
          splitPairWrite io.splitCfg (s.mem io.pgL.metaBase) s.mem idx q v := by
        by_cases hsp : idx < s.mem io.pgL.metaBase <;>
          simp only [hsp, ↓reduceIte] at hmem_sp ⊢ <;> exact hmem_sp
      refine ⟨hinv, fun idx₂ _ => ?_, fun hne => absurd rfl hne⟩
      unfold slotIoPairAt
      rw [ite_eq_left h0, ite_eq_left h0, ite_eq_right hs, ite_eq_right hs, hmem_ite, hmb_fix]
      by_cases heq : idx₂ = idx
      · subst heq; rw [ite_eq_left rfl]
        have hq' : q < 2 ^ (if idx₂ < s.mem io.pgL.metaBase then
            io.splitCfg.qBitsLo else io.splitCfg.qBitsHi) := by
          dsimp only [SlotIoLayout.splitCfg]; split_ifs
          · exact hq
          · exact hq.trans_le (Nat.pow_le_pow_right two_pos hq_ot)
        have hv' : v < 2 ^ (if idx₂ < s.mem io.pgL.metaBase then
            io.splitCfg.vBitsLo else io.splitCfg.vBitsHi) := by
          dsimp only [SlotIoLayout.splitCfg]; split_ifs <;> exact hv
        rw [splitPairRead_splitPairWrite_self (cfg := io.splitCfg) hw s.mem hq' hv']
        exact Prod.ext (Nat.mod_eq_of_lt hq) rfl
      · rw [ite_eq_right heq, splitPairRead_splitPairWrite_of_ne (cfg := io.splitCfg) hw
          (by dsimp only [SlotIoLayout.splitCfg]; omega) hod_ib s.mem heq]
  · simp only [h0, ↓reduceIte, pure_bind] at hvIo hinv ⊢
    obtain ⟨hi, hps, hmp, hti, hvl, hcs, hph⟩ := hinv
    have hsb_eq : (if io.sideBit = 0 then 0 else 1) = if io.side then 1 else 0 := by
      unfold SlotIoLayout.side; by_cases hz : io.sideBit = 0 <;> simp [hz]
    rw [hsb_eq]
    obtain ⟨_, hu_eq, hvirt⟩ :=
      pageWriteVirtBoundedProg_spec hvIo hi hps hmp hti io.side (hvl.symm ▸ hidx) hq hv
    dsimp only [PageArenaLayout.toCtx] at hu_eq hvirt
    refine ⟨by rw [hu_eq]; exact ⟨hi, hps, hmp, hti, hvl, hcs, hph⟩,
      fun idx₂ hidx₂ => ?_, fun _ => ⟨hu_eq, fun idx₂ hidx₂ => ?_⟩⟩
    · unfold slotIoPairAt; rw [ite_eq_right h0, ite_eq_right h0]
      have h1 := hvirt io.side idx₂ (hvl.symm ▸ hidx₂)
      simpa only [true_and] using h1
    · have hne_s : io.partner.side ≠ io.side := by
        rw [SlotIoLayout.partner_side]; cases io.side <;> decide
      have hnot_p : ¬(io.partner.side = io.side ∧ idx₂ = idx) := fun hp => hne_s hp.1
      have h1 := hvirt io.partner.side idx₂ hidx₂
      rw [ite_eq_right hnot_p] at h1
      unfold slotIoPairAt
      have hp0 : io.partner.usePaged ≠ 0 := h0
      rw [ite_eq_right hp0, ite_eq_right hp0, SlotIoLayout.partner_pgL]
      exact h1

/-- Raw tuple primitive swapping virtual slots `p₁` and `p₂` in `SlotIoCtx` (`¬ReadsWidth`). -/
@[expose] def slotIoSwapRawProg : SlotIoCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (ctx, (p₁, p₂)) =>
    if p₁ = p₂ then
      pure ()
    else do
      let qv₁ ← slotIoReadRawProg (ctx, p₁)
      let qv₂ ← slotIoReadRawProg (ctx, p₂)
      slotIoWriteRawProg ((ctx, p₁), qv₂)
      slotIoWriteRawProg ((ctx, p₂), qv₁)

/-- Swap virtual slots `p₁` and `p₂` in `io : SlotIoLayout` (`¬ReadsWidth`). -/
@[expose] def slotIoSwapProg (io : SlotIoLayout) (p₁ p₂ : ℕ) : Memory.Prog Unit :=
  slotIoSwapRawProg (io.toCtx, (p₁, p₂))

theorem realizesBounded_slotIoSwapRaw :
    RealizesBounded .exact slotIoSwapRawProg
      (WordEncoding.encode (α := SlotIoCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (SlotIoLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrr := realizesBounded_slotIoReadRaw
  have hwr := realizesBounded_slotIoWriteRaw
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨p₁, p₂⟩⟩
    have hv0 := h
    have hctx : (SlotIoLayout.ofCtx ctx).toCtx = ctx := SlotIoLayout.toCtx_ofCtx ctx
    have hfr_r1 := (slotIoReadProg_frame (SlotIoLayout.ofCtx ctx) p₁).frontier_eq s
    have hfr_r2 := (slotIoReadProg_frame (SlotIoLayout.ofCtx ctx) p₂).frontier_eq
      ((Memory.spec 0).clientState s (slotIoReadRawProg (ctx, p₁)))
    unfold slotIoReadProg at hfr_r1 hfr_r2
    rw [hctx] at hfr_r1 hfr_r2)
  · exact hv0
  · simpa only [StateTransitionSpec.clientState, hfr_r1] using hv0
  · simpa only [StateTransitionSpec.clientState, hfr_r2, hfr_r1] using hv0
  · have hw_pos := hv0.w_pos
    set s₂ := (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s (slotIoReadRawProg (ctx, p₁)))
      (slotIoReadRawProg (ctx, p₂))
    set qv₂ := (Memory.spec 0).clientResult
      ((Memory.spec 0).clientState s (slotIoReadRawProg (ctx, p₁)))
      (slotIoReadRawProg (ctx, p₂))
    have hfr_w1 := (slotIoWriteProg_frame (io := SlotIoLayout.ofCtx ctx) hw_pos
      p₁ qv₂.1 qv₂.2).frontier_eq s₂
    unfold slotIoWriteProg at hfr_w1
    rw [hctx] at hfr_w1
    simpa only [StateTransitionSpec.clientState, hfr_w1, s₂, hfr_r2, hfr_r1] using hv0

theorem slotIoSwapProg_frame {io : SlotIoLayout} (hw : 0 < io.pgL.w) (p₁ p₂ : ℕ) :
    BoundedFrameProg io.OwnsAddr 88 (slotIoSwapProg io p₁ p₂) := by
  unfold slotIoSwapProg slotIoSwapRawProg; dsimp only
  refine BoundedFrameProg.ite_prog (p₁ = p₂)
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (C₂ := 88) (fun _ h => h) (by decide))
    fun _ => ?_
  exact BoundedFrameProg.bind_prog (slotIoReadProg_frame io p₁) fun qv₁ =>
    BoundedFrameProg.bind_prog (slotIoReadProg_frame io p₂) fun qv₂ =>
    BoundedFrameProg.bind_prog (slotIoWriteProg_frame hw p₁ qv₂.1 qv₂.2) fun _ =>
    slotIoWriteProg_frame hw p₂ qv₁.1 qv₁.2

theorem slotIoSwapProg_spec {io : SlotIoLayout} {nSide slack p₁ p₂ : ℕ} {s : Memory.State}
    (hvIo : io.Valid io.pgL.w s.frontier)
    (hinv : io.StateInv nSide slack s.mem) (hp₁ : p₁ < nSide) (hp₂ : p₂ < nSide) :
    let s' := (Memory.spec 0).clientState s (slotIoSwapProg io p₁ p₂)
    io.StateInv nSide slack s'.mem ∧
    (∀ idx < nSide,
      slotIoPairAt io s'.mem idx = (PhysSwap.mk p₁ p₂).apply (slotIoPairAt io s.mem) idx) ∧
    (io.usePaged ≠ 0 →
      extractPageUnperm io.pgL s'.mem = extractPageUnperm io.pgL s.mem ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) := by
  dsimp only
  unfold slotIoSwapProg slotIoSwapRawProg; dsimp only
  by_cases heq : p₁ = p₂
  · rw [ite_eq_left heq]
    have hpure : (Memory.spec 0).clientState s (pure ()) = s := rfl
    rw [hpure]
    refine ⟨hinv, fun idx _ => ?_, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
    simp [PhysSwap.apply, heq]
  · rw [ite_eq_right heq]
    obtain ⟨hr1_res, hr1_st⟩ := slotIoReadProg_spec hinv hp₁
    obtain ⟨hr2_res, hr2_st⟩ := slotIoReadProg_spec hinv hp₂
    unfold slotIoReadProg at hr1_res hr1_st hr2_res hr2_st
    obtain ⟨hq1, hv1⟩ := slotIoPairAt_bounds (io := io) s.mem p₁
    obtain ⟨hq2, hv2⟩ := slotIoPairAt_bounds (io := io) s.mem p₂
    set qv₁ := slotIoPairAt io s.mem p₁
    set qv₂ := slotIoPairAt io s.mem p₂
    obtain ⟨hinv₁, harr₁, hpart₁⟩ := slotIoWriteProg_spec hvIo hinv hp₁ hq2 hv2
    set s₁ := (Memory.spec 0).clientState s (slotIoWriteProg io p₁ qv₂.1 qv₂.2)
    have hfr₁ : s₁.frontier = s.frontier :=
      (slotIoWriteProg_frame hvIo.w_pos p₁ qv₂.1 qv₂.2).frontier_eq s
    obtain ⟨hinv₂, harr₂, hpart₂⟩ := slotIoWriteProg_spec (hfr₁.symm ▸ hvIo) hinv₁ hp₂ hq1 hv1
    have hst_tot : (Memory.spec 0).clientState s
        (slotIoReadRawProg (io.toCtx, p₁) >>= fun x₁ =>
          slotIoReadRawProg (io.toCtx, p₂) >>= fun x₂ =>
          slotIoWriteRawProg ((io.toCtx, p₁), x₂) >>= fun _ =>
          slotIoWriteRawProg ((io.toCtx, p₂), x₁)) =
        (Memory.spec 0).clientState s₁ (slotIoWriteProg io p₂ qv₁.1 qv₁.2) := by
      rw [StateTransitionSpec.clientState_bind, hr1_st, hr1_res,
        StateTransitionSpec.clientState_bind, hr2_st, hr2_res,
        StateTransitionSpec.clientState_bind]
      rfl
    rw [hst_tot]
    refine ⟨hinv₂, fun idx hidx => ?_, fun hnz => ?_⟩
    · rw [harr₂ idx hidx]
      by_cases hi2 : idx = p₂
      · subst hi2; rw [ite_eq_left rfl, PhysSwap.apply_p₂]
      · rw [ite_eq_right hi2, harr₁ idx hidx]
        by_cases hi1 : idx = p₁
        · subst hi1; rw [ite_eq_left rfl, PhysSwap.apply_p₁]
        · rw [ite_eq_right hi1, PhysSwap.apply_of_ne _ _ hi1 hi2]
    · obtain ⟨hu1, hp1_eq⟩ := hpart₁ hnz
      have hvl_p1 : (extractPagePair io.pgL s₁.mem).virtLen io.partner.side =
          (extractPagePair io.pgL s.mem).virtLen io.partner.side :=
        congrArg (fun u => u.st.virtLen io.partner.side) hu1
      obtain ⟨hu2, hp2_eq⟩ := hpart₂ hnz
      exact ⟨hu2.trans hu1, fun idx hidx =>
        (hp2_eq idx (hvl_p1.symm ▸ hidx)).trans (hp1_eq idx hidx)⟩

/-- Raw tuple primitive appending `(q, v)` at `nSide` in `SlotIoCtx` (`¬ReadsWidth`). -/
@[expose] def slotIoAppendRawProg : (SlotIoCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((up, sb), ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))), nSide), qv) =>
    if up = 0 then
      if nSide < nc then
        if sb = 0 then
          writePairGenProg ((((ib, (qb, vb)), wv), nSide), qv)
        else do
          let sp ← Memory.read mb
          if nSide < sp then
            writePairGenProg ((((od, (qb, vb)), wv), nSide), qv)
          else
            writePairGenProg ((((ib, (ot, vb)), wv), nSide), qv)
      else
        pure ()
    else do
      let pctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
      let sb01 ← pure (if sb = 0 then 0 else 1)
      let c16 ← pure 16
      pageAppendBoundedProg ((pctx, sb01), c16)
      pageWriteVirtBoundedProg ((pctx, (sb01, nSide)), qv)

/-- Append `(q, v)` at `nSide` in `io : SlotIoLayout`, running `16` page-rebalance ticks when
`usePaged ≠ 0` (`¬ReadsWidth`). -/
@[expose] def slotIoAppendProg (io : SlotIoLayout) (nSide q v : ℕ) : Memory.Prog Unit :=
  slotIoAppendRawProg ((io.toCtx, nSide), (q, v))

theorem realizesBounded_slotIoAppendRaw :
    RealizesBounded .exact slotIoAppendRawProg
      (WordEncoding.encode (α := (SlotIoCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (SlotIoLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwp := realizesBounded_writePairGen
  have hap := realizesBounded_pageAppend
  have hwv := realizesBounded_pageWriteVirt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩,
      ⟨⟨qb, vb⟩, nc⟩⟩⟩, nSide⟩, qv⟩
    unfold SlotIoLayout.Valid SlotIoLayout.ofCtx at h
    dsimp only at *)
  all_goals (
    try (simp only [‹up = 0›, ↓reduceIte] at h
         obtain ⟨hw, hw_eq, hqb, hvb, _, htail⟩ := h
         subst hw_eq
         first
         | (simp only [‹sb = 0›, ↓reduceIte] at htail
            have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw
              ‹nSide < nc›
            exact ⟨hw, rfl, hqb, hvb, by omega⟩)
         | (simp only [‹¬sb = 0›, ↓reduceIte] at htail
            obtain ⟨hq_ot, hot_w, hmb_od, hod_ib, hib_fr⟩ := htail
            have hfr_w := hmem.1
            have hw_lt : pairStreamWords nc qb vb w ≤ pairStreamWords nc ot vb w :=
              pairStreamWords_mono_qBits hq_ot
            first
            | (dsimp only [Fits] at hfr_w ⊢; omega)
            | (have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw
                 ‹nSide < nc›
               exact ⟨hw, rfl, hqb, hvb, by omega⟩)
            | (have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := ot) (v_bits := vb) hw
                 ‹nSide < nc›
               exact ⟨hw, rfl, hot_w, hvb, by omega⟩))))
  all_goals (
    simp only [‹¬up = 0›, ↓reduceIte] at h
    dsimp only [PageArenaLayout.ofCtx] at h ⊢
    have hv0 := h
    unfold PageArenaLayout.Valid at h; dsimp only at h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, _, _, _, _⟩ := h
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have h16_w : 16 < 2 ^ w := lt_of_lt_of_le (by omega : 16 < 2 ^ pb) hpow)
  · dsimp only [Fits]; omega
  · dsimp only [Fits]; exact h16_w
  · exact hv0
  · set L : PageArenaLayout := ⟨mb, od, ot, pb, wv, pg, mp, ib, qb, vb, nc⟩
    have hwL : 0 < L.w := by dsimp only [L]; omega
    have hfr_ap := (pageAppendBoundedProg_frame (L := L) hwL
      (if sb = 0 then 0 else 1) 16).frontier_eq s
    dsimp only [L, PageArenaLayout.toCtx] at hfr_ap
    simpa only [StateTransitionSpec.clientState, hfr_ap] using hv0

theorem slotIoAppendProg_frame {io : SlotIoLayout} (hw : 0 < io.pgL.w) (nSide q v : ℕ) :
    BoundedFrameProg io.OwnsAddr 1400 (slotIoAppendProg io nSide q v) := by
  unfold slotIoAppendProg slotIoAppendRawProg SlotIoLayout.OwnsAddr
  dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  by_cases h0 : io.usePaged = 0
  · simp only [h0, ↓reduceIte]
    by_cases hs : io.sideBit = 0
    · simp only [hs, ↓reduceIte]
      exact BoundedFrameProg.ite_prog (nSide < io.pgL.nCap)
        (fun hp => (BoundedFrameProg.writePairGen_prog hw hp
          (fun _ h1 h2 => ⟨h1, h2⟩)).mono (C₂ := 1400) (fun _ h => h) (by decide))
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (C₂ := 1400) (fun _ h => h) (by decide))
    · simp only [hs, ↓reduceIte]
      exact BoundedFrameProg.ite_prog (nSide < io.pgL.nCap)
        (fun hp => (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun sp =>
          BoundedFrameProg.ite_prog (nSide < sp)
            (fun _ => (BoundedFrameProg.writePairGen_prog hw hp
              (fun _ h1 h2 => Or.inr (Or.inl ⟨h1, h2⟩))).mono (C₂ := 8) (fun _ h => h) le_rfl)
            (fun _ => (BoundedFrameProg.writePairGen_prog hw hp
              (fun _ h1 h2 => Or.inr (Or.inr ⟨h1, h2⟩))).mono (C₂ := 8) (fun _ h => h) le_rfl)).mono
          (C₂ := 1400) (fun _ h => h) (by decide))
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (C₂ := 1400) (fun _ h => h) (by decide))
  · simp only [h0, ↓reduceIte, pure_bind]
    exact (BoundedFrameProg.bind_prog
      (pageAppendBoundedProg_frame hw (if io.sideBit = 0 then 0 else 1) 16) fun _ =>
      pageWriteVirtBoundedProg_frame hw (if io.sideBit = 0 then 0 else 1) nSide q v).mono
      (C₂ := 1400) (fun _ h => h) (by omega)

theorem slotIoAppendProg_spec {io : SlotIoLayout} {nSide q v : ℕ} {s : Memory.State}
    (hvIo : io.Valid io.pgL.w s.frontier)
    (hinv : io.StateInv nSide 0 s.mem)
    (hcap : if io.usePaged = 0 then nSide + 1 ≤ io.pgL.nCap
      else (extractPagePair io.pgL s.mem).totalItems + 1 ≤ io.pgL.nCap)
    (hq : q < 2 ^ io.pgL.qBits) (hv : v < 2 ^ io.pgL.vBits) :
    let s' := (Memory.spec 0).clientState s (slotIoAppendProg io nSide q v)
    let slack' :=
      if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
    io.StateInv (nSide + 1) slack' s'.mem ∧
    (∀ idx < nSide + 1,
      slotIoPairAt io s'.mem idx = if idx = nSide then (q, v) else slotIoPairAt io s.mem idx) ∧
    (io.usePaged ≠ 0 →
      (extractPagePair io.pgL s'.mem).virtLen io.partner.side =
        (extractPagePair io.pgL s.mem).virtLen io.partner.side ∧
      (extractPagePair io.pgL s'.mem).totalItems =
        (extractPagePair io.pgL s.mem).totalItems + 1 ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) := by
  dsimp only
  unfold slotIoAppendProg slotIoAppendRawProg SlotIoLayout.StateInv
  unfold SlotIoLayout.Valid at hvIo
  unfold SlotIoLayout.StateInv at hinv
  dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  by_cases h0 : io.usePaged = 0
  · simp only [h0, ↓reduceIte] at hvIo hinv hcap ⊢
    obtain ⟨hw, _, _, _, _, htail⟩ := hvIo
    have hlt : nSide < io.pgL.nCap := by omega
    rw [ite_eq_left hlt]
    by_cases hs : io.sideBit = 0
    · rw [ite_eq_left hs, clientState_writePairGenProg]
      refine ⟨⟨hcap, hinv.2⟩, fun idx _ => ?_, fun hne => absurd rfl hne⟩
      unfold slotIoPairAt arenaPairAt
      rw [ite_eq_left h0, ite_eq_left h0, ite_eq_left hs, ite_eq_left hs]
      by_cases heq : idx = nSide
      · subst heq; rw [ite_eq_left rfl]
        exact Prod.ext (pairQuotAt_writePair_self hw s.mem hq) (pairValAt_writePair_self s.mem hv)
      · rw [ite_eq_right heq]
        exact Prod.ext (pairQuotAt_writePair_of_ne hw s.mem heq)
          (pairValAt_writePair_of_ne hw s.mem heq)
    · rw [ite_eq_right hs] at htail ⊢
      obtain ⟨hq_ot, hot_w, hmb_od, hod_ib, _⟩ := htail
      have hrd_st : (Memory.spec 0).clientState s (Memory.read io.pgL.metaBase) = s := rfl
      have hrd_res : (Memory.spec 0).clientResult s (Memory.read io.pgL.metaBase) =
          s.mem io.pgL.metaBase := rfl
      rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res]
      have hmem_ite : ((Memory.spec 0).clientState s
          (if nSide < s.mem io.pgL.metaBase then
            writePairGenProg
              ((((io.pgL.offDir, (io.pgL.qBits, io.pgL.vBits)), io.pgL.w), nSide), (q, v))
          else
            writePairGenProg
              ((((io.pgL.itemBase, (io.pgL.offTail, io.pgL.vBits)), io.pgL.w),
                nSide), (q, v)))).mem =
          splitPairWrite io.splitCfg (s.mem io.pgL.metaBase) s.mem nSide q v := by
        unfold splitPairWrite SlotIoLayout.splitCfg; dsimp only
        by_cases hsp : nSide < s.mem io.pgL.metaBase <;>
          simp only [hsp, ↓reduceIte] <;> rw [clientState_writePairGenProg]
      have hmb_fix : splitPairWrite io.splitCfg (s.mem io.pgL.metaBase) s.mem nSide q v
          io.pgL.metaBase = s.mem io.pgL.metaBase := by
        unfold splitPairWrite SlotIoLayout.splitCfg; dsimp only
        split_ifs
        · exact writePair_outside hw hlt s.mem (fun h => by omega)
        · exact writePair_outside hw hlt s.mem (fun h => by omega)
      refine ⟨⟨hcap, hinv.2⟩, fun idx _ => ?_, fun hne => absurd rfl hne⟩
      unfold slotIoPairAt
      rw [ite_eq_left h0, ite_eq_left h0, ite_eq_right hs, ite_eq_right hs, hmem_ite, hmb_fix]
      by_cases heq : idx = nSide
      · subst heq; rw [ite_eq_left rfl]
        have hq' : q < 2 ^ (if idx < s.mem io.pgL.metaBase then
            io.splitCfg.qBitsLo else io.splitCfg.qBitsHi) := by
          dsimp only [SlotIoLayout.splitCfg]; split_ifs
          · exact hq
          · exact hq.trans_le (Nat.pow_le_pow_right two_pos hq_ot)
        have hv' : v < 2 ^ (if idx < s.mem io.pgL.metaBase then
            io.splitCfg.vBitsLo else io.splitCfg.vBitsHi) := by
          dsimp only [SlotIoLayout.splitCfg]; split_ifs <;> exact hv
        rw [splitPairRead_splitPairWrite_self (cfg := io.splitCfg) hw s.mem hq' hv']
        exact Prod.ext (Nat.mod_eq_of_lt hq) rfl
      · rw [ite_eq_right heq, splitPairRead_splitPairWrite_of_ne (cfg := io.splitCfg) hw
          (by dsimp only [SlotIoLayout.splitCfg]; omega) hod_ib s.mem heq]
  · simp only [h0, false_or, ↓reduceIte, pure_bind] at hvIo hinv hcap ⊢
    obtain ⟨hi, hps, hmp, _, hvl, hcs, hph⟩ := hinv
    have hsb_eq : (if io.sideBit = 0 then 0 else 1) = if io.side then 1 else 0 := by
      unfold SlotIoLayout.side; by_cases hz : io.sideBit = 0 <;> simp [hz]
    rw [StateTransitionSpec.clientState_bind, hsb_eq]
    obtain ⟨hfr_ap, hu_ap, har_ap⟩ := pageAppendBoundedProg_spec hvIo hi hps hcap hcs hph
    obtain ⟨hi_ap, _, hps_ap, hvl_ap, hvl_oth, hti_ap, _, _, hvirt_ap⟩ :=
      PageUnpermState.appendSlot_spec hi hcs hph
    set s₁ := (Memory.spec 0).clientState s
      (pageAppendBoundedProg ((io.pgL.toCtx, if io.side then 1 else 0), 16))
    have hst_ap : extractPagePair io.pgL s₁.mem =
        ((extractPageUnperm io.pgL s.mem).appendSlot io.side).1.st :=
      congrArg PageUnpermState.st hu_ap
    have hps₁ : (extractPagePair io.pgL s₁.mem).pageSize = io.pgL.pgB :=
      hst_ap.symm ▸ hps_ap.trans hps
    have hti₁ : (extractPagePair io.pgL s₁.mem).totalItems ≤ io.pgL.nCap := by
      rw [hst_ap, hti_ap]; exact hcap
    have hmp₁ : (extractPagePair io.pgL s₁.mem).totalPages < io.pgL.maxPages := by
      have ⟨_, _, _, _, _, hpg32, _, _, _, hnc_mp, _, _, _, _, _⟩ := hvIo
      have hti_eq := (extractPagePair io.pgL s₁.mem).totalItems_eq
      rw [hps₁] at hti_eq
      have hle : (extractPagePair io.pgL s₁.mem).totalPages * io.pgL.pgB ≤
          (io.pgL.maxPages - 2) * io.pgL.pgB := by omega
      have htp_le := (Nat.mul_le_mul_right_iff (by omega : 0 < io.pgL.pgB)).mp hle
      omega
    have hvl₁ : (extractPagePair io.pgL s₁.mem).virtLen io.side = nSide + 1 := by
      rw [hst_ap, hvl_ap, hvl]
    have hidx₁ : nSide < (extractPagePair io.pgL s₁.mem).virtLen io.side := by omega
    obtain ⟨_, hu_wv, hvirt_wv⟩ := pageWriteVirtBoundedProg_spec (hfr_ap.symm ▸ hvIo)
      (hu_ap.symm ▸ hi_ap) hps₁ hmp₁ hti₁ io.side hidx₁ hq hv
    dsimp only [PageArenaLayout.toCtx] at hu_wv hvirt_wv ⊢
    have hph_lt₁ : (extractPageUnperm io.pgL s₁.mem).cleanPhase < 4 := by
      rw [hu_ap]
      unfold PageUnpermState.appendSlot
      split_ifs <;> dsimp only <;> try omega
      split_ifs <;> decide
    have hcs₁ : 0 < (extractPageUnperm io.pgL s₁.mem).cleanPhase → io.side = true := by
      rw [hu_ap]
      unfold PageUnpermState.appendSlot
      by_cases hp0 : (extractPageUnperm io.pgL s.mem).cleanPhase = 0
      · rw [ite_eq_left hp0]; intro h; exact absurd h (Nat.lt_irrefl 0)
      · intro _; exact hcs (Nat.pos_of_ne_zero hp0)
    have hne_side : io.partner.side ≠ io.side := by
      rw [SlotIoLayout.partner_side]; cases io.side <;> decide
    have hvl_p : (extractPagePair io.pgL s₁.mem).virtLen io.partner.side =
        (extractPagePair io.pgL s.mem).virtLen io.partner.side := by
      rw [hst_ap]; exact hvl_oth io.partner.side hne_side
    refine ⟨?_, fun idx hidx => ?_, fun _ => ?_⟩
    · rw [hu_wv]
      exact ⟨hu_ap.symm ▸ hi_ap, hps₁, hmp₁, hti₁, hvl₁, hcs₁, hph_lt₁⟩
    · unfold slotIoPairAt; rw [ite_eq_right h0, ite_eq_right h0]
      have hw1 := hvirt_wv io.side idx (hvl₁.symm ▸ hidx)
      simp only [true_and] at hw1
      rw [hw1]
      by_cases heq : idx = nSide
      · rw [ite_eq_left heq, ite_eq_left heq]
      · rw [ite_eq_right heq, ite_eq_right heq, hu_ap, har_ap]
        have ha1 := hvirt_ap (arenaPairAt io.pgL s.mem) io.side idx
          (by rw [hvl_ap, hvl]; exact hidx)
        have hnot :
            ¬(io.side = io.side ∧ idx = (extractPageUnperm io.pgL s.mem).st.virtLen io.side) :=
          fun h => heq (h.2.trans hvl)
        rwa [ite_eq_right hnot] at ha1
    · have hst_wv : extractPagePair io.pgL
          ((Memory.spec 0).clientState s₁
            (pageWriteVirtBoundedProg
              ((((((io.pgL.metaBase, io.pgL.offDir), (io.pgL.offTail, io.pgL.ptrB)),
                ((io.pgL.w, io.pgL.pgB), (io.pgL.maxPages, io.pgL.itemBase))),
                ((io.pgL.qBits, io.pgL.vBits), io.pgL.nCap)),
                (if io.side then 1 else 0, nSide)), (q, v)))).mem =
          extractPagePair io.pgL s₁.mem :=
        congrArg PageUnpermState.st hu_wv
      refine ⟨by rw [hst_wv, hvl_p], by rw [hst_wv, hst_ap, hti_ap]; rfl, fun idx hidx => ?_⟩
      have hnot_p : ¬(io.partner.side = io.side ∧ idx = nSide) := fun hp => hne_side hp.1
      have hw1 := hvirt_wv io.partner.side idx (hvl_p.symm ▸ hidx)
      rw [ite_eq_right hnot_p] at hw1
      unfold slotIoPairAt
      have hp0 : io.partner.usePaged ≠ 0 := h0
      rw [ite_eq_right hp0, ite_eq_right hp0, SlotIoLayout.partner_pgL, hw1, hu_ap, har_ap]
      have ha1 := hvirt_ap (arenaPairAt io.pgL s.mem) io.partner.side idx
        (by rw [hvl_oth _ hne_side]; exact hidx)
      have hnot_p2 :
          ¬(io.partner.side = io.side ∧
            idx = (extractPageUnperm io.pgL s.mem).st.virtLen io.side) :=
        fun hp => hne_side hp.1
      rwa [ite_eq_right hnot_p2] at ha1

/-- Raw tuple primitive popping virtual slot `nSide - 1` from `SlotIoCtx` (`¬ReadsWidth`). -/
@[expose] def slotIoPopBackRawProg : SlotIoCtx → Memory.Prog Unit
  | ((up, sb), pctx) =>
    if up = 0 then
      pure ()
    else do
      let sb01 ← pure (if sb = 0 then 0 else 1)
      let c16 ← pure 16
      pagePopBackBoundedProg ((pctx, sb01), c16)

/-- Pop virtual slot `nSide - 1` from `io : SlotIoLayout` (`16` page-rebalance ticks when
`usePaged ≠ 0`, no-op on the direct pair stream when `usePaged = 0`, `¬ReadsWidth`). -/
@[expose] def slotIoPopBackProg (io : SlotIoLayout) : Memory.Prog Unit :=
  slotIoPopBackRawProg io.toCtx

theorem realizesBounded_slotIoPopBackRaw :
    RealizesBounded .exact slotIoPopBackRawProg
      (WordEncoding.encode (α := SlotIoCtx))
      (WordEncoding.encode (α := Unit))
      (fun w ctx s => (SlotIoLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hpb := realizesBounded_pagePopBack
  realize
  all_goals (
    rcases d with ⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩
    unfold SlotIoLayout.Valid SlotIoLayout.ofCtx at h
    dsimp only [PageArenaLayout.ofCtx] at *
    simp only [‹¬up = 0›, ↓reduceIte] at h
    have hv0 := h
    unfold PageArenaLayout.Valid at h; dsimp only at h
    obtain ⟨_, _, hpb, _, _, hpg32, hpg16, _, _, _, _, _, _, _, _⟩ := h
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    dsimp only [Fits] at *
    first | exact hv0 | omega)

theorem slotIoPopBackProg_frame {io : SlotIoLayout} (hw : 0 < io.pgL.w) :
    BoundedFrameProg io.OwnsAddr 1400 (slotIoPopBackProg io) := by
  unfold slotIoPopBackProg slotIoPopBackRawProg SlotIoLayout.OwnsAddr
  dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  by_cases h0 : io.usePaged = 0
  · simp only [h0, ↓reduceIte]
    exact (BoundedFrameProg.pure_prog ()).mono (C₂ := 1400) (fun _ h => h) (by decide)
  · simp only [h0, ↓reduceIte, pure_bind]
    exact (pagePopBackBoundedProg_frame hw (if io.sideBit = 0 then 0 else 1) 16).mono
      (C₂ := 1400) (fun _ h => h) (by omega)

private theorem popBackSlot_cleanPhase (u : PageUnpermState) (sd : Bool)
    (hlt : u.cleanPhase < 4) (hsd : 0 < u.cleanPhase → sd = true) :
    (u.popBackSlot sd).1.cleanPhase < 4 ∧
    (0 < (u.popBackSlot sd).1.cleanPhase → sd = true) := by
  unfold PageUnpermState.popBackSlot
  rcases u.st.stepPopBack sd with ⟨st1, sw1⟩
  rcases u.st.rawPopBack sd with ⟨st2, sw2⟩
  by_cases hp0 : u.cleanPhase = 0
  · simp [hp0]
  · have hs_eq := hsd (Nat.pos_of_ne_zero hp0)
    refine ⟨?_, fun _ => hs_eq⟩
    rw [ite_eq_right hp0]
    split_ifs <;> dsimp only <;> [split_ifs <;> decide; decide; exact hlt]

theorem slotIoPopBackProg_spec {io : SlotIoLayout} {nSide : ℕ} {s : Memory.State}
    (hvIo : io.Valid io.pgL.w s.frontier)
    (hinv : io.StateInv nSide 0 s.mem) (hpos : 0 < nSide) :
    let s' := (Memory.spec 0).clientState s (slotIoPopBackProg io)
    let slack' :=
      if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
    io.StateInv (nSide - 1) slack' s'.mem ∧
    (∀ idx < nSide - 1, slotIoPairAt io s'.mem idx = slotIoPairAt io s.mem idx) ∧
    (io.usePaged ≠ 0 →
      (extractPagePair io.pgL s'.mem).virtLen io.partner.side =
        (extractPagePair io.pgL s.mem).virtLen io.partner.side ∧
      (extractPagePair io.pgL s'.mem).totalItems =
        (extractPagePair io.pgL s.mem).totalItems - 1 ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) := by
  intro s' slack'
  by_cases h0 : io.usePaged = 0
  · have hs' : s' = s := by
      change (Memory.spec 0).clientState s (slotIoPopBackProg io) = s
      unfold slotIoPopBackProg slotIoPopBackRawProg SlotIoLayout.toCtx
      simp only [h0, ↓reduceIte]
      rfl
    have hsl : slack' = 0 := by simp [slack', h0]
    rw [hs', hsl]
    unfold SlotIoLayout.StateInv at hinv ⊢
    rw [ite_eq_left h0] at hinv ⊢
    exact ⟨⟨Nat.sub_le_of_le_add (hinv.1.trans (Nat.le_add_right _ _)), hinv.2⟩,
      fun _ _ => rfl, fun hne => absurd h0 hne⟩
  · have hvL : io.pgL.Valid io.pgL.w s.frontier := by
      unfold SlotIoLayout.Valid at hvIo; rwa [ite_eq_right h0] at hvIo
    unfold SlotIoLayout.StateInv at hinv
    rw [ite_eq_right h0] at hinv
    obtain ⟨hi, hps, hmp, hti, hvl, hcs, hph⟩ := hinv
    have hsb_eq : (if io.sideBit = 0 then 0 else 1) = if io.side then 1 else 0 := by
      unfold SlotIoLayout.side; by_cases hz : io.sideBit = 0 <;> simp [hz]
    have hs'_eq : s' = (Memory.spec 0).clientState s
        (pagePopBackBoundedProg ((io.pgL.toCtx, if io.side then 1 else 0), 16)) := by
      change (Memory.spec 0).clientState s (slotIoPopBackProg io) = _
      unfold slotIoPopBackProg slotIoPopBackRawProg SlotIoLayout.toCtx
      simp only [h0, ↓reduceIte, pure_bind, hsb_eq]
    have hsl : slack' = if (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24 := by
      simp [slack', h0]
    have hpos_vl : 0 < (extractPagePair io.pgL s.mem).virtLen io.side := hvl.symm ▸ hpos
    obtain ⟨_, hu_pb, har_pb⟩ := pagePopBackBoundedProg_spec hvL hi hps hti hpos_vl hcs hph
    rw [← hs'_eq] at hu_pb har_pb
    obtain ⟨hi_pb, _, hps_pb, hvl_pb, hvl_oth, hti_pb, _, _, hvirt_pb⟩ :=
      PageUnpermState.popBackSlot_spec.{0} hi hpos_vl hcs hph
    have hst_pb : extractPagePair io.pgL s'.mem =
        ((extractPageUnperm io.pgL s.mem).popBackSlot io.side).1.st :=
      congrArg PageUnpermState.st hu_pb
    have hst_pb_u : (extractPageUnperm io.pgL s'.mem).st =
        ((extractPageUnperm io.pgL s.mem).popBackSlot io.side).1.st := hst_pb
    have hps' : (extractPagePair io.pgL s'.mem).pageSize = io.pgL.pgB := by
      rw [hst_pb, hps_pb, hps]
    have hti' : (extractPagePair io.pgL s'.mem).totalItems ≤ io.pgL.nCap := by
      rw [hst_pb, hti_pb]; exact (Nat.sub_le _ 1).trans hti
    have hmp' : (extractPagePair io.pgL s'.mem).totalPages < io.pgL.maxPages := by
      have ⟨_, _, _, _, _, hpg32, _, _, _, hnc_mp, _, _, _, _, _⟩ := hvL
      have hti_eq := (extractPagePair io.pgL s'.mem).totalItems_eq
      rw [hps'] at hti_eq
      have hle : (extractPagePair io.pgL s'.mem).totalPages * io.pgL.pgB ≤
          (io.pgL.maxPages - 2) * io.pgL.pgB := by omega
      have htp_le := (Nat.mul_le_mul_right_iff (by omega : 0 < io.pgL.pgB)).mp hle
      omega
    obtain ⟨hph_lt_u, hcs_u⟩ := popBackSlot_cleanPhase (extractPageUnperm io.pgL s.mem)
      io.side hph hcs
    have hph_lt' : (extractPageUnperm io.pgL s'.mem).cleanPhase < 4 := by
      rw [hu_pb]; exact hph_lt_u
    have hcs' : 0 < (extractPageUnperm io.pgL s'.mem).cleanPhase → io.side = true := by
      rw [hu_pb]; exact hcs_u
    have hne_side : io.partner.side ≠ io.side := by
      rw [SlotIoLayout.partner_side]; cases io.side <;> decide
    have hi' : (extractPageUnperm io.pgL s'.mem).InvWithSlack slack' := by
      rw [hu_pb, hsl]; exact hi_pb
    have hsinv' : io.StateInv (nSide - 1) slack' s'.mem := by
      unfold SlotIoLayout.StateInv; rw [ite_eq_right h0]
      exact ⟨hi', hps', hmp', hti', by rw [hst_pb_u, hvl_pb, hvl], hcs', hph_lt'⟩
    refine ⟨hsinv', fun idx hidx => ?_,
      fun _ => ⟨by rw [hst_pb]; exact hvl_oth io.partner.side hne_side,
        by rw [hst_pb, hti_pb]; rfl, fun idx hidx => ?_⟩⟩
    · unfold slotIoPairAt; rw [ite_eq_right h0, ite_eq_right h0, hu_pb, har_pb]
      exact hvirt_pb (arenaPairAt io.pgL s.mem) io.side idx (by rw [hvl_pb, hvl]; exact hidx)
    · have ha1 := hvirt_pb (arenaPairAt io.pgL s.mem) io.partner.side idx
        (by rw [hvl_oth _ hne_side]; exact hidx)
      unfold slotIoPairAt
      have hp0 : io.partner.usePaged ≠ 0 := h0
      rw [ite_eq_right hp0, ite_eq_right hp0, SlotIoLayout.partner_pgL, hu_pb, har_pb]
      exact ha1

/-! ## Section 2: `BlockPoolLayout` Combining `BpMetaLayout` and `SlotIoLayout` -/

private theorem frontier_slotIoReadRawProg (x : SlotIoCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (slotIoReadRawProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, idx⟩
  have hf := (slotIoReadProg_frame (SlotIoLayout.ofCtx ctx) idx).frontier_eq s
  unfold slotIoReadProg at hf
  rwa [SlotIoLayout.toCtx_ofCtx] at hf

private theorem frontier_slotIoWriteRawProg
    (x : (SlotIoCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.1).pgL.w) :
    ((Memory.spec 0).runClient s (slotIoWriteRawProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, idx⟩, ⟨q, v⟩⟩
  have hf := (slotIoWriteProg_frame (io := SlotIoLayout.ofCtx ctx) hw idx q v).frontier_eq s
  unfold slotIoWriteProg at hf
  rwa [SlotIoLayout.toCtx_ofCtx] at hf

private theorem frontier_slotIoSwapRawProg
    (x : SlotIoCtx × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1).pgL.w) :
    ((Memory.spec 0).runClient s (slotIoSwapRawProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, ⟨p₁, p₂⟩⟩
  have hf := (slotIoSwapProg_frame (io := SlotIoLayout.ofCtx ctx) hw p₁ p₂).frontier_eq s
  unfold slotIoSwapProg at hf
  rwa [SlotIoLayout.toCtx_ofCtx] at hf

private theorem frontier_slotIoAppendRawProg
    (x : (SlotIoCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.1).pgL.w) :
    ((Memory.spec 0).runClient s (slotIoAppendRawProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, ns⟩, ⟨q, v⟩⟩
  have hf := (slotIoAppendProg_frame (io := SlotIoLayout.ofCtx ctx) hw ns q v).frontier_eq s
  unfold slotIoAppendProg at hf
  rwa [SlotIoLayout.toCtx_ofCtx] at hf

private theorem frontier_slotIoPopBackRawProg
    (ctx : SlotIoCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx ctx).pgL.w) :
    ((Memory.spec 0).runClient s (slotIoPopBackRawProg ctx)).2.1.frontier = s.frontier := by
  have hf := (slotIoPopBackProg_frame (io := SlotIoLayout.ofCtx ctx) hw).frontier_eq s
  unfold slotIoPopBackProg at hf
  rwa [SlotIoLayout.toCtx_ofCtx] at hf

/-- Combined descriptor pairing a `BpMetaLayout` with a `SlotIoLayout` (`0` projection chains). -/
structure BlockPoolLayout where
  /-- Block-pool metadata table layout (`scalars +1, +10..16`, `offBktMeta 0..4`, 4 directories). -/
  mp : BpMetaLayout
  /-- Underlying `[0, nSide)` pair-slot array (`usePaged = 0` or `usePaged ≠ 0`). -/
  io : SlotIoLayout

/-- Concrete `BlockPoolLayout` for a large epoch `(c, w, N)` at `metaBase` backed by `io`. -/
@[expose] def epochBlockPoolLayout (c w N metaBase : ℕ) (io : SlotIoLayout) : BlockPoolLayout :=
  ⟨epochBpMetaLayout c w N metaBase, io⟩

/-- Register-tuple encoding of `BlockPoolLayout` for `RealizesBounded` primitives. -/
abbrev BlockPoolCtx := BpMetaCtx × SlotIoCtx

/-- Pack `BlockPoolLayout` into `BlockPoolCtx`. -/
@[expose] def BlockPoolLayout.toCtx (bpL : BlockPoolLayout) : BlockPoolCtx :=
  (bpL.mp.toCtx, bpL.io.toCtx)

/-- Unpack `BlockPoolCtx` into `BlockPoolLayout`. -/
@[expose] def BlockPoolLayout.ofCtx : BlockPoolCtx → BlockPoolLayout
  | (mctx, ioctx) => ⟨BpMetaLayout.ofCtx mctx, SlotIoLayout.ofCtx ioctx⟩

@[simp] theorem BlockPoolLayout.ofCtx_toCtx (bpL : BlockPoolLayout) :
    BlockPoolLayout.ofCtx bpL.toCtx = bpL := by
  rcases bpL with ⟨mp, io⟩; simp [BlockPoolLayout.toCtx, BlockPoolLayout.ofCtx]

@[simp] theorem BlockPoolLayout.toCtx_ofCtx (ctx : BlockPoolCtx) :
    (BlockPoolLayout.ofCtx ctx).toCtx = ctx := by
  rcases ctx with ⟨mctx, ioctx⟩; simp [BlockPoolLayout.toCtx, BlockPoolLayout.ofCtx]

/-- Word-address footprint owned by `bpL`. -/
@[expose] def BlockPoolLayout.OwnsAddr (bpL : BlockPoolLayout) (addr : ℕ) : Prop :=
  bpL.mp.OwnsMetaAddr addr ∨ bpL.io.OwnsAddr addr

/-- Static frontier validity structure for `BlockPoolLayout` (named fields, `0` projection
chains, independent of `s.mem`). -/
structure BlockPoolLayout.Valid (bpL : BlockPoolLayout) (w frontier : ℕ) : Prop where
  mp_valid : bpL.mp.Valid w frontier
  io_valid : bpL.io.Valid w frontier
  w_eq_io : bpL.mp.w = bpL.io.pgL.w
  disjoint : ∀ addr, bpL.mp.OwnsMetaAddr addr → bpL.io.OwnsAddr addr → False

theorem BpMetaLayout.OwnsMetaAddr.bounds {mp : BpMetaLayout} {w fr addr : ℕ}
    (hv : mp.Valid w fr) (ha : mp.OwnsMetaAddr addr) :
    (addr = mp.metaBase + 1 ∨ (mp.metaBase + 10 ≤ addr ∧ addr < mp.metaBase + 17)) ∨
    (mp.metaBase + mp.offBktMeta ≤ addr ∧
      addr < mp.metaBase + mp.offTailOwner + packedWords (16 * mp.maxTail) mp.ptrB mp.w) := by
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  rcases ha with h1 | h10 | hbm | hsd | htd | hso | hto
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr h10)
  · exact Or.inr ⟨hbm.1, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, hto.2⟩

/-- `epochBlockPoolLayout c w N metaBase io` satisfies `BlockPoolLayout.Valid w frontier` in both
direct (`io.usePaged = 0`) and shared-arena (`io.usePaged ≠ 0`, hosted in the same epoch or a
disjoint partner epoch) modes. -/
theorem valid_epochBlockPoolLayout {c U w N metaBase frontier : ℕ} {io : SlotIoLayout}
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hio : io.Valid w frontier) (hw_io : io.pgL.w = w)
    (hm_ib : metaBase + epochMetaWordsWhp c w N ≤ io.pgL.itemBase)
    (hmeta_disj : io.usePaged ≠ 0 →
      (io.pgL.metaBase = metaBase ∧ offBTreeMeta c w N ≤ io.pgL.offDir) ∨
      io.pgL.metaBase + io.pgL.offTail + packedWords (16 * io.pgL.pgB) io.pgL.ptrB w ≤ metaBase ∨
      metaBase + offBTreeMeta c w N ≤ io.pgL.metaBase)
    (hsplit_disj : io.usePaged = 0 → io.sideBit ≠ 0 →
      io.pgL.metaBase < metaBase ∧ metaBase + epochMetaWordsWhp c w N ≤ io.pgL.offDir) :
    (epochBlockPoolLayout c w N metaBase io).Valid w frontier := by
  have hib_fr : io.pgL.itemBase ≤ frontier := by
    unfold SlotIoLayout.Valid at hio
    by_cases h0 : io.usePaged = 0
    · rw [ite_eq_left h0] at hio
      by_cases hs : io.sideBit = 0
      · rw [ite_eq_left hs] at hio; omega
      · rw [ite_eq_right hs] at hio; omega
    · rw [ite_eq_right h0] at hio; unfold PageArenaLayout.Valid at hio; omega
  have hmp : (epochBpMetaLayout c w N metaBase).Valid w frontier :=
    valid_epochBpMetaLayout hth hNU hU (hm_ib.trans hib_fr)
  have hend := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
  have hbt_le_end : offBTreeMeta c w N ≤ epochMetaWordsWhp c w N := by
    rw [← hend]
    unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals
      offBTreeKeys
    omega
  refine
    { mp_valid := hmp
      io_valid := hio
      w_eq_io := hw_io.symm
      disjoint := fun addr hma hia => ?_ }
  have hbds := BpMetaLayout.OwnsMetaAddr.bounds hmp hma
  dsimp only [epochBlockPoolLayout, epochBpMetaLayout] at hbds
  have hob : offTailOwner c w N + packedWords (16 * maxTailWhp N) (globalPtrBits N) w =
      offBTreeMeta c w N := rfl
  rw [Nat.add_assoc metaBase, hob] at hbds
  have ho32 : 32 ≤ offBktMeta c w N := hmp.offBktMeta_ge
  have hbm_le_bt : offBktMeta c w N ≤ offBTreeMeta c w N := by
    unfold offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir; omega
  have haddr_hi : addr < metaBase + offBTreeMeta c w N := by
    rcases hbds with (rfl | h10) | htab <;> omega
  change io.OwnsAddr addr at hia
  unfold SlotIoLayout.OwnsAddr at hia
  by_cases h0 : io.usePaged = 0
  · rw [ite_eq_left h0] at hia
    by_cases hs : io.sideBit = 0
    · rw [ite_eq_left hs] at hia; unfold PageArenaLayout.OwnsItemAddr at hia; omega
    · rw [ite_eq_right hs] at hia
      obtain ⟨hmb_lt, hm_od⟩ := hsplit_disj h0 hs
      rcases hia with rfl | hlo | hhi <;> omega
  · rw [ite_eq_right h0] at hia
    rcases hia with hpg_m | hpg_i
    · have hvL : io.pgL.Valid w frontier := by
        unfold SlotIoLayout.Valid at hio; rwa [ite_eq_right h0] at hio
      unfold PageArenaLayout.Valid at hvL
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hod32, hod_ot, _, _⟩ := hvL
      rw [hw_io] at hod_ot
      unfold PageArenaLayout.OwnsMetaAddr at hpg_m
      rw [hw_io] at hpg_m
      rcases hmeta_disj h0 with ⟨hmb_eq, hbt_od⟩ | hleft | hright
      · rw [hmb_eq] at hpg_m
        rcases hpg_m with h18 | hdir | htail
        · rcases hbds with (rfl | h10) | htab <;> omega
        · omega
        · omega
      · rcases hpg_m with h18 | hdir | htail <;>
          (rcases hbds with (rfl | h10) | htab <;> omega)
      · rcases hpg_m with h18 | hdir | htail <;> omega
    · unfold PageArenaLayout.OwnsItemAddr at hpg_i
      omega

/-- Frame predicate for `BlockPoolLayout` programs: modifies only `bpL.OwnsAddr`, preserves
`frontier`, costs `≤ C`, and preserves `offBktMeta` slots `5..15` owned by `LargeEpoch`. -/
structure BlockPoolProg {α : Type} (bpL : BlockPoolLayout) (C : ℕ) (p : Memory.Prog α) : Prop where
  frame : BoundedFrameProg bpL.OwnsAddr C p
  bkt_other :
    ∀ (s : Memory.State) (b slot : ℕ), b < bpL.mp.M → 5 ≤ slot → slot < 16 →
      readPacked (bpL.mp.metaBase + bpL.mp.offBktMeta) bpL.mp.ptrB bpL.mp.w
        ((Memory.spec 0).clientState s p).mem (16 * b + slot) =
      readPacked (bpL.mp.metaBase + bpL.mp.offBktMeta) bpL.mp.ptrB bpL.mp.w
        s.mem (16 * b + slot)

theorem BlockPoolProg.mono {α : Type} {bpL : BlockPoolLayout} {C₁ C₂ : ℕ} {p : Memory.Prog α}
    (h : BlockPoolProg bpL C₁ p) (hle : C₁ ≤ C₂) : BlockPoolProg bpL C₂ p :=
  ⟨h.frame.mono (fun _ ha => ha) hle, h.bkt_other⟩

theorem BlockPoolProg.pure_prog {α : Type} (bpL : BlockPoolLayout) (x : α) :
    BlockPoolProg bpL 0 (pure x) :=
  ⟨BoundedFrameProg.pure_prog x, fun _ _ _ _ _ _ => rfl⟩

theorem BlockPoolProg.bind_prog {α β : Type} {bpL : BlockPoolLayout} {C₁ C₂ : ℕ}
    {p : Memory.Prog α} {f : α → Memory.Prog β}
    (hp : BlockPoolProg bpL C₁ p) (hf : ∀ x, BlockPoolProg bpL C₂ (f x)) :
    BlockPoolProg bpL (C₁ + C₂) (p >>= f) where
  frame := BoundedFrameProg.bind_prog hp.frame (fun x => (hf x).frame)
  bkt_other s b slot hb hlo hhi := by
    rw [StateTransitionSpec.clientState_bind]
    exact ((hf _).bkt_other _ b slot hb hlo hhi).trans (hp.bkt_other s b slot hb hlo hhi)

theorem BlockPoolProg.ite_prog {α : Type} {bpL : BlockPoolLayout} {C : ℕ} (P : Prop) [Decidable P]
    {t e : Memory.Prog α} (ht : P → BlockPoolProg bpL C t) (he : ¬P → BlockPoolProg bpL C e) :
    BlockPoolProg bpL C (if P then t else e) where
  frame := BoundedFrameProg.ite_prog P (fun h => (ht h).frame) (fun h => (he h).frame)
  bkt_other s b slot hb hlo hhi := by
    by_cases hP : P
    · rw [ite_eq_left hP]; exact (ht hP).bkt_other s b slot hb hlo hhi
    · rw [ite_eq_right hP]; exact (he hP).bkt_other s b slot hb hlo hhi

theorem BlockPoolProg.of_meta {α : Type} {bpL : BlockPoolLayout} {C : ℕ} {p : Memory.Prog α}
    (hm : BpMetaProg bpL.mp C p) :
    BlockPoolProg bpL C p :=
  ⟨hm.frame.mono (fun _ ha => Or.inl ha) le_rfl, hm.bkt_other⟩

theorem BlockPoolProg.of_io {α : Type} {bpL : BlockPoolLayout} {C : ℕ} {p : Memory.Prog α}
    (hw : 0 < bpL.mp.w)
    (hdisj : ∀ addr, bpL.mp.OwnsMetaAddr addr → bpL.io.OwnsAddr addr → False)
    (hio : BoundedFrameProg bpL.io.OwnsAddr C p) :
    BlockPoolProg bpL C p where
  frame := hio.mono (fun _ ha => Or.inr ha) le_rfl
  bkt_other s b slot hb _ hhi :=
    readPacked_congr hw
      (fun addr ha =>
        hio.mem_outside s addr (fun hio_a =>
          hdisj addr (Or.inr (Or.inr (Or.inl ha))) hio_a))
      (by omega : 16 * b + slot < 16 * bpL.mp.M)

/-- Logical `(quotient, value)` pair at bucket `b`, intra-bucket index `loc` of `bpL`. -/
@[expose] def bpPairAt (bpL : BlockPoolLayout) (mem : ℕ → ℕ) (b loc : ℕ) : ℕ × ℕ :=
  slotIoPairAt bpL.io mem ((extractBlockPool bpL.mp mem).toPhys b loc)

theorem bpPairAt_bounds (bpL : BlockPoolLayout) (mem : ℕ → ℕ) (b loc : ℕ) :
    (bpPairAt bpL mem b loc).1 < 2 ^ bpL.io.pgL.qBits ∧
    (bpPairAt bpL mem b loc).2 < 2 ^ bpL.io.pgL.vBits :=
  slotIoPairAt_bounds mem _

/-- Dynamic memory invariant for `bpL`: `extractBlockPool bpL.mp mem` is `Balanced` with
`nSide ≤ bpL.mp.nCap`, and `bpL.io` holds `nSide` live virtual slots with `slack`. -/
@[expose] def BlockPoolLayout.StateInv (bpL : BlockPoolLayout) (slack : ℕ) (mem : ℕ → ℕ) : Prop :=
  (extractBlockPool bpL.mp mem).Balanced ∧
  (extractBlockPool bpL.mp mem).nSide ≤ bpL.mp.nCap ∧
  bpL.io.StateInv (extractBlockPool bpL.mp mem).nSide slack mem

theorem BlockPoolLayout.StateInv.mono_slack {bpL : BlockPoolLayout} {s₁ s₂ : ℕ} {mem : ℕ → ℕ}
    (h : bpL.StateInv s₁ mem) (hle : s₁ ≤ s₂) (hs₂ : s₂ ≤ 24) :
    bpL.StateInv s₂ mem :=
  ⟨h.1, h.2.1, h.2.2.mono_slack hle hs₂⟩

/-- Any memory modification strictly outside `bpL.OwnsAddr` preserves `extractBlockPool`,
`bpL.StateInv`, and `bpPairAt` across all live `(b, loc)`. -/
theorem BlockPoolLayout.congr_of_outside {bpL : BlockPoolLayout} {w fr slack : ℕ}
    {mem₁ mem₂ : ℕ → ℕ} (hv : bpL.Valid w fr) (hinv : bpL.StateInv slack mem₁)
    (hout : ∀ addr, bpL.OwnsAddr addr → mem₂ addr = mem₁ addr) :
    extractBlockPool bpL.mp mem₂ = extractBlockPool bpL.mp mem₁ ∧
    bpL.StateInv slack mem₂ ∧
    (∀ b < bpL.mp.M, ∀ loc < (extractBlockPool bpL.mp mem₁).bktCount b,
      bpPairAt bpL mem₂ b loc = bpPairAt bpL mem₁ b loc) := by
  have h16le := hv.mp_valid.sixteen_MK_le_maxTail
  have hmt : bpL.mp.M * bpL.mp.K ≤ bpL.mp.maxTail := by
    rw [Nat.mul_assoc] at h16le
    exact (Nat.mul_le_mul_left_iff (by decide : 0 < 16)).mp h16le
  have hex : extractBlockPool bpL.mp mem₂ = extractBlockPool bpL.mp mem₁ :=
    extractBlockPool_congr hv.mp_valid.w_pos hv.mp_valid.K_ge hmt
      (fun a ha => hout a (Or.inl ha))
  obtain ⟨hio₂, harr₂⟩ := bpL.io.congr_of_outside hv.io_valid.w_pos hinv.2.2
    (fun a ha => hout a (Or.inr ha))
  refine ⟨hex, ⟨hex ▸ hinv.1, hex ▸ hinv.2.1, hex ▸ hio₂⟩, fun b hb loc hloc => ?_⟩
  unfold bpPairAt; rw [hex]
  exact harr₂ _ (hinv.1.core.toPhys_lt hb hloc)

/-- Metadata-only step helper: any `BpMetaProg` preserves `bpL.io.StateInv`, `slotIoPairAt` on
`[0, nSide)`, and partner state when `usePaged ≠ 0`. -/
private theorem meta_preserves_io {α : Type} {bpL : BlockPoolLayout} {w fr C nSide slack : ℕ}
    {p : Memory.Prog α} {s : Memory.State} (hv : bpL.Valid w fr) (hm : BpMetaProg bpL.mp C p)
    (hio : bpL.io.StateInv nSide slack s.mem) :
    let s' := (Memory.spec 0).clientState s p
    bpL.io.StateInv nSide slack s'.mem ∧
    (∀ idx < nSide, slotIoPairAt bpL.io s'.mem idx = slotIoPairAt bpL.io s.mem idx) ∧
    (bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  dsimp only
  set s' := (Memory.spec 0).clientState s p
  have hout_io : ∀ addr, bpL.io.OwnsAddr addr → s'.mem addr = s.mem addr :=
    fun addr hia => hm.frame.mem_outside s addr (fun hma => hv.disjoint addr hma hia)
  obtain ⟨hio', harr'⟩ := bpL.io.congr_of_outside hv.io_valid.w_pos hio hout_io
  refine ⟨hio', harr', fun hnz => ?_⟩
  have hown_pg : ∀ addr, bpL.io.pgL.OwnsAddr addr → s'.mem addr = s.mem addr := fun addr ha => by
    apply hout_io addr
    unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
  have hu_eq : extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem :=
    extractPageUnperm_congr hv.io_valid.w_pos (fun a ha => hown_pg a (Or.inl ha))
  refine ⟨hu_eq, fun idx hidx => ?_⟩
  unfold SlotIoLayout.StateInv at hio; rw [ite_eq_right hnz] at hio
  obtain ⟨hi, _, _, hti, _, _, _⟩ := hio
  have hp_lt : (extractPageUnperm bpL.io.pgL s.mem).toPhys bpL.io.partner.side idx <
      bpL.io.pgL.nCap := (hi.toPhys_lt hidx).trans_le hti
  unfold slotIoPairAt
  have hp_nz : bpL.io.partner.usePaged ≠ 0 := hnz
  rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu_eq]
  unfold PageUnpermState.virtAt
  exact arenaPairAt_congr hv.io_valid.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt

/-- I/O-only step helper: any `BoundedFrameProg bpL.io.OwnsAddr` leaves `extractBlockPool bpL.mp`
unchanged. -/
private theorem io_preserves_meta {α : Type} {bpL : BlockPoolLayout} {w fr C : ℕ}
    {p : Memory.Prog α} (s : Memory.State) (hv : bpL.Valid w fr)
    (hio : BoundedFrameProg bpL.io.OwnsAddr C p) :
    extractBlockPool bpL.mp ((Memory.spec 0).clientState s p).mem =
      extractBlockPool bpL.mp s.mem := by
  have h16le := hv.mp_valid.sixteen_MK_le_maxTail
  have hmt : bpL.mp.M * bpL.mp.K ≤ bpL.mp.maxTail := by
    rw [Nat.mul_assoc] at h16le
    exact (Nat.mul_le_mul_left_iff (by decide : 0 < 16)).mp h16le
  exact extractBlockPool_congr hv.mp_valid.w_pos hv.mp_valid.K_ge hmt
    (fun addr hma => hio.mem_outside s addr (fun hia => hv.disjoint addr hma hia))

/-! ### Decode and Execute Optional Physical Swaps (`bpExecOptSwapProg`) -/

/-- Execute an encoded `Option PhysSwap` `(hasSwap, (p₁, p₂))` on `ioctx` (`¬ReadsWidth`). -/
private def bpExecOptSwapProg : SlotIoCtx × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (ioctx, (hasSw, (p₁, p₂))) =>
    if hasSw = 0 then
      pure ()
    else
      slotIoSwapRawProg (ioctx, (p₁, p₂))

private theorem frontier_bpExecOptSwapProg (x : SlotIoCtx × (ℕ × (ℕ × ℕ))) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1).pgL.w) :
    ((Memory.spec 0).runClient s (bpExecOptSwapProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ioctx, ⟨hasSw, ⟨p₁, p₂⟩⟩⟩
  unfold bpExecOptSwapProg; dsimp only
  split_ifs with hz
  · rfl
  · exact frontier_slotIoSwapRawProg (ioctx, (p₁, p₂)) s hw

private theorem realizesBounded_bpExecOptSwap :
    RealizesBounded .exact bpExecOptSwapProg
      (WordEncoding.encode (α := SlotIoCtx × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (ioctx, _) s => (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hsw := realizesBounded_slotIoSwapRaw
  realize
  all_goals (
    rcases d with ⟨ioctx, ⟨hasSw, ⟨p₁, p₂⟩⟩⟩
    simpa using h)

private theorem bpExecOptSwapProg_frame {io : SlotIoLayout} (hw : 0 < io.pgL.w)
    (osw : ℕ × (ℕ × ℕ)) :
    BoundedFrameProg io.OwnsAddr 88 (bpExecOptSwapProg (io.toCtx, osw)) := by
  rcases osw with ⟨hasSw, ⟨p₁, p₂⟩⟩
  unfold bpExecOptSwapProg; dsimp only
  exact BoundedFrameProg.ite_prog (hasSw = 0)
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (C₂ := 88) (fun _ ha => ha) (by decide))
    (fun _ => slotIoSwapProg_frame hw p₁ p₂)

private theorem bpExecOptSwapProg_spec {bpL : BlockPoolLayout} {nSide slack : ℕ}
    {osw : Option PhysSwap} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hio : bpL.io.StateInv nSide slack s.mem)
    (hsw_lt : ∀ sw, osw = some sw → sw.p₁ < nSide ∧ sw.p₂ < nSide) :
    let s' := (Memory.spec 0).clientState s (bpExecOptSwapProg (bpL.io.toCtx, encodeOptSwap osw))
    extractBlockPool bpL.mp s'.mem = extractBlockPool bpL.mp s.mem ∧
    bpL.io.StateInv nSide slack s'.mem ∧
    (∀ idx < nSide,
      slotIoPairAt bpL.io s'.mem idx =
        BlockPoolState.applyOptSwap osw (slotIoPairAt bpL.io s.mem) idx) ∧
    (bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  dsimp only
  have hvIo : bpL.io.Valid bpL.io.pgL.w s.frontier := hv.w_eq_io ▸ hv.io_valid
  cases osw with
  | none =>
    unfold encodeOptSwap bpExecOptSwapProg; dsimp only
    rw [ite_eq_left rfl]
    exact ⟨rfl, hio, fun _ _ => rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
  | some sw =>
    obtain ⟨hp₁, hp₂⟩ := hsw_lt sw rfl
    unfold encodeOptSwap bpExecOptSwapProg; dsimp only
    rw [ite_eq_right Nat.one_ne_zero]
    have hex := io_preserves_meta s hv (slotIoSwapProg_frame hvIo.w_pos sw.p₁ sw.p₂)
    obtain ⟨hio', harr', hpart'⟩ := slotIoSwapProg_spec hvIo hio hp₁ hp₂
    unfold slotIoSwapProg at hex hio' harr' hpart'
    refine ⟨hex, hio', fun idx hidx => ?_, hpart'⟩
    rw [harr' idx hidx]
    cases sw
    rfl

/-! ### Extensionality & 16-Step `bktTickOne` / `topCleanOne` Loops via Binary Doubling -/

private theorem applyOptSwap_congr {α : Type*} {osw : Option PhysSwap} {n : ℕ}
    {arr₁ arr₂ : ℕ → α} (hsw : ∀ sw, osw = some sw → sw.p₁ < n ∧ sw.p₂ < n)
    (harr : ∀ idx < n, arr₁ idx = arr₂ idx) :
    ∀ idx < n, BlockPoolState.applyOptSwap osw arr₁ idx =
      BlockPoolState.applyOptSwap osw arr₂ idx := by
  intro idx hidx
  cases osw with
  | none => exact harr idx hidx
  | some sw =>
    obtain ⟨hp1, hp2⟩ := hsw sw rfl
    dsimp only [BlockPoolState.applyOptSwap]
    by_cases h1 : idx = sw.p₁
    · subst h1; rw [PhysSwap.apply_p₁, PhysSwap.apply_p₁]; exact harr sw.p₂ hp2
    · by_cases h2 : idx = sw.p₂
      · subst h2; rw [PhysSwap.apply_p₂, PhysSwap.apply_p₂]; exact harr sw.p₁ hp1
      · rw [PhysSwap.apply_of_ne _ _ h1 h2, PhysSwap.apply_of_ne _ _ h1 h2]
        exact harr idx hidx

private theorem runBktTicks_add {α : Type*} (b : ℕ) :
    ∀ (t₁ t₂ : ℕ) (st : BlockPoolState × (ℕ → α)),
      BlockPoolState.runBktTicks b (t₁ + t₂) st =
        BlockPoolState.runBktTicks b t₂ (BlockPoolState.runBktTicks b t₁ st)
  | 0, t₂, st => by rw [zero_add, BlockPoolState.runBktTicks_zero]
  | t₁ + 1, t₂, (bp, arr) => by
    rw [Nat.add_right_comm, BlockPoolState.runBktTicks_succ, BlockPoolState.runBktTicks_succ]
    rcases bp.bktTickOne b with ⟨bp₁, osw⟩
    exact runBktTicks_add b t₁ t₂ (bp₁, BlockPoolState.applyOptSwap osw arr)

private theorem runTopCleanTicks_add {α : Type*} :
    ∀ (t₁ t₂ : ℕ) (st : BlockPoolState × (ℕ → α)),
      BlockPoolState.runTopCleanTicks (t₁ + t₂) st =
        BlockPoolState.runTopCleanTicks t₂ (BlockPoolState.runTopCleanTicks t₁ st)
  | 0, t₂, st => by rw [zero_add, BlockPoolState.runTopCleanTicks_zero]
  | t₁ + 1, t₂, (bp, arr) => by
    rw [Nat.add_right_comm, BlockPoolState.runTopCleanTicks_succ,
      BlockPoolState.runTopCleanTicks_succ]
    rcases bp.topCleanOne with ⟨bp₁, osw⟩
    exact runTopCleanTicks_add t₁ t₂ (bp₁, BlockPoolState.applyOptSwap osw arr)

private theorem runBktTicks_stepInv_and_congr {α : Type*} {b : ℕ} :
    ∀ (k t : ℕ) {bp : BlockPoolState} (_hb : b < bp.M) (_hsi : bp.StepInv b t)
      {arr₁ arr₂ : ℕ → α} (_harr : ∀ idx < bp.nSide, arr₁ idx = arr₂ idx),
      let r₁ := BlockPoolState.runBktTicks b k (bp, arr₁)
      let r₂ := BlockPoolState.runBktTicks b k (bp, arr₂)
      r₁.1 = r₂.1 ∧
      r₁.1.StepInv b (t - k) ∧
      r₁.1.M = bp.M ∧
      r₁.1.nSide = bp.nSide ∧
      (∀ idx < bp.nSide, r₁.2 idx = r₂.2 idx)
  | 0, t, bp, _hb, hsi, _arr₁, _arr₂, harr => by
    rw [BlockPoolState.runBktTicks_zero, BlockPoolState.runBktTicks_zero, Nat.sub_zero]
    exact ⟨rfl, hsi, rfl, rfl, harr⟩
  | k + 1, t, bp, hb, hsi, arr₁, arr₂, harr => by
    have hstep := hsi.bktTickOne_spec.{0} hb
    rcases heq : bp.bktTickOne b with ⟨bp₁, osw⟩
    rw [heq] at hstep
    obtain ⟨hsi₁, hM₁, _, hn₁, _, _, hsw₁, _⟩ := hstep
    rw [BlockPoolState.runBktTicks_succ, BlockPoolState.runBktTicks_succ, heq]
    dsimp only
    have harr₁ := applyOptSwap_congr hsw₁ harr
    obtain ⟨hfst, hsi_k, hM_k, hn_k, harr_k⟩ :=
      runBktTicks_stepInv_and_congr k (t - 1) (hM₁.symm ▸ hb) hsi₁ (hn₁.symm ▸ harr₁)
    rw [Nat.sub_sub, Nat.add_comm 1 k] at hsi_k
    exact ⟨hfst, hsi_k, hM_k.trans hM₁, hn_k.trans hn₁, hn₁ ▸ harr_k⟩

private theorem runTopCleanTicks_stepInv_and_congr {α : Type*} {b₀ : ℕ} :
    ∀ (k : ℕ) {bp : BlockPoolState} (_hsi : bp.StepInv b₀ 0)
      {arr₁ arr₂ : ℕ → α} (_harr : ∀ idx < bp.nSide, arr₁ idx = arr₂ idx),
      let r₁ := BlockPoolState.runTopCleanTicks k (bp, arr₁)
      let r₂ := BlockPoolState.runTopCleanTicks k (bp, arr₂)
      r₁.1 = r₂.1 ∧
      r₁.1.StepInv b₀ 0 ∧
      r₁.1.nSide = bp.nSide ∧
      (∀ idx < bp.nSide, r₁.2 idx = r₂.2 idx)
  | 0, bp, hsi, _arr₁, _arr₂, harr => by
    rw [BlockPoolState.runTopCleanTicks_zero, BlockPoolState.runTopCleanTicks_zero]
    exact ⟨rfl, hsi, rfl, harr⟩
  | k + 1, bp, hsi, arr₁, arr₂, harr => by
    have hstep := hsi.topCleanOne_debt_spec.{0}
    rcases heq : bp.topCleanOne with ⟨bp₁, osw⟩
    rw [heq] at hstep
    obtain ⟨hsi₁, _, _, hn₁, _, _, hsw₁, _⟩ := hstep
    rw [BlockPoolState.runTopCleanTicks_succ, BlockPoolState.runTopCleanTicks_succ, heq]
    dsimp only
    have harr₁ := applyOptSwap_congr hsw₁ harr
    obtain ⟨hfst, hsi_k, hn_k, harr_k⟩ :=
      runTopCleanTicks_stepInv_and_congr k hsi₁ (hn₁.symm ▸ harr₁)
    exact ⟨hfst, hsi_k, hn_k.trans hn₁, hn₁ ▸ harr_k⟩

/-- Single combined metadata + `SlotIoLayout` swap step for `bktTickOne` (`¬ReadsWidth`). -/
private def bpBktTickStepProg : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), b) => do
    let osw ← bpBktTickMetaProg (mctx, b)
    bpExecOptSwapProg (ioctx, osw)

private theorem frontier_bpBktTickStepProg (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpBktTickStepProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, b⟩; unfold bpBktTickStepProg; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    StateTransitionSpec.clientResult]
  rw [frontier_bpExecOptSwapProg _ _ hw, runClient_frontier_bpBktTickMetaProg]

private theorem realizesBounded_bpBktTickStep :
    RealizesBounded .exact bpBktTickStepProg
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hbt := realizesBounded_bpBktTickMeta
  have hes := realizesBounded_bpExecOptSwap
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, b⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    try simp only [runClient_frontier_bpBktTickMetaProg] at *
    first | exact hmv | exact hiov)

private theorem bpBktTickStepProg_frame {bpL : BlockPoolLayout} {w fr : ℕ}
    (hv : bpL.Valid w fr) (b : ℕ) :
    BlockPoolProg bpL 240 (bpBktTickStepProg (bpL.toCtx, b)) := by
  unfold bpBktTickStepProg; dsimp only [BlockPoolLayout.toCtx]
  exact BlockPoolProg.bind_prog
    (BlockPoolProg.of_meta (bpBktTickMetaProg_frame hv.mp_valid b))
    (fun osw => BlockPoolProg.of_io hv.mp_valid.w_pos hv.disjoint
      (bpExecOptSwapProg_frame hv.io_valid.w_pos osw))

private def bpRunBktTicks2Prog : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), b) => do
    bpBktTickStepProg ((mctx, ioctx), b)
    bpBktTickStepProg ((mctx, ioctx), b)

private def bpRunBktTicks4Prog : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), b) => do
    bpRunBktTicks2Prog ((mctx, ioctx), b)
    bpRunBktTicks2Prog ((mctx, ioctx), b)

private def bpRunBktTicks8Prog : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), b) => do
    bpRunBktTicks4Prog ((mctx, ioctx), b)
    bpRunBktTicks4Prog ((mctx, ioctx), b)

/-- Execute `16` `bktTickOne` steps on `(bpL, b)` (`¬ReadsWidth`). -/
private def bpRunBktTicks16Prog : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), b) => do
    bpRunBktTicks8Prog ((mctx, ioctx), b)
    bpRunBktTicks8Prog ((mctx, ioctx), b)

private theorem frontier_bpRunBktTicks2Prog (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpRunBktTicks2Prog x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, b⟩; unfold bpRunBktTicks2Prog; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState]
  rw [frontier_bpBktTickStepProg _ _ hw, frontier_bpBktTickStepProg _ s hw]

private theorem frontier_bpRunBktTicks4Prog (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpRunBktTicks4Prog x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, b⟩; unfold bpRunBktTicks4Prog; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState]
  rw [frontier_bpRunBktTicks2Prog _ _ hw, frontier_bpRunBktTicks2Prog _ s hw]

private theorem frontier_bpRunBktTicks8Prog (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpRunBktTicks8Prog x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, b⟩; unfold bpRunBktTicks8Prog; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState]
  rw [frontier_bpRunBktTicks4Prog _ _ hw, frontier_bpRunBktTicks4Prog _ s hw]

private theorem frontier_bpRunBktTicks16Prog (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpRunBktTicks16Prog x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, b⟩; unfold bpRunBktTicks16Prog; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState]
  rw [frontier_bpRunBktTicks8Prog _ _ hw, frontier_bpRunBktTicks8Prog _ s hw]

private theorem realizesBounded_bpRunBktTicks2 :
    RealizesBounded .exact bpRunBktTicks2Prog
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have h1 := realizesBounded_bpBktTickStep
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, b⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    have hfr := frontier_bpBktTickStepProg ((mctx, ioctx), b) s hiov.w_pos
    try rw [hfr]
    first | simpa using hmv | simpa using hiov)

private theorem realizesBounded_bpRunBktTicks4 :
    RealizesBounded .exact bpRunBktTicks4Prog
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have h2 := realizesBounded_bpRunBktTicks2
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, b⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    have hfr := frontier_bpRunBktTicks2Prog ((mctx, ioctx), b) s hiov.w_pos
    try rw [hfr]
    first | simpa using hmv | simpa using hiov)

private theorem realizesBounded_bpRunBktTicks8 :
    RealizesBounded .exact bpRunBktTicks8Prog
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have h4 := realizesBounded_bpRunBktTicks4
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, b⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    have hfr := frontier_bpRunBktTicks4Prog ((mctx, ioctx), b) s hiov.w_pos
    try rw [hfr]
    first | simpa using hmv | simpa using hiov)

private theorem realizesBounded_bpRunBktTicks16 :
    RealizesBounded .exact bpRunBktTicks16Prog
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have h8 := realizesBounded_bpRunBktTicks8
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, b⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    have hfr := frontier_bpRunBktTicks8Prog ((mctx, ioctx), b) s hiov.w_pos
    try rw [hfr]
    first | simpa using hmv | simpa using hiov)

private theorem bpRunBktTicks16Prog_frame {bpL : BlockPoolLayout} {w fr : ℕ}
    (hv : bpL.Valid w fr) (b : ℕ) :
    BlockPoolProg bpL 3840 (bpRunBktTicks16Prog (bpL.toCtx, b)) := by
  have h1 := bpBktTickStepProg_frame hv b
  have h2 : BlockPoolProg bpL 480 (bpRunBktTicks2Prog (bpL.toCtx, b)) :=
    BlockPoolProg.bind_prog h1 (fun _ => h1)
  have h4 : BlockPoolProg bpL 960 (bpRunBktTicks4Prog (bpL.toCtx, b)) :=
    BlockPoolProg.bind_prog h2 (fun _ => h2)
  have h8 : BlockPoolProg bpL 1920 (bpRunBktTicks8Prog (bpL.toCtx, b)) :=
    BlockPoolProg.bind_prog h4 (fun _ => h4)
  exact BlockPoolProg.bind_prog h8 (fun _ => h8)

/-- Single `bktTickStep` refinement under `StepInv b t`. -/
private theorem bpBktTickStepProg_spec {bpL : BlockPoolLayout} {b t slack : ℕ} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hsi : (extractBlockPool bpL.mp s.mem).StepInv b t)
    (hb : b < bpL.mp.M)
    (hn_le : (extractBlockPool bpL.mp s.mem).nSide ≤ bpL.mp.nCap)
    (hio : bpL.io.StateInv (extractBlockPool bpL.mp s.mem).nSide slack s.mem) :
    let s' := (Memory.spec 0).clientState s (bpBktTickStepProg (bpL.toCtx, b))
    let res := BlockPoolState.runBktTicks b 1
      (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem)
    s'.frontier = s.frontier ∧
    extractBlockPool bpL.mp s'.mem = res.1 ∧
    res.1.StepInv b (t - 1) ∧
    res.1.nSide = (extractBlockPool bpL.mp s.mem).nSide ∧
    bpL.io.StateInv res.1.nSide slack s'.mem ∧
    (∀ idx < res.1.nSide, slotIoPairAt bpL.io s'.mem idx = res.2 idx) ∧
    (bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  dsimp only
  refine ⟨(bpBktTickStepProg_frame hv b).frame.frontier_eq s, ?_⟩
  have hstep := hsi.bktTickOne_spec.{0} hb
  rcases hbt_one : (extractBlockPool bpL.mp s.mem).bktTickOne b with ⟨bp_next, osw_next⟩
  rw [hbt_one] at hstep
  obtain ⟨hsi_next, _, _, hn_next, _, _, hsw_lt, _⟩ := hstep
  have hr1_eq : BlockPoolState.runBktTicks b 1
      (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem) =
      (bp_next, BlockPoolState.applyOptSwap osw_next (slotIoPairAt bpL.io s.mem)) := by
    rw [BlockPoolState.runBktTicks_succ, hbt_one]; dsimp only
    exact BlockPoolState.runBktTicks_zero b _
  unfold bpBktTickStepProg; dsimp only [BlockPoolLayout.toCtx]
  rw [StateTransitionSpec.clientState_bind]
  set s₁ := (Memory.spec 0).clientState s (bpBktTickMetaProg (bpL.mp.toCtx, b))
  have hfr₁ : s₁.frontier = s.frontier := runClient_frontier_bpBktTickMetaProg _ s
  have hbt := bpBktTickMetaProg_spec hv.mp_valid hsi.core hb hn_le (hsi.bktCount_le b hb)
  dsimp only at hbt
  rw [hbt_one] at hbt
  rw [hbt.2]
  obtain ⟨hio₁, harr₁, hpart₁⟩ := meta_preserves_io hv (bpBktTickMetaProg_frame hv.mp_valid b) hio
  obtain ⟨hex₂, hio₂, harr₂, hpart₂⟩ := bpExecOptSwapProg_spec (hfr₁.symm ▸ hv) hio₁ hsw_lt
  rw [hex₂, hbt.1, hr1_eq]; dsimp only
  refine ⟨rfl, hsi_next, hn_next, hn_next.symm ▸ hio₂, fun idx hidx => ?_, fun hnz => ?_⟩
  · have hidx₀ : idx < (extractBlockPool bpL.mp s.mem).nSide := hn_next ▸ hidx
    exact (harr₂ idx hidx₀).trans (applyOptSwap_congr hsw_lt harr₁ idx hidx₀)
  · obtain ⟨hu₁, hp₁⟩ := hpart₁ hnz
    obtain ⟨hu₂, hp₂⟩ := hpart₂ hnz
    have hvl₁ : (extractPagePair bpL.io.pgL s₁.mem).virtLen bpL.io.partner.side =
        (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side :=
      congrArg (fun u => u.st.virtLen bpL.io.partner.side) hu₁
    exact ⟨hu₂.trans hu₁, fun idx hidx => (hp₂ idx (hvl₁.symm ▸ hidx)).trans (hp₁ idx hidx)⟩

/-- Generic `k + k` composition helper for multi-tick `runBktTicks` programs. -/
private theorem bpRunBktTicks_comp {bpL : BlockPoolLayout} {b k : ℕ}
    {p : BlockPoolCtx × ℕ → Memory.Prog Unit}
    (hspec : ∀ (t slack : ℕ) (s : Memory.State),
      bpL.Valid bpL.mp.w s.frontier →
      (extractBlockPool bpL.mp s.mem).StepInv b t →
      b < bpL.mp.M →
      (extractBlockPool bpL.mp s.mem).nSide ≤ bpL.mp.nCap →
      bpL.io.StateInv (extractBlockPool bpL.mp s.mem).nSide slack s.mem →
      let s' := (Memory.spec 0).clientState s (p (bpL.toCtx, b))
      let res := BlockPoolState.runBktTicks b k
        (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem)
      s'.frontier = s.frontier ∧
      extractBlockPool bpL.mp s'.mem = res.1 ∧
      res.1.StepInv b (t - k) ∧
      res.1.nSide = (extractBlockPool bpL.mp s.mem).nSide ∧
      bpL.io.StateInv res.1.nSide slack s'.mem ∧
      (∀ idx < res.1.nSide, slotIoPairAt bpL.io s'.mem idx = res.2 idx) ∧
      (bpL.io.usePaged ≠ 0 →
        extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
        ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
          slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx))
    (t slack : ℕ) (s : Memory.State)
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hsi : (extractBlockPool bpL.mp s.mem).StepInv b t)
    (hb : b < bpL.mp.M)
    (hn_le : (extractBlockPool bpL.mp s.mem).nSide ≤ bpL.mp.nCap)
    (hio : bpL.io.StateInv (extractBlockPool bpL.mp s.mem).nSide slack s.mem) :
    let s' := (Memory.spec 0).clientState s (do p (bpL.toCtx, b); p (bpL.toCtx, b))
    let res := BlockPoolState.runBktTicks b (k + k)
      (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem)
    s'.frontier = s.frontier ∧
    extractBlockPool bpL.mp s'.mem = res.1 ∧
    res.1.StepInv b (t - (k + k)) ∧
    res.1.nSide = (extractBlockPool bpL.mp s.mem).nSide ∧
    bpL.io.StateInv res.1.nSide slack s'.mem ∧
    (∀ idx < res.1.nSide, slotIoPairAt bpL.io s'.mem idx = res.2 idx) ∧
    (bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  dsimp only
  rw [StateTransitionSpec.clientState_bind, runBktTicks_add]
  obtain ⟨hfr₁, hex₁, hsi₁, hn₁, hio₁, harr₁, hpart₁⟩ := hspec t slack s hv hsi hb hn_le hio
  set s₁ := (Memory.spec 0).clientState s (p (bpL.toCtx, b))
  set r₁ := BlockPoolState.runBktTicks b k
    (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem)
  obtain ⟨hfr₂, hex₂, hsi₂, hn₂, hio₂, harr₂, hpart₂⟩ := hspec (t - k) slack s₁ (hfr₁.symm ▸ hv)
    (hex₁.symm ▸ hsi₁) hb (by rw [hex₁, hn₁]; exact hn_le) (hex₁.symm ▸ hio₁)
  have hM₁ : r₁.1.M = bpL.mp.M :=
    (runBktTicks_stepInv_and_congr k t hb hsi (fun _ _ => rfl)).2.2.1
  obtain ⟨hfst_c, _, _, _, harr_c⟩ :=
    runBktTicks_stepInv_and_congr k (t - k) (hM₁.symm ▸ hb) hsi₁
      (arr₁ := slotIoPairAt bpL.io s₁.mem) (arr₂ := r₁.2) harr₁
  rw [hex₁] at hex₂ hsi₂ hn₂ hio₂ harr₂
  rw [hfst_c] at hex₂ hsi₂ hn₂ hio₂ harr₂
  rw [Nat.sub_sub] at hsi₂
  refine ⟨hfr₂.trans hfr₁, hex₂, hsi₂, hn₂.trans hn₁, hio₂, fun idx hidx => ?_, fun hnz => ?_⟩
  · exact (harr₂ idx hidx).trans (harr_c idx (hn₂ ▸ hidx))
  · obtain ⟨hu₁, hp₁⟩ := hpart₁ hnz
    obtain ⟨hu₂, hp₂⟩ := hpart₂ hnz
    have hvl₁ : (extractPagePair bpL.io.pgL s₁.mem).virtLen bpL.io.partner.side =
        (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side :=
      congrArg (fun u => u.st.virtLen bpL.io.partner.side) hu₁
    exact ⟨hu₂.trans hu₁, fun idx hidx => (hp₂ idx (hvl₁.symm ▸ hidx)).trans (hp₁ idx hidx)⟩

private theorem bpRunBktTicks16Prog_spec {bpL : BlockPoolLayout} {b t slack : ℕ} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hsi : (extractBlockPool bpL.mp s.mem).StepInv b t)
    (hb : b < bpL.mp.M)
    (hn_le : (extractBlockPool bpL.mp s.mem).nSide ≤ bpL.mp.nCap)
    (hio : bpL.io.StateInv (extractBlockPool bpL.mp s.mem).nSide slack s.mem) :
    let s' := (Memory.spec 0).clientState s (bpRunBktTicks16Prog (bpL.toCtx, b))
    let res := BlockPoolState.runBktTicks b 16
      (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem)
    s'.frontier = s.frontier ∧
    extractBlockPool bpL.mp s'.mem = res.1 ∧
    res.1.StepInv b (t - 16) ∧
    res.1.nSide = (extractBlockPool bpL.mp s.mem).nSide ∧
    bpL.io.StateInv res.1.nSide slack s'.mem ∧
    (∀ idx < res.1.nSide, slotIoPairAt bpL.io s'.mem idx = res.2 idx) ∧
    (bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  have h2 := bpRunBktTicks_comp (bpL := bpL) (b := b) (k := 1) (p := bpBktTickStepProg)
    (fun t' sl' s' hv' hsi' hb' hn' hio' =>
      bpBktTickStepProg_spec (t := t') (slack := sl') (s := s') hv' hsi' hb' hn' hio')
  have h4 := bpRunBktTicks_comp (bpL := bpL) (b := b) (k := 2) (p := bpRunBktTicks2Prog) h2
  have h8 := bpRunBktTicks_comp (bpL := bpL) (b := b) (k := 4) (p := bpRunBktTicks4Prog) h4
  exact bpRunBktTicks_comp (bpL := bpL) (b := b) (k := 8) (p := bpRunBktTicks8Prog) h8
    t slack s hv hsi hb hn_le hio

/-- Single combined metadata + `SlotIoLayout` swap step for `topCleanOne` (`¬ReadsWidth`). -/
private def bpTopCleanStepProg : BlockPoolCtx → Memory.Prog Unit
  | (mctx, ioctx) => do
    let osw ← bpTopCleanMetaProg mctx
    bpExecOptSwapProg (ioctx, osw)

private theorem frontier_bpTopCleanStepProg (x : BlockPoolCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpTopCleanStepProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨mctx, ioctx⟩; unfold bpTopCleanStepProg; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    StateTransitionSpec.clientResult]
  rw [frontier_bpExecOptSwapProg _ _ hw, runClient_frontier_bpTopCleanMetaProg]

private theorem realizesBounded_bpTopCleanStep :
    RealizesBounded .exact bpTopCleanStepProg
      (WordEncoding.encode (α := BlockPoolCtx))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, ioctx) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have htc := realizesBounded_bpTopCleanMeta
  have hes := realizesBounded_bpExecOptSwap
  realize
  all_goals (
    rcases d with ⟨mctx, ioctx⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    try simp only [runClient_frontier_bpTopCleanMetaProg] at *
    first | exact hmv | exact hiov)

private theorem bpTopCleanStepProg_frame {bpL : BlockPoolLayout} {w fr : ℕ}
    (hv : bpL.Valid w fr) :
    BlockPoolProg bpL 193 (bpTopCleanStepProg bpL.toCtx) := by
  unfold bpTopCleanStepProg; dsimp only [BlockPoolLayout.toCtx]
  exact BlockPoolProg.bind_prog
    (BlockPoolProg.of_meta (bpTopCleanMetaProg_frame hv.mp_valid))
    (fun osw => BlockPoolProg.of_io hv.mp_valid.w_pos hv.disjoint
      (bpExecOptSwapProg_frame hv.io_valid.w_pos osw))

private def bpRunTopClean2Prog : BlockPoolCtx → Memory.Prog Unit
  | (mctx, ioctx) => do
    bpTopCleanStepProg (mctx, ioctx)
    bpTopCleanStepProg (mctx, ioctx)

private def bpRunTopClean4Prog : BlockPoolCtx → Memory.Prog Unit
  | (mctx, ioctx) => do
    bpRunTopClean2Prog (mctx, ioctx)
    bpRunTopClean2Prog (mctx, ioctx)

private def bpRunTopClean8Prog : BlockPoolCtx → Memory.Prog Unit
  | (mctx, ioctx) => do
    bpRunTopClean4Prog (mctx, ioctx)
    bpRunTopClean4Prog (mctx, ioctx)

/-- Execute `16` `topCleanOne` steps on `bpL` (`¬ReadsWidth`). -/
private def bpRunTopClean16Prog : BlockPoolCtx → Memory.Prog Unit
  | (mctx, ioctx) => do
    bpRunTopClean8Prog (mctx, ioctx)
    bpRunTopClean8Prog (mctx, ioctx)

private theorem frontier_bpRunTopClean2Prog (x : BlockPoolCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpRunTopClean2Prog x)).2.1.frontier = s.frontier := by
  rcases x with ⟨mctx, ioctx⟩; unfold bpRunTopClean2Prog; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState]
  rw [frontier_bpTopCleanStepProg _ _ hw, frontier_bpTopCleanStepProg _ s hw]

private theorem frontier_bpRunTopClean4Prog (x : BlockPoolCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpRunTopClean4Prog x)).2.1.frontier = s.frontier := by
  rcases x with ⟨mctx, ioctx⟩; unfold bpRunTopClean4Prog; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState]
  rw [frontier_bpRunTopClean2Prog _ _ hw, frontier_bpRunTopClean2Prog _ s hw]

private theorem frontier_bpRunTopClean8Prog (x : BlockPoolCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpRunTopClean8Prog x)).2.1.frontier = s.frontier := by
  rcases x with ⟨mctx, ioctx⟩; unfold bpRunTopClean8Prog; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState]
  rw [frontier_bpRunTopClean4Prog _ _ hw, frontier_bpRunTopClean4Prog _ s hw]

private theorem frontier_bpRunTopClean16Prog (x : BlockPoolCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpRunTopClean16Prog x)).2.1.frontier = s.frontier := by
  rcases x with ⟨mctx, ioctx⟩; unfold bpRunTopClean16Prog; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState]
  rw [frontier_bpRunTopClean8Prog _ _ hw, frontier_bpRunTopClean8Prog _ s hw]

private theorem realizesBounded_bpRunTopClean2 :
    RealizesBounded .exact bpRunTopClean2Prog
      (WordEncoding.encode (α := BlockPoolCtx))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, ioctx) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have h1 := realizesBounded_bpTopCleanStep
  realize
  all_goals (
    rcases d with ⟨mctx, ioctx⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    have hfr := frontier_bpTopCleanStepProg (mctx, ioctx) s hiov.w_pos
    try rw [hfr]
    first | simpa using hmv | simpa using hiov)

private theorem realizesBounded_bpRunTopClean4 :
    RealizesBounded .exact bpRunTopClean4Prog
      (WordEncoding.encode (α := BlockPoolCtx))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, ioctx) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have h2 := realizesBounded_bpRunTopClean2
  realize
  all_goals (
    rcases d with ⟨mctx, ioctx⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    have hfr := frontier_bpRunTopClean2Prog (mctx, ioctx) s hiov.w_pos
    try rw [hfr]
    first | simpa using hmv | simpa using hiov)

private theorem realizesBounded_bpRunTopClean8 :
    RealizesBounded .exact bpRunTopClean8Prog
      (WordEncoding.encode (α := BlockPoolCtx))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, ioctx) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have h4 := realizesBounded_bpRunTopClean4
  realize
  all_goals (
    rcases d with ⟨mctx, ioctx⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    have hfr := frontier_bpRunTopClean4Prog (mctx, ioctx) s hiov.w_pos
    try rw [hfr]
    first | simpa using hmv | simpa using hiov)

private theorem realizesBounded_bpRunTopClean16 :
    RealizesBounded .exact bpRunTopClean16Prog
      (WordEncoding.encode (α := BlockPoolCtx))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, ioctx) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have h8 := realizesBounded_bpRunTopClean8
  realize
  all_goals (
    rcases d with ⟨mctx, ioctx⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    have hfr := frontier_bpRunTopClean8Prog (mctx, ioctx) s hiov.w_pos
    try rw [hfr]
    first | simpa using hmv | simpa using hiov)

private theorem bpRunTopClean16Prog_frame {bpL : BlockPoolLayout} {w fr : ℕ}
    (hv : bpL.Valid w fr) :
    BlockPoolProg bpL 3088 (bpRunTopClean16Prog bpL.toCtx) := by
  have h1 := bpTopCleanStepProg_frame hv
  have h2 : BlockPoolProg bpL 386 (bpRunTopClean2Prog bpL.toCtx) :=
    BlockPoolProg.bind_prog h1 (fun _ => h1)
  have h4 : BlockPoolProg bpL 772 (bpRunTopClean4Prog bpL.toCtx) :=
    BlockPoolProg.bind_prog h2 (fun _ => h2)
  have h8 : BlockPoolProg bpL 1544 (bpRunTopClean8Prog bpL.toCtx) :=
    BlockPoolProg.bind_prog h4 (fun _ => h4)
  exact BlockPoolProg.bind_prog h8 (fun _ => h8)

private theorem bpTopCleanStepProg_spec {bpL : BlockPoolLayout} {b₀ slack : ℕ} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hsi : (extractBlockPool bpL.mp s.mem).StepInv b₀ 0)
    (hn_le : (extractBlockPool bpL.mp s.mem).nSide ≤ bpL.mp.nCap)
    (hio : bpL.io.StateInv (extractBlockPool bpL.mp s.mem).nSide slack s.mem) :
    let s' := (Memory.spec 0).clientState s (bpTopCleanStepProg bpL.toCtx)
    let res := BlockPoolState.runTopCleanTicks 1
      (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem)
    s'.frontier = s.frontier ∧
    extractBlockPool bpL.mp s'.mem = res.1 ∧
    res.1.StepInv b₀ 0 ∧
    res.1.nSide = (extractBlockPool bpL.mp s.mem).nSide ∧
    bpL.io.StateInv res.1.nSide slack s'.mem ∧
    (∀ idx < res.1.nSide, slotIoPairAt bpL.io s'.mem idx = res.2 idx) ∧
    (bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  dsimp only
  refine ⟨(bpTopCleanStepProg_frame hv).frame.frontier_eq s, ?_⟩
  have hstep := hsi.topCleanOne_debt_spec.{0}
  rcases htc_one : (extractBlockPool bpL.mp s.mem).topCleanOne with ⟨bp_next, osw_next⟩
  rw [htc_one] at hstep
  obtain ⟨hsi_next, _, _, hn_next, _, _, hsw_lt, _⟩ := hstep
  have hr1_eq : BlockPoolState.runTopCleanTicks 1
      (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem) =
      (bp_next, BlockPoolState.applyOptSwap osw_next (slotIoPairAt bpL.io s.mem)) := by
    rw [BlockPoolState.runTopCleanTicks_succ, htc_one]; dsimp only
    exact BlockPoolState.runTopCleanTicks_zero _
  unfold bpTopCleanStepProg; dsimp only [BlockPoolLayout.toCtx]
  rw [StateTransitionSpec.clientState_bind]
  set s₁ := (Memory.spec 0).clientState s (bpTopCleanMetaProg bpL.mp.toCtx)
  have hfr₁ : s₁.frontier = s.frontier := runClient_frontier_bpTopCleanMetaProg _ s
  have htc := bpTopCleanMetaProg_spec hv.mp_valid hsi.core hn_le hsi.bktCount_le
  dsimp only at htc
  rw [htc_one] at htc
  rw [htc.2]
  obtain ⟨hio₁, harr₁, hpart₁⟩ := meta_preserves_io hv (bpTopCleanMetaProg_frame hv.mp_valid) hio
  obtain ⟨hex₂, hio₂, harr₂, hpart₂⟩ := bpExecOptSwapProg_spec (hfr₁.symm ▸ hv) hio₁ hsw_lt
  rw [hex₂, htc.1, hr1_eq]; dsimp only
  refine ⟨rfl, hsi_next, hn_next, hn_next.symm ▸ hio₂, fun idx hidx => ?_, fun hnz => ?_⟩
  · have hidx₀ : idx < (extractBlockPool bpL.mp s.mem).nSide := hn_next ▸ hidx
    exact (harr₂ idx hidx₀).trans (applyOptSwap_congr hsw_lt harr₁ idx hidx₀)
  · obtain ⟨hu₁, hp₁⟩ := hpart₁ hnz
    obtain ⟨hu₂, hp₂⟩ := hpart₂ hnz
    have hvl₁ : (extractPagePair bpL.io.pgL s₁.mem).virtLen bpL.io.partner.side =
        (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side :=
      congrArg (fun u => u.st.virtLen bpL.io.partner.side) hu₁
    exact ⟨hu₂.trans hu₁, fun idx hidx => (hp₂ idx (hvl₁.symm ▸ hidx)).trans (hp₁ idx hidx)⟩

private theorem bpRunTopClean_comp {bpL : BlockPoolLayout} {k : ℕ}
    {p : BlockPoolCtx → Memory.Prog Unit}
    (hspec : ∀ (b₀ slack : ℕ) (s : Memory.State),
      bpL.Valid bpL.mp.w s.frontier →
      (extractBlockPool bpL.mp s.mem).StepInv b₀ 0 →
      (extractBlockPool bpL.mp s.mem).nSide ≤ bpL.mp.nCap →
      bpL.io.StateInv (extractBlockPool bpL.mp s.mem).nSide slack s.mem →
      let s' := (Memory.spec 0).clientState s (p bpL.toCtx)
      let res := BlockPoolState.runTopCleanTicks k
        (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem)
      s'.frontier = s.frontier ∧
      extractBlockPool bpL.mp s'.mem = res.1 ∧
      res.1.StepInv b₀ 0 ∧
      res.1.nSide = (extractBlockPool bpL.mp s.mem).nSide ∧
      bpL.io.StateInv res.1.nSide slack s'.mem ∧
      (∀ idx < res.1.nSide, slotIoPairAt bpL.io s'.mem idx = res.2 idx) ∧
      (bpL.io.usePaged ≠ 0 →
        extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
        ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
          slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx))
    (b₀ slack : ℕ) (s : Memory.State)
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hsi : (extractBlockPool bpL.mp s.mem).StepInv b₀ 0)
    (hn_le : (extractBlockPool bpL.mp s.mem).nSide ≤ bpL.mp.nCap)
    (hio : bpL.io.StateInv (extractBlockPool bpL.mp s.mem).nSide slack s.mem) :
    let s' := (Memory.spec 0).clientState s (do p bpL.toCtx; p bpL.toCtx)
    let res := BlockPoolState.runTopCleanTicks (k + k)
      (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem)
    s'.frontier = s.frontier ∧
    extractBlockPool bpL.mp s'.mem = res.1 ∧
    res.1.StepInv b₀ 0 ∧
    res.1.nSide = (extractBlockPool bpL.mp s.mem).nSide ∧
    bpL.io.StateInv res.1.nSide slack s'.mem ∧
    (∀ idx < res.1.nSide, slotIoPairAt bpL.io s'.mem idx = res.2 idx) ∧
    (bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  dsimp only
  rw [StateTransitionSpec.clientState_bind, runTopCleanTicks_add]
  obtain ⟨hfr₁, hex₁, hsi₁, hn₁, hio₁, harr₁, hpart₁⟩ := hspec b₀ slack s hv hsi hn_le hio
  set s₁ := (Memory.spec 0).clientState s (p bpL.toCtx)
  set r₁ := BlockPoolState.runTopCleanTicks k
    (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem)
  obtain ⟨hfr₂, hex₂, hsi₂, hn₂, hio₂, harr₂, hpart₂⟩ := hspec b₀ slack s₁ (hfr₁.symm ▸ hv)
    (hex₁.symm ▸ hsi₁) (by rw [hex₁, hn₁]; exact hn_le) (hex₁.symm ▸ hio₁)
  obtain ⟨hfst_c, _, _, harr_c⟩ :=
    runTopCleanTicks_stepInv_and_congr k hsi₁
      (arr₁ := slotIoPairAt bpL.io s₁.mem) (arr₂ := r₁.2) harr₁
  rw [hex₁] at hex₂ hsi₂ hn₂ hio₂ harr₂
  rw [hfst_c] at hex₂ hsi₂ hn₂ hio₂ harr₂
  refine ⟨hfr₂.trans hfr₁, hex₂, hsi₂, hn₂.trans hn₁, hio₂, fun idx hidx => ?_, fun hnz => ?_⟩
  · exact (harr₂ idx hidx).trans (harr_c idx (hn₂ ▸ hidx))
  · obtain ⟨hu₁, hp₁⟩ := hpart₁ hnz
    obtain ⟨hu₂, hp₂⟩ := hpart₂ hnz
    have hvl₁ : (extractPagePair bpL.io.pgL s₁.mem).virtLen bpL.io.partner.side =
        (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side :=
      congrArg (fun u => u.st.virtLen bpL.io.partner.side) hu₁
    exact ⟨hu₂.trans hu₁, fun idx hidx => (hp₂ idx (hvl₁.symm ▸ hidx)).trans (hp₁ idx hidx)⟩

private theorem bpRunTopClean16Prog_spec {bpL : BlockPoolLayout} {b₀ slack : ℕ} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hsi : (extractBlockPool bpL.mp s.mem).StepInv b₀ 0)
    (hn_le : (extractBlockPool bpL.mp s.mem).nSide ≤ bpL.mp.nCap)
    (hio : bpL.io.StateInv (extractBlockPool bpL.mp s.mem).nSide slack s.mem) :
    let s' := (Memory.spec 0).clientState s (bpRunTopClean16Prog bpL.toCtx)
    let res := BlockPoolState.runTopCleanTicks 16
      (extractBlockPool bpL.mp s.mem, slotIoPairAt bpL.io s.mem)
    s'.frontier = s.frontier ∧
    extractBlockPool bpL.mp s'.mem = res.1 ∧
    res.1.StepInv b₀ 0 ∧
    res.1.nSide = (extractBlockPool bpL.mp s.mem).nSide ∧
    bpL.io.StateInv res.1.nSide slack s'.mem ∧
    (∀ idx < res.1.nSide, slotIoPairAt bpL.io s'.mem idx = res.2 idx) ∧
    (bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  have h2 := bpRunTopClean_comp (bpL := bpL) (k := 1) (p := bpTopCleanStepProg)
    (fun b₀' sl' s' hv' hsi' hn' hio' =>
      bpTopCleanStepProg_spec (b₀ := b₀') (slack := sl') (s := s') hv' hsi' hn' hio')
  have h4 := bpRunTopClean_comp (bpL := bpL) (k := 2) (p := bpRunTopClean2Prog) h2
  have h8 := bpRunTopClean_comp (bpL := bpL) (k := 4) (p := bpRunTopClean4Prog) h4
  exact bpRunTopClean_comp (bpL := bpL) (k := 8) (p := bpRunTopClean8Prog) h8
    b₀ slack s hv hsi hn_le hio

/-! ### `BlockPoolLayout` Operations (`bpInit`, `bpReadAt`, `bpWriteAt`, `bpAppend`, `bpPop`) -/

/-- Initialize a Phase-1 zeroed metadata slice to `BlockPoolState.empty` (`¬ReadsWidth`). -/
@[expose] def bpInitProg (bpL : BlockPoolLayout) : Memory.Prog Unit :=
  bpInitZeroedProg bpL.mp.toCtx

theorem bpInitProg_frame {bpL : BlockPoolLayout} {w fr : ℕ} (hv : bpL.Valid w fr) :
    BlockPoolProg bpL 1 (bpInitProg bpL) :=
  BlockPoolProg.of_meta (bpInitZeroedProg_frame hv.mp_valid.offBktMeta_ge hv.mp_valid.w_pos)

theorem bpInitProg_spec {bpL : BlockPoolLayout} {slack : ℕ} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hzero : ∀ addr, bpL.mp.OwnsMetaAddr addr → s.mem addr = 0)
    (hio : bpL.io.StateInv 0 slack s.mem) :
    let s' := (Memory.spec 0).clientState s (bpInitProg bpL)
    s'.frontier = s.frontier ∧
    extractBlockPool bpL.mp s'.mem =
      BlockPoolState.empty bpL.mp.M bpL.mp.K bpL.mp.maxSlabs ∧
    bpL.StateInv slack s'.mem ∧
    (bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  dsimp only
  refine ⟨(bpInitProg_frame hv).frame.frontier_eq s, ?_⟩
  obtain ⟨hemp, hbal⟩ := bpInitZeroedProg_spec hv.mp_valid hzero
  obtain ⟨hio', _, hpart'⟩ := meta_preserves_io hv
    (bpInitZeroedProg_frame hv.mp_valid.offBktMeta_ge hv.mp_valid.w_pos) hio
  unfold bpInitProg
  have hns0 : (extractBlockPool bpL.mp
      ((Memory.spec 0).clientState s (bpInitZeroedProg bpL.mp.toCtx)).mem).nSide = 0 := by
    rw [hemp]; rfl
  exact ⟨hemp, ⟨hbal, by rw [hns0]; exact Nat.zero_le _, by rwa [hns0]⟩, hpart'⟩

/-- Raw tuple primitive reading `(q, v)` at `(b, loc)` in `BlockPoolCtx` (`¬ReadsWidth`). -/
def bpReadAtRawProg : BlockPoolCtx × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((mctx, ioctx), (b, loc)) => do
    let phys ← bpToPhysProg (mctx, (b, loc))
    slotIoReadRawProg (ioctx, phys)

/-- Read `(q, v)` at `(b, loc)` in `bpL : BlockPoolLayout` (`¬ReadsWidth`). -/
@[expose] def bpReadAtProg (bpL : BlockPoolLayout) (b loc : ℕ) : Memory.Prog (ℕ × ℕ) :=
  bpReadAtRawProg (bpL.toCtx, (b, loc))

theorem frontier_bpReadAtRawProg (x : BlockPoolCtx × (ℕ × ℕ)) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpReadAtRawProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, ⟨b, loc⟩⟩
  unfold bpReadAtRawProg; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    StateTransitionSpec.clientResult, runClient_state_bpToPhysProg]
  exact frontier_slotIoReadRawProg (ioctx, _) s

theorem realizesBounded_bpReadAtRaw :
    RealizesBounded .exact bpReadAtRawProg
      (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have htp := realizesBounded_bpToPhys
  have hrr := realizesBounded_slotIoReadRaw
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, ⟨b, loc⟩⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    try simp only [runClient_state_bpToPhysProg] at *
    first | exact hmv | exact hiov)

theorem bpReadAtProg_frame {bpL : BlockPoolLayout} {w fr : ℕ} (hv : bpL.Valid w fr) (b loc : ℕ) :
    BlockPoolProg bpL 44 (bpReadAtProg bpL b loc) := by
  unfold bpReadAtProg bpReadAtRawProg; dsimp only [BlockPoolLayout.toCtx]
  exact BlockPoolProg.bind_prog
    (BlockPoolProg.of_meta (bpToPhysProg_frame bpL.mp b loc))
    (fun phys => BlockPoolProg.of_io hv.mp_valid.w_pos hv.disjoint
      (slotIoReadProg_frame bpL.io phys))

theorem bpReadAtProg_spec {bpL : BlockPoolLayout} {slack b loc : ℕ} {s : Memory.State}
    (hinv : bpL.StateInv slack s.mem)
    (hb : b < bpL.mp.M) (hloc : loc < (extractBlockPool bpL.mp s.mem).bktCount b) :
    (Memory.spec 0).clientResult s (bpReadAtProg bpL b loc) = bpPairAt bpL s.mem b loc ∧
    (Memory.spec 0).clientState s (bpReadAtProg bpL b loc) = s := by
  unfold bpReadAtProg bpReadAtRawProg bpPairAt; dsimp only [BlockPoolLayout.toCtx]
  have htp_res := bpToPhysProg_spec hinv.1.core hinv.2.1 hb hloc
  have hp_lt := hinv.1.core.toPhys_lt hb hloc
  obtain ⟨hr_res, hr_st⟩ := slotIoReadProg_spec hinv.2.2 hp_lt
  unfold slotIoReadProg at hr_res hr_st
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    clientState_bpToPhysProg, htp_res]
  exact ⟨hr_res, hr_st⟩

/-- Raw tuple primitive writing `(q, v)` at `(b, loc)` in `BlockPoolCtx` (`¬ReadsWidth`). -/
def bpWriteAtRawProg : (BlockPoolCtx × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((mctx, ioctx), (b, loc)), qv) => do
    let phys ← bpToPhysProg (mctx, (b, loc))
    slotIoWriteRawProg ((ioctx, phys), qv)

/-- Write `(q, v)` at `(b, loc)` in `bpL : BlockPoolLayout` (`¬ReadsWidth`). -/
@[expose] def bpWriteAtProg (bpL : BlockPoolLayout) (b loc q v : ℕ) : Memory.Prog Unit :=
  bpWriteAtRawProg ((bpL.toCtx, (b, loc)), (q, v))

/-- Extracts the `SlotIoCtx` component from a `(BlockPoolCtx × α)` tuple. -/
abbrev bpCtxIo {α : Type} (x : BlockPoolCtx × α) : SlotIoCtx := x.1.2

/-- Extracts the `SlotIoCtx` component from a nested `((BlockPoolCtx × α) × β)` tuple. -/
abbrev bpNestedIo {α β : Type} (x : (BlockPoolCtx × α) × β) : SlotIoCtx := x.1.1.2

theorem frontier_bpWriteAtRawProg (x : (BlockPoolCtx × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx (bpNestedIo x)).pgL.w) :
    (clientOutState ((Memory.spec 0).runClient s (bpWriteAtRawProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨mctx, ioctx⟩, ⟨b, loc⟩⟩, qv⟩
  unfold bpWriteAtRawProg; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    StateTransitionSpec.clientResult, runClient_state_bpToPhysProg]
  exact frontier_slotIoWriteRawProg ((ioctx, _), qv) s hw

theorem realizesBounded_bpWriteAtRaw :
    RealizesBounded .exact bpWriteAtRawProg
      (WordEncoding.encode (α := (BlockPoolCtx × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have htp := realizesBounded_bpToPhys
  have hwr := realizesBounded_slotIoWriteRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨mctx, ioctx⟩, ⟨b, loc⟩⟩, qv⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    try simp only [runClient_state_bpToPhysProg] at *
    first | exact hmv | exact hiov)

theorem bpWriteAtProg_frame {bpL : BlockPoolLayout} {w fr : ℕ} (hv : bpL.Valid w fr)
    (b loc q v : ℕ) :
    BlockPoolProg bpL 48 (bpWriteAtProg bpL b loc q v) := by
  unfold bpWriteAtProg bpWriteAtRawProg; dsimp only [BlockPoolLayout.toCtx]
  exact BlockPoolProg.bind_prog
    (BlockPoolProg.of_meta (bpToPhysProg_frame bpL.mp b loc))
    (fun phys => BlockPoolProg.of_io hv.mp_valid.w_pos hv.disjoint
      (slotIoWriteProg_frame hv.io_valid.w_pos phys q v))

theorem bpWriteAtProg_spec {bpL : BlockPoolLayout} {slack b loc q v : ℕ} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hinv : bpL.StateInv slack s.mem)
    (hb : b < bpL.mp.M) (hloc : loc < (extractBlockPool bpL.mp s.mem).bktCount b)
    (hq : q < 2 ^ bpL.io.pgL.qBits) (hval : v < 2 ^ bpL.io.pgL.vBits) :
    let s' := (Memory.spec 0).clientState s (bpWriteAtProg bpL b loc q v)
    s'.frontier = s.frontier ∧
    extractBlockPool bpL.mp s'.mem = extractBlockPool bpL.mp s.mem ∧
    bpL.StateInv slack s'.mem ∧
    (∀ b' < bpL.mp.M, ∀ loc' < (extractBlockPool bpL.mp s.mem).bktCount b',
      bpPairAt bpL s'.mem b' loc' =
        if b' = b ∧ loc' = loc then (q, v) else bpPairAt bpL s.mem b' loc') ∧
    (bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s'.mem = extractPageUnperm bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  dsimp only
  refine ⟨(bpWriteAtProg_frame hv b loc q v).frame.frontier_eq s, ?_⟩
  have hvIo : bpL.io.Valid bpL.io.pgL.w s.frontier := hv.w_eq_io ▸ hv.io_valid
  have htp_res := bpToPhysProg_spec hinv.1.core hinv.2.1 hb hloc
  set phys := (extractBlockPool bpL.mp s.mem).toPhys b loc
  have hp_lt := hinv.1.core.toPhys_lt hb hloc
  unfold bpWriteAtProg bpWriteAtRawProg; dsimp only [BlockPoolLayout.toCtx]
  rw [StateTransitionSpec.clientState_bind, clientState_bpToPhysProg, htp_res]
  have hex := io_preserves_meta s hv (slotIoWriteProg_frame hvIo.w_pos phys q v)
  obtain ⟨hio', harr', hpart'⟩ := slotIoWriteProg_spec hvIo hinv.2.2 hp_lt hq hval
  unfold slotIoWriteProg at hex hio' harr' hpart'
  refine ⟨hex, ⟨hex ▸ hinv.1, hex ▸ hinv.2.1, hex ▸ hio'⟩,
    fun b' hb' loc' hloc' => ?_, hpart'⟩
  unfold bpPairAt; rw [hex]
  have hp'_lt := hinv.1.core.toPhys_lt hb' hloc'
  rw [harr' _ hp'_lt]
  have hinj_iff : ((extractBlockPool bpL.mp s.mem).toPhys b' loc' = phys) ↔
      (b' = b ∧ loc' = loc) :=
    ⟨fun heq => hinv.1.core.toPhys_inj hb' hloc' hb hloc heq,
     fun ⟨hb_e, hl_e⟩ => by subst hb_e hl_e; rfl⟩
  by_cases hbl : b' = b ∧ loc' = loc
  · rw [ite_eq_left (hinj_iff.mpr hbl), ite_eq_left hbl]
  · rw [ite_eq_right (mt hinj_iff.mp hbl), ite_eq_right hbl]

/-- Raw tuple primitive appending `(q, v)` to bucket `b` in `BlockPoolCtx` (`¬ReadsWidth`). -/
def bpAppendRawProg : (BlockPoolCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((mctx, ioctx), b), qv) => do
    let ns ← bpReadScalarProg (mctx, 1)
    slotIoAppendRawProg ((ioctx, ns), qv)
    bpRawPostAppendMetaProg (mctx, b)
    bpRunBktTicks16Prog ((mctx, ioctx), b)

/-- Append `(q, v)` at `(b, bktCount b)` in `bpL : BlockPoolLayout`, running `16` bucket rebalance
ticks (and `16` page rebalance ticks when `usePaged ≠ 0`, `¬ReadsWidth`). -/
@[expose] def bpAppendProg (bpL : BlockPoolLayout) (b q v : ℕ) : Memory.Prog Unit :=
  bpAppendRawProg ((bpL.toCtx, b), (q, v))

theorem frontier_bpAppendRawProg (x : (BlockPoolCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx (bpNestedIo x)).pgL.w) :
    (clientOutState ((Memory.spec 0).runClient s (bpAppendRawProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨mctx, ioctx⟩, b⟩, qv⟩
  unfold bpAppendRawProg; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    StateTransitionSpec.clientResult, runClient_state_bpReadScalarProg]
  rw [frontier_bpRunBktTicks16Prog _ _ hw,
    runClient_frontier_bpRawPostAppendMetaProg,
    frontier_slotIoAppendRawProg ((ioctx, _), qv) s hw]

theorem realizesBounded_bpAppendRaw :
    RealizesBounded .exact bpAppendRawProg
      (WordEncoding.encode (α := (BlockPoolCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hap := realizesBounded_slotIoAppendRaw
  have hrpa := realizesBounded_bpRawPostAppendMeta
  have h16 := realizesBounded_bpRunBktTicks16
  realize
  all_goals (
    rcases d with ⟨⟨⟨mctx, ioctx⟩, b⟩, qv⟩
    dsimp only [Fits, StateTransitionSpec.clientState, StateTransitionSpec.clientResult] at *
    obtain ⟨hmv, hiov⟩ := h
    have hw_pos : 0 < w := hmv.w_eq ▸ hmv.w_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw_pos.ne'
    try simp only [runClient_state_bpReadScalarProg] at *
    try rw [runClient_frontier_bpRawPostAppendMetaProg]
    try rw [frontier_slotIoAppendRawProg _ _ hiov.w_pos]
    first | exact hw1 | simpa using hmv | simpa using hiov)

theorem bpAppendProg_frame {bpL : BlockPoolLayout} {w fr : ℕ} (hv : bpL.Valid w fr)
    (b q v : ℕ) :
    BlockPoolProg bpL 5300 (bpAppendProg bpL b q v) := by
  unfold bpAppendProg bpAppendRawProg; dsimp only [BlockPoolLayout.toCtx]
  have hf := BlockPoolProg.bind_prog
    (BlockPoolProg.of_meta (bpReadScalarProg_frame bpL.mp 1)) fun ns =>
    BlockPoolProg.bind_prog
      (BlockPoolProg.of_io hv.mp_valid.w_pos hv.disjoint
        (slotIoAppendProg_frame hv.io_valid.w_pos ns q v)) fun _ =>
    BlockPoolProg.bind_prog
      (BlockPoolProg.of_meta (bpRawPostAppendMetaProg_frame hv.mp_valid b)) fun _ =>
    bpRunBktTicks16Prog_frame hv b
  exact hf.mono (C₂ := 5300) (by decide)

theorem bpAppendProg_spec {bpL : BlockPoolLayout} {b q v : ℕ} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hinv : bpL.StateInv 0 s.mem)
    (hb : b < bpL.mp.M)
    (hn_lt : (extractBlockPool bpL.mp s.mem).nSide < bpL.mp.nCap)
    (hbkt_lt : (extractBlockPool bpL.mp s.mem).bktCount b < bpL.mp.maxSlabs * bpL.mp.K)
    (hcap_io : bpL.io.AppendCap (extractBlockPool bpL.mp s.mem).nSide s.mem)
    (hq : q < 2 ^ bpL.io.pgL.qBits) (hval : v < 2 ^ bpL.io.pgL.vBits) :
    let bp₀ := extractBlockPool bpL.mp s.mem
    let s' := (Memory.spec 0).clientState s (bpAppendProg bpL b q v)
    let slack' :=
      if bpL.io.usePaged = 0 ∨ (extractPageUnperm bpL.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    bpL.StateInv slack' s'.mem ∧
    (extractBlockPool bpL.mp s'.mem).nSide = bp₀.nSide + 1 ∧
    (extractBlockPool bpL.mp s'.mem).bktCount b = bp₀.bktCount b + 1 ∧
    (∀ b' ≠ b, (extractBlockPool bpL.mp s'.mem).bktCount b' = bp₀.bktCount b') ∧
    bpPairAt bpL s'.mem b (bp₀.bktCount b) = (q, v) ∧
    (∀ b' < bpL.mp.M, ∀ loc' < bp₀.bktCount b',
      bpPairAt bpL s'.mem b' loc' = bpPairAt bpL s.mem b' loc') ∧
    (bpL.io.usePaged ≠ 0 →
      (extractPagePair bpL.io.pgL s'.mem).virtLen bpL.io.partner.side =
        (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side ∧
      (extractPagePair bpL.io.pgL s'.mem).totalItems =
        (extractPagePair bpL.io.pgL s.mem).totalItems + 1 ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  dsimp only
  refine ⟨(bpAppendProg_frame hv b q v).frame.frontier_eq s, ?_⟩
  set bp₀ := extractBlockPool bpL.mp s.mem
  change bp₀.Balanced ∧ bp₀.nSide ≤ bpL.mp.nCap ∧ bpL.io.StateInv bp₀.nSide 0 s.mem at hinv
  change bp₀.nSide < bpL.mp.nCap at hn_lt
  change bp₀.bktCount b < bpL.mp.maxSlabs * bpL.mp.K at hbkt_lt
  have hvIo : bpL.io.Valid bpL.io.pgL.w s.frontier := hv.w_eq_io ▸ hv.io_valid
  have hns_res : (Memory.spec 0).clientResult s (bpReadScalarProg (bpL.mp.toCtx, 1)) =
      bp₀.nSide := by
    unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]; rw [ite_eq_left (Or.inl rfl)]; rfl
  unfold bpAppendProg bpAppendRawProg; dsimp only [BlockPoolLayout.toCtx]
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg, hns_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  set s₁ := (Memory.spec 0).clientState s (slotIoAppendRawProg ((bpL.io.toCtx, bp₀.nSide), (q, v)))
  have hfr₁ : s₁.frontier = s.frontier :=
    frontier_slotIoAppendRawProg ((bpL.io.toCtx, bp₀.nSide), (q, v)) s hvIo.w_pos
  have hex₁ : extractBlockPool bpL.mp s₁.mem = bp₀ := by
    have h := io_preserves_meta s hv (slotIoAppendProg_frame hvIo.w_pos bp₀.nSide q v)
    unfold slotIoAppendProg at h; exact h
  obtain ⟨hio₁, harr₁, hpart₁⟩ := slotIoAppendProg_spec hvIo hinv.2.2 hcap_io hq hval
  unfold slotIoAppendProg at hio₁ harr₁ hpart₁
  set s₂ := (Memory.spec 0).clientState s₁ (bpRawPostAppendMetaProg (bpL.mp.toCtx, b))
  have hfr₂ : s₂.frontier = s.frontier :=
    (runClient_frontier_bpRawPostAppendMetaProg _ s₁).trans hfr₁
  have hex₂ : extractBlockPool bpL.mp s₂.mem = bp₀.rawPostAppend b := by
    have h := bpRawPostAppendMetaProg_spec (hfr₁.symm ▸ hv.mp_valid) (hex₁ ▸ hinv.1.core) hb
      (hex₁ ▸ hn_lt)
    rwa [hex₁] at h
  obtain ⟨hio₂, harr₂, hpart₂⟩ := meta_preserves_io (hfr₁.symm ▸ hv)
    (bpRawPostAppendMetaProg_frame (hfr₁.symm ▸ hv.mp_valid) b) hio₁
  obtain ⟨hsi_rpa, hM_rpa, _, hn_rpa, _, _, _, _, _⟩ := hinv.1.rawPostAppend_spec hb hbkt_lt
  have hns_s₂ : (extractBlockPool bpL.mp s₂.mem).nSide = bp₀.nSide + 1 :=
    (congrArg BlockPoolState.nSide hex₂).trans hn_rpa
  obtain ⟨_, hex₃, _, _, hio₃, harr₃, hpart₃⟩ := bpRunBktTicks16Prog_spec (hfr₂.symm ▸ hv)
    (hex₂.symm ▸ hsi_rpa) hb (by rw [hns_s₂]; omega) (hns_s₂.symm ▸ hio₂)
  dsimp only [BlockPoolLayout.toCtx] at hex₃ hio₃ harr₃ hpart₃
  set s₃ := (Memory.spec 0).clientState s₂
    (bpRunBktTicks16Prog ((bpL.mp.toCtx, bpL.io.toCtx), b))
  have hbal_end := hinv.1.postAppend_runBktTicks_balanced hb hbkt_lt (slotIoPairAt bpL.io s₂.mem)
  dsimp only at hbal_end
  rw [hex₂] at hex₃ hio₃ harr₃
  obtain ⟨hbal₃, hn₃, hbc_b₃, hbc_ne₃, hnew₃, hold₃⟩ := hbal_end
  have hb_rpa : b < (bp₀.rawPostAppend b).M := hM_rpa.symm ▸ hb
  have hM_eq : (BlockPoolState.runBktTicks b 16
      (bp₀.rawPostAppend b, slotIoPairAt bpL.io s₂.mem)).1.M = bpL.mp.M :=
    (runBktTicks_stepInv_and_congr 16 16 hb_rpa hsi_rpa
      (arr₁ := slotIoPairAt bpL.io s₂.mem) (arr₂ := slotIoPairAt bpL.io s₂.mem)
      (fun _ _ => rfl)).2.2.1.trans hM_rpa
  refine ⟨⟨hex₃ ▸ hbal₃, by rw [hex₃, hn₃]; omega, hex₃ ▸ hio₃⟩,
    hex₃ ▸ hn₃, hex₃ ▸ hbc_b₃, fun b' hne => hex₃ ▸ hbc_ne₃ b' hne,
    ?_, fun b' hb' loc' hloc' => ?_, fun hnz => ?_⟩
  · unfold bpPairAt; rw [hex₃]
    set r_end := BlockPoolState.runBktTicks b 16 (bp₀.rawPostAppend b, slotIoPairAt bpL.io s₂.mem)
    have hlt_b : bp₀.bktCount b < r_end.1.bktCount b := by rw [hbc_b₃]; omega
    have htp_lt := hbal₃.core.toPhys_lt (hM_eq.symm ▸ hb) hlt_b
    rw [harr₃ _ htp_lt, hnew₃, harr₂ bp₀.nSide (Nat.lt_succ_self _),
      harr₁ bp₀.nSide (Nat.lt_succ_self _), ite_eq_left rfl]
  · unfold bpPairAt; rw [hex₃]
    set r_end := BlockPoolState.runBktTicks b 16 (bp₀.rawPostAppend b, slotIoPairAt bpL.io s₂.mem)
    have hlt_loc : loc' < r_end.1.bktCount b' := by
      by_cases hbe : b' = b
      · subst b'; rw [hbc_b₃]; omega
      · rw [hbc_ne₃ b' hbe]; exact hloc'
    have htp_lt := hbal₃.core.toPhys_lt (hM_eq.symm ▸ hb') hlt_loc
    have htp₀_lt := hinv.1.core.toPhys_lt hb' hloc'
    rw [harr₃ _ htp_lt, hold₃ b' hb' loc' hloc', harr₂ _ (Nat.lt_succ_of_lt htp₀_lt),
      harr₁ _ (Nat.lt_succ_of_lt htp₀_lt), ite_eq_right (ne_of_lt htp₀_lt)]
  · obtain ⟨hvl₁, hti₁, hp₁⟩ := hpart₁ hnz
    obtain ⟨hu₂, hp₂⟩ := hpart₂ hnz
    obtain ⟨hu₃, hp₃⟩ := hpart₃ hnz
    have hst₂ : extractPagePair bpL.io.pgL s₂.mem = extractPagePair bpL.io.pgL s₁.mem :=
      congrArg PageUnpermState.st hu₂
    have hst₃ : extractPagePair bpL.io.pgL s₃.mem = extractPagePair bpL.io.pgL s₂.mem :=
      congrArg PageUnpermState.st hu₃
    refine ⟨by rw [hst₃, hst₂, hvl₁], by rw [hst₃, hst₂, hti₁], fun idx hidx => ?_⟩
    exact (hp₃ idx (by rw [hst₂, hvl₁]; exact hidx)).trans
      ((hp₂ idx (by rw [hvl₁]; exact hidx)).trans (hp₁ idx hidx))

/-- First 4-step sub-program of `bpPopBktBack`: `prepPopBktBack` + optional swap + `slotIoPopBack`
+ `commitPopBktBack` (`3` binds, `¬ReadsWidth`). -/
private def bpPopBktPrepAndShrinkProg : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), b) => do
    let osw ← bpPrepPopMetaProg (mctx, b)
    bpExecOptSwapProg (ioctx, osw)
    slotIoPopBackRawProg ioctx
    bpCommitPopMetaProg (mctx, b)

private theorem frontier_bpPopBktPrepAndShrinkProg (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).runClient s (bpPopBktPrepAndShrinkProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, b⟩
  unfold bpPopBktPrepAndShrinkProg; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    StateTransitionSpec.clientResult]
  rw [runClient_frontier_bpCommitPopMetaProg,
    frontier_slotIoPopBackRawProg ioctx _ hw,
    frontier_bpExecOptSwapProg _ _ hw,
    runClient_frontier_bpPrepPopMetaProg]

private theorem realizesBounded_bpPopBktPrepAndShrink :
    RealizesBounded .exact bpPopBktPrepAndShrinkProg
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hpp := realizesBounded_bpPrepPopMeta
  have hes := realizesBounded_bpExecOptSwap
  have hpb := realizesBounded_slotIoPopBackRaw
  have hcp := realizesBounded_bpCommitPopMeta
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, b⟩
    dsimp only [Fits, StateTransitionSpec.clientState, StateTransitionSpec.clientResult] at *
    obtain ⟨hmv, hiov⟩ := h)
  · exact hmv
  · have hfr1 := runClient_frontier_bpPrepPopMetaProg (mctx, b) s
    rwa [hfr1]
  · set s₁ := ((Memory.spec 0).runClient s (bpPrepPopMetaProg (mctx, b))).2.1
    set osw := ((Memory.spec 0).runClient s (bpPrepPopMetaProg (mctx, b))).1
    have hfr1 : s₁.frontier = s.frontier := runClient_frontier_bpPrepPopMetaProg (mctx, b) s
    have hfr2 := frontier_bpExecOptSwapProg (ioctx, osw) s₁ hiov.w_pos
    rwa [hfr2, hfr1]
  · set s₁ := ((Memory.spec 0).runClient s (bpPrepPopMetaProg (mctx, b))).2.1
    set osw := ((Memory.spec 0).runClient s (bpPrepPopMetaProg (mctx, b))).1
    set s₂ := ((Memory.spec 0).runClient s₁ (bpExecOptSwapProg (ioctx, osw))).2.1
    have hfr1 : s₁.frontier = s.frontier := runClient_frontier_bpPrepPopMetaProg (mctx, b) s
    have hfr2 : s₂.frontier = s₁.frontier := frontier_bpExecOptSwapProg (ioctx, osw) s₁ hiov.w_pos
    have hfr3 := frontier_slotIoPopBackRawProg ioctx s₂ hiov.w_pos
    rwa [hfr3, hfr2, hfr1]

private theorem bpPopBktPrepAndShrinkProg_frame {bpL : BlockPoolLayout} {w fr : ℕ}
    (hv : bpL.Valid w fr) (b : ℕ) :
    BlockPoolProg bpL 1571 (bpPopBktPrepAndShrinkProg (bpL.toCtx, b)) := by
  unfold bpPopBktPrepAndShrinkProg; dsimp only [BlockPoolLayout.toCtx]
  exact BlockPoolProg.bind_prog
    (BlockPoolProg.of_meta (bpPrepPopMetaProg_frame hv.mp_valid b)) fun osw =>
    BlockPoolProg.bind_prog
      (BlockPoolProg.of_io hv.mp_valid.w_pos hv.disjoint
        (bpExecOptSwapProg_frame hv.io_valid.w_pos osw)) fun _ =>
    BlockPoolProg.bind_prog
      (BlockPoolProg.of_io hv.mp_valid.w_pos hv.disjoint
        (slotIoPopBackProg_frame hv.io_valid.w_pos)) fun _ =>
    BlockPoolProg.of_meta (bpCommitPopMetaProg_frame hv.mp_valid b)

/-- Raw tuple primitive popping `(b, bktCount b - 1)` from `BlockPoolCtx` (`¬ReadsWidth`). -/
def bpPopBktBackRawProg : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), b) => do
    bpPopBktPrepAndShrinkProg ((mctx, ioctx), b)
    bpRunBktTicks16Prog ((mctx, ioctx), b)
    bpRunTopClean16Prog (mctx, ioctx)

/-- Pop `(b, bktCount b - 1)` in `bpL : BlockPoolLayout`, running `16` bucket rebalance ticks, `16`
`topCleanOne` boundary ticks, and `16` page rebalance ticks when `usePaged ≠ 0` (`¬ReadsWidth`). -/
@[expose] def bpPopBktBackProg (bpL : BlockPoolLayout) (b : ℕ) : Memory.Prog Unit :=
  bpPopBktBackRawProg (bpL.toCtx, b)

theorem frontier_bpPopBktBackRawProg (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx (bpCtxIo x)).pgL.w) :
    (clientOutState ((Memory.spec 0).runClient s (bpPopBktBackRawProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, b⟩
  unfold bpPopBktBackRawProg; dsimp only
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState]
  rw [frontier_bpRunTopClean16Prog (mctx, ioctx) _ hw,
    frontier_bpRunBktTicks16Prog ((mctx, ioctx), b) _ hw,
    frontier_bpPopBktPrepAndShrinkProg ((mctx, ioctx), b) s hw]

theorem realizesBounded_bpPopBktBackRaw :
    RealizesBounded .exact bpPopBktBackRawProg
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hps := realizesBounded_bpPopBktPrepAndShrink
  have hb16 := realizesBounded_bpRunBktTicks16
  have hc16 := realizesBounded_bpRunTopClean16
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, b⟩
    dsimp only [Fits, StateTransitionSpec.clientState] at *
    obtain ⟨hmv, hiov⟩ := h
    try rw [frontier_bpRunBktTicks16Prog _ _ hiov.w_pos]
    try rw [frontier_bpPopBktPrepAndShrinkProg _ _ hiov.w_pos]
    first | simpa using hmv | simpa using hiov)

theorem bpPopBktBackProg_frame {bpL : BlockPoolLayout} {w fr : ℕ} (hv : bpL.Valid w fr) (b : ℕ) :
    BlockPoolProg bpL 8500 (bpPopBktBackProg bpL b) := by
  unfold bpPopBktBackProg bpPopBktBackRawProg; dsimp only [BlockPoolLayout.toCtx]
  have hf := BlockPoolProg.bind_prog
    (bpPopBktPrepAndShrinkProg_frame hv b) fun _ =>
    BlockPoolProg.bind_prog
      (bpRunBktTicks16Prog_frame hv b) fun _ =>
    bpRunTopClean16Prog_frame hv
  exact hf.mono (C₂ := 8500) (by decide)

theorem bpPopBktBackProg_spec {bpL : BlockPoolLayout} {b : ℕ} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier)
    (hinv : bpL.StateInv 0 s.mem)
    (hb : b < bpL.mp.M)
    (hcnt : 0 < (extractBlockPool bpL.mp s.mem).bktCount b) :
    let bp₀ := extractBlockPool bpL.mp s.mem
    let s' := (Memory.spec 0).clientState s (bpPopBktBackProg bpL b)
    let slack' :=
      if bpL.io.usePaged = 0 ∨ (extractPageUnperm bpL.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    bpL.StateInv slack' s'.mem ∧
    (extractBlockPool bpL.mp s'.mem).nSide = bp₀.nSide - 1 ∧
    (extractBlockPool bpL.mp s'.mem).bktCount b = bp₀.bktCount b - 1 ∧
    (∀ b' ≠ b, (extractBlockPool bpL.mp s'.mem).bktCount b' = bp₀.bktCount b') ∧
    (∀ b' < bpL.mp.M, ∀ loc' < (extractBlockPool bpL.mp s'.mem).bktCount b',
      bpPairAt bpL s'.mem b' loc' = bpPairAt bpL s.mem b' loc') ∧
    (bpL.io.usePaged ≠ 0 →
      (extractPagePair bpL.io.pgL s'.mem).virtLen bpL.io.partner.side =
        (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side ∧
      (extractPagePair bpL.io.pgL s'.mem).totalItems =
        (extractPagePair bpL.io.pgL s.mem).totalItems - 1 ∧
      ∀ idx < (extractPagePair bpL.io.pgL s.mem).virtLen bpL.io.partner.side,
        slotIoPairAt bpL.io.partner s'.mem idx = slotIoPairAt bpL.io.partner s.mem idx) := by
  dsimp only
  refine ⟨(bpPopBktBackProg_frame hv b).frame.frontier_eq s, ?_⟩
  set bp₀ := extractBlockPool bpL.mp s.mem
  change bp₀.Balanced ∧ bp₀.nSide ≤ bpL.mp.nCap ∧ bpL.io.StateInv bp₀.nSide 0 s.mem at hinv
  change 0 < bp₀.bktCount b at hcnt
  have hvIo : bpL.io.Valid bpL.io.pgL.w s.frontier := hv.w_eq_io ▸ hv.io_valid
  have hprep_pure := hinv.1.prepPopBktBack_spec.{0} hb hcnt
  dsimp only at hprep_pure
  set bp₁ := (bp₀.prepPopBktBack b).1
  set osw := (bp₀.prepPopBktBack b).2
  obtain ⟨hbal₁, hM₁, _, hn₁, hbc₁, hn_pos, htp_end, hsw_lt, harr_prep⟩ := hprep_pure
  unfold bpPopBktBackProg bpPopBktBackRawProg bpPopBktPrepAndShrinkProg BlockPoolLayout.toCtx
  dsimp only
  repeat rw [StateTransitionSpec.clientState_bind]
  -- Step 1: `bpPrepPopMetaProg`
  set s₁ := (Memory.spec 0).clientState s (bpPrepPopMetaProg (bpL.mp.toCtx, b))
  have hfr₁ : s₁.frontier = s.frontier := runClient_frontier_bpPrepPopMetaProg _ s
  obtain ⟨hex₁, hres₁⟩ := bpPrepPopMetaProg_spec hv.mp_valid hinv.1 hb hcnt hinv.2.1
  rw [hres₁]
  obtain ⟨hio₁, harr₁, hpart₁⟩ := meta_preserves_io hv (bpPrepPopMetaProg_frame hv.mp_valid b)
    hinv.2.2
  -- Step 2: `bpExecOptSwapProg`
  set s₂ := (Memory.spec 0).clientState s₁ (bpExecOptSwapProg (bpL.io.toCtx, encodeOptSwap osw))
  have hfr₂ : s₂.frontier = s.frontier :=
    (frontier_bpExecOptSwapProg (bpL.io.toCtx, encodeOptSwap osw) s₁
      (by simpa using hvIo.w_pos)).trans hfr₁
  obtain ⟨hex₂_rel, hio₂, harr₂, hpart₂⟩ := bpExecOptSwapProg_spec (hfr₁.symm ▸ hv) hio₁ hsw_lt
  have hex₂ : extractBlockPool bpL.mp s₂.mem = bp₁ := hex₂_rel.trans hex₁
  have hu_s₂ : bpL.io.usePaged ≠ 0 →
      extractPageUnperm bpL.io.pgL s₂.mem = extractPageUnperm bpL.io.pgL s.mem :=
    fun hnz => (hpart₂ hnz).1.trans (hpart₁ hnz).1
  -- Step 3: `slotIoPopBackRawProg`
  set s₃ := (Memory.spec 0).clientState s₂ (slotIoPopBackRawProg bpL.io.toCtx)
  have hfr₃ : s₃.frontier = s.frontier :=
    (frontier_slotIoPopBackRawProg bpL.io.toCtx s₂ hvIo.w_pos).trans hfr₂
  have hex₃ : extractBlockPool bpL.mp s₃.mem = bp₁ := by
    have h := io_preserves_meta s₂ (hfr₂.symm ▸ hv) (slotIoPopBackProg_frame hvIo.w_pos)
    unfold slotIoPopBackProg at h
    exact h.trans hex₂
  obtain ⟨hio₃_raw, harr₃, hpart₃⟩ := slotIoPopBackProg_spec (hfr₂.symm ▸ hvIo) hio₂ hn_pos
  unfold slotIoPopBackProg at hio₃_raw harr₃ hpart₃
  have hslack_eq : (if bpL.io.usePaged = 0 ∨
      (extractPageUnperm bpL.io.pgL s₂.mem).cleanPhase = 0 then 0 else 24) =
      (if bpL.io.usePaged = 0 ∨
        (extractPageUnperm bpL.io.pgL s.mem).cleanPhase = 0 then 0 else 24) := by
    by_cases h0 : bpL.io.usePaged = 0
    · simp [h0]
    · simp only [h0, false_or, hu_s₂ h0]
  set slack' :=
    if bpL.io.usePaged = 0 ∨ (extractPageUnperm bpL.io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hio₃ : bpL.io.StateInv (bp₀.nSide - 1) slack' s₃.mem := hslack_eq ▸ hio₃_raw
  -- Step 4: `bpCommitPopMetaProg`
  set s₄ := (Memory.spec 0).clientState s₃ (bpCommitPopMetaProg (bpL.mp.toCtx, b))
  have hfr₄ : s₄.frontier = s.frontier :=
    (runClient_frontier_bpCommitPopMetaProg _ s₃).trans hfr₃
  have hex₄ : extractBlockPool bpL.mp s₄.mem = bp₁.commitPopBktBack b := by
    have h := bpCommitPopMetaProg_spec (hfr₃.symm ▸ hv.mp_valid) (hex₃ ▸ hbal₁) hb
      (by rw [hex₃, hn₁]; exact hn_pos) (by rw [hex₃, hn₁]; exact hinv.2.1)
    rwa [hex₃] at h
  obtain ⟨hio₄, harr₄, hpart₄⟩ := meta_preserves_io (hfr₃.symm ▸ hv)
    (bpCommitPopMetaProg_frame (hfr₃.symm ▸ hv.mp_valid) b) hio₃
  -- Pure specs for `commitPopBktBack` + `16` `bktTickOne` + `16` `topCleanOne`
  have htp_end₁ : bp₁.toPhys b (bp₁.bktCount b - 1) = bp₁.nSide - 1 := by
    rwa [hbc₁ b, hn₁]
  have hcnt₁ : 0 < bp₁.bktCount b := by rwa [hbc₁ b]
  have hb₁ : b < bp₁.M := hM₁.symm ▸ hb
  obtain ⟨hsi₄, hM_cp, _, hn_cp, _, _, _, htp_cp⟩ :=
    hbal₁.commitPopBktBack_spec hb₁ hcnt₁ (hn₁.symm ▸ hn_pos) htp_end₁
  have hb_cp : b < (bp₁.commitPopBktBack b).M := hM_cp.symm ▸ hb₁
  have hns_s₄ : (extractBlockPool bpL.mp s₄.mem).nSide = bp₀.nSide - 1 :=
    (congrArg BlockPoolState.nSide hex₄).trans (hn_cp.trans (congrArg (· - 1) hn₁))
  -- Step 5: `bpRunBktTicks16Prog`
  obtain ⟨hfr₅_rel, hex₅, hsi₅, hn₅, hio₅, harr₅, hpart₅⟩ :=
    bpRunBktTicks16Prog_spec (hfr₄.symm ▸ hv) (hex₄.symm ▸ hsi₄) hb
      (by rw [hns_s₄]; exact (Nat.sub_le _ 1).trans hinv.2.1) (hns_s₄.symm ▸ hio₄)
  dsimp only [BlockPoolLayout.toCtx] at hfr₅_rel hex₅ hio₅ harr₅ hpart₅
  set s₅ := (Memory.spec 0).clientState s₄
    (bpRunBktTicks16Prog ((bpL.mp.toCtx, bpL.io.toCtx), b))
  have hfr₅ : s₅.frontier = s.frontier := hfr₅_rel.trans hfr₄
  rw [hex₄] at hex₅ hsi₅ hn₅ hio₅ harr₅
  rw [Nat.sub_self] at hsi₅
  set st_bkt := BlockPoolState.runBktTicks b 16
    (bp₁.commitPopBktBack b, slotIoPairAt bpL.io s₄.mem)
  -- Step 6: `bpRunTopClean16Prog`
  obtain ⟨_, hex₆, _, hn₆, hio₆, harr₆, hpart₆⟩ :=
    bpRunTopClean16Prog_spec (b₀ := b) (hfr₅.symm ▸ hv) (hex₅.symm ▸ hsi₅)
      (by rw [hex₅, hn₅, hn_cp, hn₁]; exact (Nat.sub_le _ 1).trans hinv.2.1)
      (hex₅.symm ▸ hio₅)
  dsimp only [BlockPoolLayout.toCtx] at hex₆ hio₆ harr₆ hpart₆
  set s₆ := (Memory.spec 0).clientState s₅ (bpRunTopClean16Prog (bpL.mp.toCtx, bpL.io.toCtx))
  rw [hex₅] at hex₆ hn₆ hio₆ harr₆
  obtain ⟨hfst_tc, _, _, harr_tc⟩ :=
    runTopCleanTicks_stepInv_and_congr 16 hsi₅
      (arr₁ := slotIoPairAt bpL.io s₅.mem) (arr₂ := st_bkt.2) harr₅
  rw [hfst_tc] at hex₆ hn₆ hio₆ harr₆
  have hbal_end := hbal₁.popBktBack_rebalance_balanced hb₁ hcnt₁ (hn₁.symm ▸ hn_pos) htp_end₁
    (slotIoPairAt bpL.io s₄.mem)
  dsimp only at hbal_end
  obtain ⟨hbal₆, hn_end, hbc_b_end, hbc_ne_end, harr_end⟩ := hbal_end
  have hn_end₀ : (BlockPoolState.runTopCleanTicks 16 st_bkt).1.nSide = bp₀.nSide - 1 :=
    hn_end.trans (congrArg (· - 1) hn₁)
  refine ⟨⟨hex₆ ▸ hbal₆,
      by rw [hex₆, hn_end₀]; exact (Nat.sub_le _ 1).trans hinv.2.1,
      hex₆ ▸ hio₆⟩,
    hex₆ ▸ hn_end₀,
    hex₆ ▸ (hbc_b_end.trans (congrArg (· - 1) (hbc₁ b))),
    fun b' hne => hex₆ ▸ (hbc_ne_end b' hne).trans (hbc₁ b'),
    fun b' hb' loc' hloc' => ?_,
    fun hnz => ?_⟩
  · rw [hex₆] at hloc'
    unfold bpPairAt; rw [hex₆]
    set res_end := BlockPoolState.runTopCleanTicks 16 st_bkt
    have hM_bkt : st_bkt.1.M = bpL.mp.M :=
      ((runBktTicks_stepInv_and_congr 16 16 hb_cp hsi₄
        (arr₁ := slotIoPairAt bpL.io s₄.mem) (arr₂ := slotIoPairAt bpL.io s₄.mem)
        (fun _ _ => rfl)).2.2.1.trans hM_cp).trans hM₁
    obtain ⟨_, hM_tc, _, _, hbc_tc, _, _⟩ := hsi₅.runTopCleanTicks_spec 16 st_bkt.2
    obtain ⟨_, _, _, _, hbc_bt, _, _⟩ :=
      hsi₄.runBktTicks_spec 16 hb_cp (slotIoPairAt bpL.io s₄.mem)
    have hM_end : res_end.1.M = bpL.mp.M := hM_tc.trans hM_bkt
    have htp_lt_end : res_end.1.toPhys b' loc' < res_end.1.nSide :=
      hbal₆.core.toPhys_lt (hM_end.symm ▸ hb') hloc'
    rw [harr₆ _ htp_lt_end, harr_tc _ (hn₆ ▸ htp_lt_end),
      harr_end b' (hM₁.symm ▸ hb') loc' hloc']
    have hbc_end_cp : res_end.1.bktCount b' = (bp₁.commitPopBktBack b).bktCount b' :=
      (hbc_tc b').trans (hbc_bt b')
    have hloc_cp : loc' < (bp₁.commitPopBktBack b).bktCount b' := hbc_end_cp ▸ hloc'
    have htp₁_lt_sub : bp₁.toPhys b' loc' < bp₀.nSide - 1 := by
      have h := (htp_cp b' (hM₁.symm ▸ hb') loc' hloc_cp).2
      have htp_eq := (htp_cp b' (hM₁.symm ▸ hb') loc' hloc_cp).1
      rw [htp_eq, hn₁] at h; exact h
    have htp₁_lt₀ : bp₁.toPhys b' loc' < bp₀.nSide := htp₁_lt_sub.trans_le (Nat.sub_le _ 1)
    have hloc₀ : loc' < bp₀.bktCount b' := by
      by_cases hbe : b' = b
      · subst b'; rw [hbc_b_end, hbc₁ b] at hloc'; omega
      · rw [hbc_ne_end b' hbe, hbc₁ b'] at hloc'; exact hloc'
    rw [harr₄ _ htp₁_lt_sub, harr₃ _ htp₁_lt_sub, harr₂ _ htp₁_lt₀]
    exact (applyOptSwap_congr hsw_lt harr₁ _ htp₁_lt₀).trans
      (harr_prep (slotIoPairAt bpL.io s.mem) b' loc' hb' hloc₀)
  · obtain ⟨hu₁, hp₁⟩ := hpart₁ hnz
    obtain ⟨hu₂, hp₂⟩ := hpart₂ hnz
    obtain ⟨hvl₃, hti₃, hp₃⟩ := hpart₃ hnz
    obtain ⟨hu₄, hp₄⟩ := hpart₄ hnz
    obtain ⟨hu₅, hp₅⟩ := hpart₅ hnz
    obtain ⟨hu₆, hp₆⟩ := hpart₆ hnz
    have hst₁ : extractPagePair bpL.io.pgL s₁.mem = extractPagePair bpL.io.pgL s.mem :=
      congrArg PageUnpermState.st hu₁
    have hst₂ : extractPagePair bpL.io.pgL s₂.mem = extractPagePair bpL.io.pgL s.mem :=
      (congrArg PageUnpermState.st hu₂).trans hst₁
    have hst₄ : extractPagePair bpL.io.pgL s₄.mem = extractPagePair bpL.io.pgL s₃.mem :=
      congrArg PageUnpermState.st hu₄
    have hst₅ : extractPagePair bpL.io.pgL s₅.mem = extractPagePair bpL.io.pgL s₃.mem :=
      (congrArg PageUnpermState.st hu₅).trans hst₄
    have hst₆ : extractPagePair bpL.io.pgL s₆.mem = extractPagePair bpL.io.pgL s₃.mem :=
      (congrArg PageUnpermState.st hu₆).trans hst₅
    refine ⟨by rw [hst₆, hvl₃, hst₂], by rw [hst₆, hti₃, hst₂], fun idx hidx => ?_⟩
    have hidx₂ : idx < (extractPagePair bpL.io.pgL s₂.mem).virtLen bpL.io.partner.side := by
      rwa [hst₂]
    have hidx₃ : idx < (extractPagePair bpL.io.pgL s₃.mem).virtLen bpL.io.partner.side := by
      rwa [hvl₃]
    exact (hp₆ idx (by rw [hst₅]; exact hidx₃)).trans
      ((hp₅ idx (by rw [hst₄]; exact hidx₃)).trans
        ((hp₄ idx hidx₃).trans
          ((hp₃ idx hidx₂).trans
            ((hp₂ idx (by rw [hst₁]; exact hidx)).trans (hp₁ idx hidx)))))

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
