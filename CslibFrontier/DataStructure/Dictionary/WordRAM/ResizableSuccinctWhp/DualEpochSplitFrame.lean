/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpoch
-- Retain private `import all` solely to unfold unexposed `Memory.Prog` bodies of the epoch stack
-- without modifying existing upstream modules or invalidating cached `.olean` artifacts.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPool
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochState
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeFallbackBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFallback
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochCtx
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochSubEpoch
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochDrain
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochAdvance
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemove
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFast
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpoch

/-!
# Split-Pair Cursor and Quotient-Bound Frame Preservation (`DualEpochSplitFrame`)

When an active epoch operates in unpaged `SplitPair` mode (`io.usePaged = 0 ∧ io.sideBit ≠ 0`,
used during `slideUp` and `slideDown` phases `3` and `10`), `io.OwnsAddr` includes the split-cursor
word `io.pgL.metaBase` (`base + hdrSplit`) so that slide batches may advance it, while upper-stream
slots `idx ∈ [mem io.pgL.metaBase, nSide)` are stored at width `io.pgL.offTail` (`qBitsHi`) and
masked `% 2 ^ io.pgL.qBits` (`2 ^ qBitsLo`) on read.

This module proves that user dictionary mutations (`epochInsertProg` and `epochDeleteProg`):
1. Leave `s.mem io.pgL.metaBase` unchanged in both the small (`N = 0`) and large
   (`whpThreshold c ≤ N`, fast or fallback) regimes.
2. Preserve `SplitHiQuotBounded io nSide s.mem` (`pairQuotAt ... idx < 2 ^ io.pgL.qBits` across
   all live upper-stream slots `idx ∈ [s.mem io.pgL.metaBase, nSide)`), discharging the quotient
   bound preconditions of `slotIoPairAt_split_zero_eq_direct` (`slideUp` completion) and
   `slideDownBatchProg_spec` (`slideDown` batches).

## Main definitions

* `SplitHiQuotBounded`: raw upper-stream quotients in `[mem io.pgL.metaBase, nSide)` lie below
  `2 ^ io.pgL.qBits`.

## Main results

* `epochInsertProg_preserves_split_cursor_small`, `epochDeleteProg_preserves_split_cursor_small`
* `epochInsertProg_preserves_split_cursor_large`, `epochDeleteProg_preserves_split_cursor_large`
* `epochInsertProg_preserves_hiQuot_small`, `epochDeleteProg_preserves_hiQuot_small`
* `epochInsertProg_preserves_hiQuot_large`, `epochDeleteProg_preserves_hiQuot_large`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

/-! ## Section 1: Compositional Frame Predicate `ModOnly` and `SplitHiQuotBounded` -/

/-- In unpaged `SplitPair` mode (`io.usePaged = 0 ∧ io.sideBit ≠ 0`), every live upper-stream slot
`idx ∈ [mem io.pgL.metaBase, nSide)` stores a raw `offTail`-bit quotient strictly below
`2 ^ io.pgL.qBits` (`2 ^ qBitsLo`), ensuring `slotIoPairAt` agrees with unmasked `arenaPairAt` at
`slideUp` completion (`mem io.pgL.metaBase = 0`) and across `slideDown` batches. -/
@[expose] def SplitHiQuotBounded (io : SlotIoLayout) (nSide : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ idx, mem io.pgL.metaBase ≤ idx → idx < nSide →
    pairQuotAt io.pgL.itemBase io.pgL.offTail io.pgL.vBits io.pgL.w mem idx < 2 ^ io.pgL.qBits

private def ModOnly {α : Type} (Mod : ℕ → Prop) (p : Memory.Prog α) : Prop :=
  ∀ s, ((Memory.spec 0).clientState s p).frontier = s.frontier ∧
    ∀ addr, ¬Mod addr → ((Memory.spec 0).clientState s p).mem addr = s.mem addr

private theorem modOnly_pure {α : Type} {Mod : ℕ → Prop} (x : α) :
    ModOnly Mod (pure x : Memory.Prog α) :=
  fun _ => ⟨rfl, fun _ _ => rfl⟩

private theorem modOnly_read {Mod : ℕ → Prop} (a : ℕ) :
    ModOnly Mod (Memory.read a) :=
  fun _ => ⟨rfl, fun _ _ => rfl⟩

private theorem modOnly_ro {α : Type} {Mod : ℕ → Prop} {p : Memory.Prog α}
    (hst : ∀ s, (Memory.spec 0).clientState s p = s) :
    ModOnly Mod p :=
  fun s => by rw [hst s]; exact ⟨rfl, fun _ _ => rfl⟩

private theorem modOnly_write {Mod : ℕ → Prop} {a : ℕ} (ha : Mod a) (v : ℕ) :
    ModOnly Mod (Memory.write a v) := fun s =>
  ⟨rfl, fun addr hnot => by
    change Function.update s.mem a v addr = s.mem addr
    exact Function.update_of_ne (fun heq : addr = a => hnot (heq ▸ ha)) v s.mem⟩

private theorem modOnly_mono {α : Type} {Mod₁ Mod₂ : ℕ → Prop} {p : Memory.Prog α}
    (hp : ModOnly Mod₁ p) (hsub : ∀ a, Mod₁ a → Mod₂ a) :
    ModOnly Mod₂ p := fun s =>
  ⟨(hp s).1, fun addr hnot => (hp s).2 addr (fun h1 => hnot (hsub addr h1))⟩

private theorem modOnly_of_frame {α : Type} {Mod₁ Mod : ℕ → Prop} {C : ℕ} {p : Memory.Prog α}
    (hf : BoundedFrameProg Mod₁ C p) (hsub : ∀ a, Mod₁ a → Mod a) :
    ModOnly Mod p := fun s =>
  ⟨hf.frontier_eq s, fun addr hnot => hf.mem_outside s addr (fun h1 => hnot (hsub addr h1))⟩

private theorem modOnly_bind {α β : Type} {Mod : ℕ → Prop} {p : Memory.Prog α}
    {q : α → Memory.Prog β} (hp : ModOnly Mod p) (hq : ∀ x, ModOnly Mod (q x)) :
    ModOnly Mod (p >>= q) := fun s => by
  rw [StateTransitionSpec.clientState_bind]
  obtain ⟨hfr₁, hm₁⟩ := hp s
  obtain ⟨hfr₂, hm₂⟩ := hq ((Memory.spec 0).clientResult s p) ((Memory.spec 0).clientState s p)
  exact ⟨hfr₂.trans hfr₁, fun addr hnot => (hm₂ addr hnot).trans (hm₁ addr hnot)⟩

private theorem modOnly_ite {α : Type} {Mod : ℕ → Prop} {P : Prop} [Decidable P]
    {p₁ p₂ : Memory.Prog α} (h₁ : P → ModOnly Mod p₁) (h₂ : ¬P → ModOnly Mod p₂) :
    ModOnly Mod (if P then p₁ else p₂) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact h₁ hP
  · rw [ite_eq_right hP]; exact h₂ hP

/-! ## Section 2: Unpaged Split-Safe `SlotIoLayout` Geometry and Primitives -/

private def IoSplitMod (io : SlotIoLayout) (addr : ℕ) : Prop :=
  io.OwnsAddr addr ∧ addr ≠ io.pgL.metaBase

private structure SplitIoGeom (io : SlotIoLayout) : Prop where
  w_pos : 0 < io.pgL.w
  up_zero : io.usePaged = 0
  sb_ne : io.sideBit ≠ 0
  q_le_ot : io.pgL.qBits ≤ io.pgL.offTail
  ot_le_w : io.pgL.offTail ≤ io.pgL.w
  mb_lt_od : io.pgL.metaBase < io.pgL.offDir
  od_le_ib : io.pgL.offDir + 2 ≤ io.pgL.itemBase
  own_mb : io.OwnsAddr io.pgL.metaBase

private theorem SplitIoGeom.mb_lt_ib {io : SlotIoLayout} (hg : SplitIoGeom io) :
    io.pgL.metaBase < io.pgL.itemBase := by
  have h1 := hg.mb_lt_od
  have h2 := hg.od_le_ib
  omega

private theorem split_io_geom {io : SlotIoLayout} {w fr : ℕ}
    (hv : io.Valid w fr) (hup : io.usePaged = 0) (hsb : io.sideBit ≠ 0) :
    SplitIoGeom io := by
  have hw := hv.w_pos
  unfold SlotIoLayout.Valid at hv
  rw [ite_eq_left hup] at hv
  obtain ⟨_, hw_eq, _, _, _, htail⟩ := hv
  rw [ite_eq_right hsb] at htail
  obtain ⟨hq_ot, hot_w, hmb_od, hod_ib, _⟩ := htail
  have hown : io.OwnsAddr io.pgL.metaBase := by
    unfold SlotIoLayout.OwnsAddr
    rw [ite_eq_left hup, ite_eq_right hsb]
    exact Or.inl rfl
  exact ⟨hw, hup, hsb, hq_ot, hw_eq ▸ hot_w, hmb_od, hod_ib, hown⟩

private def HiQuotPres (io : SlotIoLayout) (m₁ m₂ : ℕ → ℕ) : Prop :=
  m₂ io.pgL.metaBase = m₁ io.pgL.metaBase ∧
  ∀ idx, m₁ io.pgL.metaBase ≤ idx → idx < io.pgL.nCap →
    pairQuotAt io.pgL.itemBase io.pgL.offTail io.pgL.vBits io.pgL.w m₂ idx =
      pairQuotAt io.pgL.itemBase io.pgL.offTail io.pgL.vBits io.pgL.w m₁ idx ∨
    pairQuotAt io.pgL.itemBase io.pgL.offTail io.pgL.vBits io.pgL.w m₂ idx < 2 ^ io.pgL.qBits

private theorem hiQuotPres_refl (io : SlotIoLayout) (m : ℕ → ℕ) :
    HiQuotPres io m m :=
  ⟨rfl, fun _ _ _ => Or.inl rfl⟩

private theorem hiQuotPres_trans {io : SlotIoLayout} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁ : HiQuotPres io m₁ m₂) (h₂ : HiQuotPres io m₂ m₃) :
    HiQuotPres io m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, fun idx hsp hlt => by
    rcases h₂.2 idx (h₁.1.symm ▸ hsp) hlt with heq | hlt₃
    · rcases h₁.2 idx hsp hlt with heq₁ | hlt₂
      · exact Or.inl (heq.trans heq₁)
      · exact Or.inr (heq ▸ hlt₂)
    · exact Or.inr hlt₃⟩

private theorem hiQuotPres_of_io_unchanged {io : SlotIoLayout} (hg : SplitIoGeom io)
    {m₁ m₂ : ℕ → ℕ} (hout : ∀ addr, io.OwnsAddr addr → m₂ addr = m₁ addr) :
    HiQuotPres io m₁ m₂ := by
  refine ⟨hout _ hg.own_mb, fun idx _ hlt => Or.inl ?_⟩
  have hq_lt := wOffQ_add_one_lt_pairStreamWords
    (n := io.pgL.nCap) (q_bits := io.pgL.offTail) (v_bits := io.pgL.vBits) hg.w_pos hlt
  have hmem_hi : ∀ a, io.pgL.itemBase ≤ a →
      a < io.pgL.itemBase + pairStreamWords io.pgL.nCap io.pgL.offTail io.pgL.vBits io.pgL.w →
      m₂ a = m₁ a := fun a h1 h2 =>
    hout a (by
      unfold SlotIoLayout.OwnsAddr
      rw [ite_eq_left hg.up_zero, ite_eq_right hg.sb_ne]
      exact Or.inr (Or.inr ⟨h1, h2⟩))
  unfold pairQuotAt readBitSlice
  dsimp only
  rw [hmem_hi (io.pgL.itemBase + wOffQ io.pgL.offTail io.pgL.vBits io.pgL.w idx)
      (Nat.le_add_right _ _) (by omega),
    hmem_hi (io.pgL.itemBase + wOffQ io.pgL.offTail io.pgL.vBits io.pgL.w idx + 1)
      (by omega) (by omega)]

private theorem hiQuotPres_preserves_bounded {io : SlotIoLayout} {n₁ n₂ : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hp : HiQuotPres io m₁ m₂) (hbound : SplitHiQuotBounded io n₁ m₁)
    (hle : n₂ ≤ n₁) (hcap : n₂ ≤ io.pgL.nCap) :
    SplitHiQuotBounded io n₂ m₂ := by
  intro idx hsp hlt
  have hsp₁ : m₁ io.pgL.metaBase ≤ idx := hp.1 ▸ hsp
  have hlt₁ : idx < n₁ := hlt.trans_le hle
  have hq₁ : pairQuotAt io.pgL.itemBase io.pgL.offTail io.pgL.vBits io.pgL.w m₁ idx <
      2 ^ io.pgL.qBits := hbound idx hsp₁ hlt₁
  rcases hp.2 idx hsp₁ (hlt.trans_le hcap) with heq | hlt₂
  · exact heq ▸ hq₁
  · exact hlt₂

private theorem writePair_ne_of_lt_base {ib qB vB wv idx q v addr : ℕ} (mem : ℕ → ℕ)
    (hlt : addr < ib) :
    writePair ib qB vB wv mem idx q v addr = mem addr := by
  unfold writePair writePairVal writePairQuot writeBitSlice
  dsimp only
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

private theorem modOnly_slotIoWriteRaw {io : SlotIoLayout} (hg : SplitIoGeom io)
    (idx : ℕ) (qv : ℕ × ℕ) :
    ModOnly (IoSplitMod io) (slotIoWriteRawProg ((io.toCtx, idx), qv)) := by
  rcases qv with ⟨q, v⟩
  intro s
  have hf := slotIoWriteProg_frame (io := io) hg.w_pos idx q v
  unfold slotIoWriteProg at hf
  refine ⟨hf.frontier_eq s, fun addr hnot => ?_⟩
  by_cases heq : addr = io.pgL.metaBase
  · subst heq
    unfold slotIoWriteRawProg
    dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    rw [ite_eq_left hg.up_zero]
    by_cases hlt : idx < io.pgL.nCap
    · rw [ite_eq_left hlt, ite_eq_right hg.sb_ne, StateTransitionSpec.clientState_bind]
      have hrd_st : (Memory.spec 0).clientState s (Memory.read io.pgL.metaBase) = s := rfl
      rw [hrd_st]
      by_cases hsp : idx < (Memory.spec 0).clientResult s (Memory.read io.pgL.metaBase)
      · rw [ite_eq_left hsp, clientState_writePairGenProg]
        exact writePair_ne_of_lt_base s.mem hg.mb_lt_od
      · rw [ite_eq_right hsp, clientState_writePairGenProg]
        exact writePair_ne_of_lt_base s.mem hg.mb_lt_ib
    · rw [ite_eq_right hlt]; rfl
  · exact hf.mem_outside s addr (fun hown => hnot ⟨hown, heq⟩)

private theorem modOnly_slotIoSwapRaw {io : SlotIoLayout} (hg : SplitIoGeom io) (p₁ p₂ : ℕ) :
    ModOnly (IoSplitMod io) (slotIoSwapRawProg (io.toCtx, (p₁, p₂))) := by
  unfold slotIoSwapRawProg
  dsimp only
  refine modOnly_ite (fun _ => modOnly_pure ()) fun _ => ?_
  refine modOnly_bind (modOnly_ro (clientState_slotIoReadRawProg _)) fun qv₁ => ?_
  refine modOnly_bind (modOnly_ro (clientState_slotIoReadRawProg _)) fun qv₂ => ?_
  refine modOnly_bind (modOnly_slotIoWriteRaw hg p₁ qv₂) fun _ => ?_
  exact modOnly_slotIoWriteRaw hg p₂ qv₁

private theorem modOnly_slotIoAppendRaw {io : SlotIoLayout} (hg : SplitIoGeom io)
    (nSide : ℕ) (qv : ℕ × ℕ) :
    ModOnly (IoSplitMod io) (slotIoAppendRawProg ((io.toCtx, nSide), qv)) := by
  rcases qv with ⟨q, v⟩
  intro s
  have hf := slotIoAppendProg_frame (io := io) hg.w_pos nSide q v
  unfold slotIoAppendProg at hf
  refine ⟨hf.frontier_eq s, fun addr hnot => ?_⟩
  by_cases heq : addr = io.pgL.metaBase
  · subst heq
    unfold slotIoAppendRawProg
    dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    rw [ite_eq_left hg.up_zero]
    by_cases hlt : nSide < io.pgL.nCap
    · rw [ite_eq_left hlt, ite_eq_right hg.sb_ne, StateTransitionSpec.clientState_bind]
      have hrd_st : (Memory.spec 0).clientState s (Memory.read io.pgL.metaBase) = s := rfl
      rw [hrd_st]
      by_cases hsp : nSide < (Memory.spec 0).clientResult s (Memory.read io.pgL.metaBase)
      · rw [ite_eq_left hsp, clientState_writePairGenProg]
        exact writePair_ne_of_lt_base s.mem hg.mb_lt_od
      · rw [ite_eq_right hsp, clientState_writePairGenProg]
        exact writePair_ne_of_lt_base s.mem hg.mb_lt_ib
    · rw [ite_eq_right hlt]; rfl
  · exact hf.mem_outside s addr (fun hown => hnot ⟨hown, heq⟩)

private theorem modOnly_slotIoPopBackRaw {io : SlotIoLayout} (hup : io.usePaged = 0) :
    ModOnly (IoSplitMod io) (slotIoPopBackRawProg io.toCtx) := by
  unfold slotIoPopBackRawProg
  dsimp only [SlotIoLayout.toCtx]
  rw [ite_eq_left hup]
  exact modOnly_pure ()

private theorem splitPairWrite_hiQuotPres {io : SlotIoLayout} (hg : SplitIoGeom io)
    {idx q v : ℕ} (hq : q < 2 ^ io.pgL.qBits) (mem : ℕ → ℕ)
    (hmb : splitPairWrite io.splitCfg (mem io.pgL.metaBase) mem idx q v io.pgL.metaBase =
      mem io.pgL.metaBase) :
    HiQuotPres io mem (splitPairWrite io.splitCfg (mem io.pgL.metaBase) mem idx q v) := by
  refine ⟨hmb, fun idx' hsp' _ => ?_⟩
  have hnot_lt' : ¬idx' < mem io.pgL.metaBase := Nat.not_lt.mpr hsp'
  by_cases heq : idx' = idx
  · subst heq
    unfold splitPairWrite SlotIoLayout.splitCfg
    dsimp only
    rw [ite_eq_right hnot_lt']
    have hq_ot : q < 2 ^ io.pgL.offTail :=
      hq.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hg.q_le_ot)
    rw [pairQuotAt_writePair_self hg.w_pos mem hq_ot]
    exact Or.inr hq
  · have hne := splitPairRead_splitPairWrite_of_ne (cfg := io.splitCfg)
      (s_split := mem io.pgL.metaBase) (idx := idx) (idx' := idx') (q := q) (v := v)
      hg.w_pos (by dsimp only [SlotIoLayout.splitCfg]; have := hg.q_le_ot; omega) hg.od_le_ib
      mem heq
    unfold splitPairRead SlotIoLayout.splitCfg at hne
    dsimp only at hne
    rw [ite_eq_right hnot_lt', ite_eq_right hnot_lt'] at hne
    exact Or.inl (congrArg Prod.fst hne)

private theorem hiQuotPres_slotIoWriteRaw {io : SlotIoLayout} (hg : SplitIoGeom io)
    {idx : ℕ} {qv : ℕ × ℕ} (hq : qv.1 < 2 ^ io.pgL.qBits) (s : Memory.State) :
    HiQuotPres io s.mem
      ((Memory.spec 0).clientState s (slotIoWriteRawProg ((io.toCtx, idx), qv))).mem := by
  rcases qv with ⟨q, v⟩
  have hmb : ((Memory.spec 0).clientState s
      (slotIoWriteRawProg ((io.toCtx, idx), (q, v)))).mem io.pgL.metaBase =
      s.mem io.pgL.metaBase :=
    (modOnly_slotIoWriteRaw hg idx (q, v) s).2 io.pgL.metaBase (fun h => h.2 rfl)
  unfold slotIoWriteRawProg
  dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  rw [ite_eq_left hg.up_zero]
  by_cases hlt : idx < io.pgL.nCap
  · rw [ite_eq_left hlt, ite_eq_right hg.sb_ne]
    have hrd_st : (Memory.spec 0).clientState s (Memory.read io.pgL.metaBase) = s := rfl
    have hrd_res : (Memory.spec 0).clientResult s (Memory.read io.pgL.metaBase) =
        s.mem io.pgL.metaBase := rfl
    rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res]
    have hmem_eq : ((Memory.spec 0).clientState s
        (if idx < s.mem io.pgL.metaBase then
          writePairGenProg
            ((((io.pgL.offDir, (io.pgL.qBits, io.pgL.vBits)), io.pgL.w), idx), (q, v))
        else
          writePairGenProg
            ((((io.pgL.itemBase, (io.pgL.offTail, io.pgL.vBits)), io.pgL.w), idx), (q, v)))).mem =
        splitPairWrite io.splitCfg (s.mem io.pgL.metaBase) s.mem idx q v := by
      unfold splitPairWrite SlotIoLayout.splitCfg; dsimp only
      by_cases hsp : idx < s.mem io.pgL.metaBase <;>
        simp only [hsp, ↓reduceIte] <;> rw [clientState_writePairGenProg]
    unfold slotIoWriteRawProg at hmb
    dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx] at hmb
    rw [ite_eq_left hg.up_zero, ite_eq_left hlt, ite_eq_right hg.sb_ne,
      StateTransitionSpec.clientState_bind, hrd_st, hrd_res, hmem_eq] at hmb
    rw [hmem_eq]
    exact splitPairWrite_hiQuotPres hg hq s.mem hmb
  · rw [ite_eq_right hlt]; exact hiQuotPres_refl io s.mem

private theorem hiQuotPres_slotIoAppendRaw {io : SlotIoLayout} (hg : SplitIoGeom io)
    {nSide : ℕ} {qv : ℕ × ℕ} (hq : qv.1 < 2 ^ io.pgL.qBits) (s : Memory.State) :
    HiQuotPres io s.mem
      ((Memory.spec 0).clientState s (slotIoAppendRawProg ((io.toCtx, nSide), qv))).mem := by
  have heq : (Memory.spec 0).clientState s (slotIoAppendRawProg ((io.toCtx, nSide), qv)) =
      (Memory.spec 0).clientState s (slotIoWriteRawProg ((io.toCtx, nSide), qv)) := by
    rcases qv with ⟨q, v⟩
    unfold slotIoAppendRawProg slotIoWriteRawProg
    dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    rw [ite_eq_left hg.up_zero, ite_eq_left hg.up_zero]
  rw [heq]
  exact hiQuotPres_slotIoWriteRaw hg hq s

private theorem slotIoAppendRaw_hi_self {io : SlotIoLayout} (hg : SplitIoGeom io)
    {nSide : ℕ} {qv : ℕ × ℕ} {s : Memory.State}
    (hlt : nSide < io.pgL.nCap) (hsp : s.mem io.pgL.metaBase ≤ nSide)
    (hq : qv.1 < 2 ^ io.pgL.qBits) :
    pairQuotAt io.pgL.itemBase io.pgL.offTail io.pgL.vBits io.pgL.w
      ((Memory.spec 0).clientState s (slotIoAppendRawProg ((io.toCtx, nSide), qv))).mem nSide <
      2 ^ io.pgL.qBits := by
  rcases qv with ⟨q, v⟩
  have hnot_lt : ¬nSide < s.mem io.pgL.metaBase := Nat.not_lt.mpr hsp
  have hq_ot : q < 2 ^ io.pgL.offTail :=
    hq.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hg.q_le_ot)
  unfold slotIoAppendRawProg
  dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  have hrd_st : (Memory.spec 0).clientState s (Memory.read io.pgL.metaBase) = s := rfl
  have hrd_res : (Memory.spec 0).clientResult s (Memory.read io.pgL.metaBase) =
      s.mem io.pgL.metaBase := rfl
  rw [ite_eq_left hg.up_zero, ite_eq_left hlt, ite_eq_right hg.sb_ne,
    StateTransitionSpec.clientState_bind, hrd_st, hrd_res, ite_eq_right hnot_lt,
    clientState_writePairGenProg, pairQuotAt_writePair_self hg.w_pos s.mem hq_ot]
  exact hq

private theorem slotIoReadRaw_fst_lt {io : SlotIoLayout} (hg : SplitIoGeom io)
    (idx : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (slotIoReadRawProg (io.toCtx, idx))).1 <
      2 ^ io.pgL.qBits := by
  unfold slotIoReadRawProg
  dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  rw [ite_eq_left hg.up_zero]
  by_cases hlt : idx < io.pgL.nCap
  · rw [ite_eq_left hlt, ite_eq_right hg.sb_ne]
    have hrd_st : (Memory.spec 0).clientState s (Memory.read io.pgL.metaBase) = s := rfl
    have hrd_res : (Memory.spec 0).clientResult s (Memory.read io.pgL.metaBase) =
        s.mem io.pgL.metaBase := rfl
    rw [prog_clientResult_bind, hrd_st, hrd_res]
    by_cases hsp : idx < s.mem io.pgL.metaBase
    · rw [ite_eq_left hsp, clientResult_readPairGenProg]
      exact pairQuotAt_lt ..
    · rw [ite_eq_right hsp, prog_clientResult_bind, clientState_readPairGenProg,
        clientResult_readPairGenProg]
      by_cases hqw : io.pgL.qBits < io.pgL.w
      · rw [ite_eq_left hqw, prog_clientResult_bind,
          show (Memory.spec 0).clientState s (pure _) = s from rfl,
          prog_clientResult_pure, prog_clientResult_pure,
          Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · rw [ite_eq_right hqw, prog_clientResult_pure]
        have hot_qb : io.pgL.offTail ≤ io.pgL.qBits := by
          have := hg.ot_le_w; omega
        exact (pairQuotAt_lt ..).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hot_qb)
  · rw [ite_eq_right hlt, prog_clientResult_pure]
    exact Nat.two_pow_pos _

private theorem hiQuotPres_slotIoSwapRaw {io : SlotIoLayout} (hg : SplitIoGeom io)
    (p₁ p₂ : ℕ) (s : Memory.State) :
    HiQuotPres io s.mem
      ((Memory.spec 0).clientState s (slotIoSwapRawProg (io.toCtx, (p₁, p₂)))).mem := by
  unfold slotIoSwapRawProg
  dsimp only
  by_cases heq : p₁ = p₂
  · rw [ite_eq_left heq]; exact hiQuotPres_refl io s.mem
  · rw [ite_eq_right heq, StateTransitionSpec.clientState_bind, clientState_slotIoReadRawProg,
      StateTransitionSpec.clientState_bind, clientState_slotIoReadRawProg,
      StateTransitionSpec.clientState_bind]
    have hq₁ := slotIoReadRaw_fst_lt hg p₁ s
    have hq₂ := slotIoReadRaw_fst_lt hg p₂ s
    exact hiQuotPres_trans (hiQuotPres_slotIoWriteRaw hg hq₂ s)
      (hiQuotPres_slotIoWriteRaw hg hq₁ _)

/-! ## Section 3: Small-Epoch Split-Cursor and Quotient-Bound Preservation -/

/-- `epochInsertProg` preserves the split cursor `L.io.pgL.metaBase` in unpaged `SplitPair` mode
(`L.io.usePaged = 0 ∧ L.io.sideBit ≠ 0`). -/
theorem epochInsertProg_preserves_split_cursor_small {L : SmallEpochLayout} {w pBase : ℕ}
    {s : Memory.State} (hv : L.Valid w s.frontier) (hpt : L.ParamTable pBase s.mem)
    (hup : L.io.usePaged = 0) (hsb : L.io.sideBit ≠ 0) (u_val v_val : ℕ) :
    ((Memory.spec 0).clientState s (epochInsertProg ((pBase, u_val), v_val))).mem
      L.io.pgL.metaBase = s.mem L.io.pgL.metaBase := by
  have hg := split_io_geom hv.io_valid hup hsb
  have hne_hdr : L.io.pgL.metaBase ≠ L.metaBase + 1 :=
    fun heq => hv.disjoint_hdr _ (Or.inr heq) hg.own_mb
  have hstep : (Memory.spec 0).clientState s (epochInsertProg ((pBase, u_val), v_val)) =
      (Memory.spec 0).clientState s
        (smallEpochInsertRawProg (((L.io.toCtx, L.metaBase), u_val), v_val)) := by
    unfold epochInsertProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hpt.1, ite_eq_left rfl, StateTransitionSpec.clientState_bind, clientState_read_eq,
      prog_clientResult_read, hpt.2.1, StateTransitionSpec.clientState_bind,
      clientState_loadSmallIoCtxProg, clientResult_loadSmallIoCtxProg hpt]
  rw [hstep]
  let ModS : ℕ → Prop := fun a => a = L.metaBase + 1 ∨ IoSplitMod L.io a
  have hmod : ModOnly ModS
      (smallEpochInsertRawProg (((L.io.toCtx, L.metaBase), u_val), v_val)) := by
    unfold smallEpochInsertRawProg
    refine modOnly_bind (modOnly_ro (clientState_smallEpochScanRawProg _)) fun r => ?_
    refine modOnly_ite
      (fun _ => modOnly_mono (modOnly_slotIoWriteRaw hg r.2.1 (u_val, v_val)) (fun _ => Or.inr))
      fun _ => ?_
    refine modOnly_bind (modOnly_read _) fun nSide => ?_
    dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    refine modOnly_ite (fun _ => ?_) (fun _ => modOnly_pure ())
    refine modOnly_bind
      (modOnly_mono (modOnly_slotIoAppendRaw hg nSide (u_val, v_val)) (fun _ => Or.inr))
      fun _ => modOnly_write (Or.inl rfl) _
  exact (hmod s).2 L.io.pgL.metaBase (fun h => by
    rcases h with heq | ⟨_, hne⟩
    · exact hne_hdr heq
    · exact hne rfl)

/-- `epochDeleteProg` preserves the split cursor `L.io.pgL.metaBase` in unpaged `SplitPair` mode
(`L.io.usePaged = 0 ∧ L.io.sideBit ≠ 0`). -/
theorem epochDeleteProg_preserves_split_cursor_small {L : SmallEpochLayout} {w pBase : ℕ}
    {s : Memory.State} (hv : L.Valid w s.frontier) (hpt : L.ParamTable pBase s.mem)
    (hup : L.io.usePaged = 0) (hsb : L.io.sideBit ≠ 0) (u_val : ℕ) :
    ((Memory.spec 0).clientState s (epochDeleteProg (pBase, u_val))).mem
      L.io.pgL.metaBase = s.mem L.io.pgL.metaBase := by
  have hg := split_io_geom hv.io_valid hup hsb
  have hne_hdr : L.io.pgL.metaBase ≠ L.metaBase + 1 :=
    fun heq => hv.disjoint_hdr _ (Or.inr heq) hg.own_mb
  have hstep : (Memory.spec 0).clientState s (epochDeleteProg (pBase, u_val)) =
      (Memory.spec 0).clientState s
        (smallEpochDeleteRawProg ((L.io.toCtx, L.metaBase), u_val)) := by
    unfold epochDeleteProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hpt.1, ite_eq_left rfl, StateTransitionSpec.clientState_bind, clientState_read_eq,
      prog_clientResult_read, hpt.2.1, StateTransitionSpec.clientState_bind,
      clientState_loadSmallIoCtxProg, clientResult_loadSmallIoCtxProg hpt]
  rw [hstep]
  let ModS : ℕ → Prop := fun a => a = L.metaBase + 1 ∨ IoSplitMod L.io a
  have hmod : ModOnly ModS (smallEpochDeleteRawProg ((L.io.toCtx, L.metaBase), u_val)) := by
    unfold smallEpochDeleteRawProg
    refine modOnly_bind (modOnly_ro (clientState_smallEpochScanRawProg _)) fun r => ?_
    refine modOnly_ite (fun _ => ?_) (fun _ => modOnly_pure ())
    refine modOnly_bind (modOnly_read _) fun nSide => ?_
    refine modOnly_ite (fun _ => ?_) (fun _ => modOnly_pure ())
    simp only [pure_bind]
    refine modOnly_bind
      (modOnly_mono (modOnly_slotIoSwapRaw hg r.2.1 (nSide - 1)) (fun _ => Or.inr)) fun _ => ?_
    refine modOnly_bind (modOnly_mono (modOnly_slotIoPopBackRaw hup) (fun _ => Or.inr)) fun _ => ?_
    exact modOnly_write (Or.inl rfl) _
  exact (hmod s).2 L.io.pgL.metaBase (fun h => by
    rcases h with heq | ⟨_, hne⟩
    · exact hne_hdr heq
    · exact hne rfl)

/-- `epochInsertProg` preserves `SplitHiQuotBounded` in the small regime (`N = 0`). -/
theorem epochInsertProg_preserves_hiQuot_small {L : SmallEpochLayout} {w pBase : ℕ}
    {s : Memory.State} (hv : L.Valid w s.frontier) (hpt : L.ParamTable pBase s.mem)
    (hup : L.io.usePaged = 0) (hsb : L.io.sideBit ≠ 0)
    (hns : s.mem (L.metaBase + 1) ≤ L.io.pgL.nCap)
    (hhi : SplitHiQuotBounded L.io (s.mem (L.metaBase + 1)) s.mem)
    (u : Fin L.U) (v_val : ℕ) :
    let s' := (Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v_val))
    SplitHiQuotBounded L.io (s'.mem (L.metaBase + 1)) s'.mem := by
  dsimp only
  have hg := split_io_geom hv.io_valid hup hsb
  have hqu : u.val < 2 ^ L.io.pgL.qBits := by
    rw [hv.qBits_eq]
    exact u.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two L.U)
  have hstep : (Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v_val)) =
      (Memory.spec 0).clientState s
        (smallEpochInsertRawProg (((L.io.toCtx, L.metaBase), u.val), v_val)) := by
    unfold epochInsertProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hpt.1, ite_eq_left rfl, StateTransitionSpec.clientState_bind, clientState_read_eq,
      prog_clientResult_read, hpt.2.1, StateTransitionSpec.clientState_bind,
      clientState_loadSmallIoCtxProg, clientResult_loadSmallIoCtxProg hpt]
  rw [hstep]
  unfold smallEpochInsertRawProg
  rw [StateTransitionSpec.clientState_bind, clientState_smallEpochScanRawProg]
  set r := (Memory.spec 0).clientResult s
    (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val))
  by_cases hr1 : r.1 = 1
  · rw [ite_eq_left hr1]
    have hp := hiQuotPres_slotIoWriteRaw hg (idx := r.2.1) (qv := (u.val, v_val)) hqu s
    have hns_eq : ((Memory.spec 0).clientState s
        (slotIoWriteRawProg ((L.io.toCtx, r.2.1), (u.val, v_val)))).mem (L.metaBase + 1) =
        s.mem (L.metaBase + 1) :=
      (slotIoWriteProg_frame (io := L.io) hg.w_pos r.2.1 u.val v_val).mem_outside s
        (L.metaBase + 1) (hv.disjoint_hdr _ (Or.inr rfl))
    rw [hns_eq]
    exact hiQuotPres_preserves_bounded hp hhi le_rfl hns
  · rw [ite_eq_right hr1, StateTransitionSpec.clientState_bind, clientState_read_eq,
      prog_clientResult_read]
    dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    set ns := s.mem (L.metaBase + 1)
    by_cases hlt : ns < L.io.pgL.nCap
    · rw [ite_eq_left hlt, StateTransitionSpec.clientState_bind]
      change SplitHiQuotBounded L.io
        (((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s (slotIoAppendRawProg ((L.io.toCtx, ns), (u.val, v_val))))
          (Memory.write (L.metaBase + 1) (ns + 1))).mem (L.metaBase + 1))
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s (slotIoAppendRawProg ((L.io.toCtx, ns), (u.val, v_val))))
          (Memory.write (L.metaBase + 1) (ns + 1))).mem
      set s₁ := (Memory.spec 0).clientState s
        (slotIoAppendRawProg ((L.io.toCtx, ns), (u.val, v_val)))
      have hp₁ : HiQuotPres L.io s.mem s₁.mem :=
        hiQuotPres_slotIoAppendRaw hg (nSide := ns) (qv := (u.val, v_val)) hqu s
      have hp₂ : HiQuotPres L.io s₁.mem
          ((Memory.spec 0).clientState s₁ (Memory.write (L.metaBase + 1) (ns + 1))).mem :=
        hiQuotPres_of_io_unchanged hg fun addr ha => by
          change Function.update s₁.mem (L.metaBase + 1) (ns + 1) addr = s₁.mem addr
          exact Function.update_of_ne
            (fun heq : addr = L.metaBase + 1 => hv.disjoint_hdr addr (Or.inr heq) ha)
            (ns + 1) s₁.mem
      have hp := hiQuotPres_trans hp₁ hp₂
      have hns' : ((Memory.spec 0).clientState s₁
          (Memory.write (L.metaBase + 1) (ns + 1))).mem (L.metaBase + 1) = ns + 1 := by
        change Function.update s₁.mem (L.metaBase + 1) (ns + 1) (L.metaBase + 1) = ns + 1
        exact Function.update_self (L.metaBase + 1) (ns + 1) s₁.mem
      rw [hns']
      intro idx hsp hidx
      have hsp₀ : s.mem L.io.pgL.metaBase ≤ idx := by rw [← hp.1]; exact hsp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with hlt_ns | rfl
      · exact hiQuotPres_preserves_bounded hp hhi le_rfl hns idx hsp hlt_ns
      · have hself := slotIoAppendRaw_hi_self hg (qv := (u.val, v_val)) hlt hsp₀ hqu
        rcases hp₂.2 ns (by rw [hp₁.1]; exact hsp₀) hlt with heq | hlt₂
        · exact heq ▸ hself
        · exact hlt₂
    · rw [ite_eq_right hlt]
      exact hhi

/-- `epochDeleteProg` preserves `SplitHiQuotBounded` in the small regime (`N = 0`). -/
theorem epochDeleteProg_preserves_hiQuot_small {L : SmallEpochLayout} {w pBase : ℕ}
    {s : Memory.State} (hv : L.Valid w s.frontier) (hpt : L.ParamTable pBase s.mem)
    (hup : L.io.usePaged = 0) (hsb : L.io.sideBit ≠ 0)
    (hns : s.mem (L.metaBase + 1) ≤ L.io.pgL.nCap)
    (hhi : SplitHiQuotBounded L.io (s.mem (L.metaBase + 1)) s.mem) (u_val : ℕ) :
    let s' := (Memory.spec 0).clientState s (epochDeleteProg (pBase, u_val))
    SplitHiQuotBounded L.io (s'.mem (L.metaBase + 1)) s'.mem := by
  dsimp only
  have hg := split_io_geom hv.io_valid hup hsb
  have hstep : (Memory.spec 0).clientState s (epochDeleteProg (pBase, u_val)) =
      (Memory.spec 0).clientState s
        (smallEpochDeleteRawProg ((L.io.toCtx, L.metaBase), u_val)) := by
    unfold epochDeleteProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hpt.1, ite_eq_left rfl, StateTransitionSpec.clientState_bind, clientState_read_eq,
      prog_clientResult_read, hpt.2.1, StateTransitionSpec.clientState_bind,
      clientState_loadSmallIoCtxProg, clientResult_loadSmallIoCtxProg hpt]
  rw [hstep]
  unfold smallEpochDeleteRawProg
  rw [StateTransitionSpec.clientState_bind, clientState_smallEpochScanRawProg]
  set r := (Memory.spec 0).clientResult s
    (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u_val))
  by_cases hr1 : r.1 = 1
  · rw [ite_eq_left hr1, StateTransitionSpec.clientState_bind, clientState_read_eq,
      prog_clientResult_read]
    set ns := s.mem (L.metaBase + 1)
    by_cases hpos : 0 < ns
    · rw [ite_eq_left hpos]; simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
      have hpop_eq : ∀ st,
          (Memory.spec 0).clientState st (slotIoPopBackRawProg L.io.toCtx) = st := fun st => by
        unfold slotIoPopBackRawProg; dsimp only [SlotIoLayout.toCtx]
        rw [ite_eq_left hup]; rfl
      rw [hpop_eq]
      set s₁ := (Memory.spec 0).clientState s (slotIoSwapRawProg (L.io.toCtx, (r.2.1, ns - 1)))
      have hp₁ : HiQuotPres L.io s.mem s₁.mem := hiQuotPres_slotIoSwapRaw hg r.2.1 (ns - 1) s
      have hp₂ : HiQuotPres L.io s₁.mem
          ((Memory.spec 0).clientState s₁ (Memory.write (L.metaBase + 1) (ns - 1))).mem :=
        hiQuotPres_of_io_unchanged hg fun addr ha => by
          change Function.update s₁.mem (L.metaBase + 1) (ns - 1) addr = s₁.mem addr
          exact Function.update_of_ne
            (fun heq : addr = L.metaBase + 1 => hv.disjoint_hdr addr (Or.inr heq) ha)
            (ns - 1) s₁.mem
      have hns' : ((Memory.spec 0).clientState s₁
          (Memory.write (L.metaBase + 1) (ns - 1))).mem (L.metaBase + 1) = ns - 1 := by
        change Function.update s₁.mem (L.metaBase + 1) (ns - 1) (L.metaBase + 1) = ns - 1
        exact Function.update_self (L.metaBase + 1) (ns - 1) s₁.mem
      rw [hns']
      exact hiQuotPres_preserves_bounded (hiQuotPres_trans hp₁ hp₂) hhi (Nat.sub_le ns 1)
        ((Nat.sub_le ns 1).trans hns)
    · rw [ite_eq_right hpos]; exact hhi
  · rw [ite_eq_right hr1]; exact hhi

/-! ## Section 4: `BlockPool` and `FallbackPool` Split-Safe `PoolSafe` Proofs -/

private def PoolSplitMod (mp : BpMetaLayout) (io : SlotIoLayout) (addr : ℕ) : Prop :=
  addr = mp.metaBase + 2 ∨ mp.OwnsMetaAddr addr ∨ IoSplitMod io addr

private def PoolSafe {α : Type} (keepN : Bool) (mp : BpMetaLayout) (io : SlotIoLayout)
    (p : Memory.Prog α) : Prop :=
  ModOnly (PoolSplitMod mp io) p ∧
  (∀ s, HiQuotPres io s.mem ((Memory.spec 0).clientState s p).mem) ∧
  (keepN = true → ∀ s, ((Memory.spec 0).clientState s p).mem (mp.metaBase + 1) =
    s.mem (mp.metaBase + 1))

private theorem ps_pure {α : Type} {keepN : Bool} {mp : BpMetaLayout} {io : SlotIoLayout}
    (x : α) : PoolSafe keepN mp io (pure x : Memory.Prog α) :=
  ⟨modOnly_pure x, fun s => hiQuotPres_refl io s.mem, fun _ _ => rfl⟩

private theorem ps_ro {α : Type} {keepN : Bool} {mp : BpMetaLayout} {io : SlotIoLayout}
    {p : Memory.Prog α} (hst : ∀ s, (Memory.spec 0).clientState s p = s) :
    PoolSafe keepN mp io p :=
  ⟨modOnly_ro hst, fun s => by rw [hst s]; exact hiQuotPres_refl io s.mem,
    fun _ s => by rw [hst s]⟩

private theorem ps_bind {α β : Type} {keepN : Bool} {mp : BpMetaLayout} {io : SlotIoLayout}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : PoolSafe keepN mp io p) (hq : ∀ x, PoolSafe keepN mp io (q x)) :
    PoolSafe keepN mp io (p >>= q) :=
  ⟨modOnly_bind hp.1 (fun x => (hq x).1),
    fun s => by
      rw [StateTransitionSpec.clientState_bind]
      exact hiQuotPres_trans (hp.2.1 s) ((hq _).2.1 _),
    fun hk s => by
      rw [StateTransitionSpec.clientState_bind]
      exact ((hq _).2.2 hk _).trans (hp.2.2 hk s)⟩

private theorem ps_ite {α : Type} {keepN : Bool} {mp : BpMetaLayout} {io : SlotIoLayout}
    {P : Prop} [Decidable P] {p₁ p₂ : Memory.Prog α}
    (h₁ : P → PoolSafe keepN mp io p₁) (h₂ : ¬P → PoolSafe keepN mp io p₂) :
    PoolSafe keepN mp io (if P then p₁ else p₂) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact h₁ hP
  · rw [ite_eq_right hP]; exact h₂ hP

private theorem ps_iterate {δ σ : Type} {keepN : Bool} {mp : BpMetaLayout} {io : SlotIoLayout}
    {body : δ × σ → Memory.Prog σ} (d : δ) (fuel : ℕ) (a : σ)
    (hb : ∀ a', PoolSafe keepN mp io (body (d, a'))) :
    PoolSafe keepN mp io (iterate body d fuel a) := by
  induction fuel generalizing a with
  | zero => exact ps_pure a
  | succ k ih =>
    unfold iterate
    exact ps_bind (hb a) fun a' => ih a'

private theorem ps_bp_meta_any {α : Type} {mp : BpMetaLayout} {io : SlotIoLayout} {C : ℕ}
    {p : Memory.Prog α} (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hm : BpMetaProg mp C p) :
    PoolSafe false mp io p :=
  ⟨modOnly_of_frame hm.frame (fun _ ha => Or.inr (Or.inl ha)),
    fun s => hiQuotPres_of_io_unchanged hg
      (fun a ha => hm.frame.mem_outside s a (fun hma => hdisj a hma ha)),
    fun hk => Bool.noConfusion hk⟩

private theorem ps_bp_meta_noN {α : Type} {keepN : Bool} {mp : BpMetaLayout} {io : SlotIoLayout}
    {C : ℕ} {p : Memory.Prog α} (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hm : BpMetaProg mp C p)
    (hnoN : ∀ s, ((Memory.spec 0).clientState s p).mem (mp.metaBase + 1) =
      s.mem (mp.metaBase + 1)) :
    PoolSafe keepN mp io p :=
  ⟨modOnly_of_frame hm.frame (fun _ ha => Or.inr (Or.inl ha)),
    fun s => hiQuotPres_of_io_unchanged hg
      (fun a ha => hm.frame.mem_outside s a (fun hma => hdisj a hma ha)),
    fun _ => hnoN⟩

private theorem ps_bp_io {α : Type} {keepN : Bool} {mp : BpMetaLayout} {io : SlotIoLayout}
    {p : Memory.Prog α} (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hm : ModOnly (IoSplitMod io) p)
    (hp : ∀ s, HiQuotPres io s.mem ((Memory.spec 0).clientState s p).mem) :
    PoolSafe keepN mp io p :=
  ⟨modOnly_mono hm (fun _ ha => Or.inr (Or.inr ha)), hp,
    fun _ s => (hm s).2 (mp.metaBase + 1) (fun h => hdisj _ (Or.inl rfl) h.1)⟩

section PoolSplitSection

variable {mp : BpMetaLayout} {io : SlotIoLayout} {w fr₀ : ℕ}

private theorem bpMeta_otd_ge (hmv : mp.Valid w fr₀) :
    mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailDir := by
  have h1 := hmv.offSlabDir_ge
  have h2 := hmv.offTailDir_ge
  omega

private theorem bpMeta_oso_ge (hmv : mp.Valid w fr₀) :
    mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offSlabOwner := by
  have h1 := bpMeta_otd_ge hmv
  have h2 := hmv.offSlabOwner_ge
  omega

private theorem ps_writeTailDirRaw {keepN : Bool} (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) (idx val : ℕ) :
    PoolSafe keepN mp io (bpWriteTailDirRawProg ((mp.toCtx, idx), val)) := by
  have hotd := bpMeta_otd_ge hmv
  have ho32 := hmv.offBktMeta_ge
  refine ps_bp_meta_noN hg hdisj (bpWriteTailDirRawProg_frame hmv.w_pos hotd idx val) (fun s => ?_)
  unfold bpWriteTailDirRawProg
  dsimp only [BpMetaLayout.toCtx]
  split_ifs with hlt
  · rw [clientState_writePackedCompGenProg]
    exact writePacked_outside hmv.w_pos s.mem hlt.1 val (by omega)
  · rfl

private theorem ps_writeSlabOwner {keepN : Bool} (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) (P lane val : ℕ) :
    PoolSafe keepN mp io (bpWriteSlabOwnerProg ((mp.toCtx, (P, lane)), val)) := by
  have hoso := bpMeta_oso_ge hmv
  have ho32 := hmv.offBktMeta_ge
  refine ps_bp_meta_noN hg hdisj (bpWriteSlabOwnerProg_frame hmv.w_pos hoso P lane val)
    (fun s => ?_)
  unfold bpWriteSlabOwnerProg
  dsimp only [BpMetaLayout.toCtx]
  split_ifs with hcond
  · simp only [pure_bind]
    rw [clientState_writePackedCompGenProg]
    exact writePacked_outside (N := 4 * mp.maxBlocks) hmv.w_pos s.mem (by omega) val (by omega)
  · rfl

private theorem ps_writeScalar_ne_one {keepN : Bool} (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    {k : ℕ} (hne : k ≠ 1) (val : ℕ) :
    PoolSafe keepN mp io (bpWriteScalarProg ((mp.toCtx, k), val)) := by
  refine ps_bp_meta_noN hg hdisj (bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge k val)
    (fun s => ?_)
  unfold bpWriteScalarProg
  dsimp only [BpMetaLayout.toCtx]
  split_ifs
  · change Function.update s.mem (mp.metaBase + k) val (mp.metaBase + 1) = s.mem (mp.metaBase + 1)
    exact Function.update_of_ne (by omega : mp.metaBase + 1 ≠ mp.metaBase + k) val s.mem
  · rfl

private theorem ps_bpExecOptSwap {keepN : Bool} (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) (osw : ℕ × (ℕ × ℕ)) :
    PoolSafe keepN mp io (bpExecOptSwapProg (io.toCtx, osw)) := by
  rcases osw with ⟨hasSw, ⟨p₁, p₂⟩⟩
  unfold bpExecOptSwapProg
  exact ps_ite (fun _ => ps_pure ())
    (fun _ => ps_bp_io hdisj (modOnly_slotIoSwapRaw hg p₁ p₂) (hiQuotPres_slotIoSwapRaw hg p₁ p₂))

private theorem ps_bpRunBktTicks16 (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) (b : ℕ) :
    PoolSafe false mp io (bpRunBktTicks16Prog ((mp.toCtx, io.toCtx), b)) := by
  have h1 : PoolSafe false mp io (bpBktTickStepProg ((mp.toCtx, io.toCtx), b)) := by
    unfold bpBktTickStepProg
    exact ps_bind (ps_bp_meta_any hg hdisj (bpBktTickMetaProg_frame hmv b))
      fun osw => ps_bpExecOptSwap hg hdisj osw
  have h2 : PoolSafe false mp io (bpRunBktTicks2Prog ((mp.toCtx, io.toCtx), b)) :=
    ps_bind h1 fun _ => h1
  have h4 : PoolSafe false mp io (bpRunBktTicks4Prog ((mp.toCtx, io.toCtx), b)) :=
    ps_bind h2 fun _ => h2
  have h8 : PoolSafe false mp io (bpRunBktTicks8Prog ((mp.toCtx, io.toCtx), b)) :=
    ps_bind h4 fun _ => h4
  exact ps_bind h8 fun _ => h8

private theorem ps_bpRunTopClean16 (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) :
    PoolSafe false mp io (bpRunTopClean16Prog (mp.toCtx, io.toCtx)) := by
  have h1 : PoolSafe false mp io (bpTopCleanStepProg (mp.toCtx, io.toCtx)) := by
    unfold bpTopCleanStepProg
    exact ps_bind (ps_bp_meta_any hg hdisj (bpTopCleanMetaProg_frame hmv))
      fun osw => ps_bpExecOptSwap hg hdisj osw
  have h2 : PoolSafe false mp io (bpRunTopClean2Prog (mp.toCtx, io.toCtx)) :=
    ps_bind h1 fun _ => h1
  have h4 : PoolSafe false mp io (bpRunTopClean4Prog (mp.toCtx, io.toCtx)) :=
    ps_bind h2 fun _ => h2
  have h8 : PoolSafe false mp io (bpRunTopClean8Prog (mp.toCtx, io.toCtx)) :=
    ps_bind h4 fun _ => h4
  exact ps_bind h8 fun _ => h8

private theorem ps_bpWriteAtRaw {keepN : Bool} (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (b loc : ℕ) {qv : ℕ × ℕ} (hq : qv.1 < 2 ^ io.pgL.qBits) :
    PoolSafe keepN mp io (bpWriteAtRawProg (((mp.toCtx, io.toCtx), (b, loc)), qv)) := by
  unfold bpWriteAtRawProg
  exact ps_bind (ps_ro (clientState_bpToPhysProg _)) fun phys =>
    ps_bp_io hdisj (modOnly_slotIoWriteRaw hg phys qv) (hiQuotPres_slotIoWriteRaw hg hq)

private theorem ps_bpAppendRaw (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (b : ℕ) {qv : ℕ × ℕ} (hq : qv.1 < 2 ^ io.pgL.qBits) :
    PoolSafe false mp io (bpAppendRawProg (((mp.toCtx, io.toCtx), b), qv)) ∧
    ∀ s, s.mem io.pgL.metaBase ≤ s.mem (mp.metaBase + 1) →
      s.mem (mp.metaBase + 1) < io.pgL.nCap →
      pairQuotAt io.pgL.itemBase io.pgL.offTail io.pgL.vBits io.pgL.w
        ((Memory.spec 0).clientState s (bpAppendRawProg (((mp.toCtx, io.toCtx), b), qv))).mem
        (s.mem (mp.metaBase + 1)) < 2 ^ io.pgL.qBits := by
  refine ⟨?_, fun s hsp hlt => ?_⟩
  · unfold bpAppendRawProg
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun ns => ?_
    refine ps_bind
      (ps_bp_io hdisj (modOnly_slotIoAppendRaw hg ns qv) (hiQuotPres_slotIoAppendRaw hg hq))
      fun _ => ?_
    refine ps_bind (ps_bp_meta_any hg hdisj (bpRawPostAppendMetaProg_frame hmv b)) fun _ => ?_
    exact ps_bpRunBktTicks16 hmv hg hdisj b
  · unfold bpAppendRawProg
    have hns_res : (Memory.spec 0).clientResult s (bpReadScalarProg (mp.toCtx, 1)) =
        s.mem (mp.metaBase + 1) := by
      unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]
      rw [ite_eq_left (Or.inl rfl)]; rfl
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg, hns_res,
      StateTransitionSpec.clientState_bind]
    set ns := s.mem (mp.metaBase + 1)
    set s₁ := (Memory.spec 0).clientState s (slotIoAppendRawProg ((io.toCtx, ns), qv))
    have hself := slotIoAppendRaw_hi_self hg hlt hsp hq
    have hp₁ := hiQuotPres_slotIoAppendRaw hg (nSide := ns) hq s
    have hpost : PoolSafe false mp io
        (bpRawPostAppendMetaProg (mp.toCtx, b) >>= fun _ =>
          bpRunBktTicks16Prog ((mp.toCtx, io.toCtx), b)) :=
      ps_bind (ps_bp_meta_any hg hdisj (bpRawPostAppendMetaProg_frame hmv b)) fun _ =>
        ps_bpRunBktTicks16 hmv hg hdisj b
    rcases (hpost.2.1 s₁).2 ns (hp₁.1.symm ▸ hsp) hlt with heq | hlt₂
    · exact heq ▸ hself
    · exact hlt₂

private theorem ps_bpPopBktBackRaw (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) (b : ℕ) :
    PoolSafe false mp io (bpPopBktBackRawProg ((mp.toCtx, io.toCtx), b)) := by
  have hprep : PoolSafe false mp io (bpPopBktPrepAndShrinkProg ((mp.toCtx, io.toCtx), b)) := by
    unfold bpPopBktPrepAndShrinkProg
    refine ps_bind (ps_bp_meta_any hg hdisj (bpPrepPopMetaProg_frame hmv b)) fun osw => ?_
    refine ps_bind (ps_bpExecOptSwap hg hdisj osw) fun _ => ?_
    refine ps_bind
      (ps_bp_io hdisj (modOnly_slotIoPopBackRaw hg.up_zero)
        (fun s => by
          unfold slotIoPopBackRawProg; dsimp only [SlotIoLayout.toCtx]
          rw [ite_eq_left hg.up_zero]; exact hiQuotPres_refl io s.mem))
      fun _ => ?_
    exact ps_bp_meta_any hg hdisj (bpCommitPopMetaProg_frame hmv b)
  unfold bpPopBktBackRawProg
  refine ps_bind hprep fun _ => ?_
  refine ps_bind (ps_bpRunBktTicks16 hmv hg hdisj b) fun _ => ?_
  exact ps_bpRunTopClean16 hmv hg hdisj

private theorem ps_fbScan {keepN : Bool} (bkt q_u : ℕ) :
    PoolSafe keepN mp io (fbScanProg ((mp.toCtx, io.toCtx), (bkt, q_u))) := by
  have hstep : ∀ nSide (acc : (ℕ × ℕ) × (ℕ × ℕ)),
      PoolSafe keepN mp io
        (fbScanStepProg (((mp.toCtx, io.toCtx), (nSide, (bkt, q_u))), acc)) := by
    intro nSide ⟨⟨cur, found⟩, ⟨hitP, hitVal⟩⟩
    unfold fbScanStepProg
    refine ps_ite (fun _ => ?_)
      (fun _ => ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ps_pure _)
    refine ps_bind (ps_ro (fun s => state_fbOwnerOfProg (mp.toCtx, cur) s)) fun _ => ?_
    refine ps_bind (ps_ro (clientState_slotIoReadRawProg _)) fun _ => ?_
    exact ps_ite (fun _ => ps_pure _) (fun _ => ps_pure _)
  unfold fbScanProg
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun nSide => ?_
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
  simp only [pure_bind]
  unfold fbScanLoopProg
  exact ps_bind (ps_iterate _ _ _ (hstep nSide)) fun _ => ps_pure _

private theorem ps_fbSwapRange {keepN : Bool} (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) (b₁ b₂ len : ℕ) :
    PoolSafe keepN mp io (fbSwapRangeProg (((mp.toCtx, io.toCtx), (b₁, b₂)), len)) := by
  have hstep : ∀ cur, PoolSafe keepN mp io
      (fbSwapRangeStepProg (((mp.toCtx, io.toCtx), (b₁, b₂)), cur)) := fun cur => by
    unfold fbSwapRangeStepProg
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    simp only [pure_bind]
    exact ps_bind
      (ps_bp_io hdisj (modOnly_slotIoSwapRaw hg _ _) (hiQuotPres_slotIoSwapRaw hg _ _))
      fun _ => ps_pure _
  unfold fbSwapRangeProg fbSwapRangeLoopProg
  simp only [pure_bind]
  exact ps_bind (ps_iterate _ _ _ hstep) fun _ => ps_pure _

private theorem ps_fbFindHeavyBktLoop {keepN : Bool} (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (tailLen fuel : ℕ) (acc : ℕ × ℕ) :
    PoolSafe keepN mp io (fbFindHeavyBktLoopProg (((mp.toCtx, tailLen), acc), fuel)) := by
  have hcStep : ∀ b (ca : ℕ × ℕ), PoolSafe keepN mp io
      (fbCountBktStepProg ((mp.toCtx, (tailLen, b)), ca)) := fun b ⟨t, cnt⟩ => by
    unfold fbCountBktStepProg
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_bind
      (ps_bp_meta_noN hg hdisj (bpReadTailDirRawProg_frame mp _)
        (fun s => by rw [clientState_bpReadTailDirRawProg]))
      fun _ => ?_
    exact ps_ite (fun _ => ps_pure _) (fun _ => ps_pure _)
  have hfStep : ∀ a : ℕ × ℕ, PoolSafe keepN mp io
      (fbFindHeavyBktStepProg ((mp.toCtx, tailLen), a)) := fun ⟨b, bStar⟩ => by
    unfold fbFindHeavyBktStepProg fbCountBktLoopProg
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    simp only [pure_bind]
    refine ps_bind (ps_iterate _ _ _ (hcStep b)) fun _ => ?_
    exact ps_ite (fun _ => ps_pure _) (fun _ => ps_pure _)
  unfold fbFindHeavyBktLoopProg
  exact ps_iterate _ _ _ hfStep

private theorem ps_fbFindMatchLoop {keepN : Bool} (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (tailLen bStar fuel : ℕ) (acc : ℕ × (ℕ × ℕ)) :
    PoolSafe keepN mp io (fbFindMatchLoopProg (((mp.toCtx, (tailLen, bStar)), acc), fuel)) := by
  have hmStep : ∀ a : ℕ × (ℕ × ℕ), PoolSafe keepN mp io
      (fbFindMatchStepProg ((mp.toCtx, (tailLen, bStar)), a)) := fun ⟨t, ⟨found, src⟩⟩ => by
    unfold fbFindMatchStepProg
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_bind
      (ps_bp_meta_noN hg hdisj (bpReadTailDirRawProg_frame mp _)
        (fun s => by rw [clientState_bpReadTailDirRawProg]))
      fun _ => ?_
    exact ps_ite (fun _ => ps_pure _) (fun _ => ps_pure _)
  unfold fbFindMatchLoopProg
  exact ps_iterate _ _ _ hmStep

private theorem ps_fbSwapTailSlots {keepN : Bool} (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) (fbBase t₁ t₂ : ℕ) :
    PoolSafe keepN mp io (fbSwapTailSlotsProg (((mp.toCtx, io.toCtx), fbBase), (t₁, t₂))) := by
  unfold fbSwapTailSlotsProg fbReadTailPairProg fbWriteTailPairProg
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_bind
    (ps_bind (ps_ro (clientState_bpReadTailDirRawProg _)) fun _ =>
      ps_bind (ps_ro (clientState_bpReadTailDirRawProg _)) fun _ => ps_pure _)
    fun _ => ?_
  refine ps_bind
    (ps_bp_io hdisj (modOnly_slotIoSwapRaw hg _ _) (hiQuotPres_slotIoSwapRaw hg _ _)) fun _ => ?_
  exact ps_bind (ps_writeTailDirRaw hmv hg hdisj _ _) fun _ => ps_writeTailDirRaw hmv hg hdisj _ _

private theorem ps_fbPromoteOneBlock {keepN : Bool} (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) :
    PoolSafe keepN mp io (fbPromoteOneBlockProg (mp.toCtx, io.toCtx)) := by
  have hpStep : ∀ fbBase tailLen bStar dst, PoolSafe keepN mp io
      (fbPartHeavyStepProg (((mp.toCtx, io.toCtx), (fbBase, (tailLen, bStar))), dst)) :=
    fun fbBase tailLen bStar dst => by
      unfold fbPartHeavyStepProg
      refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
      refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
      simp only [pure_bind]
      refine ps_bind (ps_fbFindMatchLoop hg hdisj tailLen bStar _ _) fun _ => ?_
      exact ps_bind (ps_fbSwapTailSlots hmv hg hdisj fbBase _ _) fun _ => ps_pure _
  have hslStep : ∀ k t, PoolSafe keepN mp io
      (fbShiftLeftStepProg ((mp.toCtx, k), t)) := fun k t => by
    unfold fbShiftLeftStepProg
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_bind (ps_ro (clientState_bpReadTailDirRawProg _)) fun _ => ?_
    exact ps_bind (ps_writeTailDirRaw hmv hg hdisj _ _) fun _ => ps_pure _
  unfold fbPromoteOneBlockProg fbPromoteCheckProg fbPromoteInnerCheckProg
    fbPromoteBodyProg fbPartHeavyLoopProg fbPromoteFinishProg fbShiftLeftLoopProg
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  simp only [pure_bind]
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_bind (ps_fbFindHeavyBktLoop hg hdisj _ _ _) fun _ => ?_
  refine ps_bind (ps_iterate _ _ _ (hpStep _ _ _)) fun _ => ?_
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_bind (ps_writeSlabOwner hmv hg hdisj _ _ _) fun _ => ?_
  refine ps_bind (ps_iterate _ _ _ (hslStep _)) fun _ => ?_
  exact ps_writeScalar_ne_one hmv hg hdisj (by decide) _

private theorem ps_fbMaybePromote {keepN : Bool} (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) :
    PoolSafe keepN mp io (fbMaybePromoteProg (mp.toCtx, io.toCtx)) := by
  unfold fbMaybePromoteProg fbMaybePromoteCheckProg fbMaybePromoteInnerProg
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  simp only [pure_bind]
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  exact ps_ite (fun _ => ps_fbPromoteOneBlock hmv hg hdisj) (fun _ => ps_pure ())

private theorem ps_fbDemoteBlk (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) (blk : ℕ) :
    PoolSafe false mp io (fbDemoteBlkProg ((mp.toCtx, io.toCtx), blk)) := by
  have hsrStep : ∀ k rem, PoolSafe false mp io
      (fbShiftRightStepProg ((mp.toCtx, k), rem)) := fun k rem => by
    unfold fbShiftRightStepProg
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    simp only [pure_bind]
    refine ps_bind (ps_ro (clientState_bpReadTailDirRawProg _)) fun _ => ?_
    exact ps_bind (ps_writeTailDirRaw hmv hg hdisj _ _) fun _ => ps_pure _
  have hfhStep : ∀ b_val i, PoolSafe false mp io
      (fbFillHeadStepProg ((mp.toCtx, b_val), i)) := fun b_val i => by
    unfold fbFillHeadStepProg
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    exact ps_bind (ps_writeTailDirRaw hmv hg hdisj _ _) fun _ => ps_pure _
  unfold fbDemoteBlkProg fbDemoteCheckProg fbDemoteInnerProg fbDemoteSwapProg
    fbDemoteSwapBodyProg fbReadBlkPairProg fbWriteBlkPairProg fbDemoteTailProg
    fbShiftRightLoopProg fbFillHeadLoopProg
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  simp only [pure_bind]
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_bind ?_ fun _ => ?_
  · refine ps_ite (fun _ => ps_ite (fun _ => ?_) (fun _ => ps_pure _))
      (fun _ => ps_pure _)
    refine ps_bind
      (ps_bind (ps_ro (clientState_bpReadSlabOwnerProg _)) fun _ =>
        ps_bind (ps_ro (clientState_bpReadSlabOwnerProg _)) fun _ => ps_pure _) fun _ => ?_
    refine ps_bind (ps_fbSwapRange hg hdisj _ _ _) fun _ => ?_
    refine ps_bind
      (ps_bind (ps_writeSlabOwner hmv hg hdisj _ _ _) fun _ =>
        ps_writeSlabOwner hmv hg hdisj _ _ _)
      fun _ => ps_pure _
  · refine ps_bind (ps_iterate _ _ _ (hsrStep _)) fun _ => ?_
    refine ps_bind (ps_iterate _ _ _ (hfhStep _)) fun _ => ?_
    exact ps_writeScalar_ne_one hmv hg hdisj (by decide) _

private theorem ps_fbPopTailAt (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) (p : ℕ) :
    PoolSafe false mp io (fbPopTailAtProg ((mp.toCtx, io.toCtx), p)) := by
  unfold fbPopTailAtProg fbPopTailCheckProg fbPopTailInnerProg fbPopBackAndDecProg
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  simp only [pure_bind]
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_bind (ps_fbSwapTailSlots hmv hg hdisj _ _ _) fun _ => ?_
  refine ps_bind
    (ps_bp_io hdisj (modOnly_slotIoPopBackRaw hg.up_zero)
      (fun s => by
        unfold slotIoPopBackRawProg; dsimp only [SlotIoLayout.toCtx]
        rw [ite_eq_left hg.up_zero]; exact hiQuotPres_refl io s.mem))
    fun _ => ?_
  exact ps_bp_meta_any hg hdisj (bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge _ _)

private theorem ps_fbDeleteSlot (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False) (hitP : ℕ) :
    PoolSafe false mp io (fbDeleteSlotProg ((mp.toCtx, io.toCtx), hitP)) := by
  unfold fbDeleteSlotProg fbDemoteAndPopProg fbDemotePopRunProg
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_bind (ps_ro (clientState_bpDivModKProg _)) fun _ => ?_
  refine ps_ite (fun _ => ?_) (fun _ => ps_fbPopTailAt hmv hg hdisj hitP)
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_bind (ps_fbMaybePromote hmv hg hdisj) fun _ => ?_
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  simp only [pure_bind]
  refine ps_bind (ps_fbDemoteBlk hmv hg hdisj _) fun _ => ?_
  exact ps_fbPopTailAt hmv hg hdisj _

private theorem ps_enterFallback {keepN : Bool} (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hdisj2 : ¬io.OwnsAddr (mp.metaBase + 2)) :
    PoolSafe keepN mp io (enterFallbackProg (mp.toCtx, io.toCtx)) := by
  have hundo : PoolSafe keepN mp io (fbUndoTopSwapProg (mp.toCtx, io.toCtx)) := by
    unfold fbUndoTopSwapProg fbUndoTopSwapReadProg fbUndoTopSwapCheckProg fbUndoTopSwapBodyProg
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
    refine ps_bind (ps_fbSwapRange hg hdisj _ _ _) fun _ => ?_
    exact ps_writeScalar_ne_one hmv hg hdisj (by decide) _
  have hlane : ∀ b₁ b₂ lane, PoolSafe keepN mp io
      (fbSwapSlabLaneProg ((mp.toCtx, (b₁, b₂)), lane)) := fun b₁ b₂ lane => by
    unfold fbSwapSlabLaneProg fbReadSlabLanePairProg fbWriteSlabLanePairProg
    refine ps_bind
      (ps_bind (ps_ro (clientState_bpReadSlabOwnerProg _)) fun _ =>
        ps_bind (ps_ro (clientState_bpReadSlabOwnerProg _)) fun _ => ps_pure _) fun _ => ?_
    exact ps_bind (ps_writeSlabOwner hmv hg hdisj _ _ _) fun _ =>
      ps_writeSlabOwner hmv hg hdisj _ _ _
  have hcpStep : ∀ bf (acc : ℕ × ℕ), PoolSafe keepN mp io
      (fbCompactPureStepProg (((mp.toCtx, io.toCtx), bf), acc)) := fun bf ⟨P, sPure⟩ => by
    unfold fbCompactPureStepProg fbCompactPureHitProg fbCompactSwapBlkProg
      fbCompactSwapBlkBodyProg fbCompactDoRangeProg fbSwapSlabMeta3Prog
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_bind (ps_ro (clientState_bpReadSlabOwnerProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    refine ps_bind ?_ fun _ => ps_pure _
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
    simp only [pure_bind]
    refine ps_bind (ps_fbSwapRange hg hdisj _ _ _) fun _ => ?_
    refine ps_bind (hlane _ _ _) fun _ => ?_
    refine ps_bind (hlane _ _ _) fun _ => hlane _ _ _
  have hsbRaw : ∀ p, PoolSafe keepN mp io (fbSlotBktRawProg (mp.toCtx, p)) := fun p => by
    have htoBlk : ∀ P off, PoolSafe keepN mp io
        (fbTailOwnerAtBlkProg (mp.toCtx, (P, off))) := fun P off => by
      unfold fbTailOwnerAtBlkProg
      refine ps_bind (ps_ro (clientState_bpReadSlabOwnerProg _)) fun _ => ?_
      refine ps_bind (ps_ro (clientState_bpTbSlotProg _)) fun _ => ?_
      exact ps_ro (clientState_bpReadTailOwnerProg _)
    unfold fbSlotBktRawProg fbSlotBktTag2Prog
    refine ps_bind (ps_ro (clientState_bpDivModKProg _)) fun _ => ?_
    refine ps_bind (ps_ro (clientState_bpReadSlabOwnerProg _)) fun _ => ?_
    refine ps_ite (fun _ => ps_ro (clientState_bpReadSlabOwnerProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => htoBlk _ _)
    refine ps_bind (ps_ro (clientState_bpReadSlabOwnerProg _)) fun _ => ?_
    refine ps_bind (ps_ro (clientState_bpActCurProg _)) fun _ => ?_
    exact ps_ite (fun _ => ps_pure _) (fun _ => htoBlk _ _)
  have hftoStep : ∀ baseP t, PoolSafe keepN mp io
      (fbFillTailOwnerStepProg ((mp.toCtx, baseP), t)) := fun baseP t => by
    unfold fbFillTailOwnerStepProg fbFillTailOwnerWriteProg
    refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure _)
    simp only [pure_bind]
    refine ps_bind (hsbRaw _) fun _ => ?_
    exact ps_bind (ps_writeTailDirRaw hmv hg hdisj _ _) fun _ => ps_pure _
  have hwMode1 : PoolSafe keepN mp io (fbWriteModeOneProg mp.toCtx) := by
    unfold fbWriteModeOneProg
    dsimp only [BpMetaLayout.toCtx]
    refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
    exact ⟨modOnly_write (Or.inl rfl) 1,
      fun s => hiQuotPres_of_io_unchanged hg
        (fun a ha => Function.update_of_ne (fun heq : a = mp.metaBase + 2 => hdisj2 (heq ▸ ha))
          1 s.mem),
      fun _ s => Function.update_of_ne (by omega : mp.metaBase + 1 ≠ mp.metaBase + 2) 1 s.mem⟩
  unfold enterFallbackProg fbEnterCompactAndFinishProg fbCompactAndFinishAtProg
    fbRunCompactPureProg fbCompactPureLoopProg fbEnterFinishProg fbEnterFinishBodyProg
    fbFillTailOwnerLoopProg
  refine ps_bind hundo fun _ => ?_
  refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
  refine ps_bind (ps_ro (clientState_bpDivModKProg _)) fun _ => ?_
  simp only [pure_bind]
  refine ps_bind (ps_bind (ps_iterate _ _ _ (hcpStep _)) fun _ => ps_pure _) fun _ => ?_
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
  refine ps_bind (ps_iterate _ _ _ (hftoStep _)) fun _ => ?_
  refine ps_bind (ps_writeScalar_ne_one hmv hg hdisj (by decide) _) fun _ => hwMode1

private theorem ps_fallbackInsert (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (fctx : FeistelHashCtx) (u_val v_val : ℕ)
    (hq_split : ∀ s,
      ((Memory.spec 0).clientResult s (feistelSplitBoundedProg (fctx, u_val))).2 <
        2 ^ io.pgL.qBits) :
    PoolSafe false mp io (fallbackInsertProg (((fctx, (mp.toCtx, io.toCtx)), u_val), v_val)) ∧
    ∀ s,
      s.mem (mp.metaBase + 1) <
        ((Memory.spec 0).clientState s
          (fallbackInsertProg (((fctx, (mp.toCtx, io.toCtx)), u_val), v_val))).mem
          (mp.metaBase + 1) →
      s.mem io.pgL.metaBase ≤ s.mem (mp.metaBase + 1) →
      s.mem (mp.metaBase + 1) < io.pgL.nCap →
      pairQuotAt io.pgL.itemBase io.pgL.offTail io.pgL.vBits io.pgL.w
        ((Memory.spec 0).clientState s
          (fallbackInsertProg (((fctx, (mp.toCtx, io.toCtx)), u_val), v_val))).mem
        (s.mem (mp.metaBase + 1)) < 2 ^ io.pgL.qBits := by
  have hsafe : PoolSafe false mp io
      (fallbackInsertProg (((fctx, (mp.toCtx, io.toCtx)), u_val), v_val)) := by
    unfold fallbackInsertProg fbInsertNewProg fbInsertNewCheckProg fbInsertNewCommitProg
    refine ⟨?_, ?_, fun hk => Bool.noConfusion hk⟩
    · refine modOnly_bind (modOnly_ro (clientState_feistelSplitBoundedProg _)) fun _ => ?_
      refine modOnly_bind (ps_fbScan (mp := mp) (io := io) (keepN := false) _ _).1 fun _ => ?_
      refine modOnly_ite
        (fun _ => modOnly_mono (modOnly_slotIoWriteRaw hg _ _) (fun _ => Or.inr ∘ Or.inr))
        fun _ => ?_
      refine modOnly_bind (ps_fbMaybePromote (keepN := false) hmv hg hdisj).1 fun _ => ?_
      refine modOnly_bind (modOnly_ro (clientState_bpReadScalarProg _)) fun _ => ?_
      refine modOnly_bind (modOnly_ro (clientState_bpReadScalarProg _)) fun _ => ?_
      refine modOnly_ite (fun _ => ?_) (fun _ => modOnly_pure ())
      refine modOnly_ite (fun _ => ?_) (fun _ => modOnly_pure ())
      refine modOnly_ite (fun _ => ?_) (fun _ => modOnly_pure ())
      simp only [pure_bind]
      refine modOnly_bind
        (modOnly_mono (modOnly_slotIoAppendRaw hg _ _) (fun _ => Or.inr ∘ Or.inr)) fun _ => ?_
      refine modOnly_bind (ps_writeTailDirRaw (keepN := false) hmv hg hdisj _ _).1 fun _ => ?_
      exact (ps_bp_meta_any hg hdisj (bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge _ _)).1
    · intro s
      rw [StateTransitionSpec.clientState_bind, clientState_feistelSplitBoundedProg]
      have hq := hq_split s
      set bq := (Memory.spec 0).clientResult s (feistelSplitBoundedProg (fctx, u_val))
      have htail : PoolSafe false mp io
          (fbScanProg ((mp.toCtx, io.toCtx), bq) >>= fun hit =>
            if hit.1 = 1 then
              slotIoWriteRawProg ((io.toCtx, hit.2.1), (bq.2, v_val))
            else
              fbInsertNewProg (((mp.toCtx, io.toCtx), bq), v_val)) := by
        unfold fbInsertNewProg fbInsertNewCheckProg fbInsertNewCommitProg
        refine ps_bind (ps_fbScan _ _) fun hit => ?_
        refine ps_ite
          (fun _ =>
            ps_bp_io hdisj (modOnly_slotIoWriteRaw hg _ _) (hiQuotPres_slotIoWriteRaw hg hq))
          fun _ => ?_
        refine ps_bind (ps_fbMaybePromote hmv hg hdisj) fun _ => ?_
        refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
        refine ps_bind (ps_ro (clientState_bpReadScalarProg _)) fun _ => ?_
        refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
        refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
        refine ps_ite (fun _ => ?_) (fun _ => ps_pure ())
        simp only [pure_bind]
        refine ps_bind
          (ps_bp_io hdisj (modOnly_slotIoAppendRaw hg _ _) (hiQuotPres_slotIoAppendRaw hg hq))
          fun _ => ?_
        refine ps_bind (ps_writeTailDirRaw hmv hg hdisj _ _) fun _ => ?_
        exact ps_bp_meta_any hg hdisj (bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge _ _)
      exact htail.2.1 s
  refine ⟨hsafe, fun s hgt hsp hlt => ?_⟩
  unfold fallbackInsertProg at hgt ⊢
  rw [StateTransitionSpec.clientState_bind, clientState_feistelSplitBoundedProg] at hgt ⊢
  have hq := hq_split s
  set bq := (Memory.spec 0).clientResult s (feistelSplitBoundedProg (fctx, u_val))
  have hsc_st : (Memory.spec 0).clientState s (fbScanProg ((mp.toCtx, io.toCtx), bq)) = s :=
    state_fbScanProg ((mp.toCtx, io.toCtx), bq) s
  rw [StateTransitionSpec.clientState_bind, hsc_st] at hgt ⊢
  set hit := (Memory.spec 0).clientResult s (fbScanProg ((mp.toCtx, io.toCtx), bq))
  by_cases hhit : hit.1 = 1
  · rw [ite_eq_left hhit] at hgt
    have heq := (ps_bp_io (keepN := true) hdisj (modOnly_slotIoWriteRaw hg hit.2.1 (bq.2, v_val))
      (hiQuotPres_slotIoWriteRaw hg hq)).2.2 rfl s
    exact absurd hgt (by rw [heq]; exact Nat.lt_irrefl _)
  · rw [ite_eq_right hhit] at hgt ⊢
    unfold fbInsertNewProg fbInsertNewCheckProg fbInsertNewCommitProg at hgt ⊢
    have hmp_safe := ps_fbMaybePromote (keepN := true) hmv hg hdisj
    rw [StateTransitionSpec.clientState_bind] at hgt ⊢
    set s₁ := (Memory.spec 0).clientState s (fbMaybePromoteProg (mp.toCtx, io.toCtx))
    have hns₁ : s₁.mem (mp.metaBase + 1) = s.mem (mp.metaBase + 1) := hmp_safe.2.2 rfl s
    have hmb₁ : s₁.mem io.pgL.metaBase = s.mem io.pgL.metaBase := (hmp_safe.2.1 s).1
    have hns_res : (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 1)) =
        s.mem (mp.metaBase + 1) := by
      unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]
      rw [ite_eq_left (Or.inl rfl)]; exact hns₁
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg, hns_res,
      StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg] at hgt ⊢
    set fb0 := (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 10))
    dsimp only [BpMetaLayout.toCtx] at hgt ⊢
    split_ifs at hgt ⊢ with c1 c2 c3
    · rcases bq with ⟨bkt, q_u⟩
      dsimp only [Prod.snd] at hq ⊢
      set ns := s.mem (mp.metaBase + 1)
      set t := ns - fb0 * mp.K
      change pairQuotAt io.pgL.itemBase io.pgL.offTail io.pgL.vBits io.pgL.w
        ((Memory.spec 0).clientState s₁
          (slotIoAppendRawProg ((io.toCtx, ns), (q_u, v_val)) >>= fun _ =>
            bpWriteTailDirRawProg ((mp.toCtx, t), bkt) >>= fun _ =>
              bpWriteScalarProg ((mp.toCtx, 1), ns + 1))).mem ns < 2 ^ io.pgL.qBits
      rw [StateTransitionSpec.clientState_bind]
      set s₂ := (Memory.spec 0).clientState s₁
        (slotIoAppendRawProg ((io.toCtx, ns), (q_u, v_val)))
      have hself :=
        slotIoAppendRaw_hi_self hg (qv := (q_u, v_val)) hlt (by rw [hmb₁]; exact hsp) hq
      have hp₂ := hiQuotPres_slotIoAppendRaw hg (nSide := ns) (qv := (q_u, v_val)) hq s₁
      have hpost : PoolSafe false mp io
          (bpWriteTailDirRawProg ((mp.toCtx, t), bkt) >>= fun _ =>
            bpWriteScalarProg ((mp.toCtx, 1), ns + 1)) :=
        ps_bind (ps_writeTailDirRaw hmv hg hdisj t bkt) fun _ =>
          ps_bp_meta_any hg hdisj (bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge 1 (ns + 1))
      have hp₃ := hpost.2.1 s₂
      rcases hp₃.2 ns (by rw [hp₂.1, hmb₁]; exact hsp) hlt with heq | hlt₃
      · exact heq ▸ hself
      · exact hlt₃
    all_goals (
      change s.mem (mp.metaBase + 1) < s₁.mem (mp.metaBase + 1) at hgt
      exact absurd hgt (by rw [hns₁]; exact Nat.lt_irrefl _))

private theorem ps_fallbackDelete (hmv : mp.Valid w fr₀) (hg : SplitIoGeom io)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (fctx : FeistelHashCtx) (u_val : ℕ) :
    PoolSafe false mp io (fallbackDeleteProg ((fctx, (mp.toCtx, io.toCtx)), u_val)) := by
  unfold fallbackDeleteProg
  refine ps_bind (ps_ro (clientState_feistelSplitBoundedProg _)) fun _ => ?_
  refine ps_bind (ps_fbScan _ _) fun _ => ?_
  exact ps_ite (fun _ => ps_fbDeleteSlot hmv hg hdisj _) (fun _ => ps_pure ())

end PoolSplitSection

/-! ## Section 5: Large-Epoch Split-Safe Composition (`FastSplitSafe`) -/

private def FastSplitMod (fl : FastEpochLayout) (addr : ℕ) : Prop :=
  fl.OwnsFastAddr addr ∧ addr ≠ fl.io.pgL.metaBase

private def FastSplitSafe {α : Type} (keepN : Bool) (w : ℕ) (fl : FastEpochLayout)
    (p : Memory.Prog α) : Prop :=
  fl.io.usePaged = 0 → fl.io.sideBit ≠ 0 →
  ∀ s, FastLayoutReady w fl s →
    let s' := (Memory.spec 0).clientState s p
    FastLayoutReady w fl s' ∧
    (∀ addr, ¬FastSplitMod fl addr → s'.mem addr = s.mem addr) ∧
    HiQuotPres fl.io s.mem s'.mem ∧
    (keepN = true → s'.mem (fl.metaBase + 1) = s.mem (fl.metaBase + 1))

private theorem fss_ro {α : Type} {keepN : Bool} {w : ℕ} {fl : FastEpochLayout}
    {p : Memory.Prog α} (hst : ∀ s, (Memory.spec 0).clientState s p = s) :
    FastSplitSafe keepN w fl p :=
  fun _ _ s hr => by
    rw [hst s]; exact ⟨hr, fun _ _ => rfl, hiQuotPres_refl fl.io s.mem, fun _ => rfl⟩

private theorem fss_pure {α : Type} {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} (x : α) :
    FastSplitSafe keepN w fl (pure x : Memory.Prog α) :=
  fun _ _ s hr => ⟨hr, fun _ _ => rfl, hiQuotPres_refl fl.io s.mem, fun _ => rfl⟩

private theorem fss_read {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} (a : ℕ) :
    FastSplitSafe keepN w fl (Memory.read a) :=
  fun _ _ s hr => ⟨hr, fun _ _ => rfl, hiQuotPres_refl fl.io s.mem, fun _ => rfl⟩

private theorem fss_bind {α β : Type} {keepN : Bool} {w : ℕ} {fl : FastEpochLayout}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : FastSplitSafe keepN w fl p) (hq : ∀ x, FastSplitSafe keepN w fl (q x)) :
    FastSplitSafe keepN w fl (p >>= q) :=
  fun hup hsb s hr => by
    rw [StateTransitionSpec.clientState_bind]
    obtain ⟨hr₁, hm₁, hq₁, hn₁⟩ := hp hup hsb s hr
    obtain ⟨hr₂, hm₂, hq₂, hn₂⟩ :=
      hq ((Memory.spec 0).clientResult s p) hup hsb ((Memory.spec 0).clientState s p) hr₁
    exact ⟨hr₂, fun addr hnot => (hm₂ addr hnot).trans (hm₁ addr hnot),
      hiQuotPres_trans hq₁ hq₂, fun hk => (hn₂ hk).trans (hn₁ hk)⟩

private theorem fss_bind_ro {α β : Type} {keepN : Bool} {w : ℕ} {fl : FastEpochLayout}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hst : ∀ s, (Memory.spec 0).clientState s p = s)
    (hq : ∀ s, FastLayoutReady w fl s →
      FastSplitSafe keepN w fl (q ((Memory.spec 0).clientResult s p))) :
    FastSplitSafe keepN w fl (p >>= q) :=
  fun hup hsb s hr => by
    rw [StateTransitionSpec.clientState_bind, hst s]
    exact hq s hr hup hsb s hr

private theorem fss_ite {α : Type} {keepN : Bool} {w : ℕ} {fl : FastEpochLayout}
    {P : Prop} [Decidable P] {p₁ p₂ : Memory.Prog α}
    (h₁ : P → FastSplitSafe keepN w fl p₁) (h₂ : ¬P → FastSplitSafe keepN w fl p₂) :
    FastSplitSafe keepN w fl (if P then p₁ else p₂) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact h₁ hP
  · rw [ite_eq_right hP]; exact h₂ hP

private theorem poolSplitMod_to_fastSplitMod {fl : FastEpochLayout} {w fr addr : ℕ}
    (hv : fl.Valid w fr) (hup : fl.io.usePaged = 0) (hsb : fl.io.sideBit ≠ 0)
    (hp : PoolSplitMod fl.mp fl.io addr) :
    FastSplitMod fl addr := by
  have hg := split_io_geom hv.io_valid hup hsb
  have hmp_mb : fl.mp.metaBase = fl.metaBase := rfl
  rcases hp with rfl | hma | ⟨hia, hne⟩
  · refine ⟨Or.inl ⟨by omega, by omega⟩, fun heq => ?_⟩
    exact hv.disj_fast_io _ (Or.inl ⟨by omega, by omega⟩) (heq ▸ hg.own_mb)
  · exact ⟨fl.owns_of_bpMeta hv hma, fun heq => hv.bp_valid.disjoint _ hma (heq ▸ hg.own_mb)⟩
  · exact ⟨Or.inr (Or.inr hia), hne⟩

private theorem fss_of_poolSafe {α : Type} {keepN : Bool} {w : ℕ} {fl : FastEpochLayout}
    {p : Memory.Prog α}
    (hps : ∀ fr, fl.mp.Valid w fr → SplitIoGeom fl.io →
      (∀ addr, fl.mp.OwnsMetaAddr addr → fl.io.OwnsAddr addr → False) →
      ¬fl.io.OwnsAddr (fl.mp.metaBase + 2) →
      PoolSafe keepN fl.mp fl.io p) :
    FastSplitSafe keepN w fl p :=
  fun hup hsb s hr => by
    have hg := split_io_geom hr.1.io_valid hup hsb
    have hdisj2 : ¬fl.io.OwnsAddr (fl.mp.metaBase + 2) :=
      hr.1.disj_fast_io _ (Or.inl ⟨by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega,
        by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega⟩)
    obtain ⟨hm, hqp, hkn⟩ := hps s.frontier hr.1.mp_valid hg hr.1.bp_valid.disjoint hdisj2
    obtain ⟨hfr, hout⟩ := hm s
    have hout_f : ∀ addr, ¬FastSplitMod fl addr →
        ((Memory.spec 0).clientState s p).mem addr = s.mem addr :=
      fun addr hnot => hout addr (fun hp => hnot (poolSplitMod_to_fastSplitMod hr.1 hup hsb hp))
    exact ⟨hr.of_frame hfr (fun a ha => hout_f a (fun h => ha h.1)), hout_f, hqp s,
      fun hk => hkn hk s⟩

private theorem fss_fastWriteMeta {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} (off val : ℕ) :
    FastSplitSafe keepN w fl (fastWriteMetaProg ((fl.pBase, off), val)) :=
  fun hup hsb s hr => by
    have hg := split_io_geom hr.1.io_valid hup hsb
    refine ⟨fastWriteMetaProg_ready hr, fun addr hnot => ?_, ?_, fun _ => ?_⟩
    · by_cases hoff : (2 ≤ off ∧ off < 10) ∨ off = 17
      · rw [clientState_fastWriteMetaProg hr.2.1 hoff]
        refine Function.update_of_ne (fun heq => ?_) val s.mem
        subst heq
        refine hnot ⟨Or.inl ⟨by omega, by omega⟩, fun hmb => ?_⟩
        exact hr.1.disj_fast_io _ (Or.inl ⟨by omega, by omega⟩) (hmb ▸ hg.own_mb)
      · have hst :
            (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, off), val)) = s := by
          unfold fastWriteMetaProg; dsimp only; rw [ite_eq_right hoff]; rfl
        rw [hst]
    · by_cases hoff : (2 ≤ off ∧ off < 10) ∨ off = 17
      · rw [clientState_fastWriteMetaProg hr.2.1 hoff]
        exact hiQuotPres_of_io_unchanged hg fun a ha =>
          Function.update_of_ne
            (fun heq => hr.1.disj_fast_io a (Or.inl ⟨by omega, by omega⟩) ha) val s.mem
      · have hst :
            (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, off), val)) = s := by
          unfold fastWriteMetaProg; dsimp only; rw [ite_eq_right hoff]; rfl
        rw [hst]; exact hiQuotPres_refl fl.io s.mem
    · by_cases hoff : (2 ≤ off ∧ off < 10) ∨ off = 17
      · rw [clientState_fastWriteMetaProg hr.2.1 hoff]
        exact Function.update_of_ne (by omega : fl.metaBase + 1 ≠ fl.metaBase + off) val s.mem
      · have hst :
            (Memory.spec 0).clientState s (fastWriteMetaProg ((fl.pBase, off), val)) = s := by
          unfold fastWriteMetaProg; dsimp only; rw [ite_eq_right hoff]; rfl
        rw [hst]

private theorem fss_fastWriteBktLane {keepN : Bool} {w : ℕ} {fl : FastEpochLayout}
    (b lane val : ℕ) :
    FastSplitSafe keepN w fl (fastWriteBktLaneProg ((fl.pBase, (b, lane)), val)) :=
  fun hup hsb s hr => by
    have hg := split_io_geom hr.1.io_valid hup hsb
    obtain ⟨_, hr', hbp, _, _, hof, hoi⟩ := fastWriteBktLaneProg_frame (b := b) (lane := lane)
      (val := val) hr
    refine ⟨hr', fun addr hnot => ?_, hiQuotPres_of_io_unchanged hg hoi,
      fun _ => congrArg BlockPoolState.nSide hbp⟩
    by_cases heq : addr = fl.io.pgL.metaBase
    · subst heq; exact hoi _ hg.own_mb
    · exact hof addr (fun hf => hnot ⟨hf, heq⟩)

private theorem fss_fastBufInsert {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} (role : ℕ)
    (rbl : ℕ × (ℕ × ℕ)) :
    FastSplitSafe keepN w fl (fastBufInsertProg ((fl.pBase, role), rbl)) :=
  fun hup hsb s hr => by
    rcases rbl with ⟨rk, ⟨b, loc⟩⟩
    have hg := split_io_geom hr.1.io_valid hup hsb
    obtain ⟨_, hr', _, hout⟩ := fastBufInsertProg_ready (role := role) (rk := rk) (b := b)
      (loc := loc) hr
    by_cases hrole : role < 2
    · have hoi : ∀ a, fl.io.OwnsAddr a →
          ((Memory.spec 0).clientState s
            (fastBufInsertProg ((fl.pBase, role), (rk, (b, loc))))).mem a = s.mem a :=
        fun a ha => hout hrole a (fun htr => fl.disj_trie_bpAndMeta hr.1 hrole htr (Or.inr ha))
      have hon : ((Memory.spec 0).clientState s
          (fastBufInsertProg ((fl.pBase, role), (rk, (b, loc))))).mem (fl.metaBase + 1) =
          s.mem (fl.metaBase + 1) := by
        refine hout hrole (fl.metaBase + 1) (fun htr => fl.disj_trie_bpAndMeta hr.1 hrole htr ?_)
        have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) hrole
        have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := hr.1.mp_valid.offBktMeta_ge
        exact Or.inl ⟨by omega, by omega⟩
      refine ⟨hr', fun addr hnot => ?_, hiQuotPres_of_io_unchanged hg hoi, fun _ => hon⟩
      refine hout hrole addr fun htr => hnot ⟨fl.owns_of_trie hr.1 hrole htr, fun heq => ?_⟩
      exact fl.disj_trie_bpAndMeta hr.1 hrole htr (Or.inr (heq ▸ hg.own_mb))
    · have hst : (Memory.spec 0).clientState s
          (fastBufInsertProg ((fl.pBase, role), (rk, (b, loc)))) = s := by
        unfold fastBufInsertProg; dsimp only; rw [ite_eq_right hrole]; rfl
      rw [hst]; exact ⟨hr, fun _ _ => rfl, hiQuotPres_refl fl.io s.mem, fun _ => rfl⟩

private theorem fss_fastBufDelete {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} (role rk : ℕ) :
    FastSplitSafe keepN w fl (fastBufDeleteProg ((fl.pBase, role), rk)) :=
  fun hup hsb s hr => by
    have hg := split_io_geom hr.1.io_valid hup hsb
    obtain ⟨_, hr', _, hout⟩ := fastBufDeleteProg_ready (role := role) (rk := rk) hr
    by_cases hrole : role < 2
    · have hoi : ∀ a, fl.io.OwnsAddr a →
          ((Memory.spec 0).clientState s (fastBufDeleteProg ((fl.pBase, role), rk))).mem a =
            s.mem a :=
        fun a ha => (hout hrole).2 a (fun htr => fl.disj_trie_bpAndMeta hr.1 hrole htr (Or.inr ha))
      have hon : ((Memory.spec 0).clientState s
          (fastBufDeleteProg ((fl.pBase, role), rk))).mem (fl.metaBase + 1) =
          s.mem (fl.metaBase + 1) := by
        refine (hout hrole).2 (fl.metaBase + 1)
          (fun htr => fl.disj_trie_bpAndMeta hr.1 hrole htr ?_)
        have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) hrole
        have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := hr.1.mp_valid.offBktMeta_ge
        exact Or.inl ⟨by omega, by omega⟩
      refine ⟨hr', fun addr hnot => ?_, hiQuotPres_of_io_unchanged hg hoi, fun _ => hon⟩
      refine (hout hrole).2 addr fun htr => hnot ⟨fl.owns_of_trie hr.1 hrole htr, fun heq => ?_⟩
      exact fl.disj_trie_bpAndMeta hr.1 hrole htr (Or.inr (heq ▸ hg.own_mb))
    · have hst : (Memory.spec 0).clientState s (fastBufDeleteProg ((fl.pBase, role), rk)) = s := by
        unfold fastBufDeleteProg; dsimp only; rw [ite_eq_right hrole]; rfl
      rw [hst]; exact ⟨hr, fun _ _ => rfl, hiQuotPres_refl fl.io s.mem, fun _ => rfl⟩

private theorem fss_fastBufClearSteps {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} (role : ℕ) :
    FastSplitSafe keepN w fl (fastBufClearStepsProg (fl.pBase, role)) :=
  fun hup hsb s hr => by
    have hg := split_io_geom hr.1.io_valid hup hsb
    obtain ⟨_, hr', _, hout⟩ := fastBufClearStepsProg_ready (role := role) hr
    by_cases hrole : role < 2
    · have hoi : ∀ a, fl.io.OwnsAddr a →
          ((Memory.spec 0).clientState s (fastBufClearStepsProg (fl.pBase, role))).mem a =
            s.mem a :=
        fun a ha => hout hrole a (fun htr => fl.disj_trie_bpAndMeta hr.1 hrole htr (Or.inr ha))
      have hon : ((Memory.spec 0).clientState s
          (fastBufClearStepsProg (fl.pBase, role))).mem (fl.metaBase + 1) =
          s.mem (fl.metaBase + 1) := by
        refine hout hrole (fl.metaBase + 1) (fun htr => fl.disj_trie_bpAndMeta hr.1 hrole htr ?_)
        have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) hrole
        have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := hr.1.mp_valid.offBktMeta_ge
        exact Or.inl ⟨by omega, by omega⟩
      refine ⟨hr', fun addr hnot => ?_, hiQuotPres_of_io_unchanged hg hoi, fun _ => hon⟩
      refine hout hrole addr fun htr => hnot ⟨fl.owns_of_trie hr.1 hrole htr, fun heq => ?_⟩
      exact fl.disj_trie_bpAndMeta hr.1 hrole htr (Or.inr (heq ▸ hg.own_mb))
    · have hst : (Memory.spec 0).clientState s (fastBufClearStepsProg (fl.pBase, role)) = s := by
        unfold fastBufClearStepsProg; dsimp only; rw [ite_eq_right hrole]; rfl
      rw [hst]; exact ⟨hr, fun _ _ => rfl, hiQuotPres_refl fl.io s.mem, fun _ => rfl⟩

private theorem btree_disj_io_and_ns {fl : FastEpochLayout} {w fr addr : ℕ}
    (hv : fl.Valid w fr) (hbt : fl.btL.OwnsAddr addr) :
    ¬fl.io.OwnsAddr addr ∧ addr ≠ fl.metaBase + 1 := by
  have ho32 : 32 ≤ offBktMeta fl.c fl.w fl.N := hv.mp_valid.offBktMeta_ge
  have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) (role := 0) (by decide)
  have hbv := hv.bt_valid
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd0, hd1, hd2, _⟩ := hbv
  dsimp only [FastEpochLayout.btL, epochBTreeLayout, BTreeEpochLayout.OwnsAddr,
    BTreeEpochLayout.totalNodes] at hbt hd0 hd1 hd2
  have htot : 3 * numBucketsWhp fl.N * nSliceWhp fl.N = totalBTreeNodesWhp fl.N := rfl
  rw [htot] at hbt hd1 hd2
  have hk : offBTreeMeta fl.c fl.w fl.N ≤ offBTreeKeys fl.c fl.w fl.N := Nat.le_add_right _ _
  have hvl : offBTreeKeys fl.c fl.w fl.N ≤ offBTreeVals fl.c fl.w fl.N := Nat.le_add_right _ _
  have hm_bt : offBktMeta fl.c fl.w fl.N ≤ offBTreeMeta fl.c fl.w fl.N := by
    unfold offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir; omega
  have hbnd : fl.metaBase + 32 ≤ addr ∧ addr < fl.metaBase + offPageDir fl.c fl.w fl.N := by
    rcases hbt with b1 | b2 | b3 | b4 <;> exact ⟨by omega, by omega⟩
  exact ⟨hv.disj_fast_io addr (Or.inr hbnd), by omega⟩

private theorem fss_fastBTreeReset {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} (b role : ℕ) :
    FastSplitSafe keepN w fl (fastBTreeResetProg (fl.pBase, (b, role))) :=
  fun hup hsb s hr => by
    have hg := split_io_geom hr.1.io_valid hup hsb
    obtain ⟨_, hr', _, hbp, _, _, _, hoi, hof, _⟩ := fastBTreeResetProg_spec (b := b)
      (role := role) hr
    refine ⟨hr', fun addr hnot => ?_, hiQuotPres_of_io_unchanged hg hoi,
      fun _ => congrArg BlockPoolState.nSide hbp⟩
    by_cases heq : addr = fl.io.pgL.metaBase
    · subst heq; exact hoi _ hg.own_mb
    · exact hof addr (fun hf => hnot ⟨hf, heq⟩)

private theorem fss_fastBTreeDelete {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} (b role q : ℕ) :
    FastSplitSafe keepN w fl (fastBTreeDeleteProg ((fl.pBase, (b, role)), q)) :=
  fun hup hsb s hr => by
    have hg := split_io_geom hr.1.io_valid hup hsb
    obtain ⟨_, hr', hout⟩ := fastBTreeDeleteProg_ready (b := b) (role := role) (q := q) hr
    exact ⟨hr',
      fun addr hnot => hout addr fun hbt => hnot
        ⟨fl.owns_of_btree hr.1 hbt, fun heq => (btree_disj_io_and_ns hr.1 hbt).1 (heq ▸ hg.own_mb)⟩,
      hiQuotPres_of_io_unchanged hg
        (fun a ha => hout a fun hbt => (btree_disj_io_and_ns hr.1 hbt).1 ha),
      fun _ => hout _ fun hbt => (btree_disj_io_and_ns hr.1 hbt).2 rfl⟩

private theorem fss_fastBTreeUpdate {keepN : Bool} {w : ℕ} {fl : FastEpochLayout}
    (b role q newVal : ℕ) :
    FastSplitSafe keepN w fl (fastBTreeUpdateProg ((fl.pBase, (b, role)), (q, newVal))) :=
  fun hup hsb s hr => by
    have hg := split_io_geom hr.1.io_valid hup hsb
    obtain ⟨_, hr', hout⟩ := fastBTreeUpdateProg_ready (b := b) (role := role) (q := q)
      (newVal := newVal) hr
    exact ⟨hr',
      fun addr hnot => hout addr fun hbt => hnot
        ⟨fl.owns_of_btree hr.1 hbt, fun heq => (btree_disj_io_and_ns hr.1 hbt).1 (heq ▸ hg.own_mb)⟩,
      hiQuotPres_of_io_unchanged hg
        (fun a ha => hout a fun hbt => (btree_disj_io_and_ns hr.1 hbt).1 ha),
      fun _ => hout _ fun hbt => (btree_disj_io_and_ns hr.1 hbt).2 rfl⟩

private theorem fss_fastBTreeInsert {keepN : Bool} {w : ℕ} {fl : FastEpochLayout}
    (b role q val : ℕ) :
    FastSplitSafe keepN w fl (fastBTreeInsertProg ((fl.pBase, (b, role)), (q, val))) :=
  fun hup hsb s hr => by
    have hg := split_io_geom hr.1.io_valid hup hsb
    obtain ⟨_, hr', hout⟩ := fastBTreeInsertProg_ready (b := b) (role := role) (q := q)
      (val := val) hr
    exact ⟨hr',
      fun addr hnot => hout addr fun hbt => hnot
        ⟨fl.owns_of_btree hr.1 hbt, fun heq => (btree_disj_io_and_ns hr.1 hbt).1 (heq ▸ hg.own_mb)⟩,
      hiQuotPres_of_io_unchanged hg
        (fun a ha => hout a fun hbt => (btree_disj_io_and_ns hr.1 hbt).1 ha),
      fun _ => hout _ fun hbt => (btree_disj_io_and_ns hr.1 hbt).2 rfl⟩

private theorem feistelSplitBounded_snd_lt {fl : FastEpochLayout} {w fr u_val : ℕ}
    (hv : fl.Valid w fr) (hu : u_val < fl.U) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (feistelSplitBoundedProg (fl.feistelCtx, u_val))).2 <
      2 ^ fl.io.pgL.qBits := by
  have hres : ((Memory.spec 0).clientResult s
      (feistelSplitBoundedProg (fl.feistelCtx, u_val))).2 = u_val / 2 ^ bWhp fl.N := by
    unfold feistelSplitBoundedProg
    dsimp only [FastEpochLayout.feistelCtx, FastEpochLayout.dtOffBot]
    simp only [pure_bind, prog_clientResult_bind, prog_clientResult_pure,
      Nat.shiftRight_eq_div_pow]
  rw [hres]
  have hu_kb : u_val < 2 ^ keyBits fl.U := hu.trans_le (Nat.le_pow_clog Nat.one_lt_two fl.U)
  have hq_lt : u_val / 2 ^ bWhp fl.N < 2 ^ quotBitsWhp fl.U fl.N := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact hu_kb.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by unfold quotBitsWhp; omega))
  exact hq_lt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hv.qBits_le)

private theorem fastFeistelSplit_snd_lt {fl : FastEpochLayout} {w u_val : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    ((Memory.spec 0).clientResult s (fastFeistelSplitProg (fl.pBase, u_val))).2 <
      2 ^ fl.io.pgL.qBits := by
  unfold fastFeistelSplitProg
  rw [prog_clientResult_bind, clientState_read_eq, prog_clientResult_read]
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hr.2.1 46 (by decide)
  have hU_pos : 0 < fl.U :=
    lt_of_lt_of_le (whpThreshold_pos fl.c) (hr.1.thresh_le.trans hr.1.N_le_U)
  by_cases hle : u_val ≤ s.mem (fl.pBase + 46)
  · rw [ite_eq_left hle, prog_clientResult_bind, clientState_loadHashStaticCtxProg,
      clientResult_loadFeistelCtx hr.2.1]
    exact feistelSplitBounded_snd_lt hr.1 (by omega) s
  · rw [ite_eq_right hle, prog_clientResult_pure]
    exact Nat.two_pow_pos _

private theorem fastBpReadAt_fst_lt {fl : FastEpochLayout} {w : ℕ} {bl : ℕ × ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) (hup : fl.io.usePaged = 0) (hsb : fl.io.sideBit ≠ 0) :
    ((Memory.spec 0).clientResult s (fastBpReadAtProg (fl.pBase, bl))).1 <
      2 ^ fl.io.pgL.qBits := by
  rcases bl with ⟨b, loc⟩
  have hg := split_io_geom hr.1.io_valid hup hsb
  unfold fastBpReadAtProg
  rw [prog_clientResult_bind, clientState_loadBlockPoolCtxProg,
    clientResult_loadBlockPoolCtxProg hr.2.1, prog_clientResult_bind, clientState_bpToPhysProg]
  exact slotIoReadRaw_fst_lt hg _ s

private theorem fss_fastBpWriteAt {keepN : Bool} {w : ℕ} {fl : FastEpochLayout}
    (bl : ℕ × ℕ) {qv : ℕ × ℕ} (hq : qv.1 < 2 ^ fl.io.pgL.qBits) :
    FastSplitSafe keepN w fl (fastBpWriteAtProg ((fl.pBase, bl), qv)) :=
  fun hup hsb s hr => by
    rcases bl with ⟨b, loc⟩
    unfold fastBpWriteAtProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hr.2.1]
    exact fss_of_poolSafe (fun _ _ hg hdisj _ => ps_bpWriteAtRaw hg hdisj b loc hq) hup hsb s hr

private theorem fss_fastBpAppend {w : ℕ} {fl : FastEpochLayout}
    (b : ℕ) {qv : ℕ × ℕ} (hq : qv.1 < 2 ^ fl.io.pgL.qBits) :
    FastSplitSafe false w fl (fastBpAppendProg ((fl.pBase, b), qv)) ∧
    (fl.io.usePaged = 0 → fl.io.sideBit ≠ 0 → ∀ s, FastLayoutReady w fl s →
      s.mem fl.io.pgL.metaBase ≤ s.mem (fl.metaBase + 1) →
      s.mem (fl.metaBase + 1) < fl.io.pgL.nCap →
      pairQuotAt fl.io.pgL.itemBase fl.io.pgL.offTail fl.io.pgL.vBits fl.io.pgL.w
        ((Memory.spec 0).clientState s (fastBpAppendProg ((fl.pBase, b), qv))).mem
        (s.mem (fl.metaBase + 1)) < 2 ^ fl.io.pgL.qBits) := by
  refine ⟨fun hup hsb s hr => ?_, fun hup hsb s hr hsp hlt => ?_⟩
  · unfold fastBpAppendProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hr.2.1]
    exact fss_of_poolSafe (fun _ hmv hg hdisj _ => (ps_bpAppendRaw hmv hg hdisj b hq).1)
      hup hsb s hr
  · have hg := split_io_geom hr.1.io_valid hup hsb
    unfold fastBpAppendProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hr.2.1]
    exact (ps_bpAppendRaw hr.1.mp_valid hg hr.1.bp_valid.disjoint b hq).2 s hsp hlt

private theorem fss_fastBpPopBktBack {w : ℕ} {fl : FastEpochLayout} (b : ℕ) :
    FastSplitSafe false w fl (fastBpPopBktBackProg (fl.pBase, b)) :=
  fun hup hsb s hr => by
    unfold fastBpPopBktBackProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hr.2.1]
    exact fss_of_poolSafe (fun _ hmv hg hdisj _ => ps_bpPopBktBackRaw hmv hg hdisj b) hup hsb s hr

private theorem fss_fastEnterFallback {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} :
    FastSplitSafe keepN w fl (fastEnterFallbackProg fl.pBase) :=
  fun hup hsb s hr => by
    unfold fastEnterFallbackProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hr.2.1]
    exact fss_of_poolSafe (fun _ hmv hg hdisj hdisj2 => ps_enterFallback hmv hg hdisj hdisj2)
      hup hsb s hr

private theorem fss_fastFallbackInsert {w : ℕ} {fl : FastEpochLayout} (u_val v_val : ℕ) :
    FastSplitSafe false w fl (fastFallbackInsertProg ((fl.pBase, u_val), v_val)) ∧
    (fl.io.usePaged = 0 → fl.io.sideBit ≠ 0 → ∀ s, FastLayoutReady w fl s →
      s.mem (fl.metaBase + 1) <
        ((Memory.spec 0).clientState s
          (fastFallbackInsertProg ((fl.pBase, u_val), v_val))).mem (fl.metaBase + 1) →
      s.mem fl.io.pgL.metaBase ≤ s.mem (fl.metaBase + 1) →
      s.mem (fl.metaBase + 1) < fl.io.pgL.nCap →
      pairQuotAt fl.io.pgL.itemBase fl.io.pgL.offTail fl.io.pgL.vBits fl.io.pgL.w
        ((Memory.spec 0).clientState s
          (fastFallbackInsertProg ((fl.pBase, u_val), v_val))).mem
        (s.mem (fl.metaBase + 1)) < 2 ^ fl.io.pgL.qBits) := by
  refine ⟨fun hup hsb s hr => ?_, fun hup hsb s hr hgt hsp hlt => ?_⟩
  · unfold fastFallbackInsertProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read]
    have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hr.2.1 46 (by decide)
    have hU_pos : 0 < fl.U :=
      lt_of_lt_of_le (whpThreshold_pos fl.c) (hr.1.thresh_le.trans hr.1.N_le_U)
    by_cases hle : u_val ≤ s.mem (fl.pBase + 46)
    · rw [ite_eq_left hle, StateTransitionSpec.clientState_bind,
        clientState_loadHashStaticCtxProg, clientResult_loadFeistelCtx hr.2.1,
        StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
        clientResult_loadBlockPoolCtxProg hr.2.1]
      exact fss_of_poolSafe
        (fun _ hmv hg hdisj _ =>
          (ps_fallbackInsert hmv hg hdisj fl.feistelCtx u_val v_val
            (feistelSplitBounded_snd_lt hr.1 (by omega))).1)
        hup hsb s hr
    · rw [ite_eq_right hle]
      exact ⟨hr, fun _ _ => rfl, hiQuotPres_refl fl.io s.mem, fun hk => Bool.noConfusion hk⟩
  · have hg := split_io_geom hr.1.io_valid hup hsb
    unfold fastFallbackInsertProg at hgt ⊢
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read] at hgt ⊢
    have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hr.2.1 46 (by decide)
    have hU_pos : 0 < fl.U :=
      lt_of_lt_of_le (whpThreshold_pos fl.c) (hr.1.thresh_le.trans hr.1.N_le_U)
    by_cases hle : u_val ≤ s.mem (fl.pBase + 46)
    · rw [ite_eq_left hle, StateTransitionSpec.clientState_bind,
        clientState_loadHashStaticCtxProg, clientResult_loadFeistelCtx hr.2.1,
        StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
        clientResult_loadBlockPoolCtxProg hr.2.1] at hgt ⊢
      exact (ps_fallbackInsert hr.1.mp_valid hg hr.1.bp_valid.disjoint fl.feistelCtx u_val v_val
        (feistelSplitBounded_snd_lt hr.1 (by omega))).2 s hgt hsp hlt
    · rw [ite_eq_right hle] at hgt
      exact absurd hgt (Nat.lt_irrefl _)

private theorem fss_fastFallbackDelete {w : ℕ} {fl : FastEpochLayout} (u_val : ℕ) :
    FastSplitSafe false w fl (fastFallbackDeleteProg (fl.pBase, u_val)) :=
  fun hup hsb s hr => by
    unfold fastFallbackDeleteProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read]
    by_cases hle : u_val ≤ s.mem (fl.pBase + 46)
    · rw [ite_eq_left hle, StateTransitionSpec.clientState_bind,
        clientState_loadHashStaticCtxProg, clientResult_loadFeistelCtx hr.2.1,
        StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
        clientResult_loadBlockPoolCtxProg hr.2.1]
      exact fss_of_poolSafe
        (fun _ hmv hg hdisj _ => ps_fallbackDelete hmv hg hdisj fl.feistelCtx u_val)
        hup hsb s hr
    · rw [ite_eq_right hle]
      exact ⟨hr, fun _ _ => rfl, hiQuotPres_refl fl.io s.mem, fun hk => Bool.noConfusion hk⟩

/-! ## Section 6: Composing Fast-Path Shadow, Drain, Remove, and Insert Subprograms -/

private theorem fss_fastCommitShadow {keepN : Bool} {w : ℕ} {fl : FastEpochLayout}
    (b shRole shIns : ℕ) :
    FastSplitSafe keepN w fl (fastCommitShadowProg (fl.pBase, (b, (shRole, shIns)))) := by
  unfold fastCommitShadowProg
  refine fss_bind (fss_fastWriteBktLane _ _ _) fun _ => ?_
  refine fss_bind (fss_fastWriteBktLane _ _ _) fun _ => ?_
  refine fss_bind (fss_fastWriteBktLane _ _ _) fun _ => fss_fastWriteBktLane _ _ _

private theorem fss_fastShadowSteps8 {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} (b : ℕ) :
    FastSplitSafe keepN w fl (fastShadowSteps8Prog (fl.pBase, b)) := by
  have hadv : ∀ shPos cnt shRole shIns',
      FastSplitSafe keepN w fl
        (fastShadowAdvanceProg ((fl.pBase, b), ((shPos, cnt), (shRole, shIns')))) :=
    fun shPos cnt shRole shIns' => by
      unfold fastShadowAdvanceProg
      refine fss_bind (fss_read _) fun _ => ?_
      refine fss_ite (fun _ => ?_) (fun _ => fss_fastCommitShadow _ _ _)
      refine fss_ite (fun _ => ?_) (fun _ => fss_fastCommitShadow _ _ _)
      refine fss_ite (fun _ => ?_) (fun _ => fss_fastCommitShadow _ _ _)
      exact fss_bind (fss_fastWriteBktLane _ _ _) fun _ => fss_fastWriteBktLane _ _ _
  have h1 : FastSplitSafe keepN w fl (fastShadowStepProg (fl.pBase, b)) := by
    unfold fastShadowStepProg fastShadowBodyProg fastShadowBodyTailProg
    refine fss_bind (fss_read _) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
    refine fss_bind (fss_ro (clientState_fastReadBktCntProg _)) fun _ => ?_
    refine fss_bind (fss_read _) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
    refine fss_bind (fss_ro (clientState_fastBpReadAtProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastFeistelReconProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastFpHashProg _)) fun _ => ?_
    refine fss_bind (fss_read _) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastBTreeLookupProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_shadowRoleProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => hadv _ _ _ _)
    exact fss_bind (fss_fastBTreeInsert _ _ _ _) fun _ => hadv _ _ _ _
  have h2 : FastSplitSafe keepN w fl (fastShadowSteps2Prog (fl.pBase, b)) :=
    fss_bind h1 fun _ => h1
  have h4 : FastSplitSafe keepN w fl (fastShadowSteps4Prog (fl.pBase, b)) :=
    fss_bind h2 fun _ => h2
  exact fss_bind h4 fun _ => h4

private theorem fss_advanceTrySalt {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} :
    FastSplitSafe keepN w fl (advanceTrySaltProg fl.pBase) := by
  unfold advanceTrySaltProg writeTryResetMetaProg
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_bind (fss_read _) fun _ => ?_
  refine fss_bind (fss_ro (clientState_nextSaltProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_tryRoleProg _)) fun _ => ?_
  refine fss_bind (fss_fastBTreeReset _ _) fun _ => ?_
  refine fss_bind (fss_fastWriteMeta _ _) fun _ => ?_
  exact fss_bind (fss_fastWriteMeta _ _) fun _ => fss_fastWriteMeta _ _

private theorem fss_commitTrySalt {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} :
    FastSplitSafe keepN w fl (commitTrySaltProg fl.pBase) := by
  unfold commitTrySaltProg clearTryMetaProg
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_tryRoleProg _)) fun _ => ?_
  refine fss_bind (fss_fastWriteBktLane _ _ _) fun _ => ?_
  refine fss_bind (fss_fastWriteBktLane _ _ _) fun _ => ?_
  refine fss_bind (fss_fastWriteBktLane _ _ _) fun _ => ?_
  refine fss_bind (fss_fastWriteMeta _ _) fun _ => ?_
  exact fss_bind (fss_fastWriteMeta _ _) fun _ => fss_fastWriteMeta _ _

private theorem fss_startTrySalt {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} (b : ℕ) :
    FastSplitSafe keepN w fl (startTrySaltProg (fl.pBase, b)) := by
  unfold startTrySaltProg writeStartTryMetaProg writeTryResetMetaProg
  refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_tryRoleProg _)) fun _ => ?_
  refine fss_bind (fss_fastBTreeReset _ _) fun _ => ?_
  refine fss_bind (fss_fastWriteMeta _ _) fun _ => ?_
  refine fss_bind (fss_fastWriteMeta _ _) fun _ => ?_
  refine fss_bind (fss_fastWriteMeta _ _) fun _ => ?_
  exact fss_bind (fss_fastWriteMeta _ _) fun _ => fss_fastWriteMeta _ _

private theorem fss_drainTryStep {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} :
    FastSplitSafe keepN w fl (drainTryStepProg fl.pBase) := by
  unfold drainTryStepProg drainTryScanSlotProg drainTryInsertOrAdvProg
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_bind (fss_read _) fun _ => ?_
  refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
  refine fss_bind (fss_ro (clientState_fastReadBktCntProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_ite (fun _ => ?_) fun _ => ?_
  · refine fss_bind (fss_ro (clientState_fastBpReadAtProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastFeistelReconProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastFpHashProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastBTreeLookupProg _)) fun _ => ?_
    refine fss_ite (fun _ => ?_) fun _ => ?_
    · refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastFpHashProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_tryRoleProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastBTreeLookupProg _)) fun _ => ?_
      refine fss_ite (fun _ => fss_advanceTrySalt) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
      refine fss_bind (fss_read _) fun _ => ?_
      refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
      refine fss_bind (fss_fastBTreeInsert _ _ _ _) fun _ => ?_
      exact fss_bind (fss_fastWriteMeta _ _) fun _ => fss_fastWriteMeta _ _
    · refine fss_bind (fss_read _) fun _ => ?_
      exact fss_ite (fun _ => fss_fastWriteMeta _ _) (fun _ => fss_pure ())
  · refine fss_bind (fss_ro (runClient_state_drainTryCheckDpProg fl.pBase)) fun _ => ?_
    exact fss_ite (fun _ => fss_commitTrySalt) (fun _ => fss_advanceTrySalt)

private theorem fss_drainOldSlot {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} :
    FastSplitSafe keepN w fl (drainOldSlotProg fl.pBase) := by
  have hshMaint : ∀ b fp loc cIns',
      FastSplitSafe keepN w fl
        (drainOldShadowMaintProg (((fl.pBase, b), (fp, loc)), cIns')) :=
    fun b fp loc cIns' => by
      unfold drainOldShadowMaintProg
      refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_shadowRoleProg _)) fun _ => ?_
      refine fss_ite (fun _ => ?_) fun _ => ?_
      · refine fss_bind (fss_read _) fun _ => ?_
        refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
        refine fss_bind (fss_fastBTreeReset _ _) fun _ => ?_
        exact fss_bind (fss_fastWriteBktLane _ _ _) fun _ => fss_fastWriteBktLane _ _ _
      · refine fss_bind (fss_read _) fun _ => ?_
        refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
        refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
        refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
        refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
        exact fss_bind (fss_fastBTreeInsert _ _ _ _) fun _ => fss_fastWriteBktLane _ _ _
  unfold drainOldSlotProg drainOldActiveBodyProg drainOldInsertNoCollProg
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_bind (fss_read _) fun _ => ?_
  refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
  simp only [pure_bind]
  refine fss_bind (fss_ro (clientState_fastBufItemAllocProg _)) fun _ => ?_
  refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
  refine fss_bind (fss_ro (clientState_fastBufCheckSlotProg _)) fun _ => ?_
  refine fss_ite (fun _ => fss_fastWriteMeta _ _) fun _ => ?_
  refine fss_bind (fss_fastShadowSteps8 _) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadBktCntProg _)) fun _ => ?_
  refine fss_bind (fss_read _) fun _ => ?_
  refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
  refine fss_bind (fss_ro (clientState_fastBpReadAtProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastFeistelReconProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastRKeyProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastFpHashProg _)) fun _ => ?_
  refine fss_bind (fss_ro (clientState_fastBTreeLookupProg _)) fun _ => ?_
  refine fss_ite (fun _ => ?_) fun _ => ?_
  · refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_bind (fss_read _) fun _ => ?_
    refine fss_bind (fss_read _) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
    refine fss_bind (fss_fastBTreeInsert _ _ _ _) fun _ => ?_
    refine fss_bind (fss_fastWriteBktLane _ _ _) fun _ => ?_
    refine fss_bind (hshMaint _ _ _ _) fun _ => ?_
    exact fss_bind (fss_fastBufDelete _ _) fun _ => fss_fastWriteMeta _ _
  · refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    exact fss_ite (fun _ => fss_startTrySalt _) (fun _ => fss_pure ())

private theorem fss_drainTrySteps5 {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} :
    FastSplitSafe keepN w fl (drainTrySteps5Prog fl.pBase) := by
  have h1 : FastSplitSafe keepN w fl (drainTryTickProg fl.pBase) := by
    unfold drainTryTickProg
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
    refine fss_bind fss_drainTryStep fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    exact fss_ite (fun _ => fss_drainOldSlot) (fun _ => fss_pure ())
  unfold drainTrySteps5Prog
  refine fss_bind h1 fun _ => fss_bind h1 fun _ => fss_bind h1 fun _ => ?_
  exact fss_bind h1 fun _ => h1

private theorem fss_drainTicks16 {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} :
    FastSplitSafe keepN w fl (drainTicks16Prog fl.pBase) := by
  have h1 : FastSplitSafe keepN w fl (drainTickProg fl.pBase) := by
    unfold drainTickProg
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_drainOldSlot)
    refine fss_bind fss_drainTryStep fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    exact fss_ite (fun _ => fss_drainOldSlot) (fun _ => fss_pure ())
  have h2 : FastSplitSafe keepN w fl (drainTicks2Prog fl.pBase) := fss_bind h1 fun _ => h1
  have h4 : FastSplitSafe keepN w fl (drainTicks4Prog fl.pBase) := fss_bind h2 fun _ => h2
  have h8 : FastSplitSafe keepN w fl (drainTicks8Prog fl.pBase) := fss_bind h4 fun _ => h4
  exact fss_bind h8 fun _ => h8

private theorem fss_advanceSubEpoch {keepN : Bool} {w : ℕ} {fl : FastEpochLayout} :
    FastSplitSafe keepN w fl (advanceSubEpochProg fl.pBase) := by
  unfold advanceSubEpochProg
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_bind (fss_read _) fun _ => ?_
  simp only [pure_bind]
  refine fss_ite (fun _ => ?_) fun _ => ?_
  · refine fss_bind fss_drainTicks16 fun _ => ?_
    refine fss_ite (fun _ => fss_fastWriteMeta _ _) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
    refine fss_bind (fss_ro (clientState_fastBufItemAllocProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    exact fss_ite (fun _ => fss_fastWriteMeta _ _) (fun _ => fss_fastEnterFallback)
  · refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
    refine fss_bind (fss_fastBufClearSteps _) fun _ => ?_
    refine fss_ite (fun _ => fss_fastWriteMeta _ _) fun _ => ?_
    refine fss_bind (fss_fastWriteMeta _ _) fun _ => ?_
    exact fss_bind (fss_fastWriteMeta _ _) fun _ => fss_fastWriteMeta _ _

private theorem fss_fastRemoveAt {w : ℕ} {fl : FastEpochLayout} (b delLoc u_val : ℕ) :
    FastSplitSafe false w fl (fastRemoveAtProg ((fl.pBase, b), (delLoc, u_val))) := by
  have hdelBt :
      FastSplitSafe false w fl (fastDeleteFromBTreesProg ((fl.pBase, (b, delLoc)), u_val)) := by
    unfold fastDeleteFromBTreesProg fastDelShadowTryStepProg fastDelTryStepProg
    refine fss_bind (fss_read _) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastFpHashProg _)) fun _ => ?_
    refine fss_bind (fss_fastBTreeDelete _ _ _) fun _ => ?_
    refine fss_bind ?_ fun _ => ?_
    · refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
      refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
      exact fss_bind (fss_ro (clientState_shadowRoleProg _)) fun _ => fss_fastBTreeDelete _ _ _
    · refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
      refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
      refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastFpHashProg _)) fun _ => ?_
      exact fss_bind (fss_ro (clientState_tryRoleProg _)) fun _ => fss_fastBTreeDelete _ _ _
  have hunidx : FastSplitSafe false w fl (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u_val)) := by
    unfold fastUnindexAtProg
    refine fss_bind (fss_ro (clientState_fastRKeyProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
    refine fss_bind (fss_ro (clientState_fastBufLookupProg _)) fun _ => ?_
    refine fss_ite (fun _ => fss_fastBufDelete _ _) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_bind (fss_read _) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => hdelBt)
    simp only [pure_bind]
    refine fss_bind (fss_ro (clientState_fastBufLookupProg _)) fun _ => ?_
    exact fss_ite (fun _ => fss_fastBufDelete _ _) (fun _ => hdelBt)
  have hrelBt : ∀ lastLoc u_last,
      FastSplitSafe false w fl (fastRelocBTreeProg ((fl.pBase, (b, delLoc)), (lastLoc, u_last))) :=
    fun lastLoc u_last => by
      unfold fastRelocBTreeProg fastRelocShadowStepProg fastRelocTryStepProg fastRelocTryInsProg
      refine fss_bind (fss_read _) fun _ => ?_
      refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
      refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastFpHashProg _)) fun _ => ?_
      refine fss_bind (fss_fastBTreeUpdate _ _ _ _) fun _ => ?_
      refine fss_bind ?_ fun _ => ?_
      · refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
        refine fss_bind (fss_read _) fun _ => ?_
        refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
        refine fss_bind (fss_ro (clientState_shadowRoleProg _)) fun _ => ?_
        refine fss_bind (fss_fastBTreeInsert _ _ _ _) fun _ => ?_
        refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
        exact fss_ite (fun _ => fss_fastWriteBktLane _ _ _) (fun _ => fss_pure ())
      · refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
        refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
        refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
        refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
        refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
        refine fss_bind (fss_ro (clientState_fastFpHashProg _)) fun _ => ?_
        refine fss_bind (fss_ro (clientState_tryRoleProg _)) fun _ => ?_
        refine fss_ite (fun _ => fss_fastBTreeUpdate _ _ _ _) fun _ => ?_
        refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
        refine fss_bind (fss_ro (clientState_fastBTreeLookupProg _)) fun _ => ?_
        refine fss_ite (fun _ => fss_advanceTrySalt) fun _ => ?_
        refine fss_bind (fss_read _) fun _ => ?_
        refine fss_bind (fss_fastBTreeInsert _ _ _ _) fun _ => ?_
        refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
        exact fss_ite (fun _ => fss_fastWriteMeta _ _) (fun _ => fss_pure ())
  have hswapDown : ∀ lastLoc,
      FastSplitSafe false w fl (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc))) :=
    fun lastLoc => by
      unfold fastSwapLastDownProg fastRelocLastProg
      refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
      refine fss_bind_ro (clientState_fastBpReadAtProg _) fun s₁ hr₁ => ?_
      refine fss_bind (fss_ro (clientState_fastFeistelReconProg _)) fun _ => ?_
      refine fss_bind
        (fun hup hsb => fss_fastBpWriteAt _ (fastBpReadAt_fst_lt hr₁ hup hsb) hup hsb)
        fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastRKeyProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
      refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
      refine fss_bind (fss_ro (clientState_fastBufLookupProg _)) fun _ => ?_
      refine fss_ite (fun _ => fss_fastBufInsert _ _) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
      refine fss_bind (fss_read _) fun _ => ?_
      refine fss_ite (fun _ => ?_) (fun _ => hrelBt _ _)
      simp only [pure_bind]
      refine fss_bind (fss_ro (clientState_fastBufLookupProg _)) fun _ => ?_
      exact fss_ite (fun _ => fss_fastBufInsert _ _) (fun _ => hrelBt _ _)
  unfold fastRemoveAtProg fastPromoteShadowIfDoneProg fastClampTryPosProg
  refine fss_bind (fss_read _) fun _ => ?_
  refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
  refine fss_bind (fss_ro (clientState_fastReadBktCntProg _)) fun _ => ?_
  refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
  simp only [pure_bind]
  refine fss_bind hunidx fun _ => ?_
  refine fss_bind (hswapDown _) fun _ => ?_
  refine fss_bind (fss_fastBpPopBktBack b) fun _ => ?_
  refine fss_bind ?_ fun _ => ?_
  · refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure ())
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_shadowRoleProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadBktLaneProg _)) fun _ => ?_
    refine fss_bind (fss_fastWriteBktLane _ _ _) fun _ => ?_
    exact fss_bind (fss_fastWriteBktLane _ _ _) fun _ => fss_fastWriteBktLane _ _ _
  · refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    exact fss_ite (fun _ => fss_fastWriteMeta _ _) (fun _ => fss_pure ())

private theorem fss_largeEpochInsert {w : ℕ} {fl : FastEpochLayout} (u_val v_val : ℕ) :
    FastSplitSafe false w fl (largeEpochInsertProg ((fl.pBase, u_val), v_val)) ∧
    (fl.io.usePaged = 0 → fl.io.sideBit ≠ 0 → ∀ s, FastLayoutReady w fl s →
      s.mem (fl.metaBase + 1) <
        ((Memory.spec 0).clientState s
          (largeEpochInsertProg ((fl.pBase, u_val), v_val))).mem (fl.metaBase + 1) →
      s.mem fl.io.pgL.metaBase ≤ s.mem (fl.metaBase + 1) →
      s.mem (fl.metaBase + 1) < fl.io.pgL.nCap →
      pairQuotAt fl.io.pgL.itemBase fl.io.pgL.offTail fl.io.pgL.vBits fl.io.pgL.w
        ((Memory.spec 0).clientState s
          (largeEpochInsertProg ((fl.pBase, u_val), v_val))).mem
        (s.mem (fl.metaBase + 1)) < 2 ^ fl.io.pgL.qBits) := by
  have hrkFree : ∀ {keepN : Bool}, FastSplitSafe keepN w fl
      (fastCheckRKeyFreeProg (fl.pBase, u_val)) := by
    intro keepN
    unfold fastCheckRKeyFreeProg
    refine fss_bind (fss_ro (clientState_fastRKeyProg _)) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure _)
    refine fss_bind (fss_ro (clientState_fastBufLookupProg _)) fun _ => ?_
    refine fss_ite (fun _ => fss_pure _) fun _ => ?_
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    refine fss_bind (fss_read _) fun _ => ?_
    refine fss_ite (fun _ => ?_) (fun _ => fss_pure _)
    refine fss_bind (fss_ro (clientState_fastBufLookupProg _)) fun _ => ?_
    exact fss_ite (fun _ => fss_pure _) (fun _ => fss_pure _)
  have hfb_chain : fl.io.usePaged = 0 → fl.io.sideBit ≠ 0 → ∀ s, FastLayoutReady w fl s →
      s.mem (fl.metaBase + 1) <
        ((Memory.spec 0).clientState s
          (fastEnterFallbackProg fl.pBase >>= fun _ =>
            fastFallbackInsertProg ((fl.pBase, u_val), v_val))).mem (fl.metaBase + 1) →
      s.mem fl.io.pgL.metaBase ≤ s.mem (fl.metaBase + 1) →
      s.mem (fl.metaBase + 1) < fl.io.pgL.nCap →
      pairQuotAt fl.io.pgL.itemBase fl.io.pgL.offTail fl.io.pgL.vBits fl.io.pgL.w
        ((Memory.spec 0).clientState s
          (fastEnterFallbackProg fl.pBase >>= fun _ =>
            fastFallbackInsertProg ((fl.pBase, u_val), v_val))).mem
        (s.mem (fl.metaBase + 1)) < 2 ^ fl.io.pgL.qBits := by
    intro hup hsb s hr hgt hsp hlt
    rw [StateTransitionSpec.clientState_bind] at hgt ⊢
    obtain ⟨hr₁, _, hp₁, hn₁⟩ := fss_fastEnterFallback (keepN := true) hup hsb s hr
    set s₁ := (Memory.spec 0).clientState s (fastEnterFallbackProg fl.pBase)
    have heq_n : s₁.mem (fl.metaBase + 1) = s.mem (fl.metaBase + 1) := hn₁ rfl
    have hmb₁ : s₁.mem fl.io.pgL.metaBase = s.mem fl.io.pgL.metaBase := hp₁.1
    have hres := (fss_fastFallbackInsert u_val v_val).2 hup hsb s₁ hr₁
      (by omega) (by omega) (by omega)
    rwa [heq_n] at hres
  have hins : FastSplitSafe false w fl (fastInsertProg ((fl.pBase, u_val), v_val)) := by
    unfold fastInsertProg fastInsertNewStepProg
    refine fss_bind (fss_ro (clientState_fastProbeProg _)) fun pr => ?_
    refine fss_ite (fun _ => ?_) fun _ => ?_
    · refine fss_bind_ro (clientState_fastFeistelSplitProg _) fun s₁ hr₁ => ?_
      exact fss_fastBpWriteAt _ (fastFeistelSplit_snd_lt hr₁)
    · refine fss_bind hrkFree fun _ => ?_
      refine fss_ite
        (fun _ => fss_bind fss_fastEnterFallback fun _ => (fss_fastFallbackInsert u_val v_val).1)
        fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastReadBktCntProg _)) fun _ => ?_
      refine fss_bind (fss_read _) fun _ => ?_
      refine fss_ite
        (fun _ => fss_bind fss_fastEnterFallback fun _ => (fss_fastFallbackInsert u_val v_val).1)
        fun _ => ?_
      refine fss_bind ?_ fun _ => fss_advanceSubEpoch
      refine fss_bind fss_drainTrySteps5 fun _ => ?_
      refine fss_bind (fss_fastShadowSteps8 _) fun _ => ?_
      refine fss_bind_ro (clientState_fastFeistelSplitProg _) fun s₁ hr₁ => ?_
      refine fss_bind (fss_fastBpAppend _ (fastFeistelSplit_snd_lt hr₁)).1 fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastRKeyProg _)) fun _ => ?_
      refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
      exact fss_fastBufInsert _ _
  refine ⟨?_, fun hup hsb s hr hgt hsp hlt => ?_⟩
  · unfold largeEpochInsertProg
    refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
    exact fss_ite (fun _ => hins) (fun _ => (fss_fastFallbackInsert u_val v_val).1)
  · unfold largeEpochInsertProg at hgt ⊢
    rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg] at hgt ⊢
    by_cases hm0 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) = 0
    · rw [ite_eq_left hm0] at hgt ⊢
      unfold fastInsertProg at hgt ⊢
      rw [StateTransitionSpec.clientState_bind, clientState_fastProbeProg] at hgt ⊢
      dsimp only at hgt ⊢
      set pr := (Memory.spec 0).clientResult s (fastProbeProg (fl.pBase, u_val))
      by_cases hpr : pr.1.1 ≠ 0
      · rw [ite_eq_left hpr] at hgt
        have hkeep : FastSplitSafe true w fl
            (fastFeistelSplitProg (fl.pBase, u_val) >>= fun bq =>
              fastBpWriteAtProg ((fl.pBase, (pr.2.1, pr.2.2.1)), (bq.2, v_val))) :=
          fss_bind_ro (clientState_fastFeistelSplitProg _) fun _ hr₁ =>
            fss_fastBpWriteAt _ (fastFeistelSplit_snd_lt hr₁)
        have heq_n := (hkeep hup hsb s hr).2.2.2 rfl
        exact absurd hgt (by rw [heq_n]; exact Nat.lt_irrefl _)
      · rw [ite_eq_right hpr] at hgt ⊢
        have hrk_st : (Memory.spec 0).clientState s
            (fastCheckRKeyFreeProg (fl.pBase, u_val)) = s :=
          clientState_fastCheckRKeyFreeProg (fl.pBase, u_val) s
        rw [StateTransitionSpec.clientState_bind, hrk_st] at hgt ⊢
        by_cases hrk0 : (Memory.spec 0).clientResult s
            (fastCheckRKeyFreeProg (fl.pBase, u_val)) ≠ 0
        · rw [ite_eq_left hrk0] at hgt ⊢
          exact hfb_chain hup hsb s hr hgt hsp hlt
        · rw [ite_eq_right hrk0, StateTransitionSpec.clientState_bind,
            clientState_fastReadBktCntProg, StateTransitionSpec.clientState_bind,
            clientState_read_eq] at hgt ⊢
          split_ifs at hgt ⊢ with hcnt
          · exact hfb_chain hup hsb s hr hgt hsp hlt
          · set cnt := (Memory.spec 0).clientResult s (fastReadBktCntProg (fl.pBase, pr.2.1))
            unfold fastInsertNewStepProg
            rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
              StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
              clientState_fastFeistelSplitProg, StateTransitionSpec.clientState_bind,
              StateTransitionSpec.clientState_bind, clientState_fastRKeyProg,
              StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
            obtain ⟨hr_dt, _, hp_dt, hn_dt⟩ := fss_drainTrySteps5 (keepN := true) hup hsb s hr
            set s_dt := (Memory.spec 0).clientState s (drainTrySteps5Prog fl.pBase)
            obtain ⟨hr₁, _, hp_sh, hn_sh⟩ :=
              fss_fastShadowSteps8 (keepN := true) pr.2.1 hup hsb s_dt hr_dt
            set s₁ := (Memory.spec 0).clientState s_dt (fastShadowSteps8Prog (fl.pBase, pr.2.1))
            have hns₁ : s₁.mem (fl.metaBase + 1) = s.mem (fl.metaBase + 1) :=
              (hn_sh rfl).trans (hn_dt rfl)
            have hmb₁ : s₁.mem fl.io.pgL.metaBase = s.mem fl.io.pgL.metaBase :=
              hp_sh.1.trans hp_dt.1
            set bq := (Memory.spec 0).clientResult s₁ (fastFeistelSplitProg (fl.pBase, u_val))
            have hbq := fastFeistelSplit_snd_lt (u_val := u_val) hr₁
            obtain ⟨hr₂, _, hp₂, _⟩ :=
              (fss_fastBpAppend pr.2.1 (qv := (bq.2, v_val)) hbq).1 hup hsb s₁ hr₁
            have hself := (fss_fastBpAppend pr.2.1 (qv := (bq.2, v_val)) hbq).2 hup hsb s₁ hr₁
              (by omega) (by omega)
            rw [hns₁] at hself
            set s₂ := (Memory.spec 0).clientState s₁
              (fastBpAppendProg ((fl.pBase, pr.2.1), (bq.2, v_val)))
            set rk := (Memory.spec 0).clientResult s₂ (fastRKeyProg (fl.pBase, u_val))
            set curRole := (Memory.spec 0).clientResult s₂ (fastReadMetaProg (fl.pBase, 3))
            obtain ⟨hr₃, _, hp₃, _⟩ :=
              fss_fastBufInsert (keepN := false) curRole (rk, (pr.2.1, cnt)) hup hsb s₂ hr₂
            set s₃ := (Memory.spec 0).clientState s₂
              (fastBufInsertProg ((fl.pBase, curRole), (rk, (pr.2.1, cnt))))
            obtain ⟨_, _, hp₄, _⟩ := fss_advanceSubEpoch (keepN := false) hup hsb s₃ hr₃
            have hp_post := hiQuotPres_trans hp₃ hp₄
            have hmb₂ : s₂.mem fl.io.pgL.metaBase = s.mem fl.io.pgL.metaBase :=
              hp₂.1.trans hmb₁
            rcases hp_post.2 (s.mem (fl.metaBase + 1)) (by omega) hlt with heq | hlt₄
            · rw [heq]; exact hself
            · exact hlt₄
    · rw [ite_eq_right hm0] at hgt ⊢
      exact (fss_fastFallbackInsert u_val v_val).2 hup hsb s hr hgt hsp hlt

private theorem fss_largeEpochDelete {w : ℕ} {fl : FastEpochLayout} (u_val : ℕ) :
    FastSplitSafe false w fl (largeEpochDeleteProg (fl.pBase, u_val)) := by
  unfold largeEpochDeleteProg fastDeleteProg
  refine fss_bind (fss_ro (clientState_fastReadMetaProg _)) fun _ => ?_
  refine fss_ite (fun _ => ?_) (fun _ => fss_fastFallbackDelete u_val)
  refine fss_bind (fss_ro (clientState_fastProbeProg _)) fun _ => ?_
  exact fss_ite (fun _ => fss_pure ()) (fun _ => fss_fastRemoveAt _ _ _)

/-- `epochInsertProg` preserves the split cursor `fl.io.pgL.metaBase` in unpaged `SplitPair` mode
(`fl.io.usePaged = 0 ∧ fl.io.sideBit ≠ 0`). -/
theorem epochInsertProg_preserves_split_cursor_large {fl : FastEpochLayout} {w : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s)
    (hup : fl.io.usePaged = 0) (hsb : fl.io.sideBit ≠ 0) (u_val v_val : ℕ) :
    ((Memory.spec 0).clientState s (epochInsertProg ((fl.pBase, u_val), v_val))).mem
      fl.io.pgL.metaBase = s.mem fl.io.pgL.metaBase := by
  have hT_pos : 0 < whpThreshold fl.c := Nat.two_pow_pos (bMinWhp fl.c)
  have hN_pos : 0 < fl.N := lt_of_lt_of_le hT_pos hr.1.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hr.2.1 0 (by decide)
  have hstep : (Memory.spec 0).clientState s (epochInsertProg ((fl.pBase, u_val), v_val)) =
      (Memory.spec 0).clientState s (largeEpochInsertProg ((fl.pBase, u_val), v_val)) := by
    unfold epochInsertProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hm0, ite_eq_right hN_pos.ne']
  rw [hstep]
  exact ((fss_largeEpochInsert u_val v_val).1 hup hsb s hr).2.1 fl.io.pgL.metaBase
    (fun h => h.2 rfl)

/-- `epochDeleteProg` preserves the split cursor `fl.io.pgL.metaBase` in unpaged `SplitPair` mode
(`fl.io.usePaged = 0 ∧ fl.io.sideBit ≠ 0`). -/
theorem epochDeleteProg_preserves_split_cursor_large {fl : FastEpochLayout} {w : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s)
    (hup : fl.io.usePaged = 0) (hsb : fl.io.sideBit ≠ 0) (u_val : ℕ) :
    ((Memory.spec 0).clientState s (epochDeleteProg (fl.pBase, u_val))).mem
      fl.io.pgL.metaBase = s.mem fl.io.pgL.metaBase := by
  have hT_pos : 0 < whpThreshold fl.c := Nat.two_pow_pos (bMinWhp fl.c)
  have hN_pos : 0 < fl.N := lt_of_lt_of_le hT_pos hr.1.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hr.2.1 0 (by decide)
  have hstep : (Memory.spec 0).clientState s (epochDeleteProg (fl.pBase, u_val)) =
      (Memory.spec 0).clientState s (largeEpochDeleteProg (fl.pBase, u_val)) := by
    unfold epochDeleteProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hm0, ite_eq_right hN_pos.ne']
  rw [hstep]
  exact (fss_largeEpochDelete u_val hup hsb s hr).2.1 fl.io.pgL.metaBase (fun h => h.2 rfl)

/-- `epochInsertProg` preserves `SplitHiQuotBounded` in the large regime (`whpThreshold c ≤ N`). -/
theorem epochInsertProg_preserves_hiQuot_large {fl : FastEpochLayout} {w u_val v_val : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s)
    (hup : fl.io.usePaged = 0) (hsb : fl.io.sideBit ≠ 0)
    (hns' : ((Memory.spec 0).clientState s (epochInsertProg ((fl.pBase, u_val), v_val))).mem
        (fl.metaBase + 1) ≤ s.mem (fl.metaBase + 1) + 1 ∧
      ((Memory.spec 0).clientState s (epochInsertProg ((fl.pBase, u_val), v_val))).mem
        (fl.metaBase + 1) ≤ fl.io.pgL.nCap)
    (hhi : SplitHiQuotBounded fl.io (s.mem (fl.metaBase + 1)) s.mem) :
    let s' := (Memory.spec 0).clientState s (epochInsertProg ((fl.pBase, u_val), v_val))
    SplitHiQuotBounded fl.io (s'.mem (fl.metaBase + 1)) s'.mem := by
  dsimp only
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hr.1.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hr.2.1 0 (by decide)
  have hstep : (Memory.spec 0).clientState s (epochInsertProg ((fl.pBase, u_val), v_val)) =
      (Memory.spec 0).clientState s (largeEpochInsertProg ((fl.pBase, u_val), v_val)) := by
    unfold epochInsertProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hm0, ite_eq_right hN_pos.ne']
  obtain ⟨hns_le1, hns_cap⟩ := hns'
  rw [hstep] at hns_le1 hns_cap ⊢
  obtain ⟨_, _, hp, _⟩ := (fss_largeEpochInsert u_val v_val).1 hup hsb s hr
  set s' := (Memory.spec 0).clientState s (largeEpochInsertProg ((fl.pBase, u_val), v_val))
  intro idx hsp hidx
  have hmb' : s'.mem fl.io.pgL.metaBase = s.mem fl.io.pgL.metaBase := hp.1
  have hsp₀ : s.mem fl.io.pgL.metaBase ≤ idx := by omega
  have hidx_cap : idx < fl.io.pgL.nCap := hidx.trans_le hns_cap
  by_cases hlt_old : idx < s.mem (fl.metaBase + 1)
  · rcases hp.2 idx hsp₀ hidx_cap with heq | hlt₂
    · rw [heq]; exact hhi idx hsp₀ hlt_old
    · exact hlt₂
  · have heq_idx : idx = s.mem (fl.metaBase + 1) := by omega
    subst heq_idx
    exact (fss_largeEpochInsert u_val v_val).2 hup hsb s hr hidx hsp₀ hidx_cap

/-- `epochDeleteProg` preserves `SplitHiQuotBounded` in the large regime (`whpThreshold c ≤ N`). -/
theorem epochDeleteProg_preserves_hiQuot_large {fl : FastEpochLayout} {w u_val : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s)
    (hup : fl.io.usePaged = 0) (hsb : fl.io.sideBit ≠ 0)
    (hns' : ((Memory.spec 0).clientState s (epochDeleteProg (fl.pBase, u_val))).mem
        (fl.metaBase + 1) ≤ s.mem (fl.metaBase + 1) ∧
      ((Memory.spec 0).clientState s (epochDeleteProg (fl.pBase, u_val))).mem
        (fl.metaBase + 1) ≤ fl.io.pgL.nCap)
    (hhi : SplitHiQuotBounded fl.io (s.mem (fl.metaBase + 1)) s.mem) :
    let s' := (Memory.spec 0).clientState s (epochDeleteProg (fl.pBase, u_val))
    SplitHiQuotBounded fl.io (s'.mem (fl.metaBase + 1)) s'.mem := by
  dsimp only
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hr.1.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hr.2.1 0 (by decide)
  have hstep : (Memory.spec 0).clientState s (epochDeleteProg (fl.pBase, u_val)) =
      (Memory.spec 0).clientState s (largeEpochDeleteProg (fl.pBase, u_val)) := by
    unfold epochDeleteProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hm0, ite_eq_right hN_pos.ne']
  obtain ⟨hns_le, hns_cap⟩ := hns'
  rw [hstep] at hns_le hns_cap ⊢
  obtain ⟨_, _, hp, _⟩ := fss_largeEpochDelete u_val hup hsb s hr
  exact hiQuotPres_preserves_bounded hp hhi hns_le hns_cap

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
