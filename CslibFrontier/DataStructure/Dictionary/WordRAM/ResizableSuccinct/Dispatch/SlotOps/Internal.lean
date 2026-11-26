/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps.Env

/-!
# Internal Helpers for Compacted Slot Resolution and `GlobalMeta` Pool Updates

Shared internal bounds, `CompGmFrame` combinators, `writeCompGMGenProg` bind helpers, and moved-slab
invariants used privately across `Dispatch.SlotOps` submodules (never re-exported by
`CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

/-- Every entry read via `compGmAt` fits in `globalPtrBits N` bits. -/
theorem compGmAt_lt (metaBase U w N : ℕ) (mem : ℕ → ℕ) (idx : ℕ) :
    compGmAt metaBase U w N mem idx < 2 ^ globalPtrBits N := by
  unfold compGmAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Shared index and value bounds for reading a bucket's tail pointer at logical offset
`j ≥ gm (gmQIdx b) * slabSize N`. -/
theorem tailPtr_read_bounds {U w N metaBase b j : ℕ} {s : Memory.State}
    (hN : 0 < N) (hb_pos : 0 < bucketBits N) (hb : b < numBuckets N)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hj_bc : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hj_not_slab : ¬(j < compGmAt metaBase U w N s.mem (gmQIdx b) * slabSize N)) :
    let gm := compGmAt metaBase U w N s.mem
    let ptr_idx := gmTailPtrBase N + (b * tailCapPerBucket N + (j - gm (gmQIdx b) * slabSize N))
    ptr_idx < globalMetaLen N ∧ gm ptr_idx ≤ N - 1 := by
  intro gm ptr_idx
  obtain ⟨hr_lt, hr_cap⟩ := hslot.tailOffset_lt hb_pos hb hj_bc hj_not_slab
  have hptr_lt : ptr_idx < globalMetaLen N := gmTailPtrIdx_lt hb_pos hb hr_cap
  have ht_lt := (hslot.multi_tail hb_pos).ptr_lt b hb _ hr_lt
  have ht_lt' : gm ptr_idx < gm 1 := by
    simpa only [ptr_idx, gm, gmTailPtrIdx, gmTailPtrFlatIdx, Nat.add_assoc,
      ← (hslot.multi_tail hb_pos).ntails_eq] using ht_lt
  have hSN := hslot.multi_total_le hb_pos
  exact ⟨hptr_lt, by dsimp only [gm, ptr_idx] at *; omega⟩

theorem CompGmFrame.refl {metaBase itemBase U V w N m_items : ℕ} (s : Memory.State) :
    CompGmFrame metaBase itemBase U V w N m_items s s :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CompGmFrame.trans {metaBase itemBase U V w N m_items : ℕ} {s₁ s₂ s₃ : Memory.State}
    (h₁ : CompGmFrame metaBase itemBase U V w N m_items s₁ s₂)
    (h₂ : CompGmFrame metaBase itemBase U V w N m_items s₂ s₃) :
    CompGmFrame metaBase itemBase U V w N m_items s₁ s₃ :=
  ⟨h₂.frontier_eq.trans h₁.frontier_eq,
    fun a ha => (h₂.outside_eq a ha).trans (h₁.outside_eq a ha),
    h₂.lm_eq.trans h₁.lm_eq, h₂.td_eq.trans h₁.td_eq, h₂.dt_eq.trans h₁.dt_eq,
    h₂.quot_eq.trans h₁.quot_eq, h₂.val_eq.trans h₁.val_eq⟩

theorem compGmFrame_writeCompGM_ite {metaBase itemBase U V w N m_items idx val : ℕ}
    (P : Prop) [Decidable P] (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hidx : P → idx < globalMetaLen N) (hval : P → val < 2 ^ globalPtrBits N) (s : Memory.State) :
    let prog : Memory.Prog Unit :=
      if P then writeCompGMGenProg (((mkCompParams U V w N, metaBase), idx), val) else pure ()
    let s' := (Memory.spec 0).clientState s prog
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem =
      if P then Function.update (compGmAt metaBase U w N s.mem) idx val
      else compGmAt metaBase U w N s.mem := by
  split_ifs with hP
  · exact compGmFrame_writeCompGMGenProg hw hitem (hidx hP) (hval hP) s
  · exact ⟨CompGmFrame.refl s, rfl⟩

theorem validProg_writeCompGM_bind {α : Type} {w : ℕ}
    {d : ((CompParams × ℕ) × ℕ) × ℕ} {s : Memory.State} {k : Unit → Memory.Prog α}
    (hd : WriteCompGMPre w d s)
    (hk : ∀ s' : Memory.State, s'.frontier = s.frontier → ValidProg w 0 s' (k ())) :
    ValidProg w 0 s (writeCompGMGenProg d >>= k) := by
  refine validProg_bind (validProg_writeCompGMGen hd) (hk _ ?_)
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩
  obtain ⟨⟨U, V, N, _, _, _, _, _, rfl, _⟩, _⟩ := hd
  rw [clientState_writeCompGMGenProg]

theorem validProg_writeCompGM_ite_bind {α : Type} (P : Prop) [Decidable P] {w : ℕ}
    {d : ((CompParams × ℕ) × ℕ) × ℕ} {s : Memory.State} {k : Unit → Memory.Prog α}
    (hd : P → WriteCompGMPre w d s)
    (hk : ∀ s' : Memory.State, s'.frontier = s.frontier → ValidProg w 0 s' (k ())) :
    ValidProg w 0 s ((if P then writeCompGMGenProg d else pure ()) >>= k) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact validProg_writeCompGM_bind (hd hP) hk
  · rw [ite_eq_right hP, pure_bind]; exact hk s rfl

/-- Pure bounds invariant on global metadata lookup `gm` for moving `p_last` into `p_del`. -/
@[expose] def PureMovedSlabInv (N : ℕ) (gm : ℕ → ℕ) (p_del p_last : ℕ) : Prop :=
  let b_last := gm (gmSlabOwnerBIdx N p_last)
  let s_last := gm (gmSlabOwnerSIdx N p_last)
  let bel_last := gm (gmSlabBelowIdx N p_last)
  let abv_last := gm (gmSlabAboveIdx N p_last)
  let q_last := gm (gmQIdx b_last)
  p_del < maxFullSlabs N ∧
  p_last < maxFullSlabs N ∧
  b_last < numBuckets N ∧
  s_last + 1 ≤ N ∧
  (0 < s_last → bel_last < maxFullSlabs N) ∧
  (s_last + 1 < q_last → abv_last < maxFullSlabs N) ∧
  0 < bucketBits N

/-- Machine-state precondition bundling parameter constraints with `PureMovedSlabInv`. -/
@[expose] def CompGmMovedSlabPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), p_del), p_last), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      PureMovedSlabInv N (compGmAt metaBase U w N s.mem) p_del p_last

theorem pureMovedSlabInv_congr {N p_del p₁ p₂ : ℕ} {gm₁ gm₂ : ℕ → ℕ}
    (hgm : gm₁ = gm₂) (hp : p₁ = p₂) (hm : PureMovedSlabInv N gm₁ p_del p₁) :
    PureMovedSlabInv N gm₂ p_del p₂ := by
  subst hgm hp; exact hm

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
