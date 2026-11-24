/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.IncrementalRebuild
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pure Deamortized `M`-Bucket Block-Pool State Machine (`LargeBlockPoolState`)

This module develops the pure mathematical state machine `BlockPoolState` for the deamortized
`O(1)` per-bucket slab/tail allocator of a large hashed epoch in the SOSA 2024 resizable succinct
dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]).

Each bucket `b < M` owns a contiguous logical array `[0, bktCount b)` (`bktCount b = q b * K + r b`
with slab size `K = L ^ 2`), mapped bijectively onto the dense epoch slot prefix `[0, nSide)` via
`(toPhys, ownerOf)`. Background slab promotions (`Promote`, triggered at `r b ≥ 5 * K`), slab
demotions (`Demote`, triggered at `2 * r b ≤ 7 * K`), and top-boundary block evacuations
(`TopClean` / `TopSwap`) emit explicit `List PhysSwap` swap traces that **preserve every bucket's
logical `loc` coordinates** (`0` intra-bucket index updates during background rebalancing).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.BlockPoolState`: pure allocator
  state (`M`, `K`, `maxSlabs`, `nSide`, per-bucket slabs & tail rings, unreserved/tail-block stacks,
  and `TopSwap` state).
* `BlockPoolState.toPhys`, `BlockPoolState.ownerOf`: `O(1)` two-sided bijection between
  `{(b, loc) | b < M ∧ loc < bktCount b}` and `[0, nSide)`.
* `BlockPoolState.CoreValid`: structural bijection invariant over `[0, nSide)`.
* `BlockPoolState.swapTailCoords`, `BlockPoolState.actStepOne`, `BlockPoolState.maybeStartBktJob`,
  `BlockPoolState.topSwapStepOne`, `BlockPoolState.topCleanOne`: `O(1)` rebalancing primitives.

## Main results

* `BlockPoolState.CoreValid.ownerOf_toPhys`, `BlockPoolState.CoreValid.ownerOf_bounds_and_toPhys`:
  two-sided inverse laws.
* `BlockPoolState.CoreValid.sum_r_eq_tail_supply`: exact tail-slot conservation identity
  `∑ b ∈ range M, r b = (unresLen + #Act) * K + nSide % K`.
* `BlockPoolState.CoreValid.swapTailCoords_spec`: `CoreValid` and `toPhys` preservation for
  tail-coordinate swaps.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

open scoped BigOperators

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Finset

/-! ## Section 1: Pure `BlockPoolState` and Two-Sided `(toPhys, ownerOf)` Translation -/

/-- Pure state of the `M`-bucket slab/tail block pool over dense virtual slots `[0, nSide)`. -/
structure BlockPoolState where
  /-- Number of buckets `M ≥ 1`. -/
  M : ℕ
  /-- Slab block size `K ≥ 64`. -/
  K : ℕ
  /-- Per-bucket slab directory capacity `maxSlabs`. -/
  maxSlabs : ℕ
  /-- Total live slots `nSide`. -/
  nSide : ℕ
  /-- Number of `PureSlab`s (`blkTag = 1`) owned by bucket `b`. -/
  q : ℕ → ℕ
  /-- Number of non-`PureSlab` items owned by bucket `b` (`< 6 * K`). -/
  r : ℕ → ℕ
  /-- Circular head index (`< 6 * K`) into `tailRing b`. -/
  head : ℕ → ℕ
  /-- Active job code for bucket `b`: `0` idle; `1 + cur` (`0 ≤ cur < K`) `Promote`;
  `K + cur` (`1 ≤ cur ≤ K`) `Demote`. -/
  actCode : ℕ → ℕ
  /-- Physical block `< B_full` currently undergoing `Promote` or `Demote` for bucket `b`. -/
  actBlk : ℕ → ℕ
  /-- Physical block `< B_full` of bucket `b`'s `vp`-th `PureSlab` (`vp < q b`). -/
  slabOf : ℕ → ℕ → ℕ
  /-- Tail-coordinate directory `tailRing b rk < 8 * M * K` (`b < M`, `rk < 6 * K`). -/
  tailRing : ℕ → ℕ → ℕ
  /-- Physical block tag (`0` `UnreservedTail`, `1` `PureSlab`, `2` `ActiveBlock`). -/
  blkTag : ℕ → ℕ
  /-- First block metadata field (`unresPos` for `tag = 0`, `bkt` for `tag ∈ {1, 2}`). -/
  blkMeta1 : ℕ → ℕ
  /-- Second block metadata field (`tb` for `tag ∈ {0, 2}`, `vp` for `tag = 1`). -/
  blkMeta2 : ℕ → ℕ
  /-- Count of full `UnreservedTail` blocks `< B_full`. -/
  unresLen : ℕ
  /-- Dense stack of full `UnreservedTail` blocks `< B_full` (`i < unresLen`). -/
  unresStack : ℕ → ℕ
  /-- High-water mark (`≤ 8 * M`) of allocated tail-block IDs `tb`. -/
  tbHighWater : ℕ
  /-- Stack pointer (`≤ tbHighWater`) of recycled tail-block IDs. -/
  freeTbTop : ℕ
  /-- Free-list stack of recycled tail-block IDs `< tbHighWater`. -/
  freeTbStack : ℕ → ℕ
  /-- Physical block `P ≤ B_full` currently owning tail-block ID `tb`. -/
  tbPhysBlk : ℕ → ℕ
  /-- Owner bucket `b < M` of tail coordinate `tIdx < 8 * M * K`. -/
  tailOwnerBkt : ℕ → ℕ
  /-- Owner ring slot `rk < 6 * K` of tail coordinate `tIdx < 8 * M * K`. -/
  tailOwnerRing : ℕ → ℕ
  /-- `1` when a top-boundary `PureSlab ↔ UnreservedTail` block swap is active; `0` otherwise. -/
  topSwapAct : ℕ
  /-- Source `PureSlab` block `< B_full` (`blkTag = 1`) of an active `TopSwap`. -/
  topSwapSrc : ℕ
  /-- Destination `UnreservedTail` block `< B_full` (`blkTag = 0`) of an active `TopSwap`. -/
  topSwapDst : ℕ
  /-- Intra-block swap cursor `< K` of an active `TopSwap`. -/
  topSwapCur : ℕ

namespace BlockPoolState

/-- Update a 2-argument table at `(i, j)`. -/
@[expose] def set2 {α : Type*} (f : ℕ → ℕ → α) (i j : ℕ) (v : α) (i' j' : ℕ) : α :=
  if i' = i ∧ j' = j then v else f i' j'

@[simp] theorem set2_self {α : Type*} (f : ℕ → ℕ → α) (i j : ℕ) (v : α) :
    set2 f i j v i j = v := by
  simp [set2]

theorem set2_of_ne {α : Type*} (f : ℕ → ℕ → α) (i j : ℕ) (v : α) (i' j' : ℕ)
    (hne : ¬(i' = i ∧ j' = j)) : set2 f i j v i' j' = f i' j' := by
  simp [set2, hne]

/-- Number of full `K`-item physical blocks `nSide / K`. -/
@[expose] def B_full (bp : BlockPoolState) : ℕ :=
  bp.nSide / bp.K

/-- Partial top-block item count `nSide % K`. -/
@[expose] def rem (bp : BlockPoolState) : ℕ :=
  bp.nSide % bp.K

/-- Total live items `q b * K + r b` in bucket `b`. -/
@[expose] def bktCount (bp : BlockPoolState) (b : ℕ) : ℕ :=
  bp.q b * bp.K + bp.r b

/-- Number of items of `actBlk b` currently classified as `ActPrefix(b, 0 .. actCur b - 1)`. -/
@[expose] def actCur (bp : BlockPoolState) (b : ℕ) : ℕ :=
  if bp.actCode b = 0 then 0
  else if bp.actCode b ≤ bp.K then bp.actCode b - 1
  else bp.actCode b - bp.K

theorem actCur_le_K {bp : BlockPoolState} {b : ℕ} (hc : bp.actCode b ≤ 2 * bp.K) :
    bp.actCur b ≤ bp.K := by
  unfold actCur; split_ifs <;> omega

theorem actCode_ne_zero_of_lt_actCur {bp : BlockPoolState} {b k : ℕ} (hk : k < bp.actCur b) :
    bp.actCode b ≠ 0 := by
  intro hz; unfold actCur at hk; rw [ite_eq_left hz] at hk; exact Nat.not_lt_zero k hk

/-- Effective physical block under an in-progress `TopSwap` involution at offset `off`. -/
@[expose] def effBlk (bp : BlockPoolState) (P off : ℕ) : ℕ :=
  if bp.topSwapAct = 1 ∧ off < bp.topSwapCur then
    if P = bp.topSwapSrc then bp.topSwapDst
    else if P = bp.topSwapDst then bp.topSwapSrc
    else P
  else P

@[simp] theorem effBlk_involutive (bp : BlockPoolState) (P off : ℕ) :
    bp.effBlk (bp.effBlk P off) off = P := by
  unfold effBlk
  by_cases hc : bp.topSwapAct = 1 ∧ off < bp.topSwapCur
  · simp only [hc, and_self, ↓reduceIte]
    by_cases hs : P = bp.topSwapSrc
    · subst hs; by_cases hd : bp.topSwapDst = bp.topSwapSrc <;> simp [hd]
    · by_cases hd : P = bp.topSwapDst
      · subst hd; simp [hs]
      · simp [hs, hd]
  · simp [hc]

theorem effBlk_eq_self_of_ne {bp : BlockPoolState} {P off : ℕ}
    (hs : P ≠ bp.topSwapSrc) (hd : P ≠ bp.topSwapDst) :
    bp.effBlk P off = P := by
  unfold effBlk; simp [hs, hd]

/-- Physical slot of tail coordinate `tIdx`. -/
@[expose] def physOfTail (bp : BlockPoolState) (tIdx : ℕ) : ℕ :=
  bp.effBlk (bp.tbPhysBlk (tIdx / bp.K)) (tIdx % bp.K) * bp.K + tIdx % bp.K

/-- Forward translation `(b, loc) ↦ p < nSide` (`O(1)` time). -/
@[expose] def toPhys (bp : BlockPoolState) (b loc : ℕ) : ℕ :=
  let K := bp.K
  if loc < bp.q b * K then
    bp.effBlk (bp.slabOf b (loc / K)) (loc % K) * K + loc % K
  else
    let k := loc - bp.q b * K
    if k < bp.actCur b then
      bp.effBlk (bp.actBlk b) k * K + k
    else
      bp.physOfTail (bp.tailRing b ((bp.head b + k) % (6 * K)))

/-- Logical pair `(b', loc')` decoded from tail coordinate `tIdx`. -/
@[expose] def ownerOfTail (bp : BlockPoolState) (tIdx : ℕ) : ℕ × ℕ :=
  let b := bp.tailOwnerBkt tIdx
  let rk := bp.tailOwnerRing tIdx
  (b, bp.q b * bp.K + (rk + 6 * bp.K - bp.head b) % (6 * bp.K))

/-- Inverse translation `p ↦ (b, loc)` (`O(1)` time). -/
@[expose] def ownerOf (bp : BlockPoolState) (p : ℕ) : ℕ × ℕ :=
  let K := bp.K
  let off := p % K
  let P := bp.effBlk (p / K) off
  let tag := bp.blkTag P
  if tag = 1 then
    (bp.blkMeta1 P, bp.blkMeta2 P * K + off)
  else if tag = 2 then
    let b := bp.blkMeta1 P
    if off < bp.actCur b then
      (b, bp.q b * K + off)
    else
      bp.ownerOfTail (bp.blkMeta2 P * K + off)
  else
    bp.ownerOfTail (bp.blkMeta2 P * K + off)

/-- Empty `BlockPoolState` (`nSide = 0`, `tb = 0` assigned to partial top block `0`). -/
@[expose] def empty (M K maxSlabs : ℕ) : BlockPoolState where
  M := M
  K := K
  maxSlabs := maxSlabs
  nSide := 0
  q _ := 0
  r _ := 0
  head _ := 0
  actCode _ := 0
  actBlk _ := 0
  slabOf _ _ := 0
  tailRing _ _ := 0
  blkTag _ := 0
  blkMeta1 _ := 0
  blkMeta2 _ := 0
  unresLen := 0
  unresStack _ := 0
  tbHighWater := 1
  freeTbTop := 0
  freeTbStack _ := 0
  tbPhysBlk _ := 0
  tailOwnerBkt _ := 0
  tailOwnerRing _ := 0
  topSwapAct := 0
  topSwapSrc := 0
  topSwapDst := 0
  topSwapCur := 0

/-! ## Section 2: `CoreValid`, Two-Sided Bijection, and Tail-Slot Conservation -/

/-- Structural validity invariant of `BlockPoolState` establishing the two-sided bijection
`(toPhys, ownerOf)` between `{(b, loc) | b < M ∧ loc < bktCount b}` and `[0, nSide)`. -/
structure CoreValid (bp : BlockPoolState) : Prop where
  M_pos : 1 ≤ bp.M
  K_ge : 64 ≤ bp.K
  bkt_bounds : ∀ b < bp.M,
    bp.q b ≤ bp.maxSlabs ∧ bp.r b < 6 * bp.K ∧ bp.head b < 6 * bp.K ∧
    bp.actCode b ≤ 2 * bp.K ∧ bp.actCur b ≤ bp.r b
  blkTag_lt : ∀ P < bp.B_full, bp.blkTag P < 3
  blkTag_top : bp.blkTag bp.B_full = 0
  unres_fwd : ∀ i < bp.unresLen,
    bp.unresStack i < bp.B_full ∧ bp.blkTag (bp.unresStack i) = 0 ∧
    bp.blkMeta1 (bp.unresStack i) = i
  unres_bwd : ∀ P < bp.B_full, bp.blkTag P = 0 →
    bp.blkMeta1 P < bp.unresLen ∧ bp.unresStack (bp.blkMeta1 P) = P
  slab_fwd : ∀ b < bp.M, ∀ vp < bp.q b,
    bp.slabOf b vp < bp.B_full ∧ bp.blkTag (bp.slabOf b vp) = 1 ∧
    bp.blkMeta1 (bp.slabOf b vp) = b ∧ bp.blkMeta2 (bp.slabOf b vp) = vp
  slab_bwd : ∀ P < bp.B_full, bp.blkTag P = 1 →
    bp.blkMeta1 P < bp.M ∧ bp.blkMeta2 P < bp.q (bp.blkMeta1 P) ∧
    bp.slabOf (bp.blkMeta1 P) (bp.blkMeta2 P) = P
  act_fwd : ∀ b < bp.M, bp.actCode b ≠ 0 →
    bp.actBlk b < bp.B_full ∧ bp.blkTag (bp.actBlk b) = 2 ∧ bp.blkMeta1 (bp.actBlk b) = b
  act_bwd : ∀ P < bp.B_full, bp.blkTag P = 2 →
    bp.blkMeta1 P < bp.M ∧ bp.actCode (bp.blkMeta1 P) ≠ 0 ∧ bp.actBlk (bp.blkMeta1 P) = P
  tb_fwd : ∀ P ≤ bp.B_full, (bp.blkTag P = 0 ∨ bp.blkTag P = 2) →
    bp.blkMeta2 P < bp.tbHighWater ∧ bp.tbPhysBlk (bp.blkMeta2 P) = P
  freeTb_valid : ∀ i < bp.freeTbTop,
    bp.freeTbStack i < bp.tbHighWater ∧
    ∀ P ≤ bp.B_full, (bp.blkTag P = 0 ∨ bp.blkTag P = 2) → bp.blkMeta2 P ≠ bp.freeTbStack i
  freeTb_inj : ∀ i < bp.freeTbTop, ∀ j < bp.freeTbTop,
    bp.freeTbStack i = bp.freeTbStack j → i = j
  tbHighWater_supply : bp.tbHighWater ≤ bp.freeTbTop +
    ((Finset.range (bp.B_full + 1)).filter (fun P => bp.blkTag P = 0 ∨ bp.blkTag P = 2)).card
  tbHighWater_le_max : bp.tbHighWater ≤ 8 * bp.M
  topSwap_act_le : bp.topSwapAct ≤ 1
  topSwap_valid : bp.topSwapAct = 1 →
    bp.topSwapCur < bp.K ∧
    bp.topSwapSrc < bp.B_full ∧
    bp.topSwapDst < bp.B_full ∧ bp.blkTag bp.topSwapDst = 0 ∧
    bp.topSwapSrc ≠ bp.topSwapDst
  tail_fwd : ∀ b < bp.M, ∀ k, bp.actCur b ≤ k → k < bp.r b →
    let rk := (bp.head b + k) % (6 * bp.K)
    let tIdx := bp.tailRing b rk
    let tb := tIdx / bp.K
    let off := tIdx % bp.K
    let P := bp.tbPhysBlk tb
    tIdx < 8 * bp.M * bp.K ∧ P ≤ bp.B_full ∧ bp.blkMeta2 P = tb ∧
    ((bp.blkTag P = 0 ∧ (P < bp.B_full ∨ off < bp.rem)) ∨
      (P < bp.B_full ∧ bp.blkTag P = 2 ∧ bp.actCur (bp.blkMeta1 P) ≤ off)) ∧
    bp.tailOwnerBkt tIdx = b ∧ bp.tailOwnerRing tIdx = rk
  tail_bwd : ∀ P ≤ bp.B_full, ∀ off < bp.K, (P < bp.B_full ∨ off < bp.rem) →
    (bp.blkTag P = 0 ∨ (bp.blkTag P = 2 ∧ bp.actCur (bp.blkMeta1 P) ≤ off)) →
    let tIdx := bp.blkMeta2 P * bp.K + off
    let b := bp.tailOwnerBkt tIdx
    let rk := bp.tailOwnerRing tIdx
    let k := (rk + 6 * bp.K - bp.head b) % (6 * bp.K)
    b < bp.M ∧ rk < 6 * bp.K ∧ bp.actCur b ≤ k ∧ k < bp.r b ∧ bp.tailRing b rk = tIdx

theorem CoreValid.K_pos {bp : BlockPoolState} (hv : bp.CoreValid) : 0 < bp.K :=
  Nat.lt_of_lt_of_le (by decide) hv.K_ge

theorem CoreValid.nSide_eq {bp : BlockPoolState} (_hv : bp.CoreValid) :
    bp.B_full * bp.K + bp.rem = bp.nSide := by
  unfold B_full rem
  rw [Nat.mul_comm, Nat.div_add_mod]

theorem empty_coreValid {M K maxSlabs : ℕ} (hM : 1 ≤ M) (hK : 64 ≤ K) :
    (empty M K maxSlabs).CoreValid where
  M_pos := hM
  K_ge := hK
  bkt_bounds := fun _ _ => ⟨Nat.zero_le _, by dsimp [empty]; omega, by dsimp [empty]; omega,
    Nat.zero_le _, le_rfl⟩
  blkTag_lt := fun _ hP => by simp [empty, B_full] at hP
  blkTag_top := rfl
  unres_fwd := fun _ hi => absurd hi (Nat.not_lt_zero _)
  unres_bwd := fun _ hP => by simp [empty, B_full] at hP
  slab_fwd := fun _ _ _ hvp => absurd hvp (Nat.not_lt_zero _)
  slab_bwd := fun _ hP => by simp [empty, B_full] at hP
  act_fwd := fun _ _ hne => absurd rfl hne
  act_bwd := fun _ hP => by simp [empty, B_full] at hP
  tb_fwd := fun P hP _ => by
    have hP0 : P = 0 := by simp [empty, B_full] at hP; omega
    subst hP0; exact ⟨Nat.zero_lt_one, rfl⟩
  freeTb_valid := fun _ hi => absurd hi (Nat.not_lt_zero _)
  freeTb_inj := fun _ hi => absurd hi (Nat.not_lt_zero _)
  tbHighWater_supply := by simp [empty, B_full]
  tbHighWater_le_max := by dsimp [empty]; omega
  topSwap_act_le := Nat.zero_le 1
  topSwap_valid := fun h => by simp [empty] at h
  tail_fwd := fun _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)
  tail_bwd := fun P hP off _ hlt _ => by
    simp [empty, B_full, rem] at hlt

theorem CoreValid.effBlk_lt_B_full {bp : BlockPoolState} (hv : bp.CoreValid)
    {P : ℕ} (hP : P < bp.B_full) (off : ℕ) :
    bp.effBlk P off < bp.B_full := by
  unfold effBlk
  by_cases hc : bp.topSwapAct = 1 ∧ off < bp.topSwapCur
  · obtain ⟨_, hsrc, hdst, _, _⟩ := hv.topSwap_valid hc.1
    simp only [hc, and_self, ↓reduceIte]
    split_ifs <;> assumption
  · simp only [hc, ↓reduceIte]; exact hP

theorem CoreValid.effBlk_B_full {bp : BlockPoolState} (hv : bp.CoreValid) (off : ℕ) :
    bp.effBlk bp.B_full off = bp.B_full := by
  unfold effBlk
  by_cases hc : bp.topSwapAct = 1 ∧ off < bp.topSwapCur
  · obtain ⟨_, hsrc, hdst, _, _⟩ := hv.topSwap_valid hc.1
    have hne1 : bp.B_full ≠ bp.topSwapSrc := (ne_of_lt hsrc).symm
    have hne2 : bp.B_full ≠ bp.topSwapDst := (ne_of_lt hdst).symm
    simp [hc, hne1, hne2]
  · simp [hc]

private theorem add_sub_head_mod {K hd k : ℕ} (hK : 0 < K) (hhd : hd < 6 * K) (hk : k < 6 * K) :
    ((hd + k) % (6 * K) + 6 * K - hd) % (6 * K) = k := by
  have h6 : 0 < 6 * K := by omega
  by_cases hlt : hd + k < 6 * K
  · rw [Nat.mod_eq_of_lt hlt, show hd + k + 6 * K - hd = 6 * K + k by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hk]
  · have hmod : (hd + k) % (6 * K) = hd + k - 6 * K := by
      conv_lhs => rw [show hd + k = 6 * K + (hd + k - 6 * K) by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, show hd + k - 6 * K + 6 * K - hd = k by omega, Nat.mod_eq_of_lt hk]

private theorem head_add_sub_mod {K hd rk : ℕ} (hhd : hd < 6 * K) (hrk : rk < 6 * K) :
    (hd + (rk + 6 * K - hd) % (6 * K)) % (6 * K) = rk := by
  by_cases hle : hd ≤ rk
  · have hlt_sub : rk - hd < 6 * K := by omega
    rw [show rk + 6 * K - hd = 6 * K + (rk - hd) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt hlt_sub, show hd + (rk - hd) = rk by omega, Nat.mod_eq_of_lt hrk]
  · have hlt_sub : rk + 6 * K - hd < 6 * K := by omega
    rw [Nat.mod_eq_of_lt hlt_sub,
      show hd + (rk + 6 * K - hd) = 6 * K + rk by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt hrk]

private theorem mul_add_lt_of_lt {B K P off : ℕ} (hP : P < B) (hoff : off < K) :
    P * K + off < B * K := by
  have hle : (P + 1) * K ≤ B * K := Nat.mul_le_mul_right K hP
  rw [Nat.add_one_mul] at hle; omega

theorem CoreValid.toPhys_lt {bp : BlockPoolState} (hv : bp.CoreValid)
    {b loc : ℕ} (hb : b < bp.M) (hloc : loc < bp.bktCount b) :
    bp.toPhys b loc < bp.nSide := by
  have hK := hv.K_pos
  have hn := hv.nSide_eq
  obtain ⟨_, hr_lt, _, _, _⟩ := hv.bkt_bounds b hb
  unfold toPhys
  dsimp only
  by_cases hslab : loc < bp.q b * bp.K
  · rw [ite_eq_left hslab]
    have hvp : loc / bp.K < bp.q b := (Nat.div_lt_iff_lt_mul hK).mpr hslab
    obtain ⟨hP, _, _, _⟩ := hv.slab_fwd b hb (loc / bp.K) hvp
    have heff := hv.effBlk_lt_B_full hP (loc % bp.K)
    exact (mul_add_lt_of_lt heff (Nat.mod_lt loc hK)).trans_le (by omega)
  · rw [ite_eq_right hslab]
    set k := loc - bp.q b * bp.K
    have hk_lt_r : k < bp.r b := by unfold bktCount at hloc; omega
    by_cases hact : k < bp.actCur b
    · rw [ite_eq_left hact]
      obtain ⟨_, _, _, hc_le, _⟩ := hv.bkt_bounds b hb
      have hk_lt_K : k < bp.K := hact.trans_le (actCur_le_K hc_le)
      obtain ⟨hP, _, _⟩ := hv.act_fwd b hb (actCode_ne_zero_of_lt_actCur hact)
      exact (mul_add_lt_of_lt (hv.effBlk_lt_B_full hP k) hk_lt_K).trans_le (by omega)
    · rw [ite_eq_right hact]
      have hk_ge : bp.actCur b ≤ k := Nat.le_of_not_lt hact
      have htf := hv.tail_fwd b hb k hk_ge hk_lt_r
      dsimp only at htf
      set rk := (bp.head b + k) % (6 * bp.K)
      set tIdx := bp.tailRing b rk
      obtain ⟨_, hP_le, _, hkind, _, _⟩ := htf
      have hoff_lt : tIdx % bp.K < bp.K := Nat.mod_lt tIdx hK
      unfold physOfTail
      rcases hkind with ⟨_, hlt_or⟩ | ⟨hP_lt, _, _⟩
      · by_cases hP_lt : bp.tbPhysBlk (tIdx / bp.K) < bp.B_full
        · exact (mul_add_lt_of_lt (hv.effBlk_lt_B_full hP_lt _) hoff_lt).trans_le
            (by linarith)
        · have hoff_rem : tIdx % bp.K < bp.rem := hlt_or.resolve_left hP_lt
          have hP_eq : bp.tbPhysBlk (tIdx / bp.K) = bp.B_full := by omega
          rw [hP_eq, hv.effBlk_B_full]
          linarith
      · exact (mul_add_lt_of_lt (hv.effBlk_lt_B_full hP_lt _) hoff_lt).trans_le
          (by linarith)

theorem CoreValid.ownerOf_toPhys {bp : BlockPoolState} (hv : bp.CoreValid)
    {b loc : ℕ} (hb : b < bp.M) (hloc : loc < bp.bktCount b) :
    bp.ownerOf (bp.toPhys b loc) = (b, loc) := by
  have hK := hv.K_pos
  obtain ⟨_, hr_lt, hhd_lt, hc_le, _⟩ := hv.bkt_bounds b hb
  have div_mod_blk : ∀ (E off : ℕ), off < bp.K →
      (E * bp.K + off) / bp.K = E ∧ (E * bp.K + off) % bp.K = off := fun E off hoff => by
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
  by_cases hslab : loc < bp.q b * bp.K
  · have htp : bp.toPhys b loc =
        bp.effBlk (bp.slabOf b (loc / bp.K)) (loc % bp.K) * bp.K + loc % bp.K := by
      unfold toPhys; dsimp only; rw [ite_eq_left hslab]
    rw [htp]
    unfold ownerOf; dsimp only
    have hvp : loc / bp.K < bp.q b := (Nat.div_lt_iff_lt_mul hK).mpr hslab
    have hoff : loc % bp.K < bp.K := Nat.mod_lt loc hK
    obtain ⟨_, htag, hm1, hm2⟩ := hv.slab_fwd b hb (loc / bp.K) hvp
    obtain ⟨hdiv, hmod⟩ := div_mod_blk (bp.effBlk (bp.slabOf b (loc / bp.K)) (loc % bp.K))
      (loc % bp.K) hoff
    rw [hdiv, hmod, effBlk_involutive, htag]
    simp only [↓reduceIte, hm1, hm2]
    exact Prod.ext rfl (by have := Nat.div_add_mod loc bp.K; linarith)
  · set k := loc - bp.q b * bp.K
    have hk_lt_r : k < bp.r b := by unfold bktCount at hloc; omega
    have hloc_eq : bp.q b * bp.K + k = loc := by dsimp only [k]; omega
    by_cases hact : k < bp.actCur b
    · have htp : bp.toPhys b loc = bp.effBlk (bp.actBlk b) k * bp.K + k := by
        unfold toPhys; dsimp only; rw [ite_eq_right hslab, ite_eq_left hact]
      rw [htp]
      unfold ownerOf; dsimp only
      have hk_lt_K : k < bp.K := hact.trans_le (actCur_le_K hc_le)
      obtain ⟨_, htag, hm1⟩ := hv.act_fwd b hb (actCode_ne_zero_of_lt_actCur hact)
      obtain ⟨hdiv, hmod⟩ := div_mod_blk (bp.effBlk (bp.actBlk b) k) k hk_lt_K
      rw [hdiv, hmod, effBlk_involutive, htag]
      simp only [Nat.reduceEqDiff, ↓reduceIte, hm1, hact, hloc_eq]
    · have hk_ge : bp.actCur b ≤ k := Nat.le_of_not_lt hact
      set rk := (bp.head b + k) % (6 * bp.K)
      set tIdx := bp.tailRing b rk
      set P := bp.tbPhysBlk (tIdx / bp.K)
      have htp : bp.toPhys b loc = bp.effBlk P (tIdx % bp.K) * bp.K + tIdx % bp.K := by
        unfold toPhys physOfTail; dsimp only; rw [ite_eq_right hslab, ite_eq_right hact]
      rw [htp]
      unfold ownerOf; dsimp only
      have htf := hv.tail_fwd b hb k hk_ge hk_lt_r
      dsimp only at htf
      obtain ⟨_, _, hm2, hkind, hob, hor⟩ := htf
      have hoff : tIdx % bp.K < bp.K := Nat.mod_lt tIdx hK
      obtain ⟨hdiv, hmod⟩ := div_mod_blk (bp.effBlk P (tIdx % bp.K)) (tIdx % bp.K) hoff
      rw [hdiv, hmod, effBlk_involutive]
      have ht_re : bp.blkMeta2 P * bp.K + tIdx % bp.K = tIdx := by
        rw [hm2, Nat.mul_comm, Nat.div_add_mod]
      have htail_ans : bp.ownerOfTail (bp.blkMeta2 P * bp.K + tIdx % bp.K) = (b, loc) := by
        rw [ht_re]; unfold ownerOfTail; dsimp only
        rw [hob, hor, add_sub_head_mod hK hhd_lt (hk_lt_r.trans hr_lt), hloc_eq]
      rcases hkind with ⟨htag0, _⟩ | ⟨_, htag2, hge_cur⟩
      · rw [htag0]; simp only [Nat.zero_ne_one, OfNat.zero_ne_ofNat, ↓reduceIte]; exact htail_ans
      · rw [htag2]; simp only [Nat.reduceEqDiff, ↓reduceIte]
        rw [ite_eq_right (not_lt.mpr hge_cur)]
        exact htail_ans

theorem CoreValid.ownerOf_bounds_and_toPhys {bp : BlockPoolState} (hv : bp.CoreValid)
    {p : ℕ} (hp : p < bp.nSide) :
    (bp.ownerOf p).1 < bp.M ∧
    (bp.ownerOf p).2 < bp.bktCount (bp.ownerOf p).1 ∧
    bp.toPhys (bp.ownerOf p).1 (bp.ownerOf p).2 = p := by
  have hK := hv.K_pos
  have hn := hv.nSide_eq
  set off := p % bp.K
  have hoff : off < bp.K := Nat.mod_lt p hK
  have hp_re : (p / bp.K) * bp.K + off = p := by
    dsimp only [off]; rw [Nat.mul_comm, Nat.div_add_mod]
  have hdiv_le : p / bp.K ≤ bp.B_full ∧
      (p / bp.K < bp.B_full ∨ (p / bp.K = bp.B_full ∧ off < bp.rem)) := by
    by_cases hlt : p < bp.B_full * bp.K
    · exact ⟨((Nat.div_lt_iff_lt_mul hK).mpr hlt).le,
        Or.inl ((Nat.div_lt_iff_lt_mul hK).mpr hlt)⟩
    · have hge : bp.B_full ≤ p / bp.K := (Nat.le_div_iff_mul_le hK).mpr (by omega)
      have hrem_lt : bp.rem < bp.K := Nat.mod_lt bp.nSide hK
      have hhi : p / bp.K < bp.B_full + 1 :=
        (Nat.div_lt_iff_lt_mul hK).mpr (by rw [Nat.add_one_mul]; linarith)
      have heq : p / bp.K = bp.B_full := by omega
      exact ⟨heq.le, Or.inr ⟨heq, by rw [heq] at hp_re; linarith⟩⟩
  set P := bp.effBlk (p / bp.K) off
  have hP_inv : bp.effBlk P off = p / bp.K := effBlk_involutive bp (p / bp.K) off
  have hP_dom : P ≤ bp.B_full ∧ (P < bp.B_full ∨ off < bp.rem) := by
    rcases hdiv_le.2 with hlt | ⟨heq, hrem⟩
    · have h1 := hv.effBlk_lt_B_full hlt off
      exact ⟨h1.le, Or.inl h1⟩
    · have h1 : P = bp.B_full := by dsimp only [P]; rw [heq, hv.effBlk_B_full]
      exact ⟨h1.le, Or.inr hrem⟩
  by_cases htag1 : bp.blkTag P = 1
  · have how_eq : bp.ownerOf p = (bp.blkMeta1 P, bp.blkMeta2 P * bp.K + off) := by
      unfold ownerOf; dsimp only; change (if bp.blkTag P = 1 then _ else _) = _
      rw [ite_eq_left htag1]
    rw [how_eq]
    have hP_lt : P < bp.B_full := by
      by_contra hge
      have heq : P = bp.B_full := by omega
      rw [heq, hv.blkTag_top] at htag1; exact absurd htag1 (by decide)
    obtain ⟨hb, hvp, hslab_eq⟩ := hv.slab_bwd P hP_lt htag1
    set b := bp.blkMeta1 P
    set vp := bp.blkMeta2 P
    have hloc_slab : vp * bp.K + off < bp.q b * bp.K := mul_add_lt_of_lt hvp hoff
    have hloc_cnt : vp * bp.K + off < bp.bktCount b := by unfold bktCount; omega
    refine ⟨hb, hloc_cnt, ?_⟩
    unfold toPhys; dsimp only; rw [ite_eq_left hloc_slab]
    have hdiv_vp : (vp * bp.K + off) / bp.K = vp := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add]
    have hmod_vp : (vp * bp.K + off) % bp.K = off := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
    rw [hdiv_vp, hmod_vp, hslab_eq, hP_inv, hp_re]
  · have prove_tail : (bp.blkTag P = 0 ∨ (bp.blkTag P = 2 ∧ bp.actCur (bp.blkMeta1 P) ≤ off)) →
        (bp.ownerOfTail (bp.blkMeta2 P * bp.K + off)).1 < bp.M ∧
        (bp.ownerOfTail (bp.blkMeta2 P * bp.K + off)).2 <
          bp.bktCount (bp.ownerOfTail (bp.blkMeta2 P * bp.K + off)).1 ∧
        bp.toPhys (bp.ownerOfTail (bp.blkMeta2 P * bp.K + off)).1
          (bp.ownerOfTail (bp.blkMeta2 P * bp.K + off)).2 = p := fun hor => by
      obtain ⟨hb, hrk, hk_ge, hk_lt, htr⟩ := hv.tail_bwd P hP_dom.1 off hoff hP_dom.2 hor
      obtain ⟨_, _, hhd_lt, _, _⟩ := hv.bkt_bounds _ hb
      set tIdx := bp.blkMeta2 P * bp.K + off
      set b := bp.tailOwnerBkt tIdx
      set rk := bp.tailOwnerRing tIdx
      set k := (rk + 6 * bp.K - bp.head b) % (6 * bp.K)
      have howt : bp.ownerOfTail tIdx = (b, bp.q b * bp.K + k) := rfl
      rw [howt]
      refine ⟨hb, by unfold bktCount; linarith, ?_⟩
      unfold toPhys; dsimp only
      have hnot_slab : ¬(bp.q b * bp.K + k < bp.q b * bp.K) := by omega
      have hsub_k : bp.q b * bp.K + k - bp.q b * bp.K = k := Nat.add_sub_cancel_left _ _
      rw [ite_eq_right hnot_slab, hsub_k, ite_eq_right (not_lt.mpr hk_ge)]
      have hrk_re : (bp.head b + k) % (6 * bp.K) = rk := head_add_sub_mod hhd_lt hrk
      rw [hrk_re, htr]
      unfold physOfTail
      have ht_div : tIdx / bp.K = bp.blkMeta2 P := by
        dsimp only [tIdx]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add]
      have ht_mod : tIdx % bp.K = off := by
        dsimp only [tIdx]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
      have htb_P : bp.tbPhysBlk (bp.blkMeta2 P) = P :=
        (hv.tb_fwd P hP_dom.1 (hor.imp id And.left)).2
      rw [ht_div, ht_mod, htb_P, hP_inv, hp_re]
    by_cases htag2 : bp.blkTag P = 2
    · by_cases hlt_cur : off < bp.actCur (bp.blkMeta1 P)
      · have how_eq : bp.ownerOf p = (bp.blkMeta1 P, bp.q (bp.blkMeta1 P) * bp.K + off) := by
          unfold ownerOf; dsimp only
          change (if bp.blkTag P = 1 then _ else if bp.blkTag P = 2 then _ else _) = _
          rw [ite_eq_right htag1, ite_eq_left htag2, ite_eq_left hlt_cur]
        rw [how_eq]
        have hP_lt : P < bp.B_full := by
          by_contra hge
          have heq : P = bp.B_full := by omega
          rw [heq, hv.blkTag_top] at htag2; exact absurd htag2 (by decide)
        obtain ⟨hb, _, hact_eq⟩ := hv.act_bwd P hP_lt htag2
        obtain ⟨_, _, _, _, hcur_le_r⟩ := hv.bkt_bounds (bp.blkMeta1 P) hb
        set b := bp.blkMeta1 P
        refine ⟨hb, by unfold bktCount; linarith, ?_⟩
        unfold toPhys; dsimp only
        have hnot_slab : ¬(bp.q b * bp.K + off < bp.q b * bp.K) := by omega
        have hsub : bp.q b * bp.K + off - bp.q b * bp.K = off := Nat.add_sub_cancel_left _ _
        rw [ite_eq_right hnot_slab, hsub, ite_eq_left hlt_cur, hact_eq, hP_inv, hp_re]
      · have how_eq : bp.ownerOf p = bp.ownerOfTail (bp.blkMeta2 P * bp.K + off) := by
          unfold ownerOf; dsimp only
          change (if bp.blkTag P = 1 then _ else if bp.blkTag P = 2 then _ else _) = _
          rw [ite_eq_right htag1, ite_eq_left htag2, ite_eq_right hlt_cur]
        rw [how_eq]
        exact prove_tail (Or.inr ⟨htag2, Nat.le_of_not_lt hlt_cur⟩)
    · have how_eq : bp.ownerOf p = bp.ownerOfTail (bp.blkMeta2 P * bp.K + off) := by
        unfold ownerOf; dsimp only
        change (if bp.blkTag P = 1 then _ else if bp.blkTag P = 2 then _ else _) = _
        rw [ite_eq_right htag1, ite_eq_right htag2]
      rw [how_eq]
      have htag0 : bp.blkTag P = 0 := by
        by_cases hlt : P < bp.B_full
        · have := hv.blkTag_lt P hlt; omega
        · have heq : P = bp.B_full := by omega
          rw [heq]; exact hv.blkTag_top
      exact prove_tail (Or.inl htag0)

theorem CoreValid.toPhys_inj {bp : BlockPoolState} (hv : bp.CoreValid)
    {b₁ loc₁ b₂ loc₂ : ℕ} (hb₁ : b₁ < bp.M) (hl₁ : loc₁ < bp.bktCount b₁)
    (hb₂ : b₂ < bp.M) (hl₂ : loc₂ < bp.bktCount b₂)
    (heq : bp.toPhys b₁ loc₁ = bp.toPhys b₂ loc₂) :
    b₁ = b₂ ∧ loc₁ = loc₂ := by
  have h1 := hv.ownerOf_toPhys hb₁ hl₁
  have h2 := hv.ownerOf_toPhys hb₂ hl₂
  rw [heq, h2] at h1
  exact Prod.mk.inj h1.symm

/-- Total item count across all `M` buckets equals `nSide`. -/
theorem CoreValid.sum_bktCount_eq_nSide {bp : BlockPoolState} (hv : bp.CoreValid) :
    ∑ b ∈ Finset.range bp.M, bp.bktCount b = bp.nSide := by
  have hcard : ((Finset.range bp.M).sigma (fun b => Finset.range (bp.bktCount b))).card =
      (Finset.range bp.nSide).card :=
    Finset.card_bij (fun x _ => bp.toPhys x.1 x.2)
      (fun x hx => by
        simp only [mem_sigma, mem_range] at hx ⊢
        exact hv.toPhys_lt hx.1 hx.2)
      (fun ⟨b₁, l₁⟩ hx₁ ⟨b₂, l₂⟩ hx₂ heq => by
        simp only [mem_sigma, mem_range] at hx₁ hx₂
        obtain ⟨hb, hl⟩ := hv.toPhys_inj hx₁.1 hx₁.2 hx₂.1 hx₂.2 heq
        subst hb; subst hl; rfl)
      (fun p hp => by
        rw [mem_range] at hp
        obtain ⟨hb, hl, htp⟩ := hv.ownerOf_bounds_and_toPhys hp
        exact ⟨⟨(bp.ownerOf p).1, (bp.ownerOf p).2⟩, by simp [hb, hl], htp⟩)
  simpa only [card_sigma, card_range] using hcard

/-- Number of active (`actCode b ≠ 0`) buckets in `[0, M)`. -/
@[expose] def actBucketCount (bp : BlockPoolState) : ℕ :=
  ((Finset.range bp.M).filter (fun b => bp.actCode b ≠ 0)).card

/-- Exact block-tag partition of `[0, B_full)`:
`B_full = unresLen + (∑ b ∈ range M, q b) + actBucketCount`. -/
theorem CoreValid.B_full_eq_block_sum {bp : BlockPoolState} (hv : bp.CoreValid) :
    bp.B_full = bp.unresLen + (∑ b ∈ Finset.range bp.M, bp.q b) + bp.actBucketCount := by
  set S0 := (Finset.range bp.B_full).filter (fun P => bp.blkTag P = 0)
  set S1 := (Finset.range bp.B_full).filter (fun P => bp.blkTag P = 1)
  set S2 := (Finset.range bp.B_full).filter (fun P => bp.blkTag P = 2)
  have hc0 : S0.card = bp.unresLen := by
    have h := Finset.card_bij (s := Finset.range bp.unresLen) (t := S0)
      (fun i _ => bp.unresStack i)
      (fun i hi => by
        rw [mem_range] at hi
        obtain ⟨h1, h2, _⟩ := hv.unres_fwd i hi
        exact mem_filter.mpr ⟨mem_range.mpr h1, h2⟩)
      (fun i₁ h₁ i₂ h₂ heq => by
        rw [mem_range] at h₁ h₂
        have hm₁ := (hv.unres_fwd i₁ h₁).2.2
        have hm₂ := (hv.unres_fwd i₂ h₂).2.2
        rw [heq] at hm₁; exact hm₁.symm.trans hm₂)
      (fun P hP => by
        obtain ⟨h1, h2⟩ := mem_filter.mp hP
        obtain ⟨hm_lt, hm_eq⟩ := hv.unres_bwd P (mem_range.mp h1) h2
        exact ⟨bp.blkMeta1 P, mem_range.mpr hm_lt, hm_eq⟩)
    simpa only [card_range] using h.symm
  have hc1 : S1.card = ∑ b ∈ Finset.range bp.M, bp.q b := by
    symm
    have h := Finset.card_bij (s := (Finset.range bp.M).sigma (fun b => Finset.range (bp.q b)))
      (t := S1)
      (fun x _ => bp.slabOf x.1 x.2)
      (fun x hx => by
        simp only [mem_sigma, mem_range] at hx
        obtain ⟨h1, h2, _, _⟩ := hv.slab_fwd x.1 hx.1 x.2 hx.2
        exact mem_filter.mpr ⟨mem_range.mpr h1, h2⟩)
      (fun ⟨b₁, v₁⟩ hx₁ ⟨b₂, v₂⟩ hx₂ heq => by
        simp only [mem_sigma, mem_range] at hx₁ hx₂
        obtain ⟨_, _, hb₁, hv₁⟩ := hv.slab_fwd b₁ hx₁.1 v₁ hx₁.2
        obtain ⟨_, _, hb₂, hv₂⟩ := hv.slab_fwd b₂ hx₂.1 v₂ hx₂.2
        rw [heq] at hb₁ hv₁
        have hbe := hb₁.symm.trans hb₂
        have hve := hv₁.symm.trans hv₂
        subst hbe; subst hve; rfl)
      (fun P hP => by
        obtain ⟨h1, h2⟩ := mem_filter.mp hP
        obtain ⟨hb, hvp, heq⟩ := hv.slab_bwd P (mem_range.mp h1) h2
        exact ⟨⟨bp.blkMeta1 P, bp.blkMeta2 P⟩, by simp [hb, hvp], heq⟩)
    simpa only [card_sigma, card_range] using h
  have hc2 : S2.card = bp.actBucketCount := by
    symm
    exact Finset.card_bij (s := (Finset.range bp.M).filter (fun b => bp.actCode b ≠ 0))
      (t := S2)
      (fun b _ => bp.actBlk b)
      (fun b hb => by
        obtain ⟨hb_lt, hne⟩ := mem_filter.mp hb
        obtain ⟨h1, h2, _⟩ := hv.act_fwd b (mem_range.mp hb_lt) hne
        exact mem_filter.mpr ⟨mem_range.mpr h1, h2⟩)
      (fun b₁ h₁ b₂ h₂ heq => by
        obtain ⟨hb₁, hne₁⟩ := mem_filter.mp h₁
        obtain ⟨hb₂, hne₂⟩ := mem_filter.mp h₂
        have hm₁ := (hv.act_fwd b₁ (mem_range.mp hb₁) hne₁).2.2
        have hm₂ := (hv.act_fwd b₂ (mem_range.mp hb₂) hne₂).2.2
        rw [heq] at hm₁; exact hm₁.symm.trans hm₂)
      (fun P hP => by
        obtain ⟨h1, h2⟩ := mem_filter.mp hP
        obtain ⟨hb, hne, heq⟩ := hv.act_bwd P (mem_range.mp h1) h2
        exact ⟨bp.blkMeta1 P, mem_filter.mpr ⟨mem_range.mpr hb, hne⟩, heq⟩)
  have hdisj01 : Disjoint S0 S1 := disjoint_filter.mpr fun _ _ h0 h1 => by omega
  have hdisj01_2 : Disjoint (S0 ∪ S1) S2 := disjoint_left.mpr fun P h01 h2 => by
    have ht2 := (mem_filter.mp h2).2
    rcases mem_union.mp h01 with h0 | h1
    · have ht0 := (mem_filter.mp h0).2; omega
    · have ht1 := (mem_filter.mp h1).2; omega
  have hunion : S0 ∪ S1 ∪ S2 = Finset.range bp.B_full := by
    ext P
    simp only [S0, S1, S2, mem_union, mem_filter, mem_range]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro h
      have ht := hv.blkTag_lt P h
      rcases (by omega : bp.blkTag P = 0 ∨ bp.blkTag P = 1 ∨ bp.blkTag P = 2) with h0 | h1 | h2
      · exact Or.inl (Or.inl ⟨h, h0⟩)
      · exact Or.inl (Or.inr ⟨h, h1⟩)
      · exact Or.inr ⟨h, h2⟩
  have hcard_tot := congrArg Finset.card hunion
  rw [card_union_of_disjoint hdisj01_2, card_union_of_disjoint hdisj01, card_range,
    hc0, hc1, hc2] at hcard_tot
  exact hcard_tot.symm

/-- **Tail-Slot Conservation Identity**:
`∑ b ∈ range M, bp.r b = (bp.unresLen + bp.actBucketCount) * bp.K + bp.rem`. -/
theorem CoreValid.sum_r_eq_tail_supply {bp : BlockPoolState} (hv : bp.CoreValid) :
    ∑ b ∈ Finset.range bp.M, bp.r b =
      (bp.unresLen + bp.actBucketCount) * bp.K + bp.rem := by
  have hsum := hv.sum_bktCount_eq_nSide
  unfold bktCount at hsum
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← hv.nSide_eq, hv.B_full_eq_block_sum] at hsum
  linarith

/-- Total tail-owning blocks (`blkTag ∈ {0, 2}` in `[0, B_full]`) equals
`bp.unresLen + bp.actBucketCount + 1`, which is strictly `< 8 * bp.M`. -/
theorem CoreValid.tail_block_card_lt {bp : BlockPoolState} (hv : bp.CoreValid) :
    ((Finset.range (bp.B_full + 1)).filter
      (fun P => bp.blkTag P = 0 ∨ bp.blkTag P = 2)).card =
      bp.unresLen + bp.actBucketCount + 1 ∧
    bp.unresLen + bp.actBucketCount + 1 < 8 * bp.M := by
  have hK := hv.K_pos
  have hM := hv.M_pos
  have hcard_eq : ((Finset.range (bp.B_full + 1)).filter
      (fun P => bp.blkTag P = 0 ∨ bp.blkTag P = 2)).card =
      bp.unresLen + bp.actBucketCount + 1 := by
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [hv.blkTag_top, true_or, ↓reduceIte]
    have hnot : bp.B_full ∉ (Finset.range bp.B_full).filter
        (fun P => bp.blkTag P = 0 ∨ bp.blkTag P = 2) := by simp
    rw [Finset.card_insert_of_notMem hnot]
    set S0 := (Finset.range bp.B_full).filter (fun P => bp.blkTag P = 0)
    set S2 := (Finset.range bp.B_full).filter (fun P => bp.blkTag P = 2)
    have hsplit : (Finset.range bp.B_full).filter (fun P => bp.blkTag P = 0 ∨ bp.blkTag P = 2) =
        S0 ∪ S2 := by ext P; simp [S0, S2, and_or_left]
    have hdisj : Disjoint S0 S2 := disjoint_filter.mpr fun _ _ h0 h2 => by omega
    rw [hsplit, card_union_of_disjoint hdisj]
    have hc0 : S0.card = bp.unresLen := by
      have h := Finset.card_bij (s := Finset.range bp.unresLen) (t := S0)
        (fun i _ => bp.unresStack i)
        (fun i hi => by
          obtain ⟨h1, h2, _⟩ := hv.unres_fwd i (mem_range.mp hi)
          exact mem_filter.mpr ⟨mem_range.mpr h1, h2⟩)
        (fun i₁ h₁ i₂ h₂ heq => by
          have hm₁ := (hv.unres_fwd i₁ (mem_range.mp h₁)).2.2
          have hm₂ := (hv.unres_fwd i₂ (mem_range.mp h₂)).2.2
          rw [heq] at hm₁; exact hm₁.symm.trans hm₂)
        (fun P hP => by
          obtain ⟨h1, h2⟩ := mem_filter.mp hP
          obtain ⟨hm_lt, hm_eq⟩ := hv.unres_bwd P (mem_range.mp h1) h2
          exact ⟨bp.blkMeta1 P, mem_range.mpr hm_lt, hm_eq⟩)
      simpa only [card_range] using h.symm
    have hc2 : S2.card = bp.actBucketCount := by
      symm
      exact Finset.card_bij (s := (Finset.range bp.M).filter (fun b => bp.actCode b ≠ 0))
        (t := S2)
        (fun b _ => bp.actBlk b)
        (fun b hb => by
          obtain ⟨hb_lt, hne⟩ := mem_filter.mp hb
          obtain ⟨h1, h2, _⟩ := hv.act_fwd b (mem_range.mp hb_lt) hne
          exact mem_filter.mpr ⟨mem_range.mpr h1, h2⟩)
        (fun b₁ h₁ b₂ h₂ heq => by
          obtain ⟨hb₁, hne₁⟩ := mem_filter.mp h₁
          obtain ⟨hb₂, hne₂⟩ := mem_filter.mp h₂
          have hm₁ := (hv.act_fwd b₁ (mem_range.mp hb₁) hne₁).2.2
          have hm₂ := (hv.act_fwd b₂ (mem_range.mp hb₂) hne₂).2.2
          rw [heq] at hm₁; exact hm₁.symm.trans hm₂)
        (fun P hP => by
          obtain ⟨h1, h2⟩ := mem_filter.mp hP
          obtain ⟨hb, hne, heq⟩ := hv.act_bwd P (mem_range.mp h1) h2
          exact ⟨bp.blkMeta1 P, mem_filter.mpr ⟨mem_range.mpr hb, hne⟩, heq⟩)
    rw [hc0, hc2]
  refine ⟨hcard_eq, ?_⟩
  have hsum_lt : ∑ b ∈ Finset.range bp.M, bp.r b < bp.M * (6 * bp.K) := by
    have hnonempty : (Finset.range bp.M).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
    calc ∑ b ∈ Finset.range bp.M, bp.r b
        < ∑ _b ∈ Finset.range bp.M, (6 * bp.K) :=
          Finset.sum_lt_sum_of_nonempty hnonempty fun b hb =>
            (hv.bkt_bounds b (mem_range.mp hb)).2.1
      _ = bp.M * (6 * bp.K) := by rw [Finset.sum_const, card_range, smul_eq_mul]
  rw [hv.sum_r_eq_tail_supply] at hsum_lt
  have hlt_6M : bp.unresLen + bp.actBucketCount < 6 * bp.M := by
    by_contra hge
    have hmul : (6 * bp.M) * bp.K ≤ (bp.unresLen + bp.actBucketCount) * bp.K :=
      Nat.mul_le_mul_right bp.K (Nat.le_of_not_lt hge)
    linarith
  omega

/-- Deterministic `O(1)` 5-slot pigeonhole finder for `Promote` (`unresLen ≥ 5` guarantees at
least one entry in `unresStack 0 .. 4` satisfies `P + 3 ≤ B_full` and avoids both `topSwapDst`
and `topSwapSrc`). -/
@[expose] def findPromoteIdx (bp : BlockPoolState) : ℕ :=
  let ok (i : ℕ) : Bool :=
    decide (i < bp.unresLen ∧ bp.unresStack i + 3 ≤ bp.B_full ∧
      (bp.topSwapAct = 0 ∨
        (bp.unresStack i ≠ bp.topSwapDst ∧ bp.unresStack i ≠ bp.topSwapSrc)))
  if ok 0 then 0
  else if ok 1 then 1
  else if ok 2 then 2
  else if ok 3 then 3
  else 4

theorem CoreValid.findPromoteIdx_spec {bp : BlockPoolState} (hv : bp.CoreValid)
    (h5 : 5 ≤ bp.unresLen) :
    let idx := bp.findPromoteIdx
    idx < 5 ∧ idx < bp.unresLen ∧
    bp.unresStack idx + 3 ≤ bp.B_full ∧
    (bp.topSwapAct = 0 ∨
      (bp.unresStack idx ≠ bp.topSwapDst ∧ bp.unresStack idx ≠ bp.topSwapSrc)) := by
  have hex : ∃ i < 5, bp.unresStack i + 3 ≤ bp.B_full ∧
      (bp.topSwapAct = 0 ∨
        (bp.unresStack i ≠ bp.topSwapDst ∧ bp.unresStack i ≠ bp.topSwapSrc)) := by
    by_contra hall
    push Not at hall
    set img := (Finset.range 5).image bp.unresStack
    have hinj : ∀ i₁ ∈ Finset.range 5, ∀ i₂ ∈ Finset.range 5,
        bp.unresStack i₁ = bp.unresStack i₂ → i₁ = i₂ := fun i₁ h₁ i₂ h₂ heq => by
      have hm₁ := (hv.unres_fwd i₁ (by rw [mem_range] at h₁; omega)).2.2
      have hm₂ := (hv.unres_fwd i₂ (by rw [mem_range] at h₂; omega)).2.2
      rw [heq] at hm₁; exact hm₁.symm.trans hm₂
    have hcard5 : img.card = 5 := by rw [card_image_of_injOn hinj, card_range]
    set bad : Finset ℕ :=
      {bp.B_full - 2, bp.B_full - 1, bp.topSwapDst, bp.topSwapSrc}
    have hsub : img ⊆ bad := by
      intro P hP
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hP
      rw [mem_range] at hi
      have hP_lt := (hv.unres_fwd i (by omega)).1
      simp only [bad, mem_insert, mem_singleton]
      by_cases hle : bp.unresStack i + 3 ≤ bp.B_full
      · obtain ⟨_, hnot_both⟩ := hall i hi hle
        by_cases hd : bp.unresStack i = bp.topSwapDst
        · exact Or.inr (Or.inr (Or.inl hd))
        · exact Or.inr (Or.inr (Or.inr (hnot_both hd)))
      · omega
    have hle4 : bad.card ≤ 4 :=
      (card_insert_le _ _).trans (Nat.add_le_add_right
        ((card_insert_le _ _).trans (Nat.add_le_add_right
          ((card_insert_le _ _).trans (by simp)) 1)) 1)
    have := Finset.card_le_card hsub
    omega
  dsimp only [findPromoteIdx]
  set ok : ℕ → Bool := fun i =>
    decide (i < bp.unresLen ∧ bp.unresStack i + 3 ≤ bp.B_full ∧
      (bp.topSwapAct = 0 ∨
        (bp.unresStack i ≠ bp.topSwapDst ∧ bp.unresStack i ≠ bp.topSwapSrc)))
  have hok_iff : ∀ i < 5, ok i = true ↔
      (bp.unresStack i + 3 ≤ bp.B_full ∧
        (bp.topSwapAct = 0 ∨
          (bp.unresStack i ≠ bp.topSwapDst ∧ bp.unresStack i ≠ bp.topSwapSrc))) := fun i hi => by
    dsimp only [ok]; rw [decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  by_cases h0 : ok 0
  · rw [ite_eq_left h0]; obtain ⟨h1, h2⟩ := (hok_iff 0 (by decide)).mp h0
    exact ⟨by decide, by omega, h1, h2⟩
  · rw [ite_eq_right h0]
    by_cases h1 : ok 1
    · rw [ite_eq_left h1]; obtain ⟨ha, hb⟩ := (hok_iff 1 (by decide)).mp h1
      exact ⟨by decide, by omega, ha, hb⟩
    · rw [ite_eq_right h1]
      by_cases h2 : ok 2
      · rw [ite_eq_left h2]; obtain ⟨ha, hb⟩ := (hok_iff 2 (by decide)).mp h2
        exact ⟨by decide, by omega, ha, hb⟩
      · rw [ite_eq_right h2]
        by_cases h3 : ok 3
        · rw [ite_eq_left h3]; obtain ⟨ha, hb⟩ := (hok_iff 3 (by decide)).mp h3
          exact ⟨by decide, by omega, ha, hb⟩
        · rw [ite_eq_right h3]
          obtain ⟨i, hi, ha, hb⟩ := hex
          have hoki := (hok_iff i hi).mpr ⟨ha, hb⟩
          have hi4 : i = 4 := by
            rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with
              rfl | rfl | rfl | rfl | rfl <;> first | contradiction | rfl
          subst hi4; exact ⟨by decide, by omega, ha, hb⟩

/-- Deterministic `O(1)` 3-slot pigeonhole finder for `TopSwap` (`unresLen ≥ 3` guarantees at least
one entry among `unresStack 0 .. 2` satisfies `P + 2 < B_full`, i.e., `P + 3 ≤ B_full`). -/
@[expose] def findTopSwapIdx (bp : BlockPoolState) : ℕ :=
  if 0 < bp.unresLen ∧ bp.unresStack 0 + 3 ≤ bp.B_full then 0
  else if 1 < bp.unresLen ∧ bp.unresStack 1 + 3 ≤ bp.B_full then 1
  else 2

theorem CoreValid.findTopSwapIdx_spec {bp : BlockPoolState} (hv : bp.CoreValid)
    (h3 : 3 ≤ bp.unresLen) :
    let idx := bp.findTopSwapIdx
    idx < 3 ∧ idx < bp.unresLen ∧ bp.unresStack idx + 3 ≤ bp.B_full := by
  have hex : ∃ i < 3, bp.unresStack i + 3 ≤ bp.B_full := by
    by_contra hall
    push Not at hall
    set img := (Finset.range 3).image bp.unresStack
    have hinj : ∀ i₁ ∈ Finset.range 3, ∀ i₂ ∈ Finset.range 3,
        bp.unresStack i₁ = bp.unresStack i₂ → i₁ = i₂ := fun i₁ h₁ i₂ h₂ heq => by
      have hm₁ := (hv.unres_fwd i₁ (by rw [mem_range] at h₁; omega)).2.2
      have hm₂ := (hv.unres_fwd i₂ (by rw [mem_range] at h₂; omega)).2.2
      rw [heq] at hm₁; exact hm₁.symm.trans hm₂
    have hcard3 : img.card = 3 := by rw [card_image_of_injOn hinj, card_range]
    set bad : Finset ℕ := {bp.B_full - 2, bp.B_full - 1}
    have hsub : img ⊆ bad := by
      intro P hP
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hP
      rw [mem_range] at hi
      have hP_lt := (hv.unres_fwd i (by omega)).1
      have hgt := hall i hi
      simp only [bad, mem_insert, mem_singleton]; omega
    have hle2 : bad.card ≤ 2 := (card_insert_le _ _).trans (by simp)
    have := Finset.card_le_card hsub
    omega
  dsimp only [findTopSwapIdx]
  by_cases h0 : 0 < bp.unresLen ∧ bp.unresStack 0 + 3 ≤ bp.B_full
  · rw [ite_eq_left h0]; exact ⟨by decide, h0.1, h0.2⟩
  · rw [ite_eq_right h0]
    by_cases h1 : 1 < bp.unresLen ∧ bp.unresStack 1 + 3 ≤ bp.B_full
    · rw [ite_eq_left h1]; exact ⟨by decide, h1.1, h1.2⟩
    · rw [ite_eq_right h1]
      obtain ⟨i, hi, ha⟩ := hex
      have hi2 : i = 2 := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact absurd ⟨by omega, ha⟩ h0
        · exact absurd ⟨by omega, ha⟩ h1
        · rfl
      subst hi2; exact ⟨by decide, by omega, ha⟩

/-! ## Section 3: Core-Preserving Rebalancing Primitives -/

/-- Pointwise update of a 1-argument table `f` at `i`. -/
@[expose] def set1 {α : Type*} (f : ℕ → α) (i : ℕ) (v : α) (i' : ℕ) : α :=
  if i' = i then v else f i'

@[simp] theorem set1_self {α : Type*} (f : ℕ → α) (i : ℕ) (v : α) :
    set1 f i v i = v := by
  simp [set1]

theorem set1_of_ne {α : Type*} (f : ℕ → α) (i : ℕ) (v : α) (i' : ℕ) (hne : i' ≠ i) :
    set1 f i v i' = f i' := by
  simp [set1, hne]

/-- Apply an optional `PhysSwap` to an abstract item array `arr : ℕ → α`. -/
@[expose] def applyOptSwap {α : Type*} (osw : Option PhysSwap) (arr : ℕ → α) : ℕ → α :=
  match osw with
  | none => arr
  | some sw => sw.apply arr

/-- Predicate stating that `tIdx` is currently a live tail coordinate of `bp`. -/
@[expose] def LiveTail (bp : BlockPoolState) (tIdx : ℕ) : Prop :=
  ∃ b < bp.M, ∃ k, bp.actCur b ≤ k ∧ k < bp.r b ∧
    bp.tailRing b ((bp.head b + k) % (6 * bp.K)) = tIdx

theorem CoreValid.physOfTail_lt_of_live {bp : BlockPoolState} (hv : bp.CoreValid)
    {tIdx : ℕ} (ht : bp.LiveTail tIdx) :
    bp.physOfTail tIdx < bp.nSide := by
  obtain ⟨b, hb, k, hk_ge, hk_lt, htr⟩ := ht
  have hloc : bp.q b * bp.K + k < bp.bktCount b := by unfold bktCount; omega
  have hlt := hv.toPhys_lt hb hloc
  unfold toPhys at hlt; dsimp only at hlt
  have hnot_slab : ¬(bp.q b * bp.K + k < bp.q b * bp.K) := by omega
  have hsub : bp.q b * bp.K + k - bp.q b * bp.K = k := Nat.add_sub_cancel_left _ _
  rwa [ite_eq_right hnot_slab, hsub, ite_eq_right (not_lt.mpr hk_ge), htr] at hlt

theorem CoreValid.physOfTail_inj_of_live {bp : BlockPoolState} (hv : bp.CoreValid)
    {t₁ t₂ : ℕ} (ht₁ : bp.LiveTail t₁) (ht₂ : bp.LiveTail t₂)
    (heq : bp.physOfTail t₁ = bp.physOfTail t₂) :
    t₁ = t₂ := by
  have hK := hv.K_pos
  obtain ⟨b₁, hb₁, k₁, hge₁, hlt₁, htr₁⟩ := ht₁
  obtain ⟨b₂, hb₂, k₂, hge₂, hlt₂, htr₂⟩ := ht₂
  have htf₁ := hv.tail_fwd b₁ hb₁ k₁ hge₁ hlt₁
  have htf₂ := hv.tail_fwd b₂ hb₂ k₂ hge₂ hlt₂
  dsimp only at htf₁ htf₂
  rw [htr₁] at htf₁; rw [htr₂] at htf₂
  obtain ⟨_, _, hm2₁, _, _, _⟩ := htf₁
  obtain ⟨_, _, hm2₂, _, _, _⟩ := htf₂
  unfold physOfTail at heq
  have hoff₁ : t₁ % bp.K < bp.K := Nat.mod_lt t₁ hK
  have hoff₂ : t₂ % bp.K < bp.K := Nat.mod_lt t₂ hK
  have hmod_eq : t₁ % bp.K = t₂ % bp.K := by
    have h1 := congrArg (· % bp.K) heq
    simpa only [Nat.add_comm _ (t₁ % bp.K), Nat.add_comm _ (t₂ % bp.K),
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff₁, Nat.mod_eq_of_lt hoff₂] using h1
  have hdiv_eq : bp.effBlk (bp.tbPhysBlk (t₁ / bp.K)) (t₁ % bp.K) =
      bp.effBlk (bp.tbPhysBlk (t₂ / bp.K)) (t₂ % bp.K) := by
    have h1 := congrArg (· / bp.K) heq
    simpa only [Nat.add_comm _ (t₁ % bp.K), Nat.add_comm _ (t₂ % bp.K),
      Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff₁, Nat.div_eq_of_lt hoff₂,
      zero_add] using h1
  rw [← hmod_eq] at hdiv_eq
  have hP_eq : bp.tbPhysBlk (t₁ / bp.K) = bp.tbPhysBlk (t₂ / bp.K) := by
    have := congrArg (fun E => bp.effBlk E (t₁ % bp.K)) hdiv_eq
    simpa only [effBlk_involutive] using this
  have htb_eq : t₁ / bp.K = t₂ / bp.K := by
    rw [← hm2₁, hP_eq, hm2₂]
  have hr₁ := Nat.div_add_mod t₁ bp.K
  have hr₂ := Nat.div_add_mod t₂ bp.K
  rw [htb_eq, hmod_eq] at hr₁
  exact hr₁.symm.trans hr₂

/-- Swap two live tail coordinates `t₁, t₂`, swapping both their physical slots and their
`(tailRing, tailOwnerBkt, tailOwnerRing)` pointers (`0` changes to any `(b, loc)`!). -/
@[expose] def swapTailCoords (bp : BlockPoolState) (t₁ t₂ : ℕ) :
    BlockPoolState × Option PhysSwap :=
  if t₁ = t₂ then
    (bp, none)
  else
    let b₁ := bp.tailOwnerBkt t₁
    let rk₁ := bp.tailOwnerRing t₁
    let b₂ := bp.tailOwnerBkt t₂
    let rk₂ := bp.tailOwnerRing t₂
    let bp' : BlockPoolState :=
      { bp with
        tailRing := set2 (set2 bp.tailRing b₁ rk₁ t₂) b₂ rk₂ t₁
        tailOwnerBkt := set1 (set1 bp.tailOwnerBkt t₁ b₂) t₂ b₁
        tailOwnerRing := set1 (set1 bp.tailOwnerRing t₁ rk₂) t₂ rk₁ }
    (bp', some ⟨bp.physOfTail t₁, bp.physOfTail t₂⟩)

theorem CoreValid.swapTailCoords_spec {bp : BlockPoolState} (hv : bp.CoreValid)
    {t₁ t₂ : ℕ} (ht₁ : bp.LiveTail t₁) (ht₂ : bp.LiveTail t₂) :
    let (bp', osw) := bp.swapTailCoords t₁ t₂
    bp'.CoreValid ∧
    (∀ sw, osw = some sw → sw.p₁ < bp.nSide ∧ sw.p₂ < bp.nSide) ∧
    (∀ {α : Type*} (arr : ℕ → α) (b : ℕ) (loc : ℕ),
      b < bp.M → loc < bp.bktCount b →
      applyOptSwap osw arr (bp'.toPhys b loc) = arr (bp.toPhys b loc)) := by
  have hK := hv.K_pos
  unfold swapTailCoords
  by_cases heq : t₁ = t₂
  · rw [ite_eq_left heq]
    exact ⟨hv, fun _ h => by simp at h, fun _ _ _ _ _ => rfl⟩
  · rw [ite_eq_right heq]
    dsimp only
    obtain ⟨b₁, hb₁, k₁, hge₁, hlt₁, htr₁⟩ := ht₁
    obtain ⟨b₂, hb₂, k₂, hge₂, hlt₂, htr₂⟩ := ht₂
    have htf₁ := hv.tail_fwd b₁ hb₁ k₁ hge₁ hlt₁
    have htf₂ := hv.tail_fwd b₂ hb₂ k₂ hge₂ hlt₂
    dsimp only at htf₁ htf₂
    set rk₁ := (bp.head b₁ + k₁) % (6 * bp.K)
    set rk₂ := (bp.head b₂ + k₂) % (6 * bp.K)
    have htr₁' : bp.tailRing b₁ rk₁ = t₁ := htr₁
    have htr₂' : bp.tailRing b₂ rk₂ = t₂ := htr₂
    rw [htr₁'] at htf₁; rw [htr₂'] at htf₂
    obtain ⟨ht1_lt, hP1_le, hm2_1, hkind1, hob1, hor1⟩ := htf₁
    obtain ⟨ht2_lt, hP2_le, hm2_2, hkind2, hob2, hor2⟩ := htf₂
    have hbrk_ne : ¬(b₂ = b₁ ∧ rk₂ = rk₁) := by
      rintro ⟨rfl, hrk⟩; rw [hrk] at htr₂'; exact heq (htr₁'.symm.trans htr₂')
    have hp1_lt := hv.physOfTail_lt_of_live ⟨b₁, hb₁, k₁, hge₁, hlt₁, htr₁⟩
    have hp2_lt := hv.physOfTail_lt_of_live ⟨b₂, hb₂, k₂, hge₂, hlt₂, htr₂⟩
    have hp_ne : bp.physOfTail t₁ ≠ bp.physOfTail t₂ := fun hpe =>
      heq (hv.physOfTail_inj_of_live ⟨b₁, hb₁, k₁, hge₁, hlt₁, htr₁⟩
        ⟨b₂, hb₂, k₂, hge₂, hlt₂, htr₂⟩ hpe)
    rw [hob1, hor1, hob2, hor2]
    set bp' : BlockPoolState :=
      { bp with
        tailRing := set2 (set2 bp.tailRing b₁ rk₁ t₂) b₂ rk₂ t₁
        tailOwnerBkt := set1 (set1 bp.tailOwnerBkt t₁ b₂) t₂ b₁
        tailOwnerRing := set1 (set1 bp.tailOwnerRing t₁ rk₂) t₂ rk₁ }
    have hcv' : bp'.CoreValid :=
      { M_pos := hv.M_pos
        K_ge := hv.K_ge
        bkt_bounds := hv.bkt_bounds
        blkTag_lt := hv.blkTag_lt
        blkTag_top := hv.blkTag_top
        unres_fwd := hv.unres_fwd
        unres_bwd := hv.unres_bwd
        slab_fwd := hv.slab_fwd
        slab_bwd := hv.slab_bwd
        act_fwd := hv.act_fwd
        act_bwd := hv.act_bwd
        tb_fwd := hv.tb_fwd
        freeTb_valid := hv.freeTb_valid
        freeTb_inj := hv.freeTb_inj
        tbHighWater_supply := hv.tbHighWater_supply
        tbHighWater_le_max := hv.tbHighWater_le_max
        topSwap_act_le := hv.topSwap_act_le
        topSwap_valid := hv.topSwap_valid
        tail_fwd := fun b hb k hk_ge hk_lt => by
          have hact_eq : bp'.actCur b = bp.actCur b := rfl
          have hBf_eq : bp'.B_full = bp.B_full := rfl
          have hrem_eq : bp'.rem = bp.rem := rfl
          rw [hact_eq] at hk_ge
          dsimp only [bp'] at hk_lt ⊢
          rw [hBf_eq, hrem_eq]
          set rk := (bp.head b + k) % (6 * bp.K)
          by_cases hc2 : b = b₂ ∧ rk = rk₂
          · rcases hc2 with ⟨rfl, hrk_eq⟩
            rw [hrk_eq, set2_self, set1_of_ne _ _ _ _ heq, set1_self,
              set1_of_ne _ _ _ _ heq, set1_self]
            exact ⟨ht1_lt, hP1_le, hm2_1, hkind1, rfl, rfl⟩
          · rw [set2_of_ne _ _ _ _ _ _ hc2]
            by_cases hc1 : b = b₁ ∧ rk = rk₁
            · rcases hc1 with ⟨rfl, hrk_eq⟩
              rw [hrk_eq, set2_self, set1_self, set1_self]
              exact ⟨ht2_lt, hP2_le, hm2_2, hkind2, rfl, rfl⟩
            · rw [set2_of_ne _ _ _ _ _ _ hc1]
              have htf := hv.tail_fwd b hb k hk_ge hk_lt
              dsimp only at htf
              obtain ⟨ha, hb_le, hc, hd, hob, hor⟩ := htf
              have hne2 : bp.tailRing b rk ≠ t₂ := fun h => by
                rw [h] at hob hor; exact hc2 ⟨hob.symm.trans hob2, hor.symm.trans hor2⟩
              have hne1 : bp.tailRing b rk ≠ t₁ := fun h => by
                rw [h] at hob hor; exact hc1 ⟨hob.symm.trans hob1, hor.symm.trans hor1⟩
              rw [set1_of_ne _ _ _ _ hne2, set1_of_ne _ _ _ _ hne1,
                set1_of_ne _ _ _ _ hne2, set1_of_ne _ _ _ _ hne1]
              exact ⟨ha, hb_le, hc, hd, hob, hor⟩
        tail_bwd := fun P hP_le off hoff hlt hor => by
          have hBf_eq : bp'.B_full = bp.B_full := rfl
          have hrem_eq : bp'.rem = bp.rem := rfl
          have hact_eq : ∀ b, bp'.actCur b = bp.actCur b := fun _ => rfl
          rw [hBf_eq] at hP_le
          rw [hBf_eq, hrem_eq] at hlt
          dsimp only [bp'] at hoff hor ⊢
          rw [hact_eq] at hor
          set t := bp.blkMeta2 P * bp.K + off
          have hrk1_lt : rk₁ < 6 * bp.K := Nat.mod_lt _ (by omega)
          have hrk2_lt : rk₂ < 6 * bp.K := Nat.mod_lt _ (by omega)
          by_cases ht_eq2 : t = t₂
          · rw [ht_eq2, set1_self, set1_self]
            obtain ⟨_, hr1_lt, hhd1_lt, _, _⟩ := hv.bkt_bounds b₁ hb₁
            have hk_re : (rk₁ + 6 * bp.K - bp.head b₁) % (6 * bp.K) = k₁ :=
              add_sub_head_mod hK hhd1_lt (hlt₁.trans hr1_lt)
            rw [hk_re, set2_of_ne _ _ _ _ _ _ (fun h => hbrk_ne ⟨h.1.symm, h.2.symm⟩), set2_self]
            exact ⟨hb₁, hrk1_lt, hge₁, hlt₁, rfl⟩
          · rw [set1_of_ne _ _ _ _ ht_eq2, set1_of_ne _ _ _ _ ht_eq2]
            by_cases ht_eq1 : t = t₁
            · rw [ht_eq1, set1_self, set1_self]
              obtain ⟨_, hr2_lt, hhd2_lt, _, _⟩ := hv.bkt_bounds b₂ hb₂
              have hk_re : (rk₂ + 6 * bp.K - bp.head b₂) % (6 * bp.K) = k₂ :=
                add_sub_head_mod hK hhd2_lt (hlt₂.trans hr2_lt)
              rw [hk_re, set2_self]
              exact ⟨hb₂, hrk2_lt, hge₂, hlt₂, rfl⟩
            · rw [set1_of_ne _ _ _ _ ht_eq1, set1_of_ne _ _ _ _ ht_eq1]
              obtain ⟨hb, hrk, hk_ge, hk_lt, htr⟩ := hv.tail_bwd P hP_le off hoff hlt hor
              have hne2 : ¬(bp.tailOwnerBkt t = b₂ ∧ bp.tailOwnerRing t = rk₂) := by
                rintro ⟨he1, he2⟩
                rw [he1, he2, htr₂'] at htr; exact ht_eq2 htr.symm
              have hne1 : ¬(bp.tailOwnerBkt t = b₁ ∧ bp.tailOwnerRing t = rk₁) := by
                rintro ⟨he1, he2⟩
                rw [he1, he2, htr₁'] at htr; exact ht_eq1 htr.symm
              rw [set2_of_ne _ _ _ _ _ _ hne2, set2_of_ne _ _ _ _ _ _ hne1]
              exact ⟨hb, hrk, hk_ge, hk_lt, htr⟩ }
    refine ⟨hcv', fun sw hsw => ?_, fun arr b loc hb hloc => ?_⟩
    · injection hsw with hsw_eq; rw [← hsw_eq]; exact ⟨hp1_lt, hp2_lt⟩
    · dsimp only [applyOptSwap]
      have htp_b' : bp'.toPhys b loc =
          if loc < bp.q b * bp.K then
            bp.effBlk (bp.slabOf b (loc / bp.K)) (loc % bp.K) * bp.K + loc % bp.K
          else
            let k := loc - bp.q b * bp.K
            if k < bp.actCur b then
              bp.effBlk (bp.actBlk b) k * bp.K + k
            else
              bp.physOfTail (set2 (set2 bp.tailRing b₁ rk₁ t₂) b₂ rk₂ t₁ b
                ((bp.head b + k) % (6 * bp.K))) := rfl
      rw [htp_b']
      have hp1_eq_tp : bp.toPhys b₁ (bp.q b₁ * bp.K + k₁) = bp.physOfTail t₁ := by
        unfold toPhys; dsimp only
        rw [ite_eq_right (by omega), Nat.add_sub_cancel_left,
          ite_eq_right (not_lt.mpr hge₁), htr₁']
      have hp2_eq_tp : bp.toPhys b₂ (bp.q b₂ * bp.K + k₂) = bp.physOfTail t₂ := by
        unfold toPhys; dsimp only
        rw [ite_eq_right (by omega), Nat.add_sub_cancel_left,
          ite_eq_right (not_lt.mpr hge₂), htr₂']
      by_cases hslab : loc < bp.q b * bp.K
      · rw [ite_eq_left hslab]
        have hp_eq_tp : bp.toPhys b loc =
            bp.effBlk (bp.slabOf b (loc / bp.K)) (loc % bp.K) * bp.K + loc % bp.K := by
          unfold toPhys; dsimp only; rw [ite_eq_left hslab]
        rw [hp_eq_tp]
        have hne1 : bp.effBlk (bp.slabOf b (loc / bp.K)) (loc % bp.K) * bp.K + loc % bp.K ≠
            bp.physOfTail t₁ := fun hp => by
          rw [← hp_eq_tp, ← hp1_eq_tp] at hp
          obtain ⟨rfl, hl_eq⟩ := hv.toPhys_inj hb hloc hb₁ (by unfold bktCount; omega) hp
          omega
        have hne2 : bp.effBlk (bp.slabOf b (loc / bp.K)) (loc % bp.K) * bp.K + loc % bp.K ≠
            bp.physOfTail t₂ := fun hp => by
          rw [← hp_eq_tp, ← hp2_eq_tp] at hp
          obtain ⟨rfl, hl_eq⟩ := hv.toPhys_inj hb hloc hb₂ (by unfold bktCount; omega) hp
          omega
        exact PhysSwap.apply_of_ne _ arr hne1 hne2
      · rw [ite_eq_right hslab]
        dsimp only
        set k := loc - bp.q b * bp.K
        have hk_lt_r : k < bp.r b := by unfold bktCount at hloc; omega
        by_cases hact : k < bp.actCur b
        · rw [ite_eq_left hact]
          have hp_eq_tp : bp.toPhys b loc = bp.effBlk (bp.actBlk b) k * bp.K + k := by
            unfold toPhys; dsimp only; rw [ite_eq_right hslab, ite_eq_left hact]
          rw [hp_eq_tp]
          have hne1 : bp.effBlk (bp.actBlk b) k * bp.K + k ≠ bp.physOfTail t₁ := fun hp => by
            rw [← hp_eq_tp, ← hp1_eq_tp] at hp
            obtain ⟨rfl, hl_eq⟩ := hv.toPhys_inj hb hloc hb₁ (by unfold bktCount; omega) hp
            omega
          have hne2 : bp.effBlk (bp.actBlk b) k * bp.K + k ≠ bp.physOfTail t₂ := fun hp => by
            rw [← hp_eq_tp, ← hp2_eq_tp] at hp
            obtain ⟨rfl, hl_eq⟩ := hv.toPhys_inj hb hloc hb₂ (by unfold bktCount; omega) hp
            omega
          exact PhysSwap.apply_of_ne _ arr hne1 hne2
        · rw [ite_eq_right hact]
          have hp_eq_tp : bp.toPhys b loc =
              bp.physOfTail (bp.tailRing b ((bp.head b + k) % (6 * bp.K))) := by
            unfold toPhys; dsimp only; rw [ite_eq_right hslab, ite_eq_right hact]
          rw [hp_eq_tp]
          set rk := (bp.head b + k) % (6 * bp.K)
          by_cases hc2 : b = b₂ ∧ rk = rk₂
          · rcases hc2 with ⟨rfl, hrk_eq⟩
            rw [hrk_eq, set2_self, htr₂', PhysSwap.apply_p₁]
          · rw [set2_of_ne _ _ _ _ _ _ hc2]
            by_cases hc1 : b = b₁ ∧ rk = rk₁
            · rcases hc1 with ⟨rfl, hrk_eq⟩
              rw [hrk_eq, set2_self, htr₁', PhysSwap.apply_p₂]
            · rw [set2_of_ne _ _ _ _ _ _ hc1]
              have hk_ge : bp.actCur b ≤ k := Nat.le_of_not_lt hact
              have htf := hv.tail_fwd b hb k hk_ge hk_lt_r
              dsimp only at htf
              obtain ⟨_, _, _, _, hob, hor⟩ := htf
              have ht_ne1 : bp.tailRing b rk ≠ t₁ := fun h => by
                rw [h] at hob hor; exact hc1 ⟨hob.symm.trans hob1, hor.symm.trans hor1⟩
              have ht_ne2 : bp.tailRing b rk ≠ t₂ := fun h => by
                rw [h] at hob hor; exact hc2 ⟨hob.symm.trans hob2, hor.symm.trans hor2⟩
              have hlive_cur : bp.LiveTail (bp.tailRing b rk) := ⟨b, hb, k, hk_ge, hk_lt_r, rfl⟩
              have hp_ne1 : bp.physOfTail (bp.tailRing b rk) ≠ bp.physOfTail t₁ := fun hp =>
                ht_ne1 (hv.physOfTail_inj_of_live hlive_cur ⟨b₁, hb₁, k₁, hge₁, hlt₁, htr₁⟩ hp)
              have hp_ne2 : bp.physOfTail (bp.tailRing b rk) ≠ bp.physOfTail t₂ := fun hp =>
                ht_ne2 (hv.physOfTail_inj_of_live hlive_cur ⟨b₂, hb₂, k₂, hge₂, hlt₂, htr₂⟩ hp)
              exact PhysSwap.apply_of_ne _ arr hp_ne1 hp_ne2

/-- Remove entry `idx < bp.unresLen` from `unresStack` by swapping in `unresLen - 1`. -/
@[expose] def unresRemoveAt (bp : BlockPoolState) (idx : ℕ) : BlockPoolState :=
  let lastIdx := bp.unresLen - 1
  let P_last := bp.unresStack lastIdx
  { bp with
    unresLen := lastIdx
    unresStack := set1 bp.unresStack idx P_last
    blkMeta1 := if idx < lastIdx then set1 bp.blkMeta1 P_last idx else bp.blkMeta1 }

/-- Push physical block `P` (`blkTag P = 0`) onto `unresStack` at `bp.unresLen`. -/
@[expose] def unresPush (bp : BlockPoolState) (P : ℕ) : BlockPoolState :=
  { bp with
    blkTag := set1 bp.blkTag P 0
    blkMeta1 := set1 bp.blkMeta1 P bp.unresLen
    unresStack := set1 bp.unresStack bp.unresLen P
    unresLen := bp.unresLen + 1 }

/-- Push recycled tail-block ID `tb` onto `freeTbStack`. -/
@[expose] def freeTb (bp : BlockPoolState) (tb : ℕ) : BlockPoolState :=
  { bp with
    freeTbStack := set1 bp.freeTbStack bp.freeTbTop tb
    freeTbTop := bp.freeTbTop + 1 }

/-- Allocate a fresh tail-block ID `tb < 8 * bp.M` and bind it to block `P`'s `blkMeta2` and
`tbPhysBlk`. -/
@[expose] def allocTbFor (bp : BlockPoolState) (P : ℕ) : BlockPoolState :=
  if 0 < bp.freeTbTop then
    let top' := bp.freeTbTop - 1
    let tb := bp.freeTbStack top'
    { bp with
      freeTbTop := top'
      blkMeta2 := set1 bp.blkMeta2 P tb
      tbPhysBlk := set1 bp.tbPhysBlk tb P }
  else
    let tb := bp.tbHighWater
    { bp with
      tbHighWater := tb + 1
      blkMeta2 := set1 bp.blkMeta2 P tb
      tbPhysBlk := set1 bp.tbPhysBlk tb P }

/-- Advance bucket `b`'s active `Promote` or `Demote` job by 1 step (`O(1)` time, at most 1 swap).
Requires `cur < bp.r b` when `1 ≤ bp.actCode b ≤ bp.K` (always true in `Balanced`). -/
@[expose] def actStepOne (bp : BlockPoolState) (b : ℕ) : BlockPoolState × Option PhysSwap :=
  if bp.actCode b = 0 then
    (bp, none)
  else if bp.actCode b ≤ bp.K then
    let cur := bp.actCode b - 1
    if bp.r b ≤ cur then
      (bp, none)
    else
      let P_act := bp.actBlk b
      let rk_cur := (bp.head b + cur) % (6 * bp.K)
      let t_cur := bp.tailRing b rk_cur
      let t_act := bp.blkMeta2 P_act * bp.K + cur
      let (bp₁, osw) := bp.swapTailCoords t_cur t_act
      if cur + 1 < bp.K then
        ({ bp₁ with actCode := set1 bp₁.actCode b (bp.actCode b + 1) }, osw)
      else
        let vp := bp₁.q b
        let tb_old := bp₁.blkMeta2 P_act
        let bp₂ := bp₁.freeTb tb_old
        ({ bp₂ with
          q := set1 bp₂.q b (vp + 1)
          r := set1 bp₂.r b (bp₂.r b - bp.K)
          head := set1 bp₂.head b ((bp₂.head b + bp.K) % (6 * bp.K))
          actCode := set1 bp₂.actCode b 0
          slabOf := set2 bp₂.slabOf b vp P_act
          blkTag := set1 bp₂.blkTag P_act 1
          blkMeta2 := set1 bp₂.blkMeta2 P_act vp }, osw)
  else
    let cur := bp.actCode b - bp.K
    let cur' := cur - 1
    let P_act := bp.actBlk b
    let rk := (bp.head b + cur') % (6 * bp.K)
    let tIdx := bp.blkMeta2 P_act * bp.K + cur'
    let bp₁ : BlockPoolState :=
      { bp with
        tailRing := set2 bp.tailRing b rk tIdx
        tailOwnerBkt := set1 bp.tailOwnerBkt tIdx b
        tailOwnerRing := set1 bp.tailOwnerRing tIdx rk }
    if 1 < cur then
      ({ bp₁ with actCode := set1 bp₁.actCode b (bp.actCode b - 1) }, none)
    else
      let bp₂ := bp₁.unresPush P_act
      ({ bp₂ with actCode := set1 bp₂.actCode b 0 }, none)

/-- Start a `Promote` (`5 * K ≤ r b`) or `Demote` (`2 * r b ≤ 7 * K ∧ 0 < q b`) job on idle
bucket `b` (`0` swaps). -/
@[expose] def maybeStartBktJob (bp : BlockPoolState) (b : ℕ) : BlockPoolState :=
  if bp.actCode b ≠ 0 then
    bp
  else if 5 * bp.K ≤ bp.r b ∧ bp.q b < bp.maxSlabs ∧ 5 ≤ bp.unresLen then
    let idx := bp.findPromoteIdx
    let P_act := bp.unresStack idx
    let bp₁ := bp.unresRemoveAt idx
    { bp₁ with
      blkTag := set1 bp₁.blkTag P_act 2
      blkMeta1 := set1 bp₁.blkMeta1 P_act b
      actBlk := set1 bp₁.actBlk b P_act
      actCode := set1 bp₁.actCode b 1 }
  else if 0 < bp.q b ∧ 2 * bp.r b ≤ 7 * bp.K then
    let vp := bp.q b - 1
    let P_act := bp.slabOf b vp
    let bp₁ := bp.allocTbFor P_act
    { bp₁ with
      q := set1 bp₁.q b vp
      r := set1 bp₁.r b (bp.r b + bp.K)
      head := set1 bp₁.head b ((bp.head b + 5 * bp.K) % (6 * bp.K))
      actBlk := set1 bp₁.actBlk b P_act
      actCode := set1 bp₁.actCode b (2 * bp.K)
      blkTag := set1 bp₁.blkTag P_act 2
      blkMeta1 := set1 bp₁.blkMeta1 P_act b }
  else
    bp

/-- Commit a completed `K`-item `TopSwap` (`topSwapCur = K`) by swapping block metadata between
`S = topSwapSrc` and `D = topSwapDst` (`blkTag D = 0`) and clearing `topSwapAct := 0`. -/
@[expose] def commitTopSwap (bp : BlockPoolState) : BlockPoolState :=
  let S := bp.topSwapSrc
  let D := bp.topSwapDst
  let tagS := bp.blkTag S
  let m1S := bp.blkMeta1 S
  let m2S := bp.blkMeta2 S
  let posD := bp.blkMeta1 D
  let tbD := bp.blkMeta2 D
  let bp_base : BlockPoolState :=
    { bp with
      topSwapAct := 0
      topSwapCur := 0
      blkTag := set1 (set1 bp.blkTag S 0) D tagS
      blkMeta1 := set1 (set1 bp.blkMeta1 S posD) D m1S
      blkMeta2 := set1 (set1 bp.blkMeta2 S tbD) D m2S }
  if tagS = 0 then
    { bp_base with
      unresStack := set1 (set1 bp_base.unresStack posD S) m1S D
      tbPhysBlk := set1 (set1 bp_base.tbPhysBlk tbD S) m2S D }
  else if tagS = 1 then
    { bp_base with
      slabOf := set2 bp_base.slabOf m1S m2S D
      unresStack := set1 bp_base.unresStack posD S
      tbPhysBlk := set1 bp_base.tbPhysBlk tbD S }
  else
    { bp_base with
      actBlk := set1 bp_base.actBlk m1S D
      unresStack := set1 bp_base.unresStack posD S
      tbPhysBlk := set1 (set1 bp_base.tbPhysBlk tbD S) m2S D }

/-- Execute 1 swap step of an active `TopSwap` (`O(1)` time, 1 swap). -/
@[expose] def topSwapStepOne (bp : BlockPoolState) : BlockPoolState × Option PhysSwap :=
  if bp.topSwapAct = 0 then
    (bp, none)
  else
    let S := bp.topSwapSrc
    let D := bp.topSwapDst
    let cur := bp.topSwapCur
    let sw : PhysSwap := ⟨S * bp.K + cur, D * bp.K + cur⟩
    if cur + 1 < bp.K then
      ({ bp with topSwapCur := cur + 1 }, some sw)
    else
      (bp.commitTopSwap, some sw)

/-- Execute 1 top-boundary cleaning step (`O(1)` time, at most 1 swap) toward making
`P = B_full - 2` (`2 ≤ B_full`) satisfy `blkTag P = 0` and avoiding `topSwap`. -/
@[expose] def topCleanOne (bp : BlockPoolState) : BlockPoolState × Option PhysSwap :=
  if bp.B_full < 2 then
    (bp, none)
  else
    let P := bp.B_full - 2
    if bp.topSwapAct = 1 then
      if bp.topSwapSrc = P ∨ bp.topSwapDst = P ∨ bp.blkTag P ≠ 0 then
        bp.topSwapStepOne
      else
        (bp, none)
    else if bp.blkTag P = 0 then
      (bp, none)
    else if bp.blkTag P = 2 then
      bp.actStepOne (bp.blkMeta1 P)
    else if 3 ≤ bp.unresLen then
      let D := bp.unresStack bp.findTopSwapIdx
      let bp_start : BlockPoolState :=
        { bp with
          topSwapAct := 1
          topSwapSrc := P
          topSwapDst := D
          topSwapCur := 0 }
      bp_start.topSwapStepOne
    else
      (bp, none)

end BlockPoolState

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
