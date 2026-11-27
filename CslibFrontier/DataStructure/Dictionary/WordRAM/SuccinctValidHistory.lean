/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctDeleteOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabPool
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctDeleteOps
public import CslibFrontier.Tactic.WramOmega.Init
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Tactic.ValidProg
import CslibFrontier.Tactic.WramOmega

/-!
# Memory History Admissibility (`ValidHistory`) for Succinct Dictionary Programs

This module proves `(Memory.spec w).ValidHistory` for all `Memory.Prog` operations of the
fixed-capacity succinct dictionary (`queryBodyProg`, `insertBodyProg`, `deletePrepProg`, and
`deleteFinishProg`), discharging the admissibility obligation required when extracting native
Word-RAM `Code` via `Realizes.code_spec`. The proofs unfold the unexposed programs of the tail and
slab operation modules and reuse private bound lemmas of `SuccinctTailOps`, `SuccinctSlabPool`,
`SuccinctSlabMove`, `SuccinctSlabDemote` and `SuccinctDeleteOps`; from `SuccinctSlabOps` they need
only the bodies of `lastSlotOfProg`, `pushBackTailWriteProg`, `pushBackSlotProg` and
`popBackSlotProg`. This module reads all of these through `import all`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.ValidMem`: memory state well-formedness at word
  width `w` and frontier `≥ F`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.ValidProg`: predicate asserting that a
  `Memory.Prog` client produces a valid memory history from `s` whenever `ValidMem w F s` holds.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.dictFrontier`: standard dictionary frontier
  `base + totalSpace U V w n_max h_space`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.validProg_queryBody`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.validProg_insertBody`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.validProg_deletePrep`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.validProg_deleteFinish`: memory history
  admissibility for the four top-level `Memory.Prog` dictionary subroutines.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## Section 1: `ValidMem`, `ValidProg` combinators, and bit-packed array primitives -/

/-- A memory state is well-formed at word size `w` and has frontier at least `F`. -/
@[expose] def ValidMem (w F : ℕ) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧ F ≤ s.frontier

/-- A `Memory.Prog` client produces a valid memory history from `s` whenever `ValidMem w F s`
holds. -/
@[expose] def ValidProg {α : Type} (w F : ℕ) (s : Memory.State) (p : Memory.Prog α) : Prop :=
  ValidMem w F s → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)

theorem validMem_clientState {α : Type} {w F : ℕ} {s : Memory.State} {p : Memory.Prog α}
    (hm : ValidMem w F s) (hp : ValidProg w F s p) :
    ValidMem w F ((Memory.spec 0).clientState s p) :=
  ⟨wellFormed_clientState hm.1 (hp hm),
    hm.2.trans (Memory.frontier_le_clientState (w := 0) s p)⟩

theorem validProg_pure {α : Type} {w F : ℕ} {s : Memory.State} (a : α) :
    ValidProg w F s (pure a) :=
  fun _ => trivial

theorem validProg_bind {α β : Type} {w F : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : ValidProg w F s p)
    (hq : ValidProg w F ((Memory.spec 0).clientState s p)
      (q ((Memory.spec 0).clientResult s p))) :
    ValidProg w F s (p >>= q) :=
  fun hm => (validHistory_bind' w p q s).mpr ⟨hp hm, hq (validMem_clientState hm hp)⟩

theorem validProg_seq {α β : Type} {w F : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {r : Memory.Prog β}
    (hp : ValidProg w F s p)
    (hr : ∀ s', ValidProg w F s' r) :
    ValidProg w F s (p >>= fun _ => r) :=
  validProg_bind hp (hr _)

theorem validProg_ite {α : Type} {w F : ℕ} {s : Memory.State} {c : Prop} [Decidable c]
    {p₁ p₂ : Memory.Prog α}
    (h₁ : c → ValidProg w F s p₁) (h₂ : ¬c → ValidProg w F s p₂) :
    ValidProg w F s (if c then p₁ else p₂) := by
  split_ifs with h
  · exact h₁ h
  · exact h₂ h

theorem validProg_iterate {δ σ : Type} {w F : ℕ}
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → δ × σ → Memory.State → Prop}
    {d : δ} (n : ℕ) (a : σ) (s : Memory.State)
    (hbody : ∀ a' s', safe w (d, a') s' → ValidProg w F s' (body (d, a')))
    (hsafe : iterationSafe body safe w d n a s) :
    ValidProg w F s (iterate body d n a) := by
  induction n generalizing a s with
  | zero => exact validProg_pure a
  | succ n ih =>
    exact validProg_bind (hbody a s hsafe.1) (ih _ _ hsafe.2)

theorem validProg_boundedWhile {δ σ : Type} {w F : ℕ}
    {guard : δ → σ → Prop} [∀ d a, Decidable (guard d a)]
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → δ × σ → Memory.State → Prop}
    {d : δ} (n : ℕ) (a : σ) (s : Memory.State)
    (hbody : ∀ a' s', safe w (d, a') s' → ValidProg w F s' (body (d, a')))
    (hsafe : whileSafe guard body safe w d n a s) :
    ValidProg w F s (boundedWhile guard body d n a) := by
  induction n generalizing a s with
  | zero => exact validProg_pure a
  | succ n ih =>
    unfold boundedWhile
    unfold whileSafe at hsafe
    split_ifs at hsafe ⊢ with hg
    · exact validProg_bind (hbody a s hsafe.1) (ih _ _ hsafe.2)
    · exact validProg_pure a

/-- Standard dictionary frontier `base + totalSpace U V w n_max h_space`. -/
@[wram_arith]
abbrev dictFrontier (U V w n_max h_space base : ℕ) : ℕ :=
  base + totalSpace U V w n_max h_space

theorem validProg_readQuot {U V w n_max h_space base idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readQuotProg U w n_max h_space (base, idx)) := by
  intro ⟨_, hf⟩
  exact validHistory_readPackedProg hw hidx (by wram_omega [hf])

theorem validProg_writeQuot {U V w n_max h_space base idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hidx : idx < n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeQuotProg U w n_max h_space ((base, idx), val)) := by
  intro ⟨hwf, hf⟩
  exact validHistory_writePackedProg hw (quotientBits_le_of_le_pow hU) hidx hwf (by wram_omega [hf])

theorem validProg_readVal {U V w n_max h_space base idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readValProg U V w n_max h_space (base, idx)) := by
  intro ⟨_, hf⟩
  exact validHistory_readPackedProg hw hidx (by wram_omega [hf])

theorem validProg_writeVal {U V w n_max h_space base idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hV : V ≤ 2 ^ w) (hidx : idx < n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeValProg U V w n_max h_space ((base, idx), val)) := by
  intro ⟨hwf, hf⟩
  exact validHistory_writePackedProg hw (Nat.clog_le_of_le_pow hV) hidx hwf (by wram_omega [hf])

theorem validProg_readLM {U V w n_max h_space c base idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hc : c < 9) (hidx : idx < totalMicroBuckets n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readLMProg U V w n_max h_space c (base, idx)) := by
  intro ⟨_, hf⟩
  have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
    Nat.mul_le_mul_right _ hc
  exact validHistory_readPackedProg hw hidx (by rw [Nat.add_one_mul] at hsub; wram_omega [hsub, hf])

theorem validProg_writeLM {U V w n_max h_space c base idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hc : c < 9)
    (hidx : idx < totalMicroBuckets n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeLMProg U V w n_max h_space c ((base, idx), val)) := by
  intro ⟨hwf, hf⟩
  have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
    Nat.mul_le_mul_right _ hc
  exact validHistory_writePackedProg hw (effBucketPosBits_le_of_lt_pow hnU hU) hidx hwf
    (by rw [Nat.add_one_mul] at hsub; wram_omega [hsub, hf])

theorem validProg_readGM {U V w n_max h_space base idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < globalMetaLen n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readGMProg U V w n_max h_space (base, idx)) := by
  intro ⟨_, hf⟩
  exact validHistory_readPackedProg hw hidx (by wram_omega [hf])

theorem validProg_bind_readGM_eq {α : Type} {U V w n_max h_space base idx v : ℕ} {s : Memory.State}
    {k : ℕ → Memory.Prog α}
    (hw : 0 < w) (hidx : idx < globalMetaLen n_max)
    (hval : gmAt base U V w n_max h_space s.mem idx = v)
    (hk : ValidProg w (dictFrontier U V w n_max h_space base) s (k v)) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readGMProg U V w n_max h_space (base, idx) >>= k) := by
  refine validProg_bind (validProg_readGM hw hidx) ?_
  rwa [clientState_readGMProg, clientResult_readGMProg s hidx, hval]

theorem validProg_writeGM {U V w n_max h_space base idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hidx : idx < globalMetaLen n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeGMProg U V w n_max h_space ((base, idx), val)) := by
  intro ⟨hwf, hf⟩
  exact validHistory_writePackedProg hw (globalPtrBits_le_of_lt_pow hnU hU) hidx hwf
    (by wram_omega [hf])

/-! ## Section 2: Slot resolution, tail pool, and slab pool operations -/

-- The remaining proofs compose the validity lemmas above. Keep unification from
-- unfolding the client history while matching a subprogram with its certificate.
attribute [local irreducible] ValidProg

attribute [local valid_prog]
  validProg_pure validProg_bind validProg_ite
  validProg_readQuot validProg_writeQuot validProg_readVal validProg_writeVal
  validProg_readLM validProg_writeLM validProg_readGM validProg_writeGM

theorem validProg_readBucketCount {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hb : d.2 < numBuckets n_max) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (readBucketCountProg U V w n_max h_space d) := by
  unfold readBucketCountProg
  split_ifs with hb0
  · exact validProg_readGM hw (by wram_omega)
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
    have hr_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
    valid_prog

/-- Base address `d.1.1` of a left-nested dictionary input `((base, idx), extra)`. -/
abbrev dictArgBase {α β : Type} (d : (ℕ × α) × β) : ℕ := d.1.1

/-- Primary index `d.1.2` (bucket or slab index) of a left-nested dictionary input
`((base, idx), extra)`. -/
abbrev dictArgIdx {β : Type} (d : (ℕ × ℕ) × β) : ℕ := d.1.2

/-- Loop-invariant environment `d.1.1` of an `iterate` input `((env, init), steps)`. -/
abbrev loopEnv {α β : Type} (d : (α × β) × ℕ) : α := d.1.1

/-- Initial accumulator `d.1.2` of an `iterate` input `((env, init), steps)`. -/
abbrev loopInit {α β : Type} (d : (α × β) × ℕ) : β := d.1.2

theorem validProg_resolveIndexedSlot {U V w n_max h_space : ℕ} {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w)
    (hinv : SlotStoreInv n_max (gmAt (dictArgBase d) U V w n_max h_space s.mem))
    (hb : dictArgIdx d < numBuckets n_max)
    (hj_bc : d.2 < bCount n_max (gmAt (dictArgBase d) U V w n_max h_space s.mem) (dictArgIdx d))
    (hj_cap : d.2 < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space (dictArgBase d)) s
      (resolveIndexedSlotProg U V w n_max h_space d) := by
  unfold resolveIndexedSlotProg
  split_ifs with hb0
  · exact validProg_pure _
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
    valid_prog with [clientState_readGMProg, clientResult_readGMProg]
    · have hs_dir : d.2 / slabSize n_max < dirSlabsPerBucket n_max := Nat.div_lt_of_lt_mul
        (by rw [Nat.mul_comm, ← effBucketCap_eq_dirSlabs_mul_slabSize hb_pos]; exact hj_cap)
      exact gmSlabDirIdx_lt hb_pos hb hs_dir
    · exact gmTailPtrIdx_lt hb_pos hb (hinv.tailOffset_lt hb_pos hb hj_bc ‹_›).2

theorem validProg_appendTailItem {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (htail : TailBijection n_max (gmAt d.1 U V w n_max h_space s.mem)
      (fun b => gmAt d.1 U V w n_max h_space s.mem (gmRIdx b))
      (gmAt d.1 U V w n_max h_space s.mem 1))
    (hb : d.2 < numBuckets n_max)
    (hr_lt : gmAt d.1 U V w n_max h_space s.mem (gmRIdx d.2) < tailCapPerBucket n_max) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (appendTailItemProg U V w n_max h_space d) := by
  obtain ⟨hr_idx, h1_idx, hptr_lt, hown_lt, -, -⟩ :=
    appendTailItem_bounds (V := V) (h_space := h_space) ⟨htail, hb, hr_lt, hb_pos⟩
  simp only [appendTailItemProg, appendTailItemGenProg, readGMGenProg_mk, writeGMGenProg_mk,
    p_tailCap_mk, p_gmTailPtrBase_mk, p_gmTailOwnerBase_mk]
  valid_prog

theorem validProg_removeLastTailItem {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (htail : TailBijection n_max (gmAt d.1 U V w n_max h_space s.mem)
      (fun b => gmAt d.1 U V w n_max h_space s.mem (gmRIdx b))
      (gmAt d.1 U V w n_max h_space s.mem 1))
    (hb : d.2 < numBuckets n_max)
    (hr_pos : 1 ≤ gmAt d.1 U V w n_max h_space s.mem (gmRIdx d.2)) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (removeLastTailItemProg U V w n_max h_space d) := by
  obtain ⟨hr_idx_lt, -, hptr_del_lt, h1_lt, -, hown_last_lt, -, -, hg_last_lt, hg_del_lt,
      hptr_last_lt, hown_del_lt⟩ :=
    removeLastTailItem_bounds (V := V) (h_space := h_space) ⟨htail, hb, hr_pos, hb_pos⟩
  simp only [removeLastTailItemProg, removeLastTailItemGenProg, readGMGenProg_mk,
    readQuotGenProg_mk, writeQuotGenProg_mk, readValGenProg_mk, writeValGenProg_mk,
    writeGMGenProg_mk, p_gmTailPtrBase_mk, p_tailCap_mk, p_gmTailOwnerBase_mk, p_nMaxSubOne_mk]
  valid_prog

theorem validProg_gmPushSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hslab : SlabBijection n_max (gmAt d.1 U V w n_max h_space s.mem)
      (fun b' => gmAt d.1 U V w n_max h_space s.mem (gmQIdx b'))
      (gmAt d.1 U V w n_max h_space s.mem 0))
    (hb : d.2 < numBuckets n_max)
    (hp_lt : gmAt d.1 U V w n_max h_space s.mem 0 < maxFullSlabs n_max) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (gmPushSlabProg U V w n_max h_space d) := by
  obtain ⟨hq_idx_lt, h0_lt, htop_idx_lt, hownB_lt, hownS_lt, hbel_lt, habv_lt, hdir_lt, -, -⟩ :=
    gmPushSlab_bounds (V := V) (h_space := h_space) ⟨hslab, hb, hp_lt, hb_pos⟩
  simp only [gmPushSlabProg, gmPushSlabGenProg, readGMGenProg_mk, writeGMGenProg_mk,
    p_gmSlabMetaBase_mk, p_dirSlabs_mk, p_gmSlabDirBase_mk]
  valid_prog

theorem validProg_gmUnlinkTopSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hslab : SlabBijection n_max (gmAt d.1 U V w n_max h_space s.mem)
      (fun b' => gmAt d.1 U V w n_max h_space s.mem (gmQIdx b'))
      (gmAt d.1 U V w n_max h_space s.mem 0))
    (hb : d.2 < numBuckets n_max)
    (hq_pos : 1 ≤ gmAt d.1 U V w n_max h_space s.mem (gmQIdx d.2)) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (gmUnlinkTopSlabProg U V w n_max h_space d) := by
  obtain ⟨hq_idx_lt, htop_idx_lt, hbel_idx_lt, -⟩ :=
    gmUnlinkTopSlab_bounds (V := V) (h_space := h_space) ⟨hslab, hb, hq_pos, hb_pos⟩
  simp only [gmUnlinkTopSlabProg, gmUnlinkTopSlabGenProg, readGMGenProg_mk, writeGMGenProg_mk,
    p_gmSlabMetaBase_mk]
  valid_prog

theorem validProg_gmRelinkMovedSlab {U V w n_max h_space : ℕ} {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hpre : GmMovedSlabInv U V w n_max h_space (dictArgBase d) (dictArgIdx d) d.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space (dictArgBase d)) s
      (gmRelinkMovedSlabProg U V w n_max h_space d) := by
  obtain ⟨hownB_last_lt, hownS_last_lt, hq_last_lt, hdir_lt, -, htop_lt⟩ :=
    gmRelinkMovedSlab_bounds hb_pos hpre
  simp only [gmRelinkMovedSlabProg, gmRelinkMovedSlabGenProg, readGMGenProg_mk,
    writeGMGenProg_mk, p_gmSlabMetaBase_mk, p_dirSlabs_mk, p_gmSlabDirBase_mk]
  valid_prog

theorem validProg_gmLinkMovedNeighbors {U V w n_max h_space : ℕ} {d : (ℕ × ℕ) × ℕ}
    {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hpre : GmMovedSlabInv U V w n_max h_space (dictArgBase d) (dictArgIdx d) d.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space (dictArgBase d)) s
      (gmLinkMovedNeighborsProg U V w n_max h_space d) := by
  obtain ⟨hownB_last_lt, hownS_last_lt, hbel_last_lt, habv_last_lt, hq_last_lt, habv_bel_lt, -,
      hbel_abv_lt, hownB_del_lt, hownS_del_lt, hbel_del_lt, habv_del_lt⟩ :=
    gmLinkMovedNeighbors_bounds hb_pos hpre
  simp only [gmLinkMovedNeighborsProg, gmLinkMovedNeighborsGenProg, readGMGenProg_mk,
    writeGMGenProg_mk, p_gmSlabMetaBase_mk]
  valid_prog

theorem validProg_gmCompactSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hpre : GmCompactSlabInv U V w n_max h_space d.1 d.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (gmCompactSlabProg U V w n_max h_space d) := by
  have h0_lt : 0 < globalMetaLen n_max := by wram_omega
  simp only [gmCompactSlabProg, gmCompactSlabGenProg, readGMGenProg_mk,
    gmRelinkMovedSlabGenProg_mk, gmLinkMovedNeighborsGenProg_mk, writeGMGenProg_mk]
  valid_prog with [clientState_readGMProg, clientResult_readGMProg]
  · exact validProg_gmRelinkMovedSlab (d := (d, _)) hw hnU hU hb_pos (hpre.2.2.2 ‹_›)
  · exact validProg_gmLinkMovedNeighbors (d := (d, _)) hw hnU hU hb_pos
      (gmMovedSlabInv_after_relink hw hb_pos (hpre.2.2.2 ‹_›))

theorem validProg_gmPopSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hslab : SlabBijection n_max (gmAt d.1 U V w n_max h_space s.mem)
      (fun b' => gmAt d.1 U V w n_max h_space s.mem (gmQIdx b'))
      (gmAt d.1 U V w n_max h_space s.mem 0))
    (hb : d.2 < numBuckets n_max)
    (hq_pos : 1 ≤ gmAt d.1 U V w n_max h_space s.mem (gmQIdx d.2)) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (gmPopSlabProg U V w n_max h_space d) := by
  simp only [gmPopSlabProg, gmPopSlabGenProg, gmUnlinkTopSlabGenProg_mk, gmCompactSlabGenProg_mk]
  refine validProg_bind (validProg_gmUnlinkTopSlab hw hnU hU hb_pos hslab hb hq_pos) ?_
  exact validProg_gmCompactSlab
    (d := (d.1,
      (Memory.spec 0).clientResult s (gmUnlinkTopSlabProg U V w n_max h_space (d.1, d.2))))
    hw hnU hU hb_pos (gmCompactSlabInv_of_slabBijection hw hb_pos hb s hslab hq_pos)

/-! ## Section 3: Slab promotion, demotion, and amortized slot operations -/

theorem validProg_promoteStep {U V w n_max h_space : ℕ} {x : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hpre : PromoteStepInv U V w n_max h_space (dictArgBase x) (dictArgIdx x) x.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space (dictArgBase x)) s
      (promoteStepProg U V w n_max h_space x) := by
  obtain ⟨-, -, hptr_u_lt, hptr_top_lt, h0_lt, -, -, hgu_lt, hgtop_lt, hgslab_lt, htail2,
      hr2_pos, -⟩ := promoteStep_bounds hw ⟨hpre, hb_pos⟩
  have hhb := hpre.1
  simp only [promoteStepProg, promoteStepGenProg, p_slabSizeSubOne_mk, p_slabSize_mk,
    p_gmTailPtrBase_mk, p_tailCap_mk, p_nMaxSubOne_mk, readGMGenProg_mk, readQuotGenProg_mk,
    readValGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk, removeLastTailItemGenProg_mk]
  valid_prog [validProg_removeLastTailItem]
  · exact htail2
  · exact hr2_pos

theorem validProg_promoteLoop {U V w n_max h_space : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hsafe : iterationSafe (promoteStepProg U V w n_max h_space)
      (fun w' x s' =>
        PromoteStepPre U V w n_max h_space w' (dictArgBase x) (dictArgIdx x) x.2 s')
      w (loopEnv d) d.2 (loopInit d) s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (promoteLoopProg U V w n_max h_space d) := by
  unfold promoteLoopProg
  exact validProg_iterate d.2 d.1.2 s
    (fun a' s' h => validProg_promoteStep (x := (d.1.1, a')) hw hnU hU hV hb_pos h.2.1) hsafe

/-- The parameter bounds recorded by `DictEnvGen` for concrete parameters `mkDictParams`. -/
private theorem dictEnvGen_mk_bounds {w' U V w n_max h_space base : ℕ}
    (h : DictEnvGen w' (mkDictParams U V w n_max h_space) base) :
    0 < w ∧ n_max ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w := by
  obtain ⟨U', V', w₀, n', _, hw, hnU, hU, hV, heq⟩ := h.params
  have hU' : U = U' := by simpa using congrArg dpU heq
  have hV' : V = V' := by simpa using congrArg dpV heq
  have hw' : w = w₀ := by simpa using congrArg dpW heq
  have hn' : n_max = n' := by simpa using congrArg dpNMax heq
  subst hU' hV' hw' hn'
  exact ⟨hw, hnU, hU, hV⟩

theorem validProg_promoteSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hb_pos : 0 < bucketBits n_max)
    (hdenv : DictEnvGen w (mkDictParams U V w n_max h_space) d.1)
    (hpre : PromoteSlabInv U V w n_max h_space d.1 d.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (promoteSlabProg U V w n_max h_space d) := by
  obtain ⟨hw, hnU, hU, hV⟩ := dictEnvGen_mk_bounds hdenv
  obtain ⟨hloopK, _, hsafe⟩ :=
    iterate_promoteStepProg_spec (w := w) hw hb_pos (slabSize n_max) 0 s
      (by omega) (promoteLoopInv_zero hpre)
  rw [Nat.zero_add] at hloopK
  let s₁ := (Memory.spec 0).clientState s
    (promoteLoopProg U V w n_max h_space ((d, 0), slabSize n_max))
  have hp_lt1 : gmAt d.1 U V w n_max h_space s₁.mem 0 < maxFullSlabs n_max := by
    have := hloopK.tot_le
    dsimp only [s₁, promoteLoopProg] at this ⊢
    rw [Prod.mk.eta] at this
    exact nslabs_lt_maxFullSlabs_of_mul_le hb_pos (by rw [Nat.add_one_mul]; omega)
  simp only [promoteSlabProg, promoteSlabGenProg, p_slabSize_mk, promoteLoopGenProg_mk,
    gmPushSlabGenProg_mk]
  exact validProg_bind
    (validProg_promoteLoop (d := ((d, 0), slabSize n_max)) hw hnU hU hV hb_pos (hsafe hdenv))
    (validProg_gmPushSlab (d := d) hw hnU hU hb_pos hloopK.slab_bij hloopK.b_lt hp_lt1)

theorem validProg_demoteStep {U V w n_max h_space : ℕ} {x : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hpre : DemoteStepInv U V w n_max h_space (dictArgBase x) (dictArgIdx x) x.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space (dictArgBase x)) s
      (demoteStepProg U V w n_max h_space x) := by
  obtain ⟨-, htop_idx_lt, h0_idx_lt, -, hg_del_lt, hg_last_lt, ⟨htail, hb, hr_cap, -⟩, -,
      hg_tail_lt, -⟩ := demoteStep_bounds hw ⟨hpre, hb_pos⟩
  simp only [demoteStepProg, demoteStepGenProg, p_slabSizeSubOne_mk, p_slabSize_mk,
    p_nMaxSubOne_mk, readGMGenProg_mk, readQuotGenProg_mk, readValGenProg_mk,
    writeQuotGenProg_mk, writeValGenProg_mk, appendTailItemGenProg_mk]
  valid_prog [validProg_appendTailItem]

theorem validProg_demoteLoop {U V w n_max h_space : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hsafe : iterationSafe (demoteStepProg U V w n_max h_space)
      (fun w' x s' =>
        DemoteStepPre U V w n_max h_space w' (dictArgBase x) (dictArgIdx x) x.2 s')
      w (loopEnv d) d.2 (loopInit d) s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (demoteLoopProg U V w n_max h_space d) := by
  unfold demoteLoopProg
  exact validProg_iterate d.2 d.1.2 s
    (fun a' s' h => validProg_demoteStep (x := (d.1.1, a')) hw hnU hU hV hb_pos h.2.1) hsafe

theorem validProg_demoteSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hdenv : DictEnvGen w (mkDictParams U V w n_max h_space) d.1)
    (hpre : DemoteSlabInv U V w n_max h_space d.1 d.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (demoteSlabProg U V w n_max h_space d) := by
  obtain ⟨hloopK, _, hsafe⟩ :=
    iterate_demoteStepProg_spec (w := w) hw hb_pos (slabSize n_max) 0 s
      (by omega) (demoteLoopInv_zero hpre)
  rw [Nat.zero_add] at hloopK
  simp only [demoteSlabProg, demoteSlabGenProg, p_slabSize_mk, demoteLoopGenProg_mk,
    gmPopSlabGenProg_mk]
  exact validProg_bind
    (validProg_demoteLoop (d := ((d, 0), slabSize n_max)) hw hnU hU hV hb_pos (hsafe hdenv))
    (validProg_gmPopSlab (d := d) hw hnU hU hb_pos hloopK.slab_bij hloopK.b_lt hloopK.qb_pos)

theorem validProg_lastSlotOf {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w)
    (hinv : SlotStoreInv n_max (gmAt d.1 U V w n_max h_space s.mem))
    (hb : d.2 < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (lastSlotOfProg U V w n_max h_space d) := by
  simp only [lastSlotOfProg, lastSlotOfGenProg, ite_bucketBits_mk, readGMGenProg_mk,
    p_gmTailPtrBase_mk, p_tailCap_mk, p_nMaxSubOne_mk]
  split_ifs with hb0
  · exact validProg_bind (validProg_readGM hw (by wram_omega)) (validProg_pure _)
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hr_idx_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
    have hr_pos := pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
    have hcap := (hinv.multi_r_bounds hb_pos d.2 hb).1
    valid_prog with [clientState_readGMProg, clientResult_readGMProg]
    exact gmTailPtrIdx_lt hb_pos hb (by wram_omega [hcap, hr_pos])

theorem validProg_pushBackTailWrite {U V w n_max h_space : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hinv : SlotStoreInv n_max (gmAt (bucketCallBase d) U V w n_max h_space s.mem))
    (hb : bucketCallBucket d < numBuckets n_max)
    (htot : totalSlots n_max (gmAt (bucketCallBase d) U V w n_max h_space s.mem) < n_max) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (pushBackTailWriteProg U V w n_max h_space d) := by
  have htail₀ := hinv.multi_tail hb_pos
  have hr_lt := (hinv.multi_r_bounds hb_pos d.1.1.2 hb).1
  have hres_app := (appendTailItemProg_effect (U := U) (V := V) (h_space := h_space)
    hw hb_pos hb s htail₀ hr_lt).1
  have hg_new_lt : (n_max - 1) - gmAt d.1.1.1 U V w n_max h_space s.mem 1 < n_max := by omega
  have hr_idx_lt : 4 + 3 * d.1.1.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  simp only [pushBackTailWriteProg, pushBackTailWriteGenProg, p_nMaxSubOne_mk,
    appendTailItemGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk, readGMGenProg_mk]
  valid_prog [validProg_appendTailItem] with [hres_app]

theorem validProg_pushBackSlot {U V w n_max h_space : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hpre : PushBackSlotPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (pushBackSlotProg U V w n_max h_space d) := by
  rcases d with ⟨⟨⟨base', b'⟩, q_val⟩, v_val⟩
  rcases hpre with ⟨hdenv, hinv, hb, htot, hq_lt, hv_lt⟩
  simp only [pushBackSlotProg, pushBackSlotGenProg, ite_bucketBits_mk, p_twoSlabSize_mk,
    readGMGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk, writeGMGenProg_mk,
    pushBackTailWriteGenProg_mk, promoteSlabGenProg_mk]
  split_ifs with hb0
  · have h0_lt : 0 < globalMetaLen n_max := by wram_omega
    have hc_lt : gmAt base' U V w n_max h_space s.mem 0 < n_max := by
      simpa [totalSlots, hb0] using htot
    valid_prog with [clientState_readGMProg, clientResult_readGMProg]
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have htot0_lt : gmAt base' U V w n_max h_space s.mem 0 * slabSize n_max +
        gmAt base' U V w n_max h_space s.mem 1 < n_max := by
      simpa [totalSlots, hb0] using htot
    let s₁ := (Memory.spec 0).clientState s
      (pushBackTailWriteProg U V w n_max h_space (((base', b'), q_val), v_val))
    obtain ⟨hres1, _, _, _, _, htail1, hslab1, htot1, _, hrb1, hother1, _⟩ :=
      pushBackTailWriteProg_effect (U := U) (V := V) (h_space := h_space)
        hw hb_pos s hinv hb htot hq_lt hv_lt
    refine validProg_bind
      (validProg_pushBackTailWrite (d := (((base', b'), q_val), v_val))
        hw hnU hU hV hb_pos hinv hb htot) ?_
    refine validProg_ite (fun hc => ?_) (fun _ => validProg_pure ())
    rw [hres1] at hc
    have htot1_le : gmAt base' U V w n_max h_space s₁.mem 0 * slabSize n_max +
        gmAt base' U V w n_max h_space s₁.mem 1 ≤ n_max := by
      dsimp only [s₁] at htot1 ⊢; omega
    have hpre_prom : PromoteSlabInv U V w n_max h_space base' b' s₁ :=
      promoteSlabInv_of_other_and_tail hb_pos hinv hb htail1 hslab1 (by rw [hrb1, hc])
        hother1 htot1_le
    exact validProg_promoteSlab (d := (base', b')) hb_pos hdenv hpre_prom

theorem validProg_popBackSlot {U V w n_max h_space : ℕ}
    {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hpre : PopBackSlotPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (popBackSlotProg U V w n_max h_space d) := by
  rcases d with ⟨base', b'⟩
  rcases hpre with ⟨hdenv, hinv, hb, hbc⟩
  simp only [popBackSlotProg, popBackSlotGenProg, ite_bucketBits_mk, readGMGenProg_mk,
    writeGMGenProg_mk, removeLastTailItemGenProg_mk, demoteSlabGenProg_mk]
  split_ifs with hb0
  · have h0_lt : 0 < globalMetaLen n_max := by wram_omega
    valid_prog
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hr0_pos := pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
    have htot₀ := hinv.multi_total_le hb_pos
    obtain ⟨_, _, _, htail1, hslab1, htot1, _, _, hother1, -⟩ :=
      popBackTailRemove_effect (U := U) (V := V) (h_space := h_space) hw hb_pos s hinv hb hbc
    have hr_idx_lt : 4 + 3 * b' + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
    have hq_idx_lt : 4 + 3 * b' < globalMetaLen n_max := gmQIdx_lt hb_pos hb
    refine validProg_bind
      (validProg_removeLastTailItem (d := (base', b')) hw hnU hU hV hb_pos
        (hinv.multi_tail hb_pos) hb hr0_pos) ?_
    generalize
      (Memory.spec 0).clientState s (removeLastTailItemProg U V w n_max h_space (base', b')) = s₁
      at htail1 hslab1 htot1 hother1 ⊢
    valid_prog with [clientState_readGMProg,
      clientResult_readGMProg s₁ hr_idx_lt, clientResult_readGMProg s₁ hq_idx_lt]
    have htot1_le : gmAt base' U V w n_max h_space s₁.mem 0 * slabSize n_max +
        gmAt base' U V w n_max h_space s₁.mem 1 ≤ n_max := by dsimp only at htot₀ htot1 ⊢; omega
    refine validProg_demoteSlab (d := (base', b')) hw hnU hU hV hb_pos hdenv
      ⟨hb, htail1, hslab1, ‹_›, ‹_›, fun b'' hb'' hne => ?_, htot1_le⟩
    rw [(hother1 b'' hb'' hne).1, (hother1 b'' hb'' hne).2]
    exact hinv.multi_r_bounds hb_pos b'' hb''

/-! ## Section 4: Micro-Chain Accessors, Prepend/Unlink, and Search Loops -/

-- Specialize parameter projections through their named equations rather than reducing the
-- packed layout when comparing programs and intermediate states.
attribute [local irreducible] mkDictParams

theorem validProg_readLMHead {U V w n_max h_space base b m : ℕ}
    (hw : 0 < w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readLMHeadProg U V w n_max h_space ((base, b), m)) := by
  simp only [readLMHeadProg, readLMHeadGenProg, p_numMicro_mk, readLMGenProg_mk]
  exact validProg_readLM hw (by decide) (lmHeadIdx_lt hb hm)

theorem validProg_writeLMHead {U V w n_max h_space base b m v : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeLMHeadProg U V w n_max h_space (((base, b), m), v)) := by
  simp only [writeLMHeadProg, writeLMHeadGenProg, p_numMicro_mk, writeLMGenProg_mk]
  exact validProg_writeLM hw hnU hU (by decide) (lmHeadIdx_lt hb hm)

theorem validProg_readLMMod4 {U V w n_max h_space c_base base b j : ℕ}
    (hw : 0 < w) (hc : c_base + 3 < 9) {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readLMMod4Prog U V w n_max h_space c_base ((base, b), j)) := by
  simp only [readLMMod4Prog]
  simp only [pure_bind]
  split_ifs <;> exact validProg_readLM hw (by omega) (lmSlotIdx_lt hb hj)

theorem validProg_writeLMMod4 {U V w n_max h_space c_base base b j v : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hc : c_base + 3 < 9)
    {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeLMMod4Prog U V w n_max h_space c_base (((base, b), j), v)) := by
  simp only [writeLMMod4Prog]
  simp only [pure_bind]
  split_ifs <;> exact validProg_writeLM hw hnU hU (by omega) (lmSlotIdx_lt hb hj)

theorem validProg_readLMPrev {U V w n_max h_space base b j : ℕ}
    (hw : 0 < w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readLMPrevProg U V w n_max h_space ((base, b), j)) :=
  validProg_readLMMod4 hw (by decide) hb hj

theorem validProg_writeLMPrev {U V w n_max h_space base b j v : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeLMPrevProg U V w n_max h_space (((base, b), j), v)) :=
  validProg_writeLMMod4 hw hnU hU (by decide) hb hj

theorem validProg_readLMNext {U V w n_max h_space base b j : ℕ}
    (hw : 0 < w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readLMNextProg U V w n_max h_space ((base, b), j)) :=
  validProg_readLMMod4 hw (by decide) hb hj

theorem validProg_writeLMNext {U V w n_max h_space base b j v : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeLMNextProg U V w n_max h_space (((base, b), j), v)) :=
  validProg_writeLMMod4 hw hnU hU (by decide) hb hj

theorem validProg_lmPrepend {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : LMPrependPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (lmPrependProg U V w n_max h_space d) := by
  rcases d with ⟨⟨⟨base, b⟩, m⟩, j⟩
  rcases hpre with ⟨_, hb, hm, hj, _, hold⟩
  dsimp only [lmEntryBase, lmEntryBucket, lmEntryIdx] at hb hm hj hold
  simp only [lmPrependProg, lmPrependGenProg, lmWriteLoc, lmWriteVal, lmWriteHeadArg,
    readLMHeadGenProg_mk, writeLMPrevGenProg_mk, writeLMNextGenProg_mk, writeLMHeadGenProg_mk,
    pure_bind]
  valid_prog [validProg_readLMHead, validProg_writeLMPrev, validProg_writeLMNext,
    validProg_writeLMHead] with [clientState_readLMHeadProg, clientResult_readLMHeadProg]
  omega

theorem validProg_lmUnlink {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : LMUnlinkPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (lmUnlinkProg U V w n_max h_space d) := by
  rcases d with ⟨⟨⟨base, b⟩, m⟩, j⟩
  rcases hpre with ⟨_, hb, hm, hj, hp, hn⟩
  dsimp only [lmEntryBase, lmEntryBucket, lmEntryIdx] at hb hm hj hp hn
  simp only [lmUnlinkProg, lmUnlinkGenProg, lmWriteLoc, lmWriteVal, lmWriteHeadArg,
    readLMPrevGenProg_mk, readLMNextGenProg_mk, writeLMNextGenProg_mk, writeLMHeadGenProg_mk,
    writeLMPrevGenProg_mk, pure_bind]
  valid_prog [validProg_readLMPrev, validProg_readLMNext, validProg_writeLMNext,
    validProg_writeLMHead, validProg_writeLMPrev]
    with [clientState_readLMPrevProg, clientResult_readLMPrevProg,
      clientState_readLMNextProg, clientResult_readLMNextProg]
  all_goals omega

theorem validProg_microStep {U V w n_max h_space : ℕ}
    (hw : 0 < w) {x : (((ℕ × ℕ) × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)} {s : Memory.State}
    (hpre : MicroStepPre U V w n_max h_space w x s) :
    ValidProg w (dictFrontier U V w n_max h_space (nestedCallBase x)) s
      (microStepProg U V w n_max h_space x) := by
  rcases hpre with ⟨_, hb, _, hj_cap, hj_bc, hinv⟩
  dsimp only [microStepBase, microStepBucket, microStepPtr] at hb hj_cap hj_bc hinv
  have hphys_lt := (slotOf_lt_and_injective hinv).1 x.1.1.1.2 hb (x.2.1.1.1 - 1) hj_bc
  simp only [microStepProg, microStepGenProg, microLoopCtxParams, microStepGenLoc,
    microStepGenBase, microStepGenQuot, microStepQuery, microStepPtr, microStepMatchIdx,
    microStepPhys, readLMNextGenProg_mk, resolveIndexedSlotGenProg_mk, readQuotGenProg_mk,
    pure_bind]
  valid_prog [validProg_readLMNext]
    with [clientState_readLMNextProg, clientState_resolveIndexedSlotProg,
      clientResult_resolveIndexedSlotProg]
  exact validProg_resolveIndexedSlot (d := (x.1.1.1, x.2.1.1.1 - 1)) hw hinv hb hj_bc hj_cap

theorem validProg_microLoop {U V w n_max h_space : ℕ}
    (hw : 0 < w) {x : (((ℕ × ℕ) × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)} {s : Memory.State}
    (hsafe : whileSafe microLoopGuard (microStepProg U V w n_max h_space)
      (MicroStepPre U V w n_max h_space) w x.1 (effBucketCap n_max) x.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space (nestedCallBase x)) s
      (microLoopProg U V w n_max h_space x) := by
  simp only [microLoopProg, microLoopGenProg, microLoopCtxParams, microStepQuery, microStepTag,
    p_nMax_mk, boundedWhile_microStepGenProg_mk]
  exact validProg_boundedWhile (effBucketCap n_max) x.2 s
    (fun a' s' h => validProg_microStep (x := (x.1, a')) hw h) hsafe

theorem validProg_searchMicroChain {U V w n_max h_space : ℕ}
    (hw : 0 < w) {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchMicroChainPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (searchMicroChainProg U V w n_max h_space d) := by
  rcases hpre with ⟨henv, hb, hm, hinv, L, hchain, hc_lt⟩
  simp only [searchMicroChainProg, searchMicroChainGenProg, lmWriteLoc, lmWriteVal,
    lmWriteHeadArg, readLMHeadGenProg_mk, microLoopGenProg_mk, pure_bind]
  refine validProg_bind (validProg_readLMHead hw hb hm) ?_
  rw [clientState_readLMHeadProg, clientResult_readLMHeadProg s hb hm]
  exact validProg_microLoop
    (x := ((d.1, 0),
      (((lmHead n_max (lmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2 d.2, 0), 0), 0)))
    hw (searchMicroChainProg_spec henv hb hm hinv hchain hc_lt).2.2.1

theorem validProg_resolveOvfStep {U V w n_max h_space : ℕ}
    {d : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hpre : ResolveOvfStepPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (dictArgBase d)) s
      (resolveOvfStepProg U V w n_max h_space d) := by
  rcases hpre with ⟨henv, hb, hj_bc, hinv, hp, hb_pos⟩
  have hw := (dictEnvGen_mk_bounds henv).1
  have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  unfold resolveOvfStepProg
  simp only [pure_bind]
  valid_prog with [clientState_readGMProg, clientResult_readGMProg]
  · have hs_lt : d.2.1 / slabSize n_max <
        gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) :=
      (Nat.div_lt_iff_lt_mul (slabSize_pos n_max)).2 ‹_›
    exact gmSlabAboveIdx_lt hb_pos
      ((hp ‹_›) ▸ (hinv.multi_slab hb_pos).ptr_lt_maxFullSlabs hb hs_lt)
  · exact gmTailPtrIdx_lt hb_pos hb (hinv.tailOffset_lt hb_pos hb hj_bc ‹_›).2

theorem validProg_ovfStep {U V w n_max h_space : ℕ}
    (hw : 0 < w) (_hb_pos : 0 < bucketBits n_max)
    {x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)} {s : Memory.State}
    (hpre : OvfStepPre U V w n_max h_space w x s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase x)) s
      (ovfStepProg U V w n_max h_space x) := by
  rcases hpre with ⟨henv, hb, hj_bc, hinv, hp, hb_pos⟩
  unfold ovfStepProg
  simp only [pure_bind]
  refine validProg_bind
    (validProg_resolveOvfStep (d := (x.1.1, x.2.1.1.1)) ⟨henv, hb, hj_bc, hinv, hp, hb_pos⟩) ?_
  rw [clientState_resolveOvfStepProg,
    (clientResult_resolveOvfStepProg (d := (x.1.1, x.2.1.1.1)) s hb_pos hb hj_bc hinv hp).1]
  have hphys_lt := (slotOf_lt_and_injective hinv).1 x.1.1.2 hb x.2.1.1.1.1 hj_bc
  valid_prog

theorem validProg_ovfLoop {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    {d : (((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) × ℕ} {s : Memory.State}
    (hsafe : iterationSafe (ovfStepProg U V w n_max h_space)
      (OvfStepPre U V w n_max h_space) w (loopEnv d) d.2 (loopInit d) s) :
    ValidProg w (dictFrontier U V w n_max h_space (nestedCallBase d)) s
      (ovfLoopProg U V w n_max h_space d) := by
  unfold ovfLoopProg
  exact validProg_iterate d.2 d.1.2 s
    (fun a' s' h => validProg_ovfStep (x := (d.1.1, a')) hw hb_pos h) hsafe

theorem validProg_initOvfSearch {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    {d : ℕ × ℕ} {s : Memory.State}
    (hb : d.2 < numBuckets n_max)
    (hinv : SlotStoreInv n_max (gmAt d.1 U V w n_max h_space s.mem)) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (initOvfSearchProg U V w n_max h_space d) := by
  have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  have hr_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  have hbc_eq : gmAt d.1 U V w n_max h_space s.mem (4 + 3 * d.2) * slabSize n_max +
      gmAt d.1 U V w n_max h_space s.mem (4 + 3 * d.2 + 1) =
      bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2 := by
    unfold bCount gmQIdx gmRIdx; simp [Nat.ne_of_gt hb_pos, hb]
  have hbc_le := bCount_le_n_max hinv d.2
  unfold initOvfSearchProg
  simp only [pure_bind]
  valid_prog with [clientState_readGMProg, clientResult_readGMProg, hbc_eq]
  · have : min n_max (effBucketCap n_max) = effBucketCap n_max := by omega
    exact (hinv.lastDirSlab_ptr hb_pos hb (by unfold gmQIdx; omega)).1
  · have : min n_max (effBucketCap n_max) = effBucketCap n_max := by omega
    obtain ⟨hdir_lt, hp_prev_eq, hp_prev_lt_max⟩ :=
      hinv.lastDirSlab_ptr hb_pos hb (by unfold gmQIdx; omega)
    rw [clientResult_readGMProg s hdir_lt, hp_prev_eq]
    exact gmSlabAboveIdx_lt hb_pos hp_prev_lt_max

theorem validProg_searchOverflow {U V w n_max h_space : ℕ}
    (hw : 0 < w) {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchOverflowPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (dictArgBase d)) s
      (searchOverflowProg U V w n_max h_space d) := by
  rcases hpre with ⟨henv, hb, hinv⟩
  unfold searchOverflowProg
  by_cases hb0 : bucketBits n_max = 0 <;> simp only [hb0, ↓reduceIte, pure_bind]
  · exact validProg_pure _
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    refine validProg_bind (validProg_initOvfSearch (d := d.1) hw hb_pos hb hinv) ?_
    rw [clientState_initOvfSearchProg]
    exact validProg_bind
      (validProg_ovfLoop
        (d := ((d, ((((min n_max (effBucketCap n_max),
          ((Memory.spec 0).clientResult s (initOvfSearchProg U V w n_max h_space d.1)).1), 0), 0),
          0)), ((Memory.spec 0).clientResult s (initOvfSearchProg U V w n_max h_space d.1)).2))
        hw hb_pos ((searchOverflowProg_spec henv hb hinv).2.2.1 hb_pos))
      (validProg_pure _)

theorem validProg_searchBucket {U V w n_max h_space : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchMicroChainPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (searchBucketProg U V w n_max h_space d) := by
  have hw := (dictEnvGen_mk_bounds hpre.1).1
  obtain ⟨L, hchain, hc_lt⟩ := hpre.2.2.2.2
  unfold searchBucketProg
  simp only [pure_bind]
  refine validProg_bind (validProg_searchMicroChain hw hpre) ?_
  rw [(searchMicroChainProg_spec hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hchain hc_lt).1]
  exact validProg_ite (fun _ => validProg_pure _)
    (fun _ => validProg_searchOverflow (d := d.1) hw ⟨hpre.1, hpre.2.1, hpre.2.2.2.1⟩)

private theorem searchBucket_found_slot_lt {U V w n_max h_space : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchMicroChainPre U V w n_max h_space w d s)
    (hf1 : ((Memory.spec 0).clientResult s (searchBucketProg U V w n_max h_space d)).1.1 = 1) :
    ((Memory.spec 0).clientResult s (searchBucketProg U V w n_max h_space d)).2 < n_max := by
  obtain ⟨L, hchain, hc_lt⟩ := hpre.2.2.2.2
  have hspec := (searchBucketProg_spec hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hchain hc_lt).2.2
  dsimp only [ovfQueryBase, ovfQueryBucket, ovfQueryQuot, ovfSearchFound,
    ovfSearchIdx] at hspec
  split_ifs at hspec with hex
  · rw [hspec.2.2.2.2]
    exact (slotOf_lt_and_injective hpre.2.2.2.1).1 d.1.1.2 hpre.2.1 _ hspec.2.1
  · omega

theorem validProg_queryBody {U V w n_max h_space : ℕ}
    (hw : 0 < w) {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchMicroChainPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (queryBodyProg U V w n_max h_space d) := by
  obtain ⟨L, hchain, hc_lt⟩ := hpre.2.2.2.2
  unfold queryBodyProg
  simp only [pure_bind]
  refine validProg_bind (validProg_searchBucket hpre) ?_
  rw [(searchBucketProg_spec hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hchain hc_lt).1]
  exact validProg_ite
    (fun hf1 => validProg_bind (validProg_readVal hw (searchBucket_found_slot_lt hpre hf1))
      (validProg_pure _))
    (fun _ => validProg_pure _)

/-! ## Section 5: Chain Prepend/Unlink, Insert, and Delete Operations -/

theorem validProg_prependIfIndexed {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : PrependIfIndexedPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (prependIfIndexedProg U V w n_max h_space d) := by
  rcases hpre with ⟨hdenv, hb, hm, hold⟩
  simp only [prependIfIndexedProg, prependIfIndexedGenProg, p_minCap_mk, lmPrependGenProg_mk,
    pure_bind]
  exact validProg_ite
    (fun hj_min => validProg_lmPrepend (d := d) hw hnU hU ⟨hdenv, hb, hm, by omega, by omega, hold⟩)
    (fun _ => validProg_pure ())

theorem validProg_unlinkIfIndexed {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : UnlinkIfIndexedPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (unlinkIfIndexedProg U V w n_max h_space d) := by
  rcases hpre with ⟨hdenv, hb, hm, hbound⟩
  simp only [unlinkIfIndexedProg, unlinkIfIndexedGenProg, p_minCap_mk, lmUnlinkGenProg_mk,
    pure_bind]
  refine validProg_ite (fun hj_min => ?_) (fun _ => validProg_pure ())
  have hj_cap : d.2 < effBucketCap n_max := by omega
  rcases hbound hj_cap with ⟨hp, hn⟩
  exact validProg_lmUnlink (d := d) hw hnU hU ⟨hdenv, hb, hm, hj_cap, hp, hn⟩

theorem validProg_readTotalSlots {U V w n_max h_space : ℕ}
    (hw : 0 < w) {base : ℕ} {s : Memory.State} :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readTotalSlotsProg U V w n_max h_space base) := by
  simp only [readTotalSlotsProg, readTotalSlotsGenProg, ite_bucketBits_mk, readGMGenProg_mk,
    p_slabSize_mk, pure_bind]
  have h0_lt : 0 < globalMetaLen n_max := by wram_omega
  have h1_lt : 1 < globalMetaLen n_max := by wram_omega
  split_ifs <;> valid_prog

theorem validProg_copyLastPayload {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hpre : CopyLastPayloadPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (dictArgBase d)) s
      (copyLastPayloadProg U V w n_max h_space d) := by
  rcases hpre with ⟨_, hinv, hb, hbc, hdst⟩
  have hsrc : slotOf n_max (gmAt d.1.1 U V w n_max h_space s.mem) d.1.2
      (bCount n_max (gmAt d.1.1 U V w n_max h_space s.mem) d.1.2 - 1) < n_max :=
    (slotOf_lt_and_injective hinv).1 d.1.2 hb _ (by omega)
  simp only [copyLastPayloadProg, copyLastPayloadGenProg, lastSlotOfGenProg_mk, readQuotGenProg_mk,
    readValGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk]
  valid_prog [validProg_lastSlotOf]
    with [clientState_lastSlotOfProg, clientResult_lastSlotOfProg,
      clientState_readQuotProg, clientState_readValProg]

theorem validProg_insertNew {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : InsertNewPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (nestedCallBase d)) s
      (insertNewProg U V w n_max h_space d) := by
  rcases hpre with ⟨hdenv, hb, hm, hq_lt, hv_lt, hinv, hold⟩
  simp only [insertNewProg, insertNewGenProg, readTotalSlotsGenProg_mk, p_nMax_mk,
    readBucketCountGenProg_mk, pushBackSlotGenProg_mk, prependIfIndexedGenProg_mk, pure_bind]
  refine validProg_bind (validProg_readTotalSlots hw) ?_
  rw [clientState_readTotalSlotsProg, clientResult_readTotalSlotsProg]
  refine validProg_ite (fun htot => ?_) (fun _ => validProg_pure ())
  refine validProg_bind (validProg_readBucketCount (d := d.1.1.1) hw hb) ?_
  rw [clientState_readBucketCountProg]
  refine validProg_bind
    (validProg_pushBackSlot (d := d.1) hw hnU hU hV ⟨hdenv, hinv, hb, htot, hq_lt, hv_lt⟩) ?_
  have eff := pushBackSlotProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (q_val := d.1.1.2)
    (v_val := d.1.2) hw s hinv hb htot hq_lt hv_lt
  exact validProg_prependIfIndexed
    (d := ((d.1.1.1, d.2), (Memory.spec 0).clientResult s
      (readBucketCountProg U V w n_max h_space d.1.1.1)))
    hw hnU hU ⟨hdenv, hb, hm, eff.2.2.1 ▸ hold⟩

theorem validProg_insertBody {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : InsertBodyPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (nestedCallBase d)) s
      (insertBodyProg U V w n_max h_space d) := by
  rcases hpre with ⟨hsb_pre, hq_lt, hv_lt⟩
  obtain ⟨L, hchain, hc_lt⟩ := hsb_pre.2.2.2.2
  simp only [insertBodyProg, insertBodyGenProg, searchBucketGenProg_mk, writeValGenProg_mk,
    insertNewGenProg_mk, pure_bind]
  refine validProg_bind (validProg_searchBucket (d := (d.1.1, d.2)) hsb_pre) ?_
  rw [(searchBucketProg_spec hsb_pre.1 hsb_pre.2.1 hsb_pre.2.2.1 hsb_pre.2.2.2.1 hchain hc_lt).1]
  exact validProg_ite
    (fun hf1 => validProg_writeVal hw hV (searchBucket_found_slot_lt hsb_pre hf1))
    (fun _ => validProg_insertNew (d := d) hw hnU hU hV
      ⟨hsb_pre.1, hsb_pre.2.1, hsb_pre.2.2.1, hq_lt, hv_lt, hsb_pre.2.2.2.1, hchain.head_le_cap⟩)

theorem validProg_deletePrep {U V w n_max h_space : ℕ}
    (hw : 0 < w) {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchMicroChainPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (bucketCallBase d)) s
      (deletePrepProg U V w n_max h_space d) := by
  obtain ⟨L, hchain, hc_lt⟩ := hpre.2.2.2.2
  simp only [deletePrepProg, deletePrepGenProg, searchBucketGenProg_mk, lastSlotOfGenProg_mk,
    readQuotGenProg_mk, pure_bind]
  refine validProg_bind (validProg_searchBucket (d := d) hpre) ?_
  rw [(searchBucketProg_spec hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hchain hc_lt).1]
  refine validProg_ite (fun hf1 => ?_) (fun _ => validProg_pure _)
  have hbc := searchBucketProg_found_imp_pos_bCount hpre hf1
  refine validProg_bind (validProg_lastSlotOf (d := d.1.1) hw hpre.2.2.2.1 hpre.2.1 hbc) ?_
  rw [clientState_lastSlotOfProg, clientResult_lastSlotOfProg d.1.1 s hpre.2.2.2.1 hpre.2.1 hbc]
  have hlast_lt : slotOf n_max (gmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2
      (bCount n_max (gmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2 - 1) < n_max :=
    (slotOf_lt_and_injective hpre.2.2.2.1).1 d.1.1.2 hpre.2.1 _
      (by dsimp only [lmEntryBase, lmEntryBucket]; omega)
  exact validProg_bind (validProg_readQuot hw hlast_lt) (validProg_pure _)

theorem validProg_deleteSwap {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hpre : DeleteSwapPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (nestedCallBase d)) s
      (deleteSwapProg U V w n_max h_space d) := by
  obtain ⟨L, hval, hmem_if⟩ := hpre.2.2.2.2.2.2.2
  have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.2.2)
    hw hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.2.2.1 hval hmem_if
  let s₁ := (Memory.spec 0).clientState s
    (unlinkIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.1), d.2.2))
  have hslot₁ : SlotStoreInv n_max (gmAt d.1.1.1.1 U V w n_max h_space s₁.mem) :=
    eff_u.2.2.2.2.1 ▸ hpre.2.1
  have hbc₁ : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w n_max h_space s₁.mem) d.1.1.1.2 :=
    eff_u.2.2.2.2.1 ▸ hpre.2.2.2.2.1
  have eff_c := copyLastPayloadProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (phys_del := d.1.2)
    hw hslot₁ hpre.2.2.1 hbc₁ hpre.2.2.2.2.2.1
  obtain ⟨L₁, hval₁, _⟩ := eff_u.2.2.2.2.2
  simp only [deleteSwapProg, deleteSwapGenProg, unlinkIfIndexedGenProg_mk,
    copyLastPayloadGenProg_mk, prependIfIndexedGenProg_mk]
  refine validProg_bind (validProg_unlinkIfIndexed (d := ((d.1.1.1, d.2.1), d.2.2))
    hw hnU hU (unlinkIfIndexedPre_of_allChainsValid hpre.1 hpre.2.2.1 hpre.2.2.2.1 hval hmem_if)) ?_
  refine validProg_bind (validProg_copyLastPayload (d := (d.1.1.1, d.1.2))
    hw hU hV ⟨hpre.1, hslot₁, hpre.2.2.1, hbc₁, hpre.2.2.2.2.2.1⟩) ?_
  exact validProg_prependIfIndexed (d := ((d.1.1.1, d.2.1), d.1.1.2)) hw hnU hU
    ⟨hpre.1, hpre.2.2.1, hpre.2.2.2.1, eff_c.2.2.2.2.1 ▸
      (hval₁.1 d.1.1.1.2 hpre.2.2.1 d.2.1 hpre.2.2.2.1).head_le_cap⟩

theorem validProg_deleteFound {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hpre : DeleteFoundPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (nestedCallBase d)) s
      (deleteFoundProg U V w n_max h_space d) := by
  dsimp only [DeleteFoundPre, nestedCallBase, nestedCallBucket, deleteSlotIdx,
    deleteSlotPhys, deleteFoundMicro, deleteFoundLastMicro] at hpre
  obtain ⟨L, hval, hmem_del, hmem_last⟩ := hpre.2.2.2.2.2.2.2
  have hj_n : d.1.1.2 < n_max :=
    lt_of_lt_of_le hpre.2.2.2.2.2.1 (bCount_le_n_max hpre.2.1 d.1.1.1.2)
  have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.1.1.2)
    hw hpre.2.2.1 hpre.2.2.2.1 hj_n hval hmem_del
  let s₁ := (Memory.spec 0).clientState s
    (unlinkIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.1), d.1.1.2))
  have hbc_pos : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w n_max h_space s.mem) d.1.1.1.2 := by
    have := hpre.2.2.2.2.2.1; omega
  simp only [deleteFoundProg, deleteFoundGenProg, unlinkIfIndexedGenProg_mk,
    readBucketCountGenProg_mk, deleteSwapGenProg_mk, popBackSlotGenProg_mk,
    nestedCallPair, deleteFoundMicro, deleteSlotIdx, deleteSlotTarget, deleteFoundLastMicro,
    pure_bind]
  refine validProg_bind (validProg_unlinkIfIndexed (d := ((d.1.1.1, d.2.1), d.1.1.2)) hw hnU hU
    (unlinkIfIndexedPre_of_allChainsValid hpre.1 hpre.2.2.1 hpre.2.2.2.1 hval hmem_del)) ?_
  refine validProg_bind (validProg_readBucketCount (d := d.1.1.1) hw hpre.2.2.1) ?_
  rw [clientState_readBucketCountProg,
    clientResult_readBucketCountProg d.1.1.1 s₁ hpre.2.2.1, eff_u.2.2.2.2.1]
  refine validProg_ite (fun hc => ?_) (fun _ => ?_)
  · obtain ⟨L₁, hval₁, hmem₁⟩ := eff_u.2.2.2.2.2
    let j_last := bCount n_max (gmAt d.1.1.1.1 U V w n_max h_space s.mem) d.1.1.1.2 - 1
    have hj_last_n : j_last < n_max := by
      have := bCount_le_n_max hpre.2.1 d.1.1.1.2; omega
    have hmem_last₁ : j_last < effBucketCap n_max → j_last ∈ L₁ d.1.1.1.2 d.2.2 :=
      fun hj_cap => (hmem₁ d.1.1.1.2 hpre.2.2.1 d.2.2 hpre.2.2.2.2.1 j_last).mpr
        ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩
    have hsw_eff := deleteSwapProg_effect (U := U) (V := V) (w₀ := w) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (j_del := d.1.1.2)
      (phys_del := d.1.2) (m_last := d.2.2) (j_last := j_last) (s := s₁) hw
      (by rw [eff_u.2.2.2.2.1]; exact hpre.2.1) hpre.2.2.1 hpre.2.2.2.2.1
      (by rw [eff_u.2.2.2.2.1]; exact hbc_pos) hpre.2.2.2.2.2.2.1 hj_n hj_last_n hval₁ hmem_last₁
      (fun m' hm' hin => ((hmem₁ d.1.1.1.2 hpre.2.2.1 m' hm' d.1.1.2).mp hin).2 ⟨rfl, rfl⟩)
    refine validProg_bind (validProg_deleteSwap (d := (d.1, (d.2.2, j_last))) hw hnU hU hV
      ⟨hpre.1, by rw [eff_u.2.2.2.2.1]; exact hpre.2.1, hpre.2.2.1, hpre.2.2.2.2.1,
       by rw [eff_u.2.2.2.2.1]; exact hbc_pos, hpre.2.2.2.2.2.2.1, hj_last_n,
       L₁, hval₁, hmem_last₁⟩) ?_
    have hgm_sw := hsw_eff.2.2.1.trans eff_u.2.2.2.2.1
    exact validProg_popBackSlot (d := d.1.1.1) hw hnU hU hV
      ⟨hpre.1, by rw [hgm_sw]; exact hpre.2.1, hpre.2.2.1, by rw [hgm_sw]; exact hbc_pos⟩
  · exact validProg_popBackSlot (d := d.1.1.1) hw hnU hU hV
      ⟨hpre.1, by rw [eff_u.2.2.2.2.1]; exact hpre.2.1, hpre.2.2.1,
       by rw [eff_u.2.2.2.2.1]; exact hbc_pos⟩

theorem validProg_deleteFinish {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : DeleteFinishPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space (deleteFinishBase d)) s
      (deleteFinishProg U V w n_max h_space d) := by
  simp only [deleteFinishProg, deleteFinishGenProg, deleteFoundGenProg_mk, pure_bind]
  exact validProg_ite
    (fun hfound => validProg_deleteFound (d := (((d.1.1.1.1, d.1.1.1.2.2), d.1.1.2), (d.1.2, d.2)))
      hw hnU hU hV (hpre.2 hfound))
    (fun _ => validProg_pure ())

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
